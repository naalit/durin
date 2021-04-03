use crate::emit::ValPretty;
use crate::ir::{Function, Node, Slots, Val, ValExt};
use crate::ssa::{FunMode, SSA};
use inkwell::basic_block::BasicBlock;
use inkwell::IntPredicate;
use inkwell::{
    builder::Builder, context::Context, module::Module, targets::TargetMachine, types::*,
    values::*, AddressSpace,
};
use specs::{Join, RunNow, WorldExt};
use std::collections::{HashMap, VecDeque};

// Some calling conventions
pub const TAILCC: u32 = 18;
pub const CCC: u32 = 0;
pub const FASTCC: u32 = 8;

/// An owning wrapper around the Inkwell context
pub struct Backend {
    pub cxt: Context,
    pub machine: TargetMachine,
}
impl Backend {
    /// Creates a new Backend object configured to target the host machine.
    pub fn native() -> Self {
        let triple = inkwell::targets::TargetMachine::get_default_triple();
        inkwell::targets::Target::initialize_native(
            &inkwell::targets::InitializationConfig::default(),
        )
        .unwrap();
        let machine = inkwell::targets::Target::from_triple(&triple)
            .unwrap()
            .create_target_machine(
                &triple,
                inkwell::targets::TargetMachine::get_host_cpu_name()
                    .to_str()
                    .unwrap(),
                inkwell::targets::TargetMachine::get_host_cpu_features()
                    .to_str()
                    .unwrap(),
                inkwell::OptimizationLevel::None,
                inkwell::targets::RelocMode::Default,
                inkwell::targets::CodeModel::Default,
            )
            .unwrap();
        let cxt = inkwell::context::Context::create();
        Backend { cxt, machine }
    }

    pub fn codegen_and_run(&self, m: &mut crate::ir::Module) -> bool {
        let m = self.codegen_module(m);
        let ee = m
            .create_jit_execution_engine(inkwell::OptimizationLevel::Less)
            .expect("Failed to create LLVM execution engine");
        if let Ok(main_fun) = unsafe { ee.get_function::<unsafe extern "C" fn()>("main") } {
            unsafe {
                main_fun.call();
            }
            true
        } else {
            false
        }
    }

    pub fn codegen_module(&self, m: &mut crate::ir::Module) -> inkwell::module::Module {
        let mut cxt = self.cxt();
        m.codegen(&mut cxt);
        cxt.module
    }

    /// Creates a `Cxt` for code generation, which borrows the `Backend`.
    pub fn cxt(&self) -> Cxt {
        Cxt::new(&self.cxt, &self.machine)
    }
}

/// Contains all the information needed to call or define a function.
///
/// Each Durin function (that isn't a basic block) corresponds to two LLVM functions:
/// One function is used for known calls, and one for unknown calls.
/// The `known` function has precise types, can use the LLVM stack, and accepts any closed-over values as typed parameters before the rest.
/// The `unknown` function takes all parameters as `i8*`, has one closure parameter at the end, and can't use the LLVM stack to return.
#[derive(Clone, Debug)]
pub struct LFunction<'cxt> {
    /// The arity of the function as written in Durin.
    /// So the LLVM unknown version has arity `arity+1`, and the known version has arity `arity-(if stack_enabled then 1 else 0)+env.len()`.
    pub arity: u32,
    pub known: FunctionValue<'cxt>,
    pub unknown: FunctionValue<'cxt>,
    pub env: Vec<(Val, BasicTypeEnum<'cxt>, Val)>,
    pub blocks: VecDeque<(Val, Function)>,
    pub cont: Option<(Val, Vec<Val>)>,
    pub param_tys: Vec<Val>,
}

pub struct Cxt<'cxt> {
    pub cxt: &'cxt Context,
    pub builder: Builder<'cxt>,
    pub module: Module<'cxt>,
    pub machine: &'cxt TargetMachine,
    pub blocks: HashMap<Val, (BasicBlock<'cxt>, Vec<PointerValue<'cxt>>, Vec<Val>)>,
    pub functions: HashMap<Val, LFunction<'cxt>>,
    pub upvalues: HashMap<Val, BasicValueEnum<'cxt>>,
    /// Keeps track of the return continuation, if we're in a stack-enabled function
    pub cont: Option<(Val, Vec<Val>)>,
}
impl<'cxt> Cxt<'cxt> {
    pub fn new(cxt: &'cxt Context, machine: &'cxt TargetMachine) -> Self {
        let module = cxt.create_module("main");

        Cxt {
            cxt,
            builder: cxt.create_builder(),
            module,
            machine,
            blocks: HashMap::new(),
            functions: HashMap::new(),
            upvalues: HashMap::new(),
            cont: None,
        }
    }

    pub fn any_ty(&self) -> BasicTypeEnum<'cxt> {
        self.cxt
            .i8_type()
            .ptr_type(AddressSpace::Generic)
            .as_basic_type_enum()
    }

    pub fn size_ty(&self) -> IntType<'cxt> {
        self.cxt
            .ptr_sized_int_type(&self.machine.get_target_data(), None)
    }
}

impl crate::ir::Module {
    /// The size that this type takes up on the *stack*
    fn static_size<'cxt>(&self, val: Val, cxt: &Cxt<'cxt>) -> u64 {
        match self.slots().node(val).unwrap() {
            Node::Const(c) => match c {
                crate::ir::Constant::TypeType => cxt.size_ty().get_bit_width() as u64 / 8,
                crate::ir::Constant::IntType(w) => w.bits() as u64 / 8,
                crate::ir::Constant::Int(_, _)
                | crate::ir::Constant::Stop
                | crate::ir::Constant::Unreachable => {
                    unreachable!("not a type")
                }
            },
            Node::FunType(_) => cxt.size_ty().get_bit_width() as u64 / 8 * 2,
            Node::ProdType(v) => {
                // TODO alignment should probably be a property of types separate from size
                let mut size = 0;
                for &i in v {
                    let x = self.static_size(i, cxt);
                    let align = x.min(8);
                    if align > 0 {
                        while size % align != 0 {
                            size += 1;
                        }
                    }
                    size += x;
                }
                size
            }
            Node::SumType(v) => {
                let payload = v.iter().map(|&x| self.static_size(x, cxt)).max().unwrap();
                let mut tag = match v.len() {
                    0..=1 => 0,
                    2 => 1,
                    257..=65536 => 4,
                    _ => 8,
                };
                if payload > 1 {
                    tag = 8;
                }
                tag + payload
            }
            Node::Param(_, _) | Node::ExternFunType(_, _) | Node::RefTy(_) => {
                cxt.size_ty().get_bit_width() as u64 / 8
            }
            Node::Fun(_)
            | Node::ExternFun(_, _, _)
            | Node::ExternCall(_)
            | Node::BinOp(_, _, _)
            | Node::IfCase(_, _)
            | Node::Proj(_, _)
            | Node::Inj(_, _, _)
            | Node::Product(_, _)
            | Node::Ref(_)
            | Node::If(_) => {
                unreachable!("not a type")
            }
        }
    }

    fn llvm_ty<'cxt>(&self, val: Val, cxt: &Cxt<'cxt>) -> BasicTypeEnum<'cxt> {
        match self.slots().node(val).unwrap() {
            Node::Const(c) => match c {
                crate::ir::Constant::TypeType => cxt.size_ty().as_basic_type_enum(),
                crate::ir::Constant::IntType(w) => {
                    cxt.cxt.custom_width_int_type(w.bits()).as_basic_type_enum()
                }
                crate::ir::Constant::Int(_, _)
                | crate::ir::Constant::Stop
                | crate::ir::Constant::Unreachable => {
                    unreachable!("not a type")
                }
            },
            // A closure
            Node::FunType(nargs) => {
                // The argument types don't matter, just the number
                let fun_ty = cxt.cxt.void_type().fn_type(
                    &(0..*nargs)
                        .map(|_| cxt.any_ty())
                        // The closure environment is the last parameter
                        .chain(std::iter::once(cxt.any_ty()))
                        .collect::<Vec<_>>(),
                    false,
                );
                let env_ty = cxt.any_ty();
                cxt.cxt
                    .struct_type(
                        &[
                            env_ty,
                            fun_ty.ptr_type(AddressSpace::Generic).as_basic_type_enum(),
                        ],
                        false,
                    )
                    .as_basic_type_enum()
            }
            Node::ExternFunType(p, r) => {
                let r = self.llvm_ty(*r, cxt);
                let v: Vec<_> = p.iter().map(|&t| self.llvm_ty(t, cxt)).collect();
                r.fn_type(&v, false)
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum()
            }
            Node::ProdType(v) => {
                let v: Vec<_> = v.iter().map(|&x| self.llvm_ty(x, cxt)).collect();
                cxt.cxt.struct_type(&v, false).as_basic_type_enum()
            }
            Node::SumType(v) => {
                if v.len() == 1 {
                    // No tag if there's only one element
                    return self.llvm_ty(v[0], cxt);
                }

                // TODO size probably isn't a constant
                let size = v.iter().map(|&x| self.static_size(x, cxt)).max().unwrap();
                let payload = cxt
                    .cxt
                    .i8_type()
                    .array_type(size as u32)
                    .as_basic_type_enum();
                let tag = match v.len() {
                    // No tag if there's only one element
                    0..=1 => return payload,
                    // 2 => cxt.cxt.bool_type(),
                    2..=256 => cxt.cxt.i8_type(),
                    257..=65536 => cxt.cxt.i32_type(),
                    _ => cxt.cxt.i64_type(),
                };
                cxt.cxt
                    .struct_type(&[tag.as_basic_type_enum(), payload], false)
                    .as_basic_type_enum()
            }
            Node::RefTy(v) => self
                .llvm_ty(*v, cxt)
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum(),
            // Polymorphic
            Node::Param(_, _) => cxt.any_ty(),
            Node::Fun(_)
            | Node::ExternFun(_, _, _)
            | Node::ExternCall(_)
            | Node::BinOp(_, _, _)
            | Node::IfCase(_, _)
            | Node::Proj(_, _)
            | Node::Inj(_, _, _)
            | Node::Product(_, _)
            | Node::Ref(_)
            | Node::If(_) => {
                unreachable!("not a type")
            }
        }
    }

    fn gen_value<'cxt>(&self, val: Val, cxt: &Cxt<'cxt>) -> BasicValueEnum<'cxt> {
        let val = self.unredirect(val);

        if let Some(&v) = cxt.upvalues.get(&val) {
            return v;
        }
        match self.slots().node(val).unwrap() {
            Node::Fun(_) => {
                // Create a closure
                let LFunction {
                    arity,
                    unknown,
                    env,
                    ..
                } = cxt
                    .functions
                    .get(&val)
                    .unwrap_or_else(|| panic!("Couldn't find {}", val.pretty(self)));

                // Create the environment struct, then store it in an alloca and bitcast the pointer to i8*
                // TODO heap allocation instead of alloca
                let env = match env.len() {
                    0 => cxt.any_ty().into_pointer_type().get_undef(),
                    1 => {
                        // If there's only one upvalue, treat it like an `any`
                        let (val, _, _) = env[0];
                        let val = self.gen_value(val, cxt);
                        self.to_any(val, cxt)
                    }
                    _ => {
                        let env_tys: Vec<_> = env.iter().map(|&(_, ty, _)| ty).collect();
                        let mut env_val = cxt.cxt.struct_type(&env_tys, false).get_undef();
                        for (i, &(val, _, _)) in env.iter().enumerate() {
                            // TODO reuse values (all over the codebase but especially here)
                            let val = self.gen_value(val, cxt);
                            env_val = cxt
                                .builder
                                .build_insert_value(env_val, val, i as u32, "env_insert")
                                .unwrap()
                                .into_struct_value();
                        }
                        let env_ptr = cxt
                            .builder
                            .build_malloc(cxt.cxt.struct_type(&env_tys, false), "env_ptr")
                            .unwrap();
                        cxt.builder.build_store(env_ptr, env_val);
                        cxt.builder
                            .build_bitcast(env_ptr, cxt.any_ty(), "env")
                            .into_pointer_value()
                    }
                };

                // We use the unknown version of the function, which takes one environment parameter and all of type i8* (any)
                let arg_tys: Vec<_> = (0..arity + 1).map(|_| cxt.any_ty()).collect();
                let fun_ty = cxt
                    .cxt
                    .void_type()
                    .fn_type(&arg_tys, false)
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum();

                let cl = cxt
                    .cxt
                    .struct_type(&[cxt.any_ty(), fun_ty], false)
                    .get_undef();
                let cl = cxt
                    .builder
                    .build_insert_value(cl, env, 0, "cl_partial")
                    .unwrap();
                let cl = cxt
                    .builder
                    .build_insert_value(cl, unknown.as_global_value().as_pointer_value(), 1, "cl")
                    .unwrap();

                cl.as_basic_value_enum()
            }
            Node::FunType(_) => {
                let ty = cxt.cxt.struct_type(&[cxt.any_ty(), cxt.any_ty()], false);
                ty.size_of().unwrap().as_basic_value_enum()
            }
            Node::ExternFunType(_, _) | Node::RefTy(_) => {
                // Just a function pointer
                cxt.any_ty().size_of().unwrap().as_basic_value_enum()
            }
            Node::ExternFun(name, params, ret) => {
                let fun = match cxt.module.get_function(name) {
                    Some(fun) => fun,
                    None => {
                        let rty = self.llvm_ty(*ret, cxt);
                        let ptys: Vec<_> = params.iter().map(|t| self.llvm_ty(*t, cxt)).collect();
                        let fty = rty.fn_type(&ptys, false);
                        cxt.module.add_function(name, fty, None)
                    }
                };
                fun.as_global_value()
                    .as_pointer_value()
                    .as_basic_value_enum()
            }
            Node::ProdType(_) | Node::SumType(_) => {
                // TODO boxing??
                self.llvm_ty(val, cxt)
                    .size_of()
                    .unwrap()
                    .as_basic_value_enum()
            }
            Node::Proj(x, i) => {
                let x = self.gen_value(*x, cxt).into_struct_value();
                cxt.builder
                    .build_extract_value(x, *i as u32, "project")
                    .unwrap()
            }
            Node::Inj(ty, i, payload) => {
                if matches!(self.slots().node(*ty), Some(Node::SumType(v)) if v.len() == 1) {
                    // No tag or casting needed
                    return self.gen_value(*payload, cxt);
                }

                let ty = self.llvm_ty(*ty, cxt).into_struct_type();
                let payload_ty = ty.get_field_type_at_index(1).unwrap();

                // Alloca the larger type, then bitcast to store the smaller one in the alloca
                let payload = self.gen_value(*payload, cxt);
                let payload_ptr = cxt.builder.build_alloca(payload_ty, "payload.ptr");
                let casted = cxt
                    .builder
                    .build_bitcast(
                        payload_ptr,
                        payload.get_type().ptr_type(AddressSpace::Generic),
                        "payload.casted",
                    )
                    .into_pointer_value();
                cxt.builder.build_store(casted, payload);
                // Then load the original non-casted pointer to the larger type
                let payload = cxt.builder.build_load(payload_ptr, "payload.casted");

                let tag = ty
                    .get_field_type_at_index(0)
                    .unwrap()
                    .into_int_type()
                    .const_int(*i as u64, false)
                    .as_basic_value_enum();
                let agg = cxt
                    .builder
                    .build_insert_value(ty.get_undef(), tag, 0, "union.tag")
                    .unwrap();
                let agg = cxt
                    .builder
                    .build_insert_value(agg, payload, 1, "union")
                    .unwrap();
                agg.as_basic_value_enum()
            }
            Node::Product(ty, v) => {
                let ty = self.llvm_ty(*ty, cxt).into_struct_type();
                let mut agg = ty.get_undef().as_aggregate_value_enum();
                for (i, x) in v.into_iter().enumerate() {
                    let x = self.gen_value(*x, cxt);
                    agg = cxt
                        .builder
                        .build_insert_value(agg, x, i as u32, "product")
                        .unwrap();
                }
                agg.as_basic_value_enum()
            }
            Node::IfCase(_, _) => panic!("`ifcase _ _` isn't a first-class function!"),
            Node::If(_) => panic!("`if _` isn't a first-class function!"),
            Node::Ref(_) => {
                panic!("`refset`, `refget`, and `refnew` aren't first-class functions!")
            }
            Node::Param(f, i) => {
                let name = self.name(val).unwrap_or_else(|| "param".to_string());
                let ptr = cxt
                    .blocks
                    .get(f)
                    .unwrap_or_else(|| panic!("Couldn't find param {} of {}", i, f.pretty(self)))
                    .1[*i as usize];
                cxt.builder.build_load(ptr, &name)
            }
            Node::Const(c) => match c {
                crate::ir::Constant::TypeType => cxt.size_ty().size_of().as_basic_value_enum(),
                crate::ir::Constant::IntType(w) => cxt
                    .cxt
                    .custom_width_int_type(w.bits())
                    .size_of()
                    .as_basic_value_enum(),
                crate::ir::Constant::Int(w, val) => cxt
                    .cxt
                    .custom_width_int_type(w.bits())
                    .const_int(*val as u64, false)
                    .as_basic_value_enum(),
                crate::ir::Constant::Stop | crate::ir::Constant::Unreachable => {
                    panic!("stop or unreachable isn't a first-class function!")
                }
            },
            Node::ExternCall(_) => panic!("externcall isn't a first-class function!"),
            Node::BinOp(op, a, b) => {
                let a = self.gen_value(*a, cxt);
                let b = self.gen_value(*b, cxt);
                let name = self.name(val).unwrap_or_else(|| "binop".to_string());
                let name = &name;
                match op {
                    crate::ir::BinOp::IAdd => cxt
                        .builder
                        .build_int_add(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::ISub => cxt
                        .builder
                        .build_int_sub(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IMul => cxt
                        .builder
                        .build_int_mul(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IDiv => cxt
                        .builder
                        .build_int_signed_div(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IAnd => cxt
                        .builder
                        .build_and(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IOr => cxt
                        .builder
                        .build_or(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IXor => cxt
                        .builder
                        .build_xor(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IShl => cxt
                        .builder
                        .build_left_shift(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IShr => cxt
                        .builder
                        // TODO unsigned vs signed (division too)
                        .build_right_shift(a.into_int_value(), b.into_int_value(), true, name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IExp => todo!("llvm.powi intrinsic"),

                    crate::ir::BinOp::IEq => cxt
                        .builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            a.into_int_value(),
                            b.into_int_value(),
                            name,
                        )
                        .as_basic_value_enum(),
                    crate::ir::BinOp::INEq => cxt
                        .builder
                        .build_int_compare(
                            IntPredicate::NE,
                            a.into_int_value(),
                            b.into_int_value(),
                            name,
                        )
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IGt => cxt
                        .builder
                        .build_int_compare(
                            IntPredicate::SGT,
                            a.into_int_value(),
                            b.into_int_value(),
                            name,
                        )
                        .as_basic_value_enum(),
                    crate::ir::BinOp::ILt => cxt
                        .builder
                        .build_int_compare(
                            IntPredicate::SLT,
                            a.into_int_value(),
                            b.into_int_value(),
                            name,
                        )
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IGeq => cxt
                        .builder
                        .build_int_compare(
                            IntPredicate::SGE,
                            a.into_int_value(),
                            b.into_int_value(),
                            name,
                        )
                        .as_basic_value_enum(),
                    crate::ir::BinOp::ILeq => cxt
                        .builder
                        .build_int_compare(
                            IntPredicate::SLE,
                            a.into_int_value(),
                            b.into_int_value(),
                            name,
                        )
                        .as_basic_value_enum(),
                }
            }
        }
    }

    pub fn codegen<'cxt>(&mut self, cxt: &mut Cxt<'cxt>) {
        // Have the SSA system figure out which functions are blocks or stack-enabled
        SSA.setup(&mut self.world);
        SSA.run_now(&self.world);
        let modes = self.world.read_storage::<FunMode>();
        let slots = self.slots();

        // Collect all functions and their blocks
        let mut to_gen: HashMap<Val, VecDeque<(Val, crate::ir::Function)>> = HashMap::new();
        let mut stack_enabled = HashMap::new();
        for (v, &mode) in (&self.world.entities(), &modes).join() {
            match mode {
                FunMode::SSA(cont) => {
                    to_gen
                        .entry(v)
                        .or_default()
                        .push_front((v, slots.fun(v).unwrap().clone()));
                    stack_enabled.insert(v, cont);
                }
                FunMode::CPS => {
                    to_gen
                        .entry(v)
                        .or_default()
                        .push_front((v, slots.fun(v).unwrap().clone()));
                }
                FunMode::Block(parent) => {
                    to_gen
                        .entry(parent)
                        .or_default()
                        .push_back((v, slots.fun(v).unwrap().clone()));
                }
            }
        }
        drop(modes);
        drop(slots);

        // Declare all the functions before generating their bodies
        for (val, blocks) in to_gen {
            let env = self.env(val);

            let slots = self.slots();
            if let Some(fun) = slots.fun(val).cloned() {
                drop(slots);

                // Get the continuation type by whatever is passed to the continuation
                let cont = stack_enabled.get(&val);
                let cont = cont.and_then(|&cont| {
                    let uses = self.uses();
                    let u = uses.get(cont).unwrap();
                    if u.is_empty() {
                        None
                    } else {
                        let u = u.clone();
                        drop(uses);
                        for &i in &**u {
                            let slots = self.slots();
                            let ty = match slots.node(i).cloned() {
                                Some(Node::Fun(Function {
                                    callee, call_args, ..
                                })) if callee == cont => {
                                    drop(slots);
                                    call_args
                                        .clone()
                                        .into_iter()
                                        .map(|x| x.ty(self))
                                        .collect::<Vec<_>>()
                                }
                                _ => continue,
                            };
                            return Some((cont, ty));
                        }
                        None
                    }
                });

                // Generate the function signature
                let args: Vec<_> = env
                    .iter()
                    .map(|(_, ty)| ty)
                    .chain(if cont.is_some() {
                        &fun.params[0..fun.params.len() - 1]
                    } else {
                        &fun.params
                    })
                    .map(|&x| self.llvm_ty(x, cxt))
                    .collect();
                let known_ty = if let Some((_, ret_tys)) = &cont {
                    let ret_ty = if ret_tys.len() == 1 {
                        self.llvm_ty(ret_tys[0], cxt)
                    } else {
                        let v: Vec<_> = ret_tys
                            .iter()
                            .copied()
                            .map(|x| self.llvm_ty(x, cxt))
                            .collect();
                        cxt.cxt.struct_type(&v, false).as_basic_type_enum()
                    };
                    ret_ty.fn_type(&args, false)
                } else {
                    cxt.cxt.void_type().fn_type(&args, false)
                };

                // Declare the known and unknown versions of the function
                let name = self
                    .name(val)
                    .unwrap_or_else(|| format!("fun${}", val.id()));
                let known = cxt.module.add_function(&name, known_ty, None);
                known.set_call_conventions(TAILCC);

                let uargs: Vec<_> = fun
                    .params
                    .iter()
                    .map(|_| cxt.any_ty())
                    .chain(std::iter::once(cxt.any_ty()))
                    .collect();
                let unknown_ty = cxt.cxt.void_type().fn_type(&uargs, false);
                let uname = format!("u${}", name);
                let unknown = cxt.module.add_function(&uname, unknown_ty, None);
                unknown.set_call_conventions(TAILCC);

                let env = args[0..env.len()]
                    .iter()
                    .zip(env)
                    .map(|(&ty, (val, ty2))| (val, ty, ty2))
                    .collect();

                cxt.functions.insert(
                    val,
                    LFunction {
                        arity: fun.params.len() as u32,
                        known,
                        unknown,
                        env,
                        blocks,
                        cont,
                        param_tys: fun.params.to_vec(),
                    },
                );
            }
        }

        // Now generate the function bodies
        for (
            val,
            LFunction {
                unknown,
                known,
                blocks,
                cont,
                env,
                ..
            },
        ) in cxt.functions.clone()
        {
            // First generate the unknown version, which just delegates to the known version
            {
                // Remove any basic blocks and upvalues we generated last time, they're no longer accessible
                cxt.blocks = HashMap::new();
                cxt.upvalues = HashMap::new();

                let uentry = cxt.cxt.append_basic_block(unknown, "entry");
                cxt.builder.position_at_end(uentry);

                // Unpack environment
                let &env_ptr = unknown.get_params().last().unwrap();
                env_ptr.set_name("env");
                // TODO wait, what about dependently sized types?
                match env.len() {
                    0 => (),
                    1 => {
                        // There's only one upvalue, so treat the environment pointer as an `any`
                        let (val, _, ty) = env[0];
                        let value = self.from_any(env_ptr.into_pointer_value(), ty, cxt);
                        cxt.upvalues.insert(val, value);
                    }
                    _ => {
                        let env_tys: Vec<_> = env.iter().map(|&(_, ty, _)| ty).collect();
                        let env_ty = cxt.cxt.struct_type(&env_tys, false);
                        let env_ptr = cxt.builder.build_bitcast(
                            env_ptr,
                            env_ty.ptr_type(AddressSpace::Generic),
                            "env_ptr",
                        );
                        let env_val = cxt
                            .builder
                            .build_load(env_ptr.into_pointer_value(), "env")
                            .into_struct_value();

                        // Add environment slots to the context
                        for (i, &(val, _, _)) in env.iter().enumerate() {
                            let value = cxt
                                .builder
                                .build_extract_value(
                                    env_val,
                                    i as u32,
                                    &self.name(val).unwrap_or_else(|| "upvalue".to_string()),
                                )
                                .unwrap();
                            cxt.upvalues.insert(val, value);
                        }
                    }
                }

                // Call function
                let mut args: Vec<BasicValueEnum> = blocks[0]
                    .1
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, &ty)| {
                        self.from_any(unknown.get_params()[i].into_pointer_value(), ty, cxt)
                    })
                    .collect();
                if let Some(vcont) = args.pop() {
                    // `gen_call` takes the continuation as a Val, not a BasicValueEnum; so, we use an unused Val slot and stick the BasicValueEnum in the upvalues map
                    let cont = self.reserve(None);
                    cxt.upvalues.insert(cont, vcont);
                    self.gen_call(val, args, Some(cont), cxt);
                } else {
                    self.gen_call(val, args, None, cxt);
                }
            }

            let fun = known;
            cxt.cont = cont;

            let entry = cxt.cxt.append_basic_block(fun, "entry");
            cxt.builder.position_at_end(entry);

            // Remove any basic blocks and upvalues we generated last time, they're no longer accessible
            cxt.blocks = HashMap::new();
            cxt.upvalues = HashMap::new();

            // Add closed-over upvalues to the context
            for ((val, _ty, _ty2), param) in env.iter().zip(fun.get_params()) {
                cxt.upvalues.insert(*val, param);
            }

            // Declare all blocks and their parameters first
            // Block parameters are stored in allocas, which will be removed with mem2reg
            for (bval, bfun) in &blocks {
                let name = format!("{}${}", val.pretty(self), bval.pretty(self));
                let block = cxt.cxt.append_basic_block(fun, &name);
                let mut params = Vec::new();
                for (i, &ty) in bfun.params.iter().enumerate() {
                    let ty = self.llvm_ty(ty, cxt);
                    let name = self.param_name(*bval, i as u8);
                    let param = cxt.builder.build_alloca(ty, &name);
                    params.push(param);
                }
                cxt.blocks
                    .insert(*bval, (block, params, bfun.params.to_vec()));
            }

            // We store the function parameters in the parameter slots of the entry block
            let (first_block, _) = &blocks[0];
            for (&ptr, value) in cxt
                .blocks
                .get(first_block)
                .unwrap()
                .1
                .iter()
                .zip(fun.get_params().into_iter().skip(env.len()))
            {
                cxt.builder.build_store(ptr, value);
            }
            cxt.builder
                .build_unconditional_branch(cxt.blocks.get(first_block).unwrap().0);

            // Now actually generate the blocks' code
            for (bval, bfun) in blocks {
                let (block, _, _) = cxt.blocks.get(&bval).unwrap();
                cxt.builder.position_at_end(*block);

                let slots = self.slots();

                // If we're calling if x, do that
                if let Some(Node::If(x)) = slots.node(bfun.callee).cloned() {
                    drop(slots);
                    assert_eq!(bfun.call_args.len(), 2);
                    let fthen = bfun.call_args[0];
                    let felse = bfun.call_args[1];

                    let cond = self.gen_value(x, cxt).into_int_value();

                    let bstart = cxt.builder.get_insert_block().unwrap();
                    let bthen = cxt.cxt.insert_basic_block_after(bstart, "if.then");
                    let belse = cxt.cxt.insert_basic_block_after(bthen, "if.else");

                    cxt.builder.build_conditional_branch(cond, bthen, belse);

                    cxt.builder.position_at_end(bthen);
                    self.gen_call(fthen, vec![], None, cxt);

                    cxt.builder.position_at_end(belse);
                    self.gen_call(felse, vec![], None, cxt);
                // If we're calling ifcase i x, do that instead
                } else if let Some(Node::IfCase(i, x)) = slots.node(bfun.callee).cloned() {
                    drop(slots);
                    let ty = x.ty(self);
                    let slots = self.slots();
                    let payload_ty = match ty.get(&slots) {
                        Node::SumType(v) if v.len() == 1 => {
                            drop(slots);
                            // There's no tag, and no casting needed
                            let x = self.gen_value(x, cxt);
                            assert_eq!(bfun.call_args.len(), 2);
                            let fthen = bfun.call_args[0];

                            self.gen_call(fthen, vec![x], None, cxt);

                            // Skip to the next basic block
                            continue;
                        }
                        Node::SumType(v) => v[i],
                        x => unreachable!("{:?}", x),
                    };
                    assert_eq!(bfun.call_args.len(), 2);
                    let fthen = bfun.call_args[0];
                    let felse = bfun.call_args[1];
                    drop(slots);

                    let x = self.gen_value(x, cxt);
                    let tag = cxt
                        .builder
                        .build_extract_value(x.into_struct_value(), 0, "union.tag")
                        .unwrap()
                        .into_int_value();

                    let bstart = cxt.builder.get_insert_block().unwrap();
                    let bthen = cxt.cxt.insert_basic_block_after(bstart, "ifcase.then");
                    let belse = cxt.cxt.insert_basic_block_after(bthen, "ifcase.else");

                    let cond = cxt.builder.build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        tag.get_type().const_int(i as u64, false),
                        "ifcase.cond",
                    );
                    cxt.builder.build_conditional_branch(cond, bthen, belse);

                    cxt.builder.position_at_end(bthen);
                    let payload_ty = self.llvm_ty(payload_ty, cxt);
                    let payload = cxt
                        .builder
                        .build_extract_value(x.into_struct_value(), 1, "union.payload")
                        .unwrap();
                    let payload_ptr = cxt
                        .builder
                        .build_alloca(payload.get_type(), "union.payload.ptr");
                    // TODO query the needed alignment for the target type
                    payload_ptr
                        .as_instruction_value()
                        .unwrap()
                        .set_alignment(8)
                        .unwrap();
                    cxt.builder.build_store(payload_ptr, payload);
                    let payload_ptr = cxt.builder.build_bitcast(
                        payload_ptr,
                        payload_ty.ptr_type(AddressSpace::Generic),
                        "union.payload.casted_ptr",
                    );
                    let payload = cxt
                        .builder
                        .build_load(payload_ptr.into_pointer_value(), "union.payload.casted");
                    self.gen_call(fthen, vec![payload], None, cxt);

                    cxt.builder.position_at_end(belse);
                    self.gen_call(felse, vec![], None, cxt);
                } else {
                    drop(slots);

                    // Generate a call
                    let args: Vec<_> = bfun
                        .call_args
                        .iter()
                        .take(if bfun.call_args.is_empty() {
                            0
                        } else {
                            bfun.call_args.len() - 1
                        })
                        .map(|x| self.gen_value(*x, cxt))
                        .collect();
                    self.gen_call(bfun.callee, args, bfun.call_args.last().copied(), cxt);
                }
            }
        }
    }

    fn from_any<'cxt>(
        &self,
        any: PointerValue<'cxt>,
        ty: Val,
        cxt: &Cxt<'cxt>,
    ) -> BasicValueEnum<'cxt> {
        match self.slots().node(ty).unwrap() {
            Node::Const(c) => match c {
                crate::ir::Constant::TypeType => cxt
                    .builder
                    .build_ptr_to_int(any, cxt.size_ty(), "cast")
                    .as_basic_value_enum(),
                crate::ir::Constant::IntType(w) => cxt
                    .builder
                    .build_ptr_to_int(any, cxt.cxt.custom_width_int_type(w.bits()), "cast")
                    .as_basic_value_enum(),
                crate::ir::Constant::Int(_, _)
                | crate::ir::Constant::Stop
                | crate::ir::Constant::Unreachable => {
                    unreachable!("not a type")
                }
            },
            Node::SumType(x) if x.len() == 1 => self.from_any(any, x[0], cxt),
            Node::ProdType(x) if x.len() == 1 => cxt
                .builder
                .build_insert_value(
                    self.llvm_ty(ty, cxt).into_struct_type().get_undef(),
                    self.from_any(any, x[0], cxt),
                    0,
                    "wrap_cast",
                )
                .unwrap()
                .as_basic_value_enum(),
            Node::FunType(_) | Node::ProdType(_) | Node::SumType(_) => {
                match self.static_size(ty, cxt) {
                    0 => self
                        .llvm_ty(ty, cxt)
                        .into_struct_type()
                        .get_undef()
                        .as_basic_value_enum(),
                    // TODO cast to 2+ element structs or products without loading
                    // x if x <= cxt.machine.get_target_data().get_pointer_byte_size(None).into() => {
                    //     let int = cxt.builder.build_ptr_to_int(any, cxt.cxt.custom_width_int_type(x as u32 * 8), "shrink");
                    //     cxt.builder.build_bitcast(int, self.llvm_ty(ty, cxt), "cast")
                    // }
                    _ => {
                        let ptr = cxt
                            .builder
                            .build_bitcast(
                                any,
                                self.llvm_ty(ty, cxt).ptr_type(AddressSpace::Generic),
                                "ptr",
                            )
                            .into_pointer_value();
                        cxt.builder.build_load(ptr, "val")
                    }
                }
            }
            Node::ExternFunType(_, _) => {
                let lty = self.llvm_ty(ty, cxt);
                cxt.builder
                    .build_bitcast(any, lty, "extern_fun_ptr")
                    .as_basic_value_enum()
            }
            Node::RefTy(_) => {
                let lty = self.llvm_ty(ty, cxt);
                cxt.builder
                    .build_bitcast(any, lty, "ref_casted")
                    .as_basic_value_enum()
            }
            // Leave as an "any" since it's polymorphic
            Node::Param(_, _) => any.as_basic_value_enum(),
            // TODO Proj should be allowed as a type
            Node::BinOp(_, _, _)
            | Node::Fun(_)
            | Node::ExternFun(_, _, _)
            | Node::ExternCall(_)
            | Node::IfCase(_, _)
            | Node::Proj(_, _)
            | Node::Inj(_, _, _)
            | Node::Product(_, _)
            | Node::Ref(_)
            | Node::If(_) => {
                unreachable!("not a type")
            }
        }
    }

    fn to_any<'cxt>(&self, val: BasicValueEnum<'cxt>, cxt: &Cxt<'cxt>) -> PointerValue<'cxt> {
        match val.get_type() {
            BasicTypeEnum::IntType(_) => {
                let val = val.into_int_value();
                cxt.builder
                    .build_int_to_ptr(val, cxt.any_ty().into_pointer_type(), "cast")
            }
            BasicTypeEnum::StructType(x) if x.count_fields() == 0 => {
                cxt.any_ty().into_pointer_type().get_undef()
            }
            BasicTypeEnum::StructType(x) if x.count_fields() == 1 => {
                let x = cxt
                    .builder
                    .build_extract_value(val.into_struct_value(), 0, "unwrap_cast")
                    .unwrap();
                self.to_any(x, cxt)
            }
            BasicTypeEnum::ArrayType(_)
            | BasicTypeEnum::StructType(_)
            | BasicTypeEnum::VectorType(_) => {
                let ty = val.get_type();
                // TODO garbage collection
                let ptr = cxt.builder.build_malloc(ty, "cast_slot").unwrap();
                cxt.builder.build_store(ptr, val);
                cxt.builder
                    .build_bitcast(ptr, cxt.any_ty(), "casted")
                    .into_pointer_value()
            }
            BasicTypeEnum::PointerType(_) => cxt
                .builder
                .build_bitcast(val, cxt.any_ty(), "casted")
                .into_pointer_value(),
            BasicTypeEnum::FloatType(_) => unimplemented!(),
        }
    }

    /// Makes the value fit the required type, for when the level of knowledge about a type changes.
    fn cast<'cxt>(
        &self,
        val: BasicValueEnum<'cxt>,
        to: Val,
        cxt: &Cxt<'cxt>,
    ) -> BasicValueEnum<'cxt> {
        // LLVM will optimize this out most of the time
        self.from_any(self.to_any(val, cxt), to, cxt)
    }

    fn gen_call<'cxt>(
        &mut self,
        callee: Val,
        mut args: Vec<BasicValueEnum<'cxt>>,
        cont: Option<Val>,
        cxt: &mut Cxt<'cxt>,
    ) {
        let slots = self.slots();
        match slots.node(callee) {
            // If we're calling the return continuation, emit a return instruction
            _ if cxt.cont.as_ref().map_or(false, |(x, _)| *x == callee) => {
                if let Some(k) = cont {
                    args.push(self.gen_value(k, cxt));
                }
                let args = args
                    .into_iter()
                    .zip(&cxt.cont.as_ref().unwrap().1)
                    .map(|(x, &ty)| self.cast(x, ty, cxt))
                    .collect::<Vec<_>>();
                let ret = if args.len() == 1 {
                    args[0]
                } else {
                    let tys: Vec<_> = cxt
                        .cont
                        .clone()
                        .unwrap()
                        .1
                        .into_iter()
                        .map(|x| self.llvm_ty(x, cxt))
                        .collect();
                    let ty = cxt.cxt.struct_type(&tys, false);
                    let mut agg = ty.get_undef().as_aggregate_value_enum();
                    for (i, x) in args.into_iter().enumerate() {
                        agg = cxt
                            .builder
                            .build_insert_value(agg, x, i as u32, "ret_product")
                            .unwrap();
                    }
                    agg.as_basic_value_enum()
                };
                cxt.builder.build_return(Some(&ret));
            }

            // If we're calling a basic block, jump there
            _ if cxt.blocks.get(&callee).is_some() => {
                let (target, params, tys) = cxt.blocks.get(&callee).unwrap();
                if let Some(k) = cont {
                    args.push(self.gen_value(k, cxt));
                }
                let args = args
                    .into_iter()
                    .zip(tys)
                    .map(|(x, &ty)| self.cast(x, ty, cxt))
                    .collect::<Vec<_>>();
                // Set the parameters and jump to the target block
                for (&ptr, value) in params.iter().zip(args) {
                    cxt.builder.build_store(ptr, value);
                }
                cxt.builder.build_unconditional_branch(*target);
            }

            // Execute a ref op if we're doing one
            Some(Node::Ref(op)) => {
                // Execute the operation
                let args = match op {
                    crate::ir::RefOp::RefNew(ty) => {
                        let ty = self.llvm_ty(*ty, cxt);
                        let ptr = cxt.builder.build_malloc(ty, "refnew").unwrap();
                        vec![ptr.as_basic_value_enum()]
                    }
                    crate::ir::RefOp::RefGet(r) => {
                        let ptr = self.gen_value(*r, cxt).into_pointer_value();
                        let val = cxt.builder.build_load(ptr, "refget");
                        vec![val]
                    }
                    crate::ir::RefOp::RefSet(r, v) => {
                        let ptr = self.gen_value(*r, cxt).into_pointer_value();
                        let val = self.gen_value(*v, cxt);
                        cxt.builder.build_store(ptr, val);
                        Vec::new()
                    }
                };

                drop(slots);

                // Call the continuation
                let cont = cont.unwrap();
                let cont2 = args.last().map(|&v| {
                    let n = self.reserve(None);
                    cxt.upvalues.insert(n, v);
                    n
                });
                self.gen_call(cont, Vec::new(), cont2, cxt)
            }

            // If we're stopping, return void
            Some(Node::Const(crate::ir::Constant::Stop)) => {
                cxt.builder.build_return(None);
            }

            // If we're calling unreachable, emit a LLVM unreachable instruction
            Some(Node::Const(crate::ir::Constant::Unreachable)) => {
                cxt.builder.build_unreachable();
            }
            // Even if it goes through a function
            Some(Node::Fun(Function { callee, .. }))
                if matches!(
                    self.slots().node(*callee),
                    Some(Node::Const(crate::ir::Constant::Unreachable))
                ) =>
            {
                cxt.builder.build_unreachable();
            }

            // If we're calling an extern function, do that
            Some(Node::ExternCall(f)) => {
                let f = self.gen_value(*f, cxt);
                let call = cxt
                    .builder
                    .build_call(f.into_pointer_value(), &args, "extern_call");
                call.set_tail_call(true);

                drop(slots);

                let cont = cont.unwrap();
                self.gen_call(
                    cont,
                    vec![call.try_as_basic_value().left().unwrap()],
                    None,
                    cxt,
                )
            }

            // Otherwise, we're actually calling a function
            _ => {
                // The mechanism depends on whether it's a known or unknown call
                match cxt.functions.get(&self.unredirect(callee)) {
                    Some(LFunction {
                        known,
                        env,
                        cont: fcont,
                        param_tys,
                        ..
                    }) => {
                        // Known call

                        // Prepend upvalues to the argument list
                        let args = args
                            .into_iter()
                            .zip(param_tys)
                            .map(|(x, &ty)| self.cast(x, ty, cxt))
                            .collect::<Vec<_>>();
                        let mut args: Vec<_> = env
                            .iter()
                            .map(|&(val, _, _)| self.gen_value(val, cxt))
                            .chain(args)
                            .collect();

                        // The actual call depends on whether we're using the LLVM stack or not
                        if fcont.is_some() {
                            drop(slots);

                            let cont = cont.unwrap_or_else(|| {
                                panic!("No continuation given for {}", callee.pretty(self))
                            });
                            let call = cxt.builder.build_call(*known, &args, "stack_call");
                            call.set_tail_call(true);
                            call.set_call_convention(TAILCC);

                            let call = call.try_as_basic_value().left().unwrap();
                            let nargs = fcont.as_ref().unwrap().1.len();
                            let mut args = if nargs == 1 {
                                vec![call]
                            } else {
                                let call = call.into_struct_value();
                                (0..nargs as u32)
                                    .map(|i| {
                                        cxt.builder
                                            .build_extract_value(call, i, "extract_return")
                                            .unwrap()
                                    })
                                    .collect()
                            };
                            let acont = args.pop().map(|x| {
                                let v = self.reserve(None);
                                cxt.upvalues.insert(v, x);
                                v
                            });

                            self.gen_call(cont, args, acont, cxt)
                        } else {
                            if let Some(k) = cont {
                                let v = self.gen_value(k, cxt);
                                let v = self.cast(v, *param_tys.last().unwrap(), cxt);
                                args.push(v);
                            }
                            let call = cxt.builder.build_call(*known, &args, "call");
                            // Tail calls are disabled until we stop using allocas
                            // call.set_tail_call(true);
                            call.set_call_convention(TAILCC);
                            cxt.builder.build_return(None);
                        }
                    }
                    None => {
                        // Unknown call
                        if let Some(k) = cont {
                            args.push(self.gen_value(k, cxt));
                        }
                        // let args = args
                        //     .into_iter()
                        //     .zip(tys)
                        //     .map(|(x, ty)| self.cast(x, ty, cxt))
                        //     .collect::<Vec<_>>();
                        let callee = self.gen_value(callee, cxt).into_struct_value();
                        let env = cxt.builder.build_extract_value(callee, 0, "env").unwrap();
                        let fun_ptr = cxt
                            .builder
                            .build_extract_value(callee, 1, "fun_ptr")
                            .unwrap()
                            .into_pointer_value();

                        // It could be polymorphic, so we pass all arguments as word-size "any"
                        let mut args: Vec<_> = args
                            .into_iter()
                            .map(|val| self.to_any(val, cxt).as_basic_value_enum())
                            .collect();
                        // The closure environment is the last argument
                        args.push(env);

                        let call = cxt.builder.build_call(fun_ptr, &args, "closure_call");
                        // Tail calls are disabled until we stop using allocas
                        // call.set_tail_call(true);
                        call.set_call_convention(TAILCC);
                        cxt.builder.build_return(None);
                    }
                }
            }
        }
    }
}
