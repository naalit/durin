use crate::ir::{Function, Node, Val};
use inkwell::basic_block::BasicBlock;
use inkwell::IntPredicate;
use inkwell::{
    builder::Builder, context::Context, module::Module, targets::TargetMachine, types::*,
    values::*, AddressSpace,
};
use std::collections::{HashMap, HashSet, VecDeque};

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
pub struct LFunction<'cxt> {
    /// The arity of the function as written in Durin.
    /// So the LLVM unknown version has arity `arity+1`, and the known version has arity `arity-(if stack_enabled then 1 else 0)+env.len()`.
    pub arity: u32,
    pub known: FunctionValue<'cxt>,
    pub unknown: FunctionValue<'cxt>,
    pub env: Vec<(Val, BasicTypeEnum<'cxt>, Val)>,
    pub stack_enabled: bool,
    pub blocks: VecDeque<(Val, Function)>,
    pub cont: Option<Val>,
}

pub struct Cxt<'cxt> {
    pub cxt: &'cxt Context,
    pub builder: Builder<'cxt>,
    pub module: Module<'cxt>,
    pub machine: &'cxt TargetMachine,
    pub blocks: HashMap<Val, (BasicBlock<'cxt>, Vec<PointerValue<'cxt>>)>,
    pub functions: HashMap<Val, LFunction<'cxt>>,
    pub upvalues: HashMap<Val, BasicValueEnum<'cxt>>,
    /// Keeps track of the return continuation, if we're in a stack-enabled function
    pub cont: Option<Val>,
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

enum FunMode {
    /// This function can use the LLVM stack, which will replace the last parameter.
    YesStack,
    /// This function can't use the LLVM stack. It may or may not have a continuation parameter.
    NoStack,
    /// This function can use the LLVM stack if all these functions do as well.
    Maybe(Vec<Val>),
}

impl crate::ir::Module {
    // Figure out which functions can use the LLVM stack
    fn stack_enabled(&self) -> HashSet<Val> {
        let mut modes = HashMap::new();
        for val in self.vals() {
            // For a function to use the stack it must:
            // 1. be a function
            if let Node::Fun(Function { params, callee, .. }) = self.get(val).unwrap() {
                // 2. have a last parameter with a function type - the continuation - and use it
                let cont_p = if matches!(
                    params.last().and_then(|&x| self.get(x)),
                    Some(Node::FunType(_))
                ) {
                    let cont_n = params.len() as u8 - 1;
                    self.uses(val)
                        .iter()
                        .find(|&&x| *self.get(x).unwrap() == Node::Param(val, cont_n))
                        .copied()
                } else {
                    None
                };
                if let Some(cont_p) = cont_p {
                    // Instead of checking if other functions are stack-enabled, we add them to reqs, since they might be in any order
                    let mut reqs = Vec::new();
                    let good = self.uses(cont_p).iter().all(|&u| {
                        // 3. only use its continuation in known calls, not passing it around
                        match self.get(u).unwrap() {
                            Node::Fun(Function { callee, .. }) if *callee == cont_p => true,
                            // Although passing it as the continuation (last) parameter to another stack-enabled function is fine.
                            Node::Fun(Function {
                                callee, call_args, ..
                            }) if call_args.last().map_or(false, |&x| x == cont_p) => {
                                reqs.push(*callee);
                                true
                            }
                            _ => false,
                        }
                    });
                    // 4. only call other stack-enabled functions - we won't have a continuation to pass other functions
                    if !reqs.contains(callee) {
                        reqs.push(*callee);
                    }

                    if !good {
                        modes.insert(val, FunMode::NoStack);
                    } else {
                        if reqs.is_empty() {
                            modes.insert(val, FunMode::YesStack);
                        } else {
                            modes.insert(val, FunMode::Maybe(reqs));
                        }
                    }
                } else {
                    // This function doesn't have a continuation.
                    // It can still be stack-enabled as long as it only calls stack-enabled functions or their continuations.
                    if params.iter().any(|x| {
                        if let Node::FunType(_) = x.get(self) {
                            !self.uses(*x).is_empty()
                        } else {
                            false
                        }
                    }) {
                        // This function has a parameter of function type (and uses it), so it can't use the stack.
                        modes.insert(val, FunMode::NoStack);
                    } else {
                        let req = match callee.get(self) {
                            // Check if this is the last parameter of a function.
                            // If so, we require that *that* function is stack-enabled, so it has a continuation.
                            Node::Param(f, i) => {
                                if let Node::Fun(Function { params, .. }) = f.get(self) {
                                    if params.len() == *i as usize + 1 {
                                        Some(*f)
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                }
                            }
                            // The called function isn't a continuation, so we require that it's stack-enabled.
                            _ => Some(*callee),
                        };
                        if let Some(req) = req {
                            modes.insert(val, FunMode::Maybe(vec![req]));
                        } else {
                            modes.insert(val, FunMode::NoStack);
                        }
                    }
                }
            }
        }

        // Now look at requirements and figure out which functions can actually use the stack
        while let Some((val, reqs)) = modes.iter().find_map(|(&val, mode)| match mode {
            FunMode::Maybe(reqs) => Some((val, reqs)),
            _ => None,
        }) {
            let mut okay = true;
            // The new version of reqs - functions we're still waiting on
            let mut nreqs = Vec::new();
            for v in reqs.clone() {
                // Single recursion is fine
                if v == val {
                    continue;
                }
                match modes.get(&v) {
                    Some(FunMode::YesStack) => {
                        // We won't add it to nreqs, since we know it's good
                    }
                    // If it's None, it means it's an unknown function, which could be NoStack
                    Some(FunMode::NoStack) | None => {
                        okay = false;
                        break;
                    }
                    Some(FunMode::Maybe(rs)) => {
                        // Transfer that functions requirements to this one.
                        // We'll come back next iteration.
                        nreqs.extend(rs.iter().copied().filter(|&x| x != v && x != val));
                    }
                }
            }

            if !okay {
                modes.insert(val, FunMode::NoStack);
            } else if nreqs.is_empty() {
                modes.insert(val, FunMode::YesStack);
            } else {
                modes.insert(val, FunMode::Maybe(nreqs));
            }
        }

        modes
            .into_iter()
            .filter(|(_, m)| {
                if let FunMode::YesStack = m {
                    true
                } else {
                    false
                }
            })
            .map(|(v, _)| v)
            .collect()
    }

    /// The size that this type takes up on the *stack*
    fn static_size<'cxt>(&self, val: Val, cxt: &Cxt<'cxt>) -> u64 {
        match self.get(val).unwrap() {
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
            Node::ProdType(v) => v.iter().map(|&x| self.static_size(x, cxt)).sum(),
            Node::SumType(v) => v.iter().map(|&x| self.static_size(x, cxt)).max().unwrap(),
            Node::Param(_, _) => cxt.size_ty().get_bit_width() as u64 / 8,
            Node::Fun(_)
            | Node::BinOp(_, _, _)
            | Node::IfCase(_, _)
            | Node::Proj(_, _)
            | Node::Inj(_, _, _)
            | Node::Product(_, _)
            | Node::If(_) => {
                unreachable!("not a type")
            }
        }
    }

    fn llvm_ty<'cxt>(&self, val: Val, cxt: &Cxt<'cxt>) -> BasicTypeEnum<'cxt> {
        match self.get(val).unwrap() {
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
            Node::FunType(v) => {
                // The argument types don't matter, just the number
                let fun_ty = cxt.cxt.void_type().fn_type(
                    &v.iter()
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
            Node::ProdType(v) => {
                let v: Vec<_> = v.iter().map(|&x| self.llvm_ty(x, cxt)).collect();
                cxt.cxt.struct_type(&v, false).as_basic_type_enum()
            }
            Node::SumType(v) => {
                // TODO size probably isn't a constant
                let &payload = v.iter().max_by_key(|&&x| self.static_size(x, cxt)).unwrap();
                let payload = self.llvm_ty(payload, cxt);
                let tag = match v.len() {
                    // No tag if there's only one element
                    0..=1 => return payload,
                    2 => cxt.cxt.bool_type(),
                    3..=256 => cxt.cxt.i8_type(),
                    257..=65536 => cxt.cxt.i32_type(),
                    _ => cxt.cxt.i64_type(),
                };
                cxt.cxt
                    .struct_type(&[tag.as_basic_type_enum(), payload], false)
                    .as_basic_type_enum()
            }
            // Polymorphic
            Node::Param(_, _) => cxt.any_ty(),
            Node::Fun(_)
            | Node::BinOp(_, _, _)
            | Node::IfCase(_, _)
            | Node::Proj(_, _)
            | Node::Inj(_, _, _)
            | Node::Product(_, _)
            | Node::If(_) => {
                unreachable!("not a type")
            }
        }
    }

    fn gen_value<'cxt>(&self, val: Val, cxt: &Cxt<'cxt>) -> BasicValueEnum<'cxt> {
        let val = val.unredirect(self);

        if let Some(&v) = cxt.upvalues.get(&val) {
            return v;
        }
        match self.get(val).unwrap() {
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
                            .build_alloca(cxt.cxt.struct_type(&env_tys, false), "env_ptr");
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
                if matches!(self.get(*ty), Some(Node::SumType(v)) if v.len() == 1) {
                    // No tag or casting needed
                    return self.gen_value(*payload, cxt);
                }

                let payload = self.gen_value(*payload, cxt);
                let payload_ptr = cxt.builder.build_alloca(payload.get_type(), "payload.ptr");
                cxt.builder.build_store(payload_ptr, payload);

                let ty = self.llvm_ty(*ty, cxt).into_struct_type();
                let payload_ty = ty.get_field_type_at_index(1).unwrap();
                let payload_ptr = cxt
                    .builder
                    .build_bitcast(
                        payload_ptr,
                        payload_ty.ptr_type(AddressSpace::Generic),
                        "payload.ptr.casted",
                    )
                    .into_pointer_value();
                // This load can go past the alloca, but I don't think that causes any problems because we don't look at it.
                // TODO: We might want a larger alloca if this is actually undefined behaviour.
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
            Node::Param(f, i) => {
                let name = self.name(val).map(|x| x as &str).unwrap_or("param");
                let ptr = cxt.blocks.get(f).unwrap().1[*i as usize];
                cxt.builder.build_load(ptr, name)
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
            Node::BinOp(op, a, b) => {
                let a = self.gen_value(*a, cxt);
                let b = self.gen_value(*b, cxt);
                let name = self.name(val).map(|x| x as &str).unwrap_or("binop");
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
        let stack_enabled = self.stack_enabled();

        // Codegen all functions visible from the top level, and everything reachable from there
        let mut to_gen: Vec<(Val, Vec<(Val, crate::ir::Function)>)> =
            self.top_level().map(|x| (x, Vec::new())).collect();
        let scopes = self.top_level_scopes();
        // This explicit for loop allows us to add to to_gen in the body of the loop
        let mut i = 0;
        while i < to_gen.len() {
            let (val, blocks) = to_gen[i].clone();
            let env = self.env(val);
            i += 1;

            if let Node::Fun(fun) = self.get(val).unwrap() {
                // Codegen it

                // Everything in `scope` will either be generated as a basic block, or added to `to_gen`
                let scope = scopes.get(&val).cloned().unwrap_or_else(Vec::new);

                // Figure out which functions in `scope` can be basic blocks, and add others to `to_gen`
                let mut to_add = Vec::new();
                let mut not = HashSet::new();
                let mut blocks: VecDeque<_> = scope
                    .into_iter()
                    .filter_map(|x| {
                        // The body of the main function will be added separately
                        if x == val {
                            return None;
                        }
                        if let Some(Node::Fun(Function {
                            params,
                            callee,
                            call_args,
                        })) = self.get(x)
                        {
                            // A function is eligible for turning into a basic block if it doesn't call an unknown continuation - it always branches to a known destination.
                            let is_block = match self.get(*callee).unwrap() {
                                Node::Fun(_) => true,
                                Node::IfCase(_, _) | Node::If(_) => true,
                                Node::Const(crate::ir::Constant::Unreachable) => true,
                                // Calls a continuation parameter
                                Node::Param(f, _) if *f == x => false,
                                // Must be accessible from outside
                                Node::Param(_, _) => true,
                                // TODO detect if this is known from outside
                                _ => false,
                            }
                                // The function must also not be used as a first-class function (not passed around, just called)
                                // This is, in theory, an arbitrary LLVM-specific restriction
                                // In assembly and probably other IRs, basic blocks (labels) can be passed around just fine
                                && self.uses(x).iter().all(|&u| match self.get(u).unwrap() {
                                    Node::Fun(f) => f.call_args.iter().all(|a| *a != x)
                                        // Using it as an argument to if or ifcase doesn't count
                                        || matches!(self.get(f.callee), Some(Node::If(_)) | Some(Node::IfCase(_, _))),
                                    // Accessing its parameters is fine
                                    Node::Param(_, _) => true,
                                    _ => false,
                                });

                            if is_block {
                                Some((
                                    x,
                                    Function {
                                        params: params.clone(),
                                        callee: *callee,
                                        call_args: call_args.clone(),
                                    },
                                ))
                            } else {
                                // Mark it for generation, if it isn't marked already
                                if !to_add.iter().any(|(y, _)| *y == x) && !to_gen.iter().any(|(y, _)| *y == x) {
                                    to_add.push((x, Vec::new()));
                                }
                                // Things in its scope don't belong here, they'll be generated with it later
                                for i in scopes.get(&x).cloned().unwrap_or_else(Vec::new) {
                                    not.insert(i);
                                }
                                None
                            }
                        } else {
                            // We'll materialize value nodes later
                            None
                        }
                    })
                    // So we can borrow `not` again
                    .collect::<Vec<_>>()
                    .into_iter()
                    .chain(blocks)
                    .filter(|(x, _)| !not.contains(x))
                    .collect();

                // Copy any basic blocks that the function uses
                for (x, mut x_blocks) in to_add {
                    // If it's in something else's scope, we'll generate it later
                    if not.contains(&x) {
                        continue;
                    }

                    let mut xscope = scopes.get(&x).cloned().unwrap_or_else(Vec::new);
                    xscope.push(x);
                    let xscope: Vec<_> = xscope
                        .into_iter()
                        .flat_map(|x| x.get(self).args())
                        .collect();
                    for b in &blocks {
                        let &(v, _) = b;
                        let h: HashSet<_> = self.uses(v).iter().copied().collect();
                        if xscope.iter().any(|x| h.contains(&x)) {
                            x_blocks.push(b.clone());
                        }
                    }
                    to_gen.push((x, x_blocks));
                }

                // The first basic block is the actual function body
                blocks.push_front((val, fun.clone()));

                let stack_enabled = stack_enabled.contains(&val);
                let cont = if stack_enabled
                    && fun
                        .params
                        .last()
                        .and_then(|x| self.get(*x))
                        .map_or(false, |n| matches!(n, Node::FunType(_)))
                {
                    self.uses(val)
                        .iter()
                        .find(|&&x| match self.get(x).unwrap() {
                            Node::Param(_, i) => *i as usize == fun.params.len() - 1,
                            _ => false,
                        })
                        .copied()
                } else {
                    None
                };
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

                let known_ty = if cont.is_some() {
                    let &ret_ty = fun.params.last().unwrap();
                    match self.get(ret_ty).unwrap() {
                        Node::FunType(v) => {
                            let ret_ty = if v.len() == 1 {
                                v[0]
                            } else {
                                todo!("return a tuple?")
                            };
                            let ret_ty = self.llvm_ty(ret_ty, cxt);
                            ret_ty.fn_type(&args, false)
                        }
                        _ => unreachable!(),
                    }
                } else {
                    cxt.cxt.void_type().fn_type(&args, false)
                };

                let name = self
                    .name(val)
                    .cloned()
                    .unwrap_or_else(|| format!("fun${}", val.num()));
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
                        stack_enabled,
                    },
                );
            }
        }
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
        ) in &cxt.functions
        {
            // First generate the unknown version, which just delegates to the known version
            {
                // Remove any basic blocks and upvalues we generated last time, they're no longer accessible
                cxt.blocks = HashMap::new();
                cxt.upvalues = HashMap::new();

                let uentry = cxt.cxt.append_basic_block(*unknown, "entry");
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
                                    self.name(val).map(|x| x as &str).unwrap_or("upvalue"),
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
                    // Thing is, we can't call `self.reserve()` because we don't want to take `self` as mutable
                    // But we only ever need one of these at once, so we use `Val::INVALID`, which exists for this purpose
                    let cont = Val::INVALID;
                    cxt.upvalues.insert(cont, vcont);
                    self.gen_call(*val, None, args, Some(cont), &cxt);
                } else {
                    self.gen_call(*val, None, args, None, &cxt);
                }
            }

            let &fun = known;
            cxt.cont = *cont;

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
            for (bval, bfun) in blocks {
                let name = format!("{}${}", val.pretty(self), bval.pretty(self));
                let block = cxt.cxt.append_basic_block(fun, &name);
                let mut params = Vec::new();
                for &ty in &bfun.params {
                    let ty = self.llvm_ty(ty, cxt);
                    let name = self.param_name(*bval, i as u8);
                    let param = cxt.builder.build_alloca(ty, &name);
                    params.push(param);
                }
                cxt.blocks.insert(*bval, (block, params));
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
                let (block, _) = cxt.blocks.get(&bval).unwrap();
                cxt.builder.position_at_end(*block);

                // If we're calling if x, do that
                if let Some(Node::If(x)) = self.get(bfun.callee) {
                    let &x = x;
                    assert_eq!(bfun.call_args.len(), 2);
                    let fthen = bfun.call_args[0];
                    let felse = bfun.call_args[1];

                    let cond = self.gen_value(x, cxt).into_int_value();

                    let bstart = cxt.builder.get_insert_block().unwrap();
                    let bthen = cxt.cxt.insert_basic_block_after(bstart, "if.then");
                    let belse = cxt.cxt.insert_basic_block_after(bthen, "if.else");

                    cxt.builder.build_conditional_branch(cond, bthen, belse);

                    cxt.builder.position_at_end(bthen);
                    self.gen_call(fthen, None, vec![], None, cxt);

                    cxt.builder.position_at_end(belse);
                    self.gen_call(felse, None, vec![], None, cxt);
                // If we're calling ifcase i x, do that instead
                } else if let Some(Node::IfCase(i, x)) = self.get(bfun.callee) {
                    let (&i, &x) = (i, x);
                    let payload_ty = match x.get(self).clone().ty(self).get(self) {
                        Node::SumType(v) if v.len() == 1 => {
                            // There's no tag, and no casting needed
                            let x = self.gen_value(x, cxt);
                            assert_eq!(bfun.call_args.len(), 2);
                            let fthen = bfun.call_args[0];

                            self.gen_call(fthen, None, vec![x], None, cxt);

                            // Skip to the next basic block
                            continue;
                        }
                        Node::SumType(v) => v[i],
                        _ => unreachable!(),
                    };
                    assert_eq!(bfun.call_args.len(), 2);
                    let fthen = bfun.call_args[0];
                    let felse = bfun.call_args[1];

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
                    cxt.builder.build_store(payload_ptr, payload);
                    let payload_ptr = cxt.builder.build_bitcast(
                        payload_ptr,
                        payload_ty.ptr_type(AddressSpace::Generic),
                        "union.payload.casted_ptr",
                    );
                    let payload = cxt
                        .builder
                        .build_load(payload_ptr.into_pointer_value(), "union.payload.casted");
                    self.gen_call(fthen, None, vec![payload], None, cxt);

                    cxt.builder.position_at_end(belse);
                    self.gen_call(felse, None, vec![], None, cxt);
                } else {
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
                    self.gen_call(bfun.callee, None, args, bfun.call_args.last().copied(), cxt);
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
        match self.get(ty).unwrap() {
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
            // Leave as an "any" since it's polymorphic
            Node::Param(_, _) => any.as_basic_value_enum(),
            // TODO Proj should be allowed as a type
            Node::BinOp(_, _, _)
            | Node::Fun(_)
            | Node::IfCase(_, _)
            | Node::Proj(_, _)
            | Node::Inj(_, _, _)
            | Node::Product(_, _)
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
                // TODO heap allocate instead
                let ptr = cxt.builder.build_alloca(ty, "cast_slot");
                cxt.builder.build_store(ptr, val);
                cxt.builder
                    .build_bitcast(ptr, cxt.any_ty(), "casted")
                    .into_pointer_value()
            }
            BasicTypeEnum::PointerType(_) => val.into_pointer_value(),
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
        callee_ty: Option<Val>,
        mut args: Vec<BasicValueEnum<'cxt>>,
        cont: Option<Val>,
        cxt: &Cxt<'cxt>,
    ) {
        let tys = match callee_ty
            .unwrap_or_else(|| self.get(callee).unwrap().clone().ty(self))
            .get(self)
        {
            Node::FunType(tys) => tys.clone(),
            _ => unreachable!(),
        };

        // If we're calling the return continuation, emit a return instruction
        if cxt.cont == Some(callee) {
            if let Some(k) = cont {
                args.push(self.gen_value(k, cxt));
            }
            let args = args
                .into_iter()
                .zip(tys)
                .map(|(x, ty)| self.cast(x, ty, cxt))
                .collect::<Vec<_>>();
            assert_eq!(args.len(), 1);
            cxt.builder.build_return(Some(&args[0]));
        // If we're calling a basic block, jump there
        } else if let Some((target, params)) = cxt.blocks.get(&callee) {
            if let Some(k) = cont {
                args.push(self.gen_value(k, cxt));
            }
            let args = args
                .into_iter()
                .zip(tys)
                .map(|(x, ty)| self.cast(x, ty, cxt))
                .collect::<Vec<_>>();
            // Set the parameters and jump to the target block
            for (&ptr, value) in params.iter().zip(args) {
                cxt.builder.build_store(ptr, value);
            }
            cxt.builder.build_unconditional_branch(*target);
        // If we're stopping, return void
        } else if let Some(Node::Const(crate::ir::Constant::Stop)) = self.get(callee) {
            cxt.builder.build_return(None);
        // If we're calling unreachable, emit a LLVM unreachable instruction
        } else if let Some(Node::Const(crate::ir::Constant::Unreachable)) = self.get(callee) {
            cxt.builder.build_unreachable();
        // Otherwise, we're actually calling a function
        } else {
            // The mechanism depends on whether it's a known or unknown call
            match cxt.functions.get(&callee.unredirect(self)) {
                Some(LFunction {
                    known,
                    env,
                    stack_enabled,
                    cont: fcont,
                    ..
                }) => {
                    // Known call

                    // Prepend upvalues to the argument list
                    let cont_ty = tys.last().copied();
                    let args = args
                        .into_iter()
                        .zip(tys)
                        .map(|(x, ty)| self.cast(x, ty, cxt))
                        .collect::<Vec<_>>();
                    let mut args: Vec<_> = env
                        .iter()
                        .map(|&(val, _, _)| self.gen_value(val, cxt))
                        .chain(args)
                        .collect();

                    // The actual call depends on whether we're using the LLVM stack or not
                    if *stack_enabled && fcont.is_some() {
                        let cont = cont.unwrap();
                        let call = cxt.builder.build_call(*known, &args, "stack_call");
                        call.set_tail_call(true);
                        call.set_call_convention(TAILCC);
                        self.gen_call(
                            cont,
                            cont_ty,
                            vec![call.try_as_basic_value().left().unwrap()],
                            None,
                            cxt,
                        )
                    } else {
                        if let Some(k) = cont {
                            let v = self.gen_value(k, cxt);
                            let v = self.cast(v, cont_ty.unwrap(), cxt);
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
                    let args = args
                        .into_iter()
                        .zip(tys)
                        .map(|(x, ty)| self.cast(x, ty, cxt))
                        .collect::<Vec<_>>();
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
