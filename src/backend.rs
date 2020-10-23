use crate::ir::Ty;
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
        Backend {
            cxt,
            machine,
        }
    }

    pub fn codegen_module(&self, m: &crate::ir::Module) -> inkwell::module::Module {
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
    pub env: Vec<(Val, BasicTypeEnum<'cxt>)>,
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
            if let Node::Fun(Function { params, callee, .. }) = self.get(val).unwrap() {
                if let Node::FunType(_) = *self.get(*params.last().unwrap()).unwrap() {
                    let cont_n = params.len() as u8 - 1;
                    let &cont_p = self
                        .uses(val)
                        .iter()
                        .find(|&&x| *self.get(x).unwrap() == Node::Param(val, cont_n))
                        .expect("Continuation isn't used, I guess?");

                    let mut reqs = Vec::new();
                    let good = self.uses(cont_p).iter().all(|&u| {
                        // We can only replace the continuation with a call stack if the continuation is only called, not passed around.
                        match self.get(u).unwrap() {
                            Node::Fun(Function { callee, .. }) if *callee == cont_p => true,
                            // But, it can be passed as a continuation to another function that can use a call stack
                            Node::Fun(Function {
                                callee, call_args, ..
                            }) if call_args.iter().any(|&x| x == cont_p) => {
                                reqs.push(*callee);
                                true
                            }
                            _ => false,
                        }
                    });
                    // Also, we can only call functions that are guaranteed to return
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
                    // No continuation, so we won't use the call stack
                    modes.insert(val, FunMode::NoStack);
                }
            }
        }

        while let Some((val, reqs)) = modes.iter().find_map(|(&val, mode)| match mode {
            FunMode::Maybe(reqs) => Some((val, reqs)),
            _ => None,
        }) {
            let before = reqs.len();

            let mut okay = true;
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
                    Some(FunMode::Maybe(_)) => {
                        nreqs.push(v);
                    }
                }
            }

            if !okay {
                modes.insert(val, FunMode::NoStack);
            } else if nreqs.is_empty() {
                modes.insert(val, FunMode::YesStack);
            } else if nreqs.len() == before {
                // TODO is this actually what we want? What if we need to resolve other things first?
                eprintln!(
                    "[Durin] Warning: disabling stack for stuck function {}",
                    val.pretty(self)
                );
                modes.insert(val, FunMode::NoStack);
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

    fn llvm_ty<'cxt>(&self, val: Val, cxt: &Cxt<'cxt>) -> BasicTypeEnum<'cxt> {
        match self.get(val).unwrap() {
            Node::Const(c) => match c {
                crate::ir::Constant::TypeType => cxt.size_ty().as_basic_type_enum(),
                crate::ir::Constant::IntType(w) => {
                    cxt.cxt.custom_width_int_type(w.bits()).as_basic_type_enum()
                }
                crate::ir::Constant::Int(_, _) => unreachable!("not a type"),
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
            // Polymorphic
            Node::Param(_, _) => cxt.any_ty(),
            Node::Fun(_) | Node::BinOp(_, _, _) => unreachable!("not a type"),
        }
    }

    fn gen_value<'cxt>(&self, val: Val, cxt: &Cxt<'cxt>) -> BasicValueEnum<'cxt> {
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
                } = cxt.functions.get(&val).unwrap();

                // Create the environment struct, then store it in an alloca and bitcast the pointer to i8*
                // TODO heap allocation instead of alloca
                let env_tys: Vec<_> = env.iter().map(|&(_, ty)| ty).collect();
                let mut env_val = cxt.cxt.struct_type(&env_tys, false).get_undef();
                for (i, &(val, _)) in env.iter().enumerate() {
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
                let env = cxt.builder.build_bitcast(env_ptr, cxt.any_ty(), "env");

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
                    crate::ir::BinOp::IEq => cxt
                        .builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            a.into_int_value(),
                            b.into_int_value(),
                            name,
                        )
                        .as_basic_value_enum(),
                }
            }
        }
    }

    pub fn codegen<'cxt>(&self, cxt: &mut Cxt<'cxt>) {
        let stack_enabled = self.stack_enabled();

        // Codegen all functions visible from the top level, and everything reachable from there
        let mut to_gen: Vec<(Vec<(Val, Val)>, Val)> =
            self.top_level().map(|x| (Vec::new(), x)).collect();
        // This explicit for loop allows us to add to to_gen in the body of the loop
        let mut i = 0;
        while i < to_gen.len() {
            let (env, val) = to_gen[i].clone();
            i += 1;

            if let Node::Fun(fun) = self.get(val).unwrap() {
                // Codegen it

                // Everything in `scope` will either be generated as a basic block, or added to `to_gen`
                let scope = self.scope(val);

                // Figure out which functions in `scope` can be basic blocks, and add others to `to_gen`
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
                                    Node::Fun(f) => f.call_args.iter().all(|a| *a != x),
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
                                if !to_gen.iter().any(|(_, y)| *y == x) {
                                    // This function is in `val`'s scope, so it must use its parameters
                                    let env = fun
                                        .params
                                        .iter()
                                        .enumerate()
                                        .map(|(i, &ty)| {
                                            (
                                                self.uses(val)
                                                    .iter()
                                                    .find(|&&x| {
                                                        *self.get(x).unwrap()
                                                            == Node::Param(val, i as u8)
                                                    })
                                                    .copied()
                                                    .unwrap(),
                                                ty,
                                            )
                                        })
                                        .collect();
                                    to_gen.push((env, x));
                                }
                                None
                            }
                        } else {
                            // We'll materialize value nodes later
                            None
                        }
                    })
                    .collect();

                // The first basic block is the actual function body
                blocks.push_front((val, fun.clone()));

                let stack_enabled = stack_enabled.contains(&val);
                let args: Vec<_> = env
                    .iter()
                    .map(|(_, ty)| ty)
                    .chain(if stack_enabled {
                        &fun.params[0..fun.params.len() - 1]
                    } else {
                        &fun.params
                    })
                    .map(|&x| self.llvm_ty(x, cxt))
                    .collect();
                let cont = if stack_enabled {
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

                let known_ty = if stack_enabled {
                    let &ret_ty = fun.params.last().unwrap();
                    let ret_ty = match self.get(ret_ty).unwrap() {
                        Node::FunType(v) => {
                            if v.len() == 1 {
                                v[0]
                            } else {
                                todo!("return a tuple?")
                            }
                        }
                        _ => unreachable!(),
                    };
                    let ret_ty = self.llvm_ty(ret_ty, cxt);
                    ret_ty.fn_type(&args, false)
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

                // TODO only include live values in `env`
                let env = args[0..env.len()]
                    .iter()
                    .zip(env)
                    .map(|(&ty, (val, _))| (val, ty))
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
                let uentry = cxt.cxt.append_basic_block(*unknown, "entry");
                cxt.builder.position_at_end(uentry);

                // Unpack environment
                let &env_ptr = unknown.get_params().last().unwrap();
                // TODO wait, what about dependently sized types?
                let env_tys: Vec<_> = env.iter().map(|&(_, ty)| ty).collect();
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
                cxt.upvalues = HashMap::new();
                for (i, &(val, _)) in env.iter().enumerate() {
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
                // `gen_call` takes the continuation as a Val, not a BasicValueEnum; so, we use an unused Val slot and stick the BasicValueEnum in the upvalues map
                // Thing is, we can't call `self.reserve()` because we don't want to take `self` as mutable
                // But we only ever need one of these at once, so we use `Val::INVALID`, which exists for this purpose
                let cont = Val::INVALID;
                cxt.upvalues.insert(cont, args.pop().unwrap());
                self.gen_call(*val, args, Some(cont), &cxt);
            }

            let &fun = known;
            cxt.cont = *cont;

            let entry = cxt.cxt.append_basic_block(fun, "entry");
            cxt.builder.position_at_end(entry);

            // Remove any basic blocks and upvalues we generated last time, they're no longer accessible
            cxt.blocks = HashMap::new();
            cxt.upvalues = HashMap::new();

            // Add closed-over upvalues to the context
            for ((val, _ty), param) in env.iter().zip(fun.get_params()) {
                cxt.upvalues.insert(*val, param);
            }

            // Declare all blocks and their parameters first
            // Block parameters are stored in allocas, which will be removed with mem2reg
            for (bval, bfun) in blocks {
                let name = self
                    .name(*bval)
                    .cloned()
                    .unwrap_or_else(|| format!("block${}", val.num()));
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
                crate::ir::Constant::Int(_, _) => unreachable!("not a type"),
            },
            Node::FunType(_) => {
                let ptr = cxt
                    .builder
                    .build_bitcast(
                        any,
                        self.llvm_ty(ty, cxt).ptr_type(AddressSpace::Generic),
                        "ptr",
                    )
                    .into_pointer_value();
                cxt.builder.build_load(ptr, "fun")
            }
            // Leave as an "any" since it's polymorphic
            Node::Param(_, _) => any.as_basic_value_enum(),
            Node::BinOp(_, _, _) | Node::Fun(_) => unreachable!("not a type"),
        }
    }

    fn to_any<'cxt>(
        &self,
        val: BasicValueEnum<'cxt>,
        ty: Val,
        cxt: &Cxt<'cxt>,
    ) -> PointerValue<'cxt> {
        match self.get(ty).unwrap() {
            Node::Const(c) => match c {
                crate::ir::Constant::TypeType | crate::ir::Constant::IntType(_) => {
                    let val = val.into_int_value();
                    cxt.builder
                        .build_int_to_ptr(val, cxt.any_ty().into_pointer_type(), "cast")
                }
                crate::ir::Constant::Int(_, _) => unreachable!("not a type"),
            },
            Node::FunType(_) => {
                let ty = val.get_type();
                // TODO heap allocate instead
                let ptr = cxt.builder.build_alloca(ty, "cast_slot");
                cxt.builder.build_store(ptr, val);
                cxt.builder
                    .build_bitcast(ptr, cxt.any_ty(), "casted")
                    .into_pointer_value()
            }
            // Already as an "any" since it's polymorphic
            Node::Param(_, _) => val.into_pointer_value(),
            Node::BinOp(_, _, _) | Node::Fun(_) => unreachable!("not a type"),
        }
    }

    fn gen_call<'cxt>(
        &self,
        callee: Val,
        mut args: Vec<BasicValueEnum<'cxt>>,
        cont: Option<Val>,
        cxt: &Cxt<'cxt>,
    ) {
        // If we're calling the return continuation, emit a return instruction
        if cxt.cont == Some(callee) {
            if let Some(k) = cont {
                args.push(self.gen_value(k, cxt));
            }
            assert_eq!(args.len(), 1);
            cxt.builder.build_return(Some(&args[0]));
        // If we're calling a basic block, jump there
        } else if let Some((target, params)) = cxt.blocks.get(&callee) {
            if let Some(k) = cont {
                args.push(self.gen_value(k, cxt));
            }
            // Set the parameters and jump to the target block
            for (&ptr, value) in params.iter().zip(args) {
                cxt.builder.build_store(ptr, value);
            }
            cxt.builder.build_unconditional_branch(*target);
        // Otherwise, we're actually calling a function
        } else {
            // The mechanism depends on whether it's a known or unknown call
            match cxt.functions.get(&callee) {
                Some(LFunction {
                    known,
                    env,
                    stack_enabled,
                    ..
                }) => {
                    // Known call

                    // Prepend upvalues to the argument list
                    let mut args: Vec<_> = env
                        .iter()
                        .map(|&(val, _)| self.gen_value(val, cxt))
                        .chain(args)
                        .collect();

                    // The actual call depends on whether we're using the LLVM stack or not
                    if *stack_enabled {
                        let cont = cont.unwrap();
                        let call = cxt.builder.build_call(*known, &args, "stack_call");
                        call.set_tail_call(true);
                        call.set_call_convention(TAILCC);
                        self.gen_call(
                            cont,
                            vec![call.try_as_basic_value().left().unwrap()],
                            None,
                            cxt,
                        )
                    } else {
                        if let Some(k) = cont {
                            args.push(self.gen_value(k, cxt));
                        }
                        let call = cxt.builder.build_call(*known, &args, "call");
                        call.set_tail_call(true);
                        call.set_call_convention(TAILCC);
                        cxt.builder.build_return(None);
                    }
                }
                None => {
                    // Unknown call
                    if let Some(k) = cont {
                        args.push(self.gen_value(k, cxt));
                    }
                    let tys = match self.get(callee).unwrap().ty(self).inline(self) {
                        Ty::FunType(tys) => tys,
                        _ => unreachable!(),
                    };
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
                        .zip(tys)
                        .map(|(val, ty)| self.to_any(val, ty, cxt).as_basic_value_enum())
                        .collect();
                    // The closure environment is the last argument
                    args.push(env);

                    let call = cxt.builder.build_call(fun_ptr, &args, "closure_call");
                    call.set_tail_call(true);
                    call.set_call_convention(TAILCC);
                    cxt.builder.build_return(None);
                }
            }
        }
    }
}
