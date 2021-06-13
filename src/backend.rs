use crate::emit::ValPretty;
use crate::ir::{Constant, Function, Name, Node, Slot, Slots, Uses, Val, ValExt, ValType};
use crate::ssa::{FunMode, SSA};
use inkwell::{
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    memory_buffer::MemoryBuffer,
    module::{Linkage, Module},
    targets::TargetMachine,
    types::*,
    values::*,
    AddressSpace, FloatPredicate, IntPredicate,
};
use specs::prelude::*;
use std::{
    cell::RefCell,
    collections::{HashMap, VecDeque},
    convert::{TryFrom, TryInto},
    path::Path,
};

mod types;
use types::*;

// Some calling conventions
pub const TAILCC: u32 = 18;
pub const CCC: u32 = 0;
pub const FASTCC: u32 = 8;
pub const DO_TAIL_CALL: bool = true;

pub struct Data<'a> {
    slots: ReadStorage<'a, Slot>,
    uses: ReadStorage<'a, Uses>,
    entities: Entities<'a>,
}

impl crate::ir::Module {
    pub fn compile_and_link(&mut self, out_file: &Path) -> Result<(), String> {
        let backend = Backend::native();
        let module = backend.codegen_module(self);
        let cxt = &backend.cxt;
        module.set_triple(&backend.machine.get_triple());

        // Create a wrapper around the program's main function if there is one
        let do_run = if let Some(f) = module.get_function("main") {
            f.as_global_value().set_name("pk$main");
            let ty = f.get_type().print_to_string();
            // Durin might or might not have succeeded in turning `main` into direct style
            let run = match ty.to_str().unwrap() {
                // () -> _ in CPS
                "void ({}, i8 addrspace(1)*)" => true,
                // () -> () in direct style
                "{} ({})" => true,
                t => {
                    eprintln!("Warning: main function has type {}, not wrapping it", t);
                    false
                }
            };
            if run {
                let new_fun = module.add_function("main", cxt.i32_type().fn_type(&[], false), None);
                new_fun.set_gc("statepoint-example");
                {
                    let b = cxt.create_builder();
                    let bl = cxt.append_basic_block(new_fun, "entry");
                    b.position_at_end(bl);

                    let initialize = module.get_function("initialize").unwrap();
                    let num_start_blocks = cxt.i32_type().const_int(8, false);
                    b.build_call(
                        initialize,
                        &[num_start_blocks.as_basic_value_enum()],
                        "_void",
                    );

                    if f.get_type().get_return_type().is_none() {
                        // CPS
                        // We need a tailcc stop function to pass as `main`'s continuation, as well as the start function
                        let any_ty = cxt.i8_type().gc_ptr().as_basic_type_enum();
                        let fun2 = module.add_function(
                            "$_stop",
                            cxt.void_type().fn_type(&[any_ty, any_ty], false),
                            None,
                        );
                        fun2.set_call_conventions(TAILCC);

                        let fun_ty = fun2
                            .get_type()
                            .ptr_type(AddressSpace::Generic)
                            .as_basic_type_enum();
                        let clos = module.add_global(fun_ty, None, "stop_closure");
                        clos.set_initializer(&fun_ty.const_zero());
                        let clos = clos.as_pointer_value();
                        b.build_store(clos, fun2.as_global_value().as_pointer_value());
                        let clos =
                            b.build_pointer_cast(clos, cxt.i8_type().gc_ptr(), "stop_clos_ptr");
                        // Callers expect a pointer to the header
                        let clos = unsafe {
                            b.build_gep(
                                clos,
                                &[cxt.i64_type().const_int((-8i64) as u64, true)],
                                "stop_clos_header",
                            )
                        };

                        let unit = cxt
                            .struct_type(&[], false)
                            .get_undef()
                            .as_basic_value_enum();
                        let call =
                            b.build_call(f, &[unit, clos.as_basic_value_enum()], "main_call");
                        call.set_call_convention(TAILCC);
                        b.build_return(Some(&cxt.i32_type().const_zero()));

                        let bl2 = cxt.append_basic_block(fun2, "entry");
                        b.position_at_end(bl2);
                        b.build_return(None);
                    } else {
                        // Direct style
                        let unit = cxt
                            .struct_type(&[], false)
                            .get_undef()
                            .as_basic_value_enum();
                        let call = b.build_call(f, &[unit], "main_call");
                        call.set_call_convention(TAILCC);
                        call.set_tail_call(true);
                        b.build_return(Some(&cxt.i32_type().const_zero()));
                    }
                }
            }
            run
        } else {
            false
        };

        #[cfg(not(feature = "llvm-13"))]
        module.verify().map_err(|s| s.to_string())?;

        // Call out to clang to compile and link it
        {
            use std::io::Write;
            use std::process::*;
            let buffer = module.write_bitcode_to_memory();
            // We shouldn't need to store the runtime in a file, we could just pipe both files to clang's stdin
            // But we would need to somehow send an EOF without closing the pipe
            {
                use std::fs::File;
                let runtime = include_bytes!(concat!(env!("OUT_DIR"), "/runtime.bc"));
                let path: &Path = "_pika_runtime.bc".as_ref();
                // TODO what if we update the runtime and it's outdated?
                if !path.exists() {
                    let mut runtime_bc = File::create(path).unwrap();
                    runtime_bc.write_all(runtime).unwrap();
                }
            }

            #[cfg(feature = "llvm-13")]
            let opt = concat!(env!("LLVM_DIR"), "/opt");
            #[cfg(not(feature = "llvm-13"))]
            let opt = "opt";

            #[cfg(feature = "llvm-13")]
            let llc = concat!(env!("LLVM_DIR"), "/llc");
            #[cfg(not(feature = "llvm-13"))]
            let llc = "llc";

            let objfile = {
                let mut objfile = out_file.to_path_buf();
                let mut name = objfile.file_name().unwrap().to_os_string();
                name.push(".o");
                objfile.set_file_name(name);
                objfile
            };

            let mut opt = Command::new(opt)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .arg("--passes=default<O3>,rewrite-statepoints-for-gc,instcombine")
                .spawn()
                .map_err(|e| format!("Failed to launch opt: {}", e))?;
            let mut stdin = opt.stdin.as_ref().unwrap();
            stdin
                .write_all(buffer.as_slice())
                .expect("Failed to pipe bitcode to opt");

            let mut llc = Command::new(llc)
                .stdin(opt.stdout.take().unwrap())
                .args(&["-O3", "-filetype=obj", "--relocation-model=pic", "-o"])
                .arg(&objfile)
                .spawn()
                .map_err(|e| format!("Failed to launch llc: {}", e))?;

            let code = opt
                .wait()
                .map_err(|e| format!("Failed to wait on opt process: {}", e))?
                .code()
                .unwrap_or(0);
            if code != 0 {
                return Err(format!("Call to opt exited with error code {}", code));
            }
            let code = llc
                .wait()
                .map_err(|e| format!("Failed to wait on llc process: {}", e))?
                .code()
                .unwrap_or(0);
            if code != 0 {
                return Err(format!("Call to llc exited with error code {}", code));
            }

            // No need to link if it doesn't have a main function
            if do_run {
                let mut clang = Command::new("clang")
                    .stdin(Stdio::piped())
                    .args(&["-O3", "-g", "_pika_runtime.bc", "-z", "notext", "-o"])
                    .args(&[out_file, &objfile])
                    .spawn()
                    .map_err(|e| format!("Failed to launch clang: {}", e))?;
                let code = clang
                    .wait()
                    .map_err(|e| format!("Failed to wait on clang process: {}", e))?
                    .code()
                    .unwrap_or(0);
                if code != 0 {
                    return Err(format!("Call to clang exited with error code {}", code));
                }
            }
        }

        Ok(())
    }
}

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
        m.add_types();
        let cxt = self.cxt();
        let mut dispatcher = DispatcherBuilder::new()
            .with(SSA, "ssa", &[])
            .with_thread_local(&cxt)
            .build();
        dispatcher.setup(&mut m.world);
        dispatcher.dispatch(&m.world);

        drop(dispatcher);

        cxt.module
    }

    /// Creates a `Cxt` for code generation, which borrows the `Backend`.
    pub fn cxt(&self) -> Cxt {
        Cxt::new(&self.cxt, &self.machine)
    }
}

trait InkwellTyExt<'a> {
    fn gc_ptr(&self) -> PointerType<'a>;
}
impl<'a, T: BasicType<'a>> InkwellTyExt<'a> for T {
    fn gc_ptr(&self) -> PointerType<'a> {
        self.ptr_type(AddressSpace::try_from(1).unwrap())
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
    pub env: Vec<(Val, BasicTypeEnum<'cxt>, Type<'cxt>)>,
    pub blocks: VecDeque<(Val, Function)>,
    pub cont: Option<(Val, Vec<Type<'cxt>>)>,
    pub param_tys: Vec<Type<'cxt>>,
}

pub struct Cxt<'cxt> {
    pub cxt: &'cxt Context,
    pub builder: Builder<'cxt>,
    pub module: Module<'cxt>,
    pub machine: &'cxt TargetMachine,
    pub blocks: RefCell<HashMap<Val, (BasicBlock<'cxt>, Vec<PointerValue<'cxt>>, Vec<Type<'cxt>>)>>,
    pub functions: RefCell<HashMap<Val, LFunction<'cxt>>>,
    pub upvalues: RefCell<HashMap<Val, BasicValueEnum<'cxt>>>,
    /// Keeps track of the return continuation, if we're in a stack-enabled function
    pub cont: RefCell<Option<(Val, Vec<Type<'cxt>>)>>,
}
impl<'cxt> Cxt<'cxt> {
    pub fn alloc(
        &self,
        size: IntValue<'cxt>,
        header: PointerValue<'cxt>,
        name: &str,
    ) -> PointerValue<'cxt> {
        let gc_alloc = self.module.get_function("gc_alloc").unwrap();
        let call = self.builder.build_call(
            gc_alloc,
            &[size.as_basic_value_enum(), header.as_basic_value_enum()],
            name,
        );
        call.set_call_convention(FASTCC);
        call.try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value()
    }

    /// LLVM doesn't understand `inttoptr` to a GC pointer, so we need to wrap it in a `noinline` function which doesn't use GC.
    #[cfg(not(feature = "llvm-13"))]
    pub fn inttoptr(&self, i: IntValue<'cxt>) -> PointerValue<'cxt> {
        let i = self
            .builder
            .build_int_z_extend_or_bit_cast(i, self.cxt.i64_type(), "to_i64");
        let fun = if let Some(fun) = self.module.get_function("$_i2p") {
            fun
        } else {
            use inkwell::attributes::*;
            let ty = self
                .any_ty()
                .fn_type(&[self.cxt.i64_type().as_basic_type_enum()], false);
            let fun = self
                .module
                .add_function("$_i2p", ty, Some(Linkage::Private));
            fun.add_attribute(
                AttributeLoc::Function,
                self.cxt
                    .create_enum_attribute(Attribute::get_named_enum_kind_id("noinline"), 0),
            );

            let bb = self.cxt.append_basic_block(fun, "entry");
            let before = self.builder.get_insert_block().unwrap();
            self.builder.position_at_end(bb);
            let ptr = self.builder.build_int_to_ptr(
                fun.get_first_param().unwrap().into_int_value(),
                self.cxt.i8_type().ptr_type(AddressSpace::Generic),
                "inttoptr",
            );
            let ptr = self.builder.build_pointer_cast(
                ptr,
                self.any_ty().into_pointer_type(),
                "inttoptr_gc",
            );
            self.builder.build_return(Some(&ptr));

            self.builder.position_at_end(before);
            fun
        };
        let call = self
            .builder
            .build_call(fun, &[i.as_basic_value_enum()], "inttoptr");
        call.as_any_value_enum().into_pointer_value()
    }

    #[cfg(feature = "llvm-13")]
    pub fn inttoptr(&self, i: IntValue<'cxt>) -> PointerValue<'cxt> {
        self.builder.build_int_to_ptr(i, self.any_ty().into_pointer_type(), "inttoptr")
    }

    #[cfg(not(feature = "llvm-13"))]
    pub fn ptrtoint(&self, ptr: PointerValue<'cxt>) -> IntValue<'cxt> {
        let ptr = self.builder.build_pointer_cast(
            ptr,
            self.cxt.i8_type().ptr_type(AddressSpace::Generic),
            "raw_pointer",
        );
        self.builder
            .build_ptr_to_int(ptr, self.size_ty(), "ptrtoint")
    }
    
    #[cfg(feature = "llvm-13")]
    pub fn ptrtoint(&self, ptr: PointerValue<'cxt>) -> IntValue<'cxt> {
        self.builder
            .build_ptr_to_int(ptr, self.size_ty(), "ptrtoint")
    }

    pub fn if_expr(
        &self,
        cond: IntValue<'cxt>,
        fthen: impl FnOnce() -> BasicValueEnum<'cxt>,
        felse: impl FnOnce() -> BasicValueEnum<'cxt>,
    ) -> BasicValueEnum<'cxt> {
        let bstart = self.builder.get_insert_block().unwrap();
        let bthen = self.cxt.insert_basic_block_after(bstart, "if.then");
        let belse = self.cxt.insert_basic_block_after(bthen, "if.else");
        let bmerge = self.cxt.insert_basic_block_after(belse, "if.merge");

        self.builder.build_conditional_branch(cond, bthen, belse);

        self.builder.position_at_end(bthen);
        let pthen = fthen();
        self.builder.build_unconditional_branch(bmerge);

        self.builder.position_at_end(belse);
        let pelse = felse();
        self.builder.build_unconditional_branch(bmerge);

        self.builder.position_at_end(bmerge);
        let phi = self.builder.build_phi(pthen.get_type(), "if.phi");
        phi.add_incoming(&[(&pthen, bthen), (&pelse, belse)]);

        phi.as_basic_value()
    }

    pub fn if_stmt(&self, cond: IntValue<'cxt>, fthen: impl FnOnce(), felse: impl FnOnce()) {
        let bstart = self.builder.get_insert_block().unwrap();
        let bthen = self.cxt.insert_basic_block_after(bstart, "if.then");
        let belse = self.cxt.insert_basic_block_after(bthen, "if.else");
        let bmerge = self.cxt.insert_basic_block_after(belse, "if.merge");

        self.builder.build_conditional_branch(cond, bthen, belse);

        self.builder.position_at_end(bthen);
        fthen();
        self.builder.build_unconditional_branch(bmerge);

        self.builder.position_at_end(belse);
        felse();
        self.builder.build_unconditional_branch(bmerge);

        self.builder.position_at_end(bmerge);
    }

    pub fn push_val(&self, key: Val, val: BasicValueEnum<'cxt>) {
        self.upvalues.borrow_mut().insert(key, val);
    }

    pub fn pop_val(&self, key: Val) {
        self.upvalues.borrow_mut().remove(&key);
    }

    pub fn new(cxt: &'cxt Context, machine: &'cxt TargetMachine) -> Self {
        let module = cxt
            .create_module_from_ir(MemoryBuffer::create_from_memory_range(
                include_bytes!(concat!(env!("OUT_DIR"), "/prelude.bc")),
                "main",
            ))
            .unwrap();

        Cxt {
            cxt,
            builder: cxt.create_builder(),
            module,
            machine,
            blocks: Default::default(),
            functions: Default::default(),
            upvalues: Default::default(),
            cont: RefCell::new(None),
        }
    }

    fn to_any(
        &self,
        ty: &Type<'cxt>,
        val: BasicValueEnum<'cxt>,
        data: &Data,
    ) -> PointerValue<'cxt> {
        match ty {
            // Already a pointer, just do a bitcast to make sure it's the right type
            Type::Pointer
            | Type::PtrStruct(_)
            | Type::PtrEnum(_)
            | Type::Unknown(_)
            | Type::Unknown2(_)
            | Type::Type
            // | Type::Closure(_)
            | Type::ExternFun(_, _) => self
                .builder
                .build_bitcast(val, self.any_ty(), "to_any")
                .into_pointer_value(),

            // It's an integer, so do an inttoptr
            Type::Int(bits) if *bits < 64 => {
                let val = val.into_int_value();
                let val = self.builder.build_int_z_extend_or_bit_cast(val, self.cxt.i64_type(), "to_i64");
                let val = self.builder.build_left_shift(
                    val,
                    val.get_type().const_int(1, false),
                    "int_shl",
                );
                let val =
                    self.builder
                        .build_or(val, val.get_type().const_int(1, false), "int_mark");
                self.inttoptr(val)
            }
            Type::Float(crate::ir::FloatType::F32) => {
                let val = self.builder.build_bitcast(val, self.cxt.i32_type(), "to_i32").into_int_value();
                let val = self.builder.build_int_z_extend_or_bit_cast(val, self.cxt.i64_type(), "to_i64");
                let val = self.builder.build_left_shift(
                    val,
                    val.get_type().const_int(1, false),
                    "int_shl",
                );
                let val =
                    self.builder
                        .build_or(val, val.get_type().const_int(1, false), "int_mark");
                self.inttoptr(val)
            }

            // Allocate and call `store`
            Type::StackStruct(_) | Type::StackEnum(_, _) | Type::Int(_) | Type::Closure(_) | Type::Float(crate::ir::FloatType::F64) => {
                let size = ty.heap_size(self, data);
                let alloc = self.alloc(size, ty.as_rtti(self, data), "any_slot");
                let slot = unsafe {
                    self.builder.build_in_bounds_gep(alloc, &[self.size_ty().const_int(8,  false)], "store_slot")
                };
                self.store(ty, val, slot, data);
                alloc
            }
        }
    }

    fn from_any(
        &self,
        ty: &Type<'cxt>,
        ptr: PointerValue<'cxt>,
        data: &Data,
    ) -> BasicValueEnum<'cxt> {
        match ty {
            // Already a pointer, just do a bitcast to make sure it's the right type
            Type::Pointer
            | Type::PtrStruct(_)
            | Type::PtrEnum(_)
            | Type::Unknown(_)
            | Type::Unknown2(_)
            | Type::Type
            // | Type::Closure(_)
            | Type::ExternFun(_, _) => {
                let lty = ty.llvm_ty(self);
                self.builder.build_bitcast(ptr, lty, "from_any")
            }

            // It's an integer, so do an ptrtoint
            Type::Int(bits) if *bits < 64 => {
                let int_type = self.cxt.custom_width_int_type(*bits);
                let val = self.ptrtoint(ptr);
                // TODO check signedness
                let val = self.builder.build_right_shift(
                    val,
                    val.get_type().const_int(1, false),
                    true,
                    "int_unmarked",
                );
                let val = self.builder.build_int_truncate_or_bit_cast(val, int_type, "to_i");
                val.as_basic_value_enum()
            }
            Type::Float(crate::ir::FloatType::F32) => {
                let val = self.ptrtoint(ptr);
                // TODO check signedness
                let val = self.builder.build_right_shift(
                    val,
                    val.get_type().const_int(1, false),
                    true,
                    "int_unmarked",
                );
                let val = self.builder.build_int_truncate_or_bit_cast(val, self.cxt.i32_type(), "to_i");
                self.builder.build_bitcast(val, self.cxt.f32_type(), "to_f32")
                    .as_basic_value_enum()
            }

            // Load from the pointer
            Type::StackStruct(_) | Type::StackEnum(_, _) | Type::Int(_) | Type::Closure(_) | Type::Float(crate::ir::FloatType::F64)=> {
                let ptr = unsafe {
                    self.builder.build_in_bounds_gep(ptr, &[self.size_ty().const_int(8,  false)], "load_slot")
                };
                self.load(ty, ptr, data)
            }
        }
    }

    /// Like from_any, but `from` is an actual pointer, not just something pointer-shaped.
    /// Small values that would otherwise be bitcasted to and from pointers will instead be actually loaded.
    /// The inverse of `store`, and also `gen_at`.
    fn load(&self, ty: &Type<'cxt>, from: PointerValue<'cxt>, data: &Data) -> BasicValueEnum<'cxt> {
        match ty {
            // Actually load
            Type::Pointer
            | Type::StackEnum(_, _)
            | Type::Int(_)
            | Type::Float(_)
            | Type::Closure(_)
            | Type::ExternFun(_, _)
            | Type::Type => {
                let lty = ty.llvm_ty(self);
                let from = self
                    .builder
                    .build_bitcast(from, lty.gc_ptr(), "casted_load_slot")
                    .into_pointer_value();
                self.builder.build_load(from, "load")
            }

            Type::StackStruct(v) => {
                let mut ptr = from;
                let mut size = self.size_ty().const_zero();
                let mut agg = ty.llvm_ty(self).into_struct_type().get_undef();
                for (i, (param, ty)) in v.iter().enumerate() {
                    let align = ty.alignment();
                    let padding = self.padding_llvm(size, align);
                    size = self.builder.build_int_add(size, padding, "padded_size");
                    ptr = unsafe {
                        self.builder
                            .build_in_bounds_gep(ptr, &[padding], "padded_member_slot")
                    };

                    let member = self.load(ty, ptr, data);
                    let isize = ty.heap_size(self, data);
                    if let Some(param) = param {
                        self.push_val(*param, member);
                    }
                    agg = self
                        .builder
                        .build_insert_value(agg, member, i.try_into().unwrap(), "struct_load")
                        .unwrap()
                        .into_struct_value();
                    size = self.builder.build_int_add(size, isize, "struct_size");
                    ptr = unsafe {
                        self.builder
                            .build_in_bounds_gep(ptr, &[isize], "next_member_slot")
                    };
                }
                for (param, _) in v {
                    if let Some(param) = param {
                        self.pop_val(*param);
                    }
                }
                agg.as_basic_value_enum()
            }

            Type::Unknown(_) | Type::Unknown2(_) | Type::PtrStruct(_) | Type::PtrEnum(_) => {
                let size = ty.heap_size(self, data);
                let fits = self.builder.build_int_compare(
                    IntPredicate::ULT,
                    size,
                    self.size_ty().const_int(8, false),
                    "fits_in_word",
                );
                self.if_expr(
                    fits,
                    || {
                        // It's represented by a bitcasted something else on the stack, not just a pointer
                        // So load it from the pointer
                        let lty = ty.llvm_ty(self);
                        let from = self
                            .builder
                            .build_bitcast(from, lty.gc_ptr(), "casted_load_slot")
                            .into_pointer_value();
                        self.builder.build_load(from, "load")
                    },
                    || {
                        // Reallocate and copy: we don't allow interior pointers besides temporarily
                        let header = ty.as_rtti(self, data);
                        let alloc = self.alloc(size, header, "realloc");
                        let to = unsafe {
                            self.builder.build_in_bounds_gep(
                                alloc,
                                &[self.size_ty().const_int(8, false)],
                                "to_slot",
                            )
                        };
                        self.builder
                            .build_memcpy(to, 8, from, ty.alignment(), size)
                            .unwrap();
                        alloc.as_basic_value_enum()
                    },
                )
            }
        }
    }

    /// Stores the value `from` of type `ty` at the pointer `to` so that a future call to `load(to)` can recover it.
    /// It should take up the size specified in `ty.runtime_size()`.
    fn store(
        &self,
        ty: &Type<'cxt>,
        from: BasicValueEnum<'cxt>,
        to: PointerValue<'cxt>,
        data: &Data,
    ) {
        match ty {
            // Store
            Type::Pointer
            | Type::StackEnum(_, _)
            | Type::Int(_)
            | Type::Float(_)
            | Type::Closure(_)
            | Type::ExternFun(_, _)
            | Type::Type => {
                let lty = from.get_type();
                let to = self
                    .builder
                    .build_pointer_cast(to, lty.gc_ptr(), "casted_store_slot");
                self.builder.build_store(to, from);
            }

            Type::StackStruct(v) => {
                let mut ptr = to;
                let mut size = self.size_ty().const_zero();
                let agg = from.into_struct_value();
                for (i, (param, ty)) in v.iter().enumerate() {
                    let align = ty.alignment();
                    let padding = self.padding_llvm(size, align);
                    size = self.builder.build_int_add(size, padding, "padded_size");
                    ptr = unsafe {
                        self.builder
                            .build_in_bounds_gep(ptr, &[padding], "padded_member_slot")
                    };

                    let member = self
                        .builder
                        .build_extract_value(agg, i.try_into().unwrap(), "member_to_store")
                        .unwrap();
                    param.map(|p| self.push_val(p, member));
                    self.store(ty, member, ptr, data);

                    let isize = ty.heap_size(self, data);
                    size = self.builder.build_int_add(size, isize, "struct_size");
                    ptr = unsafe {
                        self.builder
                            .build_in_bounds_gep(ptr, &[isize], "next_member_slot")
                    };
                }
                for (param, _) in v {
                    param.map(|p| self.pop_val(p));
                }
            }

            Type::Unknown(_) | Type::Unknown2(_) | Type::PtrStruct(_) | Type::PtrEnum(_) => {
                let size = ty.heap_size(self, data);
                let fits = self.builder.build_int_compare(
                    IntPredicate::ULT,
                    size,
                    self.size_ty().const_int(8, false),
                    "fits_in_word",
                );
                self.if_stmt(
                    fits,
                    || {
                        // It's represented by a bitcasted something else on the stack, not just a pointer
                        // So just store the pointer
                        let lty = from.get_type();
                        let to =
                            self.builder
                                .build_pointer_cast(to, lty.gc_ptr(), "casted_store_slot");
                        self.builder.build_store(to, from);
                    },
                    || {
                        // Copy the data this points to to the new location
                        let align = ty.alignment().max(1);
                        // `from` is a pointer to the header
                        let from = unsafe {
                            self.builder.build_in_bounds_gep(
                                from.into_pointer_value(),
                                &[self.size_ty().const_int(8, false)],
                                "store_slot",
                            )
                        };
                        self.builder
                            .build_memcpy(to, align, from, align, size)
                            .unwrap();
                    },
                )
            }
        }
    }

    fn gen_struct(&self, values: &[Val], vty: &Type<'cxt>, ptr: PointerValue<'cxt>, data: &Data) {
        match vty {
            Type::StackStruct(v) | Type::PtrStruct(v) => {
                let mut size = self.size_ty().const_zero();
                let mut padding = Vec::new();
                for (p, i) in v {
                    let x = i.heap_size(self, data);
                    let align = i.alignment();
                    if align > 0 {
                        let pad = self.padding_llvm(size, align);
                        padding.push((p, i, x, Some(pad)));
                        size = self.builder.build_int_add(size, pad, "aligned_size");
                    } else {
                        padding.push((p, i, x, None));
                    }
                    size = self.builder.build_int_add(size, x, "struct_size");
                }

                let mut next = ptr;
                for (&val, (param, ty, size, padding)) in values.iter().zip(padding) {
                    if let Some(padding) = padding {
                        next = unsafe {
                            self.builder
                                .build_in_bounds_gep(next, &[padding], "member_slot_padded")
                        };
                    }
                    if let Some(param) = param {
                        // Is it better to gen it twice, or just store this?
                        self.push_val(*param, self.gen_value(val, data));
                    }
                    self.gen_at(val, &ty, next, data);
                    next = unsafe {
                        self.builder
                            .build_in_bounds_gep(next, &[size], "next_member_slot")
                    };
                }
                for (p, _) in v {
                    if let Some(p) = p {
                        self.pop_val(*p);
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    /// Like gen_value, but store the result at `ptr`.
    /// Avoids allocating and copying when creating boxed values.
    /// It should take up the size specified in `vty.runtime_size()`.
    fn gen_at(&self, val: Val, vty: &Type<'cxt>, ptr: PointerValue<'cxt>, data: &Data) {
        let val = data.slots.unredirect(val);

        if let Some(&v) = self.upvalues.borrow().get(&val) {
            self.store(vty, v, ptr, data);
            return;
        }
        match data.slots.node(val).unwrap() {
            // Projection can be a memcpy instead of a store+load
            // LLVM will figure out the most efficient way to do it
            Node::Proj(ty, x, idx) => {
                let ty = self.as_type(*ty, data);
                match &ty {
                    Type::StackStruct(v) | Type::PtrStruct(v) => {
                        // TODO only compute the size once, and use bitwise and instead of alloca
                        let size = ty.heap_size(self, data);
                        let fits = self.builder.build_int_compare(
                            IntPredicate::ULT,
                            size,
                            self.size_ty().const_int(8, false),
                            "fits_in_word",
                        );
                        let val = self.gen_value(*x, data);
                        let mut ptr2 = self
                            .if_expr(
                                fits,
                                || {
                                    // If it fits in a word, put it in an alloca so we can still work with a pointer
                                    let ptr =
                                        self.builder.build_alloca(self.size_ty(), "proj_slot");
                                    let val = self.ptrtoint(ptr);
                                    let val = self.builder.build_right_shift(
                                        val,
                                        self.size_ty().const_int(1, false),
                                        false,
                                        "proj_val_unmarked",
                                    );
                                    self.builder.build_store(ptr, val);
                                    self.builder
                                        .build_pointer_cast(
                                            ptr,
                                            self.any_ty().into_pointer_type(),
                                            "proj_slot_casted",
                                        )
                                        .as_basic_value_enum()
                                },
                                // `val` is a pointer to the header, we need a pointer to the fields
                                || unsafe {
                                    self.builder
                                        .build_in_bounds_gep(
                                            val.into_pointer_value(),
                                            &[self.size_ty().const_int(8, false)],
                                            "store_slot",
                                        )
                                        .as_basic_value_enum()
                                },
                            )
                            .into_pointer_value();

                        let mut size = self.size_ty().const_zero();
                        for (i, (param, ty)) in v.iter().enumerate() {
                            let x = ty.heap_size(self, data);
                            let align = ty.alignment();
                            if align > 0 {
                                let padding = self.padding_llvm(size, align);
                                ptr2 = unsafe {
                                    self.builder.build_in_bounds_gep(
                                        ptr2,
                                        &[padding],
                                        "member_slot_padded",
                                    )
                                };
                                size = self.builder.build_int_add(size, padding, "aligned_size");
                            }
                            if i == *idx {
                                self.builder
                                    .build_memcpy(ptr, align, ptr2, align, x)
                                    .unwrap();
                                return;
                            } else {
                                if let Some(param) = param {
                                    let p = self.load(&ty, ptr2, data);
                                    self.push_val(*param, p);
                                }
                                ptr2 = unsafe {
                                    self.builder
                                        .build_in_bounds_gep(ptr2, &[x], "next_member_slot")
                                };
                            }
                            size = self.builder.build_int_add(size, x, "struct_size");
                        }
                    }
                    _ => unreachable!(),
                }
            }

            // Creating a sum or product type can be done directly in the pointer
            Node::Inj(ty, i, payload) => {
                if matches!(data.slots.node(*ty), Some(Node::SumType(v)) if v.len() == 1) {
                    // Just do a load+store
                    let v = self.gen_value(val, data);
                    self.store(vty, v, ptr, data);
                }

                match &vty {
                    Type::StackEnum(_, v) | Type::PtrEnum(v) => {
                        let size = vty.heap_size(self, data);
                        let fits = self.builder.build_int_compare(
                            IntPredicate::ULT,
                            size,
                            self.size_ty().const_int(8, false),
                            "fits_in_word",
                        );

                        self.if_stmt(
                            fits,
                            || {
                                // Just do a load+store
                                let v = self.gen_value(val, data);
                                self.store(vty, v, ptr, data);
                            },
                            || {
                                let align = v.iter().map(|t| t.alignment()).max().unwrap_or(0);
                                let tag = tag_bytes(v.len());
                                if tag != 0 {
                                    let tag = tag.max(align);
                                    let tag = tag * 8;
                                    let tag = self.cxt.custom_width_int_type(tag);
                                    let tag_slot =
                                        self.builder.build_bitcast(ptr, tag.gc_ptr(), "tag_slot");
                                    let tag = tag.const_int(*i as u64, false).as_basic_value_enum();
                                    self.builder.build_store(tag_slot.into_pointer_value(), tag);
                                }

                                let payload_slot = unsafe {
                                    self.builder.build_in_bounds_gep(
                                        ptr,
                                        &[self.size_ty().const_int(tag.into(), false)],
                                        "payload_slot",
                                    )
                                };
                                self.gen_at(*payload, &v[*i], payload_slot, data);
                            },
                        )
                    }
                    _ => unreachable!(),
                }
            }
            Node::Product(_, values) => self.gen_struct(values, vty, ptr, data),

            // For anything else, fall back to generating the value normally and storing it
            _ => {
                let v = self.gen_value(val, data);
                self.store(vty, v, ptr, data);
            }
        }
    }

    fn gen_value(&self, val: Val, data: &Data) -> BasicValueEnum<'cxt> {
        self.try_gen_value(val, data)
            .unwrap_or_else(|| panic!("Failed to gen_value %{}", val.id()))
    }

    fn try_gen_value(&self, val: Val, data: &Data) -> Option<BasicValueEnum<'cxt>> {
        let val = data.slots.unredirect(val);

        if let Some(&v) = self.upvalues.borrow().get(&val) {
            return Some(v);
        }
        Some(match data.slots.node(val).unwrap() {
            Node::Fun(_) => {
                // Create a closure
                let functions = self.functions.borrow();
                let LFunction { unknown, env, .. } = functions
                    .get(&val)
                    .unwrap_or_else(|| panic!("Couldn't find fun {}", val.id()));

                // Store the function pointer + environment in a heap-allocated struct
                let env_ty = Type::PtrStruct(
                    std::iter::once((None, Type::Pointer))
                        .chain(env.iter().map(|(_, _, ty)| {
                            let ty = if ty.has_unknown() {
                                Type::Pointer
                            } else {
                                ty.clone()
                            };
                            (None, ty)
                        }))
                        .collect(),
                );
                let size = env_ty.heap_size(self, data);

                // We use the unknown version of the function, which takes one environment parameter and all of type i8* (any)
                let fun_ptr_val = data.entities.create();
                self.push_val(
                    fun_ptr_val,
                    unknown
                        .as_global_value()
                        .as_pointer_value()
                        .as_basic_value_enum(),
                );
                let values: Vec<_> = std::iter::once(fun_ptr_val)
                    .chain(env.iter().map(|&(x, _, _)| x))
                    .collect();

                let alloc = self.alloc(size, env_ty.as_rtti(self, data), "env_slot");
                let slot = unsafe {
                    self.builder.build_in_bounds_gep(
                        alloc,
                        &[self.size_ty().const_int(8, false)],
                        "store_slot",
                    )
                };
                self.gen_struct(&values, &env_ty, slot, data);
                self.pop_val(fun_ptr_val);

                self.builder
                    .build_bitcast(alloc, self.any_ty().into_pointer_type(), "closure")
            }
            Node::ExternFun(name, params, ret) => {
                let fun = match self.module.get_function(name) {
                    Some(fun) => fun,
                    None => {
                        let rty = self.as_type(*ret, data).llvm_ty(self);
                        let ptys: Vec<_> = params
                            .iter()
                            .map(|t| self.as_type(*t, data).llvm_ty(self))
                            .collect();
                        let fty = rty.fn_type(&ptys, false);
                        self.module.add_function(name, fty, None)
                    }
                };
                fun.as_global_value()
                    .as_pointer_value()
                    .as_basic_value_enum()
            }
            Node::Proj(ty, x, idx) => {
                let ty = self.as_type(*ty, data);
                match &ty {
                    Type::StackStruct(_) => {
                        let x = self.try_gen_value(*x, data)?.into_struct_value();
                        self.builder
                            .build_extract_value(x, *idx as u32, "project")
                            .unwrap()
                    }
                    Type::PtrStruct(v) => {
                        // TODO only compute the size once, and use bitwise and instead of alloca
                        let val = self.try_gen_value(*x, data)?;
                        let size = ty.heap_size(self, data);
                        let fits = self.builder.build_int_compare(
                            IntPredicate::ULT,
                            size,
                            self.size_ty().const_int(8, false),
                            "fits_in_word",
                        );
                        let mut ptr = self
                            .if_expr(
                                fits,
                                || {
                                    // If it fits in a word, put it in an alloca so we can still work with a pointer
                                    let ptr =
                                        self.builder.build_alloca(self.size_ty(), "proj_slot");
                                    let val = self.ptrtoint(ptr);
                                    let val = self.builder.build_right_shift(
                                        val,
                                        self.size_ty().const_int(1, false),
                                        false,
                                        "proj_val_unmarked",
                                    );
                                    self.builder.build_store(ptr, val);
                                    self.builder
                                        .build_pointer_cast(
                                            ptr,
                                            self.any_ty().into_pointer_type(),
                                            "proj_slot_casted",
                                        )
                                        .as_basic_value_enum()
                                },
                                || unsafe {
                                    self.builder
                                        .build_in_bounds_gep(
                                            val.into_pointer_value(),
                                            &[self.size_ty().const_int(8, false)],
                                            "store_slot",
                                        )
                                        .as_basic_value_enum()
                                },
                            )
                            .into_pointer_value();

                        let mut size = self.size_ty().const_zero();
                        for (i, (param, ty)) in v.iter().enumerate() {
                            let x = ty.heap_size(self, data);
                            let align = ty.alignment();
                            if align > 0 {
                                let padding = self.padding_llvm(size, align);
                                ptr = unsafe {
                                    self.builder.build_in_bounds_gep(
                                        ptr,
                                        &[padding],
                                        "member_slot_padded",
                                    )
                                };
                                size = self.builder.build_int_add(size, padding, "aligned_size");
                            }
                            if i == *idx {
                                return Some(self.load(ty, ptr, data));
                            } else {
                                if let Some(param) = param {
                                    self.push_val(*param, self.load(ty, ptr, data));
                                }
                                ptr = unsafe {
                                    self.builder
                                        .build_in_bounds_gep(ptr, &[x], "next_member_slot")
                                };
                            }
                            size = self.builder.build_int_add(size, x, "struct_size");
                        }
                        unreachable!("index out of bounds")
                    }
                    _ => unreachable!(),
                }
            }
            Node::Inj(ty, i, payload) => {
                if matches!(data.slots.node(*ty), Some(Node::SumType(v)) if v.len() == 1) {
                    // No tag or casting needed
                    return self.try_gen_value(*payload, data);
                }

                let ty = self.as_type(*ty, data);
                match &ty {
                    Type::StackEnum(_, v) | Type::PtrEnum(v) => {
                        let mut payload_size = self.size_ty().const_zero();
                        let mut align = 0;
                        for i in v {
                            let size = i.heap_size(self, data);
                            let gt = self.builder.build_int_compare(
                                IntPredicate::UGT,
                                size,
                                payload_size,
                                "gt",
                            );
                            payload_size = self
                                .builder
                                .build_select(gt, size, payload_size, "payload_size")
                                .into_int_value();

                            let ialign = i.alignment();
                            if ialign > align {
                                align = ialign;
                            }
                        }
                        let mut tag = tag_bytes(v.len());
                        if tag != 0 {
                            tag = tag.max(align);
                        }

                        let size = self.builder.build_int_add(
                            payload_size,
                            self.size_ty().const_int(tag.into(), false),
                            "sum_type_size",
                        );
                        let fits = self.builder.build_int_compare(
                            IntPredicate::ULT,
                            size,
                            self.size_ty().const_int(8, false),
                            "fits_in_word",
                        );
                        let alloc = match &ty {
                            Type::StackEnum(_, _) => {
                                let alloca = self.builder.build_array_alloca(
                                    self.cxt.i8_type(),
                                    size,
                                    "sum_type_alloca",
                                );
                                alloca
                                    .as_instruction_value()
                                    .unwrap()
                                    .set_alignment(ty.alignment())
                                    .unwrap();
                                alloca
                            }
                            Type::PtrEnum(_) => self
                                .if_expr(
                                    fits,
                                    || {
                                        let alloca = self
                                            .builder
                                            .build_alloca(self.any_ty(), "sum_type_bitcast_slot");
                                        self.builder
                                            .build_pointer_cast(
                                                alloca,
                                                self.any_ty().into_pointer_type(),
                                                "sum_type_slot",
                                            )
                                            .as_basic_value_enum()
                                    },
                                    || {
                                        let alloc = self.alloc(
                                            size,
                                            ty.as_rtti(self, data),
                                            "sum_type_alloc",
                                        );
                                        let alloc = unsafe {
                                            self.builder.build_in_bounds_gep(
                                                alloc,
                                                &[self.size_ty().const_int(8, false)],
                                                "store_slot",
                                            )
                                        };
                                        alloc.as_basic_value_enum()
                                    },
                                )
                                .into_pointer_value(),
                            _ => unreachable!(),
                        };

                        if tag != 0 {
                            let tag = tag * 8;
                            let tag = self.cxt.custom_width_int_type(tag);
                            let tag_slot =
                                self.builder
                                    .build_pointer_cast(alloc, tag.gc_ptr(), "tag_slot");
                            let tag = tag.const_int(*i as u64, false).as_basic_value_enum();
                            self.builder.build_store(tag_slot, tag);
                        }

                        let payload_slot = unsafe {
                            self.builder.build_in_bounds_gep(
                                alloc,
                                &[self.size_ty().const_int(tag.into(), false)],
                                "payload_slot",
                            )
                        };
                        self.gen_at(*payload, &v[*i], payload_slot, data);

                        match &ty {
                            Type::StackEnum(_, _) => {
                                // Copy the enum out of the alloca
                                let llvm_ty = ty.llvm_ty(self);
                                let alloc = self.builder.build_pointer_cast(
                                    alloc,
                                    llvm_ty.gc_ptr(),
                                    "sum_type_casted",
                                );
                                self.builder.build_load(alloc, "sum_type")
                            }
                            // Just return the pointer
                            Type::PtrEnum(_) => self.if_expr(
                                fits,
                                || {
                                    let ptr = self
                                        .builder
                                        .build_bitcast(
                                            alloc,
                                            self.any_ty().gc_ptr(),
                                            "sum_type_bitcast_slot_again",
                                        )
                                        .into_pointer_value();
                                    let val = self
                                        .builder
                                        .build_load(ptr, "sum_type_as_word")
                                        .into_pointer_value();
                                    let val = self.ptrtoint(val);
                                    let val = self.builder.build_right_shift(
                                        val,
                                        self.size_ty().const_int(1, false),
                                        false,
                                        "sum_type_shl",
                                    );
                                    let val = self.builder.build_or(
                                        val,
                                        self.size_ty().const_int(1, false),
                                        "sum_type_marked",
                                    );
                                    self.inttoptr(val).as_basic_value_enum()
                                },
                                || {
                                    let alloc = unsafe {
                                        self.builder.build_in_bounds_gep(
                                            alloc,
                                            &[self.size_ty().const_int(-8i64 as u64, true)],
                                            "store_slot",
                                        )
                                    };
                                    alloc.as_basic_value_enum()
                                },
                            ),
                            _ => unreachable!(),
                        }
                    }
                    _ => unreachable!(),
                }
            }
            Node::Product(ty, values) => {
                let ty = self.as_type(*ty, data);
                match &ty {
                    Type::StackStruct(v) => {
                        let ty = ty.llvm_ty(self).into_struct_type();
                        let mut agg = ty.get_undef().as_aggregate_value_enum();
                        for (i, (x, (param, _))) in values.into_iter().zip(v).enumerate() {
                            let x = self.try_gen_value(*x, data)?;
                            if let Some(param) = param {
                                self.push_val(*param, x);
                            }
                            agg = self
                                .builder
                                .build_insert_value(agg, x, i as u32, "product")
                                .unwrap();
                        }
                        for (param, _) in v {
                            if let Some(param) = param {
                                self.pop_val(*param);
                            }
                        }
                        agg.as_basic_value_enum()
                    }
                    Type::PtrStruct(_) => {
                        let size = ty.heap_size(self, data);

                        let fits = self.builder.build_int_compare(
                            IntPredicate::ULT,
                            size,
                            self.size_ty().const_int(8, false),
                            "fits_in_word",
                        );
                        let alloc = self
                            .if_expr(
                                fits,
                                || {
                                    let alloca = self
                                        .builder
                                        .build_alloca(self.any_ty(), "struct_bitcast_slot");
                                    self.builder
                                        .build_pointer_cast(
                                            alloca,
                                            self.any_ty().into_pointer_type(),
                                            "struct_slot",
                                        )
                                        .as_basic_value_enum()
                                },
                                || {
                                    let alloc =
                                        self.alloc(size, ty.as_rtti(self, data), "struct_alloc");
                                    let alloc = unsafe {
                                        self.builder.build_in_bounds_gep(
                                            alloc,
                                            &[self.size_ty().const_int(8, false)],
                                            "store_slot",
                                        )
                                    };
                                    alloc.as_basic_value_enum()
                                },
                            )
                            .into_pointer_value();

                        self.gen_struct(values, &ty, alloc, data);

                        self.if_expr(
                            fits,
                            || {
                                let ptr = self
                                    .builder
                                    .build_bitcast(
                                        alloc,
                                        self.any_ty().gc_ptr(),
                                        "struct_bitcast_slot_again",
                                    )
                                    .into_pointer_value();
                                let val = self
                                    .builder
                                    .build_load(ptr, "struct_as_word")
                                    .into_pointer_value();
                                let val = self.ptrtoint(val);
                                let val = self.builder.build_right_shift(
                                    val,
                                    self.size_ty().const_int(1, false),
                                    false,
                                    "struct_shl",
                                );
                                let val = self.builder.build_or(
                                    val,
                                    self.size_ty().const_int(1, false),
                                    "struct_marked",
                                );
                                self.inttoptr(val).as_basic_value_enum()
                            },
                            || {
                                let alloc = unsafe {
                                    self.builder.build_in_bounds_gep(
                                        alloc,
                                        &[self.size_ty().const_int(-8i64 as u64, true)],
                                        "store_slot",
                                    )
                                };
                                alloc.as_basic_value_enum()
                            },
                        )
                    }
                    _ => unreachable!(),
                }
            }
            Node::IfCase(_, _) => panic!("`ifcase _ _` isn't a first-class function!"),
            Node::If(_) => panic!("`if _` isn't a first-class function!"),
            Node::Ref(_, _) => {
                panic!("`refset`, `refget`, and `refnew` aren't first-class functions!")
            }
            Node::Param(f, i) => {
                // let name = self.name(val).unwrap_or_else(|| "param".to_string());
                let ptr = self.blocks.borrow().get(f)?.1[*i as usize];
                self.builder.build_load(ptr, "param")
            }
            Node::Const(Constant::Int(w, val)) => self
                .cxt
                .custom_width_int_type(w.bits())
                .const_int(*val as u64, false)
                .as_basic_value_enum(),
            Node::Const(Constant::Float(x)) => match x {
                crate::ir::Float::F32(x) => self
                    .cxt
                    .f32_type()
                    .const_float(f32::from_bits(*x) as f64)
                    .as_basic_value_enum(),
                crate::ir::Float::F64(x) => self
                    .cxt
                    .f64_type()
                    .const_float(f64::from_bits(*x))
                    .as_basic_value_enum(),
            },
            Node::Const(Constant::String(s)) => {
                let size = s.len() as u32;
                // We need a fake 8-byte header to be ABI-compatible with heap-allocated strings
                let bytes: Vec<_> = [0; 8]
                    .iter()
                    .chain(size.to_le_bytes().iter())
                    .cloned()
                    .chain(s.bytes())
                    .map(|x| self.cxt.i8_type().const_int(x as u64, false))
                    .collect();
                let arr = self.cxt.i8_type().const_array(&bytes);
                let g = self.module.add_global(arr.get_type(), None, "const_str");
                g.set_initializer(&arr);
                g.set_constant(true);
                let ptr = g.as_pointer_value();
                let ptr = self.builder.build_address_space_cast(
                    ptr,
                    self.any_ty().into_pointer_type(),
                    "str_ptr",
                );
                ptr.as_basic_value_enum()
            }
            Node::Const(Constant::Stop) | Node::Const(Constant::Unreachable) => {
                panic!("stop or unreachable isn't a first-class function!")
            }
            Node::FunType(_)
            | Node::ExternFunType(_, _)
            | Node::RefTy(_)
            | Node::ProdType(_)
            | Node::SumType(_)
            | Node::Const(Constant::StringTy)
            | Node::Const(Constant::TypeType)
            | Node::Const(Constant::FloatType(_))
            | Node::Const(Constant::IntType(_)) => self
                .as_type(val, data)
                .as_rtti(self, data)
                .as_basic_value_enum(),
            Node::ExternCall(_, _) => panic!("externcall isn't a first-class function!"),
            Node::BinOp(op, signed, a, b) => {
                let a = self.try_gen_value(*a, data)?;
                let b = self.try_gen_value(*b, data)?;
                match a {
                    BasicValueEnum::IntValue(a) => {
                        let b = b.into_int_value();
                        // let name = self.name(val).unwrap_or_else(|| "binop".to_string());
                        // let name = &name;
                        let name = "binop";
                        use crate::ir::BinOp::*;
                        macro_rules! lop {
                            (? $met1:ident : $met2:ident) => {
                                if *signed {
                                    lop!($met1)
                                } else {
                                    lop!($met2)
                                }
                            };
                            ($met:ident ? $($a:expr)* ; $($b:expr)*) => {
                                if *signed {
                                    lop!($met $($a),*)
                                } else {
                                    lop!($met $($b),*)
                                }
                            };
                            ($met:ident $($p:expr),* $(;$q:expr)*) => {
                                self
                                    .builder
                                    .$met($($p,)* a, b, $($q,)* name)
                                    .as_basic_value_enum()
                            };
                        }
                        match op {
                            Add => lop!(build_int_add),
                            Sub => lop!(build_int_sub),
                            Mul => lop!(build_int_mul),
                            Div => lop!(? build_int_signed_div : build_int_unsigned_div),
                            Mod => lop!(? build_int_signed_rem : build_int_unsigned_rem),
                            And => lop!(build_and),
                            Or => lop!(build_or),
                            Xor => lop!(build_xor),
                            Shl => lop!(build_left_shift),
                            Shr => lop!(build_right_shift; *signed),
                            Pow => todo!("int power"),

                            Eq => lop!(build_int_compare IntPredicate::EQ),
                            NEq => lop!(build_int_compare IntPredicate::NE),
                            // TODO unsigned vs signed
                            Lt => lop!(build_int_compare ? IntPredicate::SLT ; IntPredicate::ULT),
                            Gt => lop!(build_int_compare ? IntPredicate::SGT ; IntPredicate::UGT),
                            Leq => lop!(build_int_compare ? IntPredicate::SLE ; IntPredicate::ULE),
                            Geq => lop!(build_int_compare ? IntPredicate::SGE ; IntPredicate::UGE),
                        }
                    }
                    BasicValueEnum::FloatValue(a) => {
                        let b = b.into_float_value();
                        // let name = self.name(val).unwrap_or_else(|| "binop".to_string());
                        // let name = &name;
                        let name = "binop";
                        use crate::ir::BinOp::*;
                        macro_rules! lop {
                            (? $met1:ident : $met2:ident) => {
                                if *signed {
                                    lop!($met1)
                                } else {
                                    lop!($met2)
                                }
                            };
                            ($met:ident ? $($a:expr)* ; $($b:expr)*) => {
                                if *signed {
                                    lop!($met $($a),*)
                                } else {
                                    lop!($met $($b),*)
                                }
                            };
                            ($met:ident $($p:expr),* $(;$q:expr)*) => {
                                self
                                    .builder
                                    .$met($($p,)* a, b, $($q,)* name)
                                    .as_basic_value_enum()
                            };
                        }
                        match op {
                            Add => lop!(build_float_add),
                            Sub => lop!(build_float_sub),
                            Mul => lop!(build_float_mul),
                            Div => lop!(build_float_div),
                            Mod => lop!(build_float_rem),
                            And | Or | Xor | Shl | Shr => panic!("No bitwise operations on floats"),
                            Pow => todo!("float power"),

                            Eq => lop!(build_float_compare FloatPredicate::OEQ),
                            NEq => lop!(build_float_compare FloatPredicate::ONE),
                            // TODO unsigned vs signed
                            Lt => lop!(build_float_compare FloatPredicate::OLT),
                            Gt => lop!(build_float_compare FloatPredicate::OGT),
                            Leq => lop!(build_float_compare FloatPredicate::OLE),
                            Geq => lop!(build_float_compare FloatPredicate::OGE),
                        }
                    }
                    _ => unreachable!(),
                }
            }
        })
    }

    fn cast(
        &self,
        x: BasicValueEnum<'cxt>,
        from: &Type<'cxt>,
        to: &Type<'cxt>,
        data: &Data,
    ) -> BasicValueEnum<'cxt> {
        if from == to {
            x
        } else {
            eprintln!("durin/info: Casting from {:?} to {:?}", from, to);
            let x = self.to_any(from, x, data);
            self.from_any(to, x, data)
        }
    }

    fn gen_call(
        &self,
        callee: Val,
        mut args: Vec<(BasicValueEnum<'cxt>, Type<'cxt>)>,
        cont: Option<(Val, Type<'cxt>)>,
        data: &Data,
    ) {
        match data.slots.node(callee) {
            // If we're calling the return continuation, emit a return instruction
            _ if self
                .cont
                .borrow()
                .as_ref()
                .map_or(false, |(x, _)| *x == callee) =>
            {
                if let Some((k, ty)) = cont {
                    args.push((self.gen_value(k, data), ty));
                }
                let args = args
                    .into_iter()
                    .zip(&self.cont.borrow().as_ref().unwrap().1)
                    .map(|((x, from), to)| self.cast(x, &from, to, data))
                    .collect::<Vec<_>>();
                let ret = if args.len() == 1 {
                    args[0]
                } else {
                    let tys: Vec<_> = self
                        .cont
                        .borrow()
                        .as_ref()
                        .unwrap()
                        .1
                        .iter()
                        .map(|x| x.llvm_ty(self))
                        .collect();
                    let ty = self.cxt.struct_type(&tys, false);
                    let mut agg = ty.get_undef().as_aggregate_value_enum();
                    for (i, x) in args.into_iter().enumerate() {
                        agg = self
                            .builder
                            .build_insert_value(agg, x, i as u32, "ret_product")
                            .unwrap();
                    }
                    agg.as_basic_value_enum()
                };
                self.builder.build_return(Some(&ret));
            }

            // If we're calling a basic block, jump there
            _ if self.blocks.borrow().get(&callee).is_some() => {
                let blocks = self.blocks.borrow();
                let (target, params, tys) = blocks.get(&callee).unwrap();
                if let Some((k, ty)) = cont {
                    args.push((self.gen_value(k, data), ty));
                }
                let args = args
                    .into_iter()
                    .zip(tys)
                    .map(|((x, from), to)| self.cast(x, &from, to, data))
                    .collect::<Vec<_>>();
                // Set the parameters and jump to the target block
                for (&ptr, value) in params.iter().zip(args) {
                    self.builder.build_store(ptr, value);
                }
                self.builder.build_unconditional_branch(*target);
            }

            // Execute a ref op if we're doing one
            Some(Node::Ref(ty, op)) => {
                let ty = self.as_type(*ty, data);

                // Execute the operation
                let arg = match op {
                    crate::ir::RefOp::RefNew => {
                        let size = ty.heap_size(self, data);
                        let ptr = self.alloc(size, ty.as_rtti(self, data), "ref_ptr");
                        Some((ptr.as_basic_value_enum(), Type::Pointer))
                    }
                    crate::ir::RefOp::RefGet(r) => {
                        let ptr = self.gen_value(*r, data).into_pointer_value();
                        let ptr = unsafe {
                            self.builder.build_in_bounds_gep(
                                ptr,
                                &[self.size_ty().const_int(8, false)],
                                "ref_slot",
                            )
                        };
                        let val = self.load(&ty, ptr, data);
                        Some((val, ty))
                    }
                    crate::ir::RefOp::RefSet(r, v) => {
                        let ptr = self.gen_value(*r, data).into_pointer_value();
                        let ptr = unsafe {
                            self.builder.build_in_bounds_gep(
                                ptr,
                                &[self.size_ty().const_int(8, false)],
                                "ref_slot",
                            )
                        };
                        // TODO are there circumstances when we can use `gen_at`?
                        let val = self.gen_value(*v, data);
                        self.store(&ty, val, ptr, data);
                        None
                    }
                };

                // Call the continuation
                let (cont, _) = cont.unwrap();
                let cont2 = arg.map(|(v, ty)| {
                    let n = data.entities.create();
                    self.upvalues.borrow_mut().insert(n, v);
                    (n, ty)
                });
                self.gen_call(cont, Vec::new(), cont2, data)
            }

            // If we're stopping, return void
            Some(Node::Const(crate::ir::Constant::Stop)) => {
                self.builder.build_return(None);
            }

            // If we're calling unreachable, emit a LLVM unreachable instruction
            Some(Node::Const(crate::ir::Constant::Unreachable)) => {
                self.builder.build_unreachable();
            }
            // Even if it goes through a function
            Some(Node::Fun(Function { callee, .. }))
                if matches!(
                    data.slots.node(*callee),
                    Some(Node::Const(crate::ir::Constant::Unreachable))
                ) =>
            {
                self.builder.build_unreachable();
            }

            // If we're calling an extern function, do that
            Some(Node::ExternCall(f, ret_ty)) => {
                let args: Vec<_> = args.into_iter().map(|(v, _)| v).collect();
                let f = self.gen_value(*f, data);
                let call = self
                    .builder
                    .build_call(f.into_pointer_value(), &args, "extern_call");
                call.set_tail_call(DO_TAIL_CALL);

                let ret_ty = self.as_type(*ret_ty, data);

                let (cont, _) = cont.unwrap();
                self.gen_call(
                    cont,
                    vec![(call.try_as_basic_value().left().unwrap(), ret_ty)],
                    None,
                    data,
                )
            }

            // Otherwise, we're actually calling a function
            _ => {
                // The mechanism depends on whether it's a known or unknown call
                match self.functions.borrow().get(&data.slots.unredirect(callee)) {
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
                            .map(|((x, from), to)| self.cast(x, &from, to, data))
                            .collect::<Vec<_>>();
                        let mut args: Vec<_> = env
                            .iter()
                            .map(|&(val, _, _)| self.gen_value(val, data))
                            .chain(args)
                            .collect();

                        // The actual call depends on whether we're using the LLVM stack or not
                        if fcont.is_some() {
                            let (cont, _) = cont.unwrap_or_else(|| {
                                panic!("No continuation given for {}", callee.id())
                                //.pretty(self))
                            });
                            let call = self.builder.build_call(*known, &args, "stack_call");
                            call.set_tail_call(DO_TAIL_CALL);
                            call.set_call_convention(TAILCC);

                            let call = call.try_as_basic_value().left().unwrap();
                            let atys = &fcont.as_ref().unwrap().1;
                            let mut args = if atys.len() == 1 {
                                vec![(call, atys[0].clone())]
                            } else {
                                let call = call.into_struct_value();
                                atys.iter()
                                    .cloned()
                                    .enumerate()
                                    .map(|(i, ty)| {
                                        (
                                            self.builder
                                                .build_extract_value(
                                                    call,
                                                    i as u32,
                                                    "extract_return",
                                                )
                                                .unwrap(),
                                            ty,
                                        )
                                    })
                                    .collect()
                            };
                            let acont = args.pop().map(|(x, ty)| {
                                let v = data.entities.create();
                                self.upvalues.borrow_mut().insert(v, x);
                                (v, ty)
                            });

                            self.gen_call(cont, args, acont, data)
                        } else {
                            if let Some((k, ty)) = cont {
                                let v = self.gen_value(k, data);
                                let v = self.cast(v, &ty, param_tys.last().unwrap(), data);
                                args.push(v);
                            }
                            let call = self.builder.build_call(*known, &args, "call");

                            call.set_tail_call(DO_TAIL_CALL);
                            call.set_call_convention(TAILCC);
                            self.builder.build_return(None);
                        }
                    }
                    None => {
                        // Unknown call
                        if let Some((k, ty)) = cont {
                            args.push((self.gen_value(k, data), ty));
                        }

                        let callee = self.gen_value(callee, data).into_pointer_value();
                        let fun_ptr_slot = unsafe {
                            self.builder.build_in_bounds_gep(
                                callee,
                                &[self.size_ty().const_int(8, false)],
                                "store_slot",
                            )
                        };
                        let fun_ty = vec![self.any_ty(); args.len() + 1];
                        let fun_ty = self
                            .cxt
                            .void_type()
                            .fn_type(&fun_ty, false)
                            .ptr_type(AddressSpace::Generic);
                        let fun_ptr_ptr = self
                            .builder
                            .build_bitcast(fun_ptr_slot, fun_ty.gc_ptr(), "fun_ptr_ptr")
                            .into_pointer_value();
                        let fun_ptr = self
                            .builder
                            .build_load(fun_ptr_ptr, "fun_ptr")
                            .into_pointer_value();

                        // It could be polymorphic, so we pass all arguments as word-size "any"
                        let mut args: Vec<_> = args
                            .into_iter()
                            .map(|(val, ty)| self.to_any(&ty, val, data).as_basic_value_enum())
                            .collect();
                        // The closure environment (which is just the pointer to the closure) is the last argument
                        args.push(callee.as_basic_value_enum());

                        let call = self.builder.build_call(fun_ptr, &args, "closure_call");

                        call.set_tail_call(DO_TAIL_CALL);
                        call.set_call_convention(TAILCC);
                        self.builder.build_return(None);
                    }
                }
            }
        }
    }

    fn codegen(
        &self,
        data: &Data,
        modes: &ReadStorage<FunMode>,
        tys: &ReadStorage<ValType>,
        names: &ReadStorage<Name>,
    ) {
        // Collect all functions and their blocks
        let mut to_gen: HashMap<Val, VecDeque<(Val, crate::ir::Function)>> = HashMap::new();
        let mut stack_enabled = HashMap::new();
        for (v, mode) in (&data.entities, modes).join() {
            match mode {
                FunMode::SSA(cont) => {
                    to_gen
                        .entry(v)
                        .or_default()
                        .push_front((v, data.slots.fun(v).unwrap().clone()));
                    stack_enabled.insert(v, *cont);
                }
                FunMode::CPS => {
                    to_gen
                        .entry(v)
                        .or_default()
                        .push_front((v, data.slots.fun(v).unwrap().clone()));
                }
                FunMode::Block(parent) => {
                    to_gen
                        .entry(*parent)
                        .or_default()
                        .push_back((v, data.slots.fun(v).unwrap().clone()));
                }
            }
        }

        // Declare all the functions before generating their bodies
        for (val, blocks) in to_gen {
            let env = data.slots.env(val);

            if let Some(fun) = data.slots.fun(val).cloned() {
                // Get the continuation type by whatever is passed to the continuation
                let cont = stack_enabled.get(&val);
                let cont = cont.and_then(|&cont| {
                    let u = data.uses.get(cont).unwrap();
                    if u.is_empty() {
                        eprintln!("durin/warning: could not deduce continuation type (no uses)");
                        None
                    } else {
                        let u = u.clone();
                        for &i in &**u {
                            let ty = match data.slots.node(i).cloned() {
                                Some(Node::Fun(Function {
                                    callee, call_args, ..
                                })) if callee == cont => call_args
                                    .clone()
                                    .into_iter()
                                    .map(|x| data.slots.unredirect(x))
                                    .map(|x| **tys.get(x).unwrap())
                                    .map(|x| self.as_type(x, data))
                                    .collect::<Vec<_>>(),
                                _ => continue,
                            };
                            return Some((cont, ty));
                        }
                        eprintln!("durin/warning: could not deduce continuation type (no calls)");
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
                    .map(|&x| self.as_type(x, data).llvm_ty(self))
                    .collect();
                let known_ty = if let Some((_, ret_tys)) = &cont {
                    let ret_ty = if ret_tys.len() == 1 {
                        ret_tys[0].llvm_ty(self)
                    } else {
                        let v: Vec<_> = ret_tys.iter().map(|x| x.llvm_ty(self)).collect();
                        self.cxt.struct_type(&v, false).as_basic_type_enum()
                    };
                    ret_ty.fn_type(&args, false)
                } else {
                    self.cxt.void_type().fn_type(&args, false)
                };

                // Declare the known and unknown versions of the function
                let name = names
                    .get(val)
                    .map(|n| n.0.clone())
                    .unwrap_or_else(|| format!("fun${}", val.id()));
                let known = self.module.add_function(&name, known_ty, None);
                known.set_call_conventions(TAILCC);
                known.set_gc("statepoint-example");

                let uargs: Vec<_> = fun
                    .params
                    .iter()
                    .map(|_| self.any_ty())
                    .chain(std::iter::once(self.any_ty()))
                    .collect();
                let unknown_ty = self.cxt.void_type().fn_type(&uargs, false);
                let uname = format!("u${}", &name);
                let unknown = self.module.add_function(&uname, unknown_ty, None);
                unknown.set_call_conventions(TAILCC);
                unknown.set_gc("statepoint-example");

                let env = args[0..env.len()]
                    .iter()
                    .zip(env)
                    .map(|(&ty, (val, ty2))| (val, ty, self.as_type(ty2, data)))
                    .collect();

                let param_tys = fun.params.iter().map(|&x| self.as_type(x, data)).collect();

                self.functions.borrow_mut().insert(
                    val,
                    LFunction {
                        arity: fun.params.len() as u32,
                        known,
                        unknown,
                        env,
                        blocks,
                        cont,
                        param_tys,
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
        ) in &*self.functions.borrow()
        {
            // First generate the unknown version, which just delegates to the known version
            {
                // Remove any basic blocks and upvalues we generated last time, they're no longer accessible
                self.blocks.replace(HashMap::new());
                self.upvalues.replace(HashMap::new());

                let uentry = self.cxt.append_basic_block(*unknown, "entry");
                self.builder.position_at_end(uentry);

                // Unpack environment
                let &env_ptr = unknown.get_params().last().unwrap();
                env_ptr.set_name("env");
                // TODO what about dependently sized types?

                // Skip the header and the function pointer
                let mut ptr = unsafe {
                    self.builder.build_in_bounds_gep(
                        env_ptr.into_pointer_value(),
                        &[self.cxt.i32_type().const_int(16, false)],
                        "env_slots",
                    )
                };
                let mut size = self.size_ty().const_zero();
                for (val, _, ty) in env.iter() {
                    // If its size might depend on other upvalues, always box it since we don't know the order of upvalues
                    // and even if we did, we could have e.g. `x : { Type, y.0 }; y : { Type, x.0 }`
                    // so we just need to box those all the time
                    let ty = if ty.has_unknown() { &Type::Pointer } else { ty };
                    let x = ty.heap_size(self, data);
                    let align = ty.alignment();
                    if align > 0 {
                        let padding = self.padding_llvm(size, align);
                        ptr = unsafe {
                            self.builder
                                .build_in_bounds_gep(ptr, &[padding], "member_slot_padded")
                        };
                        size = self.builder.build_int_add(size, padding, "aligned_size");
                    }
                    let value = self.load(ty, ptr, data);
                    self.upvalues.borrow_mut().insert(*val, value);
                    ptr = unsafe {
                        self.builder
                            .build_in_bounds_gep(ptr, &[x], "next_member_slot")
                    };
                    size = self.builder.build_int_add(size, x, "struct_size");
                }

                // Call function
                let mut args: Vec<_> = blocks[0]
                    .1
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, &ty)| {
                        let ty = self.as_type(ty, data);
                        (
                            self.from_any(&ty, unknown.get_params()[i].into_pointer_value(), data),
                            ty,
                        )
                    })
                    .collect();
                if let Some((vcont, cty)) = args.pop() {
                    // `gen_call` takes the continuation as a Val, not a BasicValueEnum; so, we use an unused Val slot and stick the BasicValueEnum in the upvalues map
                    let cont = data.entities.create();
                    {
                        self.upvalues.borrow_mut().insert(cont, vcont);
                    }
                    self.gen_call(*val, args, Some((cont, cty)), data);
                } else {
                    self.gen_call(*val, args, None, data);
                }
            }

            let fun = known;
            self.cont.replace(cont.clone());

            let entry = self.cxt.append_basic_block(*fun, "entry");
            self.builder.position_at_end(entry);

            // Remove any basic blocks and upvalues we generated last time, they're no longer accessible
            self.blocks.replace(HashMap::new());
            self.upvalues.replace(HashMap::new());

            // Add closed-over upvalues to the context
            {
                let mut upvalues = self.upvalues.borrow_mut();
                for ((val, _ty, _ty2), param) in env.iter().zip(fun.get_params()) {
                    upvalues.insert(*val, param);
                }
            }

            // Declare all blocks and their parameters first
            // Block parameters are stored in allocas, which will be removed with mem2reg
            for (bval, bfun) in blocks {
                let name = format!("{}${}", val.name_or_num(names), bval.name_or_num(names));
                let block = self.cxt.append_basic_block(*fun, &name);
                let cont_num = modes
                    .get(*bval)
                    .filter(|m| matches!(m, FunMode::SSA(_)))
                    .map(|_| bfun.params.len() - 1);

                let mut params = Vec::new();
                let mut param_tys = Vec::new();
                for (i, &ty) in bfun.params.iter().enumerate() {
                    if Some(i) == cont_num {
                        // Don't allocate the continuation parameter
                        break;
                    } else {
                        let ty = self.as_type(ty, data);
                        let lty = ty.llvm_ty(self);
                        let name = bval.param_name(i as u8, &data.uses, &data.slots, names);
                        let param = self.builder.build_alloca(lty, &name);
                        params.push(param);
                        param_tys.push(ty);
                    }
                }
                self.blocks
                    .borrow_mut()
                    .insert(*bval, (block, params, param_tys));
            }

            // We store the function parameters in the parameter slots of the entry block
            let cblocks = self.blocks.borrow();
            let (first_block, _) = &blocks[0];
            for (&ptr, value) in cblocks
                .get(first_block)
                .unwrap()
                .1
                .iter()
                .zip(fun.get_params().into_iter().skip(env.len()))
            {
                self.builder.build_store(ptr, value);
            }
            self.builder
                .build_unconditional_branch(cblocks.get(first_block).unwrap().0);

            // Now actually generate the blocks' code
            for (bval, bfun) in blocks {
                let (block, _, _) = cblocks.get(&bval).unwrap();
                self.builder.position_at_end(*block);

                // If we're calling if x, do that
                if let Some(Node::If(x)) = data.slots.node(bfun.callee).cloned() {
                    assert_eq!(bfun.call_args.len(), 2);
                    let fthen = bfun.call_args[0];
                    let felse = bfun.call_args[1];

                    let cond = self.gen_value(x, data).into_int_value();

                    let bstart = self.builder.get_insert_block().unwrap();
                    let bthen = self.cxt.insert_basic_block_after(bstart, "if.then");
                    let belse = self.cxt.insert_basic_block_after(bthen, "if.else");

                    self.builder.build_conditional_branch(cond, bthen, belse);

                    self.builder.position_at_end(bthen);
                    self.gen_call(fthen, vec![], None, data);

                    self.builder.position_at_end(belse);
                    self.gen_call(felse, vec![], None, data);
                // If we're calling ifcase i x, do that instead
                } else if let Some(Node::IfCase(i, x)) = data.slots.node(bfun.callee).cloned() {
                    let vty = tys.get(x).unwrap().0;
                    let ty = self.as_type(vty, data);
                    let payload_ty = match vty.get(&data.slots) {
                        Node::SumType(v) if v.len() == 1 => {
                            // There's no tag, and no casting needed
                            assert_eq!(i, 0);
                            let x = self.gen_value(x, data);
                            assert_eq!(bfun.call_args.len(), 2);
                            let fthen = bfun.call_args[0];

                            self.gen_call(fthen, vec![(x, ty)], None, data);

                            // Skip to the next basic block
                            continue;
                        }
                        Node::SumType(v) => v[i],
                        x => unreachable!("{:?}", x),
                    };
                    let payload_ty = self.as_type(payload_ty, data);

                    assert_eq!(bfun.call_args.len(), 2);
                    let fthen = bfun.call_args[0];
                    let felse = bfun.call_args[1];

                    let x = self.gen_value(x, data);

                    let bstart = self.builder.get_insert_block().unwrap();
                    let bthen = self.cxt.insert_basic_block_after(bstart, "ifcase.then");
                    let belse = self.cxt.insert_basic_block_after(bthen, "ifcase.else");

                    let align = ty.alignment();
                    let (ptr, v) = match ty {
                        Type::StackEnum(_, v) => {
                            let alloca = self.builder.build_alloca(x.get_type(), "union_ptr");
                            alloca
                                .as_instruction_value()
                                .unwrap()
                                .set_alignment(align)
                                .unwrap();
                            self.builder.build_store(alloca, x);
                            let alloca = self.builder.build_pointer_cast(
                                alloca,
                                self.any_ty().into_pointer_type(),
                                "union_ptr_casted",
                            );
                            (alloca, v)
                        }
                        Type::PtrEnum(v) => {
                            let ptr = unsafe {
                                self.builder.build_in_bounds_gep(
                                    x.into_pointer_value(),
                                    &[self.size_ty().const_int(8, false)],
                                    "ref_slot",
                                )
                            };
                            (ptr, v)
                        }
                        _ => unreachable!(),
                    };

                    let align = v.iter().map(|t| t.alignment()).max().unwrap_or(0);
                    let mut tag_size = tag_bytes(v.len());
                    let tag = if tag_size != 0 {
                        tag_size = tag_size.max(align);
                        let tag_bits = tag_size * 8;
                        let tag_ty = self.cxt.custom_width_int_type(tag_bits);
                        let tag_slot = self
                            .builder
                            .build_bitcast(ptr, tag_ty.gc_ptr(), "tag_slot")
                            .into_pointer_value();
                        self.builder
                            .build_load(tag_slot, "ifcase_tag")
                            .into_int_value()
                    } else {
                        unreachable!()
                    };

                    let cond = self.builder.build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        tag.get_type().const_int(i as u64, false),
                        "ifcase.cond",
                    );
                    self.builder.build_conditional_branch(cond, bthen, belse);

                    self.builder.position_at_end(bthen);
                    let payload_slot = unsafe {
                        self.builder.build_in_bounds_gep(
                            ptr,
                            &[self.size_ty().const_int(tag_size.into(), false)],
                            "payload_slot",
                        )
                    };
                    let payload = self.load(&payload_ty, payload_slot, data);
                    self.gen_call(fthen, vec![(payload, payload_ty)], None, data);

                    self.builder.position_at_end(belse);
                    self.gen_call(felse, vec![], None, data);
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
                        .map(|&x| {
                            let x = data.slots.unredirect(x);
                            let ty = tys.get(x).unwrap().0;
                            let ty = self.as_type(ty, data);
                            let x = self.gen_value(x, data);
                            (x, ty)
                        })
                        .collect();
                    let cont = bfun.call_args.last().map(|&x| {
                        let x = data.slots.unredirect(x);
                        let ty = tys.get(x).unwrap().0;
                        let ty = self.as_type(ty, data);
                        (x, ty)
                    });
                    self.gen_call(bfun.callee, args, cont, data);
                }
            }
        }
    }
}

impl<'a> System<'a> for &Cxt<'_> {
    type SystemData = (
        ReadStorage<'a, Slot>,
        Entities<'a>,
        ReadStorage<'a, FunMode>,
        ReadStorage<'a, Uses>,
        ReadStorage<'a, ValType>,
        ReadStorage<'a, Name>,
    );

    fn run(&mut self, (slots, entities, modes, uses, tys, names): Self::SystemData) {
        self.codegen(
            &Data {
                slots,
                entities,
                uses,
            },
            &modes,
            &tys,
            &names,
        );
    }
}
