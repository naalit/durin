use crate::emit::ValPretty;
use crate::ir::{Constant, Function, Name, Node, Slot, Slots, Uses, Val, ValExt, ValType};
use crate::ssa::{FunMode, SSA};
use inkwell::{
    basic_block::BasicBlock, builder::Builder, context::Context, module::Module,
    targets::TargetMachine, types::*, values::*, AddressSpace, IntPredicate,
};
use specs::prelude::*;
use std::{
    cell::RefCell,
    collections::{HashMap, VecDeque},
    convert::TryInto,
};

// Some calling conventions
pub const TAILCC: u32 = 18;
pub const CCC: u32 = 0;
pub const FASTCC: u32 = 8;
pub const DO_TAIL_CALL: bool = true;

/// The number of bytes we're willing to copy around freely on the stack.
/// If a struct or enum goes above this, we'll heap- or stack-allocate it instead.
pub const STACK_THRESHOLD: u32 = 16;

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

pub fn padding(size: u32, align: u32) -> u32 {
    // (-size) & (align - 1)
    if align == 0 {
        return 0;
    }
    assert!(align.is_power_of_two());
    size.wrapping_neg() & (align - 1)
}
pub fn tag_bytes(len: usize) -> u32 {
    match len {
        0..=1 => 0,
        2..=256 => 1,
        257..=65536 => 4,
        _ => 8,
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
    pub fn padding_llvm(&self, size: IntValue<'cxt>, align: u32) -> IntValue<'cxt> {
        // The same as `padding()` above: `(-size) & (align - 1)`
        if align == 0 {
            return self.size_ty().const_zero();
        }
        assert!(
            align.is_power_of_two(),
            "alignment {} is not a power of two",
            align
        );
        let msize = self.builder.build_int_neg(size, "-size");
        self.builder.build_and(
            msize,
            self.size_ty().const_int(align as u64 - 1, false),
            "padding",
        )
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
        println!("Push {}", key.id());
        self.upvalues.borrow_mut().insert(key, val);
    }

    pub fn pop_val(&self, key: Val) {
        println!("Pop {}", key.id());
        self.upvalues.borrow_mut().remove(&key);
    }

    pub fn new(cxt: &'cxt Context, machine: &'cxt TargetMachine) -> Self {
        let module = cxt.create_module("main");

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

#[derive(Debug, Clone, PartialEq)]
pub enum Type<'cxt> {
    Pointer,
    StackStruct(Vec<(Option<Val>, Type<'cxt>)>),
    PtrStruct(Vec<(Option<Val>, Type<'cxt>)>),
    StackEnum(u32, Vec<Type<'cxt>>),
    PtrEnum(Vec<Type<'cxt>>),
    Unknown(PointerValue<'cxt>),
    Unknown2(Val),
    Int(u32),
    Closure(usize),
    ExternFun(Vec<BasicTypeEnum<'cxt>>, BasicTypeEnum<'cxt>),
    Type,
}
impl<'cxt> Type<'cxt> {
    fn alignment(&self) -> u32 {
        match self {
            Type::StackStruct(v) | Type::PtrStruct(v) => {
                if v.is_empty() {
                    0
                } else {
                    v[0].1.alignment()
                }
            }
            Type::StackEnum(bytes, _) => *bytes.min(&8),
            Type::PtrEnum(v) => {
                let mut align = 0;
                for i in v {
                    let ialign = i.alignment();
                    if ialign > align {
                        align = ialign;
                    }
                }
                let tag = tag_bytes(v.len());
                tag.max(align)
            }
            // Word-alignment for values of unknown type
            Type::Unknown(_) | Type::Unknown2(_) => 8,
            Type::Int(bits) => (bits / 8).min(8),
            Type::Closure(_) | Type::ExternFun(_, _) | Type::Pointer | Type::Type => 8,
        }
    }

    fn stack_size(&self) -> Option<u32> {
        match self {
            Type::StackStruct(v) => {
                let mut size = 0;
                for (_, i) in v {
                    let x = i.stack_size().unwrap_or(8);
                    let align = i.alignment();
                    if align > 0 {
                        size += padding(size, align);
                    }
                    size += x;
                }
                Some(size)
            }
            Type::PtrStruct(v) => {
                let mut size = 0;
                for (_, i) in v {
                    let x = i.stack_size()?;
                    let align = i.alignment();
                    if align > 0 {
                        size += padding(size, align);
                    }
                    size += x;
                }
                Some(size)
            }
            Type::StackEnum(size, _) => Some(*size),
            Type::PtrEnum(v) => {
                let mut payload = 0;
                let mut align = 0;
                for i in v {
                    let size = i.stack_size()?;
                    if size > payload {
                        payload = size;
                    }
                    let ialign = i.alignment();
                    if ialign > align {
                        align = ialign;
                    }
                }
                let mut tag = tag_bytes(v.len());
                if tag != 0 {
                    tag = tag.max(align);
                }
                Some(tag + payload)
            }
            Type::Unknown(_) | Type::Unknown2(_) => None,
            Type::Int(bits) => Some(bits / 8),
            // TODO should we ever unbox closures?
            Type::Closure(_) => Some(16),
            Type::ExternFun(_, _) => Some(8),
            Type::Type => Some(8),
            Type::Pointer => Some(8),
        }
    }

    fn heap_size(
        &self,
        cxt: &Cxt<'cxt>,
        slots: &ReadStorage<Slot>,
        uses: &ReadStorage<Uses>,
    ) -> IntValue<'cxt> {
        match self {
            Type::StackStruct(v) | Type::PtrStruct(v) => {
                let mut size = cxt.size_ty().const_zero();
                for (_, i) in v {
                    let x = i.heap_size(cxt, slots, uses);
                    let align = i.alignment();
                    if align > 0 {
                        let padding = cxt.padding_llvm(size, align);
                        size = cxt.builder.build_int_add(size, padding, "aligned_size");
                    }
                    size = cxt.builder.build_int_add(size, x, "struct_size");
                }
                size
            }
            Type::PtrEnum(v) => {
                let mut payload = cxt.size_ty().const_zero();
                let mut align = 0;
                for i in v {
                    let size = i.heap_size(cxt, slots, uses);
                    let gt = cxt
                        .builder
                        .build_int_compare(IntPredicate::UGT, size, payload, "gt");
                    payload = cxt
                        .builder
                        .build_select(gt, size, payload, "payload_size")
                        .into_int_value();

                    let ialign = i.alignment();
                    if ialign > align {
                        align = ialign;
                    }
                }
                let mut tag = tag_bytes(v.len());
                if tag != 0 {
                    tag = tag.max(align);
                    cxt.builder.build_int_add(
                        payload,
                        cxt.size_ty().const_int(tag.into(), false),
                        "sum_ty_size",
                    )
                } else {
                    payload
                }
            }
            Type::Unknown(v) => {
                let int32 = cxt.builder.build_load(*v, "ty_size").into_int_value();
                let int32 = cxt.builder.build_and(
                    int32,
                    cxt.cxt.i32_type().const_int((1 << 16) - 1, false),
                    "ty_size_trunc",
                );
                cxt.builder
                    .build_int_z_extend(int32, cxt.size_ty(), "size_i64")
            }
            Type::Unknown2(v) => Type::Unknown(cxt.gen_value(*v, slots, uses).into_pointer_value())
                .heap_size(cxt, slots, uses),
            Type::StackEnum(_, _)
            | Type::Pointer
            | Type::Int(_)
            | Type::Closure(_)
            | Type::ExternFun(_, _)
            | Type::Type => cxt
                .size_ty()
                .const_int(self.stack_size().unwrap().into(), false),
        }
    }

    fn llvm_ty(&self, cxt: &Cxt<'cxt>) -> BasicTypeEnum<'cxt> {
        match self {
            Type::StackStruct(v) => {
                let v: Vec<_> = v.iter().map(|(_, x)| x.llvm_ty(cxt)).collect();
                cxt.cxt.struct_type(&v, false).as_basic_type_enum()
            }
            Type::PtrStruct(_) => cxt.any_ty(),
            Type::StackEnum(bytes, _) => {
                // TODO use int types for small enums
                // if *bytes <= 16 {
                //     cxt.cxt
                //         .custom_width_int_type(*bytes * 8)
                //         .as_basic_type_enum()
                // } else {
                cxt.cxt.i8_type().array_type(*bytes).as_basic_type_enum()
                // }
            }
            Type::PtrEnum(_) => cxt.any_ty(),
            Type::Unknown(_) | Type::Unknown2(_) => cxt.any_ty(),
            Type::Pointer => cxt.any_ty(),
            Type::Int(bits) => cxt.cxt.custom_width_int_type(*bits).as_basic_type_enum(),
            Type::Closure(nargs) => {
                // Add an argument for the environment
                let args = vec![cxt.any_ty(); *nargs as usize + 1];
                let fun_ty = cxt
                    .cxt
                    .void_type()
                    .fn_type(&args, false)
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum();
                cxt.cxt
                    .struct_type(&[cxt.any_ty(), fun_ty], false)
                    .as_basic_type_enum()
            }
            Type::ExternFun(v, ret) => ret
                .fn_type(&v, false)
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum(),
            Type::Type => cxt
                .cxt
                .i32_type()
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum(),
        }
    }

    fn tyinfo(&self, info: &mut TyInfo<'cxt>) {
        match self {
            Type::Pointer => info.word(true),
            Type::StackStruct(tys) | Type::PtrStruct(tys) => {
                for (_, ty) in tys {
                    ty.tyinfo(info);
                }
            }
            Type::StackEnum(_, tys) | Type::PtrEnum(tys) => {
                // For enums, the tag size happens to always equal alignment
                let tag_size = self.alignment();
                info.start_variant(tys.len(), tag_size);

                for ty in tys {
                    info.next_variant();
                    ty.tyinfo(info);
                }

                info.end_variant();
            }
            Type::Unknown(v) => info.splice(*v),
            Type::Unknown2(_) => panic!("Unknown2 not supported"),
            Type::Int(i) => {
                if *i == 64 {
                    info.word(false);
                } else {
                    info.extra_bytes(*i / 8);
                }
            }
            Type::Closure(_) => {
                // TODO fully boxed closures
                info.word(true);
                info.word(false);
            }
            Type::ExternFun(_, _) => info.word(false),
            Type::Type => info.word(true),
        }
    }
}

enum TyInfoPart<'cxt> {
    Constant(Vec<u32>),
    Splice(PointerValue<'cxt>, bool),
}
impl<'cxt> TyInfoPart<'cxt> {
    fn extend(&mut self) {
        match self {
            TyInfoPart::Constant(v) => {
                // Mark the last entry as continued
                v.last_mut().map(|x| *x |= 1);
            }
            TyInfoPart::Splice(_, b) => *b = true,
        }
    }
}

enum LastType {
    Normal,
    VariantNext,
    VariantEnd(usize),
}

struct TyInfo<'cxt> {
    run_words: Vec<bool>,
    variant_stack: Vec<usize>,
    last: LastType,
    extra_bytes: u32,
    entries: Vec<TyInfoPart<'cxt>>,
}
impl<'cxt> TyInfo<'cxt> {
    fn extend(&mut self) {
        match self.last {
            LastType::Normal => {
                self.entries.last_mut().map(TyInfoPart::extend);
            }
            LastType::VariantNext => (),
            LastType::VariantEnd(i) => self.entries[i].extend(),
        }
        self.last = LastType::Normal;
    }

    fn push_raw(&mut self, entry: u32) {
        match self.entries.last_mut() {
            Some(TyInfoPart::Constant(v)) => v.push(entry),
            _ => self.entries.push(TyInfoPart::Constant(vec![entry])),
        }
    }

    fn new() -> Self {
        TyInfo {
            run_words: Vec::new(),
            variant_stack: Vec::new(),
            last: LastType::Normal,
            extra_bytes: 0,
            entries: Vec::new(),
        }
    }
}
impl<'cxt> TyInfo<'cxt> {
    fn splice(&mut self, ty: PointerValue<'cxt>) {
        self.finish_bitset();

        self.extend();
        self.entries.push(TyInfoPart::Splice(ty, false));
    }

    fn start_variant(&mut self, num: usize, tag_size: u32) {
        let offset = self.extra_bytes & 7;
        self.extra_bytes = offset;
        self.finish_bitset();

        self.variant_stack.push(self.entries.len());
        let num: u16 = num.try_into().expect("Too many variants");
        assert!(tag_size <= 8, "tag must be <= 8 bytes, got {}", tag_size);
        let entry = 0b01_0 | ((tag_size - 1) << 3) | (offset << 6) | ((num as u32) << 16);
        self.entry(entry);
    }

    fn next_variant(&mut self) {
        self.last = LastType::VariantNext;
    }

    fn end_variant(&mut self) {
        self.last = LastType::VariantEnd(self.variant_stack.pop().unwrap());
    }

    fn word(&mut self, is_pointer: bool) {
        self.finish_bytes();
        self.run_words.push(is_pointer);
    }

    fn extra_bytes(&mut self, bytes: u32) {
        self.extra_bytes += bytes;
    }

    fn entry(&mut self, entry: u32) {
        self.finish_bitset();

        // Mark the last entry as continued
        self.extend();
        self.push_raw(entry);
    }

    fn finish_bytes(&mut self) {
        let extra_bytes_padded = (self.extra_bytes + 7) & !7;
        let extra_words = extra_bytes_padded / 8;
        for _ in 0..extra_words {
            self.run_words.push(false);
        }
        self.extra_bytes = 0;
    }

    fn finish_bitset(&mut self) {
        self.finish_bytes();

        if !self.run_words.is_empty() {
            if self.run_words.len() > 24 {
                todo!("more than one bitset word")
            }

            let mut bitset: u32 = (self.run_words.len() as u32) << 3;
            for (i, b) in self.run_words.drain(..).enumerate() {
                if b {
                    bitset |= 1 << (i + 8);
                }
            }

            // Mark the last entry as continued
            self.extend();
            self.push_raw(bitset);
        }
    }

    fn codegen(mut self, ty_size: IntValue<'cxt>, cxt: &Cxt<'cxt>) -> PointerValue<'cxt> {
        self.finish_bitset();
        // Make sure it doesn't end with part of a variant, so that we can `| 1` the last entry of a spliced rtti entry
        match self.last {
            LastType::VariantNext => unreachable!(),
            // 0 is an empty bitset
            LastType::VariantEnd(_) => self.entry(0),
            LastType::Normal => (),
        }

        let ty_size = cxt
            .builder
            .build_int_truncate(ty_size, cxt.cxt.i32_type(), "ty_size_i32");

        // Don't malloc if it's constant
        if self.entries.len() == 1 {
            if let TyInfoPart::Constant(v) = &self.entries[0] {
                let rtti_size = v.len() * 4;
                let rtti_size = cxt
                    .cxt
                    .i32_type()
                    .const_int((rtti_size << 16) as u64, false);
                let sizes = cxt.builder.build_or(rtti_size, ty_size, "rtti_sizes");

                let values: Vec<_> = std::iter::once(sizes)
                    .chain(
                        v.iter()
                            .map(|&x| cxt.cxt.i32_type().const_int(x as u64, false)),
                    )
                    .collect();

                let arr = cxt.cxt.i32_type().const_array(&values);
                let global = cxt.module.add_global(arr.get_type(), None, "const_rtti");
                global.set_constant(true);
                global.set_alignment(8);
                global.set_initializer(&arr);

                return cxt
                    .builder
                    .build_bitcast(
                        global.as_pointer_value(),
                        cxt.cxt.i32_type().ptr_type(AddressSpace::Generic),
                        "const_rtti_ptr",
                    )
                    .into_pointer_value();
            }
        }

        let mut size = cxt.size_ty().const_int(0, false);
        let mut splice_sizes = VecDeque::new();
        for entry in &self.entries {
            match entry {
                TyInfoPart::Constant(v) => {
                    let esize = cxt.size_ty().const_int((v.len() * 4) as u64, false);
                    size = cxt.builder.build_int_add(size, esize, "rtti_size");
                }
                TyInfoPart::Splice(ptr, _) => {
                    let esize = cxt
                        .builder
                        .build_load(*ptr, "spliced_rtti_sizes")
                        .into_int_value();
                    let esize = cxt.builder.build_right_shift(
                        esize,
                        cxt.cxt.i32_type().const_int(16, false),
                        false,
                        "spliced_rtti_size",
                    );
                    let esize = cxt.builder.build_int_z_extend(
                        esize,
                        cxt.size_ty(),
                        "spliced_rtti_size_i64",
                    );
                    splice_sizes.push_back(esize);
                    size = cxt.builder.build_int_add(size, esize, "rtti_size");
                }
            }
        }

        let malloc = cxt
            .builder
            .build_array_malloc(cxt.cxt.i8_type(), size, "rtti_slot")
            .unwrap();
        let mut slot = cxt
            .builder
            .build_bitcast(
                malloc,
                cxt.cxt.i32_type().ptr_type(AddressSpace::Generic),
                "rtti_slot_i32",
            )
            .into_pointer_value();

        let sizes = cxt
            .builder
            .build_int_truncate(size, cxt.cxt.i32_type(), "rtti_size_i32");
        let sizes = cxt.builder.build_left_shift(
            sizes,
            cxt.cxt.i32_type().const_int(16, false),
            "rtti_size_shl",
        );
        let sizes = cxt.builder.build_or(sizes, ty_size, "rtti_sizes");
        cxt.builder.build_store(slot, sizes);
        slot = unsafe {
            cxt.builder.build_in_bounds_gep(
                slot,
                &[cxt.cxt.i32_type().const_int(1, false)],
                "rtti_slots",
            )
        };

        for entry in &self.entries {
            match entry {
                TyInfoPart::Constant(v) => {
                    let values: Vec<_> = v
                        .iter()
                        .map(|x| cxt.cxt.i32_type().const_int(*x as u64, false))
                        .collect();
                    let arr = cxt.cxt.i32_type().const_array(&values);
                    let arr_slot = cxt
                        .builder
                        .build_bitcast(
                            slot,
                            arr.get_type().ptr_type(AddressSpace::Generic),
                            "const_rtti_slot",
                        )
                        .into_pointer_value();
                    cxt.builder.build_store(arr_slot, arr);

                    slot = unsafe {
                        cxt.builder.build_in_bounds_gep(
                            slot,
                            &[cxt.cxt.i32_type().const_int(v.len() as u64, false)],
                            "rtti_next_slot",
                        )
                    };
                }
                TyInfoPart::Splice(ptr, b) => {
                    // Skip the size to get to the actual entries
                    let ptr = unsafe {
                        cxt.builder.build_in_bounds_gep(
                            *ptr,
                            &[cxt.cxt.i32_type().const_int(1, false)],
                            "spliced_rtti",
                        )
                    };

                    let size = splice_sizes.pop_front().unwrap();
                    cxt.builder.build_memcpy(slot, 4, ptr, 4, size).unwrap();
                    let size_i32s = cxt.builder.build_int_unsigned_div(
                        size,
                        cxt.size_ty().const_int(8, false),
                        "spliced_rtti_size_i32s",
                    );

                    if *b {
                        // Mark the last entry that it's continued
                        let last_idx = cxt.builder.build_int_sub(
                            size_i32s,
                            cxt.cxt.i32_type().const_int(1, false),
                            "spliced_rtti_last_idx",
                        );
                        let last_slot = unsafe {
                            cxt.builder.build_in_bounds_gep(
                                slot,
                                &[last_idx],
                                "spliced_rtti_last_slot",
                            )
                        };
                        let last_entry = cxt
                            .builder
                            .build_load(last_slot, "spliced_rtti_last_entry")
                            .into_int_value();
                        let last_entry = cxt.builder.build_or(
                            last_entry,
                            cxt.cxt.i32_type().const_int(1, false),
                            "spliced_rtti_last_entry_continued",
                        );
                        cxt.builder.build_store(last_slot, last_entry);
                    }

                    slot = unsafe {
                        cxt.builder
                            .build_in_bounds_gep(slot, &[size_i32s], "rtti_next_slot")
                    };
                }
            }
        }

        cxt.builder
            .build_bitcast(
                malloc,
                cxt.cxt.i32_type().ptr_type(AddressSpace::Generic),
                "rtti_slot_i32",
            )
            .into_pointer_value()
    }
}

impl<'cxt> Cxt<'cxt> {
    fn as_type(&self, val: Val, slots: &ReadStorage<Slot>, uses: &ReadStorage<Uses>) -> Type<'cxt> {
        match slots.node(val).unwrap() {
            Node::FunType(i) => Type::Closure(*i),
            Node::ExternFunType(args, ret) => {
                let args = args
                    .iter()
                    .map(|&x| self.as_type(x, slots, uses).llvm_ty(self))
                    .collect();
                let ret = self.as_type(*ret, slots, uses).llvm_ty(self);
                Type::ExternFun(args, ret)
            }
            Node::ProdType(v) => {
                let val = slots.unredirect(val);
                let v: Vec<_> = v.iter().enumerate().map(|(i, &x)| {
                    let ty = self.as_type(x, slots, uses);
                    let param = uses.get(val).unwrap().iter().find(|&&u| {
                        matches!(slots.node(u), Some(Node::Param(f, n)) if *f == val && *n as usize == i)
                            && !uses.get(u).unwrap().is_empty()
                    }).copied();
                    (param, ty)
                }).collect();

                // It's a StackStruct if the part we would put on the stack is smaller than STACK_THRESHOLD bytes
                let mut static_size = 0;
                for (_, i) in &v {
                    let align = i.alignment();
                    if align > 0 {
                        static_size += padding(static_size, align);
                    }
                    static_size += i.stack_size().unwrap_or(0);
                }
                if static_size <= STACK_THRESHOLD {
                    Type::StackStruct(v)
                } else {
                    Type::PtrStruct(v)
                }
            }
            Node::SumType(v) => {
                if v.len() == 1 {
                    return self.as_type(v[0], slots, uses);
                }

                let v: Vec<_> = v.iter().map(|&x| self.as_type(x, slots, uses)).collect();

                // It's a StackEnum if it's statically sized, and smaller than STACK_THRESHOLD bytes
                let mut is_static = true;
                let mut payload = 0;
                let mut align = 0;
                for i in &v {
                    let size = i.stack_size().unwrap_or_else(|| {
                        is_static = false;
                        0
                    });
                    if !is_static {
                        break;
                    }

                    if size > payload {
                        payload = size;
                    }
                    let ialign = i.alignment();
                    if ialign > align {
                        align = ialign;
                    }
                }
                let mut tag = tag_bytes(v.len());
                if tag != 0 {
                    tag = tag.max(align);
                }
                let size = tag + payload;
                if is_static && size <= STACK_THRESHOLD {
                    Type::StackEnum(size, v)
                } else {
                    Type::PtrEnum(v)
                }
            }
            Node::RefTy(_) => Type::Pointer,
            Node::Const(c) => match *c {
                Constant::TypeType => Type::Type,
                Constant::IntType(w) => Type::Int(w.bits()),
                Constant::Int(_, _) | Constant::Stop | Constant::Unreachable => {
                    panic!("not a type")
                }
            },

            Node::Param(_, _) | Node::Proj(_, _, _) => match self.try_gen_value(val, slots, uses) {
                Some(v) => Type::Unknown(v.into_pointer_value()),
                None => Type::Unknown2(val),
            },

            Node::ExternFun(_, _, _)
            | Node::Fun(_)
            | Node::IfCase(_, _)
            | Node::ExternCall(_, _)
            | Node::If(_)
            | Node::Ref(_, _)
            | Node::Inj(_, _, _)
            | Node::Product(_, _)
            | Node::BinOp(_, _, _) => panic!("not a type"),
        }
    }

    fn to_any(
        &self,
        ty: &Type<'cxt>,
        val: BasicValueEnum<'cxt>,
        slots: &ReadStorage<Slot>,
        uses: &ReadStorage<Uses>,
    ) -> PointerValue<'cxt> {
        match ty {
            // Already a pointer, just do a bitcast to make sure it's the right type
            Type::Pointer
            | Type::PtrStruct(_)
            | Type::PtrEnum(_)
            | Type::Unknown(_)
            | Type::Unknown2(_)
            | Type::Type
            | Type::ExternFun(_, _) => self
                .builder
                .build_bitcast(val, self.any_ty(), "to_any")
                .into_pointer_value(),

            // It's an integer, so do an inttoptr
            // TODO: don't try to memcpy it when it's an Unknown
            Type::Int(bits) => {
                assert!(*bits <= 64, "too big for inttoptr");
                self.builder.build_int_to_ptr(
                    val.into_int_value(),
                    self.any_ty().into_pointer_type(),
                    "to_any",
                )
            }

            // Allocate and call `store`
            Type::StackStruct(_) | Type::StackEnum(_, _) | Type::Closure(_) => {
                let size = ty.heap_size(self, slots, uses);
                let malloc = self
                    .builder
                    .build_array_malloc(self.cxt.i8_type(), size, "any_slot")
                    .unwrap();
                self.store(ty, val, malloc, slots, uses);
                malloc
            }
        }
    }

    fn from_any(
        &self,
        ty: &Type<'cxt>,
        ptr: PointerValue<'cxt>,
        slots: &ReadStorage<Slot>,
        uses: &ReadStorage<Uses>,
    ) -> BasicValueEnum<'cxt> {
        match ty {
            // Already a pointer, just do a bitcast to make sure it's the right type
            Type::Pointer
            | Type::PtrStruct(_)
            | Type::PtrEnum(_)
            | Type::Unknown(_)
            | Type::Unknown2(_)
            | Type::Type
            | Type::ExternFun(_, _) => {
                let lty = ty.llvm_ty(self);
                self.builder.build_bitcast(ptr, lty, "from_any")
            }

            // It's an integer, so do an ptrtoint
            Type::Int(bits) => {
                assert!(*bits <= 64, "too big for ptrtoint");
                let int_type = self.cxt.custom_width_int_type(*bits);
                self.builder
                    .build_ptr_to_int(ptr, int_type, "from_any")
                    .as_basic_value_enum()
            }

            // Load from the pointer
            Type::StackStruct(_) | Type::StackEnum(_, _) | Type::Closure(_) => {
                self.load(ty, ptr, slots, uses)
            }
        }
    }

    /// Like from_any, but `from` is an actual pointer, not just something pointer-shaped.
    /// Small values that would otherwise be bitcasted to and from pointers will instead be actually loaded.
    /// The inverse of `store`, and also `gen_at`.
    fn load(
        &self,
        ty: &Type<'cxt>,
        from: PointerValue<'cxt>,
        slots: &ReadStorage<Slot>,
        uses: &ReadStorage<Uses>,
    ) -> BasicValueEnum<'cxt> {
        match ty {
            // Actually load
            Type::Pointer
            | Type::StackEnum(_, _)
            | Type::Int(_)
            | Type::Closure(_)
            | Type::ExternFun(_, _)
            | Type::Type => {
                let lty = ty.llvm_ty(self);
                let from = self
                    .builder
                    .build_bitcast(
                        from,
                        lty.ptr_type(AddressSpace::Generic),
                        "casted_load_slot",
                    )
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

                    let member = self.load(ty, ptr, slots, uses);
                    let isize = ty.heap_size(self, slots, uses);
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
                let size = ty.heap_size(self, slots, uses);
                let fits = self.builder.build_int_compare(
                    IntPredicate::ULE,
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
                            .build_bitcast(
                                from,
                                lty.ptr_type(AddressSpace::Generic),
                                "casted_load_slot",
                            )
                            .into_pointer_value();
                        self.builder.build_load(from, "load")
                    },
                    || {
                        // Leave it, it's a pointer anyway
                        // TODO: we probably will need to reallocate and copy for GC reasons, or maybe mutable ref reasons
                        from.as_basic_value_enum()
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
        slots: &ReadStorage<Slot>,
        uses: &ReadStorage<Uses>,
    ) {
        match ty {
            // Store
            Type::Pointer
            | Type::StackEnum(_, _)
            | Type::Int(_)
            | Type::Closure(_)
            | Type::ExternFun(_, _)
            | Type::Type => {
                let lty = from.get_type();
                let to = self
                    .builder
                    .build_bitcast(to, lty.ptr_type(AddressSpace::Generic), "casted_store_slot")
                    .into_pointer_value();
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
                    self.store(ty, member, ptr, slots, uses);

                    let isize = ty.heap_size(self, slots, uses);
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
                let size = ty.heap_size(self, slots, uses);
                let fits = self.builder.build_int_compare(
                    IntPredicate::ULE,
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
                        let to = self
                            .builder
                            .build_bitcast(
                                to,
                                lty.ptr_type(AddressSpace::Generic),
                                "casted_store_slot",
                            )
                            .into_pointer_value();
                        self.builder.build_store(to, from);
                    },
                    || {
                        // Copy the data this points to to the new location
                        let align = ty.alignment().max(1);
                        self.builder
                            .build_memcpy(to, align, from.into_pointer_value(), align, size)
                            .unwrap();
                    },
                )
            }
        }
    }

    /// Like gen_value, but store the result at `ptr`.
    /// Avoids allocating and copying when creating boxed values.
    /// It should take up the size specified in `vty.runtime_size()`.
    fn gen_at(
        &self,
        val: Val,
        vty: &Type<'cxt>,
        ptr: PointerValue<'cxt>,
        slots: &ReadStorage<Slot>,
        uses: &ReadStorage<Uses>,
    ) {
        let val = slots.unredirect(val);

        if let Some(&v) = self.upvalues.borrow().get(&val) {
            self.store(vty, v, ptr, slots, uses);
        }
        match slots.node(val).unwrap() {
            // Projection can be a memcpy instead of a store+load
            // LLVM will figure out the most efficient way to do it
            Node::Proj(ty, x, idx) => {
                let ty = self.as_type(*ty, slots, uses);
                match &ty {
                    Type::StackStruct(v) | Type::PtrStruct(v) => {
                        // TODO only compute the size once, and use bitwise and instead of alloca
                        let size = ty.heap_size(self, slots, uses);
                        let fits = self.builder.build_int_compare(
                            IntPredicate::ULE,
                            size,
                            self.size_ty().const_int(8, false),
                            "fits_in_word",
                        );
                        let val = self.gen_value(*x, slots, uses);
                        let mut ptr2 = self
                            .if_expr(
                                fits,
                                || {
                                    // If it fits in a word, put it in an alloca so we can still work with a pointer
                                    let ptr2 =
                                        self.builder.build_alloca(self.any_ty(), "proj_slot");
                                    self.builder.build_store(ptr2, val);
                                    ptr2.as_basic_value_enum()
                                },
                                || val,
                            )
                            .into_pointer_value();

                        let mut size = self.size_ty().const_zero();
                        for (i, (param, ty)) in v.iter().enumerate() {
                            let x = ty.heap_size(self, slots, uses);
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
                                    let p = self.load(&ty, ptr2, slots, uses);
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
                if matches!(slots.node(*ty), Some(Node::SumType(v)) if v.len() == 1) {
                    // Just do a load+store
                    let v = self.gen_value(val, slots, uses);
                    self.store(vty, v, ptr, slots, uses);
                }

                match &vty {
                    Type::StackEnum(_, v) | Type::PtrEnum(v) => {
                        let size = vty.heap_size(self, slots, uses);
                        let fits = self.builder.build_int_compare(
                            IntPredicate::ULE,
                            size,
                            self.size_ty().const_int(8, false),
                            "fits_in_word",
                        );

                        self.if_stmt(
                            fits,
                            || {
                                // Just do a load+store
                                let v = self.gen_value(val, slots, uses);
                                self.store(vty, v, ptr, slots, uses);
                            },
                            || {
                                let align = v.iter().map(|t| t.alignment()).max().unwrap_or(0);
                                let tag = tag_bytes(v.len());
                                if tag != 0 {
                                    let tag = tag.max(align);
                                    let tag = tag * 8;
                                    let tag = self.cxt.custom_width_int_type(tag);
                                    let tag_slot = self.builder.build_bitcast(
                                        ptr,
                                        tag.ptr_type(AddressSpace::Generic),
                                        "tag_slot",
                                    );
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
                                self.gen_at(*payload, &v[*i], payload_slot, slots, uses);
                            },
                        )
                    }
                    _ => unreachable!(),
                }
            }
            Node::Product(_, values) => match vty {
                Type::StackStruct(v) | Type::PtrStruct(v) => {
                    let mut size = self.size_ty().const_zero();
                    let mut padding = Vec::new();
                    for (p, i) in v {
                        let x = i.heap_size(self, slots, uses);
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

                    let fits = self.builder.build_int_compare(
                        IntPredicate::ULE,
                        size,
                        self.size_ty().const_int(8, false),
                        "fits_in_word",
                    );

                    self.if_stmt(
                        fits,
                        || {
                            // Just do a load+store
                            let v = self.gen_value(val, slots, uses);
                            self.store(vty, v, ptr, slots, uses);
                        },
                        || {
                            let mut next = ptr;
                            for (&val, (param, ty, size, padding)) in values.iter().zip(padding) {
                                if let Some(padding) = padding {
                                    next = unsafe {
                                        self.builder.build_in_bounds_gep(
                                            next,
                                            &[padding],
                                            "member_slot_padded",
                                        )
                                    };
                                }
                                if let Some(param) = param {
                                    // Is it better to gen it twice, or just store this?
                                    self.push_val(*param, self.gen_value(val, slots, uses));
                                }
                                self.gen_at(val, &ty, next, slots, uses);
                                next = unsafe {
                                    self.builder.build_in_bounds_gep(
                                        next,
                                        &[size],
                                        "next_member_slot",
                                    )
                                };
                            }
                            for (p, _) in v {
                                if let Some(p) = p {
                                    self.pop_val(*p);
                                }
                            }
                        },
                    )
                }
                _ => unreachable!(),
            },

            // For anything else, fall back to generating the value normally and storing it
            _ => {
                let v = self.gen_value(val, slots, uses);
                self.store(vty, v, ptr, slots, uses);
            }
        }
    }

    fn gen_value(
        &self,
        val: Val,
        slots: &ReadStorage<Slot>,
        uses: &ReadStorage<Uses>,
    ) -> BasicValueEnum<'cxt> {
        self.try_gen_value(val, slots, uses)
            .unwrap_or_else(|| panic!("Failed to gen_value %{}", val.id()))
    }

    fn try_gen_value(
        &self,
        val: Val,
        slots: &ReadStorage<Slot>,
        uses: &ReadStorage<Uses>,
    ) -> Option<BasicValueEnum<'cxt>> {
        let val = slots.unredirect(val);

        if let Some(&v) = self.upvalues.borrow().get(&val) {
            return Some(v);
        }
        Some(match slots.node(val).unwrap() {
            Node::Fun(_) => {
                // Create a closure
                let functions = self.functions.borrow();
                let LFunction {
                    arity,
                    unknown,
                    env,
                    ..
                } = functions
                    .get(&val)
                    .unwrap_or_else(|| panic!("Couldn't find fun {}", val.id()));

                // Create the environment struct, then store it in an alloca and bitcast the pointer to i8*
                // TODO use `gen_at()`
                let env = match env.len() {
                    0 => self.any_ty().into_pointer_type().get_undef(),
                    1 => {
                        // If there's only one upvalue, treat it like an `any`
                        let (val, _, ty) = &env[0];
                        let val = self.try_gen_value(*val, slots, uses)?;
                        self.to_any(ty, val, slots, uses)
                    }
                    _ => {
                        let env_tys: Vec<_> = env.iter().map(|&(_, ty, _)| ty).collect();
                        let mut env_val = self.cxt.struct_type(&env_tys, false).get_undef();
                        for (i, &(val, _, _)) in env.iter().enumerate() {
                            // TODO reuse values (all over the codebase but especially here)
                            let val = self.gen_value(val, slots, uses);
                            env_val = self
                                .builder
                                .build_insert_value(env_val, val, i as u32, "env_insert")
                                .unwrap()
                                .into_struct_value();
                        }
                        let env_ptr = self
                            .builder
                            .build_malloc(self.cxt.struct_type(&env_tys, false), "env_ptr")
                            .unwrap();
                        self.builder.build_store(env_ptr, env_val);
                        self.builder
                            .build_bitcast(env_ptr, self.any_ty(), "env")
                            .into_pointer_value()
                    }
                };

                // We use the unknown version of the function, which takes one environment parameter and all of type i8* (any)
                let arg_tys: Vec<_> = (0..arity + 1).map(|_| self.any_ty()).collect();
                let fun_ty = self
                    .cxt
                    .void_type()
                    .fn_type(&arg_tys, false)
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum();

                let cl = self
                    .cxt
                    .struct_type(&[self.any_ty(), fun_ty], false)
                    .get_undef();
                let cl = self
                    .builder
                    .build_insert_value(cl, env, 0, "cl_partial")
                    .unwrap();
                let cl = self
                    .builder
                    .build_insert_value(cl, unknown.as_global_value().as_pointer_value(), 1, "cl")
                    .unwrap();

                cl.as_basic_value_enum()
            }
            Node::ExternFun(name, params, ret) => {
                let fun = match self.module.get_function(name) {
                    Some(fun) => fun,
                    None => {
                        let rty = self.as_type(*ret, slots, uses).llvm_ty(self);
                        let ptys: Vec<_> = params
                            .iter()
                            .map(|t| self.as_type(*t, slots, uses).llvm_ty(self))
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
                let ty = self.as_type(*ty, slots, uses);
                match &ty {
                    Type::StackStruct(_) => {
                        let x = self.try_gen_value(*x, slots, uses)?.into_struct_value();
                        self.builder
                            .build_extract_value(x, *idx as u32, "project")
                            .unwrap()
                    }
                    Type::PtrStruct(v) => {
                        // TODO only compute the size once, and use bitwise and instead of alloca
                        let val = self.try_gen_value(*x, slots, uses)?;
                        let size = ty.heap_size(self, slots, uses);
                        let fits = self.builder.build_int_compare(
                            IntPredicate::ULE,
                            size,
                            self.size_ty().const_int(8, false),
                            "fits_in_word",
                        );
                        let mut ptr = self
                            .if_expr(
                                fits,
                                || {
                                    // If it fits in a word, put it in an alloca so we can still work with a pointer
                                    let ptr = self.builder.build_alloca(self.any_ty(), "proj_slot");
                                    self.builder.build_store(ptr, val);
                                    self.builder.build_bitcast(
                                        ptr,
                                        self.any_ty(),
                                        "proj_slot_casted",
                                    )
                                },
                                || val,
                            )
                            .into_pointer_value();

                        let mut size = self.size_ty().const_zero();
                        for (i, (param, ty)) in v.iter().enumerate() {
                            let x = ty.heap_size(self, slots, uses);
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
                                return Some(self.load(ty, ptr, slots, uses));
                            } else {
                                if let Some(param) = param {
                                    self.push_val(*param, self.load(ty, ptr, slots, uses));
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
                if matches!(slots.node(*ty), Some(Node::SumType(v)) if v.len() == 1) {
                    // No tag or casting needed
                    return self.try_gen_value(*payload, slots, uses);
                }

                let ty = self.as_type(*ty, slots, uses);
                match &ty {
                    Type::StackEnum(_, v) | Type::PtrEnum(v) => {
                        let mut payload_size = self.size_ty().const_zero();
                        let mut align = 0;
                        for i in v {
                            let size = i.heap_size(self, slots, uses);
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
                            IntPredicate::ULE,
                            size,
                            self.size_ty().const_int(8, false),
                            "fits_in_word",
                        );
                        let malloc = match &ty {
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
                                        self.builder.build_bitcast(
                                            alloca,
                                            self.any_ty(),
                                            "sum_type_slot",
                                        )
                                    },
                                    || {
                                        self.builder
                                            .build_array_malloc(
                                                self.cxt.i8_type(),
                                                size,
                                                "sum_type_malloc",
                                            )
                                            .unwrap()
                                            .as_basic_value_enum()
                                    },
                                )
                                .into_pointer_value(),
                            _ => unreachable!(),
                        };

                        if tag != 0 {
                            let tag = tag * 8;
                            let tag = self.cxt.custom_width_int_type(tag);
                            let tag_slot = self.builder.build_bitcast(
                                malloc,
                                tag.ptr_type(AddressSpace::Generic),
                                "tag_slot",
                            );
                            let tag = tag.const_int(*i as u64, false).as_basic_value_enum();
                            self.builder.build_store(tag_slot.into_pointer_value(), tag);
                        }

                        let payload_slot = unsafe {
                            self.builder.build_in_bounds_gep(
                                malloc,
                                &[self.size_ty().const_int(tag.into(), false)],
                                "payload_slot",
                            )
                        };
                        self.gen_at(*payload, &v[*i], payload_slot, slots, uses);

                        match &ty {
                            Type::StackEnum(_, _) => {
                                // Copy the enum out of the alloca
                                let llvm_ty = ty.llvm_ty(self);
                                let malloc = self.builder.build_bitcast(
                                    malloc,
                                    llvm_ty.ptr_type(AddressSpace::Generic),
                                    "sum_type_casted",
                                );
                                self.builder
                                    .build_load(malloc.into_pointer_value(), "sum_type")
                            }
                            // Just return the pointer
                            Type::PtrEnum(_) => self.if_expr(
                                fits,
                                || {
                                    let ptr = self
                                        .builder
                                        .build_bitcast(
                                            malloc,
                                            self.any_ty().ptr_type(AddressSpace::Generic),
                                            "sum_type_bitcast_slot_again",
                                        )
                                        .into_pointer_value();
                                    self.builder.build_load(ptr, "sum_type_as_word")
                                },
                                || malloc.as_basic_value_enum(),
                            ),
                            _ => unreachable!(),
                        }
                    }
                    _ => unreachable!(),
                }
            }
            Node::Product(ty, values) => {
                let ty = self.as_type(*ty, slots, uses);
                match &ty {
                    Type::StackStruct(v) => {
                        let ty = ty.llvm_ty(self).into_struct_type();
                        let mut agg = ty.get_undef().as_aggregate_value_enum();
                        for (i, (x, (param, _))) in values.into_iter().zip(v).enumerate() {
                            let x = self.try_gen_value(*x, slots, uses)?;
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
                    Type::PtrStruct(v) => {
                        let mut size = self.size_ty().const_zero();
                        let mut padding = Vec::new();
                        for (p, i) in v {
                            let x = i.heap_size(self, slots, uses);
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

                        let fits = self.builder.build_int_compare(
                            IntPredicate::ULE,
                            size,
                            self.size_ty().const_int(8, false),
                            "fits_in_word",
                        );
                        let malloc = self
                            .if_expr(
                                fits,
                                || {
                                    let alloca = self
                                        .builder
                                        .build_alloca(self.any_ty(), "struct_bitcast_slot");
                                    self.builder
                                        .build_bitcast(alloca, self.any_ty(), "struct_slot")
                                },
                                || {
                                    self.builder
                                        .build_array_malloc(
                                            self.cxt.i8_type(),
                                            size,
                                            "struct_malloc",
                                        )
                                        .unwrap()
                                        .as_basic_value_enum()
                                },
                            )
                            .into_pointer_value();

                        let mut next = malloc;
                        for (&val, (param, ty, size, padding)) in values.iter().zip(padding) {
                            if let Some(padding) = padding {
                                next = unsafe {
                                    self.builder.build_in_bounds_gep(
                                        next,
                                        &[padding],
                                        "member_slot_padded",
                                    )
                                };
                            }
                            if let Some(param) = param {
                                // TODO Is it better to gen it twice, or just store this?
                                self.push_val(*param, self.gen_value(val, slots, uses));
                            }
                            self.gen_at(val, &ty, next, slots, uses);
                            next = unsafe {
                                self.builder
                                    .build_in_bounds_gep(next, &[size], "next_member_slot")
                            };
                        }

                        self.if_expr(
                            fits,
                            || {
                                let ptr = self
                                    .builder
                                    .build_bitcast(
                                        malloc,
                                        self.any_ty().ptr_type(AddressSpace::Generic),
                                        "struct_bitcast_slot_again",
                                    )
                                    .into_pointer_value();
                                self.builder.build_load(ptr, "struct_as_word")
                            },
                            || malloc.as_basic_value_enum(),
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
            Node::Const(Constant::Stop) | Node::Const(Constant::Unreachable) => {
                panic!("stop or unreachable isn't a first-class function!")
            }
            Node::FunType(_)
            | Node::ExternFunType(_, _)
            | Node::RefTy(_)
            | Node::ProdType(_)
            | Node::SumType(_)
            | Node::Const(Constant::TypeType)
            | Node::Const(Constant::IntType(_)) => {
                let ty = self.as_type(val, slots, uses);
                let mut tyinfo = TyInfo::new();
                ty.tyinfo(&mut tyinfo);
                let ty_size = ty.heap_size(self, slots, uses);
                tyinfo.codegen(ty_size, self).as_basic_value_enum()
            }
            Node::ExternCall(_, _) => panic!("externcall isn't a first-class function!"),
            Node::BinOp(op, a, b) => {
                let a = self.try_gen_value(*a, slots, uses)?;
                let b = self.try_gen_value(*b, slots, uses)?;
                // let name = self.name(val).unwrap_or_else(|| "binop".to_string());
                // let name = &name;
                let name = "binop";
                match op {
                    crate::ir::BinOp::IAdd => self
                        .builder
                        .build_int_add(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::ISub => self
                        .builder
                        .build_int_sub(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IMul => self
                        .builder
                        .build_int_mul(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IDiv => self
                        .builder
                        .build_int_signed_div(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IAnd => self
                        .builder
                        .build_and(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IOr => self
                        .builder
                        .build_or(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IXor => self
                        .builder
                        .build_xor(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IShl => self
                        .builder
                        .build_left_shift(a.into_int_value(), b.into_int_value(), name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IShr => self
                        .builder
                        // TODO unsigned vs signed (division too)
                        .build_right_shift(a.into_int_value(), b.into_int_value(), true, name)
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IExp => todo!("llvm.powi intrinsic"),

                    crate::ir::BinOp::IEq => self
                        .builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            a.into_int_value(),
                            b.into_int_value(),
                            name,
                        )
                        .as_basic_value_enum(),
                    crate::ir::BinOp::INEq => self
                        .builder
                        .build_int_compare(
                            IntPredicate::NE,
                            a.into_int_value(),
                            b.into_int_value(),
                            name,
                        )
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IGt => self
                        .builder
                        .build_int_compare(
                            IntPredicate::SGT,
                            a.into_int_value(),
                            b.into_int_value(),
                            name,
                        )
                        .as_basic_value_enum(),
                    crate::ir::BinOp::ILt => self
                        .builder
                        .build_int_compare(
                            IntPredicate::SLT,
                            a.into_int_value(),
                            b.into_int_value(),
                            name,
                        )
                        .as_basic_value_enum(),
                    crate::ir::BinOp::IGeq => self
                        .builder
                        .build_int_compare(
                            IntPredicate::SGE,
                            a.into_int_value(),
                            b.into_int_value(),
                            name,
                        )
                        .as_basic_value_enum(),
                    crate::ir::BinOp::ILeq => self
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
        })
    }

    fn cast(
        &self,
        x: BasicValueEnum<'cxt>,
        from: &Type<'cxt>,
        to: &Type<'cxt>,
        slots: &ReadStorage<Slot>,
        uses: &ReadStorage<Uses>,
    ) -> BasicValueEnum<'cxt> {
        if from == to {
            x
        } else {
            eprintln!("durin/info: Casting from {:?} to {:?}", from, to);
            let x = self.to_any(from, x, slots, uses);
            self.from_any(to, x, slots, uses)
        }
    }

    fn gen_call(
        &self,
        callee: Val,
        mut args: Vec<(BasicValueEnum<'cxt>, Type<'cxt>)>,
        cont: Option<(Val, Type<'cxt>)>,
        slots: &ReadStorage<Slot>,
        uses: &ReadStorage<Uses>,
        entities: &Entities,
    ) {
        match slots.node(callee) {
            // If we're calling the return continuation, emit a return instruction
            _ if self
                .cont
                .borrow()
                .as_ref()
                .map_or(false, |(x, _)| *x == callee) =>
            {
                if let Some((k, ty)) = cont {
                    args.push((self.gen_value(k, slots, uses), ty));
                }
                let args = args
                    .into_iter()
                    .zip(&self.cont.borrow().as_ref().unwrap().1)
                    .map(|((x, from), to)| self.cast(x, &from, to, slots, uses))
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
                    args.push((self.gen_value(k, slots, uses), ty));
                }
                let args = args
                    .into_iter()
                    .zip(tys)
                    .map(|((x, from), to)| self.cast(x, &from, to, slots, uses))
                    .collect::<Vec<_>>();
                // Set the parameters and jump to the target block
                for (&ptr, value) in params.iter().zip(args) {
                    self.builder.build_store(ptr, value);
                }
                self.builder.build_unconditional_branch(*target);
            }

            // Execute a ref op if we're doing one
            Some(Node::Ref(ty, op)) => {
                let ty = self.as_type(*ty, slots, uses);

                // Execute the operation
                let arg = match op {
                    crate::ir::RefOp::RefNew => {
                        let size = ty.heap_size(self, slots, uses);
                        let ptr = self
                            .builder
                            .build_array_malloc(self.cxt.i8_type(), size, "ref_ptr")
                            .unwrap();
                        Some((ptr.as_basic_value_enum(), Type::Pointer))
                    }
                    crate::ir::RefOp::RefGet(r) => {
                        let ptr = self.gen_value(*r, slots, uses).into_pointer_value();
                        let val = self.load(&ty, ptr, slots, uses);
                        Some((val, ty))
                    }
                    crate::ir::RefOp::RefSet(r, v) => {
                        let ptr = self.gen_value(*r, slots, uses).into_pointer_value();
                        // TODO are there circumstances when we can use `gen_at`?
                        let val = self.gen_value(*v, slots, uses);
                        self.store(&ty, val, ptr, slots, uses);
                        None
                    }
                };

                // Call the continuation
                let (cont, _) = cont.unwrap();
                let cont2 = arg.map(|(v, ty)| {
                    let n = entities.create();
                    self.upvalues.borrow_mut().insert(n, v);
                    (n, ty)
                });
                self.gen_call(cont, Vec::new(), cont2, slots, uses, entities)
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
                    slots.node(*callee),
                    Some(Node::Const(crate::ir::Constant::Unreachable))
                ) =>
            {
                self.builder.build_unreachable();
            }

            // If we're calling an extern function, do that
            Some(Node::ExternCall(f, ret_ty)) => {
                let args: Vec<_> = args.into_iter().map(|(v, _)| v).collect();
                let f = self.gen_value(*f, slots, uses);
                let call = self
                    .builder
                    .build_call(f.into_pointer_value(), &args, "extern_call");
                call.set_tail_call(DO_TAIL_CALL);

                let ret_ty = self.as_type(*ret_ty, slots, uses);

                let (cont, _) = cont.unwrap();
                self.gen_call(
                    cont,
                    vec![(call.try_as_basic_value().left().unwrap(), ret_ty)],
                    None,
                    slots,
                    uses,
                    entities,
                )
            }

            // Otherwise, we're actually calling a function
            _ => {
                // The mechanism depends on whether it's a known or unknown call
                match self.functions.borrow().get(&slots.unredirect(callee)) {
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
                            .map(|((x, from), to)| self.cast(x, &from, to, slots, uses))
                            .collect::<Vec<_>>();
                        let mut args: Vec<_> = env
                            .iter()
                            .map(|&(val, _, _)| self.gen_value(val, slots, uses))
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
                                let v = entities.create();
                                self.upvalues.borrow_mut().insert(v, x);
                                (v, ty)
                            });

                            self.gen_call(cont, args, acont, slots, uses, entities)
                        } else {
                            if let Some((k, ty)) = cont {
                                let v = self.gen_value(k, slots, uses);
                                let v = self.cast(v, &ty, param_tys.last().unwrap(), slots, uses);
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
                            args.push((self.gen_value(k, slots, uses), ty));
                        }

                        let callee = self.gen_value(callee, slots, uses).into_struct_value();
                        let env = self.builder.build_extract_value(callee, 0, "env").unwrap();
                        let fun_ptr = self
                            .builder
                            .build_extract_value(callee, 1, "fun_ptr")
                            .unwrap()
                            .into_pointer_value();

                        // It could be polymorphic, so we pass all arguments as word-size "any"
                        let mut args: Vec<_> = args
                            .into_iter()
                            .map(|(val, ty)| {
                                self.to_any(&ty, val, slots, uses).as_basic_value_enum()
                            })
                            .collect();
                        // The closure environment is the last argument
                        args.push(env);

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
        slots: &ReadStorage<Slot>,
        entities: &Entities,
        modes: &ReadStorage<FunMode>,
        uses: &ReadStorage<Uses>,
        tys: &ReadStorage<ValType>,
        names: &ReadStorage<Name>,
    ) {
        // Collect all functions and their blocks
        let mut to_gen: HashMap<Val, VecDeque<(Val, crate::ir::Function)>> = HashMap::new();
        let mut stack_enabled = HashMap::new();
        for (v, mode) in (entities, modes).join() {
            match mode {
                FunMode::SSA(cont) => {
                    to_gen
                        .entry(v)
                        .or_default()
                        .push_front((v, slots.fun(v).unwrap().clone()));
                    stack_enabled.insert(v, *cont);
                }
                FunMode::CPS => {
                    to_gen
                        .entry(v)
                        .or_default()
                        .push_front((v, slots.fun(v).unwrap().clone()));
                }
                FunMode::Block(parent) => {
                    to_gen
                        .entry(*parent)
                        .or_default()
                        .push_back((v, slots.fun(v).unwrap().clone()));
                }
            }
        }

        // Declare all the functions before generating their bodies
        for (val, blocks) in to_gen {
            let env = slots.env(val);

            if let Some(fun) = slots.fun(val).cloned() {
                // Get the continuation type by whatever is passed to the continuation
                let cont = stack_enabled.get(&val);
                let cont = cont.and_then(|&cont| {
                    let u = uses.get(cont).unwrap();
                    if u.is_empty() {
                        eprintln!("durin/warning: could not deduce continuation type (no uses)");
                        None
                    } else {
                        let u = u.clone();
                        for &i in &**u {
                            let ty = match slots.node(i).cloned() {
                                Some(Node::Fun(Function {
                                    callee, call_args, ..
                                })) if callee == cont => call_args
                                    .clone()
                                    .into_iter()
                                    .map(|x| slots.unredirect(x))
                                    .map(|x| **tys.get(x).unwrap())
                                    .map(|x| self.as_type(x, slots, uses))
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
                    .map(|&x| self.as_type(x, slots, uses).llvm_ty(self))
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

                let env = args[0..env.len()]
                    .iter()
                    .zip(env)
                    .map(|(&ty, (val, ty2))| (val, ty, self.as_type(ty2, slots, uses)))
                    .collect();

                let param_tys = fun
                    .params
                    .iter()
                    .map(|&x| self.as_type(x, slots, uses))
                    .collect();

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
                match env.len() {
                    0 => (),
                    1 => {
                        // There's only one upvalue, so treat the environment pointer as an `any`
                        let (val, _, ty) = &env[0];
                        let value = self.from_any(ty, env_ptr.into_pointer_value(), slots, uses);
                        self.upvalues.borrow_mut().insert(*val, value);
                    }
                    _ => {
                        let env_tys: Vec<_> = env.iter().map(|&(_, ty, _)| ty).collect();
                        let env_ty = self.cxt.struct_type(&env_tys, false);
                        let env_ptr = self.builder.build_bitcast(
                            env_ptr,
                            env_ty.ptr_type(AddressSpace::Generic),
                            "env_ptr",
                        );
                        let env_val = self
                            .builder
                            .build_load(env_ptr.into_pointer_value(), "env")
                            .into_struct_value();

                        // Add environment slots to the context
                        for (i, &(val, _, _)) in env.iter().enumerate() {
                            let value = self
                                .builder
                                .build_extract_value(
                                    env_val,
                                    i as u32,
                                    &names
                                        .get(val)
                                        .map(|n| n.0.clone())
                                        .unwrap_or_else(|| "upvalue".to_string()),
                                )
                                .unwrap();
                            self.upvalues.borrow_mut().insert(val, value);
                        }
                    }
                }

                // Call function
                let mut args: Vec<_> = blocks[0]
                    .1
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, &ty)| {
                        let ty = self.as_type(ty, slots, uses);
                        (
                            self.from_any(
                                &ty,
                                unknown.get_params()[i].into_pointer_value(),
                                slots,
                                uses,
                            ),
                            ty,
                        )
                    })
                    .collect();
                if let Some((vcont, cty)) = args.pop() {
                    // `gen_call` takes the continuation as a Val, not a BasicValueEnum; so, we use an unused Val slot and stick the BasicValueEnum in the upvalues map
                    let cont = entities.create();
                    {
                        self.upvalues.borrow_mut().insert(cont, vcont);
                    }
                    self.gen_call(*val, args, Some((cont, cty)), slots, uses, entities);
                } else {
                    self.gen_call(*val, args, None, slots, uses, entities);
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
                        let ty = self.as_type(ty, slots, uses);
                        let lty = ty.llvm_ty(self);
                        let name = bval.param_name(i as u8, uses, slots, names);
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
                if let Some(Node::If(x)) = slots.node(bfun.callee).cloned() {
                    assert_eq!(bfun.call_args.len(), 2);
                    let fthen = bfun.call_args[0];
                    let felse = bfun.call_args[1];

                    let cond = self.gen_value(x, slots, uses).into_int_value();

                    let bstart = self.builder.get_insert_block().unwrap();
                    let bthen = self.cxt.insert_basic_block_after(bstart, "if.then");
                    let belse = self.cxt.insert_basic_block_after(bthen, "if.else");

                    self.builder.build_conditional_branch(cond, bthen, belse);

                    self.builder.position_at_end(bthen);
                    self.gen_call(fthen, vec![], None, slots, uses, entities);

                    self.builder.position_at_end(belse);
                    self.gen_call(felse, vec![], None, slots, uses, entities);
                // If we're calling ifcase i x, do that instead
                } else if let Some(Node::IfCase(i, x)) = slots.node(bfun.callee).cloned() {
                    let vty = tys.get(x).unwrap().0;
                    let ty = self.as_type(vty, slots, uses);
                    let payload_ty = match vty.get(&slots) {
                        Node::SumType(v) if v.len() == 1 => {
                            // There's no tag, and no casting needed
                            assert_eq!(i, 0);
                            let x = self.gen_value(x, slots, uses);
                            assert_eq!(bfun.call_args.len(), 2);
                            let fthen = bfun.call_args[0];

                            self.gen_call(fthen, vec![(x, ty)], None, slots, uses, entities);

                            // Skip to the next basic block
                            continue;
                        }
                        Node::SumType(v) => v[i],
                        x => unreachable!("{:?}", x),
                    };
                    let payload_ty = self.as_type(payload_ty, slots, uses);

                    assert_eq!(bfun.call_args.len(), 2);
                    let fthen = bfun.call_args[0];
                    let felse = bfun.call_args[1];

                    let x = self.gen_value(x, slots, uses);

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
                            let alloca = self
                                .builder
                                .build_bitcast(alloca, self.any_ty(), "union_ptr_casted")
                                .into_pointer_value();
                            (alloca, v)
                        }
                        Type::PtrEnum(v) => (x.into_pointer_value(), v),
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
                            .build_bitcast(ptr, tag_ty.ptr_type(AddressSpace::Generic), "tag_slot")
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
                    let payload = self.load(&payload_ty, payload_slot, slots, uses);
                    self.gen_call(
                        fthen,
                        vec![(payload, payload_ty)],
                        None,
                        slots,
                        uses,
                        entities,
                    );

                    self.builder.position_at_end(belse);
                    self.gen_call(felse, vec![], None, slots, uses, entities);
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
                            let x = slots.unredirect(x);
                            let ty = tys.get(x).unwrap().0;
                            let ty = self.as_type(ty, slots, uses);
                            let x = self.gen_value(x, slots, uses);
                            (x, ty)
                        })
                        .collect();
                    let cont = bfun.call_args.last().map(|&x| {
                        let x = slots.unredirect(x);
                        let ty = tys.get(x).unwrap().0;
                        let ty = self.as_type(ty, slots, uses);
                        (x, ty)
                    });
                    self.gen_call(bfun.callee, args, cont, slots, uses, entities);
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
        self.codegen(&slots, &entities, &modes, &uses, &tys, &names);
    }
}
