use super::{Cxt, Data, InkwellTyExt};
use crate::ir::{Constant, Node, Slots, Val};
use inkwell::{types::*, values::*, AddressSpace, IntPredicate};
use std::{collections::VecDeque, convert::TryInto};

/// The number of bytes we're willing to copy around freely on the stack.
/// If a struct or enum goes above this, we'll heap- or stack-allocate it instead.
pub const STACK_THRESHOLD: u32 = 16;
/// The number of bytes we're willing to allocate inline in a sum or product type.
/// If a member goes above this, it's stored in its own allocation, unless it's explicitly unboxed.
pub const UNBOX_THRESHOLD: u32 = 256;

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

#[derive(Debug, Clone, PartialEq)]
pub enum Type<'cxt> {
    Pointer,
    Unbox(Box<Type<'cxt>>),
    StackStruct(Vec<Type<'cxt>>),
    PtrStruct(Vec<Type<'cxt>>),
    StackEnum(u32, Vec<Type<'cxt>>),
    PtrEnum(Vec<Type<'cxt>>),
    Unknown(PointerValue<'cxt>),
    Unknown2(Val),
    Int(u32),
    Float(crate::ir::FloatType),
    Closure(usize),
    ExternFun(Vec<BasicTypeEnum<'cxt>>, BasicTypeEnum<'cxt>),
    Type,
}
impl<'cxt> Type<'cxt> {
    /// Returns true if this type responds to explicit unboxing when storing in the heap
    pub fn can_unbox_ptr(&self) -> bool {
        matches!(
            self,
            Type::Unknown(_) | Type::Unknown2(_) | Type::PtrStruct(_) | Type::PtrEnum(_)
        )
    }

    pub fn alignment(&self) -> u32 {
        // Alignment less than 8 breaks polymorphism in certain cases
        // e.g.
        //   fun f (T: Type, x: T, y: T, r: fun 1) = call r ({ T, x, y } of sig { Type, T, T })
        //   fun g () = call f (I32, 1, 2, h)
        //   fun h (x: sig { Type, I32, I32 }) = call print x.2
        // here f will align x and y to 8 bytes assuming they might be pointers, but h will assume they're aligned to 4 bytes
        // TODO: it might be possible to use min(runtime_size(), 8), or mark polymorphic instantiations or something
        8

        // match self {
        //     Type::Unbox(x) => x.alignment(),
        //     Type::StackStruct(v) | Type::PtrStruct(v) => {
        //         if v.is_empty() {
        //             0
        //         } else {
        //             v[0].alignment()
        //         }
        //     }
        //     Type::StackEnum(bytes, _) => *bytes.min(&8),
        //     Type::PtrEnum(v) => {
        //         let mut align = 0;
        //         for i in v {
        //             let ialign = i.alignment();
        //             if ialign > align {
        //                 align = ialign;
        //             }
        //         }
        //         let tag = tag_bytes(v.len());
        //         tag.max(align)
        //     }
        //     // Word-alignment for values of unknown type
        //     Type::Unknown(_) | Type::Unknown2(_) => 8,
        //     Type::Int(bits) => (bits / 8).min(8),
        //     Type::Float(t) => match t {
        //         crate::ir::FloatType::F32 => 4,
        //         crate::ir::FloatType::F64 => 8,
        //     },
        //     Type::Closure(_) | Type::ExternFun(_, _) | Type::Pointer | Type::Type => 8,
        // }
    }

    pub fn stack_size(&self) -> Option<u32> {
        match self {
            Type::Unbox(x) => x.stack_size(),
            Type::StackStruct(v) => {
                let mut size = 0;
                for i in v {
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
                for i in v {
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
            // Round up - an i1 should be 1 byte, not 0
            Type::Int(bits) => Some((bits + 7) / 8),
            Type::Float(t) => match t {
                crate::ir::FloatType::F32 => Some(4),
                crate::ir::FloatType::F64 => Some(8),
            },
            Type::Closure(_) => Some(8),
            Type::ExternFun(_, _) => Some(8),
            Type::Type => Some(8),
            Type::Pointer => Some(8),
        }
    }

    pub fn heap_size(&self, cxt: &Cxt<'cxt>, data: &Data) -> IntValue<'cxt> {
        match self {
            Type::Unbox(x) => x.heap_size(cxt, data),
            Type::StackStruct(v) | Type::PtrStruct(v) => {
                let mut size = cxt.size_ty().const_zero();
                for i in v {
                    let x = i.heap_size(cxt, data);
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
                    let size = i.heap_size(cxt, data);
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
                let rtti_ptr = unsafe {
                    cxt.builder.build_in_bounds_gep(
                        *v,
                        &[cxt.size_ty().const_int(2, false)],
                        "rtti_ptr",
                    )
                };
                let int32 = cxt.builder.build_load(rtti_ptr, "ty_size").into_int_value();
                let int32 = cxt.builder.build_and(
                    int32,
                    cxt.cxt.i32_type().const_int((1 << 16) - 1, false),
                    "ty_size_trunc",
                );
                cxt.builder
                    .build_int_z_extend(int32, cxt.size_ty(), "size_i64")
            }
            Type::Unknown2(v) => {
                Type::Unknown(cxt.gen_value(*v, data).into_pointer_value()).heap_size(cxt, data)
            }
            Type::StackEnum(_, _)
            | Type::Pointer
            | Type::Int(_)
            | Type::Float(_)
            | Type::Closure(_)
            | Type::ExternFun(_, _)
            | Type::Type => cxt
                .size_ty()
                .const_int(self.stack_size().unwrap().into(), false),
        }
    }

    /// Whether this value would contain a pointer if allocated on the stack
    fn has_ptr(&self) -> bool {
        match self {
            Type::Unbox(x) => x.has_ptr(),
            Type::Pointer => true,
            Type::PtrStruct(_) => true,
            Type::PtrEnum(_) => true,
            Type::Unknown(_) => true,
            Type::Unknown2(_) => true,
            Type::Closure(_) => true,
            Type::Type => true,

            Type::Int(_) => false,
            Type::Float(_) => false,
            Type::ExternFun(_, _) => false,

            // Stack structs and enums can't have pointers in them
            // That's because LLVM can't see pointers inside of structs
            Type::StackStruct(_) => false,
            Type::StackEnum(_, _) => false,
        }
    }

    /// Whether this value might contain something of unknown size
    pub fn has_unknown(&self) -> bool {
        match self {
            Type::Unbox(x) => x.has_unknown(),
            Type::PtrStruct(v) => v.iter().any(Type::has_unknown),
            Type::PtrEnum(v) => v.iter().any(Type::has_unknown),
            Type::Unknown(_) => true,
            Type::Unknown2(_) => true,
            _ => false,
        }
    }

    pub fn llvm_ty(&self, cxt: &Cxt<'cxt>) -> BasicTypeEnum<'cxt> {
        match self {
            Type::Unbox(x) => x.llvm_ty(cxt),
            Type::StackStruct(v) => {
                let v: Vec<_> = v.iter().map(|x| x.llvm_ty(cxt)).collect();
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
            Type::Float(t) => match t {
                crate::ir::FloatType::F32 => cxt.cxt.f32_type().as_basic_type_enum(),
                crate::ir::FloatType::F64 => cxt.cxt.f64_type().as_basic_type_enum(),
            },
            Type::Closure(_) => cxt.any_ty(),
            Type::ExternFun(v, ret) => ret
                .fn_type(&v.iter().map(|&x| x.into()).collect::<Vec<_>>(), false)
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum(),
            Type::Type => cxt.cxt.i32_type().gc_ptr().as_basic_type_enum(),
        }
    }

    /// The same as `tyinfo()`, but the root type is always boxed (it doesn't listen to UNBOX_THRESHOLD).
    /// This is used with explicit unboxing, but also for the root RTTI of a heap allocation.
    fn tyinfo_unbox(&self, info: &mut TyInfo<'cxt>, cxt: &Cxt<'cxt>, data: &Data) {
        match self {
            Type::StackStruct(tys) | Type::PtrStruct(tys) => {
                for ty in tys {
                    ty.tyinfo(info, cxt, data);
                }
            }
            Type::StackEnum(_, tys) | Type::PtrEnum(tys) => {
                // For enums, the tag size happens to always equal alignment
                let tag_size = self.alignment();
                let heap_size = self.heap_size(cxt, data);
                info.start_variant(tys.len(), tag_size, heap_size, cxt);

                for ty in tys {
                    info.next_variant();
                    ty.tyinfo(info, cxt, data);
                }

                info.end_variant();
            }
            Type::Unknown(v) => {
                let rtti_ptr = unsafe {
                    cxt.builder.build_in_bounds_gep(
                        *v,
                        &[cxt.size_ty().const_int(2, false)],
                        "rtti_ptr",
                    )
                };
                info.splice(rtti_ptr)
            }
            Type::Unknown2(_) => panic!("Unknown2 not supported"),
            _ => self.tyinfo(info, cxt, data),
        }
    }

    /// Adds this type's info to `info`, assuming this type is the next member in a struct.
    /// If this type can be boxed and is larger than UNBOX_THRESHOLD, then it will just add a pointer word.
    fn tyinfo(&self, info: &mut TyInfo<'cxt>, cxt: &Cxt<'cxt>, data: &Data) {
        match self {
            Type::Unbox(x) => x.tyinfo_unbox(info, cxt, data),
            Type::Pointer => info.word(true),
            Type::StackStruct(tys) | Type::PtrStruct(tys) => {
                let heap_size = self.heap_size(cxt, data);

                cxt.or_box(heap_size, info, |info| {
                    for ty in tys {
                        ty.tyinfo(info, cxt, data);
                    }
                });
            }
            Type::StackEnum(_, tys) | Type::PtrEnum(tys) => {
                // For enums, the tag size happens to always equal alignment
                let tag_size = self.alignment();
                let heap_size = self.heap_size(cxt, data);

                cxt.or_box(heap_size, info, |info| {
                    info.start_variant(tys.len(), tag_size, heap_size, cxt);

                    for ty in tys {
                        info.next_variant();
                        ty.tyinfo(info, cxt, data);
                    }

                    info.end_variant();
                });
            }
            Type::Unknown(v) => {
                let heap_size = self.heap_size(cxt, data);

                cxt.or_box(heap_size, info, |info| {
                    let rtti_ptr = unsafe {
                        cxt.builder.build_in_bounds_gep(
                            *v,
                            &[cxt.size_ty().const_int(2, false)],
                            "rtti_ptr",
                        )
                    };
                    info.splice(rtti_ptr)
                })
            }
            Type::Unknown2(_) => panic!("Unknown2 not supported"),
            Type::Float(t) => match t {
                crate::ir::FloatType::F32 => info.extra_bytes(4),
                crate::ir::FloatType::F64 => info.word(false),
            },
            Type::Int(i) => {
                if *i == 64 {
                    info.word(false);
                } else {
                    info.extra_bytes(*i / 8);
                }
            }
            Type::Closure(_) => info.word(true),
            Type::ExternFun(_, _) => info.word(false),
            Type::Type => info.word(true),
        }
    }

    pub fn as_rtti(&self, cxt: &Cxt<'cxt>, data: &Data) -> PointerValue<'cxt> {
        let mut tyinfo = TyInfo::new();
        self.tyinfo_unbox(&mut tyinfo, cxt, data);
        let ty_size = self.heap_size(cxt, data);
        tyinfo.codegen(ty_size, cxt)
    }
}

impl<'cxt> Cxt<'cxt> {
    /// Runs `unbox(info)`, but if `size` is higher than `UNBOX_THRESHOLD`, it just adds a pointer word.
    /// If `size` isn't known until runtime, it uses RTTI splicing.
    fn or_box(
        &self,
        size: IntValue<'cxt>,
        info: &mut TyInfo<'cxt>,
        unbox: impl FnOnce(&mut TyInfo<'cxt>),
    ) {
        // If it's bigger than UNBOX_THRESHOLD, skip it
        let too_big = self.builder.build_int_compare(
            IntPredicate::UGT,
            size,
            self.size_ty().const_int(UNBOX_THRESHOLD.into(), false),
            "too_big",
        );
        match too_big.get_zero_extended_constant() {
            Some(0) => unbox(info),
            Some(1) => info.word(true),
            _ => {
                let mut info_unbox = TyInfo::new();
                unbox(&mut info_unbox);

                let mut info_box = TyInfo::new();
                info_box.word(true);

                let ptr = self
                    .if_expr(
                        too_big,
                        || {
                            info_box
                                .codegen(self.size_ty().const_int(8, false), self)
                                .as_basic_value_enum()
                        },
                        || info_unbox.codegen(size, self).as_basic_value_enum(),
                    )
                    .into_pointer_value();

                let rtti_ptr = unsafe {
                    self.builder.build_in_bounds_gep(
                        ptr,
                        &[self.size_ty().const_int(2, false)],
                        "rtti_ptr",
                    )
                };

                info.splice(rtti_ptr);
            }
        }
    }
}

enum TyInfoPart<'cxt> {
    Constant(Vec<u32>),
    Entry(IntValue<'cxt>, bool),
    Splice(PointerValue<'cxt>, bool),
}
impl<'cxt> TyInfoPart<'cxt> {
    fn extend(&mut self) {
        match self {
            TyInfoPart::Constant(v) => {
                // Mark the last entry as continued
                v.last_mut().map(|x| *x |= 1);
            }
            TyInfoPart::Entry(_, b) | TyInfoPart::Splice(_, b) => *b = true,
        }
    }
}

enum LastType {
    Normal,
    VariantNext,
    VariantEnd((usize, usize)),
}

// Type information is structured as a 16-bit size of the type in bytes, 16-bit size of the type info in bytes, then a number of 32-bit *entries*, one after another.
// They can be one of 3 (4 including arrays to add later) types:
//
// 0..0 0..0 00 0
// ---- ---- -- - whether there's another struct member after this
// |    |    |
// |    |    00 is the type for a bitset of up to 24 words
// |    5-bit number of words in this bitset
// 24-bit bitset
//
// 0..0 0..0 0..0 000 01 0
// ---- ---- ---- --- -- - whether there's another struct member after this
// |    |    |    |   |
// |    |    |    |   01 is the type for a case split
// |    |    |    3-bit size of the tag in bytes (up to 8)
// |    |    3-bit offset of the tag in bytes from the end of the last entry
// |    11-bit number of variants
// 12-bit size of the variant in words, including the tag
//
// 0....0 0 10 0
// ------ - -- - whether there's another struct member after this
// |      | |
// |      | 10 is the type for a run-length encoding
// |      whether the words in this run are pointers
// 28-bit size of the run in words
struct TyInfo<'cxt> {
    run_words: Vec<bool>,
    variant_stack: Vec<(usize, usize)>,
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
            LastType::VariantEnd((i, j)) => match &mut self.entries[i] {
                TyInfoPart::Constant(v) => v[j] |= 1,
                TyInfoPart::Entry(_, b) => *b = true,
                _ => unreachable!(),
            },
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
impl<'cxt> Cxt<'cxt> {
    fn const_u32_arr(&self, arr: &[u32], name: &str) -> PointerValue<'cxt> {
        // Include a 64-bit fake header
        let arr: Vec<_> = [0, 0]
            .iter()
            .chain(arr.iter())
            .map(|&x| self.cxt.i32_type().const_int(x as u64, false))
            .collect();
        let arr = self.cxt.i32_type().const_array(&arr);
        let global = self.module.add_global(arr.get_type(), None, name);
        global.set_unnamed_addr(true);
        global.set_constant(true);
        global.set_alignment(8);
        global.set_initializer(&arr);
        self.builder.build_address_space_cast(
            global.as_pointer_value(),
            self.cxt.i32_type().gc_ptr(),
            "const_arr_ptr",
        )
    }
}
impl<'cxt> TyInfo<'cxt> {
    fn splice(&mut self, ty: PointerValue<'cxt>) {
        self.finish_bitset();

        self.extend();
        self.entries.push(TyInfoPart::Splice(ty, false));
    }

    fn start_variant(
        &mut self,
        num: usize,
        tag_size: u32,
        total_size: IntValue<'cxt>,
        cxt: &Cxt<'cxt>,
    ) {
        if let Some(total_size) = total_size.get_zero_extended_constant() {
            let offset = self.extra_bytes & 7;
            self.extra_bytes -= offset;
            self.finish_bitset();

            let num: u16 = num.try_into().expect("Too many variants");
            assert!(tag_size <= 8, "tag must be <= 8 bytes, got {}", tag_size);
            assert!(
                total_size < 4096,
                "Total size must be less than 4096, got {}",
                total_size
            );
            assert!(
                num < 2048,
                "Number of variants must be less than 2048, got {}",
                num
            );
            let entry = total_size as u32;
            let entry = (entry << 11) | num as u32;
            let entry = (entry << 3) | offset;
            let entry = (entry << 3) | (tag_size - 1);
            let entry = (entry << 3) | 0b01_0;
            self.entry(entry);

            self.variant_stack.push((
                self.entries.len() - 1,
                match self.entries.last().unwrap() {
                    TyInfoPart::Constant(v) => v.len() - 1,
                    _ => unreachable!(),
                },
            ));
        } else {
            let offset = self.extra_bytes & 7;
            self.extra_bytes -= offset;
            self.finish_bitset();

            let num: u16 = num.try_into().expect("Too many variants");
            assert!(tag_size <= 8, "tag must be <= 8 bytes, got {}", tag_size);
            assert!(
                num < 2048,
                "Number of variants must be less than 2048, got {}",
                num
            );
            let entry = num as u32;
            let entry = (entry << 3) | offset;
            let entry = (entry << 3) | (tag_size - 1);
            let entry = (entry << 3) | 0b01_0;
            let total_size =
                cxt.builder
                    .build_int_truncate(total_size, cxt.cxt.i32_type(), "size_i32");
            let total_size = cxt.builder.build_left_shift(
                total_size,
                cxt.cxt.i32_type().const_int(20, false),
                "size_shl",
            );
            let entry = cxt.builder.build_or(
                total_size,
                cxt.cxt.i32_type().const_int(entry as u64, false),
                "variant_start_entry",
            );
            self.extend();
            self.entries.push(TyInfoPart::Entry(entry, false));

            self.variant_stack.push((self.entries.len() - 1, 0));
        }
    }

    fn next_variant(&mut self) {
        self.finish_bitset();
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

    pub fn codegen(mut self, ty_size: IntValue<'cxt>, cxt: &Cxt<'cxt>) -> PointerValue<'cxt> {
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

        // Don't allocate if it's constant
        if self.entries.len() == 1 {
            if let TyInfoPart::Constant(v) = &self.entries[0] {
                let rtti_size = v.len() * 4;
                let rtti_size = cxt
                    .cxt
                    .i32_type()
                    .const_int((rtti_size << 16) as u64, false);
                let sizes = cxt.builder.build_or(rtti_size, ty_size, "rtti_sizes");

                // We need a 64-bit fake header
                let values: Vec<_> = [0u32, 0]
                    .iter()
                    .map(|&x| cxt.cxt.i32_type().const_int(x as u64, false))
                    .chain(std::iter::once(sizes))
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

                return cxt.builder.build_address_space_cast(
                    global.as_pointer_value(),
                    cxt.cxt.i32_type().gc_ptr(),
                    "const_rtti_ptr",
                );
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
                TyInfoPart::Entry(_, _) => {
                    let esize = cxt.size_ty().const_int(1, false);
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
        let alloc_size =
            cxt.builder
                .build_int_add(size, cxt.size_ty().const_int(4, false), "alloc_size");

        let rtti_rtti = if let Some(size) = size.get_zero_extended_constant() {
            // The size of the RTTI RTTI is 0, since it doesn't include space for the size itself
            cxt.const_u32_arr(&[size as u32], "rtti_const_rtti")
        } else {
            let just_size_rtti = cxt.const_u32_arr(&[4], "just_size_rtti");

            let alloc = cxt.alloc(
                cxt.cxt.i64_type().const_int(4, false),
                just_size_rtti,
                "rtti_rtti",
            );
            let alloc_i32 = cxt
                .builder
                .build_bitcast(alloc, cxt.cxt.i32_type().gc_ptr(), "rtti_size_alloc")
                .into_pointer_value();
            // Store after the header
            let slot = unsafe {
                cxt.builder.build_in_bounds_gep(
                    alloc_i32,
                    &[cxt.cxt.i32_type().const_int(2, false)],
                    "rtti_size_slot",
                )
            };
            let size =
                cxt.builder
                    .build_int_truncate(alloc_size, cxt.cxt.i32_type(), "alloc_size_i32");
            cxt.builder.build_store(slot, size);
            alloc_i32
        };
        let alloc = cxt.alloc(alloc_size, rtti_rtti, "rtti_slot");
        let slot = cxt
            .builder
            .build_bitcast(alloc, cxt.cxt.i32_type().gc_ptr(), "rtti_slot_i32")
            .into_pointer_value();
        // Skip the header
        let mut slot = unsafe {
            cxt.builder.build_in_bounds_gep(
                slot,
                &[cxt.cxt.i32_type().const_int(2, false)],
                "rtti_size_slot",
            )
        };

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
                        .build_bitcast(slot, arr.get_type().gc_ptr(), "const_rtti_slot")
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
                TyInfoPart::Entry(entry, b) => {
                    let entry = if *b {
                        cxt.builder.build_or(
                            *entry,
                            cxt.cxt.i32_type().const_int(1, false),
                            "rtti_entry_extend",
                        )
                    } else {
                        *entry
                    };
                    cxt.builder.build_store(slot, entry);

                    slot = unsafe {
                        cxt.builder.build_in_bounds_gep(
                            slot,
                            &[cxt.cxt.i32_type().const_int(1, false)],
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
                        cxt.size_ty().const_int(4, false),
                        "spliced_rtti_size_i32s",
                    );

                    if *b {
                        // Mark the last entry that it's continued
                        let last_idx = cxt.builder.build_int_sub(
                            size_i32s,
                            cxt.cxt.i64_type().const_int(1, false),
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
            .build_bitcast(alloc, cxt.cxt.i32_type().gc_ptr(), "rtti_slot_i32")
            .into_pointer_value()
    }
}

impl<'cxt> Cxt<'cxt> {
    pub fn any_ty(&self) -> BasicTypeEnum<'cxt> {
        self.cxt.i8_type().gc_ptr().as_basic_type_enum()
    }

    pub fn size_ty(&self) -> IntType<'cxt> {
        self.cxt
            .ptr_sized_int_type(&self.machine.get_target_data(), None)
    }

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

    pub fn as_type(&self, val: Val, data: &Data) -> Type<'cxt> {
        match data.slots.node(val).unwrap() {
            Node::Unbox(inner) => Type::Unbox(Box::new(self.as_type(*inner, data))),
            Node::FunType(i) => Type::Closure(*i),
            Node::ExternFunType(args, ret) => {
                let args = args
                    .iter()
                    .map(|&x| self.as_type(x, data).llvm_ty(self))
                    .collect();
                let ret = self.as_type(*ret, data).llvm_ty(self);
                Type::ExternFun(args, ret)
            }
            Node::ProdType(v) => {
                let v: Vec<_> = v.iter().map(|&x| self.as_type(x, data)).collect();

                // It's a StackStruct if the part we would put on the stack is smaller than STACK_THRESHOLD bytes
                let mut is_static = true;
                let mut static_size = 0;
                for i in &v {
                    // If it has a pointer, it needs to be heap-allocated, because LLVM can't see pointers inside of structs for GC purposes
                    if i.has_ptr() {
                        is_static = false;
                        break;
                    }
                    let align = i.alignment();
                    if align > 0 {
                        static_size += padding(static_size, align);
                    }
                    static_size += i.stack_size().unwrap_or(0);
                }
                if is_static && static_size <= STACK_THRESHOLD {
                    Type::StackStruct(v)
                } else {
                    Type::PtrStruct(v)
                }
            }
            Node::SumType(v) => {
                if v.len() == 1 {
                    return self.as_type(v[0], data);
                }

                let v: Vec<_> = v.iter().map(|&x| self.as_type(x, data)).collect();

                // It's a StackEnum if it's statically sized, and smaller than STACK_THRESHOLD bytes
                let mut is_static = true;
                let mut payload = 0;
                let mut align = 0;
                for i in &v {
                    // If it has a pointer, it needs to be heap-allocated, because LLVM can't see pointers inside of structs for GC purposes
                    if i.has_ptr() {
                        is_static = false;
                        break;
                    }
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
                // For now, LLVM doesn't support returning arrays of more than 3 elements in GC'd functions
                // TODO pass an output pointer like C compilers do for structs
                if is_static && size < 4 {
                    Type::StackEnum(size, v)
                } else {
                    Type::PtrEnum(v)
                }
            }
            Node::RefTy(_) => Type::Pointer,
            Node::Const(c) => match *c {
                Constant::TypeType => Type::Type,
                Constant::IntType(w) => Type::Int(w.bits()),
                Constant::FloatType(t) => Type::Float(t),
                Constant::StringTy | Constant::BoxTy => Type::Pointer,
                Constant::Int(_, _)
                | Constant::Float(_)
                | Constant::Stop
                | Constant::String(_)
                | Constant::Unreachable => {
                    panic!("not a type")
                }
            },

            Node::Param(_, _) | Node::Proj(_, _, _) => match self.try_gen_value(val, data) {
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
            | Node::BinOp(_, _, _, _) => panic!("not a type"),
        }
    }
}
