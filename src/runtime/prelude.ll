target datalayout = "ni:1"

; _Thread_local struct {
;     uint8_t* block;
;     uint8_t* end;
;     uint8_t* ptr;
; } local_alloc;
%struct_alloc = type { i8*, i8*, i8* }
@local_alloc = external thread_local global %struct_alloc, align 8

; `%size` should include a word for the header
declare void @initialize(i32 %num_start_blocks)
declare void @finalize()

module asm ".globl __LLVM_StackMaps"

declare i8* @llvm.addressofreturnaddress()
declare i8 addrspace(1)* @immix_alloc(i64 %size, i32 addrspace(1)* %header, i8* %rsp)
define private i8 addrspace(1)* @gc_alloc_slow(i64 %size, i32 addrspace(1)* %header) noinline cold {
    %rsp = call i8* @llvm.addressofreturnaddress()
    %alloc = call i8 addrspace(1)* @immix_alloc(i64 %size, i32 addrspace(1)* %header, i8* %rsp)
    ret i8 addrspace(1)* %alloc
}

define private fastcc i8 addrspace(1)* @to_gc_pointer(i8* %x) noinline {
    %y = addrspacecast i8* %x to i8 addrspace(1)*
    ret i8 addrspace(1)* %y
}

; The returned pointer points to the header of the object; the actual object starts one word later
define private fastcc i8 addrspace(1)* @gc_alloc(i64 %size1, i32 addrspace(1)* %header) gc "statepoint-example" {
    ; Add 1-word header
    %size2 = add i64 %size1, 8
    ; Round up to multiple of 8: (size + 7) & ~7
    ; size + 7 >= next multiple of 8 only if size isn't a multiple of eight
    ; Then we cut off the remainder to get the multiple of 8
    %size3 = add i64 %size2, 7
    ; ~7 = -8 in 2's complement
    %size = and i64 %size3, -8
    ; -size, so we can use getelementptr to bump downwards
    %nsize = mul i64 %size, -1

    %heapPtr = getelementptr inbounds %struct_alloc, %struct_alloc* @local_alloc, i64 0, i32 2
    %heapEnd = getelementptr inbounds %struct_alloc, %struct_alloc* @local_alloc, i64 0, i32 1

    %ptr = load i8*, i8** %heapPtr, align 8
    %next = getelementptr inbounds i8, i8* %ptr, i64 %nsize
    %end = load i8*, i8** %heapEnd, align 8
    %cond = icmp slt i8* %next, %end
    br i1 %cond, label %slow, label %fast

slow:
    %r = call i8 addrspace(1)* @gc_alloc_slow(i64 %size, i32 addrspace(1)* %header)
    ret i8 addrspace(1)* %r

fast:
    store i8* %next, i8** %heapPtr, align 8

    %next.rtti = bitcast i8* %next to i32 addrspace(1)**
    store i32 addrspace(1)* %header, i32 addrspace(1)** %next.rtti, align 8

    %alloc = call fastcc i8 addrspace(1)* @to_gc_pointer(i8* %next)

    ret i8 addrspace(1)* %alloc
}

; "%d\n"
@istr = private unnamed_addr constant [4 x i8] c"%d\0a\00", align 1
declare i32 @printf(i8*, ...)

define private {} @print_i32(i32 %a) {
    %_0 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @istr, i32 0, i32 0), i32 %a)
    ret {} undef
}

; "%.*s"
@sstr = private unnamed_addr constant [5 x i8] c"%.*s\00", align 1
define private {} @print_str(i8 addrspace(1)* %str_) {
entry:
    ; Skip the header
    %str = getelementptr inbounds i8, i8 addrspace(1)* %str_, i32 8

    %as_i32 = bitcast i8 addrspace(1)* %str to i32 addrspace(1)*
    %size = load i32, i32 addrspace(1)* %as_i32
    %bytes = getelementptr inbounds i8, i8 addrspace(1)* %str, i32 4
    %q = addrspacecast i8 addrspace(1)* %bytes to i8*
    %_0 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @sstr, i32 0, i32 0), i32 %size, i8* %q)
    ret {} undef
}