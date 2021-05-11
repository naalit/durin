// Immix collector - tracing functionality
//
// It uses a four-color incremental algorithm:
// All objects start out white. When the GC sees a white pointer, first it "marks" it, turns it gray and adds it to the "gray stack".
// When marking, it may move the object and leave a forwarding pointer in the header, with the third-to-last bit set.
// It will also set the line marks for each line the object is on.
// Then, later, the GC pops it off the gray stack and "traces" it, turning it black and marking all pointers inside of it.
// There's a fourth color, "off-white", which is treated the same as white but can be swapped with black to trigger a major GC - no objects will be black anymore.
//
// It's not currently actually run incrementally, just generationally. To run it incrementally, the code generator needs a write barrier which,
// when writing a white object reference to a black object, sets the black object to gray and adds it to the gray stack.
//
// Object headers are 64 bits:
// 0..0 0 00
// ---- - -- color
// |    |
// |    set to 1 if it's been relocated
// 61-bit word-aligned type information pointer
//
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
// 0..0 0..0 000 01 0
// ---- ---- --- -- - whether there's another struct member after this
// |    |    |   |
// |    |    |   01 is the type for a case split
// |    |    3-bit size of the tag in bytes (up to 8)
// |    10-bit offset of the tag in bytes from the end of the last entry
// 16-bit number of variants
//
// 0....0 0 10 0
// ------ - -- - whether there's another struct member after this
// |      | |
// |      | 10 is the type for a run-length encoding
// |      whether the words in this run are pointers
// 28-bit size of the run in words

#include "common.h"
#include "immix.h"
#include <string.h>

static const uint64_t COLOR_MASK = 0b11;
static const uint64_t COLOR_WHITE = 0;
static const uint64_t COLOR_GRAY = 1;

static uint64_t current_black = 0b10;
static uint64_t current_off_white = 0b11;
static void swap_black() {
    current_black ^= 1;
    current_off_white ^= 1;
}

static void trace(uint32_t* rtti, uint64_t* object);

#ifdef EVACUATE
static const uint64_t RELOC_MASK = 0b100;

static bool can_evacuate = false;
static uint32_t evac_block_idx;
static void* evac_heap_ptr;
static void* evac_heap_end;

static bool evacuate(uint64_t** object_ptr, uint64_t size) {
    if (!can_evacuate)
        return false;

    // Allocate space
    void* new_heap_ptr = evac_heap_ptr + size;
    if (new_heap_ptr > evac_heap_end) {
        can_evacuate = false;
        return false;
    }
    void* to = evac_heap_ptr;
    evac_heap_ptr = new_heap_ptr;

    // Pointer to the header
    uint64_t* from = *object_ptr - 1;

    memcpy(to, from, size);

    if ((uint64_t)to & 0b111)
        panic("Evacuation target pointer isn't word-aligned!");

    // Set the relocation bit in the old object header, and set the rest to the pointer to the new object
    *from = ((uint64_t)to + 8) | RELOC_MASK;
    *object_ptr = (uint64_t*)(to + 8);

    return true;
}

static void try_reserve_evac_block() {
    if (can_evacuate) {
        // If we're already using a block, and we haven't finished it, make sure the mutator doesn't use it
        all_blocks[evac_block_idx].available = false;
    } else {
        // Try to find an empty block to evacuate into
        for (uint32_t i = 0; i < num_blocks; i++) {
            if (all_blocks[i].available && all_blocks[i].empty) {
                all_blocks[i].available = false;
                evac_block_idx = i;
                evac_heap_ptr = all_blocks[i].start;
                evac_heap_end = evac_heap_ptr + BLOCK_SIZE;
                can_evacuate = true;
                return;
            }
        }
    }
}
#endif

#ifdef INCREMENTAL
static uint64_t** gray_stack = NULL;
static uint64_t gray_stack_len = 0;
static uint64_t gray_stack_cap = 0;
static void gray_stack_push(uint64_t* ptr) {
    if (gray_stack_len >= gray_stack_cap) {
        // Reallocate
        gray_stack_cap = gray_stack_cap > 0 ? gray_stack_cap * 2 : 16;
        gray_stack = (uint64_t**) realloc(gray_stack, gray_stack_cap * sizeof(uint64_t*));
    }
    gray_stack[gray_stack_len++] = ptr;
}

static void trace_gray_stack() {
    for (int i = 0; i < gray_stack_len; i++) {
        uint64_t* ptr = gray_stack[i];
        uint64_t header = *(ptr - 1);
        uint64_t rtti_pointer = header >> 13 << 3;
        trace((uint32_t*)rtti_pointer, ptr);
    }
    gray_stack_len = 0;
}
#endif

static void mark(uint64_t** ptr, uint64_t** derived) {
    // If the last bit is set, it means it's not actually a pointer
    // All real pointers are aligned to at least 2 bytes
    if ((uint64_t)*ptr & 0b111) {
        panic("Unaligned pointer %lx!", (uint64_t)*ptr);
        return;
    }

    if (!heap_contains(*ptr)) {
        // It's probably a pointer to the stack or data section
        return;
    }

    uint64_t header = *(*ptr - 1);
    #ifdef EVACUATE
    if (header & RELOC_MASK) {
        // printf("Relocated %lx to %lx\n", *ptr, header & ~RELOC_MASK);
        if (derived && derived != ptr) {
            uint64_t offset = (uint64_t)(*derived) - (uint64_t)(*ptr);
            *ptr = (uint64_t*) (header & ~RELOC_MASK);
            *(uint64_t*)derived = (uint64_t)*ptr + offset;
        } else {
            *ptr = (uint64_t*) (header & ~RELOC_MASK);
        }
        // If it's been reallocated, we know it's already been marked
        return;
    }
    #endif

    uint64_t color = header & COLOR_MASK;
    // If it's gray or black, we've already marked it so we don't need to do it again
    if (color == COLOR_WHITE || color == current_off_white) {
        uint32_t* rtti = (uint32_t*)(header & ~COLOR_MASK);
        uint32_t size = *rtti & ((1 << 16) - 1);

        void* block = all_blocks[0].start + ((void*)(*ptr - 1) - all_blocks[0].start) / BLOCK_SIZE * BLOCK_SIZE;
        uint32_t block_idx = (block - all_blocks[0].start) / BLOCK_SIZE;

        #ifdef EVACUATE
        uint64_t* before = *ptr;
        // Add the header word to the size
        if (block_idx != evac_block_idx && evacuate(ptr, size + 8)) {
            if (derived && derived != ptr) {
                uint64_t offset = (uint64_t)(*derived) - (uint64_t)before;
                *(uint64_t*)derived = (uint64_t)*ptr + offset;
            }
            block = all_blocks[0].start + ((void*)(*ptr - 1) - all_blocks[0].start) / BLOCK_SIZE * BLOCK_SIZE;
            block_idx = (block - all_blocks[0].start) / BLOCK_SIZE;
        }
        assert(*(*ptr - 1) == header);
        #endif

        uint64_t* iptr = *ptr;

        // Mark gray
        iptr[-1] = (header & ~COLOR_MASK) | COLOR_GRAY;

        // Mark each line it covers
        uint32_t line_idx = ((void*)(iptr - 1) - block) / LINE_SIZE;
        // size doesn't include the header, so calc the offset from iptr instead of (iptr - 1)
        void* end_ptr = (void*)iptr + size;
        // The `end` argument of `bitset_set_range` is exclusive, so +1
        uint32_t line_end = (end_ptr - block) / LINE_SIZE + 1;
        bitset_set_range(all_blocks[block_idx].line_mark, line_idx, line_end);

        // If there aren't any pointers, the first entry will be 0 and we can skip tracing
        // This is mostly useful in incremental mode, since we don't need to add it to the gray stack
        if (rtti[1]) {
            #ifdef INCREMENTAL
            // Add to gray stack to be traced later
            gray_stack_push(iptr);
            #else
            // Trace now, starting at the first entry, not the size
            trace(rtti + 1, iptr);
            #endif
        } else {
            // Mark black right away, don't trace
            iptr[-1] = (header & ~COLOR_MASK) | current_black;
        }

        // Mark the type info
        uint64_t* rtti2 = (uint64_t*)rtti;
        mark(&rtti2, NULL);
        if ((void*)rtti != (void*)rtti2) {
            // The type info got moved, so update the header
            color = iptr[-1] & COLOR_MASK;
            iptr[-1] = (uint64_t)rtti2 | color;
        }
    }
}

// Tracing with type information

// Advances `rtti` through one set of entries, without doing anything.
// Used for variants that aren't present.
static void rtti_skip(uint32_t** rtti) {
    while (true) {
        uint32_t entry = *(*rtti)++;
        if ((entry & 0b110) == 0b010) {
            // Case split
            uint32_t variants = entry >> 16;
            for (int i = 0; i < variants; i++) {
                rtti_skip(rtti);
            }
        }
        if (entry & 1) {
            continue;
        } else {
            break;
        }
    }
}

// Advances `rtti` through one set of entries, also advancing `object` and marking any pointers.
static void rtti_go(uint32_t** rtti, uint64_t** object) {
    while(true) {
        uint32_t entry = *(*rtti)++;
        uint32_t type = (entry & 0b110) >> 1;
        switch (type) {
        case 0b00: {
            // Bitset
            uint32_t size = (entry >> 3) & 0b11111;
            uint32_t bitset = entry >> 8;
            
            for (int word = 0; word < size; word++, *object += 1) {
                if (bitset & (1 << word)) {
                    mark((uint64_t**)*object, NULL);
                }
            }
            break;
        }
        case 0b01: {
            // Case split
            uint32_t tag_bytes = ((entry >> 3) & 0b111) + 1;
            uint32_t offset = (entry >> 6) & ((1 << 10) - 1);
            uint32_t variants = entry >> 16;

            uint32_t offset_words = offset / 8;
            uint32_t offset_bytes = offset % 8;
            *object += offset_words;
            // Only works on little-endian systems
            // Example:
            // Offset 1, size 2
            // little-endian bytes
            //      AAAA BBBB CCCC DDDD
            //           ---------
            // to uint64_t
            //      DDDDCCCCBBBBAAAA
            // offset 1 -->
            //      0000DDDDCCCCBBBB
            // size 2       --------
            //      00000000CCCCBBBB
            uint64_t mask = (1UL << (tag_bytes * 8)) - 1;
            uint64_t tag = (**object >> (offset_bytes * 8)) & mask;
            
            if (tag >= variants) {
                panic("tag %lu in word %lu out of range, expected one of %u variants\n", tag, **object, variants);
            }
            *object += 1;

            for (int v = 0; v < variants; v++) {
                if (v == tag)
                    rtti_go(rtti, object);
                else
                    rtti_skip(rtti);
            }

            break;
        }
        case 0b10: {
            // RLE
            bool pointer = (entry & 0b1000) != 0;
            uint32_t size = entry >> 4;
            
            for (int word = 0; word < size; word++, *object += 1) {
                if (pointer) {
                    mark((uint64_t**)*object, NULL);
                }
            }
            break;
        }
        default:
            panic("Not supported: type %u\n", type);
        }
        if (entry & 1)
            continue;
        else
            break;
    }
}

static void trace(uint32_t* rtti, uint64_t* object) {
    // Mark all pointers in the object and then set it black
    uint64_t* iptr = object;
    // printf("Tracing object\n");
    rtti_go(&rtti, &object);
    iptr[-1] = (iptr[-1] & ~COLOR_MASK) | current_black;
}

static void mark_stack(uint64_t* rsp) {
    while (true) {
        uint64_t ret_address = *rsp;
        rsp++;
        StackEntry* entry = stack_table_lookup(ret_address);
        if (entry == NULL) {
            break;
        }
        // printf("Walking stack frame\n");

        if (entry->num_locations) {
            Location* end = entry->locations + entry->num_locations;
            for (Location* loc = entry->locations; loc < end; loc++) {
                mark((uint64_t**)rsp + loc->base_offset/8, (uint64_t**)rsp + loc->derived_offset/8);
            }
        }

        rsp += entry->stack_size / 8;
    }
}

static void reset_line_marks() {
    for (int i = 0; i < num_blocks; i++) {
        memset(all_blocks[i].line_mark, 0, 8 * LINES_PER_BLOCK / 64);
    }
}

#ifdef REPORT_PAUSES
static const uint32_t PAUSE_CAP = 128;
static clock_t pauses[PAUSE_CAP];
static uint32_t pause_cursor = 0;
#endif

static uint64_t open_lines;
static uint64_t full_lines;

static void run_full_gc(uint64_t* rsp, bool major) {
    #ifdef REPORT_PAUSES
    clock_t before = clock();
    #endif

    local_alloc.block = NULL;
    local_alloc.end = NULL;
    local_alloc.ptr = NULL;

    if (major) {
        reset_line_marks();
        swap_black();
    }

    mark_stack(rsp);
    for (uint32_t i = 0; i < extra_roots.len; i++) {
        uint64_t* root = extra_roots.roots[i];
        mark(&root, NULL);
        extra_roots.roots[i] = root;
    }

    #ifdef INCREMENTAL
    trace_gray_stack();
    #endif

    uint64_t null_bytes[LINES_PER_BLOCK / 64];
    uint64_t filled_bytes[LINES_PER_BLOCK / 64];
    for (int i = 0; i < LINES_PER_BLOCK / 64; i++) {
        null_bytes[i] = 0;
        filled_bytes[i] = ~0UL;
    }

    full_lines = 0;
    uint32_t open_blocks = 0;
    uint32_t partial_blocks = 0;
    
    for (int i = 0; i < num_blocks; i++) {
        for (int b = 0; b < LINES_PER_BLOCK / 64; b++) {
            full_lines += __builtin_popcountl(all_blocks[i].line_mark[b]);
        }

        if (!memcmp(all_blocks[i].line_mark, null_bytes, 8 * LINES_PER_BLOCK / 64)) {
            all_blocks[i].available = true;
            all_blocks[i].empty = true;
            open_blocks += 1;
        } else if (memcmp(all_blocks[i].line_mark, filled_bytes, 8 * LINES_PER_BLOCK / 64)) {
            all_blocks[i].available = true;
            all_blocks[i].empty = false;
            partial_blocks += 1;
        } else {
            all_blocks[i].available = false;
            all_blocks[i].empty = false;
        }
    }
    open_lines = num_blocks * LINES_PER_BLOCK - full_lines;

    // printf("%s GC finished, %lu full lines, %lu open lines\n", major ? "Major" : "Minor", full_lines, open_lines);

    if (open_lines == 0)
        panic("Out of space!\n");

    #ifdef EVACUATE
    if (can_evacuate || (open_blocks > 0 && (open_blocks > 1 || partial_blocks > 0)))
        try_reserve_evac_block();
    #endif

    #ifdef REPORT_PAUSES
    clock_t after = clock();
    if (pause_cursor < PAUSE_CAP) {
        pauses[pause_cursor++] = after - before;
    }
    #endif
}

static void run_gc(uint64_t* rsp) {
    #ifdef GENERATIONAL
    run_full_gc(rsp, full_lines > open_lines);
    #else
    run_full_gc(rsp, true);
    #endif
}

void finalize() {
    #ifdef REPORT_PAUSES
    printf("%u pauses:\n", pause_cursor);
    for (uint32_t i = 0; i < pause_cursor; i++) {
        printf("\t%f ms\n", (double)pauses[i] / 1000.0);
    }
    #endif
}
