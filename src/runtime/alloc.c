// Immix block allocator
#include "common.h"
#include "immix.h"

void initialize(uint32_t num_start_blocks) {
    if (BLOCK_SIZE % LINE_SIZE)
        panic("Block size must be a multiple of line size, got block=%u and line=%u\n", BLOCK_SIZE, LINE_SIZE);
    if ((BLOCK_SIZE / LINE_SIZE) % 64)
        panic("Must be a multiple of 64 lines per block, got block=%u and line=%u\n", BLOCK_SIZE, LINE_SIZE);

    gen_stack_table();

    num_blocks = num_start_blocks;
    all_blocks = malloc(num_start_blocks * sizeof(BlockMetadata));
    // Put all blocks in one huge malloc
    void* block_start = malloc(num_start_blocks * BLOCK_SIZE);
    for (int i = 0; i < num_start_blocks; i++) {
        all_blocks[i].available = true;
        all_blocks[i].empty = true;
        all_blocks[i].start = block_start;
        block_start += BLOCK_SIZE;
    }

    reset_line_marks();

    #ifdef EVACUATE
    if (num_start_blocks > 1)
        try_reserve_evac_block();
    #endif
}

/// Moves to the next open line, starting at `local_alloc.end`.
/// Returns true if it found one, false if it exhausted the current block.
static bool next_line() {
    if (!local_alloc.block)
        return false;

    // Search for an open line
    uint32_t block_idx = (local_alloc.block - all_blocks[0].start) / BLOCK_SIZE;
    void* block_ptr = local_alloc.block;
    // next_ptr points to the low end of an occupied line
    void* next_ptr = local_alloc.end;
    // line_idx points to the line below next_ptr - `next_ptr` is the end of line `line_idx`
    uint32_t line_idx = (next_ptr - block_ptr) / LINE_SIZE - 1;
    uint64_t* lines = all_blocks[block_idx].line_mark;
    bool found = false;
    // If `next_ptr == block_ptr`, then we're past the end of the block
    while (next_ptr > block_ptr) {
        if (!bitset_get(lines, line_idx)) {
            if (!found) {
                found = true;
                local_alloc.ptr = next_ptr;
            }
            // Zero-initialize the line to make sure the GC never sees old data if it runs before stores to the region
            memset(next_ptr-LINE_SIZE, 0, LINE_SIZE);
        } else if (found) {
            local_alloc.end = next_ptr;
            return true;
        }
        next_ptr -= LINE_SIZE;
        line_idx--;
    }
    if (found) {
        local_alloc.end = block_ptr;
        return true;
    } else {
        return false;
    }
}

/// Moves to the next block with open lines, and moves to the first open line.
/// Prioritizes recycling nonempty blocks over allocating into empty ones.
/// Returns true if it found one, false if there are no more blocks with open lines.
static bool next_block() {
    // Search for an open block
    uint32_t block_idx;
    bool empty;
    if (local_alloc.block) {
        block_idx = (local_alloc.block - all_blocks[0].start) / BLOCK_SIZE;
        empty = all_blocks[block_idx].empty;
    } else {
        block_idx = -1;
        empty = false;
    }
    if (!empty) {
        // Try to recycle a block first
        // printf("Attempting to recycle block starting at block %u\n", block_idx);
        while (++block_idx < num_blocks) {
            BlockMetadata block = all_blocks[block_idx];
            if (block.available && !block.empty) {
                local_alloc.block = block.start;
                local_alloc.ptr = local_alloc.end = block.start + BLOCK_SIZE;
                all_blocks[block_idx].available = false;
                if (next_line()) {
                    return true;
                } else {
                    // This block doesn't have open lines
                    // printf("Skipping full block %u\n", block_idx);
                    continue;
                }
            }
            // printf("Skipping block %u\n", block_idx);
        }
        // We couldn't find a block to recycle, so find an empty block starting at the top
        block_idx = -1;
    }
    // Try to find an empty block
    // printf("Attempting to find empty block starting at block %u\n", block_idx);
    while (++block_idx < num_blocks) {
        BlockMetadata block = all_blocks[block_idx];
        if (block.available && block.empty) {
            // If it's empty, don't bother calling next_line(), just use the whole block
            local_alloc.block = local_alloc.end = block.start;
            local_alloc.ptr = block.start + BLOCK_SIZE;
            all_blocks[block_idx].available = false;
            return true;
        }
        // printf("Skipping block %u\n", block_idx);
    }
    // We couldn't find anything
    return false;
}

// `size` should include a word for the header
void* immix_alloc(uint64_t size, uint32_t* header, uint64_t* rsp, uint64_t* rbp) {
    // printf("Calling immix_alloc of %ld bytes\n", size);
    while (true) {
        // Try this line
        if (local_alloc.ptr && local_alloc.ptr - size >= local_alloc.end) {
            void* next_ptr = local_alloc.ptr - size;
            *(uint32_t**)next_ptr = header;
            local_alloc.ptr = next_ptr;
            if ((uint64_t)next_ptr & 1)
                panic("Unaligned pointer in immix_alloc()");
            return next_ptr;
        // Try this block
        } else if (next_line()) {
            continue;
        // Request a new block
        } else if (next_block()) {
            continue;
        } else {
            // There's no more free space, run the GC!
            // But make sure it can see the RTTI pointer is live
            push_extra_root(header);

            run_gc(rsp, rbp);

            header = pop_extra_root();

            continue;
        }
    }
}

