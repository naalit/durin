#ifndef __RUNTIME_IMMIX_H__
#define __RUNTIME_IMMIX_H__

#define EVACUATE
// #define GENERATIONAL
// #define INCREMENTAL
// #define REPORT_PAUSES

#define BLOCK_SIZE 32768
#define LINE_SIZE 128
#define LINES_PER_BLOCK BLOCK_SIZE / LINE_SIZE

typedef struct BlockMetadata {
    bool available;
    bool empty;
    void* start;
    uint64_t line_mark[LINES_PER_BLOCK / 64];
} BlockMetadata;
static BlockMetadata* all_blocks;
static uint32_t num_blocks;

static bool heap_contains(void* ptr) {
    void* start = all_blocks[0].start;
    void* end = start + num_blocks * BLOCK_SIZE;
    return ptr >= start && ptr < end;
}

static void run_gc(uint64_t* rsp, uint64_t* rbp);

static void reset_line_marks();

#ifdef EVACUATE
static void try_reserve_evac_block();
#endif

// -- External API -- //

_Thread_local struct {
    // The start of the block that the local allocator is currently using
    void* block;
    // The low end of the open space
    void* end;
    // The high end of the open space, which is decremented to allocate
    // Invariant: block <= end <= ptr
    void* ptr;
} local_alloc;

// `size` should include a word for the header
void* immix_alloc(uint64_t size, uint32_t* header, uint64_t* rsp, uint64_t* rbp);

void initialize(uint32_t num_start_blocks);

void finalize();

#endif
