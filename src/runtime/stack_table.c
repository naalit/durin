#include "common.h"

// This will link to the stack map section of the same name that LLVM generates in the object file
extern uint8_t __LLVM_StackMaps[];


// Each stack table entry represents a call site, and consists of a return address, a stack size, and a number of locations,
// each of which represents the position on the stack of a base and derived pointer.
// Stack table entries are split up into a number of buckets according to the last few bits of the return address.
// That way, we don't have to look through all the entries to look up a return address, just the entries in that bucket.
// When we're building the table, we don't know how many entries will be in each bucket, so they're not stored in order;
// instead, each entry has a "pointer" (an offset into the table) to the next entry in the bucket.

#define NUM_BUCKETS 32

typedef struct StackBucket {
    uint32_t first;
    uint32_t num_functions;
} StackBucket;

typedef struct Location {
    uint32_t base_offset;
    uint32_t derived_offset;
    uint32_t num_pointers;
} Location;

typedef struct StackEntry {
    uint64_t ret_address;
    uint64_t stack_size;
    Location* locations;
    uint32_t num_locations;
    uint32_t next;
} StackEntry;

static struct StackTable {
    StackBucket buckets[NUM_BUCKETS];
    uint64_t entries_len;
    StackEntry* entries;
} stack_table;

// To lookup an entry, we find the bucket, then follow the `next` pointers until we find an entry with a matching return address.
// Returns NULL if there's no entry for the provided return address.
static StackEntry* stack_table_lookup(uint64_t ret_address) {
    uint64_t hash = ret_address % NUM_BUCKETS;
    StackBucket bucket = stack_table.buckets[hash];
    uint32_t idx = bucket.first;

    for (uint32_t i = 0; i < bucket.num_functions; i++) {
        if (stack_table.entries[idx].ret_address == ret_address) {
            return &stack_table.entries[idx];
        } else {
            idx = stack_table.entries[idx].next;
        }
    }

    return NULL;
}

// We insert entries at the front of their buckets, so we just set the `next` pointer on the new entry to the old `first` entry, and set `first` to the new entry.
static void stack_table_insert(uint64_t ret_address, uint32_t entry) {
    uint64_t hash = ret_address % NUM_BUCKETS;
    StackBucket* bucket = &stack_table.buckets[hash];

    bucket->num_functions++;
    stack_table.entries[entry].next = bucket->first;
    bucket->first = entry;
}


// This function just follows the stack map format documented at https://llvm.org/docs/StackMaps.html#stackmap-format
// and https://www.llvm.org/docs/Statepoints.html#statepoint-stackmap-format.
static void gen_stack_table() {
    void* ptr = __LLVM_StackMaps;
    // This macro allows us to easily get a certain size value and then advance the pointer past it
    #define GET(t) *(t*)ptr; ptr += sizeof(t)
 
    uint8_t version = GET(uint8_t);
    if (version != 3) {
        printf("Warning: unsupported stackmap version: %u\n", version);
    }
    // Reserved
    GET(uint8_t);
    GET(uint16_t);

    uint32_t num_functions = GET(uint32_t);
    uint32_t num_constants = GET(uint32_t);
    uint32_t num_records = GET(uint32_t);

    // Allocate space for num_records entries in the stack table
    stack_table.entries = malloc(sizeof(StackEntry) * num_records);

    struct FunctionData {
        uint64_t address;
        uint64_t stack_size;
        uint64_t num_records;        
    }* funcs = malloc(sizeof(struct FunctionData) * num_functions);
    struct FunctionData* funcs_end = funcs + num_functions;
    for (struct FunctionData* f = funcs; f < funcs_end; f++) {
        f->address = GET(uint64_t);
        f->stack_size = GET(uint64_t);
        f->num_records = GET(uint64_t);
    }

    for (int i = 0; i < num_constants; i++) {
        uint64_t c = GET(uint64_t);
        printf("Warning: unidentified constant with value %lx\n", c);
    }

    uint32_t entry_num = 0;
    StackEntry* entry = stack_table.entries;

    // Entries are laid out per function
    for (struct FunctionData* f = funcs; f < funcs_end; f++) {
        for (int r = 0; r < f->num_records; r++) {
            uint64_t _id = GET(uint64_t);
            // This is the offset of the instruction to return to (one past the call instruction) from the start of the function
            uint32_t offset = GET(uint32_t);

            // Reserved
            GET(uint16_t);

            // There are three fake locations we're ignoring, representing the calling convention, the statepoint flags, and the numbef of deopt locations.
            // Those last two will always be zero unless the compiler is generating statepoint instructions manually, and even then those features are pretty much only for JITs.
            // After that come the real locations, in pairs of two.
            // We'll use "entries" here to refer to "locations" in the LLVM stack map, counting each pointer and the three fake ones.
            // "location" here will refer to `Location`s, each with two pointers and not including the fake ones.
            uint16_t num_entries = GET(uint16_t);
            assert(num_entries >= 3);
            uint16_t num_locations = (num_entries - 3) / 2;

            entry->stack_size = f->stack_size; 
            entry->ret_address = f->address+(uint64_t)offset;
            entry->num_locations = num_locations;
            Location* locations = num_locations > 0 ? (Location*)malloc(sizeof(Location)*num_locations) : NULL;
            entry->locations = locations;

            // Add to hash table
            stack_table_insert(entry->ret_address, entry_num);

            // Skip calling convention, flags, and deopt locations
            // If we don't care about verifying them, this would be faster:
            // ptr += 36;
            for (int l = 0; l < 3; l++) {
                uint8_t type = GET(uint8_t);
                assert(type == 0x4);
                // Reserved
                GET(uint8_t);

                uint16_t _size = GET(uint16_t);
                uint16_t _regnum = GET(uint16_t);
                // Reserved
                GET(uint16_t);
                int32_t value = GET(int32_t);
                switch (l) {
                case 0:
                    // We don't care about the calling convention
                    break;
                case 1:
                    // Flags should always be zero
                    assert(value == 0);
                    break;
                case 2:
                    // Deopt locations should always be zero
                    assert(value == 0);
                    break;
                default:
                    panic("unreachable\n");
                }
            }

            // The actual locations can technically describe values in registers and more complex situations, but with statepoints they will always be on the stack.
            // That's represented as an indirect location [reg + offset], type `0x3`, with register `rsp` which is number 7, and size 8 since it's one pointer.
            // LLVM can also put a group of pointers in one location with a size greater than 8, in which case there's a group of base pointers then a group of derived pointers.
            for (int l = 0; l < num_locations; l++) {
                // Base pointer
                {
                    uint8_t type = GET(uint8_t);
                    // Reserved
                    GET(uint8_t);

                    uint16_t size = GET(uint16_t);
                    uint16_t regnum = GET(uint16_t);
                    // Reserved
                    GET(uint16_t);
                    int32_t offset = GET(int32_t);

                    assert(type == 0x3);
                    assert(regnum == 7);
                    locations[l].base_offset = offset;
                    locations[l].num_pointers = (uint32_t)size / 8;
                }
                // Derived pointer
                {
                    uint8_t type = GET(uint8_t);
                    // Reserved
                    GET(uint8_t);

                    uint16_t size = GET(uint16_t);
                    uint16_t regnum = GET(uint16_t);
                    // Reserved
                    GET(uint16_t);
                    int32_t offset = GET(int32_t);

                    assert(type == 0x3);
                    assert((uint32_t)size == locations[l].num_pointers * 8);
                    assert(regnum == 7);
                    locations[l].derived_offset = offset;
                }
            }

            // Padding to align to 8 bytes
            if ((uint64_t)ptr & 7) {
                GET(uint32_t);
            }
            GET(uint16_t);

            // Live outs are another feature used in JITs that we don't have to worry about
            uint16_t nliveouts = GET(uint16_t);
            assert(nliveouts == 0);

            // Padding to align to 8 bytes
            // This is always required because it was aligned to 8 bytes 4 bytes ago
            GET(uint32_t);

            // Next table entry
            entry_num++;
            entry++;
        }
    }

    free(funcs);

    #undef GET
}
