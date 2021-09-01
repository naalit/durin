#ifndef __RUNTIME_COMMON_H__
#define __RUNTIME_COMMON_H__

#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>
#include <time.h>
#include <string.h>

// A separate function so it can be a breakpoint
static void panic_exit() {
    exit(1);
}

#define panic(...) { printf(__VA_ARGS__); panic_exit(); }

static struct {
    uint32_t len;
    void* roots[32];
} extra_roots;
static void push_extra_root(void* root) {
    if (extra_roots.len >= 32)
        panic("Ran out of space for extra roots!");
    extra_roots.roots[extra_roots.len++] = root;
}
static void* pop_extra_root() {
    if (extra_roots.len < 0)
        panic("No root to pop!");
    return extra_roots.roots[--extra_roots.len];
}

static bool bitset_get(uint64_t* bitset, uint32_t bit) {
    uint32_t i = bit / 64;
    // printf("i = %u\n", i);
    uint32_t first_bit = i * 64;
    uint32_t bit_idx = bit - first_bit;
    return (bitset[i] & (1UL << bit_idx)) != 0;
}

static void bitset_set(uint64_t* bitset, uint32_t bit) {
    uint32_t i = bit / 64;
    uint32_t first_bit = i * 64;
    uint32_t bit_idx = bit - first_bit;
    bitset[i] |= (1UL << bit_idx);
}

// Sets all bits `start <= i < end` to 1.
// This function uses bitmasks to work in parallel, so it's O(number of words affected).
// TODO SIMD?
static void bitset_set_range(uint64_t* bitset, uint32_t start, uint32_t end) {
    uint32_t start_word = start / 64;
    uint32_t end_word = end / 64;
    uint32_t first_bit = start_word * 64;
    uint32_t last_word_first_bit = end_word * 64;

    uint32_t start_bit_idx = start - first_bit;
    uint32_t end_bit_idx = end - last_word_first_bit;

    // We don't need to do the last word if we're not going to set anything in it
    uint32_t real_end = end_bit_idx != 0 || start_word == end_word ? end_word : end_word - 1;

    for (uint32_t word = start_word; word <= real_end; word++) {
        uint64_t mask = ~0UL;

        if (word == start_word)
            mask &= ~((1UL << start_bit_idx) - 1);
        if (word == end_word)
            mask &= ((1UL << end_bit_idx) - 1);

        bitset[word] |= mask;
    }
}

#endif
