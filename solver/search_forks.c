#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#define TOTAL_CELLS 125
#define TOTAL_LINES 109

typedef unsigned __int128 u128;

typedef struct {
    int cells[5];
    u128 mask;
} Line5;

static Line5 all_lines[TOTAL_LINES];
static int line_count = 0;
static inline int cell_index(int x, int y, int z) { return x * 25 + y * 5 + z; }

void generate_lines() {
    line_count = 0;
    for (int x = 0; x < 5; x++) for (int y = 0; y < 5; y++) {
        Line5 l; l.mask = 0;
        for (int z = 0; z < 5; z++) { int c = cell_index(x, y, z); l.cells[z] = c; l.mask |= ((u128)1 << c); }
        all_lines[line_count++] = l;
    }
    for (int x = 0; x < 5; x++) for (int z = 0; z < 5; z++) {
        Line5 l; l.mask = 0;
        for (int y = 0; y < 5; y++) { int c = cell_index(x, y, z); l.cells[y] = c; l.mask |= ((u128)1 << c); }
        all_lines[line_count++] = l;
    }
    for (int y = 0; y < 5; y++) for (int z = 0; z < 5; z++) {
        Line5 l; l.mask = 0;
        for (int x = 0; x < 5; x++) { int c = cell_index(x, y, z); l.cells[x] = c; l.mask |= ((u128)1 << c); }
        all_lines[line_count++] = l;
    }
    for (int z = 0; z < 5; z++) {
        Line5 l1, l2; l1.mask = 0; l2.mask = 0;
        for (int i = 0; i < 5; i++) {
            int c1 = cell_index(i, i, z), c2 = cell_index(i, 4 - i, z);
            l1.cells[i] = c1; l1.mask |= ((u128)1 << c1);
            l2.cells[i] = c2; l2.mask |= ((u128)1 << c2);
        }
        all_lines[line_count++] = l1; all_lines[line_count++] = l2;
    }
    for (int y = 0; y < 5; y++) {
        Line5 l1, l2; l1.mask = 0; l2.mask = 0;
        for (int i = 0; i < 5; i++) {
            int c1 = cell_index(i, y, i), c2 = cell_index(i, y, 4 - i);
            l1.cells[i] = c1; l1.mask |= ((u128)1 << c1);
            l2.cells[i] = c2; l2.mask |= ((u128)1 << c2);
        }
        all_lines[line_count++] = l1; all_lines[line_count++] = l2;
    }
    for (int x = 0; x < 5; x++) {
        Line5 l1, l2; l1.mask = 0; l2.mask = 0;
        for (int i = 0; i < 5; i++) {
            int c1 = cell_index(x, i, i), c2 = cell_index(x, i, 4 - i);
            l1.cells[i] = c1; l1.mask |= ((u128)1 << c1);
            l2.cells[i] = c2; l2.mask |= ((u128)1 << c2);
        }
        all_lines[line_count++] = l1; all_lines[line_count++] = l2;
    }
    Line5 d1, d2, d3, d4;
    d1.mask = 0; d2.mask = 0; d3.mask = 0; d4.mask = 0;
    for (int i = 0; i < 5; i++) {
        int c1 = cell_index(i, i, i), c2 = cell_index(i, i, 4 - i);
        int c3 = cell_index(i, 4 - i, i), c4 = cell_index(i, 4 - i, 4 - i);
        d1.cells[i] = c1; d1.mask |= ((u128)1 << c1);
        d2.cells[i] = c2; d2.mask |= ((u128)1 << c2);
        d3.cells[i] = c3; d3.mask |= ((u128)1 << c3);
        d4.cells[i] = c4; d4.mask |= ((u128)1 << c4);
    }
    all_lines[line_count++] = d1; all_lines[line_count++] = d2;
    all_lines[line_count++] = d3; all_lines[line_count++] = d4;
}

static inline int popcount128(u128 x) {
    uint64_t lo = (uint64_t)x;
    uint64_t hi = (uint64_t)(x >> 64);
    return __builtin_popcountll(lo) + __builtin_popcountll(hi);
}

// Intersecting line pairs
typedef struct {
    int l1, l2;
    int common_cell;
} LinePair;

static LinePair intersecting_pairs[2000];
static int num_pairs = 0;

void find_intersecting_pairs() {
    num_pairs = 0;
    for (int i = 0; i < TOTAL_LINES; i++) {
        for (int j = i + 1; j < TOTAL_LINES; j++) {
            u128 common = all_lines[i].mask & all_lines[j].mask;
            if (common != 0) {
                int c = __builtin_ctzll((uint64_t)common);
                if (common >> 64) c = 64 + __builtin_ctzll((uint64_t)(common >> 64));
                intersecting_pairs[num_pairs].l1 = i;
                intersecting_pairs[num_pairs].l2 = j;
                intersecting_pairs[num_pairs].common_cell = c;
                num_pairs++;
            }
        }
    }
    printf("Total intersecting line pairs in 5x5x5: %d\n", num_pairs);
}

int main() {
    generate_lines();
    find_intersecting_pairs();

    // Check: For each pair of intersecting lines (l1, l2) with common cell c,
    // how many total cells do they span?
    // Since each line has 5 cells and they share 1 cell:
    // Exactly 5 + 5 - 1 = 9 cells!
    // For White to form a double threat at c:
    // White must occupy 3 cells in l1 \ {c} and 3 cells in l2 \ {c} (total 6 cells),
    // and Black must occupy ZERO cells in (l1 U l2)!
    // If Black plays even ONE stone anywhere in l1 U l2, that double threat is DEAD!
    printf("Theoretical Analysis of Double-Threat Forks in 5x5x5:\n");
    printf("1. Any two intersecting lines span exactly 9 cells (5 + 5 - 1).\n");
    printf("2. To form a double-threat fork at common cell c, White requires 6 stones in (l1 U l2) \\ {c}.\n");
    printf("3. If Black places even a SINGLE stone in l1, l1 cannot be won by White.\n");
    printf("4. If Black places even a SINGLE stone in l2, l2 cannot be won by White.\n");
    printf("5. Black has 6 defensive moves while White is accumulating 6 stones!\n");
    printf("6. Probability that Black fails to hit either line in 6 random moves: extremely low.\n");
    return 0;
}
