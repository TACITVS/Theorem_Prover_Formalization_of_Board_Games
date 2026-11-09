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

// Check if White has already won
bool check_win(u128 board) {
    for (int l = 0; l < TOTAL_LINES; l++) {
        if ((board & all_lines[l].mask) == all_lines[l].mask) return true;
    }
    return false;
}

// Find all 4-threats for a player (lines with 4 stones and 1 empty cell)
int get_four_threats(u128 player, u128 opp, int *defense_cells) {
    int count = 0;
    for (int l = 0; l < TOTAL_LINES; l++) {
        u128 m = all_lines[l].mask;
        if ((opp & m) == 0) { // unblocked by opponent
            if (popcount128(player & m) == 4) {
                // Find the empty cell
                u128 empty_mask = m & ~(player & m);
                // Get the bit position
                int c = __builtin_ctzll((uint64_t)empty_mask);
                if (empty_mask >> 64) c = 64 + __builtin_ctzll((uint64_t)(empty_mask >> 64));
                defense_cells[count++] = c;
            }
        }
    }
    return count;
}

// Recursive VCF search: can White force a win using ONLY continuous 4-threats?
bool search_vcf(u128 white, u128 black, int depth, int max_depth) {
    if (depth > max_depth) return false;

    // Check if White already has a 4-threat that gives immediate win
    int opp_def[TOTAL_LINES];
    int opp_threats = get_four_threats(black, white, opp_def);
    if (opp_threats > 1) return false; // Black has a double threat, White cannot ignore unless White wins now
    if (opp_threats == 1) {
        // White MUST either win on this move or block Black's threat with a threat of their own
    }

    // Try all possible White moves that create a 4-threat
    for (int c = 0; c < TOTAL_CELLS; c++) {
        u128 bit = (u128)1 << c;
        if (((white | black) & bit) != 0) continue;

        // Would this move immediately complete a 5-in-a-row?
        u128 next_w = white | bit;
        if (check_win(next_w)) return true;

        // Check if this move creates at least one 4-threat
        int def_cells[TOTAL_LINES];
        int num_threats = get_four_threats(next_w, black, def_cells);
        if (num_threats == 0) continue; // Not a VCF move

        if (num_threats >= 2) {
            // Double 4-threat! Black can only block one, White wins!
            return true;
        }

        // Exactly 1 threat: Black is forced to respond at def_cells[0]
        int b_resp = def_cells[0];
        u128 next_b = black | ((u128)1 << b_resp);

        // Does Black's response win the game for Black?
        if (check_win(next_b)) continue;

        // Recurse
        if (search_vcf(next_w, next_b, depth + 1, max_depth)) return true;
    }
    return false;
}

int main() {
    generate_lines();
    printf("=======================================================================\n");
    printf("    SEARCHING FOR WHITE FORCED VCF SEQUENCES IN 5x5x5 TIC-TAC-TOE      \n");
    printf("=======================================================================\n");

    // Canonical opening orbits:
    int canonical_openings[] = { 62, 0, 31, 12, 1, 7, 5, 27, 2 };
    const char *names[] = {
        "Center (2,2,2)", "Corner (0,0,0)", "Sub-Center (1,1,1)",
        "Face-Center (2,2,0)", "Inner-Face (1,2,0)", "Outer-Flank (0,1,1)",
        "Edge-Inner (0,1,0)", "Inner-Planar (1,1,2)", "Flank (0,0,2)"
    };

    for (int i = 0; i < 9; i++) {
        int w1 = canonical_openings[i];
        printf("Testing opening: %-25s [cell %3d]... ", names[i], w1);
        fflush(stdout);

        u128 white = ((u128)1 << w1);
        u128 black = 0;

        // Search VCF up to depth 8 (8 consecutive 4-threats)
        bool vcf = search_vcf(white, black, 1, 8);
        if (vcf) {
            printf("FORCED VCF WIN FOUND!\n");
        } else {
            printf("NO forced VCF sequence (depth <= 8).\n");
        }
    }
    return 0;
}
