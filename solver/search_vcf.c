/**
 * search_vcf.c - Heuristic VCF (Victory-Continue-Fours) Threat-Space Search for 5x5x5 Qubic
 * 
 * Searches threat-producing continuations of a supplied White-to-move position.
 * 
 * NOTE: Quiet setup moves are omitted. main() uses synthetic one-stone inputs,
 * which cannot create a four-stone threat on the next White move. Its negative
 * outputs provide no opening search bound and no minimax game-value proof.
 */

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

static inline int cell_index(int x, int y, int z) {
    return z * 25 + y * 5 + x;
}

void generate_lines() {
    line_count = 0;
    // 25 Ortho X
    for (int z = 0; z < 5; z++) for (int y = 0; y < 5; y++) {
        Line5 l; l.mask = 0;
        for (int x = 0; x < 5; x++) { int c = cell_index(x, y, z); l.cells[x] = c; l.mask |= ((u128)1 << c); }
        all_lines[line_count++] = l;
    }
    // 25 Ortho Y
    for (int z = 0; z < 5; z++) for (int x = 0; x < 5; x++) {
        Line5 l; l.mask = 0;
        for (int y = 0; y < 5; y++) { int c = cell_index(x, y, z); l.cells[y] = c; l.mask |= ((u128)1 << c); }
        all_lines[line_count++] = l;
    }
    // 25 Ortho Z
    for (int y = 0; y < 5; y++) for (int x = 0; x < 5; x++) {
        Line5 l; l.mask = 0;
        for (int z = 0; z < 5; z++) { int c = cell_index(x, y, z); l.cells[z] = c; l.mask |= ((u128)1 << c); }
        all_lines[line_count++] = l;
    }
    // 10 Diag XY
    for (int z = 0; z < 5; z++) {
        Line5 l1, l2; l1.mask = 0; l2.mask = 0;
        for (int i = 0; i < 5; i++) {
            int c1 = cell_index(i, i, z), c2 = cell_index(4 - i, i, z);
            l1.cells[i] = c1; l1.mask |= ((u128)1 << c1);
            l2.cells[i] = c2; l2.mask |= ((u128)1 << c2);
        }
        all_lines[line_count++] = l1; all_lines[line_count++] = l2;
    }
    // 10 Diag XZ
    for (int y = 0; y < 5; y++) {
        Line5 l1, l2; l1.mask = 0; l2.mask = 0;
        for (int i = 0; i < 5; i++) {
            int c1 = cell_index(i, y, i), c2 = cell_index(4 - i, y, i);
            l1.cells[i] = c1; l1.mask |= ((u128)1 << c1);
            l2.cells[i] = c2; l2.mask |= ((u128)1 << c2);
        }
        all_lines[line_count++] = l1; all_lines[line_count++] = l2;
    }
    // 10 Diag YZ
    for (int x = 0; x < 5; x++) {
        Line5 l1, l2; l1.mask = 0; l2.mask = 0;
        for (int i = 0; i < 5; i++) {
            int c1 = cell_index(x, i, i), c2 = cell_index(x, 4 - i, i);
            l1.cells[i] = c1; l1.mask |= ((u128)1 << c1);
            l2.cells[i] = c2; l2.mask |= ((u128)1 << c2);
        }
        all_lines[line_count++] = l1; all_lines[line_count++] = l2;
    }
    // 4 Space Diag
    Line5 s1, s2, s3, s4;
    s1.mask = 0; s2.mask = 0; s3.mask = 0; s4.mask = 0;
    for (int i = 0; i < 5; i++) {
        int c1 = cell_index(i, i, i), c2 = cell_index(4 - i, i, i);
        int c3 = cell_index(i, 4 - i, i), c4 = cell_index(4 - i, 4 - i, i);
        s1.cells[i] = c1; s1.mask |= ((u128)1 << c1);
        s2.cells[i] = c2; s2.mask |= ((u128)1 << c2);
        s3.cells[i] = c3; s3.mask |= ((u128)1 << c3);
        s4.cells[i] = c4; s4.mask |= ((u128)1 << c4);
    }
    all_lines[line_count++] = s1; all_lines[line_count++] = s2;
    all_lines[line_count++] = s3; all_lines[line_count++] = s4;
}

static inline int popcount128(u128 x) {
    uint64_t lo = (uint64_t)x;
    uint64_t hi = (uint64_t)(x >> 64);
    return __builtin_popcountll(lo) + __builtin_popcountll(hi);
}

// Check if player has completed a winning line
bool check_win(u128 board) {
    for (int l = 0; l < TOTAL_LINES; l++) {
        if ((board & all_lines[l].mask) == all_lines[l].mask) return true;
    }
    return false;
}

// Find all 4-threats for a player (lines with 4 stones and 1 empty cell)
// Populates defense_cells with the missing cell for each threat line.
int get_four_threats(u128 player, u128 opp, int *defense_cells) {
    int count = 0;
    for (int l = 0; l < TOTAL_LINES; l++) {
        u128 m = all_lines[l].mask;
        if ((opp & m) == 0) { // unblocked by opponent
            if (popcount128(player & m) == 4) {
                u128 empty_mask = m & ~(player & m);
                int c = -1;
                uint64_t lo = (uint64_t)empty_mask;
                if (lo != 0) {
                    c = __builtin_ctzll(lo);
                } else {
                    uint64_t hi = (uint64_t)(empty_mask >> 64);
                    if (hi != 0) {
                        c = 64 + __builtin_ctzll(hi);
                    }
                }
                if (c >= 0) {
                    defense_cells[count++] = c;
                }
            }
        }
    }
    return count;
}

// Deduplicate defense cells to find the number of distinct cells required to block threats
int count_unique_cells(const int *cells, int count, int *unique_out) {
    int u = 0;
    for (int i = 0; i < count; i++) {
        bool found = false;
        for (int j = 0; j < u; j++) {
            if (unique_out[j] == cells[i]) { found = true; break; }
        }
        if (!found) unique_out[u++] = cells[i];
    }
    return u;
}

// Recursive VCF search: can White force a win using ONLY continuous 4-threats?
bool search_vcf(u128 white, u128 black, int depth, int max_depth) {
    if (depth > max_depth) return false;

    // Check Black's existing 4-threats
    int opp_def[TOTAL_LINES];
    int opp_threats = get_four_threats(black, white, opp_def);
    int opp_unique[TOTAL_LINES];
    int opp_u = count_unique_cells(opp_def, opp_threats, opp_unique);

    if (opp_u > 1) {
        // Black has an unblockable double threat with distinct target cells.
        // White can only survive if White wins immediately on this move.
        for (int c = 0; c < TOTAL_CELLS; c++) {
            u128 bit = (u128)1 << c;
            if (((white | black) & bit) == 0 && check_win(white | bit)) return true;
        }
        return false;
    }

    // Try all possible White moves that create a 4-threat
    for (int c = 0; c < TOTAL_CELLS; c++) {
        u128 bit = (u128)1 << c;
        if (((white | black) & bit) != 0) continue;

        // Would this move immediately complete a 5-in-a-row?
        u128 next_w = white | bit;
        if (check_win(next_w)) return true;

        // If Black already had 1 threat, White's move must either win now or occupy that threat cell
        if (opp_u == 1 && c != opp_unique[0]) {
            // Did not block Black's threat, so unless White wins immediately (handled above), White loses
            continue;
        }

        // Check White's threats after this move
        int def_cells[TOTAL_LINES];
        int num_threats = get_four_threats(next_w, black, def_cells);
        if (num_threats == 0) continue; // Not a VCF move

        int unique_def[TOTAL_LINES];
        int num_unique = count_unique_cells(def_cells, num_threats, unique_def);

        if (num_unique >= 2) {
            // True double 4-threat: Black cannot block both distinct cells simultaneously!
            return true;
        }

        // Exactly 1 unique defense cell required: Black must play that unique cell
        int b_resp = unique_def[0];
        u128 next_b = black | ((u128)1 << b_resp);

        // Does Black's response win the game for Black?
        if (check_win(next_b)) continue;

        // Recurse down the threat chain
        if (search_vcf(next_w, next_b, depth + 1, max_depth)) return true;
    }
    return false;
}

int main() {
    generate_lines();
    printf("=======================================================================\n");
    printf("       RESTRICTED VCF SMOKE TEST ON SYNTHETIC ONE-STONE INPUTS        \n");
    printf("=======================================================================\n");

    // Representatives of the 10 cell orbits. These are synthetic White-to-move
    // test inputs, not legal histories after an actual White opening move.
    int canonical_openings[] = { 62, 0, 31, 12, 37, 32, 2, 6, 1, 7 };
    const char *names[] = {
        "Center (2,2,2)       [deg 13]",
        "Corner (0,0,0)       [deg  7]",
        "Sub-Center (1,1,1)   [deg  7]",
        "Face-Center (2,2,0)  [deg  5]",
        "Inner-Axis (2,2,1)   [deg  5]",
        "Inner-Planar (2,1,1) [deg  4]",
        "Edge-Center (2,0,0)  [deg  4]",
        "Outer-Flank (1,1,0)  [deg  4]",
        "Edge-Inner (1,0,0)   [deg  4]",
        "Face-Interior (2,1,0)[deg  3]"
    };

    printf("Threat-only continuations; quiet setup moves omitted (limit 8):\n\n");

    for (int i = 0; i < 10; i++) {
        int w1 = canonical_openings[i];
        printf("Orbit %2d: %-30s [cell %3d]... ", i + 1, names[i], w1);
        fflush(stdout);

        u128 white = ((u128)1 << w1);
        u128 black = 0;

        bool vcf = search_vcf(white, black, 1, 8);
        if (vcf) {
            printf("FORCED VCF WIN FOUND!\n");
        } else {
            printf("NO threat-only continuation from this input.\n");
        }
    }
    printf("\nThese one-stone inputs cannot create a four-stone threat on the next move.\n");
    printf("The test does not explore setup moves or establish an opening depth bound.\n");
    printf("The full game value remains unproved; see research-019 for verified bounds.\n");
    return 0;
}
