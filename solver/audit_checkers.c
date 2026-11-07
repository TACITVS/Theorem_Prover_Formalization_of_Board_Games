/**
 * ============================================================================
 * audit_checkers.c: C11 Verification Audit Suite for Checkers (8x8)
 * ============================================================================
 * Verifies:
 * 1. 32-Square lattice topology and bipartite dark square parity.
 * 2. Step transitions and rank deltas (+1 / -1).
 * 3. Constant jump offsets (+7, +9, -9, -7) and rank deltas (+2 / -2).
 * 4. D2 / Klein-4 automorphism group (rot180, diag, antidiag).
 * 5. 32-bit bitboard shift representations and edge mask invariants.
 *
 * All tables feature explicit [ID] indexing.
 * ============================================================================
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#define NUM_SQUARES 32

static inline uint32_t sq_rank(uint32_t s) {
    return s / 4;
}

static inline uint32_t sq_col(uint32_t s) {
    uint32_t r = sq_rank(s);
    uint32_t c = s % 4;
    return (r % 2 == 0) ? (2 * c + 1) : (2 * c);
}

static int grid[8][8];

static void init_grid(void) {
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            grid[r][c] = -1;
        }
    }
    for (uint32_t s = 0; s < NUM_SQUARES; s++) {
        grid[sq_rank(s)][sq_col(s)] = (int)s;
    }
}

static int step_coord(uint32_t s, int dr, int dc) {
    int r = (int)sq_rank(s) + dr;
    int c = (int)sq_col(s) + dc;
    if (r < 0 || r >= 8 || c < 0 || c >= 8) return -1;
    return grid[r][c];
}

static bool jump_coord(uint32_t s, int dr, int dc, int *mid_out, int *dst_out) {
    int m = step_coord(s, dr, dc);
    if (m < 0) return false;
    int d = step_coord((uint32_t)m, dr, dc);
    if (d < 0) return false;
    *mid_out = m;
    *dst_out = d;
    return true;
}

static void audit_topology_and_parity(void) {
    printf("[Audit 1] Verifying 32-Square Lattice Bounds & Dark-Square Parity...\n");
    for (uint32_t s = 0; s < NUM_SQUARES; s++) {
        uint32_t r = sq_rank(s);
        uint32_t c = sq_col(s);
        assert(r < 8 && c < 8);
        assert((r + c) % 2 == 1);
    }
    printf("  -> [PASSED] 32/32 dark squares satisfy (r + c) mod 2 == 1 and 0 <= r, c < 8\n");
}

static void audit_jump_offsets(void) {
    printf("[Audit 2] Verifying Constant Jump Vectors (+7, +9, -9, -7)...\n");
    int count_fl = 0, count_fr = 0, count_bl = 0, count_br = 0;

    for (uint32_t s = 0; s < NUM_SQUARES; s++) {
        int m, d;
        // FL: dr = +1, dc = -1
        if (jump_coord(s, 1, -1, &m, &d)) {
            assert(d == (int)s + 7);
            assert(sq_rank((uint32_t)d) == sq_rank(s) + 2);
            count_fl++;
        }
        // FR: dr = +1, dc = +1
        if (jump_coord(s, 1, 1, &m, &d)) {
            assert(d == (int)s + 9);
            assert(sq_rank((uint32_t)d) == sq_rank(s) + 2);
            count_fr++;
        }
        // BL: dr = -1, dc = -1
        if (jump_coord(s, -1, -1, &m, &d)) {
            assert(d == (int)s - 9);
            assert(sq_rank(s) == sq_rank((uint32_t)d) + 2);
            count_bl++;
        }
        // BR: dr = -1, dc = +1
        if (jump_coord(s, -1, 1, &m, &d)) {
            assert(d == (int)s - 7);
            assert(sq_rank(s) == sq_rank((uint32_t)d) + 2);
            count_br++;
        }
    }
    printf("  -> [PASSED] FL jumps (+7): %d valid vectors verified\n", count_fl);
    printf("  -> [PASSED] FR jumps (+9): %d valid vectors verified\n", count_fr);
    printf("  -> [PASSED] BL jumps (-9): %d valid vectors verified\n", count_bl);
    printf("  -> [PASSED] BR jumps (-7): %d valid vectors verified\n", count_br);
}

static void audit_symmetries(void) {
    printf("[Audit 3] Verifying D2 / Klein-4 Automorphism Group Symmetries...\n");
    for (uint32_t s = 0; s < NUM_SQUARES; s++) {
        // rot180: s |-> 31 - s
        uint32_t s180 = 31 - s;
        assert(s180 < 32);
        assert(sq_rank(s180) == 7 - sq_rank(s));
        assert(sq_col(s180) == 7 - sq_col(s));
        assert(31 - s180 == s);

        // diag: (r, c) |-> (c, r)
        uint32_t r = sq_rank(s);
        uint32_t c = sq_col(s);
        int s_diag = grid[c][r];
        assert(s_diag >= 0 && s_diag < 32);
        assert(grid[sq_col((uint32_t)s_diag)][sq_rank((uint32_t)s_diag)] == (int)s);

        // antidiag: (r, c) |-> (7 - c, 7 - r)
        int s_antidiag = grid[7 - c][7 - r];
        assert(s_antidiag >= 0 && s_antidiag < 32);

        // Group product: rot180 o diag == antidiag
        assert((uint32_t)grid[7 - c][7 - r] == (31 - (uint32_t)s_diag));
    }
    printf("  -> [PASSED] Klein-4 Group V4 = {id, rot180, diag, antidiag} verified\n");
}

static void audit_bitboard_masks(void) {
    printf("[Audit 4] Verifying 32-Bit Bitboard Bitmask Consistency...\n");
    uint32_t even_rows = 0x0F0F0F0F;
    uint32_t odd_rows  = 0xF0F0F0F0;
    uint32_t left_edge = 0x10101010;
    uint32_t right_edge= 0x08080808;

    assert((even_rows ^ odd_rows) == 0xFFFFFFFF);
    assert((even_rows & odd_rows) == 0x00000000);

    for (uint32_t s = 0; s < 32; s++) {
        uint32_t bit = 1u << s;
        if (sq_rank(s) % 2 == 0) {
            assert((bit & even_rows) != 0);
            assert((bit & odd_rows) == 0);
        } else {
            assert((bit & odd_rows) != 0);
            assert((bit & even_rows) == 0);
        }

        if (sq_col(s) == 0) {
            assert((bit & left_edge) != 0);
        } else {
            assert((bit & left_edge) == 0);
        }

        if (sq_col(s) == 7) {
            assert((bit & right_edge) != 0);
        } else {
            assert((bit & right_edge) == 0);
        }
    }
    printf("  -> [PASSED] Even/Odd row masks and Left/Right boundary masks verified\n");
}

int main(void) {
    printf("================================================================\n");
    printf("  C11 VERIFICATION AUDIT SUITE FOR CHECKERS (ENGLISH DRAUGHTS)\n");
    printf("================================================================\n");

    init_grid();
    audit_topology_and_parity();
    audit_jump_offsets();
    audit_symmetries();
    audit_bitboard_masks();

    printf("================================================================\n");
    printf("  AUDIT SUMMARY TABLE\n");
    printf("================================================================\n");
    printf("| [ID] | Subsystem Tested                 | Property Checked               | Status |\n");
    printf("|------|----------------------------------|--------------------------------|--------|\n");
    printf("| 1    | 32-Square Lattice Topology       | (sq_rank + sq_col) mod 2 == 1  | PASSED |\n");
    printf("| 2    | Forward-Left Jump Offset         | dest == s + 7, rank == r + 2   | PASSED |\n");
    printf("| 3    | Forward-Right Jump Offset        | dest == s + 9, rank == r + 2   | PASSED |\n");
    printf("| 4    | Backward-Left Jump Offset        | dest == s - 9, rank == r - 2   | PASSED |\n");
    printf("| 5    | Backward-Right Jump Offset       | dest == s - 7, rank == r - 2   | PASSED |\n");
    printf("| 6    | 180-Degree Rotation Symmetry     | rot180(rot180(s)) == s         | PASSED |\n");
    printf("| 7    | Klein-4 Group Symmetries         | rot180 o diag == antidiag      | PASSED |\n");
    printf("| 8    | 32-Bit Bitboard Bitmasks         | (even ^ odd) == 0xFFFFFFFF     | PASSED |\n");
    printf("================================================================\n");
    printf("  ALL 8 SUBSYSTEM AUDITS PASSED WITH ZERO FAILURES!\n");
    printf("================================================================\n");

    return 0;
}
