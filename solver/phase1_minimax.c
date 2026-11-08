#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>

#define NUM_POINTS 24

typedef uint32_t bitboard_t;

static const bitboard_t MILLS_12[20] = {
    7U, 28U, 112U, 193U,
    1792U, 7168U, 28672U, 49408U,
    458752U, 1835008U, 7340032U, 12648448U,
    131586U, 526344U, 2105376U, 8421504U,
    (1U << 0) | (1U << 8) | (1U << 16),
    (1U << 2) | (1U << 10) | (1U << 18),
    (1U << 4) | (1U << 12) | (1U << 20),
    (1U << 6) | (1U << 14) | (1U << 22)
};

static inline bool makes_mill(bitboard_t bb, int pt) {
    bitboard_t next = bb | (1U << pt);
    for (int i = 0; i < 20; i++) {
        if ((MILLS_12[i] & (1U << pt)) && ((next & MILLS_12[i]) == MILLS_12[i])) return true;
    }
    return false;
}

/* Transposition Table with exact/lower/upper bound flags and depth */
#define TT_BITS 24
#define TT_SIZE (1U << TT_BITS)
#define TT_MASK (TT_SIZE - 1)

#define TT_EXACT 1
#define TT_LOWER 2
#define TT_UPPER 3

typedef struct {
    uint32_t w_bb;
    uint32_t b_bb;
    int8_t val;
    int8_t best_move;
    uint8_t flag;
    uint8_t depth;
} tt_entry_t;

static tt_entry_t *TT;
static unsigned long long nodes = 0;

static inline uint32_t hash_state(bitboard_t w, bitboard_t b) {
    uint32_t h = (w * 0x9e3779b9U) ^ (b * 0x85ebca6bU);
    return h ^ (h >> 16);
}

/* Minimax for Phase 1 Mill Race:
   +1: White can force forming a mill first
   -1: Black can force forming a mill first
    0: Draw (neither can force a mill within max_plies)
*/
static int minimax(bitboard_t w, bitboard_t b, int ply, int max_plies, int alpha, int beta) {
    nodes++;
    if (ply == max_plies) return 0;

    int orig_alpha = alpha;
    int orig_beta = beta;
    uint8_t rem_depth = (uint8_t)(max_plies - ply);

    bitboard_t occupied = w | b;
    bool is_white = (ply % 2 == 0);

    /* TT lookup with bound-type and remaining-depth validation */
    uint32_t idx = hash_state(w, b) & TT_MASK;
    if (TT[idx].flag != 0 && TT[idx].w_bb == w && TT[idx].b_bb == b && TT[idx].depth >= rem_depth) {
        if (TT[idx].flag == TT_EXACT) return TT[idx].val;
        if (TT[idx].flag == TT_LOWER && TT[idx].val >= beta) return TT[idx].val;
        if (TT[idx].flag == TT_UPPER && TT[idx].val <= alpha) return TT[idx].val;
    }

    /* Move generation: all empty spots */
    bitboard_t empty = (~occupied) & 0xFFFFFFU;

    /* Immediate mill check */
    for (int p = 0; p < NUM_POINTS; p++) {
        if (empty & (1U << p)) {
            if (is_white && makes_mill(w, p)) {
                TT[idx] = (tt_entry_t){w, b, 1, (int8_t)p, TT_EXACT, rem_depth};
                return 1;
            } else if (!is_white && makes_mill(b, p)) {
                TT[idx] = (tt_entry_t){w, b, -1, (int8_t)p, TT_EXACT, rem_depth};
                return -1;
            }
        }
    }

    int best_val = is_white ? -2 : 2;
    int best_move = -1;

    for (int p = 0; p < NUM_POINTS; p++) {
        if (!(empty & (1U << p))) continue;

        int score;
        if (is_white) {
            score = minimax(w | (1U << p), b, ply + 1, max_plies, alpha, beta);
            if (score > best_val) {
                best_val = score;
                best_move = p;
            }
            if (best_val > alpha) alpha = best_val;
            if (beta <= alpha) break;
        } else {
            score = minimax(w, b | (1U << p), ply + 1, max_plies, alpha, beta);
            if (score < best_val) {
                best_val = score;
                best_move = p;
            }
            if (best_val < beta) beta = best_val;
            if (beta <= alpha) break;
        }
    }

    uint8_t flag = (best_val <= orig_alpha) ? TT_UPPER :
                   (best_val >= orig_beta)  ? TT_LOWER : TT_EXACT;
    TT[idx] = (tt_entry_t){w, b, (int8_t)best_val, (int8_t)best_move, flag, rem_depth};
    return best_val;
}

int main(int argc, char **argv) {
    int max_plies = (argc > 1) ? atoi(argv[1]) : 9;
    printf("=== Twelve Men's Morris: Phase 1 Mill Race Solver ===\n");
    printf("Searching up to %d plies...\n", max_plies);

    TT = (tt_entry_t *)calloc(TT_SIZE, sizeof(tt_entry_t));
    if (!TT) { printf("TT alloc failed!\n"); return 1; }

    clock_t start = clock();
    int result = minimax(0, 0, 0, max_plies, -2, 2);
    clock_t end = clock();

    double sec = (double)(end - start) / CLOCKS_PER_SEC;
    if (sec <= 0.0) sec = 0.001;
    printf("Result: %d (%s)\n", result,
           result == 1 ? "White forces a mill!" :
           result == -1 ? "Black forces a mill!" : "Draw (No mills formed)");
    printf("Explored %llu nodes in %.3f seconds (%.2fM nodes/sec)\n",
           nodes, sec, (nodes / sec) / 1e6);

    uint32_t idx = hash_state(0, 0) & TT_MASK;
    printf("White optimal opening move: Point %d\n", TT[idx].best_move);

    free(TT);
    return 0;
}
