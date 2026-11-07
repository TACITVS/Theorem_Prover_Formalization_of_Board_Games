#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>

#define NUM_POINTS 24

typedef uint32_t bitboard_t;

/* 16 Mills of Nine Men's Morris */
static const bitboard_t MILLS_9[16] = {
    7U, 28U, 112U, 193U,
    1792U, 7168U, 28672U, 49408U,
    458752U, 1835008U, 7340032U, 12648448U,
    131586U, 526344U, 2105376U, 8421504U
};

static inline bool makes_mill_9(bitboard_t bb, int pt) {
    bitboard_t next = bb | (1U << pt);
    for (int i = 0; i < 16; i++) {
        if ((MILLS_9[i] & (1U << pt)) && ((next & MILLS_9[i]) == MILLS_9[i])) return true;
    }
    return false;
}

#define TT_BITS 24
#define TT_SIZE (1U << TT_BITS)
#define TT_MASK (TT_SIZE - 1)

typedef struct {
    uint32_t w_bb;
    uint32_t b_bb;
    int8_t val;
    int8_t best_move;
    uint8_t is_valid;
    uint8_t pad;
} tt_entry_t;

static tt_entry_t *TT;
static unsigned long long nodes = 0;

static inline uint32_t hash_state(bitboard_t w, bitboard_t b) {
    uint32_t h = w * 0x9e3779b9U ^ b * 0x85ebca6bU;
    return h ^ (h >> 16);
}

static int minimax_9(bitboard_t w, bitboard_t b, int ply, int max_plies, int alpha, int beta) {
    nodes++;
    if (ply == max_plies) return 0;

    bitboard_t occupied = w | b;
    bool is_white = (ply % 2 == 0);

    uint32_t idx = hash_state(w, b) & TT_MASK;
    if (TT[idx].is_valid && TT[idx].w_bb == w && TT[idx].b_bb == b) {
        return TT[idx].val;
    }

    bitboard_t empty = (~occupied) & 0xFFFFFFU;

    for (int p = 0; p < NUM_POINTS; p++) {
        if (empty & (1U << p)) {
            if (is_white && makes_mill_9(w, p)) {
                TT[idx] = (tt_entry_t){w, b, 1, (int8_t)p, 1, 0};
                return 1;
            } else if (!is_white && makes_mill_9(b, p)) {
                TT[idx] = (tt_entry_t){w, b, -1, (int8_t)p, 1, 0};
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
            score = minimax_9(w | (1U << p), b, ply + 1, max_plies, alpha, beta);
            if (score > best_val) {
                best_val = score;
                best_move = p;
            }
            if (best_val > alpha) alpha = best_val;
            if (beta <= alpha) break;
        } else {
            score = minimax_9(w, b | (1U << p), ply + 1, max_plies, alpha, beta);
            if (score < best_val) {
                best_val = score;
                best_move = p;
            }
            if (best_val < beta) beta = best_val;
            if (beta <= alpha) break;
        }
    }

    TT[idx] = (tt_entry_t){w, b, (int8_t)best_val, (int8_t)best_move, 1, 0};
    return best_val;
}

int main(int argc, char **argv) {
    int max_plies = (argc > 1) ? atoi(argv[1]) : 18;
    printf("=== Nine Men's Morris: Phase 1 Mill Race Solver ===\n");
    printf("Searching up to %d plies...\n", max_plies);

    TT = (tt_entry_t *)calloc(TT_SIZE, sizeof(tt_entry_t));
    if (!TT) { printf("TT alloc failed!\n"); return 1; }

    clock_t start = clock();
    int result = minimax_9(0, 0, 0, max_plies, -2, 2);
    clock_t end = clock();

    double sec = (double)(end - start) / CLOCKS_PER_SEC;
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
