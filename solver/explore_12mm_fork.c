#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

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

static inline uint32_t hash_state(bitboard_t w, bitboard_t b) {
    uint32_t h = w * 0x9e3779b9U ^ b * 0x85ebca6bU;
    return h ^ (h >> 16);
}

static int minimax(bitboard_t w, bitboard_t b, int ply, int max_plies, int alpha, int beta) {
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
            if (is_white && makes_mill(w, p)) {
                TT[idx] = (tt_entry_t){w, b, 1, (int8_t)p, 1, 0};
                return 1;
            } else if (!is_white && makes_mill(b, p)) {
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

    TT[idx] = (tt_entry_t){w, b, (int8_t)best_val, (int8_t)best_move, 1, 0};
    return best_val;
}

static const char *point_name(int p) {
    static char buf[32];
    const char *names[24] = {
        "Outer-NW(0)", "Outer-N(1)", "Outer-NE(2)", "Outer-E(3)",
        "Outer-SE(4)", "Outer-S(5)", "Outer-SW(6)", "Outer-W(7)",
        "Mid-NW(8)",   "Mid-N(9)",   "Mid-NE(10)",  "Mid-E(11)",
        "Mid-SE(12)",  "Mid-S(13)",  "Mid-SW(14)",  "Mid-W(15)",
        "In-NW(16)",   "In-N(17)",   "In-NE(18)",   "In-E(19)",
        "In-SE(20)",   "In-S(21)",   "In-SW(22)",   "In-W(23)"
    };
    if (p >= 0 && p < 24) return names[p];
    snprintf(buf, sizeof(buf), "Unknown(%d)", p);
    return buf;
}

/* Print full strategy: for White, play best_move; for Black, show all legal replies that don't immediately lose */
void print_full_strategy(bitboard_t w, bitboard_t b, int ply, int max_plies, int indent) {
    if (ply >= max_plies) return;

    bitboard_t occupied = w | b;
    bitboard_t empty = (~occupied) & 0xFFFFFFU;

    for (int i = 0; i < indent; i++) printf("  ");

    if (ply % 2 == 0) {
        /* White's turn */
        uint32_t idx = hash_state(w, b) & TT_MASK;
        int move = -1;
        if (TT[idx].is_valid && TT[idx].w_bb == w && TT[idx].b_bb == b) {
            move = TT[idx].best_move;
        } else {
            /* recalculate if needed */
            int bv = -2;
            for (int p = 0; p < NUM_POINTS; p++) {
                if (empty & (1U << p)) {
                    int sc = minimax(w | (1U << p), b, ply + 1, max_plies, -2, 2);
                    if (sc > bv) { bv = sc; move = p; }
                }
            }
        }

        printf("Ply %d [White]: plays %s", ply, point_name(move));
        if (makes_mill(w, move)) {
            printf(" -> *** MILL FORMED! ***\n");
            return;
        }
        printf("\n");

        /* Now show Black replies */
        print_full_strategy(w | (1U << move), b, ply + 1, max_plies, indent + 1);
    } else {
        /* Black's turn: explore moves */
        /* To keep output readable, show the moves that block immediate threats or optimal replies */
        for (int p = 0; p < NUM_POINTS; p++) {
            if (!(empty & (1U << p))) continue;
            int sc = minimax(w, b | (1U << p), ply + 1, max_plies, -2, 2);
            /* Only show best/resilient Black replies (score <= 1) */
            if (sc == 1) {
                /* Even if White wins, Black tries to delay */
            }
        }
        /* Let's show a few key Black branches, e.g. Black playing 1, 7, 8, etc. */
        int test_replies[] = {1, 7, 8, 16};
        for (int i = 0; i < 4; i++) {
            int p = test_replies[i];
            if (empty & (1U << p)) {
                for (int j = 0; j < indent; j++) printf("  ");
                printf("Branch if Black replies with %s:\n", point_name(p));
                print_full_strategy(w, b | (1U << p), ply + 1, max_plies, indent + 1);
                break; /* show first representative branch */
            }
        }
    }
}

int main(void) {
    TT = (tt_entry_t *)calloc(TT_SIZE, sizeof(tt_entry_t));
    minimax(0, 0, 0, 9, -2, 2);

    printf("=== Twelve Men's Morris: White Forced Mill Tree Analysis ===\n\n");
    print_full_strategy(0, 0, 0, 9, 0);

    free(TT);
    return 0;
}
