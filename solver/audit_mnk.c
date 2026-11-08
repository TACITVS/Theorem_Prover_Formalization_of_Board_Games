#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define MAX_CELLS 64
#define MAX_LINES 256

int M, N, K, num_cells, num_lines;
uint64_t lines[MAX_LINES];

void init_lines(int m, int n, int k) {
    M = m; N = n; K = k;
    num_cells = m * n;
    num_lines = 0;
    for (int r = 0; r < m; r++) {
        for (int c = 0; c <= n - k; c++) {
            uint64_t mask = 0;
            for (int i = 0; i < k; i++) mask |= (1ULL << (r * n + c + i));
            lines[num_lines++] = mask;
        }
    }
    for (int c = 0; c < n; c++) {
        for (int r = 0; r <= m - k; r++) {
            uint64_t mask = 0;
            for (int i = 0; i < k; i++) mask |= (1ULL << ((r + i) * n + c));
            lines[num_lines++] = mask;
        }
    }
    for (int r = 0; r <= m - k; r++) {
        for (int c = 0; c <= n - k; c++) {
            uint64_t mask = 0;
            for (int i = 0; i < k; i++) mask |= (1ULL << ((r + i) * n + c + i));
            lines[num_lines++] = mask;
        }
    }
    for (int r = k - 1; r < m; r++) {
        for (int c = 0; c <= n - k; c++) {
            uint64_t mask = 0;
            for (int i = 0; i < k; i++) mask |= (1ULL << ((r - i) * n + c + i));
            lines[num_lines++] = mask;
        }
    }
}

int formula_lines(int m, int n, int k) {
    int h = (k <= n) ? m * (n - k + 1) : 0;
    int v = (k <= m) ? n * (m - k + 1) : 0;
    int d1 = (k <= m && k <= n) ? (m - k + 1) * (n - k + 1) : 0;
    int d2 = (k <= m && k <= n) ? (m - k + 1) * (n - k + 1) : 0;
    return h + v + d1 + d2;
}

static inline int check_win(uint64_t mask) {
    for (int i = 0; i < num_lines; i++) {
        if ((mask & lines[i]) == lines[i]) return 1;
    }
    return 0;
}

#define TT_SIZE (1 << 23)
#define TT_EXACT 1
#define TT_LOWER 2
#define TT_UPPER 3

typedef struct {
    uint64_t p1, p2;
    int8_t val;
    uint8_t flag;
    uint8_t depth;
} TTEntry;

TTEntry tt[TT_SIZE];

static inline uint32_t hash_pos(uint64_t p1, uint64_t p2) {
    uint64_t h = p1 * 0x517cc1b727220a95ULL ^ p2 * 0x6e2e0be880784dd1ULL;
    return (uint32_t)(h ^ (h >> 32)) & (TT_SIZE - 1);
}

int negamax(uint64_t p_turn, uint64_t p_opp, int alpha, int beta, int depth) {
    uint64_t occ = p_turn | p_opp;
    if (__builtin_popcountll(occ) == num_cells) return 0;

    uint32_t h = hash_pos(p_turn, p_opp);
    TTEntry* e = &tt[h];
    if (e->flag != 0 && e->p1 == p_turn && e->p2 == p_opp) {
        if (e->flag == TT_EXACT) return e->val;
        if (e->flag == TT_LOWER && e->val >= beta) return e->val;
        if (e->flag == TT_UPPER && e->val <= alpha) return e->val;
    }

    int orig_alpha = alpha;
    int best = -2;

    for (int c = 0; c < num_cells; c++) {
        if (!(occ & (1ULL << c))) {
            if (check_win(p_turn | (1ULL << c))) {
                best = 1;
                goto store;
            }
        }
    }

    for (int c = 0; c < num_cells; c++) {
        if (!(occ & (1ULL << c))) {
            uint64_t next_p_turn = p_turn | (1ULL << c);
            int score = -negamax(p_opp, next_p_turn, -beta, -alpha, depth + 1);
            if (score > best) best = score;
            if (score > alpha) alpha = score;
            if (alpha >= beta) break;
            if (best == 1) break;
        }
    }

store:
    e->p1 = p_turn;
    e->p2 = p_opp;
    e->val = (int8_t)best;
    e->depth = (uint8_t)depth;
    if (best <= orig_alpha) e->flag = TT_UPPER;
    else if (best >= beta) e->flag = TT_LOWER;
    else e->flag = TT_EXACT;
    return best;
}

int solve_mnk(int m, int n, int k) {
    init_lines(m, n, k);
    memset(tt, 0, sizeof(tt));
    return negamax(0, 0, -1, 1, 0);
}

int main(void) {
    printf("====================================================================\n");
    printf("       AUDIT & VERIFICATION SUITE: (m, n, k) POSITIONAL GAMES        \n");
    printf("====================================================================\n\n");

    // Pass 1: Line Counting Formula vs Explicit Hypergraph Generator
    printf("[PASS 1] Verifying Universal Line Counting Formula L(m, n, k)...\n");
    struct { int m, n, k, expected; } cases[] = {
        {3, 3, 3, 8},
        {3, 4, 3, 14},
        {4, 4, 4, 10},
        {5, 4, 4, 17},
        {6, 4, 4, 24},
        {7, 4, 4, 31},
        {8, 4, 4, 38},
        {5, 5, 4, 28},
        {8, 8, 5, 96},
        {15, 15, 5, 572}
    };
    for (size_t i = 0; i < sizeof(cases)/sizeof(cases[0]); i++) {
        init_lines(cases[i].m, cases[i].n, cases[i].k);
        int calc = formula_lines(cases[i].m, cases[i].n, cases[i].k);
        assert(calc == cases[i].expected);
        assert(num_lines == cases[i].expected);
        printf("  (%2d, %2d, %d): L = %3d (Formula: %3d) [OK]\n",
               cases[i].m, cases[i].n, cases[i].k, num_lines, calc);
    }
    printf("  -> PASS 1: All 10 landmark instances verified matching exact formula.\n\n");

    // Pass 2: Hypergraph Handshaking Lemma (Sum of cell degrees = k * L)
    printf("[PASS 2] Verifying Hypergraph Handshaking Identity: Sum deg(c) = k * L...\n");
    for (size_t i = 0; i < 7; i++) { // For cases fitting in 64 bits
        init_lines(cases[i].m, cases[i].n, cases[i].k);
        int sum_degrees = 0;
        for (int c = 0; c < num_cells; c++) {
            int deg = 0;
            for (int l = 0; l < num_lines; l++) {
                if (lines[l] & (1ULL << c)) deg++;
            }
            sum_degrees += deg;
        }
        assert(sum_degrees == cases[i].k * num_lines);
        printf("  (%2d, %2d, %d): Sum deg(c) = %3d = %d * %3d [OK]\n",
               cases[i].m, cases[i].n, cases[i].k, sum_degrees, cases[i].k, num_lines);
    }
    printf("  -> PASS 2: Hypergraph Handshaking identity confirmed.\n\n");

    // Pass 3: Game-Theoretic Value Verification
    printf("[PASS 3] Verifying Exact Game-Theoretic Values via Negamax Engine...\n");
    int val_333 = solve_mnk(3, 3, 3);
    printf("  (3, 3, 3) Classic Tic-Tac-Toe: %s (Expected: DRAW)\n",
           val_333 == 0 ? "DRAW [OK]" : "FAIL");
    assert(val_333 == 0);

    int val_343 = solve_mnk(3, 4, 3);
    printf("  (3, 4, 3) Rectangular Tic-Tac-Toe: %s (Expected: WIN P1)\n",
           val_343 == 1 ? "WIN FOR PLAYER 1 [OK]" : "FAIL");
    assert(val_343 == 1);

    int val_444 = solve_mnk(4, 4, 4);
    printf("  (4, 4, 4) 4x4 Tic-Tac-Toe: %s (Expected: DRAW)\n",
           val_444 == 0 ? "DRAW [OK]" : "FAIL");
    assert(val_444 == 0);

    int val_544 = solve_mnk(5, 4, 4);
    printf("  (5, 4, 4) Strip Tic-Tac-Toe: %s (Expected: DRAW)\n",
           val_544 == 0 ? "DRAW [OK]" : "FAIL");
    assert(val_544 == 0);

    printf("  -> PASS 3: Game-theoretic values fully match formal theorems!\n\n");
    printf("ALL AUDIT PASSES COMPLETED WITH ZERO ERRORS!\n");
    return 0;
}
