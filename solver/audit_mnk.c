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

/* Bounded-horizon strong-game search, independent of the negamax/TT engine:
   can the side to move force completing a line within d of its own moves,
   with the opponent never completing a line first?  (Mirrors forces_win.) */
static int owns_line(uint64_t me) {
    for (int i = 0; i < num_lines; i++) if ((me & lines[i]) == lines[i]) return 1;
    return 0;
}

static int forces_win_within(uint64_t me, uint64_t opp, int d) {
    uint64_t full = (num_cells == 64) ? ~0ULL : ((1ULL << num_cells) - 1);
    uint64_t empty = full & ~(me | opp);
    if (d <= 0) return 0;
    for (uint64_t cs = empty; cs; cs &= cs - 1)
        if (owns_line(me | (cs & -cs))) return 1;
    if (d == 1) return 0;
    for (uint64_t cs = empty; cs; cs &= cs - 1) {
        uint64_t mv = cs & -cs, me1 = me | mv, emp1 = empty & ~mv;
        if (!emp1) continue;                       /* board full: draw */
        int ok = 1;
        for (uint64_t rs = emp1; ok && rs; rs &= rs - 1) {
            uint64_t opp1 = opp | (rs & -rs);
            if (owns_line(opp1) || !forces_win_within(me1, opp1, d - 1)) ok = 0;
        }
        if (ok) return 1;
    }
    return 0;
}

/* Smallest d <= maxd with a forced win, or 0 if none. */
static int min_horizon(int m, int n, int k, int maxd) {
    init_lines(m, n, k);
    for (int d = 1; d <= maxd; d++) if (forces_win_within(0, 0, d)) return d;
    return 0;
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
        {15, 15, 5, 572},
        {7, 5, 3, 76},
        {11, 7, 5, 124},
        {13, 11, 7, 212},
        {11, 7, 7, 56},
        {17, 13, 11, 184},
        {19, 17, 13, 284}
    };
    for (size_t i = 0; i < sizeof(cases)/sizeof(cases[0]); i++) {
        int calc = formula_lines(cases[i].m, cases[i].n, cases[i].k);
        assert(calc == cases[i].expected);
        if (cases[i].m * cases[i].n <= MAX_CELLS && cases[i].expected <= MAX_LINES) {
            init_lines(cases[i].m, cases[i].n, cases[i].k);
            assert(num_lines == cases[i].expected);
        }
        printf("  (%2d, %2d, %2d): L = %3d (Formula: %3d) [OK]\n",
               cases[i].m, cases[i].n, cases[i].k, cases[i].expected, calc);
    }
    printf("  -> PASS 1: All 16 landmark and prime series instances verified matching exact formula.\n\n");

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

    // Pass 4: arithmetic hypothesis of the Erdos-Selfridge criterion.
    // (Only the inequality is checked here; the draw then follows from the cited
    //  Erdos-Selfridge theorem (1973) plus strategy stealing, which are not formalized.)
    printf("[PASS 4] Verifying the Erdos-Selfridge hypothesis L < 2^(k-1)...\n");
    struct { int m, n, k; const char* note; } prime_cases[] = {
        {11, 7, 7, "Prime dimensions (11, 7, 7)"},
        {17, 13, 11, "Consecutive prime triple (17, 13, 11)"},
        {19, 17, 13, "Consecutive prime triple (19, 17, 13)"}
    };
    for (size_t i = 0; i < sizeof(prime_cases)/sizeof(prime_cases[0]); i++) {
        int m = prime_cases[i].m;
        int n = prime_cases[i].n;
        int k = prime_cases[i].k;
        int L = formula_lines(m, n, k);
        uint64_t erdos_threshold = 1ULL << (k - 1);
        assert((uint64_t)L < erdos_threshold);
        printf("  %s: L(%d, %d, %d) = %d < 2^%d = %llu -> draw by Erdos-Selfridge [OK]\n",
               prime_cases[i].note, m, n, k, L, k - 1, (unsigned long long)erdos_threshold);
    }
    printf("  -> PASS 4: Erdos-Selfridge hypothesis holds for all three instances.\n\n");

    // Pass 5: exact forced-win horizons (in Player 1 moves) with an independent search.
    printf("[PASS 5] Verifying exact forced-win horizons in the strong game...\n");
    struct { int m, n, k, expect; } horizons[] = {
        {3, 3, 3, 0},   /* no forced win at all (5 P1 moves fill the board) */
        {3, 4, 3, 4}, {3, 5, 3, 4}, {3, 6, 3, 4}, {3, 7, 3, 4}, {3, 8, 3, 4},
        {4, 3, 3, 4}, {5, 3, 3, 4}, {6, 3, 3, 4},
        {4, 4, 3, 3}, {4, 5, 3, 3}, {5, 5, 3, 3}
    };
    for (size_t i = 0; i < sizeof(horizons)/sizeof(horizons[0]); i++) {
        int h = min_horizon(horizons[i].m, horizons[i].n, horizons[i].k, 5);
        assert(h == horizons[i].expect);
        if (h) printf("  (%d, %d, %d): P1 forces a win in exactly %d own moves = %d plies [OK]\n",
                      horizons[i].m, horizons[i].n, horizons[i].k, h, 2 * h - 1);
        else   printf("  (%d, %d, %d): no forced P1 win [OK]\n",
                      horizons[i].m, horizons[i].n, horizons[i].k);
    }
    printf("  -> PASS 5: horizons match the Rocq theorems (<= 7 plies for k = 3, max(m,n) >= 4).\n\n");

    // Pass 6: the former "subgrid projection" argument fails on 3 x 5.
    printf("[PASS 6] Replaying the refuted subgrid-projection line on 3 x 5...\n");
    init_lines(3, 5, 3);
    {
        uint64_t p1 = (1ULL << 1) | (1ULL << 0) | (1ULL << 6);  /* P1: 1, 0, 6 (= 3x4 moves 1, 0, 5) */
        uint64_t p2 = (1ULL << 3) | (1ULL << 2);                /* P2: 3, 2 */
        assert(!owns_line(p1) && !owns_line(p2));
        assert(owns_line(p2 | (1ULL << 4)));                    /* P2 plays (0, 4) and wins at ply 6 */
        printf("  P1 1, P2 3, P1 0, P2 2, P1 6, P2 4: Player 2 completes (0,2)-(0,3)-(0,4) [OK]\n");
    }
    printf("  -> PASS 6: exterior moves are NOT dummy moves; see MNKWindow.v for the sound argument.\n\n");

    printf("ALL AUDIT PASSES COMPLETED WITH ZERO ERRORS!\n");
    return 0;
}
