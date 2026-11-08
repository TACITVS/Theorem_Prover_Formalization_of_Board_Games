#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define MAX_CELLS 64
#define MAX_LINES 256

int M = 3, N = 4, K = 3;
int num_cells;
int num_lines;
uint64_t lines[MAX_LINES];

void init_lines(int m, int n, int k) {
    M = m; N = n; K = k;
    num_cells = m * n;
    num_lines = 0;
    // Horizontals
    for (int r = 0; r < m; r++) {
        for (int c = 0; c <= n - k; c++) {
            uint64_t mask = 0;
            for (int i = 0; i < k; i++) mask |= (1ULL << (r * n + c + i));
            lines[num_lines++] = mask;
        }
    }
    // Verticals
    for (int c = 0; c < n; c++) {
        for (int r = 0; r <= m - k; r++) {
            uint64_t mask = 0;
            for (int i = 0; i < k; i++) mask |= (1ULL << ((r + i) * n + c));
            lines[num_lines++] = mask;
        }
    }
    // Diag down-right
    for (int r = 0; r <= m - k; r++) {
        for (int c = 0; c <= n - k; c++) {
            uint64_t mask = 0;
            for (int i = 0; i < k; i++) mask |= (1ULL << ((r + i) * n + c + i));
            lines[num_lines++] = mask;
        }
    }
    // Diag up-right
    for (int r = k - 1; r < m; r++) {
        for (int c = 0; c <= n - k; c++) {
            uint64_t mask = 0;
            for (int i = 0; i < k; i++) mask |= (1ULL << ((r - i) * n + c + i));
            lines[num_lines++] = mask;
        }
    }
}

static inline int check_win(uint64_t mask) {
    for (int i = 0; i < num_lines; i++) {
        if ((mask & lines[i]) == lines[i]) return 1;
    }
    return 0;
}

// Transposition table
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
uint64_t node_count = 0;

static inline uint32_t hash_pos(uint64_t p1, uint64_t p2) {
    uint64_t h = p1 * 0x517cc1b727220a95ULL ^ p2 * 0x6e2e0be880784dd1ULL;
    return (uint32_t)(h ^ (h >> 32)) & (TT_SIZE - 1);
}

int negamax(uint64_t p_turn, uint64_t p_opp, int alpha, int beta, int depth) {
    node_count++;
    uint64_t occ = p_turn | p_opp;
    if (__builtin_popcountll(occ) == num_cells) return 0; // Draw

    uint32_t h = hash_pos(p_turn, p_opp);
    TTEntry* e = &tt[h];
    if (e->flag != 0 && e->p1 == p_turn && e->p2 == p_opp) {
        if (e->flag == TT_EXACT) return e->val;
        if (e->flag == TT_LOWER && e->val >= beta) return e->val;
        if (e->flag == TT_UPPER && e->val <= alpha) return e->val;
    }

    int orig_alpha = alpha;
    int best = -2;

    // Check immediate winning move
    for (int c = 0; c < num_cells; c++) {
        if (!(occ & (1ULL << c))) {
            if (check_win(p_turn | (1ULL << c))) {
                best = 1;
                goto store;
            }
        }
    }

    // Try moves
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

int main(int argc, char** argv) {
    int m = 3, n = 4, k = 3;
    if (argc >= 4) {
        m = atoi(argv[1]);
        n = atoi(argv[2]);
        k = atoi(argv[3]);
    }
    init_lines(m, n, k);
    printf("=== Positional (m, n, k) Game Solver ===\n");
    printf("Parameters: (%d, %d, %d) | Total Cells: %d | Total Winning Lines: %d\n",
           m, n, k, num_cells, num_lines);
    memset(tt, 0, sizeof(tt));
    node_count = 0;
    int val = negamax(0, 0, -1, 1, 0);
    printf("Nodes explored: %llu\n", (unsigned long long)node_count);
    printf("Game-Theoretic Value: %s (val = %d)\n", 
           val == 1 ? "WIN FOR PLAYER 1" : (val == 0 ? "DRAW" : "WIN FOR PLAYER 2"), val);
    return 0;
}
