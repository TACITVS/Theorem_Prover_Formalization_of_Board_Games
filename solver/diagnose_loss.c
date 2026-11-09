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

#define MAX_X (TOTAL_LINES * 2)
#define MAX_Y TOTAL_CELLS

static int matchX[MAX_X], matchY[MAX_Y], dist[MAX_X + 1], adj[MAX_X][5], adj_deg[MAX_X];

bool hk_bfs(int nx) {
    int queue[MAX_X], qhead = 0, qtail = 0;
    for (int u = 0; u < nx; u++) {
        if (matchX[u] == -1) { dist[u] = 0; queue[qtail++] = u; }
        else dist[u] = 1e9;
    }
    dist[nx] = 1e9;
    while (qhead < qtail) {
        int u = queue[qhead++];
        if (dist[u] < dist[nx]) {
            for (int i = 0; i < adj_deg[u]; i++) {
                int v = adj[u][i];
                int next_u = matchY[v];
                int d_next = (next_u == -1) ? dist[nx] : dist[next_u];
                if (d_next == 1e9) {
                    if (next_u != -1) { dist[next_u] = dist[u] + 1; queue[qtail++] = next_u; }
                    else dist[nx] = dist[u] + 1;
                }
            }
        }
    }
    return dist[nx] != 1e9;
}

bool hk_dfs(int u, int nx) {
    if (u != nx) {
        for (int i = 0; i < adj_deg[u]; i++) {
            int v = adj[u][i];
            int next_u = (matchY[v] == -1) ? nx : matchY[v];
            if (dist[next_u] == dist[u] + 1) {
                if (hk_dfs(next_u, nx)) {
                    matchY[v] = u; matchX[u] = v; return true;
                }
            }
        }
        dist[u] = 1e9; return false;
    }
    return true;
}

int hopcroft_karp(int nx, int ny) {
    for (int u = 0; u < nx; u++) matchX[u] = -1;
    for (int v = 0; v < ny; v++) matchY[v] = -1;
    int matching = 0;
    while (hk_bfs(nx)) {
        for (int u = 0; u < nx; u++) {
            if (matchX[u] == -1 && hk_dfs(u, nx)) matching++;
        }
    }
    return matching;
}

bool check_perfect_matching(u128 white, u128 black, int *out_unb) {
    int unblocked[TOTAL_LINES], num_unb = 0;
    for (int i = 0; i < TOTAL_LINES; i++) {
        if ((black & all_lines[i].mask) == 0) unblocked[num_unb++] = i;
    }
    *out_unb = num_unb;

    int cell_to_y[TOTAL_CELLS], num_u = 0;
    for (int c = 0; c < TOTAL_CELLS; c++) {
        if (((white | black) & ((u128)1 << c)) == 0) cell_to_y[c] = num_u++;
        else cell_to_y[c] = -1;
    }

    int nx = num_unb * 2;
    int ny = num_u;
    if (nx > ny) return false;

    for (int l = 0; l < num_unb; l++) {
        int orig = unblocked[l];
        int u1 = l * 2, u2 = l * 2 + 1;
        adj_deg[u1] = 0; adj_deg[u2] = 0;
        for (int j = 0; j < 5; j++) {
            int c = all_lines[orig].cells[j];
            int y = cell_to_y[c];
            if (y != -1) {
                adj[u1][adj_deg[u1]++] = y;
                adj[u2][adj_deg[u2]++] = y;
            }
        }
    }
    return hopcroft_karp(nx, ny) == nx;
}

static inline int popcount128(u128 x) {
    uint64_t lo = (uint64_t)x;
    uint64_t hi = (uint64_t)(x >> 64);
    return __builtin_popcountll(lo) + __builtin_popcountll(hi);
}

int pick_black_move(u128 white, u128 black) {
    // Priority 1: Block White 4-in-a-row (immediate threat)
    for (int l = 0; l < TOTAL_LINES; l++) {
        u128 m = all_lines[l].mask;
        if ((black & m) == 0 && popcount128(white & m) == 4) {
            u128 empty_mask = m & ~white;
            int c = __builtin_ctzll((uint64_t)empty_mask);
            if (empty_mask >> 64) c = 64 + __builtin_ctzll((uint64_t)(empty_mask >> 64));
            return c;
        }
    }

    // Priority 2: Block White 3-in-a-row fork
    int best_3_block = -1; int max_3 = 0;
    for (int c = 0; c < TOTAL_CELLS; c++) {
        u128 bit = (u128)1 << c;
        if (((white | black) & bit) != 0) continue;
        int count_3 = 0;
        for (int l = 0; l < TOTAL_LINES; l++) {
            u128 m = all_lines[l].mask;
            if ((m & bit) != 0 && (black & m) == 0 && popcount128(white & m) == 3) count_3++;
        }
        if (count_3 > max_3) { max_3 = count_3; best_3_block = c; }
    }
    if (max_3 > 0) return best_3_block;

    // Priority 3: Maximize surviving lines eliminated
    int best_c = -1; int max_elim = -1;
    for (int c = 0; c < TOTAL_CELLS; c++) {
        u128 bit = (u128)1 << c;
        if (((white | black) & bit) != 0) continue;
        int elim = 0;
        for (int l = 0; l < TOTAL_LINES; l++) {
            u128 m = all_lines[l].mask;
            if ((m & bit) != 0 && (black & m) == 0) elim++;
        }
        if (elim > max_elim) { max_elim = elim; best_c = c; }
    }
    return best_c;
}

static inline uint32_t fast_rand(uint32_t *state) {
    uint32_t x = *state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

int pick_white_move_adversarial(u128 white, u128 black, uint32_t *seed) {
    for (int l = 0; l < TOTAL_LINES; l++) {
        u128 m = all_lines[l].mask;
        if ((black & m) == 0 && popcount128(white & m) == 4) {
            u128 empty_mask = m & ~white;
            int c = __builtin_ctzll((uint64_t)empty_mask);
            if (empty_mask >> 64) c = 64 + __builtin_ctzll((uint64_t)(empty_mask >> 64));
            return c;
        }
    }

    int r = fast_rand(seed) % 100;
    if (r < 70) {
        int best_c = -1; double max_d = -1;
        for (int c = 0; c < TOTAL_CELLS; c++) {
            u128 bit = (u128)1 << c;
            if (((white | black) & bit) != 0) continue;
            double d = 0;
            for (int l = 0; l < TOTAL_LINES; l++) {
                u128 m = all_lines[l].mask;
                if ((m & bit) != 0 && (black & m) == 0) {
                    int wc = popcount128(white & m);
                    d += 1.0 / (double)(1 << (4 - wc));
                }
            }
            if (d > max_d) { max_d = d; best_c = c; }
        }
        if (best_c != -1) return best_c;
    }

    int empty_cells[TOTAL_CELLS], num_e = 0;
    for (int c = 0; c < TOTAL_CELLS; c++) {
        if (((white | black) & ((u128)1 << c)) == 0) empty_cells[num_e++] = c;
    }
    if (num_e == 0) return -1;
    return empty_cells[fast_rand(seed) % num_e];
}

int main() {
    generate_lines();
    int num_games = 10000;
    uint32_t seed = 42;

    for (int g = 0; g < num_games; g++) {
        uint32_t initial_seed = seed;
        u128 white = 0, black = 0;
        int w_moves[64], b_moves[64];
        int total_r = 0;
        bool white_won = false;

        for (int round = 1; round <= 62; round++) {
            int w = pick_white_move_adversarial(white, black, &seed);
            if (w == -1) break;
            white |= ((u128)1 << w);
            w_moves[round - 1] = w;
            total_r = round;

            for (int l = 0; l < TOTAL_LINES; l++) {
                if ((white & all_lines[l].mask) == all_lines[l].mask) {
                    white_won = true;
                    break;
                }
            }
            if (white_won) {
                printf("\n>>> DIAGNOSTIC: WHITE WON IN GAME %d (initial seed: %u) at Round %d! <<<\n", g + 1, initial_seed, round);
                printf("Moves played:\n");
                for (int i = 0; i < round; i++) {
                    if (i < round - 1)
                        printf("  Round %2d: White played %3d, Black played %3d\n", i + 1, w_moves[i], b_moves[i]);
                    else
                        printf("  Round %2d: White played %3d (WINNING MOVE!)\n", i + 1, w_moves[i]);
                }
                break;
            }

            int b = pick_black_move(white, black);
            if (b == -1) break;
            black |= ((u128)1 << b);
            b_moves[round - 1] = b;

            int unb;
            if (check_perfect_matching(white, black, &unb)) break;
        }
    }
    return 0;
}
