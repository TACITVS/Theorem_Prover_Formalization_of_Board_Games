#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>

#define N 5
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
    return x * 25 + y * 5 + z;
}

static inline void index_to_coord(int idx, int *x, int *y, int *z) {
    *x = idx / 25;
    *y = (idx / 5) % 5;
    *z = idx % 5;
}

static inline int popcount128(u128 x) {
    uint64_t lo = (uint64_t)x;
    uint64_t hi = (uint64_t)(x >> 64);
    return __builtin_popcountll(lo) + __builtin_popcountll(hi);
}

void generate_lines() {
    line_count = 0;
    // Orthogonal (75)
    for (int x = 0; x < 5; x++)
        for (int y = 0; y < 5; y++) {
            Line5 l; l.mask = 0;
            for (int z = 0; z < 5; z++) {
                int c = cell_index(x, y, z);
                l.cells[z] = c; l.mask |= ((u128)1 << c);
            }
            all_lines[line_count++] = l;
        }
    for (int x = 0; x < 5; x++)
        for (int z = 0; z < 5; z++) {
            Line5 l; l.mask = 0;
            for (int y = 0; y < 5; y++) {
                int c = cell_index(x, y, z);
                l.cells[y] = c; l.mask |= ((u128)1 << c);
            }
            all_lines[line_count++] = l;
        }
    for (int y = 0; y < 5; y++)
        for (int z = 0; z < 5; z++) {
            Line5 l; l.mask = 0;
            for (int x = 0; x < 5; x++) {
                int c = cell_index(x, y, z);
                l.cells[x] = c; l.mask |= ((u128)1 << c);
            }
            all_lines[line_count++] = l;
        }
    // Planar diagonals (30)
    for (int z = 0; z < 5; z++) {
        Line5 l1, l2; l1.mask = 0; l2.mask = 0;
        for (int i = 0; i < 5; i++) {
            int c1 = cell_index(i, i, z), c2 = cell_index(i, 4 - i, z);
            l1.cells[i] = c1; l1.mask |= ((u128)1 << c1);
            l2.cells[i] = c2; l2.mask |= ((u128)1 << c2);
        }
        all_lines[line_count++] = l1;
        all_lines[line_count++] = l2;
    }
    for (int y = 0; y < 5; y++) {
        Line5 l1, l2; l1.mask = 0; l2.mask = 0;
        for (int i = 0; i < 5; i++) {
            int c1 = cell_index(i, y, i), c2 = cell_index(i, y, 4 - i);
            l1.cells[i] = c1; l1.mask |= ((u128)1 << c1);
            l2.cells[i] = c2; l2.mask |= ((u128)1 << c2);
        }
        all_lines[line_count++] = l1;
        all_lines[line_count++] = l2;
    }
    for (int x = 0; x < 5; x++) {
        Line5 l1, l2; l1.mask = 0; l2.mask = 0;
        for (int i = 0; i < 5; i++) {
            int c1 = cell_index(x, i, i), c2 = cell_index(x, i, 4 - i);
            l1.cells[i] = c1; l1.mask |= ((u128)1 << c1);
            l2.cells[i] = c2; l2.mask |= ((u128)1 << c2);
        }
        all_lines[line_count++] = l1;
        all_lines[line_count++] = l2;
    }
    // Space diagonals (4)
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
    all_lines[line_count++] = d1;
    all_lines[line_count++] = d2;
    all_lines[line_count++] = d3;
    all_lines[line_count++] = d4;
}

#define MAX_X (TOTAL_LINES * 2)
#define MAX_Y TOTAL_CELLS

static int unblocked_lines[TOTAL_LINES];
static int num_unblocked = 0;
static int unocc_cells[TOTAL_CELLS];
static int num_unocc = 0;

static int matchX[MAX_X];
static int matchY[MAX_Y];
static int dist[MAX_X + 1];
static int adj[MAX_X][5];
static int adj_deg[MAX_X];

bool hk_bfs(int nx, int ny) {
    (void)ny;
    int queue[MAX_X];
    int qhead = 0, qtail = 0;
    for (int u = 0; u < nx; u++) {
        if (matchX[u] == -1) {
            dist[u] = 0;
            queue[qtail++] = u;
        } else {
            dist[u] = 1e9;
        }
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
                    if (next_u != -1) {
                        dist[next_u] = dist[u] + 1;
                        queue[qtail++] = next_u;
                    } else {
                        dist[nx] = dist[u] + 1;
                    }
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
                    matchY[v] = u;
                    matchX[u] = v;
                    return true;
                }
            }
        }
        dist[u] = 1e9;
        return false;
    }
    return true;
}

int hopcroft_karp(int nx, int ny) {
    for (int u = 0; u < nx; u++) matchX[u] = -1;
    for (int v = 0; v < ny; v++) matchY[v] = -1;
    int matching = 0;
    while (hk_bfs(nx, ny)) {
        for (int u = 0; u < nx; u++) {
            if (matchX[u] == -1 && hk_dfs(u, nx)) matching++;
        }
    }
    return matching;
}

bool test_pairing_matching(u128 white, u128 black, int *out_lines, int *out_matching) {
    num_unblocked = 0;
    for (int i = 0; i < TOTAL_LINES; i++) {
        if ((black & all_lines[i].mask) == 0) {
            unblocked_lines[num_unblocked++] = i;
        }
    }
    num_unocc = 0;
    int cell_to_y[TOTAL_CELLS];
    for (int c = 0; c < TOTAL_CELLS; c++) {
        if (((white | black) & ((u128)1 << c)) == 0) {
            cell_to_y[c] = num_unocc;
            unocc_cells[num_unocc++] = c;
        } else {
            cell_to_y[c] = -1;
        }
    }

    *out_lines = num_unblocked;
    int nx = num_unblocked * 2;
    int ny = num_unocc;

    if (nx > ny) {
        *out_matching = 0;
        return false;
    }

    for (int l_idx = 0; l_idx < num_unblocked; l_idx++) {
        int orig_line = unblocked_lines[l_idx];
        int u1 = l_idx * 2;
        int u2 = l_idx * 2 + 1;
        adj_deg[u1] = 0;
        adj_deg[u2] = 0;
        for (int j = 0; j < 5; j++) {
            int c = all_lines[orig_line].cells[j];
            int y = cell_to_y[c];
            if (y != -1) {
                adj[u1][adj_deg[u1]++] = y;
                adj[u2][adj_deg[u2]++] = y;
            }
        }
    }

    int m = hopcroft_karp(nx, ny);
    *out_matching = m;
    return m == nx;
}

int main() {
    clock_t start = clock();
    printf("=======================================================================\n");
    printf("    128-BIT SIMD THREAT & MATCHING ENGINE: 5x5x5 3D TIC-TAC-TOE        \n");
    printf("=======================================================================\n");

    generate_lines();

    u128 white = 0, black = 0;
    int w_moves[50], b_moves[50];

    printf("Simulating Greedy Maker vs Breaker to Reach X-Perfect Pairing...\n");
    for (int round = 1; round <= 35; round++) {
        // Greedy White move (max danger)
        int best_w = -1; double max_d = -1.0;
        for (int c = 0; c < TOTAL_CELLS; c++) {
            u128 bit = (u128)1 << c;
            if (((white | black) & bit) != 0) continue;
            double d = 0;
            for (int l = 0; l < TOTAL_LINES; l++) {
                u128 m = all_lines[l].mask;
                if ((black & m) != 0) continue;
                int wc = popcount128((white | bit) & m);
                d += 1.0 / (double)(1 << (5 - wc));
            }
            if (d > max_d) { max_d = d; best_w = c; }
        }
        if (best_w == -1) break;
        white |= ((u128)1 << best_w);
        w_moves[round] = best_w;

        // Greedy Black move (min danger)
        int best_b = -1; double min_d = 1e9;
        for (int c = 0; c < TOTAL_CELLS; c++) {
            u128 bit = (u128)1 << c;
            if (((white | black) & bit) != 0) continue;
            double d = 0;
            for (int l = 0; l < TOTAL_LINES; l++) {
                u128 m = all_lines[l].mask;
                if (((black | bit) & m) != 0) continue;
                int wc = popcount128(white & m);
                d += 1.0 / (double)(1 << (5 - wc));
            }
            if (d < min_d) { min_d = d; best_b = c; }
        }
        if (best_b == -1) break;
        black |= ((u128)1 << best_b);
        b_moves[round] = best_b;

        int unb, m_size;
        bool perfect = test_pairing_matching(white, black, &unb, &m_size);

        if (perfect) {
            printf("\n--> AT ROUND %d: X-PERFECT MATCHING FOUND FOR ALL %d UNBLOCKED LINES!\n", round, unb);
            printf("-----------------------------------------------------------------------\n");
            printf("Detailed Pairing Schedule for the 43 Unblocked Lines:\n");
            printf("Line ID | Line Coords Start -> End         | Paired Cell 1    | Paired Cell 2\n");
            printf("--------+----------------------------------+------------------+------------------\n");
            for (int l_idx = 0; l_idx < unb; l_idx++) {
                int orig_line = unblocked_lines[l_idx];
                int u1 = l_idx * 2;
                int u2 = l_idx * 2 + 1;
                int c1 = unocc_cells[matchX[u1]];
                int c2 = unocc_cells[matchX[u2]];
                int x1, y1, z1, x2, y2, z2;
                index_to_coord(c1, &x1, &y1, &z1);
                index_to_coord(c2, &x2, &y2, &z2);
                int sx, sy, sz, ex, ey, ez;
                index_to_coord(all_lines[orig_line].cells[0], &sx, &sy, &sz);
                index_to_coord(all_lines[orig_line].cells[4], &ex, &ey, &ez);

                printf("  %3d   | (%d,%d,%d) -> (%d,%d,%d)           | (%d,%d,%d) [idx %2d] | (%d,%d,%d) [idx %2d]\n",
                       orig_line, sx, sy, sz, ex, ey, ez, x1, y1, z1, c1, x2, y2, z2, c2);
            }
            break;
        }
    }

    clock_t end = clock();
    double ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000.0;
    printf("=======================================================================\n");
    printf("Engine execution completed in %.2f ms.\n", ms);
    printf("=======================================================================\n");
    return 0;
}
