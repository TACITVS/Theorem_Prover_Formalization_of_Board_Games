/**
 * test_hall_deficiency.c - Verification of Hall Deficiency Contraction in 5x5x5 Qubic
 * 
 * Computes exact Hall deficiency Delta(t) = 2*|L_B| - nu(G) at each round t,
 * where nu(G) is the maximum bipartite matching size between 2*L_B and free cells F.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#define TOTAL_CELLS 125
#define TOTAL_LINES 109

typedef unsigned __int128 u128;

typedef struct {
    int cells[5];
    u128 mask;
} Line5;

static Line5 all_lines[TOTAL_LINES];
static int line_count = 0;

static inline int cell_index(int x, int y, int z) { return z * 25 + y * 5 + x; }

void generate_lines() {
    line_count = 0;
    for (int z = 0; z < 5; z++) for (int y = 0; y < 5; y++) {
        Line5 l; l.mask = 0;
        for (int x = 0; x < 5; x++) { int c = cell_index(x, y, z); l.cells[x] = c; l.mask |= ((u128)1 << c); }
        all_lines[line_count++] = l;
    }
    for (int z = 0; z < 5; z++) for (int x = 0; x < 5; x++) {
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
            int c1 = cell_index(i, i, z), c2 = cell_index(4 - i, i, z);
            l1.cells[i] = c1; l1.mask |= ((u128)1 << c1);
            l2.cells[i] = c2; l2.mask |= ((u128)1 << c2);
        }
        all_lines[line_count++] = l1; all_lines[line_count++] = l2;
    }
    for (int y = 0; y < 5; y++) {
        Line5 l1, l2; l1.mask = 0; l2.mask = 0;
        for (int i = 0; i < 5; i++) {
            int c1 = cell_index(i, y, i), c2 = cell_index(4 - i, y, i);
            l1.cells[i] = c1; l1.mask |= ((u128)1 << c1);
            l2.cells[i] = c2; l2.mask |= ((u128)1 << c2);
        }
        all_lines[line_count++] = l1; all_lines[line_count++] = l2;
    }
    for (int x = 0; x < 5; x++) {
        Line5 l1, l2; l1.mask = 0; l2.mask = 0;
        for (int i = 0; i < 5; i++) {
            int c1 = cell_index(x, i, i), c2 = cell_index(x, 4 - i, i);
            l1.cells[i] = c1; l1.mask |= ((u128)1 << c1);
            l2.cells[i] = c2; l2.mask |= ((u128)1 << c2);
        }
        all_lines[line_count++] = l1; all_lines[line_count++] = l2;
    }
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

// Bipartite Matching via Hopcroft-Karp
#define MAX_U 220
#define MAX_V 125
static int adj[MAX_U][5];
static int deg_u[MAX_U];
static int pair_u[MAX_U], pair_v[MAX_V], dist[MAX_U];

bool bfs(int num_u) {
    int queue[MAX_U], qhead = 0, qtail = 0;
    for (int u = 0; u < num_u; u++) {
        if (pair_u[u] == -1) { dist[u] = 0; queue[qtail++] = u; }
        else dist[u] = -1;
    }
    int d_inf = -1;
    while (qhead < qtail) {
        int u = queue[qhead++];
        if (d_inf != -1 && dist[u] >= d_inf) continue;
        for (int i = 0; i < deg_u[u]; i++) {
            int v = adj[u][i];
            int next_u = pair_v[v];
            if (next_u == -1) {
                if (d_inf == -1) d_inf = dist[u] + 1;
            } else if (dist[next_u] == -1) {
                dist[next_u] = dist[u] + 1;
                queue[qtail++] = next_u;
            }
        }
    }
    return d_inf != -1;
}

bool dfs(int u) {
    for (int i = 0; i < deg_u[u]; i++) {
        int v = adj[u][i];
        int next_u = pair_v[v];
        if (next_u == -1 || (dist[next_u] == dist[u] + 1 && dfs(next_u))) {
            pair_u[u] = v;
            pair_v[v] = u;
            return true;
        }
    }
    dist[u] = -1;
    return false;
}

int max_bipartite_matching(int num_u, int num_v) {
    for (int u = 0; u < num_u; u++) pair_u[u] = -1;
    for (int v = 0; v < num_v; v++) pair_v[v] = -1;
    int matching = 0;
    while (bfs(num_u)) {
        for (int u = 0; u < num_u; u++) {
            if (pair_u[u] == -1 && dfs(u)) matching++;
        }
    }
    return matching;
}

int compute_hall_deficiency(u128 white, u128 black, int *out_unblocked, int *out_demand, int *out_matching) {
    int unblocked_lines[TOTAL_LINES], num_unb = 0;
    for (int l = 0; l < TOTAL_LINES; l++) {
        if ((black & all_lines[l].mask) == 0) unblocked_lines[num_unb++] = l;
    }

    int free_cells[TOTAL_CELLS], cell_to_v[TOTAL_CELLS], num_free = 0;
    for (int c = 0; c < TOTAL_CELLS; c++) {
        if (((white | black) & ((u128)1 << c)) == 0) {
            cell_to_v[c] = num_free;
            free_cells[num_free++] = c;
        } else {
            cell_to_v[c] = -1;
        }
    }

    int num_u = num_unb * 2;
    for (int i = 0; i < num_unb; i++) {
        int l = unblocked_lines[i];
        int u1 = 2 * i, u2 = 2 * i + 1;
        deg_u[u1] = 0; deg_u[u2] = 0;
        for (int k = 0; k < 5; k++) {
            int c = all_lines[l].cells[k];
            int v = cell_to_v[c];
            if (v != -1) {
                adj[u1][deg_u[u1]++] = v;
                adj[u2][deg_u[u2]++] = v;
            }
        }
    }

    int m = max_bipartite_matching(num_u, num_free);
    int demand = num_u;
    int deficiency = demand - m;

    if (out_unblocked) *out_unblocked = num_unb;
    if (out_demand) *out_demand = demand;
    if (out_matching) *out_matching = m;
    return deficiency;
}

int pick_black_elim(u128 white, u128 black) {
    // Tier 1: Immediate threat block
    for (int l = 0; l < TOTAL_LINES; l++) {
        u128 m = all_lines[l].mask;
        if ((black & m) == 0 && __builtin_popcountll((uint64_t)(white & m)) + __builtin_popcountll((uint64_t)((white & m) >> 64)) == 4) {
            u128 empty_mask = m & ~white;
            int c = __builtin_ctzll((uint64_t)empty_mask);
            if (empty_mask >> 64) c = 64 + __builtin_ctzll((uint64_t)(empty_mask >> 64));
            return c;
        }
    }
    // Tier 2: Fork block (cells intersecting >= 2 lines with 3 white stones)
    for (int c = 0; c < TOTAL_CELLS; c++) {
        u128 bit = (u128)1 << c;
        if (((white | black) & bit) != 0) continue;
        int count_3 = 0;
        for (int l = 0; l < TOTAL_LINES; l++) {
            u128 m = all_lines[l].mask;
            if ((m & bit) != 0 && (black & m) == 0) {
                int wc = __builtin_popcountll((uint64_t)(white & m)) + __builtin_popcountll((uint64_t)((white & m) >> 64));
                if (wc == 3) count_3++;
            }
        }
        if (count_3 >= 2) return c;
    }
    // Tier 3: Maximize unblocked lines eliminated
    int best_c = -1, max_elim = -1;
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

int main() {
    generate_lines();
    printf("=======================================================================\n");
    printf("     HALL DEFICIENCY CONTRACTION TRAJECTORY (White Opens Center)       \n");
    printf("=======================================================================\n");

    u128 white = 0, black = 0;
    int unb, demand, m;
    int init_def = compute_hall_deficiency(white, black, &unb, &demand, &m);
    printf("Initial State (Round 0): Unblocked=%3d | Demand=%3d | Matched=%3d | Delta=%3d\n",
           unb, demand, m, init_def);

    // White opens at Center (62)
    int white_moves[] = { 62, 33, 4, 24, 9, 57, 72, 48, 124, 20, 8, 34, 32, 109, 83, 108, 107, 122, 22 };

    for (int round = 1; round <= 19; round++) {
        int w = white_moves[round - 1];
        white |= ((u128)1 << w);

        int b = pick_black_elim(white, black);
        black |= ((u128)1 << b);

        int def = compute_hall_deficiency(white, black, &unb, &demand, &m);
        printf("Round %2d: W=%3d, B=%3d | Unblocked=%2d | Demand=%2d | Matched=%2d | Delta=%2d  %s\n",
               round, w, b, unb, demand, m, def, def == 0 ? ">>> MATCHED! DELTA = 0 <<<" : "");
        if (def == 0) break;
    }
    return 0;
}
