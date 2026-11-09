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

int test_matching_state(u128 white, u128 black, int *unb_lines, int *unocc) {
    int unblocked[TOTAL_LINES], num_unb = 0;
    for (int i = 0; i < TOTAL_LINES; i++) {
        if ((black & all_lines[i].mask) == 0) unblocked[num_unb++] = i;
    }
    *unb_lines = num_unb;

    int cell_to_y[TOTAL_CELLS], num_u = 0;
    for (int c = 0; c < TOTAL_CELLS; c++) {
        if (((white | black) & ((u128)1 << c)) == 0) cell_to_y[c] = num_u++;
        else cell_to_y[c] = -1;
    }
    *unocc = num_u;

    int nx = num_unb * 2;
    int ny = num_u;
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
    return hopcroft_karp(nx, ny);
}

int main() {
    generate_lines();
    printf("Testing early rounds for X-perfect matching...\n");

    // Test a greedy sequence of moves
    u128 white = 0, black = 0;
    int test_moves[] = {
        62, 0, 24, 100, 124, 31, 43, 81, 93, // 9 high degree moves
        12, 52, 60, 64, 72, 112,              // 6 face centers
        37, 57                                // 2 inner axes
    };

    // Suppose Black plays these stones, while White plays outside them
    for (int step = 0; step < 17; step++) {
        black |= ((u128)1 << test_moves[step]);
        // White plays some dummy cell not in test_moves
        int dummy = 1 + step * 2;
        while (((white | black) & ((u128)1 << dummy)) != 0) dummy++;
        white |= ((u128)1 << dummy);

        int unb, unocc;
        int m = test_matching_state(white, black, &unb, &unocc);
        printf("Step %2d: Black stones = %2d | Unblocked lines = %2d (Demand %2d) | Empty cells = %3d | Matched = %2d/%2d %s\n",
               step + 1, step + 1, unb, unb * 2, unocc, m, unb * 2, (m == unb * 2) ? "[PERFECT MATCHING!]" : "");
    }
    return 0;
}
