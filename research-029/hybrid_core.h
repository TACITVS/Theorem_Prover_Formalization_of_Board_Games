/* Position-parametrised hybrid evaluator (same rule as hybrid.c / hybrid.py),
 * for use inside the engine. Thread-safe: no mutable globals after h_init().
 * region[c] = -1 code region, j >= 0 potential region j. Score 0 means the
 * code region has two disjoint information sets and all budgets hold. */
#ifndef HYBRID_CORE_H
#define HYBRID_CORE_H
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 h128;
#define HN 125
#define HNL 109
#define HMAXR 64

static int h_lines[HNL][5];
static int h_nbr[HN][HN], h_nnbr[HN];
static const int H_UNITS[6] = {0, 16, 8, 4, 2, 1};

typedef struct { uint8_t occ[HN]; int live[HNL], nlive; } HPos;

static int h_cmp_line(const void *a, const void *b) {
    const int *x = a, *y = b;
    for (int i = 0; i < 5; i++) if (x[i] != y[i]) return x[i] - y[i];
    return 0;
}
static int h_cmp_int(const void *a, const void *b) { return *(const int *)a - *(const int *)b; }

static void h_init(void) {
    int n = 0;
    for (int s = 0; s < HN; s++) {
        int x = s % 5, y = s / 5 % 5, z = s / 25;
        for (int dx = -1; dx <= 1; dx++) for (int dy = -1; dy <= 1; dy++) for (int dz = -1; dz <= 1; dz++) {
            if (!dx && !dy && !dz) continue;
            if (dx < 0 || (dx == 0 && (dy < 0 || (dy == 0 && dz < 0)))) continue;
            int a = x - dx, b = y - dy, c = z - dz;
            if (a >= 0 && a <= 4 && b >= 0 && b <= 4 && c >= 0 && c <= 4) continue;
            int ok = 1, cs[5];
            for (int t = 0; t < 5; t++) {
                a = x + t * dx; b = y + t * dy; c = z + t * dz;
                if (a < 0 || a > 4 || b < 0 || b > 4 || c < 0 || c > 4) { ok = 0; break; }
                cs[t] = a + 5 * b + 25 * c;
            }
            if (!ok) continue;
            qsort(cs, 5, sizeof(int), h_cmp_int);
            memcpy(h_lines[n++], cs, sizeof cs);
        }
    }
    qsort(h_lines, HNL, sizeof h_lines[0], h_cmp_line);
    for (int l = 0; l < HNL; l++)
        for (int a = 0; a < 5; a++) for (int b = 0; b < 5; b++) if (a != b)
            h_nbr[h_lines[l][a]][h_nnbr[h_lines[l][a]]++] = h_lines[l][b];
}

/* board[c]: 0 empty, 1 white, 2 black */
static void h_pos(HPos *p, const uint8_t *board) {
    p->nlive = 0;
    for (int c = 0; c < HN; c++) p->occ[c] = board[c] != 0;
    for (int l = 0; l < HNL; l++) {
        int ok = 1;
        for (int t = 0; t < 5; t++) if (board[h_lines[l][t]] == 2) ok = 0;
        if (ok) p->live[p->nlive++] = l;
    }
}

static inline int h_top(h128 v) {
    uint64_t hi = (uint64_t)(v >> 64), lo = (uint64_t)v;
    return hi ? 127 - __builtin_clzll(hi) : 63 - __builtin_clzll(lo);
}

static int h_rank(const h128 *rows, int n) {
    h128 piv[128] = {0};
    int r = 0;
    for (int i = 0; i < n; i++) {
        h128 v = rows[i];
        while (v) { int t = h_top(v); if (piv[t]) v ^= piv[t]; else { piv[t] = v; r++; break; } }
    }
    return r;
}

typedef struct { h128 vec[128], cmb[128]; uint8_t has[128]; int elems[128], n; } HBasis;

static void h_basis(HBasis *B, const int *el, int n, const h128 *col) {
    memset(B->has, 0, sizeof B->has);
    B->n = n;
    for (int i = 0; i < n; i++) {
        B->elems[i] = el[i];
        h128 v = col[el[i]], cb = (h128)1 << i;
        while (v) {
            int t = h_top(v);
            if (B->has[t]) { v ^= B->vec[t]; cb ^= B->cmb[t]; }
            else { B->has[t] = 1; B->vec[t] = v; B->cmb[t] = cb; break; }
        }
    }
}

static int h_circuit(const HBasis *B, h128 v, h128 *combo) {
    h128 cb = 0;
    while (v) { int t = h_top(v); if (!B->has[t]) return 1; v ^= B->vec[t]; cb ^= B->cmb[t]; }
    *combo = cb;
    return 0;
}

static int h_partition(const int *cells, int nc, const h128 *col, int r) {
    int sets[2][128], ns[2] = {0, 0}, where[HN];
    for (int i = 0; i < HN; i++) where[i] = -1;
    for (int si = 0; si < nc; si++) {
        int s = cells[si];
        if (!col[s]) continue;
        HBasis B[2];
        h_basis(&B[0], sets[0], ns[0], col);
        h_basis(&B[1], sets[1], ns[1], col);
        int px[HN], pj[HN], q[HN], qh = 0, qt = 0, sx = -1, sj = -1;
        uint8_t seen[HN] = {0};
        for (int i = 0; i < HN; i++) px[i] = -1;
        seen[s] = 1; q[qt++] = s;
        while (qh < qt && sx < 0) {
            int x = q[qh++];
            for (int j = 0; j < 2; j++) {
                if (where[x] == j) continue;
                h128 combo;
                if (h_circuit(&B[j], col[x], &combo)) { sx = x; sj = j; break; }
                for (int k = 0; k < B[j].n; k++)
                    if ((combo >> k) & 1) {
                        int y = B[j].elems[k];
                        if (!seen[y]) { seen[y] = 1; px[y] = x; pj[y] = j; q[qt++] = y; }
                    }
            }
        }
        if (sx < 0) continue;
        int mx[HN], mj[HN], nm = 0, x = sx;
        mx[nm] = sx; mj[nm++] = sj;
        while (px[x] >= 0) { mx[nm] = px[x]; mj[nm++] = pj[x]; x = px[x]; }
        for (int k = 0; k < nm; k++) {
            int e = mx[k], to = mj[k], old = where[e];
            if (old >= 0)
                for (int t = 0; t < ns[old]; t++)
                    if (sets[old][t] == e) { memmove(&sets[old][t], &sets[old][t + 1], (size_t)(ns[old] - t - 1) * sizeof(int)); ns[old]--; break; }
            sets[to][ns[to]++] = e;
            where[e] = to;
        }
        if (ns[0] == r && ns[1] == r) break;
    }
    return ns[0] + ns[1];
}

static int h_evaluate(const HPos *p, const int *region, int m, int *short_out) {
    int budget[HMAXR] = {0}, nrows = 0, penalty = 0, nopt = 0;
    h128 rows[HNL], om[HNL];
    int ou[HNL], oj[HNL];
    for (int li = 0; li < p->nlive; li++) {
        const int *lc = h_lines[p->live[li]];
        h128 cm = 0;
        int cc = 0, pr[5], pc[5], np = 0;
        for (int t = 0; t < 5; t++) {
            int c = lc[t];
            if (p->occ[c]) continue;
            int rg = region[c];
            if (rg < 0) { cm |= (h128)1 << c; cc++; continue; }
            int k = 0;
            while (k < np && pr[k] != rg) k++;
            if (k == np) { pr[np] = rg; pc[np++] = 0; }
            pc[k]++;
        }
        int bj = -1, bc = 0;
        for (int k = 0; k < np; k++) if (pc[k] > bc) { bc = pc[k]; bj = pr[k]; }
        if (cc < 2) { if (bj < 0) { penalty += 100; continue; } budget[bj] += H_UNITS[bc]; }
        else if (bj >= 0 && bc >= 3) { ou[nopt] = H_UNITS[bc]; oj[nopt] = bj; om[nopt++] = cm; }
        else rows[nrows++] = cm;
    }
    for (int u = 1; u <= 4; u <<= 1)
        for (int k = 0; k < nopt; k++) {
            if (ou[k] != u) continue;
            if (budget[oj[k]] + u <= 15) budget[oj[k]] += u; else rows[nrows++] = om[k];
        }
    for (int j = 0; j < m; j++) if (budget[j] > 15) penalty += 50 * (budget[j] - 15);
    int cells[HN], nc = 0;
    for (int c = 0; c < HN; c++) if (!p->occ[c] && region[c] < 0) cells[nc++] = c;
    int rank = h_rank(rows, nrows), sh = 2 * rank - nc;
    if (penalty == 0) {
        h128 col[HN];
        memset(col, 0, sizeof col);
        for (int i = 0; i < nrows; i++)
            for (int k = 0; k < nc; k++) if ((rows[i] >> cells[k]) & 1) col[cells[k]] |= (h128)1 << i;
        sh = 2 * rank - h_partition(cells, nc, col, rank);
    }
    if (short_out) *short_out = sh;
    return (sh > 0 ? sh : 0) + penalty;
}

static uint64_t h_xs(uint64_t *s) { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; return *s; }

/* Local annealing from `region` for `steps` evaluations; region <- best found. */
static int h_anneal(const HPos *p, int *region, int m, long steps, uint64_t *rng, double T0, double T1) {
    int freec[HN], nf = 0, best_r[HN];
    for (int c = 0; c < HN; c++) if (!p->occ[c]) freec[nf++] = c;
    int cur = h_evaluate(p, region, m, NULL), best = cur;
    memcpy(best_r, region, sizeof best_r);
    for (long it = 0; it < steps && best > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)steps);
        int c = freec[h_xs(rng) % (uint64_t)nf], old = region[c], nw;
        double r = (h_xs(rng) % 10000) / 10000.0;
        if (r < 0.3) nw = -1;
        else if (r < 0.75) {
            int cand[HN], k = 0;
            for (int q = 0; q < h_nnbr[c]; q++) { int y = h_nbr[c][q]; if (region[y] >= 0) cand[k++] = region[y]; }
            nw = k ? cand[h_xs(rng) % (uint64_t)k] : (int)(h_xs(rng) % (uint64_t)m);
        } else nw = (int)(h_xs(rng) % (uint64_t)m);
        if (nw == old) continue;
        region[c] = nw;
        int sc = h_evaluate(p, region, m, NULL);
        if (sc <= cur || (h_xs(rng) % 100000) / 100000.0 < exp((cur - sc) / T)) {
            cur = sc;
            if (sc < best) { best = sc; memcpy(best_r, region, sizeof best_r); }
        } else region[c] = old;
    }
    memcpy(region, best_r, sizeof best_r);
    return best;
}

static int h_load_layout(const char *path, int *region) {
    FILE *f = fopen(path, "r");
    if (!f) return 0;
    int sc;
    if (fscanf(f, "score %d", &sc) != 1) rewind(f);
    for (int c = 0; c < HN; c++) if (fscanf(f, "%d", &region[c]) != 1) { fclose(f); return 0; }
    fclose(f);
    return 1;
}
#endif
