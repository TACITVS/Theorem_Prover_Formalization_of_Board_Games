/* Research 029: fast exact search for hybrid regional certificates (C + OpenMP).
 *
 * Same model and the same evaluation rule as hybrid.py (the reference):
 *   region[c] = -1 for the code region, j >= 0 for potential region j.
 *   Live lines (no Black stone) are assigned greedily. A line with < 2 free
 *   cells in the code region goes to the potential region holding most of its
 *   cells. Other lines go to a potential region (fragment >= 3 cells) while
 *   that region's budget sum 2^(5-s) <= 15 allows, cheapest first. The rest
 *   stay in the code region.
 *   score = max(0, 2*rank - |I0| - |I1|) + penalties, where I0, I1 is a
 *   maximum pair of disjoint independent sets of the code region's column
 *   matroid over GF(2) (Edmonds matroid partition). Score 0 means the code
 *   region has two disjoint information sets and every potential region is
 *   within budget.
 *
 * One annealing run per thread. The best layout of each seed is checkpointed
 * every 30 s to <ckdir>/seed<k>.txt and resumed automatically. Progress is
 * printed every 5 s. This is a search, not a proof.
 *
 * Build: gcc -O3 -march=native -fopenmp hybrid.c -o hybrid.exe
 */
#include <math.h>
#include <omp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;
#define N 125
#define NL 109
#define MAXR 64

static int line_cells[NL][5];          /* lines sorted lexicographically, cells ascending */
static uint8_t occupied[N], is_black[N];
static int live[NL], nlive;
static int nbr[N][N], nnbr[N];
static const int UNITS[6] = {0, 16, 8, 4, 2, 1};
static volatile sig_atomic_t stop_flag = 0;
static void on_sigint(int s) { (void)s; stop_flag = 1; }

static int cmp_line(const void *a, const void *b) {
    const int *x = a, *y = b;
    for (int i = 0; i < 5; i++) if (x[i] != y[i]) return x[i] - y[i];
    return 0;
}
static int cmp_int(const void *a, const void *b) { return *(const int *)a - *(const int *)b; }

static void init_lines(void) {
    int n = 0;
    for (int s = 0; s < N; s++) {
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
            qsort(cs, 5, sizeof(int), cmp_int);
            memcpy(line_cells[n++], cs, sizeof cs);
        }
    }
    if (n != NL) { fprintf(stderr, "expected 109 lines, got %d\n", n); exit(1); }
    qsort(line_cells, NL, sizeof line_cells[0], cmp_line);
}

static inline int top_bit(u128 v) {
    uint64_t hi = (uint64_t)(v >> 64), lo = (uint64_t)v;
    return hi ? 127 - __builtin_clzll(hi) : 63 - __builtin_clzll(lo);
}

static int gf2_rank(u128 *rows, int n) {
    u128 piv[128] = {0};
    int r = 0;
    for (int i = 0; i < n; i++) {
        u128 v = rows[i];
        while (v) {
            int t = top_bit(v);
            if (piv[t]) v ^= piv[t]; else { piv[t] = v; r++; break; }
        }
    }
    return r;
}

/* ------------------------------------------------ matroid partition (2 copies) */
typedef struct { u128 vec[128], cmb[128]; uint8_t has[128]; int elems[128], n; } Basis;

static void basis_build(Basis *B, const int *elems, int n, const u128 *col) {
    memset(B->has, 0, sizeof B->has);
    B->n = n;
    for (int i = 0; i < n; i++) {
        B->elems[i] = elems[i];
        u128 v = col[elems[i]], cb = (u128)1 << i;
        while (v) {
            int t = top_bit(v);
            if (B->has[t]) { v ^= B->vec[t]; cb ^= B->cmb[t]; }
            else { B->has[t] = 1; B->vec[t] = v; B->cmb[t] = cb; break; }
        }
    }
}

/* returns 1 if v is independent of B; else 0 and *combo = elements expressing v */
static int basis_circuit(const Basis *B, u128 v, u128 *combo) {
    u128 cb = 0;
    while (v) {
        int t = top_bit(v);
        if (!B->has[t]) return 1;
        v ^= B->vec[t]; cb ^= B->cmb[t];
    }
    *combo = cb;
    return 0;
}

/* max |I0|+|I1| over disjoint independent sets; cells: code cells (ascending). */
static int partition(const int *cells, int nc, const u128 *col, int r) {
    int sets[2][128], ns[2] = {0, 0};
    int where[N];
    for (int i = 0; i < N; i++) where[i] = -1;
    for (int si = 0; si < nc; si++) {
        int s = cells[si];
        if (!col[s]) continue;
        Basis B[2];
        basis_build(&B[0], sets[0], ns[0], col);
        basis_build(&B[1], sets[1], ns[1], col);
        int par_x[N], par_j[N];
        uint8_t seen[N] = {0};
        for (int i = 0; i < N; i++) par_x[i] = -1;
        int queue[N], qh = 0, qt = 0, sink_x = -1, sink_j = -1;
        seen[s] = 1; queue[qt++] = s;
        while (qh < qt && sink_x < 0) {
            int x = queue[qh++];
            for (int j = 0; j < 2; j++) {
                if (where[x] == j) continue;
                u128 combo;
                if (basis_circuit(&B[j], col[x], &combo)) { sink_x = x; sink_j = j; break; }
                for (int k = 0; k < B[j].n; k++)
                    if ((combo >> k) & 1) {
                        int y = B[j].elems[k];
                        if (!seen[y]) { seen[y] = 1; par_x[y] = x; par_j[y] = j; queue[qt++] = y; }
                    }
            }
        }
        if (sink_x < 0) continue;
        int mx[N], mj[N], nm = 0, x = sink_x, j = sink_j;
        mx[nm] = x; mj[nm++] = j;
        while (par_x[x] >= 0) { int px = par_x[x], pj = par_j[x]; mx[nm] = px; mj[nm++] = pj; x = px; }
        for (int k = 0; k < nm; k++) {
            int e = mx[k], to = mj[k], old = where[e];
            if (old >= 0) {
                for (int q = 0; q < ns[old]; q++)
                    if (sets[old][q] == e) { memmove(&sets[old][q], &sets[old][q + 1], (size_t)(ns[old] - q - 1) * sizeof(int)); ns[old]--; break; }
            }
            sets[to][ns[to]++] = e;
            where[e] = to;
        }
        if (ns[0] == r && ns[1] == r) break;
    }
    return ns[0] + ns[1];
}

/* ------------------------------------------------ evaluation (mirrors hybrid.py) */
typedef struct { int short_, penalty, rank, ncode, nrows; } Eval;

static int evaluate(const int *region, int m, Eval *ev) {
    int budget[MAXR] = {0};
    u128 rows[NL];
    int nrows = 0, penalty = 0;
    int opt_u[NL], opt_j[NL], nopt = 0;
    u128 opt_mask[NL];
    for (int li = 0; li < nlive; li++) {
        const int *lc = line_cells[live[li]];
        u128 cm = 0;
        int cc = 0, preg[5], pcnt[5], np = 0;
        for (int t = 0; t < 5; t++) {
            int c = lc[t];
            if (occupied[c]) continue;
            int rg = region[c];
            if (rg < 0) { cm |= (u128)1 << c; cc++; continue; }
            int k = 0;
            while (k < np && preg[k] != rg) k++;
            if (k == np) { preg[np] = rg; pcnt[np++] = 0; }
            pcnt[k]++;
        }
        int bj = -1, bc = 0;
        for (int k = 0; k < np; k++) if (pcnt[k] > bc) { bc = pcnt[k]; bj = preg[k]; }
        if (cc < 2) {
            if (bj < 0) { penalty += 100; continue; }
            budget[bj] += UNITS[bc];
        } else if (bj >= 0 && bc >= 3) {
            opt_u[nopt] = UNITS[bc]; opt_j[nopt] = bj; opt_mask[nopt++] = cm;
        } else rows[nrows++] = cm;
    }
    for (int u = 1; u <= 4; u <<= 1)          /* cheapest first, then line order */
        for (int k = 0; k < nopt; k++) {
            if (opt_u[k] != u) continue;
            if (budget[opt_j[k]] + u <= 15) budget[opt_j[k]] += u;
            else rows[nrows++] = opt_mask[k];
        }
    for (int j = 0; j < m; j++) if (budget[j] > 15) penalty += 50 * (budget[j] - 15);
    int cells[N], nc = 0;
    for (int c = 0; c < N; c++) if (!occupied[c] && region[c] < 0) cells[nc++] = c;
    u128 tmp[NL];
    memcpy(tmp, rows, (size_t)nrows * sizeof(u128));
    int rank = gf2_rank(tmp, nrows);
    int sh = 2 * rank - nc;
    if (penalty == 0 && rank <= 128) {
        u128 col[N];
        memset(col, 0, sizeof col);
        for (int i = 0; i < nrows; i++)
            for (int k = 0; k < nc; k++) if ((rows[i] >> cells[k]) & 1) col[cells[k]] |= (u128)1 << i;
        if (nrows <= 128) sh = 2 * rank - partition(cells, nc, col, rank);
    }
    if (ev) { ev->short_ = sh; ev->penalty = penalty; ev->rank = rank; ev->ncode = nc; ev->nrows = nrows; }
    return (sh > 0 ? sh : 0) + penalty;
}

/* ------------------------------------------------ annealing */
static uint64_t xs(uint64_t *s) { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; return *s; }

static int load_layout(const char *path, int *region, int *score) {
    FILE *f = fopen(path, "r");
    if (!f) return 0;
    int sc = -1;
    if (fscanf(f, "score %d", &sc) != 1) { rewind(f); sc = -1; }
    for (int c = 0; c < N; c++) if (fscanf(f, "%d", &region[c]) != 1) { fclose(f); return 0; }
    fclose(f);
    if (score) *score = sc;
    return 1;
}

static void save_layout(const char *path, const int *region, int score) {
    char tmp[512];
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "w");
    if (!f) return;
    fprintf(f, "score %d\n", score);
    for (int c = 0; c < N; c++) fprintf(f, "%d%c", region[c], c % 25 == 24 ? '\n' : ' ');
    fclose(f);
    remove(path);
    rename(tmp, path);
}

static void parse_list(const char *s, uint8_t *mark, int black) {
    while (*s) {
        char *e;
        long v = strtol(s, &e, 10);
        if (e == s) { s++; continue; }
        if (v >= 0 && v < N) { occupied[v] = 1; if (black) is_black[v] = 1; (void)mark; }
        s = e;
    }
}

int main(int argc, char **argv) {
    int seeds = 22, m = 40, threads = 22;
    double seconds = 120;
    const char *ckdir = "hybrid_c_ckpt", *start = NULL, *white = "", *black = "", *tag = "empty";
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--seeds")) seeds = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--threads")) threads = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--seconds")) seconds = atof(argv[++i]);
        else if (!strcmp(argv[i], "--regions")) m = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--ckdir")) ckdir = argv[++i];
        else if (!strcmp(argv[i], "--start")) start = argv[++i];
        else if (!strcmp(argv[i], "--white")) white = argv[++i];
        else if (!strcmp(argv[i], "--black")) black = argv[++i];
        else if (!strcmp(argv[i], "--tag")) tag = argv[++i];
        else { fprintf(stderr, "unknown option %s\n", argv[i]); return 2; }
    }
    if (m > MAXR) m = MAXR;
    init_lines();
    parse_list(white, NULL, 0);
    parse_list(black, NULL, 1);
    for (int l = 0; l < NL; l++) {
        int ok = 1;
        for (int t = 0; t < 5; t++) if (is_black[line_cells[l][t]]) ok = 0;
        if (ok) live[nlive++] = l;
    }
    for (int l = 0; l < NL; l++)
        for (int a = 0; a < 5; a++) for (int b = 0; b < 5; b++) if (a != b) {
            int x = line_cells[l][a], y = line_cells[l][b];
            nbr[x][nnbr[x]++] = y;
        }
    signal(SIGINT, on_sigint);
    char cmd[600];
    snprintf(cmd, sizeof cmd, "mkdir %s 2>nul", ckdir);
    if (system(cmd)) { /* directory may already exist */ }

    int base_region[N];
    for (int c = 0; c < N; c++) base_region[c] = -1;
    Eval e0;
    evaluate(base_region, m, &e0);
    printf("hybrid.c [%s]: %d live lines, whole-line exact shortfall %d; %d seeds x %.0fs on %d threads "
           "(about %.1f min wall); checkpoints every 30s in %s/\n",
           tag, nlive, e0.short_, seeds, seconds, threads,
           seconds * ((seeds + threads - 1) / threads) / 60.0, ckdir);
    fflush(stdout);

    int *best_score = malloc(sizeof(int) * (size_t)seeds);
    int (*best_region)[N] = malloc(sizeof(int[N]) * (size_t)seeds);
    long long total_evals = 0;
    double t0 = omp_get_wtime(), last_print = t0;
    omp_set_num_threads(threads);
#pragma omp parallel for schedule(dynamic, 1)
    for (int sd = 0; sd < seeds; sd++) {
        char ck[512];
        snprintf(ck, sizeof ck, "%s/seed%d.txt", ckdir, sd);
        int region[N], cur, best;
        int loaded = load_layout(ck, region, NULL);
        if (!loaded && start) loaded = load_layout(start, region, NULL);
        if (!loaded) for (int c = 0; c < N; c++) region[c] = -1;
        for (int c = 0; c < N; c++) if (occupied[c]) region[c] = -1;
        cur = evaluate(region, m, NULL);
        best = cur;
        memcpy(best_region[sd], region, sizeof region);
        uint64_t rng = 0x9E3779B97F4A7C15ull * (uint64_t)(sd + 1) + 12345;
        double T = loaded ? 1.0 : 3.0, ts = omp_get_wtime(), last_ck = ts;
        long long it = 0;
        int freec[N], nf = 0;
        for (int c = 0; c < N; c++) if (!occupied[c]) freec[nf++] = c;
        while (!stop_flag) {
            it++;
            if ((it & 255) == 0) {
                double t = omp_get_wtime();
                if (t - ts > seconds) break;
                /* time-based geometric cooling, 4 reheat cycles per run */
                double phase = fmod((t - ts) / (seconds / 4.0), 1.0);
                T = (loaded ? 1.5 : 3.0) * pow(0.15 / (loaded ? 1.5 : 3.0), phase);
                if (t - last_ck > 30) { last_ck = t; save_layout(ck, best_region[sd], best); }
#pragma omp atomic
                total_evals += 256;
                if (t - last_print > 5) {
#pragma omp critical(print)
                    if (t - last_print > 5) {
                        last_print = t;
                        printf("  [%4.0fs] seed %d: current %d best %d, T %.2f | %.0f k evals/s total\n",
                               t - t0, sd, cur, best, T, total_evals / (t - t0) / 1e3);
                        fflush(stdout);
                    }
                }
            }
            int c = freec[xs(&rng) % (uint64_t)nf];
            int old = region[c], nw;
            double r = (xs(&rng) % 10000) / 10000.0;
            if (r < 0.3) nw = -1;
            else if (r < 0.75) {
                int cand[N], k = 0;
                for (int q = 0; q < nnbr[c]; q++) { int y = nbr[c][q]; if (region[y] >= 0) cand[k++] = region[y]; }
                nw = k ? cand[xs(&rng) % (uint64_t)k] : (int)(xs(&rng) % (uint64_t)m);
            } else nw = (int)(xs(&rng) % (uint64_t)m);
            if (nw == old) continue;
            region[c] = nw;
            int sc = evaluate(region, m, NULL);
            if (sc <= cur || (xs(&rng) % 100000) / 100000.0 < exp((cur - sc) / T)) {
                cur = sc;
                if (sc < best) { best = sc; memcpy(best_region[sd], region, sizeof region); }
            } else region[c] = old;
        }
        save_layout(ck, best_region[sd], best);
        best_score[sd] = best;
        Eval ev;
        evaluate(best_region[sd], m, &ev);
#pragma omp critical(print)
        {
            printf("  seed %d done: exact shortfall %d (rank %d, code cells %d, code fragments %d, penalty %d), %lld evals\n",
                   sd, ev.short_, ev.rank, ev.ncode, ev.nrows, ev.penalty, it);
            fflush(stdout);
        }
    }
    int bs = 0;
    for (int sd = 1; sd < seeds; sd++) if (best_score[sd] < best_score[bs]) bs = sd;
    char bp[512];
    snprintf(bp, sizeof bp, "%s/best.txt", ckdir);
    save_layout(bp, best_region[bs], best_score[bs]);
    printf("%s [%s]: best score %d (seed %d) -> %s; %.0f k evals/s total over %.0fs\n",
           stop_flag ? "INTERRUPTED (checkpoints saved; rerun to resume)" : "DONE", tag,
           best_score[bs], bs, bp, total_evals / (omp_get_wtime() - t0) / 1e3, omp_get_wtime() - t0);
    return 0;
}
