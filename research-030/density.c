/* Research 030: how dense can a valid binary code region of the 5x5x5 cube be?
 *
 * A code region is a cell set C together with a set S of cube lines, each
 * meeting C in >= 2 cells; its fragments are l ∩ C. It is *valid* when the
 * GF(2) span of the fragments has two disjoint information sets inside C
 * (exact Edmonds matroid partition). Research 026 proved 6L <= 5F for every
 * pairing/potential region; if valid code regions obey the same bound, no
 * hybrid regional certificate exists at the empty board (6*109 > 5*125).
 *
 * This program *searches* for a counterexample: it maximises 6L - 5F over
 * valid regions by annealing (toggle cells, toggle lines), with a penalty
 * for the partition deficiency. A positive maximum would refute the lemma; a
 * non-positive one is evidence only. Checkpoints the best region per seed
 * every 30 s; progress every 5 s.
 *
 * Build: gcc -O3 -march=native -fopenmp density.c -o density.exe
 */
#include <omp.h>
#include "../research-029/hybrid_core.h"

typedef struct { int score, L, F, def; } DEv;

static int fmin_list[8] = {2, 6, 10, 15, 20, 30, 45, 65};
static __thread int fmin_cur = 2;

static DEv dens_eval(const uint8_t *inC, const uint8_t *inS) {
    h128 rows[HNL];
    int nr = 0, F = 0, cells[HN], nc = 0;
    for (int c = 0; c < HN; c++) if (inC[c]) { F++; cells[nc++] = c; }
    for (int l = 0; l < HNL; l++) {
        if (!inS[l]) continue;
        h128 m = 0;
        int k = 0;
        for (int t = 0; t < 5; t++) if (inC[h_lines[l][t]]) { m |= (h128)1 << h_lines[l][t]; k++; }
        if (k >= 2) rows[nr++] = m;
    }
    int r = h_rank(rows, nr);
    h128 col[HN];
    memset(col, 0, sizeof col);
    for (int i = 0; i < nr; i++)
        for (int k = 0; k < nc; k++) if ((rows[i] >> cells[k]) & 1) col[cells[k]] |= (h128)1 << i;
    int def = 2 * r - h_partition(cells, nc, col, r);
    DEv e = {6 * nr - 5 * F - 12 * def - (F < fmin_cur ? 20 * (fmin_cur - F) : 0), nr, F, def};
    return e;
}

static volatile int stop_flag = 0;

int main(int argc, char **argv) {
    int seeds = 22, threads = 22;
    double seconds = 120;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--seeds")) seeds = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--threads")) threads = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--seconds")) seconds = atof(argv[++i]);
    }
    h_init();
    if (system("mkdir density_ckpt 2>nul")) {}
    printf("density search: maximise 6L - 5F over valid GF(2) code regions; %d seeds x %.0fs on %d threads\n",
           seeds, seconds, threads);
    fflush(stdout);
    int best_all = -1 << 30;
    double t0 = omp_get_wtime(), last = t0;
    long long evals = 0;
    omp_set_num_threads(threads);
#pragma omp parallel for schedule(dynamic, 1)
    for (int sd = 0; sd < seeds; sd++) {
        uint8_t inC[HN] = {0}, inS[HNL], bC[HN], bS[HNL];
        fmin_cur = fmin_list[sd % 8];
        for (int l = 0; l < HNL; l++) inS[l] = 1;
        uint64_t rng = 0x5DEECE66Dull * (uint64_t)(sd + 7) + 11;
        /* starts: random sets (even seeds) or axis boxes a x b x c (odd seeds) */
        if (sd % 2 == 0) {
            for (int k = 0; k < 10 + 3 * sd; k++) inC[h_xs(&rng) % HN] = 1;
        } else {
            int a = 2 + (int)(h_xs(&rng) % 4), b = 2 + (int)(h_xs(&rng) % 4), c = 1 + (int)(h_xs(&rng) % 5);
            for (int x = 0; x < a; x++) for (int y = 0; y < b; y++) for (int z = 0; z < c; z++) inC[x + 5 * y + 25 * z] = 1;
        }
        DEv cur = dens_eval(inC, inS), best = {-1 << 30, 0, 0, 0};
        memcpy(bC, inC, sizeof inC); memcpy(bS, inS, sizeof inS);
        double ts = omp_get_wtime(), lck = ts;
        long long it = 0;
        double T = 4.0;
        while (!stop_flag) {
            it++;
            if ((it & 1023) == 0) {
                double t = omp_get_wtime();
                if (t - ts > seconds) break;
                double ph = fmod((t - ts) / (seconds / 4), 1.0);
                T = 4.0 * pow(0.1 / 4.0, ph);
#pragma omp atomic
                evals += 1024;
                if (t - lck > 30) {
                    lck = t;
                    char p[64];
                    snprintf(p, sizeof p, "density_ckpt/seed%d.txt", sd);
                    FILE *f = fopen(p, "w");
                    if (f) {
                        fprintf(f, "score %d L %d F %d def %d\ncells", best.score, best.L, best.F, best.def);
                        for (int c = 0; c < HN; c++) if (bC[c]) fprintf(f, " %d", c);
                        fprintf(f, "\nlines");
                        for (int l = 0; l < HNL; l++) if (bS[l]) fprintf(f, " %d", l);
                        fprintf(f, "\n");
                        fclose(f);
                    }
                }
                if (t - last > 5) {
#pragma omp critical
                    if (t - last > 5) {
                        last = t;
                        printf("  [%4.0fs] seed %d: current %d (L %d F %d def %d), best valid %d | overall best %d | %.0f k evals/s\n",
                               t - t0, sd, cur.score, cur.L, cur.F, cur.def, best.score, best_all, evals / (t - t0) / 1e3);
                        fflush(stdout);
                    }
                }
            }
            int which = (int)(h_xs(&rng) % 3);
            int idx;
            if (which < 2) { idx = (int)(h_xs(&rng) % HN); inC[idx] ^= 1; }
            else { idx = (int)(h_xs(&rng) % HNL); inS[idx] ^= 1; }
            DEv e = dens_eval(inC, inS);
            if (e.score >= cur.score || (h_xs(&rng) % 100000) / 100000.0 < exp((e.score - cur.score) / T)) {
                cur = e;
                if (e.def == 0 && e.F >= fmin_cur && e.score > best.score) {
                    best = e; memcpy(bC, inC, sizeof inC); memcpy(bS, inS, sizeof inS);
#pragma omp critical
                    if (best.score > best_all) best_all = best.score;
                }
            } else {
                if (which < 2) inC[idx] ^= 1; else inS[idx] ^= 1;
            }
        }
        char p[64];
        snprintf(p, sizeof p, "density_ckpt/seed%d.txt", sd);
        FILE *f = fopen(p, "w");
        if (f) {
            fprintf(f, "score %d L %d F %d def %d\ncells", best.score, best.L, best.F, best.def);
            for (int c = 0; c < HN; c++) if (bC[c]) fprintf(f, " %d", c);
            fprintf(f, "\nlines");
            for (int l = 0; l < HNL; l++) if (bS[l]) fprintf(f, " %d", l);
            fprintf(f, "\n");
            fclose(f);
        }
#pragma omp critical
        { printf("  seed %d (F>=%d) done: best valid 6L-5F = %d (L %d, F %d)\n", sd, fmin_cur, best.score, best.L, best.F); fflush(stdout); }
    }
    printf("DONE: maximum valid 6L - 5F found = %d (positive would refute the density lemma)\n", best_all);
    return 0;
}
