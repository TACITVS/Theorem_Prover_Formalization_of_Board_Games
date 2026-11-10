/* Research 029: a fast 5x5x5 Qubic engine for generating strong-play games.
 *
 * Purpose: produce test positions reached by good White play, so that Black
 * certificates (pairing, linear codes, trees) are tested where it matters.
 * The engine's output is data, never proof.
 *
 * Search: negamax alpha-beta with a transposition table, iterative deepening
 * under a per-move time limit. A forced block (the opponent has a four) does not
 * consume depth. Quiescence searches four-making moves (threat sequences) up to
 * QPLY plies. Games run in parallel with OpenMP, one game per thread.
 *
 * Checkpointing: every finished game is appended to the output file as one JSON
 * line. On Ctrl-C, unfinished games are written as "partial" records, and
 * --resume continues them from their saved move list.
 *
 * Build: gcc -O3 -march=native -fopenmp engine.c -o engine.exe
 */
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <omp.h>
#include "hybrid_core.h"

#define N 125
#define NL 109
#define WIN 100000
#define QPLY 8
#define MAXPLY 125
#define TT_BITS 20

static int line_cells[NL][5];
static int lines_of[N][13];
static int nlines_of[N];
static uint64_t zob[2][N];
static volatile sig_atomic_t stop_flag = 0;

static void on_sigint(int s) { (void)s; stop_flag = 1; }

static double now(void) { return omp_get_wtime(); }

static void init_lines(void) {
    int n = 0;
    for (int s = 0; s < N; s++) {
        int x = s % 5, y = s / 5 % 5, z = s / 25;
        for (int dx = -1; dx <= 1; dx++)
            for (int dy = -1; dy <= 1; dy++)
                for (int dz = -1; dz <= 1; dz++) {
                    if (!dx && !dy && !dz) continue;
                    /* canonical: (dx,dy,dz) lexicographically positive */
                    if (dx < 0 || (dx == 0 && (dy < 0 || (dy == 0 && dz < 0)))) continue;
                    int ok = 1, cs[5];
                    for (int t = 0; t < 5; t++) {
                        int a = x + t * dx, b = y + t * dy, c = z + t * dz;
                        if (a < 0 || a > 4 || b < 0 || b > 4 || c < 0 || c > 4) { ok = 0; break; }
                        cs[t] = a + 5 * b + 25 * c;
                    }
                    if (!ok) continue;
                    /* start must be an endpoint: previous cell out of range */
                    int a = x - dx, b = y - dy, c = z - dz;
                    if (a >= 0 && a <= 4 && b >= 0 && b <= 4 && c >= 0 && c <= 4) continue;
                    if (n >= NL) { fprintf(stderr, "too many lines\n"); exit(1); }
                    memcpy(line_cells[n++], cs, sizeof cs);
                }
    }
    if (n != NL) { fprintf(stderr, "expected 109 lines, got %d\n", n); exit(1); }
    for (int l = 0; l < NL; l++)
        for (int t = 0; t < 5; t++) {
            int c = line_cells[l][t];
            lines_of[c][nlines_of[c]++] = l;
        }
    uint64_t r = 0x9E3779B97F4A7C15ull;
    for (int s = 0; s < 2; s++)
        for (int c = 0; c < N; c++) {
            r ^= r << 13; r ^= r >> 7; r ^= r << 17;
            zob[s][c] = r * 0x2545F4914F6CDD1Dull;
        }
}

typedef struct { uint64_t key; int16_t score; int8_t depth; uint8_t flag; uint8_t move; } TTE;

typedef struct {
    uint8_t board[N];            /* 0 empty, 1 white, 2 black */
    uint8_t cnt[2][NL];
    int nstones;
    uint64_t hash;
    TTE *tt;
    long long nodes;
    double deadline;
    int timeout;
    uint64_t rng;
} Eng;

static const int VAL[5] = {0, 2, 12, 80, 600};      /* own-only line with k stones */
static const int ORD_OWN[5] = {1, 6, 40, 400, 100000};
static const int ORD_OPP[5] = {1, 5, 35, 300, 50000};

static void make(Eng *e, int c, int s) {
    e->board[c] = (uint8_t)(s + 1);
    for (int i = 0; i < nlines_of[c]; i++) e->cnt[s][lines_of[c][i]]++;
    e->hash ^= zob[s][c];
    e->nstones++;
}

static void unmake(Eng *e, int c, int s) {
    e->board[c] = 0;
    for (int i = 0; i < nlines_of[c]; i++) e->cnt[s][lines_of[c][i]]--;
    e->hash ^= zob[s][c];
    e->nstones--;
}

/* Cells completing a line for side s (s has 4, opponent 0). Returns count. */
static int fours(const Eng *e, int s, int *cells) {
    int n = 0, o = 1 - s;
    for (int l = 0; l < NL; l++)
        if (e->cnt[s][l] == 4 && e->cnt[o][l] == 0)
            for (int t = 0; t < 5; t++) {
                int c = line_cells[l][t];
                if (!e->board[c]) {
                    int dup = 0;
                    for (int k = 0; k < n; k++) dup |= cells[k] == c;
                    if (!dup) cells[n++] = c;
                    break;
                }
            }
    return n;
}

static int evaluate(const Eng *e, int s) {
    int o = 1 - s, v = 0;
    for (int l = 0; l < NL; l++) {
        if (!e->cnt[o][l]) v += VAL[e->cnt[s][l]];
        if (!e->cnt[s][l]) v -= VAL[e->cnt[o][l]];
    }
    return v + 6;   /* tempo */
}

static int cell_score(const Eng *e, int c, int s) {
    int o = 1 - s, v = 0;
    for (int i = 0; i < nlines_of[c]; i++) {
        int l = lines_of[c][i];
        if (!e->cnt[o][l]) v += ORD_OWN[e->cnt[s][l]];
        if (!e->cnt[s][l]) v += ORD_OPP[e->cnt[o][l]];
    }
    return v;
}

static int gen_moves(const Eng *e, int s, int *moves, int first) {
    int n = 0, sc[N];
    for (int c = 0; c < N; c++)
        if (!e->board[c]) { moves[n] = c; sc[n] = cell_score(e, c, s) + (c == first ? 1 << 28 : 0); n++; }
    for (int i = 1; i < n; i++) {   /* insertion sort, descending */
        int m = moves[i], v = sc[i], j = i - 1;
        while (j >= 0 && sc[j] < v) { sc[j + 1] = sc[j]; moves[j + 1] = moves[j]; j--; }
        sc[j + 1] = v; moves[j + 1] = m;
    }
    return n;
}

static int time_up(Eng *e) {
    if ((e->nodes & 4095) == 0 && (now() > e->deadline || stop_flag)) e->timeout = 1;
    return e->timeout;
}

/* Threat quiescence: side s may play moves that make a four; the opponent must block. */
static int qsearch(Eng *e, int s, int alpha, int beta, int qply, int ply) {
    int buf[N];
    e->nodes++;
    if (fours(e, s, buf)) return WIN - ply;
    int nb = fours(e, 1 - s, buf);
    if (nb >= 2) return -(WIN - ply - 1);
    int stand = evaluate(e, s);
    if (nb == 1) {                       /* must block; continue the sequence */
        if (qply <= 0) return stand;
        int c = buf[0];
        make(e, c, s);
        int v = -qsearch(e, 1 - s, -beta, -alpha, qply - 1, ply + 1);
        unmake(e, c, s);
        return v;
    }
    if (stand >= beta) return stand;
    if (stand > alpha) alpha = stand;
    if (qply <= 0 || e->nstones >= N) return alpha;
    /* four-making moves */
    int o = 1 - s;
    uint8_t seen[N] = {0};
    for (int l = 0; l < NL; l++) {
        if (e->cnt[s][l] != 3 || e->cnt[o][l]) continue;
        for (int t = 0; t < 5; t++) {
            int c = line_cells[l][t];
            if (e->board[c] || seen[c]) continue;
            seen[c] = 1;
            make(e, c, s);
            int v = -qsearch(e, o, -beta, -alpha, qply - 1, ply + 1);
            unmake(e, c, s);
            if (v > alpha) { alpha = v; if (alpha >= beta) return alpha; }
        }
    }
    return alpha;
}

static int search(Eng *e, int s, int depth, int alpha, int beta, int ply, int *best_out) {
    int buf[N], moves[N];
    e->nodes++;
    if (time_up(e)) return 0;
    if (fours(e, s, buf)) { if (best_out) *best_out = buf[0]; return WIN - ply; }
    int nb = fours(e, 1 - s, buf);
    if (nb >= 2) { if (best_out) *best_out = buf[0]; return -(WIN - ply - 1); }
    if (e->nstones >= N) return 0;
    if (nb == 1) {                        /* forced block: no depth used */
        int c = buf[0];
        make(e, c, s);
        int v = -search(e, 1 - s, depth, -beta, -alpha, ply + 1, NULL);
        unmake(e, c, s);
        if (best_out) *best_out = c;
        return v;
    }
    if (depth <= 0) return qsearch(e, s, alpha, beta, QPLY, ply);

    TTE *t = &e->tt[e->hash & ((1u << TT_BITS) - 1)];
    int ttmove = -1;
    if (t->key == e->hash) {
        ttmove = t->move;
        if (t->depth >= depth && !best_out) {
            int v = t->score;
            if (t->flag == 0) return v;
            if (t->flag == 1 && v >= beta) return v;
            if (t->flag == 2 && v <= alpha) return v;
        }
    }
    int n = gen_moves(e, s, moves, ttmove);
    int width = ply == 0 ? n : (depth >= 3 ? 16 : 24);
    if (n > width) n = width;
    int a0 = alpha, best = -WIN - 1, bm = moves[0];
    for (int i = 0; i < n; i++) {
        int c = moves[i];
        make(e, c, s);
        int v = -search(e, 1 - s, depth - 1, -beta, -alpha, ply + 1, NULL);
        unmake(e, c, s);
        if (e->timeout) break;
        if (v > best) { best = v; bm = c; }
        if (v > alpha) alpha = v;
        if (alpha >= beta) break;
    }
    if (!e->timeout) {
        t->key = e->hash;
        t->score = (int16_t)(best > 30000 ? 30000 : best < -30000 ? -30000 : best);
        t->depth = (int8_t)depth;
        t->flag = best <= a0 ? 2 : best >= beta ? 1 : 0;
        t->move = (uint8_t)bm;
    }
    if (best_out) *best_out = bm;
    return best;
}

typedef struct { int move, depth, score; long long nodes; } MoveInfo;

static MoveInfo think(Eng *e, int s, double seconds, int randomize) {
    MoveInfo mi = {-1, 0, 0, 0};
    e->deadline = now() + seconds;
    e->timeout = 0;
    long long n0 = e->nodes;
    for (int d = 1; d <= 30; d++) {
        int bm = -1;
        int v = search(e, s, d, -WIN - 1, WIN + 1, 0, &bm);
        if (e->timeout) break;
        mi.move = bm; mi.depth = d; mi.score = v;
        if (v > WIN - 200 || v < -WIN + 200) break;
    }
    if (mi.move < 0) {                   /* no full iteration finished: take best-ordered move */
        int moves[N];
        int buf[N];
        if (fours(e, s, buf)) mi.move = buf[0];
        else if (fours(e, 1 - s, buf)) mi.move = buf[0];
        else { gen_moves(e, s, moves, -1); mi.move = moves[0]; }
    }
    if (randomize && mi.score < WIN - 200 && mi.score > -WIN + 200) {
        /* opening diversity: pick among the 3 best-ordered moves */
        int moves[N], n = gen_moves(e, s, moves, mi.move);
        e->rng ^= e->rng << 13; e->rng ^= e->rng >> 7; e->rng ^= e->rng << 17;
        int k = n < 3 ? n : 3;
        mi.move = moves[e->rng % (uint64_t)k];
    }
    mi.nodes = e->nodes - n0;
    return mi;
}

/* ------------------------------------------------- certificate-seeking Black */
typedef unsigned __int128 u128;

/* 2*rank - free of the residual code (live lines, free cells), or a large value
 * if some live line has fewer than 2 free cells. Negative or zero is needed for
 * a whole-line code leaf (necessary, not sufficient). */
static int code_deficit(const Eng *e) {
    u128 rows[NL];
    int nr = 0, nfree = 0;
    for (int c = 0; c < N; c++) nfree += !e->board[c];
    for (int l = 0; l < NL; l++) {
        if (e->cnt[1][l]) continue;
        u128 r = 0;
        int k = 0;
        for (int t = 0; t < 5; t++) {
            int c = line_cells[l][t];
            if (!e->board[c]) { r |= (u128)1 << c; k++; }
        }
        if (k < 2) return 1000;
        rows[nr++] = r;
    }
    int rank = 0;
    for (int bit = 0; bit < N && rank < nr; bit++) {
        int p = -1;
        for (int i = rank; i < nr; i++) if ((rows[i] >> bit) & 1) { p = i; break; }
        if (p < 0) continue;
        u128 t = rows[p]; rows[p] = rows[rank]; rows[rank] = t;
        for (int i = 0; i < nr; i++) if (i != rank && ((rows[i] >> bit) & 1)) rows[i] ^= rows[rank];
        rank++;
    }
    return 2 * rank - nfree;
}

/* Black (s = 1) picks, among its top-k ordered moves that a depth-limited White
 * search cannot refute, the one with the smallest code deficit. */
static MoveInfo think_cert(Eng *e, double seconds, int k, int safe_depth) {
    MoveInfo base = think(e, 1, seconds, 0);
    int buf[N], moves[N];
    if (fours(e, 1, buf) || fours(e, 0, buf)) return base;    /* tactics first */
    int n = gen_moves(e, 1, moves, base.move);
    if (n > k) n = k;
    int best = base.move, bestdef = 1 << 30;
    for (int i = 0; i < n; i++) {
        int c = moves[i];
        make(e, c, 1);
        e->deadline = now() + seconds;
        e->timeout = 0;
        int v = search(e, 0, safe_depth, -WIN - 1, WIN + 1, 1, NULL);   /* White's view */
        int def = code_deficit(e);
        unmake(e, c, 1);
        if (e->timeout || v > WIN - 200) continue;                     /* unsafe or unknown */
        if (def < bestdef) { bestdef = def; best = c; }
    }
    base.move = best;
    base.score = bestdef;
    return base;
}

/* Black (s = 1) picks, among its top-k safe moves, the one whose position has
 * the lowest hybrid exact shortfall after a short warm-started local search
 * from the game's current layout. The layout is updated to the winner's. */
static MoveInfo think_hybrid(Eng *e, int *region, double seconds, int k, int safe_depth,
                             long steps, uint64_t *rng, int *score_out) {
    MoveInfo base = think(e, 1, seconds, 0);
    int buf[N], moves[N], tmp[N], bestreg[N];
    HPos p;
    int bestsc = 1 << 30, best = -1;
    if (fours(e, 1, buf) || fours(e, 0, buf)) {          /* tactics first */
        make(e, base.move, 1);
        h_pos(&p, e->board);
        *score_out = h_anneal(&p, region, 40, steps, rng, 1.0, 0.2);
        unmake(e, base.move, 1);
        return base;
    }
    int n = gen_moves(e, 1, moves, base.move);
    if (n > k) n = k;
    for (int i = 0; i < n; i++) {
        int c = moves[i];
        make(e, c, 1);
        e->deadline = now() + seconds;
        e->timeout = 0;
        int v = search(e, 0, safe_depth, -WIN - 1, WIN + 1, 1, NULL);
        if (!e->timeout && v < WIN - 200) {
            memcpy(tmp, region, sizeof tmp);
            h_pos(&p, e->board);
            int sc = h_anneal(&p, tmp, 40, steps, rng, 1.0, 0.2);
            if (sc < bestsc) { bestsc = sc; best = c; memcpy(bestreg, tmp, sizeof tmp); }
        }
        unmake(e, c, 1);
    }
    if (best < 0) {
        make(e, base.move, 1);
        h_pos(&p, e->board);
        *score_out = h_anneal(&p, region, 40, steps, rng, 1.0, 0.2);
        unmake(e, base.move, 1);
        return base;
    }
    memcpy(region, bestreg, sizeof bestreg);
    base.move = best;
    *score_out = bestsc;
    return base;
}

/* ------------------------------------------------------------------ games */
typedef struct { int id, nmoves, moves[MAXPLY], done; char result[8]; int hyb[MAXPLY]; int region[N]; } Game;

static long long g_nodes = 0;
static int g_done = 0, g_maxdepth = 0;
static double g_t0, g_last = 0;

static void write_game(FILE *f, const Game *g, const char *status) {
    fprintf(f, "{\"id\":%d,\"status\":\"%s\",\"result\":\"%s\",\"plies\":%d,\"moves\":[",
            g->id, status, g->result, g->nmoves);
    for (int i = 0; i < g->nmoves; i++) fprintf(f, "%s%d", i ? "," : "", g->moves[i]);
    fprintf(f, "],\"hybrid\":[");
    for (int i = 0; i < g->nmoves; i++) fprintf(f, "%s%d", i ? "," : "", g->hyb[i]);
    fprintf(f, "]}\n");
    fflush(f);
}

static int parse_line(const char *s, Game *g) {
    const char *p = strstr(s, "\"id\":");
    if (!p) return 0;
    g->id = atoi(p + 5);
    g->done = strstr(s, "\"status\":\"done\"") != NULL;
    p = strstr(s, "\"result\":\"");
    if (p) { sscanf(p + 10, "%7[^\"]", g->result); }
    p = strstr(s, "\"moves\":[");
    g->nmoves = 0;
    if (p) {
        p += 9;
        while (*p && *p != ']') {
            g->moves[g->nmoves++] = (int)strtol(p, (char **)&p, 10);
            if (*p == ',') p++;
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    int games = 24, threads = 22, maxply = 60, random_plies = 4, resume = 0;
    int cert_black = 0, cert_k = 12, safe_depth = 4, hyb_black = 0;
    long hyb_steps = 30000;
    const char *layout = "hybrid_c_empty/best.txt";
    double move_time = 1.0;
    const char *out = "games.jsonl";
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--games")) games = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--threads")) threads = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--time")) move_time = atof(argv[++i]);
        else if (!strcmp(argv[i], "--maxply")) maxply = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--random-plies")) random_plies = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--out")) out = argv[++i];
        else if (!strcmp(argv[i], "--resume")) resume = 1;
        else if (!strcmp(argv[i], "--black-cert")) cert_black = 1;
        else if (!strcmp(argv[i], "--cert-k")) cert_k = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--safe-depth")) safe_depth = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--black-hybrid")) hyb_black = 1;
        else if (!strcmp(argv[i], "--hyb-steps")) hyb_steps = atol(argv[++i]);
        else if (!strcmp(argv[i], "--layout")) layout = argv[++i];
        else { fprintf(stderr, "unknown option %s\n", argv[i]); return 2; }
    }
    if (maxply > MAXPLY) maxply = MAXPLY;
    init_lines();
    h_init();
    int start_region[N];
    for (int c = 0; c < N; c++) start_region[c] = -1;
    if (hyb_black) {
        if (!h_load_layout(layout, start_region)) { fprintf(stderr, "cannot read layout %s\n", layout); return 1; }
        printf("hybrid-aware Black: start layout %s, %ld local steps per candidate\n", layout, hyb_steps);
    }
    signal(SIGINT, on_sigint);

    Game *gs = calloc((size_t)games, sizeof(Game));
    for (int i = 0; i < games; i++) gs[i].id = i;
    if (resume) {
        FILE *f = fopen(out, "r");
        if (f) {
            char *line = malloc(1 << 16);
            while (fgets(line, 1 << 16, f)) {
                Game g;
                memset(&g, 0, sizeof g);
                if (parse_line(line, &g) && g.id >= 0 && g.id < games) gs[g.id] = g;
            }
            free(line);
            fclose(f);
        }
    }
    int todo = 0;
    for (int i = 0; i < games; i++) todo += !gs[i].done;
    FILE *f = fopen(out, "a");
    if (!f) { perror(out); return 1; }
    printf("engine: %d lines; %d games to play (%d already done), %d threads, %.2fs/move, "
           "max %d plies; upper bound %.1f min wall\n",
           NL, todo, games - todo, threads, move_time, maxply,
           (double)((todo + threads - 1) / threads) * maxply * move_time / 60.0);
    fflush(stdout);
    g_t0 = now();
    omp_set_num_threads(threads);
#pragma omp parallel for schedule(dynamic, 1)
    for (int gi = 0; gi < games; gi++) {
        Game *g = &gs[gi];
        if (g->done || stop_flag) continue;
        Eng e;
        memset(&e, 0, sizeof e);
        e.tt = calloc((size_t)1 << TT_BITS, sizeof(TTE));
        e.rng = 0x1234567ull + (uint64_t)gi * 0x9E3779B97F4A7C15ull;
        for (int i = 0; i < g->nmoves; i++) make(&e, g->moves[i], i & 1);
        strcpy(g->result, "open");
        memcpy(g->region, start_region, sizeof start_region);
        for (int i = g->nmoves; i < MAXPLY; i++) g->hyb[i] = -1;
        uint64_t hrng = 0xABCDEF12345ull + (uint64_t)gi * 0x9E3779B97F4A7C15ull;
        while (g->nmoves < maxply && !stop_flag) {
            int s = g->nmoves & 1;
            int hsc = -1;
            MoveInfo mi = (s == 1 && hyb_black)   /* hybrid Black from its first move */
                ? think_hybrid(&e, g->region, move_time, cert_k, safe_depth, hyb_steps, &hrng, &hsc)
                : (s == 1 && cert_black && g->nmoves >= random_plies)
                ? think_cert(&e, move_time, cert_k, safe_depth)
                : think(&e, s, move_time, g->nmoves < random_plies);
            g->hyb[g->nmoves] = hsc;
            if (hsc >= 0 && hsc < 1000) {
#pragma omp critical(progress)
                { printf("    game %d round %d: Black %d, hybrid shortfall %d\n", g->id, g->nmoves / 2 + 1, mi.move, hsc); fflush(stdout); }
            }
            if (stop_flag && mi.depth == 0) break;
            make(&e, mi.move, s);
            g->moves[g->nmoves++] = mi.move;
#pragma omp atomic
            g_nodes += mi.nodes;
            if (mi.depth > g_maxdepth) g_maxdepth = mi.depth;
            int buf[N];
            (void)buf;
            int won = 0;
            for (int i = 0; i < nlines_of[mi.move]; i++)
                if (e.cnt[s][lines_of[mi.move][i]] == 5) won = 1;
            if (won) { strcpy(g->result, s ? "black" : "white"); break; }
            if (e.nstones >= N) { strcpy(g->result, "draw"); break; }
            double t = now();
            if (t - g_last > 2.0) {
#pragma omp critical(progress)
                if (t - g_last > 2.0) {
                    g_last = t;
                    printf("  [%5.0fs] games done %d/%d | game %d ply %d: %s %d depth %d eval %d | "
                           "%.2f M nodes/s total, max depth %d\n",
                           t - g_t0, g_done, todo, g->id, g->nmoves, s ? "Black" : "White",
                           mi.move, mi.depth, mi.score, g_nodes / (t - g_t0) / 1e6, g_maxdepth);
                    fflush(stdout);
                }
            }
        }
        int finished = !stop_flag || strcmp(g->result, "open") != 0 || g->nmoves >= maxply;
#pragma omp critical(output)
        {
            write_game(f, g, finished ? "done" : "partial");
            if (finished) {
                g_done++;
                printf("  game %d finished: %s after %d plies\n", g->id, g->result, g->nmoves);
                fflush(stdout);
            }
        }
        free(e.tt);
    }
    fclose(f);
    printf("%s after %.0fs; %.2f M nodes/s; results in %s\n",
           stop_flag ? "INTERRUPTED (partial games saved; use --resume)" : "DONE",
           now() - g_t0, g_nodes / (now() - g_t0) / 1e6, out);
    return 0;
}
