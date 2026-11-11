/* Research 032: Maker-Breaker engine on the 109 lines of the 5x5x5 board (Q0).
 * Fast version: bitboards and AVX2. `mb_ref.c` is the plain reference; both
 * must produce byte-identical games for the same command line (see README).
 *
 * Maker (moves first) wins by owning all five cells of a line. Breaker wins if
 * that never happens. Breaker's own lines mean nothing. Output is test data,
 * never proof.
 *
 * Style: functional. A position is an immutable value; `play` returns a new
 * one and nothing is ever undone. Every function above `main` is a pure
 * function of its arguments: no globals, geometry passed as `const Geo *`, node
 * counts returned in results, and a node budget instead of a clock, so a move
 * is a deterministic function of (position, budget). Kept mutable on purpose,
 * both local: loop accumulators, and the transposition table, a memo cache that
 * `think` creates and frees itself. Effects live only in `main`.
 *
 * What makes it fast:
 *   - Position = 448 bytes, 32-byte aligned, copied with 14 AVX2 moves.
 *   - Line states are 109 bytes in four YMM registers: "which lines have 3 (or
 *     4) Maker stones" is 4 compares + 4 movemasks, not a 109-step loop. A count
 *     of four-lines (`n4`) skips even that at most nodes.
 *   - Occupancy is a 125-bit bitboard; the empty cell of a line is one
 *     and-not + tzcnt against the line's precomputed mask.
 *   - Move-ordering scores are kept incrementally (at most 65 adds per move
 *     instead of ~545 table reads per node) as 125 uint16 in eight YMM
 *     registers. Moves are selected lazily: each pick is a SIMD max over the
 *     board, so a node that cuts off on its first move never sorts anything.
 *   - The child's transposition slot is prefetched as soon as its hash exists.
 *   - One game per thread: no shared state, linear scaling.
 *
 * Exact adjudication (Erdos-Selfridge): pot = sum over live lines (no Breaker
 * stone) of 2^(Maker stones on it). Breaker wins if
 *     Breaker to move and pot < 32,   or   Maker to move and pot < 16.
 *
 * Control: progress with an ETA every 2 s. Ctrl-C, or creating the stop file
 * (default `STOP` in the working directory), ends each game after its current
 * move and saves it as "partial"; --resume continues, and because moves are
 * deterministic the result equals an uninterrupted run. Finished games are
 * appended as they end.
 *
 * Build: gcc -O3 -march=native -fopenmp mb.c -o mb.exe      (needs AVX2, BMI)
 */
#include <immintrin.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

#ifndef __AVX2__
#error "mb.c needs AVX2; build mb_ref.c on other machines"
#endif

#define WIN 100000
#define BW 50000
#define QPLY 10
#define TT_BITS 20

#include "mbcore.h"

/* Move ordering keys: 0 for a taken cell, score + 1 for a free one. */
typedef struct { _Alignas(32) uint16_t k[128]; } Keys;

static inline Keys move_keys(const Pos *p) {
    const __m256i bit = _mm256_setr_epi16(1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048,
                                          4096, 8192, 16384, (short)0x8000);
    const __m256i one = _mm256_set1_epi16(1);
    Keys K;
    for (int j = 0; j < 8; j++) {
        const uint16_t freebits = (uint16_t)~(p->occ[j >> 2] >> (16 * (j & 3)));
        const __m256i open = _mm256_cmpeq_epi16(
            _mm256_and_si256(_mm256_set1_epi16((short)freebits), bit), bit);
        const __m256i sc = _mm256_load_si256((const __m256i *)(p->score + 16 * j));
        _mm256_store_si256((__m256i *)(K.k + 16 * j),
                           _mm256_and_si256(_mm256_adds_epu16(sc, one), open));
    }
    return K;
}

/* The best remaining cell (highest key, lowest index on ties), or -1. */
static inline int best_key(const Keys *K) {
    __m256i v[8], m;
    for (int j = 0; j < 8; j++) v[j] = _mm256_load_si256((const __m256i *)(K->k + 16 * j));
    m = _mm256_max_epu16(_mm256_max_epu16(_mm256_max_epu16(v[0], v[1]), _mm256_max_epu16(v[2], v[3])),
                         _mm256_max_epu16(_mm256_max_epu16(v[4], v[5]), _mm256_max_epu16(v[6], v[7])));
    const __m128i h = _mm_max_epu16(_mm256_castsi256_si128(m), _mm256_extracti128_si256(m, 1));
    const int top = 0xFFFF ^ _mm_extract_epi16(
        _mm_minpos_epu16(_mm_xor_si128(h, _mm_set1_epi16(-1))), 0);
    if (!top) return -1;
    const __m256i t = _mm256_set1_epi16((short)top);
    for (int j = 0; j < 8; j++) {
        const uint32_t eq = (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi16(v[j], t));
        if (eq) return 16 * j + ((int)_tzcnt_u32(eq) >> 1);
    }
    return -1;
}

static inline Keys without(Keys K, int c) { K.k[c] = 0; return K; }

/* The i-th move (i = 0, 1, 2) in search order: `first` if it is free, then by key. */
static int nth_move(const Pos *p, int first, int i) {
    Keys K = move_keys(p);
    int c = -1;
    if (first >= 0 && first < N && K.k[first]) { c = first; K = without(K, first); i--; }
    for (; i >= 0; i--) { c = best_key(&K); if (c >= 0) K = without(K, c); }
    return c;
}

/* ------------------------------------------------------------ search */
typedef struct { uint64_t key; int32_t score; int8_t depth; uint8_t flag; uint8_t move; } TTE;
typedef struct { int score, move; long long nodes; int cut; } Res;   /* cut: budget ran out */

static inline Res leaf(int score, int move) { return (Res){score, move, 1, 0}; }
static inline Res negate(Res r, int move) { return (Res){-r.score, move, r.nodes + 1, r.cut}; }

/* Quiescence: Maker's four-making moves and Breaker's forced blocks. */
static Res qsearch(const Geo *G, const Pos *p, int alpha, int beta, int q, int ply) {
    const Fours f = fours(G, p);
    if (side(p) == 1) {
        if (f.n >= 2) return leaf(-(WIN - ply - 1), -1);
        if (p->pot < 32) return leaf(BW - ply, -1);
        if (f.n == 1 && q > 0) {
            const Pos next = play(G, p, f.c[0]);
            return negate(qsearch(G, &next, -beta, -alpha, q - 1, ply + 1), -1);
        }
        return leaf(-p->ev, -1);
    }
    if (f.n) return leaf(WIN - ply, -1);
    if (p->pot < 16) return leaf(-(BW - ply), -1);
    if (p->ev >= beta || q <= 0) return leaf(p->ev > alpha ? p->ev : alpha, -1);
    int a = p->ev > alpha ? p->ev : alpha;
    long long nodes = 1;
    uint64_t seen[2] = {p->occ[0], p->occ[1]};          /* taken or already tried */
    const LineSet threes = lines_with(p, 3);
    for (int j = 0; j < 4 && a < beta; j++)
        for (uint32_t w = threes.w[j]; w && a < beta; w &= w - 1) {
            const uint8_t *const cs = G->cells[32 * j + (int)_tzcnt_u32(w)];
            for (int t = 0; t < 5 && a < beta; t++) {
                const int c = cs[t];
                if (seen[c >> 6] >> (c & 63) & 1) continue;
                seen[c >> 6] |= 1ull << (c & 63);
                const Pos next = play(G, p, c);
                const Res r = qsearch(G, &next, -beta, -a, q - 1, ply + 1);
                nodes += r.nodes;
                if (-r.score > a) a = -r.score;
            }
        }
    return (Res){a, -1, nodes, 0};
}

static Res search(const Geo *G, TTE *tt, const Pos *p, int depth, int alpha, int beta, int ply,
                  long long budget) {
    if (budget <= 0) return (Res){0, -1, 0, 1};
    const Fours f = fours(G, p);
    if (side(p) == 0) {
        if (f.n) return leaf(WIN - ply, f.c[0]);
        if (p->pot < 16) return leaf(-(BW - ply), -1);
    } else {
        if (f.n >= 2) return leaf(-(WIN - ply - 1), f.c[0]);
        if (p->pot < 32) return leaf(BW - ply, -1);
        if (f.n == 1) {                       /* forced block: uses no depth */
            const Pos next = play(G, p, f.c[0]);
            return negate(search(G, tt, &next, depth, -beta, -alpha, ply + 1, budget - 1), f.c[0]);
        }
    }
    if (depth <= 0) return qsearch(G, p, alpha, beta, QPLY, ply);

    TTE *const slot = &tt[p->hash & ((1u << TT_BITS) - 1)];
    const TTE seen = *slot;
    const int hit = seen.key == p->hash;
    if (hit && seen.depth >= depth && ply > 0) {
        if (seen.flag == 0) return leaf(seen.score, seen.move);
        if (seen.flag == 1 && seen.score >= beta) return leaf(seen.score, seen.move);
        if (seen.flag == 2 && seen.score <= alpha) return leaf(seen.score, seen.move);
    }
    const int nfree = N - p->nstones;
    const int width = ply == 0 ? nfree : (depth >= 3 ? 16 : 24);
    const int n = nfree < width ? nfree : width;
    Keys K = move_keys(p);
    const int first = hit && seen.move < N && K.k[seen.move] ? seen.move : -1;
    if (first >= 0) K = without(K, first);
    int a = alpha, best = -WIN - 1, bm = -1;
    long long nodes = 1;
    for (int i = 0; i < n && a < beta; i++) {
        const int c = i == 0 && first >= 0 ? first : best_key(&K);
        K = without(K, c);
        if (bm < 0) bm = c;
        const Pos next = play(G, p, c);
        _mm_prefetch((const char *)&tt[next.hash & ((1u << TT_BITS) - 1)], _MM_HINT_T0);
        const Res r = search(G, tt, &next, depth - 1, -beta, -a, ply + 1, budget - nodes);
        nodes += r.nodes;
        if (r.cut) return (Res){best, bm, nodes, 1};
        if (-r.score > best) { best = -r.score; bm = c; }
        if (best > a) a = best;
    }
    *slot = (TTE){p->hash, best, (int8_t)depth, (uint8_t)(best <= alpha ? 2 : best >= beta ? 1 : 0),
                  (uint8_t)bm};
    return (Res){best, bm, nodes, 0};
}

typedef struct { int move, depth, score; long long nodes; } MoveInfo;

static int decided(int score) { return score > BW - 400 || score < -BW + 400; }

static uint64_t mix(uint64_t x) {
    x ^= x >> 33; x *= 0xFF51AFD7ED558CCDull; x ^= x >> 33; x *= 0xC4CEB9FE1A85EC53ull;
    return x ^ (x >> 33);
}

/* The move for the side to move: iterative deepening within `budget` nodes.
 * `dice` != 0 asks for opening variety: one of the 3 best-ordered moves. */
static MoveInfo think(const Geo *G, const Pos *p, long long budget, uint64_t dice) {
    TTE *const tt = calloc((size_t)1 << TT_BITS, sizeof(TTE));
    MoveInfo mi = {nth_move(p, -1, 0), 0, 0, 0};
    for (int d = 1; d <= 40 && !decided(mi.score); d++) {
        const Res r = search(G, tt, p, d, -WIN - 1, WIN + 1, 0, budget - mi.nodes);
        mi.nodes += r.nodes;
        if (r.cut) break;
        mi.move = r.move; mi.depth = d; mi.score = r.score;
    }
    free(tt);
    if (mi.depth == 0) {                      /* no iteration finished: block if needed */
        const Fours f = fours(G, p);
        if (f.n) mi.move = f.c[0];
    }
    if (dice && !decided(mi.score)) {
        const int nfree = N - p->nstones;
        mi.move = nth_move(p, mi.move, (int)(dice % (uint64_t)(nfree < 3 ? nfree : 3)));
    }
    return mi;
}

/* ------------------------------------------------------------ games */
typedef struct { int id, nmoves, done; uint8_t moves[N]; int pot[N + 1]; char result[12]; } Game;

static Game new_game(int id) {
    Game g;
    memset(&g, 0, sizeof g);
    g.id = id;
    g.pot[0] = NL;
    strcpy(g.result, "open");
    return g;
}

static Game with_move(Game g, int c, int pot) {
    g.moves[g.nmoves] = (uint8_t)c;
    g.pot[++g.nmoves] = pot;
    return g;
}

static Game with_result(Game g, const char *result) {
    strcpy(g.result, result);
    g.done = 1;
    return g;
}

static Pos position_of(const Geo *G, const Game *g) {
    Pos p = empty_pos(G);
    for (int i = 0; i < g->nmoves; i++) { const Pos next = play(G, &p, g->moves[i]); p = next; }
    return p;
}

/* A saved record, with its potential trace rebuilt from the moves. */
static Game parse_game(const Geo *G, const char *s) {
    const char *p = strstr(s, "\"id\":");
    if (!p) return new_game(-1);
    Game g = new_game(atoi(p + 5));
    Pos pos = empty_pos(G);
    p = strstr(s, "\"moves\":[");
    if (p)
        for (p += 9; *p && *p != ']' && g.nmoves < N; p += *p == ',') {
            const int c = (int)strtol(p, (char **)&p, 10);
            if (c < 0 || c >= N || taken(&pos, c)) return new_game(-1);
            const Pos next = play(G, &pos, c);
            g = with_move(g, c, next.pot);
            pos = next;
        }
    char result[12] = "open";
    p = strstr(s, "\"result\":\"");
    if (p) sscanf(p + 10, "%11[^\"]", result);
    return strstr(s, "\"status\":\"done\"") ? with_result(g, result) : g;
}

/* ------------------------------------------------------------ effects: main only */
static volatile sig_atomic_t stop_flag = 0;
static void on_sigint(int s) { (void)s; stop_flag = 1; }

static int file_exists(const char *path) {
    FILE *f = fopen(path, "r");
    if (f) fclose(f);
    return f != NULL;
}

static void write_game(FILE *f, const Game *g) {
    fprintf(f, "{\"id\":%d,\"status\":\"%s\",\"result\":\"%s\",\"plies\":%d,\"moves\":[",
            g->id, g->done ? "done" : "partial", g->result, g->nmoves);
    for (int i = 0; i < g->nmoves; i++) fprintf(f, "%s%d", i ? "," : "", g->moves[i]);
    fprintf(f, "],\"pot\":[");
    for (int i = 0; i <= g->nmoves; i++) fprintf(f, "%s%d", i ? "," : "", g->pot[i]);
    fprintf(f, "]}\n");
    fflush(f);
}

int main(int argc, char **argv) {
    int games = 22, threads = 22, random_plies = 4, resume = 0;
    long long nm = 1000000, nb = 1000000;
    const char *out = "mb_games.jsonl", *stop_file = "STOP";
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--games")) games = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--threads")) threads = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--nm")) nm = atoll(argv[++i]);
        else if (!strcmp(argv[i], "--nb")) nb = atoll(argv[++i]);
        else if (!strcmp(argv[i], "--random-plies")) random_plies = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--out")) out = argv[++i];
        else if (!strcmp(argv[i], "--stop-file")) stop_file = argv[++i];
        else if (!strcmp(argv[i], "--resume")) resume = 1;
        else { fprintf(stderr, "unknown option %s\n", argv[i]); return 2; }
    }
    if (file_exists(stop_file)) {
        fprintf(stderr, "stop file '%s' exists; delete it to run\n", stop_file);
        return 3;
    }
    const Geo geo = make_geo();
    const Geo *const G = &geo;
    signal(SIGINT, on_sigint);

    Game *const gs = malloc((size_t)games * sizeof(Game));
    for (int i = 0; i < games; i++) gs[i] = new_game(i);
    if (resume) {
        FILE *in = fopen(out, "r");
        if (in) {
            char *line = malloc(1 << 16);
            while (fgets(line, 1 << 16, in)) {
                const Game g = parse_game(G, line);
                if (g.id >= 0 && g.id < games) gs[g.id] = g;
            }
            free(line);
            fclose(in);
        }
    }
    int todo = 0;
    long long plies_before = 0;
    for (int i = 0; i < games; i++) if (!gs[i].done) { todo++; plies_before += gs[i].nmoves; }
    FILE *f = fopen(out, "a");
    if (!f) { perror(out); return 1; }
    const double per_ply = (double)(nm + nb) / 2.0 / 2.0e6;      /* seconds, at ~2 M nodes/s/thread */
    const double waves = (double)todo / (double)(threads < todo ? threads : todo ? todo : 1);
    printf("mb: Maker-Breaker on %d lines; %d games to play (%d done), %d threads; "
           "Maker %lld nodes/move, Breaker %lld nodes/move\n"
           "    estimate: about %.1f min wall if games last ~72 plies; hard upper bound %.1f min "
           "(125 plies)\n    stop: Ctrl-C or create file '%s'; continue with --resume\n",
           NL, todo, games - todo, threads, nm, nb,
           waves * 72 * per_ply / 60.0, waves * 125 * per_ply / 60.0, stop_file);
    fflush(stdout);

    const double t0 = omp_get_wtime();
    double last = 0;
    long long nodes = 0, plies = 0, done_plies = 0;
    int ndone = 0, nmaker = 0, nbreaker = 0, maxdepth = 0;
    omp_set_num_threads(threads);
#pragma omp parallel for schedule(dynamic, 1)
    for (int gi = 0; gi < games; gi++) {
        if (gs[gi].done || stop_flag) continue;
        Game g = gs[gi];
        Pos p = position_of(G, &g);
        while (!g.done && !stop_flag) {
            if (breaker_certified(&p) || g.nmoves >= N) { g = with_result(g, "breaker"); break; }
            const int s = side(&p);
            const uint64_t dice = g.nmoves < random_plies
                ? 1 + mix(((uint64_t)g.id << 8) + (uint64_t)g.nmoves) % 1000003 : 0;
            const MoveInfo mi = think(G, &p, s ? nb : nm, dice);
            const Pos next = play(G, &p, mi.move);
            g = with_move(g, mi.move, next.pot);
            if (s == 0 && maker_has_line_through(G, &next, mi.move)) g = with_result(g, "maker");
            p = next;
#pragma omp critical(progress)
            {
                nodes += mi.nodes; plies++;
                if (mi.depth > maxdepth) maxdepth = mi.depth;
                const double t = omp_get_wtime();
                if (t - last >= 2.0) {
                    last = t;
                    if (file_exists(stop_file)) stop_flag = 1;
                    /* ETA: plies still to play (games assumed as long as those finished so
                       far, 72 before any has) over the plies played per second so far. */
                    const double len = ndone ? (double)done_plies / ndone : 72.0;
                    const double left = len * todo - (double)(plies + plies_before);
                    const double floor_left = 2.0 * (todo - ndone);
                    const double eta = (left > floor_left ? left : floor_left) / ((double)plies / (t - t0));
                    printf("  [%6.1fs] done %d/%d (maker %d, breaker %d) | ETA ~%.0fs | game %d ply %d "
                           "%s->%d depth %d score %d pot %d | %.1f M nodes/s\n",
                           t - t0, ndone, todo, nmaker, nbreaker, eta, g.id, g.nmoves,
                           s ? "B" : "M", mi.move, mi.depth, mi.score, p.pot,
                           (double)nodes / (t - t0) / 1e6);
                    fflush(stdout);
                }
            }
        }
#pragma omp critical(progress)
        {
            write_game(f, &g);
            if (g.done) {
                ndone++; done_plies += g.nmoves;
                if (!strcmp(g.result, "maker")) nmaker++; else nbreaker++;
                printf("  game %d: %s at ply %d (final pot %d)\n", g.id, g.result, g.nmoves, p.pot);
            } else {
                printf("  game %d: stopped at ply %d, saved for --resume\n", g.id, g.nmoves);
            }
            fflush(stdout);
        }
        gs[gi] = g;
    }
    const double dt = omp_get_wtime() - t0;
    printf("%s: %d games this run, maker %d, breaker %d, %.1fs, %.1f M nodes/s, max depth %d\n",
           stop_flag ? "STOPPED (run again with --resume)" : "finished",
           ndone, nmaker, nbreaker, dt, (double)nodes / (dt + 1e-9) / 1e6, maxdepth);
    fclose(f);
    free(gs);
    return 0;
}
