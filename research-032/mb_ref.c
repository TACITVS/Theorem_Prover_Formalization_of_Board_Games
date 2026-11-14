/* Research 032: Maker-Breaker engine on the 109 lines of the 5x5x5 board (Q0).
 * REFERENCE version: plain byte arrays, no SIMD, slow on purpose. `mb.c` is the
 * fast version and must produce byte-identical games for the same command line.
 * Nodes-per-move options only (--nm, --nb); no ETA and no stop file here.
 *
 * Maker (moves first) wins by owning all five cells of a line. Breaker wins if
 * that never happens. Breaker's own lines mean nothing. Output is test data,
 * never proof.
 *
 * Style: functional. A position is an immutable 256-byte value; `play` returns
 * a new position and nothing is ever undone. Every function below `main` is a
 * pure function of its arguments:
 *   - no global variables except the Ctrl-C flag, which only `main` reads;
 *   - the geometry tables are built once and passed as `const Geo *`;
 *   - the search returns its node count in its result, and its work limit is a
 *     node budget, not a clock, so a move is a deterministic function of
 *     (position, budget). Same command line, same games, on any machine.
 * Two things are kept mutable on purpose, both local:
 *   - loop accumulators (alpha, best move, node count) inside one function;
 *   - the transposition table, a memo cache that `think` creates and frees
 *     itself. It changes speed, never the meaning of a position.
 * Effects (files, printing, signals, OpenMP) live only in `main`.
 *
 * Exact adjudication (Erdos-Selfridge): pot = sum over live lines (no Breaker
 * stone) of 2^(Maker stones on it). Breaker wins if
 *     Breaker to move and pot < 32,   or   Maker to move and pot < 16.
 * The search uses this as a sound cutoff and the game stops there.
 *
 * Checkpointing: each finished game is appended as one JSON line. On Ctrl-C,
 * unfinished games are written as "partial"; --resume continues them and, since
 * moves are deterministic, gives exactly the games an uninterrupted run gives.
 *
 * Build: gcc -O3 -march=native -fopenmp mb.c -o mb.exe
 */
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

#define N 125
#define NL 109
#define WIN 100000
#define BW 50000
#define QPLY 10
#define TT_BITS 20
#define DEAD 255

/* ------------------------------------------------------------ geometry */
typedef struct {
    uint8_t cells[NL][5];        /* the five cells of each line */
    uint8_t of[N][13];           /* the lines through each cell */
    uint8_t nof[N];
    uint64_t zob[2][N];
} Geo;

static Geo make_geo(void) {
    Geo g;
    memset(&g, 0, sizeof g);
    int n = 0;
    for (int s = 0; s < N; s++) {
        const int x = s % 5, y = s / 5 % 5, z = s / 25;
        for (int dx = -1; dx <= 1; dx++)
            for (int dy = -1; dy <= 1; dy++)
                for (int dz = -1; dz <= 1; dz++) {
                    if (!dx && !dy && !dz) continue;
                    if (dx < 0 || (dx == 0 && (dy < 0 || (dy == 0 && dz < 0)))) continue;
                    const int ex = x + 4 * dx, ey = y + 4 * dy, ez = z + 4 * dz;
                    const int px = x - dx, py = y - dy, pz = z - dz;
                    const int end_in = ex >= 0 && ex <= 4 && ey >= 0 && ey <= 4 && ez >= 0 && ez <= 4;
                    const int prev_in = px >= 0 && px <= 4 && py >= 0 && py <= 4 && pz >= 0 && pz <= 4;
                    if (!end_in || prev_in) continue;      /* s must be the line's first cell */
                    if (n >= NL) { fprintf(stderr, "too many lines\n"); exit(1); }
                    for (int t = 0; t < 5; t++)
                        g.cells[n][t] = (uint8_t)((x + t * dx) + 5 * (y + t * dy) + 25 * (z + t * dz));
                    n++;
                }
    }
    if (n != NL) { fprintf(stderr, "expected 109 lines, got %d\n", n); exit(1); }
    for (int l = 0; l < NL; l++)
        for (int t = 0; t < 5; t++) { const int c = g.cells[l][t]; g.of[c][g.nof[c]++] = (uint8_t)l; }
    uint64_t r = 0x9E3779B97F4A7C15ull;
    for (int s = 0; s < 2; s++)
        for (int c = 0; c < N; c++) {
            r ^= r << 13; r ^= r >> 7; r ^= r << 17;
            g.zob[s][c] = r * 0x2545F4914F6CDD1Dull;
        }
    return g;
}

/* ------------------------------------------------------------ positions */
typedef struct {
    uint8_t owner[N];            /* 0 empty, 1 Maker, 2 Breaker */
    uint8_t line[NL];            /* Maker stones on the line, or DEAD once Breaker is on it */
    int16_t nstones;             /* side to move = nstones & 1 (0 Maker, 1 Breaker) */
    int32_t pot;                 /* exact Erdos-Selfridge potential */
    int32_t ev;                  /* heuristic value, Maker's view */
    uint64_t hash;
} Pos;

static const int VAL[6] = {1, 3, 12, 80, 600, 5000};
static const int ORD[5] = {1, 6, 40, 400, 4000};

static Pos empty_pos(void) {
    Pos p;
    memset(&p, 0, sizeof p);
    p.pot = NL;
    p.ev = NL * VAL[0];
    return p;
}

static int side(const Pos *p) { return p->nstones & 1; }

/* The position after the side to move takes cell c. The argument is untouched. */
static Pos play(const Geo *G, const Pos *p, int c) {
    const int s = side(p);
    Pos q = *p;
    q.owner[c] = (uint8_t)(s + 1);
    q.hash = p->hash ^ G->zob[s][c];
    q.nstones = (int16_t)(p->nstones + 1);
    for (int i = 0; i < G->nof[c]; i++) {
        const int l = G->of[c][i], v = p->line[l];
        if (v == DEAD) continue;
        if (s == 0) { q.pot += 1 << v; q.ev += VAL[v + 1] - VAL[v]; q.line[l] = (uint8_t)(v + 1); }
        else        { q.pot -= 1 << v; q.ev -= VAL[v];              q.line[l] = DEAD; }
    }
    return q;
}

static int maker_has_line_through(const Geo *G, const Pos *p, int c) {
    int won = 0;
    for (int i = 0; i < G->nof[c]; i++) won |= p->line[G->of[c][i]] == 5;
    return won;
}

/* Breaker has provably won (Erdos-Selfridge) with the current side to move. */
static int breaker_certified(const Pos *p) { return p->pot < (side(p) ? 32 : 16); }

/* Cells where Maker would complete a line (distinct, at most 16 reported). */
typedef struct { int n; uint8_t c[16]; } Fours;

static Fours fours(const Geo *G, const Pos *p) {
    Fours f = {0, {0}};
    for (int l = 0; l < NL; l++) {
        if (p->line[l] != 4) continue;
        for (int t = 0; t < 5; t++) {
            const int c = G->cells[l][t];
            if (p->owner[c]) continue;
            int dup = 0;
            for (int k = 0; k < f.n; k++) dup |= f.c[k] == c;
            if (!dup && f.n < 16) f.c[f.n++] = (uint8_t)c;
            break;
        }
    }
    return f;
}

/* Free cells, best first: a cell is worth the live lines through it. */
typedef struct { int n; uint8_t c[N]; } Moves;

static Moves ordered_moves(const Geo *G, const Pos *p, int first) {
    Moves m;
    int sc[N];
    m.n = 0;
    for (int c = 0; c < N; c++) {
        if (p->owner[c]) continue;
        int v = c == first ? 1 << 28 : 0;
        for (int i = 0; i < G->nof[c]; i++) {
            const int l = p->line[G->of[c][i]];
            if (l != DEAD) v += ORD[l];
        }
        int j = m.n++;                                   /* insertion, descending */
        while (j > 0 && sc[j - 1] < v) { sc[j] = sc[j - 1]; m.c[j] = m.c[j - 1]; j--; }
        sc[j] = v; m.c[j] = (uint8_t)c;
    }
    return m;
}

/* ------------------------------------------------------------ search */
typedef struct { uint64_t key; int32_t score; int8_t depth; uint8_t flag; uint8_t move; } TTE;
typedef struct { int score, move; long long nodes; int cut; } Res;   /* cut: budget ran out */

static Res leaf(int score, int move) { return (Res){score, move, 1, 0}; }
static Res negate(Res r, int move) { return (Res){-r.score, move, r.nodes + 1, r.cut}; }

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
    uint8_t seen[N] = {0};
    for (int l = 0; l < NL && a < beta; l++) {
        if (p->line[l] != 3) continue;
        for (int t = 0; t < 5 && a < beta; t++) {
            const int c = G->cells[l][t];
            if (p->owner[c] || seen[c]) continue;
            seen[c] = 1;
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
    const Moves m = ordered_moves(G, p, hit ? seen.move : -1);
    const int width = ply == 0 ? m.n : (depth >= 3 ? 16 : 24);
    const int n = m.n < width ? m.n : width;
    int a = alpha, best = -WIN - 1, bm = m.c[0];
    long long nodes = 1;
    for (int i = 0; i < n && a < beta; i++) {
        const Pos next = play(G, p, m.c[i]);
        const Res r = search(G, tt, &next, depth - 1, -beta, -a, ply + 1, budget - nodes);
        nodes += r.nodes;
        if (r.cut) return (Res){best, bm, nodes, 1};
        if (-r.score > best) { best = -r.score; bm = m.c[i]; }
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
    const Moves fallback = ordered_moves(G, p, -1);
    MoveInfo mi = {fallback.c[0], 0, 0, 0};
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
        const Moves m = ordered_moves(G, p, mi.move);
        mi.move = m.c[dice % (uint64_t)(m.n < 3 ? m.n : 3)];
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
    Pos p = empty_pos();
    for (int i = 0; i < g->nmoves; i++) { const Pos next = play(G, &p, g->moves[i]); p = next; }
    return p;
}

static Game parse_game(const char *s) {
    Game g = new_game(-1);
    const char *p = strstr(s, "\"id\":");
    if (!p) return g;
    g.id = atoi(p + 5);
    g.done = strstr(s, "\"status\":\"done\"") != NULL;
    p = strstr(s, "\"result\":\"");
    if (p) sscanf(p + 10, "%11[^\"]", g.result);
    p = strstr(s, "\"moves\":[");
    if (p)
        for (p += 9; *p && *p != ']'; p += *p == ',')
            g.moves[g.nmoves++] = (uint8_t)strtol(p, (char **)&p, 10);
    return g;
}

/* ------------------------------------------------------------ effects: main only */
static volatile sig_atomic_t stop_flag = 0;
static void on_sigint(int s) { (void)s; stop_flag = 1; }

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
    const char *out = "mb_games.jsonl";
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--games")) games = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--threads")) threads = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--nm")) nm = atoll(argv[++i]);
        else if (!strcmp(argv[i], "--nb")) nb = atoll(argv[++i]);
        else if (!strcmp(argv[i], "--random-plies")) random_plies = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--out")) out = argv[++i];
        else if (!strcmp(argv[i], "--resume")) resume = 1;
        else { fprintf(stderr, "unknown option %s\n", argv[i]); return 2; }
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
                const Game g = parse_game(line);
                if (g.id >= 0 && g.id < games) {
                    Game h = new_game(g.id);          /* rebuild the potential trace */
                    Pos r = empty_pos();
                    for (int k = 0; k < g.nmoves; k++) {
                        const Pos next = play(G, &r, g.moves[k]);
                        h = with_move(h, g.moves[k], next.pot);
                        r = next;
                    }
                    gs[g.id] = g.done ? with_result(h, g.result) : h;
                }
            }
            free(line);
            fclose(in);
        }
    }
    int todo = 0;
    for (int i = 0; i < games; i++) todo += !gs[i].done;
    FILE *f = fopen(out, "a");
    if (!f) { perror(out); return 1; }
    printf("mb: Maker-Breaker on %d lines; %d games to play (%d done), %d threads; "
           "Maker %lld nodes/move, Breaker %lld nodes/move\n"
           "    estimate at ~2.5 M nodes/s per thread: about %.1f min wall for games of 70 plies, "
           "hard upper bound %.1f min (125 plies)\n",
           NL, todo, games - todo, threads, nm, nb,
           (double)((todo + threads - 1) / threads) * 35.0 * (double)(nm + nb) / 2.5e6 / 60.0,
           (double)((todo + threads - 1) / threads) * 62.5 * (double)(nm + nb) / 2.5e6 / 60.0);
    fflush(stdout);

    const double t0 = omp_get_wtime();
    double last = 0;
    long long nodes = 0, plies = 0;
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
                    printf("  [%6.1fs] done %d/%d (maker %d, breaker %d) | game %d ply %d %s->%d "
                           "depth %d score %d pot %d | %lld plies total | %.1f M nodes/s\n",
                           t - t0, ndone, todo, nmaker, nbreaker, g.id, g.nmoves, s ? "B" : "M",
                           mi.move, mi.depth, mi.score, p.pot, plies, (double)nodes / (t - t0) / 1e6);
                    fflush(stdout);
                }
            }
        }
#pragma omp critical(progress)
        {
            write_game(f, &g);
            if (g.done) {
                ndone++;
                if (!strcmp(g.result, "maker")) nmaker++; else nbreaker++;
                printf("  game %d: %s at ply %d (final pot %d)\n", g.id, g.result, g.nmoves, p.pot);
            } else {
                printf("  game %d: interrupted at ply %d, saved for --resume\n", g.id, g.nmoves);
            }
            fflush(stdout);
        }
        gs[gi] = g;
    }
    const double dt = omp_get_wtime() - t0;
    printf("finished: %d games this run, maker %d, breaker %d, %.1fs, %.1f M nodes/s, max depth %d\n",
           ndone, nmaker, nbreaker, dt, (double)nodes / (dt + 1e-9) / 1e6, maxdepth);
    fclose(f);
    free(gs);
    return 0;
}
