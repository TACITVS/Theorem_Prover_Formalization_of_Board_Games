/* Research 032: df-pn proof search for the Maker-Breaker game on 5x5x5 (Q0).
 *
 * Question answered per position: does Maker win, or does Breaker? Unlike the
 * engine `mb.c`, this search is exact: full width, no depth limit, and a
 * position is "solved" only when its whole AND/OR tree is closed. (It relies on
 * 64-bit position hashes, so a result is still evidence until Rocq checks a
 * certificate.)
 *
 * Algorithm: depth-first proof-number search (Nagai 2002) in negamax form,
 * with the 1+epsilon threshold of Pawlewicz and Lew (2007) against thrashing.
 *   phi(n)   = effort to prove that the side to move at n wins
 *   delta(n) = effort to prove that it loses
 *   phi(n) = min over children of delta,  delta(n) = sum over children of phi.
 * Maker's forcing sequences need no separate threat-space search here: a forced
 * Breaker reply is a node with one child, which proof numbers follow for free.
 *
 * Exact leaves:
 *   - Maker completes a line next move, or has two completion cells.
 *   - Erdos-Selfridge: potential below 32 (Breaker to move) or 16 (Maker).
 *   - Pairing: every live line gets two free cells of its own. Decided by
 *     maximum bipartite matching (Hopcroft-Karp 1973, O(E sqrt V)).
 * Sound pruning: a cell on no live line is never played. Such a move is a pass,
 * and in a Maker-Breaker game an extra stone never hurts its owner, so a pass
 * is no better than any other move.
 *
 * Job: for each game of an `mb.exe` output file, walk backwards from the final
 * position and solve the position after ply k, k-1, k-2, ... within a node
 * budget each. The first position that exceeds the budget closes the game. The
 * smallest solved ply is the game's "proof frontier".
 *
 * Style: functional, as in mb.c. `mid` is a pure function of its arguments
 * except for the transposition table, the memo that df-pn is built on. Effects
 * live in `main`.
 *
 * Control: progress every 2 s. Ctrl-C, the stop file, or --max-seconds end the
 * run cleanly: each open game writes its table to `<out>.g<id>.tt` and a
 * "partial" record; --resume reloads both, so no search effort is lost.
 *
 * Build: gcc -O3 -march=native -fopenmp dfpn.c -o dfpn.exe
 */
#define MB_ORD {1, 2, 4, 8, 16, 32}       /* score[c] = Erdos-Selfridge weight of cell c */
#include "mbcore.h"
#include <signal.h>
#include <omp.h>

#define INF 0x40000000u

/* ------------------------------------------------------------ transposition table */
typedef struct { uint64_t key; uint32_t phi, delta; } Ent;          /* key 0 = empty */
typedef struct { Ent *e; uint64_t nbuckets; } Table;                /* buckets of 4 = one cache line */

static inline uint64_t key_of(uint64_t hash) { return hash | 1; }
static inline Ent *bucket(const Table *t, uint64_t key) { return t->e + 4 * ((key >> 7) & (t->nbuckets - 1)); }

static inline Ent probe(const Table *t, uint64_t key) {
    const Ent *const b = bucket(t, key);
    for (int i = 0; i < 4; i++) if (b[i].key == key) return b[i];
    return (Ent){0, 1, 1};
}

/* The table's only write. Keeps solved entries; otherwise evicts the cheapest one. */
static inline void store(Table *t, uint64_t key, uint32_t phi, uint32_t delta) {
    Ent *const b = bucket(t, key);
    for (int i = 0; i < 4; i++)
        if (b[i].key == key || b[i].key == 0) { b[i] = (Ent){key, phi, delta}; return; }
    int victim = (int)(key >> 3 & 3);                     /* used if all four are solved */
    uint64_t cheapest = ~0ull;
    for (int i = 0; i < 4; i++) {
        if (b[i].phi == 0 || b[i].delta == 0) continue;
        const uint64_t cost = (uint64_t)b[i].phi + b[i].delta;
        if (cost < cheapest) { cheapest = cost; victim = i; }
    }
    b[victim] = (Ent){key, phi, delta};
}

/* ------------------------------------------------------------ exact leaves */
typedef struct { int16_t ml[2 * NL], mr[N], dist[2 * NL]; uint8_t line[2 * NL]; } Match;

static int hk_augment(const Geo *G, const Pos *p, Match *m, int u) {
    const uint8_t *const cs = G->cells[m->line[u]];
    for (int t = 0; t < 5; t++) {
        const int c = cs[t];
        if (taken(p, c)) continue;
        const int w = m->mr[c];
        if (w < 0 || (m->dist[w] == m->dist[u] + 1 && hk_augment(G, p, m, w))) {
            m->ml[u] = (int16_t)c; m->mr[c] = (int16_t)u;
            return 1;
        }
    }
    m->dist[u] = -2;
    return 0;
}

/* Can every live line be given two free cells of its own? (Hopcroft-Karp.) */
static int has_pairing(const Geo *G, const Pos *p) {
    Match m;
    int nl = 0;
    for (int l = 0; l < NL; l++) {
        if (p->line[l] == DEAD) continue;
        if (p->line[l] >= 4) return 0;                    /* one free cell left: cannot be paired */
        m.line[nl++] = (uint8_t)l; m.line[nl++] = (uint8_t)l;
    }
    if (nl > N - p->nstones) return 0;
    memset(m.ml, -1, sizeof m.ml);
    memset(m.mr, -1, sizeof m.mr);
    int matched = 0;
    for (int u = 0; u < nl; u++)                          /* greedy start */
        for (int t = 0; t < 5; t++) {
            const int c = G->cells[m.line[u]][t];
            if (!taken(p, c) && m.mr[c] < 0) { m.ml[u] = (int16_t)c; m.mr[c] = (int16_t)u; matched++; break; }
        }
    while (matched < nl) {
        int16_t queue[2 * NL];
        int head = 0, tail = 0, reach = 0;
        for (int u = 0; u < nl; u++) {
            m.dist[u] = m.ml[u] < 0 ? 0 : -1;
            if (m.ml[u] < 0) queue[tail++] = (int16_t)u;
        }
        while (head < tail) {                             /* layers of alternating paths */
            const int u = queue[head++];
            for (int t = 0; t < 5; t++) {
                const int c = G->cells[m.line[u]][t];
                if (taken(p, c)) continue;
                const int w = m.mr[c];
                if (w < 0) reach = 1;
                else if (m.dist[w] == -1) { m.dist[w] = (int16_t)(m.dist[u] + 1); queue[tail++] = (int16_t)w; }
            }
        }
        if (!reach) return 0;
        int gained = 0;
        for (int u = 0; u < nl; u++) if (m.ml[u] < 0 && m.dist[u] == 0) gained += hk_augment(G, p, &m, u);
        if (!gained) return 0;
        matched += gained;
    }
    return 1;
}

/* +1: the side to move wins; -1: it loses; 0: not a leaf. `fresh` allows the
 * (costlier) pairing test, which is pointless on a node expanded before. */
static int leaf_value(const Geo *G, const Pos *p, const Fours *f, int fresh) {
    if (side(p) == 0) {
        if (f->n) return 1;
        if (p->pot < 16) return -1;
        return fresh && has_pairing(G, p) ? -1 : 0;
    }
    if (f->n >= 2) return -1;
    if (p->pot < 32) return 1;
    return fresh && f->n == 0 && has_pairing(G, p) ? 1 : 0;
}

/* ------------------------------------------------------------ df-pn */
typedef struct { uint32_t phi, delta; long long nodes; } DRes;

static inline uint32_t sat(uint64_t x) { return x >= INF ? INF : (uint32_t)x; }

/* First numbers for a child never seen: exact if Erdos-Selfridge already
 * decides it, otherwise "Breaker's task grows with the potential above the bar". */
static inline Ent first_guess(int child_side, int child_pot) {
    const int bar = child_side ? 32 : 16;
    if (child_pot < bar) return child_side ? (Ent){0, 0, INF} : (Ent){0, INF, 0};
    const uint32_t breaker_work = 1 + (uint32_t)(child_pot - bar) / 8;
    return child_side ? (Ent){0, breaker_work, 1} : (Ent){0, 1, breaker_work};
}

static DRes mid(const Geo *G, Table *T, const Pos *p, uint32_t th_phi, uint32_t th_delta,
                long long budget, int fresh) {
    const int s = side(p);
    const uint64_t key = key_of(p->hash);
    const Fours f = fours(G, p);
    const int lv = leaf_value(G, p, &f, fresh);
    if (lv) {
        const DRes r = {lv > 0 ? 0 : INF, lv > 0 ? INF : 0, 1};
        store(T, key, r.phi, r.delta);
        return r;
    }
    /* children: the forced block, or every free cell on a live line, heaviest first */
    uint8_t cell[N], isnew[N];
    uint32_t cphi[N], cdelta[N];
    int n = 0;
    if (s == 1 && f.n == 1) cell[n++] = f.c[0];
    else {
        /* Counting sort by weight (1..255), linear time. Bucket k = 255 - weight,
           so heavy cells come first; within a bucket cells stay in index order.
           Weight 0 means a dead cell: dropped. */
        int start[257] = {0};
        for (int w = 0; w < 2; w++)
            for (uint64_t b = ~p->occ[w]; b; b &= b - 1) {
                const int sc = p->score[64 * w + (int)_tzcnt_u64(b)];
                if (sc) start[256 - (sc > 255 ? 255 : sc)]++;
            }
        for (int i = 1; i < 257; i++) start[i] += start[i - 1];
        n = start[256];
        for (int w = 0; w < 2; w++)
            for (uint64_t b = ~p->occ[w]; b; b &= b - 1) {
                const int c = 64 * w + (int)_tzcnt_u64(b), sc = p->score[c];
                if (sc) cell[start[255 - (sc > 255 ? 255 : sc)]++] = (uint8_t)c;
            }
    }
    for (int i = 0; i < n; i++)
        _mm_prefetch((const char *)bucket(T, key_of(p->hash ^ G->zob[s][cell[i]])), _MM_HINT_T0);
    uint64_t sum = 0;
    for (int i = 0; i < n; i++) {
        const int c = cell[i];
        const Ent hit = probe(T, key_of(p->hash ^ G->zob[s][c]));
        const Ent e = hit.key ? hit : first_guess(1 - s, s == 0 ? p->pot + p->score[c] : p->pot - p->score[c]);
        isnew[i] = !hit.key;
        cphi[i] = e.phi; cdelta[i] = e.delta;
        sum += e.phi;
    }
    long long nodes = 1;
    uint32_t phi, delta;
    for (;;) {
        int best = 0;
        uint32_t d1 = INF + 1, d2 = INF + 1;              /* smallest and second smallest child delta */
        for (int i = 0; i < n; i++) {
            if (cdelta[i] < d1) { d2 = d1; d1 = cdelta[i]; best = i; }
            else if (cdelta[i] < d2) d2 = cdelta[i];
        }
        phi = sat(d1); delta = sat(sum);
        if (phi == 0 || delta == 0 || phi >= th_phi || delta >= th_delta || nodes >= budget) break;
        const uint32_t c_phi = th_delta >= INF ? INF : sat((uint64_t)th_delta - delta + cphi[best]);
        const uint64_t eps = (uint64_t)d2 + 1 + d2 / 4;
        const uint32_t c_delta = d2 >= INF || eps >= th_phi ? th_phi : (uint32_t)eps;
        const Pos next = play(G, p, cell[best]);
        /* Pairing test only after a Breaker move: a Maker move keeps every live
           line and removes a free cell, so it cannot create a pairing. */
        const DRes r = mid(G, T, &next, c_phi, c_delta, budget - nodes, isnew[best] && s == 1);
        sum += (uint64_t)r.phi - cphi[best];
        cphi[best] = r.phi; cdelta[best] = r.delta; isnew[best] = 0;
        nodes += r.nodes;
    }
    store(T, key, phi, delta);
    return (DRes){phi, delta, nodes};
}

/* ------------------------------------------------------------ jobs */
typedef struct { int id, nmoves; uint8_t moves[N]; } Game;
typedef struct { int next_ply, closed; long long used; } Progress;   /* where a game's walk stands */

static Pos position_at(const Geo *G, const Game *g, int ply) {
    Pos p = empty_pos(G);
    for (int i = 0; i < ply; i++) { const Pos next = play(G, &p, g->moves[i]); p = next; }
    return p;
}

/* Which exact leaf decides the position on its own, or "search" if none does.
 * Recomputed from the position: a one-node result can also come from the table. */
static const char *how_solved(const Geo *G, const Pos *p) {
    const Fours f = fours(G, p);
    if (!leaf_value(G, p, &f, 1)) return "search";
    if (side(p) == 0 ? f.n > 0 : f.n >= 2) return "threat";
    return p->pot < (side(p) ? 32 : 16) ? "es" : "pairing";
}

static Game parse_game(const char *s) {
    Game g = {-1, 0, {0}};
    const char *p = strstr(s, "\"id\":");
    if (!p || !strstr(s, "\"status\":\"done\"")) return g;
    g.id = atoi(p + 5);
    p = strstr(s, "\"moves\":[");
    if (p)
        for (p += 9; *p && *p != ']' && g.nmoves < N; p += *p == ',')
            g.moves[g.nmoves++] = (uint8_t)strtol(p, (char **)&p, 10);
    return g;
}

/* ------------------------------------------------------------ effects: main only */
static volatile sig_atomic_t stop_flag = 0;
static void on_sigint(int s) { (void)s; stop_flag = 1; }

static int file_exists(const char *path) {
    FILE *f = fopen(path, "rb");
    if (f) fclose(f);
    return f != NULL;
}

int main(int argc, char **argv) {
    int threads = 22, tt_bits = 23, resume = 0, from_ply = -1, min_ply = 0, max_games = 1 << 30;
    long long budget = 20000000, slice = 500000;
    double max_seconds = 540;
    const char *in = NULL, *out = "dfpn.jsonl", *stop_file = "STOP";
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--games")) in = argv[++i];
        else if (!strcmp(argv[i], "--out")) out = argv[++i];
        else if (!strcmp(argv[i], "--threads")) threads = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--budget")) budget = atoll(argv[++i]);
        else if (!strcmp(argv[i], "--tt-bits")) tt_bits = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--from-ply")) from_ply = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--min-ply")) min_ply = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--max-games")) max_games = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--max-seconds")) max_seconds = atof(argv[++i]);
        else if (!strcmp(argv[i], "--stop-file")) stop_file = argv[++i];
        else if (!strcmp(argv[i], "--resume")) resume = 1;
        else { fprintf(stderr, "unknown option %s\n", argv[i]); return 2; }
    }
    if (!in) { fprintf(stderr, "usage: dfpn --games mb_games.jsonl [--budget N] [--resume] ...\n"); return 2; }
    if (file_exists(stop_file)) { fprintf(stderr, "stop file '%s' exists; delete it to run\n", stop_file); return 3; }
    const Geo geo = make_geo();
    const Geo *const G = &geo;
    signal(SIGINT, on_sigint);

    enum { MAXG = 4096 };
    Game *const gs = malloc(MAXG * sizeof(Game));
    Progress *const pr = malloc(MAXG * sizeof(Progress));
    int ng = 0;
    char *const line = malloc(1 << 16);
    FILE *fi = fopen(in, "r");
    if (!fi) { perror(in); return 1; }
    while (ng < MAXG && ng < max_games && fgets(line, 1 << 16, fi)) {
        const Game g = parse_game(line);
        if (g.id < 0) continue;
        gs[ng] = g;
        pr[ng] = (Progress){from_ply >= 0 && from_ply < g.nmoves ? from_ply : g.nmoves, 0, 0};
        ng++;
    }
    fclose(fi);
    if (resume && (fi = fopen(out, "r"))) {                /* replay our own records, in order */
        while (fgets(line, 1 << 16, fi)) {
            const char *p = strstr(line, "\"id\":"), *q = strstr(line, "\"ply\":"), *u = strstr(line, "\"nodes\":");
            if (!p || !q || !u) continue;
            for (int i = 0; i < ng; i++) {
                if (gs[i].id != atoi(p + 5)) continue;
                if (strstr(line, "\"status\":\"partial\"")) pr[i] = (Progress){atoi(q + 6), 0, atoll(u + 8)};
                else if (strstr(line, "\"result\":\"unknown\"")) pr[i].closed = 1;
                else pr[i] = (Progress){atoi(q + 6) - 1, 0, 0};
            }
        }
        fclose(fi);
    }
    int open_games = 0;
    for (int i = 0; i < ng; i++) { pr[i].closed |= pr[i].next_ply < min_ply; open_games += !pr[i].closed; }
    FILE *fo = fopen(out, "a");
    if (!fo) { perror(out); return 1; }
    const double tt_mb = (double)(16ull << tt_bits) / 1048576.0;
    const int active = threads < open_games ? threads : open_games;
    printf("dfpn: %d games (%d open), %d threads, budget %lld nodes per position, table %.0f MB "
           "per thread (%.1f GB in all)\n"
           "    each game walks back from its last position until one position exceeds the budget\n"
           "    wall-clock cap %.0f s, then a clean stop with tables saved; stop early with Ctrl-C "
           "or file '%s'; continue with --resume\n",
           ng, open_games, threads, budget, tt_mb, tt_mb * active / 1024.0, max_seconds, stop_file);
    fflush(stdout);

    const double t0 = omp_get_wtime();
    double last = 0;
    long long total_nodes = 0;
    int solved_positions = 0, closed_now = 0;
    omp_set_num_threads(threads);
#pragma omp parallel for schedule(dynamic, 1)
    for (int gi = 0; gi < ng; gi++) {
        if (pr[gi].closed || stop_flag) continue;
        const Game *const g = &gs[gi];
        char ttpath[600];
        snprintf(ttpath, sizeof ttpath, "%s.g%d.tt", out, g->id);
        Table T = {calloc((size_t)1 << tt_bits, sizeof(Ent)), (1ull << tt_bits) / 4};
        if (!T.e) { fprintf(stderr, "out of memory for table\n"); exit(1); }
        FILE *ft = resume ? fopen(ttpath, "rb") : NULL;
        if (ft) {                                          /* saved table from a stopped run */
            if (fread(T.e, sizeof(Ent), (size_t)1 << tt_bits, ft) != (size_t)1 << tt_bits)
                memset(T.e, 0, sizeof(Ent) << tt_bits);
            fclose(ft);
        }
        Progress me = pr[gi];
        while (!me.closed && !stop_flag) {
            const Pos root = position_at(G, g, me.next_ply);
            const double tp = omp_get_wtime();
            DRes r = {1, 1, 0};
            int first = me.used == 0;
            while (r.phi && r.delta && me.used < budget && !stop_flag) {
                const long long room = budget - me.used < slice ? budget - me.used : slice;
                const DRes part = mid(G, &T, &root, INF, INF, room, first);
                first = 0;
                r = (DRes){part.phi, part.delta, r.nodes + part.nodes};
                me.used += part.nodes;
#pragma omp critical(progress)
                {
                    total_nodes += part.nodes;
                    const double t = omp_get_wtime();
                    if (t - t0 > max_seconds || (t - last >= 2.0 && file_exists(stop_file))) stop_flag = 1;
                    if (t - last >= 2.0) {
                        last = t;
                        const double rate = (double)total_nodes / (t - t0);
                        printf("  [%6.1fs] %d positions solved, %d/%d games closed | game %d ply %d: "
                               "%.1f/%.1f M nodes, phi %u delta %u | %.1f M nodes/s | this position "
                               "ends in <= %.0fs, wall cap in %.0fs\n",
                               t - t0, solved_positions, closed_now, open_games, g->id, me.next_ply,
                               (double)me.used / 1e6, (double)budget / 1e6, part.phi, part.delta,
                               rate / 1e6, (double)(budget - me.used) / (rate / active + 1.0),
                               max_seconds - (t - t0));
                        fflush(stdout);
                    }
                }
            }
            const int solved = !r.phi || !r.delta;
            const int stopped = !solved && me.used < budget;
            const int stm_wins = r.phi == 0;
            const char *result = !solved ? (stopped ? "open" : "unknown")
                               : (side(&root) == 0) == stm_wins ? "maker" : "breaker";
#pragma omp critical(progress)
            {
                fprintf(fo, "{\"id\":%d,\"ply\":%d,\"status\":\"%s\",\"result\":\"%s\",\"how\":\"%s\","
                            "\"nodes\":%lld,\"phi\":%u,\"delta\":%u,\"secs\":%.2f}\n",
                        g->id, me.next_ply, stopped ? "partial" : "done", result,
                        solved ? how_solved(G, &root) : "search", me.used, r.phi, r.delta,
                        omp_get_wtime() - tp);
                fflush(fo);
                if (solved) solved_positions++;
                if (!solved && !stopped) {
                    closed_now++;
                    printf("  game %d: frontier at ply %d of %d (ply %d not solved in %lld nodes)\n",
                           g->id, me.next_ply + 1, g->nmoves, me.next_ply, budget);
                    fflush(stdout);
                }
            }
            if (stopped) break;
            me = solved ? (Progress){me.next_ply - 1, me.next_ply - 1 < min_ply, 0}
                        : (Progress){me.next_ply, 1, me.used};
            if (solved && me.closed) {
#pragma omp critical(progress)
                { closed_now++; printf("  game %d: solved down to ply %d\n", g->id, min_ply); fflush(stdout); }
            }
        }
        if (!me.closed) {                                  /* stopped: keep the table for --resume */
            FILE *fw = fopen(ttpath, "wb");
            if (fw) { fwrite(T.e, sizeof(Ent), (size_t)1 << tt_bits, fw); fclose(fw); }
        } else remove(ttpath);
        free(T.e);
        pr[gi] = me;
    }
    const double dt = omp_get_wtime() - t0;
    printf("%s: %d positions solved, %d games closed, %.1fs, %.1f M nodes/s\n",
           stop_flag ? "STOPPED (tables saved; run again with --resume)" : "finished",
           solved_positions, closed_now, dt, (double)total_nodes / (dt + 1e-9) / 1e6);
    fclose(fo);
    free(line); free(gs); free(pr);
    return 0;
}
