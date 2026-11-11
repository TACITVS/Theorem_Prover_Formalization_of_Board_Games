/* Research 032: shared core for the Maker-Breaker programs (mb.c, dfpn.c).
 *
 * Immutable positions on bitboards and AVX2. Everything here is a pure function.
 * Define MB_ORD before including to choose the per-line weights behind
 * Pos.score (mb.c: move-ordering weights; dfpn.c: 2^v, the Erdos-Selfridge
 * weight, so that score[c] is exactly the potential a stone on c adds or removes).
 */
#ifndef MBCORE_H
#define MBCORE_H
#include <immintrin.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef __AVX2__
#error "needs AVX2"
#endif

#define N 125
#define NL 109
#define DEAD 255

/* ------------------------------------------------------------ geometry */
typedef struct {
    uint8_t cells[NL][5];        /* the five cells of each line */
    uint8_t of[N][13];           /* the lines through each cell */
    uint8_t nof[N];
    uint64_t mask[NL][2];        /* each line as a 125-bit set of cells */
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
        for (int t = 0; t < 5; t++) {
            const int c = g.cells[l][t];
            g.of[c][g.nof[c]++] = (uint8_t)l;
            g.mask[l][c >> 6] |= 1ull << (c & 63);
        }
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
    _Alignas(32) uint8_t line[128];  /* Maker stones on the line; DEAD once Breaker is on it */
    uint16_t score[128];             /* per cell: sum of ORD over the live lines through it */
    uint64_t occ[2];                 /* occupied cells; bits 125..127 are always set */
    uint64_t hash;
    int32_t pot;                     /* exact Erdos-Selfridge potential */
    int32_t ev;                      /* heuristic value, Maker's view */
    int16_t nstones;                 /* side to move = nstones & 1 (0 Maker, 1 Breaker) */
    int16_t n4;                      /* live lines with four Maker stones */
} Pos;

static const int VAL[6] = {1, 3, 12, 80, 600, 5000};
#ifndef MB_ORD
#define MB_ORD {1, 6, 40, 400, 4000, 4000}
#endif
static const int ORD[6] = MB_ORD;      /* weight of a live line with v Maker stones */

static Pos empty_pos(const Geo *G) {
    Pos p;
    memset(&p, 0, sizeof p);
    memset(p.line + NL, DEAD, 128 - NL);
    for (int c = 0; c < N; c++) p.score[c] = (uint16_t)(G->nof[c] * ORD[0]);
    p.occ[1] = 7ull << 61;
    p.pot = NL;
    p.ev = NL * VAL[0];
    return p;
}

static inline int side(const Pos *p) { return p->nstones & 1; }
static inline int taken(const Pos *p, int c) { return (int)(p->occ[c >> 6] >> (c & 63)) & 1; }

/* The position after the side to move takes cell c. The argument is untouched. */
static inline Pos play(const Geo *G, const Pos *p, int c) {
    const int s = side(p);
    Pos q = *p;
    q.occ[c >> 6] |= 1ull << (c & 63);
    q.hash ^= G->zob[s][c];
    q.nstones++;
    for (int i = 0; i < G->nof[c]; i++) {
        const int l = G->of[c][i], v = p->line[l];
        if (v == DEAD) continue;
        const uint8_t *const cs = G->cells[l];
        int d;
        if (s == 0) {
            q.pot += 1 << v; q.ev += VAL[v + 1] - VAL[v]; q.line[l] = (uint8_t)(v + 1);
            q.n4 += (v == 3) - (v == 4);
            d = ORD[v + 1] - ORD[v];
        } else {
            q.pot -= 1 << v; q.ev -= VAL[v]; q.line[l] = DEAD;
            q.n4 -= v == 4;
            d = -ORD[v];
        }
        for (int t = 0; t < 5; t++) q.score[cs[t]] = (uint16_t)(q.score[cs[t]] + d);
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

/* Lines whose state byte equals v, as four 32-bit masks (line l = bit l%32 of word l/32). */
typedef struct { uint32_t w[4]; } LineSet;

static inline LineSet lines_with(const Pos *p, int v) {
    const __m256i x = _mm256_set1_epi8((char)v);
    LineSet s;
    for (int j = 0; j < 4; j++)
        s.w[j] = (uint32_t)_mm256_movemask_epi8(
            _mm256_cmpeq_epi8(_mm256_load_si256((const __m256i *)(p->line + 32 * j)), x));
    return s;
}

/* The lowest free cell of line l (the line must have one). */
static inline int free_cell(const Geo *G, const Pos *p, int l) {
    const uint64_t lo = G->mask[l][0] & ~p->occ[0];
    return lo ? (int)_tzcnt_u64(lo) : 64 + (int)_tzcnt_u64(G->mask[l][1] & ~p->occ[1]);
}

/* Cells where Maker would complete a line (distinct, at most 16 reported). */
typedef struct { int n; uint8_t c[16]; } Fours;

static inline Fours fours(const Geo *G, const Pos *p) {
    Fours f;
    f.n = 0;
    if (!p->n4) return f;
    const LineSet s = lines_with(p, 4);
    for (int j = 0; j < 4; j++)
        for (uint32_t w = s.w[j]; w; w &= w - 1) {
            const int c = free_cell(G, p, 32 * j + (int)_tzcnt_u32(w));
            int dup = 0;
            for (int k = 0; k < f.n; k++) dup |= f.c[k] == c;
            if (!dup && f.n < 16) f.c[f.n++] = (uint8_t)c;
        }
    return f;
}

#endif
