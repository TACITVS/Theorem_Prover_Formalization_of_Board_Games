/* Strategy DISCOVERY tool (not the proof).
   Finds a shallow opening tree for defender DEF whose leaves are covered by
   follow-up structures whose soundness is proved deductively in Rocq:

   R1 (weak follow-up, any defender, any parity):
      disjoint units, each a vertical domino or a "base pair" of two currently
      playable cells; every live attacker line contains a whole unit.
   R2 (claimeven follow-up, defender is the responder, attacker to move):
      every column is FULL, RIGID (even #empty: dominoes from the bottom,
      defender gets every upper cell), FREE, or part of a CHAIN with a partner
      column (t lock-step cross pairs from the bottoms, then rigid dominoes).
      FREE columns carry an R1 structure.  Lines must contain a guaranteed
      cell or a whole pair. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#ifndef W
#define W 8
#endif
#ifndef H
#define H 8
#endif
#ifndef K
#define K 5
#endif
#define H1 8
#define NCELL (W * H)
typedef uint64_t u64;
typedef unsigned __int128 LS;
#define BIT(c, r) (1ULL << ((c) * H1 + (r)))
#define ctz __builtin_ctzll
#define popc __builtin_popcountll

static u64 BOTTOM, FULL, COLMASK[W], TOPCELL[W];
static u64 LINES[256];
static int LINECOLS[256];
static int NL;
static LS CELL_LINES[64];
static LS ALL_LINES;

static void init(void) {
  for (int c = 0; c < W; c++) {
    COLMASK[c] = ((1ULL << H) - 1) << (c * H1);
    TOPCELL[c] = BIT(c, H - 1);
    BOTTOM |= BIT(c, 0);
    FULL |= COLMASK[c];
  }
  int D[4][2] = {{0, 1}, {1, 0}, {1, 1}, {1, -1}};
  for (int d = 0; d < 4; d++)
    for (int c = 0; c < W; c++)
      for (int r = 0; r < H; r++) {
        int ec = c + (K - 1) * D[d][0], er = r + (K - 1) * D[d][1];
        if (ec < 0 || ec >= W || er < 0 || er >= H) continue;
        u64 m = 0; int cols = 0;
        for (int i = 0; i < K; i++) { m |= BIT(c + i * D[d][0], r + i * D[d][1]); cols |= 1 << (c + i * D[d][0]); }
        LINES[NL] = m; LINECOLS[NL] = cols; NL++;
      }
  for (int l = 0; l < NL; l++) {
    ALL_LINES |= (LS)1 << l;
    u64 m = LINES[l];
    while (m) { CELL_LINES[ctz(m)] |= (LS)1 << l; m &= m - 1; }
  }
}

typedef struct { u64 st[2]; u64 mask; int n; } Pos;
static inline u64 playable(const Pos *p) { return (((p->mask & 0x7F7F7F7F7F7F7F7FULL) + BOTTOM) & FULL) & ~p->mask; }
static inline int height(const Pos *p, int c) { return popc(p->mask & COLMASK[c]); }
static inline int has_line(u64 s) {
  for (int l = 0; l < NL; l++) if ((LINES[l] & s) == LINES[l]) return 1;
  return 0;
}
static inline u64 win_cells(const Pos *p, int P) {
  u64 s = p->st[P], o = p->st[1 - P], w = 0;
  for (int l = 0; l < NL; l++) {
    u64 L = LINES[l];
    if (L & o) continue;
    u64 e = L & ~s;
    if (e && !(e & (e - 1))) w |= e;
  }
  return w & playable(p);
}
static inline LS lines_any(u64 m) { LS r = 0; while (m) { r |= CELL_LINES[ctz(m)]; m &= m - 1; } return r; }
static inline LS lines_pair(u64 a, u64 b) { return CELL_LINES[ctz(a)] & CELL_LINES[ctz(b)]; }
static LS live_lines(const Pos *p, int D) {
  LS r = 0;
  for (int l = 0; l < NL; l++) if (!(LINES[l] & p->st[D])) r |= (LS)1 << l;
  return r;
}

/* ---------------- R1: weak units restricted to column set ---------------- */
/* (call counters removed: rules are shared by worker threads) */
typedef struct { u64 cells; LS hit; } Unit;
static int r1_rec(Unit *U, int nu, u64 used, LS need, int budget[1]) {
  if (!need) return 1;
  if (--budget[0] < 0) return 0;
  /* pick uncovered line with fewest candidate units */
  int best = -1, bestn = 1 << 30;
  LS nd = need;
  while (nd) {
    int l = (int)(((u64)nd) ? ctz((u64)nd) : 64 + ctz((u64)(nd >> 64)));
    nd &= nd - 1;
    int n = 0;
    for (int u = 0; u < nu; u++) if (!(U[u].cells & used) && ((U[u].hit >> l) & 1)) n++;
    if (n < bestn) { bestn = n; best = l; if (n == 0) return 0; }
  }
  for (int u = 0; u < nu; u++) {
    if ((U[u].cells & used) || !((U[u].hit >> best) & 1)) continue;
    if (r1_rec(U, nu, used | U[u].cells, need & ~U[u].hit, budget)) return 1;
  }
  return 0;
}
static const int TOP_ALL[W] = {[0 ... W - 1] = H};
/* top[c] = exclusive upper bound of usable rows in column c */
static int r1_solve_top(const Pos *p, int colset, LS need, const int *top) {

  if (!need) return 1;
  Unit U[200]; int nu = 0;
  u64 empty = FULL & ~p->mask;
  for (int c = 0; c < W; c++) {
    if (!((colset >> c) & 1)) continue;
    for (int r = 0; r + 1 < top[c]; r++) {
      u64 a = BIT(c, r), b = BIT(c, r + 1);
      if ((a & empty) && (b & empty)) { LS h = lines_pair(a, b) & need; if (h) { U[nu].cells = a | b; U[nu].hit = h; nu++; } }
    }
  }
  u64 pb = playable(p);
  for (int a = 0; a < W; a++) {
    if (!((colset >> a) & 1)) continue;
    u64 ba = pb & COLMASK[a];
    if (!ba || ctz(ba) - a * H1 >= top[a]) continue;
    for (int b = a + 1; b < W; b++) {
      if (!((colset >> b) & 1)) continue;
      u64 bb = pb & COLMASK[b];
      if (!bb || ctz(bb) - b * H1 >= top[b]) continue;
      LS h = lines_pair(ba, bb) & need;
      if (h) { U[nu].cells = ba | bb; U[nu].hit = h; nu++; }
    }
  }
  LS can = 0;
  for (int u = 0; u < nu; u++) can |= U[u].hit;
  if ((can & need) != need) return 0;
  int budget[1] = {200000};
  return r1_rec(U, nu, 0, need, budget);
}
static int r1_solve(const Pos *p, int colset, LS need) { return r1_solve_top(p, colset, need, TOP_ALL); }

/* ---------------- R2/R3: claimeven structure (thread-safe context) -------- */
#define R2MEMO 2048
typedef struct {
  int h[W], m[W], top[W];
  LS live;
  const Pos *p;
  int budget;
  unsigned gen;
  struct { u64 k0, k1; unsigned gen; } memo[R2MEMO];
} R2Ctx;

static inline u64 colG(const R2Ctx *x, int c, int from) { /* uppers of rigid dominoes */
  u64 g = 0;
  for (int r = from + 1; r < x->top[c]; r += 2) g |= BIT(c, r);
  return g;
}
static int r2_rec(R2Ctx *x, int c, int assigned, int freecols, LS covered) {
  if (--x->budget < 0) return 0;
  int hard = assigned & ~freecols;
  LS unc = x->live & ~covered;
  {
    LS nd = unc;
    while (nd) {
      int l = (int)(((u64)nd) ? ctz((u64)nd) : 64 + ctz((u64)(nd >> 64)));
      nd &= nd - 1;
      if ((LINECOLS[l] & ~hard) == 0) return 0;
    }
  }
  while (c < W && ((assigned >> c) & 1)) c++;
  if (c == W) {
    int F = 0;
    for (int i = 0; i < W; i++) if ((freecols >> i) & 1) F += x->m[i];
    if (F & 1) return 0;
    return r1_solve_top(x->p, freecols, unc, x->top);
  }
  /* memo of failed states */
  u64 k0 = (u64)covered ^ ((u64)assigned << 48) ^ ((u64)freecols << 56);
  u64 k1 = (u64)(covered >> 64) ^ ((u64)c << 60);
  unsigned slot = (unsigned)((k0 * 0x9E3779B97F4A7C15ULL ^ k1 * 0xC2B2AE3D27D4EB4FULL) >> 40) & (R2MEMO - 1);
  if (x->memo[slot].gen == x->gen && x->memo[slot].k0 == k0 && x->memo[slot].k1 == k1) return 0;
  int m = x->m[c], h = x->h[c];
  int ok = 0;
  if (m == 0) ok = r2_rec(x, c + 1, assigned | (1 << c), freecols, covered);
  else {
    if (m % 2 == 0)
      ok = r2_rec(x, c + 1, assigned | (1 << c), freecols, covered | (lines_any(colG(x, c, h)) & x->live));
    for (int b = c + 1; b < W && !ok; b++) {
      if ((assigned >> b) & 1) continue;
      int mb = x->m[b], hb = x->h[b];
      if (mb == 0) continue;
      for (int t = 1; t <= m && t <= mb && !ok; t++) {
        if ((m - t) % 2 || (mb - t) % 2) continue;
        LS cov = covered;
        for (int i = 0; i < t; i++) cov |= lines_pair(BIT(c, h + i), BIT(b, hb + i));
        cov |= lines_any(colG(x, c, h + t) | colG(x, b, hb + t));
        cov &= x->live;
        ok = r2_rec(x, c + 1, assigned | (1 << c) | (1 << b), freecols, cov);
      }
    }
    if (!ok) ok = r2_rec(x, c + 1, assigned | (1 << c), freecols | (1 << c), covered);
  }
  if (!ok) { x->memo[slot].gen = x->gen; x->memo[slot].k0 = k0; x->memo[slot].k1 = k1; }
  return ok;
}
/* fc = frozen column (-1 none), ft = row of the defender threat cell in fc. */
static int r2_solve(R2Ctx *x, const Pos *p, int D, int fc, int ft) {
  x->p = p;
  x->gen++;
  x->live = live_lines(p, D);
  for (int c = 0; c < W; c++) { x->h[c] = height(p, c); x->top[c] = H; }
  if (fc >= 0) {
    x->top[fc] = ft - 1;
    u64 dead = 0;
    for (int r = ft; r < H; r++) dead |= BIT(fc, r);
    x->live &= ~lines_any(dead);
  }
  for (int c = 0; c < W; c++) x->m[c] = x->top[c] - x->h[c];
  if (!x->live) return 1;
  int max_pairs = (NCELL - p->n) / 2;
  int num_live = popc((u64)x->live) + popc((u64)(x->live >> 64));
  if (num_live > max_pairs * 4) return 0;
  x->budget = (p->n <= 4) ? 5000 : (p->n <= 8) ? 25000 : 100000;
  return r2_rec(x, 0, 0, 0, 0);
}

/* defender threat cells: empty, not playable, completing a defender line */
static u64 threat_cells(const Pos *p, int P) {
  u64 s = p->st[P], o = p->st[1 - P], w = 0;
  for (int l = 0; l < NL; l++) {
    u64 L = LINES[l];
    if (L & o) continue;
    u64 e = L & ~s;
    if (e && !(e & (e - 1))) w |= e;
  }
  return w & ~p->mask & ~playable(p);
}

/* ---------------- leaf test ----------------
   returns 0 = no rule, 1 = R1 (weak follow-up / dead), 2 = R2 (claimeven),
   3 = R3 (claimeven anchored by a defender threat).  Fills *fc,*ft for R3. */
static int DEF;
static int USE_R2 = 1;
static long long r1calls = 0, r2calls = 0;
static R2Ctx DEFAULT_R2_CTX;

static int leaf_x(R2Ctx *x, const Pos *p, int *ofc, int *oft) {
  int side = p->n & 1;
  LS live = live_lines(p, DEF);
  if (!live) return 1;
  __atomic_fetch_add(&r1calls, 1, __ATOMIC_RELAXED);
  if (r1_solve(p, (1 << W) - 1, live)) return 1;
  if (!USE_R2 || side == DEF) return 0;
  int E = NCELL - p->n;
  if (E % 2 == 0) {
    __atomic_fetch_add(&r2calls, 1, __ATOMIC_RELAXED);
    if (r2_solve(x, p, DEF, -1, 0)) return 2;
  }
  u64 th = threat_cells(p, DEF);
  while (th) {
    int i = ctz(th); th &= th - 1;
    int c = i / H1, r = i % H1;
    int Z = H - r + 1;
    if ((E - Z) % 2) continue;
    __atomic_fetch_add(&r2calls, 1, __ATOMIC_RELAXED);
    if (r2_solve(x, p, DEF, c, r)) { if (ofc) { *ofc = c; *oft = r; } return 3; }
  }
  return 0;
}

static inline int leaf(const Pos *p) {
  return leaf_x(&DEFAULT_R2_CTX, p, NULL, NULL);
}

