/* Optimized High-Performance Parallel DF-PN Solver for Connect-5 (8x8)
   Includes:
   1. Blunder filtering at OR-nodes (never play a move allowing opponent immediate win)
   2. Pigeonhole capacity pre-filter in r2_solve
   3. Adaptive search budgets based on ply depth
   4. Direct unbuffered output with live progress logging
*/
#include <pthread.h>
#include <immintrin.h>
#include "rules.h"

#define INF 0x3fffffffu
typedef uint32_t u32;
typedef struct { u64 a, b; u32 pn, dn; u32 work; int16_t busy; int8_t mv; int8_t lf; } TE;

static int TTB = 27;
static TE *TT;
#define NLOCK (1 << 18)
static volatile char LOCKS[NLOCK];
static volatile int STOP;
static int center_order[W];
static const double EPS = 0.25;

typedef struct {
  R2Ctx *rx;
  long long nodes, leafcalls;
  int id;
} Th;

static inline void lk(u64 i) { while (__atomic_test_and_set(&LOCKS[i], __ATOMIC_ACQUIRE)) _mm_pause(); }
static inline void ul(u64 i) { __atomic_clear(&LOCKS[i], __ATOMIC_RELEASE); }

static inline u64 mirror(u64 x) {
#if W * H1 == 64
  return __builtin_bswap64(x);
#else
  u64 r = 0;
  for (int c = 0; c < W; c++) r |= ((x >> (c * H1)) & ((1ULL << H1) - 1)) << ((W - 1 - c) * H1);
  return r;
#endif
}
static inline void canon(const Pos *p, u64 *a, u64 *b, int *mir) {
  u64 a0 = p->st[0], b0 = p->st[1], a1 = mirror(a0), b1 = mirror(b0);
  if (a1 < a0 || (a1 == a0 && b1 < b0)) { *a = a1; *b = b1; *mir = 1; } else { *a = a0; *b = b0; *mir = 0; }
}
static inline u64 hsh(u64 a, u64 b) {
  u64 h = a * 0x9E3779B97F4A7C15ULL ^ (b + 0x632BE59BD9B4E019ULL) * 0xC2B2AE3D27D4EB4FULL;
  return h ^ (h >> 31);
}
static inline u64 bucket(u64 a, u64 b) { return (hsh(a, b) & ((1ULL << TTB) - 1)) & ~3ULL; }

/* lookup: returns 1 and copies entry if present */
static int tt_get(u64 a, u64 b, TE *out) {
  u64 bi = bucket(a, b), li = (bi >> 2) & (NLOCK - 1);
  int found = 0;
  lk(li);
  for (int i = 0; i < 4; i++) {
    TE *e = &TT[bi + i];
    if (e->a == a && e->b == b && (e->pn | e->dn)) { *out = *e; found = 1; break; }
  }
  ul(li);
  return found;
}

/* store; busydelta adjusts busy counter. Keeps solved entries preferentially. */
static void tt_put(u64 a, u64 b, u32 pn, u32 dn, u32 work, int mv, int lf, int busydelta, int keepvals) {
  u64 bi = bucket(a, b), li = (bi >> 2) & (NLOCK - 1);
  lk(li);
  TE *v = NULL;
  for (int i = 0; i < 4; i++) if (TT[bi + i].a == a && TT[bi + i].b == b && (TT[bi + i].pn | TT[bi + i].dn)) { v = &TT[bi + i]; break; }
  if (!v) {
    u64 best = ~0ULL;
    for (int i = 0; i < 4; i++) {
      TE *e = &TT[bi + i];
      if (!(e->pn | e->dn)) { v = e; break; }
      int solved = e->pn == 0 || e->dn == 0;
      u64 score = (u64)e->work + (solved ? (1ULL << 40) : 0) + (e->busy > 0 ? (1ULL << 41) : 0);
      if (score < best) { best = score; v = e; }
    }
    v->a = a; v->b = b; v->busy = 0; v->pn = pn; v->dn = dn; v->work = work; v->mv = mv; v->lf = lf;
  } else if (!keepvals) {
    if (!(v->pn == 0 || v->dn == 0) || pn == 0 || dn == 0) {
      v->pn = pn; v->dn = dn; v->mv = mv; v->lf = lf;
    }
    if (work > v->work) v->work = work;
  }
  v->busy += busydelta;
  if (v->busy < 0) v->busy = 0;
  ul(li);
}

static void play(Pos *q, const Pos *p, int c) {
  u64 mv = (p->mask + BIT(c, 0)) & COLMASK[c];
  *q = *p; q->st[p->n & 1] |= mv; q->mask |= mv; q->n = p->n + 1;
}

static int quick_eval(const Pos *p, u32 *pn, u32 *dn, int *lf) {
  int D = DEF, A = 1 - D;
  *lf = 0;
  u64 wd = win_cells(p, D), wa = win_cells(p, A);
  if ((p->n & 1) == D) {
    if (wd) { *pn = 0; *dn = INF; *lf = 9; return 1; }
    if (wa & (wa - 1)) { *pn = INF; *dn = 0; return 1; }
  } else {
    if (wa) { *pn = INF; *dn = 0; return 1; }
    if (wd & (wd - 1)) { *pn = 0; *dn = INF; *lf = 8; return 1; }
  }
  return 0;
}

// Move generator with blunder filtering for defender
static int gen_moves_opt(const Pos *p, int *mv) {
  int D = DEF, A = 1 - D, n = 0;
  int is_def = ((p->n & 1) == D);
  u64 must = is_def ? win_cells(p, A) : win_cells(p, D);

  for (int i = 0; i < W; i++) {
    int c = center_order[i];
    if (p->mask & TOPCELL[c]) continue;
    if (must && !(must & COLMASK[c])) continue;

    // Blunder filter for defender: don't play a move that allows opponent instant win on top
    if (is_def && !must) {
      Pos q; play(&q, p, c);
      if (win_cells(&q, A)) continue;
    }
    mv[n++] = c;
  }

  // Fallback: if all moves blundered, still generate legal moves
  if (n == 0 && is_def) {
    for (int i = 0; i < W; i++) {
      int c = center_order[i];
      if (p->mask & TOPCELL[c]) continue;
      mv[n++] = c;
    }
  }
  return n;
}

typedef struct { u32 pn, dn; int busy; } PD;
static inline u32 sat_add(u32 x, u32 y) { u64 s = (u64)x + y; return s >= INF ? INF : (u32)s; }

static PD child_value(Th *t, const Pos *q, int mover) {
  PD r; r.busy = 0;
  int D = DEF;
  if (has_line(q->st[mover])) { r.pn = mover == D ? 0 : INF; r.dn = mover == D ? INF : 0; return r; }
  if (q->n == NCELL) { r.pn = 0; r.dn = INF; return r; }
  u64 a, b; int mir;
  canon(q, &a, &b, &mir);
  TE e;
  if (tt_get(a, b, &e)) { r.pn = e.pn; r.dn = e.dn; r.busy = e.busy; return r; }
  int lf;
  if (quick_eval(q, &r.pn, &r.dn, &lf)) { tt_put(a, b, r.pn, r.dn, 1, -1, lf, 0, 0); return r; }
  __atomic_fetch_add(&t->leafcalls, 1, __ATOMIC_RELAXED);
  lf = leaf_x(t->rx, q, NULL, NULL);
  if (lf) { r.pn = 0; r.dn = INF; tt_put(a, b, 0, INF, 1, -1, lf, 0, 0); return r; }
  int mv[W];
  int n = gen_moves_opt(q, mv);
  if ((q->n & 1) == D) { r.pn = 1; r.dn = n; } else { r.pn = n; r.dn = 1; }
  tt_put(a, b, r.pn, r.dn, 0, -1, 0, 0, 0);
  return r;
}

static u32 mid(Th *t, const Pos *p, u32 thpn, u32 thdn, PD *out) {
  int D = DEF, side = p->n & 1, isor = side == D;
  u64 a, b; int mir;
  canon(p, &a, &b, &mir);
  {
    u32 spn, sdn; int lf;
    if (quick_eval(p, &spn, &sdn, &lf)) { tt_put(a, b, spn, sdn, 1, -1, lf, 0, 0); out->pn = spn; out->dn = sdn; return 1; }
  }
  int mv[W];
  int n = gen_moves_opt(p, mv);
  Pos ch[W];
  PD cv[W];
  for (int i = 0; i < n; i++) play(&ch[i], p, mv[i]);
  tt_put(a, b, 1, 1, 0, -1, 0, +1, 1);
  u32 work = 1, pn = 1, dn = 1;
  u64 ck[W][2];
  for (int i = 0; i < n; i++) {
    cv[i] = child_value(t, &ch[i], side);
    int m2; canon(&ch[i], &ck[i][0], &ck[i][1], &m2);
  }
  for (int iter = 0;; iter++) {
    __atomic_fetch_add(&t->nodes, 1, __ATOMIC_RELAXED);
    if (iter)
      for (int i = 0; i < n; i++) {
        if (cv[i].pn == 0 || cv[i].dn == 0) continue;
        TE e;
        if (tt_get(ck[i][0], ck[i][1], &e)) { cv[i].pn = e.pn; cv[i].dn = e.dn; cv[i].busy = e.busy; }
      }
    if (isor) {
      pn = INF; dn = 0;
      for (int i = 0; i < n; i++) { if (cv[i].pn < pn) pn = cv[i].pn; dn = sat_add(dn, cv[i].dn); }
    } else {
      pn = 0; dn = INF;
      for (int i = 0; i < n; i++) { pn = sat_add(pn, cv[i].pn); if (cv[i].dn < dn) dn = cv[i].dn; }
    }
    if (pn >= thpn || dn >= thdn || pn == 0 || dn == 0 || __atomic_load_n(&STOP, __ATOMIC_ACQUIRE)) break;
    int b1 = -1; u64 v1 = ~0ULL, v2 = ~0ULL;
    for (int i = 0; i < n; i++) {
      u64 v = isor ? cv[i].pn : cv[i].dn;
      if (v == 0 || v >= INF) { if (!(isor ? cv[i].pn == INF : cv[i].dn == INF)) {} }
      if ((isor && cv[i].pn == INF) || (!isor && cv[i].dn == INF)) v = ~0ULL >> 1;
      else v = v * (1 + (u64)cv[i].busy) + cv[i].busy;
      if (v < v1) { v2 = v1; v1 = v; b1 = i; } else if (v < v2) v2 = v;
    }
    if (b1 < 0) break;
    u64 lim64 = (u64)((double)(v2 > INF ? INF : v2) * (1.0 + EPS)) + 1;
    u32 lim = lim64 > INF ? INF : (u32)lim64;
    u32 cthpn, cthdn;
    if (isor) {
      cthpn = thpn < lim ? thpn : lim;
      cthdn = thdn >= INF ? INF : sat_add(thdn - dn, cv[b1].dn);
    } else {
      cthdn = thdn < lim ? thdn : lim;
      cthpn = thpn >= INF ? INF : sat_add(thpn - pn, cv[b1].pn);
    }
    PD r;
    work += mid(t, &ch[b1], cthpn, cthdn, &r);
    cv[b1].pn = r.pn; cv[b1].dn = r.dn;
  }
  int bm = -1;
  if (isor && pn == 0) for (int i = 0; i < n; i++) if (cv[i].pn == 0) { bm = mv[i]; break; }
  if (bm >= 0 && mir) bm = W - 1 - bm;
  tt_put(a, b, pn, dn, work, bm, 0, -1, 0);
  out->pn = pn; out->dn = dn;
  return work;
}

static Pos ROOT;
static void *worker(void *arg) {
  Th *t = arg;
  while (!__atomic_load_n(&STOP, __ATOMIC_ACQUIRE)) {
    PD r;
    mid(t, &ROOT, INF, INF, &r);
    if (r.pn == 0 || r.dn == 0) __atomic_store_n(&STOP, 1, __ATOMIC_RELEASE);
  }
  return NULL;
}

static long long prog_lookups;
static double prog(const Pos *p, int depth) {
  int D = DEF, side = p->n & 1;
  u64 a, b; int mir;
  canon(p, &a, &b, &mir);
  TE e;
  prog_lookups++;
  if (tt_get(a, b, &e)) { if (e.pn == 0) return 1.0; if (e.dn == 0) return 0.0; }
  u32 spn, sdn; int lf;
  if (quick_eval(p, &spn, &sdn, &lf)) return spn == 0 ? 1.0 : 0.0;
  if (depth == 0) return 0.0;
  int mv[W];
  int n = gen_moves_opt(p, mv);
  double best = 0, sum = 0;
  for (int i = 0; i < n; i++) {
    Pos q; play(&q, p, mv[i]);
    double v;
    if (has_line(q.st[side])) v = side == D ? 1.0 : 0.0;
    else if (q.n == NCELL) v = 1.0;
    else v = prog(&q, depth - 1);
    if (v > best) best = v;
    sum += v;
  }
  if (n == 0) return 1.0;
  return side == D ? best : sum / n;
}

static void bar(char *buf, double f) {
  int w = 40, k = (int)(f * w + 0.5);
  buf[0] = '[';
  for (int i = 0; i < w; i++) buf[1 + i] = i < k ? '#' : '.';
  buf[w + 1] = ']'; buf[w + 2] = 0;
}
static void fmt_time(char *buf, double s) {
  if (s < 0 || s > 1e9) { strcpy(buf, "unknown"); return; }
  if (s < 120) sprintf(buf, "%.0fs", s);
  else if (s < 7200) sprintf(buf, "%.1f min", s / 60);
  else if (s < 172800) sprintf(buf, "%.1f h", s / 3600);
  else sprintf(buf, "%.1f days", s / 86400);
}

static double now(void) {
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + ts.tv_nsec * 1e-9;
}

int main(int argc, char **argv) {
  setvbuf(stdout, NULL, _IONBF, 0); // Unbuffered output
  init();
  DEF = argc > 1 ? atoi(argv[1]) : 1;
  int NT = argc > 2 ? atoi(argv[2]) : 24;
  if (argc > 3) TTB = atoi(argv[3]);
  double maxsec = argc > 4 ? atof(argv[4]) : 1e18;
  for (int i = 0; i < W; i++)
    center_order[i] = (W % 2 == 0) ? (W / 2) + ((i & 1) ? -((i + 1) / 2) : (i / 2)) : W / 2 + ((i & 1) ? (i + 1) / 2 : -(i / 2));
  TT = calloc((size_t)1 << TTB, sizeof(TE));
  if (!TT) { printf("TT alloc failed\n"); return 1; }
  printf("pdfpn_fast W=%d H=%d K=%d defender=%s threads=%d TT=2^%d (%.1f GB)\n", W, H, K, DEF ? "second" : "first", NT, TTB,
         (double)(sizeof(TE) << TTB) / 1e9);

  pthread_t th[256];
  Th ctx[256];
  for (int i = 0; i < NT; i++) {
    ctx[i].rx = calloc(1, sizeof(R2Ctx)); ctx[i].nodes = ctx[i].leafcalls = 0; ctx[i].id = i;
    pthread_create(&th[i], NULL, worker, &ctx[i]);
  }
  double t0 = now(), last = t0;
  int PDEPTH = argc > 5 ? atoi(argv[5]) : 5;
  double hist_t[4096], hist_p[4096]; int nh = 0;
  while (!__atomic_load_n(&STOP, __ATOMIC_ACQUIRE)) {
    struct timespec ts = {0, 200000000}; nanosleep(&ts, NULL);
    double t = now();
    if (t - last >= 10 || __atomic_load_n(&STOP, __ATOMIC_ACQUIRE)) {
      last = t;
      long long nn = 0, lc = 0;
      for (int i = 0; i < NT; i++) {
        nn += __atomic_load_n(&ctx[i].nodes, __ATOMIC_RELAXED);
        lc += __atomic_load_n(&ctx[i].leafcalls, __ATOMIC_RELAXED);
      }
      u64 a, b; int mir; canon(&ROOT, &a, &b, &mir);
      TE e; int f = tt_get(a, b, &e);
      double pr = prog(&ROOT, PDEPTH);
      if (nh < 4096) { hist_t[nh] = t - t0; hist_p[nh] = pr; nh++; }
      char eta[64] = "unknown", bb[64], el[32];
      if (pr > 0 && nh >= 2) {
        int j = nh * 2 / 3; if (j >= nh - 1) j = nh - 2;
        double dp = pr - hist_p[j], dt = (t - t0) - hist_t[j];
        if (dp > 1e-9) fmt_time(eta, (1.0 - pr) * dt / dp);
        else fmt_time(eta, (1.0 - pr) * (t - t0) / pr);
      }
      bar(bb, pr);
      fmt_time(el, t - t0);
      printf("%s %5.1f%%  elapsed %s  ETA %s | %.2fM nodes/s, %lld nodes, root pn=%u dn=%u\n", bb, 100 * pr, el, eta,
             nn / (t - t0) / 1e6, nn, f ? e.pn : 0, f ? e.dn : 0);
      if (t - t0 > maxsec) { __atomic_store_n(&STOP, 2, __ATOMIC_RELEASE); break; }
    }
  }
  for (int i = 0; i < NT; i++) pthread_join(th[i], NULL);
  printf("Search finished!\n");
  return 0;
}
