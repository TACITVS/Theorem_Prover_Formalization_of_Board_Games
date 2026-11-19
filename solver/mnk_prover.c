/*
 * mnk_prover.c
 *
 * AND/OR prover for the statement "the first player (P1) cannot force a win" in an
 * (m, n, k)-game.  Combined with strategy stealing (formalized in MNKStrategyStealing.v,
 * theorem mnk_value_win_or_draw), a proof of that statement shows the game is a draw.
 *
 * ------------------------------------------------------------------------------------------
 * Rules used by the search
 * ------------------------------------------------------------------------------------------
 *
 *   Maker-Breaker (default, "MB")
 *       P1 is Maker and moves first, P2 is Breaker.  Maker wins by occupying every cell of
 *       some line; Breaker wins otherwise.  If Breaker wins, P2 can use the Breaker strategy
 *       in the ordinary (strong) game, so P1 cannot win there either.  Every reduction
 *       below is sound for Maker-Breaker, and the computed values are exact Maker-Breaker
 *       values.
 *
 *   Strong game ("SG")
 *       The search tree follows the ordinary rules: P2's own lines count, so P2 threats
 *       force P1 to block and a completed P2 line ends the game.  Leaf tests still use the
 *       Maker-Breaker safety of P1's lines, which remains sound.  P1 moves are never
 *       restricted (a P1 move on a cell that is dead for P1 can still block P2), while P2
 *       moves may be restricted (fewer P2 options only makes a proof harder).  Therefore a
 *       "P1 cannot win" answer is a proof, but a "P1 wins" answer only means "not proved".
 *
 * ------------------------------------------------------------------------------------------
 * Node analysis (Maker = P1)
 * ------------------------------------------------------------------------------------------
 *
 *   Hypergraph     The live Maker lines (no Breaker stone), each represented by its set of
 *                  free cells F(L).  Subsumption drops a line whose free set contains the
 *                  free set of another line: blocking the smaller line blocks both.
 *
 *   Maker wins     Maker to move: a line with one free cell, or a cell lying on two lines
 *                  with two free cells each and different partner cells (a double threat).
 *
 *   Components     Connected components of the hypergraph are independent subgames:
 *                  Breaker always answers in the component Maker just played in.
 *
 *   Twin pairs     Cells u, v with exactly the same lines through them form a free pairing:
 *                  Breaker answers one with the other, which blocks all those lines.  The
 *                  twins and their lines are removed first, repeatedly.
 *
 *   Safe component (Breaker wins it with Maker moving first) if one of these holds:
 *       ES      sum_L 2^-|F(L)| + max_x sum_{L ∋ x} 2^-|F(L)| < 1
 *               (Erdős–Selfridge, Maker first; formalized as es_inv in MNKErdosSelfridge.v)
 *       2-matching   every line receives two private free cells (a pairing strategy)
 *       greedy hybrid   greedily chosen pairs on the short lines, plus the ES bound on the
 *               remaining lines with every paired cell pessimistically given to Maker
 *       cover   disjoint pairs such that every line contains a whole pair ("set matching");
 *               a single pair may block several overlapping lines
 *       cover + ES   an exact cover of the short lines, plus ES on the rest as above
 *   A component with a double-threat cell is unsafe outright (Maker plays it first).
 *   Safety depends only on the component, so results are cached by an exact key.
 *
 *   Leaves         Maker to move:   every component is safe.
 *                  Breaker to move: every component is safe, or all but one are safe and
 *                  the remaining one satisfies the Breaker-first ES bound sum < 1.
 *
 *   Move pruning   Breaker moves: only cells of unsafe components (a move elsewhere is
 *                  never better).  Maker moves (MB only): only cells of unsafe components.
 *                  Dominance: if every live line through u also passes through v, then v is
 *                  at least as good as u for either player, so u is skipped (MB only for
 *                  Maker; always allowed for Breaker, since it only removes P2 options).
 *
 *   Relevance      (MB, df-pn engines; after Hsu, Ko, Chen, Wei, Hsueh and Wu, TCS 815, 2020.)
 *   zones          A zone of a proved position is a set Z of free cells such that Breaker
 *                  still wins when Maker is handed every free cell outside Z at no cost in
 *                  tempo.  If Maker's move v is refuted with zone Z, every Maker move u
 *                  outside Z is refuted too: compared with that position, Maker owns fewer
 *                  cells and Breaker plays the same strategy, treating Maker moves outside Z
 *                  as passes (extra Breaker moves never hurt in Maker-Breaker).  Zones are
 *                  built bottom up:
 *                    leaf           the strategy cells of every safe component: twin pairs,
 *                                   2-matching cells, pair cells plus the lines no pair covers,
 *                                   or the whole component for ES; with the Breaker-first
 *                                   leaf, also the whole remaining component;
 *                    Breaker node   {b} ∪ zone(child), b the refuting Breaker move;
 *                    Maker node     the zones of the refuted children it relies on, plus the
 *                                   safe components whose moves restrict-Maker skipped, plus
 *                                   the dominating cell of every skipped dominated move.
 *                  A child's zone is kept in that child's canonical coordinates and mapped
 *                  back through the inverse symmetry.  Zones are not used in the strong game,
 *                  where cells handed to P1 would also break P2's own winning lines.
 *                  Off by default (flag 1024).  Measured on (7,7,5) MB: 4,700 -> 3,214 search
 *                  calls and 65.5K -> 54.9K evaluations.  Zones cover about 80% of the free
 *                  cells of a refuted child and 98% at a proved Maker node, because a zone must
 *                  hold a blocking pair of every live line, and components and restrict-Maker
 *                  already capture most of the pruning.  A certificate that relies on zones
 *                  needs its own Rocq lemma, which this modest gain does not yet justify.
 *
 *   Transpositions Positions are canonical under the board's symmetry group.  In MB the
 *                  state is reduced to (Maker stones on live lines, free cells on live
 *                  lines): dead stones and dead cells cannot matter.  Every node is expanded
 *                  from its canonical representative, so the move list is a function of the
 *                  transposition key (required for a consistent proof-number search).
 *
 * ------------------------------------------------------------------------------------------
 * Engines
 * ------------------------------------------------------------------------------------------
 *
 *   DFS    depth-first AND/OR search with a transposition table of solved positions.
 *   DFPN   depth-first proof-number search (Nagai).  Proof target: "P1 cannot win".
 *          Breaker-to-move nodes are OR nodes, Maker-to-move nodes are AND nodes.
 *          Uses the 1 + epsilon threshold rule (epsilon = 1/2, see DFPN_EPSILON_INVERSE).
 *
 *   PDFPN  (default) parallel df-pn: every thread runs df-pn from the root over the shared
 *          table.  A thread inside a node raises that node's selection key for the others
 *          ("virtual proof numbers"), so threads spread over the most promising siblings.
 *          Which proof is found, and the counts, vary from run to run; soundness does not,
 *          because a solved table entry is a proven fact that is never overwritten (see the
 *          table).  With one thread it is exactly DFPN.
 *
 *   Threads in DFPN (OpenMP builds)
 *          Node evaluation dominates the run time, and nearly all evaluations come from the
 *          first look-up of the children of a newly expanded node.  Those children are
 *          evaluated in parallel, in order, and handed to the selection loop, which stores each
 *          one at the moment the serial program would have evaluated it.  Once a child ends the
 *          loop (a proved reply at an OR node, a Maker win at an AND node), evaluations of
 *          later children are cancelled and discarded, since the serial program never makes
 *          them.  The table therefore sees exactly the serial sequence of operations, evictions
 *          included, and the proof is exactly that of the serial program.  Batches whose
 *          expected cost is too small to repay waking the threads stay serial.  The speed-up is
 *          limited by the single longest evaluation in each batch.
 *
 *   Shared state.  Evaluation is a pure function of the position.  The component cache and
 *          the transposition table are guarded by striped spin locks and copied in and out
 *          whole; counters are per thread and summed at the end.
 *
 * ------------------------------------------------------------------------------------------
 * Build
 * ------------------------------------------------------------------------------------------
 *
 *   Linux / WSL:   gcc -std=c11 -O3 -march=native -fopenmp -o mnk_prover mnk_prover.c
 *   Windows:       clang -std=c11 -O3 -march=native -fopenmp -o mnk_prover.exe mnk_prover.c
 *
 *   Without -fopenmp the program builds and runs single-threaded.
 *
 *   With MinGW-w64 GCC on Windows add -Wa,-muse-unaligned-vector-move: that compiler does not
 *   align the stack to 32 bytes, yet emits aligned AVX moves for 32-byte stack objects
 *   (GCC bug 54412), which crashes with an access violation.  Clang realigns the stack
 *   correctly and needs no workaround.
 *
 * ------------------------------------------------------------------------------------------
 * Usage
 * ------------------------------------------------------------------------------------------
 *
 *   mnk_prover m n k [MB|SG] [flags] [tt_log2] [PDFPN|DFPN|DFS] [time_limit_seconds] [threads]
 *
 *   flags (default 1023 = all but relevance zones; 2047 = all):
 *       1 components          2 2-matching pairing      4 subsumption
 *       8 restrict Maker      16 double-threat stop     32 greedy pair+ES hybrid
 *       64 dominance          128 reduced MB state      256 exact pair cover
 *       512 twin pairs        1024 relevance zones (MB, df-pn engines)
 *
 *   threads: worker threads for DFPN and PDFPN (default: every logical processor; DFS is
 *            serial).  A build without -fopenmp always uses one.
 */

#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifdef _OPENMP
#include <omp.h>
/* OMP(parallel for ...) expands to the OpenMP pragma, and to nothing in a serial build. */
#define OMP_PRAGMA(text) _Pragma(#text)
#define OMP(directive)   OMP_PRAGMA(omp directive)
#else
#define OMP(directive)
#endif

typedef uint64_t Bitboard;

enum {
    MAX_CELLS = 64,
    MAX_LINES = 256,
    MAX_SYMMETRIES = 8,
    MAX_K = 16,                       /* longest supported line                       */
    MAX_LINE_PAIRS = MAX_K * (MAX_K - 1) / 2,
    PROGRESS_INTERVAL = 20000000      /* search calls between progress reports       */
};

/* Recursion nodes per exact pair-cover attempt (override with -DCOVER_BUDGET=n). */
#ifndef COVER_BUDGET
#define COVER_BUDGET 20000
#endif

/*
 * Shape of the cover search, after Hsu et al. (TCS 815, 2020, Section 5).
 *
 * COVER_BRANCH_LIMIT is the number of candidate pairs tried per level; 0 means all of them.
 *
 * COVER_PAIR_SCORE picks how candidates are ranked:
 *   0  by the number c of open lines the pair covers;
 *   1  by Hsu et al.'s score 2c - |E(u) xor E(v)| = 4c - deg(u) - deg(v), with degrees
 *      counted over the open lines.
 *
 * A limited search may miss covers; it never reports a false one.  Measured on (7,7,5) MB,
 * one thread:
 *   all candidates, score 0   4.7 s (the earlier default)
 *   2 candidates, score 0     1.9 s
 *   1 candidate,  score 1     2.3 s
 *   2 candidates, score 1     1.2 s
 *   3 candidates, score 1     3.0 s
 * Hsu et al. also found N = 2 best.  With N = 2 the tree is small enough that COVER_BUDGET
 * (2,000 to 100,000) makes no difference.
 */
#ifndef COVER_BRANCH_LIMIT
#define COVER_BRANCH_LIMIT 2
#endif
#ifndef COVER_PAIR_SCORE
#define COVER_PAIR_SCORE 1
#endif

/* Partial cover levels tried after the full cover: cover the lines with at most k-1, k-2, ...
   free cells and apply ES to the rest (override with -DCOVER_ES_LEVELS=n).  Off by default:
   on (7,4,4), (8,4,4) and (7,7,5) they never shortened a proof (the greedy pairs + ES test
   covers that ground) and cost up to a third of the run time. */
#ifndef COVER_ES_LEVELS
#define COVER_ES_LEVELS 0
#endif

/* =========================================================================================
 * Small bit utilities
 * ========================================================================================= */

static inline int popcount(Bitboard b)
{
    return __builtin_popcountll(b);
}

static inline int lowest_cell(Bitboard b)
{
    return __builtin_ctzll(b);
}

static inline Bitboard cell_bit(int cell)
{
    return (Bitboard)1 << cell;
}

/* =========================================================================================
 * Options and statistics
 * ========================================================================================= */

typedef enum { RULES_MAKER_BREAKER, RULES_STRONG } Rules;
typedef enum { ENGINE_DFS, ENGINE_DFPN, ENGINE_PARALLEL_DFPN } Engine;

typedef struct {
    Rules  rules;
    Engine engine;
    int    threads;         /* worker threads (OpenMP builds; DFS always uses one)      */
    bool   components;      /* split into independent subgames                          */
    bool   matching;        /* 2-matching pairing test                                  */
    bool   subsumption;     /* drop lines containing another line's free set            */
    bool   restrict_maker;  /* Maker moves only in unsafe components (MB)               */
    bool   double_threat;   /* Maker double-threat cells are immediate Maker wins       */
    bool   greedy_hybrid;   /* greedy pairs on hot lines + ES on the rest               */
    bool   dominance;       /* skip dominated moves                                     */
    bool   reduced_state;   /* MB transposition key ignores dead stones and dead cells */
    bool   pair_cover;      /* exact shared-pair cover search (+ ES on the rest)        */
    bool   twins;           /* remove twin pairs before the safety tests                */
    bool   zones;           /* Breaker relevance zones prune Maker moves (MB, df-pn)    */
    int    tt_log2;        /* transposition table holds 2^tt_log2 entries             */
    double time_limit;      /* seconds; 0 = unlimited                                   */
} Options;

typedef struct {
    uint64_t search_calls;
    uint64_t evaluations;
    uint64_t safe_by_es;
    uint64_t safe_by_matching;
    uint64_t safe_by_cover;
    uint64_t safe_by_cover_es;
    uint64_t safe_by_greedy_hybrid;
    uint64_t safe_by_twins;
    uint64_t twin_pairs;
    uint64_t unsafe_by_double_threat;
    uint64_t cover_attempts[MAX_K + 1];     /* per hot level */
    uint64_t cover_exhausted[MAX_K + 1];
    uint64_t cover_refuted[MAX_K + 1];      /* refuted by the 2-matching condition  */
    uint64_t cover_found[MAX_K + 1];        /* a cover of the hot lines exists      */
    uint64_t cover_safe[MAX_K + 1];         /* ... and the rest passed ES           */
    uint64_t cover_budget_exhausted;
    uint64_t breaker_first_leaves;
    uint64_t maker_wins_detected;
    uint64_t dominated_moves;
    uint64_t tt_evictions;
    uint64_t component_cache_hits;
    uint64_t component_cache_misses;
    uint64_t evaluations_cancelled;         /* speculative evaluations stopped early  */
    uint64_t zone_pruned_moves;             /* Maker moves refuted by a sibling's zone */
    uint64_t zone_nodes;                    /* Maker nodes proved with a zone           */
    uint64_t zone_cells;                    /* ... total zone size                       */
    uint64_t zone_free_cells;               /* ... total free cells on live lines       */
} Statistics;

enum { STATISTICS_SCALARS = 22, STATISTICS_ARRAYS = 5 };
_Static_assert(sizeof(Statistics) ==
                   (STATISTICS_SCALARS + STATISTICS_ARRAYS * (MAX_K + 1)) * sizeof(uint64_t),
               "a Statistics field was added or removed: update statistics_add");

static Options options;
static double  start_time;

/* Search control, shared by every thread (static atomics start at zero: false). */
static atomic_bool        search_aborted;        /* time limit reached: result unresolved */
static atomic_bool        search_finished;       /* root solved: all threads stop          */
static atomic_ullong      search_call_counter;   /* all threads' search calls              */

static inline bool search_should_stop(void)
{
    return atomic_load_explicit(&search_aborted, memory_order_relaxed) ||
           atomic_load_explicit(&search_finished, memory_order_relaxed);
}

/*
 * Spin lock for very short critical sections (copying a table entry).  0 = free.  Locks are
 * striped: one lock guards many slots, so the lock arrays stay small.
 */
static inline void spin_lock(atomic_int* lock)
{
    while (atomic_exchange_explicit(lock, 1, memory_order_acquire)) {
        while (atomic_load_explicit(lock, memory_order_relaxed)) {
            /* spin until the holder releases it */
        }
    }
}

static inline void spin_unlock(atomic_int* lock)
{
    atomic_store_explicit(lock, 0, memory_order_release);
}

/*
 * Counters are thread-local, so evaluation threads never contend for them.  At the end of each
 * parallel batch every helper thread adds its counters to `helper_totals` and clears them;
 * the searching thread keeps its own in `stats`.  report_totals() combines the two.
 */
static _Thread_local Statistics stats;
static Statistics               helper_totals;

static void statistics_add(Statistics* into, const Statistics* from)
{
    into->search_calls            += from->search_calls;
    into->evaluations             += from->evaluations;
    into->safe_by_es              += from->safe_by_es;
    into->safe_by_matching        += from->safe_by_matching;
    into->safe_by_cover           += from->safe_by_cover;
    into->safe_by_cover_es        += from->safe_by_cover_es;
    into->safe_by_greedy_hybrid   += from->safe_by_greedy_hybrid;
    into->safe_by_twins           += from->safe_by_twins;
    into->twin_pairs              += from->twin_pairs;
    into->unsafe_by_double_threat += from->unsafe_by_double_threat;
    for (int i = 0; i <= MAX_K; i++) {
        into->cover_attempts[i]  += from->cover_attempts[i];
        into->cover_exhausted[i] += from->cover_exhausted[i];
        into->cover_refuted[i]   += from->cover_refuted[i];
        into->cover_found[i]     += from->cover_found[i];
        into->cover_safe[i]      += from->cover_safe[i];
    }
    into->cover_budget_exhausted  += from->cover_budget_exhausted;
    into->breaker_first_leaves    += from->breaker_first_leaves;
    into->maker_wins_detected     += from->maker_wins_detected;
    into->dominated_moves         += from->dominated_moves;
    into->tt_evictions            += from->tt_evictions;
    into->component_cache_hits    += from->component_cache_hits;
    into->component_cache_misses  += from->component_cache_misses;
    into->evaluations_cancelled   += from->evaluations_cancelled;
    into->zone_pruned_moves       += from->zone_pruned_moves;
    into->zone_nodes              += from->zone_nodes;
    into->zone_cells              += from->zone_cells;
    into->zone_free_cells         += from->zone_free_cells;
}

/*
 * A speculative evaluation (see prefetch_children) is the evaluation of child `index` while an
 * earlier child may still end the parent's loop.  It is cancelled once `cutoff` drops below
 * `index`.  The long-running tests poll speculation_cancelled(); after cancellation every test
 * fails fast, the result is discarded, and nothing is cached.  `cutoff` is NULL outside
 * speculative evaluations (always, in a serial build).
 */
typedef struct {
    const atomic_int* cutoff;
    int               index;
    bool              cancelled;
} Speculation;

static _Thread_local Speculation speculation;

static bool speculation_cancelled(void)
{
    if (!speculation.cancelled && speculation.cutoff &&
        atomic_load_explicit(speculation.cutoff, memory_order_relaxed) < speculation.index) {
        speculation.cancelled = true;
    }
    return speculation.cancelled;
}

#ifdef _OPENMP
/* Called by every thread of a parallel team just before the team ends. */
static void statistics_fold_helper(void)
{
    if (omp_get_thread_num() != 0) {
        OMP(critical(statistics))
        {
            statistics_add(&helper_totals, &stats);
        }
        memset(&stats, 0, sizeof stats);
    }
}
#endif

/* All counters so far; called by the searching thread outside parallel regions. */
static Statistics report_totals(void)
{
    Statistics total = stats;
    statistics_add(&total, &helper_totals);
    return total;
}

/* Wall-clock seconds (clock() measures process CPU time on POSIX systems). */
static double wall_seconds(void)
{
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static double elapsed_seconds(void)
{
    return wall_seconds() - start_time;
}

/* =========================================================================================
 * Board geometry and symmetry
 * ========================================================================================= */

typedef struct {
    int      rows;
    int      cols;
    int      k;
    int      cell_count;
    int      line_count;
    Bitboard all_cells;
    Bitboard line[MAX_LINES];
    Bitboard line_reach[MAX_CELLS];  /* union of all lines through each cell              */
    uint64_t potential_limit;        /* 2^k: the ES threshold in integer weights        */
    int      symmetry_count;
    int      symmetry_inverse[MAX_SYMMETRIES];   /* the transform undoing transform t     */
    /* symmetry_table[t][j][v] = image under transform t of byte value v at byte j. */
    Bitboard symmetry_table[MAX_SYMMETRIES][8][256];
} Board;

static Board board;

/* Image (row, col) of (r, c) under symmetry t.  Transforms 4..7 exist only for squares. */
static void transform_cell(int t, int r, int c, int* out_r, int* out_c)
{
    const int last_r = board.rows - 1;
    const int last_c = board.cols - 1;

    switch (t) {
    case 0:  *out_r = r;          *out_c = c;          break;   /* identity            */
    case 1:  *out_r = r;          *out_c = last_c - c; break;   /* mirror columns      */
    case 2:  *out_r = last_r - r; *out_c = c;          break;   /* mirror rows         */
    case 3:  *out_r = last_r - r; *out_c = last_c - c; break;   /* rotate 180          */
    case 4:  *out_r = c;          *out_c = r;          break;   /* transpose           */
    case 5:  *out_r = last_c - c; *out_c = last_r - r; break;   /* anti-transpose      */
    case 6:  *out_r = c;          *out_c = last_r - r; break;   /* rotate 90           */
    default: *out_r = last_c - c; *out_c = r;          break;   /* rotate 270          */
    }
}

static bool board_init(int rows, int cols, int k)
{
    if (rows < 1 || cols < 1 || rows * cols > MAX_CELLS || k < 2 || k > MAX_K) {
        fprintf(stderr, "unsupported board (%d,%d,%d): need 1 <= m*n <= %d and 2 <= k <= %d\n",
                rows, cols, k, MAX_CELLS, MAX_K);
        return false;
    }

    board.rows = rows;
    board.cols = cols;
    board.k = k;
    board.cell_count = rows * cols;
    board.all_cells = board.cell_count == 64 ? ~(Bitboard)0 : cell_bit(board.cell_count) - 1;
    board.potential_limit = (uint64_t)1 << k;

    static const int direction[4][2] = { { 0, 1 }, { 1, 0 }, { 1, 1 }, { -1, 1 } };
    board.line_count = 0;
    for (int d = 0; d < 4; d++) {
        const int dr = direction[d][0];
        const int dc = direction[d][1];
        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                const int end_r = r + (k - 1) * dr;
                const int end_c = c + (k - 1) * dc;
                if (end_r < 0 || end_r >= rows || end_c < 0 || end_c >= cols) {
                    continue;
                }
                if (board.line_count == MAX_LINES) {
                    fprintf(stderr, "too many lines (limit %d)\n", MAX_LINES);
                    return false;
                }
                Bitboard line = 0;
                for (int i = 0; i < k; i++) {
                    line |= cell_bit((r + i * dr) * cols + (c + i * dc));
                }
                board.line[board.line_count++] = line;
            }
        }
    }

    memset(board.line_reach, 0, sizeof board.line_reach);
    for (int i = 0; i < board.line_count; i++) {
        for (Bitboard f = board.line[i]; f; f &= f - 1) {
            board.line_reach[lowest_cell(f)] |= board.line[i];
        }
    }

    board.symmetry_count = (rows == cols) ? 8 : 4;
    int image[MAX_SYMMETRIES][MAX_CELLS];
    for (int t = 0; t < board.symmetry_count; t++) {
        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                int tr, tc;
                transform_cell(t, r, c, &tr, &tc);
                image[t][r * cols + c] = tr * cols + tc;
            }
        }
    }
    for (int t = 0; t < board.symmetry_count; t++) {
        board.symmetry_inverse[t] = -1;
        for (int u = 0; u < board.symmetry_count && board.symmetry_inverse[t] < 0; u++) {
            bool undoes = true;
            for (int cell = 0; cell < board.cell_count && undoes; cell++) {
                undoes = image[u][image[t][cell]] == cell;
            }
            if (undoes) {
                board.symmetry_inverse[t] = u;
            }
        }
        if (board.symmetry_inverse[t] < 0) {
            fprintf(stderr, "internal error: symmetry %d has no inverse\n", t);
            return false;
        }
    }
    for (int t = 0; t < board.symmetry_count; t++) {
        for (int j = 0; j < 8; j++) {
            for (int v = 0; v < 256; v++) {
                Bitboard out = 0;
                for (int bit = 0; bit < 8; bit++) {
                    const int cell = j * 8 + bit;
                    if (((v >> bit) & 1) && cell < board.cell_count) {
                        out |= cell_bit(image[t][cell]);
                    }
                }
                board.symmetry_table[t][j][v] = out;
            }
        }
    }
    return true;
}

static inline Bitboard apply_symmetry(int t, Bitboard b)
{
    Bitboard out = 0;
    for (int j = 0; j < 8; j++) {
        out |= board.symmetry_table[t][j][(b >> (8 * j)) & 0xFF];
    }
    return out;
}

/* =========================================================================================
 * Positions and canonical states
 * ========================================================================================= */

typedef struct {
    Bitboard maker;     /* P1 stones */
    Bitboard breaker;   /* P2 stones */
} Position;

static inline bool position_less(Position a, Position b)
{
    return a.maker < b.maker || (a.maker == b.maker && a.breaker < b.breaker);
}

/*
 * The smallest image of the position under the symmetry group.  `transform`, if not NULL,
 * receives the transform that produced it (0 = identity).
 */
static Position symmetry_canonical(Position p, int* transform)
{
    Position best = p;
    int      best_t = 0;
    for (int t = 1; t < board.symmetry_count; t++) {
        const Position image = { apply_symmetry(t, p.maker), apply_symmetry(t, p.breaker) };
        if (position_less(image, best)) {
            best = image;
            best_t = t;
        }
    }
    if (transform) {
        *transform = best_t;
    }
    return best;
}

/*
 * Canonical search state.  In Maker-Breaker with the reduced state, a position is
 * equivalent to (A, B) = (Maker stones on live lines, free cells on live lines): a line is
 * live exactly when it lies inside A ∪ B, and its free cells are its cells in B.  The state
 * is represented as the position with Maker stones A and Breaker stones on every other cell,
 * so the ordinary evaluation applies to it unchanged.
 *
 * The reduction keeps cell coordinates, so `transform` (if not NULL) receives the symmetry
 * that maps the reduced position to the returned one.  A relevance zone of the result maps
 * back through the inverse transform; dead cells, which the reduction hands to Breaker, lie
 * on no live line and cannot matter to a zone.
 */
static Position canonical_state(Position p, int* transform)
{
    if (options.rules == RULES_MAKER_BREAKER && options.reduced_state) {
        const Bitboard occupied = p.maker | p.breaker;
        Bitboard live_maker = 0;
        Bitboard live_free = 0;
        for (int i = 0; i < board.line_count; i++) {
            const Bitboard line = board.line[i];
            if (line & p.breaker) {
                continue;
            }
            live_maker |= line & p.maker;
            live_free |= line & ~occupied;
        }
        p.maker = live_maker;
        p.breaker = board.all_cells & ~(live_maker | live_free);
    }
    return symmetry_canonical(p, transform);
}

/* =========================================================================================
 * Hypergraph of live Maker lines
 * ========================================================================================= */

typedef struct {
    int      count;
    Bitboard free_cells[MAX_LINES];
    uint8_t  free_count[MAX_LINES];
} Hypergraph;

static void hypergraph_build(Position p, Hypergraph* h)
{
    const Bitboard occupied = p.maker | p.breaker;
    Bitboard live[MAX_LINES];
    uint8_t  live_count[MAX_LINES];
    int      n = 0;

    for (int i = 0; i < board.line_count; i++) {
        const Bitboard line = board.line[i];
        if (line & p.breaker) {
            continue;
        }
        live[n] = line & ~occupied;
        live_count[n] = (uint8_t)popcount(live[n]);
        n++;
    }

    h->count = 0;
    if (!options.subsumption) {
        memcpy(h->free_cells, live, (size_t)n * sizeof live[0]);
        memcpy(h->free_count, live_count, (size_t)n * sizeof live_count[0]);
        h->count = n;
        return;
    }

    /* Keep a line only if no already kept (smaller or equal) line lies inside it. */
    for (int size = 0; size <= board.k; size++) {
        for (int i = 0; i < n; i++) {
            if (live_count[i] != size) {
                continue;
            }
            bool subsumed = false;
            for (int j = 0; j < h->count; j++) {
                if ((h->free_cells[j] & ~live[i]) == 0) {
                    subsumed = true;
                    break;
                }
            }
            if (!subsumed) {
                h->free_cells[h->count] = live[i];
                h->free_count[h->count] = (uint8_t)size;
                h->count++;
            }
        }
    }
}

/*
 * Cells where Maker would create two threats with different completion cells: a cell shared
 * by two 2-cell lines with different partners.  Lines are given as free sets with sizes.
 */
static Bitboard double_threat_cells_of(const Bitboard* lines, const uint8_t* sizes, int n)
{
    int partner[MAX_CELLS];
    for (int c = 0; c < board.cell_count; c++) {
        partner[c] = -1;
    }

    Bitboard result = 0;
    for (int i = 0; i < n; i++) {
        if (sizes[i] != 2) {
            continue;
        }
        const Bitboard f = lines[i];
        const int u = lowest_cell(f);
        const int v = lowest_cell(f & (f - 1));
        if (partner[u] < 0) {
            partner[u] = v;
        } else if (partner[u] != v) {
            result |= cell_bit(u);
        }
        if (partner[v] < 0) {
            partner[v] = u;
        } else if (partner[v] != u) {
            result |= cell_bit(v);
        }
    }
    return result;
}

static Bitboard double_threat_cells(const Hypergraph* h)
{
    return double_threat_cells_of(h->free_cells, h->free_count, h->count);
}

/* Free cells completing a line of `owner` (lines without an `opponent` stone). */
static Bitboard completion_cells(Bitboard owner, Bitboard opponent)
{
    const Bitboard occupied = owner | opponent;
    Bitboard result = 0;
    for (int i = 0; i < board.line_count; i++) {
        const Bitboard line = board.line[i];
        if (line & opponent) {
            continue;
        }
        const Bitboard f = line & ~occupied;
        if (f != 0 && (f & (f - 1)) == 0) {
            result |= f;
        }
    }
    return result;
}

/* Integer ES weight of a line with `free_count` free cells: 2^(k - free_count). */
static inline uint64_t line_weight(int free_count)
{
    return (uint64_t)1 << (board.k - free_count);
}

/* =========================================================================================
 * Safety tests for one component (Maker moves first inside it)
 *
 * A component is given as an array of line free sets `lines[0..n-1]` and its cell set.
 * ========================================================================================= */

typedef struct {
    int             n;
    const Bitboard* lines;
    const uint8_t*  sizes;
    Bitboard        cells;
} Component;

/* Maker-first Erdős–Selfridge: phi + max weight < 2^k. */
static bool es_maker_first(const Component* comp, uint64_t* potential_out)
{
    uint64_t weight[MAX_CELLS] = { 0 };
    uint64_t potential = 0;
    for (int i = 0; i < comp->n; i++) {
        const uint64_t w = line_weight(comp->sizes[i]);
        potential += w;
        for (Bitboard f = comp->lines[i]; f; f &= f - 1) {
            weight[lowest_cell(f)] += w;
        }
    }
    uint64_t max_weight = 0;
    for (Bitboard f = comp->cells; f; f &= f - 1) {
        const int c = lowest_cell(f);
        if (weight[c] > max_weight) {
            max_weight = weight[c];
        }
    }
    *potential_out = potential;
    return potential + max_weight < board.potential_limit;
}

/*
 * --- 2-matching: each line gets two private free cells (Kuhn's augmenting paths). ---
 *
 * Slots 2i and 2i+1 belong to line i.  `owned` is the set of cells assigned to some slot and
 * owner[c] is valid exactly for c in `owned`.  A slot that sees an unowned cell takes it at
 * once; only otherwise is an augmenting path searched.
 */
typedef struct {
    const Component* comp;
    int              owner[MAX_CELLS];
    Bitboard         owned;
    Bitboard         visited;   /* cells visited by the current augmenting search */
} Matching;

static bool matching_augment(Matching* m, int slot)
{
    const Bitboard line = m->comp->lines[slot / 2];
    const Bitboard unowned = line & ~m->owned;
    if (unowned) {
        const int c = lowest_cell(unowned);
        m->owner[c] = slot;
        m->owned |= cell_bit(c);
        return true;
    }
    /* Every cell of the line is owned: try to move one owner elsewhere. */
    for (Bitboard candidates = line; candidates; candidates &= candidates - 1) {
        const int c = lowest_cell(candidates);
        if (m->visited & cell_bit(c)) {
            continue;
        }
        m->visited |= cell_bit(c);
        if (matching_augment(m, m->owner[c])) {
            m->owner[c] = slot;
            return true;
        }
    }
    return false;
}

/* On success `matched_out` receives the matched cells: the cells Breaker's pairing uses. */
static bool has_two_matching(const Component* comp, Bitboard* matched_out)
{
    if (2 * comp->n > popcount(comp->cells)) {
        return false;
    }
    Matching m;
    m.comp = comp;
    m.owned = 0;
    for (int slot = 0; slot < 2 * comp->n; slot++) {
        m.visited = 0;
        if (!matching_augment(&m, slot)) {
            return false;
        }
    }
    *matched_out = m.owned;
    return true;
}

/* --- Pairs + ES on the uncovered lines. --- */

typedef struct {
    int      count;
    int      first[MAX_CELLS / 2];
    int      second[MAX_CELLS / 2];
    Bitboard cells;                  /* union of all paired cells */
} PairSet;

static inline Bitboard pair_mask(const PairSet* pairs, int i)
{
    return cell_bit(pairs->first[i]) | cell_bit(pairs->second[i]);
}

static bool line_contains_pair(const PairSet* pairs, Bitboard line)
{
    for (int i = 0; i < pairs->count; i++) {
        const Bitboard m = pair_mask(pairs, i);
        if ((line & m) == m) {
            return true;
        }
    }
    return false;
}

/*
 * Breaker strategy: if Maker takes a paired cell, take its partner (every line containing a
 * pair is then blocked); otherwise play the ES-greedy unpaired cell.  For the uncovered lines
 * every paired cell is assumed to be Maker's.  The strategy wins when the Maker-first ES bound
 * holds for the uncovered lines restricted to unpaired cells.
 */
static bool pairs_plus_es(const Component* comp, const PairSet* pairs)
{
    uint64_t weight[MAX_CELLS] = { 0 };
    uint64_t potential = 0;
    for (int i = 0; i < comp->n; i++) {
        const Bitboard line = comp->lines[i];
        if (line_contains_pair(pairs, line)) {
            continue;
        }
        const Bitboard unpaired = line & ~pairs->cells;
        const int remaining = popcount(unpaired);
        if (remaining == 0) {
            return false;   /* Maker could collect the whole line on paired cells */
        }
        const uint64_t w = line_weight(remaining);
        potential += w;
        for (Bitboard f = unpaired; f; f &= f - 1) {
            weight[lowest_cell(f)] += w;
        }
    }
    uint64_t max_weight = 0;
    for (Bitboard f = comp->cells & ~pairs->cells; f; f &= f - 1) {
        const int c = lowest_cell(f);
        if (weight[c] > max_weight) {
            max_weight = weight[c];
        }
    }
    return potential + max_weight < board.potential_limit;
}

/*
 * Relevance zone of the pairs + ES strategy: the paired cells, plus every cell of the lines no
 * pair covers.  Handing Maker the cells outside it leaves each covered line its pair and each
 * uncovered line unchanged, so the strategy still wins.
 */
static Bitboard pairs_zone(const Component* comp, const PairSet* pairs)
{
    Bitboard zone = pairs->cells;
    for (int i = 0; i < comp->n; i++) {
        if (!line_contains_pair(pairs, comp->lines[i])) {
            zone |= comp->lines[i];
        }
    }
    return zone;
}

/*
 * Greedy hybrid: pair the lines with at most `hot` free cells using low-degree cells.  On
 * success `zone_out` receives the strategy's relevance zone.
 */
static bool greedy_hybrid_safe(const Component* comp, Bitboard* zone_out)
{
    int degree[MAX_CELLS] = { 0 };
    for (int i = 0; i < comp->n; i++) {
        for (Bitboard f = comp->lines[i]; f; f &= f - 1) {
            degree[lowest_cell(f)]++;
        }
    }

    for (int hot = 2; hot <= board.k; hot++) {
        PairSet pairs = { 0 };
        for (int size = 2; size <= hot; size++) {
            for (int i = 0; i < comp->n; i++) {
                if (comp->sizes[i] != size || line_contains_pair(&pairs, comp->lines[i])) {
                    continue;
                }
                const Bitboard candidates = comp->lines[i] & ~pairs.cells;
                if (popcount(candidates) < 2) {
                    continue;
                }
                int a = -1;
                int b = -1;
                for (Bitboard f = candidates; f; f &= f - 1) {
                    const int x = lowest_cell(f);
                    if (a < 0 || degree[x] < degree[a]) {
                        b = a;
                        a = x;
                    } else if (b < 0 || degree[x] < degree[b]) {
                        b = x;
                    }
                }
                pairs.first[pairs.count] = a;
                pairs.second[pairs.count] = b;
                pairs.count++;
                pairs.cells |= cell_bit(a) | cell_bit(b);
            }
        }
        if (pairs_plus_es(comp, &pairs)) {
            stats.safe_by_greedy_hybrid++;
            *zone_out = pairs_zone(comp, &pairs);
            return true;
        }
    }
    return false;
}

/*
 * --- Exact shared-pair cover (set matching) by backtracking. ---
 *
 * The search state is the list of "open" lines, those still lacking a pair, each reduced to
 * its unused free cells.  A pair of unused cells covers a line exactly when both cells lie in
 * that reduced set, so no other bookkeeping is needed.
 */

typedef struct {
    int     budget;   /* recursion nodes left       */
    PairSet pairs;    /* pairs on the current path  */
} CoverSearch;

/*
 * Necessary condition for covering the open lines.  Two open lines sharing at most one unused
 * free cell can never be covered by the same pair, so in any cover a family S of pairwise
 * such lines receives |S| distinct, hence disjoint, pairs: every line of S gets two private
 * cells.  S is chosen greedily, shortest lines first; if S has no 2-matching, no cover
 * exists.  This refutes most infeasible instances without backtracking.
 */
static bool cover_may_exist(const Bitboard* open, int open_count)
{
    uint8_t sizes[MAX_LINES];
    for (int i = 0; i < open_count; i++) {
        const int size = popcount(open[i]);
        if (size < 2) {
            return false;
        }
        sizes[i] = (uint8_t)size;
    }

    Bitboard family_lines[MAX_LINES];
    uint8_t  family_sizes[MAX_LINES];
    int      m = 0;
    Bitboard cells = 0;
    for (int size = 2; size <= board.k; size++) {
        for (int i = 0; i < open_count; i++) {
            if (sizes[i] != size) {
                continue;
            }
            const Bitboard f = open[i];
            bool independent = true;
            for (int j = 0; j < m && independent; j++) {
                const Bitboard shared = f & family_lines[j];
                independent = (shared & (shared - 1)) == 0;   /* at most one common cell */
            }
            if (independent) {
                family_lines[m] = f;
                family_sizes[m] = (uint8_t)size;
                m++;
                cells |= f;
            }
        }
    }
    const Component family = { m, family_lines, family_sizes, cells };
    Bitboard matched = 0;   /* not needed here */
    return has_two_matching(&family, &matched);
}

static bool cover_recurse(CoverSearch* s, const Bitboard* open, int open_count)
{
    if (open_count == 0) {
        return true;   /* every line contains a chosen pair */
    }
    if (--s->budget < 0) {
        return false;
    }
    if ((s->budget & 63) == 0 && speculation_cancelled()) {
        s->budget = -1;   /* unwind as if exhausted; the caller sees the cancellation */
        return false;
    }
    if (!cover_may_exist(open, open_count)) {
        return false;
    }

    /* Most constrained open line: fewest unused cells, hence fewest candidate pairs. */
    int best_line = 0;
    int best_size = popcount(open[0]);
    for (int i = 1; i < open_count; i++) {
        const int size = popcount(open[i]);
        if (size < best_size) {
            best_size = size;
            best_line = i;
        }
    }

    /* Open-line degree of each cell of that line (only needed by the Hsu et al. score). */
    int degree[MAX_CELLS];
    if (COVER_PAIR_SCORE == 1) {
        for (Bitboard a = open[best_line]; a; a &= a - 1) {
            const int u = lowest_cell(a);
            degree[u] = 0;
            for (int i = 0; i < open_count; i++) {
                degree[u] += (int)((open[i] >> u) & 1);
            }
        }
    }

    /* Candidate pairs inside that line, best score first. */
    int cand_u[MAX_LINE_PAIRS];
    int cand_v[MAX_LINE_PAIRS];
    int cand_score[MAX_LINE_PAIRS];
    int cand_count = 0;
    for (Bitboard a = open[best_line]; a; a &= a - 1) {
        const int u = lowest_cell(a);
        for (Bitboard b = a & (a - 1); b; b &= b - 1) {
            const int v = lowest_cell(b);
            const Bitboard pair = cell_bit(u) | cell_bit(v);
            int score = 0;
            for (int i = 0; i < open_count; i++) {
                score += (open[i] & pair) == pair;
            }
            if (COVER_PAIR_SCORE == 1) {
                score = 4 * score - degree[u] - degree[v];
            }
            int j = cand_count++;
            while (j > 0 && cand_score[j - 1] < score) {
                cand_u[j] = cand_u[j - 1];
                cand_v[j] = cand_v[j - 1];
                cand_score[j] = cand_score[j - 1];
                j--;
            }
            cand_u[j] = u;
            cand_v[j] = v;
            cand_score[j] = score;
        }
    }

    const int tries = COVER_BRANCH_LIMIT > 0 && cand_count > COVER_BRANCH_LIMIT ? COVER_BRANCH_LIMIT
                                                                              : cand_count;
    for (int q = 0; q < tries; q++) {
        const Bitboard pair = cell_bit(cand_u[q]) | cell_bit(cand_v[q]);
        Bitboard child[MAX_LINES];
        int      child_count = 0;
        for (int i = 0; i < open_count; i++) {
            if ((open[i] & pair) != pair) {
                child[child_count++] = open[i] & ~pair;
            }
        }
        s->pairs.first[s->pairs.count] = cand_u[q];
        s->pairs.second[s->pairs.count] = cand_v[q];
        s->pairs.count++;
        if (cover_recurse(s, child, child_count)) {
            return true;
        }
        s->pairs.count--;
        if (s->budget < 0) {
            return false;
        }
    }
    return false;
}

/*
 * Cover all lines (strongest); optionally, cover only the short lines and use ES for the rest.
 * On success `zone_out` receives the strategy's relevance zone.
 */
static bool pair_cover_safe(const Component* comp, Bitboard* zone_out)
{
    const int lowest_hot = board.k - COVER_ES_LEVELS < 2 ? 2 : board.k - COVER_ES_LEVELS;
    for (int hot = board.k; hot >= lowest_hot; hot--) {
        Bitboard open[MAX_LINES];
        int      open_count = 0;
        for (int i = 0; i < comp->n; i++) {
            if (comp->sizes[i] <= hot) {
                open[open_count++] = comp->lines[i];
            }
        }
        if (open_count == 0) {
            continue;
        }
        stats.cover_attempts[hot]++;
        CoverSearch s;
        memset(&s, 0, sizeof s);
        s.budget = COVER_BUDGET;
        if (!cover_recurse(&s, open, open_count)) {
            if (speculation.cancelled) {
                return false;   /* the result is discarded anyway */
            }
            if (s.budget < 0) {
                stats.cover_budget_exhausted++;
                stats.cover_exhausted[hot]++;
            } else if (s.budget == COVER_BUDGET - 1) {
                stats.cover_refuted[hot]++;   /* refuted at the root, without branching */
            }
            continue;
        }
        stats.cover_found[hot]++;
        for (int i = 0; i < s.pairs.count; i++) {
            s.pairs.cells |= pair_mask(&s.pairs, i);
        }
        if (pairs_plus_es(comp, &s.pairs)) {
            stats.cover_safe[hot]++;
            if (hot == board.k) {
                stats.safe_by_cover++;
            } else {
                stats.safe_by_cover_es++;
            }
            *zone_out = pairs_zone(comp, &s.pairs);
            return true;
        }
    }
    return false;
}

/*
 * Twin pairs.  Cells u != v are twins when every line through u passes through v and vice
 * versa, and some line does.  Breaker answers u with v and v with u, which blocks every line
 * through them, and no other line touches u or v.  So the component is safe whenever the
 * rest of it is, and the twins and their lines can be removed.  Removal can create new twins,
 * so this repeats to a fixed point.
 *
 * The reduction never hides a pair cover: in any cover, the pairs touching u or v cover only
 * lines through u or v, all of which contain {u, v}, so they can be replaced by {u, v}.
 *
 * "Every line through u passes through v" is "v ∈ common[u]" with common[u] the intersection
 * of the lines through u (see undominated_moves).  Writes the remaining lines to `lines` and
 * `sizes` and returns their number; `twin_cells` receives every removed twin cell (the cells
 * the twin strategy uses).
 */
static int remove_twin_pairs(const Component* comp, Bitboard* lines, uint8_t* sizes, Bitboard* twin_cells)
{
    int n = comp->n;
    memcpy(lines, comp->lines, (size_t)n * sizeof lines[0]);
    memcpy(sizes, comp->sizes, (size_t)n * sizeof sizes[0]);
    *twin_cells = 0;

    for (;;) {
        Bitboard covered = 0;
        for (int i = 0; i < n; i++) {
            covered |= lines[i];
        }
        Bitboard common[MAX_CELLS];
        for (Bitboard f = covered; f; f &= f - 1) {
            common[lowest_cell(f)] = ~(Bitboard)0;
        }
        for (int i = 0; i < n; i++) {
            for (Bitboard f = lines[i]; f; f &= f - 1) {
                common[lowest_cell(f)] &= lines[i];
            }
        }

        /* Disjoint twin pairs of this pass.  Pairs whose lines overlap are compatible: after
           one pair's lines are removed, the other two cells are still twins (or idle). */
        Bitboard twins = 0;
        for (Bitboard f = covered; f; f &= f - 1) {
            const int u = lowest_cell(f);
            if (twins & cell_bit(u)) {
                continue;
            }
            for (Bitboard g = common[u] & ~twins & ~cell_bit(u); g; g &= g - 1) {
                const int v = lowest_cell(g);
                if ((common[v] >> u) & 1) {
                    twins |= cell_bit(u) | cell_bit(v);
                    stats.twin_pairs++;
                    break;
                }
            }
        }
        if (!twins) {
            return n;
        }
        *twin_cells |= twins;

        /* A line meeting a twin cell contains that cell's partner as well: drop it. */
        int kept = 0;
        for (int i = 0; i < n; i++) {
            if (lines[i] & twins) {
                continue;
            }
            lines[kept] = lines[i];
            sizes[kept] = sizes[i];
            kept++;
        }
        n = kept;
    }
}

/*
 * Is the component safe (Breaker wins it with Maker moving first)?  `potential_out` receives
 * the ES potential of the (reduced) component, for the Breaker-first test of the caller.
 * Tests run cheapest first; the exact pair cover, a bounded backtracking search, runs last.
 *
 * When safe, `zone_out` receives the relevance zone of the winning strategy: the twin cells,
 * plus the cells the deciding test relies on (all cells of the reduced component for ES).
 */
static bool component_is_safe(const Component* original, uint64_t* potential_out, Bitboard* zone_out)
{
    Bitboard   reduced_lines[MAX_LINES];
    uint8_t    reduced_sizes[MAX_LINES];
    Component  reduced;
    const Component* comp = original;
    Bitboard   twin_cells = 0;
    Bitboard   test_zone = 0;

    if (options.twins) {
        const int n = remove_twin_pairs(original, reduced_lines, reduced_sizes, &twin_cells);
        if (n == 0) {
            *potential_out = 0;
            *zone_out = twin_cells;
            stats.safe_by_twins++;
            return true;
        }
        if (n < original->n) {
            Bitboard cells = 0;
            for (int i = 0; i < n; i++) {
                cells |= reduced_lines[i];
            }
            reduced = (Component){ n, reduced_lines, reduced_sizes, cells };
            comp = &reduced;
        }
    }

    if (es_maker_first(comp, potential_out)) {
        stats.safe_by_es++;
        /* ES relies on every cell of the component.  (Looking for a pairing with a smaller
           zone as well was measured: no gain on (6,4,4), (7,4,4) or (7,7,5).) */
        *zone_out = twin_cells | comp->cells;
        return true;
    }
    /* A cell on two 2-cell lines with different partners wins the component for Maker (who
       moves first in it), so no test below can succeed. */
    if (double_threat_cells_of(comp->lines, comp->sizes, comp->n)) {
        stats.unsafe_by_double_threat++;
        return false;
    }
    if (options.matching && has_two_matching(comp, &test_zone)) {
        stats.safe_by_matching++;
        *zone_out = twin_cells | test_zone;
        return true;
    }
    if ((options.greedy_hybrid && greedy_hybrid_safe(comp, &test_zone)) ||
        (options.pair_cover && pair_cover_safe(comp, &test_zone))) {
        *zone_out = twin_cells | test_zone;
        return true;
    }
    return false;
}

/* =========================================================================================
 * Component cache
 *
 * A component with free cells F is determined exactly by F and by Maker's stones on the lines
 * that meet F: such a line is live precisely when it lies inside F ∪ Maker (every free cell of
 * a live line meeting F belongs to the same component), and its free set is then its part in
 * F.  The key (F, Maker ∩ reach(F)) is therefore exact, not a hash: a hit can never confuse
 * two different subgames.  Results depend only on the component, so they are shared by every
 * position in which the same subgame appears.
 * ========================================================================================= */

typedef struct {
    Bitboard free_cells;     /* F; 0 marks an empty slot (a component always has free cells) */
    Bitboard maker_near;     /* Maker stones on lines meeting F                              */
    Bitboard zone;           /* relevance zone of Breaker's strategy, when safe              */
    bool     safe;
    bool     breaker_first;  /* Breaker-first ES holds (sum of weights < 1)                  */
} ComponentCacheEntry;

enum {
    COMPONENT_CACHE_LOG2 = 21,
    COMPONENT_CACHE_LOCKS = 4096   /* striped locks; a power of two */
};

static ComponentCacheEntry* component_cache = NULL;

/*
 * Evaluation threads share the cache.  An entry is two words plus flags, so an unguarded
 * reader could see half of one entry and half of another; each slot is therefore read and
 * written under the spin lock of its stripe.  A lock is held only for that copy, never during
 * the safety tests, so contention is negligible.  Static atomics start at zero, i.e. unlocked.
 */
static atomic_int component_cache_lock[COMPONENT_CACHE_LOCKS];

static inline atomic_int* cache_lock_of(size_t slot_index)
{
    return &component_cache_lock[slot_index & (COMPONENT_CACHE_LOCKS - 1)];
}

static bool component_cache_allocate(void)
{
    const size_t entries = (size_t)1 << COMPONENT_CACHE_LOG2;
    component_cache = calloc(entries, sizeof *component_cache);
    if (!component_cache) {
        fprintf(stderr, "cannot allocate the component cache (%zu MB)\n",
                entries * sizeof *component_cache >> 20);
        return false;
    }
    return true;
}

static void component_cache_free(void)
{
    free(component_cache);
    component_cache = NULL;
}

static inline size_t component_cache_index(Bitboard free_cells, Bitboard maker_near)
{
    uint64_t h = (free_cells * 0x9E3779B97F4A7C15ull) ^ (maker_near * 0xD6E8FEB86659FD93ull);
    h ^= h >> 31;
    return (size_t)h & (((size_t)1 << COMPONENT_CACHE_LOG2) - 1);
}

static inline Bitboard reach_of(Bitboard cells)
{
    Bitboard reach = 0;
    for (; cells; cells &= cells - 1) {
        reach |= board.line_reach[lowest_cell(cells)];
    }
    return reach;
}

/*
 * Safety of one component, memoized.  `breaker_first` receives the Breaker-first ES test and
 * `zone`, when safe, the relevance zone of Breaker's strategy (otherwise all its cells).
 */
static bool component_safety(const Component* comp, Bitboard maker, bool* breaker_first, Bitboard* zone)
{
    *zone = comp->cells;
    if (speculation.cancelled) {
        *breaker_first = false;
        return false;   /* the evaluation is being discarded */
    }
    const Bitboard maker_near = maker & reach_of(comp->cells);
    const size_t   index = component_cache_index(comp->cells, maker_near);

    spin_lock(cache_lock_of(index));
    const ComponentCacheEntry seen = component_cache[index];
    spin_unlock(cache_lock_of(index));
    if (seen.free_cells == comp->cells && seen.maker_near == maker_near) {
        stats.component_cache_hits++;
        *breaker_first = seen.breaker_first;
        *zone = seen.zone;
        return seen.safe;
    }
    stats.component_cache_misses++;

    uint64_t potential = 0;
    const bool safe = component_is_safe(comp, &potential, zone);
    *breaker_first = potential < board.potential_limit;
    if (speculation.cancelled) {
        return safe;   /* possibly cut short: never cache it */
    }

    const ComponentCacheEntry entry = { comp->cells, maker_near, *zone, safe, *breaker_first };
    spin_lock(cache_lock_of(index));
    component_cache[index] = entry;
    spin_unlock(cache_lock_of(index));
    return safe;
}

/* =========================================================================================
 * Whole-position analysis
 * ========================================================================================= */

typedef struct {
    Bitboard unsafe_cells;          /* union of the cells of unsafe components             */
    Bitboard safe_zone;             /* union of the relevance zones of safe components     */
    int      unsafe_components;
    bool     breaker_first_fix;     /* one unsafe component, and it passes Breaker-first ES */
    uint64_t weight[MAX_CELLS];     /* ES weights over all lines, for move ordering         */
} Analysis;

static void analyse(const Hypergraph* h, Bitboard maker, Analysis* out)
{
    memset(out, 0, sizeof *out);
    for (int i = 0; i < h->count; i++) {
        const uint64_t w = line_weight(h->free_count[i]);
        for (Bitboard f = h->free_cells[i]; f; f &= f - 1) {
            out->weight[lowest_cell(f)] += w;
        }
    }

    bool assigned[MAX_LINES] = { false };
    for (int seed = 0; seed < h->count; seed++) {
        if (assigned[seed]) {
            continue;
        }

        /* Gather the component of `seed` (all lines, if components are disabled). */
        Bitboard lines[MAX_LINES];
        uint8_t  sizes[MAX_LINES];
        int      n = 0;
        Bitboard cells = h->free_cells[seed];
        assigned[seed] = true;
        lines[n] = h->free_cells[seed];
        sizes[n] = h->free_count[seed];
        n++;
        bool grew = true;
        while (grew) {
            grew = false;
            for (int i = 0; i < h->count; i++) {
                if (assigned[i] || (options.components && !(h->free_cells[i] & cells))) {
                    continue;
                }
                assigned[i] = true;
                cells |= h->free_cells[i];
                lines[n] = h->free_cells[i];
                sizes[n] = h->free_count[i];
                n++;
                grew = true;
            }
        }

        const Component comp = { n, lines, sizes, cells };
        bool     breaker_first = false;
        Bitboard zone = 0;
        if (component_safety(&comp, maker, &breaker_first, &zone)) {
            out->safe_zone |= zone;
        } else {
            out->unsafe_cells |= cells;
            out->unsafe_components++;
            out->breaker_first_fix = breaker_first;
        }
    }
    out->breaker_first_fix = out->breaker_first_fix && out->unsafe_components == 1;
}

/*
 * Remove dominated moves: u is dominated by v when every line through u passes through v, so a
 * stone on v does at least everything a stone on u does.  Ties (equal line sets) keep the lower
 * cell.  With `include_p2_lines` (strong game, P2 to move) P2's own live lines count as well,
 * because a P2 stone also builds P2 threats; ignoring them prunes P2's counter-attacks.
 *
 * "Every line through u passes through v" is the same as "v lies in the intersection of the
 * lines through u", so the test needs one bitboard per cell: common[u] = AND of those lines.
 * Two lines in different directions meet only in u, so common[u] is usually just {u} and
 * almost every cell is decided by a single AND.
 *
 * `dominators` receives the cell that caused each removal.  A relevance zone that relies on
 * skipping u must contain its dominator v: with Maker handed the cells outside the zone, v is
 * still free and still dominates u.  A dominator may itself be removed later by its own
 * dominator; the chain ends at a kept cell, since tied cells are removed only in favour of a
 * lower one.
 */
static Bitboard undominated_moves(const Hypergraph* h, Position p, Bitboard moves, bool include_p2_lines,
                                  Bitboard* dominators)
{
    Bitboard common[MAX_CELLS];
    for (Bitboard f = moves; f; f &= f - 1) {
        common[lowest_cell(f)] = ~(Bitboard)0;   /* no line yet: every cell qualifies */
    }
    for (int i = 0; i < h->count; i++) {
        const Bitboard line = h->free_cells[i];
        for (Bitboard f = line & moves; f; f &= f - 1) {
            common[lowest_cell(f)] &= line;
        }
    }
    if (include_p2_lines) {
        for (int i = 0; i < board.line_count; i++) {
            const Bitboard line = board.line[i];
            if (line & p.maker) {
                continue;
            }
            for (Bitboard f = line & moves; f; f &= f - 1) {
                common[lowest_cell(f)] &= line;
            }
        }
    }

    Bitboard keep = moves;
    *dominators = 0;
    for (Bitboard f = moves; f; f &= f - 1) {
        const int u = lowest_cell(f);
        for (Bitboard g = common[u] & keep & ~cell_bit(u); g; g &= g - 1) {
            const int v = lowest_cell(g);
            const bool equal = (common[v] >> u) & 1;   /* u also lies on every line through v */
            /* Strictly dominated, or equal and v is the kept representative. */
            if (!equal || v < u) {
                keep &= ~cell_bit(u);
                *dominators |= cell_bit(v);
                break;
            }
        }
    }
    stats.dominated_moves += (uint64_t)popcount(moves & ~keep);
    return keep;
}

/* =========================================================================================
 * Node evaluation
 * ========================================================================================= */

typedef enum { STATUS_OPEN, STATUS_PROVED, STATUS_DISPROVED } Status;   /* PROVED = P1 cannot win */

/*
 * Result of an evaluation besides its status: the moves to search and a relevance zone.
 *   PROVED   `zone` is a relevance zone of the position.
 *   OPEN     `zone` holds the cells that every zone proved for this node must contain on top
 *            of its children's zones: at a Maker node, the zones of the safe components whose
 *            moves were skipped and the dominators of skipped dominated moves.
 * The default, every cell, is always a valid zone.
 */
typedef struct {
    int      count;
    int      cell[MAX_CELLS];
    Bitboard zone;
} MoveList;

/* Order moves by ES weight, putting `urgent` cells first. */
static void order_moves(Bitboard moves, const uint64_t* weight, Bitboard urgent, MoveList* out)
{
    uint64_t score[MAX_CELLS];
    out->count = 0;
    for (Bitboard f = moves; f; f &= f - 1) {
        const int c = lowest_cell(f);
        const uint64_t s = weight[c] + ((urgent & cell_bit(c)) ? ((uint64_t)1 << 40) : 0);
        int j = out->count++;
        while (j > 0 && score[j - 1] < s) {
            out->cell[j] = out->cell[j - 1];
            score[j] = score[j - 1];
            j--;
        }
        out->cell[j] = c;
        score[j] = s;
    }
}

static Status evaluate_maker_to_move(Position p, MoveList* moves)
{
    Hypergraph h;
    hypergraph_build(p, &h);
    for (int i = 0; i < h.count; i++) {
        if (h.free_count[i] <= 1) {
            stats.maker_wins_detected++;
            return STATUS_DISPROVED;
        }
    }

    Bitboard forced = 0;
    if (options.rules == RULES_STRONG) {
        const Bitboard p2_threats = completion_cells(p.breaker, p.maker);
        if (popcount(p2_threats) >= 2) {
            return STATUS_PROVED;    /* P1 cannot stop both P2 completions */
        }
        forced = p2_threats;
    }

    const Bitboard urgent = double_threat_cells(&h);
    if (!forced && options.double_threat && urgent) {
        stats.maker_wins_detected++;
        return STATUS_DISPROVED;
    }

    Analysis a;
    analyse(&h, p.maker, &a);
    if (!a.unsafe_cells) {
        moves->zone = a.safe_zone;
        return STATUS_PROVED;
    }

    Bitboard candidates;
    if (forced) {
        candidates = forced;
    } else if (options.rules == RULES_MAKER_BREAKER && options.restrict_maker) {
        /* Moves in safe components are skipped, so a proof relies on those components'
           strategies (and on the dominators of skipped dominated moves). */
        candidates = a.unsafe_cells;
        moves->zone = a.safe_zone;
        if (options.dominance) {
            Bitboard dominators = 0;
            candidates = undominated_moves(&h, p, candidates, false, &dominators);
            moves->zone |= dominators;
        }
    } else {
        candidates = board.all_cells & ~(p.maker | p.breaker);
        moves->zone = 0;   /* every move is searched */
    }
    order_moves(candidates, a.weight, urgent, moves);
    return STATUS_OPEN;
}

static Status evaluate_breaker_to_move(Position p, MoveList* moves)
{
    if (options.rules == RULES_STRONG && completion_cells(p.breaker, p.maker)) {
        return STATUS_PROVED;    /* P2 completes a line now */
    }

    Hypergraph h;
    hypergraph_build(p, &h);
    Bitboard threats = 0;
    for (int i = 0; i < h.count; i++) {
        if (h.free_count[i] == 0) {
            return STATUS_DISPROVED;
        }
        if (h.free_count[i] == 1) {
            threats |= h.free_cells[i];
        }
    }
    if (popcount(threats) >= 2) {
        return STATUS_DISPROVED;
    }

    if (threats) {
        const uint64_t no_weight[MAX_CELLS] = { 0 };
        order_moves(threats, no_weight, 0, moves);
        return STATUS_OPEN;
    }

    Analysis a;
    analyse(&h, p.maker, &a);
    if (!a.unsafe_cells) {
        moves->zone = a.safe_zone;   /* Breaker passes, then answers inside each component */
        return STATUS_PROVED;
    }
    if (a.breaker_first_fix) {
        stats.breaker_first_leaves++;
        moves->zone = a.safe_zone | a.unsafe_cells;   /* ES needs the whole last component */
        return STATUS_PROVED;
    }
    Bitboard candidates = a.unsafe_cells;
    if (options.dominance) {
        Bitboard dominators = 0;   /* Breaker's own options: irrelevant to zones */
        candidates = undominated_moves(&h, p, candidates, options.rules == RULES_STRONG, &dominators);
    }
    order_moves(candidates, a.weight, double_threat_cells(&h), moves);
    return STATUS_OPEN;
}

static Status evaluate(Position p, bool maker_to_move, MoveList* moves)
{
    stats.evaluations++;
    moves->count = 0;
    moves->zone = board.all_cells;
    if (!(board.all_cells & ~(p.maker | p.breaker))) {
        moves->zone = 0;
        return STATUS_PROVED;   /* board full, no Maker line */
    }
    return maker_to_move ? evaluate_maker_to_move(p, moves) : evaluate_breaker_to_move(p, moves);
}

/* `transform` (if not NULL) receives the symmetry that canonicalized the child. */
static Position child_state(Position p, bool maker_to_move, int cell, int* transform)
{
    if (maker_to_move) {
        p.maker |= cell_bit(cell);
    } else {
        p.breaker |= cell_bit(cell);
    }
    return canonical_state(p, transform);
}

/* A zone given in a child's canonical coordinates, in the parent's coordinates. */
static inline Bitboard zone_to_parent(Bitboard zone, int transform)
{
    return transform == 0 ? zone : apply_symmetry(board.symmetry_inverse[transform], zone);
}

/* =========================================================================================
 * Transposition table
 *
 * Lookups return copies, so no caller ever holds a pointer into the table across a store.
 * ========================================================================================= */

#define PN_INFINITY 0x3FFFFFFFu

typedef struct {
    uint32_t proof;      /* proof number for "P1 cannot win"    */
    uint32_t disproof;   /* disproof number                      */
} ProofNumbers;

static const ProofNumbers PN_PROVED    = { 0, PN_INFINITY };
static const ProofNumbers PN_DISPROVED = { PN_INFINITY, 0 };
static const ProofNumbers PN_UNKNOWN   = { 1, 1 };   /* a child that was not looked up */

static inline bool pn_solved(ProofNumbers v)
{
    return v.proof == 0 || v.disproof == 0;
}

typedef struct {
    Bitboard     maker;
    Bitboard     breaker;
    Bitboard     zone;        /* relevance zone when proved (canonical coordinates)  */
    ProofNumbers value;
    uint32_t     work;        /* subtree effort, used for replacement                */
    uint8_t      turn;        /* 0 = empty, 1 = Breaker to move, 2 = Maker to move  */
    uint8_t      searchers;   /* threads currently searching below this node        */
} TTEntry;

enum {
    TT_BUCKET = 4,
    TT_LOCKS  = 1 << 16   /* striped bucket locks; a power of two */
};

static TTEntry* tt_table = NULL;
static size_t   tt_mask = 0;

/*
 * Threads share the table.  Every bucket is read and written under the spin lock of its
 * stripe and lookups copy the entry out, so no thread sees a half-written entry or keeps a
 * pointer into the table.  A solved value is a proven fact and is never replaced by an
 * unsolved one: a thread may finish a selection loop with values read before another thread
 * solved the node.
 */
static atomic_int tt_lock[TT_LOCKS];

static bool tt_allocate(int log2_entries)
{
    if (log2_entries < 4 || log2_entries > 34) {
        fprintf(stderr, "tt_log2 must be in [4, 34]\n");
        return false;
    }
    const size_t entries = (size_t)1 << log2_entries;
    tt_table = calloc(entries, sizeof *tt_table);
    if (!tt_table) {
        fprintf(stderr, "cannot allocate %zu transposition entries (%zu MB)\n",
                entries, entries * sizeof *tt_table >> 20);
        return false;
    }
    tt_mask = entries - 1;
    return true;
}

static void tt_free(void)
{
    free(tt_table);
    tt_table = NULL;
    tt_mask = 0;
}

static inline uint8_t turn_code(bool maker_to_move)
{
    return maker_to_move ? 2 : 1;
}

/* Index of the first entry of the bucket of (p, turn). */
static inline size_t tt_bucket_index(Position p, uint8_t turn)
{
    uint64_t h = (p.maker * 0x9E3779B97F4A7C15ull) ^ (p.breaker * 0xC2B2AE3D27D4EB4Full) ^ turn;
    h ^= h >> 29;
    return (size_t)h & tt_mask & ~(size_t)(TT_BUCKET - 1);
}

static inline atomic_int* tt_lock_of(size_t bucket)
{
    return &tt_lock[(bucket / TT_BUCKET) & (TT_LOCKS - 1)];
}

/* The entry of (p, turn) in the bucket starting at `bucket`, or NULL.  Caller holds the lock. */
static inline TTEntry* tt_find(size_t bucket, Position p, uint8_t turn)
{
    for (int i = 0; i < TT_BUCKET; i++) {
        TTEntry* e = &tt_table[bucket + i];
        if (e->turn == turn && e->maker == p.maker && e->breaker == p.breaker) {
            return e;
        }
    }
    return NULL;
}

/*
 * Copies out the value of (p, side to move).  `searchers`, if not NULL, gets its thread count;
 * `zone`, if not NULL, its relevance zone (meaningful when the value is proved).
 */
static bool tt_lookup(Position p, bool maker_to_move, ProofNumbers* out, int* searchers, Bitboard* zone)
{
    const uint8_t turn = turn_code(maker_to_move);
    const size_t  bucket = tt_bucket_index(p, turn);

    spin_lock(tt_lock_of(bucket));
    const TTEntry* e = tt_find(bucket, p, turn);
    if (e) {
        *out = e->value;
        if (searchers) {
            *searchers = e->searchers;
        }
        if (zone) {
            *zone = e->zone;
        }
    }
    spin_unlock(tt_lock_of(bucket));
    return e != NULL;
}

/* Stores a value; `zone` is its relevance zone when the value is proved (else ignored). */
static void tt_store(Position p, bool maker_to_move, ProofNumbers value, uint64_t work, Bitboard zone)
{
    const uint8_t turn = turn_code(maker_to_move);
    const size_t  bucket = tt_bucket_index(p, turn);
    uint32_t      effort = work > UINT32_MAX ? UINT32_MAX : (uint32_t)work;

    spin_lock(tt_lock_of(bucket));
    TTEntry* slot = tt_find(bucket, p, turn);
    if (slot) {
        if (pn_solved(slot->value) && !pn_solved(value)) {
            value = slot->value;   /* already solved by another thread: keep the fact */
            zone = slot->zone;
        }
        if (slot->work > effort) {
            effort = slot->work;
        }
    } else {
        for (int i = 0; i < TT_BUCKET && !slot; i++) {
            if (tt_table[bucket + i].turn == 0) {
                slot = &tt_table[bucket + i];
            }
        }
        if (!slot) {
            /* Evict the least effort, preferring an entry that no thread is searching. */
            slot = &tt_table[bucket];
            for (int i = 1; i < TT_BUCKET; i++) {
                TTEntry* e = &tt_table[bucket + i];
                const bool e_idle = e->searchers == 0;
                const bool slot_idle = slot->searchers == 0;
                if ((e_idle && !slot_idle) || (e_idle == slot_idle && e->work < slot->work)) {
                    slot = e;
                }
            }
            stats.tt_evictions++;
        }
        slot->maker = p.maker;
        slot->breaker = p.breaker;
        slot->turn = turn;
        slot->searchers = 0;
    }
    slot->value = value;
    slot->zone = zone;
    slot->work = effort;
    spin_unlock(tt_lock_of(bucket));
}

/*
 * Adds `delta` to the searcher count of (p, side to move).  Returns false, changing nothing,
 * if the position is not in the table (then the matching decrement must be skipped too).
 */
static bool tt_add_searchers(Position p, bool maker_to_move, int delta)
{
    const uint8_t turn = turn_code(maker_to_move);
    const size_t  bucket = tt_bucket_index(p, turn);

    spin_lock(tt_lock_of(bucket));
    TTEntry* e = tt_find(bucket, p, turn);
    if (e) {
        const int count = e->searchers + delta;
        e->searchers = (uint8_t)(count < 0 ? 0 : count > UINT8_MAX ? UINT8_MAX : count);
    }
    spin_unlock(tt_lock_of(bucket));
    return e != NULL;
}

/* =========================================================================================
 * Search bookkeeping
 * ========================================================================================= */

static void note_search_call(void)
{
    stats.search_calls++;
    const unsigned long long calls =
        atomic_fetch_add_explicit(&search_call_counter, 1, memory_order_relaxed) + 1;
    if ((calls & 4095) == 0 && options.time_limit > 0 && elapsed_seconds() > options.time_limit) {
        atomic_store_explicit(&search_aborted, true, memory_order_relaxed);
    }
    if (calls % PROGRESS_INTERVAL == 0) {
        fprintf(stderr, "  [%7.1fs] search calls %llu (all threads)\n", elapsed_seconds(), calls);
    }
}

/* =========================================================================================
 * Engine 1: depth-first AND/OR search.  Returns true when P1 (Maker) wins.
 * ========================================================================================= */

static bool dfs_p1_wins(Position p, bool maker_to_move)
{
    note_search_call();
    if (search_should_stop()) {
        return false;
    }

    ProofNumbers known;
    if (tt_lookup(p, maker_to_move, &known, NULL, NULL) && pn_solved(known)) {
        return known.disproof == 0;
    }

    const uint64_t calls_before = stats.search_calls;
    MoveList moves;
    const Status status = evaluate(p, maker_to_move, &moves);

    bool p1_wins;
    if (status == STATUS_PROVED) {
        p1_wins = false;
    } else if (status == STATUS_DISPROVED) {
        p1_wins = true;
    } else if (maker_to_move) {
        p1_wins = false;
        for (int i = 0; i < moves.count && !p1_wins && !search_should_stop(); i++) {
            p1_wins = dfs_p1_wins(child_state(p, true, moves.cell[i], NULL), false);
        }
    } else {
        p1_wins = true;
        for (int i = 0; i < moves.count && p1_wins && !search_should_stop(); i++) {
            p1_wins = dfs_p1_wins(child_state(p, false, moves.cell[i], NULL), true);
        }
    }

    if (search_should_stop()) {
        return false;   /* incomplete: never store */
    }
    /* This engine does not track zones (the option is off for it): store the trivial one. */
    tt_store(p, maker_to_move, p1_wins ? PN_DISPROVED : PN_PROVED, stats.search_calls - calls_before,
             board.all_cells);
    return p1_wins;
}

/* =========================================================================================
 * Engine 2: df-pn.  Proof target "P1 cannot win"; Maker nodes are AND, Breaker nodes OR.
 * ========================================================================================= */

static inline uint32_t pn_add(uint32_t a, uint32_t b)
{
    if (a >= PN_INFINITY || b >= PN_INFINITY) {
        return PN_INFINITY;
    }
    const uint64_t sum = (uint64_t)a + b;
    return sum >= PN_INFINITY ? PN_INFINITY - 1 : (uint32_t)sum;
}

static inline uint32_t pn_min(uint32_t a, uint32_t b)
{
    return a < b ? a : b;
}

/*
 * Threshold that keeps the selected child below its second-best sibling.  Plain df-pn uses
 * second + 1, which switches between two close siblings on every unit of progress; the
 * 1 + epsilon rule (Pawlewicz and Lew) allows second * (1 + 1/DFPN_EPSILON_INVERSE) + 1.
 * DFPN_EPSILON_INVERSE = 0 gives plain df-pn.
 */
#ifndef DFPN_EPSILON_INVERSE
#define DFPN_EPSILON_INVERSE 2
#endif

static inline uint32_t pn_second_threshold(uint32_t second)
{
    if (second >= PN_INFINITY) {
        return PN_INFINITY;
    }
    const uint32_t slack = DFPN_EPSILON_INVERSE > 0 ? second / DFPN_EPSILON_INVERSE + 1 : 1;
    return pn_add(second, slack);
}

/* Threshold for the selected child when the parent's total must stay below `threshold`. */
static inline uint32_t pn_child_threshold(uint32_t threshold, uint32_t total, uint32_t child)
{
    if (threshold >= PN_INFINITY) {
        return PN_INFINITY;
    }
    const uint64_t t = (uint64_t)threshold - total + child;   /* total < threshold here */
    return t >= PN_INFINITY ? PN_INFINITY - 1 : (uint32_t)t;
}

/* Initial proof numbers of an evaluated node (mobility initialization). */
static ProofNumbers initial_numbers(Status status, bool maker_to_move, int move_count)
{
    if (status == STATUS_PROVED) {
        return PN_PROVED;
    }
    if (status == STATUS_DISPROVED) {
        return PN_DISPROVED;
    }
    ProofNumbers value;
    if (maker_to_move) {
        /* AND node: every move must be refuted. */
        value.proof = (uint32_t)move_count;
        value.disproof = 1;
    } else {
        /* OR node: one good reply suffices. */
        value.proof = 1;
        value.disproof = (uint32_t)move_count;
    }
    return value;
}

/*
 * Deterministic DFPN with threads: running mean of the cost of one child evaluation, kept by
 * the searching thread.  A batch of children is shared out only when its expected serial cost
 * repays waking a thread team (PARALLEL_BATCH_SECONDS); cheap evaluations, as on k = 4
 * boards, stay serial.  The estimate only decides speed: both paths give the same search.
 */
#ifndef PARALLEL_BATCH_SECONDS
#define PARALLEL_BATCH_SECONDS 5e-4
#endif

static double evaluation_seconds_mean = 0.0;

static inline bool measuring_evaluations(void)
{
    return options.engine == ENGINE_DFPN && options.threads > 1;
}

static inline void note_evaluation_seconds(double seconds)
{
    evaluation_seconds_mean += (seconds - evaluation_seconds_mean) / 32.0;
}

/*
 * Proof numbers of a canonical state, evaluating (and storing) it on a table miss.
 * `searchers` receives the number of threads currently searching below it and `zone` its
 * relevance zone (meaningful when proved), in its own canonical coordinates.
 */
static ProofNumbers lookup_or_evaluate(Position p, bool maker_to_move, int* searchers, Bitboard* zone)
{
    ProofNumbers value;
    *searchers = 0;
    if (tt_lookup(p, maker_to_move, &value, searchers, zone)) {
        return value;
    }
    const bool   measure = measuring_evaluations();
    const double started = measure ? wall_seconds() : 0.0;
    MoveList     moves;
    const Status status = evaluate(p, maker_to_move, &moves);
    if (measure) {
        note_evaluation_seconds(wall_seconds() - started);
    }
    value = initial_numbers(status, maker_to_move, moves.count);
    *zone = moves.zone;
    tt_store(p, maker_to_move, value, 1, *zone);
    return value;
}

/*
 * Children evaluated ahead of the selection loop.  ready[i] means value[i] (with zone[i]) is
 * child i's evaluation and is not yet in the table: the selection loop stores it at the moment
 * the serial program would have evaluated and stored it, so the table goes through exactly the
 * serial sequence of operations, evictions included.
 */
typedef struct {
    ProofNumbers value[MAX_CELLS];
    Bitboard     zone[MAX_CELLS];
    bool         ready[MAX_CELLS];
} Prefetch;

#ifdef _OPENMP
/*
 * True when this child's value ends the parent's selection loop: a proved Maker-to-move child
 * of an OR node, or a disproved (Maker wins) Breaker-to-move child of an AND node.
 */
static inline bool child_ends_loop(ProofNumbers value, bool child_maker_to_move)
{
    return child_maker_to_move ? value.proof == 0 : value.disproof == 0;
}

static void atomic_lower(atomic_int* target, int value)
{
    int current = atomic_load_explicit(target, memory_order_relaxed);
    while (value < current &&
           !atomic_compare_exchange_weak_explicit(target, &current, value, memory_order_relaxed,
                                                  memory_order_relaxed)) {
        /* `current` was reloaded; retry while `value` is still lower */
    }
}
#endif

/*
 * Deterministic DFPN with threads: evaluates in parallel the children that the serial
 * selection loop is about to evaluate, i.e. those missing from the table up to the first
 * child that ends the loop.  Threads take children in index order; once a child ends the
 * loop, evaluations of later children are cancelled (or never started) and discarded, so
 * `out` holds exactly the evaluations the serial loop would make.  Workers touch only their
 * own locals, their own counters and the locked component cache.
 */
static void prefetch_children(const Position* child, int count, bool child_maker_to_move, Prefetch* out)
{
    for (int i = 0; i < count; i++) {
        out->ready[i] = false;
    }
#ifdef _OPENMP
    if (options.engine != ENGINE_DFPN || options.threads < 2 || omp_in_parallel()) {
        return;
    }
    int missing[MAX_CELLS];
    int missing_count = 0;
    for (int i = 0; i < count; i++) {
        ProofNumbers known;
        if (!tt_lookup(child[i], child_maker_to_move, &known, NULL, NULL)) {
            missing[missing_count++] = i;
        } else if (child_ends_loop(known, child_maker_to_move)) {
            break;   /* the serial loop stops here: later children are never needed */
        }
    }
    if (missing_count < 2 || missing_count * evaluation_seconds_mean < PARALLEL_BATCH_SECONDS) {
        return;   /* too little work to share out: the selection loop evaluates on demand */
    }

    ProofNumbers value[MAX_CELLS];
    Bitboard     zone[MAX_CELLS];
    double       seconds[MAX_CELLS];
    bool         complete[MAX_CELLS];
    atomic_int   cutoff;   /* lowest j whose child ends the loop; missing_count while none */
    atomic_init(&cutoff, missing_count);
    const int team = missing_count < options.threads ? missing_count : options.threads;

    OMP(parallel num_threads(team))
    {
        OMP(for schedule(dynamic, 1))
        for (int j = 0; j < missing_count; j++) {
            complete[j] = false;
            if (atomic_load_explicit(&cutoff, memory_order_relaxed) < j) {
                continue;   /* an earlier child already ends the loop */
            }
            speculation.cutoff = &cutoff;
            speculation.index = j;
            speculation.cancelled = false;

            const double started = wall_seconds();
            MoveList     moves;
            const Status status = evaluate(child[missing[j]], child_maker_to_move, &moves);
            seconds[j] = wall_seconds() - started;

            const bool cancelled = speculation.cancelled;
            speculation.cutoff = NULL;
            if (cancelled) {
                stats.evaluations_cancelled++;
                continue;
            }
            value[j] = initial_numbers(status, child_maker_to_move, moves.count);
            zone[j] = moves.zone;
            complete[j] = true;
            if (child_ends_loop(value[j], child_maker_to_move)) {
                atomic_lower(&cutoff, j);
            }
        }
        statistics_fold_helper();
    }

    /* Every j up to the final cutoff is complete (a j is cancelled only beyond the cutoff,
       and the cutoff never rises); later ones are discarded. */
    const int last = atomic_load(&cutoff) < missing_count ? atomic_load(&cutoff) : missing_count - 1;
    for (int j = 0; j <= last; j++) {
        out->ready[missing[j]] = complete[j];
        if (complete[j]) {   /* value, zone and seconds are written only for complete ones */
            out->value[missing[j]] = value[j];
            out->zone[missing[j]] = zone[j];
            note_evaluation_seconds(seconds[j]);
        }
    }
#else
    (void)child;
    (void)child_maker_to_move;
#endif
}
/*
 * At an AND node (Maker to move) a child is selected by its disproof number, the smallest of
 * which is the node's disproof number, while the children's proof numbers add up.  At an OR
 * node the roles swap.  `key` is the selected-by number, `sum` the added-up one.
 */
static inline uint32_t key_of(ProofNumbers v, bool and_node)
{
    return and_node ? v.disproof : v.proof;
}

static inline uint32_t sum_of(ProofNumbers v, bool and_node)
{
    return and_node ? v.proof : v.disproof;
}

static inline ProofNumbers from_key_and_sum(uint32_t key, uint32_t sum, bool and_node)
{
    const ProofNumbers v = { and_node ? sum : key, and_node ? key : sum };
    return v;
}

/*
 * Selection key of a child that `searchers` other threads are working on (parallel engine):
 * it looks (1 + searchers) times harder, so idle threads spread over promising siblings
 * instead of piling into one subtree ("virtual proof numbers").
 */
static inline uint32_t virtual_key(uint32_t key, int searchers)
{
    if (searchers == 0 || key >= PN_INFINITY) {
        return key;
    }
    const uint64_t v = (uint64_t)key * (uint64_t)(1 + searchers) + (uint64_t)searchers;
    return v >= PN_INFINITY ? PN_INFINITY - 1 : (uint32_t)v;
}

/*
 * A Maker move proved to win lies outside the zone of a refuted sibling, which says the move
 * loses.  Both cannot hold, so a zone is wrong: stop rather than risk an unsound proof.
 */
static void zone_contradiction(Position p, int cell)
{
    fprintf(stderr,
            "internal error: Maker move %d wins, yet a sibling's relevance zone refutes it\n"
            "  position: maker %016llx, breaker %016llx\n",
            cell, (unsigned long long)p.maker, (unsigned long long)p.breaker);
    abort();
}

/*
 * Relevance zone of a proved AND node (Maker to move), after Hsu et al.'s Algorithm 4.  The
 * moves are visited in order.  A move outside the intersection of the zones collected so far
 * is refuted by one of them; any other move must be proved, and its zone is added.  A move
 * that the selection loop pruned through the zone of a *later* sibling is then covered by
 * adding that sibling's zone.  The node's own requirement (skipped safe components and
 * dominators) comes from the evaluation.  `zone[i]` is in the parent's coordinates and set
 * when `value[i]` is proved.
 */
static Bitboard and_node_zone(const MoveList* moves, const ProofNumbers* value, const Bitboard* zone)
{
    /* (Visiting the smallest zones first instead of move order was measured: no gain.) */
    Bitboard result = moves->zone;
    Bitboard allowed = ~(Bitboard)0;
    Bitboard pending = 0;   /* moves left to a later sibling's zone */
    for (int i = 0; i < moves->count; i++) {
        const Bitboard move = cell_bit(moves->cell[i]);
        if (!(allowed & move)) {
            continue;
        }
        if (value[i].proof == 0) {
            result |= zone[i];
            allowed &= zone[i];
        } else {
            pending |= move;
        }
    }
    for (Bitboard f = pending; f; f &= f - 1) {
        const Bitboard move = cell_bit(lowest_cell(f));
        if (!(allowed & move)) {
            continue;   /* a zone added meanwhile refutes it */
        }
        int witness = -1;
        for (int j = 0; j < moves->count && witness < 0; j++) {
            if (value[j].proof == 0 && !(zone[j] & move)) {
                witness = j;
            }
        }
        if (witness < 0) {
            fprintf(stderr, "internal error: a pruned Maker move has no refuting zone\n");
            abort();
        }
        result |= zone[witness];
        allowed &= zone[witness];
    }
    return result;
}

static void dfpn_mid(Position p, bool maker_to_move, uint32_t proof_threshold, uint32_t disproof_threshold)
{
    note_search_call();
    if (search_should_stop()) {
        return;
    }

    /* One evaluation per call: the table decides whether to stop, the evaluation supplies the
       move list (a table miss here means the root, or an entry evicted since the parent's
       look-up). */
    ProofNumbers value;
    if (tt_lookup(p, maker_to_move, &value, NULL, NULL) &&
        (pn_solved(value) || value.proof >= proof_threshold || value.disproof >= disproof_threshold)) {
        return;
    }
    MoveList moves;
    const Status status = evaluate(p, maker_to_move, &moves);
    if (status != STATUS_OPEN) {
        tt_store(p, maker_to_move, initial_numbers(status, maker_to_move, 0), 1, moves.zone);
        return;
    }
    Position child[MAX_CELLS];
    int      child_transform[MAX_CELLS];   /* symmetry that canonicalized each child */
    for (int i = 0; i < moves.count; i++) {
        child[i] = child_state(p, maker_to_move, moves.cell[i], &child_transform[i]);
    }
    Prefetch prefetch;
    prefetch_children(child, moves.count, !maker_to_move, &prefetch);

    const bool     and_node = maker_to_move;
    const bool     zone_pruning = options.zones && and_node;
    const uint32_t key_threshold = and_node ? disproof_threshold : proof_threshold;
    const uint32_t sum_threshold = and_node ? proof_threshold : disproof_threshold;
    const bool     entered = tt_add_searchers(p, maker_to_move, +1);
    const uint64_t calls_before = stats.search_calls;

    for (;;) {
        /* Look the children up in move order, until one decides the node.  At an AND node a
           move already outside `allowed` is refuted by an earlier sibling's zone: it is
           neither looked up nor evaluated (its prefetched value, if any, is dropped, as the
           serial program never computes it). */
        ProofNumbers child_value[MAX_CELLS];       /* as stored in the table                 */
        Bitboard     child_zone[MAX_CELLS];        /* parent coordinates; set when proved    */
        int          child_searchers[MAX_CELLS];
        int          looked_up = 0;
        Bitboard     allowed = ~(Bitboard)0;       /* AND node: moves no proved zone refutes */

        for (int i = 0; i < moves.count; i++) {
            ProofNumbers c;
            Bitboard     zone = board.all_cells;
            int          searchers = 0;
            looked_up = i + 1;
            if (zone_pruning && !(allowed & cell_bit(moves.cell[i]))) {
                prefetch.ready[i] = false;
                child_value[i] = PN_UNKNOWN;   /* pruned below */
                child_zone[i] = 0;
                child_searchers[i] = 0;
                continue;
            }
            if (prefetch.ready[i]) {
                c = prefetch.value[i];   /* evaluated ahead: store it where the serial loop would */
                zone = prefetch.zone[i];
                prefetch.ready[i] = false;
                tt_store(child[i], !maker_to_move, c, 1, zone);
            } else {
                c = lookup_or_evaluate(child[i], !maker_to_move, &searchers, &zone);
            }
            child_value[i] = c;
            child_zone[i] = c.proof == 0 ? zone_to_parent(zone, child_transform[i]) : 0;
            child_searchers[i] = searchers;
            if (zone_pruning && c.proof == 0) {
                allowed &= child_zone[i];
            }
            if (key_of(c, and_node) == 0) {
                break;   /* solved: the remaining children cannot change that */
            }
        }

        /* Combine.  At an AND node, a move outside `allowed` lies outside the zone of a proved
           sibling, so it is refuted as well (Hsu et al., Property 2) and counts as proved. */
        uint32_t     key = PN_INFINITY;   /* min over children */
        uint32_t     sum = 0;             /* sum over children */
        int          best_index = -1;     /* serial choice: smallest key        */
        uint32_t     second = PN_INFINITY;
        int          virtual_index = -1;  /* choice with other threads counted  */
        uint32_t     virtual_best = PN_INFINITY;
        uint32_t     virtual_second = PN_INFINITY;
        ProofNumbers selection_value[MAX_CELLS];
        int          pruned = 0;

        for (int i = 0; i < looked_up; i++) {
            ProofNumbers c = child_value[i];
            if (zone_pruning && c.proof != 0 && !(allowed & cell_bit(moves.cell[i]))) {
                if (c.disproof == 0) {
                    zone_contradiction(p, moves.cell[i]);
                }
                c = PN_PROVED;
                pruned++;
            }
            selection_value[i] = c;
            const uint32_t k = key_of(c, and_node);
            sum = pn_add(sum, sum_of(c, and_node));
            if (k < key) {
                second = key;
                key = k;
                best_index = i;
            } else if (k < second) {
                second = k;
            }
            const uint32_t vk = virtual_key(k, child_searchers[i]);
            if (vk < virtual_best) {
                virtual_second = virtual_best;
                virtual_best = vk;
                virtual_index = i;
            } else if (vk < virtual_second) {
                virtual_second = vk;
            }
        }

        value = from_key_and_sum(key, sum, and_node);
        Bitboard zone = board.all_cells;
        if (value.proof == 0 && options.zones) {
            if (and_node) {
                zone = and_node_zone(&moves, child_value, child_zone);
                stats.zone_pruned_moves += (uint64_t)pruned;
                stats.zone_nodes++;
                stats.zone_cells += (uint64_t)popcount(zone);
                stats.zone_free_cells += (uint64_t)popcount(board.all_cells & ~(p.maker | p.breaker));
            } else {
                zone = cell_bit(moves.cell[best_index]) | child_zone[best_index];
            }
        }
        tt_store(p, maker_to_move, value, stats.search_calls - calls_before + 1, zone);
        if (pn_solved(value) || key >= key_threshold || sum >= sum_threshold || best_index < 0) {
            break;
        }

        /* Take the virtual choice unless its true key already reaches this node's threshold
           (it would return at once); the serial choice always makes progress. */
        int      chosen = best_index;
        uint32_t chosen_second = second;
        if (virtual_index >= 0 && key_of(selection_value[virtual_index], and_node) < key_threshold) {
            chosen = virtual_index;
            chosen_second = virtual_second;
        }
        const uint32_t child_key_threshold = pn_min(key_threshold, pn_second_threshold(chosen_second));
        const uint32_t child_sum_threshold =
            pn_child_threshold(sum_threshold, sum, sum_of(selection_value[chosen], and_node));
        const ProofNumbers child_threshold =
            from_key_and_sum(child_key_threshold, child_sum_threshold, and_node);

        dfpn_mid(child[chosen], !maker_to_move, child_threshold.proof, child_threshold.disproof);
        if (search_should_stop()) {
            break;
        }
    }
    if (entered) {
        tt_add_searchers(p, maker_to_move, -1);
    }
}

/* One searching thread: root iterations until the root is solved or the time runs out. */
static void dfpn_root_loop(Position root)
{
    while (!search_should_stop()) {
        dfpn_mid(root, true, PN_INFINITY, PN_INFINITY);
        ProofNumbers value;
        if (tt_lookup(root, true, &value, NULL, NULL) && pn_solved(value)) {
            atomic_store_explicit(&search_finished, true, memory_order_relaxed);
        }
    }
}

/*
 * Returns 1 if P1 wins, 0 if P1 cannot win, -1 if unresolved.  The parallel engine runs one
 * root loop per thread over the shared table; the first thread to see the root solved stops
 * them all.
 */
static int dfpn_solve(Position root)
{
#ifdef _OPENMP
    if (options.engine == ENGINE_PARALLEL_DFPN && options.threads > 1) {
        OMP(parallel)
        {
            dfpn_root_loop(root);
            statistics_fold_helper();
        }
    } else {
        dfpn_root_loop(root);
    }
#else
    dfpn_root_loop(root);
#endif
    ProofNumbers value;
    if (!tt_lookup(root, true, &value, NULL, NULL) || !pn_solved(value)) {
        return -1;
    }
    return value.disproof == 0 ? 1 : 0;
}

/* =========================================================================================
 * Command line
 * ========================================================================================= */

static void options_from_flags(int flags)
{
    options.components     = flags & 1;
    options.matching       = flags & 2;
    options.subsumption    = flags & 4;
    options.restrict_maker = flags & 8;
    options.double_threat  = flags & 16;
    options.greedy_hybrid  = flags & 32;
    options.dominance      = flags & 64;
    options.reduced_state  = flags & 128;
    options.pair_cover     = flags & 256;
    options.twins          = flags & 512;
    options.zones          = flags & 1024;
}

/* Every rule except relevance zones (1024), which are off by default (see the header). */
enum { DEFAULT_FLAGS = 1023 };

static const char* engine_name(Engine engine)
{
    switch (engine) {
    case ENGINE_DFS:           return "DFS";
    case ENGINE_DFPN:          return "DFPN";
    case ENGINE_PARALLEL_DFPN: return "PDFPN";
    }
    return "?";
}

static void print_usage(const char* program)
{
    fprintf(stderr,
            "usage: %s m n k [MB|SG] [flags] [tt_log2] [PDFPN|DFPN|DFS] [time_limit_seconds] [threads]\n"
            "  flags: 1 components, 2 2-matching, 4 subsumption, 8 restrict Maker,\n"
            "         16 double-threat stop, 32 greedy hybrid, 64 dominance,\n"
            "         128 reduced MB state, 256 exact pair cover, 512 twin pairs,\n"
            "         1024 relevance zones (MB, df-pn engines)\n"
            "         (default 1023 = all but relevance zones; 2047 = all)\n"
            "  engines: PDFPN (default; all threads search the tree, the proof varies run to run),\n"
            "           DFPN (children evaluated in parallel; exactly the serial proof), DFS (serial)\n"
            "  threads: default all logical processors\n",
            program);
}

int main(int argc, char** argv)
{
    if (argc < 4) {
        print_usage(argv[0]);
        return 2;
    }
    const int rows = atoi(argv[1]);
    const int cols = atoi(argv[2]);
    const int k = atoi(argv[3]);

    options.rules = (argc > 4 && argv[4][0] == 'S') ? RULES_STRONG : RULES_MAKER_BREAKER;
    options_from_flags(argc > 5 ? atoi(argv[5]) : DEFAULT_FLAGS);
    options.tt_log2 = argc > 6 ? atoi(argv[6]) : 24;
    options.engine = ENGINE_PARALLEL_DFPN;
    if (argc > 7 && strcmp(argv[7], "DFS") == 0) {
        options.engine = ENGINE_DFS;
    } else if (argc > 7 && strcmp(argv[7], "DFPN") == 0) {
        options.engine = ENGINE_DFPN;
    }
    options.time_limit = argc > 8 ? atof(argv[8]) : 0.0;

    options.threads = 1;
#ifdef _OPENMP
    options.threads = argc > 9 ? atoi(argv[9]) : omp_get_num_procs();
    if (options.threads < 1) {
        options.threads = 1;
    }
    omp_set_num_threads(options.threads);
#endif
    if (options.engine == ENGINE_DFS) {
        options.threads = 1;   /* the DFS engine is serial */
    }

    if (options.rules == RULES_STRONG) {
        /* Unsound with P2 lines in play (see the header). Breaker dominance stays allowed. */
        options.restrict_maker = false;
        options.reduced_state = false;
        options.zones = false;
    }
    if (options.engine == ENGINE_DFS) {
        options.zones = false;   /* the DFS engine does not track zones */
    }
    if (!board_init(rows, cols, k) || !tt_allocate(options.tt_log2)) {
        return 1;
    }
    if (!component_cache_allocate()) {
        tt_free();
        return 1;
    }

    start_time = wall_seconds();
    const Position root = canonical_state((Position){ 0, 0 }, NULL);
    int result;
    if (options.engine == ENGINE_DFS) {
        const bool p1_wins = dfs_p1_wins(root, true);
        result = atomic_load(&search_aborted) ? -1 : (p1_wins ? 1 : 0);
    } else {
        result = dfpn_solve(root);
    }
    const double seconds = elapsed_seconds();
    const Statistics total = report_totals();

    const char* verdict;
    if (result < 0) {
        verdict = "UNRESOLVED (time limit)";
    } else if (result == 0) {
        verdict = "P1 CANNOT WIN (draw)";
    } else if (options.rules == RULES_STRONG) {
        verdict = "not proved (P1 wins against restricted P2)";
    } else {
        verdict = "P1 (Maker) WINS";
    }

    printf("(%d,%d,%d) %s %s: %s\n", rows, cols, k,
           options.rules == RULES_STRONG ? "SG" : "MB",
           engine_name(options.engine), verdict);
    printf("  search calls %llu, evaluations %llu, time %.2f s, threads %d\n",
           (unsigned long long)total.search_calls, (unsigned long long)total.evaluations, seconds,
           options.threads);
    printf("  safe components: ES %llu, 2-matching %llu, cover %llu, cover+ES %llu, greedy hybrid %llu"
           " (cover budget exhausted %llu)\n",
           (unsigned long long)total.safe_by_es, (unsigned long long)total.safe_by_matching,
           (unsigned long long)total.safe_by_cover, (unsigned long long)total.safe_by_cover_es,
           (unsigned long long)total.safe_by_greedy_hybrid, (unsigned long long)total.cover_budget_exhausted);
    for (int hot = board.k; hot >= 2 && options.pair_cover; hot--) {
        printf("  cover, lines of size <= %d: %llu attempts, %llu refuted at once, %llu exhausted, %llu covers found, %llu safe\n",
               hot, (unsigned long long)total.cover_attempts[hot], (unsigned long long)total.cover_refuted[hot],
               (unsigned long long)total.cover_exhausted[hot],
               (unsigned long long)total.cover_found[hot], (unsigned long long)total.cover_safe[hot]);
    }
    printf("  twin pairs removed %llu (components emptied %llu), unsafe by double threat %llu\n",
           (unsigned long long)total.twin_pairs, (unsigned long long)total.safe_by_twins,
           (unsigned long long)total.unsafe_by_double_threat);
    printf("  Breaker-first leaves %llu, Maker wins detected %llu, dominated moves skipped %llu\n",
           (unsigned long long)total.breaker_first_leaves, (unsigned long long)total.maker_wins_detected,
           (unsigned long long)total.dominated_moves);
    if (options.zones) {
        const double nodes = total.zone_nodes > 0 ? (double)total.zone_nodes : 1.0;
        printf("  relevance zones: %llu Maker moves refuted by a sibling's zone; %llu Maker nodes"
               " proved, zone %.1f of %.1f free cells on average\n",
               (unsigned long long)total.zone_pruned_moves, (unsigned long long)total.zone_nodes,
               (double)total.zone_cells / nodes, (double)total.zone_free_cells / nodes);
    }
    printf("  component cache: %llu hits, %llu misses\n", (unsigned long long)total.component_cache_hits,
           (unsigned long long)total.component_cache_misses);
    if (options.engine == ENGINE_DFPN && options.threads > 1) {
        printf("  speculative evaluations cancelled: %llu\n",
               (unsigned long long)total.evaluations_cancelled);
    }
    printf("  transposition table: 2^%d entries, %llu evictions\n", options.tt_log2,
           (unsigned long long)total.tt_evictions);
    if (result < 0 && options.engine != ENGINE_DFS && total.tt_evictions > tt_mask) {
        /* df-pn can cycle when evicted nodes come back with fresh (smaller) proof numbers. */
        printf("  warning: heavy eviction; df-pn may be cycling - try a larger tt_log2\n");
    }

    component_cache_free();
    tt_free();
    return 0;
}
