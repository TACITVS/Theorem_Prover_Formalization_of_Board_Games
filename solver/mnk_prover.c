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
 * ------------------------------------------------------------------------------------------
 * Build
 * ------------------------------------------------------------------------------------------
 *
 *   Linux / WSL:   gcc -std=c11 -O3 -march=native -o mnk_prover mnk_prover.c
 *   Windows:       clang -std=c11 -O3 -march=native -o mnk_prover.exe mnk_prover.c
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
 *   mnk_prover m n k [MB|SG] [flags] [tt_log2] [DFS|DFPN] [time_limit_seconds]
 *
 *   flags (default 1023 = all):
 *       1 components          2 2-matching pairing      4 subsumption
 *       8 restrict Maker      16 double-threat stop     32 greedy pair+ES hybrid
 *       64 dominance          128 reduced MB state      256 exact pair cover
 *       512 twin pairs
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

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
typedef enum { ENGINE_DFS, ENGINE_DFPN } Engine;

typedef struct {
    Rules  rules;
    Engine engine;
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
    int    tt_log2;         /* transposition table holds 2^tt_log2 entries             */
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
} Statistics;

static Options    options;
static Statistics stats;
static bool       search_aborted = false;
static double     start_time;

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

/* The smallest image of the position under the symmetry group. */
static Position symmetry_canonical(Position p)
{
    Position best = p;
    for (int t = 1; t < board.symmetry_count; t++) {
        const Position image = { apply_symmetry(t, p.maker), apply_symmetry(t, p.breaker) };
        if (position_less(image, best)) {
            best = image;
        }
    }
    return best;
}

/*
 * Canonical search state.  In Maker-Breaker with the reduced state, a position is
 * equivalent to (A, B) = (Maker stones on live lines, free cells on live lines): a line is
 * live exactly when it lies inside A ∪ B, and its free cells are its cells in B.  The state
 * is represented as the position with Maker stones A and Breaker stones on every other cell,
 * so the ordinary evaluation applies to it unchanged.
 */
static Position canonical_state(Position p)
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
    return symmetry_canonical(p);
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

static bool has_two_matching(const Component* comp)
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

/* Greedy hybrid: pair the lines with at most `hot` free cells using low-degree cells. */
static bool greedy_hybrid_safe(const Component* comp)
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
    return has_two_matching(&family);
}

static bool cover_recurse(CoverSearch* s, const Bitboard* open, int open_count)
{
    if (open_count == 0) {
        return true;   /* every line contains a chosen pair */
    }
    if (--s->budget < 0 || !cover_may_exist(open, open_count)) {
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

    /* Candidate pairs inside that line, ordered by how many open lines they cover. */
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

    for (int q = 0; q < cand_count; q++) {
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

/* Cover all lines (strongest); optionally, cover only the short lines and use ES for the rest. */
static bool pair_cover_safe(const Component* comp)
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
 * `sizes` and returns their number.
 */
static int remove_twin_pairs(const Component* comp, Bitboard* lines, uint8_t* sizes)
{
    int n = comp->n;
    memcpy(lines, comp->lines, (size_t)n * sizeof lines[0]);
    memcpy(sizes, comp->sizes, (size_t)n * sizeof sizes[0]);

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
 */
static bool component_is_safe(const Component* original, uint64_t* potential_out)
{
    Bitboard   reduced_lines[MAX_LINES];
    uint8_t    reduced_sizes[MAX_LINES];
    Component  reduced;
    const Component* comp = original;

    if (options.twins) {
        const int n = remove_twin_pairs(original, reduced_lines, reduced_sizes);
        if (n == 0) {
            *potential_out = 0;
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
        return true;
    }
    /* A cell on two 2-cell lines with different partners wins the component for Maker (who
       moves first in it), so no test below can succeed. */
    if (double_threat_cells_of(comp->lines, comp->sizes, comp->n)) {
        stats.unsafe_by_double_threat++;
        return false;
    }
    if (options.matching && has_two_matching(comp)) {
        stats.safe_by_matching++;
        return true;
    }
    if (options.greedy_hybrid && greedy_hybrid_safe(comp)) {
        return true;
    }
    if (options.pair_cover && pair_cover_safe(comp)) {
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
    bool     safe;
    bool     breaker_first;  /* Breaker-first ES holds (sum of weights < 1)                  */
} ComponentCacheEntry;

enum { COMPONENT_CACHE_LOG2 = 21 };

static ComponentCacheEntry* component_cache = NULL;

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

static inline ComponentCacheEntry* component_cache_slot(Bitboard free_cells, Bitboard maker_near)
{
    uint64_t h = (free_cells * 0x9E3779B97F4A7C15ull) ^ (maker_near * 0xD6E8FEB86659FD93ull);
    h ^= h >> 31;
    return &component_cache[(size_t)h & (((size_t)1 << COMPONENT_CACHE_LOG2) - 1)];
}

static inline Bitboard reach_of(Bitboard cells)
{
    Bitboard reach = 0;
    for (; cells; cells &= cells - 1) {
        reach |= board.line_reach[lowest_cell(cells)];
    }
    return reach;
}

/* Safety of one component, memoized.  `breaker_first` receives the Breaker-first ES test. */
static bool component_safety(const Component* comp, Bitboard maker, bool* breaker_first)
{
    const Bitboard maker_near = maker & reach_of(comp->cells);
    ComponentCacheEntry* slot = component_cache_slot(comp->cells, maker_near);
    if (slot->free_cells == comp->cells && slot->maker_near == maker_near) {
        stats.component_cache_hits++;
        *breaker_first = slot->breaker_first;
        return slot->safe;
    }
    stats.component_cache_misses++;

    uint64_t potential = 0;
    const bool safe = component_is_safe(comp, &potential);
    *breaker_first = potential < board.potential_limit;

    slot->free_cells = comp->cells;
    slot->maker_near = maker_near;
    slot->safe = safe;
    slot->breaker_first = *breaker_first;
    return safe;
}

/* =========================================================================================
 * Whole-position analysis
 * ========================================================================================= */

typedef struct {
    Bitboard unsafe_cells;          /* union of the cells of unsafe components             */
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
        bool breaker_first = false;
        if (!component_safety(&comp, maker, &breaker_first)) {
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
 */
static Bitboard undominated_moves(const Hypergraph* h, Position p, Bitboard moves, bool include_p2_lines)
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
    for (Bitboard f = moves; f; f &= f - 1) {
        const int u = lowest_cell(f);
        for (Bitboard g = common[u] & keep & ~cell_bit(u); g; g &= g - 1) {
            const int v = lowest_cell(g);
            const bool equal = (common[v] >> u) & 1;   /* u also lies on every line through v */
            /* Strictly dominated, or equal and v is the kept representative. */
            if (!equal || v < u) {
                keep &= ~cell_bit(u);
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

typedef struct {
    int count;
    int cell[MAX_CELLS];
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
        return STATUS_PROVED;
    }

    Bitboard candidates;
    if (forced) {
        candidates = forced;
    } else if (options.rules == RULES_MAKER_BREAKER && options.restrict_maker) {
        candidates = a.unsafe_cells;
        if (options.dominance) {
            candidates = undominated_moves(&h, p, candidates, false);
        }
    } else {
        candidates = board.all_cells & ~(p.maker | p.breaker);
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
        return STATUS_PROVED;
    }
    if (a.breaker_first_fix) {
        stats.breaker_first_leaves++;
        return STATUS_PROVED;
    }
    Bitboard candidates = a.unsafe_cells;
    if (options.dominance) {
        candidates = undominated_moves(&h, p, candidates, options.rules == RULES_STRONG);
    }
    order_moves(candidates, a.weight, double_threat_cells(&h), moves);
    return STATUS_OPEN;
}

static Status evaluate(Position p, bool maker_to_move, MoveList* moves)
{
    stats.evaluations++;
    moves->count = 0;
    if (!(board.all_cells & ~(p.maker | p.breaker))) {
        return STATUS_PROVED;   /* board full, no Maker line */
    }
    return maker_to_move ? evaluate_maker_to_move(p, moves) : evaluate_breaker_to_move(p, moves);
}

static Position child_state(Position p, bool maker_to_move, int cell)
{
    if (maker_to_move) {
        p.maker |= cell_bit(cell);
    } else {
        p.breaker |= cell_bit(cell);
    }
    return canonical_state(p);
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

static inline bool pn_solved(ProofNumbers v)
{
    return v.proof == 0 || v.disproof == 0;
}

typedef struct {
    Bitboard     maker;
    Bitboard     breaker;
    ProofNumbers value;
    uint32_t     work;      /* subtree effort, used for replacement            */
    uint8_t      turn;      /* 0 = empty, 1 = Breaker to move, 2 = Maker to move */
} TTEntry;

enum { TT_BUCKET = 4 };

static TTEntry* tt_table = NULL;
static size_t   tt_mask = 0;

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

static inline TTEntry* tt_bucket(Position p, uint8_t turn)
{
    uint64_t h = (p.maker * 0x9E3779B97F4A7C15ull) ^ (p.breaker * 0xC2B2AE3D27D4EB4Full) ^ turn;
    h ^= h >> 29;
    return &tt_table[(size_t)h & tt_mask & ~(size_t)(TT_BUCKET - 1)];
}

static inline uint8_t turn_code(bool maker_to_move)
{
    return maker_to_move ? 2 : 1;
}

static bool tt_lookup(Position p, bool maker_to_move, ProofNumbers* out)
{
    const uint8_t turn = turn_code(maker_to_move);
    const TTEntry* bucket = tt_bucket(p, turn);
    for (int i = 0; i < TT_BUCKET; i++) {
        const TTEntry* e = &bucket[i];
        if (e->turn == turn && e->maker == p.maker && e->breaker == p.breaker) {
            *out = e->value;
            return true;
        }
    }
    return false;
}

static void tt_store(Position p, bool maker_to_move, ProofNumbers value, uint64_t work)
{
    const uint8_t turn = turn_code(maker_to_move);
    TTEntry* bucket = tt_bucket(p, turn);
    TTEntry* slot = NULL;

    for (int i = 0; i < TT_BUCKET && !slot; i++) {
        TTEntry* e = &bucket[i];
        if (e->turn == turn && e->maker == p.maker && e->breaker == p.breaker) {
            slot = e;
        }
    }
    for (int i = 0; i < TT_BUCKET && !slot; i++) {
        if (bucket[i].turn == 0) {
            slot = &bucket[i];
        }
    }
    if (!slot) {
        slot = &bucket[0];
        for (int i = 1; i < TT_BUCKET; i++) {
            if (bucket[i].work < slot->work) {
                slot = &bucket[i];
            }
        }
        slot->work = 0;   /* evicting: do not inherit the old entry's effort */
        stats.tt_evictions++;
    }

    uint32_t effort = work > UINT32_MAX ? UINT32_MAX : (uint32_t)work;
    if (slot->turn == turn && slot->maker == p.maker && slot->breaker == p.breaker &&
        slot->work > effort) {
        effort = slot->work;
    }
    slot->maker = p.maker;
    slot->breaker = p.breaker;
    slot->value = value;
    slot->work = effort;
    slot->turn = turn;
}

/* =========================================================================================
 * Search bookkeeping
 * ========================================================================================= */

static void note_search_call(void)
{
    stats.search_calls++;
    if ((stats.search_calls & 4095) == 0 && options.time_limit > 0 &&
        elapsed_seconds() > options.time_limit) {
        search_aborted = true;
    }
    if (stats.search_calls % PROGRESS_INTERVAL == 0) {
        fprintf(stderr, "  [%7.1fs] search calls %llu, evaluations %llu\n", elapsed_seconds(),
                (unsigned long long)stats.search_calls, (unsigned long long)stats.evaluations);
    }
}

/* =========================================================================================
 * Engine 1: depth-first AND/OR search.  Returns true when P1 (Maker) wins.
 * ========================================================================================= */

static bool dfs_p1_wins(Position p, bool maker_to_move)
{
    note_search_call();
    if (search_aborted) {
        return false;
    }

    ProofNumbers known;
    if (tt_lookup(p, maker_to_move, &known) && pn_solved(known)) {
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
        for (int i = 0; i < moves.count && !p1_wins && !search_aborted; i++) {
            p1_wins = dfs_p1_wins(child_state(p, true, moves.cell[i]), false);
        }
    } else {
        p1_wins = true;
        for (int i = 0; i < moves.count && p1_wins && !search_aborted; i++) {
            p1_wins = dfs_p1_wins(child_state(p, false, moves.cell[i]), true);
        }
    }

    if (search_aborted) {
        return false;   /* incomplete: never store */
    }
    tt_store(p, maker_to_move, p1_wins ? PN_DISPROVED : PN_PROVED, stats.search_calls - calls_before);
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

/* Proof numbers of a canonical state, evaluating (and storing) it on a table miss. */
static ProofNumbers lookup_or_evaluate(Position p, bool maker_to_move)
{
    ProofNumbers value;
    if (tt_lookup(p, maker_to_move, &value)) {
        return value;
    }
    MoveList moves;
    const Status status = evaluate(p, maker_to_move, &moves);
    value = initial_numbers(status, maker_to_move, moves.count);
    tt_store(p, maker_to_move, value, 1);
    return value;
}

static void dfpn_mid(Position p, bool maker_to_move, uint32_t proof_threshold, uint32_t disproof_threshold)
{
    note_search_call();
    if (search_aborted) {
        return;
    }

    /* One evaluation per call: the table decides whether to stop, the evaluation supplies the
       move list (a table miss here means the root, or an entry evicted since the parent's
       look-up). */
    ProofNumbers value;
    if (tt_lookup(p, maker_to_move, &value) &&
        (pn_solved(value) || value.proof >= proof_threshold || value.disproof >= disproof_threshold)) {
        return;
    }
    MoveList moves;
    const Status status = evaluate(p, maker_to_move, &moves);
    if (status != STATUS_OPEN) {
        tt_store(p, maker_to_move, initial_numbers(status, maker_to_move, 0), 1);
        return;
    }
    Position child[MAX_CELLS];
    for (int i = 0; i < moves.count; i++) {
        child[i] = child_state(p, maker_to_move, moves.cell[i]);
    }

    const uint64_t calls_before = stats.search_calls;
    for (;;) {
        uint32_t proof, disproof;
        uint32_t best = PN_INFINITY;
        uint32_t second = PN_INFINITY;
        int      best_index = -1;
        ProofNumbers best_value = { 0, 0 };

        if (maker_to_move) {   /* AND: proof = sum, disproof = min */
            proof = 0;
            disproof = PN_INFINITY;
            for (int i = 0; i < moves.count; i++) {
                const ProofNumbers c = lookup_or_evaluate(child[i], false);
                proof = pn_add(proof, c.proof);
                disproof = pn_min(disproof, c.disproof);
                if (c.disproof < best) {
                    second = best;
                    best = c.disproof;
                    best_index = i;
                    best_value = c;
                } else if (c.disproof < second) {
                    second = c.disproof;
                }
                if (disproof == 0) {
                    break;
                }
            }
        } else {               /* OR: proof = min, disproof = sum */
            proof = PN_INFINITY;
            disproof = 0;
            for (int i = 0; i < moves.count; i++) {
                const ProofNumbers c = lookup_or_evaluate(child[i], true);
                proof = pn_min(proof, c.proof);
                disproof = pn_add(disproof, c.disproof);
                if (c.proof < best) {
                    second = best;
                    best = c.proof;
                    best_index = i;
                    best_value = c;
                } else if (c.proof < second) {
                    second = c.proof;
                }
                if (proof == 0) {
                    break;
                }
            }
        }

        value.proof = proof;
        value.disproof = disproof;
        tt_store(p, maker_to_move, value, stats.search_calls - calls_before + 1);
        if (pn_solved(value) || proof >= proof_threshold || disproof >= disproof_threshold ||
            best_index < 0) {
            return;
        }

        uint32_t child_proof_threshold, child_disproof_threshold;
        if (maker_to_move) {
            child_disproof_threshold = pn_min(disproof_threshold, pn_second_threshold(second));
            child_proof_threshold = pn_child_threshold(proof_threshold, proof, best_value.proof);
        } else {
            child_proof_threshold = pn_min(proof_threshold, pn_second_threshold(second));
            child_disproof_threshold = pn_child_threshold(disproof_threshold, disproof, best_value.disproof);
        }
        dfpn_mid(child[best_index], !maker_to_move, child_proof_threshold, child_disproof_threshold);
        if (search_aborted) {
            return;
        }
    }
}

/* Returns 1 if P1 wins, 0 if P1 cannot win, -1 if unresolved. */
static int dfpn_solve(Position root)
{
    ProofNumbers value = { 1, 1 };
    while (!search_aborted) {
        dfpn_mid(root, true, PN_INFINITY, PN_INFINITY);
        if (!tt_lookup(root, true, &value)) {
            return -1;   /* root entry evicted; should not happen */
        }
        if (pn_solved(value)) {
            return value.disproof == 0 ? 1 : 0;
        }
    }
    return -1;
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
}

static void print_usage(const char* program)
{
    fprintf(stderr,
            "usage: %s m n k [MB|SG] [flags] [tt_log2] [DFS|DFPN] [time_limit_seconds]\n"
            "  flags: 1 components, 2 2-matching, 4 subsumption, 8 restrict Maker,\n"
            "         16 double-threat stop, 32 greedy hybrid, 64 dominance,\n"
            "         128 reduced MB state, 256 exact pair cover, 512 twin pairs\n"
            "         (default 1023 = all)\n",
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
    options_from_flags(argc > 5 ? atoi(argv[5]) : 1023);
    options.tt_log2 = argc > 6 ? atoi(argv[6]) : 24;
    options.engine = (argc > 7 && strcmp(argv[7], "DFS") == 0) ? ENGINE_DFS : ENGINE_DFPN;
    options.time_limit = argc > 8 ? atof(argv[8]) : 0.0;

    if (options.rules == RULES_STRONG) {
        /* Unsound with P2 lines in play (see the header). Breaker dominance stays allowed. */
        options.restrict_maker = false;
        options.reduced_state = false;
    }
    if (!board_init(rows, cols, k) || !tt_allocate(options.tt_log2)) {
        return 1;
    }
    if (!component_cache_allocate()) {
        tt_free();
        return 1;
    }

    start_time = wall_seconds();
    const Position root = canonical_state((Position){ 0, 0 });
    int result;
    if (options.engine == ENGINE_DFS) {
        const bool p1_wins = dfs_p1_wins(root, true);
        result = search_aborted ? -1 : (p1_wins ? 1 : 0);
    } else {
        result = dfpn_solve(root);
    }
    const double seconds = elapsed_seconds();

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
           options.engine == ENGINE_DFS ? "DFS" : "DFPN", verdict);
    printf("  search calls %llu, evaluations %llu, time %.2f s\n",
           (unsigned long long)stats.search_calls, (unsigned long long)stats.evaluations, seconds);
    printf("  safe components: ES %llu, 2-matching %llu, cover %llu, cover+ES %llu, greedy hybrid %llu"
           " (cover budget exhausted %llu)\n",
           (unsigned long long)stats.safe_by_es, (unsigned long long)stats.safe_by_matching,
           (unsigned long long)stats.safe_by_cover, (unsigned long long)stats.safe_by_cover_es,
           (unsigned long long)stats.safe_by_greedy_hybrid, (unsigned long long)stats.cover_budget_exhausted);
    for (int hot = board.k; hot >= 2 && options.pair_cover; hot--) {
        printf("  cover, lines of size <= %d: %llu attempts, %llu refuted at once, %llu exhausted, %llu covers found, %llu safe\n",
               hot, (unsigned long long)stats.cover_attempts[hot], (unsigned long long)stats.cover_refuted[hot],
               (unsigned long long)stats.cover_exhausted[hot],
               (unsigned long long)stats.cover_found[hot], (unsigned long long)stats.cover_safe[hot]);
    }
    printf("  twin pairs removed %llu (components emptied %llu), unsafe by double threat %llu\n",
           (unsigned long long)stats.twin_pairs, (unsigned long long)stats.safe_by_twins,
           (unsigned long long)stats.unsafe_by_double_threat);
    printf("  Breaker-first leaves %llu, Maker wins detected %llu, dominated moves skipped %llu\n",
           (unsigned long long)stats.breaker_first_leaves, (unsigned long long)stats.maker_wins_detected,
           (unsigned long long)stats.dominated_moves);
    printf("  component cache: %llu hits, %llu misses\n", (unsigned long long)stats.component_cache_hits,
           (unsigned long long)stats.component_cache_misses);
    printf("  transposition table: 2^%d entries, %llu evictions\n", options.tt_log2,
           (unsigned long long)stats.tt_evictions);
    if (result < 0 && options.engine == ENGINE_DFPN && stats.tt_evictions > tt_mask) {
        /* df-pn can cycle when evicted nodes come back with fresh (smaller) proof numbers. */
        printf("  warning: heavy eviction; df-pn may be cycling - try a larger tt_log2\n");
    }

    component_cache_free();
    tt_free();
    return 0;
}
