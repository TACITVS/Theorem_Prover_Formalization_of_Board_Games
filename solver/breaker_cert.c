/*
 * breaker_cert.c: Breaker-strategy certificates for Maker-Breaker (m, n, k) games, checked in Rocq
 *
 * For each job on the command line, the program proves that Breaker stops Maker (Player 1,
 * moving first): within a given number of Maker moves (a lower bound on how fast Maker can
 * win), or for ever (a Breaker win, hence a draw of the strong game).  The strategy is written
 * as a term of type `brcert` (MNKBreakerCert.v); the Rocq checker `check_br` accepts it, and
 * its soundness theorem turns that into `~ maker_wins`.
 *
 * ------------------------------------------------------------------------------------------
 * Certificate shape (must match check_br)
 * ------------------------------------------------------------------------------------------
 *
 *   At every certificate position Maker is to move.
 *
 *   BrNode moves    For every free cell m whose Maker move leaves a free cell, `moves` holds
 *                   one entry BmCons m c sub: Breaker replies c and continues with `sub`.
 *                   No Maker move may complete a line.
 *   BrShort         Every line carries a Breaker stone or lacks more Maker stones than Maker
 *                   has moves left (bounded jobs only).
 *   BrES            Erdos-Selfridge with K = k: for every free cell x,
 *                   phi + wgt(x) < 2^k, where an open line (no Breaker stone) with s Maker
 *                   stones weighs 2^s, phi sums all open lines and wgt(x) the open lines
 *                   through x.
 *   BrPair pairs    Disjoint pairs of free cells such that every open line contains a whole
 *                   pair; Breaker answers each move in its partner cell.
 *
 * ------------------------------------------------------------------------------------------
 * Search
 * ------------------------------------------------------------------------------------------
 *
 *   1. Does Breaker hold?  Depth-first proof-number search (df-pn): AND over Maker moves, OR
 *      over Breaker replies, with one table entry per node keyed by the canonical form under
 *      the board's symmetries.  When Maker threatens to complete a line, only the block is
 *      tried; replies on cells that lie on no open line are never tried (such a reply is a
 *      pass, never better than another reply).  The table is never pruned, so once the root
 *      is proved the whole proof is in it.
 *   2. The smallest certificate: at every node and for every Maker move, the proved reply
 *      whose sub-certificate has the fewest positions (exact over the proved nodes,
 *      memoised per canonical position and bound).
 *   3. The certificate is written in real board coordinates.  Leaf rules are recomputed on
 *      the real position, so the canonical table never leaks into the output.
 *
 *   Cells are numbered r * n + c, as in MNKBoard.v.
 *
 * ------------------------------------------------------------------------------------------
 * Build and usage
 * ------------------------------------------------------------------------------------------
 *
 *   clang -std=c11 -O3 -march=native -o breaker_cert.exe breaker_cert.c
 *
 *   breaker_cert output.v m n k bound [m n k bound ...]
 *
 *   bound is a number d (Maker cannot win within d moves) or "draw" (Maker never wins).
 */

#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t Bitboard;

enum {
    MAX_CELLS        = 64,
    MAX_LINES        = 1024,
    MAX_SYMMETRIES   = 8,
    UNBOUNDED        = 127,            /* the bound of a "draw" job                       */
    TABLE_LOG2       = 20,             /* initial table size; tables double when needed   */
    TABLE_LOG2_LIMIT = 27,             /* give up beyond 2^27 search nodes (4 GB)         */
    PAIRING_BUDGET   = 20000,          /* search steps allowed per pairing attempt        */
};

static const uint32_t SIZE_INFINITE = UINT32_MAX;

static inline Bitboard cell_bit(int cell)
{
    return (Bitboard)1 << cell;
}

static inline int popcount(Bitboard b)
{
    return __builtin_popcountll(b);
}

static inline int lowest_cell(Bitboard b)
{
    return __builtin_ctzll(b);
}

static inline int next_bound(int bound)
{
    return bound == UNBOUNDED ? UNBOUNDED : bound - 1;
}

/* =========================================================================================
 * Board geometry
 * ========================================================================================= */

typedef struct {
    int      rows;
    int      cols;
    int      k;
    int      cells;
    Bitboard all_cells;
    int      line_count;
    Bitboard line[MAX_LINES];
    int      symmetry_count;
    int      image[MAX_SYMMETRIES][MAX_CELLS];
    int      preimage[MAX_SYMMETRIES][MAX_CELLS];
} Board;

static Board board;

static void add_line(int r, int c, int dr, int dc)
{
    Bitboard line = 0;
    for (int i = 0; i < board.k; i++) {
        line |= cell_bit((r + i * dr) * board.cols + (c + i * dc));
    }
    if (board.line_count == MAX_LINES) {
        fprintf(stderr, "too many lines\n");
        exit(1);
    }
    board.line[board.line_count++] = line;
}

/* Lines of gen_lines m n k: horizontal, vertical, diagonal, anti-diagonal. */
static void board_init(int rows, int cols, int k)
{
    memset(&board, 0, sizeof board);
    board.rows = rows;
    board.cols = cols;
    board.k = k;
    board.cells = rows * cols;
    board.all_cells = board.cells == 64 ? ~(Bitboard)0 : cell_bit(board.cells) - 1;

    for (int r = 0; r < rows; r++) {
        for (int c = 0; c + k <= cols; c++) {
            add_line(r, c, 0, 1);
        }
    }
    for (int r = 0; r + k <= rows; r++) {
        for (int c = 0; c < cols; c++) {
            add_line(r, c, 1, 0);
        }
    }
    for (int r = 0; r + k <= rows; r++) {
        for (int c = 0; c + k <= cols; c++) {
            add_line(r, c, 1, 1);
            add_line(r, c + k - 1, 1, -1);
        }
    }

    /* Symmetries: the four reflections of a rectangle, eight for a square. */
    const int last_r = rows - 1;
    const int last_c = cols - 1;
    const int count = rows == cols ? 8 : 4;
    for (int t = 0; t < count; t++) {
        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                int nr = r;
                int nc = c;
                switch (t) {
                case 0: nr = r;          nc = c;          break;
                case 1: nr = r;          nc = last_c - c; break;
                case 2: nr = last_r - r; nc = c;          break;
                case 3: nr = last_r - r; nc = last_c - c; break;
                case 4: nr = c;          nc = r;          break;
                case 5: nr = c;          nc = last_r - r; break;
                case 6: nr = last_c - c; nc = r;          break;
                default: nr = last_c - c; nc = last_r - r; break;
                }
                board.image[t][r * cols + c] = nr * cols + nc;
                board.preimage[t][nr * cols + nc] = r * cols + c;
            }
        }
    }
    board.symmetry_count = count;
}

static Bitboard apply_symmetry(int t, Bitboard set)
{
    Bitboard out = 0;
    while (set) {
        const int cell = lowest_cell(set);
        set &= set - 1;
        out |= cell_bit(board.image[t][cell]);
    }
    return out;
}

typedef struct {
    Bitboard maker;
    Bitboard breaker;
} Position;

/* The canonical form of `p` under the board's symmetries, and the symmetry reaching it. */
static Position canonical_with(Position p, int* symmetry)
{
    Position best = p;
    *symmetry = 0;
    for (int t = 1; t < board.symmetry_count; t++) {
        const Position q = { apply_symmetry(t, p.maker), apply_symmetry(t, p.breaker) };
        if (q.maker < best.maker || (q.maker == best.maker && q.breaker < best.breaker)) {
            best = q;
            *symmetry = t;
        }
    }
    return best;
}

static Position canonical(Position p)
{
    int symmetry;
    return canonical_with(p, &symmetry);
}

static inline Bitboard free_cells(Position p)
{
    return board.all_cells & ~(p.maker | p.breaker);
}

/* Cells that complete a line for Maker: open lines missing exactly one cell. */
static Bitboard winning_cells(Position p)
{
    Bitboard cells = 0;
    for (int i = 0; i < board.line_count; i++) {
        const Bitboard line = board.line[i];
        if ((line & p.breaker) == 0) {
            const Bitboard missing = line & ~p.maker;
            if (popcount(missing) == 1) {
                cells |= missing;
            }
        }
    }
    return cells;
}

/*
 * Maker, to move, has a double threat: a cell on two open lines that both miss exactly two
 * cells, with different second cells.  Playing it leaves two winning cells, so Maker wins
 * within two moves.
 */
static bool has_double_threat(Position p)
{
    Bitboard seen = 0;              /* cells on some open line missing two cells         */
    Bitboard partner[MAX_CELLS];    /* for c in seen: the other missing cell of one line */
    for (int i = 0; i < board.line_count; i++) {
        const Bitboard line = board.line[i];
        if ((line & p.breaker) != 0) {
            continue;
        }
        const Bitboard missing = line & ~p.maker;
        if (popcount(missing) != 2) {
            continue;
        }
        for (Bitboard f = missing; f; f &= f - 1) {
            const int c = lowest_cell(f);
            const Bitboard other = missing & ~cell_bit(c);
            if (seen & cell_bit(c)) {
                if (partner[c] != other) {
                    return true;
                }
            } else {
                seen |= cell_bit(c);
                partner[c] = other;
            }
        }
    }
    return false;
}

typedef struct {
    int count;
    int cell[MAX_CELLS];
} MoveList;

/*
 * The cells of `candidates`, most valuable first: a cell scores the sum over the open lines
 * through it of base^(Maker stones on the line), with base = 2^shift.  shift = 1 gives the
 * Erdos-Selfridge weights (Breaker's greedy reply comes first); shift = 3 stresses the lines
 * nearest completion (Maker's likeliest refutations).  Ties keep cell order.
 */
static void order_cells(Position p, Bitboard candidates, int shift, MoveList* moves)
{
    int score[MAX_CELLS] = { 0 };
    for (int i = 0; i < board.line_count; i++) {
        const Bitboard line = board.line[i];
        if ((line & p.breaker) == 0) {
            const int weight = 1 << (shift * popcount(line & p.maker));
            Bitboard open = line & ~p.maker;
            while (open) {
                const int cell = lowest_cell(open);
                open &= open - 1;
                score[cell] += weight;
            }
        }
    }
    moves->count = 0;
    while (candidates) {
        const int cell = lowest_cell(candidates);
        candidates &= candidates - 1;
        int i = moves->count++;
        while (i > 0 && score[moves->cell[i - 1]] < score[cell]) {
            moves->cell[i] = moves->cell[i - 1];
            i--;
        }
        moves->cell[i] = cell;
    }
}

/* =========================================================================================
 * Leaf rules (mirroring short_ok, es_ok and pairing_ok in MNKBreakerCert.v)
 * ========================================================================================= */

typedef enum {
    LEAF_NONE,
    LEAF_SHORT,
    LEAF_ES,
    LEAF_PAIR,
} LeafKind;

typedef struct {
    int      count;
    int      first[MAX_CELLS / 2];
    int      second[MAX_CELLS / 2];
    Bitboard cells[MAX_CELLS / 2];
} Pairing;

/* Every line is blocked or lacks more than `bound` Maker stones. */
static bool short_leaf(Position p, int bound)
{
    for (int i = 0; i < board.line_count; i++) {
        const Bitboard line = board.line[i];
        if ((line & p.breaker) == 0 && board.k - popcount(line & p.maker) <= bound) {
            return false;
        }
    }
    return true;
}

/* phi + wgt(x) < 2^k for every free cell x. */
static bool es_leaf(Position p)
{
    uint64_t weight[MAX_CELLS] = { 0 };
    uint64_t phi = 0;
    for (int i = 0; i < board.line_count; i++) {
        const Bitboard line = board.line[i];
        if ((line & p.breaker) == 0) {
            const uint64_t w = (uint64_t)1 << popcount(line & p.maker);
            phi += w;
            Bitboard cells = line;
            while (cells) {
                const int cell = lowest_cell(cells);
                cells &= cells - 1;
                weight[cell] += w;
            }
        }
    }
    const uint64_t limit = (uint64_t)1 << board.k;
    Bitboard free = free_cells(p);
    while (free) {
        const int cell = lowest_cell(free);
        free &= free - 1;
        if (phi + weight[cell] >= limit) {
            return false;
        }
    }
    return true;
}

static void pairing_push(Pairing* pairing, int x, int y)
{
    const int slot = pairing->count++;
    pairing->first[slot] = x;
    pairing->second[slot] = y;
    pairing->cells[slot] = cell_bit(x) | cell_bit(y);
}

/*
 * 2-matching (Kuhn's augmenting paths): every line gets two private cells, and those two cells
 * form its pair.  Slots 2i and 2i+1 belong to line i; owner[c] is valid for c in `owned`.
 */
typedef struct {
    const Bitboard* lines;
    int             owner[MAX_CELLS];
    Bitboard        owned;
    Bitboard        visited;
} Matching;

static bool matching_augment(Matching* m, int slot)
{
    const Bitboard line = m->lines[slot / 2];
    const Bitboard unowned = line & ~m->owned;
    if (unowned) {
        const int c = lowest_cell(unowned);
        m->owner[c] = slot;
        m->owned |= cell_bit(c);
        return true;
    }
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

static bool two_matching(const Bitboard* lines, int count, Pairing* pairing)
{
    Bitboard cells = 0;
    for (int i = 0; i < count; i++) {
        cells |= lines[i];
    }
    if (2 * count > popcount(cells)) {
        return false;
    }
    Matching m;
    m.lines = lines;
    m.owned = 0;
    for (int slot = 0; slot < 2 * count; slot++) {
        m.visited = 0;
        if (!matching_augment(&m, slot)) {
            return false;
        }
    }
    if (pairing != NULL) {
        int first[MAX_LINES];
        for (Bitboard f = m.owned; f; f &= f - 1) {
            const int c = lowest_cell(f);
            if (m.owner[c] % 2 == 0) {
                first[m.owner[c] / 2] = c;
            }
        }
        pairing->count = 0;
        for (Bitboard f = m.owned; f; f &= f - 1) {
            const int c = lowest_cell(f);
            if (m.owner[c] % 2 == 1) {
                pairing_push(pairing, first[m.owner[c] / 2], c);
            }
        }
    }
    return true;
}

/*
 * Necessary condition for a cover: open lines sharing at most one cell pairwise need distinct,
 * hence disjoint, pairs, so such a family (chosen greedily, shortest lines first) must have a
 * 2-matching.
 */
static bool cover_may_exist(const Bitboard* open, int count)
{
    Bitboard family[MAX_LINES];
    int m = 0;
    for (int size = 2; size <= board.k; size++) {
        for (int i = 0; i < count; i++) {
            if (popcount(open[i]) != size) {
                continue;
            }
            bool independent = true;
            for (int j = 0; j < m && independent; j++) {
                const Bitboard shared = open[i] & family[j];
                independent = (shared & (shared - 1)) == 0;
            }
            if (independent) {
                family[m++] = open[i];
            }
        }
    }
    return two_matching(family, m, NULL);
}

enum { COVER_BRANCH_LIMIT = 2, MAX_LINE_PAIRS = 64 };

/*
 * Exact shared-pair cover by backtracking, after the prover (Hsu et al.'s pair score
 * 4c - deg(u) - deg(v), two candidates per level).  `open` holds the lines still lacking a
 * pair, each reduced to its unused free cells.
 */
static bool cover_recurse(const Bitboard* open, int count, Pairing* pairing, long* budget)
{
    if (count == 0) {
        return true;
    }
    if (--*budget < 0) {
        return false;
    }
    for (int i = 0; i < count; i++) {
        if (popcount(open[i]) < 2) {
            return false;
        }
    }
    if (!cover_may_exist(open, count)) {
        return false;
    }

    int best = 0;
    for (int i = 1; i < count; i++) {
        if (popcount(open[i]) < popcount(open[best])) {
            best = i;
        }
    }
    int degree[MAX_CELLS];
    for (Bitboard a = open[best]; a; a &= a - 1) {
        const int u = lowest_cell(a);
        degree[u] = 0;
        for (int i = 0; i < count; i++) {
            degree[u] += (int)((open[i] >> u) & 1);
        }
    }

    int cand_u[MAX_LINE_PAIRS];
    int cand_v[MAX_LINE_PAIRS];
    int cand_score[MAX_LINE_PAIRS];
    int cand_count = 0;
    for (Bitboard a = open[best]; a; a &= a - 1) {
        const int u = lowest_cell(a);
        for (Bitboard b = a & (a - 1); b; b &= b - 1) {
            const int v = lowest_cell(b);
            if (cand_count == MAX_LINE_PAIRS) {
                break;
            }
            const Bitboard pair = cell_bit(u) | cell_bit(v);
            int covered = 0;
            for (int i = 0; i < count; i++) {
                covered += (open[i] & pair) == pair;
            }
            const int score = 4 * covered - degree[u] - degree[v];
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

    const int tries = cand_count < COVER_BRANCH_LIMIT ? cand_count : COVER_BRANCH_LIMIT;
    for (int q = 0; q < tries; q++) {
        const Bitboard pair = cell_bit(cand_u[q]) | cell_bit(cand_v[q]);
        Bitboard child[MAX_LINES];
        int child_count = 0;
        for (int i = 0; i < count; i++) {
            if ((open[i] & pair) != pair) {
                child[child_count++] = open[i] & ~pair;
            }
        }
        pairing_push(pairing, cand_u[q], cand_v[q]);
        if (cover_recurse(child, child_count, pairing, budget)) {
            return true;
        }
        pairing->count--;
        if (*budget < 0) {
            return false;
        }
    }
    return false;
}

/* Disjoint pairs of free cells such that every open line contains a whole pair. */
static bool pairing_search(Position p, Pairing* pairing)
{
    Bitboard open[MAX_LINES];
    int count = 0;
    const Bitboard free = free_cells(p);
    for (int i = 0; i < board.line_count; i++) {
        if ((board.line[i] & p.breaker) == 0) {
            open[count++] = board.line[i] & free;
        }
    }
    if (two_matching(open, count, pairing)) {
        return true;
    }
    pairing->count = 0;
    long budget = PAIRING_BUDGET;
    return cover_recurse(open, count, pairing, &budget);
}

/*
 * The pairing search runs on the canonical form and its pairs are mapped back, so symmetric
 * positions (which share one table entry) always get the same answer.
 */
static bool pairing_leaf(Position p, Pairing* pairing)
{
    int symmetry;
    const Position q = canonical_with(p, &symmetry);
    if (!pairing_search(q, pairing)) {
        return false;
    }
    for (int i = 0; i < pairing->count; i++) {
        pairing->first[i] = board.preimage[symmetry][pairing->first[i]];
        pairing->second[i] = board.preimage[symmetry][pairing->second[i]];
        pairing->cells[i] = cell_bit(pairing->first[i]) | cell_bit(pairing->second[i]);
    }
    return true;
}

/* The cheapest leaf rule that settles `p` (cheapest to check in Rocq first). */
static LeafKind classify(Position p, int bound, Pairing* pairing)
{
    if (bound != UNBOUNDED && short_leaf(p, bound)) {
        return LEAF_SHORT;
    }
    if (es_leaf(p)) {
        return LEAF_ES;
    }
    Pairing scratch;
    if (pairing_leaf(p, pairing != NULL ? pairing : &scratch)) {
        return LEAF_PAIR;
    }
    return LEAF_NONE;
}

/* =========================================================================================
 * Hash tables (canonical keys, in RAM, grown on demand)
 *
 * Both tables use open addressing and double in size at 3/4 load.  A pointer into a table is
 * invalidated by the next insertion, so callers look an entry up again after any recursion.
 * ========================================================================================= */

typedef enum {
    TURN_NONE    = 0,                   /* marks an empty table slot                         */
    TURN_MAKER   = 1,                   /* Maker to move: an AND node                        */
    TURN_BREAKER = 2,                   /* Breaker to reply: an OR node                      */
} Turn;

typedef struct {
    uint32_t proof;                     /* cost estimate of proving that Breaker holds       */
    uint32_t disproof;                  /* cost estimate of proving that Maker gets through */
} Numbers;

typedef struct {
    Bitboard maker;
    Bitboard breaker;
    Numbers  value;
    int8_t   bound;                     /* Maker moves left                                  */
    uint8_t  turn;                      /* a Turn                                            */
} NodeEntry;

typedef struct {
    Bitboard maker;
    Bitboard breaker;
    uint32_t size;                      /* fewest certificate positions                      */
    int8_t   bound;
    bool     used;
} SizeEntry;

typedef struct {
    NodeEntry* slot;
    size_t     mask;
    size_t     used;
} NodeTable;

typedef struct {
    SizeEntry* slot;
    size_t     mask;
    size_t     used;
} SizeTable;

static NodeTable nodes;
static SizeTable sizes;
static uint64_t  search_calls;

static inline size_t hash_key(Position key, int bound)
{
    uint64_t hash = key.maker * 0x9E3779B97F4A7C15ull ^ key.breaker * 0xC2B2AE3D27D4EB4Full;
    hash ^= (uint64_t)bound * 0x165667B19E3779F9ull;
    hash ^= hash >> 29;
    return (size_t)hash;
}

static void* allocate_slots(size_t count, size_t size)
{
    void* slots = calloc(count, size);
    if (slots == NULL) {
        fprintf(stderr, "out of memory (%zu table slots of %zu bytes)\n", count, size);
        exit(1);
    }
    return slots;
}

static void nodes_reset(void)
{
    free(nodes.slot);
    nodes.mask = ((size_t)1 << TABLE_LOG2) - 1;
    nodes.slot = allocate_slots(nodes.mask + 1, sizeof *nodes.slot);
    nodes.used = 0;
}

static void size_table_init(SizeTable* table)
{
    table->mask = ((size_t)1 << TABLE_LOG2) - 1;
    table->slot = allocate_slots(table->mask + 1, sizeof *table->slot);
    table->used = 0;
}

static void sizes_reset(void)
{
    free(sizes.slot);
    size_table_init(&sizes);
}

static inline size_t node_hash(Position key, int bound, Turn turn)
{
    return hash_key(key, 2 * bound + (int)turn);
}

static NodeEntry* nodes_find(Position key, int bound, Turn turn)
{
    size_t index = node_hash(key, bound, turn) & nodes.mask;
    while (nodes.slot[index].turn != TURN_NONE) {
        NodeEntry* entry = &nodes.slot[index];
        if (entry->maker == key.maker && entry->breaker == key.breaker && entry->bound == bound
            && entry->turn == (uint8_t)turn) {
            return entry;
        }
        index = (index + 1) & nodes.mask;
    }
    return NULL;
}

static void nodes_grow(void)
{
    if (nodes.mask + 1 >= ((size_t)1 << TABLE_LOG2_LIMIT)) {
        fprintf(stderr, "node table reached 2^%d entries: giving up\n", TABLE_LOG2_LIMIT);
        exit(1);
    }
    const NodeTable old = nodes;
    nodes.mask = 2 * old.mask + 1;
    nodes.slot = allocate_slots(nodes.mask + 1, sizeof *nodes.slot);
    for (size_t i = 0; i <= old.mask; i++) {
        const NodeEntry* entry = &old.slot[i];
        if (entry->turn != TURN_NONE) {
            const Position key = { entry->maker, entry->breaker };
            size_t index = node_hash(key, entry->bound, (Turn)entry->turn) & nodes.mask;
            while (nodes.slot[index].turn != TURN_NONE) {
                index = (index + 1) & nodes.mask;
            }
            nodes.slot[index] = *entry;
        }
    }
    free(old.slot);
}

/* Stores the numbers of a node, creating its entry if absent. */
static void nodes_store(Position key, int bound, Turn turn, Numbers value)
{
    NodeEntry* entry = nodes_find(key, bound, turn);
    if (entry == NULL) {
        if ((nodes.used + 1) * 4 > (nodes.mask + 1) * 3) {
            nodes_grow();
        }
        size_t index = node_hash(key, bound, turn) & nodes.mask;
        while (nodes.slot[index].turn != TURN_NONE) {
            index = (index + 1) & nodes.mask;
        }
        nodes.used++;
        entry = &nodes.slot[index];
        entry->maker = key.maker;
        entry->breaker = key.breaker;
        entry->bound = (int8_t)bound;
        entry->turn = (uint8_t)turn;
    }
    entry->value = value;
}

static const SizeEntry* sizes_find(Position key, int bound)
{
    size_t index = hash_key(key, bound) & sizes.mask;
    while (sizes.slot[index].used) {
        const SizeEntry* entry = &sizes.slot[index];
        if (entry->maker == key.maker && entry->breaker == key.breaker && entry->bound == bound) {
            return entry;
        }
        index = (index + 1) & sizes.mask;
    }
    return NULL;
}

static void size_table_grow(SizeTable* table)
{
    const SizeTable old = *table;
    table->mask = 2 * old.mask + 1;
    table->slot = allocate_slots(table->mask + 1, sizeof *table->slot);
    for (size_t i = 0; i <= old.mask; i++) {
        if (old.slot[i].used) {
            const Position key = { old.slot[i].maker, old.slot[i].breaker };
            size_t index = hash_key(key, old.slot[i].bound) & table->mask;
            while (table->slot[index].used) {
                index = (index + 1) & table->mask;
            }
            table->slot[index] = old.slot[i];
        }
    }
    free(old.slot);
}

static void sizes_store(Position key, int bound, uint32_t size)
{
    if ((sizes.used + 1) * 4 > (sizes.mask + 1) * 3) {
        size_table_grow(&sizes);
    }
    size_t index = hash_key(key, bound) & sizes.mask;
    while (sizes.slot[index].used) {
        index = (index + 1) & sizes.mask;
    }
    sizes.used++;
    SizeEntry* entry = &sizes.slot[index];
    entry->used = true;
    entry->maker = key.maker;
    entry->breaker = key.breaker;
    entry->bound = (int8_t)bound;
    entry->size = size;
}

/* =========================================================================================
 * Phase 1: does Breaker hold Maker for `bound` more moves?  (df-pn)
 *
 * "Proved" means that Breaker holds.  A Maker node (Maker to move, `bound` Maker moves left)
 * is an AND node over Maker's moves; a Breaker node (Maker has just moved, `bound` Maker moves
 * left after that move) is an OR node over Breaker's replies.  A node is evaluated once, when
 * first met, and its numbers are kept in the node table, which is never pruned.
 * ========================================================================================= */

#define PN_INFINITY 0x3FFFFFFFu

static const Numbers PN_PROVED    = { 0, PN_INFINITY };
static const Numbers PN_DISPROVED = { PN_INFINITY, 0 };

/* Sum of two numbers, each at most PN_INFINITY; an unsolved sum stays below PN_INFINITY. */
static inline uint32_t pn_add(uint32_t a, uint32_t b)
{
    const uint32_t sum = a + b;
    return sum >= PN_INFINITY ? PN_INFINITY - 1 : sum;
}

/* Free cells on open lines (lines without a Breaker stone). */
static Bitboard live_cells(Position p)
{
    Bitboard live = 0;
    for (int i = 0; i < board.line_count; i++) {
        if ((board.line[i] & p.breaker) == 0) {
            live |= board.line[i];
        }
    }
    return live & free_cells(p);
}

/*
 * Breaker's candidate replies after Maker's move, best (Erdos-Selfridge greedy) first.  When
 * Maker still has a move and threatens to complete a line, only the block can hold; against
 * two threats nothing can.  A cell on no open line is tried only when no other cell is free.
 */
static void breaker_replies(Position after, int bound, MoveList* replies)
{
    replies->count = 0;
    const Bitboard threats = bound > 0 ? winning_cells(after) : 0;
    if (popcount(threats) >= 2) {
        return;
    }
    if (threats) {
        replies->count = 1;
        replies->cell[0] = lowest_cell(threats);
        return;
    }
    const Bitboard live = live_cells(after);
    if (live != 0) {
        order_cells(after, live, 1, replies);
    } else if (free_cells(after) != 0) {
        replies->count = 1;
        replies->cell[0] = lowest_cell(free_cells(after));
    }
}

/* The moves of a node, best first: Maker's moves, or Breaker's replies. */
static void node_moves(Position p, Turn turn, int bound, MoveList* moves)
{
    if (turn == TURN_MAKER) {
        order_cells(p, free_cells(p), 3, moves);
    } else {
        breaker_replies(p, bound, moves);
    }
}

static inline Position child_of(Position p, Turn turn, int cell)
{
    if (turn == TURN_MAKER) {
        return (Position){ p.maker | cell_bit(cell), p.breaker };
    }
    return (Position){ p.maker, p.breaker | cell_bit(cell) };
}

/*
 * Static evaluation, with mobility initialisation for open nodes.  A Maker node is proved
 * exactly when `bound` is 0 or a leaf rule applies (so the printed leaf always exists).
 */
static Numbers evaluate_node(Position p, Turn turn, int bound)
{
    MoveList moves;
    if (turn == TURN_MAKER) {
        if (bound == 0) {
            return PN_PROVED;
        }
        if (winning_cells(p) != 0 || (bound >= 2 && has_double_threat(p))) {
            return PN_DISPROVED;
        }
        if (classify(p, bound, NULL) != LEAF_NONE) {
            return PN_PROVED;
        }
        node_moves(p, turn, bound, &moves);
        return (Numbers){ (uint32_t)moves.count, 1 };
    }
    if (bound == 0 || free_cells(p) == 0) {
        return PN_PROVED;                      /* Maker has no move left, or the board is full */
    }
    node_moves(p, turn, bound, &moves);
    if (moves.count == 0) {
        return PN_DISPROVED;                   /* two threats */
    }
    return (Numbers){ 1, (uint32_t)moves.count };
}

/* The numbers of a node, evaluating and storing it when it is not in the table. */
static Numbers node_value(Position p, Turn turn, int bound)
{
    const Position key = canonical(p);
    const NodeEntry* entry = nodes_find(key, bound, turn);
    if (entry != NULL) {
        return entry->value;
    }
    const Numbers value = evaluate_node(p, turn, bound);
    nodes_store(key, bound, turn, value);
    return value;
}

static inline bool pn_solved(Numbers value)
{
    return value.proof == 0 || value.disproof == 0;
}

/* A child's threshold for the summed number: the parent's slack, plus the child's share. */
static inline uint32_t sum_threshold_of(uint32_t threshold, uint32_t sum, uint32_t child)
{
    return threshold >= PN_INFINITY ? PN_INFINITY : threshold - sum + child;
}

/*
 * Nagai's MID: search below `p` until its proof number reaches `proof_threshold` or its
 * disproof number reaches `disproof_threshold` (in particular, until it is solved).
 */
static void dfpn(Position p, Turn turn, int bound, uint32_t proof_threshold,
                 uint32_t disproof_threshold)
{
    search_calls++;
    if ((search_calls & ((1u << 22) - 1)) == 0) {
        fprintf(stderr, "  [df-pn] %" PRIu64 " calls, %zu nodes\n", search_calls, nodes.used);
    }
    const Numbers start = node_value(p, turn, bound);
    if (pn_solved(start) || start.proof >= proof_threshold || start.disproof >= disproof_threshold) {
        return;
    }

    MoveList moves;
    node_moves(p, turn, bound, &moves);
    const bool     and_node = turn == TURN_MAKER;
    const Turn     child_turn = and_node ? TURN_BREAKER : TURN_MAKER;
    const int      child_bound = and_node ? next_bound(bound) : bound;
    const Position key = canonical(p);
    Position       child[MAX_CELLS];
    for (int i = 0; i < moves.count; i++) {
        child[i] = child_of(p, turn, moves.cell[i]);
    }

    for (;;) {
        /* AND node: proof = sum of the children's proofs, disproof = their least disproof.
           OR node: the other way round.  `min` and `sum` name those two roles. */
        uint32_t min = PN_INFINITY;
        uint32_t second = PN_INFINITY;
        uint32_t sum = 0;
        int      best = -1;
        Numbers  best_value = PN_PROVED;
        for (int i = 0; i < moves.count; i++) {
            const Numbers c = node_value(child[i], child_turn, child_bound);
            const uint32_t c_min = and_node ? c.disproof : c.proof;
            const uint32_t c_sum = and_node ? c.proof : c.disproof;
            sum = pn_add(sum, c_sum);
            if (c_min < min) {
                second = min;
                min = c_min;
                best = i;
                best_value = c;
            } else if (c_min < second) {
                second = c_min;
            }
            if (c_min == 0) {
                break;                         /* this child decides the node */
            }
        }

        Numbers value;
        if (min == 0) {
            value = and_node ? PN_DISPROVED : PN_PROVED;
        } else if (sum == 0) {
            value = and_node ? PN_PROVED : PN_DISPROVED;
        } else if (and_node) {
            value = (Numbers){ sum, min };
        } else {
            value = (Numbers){ min, sum };
        }
        nodes_store(key, bound, turn, value);
        if (pn_solved(value) || value.proof >= proof_threshold
            || value.disproof >= disproof_threshold) {
            return;
        }

        const uint32_t min_threshold = and_node ? disproof_threshold : proof_threshold;
        const uint32_t sum_threshold = and_node ? proof_threshold : disproof_threshold;
        const uint32_t child_min_threshold = min_threshold < second + 1 ? min_threshold : second + 1;
        const uint32_t child_sum_threshold =
            sum_threshold_of(sum_threshold, sum, and_node ? best_value.proof : best_value.disproof);
        if (and_node) {
            dfpn(child[best], child_turn, child_bound, child_sum_threshold, child_min_threshold);
        } else {
            dfpn(child[best], child_turn, child_bound, child_min_threshold, child_sum_threshold);
        }
    }
}

/* Proves or disproves that Breaker holds Maker for `bound` moves from `root`. */
static bool breaker_holds(Position root, int bound)
{
    for (;;) {
        dfpn(root, TURN_MAKER, bound, PN_INFINITY, PN_INFINITY);
        const Numbers value = node_value(root, TURN_MAKER, bound);
        if (pn_solved(value)) {
            return value.proof == 0;
        }
    }
}

static inline bool node_proved(Position p, Turn turn, int bound)
{
    return node_value(p, turn, bound).proof == 0;
}

/* =========================================================================================
 * Phase 2: the smallest certificate
 * ========================================================================================= */

static uint32_t saturating_add(uint32_t a, uint32_t b)
{
    return a > SIZE_INFINITE - b ? SIZE_INFINITE : a + b;
}

static uint32_t certificate_size(Position p, int bound);

/*
 * Fewest positions below Maker's move `move`, over the replies proved in phase 1 (or proved
 * by a leaf rule now); also the reply.
 */
static uint32_t move_size(Position p, int move, int bound, int* best_reply)
{
    const Position after = { p.maker | cell_bit(move), p.breaker };
    const int rest = next_bound(bound);
    MoveList replies;
    breaker_replies(after, rest, &replies);
    uint32_t best = SIZE_INFINITE;
    *best_reply = -1;
    for (int i = 0; i < replies.count && best > 1; i++) {
        const Position next = { after.maker, after.breaker | cell_bit(replies.cell[i]) };
        if (node_proved(next, TURN_MAKER, rest)) {
            const uint32_t size = certificate_size(next, rest);
            if (size < best) {
                best = size;
                *best_reply = replies.cell[i];
            }
        }
    }
    return best;
}

/* Fewest certificate positions for a position where Breaker holds for `bound` moves. */
static uint32_t certificate_size(Position p, int bound)
{
    if (classify(p, bound, NULL) != LEAF_NONE) {
        return 1;
    }
    const Position key = canonical(p);
    const SizeEntry* known = sizes_find(key, bound);
    if (known != NULL) {
        return known->size;
    }
    uint32_t total = 1;
    for (Bitboard moves = free_cells(p); moves; moves &= moves - 1) {
        const int move = lowest_cell(moves);
        const Position after = { p.maker | cell_bit(move), p.breaker };
        if (free_cells(after) != 0) {
            int reply = -1;
            total = saturating_add(total, move_size(p, move, bound, &reply));
        }
    }
    sizes_store(key, bound, total);
    return total;
}

/* =========================================================================================
 * Output
 * ========================================================================================= */

typedef struct {
    uint64_t nodes;
    uint64_t short_leaves;
    uint64_t es_leaves;
    uint64_t pair_leaves;
    uint64_t repeated;                  /* positions printed before (same real board)        */
    uint64_t repeated_canonical;        /* positions whose canonical form was printed before */
} PrintStats;

static PrintStats printed;

/*
 * Sets of printed positions, by real board and by canonical form (size tables with the size
 * unused).  They measure how much a certificate repeats itself: the gain that sharing
 * repeated sub-certificates would bring.
 */
static SizeTable printed_real;
static SizeTable printed_canonical;

/* Inserts (key, bound) into `table`; returns whether it was there already. */
static bool seen_before(SizeTable* table, Position key, int bound)
{
    size_t index = hash_key(key, bound) & table->mask;
    while (table->slot[index].used) {
        const SizeEntry* entry = &table->slot[index];
        if (entry->maker == key.maker && entry->breaker == key.breaker && entry->bound == bound) {
            return true;
        }
        index = (index + 1) & table->mask;
    }
    if ((table->used + 1) * 4 > (table->mask + 1) * 3) {
        size_table_grow(table);
        index = hash_key(key, bound) & table->mask;
        while (table->slot[index].used) {
            index = (index + 1) & table->mask;
        }
    }
    table->used++;
    SizeEntry* entry = &table->slot[index];
    entry->used = true;
    entry->maker = key.maker;
    entry->breaker = key.breaker;
    entry->bound = (int8_t)bound;
    entry->size = 0;
    return false;
}

static void print_indent(FILE* out, int indent)
{
    fprintf(out, "\n%*s", 2 * indent, "");
}

static void print_certificate(FILE* out, Position p, int bound, int indent)
{
    printed.repeated += seen_before(&printed_real, p, bound);
    printed.repeated_canonical += seen_before(&printed_canonical, canonical(p), bound);
    Pairing pairing;
    switch (classify(p, bound, &pairing)) {
    case LEAF_SHORT:
        printed.short_leaves++;
        fprintf(out, "BrShort");
        return;
    case LEAF_ES:
        printed.es_leaves++;
        fprintf(out, "BrES");
        return;
    case LEAF_PAIR:
        printed.pair_leaves++;
        fprintf(out, "BrPair (");
        for (int i = 0; i < pairing.count; i++) {
            fprintf(out, "(%d, %d) :: ", pairing.first[i], pairing.second[i]);
        }
        fprintf(out, "nil)");
        return;
    case LEAF_NONE:
        break;
    }

    printed.nodes++;
    fprintf(out, "BrNode");
    int open = 0;
    for (Bitboard moves = free_cells(p); moves; moves &= moves - 1) {
        const int move = lowest_cell(moves);
        const Position after = { p.maker | cell_bit(move), p.breaker };
        if (free_cells(after) == 0) {
            continue;
        }
        int reply = -1;
        if (move_size(p, move, bound, &reply) == SIZE_INFINITE || reply < 0) {
            fprintf(stderr, "internal error: Maker move %d has no holding reply\n", move);
            exit(1);
        }
        const Position next = { after.maker, after.breaker | cell_bit(reply) };
        print_indent(out, indent + 1);
        fprintf(out, "(BmCons %d %d (", move, reply);
        print_certificate(out, next, next_bound(bound), indent + 2);
        fprintf(out, ")");
        open++;
    }
    fprintf(out, " BmNil");
    for (int i = 0; i < open; i++) {
        fprintf(out, ")");
    }
}

/* =========================================================================================
 * Main
 * ========================================================================================= */

static bool solve_job(FILE* out, int rows, int cols, int k, int bound)
{
    if (rows * cols > MAX_CELLS || rows <= 0 || cols <= 0 || k <= 0) {
        fprintf(stderr, "(%d,%d,%d): unsupported board\n", rows, cols, k);
        return false;
    }
    if (bound < 0 || bound > UNBOUNDED) {
        fprintf(stderr, "(%d,%d,%d): bound out of range\n", rows, cols, k);
        return false;
    }
    board_init(rows, cols, k);
    nodes_reset();
    sizes_reset();
    search_calls = 0;

    const Position root = { 0, 0 };
    char label[32];
    if (bound == UNBOUNDED) {
        snprintf(label, sizeof label, "draw");
    } else {
        snprintf(label, sizeof label, "within_%d", bound);
    }
    if (!breaker_holds(root, bound)) {
        fprintf(stderr, "(%d,%d,%d) %s: Breaker does not hold (Maker wins)\n",
                rows, cols, k, label);
        return false;
    }
    const uint32_t size = certificate_size(root, bound);

    if (bound == UNBOUNDED) {
        fprintf(out, "\n(** (%d, %d, %d): Maker never wins; %" PRIu32 " certificate positions. *)\n",
                rows, cols, k, size);
    } else {
        fprintf(out, "\n(** (%d, %d, %d): Maker cannot win within %d moves; %" PRIu32
                " certificate positions. *)\n", rows, cols, k, bound, size);
    }
    fprintf(out, "Definition br_cert_%d_%d_%d_%s : brcert :=\n  ", rows, cols, k, label);
    memset(&printed, 0, sizeof printed);
    size_table_init(&printed_real);
    size_table_init(&printed_canonical);
    print_certificate(out, root, bound, 1);
    fprintf(out, ".\n");
    printf("  repeated positions: %" PRIu64 " same board, %" PRIu64 " same canonical form\n",
           printed.repeated, printed.repeated_canonical);
    free(printed_real.slot);
    free(printed_canonical.slot);

    const uint64_t total = printed.nodes + printed.short_leaves + printed.es_leaves
                         + printed.pair_leaves;
    printf("(%d,%d,%d) %s: %" PRIu32 " positions (%" PRIu64 " nodes, %" PRIu64 " short, %"
           PRIu64 " ES, %" PRIu64 " pairing leaves)\n", rows, cols, k, label, size,
           printed.nodes, printed.short_leaves, printed.es_leaves, printed.pair_leaves);
    printf("  df-pn calls %" PRIu64 ", table nodes %zu, sized positions %zu\n",
           search_calls, nodes.used, sizes.used);
    if (total != size) {
        fprintf(stderr, "internal error: printed %" PRIu64 " positions, expected %" PRIu32 "\n",
                total, size);
        return false;
    }
    return true;
}

int main(int argc, char** argv)
{
    if (argc < 6 || (argc - 2) % 4 != 0) {
        fprintf(stderr, "usage: %s output.v m n k bound [m n k bound ...]  (bound: d or draw)\n",
                argv[0]);
        return 2;
    }
    FILE* out = fopen(argv[1], "w");
    if (out == NULL) {
        fprintf(stderr, "cannot write %s\n", argv[1]);
        return 1;
    }
    fprintf(out,
            "(** * Breaker certificates (GENERATED by solver/breaker_cert.c: do not edit)\n"
            "\n"
            "    Each [br_cert_m_n_k_within_d] is a Breaker strategy stopping Maker (moving\n"
            "    first) from completing k in a row on the m x n board within d moves; each\n"
            "    [br_cert_m_n_k_draw] stops Maker for ever.  They are checked with\n"
            "    [check_br] (MNKBreakerCert.v). *)\n"
            "\n"
            "From MNK Require Import MNKBreakerCert.\n");

    bool ok = true;
    for (int arg = 2; arg + 3 < argc; arg += 4) {
        const int bound = strcmp(argv[arg + 3], "draw") == 0 ? (int)UNBOUNDED : atoi(argv[arg + 3]);
        ok = solve_job(out, atoi(argv[arg]), atoi(argv[arg + 1]), atoi(argv[arg + 2]), bound) && ok;
    }
    fclose(out);
    free(nodes.slot);
    free(sizes.slot);
    return ok ? 0 : 1;
}
