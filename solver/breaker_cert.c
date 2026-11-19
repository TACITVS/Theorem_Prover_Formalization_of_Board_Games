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
 *   1. Does Breaker hold?  AND over Maker moves, OR over Breaker replies, with a table of
 *      solved positions keyed by the canonical form under the board's symmetries.  When
 *      Maker threatens to complete a line, only the block is tried.
 *   2. The smallest certificate: at every node and for every Maker move, the holding reply
 *      whose sub-certificate has the fewest positions (exact, memoised per canonical
 *      position and bound).
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
    TABLE_LOG2_LIMIT = 27,             /* give up beyond 2^27 solved positions (3 GB)     */
    PAIRING_BUDGET   = 200000,         /* search steps allowed per pairing attempt        */
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

static Position canonical(Position p)
{
    Position best = p;
    for (int t = 1; t < board.symmetry_count; t++) {
        const Position q = { apply_symmetry(t, p.maker), apply_symmetry(t, p.breaker) };
        if (q.maker < best.maker || (q.maker == best.maker && q.breaker < best.breaker)) {
            best = q;
        }
    }
    return best;
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

typedef struct {
    int count;
    int cell[MAX_CELLS];
} MoveList;

/*
 * The cells of `candidates`, most valuable to Maker first: a cell scores the sum over the open
 * lines through it of 8^(Maker stones on the line).  Ties keep cell order.
 */
static void order_cells(Position p, Bitboard candidates, MoveList* moves)
{
    int score[MAX_CELLS] = { 0 };
    for (int i = 0; i < board.line_count; i++) {
        const Bitboard line = board.line[i];
        if ((line & p.breaker) == 0) {
            const int weight = 1 << (3 * popcount(line & p.maker));
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

static bool line_has_pair(Bitboard line, const Pairing* pairing)
{
    for (int i = 0; i < pairing->count; i++) {
        if ((line & pairing->cells[i]) == pairing->cells[i]) {
            return true;
        }
    }
    return false;
}

/* Backtracking: cover the open line with the fewest available cells first. */
static bool extend_pairing(const Bitboard* lines, int count, Bitboard available,
                           Pairing* pairing, long* budget)
{
    if (--*budget < 0) {
        return false;
    }
    int best = -1;
    int best_free = MAX_CELLS + 1;
    for (int i = 0; i < count; i++) {
        if (line_has_pair(lines[i], pairing)) {
            continue;
        }
        const int f = popcount(lines[i] & available);
        if (f < 2) {
            return false;
        }
        if (f < best_free) {
            best_free = f;
            best = i;
        }
    }
    if (best < 0) {
        return true;
    }
    const Bitboard cells = lines[best] & available;
    for (Bitboard xs = cells; xs; xs &= xs - 1) {
        const int x = lowest_cell(xs);
        for (Bitboard ys = xs & (xs - 1); ys; ys &= ys - 1) {
            const int y = lowest_cell(ys);
            const int slot = pairing->count++;
            pairing->first[slot] = x;
            pairing->second[slot] = y;
            pairing->cells[slot] = cell_bit(x) | cell_bit(y);
            if (extend_pairing(lines, count, available & ~pairing->cells[slot], pairing, budget)) {
                return true;
            }
            pairing->count--;
        }
    }
    return false;
}

/* Disjoint pairs of free cells such that every open line contains a whole pair. */
static bool pairing_leaf(Position p, Pairing* pairing)
{
    Bitboard open[MAX_LINES];
    int count = 0;
    for (int i = 0; i < board.line_count; i++) {
        if ((board.line[i] & p.breaker) == 0) {
            open[count++] = board.line[i];
        }
    }
    pairing->count = 0;
    long budget = PAIRING_BUDGET;
    return extend_pairing(open, count, free_cells(p), pairing, &budget);
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

typedef struct {
    Bitboard maker;
    Bitboard breaker;
    int8_t   hold_bound;                /* largest bound known to hold; 0 = none known       */
    int8_t   fail_bound;                /* smallest bound known to fail; 0 = none known      */
    bool     used;
} SolvedEntry;

typedef struct {
    Bitboard maker;
    Bitboard breaker;
    uint32_t size;                      /* fewest certificate positions                      */
    int8_t   bound;
    bool     used;
} SizeEntry;

typedef struct {
    SolvedEntry* slot;
    size_t       mask;
    size_t       used;
} SolvedTable;

typedef struct {
    SizeEntry* slot;
    size_t     mask;
    size_t     used;
} SizeTable;

static SolvedTable solved;
static SizeTable   sizes;
static uint64_t    search_nodes;

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

static void solved_reset(void)
{
    free(solved.slot);
    solved.mask = ((size_t)1 << TABLE_LOG2) - 1;
    solved.slot = allocate_slots(solved.mask + 1, sizeof *solved.slot);
    solved.used = 0;
}

static void sizes_reset(void)
{
    free(sizes.slot);
    sizes.mask = ((size_t)1 << TABLE_LOG2) - 1;
    sizes.slot = allocate_slots(sizes.mask + 1, sizeof *sizes.slot);
    sizes.used = 0;
}

static SolvedEntry* solved_find(Position key)
{
    size_t index = hash_key(key, 0) & solved.mask;
    while (solved.slot[index].used) {
        if (solved.slot[index].maker == key.maker && solved.slot[index].breaker == key.breaker) {
            return &solved.slot[index];
        }
        index = (index + 1) & solved.mask;
    }
    return NULL;
}

static void solved_grow(void)
{
    if (solved.mask + 1 >= ((size_t)1 << TABLE_LOG2_LIMIT)) {
        fprintf(stderr, "solved table reached 2^%d entries: giving up\n", TABLE_LOG2_LIMIT);
        exit(1);
    }
    const SolvedTable old = solved;
    solved.mask = 2 * old.mask + 1;
    solved.slot = allocate_slots(solved.mask + 1, sizeof *solved.slot);
    for (size_t i = 0; i <= old.mask; i++) {
        if (old.slot[i].used) {
            const Position key = { old.slot[i].maker, old.slot[i].breaker };
            size_t index = hash_key(key, 0) & solved.mask;
            while (solved.slot[index].used) {
                index = (index + 1) & solved.mask;
            }
            solved.slot[index] = old.slot[i];
        }
    }
    free(old.slot);
}

/* The entry of `key`, created if absent.  Valid until the next insertion. */
static SolvedEntry* solved_insert(Position key)
{
    SolvedEntry* entry = solved_find(key);
    if (entry != NULL) {
        return entry;
    }
    if ((solved.used + 1) * 4 > (solved.mask + 1) * 3) {
        solved_grow();
    }
    size_t index = hash_key(key, 0) & solved.mask;
    while (solved.slot[index].used) {
        index = (index + 1) & solved.mask;
    }
    solved.used++;
    entry = &solved.slot[index];
    entry->used = true;
    entry->maker = key.maker;
    entry->breaker = key.breaker;
    return entry;
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

static void sizes_grow(void)
{
    const SizeTable old = sizes;
    sizes.mask = 2 * old.mask + 1;
    sizes.slot = allocate_slots(sizes.mask + 1, sizeof *sizes.slot);
    for (size_t i = 0; i <= old.mask; i++) {
        if (old.slot[i].used) {
            const Position key = { old.slot[i].maker, old.slot[i].breaker };
            size_t index = hash_key(key, old.slot[i].bound) & sizes.mask;
            while (sizes.slot[index].used) {
                index = (index + 1) & sizes.mask;
            }
            sizes.slot[index] = old.slot[i];
        }
    }
    free(old.slot);
}

static void sizes_store(Position key, int bound, uint32_t size)
{
    if ((sizes.used + 1) * 4 > (sizes.mask + 1) * 3) {
        sizes_grow();
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
 * Phase 1: does Breaker hold Maker for `bound` more moves?
 * ========================================================================================= */

/*
 * Breaker's candidate replies after Maker's move, best first.  When Maker still has a move and
 * threatens to complete a line, only the block can hold; against two threats nothing can.
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
    order_cells(after, free_cells(after), replies);
}

static bool holds(Position p, int bound);

/* Does Breaker have a reply to Maker's move `move` that holds for the remaining moves? */
static bool move_held(Position p, int move, int bound)
{
    const Position after = { p.maker | cell_bit(move), p.breaker };
    if (free_cells(after) == 0) {
        return true;                       /* the board is full without a Maker line      */
    }
    const int rest = next_bound(bound);
    MoveList replies;
    breaker_replies(after, rest, &replies);
    for (int i = 0; i < replies.count; i++) {
        const Position next = { after.maker, after.breaker | cell_bit(replies.cell[i]) };
        if (holds(next, rest)) {
            return true;
        }
    }
    return false;
}

static bool holds(Position p, int bound)
{
    if (bound == 0) {
        return true;
    }
    if (winning_cells(p)) {
        return false;
    }
    if (bound != UNBOUNDED && short_leaf(p, bound)) {
        return true;
    }
    if (es_leaf(p)) {
        return true;
    }
    const Position key = canonical(p);
    const SolvedEntry* known = solved_find(key);
    if (known != NULL) {
        if (known->hold_bound >= bound) {
            return true;
        }
        if (known->fail_bound != 0 && known->fail_bound <= bound) {
            return false;
        }
    }
    Pairing pairing;
    bool result = pairing_leaf(p, &pairing);
    if (!result) {
        search_nodes++;
        MoveList moves;
        order_cells(p, free_cells(p), &moves);
        result = true;
        for (int i = 0; i < moves.count && result; i++) {
            result = move_held(p, moves.cell[i], bound);
        }
    }

    SolvedEntry* entry = solved_insert(key);      /* looked up again: the table may have grown */
    if (result) {
        if (bound > entry->hold_bound) {
            entry->hold_bound = (int8_t)bound;
        }
    } else if (entry->fail_bound == 0 || bound < entry->fail_bound) {
        entry->fail_bound = (int8_t)bound;
    }
    return result;
}

/* =========================================================================================
 * Phase 2: the smallest certificate
 * ========================================================================================= */

static uint32_t saturating_add(uint32_t a, uint32_t b)
{
    return a > SIZE_INFINITE - b ? SIZE_INFINITE : a + b;
}

static uint32_t certificate_size(Position p, int bound);

/* Fewest positions below Maker's move `move`, over the holding replies; also the reply. */
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
        if (holds(next, rest)) {
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
} PrintStats;

static PrintStats printed;

static void print_indent(FILE* out, int indent)
{
    fprintf(out, "\n%*s", 2 * indent, "");
}

static void print_certificate(FILE* out, Position p, int bound, int indent)
{
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
    solved_reset();
    sizes_reset();
    search_nodes = 0;

    const Position root = { 0, 0 };
    char label[32];
    if (bound == UNBOUNDED) {
        snprintf(label, sizeof label, "draw");
    } else {
        snprintf(label, sizeof label, "within_%d", bound);
    }
    if (!holds(root, bound)) {
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
    print_certificate(out, root, bound, 1);
    fprintf(out, ".\n");

    const uint64_t total = printed.nodes + printed.short_leaves + printed.es_leaves
                         + printed.pair_leaves;
    printf("(%d,%d,%d) %s: %" PRIu32 " positions (%" PRIu64 " nodes, %" PRIu64 " short, %"
           PRIu64 " ES, %" PRIu64 " pairing leaves)\n", rows, cols, k, label, size,
           printed.nodes, printed.short_leaves, printed.es_leaves, printed.pair_leaves);
    printf("  search nodes %" PRIu64 ", solved positions %zu, sized positions %zu\n",
           search_nodes, solved.used, sizes.used);
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
    free(solved.slot);
    free(sizes.slot);
    return ok ? 0 : 1;
}
