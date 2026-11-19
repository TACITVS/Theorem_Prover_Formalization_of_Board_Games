/*
 * mb_win_cert.c: Maker-win certificates for Maker-Breaker (m, n, k) games, checked in Rocq
 *
 * For each board given on the command line, the program proves that Maker (Player 1, moving
 * first) claims a whole line in the Maker-Breaker game, and writes the strategy as a term of
 * type `mbcert` (MNKMakerBreakerCert.v).  The Rocq checker `check_mb` accepts it, and its
 * soundness theorem turns that into `maker_wins`.
 *
 * ------------------------------------------------------------------------------------------
 * Certificate shape (must match check_mb)
 * ------------------------------------------------------------------------------------------
 *
 *   MB m replies    Maker plays m.  If m completes a line, `replies` is RNil.  Otherwise
 *                   `replies` holds one sub-certificate for every Breaker reply after which
 *                   Maker has no cell completing a line; the checker settles the other
 *                   replies by finding such a cell itself.
 *
 *   So after a Maker threat (one cell t completing a line), only the reply t is listed; after
 *   a double threat, none is.
 *
 * ------------------------------------------------------------------------------------------
 * Search
 * ------------------------------------------------------------------------------------------
 *
 *   1. Iterative deepening on d, the number of Maker moves: is there a Maker win within d?
 *      AND/OR search with a table of solved positions, keyed by the canonical form of the
 *      position under the board's symmetries.  Maker moves are restricted to free cells of
 *      live lines (lines without a Breaker stone): this only limits which wins are found.
 *   2. Among the fastest winning strategies, the one with the fewest certificate nodes: at each
 *      Maker node, the winning move minimising 1 + the sizes of the listed replies'
 *      sub-certificates (exact, memoised per canonical position and depth).
 *   3. The certificate is written in real board coordinates; the table is queried with
 *      canonical keys, so every symmetric position shares one entry.
 *
 *   Cells are numbered r * n + c, as in MNKBoard.v.
 *
 * ------------------------------------------------------------------------------------------
 * Build and usage
 * ------------------------------------------------------------------------------------------
 *
 *   clang -std=c11 -O3 -march=native -o mb_win_cert.exe mb_win_cert.c
 *
 *   mb_win_cert output.v [extra_depth] m n k [m n k ...]
 *
 *   extra_depth (default 0): the certificate is the fastest win.  With extra_depth > 0, depths
 *   up to that many moves longer are tried too, and the smallest certificate is kept, which
 *   may be a slower win.
 */

#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t Bitboard;

enum {
    MAX_CELLS      = 64,
    MAX_LINES      = 1024,
    MAX_SYMMETRIES = 8,
    MAX_DEPTH      = 24,
    TABLE_LOG2       = 20,             /* initial table size; tables double when needed   */
    TABLE_LOG2_LIMIT = 27,             /* give up beyond 2^27 solved positions (3 GB)     */
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

/* Cells that complete a line for Maker: lines without a Breaker stone missing one cell. */
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

static inline Bitboard free_cells(Position p)
{
    return board.all_cells & ~(p.maker | p.breaker);
}

/*
 * Erdos-Selfridge, Maker to move: Breaker holds every line when the live lines satisfy
 * sum 2^-(free cells) < 1/2, i.e. sum 2^(Maker stones) < 2^(k-1).  This only prunes the
 * search; the certificate is checked in Rocq whatever the search does, so a pruning rule
 * can at worst miss a win, never produce a wrong certificate.
 */
static bool breaker_holds_by_potential(Position p)
{
    uint64_t total = 0;
    for (int i = 0; i < board.line_count; i++) {
        const Bitboard line = board.line[i];
        if ((line & p.breaker) == 0) {
            total += (uint64_t)1 << popcount(line & p.maker);
        }
    }
    return 2 * total < ((uint64_t)1 << board.k);
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
    int8_t   win_depth;                 /* smallest depth known to win; 0 = none known       */
    int8_t   fail_depth;                /* largest depth known not to win; 0 = none known    */
    bool     used;
} SolvedEntry;

typedef struct {
    Bitboard maker;
    Bitboard breaker;
    uint32_t size;                      /* fewest certificate nodes; SIZE_INFINITE = no win  */
    int8_t   depth;
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

static inline size_t hash_key(Position key, int depth)
{
    uint64_t hash = key.maker * 0x9E3779B97F4A7C15ull ^ key.breaker * 0xC2B2AE3D27D4EB4Full;
    hash ^= (uint64_t)depth * 0x165667B19E3779F9ull;
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

static const SizeEntry* sizes_find(Position key, int depth)
{
    size_t index = hash_key(key, depth) & sizes.mask;
    while (sizes.slot[index].used) {
        const SizeEntry* entry = &sizes.slot[index];
        if (entry->maker == key.maker && entry->breaker == key.breaker && entry->depth == depth) {
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
            size_t index = hash_key(key, old.slot[i].depth) & sizes.mask;
            while (sizes.slot[index].used) {
                index = (index + 1) & sizes.mask;
            }
            sizes.slot[index] = old.slot[i];
        }
    }
    free(old.slot);
}

static void sizes_store(Position key, int depth, uint32_t size)
{
    if ((sizes.used + 1) * 4 > (sizes.mask + 1) * 3) {
        sizes_grow();
    }
    size_t index = hash_key(key, depth) & sizes.mask;
    while (sizes.slot[index].used) {
        index = (index + 1) & sizes.mask;
    }
    sizes.used++;
    SizeEntry* entry = &sizes.slot[index];
    entry->used = true;
    entry->maker = key.maker;
    entry->breaker = key.breaker;
    entry->depth = (int8_t)depth;
    entry->size = size;
}

/* =========================================================================================
 * Phase 1: is there a Maker win within `depth` Maker moves?
 * ========================================================================================= */

typedef struct {
    int count;
    int cell[MAX_CELLS];
} MoveList;

/*
 * The cells of `candidates`, most valuable to Maker first: a cell scores the sum over the live
 * lines through it of 8^(Maker stones on the line), so lines nearer completion weigh more.
 * Ties keep cell order.
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

/* Free cells of live lines (lines without a Breaker stone). */
static Bitboard live_free_cells(Position p)
{
    Bitboard cells = 0;
    for (int i = 0; i < board.line_count; i++) {
        if ((board.line[i] & p.breaker) == 0) {
            cells |= board.line[i];
        }
    }
    return cells & free_cells(p);
}

/* Maker's candidate moves: free cells of live lines, most promising first. */
static void maker_moves(Position p, MoveList* moves)
{
    order_cells(p, live_free_cells(p), moves);
}

static bool wins_within(Position p, int depth);

/* Does Maker's move `move` win within `depth` moves (counting this one)? */
static bool move_wins(Position p, int move, int depth)
{
    const Position after = { p.maker | cell_bit(move), p.breaker };
    const Bitboard replies = free_cells(after);
    if (replies == 0) {
        return false;                      /* the board is full without a Maker line      */
    }
    const Bitboard threats = winning_cells(after);
    if (popcount(threats) >= 2) {
        return true;                       /* every reply leaves a winning cell           */
    }
    if (threats) {
        const Position blocked = { after.maker, after.breaker | threats };
        return wins_within(blocked, depth - 1);
    }
    /* The replies most valuable to Maker are the likeliest refutations: try them first. */
    MoveList order;
    order_cells(after, replies, &order);
    for (int i = 0; i < order.count; i++) {
        const Position next = { after.maker, after.breaker | cell_bit(order.cell[i]) };
        if (!wins_within(next, depth - 1)) {
            return false;
        }
    }
    return true;
}

static bool wins_within(Position p, int depth)
{
    if (depth <= 0) {
        return false;
    }
    if (winning_cells(p)) {
        return true;
    }
    if (depth == 1 || breaker_holds_by_potential(p)) {
        return false;
    }
    const Position key = canonical(p);
    const SolvedEntry* known = solved_find(key);
    if (known != NULL) {
        if (known->win_depth != 0 && known->win_depth <= depth) {
            return true;
        }
        if (known->fail_depth >= depth) {
            return false;
        }
    }
    search_nodes++;

    MoveList moves;
    maker_moves(p, &moves);
    bool result = false;
    for (int i = 0; i < moves.count && !result; i++) {
        result = move_wins(p, moves.cell[i], depth);
    }

    SolvedEntry* entry = solved_insert(key);      /* looked up again: the table may have grown */
    if (result) {
        if (entry->win_depth == 0 || depth < entry->win_depth) {
            entry->win_depth = (int8_t)depth;
        }
    } else if (depth > entry->fail_depth) {
        entry->fail_depth = (int8_t)depth;
    }
    return result;
}

/* =========================================================================================
 * Phase 2: the smallest certificate
 * ========================================================================================= */

static uint32_t certificate_size(Position p, int depth);

static uint32_t saturating_add(uint32_t a, uint32_t b)
{
    return a > SIZE_INFINITE - b ? SIZE_INFINITE : a + b;
}

/* Certificate nodes for Maker's move `move`, which must win within `depth` from a position
   where Maker has no cell completing a line. */
static uint32_t move_size(Position p, int move, int depth)
{
    const Position after = { p.maker | cell_bit(move), p.breaker };
    const Bitboard threats = winning_cells(after);
    if (popcount(threats) >= 2) {
        return 1;
    }
    if (threats) {
        const Position blocked = { after.maker, after.breaker | threats };
        return saturating_add(1, certificate_size(blocked, depth - 1));
    }
    uint32_t total = 1;
    Bitboard rest = free_cells(after);
    while (rest) {
        const int reply = lowest_cell(rest);
        rest &= rest - 1;
        const Position next = { after.maker, after.breaker | cell_bit(reply) };
        total = saturating_add(total, certificate_size(next, depth - 1));
    }
    return total;
}

/* Fewest certificate nodes for a Maker win within `depth`, or SIZE_INFINITE. */
static uint32_t certificate_size(Position p, int depth)
{
    if (winning_cells(p)) {
        return 1;
    }
    if (!wins_within(p, depth)) {
        return SIZE_INFINITE;
    }
    const Position key = canonical(p);
    const SizeEntry* known = sizes_find(key, depth);
    if (known != NULL) {
        return known->size;
    }
    MoveList moves;
    maker_moves(p, &moves);
    uint32_t best = SIZE_INFINITE;
    for (int i = 0; i < moves.count && best > 1; i++) {
        if (move_wins(p, moves.cell[i], depth)) {
            const uint32_t size = move_size(p, moves.cell[i], depth);
            if (size < best) {
                best = size;
            }
        }
    }
    sizes_store(key, depth, best);
    return best;
}

/* =========================================================================================
 * Output
 * ========================================================================================= */

static uint64_t printed_nodes;

static void print_indent(FILE* out, int indent)
{
    fprintf(out, "\n%*s", 2 * indent, "");
}

static void print_certificate(FILE* out, Position p, int depth, int indent)
{
    printed_nodes++;
    const Bitboard wins = winning_cells(p);
    if (wins) {
        fprintf(out, "MB %d RNil", lowest_cell(wins));
        return;
    }
    const uint32_t target = certificate_size(p, depth);
    MoveList moves;
    maker_moves(p, &moves);
    int move = -1;
    for (int i = 0; i < moves.count; i++) {
        if (move_wins(p, moves.cell[i], depth) && move_size(p, moves.cell[i], depth) == target) {
            move = moves.cell[i];
            break;
        }
    }
    if (move < 0) {
        fprintf(stderr, "internal error: no move reaches the certificate size\n");
        exit(1);
    }

    const Position after = { p.maker | cell_bit(move), p.breaker };
    const Bitboard threats = winning_cells(after);
    Bitboard listed = 0;
    if (popcount(threats) == 1) {
        listed = threats;
    } else if (threats == 0) {
        listed = free_cells(after);
    }

    fprintf(out, "MB %d", move);
    int open = 0;
    while (listed) {
        const int reply = lowest_cell(listed);
        listed &= listed - 1;
        const Position next = { after.maker, after.breaker | cell_bit(reply) };
        print_indent(out, indent + 1);
        fprintf(out, "(RCons %d (", reply);
        print_certificate(out, next, depth - 1, indent + 2);
        fprintf(out, ")");
        open++;
    }
    fprintf(out, " RNil");
    for (int i = 0; i < open; i++) {
        fprintf(out, ")");
    }
}

/* =========================================================================================
 * Main
 * ========================================================================================= */

static bool solve_board(FILE* out, int rows, int cols, int k, int extra_depth)
{
    if (rows * cols > MAX_CELLS || rows <= 0 || cols <= 0 || k <= 0) {
        fprintf(stderr, "(%d,%d,%d): unsupported board\n", rows, cols, k);
        return false;
    }
    board_init(rows, cols, k);
    solved_reset();
    sizes_reset();
    search_nodes = 0;

    const Position root = { 0, 0 };
    const int max_moves = (board.cells + 1) / 2;
    int depth = 1;
    while (depth <= max_moves && depth <= MAX_DEPTH && !wins_within(root, depth)) {
        depth++;
    }
    if (depth > max_moves || depth > MAX_DEPTH) {
        fprintf(stderr, "(%d,%d,%d): no Maker win found\n", rows, cols, k);
        return false;
    }

    int best_depth = depth;
    uint32_t best_size = certificate_size(root, depth);
    printf("(%d,%d,%d): Maker wins within %d moves; certificate %" PRIu32 " nodes",
           rows, cols, k, depth, best_size);
    for (int d = depth + 1; d <= depth + extra_depth && d <= MAX_DEPTH; d++) {
        const uint32_t size = certificate_size(root, d);
        printf("; within %d: %" PRIu32 " nodes", d, size);
        if (size < best_size) {
            best_size = size;
            best_depth = d;
        }
    }
    printf("\n  search nodes %" PRIu64 ", solved positions %zu, sized positions %zu\n",
           search_nodes, solved.used, sizes.used);

    fprintf(out, "\n(** (%d, %d, %d): Maker wins within %d moves; %" PRIu32 " certificate nodes. *)\n",
            rows, cols, k, best_depth, best_size);
    fprintf(out, "Definition mb_depth_%d_%d_%d : nat := %d.\n\n", rows, cols, k, best_depth);
    fprintf(out, "Definition mb_cert_%d_%d_%d : mbcert :=\n  ", rows, cols, k);
    printed_nodes = 0;
    print_certificate(out, root, best_depth, 1);
    fprintf(out, ".\n");
    if (printed_nodes != best_size) {
        fprintf(stderr, "internal error: printed %" PRIu64 " nodes, expected %" PRIu32 "\n",
                printed_nodes, best_size);
        return false;
    }
    return true;
}

int main(int argc, char** argv)
{
    if (argc < 5) {
        fprintf(stderr, "usage: %s output.v [extra_depth] m n k [m n k ...]\n", argv[0]);
        return 2;
    }
    int arg = 2;
    int extra_depth = 0;
    if ((argc - 2) % 3 == 1) {
        extra_depth = atoi(argv[arg++]);
    }
    if ((argc - arg) % 3 != 0) {
        fprintf(stderr, "boards are given as m n k triples\n");
        return 2;
    }

    FILE* out = fopen(argv[1], "w");
    if (out == NULL) {
        fprintf(stderr, "cannot write %s\n", argv[1]);
        return 1;
    }
    fprintf(out,
            "(** * Maker-Breaker win certificates (GENERATED by solver/mb_win_cert.c: do not edit)\n"
            "\n"
            "    Each [mb_cert_m_n_k] is a Maker strategy for the Maker-Breaker game on the\n"
            "    m x n board with k in a row, Maker moving first.  MNKMakerWins.v checks them\n"
            "    with [check_mb]. *)\n"
            "\n"
            "From MNK Require Import MNKMakerBreakerCert.\n");

    bool ok = true;
    for (; arg + 2 < argc; arg += 3) {
        ok = solve_board(out, atoi(argv[arg]), atoi(argv[arg + 1]), atoi(argv[arg + 2]),
                         extra_depth) && ok;
    }
    fclose(out);
    free(solved.slot);
    free(sizes.slot);
    return ok ? 0 : 1;
}
