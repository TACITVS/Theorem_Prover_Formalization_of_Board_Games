#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define W 9
#define H 7
#define TOTAL_CELLS (W * H) // 63 cells

// Masks for bitboard boundary check
// Column c offset: 7 * c
// ROW_456_MASK: rows 4, 5, 6 of each column (bits 4, 5, 6 in each 7-bit column)
// 0x70 = 0b01110000
#define ROW_456_MASK (\
    (0x70ULL) | (0x70ULL << 7) | (0x70ULL << 14) | (0x70ULL << 21) | \
    (0x70ULL << 28) | (0x70ULL << 35) | (0x70ULL << 42) | (0x70ULL << 49) | (0x70ULL << 56))

// ROW_012_MASK: rows 0, 1, 2 of each column (bits 0, 1, 2 in each 7-bit column)
// 0x07 = 0b00000111
#define ROW_012_MASK (\
    (0x07ULL) | (0x07ULL << 7) | (0x07ULL << 14) | (0x07ULL << 21) | \
    (0x07ULL << 28) | (0x07ULL << 35) | (0x07ULL << 42) | (0x07ULL << 49) | (0x07ULL << 56))

typedef struct {
    uint64_t white;
    uint64_t black;
    uint8_t heights[W];
    uint8_t ply; // 0 = White to move, 1 = Black to move, etc.
} Board;

static inline bool has_won(uint64_t p) {
    // 1. Vertical (step 1 bit in same column, lowest bit is row 0, 1, or 2)
    uint64_t v = p & (p >> 1) & (p >> 2) & (p >> 3) & (p >> 4) & ROW_012_MASK;
    if (v) return true;

    // 2. Horizontal (step 7 bits, exactly 1 column across)
    uint64_t h = p & (p >> 7) & (p >> 14) & (p >> 21) & (p >> 28);
    if (h) return true;

    // 3. Positive Diagonal (slope +1, step 7 + 1 = 8 bits, lowest bit is row 0, 1, or 2)
    uint64_t d1 = p & (p >> 8) & (p >> 16) & (p >> 24) & (p >> 32) & ROW_012_MASK;
    if (d1) return true;

    // 4. Negative Diagonal (slope -1, step 7 - 1 = 6 bits, lowest bit is row 4, 5, or 6)
    uint64_t d2 = p & (p >> 6) & (p >> 12) & (p >> 18) & (p >> 24) & ROW_456_MASK;
    if (d2) return true;

    return false;
}

// Fast xorshift64star PRNG
static uint64_t rng_state = 0x853c49e6748fea9bULL;
static inline uint64_t next_u64(void) {
    uint64_t x = rng_state;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rng_state = x;
    return x * 0x2545F4914F6CDD1DULL;
}

static inline uint32_t rand_int(uint32_t n) {
    return (uint32_t)(next_u64() % n);
}

static inline void init_board(Board *b) {
    b->white = 0;
    b->black = 0;
    memset(b->heights, 0, sizeof(b->heights));
    b->ply = 0;
}

static inline bool play_move(Board *b, int col) {
    if (col < 0 || col >= W || b->heights[col] >= H) return false;
    uint8_t row = b->heights[col]++;
    uint64_t bit = 1ULL << (col * 7 + row);
    if ((b->ply & 1) == 0) {
        b->white |= bit;
    } else {
        b->black |= bit;
    }
    b->ply++;
    return true;
}

static inline void undo_move(Board *b, int col) {
    b->ply--;
    uint8_t row = --b->heights[col];
    uint64_t bit = 1ULL << (col * 7 + row);
    if ((b->ply & 1) == 0) {
        b->white &= ~bit;
    } else {
        b->black &= ~bit;
    }
}

// Check 92 winning lines unit test
static void verify_line_detection(void) {
    int total_lines = 0;
    // Horizontal: 7 rows, cols 0..4, 1..5, 2..6, 3..7, 4..8 -> 5 * 7 = 35 lines
    for (int r = 0; r < H; r++) {
        for (int c = 0; c <= W - 5; c++) {
            uint64_t mask = 0;
            for (int i = 0; i < 5; i++) mask |= (1ULL << ((c + i) * 7 + r));
            if (!has_won(mask)) {
                printf("FATAL ERROR: Failed to detect horizontal line at r=%d, c=%d\n", r, c);
                exit(1);
            }
            total_lines++;
        }
    }
    // Vertical: 9 columns, rows 0..4, 1..5, 2..6 -> 3 * 9 = 27 lines
    for (int c = 0; c < W; c++) {
        for (int r = 0; r <= H - 5; r++) {
            uint64_t mask = 0;
            for (int i = 0; i < 5; i++) mask |= (1ULL << (c * 7 + r + i));
            if (!has_won(mask)) {
                printf("FATAL ERROR: Failed to detect vertical line at c=%d, r=%d\n", c, r);
                exit(1);
            }
            total_lines++;
        }
    }
    // Positive Diagonals: (W-4)*(H-4) = 5 * 3 = 15 lines
    for (int c = 0; c <= W - 5; c++) {
        for (int r = 0; r <= H - 5; r++) {
            uint64_t mask = 0;
            for (int i = 0; i < 5; i++) mask |= (1ULL << ((c + i) * 7 + (r + i)));
            if (!has_won(mask)) {
                printf("FATAL ERROR: Failed to detect pos diagonal at c=%d, r=%d\n", c, r);
                exit(1);
            }
            total_lines++;
        }
    }
    // Negative Diagonals: (W-4)*(H-4) = 5 * 3 = 15 lines
    for (int c = 0; c <= W - 5; c++) {
        for (int r = 4; r < H; r++) {
            uint64_t mask = 0;
            for (int i = 0; i < 5; i++) mask |= (1ULL << ((c + i) * 7 + (r - i)));
            if (!has_won(mask)) {
                printf("FATAL ERROR: Failed to detect neg diagonal at c=%d, r=%d\n", c, r);
                exit(1);
            }
            total_lines++;
        }
    }

    if (total_lines != 92) {
        printf("FATAL ERROR: Total lines is %d, expected 92!\n", total_lines);
        exit(1);
    }
    printf("[Verification Passed] All %d winning lines on 9x7 Connect-5 detected with 100%% precision!\n", total_lines);
}

// Tactical 1-ply check for rollouts
static inline int find_winning_move(const Board *b, uint64_t mask) {
    for (int c = 0; c < W; c++) {
        if (b->heights[c] < H) {
            uint64_t next_mask = mask | (1ULL << (c * 7 + b->heights[c]));
            if (has_won(next_mask)) return c;
        }
    }
    return -1;
}

// Fast rollout returning +1 (White win), -1 (Black win), 0 (Draw)
static int fast_rollout(Board *b, uint64_t *cell_visits) {
    while (b->ply < TOTAL_CELLS) {
        uint64_t my_mask = (b->ply & 1) == 0 ? b->white : b->black;
        uint64_t opp_mask = (b->ply & 1) == 0 ? b->black : b->white;

        // 1. Immediate win check
        int win_col = find_winning_move(b, my_mask);
        if (win_col != -1) {
            if (cell_visits) cell_visits[win_col * 7 + b->heights[win_col]]++;
            play_move(b, win_col);
            return (b->ply & 1) == 1 ? +1 : -1;
        }

        // 2. Immediate block check
        int block_col = find_winning_move(b, opp_mask);
        int chosen_col;
        if (block_col != -1) {
            chosen_col = block_col;
        } else {
            // Pick legal move
            int legal[W];
            int n_legal = 0;
            for (int c = 0; c < W; c++) {
                if (b->heights[c] < H) legal[n_legal++] = c;
            }
            if (n_legal == 0) return 0; // Board full
            chosen_col = legal[rand_int(n_legal)];
        }

        if (cell_visits) cell_visits[chosen_col * 7 + b->heights[chosen_col]]++;
        play_move(b, chosen_col);

        // Check if move won
        uint64_t current_mask = ((b->ply - 1) & 1) == 0 ? b->white : b->black;
        if (has_won(current_mask)) {
            return ((b->ply - 1) & 1) == 0 ? +1 : -1;
        }
    }
    return 0; // Draw
}

// MCTS Node
typedef struct MCTSNode {
    uint32_t visits;
    double white_value; // sum of outcomes from White's perspective (+1 win, -1 loss, 0 draw)
    int move_col;
    struct MCTSNode *parent;
    struct MCTSNode *children[W];
    uint8_t unexpanded_moves[W];
    uint8_t n_unexpanded;
    bool is_terminal;
    int terminal_result; // +1, -1, 0
} MCTSNode;

#define MAX_POOL 1500000
static MCTSNode node_pool[MAX_POOL];
static uint32_t node_count = 0;

static inline MCTSNode* alloc_node(MCTSNode *parent, int move_col, const Board *b) {
    if (node_count >= MAX_POOL) return NULL;
    MCTSNode *n = &node_pool[node_count++];
    n->visits = 0;
    n->white_value = 0.0;
    n->move_col = move_col;
    n->parent = parent;
    memset(n->children, 0, sizeof(n->children));
    n->is_terminal = false;
    n->terminal_result = 0;

    // Check if terminal
    if (b->ply > 0) {
        uint64_t last_mask = ((b->ply - 1) & 1) == 0 ? b->white : b->black;
        if (has_won(last_mask)) {
            n->is_terminal = true;
            n->terminal_result = ((b->ply - 1) & 1) == 0 ? +1 : -1;
            n->n_unexpanded = 0;
            return n;
        }
    }
    if (b->ply >= TOTAL_CELLS) {
        n->is_terminal = true;
        n->terminal_result = 0;
        n->n_unexpanded = 0;
        return n;
    }

    // List legal moves
    n->n_unexpanded = 0;
    // Order moves from center outwards (4, 3, 5, 2, 6, 1, 7, 0, 8)
    static const int center_order[W] = {4, 3, 5, 2, 6, 1, 7, 0, 8};
    for (int i = 0; i < W; i++) {
        int c = center_order[i];
        if (b->heights[c] < H) {
            n->unexpanded_moves[n->n_unexpanded++] = c;
        }
    }
    return n;
}

// UCT Selection
static inline MCTSNode* select_child_uct(MCTSNode *node, bool is_white_turn, double c_param) {
    MCTSNode *best_child = NULL;
    double best_uct = -1e9;

    for (int i = 0; i < W; i++) {
        MCTSNode *child = node->children[i];
        if (!child || child->visits == 0) continue;

        double exploitation = (child->white_value / (double)child->visits);
        if (!is_white_turn) exploitation = -exploitation; // Flip for Black

        double exploration = c_param * sqrt(log((double)node->visits) / (double)child->visits);
        double uct = exploitation + exploration;

        if (uct > best_uct) {
            best_uct = uct;
            best_child = child;
        }
    }
    return best_child;
}

// Run MCTS search from a given position
static void mcts_search(Board *root_board, int iterations, double c_param, uint64_t *cell_visits) {
    node_count = 0;
    MCTSNode *root = alloc_node(NULL, -1, root_board);

    for (int iter = 0; iter < iterations; iter++) {
        Board sim_board = *root_board;
        MCTSNode *curr = root;

        // 1. Selection
        while (!curr->is_terminal && curr->n_unexpanded == 0) {
            bool is_white = (sim_board.ply & 1) == 0;
            MCTSNode *next = select_child_uct(curr, is_white, c_param);
            if (!next) break;
            play_move(&sim_board, next->move_col);
            curr = next;
        }

        // 2. Expansion
        if (!curr->is_terminal && curr->n_unexpanded > 0) {
            int move = curr->unexpanded_moves[--curr->n_unexpanded];
            play_move(&sim_board, move);
            MCTSNode *child = alloc_node(curr, move, &sim_board);
            if (child) {
                curr->children[move] = child;
                curr = child;
            }
        }

        // 3. Simulation (Rollout)
        int outcome = 0;
        if (curr->is_terminal) {
            outcome = curr->terminal_result;
        } else {
            Board rollout_board = sim_board;
            outcome = fast_rollout(&rollout_board, cell_visits);
        }

        // 4. Backpropagation
        while (curr != NULL) {
            curr->visits++;
            curr->white_value += outcome;
            curr = curr->parent;
        }
    }
}

// Print 2D Heatmap
static void print_heatmap(const uint64_t *visits) {
    uint64_t max_val = 1;
    for (int i = 0; i < TOTAL_CELLS; i++) {
        if (visits[i] > max_val) max_val = visits[i];
    }

    printf("\n=== SPATIAL VISITATION HEATMAP (9x7 Grid) ===\n");
    printf("Row \\ Col  0    1    2    3    4(C) 5    6    7    8\n");
    printf("----------------------------------------------------\n");
    for (int r = H - 1; r >= 0; r--) {
        printf(" Row %d |", r);
        for (int c = 0; c < W; c++) {
            uint64_t v = visits[c * 7 + r];
            double pct = (double)v / (double)max_val * 100.0;
            if (pct >= 75.0) {
                printf(" \033[1;31m%3.0f%%\033[0m", pct); // Bright Red (Hot)
            } else if (pct >= 50.0) {
                printf(" \033[1;33m%3.0f%%\033[0m", pct); // Yellow (Warm)
            } else if (pct >= 25.0) {
                printf(" \033[1;32m%3.0f%%\033[0m", pct); // Green
            } else {
                printf(" %3.0f%%", pct);
            }
        }
        printf("\n");
    }
    printf("----------------------------------------------------\n");
}

int main(int argc, char **argv) {
    (void)argc; (void)argv;
    printf("========================================================================\n");
    printf("  MONTE CARLO TREE SEARCH (MCTS) DISCOVERY ENGINE: CONNECT-5 (9x7)      \n");
    printf("  Grid: 9 Columns x 7 Rows | Winning Lines: 92 | Cells: 63 (Single uint64)\n");
    printf("========================================================================\n\n");

    verify_line_detection();

    uint64_t global_cell_visits[TOTAL_CELLS];
    memset(global_cell_visits, 0, sizeof(global_cell_visits));

    // EXPERIMENT 1: Root Analysis - Comparing All 9 Opening Moves
    printf("\n------------------------------------------------------------------------\n");
    printf("  EXPERIMENT 1: Root MCTS Evaluation of All 9 Opening Moves (White)\n");
    printf("------------------------------------------------------------------------\n");

    Board root;
    init_board(&root);

    int root_iters = 300000;
    printf("Running %d MCTS simulations from starting position...\n", root_iters);
    clock_t start = clock();
    mcts_search(&root, root_iters, 1.414, global_cell_visits);
    clock_t end = clock();
    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;
    printf("Completed in %.2f seconds (%.0f iterations/sec)!\n\n", elapsed, root_iters / elapsed);

    MCTSNode *root_node = &node_pool[0];
    printf("Col | Name      | Visits    | Share   | White Win Rate | Status\n");
    printf("----+-----------+-----------+---------+----------------+--------------------\n");
    int best_opening_col = -1;
    uint32_t max_visits = 0;
    for (int c = 0; c < W; c++) {
        MCTSNode *child = root_node->children[c];
        if (child && child->visits > 0) {
            double win_rate = ((child->white_value / (double)child->visits) + 1.0) / 2.0 * 100.0;
            double share = (double)child->visits / (double)root_node->visits * 100.0;
            const char *label = (c == 4) ? "Center 4" : (c == 3 || c == 5) ? "Flank In" : (c == 2 || c == 6) ? "Mid Flk" : "Outer";
            printf(" %d  | %-9s | %9u | %6.2f%% | %12.2f%% | %s\n",
                   c, label, child->visits, share, win_rate,
                   (win_rate >= 70.0) ? "CRUSHING ADVANTAGE" : (win_rate >= 55.0) ? "FAVORED" : "EQUAL/WEAK");
            if (child->visits > max_visits) {
                max_visits = child->visits;
                best_opening_col = c;
            }
        }
    }
    printf("------------------------------------------------------------------------\n");
    printf(">> MCTS Verdict: Best Opening Move is Column %d (Visits: %u / %.1f%%)\n\n",
           best_opening_col, max_visits, (double)max_visits / root_node->visits * 100.0);

    // EXPERIMENT 2: Black's Optimal Defensive Reply Against Center Column 4
    printf("------------------------------------------------------------------------\n");
    printf("  EXPERIMENT 2: Black's Defensive Replies to Opening (4, 0)\n");
    printf("------------------------------------------------------------------------\n");

    Board after_p1;
    init_board(&after_p1);
    play_move(&after_p1, 4); // White plays Center Column 4

    printf("Simulating 250,000 MCTS rollouts after Ply 1: White plays (4, 0)...\n");
    start = clock();
    mcts_search(&after_p1, 250000, 1.414, global_cell_visits);
    end = clock();
    elapsed = (double)(end - start) / CLOCKS_PER_SEC;
    printf("Completed in %.2f seconds (%.0f iterations/sec)!\n\n", elapsed, 250000 / elapsed);

    MCTSNode *p2_root = &node_pool[0];
    printf("Col | Name      | Visits    | Share   | Black Survival Rate | Evaluation\n");
    printf("----+-----------+-----------+---------+---------------------+--------------------\n");
    int best_p2_col = -1;
    uint32_t max_p2_visits = 0;
    for (int c = 0; c < W; c++) {
        MCTSNode *child = p2_root->children[c];
        if (child && child->visits > 0) {
            // child->white_value is from White's perspective; Black's win/draw rate is inverted
            double white_wr = ((child->white_value / (double)child->visits) + 1.0) / 2.0;
            double black_survival = (1.0 - white_wr) * 100.0;
            double share = (double)child->visits / (double)p2_root->visits * 100.0;
            const char *label = (c == 4) ? "Center 4" : (c == 3 || c == 5) ? "Adjacent" : "Divergent";
            printf(" %d  | %-9s | %9u | %6.2f%% | %17.2f%% | %s\n",
                   c, label, child->visits, share, black_survival,
                   (black_survival < 20.0) ? "COLLAPSE" : (black_survival < 40.0) ? "SEVERE DEFICIT" : "HOLDABLE");
            if (child->visits > max_p2_visits) {
                max_p2_visits = child->visits;
                best_p2_col = c;
            }
        }
    }
    printf("------------------------------------------------------------------------\n");
    printf(">> MCTS Verdict: Black's Primary Defensive Counter is Column %d\n\n", best_p2_col);

    // EXPERIMENT 3: Self-Play Tournament (MCTS vs MCTS)
    printf("------------------------------------------------------------------------\n");
    printf("  EXPERIMENT 3: Autonomous MCTS Self-Play Tournament (50 Games)\n");
    printf("------------------------------------------------------------------------\n");
    int white_wins = 0, black_wins = 0, draws = 0;
    int iters_per_move = 15000;
    printf("Running 50 games at %d iterations per ply...\n", iters_per_move);

    int sample_game_plies[TOTAL_CELLS];
    int sample_game_length = 0;

    for (int g = 1; g <= 50; g++) {
        Board game;
        init_board(&game);
        while (game.ply < TOTAL_CELLS) {
            mcts_search(&game, iters_per_move, 1.414, NULL);
            MCTSNode *r = &node_pool[0];
            // Pick most visited child
            int best_c = -1;
            uint32_t best_v = 0;
            for (int c = 0; c < W; c++) {
                if (r->children[c] && r->children[c]->visits > best_v) {
                    best_v = r->children[c]->visits;
                    best_c = c;
                }
            }
            if (best_c == -1) break; // No legal move
            if (g == 1) sample_game_plies[sample_game_length++] = best_c;
            play_move(&game, best_c);

            // Check win
            uint64_t last_m = ((game.ply - 1) & 1) == 0 ? game.white : game.black;
            if (has_won(last_m)) {
                if (((game.ply - 1) & 1) == 0) white_wins++;
                else black_wins++;
                break;
            }
        }
        if (game.ply >= TOTAL_CELLS && !has_won(game.white) && !has_won(game.black)) {
            draws++;
        }
        if (g % 10 == 0) {
            printf("  Games 1-%2d: White Wins: %2d (%.1f%%) | Black Wins: %2d (%.1f%%) | Draws: %2d (%.1f%%)\n",
                   g, white_wins, (double)white_wins/g*100.0,
                   black_wins, (double)black_wins/g*100.0,
                   draws, (double)draws/g*100.0);
        }
    }

    printf("\n>> Tournament Results: White: %d (%.1f%%) | Black: %d (%.1f%%) | Draws: %d (%.1f%%)\n",
           white_wins, (double)white_wins/50.0*100.0,
           black_wins, (double)black_wins/50.0*100.0,
           draws, (double)draws/50.0*100.0);

    printf("\nSample Game 1 Move Sequence (Plies: %d):\n", sample_game_length);
    for (int p = 0; p < sample_game_length; p++) {
        printf("Ply %2d (%s): Col %d\n", p + 1, (p & 1) == 0 ? "White" : "Black", sample_game_plies[p]);
    }

    // Print Heatmap
    print_heatmap(global_cell_visits);

    return 0;
}
