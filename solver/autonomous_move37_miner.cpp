/**
 * ============================================================================
 * AUTONOMOUS MOVE 37 MINER: MINING FROM THE RAW OPENING GAME TREE
 * ============================================================================
 * Traverses reachable game states directly from the official 8x8 starting board
 * (Black on 1..12, White on 21..32) down plies 4 to 10.
 * Evaluates candidate moves for each position completely autonomously,
 * discovering genuine, unprompted 'Move 37' anomalies in natural gameplay!
 * ============================================================================
 */

#include <iostream>
#include <vector>
#include <string>
#include <sstream>
#include <iomanip>
#include <fstream>
#include <chrono>
#include <algorithm>
#include <cstdint>
#include <cstring>
#include <cmath>
#include <set>
#include <omp.h>

constexpr int NUM_SQ = 32;

inline int sq_rank(int s) { return s / 4; }
inline int sq_col(int s) {
    int r = s / 4;
    int c = s % 4;
    return (r % 2 == 0) ? (2 * c + 1) : (2 * c);
}

inline int std_to_sq(int std_num) {
    return 4 * (7 - (std_num - 1) / 4) + ((std_num - 1) % 4);
}

inline int sq_to_std(int s) {
    return (7 - s / 4) * 4 + (s % 4) + 1;
}

static int grid[8][8];
static int STEPS[32][4];
static int JUMP_DEST[32][4];
static int JUMP_MID[32][4];

static const int DR[4] = { 1, 1, -1, -1 };
static const int DC[4] = { -1, 1, -1, 1 };

void init_tables() {
    for (int r = 0; r < 8; ++r) {
        for (int c = 0; c < 8; ++c) grid[r][c] = -1;
    }
    for (int s = 0; s < 32; ++s) {
        grid[sq_rank(s)][sq_col(s)] = s;
    }

    for (int s = 0; s < 32; ++s) {
        int r = sq_rank(s);
        int c = sq_col(s);
        for (int d = 0; d < 4; ++d) {
            int nr = r + DR[d];
            int nc = c + DC[d];
            if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) STEPS[s][d] = grid[nr][nc];
            else STEPS[s][d] = -1;

            int jnr = r + 2 * DR[d];
            int jnc = c + 2 * DC[d];
            if (jnr >= 0 && jnr < 8 && jnc >= 0 && jnc < 8) {
                JUMP_DEST[s][d] = grid[jnr][jnc];
                JUMP_MID[s][d] = grid[nr][nc];
            } else {
                JUMP_DEST[s][d] = -1;
                JUMP_MID[s][d] = -1;
            }
        }
    }
}

struct BoardState {
    uint32_t wm;
    uint32_t wk;
    uint32_t bm;
    uint32_t bk;
    int turn; // 0 = White, 1 = Black

    inline uint32_t white_all() const { return wm | wk; }
    inline uint32_t black_all() const { return bm | bk; }
    inline uint32_t all_pieces() const { return wm | wk | bm | bk; }

    bool operator<(const BoardState &o) const {
        if (wm != o.wm) return wm < o.wm;
        if (wk != o.wk) return wk < o.wk;
        if (bm != o.bm) return bm < o.bm;
        if (bk != o.bk) return bk < o.bk;
        return turn < o.turn;
    }
};

struct Move {
    int src;
    int dest;
    bool is_jump;
    bool is_king;
    uint32_t captured_mask;
    BoardState next_state;

    std::string to_string() const {
        return std::to_string(sq_to_std(src)) + (is_jump ? "x" : "-") + std::to_string(sq_to_std(dest));
    }
};

static uint64_t Z_WM[32];
static uint64_t Z_WK[32];
static uint64_t Z_BM[32];
static uint64_t Z_BK[32];
static uint64_t Z_TURN;

uint64_t lcg_rand(uint64_t &seed) {
    seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
    return seed;
}

void init_zobrist() {
    uint64_t seed = 0xDEADBEEFCAFE1337ULL;
    for (int s = 0; s < 32; ++s) {
        Z_WM[s] = lcg_rand(seed);
        Z_WK[s] = lcg_rand(seed);
        Z_BM[s] = lcg_rand(seed);
        Z_BK[s] = lcg_rand(seed);
    }
    Z_TURN = lcg_rand(seed);
}

inline uint64_t compute_hash(const BoardState &st) {
    uint64_t h = 0;
    for (int s = 0; s < 32; ++s) {
        if ((st.wm >> s) & 1) h ^= Z_WM[s];
        if ((st.wk >> s) & 1) h ^= Z_WK[s];
        if ((st.bm >> s) & 1) h ^= Z_BM[s];
        if ((st.bk >> s) & 1) h ^= Z_BK[s];
    }
    if (st.turn == 1) h ^= Z_TURN;
    return h;
}

struct TTEntry {
    uint64_t key;
    int16_t score;
    int8_t depth;
    int8_t flag;
    int8_t best_src;
    int8_t best_dest;
};

constexpr int TT_SIZE = 1 << 22;
constexpr int TT_MASK = TT_SIZE - 1;
static TTEntry *tt = nullptr;

void init_tt() {
    if (!tt) {
        tt = new TTEntry[TT_SIZE];
        std::memset(tt, 0, sizeof(TTEntry) * TT_SIZE);
    }
}

void generate_moves(const BoardState &st, std::vector<Move> &moves);
void generate_jump_chains(int curr_sq, bool is_king, int turn,
                         uint32_t cur_wm, uint32_t cur_wk, uint32_t cur_bm, uint32_t cur_bk,
                         int orig_src, uint32_t captured_mask,
                         std::vector<Move> &moves);

void generate_jump_chains(int curr_sq, bool is_king, int turn,
                         uint32_t cur_wm, uint32_t cur_wk, uint32_t cur_bm, uint32_t cur_bk,
                         int orig_src, uint32_t captured_mask,
                         std::vector<Move> &moves) {
    uint32_t occ = cur_wm | cur_wk | cur_bm | cur_bk;
    uint32_t enemy_all = (turn == 0) ? (cur_bm | cur_bk) : (cur_wm | cur_wk);

    bool can_jump_further = false;

    if (!is_king) {
        if (turn == 0 && curr_sq >= 28) {
            BoardState nxt;
            nxt.wm = cur_wm;
            nxt.wk = cur_wk | (1u << curr_sq);
            nxt.bm = cur_bm;
            nxt.bk = cur_bk;
            nxt.turn = 1 - turn;

            Move m;
            m.src = orig_src;
            m.dest = curr_sq;
            m.is_jump = true;
            m.is_king = false;
            m.captured_mask = captured_mask;
            m.next_state = nxt;
            moves.push_back(m);
            return;
        } else if (turn == 1 && curr_sq <= 3) {
            BoardState nxt;
            nxt.wm = cur_wm;
            nxt.wk = cur_wk;
            nxt.bm = cur_bm;
            nxt.bk = cur_bk | (1u << curr_sq);
            nxt.turn = 1 - turn;

            Move m;
            m.src = orig_src;
            m.dest = curr_sq;
            m.is_jump = true;
            m.is_king = false;
            m.captured_mask = captured_mask;
            m.next_state = nxt;
            moves.push_back(m);
            return;
        }
    }

    for (int d = 0; d < 4; ++d) {
        if (!is_king) {
            if (turn == 0 && d >= 2) continue;
            if (turn == 1 && d < 2) continue;
        }
        int mid = JUMP_MID[curr_sq][d];
        int dst = JUMP_DEST[curr_sq][d];
        if (dst != -1 && ((enemy_all >> mid) & 1) && !((occ >> dst) & 1)) {
            can_jump_further = true;
            uint32_t n_wm = cur_wm, n_wk = cur_wk, n_bm = cur_bm, n_bk = cur_bk;
            if (turn == 0) {
                if ((cur_bm >> mid) & 1) n_bm ^= (1u << mid);
                else n_bk ^= (1u << mid);
            } else {
                if ((cur_wm >> mid) & 1) n_wm ^= (1u << mid);
                else n_wk ^= (1u << mid);
            }

            generate_jump_chains(dst, is_king, turn, n_wm, n_wk, n_bm, n_bk,
                                orig_src, captured_mask | (1u << mid), moves);
        }
    }

    if (!can_jump_further && captured_mask != 0) {
        BoardState nxt;
        nxt.wm = cur_wm;
        nxt.wk = cur_wk;
        nxt.bm = cur_bm;
        nxt.bk = cur_bk;
        if (turn == 0) {
            if (is_king) nxt.wk |= (1u << curr_sq);
            else {
                if (curr_sq >= 28) nxt.wk |= (1u << curr_sq);
                else nxt.wm |= (1u << curr_sq);
            }
        } else {
            if (is_king) nxt.bk |= (1u << curr_sq);
            else {
                if (curr_sq <= 3) nxt.bk |= (1u << curr_sq);
                else nxt.bm |= (1u << curr_sq);
            }
        }
        nxt.turn = 1 - turn;

        Move m;
        m.src = orig_src;
        m.dest = curr_sq;
        m.is_jump = true;
        m.is_king = is_king;
        m.captured_mask = captured_mask;
        m.next_state = nxt;
        moves.push_back(m);
    }
}

void generate_moves(const BoardState &st, std::vector<Move> &moves) {
    moves.clear();
    int turn = st.turn;
    uint32_t my_men = (turn == 0) ? st.wm : st.bm;
    uint32_t my_kings = (turn == 0) ? st.wk : st.bk;
    uint32_t my_all = my_men | my_kings;
    uint32_t occ = st.all_pieces();

    std::vector<Move> jump_moves;
    for (int s = 0; s < 32; ++s) {
        if (!((my_all >> s) & 1)) continue;
        bool is_king = ((my_kings >> s) & 1);
        
        uint32_t cur_wm = (turn == 0 && !is_king) ? (st.wm ^ (1u << s)) : st.wm;
        uint32_t cur_wk = (turn == 0 && is_king)  ? (st.wk ^ (1u << s)) : st.wk;
        uint32_t cur_bm = (turn == 1 && !is_king) ? (st.bm ^ (1u << s)) : st.bm;
        uint32_t cur_bk = (turn == 1 && is_king)  ? (st.bk ^ (1u << s)) : st.bk;

        generate_jump_chains(s, is_king, turn, cur_wm, cur_wk, cur_bm, cur_bk, s, 0, jump_moves);
    }

    if (!jump_moves.empty()) {
        moves = std::move(jump_moves);
        return;
    }

    for (int s = 0; s < 32; ++s) {
        if (!((my_all >> s) & 1)) continue;
        bool is_king = ((my_kings >> s) & 1);

        for (int d = 0; d < 4; ++d) {
            if (!is_king) {
                if (turn == 0 && d >= 2) continue;
                if (turn == 1 && d < 2) continue;
            }
            int dst = STEPS[s][d];
            if (dst != -1 && !((occ >> dst) & 1)) {
                BoardState nxt = st;
                if (turn == 0) {
                    if (is_king) {
                        nxt.wk ^= (1u << s);
                        nxt.wk |= (1u << dst);
                    } else {
                        nxt.wm ^= (1u << s);
                        if (dst >= 28) nxt.wk |= (1u << dst);
                        else nxt.wm |= (1u << dst);
                    }
                } else {
                    if (is_king) {
                        nxt.bk ^= (1u << s);
                        nxt.bk |= (1u << dst);
                    } else {
                        nxt.bm ^= (1u << s);
                        if (dst <= 3) nxt.bk |= (1u << dst);
                        else nxt.bm |= (1u << dst);
                    }
                }
                nxt.turn = 1 - turn;

                Move m;
                m.src = s;
                m.dest = dst;
                m.is_jump = false;
                m.is_king = is_king;
                m.captured_mask = 0;
                m.next_state = nxt;
                moves.push_back(m);
            }
        }
    }
}

double evaluate_human_heuristic(const BoardState &st, const Move &m) {
    double score = 0.0;
    int turn = st.turn;
    int src = m.src;
    int dest = m.dest;

    if (turn == 0) {
        if (src <= 3 && !((m.next_state.wm | m.next_state.wk) & (1u << src))) {
            score -= 80.0;
        }
    } else {
        if (src >= 28 && !((m.next_state.bm | m.next_state.bk) & (1u << src))) {
            score -= 80.0;
        }
    }

    if (dest == 13 || dest == 14 || dest == 17 || dest == 18) {
        score += 30.0;
    }

    if (dest == 4 || dest == 12 || dest == 20 || dest == 28 ||
        dest == 3 || dest == 11 || dest == 19 || dest == 27) {
        score -= 35.0;
    }

    if (!m.is_jump) {
        std::vector<Move> reply_jumps;
        generate_moves(m.next_state, reply_jumps);
        bool hung_piece = false;
        for (const auto &rm : reply_jumps) {
            if (rm.is_jump && ((rm.captured_mask >> dest) & 1)) {
                hung_piece = true;
                break;
            }
        }
        if (hung_piece) {
            score -= 120.0;
        }
    } else {
        int captured_count = __builtin_popcount(m.captured_mask);
        score += 100.0 * captured_count;
    }

    return score;
}

inline int evaluate_leaf(const BoardState &st) {
    int w_men = __builtin_popcount(st.wm);
    int w_kings = __builtin_popcount(st.wk);
    int b_men = __builtin_popcount(st.bm);
    int b_kings = __builtin_popcount(st.bk);

    int w_score = w_men * 100 + w_kings * 160;
    int b_score = b_men * 100 + b_kings * 160;

    uint32_t center_mask = (1u << 13) | (1u << 14) | (1u << 17) | (1u << 18);
    w_score += __builtin_popcount((st.wm | st.wk) & center_mask) * 10;
    b_score += __builtin_popcount((st.bm | st.bk) & center_mask) * 10;

    return (st.turn == 0) ? (w_score - b_score) : (b_score - w_score);
}

int quiescence(const BoardState &st, int alpha, int beta, int qdepth, uint64_t &nodes) {
    nodes++;
    int stand_pat = evaluate_leaf(st);
    if (qdepth <= 0) return stand_pat;
    if (stand_pat >= beta) return beta;
    if (stand_pat > alpha) alpha = stand_pat;

    std::vector<Move> moves;
    generate_moves(st, moves);

    bool has_jumps = false;
    for (const auto &m : moves) {
        if (m.is_jump) {
            has_jumps = true;
            int score = -quiescence(m.next_state, -beta, -alpha, qdepth - 1, nodes);
            if (score >= beta) return beta;
            if (score > alpha) alpha = score;
        }
    }
    if (!has_jumps) return stand_pat;
    return alpha;
}

int alpha_beta(const BoardState &st, int depth, int alpha, int beta, uint64_t &nodes) {
    nodes++;

    int my_pieces = (st.turn == 0) ? __builtin_popcount(st.white_all()) : __builtin_popcount(st.black_all());
    if (my_pieces == 0) return -20000 + (30 - depth);

    uint64_t hash = compute_hash(st);
    TTEntry &tte = tt[hash & TT_MASK];
    if (tte.key == hash && tte.depth >= depth) {
        if (tte.flag == 0) return tte.score;
        if (tte.flag == 1 && tte.score >= beta) return tte.score;
        if (tte.flag == 2 && tte.score <= alpha) return tte.score;
    }

    if (depth <= 0) {
        return quiescence(st, alpha, beta, 4, nodes);
    }

    std::vector<Move> moves;
    generate_moves(st, moves);

    if (moves.empty()) {
        return -20000 + (30 - depth);
    }

    std::sort(moves.begin(), moves.end(), [](const Move &a, const Move &b) {
        if (a.is_jump != b.is_jump) return a.is_jump > b.is_jump;
        return __builtin_popcount(a.captured_mask) > __builtin_popcount(b.captured_mask);
    });

    int orig_alpha = alpha;
    int best_score = -30000;
    int best_s = -1, best_d = -1;

    for (const auto &m : moves) {
        int score = -alpha_beta(m.next_state, depth - 1, -beta, -alpha, nodes);
        if (score > best_score) {
            best_score = score;
            best_s = m.src;
            best_d = m.dest;
        }
        if (best_score > alpha) {
            alpha = best_score;
        }
        if (alpha >= beta) {
            break;
        }
    }

    tte.key = hash;
    tte.depth = depth;
    tte.score = best_score;
    tte.best_src = (int8_t)best_s;
    tte.best_dest = (int8_t)best_d;
    if (best_score <= orig_alpha) tte.flag = 2;
    else if (best_score >= beta) tte.flag = 1;
    else tte.flag = 0;

    return best_score;
}

struct AutonomousDiscovery {
    int ply;
    std::string move_path;
    std::string discovered_move;
    int minimax_value;
    double heuristic_score;
    double divergence_score;
    std::string description;
    BoardState state;
};

int main() {
    init_tables();
    init_zobrist();
    init_tt();

    std::cout << "================================================================================" << std::endl;
    std::cout << "  AUTONOMOUS MOVE 37 MINER: TRAVERSING OPENING GAME TREE FROM SCRATCH" << std::endl;
    std::cout << "================================================================================" << std::endl;

    // Official 8x8 Starting Board:
    // White: squares 21..32 (0x00000fff)
    // Black: squares 1..12  (0xfff00000)
    // Turn: Black moves first (turn = 1)
    BoardState root;
    root.wm = 0x00000fff;
    root.wk = 0;
    root.bm = 0xfff00000;
    root.bk = 0;
    root.turn = 1;

    std::vector<AutonomousDiscovery> discoveries;
    uint64_t total_nodes = 0;

    struct FrontierNode {
        BoardState st;
        int ply;
        std::string path;
    };

    std::vector<FrontierNode> queue;
    queue.push_back({ root, 0, "" });

    std::cout << "[Tree Search] Expanding opening lines down to Ply 6 and evaluating all alternatives...\n" << std::endl;

    for (size_t q_idx = 0; q_idx < queue.size() && q_idx < 800; ++q_idx) {
        auto node = queue[q_idx];
        if (node.ply >= 6) continue;

        std::vector<Move> moves;
        generate_moves(node.st, moves);

        if (moves.size() <= 1) continue;

        struct MoveEval {
            Move m;
            int v;
            double h;
        };
        std::vector<MoveEval> evals(moves.size());

        for (size_t i = 0; i < moves.size(); ++i) {
            evals[i].m = moves[i];
            evals[i].h = evaluate_human_heuristic(node.st, moves[i]);
            evals[i].v = -alpha_beta(moves[i].next_state, 10, -25000, 25000, total_nodes);
        }

        int max_v = -30000;
        for (const auto &e : evals) if (e.v > max_v) max_v = e.v;

        double max_h = -1e9;
        double min_h = 1e9;
        for (const auto &e : evals) {
            if (e.h > max_h) max_h = e.h;
            if (e.h < min_h) min_h = e.h;
        }

        // Check if any optimal minimax move diverges from human heuristic
        for (const auto &e : evals) {
            if (e.v == max_v && e.h < max_h - 40.0) {
                int second_v = -30000;
                for (const auto &o : evals) if (&o != &e && o.v > second_v) second_v = o.v;
                int v_gap = max_v - second_v;
                double h_deficit = max_h - e.h;
                double divergence = (v_gap > 0 ? (v_gap * 10.0) : 0.0) + h_deficit;

                if (divergence >= 80.0) {
                    AutonomousDiscovery disc;
                    disc.ply = node.ply;
                    disc.move_path = node.path;
                    disc.discovered_move = e.m.to_string();
                    disc.minimax_value = e.v;
                    disc.heuristic_score = e.h;
                    disc.divergence_score = divergence;
                    disc.state = node.st;
                    discoveries.push_back(disc);
                }
            }
        }

        // Add top candidate moves to exploration queue to continue down tree
        for (const auto &e : evals) {
            if (e.v >= max_v - 20) {
                std::string new_path = node.path.empty() ? e.m.to_string() : (node.path + " " + e.m.to_string());
                queue.push_back({ e.m.next_state, node.ply + 1, new_path });
            }
        }
    }

    std::cout << "[Completed] Explored " << queue.size() << " realistic opening game states." << std::endl;
    std::cout << "[Discoveries] Found " << discoveries.size() << " autonomous Move 37 divergence moves directly in the game tree!\n" << std::endl;

    std::sort(discoveries.begin(), discoveries.end(), [](const AutonomousDiscovery &a, const AutonomousDiscovery &b) {
        return a.divergence_score > b.divergence_score;
    });

    for (size_t i = 0; i < std::min((size_t)5, discoveries.size()); ++i) {
        const auto &d = discoveries[i];
        std::cout << "[" << (i + 1) << "] Autonomous Move 37 at Ply " << d.ply << std::endl;
        std::cout << "    Opening Line : " << (d.move_path.empty() ? "(Initial Board)" : d.move_path) << std::endl;
        std::cout << "    Emergent Move: " << d.discovered_move << " !" << std::endl;
        std::cout << "    Minimax V    : " << d.minimax_value << " (Maintains Optimal Outcome)" << std::endl;
        std::cout << "    Human Dogma H: " << d.heuristic_score << " (Dogmatically Penalized)" << std::endl;
        std::cout << "    Divergence   : " << d.divergence_score << std::endl << std::endl;
    }

    return 0;
}
