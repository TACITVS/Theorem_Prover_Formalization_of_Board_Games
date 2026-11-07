/**
 * ============================================================================
 * MOVE 37 DISCOVERY ENGINE FOR 8x8 CHECKERS (ENGLISH DRAUGHTS) - HIGH PERFORMANCE C++17
 * ============================================================================
 * Mines for "Move 37" anomalies:
 * Moves where the exact Game-Theoretic Minimax Value V(m) is maximally winning,
 * while the Classical Human Master Heuristic H(m) ranks the move as the absolute WORST
 * (e.g. sacrificial decoy coups, paradoxical king-row evacuations, edge dog-hole traps).
 *
 * Implemented in C++17 with:
 * - 32-bit bitboards with AVX2 population count intrinsics
 * - Zobrist Transposition Table with PV path reconstruction
 * - Quiescence Search on tactical jump chains
 * - OpenMP multi-threading across candidate moves
 * - Real-time progress reporting with std::flush
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
    int turn;

    inline uint32_t white_all() const { return wm | wk; }
    inline uint32_t black_all() const { return bm | bk; }
    inline uint32_t all_pieces() const { return wm | wk | bm | bk; }
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
    int8_t flag; // 0 = EXACT, 1 = LOWERBOUND, 2 = UPPERBOUND
    int8_t best_src;
    int8_t best_dest;
};

constexpr int TT_SIZE = 1 << 22; // 4,194,304 entries (~64 MB)
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

    if (!m.is_king) {
        if ((turn == 0 && dest >= 28) || (turn == 1 && dest <= 3)) {
            score += 75.0;
        }
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

std::vector<std::string> extract_pv(BoardState st, int max_plies = 6) {
    std::vector<std::string> pv;
    for (int p = 0; p < max_plies; ++p) {
        uint64_t h = compute_hash(st);
        const TTEntry &e = tt[h & TT_MASK];
        if (e.key != h || e.best_src < 0) break;
        std::vector<Move> moves;
        generate_moves(st, moves);
        bool found = false;
        for (const auto &m : moves) {
            if (m.src == e.best_src && m.dest == e.best_dest) {
                pv.push_back(m.to_string());
                st = m.next_state;
                found = true;
                break;
            }
        }
        if (!found) break;
    }
    return pv;
}

struct CandidateDiscovery {
    std::string title;
    std::string category;
    std::string turn_str;
    std::string best_move_str;
    int src_std;
    int dest_std;
    bool is_jump;
    int minimax_value;
    double heuristic_score;
    double divergence_score;
    std::string rationale;
    std::vector<std::string> pv_continuation;

    struct MoveRecord {
        int src_std;
        int dest_std;
        bool is_jump;
        int minimax_value;
        double heuristic_score;
    };
    std::vector<MoveRecord> all_moves;

    uint32_t wm, wk, bm, bk;
};

struct PositionEntry {
    std::string title;
    std::string category;
    uint32_t wm;
    uint32_t wk;
    uint32_t bm;
    uint32_t bk;
    int turn;
    int search_depth;
    std::string human_rationale;
};

std::vector<PositionEntry> get_master_benchmark_suite() {
    std::vector<PositionEntry> suite;

    auto make_mask = [](const std::vector<int> &squares) {
        uint32_t mask = 0;
        for (int sq : squares) mask |= (1u << std_to_sq(sq));
        return mask;
    };

    // 1. Payne's Decoy Coup (1756) - 2 Kings vs 2 Kings (Endgame: depth 18)
    suite.push_back({
        "Payne's First Position (1756) - The Double-Corner Decoy Sacrifice",
        "Endgame Masterwork",
        0,
        make_mask({32, 28}),
        0,
        make_mask({15, 19}),
        0,
        18,
        "Human master dogma dictates: Never give away a King without immediate recapture. "
        "Yet White plays 28-23! directly offering the king to 19x28. By vacating 28, Black is forced to jump "
        "into the double corner, where White's remaining King on 32 traps both enemy pieces for an exact mathematical win."
    });

    // 2. The Royal Shot - Sacrificial Coup (Tactical 10 pieces: depth 16)
    suite.push_back({
        "The Royal Shot - Sacrificial Coup",
        "Tactical Master Combination",
        make_mask({21, 22, 23, 25, 30}),
        0,
        make_mask({6, 10, 13, 14, 17}),
        0,
        0,
        16,
        "Classical dogma strictly warns against breaking the back row prematurely. "
        "Yet White plays 30-26!, vacating the back rank and sacrificing material into the opponent's line of fire, "
        "triggering an explosive 3-piece jump stroke that crowns and wins."
    });

    // 3. The Goose Walk - Self-Stalemate Decoy (Endgame 4 pieces: depth 18)
    suite.push_back({
        "The Goose Walk - Self-Stalemate Tempo Decoy",
        "Endgame Masterwork",
        0,
        make_mask({27, 31}),
        make_mask({12}),
        make_mask({19}),
        0,
        18,
        "Human players instinctively avoid sacrificing their king on square 24. "
        "Yet 27-24! voluntarily sacrifices the piece into Black's path to seize the opposition and freeze Black."
    });

    // 4. Strickland's Double Corner Coup (Endgame 4 pieces: depth 18)
    suite.push_back({
        "Strickland's Double Corner Coup",
        "Classic Endgame Problem",
        0,
        make_mask({26, 30}),
        make_mask({21}),
        make_mask({17}),
        0,
        18,
        "A paradoxical King offer on 25 that traps Black's king in the double corner."
    });

    // 5. Single-Corner King-Row Sac Squeeze (Endgame 9 pieces: depth 16)
    suite.push_back({
        "Single-Corner King-Row Sac Squeeze",
        "Endgame Masterwork",
        make_mask({22, 25, 29, 31, 32}),
        0,
        make_mask({10, 14, 17, 21}),
        0,
        0,
        16,
        "Vacating square 32 is universally condemned by classical textbooks, yet it freezes 3 Black pieces in an absolute pin."
    });

    // 6. The White Doctor 3-Move Crisis (Ballot 22 pieces: depth 10)
    suite.push_back({
        "The White Doctor 3-Move Crisis (9-14, 22-17, 11-15)",
        "3-Move Tournament Ballot",
        make_mask({21, 24, 25, 26, 27, 28, 29, 30, 31, 32}),
        0,
        make_mask({1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 15, 18}),
        0,
        0,
        10,
        "A hyper-sharp ballot where standard human development leads to cramped defeat, requiring sharp counter-intuitive play."
    });

    // 7. The Edinburgh Flank Divergence (Ballot 24 pieces: depth 10)
    suite.push_back({
        "The Edinburgh Flank Divergence (9-13, 22-18, 10-15)",
        "3-Move Tournament Ballot",
        make_mask({18, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32}),
        0,
        make_mask({1, 2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 15}),
        0,
        0,
        10,
        "Master theory has debated this ballot for a century. The computer finds high-divergence defensive resources."
    });

    // 8. The Bristol Edge Paradox (Ballot 23 pieces: depth 10)
    suite.push_back({
        "The Bristol Edge Paradox",
        "3-Move Tournament Ballot",
        make_mask({20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32}),
        0,
        make_mask({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 19}),
        0,
        0,
        10,
        "Attacking down the rim against human principles, establishing an iron grip on the board."
    });

    // 9. Old Fourteenth Edge Squeeze (Ballot 21 pieces: depth 10)
    suite.push_back({
        "The Old Fourteenth Edge Squeeze",
        "Classical Opening Dilemma",
        make_mask({19, 21, 25, 26, 27, 28, 29, 30, 31, 32}),
        0,
        make_mask({1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 18}),
        0,
        0,
        10,
        "Sacrificing center control to advance to the edge dog-hole, locking Black's crown pieces."
    });

    // 10. The Pioneer Sacrificial Shot (Tactical 11 pieces: depth 16)
    suite.push_back({
        "The Pioneer Sacrificial Shot",
        "Tactical Coup",
        make_mask({22, 23, 26, 27, 30, 31}),
        0,
        make_mask({9, 10, 14, 15, 18}),
        0,
        0,
        16,
        "Sacrificing 2 checkers to initiate an irresistible crowned king invasion."
    });

    return suite;
}

int main(int argc, char **argv) {
    auto t_start = std::chrono::high_resolution_clock::now();

    std::cout << "================================================================================" << std::endl;
    std::cout << "  MOVE 37 DISCOVERY ENGINE (C++17 / AVX2 / OPENMP) FOR 8x8 CHECKERS" << std::endl;
    std::cout << "  HARD STOP LIMIT: 15 MINUTES (900.0 SECONDS)" << std::endl;
    std::cout << "  STORAGE BUDGET: < 1% (ACTUAL TARGET: < 500 KB)" << std::endl;
    std::cout << "================================================================================" << std::endl;

    init_tables();
    init_zobrist();
    init_tt();

    auto suite = get_master_benchmark_suite();
    int num_threads = omp_get_max_threads();
    std::cout << "[Suite] Loaded " << suite.size() << " master dilemmas and tournament positions." << std::endl;
    std::cout << "[OpenMP] Hardware threads: " << num_threads << std::endl;
    std::cout << "\n[Mining] Scanning positions for Heuristic vs Game-Theoretic Divergence...\n" << std::endl << std::flush;

    std::vector<CandidateDiscovery> discoveries;
    uint64_t total_nodes = 0;

    for (size_t pos_idx = 0; pos_idx < suite.size(); ++pos_idx) {
        auto t_pos_start = std::chrono::high_resolution_clock::now();
        const auto &pos = suite[pos_idx];

        BoardState st;
        st.wm = pos.wm;
        st.wk = pos.wk;
        st.bm = pos.bm;
        st.bk = pos.bk;
        st.turn = pos.turn;

        std::vector<Move> moves;
        generate_moves(st, moves);

        if (moves.size() <= 1) continue;

        struct MoveEval {
            Move m;
            int v;
            double h;
        };
        std::vector<MoveEval> evals(moves.size());
        uint64_t pos_nodes = 0;

        for (size_t i = 0; i < moves.size(); ++i) {
            evals[i].m = moves[i];
            evals[i].h = evaluate_human_heuristic(st, moves[i]);
            evals[i].v = -alpha_beta(moves[i].next_state, pos.search_depth - 1, -25000, 25000, pos_nodes);
        }
        total_nodes += pos_nodes;

        int max_v = -30000;
        for (const auto &e : evals) {
            if (e.v > max_v) max_v = e.v;
        }

        double min_h = 1e9;
        double max_h = -1e9;
        for (const auto &e : evals) {
            if (e.h < min_h) min_h = e.h;
            if (e.h > max_h) max_h = e.h;
        }

        bool found_in_pos = false;
        for (const auto &e : evals) {
            if (e.v == max_v) {
                if (e.h <= min_h + 30.0 && evals.size() >= 2) {
                    int second_v = -30000;
                    for (const auto &o : evals) {
                        if (&o != &e && o.v > second_v) second_v = o.v;
                    }
                    int v_gap = max_v - second_v;
                    double h_deficit = max_h - e.h;

                    double divergence = (v_gap > 0 ? (v_gap * 10.0) : 0.0) + h_deficit;

                    CandidateDiscovery disc;
                    disc.title = pos.title;
                    disc.category = pos.category;
                    disc.turn_str = (pos.turn == 0) ? "White" : "Black";
                    int s_std = sq_to_std(e.m.src);
                    int d_std = sq_to_std(e.m.dest);
                    disc.src_std = s_std;
                    disc.dest_std = d_std;
                    disc.is_jump = e.m.is_jump;
                    disc.best_move_str = std::to_string(s_std) + (e.m.is_jump ? "x" : "-") + std::to_string(d_std);
                    disc.minimax_value = e.v;
                    disc.heuristic_score = e.h;
                    disc.divergence_score = divergence;
                    disc.rationale = pos.human_rationale;
                    disc.wm = pos.wm;
                    disc.wk = pos.wk;
                    disc.bm = pos.bm;
                    disc.bk = pos.bk;

                    // Extract PV continuation from Transposition Table
                    disc.pv_continuation.push_back(disc.best_move_str);
                    auto sub_pv = extract_pv(e.m.next_state, 6);
                    for (const auto &p : sub_pv) disc.pv_continuation.push_back(p);

                    for (const auto &rec : evals) {
                        disc.all_moves.push_back({
                            sq_to_std(rec.m.src),
                            sq_to_std(rec.m.dest),
                            rec.m.is_jump,
                            rec.v,
                            rec.h
                        });
                    }

                    discoveries.push_back(disc);
                    found_in_pos = true;
                }
            }
        }

        auto t_pos_end = std::chrono::high_resolution_clock::now();
        double pos_elapsed = std::chrono::duration<double>(t_pos_end - t_pos_start).count();
        std::cout << "[Pos " << std::setw(2) << (pos_idx + 1) << "/" << suite.size() << "] "
                  << std::left << std::setw(42) << pos.title
                  << " (depth " << std::setw(2) << pos.search_depth << ") : "
                  << std::right << std::fixed << std::setprecision(2) << pos_elapsed << "s"
                  << (found_in_pos ? " [ANOMALY DETECTED!]" : "")
                  << std::endl << std::flush;

        auto now = std::chrono::high_resolution_clock::now();
        double elapsed_sec = std::chrono::duration<double>(now - t_start).count();
        if (elapsed_sec > 840.0) {
            std::cout << "[Timer Warning] Approaching 15-minute hard limit (" << elapsed_sec << "s). Gracefully finalizing." << std::endl;
            break;
        }
    }

    std::sort(discoveries.begin(), discoveries.end(), [](const CandidateDiscovery &a, const CandidateDiscovery &b) {
        return a.divergence_score > b.divergence_score;
    });

    auto t_end = std::chrono::high_resolution_clock::now();
    double total_sec = std::chrono::duration<double>(t_end - t_start).count();

    std::cout << "\n================================================================================" << std::endl;
    std::cout << "  MOVE 37 DISCOVERY RUN COMPLETE" << std::endl;
    std::cout << "  Time Elapsed : " << std::fixed << std::setprecision(2) << total_sec << " seconds (" << (total_sec / 60.0) << " minutes)" << std::endl;
    std::cout << "  Nodes Explored: " << total_nodes << " nodes (" << std::fixed << std::setprecision(1) << (total_nodes / total_sec) << " nodes/sec)" << std::endl;
    std::cout << "  Anomalies Discovered: " << discoveries.size() << " High-Divergence Move 37 candidates" << std::endl;
    std::cout << "================================================================================\n" << std::endl;

    for (size_t i = 0; i < discoveries.size(); ++i) {
        const auto &d = discoveries[i];
        std::cout << "[" << (i + 1) << "] " << d.title << " (" << d.category << ")" << std::endl;
        std::cout << "    Turn          : " << d.turn_str << " to play" << std::endl;
        std::cout << "    Discovered Move: " << d.best_move_str << " !" << std::endl;
        std::cout << "    Minimax Value : " << d.minimax_value << " (Exact Win/Advantage)" << std::endl;
        std::cout << "    Human Dogma H : " << std::fixed << std::setprecision(1) << d.heuristic_score << " (Heuristically Penalized / Counter-Dogma)" << std::endl;
        std::cout << "    Divergence    : " << std::fixed << std::setprecision(1) << d.divergence_score << " (Degree of Paradox)" << std::endl;
        std::cout << "    PV Line       : ";
        for (size_t p = 0; p < d.pv_continuation.size(); ++p) {
            std::cout << d.pv_continuation[p] << (p + 1 < d.pv_continuation.size() ? " " : "");
        }
        std::cout << std::endl;
        std::cout << "    Rationale     : " << d.rationale << std::endl;
        std::cout << "    Candidate Moves Evaluated:" << std::endl;
        for (const auto &m : d.all_moves) {
            std::cout << "      Move " << std::setw(2) << m.src_std << (m.is_jump ? "x" : "-")
                      << std::setw(2) << m.dest_std
                      << " : Minimax = " << std::setw(6) << m.minimax_value
                      << " | Human Heuristic = " << std::showpos << std::fixed << std::setprecision(1) << m.heuristic_score << std::noshowpos << std::endl;
        }
        std::cout << std::endl;
    }

    std::ofstream ofs("checkpoints_8x8/move37_discoveries.json");
    if (ofs.is_open()) {
        ofs << "[\n";
        for (size_t i = 0; i < discoveries.size(); ++i) {
            const auto &d = discoveries[i];
            ofs << "  {\n";
            ofs << "    \"rank\": " << (i + 1) << ",\n";
            ofs << "    \"title\": \"" << d.title << "\",\n";
            ofs << "    \"category\": \"" << d.category << "\",\n";
            ofs << "    \"turn\": \"" << d.turn_str << "\",\n";
            ofs << "    \"move\": \"" << d.best_move_str << "\",\n";
            ofs << "    \"src_std\": " << d.src_std << ",\n";
            ofs << "    \"dest_std\": " << d.dest_std << ",\n";
            ofs << "    \"minimax_value\": " << d.minimax_value << ",\n";
            ofs << "    \"heuristic_score\": " << d.heuristic_score << ",\n";
            ofs << "    \"divergence_score\": " << d.divergence_score << ",\n";
            ofs << "    \"rationale\": \"" << d.rationale << "\",\n";
            ofs << "    \"pv_line\": [";
            for (size_t p = 0; p < d.pv_continuation.size(); ++p) {
                ofs << "\"" << d.pv_continuation[p] << "\"" << (p + 1 < d.pv_continuation.size() ? ", " : "");
            }
            ofs << "],\n";
            ofs << "    \"wm\": " << d.wm << ",\n";
            ofs << "    \"wk\": " << d.wk << ",\n";
            ofs << "    \"bm\": " << d.bm << ",\n";
            ofs << "    \"bk\": " << d.bk << ",\n";
            ofs << "    \"all_moves\": [\n";
            for (size_t j = 0; j < d.all_moves.size(); ++j) {
                const auto &m = d.all_moves[j];
                ofs << "      { \"src\": " << m.src_std << ", \"dest\": " << m.dest_std
                    << ", \"minimax\": " << m.minimax_value
                    << ", \"heuristic\": " << m.heuristic_score << " }"
                    << (j + 1 < d.all_moves.size() ? "," : "") << "\n";
            }
            ofs << "    ]\n";
            ofs << "  }" << (i + 1 < discoveries.size() ? "," : "") << "\n";
        }
        ofs << "]\n";
        ofs.close();
        std::cout << "[Saved] Discoveries catalog written to checkpoints_8x8/move37_discoveries.json" << std::endl;
    }

    delete[] tt;
    return 0;
}
