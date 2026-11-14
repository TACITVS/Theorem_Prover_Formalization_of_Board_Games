// qubic5_solver.cpp
// High-Performance 128-Bit Bitboard & Symmetry-DAG Proof Engine for 5x5x5 Qubic
// Compile: g++ -O3 -march=native -fopenmp -std=c++20 qubic5_solver.cpp -o qubic5_solver

#include <iostream>
#include <vector>
#include <array>
#include <algorithm>
#include <cstdint>
#include <cmath>
#include <chrono>
#include <random>
#include <iomanip>
#include <cstring>
#include <string>
#include <omp.h>

using u128 = unsigned __int128;

static inline constexpr u128 BIT(int i) {
    return u128(1) << (124 - i);
}

static inline int popcnt128(u128 x) {
    return __builtin_popcountll(static_cast<uint64_t>(x >> 64)) +
           __builtin_popcountll(static_cast<uint64_t>(x));
}

struct State {
    u128 m;
    u128 b;
    bool operator==(const State& o) const { return m == o.m && b == o.b; }
    bool operator<(const State& o) const {
        return (m != o.m) ? (m > o.m) : (b > o.b); // Descending u128 == Ascending lex tuple
    }
};

struct StateHash {
    size_t operator()(const State& s) const noexcept {
        uint64_t m_hi = static_cast<uint64_t>(s.m >> 64);
        uint64_t m_lo = static_cast<uint64_t>(s.m);
        uint64_t b_hi = static_cast<uint64_t>(s.b >> 64);
        uint64_t b_lo = static_cast<uint64_t>(s.b);
        uint64_t h = m_lo ^ (m_hi * 0x9e3779b97f4a7c15ULL);
        h ^= b_lo * 0xbf58476d1ce4e5b9ULL + (b_hi * 0x94d049bb133111ebULL);
        h ^= (h >> 30);
        h *= 0xbf58476d1ce4e5b9ULL;
        h ^= (h >> 27);
        return static_cast<size_t>(h);
    }
};

// Global Hypergraph H_5 Data
static constexpr int NUM_CELLS = 125;
static constexpr int NUM_LINES = 109;
static constexpr int CENTER_IDX = 62; // (2,2,2)

int line_cells[NUM_LINES][5];
u128 line_mask[NUM_LINES];
std::vector<int> pt_lines[NUM_CELLS];
u128 pt_neighbor_mask[NUM_CELLS]; // All cells sharing a line with cell i
int degs[NUM_CELLS];

// 48 Symmetries of O_h + 3.14 MB Fast Byte Lookup Table
int sym_perm[48][NUM_CELLS];
alignas(64) u128 sym_lut[48][16][256];

// Veblen K_4 Gadgets (168 total: 4 lines in 6 cells)
struct K4Gadget {
    std::array<int, 4> lines;
    std::array<int, 6> cells;
    u128 cell_mask;
};
std::vector<K4Gadget> k4_gadgets;

void init_hypergraph() {
    auto pt_to_idx = [](int x, int y, int z) { return x * 25 + y * 5 + z; };

    std::vector<std::array<int, 5>> raw_lines;
    for (int x = 0; x < 5; ++x)
        for (int y = 0; y < 5; ++y)
            for (int z = 0; z < 5; ++z)
                for (int dx : {-1, 0, 1})
                    for (int dy : {-1, 0, 1})
                        for (int dz : {-1, 0, 1}) {
                            if (dx == 0 && dy == 0 && dz == 0) continue;
                            int first_nz = (dx != 0) ? dx : ((dy != 0) ? dy : dz);
                            if (first_nz < 0) continue;
                            std::array<int, 5> pts;
                            bool ok = true;
                            for (int k = 0; k < 5; ++k) {
                                int nx = x + k * dx, ny = y + k * dy, nz = z + k * dz;
                                if (nx < 0 || nx >= 5 || ny < 0 || ny >= 5 || nz < 0 || nz >= 5) {
                                    ok = false; break;
                                }
                                pts[k] = pt_to_idx(nx, ny, nz);
                            }
                            if (ok) {
                                std::sort(pts.begin(), pts.end());
                                raw_lines.push_back(pts);
                            }
                        }
    std::sort(raw_lines.begin(), raw_lines.end());
    raw_lines.erase(std::unique(raw_lines.begin(), raw_lines.end()), raw_lines.end());

    for (int i = 0; i < NUM_CELLS; ++i) {
        pt_lines[i].clear();
        pt_neighbor_mask[i] = 0;
    }
    for (int j = 0; j < NUM_LINES; ++j) {
        u128 m = 0;
        for (int k = 0; k < 5; ++k) {
            int c = raw_lines[j][k];
            line_cells[j][k] = c;
            m |= BIT(c);
            pt_lines[c].push_back(j);
        }
        line_mask[j] = m;
        for (int k = 0; k < 5; ++k) {
            pt_neighbor_mask[raw_lines[j][k]] |= m;
        }
    }
    for (int i = 0; i < NUM_CELLS; ++i) {
        degs[i] = static_cast<int>(pt_lines[i].size());
    }

    // Build 48 cube symmetries O_h
    int perms[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
    int s_idx = 0;
    for (int p = 0; p < 6; ++p) {
        for (int sx : {-1, 1})
            for (int sy : {-1, 1})
                for (int sz : {-1, 1}) {
                    for (int i = 0; i < NUM_CELLS; ++i) {
                        int c[3] = {i / 25, (i / 5) % 5, i % 5};
                        int nx = sx * (c[perms[p][0]] - 2) + 2;
                        int ny = sy * (c[perms[p][1]] - 2) + 2;
                        int nz = sz * (c[perms[p][2]] - 2) + 2;
                        sym_perm[s_idx][i] = pt_to_idx(nx, ny, nz);
                    }
                    ++s_idx;
                }
    }

    // Precompute 8-bit chunk LUTs for fast u128 symmetry permutation
    std::memset(sym_lut, 0, sizeof(sym_lut));
    for (int g = 0; g < 48; ++g) {
        for (int b = 0; b < 16; ++b) {
            for (int val = 0; val < 256; ++val) {
                u128 out = 0;
                for (int bit = 0; bit < 8; ++bit) {
                    if ((val >> bit) & 1) {
                        int pos = 8 * b + bit;
                        if (pos <= 124) {
                            int cell = 124 - pos;
                            out |= BIT(sym_perm[g][cell]);
                        }
                    }
                }
                sym_lut[g][b][val] = out;
            }
        }
    }

    // Enumerate all 168 Veblen K_4 Gadgets (4 lines pairwise intersecting in 6 cells)
    int inter_cell[NUM_LINES][NUM_LINES];
    std::memset(inter_cell, -1, sizeof(inter_cell));
    for (int i = 0; i < NUM_LINES; ++i) {
        for (int j = i + 1; j < NUM_LINES; ++j) {
            u128 common = line_mask[i] & line_mask[j];
            if (common != 0) {
                for (int k = 0; k < 5; ++k) {
                    if (common & BIT(line_cells[i][k])) {
                        inter_cell[i][j] = inter_cell[j][i] = line_cells[i][k];
                        break;
                    }
                }
            }
        }
    }
    for (int i = 0; i < NUM_LINES; ++i)
        for (int j = i + 1; j < NUM_LINES; ++j) {
            if (inter_cell[i][j] < 0) continue;
            for (int k = j + 1; k < NUM_LINES; ++k) {
                if (inter_cell[i][k] < 0 || inter_cell[j][k] < 0) continue;
                for (int l = k + 1; l < NUM_LINES; ++l) {
                    if (inter_cell[i][l] < 0 || inter_cell[j][l] < 0 || inter_cell[k][l] < 0) continue;
                    std::array<int, 6> pts = {
                        inter_cell[i][j], inter_cell[i][k], inter_cell[i][l],
                        inter_cell[j][k], inter_cell[j][l], inter_cell[k][l]
                    };
                    std::sort(pts.begin(), pts.end());
                    bool distinct = true;
                    for (int q = 0; q < 5; ++q) if (pts[q] == pts[q+1]) distinct = false;
                    if (distinct) {
                        u128 cm = 0;
                        for (int pt : pts) cm |= BIT(pt);
                        k4_gadgets.push_back({{i, j, k, l}, pts, cm});
                    }
                }
            }
        }
}

static inline u128 apply_sym(int g, u128 mask) {
    uint64_t lo = static_cast<uint64_t>(mask);
    uint64_t hi = static_cast<uint64_t>(mask >> 64);
    u128 res = sym_lut[g][0][lo & 0xFF]
             | sym_lut[g][1][(lo >> 8) & 0xFF]
             | sym_lut[g][2][(lo >> 16) & 0xFF]
             | sym_lut[g][3][(lo >> 24) & 0xFF]
             | sym_lut[g][4][(lo >> 32) & 0xFF]
             | sym_lut[g][5][(lo >> 40) & 0xFF]
             | sym_lut[g][6][(lo >> 48) & 0xFF]
             | sym_lut[g][7][(lo >> 56) & 0xFF]
             | sym_lut[g][8][hi & 0xFF]
             | sym_lut[g][9][(hi >> 8) & 0xFF]
             | sym_lut[g][10][(hi >> 16) & 0xFF]
             | sym_lut[g][11][(hi >> 24) & 0xFF]
             | sym_lut[g][12][(hi >> 32) & 0xFF]
             | sym_lut[g][13][(hi >> 40) & 0xFF]
             | sym_lut[g][14][(hi >> 48) & 0xFF]
             | sym_lut[g][15][(hi >> 56) & 0xFF];
    return res;
}

static inline State canonicalize(u128 m, u128 b) {
    u128 best_m = m;
    u128 best_b = b;
    for (int g = 1; g < 48; ++g) {
        u128 gm = apply_sym(g, m);
        if (gm >= best_m) {
            u128 gb = apply_sym(g, b);
            if (gm > best_m || gb > best_b) {
                best_m = gm;
                best_b = gb;
            }
        }
    }
    return {best_m, best_b};
}

// Exact Integer Threat-Aware Erdos-Selfridge Breaker Move (Weights in units of 1/32)
int es_breaker_move(u128 m, u128 b) {
    u128 occ = m | b;
    int line_w[NUM_LINES];
    u128 threat_mask = 0;

    for (int j = 0; j < NUM_LINES; ++j) {
        if ((line_mask[j] & b) != 0) {
            line_w[j] = 0;
        } else {
            int m_cnt = popcnt128(line_mask[j] & m);
            line_w[j] = 1 << m_cnt; // 2^(m_cnt) == 32 * 2^(-empty_cnt)
            if (m_cnt == 4) {
                threat_mask |= (line_mask[j] & ~occ);
            }
        }
    }

    int best_cell = -1;
    int best_score = -1;
    int best_deg = -1;

    for (int i = 0; i < NUM_CELLS; ++i) {
        u128 bit = BIT(i);
        if (occ & bit) continue;
        if (threat_mask != 0 && !(threat_mask & bit)) continue;
        int s = 0;
        for (int j : pt_lines[i]) s += line_w[j];
        if (s > best_score || (s == best_score && degs[i] > best_deg)) {
            best_score = s;
            best_deg = degs[i];
            best_cell = i;
        }
    }
    return best_cell;
}

// Compute Raw Phi'_t and Degree-1 Kernelized Phi'_t (in units of 1/32, so < 32 means Phi' < 1.0)
void compute_phis(u128 m, u128 b, int& raw_phi32, int& kern_phi32, int& max_c4, int& max_c3) {
    u128 occ = m | b;
    int alive_deg[NUM_CELLS] = {0};
    int alive_lines[NUM_LINES];
    int line_w[NUM_LINES];
    int n_alive = 0;
    raw_phi32 = 0;
    max_c4 = 0;
    max_c3 = 0;

    for (int j = 0; j < NUM_LINES; ++j) {
        if ((line_mask[j] & b) == 0) {
            int m_cnt = popcnt128(line_mask[j] & m);
            int w = 1 << m_cnt;
            raw_phi32 += w;
            if (m_cnt == 4) ++max_c4;
            else if (m_cnt == 3) ++max_c3;
            alive_lines[n_alive] = j;
            line_w[n_alive] = w;
            ++n_alive;
            for (int k = 0; k < 5; ++k) {
                int c = line_cells[j][k];
                if (!(occ & BIT(c))) ++alive_deg[c];
            }
        }
    }

    kern_phi32 = 0;
    for (int idx = 0; idx < n_alive; ++idx) {
        int j = alive_lines[idx];
        int deg1_cnt = 0;
        for (int k = 0; k < 5; ++k) {
            int c = line_cells[j][k];
            if (!(occ & BIT(c)) && alive_deg[c] == 1) ++deg1_cnt;
        }
        if (deg1_cnt < 2) kern_phi32 += line_w[idx];
    }
}

// Stack-Allocated Hopcroft-Karp Bipartite 2-Matching (Zero Heap Allocation)
bool check_hopcroft_karp(u128 m, u128 b, bool use_k4 = false) {
    u128 occ = m | b;
    int empty_cnt = NUM_CELLS - popcnt128(occ);

    u128 covered_lines_mask = 0;
    if (use_k4) {
        // Greedily pack disjoint K_4 gadgets on empty cells that cover 3 or 4 alive lines
        for (const auto& g : k4_gadgets) {
            if ((g.cell_mask & occ) != 0) continue;
            int alive_in_g = 0;
            for (int l_idx : g.lines) {
                if ((line_mask[l_idx] & b) == 0 && !(covered_lines_mask & (u128(1) << l_idx))) {
                    ++alive_in_g;
                }
            }
            if (alive_in_g == 4) {
                occ |= g.cell_mask;
                empty_cnt -= 6;
                for (int l_idx : g.lines) covered_lines_mask |= (u128(1) << l_idx);
            }
        }
    }

    int alive_list[NUM_LINES];
    int n_alive = 0;
    for (int j = 0; j < NUM_LINES; ++j) {
        if ((line_mask[j] & b) == 0 && !(covered_lines_mask & (u128(1) << j))) {
            alive_list[n_alive++] = j;
        }
    }
    if (n_alive == 0) return true;
    int n_left = 2 * n_alive;
    if (n_left > empty_cnt) return false;

    int adj[218][5];
    int adj_sz[218];
    for (int r = 0; r < n_alive; ++r) {
        int j = alive_list[r];
        int deg = 0;
        for (int k = 0; k < 5; ++k) {
            int c = line_cells[j][k];
            if (!(occ & BIT(c))) {
                adj[2*r][deg] = c;
                adj[2*r+1][deg] = c;
                ++deg;
            }
        }
        if (deg < 2) return false;
        adj_sz[2*r] = adj_sz[2*r+1] = deg;
    }

    int16_t match_u[218];
    int16_t match_v[NUM_CELLS];
    int16_t dist[218];
    int16_t q[218];
    std::fill_n(match_u, n_left, -1);
    std::fill_n(match_v, NUM_CELLS, -1);

    int matched = 0;
    while (true) {
        int q_head = 0, q_tail = 0;
        for (int u = 0; u < n_left; ++u) {
            if (match_u[u] == -1) {
                dist[u] = 0;
                q[q_tail++] = u;
            } else {
                dist[u] = -1;
            }
        }
        bool found_aug = false;
        while (q_head < q_tail) {
            int u = q[q_head++];
            for (int k = 0; k < adj_sz[u]; ++k) {
                int v = adj[u][k];
                int next_u = match_v[v];
                if (next_u == -1) {
                    found_aug = true;
                } else if (dist[next_u] == -1) {
                    dist[next_u] = dist[u] + 1;
                    q[q_tail++] = next_u;
                }
            }
        }
        if (!found_aug) break;

        auto dfs = [&](auto& self, int u) -> bool {
            for (int k = 0; k < adj_sz[u]; ++k) {
                int v = adj[u][k];
                int next_u = match_v[v];
                if (next_u == -1 || (dist[next_u] == dist[u] + 1 && self(self, next_u))) {
                    match_u[u] = v;
                    match_v[v] = u;
                    return true;
                }
            }
            dist[u] = -1;
            return false;
        };

        for (int u = 0; u < n_left; ++u) {
            if (match_u[u] == -1 && dfs(dfs, u)) ++matched;
        }
    }
    return matched == n_left;
}

// Parallel BFS Expansion Step for the Canonical DAG
void expand_dag_level(const std::vector<State>& curr_dag,
                      std::vector<State>& after_maker_out,
                      std::vector<State>& next_dag_out,
                      bool coupled_only = false) {
    int n_threads = omp_get_max_threads();
    std::vector<std::vector<State>> local_after_m(n_threads);

    #pragma omp parallel
    {
        int tid = omp_get_thread_num();
        auto& out_vec = local_after_m[tid];
        out_vec.reserve(curr_dag.size() * 20 / n_threads + 64);

        #pragma omp for schedule(dynamic, 64)
        for (size_t idx = 0; idx < curr_dag.size(); ++idx) {
            u128 m = curr_dag[idx].m;
            u128 b = curr_dag[idx].b;
            u128 occ = m | b;

            // Find stabilizers of (m, b)
            int stabs[48];
            int n_stabs = 0;
            for (int g = 0; g < 48; ++g) {
                if (apply_sym(g, m) == m && apply_sym(g, b) == b) {
                    stabs[n_stabs++] = g;
                }
            }

            // Compute alive line mask
            u128 alive_cell_mask = 0;
            u128 coupled_cell_mask = 0;
            for (int j = 0; j < NUM_LINES; ++j) {
                if ((line_mask[j] & b) == 0) {
                    alive_cell_mask |= line_mask[j];
                    if ((line_mask[j] & m) != 0) {
                        coupled_cell_mask |= line_mask[j];
                    }
                }
            }

            u128 visited = occ;
            int dead_rep = -1;
            for (int e = 0; e < NUM_CELLS; ++e) {
                u128 bit = BIT(e);
                if (visited & bit) continue;
                for (int s = 0; s < n_stabs; ++s) {
                    visited |= BIT(sym_perm[stabs[s]][e]);
                }
                if (coupled_only && m != 0) {
                    if (coupled_cell_mask & bit) {
                        out_vec.push_back(canonicalize(m | bit, b));
                    }
                } else {
                    if (alive_cell_mask & bit) {
                        out_vec.push_back(canonicalize(m | bit, b));
                    } else if (dead_rep == -1) {
                        dead_rep = e;
                    }
                }
            }
            if (!coupled_only && dead_rep != -1) {
                out_vec.push_back(canonicalize(m | BIT(dead_rep), b));
            }
        }
    }

    // Merge and deduplicate after_maker
    size_t total_m = 0;
    for (const auto& v : local_after_m) total_m += v.size();
    after_maker_out.clear();
    after_maker_out.reserve(total_m);
    for (auto& v : local_after_m) {
        after_maker_out.insert(after_maker_out.end(), v.begin(), v.end());
        std::vector<State>().swap(v);
    }
    std::sort(after_maker_out.begin(), after_maker_out.end());
    after_maker_out.erase(std::unique(after_maker_out.begin(), after_maker_out.end()), after_maker_out.end());

    // Step B: Deterministic Equivariant Breaker Move
    next_dag_out.resize(after_maker_out.size());
    #pragma omp parallel for schedule(static)
    for (size_t idx = 0; idx < after_maker_out.size(); ++idx) {
        u128 m = after_maker_out[idx].m;
        u128 b = after_maker_out[idx].b;
        int b_move = es_breaker_move(m, b);
        next_dag_out[idx] = canonicalize(m, b | BIT(b_move));
    }
    std::sort(next_dag_out.begin(), next_dag_out.end());
    next_dag_out.erase(std::unique(next_dag_out.begin(), next_dag_out.end()), next_dag_out.end());
}

// Recursive Threat-Space Forcing Win Detector (Depth-Limited)
bool find_forcing_win(u128 m, u128 b, int depth_left) {
    u128 occ = m | b;
    int threat_cells[10];
    int n_threats = 0;
    for (int j = 0; j < NUM_LINES; ++j) {
        if ((line_mask[j] & b) == 0 && popcnt128(line_mask[j] & m) == 4) {
            return true; // Immediate 5-in-a-row available!
        }
    }
    if (depth_left <= 0) return false;

    // Look for moves i that create >= 2 four-in-a-rows (instant fork win) or 1 four-in-a-row (forcing move)
    for (int i = 0; i < NUM_CELLS; ++i) {
        u128 bit = BIT(i);
        if (occ & bit) continue;
        u128 m_new = m | bit;
        u128 forced_replies = 0;
        for (int j : pt_lines[i]) {
            if ((line_mask[j] & b) == 0 && popcnt128(line_mask[j] & m_new) == 4) {
                forced_replies |= (line_mask[j] & ~(occ | bit));
            }
        }
        int n_rep = popcnt128(forced_replies);
        if (n_rep >= 2) return true; // Double threat!
        if (n_rep == 1) {
            if (find_forcing_win(m_new, b | forced_replies, depth_left - 1)) return true;
        }
    }
    return false;
}

int main(int argc, char** argv) {
    bool deep_mode = false;
    for (int i = 1; i < argc; ++i) {
        if (std::string(argv[i]) == "--deep") deep_mode = true;
    }

    auto t_start = std::chrono::high_resolution_clock::now();
    init_hypergraph();

    std::cout << "========================================================================\n";
    std::cout << " 5x5x5 QUBIC BITBOARD & SYMMETRY-DAG PROOF ENGINE (C++20 / OpenMP)\n";
    std::cout << " Hardware Threads Detected: " << omp_get_max_threads()
              << " | Veblen K_4 Gadgets: " << k4_gadgets.size() << "\n";
    std::cout << "========================================================================\n\n";

    // -------------------------------------------------------------------------
    // SUITE 1: Exact Full-Board DAG Enumeration (Plies 2, 4, 6, and 8)
    // -------------------------------------------------------------------------
    std::cout << "=== SUITE 1: Exact Full-Board Canonical DAG Enumeration ===\n";
    std::vector<State> dag = {{0, 0}};
    int max_full_t = deep_mode ? 4 : 3;

    size_t ply_counts[5] = {1, 0, 0, 0, 0};
    double max_phi_full[5] = {3.40625, 0, 0, 0, 0};
    double max_phi_off[5]  = {3.40625, 0, 0, 0, 0};

    for (int t = 1; t <= max_full_t; ++t) {
        auto t0 = std::chrono::high_resolution_clock::now();
        std::vector<State> after_m, next_dag;
        expand_dag_level(dag, after_m, next_dag, false);

        int max_p_center = 0, max_p_off = 0;
        #pragma omp parallel for reduction(max:max_p_center, max_p_off)
        for (size_t i = 0; i < after_m.size(); ++i) {
            int raw_p, kern_p, c4, c3;
            compute_phis(after_m[i].m, after_m[i].b, raw_p, kern_p, c4, c3);
            if (after_m[i].m & BIT(CENTER_IDX)) {
                if (raw_p > max_p_center) max_p_center = raw_p;
            } else {
                if (raw_p > max_p_off) max_p_off = raw_p;
            }
        }

        ply_counts[t] = next_dag.size();
        max_phi_full[t] = max_p_center / 32.0;
        max_phi_off[t]  = max_p_off / 32.0;
        dag.swap(next_dag);

        double dt = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - t0).count();
        std::cout << "Round t=" << t << " (Ply " << 2*t << "): "
                  << "After Maker = " << std::setw(9) << after_m.size()
                  << " | Canonical DAG = " << std::setw(9) << ply_counts[t]
                  << " | max(Phi'_center) = " << std::fixed << std::setprecision(4) << max_phi_full[t]
                  << " | max(Phi'_off) = " << max_phi_off[t]
                  << " [" << std::setprecision(2) << dt << "s]\n";
    }

    // Verify Unit-Test Checksums
    if (ply_counts[1] == 10 && ply_counts[2] == 269 && ply_counts[3] == 17670) {
        std::cout << "[CHECKSUM PASS] Exact match with mathematical oracle: 10 -> 269 -> 17,670!\n\n";
    } else {
        std::cout << "[WARNING] Checksum mismatch!\n\n";
    }

    // -------------------------------------------------------------------------
    // SUITE 2: Principal Center Opening x1=(2,2,2) Threat-Coupled DAG (Plies 2..10+)
    // -------------------------------------------------------------------------
    std::cout << "=== SUITE 2: Center Opening x1=(2,2,2) Threat-Coupled DAG ===\n";
    u128 m0 = BIT(CENTER_IDX);
    int b0_move = es_breaker_move(m0, 0);
    std::vector<State> c_dag = {canonicalize(m0, BIT(b0_move))};
    int max_coupled_t = deep_mode ? 6 : 5;
    std::vector<size_t> coupled_dag_sizes(max_coupled_t + 1, 0);
    coupled_dag_sizes[1] = 1;

    for (int t = 2; t <= max_coupled_t; ++t) {
        auto t0 = std::chrono::high_resolution_clock::now();
        std::vector<State> after_m, next_dag;
        expand_dag_level(c_dag, after_m, next_dag, true);

        int max_p = 0, min_p = 999999, max_c4 = 0, max_c3 = 0;
        long long sum_p = 0;
        #pragma omp parallel for reduction(max:max_p, max_c4, max_c3) reduction(min:min_p) reduction(+:sum_p)
        for (size_t i = 0; i < after_m.size(); ++i) {
            int raw_p, kern_p, c4, c3;
            compute_phis(after_m[i].m, after_m[i].b, raw_p, kern_p, c4, c3);
            if (raw_p > max_p) max_p = raw_p;
            if (raw_p < min_p) min_p = raw_p;
            if (c4 > max_c4) max_c4 = c4;
            if (c3 > max_c3) max_c3 = c3;
            sum_p += raw_p;
        }
        coupled_dag_sizes[t] = next_dag.size();
        c_dag.swap(next_dag);
        double dt = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - t0).count();
        std::cout << "[Coupled] Round t=" << t << " (Ply " << 2*t << "): "
                  << "After Maker = " << std::setw(9) << after_m.size()
                  << " | Canonical DAG = " << std::setw(9) << coupled_dag_sizes[t]
                  << " | Phi' max/mean/min = " << std::fixed << std::setprecision(4)
                  << (max_p / 32.0) << "/" << (sum_p / (32.0 * after_m.size())) << "/" << (min_p / 32.0)
                  << " | max_c4=" << max_c4 << ", max_c3=" << max_c3
                  << " [" << std::setprecision(2) << dt << "s]\n";
    }
    std::cout << "\n";

    // -------------------------------------------------------------------------
    // SUITE 3: Adversarial Falsification Hunter (50,000 Threat-Seeking Games)
    // -------------------------------------------------------------------------
    std::cout << "=== SUITE 3: Multi-Threaded Adversarial Falsification Search (50,000 Games) ===\n";
    auto t3_start = std::chrono::high_resolution_clock::now();
    int total_wins = 0;
    int global_max_c4 = 0;
    int global_max_c3 = 0;
    std::vector<int> max_phi_by_round(64, 0);

    #pragma omp parallel reduction(+:total_wins) reduction(max:global_max_c4, global_max_c3)
    {
        std::mt19937_64 rng(1337 + omp_get_thread_num() * 99991);
        std::uniform_real_distribution<double> noise(0.0, 0.25);
        int local_max_phi[64] = {0};

        #pragma omp for schedule(static)
        for (int game = 0; game < 50000; ++game) {
            u128 m = 0, b = 0;
            double base_m = (game % 3 == 0) ? 3.5 : ((game % 3 == 1) ? 2.5 : 2.0);
            for (int t = 1; t <= 63; ++t) {
                u128 occ = m | b;
                if (popcnt128(occ) >= NUM_CELLS) break;

                if (t >= 6 && find_forcing_win(m, b, 5)) {
                    ++total_wins;
                    break;
                }

                // Compute Maker move maximizing base_m potential + 3-in-a-row fork bonus + noise
                int line_m_cnt[NUM_LINES];
                bool line_alive[NUM_LINES];
                bool any_alive = false;
                for (int j = 0; j < NUM_LINES; ++j) {
                    if ((line_mask[j] & b) == 0) {
                        line_alive[j] = true;
                        line_m_cnt[j] = popcnt128(line_mask[j] & m);
                        any_alive = true;
                    } else {
                        line_alive[j] = false;
                    }
                }
                if (!any_alive) break;

                int best_m_cell = -1;
                double best_val = -1e18;
                for (int i = 0; i < NUM_CELLS; ++i) {
                    if (occ & BIT(i)) continue;
                    double val = noise(rng);
                    int c3_created = 0;
                    for (int j : pt_lines[i]) {
                        if (!line_alive[j]) continue;
                        int mc = line_m_cnt[j] + 1;
                        val += std::pow(base_m, mc - 5);
                        if (mc == 3) ++c3_created;
                        if (mc == 4) val += 0.5;
                    }
                    val += 0.2 * c3_created * (c3_created - 1);
                    if (val > best_val) {
                        best_val = val;
                        best_m_cell = i;
                    }
                }
                m |= BIT(best_m_cell);

                int raw_p, kern_p, c4, c3;
                compute_phis(m, b, raw_p, kern_p, c4, c3);
                if (raw_p > local_max_phi[t]) local_max_phi[t] = raw_p;
                if (c4 > global_max_c4) global_max_c4 = c4;
                if (c3 > global_max_c3) global_max_c3 = c3;
                if (c4 >= 2) {
                    ++total_wins;
                    break;
                }

                int bm = es_breaker_move(m, b);
                if (bm < 0) break;
                b |= BIT(bm);
            }
        }
        #pragma omp critical
        {
            for (int t = 1; t < 64; ++t) {
                if (local_max_phi[t] > max_phi_by_round[t]) max_phi_by_round[t] = local_max_phi[t];
            }
        }
    }
    double dt3 = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - t3_start).count();
    std::cout << "Adversarial Games Run : 50,000 [" << std::setprecision(2) << dt3 << "s]\n";
    std::cout << "Maker Wins Found      : " << total_wins << " / 50,000\n";
    std::cout << "Max Simultaneous 4-in-a-rows (c4): " << global_max_c4 << " (Fork requires >= 2)\n";
    std::cout << "Max Simultaneous 3-in-a-rows (c3): " << global_max_c3 << "\n\n";

    // -------------------------------------------------------------------------
    // SUITE 4: 10,000-Trial Cutoff Horizon & Knuth Tree-Size Estimator
    // -------------------------------------------------------------------------
    std::cout << "=== SUITE 4: 10,000-Trial Cutoff Horizons & Knuth DAG Estimator ===\n";
    auto t4_start = std::chrono::high_resolution_clock::now();
    constexpr int N_TRIALS = 10000;
    std::vector<int> hk_std(N_TRIALS), hk_k4(N_TRIALS), es_kern(N_TRIALS), es_raw(N_TRIALS), dead_col(N_TRIALS);
    std::vector<double> knuth_dag_log10(N_TRIALS), knuth_coupled_log10(N_TRIALS);

    #pragma omp parallel
    {
        std::mt19937_64 rng(42 + omp_get_thread_num() * 10007);
        std::uniform_real_distribution<double> noise(0.0, 0.05);

        #pragma omp for schedule(static)
        for (int tr = 0; tr < N_TRIALS; ++tr) {
            u128 m = 0, b = 0;
            int t_hk = 63, t_k4 = 63, t_esk = 63, t_esr = 63, t_dead = 63;
            double log10_active = 0.0, log10_coupled = 0.0;

            for (int t = 1; t <= 63; ++t) {
                u128 occ = m | b;
                u128 alive_mask = 0, coupled_mask = 0;
                int line_w[NUM_LINES] = {0};

                for (int j = 0; j < NUM_LINES; ++j) {
                    if ((line_mask[j] & b) == 0) {
                        alive_mask |= line_mask[j];
                        int mc = popcnt128(line_mask[j] & m);
                        line_w[j] = 1 << mc;
                        if (mc >= 1) coupled_mask |= line_mask[j];
                    }
                }
                u128 active_cells = alive_mask & ~occ;
                int n_active = popcnt128(active_cells);
                if (n_active == 0) {
                    if (t_dead == 63) t_dead = t;
                    break;
                }
                u128 coupled_cells = (t == 1) ? active_cells : (coupled_mask & ~occ);
                int n_coupled = popcnt128(coupled_cells);
                if (n_coupled == 0) n_coupled = n_active;

                if (t_k4 == 63 && t_esk == 63) {
                    log10_active += std::log10(static_cast<double>(n_active));
                    log10_coupled += std::log10(static_cast<double>(std::min(n_coupled, 8)));
                }

                // Maker move selection
                int best_c = -1;
                double best_s = -1e18;
                for (int i = 0; i < NUM_CELLS; ++i) {
                    if (!(active_cells & BIT(i))) continue;
                    double s = (tr % 5 == 0) ? noise(rng) : (noise(rng));
                    if (tr % 5 != 0) {
                        for (int j : pt_lines[i]) s += line_w[j] / 32.0;
                    }
                    if (s > best_s) { best_s = s; best_c = i; }
                }
                m |= BIT(best_c);

                int raw_p, kern_p, c4, c3;
                compute_phis(m, b, raw_p, kern_p, c4, c3);
                if (t_esr == 63 && raw_p < 32) t_esr = t;
                if (t_esk == 63 && kern_p < 32) t_esk = t;

                int bm = es_breaker_move(m, b);
                if (bm >= 0) b |= BIT(bm);

                if (t >= 9) {
                    if (t_k4 == 63 && check_hopcroft_karp(m, b, true)) t_k4 = t;
                    if (t_hk == 63 && t >= 10 && check_hopcroft_karp(m, b, false)) t_hk = t;
                }
            }

            int stop_t = std::min({t_k4, t_hk, t_esk});
            double log10_fact = std::lgamma(stop_t + 1) / std::log(10.0);
            hk_std[tr]  = t_hk;
            hk_k4[tr]   = t_k4;
            es_kern[tr] = t_esk;
            es_raw[tr]  = t_esr;
            dead_col[tr]= t_dead;
            knuth_dag_log10[tr]     = log10_active - log10_fact - std::log10(48.0);
            knuth_coupled_log10[tr] = log10_coupled - std::log10(48.0);
        }
    }

    auto stats = [](const std::vector<int>& v) {
        double sum = 0;
        int mn = 999, mx = -1;
        for (int x : v) { sum += x; if (x < mn) mn = x; if (x > mx) mx = x; }
        double mean = sum / v.size();
        double var = 0;
        for (int x : v) var += (x - mean) * (x - mean);
        return std::make_tuple(mean, std::sqrt(var / v.size()), mn, mx);
    };

    auto [m_k4, s_k4, min_k4, max_k4]     = stats(hk_k4);
    auto [m_hk, s_hk, min_hk, max_hk]     = stats(hk_std);
    auto [m_esk, s_esk, min_esk, max_esk] = stats(es_kern);
    auto [m_esr, s_esr, min_esr, max_esr] = stats(es_raw);
    auto [m_dd, s_dd, min_dd, max_dd]     = stats(dead_col);

    double mean_dag_log = 0, mean_coup_log = 0;
    for (int i = 0; i < N_TRIALS; ++i) {
        mean_dag_log += knuth_dag_log10[i];
        mean_coup_log += knuth_coupled_log10[i];
    }
    mean_dag_log /= N_TRIALS;
    mean_coup_log /= N_TRIALS;

    double dt4 = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - t4_start).count();
    double total_dt = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - t_start).count();

    std::cout << "=== COPY-PASTE SUMMARY FOR RESEARCH FEEDBACK ===\n";
    std::cout << std::fixed << std::setprecision(2);
    std::cout << "Full DAG Counts     : Ply2=" << ply_counts[1] << ", Ply4=" << ply_counts[2] << ", Ply6=" << ply_counts[3];
    if (max_full_t >= 4) std::cout << ", Ply8=" << ply_counts[4];
    std::cout << "\nCoupled Center DAG  : ";
    for (int t = 1; t <= max_coupled_t; ++t) std::cout << "Ply" << 2*t << "=" << coupled_dag_sizes[t] << (t < max_coupled_t ? ", " : "\n");
    std::cout << "Falsification 50k   : Maker_Wins=" << total_wins << ", Max_c4=" << global_max_c4 << ", Max_c3=" << global_max_c3 << "\n";
    std::cout << "Max Phi' Profile    : t1=" << (max_phi_by_round[1]/32.0) << ", t5=" << (max_phi_by_round[5]/32.0)
              << ", t10=" << (max_phi_by_round[10]/32.0) << ", t15=" << (max_phi_by_round[15]/32.0)
              << ", t20=" << (max_phi_by_round[20]/32.0) << ", t25=" << (max_phi_by_round[25]/32.0) << "\n";
    std::cout << "K4+HK Pairing Cutoff: Mean=" << m_k4  << " (std=" << s_k4  << ", min=" << min_k4  << ", max=" << max_k4  << ")\n";
    std::cout << "Std HK Pairing      : Mean=" << m_hk  << " (std=" << s_hk  << ", min=" << min_hk  << ", max=" << max_hk  << ")\n";
    std::cout << "Kernelized ES (<1)  : Mean=" << m_esk << " (std=" << s_esk << ", min=" << min_esk << ", max=" << max_esk << ")\n";
    std::cout << "Raw ES (<1)         : Mean=" << m_esr << " (std=" << s_esr << ", min=" << min_esr << ", max=" << max_esr << ")\n";
    std::cout << "100% Dead Collapse  : Mean=" << m_dd  << " (std=" << s_dd  << ", min=" << min_dd  << ", max=" << max_dd  << ")\n";
    std::cout << "Knuth Unord DAG     : 10^" << mean_dag_log << " states | Coupled Tree: 10^" << mean_coup_log << " [" << dt4 << "s, Total " << total_dt << "s]\n";
    std::cout << "================================================\n";
    return 0;
}