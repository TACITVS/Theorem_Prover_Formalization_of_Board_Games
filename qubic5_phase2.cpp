// qubic5_phase2.cpp
// Phase-2 Engine: Exact Potential-Ridge Stratification & Full-Horizon (t=1..25) Cutoff Search
// Compile: g++ -O3 -march=native -fopenmp -std=c++20 qubic5_phase2.cpp -o qubic5_phase2

#include <iostream>
#include <vector>
#include <array>
#include <algorithm>
#include <cstdint>
#include <cmath>
#include <chrono>
#include <iomanip>
#include <cstring>
#include <map>
#include <omp.h>

using u128 = unsigned __int128;

static inline constexpr u128 BIT(int i) { return u128(1) << (124 - i); }
static inline int popcnt128(u128 x) {
    return __builtin_popcountll(static_cast<uint64_t>(x >> 64)) +
           __builtin_popcountll(static_cast<uint64_t>(x));
}

struct State {
    u128 m;
    u128 b;
    bool operator==(const State& o) const { return m == o.m && b == o.b; }
    bool operator<(const State& o) const {
        return (m != o.m) ? (m > o.m) : (b > o.b);
    }
};

static constexpr int NUM_CELLS = 125;
static constexpr int NUM_LINES = 109;
static constexpr int CENTER_IDX = 62;

int line_cells[NUM_LINES][5];
u128 line_mask[NUM_LINES];
std::vector<int> pt_lines[NUM_CELLS];
int degs[NUM_CELLS];
int sym_perm[48][NUM_CELLS];
alignas(64) u128 sym_lut[48][16][256];

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

    for (int i = 0; i < NUM_CELLS; ++i) pt_lines[i].clear();
    for (int j = 0; j < NUM_LINES; ++j) {
        u128 m = 0;
        for (int k = 0; k < 5; ++k) {
            int c = raw_lines[j][k];
            line_cells[j][k] = c;
            m |= BIT(c);
            pt_lines[c].push_back(j);
        }
        line_mask[j] = m;
    }
    for (int i = 0; i < NUM_CELLS; ++i) degs[i] = static_cast<int>(pt_lines[i].size());

    int perms[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
    int s_idx = 0;
    for (int p = 0; p < 6; ++p)
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

    std::memset(sym_lut, 0, sizeof(sym_lut));
    for (int g = 0; g < 48; ++g)
        for (int b = 0; b < 16; ++b)
            for (int val = 0; val < 256; ++val) {
                u128 out = 0;
                for (int bit = 0; bit < 8; ++bit) {
                    if ((val >> bit) & 1) {
                        int pos = 8 * b + bit;
                        if (pos <= 124) out |= BIT(sym_perm[g][124 - pos]);
                    }
                }
                sym_lut[g][b][val] = out;
            }
}

static inline u128 apply_sym(int g, u128 mask) {
    uint64_t lo = static_cast<uint64_t>(mask);
    uint64_t hi = static_cast<uint64_t>(mask >> 64);
    return sym_lut[g][0][lo & 0xFF] | sym_lut[g][1][(lo >> 8) & 0xFF]
         | sym_lut[g][2][(lo >> 16) & 0xFF] | sym_lut[g][3][(lo >> 24) & 0xFF]
         | sym_lut[g][4][(lo >> 32) & 0xFF] | sym_lut[g][5][(lo >> 40) & 0xFF]
         | sym_lut[g][6][(lo >> 48) & 0xFF] | sym_lut[g][7][(lo >> 56) & 0xFF]
         | sym_lut[g][8][hi & 0xFF] | sym_lut[g][9][(hi >> 8) & 0xFF]
         | sym_lut[g][10][(hi >> 16) & 0xFF] | sym_lut[g][11][(hi >> 24) & 0xFF]
         | sym_lut[g][12][(hi >> 32) & 0xFF] | sym_lut[g][13][(hi >> 40) & 0xFF]
         | sym_lut[g][14][(hi >> 48) & 0xFF] | sym_lut[g][15][(hi >> 56) & 0xFF];
}

static inline State canonicalize(u128 m, u128 b) {
    u128 best_m = m, best_b = b;
    for (int g = 1; g < 48; ++g) {
        u128 gm = apply_sym(g, m);
        if (gm >= best_m) {
            u128 gb = apply_sym(g, b);
            if (gm > best_m || gb > best_b) { best_m = gm; best_b = gb; }
        }
    }
    return {best_m, best_b};
}

int es_breaker_move(u128 m, u128 b) {
    u128 occ = m | b;
    int line_w[NUM_LINES];
    u128 threat_mask = 0;
    for (int j = 0; j < NUM_LINES; ++j) {
        if ((line_mask[j] & b) != 0) {
            line_w[j] = 0;
        } else {
            int mc = popcnt128(line_mask[j] & m);
            line_w[j] = 1 << mc;
            if (mc == 4) threat_mask |= (line_mask[j] & ~occ);
        }
    }
    int best_cell = -1, best_score = -1, best_deg = -1;
    for (int i = 0; i < NUM_CELLS; ++i) {
        u128 bit = BIT(i);
        if (occ & bit) continue;
        if (threat_mask != 0 && !(threat_mask & bit)) continue;
        int s = 0;
        for (int j : pt_lines[i]) s += line_w[j];
        if (s > best_score || (s == best_score && degs[i] > best_deg)) {
            best_score = s; best_deg = degs[i]; best_cell = i;
        }
    }
    return best_cell;
}

void compute_phis(u128 m, u128 b, int& raw_phi32, int& kern_phi32, int& max_c4, int& max_c3, int& max_c2) {
    u128 occ = m | b;
    int alive_deg[NUM_CELLS] = {0};
    int alive_lines[NUM_LINES], line_w[NUM_LINES], n_alive = 0;
    raw_phi32 = max_c4 = max_c3 = max_c2 = 0;

    for (int j = 0; j < NUM_LINES; ++j) {
        if ((line_mask[j] & b) == 0) {
            int mc = popcnt128(line_mask[j] & m);
            int w = 1 << mc;
            raw_phi32 += w;
            if (mc == 4) ++max_c4;
            else if (mc == 3) ++max_c3;
            else if (mc == 2) ++max_c2;
            alive_lines[n_alive] = j;
            line_w[n_alive++] = w;
            for (int k = 0; k < 5; ++k) {
                int c = line_cells[j][k];
                if (!(occ & BIT(c))) ++alive_deg[c];
            }
        }
    }
    kern_phi32 = 0;
    for (int idx = 0; idx < n_alive; ++idx) {
        int j = alive_lines[idx], deg1_cnt = 0;
        for (int k = 0; k < 5; ++k) {
            int c = line_cells[j][k];
            if (!(occ & BIT(c)) && alive_deg[c] == 1) ++deg1_cnt;
        }
        if (deg1_cnt < 2) kern_phi32 += line_w[idx];
    }
}

// Fast Stack Hopcroft-Karp on a specified subset of alive lines and available empty cells
bool run_hk_subset(const int* lines_subset, int n_alive, u128 avail_empty_mask) {
    if (n_alive == 0) return true;
    int n_left = 2 * n_alive;
    if (n_left > popcnt128(avail_empty_mask)) return false;

    int adj[218][5], adj_sz[218];
    for (int r = 0; r < n_alive; ++r) {
        int j = lines_subset[r], deg = 0;
        for (int k = 0; k < 5; ++k) {
            int c = line_cells[j][k];
            if (avail_empty_mask & BIT(c)) {
                adj[2*r][deg] = adj[2*r+1][deg] = c;
                ++deg;
            }
        }
        if (deg < 2) return false;
        adj_sz[2*r] = adj_sz[2*r+1] = deg;
    }

    int16_t match_u[218], match_v[NUM_CELLS], dist[218], q[218];
    std::fill_n(match_u, n_left, -1);
    std::fill_n(match_v, NUM_CELLS, -1);
    int matched = 0;
    while (true) {
        int q_head = 0, q_tail = 0;
        for (int u = 0; u < n_left; ++u) {
            if (match_u[u] == -1) { dist[u] = 0; q[q_tail++] = u; }
            else dist[u] = -1;
        }
        bool found_aug = false;
        while (q_head < q_tail) {
            int u = q[q_head++];
            for (int k = 0; k < adj_sz[u]; ++k) {
                int next_u = match_v[adj[u][k]];
                if (next_u == -1) found_aug = true;
                else if (dist[next_u] == -1) { dist[next_u] = dist[u] + 1; q[q_tail++] = next_u; }
            }
        }
        if (!found_aug) break;
        auto dfs = [&](auto& self, int u) -> bool {
            for (int k = 0; k < adj_sz[u]; ++k) {
                int v = adj[u][k], next_u = match_v[v];
                if (next_u == -1 || (dist[next_u] == dist[u] + 1 && self(self, next_u))) {
                    match_u[u] = v; match_v[v] = u; return true;
                }
            }
            dist[u] = -1; return false;
        };
        for (int u = 0; u < n_left; ++u) if (match_u[u] == -1 && dfs(dfs, u)) ++matched;
    }
    return matched == n_left;
}

// Orthogonal ES-Pairing Split + Hopcroft-Karp Draw Certificate Checker
// Returns: 0 = not yet certified, 1 = Pure HK, 2 = Kernelized ES (<1), 3 = Orthogonal ES+HK Split
int check_draw_certificate(u128 m, u128 b) {
    int raw_p, kern_p, c4, c3, c2;
    compute_phis(m, b, raw_p, kern_p, c4, c3, c2);
    if (kern_p < 32) return 2; // Kernelized ES < 1.0!

    u128 avail_empty = ~(m | b) & ((u128(1) << 125) - 1);
    int alive_lines[NUM_LINES], line_w[NUM_LINES], line_rem[NUM_LINES], n_alive = 0;
    for (int j = 0; j < NUM_LINES; ++j) {
        if ((line_mask[j] & b) == 0) {
            int mc = popcnt128(line_mask[j] & m);
            alive_lines[n_alive] = j;
            line_w[n_alive] = 1 << mc;
            line_rem[n_alive] = 5 - mc;
            ++n_alive;
        }
    }
    if (n_alive == 0) return 1;
    if (run_hk_subset(alive_lines, n_alive, avail_empty)) return 1; // Pure HK!

    // Try Orthogonal ES-Pairing Split: put lines with fewest empty cells into S_ES (where Phi + max_D < 32),
    // and pair the remaining lines S_pair in avail_empty \ V_ES!
    int order[NUM_LINES];
    for (int i = 0; i < n_alive; ++i) order[i] = i;
    std::sort(order, order + n_alive, [&](int a, int b_idx) {
        return line_rem[a] < line_rem[b_idx];
    });

    bool in_es[NUM_LINES] = {false};
    u128 v_es_mask = 0;
    for (int step = 0; step < n_alive; ++step) {
        int seed = order[step];
        if (in_es[seed]) continue;

        bool cand_es[NUM_LINES];
        std::memcpy(cand_es, in_es, sizeof(in_es));
        cand_es[seed] = true;
        u128 cand_v = v_es_mask | (line_mask[alive_lines[seed]] & avail_empty);

        // Closure: any alive line with < 2 empty cells outside cand_v must also join cand_es
        bool changed = true;
        while (changed) {
            changed = false;
            for (int i = 0; i < n_alive; ++i) {
                if (!cand_es[i]) {
                    u128 rem_out = (line_mask[alive_lines[i]] & avail_empty) & ~cand_v;
                    if (popcnt128(rem_out) < 2) {
                        cand_es[i] = true;
                        cand_v |= (line_mask[alive_lines[i]] & avail_empty);
                        changed = true;
                    }
                }
            }
        }
        int phi_es = 0;
        for (int i = 0; i < n_alive; ++i) if (cand_es[i]) phi_es += line_w[i];
        if (phi_es >= 32) continue;

        int max_d = 0;
        for (int c = 0; c < NUM_CELLS; ++c) {
            if (cand_v & BIT(c)) {
                int d = 0;
                for (int i = 0; i < n_alive; ++i)
                    if (cand_es[i] && (line_mask[alive_lines[i]] & BIT(c))) d += line_w[i];
                if (d > max_d) max_d = d;
            }
        }
        if (phi_es + max_d >= 32) continue;

        // Valid ES subset! Check HK on complement S_pair using avail_empty & ~cand_v
        std::memcpy(in_es, cand_es, sizeof(in_es));
        v_es_mask = cand_v;
        int pair_lines[NUM_LINES], n_pair = 0;
        for (int i = 0; i < n_alive; ++i) if (!in_es[i]) pair_lines[n_pair++] = alive_lines[i];
        if (run_hk_subset(pair_lines, n_pair, avail_empty & ~v_es_mask)) return 3;
    }
    return 0;
}

int main() {
    auto t_start = std::chrono::high_resolution_clock::now();
    init_hypergraph();

    std::cout << "========================================================================\n";
    std::cout << " PHASE-2 ENGINE: POTENTIAL-RIDGE HISTOGRAM & HORIZON SEARCH (t=1..25)\n";
    std::cout << " Hardware Threads: " << omp_get_max_threads() << "\n";
    std::cout << "========================================================================\n\n";

    // -------------------------------------------------------------------------
    // PART 1: Off-Center Opening (H_5^off) Exact Potential Drop at t=1..5
    // -------------------------------------------------------------------------
    std::cout << "=== PART 1: Off-Center Opening x1=(0,0,0) [Corner] Exact DAG (t=1..5) ===\n";
    u128 m_corner = BIT(0);
    int b_corner = es_breaker_move(m_corner, 0); // Takes Center (2,2,2)!
    std::vector<State> off_dag = {canonicalize(m_corner, BIT(b_corner))};

    for (int t = 2; t <= 5; ++t) {
        auto t0 = std::chrono::high_resolution_clock::now();
        int n_threads = omp_get_max_threads();
        std::vector<std::vector<State>> local_m(n_threads);
        #pragma omp parallel
        {
            int tid = omp_get_thread_num();
            #pragma omp for schedule(dynamic, 64)
            for (size_t idx = 0; idx < off_dag.size(); ++idx) {
                u128 m = off_dag[idx].m, b = off_dag[idx].b, occ = m | b;
                int stabs[48], n_stabs = 0;
                for (int g = 0; g < 48; ++g)
                    if (apply_sym(g, m) == m && apply_sym(g, b) == b) stabs[n_stabs++] = g;
                u128 coupled = 0;
                for (int j = 0; j < NUM_LINES; ++j)
                    if ((line_mask[j] & b) == 0 && (line_mask[j] & m) != 0) coupled |= line_mask[j];
                u128 vis = occ;
                for (int e = 0; e < NUM_CELLS; ++e) {
                    u128 bit = BIT(e);
                    if (vis & bit) continue;
                    for (int s = 0; s < n_stabs; ++s) vis |= BIT(sym_perm[stabs[s]][e]);
                    if (coupled & bit) local_m[tid].push_back(canonicalize(m | bit, b));
                }
            }
        }
        std::vector<State> after_m;
        for (auto& v : local_m) after_m.insert(after_m.end(), v.begin(), v.end());
        std::sort(after_m.begin(), after_m.end());
        after_m.erase(std::unique(after_m.begin(), after_m.end()), after_m.end());

        int max_p = 0;
        #pragma omp parallel for reduction(max:max_p)
        for (size_t i = 0; i < after_m.size(); ++i) {
            int rp, kp, c4, c3, c2;
            compute_phis(after_m[i].m, after_m[i].b, rp, kp, c4, c3, c2);
            if (rp > max_p) max_p = rp;
        }
        off_dag.resize(after_m.size());
        #pragma omp parallel for schedule(static)
        for (size_t i = 0; i < after_m.size(); ++i) {
            int bm = es_breaker_move(after_m[i].m, after_m[i].b);
            off_dag[i] = canonicalize(after_m[i].m, after_m[i].b | BIT(bm));
        }
        std::sort(off_dag.begin(), off_dag.end());
        off_dag.erase(std::unique(off_dag.begin(), off_dag.end()), off_dag.end());
        double dt = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - t0).count();
        std::cout << "[Off-Center Corner] t=" << t << " (Ply " << 2*t << "): "
                  << "Canonical DAG = " << std::setw(8) << off_dag.size()
                  << " | max(Phi'_off) = " << std::fixed << std::setprecision(4) << (max_p / 32.0)
                  << " (" << max_p << "/32) [" << std::setprecision(2) << dt << "s]\n";
    }
    std::cout << "\n";

    // -------------------------------------------------------------------------
    // PART 2: Center Opening x1=(2,2,2) Ridge Search from t=1 to t=25 (Ply 50)
    // -------------------------------------------------------------------------
    std::cout << "=== PART 2: Center Opening Ridge Search (t=1..25, Max Beam = 250,000/round) ===\n";
    static constexpr size_t MAX_BEAM = 250000;
    u128 m0 = BIT(CENTER_IDX);
    int b0 = es_breaker_move(m0, 0);
    std::vector<State> beam = {canonicalize(m0, BIT(b0))};

    size_t total_hk_certs = 0, total_es_certs = 0, total_split_certs = 0;

    for (int t = 2; t <= 25; ++t) {
        if (beam.empty()) {
            std::cout << ">>> ALL HIGH-POTENTIAL RIDGE BRANCHES CERTIFIED DRAWN BY ROUND t=" << t-1 << "! <<<\n";
            break;
        }
        auto t0 = std::chrono::high_resolution_clock::now();
        int n_threads = omp_get_max_threads();
        std::vector<std::vector<State>> local_m(n_threads);

        #pragma omp parallel
        {
            int tid = omp_get_thread_num();
            local_m[tid].reserve(beam.size() * 8 / n_threads + 64);
            #pragma omp for schedule(dynamic, 64)
            for (size_t idx = 0; idx < beam.size(); ++idx) {
                u128 m = beam[idx].m, b = beam[idx].b, occ = m | b;
                int stabs[48], n_stabs = 0;
                for (int g = 0; g < 48; ++g)
                    if (apply_sym(g, m) == m && apply_sym(g, b) == b) stabs[n_stabs++] = g;

                // Strong Coupling for t >= 5: prioritize cells lying on >=2 alive lines with Maker stones (2-fans!)
                // or lines with >=2 Maker stones, or top ES-weight cells
                u128 strong_mask = 0, any_coupled = 0;
                int cell_fan_deg[NUM_CELLS] = {0};
                for (int j = 0; j < NUM_LINES; ++j) {
                    if ((line_mask[j] & b) == 0) {
                        int mc = popcnt128(line_mask[j] & m);
                        if (mc >= 1) {
                            any_coupled |= line_mask[j];
                            if (mc >= 2) strong_mask |= line_mask[j];
                            for (int k = 0; k < 5; ++k) ++cell_fan_deg[line_cells[j][k]];
                        }
                    }
                }
                for (int c = 0; c < NUM_CELLS; ++c)
                    if (cell_fan_deg[c] >= 2) strong_mask |= BIT(c);

                u128 target_mask = (t <= 4 || (strong_mask & ~occ) == 0) ? any_coupled : strong_mask;
                u128 vis = occ;
                for (int e = 0; e < NUM_CELLS; ++e) {
                    u128 bit = BIT(e);
                    if (vis & bit) continue;
                    for (int s = 0; s < n_stabs; ++s) vis |= BIT(sym_perm[stabs[s]][e]);
                    if (target_mask & bit) {
                        local_m[tid].push_back(canonicalize(m | bit, b));
                    }
                }
            }
        }

        std::vector<State> after_m;
        for (auto& v : local_m) {
            after_m.insert(after_m.end(), v.begin(), v.end());
            std::vector<State>().swap(v);
        }
        std::sort(after_m.begin(), after_m.end());
        after_m.erase(std::unique(after_m.begin(), after_m.end()), after_m.end());

        // Compute Phi' histogram before Breaker moves
        int max_p = 0, min_p = 999999, max_c4 = 0, max_c3 = 0;
        int top_ridge_cnt = 0; // states within 2/32 of max_p
        #pragma omp parallel for reduction(max:max_p, max_c4, max_c3) reduction(min:min_p)
        for (size_t i = 0; i < after_m.size(); ++i) {
            int rp, kp, c4, c3, c2;
            compute_phis(after_m[i].m, after_m[i].b, rp, kp, c4, c3, c2);
            if (rp > max_p) max_p = rp;
            if (rp < min_p) min_p = rp;
            if (c4 > max_c4) max_c4 = c4;
            if (c3 > max_c3) max_c3 = c3;
        }
        #pragma omp parallel for reduction(+:top_ridge_cnt)
        for (size_t i = 0; i < after_m.size(); ++i) {
            int rp, kp, c4, c3, c2;
            compute_phis(after_m[i].m, after_m[i].b, rp, kp, c4, c3, c2);
            if (rp >= max_p - 2) ++top_ridge_cnt;
        }

        // Breaker replies -> deduplicate
        std::vector<State> post_b(after_m.size());
        #pragma omp parallel for schedule(static)
        for (size_t i = 0; i < after_m.size(); ++i) {
            int bm = es_breaker_move(after_m[i].m, after_m[i].b);
            post_b[i] = canonicalize(after_m[i].m, after_m[i].b | BIT(bm));
        }
        std::sort(post_b.begin(), post_b.end());
        post_b.erase(std::unique(post_b.begin(), post_b.end()), post_b.end());

        // Check Draw Certificates (for t >= 8) and score survivors for ridge retention
        struct ScoredState {
            int score;
            State st;
            bool operator<(const ScoredState& o) const { return score > o.score; }
        };
        std::vector<std::vector<ScoredState>> surv_local(n_threads);
        size_t hk_c = 0, es_c = 0, sp_c = 0;

        #pragma omp parallel reduction(+:hk_c, es_c, sp_c)
        {
            int tid = omp_get_thread_num();
            #pragma omp for schedule(dynamic, 64)
            for (size_t i = 0; i < post_b.size(); ++i) {
                u128 m = post_b[i].m, b = post_b[i].b;
                if (t >= 8) {
                    int cert = check_draw_certificate(m, b);
                    if (cert == 1) { ++hk_c; continue; }
                    if (cert == 2) { ++es_c; continue; }
                    if (cert == 3) { ++sp_c; continue; }
                }
                int rp, kp, c4, c3, c2;
                compute_phis(m, b, rp, kp, c4, c3, c2);
                int sc = rp * 1000 + c4 * 50000 + c3 * 500 + c2 * 20;
                surv_local[tid].push_back({sc, post_b[i]});
            }
        }
        total_hk_certs += hk_c; total_es_certs += es_c; total_split_certs += sp_c;

        std::vector<ScoredState> all_surv;
        for (auto& v : surv_local) all_surv.insert(all_surv.end(), v.begin(), v.end());
        if (all_surv.size() > MAX_BEAM) {
            std::nth_element(all_surv.begin(), all_surv.begin() + MAX_BEAM, all_surv.end());
            all_surv.resize(MAX_BEAM);
        }
        beam.resize(all_surv.size());
        for (size_t i = 0; i < all_surv.size(); ++i) beam[i] = all_surv[i].st;

        double dt = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - t0).count();
        std::cout << "t=" << std::setw(2) << t << " (Ply " << std::setw(2) << 2*t << "): "
                  << "DAG=" << std::setw(8) << post_b.size()
                  << " | RidgeTop=" << std::setw(6) << top_ridge_cnt
                  << " | Phi'=" << std::fixed << std::setprecision(4) << (max_p/32.0) << "(" << std::setw(3) << max_p << "/32)"
                  << " | c4=" << max_c4 << ",c3=" << max_c3
                  << " | Pruned[HK=" << hk_c << ",Split=" << sp_c << ",ES=" << es_c << "]"
                  << " | Kept=" << beam.size() << " [" << std::setprecision(2) << dt << "s]\n";
    }

    double tot = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - t_start).count();
    std::cout << "\n========================================================================\n";
    std::cout << "Total Draw Certificates Issued: HK=" << total_hk_certs
              << ", Orthogonal_Split=" << total_split_certs
              << ", Kernelized_ES=" << total_es_certs
              << " [Total Time: " << std::fixed << std::setprecision(2) << tot << "s]\n";
    std::cout << "========================================================================\n";
    return 0;
}