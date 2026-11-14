// qubic5_phase3.cpp
// Phase-3 Engine: Lemma-1 Fork-Pivot / 2-Fan Breaker vs. High-Speed Ridge Search (t=1..25)
// Compile: clang++ -O3 -march=native -fopenmp -std=c++20 qubic5_phase3.cpp -o qubic5_phase3

#include <iostream>
#include <vector>
#include <array>
#include <algorithm>
#include <cstdint>
#include <cmath>
#include <chrono>
#include <iomanip>
#include <cstring>
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

// Upgraded Lemma-1 Fork-Pivot & 2-Fan Coupled Breaker
// Fixes the 8+8=16 < 8+4+4+4=20 Fork-Pivot blindness of pure base-2 ES!
int fan_coupled_breaker_move(u128 m, u128 b) {
    u128 occ = m | b;
    int line_mc[NUM_LINES];
    u128 threat4_mask = 0;

    for (int j = 0; j < NUM_LINES; ++j) {
        if ((line_mask[j] & b) != 0) {
            line_mc[j] = -1;
        } else {
            int mc = popcnt128(line_mask[j] & m);
            line_mc[j] = mc;
            if (mc == 4) threat4_mask |= (line_mask[j] & ~occ);
        }
    }

    int best_cell = -1;
    int best_score = -1;
    int best_deg = -1;

    for (int i = 0; i < NUM_CELLS; ++i) {
        u128 bit = BIT(i);
        if (occ & bit) continue;
        if (threat4_mask != 0 && !(threat4_mask & bit)) continue;

        int es_score = 0;
        int k3 = 0, k2 = 0, k1 = 0;
        for (int j : pt_lines[i]) {
            int mc = line_mc[j];
            if (mc < 0) continue;
            es_score += (1 << mc);
            if (mc == 3) ++k3;
            else if (mc == 2) ++k2;
            else if (mc == 1) ++k1;
        }

        // Lemma-1 2-Fan Coupling Bonus:
        // - k3 >= 2 is an immediate next-turn double-4-in-a-row Fork Pivot (+500 bonus per pair)
        // - k3 >= 1 and k2 >= 1 is a 1-step precursor fork (+40 bonus per pair)
        // - k2 >= 2 is a 2-in-a-row 2-fan intersection (+8 bonus per pair)
        int fan_bonus = 500 * (k3 * (k3 - 1) / 2)
                      +  40 * (k3 * k2)
                      +   8 * (k2 * (k2 - 1) / 2)
                      +   2 * (k2 * k1);
        int total_score = es_score + fan_bonus;

        if (total_score > best_score || (total_score == best_score && degs[i] > best_deg)) {
            best_score = total_score;
            best_deg = degs[i];
            best_cell = i;
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

int check_draw_certificate(u128 m, u128 b, int kern_p) {
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
    if (run_hk_subset(alive_lines, n_alive, avail_empty)) return 1;

    int order[NUM_LINES];
    for (int i = 0; i < n_alive; ++i) order[i] = i;
    std::sort(order, order + n_alive, [&](int a, int b_idx) { return line_rem[a] < line_rem[b_idx]; });

    bool in_es[NUM_LINES] = {false};
    u128 v_es_mask = 0;
    for (int step = 0; step < n_alive; ++step) {
        int seed = order[step];
        if (in_es[seed]) continue;
        bool cand_es[NUM_LINES];
        std::memcpy(cand_es, in_es, sizeof(in_es));
        cand_es[seed] = true;
        u128 cand_v = v_es_mask | (line_mask[alive_lines[seed]] & avail_empty);
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
    std::cout << " PHASE-3 ENGINE: LEMMA-1 FORK-PIVOT BREAKER (B_Fan) RIDGE TEST (t=1..25)\n";
    std::cout << " Hardware Threads: " << omp_get_max_threads() << " | Beam Width: 250,000\n";
    std::cout << "========================================================================\n\n";

    static constexpr size_t MAX_BEAM = 250000;
    u128 m0 = BIT(CENTER_IDX);
    int b0 = fan_coupled_breaker_move(m0, 0);
    std::vector<State> beam = {canonicalize(m0, BIT(b0))};

    size_t total_hk = 0, total_es = 0, total_split = 0;
    int global_max_c4 = 0;

    for (int t = 2; t <= 25; ++t) {
        if (beam.empty()) {
            std::cout << ">>> 100% OF RIDGE BRANCHES CERTIFIED DRAWN BY ROUND t=" << t-1 << "! <<<\n";
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

        int max_p = 0, max_c4 = 0, max_c3 = 0;
        #pragma omp parallel for reduction(max:max_p, max_c4, max_c3)
        for (size_t i = 0; i < after_m.size(); ++i) {
            int rp, kp, c4, c3, c2;
            compute_phis(after_m[i].m, after_m[i].b, rp, kp, c4, c3, c2);
            if (rp > max_p) max_p = rp;
            if (c4 > max_c4) max_c4 = c4;
            if (c3 > max_c3) max_c3 = c3;
        }
        if (max_c4 > global_max_c4) global_max_c4 = max_c4;

        int top_ridge_cnt = 0;
        #pragma omp parallel for reduction(+:top_ridge_cnt)
        for (size_t i = 0; i < after_m.size(); ++i) {
            int rp, kp, c4, c3, c2;
            compute_phis(after_m[i].m, after_m[i].b, rp, kp, c4, c3, c2);
            if (rp >= max_p - 2) ++top_ridge_cnt;
        }

        // Breaker replies using B_Fan -> deduplicate
        std::vector<State> post_b(after_m.size());
        #pragma omp parallel for schedule(static)
        for (size_t i = 0; i < after_m.size(); ++i) {
            int bm = fan_coupled_breaker_move(after_m[i].m, after_m[i].b);
            post_b[i] = canonicalize(after_m[i].m, after_m[i].b | BIT(bm));
        }
        std::sort(post_b.begin(), post_b.end());
        post_b.erase(std::unique(post_b.begin(), post_b.end()), post_b.end());

        // Fast Score FIRST (0.1s), then check Draw Certificates on top candidates!
        struct ScoredState {
            int score;
            int kern_p;
            State st;
            bool operator<(const ScoredState& o) const { return score > o.score; }
        };
        std::vector<ScoredState> scored(post_b.size());
        #pragma omp parallel for schedule(static)
        for (size_t i = 0; i < post_b.size(); ++i) {
            int rp, kp, c4, c3, c2;
            compute_phis(post_b[i].m, post_b[i].b, rp, kp, c4, c3, c2);
            int sc = rp * 1000 + c4 * 50000 + c3 * 500 + c2 * 20;
            scored[i] = {sc, kp, post_b[i]};
        }

        // Keep top 600,000 candidates by score to test certificates and fill MAX_BEAM=250,000
        size_t cand_limit = std::min(scored.size(), size_t(600000));
        if (scored.size() > cand_limit) {
            std::nth_element(scored.begin(), scored.begin() + cand_limit, scored.end());
            scored.resize(cand_limit);
        }
        std::sort(scored.begin(), scored.end());

        std::vector<int> cert_res(cand_limit, 0);
        size_t hk_c = 0, es_c = 0, sp_c = 0;
        if (t >= 8) {
            #pragma omp parallel for schedule(dynamic, 64) reduction(+:hk_c, es_c, sp_c)
            for (size_t i = 0; i < cand_limit; ++i) {
                int c = check_draw_certificate(scored[i].st.m, scored[i].st.b, scored[i].kern_p);
                cert_res[i] = c;
                if (c == 1) ++hk_c;
                else if (c == 2) ++es_c;
                else if (c == 3) ++sp_c;
            }
        }
        total_hk += hk_c; total_es += es_c; total_split += sp_c;

        beam.clear();
        beam.reserve(MAX_BEAM);
        for (size_t i = 0; i < cand_limit && beam.size() < MAX_BEAM; ++i) {
            if (cert_res[i] == 0) beam.push_back(scored[i].st);
        }

        double dt = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - t0).count();
        std::cout << "t=" << std::setw(2) << t << " (Ply " << std::setw(2) << 2*t << "): "
                  << "DAG=" << std::setw(7) << post_b.size()
                  << " | RidgeTop=" << std::setw(5) << top_ridge_cnt
                  << " | Phi'=" << std::fixed << std::setprecision(4) << (max_p/32.0) << "(" << std::setw(3) << max_p << "/32)"
                  << " | c4=" << max_c4 << ",c3=" << max_c3
                  << " | Cert[HK=" << hk_c << ",Sp=" << sp_c << ",ES=" << es_c << "]"
                  << " | Kept=" << beam.size() << " [" << std::setprecision(2) << dt << "s]\n";
    }

    double tot = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - t_start).count();
    std::cout << "\n========================================================================\n";
    std::cout << "Global Max Simultaneous 4-in-a-rows (c4) vs B_Fan : " << global_max_c4 << " (Fork requires >= 2)\n";
    std::cout << "Total Draw Certificates (Top Ridge): HK=" << total_hk
              << ", Split=" << total_split << ", ES=" << total_es
              << " [Total Time: " << std::fixed << std::setprecision(2) << tot << "s]\n";
    std::cout << "========================================================================\n";
    return 0;
}