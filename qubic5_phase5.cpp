// qubic5_phase5.cpp
// Phase-5 Engine: Pure Base-2 ES + Clean Lemma-1 Fork-Pivot Guard -> Full Ridge Extinction (t=1..45)
// Compile: clang++ -O3 -march=native -fopenmp -std=c++20 qubic5_phase5.cpp -o qubic5_phase5

#include <iostream>
#include <vector>
#include <array>
#include <algorithm>
#include <cstdint>
#include <cmath>
#include <chrono>
#include <iomanip>
#include <cstring>
#include <string>
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

// Hybrid Base-2 Erdos-Selfridge + Clean Lemma-1 Fork-Pivot Guard:
// - Uses exact Base-2 weights {1, 2, 4, 8, 16} to guarantee monotonic Phi'_t drop & early HK pairing
// - Activates Fork-Pivot guard ONLY when k3 >= 2 (immediate next-move double-4-in-a-row)
//   or (k3 == 1 && k2 >= 2) (2-fan fork setup where 8 + 4 + 4 = 16 would otherwise lose to 20)
int hybrid_es_pivot_breaker(u128 m, u128 b) {
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

    int best_cell = -1, best_score = -1, best_deg = -1;
    for (int i = 0; i < NUM_CELLS; ++i) {
        u128 bit = BIT(i);
        if (occ & bit) continue;
        if (threat4_mask != 0 && !(threat4_mask & bit)) continue;

        int score = 0, k3 = 0, k2 = 0;
        for (int j : pt_lines[i]) {
            int mc = line_mc[j];
            if (mc >= 0) {
                score += (1 << mc); // Pure Base-2 ES weight: 1, 2, 4, 8, 16
                if (mc == 3) ++k3;
                else if (mc == 2) ++k2;
            }
        }
        // Clean Lemma-1 Fork-Pivot Guard (Zero distortion when k3 == 0!):
        if (k3 >= 2) score += 5000 * k3;
        else if (k3 == 1 && k2 >= 2) score += 16; // Boosts (1x3 + 2x2) from 16 to 32 so it beats scattered 1-stone lines

        if (score > best_score || (score == best_score && degs[i] > best_deg)) {
            best_score = score; best_deg = degs[i]; best_cell = i;
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
    int alive_lines[NUM_LINES], n_alive = 0;
    for (int j = 0; j < NUM_LINES; ++j) {
        if ((line_mask[j] & b) == 0) alive_lines[n_alive++] = j;
    }
    if (n_alive == 0 || run_hk_subset(alive_lines, n_alive, avail_empty)) return 1;
    return 0;
}

bool can_maker_force_win_2p(u128 m, u128 b, int rounds_left, int breaker_branch_k) {
    u128 occ = m | b;
    u128 threat4_cells = 0;
    for (int j = 0; j < NUM_LINES; ++j) {
        if ((line_mask[j] & b) == 0 && popcnt128(line_mask[j] & m) == 4) {
            threat4_cells |= (line_mask[j] & ~occ);
        }
    }
    if (popcnt128(threat4_cells) >= 2) return true;
    if (rounds_left <= 0) return false;

    std::vector<int> b_cands;
    if (popcnt128(threat4_cells) == 1) {
        for (int i = 0; i < NUM_CELLS; ++i) if (threat4_cells & BIT(i)) b_cands.push_back(i);
    } else {
        struct Cand { int sc; int cell; };
        std::vector<Cand> sc_list;
        for (int i = 0; i < NUM_CELLS; ++i) {
            if (occ & BIT(i)) continue;
            int s = 0, k3 = 0;
            for (int j : pt_lines[i]) {
                if ((line_mask[j] & b) == 0) {
                    int mc = popcnt128(line_mask[j] & m);
                    s += (1 << (2 * mc));
                    if (mc == 3) ++k3;
                }
            }
            if (k3 >= 2) s += 10000;
            sc_list.push_back({s, i});
        }
        std::sort(sc_list.begin(), sc_list.end(), [](const Cand& a, const Cand& b){ return a.sc > b.sc; });
        for (int i = 0; i < std::min<int>(breaker_branch_k, sc_list.size()); ++i)
            b_cands.push_back(sc_list[i].cell);
    }

    for (int bm : b_cands) {
        u128 b_next = b | BIT(bm);
        u128 occ_next = m | b_next;
        bool maker_wins_against_bm = false;
        for (int mm = 0; mm < NUM_CELLS; ++mm) {
            if (occ_next & BIT(mm)) continue;
            bool relevant = false;
            for (int j : pt_lines[mm]) {
                if ((line_mask[j] & b_next) == 0 && popcnt128(line_mask[j] & m) >= 2) {
                    relevant = true; break;
                }
            }
            if (!relevant) continue;
            if (can_maker_force_win_2p(m | BIT(mm), b_next, rounds_left - 1, breaker_branch_k)) {
                maker_wins_against_bm = true;
                break;
            }
        }
        if (!maker_wins_against_bm) return false;
    }
    return true;
}

void run_extinction_search(const std::vector<State>& init_beam, const std::string& label, size_t max_beam, int min_cert_t) {
    std::cout << "========================================================================\n";
    std::cout << " EXTINCTION SEARCH: " << label << " (Max Beam = " << max_beam << ")\n";
    std::cout << "========================================================================\n";
    auto t_start = std::chrono::high_resolution_clock::now();

    std::vector<State> beam = init_beam;
    int global_max_c4 = 0, global_max_c3 = 0;
    size_t total_hk = 0, total_es = 0;
    int unrefuted_forks = 0, refuted_forks = 0;
    int extinction_round = -1;

    for (int t = 2; t <= 45; ++t) {
        if (beam.empty()) {
            extinction_round = t - 1;
            std::cout << ">>> 100% OF RIDGE BRANCHES EXTINGUISHED (CERTIFIED DRAWN) AT ROUND t=" << extinction_round
                      << " (Ply " << 2*extinction_round << ")! <<<\n";
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
                if ((target_mask & ~occ) == 0) continue; // All lines dead!
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

        if (after_m.empty()) {
            extinction_round = t;
            std::cout << ">>> 100% OF RIDGE BRANCHES EXTINGUISHED AT ROUND t=" << t << "! <<<\n";
            break;
        }

        int max_p = 0, max_c4 = 0, max_c3 = 0;
        std::vector<State> c4_fork_states;
        #pragma omp parallel for reduction(max:max_p, max_c4, max_c3)
        for (size_t i = 0; i < after_m.size(); ++i) {
            int rp, kp, c4, c3, c2;
            compute_phis(after_m[i].m, after_m[i].b, rp, kp, c4, c3, c2);
            if (rp > max_p) max_p = rp;
            if (c4 > max_c4) max_c4 = c4;
            if (c3 > max_c3) max_c3 = c3;
            if (c4 >= 2) {
                #pragma omp critical
                if (c4_fork_states.size() < 25) c4_fork_states.push_back(after_m[i]);
            }
        }
        if (max_c4 > global_max_c4) global_max_c4 = max_c4;
        if (max_c3 > global_max_c3) global_max_c3 = max_c3;

        if (!c4_fork_states.empty() && unrefuted_forks + refuted_forks < 50) {
            for (const auto& st : c4_fork_states) {
                bool forced_from_prev = true;
                for (int i = 0; i < NUM_CELLS; ++i) {
                    if (st.m & BIT(i)) {
                        u128 m_prev = st.m & ~BIT(i);
                        bool any_b_refutes = false;
                        for (int bi = 0; bi < NUM_CELLS; ++bi) {
                            if (st.b & BIT(bi)) {
                                u128 b_prev = st.b & ~BIT(bi);
                                if (!can_maker_force_win_2p(m_prev, b_prev, 2, 5)) {
                                    any_b_refutes = true; break;
                                }
                            }
                        }
                        if (any_b_refutes) { forced_from_prev = false; break; }
                    }
                }
                if (forced_from_prev) ++unrefuted_forks;
                else ++refuted_forks;
            }
        }

        std::vector<State> post_b(after_m.size());
        #pragma omp parallel for schedule(static)
        for (size_t i = 0; i < after_m.size(); ++i) {
            int bm = hybrid_es_pivot_breaker(after_m[i].m, after_m[i].b);
            post_b[i] = canonicalize(after_m[i].m, after_m[i].b | BIT(bm));
        }
        std::sort(post_b.begin(), post_b.end());
        post_b.erase(std::unique(post_b.begin(), post_b.end()), post_b.end());

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

        size_t cand_limit = std::min(scored.size(), max_beam * 2);
        if (scored.size() > cand_limit) {
            std::nth_element(scored.begin(), scored.begin() + cand_limit, scored.end());
            scored.resize(cand_limit);
        }
        std::sort(scored.begin(), scored.end());

        std::vector<int> cert_res(cand_limit, 0);
        size_t hk_c = 0, es_c = 0;
        if (t >= min_cert_t) {
            #pragma omp parallel for schedule(dynamic, 64) reduction(+:hk_c, es_c)
            for (size_t i = 0; i < cand_limit; ++i) {
                int c = check_draw_certificate(scored[i].st.m, scored[i].st.b, scored[i].kern_p);
                cert_res[i] = c;
                if (c == 1) ++hk_c;
                else if (c == 2) ++es_c;
            }
        }
        total_hk += hk_c; total_es += es_c;

        beam.clear();
        beam.reserve(max_beam);
        for (size_t i = 0; i < cand_limit && beam.size() < max_beam; ++i) {
            if (cert_res[i] == 0) beam.push_back(scored[i].st);
        }

        double dt = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - t0).count();
        std::cout << "t=" << std::setw(2) << t << " (Ply " << std::setw(2) << 2*t << "): "
                  << "DAG=" << std::setw(7) << post_b.size()
                  << " | Phi'=" << std::fixed << std::setprecision(4) << (max_p/32.0) << "(" << std::setw(3) << max_p << "/32)"
                  << " | c4=" << max_c4 << ",c3=" << std::setw(2) << max_c3
                  << " | Cert[HK=" << std::setw(6) << hk_c << ",ES=" << std::setw(6) << es_c << "]"
                  << " | Kept=" << std::setw(6) << beam.size() << " [" << std::setprecision(2) << dt << "s]\n";
    }

    double tot = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - t_start).count();
    std::cout << "--> SUMMARY [" << label << "]: Extinction_Round=" << extinction_round
              << " | Global_Max_c4=" << global_max_c4
              << " | 2P-Refuted=" << refuted_forks << ", Unrefuted=" << unrefuted_forks
              << " | Total_Certs[HK=" << total_hk << ", ES=" << total_es << "] (" << tot << "s)\n\n";
}

int main() {
    init_hypergraph();

    // 1. Build all 9 Off-Center Opening Orbits (H_5^off)
    std::vector<State> off_init;
    for (int i = 0; i < NUM_CELLS; ++i) {
        if (i == CENTER_IDX) continue;
        u128 m0 = BIT(i);
        int b0 = hybrid_es_pivot_breaker(m0, 0);
        off_init.push_back(canonicalize(m0, BIT(b0)));
    }
    std::sort(off_init.begin(), off_init.end());
    off_init.erase(std::unique(off_init.begin(), off_init.end()), off_init.end());

    // Run 1: All 9 Off-Center Openings (H_5^off) through complete ridge extinction!
    run_extinction_search(off_init, "RUN 1: All 9 Off-Center Openings (H_5^off)", 150000, 10);

    // Run 2: Principal Center Opening x1=(2,2,2) through complete ridge extinction!
    u128 mc = BIT(CENTER_IDX);
    int bc = hybrid_es_pivot_breaker(mc, 0);
    std::vector<State> center_init = {canonicalize(mc, BIT(bc))};
    run_extinction_search(center_init, "RUN 2: Principal Center Opening x1=(2,2,2)", 150000, 12);

    return 0;
}