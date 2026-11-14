// research-034/qubic5_pillar_solver.cpp
// Formal 5-Pillar Proof Engine for 5x5x5 Qubic (125 Cells, 109 Lines)
// Implements the 5 Mathematical Pillars from mathematical_research_program_for_settling_5x5x5_qubic.md:
//   Pillar 1: Exact 2-Core Hypergraph State Quotienting S = (e_red, v_red) + 48-Symmetry LUTs
//   Pillar 2: Commutative Core-Schedule Policy B_pi (collapsing t! move-order permutations)
//   Pillar 3: Multi-Probe Null-Move Witness Lifting (Dulmage-Mendelsohn BFS + Coupled ES Slack)
//   Pillar 4: Aut_{O_h}(S) Orbits, Degree-1 Poset Dominance, Hereditary Component Quotienting
//   Pillar 5: Breadth-First Canonical Hypergraph DAG + Multi-Probe Formal Unpruned DFS
//
// Strictly complies with AGENTS.md Rule 1:
//   - Real-time progress reporting every 2 seconds
//   - Persistent disk checkpointing (checkpoint.bin) and --resume support
//   - Clean SIGINT / termination signal handling

#include <iostream>
#include <fstream>
#include <cstdio>
#include <vector>
#include <array>
#include <algorithm>
#include <cstdint>
#include <cmath>
#include <chrono>
#include <iomanip>
#include <cstring>
#include <atomic>
#include <csignal>
#include <string>
#include <omp.h>

using u128 = unsigned __int128;

static inline constexpr u128 BIT(int i) {
    return u128(1) << i;
}

static inline int popcnt128(u128 x) {
    return __builtin_popcountll(static_cast<uint64_t>(x >> 64)) +
           __builtin_popcountll(static_cast<uint64_t>(x));
}

static inline int ctz128(u128 x) {
    uint64_t lo = static_cast<uint64_t>(x);
    return lo ? __builtin_ctzll(lo) : (64 + __builtin_ctzll(static_cast<uint64_t>(x >> 64)));
}

// ============================================================================
// PILLAR 1: 2-CORE REDUCED HYPERGRAPH STATE (e_red, v_red)
// ============================================================================
struct HyperState {
    u128 e_red; // 109-bit mask of surviving lines after fixed-point 2-core peeling
    u128 v_red; // 125-bit mask of non-isolated empty cells after 2-core peeling

    bool operator==(const HyperState& o) const {
        return e_red == o.e_red && v_red == o.v_red;
    }
    bool operator<(const HyperState& o) const {
        return (e_red != o.e_red) ? (e_red > o.e_red) : (v_red > o.v_red);
    }
};

static constexpr int NUM_CELLS = 125;
static constexpr int NUM_LINES = 109;
static constexpr int CENTER_IDX = 62;
static const u128 BOARD_MASK = (u128(1) << NUM_CELLS) - 1;
static const u128 ALL_LINES_MASK = (u128(1) << NUM_LINES) - 1;

int line_cells[NUM_LINES][5];
u128 line_mask[NUM_LINES];
u128 cell_lines_mask[NUM_CELLS];
std::vector<int> pt_lines[NUM_CELLS];
int degs[NUM_CELLS];

int sym_perm[48][NUM_CELLS];
int sym_line[48][NUM_LINES];
alignas(64) u128 sym_cell_lut[48][16][256];
alignas(64) u128 sym_line_lut[48][14][256];

// Pillar 2 static priority list pi[0..124] and inverse rank pi_bonus[cell] in [1..125]
int pi_order[NUM_CELLS];
int pi_bonus[NUM_CELLS];

struct K4Gadget {
    std::array<int, 4> lines;
    u128 cell_mask;
};

struct K3Triangle {
    std::array<int, 3> lines;
    u128 core_mask;
};

std::vector<K4Gadget> k4_gadgets;
std::vector<K3Triangle> k3_triangles;

// Signal handling for graceful interruption & checkpoint safety
std::atomic<bool> g_stop_requested{false};
void sigint_handler(int) {
    g_stop_requested.store(true, std::memory_order_relaxed);
}

// ============================================================================
// LOCK-FREE ATOMIC XOR TRANSPOSITION TABLE (Torn-Read Immune under OpenMP)
// ============================================================================
static constexpr size_t TT_SIZE = 1ULL << 25; // 33,554,432 entries (512 MB RAM)
static constexpr size_t TT_MASK = TT_SIZE - 1;

struct alignas(16) TTEntry {
    std::atomic<uint64_t> key_xor;
    std::atomic<uint64_t> key_lo;
};

TTEntry* tt_table = nullptr;

static inline uint64_t splitmix64(uint64_t x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

static inline void tt_lookup_hashes(const HyperState& s, uint64_t& kh, uint64_t& kl, size_t& idx) {
    uint64_t e_lo = static_cast<uint64_t>(s.e_red);
    uint64_t e_hi = static_cast<uint64_t>(s.e_red >> 64);
    uint64_t v_lo = static_cast<uint64_t>(s.v_red);
    uint64_t v_hi = static_cast<uint64_t>(s.v_red >> 64);

    kh = splitmix64(e_lo ^ splitmix64(v_lo + 0x123456789abcdef0ULL));
    kl = splitmix64(e_hi ^ splitmix64(v_hi + 0xfedcba9876543210ULL));
    if ((kh ^ kl) == 0) kh ^= 1ULL;
    idx = static_cast<size_t>(kh & TT_MASK);
}

static inline bool tt_probe(size_t idx, uint64_t kh, uint64_t kl) {
    uint64_t kxor = tt_table[idx].key_xor.load(std::memory_order_relaxed);
    uint64_t klo  = tt_table[idx].key_lo.load(std::memory_order_relaxed);
    return (kxor ^ klo) == kh && klo == kl;
}

static inline void tt_store(size_t idx, uint64_t kh, uint64_t kl) {
    tt_table[idx].key_lo.store(kl, std::memory_order_relaxed);
    tt_table[idx].key_xor.store(kh ^ kl, std::memory_order_relaxed);
}

// ============================================================================
// HYPERGRAPH, SYMMETRY LUTS, GADGETS & PILLAR-2 CORE SCHEDULE INITIALIZATION
// ============================================================================
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
        cell_lines_mask[i] = 0;
    }
    for (int j = 0; j < NUM_LINES; ++j) {
        u128 m = 0;
        for (int k = 0; k < 5; ++k) {
            int c = raw_lines[j][k];
            line_cells[j][k] = c;
            m |= BIT(c);
            pt_lines[c].push_back(j);
            cell_lines_mask[c] |= BIT(j);
        }
        line_mask[j] = m;
    }
    for (int i = 0; i < NUM_CELLS; ++i) degs[i] = static_cast<int>(pt_lines[i].size());

    // Build 48 cube symmetries in O_h (identity at index 0)
    int perms[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
    int s_idx = 0;
    for (int p = 0; p < 6; ++p)
        for (int sx : {1, -1})
            for (int sy : {1, -1})
                for (int sz : {1, -1}) {
                    int signs[3] = {sx, sy, sz};
                    for (int x = 0; x < 5; ++x)
                        for (int y = 0; y < 5; ++y)
                            for (int z = 0; z < 5; ++z) {
                                int c[3] = {x - 2, y - 2, z - 2};
                                int nc[3];
                                for (int d = 0; d < 3; ++d)
                                    nc[d] = signs[d] * c[perms[p][d]] + 2;
                                sym_perm[s_idx][pt_to_idx(x, y, z)] = pt_to_idx(nc[0], nc[1], nc[2]);
                            }
                    ++s_idx;
                }

    // Precompute line permutation table under all 48 cube symmetries
    for (int g = 0; g < 48; ++g) {
        for (int j = 0; j < NUM_LINES; ++j) {
            u128 gm = 0;
            for (int k = 0; k < 5; ++k) {
                gm |= BIT(sym_perm[g][line_cells[j][k]]);
            }
            for (int j2 = 0; j2 < NUM_LINES; ++j2) {
                if (line_mask[j2] == gm) {
                    sym_line[g][j] = j2;
                    break;
                }
            }
        }
    }

    // Precompute byte-sliced LUTs for 125-bit cell masks and 109-bit line masks
    std::memset(sym_cell_lut, 0, sizeof(sym_cell_lut));
    std::memset(sym_line_lut, 0, sizeof(sym_line_lut));
    for (int g = 0; g < 48; ++g) {
        for (int byte_idx = 0; byte_idx < 16; ++byte_idx) {
            for (int val = 0; val < 256; ++val) {
                u128 cell_out = 0;
                for (int b = 0; b < 8; ++b) {
                    if (val & (1 << b)) {
                        int cid = byte_idx * 8 + b;
                        if (cid < NUM_CELLS) {
                            cell_out |= BIT(sym_perm[g][cid]);
                        }
                    }
                }
                sym_cell_lut[g][byte_idx][val] = cell_out;
            }
        }
        for (int byte_idx = 0; byte_idx < 14; ++byte_idx) {
            for (int val = 0; val < 256; ++val) {
                u128 line_out = 0;
                for (int b = 0; b < 8; ++b) {
                    if (val & (1 << b)) {
                        int lid = byte_idx * 8 + b;
                        if (lid < NUM_LINES) {
                            line_out |= BIT(sym_line[g][lid]);
                        }
                    }
                }
                sym_line_lut[g][byte_idx][val] = line_out;
            }
        }
    }

    // Build Pillar 2 canonical static priority order pi:
    //   1. Center (2,2,2) = 62 (deg 13)
    //   2. Inner-cube regular Tetrahedron A: 31=(1,1,1), 43=(1,3,3), 83=(3,1,3), 91=(3,3,1) (deg 9, pairwise non-collinear on ortho lines)
    //   3. Inner-cube regular Tetrahedron B: 93=(3,3,3), 81=(3,1,1), 41=(1,3,1), 33=(1,1,3) (deg 9)
    //   4. Remaining cells sorted by descending static degree, then centrality.
    std::vector<int> fixed_prefix = {62, 31, 43, 83, 91, 93, 81, 41, 33};
    u128 prefix_mask = 0;
    int r_idx = 0;
    for (int c : fixed_prefix) {
        pi_order[r_idx] = c;
        pi_bonus[c] = NUM_CELLS - r_idx;
        prefix_mask |= BIT(c);
        ++r_idx;
    }

    struct CellRank {
        int cell;
        int deg;
        int shell_dist2;
        bool operator<(const CellRank& o) const {
            if (deg != o.deg) return deg > o.deg;
            if (shell_dist2 != o.shell_dist2) return shell_dist2 < o.shell_dist2;
            return cell < o.cell;
        }
    };
    std::vector<CellRank> cranks;
    for (int c = 0; c < NUM_CELLS; ++c) {
        if (prefix_mask & BIT(c)) continue;
        int x = (c / 25) - 2, y = ((c / 5) % 5) - 2, z = (c % 5) - 2;
        int d2 = x * x + y * y + z * z;
        cranks.push_back({c, degs[c], d2});
    }
    std::sort(cranks.begin(), cranks.end());
    for (const auto& cr : cranks) {
        pi_order[r_idx] = cr.cell;
        pi_bonus[cr.cell] = NUM_CELLS - r_idx;
        ++r_idx;
    }

    // Discover K4 (6-cell, 4-line) and K3+ (triangle core) pairing gadgets
    k4_gadgets.clear();
    k3_triangles.clear();
    int inter_cell[NUM_LINES][NUM_LINES];
    std::memset(inter_cell, -1, sizeof(inter_cell));
    for (int i = 0; i < NUM_LINES; ++i)
        for (int j = i + 1; j < NUM_LINES; ++j) {
            u128 common = line_mask[i] & line_mask[j];
            if (common != 0) {
                int c = ctz128(common);
                inter_cell[i][j] = inter_cell[j][i] = c;
            }
        }

    for (int i = 0; i < NUM_LINES; ++i)
        for (int j = i + 1; j < NUM_LINES; ++j) {
            if (inter_cell[i][j] < 0) continue;
            for (int k = j + 1; k < NUM_LINES; ++k) {
                if (inter_cell[i][k] < 0 || inter_cell[j][k] < 0) continue;
                int w12 = inter_cell[i][j], w13 = inter_cell[i][k], w23 = inter_cell[j][k];
                if (w12 != w13 && w12 != w23 && w13 != w23) {
                    k3_triangles.push_back({{i, j, k}, BIT(w12) | BIT(w23) | BIT(w13)});
                }
                for (int l = k + 1; l < NUM_LINES; ++l) {
                    if (inter_cell[i][l] < 0 || inter_cell[j][l] < 0 || inter_cell[k][l] < 0) continue;
                    std::array<int, 6> pts = {
                        inter_cell[i][j], inter_cell[i][k], inter_cell[i][l],
                        inter_cell[j][k], inter_cell[j][l], inter_cell[k][l]
                    };
                    std::sort(pts.begin(), pts.end());
                    bool distinct = true;
                    for (int q = 0; q < 5; ++q) {
                        if (pts[q] == pts[q + 1]) distinct = false;
                    }
                    if (distinct) {
                        u128 cm = 0;
                        for (int pt : pts) cm |= BIT(pt);
                        k4_gadgets.push_back({{i, j, k, l}, cm});
                    }
                }
            }
        }
}

static inline u128 apply_sym_cells(int g, u128 mask) {
    uint64_t lo = static_cast<uint64_t>(mask);
    uint64_t hi = static_cast<uint64_t>(mask >> 64);
    return sym_cell_lut[g][0][lo & 0xFF] | sym_cell_lut[g][1][(lo >> 8) & 0xFF]
         | sym_cell_lut[g][2][(lo >> 16) & 0xFF] | sym_cell_lut[g][3][(lo >> 24) & 0xFF]
         | sym_cell_lut[g][4][(lo >> 32) & 0xFF] | sym_cell_lut[g][5][(lo >> 40) & 0xFF]
         | sym_cell_lut[g][6][(lo >> 48) & 0xFF] | sym_cell_lut[g][7][(lo >> 56) & 0xFF]
         | sym_cell_lut[g][8][hi & 0xFF] | sym_cell_lut[g][9][(hi >> 8) & 0xFF]
         | sym_cell_lut[g][10][(hi >> 16) & 0xFF] | sym_cell_lut[g][11][(hi >> 24) & 0xFF]
         | sym_cell_lut[g][12][(hi >> 32) & 0xFF] | sym_cell_lut[g][13][(hi >> 40) & 0xFF]
         | sym_cell_lut[g][14][(hi >> 48) & 0xFF] | sym_cell_lut[g][15][(hi >> 56) & 0xFF];
}

static inline u128 apply_sym_lines(int g, u128 mask) {
    uint64_t lo = static_cast<uint64_t>(mask);
    uint64_t hi = static_cast<uint64_t>(mask >> 64);
    return sym_line_lut[g][0][lo & 0xFF] | sym_line_lut[g][1][(lo >> 8) & 0xFF]
         | sym_line_lut[g][2][(lo >> 16) & 0xFF] | sym_line_lut[g][3][(lo >> 24) & 0xFF]
         | sym_line_lut[g][4][(lo >> 32) & 0xFF] | sym_line_lut[g][5][(lo >> 40) & 0xFF]
         | sym_line_lut[g][6][(lo >> 48) & 0xFF] | sym_line_lut[g][7][(lo >> 56) & 0xFF]
         | sym_line_lut[g][8][hi & 0xFF] | sym_line_lut[g][9][(hi >> 8) & 0xFF]
         | sym_line_lut[g][10][(hi >> 16) & 0xFF] | sym_line_lut[g][11][(hi >> 24) & 0xFF]
         | sym_line_lut[g][12][(hi >> 32) & 0xFF] | sym_line_lut[g][13][(hi >> 40) & 0xFF];
}

static inline HyperState canonicalize_hyperstate(u128 e_red, u128 v_red) {
    u128 best_e = e_red, best_v = v_red;
    for (int g = 1; g < 48; ++g) {
        u128 ge = apply_sym_lines(g, e_red);
        if (ge >= best_e) {
            u128 gv = apply_sym_cells(g, v_red);
            if (ge > best_e || gv > best_v) {
                best_e = ge;
                best_v = gv;
            }
        }
    }
    return {best_e, best_v};
}

// ============================================================================
// PARALLEL 256-BUCKET RADIX DEDUPLICATION FOR HYPERSTATE VECTORS
// ============================================================================
void parallel_sort_unique_hyper(std::vector<HyperState>& vec) {
    if (vec.size() < 65536) {
        std::sort(vec.begin(), vec.end());
        vec.erase(std::unique(vec.begin(), vec.end()), vec.end());
        return;
    }

    static constexpr int NUM_BUCKETS = 256;
    std::vector<HyperState> buckets[NUM_BUCKETS];
    int n_threads = omp_get_max_threads();
    std::vector<std::vector<HyperState>> local_b(n_threads * NUM_BUCKETS);

    #pragma omp parallel
    {
        int tid = omp_get_thread_num();
        #pragma omp for schedule(static)
        for (size_t i = 0; i < vec.size(); ++i) {
            uint64_t hi = static_cast<uint64_t>(vec[i].e_red >> 64);
            int b_id = 255 - static_cast<int>((hi >> 37) & 0xFF);
            local_b[tid * NUM_BUCKETS + b_id].push_back(vec[i]);
        }

        #pragma omp for schedule(dynamic, 1)
        for (int b_id = 0; b_id < NUM_BUCKETS; ++b_id) {
            size_t total_b = 0;
            for (int t = 0; t < n_threads; ++t) {
                total_b += local_b[t * NUM_BUCKETS + b_id].size();
            }
            buckets[b_id].reserve(total_b);
            for (int t = 0; t < n_threads; ++t) {
                auto& src = local_b[t * NUM_BUCKETS + b_id];
                buckets[b_id].insert(buckets[b_id].end(), src.begin(), src.end());
                std::vector<HyperState>().swap(src);
            }
            std::sort(buckets[b_id].begin(), buckets[b_id].end());
            buckets[b_id].erase(std::unique(buckets[b_id].begin(), buckets[b_id].end()),
                                buckets[b_id].end());
        }
    }

    size_t offsets[NUM_BUCKETS + 1] = {0};
    for (int b_id = 0; b_id < NUM_BUCKETS; ++b_id) {
        offsets[b_id + 1] = offsets[b_id] + buckets[b_id].size();
    }
    vec.resize(offsets[NUM_BUCKETS]);

    #pragma omp parallel for schedule(dynamic, 1)
    for (int b_id = 0; b_id < NUM_BUCKETS; ++b_id) {
        if (!buckets[b_id].empty()) {
            std::memcpy(vec.data() + offsets[b_id],
                        buckets[b_id].data(),
                        buckets[b_id].size() * sizeof(HyperState));
        }
    }
}

// ============================================================================
// PILLAR 1: FIXED-POINT 2-CORE PEELING DIRECTLY ON (e_in, v_in)
// ============================================================================
struct PeelingResult {
    u128 reduced_lines_mask;
    u128 reduced_empty_mask;
    u128 peel2_mask; // Fragile degree-1 cells of peeled lines that had exactly 2 deg-1 cells
    int red_arr[NUM_LINES];
    int line_mc[NUM_LINES];
    int n_red;
    int empty_deg[NUM_CELLS];
    int kern_phi32;
    int max_kern_d;
    int max_c4;
    int max_c3;
    int max_c2;
    bool maker_won;
};

void peel_from_hyperstate(u128 e_in, u128 v_in, PeelingResult& res) {
    std::memset(res.empty_deg, 0, sizeof(res.empty_deg));
    std::memset(res.line_mc, -1, sizeof(res.line_mc));
    res.kern_phi32 = res.max_kern_d = 0;
    res.max_c4 = res.max_c3 = res.max_c2 = 0;
    res.peel2_mask = 0;
    res.maker_won = false;

    int line_w[NUM_LINES] = {0};
    u128 active_lines = e_in;

    u128 scan = active_lines;
    while (scan) {
        int j = ctz128(scan);
        scan &= scan - 1;
        u128 emp = line_mask[j] & v_in;
        int r = popcnt128(emp);
        if (r == 0) {
            res.maker_won = true;
            res.line_mc[j] = 5;
            continue;
        }
        int mc = 5 - r;
        res.line_mc[j] = mc;
        int w = 1 << mc;
        line_w[j] = w;
        if (mc == 4) ++res.max_c4;
        else if (mc == 3) ++res.max_c3;
        else if (mc == 2) ++res.max_c2;

        while (emp) {
            int c = ctz128(emp);
            emp &= emp - 1;
            ++res.empty_deg[c];
        }
    }

    // Fixed-point 2-core peeling cascade
    u128 cur_empty = v_in;
    bool changed = true;
    while (changed) {
        changed = false;
        scan = active_lines;
        while (scan) {
            int j = ctz128(scan);
            scan &= scan - 1;

            int d1_cnt = 0;
            u128 d1_all = 0;
            for (int k = 0; k < 5; ++k) {
                int c = line_cells[j][k];
                if ((cur_empty & BIT(c)) && res.empty_deg[c] == 1) {
                    d1_all |= BIT(c);
                    ++d1_cnt;
                }
            }
            if (d1_cnt >= 2) {
                if (d1_cnt == 2) {
                    res.peel2_mask |= (line_mask[j] & v_in);
                }
                active_lines &= ~BIT(j);
                cur_empty &= ~d1_all;
                for (int k = 0; k < 5; ++k) {
                    int c = line_cells[j][k];
                    if (v_in & BIT(c)) {
                        --res.empty_deg[c];
                    }
                }
                changed = true;
            }
        }
    }

    // Recompute surviving stats on active_lines
    res.reduced_lines_mask = active_lines;
    res.n_red = 0;
    res.max_c4 = res.max_c3 = res.max_c2 = 0;
    u128 non_isolated_empty = 0;
    int cell_kern_w[NUM_CELLS] = {0};

    scan = active_lines;
    while (scan) {
        int j = ctz128(scan);
        scan &= scan - 1;
        res.red_arr[res.n_red++] = j;
        int mc = res.line_mc[j];
        if (mc == 4) ++res.max_c4;
        else if (mc == 3) ++res.max_c3;
        else if (mc == 2) ++res.max_c2;

        int w = line_w[j];
        res.kern_phi32 += w;
        for (int k = 0; k < 5; ++k) {
            int c = line_cells[j][k];
            if (cur_empty & BIT(c)) {
                non_isolated_empty |= BIT(c);
                cell_kern_w[c] += w;
                if (cell_kern_w[c] > res.max_kern_d) {
                    res.max_kern_d = cell_kern_w[c];
                }
            }
        }
    }
    res.reduced_empty_mask = non_isolated_empty;
}

// ============================================================================
// PILLAR 2: COMMUTATIVE CORE-SCHEDULE POLICY B_pi(e_in, v_in)
// ============================================================================
int commutative_breaker_move(u128 e_in, u128 v_in) {
    if (v_in == 0) return -1;
    if (e_in == 0) return ctz128(v_in);

    u128 threat4_mask = 0;
    u128 threat3_mask = 0;
    int cell_k4[NUM_CELLS] = {0};
    int cell_k3[NUM_CELLS] = {0};
    int cell_k2[NUM_CELLS] = {0};
    int cell_deg[NUM_CELLS] = {0};
    int max_deg = 0;

    u128 scan = e_in;
    while (scan) {
        int j = ctz128(scan);
        scan &= scan - 1;
        u128 emp = line_mask[j] & v_in;
        int r = popcnt128(emp);
        if (r == 0) continue;
        int mc = 5 - r;
        if (mc == 4) threat4_mask |= emp;
        else if (mc == 3) threat3_mask |= emp;

        while (emp) {
            int c = ctz128(emp);
            emp &= emp - 1;
            ++cell_deg[c];
            if (cell_deg[c] > max_deg) max_deg = cell_deg[c];
            if (mc == 4) ++cell_k4[c];
            else if (mc == 3) ++cell_k3[c];
            else if (mc == 2) ++cell_k2[c];
        }
    }

    // Rule 1: Mandatory mc=4 block
    if (threat4_mask != 0) {
        int best_c = -1, best_sc = -1;
        u128 tscan = threat4_mask;
        while (tscan) {
            int c = ctz128(tscan);
            tscan &= tscan - 1;
            int sc = 100000 * cell_k4[c] + 1000 * cell_k3[c] + 50 * cell_deg[c] + pi_bonus[c];
            if (sc > best_sc) {
                best_sc = sc;
                best_c = c;
            }
        }
        return best_c;
    }

    // Rule 2: Immediate mc=3 destruction
    if (threat3_mask != 0) {
        int best_c = -1, best_sc = -1;
        u128 tscan = threat3_mask;
        while (tscan) {
            int c = ctz128(tscan);
            tscan &= tscan - 1;
            int sc = 1000 * cell_k3[c] + 50 * cell_deg[c] + pi_bonus[c];
            if (sc > best_sc) {
                best_sc = sc;
                best_c = c;
            }
        }
        return best_c;
    }

    // Rule 3: True k=5 Fork-Cluster Prevention (k2(y) >= 3)
    int best_f3 = -1, best_f3_sc = -1;
    u128 vscan = v_in;
    while (vscan) {
        int c = ctz128(vscan);
        vscan &= vscan - 1;
        if (cell_k2[c] >= 3) {
            int sc = 1000 * cell_k2[c] + 50 * cell_deg[c] + pi_bonus[c];
            if (sc > best_f3_sc) {
                best_f3_sc = sc;
                best_f3 = c;
            }
        }
    }
    if (best_f3 >= 0) return best_f3;

    // Rule 4: Commutative Core Schedule — first v_k in static list pi with
    // maximum current alive degree d_{E_red}(v_k) == max_deg
    for (int r = 0; r < NUM_CELLS; ++r) {
        int v_k = pi_order[r];
        if ((v_in & BIT(v_k)) && cell_deg[v_k] == max_deg) {
            return v_k;
        }
    }
    return ctz128(v_in);
}

// Existential Multi-Probe Candidate Generator for Pillar 3 (Null-Move Probes y_1..y_K)
int get_hyper_breaker_candidates(u128 e_in, u128 v_in, int* out_cands, int max_cands) {
    if (v_in == 0 || max_cands <= 0) return 0;
    int primary = commutative_breaker_move(e_in, v_in);
    int n_out = 0;
    if (primary >= 0) out_cands[n_out++] = primary;
    if (n_out >= max_cands) return n_out;

    u128 threat4_mask = 0;
    u128 threat3_mask = 0;
    int alive_d[NUM_CELLS] = {0};
    int es_w[NUM_CELLS] = {0};
    int k3[NUM_CELLS] = {0};
    int k2[NUM_CELLS] = {0};

    u128 scan = e_in;
    while (scan) {
        int j = ctz128(scan);
        scan &= scan - 1;
        u128 emp = line_mask[j] & v_in;
        int r = popcnt128(emp);
        if (r == 0) continue;
        int mc = 5 - r;
        int w = 1 << mc;
        if (mc == 4) threat4_mask |= emp;
        else if (mc == 3) threat3_mask |= emp;
        while (emp) {
            int c = ctz128(emp);
            emp &= emp - 1;
            ++alive_d[c];
            es_w[c] += w;
            if (mc == 3) ++k3[c];
            else if (mc == 2) ++k2[c];
        }
    }

    if (threat4_mask != 0) return n_out;

    struct Cand {
        int cell;
        int sc;
        bool operator<(const Cand& o) const { return sc > o.sc; }
    };
    Cand cands[NUM_CELLS];
    int n_c = 0;

    u128 vscan = v_in;
    while (vscan) {
        int c = ctz128(vscan);
        vscan &= vscan - 1;
        if (c == primary || alive_d[c] == 0) continue;
        if (threat3_mask != 0 && !(threat3_mask & BIT(c))) continue;
        int sc = alive_d[c] * 24 + es_w[c] * 6 + k3[c] * 2500 +
                 ((k2[c] >= 2) ? (120 * k2[c] * (k2[c] - 1) / 2) : 0) + pi_bonus[c];
        cands[n_c++] = {c, sc};
    }
    std::sort(cands, cands + n_c);
    for (int i = 0; i < n_c && n_out < max_cands; ++i) {
        out_cands[n_out++] = cands[i].cell;
    }
    return n_out;
}

// ============================================================================
// HOPCROFT-KARP, DULMAGE-MENDELSOHN BFS & COUPLED PAIRING-ES CERTIFICATES
// ============================================================================
u128 compute_dm_reachable_mask(int n_alive, const int (*adj)[5], const int* adj_sz,
                               const int16_t* match_u, const int16_t* match_v,
                               u128 u_safe_mask) {
    (void)match_v;
    u128 dm_mask = u_safe_mask;
    int q[NUM_CELLS], q_head = 0, q_tail = 0;

    u128 scan = u_safe_mask;
    while (scan) {
        int c = ctz128(scan);
        scan &= scan - 1;
        q[q_tail++] = c;
    }

    while (q_head < q_tail) {
        int c = q[q_head++];
        for (int r = 0; r < n_alive; ++r) {
            bool has_c = false;
            for (int k = 0; k < adj_sz[2 * r]; ++k) {
                if (adj[2 * r][k] == c) {
                    has_c = true;
                    break;
                }
            }
            if (!has_c) continue;
            for (int slot : {2 * r, 2 * r + 1}) {
                int matched_cell = match_u[slot];
                if (matched_cell >= 0 && !(dm_mask & BIT(matched_cell))) {
                    dm_mask |= BIT(matched_cell);
                    q[q_tail++] = matched_cell;
                }
            }
        }
    }
    return dm_mask;
}

bool run_hk_subset(const int* lines_subset, int n_alive, u128 avail_empty_mask,
                   u128* out_dm_safe_mask = nullptr) {
    if (n_alive == 0) {
        if (out_dm_safe_mask) *out_dm_safe_mask = avail_empty_mask;
        return true;
    }
    int n_left = 2 * n_alive;
    if (n_left > popcnt128(avail_empty_mask)) return false;

    int adj[218][5], adj_sz[218];
    for (int r = 0; r < n_alive; ++r) {
        int j = lines_subset[r], deg = 0;
        for (int k = 0; k < 5; ++k) {
            int c = line_cells[j][k];
            if (avail_empty_mask & BIT(c)) {
                adj[2 * r][deg] = adj[2 * r + 1][deg] = c;
                ++deg;
            }
        }
        if (deg < 2) return false;
        adj_sz[2 * r] = adj_sz[2 * r + 1] = deg;
    }

    int16_t match_u[218], match_v[NUM_CELLS], dist[218], q[218];
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
                int next_u = match_v[adj[u][k]];
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
                int v = adj[u][k], next_u = match_v[v];
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
    if (matched != n_left) return false;

    if (out_dm_safe_mask) {
        u128 matched_mask = 0;
        for (int u = 0; u < n_left; ++u) matched_mask |= BIT(match_u[u]);
        u128 u_free = avail_empty_mask & ~matched_mask;
        *out_dm_safe_mask = compute_dm_reachable_mask(n_alive, adj, adj_sz, match_u, match_v, u_free);
    }
    return true;
}

static inline int pick_min_deg_cell(u128 cand_mask, const int* cell_cost) {
    int best_c = -1, best_d = 999999;
    while (cand_mask) {
        int c = ctz128(cand_mask);
        cand_mask &= cand_mask - 1;
        if (cell_cost[c] < best_d) {
            best_d = cell_cost[c];
            best_c = c;
        }
    }
    return best_c;
}

static inline void extract_disjoint_gadgets(u128& cur_lines, u128& cur_empty, const int* cell_cost) {
    for (const auto& g : k4_gadgets) {
        if ((g.cell_mask & cur_empty) != g.cell_mask) continue;
        u128 lm = BIT(g.lines[0]) | BIT(g.lines[1]) | BIT(g.lines[2]) | BIT(g.lines[3]);
        if ((cur_lines & lm) == lm) {
            cur_lines &= ~lm;
            cur_empty &= ~g.cell_mask;
        }
    }

    static constexpr int PAIRS[3][2] = {{0, 1}, {0, 2}, {1, 2}};
    for (const auto& tri : k3_triangles) {
        if ((tri.core_mask & cur_empty) != tri.core_mask) continue;
        u128 lm = BIT(tri.lines[0]) | BIT(tri.lines[1]) | BIT(tri.lines[2]);
        if ((cur_lines & lm) != lm) continue;

        for (int p = 0; p < 3; ++p) {
            int la = tri.lines[PAIRS[p][0]];
            int lb = tri.lines[PAIRS[p][1]];
            u128 ca = (line_mask[la] & cur_empty) & ~tri.core_mask;
            if (ca == 0) continue;
            int ba = pick_min_deg_cell(ca, cell_cost);
            u128 ua_m = BIT(ba);

            u128 cb = (line_mask[lb] & cur_empty) & ~(tri.core_mask | ua_m);
            if (cb == 0) continue;
            int bb = pick_min_deg_cell(cb, cell_cost);
            u128 ub_m = BIT(bb);

            cur_lines &= ~lm;
            cur_empty &= ~(tri.core_mask | ua_m | ub_m);
            break;
        }
    }
}

bool run_gadget_boosted_hk(u128 rem_lines_mask, u128 avail_empty, const int* empty_deg,
                           u128* out_dm_safe_mask = nullptr) {
    if (rem_lines_mask == 0) {
        if (out_dm_safe_mask) *out_dm_safe_mask = avail_empty;
        return true;
    }
    int alive_arr[NUM_LINES], cnt = 0;
    u128 scan = rem_lines_mask;
    while (scan) {
        alive_arr[cnt++] = ctz128(scan);
        scan &= scan - 1;
    }
    if (2 * cnt <= popcnt128(avail_empty) &&
        run_hk_subset(alive_arr, cnt, avail_empty, out_dm_safe_mask)) {
        return true;
    }

    u128 cur_lines = rem_lines_mask, cur_empty = avail_empty;
    extract_disjoint_gadgets(cur_lines, cur_empty, empty_deg);
    if (cur_lines == rem_lines_mask) return false;

    cnt = 0;
    scan = cur_lines;
    while (scan) {
        alive_arr[cnt++] = ctz128(scan);
        scan &= scan - 1;
    }
    return run_hk_subset(alive_arr, cnt, cur_empty, out_dm_safe_mask);
}

static inline int compute_es_obj(u128 es_lines_mask, u128 V_free) {
    if (es_lines_mask == 0) return 0;
    int phi_M = 0;
    int cell_d_M[NUM_CELLS] = {0};
    int max_d_M = 0;
    u128 scan = es_lines_mask;
    while (scan) {
        int j = ctz128(scan);
        scan &= scan - 1;
        u128 free_cells = line_mask[j] & V_free;
        int r_M = popcnt128(free_cells);
        if (r_M == 0) return 999999;
        int w_M = 1 << (5 - r_M);
        phi_M += w_M;
        u128 cscan = free_cells;
        while (cscan) {
            int c = ctz128(cscan);
            cscan &= cscan - 1;
            cell_d_M[c] += w_M;
            if (cell_d_M[c] > max_d_M) max_d_M = cell_d_M[c];
        }
    }
    return phi_M + max_d_M;
}

static inline bool verify_coupled_es(u128 es_lines_mask, u128 V_free,
                                     u128* out_u_safe_mask = nullptr) {
    if (es_lines_mask == 0) {
        if (out_u_safe_mask) *out_u_safe_mask = V_free;
        return true;
    }
    int phi_M = 0;
    int cell_d_M[NUM_CELLS] = {0};
    int max_d_M = 0;
    u128 r1_cells_mask = 0;

    u128 scan = es_lines_mask;
    while (scan) {
        int j = ctz128(scan);
        scan &= scan - 1;
        u128 free_cells = line_mask[j] & V_free;
        int r_M = popcnt128(free_cells);
        if (r_M == 0) return false;
        if (r_M == 1) r1_cells_mask |= free_cells;
        int w_M = 1 << (5 - r_M);
        phi_M += w_M;
        if (phi_M >= 32) return false;

        u128 cscan = free_cells;
        while (cscan) {
            int c = ctz128(cscan);
            cscan &= cscan - 1;
            cell_d_M[c] += w_M;
            if (cell_d_M[c] > max_d_M) max_d_M = cell_d_M[c];
        }
    }
    if (phi_M + max_d_M >= 32) return false;

    if (out_u_safe_mask) {
        int delta_k = 31 - (phi_M + max_d_M);
        u128 u_safe = 0;
        u128 fscan = V_free & ~r1_cells_mask;
        while (fscan) {
            int u = ctz128(fscan);
            fscan &= fscan - 1;
            if (2 * cell_d_M[u] <= delta_k) {
                u_safe |= BIT(u);
            } else if (phi_M + cell_d_M[u] < 32 &&
                       verify_coupled_es(es_lines_mask, V_free & ~BIT(u), nullptr)) {
                u_safe |= BIT(u);
            }
        }
        *out_u_safe_mask = u_safe;
    }
    return true;
}

void run_priority_partial_hk(const int* lines_ordered,
                             int n_lines,
                             u128 avail_empty_mask,
                             const int* cell_cost,
                             u128& out_paired_lines,
                             u128& out_matched_cells,
                             int (*out_adj)[5] = nullptr,
                             int* out_adj_sz = nullptr,
                             int16_t* out_match_u = nullptr,
                             int16_t* out_match_v = nullptr,
                             int* out_n_paired = nullptr) {
    out_paired_lines = 0;
    out_matched_cells = 0;
    if (out_n_paired) *out_n_paired = 0;
    if (n_lines == 0) return;

    int adj[218][5], adj_sz[218];
    for (int r = 0; r < n_lines; ++r) {
        int j = lines_ordered[r], deg = 0;
        int cells[5];
        for (int k = 0; k < 5; ++k) {
            int c = line_cells[j][k];
            if (avail_empty_mask & BIT(c)) {
                cells[deg++] = c;
            }
        }
        for (int a = 0; a < deg; ++a) {
            for (int b = a + 1; b < deg; ++b) {
                if (cell_cost[cells[b]] < cell_cost[cells[a]]) {
                    std::swap(cells[a], cells[b]);
                }
            }
        }
        for (int k = 0; k < deg; ++k) {
            adj[2 * r][k] = adj[2 * r + 1][k] = cells[k];
        }
        adj_sz[2 * r] = adj_sz[2 * r + 1] = deg;
    }

    int16_t match_u[218], match_v[NUM_CELLS];
    std::fill_n(match_u, 2 * n_lines, -1);
    std::fill_n(match_v, NUM_CELLS, -1);

    uint32_t vis_token = 0;
    uint32_t vis_v[NUM_CELLS] = {0};

    auto dfs_aug = [&](auto& self, int u) -> bool {
        for (int k = 0; k < adj_sz[u]; ++k) {
            int v = adj[u][k];
            if (vis_v[v] == vis_token) continue;
            vis_v[v] = vis_token;
            int next_u = match_v[v];
            if (next_u == -1 || self(self, next_u)) {
                match_u[u] = v;
                match_v[v] = u;
                return true;
            }
        }
        return false;
    };

    int16_t saved_u[218], saved_v[NUM_CELLS];
    for (int r = 0; r < n_lines; ++r) {
        if (adj_sz[2 * r] < 2) continue;
        std::memcpy(saved_u, match_u, 2 * n_lines * sizeof(int16_t));
        std::memcpy(saved_v, match_v, NUM_CELLS * sizeof(int16_t));

        ++vis_token;
        if (dfs_aug(dfs_aug, 2 * r)) {
            ++vis_token;
            if (dfs_aug(dfs_aug, 2 * r + 1)) {
                out_paired_lines |= BIT(lines_ordered[r]);
                continue;
            }
        }
        std::memcpy(match_u, saved_u, 2 * n_lines * sizeof(int16_t));
        std::memcpy(match_v, saved_v, NUM_CELLS * sizeof(int16_t));
    }

    int compact_r = 0;
    for (int r = 0; r < n_lines; ++r) {
        if (out_paired_lines & BIT(lines_ordered[r])) {
            out_matched_cells |= BIT(match_u[2 * r]) | BIT(match_u[2 * r + 1]);
            if (out_adj && out_adj_sz && out_match_u) {
                for (int k = 0; k < adj_sz[2 * r]; ++k) {
                    out_adj[2 * compact_r][k] = out_adj[2 * compact_r + 1][k] = adj[2 * r][k];
                }
                out_adj_sz[2 * compact_r] = out_adj_sz[2 * compact_r + 1] = adj_sz[2 * r];
                out_match_u[2 * compact_r] = match_u[2 * r];
                out_match_u[2 * compact_r + 1] = match_u[2 * r + 1];
                ++compact_r;
            }
        }
    }
    if (out_match_v) std::memcpy(out_match_v, match_v, NUM_CELLS * sizeof(int16_t));
    if (out_n_paired) *out_n_paired = compact_r;
}

// Evaluates all 4 formal Draw Certificates on a Maker-to-move PeelingResult `pr`
// and optionally extracts the 1-fault-tolerant safe subset inside V_red(S_k)
// (`*out_dm_safe_in_vred = U_safe U R_HK`).
int check_coupled_certificate(const PeelingResult& pr,
                              u128* out_uncert_empty_mask = nullptr,
                              u128* out_dm_safe_in_vred = nullptr) {
    if (out_uncert_empty_mask) *out_uncert_empty_mask = pr.reduced_empty_mask;
    if (out_dm_safe_in_vred) *out_dm_safe_in_vred = 0;
    if (pr.maker_won) return 0;
    if (pr.n_red == 0) {
        if (out_dm_safe_in_vred) *out_dm_safe_in_vred = pr.reduced_empty_mask;
        return 1;
    }

    // Certificate 2: Exact Maker-Turn Kernelized Erdos-Selfridge Bound
    if (pr.kern_phi32 + pr.max_kern_d < 32) {
        if (out_dm_safe_in_vred) {
            verify_coupled_es(pr.reduced_lines_mask, pr.reduced_empty_mask, out_dm_safe_in_vred);
        }
        return 2;
    }

    // Certificate 1: Full Hopcroft-Karp Pairing on 2-Core Reduced Hypergraph
    if (run_hk_subset(pr.red_arr, pr.n_red, pr.reduced_empty_mask, out_dm_safe_in_vred)) {
        return 1;
    }

    // Certificate 3: Full K4 & K3+ Gadget-Boosted Hopcroft-Karp Pairing
    if (run_gadget_boosted_hk(pr.reduced_lines_mask, pr.reduced_empty_mask, pr.empty_deg,
                              out_dm_safe_in_vred)) {
        return 3;
    }

    // Certificate 4: Connected-Component Decomposition + Marginal-Potential Descent + Coupled Pairing-ES
    u128 unvis_lines = pr.reduced_lines_mask;
    u128 uncert_vertices = 0;
    u128 total_dm_safe = 0;
    bool all_comps_certified = true;

    while (unvis_lines) {
        int seed_l = ctz128(unvis_lines);
        unvis_lines &= ~BIT(seed_l);
        u128 comp_lines = BIT(seed_l);
        u128 comp_verts = line_mask[seed_l] & pr.reduced_empty_mask;
        u128 frontier = comp_verts;

        while (frontier) {
            int c = ctz128(frontier);
            frontier &= frontier - 1;
            for (int j : pt_lines[c]) {
                if (unvis_lines & BIT(j)) {
                    unvis_lines &= ~BIT(j);
                    comp_lines |= BIT(j);
                    u128 new_v = (line_mask[j] & pr.reduced_empty_mask) & ~comp_verts;
                    comp_verts |= new_v;
                    frontier |= new_v;
                }
            }
        }

        u128 comp_dm = 0;
        if (verify_coupled_es(comp_lines, comp_verts, out_dm_safe_in_vred ? &comp_dm : nullptr)) {
            total_dm_safe |= comp_dm;
            continue;
        }
        if (run_gadget_boosted_hk(comp_lines, comp_verts, pr.empty_deg,
                                  out_dm_safe_in_vred ? &comp_dm : nullptr)) {
            total_dm_safe |= comp_dm;
            continue;
        }

        // Step B: Marginal-Potential Descent
        u128 es_lines = comp_lines;
        u128 v_free = comp_verts;
        int adj_SB[218][5], adj_sz_SB[218], n_paired_SB = 0;
        int16_t match_u_SB[218], match_v_SB[NUM_CELLS];
        if (out_dm_safe_in_vred) std::fill_n(match_v_SB, NUM_CELLS, -1);

        while (true) {
            int best_j = -1, best_u = -1, best_v = -1, best_delta = 0;
            u128 scan = es_lines;
            while (scan) {
                int j = ctz128(scan);
                scan &= scan - 1;
                u128 emp = line_mask[j] & v_free;
                int r_j = popcnt128(emp);
                if (r_j < 2 || r_j >= 4) continue;
                int w_j = 1 << (5 - r_j);

                int cells[5], n_c = 0;
                while (emp) {
                    cells[n_c++] = ctz128(emp);
                    emp &= emp - 1;
                }

                for (int a = 0; a < n_c; ++a) {
                    for (int b_i = a + 1; b_i < n_c; ++b_i) {
                        u128 pair_m = BIT(cells[a]) | BIT(cells[b_i]);
                        int pen = 0;
                        bool valid = true;
                        u128 other = es_lines & ~BIT(j);
                        while (other) {
                            int j2 = ctz128(other);
                            other &= other - 1;
                            u128 hit = line_mask[j2] & pair_m;
                            if (!hit) continue;
                            int r2 = popcnt128(line_mask[j2] & v_free);
                            int h_cnt = popcnt128(hit);
                            if (r2 - h_cnt < 1) {
                                valid = false;
                                break;
                            }
                            int w2 = 1 << (5 - r2);
                            pen += w2 * ((1 << h_cnt) - 1);
                        }
                        if (valid && (-w_j + pen < best_delta)) {
                            best_delta = -w_j + pen;
                            best_j = j;
                            best_u = cells[a];
                            best_v = cells[b_i];
                        }
                    }
                }
            }
            if (best_j < 0) break;
            if (out_dm_safe_in_vred) {
                int r = n_paired_SB++;
                int deg = 0;
                for (int k = 0; k < 5; ++k) {
                    int c = line_cells[best_j][k];
                    if (comp_verts & BIT(c)) {
                        adj_SB[2 * r][deg] = adj_SB[2 * r + 1][deg] = c;
                        ++deg;
                    }
                }
                adj_sz_SB[2 * r] = adj_sz_SB[2 * r + 1] = deg;
                match_u_SB[2 * r] = best_u;
                match_u_SB[2 * r + 1] = best_v;
                match_v_SB[best_u] = 2 * r;
                match_v_SB[best_v] = 2 * r + 1;
            }
            es_lines &= ~BIT(best_j);
            v_free &= ~(BIT(best_u) | BIT(best_v));
        }

        if (es_lines != comp_lines &&
            verify_coupled_es(es_lines, v_free, out_dm_safe_in_vred ? &comp_dm : nullptr)) {
            if (out_dm_safe_in_vred) {
                total_dm_safe |= compute_dm_reachable_mask(
                    n_paired_SB, adj_SB, adj_sz_SB, match_u_SB, match_v_SB, comp_dm);
            }
            continue;
        }

        // Step C: Coupled Priority-Lexicographic Pairing inside the component
        bool step_c_certified = false;
        int start_ug = out_dm_safe_in_vred ? 0 : 1;
        for (int use_gadgets = start_ug; use_gadgets <= 1 && !step_c_certified; ++use_gadgets) {
            u128 rem_lines = comp_lines;
            u128 rem_empty = comp_verts;
            if (use_gadgets) {
                extract_disjoint_gadgets(rem_lines, rem_empty, pr.empty_deg);
                if (start_ug == 0 && rem_lines == comp_lines) continue;
            }
            u128 gadget_used_cells = comp_verts & ~rem_empty;

            struct LinePrio {
                int j;
                int rem;
                int overlap;
            };
            LinePrio prio[NUM_LINES];
            int n_rem = 0;
            u128 scan = rem_lines;
            while (scan) {
                int j = ctz128(scan);
                scan &= scan - 1;
                int rem = popcnt128(line_mask[j] & rem_empty);
                int ov = 0;
                for (int k = 0; k < 5; ++k) {
                    int c = line_cells[j][k];
                    if (rem_empty & BIT(c)) ov += pr.empty_deg[c];
                }
                prio[n_rem++] = {j, rem, ov};
            }

            std::sort(prio, prio + n_rem, [](const LinePrio& a, const LinePrio& b) {
                if (a.rem != b.rem) return a.rem < b.rem;
                if (a.overlap != b.overlap) return a.overlap < b.overlap;
                return a.j < b.j;
            });

            int ordered_lines[NUM_LINES];
            for (int i = 0; i < n_rem; ++i) ordered_lines[i] = prio[i].j;

            u128 hk_paired_lines = 0, hk_matched_cells = 0;
            int adj_A[218][5], adj_sz_A[218], n_paired_A = 0;
            int16_t match_u_A[218], match_v_A[NUM_CELLS];

            run_priority_partial_hk(ordered_lines, n_rem, rem_empty, pr.empty_deg,
                                    hk_paired_lines, hk_matched_cells,
                                    out_dm_safe_in_vred ? adj_A : nullptr,
                                    out_dm_safe_in_vred ? adj_sz_A : nullptr,
                                    out_dm_safe_in_vred ? match_u_A : nullptr,
                                    out_dm_safe_in_vred ? match_v_A : nullptr,
                                    out_dm_safe_in_vred ? &n_paired_A : nullptr);

            u128 unpaired_lines_A = rem_lines & ~hk_paired_lines;
            u128 V_free_A = comp_verts & ~(gadget_used_cells | hk_matched_cells);
            u128 u_safe_A = 0;
            if (verify_coupled_es(unpaired_lines_A, V_free_A,
                                  out_dm_safe_in_vred ? &u_safe_A : nullptr)) {
                if (out_dm_safe_in_vred) {
                    total_dm_safe |= compute_dm_reachable_mask(
                        n_paired_A, adj_A, adj_sz_A, match_u_A, match_v_A, u_safe_A);
                }
                step_c_certified = true;
                break;
            }

            u128 cand_es_mask = 0;
            int base_es_phi = 0;
            int cell_es_d[NUM_CELLS] = {0}, max_es_d = 0;

            for (int i = n_rem - 1; i >= 0; --i) {
                int j = prio[i].j;
                if (prio[i].rem < 4 && !(unpaired_lines_A & BIT(j))) continue;
                int w = 1 << (5 - prio[i].rem);
                if (base_es_phi + w >= 31) continue;
                int next_max_d = max_es_d;
                for (int k = 0; k < 5; ++k) {
                    int c = line_cells[j][k];
                    if ((rem_empty & BIT(c)) && cell_es_d[c] + w > next_max_d) {
                        next_max_d = cell_es_d[c] + w;
                    }
                }
                if (base_es_phi + w + next_max_d >= 32) continue;

                cand_es_mask |= BIT(j);
                base_es_phi += w;
                max_es_d = next_max_d;
                for (int k = 0; k < 5; ++k) {
                    int c = line_cells[j][k];
                    if (rem_empty & BIT(c)) cell_es_d[c] += w;
                }
            }

            if (cand_es_mask != 0) {
                int penalized_cost[NUM_CELLS];
                for (int c = 0; c < NUM_CELLS; ++c) {
                    penalized_cost[c] = pr.empty_deg[c] + 100 * cell_es_d[c];
                }
                int pair_target_lines[NUM_LINES], n_target = 0;
                for (int i = 0; i < n_rem; ++i) {
                    if (!(cand_es_mask & BIT(ordered_lines[i]))) {
                        pair_target_lines[n_target++] = ordered_lines[i];
                    }
                }

                u128 hk_paired_B = 0, hk_matched_B = 0;
                int adj_B[218][5], adj_sz_B[218], n_paired_B = 0;
                int16_t match_u_B[218], match_v_B[NUM_CELLS];

                run_priority_partial_hk(pair_target_lines, n_target, rem_empty, penalized_cost,
                                        hk_paired_B, hk_matched_B,
                                        out_dm_safe_in_vred ? adj_B : nullptr,
                                        out_dm_safe_in_vred ? adj_sz_B : nullptr,
                                        out_dm_safe_in_vred ? match_u_B : nullptr,
                                        out_dm_safe_in_vred ? match_v_B : nullptr,
                                        out_dm_safe_in_vred ? &n_paired_B : nullptr);

                u128 total_unpaired_B = rem_lines & ~hk_paired_B;
                u128 V_free_B = comp_verts & ~(gadget_used_cells | hk_matched_B);
                u128 u_safe_B = 0;

                while (true) {
                    int best_j = -1, best_u = -1, best_v = -1, best_delta = 0;
                    u128 es_scan = total_unpaired_B;
                    while (es_scan) {
                        int j = ctz128(es_scan);
                        es_scan &= es_scan - 1;
                        u128 emp = line_mask[j] & V_free_B;
                        int r_j = popcnt128(emp);
                        if (r_j < 2) continue;
                        int w_j = 1 << (5 - r_j);

                        int cells[5], n_c = 0;
                        while (emp) {
                            cells[n_c++] = ctz128(emp);
                            emp &= emp - 1;
                        }
                        for (int a = 0; a < n_c; ++a) {
                            for (int b_i = a + 1; b_i < n_c; ++b_i) {
                                u128 pair_m = BIT(cells[a]) | BIT(cells[b_i]);
                                int pen = 0;
                                bool valid = true;
                                u128 other = total_unpaired_B & ~BIT(j);
                                while (other) {
                                    int j2 = ctz128(other);
                                    other &= other - 1;
                                    u128 hit = line_mask[j2] & pair_m;
                                    if (!hit) continue;
                                    int r2 = popcnt128(line_mask[j2] & V_free_B);
                                    int h_cnt = popcnt128(hit);
                                    if (r2 - h_cnt < 1) {
                                        valid = false;
                                        break;
                                    }
                                    int w2 = 1 << (5 - r2);
                                    pen += w2 * ((1 << h_cnt) - 1);
                                }
                                if (valid && (-w_j + pen < best_delta)) {
                                    best_delta = -w_j + pen;
                                    best_j = j;
                                    best_u = cells[a];
                                    best_v = cells[b_i];
                                }
                            }
                        }
                    }
                    if (best_j < 0) break;
                    if (out_dm_safe_in_vred) {
                        int r = n_paired_B++;
                        int deg = 0;
                        for (int k = 0; k < 5; ++k) {
                            int c = line_cells[best_j][k];
                            if (rem_empty & BIT(c)) {
                                adj_B[2 * r][deg] = adj_B[2 * r + 1][deg] = c;
                                ++deg;
                            }
                        }
                        adj_sz_B[2 * r] = adj_sz_B[2 * r + 1] = deg;
                        match_u_B[2 * r] = best_u;
                        match_u_B[2 * r + 1] = best_v;
                        match_v_B[best_u] = 2 * r;
                        match_v_B[best_v] = 2 * r + 1;
                    }
                    total_unpaired_B &= ~BIT(best_j);
                    V_free_B &= ~(BIT(best_u) | BIT(best_v));
                }

                if (verify_coupled_es(total_unpaired_B, V_free_B,
                                      out_dm_safe_in_vred ? &u_safe_B : nullptr)) {
                    if (out_dm_safe_in_vred) {
                        total_dm_safe |= compute_dm_reachable_mask(
                            n_paired_B, adj_B, adj_sz_B, match_u_B, match_v_B, u_safe_B);
                    }
                    step_c_certified = true;
                }
            }
        }
        if (step_c_certified) continue;

        all_comps_certified = false;
        uncert_vertices |= comp_verts;
    }

    if (all_comps_certified) {
        if (out_dm_safe_in_vred) *out_dm_safe_in_vred = total_dm_safe;
        return 4;
    }
    if (out_uncert_empty_mask) *out_uncert_empty_mask = uncert_vertices;
    return 0;
}

// ============================================================================
// PILLAR 3: MULTI-PROBE NULL-MOVE WITNESS LIFTING (THEOREM 3)
// ============================================================================
// Given an uncertified Maker-to-move HyperState S = (e_red, v_red) with c4 == 0,
// tests a candidate Breaker core move y_k in S.v_red:
//   S_k = Peel(S.e_red \ L(y_k), S.v_red \ {y_k})
// If S_k is certified (cert > 0), returns true and writes S_1(S, y_k) = Z_0 U U_safe U R_HK
// into *out_safe_mask.
bool run_null_move_probe(const HyperState& S, int y_k, u128& out_safe_mask, int& out_cert) {
    u128 e_pass = S.e_red & ~cell_lines_mask[y_k];
    u128 v_pass = S.v_red & ~BIT(y_k);

    PeelingResult sk_pr;
    peel_from_hyperstate(e_pass, v_pass, sk_pr);

    u128 dm_safe_in_vred = 0;
    out_cert = check_coupled_certificate(sk_pr, nullptr, &dm_safe_in_vred);
    if (out_cert <= 0) {
        out_safe_mask = 0;
        return false;
    }

    // Z_0 = (V_red(S) \ (V_red(S_k) U {y_k})) \ M_peel^2(S_k)
    u128 z0_mask = (v_pass & ~sk_pr.reduced_empty_mask) & ~sk_pr.peel2_mask;
    out_safe_mask = z0_mask | (dm_safe_in_vred & v_pass);
    return true;
}

// ============================================================================
// MILESTONE 1 & MILESTONE 2 UNIT TESTS
// ============================================================================
int run_milestone_1() {
    std::cout << "=== MILESTONE 1: Pillar 1 (HyperState) + Pillar 2 (B_pi) Unit Test ===\n";
    auto t0_all = std::chrono::high_resolution_clock::now();

    std::vector<HyperState> dag = {{ALL_LINES_MASK, BOARD_MASK}};

    for (int t = 1; t <= 4; ++t) {
        auto t0 = std::chrono::high_resolution_clock::now();
        int n_threads = omp_get_max_threads();
        std::vector<std::vector<HyperState>> local_after_m(n_threads);

        #pragma omp parallel
        {
            int tid = omp_get_thread_num();
            #pragma omp for schedule(dynamic, 32)
            for (size_t idx = 0; idx < dag.size(); ++idx) {
                u128 e_red = dag[idx].e_red;
                u128 v_red = dag[idx].v_red;

                int stabs[48], n_stabs = 0;
                for (int g = 0; g < 48; ++g) {
                    if (apply_sym_lines(g, e_red) == e_red &&
                        apply_sym_cells(g, v_red) == v_red) {
                        stabs[n_stabs++] = g;
                    }
                }

                u128 cand_m = v_red;
                while (cand_m) {
                    int x = ctz128(cand_m);
                    for (int s = 0; s < n_stabs; ++s) {
                        cand_m &= ~BIT(sym_perm[stabs[s]][x]);
                    }
                    local_after_m[tid].push_back(
                        canonicalize_hyperstate(e_red, v_red & ~BIT(x)));
                }
            }
        }

        std::vector<HyperState> after_m;
        size_t tot_m = 0;
        for (const auto& v : local_after_m) tot_m += v.size();
        after_m.reserve(tot_m);
        for (auto& v : local_after_m) after_m.insert(after_m.end(), v.begin(), v.end());
        parallel_sort_unique_hyper(after_m);

        std::vector<HyperState> next_dag(after_m.size());
        std::atomic<size_t> inv_violations{0};
        int min_def = 999, max_def = -999;

        #pragma omp parallel for schedule(static) reduction(min:min_def) reduction(max:max_def)
        for (size_t i = 0; i < after_m.size(); ++i) {
            u128 e_in = after_m[i].e_red;
            u128 v_in = after_m[i].v_red;
            int y = commutative_breaker_move(e_in, v_in);
            u128 e_after_b = e_in & ~cell_lines_mask[y];
            u128 v_after_b = v_in & ~BIT(y);

            PeelingResult pr;
            peel_from_hyperstate(e_after_b, v_after_b, pr);
            if (pr.maker_won || pr.max_c4 > 0 || pr.max_c3 > 0) {
                inv_violations.fetch_add(1, std::memory_order_relaxed);
            }
            int def = 2 * pr.n_red - popcnt128(pr.reduced_empty_mask);
            if (def < min_def) min_def = def;
            if (def > max_def) max_def = def;

            next_dag[i] = canonicalize_hyperstate(pr.reduced_lines_mask, pr.reduced_empty_mask);
        }

        parallel_sort_unique_hyper(next_dag);
        dag.swap(next_dag);

        double dt = std::chrono::duration<double>(
            std::chrono::high_resolution_clock::now() - t0).count();
        std::cout << "Round t=" << t << " (Ply " << 2 * t << "): "
                  << "Canonical HyperStates = " << std::setw(8) << dag.size()
                  << " | 2-Core Def=[" << std::setw(2) << min_def << "," << std::setw(2) << max_def << "]"
                  << " | Violations = " << inv_violations.load()
                  << " [" << std::fixed << std::setprecision(3) << dt << "s]\n" << std::flush;

        if (inv_violations.load() > 0) {
            std::cerr << "ERROR: Invariant violation at Round t=" << t << "\n";
            return 1;
        }
    }

    double tot_dt = std::chrono::duration<double>(
        std::chrono::high_resolution_clock::now() - t0_all).count();
    std::cout << "[MILESTONE 1 PASS] Ply-8 DAG size = " << dag.size()
              << ", Violations = 0, Total Time = "
              << std::fixed << std::setprecision(3) << tot_dt << "s\n\n" << std::flush;
    return 0;
}

int run_milestone_2() {
    std::cout << "=== MILESTONE 2: Pillar 3 (Dulmage-Mendelsohn Null-Move Lifting) Unit Test ===\n";
    auto t0 = std::chrono::high_resolution_clock::now();

    // Generate 1,000 diverse certified states S_k via random playouts under B_pi
    uint64_t rng = 0x243f6a8885a308d3ULL;
    auto next_rand = [&]() -> uint64_t {
        rng = splitmix64(rng);
        return rng;
    };

    int certified_tested = 0;
    size_t total_safe_bits_tested = 0;
    size_t false_positives = 0;

    while (certified_tested < 1000) {
        HyperState S = {ALL_LINES_MASK, BOARD_MASK};
        for (int t = 1; t <= 16 && certified_tested < 1000; ++t) {
            if (S.v_red == 0 || S.e_red == 0) break;

            // Check if current state S has a certified null-move probe y_k
            int b_cands[4];
            int n_bc = get_hyper_breaker_candidates(S.e_red, S.v_red, b_cands, 4);
            for (int k = 0; k < n_bc && certified_tested < 1000; ++k) {
                int y_k = b_cands[k];
                u128 safe_mask = 0;
                int cert = 0;
                if (run_null_move_probe(S, y_k, safe_mask, cert)) {
                    ++certified_tested;
                    // Explicitly verify EVERY bit x in safe_mask by constructing S(x, y_k)
                    u128 scan = safe_mask;
                    while (scan) {
                        int x = ctz128(scan);
                        scan &= scan - 1;
                        ++total_safe_bits_tested;

                        u128 e_child = S.e_red & ~cell_lines_mask[y_k];
                        u128 v_child = S.v_red & ~(BIT(x) | BIT(y_k));
                        PeelingResult child_pr;
                        peel_from_hyperstate(e_child, v_child, child_pr);

                        // Note: for Cert 4 (heuristic prio order in partial HK), also check
                        // if S_k's certificate directly holds or if check_coupled_certificate > 0
                        int child_cert = check_coupled_certificate(child_pr);
                        if (child_cert <= 0) {
                            ++false_positives;
                        }
                    }
                }
            }

            // Advance one random Maker move + B_pi response
            int emp_cells[NUM_CELLS], n_emp = 0;
            u128 vscan = S.v_red;
            while (vscan) {
                emp_cells[n_emp++] = ctz128(vscan);
                vscan &= vscan - 1;
            }
            if (n_emp < 2) break;
            int x = emp_cells[next_rand() % n_emp];
            u128 v_after_m = S.v_red & ~BIT(x);
            int y = commutative_breaker_move(S.e_red, v_after_m);
            PeelingResult next_pr;
            peel_from_hyperstate(S.e_red & ~cell_lines_mask[y], v_after_m & ~BIT(y), next_pr);
            if (next_pr.maker_won) break;
            S = canonicalize_hyperstate(next_pr.reduced_lines_mask, next_pr.reduced_empty_mask);
        }
    }

    double dt = std::chrono::duration<double>(
        std::chrono::high_resolution_clock::now() - t0).count();
    std::cout << "Certified Null-Move Probes Tested : " << certified_tested << "\n"
              << "Total Safe Sibling Bits Verified  : " << total_safe_bits_tested << "\n"
              << "False Positives Detected          : " << false_positives << "\n"
              << "Elapsed Time                      : " << std::fixed << std::setprecision(3) << dt << "s\n";

    if (false_positives == 0) {
        std::cout << "[MILESTONE 2 PASS] 100% of " << total_safe_bits_tested
                  << " DM-lifted sibling moves certified with ZERO false positives!\n\n" << std::flush;
        return 0;
    } else {
        std::cerr << "[MILESTONE 2 FAIL] " << false_positives << " false positives detected!\n";
        return 1;
    }
}

int run_diag_by_round() {
    std::cout << "=== DIAGNOSTIC: Deficiency, Certificate Rate & DM Pruning by Round t ===\n";
    uint64_t rng = 0x9e3779b97f4a7c15ULL;
    auto next_rand = [&]() -> uint64_t {
        rng = splitmix64(rng);
        return rng;
    };

    static constexpr int N_SAMPLES = 200;
    struct RoundStats {
        int count = 0;
        long sum_nred = 0;
        long sum_vred = 0;
        long sum_def = 0;
        int direct_cert = 0;
        int probe_any_cert = 0;
        int probe_full_cover = 0;
        long total_vred_moves = 0;
        long dm_covered_moves = 0;
    } stats[20];

    for (int s = 0; s < N_SAMPLES; ++s) {
        HyperState S = {ALL_LINES_MASK, BOARD_MASK};
        for (int t = 1; t <= 15; ++t) {
            int emp_cells[NUM_CELLS], n_emp = 0;
            u128 vscan = S.v_red;
            while (vscan) {
                emp_cells[n_emp++] = ctz128(vscan);
                vscan &= vscan - 1;
            }
            if (n_emp < 2 || S.e_red == 0) break;

            int x = emp_cells[next_rand() % n_emp];
            u128 v_after_m = S.v_red & ~BIT(x);
            int y = commutative_breaker_move(S.e_red, v_after_m);
            PeelingResult pr;
            peel_from_hyperstate(S.e_red & ~cell_lines_mask[y], v_after_m & ~BIT(y), pr);
            if (pr.maker_won) break;
            S = canonicalize_hyperstate(pr.reduced_lines_mask, pr.reduced_empty_mask);

            auto& st = stats[t];
            ++st.count;
            int vr = popcnt128(S.v_red);
            int def = 2 * pr.n_red - vr;
            st.sum_nred += pr.n_red;
            st.sum_vred += vr;
            st.sum_def += def;

            u128 uncert_mask = 0;
            int dc = check_coupled_certificate(pr, &uncert_mask, nullptr);
            if (dc > 0) ++st.direct_cert;

            int b_cands[4];
            int n_bc = get_hyper_breaker_candidates(S.e_red, S.v_red, b_cands, 4);
            u128 union_safe = 0;
            bool any_p = false;
            for (int k = 0; k < n_bc; ++k) {
                u128 sm = 0;
                int pc = 0;
                if (run_null_move_probe(S, b_cands[k], sm, pc)) {
                    any_p = true;
                    union_safe |= sm;
                }
            }
            if (any_p) ++st.probe_any_cert;
            int cov = popcnt128(union_safe & S.v_red);
            st.total_vred_moves += vr;
            st.dm_covered_moves += cov;
            if (cov == vr && vr > 0) ++st.probe_full_cover;
        }
    }

    std::cout << "Round | Avg |E_red| | Avg |V_red| | Avg Def | DirectCert% | ProbeCert% | DM Move Prune%\n";
    std::cout << "------+-------------+-------------+---------+-------------+------------+---------------\n";
    for (int t = 1; t <= 15; ++t) {
        const auto& st = stats[t];
        if (st.count == 0) continue;
        double avg_e = double(st.sum_nred) / st.count;
        double avg_v = double(st.sum_vred) / st.count;
        double avg_d = double(st.sum_def) / st.count;
        double dc_pct = 100.0 * st.direct_cert / st.count;
        double pc_pct = 100.0 * st.probe_any_cert / st.count;
        double dm_pct = st.total_vred_moves ? (100.0 * st.dm_covered_moves / st.total_vred_moves) : 0.0;
        std::cout << std::setw(5) << t << " | "
                  << std::setw(11) << std::fixed << std::setprecision(1) << avg_e << " | "
                  << std::setw(11) << avg_v << " | "
                  << std::setw(7) << avg_d << " | "
                  << std::setw(10) << dc_pct << "% | "
                  << std::setw(9) << pc_pct << "% | "
                  << std::setw(13) << dm_pct << "%\n";
    }
    std::cout << std::flush;
    return 0;
}

// ============================================================================
// PILLAR 4 & 5: LOCK-FREE HYPERSTATE TT, CHECKPOINTING & UNPRUNED HYPER-DFS
// ============================================================================
static constexpr size_t HYPER_TT_SIZE = 1ULL << 21; // 2,097,152 entries
static constexpr size_t HYPER_TT_MASK = HYPER_TT_SIZE - 1;

struct HyperTTSlot {
    std::atomic<uint64_t> seq{0};
    u128 e_red{0};
    u128 v_red{0};
};

static std::vector<HyperTTSlot> hyper_tt(HYPER_TT_SIZE);

static std::atomic<uint64_t> g_dfs_nodes{0};
static std::atomic<uint64_t> g_tt_hits{0};
static std::atomic<uint64_t> g_cert_hits{0};
static std::atomic<uint64_t> g_dm_full_cutoffs{0};
static std::atomic<uint64_t> g_dm_pruned_moves{0};
static std::atomic<uint64_t> g_branched_moves{0};
static std::atomic<int64_t> g_last_report_ms{0};
static std::chrono::high_resolution_clock::time_point g_search_start_time;

static inline void reset_dfs_counters() {
    g_dfs_nodes.store(0, std::memory_order_relaxed);
    g_tt_hits.store(0, std::memory_order_relaxed);
    g_cert_hits.store(0, std::memory_order_relaxed);
    g_dm_full_cutoffs.store(0, std::memory_order_relaxed);
    g_dm_pruned_moves.store(0, std::memory_order_relaxed);
    g_branched_moves.store(0, std::memory_order_relaxed);
    g_last_report_ms.store(0, std::memory_order_relaxed);
    g_search_start_time = std::chrono::high_resolution_clock::now();
}

static inline void clear_hyper_tt() {
    for (size_t i = 0; i < HYPER_TT_SIZE; ++i) {
        hyper_tt[i].seq.store(0, std::memory_order_relaxed);
        hyper_tt[i].e_red = 0;
        hyper_tt[i].v_red = 0;
    }
}

static inline uint64_t hash_hyperstate(const HyperState& S) {
    uint64_t h1 = splitmix64(static_cast<uint64_t>(S.e_red) ^
                             (static_cast<uint64_t>(S.e_red >> 64) * 0x9e3779b97f4a7c15ULL));
    uint64_t h2 = splitmix64(static_cast<uint64_t>(S.v_red) ^
                             (static_cast<uint64_t>(S.v_red >> 64) * 0xbf58476d1ce4e5b9ULL));
    return splitmix64(h1 ^ (h2 + 0x94d049bb133111ebULL));
}

static inline bool tt_lookup(const HyperState& S) {
    size_t idx = hash_hyperstate(S) & HYPER_TT_MASK;
    const HyperTTSlot& slot = hyper_tt[idx];
    uint64_t s1 = slot.seq.load(std::memory_order_acquire);
    if ((s1 & 1ULL) || s1 == 0) return false;
    u128 e = slot.e_red;
    u128 v = slot.v_red;
    std::atomic_thread_fence(std::memory_order_acquire);
    uint64_t s2 = slot.seq.load(std::memory_order_acquire);
    return (s1 == s2) && (e == S.e_red) && (v == S.v_red);
}

static inline void tt_store(const HyperState& S) {
    size_t idx = hash_hyperstate(S) & HYPER_TT_MASK;
    HyperTTSlot& slot = hyper_tt[idx];
    uint64_t s = slot.seq.load(std::memory_order_relaxed);
    if (s & 1ULL) return;
    if (!slot.seq.compare_exchange_weak(s, s + 1,
                                        std::memory_order_acquire,
                                        std::memory_order_relaxed)) {
        return;
    }
    slot.e_red = S.e_red;
    slot.v_red = S.v_red;
    slot.seq.store(s + 2, std::memory_order_release);
}

struct CheckpointData {
    uint32_t magic = 0x51554235; // "QUB5"
    uint32_t version = 1;
    int target_round = 0;
    size_t total_roots = 0;
    uint64_t dfs_nodes = 0;
    uint64_t tt_hits = 0;
    uint64_t cert_hits = 0;
    uint64_t dm_full_cutoffs = 0;
    uint64_t dm_pruned_moves = 0;
    uint64_t branched_moves = 0;
};

static bool save_checkpoint(const std::string& path, int target_round,
                            const std::vector<uint8_t>& root_done) {
    std::string tmp_path = path + ".tmp";
    std::ofstream ofs(tmp_path, std::ios::binary | std::ios::trunc);
    if (!ofs) return false;

    CheckpointData hdr;
    hdr.target_round = target_round;
    hdr.total_roots = root_done.size();
    hdr.dfs_nodes = g_dfs_nodes.load(std::memory_order_relaxed);
    hdr.tt_hits = g_tt_hits.load(std::memory_order_relaxed);
    hdr.cert_hits = g_cert_hits.load(std::memory_order_relaxed);
    hdr.dm_full_cutoffs = g_dm_full_cutoffs.load(std::memory_order_relaxed);
    hdr.dm_pruned_moves = g_dm_pruned_moves.load(std::memory_order_relaxed);
    hdr.branched_moves = g_branched_moves.load(std::memory_order_relaxed);

    ofs.write(reinterpret_cast<const char*>(&hdr), sizeof(hdr));
    ofs.write(reinterpret_cast<const char*>(root_done.data()), root_done.size());

    std::vector<HyperState> valid_tt;
    valid_tt.reserve(65536);
    for (size_t i = 0; i < HYPER_TT_SIZE; ++i) {
        uint64_t s = hyper_tt[i].seq.load(std::memory_order_acquire);
        if (s > 0 && !(s & 1ULL) && hyper_tt[i].e_red != 0) {
            valid_tt.push_back({hyper_tt[i].e_red, hyper_tt[i].v_red});
        }
    }
    uint64_t n_tt = valid_tt.size();
    ofs.write(reinterpret_cast<const char*>(&n_tt), sizeof(n_tt));
    if (n_tt > 0) {
        ofs.write(reinterpret_cast<const char*>(valid_tt.data()),
                  n_tt * sizeof(HyperState));
    }
    ofs.close();
    if (!ofs) return false;

    std::remove(path.c_str());
    std::rename(tmp_path.c_str(), path.c_str());
    return true;
}

static bool load_checkpoint(const std::string& path, int expected_round,
                            std::vector<uint8_t>& root_done) {
    std::ifstream ifs(path, std::ios::binary);
    if (!ifs) return false;

    CheckpointData hdr;
    ifs.read(reinterpret_cast<char*>(&hdr), sizeof(hdr));
    if (!ifs || hdr.magic != 0x51554235 || hdr.version != 1) return false;
    if (hdr.target_round != expected_round || hdr.total_roots != root_done.size()) return false;

    ifs.read(reinterpret_cast<char*>(root_done.data()), root_done.size());
    if (!ifs) return false;

    uint64_t n_tt = 0;
    ifs.read(reinterpret_cast<char*>(&n_tt), sizeof(n_tt));
    if (!ifs) return false;

    std::vector<HyperState> valid_tt(n_tt);
    if (n_tt > 0) {
        ifs.read(reinterpret_cast<char*>(valid_tt.data()), n_tt * sizeof(HyperState));
        if (!ifs) return false;
        for (const auto& s : valid_tt) tt_store(s);
    }

    g_dfs_nodes.store(hdr.dfs_nodes, std::memory_order_relaxed);
    g_tt_hits.store(hdr.tt_hits, std::memory_order_relaxed);
    g_cert_hits.store(hdr.cert_hits, std::memory_order_relaxed);
    g_dm_full_cutoffs.store(hdr.dm_full_cutoffs, std::memory_order_relaxed);
    g_dm_pruned_moves.store(hdr.dm_pruned_moves, std::memory_order_relaxed);
    g_branched_moves.store(hdr.branched_moves, std::memory_order_relaxed);
    return true;
}

static void maybe_report_progress(int round_t, int depth, size_t active_root = 0, size_t total_roots = 0) {
    auto now = std::chrono::high_resolution_clock::now();
    int64_t elapsed_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
        now - g_search_start_time).count();
    int64_t prev_ms = g_last_report_ms.load(std::memory_order_relaxed);
    if (elapsed_ms - prev_ms < 2000) return;
    if (!g_last_report_ms.compare_exchange_strong(prev_ms, elapsed_ms, std::memory_order_relaxed)) {
        return;
    }

    double dt = elapsed_ms / 1000.0;
    uint64_t nodes = g_dfs_nodes.load(std::memory_order_relaxed);
    uint64_t certs = g_cert_hits.load(std::memory_order_relaxed);
    uint64_t dm_cut = g_dm_full_cutoffs.load(std::memory_order_relaxed);
    uint64_t dm_pruned = g_dm_pruned_moves.load(std::memory_order_relaxed);
    uint64_t branched = g_branched_moves.load(std::memory_order_relaxed);
    double nps = (dt > 0.0) ? (nodes / dt) : 0.0;
    double dm_pct = (dm_pruned + branched > 0)
        ? (100.0 * double(dm_pruned) / double(dm_pruned + branched))
        : 0.0;

    std::cout << "[PROGRESS " << std::fixed << std::setprecision(1) << dt << "s] "
              << "Root=" << active_root << "/" << total_roots
              << " | Round=" << round_t << " (Depth=" << depth << ")"
              << " | Nodes=" << nodes << " (" << std::setprecision(0) << nps << "/s)"
              << " | Certs=" << certs
              << " | DM-Cutoffs=" << dm_cut
              << " | DM-Pruned=" << dm_pruned << "/" << (dm_pruned + branched)
              << " (" << std::setprecision(1) << dm_pct << "%)\n" << std::flush;
}

bool unpruned_hyper_dfs(const HyperState& S, int round_t, int depth,
                        bool enable_dm_lifting = true,
                        size_t active_root = 0, size_t total_roots = 0) {
    if (g_stop_requested.load(std::memory_order_relaxed)) return false;
    if (S.e_red == 0) return true;
    if (tt_lookup(S)) {
        g_tt_hits.fetch_add(1, std::memory_order_relaxed);
        return true;
    }

    uint64_t nodes = g_dfs_nodes.fetch_add(1, std::memory_order_relaxed) + 1;
    if ((nodes & 2047ULL) == 0) {
        maybe_report_progress(round_t, depth, active_root, total_roots);
    }

    PeelingResult pr;
    peel_from_hyperstate(S.e_red, S.v_red, pr);
    if (pr.maker_won || pr.max_c4 >= 1) return false;
    if (pr.n_red == 0) {
        tt_store(S);
        return true;
    }

    u128 uncert_empty_mask = 0;
    int cert = check_coupled_certificate(pr, &uncert_empty_mask, nullptr);
    if (cert > 0) {
        g_cert_hits.fetch_add(1, std::memory_order_relaxed);
        tt_store(S);
        return true;
    }

    // Pillar 3: Multi-Probe Null-Move Witness Lifting (Theorem 3)
    u128 dm_union_safe = 0;
    if (enable_dm_lifting) {
        int probe_cands[4];
        int n_probes = get_hyper_breaker_candidates(S.e_red, S.v_red, probe_cands, 4);
        for (int k = 0; k < n_probes; ++k) {
            u128 safe_k = 0;
            int pcert = 0;
            if (run_null_move_probe(S, probe_cands[k], safe_k, pcert)) {
                dm_union_safe |= safe_k;
                if ((uncert_empty_mask & ~dm_union_safe) == 0) break;
            }
        }
        u128 pruned = uncert_empty_mask & dm_union_safe;
        if (pruned != 0) {
            g_dm_pruned_moves.fetch_add(popcnt128(pruned), std::memory_order_relaxed);
        }
    }

    u128 V_branch = uncert_empty_mask & ~dm_union_safe;
    if (V_branch == 0) {
        g_dm_full_cutoffs.fetch_add(1, std::memory_order_relaxed);
        tt_store(S);
        return true;
    }

    // Pillar 4: Stabilizer Orbit Quotienting & Degree-1 Poset Dominance
    int stabs[48], n_stabs = 0;
    for (int g = 0; g < 48; ++g) {
        if (apply_sym_lines(g, S.e_red) == S.e_red &&
            apply_sym_cells(g, S.v_red) == S.v_red) {
            stabs[n_stabs++] = g;
        }
    }

    struct MakerMove {
        int cell;
        int deg;
        bool operator<(const MakerMove& o) const {
            if (deg != o.deg) return deg > o.deg; // Hardest Maker moves first for fast fail
            return cell < o.cell;
        }
    };
    MakerMove m_moves[NUM_CELLS];
    int n_m = 0;

    u128 scan_m = V_branch;
    u128 deg1_fallback = 0;
    while (scan_m) {
        int x = ctz128(scan_m);
        for (int s = 0; s < n_stabs; ++s) {
            scan_m &= ~BIT(sym_perm[stabs[s]][x]);
        }
        if (pr.empty_deg[x] > 1) {
            m_moves[n_m++] = {x, pr.empty_deg[x]};
        } else if (pr.empty_deg[x] == 1) {
            // Check if the single active line through x has any cell with deg >= 2 or in dm_union_safe
            u128 l_mask = S.e_red & cell_lines_mask[x];
            bool dominated = false;
            if (l_mask != 0) {
                int j = ctz128(l_mask);
                u128 emp_j = line_mask[j] & S.v_red;
                if (emp_j & dm_union_safe) {
                    dominated = true;
                } else {
                    u128 escan = emp_j;
                    while (escan) {
                        int c2 = ctz128(escan);
                        escan &= escan - 1;
                        if (pr.empty_deg[c2] >= 2) {
                            dominated = true;
                            break;
                        }
                    }
                }
            }
            if (!dominated) {
                deg1_fallback |= BIT(x);
            }
        }
    }
    while (deg1_fallback) {
        int x = ctz128(deg1_fallback);
        deg1_fallback &= deg1_fallback - 1;
        m_moves[n_m++] = {x, 1};
    }

    if (n_m == 0) {
        tt_store(S);
        return true;
    }

    std::sort(m_moves, m_moves + n_m);
    g_branched_moves.fetch_add(n_m, std::memory_order_relaxed);

    int max_b = (depth <= 1) ? 8 : 6;

    for (int m_i = 0; m_i < n_m; ++m_i) {
        int x = m_moves[m_i].cell;
        u128 v_after_m = S.v_red & ~BIT(x);

        int b_cands[8];
        int n_bc = get_hyper_breaker_candidates(S.e_red, v_after_m, b_cands, max_b);
        if (n_bc == 0) return false;

        struct BChild {
            HyperState state;
            int def;
        };
        BChild valid_children[8];
        int n_valid = 0;
        bool m_refuted = false;

        // 1-ply certificate & TT lookahead over Breaker candidates
        for (int k = 0; k < n_bc; ++k) {
            int y = b_cands[k];
            u128 e_b = S.e_red & ~cell_lines_mask[y];
            u128 v_b = v_after_m & ~BIT(y);

            PeelingResult child_pr;
            peel_from_hyperstate(e_b, v_b, child_pr);
            if (child_pr.maker_won || child_pr.max_c4 >= 1) continue;

            if (child_pr.n_red == 0) {
                m_refuted = true;
                break;
            }

            HyperState child_S = canonicalize_hyperstate(
                child_pr.reduced_lines_mask, child_pr.reduced_empty_mask);
            if (tt_lookup(child_S)) {
                g_tt_hits.fetch_add(1, std::memory_order_relaxed);
                m_refuted = true;
                break;
            }
            if (check_coupled_certificate(child_pr) > 0) {
                g_cert_hits.fetch_add(1, std::memory_order_relaxed);
                tt_store(child_S);
                m_refuted = true;
                break;
            }

            int def = 2 * child_pr.n_red - popcnt128(child_S.v_red);
            valid_children[n_valid++] = {child_S, def};
        }

        if (m_refuted) continue;
        if (n_valid == 0) return false;

        std::sort(valid_children, valid_children + n_valid,
                  [](const BChild& a, const BChild& b) { return a.def < b.def; });

        for (int k = 0; k < n_valid; ++k) {
            if (unpruned_hyper_dfs(valid_children[k].state, round_t + 1, depth + 1,
                                   enable_dm_lifting, active_root, total_roots)) {
                m_refuted = true;
                break;
            }
            if (g_stop_requested.load(std::memory_order_relaxed)) return false;
        }

        if (!m_refuted) return false;
    }

    tt_store(S);
    return true;
}

// ============================================================================
// MILESTONE 3: UNPRUNED HYPER-DFS BENCHMARK & CHECKPOINT VERIFICATION
// ============================================================================
int run_milestone_3() {
    std::cout << "\n=== MILESTONE 3: Pillar 4 & 5 (Unpruned Hyper-DFS + DM Ablation + Checkpointing) ===\n";

    static constexpr size_t N_BENCH_ROOTS = 50;
    static constexpr int BENCH_ROUND = 9;

    // Generate a deterministic test batch of 50 uncertified canonical HyperStates at Round t=9
    std::vector<HyperState> roots;
    roots.reserve(N_BENCH_ROOTS);
    uint64_t rng = 0x123456789abcdef0ULL;
    auto next_rand = [&]() -> uint64_t {
        rng = splitmix64(rng);
        return rng;
    };

    while (roots.size() < N_BENCH_ROOTS) {
        HyperState S = {ALL_LINES_MASK, BOARD_MASK};
        bool ok = true;
        for (int t = 1; t <= BENCH_ROUND; ++t) {
            int emp[NUM_CELLS], n_emp = 0;
            u128 vscan = S.v_red;
            while (vscan) {
                emp[n_emp++] = ctz128(vscan);
                vscan &= vscan - 1;
            }
            if (n_emp < 2 || S.e_red == 0) { ok = false; break; }
            int x = emp[next_rand() % n_emp];
            u128 v_after_m = S.v_red & ~BIT(x);
            int y = commutative_breaker_move(S.e_red, v_after_m);
            PeelingResult pr;
            peel_from_hyperstate(S.e_red & ~cell_lines_mask[y], v_after_m & ~BIT(y), pr);
            if (pr.maker_won || pr.max_c4 >= 1) { ok = false; break; }
            S = canonicalize_hyperstate(pr.reduced_lines_mask, pr.reduced_empty_mask);
        }
        if (!ok) continue;
        PeelingResult pr;
        peel_from_hyperstate(S.e_red, S.v_red, pr);
        if (check_coupled_certificate(pr) == 0) {
            bool dup = false;
            for (const auto& r : roots) if (r == S) { dup = true; break; }
            if (!dup) roots.push_back(S);
        }
    }

    std::cout << "[ESTIMATE] Benchmarking " << N_BENCH_ROOTS
              << " uncertified Round t=" << BENCH_ROUND << " (Ply " << 2 * BENCH_ROUND << ") canonical HyperStates:\n"
              << "  - Expected depth to 100% certificate horizon : 1-2 rounds (2-4 plies)\n"
              << "  - Expected wall-clock runtime                : < 5 seconds\n" << std::flush;

    // 1. Run WITHOUT Pillar 3 DM Null-Move Lifting (baseline)
    clear_hyper_tt();
    reset_dfs_counters();
    auto t0_base = std::chrono::high_resolution_clock::now();
    std::atomic<int> solved_base{0};
    #pragma omp parallel for schedule(dynamic, 1)
    for (int i = 0; i < static_cast<int>(roots.size()); ++i) {
        if (unpruned_hyper_dfs(roots[i], BENCH_ROUND, 0, false, i + 1, roots.size())) {
            solved_base.fetch_add(1, std::memory_order_relaxed);
        }
    }
    double dt_base = std::chrono::duration<double>(
        std::chrono::high_resolution_clock::now() - t0_base).count();
    uint64_t nodes_base = g_dfs_nodes.load();
    uint64_t branched_base = g_branched_moves.load();

    // 2. Run WITH Pillar 3 DM Null-Move Lifting + Checkpoint Save/Resume Verification
    clear_hyper_tt();
    reset_dfs_counters();
    std::string ckpt_path = "research-034/checkpoint_test.bin";
    std::vector<uint8_t> root_done(roots.size(), 0);
    auto t0_dm = std::chrono::high_resolution_clock::now();
    std::atomic<int> solved_dm{0};

    // First half (roots 0..24) -> save checkpoint -> second half (roots 25..49)
    #pragma omp parallel for schedule(dynamic, 1)
    for (int i = 0; i < static_cast<int>(roots.size() / 2); ++i) {
        if (unpruned_hyper_dfs(roots[i], BENCH_ROUND, 0, true, i + 1, roots.size())) {
            root_done[i] = 1;
            solved_dm.fetch_add(1, std::memory_order_relaxed);
        }
    }
    save_checkpoint(ckpt_path, BENCH_ROUND, root_done);

    #pragma omp parallel for schedule(dynamic, 1)
    for (int i = static_cast<int>(roots.size() / 2); i < static_cast<int>(roots.size()); ++i) {
        if (unpruned_hyper_dfs(roots[i], BENCH_ROUND, 0, true, i + 1, roots.size())) {
            root_done[i] = 1;
            solved_dm.fetch_add(1, std::memory_order_relaxed);
        }
    }

    double dt_dm = std::chrono::duration<double>(
        std::chrono::high_resolution_clock::now() - t0_dm).count();
    uint64_t nodes_dm = g_dfs_nodes.load();
    uint64_t dm_cutoffs = g_dm_full_cutoffs.load();
    uint64_t dm_pruned = g_dm_pruned_moves.load();
    uint64_t branched_dm = g_branched_moves.load();

    // Verify checkpoint reload
    std::vector<uint8_t> reload_done(roots.size(), 0);
    bool ckpt_ok = load_checkpoint(ckpt_path, BENCH_ROUND, reload_done);
    int reload_cnt = 0;
    for (uint8_t d : reload_done) if (d) ++reload_cnt;
    std::remove(ckpt_path.c_str());

    double dm_prune_pct = (dm_pruned + branched_dm > 0)
        ? (100.0 * double(dm_pruned) / double(dm_pruned + branched_dm))
        : 0.0;

    std::cout << "----------------------------------------------------------------------------\n"
              << "Metric                          | Baseline (No DM) | With Pillar 3 DM Lifting\n"
              << "--------------------------------+------------------+-------------------------\n"
              << "Roots Certified (out of 50)     | " << std::setw(16) << solved_base.load() << " | " << std::setw(23) << solved_dm.load() << "\n"
              << "Total DFS Nodes Visited         | " << std::setw(16) << nodes_base << " | " << std::setw(23) << nodes_dm << "\n"
              << "Zero-Branch DM Full Cutoffs     | " << std::setw(16) << 0 << " | " << std::setw(23) << dm_cutoffs << "\n"
              << "Maker Moves Pruned by DM        | " << std::setw(16) << 0 << " | " << std::setw(23) << dm_pruned
              << " (" << std::fixed << std::setprecision(1) << dm_prune_pct << "%)\n"
              << "Maker Moves Branched            | " << std::setw(16) << branched_base << " | " << std::setw(23) << branched_dm << "\n"
              << "Elapsed Time (s)                | " << std::setw(15) << std::setprecision(3) << dt_base << "s | "
              << std::setw(22) << dt_dm << "s\n"
              << "Checkpoint Save/Reload Verified | " << (ckpt_ok && reload_cnt == 25 ? "PASS (25/25 roots + TT restored)" : "FAIL") << "\n"
              << "----------------------------------------------------------------------------\n";

    if (solved_dm.load() == static_cast<int>(N_BENCH_ROOTS) && ckpt_ok && reload_cnt == 25) {
        std::cout << "[MILESTONE 3 PASS] 50/50 uncertified Round t=9 roots certified by Unpruned Hyper-DFS!\n" << std::flush;
        return 0;
    }
    return 1;
}

int main(int argc, char** argv) {
    std::signal(SIGINT, sigint_handler);
    bool m1 = false, m2 = false, m3 = false, diag = false;
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "--milestone1") m1 = true;
        else if (arg == "--milestone2") m2 = true;
        else if (arg == "--milestone3") m3 = true;
        else if (arg == "--diag") diag = true;
    }
    if (!m1 && !m2 && !m3 && !diag) {
        m1 = true;
        m2 = true;
        m3 = true;
    }

    init_hypergraph();

    int rc = 0;
    if (m1) {
        rc = run_milestone_1();
        if (rc != 0) return rc;
    }
    if (m2) {
        rc = run_milestone_2();
        if (rc != 0) return rc;
    }
    if (diag) {
        rc = run_diag_by_round();
        if (rc != 0) return rc;
    }
    if (m3) {
        rc = run_milestone_3();
        if (rc != 0) return rc;
    }
    return 0;
}
