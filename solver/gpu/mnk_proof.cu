/*
 * mnk_proof.cu
 *
 * Computational draw proof for (m, n, k)-games: GPU greedy proof, CPU exact repair,
 * GPU verification.  Everything stays in GPU memory and host RAM (no disk spilling).
 *
 * ------------------------------------------------------------------------------------------
 * What is proved
 * ------------------------------------------------------------------------------------------
 *   "P1 cannot force a win."  With strategy stealing (MNKStrategyStealing.v,
 *   mnk_value_win_or_draw) this means the game is a draw.
 *
 *   The proof is an AND/OR DAG over canonical positions (board symmetry group D4 or D2):
 *     - P1 nodes (P1 to move) expand every free cell;
 *     - P2 nodes get one reply, chosen by a deterministic threat-aware greedy rule.
 *   Sound leaves:
 *     - P1 node: board full, or es_inv  phi_P1 + max_free w_P1 < 2^k  (P1 cannot win).
 *     - P2 node: board full, P2 completes a line, or Breaker-first ES  phi_P1 < 2^k.
 *     - P2 node in the set H of positions proved held exactly by the CPU solver.
 *   Failures (positions where the greedy proof breaks):
 *     - P1 node where P1 completes a line;
 *     - P2 node where P1 has two completion cells (P2 cannot block both).
 *
 * ------------------------------------------------------------------------------------------
 * Pipeline
 * ------------------------------------------------------------------------------------------
 *   1. GPU pass: level-synchronous greedy proof over P1-to-move levels (ply = stone count, so
 *      levels never overlap).  A level that does not fit into the device buffer is split
 *      into sorted halves kept in host RAM.  Every processed P1 node is inserted into a Bloom
 *      filter.
 *   2. CPU cascade (OpenMP): starting from the lost P2 nodes, climb to their bad P1 parents
 *      (kept only if the Bloom filter says they were visited and they are internal), then to
 *      the P2 nodes whose greedy reply leads there.  Each such P2 node is decided by an exact
 *      null-window search: held nodes join H, lost or undecided ones continue the climb.
 *   3. GPU verification: the greedy proof again, with H as leaves.  Zero failures completes
 *      the proof.  Soundness rests only on this pass and on the exact solver; the cascade is
 *      merely the procedure that finds H.
 *
 * ------------------------------------------------------------------------------------------
 * Build and usage (WSL, CUDA 12.x)
 * ------------------------------------------------------------------------------------------
 *   nvcc -O3 -std=c++17 -arch=sm_89 -Xcompiler -fopenmp,-march=native -o mnk_proof mnk_proof.cu -lgomp
 *   ./mnk_proof m n k [bloom_log2=34] [level_capacity=80000000] [sub_batch=500000] [exact_node_limit=50000000]
 */

#include <cuda_runtime.h>
#include <omp.h>
#include <thrust/execution_policy.h>
#include <thrust/remove.h>
#include <thrust/sort.h>
#include <thrust/unique.h>

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <unordered_set>
#include <utility>
#include <vector>

using Bitboard = uint64_t;

constexpr int kMaxCells = 64;
constexpr int kMaxLines = 256;
constexpr int kMaxSymmetries = 8;
constexpr int kBloomProbes = 5;
constexpr int kThreadsPerBlock = 128;

/* =========================================================================================
 * Error handling
 * ========================================================================================= */

#define CUDA_CHECK(call)                                                                     \
    do {                                                                                     \
        const cudaError_t status_ = (call);                                                  \
        if (status_ != cudaSuccess) {                                                        \
            std::fprintf(stderr, "CUDA error '%s' at %s:%d\n", cudaGetErrorString(status_),  \
                         __FILE__, __LINE__);                                                \
            std::exit(1);                                                                    \
        }                                                                                    \
    } while (0)

/* Owning wrapper for device memory: freed exactly once, never copied. */
template <typename T>
class DeviceBuffer {
public:
    DeviceBuffer() = default;
    explicit DeviceBuffer(size_t count) { allocate(count); }
    ~DeviceBuffer() { release(); }

    DeviceBuffer(const DeviceBuffer&) = delete;
    DeviceBuffer& operator=(const DeviceBuffer&) = delete;

    DeviceBuffer(DeviceBuffer&& other) noexcept
        : data_(std::exchange(other.data_, nullptr)), count_(std::exchange(other.count_, 0)) {}

    DeviceBuffer& operator=(DeviceBuffer&& other) noexcept
    {
        if (this != &other) {
            release();
            data_ = std::exchange(other.data_, nullptr);
            count_ = std::exchange(other.count_, 0);
        }
        return *this;
    }

    void allocate(size_t count)
    {
        release();
        if (count > 0) {
            CUDA_CHECK(cudaMalloc(&data_, count * sizeof(T)));
            count_ = count;
        }
    }

    void release()
    {
        if (data_ != nullptr) {
            cudaFree(data_);
            data_ = nullptr;
            count_ = 0;
        }
    }

    T* get() const { return data_; }
    size_t size() const { return count_; }

private:
    T* data_ = nullptr;
    size_t count_ = 0;
};

/* =========================================================================================
 * Positions, hashing
 * ========================================================================================= */

struct Position {
    Bitboard p1;
    Bitboard p2;
};

__host__ __device__ inline bool operator<(const Position& a, const Position& b)
{
    return a.p1 < b.p1 || (a.p1 == b.p1 && a.p2 < b.p2);
}

__host__ __device__ inline bool operator==(const Position& a, const Position& b)
{
    return a.p1 == b.p1 && a.p2 == b.p2;
}

/* Empty output slots are marked with all bits set (never a legal position). */
__host__ __device__ inline Position marker_position()
{
    return Position{ ~Bitboard(0), ~Bitboard(0) };
}

struct IsMarker {
    __host__ __device__ bool operator()(const Position& p) const { return p == marker_position(); }
};

__host__ __device__ inline uint64_t mix64(uint64_t z)
{
    z ^= z >> 30;
    z *= 0xbf58476d1ce4e5b9ull;
    z ^= z >> 27;
    z *= 0x94d049bb133111ebull;
    z ^= z >> 31;
    return z;
}

struct PositionHash {
    size_t operator()(const Position& p) const { return static_cast<size_t>(mix64(p.p1 ^ mix64(p.p2))); }
};

using PositionSet = std::unordered_set<Position, PositionHash>;

/* Double hashing for the Bloom filter: probe q uses bit (h1 + q * h2) mod 2^b. */
__host__ __device__ inline void bloom_hashes(const Position& p, uint64_t& h1, uint64_t& h2)
{
    h1 = mix64(p.p1 ^ mix64(p.p2 + 0x9e3779b97f4a7c15ull));
    h2 = mix64(h1 ^ 0xda942042e4dd58b5ull) | 1;
}

__host__ __device__ inline int popcount64(Bitboard b)
{
#ifdef __CUDA_ARCH__
    return __popcll(b);
#else
    return __builtin_popcountll(b);
#endif
}

__host__ __device__ inline int lowest_cell(Bitboard b)
{
#ifdef __CUDA_ARCH__
    return __ffsll(static_cast<long long>(b)) - 1;
#else
    return __builtin_ctzll(b);
#endif
}

__host__ __device__ inline Bitboard cell_bit(int cell)
{
    return Bitboard(1) << cell;
}

/* =========================================================================================
 * Board geometry, shared by host and device code
 * ========================================================================================= */

struct Geometry {
    const Bitboard* lines;
    const uint8_t (*image)[kMaxCells];   /* image[t][cell] under symmetry t */
    int line_count;
    int cell_count;
    int k;
    int symmetry_count;
    Bitboard all_cells;
};

/* Host copy. */
struct HostBoard {
    int rows = 0;
    int cols = 0;
    int k = 0;
    int cell_count = 0;
    int line_count = 0;
    int symmetry_count = 0;
    Bitboard all_cells = 0;
    Bitboard lines[kMaxLines] = {};
    uint8_t image[kMaxSymmetries][kMaxCells] = {};

    Geometry geometry() const
    {
        return Geometry{ lines, image, line_count, cell_count, k, symmetry_count, all_cells };
    }
};

static HostBoard host_board;

/* Device copy (constant memory). */
__constant__ Bitboard d_lines[kMaxLines];
__constant__ uint8_t d_image[kMaxSymmetries][kMaxCells];
__constant__ int d_line_count;
__constant__ int d_cell_count;
__constant__ int d_k;
__constant__ int d_symmetry_count;
__constant__ Bitboard d_all_cells;
__constant__ uint64_t d_bloom_mask;

__device__ inline Geometry device_geometry()
{
    return Geometry{ d_lines, d_image, d_line_count, d_cell_count, d_k, d_symmetry_count, d_all_cells };
}

static bool init_board(int rows, int cols, int k)
{
    if (rows < 1 || cols < 1 || rows * cols > kMaxCells || k < 2 || k > 16) {
        std::fprintf(stderr, "unsupported board (%d,%d,%d)\n", rows, cols, k);
        return false;
    }
    HostBoard& b = host_board;
    b.rows = rows;
    b.cols = cols;
    b.k = k;
    b.cell_count = rows * cols;
    b.all_cells = b.cell_count == 64 ? ~Bitboard(0) : cell_bit(b.cell_count) - 1;

    /* Same line order as the original prototype: rows, columns, diagonals, anti-diagonals. */
    b.line_count = 0;
    auto add_line = [&](int r0, int c0, int dr, int dc) {
        Bitboard line = 0;
        for (int i = 0; i < k; i++) {
            line |= cell_bit((r0 + i * dr) * cols + (c0 + i * dc));
        }
        b.lines[b.line_count++] = line;
    };
    for (int r = 0; r < rows; r++)
        for (int c = 0; c + k <= cols; c++) add_line(r, c, 0, 1);
    for (int c = 0; c < cols; c++)
        for (int r = 0; r + k <= rows; r++) add_line(r, c, 1, 0);
    for (int r = 0; r + k <= rows; r++)
        for (int c = 0; c + k <= cols; c++) add_line(r, c, 1, 1);
    for (int r = k - 1; r < rows; r++)
        for (int c = 0; c + k <= cols; c++) add_line(r, c, -1, 1);

    b.symmetry_count = (rows == cols) ? 8 : 4;
    for (int t = 0; t < b.symmetry_count; t++) {
        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                int tr = r;
                int tc = c;
                switch (t) {
                case 0: tr = r;            tc = c;            break;
                case 1: tr = r;            tc = cols - 1 - c; break;
                case 2: tr = rows - 1 - r; tc = c;            break;
                case 3: tr = rows - 1 - r; tc = cols - 1 - c; break;
                case 4: tr = c;            tc = r;            break;
                case 5: tr = cols - 1 - c; tc = rows - 1 - r; break;
                case 6: tr = c;            tc = rows - 1 - r; break;
                default: tr = cols - 1 - c; tc = r;           break;
                }
                b.image[t][r * cols + c] = static_cast<uint8_t>(tr * cols + tc);
            }
        }
    }

    CUDA_CHECK(cudaMemcpyToSymbol(d_lines, b.lines, sizeof b.lines));
    CUDA_CHECK(cudaMemcpyToSymbol(d_image, b.image, sizeof b.image));
    CUDA_CHECK(cudaMemcpyToSymbol(d_line_count, &b.line_count, sizeof(int)));
    CUDA_CHECK(cudaMemcpyToSymbol(d_cell_count, &b.cell_count, sizeof(int)));
    CUDA_CHECK(cudaMemcpyToSymbol(d_k, &b.k, sizeof(int)));
    CUDA_CHECK(cudaMemcpyToSymbol(d_symmetry_count, &b.symmetry_count, sizeof(int)));
    CUDA_CHECK(cudaMemcpyToSymbol(d_all_cells, &b.all_cells, sizeof(Bitboard)));
    return true;
}

/* =========================================================================================
 * Game logic shared by GPU kernel and CPU cascade (one definition, identical results)
 * ========================================================================================= */

__host__ __device__ inline Bitboard apply_symmetry(const Geometry& g, int t, Bitboard b)
{
    Bitboard out = 0;
    while (b) {
        out |= cell_bit(g.image[t][lowest_cell(b)]);
        b &= b - 1;
    }
    return out;
}

__host__ __device__ inline Position canonical(const Geometry& g, Position p)
{
    Position best = p;
    for (int t = 1; t < g.symmetry_count; t++) {
        const Position q{ apply_symmetry(g, t, p.p1), apply_symmetry(g, t, p.p2) };
        if (q < best) {
            best = q;
        }
    }
    return best;
}

/*
 * ES potential of `maker` against `breaker`: phi = sum over live lines of 2^(maker stones),
 * weight[c] = the same sum over live lines through free cell c, and `completions` = free
 * cells that would complete a maker line.
 */
__host__ __device__ inline void potential(const Geometry& g, Bitboard maker, Bitboard breaker,
                                          uint64_t& phi, uint64_t* weight, Bitboard& completions)
{
    const Bitboard occupied = maker | breaker;
    phi = 0;
    completions = 0;
    for (int c = 0; c < g.cell_count; c++) {
        weight[c] = 0;
    }
    for (int i = 0; i < g.line_count; i++) {
        const Bitboard line = g.lines[i];
        if (line & breaker) {
            continue;
        }
        const int stones = popcount64(line & maker);
        const uint64_t w = uint64_t(1) << stones;
        phi += w;
        Bitboard free_cells = line & ~occupied;
        if (stones == g.k - 1) {
            completions |= free_cells;
        }
        while (free_cells) {
            weight[lowest_cell(free_cells)] += w;
            free_cells &= free_cells - 1;
        }
    }
}

/* True when a P1-to-move node is expanded: not full, P1 cannot complete, not an es_inv leaf. */
__host__ __device__ inline bool p1_node_is_internal(const Geometry& g, Position x)
{
    const Bitboard free_cells = g.all_cells & ~(x.p1 | x.p2);
    if (!free_cells) {
        return false;
    }
    uint64_t phi;
    uint64_t weight[kMaxCells];
    Bitboard completions;
    potential(g, x.p1, x.p2, phi, weight, completions);
    if (completions) {
        return false;
    }
    uint64_t max_weight = 0;
    for (Bitboard f = free_cells; f; f &= f - 1) {
        max_weight = weight[lowest_cell(f)] > max_weight ? weight[lowest_cell(f)] : max_weight;
    }
    return phi + max_weight >= (uint64_t(1) << g.k);
}

enum P2NodeKind : int { kP2Internal = 0, kP2Leaf = 1, kP2Lost = 2 };

/*
 * A canonical P2-to-move node.  Leaf: board full, P2 completes a line, or Breaker-first ES.
 * Lost: P1 has two completion cells.  Internal: `reply` receives the canonical P1-to-move
 * position after the greedy reply:
 *   - a single P1 threat is blocked;
 *   - otherwise candidates are tried in order of 2*w_P1 + w_P2 (ties: lowest cell), and the
 *     first one after which no single P1 move creates two threats is taken; if none is safe,
 *     the best-scoring candidate is used.
 * `unsafe_rejections` (may be null) counts candidates rejected by the safety test.
 */
__host__ __device__ inline P2NodeKind p2_node(const Geometry& g, Position w, Position& reply,
                                              unsigned long long* unsafe_rejections)
{
    const Bitboard free_cells = g.all_cells & ~(w.p1 | w.p2);
    if (!free_cells) {
        return kP2Leaf;
    }
    uint64_t phi1, phi2;
    uint64_t w1[kMaxCells], w2[kMaxCells];
    Bitboard c1, c2;
    potential(g, w.p1, w.p2, phi1, w1, c1);
    potential(g, w.p2, w.p1, phi2, w2, c2);
    if (c2) {
        return kP2Leaf;                                 /* P2 completes a line */
    }
    if (phi1 < (uint64_t(1) << g.k)) {
        return kP2Leaf;                                 /* Breaker-first ES */
    }
    if (popcount64(c1) >= 2) {
        return kP2Lost;
    }

    int best = -1;
    if (c1) {
        best = lowest_cell(c1);                         /* forced block */
    } else {
        Bitboard tried = 0;
        int top = -1;
        for (int round = 0; round < g.cell_count && best < 0; round++) {
            int candidate = -1;
            uint64_t candidate_score = 0;
            for (Bitboard f = free_cells & ~tried; f; f &= f - 1) {
                const int d = lowest_cell(f);
                const uint64_t score = w1[d] * 2 + w2[d];
                if (candidate < 0 || score > candidate_score) {
                    candidate_score = score;
                    candidate = d;
                }
            }
            if (candidate < 0) {
                break;
            }
            if (top < 0) {
                top = candidate;
            }
            tried |= cell_bit(candidate);

            /* Safety: after P2 takes `candidate`, may P1 create two threats with one move?
               partner[u] = v records a P1 line with k-2 stones and free cells {u, v}. */
            uint8_t partner[kMaxCells];
            for (int c = 0; c < g.cell_count; c++) {
                partner[c] = 0xFF;
            }
            bool safe = true;
            const Bitboard p2_after = w.p2 | cell_bit(candidate);
            const Bitboard occupied_after = w.p1 | p2_after;
            for (int i = 0; i < g.line_count && safe; i++) {
                const Bitboard line = g.lines[i];
                if ((line & p2_after) || popcount64(line & w.p1) != g.k - 2) {
                    continue;
                }
                Bitboard pair = line & ~occupied_after;
                const int u = lowest_cell(pair);
                pair &= pair - 1;
                const int v = lowest_cell(pair);
                if (partner[u] == 0xFF) {
                    partner[u] = static_cast<uint8_t>(v);
                } else if (partner[u] != v) {
                    safe = false;
                }
                if (partner[v] == 0xFF) {
                    partner[v] = static_cast<uint8_t>(u);
                } else if (partner[v] != u) {
                    safe = false;
                }
            }
            if (safe) {
                best = candidate;
            } else if (unsafe_rejections != nullptr) {
#ifdef __CUDA_ARCH__
                atomicAdd(unsafe_rejections, 1ull);
#else
                ++*unsafe_rejections;
#endif
            }
        }
        if (best < 0) {
            best = top;
        }
    }
    reply = canonical(g, Position{ w.p1, w.p2 | cell_bit(best) });
    return kP2Internal;
}

/* =========================================================================================
 * GPU expansion kernel
 * ========================================================================================= */

__device__ inline bool sorted_contains(const Position* values, uint64_t count, Position x)
{
    uint64_t lo = 0;
    uint64_t hi = count;
    while (lo < hi) {
        const uint64_t mid = (lo + hi) >> 1;
        if (values[mid] < x) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    return lo < count && values[lo] == x;
}

struct PassCounters {
    unsigned long long unsafe_rejections;
    unsigned long long held_leaf_hits;
};

/*
 * One thread per P1-to-move node.  Output layout: slot i*F + j for the j-th free cell of
 * node i (F = free cells per node at this level).  Unused slots hold the marker position.
 */
__global__ void expand_level(const Position* nodes, uint64_t node_count, int free_per_node,
                             Position* replies, Position* lost_p2, Position* p1_wins,
                             uint64_t* bloom, const Position* held, uint64_t held_count,
                             PassCounters* counters)
{
    const uint64_t i = blockIdx.x * uint64_t(blockDim.x) + threadIdx.x;
    if (i >= node_count) {
        return;
    }
    const Geometry g = device_geometry();
    const Position marker = marker_position();
    for (int j = 0; j < free_per_node; j++) {
        replies[i * free_per_node + j] = marker;
        lost_p2[i * free_per_node + j] = marker;
    }
    p1_wins[i] = marker;

    const Position x = nodes[i];
    if (bloom != nullptr) {
        uint64_t h1, h2;
        bloom_hashes(x, h1, h2);
        for (int q = 0; q < kBloomProbes; q++) {
            const uint64_t bit = (h1 + uint64_t(q) * h2) & d_bloom_mask;
            atomicOr(reinterpret_cast<unsigned long long*>(&bloom[bit >> 6]), 1ull << (bit & 63));
        }
    }

    const Bitboard free_cells = g.all_cells & ~(x.p1 | x.p2);
    if (!free_cells) {
        return;
    }
    uint64_t phi;
    uint64_t weight[kMaxCells];
    Bitboard completions;
    potential(g, x.p1, x.p2, phi, weight, completions);
    if (completions) {
        p1_wins[i] = x;                                 /* failure: P1 completes a line */
        return;
    }
    uint64_t max_weight = 0;
    for (Bitboard f = free_cells; f; f &= f - 1) {
        max_weight = weight[lowest_cell(f)] > max_weight ? weight[lowest_cell(f)] : max_weight;
    }
    if (phi + max_weight < (uint64_t(1) << g.k)) {
        return;                                         /* es_inv leaf */
    }

    /* Images of the parent; the child's canonical form is min_t (image_t(x) + image_t(c)). */
    Bitboard image_p1[kMaxSymmetries];
    Bitboard image_p2[kMaxSymmetries];
    for (int t = 0; t < g.symmetry_count; t++) {
        image_p1[t] = apply_symmetry(g, t, x.p1);
        image_p2[t] = apply_symmetry(g, t, x.p2);
    }

    int j = 0;
    for (Bitboard f = free_cells; f; f &= f - 1, j++) {
        const int c = lowest_cell(f);
        Position child{ image_p1[0] | cell_bit(g.image[0][c]), image_p2[0] };
        for (int t = 1; t < g.symmetry_count; t++) {
            const Position q{ image_p1[t] | cell_bit(g.image[t][c]), image_p2[t] };
            if (q < child) {
                child = q;
            }
        }
        if (!(g.all_cells & ~(child.p1 | child.p2))) {
            continue;                                   /* board full */
        }
        if (held_count > 0 && sorted_contains(held, held_count, child)) {
            atomicAdd(&counters->held_leaf_hits, 1ull);
            continue;                                   /* proved held exactly */
        }
        Position reply;
        const P2NodeKind kind = p2_node(g, child, reply, &counters->unsafe_rejections);
        if (kind == kP2Lost) {
            lost_p2[i * free_per_node + j] = child;
        } else if (kind == kP2Internal) {
            replies[i * free_per_node + j] = reply;
        }
    }
}

/* =========================================================================================
 * GPU pass driver (memory bounded: oversized levels are split in host RAM)
 * ========================================================================================= */

struct PassConfig {
    size_t level_capacity;    /* positions per level buffer          */
    size_t sub_batch;         /* nodes expanded per kernel launch    */
};

struct PassResult {
    std::vector<Position> lost_p2;    /* distinct P2 nodes where P1 has a double threat */
    std::vector<Position> p1_wins;    /* distinct P1 nodes where P1 completes a line    */
    uint64_t processed = 0;
    uint64_t splits = 0;
    double seconds = 0;
    PassCounters counters = {};
};

static void sort_unique(std::vector<Position>& v)
{
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
}

/* Remove marker slots from a device array and append the rest to a host vector. */
static void append_non_markers(std::vector<Position>& host, Position* device, size_t count)
{
    const size_t kept = thrust::remove_if(thrust::device, device, device + count, IsMarker()) - device;
    if (kept > 0) {
        const size_t offset = host.size();
        host.resize(offset + kept);
        CUDA_CHECK(cudaMemcpy(host.data() + offset, device, kept * sizeof(Position), cudaMemcpyDeviceToHost));
    }
}

static size_t sort_unique_device(Position* data, size_t count)
{
    thrust::sort(thrust::device, data, data + count);
    return thrust::unique(thrust::device, data, data + count) - data;
}

class GreedyProofPass {
public:
    explicit GreedyProofPass(const PassConfig& config)
        : config_(config),
          level_a_(config.level_capacity),
          level_b_(config.level_capacity),
          replies_(config.sub_batch * host_board.cell_count),
          lost_p2_(config.sub_batch * host_board.cell_count),
          p1_wins_(config.sub_batch),
          counters_(1) {}

    PassResult run(const char* name, uint64_t* bloom, const std::vector<Position>& held)
    {
        DeviceBuffer<Position> held_device(held.size());
        if (!held.empty()) {
            CUDA_CHECK(cudaMemcpy(held_device.get(), held.data(), held.size() * sizeof(Position),
                                  cudaMemcpyHostToDevice));
        }
        CUDA_CHECK(cudaMemset(counters_.get(), 0, sizeof(PassCounters)));

        PassResult result;
        struct Piece {
            std::vector<Position> nodes;
            int ply;
            double weight;   /* fraction of the whole proof this piece represents */
        };
        std::vector<Piece> pending;
        pending.push_back(Piece{ { Position{ 0, 0 } }, 0, 1.0 });

        double done = 0;
        const auto start = std::chrono::steady_clock::now();
        auto last_report = start;

        while (!pending.empty()) {
            Piece piece = std::move(pending.back());
            pending.pop_back();
            size_t count = piece.nodes.size();
            int ply = piece.ply;
            CUDA_CHECK(cudaMemcpy(level_a_.get(), piece.nodes.data(), count * sizeof(Position),
                                  cudaMemcpyHostToDevice));
            piece.nodes.clear();
            piece.nodes.shrink_to_fit();

            Position* current = level_a_.get();
            Position* next = level_b_.get();
            bool split = false;

            while (count > 0) {
                const int free_per_node = host_board.cell_count - ply;
                size_t used = 0;
                bool overflow = false;
                std::vector<Position> level_lost;
                std::vector<Position> level_wins;

                for (size_t offset = 0; offset < count && !overflow; offset += config_.sub_batch) {
                    const size_t batch = std::min(config_.sub_batch, count - offset);
                    const unsigned blocks = static_cast<unsigned>((batch + kThreadsPerBlock - 1) / kThreadsPerBlock);
                    expand_level<<<blocks, kThreadsPerBlock>>>(
                        current + offset, batch, free_per_node, replies_.get(), lost_p2_.get(), p1_wins_.get(),
                        bloom, held_device.get(), held.size(), counters_.get());
                    CUDA_CHECK(cudaGetLastError());

                    const size_t slots = batch * free_per_node;
                    const size_t produced =
                        thrust::remove_if(thrust::device, replies_.get(), replies_.get() + slots, IsMarker()) -
                        replies_.get();
                    append_non_markers(level_lost, lost_p2_.get(), slots);
                    append_non_markers(level_wins, p1_wins_.get(), batch);

                    if (used + produced > config_.level_capacity) {
                        used = sort_unique_device(next, used);
                        if (used + produced > config_.level_capacity) {
                            overflow = true;
                            break;
                        }
                    }
                    CUDA_CHECK(cudaMemcpy(next + used, replies_.get(), produced * sizeof(Position),
                                          cudaMemcpyDeviceToDevice));
                    used += produced;
                }

                if (overflow) {
                    if (count == 1) {
                        std::fprintf(stderr, "level capacity too small for the children of one node\n");
                        std::exit(1);
                    }
                    /* Split this level into two halves and solve them later. */
                    result.splits++;
                    const size_t half = count / 2;
                    Piece first{ std::vector<Position>(half), ply, piece.weight / 2 };
                    Piece second{ std::vector<Position>(count - half), ply, piece.weight / 2 };
                    CUDA_CHECK(cudaMemcpy(first.nodes.data(), current, half * sizeof(Position),
                                          cudaMemcpyDeviceToHost));
                    CUDA_CHECK(cudaMemcpy(second.nodes.data(), current + half, (count - half) * sizeof(Position),
                                          cudaMemcpyDeviceToHost));
                    pending.push_back(std::move(second));
                    pending.push_back(std::move(first));
                    split = true;
                    break;
                }

                /* The level is complete: only now do its failures count. */
                result.lost_p2.insert(result.lost_p2.end(), level_lost.begin(), level_lost.end());
                result.p1_wins.insert(result.p1_wins.end(), level_wins.begin(), level_wins.end());
                result.processed += count;
                count = sort_unique_device(next, used);
                std::swap(current, next);
                ply += 2;

                const auto now = std::chrono::steady_clock::now();
                if (std::chrono::duration<double>(now - last_report).count() > 60) {
                    last_report = now;
                    std::printf("    [%5.0fs] done %.4f  processed %llu  ply %d  failures (raw) %zu\n",
                                std::chrono::duration<double>(now - start).count(), done,
                                static_cast<unsigned long long>(result.processed), ply,
                                result.lost_p2.size() + result.p1_wins.size());
                    std::fflush(stdout);
                }
            }
            if (!split) {
                done += piece.weight;
            }
        }

        sort_unique(result.lost_p2);
        sort_unique(result.p1_wins);
        CUDA_CHECK(cudaMemcpy(&result.counters, counters_.get(), sizeof(PassCounters), cudaMemcpyDeviceToHost));
        result.seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
        std::printf("  %s: processed %llu P1 nodes, splits %llu, %.1f s; failures: %zu lost P2 nodes + %zu P1 wins;"
                    " held-leaf hits %llu\n",
                    name, static_cast<unsigned long long>(result.processed),
                    static_cast<unsigned long long>(result.splits), result.seconds, result.lost_p2.size(),
                    result.p1_wins.size(), result.counters.held_leaf_hits);
        std::fflush(stdout);
        return result;
    }

private:
    PassConfig config_;
    DeviceBuffer<Position> level_a_;
    DeviceBuffer<Position> level_b_;
    DeviceBuffer<Position> replies_;
    DeviceBuffer<Position> lost_p2_;
    DeviceBuffer<Position> p1_wins_;
    DeviceBuffer<PassCounters> counters_;
};

/* =========================================================================================
 * Host Bloom filter (a copy of the device filter after pass 1)
 * ========================================================================================= */

class HostBloom {
public:
    HostBloom() = default;
    HostBloom(std::vector<uint64_t> words, uint64_t mask) : words_(std::move(words)), mask_(mask) {}

    bool contains(const Position& p) const
    {
        uint64_t h1, h2;
        bloom_hashes(p, h1, h2);
        for (int q = 0; q < kBloomProbes; q++) {
            const uint64_t bit = (h1 + uint64_t(q) * h2) & mask_;
            if (!((words_[bit >> 6] >> (bit & 63)) & 1)) {
                return false;
            }
        }
        return true;
    }

    double fill_ratio() const
    {
        uint64_t ones = 0;
        for (uint64_t w : words_) {
            ones += static_cast<uint64_t>(popcount64(w));
        }
        return static_cast<double>(ones) / static_cast<double>(mask_ + 1);
    }

private:
    std::vector<uint64_t> words_;
    uint64_t mask_ = 0;
};

/* =========================================================================================
 * Exact solver (CPU): strong-game null-window negamax with ES bounds, threats, ordering and
 * dead cells.  One instance per OpenMP thread, each owning its transposition table.
 * ========================================================================================= */

class ExactSolver {
public:
    explicit ExactSolver(int table_log2) : entry_count_(size_t(1) << table_log2) {}

    /* Decide a P2-to-move position: 0 = P2 holds (P1 cannot win), 1 = P1 wins, 2 = undecided. */
    int decide_p2_to_move(const Position& w, uint64_t node_limit)
    {
        if (!table_) {
            allocate_table();
        }
        nodes_ = 0;
        limit_ = node_limit;
        aborted_ = false;
        const int value = negamax(w.p2, w.p1, -1, 0);
        if (aborted_) {
            return 2;
        }
        return value >= 0 ? 0 : 1;
    }

    uint64_t nodes() const { return nodes_; }

private:
    enum Bound : uint8_t { kEmpty = 0, kExact = 1, kLower = 2, kUpper = 3 };

    /* Plain data: an all-zero entry is empty, so calloc'd memory is a valid empty table. */
    struct Entry {
        Bitboard me;
        Bitboard opponent;
        int8_t value;
        uint8_t bound;
    };

    struct FreeDeleter {
        void operator()(Entry* p) const { std::free(p); }
    };

    /* calloc lets the OS supply zero pages lazily: a thread that never runs an exact search
       never touches its table, and no up-front fill of entry_count_ entries is needed. */
    void allocate_table()
    {
        table_.reset(static_cast<Entry*>(std::calloc(entry_count_, sizeof(Entry))));
        if (!table_) {
            std::fprintf(stderr, "cannot allocate the exact-solver table (%zu MB)\n",
                         entry_count_ * sizeof(Entry) >> 20);
            std::exit(1);
        }
    }

    Entry& slot(Bitboard me, Bitboard opponent)
    {
        const uint64_t h = (me * 0x517cc1b727220a95ull) ^ (opponent * 0x6e2e0be880784dd1ull);
        return table_.get()[static_cast<size_t>(h ^ (h >> 32)) & (entry_count_ - 1)];
    }

    static uint64_t max_free_weight(const uint64_t* weight, Bitboard free_cells)
    {
        uint64_t best = 0;
        for (; free_cells; free_cells &= free_cells - 1) {
            best = std::max(best, weight[lowest_cell(free_cells)]);
        }
        return best;
    }

    /* Value for the side to move (`me`): 1 win, 0 draw, -1 loss, within (alpha, beta). */
    int negamax(Bitboard me, Bitboard opponent, int alpha, int beta)
    {
        if (++nodes_ > limit_) {
            aborted_ = true;
            return 0;
        }
        const Geometry g = host_board.geometry();
        const Bitboard occupied = me | opponent;
        const Bitboard free_cells = g.all_cells & ~occupied;
        if (!free_cells) {
            return 0;
        }

        Entry& cached = slot(me, opponent);
        if (cached.bound != kEmpty && cached.me == me && cached.opponent == opponent) {
            if (cached.bound == kExact) return cached.value;
            if (cached.bound == kLower && cached.value >= beta) return cached.value;
            if (cached.bound == kUpper && cached.value <= alpha) return cached.value;
        }

        const int alpha0 = alpha;
        const int beta0 = beta;
        const uint64_t limit = uint64_t(1) << g.k;
        int lower = -1;
        int upper = 1;
        int best = -2;
        uint64_t weight_me[kMaxCells], weight_opp[kMaxCells];
        uint64_t phi_me, phi_opp;
        Bitboard wins_me, threats_opp;
        Bitboard moves = free_cells;
        int order[kMaxCells];
        int move_count = 0;

        potential(g, me, opponent, phi_me, weight_me, wins_me);
        potential(g, opponent, me, phi_opp, weight_opp, threats_opp);
        if (wins_me) {
            best = 1;
            goto store;
        }
        if (phi_opp < limit) {
            lower = 0;                                   /* the opponent cannot win */
        }
        if (phi_me + max_free_weight(weight_me, free_cells) < limit) {
            upper = 0;                                   /* we cannot win */
        }
        if (lower < 0) {
            /* Refined: after our greedy block of the opponent, does es_inv hold for them? */
            int block = -1;
            uint64_t block_weight = 0;
            for (Bitboard f = free_cells; f; f &= f - 1) {
                const int c = lowest_cell(f);
                if (block < 0 || weight_opp[c] > block_weight) {
                    block_weight = weight_opp[c];
                    block = c;
                }
            }
            uint64_t phi_after;
            uint64_t weight_after[kMaxCells];
            Bitboard ignored;
            potential(g, opponent, me | cell_bit(block), phi_after, weight_after, ignored);
            if (phi_after + max_free_weight(weight_after, free_cells & ~cell_bit(block)) < limit) {
                lower = 0;
            }
        }
        if (lower == upper) { best = 0; goto store; }
        if (lower >= beta) { best = lower; goto store; }
        if (upper <= alpha) { best = upper; goto store; }
        alpha = std::max(alpha, lower);
        beta = std::min(beta, upper);

        if (popcount64(threats_opp) >= 2) {
            best = -1;
            goto clamp;
        }
        if (threats_opp) {
            moves = threats_opp;
        } else {
            Bitboard live = 0;
            for (Bitboard f = moves; f; f &= f - 1) {
                const int c = lowest_cell(f);
                if (weight_me[c] | weight_opp[c]) {
                    live |= cell_bit(c);
                }
            }
            if (!live) {
                best = 0;
                goto clamp;
            }
            moves = live;
        }

        for (Bitboard f = moves; f; f &= f - 1) {
            order[move_count++] = lowest_cell(f);
        }
        for (int i = 1; i < move_count; i++) {
            const int c = order[i];
            const uint64_t score = weight_me[c] + weight_opp[c];
            int j = i - 1;
            while (j >= 0 && weight_me[order[j]] + weight_opp[order[j]] < score) {
                order[j + 1] = order[j];
                j--;
            }
            order[j + 1] = c;
        }
        for (int i = 0; i < move_count; i++) {
            const int score = -negamax(opponent, me | cell_bit(order[i]), -beta, -alpha);
            if (aborted_) {
                return 0;
            }
            best = std::max(best, score);
            alpha = std::max(alpha, score);
            if (alpha >= beta || best == 1) {
                break;
            }
        }

    clamp:
        best = std::max(best, lower);
        best = std::min(best, upper);

    store:
        if (aborted_) {
            return 0;
        }
        {
            Entry& e = slot(me, opponent);
            e.me = me;
            e.opponent = opponent;
            e.value = static_cast<int8_t>(best);
            e.bound = best <= alpha0 ? kUpper : (best >= beta0 ? kLower : kExact);
        }
        return best;
    }

    std::unique_ptr<Entry, FreeDeleter> table_;
    size_t entry_count_;
    uint64_t nodes_ = 0;
    uint64_t limit_ = 0;
    bool aborted_ = false;
};

/* =========================================================================================
 * CPU cascade
 * ========================================================================================= */

struct ProofSets {
    PositionSet held;        /* P2 nodes proved held exactly: proof leaves      */
    PositionSet lost;        /* P2 nodes proved lost (or double-threat nodes)   */
    PositionSet undecided;   /* P2 nodes the exact solver could not decide      */
    PositionSet bad_p1;      /* P1 nodes known to be P1 wins                    */
};

class Cascade {
public:
    Cascade(const HostBloom& bloom, uint64_t node_limit, int threads)
        : bloom_(bloom), node_limit_(node_limit)
    {
        solvers_.reserve(static_cast<size_t>(threads));
        for (int t = 0; t < threads; t++) {
            solvers_.emplace_back(22);
        }
    }

    /* Returns false if the climb reaches the root (the method cannot complete the proof). */
    bool run(const std::vector<Position>& lost_p2, const std::vector<Position>& p1_wins, ProofSets& sets)
    {
        const Geometry g = host_board.geometry();
        const auto start = std::chrono::steady_clock::now();
        std::vector<Position> frontier = lost_p2;
        for (const Position& y : lost_p2) {
            sets.lost.insert(y);
        }
        std::vector<Position> new_bad;
        for (const Position& x : p1_wins) {
            if (sets.bad_p1.insert(x).second) {
                new_bad.push_back(x);
            }
        }

        for (int level = 0; !frontier.empty() || !new_bad.empty(); level++) {
            /* 1. Bad P1 parents of the lost P2 frontier. */
            for (const Position& x : parents_of(g, frontier)) {
                if (sets.bad_p1.insert(x).second) {
                    new_bad.push_back(x);
                }
            }
            for (const Position& x : new_bad) {
                if (x.p1 == 0 && x.p2 == 0) {
                    std::printf("  cascade reached the ROOT: this method cannot complete the proof\n");
                    return false;
                }
            }

            /* 2. P2 nodes whose greedy reply leads to a bad P1 node. */
            std::vector<Position> candidates = greedy_predecessors(g, new_bad);
            const size_t new_bad_count = new_bad.size();
            new_bad.clear();
            std::vector<Position> todo;
            for (const Position& w : candidates) {
                if (!sets.held.count(w) && !sets.lost.count(w) && !sets.undecided.count(w)) {
                    todo.push_back(w);
                }
            }

            /* 3. Decide each one exactly. */
            std::vector<int> verdict(todo.size());
            std::vector<uint64_t> effort(todo.size());
            #pragma omp parallel for schedule(dynamic, 1)
            for (long long i = 0; i < static_cast<long long>(todo.size()); i++) {
                ExactSolver& solver = solvers_[static_cast<size_t>(omp_get_thread_num())];
                verdict[static_cast<size_t>(i)] = solver.decide_p2_to_move(todo[static_cast<size_t>(i)], node_limit_);
                effort[static_cast<size_t>(i)] = solver.nodes();
            }

            frontier.clear();
            size_t held = 0, lost = 0, undecided = 0;
            uint64_t total_effort = 0, max_effort = 0;
            int min_stones = 99, max_stones = 0;
            for (size_t i = 0; i < todo.size(); i++) {
                total_effort += effort[i];
                max_effort = std::max(max_effort, effort[i]);
                const int stones = popcount64(todo[i].p1 | todo[i].p2);
                min_stones = std::min(min_stones, stones);
                max_stones = std::max(max_stones, stones);
                if (verdict[i] == 0) {
                    sets.held.insert(todo[i]);
                    held++;
                } else {
                    (verdict[i] == 1 ? sets.lost : sets.undecided).insert(todo[i]);
                    (verdict[i] == 1 ? lost : undecided)++;
                    frontier.push_back(todo[i]);
                }
            }
            std::printf("  cascade level %d: %zu new bad P1 nodes -> %zu P2 candidates (%zu new, stones %d..%d):"
                        " held %zu, lost %zu, undecided %zu; exact nodes %llu (max %llu)  [%.1f s]\n",
                        level, new_bad_count, candidates.size(), todo.size(), todo.empty() ? 0 : min_stones,
                        max_stones, held,
                        lost, undecided, static_cast<unsigned long long>(total_effort),
                        static_cast<unsigned long long>(max_effort),
                        std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count());
            std::fflush(stdout);
        }
        return true;
    }

private:
    /* P1-to-move parents canon(Y - p) that were visited (Bloom) and are internal. */
    std::vector<Position> parents_of(const Geometry& g, const std::vector<Position>& p2_nodes) const
    {
        std::vector<std::vector<Position>> per_thread(static_cast<size_t>(omp_get_max_threads()));
        #pragma omp parallel for schedule(dynamic, 64)
        for (long long i = 0; i < static_cast<long long>(p2_nodes.size()); i++) {
            const Position& y = p2_nodes[static_cast<size_t>(i)];
            auto& out = per_thread[static_cast<size_t>(omp_get_thread_num())];
            for (Bitboard s = y.p1; s; s &= s - 1) {
                const Position x = canonical(g, Position{ y.p1 & ~(s & (~s + 1)), y.p2 });
                if (bloom_.contains(x) && p1_node_is_internal(g, x)) {
                    out.push_back(x);
                }
            }
        }
        std::vector<Position> merged;
        for (auto& v : per_thread) {
            merged.insert(merged.end(), v.begin(), v.end());
        }
        sort_unique(merged);
        return merged;
    }

    /* Internal P2 nodes W = canon(X - s) with greedy(W) = X and a visited internal parent. */
    std::vector<Position> greedy_predecessors(const Geometry& g, const std::vector<Position>& bad_p1) const
    {
        std::vector<std::vector<Position>> per_thread(static_cast<size_t>(omp_get_max_threads()));
        #pragma omp parallel for schedule(dynamic, 64)
        for (long long i = 0; i < static_cast<long long>(bad_p1.size()); i++) {
            const Position& x = bad_p1[static_cast<size_t>(i)];
            auto& out = per_thread[static_cast<size_t>(omp_get_thread_num())];
            for (Bitboard s = x.p2; s; s &= s - 1) {
                const Position w = canonical(g, Position{ x.p1, x.p2 & ~(s & (~s + 1)) });
                Position reply;
                if (p2_node(g, w, reply, nullptr) != kP2Internal || !(reply == x)) {
                    continue;
                }
                bool reachable = false;
                for (Bitboard p = w.p1; p && !reachable; p &= p - 1) {
                    const Position parent = canonical(g, Position{ w.p1 & ~(p & (~p + 1)), w.p2 });
                    reachable = bloom_.contains(parent) && p1_node_is_internal(g, parent);
                }
                if (reachable) {
                    out.push_back(w);
                }
            }
        }
        std::vector<Position> merged;
        for (auto& v : per_thread) {
            merged.insert(merged.end(), v.begin(), v.end());
        }
        sort_unique(merged);
        return merged;
    }

    const HostBloom& bloom_;
    uint64_t node_limit_;
    std::vector<ExactSolver> solvers_;
};

/* =========================================================================================
 * Main
 * ========================================================================================= */

int main(int argc, char** argv)
{
    if (argc < 4) {
        std::fprintf(stderr, "usage: %s m n k [bloom_log2=34] [level_capacity=80000000] [sub_batch=500000]"
                             " [exact_node_limit=50000000]\n", argv[0]);
        return 2;
    }
    if (!init_board(std::atoi(argv[1]), std::atoi(argv[2]), std::atoi(argv[3]))) {
        return 1;
    }
    const int bloom_log2 = argc > 4 ? std::atoi(argv[4]) : 34;
    PassConfig config;
    config.level_capacity = argc > 5 ? std::strtoull(argv[5], nullptr, 10) : 80000000ull;
    config.sub_batch = argc > 6 ? std::strtoull(argv[6], nullptr, 10) : 500000ull;
    const uint64_t node_limit = argc > 7 ? std::strtoull(argv[7], nullptr, 10) : 50000000ull;
    if (bloom_log2 < 10 || bloom_log2 > 36 || config.level_capacity == 0 || config.sub_batch == 0) {
        std::fprintf(stderr, "invalid parameters\n");
        return 2;
    }

    const uint64_t bloom_mask = (uint64_t(1) << bloom_log2) - 1;
    CUDA_CHECK(cudaMemcpyToSymbol(d_bloom_mask, &bloom_mask, sizeof bloom_mask));
    const int threads = omp_get_max_threads();
    std::printf("(%d,%d,%d) %d lines, %d symmetries  [bloom 2^%d bits, level capacity %zu, sub-batch %zu,"
                " exact node limit %llu, %d CPU threads]\n",
                host_board.rows, host_board.cols, host_board.k, host_board.line_count, host_board.symmetry_count,
                bloom_log2, config.level_capacity, config.sub_batch,
                static_cast<unsigned long long>(node_limit), threads);
    std::fflush(stdout);

    const auto start = std::chrono::steady_clock::now();
    GreedyProofPass pass(config);

    /* Pass 1 with the Bloom filter, which is then moved to host RAM. */
    HostBloom bloom;
    PassResult result;
    {
        const size_t words = static_cast<size_t>((bloom_mask + 1) / 64);
        DeviceBuffer<uint64_t> device_bloom(words);
        CUDA_CHECK(cudaMemset(device_bloom.get(), 0, words * sizeof(uint64_t)));
        result = pass.run("pass 1 (greedy proof + Bloom)", device_bloom.get(), {});
        std::vector<uint64_t> host_words(words);
        CUDA_CHECK(cudaMemcpy(host_words.data(), device_bloom.get(), words * sizeof(uint64_t),
                              cudaMemcpyDeviceToHost));
        bloom = HostBloom(std::move(host_words), bloom_mask);
    }   /* device Bloom freed here */
    const double fill = bloom.fill_ratio();
    std::printf("  Bloom fill %.4f -> false-positive rate about %.5f\n", fill, std::pow(fill, kBloomProbes));

    ProofSets sets;
    Cascade cascade(bloom, node_limit, threads);
    bool ok = true;
    for (int round = 1; !result.lost_p2.empty() || !result.p1_wins.empty(); round++) {
        if (round > 4) {
            std::printf("  giving up after 4 repair rounds\n");
            ok = false;
            break;
        }
        if (!cascade.run(result.lost_p2, result.p1_wins, sets)) {
            ok = false;
            break;
        }
        std::vector<Position> held(sets.held.begin(), sets.held.end());
        sort_unique(held);
        std::printf("  %zu P2 nodes held exactly, %zu lost, %zu undecided\n", held.size(), sets.lost.size(),
                    sets.undecided.size());
        result = pass.run("verification pass (greedy proof with held leaves)", nullptr, held);
    }

    const bool proved = ok && result.lost_p2.empty() && result.p1_wins.empty();
    std::printf("  => %s  total %.1f s\n",
                proved ? "DRAW PROVED: P1 cannot win (and P2 cannot win by strategy stealing)" : "proof NOT completed",
                std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count());
    return proved ? 0 : 3;
}
