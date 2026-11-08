import os
import sys
import time
import ctypes
import numpy as np

# Load CUDA Driver API and NVRTC DLLs
cuda_dirs = [
    r"C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.5\bin\x64",
    r"C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.5\bin",
    r"C:\Users\baian\AppData\Local\Programs\Python\Python312\Lib\site-packages\nvidia\cuda_nvrtc\bin",
    r"C:\Users\baian\AppData\Local\Programs\Python\Python312\Lib\site-packages\nvidia\cuda_runtime\bin"
]
for d in cuda_dirs:
    if os.path.exists(d):
        os.add_dll_directory(d)
        os.environ["PATH"] = d + os.pathsep + os.environ.get("PATH", "")

hCuda = ctypes.WinDLL("nvcuda.dll")
nvrtc_candidates = [
    r"C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.5\bin\x64\nvrtc64_130_0.dll",
    r"C:\Users\baian\AppData\Local\Programs\Python\Python312\Lib\site-packages\nvidia\cuda_nvrtc\bin\nvrtc64_120_0.dll",
    "nvrtc64_130_0.dll",
    "nvrtc64_120_0.dll"
]
hNvrtc = None
for cand in nvrtc_candidates:
    if os.path.exists(cand) or not os.path.isabs(cand):
        try:
            hNvrtc = ctypes.WinDLL(cand)
            break
        except OSError:
            continue
assert hNvrtc is not None, "Could not load NVRTC DLL"

assert hCuda.cuInit(0) == 0
dev = ctypes.c_int()
assert hCuda.cuDeviceGet(ctypes.byref(dev), 0) == 0
ctx = ctypes.c_void_p()
assert hCuda.cuCtxCreate(ctypes.byref(ctx), 0, dev) == 0

CUDA_SRC = b"""
#define W 8
#define H 8
#define K 5
#define NL 96
#define FULL_MASK 0xFFFFFFFFFFFFFFFFULL
#define BOTTOM_MASK 0x0101010101010101ULL
#define BIT(c, r) (1ULL << ((c) * 8 + (r)))
#define COLMASK(c) (0xFFULL << ((c) * 8))

typedef unsigned long long u64;
typedef signed char i8;

__device__ inline bool has_won_5(u64 s) {
    u64 m;
    // Vertical (shift 1, starting row r0 in 0..3)
    m = s & (s >> 1);
    if ((m & (m >> 2) & (s >> 4)) & 0x0F0F0F0F0F0F0F0FULL) return true;
    // Horizontal (shift 8)
    m = s & (s >> 8);
    if ((m & (m >> 16) & (s >> 32)) & FULL_MASK) return true;
    // Diagonal / (shift 9, starting row r0 in 0..3)
    m = s & (s >> 9);
    if ((m & (m >> 18) & (s >> 36)) & 0x0F0F0F0F0F0F0F0FULL) return true;
    // Diagonal \\ (shift 7, starting col c0 in 0..3 and row r0 in 4..7)
    m = s & (s >> 7);
    if ((m & (m >> 14) & (s >> 28)) & 0x00000000F0F0F0F0ULL) return true;
    return false;
}

__device__ inline u64 splitmix64(u64 *state) {
    u64 z = (*state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

__device__ inline u64 splitmix64_init(u64 seed) {
    return splitmix64(&seed);
}

// Kernel 1: Exhaustively verify 96 winning lines, 480 4-stone near-misses, and n_random bitboards
extern "C" __global__ void verify_detector_kernel(
    const u64 *d_lines,
    int n_random,
    int *d_errors
) {
    int idx = blockDim.x * blockIdx.x + threadIdx.x;
    if (idx < NL) {
        u64 mask = d_lines[idx];
        if (!has_won_5(mask)) atomicAdd(d_errors, 1);
        for (int bit = 0; bit < 64; bit++) {
            u64 b = 1ULL << bit;
            if ((mask & b) && has_won_5(mask ^ b)) {
                atomicAdd(d_errors, 1);
            }
        }
    }
    if (idx < n_random) {
        u64 rng = (u64)idx + 1ULL;
        u64 s = splitmix64(&rng) & FULL_MASK;
        bool shift_res = has_won_5(s);
        bool enum_res = false;
        for (int l = 0; l < NL; l++) {
            if ((s & d_lines[l]) == d_lines[l]) {
                enum_res = true;
                break;
            }
        }
        if (shift_res != enum_res) atomicAdd(d_errors, 1);
    }
}

// Kernel 2: Generate N distinct legal non-terminal Connect-5 positions with true alternating mover parity
extern "C" __global__ void generate_boards_kernel(
    u64 *d_white,
    u64 *d_black,
    i8 *d_mover,
    int n
) {
    int idx = blockDim.x * blockIdx.x + threadIdx.x;
    if (idx >= n) return;

    u64 rng = splitmix64_init((u64)idx + 1ULL);
    u64 w = 0, b = 0;
    int heights[8] = {0};
    int target_moves = 10 + (int)(splitmix64(&rng) % 31); // 10..40 plies
    int actual_moves = 0;

    for (int m = 0; m < target_moves; m++) {
        int start_c = (int)(splitmix64(&rng) & 7ULL);
        int chosen_c = -1;
        for (int off = 0; off < 8; off++) {
            int c = (start_c + off) & 7;
            if (heights[c] < 8) {
                u64 bit = 1ULL << (c * 8 + heights[c]);
                u64 next_s = ((actual_moves & 1) == 0) ? (w | bit) : (b | bit);
                if (!has_won_5(next_s)) {
                    chosen_c = c;
                    break;
                }
            }
        }
        if (chosen_c < 0) break;
        u64 bit = 1ULL << (chosen_c * 8 + heights[chosen_c]++);
        if ((actual_moves & 1) == 0) w |= bit;
        else b |= bit;
        actual_moves++;
    }
    d_white[idx] = w;
    d_black[idx] = b;
    d_mover[idx] = (i8)(actual_moves & 1);
}

struct EvalResult {
    i8 score;       // 1 = Win in 1, -1 = Loss (opponent has >=2 winning threats), 0 = Non-terminal tactical score
    i8 best_col;    // Best recommended move
    i8 num_moves;   // Number of valid moves
    i8 pad;
    i8 col_scores[8];
};

// Kernel 3: Parallel 1-Ply/2-Ply Bitboard Tactical Playout Evaluator (true per-board mover)
extern "C" __global__ void eval_boards(
    const u64 *white_boards,
    const u64 *black_boards,
    const i8 *movers,
    EvalResult *d_results,
    int n
) {
    int idx = blockDim.x * blockIdx.x + threadIdx.x;
    if (idx >= n) return;

    u64 w = white_boards[idx];
    u64 b = black_boards[idx];
    int mover = (int)movers[idx];
    u64 mask = w | b;

    u64 my_stones = (mover == 0) ? w : b;
    u64 opp_stones = (mover == 0) ? b : w;

    EvalResult res;
    res.score = 0;
    res.best_col = -1;
    res.num_moves = 0;
    res.pad = (i8)mover;
    for (int c = 0; c < 8; c++) res.col_scores[c] = -128;

    if (has_won_5(opp_stones)) { res.score = -1; d_results[idx] = res; return; }
    if (has_won_5(my_stones))  { res.score = 1;  d_results[idx] = res; return; }

    int my_win_col = -1;
    int opp_win_count = 0;
    int opp_must_block_col = -1;

    u64 landings[8];
    for (int c = 0; c < 8; c++) {
        u64 col_bit = 1ULL << (c * 8);
        u64 col_mask = 0xFFULL << (c * 8);
        u64 land = (((mask & 0x7F7F7F7F7F7F7F7FULL) + col_bit) & col_mask) & ~mask;
        landings[c] = land;
        if (land) {
            res.num_moves++;
            if (has_won_5(my_stones | land)) my_win_col = c;
            if (has_won_5(opp_stones | land)) {
                opp_win_count++;
                opp_must_block_col = c;
            }
        }
    }

    if (my_win_col >= 0) {
        res.score = 1;
        res.best_col = my_win_col;
        res.col_scores[my_win_col] = 100;
        d_results[idx] = res;
        return;
    }
    if (opp_win_count >= 2) {
        res.score = -1;
        d_results[idx] = res;
        return;
    }

    int best_score = -999;
    int best_c = -1;
    for (int c = 0; c < 8; c++) {
        u64 land = landings[c];
        if (!land) continue;
        if (opp_win_count == 1 && c != opp_must_block_col) {
            res.col_scores[c] = -100;
            continue;
        }
        u64 next_land = (land << 1) & COLMASK(c);
        if (next_land && has_won_5(opp_stones | next_land)) {
            res.col_scores[c] = -50;
            continue;
        }
        int score = (c == 3 || c == 4) ? 6 : (c == 2 || c == 5) ? 4 : (c == 1 || c == 6) ? 2 : 0;
        res.col_scores[c] = (i8)score;
        if (score > best_score) {
            best_score = score;
            best_c = c;
        }
    }
    res.best_col = best_c;
    d_results[idx] = res;
}
"""

prog = ctypes.c_void_p()
hNvrtc.nvrtcCreateProgram(ctypes.byref(prog), CUDA_SRC, b"c5_eval.cu", 0, None, None)
opts = (ctypes.c_char_p * 1)(b"--gpu-architecture=sm_89")
res = hNvrtc.nvrtcCompileProgram(prog, 1, opts)
if res != 0:
    log_sz = ctypes.c_size_t()
    hNvrtc.nvrtcGetProgramLogSize(prog, ctypes.byref(log_sz))
    log = ctypes.create_string_buffer(log_sz.value)
    hNvrtc.nvrtcGetProgramLog(prog, log)
    print("Compilation Log:\n", log.value.decode())
    sys.exit(1)

cubin_sz = ctypes.c_size_t()
hNvrtc.nvrtcGetCUBINSize(prog, ctypes.byref(cubin_sz))
cubin = ctypes.create_string_buffer(cubin_sz.value)
hNvrtc.nvrtcGetCUBIN(prog, cubin)

mod = ctypes.c_void_p()
assert hCuda.cuModuleLoadData(ctypes.byref(mod), cubin) == 0

k_verify = ctypes.c_void_p()
k_gen = ctypes.c_void_p()
k_eval = ctypes.c_void_p()
assert hCuda.cuModuleGetFunction(ctypes.byref(k_verify), mod, b"verify_detector_kernel") == 0
assert hCuda.cuModuleGetFunction(ctypes.byref(k_gen), mod, b"generate_boards_kernel") == 0
assert hCuda.cuModuleGetFunction(ctypes.byref(k_eval), mod, b"eval_boards") == 0

hCuda.cuMemcpyHtoD.argtypes = [ctypes.c_uint64, ctypes.c_void_p, ctypes.c_size_t]
hCuda.cuMemcpyDtoH.argtypes = [ctypes.c_void_p, ctypes.c_uint64, ctypes.c_size_t]

# 1. Build 96 winning line masks and run GPU Win-Detector Verification
h_lines = np.zeros(96, dtype=np.uint64)
idx = 0
for r in range(8):
    for c in range(4):
        m = 0
        for i in range(5): m |= (1 << ((c + i) * 8 + r))
        h_lines[idx] = m; idx += 1
for c in range(8):
    for r in range(4):
        m = 0
        for i in range(5): m |= (1 << (c * 8 + (r + i)))
        h_lines[idx] = m; idx += 1
for c in range(4):
    for r in range(4):
        m = 0
        for i in range(5): m |= (1 << ((c + i) * 8 + (r + i)))
        h_lines[idx] = m; idx += 1
for c in range(4):
    for r in range(4, 8):
        m = 0
        for i in range(5): m |= (1 << ((c + i) * 8 + (r - i)))
        h_lines[idx] = m; idx += 1
assert idx == 96

d_lines = ctypes.c_uint64()
d_errors = ctypes.c_uint64()
h_errors = np.zeros(1, dtype=np.int32)
assert hCuda.cuMemAlloc(ctypes.byref(d_lines), 96 * 8) == 0
assert hCuda.cuMemAlloc(ctypes.byref(d_errors), 4) == 0
assert hCuda.cuMemcpyHtoD(d_lines, h_lines.ctypes.data, 96 * 8) == 0
assert hCuda.cuMemcpyHtoD(d_errors, h_errors.ctypes.data, 4) == 0

c_n_rand = ctypes.c_int(100000)
v_params = (ctypes.c_void_p * 3)(
    ctypes.cast(ctypes.byref(d_lines), ctypes.c_void_p),
    ctypes.cast(ctypes.byref(c_n_rand), ctypes.c_void_p),
    ctypes.cast(ctypes.byref(d_errors), ctypes.c_void_p)
)
assert hCuda.cuLaunchKernel(k_verify, (100000 + 255) // 256, 1, 1, 256, 1, 1, 0, None, v_params, None) == 0
hCuda.cuCtxSynchronize()
assert hCuda.cuMemcpyDtoH(h_errors.ctypes.data, d_errors, 4) == 0
print(f"[1/3] GPU Win-Detector Verification (96 lines, 480 near-misses, 100,000 random bitboards): errors = {h_errors[0]}", flush=True)
assert h_errors[0] == 0

# 2. Generate 4,194,304 boards with SplitMix64 and verify distinctness & true mover parity on first 262,144
N_BENCH = 4_194_304
N_CHECK = 262_144
d_white = ctypes.c_uint64()
d_black = ctypes.c_uint64()
d_mover = ctypes.c_uint64()
d_res = ctypes.c_uint64()

assert hCuda.cuMemAlloc(ctypes.byref(d_white), N_BENCH * 8) == 0
assert hCuda.cuMemAlloc(ctypes.byref(d_black), N_BENCH * 8) == 0
assert hCuda.cuMemAlloc(ctypes.byref(d_mover), N_BENCH) == 0
assert hCuda.cuMemAlloc(ctypes.byref(d_res), N_BENCH * 12) == 0

c_n_bench = ctypes.c_int(N_BENCH)
g_params = (ctypes.c_void_p * 4)(
    ctypes.cast(ctypes.byref(d_white), ctypes.c_void_p),
    ctypes.cast(ctypes.byref(d_black), ctypes.c_void_p),
    ctypes.cast(ctypes.byref(d_mover), ctypes.c_void_p),
    ctypes.cast(ctypes.byref(c_n_bench), ctypes.c_void_p)
)
threads_per_block = 256
blocks = (N_BENCH + threads_per_block - 1) // threads_per_block
assert hCuda.cuLaunchKernel(k_gen, blocks, 1, 1, threads_per_block, 1, 1, 0, None, g_params, None) == 0
hCuda.cuCtxSynchronize()

h_w_chk = np.zeros(N_CHECK, dtype=np.uint64)
h_b_chk = np.zeros(N_CHECK, dtype=np.uint64)
h_m_chk = np.zeros(N_CHECK, dtype=np.int8)
assert hCuda.cuMemcpyDtoH(h_w_chk.ctypes.data, d_white, N_CHECK * 8) == 0
assert hCuda.cuMemcpyDtoH(h_b_chk.ctypes.data, d_black, N_CHECK * 8) == 0
assert hCuda.cuMemcpyDtoH(h_m_chk.ctypes.data, d_mover, N_CHECK) == 0

pairs = np.column_stack((h_w_chk, h_b_chk))
unique_pairs = np.unique(pairs, axis=0)
popcounts = np.bitwise_count(h_w_chk | h_b_chk)
wrong_mover = int(np.count_nonzero((popcounts & 1) != h_m_chk))
print(f"[2/3] SplitMix64 Legal Board Audit ({N_CHECK:,} sample): {len(unique_pairs):,} distinct ({100.0*len(unique_pairs)/N_CHECK:.2f}%), wrong_mover = {wrong_mover}", flush=True)
assert wrong_mover == 0

# 3. Benchmark 25 iterations x 4,194,304 boards = 104,857,600 tactical evaluations on RTX 4060
ITERS = 25
e_params = (ctypes.c_void_p * 5)(
    ctypes.cast(ctypes.byref(d_white), ctypes.c_void_p),
    ctypes.cast(ctypes.byref(d_black), ctypes.c_void_p),
    ctypes.cast(ctypes.byref(d_mover), ctypes.c_void_p),
    ctypes.cast(ctypes.byref(d_res), ctypes.c_void_p),
    ctypes.cast(ctypes.byref(c_n_bench), ctypes.c_void_p)
)

# Warmup
assert hCuda.cuLaunchKernel(k_eval, blocks, 1, 1, threads_per_block, 1, 1, 0, None, e_params, None) == 0
hCuda.cuCtxSynchronize()

t0 = time.perf_counter()
for _ in range(ITERS):
    res = hCuda.cuLaunchKernel(k_eval, blocks, 1, 1, threads_per_block, 1, 1, 0, None, e_params, None)
    assert res == 0
hCuda.cuCtxSynchronize()
t1 = time.perf_counter()

h_res = np.zeros((N_BENCH, 12), dtype=np.int8)
assert hCuda.cuMemcpyDtoH(h_res.ctypes.data, d_res, N_BENCH * 12) == 0
scores = h_res[:, 0]

elapsed = t1 - t0
total_evals = N_BENCH * ITERS
rate = total_evals / elapsed
print(f"[3/3] RTX 4060 Tactical Playout Benchmark ({N_BENCH:,} boards x {ITERS} iters = {total_evals:,} evals):", flush=True)
print(f"      Execution Time : {elapsed * 1000:.2f} ms", flush=True)
print(f"      Throughput     : {rate / 1e6:.2f} MILLION tactical board evaluations / second", flush=True)
print(f"      Outcome Split  : Wins-in-1 = {np.count_nonzero(scores == 1):,}, Double-Threat-Losses = {np.count_nonzero(scores == -1):,}, Tactical-Neutral = {np.count_nonzero(scores == 0):,}", flush=True)
