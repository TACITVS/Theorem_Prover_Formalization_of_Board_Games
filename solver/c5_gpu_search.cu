#include <cuda_runtime.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <vector>
#include <algorithm>
#include <iostream>
#include <chrono>

#define W 8
#define H 8
#define K 5
#define FULL_MASK 0xFFFFFFFFFFFFFFFFULL
#define BOTTOM_MASK 0x0101010101010101ULL

typedef unsigned long long u64;
typedef uint32_t u32;
typedef int8_t i8;

// Bit operations
#define BIT(c, r) (1ULL << ((c) * 8 + (r)))
#define COLMASK(c) (0xFFULL << ((c) * 8))

// Constant memory for winning lines
__constant__ u64 c_LINES[96];
static u64 h_LINES[96];

// Initialize the 96 winning lines
void init_lines() {
    int nl = 0;
    // Horizontal lines (32)
    for (int r = 0; r < H; r++) {
        for (int c = 0; c <= W - K; c++) {
            u64 m = 0;
            for (int i = 0; i < K; i++) m |= BIT(c + i, r);
            h_LINES[nl++] = m;
        }
    }
    // Vertical lines (32)
    for (int c = 0; c < W; c++) {
        for (int r = 0; r <= H - K; r++) {
            u64 m = 0;
            for (int i = 0; i < K; i++) m |= BIT(c, r + i);
            h_LINES[nl++] = m;
        }
    }
    // Diagonal / lines (16)
    for (int c = 0; c <= W - K; c++) {
        for (int r = 0; r <= H - K; r++) {
            u64 m = 0;
            for (int i = 0; i < K; i++) m |= BIT(c + i, r + i);
            h_LINES[nl++] = m;
        }
    }
    // Diagonal \ lines (16)
    for (int c = 0; c <= W - K; c++) {
        for (int r = K - 1; r < H; r++) {
            u64 m = 0;
            for (int i = 0; i < K; i++) m |= BIT(c + i, r - i);
            h_LINES[nl++] = m;
        }
    }
    cudaMemcpyToSymbol(c_LINES, h_LINES, sizeof(h_LINES));
}

// 5-in-a-row detector (both host and device)
__host__ __device__ inline bool has_won_5(u64 s) {
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
    // Diagonal \ (shift 7, starting col c0 in 0..3 and row r0 in 4..7)
    m = s & (s >> 7);
    if ((m & (m >> 14) & (s >> 28)) & 0x00000000F0F0F0F0ULL) return true;
    return false;
}

static inline u64 splitmix64(u64 *state) {
    u64 z = (*state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

// Generate a legal, non-terminal reachable Connect-5 board using SplitMix64
static inline void generate_legal_board(u64 seed, u64 *out_w, u64 *out_b, i8 *out_mover) {
    u64 rng = splitmix64(&seed);
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
    *out_w = w;
    *out_b = b;
    *out_mover = (i8)(actual_moves & 1);
}

// GPU Evaluation Result Structure
struct EvalResult {
    i8 score;       // 1 = Win in 1, -1 = Loss (opponent has >=2 winning threats), 0 = Non-terminal tactical score
    i8 best_col;    // Best recommended move
    i8 num_moves;   // Number of valid moves
    i8 pad;
    i8 col_scores[8]; // Relative scores of moves 0..7 (-128 if illegal/blunder)
};

// Massively parallel 1-ply/2-ply tactical threat & blunder evaluator kernel
__global__ void eval_batch_kernel(
    const u64 *d_white,
    const u64 *d_black,
    const i8 *d_mover, // 0 = White, 1 = Black (per position)
    EvalResult *d_results,
    int n
) {
    int idx = blockDim.x * blockIdx.x + threadIdx.x;
    if (idx >= n) return;

    u64 w = d_white[idx];
    u64 b = d_black[idx];
    int mover = (int)d_mover[idx];
    u64 mask = w | b;

    u64 my_stones = (mover == 0) ? w : b;
    u64 opp_stones = (mover == 0) ? b : w;

    EvalResult res;
    res.score = 0;
    res.best_col = -1;
    res.num_moves = 0;
    res.pad = (i8)mover;
    for (int c = 0; c < 8; c++) res.col_scores[c] = -128;

    if (has_won_5(opp_stones)) {
        res.score = -1;
        d_results[idx] = res;
        return;
    }
    if (has_won_5(my_stones)) {
        res.score = 1;
        d_results[idx] = res;
        return;
    }

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

        int score = 0;
        if (c == 3 || c == 4) score += 6;
        else if (c == 2 || c == 5) score += 4;
        else if (c == 1 || c == 6) score += 2;

        res.col_scores[c] = (i8)score;
        if (score > best_score) {
            best_score = score;
            best_c = c;
        }
    }

    res.best_col = best_c;
    d_results[idx] = res;
}

int main() {
    printf("Initializing Connect-5 Bitboard Tactical Evaluator on GPU...\n");
    init_lines();

    int dev = 0;
    cudaGetDevice(&dev);
    cudaDeviceProp prop;
    cudaGetDeviceProperties(&prop, dev);
    printf("Device: %s (%d SMs, Compute %d.%d, VRAM: %.1f GB)\n",
           prop.name, prop.multiProcessorCount, prop.major, prop.minor,
           (double)prop.totalGlobalMem / (1024*1024*1024));

    // Part 1: 262,144-position validation & distinctness check
    const int N_CHECK = 262144;
    std::vector<u64> h_w(N_CHECK), h_b(N_CHECK);
    std::vector<i8> h_m(N_CHECK);
    std::vector<std::pair<u64, u64>> pairs(N_CHECK);

    int wrong_mover_count = 0;
    for (int i = 0; i < N_CHECK; i++) {
        generate_legal_board((u64)i + 1ULL, &h_w[i], &h_b[i], &h_m[i]);
        pairs[i] = {h_w[i], h_b[i]};
        u64 msk = h_w[i] | h_b[i];
        int pop = 0;
        while (msk) { msk &= msk - 1; pop++; }
        if ((pop & 1) != h_m[i]) wrong_mover_count++;
    }
    std::sort(pairs.begin(), pairs.end());
    size_t distinct_count = std::unique(pairs.begin(), pairs.end()) - pairs.begin();
    printf("Generated %d legal boards: %zu distinct (%.2f%%), wrong_mover = %d\n",
           N_CHECK, distinct_count, 100.0 * (double)distinct_count / N_CHECK, wrong_mover_count);

    // Part 2: 4,194,304-position x 25-iteration throughput benchmark (104,857,600 tactical evaluations)
    const int N_BENCH = 4194304;
    const int ITERS = 25;
    u64 *h_bw = (u64*)malloc(N_BENCH * sizeof(u64));
    u64 *h_bb = (u64*)malloc(N_BENCH * sizeof(u64));
    i8 *h_bm = (i8*)malloc(N_BENCH * sizeof(i8));
    EvalResult *h_results = (EvalResult*)malloc(N_BENCH * sizeof(EvalResult));

    for (int i = 0; i < N_BENCH; i++) {
        generate_legal_board((u64)i + 1ULL, &h_bw[i], &h_bb[i], &h_bm[i]);
    }

    u64 *d_white, *d_black;
    i8 *d_mover;
    EvalResult *d_results;
    cudaMalloc(&d_white, N_BENCH * sizeof(u64));
    cudaMalloc(&d_black, N_BENCH * sizeof(u64));
    cudaMalloc(&d_mover, N_BENCH * sizeof(i8));
    cudaMalloc(&d_results, N_BENCH * sizeof(EvalResult));

    cudaMemcpy(d_white, h_bw, N_BENCH * sizeof(u64), cudaMemcpyHostToDevice);
    cudaMemcpy(d_black, h_bb, N_BENCH * sizeof(u64), cudaMemcpyHostToDevice);
    cudaMemcpy(d_mover, h_bm, N_BENCH * sizeof(i8), cudaMemcpyHostToDevice);

    int threads = 256;
    int blocks = (N_BENCH + threads - 1) / threads;

    // Warmup launch
    eval_batch_kernel<<<blocks, threads>>>(d_white, d_black, d_mover, d_results, N_BENCH);
    cudaDeviceSynchronize();

    printf("Benchmarking GPU Tactical Evaluator (%d threads x %d iterations = %lld evaluations)...\n",
           N_BENCH, ITERS, (long long)N_BENCH * ITERS);
    auto t0 = std::chrono::high_resolution_clock::now();
    for (int it = 0; it < ITERS; it++) {
        eval_batch_kernel<<<blocks, threads>>>(d_white, d_black, d_mover, d_results, N_BENCH);
    }
    cudaDeviceSynchronize();
    auto t1 = std::chrono::high_resolution_clock::now();
    double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();

    cudaMemcpy(h_results, d_results, N_BENCH * sizeof(EvalResult), cudaMemcpyDeviceToHost);

    int wins = 0, losses = 0, neutral = 0;
    for (int i = 0; i < N_BENCH; i++) {
        if (h_results[i].score == 1) wins++;
        else if (h_results[i].score == -1) losses++;
        else neutral++;
    }

    double total_evals = (double)N_BENCH * ITERS;
    printf("GPU Execution Time: %.3f ms\n", ms);
    printf("Throughput: %.2f Million tactical board evaluations / second\n", (total_evals / (ms / 1000.0)) / 1e6);
    printf("Batch Results (%d boards): Wins-in-1=%d, Double-Threat-Losses=%d, Tactical-Neutral=%d\n",
           N_BENCH, wins, losses, neutral);

    cudaFree(d_white);
    cudaFree(d_black);
    cudaFree(d_mover);
    cudaFree(d_results);
    free(h_bw);
    free(h_bb);
    free(h_bm);
    free(h_results);
    return 0;
}
