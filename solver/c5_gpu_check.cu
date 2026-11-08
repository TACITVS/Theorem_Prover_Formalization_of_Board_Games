#include <cuda_runtime.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

#define W 8
#define H 8
#define K 5
#define NL 96
#define FULL_MASK 0xFFFFFFFFFFFFFFFFULL
#define BIT(c, r) (1ULL << ((c) * 8 + (r)))

typedef unsigned long long u64;

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

__constant__ u64 d_LINES[NL];
static u64 h_LINES[NL];

void init_lines() {
    int nl = 0;
    for (int r = 0; r < H; r++)
        for (int c = 0; c <= W - K; c++) {
            u64 m = 0;
            for (int i = 0; i < K; i++) m |= BIT(c + i, r);
            h_LINES[nl++] = m;
        }
    for (int c = 0; c < W; c++)
        for (int r = 0; r <= H - K; r++) {
            u64 m = 0;
            for (int i = 0; i < K; i++) m |= BIT(c, r + i);
            h_LINES[nl++] = m;
        }
    for (int c = 0; c <= W - K; c++)
        for (int r = 0; r <= H - K; r++) {
            u64 m = 0;
            for (int i = 0; i < K; i++) m |= BIT(c + i, r + i);
            h_LINES[nl++] = m;
        }
    for (int c = 0; c <= W - K; c++)
        for (int r = K - 1; r < H; r++) {
            u64 m = 0;
            for (int i = 0; i < K; i++) m |= BIT(c + i, r - i);
            h_LINES[nl++] = m;
        }
    cudaMemcpyToSymbol(d_LINES, h_LINES, sizeof(h_LINES));
}

__device__ inline u64 splitmix64_dev(u64 x) {
    x += 0x9E3779B97F4A7C15ULL;
    x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
    x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
    return x ^ (x >> 31);
}

__global__ void verify_detector_kernel(int n_random, int *d_errors) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // 1. Thread 0..95: verify all 96 winning lines and all 480 4-stone near misses
    if (idx < NL) {
        u64 mask = d_LINES[idx];
        if (!has_won_5(mask)) atomicAdd(d_errors, 1);
        for (int bit = 0; bit < 64; bit++) {
            u64 b = 1ULL << bit;
            if (mask & b) {
                if (has_won_5(mask ^ b)) atomicAdd(d_errors, 1);
            }
        }
    }

    // 2. Thread 0..n_random-1: compare shift detector vs 96-line table on random boards
    if (idx < n_random) {
        u64 s = splitmix64_dev((u64)idx + 1ULL) & FULL_MASK;
        bool shift_res = has_won_5(s);
        bool enum_res = false;
        for (int l = 0; l < NL; l++) {
            if ((s & d_LINES[l]) == d_LINES[l]) {
                enum_res = true;
                break;
            }
        }
        if (shift_res != enum_res) atomicAdd(d_errors, 1);
    }
}

int main() {
    init_lines();
    const int N_RANDOM = 100000;
    int *d_errors;
    cudaMalloc(&d_errors, sizeof(int));
    cudaMemset(d_errors, 0, sizeof(int));

    int threads = 256;
    int blocks = (N_RANDOM + threads - 1) / threads;
    verify_detector_kernel<<<blocks, threads>>>(N_RANDOM, d_errors);
    cudaDeviceSynchronize();

    int h_errors = -1;
    cudaMemcpy(&h_errors, d_errors, sizeof(int), cudaMemcpyDeviceToHost);
    cudaFree(d_errors);

    printf("GPU Win-Detector Verification (96 lines, 480 near-misses, %d random bitboards): errors = %d (expected 0)\n",
           N_RANDOM, h_errors);
    return (h_errors == 0) ? 0 : 1;
}
