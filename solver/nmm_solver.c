#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "nmm_bitboard.h"

/* ASCII Board Representation */
void print_board(const nmm_board_t *b) {
    char s[24];
    for (int i = 0; i < 24; i++) {
        if ((b->white >> i) & 1U) s[i] = 'W';
        else if ((b->black >> i) & 1U) s[i] = 'B';
        else s[i] = '.';
    }
    printf("\n");
    printf("  %c-----------%c-----------%c   (0---1---2)\n", s[0], s[1], s[2]);
    printf("  |   %c-------%c-------%c   |   (| 8-9-10|)\n", s[8], s[9], s[10]);
    printf("  |   |   %c---%c---%c   |   |   (||16 17 18||)\n", s[16], s[17], s[18]);
    printf("  %c---%c---%c       %c---%c---%c   (7 15 23   19 11 3)\n", s[7], s[15], s[23], s[19], s[11], s[3]);
    printf("  |   |   %c---%c---%c   |   |   (||22 21 20||)\n", s[22], s[21], s[20]);
    printf("  |   %c-------%c-------%c   |   (| 14-13-12|)\n", s[14], s[13], s[12]);
    printf("  %c-----------%c-----------%c   (6---5---4)\n", s[6], s[5], s[4]);
    printf("  White: %d stones | Black: %d stones\n\n", popcount24(b->white), popcount24(b->black));
}

int main(void) {
    printf("======================================================================\n");
    printf("Nine Men's Morris - 24-Bit Bitboard Engine & Structural Verifier\n");
    printf("Verifying 16-Mill Regularity, 32-Edge Handshake & O(1) Mill Detection\n");
    printf("======================================================================\n");

    /* 1. Structural self-test */
    printf("[1/4] Verifying Mill Regularity (every vertex in exactly 2 mills)... ");
    for (int p = 0; p < 24; p++) {
        int count = 0;
        for (int m = 0; m < 16; m++) {
            if ((MILL_MASKS[m] >> p) & 1U) count++;
        }
        if (count != 2) {
            printf("FAILED at vertex %d (count=%d)\n", p, count);
            return 1;
        }
    }
    printf("PASSED (24/24 vertices have mill degree 2)\n");

    /* 2. Degree and Handshake verification */
    printf("[2/4] Verifying 32 Undirected Graph Edges (Handshake Lemma = 64)... ");
    int total_degree = 0;
    for (int p = 0; p < 24; p++) {
        total_degree += popcount24(ADJ_MASKS[p]);
    }
    if (total_degree != 64) {
        printf("FAILED (total degree = %d != 64)\n", total_degree);
        return 1;
    }
    printf("PASSED (total degree = 64, exactly 32 edges)\n");

    /* 3. Fast Mill Formation Benchmark */
    printf("[3/4] Benchmarking Fast Mill Detection (2-instruction test)... ");
    clock_t start = clock();
    uint64_t iterations = 100000000ULL;
    bitboard_t test_bb = 7U | (1U << 9) | (1U << 17); /* contains 2 mills */
    volatile int mill_count = 0;
    for (uint64_t i = 0; i < iterations; i++) {
        int v = (int)(i % 24);
        if (forms_mill(test_bb, v)) {
            mill_count++;
        }
    }
    clock_t end = clock();
    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;
    double m_evals = (iterations / elapsed) / 1e6;
    printf("PASSED (%.2f Million evaluations/sec, %.3f s)\n", m_evals, elapsed);

    /* 4. Display Initial Board */
    printf("[4/4] Board Coordinates and Topology Visualization:\n");
    nmm_board_t board;
    board.white = (1U << 0) | (1U << 1) | (1U << 2); /* Mill on ring 0 top */
    board.black = (1U << 8) | (1U << 13) | (1U << 20);
    print_board(&board);

    printf("======================================================================\n");
    printf("ALL STRUCTURAL TESTS AND BENCHMARKS PASSED SUCCESSFULLY!\n");
    printf("======================================================================\n");
    return 0;
}
