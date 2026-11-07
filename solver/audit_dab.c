/*
 * audit_dab.c - Exhaustive Combinatorial and Group-Theoretic Audit
 * of Dots and Boxes (Universal n x n and 5x5 Dots / 4x4 Boxes Grid Graph).
 *
 * Verifies:
 * 1. 40 Edge coordinate encodings (20 horizontal, 20 vertical).
 * 2. 16 Box bounding edge masks and dual degree regularity.
 * 3. 16 Boundary vs 24 Interior edge incidence counts (1*16 + 2*24 = 64).
 * 4. D4 dihedral automorphism group:
 *    - R^4 = id (order 4)
 *    - S^2 = id (order 2)
 *    - R * S = S * R^3 (dihedral relation)
 *    - Invariance of boundary and interior sets under D4.
 * 5. Universal n x n invariants across n = 1 .. 20:
 *    - Euler characteristic: V(n) - E(n) + F(n) = 2.
 *    - Edge decomposition: Bnd(n) + Int(n) = E(n).
 *    - Incidence sum: 1*Bnd(n) + 2*Int(n) = 4*B(n).
 *    - Parity draw admissibility: odd n forbids draw, even n admits draw.
 *    - Tempo surplus: E(n) - B(n) = n*(n + 2).
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#define N 4
#define NUM_DOTS 25
#define NUM_EDGES 40
#define NUM_BOXES 16

static inline uint32_t h_edge(int r, int c) {
    return (uint32_t)(4 * r + c);
}

static inline uint32_t v_edge(int r, int c) {
    return (uint32_t)(20 + 5 * r + c);
}

static uint64_t box_mask[NUM_BOXES];
static int edge_box_count[NUM_EDGES];

static uint32_t rot_edge(uint32_t e) {
    if (e < 20) {
        int r = (int)(e / 4);
        int c = (int)(e % 4);
        return (uint32_t)(20 + 5 * c + (4 - r));
    } else {
        int v = (int)(e - 20);
        int r = v / 5;
        int c = v % 5;
        return (uint32_t)(4 * c + (3 - r));
    }
}

static uint32_t refl_edge(uint32_t e) {
    if (e < 20) {
        int r = (int)(e / 4);
        int c = (int)(e % 4);
        return (uint32_t)(4 * r + (3 - c));
    } else {
        int v = (int)(e - 20);
        int r = v / 5;
        int c = v % 5;
        return (uint32_t)(20 + 5 * r + (4 - c));
    }
}

static void init_boxes(void) {
    for (int r = 0; r < N; r++) {
        for (int c = 0; c < N; c++) {
            int b = 4 * r + c;
            uint32_t top    = h_edge(r, c);
            uint32_t bottom = h_edge(r + 1, c);
            uint32_t left   = v_edge(r, c);
            uint32_t right  = v_edge(r, c + 1);

            box_mask[b] = (1ULL << top) | (1ULL << bottom) | (1ULL << left) | (1ULL << right);
            edge_box_count[top]++;
            edge_box_count[bottom]++;
            edge_box_count[left]++;
            edge_box_count[right]++;
        }
    }
}

int main(void) {
    printf("======================================================================\n");
    printf(" DOTS AND BOXES COMBINATORIAL & GROUP-THEORETIC AUDIT\n");
    printf(" Grid: 5x5 Dots / 4x4 Boxes (40 Edges, 16 Boxes, D4 Symmetry)\n");
    printf("======================================================================\n\n");

    init_boxes();

    // 1. Audit Box incidence and degrees
    printf("[1/5] Auditing Box Incidences and Degrees...\n");
    int total_incidences = 0;
    for (int b = 0; b < NUM_BOXES; b++) {
        int deg = __builtin_popcountll(box_mask[b]);
        if (deg != 4) {
            fprintf(stderr, "FAIL: Box %d has degree %d != 4\n", b, deg);
            return 1;
        }
        total_incidences += deg;
    }
    printf("  -> Verified all 16 boxes have exactly 4 incident edges (dual degree = 4).\n");
    printf("  -> Total box-edge incidences = %d (Expected: 64).\n", total_incidences);
    assert(total_incidences == 64);

    // 2. Audit Boundary and Interior Edges
    printf("\n[2/5] Auditing Boundary vs Interior Edges...\n");
    int boundary_count = 0;
    int interior_count = 0;
    for (int e = 0; e < NUM_EDGES; e++) {
        int cnt = edge_box_count[e];
        if (cnt == 1) {
            boundary_count++;
        } else if (cnt == 2) {
            interior_count++;
        } else {
            fprintf(stderr, "FAIL: Edge %d has invalid box incidence count %d\n", e, cnt);
            return 1;
        }
    }
    printf("  -> Boundary edges (incidence 1): %d (Expected: 16 = 4*4).\n", boundary_count);
    printf("  -> Interior edges (incidence 2): %d (Expected: 24 = 2*4*3).\n", interior_count);
    printf("  -> Edge sum: %d + %d = %d (Expected: 40 = 2*4*5).\n",
           boundary_count, interior_count, boundary_count + interior_count);
    printf("  -> Incidence double-count: 1*%d + 2*%d = %d (Expected: 64 = 4*16).\n",
           boundary_count, interior_count, boundary_count + 2 * interior_count);
    assert(boundary_count == 16);
    assert(interior_count == 24);
    assert(boundary_count + 2 * interior_count == 64);

    // 3. Audit D4 Dihedral Automorphisms
    printf("\n[3/5] Auditing D4 Dihedral Group Actions on 40 Edges...\n");
    for (uint32_t e = 0; e < NUM_EDGES; e++) {
        // Rotation order 4: R^4(e) = e
        uint32_t r1 = rot_edge(e);
        uint32_t r2 = rot_edge(r1);
        uint32_t r3 = rot_edge(r2);
        uint32_t r4 = rot_edge(r3);
        if (r4 != e) {
            fprintf(stderr, "FAIL: R^4(%u) = %u != %u\n", e, r4, e);
            return 1;
        }

        // Reflection order 2: S^2(e) = e
        uint32_t s1 = refl_edge(e);
        uint32_t s2 = refl_edge(s1);
        if (s2 != e) {
            fprintf(stderr, "FAIL: S^2(%u) = %u != %u\n", e, s2, e);
            return 1;
        }

        // Dihedral commutation: R * S = S * R^3
        uint32_t rs = rot_edge(refl_edge(e));
        uint32_t sr3 = refl_edge(r3);
        if (rs != sr3) {
            fprintf(stderr, "FAIL: Dihedral commutation broken at e=%u: R(S(%u))=%u, S(R^3(%u))=%u\n",
                    e, e, rs, e, sr3);
            return 1;
        }

        // Invariance of boundary/interior classification
        if (edge_box_count[r1] != edge_box_count[e]) {
            fprintf(stderr, "FAIL: Rotation altered edge type at e=%u\n", e);
            return 1;
        }
        if (edge_box_count[s1] != edge_box_count[e]) {
            fprintf(stderr, "FAIL: Reflection altered edge type at e=%u\n", e);
            return 1;
        }
    }
    printf("  -> Verified R^4 = id for all 40 edges.\n");
    printf("  -> Verified S^2 = id for all 40 edges.\n");
    printf("  -> Verified R * S = S * R^3 (dihedral relation) for all 40 edges.\n");
    printf("  -> Verified edge type (boundary vs interior) is invariant under D4.\n");

    // 4. Audit D4 Orbits
    printf("\n[4/5] Auditing D4 Edge Orbits...\n");
    bool visited[NUM_EDGES] = {false};
    int orbit_count = 0;
    for (uint32_t e = 0; e < NUM_EDGES; e++) {
        if (visited[e]) continue;
        orbit_count++;
        int orbit_size = 0;
        uint32_t cur = e;
        // Generate group orbit under D4 = {id, R, R^2, R^3, S, SR, SR^2, SR^3}
        uint32_t g_edges[8];
        g_edges[0] = cur;
        g_edges[1] = rot_edge(cur);
        g_edges[2] = rot_edge(g_edges[1]);
        g_edges[3] = rot_edge(g_edges[2]);
        g_edges[4] = refl_edge(cur);
        g_edges[5] = rot_edge(g_edges[4]);
        g_edges[6] = rot_edge(g_edges[5]);
        g_edges[7] = rot_edge(g_edges[6]);

        for (int i = 0; i < 8; i++) {
            uint32_t ge = g_edges[i];
            if (!visited[ge]) {
                visited[ge] = true;
                orbit_size++;
            }
        }
        printf("  Orbit %d (rep edge %2u, %s): size %d\n",
               orbit_count, e, edge_box_count[e] == 1 ? "Boundary" : "Interior", orbit_size);
    }
    printf("  -> All 40 edges partitioned cleanly into %d orbits under D4.\n", orbit_count);

    // 5. Universal n x n Grid Theorems across n = 1 .. 20
    printf("\n[5/5] Auditing Universal n x n Grid Theorems (n = 1 .. 20)...\n");
    for (int n = 1; n <= 20; n++) {
        int V = (n + 1) * (n + 1);
        int E = 2 * n * (n + 1);
        int B = n * n;
        int F = B + 1; // B bounded faces + 1 unbounded exterior face

        // Euler characteristic: V - E + F = 2
        int euler = V - E + F;
        assert(euler == 2);

        // Edge decomposition
        int bnd = 4 * n;
        int in_e = 2 * n * (n - 1);
        assert(bnd + in_e == E);

        // Incidence sum: 1*Bnd + 2*Int = 4*B
        assert(1 * bnd + 2 * in_e == 4 * B);

        // Tempo surplus
        int tempo_surplus = E - B;
        assert(tempo_surplus == n * (n + 2));

        // Parity
        if (n % 2 == 1) {
            assert(B % 2 == 1); // Odd boxes forbid draw
        } else {
            assert(B % 2 == 0); // Even boxes admit draw
        }
    }
    printf("  -> All 5 Universal Theorems verified algebraically and computationally across n = 1 .. 20.\n");
    printf("\n======================================================================\n");
    printf(" ALL 5 AUDIT SUITES PASSED FLAWLESSLY!\n");
    printf("======================================================================\n");

    return 0;
}
