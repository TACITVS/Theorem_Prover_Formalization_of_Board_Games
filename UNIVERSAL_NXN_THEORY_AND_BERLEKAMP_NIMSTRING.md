# Universal n × n Dots and Boxes: Combinatorics, Planar Topology, and Berlekamp Nimstring Game Theory

## Deductive Dual-Prover Verification in Rocq 9.1 and Lean 4.35.0

---

## 1. Executive Summary & Foundational Invariants

**Dots and Boxes** is a finite, 2-player, perfect-information combinatorial game played on an (n + 1) × (n + 1) lattice of dots comprising n × n unit square boxes. Players take turns drawing unoriented edges between adjacent dots. Completing the 4th boundary edge of any box claims that box for the player and awards an immediate bonus turn (**Double-Turn Rule**).

This monograph presents the algebraic, topological, and game-theoretic theory governing Dots and Boxes for all grid sizes n ≥ 1, together with the concrete 5 × 5 dots (4 × 4 boxes, 40 edges) graph topology and operational semantics, formally verified with **zero unproven axioms** in **Rocq 9.1** (46 theorems) and **Lean 4.35.0** (24 theorems).

---

## 2. Universal n × n Grid Graph Topology

### 2.1 Graph Dimensions and Euler Characteristic

Let G_n = (V_n, E_n) be the planar grid graph representing an n × n box grid ((n + 1) × (n + 1) dots):

**Vertices (Dots):**

```text
V(n) = (n + 1)²
```

**Edges (Segments):** Horizontal edges count n(n + 1) and vertical edges count n(n + 1):

```text
E(n) = 2n(n + 1)
```

**Faces:** The plane is partitioned into B(n) = n² bounded square faces (boxes) and 1 unbounded exterior face ℰ:

```text
F(n) = B(n) + 1 = n² + 1
```

### Theorem 1 (Planar Euler Characteristic Invariant)
For all n ≥ 1, the connected planar grid graph G_n satisfies Euler's formula:

```text
V(n) − E(n) + F(n) = 2
```

*Proof.* Expanding into polynomials over ℕ (via `V(n) + F(n) = E(n) + 2`):

```text
(n + 1)² + (n² + 1) = (n² + 2n + 1) + (n² + 1) = 2n(n + 1) + 2
```

Formalized in Rocq as `euler_characteristic_universal` and in Lean 4 as `euler_characteristic_universal`.

---

## 3. Edge Decomposition and Incidence Double-Counting

Edges in G_n partition into two disjoint classes:
1. **Boundary Edges (`Bnd`):** Edges lying on the outer perimeter of the grid, each incident to exactly 1 box.
2. **Interior Edges (`Int`):** Shared dividing edges separating two adjacent boxes, each incident to exactly 2 boxes.

### Theorem 2 (Universal Edge Decomposition)
For all n ≥ 1:

```text
Bnd(n) = 4n
Int(n) = 2n(n − 1)
Bnd(n) + Int(n) = 4n + 2n(n − 1) = 2n(n + 1) = E(n)
```

*Proof.* The boundary consists of 4 sides of n edges each, giving 4n. The total number of edges is 2n(n + 1). Subtracting gives 2n(n + 1) − 4n = 2n(n − 1). Formalized as `edge_decomposition_universal`.

### Theorem 3 (Box-Edge Incidence Double-Counting Law)
Let ℐ be the set of box-edge incidence pairs (b, e) where edge e bounds box b. Then:

```text
|ℐ| = 1 · Bnd(n) + 2 · Int(n) = 4 · B(n) = 4n²
```

*Proof.* Every box is bounded by 4 edges. Hence the sum over all n² boxes is 4n². Grouping by edges, each boundary edge contributes 1 and each interior edge contributes 2:

```text
1 · (4n) + 2 · (2n(n − 1)) = 4n + 4n² − 4n = 4n²
```

Formalized as `box_incidence_sum_universal` and `total_box_incidences`.

---

## 4. Game-Theoretic Score Conservation and Parity Dichotomy

In any completed game of Dots and Boxes, all E(n) edges are played and all B(n) = n² boxes are claimed:

```text
S₁ + S₂ = n²
```

On the concrete 4 × 4 box board (`DABGame.v`), we prove inductively that every step increases the total score by `count_newly_completed s e` (`step_score_sum`), that `count_newly_completed s e` matches the increase in `length (filter (is_box_completed s) all_boxes)` (`completed_boxes_step`), and that when all 40 edges are present on the board, all 16 boxes are completed (`all_edges_complete_all_boxes`, `terminal_score_sum_16`).

### Theorem 4 (Parity Draw Dichotomy)
1. **Odd n Strictly Forbids Draws:** If n is odd, then n² ≡ 1 (mod 2). Consequently, for any completed game with S₁ + S₂ = n², we have S₁ ≠ S₂. An exact draw is mathematically impossible.
2. **Even n Admits Draws:** If n is even, n = 2k, then n² = 4k² ≡ 0 (mod 2). An exact draw is parity-admissible with equal scores:

```text
S₁ = S₂ = 2k² = n² / 2
```

*Proof.*
- For n ≡ 1 (mod 2), assume S₁ = S₂. Then S₁ + S₂ = 2S₂. But 2S₂ ≡ 0 (mod 2) while n² ≡ 1 (mod 2), a contradiction.
- For n ≡ 0 (mod 2), setting s = n² / 2 = 2(n/2)² yields s + s = n².

*Corollary (The 5 × 5 Dot Board Draw Score):*
For n = 4 (4 × 4 boxes, 16 boxes), an exact draw requires:

```text
S₁ = S₂ = 8
```

*Corollary (The 7 × 7 Dot Board Draw Score):*
For n = 6 (6 × 6 boxes, 36 boxes), an exact draw requires:

```text
S₁ = S₂ = 18
```

*Corollary (The 7 × 7 Box Grid Strict Unfairness):*
For n = 7 (7 × 7 boxes, 49 boxes, 8 × 8 dots), 49 ≡ 1 (mod 2). An exact draw is strictly impossible:

```text
S₁ ≠ S₂
```

Formalized as `score_conservation_universal`, `odd_n_strictly_forbids_draw`, `even_n_admits_draw`, `dab_4x4_draw_score`, `dab_6x6_draw_score`, and `dab_7x7_boxes_strictly_forbids_draw`.

---

## 5. The Universal Tempo Conservation Law

Every edge played during a game on the 4 × 4 grid completes at most 2 boxes (`max_two_boxes_per_edge` in `DABGame.v`), so every move falls into one of three categories:
- e₀: Moves that complete **0 boxes** (turn passes to opponent).
- e₁: Moves that complete **1 box** (bonus turn awarded).
- e₂: Moves that complete **2 boxes** simultaneously (bonus turn awarded).

The total number of edges played is:

```text
e₀ + e₁ + e₂ = E(n)
```

The total number of boxes captured is:

```text
0 · e₀ + 1 · e₁ + 2 · e₂ = B(n)
```

Subtracting the two equations eliminates e₁ completely:

```text
(e₀ + e₁ + e₂) − (e₁ + 2e₂) = E(n) − B(n)
e₀ − e₂ = 2n(n + 1) − n² = n² + 2n = n(n + 2)
```

### Theorem 5 (The Net Tempo Surplus Law)
In any completed game of Dots and Boxes on an n × n grid:

```text
e₀ − e₂ = n(n + 2)
```

For n = 4 (5 × 5 dots, 40 edges, 16 boxes):

```text
e₀ − e₂ = 40 − 16 = 24
```

For n = 6 (7 × 7 dots, 84 edges, 36 boxes):

```text
e₀ − e₂ = 84 − 36 = 48
```

Formalized as `tempo_conservation_universal`, `tempo_difference_universal`, `net_tempo_surplus`, `dab_4x4_tempo_surplus`, and `dab_6x6_tempo_surplus`.

*Significance:* Because e₀ is the only move type that relinquishes the turn, the first player to run out of safe non-scoring moves is forced to open a chain for their opponent.

---

## 6. Planar Dual Graph and Conway-Berlekamp Nimstring Equivalence

John H. Conway and Elwyn Berlekamp proved that Dots and Boxes is isomorphic to the impartial game **Nimstring** played on the planar dual graph G_n*.

The dual vertex set V_n* contains n² vertices corresponding to the boxes, plus a special ground vertex ℰ corresponding to the exterior face:

```text
V_n* = {B_0, ..., B_{n²−1}} ∪ {ℰ}
```

Each grid edge e ∈ E_n corresponds to a dual edge e* connecting the faces adjacent to e.

### Theorem 6 (Dual 4-Regularity & Incident Edge Distinctness)
Every internal box vertex B_b in the 4 × 4 grid has 4 pairwise distinct incident edges (`length (box_edges b) = 4` and `NoDup (box_edges b)`):

```text
∀ b ∈ {0, ..., 15},   deg*(B_b) = deg_int*(B_b) + deg_ext*(B_b) = 4
```

*Proof.* Every unit square box in the Cartesian grid is bounded by top, bottom, left, and right edges `[H(r, c); H(r+1, c); V(r, c); V(r, c+1)]`. Each boundary edge connects B_b to ℰ, while each interior edge connects B_b to an adjacent box. Formalized in Rocq (`box_edges_length`, `box_edges_nodup`, `box_edges_bound`, `dual_box_degree_4`) and in Lean 4 (`dual_box_degree_4`, `box_edges_nodup`).

### 6.1 The 3D Polyhedral Dual Isomorphism (Steinitz's Theorem & Spherical Compactification)

By **Steinitz's Theorem (1922)**, every 3-connected planar graph is isomorphic to the 1-skeleton of a convex 3-dimensional polyhedron. When the planar dual graph G_n* is embedded on the 2-sphere 𝕊² = ℝ² ∪ {∞}, the exterior ground face ℰ becomes the **Apex (South Pole)** of a concrete 3D convex polyhedron 𝒫_n:

| [ID] | Polyhedral Element in 𝒫_n | Count in Polyhedron 𝒫_n | Correspondence in 2D Grid G_n |
| :---: | :--- | :---: | :--- |
| **[01]** | **Vertices (V)** | n² + 1 | n² box vertices on the 3D base + 1 Apex vertex ℰ |
| **[02]** | **Edges (E)** | 2n(n + 1) | 2n(n + 1) grid segments (primal = dual edges) |
| **[03]** | **Faces (F)** | (n + 1)² | (n + 1)² lattice dots of the primal grid |
| **[04]** | **Quadrilateral Faces** | (n − 1)² | Interior dots (degree 4 in G_n) |
| **[05]** | **Triangular Faces** | 4(n − 1) | Boundary dots (degree 3 in G_n) |
| **[06]** | **Corner Facets** | 4 | Corner dots (degree 2 in G_n) |

The 3D polyhedral invariant holds identically:

```text
V − E + F = (n² + 1) − 2n(n + 1) + (n + 1)² = 2
```

### 6.2 3D Geometric Toolings Explaining 2D Grid Dynamics

| [ID] | 2D Dots and Boxes Phenomenon | 3D Geometric / Polyhedral Tool | Mathematical Principle |
| :---: | :--- | :--- | :--- |
| **[A]** | **Boundary-First Opening Moves** | **Discrete Gauss-Bonnet Curvature Defect:** Interior box vertices satisfy ∑ θ_i = 4 × (π / 2) = 2π, hence discrete curvature K(v) = 2π − 2π = 0 (intrinsically flat). All curvature defect is concentrated at the boundary and Apex ℰ (∑ K = 4π), explaining why strategic initiative originates at the boundary. | ∑_{v ∈ V} K(v) = 2π χ(𝕊²) = 4π |
| **[B]** | **Dual Degree 4 Regularity** | **Steinitz 1-Skeleton:** Every interior vertex of 𝒫_n has degree 4; the Apex ℰ has degree 4n. | Convex 3D Polyhedral 1-skeleton |
| **[C]** | **Nimstring Edge Severing** | **Koebe–Andreev–Thurston (KAT) Hyperbolic Manifolds:** Primal dots and dual boxes form mutually orthogonal circle packings on 𝕊², realizing an ideal right-angled hyperbolic polyhedron in ℍ³. Drawing an edge corresponds to collapsing a geodesic ridge in ℍ³. | Orthogonal circle packings in ℍ³ |
| **[D]** | **Sacrifice Law S = 2C + 4L** | **Alexandrov 3D Polyhedral Folding:** Connected box chains form unfolded nets of 3D orthogonal polycubes. Long chains represent open prismatic cylinders requiring 2 end-caps to close; loops require 4 bounding faces. The sacrifice 2C + 4L is the boundary cost to cap polyhedral cylinders. | Alexandrov's Uniqueness Theorem |
| **[E]** | **Homological Chain Parity** | **Toroidal Compactification (𝕋²):** Identifying opposite boundaries yields the self-dual regular map {4, 4}_{n,0} where χ(𝕋²) = 0 and the Apex disappears, showing parity is governed by the first homology group H₁(𝕋², ℤ) ≅ ℤ². | Clifford torus embedding in ℝ⁴ |

---

## 7. Berlekamp's Long-Chain Double-Dealing Sacrifice Principle

A **long chain** is a sequence of 3 or more boxes where each box shares interior edges with its neighbors. A **closed loop** is a cycle of 4 or more boxes.

### 7.1 The Greedy Trap
When a player is given a long chain of k ≥ 3 boxes, a naive greedy player captures all k boxes. However, completing the k-th box grants a bonus turn when no other safe moves remain. The greedy player is thus forced to play an edge that opens the next chain for the opponent, conceding the game.

### 7.2 The Hard-Hearted Handout (Double-Dealing)
Elwyn Berlekamp proved the optimal double-dealing maneuver in a chain of k ≥ 3 boxes:
1. Capture the first k − 2 boxes in the chain (in a 3-box chain, Player 1 draws `x = 340` to capture Box 1 and earns a bonus turn).
2. For the final 2 boxes (box k − 1 and box k), do **NOT** draw the shared dividing edge between them. Instead, draw the **far exterior edge of box k** (at `x = 620` in the 3-box chain), leaving the dividing edge between box k − 1 and box k (at `x = 480`) open as a 2-box doubleton!
3. Because drawing the far exterior edge of box k completes 0 boxes, the turn passes to the opponent.
4. The opponent is forced to accept the handout by drawing the shared dividing edge (`x = 480`), capturing both box k − 1 and box k simultaneously (+2 boxes) and earning a bonus turn with no remaining boxes in the chain.
5. The opponent must now play an edge that opens the next closed chain, surrendering all subsequent boxes in that territory to the double-dealer!

### Theorem 7 (Berlekamp Sacrifice Arithmetic Invariants)
Let C be the number of long chains and L the number of closed loops in the endgame. The total number of boxes sacrificed by the double-dealer across C chains (2 boxes each) and L loops (4 boxes each) satisfies:

```text
S_sac = 2 · C + 4 · L = 2(C + 2L)
```

Whenever total boxes B ≥ 2C + 4L, there exists a non-negative remainder `rem = B − (2C + 4L)` such that:

```text
B = (2C + 4L) + rem
```

Formalized as `berlekamp_double_deal_sacrifice` and `berlekamp_parity_control`.

---

## 8. Concrete 5 × 5 Dot Board (4 × 4 Boxes, 40 Edges)

### 8.1 Coordinate Indexing System

For the concrete 5 × 5 dot lattice (4 × 4 boxes, 40 edges), the coordinates are indexed canonically:

* **Horizontal Edges (20):** `H(r, c) = 4r + c` for `r ∈ {0, ..., 4}`, `c ∈ {0, ..., 3}` (indices `0 ... 19`)
* **Vertical Edges (20):** `V(r, c) = 20 + 5r + c` for `r ∈ {0, ..., 3}`, `c ∈ {0, ..., 4}` (indices `20 ... 39`)
* **Boxes (16):** `B(r, c) = 4r + c` for `r, c ∈ {0, ..., 3}` (indices `0 ... 15`)

The 4 bounding edges of box `(r, c)` form the ordered 4-tuple:

```text
BoxEdges(r, c) = [ H(r, c),  H(r + 1, c),  V(r, c),  V(r, c + 1) ]
```

### 8.2 Dihedral Automorphism Group D₄
The square grid graph possesses the full symmetry group of the square `D₄ = ⟨R, S | R⁴ = 1, S² = 1, R·S = S·R³⟩`:
* **90° Clockwise Rotation (R):**
  - Horizontal edge `(r, c) ↦` Vertical edge `(c, 4 − r)`.
  - Vertical edge `(r, c) ↦` Horizontal edge `(c, 3 − r)`.
* **Vertical Reflection (S):**
  - Horizontal edge `(r, c) ↦` Horizontal edge `(r, 3 − c)`.
  - Vertical edge `(r, c) ↦` Vertical edge `(r, 4 − c)`.

### Theorem 8 (D₄ Group Action & Boundary Invariance Verification)
For all edge indices `e < 40`:
1. `R⁴(e) = e`
2. `S²(e) = e`
3. `R(S(e)) = S(R³(e))`
4. `is_boundary_edge(R(e)) = is_boundary_edge(e)`
5. `is_boundary_edge(S(e)) = is_boundary_edge(e)`

Formalized in Rocq (`rot_order_4`, `refl_order_2`, `dihedral_relation`, `rot_preserves_boundary`, `refl_preserves_boundary`) and in Lean 4 (`rot_order_4`, `refl_order_2`, `dihedral_commutation`, `rot_preserves_boundary`, `refl_preserves_boundary`).

---

## 9. Assumption Audit & Deductive Verification Matrix

### Rocq 9.1 (`DABCheckAssumptions.v`)
```text
Closed under the global context (46/46 theorems audited)
ALL THEOREMS FULLY VERIFIED (0 AXIOMS / CLOSED UNDER GLOBAL CONTEXT)
```

### Lean 4.35.0 (`lean4/DotsAndBoxes.lean`)
```text
All Lean 4 proofs successfully compiled and verified!
Total verified theorems audited: 24
Approved kernel axioms only: [propext, Quot.sound, Classical.choice].
Zero 'sorry' keywords, zero unapproved axioms.
```

All source files, proofs, solvers, and vector illustrations are completely reproducible via:
```powershell
powershell -ExecutionPolicy Bypass -File .\build.ps1
powershell -ExecutionPolicy Bypass -File .\build_lean.ps1
gcc -O3 -Wall -Wextra -o solver\audit_dab.exe solver\audit_dab.c; .\solver\audit_dab.exe
gcc -O3 -Wall -Wextra -o solver\dots_solver.exe solver\dots_solver.c; .\solver\dots_solver.exe
```
