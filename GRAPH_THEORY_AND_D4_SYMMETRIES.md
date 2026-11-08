# Graph Theory, Mill Regularity, and D₄ Dihedral Symmetry of Nine Men's Morris

[![Back to Main Landing Page](https://img.shields.io/badge/⬅_Back_to_Main_Page-README.md-2563eb?style=for-the-badge)](README.md)
[![Rocq 9.1 Verified](https://img.shields.io/badge/Rocq_9.1-65_Theorems_Closed-22c55e?style=for-the-badge)](build.ps1)
[![Lean 4.35.0 Verified](https://img.shields.io/badge/Lean_4.35.0-26_Theorems_0_sorry-10b981?style=for-the-badge)](build_lean.ps1)

> **Abstract:** Nine Men's Morris is played on a 24-vertex planar graph `G = (V, E)` embedded in the real plane `R^2` as three concentric squares interconnected by four orthogonal radial segments. This document establishes the exact algebraic and topological foundations of the game, including its 32 undirected edges, 16 collinear 3-vertex mills, Handshake Lemma invariant, and 8-element D₄ dihedral automorphism group action. Every theorem herein is machine-verified in both **Rocq 9.1** ([`NMMGraph.v`](NMMGraph.v)) and **Lean 4.35.0** ([`lean4/NineMensMorris.lean`](lean4/NineMensMorris.lean)) with **zero unproven axioms and zero sorrys**.

---

## 1. Planar Graph Topology and Canonical Indexing

The 24 vertices `V = {0, 1, ..., 23}` are partitioned into three concentric squares (rings `r in {0, 1, 2}`), each containing 8 vertices indexed clockwise starting from the North-West corner:

```text
  0-----------1-----------2   (Ring 0 Outer: 0 to 7)
  |   8-------9------10   |   (Ring 1 Middle: 8 to 15)
  |   |  16--17--18   |   |   (Ring 2 Inner: 16 to 23)
  7--15--23       19-11---3
  |   |  22--21--20   |   |
  |  14------13------12   |
  6-----------5-----------4
```

### Algebraic Coordinate Decomposition

For any vertex `p in {0, ..., 23}`:
- **Ring Index:** `ring(p) = floor(p / 8) in {0, 1, 2}`
- **Cyclic Position:** `pos(p) = p mod 8 in {0, ..., 7}`
  - Even positions `{0, 2, 4, 6}` correspond to the 12 **corners**.
  - Odd positions `{1, 3, 5, 7}` correspond to the 12 **midpoints**.

---

## 2. Vertex Degree Distribution & Handshake Invariant

The 32 undirected edges `E` are formed by:
1. **Concentric Cycles (24 edges):** Each ring `r` forms an 8-cycle: `e = (8r + i, 8r + ((i + 1) mod 8))` for `r in {0, 1, 2}`, `i in {0, ..., 7}`.
2. **Radial Orthogonal Connectors (8 edges):** Connecting corresponding midpoints across adjacent rings:
   - **North:** `(1, 9)` and `(9, 17)`
   - **East:** `(3, 11)` and `(11, 19)`
   - **South:** `(5, 13)` and `(13, 21)`
   - **West:** `(7, 15)` and `(15, 23)`

### Degree Classification

- **12 Corners:** `deg(p) = 2` for all `p in {0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22}`.
- **8 Outer/Inner Midpoints:** `deg(p) = 3` for all `p in {1, 3, 5, 7, 17, 19, 21, 23}`.
- **4 Middle Midpoints:** `deg(p) = 4` for all `p in {9, 11, 13, 15}`.

### Handshake Lemma

The sum of degrees over all 24 vertices satisfies Euler's Handshake Lemma:

```text
sum_{v in V} deg(v) = (12 × 2) + (8 × 3) + (4 × 4) = 24 + 24 + 16 = 64 = 2 * card(E)
```

Mechanized in Rocq (`handshake_lemma`) and Lean 4 (`handshake_lemma_64`).

---

## 3. The 16 Mills and Mill Regularity Theorem

A **mill** is a collinear triplet of vertices along a graph line. There are exactly 16 mills in `M`:
- **Ring 0 (4 mills):** `(0, 1, 2)`, `(2, 3, 4)`, `(4, 5, 6)`, `(0, 6, 7)`
- **Ring 1 (4 mills):** `(8, 9, 10)`, `(10, 11, 12)`, `(12, 13, 14)`, `(8, 14, 15)`
- **Ring 2 (4 mills):** `(16, 17, 18)`, `(18, 19, 20)`, `(20, 21, 22)`, `(16, 22, 23)`
- **Radial Cross (4 mills):** `(1, 9, 17)`, `(3, 11, 19)`, `(5, 13, 21)`, `(7, 15, 23)`

### Theorem (Mill Regularity)

**Every single vertex `v in V` belongs to EXACTLY 2 distinct mills:**

```text
forall v in V,  deg_M(v) = 2
```

*Proof:*
- Each corner `v in {0, 2, 4, 6}` of ring `r` belongs to the two adjacent sides of ring `r`.
- Each midpoint `v in {1, 3, 5, 7}` of ring `r` belongs to one ring side and one radial cross line.
- Double-counting verification: `16 mills × 3 vertices = 48 vertex incidences = 24 vertices × 2`.

Mechanized in Rocq (`mill_regularity`) and Lean 4 (`mill_regularity_all`).

---

## 4. D₄ Dihedral Symmetry Group Actions

The automorphism group of the Nine Men's Morris graph is isomorphic to the dihedral group of order 8:

```text
D_4 = < R, S | R^4 = Id,  S^2 = Id,  R · S = S · R^3 >
```

### Explicit Permutation Formulas

1. **Clockwise 90° Rotation `R`:** `R(p) = 8 * (p / 8) + ((p + 2) mod 8)`
2. **Vertical Axis Reflection `S` (North-South Midline):** `S(p) = 8 * (p / 8) + ((10 - (p mod 8)) mod 8)`

### Automorphism Invariance Theorems

1. **Adjacency Preservation:** For all `u, v in V`: `Adj(R(u), R(v)) = Adj(u, v)` and `Adj(S(u), S(v)) = Adj(u, v)`.
2. **Mill System Preservation:** For every mill `m = {a, b, c} in M`: `R(m) in M` and `S(m) in M`.
3. **Move Action Involution:** For every move `m`: `rot_move^4(m) = m` (`rot_move_order_4`) and `refl_move^2(m) = m` (`refl_move_involutive`).

Mechanized in Rocq (`rot_preserves_adjacency`, `refl_preserves_adjacency`, `rot_preserves_mills`, `refl_preserves_mills`, `rot_move_order_4`, `refl_move_involutive`) and Lean 4 (`rot_preserves_adjacency`, `refl_preserves_adjacency`, `rot_preserves_mills`, `refl_preserves_mills`).

---

## 5. Machine Verification Summary

| Theorem Description | Mathematical Invariant | Rocq 9.1 (`.v`) | Lean 4.35.0 (`.lean`) | Axioms |
| :--- | :---: | :--- | :--- | :---: |
| **Point Universe Cardinality** | `card(V) = 24` | `all_points_length` | `all_points_length` | **0** |
| **Mill System Cardinality** | `card(M) = 16` | `all_mills_count` | `all_mills_count` | **0** |
| **Mill Regularity** | `forall v in V, deg_M(v) = 2` | `mill_regularity` | `mill_regularity_all` | **0** |
| **Graph Handshake Lemma** | `sum_{v} deg(v) = 64 = 2 * card(E)` | `handshake_lemma` | `handshake_lemma_64` | **0** |
| **Corner Degree Classification** | `forall c in Corners, deg(c) = 2` | `corner_degree_2` | `corners_degree_2` | **0** |
| **Outer/Inner Midpoint Degrees** | `forall m in Mid_{0,2}, deg(m) = 3` | `outer_inner_midpoint_degree_3` | `outer_inner_midpoints_degree_3` | **0** |
| **Middle Midpoint Degrees** | `forall m in Mid_1, deg(m) = 4` | `middle_midpoint_degree_4` | `middle_midpoints_degree_4` | **0** |
| **D₄ Rotation Order 4** | `R^4 = Id` | `rot_order_4` | `rot_order_4` | **0** |
| **D₄ Reflection Order 2** | `S^2 = Id` | `refl_order_2` | `refl_order_2` | **0** |
| **D₄ Commutation Law** | `R · S = S · R^3` | `dihedral_relation` | `dihedral_commutation` | **0** |
| **D₄ Adjacency Automorphism** | `Adj(g(u), g(v)) = Adj(u, v)` | `rot_preserves_adjacency` | `rot_preserves_adjacency` | **0** |
| **D₄ Mill Automorphism** | `g(M) = M` | `rot_preserves_mills` | `rot_preserves_mills` | **0** |
| **D₄ Move Involution** | `rot_move^4(m) = m, refl_move^2(m) = m` | `rot_move_order_4` | — | **0** |
| **Midpoint Mill Transversal** | `forall m in M, m intersect Midpoints != empty` | `all_mills_intersect_midpoints` | `all_mills_intersect_midpoints` | **0** |
| **8-Stone Transversal Lower Bound** | `2k >= 16 -> k >= 8` | `transversal_size_lower_bound` | `transversal_8_covers_all_mills` | **0** |
| **24-Bit Bitboard Reflection** | `testBit(BB(S), v) <-> v in S` | `testbit_stones_to_bitboard` | `mill_masks_exact` | **0** |
