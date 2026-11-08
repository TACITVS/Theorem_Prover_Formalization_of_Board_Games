# Graph Theory, Mill Regularity, and D₄ Dihedral Symmetry of Nine & Twelve Men's Morris

[![Back to Main Landing Page](https://img.shields.io/badge/⬅_Back_to_Main_Page-README.md-2563eb?style=for-the-badge)](README.md)
[![Rocq 9.1 Verified](https://img.shields.io/badge/Rocq_9.1-85_Theorems_Closed-22c55e?style=for-the-badge)](build.ps1)
[![Lean 4.35.0 Verified](https://img.shields.io/badge/Lean_4.35.0-46_Theorems_0_sorry-10b981?style=for-the-badge)](build_lean.ps1)

> **Abstract:** Nine Men's Morris and Twelve Men's Morris are played on a 24-vertex graph `G = (V, E)` embedded in the plane as three concentric squares interconnected by four orthogonal radial midpoint segments (32 edges, 16 mills) and, in Twelve Men's Morris, four diagonal corner segments (40 edges, 20 mills). This document establishes the exact algebraic and topological foundations of both games, including vertex degree distributions, Handshake Lemma invariants, broken vs. uniform mill regularity, the 8-element D₄ dihedral automorphism group action, and the Ply 8 Corner Ray Double-Fork Theorem. Every theorem herein is machine-verified in both **Rocq 9.1** ([`NMMGraph.v`](NMMGraph.v), [`NMM12Graph.v`](NMM12Graph.v)) and **Lean 4.35.0** ([`lean4/NineMensMorris.lean`](lean4/NineMensMorris.lean), [`lean4/TwelveMensMorris.lean`](lean4/TwelveMensMorris.lean)) with **zero unproven axioms and zero sorrys**.

---

## 1. Planar Graph Topology and Canonical Indexing

The 24 vertices `V = {0, 1, ..., 23}` are partitioned into three concentric squares (rings `r ∈ {0, 1, 2}`), each containing 8 vertices indexed clockwise starting from the North-West corner:

```text
  0-----------1-----------2   (Ring 0 Outer: 0 to 7)
  | \ 8-------9------10 / |   (Ring 1 Middle: 8 to 15)
  |   | \16--17--18 / |   |   (Ring 2 Inner: 16 to 23)
  7--15--23       19-11---3
  |   | /22--21--20 \ |   |
  | /14------13------12 \ |
  6-----------5-----------4
```

### Algebraic Coordinate Decomposition
For any vertex `p ∈ {0, ..., 23}`:
- **Ring Index:** `ring(p) = p / 8` ∈ `{0 (Outer), 1 (Middle), 2 (Inner)}`
- **Cyclic Position:** `pos(p) = p mod 8` ∈ `{0, ..., 7}`
  - Even positions `{0, 2, 4, 6}` correspond to the 12 **corners**.
  - Odd positions `{1, 3, 5, 7}` correspond to the 12 **midpoints**.

---

## 2. Vertex Degree Distribution & Handshake Invariants

### Nine Men's Morris (32 Edges)
1. **Concentric Cycles (24 edges):** Each ring `r` forms an 8-cycle `(8r + i, 8r + (i+1) mod 8)`.
2. **Radial Orthogonal Connectors (8 edges):** Connecting corresponding midpoints across adjacent rings: `(1, 9, 17)`, `(3, 11, 19)`, `(5, 13, 21)`, `(7, 15, 23)`.
3. **Degree Distribution & Handshake (`handshake_lemma`):**
   - 12 Corners have `deg(p) = 2`; 8 Outer/Inner Midpoints have `deg(p) = 3`; 4 Middle Midpoints have `deg(p) = 4`.
   - `Σ_{v ∈ V} deg(v) = (12 × 2) + (8 × 3) + (4 × 4) = 64 = 2 × card(E_9)`.

### Twelve Men's Morris (40 Edges)
Adding the 8 diagonal corner edges along `(0, 8, 16)`, `(2, 10, 18)`, `(4, 12, 20)`, `(6, 14, 22)`:
- **8 Middle Ring Vertices (`{8..15}`):** `deg_12(p) = 4` (`middle_ring_degree_4`).
- **8 Outer Ring Vertices (`{0..7}`):** `deg_12(p) = 3` (`outer_ring_degree_3`).
- **8 Inner Ring Vertices (`{16..23}`):** `deg_12(p) = 3` (`inner_ring_degree_3`).
- **Handshake Lemma (`handshake_lemma_12`):** `Σ_{v ∈ V} deg_12(v) = (8 × 4) + (16 × 3) = 32 + 48 = 80 = 2 × card(E_12)`.

---

## 3. Mill Regularity vs. Broken Regularity

- **Nine Men's Morris (16 Mills):** Every vertex `v ∈ V` belongs to **strictly 2 mills** (`mill_regularity`: `16 × 3 = 48 = 24 × 2`).
- **Twelve Men's Morris (20 Mills):** Adding the 4 diagonal mills `(0, 8, 16)`, `(2, 10, 18)`, `(4, 12, 20)`, `(6, 14, 22)` creates **Broken Mill Regularity**:
  - Every corner `c ∈ Corners` belongs to **strictly 3 mills** (`corner_mill_degree_3`).
  - Every midpoint `m ∈ Midpoints` belongs to **strictly 2 mills** (`midpoint_mill_degree_2`).
  - **Incidence Handshake (`mill_incidence_handshake_12`):** `(12 × 3) + (12 × 2) = 60 = 20 × 3`.

---

## 4. D₄ Dihedral Symmetry Group Actions

The automorphism group of both the 9MM and 12MM graphs is isomorphic to the dihedral group of order 8:
```text
D4 = ⟨ R, S | R^4 = Id, S^2 = Id, R · S = S · R^3 ⟩
```

### Explicit Permutation Formulas
1. **Clockwise 90-Degree Rotation R:** `R(p) = 8 × (p / 8) + (pos(p) + 2) mod 8`
2. **Vertical Axis Reflection S (North-South Midline):** `S(p) = 8 × (p / 8) + (10 - (pos(p) mod 8)) mod 8`

Both `R` and `S` preserve adjacency, all 16 classical mills (`rot_preserves_mills`, `refl_preserves_mills`), and all 20 Twelve Men's Morris mills (`rot_preserves_all_20_mills`, `refl_preserves_all_20_mills`).

---

## 5. Machine Verification Summary

| Theorem Description | Mathematical Formula / Invariant | Rocq 9.1 (`.v`) | Lean 4.35.0 (`.lean`) | Axioms |
| :--- | :--- | :--- | :--- | :---: |
| Point Universe Cardinality | `card(V) = 24` | `all_points_length` | `all_points_length` | **0** |
| 9MM Mill System Cardinality | `card(Mills_9) = 16` | `all_mills_count` | `all_mills_count` | **0** |
| 9MM Uniform Mill Regularity | `∀ v ∈ V, deg_mill(v) = 2` | `mill_regularity` | `mill_regularity_all` | **0** |
| 9MM Graph Handshake Lemma | `Σ deg(v) = 64 = 2 * card(E_9)` | `handshake_lemma` | `handshake_lemma_64` | **0** |
| 12MM Mill System Cardinality | `card(Mills_12) = 20` | `all_mills_12_count` | `all_mills_12_count` | **0** |
| 12MM Broken Regularity (Corners) | `∀ c ∈ Corners, deg_mill_12(c) = 3` | `corner_mill_degree_3` | `corners_mill_degree_3` | **0** |
| 12MM Broken Regularity (Midpoints) | `∀ m ∈ Midpoints, deg_mill_12(m) = 2` | `midpoint_mill_degree_2` | `midpoints_mill_degree_2` | **0** |
| 12MM Graph Handshake Lemma | `Σ deg_12(v) = 80 = 2 * card(E_12)` | `handshake_lemma_12` | `graph_12_handshake` | **0** |
| D₄ Rotation & Reflection Orders | `R^4 = Id, S^2 = Id, R · S = S · R^3` | `rot_order_4`, `refl_order_2`, `dihedral_relation` | `rot_order_4`, `refl_order_2`, `dihedral_commutation` | **0** |
| D₄ 20-Mill Automorphism | `R(Mills_12) = Mills_12, S(Mills_12) = Mills_12` | `rot_preserves_all_20_mills`, `refl_preserves_all_20_mills` | `rot_preserves_all_20_mills`, `refl_preserves_all_20_mills` | **0** |
| 12MM 8-Stone Transversal Barrier | `∀ m ∈ Mills_12, m ∩ T_12 ≠ ∅` | `transversal_12_8_covers_all_20_mills` | `transversal_12_8_covers_all_20_mills` | **0** |
| Corner 0 Unblocked Rays at Ply 1 | `∀ b1 ≠ 0, ≥ 2 rays of Corner 0 unblocked` | `corner_0_two_rays_unblocked_after_ply1` | `corner_0_two_rays_unblocked_after_ply1` | **0** |
| Ply 8 Double-Fork Theorem | `[0,6,8,14]` threatens `{15, 22}` (`15 ≠ 22`) | `ply8_corner_fork_theorem` | `ply8_corner_fork_theorem` | **0** |
