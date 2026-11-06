# Graph Theory, Mill Regularity, and D4 Dihedral Symmetry of Nine Men's Morris

[![Back to Main Landing Page](https://img.shields.io/badge/⬅_Back_to_Main_Page-README.md-2563eb?style=for-the-badge)](README.md)
[![Rocq 9.1 Verified](https://img.shields.io/badge/Rocq_9.1-33_Theorems_Closed-22c55e?style=for-the-badge)](build.ps1)
[![Lean 4.35.0 Verified](https://img.shields.io/badge/Lean_4.35.0-19_Theorems_0_sorry-10b981?style=for-the-badge)](build_lean.ps1)

> **Abstract:** Nine Men's Morris is played on a 24-vertex planar graph G = (V, E) embedded in the real plane as three concentric squares interconnected by four orthogonal radial segments. This document establishes the exact algebraic and topological foundations of the game, including its 32 undirected edges, 16 collinear 3-vertex mills, Handshake Lemma invariant, and 8-element D4 dihedral automorphism group action. Every theorem herein is machine-verified in both **Rocq 9.1** (`NMMGraph.v`) and **Lean 4.35.0** (`NineMensMorris.lean`) with **zero unproven axioms and zero sorrys**.

---

## 1. Planar Graph Topology and Canonical Indexing

The 24 vertices V = {0, 1, ..., 23} are partitioned into three concentric squares (rings r ∈ {0, 1, 2}), each containing 8 vertices indexed clockwise starting from the North-West corner:

```
  0-----------1-----------2   (Ring 0 Outer: 0 to 7)
  |   8-------9------10   |   (Ring 1 Middle: 8 to 15)
  |   |  16--17--18   |   |   (Ring 2 Inner: 16 to 23)
  7--15--23       19-11---3
  |   |  22--21--20   |   |
  |  14------13------12   |
  6-----------5-----------4
```

### Algebraic Coordinate Decomposition
For any vertex p ∈ {0, ..., 23}:
- **Ring Index:** `ring(p) = p / 8` ∈ {0 (Outer), 1 (Middle), 2 (Inner)}
- **Cyclic Position:** `pos(p) = p mod 8` ∈ {0, ..., 7}
  - Even positions {0, 2, 4, 6} correspond to the 12 **corners**.
  - Odd positions {1, 3, 5, 7} correspond to the 12 **midpoints**.

---

## 2. Vertex Degree Distribution & Handshake Invariant

The 32 undirected edges E are formed by:
1. **Concentric Cycles (24 edges):** Each ring r forms an 8-cycle `(8r + i, 8r + (i+1) mod 8)`.
2. **Radial Orthogonal Connectors (8 edges):** Connecting corresponding midpoints across adjacent rings:
   - North: (1, 9) and (9, 17)
   - East: (3, 11) and (11, 19)
   - South: (5, 13) and (13, 21)
   - West: (7, 15) and (15, 23)

### Degree Classification
- **12 Corners:** Deg(p) = 2 for p ∈ {0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22}.
- **8 Outer/Inner Midpoints:** Deg(p) = 3 for p ∈ {1, 3, 5, 7, 17, 19, 21, 23}.
- **4 Middle Midpoints:** Deg(p) = 4 for p ∈ {9, 11, 13, 15}.

### Handshake Lemma
The sum of degrees over all 24 vertices satisfies Euler's Handshake Lemma:
```
Σ_{v ∈ V} Deg(v) = (12 × 2) + (8 × 3) + (4 × 4) = 24 + 24 + 16 = 64 = 2 × |E|
```
Mechanized in Rocq (`handshake_lemma`) and Lean 4 (`handshake_lemma_64`).

---

## 3. The 16 Mills and Mill Regularity Theorem

A **mill** is a collinear triplet of vertices along a graph line. There are exactly 16 mills:
- **Ring 0 (4 mills):** (0, 1, 2), (2, 3, 4), (4, 5, 6), (0, 6, 7)
- **Ring 1 (4 mills):** (8, 9, 10), (10, 11, 12), (12, 13, 14), (8, 14, 15)
- **Ring 2 (4 mills):** (16, 17, 18), (18, 19, 20), (20, 21, 22), (16, 22, 23)
- **Radial Cross (4 mills):** (1, 9, 17), (3, 11, 19), (5, 13, 21), (7, 15, 23)

### Theorem (Mill Regularity)
**Every single vertex v ∈ V belongs to EXACTLY 2 distinct mills.**
- *Proof:*
  - Each corner v ∈ {0, 2, 4, 6} of ring r belongs to the two adjacent sides of ring r.
  - Each midpoint v ∈ {1, 3, 5, 7} of ring r belongs to one ring side and one radial cross line.
  - Verification: 16 mills × 3 vertices = 48 vertex instances = 24 vertices × 2.
- Mechanized in Rocq (`mill_regularity`) and Lean 4 (`mill_regularity_all`).

---

## 4. D4 Dihedral Symmetry Group Actions

The automorphism group of the Nine Men's Morris graph is isomorphic to the dihedral group of order 8:
```
D4 = ⟨ R, S | R^4 = Id, S^2 = Id, R · S = S · R^3 ⟩
```

### Explicit Permutation Formulas
1. **Clockwise 90-Degree Rotation R:**
   ```
   R(p) = 8 × (p / 8) + (pos(p) + 2) mod 8
   ```
2. **Vertical Axis Reflection S (North-South Midline):**
   ```
   S(p) = 8 × (p / 8) + (10 - (pos(p) mod 8)) mod 8
   ```

### Automorphism Invariance Theorems
1. **Adjacency Preservation:** For all u, v ∈ V:
   - `is_adjacent(R(u), R(v)) = is_adjacent(u, v)`
   - `is_adjacent(S(u), S(v)) = is_adjacent(u, v)`
2. **Mill System Preservation:** For every mill m = (a, b, c) ∈ Mills:
   - `sort(R(a), R(b), R(c)) ∈ Mills`
   - `sort(S(a), S(b), S(c)) ∈ Mills`

Mechanized in Rocq (`rot_preserves_adjacency`, `refl_preserves_adjacency`, `rot_preserves_mills`, `refl_preserves_mills`) and Lean 4 (`rot_preserves_adjacency`, `refl_preserves_adjacency`, `rot_preserves_mills`, `refl_preserves_mills`).

---

## 5. Machine Verification Summary

| Theorem Description | Mathematical Formula / Invariant | Rocq 9.1 (`.v`) | Lean 4.35.0 (`.lean`) | Axioms |
| :--- | :--- | :--- | :--- | :---: |
| Point Universe Cardinality | |V| = 24 | `all_points_length` | `all_points_length` | **0** |
| Mill System Cardinality | |Mills| = 16 | `all_mills_count` | `all_mills_count` | **0** |
| Mill Regularity | ∀ v ∈ V, deg_mill(v) = 2 | `mill_regularity` | `mill_regularity_all` | **0** |
| Graph Handshake Lemma | Σ deg(v) = 64 = 2|E| | `handshake_lemma` | `handshake_lemma_64` | **0** |
| Corner Degree Classification | ∀ c ∈ Corners, deg(c) = 2 | `corner_degree_2` | `corners_degree_2` | **0** |
| Outer/Inner Midpoint Degrees | ∀ m ∈ Mid_02, deg(m) = 3 | `outer_inner_midpoint_degree_3` | `outer_inner_midpoints_degree_3` | **0** |
| Middle Midpoint Degrees | ∀ m ∈ Mid_1, deg(m) = 4 | `middle_midpoint_degree_4` | `middle_midpoints_degree_4` | **0** |
| D4 Rotation Order 4 | R^4 = Id | `rot_order_4` | `rot_order_4` | **0** |
| D4 Reflection Order 2 | S^2 = Id | `refl_order_2` | `refl_order_2` | **0** |
| D4 Commutation | R · S = S · R^3 | `dihedral_relation` | `dihedral_commutation` | **0** |
| D4 Adjacency Automorphism | Adj(g(u), g(v)) = Adj(u, v) | `rot_preserves_adjacency`, `refl_preserves_adjacency` | `rot_preserves_adjacency`, `refl_preserves_adjacency` | **0** |
| D4 Mill Automorphism | g(Mills) = Mills | `rot_preserves_mills`, `refl_preserves_mills` | `rot_preserves_mills`, `refl_preserves_mills` | **0** |
| Midpoint Mill Transversal | ∀ m ∈ Mills, m ∩ Midpoints ≠ ∅ | `all_mills_intersect_midpoints` | `all_mills_intersect_midpoints` | **0** |
| 24-Bit Bitboard Reflection | TestBit(BB(S), v) = (v ∈ S) | `testbit_stones_to_bitboard` | `mill_masks_exact` | **0** |
