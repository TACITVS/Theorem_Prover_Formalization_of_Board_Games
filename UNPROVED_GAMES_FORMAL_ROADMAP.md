# Formal Verification Roadmap: Solved Combinatorial Games & Open Unsolved Frontiers

[![Back to Main Landing Page](https://img.shields.io/badge/⬅_Back_to_Main_Page-README.md-2563eb?style=for-the-badge)](README.md)
[![Rocq 9.1 Verified](https://img.shields.io/badge/Rocq_9.1-85_Theorems_Closed-22c55e?style=for-the-badge)](build.ps1)
[![Lean 4.35.0 Verified](https://img.shields.io/badge/Lean_4.35.0-46_Theorems_0_sorry-10b981?style=for-the-badge)](build_lean.ps1)
[![Connect-5 8x7 Repository](https://img.shields.io/badge/🎲_Connect--5_8x7-Repository-blue?style=for-the-badge)](https://github.com/TACITVS/8x7_Connect_5_Is_A_Proven_Fair_Game)

> **Abstract:** Between 1980 and 2026, computer scientists and combinatorial game theorists resolved the exact game-theoretic values of over a dozen classic board games. However, virtually **every single one of these historic solutions relied on unverified C/C++ code, ad-hoc retrograde databases, or proprietary mainframe scripts**.
>
> Across the **6 verified branches** of this repository — **8×7 Connect-5 (`main`)**, **Nine Men's Morris (`nine-mens-morris`)**, **Twelve Men's Morris (`twelve-mens-morris`)**, **Three Men's Morris (`three-mens-morris`)**, **Six Men's Morris (`six-mens-morris`)**, and **15×15 Freestyle Gomoku (`gomoku-15x15-freestyle`)** — we provide zero-axiom machine-checked formalizations in **Rocq 9.1** and **Lean 4.35.0**. This document catalogs both **solved board games** (verified and upcoming) and **open unsolved classic games whose game-theoretic fairness remains unknown**.

---

## 1. Summary Catalog of Solved Board Games & Formal Verification Status

| Board Game | Dimensions / State Space | Game-Theoretic Value | Original Computational Solver | Formal Theorem Prover Status | Core Mathematical Structure |
| :--- | :---: | :---: | :--- | :---: | :--- |
| **Connect-5 (`8 × 7` Gravity)** | 56 cells (`4.5 × 10^14` states) | **Exact Draw** | Victor Allis (1988), DeepMind Suite | ✅ **VERIFIED (`main` — Rocq 9.1 & Lean 4)** | Follow-Up Induction, Claimeven Parity, Rigid Domino Couplings |
| **Nine Men's Morris (Mill)** | 24 points (`10^10` states) | **Exact Draw** | Ralph Gasser (1993, ETH Zurich) | ✅ **VERIFIED (`nine-mens-morris` — Rocq 9.1 & Lean 4)** | 3-Phase DAG, D₄ Dihedral Symmetry, 8-Stone Transversal Barrier |
| **Twelve Men's Morris (Morabaraba)** | 24 points (`10^12` states) | **Win White (49 Moves)** | Gévay & Danner (2016) | ✅ **VERIFIED (`twelve-mens-morris` — Rocq 9.1 & Lean 4)** | 20 Mills (4 Diagonals), Broken Regularity, Ply 8 Double-Fork |
| **Three Men's Morris (9-Holes)** | 9 points (`3^9` states) | **Exact Draw** | Classical Combinatorial Folklore | ✅ **VERIFIED (`three-mens-morris` — Rocq 9.1 & Lean 4)** | Complete Phase 1 + Phase 2 Constructive Strategy Tree Proof |
| **Six Men's Morris** | 16 points (`3^16 = 4.3 × 10^7`) | **Exact Draw** | Ralph Gasser (1993) | ✅ **VERIFIED (`six-mens-morris` — Rocq 9.1 & Lean 4)** | 16-Vertex 2-Ring Graph, 4-Stone Transversal, 59,049-State Solver |
| **Freestyle Gomoku (`15 × 15`)** | 225 cells (`10^105` states) | **Win White (35 Plies)** | Victor Allis (1993 PhD Thesis) | ✅ **VERIFIED (`gomoku-15x15-freestyle` — Rocq 9.1 & Lean 4)** | 572 Winning Lines, 45-Stone Transversal, Surewicz 35-Ply VCF Tree |
| **Classic Connect-Four** | `7 × 6` grid (`4.53 × 10^12`) | **Win White (P1)** | Allen (1988), Allis (1988), Tromp (1995) | ⏳ **Planned** | Claimeven (57/69 lines), Center Column 3 Pigeonhole, Odd-Threat Zugzwang |
| **Even-Height Connect-Four** | `6 × 6`, `8 × 6`, `8 × 8` | **Win Black (P2)** | John Tromp (1995–2015) | ⏳ **Planned** | Parity Inversion, Strong Domino Traps, Zugzwang Exploitation |
| **Qubic (3D Connect-Four)** | `4 × 4 × 4` (`10^13` states) | **Win White (P1)** | Patashnik (1980), Allis (1994) | ⏳ **Planned** | 64-Bit Exact Hardware Saturation, 76 Winning Lines, VCF/VCT Search |
| **Quarto** | `4 × 4` grid (16 pieces) | **Exact Draw** | Luc Goossens (1998) | ⏳ **Planned** | `(Z_2)^4` Affine Hypercube Symmetry, Lean 4 Quotient Types |
| **Pentago** | `6 × 6` (4 rotating quadrants) | **Win White (P1)** | Geoffrey Irving (2014) | ⏳ **Planned** | D₄ Symmetries + 90° Quadrant Rotations, Retrograde Databases |
| **Hex (`7 × 7` and `8 × 8`)** | 49 and 64 cells | **Win White (P1)** | Hayward, Henderson et al. (2002) | ⏳ **Planned** | Virtual Connection H-Search, Resistance Networks, Carrier Sets |

---

## 2. Unsolved Frontiers: Games Whose Fairness Is Mathematically Unknown

| Game Frontier | Dimensions / Complexity | Suspected / Conjectured Value | Core Unsolved Mathematical Question |
| :--- | :---: | :---: | :--- |
| **Dots and Boxes (`5 × 5` Dots)** | 16 Boxes, 40 Edges | **Conjectured Exact Draw (8–8)** | Famous Conway/Berlekamp open problem: even box parity permits an 8–8 draw, but optimal strategy is unproven. |
| **Connect-5 Critical Threshold** | `8 × 8` and `9 × 7` with gravity | **UNKNOWN (Draw vs. Win White)** | At what exact grid size `(w, h)` does gravity Connect-5 transition from a Claimeven Draw to a First-Player Win? |
| **Connect6 Critical Threshold** | `7 × 7`, `8 × 8`, `9 × 9` grids | **UNKNOWN Boundary** | Designed by I-Chen Wu (2005) for fairness; the critical board size where first-mover advantage forces a win is open. |
| **Russian Checkers (Shashki)** | `8 × 8`, flying kings, backward captures | **Conjectured Exact Draw** | English draughts is solved (Draw); Russian checkers with flying kings has never been computationally exhausted. |

---

## 3. Open Research Target: `5 × 5` Dots and Boxes (16 Boxes)

We highlight **`5 × 5` Dots and Boxes** (16 Boxes, 40 Edges) as a prime open frontier for formal investigation:
1. **The Game:** Played on a `5 × 5` square dot grid containing 40 lines (20 horizontal, 20 vertical) forming 16 unit square boxes.
2. **Conjectured Value:** **Exact 8–8 Fair Draw** under optimal Berlekamp double-dealing strategy.
3. **Formalization Target:** Mechanize Conway's nimstring theory, Berlekamp's long-chain rule, and the 40-edge graph topology in Rocq 9.1 and Lean 4.35.0 with zero unproven axioms.
