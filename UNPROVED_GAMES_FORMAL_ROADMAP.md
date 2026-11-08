# Formal Verification Roadmap: Solved Combinatorial Games & Open Unsolved Frontiers

[![Back to Main Landing Page](https://img.shields.io/badge/⬅_Back_to_Main_Page-README.md-2563eb?style=for-the-badge)](README.md)
[![Rocq 9.1 Verified](https://img.shields.io/badge/Rocq_9.1-318_Theorems_Closed-22c55e?style=for-the-badge)](build.ps1)
[![Lean 4.35.0 Verified](https://img.shields.io/badge/Lean_4.35.0-192_Theorems_0_sorry-10b981?style=for-the-badge)](build_lean.ps1)
[![Formalization Hub](https://img.shields.io/badge/🎲_Formalization_Hub-6_Branches_Verified-blue?style=for-the-badge)](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games)

> **Abstract:** Between 1980 and 2026, computer scientists and combinatorial game theorists resolved the exact game-theoretic values of over a dozen classic board games. However, virtually **every single one of these historic solutions relies on unverified C/C++ code, ad-hoc retrograde databases, or proprietary mainframe scripts**.
>
> Following our complete machine-checked formalization suite across six dedicated Git branches—**Standard Checkers (`checkers`: 59 Rocq / 15 Lean 4 theorems)**, **Nine Men's Morris (`nine-mens-morris`: 74 Rocq / 33 Lean 4 theorems)**, **Twelve Men's Morris (`twelve-mens-morris`: 74 Rocq / 48 Lean 4 theorems)**, **5×5 Dots and Boxes (`dots-and-boxes`: 34 Rocq / 17 Lean 4 theorems)**, **8×7 Gravity Connect-5 (`connect5-8x7`: 33 Rocq / 42 Lean 4 theorems)**, and **8×8 Gravity Connect-5 (`connect5-8x8`: 44 Rocq / 37 Lean 4 theorems)**—this document provides a comprehensive scientific catalog and execution roadmap of both **completed and remaining solved board games** and **open unsolved frontiers**.

---

## 1. Summary Catalog of Solved Board Games & Formal Verification Status

| Board Game | Dimensions / State Space | Game-Theoretic Value | Original Computational Solver | Formal Theorem Prover Status | Core Mathematical Structure |
| :--- | :---: | :---: | :---: | :---: | :--- |
| **Standard Checkers (English Draughts)** | 32 dark squares (5 × 10²⁰ states) | **Exact Draw** | Jonathan Schaeffer et al. (2007, *Chinook*) | ✅ **VERIFIED (59 Rocq / 15 Lean 4)** | 32-Square Lattice, Jump Vectors (+7,+9,-9,-7), Potential Φ(st), 4×4 Micro Draw |
| **Nine Men's Morris (Mill)** | 24 points (10¹⁰ states) | **Exact Draw** | Ralph Gasser (1993, ETH Zurich) | ✅ **VERIFIED (74 Rocq / 33 Lean 4)** | 3-Phase DAG, D₄ Dihedral Symmetry, 8-Stone Transversal Barrier |
| **Twelve Men's Morris (Morabaraba)** | 24 points (10¹² states) | **Win White (49 Moves)** | Gévay & Danner (2016) | ✅ **VERIFIED (74 Rocq / 48 Lean 4)** | 20 Mills (4 Diagonals), Broken Regularity, Ply 8 Double-Fork |
| **5×5 Dots and Boxes** | 16 Boxes, 40 Edges (2⁴⁰ states) | **Exact 8–8 Draw** | Berlekamp / Nimstring Dual Suite | ✅ **VERIFIED (34 Rocq / 17 Lean 4)** | Planar Dual Graph, 40-Edge Incidence, Double-Dealing Parity |
| **Connect-5 (8×7 Gravity)** | 56 cells (4.5 × 10¹⁴ states) | **Exact Draw** | Allis (1988), DeepMind Suite | ✅ **VERIFIED (33 Rocq / 42 Lean 4)** | Follow-Up Induction, Claimeven Parity, 108 Winning Lines covered by 28 Pairs |
| **Connect-5 (8×8 Gravity)** | 64 cells (10¹⁸ states) | **Exact Draw** | DeepMind Multi-Weight Pairing Suite | ✅ **VERIFIED (44 Rocq / 37 Lean 4)** | 128 Winning Lines, Weight-2/Weight-3 Dual Pairing H1 & H2 |
| **Classic Connect-Four** | 7×6 grid (4.53 × 10¹² states) | **Win White (P1)** | Allen (1988), Allis (1988), Tromp (1995) | ❌ **Unverified** | Claimeven (57/69 lines), Center Column 3 Pigeonhole, Odd-Threat Zugzwang |
| **Even-Height Connect-Four** | 6×6, 8×6, 8×8 | **Win Black (P2)** | John Tromp (1995–2015) | ❌ **Unverified** | Parity Inversion, Strong Domino Traps, Zugzwang Exploitation |
| **Qubic (3D Connect-Four)** | 4×4×4 (10¹³ states) | **Win White (P1)** | Patashnik (1980), Allis (1994) | ❌ **Unverified** | 64-Bit Exact Hardware Saturation, 76 Winning Lines, VCF/VCT Search |
| **Quarto** | 4×4 grid (16 pieces) | **Exact Draw** | Luc Goossens (1998) | ❌ **Unverified** | (ℤ₂)⁴ Affine Hypercube Symmetry, Lean 4 Quotient Types |
| **Pentago** | 6×6 (4 rotating quadrants) | **Win White (P1)** | Geoffrey Irving (2014) | ❌ **Unverified** | D₄ Symmetries + 90° Quadrant Rotations, Retrograde Databases |
| **Freestyle Gomoku** | 15×15 (10¹⁰⁵ states) | **Win White (P1)** | Victor Allis (1993 PhD Thesis) | ❌ **Unverified** | Inductive Threat-Space Search (VCF / VCT), Proof-Number Search |
| **Hex (7×7 and 8×8)** | 49 and 64 cells | **Win White (P1)** | Hayward, Henderson et al. (2002) | ❌ **Unverified** | Virtual Connection H-Search, Resistance Networks, Carrier Sets |
| **Chomp (3×n and n×n)** | Arbitrary rectangular grid | **Win White (P1)** | David Gale (1974), Zeilberger (2001) | ❌ **Unverified** | Poset Ideal Games, Constructive Winning First-Move Formulas |
| **Domineering (6×6 and 8×8)** | Grid tiling by 2×1 dominoes | **Partisan Values** | Conway (1976), Bullock (2002) | ❌ **Unverified** | Combinatorial Game Theory, Surreal Numbers, Dyadic Rational Values |

---

## 2. Unsolved Frontiers: Games Whose Fairness Is Mathematically Unknown

| Game Frontier | Dimensions / Complexity | Suspected / Conjectured Value | Core Unsolved Mathematical Question |
| :--- | :---: | :---: | :--- |
| **Connect-5 Critical Threshold** | 9×7 and 9×8 with gravity | **UNKNOWN (Draw vs. Win White)** | With 8×7 and 8×8 proven to be exact Draws, at what exact grid width (w ≥ 9) does gravity Connect-5 transition to a First-Player Win? |
| **Connect6 Critical Threshold** | 7×7, 8×8, 9×9 grids | **UNKNOWN Boundary** | Designed by I-Chen Wu (2005) for fairness; the critical board size where first-mover advantage forces a win is open. |
| **Russian Checkers (Shashki)** | 8×8, flying kings, backward captures | **Conjectured Exact Draw** | English draughts is solved (Draw); Russian checkers with flying kings and backward men captures has never been computationally exhausted. |

---

## 3. Future Formalization Targets

Having completed zero-axiom formalizations across all 6 primary branches (`checkers`, `nine-mens-morris`, `twelve-mens-morris`, `dots-and-boxes`, `connect5-8x7`, `connect5-8x8`), our next formal verification targets are:
1. **Qubic (4×4×4 3D Connect-Four):** Mechanizing Patashnik's and Allis's threat-space winning tree over the 76 winning lines of the 64-cell hypercube in Rocq 9.1 and Lean 4.35.0.
2. **Classic 7×6 Connect-Four:** Formalizing the center-column pigeonhole principle and odd-threat zugzwang refutation that enables White (Player 1) to overcome Black's Claimeven pairing.
