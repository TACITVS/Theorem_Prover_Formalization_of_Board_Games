# Formal Verification Roadmap: Solved Combinatorial Games & Open Unsolved Frontiers

[![Back to Main Landing Page](https://img.shields.io/badge/⬅_Back_to_Main_Page-README.md-2563eb?style=for-the-badge)](README.md)
[![Rocq 9.1 Verified](https://img.shields.io/badge/Rocq_9.1-57_Theorems_Closed-22c55e?style=for-the-badge)](build.ps1)
[![Lean 4.35.0 Verified](https://img.shields.io/badge/Lean_4.35.0-26_Theorems_0_sorry-10b981?style=for-the-badge)](build_lean.ps1)
[![Connect-5 8x7 Repository](https://img.shields.io/badge/🎲_Connect--5_8x7-Repository-blue?style=for-the-badge)](https://github.com/TACITVS/8x7_Connect_5_Is_A_Proven_Fair_Game)

> **Abstract:** Between 1980 and 2026, computer scientists and combinatorial game theorists resolved the exact game-theoretic values of over a dozen classic board games. However, virtually **every single one of these historic solutions relies on unverified C/C++ code, ad-hoc retrograde databases, or proprietary mainframe scripts**.
>
> Following our complete machine-checked formal proof of **8x7 Connect-5 (`game_value = Draw`)** and **Nine Men's Morris (`game_value = Draw`)**, this document provides a comprehensive scientific catalog and execution roadmap of both **famous solved board games awaiting machine proof** and **unsolved classic games whose game-theoretic fairness is unknown**.

---

## 1. Summary Catalog of Solved Board Games Awaiting Formal Verification

| Board Game | Dimensions / State Space | Game-Theoretic Value | Original Computational Solver | Formal Theorem Prover Status | Core Mathematical Structure |
| :--- | :---: | :---: | :--- | :---: | :--- |
| **Nine Men's Morris (Mill)** | 24 points (10^10 states) | **Exact Draw** | Ralph Gasser (1993, ETH Zurich) | ✅ **VERIFIED (Rocq 9.1 & Lean 4)** | 3-Phase DAG, D4 Dihedral Symmetry, 8-Stone Transversal Barrier |
| **Classic Connect-Four** | 7x6 grid (4.53 x 10^12) | **Win White (P1)** | Allen (1988), Allis (1988), Tromp (1995) | ❌ **Unverified** | Claimeven (57/69 lines), Center Column 3 Pigeonhole, Odd-Threat Zugzwang |
| **Even-Height Connect-Four** | 6x6, 8x6, 8x8 | **Win Black (P2)** | John Tromp (1995–2015) | ❌ **Unverified** | Parity Inversion, Strong Domino Traps, Zugzwang Exploitation |
| **Qubic (3D Connect-Four)** | 4x4x4 (10^13 states) | **Win White (P1)** | Patashnik (1980), Allis (1994) | ❌ **Unverified** | 64-Bit Exact Hardware Saturation, 76 Winning Lines, VCF/VCT Search |
| **Quarto** | 4x4 grid (16 pieces) | **Exact Draw** | Luc Goossens (1998) | ❌ **Unverified** | (Z_2)^4 Affine Hypercube Symmetry, Lean 4 Quotient Types |
| **Pentago** | 6x6 (4 rotating quadrants) | **Win White (P1)** | Geoffrey Irving (2014) | ❌ **Unverified** | D4 Symmetries + 90-degree Quadrant Rotations, Retrograde Databases |
| **Freestyle Gomoku** | 15x15 (10^105 states) | **Win White (P1)** | Victor Allis (1993 PhD Thesis) | ❌ **Unverified** | Inductive Threat-Space Search (VCF / VCT), Proof-Number Search |
| **Hex (7x7 and 8x8)** | 49 and 64 cells | **Win White (P1)** | Hayward, Henderson et al. (2002) | ❌ **Unverified** | Virtual Connection H-Search, Resistance Networks, Carrier Sets |
| **Chomp (3xn and nxn)** | Arbitrary rectangular grid | **Win White (P1)** | David Gale (1974), Zeilberger (2001) | ❌ **Unverified** | Poset Ideal Games, Constructive Winning First-Move Formulas |
| **Domineering (6x6 and 8x8)** | Grid tiling by 2x1 dominoes | **Partisan Values** | Conway (1976), Bullock (2002) | ❌ **Unverified** | Combinatorial Game Theory, Surreal Numbers, Dyadic Rational Values |

---

## 2. Unsolved Frontiers: Games Whose Fairness Is Mathematically Unknown

| Game Frontier | Dimensions / Complexity | Suspected / Conjectured Value | Core Unsolved Mathematical Question |
| :--- | :---: | :---: | :--- |
| **Twelve Men's Morris** | 24 points, 20 mills (4 diagonals), 12 stones | **UNKNOWN (Draw vs. Win White)** | Does adding 4 diagonal corner mills destroy the 8-stone transversal barrier and allow White to force a win? |
| **Dots and Boxes (5x5 Dots)** | 16 Boxes, 40 Edges | **Conjectured Exact Draw (8–8)** | Famous Conway/Berlekamp open problem: even box parity permits an 8–8 draw, but optimal strategy is unproven. |
| **Connect-5 Critical Threshold** | 8x8 and 9x7 with gravity | **UNKNOWN (Draw vs. Win White)** | At what exact grid size (w, h) does gravity Connect-5 transition from a Claimeven Draw to a First-Player Win? |
| **Connect6 Critical Threshold** | 7x7, 8x8, 9x9 grids | **UNKNOWN Boundary** | Designed by I-Chen Wu (2005) for fairness; the critical board size where first-mover advantage forces a win is open. |
| **Russian Checkers (Shashki)** | 8x8, flying kings, backward captures | **Conjectured Exact Draw** | English draughts is solved (Draw); Russian checkers with flying kings has never been computationally exhausted. |

---

## 3. Active Next Project: Twelve Men's Morris

We select **Twelve Men's Morris** as our immediate next formal investigation. It directly extends our 24-point concentric graph from Nine Men's Morris by adding:
1. **4 Diagonal Mills:** Across the 4 corners: NW (0, 8, 16), NE (2, 10, 18), SE (4, 12, 20), SW (6, 14, 22), bringing total mills from 16 to 20.
2. **12 Stones Per Player:** In Phase 1, 24 plies are played, allowing the board to become completely saturated (24/24 points occupied).
3. **Broken Regularity:** Corner mill degrees increase to 3, while midpoints remain 2, testing whether White can force a win or Black can maintain a draw barrier.
