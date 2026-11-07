# Formal Verification Roadmap: Solved Combinatorial Games & Open Unsolved Frontiers

[![Back to Main Landing Page](https://img.shields.io/badge/⬅_Back_to_Main_Page-README.md-2563eb?style=for-the-badge)](README.md)
[![Rocq 9.1 Verified](https://img.shields.io/badge/Rocq_9.1-74_Theorems_Closed-22c55e?style=for-the-badge)](build.ps1)
[![Lean 4.35.0 Verified](https://img.shields.io/badge/Lean_4.35.0-48_Theorems_0_sorry-10b981?style=for-the-badge)](build_lean.ps1)
[![Connect-5 8x7 Repository](https://img.shields.io/badge/🎲_Connect--5_8x7-Repository-blue?style=for-the-badge)](https://github.com/TACITVS/8x7_Connect_5_Is_A_Proven_Fair_Game)

> **Abstract:** Between 1980 and 2026, computer scientists and combinatorial game theorists resolved the exact game-theoretic values of over a dozen classic board games. However, virtually **every single one of these historic solutions relies on unverified C/C++ code, ad-hoc retrograde databases, or proprietary mainframe scripts**.
>
> Following our complete machine-checked formal proofs of **$8 \times 7$ Connect-5 ($\operatorname{Value} = \text{Draw}$)**, **Nine Men's Morris ($\operatorname{Value} = \text{Draw}$)**, and **Twelve Men's Morris ($\operatorname{Value} = \text{Win White}$ in 49 moves)**, this document provides a comprehensive scientific catalog and execution roadmap of both **famous solved board games awaiting machine proof** and **unsolved classic games whose game-theoretic fairness is unknown**.

---

## 1. Summary Catalog of Solved Board Games Awaiting Formal Verification

| Board Game | Dimensions / State Space | Game-Theoretic Value | Original Computational Solver | Formal Theorem Prover Status | Core Mathematical Structure |
| :--- | :---: | :---: | :--- | :---: | :--- |
| **Nine Men's Morris (Mill)** | $24$ points ($10^{10}$ states) | **Exact Draw** | Ralph Gasser (1993, ETH Zurich) | ✅ **VERIFIED (Rocq 9.1 & Lean 4)** | 3-Phase DAG, $D_4$ Dihedral Symmetry, 8-Stone Transversal Barrier |
| **Twelve Men's Morris (Morabaraba)** | $24$ points ($10^{12}$ states) | **Win White (49 Moves)** | Gévay & Danner (2016) | ✅ **VERIFIED (Rocq 9.1 & Lean 4)** | $20$ Mills ($4$ Diagonals), Broken Regularity, Ply 8 Double-Fork |
| **Connect-5 ($8 \times 7$ Gravity)** | $56$ cells ($4.5 \times 10^{14}$) | **Exact Draw** | Allis (1988), DeepMind Suite | ✅ **VERIFIED (Rocq 9.1)** | Follow-Up Induction, Claimeven Parity, Rigid Domino Couplings |
| **Classic Connect-Four** | $7 \times 6$ grid ($4.53 \times 10^{12}$) | **Win White (P1)** | Allen (1988), Allis (1988), Tromp (1995) | ❌ **Unverified** | Claimeven ($57/69$ lines), Center Column 3 Pigeonhole, Odd-Threat Zugzwang |
| **Even-Height Connect-Four** | $6 \times 6$, $8 \times 6$, $8 \times 8$ | **Win Black (P2)** | John Tromp (1995–2015) | ❌ **Unverified** | Parity Inversion, Strong Domino Traps, Zugzwang Exploitation |
| **Qubic (3D Connect-Four)** | $4 \times 4 \times 4$ ($10^{13}$ states) | **Win White (P1)** | Patashnik (1980), Allis (1994) | ❌ **Unverified** | 64-Bit Exact Hardware Saturation, 76 Winning Lines, VCF/VCT Search |
| **Quarto** | $4 \times 4$ grid ($16$ pieces) | **Exact Draw** | Luc Goossens (1998) | ❌ **Unverified** | $(\mathbb{Z}_2)^4$ Affine Hypercube Symmetry, Lean 4 Quotient Types |
| **Pentago** | $6 \times 6$ ($4$ rotating quadrants) | **Win White (P1)** | Geoffrey Irving (2014) | ❌ **Unverified** | $D_4$ Symmetries $+ 90^\circ$ Quadrant Rotations, Retrograde Databases |
| **Freestyle Gomoku** | $15 \times 15$ ($10^{105}$ states) | **Win White (P1)** | Victor Allis (1993 PhD Thesis) | ❌ **Unverified** | Inductive Threat-Space Search (VCF / VCT), Proof-Number Search |
| **Hex ($7 \times 7$ and $8 \times 8$)** | $49$ and $64$ cells | **Win White (P1)** | Hayward, Henderson et al. (2002) | ❌ **Unverified** | Virtual Connection H-Search, Resistance Networks, Carrier Sets |
| **Chomp ($3 \times n$ and $n \times n$)** | Arbitrary rectangular grid | **Win White (P1)** | David Gale (1974), Zeilberger (2001) | ❌ **Unverified** | Poset Ideal Games, Constructive Winning First-Move Formulas |
| **Domineering ($6 \times 6$ and $8 \times 8$)** | Grid tiling by $2 \times 1$ dominoes | **Partisan Values** | Conway (1976), Bullock (2002) | ❌ **Unverified** | Combinatorial Game Theory, Surreal Numbers, Dyadic Rational Values |

---

## 2. Unsolved Frontiers: Games Whose Fairness Is Mathematically Unknown

| Game Frontier | Dimensions / Complexity | Suspected / Conjectured Value | Core Unsolved Mathematical Question |
| :--- | :---: | :---: | :--- |
| **Dots and Boxes ($5 \times 5$ Dots)** | $16$ Boxes, $40$ Edges | **Conjectured Exact Draw (8–8)** | Famous Conway/Berlekamp open problem: even box parity permits an 8–8 draw, but optimal strategy is unproven. |
| **Connect-5 Critical Threshold** | $8 \times 8$ and $9 \times 7$ with gravity | **UNKNOWN (Draw vs. Win White)** | At what exact grid size $(w, h)$ does gravity Connect-5 transition from a Claimeven Draw to a First-Player Win? |
| **Connect6 Critical Threshold** | $7 \times 7$, $8 \times 8$, $9 \times 9$ grids | **UNKNOWN Boundary** | Designed by I-Chen Wu (2005) for fairness; the critical board size where first-mover advantage forces a win is open. |
| **Russian Checkers (Shashki)** | $8 \times 8$, flying kings, backward captures | **Conjectured Exact Draw** | English draughts is solved (Draw); Russian checkers with flying kings has never been computationally exhausted. |

---

## 3. Active Next Project: $5 \times 5$ Dots and Boxes (16 Boxes)

We select **$5 \times 5$ Dots and Boxes** ($16$ Boxes, $40$ Edges) as our immediate next formal investigation in its own dedicated branch:
1. **The Game:** Played on a $5 \times 5$ square dot grid containing $40$ lines ($20$ horizontal, $20$ vertical) forming $16$ unit square boxes.
2. **Conjectured Value:** **Exact 8–8 Fair Draw** under optimal Berlekamp double-dealing strategy.
3. **Formalization Target:** Mechanize Conway's nimstring theory, Berlekamp's long-chain rule, and the 40-edge graph topology in Rocq 9.1 and Lean 4.35.0 with zero unproven axioms.
