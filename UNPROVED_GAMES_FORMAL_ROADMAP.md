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
| **Dots and Boxes ($5 \times 5$ Dots)** | $16$ boxes, $40$ edges | **Exact Draw ($8 - 8$)** | Wilson (1995), Barker & Korf (2012) | ✅ **VERIFIED (Rocq 9.1 & Lean 4)** | Dual 4-Regularity, Net Tempo Surplus $e_0 - e_2 = 24$, Berlekamp Sacrifice |
| **Domineering ($6 \times 6$ and $8 \times 8$)** | Grid tiling by $2 \times 1$ dominoes | **Partisan Values** | Conway (1976), Bullock (2002) | ❌ **Unverified** | Combinatorial Game Theory, Surreal Numbers, Dyadic Rational Values |

---

## 2. Unsolved Frontiers: Games Whose Fairness Is Mathematically Unknown

| [ID] | Game Frontier | Dimensions / State Space | Conjectured / Suspected Value | Core Unsolved Mathematical Question | Key Mathematical Structures |
| :---: | :--- | :---: | :---: | :--- | :--- |
| **[01]** | **Connect-5 Critical Boundary** | $8 \times 8$ and $9 \times 7$ Gravity Grids | **UNKNOWN (Draw vs. Win White)** | At what exact grid size $(w, h)$ does gravity Connect-5 transition from a Claimeven Draw to a First-Player Win? | Claimeven Domino Couplings, Parity Breaking, Potential Functions |
| **[02]** | **Connect6 Critical Threshold** | $7 \times 7$, $8 \times 8$, $9 \times 9$ Grids | **UNKNOWN Boundary** | Designed by I-Chen Wu (2005) for fairness (2 stones/turn); what is the minimal board size where P1 can force a win? | 2-Stone Threat Dynamics, Double-Threat Disjunctions, Matroid Theory |
| **[03]** | **Russian Checkers (Shashki)** | $8 \times 8$ ($32$ active squares) | **Conjectured Exact Draw** | English draughts is solved (Draw); do flying kings and mandatory backward captures preserve an exact draw? | Diagonals Homology, Flying King Mobility, Backward Capture Transversals |
| **[04]** | **Havannah** | Base sizes $4, 5, 6$ Hexagonal Board | **UNKNOWN (Draw vs. Win White)** | Can White force a Ring, Bridge, or Fork on small boards, or do three winning topological paths force a Draw? | Hexagonal Topology, Cycle Ring Detection, 6-Corner Graph Diameter |
| **[05]** | **Breakthrough** | $8 \times 8$ Grid ($32$ pieces) | **UNKNOWN (Win White vs. Win Black)** | Invented by Dan Troyka (2000); which player has the forced breakthrough race victory on standard boards? | Forward Infiltration Cones, Capture Invariants, Distance Monotonicity |
| **[06]** | **Ataxx** | $7 \times 7$ Grid ($49$ squares) | **UNKNOWN (Draw vs. Win P1/P2)** | Does the cloning (dist 1) vs. jumping (dist 2) infection mechanic yield an exact draw or a decisive win? | Voronoi Infection Dynamics, Clonal Growth Thresholds, Parity Invariants |
| **[07]** | **Lines of Action (LOA)** | $8 \times 8$ Grid ($24$ pieces) | **UNKNOWN (Draw vs. Win White)** | Claude Soucie's 1969 classic: can White force a connected group via line-of-sight piece counts? | Connected Component Invariants, Line Density Conservation, Spectral Graph Bounds |
| **[08]** | **Cram (Impartial Dominoes)** | Odd $\times$ Odd ($5 \times 5, 7 \times 7$) | **UNKNOWN (Win P1 vs. Win P2)** | Impartial $2 \times 1$ tiling; even boards are solved by symmetry, but odd $\times$ odd boards remain open. | Sprague-Grundy Nim-Values, Bipartite Matching Invariants, Symmetry Breaking |
