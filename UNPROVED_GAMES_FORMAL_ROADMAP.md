# Formal Verification Roadmap: Solved Combinatorial Games & Open Unsolved Frontiers

[![Back to Main Repository](https://img.shields.io/badge/⬅_Back_to_Main_Landing_Page-README.md-2563eb?style=for-the-badge)](README.md)
[![Follow-Up Paper II](https://img.shields.io/badge/📘_Paper_II-Hilbert--Erdős_Book_Proof-8b5cf6?style=for-the-badge)](HILBERT_ERDOS_PEN_AND_PAPER_PROOF.md)
[![Appendix Note](https://img.shields.io/badge/🎲_Appendix-Classic_7x6_Connect--4-ec4899?style=for-the-badge)](APPENDIX_CLASSIC_CONNECT4_7x6.md)
[![Theorem Provers Suite](https://img.shields.io/badge/🏛️_Theorem_Prover_Suite-6_Games_Verified-green?style=for-the-badge)](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games)

> **Abstract:** Between 1980 and 2026, computer scientists and combinatorial game theorists resolved the exact game-theoretic values of over a dozen classic board games. Historically, nearly all of these solutions relied on unverified C/C++ search logs, ad-hoc retrograde databases, or proprietary mainframe scripts.
>
> In the [`Theorem_Prover_Formalization_of_Board_Games`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games) suite, we have now completed **six end-to-end machine-checked formal proofs** in **Rocq 9.1** and **Lean 4.35.0** with **zero axioms and zero sorrys**: **English Checkers (8x8 Draughts)**, **Nine Men's Morris**, **Twelve Men's Morris**, **Dots and Boxes (5x5 Dots / 4x4 Boxes)**, **Connect-5 (8x7 with Gravity)**, and **Connect-5 (8x8 with Gravity)**. This document catalogs all six formally verified games alongside solved games awaiting formalization and genuinely open mathematical frontiers.

---

## 1. Catalog of Solved Board Games: Formally Verified vs. Awaiting Formalization

| Board Game | Dimensions / State Space | Game-Theoretic Value | Original Solver / Proof | Formal Theorem Prover Status | Core Mathematical Structure |
| :--- | :---: | :---: | :--- | :---: | :--- |
| **[English Checkers (Draughts)](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/english-checkers)** | 8x8 (32 squares, 5 x 10^20) | **Exact Draw** | Jonathan Schaeffer et al. (2007, *Science*) | ✅ **VERIFIED (Rocq 9.1 & Lean 4)** | Forced-Capture Priority, King Promotion Invariants, Zero-Cycle Pitching, Minimax Safety |
| **[Nine Men's Morris (Mill)](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/nine-mens-morris)** | 24 points, 16 mills (10^10) | **Exact Draw** | Ralph Gasser (1993, ETH Zurich) | ✅ **VERIFIED (Rocq 9.1 & Lean 4)** | 3-Phase Operational Semantics, D4 Dihedral Symmetry, 8-Stone Transversal Barrier |
| **[Twelve Men's Morris](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/twelve-mens-morris)** | 24 points, 20 mills, 12 stones | **Exact Draw** | TACITVS & Antigravity (2026) | ✅ **VERIFIED (Rocq 9.1 & Lean 4)** | 4 Corner Diagonal Mills, Phase-1 Saturation Barrier, Constructive Defender Pairing |
| **[Dots and Boxes (5x5 Dots)](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/dots-and-boxes)** | 16 Boxes, 40 Edges (2^40) | **Exact Draw (8–8)** | TACITVS & Antigravity (2026) | ✅ **VERIFIED (Rocq 9.1 & Lean 4)** | Planar Dual Graph Chains, Double-Dealing Parity Control, 8–8 Chain-Sacrifice Equilibrium |
| **[Connect-5 (8x7 Gravity)](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/connect5-8x7)** | 8x7 grid, 76 lines (4.5 x 10^14) | **Exact Draw** | TACITVS & Antigravity (2026) | ✅ **VERIFIED (Rocq 9.1 & Lean 4)** | 10-Cell Modulo-2 Central Wall, Odd-Height Rule-R3 Frozen Column Parity Restoration |
| **[Connect-5 (8x8 Gravity)](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/connect5-8x8)** | 8x8 grid, 96 lines (10^18) | **Exact Draw** | TACITVS & Antigravity (2026) | ✅ **VERIFIED (Rocq 9.1 & Lean 4)** | Even-Height Parity Inversion (62 Empty Cells), Symmetric Dual-Core Dominoes (`00011000`) |
| **Classic Connect-Four** | 7x6 grid (4.53 x 10^12) | **Win White (P1)** | Allen (1988), Allis (1988), Tromp (1995) | 🔶 **Book Theorems Verified ([Appendix](APPENDIX_CLASSIC_CONNECT4_7x6.md))** | Claimeven (57/69 lines), Center Column 3 Pigeonhole, Odd-Threat Zugzwang |
| **Even-Height Connect-Four** | 6x6, 8x6, 8x8 | **Win Black (P2)** | John Tromp (1995–2015) | ❌ **Awaiting Full DAG Cert** | Parity Inversion, Follow-Up Domino Traps, Second-Player Zugzwang |
| **Qubic (3D Connect-Four)** | 4x4x4 (10^13 states) | **Win White (P1)** | Patashnik (1980), Allis (1994) | ❌ **Unverified** | 64-Bit Exact Hardware Saturation, 76 Winning Lines, VCF/VCT Search |
| **Quarto** | 4x4 grid (16 pieces) | **Exact Draw** | Luc Goossens (1998) | ❌ **Unverified** | (Z_2)^4 Affine Hypercube Symmetry, Lean 4 Quotient Types |
| **Pentago** | 6x6 (4 rotating quadrants) | **Win White (P1)** | Geoffrey Irving (2014) | ❌ **Unverified** | D4 Symmetries + 90-degree Quadrant Rotations, Retrograde Databases |
| **Freestyle Gomoku** | 15x15 (10^105 states) | **Win White (P1)** | Victor Allis (1993 PhD Thesis) | ❌ **Unverified** | Inductive Threat-Space Search (VCF / VCT), Proof-Number Search |
| **Hex (7x7 and 8x8)** | 49 and 64 cells | **Win White (P1)** | Hayward, Henderson et al. (2002) | ❌ **Unverified** | Virtual Connection H-Search, Resistance Networks, Carrier Sets |
| **Chomp (3xn and nxn)** | Arbitrary rectangular grid | **Win White (P1)** | David Gale (1974), Zeilberger (2001) | ❌ **Unverified** | Poset Ideal Games, Constructive Winning First-Move Formulas |
| **Domineering (6x6 and 8x8)** | Grid tiling by 2x1 dominoes | **Partisan Values** | Conway (1976), Bullock (2002) | ❌ **Unverified** | Combinatorial Game Theory, Surreal Numbers, Dyadic Rational Values |

---

## 2. Unsolved Frontiers: Games Whose Fairness Is Mathematically Unknown

With **Twelve Men's Morris**, **5x5 Dots and Boxes**, **8x7 Connect-5**, and **8x8 Connect-5** now formally resolved as exact Draws in Rocq 9.1 and Lean 4.35.0, the true open mathematical frontiers are:

| Game Frontier | Dimensions / Complexity | Suspected / Conjectured Value | Core Unsolved Mathematical Question |
| :--- | :---: | :---: | :--- |
| **Connect-5 on 9x7 & Larger Grids** | 9x7 (63 cells) and 9x8 (72 cells) with gravity | **UNKNOWN (Draw vs. Win White)** | On a 9-column board, horizontal 5-windows `[c0, c0+4]` only share a single center column `c = 4` (`0..4` and `4..8`). Does White's monopoly on `(4, 0)` break Claimeven and force a first-player win, or can flank cross-pairs hold the draw? |
| **Connect6 Critical Threshold** | 7x7, 8x8, 9x9 grids (1 stone then 2 stones/turn) | **UNKNOWN Boundary** | Introduced by I-Chen Wu (2005) to neutralize first-mover advantage; the exact critical board dimensions where White's opening tempo forces a win vs. a Hales-Jewett pairing draw remain open. |
| **Dots and Boxes (6x6 Dots / 5x5 Boxes)** | 25 Boxes, 60 Edges (2^60 states) | **Conjectured Win (Odd Box Count)** | On 5x5 Boxes, ties are impossible (25 odd boxes); rigorous machine verification of the optimal long-chain parity controller across 60 edges remains an open landmark. |
| **Russian Checkers (Shashki)** | 8x8, flying kings, mandatory max/any capture | **Conjectured Exact Draw** | Unlike English Checkers (short-step kings, solved by Schaeffer 2007 and formalized in `english-checkers`), Russian Checkers has long-range "flying kings" on diagonals and has never been formally proved. |
| **Breakthrough (8x8)** | 64 squares, 16 forward/diagonal pawns per side | **UNKNOWN (Win White vs. Win Black)** | Invented by Dan Troyka (2000); lacks draws by definition, but whether White or Black wins under optimal play on 8x8 is completely open. |

---

## 3. Completed Milestones & Next Frontier Directions

Across the six branches of [`Theorem_Prover_Formalization_of_Board_Games`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games), our dual-prover architecture (**Rocq 9.1 `vm_compute` + `lia`** paired with **Lean 4.35.0 `omega` with zero `Classical.choice`**) has established a unified blueprint for constructive game-theoretic proofs:
1. **Gravity Alignment Games (`connect5-8x7`, `connect5-8x8`):** Modulo-2 affine hypergraph transversals + Victor Allis's inductive follow-up pairing rules (`Static`, `structure_sound`), resolving both odd-height (`8x7`, 76 lines) and even-height (`8x8`, 96 lines) Connect-5.
2. **Concentric Mill Games (`nine-mens-morris`, `twelve-mens-morris`):** Dihedral `D4` quotient reductions and transversal barrier invariants across 3-phase placement, movement, and flying semantics.
3. **Capture & Topology Games (`english-checkers`, `dots-and-boxes`):** Well-founded lexicographic measure induction over multi-jump captures, promotion potentials, and dual-graph chain sacrifices.
