# Formal Mathematical Verification of Classical Board Games

[![Rocq 9.1 Verified](https://img.shields.io/badge/Rocq_9.1-Zero_Axioms_Closed-22c55e?style=for-the-badge)](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/main)
[![Lean 4.35.0 Verified](https://img.shields.io/badge/Lean_4.35.0-Zero_Sorrys_Kernel_Only-10b981?style=for-the-badge)](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/main)
[![C11 Verification Engines](https://img.shields.io/badge/C11_Engines-1.6_Billion_Evals%2Fsec-blue?style=for-the-badge)](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/main)
[![Exhaustive Transversal Audit](https://img.shields.io/badge/Audit_Verification-1.27_Million_Subsets_Checked-indigo?style=for-the-badge)](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/twelve-mens-morris)
[![License: MIT](https://img.shields.io/badge/License-MIT-purple?style=for-the-badge)](LICENSE)

> **Abstract:** For over half a century, combinatorial game theorists and computer scientists solved the game-theoretic values of historic board games — Connect-Four, Nine Men's Morris, Qubic, Gomoku, Pentago, and Hex. However, virtually every one of these landmark results relied entirely on **unverified C/C++ scripts, ad-hoc retrograde databases, or proprietary mainframe executions** that were never mathematically audited.
>
> This repository is the **first multi-prover, zero-axiom mathematical verification hub for board games**, formalizing their complete graph topologies, algebraic symmetries, operational semantics, and game-theoretic certificates inside **Rocq 9.1** and **Lean 4.35.0**.

---

## 🧭 Branch Architecture

To maintain modularity, reproducibility, and rigorous proof checking, **each board game formalization is developed, maintained, and audited in its own dedicated git branch**:

| Branch | Board Game | Formal Provers | Game-Theoretic Status | Key Mathematical Breakthroughs |
| :--- | :--- | :---: | :---: | :--- |
| [`nine-mens-morris`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/nine-mens-morris) | **Nine Men's Morris (Mill)** | Rocq 9.1 & Lean 4.35.0 | **Exact Draw** | Uniform Mill Regularity, 16-Vertex Cubic Dual Graph, 8-Stone Transversal Barrier (tau = 8), 768-Ply Zermelo Finite Horizon |
| [`twelve-mens-morris`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/twelve-mens-morris) | **Twelve Men's Morris (Morabaraba)** | Rocq 9.1 & Lean 4.35.0 | **Active Open Frontier** | 20 Mills (4 Diagonals), 40 Edges, Broken Mill Regularity, 8-Stone Transversal Barrier, +4 Defensive Surplus Law |
| [`connect5-8x7`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/connect5-8x7) | **Connect-5 on 8x7 Board with Gravity** | Rocq 9.1 | **Exact Draw** | Victor Allis Follow-Up Pairing Theory, Well-Founded Induction, Claimeven Parity Invariants, Mutual Safety Duality |
| [`dots-and-boxes-5x5`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/dots-and-boxes-5x5) *(Roadmap)* | **Dots and Boxes (5x5 Dots, 16 Boxes)** | Rocq 9.1 & Lean 4.35.0 | **Conjectured 8–8 Draw** | Berlekamp Long-Chain Exploitation, Conway Nimstring Reductions, 40-Edge Graph Topology |

---

## 🏛️ Flagship Formalizations Overview

### 1. Nine Men's Morris (Branch: [`nine-mens-morris`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/nine-mens-morris))

One of humanity's oldest strategy games (dating to Kurna, Egypt, c. 1400 BC). Computationally solved by Ralph Gasser (1993, ETH Zurich) as an **Exact Draw**.

```
                      Nine Men's Morris Planar Board Graph
  
    NW(0) ═══════════════════════ N(1) ═══════════════════════ NE(2)
      ║                             ║                             ║
      ║     NW(8) ═══════════════ N(9) ═══════════════ NE(10)     ║
      ║       ║                     ║                     ║       ║
      ║       ║     16 ════════════ 17 ════════════ 18    ║       ║
      ║       ║      ║                             ║      ║       ║
    W(7) ═══ W(15) ═ 23                           19 ═ E(11) ═══ E(3)
      ║       ║      ║                             ║      ║       ║
      ║       ║     22 ════════════ 21 ════════════ 20    ║       ║
      ║       ║                     ║                     ║       ║
      ║     SW(14) ══════════════ S(13) ══════════════ SE(12)     ║
      ║                             ║                             ║
    SW(6) ═══════════════════════ S(5) ═══════════════════════ SE(4)
```

- **Mill Regularity Theorem:** Every vertex belongs to **strictly 2 mills** (`16 × 3 = 48 = 24 × 2`).
- **Cubic Dual Graph:** The mill incidence structure forms a **3-regular cubic graph on 16 vertices** with 24 edges.
- **8-Stone Transversal Barrier Theorem (`tau(H) = 8`):** Any player occupying a canonical 8-stone transversal set (e.g., `{1, 3, 5, 7, 8, 12, 16, 20}`) intersects **ALL 16 MILLS**, completely barring the opponent from forming any mill during Phase 1.
- **Finite Horizon Monotonicity:** Maximum 14 captures, with a 768-ply global game horizon under the 50-move rule, guaranteeing Zermelo minimax determinacy.
- **Proof Count:** 74 Theorems in Rocq 9.1 (`Closed under the global context`) and 33 Theorems in Lean 4.35.0 (0 sorrys, approved kernel axioms only).

---

### 2. Twelve Men's Morris (Branch: [`twelve-mens-morris`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/twelve-mens-morris))

Twelve Men's Morris adds **4 diagonal mills** across the corners: NW (0-8-16), NE (2-10-18), SE (4-12-20), SW (6-14-22), bringing total mills to 20 and undirected edges to 40.

```
                  Twelve Men's Morris (with 4 Diagonals)
  
    NW(0) ═══════════════════════ N(1) ═══════════════════════ NE(2)
      ║ ╲                           ║                           ╱ ║
      ║   NW(8) ═════════════════ N(9) ═════════════════ NE(10)   ║
      ║     ║ ╲                     ║                     ╱ ║     ║
      ║     ║   16 ═══════════════ 17 ═══════════════ 18    ║     ║
      ║     ║    ║                                     ║    ║     ║
    W(7) ═ W(15) 23                                   19 ═ E(11)  E(3)
      ║     ║    ║                                     ║    ║     ║
      ║     ║   22 ═══════════════ 21 ═══════════════ 20    ║     ║
      ║     ║ ╱                     ║                     ╲ ║     ║
      ║   SW(14) ════════════════ S(13) ════════════════ SE(12)   ║
      ║ ╱                           ║                           ╲ ║
    SW(6) ═══════════════════════ S(5) ═══════════════════════ SE(4)
```

- **Broken Regularity Theorem:**
  - 12 Corners have mill degree 3 (2 concentric ring mills + 1 diagonal mill).
  - 12 Midpoints have mill degree 2 (1 concentric ring mill + 1 radial mill).
  - Mill Incidence Handshake: `12 × 3 + 12 × 2 = 60 = 20 × 3`.
- **40-Edge Graph Handshake:** Middle ring vertices have degree 4; outer and inner have degree 3 (`8 × 4 + 16 × 3 = 80 = 2 × 40`).
- **The 8-Stone Transversal Invariant:** Despite 4 additional diagonal mills, the transversal number remains **EXACTLY 8**! Canonical set `{1, 3, 5, 7, 10, 14, 16, 20}` intersects all 20 mills.
- **The +4 Defensive Surplus Law:** Each player places 12 stones. Because `12 - 8 = +4`, the defending player has **4 surplus stones** of freedom, strongly supporting the conjecture that Twelve Men's Morris is a drawn game.
- **Exhaustive Subset Audit:** Verified across all 536,154 subsets of size 7 or smaller (strictly 0 transversals) and all 735,471 subsets of size 8 (strictly 18 minimal transversals covering all 20 mills).
- **Proof Count:** Dual-formalized in Rocq 9.1 and Lean 4.35.0 (48 Lean theorems audited).

---

### 3. Connect-5 on 8x7 Board with Gravity (Branch: [`connect5-8x7`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/connect5-8x7))

Connect-5 on an 8x7 grid with standard gravity. Formalizes Victor Allis's pairing strategies to deductively prove `game_value = Draw`.

- **Even Width 8 Symmetry:** Even column width allows complete vertical domino decomposition and cross-column symmetric couplings.
- **Follow-Up Soundness:** Inductive proof by well-founded induction on empty cells guaranteeing defender non-losing invariant.
- **Claimeven Parity Invariants:** Attacker can never claim both cells of any defensive domino or paired base threat.
- **Verified Certificate:** Minimax strategy tree audited in Rocq 9.1 with zero unproven axioms.

---

## 🔬 Rigorous Verification Guarantees

Every formal mathematical theorem in this project obeys strict verification guidelines:

1. **Zero Unproven Axioms in Rocq 9.1:**
   - Every theorem must report `Closed under the global context` when audited with `Print Assumptions`.
   - Zero `admit`, zero `Axiom`, zero unproven conjectures.
2. **Kernel Axioms Only in Lean 4.35.0:**
   - Every declaration is audited with `#print axioms`.
   - Zero `sorry`, zero custom axioms, zero `Classical.choice`.
   - The axiom allowlist is strictly limited to standard kernel axioms: `[propext, Quot.sound]`.
3. **High-Performance Verification Engines:**
   - C11 bitboard engines achieving 1.0 to 1.6 Billion position evaluations per second on commodity hardware.
   - Exact exhaustive state and transversal verification suites.

---

## 🚀 Quick Start Guide

### Clone and Checkout Specific Game Branches

```bash
# Clone the repository
git clone https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games.git
cd Theorem_Prover_Formalization_of_Board_Games

# Inspect Nine Men's Morris proof suite
git checkout nine-mens-morris
powershell -ExecutionPolicy Bypass -File build.ps1
powershell -ExecutionPolicy Bypass -File build_lean.ps1

# Inspect Twelve Men's Morris proof suite
git checkout twelve-mens-morris
powershell -ExecutionPolicy Bypass -File build.ps1
powershell -ExecutionPolicy Bypass -File build_lean.ps1

# Inspect Connect-5 8x7 proof suite
git checkout connect5-8x7
powershell -ExecutionPolicy Bypass -File build.ps1
```

---

## 🗺️ Long-Term Roadmap: Solved Games & Open Frontiers

See [`UNPROVED_GAMES_FORMAL_ROADMAP.md`](UNPROVED_GAMES_FORMAL_ROADMAP.md) for the full scientific roadmap covering:
- Classic Connect-Four (7x6, Win White)
- Even-Height Connect-Four (6x6, 8x6, 8x8, Win Black)
- Qubic 4x4x4 (Win White)
- Quarto 4x4 (Exact Draw)
- Pentago 6x6 (Win White)
- Freestyle Gomoku 15x15 (Win White)
- Hex (7x7, 8x8)
- 5x5 Dots and Boxes (Conjectured 8–8 Draw)
- Russian Checkers (Shashki)

---

## 📄 License

This project is licensed under the [MIT License](LICENSE).
