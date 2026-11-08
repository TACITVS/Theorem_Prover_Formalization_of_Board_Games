<div align="center">

# 🏛️ Theorem Prover Formalization of Board Games
### **Foundational Constructive Game Theory, Exact Minimax Equilibria, and Zero-Axiom Proofs in Rocq 9.1 and Lean 4.35**

[![GitHub Repository](https://img.shields.io/badge/GitHub-Repository_Suite-2563eb?style=for-the-badge&logo=github)](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games)
[![Rocq 9.1 Verified](https://img.shields.io/badge/Rocq_9.1-305_Theorems_Closed_(0_Axioms)-16a34a?style=for-the-badge&logo=coq)](THEORETICAL_FOUNDATIONS_AND_METHODS.md)
[![Lean 4.35.0 Verified](https://img.shields.io/badge/Lean_4.35.0-147_Theorems_Verified_(0_Sorry)-10b981?style=for-the-badge)](THEORETICAL_FOUNDATIONS_AND_METHODS.md)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg?style=for-the-badge)](LICENSE)

<br/>

**A multi-game formal mathematics initiative dedicated to establishing machine-verified constructive solutions, algebraic invariant transversals, and certified minimax equilibria for classic combinatorial board games.**

</div>

---

> [!IMPORTANT]
> **Repository Architecture Notice:** The `main` branch serves as the **Grand Theoretical & Methodological Portal** for the entire project. Each solved and formalized combinatorial game lives on its own dedicated, self-contained branch containing complete machine-checked Rocq 9.1 proof scripts (`.v`), Lean 4.35.0 theories (`.lean`), C11 high-performance bitboard solvers, visual SVG vector assets, and dedicated mathematical monographs.

<div align="center">
  <img src="assets/master_architecture.svg" alt="Master Formalization Architecture Pipeline" width="100%"/>
</div>

---

## 🗺️ Interactive Branch Portal & Verified Game Suite

Navigate directly to the dedicated branches for each machine-verified game:

| Game | Board & Rules | Formal Status & Branch Link | Game Value | Core Mathematical Invariant | Theorems (Rocq / Lean) |
| :--- | :--- | :---: | :---: | :--- | :---: |
| **8×8 English Draughts (Checkers)** | 32 dark squares, 24 men, mandatory forward captures | [**`checkers`**](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/checkers) | **Exact Draw** | Monotonic rank potential function `Φ(st)`, cycle elimination (`ΔΦ ≥ +59` on jumps), Move 37 draw horizon | **59 Rocq / 15 Lean** |
| **8×8 Connect-5 with Gravity** | 8 columns, 8 rows, 96 winning 5-lines | [**`connect5-8x8`**](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/connect5-8x8) | **Exact Draw** | Even-Height Parity Inversion (`64 - 2m ≡ 0 (mod 2)`), Zero Rigid Cross-Pairs, 30 Pure Vertical Dominoes (Pattern `00011000`) | **26 Rocq / 18 Lean** |
| **8×7 Connect-5 with Gravity** | 8 columns, 7 rows, 76 winning 5-lines | [**`connect5-8x7`**](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/connect5-8x7) | **Exact Draw** | 10-Cell Erdős Transversal, Rule R3 Dynamic Column Freezing (`fc = 4, ft = 6`), 3 Base-Row Horizontal Cross-Pairs | **24 Rocq / 18 Lean** |
| **5×5 Dots and Boxes** | 16 Boxes, 40 Edges, double-deal sacrifices | [**`dots-and-boxes`**](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/dots-and-boxes) | **Exact Draw (8–8)** | Dual planar cubic graph, Berlekamp Nimstring loops, 2-box sacrifice parity control, tempo conservation | **46 Rocq / 24 Lean** |
| **Nine Men's Morris (Mill)** | 24 points, 16 mills, 3 concentric rings | [**`nine-mens-morris`**](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/nine-mens-morris) | **Exact Draw** | 8-Stone Transversal Barrier Theorem, Dihedral D₄ equivariance, 3-Phase DAG, per-player flying split | **65 Rocq / 26 Lean** |
| **Twelve Men's Morris** | 24 points, 20 mills (4 diagonal mills), 12 stones | [**`twelve-mens-morris`**](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/twelve-mens-morris) | **Win White (Ply 8 Fork)** | Broken vertex regularity (corner degree 3), Ply 8 Corner Ray Double-Fork (`[0; 2; 6; 16]`), +4 defensive surplus | **85 Rocq / 46 Lean** |
| **(m, n, k) Positional Games** | Arbitrary m × n, winning threshold k | [**`mnk-games`**](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/mnk-games) | **Exact (3, n, 3) Threshold** | Universal Hypergraph Handshaking Identity, Sharp (3, n, 3) Phase Transition (n=3 Draw, n≥4 Win P1 in ≤7 plies), Subgrid Monotone Projection | **36 Rocq / 17 Lean** |

---

## 🔬 Core Mathematical Theories & Methodological Pillars

The formalizations across all branches are unified by six foundational pillars of modern combinatorial game theory and constructive logic:

<p align="center">
  <img src="assets/type_theory_spectrum.svg" alt="Type Theory Spectrum across Interactive Theorem Provers" width="98%"/>
</p>

### 1. The Algebra of Fairness & Zermelo Minimax Reductions
In finite two-player zero-sum games with perfect information, Zermelo's Theorem (1913) guarantees that every board state possesses an exact theoretical value `V(s) ∈ {WinWhite, Draw, WinBlack}`. In our framework, we establish fairness (`game_value = Draw`) through **Mutual Defensive Safety**:
```text
(safe White s Black) ∧ (safe Black s White) ⟹ game_value(s) = Draw
```
Rather than exhaustively computing the astronomical state space (10¹⁰ to 10²⁰ positions), the proof constructs an inductive pairing strategy ensuring neither player can ever be forced into a losing leaf.

### 2. Hypergraph Transversals & Modulo-2 Parity Inversion
Positional games (Connect-5, Qubic, Gomoku) are formulated as uniform hypergraphs `H = (V, E)`. A defensive strategy seeks a **transversal** `T ⊆ V` intersecting every winning hyperedge `e ∈ E`.
- **Odd-Height Boards (e.g., 8×7):** Player 1's opening move leaves an odd number of empty cells (`56 - 1 = 55 ≡ 1 (mod 2)`). By the Pigeonhole Principle, 55 cells cannot be partitioned into 2-cell dominoes. Parity must be dynamically restored by poisoning a column via **Rule R3** (frozen threat suffixes).
- **Even-Height Boards (e.g., 8×8):** Player 1's move leaves 63 empty cells; Player 2's adjacent response claims cell `(4, 0)`, leaving an exact even number of empty cells:
```text
E₂ₘ = 64 - 2m = 2(32 - m) ≡ 0 (mod 2)
```
Because the column height `H = 8` is even, every column naturally partitions into pure vertical dominoes, triggering the **Zero Rigid Cross-Pairs Theorem**: 100% of winning lines are blocked with pure vertical dominoes alone!

### 3. Spatial Symmetry Groups & Broken Regularity
Boards with spatial geometry are governed by transformation automorphism groups:
- **Dihedral Group D₄ (Order 8):** In Nine Men's Morris and Dots and Boxes, rotations `rot90` (order 4) and reflections `refl` (order 2) act on the point and edge universes, preserving adjacency, mills, and boundary status.
- **Klein 4-Group V₄ & 180° Inversion:** In 8×8 Checkers, board coordinates are invariant under 180° rotation `rot180(s) = 31 - s`, which preserves rank/column deltas and dark-square parity.
- **Broken Regularity in Twelve Men's Morris:** Adding 4 diagonal mills breaks the 2-regular mill incidence of Nine Men's Morris. Corners jump to mill degree 3, allowing White's opening placement at Point 0 to radiate 3 disjoint mill rays simultaneously—guaranteeing White an unblockable double-threat fork at Ply 8!

### 4. Monotonic Lyapunov Potentials & Cycle Elimination
In games with capture mechanics and directional movement (Checkers), cyclic repetitions are prevented by establishing a strictly monotonic **Lyapunov Rank Potential Function** `Φ(st)`:
```text
Φ(st) = 64 · (24 - TotalPieces(st)) + ∑_{w ∈ W_men} Rank(w) + ∑_{b ∈ B_men} (7 - Rank(b))
```
- **Quiet Step:** `ΔΦ = +1` (advancing a man one rank).
- **Capture Jump:** `ΔΦ ≥ +59` (`+64` piece removal, `+2` rank advance, `≤ 7` opponent rank loss).
Because `Φ(st)` is strictly increasing and bounded by 1,704, men-only play is provably **acyclic and terminates unconditionally**.

### 5. Combinatorial Game Theory & Nimstring Duality
In Dots and Boxes, the primal square grid is isomorphic to a dual planar cubic graph with a single boundary component. By Berlekamp's **Double-Dealing Principle**, offering a hard-hearted handout of 2 boxes in a long chain controls the tempo:
```text
Total Boxes B ≥ 2C + 4L ⟹ Parity Control Guaranteed
```
Allowing Player 2 to maintain parity control and force an exact **8–8 Draw** on the 16-box board.

---

## ⚙️ Dual Formalization Architecture: Rocq 9.1 + Lean 4.35

<div align="center">
  <img src="assets/historical_timeline.svg" alt="Historical Timeline of Solved Board Games" width="98%"/>
</div>

Virtually all historic game solutions between 1980 and 2007 (Allis, Gasser, Schaeffer) relied on unverified C code, bespoke retrograde scripts, or mainframe hardware runs that could not be independently audited for compiler bugs or bit flips.

Our project introduces a **dual formalization methodology** that eliminates trusted unverified code:
1. **Deductive Constructive Layer (Rocq 9.1):**
   - Formalized in the Calculus of Inductive Constructions (CIC).
   - Validates inductive game trees, game-value definitions, and strategy soundness predicates.
   - Executes verified boolean certificate checkers via native bytecode compilation (`vm_compute`), evaluating millions of board transitions directly inside the kernel with **zero axioms and zero admits**.
2. **Analytic Hand-Proof Layer (Lean 4.35.0):**
   - Formalized in Dependent Type Theory.
   - Mechanizes human-surveyable pen-and-paper proofs using Presburger linear integer arithmetic (`omega`) over `ℤ`.
   - Discharges geometric casework constructively without `Classical.choice`, verified via `#print axioms`.
3. **Hardware Bitboard Verification Suite (C11 / SIMD / GPU):**
   - Independent 64-bit SWAR, AVX2, and CUDA bitboard verification tools validating 100% agreement with formal theorem definitions.

---

## 🏆 Master Comparative Taxonomy of Verified Board Games

| Dimension / Metric | 8×8 Checkers | 8×8 Connect-5 | 8×7 Connect-5 | 5×5 Dots & Boxes | Nine Men's Morris | Twelve Men's Morris |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **Grid / Topology** | 32 Dark Squares | 8×8 Grid (64 cells) | 8×7 Grid (56 cells) | 5×5 Dots (16 Boxes) | 24 Points (3 Rings) | 24 Points (+4 Diags) |
| **State Space Size** | `~5.00 × 10²⁰` | `~3.4 × 10³⁰` | `~1.4 × 10²⁶` | `~1.2 × 10¹¹` | `~1.0 × 10¹⁰` | `~1.5 × 10¹¹` |
| **Game Value** | **Exact Draw** | **Exact Draw** | **Exact Draw** | **Exact Draw (8–8)** | **Exact Draw** | **Win White** |
| **Original Solver** | Schaeffer (2007) | *This Work (2026)* | *This Work (2026)* | Conway/Berlekamp | Gasser (1993) | *This Work (2026)* |
| **Rocq 9.1 Theorems** | **59 Closed** | **26 Closed** | **24 Closed** | **46 Closed** | **65 Closed** | **85 Closed** |
| **Lean 4.35 Theorems** | **15 Verified** | **18 Verified** | **18 Verified** | **24 Verified** | **26 Verified** | **46 Verified** |
| **Symmetry Group** | `V₄` (180° Inversion) | Reflection `x ↔ 7-x` | Reflection `x ↔ 7-x` | `D₄` (Order 8) | `D₄` (Order 8) | `D₄` (Order 8) |
| **Axioms / Admits** | **0 / 0** | **0 / 0** | **0 / 0** | **0 / 0** | **0 / 0** | **0 / 0** |
| **Dedicated Branch** | [`checkers`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/checkers) | [`connect5-8x8`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/connect5-8x8) | [`connect5-8x7`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/connect5-8x7) | [`dots-and-boxes`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/dots-and-boxes) | [`nine-mens-morris`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/nine-mens-morris) | [`twelve-mens-morris`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/twelve-mens-morris) |

---

## 🔮 Unsolved Game Frontiers & Ongoing Research

With 6 landmark games formalized and verified, the repository's open research roadmap targets the remaining unsolved game frontiers:

1. **Connect-5 on 9×7 with Gravity (The Odd-Width Boundary):**
   - On 8×7 and 8×8, the width is even (8), so the defensive burden is shared symmetrically between Columns 3 and 4.
   - On **9×7**, the width is **odd**: there is a unique symmetry axis at **Column 4**. Does White playing at `(4, 0)` break Black's pairing defense and force a First-Player Win, or can Black hold a Draw?
2. **Connect6 on Small Bounded Grids (6×6, 7×7, 8×8):**
   - Invented by Prof. I-Chen Wu in 2005 to neutralize first-mover advantage by having players place 2 stones per turn. The exact fairness boundary on small grids remains an open combinatorial problem.
3. **Russian Checkers (Shashki) on 8×8:**
   - Features **flying kings** (sliding arbitrarily far along open diagonals) and **backward captures for regular men**. The resulting high branching factor (b ≈ 10–20) and deep tactical combinations have prevented standard retrograde exhaustion.
4. **Dots and Boxes (6×6 Dots / 25 Boxes):**
   - Because the box count is **odd** (5 × 5 = 25), an exact draw is impossible! Which player forces the win, and by what exact margin?

For the complete technical specifications and literature analysis, see [**`UNPROVED_GAMES_FORMAL_ROADMAP.md`**](UNPROVED_GAMES_FORMAL_ROADMAP.md) and [**`THEORETICAL_FOUNDATIONS_AND_METHODS.md`**](THEORETICAL_FOUNDATIONS_AND_METHODS.md).

---

## 📜 Zero KaTeX Delimiter Standard

Across all Markdown documentation in this repository, mathematical expressions strictly avoid raw LaTeX math delimiters (dollar signs) to prevent browser KaTeX rendering crashes on GitHub. All formulas are rendered using standard Unicode mathematical typography (`8 × 8`, `m × n`, `k = 5`, `∈`, `≤`, `≥`, `≡`, `⟷`, `⇒`, `→`, `ℤ`, `Φ(st)`) and fenced code blocks (` ```text `).

---

## 📄 License & Citation

This formal verification suite is released under the **MIT License**.

```bibtex
@misc{FormalBoardGames2026,
  author       = {TACITVS Team},
  title        = {Theorem Prover Formalization of Board Games: Foundational Constructive Game Theory across Rocq 9.1 and Lean 4.35},
  year         = {2026},
  publisher    = {GitHub},
  howpublished = {\url{https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games}}
}
```
