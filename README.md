# Generalized $(m, n, k)$ Positional Games Without Gravity

[![Rocq 9.1](https://img.shields.io/badge/Rocq%20Prover-9.1.0-blue.svg)](https://rocq-prover.org/)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0-brightgreen.svg)](https://leanprover.github.io/)
[![Theorems Closed](https://img.shields.io/badge/Rocq%20Theorems-114%20Closed%20(0%20adm)-success.svg)](CheckAssumptions.v)
[![Lean Theorems](https://img.shields.io/badge/Lean%20Theorems-63%20Verified%20(0%20sorry)-success.svg)](lean4/MNKGames.lean)

Machine-checked formalization of the family of **$(m, n, k)$ games without gravity** (generalized Tic-Tac-Toe / Gomoku) in **Rocq 9.1**, with an independent **Lean 4.35.0** cross-check of the computational core and of the Erdős–Selfridge and strategy-stealing theorems. Details are in the [Mathematical Monograph](MNK_MATHEMATICAL_MONOGRAPH.md).

All game-theoretic statements are about the **strong (maker-maker) game**: players alternately claim empty cells, and the first player to own all $k$ cells of a line wins. They are stated with an explicit semantic predicate `forces_win lines p d b`: player $p$, to move on board $b$, completes a line within $d$ of its own moves against **every** legal reply, and the opponent never completes a line first. A position is a **draw** when neither player can force a win (`game_is_draw`).

---

## Main Theorem: The $(3, n, 3)$ Sharp Phase Transition

![Phase Transition Architecture](assets/mnk_phase_transition.svg)

$$
\begin{aligned}
\mathrm{Value}(3, 3, 3) &= \mathrm{DRAW} \\
\mathrm{Value}(3, 4, 3) &= \mathrm{WIN}_{P1} \text{ in exactly } 7 \text{ plies} \\
\mathrm{Value}(3, n, 3) &= \mathrm{WIN}_{P1} \text{ within } 7 \text{ plies}, \quad \forall n \ge 4
\end{aligned}
$$

The three lines are `mnk_3_3_3_draw`, `mnk_3_4_3_exactly_7_plies` and `mnk_3_n_3_first_player_win`, packaged together as `sharp_phase_transition_3_n_3`. The values themselves are classical; what is new here (to our knowledge, see [Related formal work](#related-formal-work)) is a complete machine-checked proof for **every** $n$.

### How it is proved
1. **$(3, 3, 3)$ draw.** A verified exhaustive evaluator `wins_b` (`wins_b_spec`: `wins_b = true` $\iff$ `forces_win`) shows that neither player can force a win.
2. **$(3, 4, 3)$ win.** The original 132-node certificate (opening at cell $1 = (0, 1)$) is re-checked by a **sound** checker, and `check_cert_sound` turns the check into `forces_win (gen_lines 3 4 3) P1 4`. The evaluator also proves that no forced win exists within 5 plies.
3. **All $n \ge 4$: Window Simulation Theorem** (`window_certificate_lifts`, [`MNKWindow.v`](MNKWindow.v)). Player 1 plays inside the $3 \times 4$ window. Any Player 2 move in a column $\ge 4$ is a *far* move, recorded only by a counter. A line through a far cell meets the window only in columns $2..3$, so Player 2 is conservatively deemed to have won once it owns a window line, or once $f \ge 1$ and $f + e \ge 3$. Here $f$ is the number of far moves and $e$ is the number of Player 2 stones in columns $2..3$. A 158-node certificate passes this check, and the theorem lifts it to a forced win on the empty $3 \times n$ board for every $n \ge 4$.

### Why the former "Subgrid Monotone Projection" argument was wrong
Earlier revisions claimed that cells outside the $3 \times 4$ core "intersect zero winning lines", so that Player 2's exterior moves would be harmless dummy moves. **That is false**, because lines cross the boundary of the core. Following the 132-node strategy on $3 \times 5$:

$$
P1{:}\,(0,1),\; P2{:}\,(0,3),\; P1{:}\,(0,0),\; P2{:}\,(0,2),\; P1{:}\,(1,1),\; P2{:}\,(0,4) \;\Rightarrow\; P2 \text{ owns } (0,2)\text{-}(0,3)\text{-}(0,4)
$$

Player 2 wins at ply 6, before Player 1's planned winning move. This is machine-checked as `subgrid_projection_counterexample_3_5_3` (Rocq and Lean). `projected_cert_rejected_3_5_3` shows that the embedded certificate is rejected on $3 \times 5$.

---

## Complete Characterization of the $(m, n, 3)$ Games (formal)

$$
\forall m, n \in \mathbb{N}: \quad \mathrm{Value}(m, n, 3) = \begin{cases}
\mathrm{DRAW} & \text{if } \min(m, n) \le 2 \text{ or } (m, n) = (3, 3) \\
\mathrm{WIN}_{P1} \text{ within } 7 \text{ plies} & \text{if } \min(m, n) \ge 3 \text{ and } \max(m, n) \ge 4
\end{cases}
$$

Proved as `mnk_k3_complete_characterization`:
* $\min(m, n) \le 2$: these boards **do** contain 3-in-a-row lines whenever the other side is $\ge 3$. The draw comes from a **domino pairing strategy**: pair $(r, 2j) \leftrightarrow (r, 2j{+}1)$, or the column version. Every line contains a full domino, and the opponent always answers in the partner cell (`pairing_draw`, `mnk_two_rows_draw`, `mnk_two_cols_draw`, [`MNKPairing.v`](MNKPairing.v)).
* $(m, 3, 3)$ with $m \ge 4$: $4 \times 3$ window certificate (`mnk_m_3_3_first_player_win`).
* $m, n \ge 4$: $4 \times 4$ corner-window certificate, giving a win **within 5 plies** (`mnk_m_n_3_first_player_win_5_plies`).

---

## Two Classical Theorems of Positional Game Theory, Machine-Checked

Both theorems hold for **every** hypergraph, not only for $(m, n, k)$ boards, and both are proved in Rocq and independently re-proved in Lean.

### Strategy stealing (Nash): the second player never wins
`strategy_stealing` ([`MNKStrategyStealing.v`](MNKStrategyStealing.v)): for every family of winning lines and every board size, the second player has no forced win from the empty board. The proof formalizes three facts about `forces_win`:
* **Colour symmetry** (`forces_win_swap`): exchanging all stone colours exchanges the roles of the players.
* **An extra stone never hurts** (`steal`): adding a stone of your own colour either completes a line at once or keeps a forced win within the same number of moves.
* **No double wins** (`not_both`): two players cannot both force a win from the same position.

Combined with the verified evaluator, this gives a constructive dichotomy with no excluded middle (`positional_game_win_or_draw`, `mnk_value_win_or_draw`): every $(m, n, k)$ game is **either a forced first-player win or a draw**.

### The Erdős–Selfridge theorem (1973)

$$
\sum_{A \in E} 2^{-\lvert A \rvert} < \tfrac{1}{2} \;\Longrightarrow\; \text{Breaker, moving second, prevents Maker from claiming a whole edge.}
$$

`erdos_selfridge_breaker_second` ([`MNKErdosSelfridge.v`](MNKErdosSelfridge.v)) proves this for arbitrary non-uniform hypergraphs, and `erdos_selfridge_breaker_first` proves the variant where Breaker moves first, which needs only a sum below $1$. The proof is the classical potential-function argument with every weight scaled by $2^K$, so it stays in the natural numbers. A Maker move at $x$ adds exactly the weight through $x$. A greedy Breaker reply removes at least as much. A completed Maker line alone would weigh $2^K$.

In the strong game each player can play Breaker against the other, so the game is a **draw** (`erdos_selfridge_draw`). For $(m, n, k)$ boards this gives `mnk_erdos_selfridge_draw`:

$$
\mathcal{L}(m, n, k) < 2^{k-1} \;\Longrightarrow\; \mathrm{Value}(m, n, k) = \mathrm{DRAW}.
$$

### From Maker–Breaker strategies to game values
[`MNKMakerBreaker.v`](MNKMakerBreaker.v) proves three general facts. Each holds for every board and every family of winning lines, and together they turn a Breaker strategy into game values:
* **A Breaker win is a draw** (`breaker_win_draw`). Suppose Player 1, as Maker, cannot claim a line against some Breaker strategy. Then Player 2 uses that strategy to stop Player 1 in the strong game, and strategy stealing stops Player 2.
* **Longer lines are harder for Maker** (`maker_wins_refine`, `mnk_lines_refine`). If every line of one family contains a line of another, a Maker win for the first family is a Maker win for the second. Every $k'$-in-a-row contains a $k$-in-a-row when $k \le k'$, so a Breaker win for $(m, n, k)$ is a Breaker win for every $(m, n, k')$ with $k' \ge k$, and all those games are draws (`mnk_draw_longer_lines`). One draw certificate therefore covers a whole family of line lengths.
* **Pairing in the middle of the game** (`pairing_no_maker_win`). Breaker has answered every paired Maker stone with its partner. Every line either already carries a Breaker stone or contains a whole pair. Then Maker cannot win. Unlike `pairing_draw`, lines Breaker has already blocked need no pair, so the rule applies at any position reached in play; it is the pairing leaf of a draw certificate.

---

## Prime Dimensions and the Erdős–Selfridge Criterion

Primality and coprimality of $m, n$ play **no role** in any of the arguments. (An earlier revision claimed that $\gcd(m, n) = 1$ prevents rectangular tilings of the board, which is false: $1 \times n$ strips tile every board.)

| Game | $\mathcal{L}$ | $2^{k-1}$ | Status |
| :--- | ---: | ---: | :--- |
| $(7, 5, 3)$ | 76 | 4 | $\mathrm{WIN}_{P1}$ within 5 plies: formal (since $m, n \ge 4$) |
| $(11, 7, 5)$ | 124 | 16 | value not determined here (criterion does not apply) |
| $(13, 11, 7)$ | 212 | 64 | value not determined here (criterion does not apply) |
| $(11, 7, 7)$ | 56 | 64 | $\mathrm{DRAW}$: formal (`mnk_prime_triple_11_7_7_draw`, Rocq and Lean) |
| $(17, 13, 11)$ | 184 | 1024 | $\mathrm{DRAW}$: formal (`mnk_prime_triple_17_13_11_draw`, Rocq and Lean) |
| $(19, 17, 13)$ | 284 | 4096 | $\mathrm{DRAW}$: formal (`mnk_prime_triple_19_17_13_draw`, Rocq and Lean) |

### The prime-triple law, corrected
For consecutive primes $p < q < r$ with $p \ge 7$, there are two primes in $(p, 2p)$ (Ramanujan, 1919: the second Ramanujan prime is $11$), so $r < 2p$. Note that this does **not** follow from Bertrand's postulate, which an earlier revision cited, and that it fails for $(3, 5, 7)$ and $(5, 7, 11)$. For every board with $k \le m < 2k$ and $k \le n < 2k$:

$$
\mathcal{L}(m, n, k) \le 6k^2 - 2k < 6k^2 < 2^{k-1} \qquad (k \ge 11),
$$

machine-checked universally as `erdos_selfridge_hypothesis_near_square`. With the formal Erdős–Selfridge theorem this gives `mnk_near_square_draw`: **every** board with $11 \le k \le m, n < 2k$ is a draw. Hence every game $(r, q, p)$ on a consecutive prime triple with $p \ge 11$ is a draw. Only Ramanujan's number-theoretic input $r < 2p$ is cited.

For square boards with $k$ in a row, $\mathcal{L}(k, k, k) = 2k + 2$, and the whole family is now classified (`mnk_square_classification`): **for every $k \ge 1$, the $(k, k, k)$ game is a draw if and only if $k \ge 3$.**
* $k = 1, 2$: first-player wins, in 1 and 3 plies (`mnk_1_1_1_first_player_win`, `mnk_2_2_2_first_player_win`).
* $k = 3$: the verified evaluator (`mnk_3_3_3_draw`).
* $k = 4$: here $\mathcal{L} = 10 \ge 2^3$, so the simple criterion fails. The refined form `erdos_selfridge_draw_refined` asks instead that the total weight plus the weight of any single cell stay below $2^k$. Every cell of the $4 \times 4$ board lies on at most 3 lines, and $10 + 3 = 13 < 16$, so the game is a draw (`mnk_4_4_4_draw`, Rocq and Lean).
* $k \ge 5$: $2k + 2 < 2^{k-1}$ (`mnk_square_k_draw`).

---

## Universal Line Counting and the Handshaking Identity (formal)

The generator `gen_lines m n k`, written $G(m, n, k)$ below, explicitly lists the horizontal, vertical, diagonal and anti-diagonal lines, and is characterized by `in_gen_lines`. For **all** $m, n, k$:

$$
\lvert G(m, n, k) \rvert = \mathcal{L}(m, n, k), \qquad \mathcal{L}(m, n, k) = m(n - k + 1) + n(m - k + 1) + 2(m - k + 1)(n - k + 1) \quad (k \le \min(m, n))
$$

$$
\sum_{x = 0}^{mn - 1} \deg(x) = k \cdot \mathcal{L}(m, n, k)
$$

These are `gen_lines_count` and `mnk_handshaking`. Every generated line has exactly $k$ distinct in-grid cells (`gen_lines_uniform`, `gen_lines_nodup`, `gen_lines_in_range`).

Landmark line counts (formal): $(3,3,3){:}\ 8$, $(3,4,3){:}\ 14$, $(4,4,4){:}\ 10$, $(5,4,4){:}\ 17$, $(6,4,4){:}\ 24$, $(7,4,4){:}\ 31$, $(8,4,4){:}\ 38$, $(5,5,4){:}\ 28$, $(8,8,5){:}\ 96$, $(15,15,5){:}\ 572$. The value $(4,4,4) = \mathrm{DRAW}$ is now formal (see above). The value $(5,4,4) = \mathrm{DRAW}$ is confirmed only computationally, by the negamax harness. No game value is claimed for $(6,4,4)$, $(7,4,4)$, $(8,4,4)$, $(5,5,4)$, $(8,8,5)$ or $(15,15,5)$.

---

## Errata: Corrections in This Revision

| # | Previous claim / code | Problem | Fix |
| :- | :--- | :--- | :--- |
| 1 | `check_p1_cert` | Ignored Player 2's own lines; accepted `Branch m []` on a filled board (a draw) | Sound checker `check_cert` + soundness theorem `check_cert_sound` |
| 2 | `win_3_4_3_certified` | Only "a boolean function returns `true`"; no game semantics | Inductive `forces_win`; the certificate now **proves** `forces_win` |
| 3 | `sharp_phase_transition_3_n_3` | Proved only `L(3,n,3) >= 14 /\ depth <= 7`, nothing about play | Now: (3,3,3) draw $\wedge$ $\forall n \ge 4$, forced win within 7 plies |
| 4 | "Subgrid Monotone Projection" | False: boundary-crossing lines (counterexample above) | Window Simulation Theorem with a conservative far-move rule |
| 5 | `mnk_line_count_formula_closed` called "universal line counting" | Only unfolds a definition | `gen_lines_count` against an explicit generator |
| 6 | Handshaking identity "proved" | Never formalized | `mnk_handshaking` |
| 7 | "$\mathrm{Value}(3,3,3) = \mathrm{DRAW}$" | Never formalized | `mnk_3_3_3_draw` |
| 8 | Erdős–Selfridge "machine-checked draws" | Only the inequality was checked | The Erdős–Selfridge theorem itself is now formalized, so the draws are formal |
| 9 | "Bertrand $\Rightarrow p_{i+2} < 2p_i$", "$\mathcal{L} < 4p_i^2$" | False citation / unjustified step | Ramanujan-prime citation; $\mathcal{L} < 6k^2$ proved |
| 10 | "$\min(m,n) \le 2$: DRAW (No 3-lines)" | Wrong reason; never formalized | Pairing-strategy proofs |
| 11 | "$\gcd(m,n) = 1$ $\Rightarrow$ no rectangular tiling" | False | Removed |
| 12 | $(6,4,4)$, $(7,4,4)$, $(8,4,4)$ labelled DRAW | Never verified | Labels removed |

---

## Formal Proof Architecture

```text
mnk-games/
├── _CoqProject                       # Rocq library mapping (-Q . MNK)
├── MNKBoard.v                        # Coordinates, verified line generator, counting, handshaking, E-S arithmetic
├── MNKGame.v                         # Board ops, monotonicity, forces_win semantics, verified evaluator
├── MNKCertChecker.v                  # Sound certificate checker + soundness theorem
├── MNKWindow.v                       # Window Simulation Theorem (lifting window certificates)
├── MNKPairing.v                      # Pairing strategies; draws for min(m, n) <= 2
├── MNKPhaseTransition.v              # Certificates, (3,3,3) draw, (3,n,3) transition, (m,n,3) characterization
├── MNKErdosSelfridge.v               # Erdős–Selfridge theorem (Maker–Breaker), strong-game draws, (k,k,k) classification
├── MNKStrategyStealing.v             # Strategy stealing: the second player never wins; win-or-draw dichotomy
├── MNKMakerBreaker.v                 # Breaker win => draw; monotonicity in k; mid-game pairing
├── CheckAssumptions.v                # Strict audit (125 theorems closed, 0 axioms)
├── build.ps1                         # Rocq 9.1 build + audit (counts every Print Assumptions)
├── lean4/
│   ├── lakefile.toml                 # Lake project definition
│   ├── lean-toolchain                # Lean 4.35.0 toolchain
│   └── MNKGames.lean                 # 63 audited Lean theorems: checker soundness, certificates, E-S, strategy stealing
├── build_lean.ps1                    # Lean 4 compilation and axiom auditor
├── solver/
│   ├── mnk_solver.c                  # 64-bit bitboard negamax engine with transposition table
│   └── audit_mnk.c                   # 6-pass numerical harness (lines, handshaking, values, E-S, horizons, counterexample)
├── assets/
│   └── mnk_phase_transition.svg      # Illustration of the phase transition and the window argument
├── MNK_MATHEMATICAL_MONOGRAPH.md     # Mathematical treatise
└── README.md                         # This file
```

The Lean file independently re-checks every certificate and the counterexample, and proves the soundness of its own checker. It also re-proves the Erdős–Selfridge theorem, the three prime-dimension draws and strategy stealing. The lifting theorem, the (3,3,3) draw, the pairing draws, the characterization, the universal $(m, n, k)$ corollaries and the Maker–Breaker transfer theorems of `MNKMakerBreaker.v` are proved in Rocq only.

---

## Verification & Reproduction

### 1. Compile the Rocq 9.1 proof
```powershell
powershell -ExecutionPolicy Bypass -File .\build.ps1
```
```text
=== Compiling Generalized (m, n, k) Games Formal Mathematical Proof in Rocq 9.1 ===
Compiling MNKBoard.v... OK (2.53s)
Compiling MNKGame.v... OK (0.65s)
Compiling MNKCertChecker.v... OK (0.47s)
Compiling MNKWindow.v... OK (0.87s)
Compiling MNKPairing.v... OK (0.75s)
Compiling MNKPhaseTransition.v... OK (28.45s)
Compiling MNKErdosSelfridge.v... OK (0.66s)
Compiling MNKStrategyStealing.v... OK (0.55s)
Compiling MNKMakerBreaker.v... OK (0.56s)
Compiling CheckAssumptions.v... OK (12.3s)
...
SUCCESS: 125/125 theorems closed under global context (0 axioms, 0 admits)!
```

### 2. Compile the Lean 4.35.0 cross-check
```powershell
powershell -ExecutionPolicy Bypass -File .\build_lean.ps1
```
```text
Axiom dependency report (63 theorems audited, 35 use only standard axioms):
SUCCESS: 63 Lean 4 theorems verified with 0 sorry and 0 custom axioms (11.32s)!
```

### 3. Run the C verification harness
```powershell
gcc -O3 -Wall -Wextra solver\audit_mnk.c -o solver\audit_mnk.exe
.\solver\audit_mnk.exe
```
```text
[PASS 1] Verifying Universal Line Counting Formula L(m, n, k)... 16/16 [OK]
[PASS 2] Verifying Hypergraph Handshaking Identity: Sum deg(c) = k * L... 7/7 [OK]
[PASS 3] Verifying Exact Game-Theoretic Values via Negamax Engine...
  (3, 3, 3): DRAW, (3, 4, 3): WIN FOR PLAYER 1, (4, 4, 4): DRAW, (5, 4, 4): DRAW [OK]
[PASS 4] Verifying the Erdos-Selfridge hypothesis L < 2^(k-1)... 3/3 [OK]
[PASS 5] Verifying exact forced-win horizons in the strong game...
  (3, n, 3) for n = 4..8 and (m, 3, 3) for m = 4..6: exactly 7 plies; (4,4,3), (4,5,3), (5,5,3): 5 plies [OK]
[PASS 6] Replaying the refuted subgrid-projection line on 3 x 5... [OK]
ALL AUDIT PASSES COMPLETED WITH ZERO ERRORS!
```

---

## Related Formal Work

A search of the Archive of Formal Proofs (Isabelle), Lean's Mathlib and Reservoir package index, the Rocq package index, the Lean community chat archives and arXiv (November 2026) found **no earlier machine-checked development of general $(m, n, k)$ games**, **no proof-assistant proof that tic-tac-toe is a draw**, and **no formalization of the Erdős–Selfridge game theorem or of strategy stealing**. A search cannot prove absence, so these are "to our knowledge" statements. The closest work we found:

* **Tic-tac-toe in Lean 4** ([aochagavia/tic-tac-toe](https://reservoir.lean-lang.org/@aochagavia/tic-tac-toe)): defines the game and proves basic facts, such as that a drawn game ends on a full board with no winning line. It does not prove that the game is a draw.
* **Game trees in Rocq** ([bloomberg/game-trees](https://github.com/bloomberg/game-trees)): verified game-tree unfolding, with tic-tac-toe used only as a minimax example.
* **Hales–Jewett** in Mathlib and in the AFP (Isabelle): the colouring theorem behind high-dimensional tic-tac-toe, without its game consequence.
* **Hypergraph Colouring Bounds** (AFP, 2023, Edmonds and Paulson): probabilistic-method colouring bounds for hypergraphs. The Erdős–Selfridge potential argument is the game-theoretic, derandomized cousin of such bounds.
* Concurrent 2026 strong-game results on grids with Lean proofs: **transversal achievement game** ([arXiv:2608.13501](https://arxiv.org/abs/2608.13501)) and **square achievement game** ([arXiv:2610.22410](https://arxiv.org/abs/2610.22410)). The latter extends one checked board to all larger boards by a simulation theorem, in the same spirit as our Window Simulation Theorem. Also a Lean proof that Maker wins the **Snaky** hexomino Maker–Breaker game on the infinite board within 21 moves ([openai/math](https://github.com/openai/math)).

---

## Cross-Branch Navigation

* Master Theory Hub & Portal: [`main`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/main)
* 8x8 English Checkers: [`checkers`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/checkers)
* Connect-5 (8x8 Grid): [`connect5-8x8`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/connect5-8x8)
* Connect-5 (8x7 Grid): [`connect5-8x7`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/connect5-8x7)
* Dots and Boxes (5x5 / 16 Box): [`dots-and-boxes`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/dots-and-boxes)
* Nine Men's Morris: [`nine-mens-morris`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/nine-mens-morris)
* Twelve Men's Morris: [`twelve-mens-morris`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/twelve-mens-morris)
* Generalized (m, n, k) Positional Games: [`mnk-games`](https://github.com/TACITVS/Theorem_Prover_Formalization_of_Board_Games/tree/mnk-games)
