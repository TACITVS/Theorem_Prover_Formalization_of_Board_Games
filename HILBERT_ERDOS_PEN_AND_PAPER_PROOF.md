# Follow-Up Monograph: A Hilbert–Zermelo–Erdős Pen-and-Paper Proof of 8×8 Connect-5 Fairness (With Constructive Mechanization in Lean 4 & Rocq 9.1)

[![Back to Main Repository](https://img.shields.io/badge/⬅_Back_to_Main_Landing_Page-README.md-2563eb?style=for-the-badge)](README.md)
[![8x8 Mathematical Monograph](https://img.shields.io/badge/📜_Companion_Monograph-8x8_Mathematical_Monograph-f59e0b?style=for-the-badge)](CONNECT5_8x8_MATHEMATICAL_MONOGRAPH.md)
[![Lean 4.35.0 Verified](https://img.shields.io/badge/Lean_4.35.0-18_Analytic_Hand--Proof_Theorems_(0_Sorrys)-10b981?style=for-the-badge)](lean4/Connect5HandProof.lean)
[![Rocq 9.1 Verified](https://img.shields.io/badge/Rocq_9.1-26_Theorems_Verified_(0_Axioms)-16a34a?style=for-the-badge&logo=coq)](CheckAssumptions.v)
[![Classic Connect-4 Appendix](https://img.shields.io/badge/🎲_Appendix-Classic_7x6_Connect--4-ec4899?style=for-the-badge)](APPENDIX_CLASSIC_CONNECT4_7x6.md)

> **Subtitle:** *How David Hilbert, Ernst Zermelo, and Paul Erdős Would Prove `game_value(8, 8, 5) = Draw` on a Single Chalkboard Using Modulo-2 Affine Geometry, Even-Height Parity Inversion, and the Symmetric Dual-Core Transversal (`00011000`)—Without Inspecting 96 Cases by Machine.*

---

## Abstract

In our primary formalization ([`C5Game.v`](C5Game.v) through [`C5CertChecker.v`](C5CertChecker.v)), we verified the deductive pairing theory and boolean reflection checker for **8 × 8 Gravity Connect-5** (`k = 5`, `96` winning lines across `64` cells) in **Rocq 9.1** via bytecode evaluation (`vm_compute`). However, a pure mathematician in the tradition of **David Hilbert (1862–1943)**, **Ernst Zermelo (1871–1953)**, and **Paul Erdős (1913–1996)** always asks a deeper structural question:

> *"Why does the Symmetric Dual-Core Domino Structure (`Pattern 00011000`) block all 96 winning lines on the 8 × 8 board? Can a human mathematician verify this on a single page of pen-and-paper without enumerating 96 hyperedges?"*

In this follow-up monograph, we give a **complete, self-contained pen-and-paper proof ("FROM THE BOOK")** that reduces the 96-line transversal property on the 8 × 8 grid to **four elementary observations**:
1. **Even-Height Parity Inversion at Ply 2** (`64 - 2 = 62 ≡ 0 (mod 2)`), eliminating the need for ground cross-pairs;
2. **The Middle-Two Vertical Domino Lemma** (`{3, 4} ⊆ [r0, r0 + 4]` for every `r0 ∈ {0, 1, 2, 3}`);
3. **The 5-Column Window Pigeonhole Lemma** (`{3, 4} ⊆ [c0, c0 + 4]` and `{2, 6} ∩ [c0, c0 + 4] ≠ ∅` for every `c0 ∈ {0, 1, 2, 3}`);
4. **Modulo-2 Parity Preservation at Distance 2** (`r4 + s · (c - 4) ≡ r4 (mod 2)` when `|c - 4| = 2`).

Furthermore, we accompany this human-readable proof with a **standalone, zero-axiom formalization in Lean 4.35.0** ([`lean4/Connect5HandProof.lean`](lean4/Connect5HandProof.lean), **18 theorems**) that translates our pen-and-paper arguments line-by-line into linear integer arithmetic (`omega`) with **zero `sorry`s, zero custom axioms, and zero uses of `Classical.choice`**, complementing our **26 machine-checked theorems in Rocq 9.1** ([`CheckAssumptions.v`](CheckAssumptions.v)).

---

## 1. The Three Mathematical Pillars: Zermelo, Erdős, and Hilbert

### 1.1 Ernst Zermelo (1913): Strategy-Stealing Fails Under Gravity, Requiring Explicit Duality
In 1913, **Ernst Zermelo** founded mathematical game theory (*"Über eine Anwendung der Mengenlehre auf die Theorie des Schachspiels"*), proving that every finite, deterministic, two-player game of perfect information has a well-defined minimax value `V ∈ {Win White, Draw, Win Black}`:
- **Proposition 1.1 (Zermelo's Mutual Safety Equilibrium):** Let `G` be a finite positional game with outcome function `O(σ_W, σ_B) ∈ {Win White, Draw, Win Black}`. If Player 1 (White) possesses a strategy `σ_W*` that guarantees `O(σ_W*, σ_B) ≠ Win Black` (`safe White`), and Player 2 (Black) possesses a strategy `σ_B*` that guarantees `O(σ_W, σ_B*) ≠ Win White` (`safe Black`), then under optimal play `V(G) = Draw`.
  *(Mechanized in [`C5Certificate.v`](C5Certificate.v) as `mutual_safety_draw` and in [`lean4/Connect5HandProof.lean`](lean4/Connect5HandProof.lean) as `zermelo_mutual_safety_draw`.)*
- **Why Strategy-Stealing Fails Under Gravity:** In free-placement Maker-Breaker games (Hex, Gomoku, Tic-Tac-Toe), John Nash's *Strategy-Stealing Argument* proves that an extra stone is never a liability, ruling out a second-player win immediately. Under **columnar gravity**, however, a stone at `(c, r)` immediately unlocks `(c, r + 1)` for the opponent! Indeed, in **Even-Height Connect-Four** (`6 × 6`, `8 × 6`, `8 × 8` with `k = 4`), John Tromp proved that **Player 2 (Black) forces a win** via Zugzwang. Thus, proving `game_value = Draw` on `8 × 8` Connect-5 (`k = 5`) requires constructive defensive invariants for **both** players.

### 1.2 Paul Erdős & Selfridge (1973): From Exponential Potentials to Exact Hales–Jewett Domino Pairings
In 1973, **Paul Erdős and John Selfridge** proved their famous criterion for Maker-Breaker games on a hypergraph `(V, H)`: if `∑_{L ∈ H} 2^{-|L|} < 1/2`, Breaker wins.
- On the `8 × 8` Connect-5 board, there are `|H| = 96` winning lines of length `k = 5`:
  ```text
  ∑_{L ∈ H} 2^{-5} = 96 / 32 = 3.00 >= 0.50.
  ```
  Thus the Erdős–Selfridge potential is `6×` too large to give a draw automatically.
- Instead, **Hales and Jewett (1963)** and **Victor Allis (1988)** showed that if the defender can assign disjoint 2-cell pairs `{(u_i, v_i)}` such that whenever the attacker claims `u_i`, the defender can immediately claim `v_i` (a **Strong Vertical Domino** `((c, r_low), (c, r_low + 1))` under gravity), then the defender is **unconditionally guaranteed** every upper cell `v_i`.

### 1.3 David Hilbert (1900): Presburger Arithmetic (`lia` / `omega`) Over Case Enumeration
Rather than verifying `check_cover` by iterating over 96 five-cell lists, **David Hilbert's** program of axiomatic geometry invites us to represent every winning line on `8 × 8` as a bounded affine map over `ℤ`:
```text
L(c0, r4, s) = { (c, r4 + s · (c - 4)) : c ∈ [c0, c0 + 4] },   where c0 ∈ {0, 1, 2, 3}, s ∈ {-1, 0, +1},
```
and discharge universal coverage in **Presburger arithmetic** (decidable linear integer arithmetic, proved complete by Hilbert's student Mojżesz Presburger in 1929).

---

## 2. The Complete Pen-and-Paper Proof ("FROM THE BOOK")

Let `V = {0, ..., 7} × {0, ..., 7}` be the `64`-cell `8 × 8` board. White opens at `(3, 0)` on Ply 1 (`b_open`), and Black responds at `(4, 0)` on Ply 2 (`b_ply2`).

### 2.1 Proposition 2.1: Even-Height Parity Inversion at Ply 2
- After White's opening move at `(3, 0)` (Ply 1), there remain:
  ```text
  |V \ {(3, 0)}| = 64 - 1 = 63 ≡ 1 (mod 2)   (ODD empty cells).
  ```
- After Black's opening response at `(4, 0)` (Ply 2), there remain:
  ```text
  |V \ {(3, 0), (4, 0)}| = 64 - 2 = 62 ≡ 0 (mod 2)   (EVEN empty cells!).
  ```
- At every subsequent Black defense turn after `2m` plies (`1 ≤ m ≤ 32`), the remaining empty cell count is strictly **even**:
  ```text
  E_{2m} = 64 - 2m = 2(32 - m) ≡ 0 (mod 2).
  ```
*(Mechanized as `parity_trap_ply1`, `parity_restored_ply2`, and `book_step5_r3_parity_law_lia` in [`C5CertChecker.v`](C5CertChecker.v), and `ply1_parity_obstruction` in [`lean4/Connect5HandProof.lean`](lean4/Connect5HandProof.lean).)*

---

### 2.2 The Symmetric Dual-Core Domino Structure (`Pattern 00011000`)

At Ply 2 (`b_ply2`), Black partitions `60` of the `62` empty cells into **30 Strong Vertical Dominoes** (`s_rigid = []`, **zero cross-pairs**), leaving only the two top center cells `(3, 7)` and `(4, 7)` unassigned:
1. **Center Columns `c ∈ {3, 4}` (Even-Row Upper Cells):**
   Three vertical dominoes per column above row `0`:
   ```text
   ((c, 1), (c, 2)),   ((c, 3), (c, 4)),   ((c, 5), (c, 6))   for c ∈ {3, 4}.
   ```
   Together with Black's ground stone at `(4, 0)`, Black is guaranteed:
   - Column `4`: all **four even rows** `{(4, 0), (4, 2), (4, 4), (4, 6)}`.
   - Column `3`: the **three positive even rows** `{(3, 2), (3, 4), (3, 6)}`.
2. **Flank Columns `c ∈ {0, 1, 2, 5, 6, 7}` (Odd-Row Upper Cells):**
   Four vertical dominoes per column from bottom to top:
   ```text
   ((c, 0), (c, 1)),   ((c, 2), (c, 3)),   ((c, 4), (c, 5)),   ((c, 6), (c, 7))   for c ∈ {0, 1, 2, 5, 6, 7}.
   ```
   Black is guaranteed all **four odd rows** `{(c, 1), (c, 3), (c, 5), (c, 7)}` in every flank column `c ∈ {0, 1, 2, 5, 6, 7}`.

In particular, restricting to the 4-column **Core Quartet `{Col 2, Col 3, Col 4, Col 6}`**, Black is guaranteed the **12-cell Core Transversal `InCoreDual`**:
```text
InCoreDual = {(4, 0), (4, 2), (4, 4), (4, 6)}
           ∪ {(2, 1), (2, 3), (2, 5), (2, 7)}
           ∪ {(6, 1), (6, 3), (6, 5), (6, 7)}.
```

---

### 2.3 Lemma 2.2 (Step 1): All 32 Vertical Winning Lines Are Blocked
> **Lemma 2.2 (Vertical Domino Transversal):**
> *Every vertical 5-in-a-row line in any column `c ∈ {0..7}` spans 5 consecutive rows `[r0, r0 + 4]` with `r0 ∈ {0, 1, 2, 3}`. Every such interval contains `{3, 4}`:*
> - *Since `r0 ≤ 3`, we have `r0 ≤ 3 < 4 ≤ r0 + 4`, so `{(c, 3), (c, 4)} ⊆ L`.*
> - *In Center Columns `c ∈ {3, 4}`, `((c, 3), (c, 4))` is a strong vertical domino with upper cell `(c, 4)`.*
> - *In Flank Columns `c ∈ {0, 1, 2, 5, 6, 7}`, `(c, 3)` is the upper cell of `((c, 2), (c, 3))` (and `L` also contains a full flank domino `((c, 2), (c, 3))` if `r0 ≤ 2` or `((c, 4), (c, 5))` if `r0 = 3`).*
> *Hence all `8 × 4 = 32` vertical winning lines are unconditionally blocked.* **Q.E.D.**

*(Mechanized as `book_step1_vertical_middle_two_dominoes` in [`C5CertChecker.v`](C5CertChecker.v) and `vertical_domino_transversal` in [`lean4/Connect5HandProof.lean`](lean4/Connect5HandProof.lean).)*

---

### 2.4 Theorem 2.3 (Steps 2 & 3): All 64 Non-Vertical Winning Lines Hit `InCoreDual`
> **Theorem 2.3 (The Hilbert–Erdős Modulo-2 Transversal Theorem on 8×8):**
> *Let `L` be any valid non-vertical 5-in-a-row winning line (`32` horizontal, `16` upward diagonal `/`, `16` downward diagonal `\`), parameterized by its starting column `c0 ∈ {0, 1, 2, 3}`, slope `s ∈ {-1, 0, +1}`, and Column-4 row intercept `r4 ∈ {0..7}`:*
> ```text
> r(c) = r4 + s · (c - 4),   with 0 ≤ r(c) ≤ 7 for all c ∈ [c0, c0 + 4].
> ```
> *Then `L ∩ InCoreDual ≠ ∅`.*
>
> **Pen-and-Paper Proof ("FROM THE BOOK"):**
> 1. **Step 2 (5-Column Window Pigeonhole):**
>    Because `0 ≤ c0 ≤ 3`, the 5-column window `[c0, c0 + 4]` satisfies `c0 ≤ 3 < 4 ≤ c0 + 4`, so **`L` always crosses Column 3 and Column 4**. Moreover:
>    - If `c0 ∈ {0, 1, 2}`, then `c0 ≤ 2 ≤ c0 + 4`, so **`L` crosses Flank Column `c = 2`**.
>    - If `c0 = 3`, then `[c0, c0 + 4] = [3, 7]`, so **`L` crosses Flank Column `c = 6`**.
> 2. **Step 3 (Modulo-2 Parity Split on `r4`):**
>    - **Case I (`r4` is EVEN):**
>      Since `0 ≤ r4 ≤ 7` and `r4 ≡ 0 (mod 2)`, we have `r4 ∈ {0, 2, 4, 6}`. Because `L` crosses Column `4` at `(4, r4)`, `L` immediately hits `{(4, 0), (4, 2), (4, 4), (4, 6)} ⊆ InCoreDual`!
>    - **Case II (`r4` is ODD):**
>      At both `c = 2` (`c - 4 = -2`) and `c = 6` (`c - 4 = +2`), the row coordinate shifts by an **even multiple** `±2s`:
>      ```text
>      r(2) = r4 - 2s ≡ r4 ≡ 1 (mod 2),     r(6) = r4 + 2s ≡ r4 ≡ 1 (mod 2).
>      ```
>      Thus **`r(2)` and `r(6)` are strictly ODD** for every slope `s ∈ {-1, 0, +1}`!
>      - If `c0 ≤ 2`, `L` crosses Column `2` at `(2, r(2))` with `0 ≤ r(2) ≤ 7` and `r(2)` odd, so `(2, r(2)) ∈ {(2, 1), (2, 3), (2, 5), (2, 7)} ⊆ InCoreDual`.
>      - If `c0 = 3`, `L` crosses Column `6` at `(6, r(6))` with `0 ≤ r(6) ≤ 7` and `r(6)` odd, so `(6, r(6)) ∈ {(6, 1), (6, 3), (6, 5), (6, 7)} ⊆ InCoreDual`.
>
> Combining Cases I and II, every one of the `64` non-vertical winning lines intersects `InCoreDual`. Together with Lemma 2.2 (`32` vertical lines), all **`96 / 96` winning lines** are blocked! **Q.E.D.**

*(Mechanized as `pigeonhole_5col_window`, `modulo2_parity_preservation`, `erdos_10cell_transversal_hand_proof`, `book_step3_central_wall_blocks_all_horizontals`, and `book_step4_central_wall_diagonal_dichotomy` in [`lean4/Connect5HandProof.lean`](lean4/Connect5HandProof.lean), and `dual_core_covers_all_96_lines` + `book_step2..book_central_wall_decomposition` in [`C5CertChecker.v`](C5CertChecker.v).)*

---

### 2.5 Proposition 2.4: Why the Unassigned Dead Cells `(3, 7)` and `(4, 7)` Are Double-Blocked
Because `(3, 7)` and `(4, 7)` are left outside the 30 dominoes, we verify by hand that every winning line passing through `(4, 7)` (and symmetrically `(3, 7)`) contains **at least two** guaranteed Black cells:
1. **The Vertical Line in Column 4 (`{(4,3), (4,4), (4,5), (4,6), (4,7)}`):**
   Contains **both** `(4, 4)` and `(4, 6)` (`2` guaranteed cells).
2. **The Four Row-7 Horizontal Lines (`c0 ∈ {0, 1, 2, 3}` at `r = 7`):**
   - If `c0 ∈ {0, 1}`, `[c0, c0 + 4]` contains columns `1` and `2`, hitting **both** `(1, 7)` and `(2, 7)`.
   - If `c0 ∈ {2, 3}`, `[c0, c0 + 4]` contains columns `5` and `6`, hitting **both** `(5, 7)` and `(6, 7)`.
3. **The Single Upward Diagonal Through `(4, 7)` (`{(0,3), (1,4), (2,5), (3,6), (4,7)}`):**
   Hits `(0, 3)` (flank odd), `(2, 5)` (flank odd), and `(3, 6)` (center even)—**triple-blocked (`3` guaranteed cells)**!

*(Mechanized as `dead_cells_3_7_and_4_7_blocked` and `dead_cell_4_7_six_lines_double_blocked` in [`C5CertChecker.v`](C5CertChecker.v), and `dead_cell_4_7_vertical_double_blocked` + `dead_cell_4_7_nonvertical_double_blocked` in [`lean4/Connect5HandProof.lean`](lean4/Connect5HandProof.lean).)*

---

## 3. Rule-R3 Frozen-Column Parity Restoration on 8×8 (`s_frozen`)

When White defends on an odd-empty board `E ≡ 1 (mod 2)` (such as after Black's odd-ply move `1, 3, ..., 2m+1`), a frozen threat at an **even** row `ft ∈ {2, 4, 6}` above an empty odd poison cell `(fc, ft - 1)` freezes the column suffix `F = {(fc, r) : ft - 1 ≤ r ≤ 7}` of cardinality:
```text
|F| = 7 - (ft - 1) + 1 = 9 - ft ∈ {3, 5, 7}   (ODD!).
```
Subtracting this odd suffix from the odd empty cell count `E` restores **even parity** across the remaining active cells:
```text
E - |F| = E - (9 - ft) ≡ 1 - 1 ≡ 0 (mod 2).
```
*(Mechanized universally as `r3_frozen_column_restores_even_parity` in [`C5CertChecker.v`](C5CertChecker.v) and `r3_frozen_suffix_restores_even_parity` in [`lean4/Connect5HandProof.lean`](lean4/Connect5HandProof.lean), and instantiated on a concrete 13-ply reachable position `b_r3` with `empties b_r3 = 51` and `s_frozen = Some (4, 2)` in `r3_concrete_check_static_true`, `r3_concrete_Static`, and `r3_concrete_cert_safe`.)*

---

## 4. Complete Cross-Reference of All 18 Lean 4.35.0 & 26 Rocq 9.1 Theorems

| Analytic Hand-Proof Step | Lean 4.35.0 Theorem ([`Connect5HandProof.lean`](lean4/Connect5HandProof.lean)) | Rocq 9.1 Theorem ([`C5CertChecker.v`](C5CertChecker.v)) |
| :--- | :--- | :--- |
| **Ply-1 Odd (`63`) & Ply-2 Even (`62`) Parity** | `ply1_parity_obstruction` | `parity_trap_ply1`, `parity_restored_ply2` |
| **Step 1: Vertical Domino Transversal (`32` lines)** | `vertical_domino_transversal` | `book_step1_vertical_middle_two_dominoes` |
| **Step 2: 5-Column Window Pigeonhole** | `pigeonhole_5col_window`, `horizontal_5col_pair_transversal` | `book_step2_central_wall_pigeonhole` |
| **Step 3: Modulo-2 Parity & Core Coverage (`64` lines)** | `modulo2_parity_preservation`, `erdos_10cell_transversal_hand_proof`, `book_step3_central_wall_blocks_all_horizontals`, `book_step4_central_wall_diagonal_dichotomy` | `dual_core_covers_all_96_lines`, `book_step3_horizontal_parity_split`, `book_step4_diagonal_parity_alternation`, `book_central_wall_decomposition` |
| **Pure Odd-Row Claimeven (`80 / 96` lines)** | `black_odd_row_transversal_hand_proof` | Motivating lemma for Pattern `00011000` |
| **Dead Cells `(3,7)` & `(4,7)` Double-Blocking** | `dead_cell_4_7_vertical_double_blocked`, `dead_cell_4_7_nonvertical_double_blocked` | `dead_cells_3_7_and_4_7_blocked`, `dead_cell_4_7_six_lines_double_blocked` |
| **Rule-R3 Frozen Suffix Parity (`9 - ft` odd)** | `r3_frozen_suffix_restores_even_parity` | `r3_frozen_column_restores_even_parity`, `book_step5_r3_parity_law_lia`, `r3_concrete_cert_safe` |
| **Zermelo Equilibrium & Follow-Up Induction** | `zermelo_mutual_safety_draw`, `allis_followup_induction` | `structure_sound`, `strategy_sound`, `mutual_safety_draw`, `connect5_8x8_fair` |
| **Classic `7 × 6` Connect-Four Book Theorems** | `c4_7x6_book_thm1a..thm3` (4 theorems) | `c4_7x6_claimeven_57_of_69_and_center3_cover`, `c4_7x6_book_theorems_lia` |
