# Research 026: the regional Erdős–Selfridge barrier

**The value of the 5×5×5 game is still unresolved.** This note does not prove
that the game is a draw, and it does not prove a first-player win. It proves a
clean theorem about *proof methods*: the two classical drawing arguments
(pairing and the Erdős–Selfridge potential), and every way of mixing them by
cutting the board into independent regions, cannot work on the empty board.
The reason is a single inequality, `6 · lines ≤ 5 · cells`, and
`6 · 109 = 654 > 625 = 5 · 125`.

Black is called Breaker and White is called Maker throughout, because every
argument here only blocks. A *live* line is a winning line with no Black stone.

## 1. Regional certificates

Fix a position with Maker to move.

**Definition.** A *regional certificate* consists of

- pairwise disjoint sets of free cells `R_1, …, R_r` (the regions), and
- for every live line `L`, a region `ρ(L)`, with *fragment*
  `f(L) = L ∩ R_ρ(L)`,

such that for every region `R`

```text
        Σ   2^(−|f(L)|)   <   1/2 .                                  (ES)
     ρ(L) = R
```

Two familiar special cases:

| Certificate | Regions | Why (ES) holds |
| :--- | :--- | :--- |
| Pairing strategy | one 2-cell region per live line | each sum is `1/4` |
| Erdős–Selfridge criterion (Maker moves first) | one region, all free cells | it is the criterion itself |

A regional certificate is any hybrid: some lines handled by pairs, some by a
potential on a larger block, with different blocks for different lines.

**Theorem 1 (soundness).** If a position has a regional certificate, Maker
never completes a line. In the real game, Black does not lose from it.

*Proof.* For a region `R` and a later position let

```text
Φ_R = Σ 2^(−(number of free cells of f(L))),
```

summed over the lines assigned to `R` whose fragment contains no Breaker
stone. Write `w(L)` for a single term, `G(x) = Σ_{f(L) ∋ x} w(L)` for a free
cell `x ∈ R`. Breaker's strategy: after Maker plays in `R`, play the free cell
of `R` with the largest `G`; if `R` is full, or Maker played outside every
region, play anywhere.

*Claim: immediately after every Maker move in `R`, `Φ_R < 1`.*
Initially `Φ_R < 1/2` by (ES). A Maker move at `x` doubles exactly the terms
counted in `G(x) ≤ Φ_R`, so after Maker's first move in `R`, `Φ_R < 1`.
Now suppose `Φ_R < 1` after a Maker move in `R`. Breaker answers at the
maximiser `y`, which removes `G(y)`. Any extra Breaker stones in `R` only
remove further terms. Maker's next move in `R` at `x` adds the current value
of `G(x)`, which is at most its value before `y` was played, hence at most
`G(y)`. So `Φ_R` did not increase. ∎ (claim)

A fragment fully occupied by Maker would contribute `2^0 = 1` to `Φ_R` right
after Maker's move, contradicting the claim. So no fragment, and therefore no
line, is ever fully occupied by Maker. ∎

## 2. The barrier

**Theorem 2 (density bound).** If a position has a regional certificate, then

```text
        6 · (number of live lines)  ≤  5 · (number of free cells).
```

**Corollary 3.** The empty 5×5×5 board has no regional certificate:
`6 · 109 = 654 > 625 = 5 · 125`. In particular it has no pairing strategy
(the known count `109 > 62`), the Erdős–Selfridge criterion fails
(the known `109/32 > 1/2`), and no combination of the two on disjoint regions
succeeds either. At most 104 of the 109 lines can ever be covered this way.

*Proof of Theorem 2.* It suffices to show, for a single region with `n` cells
and `m` assigned lines, that `6m ≤ 5n`; summing over the disjoint regions
gives the theorem.

Let `a_s` be the number of fragments of size `s` in the region.

1. *Sizes.* A fragment has at most 5 cells. A fragment of size 1 alone
   contributes `1/2`, violating (ES). So `s ∈ {2,3,4,5}`.
2. *Budget.* Multiplying (ES) by 32 gives `8a₂ + 4a₃ + 2a₄ + a₅ < 16`, so
   `8a₂ + 4a₃ + 2a₄ + a₅ ≤ 15`. In particular `m ≤ 15`.
3. *Pairs.* Two distinct winning lines share at most one cell
   (`two_lines_intersect_at_most_once`), so two distinct fragments share at
   most one cell, and no pair of cells lies in two fragments. Counting pairs
   of cells inside the region: `a₂ + 3a₃ + 6a₄ + 10a₅ ≤ n(n−1)/2`.

If `n ≥ 18` then `6m ≤ 90 ≤ 5n`. If `n ≤ 17`, minimise the number of pairs
used by `m` fragments under the budget. Starting from all fragments of size 5
(budget `m`, pairs `10m`), shrinking a fragment to size 4, 3, 2 costs 1, 3, 7
budget units and saves 4, 7, 9 pairs, so size 4 is used first, then size 3:

| `m` | cheapest sizes | pairs | least `n` | `⌊5n/6⌋` |
| ---: | :--- | ---: | ---: | ---: |
| 1 | 2 | 1 | 2 | 1 |
| 2 | 2, 3 | 4 | 4 | 3 |
| 3 | 3, 3, 3 | 9 | 5 | 4 |
| 4 | 3, 3, 3, 4 | 15 | 6 | 5 |
| 5 | 3, 3, 4, 4, 4 | 24 | 8 | 6 |
| 6 | 3, 4⁵ | 33 | 9 | 7 |
| 7 | 4⁷ | 42 | 10 | 8 |
| 8 | 4⁷, 5 | 52 | 11 | 9 |
| 9 | 4⁶, 5³ | 66 | 12 | 10 |
| 10 | 4⁵, 5⁵ | 80 | 14 | 11 |
| 11 | 4⁴, 5⁷ | 94 | 15 | 12 |
| 12 | 4³, 5⁹ | 108 | 16 | 13 |
| 13 | 4², 5¹¹ | 122 | 17 | 14 |
| 14 | 4, 5¹³ | 136 | 17 | 14 |
| 15 | 5¹⁵ | 150 | 18 | 15 |

In every row `m ≤ ⌊5n/6⌋`. ∎

The table is a reading aid. `verify.py` also enumerates all 166 size
profiles independently.

## Machine-checked statements

Everything in Sections 1 and 2 is proved in Rocq 9.1 against the hash-pinned
[`trusted/Rules.v`](../QUBIC-PROOF-GATE-001/trusted/Rules.v), with every
`Print Assumptions` closed under the global context (no axioms, no admits).
The whole development compiles in about two seconds.

| Statement | Rocq theorem | File |
| :--- | :--- | :--- |
| Per-region arithmetic `6m ≤ 5n` | `region_bound` | [`RegionalBarrier.v`](RegionalBarrier.v) |
| Theorem 1: a certified position is a Black non-loss under the explicit policy, against every White strategy | `regional_certificate_nonloss` | [`RegionalCertificates.v`](RegionalCertificates.v) |
| Executable leaf check, usable inside a strategy tree | `checked_regional_leaf_policy` | same |
| Corollary 3: the empty board has no regional certificate | `empty_board_has_no_regional_certificate` | same |
| Every pairing leaf of `SafePairing.v` is a regional certificate | `pairing_leaf_is_regional` | same |
| Hence no pairing works at the empty board (re-derived) | `no_pairing_leaf_at_empty_board` | same |

The Rocq definition is slightly more general than Section 1. Every cell has a
region id (`reg`), every line has an assigned region (`asg`), and region cells
may already hold stones. A line's weight is `0` once it holds a Black stone,
and otherwise `2^(5 − |fragment| + White stones in the fragment)`. The
certificate condition is that every region's total weight is below 16. The
Black policy `regional_policy` answers inside the region of White's last move,
on the free cell White would gain most from. The proof keeps this invariant at
White-to-move positions: every region is below 32, and no single White move can
lift its region to 32. A completed White line would have weight 32, so it never
appears.

Pairing leaves embed as 2-cell regions, so the barrier formally generalises the
repository's earlier pairing impossibility result (result 9 in the main README).

### What the barrier does and does not say

- It is a **necessary** condition, derived from abstract counting. The
  constant `5/6` is attained only by packings as dense as a projective plane
  of order 4, which the cube does not contain. Real regional certificates on
  this board need far fewer live lines than `5/6` of the free cells; the
  positions already certified in this repository sit near `1/2`.
- After one round (Black on the centre or a corner) the count alone no longer
  excludes a certificate: `6 · 102 = 612 ≤ 615`. The barrier is a statement
  about the empty board, not about how deep a strategy tree must go.
- It does **not** cover regions that are solved exactly instead of by (ES).
  Exact solving is strictly stronger: the complete quadrilateral (four
  3-cell fragments on six cells, each cell in two) has sum exactly `1/2`, yet
  Breaker wins it as second player (`verify.py`, step 4). Whether the empty
  board splits into exactly solved regions is open; any such region must
  carry more than `0.87` lines per cell on average.
- It does **not** cover the linear-code leaves of research 021.

## 3. Structure: 5×5×5 is Qubic plus three planes

Call a cell *generic* if no coordinate equals 2. The 64 generic cells form a
4×4×4 cube. `verify.py` (step 2) checks:

- **76 lines** meet the generic cells. Each consists of exactly 4 generic
  cells and 1 middle cell, and the 76 generic parts are exactly the 76 winning
  lines of 4×4×4 Qubic.
  - 48 axis lines each own a private middle cell;
  - 24 plane diagonals share 12 middle cells, two per cell;
  - 4 space diagonals share the centre.
- **33 lines** lie entirely inside the three middle planes.

So the 5×5×5 game is 4×4×4 Qubic, which the first player wins, where every
Qubic line needs one additional cell, together with three interlocking 5×5
boards made of those additional cells. This is why the game resists both
sides: Maker's Qubic attack must also win 76 extra cells, and Breaker cannot
afford to answer in the Qubic part and in the middle planes at once.

## 4. Why there is still no proof of the game value

This is an assessment, not a theorem.

| Board | Lines | `Σ 2^(−n)` | Value |
| :---: | ---: | ---: | :--- |
| 3×3×3 | 49 | 6.13 | first player wins |
| 4×4×4 | 76 | 4.75 | first player wins |
| **5×5×5** | **109** | **3.41** | **open** |
| 6×6×6 | 148 | 2.31 | open |
| 7×7×7 | 193 | 1.51 | draw (pairing after 4 moves) |
| 8×8×8 | 244 | 0.95 | draw |

1. **No static certificate at the root.** Corollary 3 closes the pairing and
   potential families. Research 022 closes whole-line linear codes.
2. **A strategy tree is out of reach by enumeration.** Static certificates
   first appear around Black's 10th move even when White cooperates. White
   has about 110 quiet moves per turn, so a tree to that depth has on the
   order of `110^10 / (10! · 96) ≈ 10^12` White move sets even after
   transpositions and the 96 symmetries, and against a White who refuses to
   cooperate the certificates arrive later still.
3. **Every certificate in this repository only blocks.** Pairing, linear-code
   and regional certificates all prove that Breaker wins the Maker–Breaker
   game. Nobody knows that this is true for 5×5×5. If Maker wins the
   Maker–Breaker game, a draw proof must use Black's own threats, and no leaf
   type currently in the gate can finish it.

A resolution therefore needs either a new certificate that is valid within
the first few moves, or a search on a scale this project has not attempted.

## Reproduce

```powershell
python research-026/verify.py --rocq "C:\Rocq-Platform~9.1~2026.01\bin\rocq.exe"
```

Expected final line:
`ALL CHECKS PASSED. The value of the 5x5x5 game remains unresolved.`
Step 5 copies the pinned rules and the needed gate files into a temporary
directory, checks the pinned hashes, compiles, audits assumptions and runs
`rocq check`. Runtime is a few seconds; there is no long-running search.
