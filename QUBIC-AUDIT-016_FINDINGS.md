# QUBIC-AUDIT-016 — Independent Referee Findings & Mathematical Audit

**Repository:** `TACITVS/Theorem_Prover_Formalization_of_Board_Games`  
**Branch:** `qubic-5x5x5`  
**Standard of Review:** Modern extremal combinatorics & constructive formal mathematics (Rocq 9.1, 0 axioms, 0 admits).

---

## 1. Executive Summary & Verdict

- **Did the formal proof of `Goal.ExactDraw` pass?**  
  **NO.** The proof gate [`QUBIC-PROOF-GATE-001`](file:///C:/Rocq-Platform~9.1~2026.01/Math_Proofs/Qubic_5x5x5/QUBIC-PROOF-GATE-001) executed via [`tools/verify_gate.py`](file:///C:/Rocq-Platform~9.1~2026.01/Math_Proofs/Qubic_5x5x5/QUBIC-PROOF-GATE-001/tools/verify_gate.py) correctly reported:
  ```
  REJECTED: Axiom/assumption audit FAILED: expected 2 closed theorems, got 0.
  ```
- **Why did previous runs hang for ~10 minutes?**  
  The proof script contained `destruct (Rules.step_game 125 ...)` over abstract strategies. The most likely cause is symbolic unfolding of the 125-deep fixpoint with duplicated `if`/`let` subterms, which can grow the term exponentially. This explanation is a hypothesis; it was not profiled.
- **Why was the proposed pairing strategy refuted?**  
  The proposed 43-pair + 17-defense stone policy loses on move 5 to a trivial 5-move attack on Line 0 (Counterexample 016).

---

## 2. Counterexample 016: Move-5 Refutation of `black_pairing_policy`

Under `agent/Solution.v`, Black was assigned `black_pairing_policy` relying on 43 disjoint pairs and 17 defense stones.

Consider the elementary White strategy playing the coordinates of Line 0:
$$\text{Line } 0 = [0, 1, 2, 3, 4]$$

1. **Move 1 (White plays 0):**  
   Cell `0` is not in `pairing_schedule`. Black calls `next_defense_stone`.  
   Because `0` is already occupied by White, Black chooses the next available stone in `black_defense_stones`, which is `91`.  
   Black plays **91** (nowhere near Line 0).
2. **Move 2 (White plays 1):**  
   Cell `1` is paired with `11` in `pairing_schedule` (Line 26).  
   Black plays **11** to defend Line 26.
3. **Move 3 (White plays 2):**  
   Cell `2` is paired with `77` in `pairing_schedule` (Line 52).  
   Black plays **77** to defend Line 52.
4. **Move 4 (White plays 3):**  
   Cell `3` is paired with `123` in `pairing_schedule` (Line 101).  
   Black plays **123** to defend Line 101.
5. **Move 5 (White plays 4):**  
   Cell `4` is paired with `94` in `pairing_schedule` (Line 103).  
   White plays **4**, completing all five cells of Line 0:
   $$\{0, 1, 2, 3, 4\} \subset \text{white\_stones}$$
   **`has_win (white_stones) = true`. White wins on Ply 9.**

**Kernel-checked:** with `line0_attack := fun st => length (white_stones st)`, Rocq proves `outcome (play line0_attack black_pairing_policy) = WhiteWins` by `vm_compute` (one concrete 9-ply game, 0.49 s, closed under the global context). The final history is `[0; 91; 1; 11; 2; 77; 3; 123; 4]`. Black never plays a 5th stone.

Black's policy blindly paired on unrelated lines while White marched directly down Line 0.  
The condition `length (white_stones st) < 5` ceased to hold on move 5, at which point Black had played only 4 stones ($4 < 17$), rendering the inductive invariant mathematically false.

---

## 3. Structural Obstructions in Extremal Combinatorics

### Obstruction A: Static Pairing Impossibility
1. In $\mathbb{Z}_5^3$, any two distinct straight lines intersect in at most one point:
   $$|L_i \cap L_j| \le 1 \quad \forall i \ne j$$
2. A 2-element cell pair $\{u, v\}$ can be a subset of **at most one** winning line.
3. The 125 cells can accommodate at most $\lfloor 125 / 2 \rfloor = 62$ disjoint pairs.
4. Therefore, any static pairing can cover at most 62 lines.
5. With 109 lines in $5 \times 5 \times 5$, at least $109 - 62 = \mathbf{47\text{ lines}}$ are left completely unprotected on the empty board.

### Obstruction B: Failure of the $7^3$ Method (Cain, Raymond, Källersjö 2025) on $5^3$
- In $7 \times 7 \times 7$ ($k = 7, |V| = 343, |F| = 193$):  
  Because $k = 7$, White cannot win in the first 4 moves. After 4 defensive moves by Black, unblocked lines drop to $< 167$, and Hopcroft-Karp finds a perfect matching covering all remaining lines ($2L \le 343 - 8 = 335$).
- In $5 \times 5 \times 5$ ($k = 5, |V| = 125, |F| = 109$):  
  The maximum degree of any cell is 13 (center 62) and 7 (corners). In 4 moves, Black can block at most $13 + 3 \times 7 = 34$ lines.  
  Remaining unblocked lines: $109 - 34 \ge 75$.  
  Required cells to pair 75 lines: $2 \times 75 = 150$.  
  Remaining free cells: $125 - 8 = 117$.  
  Since $150 > 117$, **no matching can possibly exist after 4 moves**.  
  *Correction (re-audit):* an earlier version claimed the capacity condition could not be met before Round 17. That was false. The crude degree bound (sum of the $k$ largest cell degrees) only excludes $k \le 6$, and the Counterexample 014 position already blocks 57 lines with 10 Black stones, meeting the capacity condition at Round 10. Capacity is necessary, not sufficient (Audit 014).

---

## 4. Current State of the Science

In combinatorial game theory (József Beck, *Combinatorial Games: Tic-Tac-Toe Theory*, Cambridge Univ. Press, 2008), the game-theoretic value of $5 \times 5 \times 5$ 3D Tic-Tac-Toe remains an **unresolved open problem**.

Any formal claim that $5^3$ is a proven exact draw without an explicit, verified reachability engine against all legal White strategies is premature. The specification-locked proof gate [`QUBIC-PROOF-GATE-001`](file:///C:/Rocq-Platform~9.1~2026.01/Math_Proofs/Qubic_5x5x5/QUBIC-PROOF-GATE-001) correctly enforced this standard and failed closed.
