# Research 023: the center star dispersion theorem and opening bifurcation

**The full game value remains unresolved.** This research identifies the exact
geometric and combinatorial mechanism separating White's center opening (cell 62)
from all five non-center opening classes `[0; 1; 2; 7; 12]`.

All six named theorems are proved in Rocq 9.1 with **0 axioms and 0 admits**
in [`QUBIC-PROOF-GATE-001/agent/ZCenterStar.v`](../QUBIC-PROOF-GATE-001/agent/ZCenterStar.v).

---

## 1. The Center Star Dispersion Theorem

The center cell `(2, 2, 2)` (index 62) is the unique cell of degree 13:

```coq
Theorem center_uniquely_dominates_degree :
  forall c, c < 125 -> c <> 62 -> length (lines_through c) < length (lines_through 62).
```

By the Linear Hypergraph Lemma, any two distinct lines intersect in at most one cell:
$$|L_i \cap L_j| \le 1 \quad \forall i \ne j$$

Because all 13 center lines already share cell 62, **no two lines through the center can share any other cell**:

```coq
Theorem center_lines_pairwise_disjoint_outside_center :
  forall c, c < 125 -> c <> 62 ->
  length (filter (fun l => existsb (Nat.eqb c) l) center_lines) <= 1.
```

### Geometric Structure
The 13 lines through cell 62 form a **13-spoke star graph $S_{13}$** centered at 62 with 52 independent spokes ($13 \times 4 = 52$):

```coq
Theorem center_spoke_census :
  length (filter (fun c => length (filter (fun l => existsb (Nat.eqb c) l) center_lines) =? 1) (seq 0 125)) = 52 /\
  length (filter (fun c => length (filter (fun l => existsb (Nat.eqb c) l) center_lines) =? 0) (seq 0 125)) = 72.
```

- Exactly **52 cells** belong to a center line (each on exactly 1 center line).
- Exactly **72 cells** belong to zero center lines.
- **Consequence:** Any single stone placed by Black can eliminate **at most one** of the 13 lines through the center.

---

## 2. The Move-1 Opening Bifurcation

This geometric structure explains the fundamental difference between White's opening choices:

### Case A: White opens non-center ($W \in \{0, 1, 2, 7, 12\}$)
- Black can immediately play **$B = 62$ (Center)** on Move 1.
- In a single move, Black eliminates all **13 lines simultaneously**.
- For $W \in \{0, 2, 12\}$, Black playing 62 directly blocks the line White just started:
  * $W = 0$ (Corner): blocks the space diagonal `[0; 31; 62; 93; 124]` (`corner_zero_shares_space_diagonal_with_center`).
  * $W = 2$ (Edge-Center): blocks the planar diagonal `[2; 32; 62; 92; 122]` (`edge_center_two_shares_diagonal_with_center`).
  * $W = 12$ (Face-Center): blocks the orthogonal axis `[12; 37; 62; 87; 112]` (`face_center_twelve_shares_axis_with_center`).
- The residual line count drops instantly from 109 to 96, and the binary code rank drops from 89 to 84.
- Over the next 9 rounds, greedy minimum-rank defense frequently finds sample paths achieving $2 \times \text{rank} \le \text{free cells}$ by **Round 10 (ply 20)**, yielding verified local Linear Leaves.

### Case B: White opens at Center ($W = 62$)
- White claims the hub of the 13-spoke star $S_{13}$.
- By the Center Star Dispersion Theorem, Black can block **at most 1 spoke per move**.
- At Round 10, even if Black spent every move blocking a center spoke, at least $13 - 10 = 3$ center spokes remain unblocked.
- Consequently, the binary rank at Round 10 stays at ~55 (needed: $\le 52$).
- The threshold $2 \times \text{rank} \le \text{free cells}$ is delayed by ~4 rounds, with sample leaves first appearing around **Round 14 (ply 28)**.

> [!NOTE]
> **Sample Paths vs. Exhaustive Minimax Trees:**
> These simulation findings demonstrate that local linear leaves are reachable along sample game paths. However, settling `Goal.ExactDraw` requires an exhaustive strategy tree (`LinearDefenseNode` in `ZZLinearTrees.v`) that covers **100% of White's legal replies** from the opening to certified leaves. A high-probability sample path is empirical evidence, not a full-game proof.

---

## 3. Reproduce & Verify

From the repository root:

```powershell
python research-023/verify.py
```

This verifies the hash-pinned sources, builds all dependencies in a sandbox, audits the six theorems, and passes standalone `rocq check`.
