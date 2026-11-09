# QUBIC-RESEARCH-013 — New Full-109-Line, Nonterminal Safe Leaf

## What is proved without any optimization oracle

1. The original `OptimalCore17_85` from the uploaded QUBIC-FINAL-001 has 17 distinct stones, blocks 85 of the 109 winning lines, and its 24 reserved pairs are sound.
2. An *algebraic* upper bound for 17 Black stones is 85 blocked lines: every stone hits exactly three of the 75 orthogonal lines, so at most 3×17=51 orthogonal lines; all nonorthogonal lines total 34. This establishes 85 as an optimal geometric line-cover count.
3. The original 85-cover Black set is **terminal**, containing the complete space diagonal `(-2,-2,-2), (-1,-1,-1), (0,0,0), (1,1,1), (2,2,2)`. It is not a legal *nonterminal* 17-round destination. Rocq should test `has_winning_line Lines109 OptimalCore17_85 = true`.
4. The new certificate in `QUBIC-RESEARCH-013_safe10_certificate.json` specifies 10 Black and 10 White stones. Neither side has a winning line, all 20 placements are distinct, and the position is reachable through 10 legal nonterminal rounds by alternating the listed White and Black moves.
5. Black's 10 stones hit 57 distinct lines. The remaining 52 winning lines have 52 disjoint two-cell pairs using 104 distinct free endpoints. Exactly one free cell remains unreserved after the 20 moves. The certificate checker independently regenerates the full 109-line hypergraph and verifies all conditions.
6. For every one of 105 legal White moves from that state, the verifier checks a legal Black reply consuming one pair, and establishes that the rest remain valid. A general induction, as in `Permanent_Pairing_Defense_Theorem`, yields future safety.

## Computational optimization findings — not yet kernel-certified upper bounds

A binary mixed-integer maximum-coverage model (HiGHS) was solved to optimality in floating-point branch-and-bound:

| k Black stones | maximum winning lines hit |
|---|---:|
| 7 | 45 |
| 8 | 49 |
| 9 | 53 |
| 10 | 57 |
| 17 | 85 |
| 17 with no completed Black line | 82 |

The earlier proved necessary condition for a complete disjoint pairing after k rounds is `blocked_lines >= k+47`. These results therefore indicate that 10 rounds is the earliest possible pairing-safe leaf (k=9 requires >=56 hits, numerical optimizer gives <=53; k=10 requires >=57 and the supplied witness achieves 57). The *existence* of the 10-round safe leaf is independently checkable. The *minimum-round optimality* needs a formally checked upper bound for all smaller k.

## Rocq integration

Keep the user's existing `QubicGame.v` and put `QUBIC-RESEARCH-013_safe10.v` alongside it. On Rocq 9.1:

```powershell
rocq compile -Q . "" QubicGame.v
rocq compile -Q . "" QUBIC-RESEARCH-013_safe10.v
```

The add-on invokes `SafeForNRounds` and its existing conditional permanent defense theorem to establish a new *concrete* conditional defensive result for the full 109-line game. The add-on also checks that the original 85-cover core already contains a Black win. These Rocq scripts **have not been compiled by us** because Rocq is not installed in the runtime; only the independent Python checker was executed successfully. If the original development fails to compile, fix it before trusting the add-on.

Python check:

```powershell
python QUBIC-RESEARCH-013_verify.py QUBIC-RESEARCH-013_safe10_certificate.json
```

## The actual open proof obligation

`BlackHasNonLosingStrategyFromEmptyBoard` in the user source is **only a Definition**, not a theorem with a proof. None of the submitted files shows that Black can force the particular 10-round, 17-round, or any other certified pairing-safe state against arbitrary White moves. The missing statement still has `forall White / exists Black` quantifier alternation, legal terminal states, and must be linked to pairing-safe leaves.

The original 85-cover construction is terminal; the new 10-round safe leaf is nonterminal but only existentially reachable, not forced. Do not confuse either with a minimax solution.
