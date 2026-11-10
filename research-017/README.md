# Research 017: checked first-player nonloss and the remaining game value

**The objective is not yet achieved.** This work proves that the first player
can avoid losing in standard 5×5×5 Qubic. It does not determine whether optimal
play is a draw or a first-player win. This is a formalization of the usual
strategy-stealing argument, not a claim of a new solution to the open problem.

Rules: White starts, one stone is placed in an empty cell each turn, five cells
on any straight winning line win immediately, and a full board without a winner
is a draw. The cell encoding is `x + 5*y + 25*z`, with coordinates from 0 to 4.
“Fair” here means both players have a nonlosing strategy, i.e. the locked
`Goal.ExactDraw`; “unfair” means a player can force a win against every opponent.

## What is proved

All the new theorem dependencies below are assumption-free. They import the
unchanged hash-pinned `Rules.v` and `Goal.v`.

| File | Checked result |
| --- | --- |
| `agent/Geometry.v` | The 109 distinct locked lines are exactly all standard coordinate lines, up to reversal. Independently generates 218 oriented lines from constant/increasing/decreasing coordinate sequences. |
| `agent/Minimax.v` | Boolean minimax search extracts one total policy with the asserted guarantee against every opposing policy. Proves equivalence with both locked nonloss goals and exact draw. |
| `agent/RulesFacts.v` | Every play has valid cells, no repeated cells, an exact partition of stones between players, and a correct terminal result. Proves fallback requests are legal while the board has space. |
| `agent/Stealing.v` | Extra White stones cannot harm a defensive strategy. Color symmetry and this simulation prove unconditional `Goal.WhiteNonLossFromEmpty`, ruling out a forced second-player win. |
| `agent/Solution.v` | Replaces its admitted `white_nonloss` with the checked strategy-stealing proof. `black_nonloss` remains admitted. |
| `Regressions.v` | Replays the original pairing policy's loss on ply 9, a Black win on ply 10, a full-board draw, and a White win on ply 125 taking precedence over a draw. These concrete plays are not optimal-play conclusions. |

The `agent/` paths above are under `QUBIC-PROOF-GATE-001/`.

The key full-game theorem is:

```coq
Theorem white_nonloss_proved : Goal.WhiteNonLossFromEmpty.
(* exists white, forall black,
     Rules.outcome (Rules.play white black) <> Rules.BlackWins *)
```

The proof of monotonicity simulates a virtual defensive game inside a board
with extra White stones. If a virtual White move selects an extra stone White
already owns, the actual game places a fresh stone elsewhere. Inclusion of
White's virtual stones in its actual stones is preserved, while Black's stones
are identical. Immediate wins and full-board termination are handled before
the induction continues. The proof covers arbitrary total opponent policies,
including illegal requests normalized by the locked evaluator.

## Exact remaining obligation

`Stealing.exact_draw_iff_black_nonloss` proves, for these precise rules:

```coq
Goal.ExactDraw <-> Goal.BlackNonLossFromEmpty
```

The second conjunct is now supplied by a separate unconditional proof. The
remaining alternatives are:

```coq
Goal.BlackNonLossFromEmpty
(* exists black, forall white, outcome (play white black) <> WhiteWins *)
```

or its constructive minimax alternative `Minimax.WhiteForcedWin`. In particular:

```coq
Minimax.black_nonloss_value = true  (* proves exact draw *)
Minimax.black_nonloss_value = false (* extracts a forced White win *)
```

Neither equality has been proved. The solver definition is finite but its
125-ply empty-board computation has not been evaluated. A shallow search, a
single draw, or one reachable pairing-safe leaf does not resolve this equality.
The extracted search policies are mathematical witnesses; their full search is
not offered as a practical playing engine.

The 2025 paper [Cubic tic-tac-toe: A matching-based approach](https://arxiv.org/abs/2509.21494)
settles the 7³ case and explicitly leaves the 5³ and 6³ cases open. Its
Observation 3 describes the strategy-stealing argument formalized here. The
literature search for this session found no later primary-source resolution
of 5³; that is not a proof that none exists.

## Reproduce

From the repository root, with Rocq 9.1 and Python available:

```powershell
python research-017/verify.py
```

The script verifies the existing trusted-source hashes, copies only source
files into a fresh temporary directory, compiles ordinary `.vo` objects,
checks `Print Assumptions` for 15 named partial-result theorems, and invokes
the standalone recursive `rocq check` verifier. It never changes the original
gate, trusted sources, or manifest. It makes no claim of independent human
review of the existing manifest.

The global acceptance criterion remains a separate command:

```powershell
python QUBIC-PROOF-GATE-001/tools/verify_gate.py
```

It must still reject: the global `black_nonloss` obligation is unproved.
The retained `Admitted` is an explicit unresolved obligation, never evidence
for the game value. The partial-result audit does not assert that every source
file in this repository is free of admits.
