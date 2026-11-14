# Research 031: a fork-aware Black policy delays any White win to ply 17

Status: **kernel-checked.** `python research-031/verify.py` builds everything
from the pinned sources, compiles `Survival.v`, requires its assumption audit to
be closed, and re-checks the module with `rocq check` (about 45 s).

The value of 5×5×5 Qubic is still unresolved. This is an opening bound, not a
draw proof.

## Result

```coq
Theorem cross_policy_delays_white_win_until_ply_seventeen : forall w,
  outcome (play w cross_policy) = WhiteWins ->
  17 <= length (history (final_state (play w cross_policy))).
```

Against the Black strategy `cross_policy`, no White strategy wins before ply
17, that is before White's 9th stone. The previous bound (research 019,
`blocking_policy`) was ply 15.

## The policy

1. If White has a cell that completes a line, take it.
2. Otherwise, if some cell would give White two completion cells at once (a
   *fork cell*), take it.
3. Otherwise request cell 0.

## Why it works (no game-tree enumeration)

- A fork cell needs two lines through it with three White stones each. Two
  lines share at most one cell, so that is six White stones.
- With at most six White stones, those six are all of White's stones. So there
  is no second fork cell and no separate threat: one Black move removes every
  danger (`fork_structure`, `third_line`, `cross_policy_no_fork`).
- Hence White has no fork after its 7th move, its completion cell is unique and
  gets blocked, and White cannot win on move 8.

## Limits

- The argument stops at six White stones. From the seventh stone on, a fork
  cell and a separate threat can coexist, and this counting no longer suffices.
- Extending the bound move by move will not reach the end of the game. The
  fork lemmas are the reusable part.
