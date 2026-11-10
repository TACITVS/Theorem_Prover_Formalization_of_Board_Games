# Research 019: a quantified opening bound and sound tactical pruning

**The full game value remains unresolved.** This stage proves a statement from
the empty board against every White strategy: a fixed, concrete blocking policy
prevents White from winning in the first 14 plies. It also proves minimax pruning
rules for forced blocks and distinct-target forks over the full remaining game.

## Opening theorem

`QUBIC-PROOF-GATE-001/agent/Tactics.v` proves:

```coq
Theorem blocking_policy_delays_white_win_until_ply_fifteen : forall w,
  outcome (play w blocking_policy) = WhiteWins ->
  15 <= length (history (final_state (play w blocking_policy))).
```

The policy blocks an immediate White completion when one exists and otherwise
requests cell 0, using the locked rules' ordinary fallback for illegal requests.
The proof covers all White strategies and all opening cells, without enumerating
the opening game tree. A truncated 14-ply computation returning `Draw` is never
used as a full-game draw claim: a separate evaluator theorem connects the prefix
bound to the ply count of an actual full-game White win.

The combinatorial proof establishes:

1. Every winning line has five distinct cells.
2. Distinct winning lines intersect in at most one cell, checked against all
   109 frozen lines.
3. Two threats with **distinct completion cells** require at least seven White
   stones. Their two four-stone supports have union size at least seven.
4. With fewer than seven White stones and no existing White win, any immediate
   completion is unique. Blocking it removes every immediate White win.

Thus White cannot force a win within its first seven moves. The theorem does
not show that White can force a win on its eighth move, or eventually.

## Full-horizon tactical rules

These results refer to Black's nonloss Boolean in the exact minimax solver over
all remaining plies:

- `ignoring_white_completion_loses`: if Black cannot win immediately, any reply
  that leaves a White completion cell free loses on the next White move.
- `forced_block_minimax_equality`: under those hypotheses, the minimax value
  equals the nonloss value of blocking the threatened cell. Omitting other Black
  replies is therefore sound.
- `checked_fork_has_total_white_win`: two distinct White completion cells yield
  a total White winning policy against every Black policy, provided Black has
  no immediate winning move and at least two plies remain.

The fork checker enumerates completion **cells**, not threat lines, and checks
Black's immediate winning replies before accepting a White fork. None of these
rules permits omitting White's quiet setup moves.

## Regression positions

`Regressions.v` checks exact legal prefixes of the locked evaluator:

- A true fork after 13 plies, with seven White stones, completion cells 4 and 20,
  and no Black immediate win. White has a proved strategy to win from this
  position against every Black continuation. Reaching that position against
  every opponent from the empty board is not established.
- Two different threat lines sharing completion cell 62. There is only one
  completion cell; the fork checker rejects and the blocking policy selects 62.
- A White fork where Black instead wins immediately at cell 29. The checked
  cutoff rejects the fork, and the evaluator proves Black wins before White
  can complete either threatened line.

## Why the older VCF opening output was insufficient

The old `solver/search_vcf.c` main routine starts with one White stone and no
Black stone, then calls a White-to-move function that only explores moves which
immediately create four-stone threats. Adding one White stone cannot do that.
The search therefore stops before exploring any quiet setup sequence; its
depth limit of eight provides no general eight-move opening bound. The routine
is now labelled a restricted synthetic-input smoke test and its misleading
game-value conclusion has been removed.

The quantified Rocq opening theorem above supplies actual strategy evidence.
It does not replace the missing full-game minimax proof.

## Reproduce

```powershell
python research-019/verify.py
```

The script checks the unchanged trusted-source hashes, compiles ordinary `.vo`
files from source in a fresh temporary directory, audits the assumptions of
15 selected results, and runs recursive `rocq check`. The global acceptance
gate remains unchanged and must still reject the admitted `black_nonloss`.
