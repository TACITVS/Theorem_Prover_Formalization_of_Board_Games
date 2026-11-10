# Research 020: full-game symmetry and the ten opening cases

**The full game value is still unproved.** This work proves an exact equivalence
between the locked draw goal and ten full-game opening nonloss obligations. It
does not prove any of those ten obligations. The reduction covers strategies
and minimax over the full remaining game, rather than only cell degrees.

## Game-theoretic symmetry

`QUBIC-PROOF-GATE-001/agent/SymmetryGame.v` defines a board isomorphism with
bounded, mutually inverse cell maps and verified images of all winning lines.
It proves validity preservation, win preservation, and:

```coq
Theorem solve_symmetry : forall iso accept owner n turn st,
  valid_state st -> n + length (history st) = 125 ->
  solve accept owner n turn (transport iso st) =
  solve accept owner n turn st.
```

This holds for any terminal acceptance predicate and for arbitrary total policies,
including requests for occupied and out-of-range cells. It therefore preserves
the quantified game guarantees used by the locked goals.

An important detail is the deterministic fallback rule. Mapping an illegal raw
request does not generally map the smallest free cell chosen as its fallback.
The proof instead maps each request's **effective legal move** and shows that
the resulting branch values cover exactly the same possibilities in both boards.
A regression checks a concrete occupied-cell example where raw fallback
equivariance would be false.

## Concrete cube transformations

The five coordinate generators (three reflections and two coordinate swaps)
have finite, checked inverses and line images, including reversed orientations.
Composition builds the 48 cube transformations. Their actions on the 125 cells
are proved pairwise distinct. Every opening cell maps to exactly one of these
ten representatives; orbit sizes are checked independently in `Regressions.v`.

| Cell | Coordinates `(x,y,z)` | Orbit size |
| --- | --- | --- |
| 0 | (0,0,0) | 8 |
| 1 | (1,0,0) | 24 |
| 2 | (2,0,0) | 12 |
| 6 | (1,1,0) | 24 |
| 7 | (2,1,0) | 24 |
| 12 | (2,2,0) | 6 |
| 31 | (1,1,1) | 8 |
| 32 | (2,1,1) | 12 |
| 37 | (2,2,1) | 6 |
| 62 | (2,2,2) | 1 |

Cell encoding remains `x + 5*y + 25*z`.

## Exact remaining obligations

`opening_state c` is the board immediately after White legally opens at cell c.
It is Black's turn and **124 plies remain**. Define:

```coq
Definition opening_nonloss c : Prop :=
  solve prevents_white false 124 false (opening_state c) = true.
```

The main result is:

```coq
Goal.ExactDraw <->
  forall c, In c [0;1;2;6;7;12;31;32;37;62] -> opening_nonloss c
```

The proof uses the unconditional first-player nonloss result from Research 017.
No finite-horizon truncation or empirical symmetry assumption replaces a game
guarantee. An accepted defensive strategy for each of these ten positions would
settle the original draw objective. None is supplied here. In particular, a
bounded search returning unknown is not a proof of a false nonloss value.

The opposite result is also connected to the original objective:

```coq
WhiteForcedWin <-> ten_opening_check = false
```

Thus a proved false full-game value for even one representative opening would
establish a forced first-player win. No such value is supplied. The reduction
preserves both possible resolutions of the original fairness/unfairness task.

## Reproduce

```powershell
python research-020/verify.py
```

This checks the unchanged trusted-source hashes, compiles from source in a fresh
temporary directory, audits 14 selected results, and runs recursive `rocq check`.
The global acceptance gate remains unchanged and still rejects the admitted
`black_nonloss` theorem.
