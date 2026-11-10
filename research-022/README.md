# Research 022: layer symmetry and the center parity obstruction

The full game value remains unresolved. This suite verifies two reductions
and an obstruction to using the whole-line binary code directly at the empty
board. Its seven selected assumption audits are closed, and ordinary recursive
`rocq check` passes after a fresh source build.

## Six opening cases

Apply the permutation `[1,0,2,4,3]` to the coordinate levels on all three axes.
It exchanges inner and outer layers. It commutes with reversal, and maps each
of the 109 winning lines to another winning line as a set. The order of the
five cells on a line can change beyond simple reversal.

`ZLayerSymmetry.v` constructs a `BoardIso`, so the existing full-game symmetry
theorem applies to all remaining play, including normalized illegal requests.
Combining this map with the cube symmetries proves

```coq
Goal.ExactDraw <-> forall c, In c [0;1;2;7;12;62] -> opening_nonloss c.
```

The previous geometric representatives pair as follows. Cells 7 and 62 remain
in their own classes.

| Geometric opening representatives | New representative |
| --- | --- |
| 0, 31 | 0 |
| 1, 6 | 1 |
| 2, 32 | 2 |
| 7 | 7 |
| 12, 37 | 12 |
| 62 | 62 |

For White's center opening, the proof also preserves the center under each
chosen transformation. Black nonloss after that opening is equivalent to one
successful full-horizon Black reply among `[0;1;2;7;12]`. The six opening
values and the five center-reply values remain undetermined.

## A singleton in the whole-line code

`ZLinearObstruction.v` gives an explicit finite identity. Taking the XOR of
19 winning-line indicators yields the indicator of the center cell alone.
The selected indices in the fixed `all_lines` order are

```text
2 10 14 22 27 36 37 38 47 57 61 63 67 79 80 89 90 99 100
```

Rocq checks the XOR identity and proves that its result belongs to the span of
the whole-line indicators. It then proves that every information set for this
code must contain cell 62. Two such information sets cannot be disjoint.

The resulting theorem rejects every pair of decoders for the original
whole-line leaf checker at the empty board

```coq
Theorem every_whole_line_leaf_rejects_empty : forall decoder0 decoder1,
  linear_leafb decoder0 decoder1 initial_state = false.
```

This identifies a structural obstruction independent of the numerical rank
bound. A strategy using this checker needs an opening phase before reaching
a successful leaf. The general exchange theorem also allows other XOR-closed
codes with suitable supports in the winning lines. Constructing such a code
with two disjoint information sets at an opening remains unresolved.

## Reproduce

```powershell
python research-022/verify.py
```

The verifier checks the pinned trusted-source hashes, builds all dependencies
from source in a temporary directory, audits seven selected theorems, and runs
the recursive kernel checker. It imports the proved helper modules and keeps
the unfinished `Solution.v` outside this partial-result audit.
