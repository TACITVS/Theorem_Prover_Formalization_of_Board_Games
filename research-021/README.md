# Research 021: a linear-code defense beyond fixed pairing

**The empty-board game value remains unproved.** The new, kernel-checked result
is a strict extension of the existing pairing certificate method: a legal,
nonterminal position has a complete Black nonloss strategy even though **no
mate function satisfies the repository's static pairing invariant there**.

This is a result about an actual standard 109-line Qubic position and all of
its remaining play. It is not a proof that Black can force that position from
the empty board.

## The checked separation

The position follows these legal moves, alternating White and Black:

| Round | White | Black |
| --- | ---: | ---: |
| 1 | 38 | 62 |
| 2 | 5 | 83 |
| 3 | 98 | 104 |
| 4 | 79 | 41 |
| 5 | 4 | 100 |
| 6 | 24 | 124 |
| 7 | 76 | 93 |
| 8 | 39 | 31 |
| 9 | 2 | 48 |
| 10 | 122 | 9 |

Cell encoding is `x + 5*y + 25*z`. White is to move, neither player has won,
105 cells are free, and 53 winning lines contain no Black stone.

Rocq proves both parts of the following statement, with no assumptions:

```coq
Theorem linear_defense_strictly_beyond_pairing :
  (exists b : BlackStrategy, forall w : WhiteStrategy,
    outcome (step_game 105 true linear_state w b) <> WhiteWins) /\
  (forall mate, well_mated mate -> ~ pairing_safe mate linear_state).
```

The second part quantifies over every partner function, rather than rejecting
one chosen table. Distinct geometric lines share at most one cell, so each
nontrivial pair covers at most one line. The existing pairing invariant
requires two free cells per unblocked line. Here that would require 106 cells,
but only 105 are available. `ZPairingSeparation.v` proves this capacity bound
for the actual `well_mated` and `pairing_safe` definitions.

This rules out that invariant/certificate class. It does not classify every
policy that might use some pairing moves together with other tactical ideas.

A second, independently checked witness strengthens the numerical separation:

| Witness | Plies played | Free cells | Unblocked lines | Cells required by pairing | Cells in each information set |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Witness.v` | 20 | 105 | 53 | 106 | 52 |
| `StrongerWitness.v` | 22 | 103 | 54 | 108 | 51 |

Both positions are legal and nonterminal, and both have the same universal
remaining-game nonloss guarantee. The second has a five-cell pairing deficit.
Its data are in `stronger_linear_leaf.json`; it is also a local position,
not a forced opening tree.

## Replacing partners with information sets

View a board as a third-order `5 x 5 x 5` occupancy tensor. Flattening its
coordinates gives a vector with 125 entries over the binary field. For each
line not already blocked by Black, take the indicator vector of the cells
White still needs. Let **C** be the XOR span of those residual line vectors.

An information set is a set of free cells whose coordinates determine every
word in C. The certificate supplies **two disjoint information sets**, each
with 52 cells, together with explicit linear decoders. For each of the 53
residual rows, Rocq checks that both decoders reconstruct that entire row.
Linearity then proves reconstruction for every word in C.

The exchange proof maintains two reserves that detect every codeword zero on
Black's stones:

1. A White move touches at most one reserve. The untouched reserve prevents
   White from completing any unblocked winning line on that move.
2. If the move damages the other reserve, consider a codeword that becomes
   undetectable there. It must have a 1 at White's new cell.
3. The untouched reserve detects this word at some free cell. Black takes
   that cell. XOR closure proves that this single response eliminates every
   word causing the same defect, repairing the invariant.
4. Remove the two newly occupied cells from both reserves and repeat.

`ZLinearDefense.v` proves the induction through the entire remaining game,
including immediate wins, exhaustion of the board, and normalized illegal
requests. A single total Black strategy is obtained against all White
strategies. The current exported policy uses the existing minimax policy
extraction; it is not an efficient certified playing program. In particular,
the proof's finite `code_words` family must never be explicitly enumerated
for the 53-row witness. Certificate checking uses only the short decoders.

The exchange idea connects to established matroid circuit-game strategies;
see Bednarska and Pikhurko, [*Biased positional games on matroids* (2005)](https://pikhurko.github.io/E/BednarskaPikhurko05ejc.pdf).
We prove the required binary exchange argument directly in Rocq. We claim a
verified application and separation from the pairing invariant here, not a
new general matroid theorem or a published novelty result.

## What the tensor/topology calculation reveals

`tensor_structure.py` makes a second connection precise using exact binary
arithmetic. **These structural ranks are Python calculations, not Rocq
dimension theorems.** The game guarantees above do not trust these ranks.

Take three disjoint five-point sets X, Y, Z. Their simplicial join has 15
vertices, 75 edges, and 125 triangular faces. Identify each cell `(x,y,z)`
with a triangle. Its boundary has edges `(x,y)`, `(x,z)`, `(y,z)`. The matrix
of this boundary map is exactly the incidence matrix of the 75 axis lines.

| Exact calculation over F2 | Value |
| --- | ---: |
| Rank of vertex-edge boundary | 14 |
| Rank of edge-triangle boundary / axis incidence | 61 |
| First homology dimension | 0 |
| Second homology / axis-incidence kernel dimension | 64 |
| Rank after adding the 34 geometric diagonals | 89 |
| Full incidence kernel dimension | 36 |

The 64 independent kernel vectors have an explicit tensor form:

`(e_i + e_4) tensor (e_j + e_4) tensor (e_k + e_4)`, for `i,j,k < 4`.

Each is the eight corners of a rectangular subbox. The script checks all
boundaries, boundary-squared-zero, independence, and the dimensions. It also
constructs two disjoint 61-cell information sets for the axis incidence code.
Thus the axis-only constraints admit this defense already on an empty cube.
The 34 diagonals add 28 independent constraints; the full natural line code
has rank 89, too large for two disjoint information sets on 125 cells.

This pinpoints a concrete obstruction to the direct tensor approach. The
diagonal constraints cannot be dropped or replaced by wrapping affine lines.
The current successful full-game leaf appears after Black has blocked enough
of them and other lines. How to force such a leaf against every White opening
and continuation remains unresolved.

## Connection to the empty-board goal

`ZZLinearTrees.v` extends the existing adversarial strategy-tree checker with
linear-code leaves. Every existing certificate embeds unchanged. A branch
still checks every White request, an explicit Black response, and terminal
results before entering its child.

The assumption-free theorem `checked_empty_linear_tree_proves_exact_draw`
connects an accepted **empty-board** tree to the unchanged `Goal.ExactDraw`.
The witness supplies an accepted linear leaf at its local position and a
negative regression showing that this same certificate fails at the empty
board. No accepted empty-board tree is supplied.

## Reproduce

```powershell
python research-021/verify.py
python research-021/tensor_structure.py --check
```

The first command reproduces the decoder source, verifies the trusted-source
hashes, compiles the proof dependencies from source in a fresh temporary
directory, audits 27 selected results, and runs ordinary recursive
`rocq check`. All 27 assumption audits are closed. It does not import the
unfinished `Solution.v` or weaken the global acceptance check.

The second command independently repeats the tensor calculations and compares
the stored report. Search and certificate generation require only Python's
standard library:

```powershell
python research-021/linear_search.py --trials 1000 --seed 2102
python research-021/generate_witness.py --check
```

`linear_leaf.json` and the search program are untrusted certificate sources.
The Rocq checker verifies the concrete rows and game guarantees itself; a
Python search success or rank value is not an accepted theorem.
