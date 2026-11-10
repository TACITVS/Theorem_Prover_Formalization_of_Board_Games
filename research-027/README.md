# Research 027: a precise programme for importing ideas from other fields

**The value of the 5×5×5 game is still unresolved.** This note proves no new
theorem about the game's value. It turns the question "could the key lie in
another area of mathematics, for example tensor algebra or algebraic topology?"
into precise, testable problems. It also records what the existing results
already rule out.

Three kinds of statements appear below, and they are labelled:

- **[Rocq]**: kernel-checked in this repository;
- **[proof]**: a short pen-and-paper proof given here;
- **[computed]**: an exact computation by `compute.py` or `small_cases.py`
  (Python, not formally verified).

## 1. The shape every proof must have

Positions below have White to move.

**Definition 1 (Black invariant).** A set `I` of positions is a *Black
invariant* if, for every `p ∈ I` and every legal White move `w`:

1. `w` does not complete a White line; and
2. unless the game has ended, Black has a legal reply `b` with `p·w·b ∈ I`, or
   `p·w·b` is terminal and is not a White win.

Black does not lose from `p` exactly when `p` lies in some invariant: the set
of all Black non-loss positions is one. So the existence of an invariant is
trivial. The whole difficulty is **describing one compactly**.

**Definition 2 (certificate class).** A *certificate class* `K` consists of

- finite objects `κ`;
- a checkable predicate `Safe(p, κ)`;
- an explicit reply rule;
- **one uniform proof** that `{p : ∃κ, Safe(p, κ)}` is a Black invariant.

The repository already contains three classes of this kind, all **[Rocq]**:

| Class | Certificate | Soundness theorem |
| :--- | :--- | :--- |
| Pairing | partner function | `static_pairing_policy_nonloss` (`SafePairing.v`) |
| Linear code | two disjoint information sets over GF(2) | `ZLinearDefense.v` (research 021) |
| Regional Erdős–Selfridge | regions plus line assignment | `regional_certificate_nonloss` (research 026) |

**Definition 3 (activation depth).** `d(K)` is the least `k` such that Black
has a strategy guaranteeing, against every White strategy, that the position
after Black's `k`-th move satisfies `Safe(·, κ)` for some `κ`. If no such `k`
exists, `d(K) = ∞`.

A draw proof through `K` is a finite opening tree of depth `d(K)` with
`K`-certificates at its leaves. The tree checkers `TreeCertificates.v` and
`ZZLinearTrees.v` already accept such trees. A rough count of the White
move sets the tree must handle, `C(125, d)/96` up to symmetry
**[computed]**:

| `d` | 3 | 4 | 5 | 6 | 7 | 8 | 10 |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| White move sets | 3.3·10³ | 1.0·10⁵ | 2.4·10⁶ | 4.9·10⁷ | 8.3·10⁸ | 1.2·10¹⁰ | 1.8·10¹² |

The known certified positions of every class appear around Black's 10th move.

> **Target T.** Find a certificate class `K` with a uniform soundness proof and
> `d(K) ≤ 6`. Any idea from another field should be judged by whether it gets
> closer to T.

## 2. A dichotomy that any approach must respect

**Definition 4.** A certificate class is *blocking* if its soundness proof
never uses that a completed Black line ends the game. Its guarantee then holds
in the Maker–Breaker game, where White (Maker, moving first) only tries to
complete a line and Black (Breaker) only tries to prevent it.

All three classes above are blocking. Their soundness theorems show that White
never completes a line, whatever Black's own lines are.

**Proposition 5 [proof].** Suppose a draw proof uses blocking leaves, and no
branch of its opening tree is closed because Black has completed a line. Then
Breaker wins the Maker–Breaker game on the 5×5×5 board.

*Proof.* The same Black strategy is a valid Breaker strategy, since no step
used a Black win. ∎

**Consequence.** If Maker wins the Maker–Breaker game on 5×5×5, then no
blocking certificate class works at any activation depth. Every draw proof
must then use Black's counter-threats. The value of this Maker–Breaker game
is therefore the first fork in the road:

> **Question Q0.** Does Maker, moving first, win the Maker–Breaker game on the
> 109 lines of the 5×5×5 board?

We know of no published answer. For comparison, 3×3×3 and 4×4×4 are
first-player wins, hence Maker wins.

## 3. The two capacity barriers

Every known class pays for its certificate with free cells.

- **Pairing** needs `2L ≤ F`, with `L` the number of live lines and `F` the
  number of free cells.
- **Regional Erdős–Selfridge** needs `6L ≤ 5F` per region, and therefore
  overall. It fails at the empty board **[Rocq]**, but is already satisfiable
  in count after one round: `6·96 = 576 ≤ 615`.
- **Linear codes** need `2·rank ≤ F`, where `rank` is the rank of the residual
  line vectors. The reason is that the two information sets are disjoint and
  each has `rank` cells.

The code barrier is where linear algebra, and hence topology, enters:

```text
rank = L − λ,   λ = dimension of the space of linear relations among the residual lines.
```

Pairing behaves as if `λ = 0`. A code certificate profits **exactly** from the
relations ("cycles") among lines.

**Exact ranks [computed].** The 109 × 125 incidence matrix:

| Field | all 109 lines | 75 axis lines | 34 diagonals | relations `λ` |
| :--- | ---: | ---: | ---: | ---: |
| GF(2) | 89 | 61 | 34 | 20 |
| GF(3) | 88 | 61 | 34 | 21 |
| GF(5) | **86** | 61 | 34 | **23** |
| GF(7) | 89 | 61 | 34 | 20 |
| Q | 89 | 61 | 34 | 20 |

Research 021 found the axis part has the structure of a simplicial boundary
map, and that the diagonals are what push the rank past 62.

The gap `2·rank − F` for whole-line codes over GF(2) **[computed]**:

| Stage | `F` | `L` | rank | `2·rank − F` |
| :--- | ---: | ---: | ---: | ---: |
| empty board | 125 | 109 | 89 | 53 |
| after one round (best Black reply, every opening) | 123 | 96 | 84 | 45 |
| after two rounds, line W0 B62 (worst White move, best greedy Black reply) | 121 | 90 | 80 | 39 |

The gap closes by about 6–8 per round, which points to round 7–8 or later.
That fits the observed leaves near round 10.

**Proposition 6 [proof]. Whole-line code leaves need `d ≥ 3`.**

*Proof.* In one round:

- White's stone deletes one column, lowering the rank by at most 1.
- Black's stone deletes the live lines through it: at most 13 lines at the
  centre, at most 7 at any other cell. Its column is zero on the remaining
  lines.

So after `k` rounds `rank ≥ 89 − k − 13 − 7(k − 1)`. For `k = 1` this gives
`rank ≥ 75`, and `150 > 123`. For `k = 2` it gives `rank ≥ 67`, and
`134 > 121`. Both violate `2·rank ≤ F`. ∎

## 4. What other fields cannot do, stated precisely

1. **No Hex-type argument.** Hex cannot end in a draw, a fact equivalent to
   Brouwer's fixed-point theorem. Here, a complete colouring of the board with
   no monochromatic line exists (research 025, SAT, independently checked).
   So no topological "every full board has a winner" theorem exists for
   5×5×5.
2. **Relabelling cannot lower rank.** Viewing the incidence matrix as a
   boundary map (research 021) or a tensor flattening changes the language,
   not the rank. Among the fields tested, the minimum is 86 (GF(5)), so
   whole-line codes fail at the empty board under every such reinterpretation.
   Independently, the parity identity of research 022 forces the centre into
   every GF(2) information set **[Rocq]**.
3. **Tensor rank and slice rank answer static questions.** Examples are the
   largest line-free set of cells, or whether drawn boards exist. A game value
   alternates "Black has a reply such that for every White move…" about 60
   times. Static bounds can feed into a certificate class, but cannot replace
   one.

So an idea from another field has to act on **which vectors or regions the
certificate uses**, not on how the existing ones are described.

## 5. Your hunch made precise: fragment codes

Combine the two working ideas: pieces of lines (as in research 026) and linear
relations (as in research 021).

**Definition 7 (fragment code).** At a position, choose for each live line
`Lᵢ` a *fragment* `fᵢ` of at least 2 of the cells White still needs on it. Let
`C_f` be the span of the fragment indicator vectors over a field `𝔽`. The
fragment system is *admissible* if the column matroid of `C_f` has two
disjoint bases inside the free cells, i.e. two disjoint information sets.

Whole lines (`fᵢ` = all needed cells) are the research 021 certificate.
Fragments of size 2 give exactly pairing (Proposition 8). Everything in
between is unexplored.

**Expected soundness (to be checked, not proved).** The research 021 exchange
argument only uses that the code is a linear span, and that a White line
completion would leave some codeword with no free cell in a reserve. If White
completes `Lᵢ`, it fills `fᵢ ⊆ Lᵢ`, so the argument should carry over
unchanged over GF(2). Checking this in Rocq means generalising the
row vectors in `ZLinearDefense.v`, and is the first concrete task.

**Proposition 8 [proof]. Size-2 fragments reduce to pairing.**

*Proof.* Treat the pairs as edges of a graph on the cells. Over any field, a
connected component with `u` vertices spans a code of dimension at least
`u − 1`. Two disjoint information sets inside it need `2(u − 1) ≤ u`, so
`u ≤ 2`: every component is a single pair. ∎

**Proposition 9 [proof]. Graph-like cycles are not enough.** At the empty
board, over GF(2), no admissible fragment system has every used cell in
exactly two fragments.

*Proof.* Such a system is dual to a simple graph `G*`:

- the fragments are its vertices;
- the cells are its edges, joining the two fragments that contain them;
- the graph is simple because two lines share at most one cell.

The fragment vectors span the cut space of `G*`. A component with `k`
fragments therefore has rank `k − 1`, and needs `2(k − 1) ≤ c` cells. A
triangle (`k = 3, c = 3`) fails, so `k ≥ 4`, and then
`c ≥ 2k − 2 ≥ 1.5k`. Summing over components:
`cells ≥ 1.5 · 109 > 125`. ∎

This is the precise sense in which your topology hunch must reach beyond
graphs. Only 1-dimensional cycles appear when cells have degree two. The
required relations need cells shared by three or more fragments, i.e.
higher-dimensional cycle structure.

**Necessary count.** At the empty board an admissible fragment code needs
`109 − λ ≤ 62`, i.e. **at least 47 independent linear relations** among the
109 fragments. Whole lines give 20 over GF(2) and 23 over GF(5).

**Where an algebraic source of relations already exists [computed].** Over
GF(5), every polynomial of total degree ≤ 3 in the coordinates sums to zero
along every line. The reason is that `Σ_{t∈GF(5)} tᵏ = 0` for `k < 4`, and
each line is an affine line of GF(5)³. This gives 20 independent
annihilators, out of a kernel of dimension 39. This is the polynomial method
(Chevalley–Warning type) acting on the board. It is also why GF(5), whose
characteristic equals the line length, has the lowest rank.

Equivalently, `rank = 125 − dim(annihilators)`, so admissibility at the empty
board needs annihilators of dimension at least 63. Whole lines over GF(5)
reach 39.

## 6. Small cases that calibrate the questions [computed]

| Hypergraph | cells | lines | lines/cell | rank GF(2), GF(3), GF(5) | two disjoint bases? | Maker wins? |
| :--- | ---: | ---: | ---: | :--- | :--- | :--- |
| complete quadrilateral | 6 | 4 | 0.667 | 3, 4, 4 | yes over GF(2) | no |
| Fano plane PG(2,2) | 7 | 7 | 1.000 | 4, 6, 7 | no | yes |
| AG(2,3) | 9 | 12 | 1.333 | 9, 6, 9 | no | yes |
| PG(2,3) | 13 | 13 | 1.000 | 12, 7, 13 | no | **no** |
| 3×3×3 cube | 27 | 49 | 1.815 | 26, 23, 27 | no | yes (known) |
| 4×4×4 cube | 64 | 76 | 1.188 | 45, 56, 56 | no | yes (known) |
| 5×5×5 cube | 125 | 109 | 0.872 | 89, 88, 86 | no | **open** |

Maker-Breaker values for up to 13 cells are exact brute force, confirmed by a
second, independent solver.

What the table shows:

- **The quadrilateral** is the smallest case where a code certificate succeeds
  while both classical methods fail. Pairing needs 8 cells and has 6. The
  Erdős–Selfridge sum is exactly 1/2, not below it. The single relation (each
  cell lies on two lines) supplies the slack.
- **No Maker-win case has two disjoint bases over any tested field.** That is
  consistent with the GF(2) theorem of research 021, and with (but does not
  prove) the generalisation to other fields in Q2 below.
- **PG(2,3) is a Breaker win with density 1.0**, above both the regional
  barrier of 5/6 and the cube's 0.872. So *exactly solved* regions can beat
  every potential-function bound. However, the largest set of pairwise
  collinear cube cells has 9 elements (the 8 corners and the centre), so
  PG(2,3) cannot sit inside the board.

## 7. The open problems, in order of leverage

Each comes with what would count as success and how it could fail.

| # | Problem | Success | Failure mode |
| :--- | :--- | :--- | :--- |
| Q0 | Maker–Breaker value of 5×5×5 | decides whether blocking certificates can ever work | infeasible search; partial results on restricted openings still help |
| Q1 | Rocq soundness of fragment codes over GF(2) (generalise `ZLinearDefense.v`) | a new certificate class, with pairing and whole-line codes as special cases | the exchange step needs whole lines; then find out exactly where |
| Q2 | Does the two-reserve exchange theorem hold over GF(q)? | lets GF(5) and polynomial annihilators be used | a counterexample: a Maker-win hypergraph with two disjoint GF(q) bases |
| Q3 | Fragment systems with at least 47 relations and two disjoint bases, at the empty board or after one round | `d ≤ 1` or `2` for a sound class, which is target T | a geometric obstruction generalising Propositions 8–9 and research 022 |
| Q4 | Densest Breaker-win linear hypergraphs with edges of size 2–5 that embed in the cube | exact-region certificates beyond 5/6 | proof that embeddable ones stay below 109/125 |
| Q5 | Sharpen the regional constant 5/6 for cube geometry | a nontrivial lower bound on `d` for regional leaves | none: either answer is informative |

Q3 is the precise form of "tensor algebra / algebraic topology might hold the
key". It asks for higher-dimensional linear relations among pieces of the 109
lines, enough of them (47), arranged so that two disjoint information sets
survive. Proposition 9 shows that graph-like relations cannot do it. The
GF(5) polynomial annihilators show that algebraic relations of the right kind
exist, but whole lines give only 39 of the 63 annihilating dimensions needed.

## Reproduce

```powershell
python research-027/compute.py       # ranks, residual capacities, tree sizes (about 6 s)
python research-027/small_cases.py   # polynomial annihilators, small designs, clique bound (under 1 s)
```

`compute.py` writes `numbers.json`. Both scripts print progress and finish in
seconds; there is no long-running search.
