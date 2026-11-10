# Research 030: how dense can a GF(2) code region of the cube be?

Status: **computations only, no Rocq theorem.** This route was tested and set
aside. Its payoff is too small for the cost of a proof.

## Question

Research 026 proved that every pairing or potential region satisfies
`6·lines ≤ 5·cells`. Because `6·109 > 5·125`, no combination of such regions
certifies the empty board. If every *valid* code region (one with two disjoint
information sets, research 021) obeyed the same bound, the barrier would extend
to all hybrids of research 029.

The lemma cannot follow from linearity alone. PG(2,4) is a linear hypergraph
with 21 points and 21 lines, and GF(2) rank 10, so it is valid with density 1.
Any proof must use the geometry of the cube.

## Search (`density.c`, C + OpenMP)

The program anneals over cell sets `C` and line sets `S`, maximising
`6L − 5F` subject to exact validity (Edmonds matroid partition, from
`research-029/hybrid_core.h`). Each seed has a minimum region size Fmin. There
are 24 seeds of 75 s each, and the best region per seed is checkpointed to
`density_ckpt/`. `profile.py` re-checks every region with the research-028
Python reference.

| Fmin | 2 | 6 | 10 | 15 | 20 | 30 | 45 | 65 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| best `(L, F)` | (1, 2) | (3, 6) | (5, 10) | (8, 16) | (10, 20) | (17, 32) | (24, 46) | (34, 66) |
| best `6L − 5F` | −4 | −12 | −20 | −32 | −40 | −58 | −86 | −126 |

All 24 regions were independently confirmed valid. Every one has slack
`F − 2·rank = 0` and at most one dependent line (`L − rank ≤ 1`).

## What this says

- **In the cube, valid code regions are about as dense as pairings:**
  `L ≈ F/2`, far below `5F/6`. Two disjoint information sets force
  `F ≥ 2·rank`. Dense cell sets, such as research 029's 23-cell core with 64
  lines, have rank close to their size, so they are invalid. This explains why
  hybrids stall: a code region buys flexibility, not density.
- **Proving the lemma would be cube-specific and expensive.** Because of
  PG(2,4), it needs a cube-specific argument, probably a computation over local
  configurations.
- **Even proved, the barrier would rule out only round 0.** One Black stone in
  the centre kills 13 lines, leaving 96 live lines on 123 free cells, which is
  already below `5/6`. The density condition is therefore not what delays
  certificates to round 10 or later. The binding constraints are the
  partition structure (research 027, Proposition 8) and the shape of the live
  lines.

The density lemma is very likely true, but proving it is not worth the cost:
the only theorem it buys is an empty-board statement that research 026 already
almost has.

```bash
gcc -O3 -march=native -fopenmp research-030/density.c -o research-030/density.exe
cd research-030 && ./density.exe --seeds 24 --threads 22 --seconds 75 && python profile.py
```
