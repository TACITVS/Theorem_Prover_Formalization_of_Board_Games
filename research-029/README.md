# Research 029: a Qubic engine, and how late certificates appear under good play

Status: **computations only.** Nothing here is a Rocq theorem, and the value of
5x5x5 Qubic is still unresolved. Engine games are test data, not proof.

Research 028 found that the known research-021 games are trivial: White does
not defend, and Black ends up with two winning threats. Meaningful tests need
positions reached by good White play. This note adds a fast engine and measures
when Black certificates appear in engine games.

## The engine (`engine.c`)

- **Board:** stone counts per line, updated incrementally, with Zobrist
  hashing.
- **Search:** negamax alpha-beta with a transposition table and iterative
  deepening under a per-move time limit. A forced block, where the opponent has
  a four, uses no depth. Quiescence searches four-making threat sequences up to
  8 plies.
- **Parallel:** OpenMP plays one game per thread. On 22 of the 24 logical CPUs it
  runs at about 20â€“25 M nodes/s in total, and at 1 s per move it reaches depth
  5â€“9.
- **Progress:** a status line prints every 2 s with games done, ply, depth,
  eval and nodes/s.
- **Checkpoints:** each game is appended to the output as one JSON line. On
  Ctrl-C, unfinished games are saved as `partial`, and `--resume` continues them.
- **`--black-cert`:** Black takes its 12 best-ordered moves, discards any where a
  depth-4 White search finds a forced win, and plays the one that minimises the
  **code deficit** `2Â·rank âˆ’ free`. Here `rank` is the GF(2) rank of the residual
  rows, computed in C with 128-bit Gaussian elimination. A whole-line code leaf
  needs a deficit of at most 0; that is necessary, not sufficient.

The GPU is not used. Alpha-beta search is branchy and sequential, which suits
CPU threads. A GPU would pay off only for batch work such as screening millions
of positions by rank.

Build: `gcc -O3 -march=native -fopenmp engine.c -o engine.exe`.

## Results (`analyze.py`, about 1 s per 22 games)

Each run was 22 games at 1 s per move, with the first 6 plies randomised, played
to 60 plies. Every game was still open at ply 60, and no side won. At every
White-to-move position the analysis tested pairing (max flow) and a whole-line
code leaf (exact matroid partition). A position counts as *trivial* when Black
already threatens to win.

| Black plays | first non-trivial code leaf (round) | first pairing (round) |
| --- | --- | --- |
| engine, attacking | 15â€“27, in 21 of 22 games (median 20) | 15â€“27, in 21 of 22 games |
| `--black-cert` (certificate-seeking) | **11â€“22, in all 22 games (median 13â€“14)** | 12â€“22 |

Mean code deficit `2Â·rank âˆ’ free` with certificate-seeking Black, by round:

| round | 0 | 2 | 4 | 6 | 8 | 10 | 12 | 13 | 14 | 16 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| deficit | 53 | 45.5 | 34.4 | 25.9 | 17.6 | 9.6 | 1.3 | âˆ’2.7 | âˆ’6.2 | âˆ’14.5 |

## What this says

- **The capacity bound is what binds.** Code leaves appear within a round of
  the deficit reaching 0.
- **The deficit falls about 4 per round,** and this is easy to explain. Each
  round removes two free cells, which adds 2. Black's stone kills lines worth
  about 3 units of rank, which subtracts 6.
- **Whole-line codes therefore need about 53 / 4 â‰ˆ 13 rounds of explicit tree**
  against good White play. The programme in research 027 targets activation by
  round 6. An explicit opening tree 13 rounds deep is far beyond any checkable
  size.

**Quantitative target for any new leaf class.** It must start with a capacity
deficit of about 25 or less at the empty board, or reduce it about twice as
fast per round. Fragment codes (research 028) did neither.

**Caveats.**

- White here plays its own engine and is not trying to delay certificates; a
  White that did would push activation later.
- Black is a one-step greedy certificate-seeker; a Black that looked ahead on
  the deficit might activate somewhat earlier.
- The "safe" filter is a depth-4 search, not a proof.

## Reproduce

```bash
gcc -O3 -march=native -fopenmp research-029/engine.c -o research-029/engine.exe
research-029/engine.exe --games 22 --threads 22 --time 1.0 --maxply 60 --random-plies 6 --out research-029/games_t1.jsonl
research-029/engine.exe --games 22 --threads 22 --time 1.0 --maxply 60 --random-plies 6 --black-cert --out research-029/games_cert.jsonl
python research-029/analyze.py research-029/games_cert.jsonl --out research-029/activation_cert.json
```

Each run takes about 80 s of wall time.

## Hybrid regional certificates: code regions plus potential regions

This combines research 026 with research 021. Cells are split into one **code
region** and up to 40 **potential regions**. Black always answers in the region
of White's last move.

- **Potential region.** Its fragments must satisfy `Σ 2^(5−s) ≤ 15`, where `s`
  is a fragment's free size (research 026's φ < 16). A 2-cell potential region
  is a pairing.
- **Code region.** Its GF(2) code needs two disjoint information sets
  (research 021). The **exact shortfall** is `2·rank − max(|I0|+|I1|)`,
  computed by Edmonds matroid partition; 0 is needed.

The capacity bound `2·rank − cells` is misleading here. Fragments with only 2
cells behave like graph edges, and on a connected graph the capacity bound can
pass while two disjoint bases still do not exist. That is research 027's
Proposition 8. Python layouts that optimised the capacity bound reached 10,
but their exact shortfall was 19–22. All numbers below are exact.

**Programs.**

- `hybrid.c` (C + OpenMP) is the search. It runs one annealing search per
  thread, about 2 M exact evaluations/s on 22 threads, roughly 130× the Python
  version. It checkpoints each seed every 30 s and resumes automatically.
- `hybrid.py` is the slower reference implementation. `exact_shortfall.py`
  re-scores every C layout with it, independently.

**Results.** Best exact shortfall, with 22 seeds per position (270 s each for
the empty board, 60 s each for game positions). Positions come from
`games_cert.jsonl`, played by the certificate-seeking Black. Whole-line codes
are in brackets.

| round | 0 (empty) | 3 | 4 | 5 | 6 | first whole-line leaf |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| game 0 | **19** (53) | **15** (37) | **10** (31) | **8** (27) | **6** (21) | round 12 |
| game 18 | **19** (53) | **17** (41) | **14** (35) | **12** (29) | **9** (27) | round 13 |

- **The empty-board value 19 is robust.** All 22 independent cold starts ended
  at 19, or at 20 for a few seeds. Their layouts differ, with code regions of
  23–29 cells, but the same pattern recurs: a small dense code core of about
  23 cells holds 64 lines but has rank 21, so it lacks cells. About 100 cells
  of potential regions hold the remaining ~45 lines, at about 2.2 cells per
  line. This is heuristic evidence that 19 is the floor of this model, not a
  proof.
- **The hybrid gains about 3–4 rounds.** It keeps about a third to a half of
  the whole-line shortfall and falls by 2–3 per round. Extrapolated, it reaches
  zero around round 8–10, against rounds 12–13 for whole-line leaves in the
  same games. That is a real gain, but not yet the round-6 target.
- **Caveats.**
  - Black in these games minimised the *whole-line* deficit, not the hybrid
    one, so a hybrid-aware Black should do better.
  - 60 s per game position is less converged than the 270 s used for the empty
    board.
  - No layout reached 0, so there is nothing to export to Rocq yet.
  - Soundness of the composition would need a new Rocq theorem: generalising
    `RegionalCertificates.v` with a code-region case built on
    `linear_information_minimax`.

### Hybrid-aware Black (`engine.exe --black-hybrid`)

Black now starts from the best empty-board layout and carries a layout through
the game. For each of its top 12 safe moves, it runs 100k exact evaluations of
warm-started local search, then plays the move with the lowest score. That
score is recorded per round in `games_hybrid.jsonl`. The run was 22 games of 12
rounds, about 190 s of wall time, and every game was still open.

These in-game scores are poor upper bounds: the round-1 median was 26, above the
converged empty-board 19. So Black's guidance is noisy. The table gives
converged values: `hybrid.exe` with 22 seeds × 60 s per position. Whole-line
values are in brackets.

| game | round 4 | round 6 | round 8 | round 10 | round 12 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 11 | 11 (33) | 8 (29) | 6 (21) | **6** (16) | **6** (12) |
| 1 | 15 (33) | 10 (21) | 7 (15) | | |
| 3 | 17 (37) | 14 (25) | 8 (21) | | |

**Conclusion.**

- **The hybrid-aware Black is not better** than the certificate-seeking Black
  of `games_cert.jsonl`: games 0 and 18 reached 10–14 at round 4 and 6–9 at
  round 6.
- **The hybrid's advantage is front-loaded.** It roughly halves the shortfall
  early. From round 8 on, though, it stalls at about 6 in game 11, while the
  whole-line shortfall keeps falling by about 4 per round. So the hybrid
  reaches zero no more than a few rounds before whole-line codes, around round
  12 or later, and nowhere near round 6.
- **The classical route looks exhausted.** Pairing, potential, whole-line
  codes, fragment codes and hybrids of potential and code regions all need an
  explicit opening tree of roughly 10 or more rounds, far beyond any checkable
  size.

The remaining caveats are heuristic: the searches are not exhaustive, and a
much better guided Black might do somewhat better. None of these numbers is a
theorem.

```bash
gcc -O3 -march=native -fopenmp research-029/hybrid.c -o research-029/hybrid.exe
research-029/hybrid.exe --seeds 22 --threads 22 --seconds 270 --ckdir hybrid_c_empty
research-029/hybrid.exe --seeds 22 --seconds 60 --white 4,24,100,104,0,72 --black 20,9,62,124,52,120 --ckdir hybrid_c_game0@6
python research-029/exact_shortfall.py research-029/hybrid_c_empty/best.txt
research-029/engine.exe --games 22 --threads 22 --time 1.0 --maxply 24 --random-plies 6 --black-hybrid --hyb-steps 100000 --out research-029/games_hybrid.jsonl
```
