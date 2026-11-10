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
