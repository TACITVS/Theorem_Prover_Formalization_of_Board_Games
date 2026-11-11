# Research 032: who wins the Maker–Breaker game on the 5×5×5 board? (Q0)

Status: **computations only, no Rocq theorem.** The value of 5×5×5 Qubic is
still unresolved, and so is Q0. Engine games are test data, not proof.

## Question

Research 027 (Proposition 5) showed that every certificate class in this
repository is *blocking*: it never uses Black's own lines. If Maker (moving
first) wins the Maker–Breaker game on the 109 lines, no blocking class works at
any depth. A White win in the real game also needs a Maker win. So Q0 is the
first fork for the whole programme.

## Result

Three matches of 22 games each. The first 6 plies are randomised among the three
best-ordered moves; after that both sides search. Budgets are nodes per move.

| match | Maker budget | Breaker budget | Maker wins | Breaker wins | game length (plies) | Maker threats per game |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| equal | 20 M | 20 M | **0** | 22 | 55–77, median 65 | 1–8, median 4.5 |
| Maker favoured 40× | 40 M | 1 M | **0** | 22 | 59–77, median 64 | 2–7, median 5 |
| Breaker favoured 40× | 1 M | 40 M | **0** | 22 | 57–77, median 65 | 2–8, median 5 |

- **Breaker won all 66 games**, and each win is exact for its final position:
  the game stops when the Erdős–Selfridge criterion holds, which proves Breaker
  wins from there. `analyze.py` replays every game from scratch and confirms it.
- **Giving Maker 40 times Breaker's budget changed nothing.** Game length and
  the number of Maker threats are the same in all three matches.
- **Maker rarely gets to force.** A "threat" is a live line brought to four
  Maker stones. Maker manages about 5 per game and never two at once.
- An earlier clock-based version of the engine gave the same picture: 66 games,
  66 Breaker wins, including Maker at 2 s against Breaker at 0.2 s per move.

## What this says, and what it does not

- This is evidence that **Breaker wins Q0**, which keeps blocking certificates
  alive and argues against a White win in the real game.
- It is **not a proof.** Both sides use the same search and the same
  heuristic, searching 7–13 plies with a move-width limit of 16–24. A Maker win
  that needs a long quiet build-up would be invisible to it.
- The Erdős–Selfridge certificate arrives at ply 55–77, that is round 28–39.
  That is far too late to serve as a leaf of an opening tree; it only
  adjudicates these games.

## Proof search: how early is Breaker's win exact? (`dfpn.c`)

A playing engine cannot decide Q0; a proof search can. `dfpn.c` is a df-pn
search: full width, no depth limit, and a position counts as solved only when
its whole tree is closed. Its exact leaves are Maker threats, the
Erdős–Selfridge potential, and a **pairing** (every live line gets two free
cells of its own, found by bipartite matching).

Each of the 22 equal-budget games was walked backwards from its last position,
solving the position after ply k, k−1, k−2, … with at most 50 M nodes each,
until one position exceeded the budget. The run took 294 s on 22 threads.

| Earliest ply at which Breaker's win is exact | min | median | max |
| --- | ---: | ---: | ---: |
| by the Erdős–Selfridge potential | 55 | 65 | 77 |
| by a pairing | 22 | 30 | 42 |
| by df-pn search | 17 | 21 | 25 |

- **980 positions solved, all as Breaker wins, none as a Maker win.**
- **Pairing is a far better leaf than the potential:** it holds about 35 plies
  earlier. Search then gains a median of 9 more plies.
- **Then there is a wall.** Raising the budget from 2 M to 50 M nodes per
  position (25 times) moved the frontier by 0 to 2 plies. The search effort with
  Maker to move, by distance before the first pairing position:

  | plies before pairing | 2 | 4 | 6 | 8 |
  | --- | ---: | ---: | ---: | ---: |
  | positions | 22 | 22 | 20 | 12 |
  | median nodes | 352 | 5,114 | 74,465 | 210,763 |
  | largest | 19,504 | 98,082 | 2,962,807 | 43,129,775 |

  That is roughly a factor 15 per Maker move over the first steps. The later
  columns of the full output hold only the few games that got that far, so they
  understate the cost.
- **The empty board is out of reach for this method.** A 40 M node probe
  (83 s, one thread) ended unsolved with proof number 14,160 and disproof number
  2.6 million, still rising. Covering the roughly 10 Maker moves between the
  empty board and the current frontier at a factor of 15 each would need about
  10¹¹ times the present budget.

Independent check (`check_dfpn.py`, shares no code with the C programs): all 22
potential leaves, all 667 pairing certificates (verified cell by cell) and the
60 smallest searches (re-solved by plain search over *every* free cell, which
also tests the dead-cell pruning) agree with the solver.

**What this means.**

- Along games played by this Breaker, the Maker–Breaker value is known exactly
  from about ply 21 on, and it is a Breaker win every time.
- For the real game, the proof frontier is about round 9–13. That is the same
  wall the certificate route hit in research 029 (round 10 or later), now
  measured with an exact search instead of estimated.
- Plain search will not close the gap. What is needed is a leaf that holds
  earlier than pairing, or a way to make one proof cover many Maker moves at
  once.

**Limits.**

- Positions are identified by 64-bit hashes and no proof tree is exported, so
  these are computed results, not Rocq theorems.
- The frontier is measured along games chosen by the engine. A Breaker that
  played for an early pairing might reach it sooner.
- The reported node counts are incremental: each position starts with the table
  left by the later positions of the same game.

## Algorithms and complexity

Standard for this project: use the asymptotically best algorithm known in the
peer-reviewed literature, and state the reason for any exception.

| Component | Algorithm used | Cost | Literature | Verdict |
| --- | --- | --- | --- | --- |
| Deciding the game | alpha-beta, iterative deepening, transposition table | exponential in depth | Maker–Breaker is PSPACE-complete already on 5-uniform hypergraphs (Koepke 2025); polynomial only up to rank 3 (Galliot, Gravier, Sivignon) | Exponential search is the justified exception. For *solving*, proof-number search (Allis 1994) and df-pn (Nagai 2002) are the standard; alpha-beta is used here only to play test games |
| Solving a position (`dfpn.c`) | df-pn with the 1+ε threshold | exponential; memory bounded by the table | Nagai 2002; Pawlewicz and Lew 2007 | the standard for solving; parallel df-pn (Pawlewicz and Hayward 2013) not used, threads run separate games instead |
| Pairing leaf | Hopcroft–Karp matching, two copies per live line | O(E√V) | Hopcroft and Karp 1973 | best known for bipartite matching of this kind; skipped after Maker moves, which cannot create a pairing |
| Child ordering in df-pn | counting sort on weights 1–255 | O(n) | — | linear |
| Exact Breaker win | Erdős–Selfridge potential, kept incrementally | O(1) per line touched | Erdős and Selfridge 1973 | best known sound test of this kind |
| Threat detection | counter of four-lines, then 4 AVX2 compares | O(1) per node | — | constant |
| Move ordering | incremental scores, lazy selection by SIMD max | O(k) vector passes for k moves searched | selection instead of sorting | no sort; the reference's insertion sort is quadratic and kept only as a reference |
| Position update | copy 448 bytes, at most 13 lines × 5 cells | O(1) | copy-make | constant |

## Programs

- **`mb.c`:** the engine. Functional style: positions are immutable values and
  every function above `main` is pure. Bitboards and AVX2; one game per thread.
- **`mb_ref.c`:** the plain reference, with byte arrays and a sort and no SIMD.
- **`mbcore.h`:** the bitboard position core shared by `mb.c` and `dfpn.c`.
- **`analyze.py`:** independent replay and summary (under a second).
- **`dfpn.c`:** the proof search. About 0.2 M nodes/s per thread; each node
  expands up to 100 children and may run a matching.
- **`check_dfpn.py`:** independent check of the solver's results (about 1 min).
- **`frontier.py`:** summary of the solver's output.

Checks made:

- **Equivalence:** `mb.c` and `mb_ref.c` give byte-identical games (22 games at
  300k nodes per move).
- **Determinism:** the same games with 1 and with 2 threads.
- **Stop and resume:** a run stopped with the stop file after 3 s (22 partial
  games) and resumed equals the uninterrupted run.
- **Solver stop and resume:** a `dfpn.exe` run cut by its wall-clock cap after
  3 s saved 4 tables; resumed, it gave the same 176 records as an uninterrupted
  run, node counts included.

Speed on an i7-13700HX, 22 threads:

| version | 300k nodes/move | 2 M nodes/move |
| --- | ---: | ---: |
| `mb_ref.c` | 24 M nodes/s | not measured |
| `mb.c` | 133 M nodes/s | 212 M nodes/s |

Profile-guided compilation was tried and gave no gain. The GPU is not used:
alpha-beta is branchy and sequential.

## Reproduce

```bash
gcc -O3 -march=native -fopenmp research-032/mb.c -o research-032/mb.exe
cd research-032
./mb.exe --games 22 --nm 20000000 --nb 20000000 --random-plies 6 --out mb_equal.jsonl
./mb.exe --games 22 --nm 40000000 --nb 1000000 --random-plies 6 --out mb_maker_fav.jsonl
./mb.exe --games 22 --nm 1000000 --nb 40000000 --random-plies 6 --out mb_breaker_fav.jsonl
python analyze.py mb_equal.jsonl mb_maker_fav.jsonl mb_breaker_fav.jsonl
```

```bash
gcc -O3 -march=native -fopenmp dfpn.c -o dfpn.exe
./dfpn.exe --games mb_equal.jsonl --threads 22 --budget 50000000 --tt-bits 23 --out df_equal.jsonl
python frontier.py df_equal.jsonl
python check_dfpn.py mb_equal.jsonl df_equal.jsonl --cap 20000 --max-search 60
./dfpn.exe --games mb_equal.jsonl --max-games 1 --threads 1 --from-ply 0 --min-ply 0 --budget 40000000 --tt-bits 25 --out df_empty.jsonl
```

The solver run takes about 5 minutes and uses 2.8 GB. It stops cleanly at
`--max-seconds` (default 540), on Ctrl-C or on the `STOP` file, saving its
tables; `--resume` continues.

Each match takes about 2 minutes and prints progress with an ETA every 2 s. To
pause, press Ctrl-C or create a file named `STOP` in the working directory;
delete it and add `--resume` to continue. Because moves depend only on the
position and the node budget, the same commands reproduce the same games.

## Sources

- F. Koepke, *Solving Maker-Breaker Games on 5-uniform hypergraphs is
  PSPACE-complete*, Electronic Journal of Combinatorics, 2025
  (arXiv:2502.20271).
- F. Galliot, S. Gravier, I. Sivignon, *Maker-Breaker is solved in polynomial
  time on hypergraphs of rank 3* (arXiv:2209.12819).
- L. V. Allis, *Searching for Solutions in Games and Artificial Intelligence*,
  PhD thesis, 1994 (proof-number search, threat-space search).
- A. Nagai, *Df-pn algorithm for searching AND/OR trees and its applications*,
  PhD thesis, 2002.
- J. Pawlewicz, Ł. Lew, *Improving depth-first pn-search: 1+ε trick*, Computers
  and Games 2006 (LNCS 4630, 2007).
- J. E. Hopcroft, R. M. Karp, *An n^(5/2) algorithm for maximum matchings in
  bipartite graphs*, SIAM Journal on Computing, 1973.
- P. Erdős, J. L. Selfridge, *On a combinatorial game*, 1973.
