# Solver research notes: computational draw proofs for (m,n,k)-games

These are working notes on the computational search side of the project, separate from the
formal Rocq and Lean development. They record what was built, what was measured, what the
literature already has, and what is planned next. All numbers come from this machine: a
24-thread CPU, 32 GB RAM, and an RTX GPU with 8 GB, sm_89. The GPU is used through WSL2 Ubuntu
with nvcc 12.4. Results here are **computational**: they are not formally verified unless this
file says so.

## 1. Problem statement

The theorem `mnk_value_win_or_draw` (strategy stealing, formalized in Rocq and Lean) says that
the value of any (m,n,k) game is either "first player wins" or "draw". So a draw proof only
has to show that **P1 cannot force a win**. That is an AND/OR proof:

- P1 nodes are AND nodes: every P1 move must be refuted.
- P2 nodes are OR nodes: one good reply is enough.

### Sound leaf tests used so far

Each test says that P1 cannot win from the position.

- **P1 to move, Maker-first Erdős–Selfridge bound (`es_inv`):** phi_P1 + max_free w_P1 < 2^k.
  - phi is the sum, over live P1 lines (lines with no P2 stone), of 2^(number of P1 stones).
  - w(x) is the same sum restricted to the lines through x.
- **P2 to move, Breaker-first bound:** phi_P1 < 2^k.
- **Other P2-to-move leaves:** P2 completes a line, or the board is full.

### Sound move restrictions used so far

- **Forced block:** if the opponent has exactly one completion cell, the side to move must
  take it.
- **Double threat:** two completion cells with no immediate win of our own means a loss.
- **Dead cells:** cells on no live line of either player are skipped, by the
  extra-stone-never-hurts argument.

## 2. What was built (chronologically)

### 2.1 CPU experiments (`scratchpad`, superseded)

| Program | Idea | Outcome |
|---|---|---|
| `es2_solver.c` | Exact null-window negamax; flags for ES bounds, refined ES bound, threats, ordering and dead cells | ES bounds cut (6,6,5) to 0.02 s and (8,4,4) to 49 s |
| `es3_solver.c` | Draw-certificate size with ES leaves and an exact P2 oracle | (5,4,4) 8,286 nodes; (6,6,5) 45,166 nodes |
| `par_solver.c` | Naive YBWC with OpenMP tasks | Slower on (8,4,4): speculative work |
| `lazy_solver.c` | Lazy SMP | Modest gain |
| `and_solver.c` | Split only at P1 (AND) nodes | Best CPU parallel design |
| `bfs_proof.c`, `bfs_chunk.c` | Level-synchronous greedy proof; chunked recomputation | Recomputation 2–5× for 7–180× less memory |
| `automorph.c` | Full automorphism group of the line hypergraph | Only (4,4,4), (5,5,5) and (6,6,6) have more than the geometric group |

**Pruning ablation (es2, nodes).** Flags 28 is everything except the ES bounds; flags 31 adds
them.

| Board | Flags 28 | Flags 31 | Value |
|---|---:|---:|---|
| (5,5,4) | 6.39M | 218K | draw |
| (6,4,4) | 3.75M | 132K | draw |
| (7,4,4) | 71.2M | 3.86M | draw |
| (6,5,4) | 5.81M | 51K | P1 win |
| (6,6,4) | 8.38M | 163K | P1 win |
| (8,4,4) | timeout | 49 s | draw |
| (6,6,5) | timeout | 0.02 s | draw |

### 2.2 GPU greedy proof (`mnk_gpu*.cu`, then `solver/gpu/mnk_proof.cu`)

**Level-synchronous AND/OR proof.**
- Only the P1-to-move levels are stored, since ply equals stone count, so levels never
  overlap.
- One fused kernel per level does the following for each node:
  1. Leaf tests.
  2. All P1 moves.
  3. Incremental D4/D2 canonicalization: g(P + c) = g(P) + g(c).
  4. P2-node tests.
  5. One greedy P2 reply.
  6. Full canonicalization.
- Duplicates are removed with a thrust sort + unique.

**Memory bound, no SSD.** A level that does not fit in the device buffer is split into sorted
halves held in host RAM, and each half is solved separately.

**P2 reply policy.**
- v1: argmax of 2·w_P1 + w_P2.
- v3 (threat-aware): the first candidate in that score order after which no single P1 move
  creates two threats. This test is a "pair map" over P1 lines that have k−2 P1 stones.

**Exact repair cascade (CPU, in-process).**
1. Every visited P1 node is recorded in a 2^34-bit Bloom filter. False-positive rate is about
   0.3%, and false positives cost only extra exact solves.
2. From each lost P2 node Y, climb to its bad P1 parents X = canon(Y − p), keeping only parents
   that are in the Bloom filter and are internal nodes.
3. From each bad X, find the P2 nodes W with greedy(W) = X.
4. Decide each W exactly with es2-style negamax. W holds → add it to the proof-leaf set H.
   W is lost → climb again.

**Verification pass.** The greedy proof is run again with H as leaves. Zero failures means
the draw proof is complete. The cascade is only a heuristic for finding H. Soundness rests on
the verification pass plus the exact solver.

### 2.3 Results of the GPU pipeline

| Board | Cells | P1 nodes (pass 1) | Greedy failures | Cascade levels | Result | Wall time |
|---|---:|---:|---:|---:|---|---:|
| (6,6,5) | 36 | 478 | 0 | 0 | draw proved | 0.2 s |
| (5,5,4) | 25 | 24,240 | 42 | 4 | draw proved | 1.0 s |
| (8,4,4) | 32 | 5,137,615 | 20,837 | 7 | draw proved | 124 s (GPU shared; ~3 s alone) |
| (9,5,5) | 45 | 2,038,608 | 0 | 0 | draw proved | 2.0 s |
| (10,5,5) | 50 | 200,157,445 | 594 | 4 | draw proved | 192.5 s |
| (7,7,5) | 49 | 1,681,370,394 | 682 | 3 | draw proved | 946 s |

**Greedy reply quality on (7,7,5).** Both runs searched about 1.65G positions.

| Policy | Distinct failures |
|---|---:|
| Plain greedy | 11,322 |
| Threat-aware | 682 |

The failures accrued linearly, at about 0.6 per million positions.

**Repair difficulty differs by board.**
- On (8,4,4), 88% of the first-level W nodes were themselves lost. The climb reached positions
  with 3–5 stones, yet every exact solve stayed under 10^6 nodes.
- On (7,7,5), 94% of the first-level W nodes were lost. By the third level all of them held.

### 2.4 Throughput observations

- (7,7,5) pass 1 took 583 s, against 362 s for verification on the same tree. The difference is
  Bloom insertion (5 random 64-bit atomics per node) plus the split bookkeeping.
- (10,5,5) pass 1 was 5× slower than its verification pass. Most of that time went to the early
  levels, which needs investigating; Bloom atomics alone do not explain it.
- The kernel is branchy: per-line loops, local-memory weight arrays w[64], and the
  threat-safety loop rescans all lines for each candidate. The planned shift-based, bit-sliced
  evaluation has not been implemented yet.

### 2.5 CPU AND/OR prover (`solver/mnk_prover.c`)

This prover is the response to the gap analysis in Section 4. It searches the OR nodes, uses
component and pairing leaves, and reduces AND branching. It is single-threaded C11, has two
engines (depth-first AND/OR search and df-pn), and has two rule modes:

- **MB (Maker–Breaker).** Every reduction is sound. A Breaker win implies "P1 cannot win".
- **SG (strong game).** P2's lines count. P1 moves are never pruned. P2 moves may be pruned,
  since fewer P2 options only make a draw proof harder. "P1 wins" therefore means only
  "not proved".

**Leaf tests, per connected component of the live P1-line hypergraph** (after subsumption):

1. **Twin pairs.** If u and v lie on exactly the same lines, they form a free pairing. The pair
   and its lines are removed, repeated to a fixed point.
2. **Maker-first ES** on the component.
3. **Double-threat cell:** the component is lost for Breaker outright.
4. **2-matching** (private pairs).
5. **Greedy pairs + ES.**
6. **Exact shared-pair cover** ("set matching"). Optionally followed by **cover + ES** on the
   long lines.

**Other reductions.**
- A P2-to-move leaf when all components but one are safe and the last one passes
  Breaker-first ES.
- Moves restricted to unsafe components.
- Dominance (lines(u) ⊆ lines(v)).
- An MB reduced state (dead stones and dead cells erased).
- Symmetry-canonical transpositions.
- An exact-key cache of component results.

**Two observations that made the cover practical.**

- **Pairs and directions.** A pair can only cover lines that contain both of its cells. On a
  grid those lines are collinear, so two lines sharing at most one free cell need *different*
  pairs. In any cover, a family S of such lines therefore gets |S| disjoint pairs, so S must
  have a 2-matching. This necessary condition is checked with Kuhn's algorithm at the root of
  the cover search and at every backtracking node. On (7,7,5) it refutes about half of all
  cover attempts immediately, and it cuts budget exhaustion by 100×.
- **Dominance as bitboards.** lines(u) ⊆ lines(v) holds exactly when v lies in the
  intersection of the lines through u. That replaces m² comparisons of 256-bit line sets with
  one AND per cell, and gives identical results. The same test finds twin pairs.

**Engineering notes.**
- **The df-pn thrashing was a node-identity bug.** Fixed by expanding the canonical
  representative, so the move list is a function of the TT key.
- **A too-small TT livelocks df-pn.** Evicted grandchildren return with fresh proof numbers.
  For example, (7,4,4) never finishes at 2^22 entries but takes 2 s at 2^24. Evictions are now
  reported.
- **MinGW-w64 GCC miscompiles AVX code on Windows.** It emits aligned AVX moves for 32-byte
  stack objects without realigning the stack (GCC bug 54412), which crashed the cover search.
  Build with clang on Windows instead.
- **Strong-game Breaker dominance must count P2's own lines.** Otherwise it prunes P2's
  counter-threats and loses the (3,3,3) draw proof. That is not unsound, but it is a lost
  proof.

**(7,7,5) progression.** Single thread, df-pn, MB rules unless noted. "Calls" are df-pn `mid`
calls; "evals" are node evaluations.

| Step | Calls | Evals | Time |
|---|---:|---:|---:|
| Flags 31: ES, 2-matching, components, subsumption, Maker restriction | — | — | timeout (300 s) |
| + dominance, reduced state, greedy hybrid, exact pair cover (budget 4000) | 9,500 | 97,942 | 44 s |
| + component cache, bitboard dominance | 9,500 | 97,942 | 28 s |
| + twin pairs, double-threat abort, greedy before cover | 9,476 | 97,866 | ~28 s |
| + 2-matching refutation at the cover root | 9,476 | 97,866 | 11 s |
| + refutation at every cover node, budget 20000 | 4,502 | 48,227 | 8.7 s |
| + partial cover+ES levels dropped, open-line cover state, Kuhn fast path | 4,502 | 48,227 | 5.8–7.9 s |
| + 1+ε thresholds (ε = 1/2) | 2,490 | 36,096 | 5.2 s |
| + Hsu et al. cover shape: pair score 4c − deg u − deg v, best 2 candidates per level | 4,700 | 65,518 | 1.2 s |

The SG rules give the same picture (for example 4,009 calls and 45,152 evals before 1+ε).
For comparison:
- the GPU greedy pipeline needed 1.68×10^9 P1 nodes and 946 s;
- Hsu et al. report 2.5 s on one thread of a Xeon Gold 6154.

**The last row trades proof size for leaf cost.**
- The limited cover search misses some covers, so the proof grows: calls ×1.9, evaluations
  ×1.8.
- Each evaluation became about 7× cheaper. The old search exhausted its 20,000-node budget on
  most infeasible components, even with the 2-matching refutation; a 2-way search fails within
  a few hundred nodes.
- Candidates tried per level (N), MB, one thread:

  | N | Pair score | Time |
  |---|---|---:|
  | all | c | 4.7 s |
  | 2 | c | 1.9 s |
  | 1 | Hsu | 2.3 s |
  | 2 | Hsu | 1.2 s |
  | 3 | Hsu | 3.0 s |

- Hsu et al. also found N = 2 best (Section 3.2).
- On (8,4,4) SG the change is neutral: 17.7 s against 18.5 s. The leaves there are cheap.

Wall times on this machine vary by about ±25% between identical runs, so the call and
evaluation counts are the reliable measures. The proof is now about 10^4–10^5 nodes, which is
the size the Section 4 diagnosis asked for.

**Effect of the 1+ε rule.** With ε = 1/2:

| Board | Evals before | Evals after |
|---|---:|---:|
| (8,4,4) MB | 729K | 157K |
| (7,7,5) MB | 48K | 36K |
| (7,4,4) MB | 521K | 493K |
| (7,4,4) SG | 484K | 614K (worse) |

The net effect is positive, so ε = 1/2 is the default.

**What the cover statistics showed** (before the refutation test).
- On (7,7,5), 77% of full-cover attempts exhausted their budget, and only 2% found a cover.
- Partial levels (cover the short lines, then ES) found covers easily, but ES then failed: 1
  success in 148K attempts.

Infeasibility was therefore the bottleneck, which led to the 2-matching refutation. Inside
the search, that test refutes 40–70% of nodes at every depth.

### 2.6 Parallel search (OpenMP, 24 logical processors)

**Where the serial time goes** ((7,7,5) MB, 4.7 s of evaluation in that run):

| Evaluation context | Time | Count |
|---|---:|---:|
| A node's own re-evaluation in `dfpn_mid` (component cache hits) | 0.01 s | 2,490 |
| Children of AND nodes (Breaker to move) | 1.21 s | 15,928 |
| Children of OR nodes (Maker to move) | 3.45 s | 17,678, of which 1,108 proved |

Evaluation is essentially the whole run time, and it is a pure function of the position.

**Scheme 1: `DFPN` with children evaluated in parallel (deterministic).**
- When a node is expanded, the children missing from the table are evaluated in parallel,
  then stored by the searching thread, so df-pn makes exactly the serial choices.
- **Evaluating every child failed.** Evaluations doubled (36K → 77K) with no speed-up. At an
  OR node the serial loop stops at the first proved reply, and good move ordering puts it
  first, so the extra children are the expensive failing cover searches.
- **Ordered speculation with cancellation fixed that.** Threads take children in index order.
  Once a child ends the loop, evaluations of later children are cancelled (the cover search
  polls every 64 nodes) and discarded, never cached.
- **Result:** the same proof at every thread count (2,490 calls), but the speed-up stops at
  about 1.7× (5.0 s → 2.9 s) from 8 threads on.
- **Why:** over 2,000 parallel batches, the single longest evaluation of each batch accounts
  for 2.36 s of the 2.73 s spent in batches. The critical path is individual evaluations.
  Lowering the cover budget shortens it, but the proof grows: 2.47 s at budget 5,000, 2.63 s
  at 10,000.
- **Two defects found by the validation matrix, both fixed.**
  1. **Not exact under eviction.** (8,4,4) SG differed from serial: 1,530,794 against
     1,530,097 calls. The serial run makes 653,595 evictions, and storing a whole batch at
     once changes which entries are evicted. Now the selection loop stores each prefetched
     child at the moment the serial loop would have evaluated it, and children past the
     cutoff are discarded. The table sees exactly the serial sequence of operations, and the
     counts match even with heavy eviction.
  2. **Slower than serial on cheap boards.** Waking a 24-thread team for every expansion
     costs about 65–95 µs, far more than a k = 4 evaluation. For example, (7,4,4) MB with
     flags 31 took 38 s against 3.1 s serial. A batch is now shared out only if (missing
     children) × (running mean evaluation cost) ≥ 0.5 ms, and the team is sized to the
     batch. Afterwards (7,4,4) took 3.16 s against 2.82 s serial, and (7,7,5) 2.89 s against
     5.96 s serial.

**Scheme 2: `PDFPN`, tree-parallel df-pn over a shared table.**
- Every thread runs df-pn from the root. A thread inside a node increments that entry's
  searcher count. When choosing a child, the others use the *virtual* key
  key × (1 + searchers) + searchers. Threads therefore spread over promising siblings
  (after Kaneko 2010 and Pawlewicz–Hayward 2013).
- If the virtual choice's true key already reaches the node's threshold, the thread takes the
  serial choice instead. Otherwise it would return at once and could spin.
- **Soundness under concurrency:**
  - a solved value is derived only from solved child values;
  - `tt_store` never replaces a solved entry with an unsolved one (a thread may finish a
    selection loop on values read before another thread solved the node);
  - every table and component-cache access is a whole-entry copy under a striped spin lock,
    with no nesting, hence no deadlock.
- With one thread, the program is exactly the serial program (2,490 calls).

| (7,7,5) MB, PDFPN | 1 thread | 4 | 8 | 12 | 24 |
|---|---:|---:|---:|---:|---:|
| Time | 5.24 s | 2.09 s | 1.44 s | 1.16 s | **0.91 s** |
| df-pn calls, all threads | 2,490 | 3,920 | 5,195 | 4,476 | 5,718 |

**Validation of PDFPN.**
- Setup: 13 boards, (3,3,3) through (8,4,4) plus (7,7,5); MB and SG; flags 31 and 1023;
  three runs each.
- Every verdict matches the known value. This includes the P1-win boards (4,3,3), (5,5,4)
  MB, (6,5,4), (6,6,4) and (8,4,4) MB, which come out as Maker wins under MB and "not proved"
  under SG.
- It is faster than serial on every non-trivial board. Final build, same machine, same run of
  the matrix:

| Board, rules, flags | Serial DFPN | DFPN, 24 threads (same calls) | PDFPN, 24 threads (3 runs) |
|---|---:|---:|---:|
| (7,7,5) MB 1023 | 4.69 s | 2.75 s | 0.89–0.92 s |
| (7,7,5) SG 1023 | 5.54 s | 2.66 s | 1.02–1.14 s |
| (8,4,4) SG 1023 | 23.8 s | 24.3 s | 2.30–2.45 s |
| (8,4,4) SG 31 | 16.3 s | 16.6 s | 1.96–2.34 s |
| (8,4,4) MB 31 (Maker wins) | 37.2 s | 39.4 s | 0.20–0.79 s |
| (7,4,4) MB 31 | 3.32 s | 3.53 s | 0.40–0.65 s |

- **DFPN with 24 threads** gives exactly the serial call count on all 50 configurations,
  including (8,4,4) MB with flags 31 at 7.3M calls. It helps only where evaluations are
  expensive ((7,7,5)); elsewhere the cost gate keeps it within about 5–10% of serial.
- **PDFPN on (8,4,4) MB with flags 31** is 50–180× faster than serial. A disproof needs only
  one winning Maker line, and with many threads exploring siblings, one of them finds a short
  win long before serial df-pn's ordering reaches it.

PDFPN is therefore the default engine. DFPN stays available for exactly reproducible runs.

The speed-up is about 6× on 24 logical processors. Hsu et al. report 2.5 s on **one
thread** of a Xeon Gold 6154 at 3.0 GHz (Section 3.2). With the cover shape above, this
prover was about 2× slower than that per thread (4.7–6.6 s serial).

**After adopting Hsu et al.'s cover shape** (Section 2.5, last row). The same matrix was re-run
on 2026-11-19:
- all 50 verdicts are identical to the run above;
- DFPN-24 again reproduces the serial call count on every configuration;
- all 150 PDFPN runs are correct.

| Board, rules, flags | Serial DFPN | DFPN, 24 threads | PDFPN, 24 threads (3 runs) |
|---|---:|---:|---:|
| (7,7,5) MB 1023 | 1.19 s (4,700 calls) | 1.12 s | 0.23–0.24 s |
| (7,7,5) SG 1023 | 1.25 s (4,681 calls) | 1.09 s | 0.24–0.26 s |
| (8,4,4) SG 1023 | 17.5 s | 17.3 s | 2.33–2.49 s |
| (8,4,4) SG 31 | 12.5 s | 12.5 s | 2.11–2.67 s |
| (8,4,4) MB 31 (Maker wins) | 30.6 s | 30.9 s | 0.22–0.90 s |
| (7,4,4) MB 31 | 2.68 s | 2.76 s | 0.46–0.49 s |

- **Per thread:** (7,7,5) now takes 1.2 s serial against Hsu et al.'s 2.5 s. The CPUs differ,
  so this is a comparison of published figures, not a controlled one.
- **24 threads:** 0.23–0.26 s, about 10× under their figure.
- **Small proofs:** DFPN-24 no longer gains on (7,7,5). Its leaves are now cheap enough that
  the cost gate keeps most nodes serial.

## 3. Literature: what is already known

### 3.1 Hsu, Ko, Hsueh, Wu, *Solving 7,7,5-game and 8,8,5-game*, ICGA J. 40(3) 2018

- **DOI:** 10.3233/ICG-180061.
- The 7,7,5 and 8,8,5 games are solved as draws, with methods based on pairing strategies and
  potential weights.
- Solve times: about 1 minute for 7,7,5 and about 3 days for 8,8,5.

### 3.2 Hsu, Ko, Chen, Wei, Hsueh, Wu, *On solving the 7,7,5-game and the 8,8,5-game*, TCS 815 (2020) 79–94

- **DOI:** 10.1016/j.tcs.2020.02.023 (ScienceDirect PII S0304397520301146).

- **Abstract:** an AND/OR search tree algorithm for mnk-games, three novel methods to reduce
  the branching factor, and a new method for finding pairing strategies.
- **Keywords:** pairing strategy, relevancy-zone.
- **Solve times:** 7,7,5 in 2.5 s; 8,8,5 draw in 17.4 h (62,634 s).
- **Hardware:** "The experiments were performed with **one thread** on the machine equipped
  with Intel(R) Xeon(R) Gold 6154 CPU @ 3.00 GHz" (Section 6). The 2.5 s is single-threaded.
- **Sources read (2026-11-19):**
  - the paper itself, supplied by the user;
  - W.-Y. Hsu's master's thesis, *Solving 7,7,5-Game and 8,8,5-Game* (National Chiao Tung
    University, July 2019; advisors J.-C. Chen and I-C. Wu). It contains the same tables and
    the same hardware statement.

  Both are scans without a text layer; they were read as rendered page images.

**Search.** Plain recursive AND/OR search with a transposition table, no proof numbers.
- Maker nodes are AND and Breaker nodes OR.
- Moves are ordered by potential weight w(v) = Σ_{e∋v} 2^{M(e)} over unblocked lines, where
  M(e) is the number of Maker marks on e.
- Early return: at a Breaker node, each Breaker move is first tested for an immediate pairing
  strategy.

**Three reductions** (Section 4).
1. **Partial pairing (Theorem 1).**
   - Definition: V_pair is a set of free cells that can be split into disjoint pairs so that
     every line meeting V_pair contains a whole pair.
   - (V, E) and (V − V_pair, E − E_pair) have the same value.
   - Implemented only for *mutually dominated* cells (E(u) = E(v), removed repeatedly) plus
     cells on no line. That is exactly our twin pairs (flag 512).
2. **Vertex domination (Theorem 2).** If E(v_i) ⊇ E(v_j), the dominated cell v_j can be
   skipped by either player. This is our dominance (flag 64). They apply it to both players;
   we apply it to Breaker always and to Maker in MB only.
3. **Breaker relevance zones (Section 4.3).** This is what we lack.
   - R(s) is the set of cells Breaker might mark under its winning strategy s.
   - **Property 2:** if Breaker wins after Maker plays v, using strategy s, then Breaker
     also wins after any Maker move v' ∉ R(s), with the same s.
   - **Property 3:** at a Maker node, if the zones of the refuted moves v_1..v_t have an
     empty intersection, the node is a Breaker win with zone ∪ R(s_i).
   - Algorithm 4: a Maker node keeps V_tocheck ← V_tocheck ∩ R_subtree after each refuted
     move, skips moves outside V_tocheck, and returns R = ∪ R_subtree.
   - Zones at leaves come from the pairing strategy: R = the cells of the pairs (Theorem 3).
   - Zones of reduced games are extended by the partial pairs (Theorem 4) and by the
     dominating cell for each skipped dominated move (Theorem 5).
   - Breaker nodes return {v} ∪ R(child).

**Pairing search** (Section 5, Algorithms 2, 3 and 9).
- Pairs may be shared by several lines. This is the same "set matching" as our exact cover.
- Greedy rule 1: a free line with exactly two unassigned cells takes them as its pair
  (forced).
- Greedy rule 2: two cells with identical free-line sets form a pair (twins).
- Then backtracking on the line with the fewest unassigned cells (the hyperedge score).
  Candidate pairs on that line are ranked by the pair score
  2|E(v₁)∩E(v₂)| − |E(v₁) △ E(v₂)|, and **only the best N candidates are tried per level.**
- Effect of N on (7,7,5): N = 0 (greedy rules only) 1,870 s; **N = 2: 2.5 s**; N = 3: 9.4 s;
  N = 4: 16.7 s; N = 5: 29.0 s. On 8,8,5 only N = 2 finished within 72 h.

**Ablation without pairing terminals** (Table 1, 7,7,5):

| Methods | Time |
|---|---:|
| All three methods | 7,457 s |
| Partial pairing + r-zones | 31,441 s |
| Partial pairing + domination | 33,856 s |
| Any one method alone | > 72 h |

They give no ablation of the r-zones *with* pairing terminals on.

**Earlier result cited by them.** C.-Y. Chen (2013 master's thesis, National Taiwan Normal
University) solved 7,7,5 in about 5 days on 10 threads, with df-pn and heuristics.

**Comparison with this prover.**
- Same per-node ideas: pairing leaves including shared pairs, twins, domination, potential
  ordering.
- Things they have that we lack:
  - relevance zones;
  - a far cheaper pairing search (N = 2 per level, against our 20,000-node budget with a
    2-matching refutation).
- Things we have that they lack:
  - df-pn with 1+ε;
  - component decomposition and the component cache;
  - ES and pairs+ES leaves;
  - the 2-matching infeasibility test;
  - symmetry reduction;
  - parallel search.
- Per thread they remain about 2× faster on 7,7,5.

### 3.3 Czifra, Csóka, Zombori, Makay, *Towards solving the 7-in-a-row game* (arXiv 2107.05363)

**Search.** Proof-number search (PNS) with a symmetry-aware transposition table.

**Leaf tests and reductions.**
- **Breaker win stop:** potential below 1.
- **Maker win stop:** under optimal Breaker play, Maker wins exactly when Maker can move into
  the crossing of two 2-lines.
- **Forced moves.**
- **Dead-square elimination.**
- **Dominated squares:** E(u) ⊆ E(v); mutually dominating squares form a partial pairing.
- **Components:** splitting at cut vertices into independent subgames.

**Ablation (proof size, 4×n boards).**

| Technique | Proof size when it is removed |
|---|---|
| Forced moves | 70× larger |
| Dominated squares | 3.6–15.6× larger |
| Components | up to 3× larger |
| Heuristic PN/DN initialization | 24–42× larger |

**Isomorphism.** Canonical forms cut nodes about 10× but cost more time than they saved
(hypergraph canonical forms; ours are board-symmetry forms and cheap).

### 3.4 Uiterwijk, *Set Matching: an enhancement of the Hales–Jewett pairing strategy*, ICGA J. 2018

This is relevant to finding pairings when one pair must cover several lines.

## 4. Gap analysis: what they do that we do not

| Technique | Hsu et al. | Czifra et al. | Ours (GPU pipeline) | Ours (`mnk_prover.c`, now) |
|---|---|---|---|---|
| OR nodes searched (best reply found) | yes (AND/OR search) | yes (PNS) | **no**: one greedy reply, repaired afterwards | yes (df-pn, 1+ε) |
| Pairing-strategy leaves | yes (core method: greedy rules, then the best N = 2 pairs per level) | partial pairings | **no** | yes: 2-matching, shared-pair cover (their score, N = 2, plus a 2-matching refutation at each node), twin pairs |
| Relevance zones in draw proofs | yes (Breaker r-zones; essential without pairing leaves: Table 1) | no | **no** | yes, optional (flag 1024, off by default: small gain, Section 5.7) |
| Potential (ES) leaves | potential weights | yes | yes | yes (per component) |
| Component decomposition | ? | yes (cut vertices) | **no** | yes (connected components, exact-key cache) |
| Dominated squares / partial pairing | yes (credited) | yes | dead cells only | yes (bitboard test; SG-aware for P2) |
| Symmetry-aware transpositions | yes | yes (dropped: too slow) | yes (cheap D4) | yes (canonical expansion) |
| Massive GPU parallelism | no | no | **yes** | no GPU; 24-thread CPU search (PDFPN) |
| Formal (Rocq/Lean) soundness of leaf rules | no | no | **yes** (ES, strategy stealing) | ES, strategy stealing, mid-game pairing (`pairing_no_maker_win`, Rocq); Breaker-certificate checker `check_br` with ES, pairing and move-bound leaves (no component or hybrid leaves yet) |

**Diagnosis.** The (7,7,5) proof DAG has 1.68×10^9 P1 nodes. A 2.5 s solve implies a proof
smaller by 3–4 orders of magnitude. The gap is **algorithmic (proof size)**, not throughput.
A single greedy reply at every OR node can never find small proofs, and ES leaves fire much
later than pairing or component arguments do.

## 5. Plan: improvements, with soundness arguments

### 5.1 Sum-of-games leaf test

Decompose the live P1-line hypergraph into connected components (cells linked by live lines).
P2 always answers in the component where P1 just played, so the game is a sum of independent
Maker-first Maker–Breaker games.

**Each component is safe** if any of the following holds:
- **(a) Component ES:** phi_C + max w_C < 2^k, using free-cell weights 2^-|F_L|. This is
  implied by global `es_inv`, so it is strictly stronger.
- **(b) Pairing:** a 2-matching of lines to private free cells, after subsumption reduction.
- **(c) Exact solve:** a tiny exact Maker–Breaker solve if the component is small.

Subsumption: if F_L ⊆ F_L', drop L'. Blocking L also blocks L'.

**Leaf conditions.**
- **P1 to move:** the position is a leaf when every component is safe.
- **P2 to move:** the position is a leaf when every component but one is safe, and one P2 move
  makes that last one safe.

### 5.2 Restrict P1 moves to unsafe components

Moves into a safe component are answered inside it, and that component stays safe forever.
Lines never cross components, and P2 stones only kill P1 lines. P2's complete strategy is:

- the proof tree for moves in unsafe components;
- the component strategy for moves in safe components;
- any move for dead cells, since extra P2 stones never hurt.

So the AND branching factor drops to the number of cells in unsafe components. This is the
same effect a relevancy zone has.

### 5.3 Search OR nodes

Search the P2 nodes instead of committing to one greedy reply.

- **Engine:** depth-first null-window AND/OR search (alpha-beta with TT, the es2 engine), with
  replies ordered by the threat-aware score, so the first reply is usually a proof. Upgrade to
  df-pn if ordering is not enough.
- **Parallelism:** 24 threads, splitting at AND nodes (the `and_solver` design).

### 5.4 Keep the GPU for what it is good at

- Breadth-first verification of a finished proof DAG: every node checks independently.
- Exhaustive leaf screening.

### 5.5 Formal certificate

A proof small enough (about 10^5–10^6 nodes) could be checked inside Rocq with the existing ES
theorems plus a pairing lemma. That would be a machine-checked (7,7,5) draw, which as far as
we know nobody has.

### 5.6 Review of the engineering handout (`solver/mnk_solver_optimization_rocq_certificate_engineering_handout.md`)

**Adopted and measured.**
- **Twin-pair elimination (3.2.2).** Implemented with the bitboard test. The reduction is
  without loss for the cover search: any cover can be rewritten to use the twin pair.
- **2-line conflict abort (3.3.2).** Strengthened: a component with a double-threat cell is
  unsafe outright, so all four tests are skipped. The Breaker-first potential is still
  computed, because Breaker moving first can take that cell.
- **Greedy hybrid before the exact cover (3.3.1).**
- **Kuhn fast path through an `owned` bitboard (5.3).**
- **Wall-clock timer (4.4.1).** Uses `timespec_get`, which is portable C11.
- **1+ε thresholds (4.2).** ε = 1/2 measured best.
- **No double evaluation in `dfpn_mid` (4.3).**
- **24-thread parallel df-pn (4.4).** Shared table with striped locks and virtual proof
  numbers (Section 2.6), plus a deterministic variant that only evaluates children in
  parallel.

**Not needed at present (measured).**
- **Collinear O(n) subsumption (3.2.1)** and the **nibble symmetry table (5.1).** Together
  under 1% of the profile.
- **Protecting PROVED entries from eviction (4.3.3).** There are 0 evictions at 2^24 entries.

**Deferred: high value, larger work.**
- Constructive relevance zones with certificate export (3.1, 7).
- A standalone `mnk_verify.c`.
- The GPU items (6.x):
  - VRAM over-commit: the guard sounds plausible for the (10,5,5) pass-1 slowdown, but is not
    verified yet;
  - warp-aggregated compaction;
  - pre-extracted (k−2)-lines;
  - a word-blocked Bloom filter.

**Corrections to the handout.**
- **3.1.2 sibling pruning.** The argument goes through the null-move position (M, B ∪ {b0})
  with Maker to move, as the handout's certificate schema in fact does. It does not go through
  "remove m0 from T0's position". The latter needs an extra monotonicity step, because with m0
  free Maker can still play it later.
- **The cover pre-check.** It applies exactly when two size-2 lines share a cell *with
  different partners*. Two identical size-2 lines are fine.

### 5.7 Design: Breaker relevance zones in df-pn (MB only)

**Definition.** A *zone* of a Breaker-win position P is a set Z of free cells such that
Breaker still wins after Maker is given every free cell outside Z, at no cost in tempo. This
is Hsu et al.'s R(s), stated as a property of the position rather than of a strategy, so it
can be stored in the TT next to a proved value.

**Pruning (their Property 2).** At a Maker node P, suppose the child P + v is proved with zone
Z. Then every sibling P + u with u ∉ Z ∪ {v} is proved too.
- *Why:* compare P + u with P + v + (free \ Z \ {v}) given to Maker, which is a Breaker win.
  - Maker's cells in P + u are a subset of Maker's cells there, since u ∉ Z.
  - P + u has the same Breaker cells and a superset of the free cells, Z ⊆ free(P + u).
  - Breaker plays that position's strategy and treats every Maker move outside Z as a pass;
    in Maker–Breaker an extra Breaker move never hurts.

**Zones returned upward.**
- **Breaker node:** if Breaker's move b proves the child with zone Z, the node's zone is
  {b} ∪ Z.
- **Maker node:** the union of
  - the zones of the children proved by search;
  - the strategy cells of the safe components, whose moves `restrict_maker` skips;
  - the dominating cell of every skipped dominated move (their Theorem 5).

  Each skipped child u lies outside some proved sibling zone Z_v ⊆ R, and the comparison
  above still holds inside the smaller game.
- **Leaves:** the strategy cells of each component.
  - Cells used by a 2-matching, a cover or twin pairs: every line keeps a pair, so the
    cells outside cannot complete it.
  - All free cells of an ES-safe component: Erdős–Selfridge needs the whole component.
  - The empty set for a full board.

**Fit with this prover.**
- **Canonical states.** A child's zone is stored in that child's canonical coordinates, so
  it must be mapped back through the inverse of the symmetry that `symmetry_canonical`
  applied. `symmetry_canonical` must therefore report which transform it used. When several
  transforms give the same image, any of them yields a valid zone, because they differ by an
  automorphism of the child.
- **Reduced state.** It only turns dead free cells into Breaker stones. Maker gains nothing
  from dead cells, so zones in reduced coordinates stay valid.
- **df-pn.** At an AND node, while children are looked up, keep `allowed`, the intersection
  of Z_v ∪ {v} over the proved children seen so far. Children outside `allowed` count as
  proved (proof number 0).
  - The mask is recomputed on every visit from the TT, so nothing new is stored for open
    nodes.
  - If a proved child's entry is evicted, the only loss is less pruning.
- **TT cost.** A 64-bit zone on proved entries takes `TTEntry` from 32 to 40 bytes: 640 MB
  at 2^24 entries, in RAM.
- **Component cache.** Its entries need the strategy cells as well as the verdict.
- **SG.** Zones apply to MB only. In SG, cells given to Maker would destroy P2's own winning
  lines, which the proof may rely on. That is no loss: an MB proof already shows that P1
  cannot win the strong game.

**Expected gain.**
- Hsu et al. measured zones as essential with pairing leaves off: 7,457 s with them, over
  72 h without.
- With pairing leaves on, the gain is not measured. Our components and `restrict_maker`
  already skip the safe parts of the board.
- The larger effect is expected on (8,8,5), where 17.4 h is their figure to beat.

**Measured outcome (implemented 2026-11-19, flag 1024).** Serial DFPN, MB rules:

| Board | Zones | Search calls | Evaluations | Time |
|---|---|---:|---:|---:|
| (7,7,5) | off | 4,700 | 65,518 | 1.32 s |
| (7,7,5) | on | 3,214 | 54,919 | 1.30 s |
| (6,4,4) | off | 5,040 | 27,964 | 0.07 s |
| (6,4,4) | on | 3,795 | 21,712 | 0.06 s |

- On (7,7,5), 1,070 Maker moves were refuted by a sibling's zone. Zones cover about 80% of
  the free cells of a refuted child (36.8 of 46) and 98% at a proved Maker node (44.4 of 45.1).
  A zone must contain a blocking pair of every live line, so it can never be small.
- Components and `restrict_maker` already skip the safe parts of the board, which is most of
  what zones would prune. The serial time does not improve, because zone bookkeeping costs
  about what the skipped evaluations save. PDFPN-24 goes from about 0.24 s to 0.20 s.
- Validation: 98 configurations with flags 31, 1023 and 2047 (plus MB variants 2039 and 1983).
  All verdicts agree, and the internal consistency check (no Maker win outside a sibling's
  zone) never fired.
- **Decision: off by default.** A certificate that uses zone pruning needs its own Rocq lemma
  (Property 2 above, as a theorem about `maker_wins`). For a 1.5× smaller search tree and no
  speed-up, that is not worth it yet. The code stays for (8,8,5), where the trade-off may differ.

## 6. Status log

- **2026-11-18:**
  - The GPU pipeline proved (5,5,4), (6,6,5), (8,4,4), (9,5,5), (10,5,5) and (7,7,5) to be
    draws (computational).
  - (7,7,5) and (8,8,5) were already known draws, from Hsu et al.
  - No published result was found for (9,5,5) or (10,5,5). They may well be known, or settled
    by pairing arguments, so they are not claimed as new.
  - Runs on (11,5,5) and (12,5,5) were stopped at the user's request.
  - `mnk_prover.c` and `gpu/mnk_proof.cu` were rewritten in a consistent, documented style:
    - typed option, analysis and search structures;
    - copy-based transposition-table access;
    - owned device buffers (RAII);
    - lazily allocated per-thread exact-solver tables.

    The GPU rewrite reproduces the original exactly: the same node, failure and cascade counts
    on (5,5,4), (8,4,4), (6,6,5) and (7,6,5).
  - The CPU prover proves (7,7,5) on one thread:
    - MB rules: 2,490 df-pn calls, 36,096 evaluations, about 5.5 s;
    - SG rules: 2,849 calls, 39,720 evaluations, about 7.7 s.
  - The validation matrix covers (3,3,3) through (8,4,4) under MB and SG, flags 31 and 1023,
    and DFS and df-pn. It includes the negative tests (4,3,3), (6,5,4) and (6,6,4), and every
    verdict matches the known values.
- **2026-11-19:**
  - Parallel search was added (Section 2.6).
  - PDFPN, the tree-parallel df-pn over a shared locked table, is now the default. It proves
    (7,7,5) in 0.89–0.92 s (MB) and 1.02–1.14 s (SG) on 24 logical processors, against 4.7 s
    and 5.5 s serial in the same run. Validation: 150 PDFPN runs, all verdicts correct.
  - The deterministic DFPN mode evaluates children in parallel and reproduces the serial
    proof exactly, evictions included. It reaches about 2× on (7,7,5).
  - The Hsu et al. TCS paper and W.-Y. Hsu's thesis were read, both supplied by the user
    (Section 3.2). Their 2.5 s is single-threaded on a Xeon Gold 6154.
  - Their cover-search shape was adopted:
    - pair score 2|E(u)∩E(v)| − |E(u)△E(v)|;
    - only the best 2 candidate pairs tried per level.

    (7,7,5) MB now takes 1.2 s serial and 0.23–0.24 s with PDFPN on 24 threads. All 50
    validation verdicts are unchanged.
  - Breaker relevance zones were implemented (Section 5.7): 1.5× fewer search calls on
    (7,7,5) MB, no serial speed-up. They are off by default (flag 1024 turns them on), since
    a certificate using them would need its own Rocq lemma.
  - Back to the formal goal. `MNKMakerBreaker.v` (Rocq, 0 axioms) proves:
    - a Breaker win from the empty board makes the strong game a draw;
    - a Breaker win for (m, n, k) is a Breaker win, and a draw, for every (m, n, k') with
      k' >= k;
    - the pairing strategy at any mid-game position: the pairing leaf rule for a future
      draw-certificate checker.
  - Further formal results (Rocq, 0 axioms):
    - **Embeddings** (`maker_wins_simulate`): a Breaker win for (m, n, k) is a Breaker win,
      and a draw, for every board fitting inside m × n (either way round) with k' >= k.
      One draw certificate therefore covers a whole family of boards.
    - **Hales–Jewett** (`MNKHalesJewett.v`): every (m, n, k) game with k >= 9 is a draw, for
      all m, n. It uses one 8 × 8 periodic domino pairing, found by
      `solver/hales_jewett_tile.py` and checked by computation over one period.
    - **Maker–Breaker win certificates** (`MNKMakerBreakerCert.v`, generator
      `solver/mb_win_cert.c`): (3,3,3) in 17 nodes within 4 moves, (5,5,4) in 1,993 nodes
      within 5 moves, checked in about 3 s. The generator now keeps the fastest win; a
      1,945-node certificate exists for (5,5,4), but it takes 6 moves. Replies after which Maker has a winning cell are settled by the checker,
      so a threat costs one listed reply. Since tic-tac-toe is a draw, Maker–Breaker and the
      strong game provably differ. The known (5,5,4) draw can never come from a Breaker
      strategy: it needs a strong-game draw checker.
    - The generator's plain search (iterative deepening, symmetric table, no Breaker-safe
      leaves) did not finish (8,4,4). The first run's table passed 9 GB. A second run, with
      Breaker replies ordered by value and an Erdős–Selfridge prune, was stopped after about
      6 minutes at 2.3 GB. The df-pn prover proves that win in 0.37 s, so exporting its
      disproof tree is the way to larger Maker wins.
  - **Breaker certificates** (`MNKBreakerCert.v`, generator `solver/breaker_cert.c`, Rocq,
    0 axioms). One checker serves draws and speed lower bounds. It takes a move bound
    (`Some d` or `None`) and has three leaf rules: Erdős–Selfridge (`es_inv`), mid-game
    pairing, and "too slow", i.e. every open line lacks more than d Maker stones
    (`short_no_win`). The generator runs an AND/OR search on canonical positions, then an
    exact minimisation of the certificate size.
    - Speed (optimal = fewest own moves, both bounds formal):
      - (m,n,3), m,n >= 4: exactly 3 moves (5 plies). The lower bound needs no certificate.
      - (3,n,3), 4 <= n <= 21: exactly 4 moves (7 plies); 133 to 3,907 positions, 3n + 1
        nodes each.
      - Maker–Breaker (3,3,3): exactly 4 moves (73 positions).
      - Maker–Breaker (5,5,4): exactly 5 moves (601 positions).
    - (5,4,4): Breaker win in 381 positions (21 nodes, 170 ES and 190 pairing leaves),
      checked in 0.25 s. So every board inside 5 × 4 (either way round) with k >= 4 is a
      formal draw.
    - Limits: with only these leaves the search does not finish (6,4,4), (6,6,5) or (7,6,5)
      (2^27 table entries, about 3 GB, after 150–200 s). The prover needs 5,040, 7 and 337
      calls, thanks to components, subsumption, the pairing + ES hybrid and dominance. Next
      step: Rocq lemmas for those rules (decomposition into independent components first),
      then certificates that use them.
    - The (3,n,3) certificates grow as 3n + 1 nodes, which suggests a uniform Breaker
      strategy (answer next to Maker's first stone in its row, then block the one line
      holding both Maker stones). A direct Rocq proof could give "exactly 7 plies" for
      every n.
