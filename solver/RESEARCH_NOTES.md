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

The SG rules give the same picture (for example 4,009 calls and 45,152 evals before 1+ε).
For comparison:
- the GPU greedy pipeline needed 1.68×10^9 P1 nodes and 946 s;
- Hsu et al. report 2.5 s.

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

## 3. Literature: what is already known

### 3.1 Hsu, Ko, Hsueh, Wu, *Solving 7,7,5-game and 8,8,5-game*, ICGA J. 40(3) 2018

- The 7,7,5 and 8,8,5 games are solved as draws, with methods based on pairing strategies and
  potential weights.
- Solve times: about 1 minute for 7,7,5 and about 3 days for 8,8,5.

### 3.2 Hsu, Ko, Chen, Wei, Hsueh, Wu, *On solving the 7,7,5-game and the 8,8,5-game*, TCS 815 (2020) 79–94

- **Abstract:** an AND/OR search tree algorithm for mnk-games, three novel methods to reduce
  the branching factor, and a new method for finding pairing strategies.
- **Keywords:** pairing strategy, relevancy-zone.
- **Solve times:** 7,7,5 in 2.5 s; 8,8,5 draw in 17.4 h.
- **Access:** the full text could not be retrieved (paywalled: ScienceDirect returns 403, and
  no repository copy was found). The exact definitions of the three branching-factor
  reductions and of the pairing-finding method are therefore **not verified here**.
- **What a citing paper credits them with** (Czifra et al., below):
  - partial pairings that remove parts of the hypergraph without changing the proof value;
  - relevance zones in breaker-win (draw) proofs;
  - transposition tables;
  - move ordering by potential.

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
| Pairing-strategy leaves | yes (core method) | partial pairings | **no** | yes: 2-matching, exact shared-pair cover, twin pairs, pairs+ES |
| Relevance zones in draw proofs | yes | no | **no** | **no** (next) |
| Potential (ES) leaves | potential weights | yes | yes | yes (per component) |
| Component decomposition | ? | yes (cut vertices) | **no** | yes (connected components, exact-key cache) |
| Dominated squares / partial pairing | yes (credited) | yes | dead cells only | yes (bitboard test; SG-aware for P2) |
| Symmetry-aware transpositions | yes | yes (dropped: too slow) | yes (cheap D4) | yes (canonical expansion) |
| Massive GPU parallelism | no | no | **yes** | no (single thread so far) |
| Formal (Rocq/Lean) soundness of leaf rules | no | no | **yes** (ES, strategy stealing) | ES and strategy stealing; pairing lemma not yet |

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

**Not needed at present (measured).**
- **Collinear O(n) subsumption (3.2.1)** and the **nibble symmetry table (5.1).** Together
  under 1% of the profile.
- **Protecting PROVED entries from eviction (4.3.3).** There are 0 evictions at 2^24 entries.

**Deferred: high value, larger work.**
- Constructive relevance zones with certificate export (3.1, 7).
- A standalone `mnk_verify.c`.
- 24-thread parallel df-pn (4.4).
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
    - SG rules: 2,849 calls, 39,720 evaluations, about 7.7 s. The validation matrix covers (3,3,3) through (8,4,4) under MB
    and SG, flags 31 and 1023, and DFS and df-pn. It includes the negative tests (4,3,3),
    (6,5,4) and (6,6,4), and every verdict matches the known values.
