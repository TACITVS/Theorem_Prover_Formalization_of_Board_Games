# Research 028: fragment codes, and code-leaf trees pushed backwards

Status: **computations and proof tooling; no new theorem about the game.** The
value of 5x5x5 Qubic is still unresolved.

## Part B: strategy trees with code leaves (tooling, plus a cautionary finding)

`ZZLinearTrees.v` already proves that a tree accepted by `linear_treeb` is a
sound Black non-loss strategy. Each node gives Black's reply to every White
request, and each leaf is a whole-line code leaf. This part adds:

- **`tree_extend.py`:** searches for such trees backwards from a position, to a
  fixed depth.
- **`adaptive.py`:** extra depth only on the branches that need it.
- **`export_tree.py`:** writes a tree as a Rocq file. Each leaf stores only its
  information set `I0`, as one 125-bit mask. A small Gaussian elimination inside
  Rocq builds the decoders for `I0` and for the remaining free cells, and
  `linear_leafb` re-checks them. So no Python output is trusted.
- **`export_split.py` and `verify.py --split`:** check large trees as one lemma
  per White request, about 10 requests per file. The files compile and pass
  `rocq check -norec` in parallel, and each finished `.vo` file is a resume
  checkpoint, so no run has to exceed 10 minutes.

The pipeline works. It kernel-checked depth-1 trees at the research-021 witness
game after 18 plies and the stronger game after 20 plies. It then compiled a
depth-2 tree with 12,911 leaves at the witness game after 16 plies, in 13
parallel parts in about 4 minutes.

**Cautionary finding: those positions are trivial.** In both research-021
games, White's moves do not defend. Black already threatens to complete
**two** lines:

| game, rounds played | Black's winning cells |
| --- | --- |
| witness, rounds 8–10 | 0 and 20 |
| stronger, rounds 10–11 | 33 and 43 (and 83 at round 11) |

White can block only one of them, so these positions, including research-021's
own leaves, are forced Black **wins**. Black's apparently "universal" reply,
corner 0, was just Black completing a line. The earlier search did not model
Black's immediate wins, which is also why six branches had looked hard.

The kernel results are correct but say nothing new, so those generated files
are not kept. The search now handles Black's immediate wins as terminal
(`'win'`). It also refuses to start from a position where Black already
threatens to win, unless `--allow-trivial` is given.

**What would be meaningful.** The same tree-plus-code-leaf certificates need
positions reached by strong White play, not by the research-021 witness games.
Those have to come from an engine that plays White well.

**Probe from a threat-free position.** The stronger game after 16 plies
(stronger@8) is the last position in it where neither side threatens anything.
From there, a depth-2 search with up to 40 Black replies per node covered **0
of 109** White moves (about 60 s). So, starting from a non-trivial position,
two rounds of explicit tree followed by whole-line code leaves are nowhere near
enough. This fits the Part A finding: each round of look-ahead lacks 2–3 GF(2)
relations, and a depth-2 tree recovers only what two Black stones can block.

## Part A (computation): fragment codes

Status: **computations only; negative result.**

Research 027 proposed *fragment codes*. Each live line (no Black stone) gets a
fragment of at least two of its free cells. The GF(2) span of the fragments must
have two disjoint information sets among the free cells, meaning the column
matroid has two disjoint bases. Whole-line codes (research 021) are the special
case where each fragment is the line's whole free part.

**Soundness needs no new proof.** `linear_information_minimax`
(`QUBIC-PROOF-GATE-001/agent/ZLinearDefense.v`) holds for any XOR-closed code
whose coverage says that each live line contains a nonzero codeword. A
fragment-code certificate is such a code. Formalising one would only need a
checker that generalises `linear_leafb` from residual rows to arbitrary rows.

The plan was to formalise fragment codes only if they certify Black at least two
rounds earlier than existing leaves. They do not, so no formalisation was done.

## Step 1: small hypergraphs (`fragment_search.py smoke`, about 1 s)

The test used 300 random linear hypergraphs on 4–9 vertices with edges of size 2–4.
Every fragment system was enumerated, and each hypergraph was solved exactly as
a Maker–Breaker game with Maker moving first.

| quantity | count |
| --- | ---: |
| hypergraphs admitting a fragment code | 209 |
| ... of which are Maker wins (would be a soundness bug) | **0** |
| ... of which have no pairing strategy | 1 |
| ... of which fail the Erdős–Selfridge bound | 22 |
| matroid-partition answers checked against brute force | 3000 (all agree) |

## Step 2: backward walk along the known games (`fragment_search.py backward`, about 100 s)

Each game is cut back to earlier positions, all with White to move. Three games
were used:

- the research-021 witness (10 rounds);
- the research-021 stronger witness (11 rounds);
- the research-013 pairing position (10 rounds; its stone sets carry no move
  order, so its prefixes are positions but not necessarily game prefixes).

At each position the script tests:

- a pairing, by max flow;
- a whole-line code, by exact matroid partition;
- a fragment code, by 6 s of annealing over fragment choices. It minimises GF(2)
  rank and runs an exact partition test whenever `2 * rank <= free`.

| game @ round | free | live | pairing | whole-line code (rank) | best fragment rank found | rank needed |
| --- | ---: | ---: | :---: | :---: | ---: | ---: |
| r021-witness @ 10 | 105 | 53 | no | **yes** (52) | 52 | <= 52 |
| r021-witness @ 9 | 107 | 57 | no | no (55) | 55 | <= 53 |
| r021-witness @ 8 | 109 | 61 | no | no (58) | 58 | <= 54 |
| r021-witness @ 7 | 111 | 65 | no | no (62) | 62 | <= 55 |
| r021-witness @ 6 | 113 | 69 | no | no (65) | 65 | <= 56 |
| r021-witness @ 5 | 115 | 73 | no | no (68) | 68 | <= 57 |
| r021-stronger @ 11 | 103 | 54 | no | **yes** (51) | 51 | <= 51 |
| r021-stronger @ 10 | 105 | 56 | no | no (53) | 53 | <= 52 |
| r021-stronger @ 9 | 107 | 59 | no | no (56) | 56 | <= 53 |
| r021-stronger @ 8 | 109 | 63 | no | no (59) | 59 | <= 54 |
| r021-stronger @ 7 | 111 | 66 | no | no (62) | 62 | <= 55 |
| r021-stronger @ 6 | 113 | 70 | no | no (65) | 65 | <= 56 |
| r021-stronger @ 5 | 115 | 74 | no | no (68) | 68 | <= 57 |
| r013-pairing @ 10 | 105 | 52 | **yes** | **yes** (51) | 51 | <= 52 |
| r013-pairing @ 9 | 107 | 57 | no | no (56) | 54 | <= 53 |
| r013-pairing @ 8 | 109 | 61 | no | no (59) | 58 | <= 54 |
| r013-pairing @ 7 | 111 | 66 | no | no (63) | 63 | <= 55 |
| r013-pairing @ 6 | 113 | 70 | no | no (66) | 66 | <= 56 |
| r013-pairing @ 5 | 115 | 81 | no | no (75) | 75 | <= 57 |

"Rank needed" is `floor(free / 2)`, the capacity bound. Reaching it is necessary
for a certificate but not sufficient.

**Finding.** Fragments gained 0 rounds over whole-line codes. In 17 of the 19
positions the search never got below the whole-line rank. The exceptions are
the r013 prefixes at rounds 9 and 8, where it got 2 and 1 below, still short of
the bound. The reason is structural. The rank drops only through *relations*,
meaning sets of fragments that cover every cell an even number of times.
Shrinking a fragment breaks the relations it belonged to and rarely creates new
ones. The shortfall grows by about 2–3 relations per round going backwards:
2, 4, 7, 9 and 11 along the witness game.

This is a heuristic search, not a proof that no fragment code exists at these
positions. These games are also favourable to Black: as Part B shows, White
does not defend in them. Fragment codes failing even here makes the negative
result stronger. It is strong enough evidence to stop. Fragment codes alone will not
lower the activation depth.

## Step 3: 4x4x4 as a falsification testbed (`cube4.py`, about 60 s)

4x4x4 Qubic is a first-player win (Patashnik 1980, Allis 1994). So no
second-player certificate can exist at the empty board or along White's best
play. The 4-cube cannot be a smaller copy of the 5x5x5 question. It *can* catch
bugs: every certified position is attacked with a White threat-space (VCF)
search.

The run used 10 games: a greedy Black against a greedy White that plays a random
move 35 % of the time. Each class was recorded at the first round it certified
Black.

| | pairing | whole-line code | fragment code |
| --- | ---: | ---: | ---: |
| games certified | 6 | 6 | 6 |
| mean first round | 18.7 | 18.7 | 18.7 |
| certified positions with a White VCF win | 0 | 0 | 0 |

Four games ended with a Black win and none with a White win. In all six certified
games the three classes switched on in the same round, between rounds 16 and 21
of 32. On the denser 4-cube (76 lines on 64 cells) every class waits until
nearly all lines are dead. There, all three are just pairing.

## What this means for the programme

The tensor/topology idea in its simplest linear form, fragment codes over GF(2),
does not move the frontier. Any idea from another field now needs to beat the
whole-line rank by about 2–3 relations *per round* of look-ahead, using
structure that local fragment choices cannot find. Candidates are:

- non-linear (e.g. GF(3), or mixed-field) codes;
- codes whose information sets change adaptively with White's moves;
- certificates that are not codes at all.

## Reproduce

```bash
python research-028/fragment_search.py smoke --trials 300
python research-028/fragment_search.py backward --seconds 6
python research-028/cube4.py --games 10 --seconds 0.4
```

The backward walk and `cube4.py` checkpoint after every position or game and
accept `--resume`. Results are written to `backward_results.json` and
`cube4_results.json`.
