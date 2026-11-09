# QUBIC-AUDIT-014/015 — Independent referee findings

**Repository:** TACITVS/Theorem_Prover_Formalization_of_Board_Games  
**Branch:** `qubic-5x5x5`  
**Reviewed commit:** `033f6b53cf3a5925e799ae288f795d1d555ad26b` (2026-11-09 18:40:58 UTC)

## Mathematical status

The new `QubicAlgebraic.v` confirms numerical arithmetic, a finite 10-round pairing certificate, and conditional line blocking. **There is no theorem asserting a Black nonlosing strategy from the empty board against every legal White strategy.** The README's exact-draw claim is unsupported by those statements. The monograph explicitly calls adversarial reachability a remaining open frontier.

## High-severity logical gaps

1. `minimal_horizon_lower_bound_k7/k8/k9` prove only fixed numerical inequalities involving `B_max_*`; they do **not** prove that those values are upper bounds on the number of lines blocked by arbitrary sets of 7/8/9 Black cells.
2. `move1_center_strict_contraction` proves `37-38<0`, and `move1_noncenter_strict_contraction` proves a generic implication `dW<=31 && dB>=37 -> dW-dB<=-6`; neither statement quantifies over the game's board cells, legal replies, or a potential function evaluated on actual positions. The claimed global potential contraction is not a theorem of these files.
3. The capacity condition `2*(109-B)<=125-2*k` is necessary, not sufficient, for a complete disjoint pairing. See independently checked 10-round counterexample below.
4. `QubicAlgebraic.safe10_blocks_all_109_lines` assumes `safe10_defense_active b`; no theorem proves that this predicate, or a complete defensive pairing, can be *forced* from the empty board. The concrete 10-round certificate is valid but existential.
5. `research-013/QUBIC-RESEARCH-013_safe10.v` imports `QubicGame`, which is absent from the repository tree, and is omitted from `build.ps1`; the standalone Rocq safe-leaf proof cannot be built as checked in.

## Counterexample 014: capacity satisfied, pairing impossible

Under `QubicBoard.v` cell convention `cell=x+5*y+25*z`:

- Black: `[0,29,31,43,62,81,95,100,108,124]`
- White: `[5,25,30,50,51,52,53,55,75,80]`
- Exactly 57 lines blocked and 52 surviving; 105 free cells; `2*52=104<=105`.
- Surviving line `[50,51,52,53,54]` has four White cells `[50,51,52,53]`, only free cell `54`, and no Black stone. It cannot have two free endpoints.
- Both players have ten distinct, disjoint cells and neither has won. Any alternating ordering of these final stones is a legal, nonterminal ten-round history because victories are monotone.

See `QUBIC-AUDIT-014_capacity_not_sufficient.py`; it prints `VERIFIED` with pure standard-library independent line enumeration.

## Counterexample 015: defects in VCF solver

`solver/search_vcf.c`:

- `canonical_openings` lists nine cells, but just seven distinct symmetry classes; the missing 10-orbit representatives are `(0,0,1)`, `(0,1,1)`, `(1,1,2)` as sorted coordinate distances from cube center.
- The rule `num_threats >= 2 -> forced win` is incorrect when different winning lines have the same missing cell. With White's cells `[12,37,52,57,67,72,87,112]` and Black empty, two different four-in-row threats both require the same Black response `62`, which blocks both.
- `get_four_threats` computes `__builtin_ctzll((uint64_t)empty_mask)` before testing the high 64-bit half. The call is undefined for a missing cell with index 64-124.
- Search checks only threat-producing White moves and depth<=8; its negative result is not exhaustive minimax evidence. The `opp_threats>1` early return may also omit a White immediate winning move.

See `QUBIC-AUDIT-015_vcf_regressions.py` for the first two exact counterexamples.

## Build/validation problems

- `build.ps1` prints `OK` after each native compiler invocation without checking `$LASTEXITCODE`. `$ErrorActionPreference = "Stop"` does not universally turn nonzero native exit codes into terminating errors.
- The README and monograph claim EXACT DRAW while the monograph elsewhere acknowledges that the alternating adversarial reachability proof is missing.
- `solver/stress_test_beck.c` counts a pairing-safe **early leaf** as `Hopcroft-Karp Draw` and breaks out; these are certified conditional non-loss terminals for that simulation, not actual complete games played to board draw.
- At reviewed commit, GitHub's API showed **zero check runs**, so local compilation claims were not independently confirmed by CI. Rocq and Lean compilers were unavailable in the audit environment.

## Required acceptance criterion

Prove (or refute) a full legal-game minimax statement on the full 109-line board, with both players' immediate wins and terminal rules, such as

`exists BlackStrategy, forall WhiteStrategy, WhiteNeverWins (play WhiteStrategy BlackStrategy)`.

A verified conditional pairing theorem or a single 10-round safe leaf does not discharge this quantified objective. A White winning strategy also settles the game if the draw conjecture is false.
