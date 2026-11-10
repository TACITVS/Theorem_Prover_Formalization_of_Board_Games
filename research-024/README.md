# Research 024: Move-1 Master Reduction and Center Dominance

The full game value remains unresolved. This suite proves that the opening branching
factor at Move 1 collapses completely from 15,500 arbitrary opening pairs down to
strictly **10 canonical lines of play**, certified with 0 axioms and 0 admits in Rocq 9.1.

## Summary of Proved Results

1. **Non-Center Openings ($W \in \{0, 1, 2, 7, 12\}$):**
   - Black playing $B = 62$ (the Center cell) is strictly legal and unoccupied (`non_center_reply_is_legal`).
   - Cell 62 is the uniquely maximal degree cell on the board (degree 13, whereas all other 124 cells have degree $\le 7$).
   - Playing 62 instantly neutralizes 13 winning lines in a single move.
   - For openings 0 (Corner), 2 (Edge-Center), and 12 (Face-Center), playing 62 directly blocks White's initial winning line.
   - Black playing 62 is unconditionally sound: whenever the state after replying with 62 is non-losing, the opening is non-losing (`non_center_opening_center_reply_sound`).

2. **Center Opening ($W = 62$):**
   - When White occupies the center, cell 62 is fixed under all 48 symmetries in $O_h$ and the layer permutation $\pi = [1,0,2,4,3]$.
   - Black non-loss is provably equivalent to finding *at least one* valid reply among the 5 non-center canonical classes: `[0; 1; 2; 7; 12]` (`center_opening_iff_five_replies`).

3. **Master Move-1 Reduction Theorem (`master_move_one_reduction`):**
   ```coq
   Theorem master_move_one_reduction :
     (exists c, In c center_replies /\ center_reply_value c = true) ->
     (forall w, In w non_center_openings -> non_center_reply_value w = true) ->
     Goal.ExactDraw.
   ```
   This formally links the grand goal `Goal.ExactDraw` to precisely **10 opening pairs**:
   - 1 successful reply among 5 non-centers against White's Center opening.
   - Deterministic reply 62 against the 5 non-center openings.

## Assumption Audit

All 4 audited theorems in `ZCenterDominance.v` evaluate to `Closed under the global context`
with 0 axioms, 0 admits, and pass recursive `rocq check`.

## Reproduce

```powershell
python research-024/verify.py --rocq "C:\Rocq-Platform~9.1~2026.01\bin\rocq.exe"
```
