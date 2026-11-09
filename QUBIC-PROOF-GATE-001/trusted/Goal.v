(* QUBIC-PROOF-GATE-001 — REVIEW AND FREEZE BEFORE USE.
   The independent Rules module MUST be reviewed and immutable.
   This module is not a proof and cannot compile until Rules.v exists. *)
From QubicTrusted Require Import Rules.

(* Black is the SECOND player; strategies must be legal, total policies on all
   reachable positions, and play must stop immediately when either player wins.
   Rules.play must be a terminating, deterministic evaluation of full games. *)
Definition BlackNonLossFromEmpty : Prop :=
  exists black : Rules.BlackStrategy,
    forall white : Rules.WhiteStrategy,
      Rules.outcome (Rules.play white black) <> Rules.WhiteWins.

Definition WhiteNonLossFromEmpty : Prop :=
  exists white : Rules.WhiteStrategy,
    forall black : Rules.BlackStrategy,
      Rules.outcome (Rules.play white black) <> Rules.BlackWins.

(* Do NOT label a proof of only the first conjunct an "exact draw". *)
Definition ExactDraw : Prop :=
  BlackNonLossFromEmpty /\ WhiteNonLossFromEmpty.
