(* HUMAN-OWNED AND HASH-PINNED. Never permit agent edits to this file. *)
From QubicTrusted Require Import Goal.
From QubicAgent Require Import Solution.

Theorem accepted_black_nonloss : QubicTrusted.Goal.BlackNonLossFromEmpty.
Proof.
  exact QubicAgent.Solution.black_nonloss.
Qed.

Theorem accepted_exact_draw : QubicTrusted.Goal.ExactDraw.
Proof.
  exact QubicAgent.Solution.exact_draw.
Qed.

Print Assumptions accepted_black_nonloss.
Print Assumptions accepted_exact_draw.
