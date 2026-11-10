(** Strategy certificates with both existing trees and linear-code leaves.
    An accepted empty-board certificate would prove the unchanged draw goal.
    No empty-board certificate is asserted here. *)
From Stdlib Require Import List Arith Bool Lia.
From QubicTrusted Require Import Rules Goal.
From QubicAgent Require Import Minimax RulesFacts SafePairing Stealing
  TreeCertificates ZLinearAlgebra ZLinearDefense.

Inductive LinearDefenseCertificate : Type :=
| ExistingTree : DefenseCertificate -> LinearDefenseCertificate
| LinearLeaf : Decoder -> Decoder -> LinearDefenseCertificate
| LinearDefenseNode : (cell -> cell) -> (cell -> LinearDefenseCertificate) -> LinearDefenseCertificate.

Fixpoint linear_treeb (certificate : LinearDefenseCertificate) (st : GameState) : bool :=
  match certificate with
  | ExistingTree tree => certificateb tree st
  | LinearLeaf decoder0 decoder1 => linear_leafb decoder0 decoder1 st
  | LinearDefenseNode replies children =>
      forallb (roundb (fun c after_black => linear_treeb (children c) after_black)
        replies st) requests
  end.

Theorem every_existing_tree_embeds : forall certificate st,
  linear_treeb (ExistingTree certificate) st = certificateb certificate st.
Proof. reflexivity. Qed.

Local Opaque solve.

Theorem checked_linear_tree_minimax : forall certificate st n,
  linear_treeb certificate st = true -> valid_state st ->
  n + length (history st) = 125 -> solve prevents_white false n true st = true.
Proof.
  fix IH 1. intros certificate st n Hcheck Hvalid Hlen.
  destruct certificate as [old|decoder0 decoder1|replies children].
  - apply checked_defense_tree_minimax with (certificate := old); assumption.
  - apply checked_linear_leaf_minimax with (decoder0 := decoder0) (decoder1 := decoder1); assumption.
  - destruct n as [|n]; [rewrite pairing_solve_zero; reflexivity|].
    change (forallb
      (roundb (fun c after_black => linear_treeb (children c) after_black) replies st)
      requests = true) in Hcheck.
    rewrite pairing_solve_successor. cbn [Bool.eqb].
    apply forallb_forall. intros request Hin.
    apply forallb_forall with (x := request) in Hcheck; [|exact Hin].
    unfold roundb, branch in Hcheck. unfold branch.
    set (after_white := move_state true st request) in *.
    assert (Hwhite_len : length (history after_white) = S (length (history st)))
      by (apply move_state_history).
    assert (Hwhite_valid : valid_state after_white) by
      (apply move_preserves_validity; [exact Hvalid|lia]).
    destruct (move_result true after_white) as [r|] eqn:Hwhite_result;
      [exact Hcheck|].
    destruct n as [|n].
    { exfalso. apply (continuing_not_full true after_white Hwhite_result). lia. }
    change (solve prevents_white false (S n) false after_white = true).
    rewrite pairing_solve_successor. cbn [Bool.eqb].
    apply existsb_exists. exists (canonical_request (replies (effective_move st request))).
    split; [apply canonical_request_in|]. rewrite branch_canonical. unfold branch.
    set (after_black := move_state false after_white (replies (effective_move st request))) in *.
    assert (Hwhite_notfull := continuing_not_full true after_white Hwhite_result).
    assert (Hblack_valid : valid_state after_black) by
      (apply move_preserves_validity; [exact Hwhite_valid|lia]).
    assert (Hblack_len : length (history after_black) = S (length (history after_white)))
      by (apply move_state_history).
    destruct (move_result false after_black) as [r|] eqn:Hblack_result;
      [exact Hcheck|].
    apply (IH (children (effective_move st request)) after_black n);
      try assumption. lia.
Qed.

Theorem checked_linear_tree_total_defense : forall certificate st n,
  linear_treeb certificate st = true -> valid_state st ->
  n + length (history st) = 125 ->
  exists b : BlackStrategy, forall w : WhiteStrategy,
    outcome (step_game n true st w b) <> WhiteWins.
Proof.
  intros certificate st n Hcheck Hvalid Hlen.
  exists (search_policy prevents_white false true). intros w.
  pose proof (checked_linear_tree_minimax certificate st n Hcheck Hvalid Hlen) as Hsolve.
  pose proof (solve_policy_sound prevents_white false true n true st w Hlen Hsolve) as Hsound.
  cbn [policies Bool.eqb] in Hsound.
  destruct (outcome (step_game n true st w (search_policy prevents_white false true)));
    cbn in Hsound; congruence.
Qed.

Theorem checked_empty_linear_tree_proves_exact_draw : forall certificate,
  linear_treeb certificate initial_state = true -> Goal.ExactDraw.
Proof.
  intros certificate Hcheck. apply exact_draw_iff_black_nonloss.
  apply black_nonloss_value_true.
  apply (checked_linear_tree_minimax certificate initial_state 125 Hcheck
    initial_state_valid eq_refl).
Qed.

Print Assumptions every_existing_tree_embeds.
Print Assumptions checked_linear_tree_minimax.
Print Assumptions checked_linear_tree_total_defense.
Print Assumptions checked_empty_linear_tree_proves_exact_draw.
