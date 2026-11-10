(** trusted/agent/ZCenterDominance.v: Move-1 Master Reduction and Center Dominance
    for 5x5x5 Qubic.
    Branch: agent-qubic-5x5x5 *)

From Stdlib Require Import List Arith Bool Lia.
From QubicTrusted Require Import Rules Goal.
From QubicAgent Require Import Geometry Minimax Stealing RulesFacts SymmetryGame ZLayerSymmetry ZCenterStar.
Import ListNotations.

Local Opaque solve.

Definition non_center_openings : list cell := [0; 1; 2; 7; 12].

Definition non_center_reply_value (w : cell) : bool :=
  branch prevents_white (solve prevents_white false 123) false (opening_state w) 62.

Lemma non_center_openings_fresh : forall w,
  In w non_center_openings -> w <> 62.
Proof.
  intros w Hw.
  unfold non_center_openings in Hw.
  destruct Hw as [H|[H|[H|[H|[H|H]]]]]; try (subst w; lia); destruct H.
Qed.

Lemma non_center_reply_is_legal : forall w,
  In w non_center_openings ->
  is_legal_move (opening_state w) 62 = true.
Proof.
  intros w Hw.
  unfold non_center_openings in Hw.
  destruct Hw as [H|[H|[H|[H|[H|H]]]]]; subst; try reflexivity; destruct H.
Qed.

Lemma non_center_opening_center_reply_sound : forall w,
  In w non_center_openings ->
  non_center_reply_value w = true ->
  opening_nonloss w.
Proof.
  intros w Hw Hreply.
  unfold opening_nonloss.
  rewrite Stealing.solve_successor.
  change (existsb (branch prevents_white (solve prevents_white false 123) false (opening_state w)) requests = true).
  apply existsb_exists.
  exists 62. split.
  - apply in_seq. lia.
  - exact Hreply.
Qed.

Theorem master_move_one_reduction :
  (exists c, In c center_replies /\ center_reply_value c = true) ->
  (forall w, In w non_center_openings -> non_center_reply_value w = true) ->
  Goal.ExactDraw.
Proof.
  intros Hcenter Hnon_center.
  rewrite exact_draw_iff_six_openings.
  intros c Hc.
  unfold six in Hc.
  destruct Hc as [H0 | [H1 | [H2 | [H7 | [H12 | [H62 | Hnil]]]]]].
  - subst c. apply non_center_opening_center_reply_sound; [simpl; tauto|apply Hnon_center; simpl; tauto].
  - subst c. apply non_center_opening_center_reply_sound; [simpl; tauto|apply Hnon_center; simpl; tauto].
  - subst c. apply non_center_opening_center_reply_sound; [simpl; tauto|apply Hnon_center; simpl; tauto].
  - subst c. apply non_center_opening_center_reply_sound; [simpl; tauto|apply Hnon_center; simpl; tauto].
  - subst c. apply non_center_opening_center_reply_sound; [simpl; tauto|apply Hnon_center; simpl; tauto].
  - subst c. rewrite center_opening_iff_five_replies. exact Hcenter.
  - contradiction.
Qed.

Print Assumptions non_center_openings_fresh.
Print Assumptions non_center_reply_is_legal.
Print Assumptions non_center_opening_center_reply_sound.
Print Assumptions master_move_one_reduction.
