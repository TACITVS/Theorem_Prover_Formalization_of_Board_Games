(** Untrusted strategy trees, checked against all White requests. A node
    chooses one Black reply per actual White move. A pairing leaf supplies
    its own verified complete endgame policy. No search program is trusted. *)
From Stdlib Require Import List Arith Bool Lia.
From QubicTrusted Require Import Rules Goal.
From QubicAgent Require Import Minimax RulesFacts SafePairing Stealing.

Inductive DefenseCertificate : Type :=
| PairingLeaf : list cell -> DefenseCertificate
| DefenseNode : (cell -> cell) -> (cell -> DefenseCertificate) -> DefenseCertificate.

Definition roundb (continuation : cell -> GameState -> bool)
    (replies : cell -> cell) (st : GameState) (request : cell) : bool :=
  let x := effective_move st request in
  branch prevents_white
    (fun _ after_white =>
      branch prevents_white (fun _ after_black => continuation x after_black)
        false after_white (replies x))
    true st request.

Fixpoint certificateb (certificate : DefenseCertificate) (st : GameState) : bool :=
  match certificate with
  | PairingLeaf table => pairing_leafb table st
  | DefenseNode replies children =>
      forallb (roundb (fun c after_black => certificateb (children c) after_black)
        replies st) requests
  end.

Lemma continuing_not_full : forall turn st,
  move_result turn st = None -> length (history st) <> 125.
Proof.
  intros turn st H. unfold move_result in H. destruct (has_win _); [discriminate|].
  destruct (length (history st) =? 125) eqn:Hfull; [discriminate|].
  apply Nat.eqb_neq. exact Hfull.
Qed.

Local Opaque solve.

Theorem checked_defense_tree_minimax : forall certificate st n,
  certificateb certificate st = true -> valid_state st ->
  n + length (history st) = 125 -> solve prevents_white false n true st = true.
Proof.
  fix IH 1. intros certificate st n Hcheck Hvalid Hlen.
  destruct certificate as [table|replies children].
  - apply checked_pairing_leaf_minimax with (table := table); assumption.
  - destruct n as [|n]; [rewrite pairing_solve_zero; reflexivity|].
    change (forallb
      (roundb (fun c after_black => certificateb (children c) after_black) replies st)
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

Theorem checked_tree_has_total_defense : forall certificate st n,
  certificateb certificate st = true -> valid_state st ->
  n + length (history st) = 125 ->
  exists b : BlackStrategy, forall w : WhiteStrategy,
    outcome (step_game n true st w b) <> WhiteWins.
Proof.
  intros certificate st n Hcheck Hvalid Hlen.
  exists (search_policy prevents_white false true). intros w.
  pose proof (checked_defense_tree_minimax certificate st n Hcheck Hvalid Hlen) as Hsolve.
  pose proof (solve_policy_sound prevents_white false true n true st w Hlen Hsolve) as Hsound.
  cbn [policies Bool.eqb] in Hsound.
  destruct (outcome (step_game n true st w (search_policy prevents_white false true)));
    cbn in Hsound; congruence.
Qed.

Theorem checked_empty_tree_proves_exact_draw : forall certificate,
  certificateb certificate initial_state = true -> Goal.ExactDraw.
Proof.
  intros certificate Hcheck. apply exact_draw_iff_black_nonloss.
  apply black_nonloss_value_true.
  apply (checked_defense_tree_minimax certificate initial_state 125 Hcheck
    initial_state_valid eq_refl).
Qed.

Print Assumptions checked_defense_tree_minimax.
Print Assumptions checked_tree_has_total_defense.
Print Assumptions checked_empty_tree_proves_exact_draw.
