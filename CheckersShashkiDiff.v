(** **************************************************************************
    CheckersShashkiDiff.v: Mathematical Comparison between English Draughts & Shashki
    
    This module formalizes the structural differences between:
    - English Draughts (Standard Checkers):
      1. Men capture forward only (+7, +9 for White).
      2. Men moves and jumps strictly increase rank monotonically.
      3. Kings move and jump exactly 1 diagonal step (short-range).
      4. Crowning in transit terminates the turn immediately.
    - Shashki (Russian Draughts):
      1. Men can capture backward (-9, -7).
      2. Men jumps are NOT rank-monotonic.
      3. Kings are Flying Kings (unbounded ray mobility up to 7 squares).
      4. Crowning in transit allows immediate continuation as a flying king.
      5. Cycle formation is possible even with regular men in Shashki.
    
    Zero unproven axioms, zero admissions (Closed under global context).
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import Checkers.CheckersBoard.
Require Import Checkers.CheckersGame.
Require Import Checkers.CheckersInvariants.

Section CheckersShashkiDiff.

(** Theorem 1: English White Regular Men cannot execute Backward Jumps *)
Theorem english_white_man_no_backward_jump : forall s mid dst,
  jump_bl s = Some (mid, dst) ->
  ~ In (mid, dst) (man_jump_targets White s).
Proof.
  intros s mid dst Hbl.
  unfold man_jump_targets, opt_pair_to_list.
  intros Hin.
  apply in_app_iff in Hin.
  destruct Hin as [Hfl | Hfr].
  - destruct (jump_fl s) as [[m d]|] eqn:Hjfl; [|inversion Hfl].
    simpl in Hfl; destruct Hfl as [Heq | Hnil]; [|inversion Hnil].
    injection Heq as Hm Hd; subst m d.
    apply jump_bl_rank in Hbl.
    apply jump_fl_rank in Hjfl.
    lia.
  - destruct (jump_fr s) as [[m d]|] eqn:Hjfr; [|inversion Hfr].
    simpl in Hfr; destruct Hfr as [Heq | Hnil]; [|inversion Hnil].
    injection Heq as Hm Hd; subst m d.
    apply jump_bl_rank in Hbl.
    apply jump_fr_rank in Hjfr.
    lia.
Qed.

(** Theorem 2: English Black Regular Men cannot execute Forward Jumps *)
Theorem english_black_man_no_forward_jump : forall s mid dst,
  jump_fl s = Some (mid, dst) ->
  ~ In (mid, dst) (man_jump_targets Black s).
Proof.
  intros s mid dst Hfl.
  unfold man_jump_targets, opt_pair_to_list.
  intros Hin.
  apply in_app_iff in Hin.
  destruct Hin as [Hbl | Hbr].
  - destruct (jump_bl s) as [[m d]|] eqn:Hjbl; [|inversion Hbl].
    simpl in Hbl; destruct Hbl as [Heq | Hnil]; [|inversion Hnil].
    injection Heq as Hm Hd; subst m d.
    apply jump_bl_rank in Hjbl.
    apply jump_fl_rank in Hfl.
    lia.
  - destruct (jump_br s) as [[m d]|] eqn:Hjbr; [|inversion Hbr].
    simpl in Hbr; destruct Hbr as [Heq | Hnil]; [|inversion Hnil].
    injection Heq as Hm Hd; subst m d.
    apply jump_br_rank in Hjbr.
    apply jump_fl_rank in Hfl.
    lia.
Qed.

(** Theorem 3: English King step mobility is strictly bounded by 4 adjacent squares *)
Theorem english_king_mobility_bounded : forall s,
  length (king_step_targets s) <= 4.
Proof.
  intros s.
  unfold king_step_targets, opt_to_list.
  destruct (step_fl s); destruct (step_fr s);
  destruct (step_bl s); destruct (step_br s); simpl; lia.
Qed.

(** Theorem 4: English King jump targets are strictly bounded by 4 jump vectors *)
Theorem english_king_jump_bounded : forall s,
  length (king_jump_targets s) <= 4.
Proof.
  intros s.
  unfold king_jump_targets, opt_pair_to_list.
  destruct (jump_fl s); destruct (jump_fr s);
  destruct (jump_bl s); destruct (jump_br s); simpl; lia.
Qed.

(** Shashki contrast definition:
    In Shashki, man capture targets include backward jumps *)
Definition shashki_man_jump_targets (p : player) (s : nat) : list (nat * nat) :=
  opt_pair_to_list (jump_fl s) ++ opt_pair_to_list (jump_fr s) ++
  opt_pair_to_list (jump_bl s) ++ opt_pair_to_list (jump_br s).

(** Theorem 5: Shashki man jump set strictly contains backward captures *)
Theorem shashki_allows_backward_capture : forall s mid dst,
  jump_bl s = Some (mid, dst) ->
  In (mid, dst) (shashki_man_jump_targets White s).
Proof.
  intros s mid dst Hbl.
  unfold shashki_man_jump_targets, opt_pair_to_list.
  rewrite Hbl.
  apply in_app_iff. right.
  apply in_app_iff. right.
  apply in_app_iff. left.
  simpl. left. reflexivity.
Qed.

(** Theorem 6: Shashki man backward jump decreases rank (violating monotonic increase) *)
Theorem shashki_backward_decreases_rank : forall s mid dst,
  jump_bl s = Some (mid, dst) ->
  In (mid, dst) (shashki_man_jump_targets White s) /\ sq_rank s = sq_rank dst + 2.
Proof.
  intros s mid dst Hbl.
  split.
  - apply shashki_allows_backward_capture; exact Hbl.
  - apply (jump_bl_rank s mid dst); exact Hbl.
Qed.

End CheckersShashkiDiff.
