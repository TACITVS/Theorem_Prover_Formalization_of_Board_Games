(** Legality and terminal correctness of the unchanged, hash-pinned Rules.
    These facts apply to every pair of total policies, including policies
    requesting occupied or out-of-range cells. *)
From Stdlib Require Import List Arith Bool Lia Permutation.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Minimax.
Import ListNotations.

Lemma member_spec : forall c stones,
  existsb (Nat.eqb c) stones = true <-> In c stones.
Proof.
  intros c stones. rewrite existsb_exists. split.
  - intros [d [Hd Heq]]. apply Nat.eqb_eq in Heq. subst. exact Hd.
  - intros H. exists c. split; [exact H|apply Nat.eqb_refl].
Qed.

Lemma occupied_spec : forall st c,
  occupied st c = true <-> In c (white_stones st ++ black_stones st).
Proof.
  intros st c. unfold occupied. rewrite orb_true_iff, !member_spec, in_app_iff.
  reflexivity.
Qed.

Record valid_state (st : GameState) : Prop := {
  history_valid : Forall (fun c => c < 125) (history st);
  history_nodup : NoDup (history st);
  history_partition : Permutation (history st) (white_stones st ++ black_stones st)
}.

Lemma initial_state_valid : valid_state initial_state.
Proof. constructor; constructor. Qed.

Lemma valid_history_occupied : forall st c,
  valid_state st -> (In c (history st) <-> occupied st c = true).
Proof.
  intros st c Hvalid. rewrite occupied_spec.
  split; intro H.
  - eapply Permutation_in; [exact (history_partition st Hvalid)|exact H].
  - eapply Permutation_in; [apply Permutation_sym; exact (history_partition st Hvalid)|exact H].
Qed.

Lemma free_cell_exists : forall st,
  valid_state st -> length (history st) < 125 ->
  exists c, c < 125 /\ occupied st c = false.
Proof.
  intros st Hvalid Hlen.
  destruct (find (fun c => negb (occupied st c)) all_cells) eqn:Hfind.
  - apply find_some in Hfind as [Hin Hfree].
    apply in_seq in Hin. exists c. apply negb_true_iff in Hfree.
    split; [lia|exact Hfree].
  - assert (Hincl : incl all_cells (history st)).
    { intros c Hc. apply (valid_history_occupied st c Hvalid).
      pose proof (@find_none cell _ _ Hfind c Hc) as Hnone.
      cbn beta in Hnone. apply negb_false_iff in Hnone. exact Hnone. }
    pose proof (NoDup_incl_length (seq_NoDup 125 0) Hincl) as Hbound.
    cbn in Hbound. exfalso.
    exact (Nat.lt_irrefl 125 (Nat.le_lt_trans _ _ _ Hbound Hlen)).
Qed.

(** The local recursive scanner in Rules is definitionally this function. *)
Fixpoint scan_free (st : GameState) (n : nat) : cell :=
  match n with
  | 0 => 0
  | S rem => if negb (occupied st (125 - n)) then 125 - n else scan_free st rem
  end.

Lemma scan_free_sound : forall n st,
  n <= 125 ->
  (exists c, 125 - n <= c /\ c < 125 /\ occupied st c = false) ->
  is_legal_move st (scan_free st n) = true.
Proof.
  induction n as [|n IH]; intros st Hn [c [Hlo [Hhi Hfree]]].
  - cbn in Hlo. lia.
  - cbn [scan_free]. destruct (negb (occupied st (125 - S n))) eqn:Hfirst.
    + unfold is_legal_move. rewrite Hfirst, andb_true_r.
      apply Nat.ltb_lt. lia.
    + apply IH; [lia|]. exists c. repeat split; try assumption.
      apply negb_false_iff in Hfirst.
      assert (Hneq : c <> 125 - S n) by (intro H; subst; congruence).
      lia.
Qed.

Theorem fallback_is_legal : forall st,
  valid_state st -> length (history st) < 125 ->
  is_legal_move st (next_available_cell st) = true.
Proof.
  intros st Hvalid Hlen. change (is_legal_move st (scan_free st 125) = true).
  apply scan_free_sound; [lia|].
  destruct (free_cell_exists st Hvalid Hlen) as [c [Hc Hfree]].
  exists c. repeat split; auto with arith.
Qed.

Theorem effective_move_is_legal : forall st c,
  valid_state st -> length (history st) < 125 ->
  is_legal_move st (effective_move st c) = true.
Proof.
  intros st c Hvalid Hlen. unfold effective_move.
  destruct (is_legal_move st c) eqn:Hlegal; [exact Hlegal|].
  apply fallback_is_legal; assumption.
Qed.

Theorem move_preserves_validity : forall turn st c,
  valid_state st -> length (history st) < 125 ->
  valid_state (move_state turn st c).
Proof.
  intros turn st c Hvalid Hlen.
  pose proof (effective_move_is_legal st c Hvalid Hlen) as Hlegal.
  unfold is_legal_move in Hlegal.
  apply andb_true_iff in Hlegal as [Hbound Hfree].
  apply Nat.ltb_lt in Hbound. apply negb_true_iff in Hfree.
  assert (Hfresh : ~ In (effective_move st c) (history st)).
  { intro Hin. apply (valid_history_occupied st _ Hvalid) in Hin. congruence. }
  destruct Hvalid as [Hrange Hnd Hpartition].
  destruct turn; constructor; cbn [move_state history white_stones black_stones].
  - constructor; assumption.
  - constructor; assumption.
  - apply perm_skip. exact Hpartition.
  - constructor; assumption.
  - constructor; assumption.
  - eapply Permutation_trans; [apply perm_skip; exact Hpartition|].
    apply Permutation_middle.
Qed.

Definition quiet (st : GameState) : Prop :=
  has_win (white_stones st) = false /\ has_win (black_stones st) = false.

Definition result_correct (st : GameState) (r : Result) : Prop :=
  valid_state st /\
  match r with
  | WhiteWins => has_win (white_stones st) = true /\ has_win (black_stones st) = false
  | BlackWins => has_win (black_stones st) = true /\ has_win (white_stones st) = false
  | Draw => length (history st) = 125 /\ quiet st
  end.

Lemma continuing_move_quiet : forall turn st c,
  quiet st -> move_result turn (move_state turn st c) = None ->
  quiet (move_state turn st c).
Proof.
  intros turn st c [Hw Hb] Hresult.
  unfold move_result, move_state in *. destruct turn;
    cbn [white_stones black_stones history List.length] in *.
  - destruct (has_win (effective_move st c :: white_stones st)) eqn:Hnew;
      [discriminate|]. split; assumption.
  - destruct (has_win (effective_move st c :: black_stones st)) eqn:Hnew;
      [discriminate|]. split; assumption.
Qed.

Lemma terminating_move_correct : forall turn st c r,
  valid_state st -> length (history st) < 125 -> quiet st ->
  move_result turn (move_state turn st c) = Some r ->
  result_correct (move_state turn st c) r.
Proof.
  intros turn st c r Hvalid Hlen [Hw Hb] Hresult.
  split; [apply move_preserves_validity; assumption|].
  unfold move_result, move_state in *. destruct turn;
    cbn [white_stones black_stones history List.length] in *.
  - destruct (has_win (effective_move st c :: white_stones st)) eqn:Hnew.
    + inversion Hresult; subst. split; [reflexivity|assumption].
    + destruct (S (length (history st)) =? 125) eqn:Hfull; [|discriminate].
      inversion Hresult; subst. apply Nat.eqb_eq in Hfull. repeat split; assumption.
  - destruct (has_win (effective_move st c :: black_stones st)) eqn:Hnew.
    + inversion Hresult; subst. split; [reflexivity|assumption].
    + destruct (S (length (history st)) =? 125) eqn:Hfull; [|discriminate].
      inversion Hresult; subst. apply Nat.eqb_eq in Hfull. repeat split; assumption.
Qed.

Theorem step_game_correct : forall n turn st w b,
  n + length (history st) = 125 -> valid_state st -> quiet st ->
  let tr := step_game n turn st w b in
  result_correct (final_state tr) (outcome tr).
Proof.
  induction n as [|n IH]; intros turn st w b Hlen Hvalid Hquiet.
  - split; [exact Hvalid|]. split; [cbn in Hlen; exact Hlen|exact Hquiet].
  - rewrite step_game_equation. cbn zeta.
    destruct (move_result turn (move_state turn st (if turn then w st else b st)))
      as [r|] eqn:Hresult.
    + apply terminating_move_correct; try assumption; lia.
    + apply IH.
      * rewrite move_state_history. lia.
      * apply move_preserves_validity; [assumption|lia].
      * apply continuing_move_quiet; assumption.
Qed.

Theorem every_play_is_legal_and_terminal : forall w b,
  result_correct (final_state (play w b)) (outcome (play w b)).
Proof.
  intros w b. apply step_game_correct; [reflexivity|apply initial_state_valid|].
  split; reflexivity.
Qed.

Print Assumptions fallback_is_legal.
Print Assumptions move_preserves_validity.
Print Assumptions every_play_is_legal_and_terminal.
