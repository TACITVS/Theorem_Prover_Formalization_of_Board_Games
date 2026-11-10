(** Strategy stealing for the locked, finite, symmetric placement game.
    Owning extra cells cannot harm White's ability to avoid losing. *)
From Stdlib Require Import List Arith Bool Lia Permutation.
From QubicTrusted Require Import Rules Goal.
From QubicAgent Require Import Minimax RulesFacts.
Import ListNotations.

Lemma has_win_monotone : forall small large,
  incl small large -> has_win small = true -> has_win large = true.
Proof.
  intros small large Hincl Hwin. unfold has_win in *.
  apply existsb_exists in Hwin as [l [Hl Hline]].
  apply existsb_exists. exists l. split; [exact Hl|].
  unfold has_line in *. apply forallb_forall. intros c Hc.
  apply member_spec, Hincl, member_spec.
  apply forallb_forall with (x := c) in Hline; assumption.
Qed.

Definition dominates (small large : GameState) : Prop :=
  incl (white_stones small) (white_stones large) /\
  black_stones small = black_stones large.

Lemma valid_white_nodup : forall st, valid_state st -> NoDup (white_stones st).
Proof.
  intros st Hvalid.
  pose proof (Permutation_NoDup (history_partition st Hvalid)
    (history_nodup st Hvalid)) as Hnd.
  apply NoDup_app_remove_r in Hnd. exact Hnd.
Qed.

Lemma dominance_history_length : forall small large,
  valid_state small -> valid_state large -> dominates small large ->
  length (history small) <= length (history large).
Proof.
  intros small large Hs Hl [Hw Hb].
  pose proof (NoDup_incl_length (valid_white_nodup small Hs) Hw) as Hle.
  pose proof (Permutation_length (history_partition small Hs)) as Hsl.
  pose proof (Permutation_length (history_partition large Hl)) as Hll.
  rewrite !length_app in Hsl, Hll. rewrite Hb in Hsl. lia.
Qed.

Lemma dominance_quiet : forall small large,
  dominates small large -> quiet large -> quiet small.
Proof.
  intros small large [Hw Hb] [HlargeW HlargeB]. split.
  - destruct (has_win (white_stones small)) eqn:Hsmall; [|reflexivity].
    pose proof (has_win_monotone _ _ Hw Hsmall). congruence.
  - rewrite Hb. exact HlargeB.
Qed.

Lemma solve_successor : forall accept owner n turn st,
  solve accept owner (S n) turn st =
  if Bool.eqb turn owner
  then existsb (branch accept (solve accept owner n) turn st) requests
  else forallb (branch accept (solve accept owner n) turn st) requests.
Proof. reflexivity. Qed.

Lemma solve_empty_horizon : forall accept owner turn st,
  solve accept owner 0 turn st = accept Draw.
Proof. reflexivity. Qed.

Local Opaque solve.

Lemma white_move_simulation : forall small large v,
  valid_state small -> valid_state large ->
  length (history small) < 125 -> length (history large) < 125 ->
  dominates small large ->
  exists a, dominates (move_state true small v) (move_state true large a).
Proof.
  intros small large v Hs Hl Hslen Hllen [Hw Hb].
  set (d := effective_move small v).
  pose proof (effective_move_is_legal small v Hs Hslen) as Hd.
  change (is_legal_move small d = true) in Hd.
  destruct (is_legal_move large d) eqn:Hlarge.
  - exists d. unfold dominates, move_state. cbn zeta.
    assert (Heff : effective_move large d = d).
    { unfold effective_move. rewrite Hlarge. reflexivity. }
    rewrite Heff. cbn [white_stones black_stones]. split; [|exact Hb].
    intros c [Hc|Hc]; [left; exact Hc|right; apply Hw; exact Hc].
  - assert (Hown : In d (white_stones large)).
    { unfold is_legal_move in Hd, Hlarge.
      apply andb_true_iff in Hd as [Hrange Hfree]. rewrite Hrange in Hlarge.
      cbn in Hlarge. apply negb_false_iff in Hlarge.
      apply occupied_spec in Hlarge. apply in_app_iff in Hlarge as [H|H]; [exact H|].
      apply negb_true_iff in Hfree.
      assert (Hocc : occupied small d = true).
      { apply occupied_spec, in_app_iff. right. rewrite Hb. exact H. }
      congruence. }
    exists 0. unfold dominates, move_state. cbn [white_stones black_stones].
    split; [|exact Hb]. intros c [Hc|Hc]; right.
    + subst c. exact Hown.
    + apply Hw. exact Hc.
Qed.

Lemma black_move_simulation : forall small large a,
  valid_state small -> valid_state large ->
  length (history small) < 125 -> length (history large) < 125 ->
  dominates small large ->
  exists v, dominates (move_state false small v) (move_state false large a).
Proof.
  intros small large a Hs Hl Hslen Hllen [Hw Hb].
  set (d := effective_move large a).
  pose proof (effective_move_is_legal large a Hl Hllen) as Hd.
  change (is_legal_move large d = true) in Hd.
  assert (Hsmall : is_legal_move small d = true).
  { unfold is_legal_move in *. apply andb_true_iff in Hd as [Hrange Hfree].
    rewrite Hrange. cbn. apply negb_true_iff in Hfree.
    apply negb_true_iff. destruct (occupied small d) eqn:Hocc; [|reflexivity].
    apply occupied_spec in Hocc. apply in_app_iff in Hocc as [H|H].
    - assert (Hbad : occupied large d = true).
      { apply occupied_spec, in_app_iff. left. apply Hw. exact H. } congruence.
    - assert (Hbad : occupied large d = true).
      { apply occupied_spec, in_app_iff. right. rewrite <- Hb. exact H. } congruence. }
  exists d. unfold dominates, move_state. cbn zeta.
  assert (Heff : effective_move small d = d).
  { unfold effective_move. rewrite Hsmall. reflexivity. }
  rewrite Heff. cbn [white_stones black_stones]. split; [exact Hw|].
  unfold d. rewrite Hb. reflexivity.
Qed.

(** Move simulation transfers a true virtual branch to the real board.
    Actual early victories and board exhaustion are handled before recursion. *)
Lemma branch_dominance : forall n m turn small large v a,
  (forall m small large,
    m + length (history small) = 125 ->
    n + length (history large) = 125 ->
    valid_state small -> valid_state large ->
    quiet small -> quiet large -> dominates small large ->
    solve prevents_black true m turn small = true ->
    solve prevents_black true n turn large = true) ->
  S m + length (history small) = 125 ->
  S n + length (history large) = 125 ->
  valid_state small -> valid_state large -> quiet small -> quiet large ->
  dominates (move_state (negb turn) small v) (move_state (negb turn) large a) ->
  branch prevents_black (solve prevents_black true m) (negb turn) small v = true ->
  branch prevents_black (solve prevents_black true n) (negb turn) large a = true.
Proof.
  intros n m turn small large v a IH Hsl Hll Hs Hl Hsq Hlq Hdom Hbranch.
  set (s' := move_state (negb turn) small v) in *.
  set (l' := move_state (negb turn) large a) in *.
  assert (Hsv : valid_state s') by (apply move_preserves_validity; [exact Hs|lia]).
  assert (Hlv : valid_state l') by (apply move_preserves_validity; [exact Hl|lia]).
  assert (Hlength : length (history s') <= length (history l'))
    by (apply dominance_history_length; assumption).
  unfold branch in Hbranch |- *. fold s' in Hbranch. fold l'.
  destruct (move_result (negb turn) l') as [r|] eqn:Hlresult.
  - destruct r; try reflexivity.
    assert (Hbad : move_result (negb turn) s' = Some BlackWins).
    { destruct turn.
      - change (move_result false s' = Some BlackWins).
        change (move_result false l' = Some BlackWins) in Hlresult.
        unfold move_result in Hlresult |- *.
        destruct Hdom as [_ Hblack]. rewrite Hblack.
        destruct (has_win (black_stones l')); [reflexivity|].
        destruct (length (history l') =? 125); discriminate.
      - change (move_result true l' = Some BlackWins) in Hlresult.
        unfold move_result in Hlresult.
        destruct (has_win (white_stones l')); [discriminate|].
        destruct (length (history l') =? 125); discriminate. }
    rewrite Hbad in Hbranch. discriminate.
  - assert (Hlquiet : quiet l') by (apply continuing_move_quiet; assumption).
    assert (Hsquiet : quiet s') by (apply dominance_quiet with (large := l'); assumption).
    assert (Hnotfull : length (history l') <> 125).
    { unfold move_result in Hlresult.
      destruct (has_win _); [discriminate|].
      destruct (length (history l') =? 125) eqn:Hfull; [discriminate|].
      apply Nat.eqb_neq. exact Hfull. }
    assert (Hsresult : move_result (negb turn) s' = None).
    { unfold move_result. destruct Hsquiet as [Hw Hb].
      assert (Hcurrent : has_win
        (if negb turn then white_stones s' else black_stones s') = false)
        by (destruct turn; assumption).
      rewrite Hcurrent. destruct (length (history s') =? 125) eqn:Hfull;
        [|reflexivity].
      apply Nat.eqb_eq in Hfull.
      assert (Hmax : length (history l') <= 125).
      { unfold l'. rewrite move_state_history. lia. }
      exfalso. apply Hnotfull. lia. }
    rewrite Hsresult in Hbranch.
    rewrite Bool.negb_involutive in Hbranch |- *.
    apply IH with (m := m) (small := s');
      try assumption.
    + unfold s'. rewrite move_state_history. lia.
    + unfold l'. rewrite move_state_history. lia.
Qed.

Theorem extra_white_stones_do_not_hurt : forall n m turn small large,
  m + length (history small) = 125 ->
  n + length (history large) = 125 ->
  valid_state small -> valid_state large ->
  quiet small -> quiet large -> dominates small large ->
  solve prevents_black true m turn small = true ->
  solve prevents_black true n turn large = true.
Proof.
  induction n as [|n IH]; intros m turn small large Hsl Hll Hs Hl Hsq Hlq Hdom Hsolve.
  - rewrite solve_empty_horizon. reflexivity.
  - assert (Hlength : length (history small) <= length (history large))
      by (apply dominance_history_length; assumption).
    destruct m as [|m]; [lia|].
    rewrite solve_successor in Hsolve |- *.
    destruct turn; cbn [Bool.eqb] in *.
    + apply existsb_exists in Hsolve as [v [Hv Hbranch]].
      destruct (white_move_simulation small large v Hs Hl ltac:(lia) ltac:(lia) Hdom)
        as [a Ha].
      apply existsb_exists. exists (canonical_request a).
      split; [apply canonical_request_in|]. rewrite branch_canonical.
      apply (branch_dominance n m false small large v a); try assumption.
      intros. apply IH with (small := small0) (m := m0); assumption.
    + apply forallb_forall. intros a Ha.
      destruct (black_move_simulation small large a Hs Hl ltac:(lia) ltac:(lia) Hdom)
        as [v Hv].
      apply forallb_forall with (x := canonical_request v) in Hsolve;
        [|apply canonical_request_in]. rewrite branch_canonical in Hsolve.
      apply (branch_dominance n m true small large v a); try assumption.
      intros. apply IH with (small := small0) (m := m0); assumption.
Qed.

Definition swap_colors (st : GameState) : GameState :=
  make_state (black_stones st) (white_stones st) (history st).

Definition swap_result (r : Result) : Result :=
  match r with WhiteWins => BlackWins | BlackWins => WhiteWins | Draw => Draw end.

Lemma occupied_swap : forall st c, occupied (swap_colors st) c = occupied st c.
Proof. intros. unfold occupied, swap_colors. cbn. apply orb_comm. Qed.

Lemma legal_swap : forall st c, is_legal_move (swap_colors st) c = is_legal_move st c.
Proof. intros. unfold is_legal_move. rewrite occupied_swap. reflexivity. Qed.

Lemma fallback_swap : forall st,
  next_available_cell (swap_colors st) = next_available_cell st.
Proof.
  intros st. change (scan_free (swap_colors st) 125 = scan_free st 125).
  assert (H : forall n, scan_free (swap_colors st) n = scan_free st n).
  { induction n; [reflexivity|]. cbn [scan_free]. rewrite occupied_swap, IHn.
    reflexivity. }
  apply H.
Qed.

Lemma effective_swap : forall st c,
  effective_move (swap_colors st) c = effective_move st c.
Proof. intros. unfold effective_move. rewrite legal_swap, fallback_swap. reflexivity. Qed.

Lemma move_state_swap : forall turn st c,
  swap_colors (move_state turn st c) = move_state (negb turn) (swap_colors st) c.
Proof.
  intros [] st c; unfold move_state; rewrite effective_swap; reflexivity.
Qed.

Lemma move_result_swap : forall turn st,
  move_result (negb turn) (swap_colors st) = option_map swap_result (move_result turn st).
Proof.
  intros [] st; unfold move_result, swap_colors;
    cbn [negb white_stones black_stones history];
    destruct (has_win _); [reflexivity| |reflexivity| ];
    destruct (length (history st) =? 125); reflexivity.
Qed.

Lemma existsb_extensional : forall (f g : cell -> bool) ls,
  (forall c, f c = g c) -> existsb f ls = existsb g ls.
Proof.
  intros f g ls H. induction ls as [|c ls IH]; [reflexivity|].
  cbn. rewrite H, IH. reflexivity.
Qed.

Lemma forallb_extensional : forall (f g : cell -> bool) ls,
  (forall c, f c = g c) -> forallb f ls = forallb g ls.
Proof.
  intros f g ls H. induction ls as [|c ls IH]; [reflexivity|].
  cbn. rewrite H, IH. reflexivity.
Qed.

Lemma solve_color_symmetry : forall n owner turn st,
  solve prevents_black (negb owner) n (negb turn) (swap_colors st) =
  solve prevents_white owner n turn st.
Proof.
  induction n as [|n IH]; intros owner turn st.
  - rewrite !solve_empty_horizon. reflexivity.
  - rewrite !solve_successor.
    assert (Hturn : Bool.eqb (negb turn) (negb owner) = Bool.eqb turn owner)
      by (destruct turn, owner; reflexivity).
    rewrite Hturn.
    assert (Hbranches : forall c,
      branch prevents_black (solve prevents_black (negb owner) n)
        (negb turn) (swap_colors st) c =
      branch prevents_white (solve prevents_white owner n) turn st c).
    { intros c. unfold branch. rewrite <- move_state_swap, move_result_swap.
      destruct (move_result turn (move_state turn st c)) as [r|].
      - destruct r; reflexivity.
      - cbn [option_map]. apply IH. }
    destruct (Bool.eqb turn owner);
      [apply existsb_extensional|apply forallb_extensional]; exact Hbranches.
Qed.

(** A defensive strategy for the second player can be used by the first
    player after an extra opening stone. The simulation above also handles
    the case where that strategy asks for an already owned extra stone. *)
Theorem black_nonloss_implies_white_nonloss_value :
  black_nonloss_value = true -> white_nonloss_value = true.
Proof.
  intros Hblack. unfold white_nonloss_value. rewrite solve_successor.
  change (existsb (branch prevents_black (solve prevents_black true 124)
    true initial_state) requests = true).
  apply existsb_exists. exists 0. split.
  - apply in_seq. lia.
  - unfold branch.
    change (solve prevents_black true 124 false (make_state [0] [] [0]) = true).
    apply extra_white_stones_do_not_hurt with (m := 125) (small := initial_state).
    + reflexivity.
    + reflexivity.
    + apply initial_state_valid.
    + change (valid_state (move_state true initial_state 0)).
      apply move_preserves_validity; [apply initial_state_valid|cbn; lia].
    + split; reflexivity.
    + split; reflexivity.
    + split; [intros c H; contradiction|reflexivity].
    + pose proof (solve_color_symmetry 125 false true initial_state) as Hsym.
      change (solve prevents_black true 125 false initial_state = black_nonloss_value) in Hsym.
      rewrite Hsym. exact Hblack.
Qed.

(** This is an UNCONDITIONAL theorem about the full locked game. It rules
    out a forced second-player win, but does not distinguish draw from a
    forced first-player win. *)
Theorem white_nonloss_proved : Goal.WhiteNonLossFromEmpty.
Proof.
  destruct black_nonloss_value eqn:Hblack.
  - apply white_nonloss_value_true, black_nonloss_implies_white_nonloss_value.
    exact Hblack.
  - destruct (black_nonloss_value_false Hblack) as [w Hw].
    exists w. intros b. rewrite Hw. discriminate.
Qed.

Theorem white_nonloss_value_proved : white_nonloss_value = true.
Proof. apply white_nonloss_iff_value. exact white_nonloss_proved. Qed.

Theorem second_player_cannot_force_win : ~ BlackForcedWin.
Proof.
  intros [b Hb]. destruct white_nonloss_proved as [w Hw].
  specialize (Hw b). specialize (Hb w). congruence.
Qed.

Theorem exact_draw_iff_black_nonloss : Goal.ExactDraw <-> Goal.BlackNonLossFromEmpty.
Proof.
  split; [intros [Hb _]; exact Hb|]. intros Hb.
  split; [exact Hb|exact white_nonloss_proved].
Qed.

Theorem draw_or_first_player_forced_win : Goal.ExactDraw \/ WhiteForcedWin.
Proof.
  destruct black_nonloss_value eqn:Hblack.
  - left. apply exact_draw_iff_black_nonloss, black_nonloss_value_true. exact Hblack.
  - right. apply black_nonloss_value_false. exact Hblack.
Qed.

Print Assumptions extra_white_stones_do_not_hurt.
Print Assumptions white_nonloss_proved.
Print Assumptions second_player_cannot_force_win.
Print Assumptions exact_draw_iff_black_nonloss.
Print Assumptions draw_or_first_player_forced_win.

