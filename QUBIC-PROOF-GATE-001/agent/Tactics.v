(** Tactical pruning and an opening lower bound for the locked game.
    Distinct threatened LINES are not sufficient: their completion CELLS
    must be distinct. Existing wins must be checked before fork reasoning. *)
From Stdlib Require Import List Arith Bool Lia Permutation.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Geometry Minimax RulesFacts SafePairing.
Import ListNotations.

Fixpoint distinct_cells (xs : list cell) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (existsb (Nat.eqb x) rest) && distinct_cells rest
  end.

Lemma distinct_cells_sound : forall xs, distinct_cells xs = true -> NoDup xs.
Proof.
  induction xs as [|x xs IH]; cbn; intros H; [constructor|].
  apply andb_true_iff in H as [Hnot Hrest]. apply negb_true_iff in Hnot.
  constructor; [|apply IH; exact Hrest].
  intro Hin. apply member_spec in Hin. congruence.
Qed.

Lemma winning_line_properties : forall l,
  In l all_lines -> length l = 5 /\ NoDup l.
Proof.
  intros l Hl.
  assert (Hcheck : forallb (fun l => (length l =? 5) && distinct_cells l) all_lines = true)
    by reflexivity.
  apply forallb_forall with (x := l) in Hcheck; [|exact Hl].
  apply andb_true_iff in Hcheck as [Hlength Hnd].
  apply Nat.eqb_eq in Hlength. apply distinct_cells_sound in Hnd. auto.
Qed.

Definition intersection (a b : list cell) : list cell :=
  filter (fun c => existsb (Nat.eqb c) b) a.

Lemma winning_lines_linear : forall a b,
  In a all_lines -> In b all_lines -> a <> b -> length (intersection a b) <= 1.
Proof.
  intros a b Ha Hb Hneq.
  assert (Hcheck : forallb (fun a => forallb (fun b =>
    if line_eqb a b then true else length (intersection a b) <=? 1) all_lines) all_lines = true)
    by reflexivity.
  apply forallb_forall with (x := a) in Hcheck; [|exact Ha].
  apply forallb_forall with (x := b) in Hcheck; [|exact Hb].
  destruct (line_eqb a b) eqn:Heq.
  - apply line_eqb_spec in Heq. contradiction.
  - apply Nat.leb_le. exact Hcheck.
Qed.

Definition without (c : cell) (l : list cell) : list cell :=
  filter (fun d => negb (c =? d)) l.

Lemma without_absent : forall l c, ~ In c l -> without c l = l.
Proof.
  induction l as [|a l IH]; intros c Hnot; [reflexivity|].
  unfold without in *. cbn. destruct (c =? a) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst a. exfalso. apply Hnot. left. reflexivity.
  - cbn. rewrite IH; [reflexivity|]. intro Hin. apply Hnot. right. exact Hin.
Qed.

Lemma without_length : forall l c,
  NoDup l -> In c l -> S (length (without c l)) = length l.
Proof.
  induction l as [|a l IH]; intros c Hnd Hin; [contradiction|].
  inversion Hnd as [|? ? Hnot Htail]; subst.
  destruct (c =? a) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst a.
    unfold without at 1. cbn. rewrite Nat.eqb_refl. cbn.
    change (S (length (without c l)) = S (length l)).
    rewrite without_absent; [reflexivity|exact Hnot].
  - assert (Hcl : In c l) by (destruct Hin as [H|H]; [subst a; rewrite Nat.eqb_refl in Heq; discriminate|exact H]).
    specialize (IH c Htail Hcl).
    unfold without at 1. cbn. rewrite Heq. cbn. exact (f_equal S IH).
Qed.

Lemma filter_lengths_partition : forall (f : cell -> bool) l,
  length (filter f l) + length (filter (fun c => negb (f c)) l) = length l.
Proof.
  intros f l. induction l as [|c l IH]; [reflexivity|].
  cbn. destruct (f c); cbn; lia.
Qed.

Definition four_threat (stones l : list cell) (target : cell) : Prop :=
  In l all_lines /\ In target l /\ ~ In target stones /\
  (forall c, In c l -> c <> target -> In c stones).

Lemma threat_support : forall stones l target,
  four_threat stones l target ->
  length (without target l) = 4 /\ NoDup (without target l) /\
  incl (without target l) stones.
Proof.
  intros stones l target [Hl [Ht [Hnot Hall]]].
  destruct (winning_line_properties l Hl) as [Hlen Hnd].
  pose proof (without_length l target Hnd Ht) as Hsupport_len.
  split; [lia|]. split; [apply NoDup_filter; exact Hnd|].
  intros c Hc. apply filter_In in Hc as [Hc Hneq].
  apply negb_true_iff, Nat.eqb_neq in Hneq. apply Hall; [exact Hc|congruence].
Qed.

(** Two legal, distinct completion cells require at least seven White stones.
    The statement quantifies over actual lines and stones, not just numbers. *)
Theorem distinct_targets_require_seven_stones : forall stones l1 l2 d1 d2,
  four_threat stones l1 d1 -> four_threat stones l2 d2 -> d1 <> d2 ->
  7 <= length stones.
Proof.
  intros stones l1 l2 d1 d2 Ht1 Ht2 Htargets.
  pose proof (threat_support stones l1 d1 Ht1) as [Hlen1 [Hnd1 Hin1]].
  pose proof (threat_support stones l2 d2 Ht2) as [Hlen2 [Hnd2 Hin2]].
  destruct Ht1 as [Hl1 [Hd1 [Hnot1 Hall1]]].
  destruct Ht2 as [Hl2 [Hd2 [Hnot2 Hall2]]].
  assert (Hlines : l1 <> l2).
  { intros Heq. subst l2. apply Hnot2, Hall1; [exact Hd2|congruence]. }
  set (s1 := without d1 l1) in *.
  set (s2 := without d2 l2) in *.
  set (overlap := filter (fun c => existsb (Nat.eqb c) s1) s2).
  set (fresh := filter (fun c => negb (existsb (Nat.eqb c) s1)) s2).
  assert (Hsmall_overlap : length overlap <= 1).
  { assert (Hincl : incl overlap (intersection l2 l1)).
    { intros c Hc. apply filter_In in Hc as [Hc Hmem].
      apply member_spec in Hmem. unfold s1, without in Hmem.
      unfold s2, without in Hc.
      apply filter_In in Hmem as [Hmem _]. apply filter_In in Hc as [Hc _].
      apply filter_In. split; [exact Hc|apply member_spec; exact Hmem]. }
    pose proof (NoDup_incl_length (NoDup_filter _ Hnd2) Hincl) as Hbound.
    pose proof (winning_lines_linear l2 l1 Hl2 Hl1 ltac:(congruence)) as Hlinear.
    exact (Nat.le_trans _ _ _ Hbound Hlinear). }
  assert (Hfresh_len : 3 <= length fresh).
  { pose proof (filter_lengths_partition (fun c => existsb (Nat.eqb c) s1) s2).
    change (length overlap + length fresh = length s2) in H. lia. }
  assert (Hunion_nd : NoDup (s1 ++ fresh)).
  { apply NoDup_app; [exact Hnd1|apply NoDup_filter; exact Hnd2|].
    intros c Hc Hin. apply filter_In in Hin as [_ Hnot].
    apply negb_true_iff in Hnot. apply member_spec in Hc. congruence. }
  assert (Hunion_in : incl (s1 ++ fresh) stones).
  { intros c Hin. apply in_app_iff in Hin as [Hin|Hin].
    - apply Hin1. exact Hin.
    - apply filter_In in Hin as [Hin _]. apply Hin2. exact Hin. }
  pose proof (NoDup_incl_length Hunion_nd Hunion_in) as Hbound.
  rewrite length_app, Hlen1 in Hbound.
  exact (Nat.le_trans _ _ _ (Nat.add_le_mono _ _ _ _ (Nat.le_refl 4) Hfresh_len) Hbound).
Qed.

Definition white_completionb (st : GameState) (c : cell) : bool :=
  is_legal_move st c && has_win (c :: white_stones st).

Lemma added_win_gives_threat : forall stones c,
  has_win stones = false -> ~ In c stones -> has_win (c :: stones) = true ->
  exists l, four_threat stones l c.
Proof.
  intros stones c Hquiet Hnot Hwin.
  unfold has_win in Hwin. apply existsb_exists in Hwin as [l [Hl Hline]].
  assert (Hall : forall d, In d l -> d = c \/ In d stones).
  { intros d Hd. unfold has_line in Hline.
    apply forallb_forall with (x := d) in Hline; [|exact Hd].
    apply member_spec in Hline. cbn in Hline. intuition congruence. }
  assert (Hc : In c l).
  { destruct (in_dec Nat.eq_dec c l) as [H|H]; [exact H|].
    assert (Hbad : has_win stones = true).
    { unfold has_win. apply existsb_exists. exists l. split; [exact Hl|].
      unfold has_line. apply forallb_forall. intros d Hd. apply member_spec.
      destruct (Hall d Hd); [subst d; contradiction|assumption]. }
    congruence. }
  exists l. repeat split; try assumption.
  intros d Hd Hneq. destruct (Hall d Hd); congruence.
Qed.

Theorem white_completion_unique_below_seven : forall st c d,
  has_win (white_stones st) = false -> length (white_stones st) < 7 ->
  white_completionb st c = true -> white_completionb st d = true -> c = d.
Proof.
  intros st c d Hquiet Hlen Hc Hd.
  unfold white_completionb in Hc, Hd.
  apply andb_true_iff in Hc as [Hlegalc Hwinc].
  apply andb_true_iff in Hd as [Hlegald Hwind].
  destruct (legal_move_fresh st c Hlegalc) as [_ [Hnotc _]].
  destruct (legal_move_fresh st d Hlegald) as [_ [Hnotd _]].
  destruct (added_win_gives_threat _ c Hquiet Hnotc Hwinc) as [l1 Hl1].
  destruct (added_win_gives_threat _ d Hquiet Hnotd Hwind) as [l2 Hl2].
  destruct (Nat.eq_dec c d) as [H|H]; [exact H|].
  pose proof (distinct_targets_require_seven_stones _ _ _ _ _ Hl1 Hl2 H). lia.
Qed.

Definition blocking_policy : BlackStrategy := fun st =>
  match find (white_completionb st) all_cells with
  | Some c => c
  | None => 0
  end.

Definition white_next_safe (st : GameState) : Prop :=
  forall c, is_legal_move st c = true -> has_win (c :: white_stones st) = false.

Lemma legal_before_black_move : forall st request c,
  is_legal_move (move_state false st request) c = true -> is_legal_move st c = true.
Proof.
  intros st request c Hlegal.
  destruct (legal_move_fresh _ _ Hlegal) as [Hbound [HnotW HnotB]].
  unfold is_legal_move. apply andb_true_iff. split; [apply Nat.ltb_lt; exact Hbound|].
  apply negb_true_iff. destruct (occupied st c) eqn:Hocc; [|reflexivity].
  apply occupied_spec in Hocc. apply in_app_iff in Hocc as [H|H].
  - exfalso. apply HnotW. exact H.
  - exfalso. apply HnotB. change (In c (effective_move st request :: black_stones st)).
    right. exact H.
Qed.

Lemma completion_before_black_move : forall st request c,
  white_completionb (move_state false st request) c = true -> white_completionb st c = true.
Proof.
  intros st request c H. unfold white_completionb in *.
  apply andb_true_iff in H as [Hlegal Hwin].
  apply andb_true_iff. split; [apply legal_before_black_move with (request := request); exact Hlegal|exact Hwin].
Qed.

Theorem blocking_policy_removes_unique_completion : forall st,
  has_win (white_stones st) = false -> length (white_stones st) < 7 ->
  white_next_safe (move_state false st (blocking_policy st)).
Proof.
  intros st Hquiet Hsmall c Hlegal.
  set (next := move_state false st (blocking_policy st)) in *.
  destruct (has_win (c :: white_stones next)) eqn:Hwin; [|reflexivity].
  assert (Hcompletion : white_completionb next c = true).
  { unfold white_completionb. rewrite Hlegal, Hwin. reflexivity. }
  pose proof (completion_before_black_move st (blocking_policy st) c Hcompletion) as Hold.
  destruct (find (white_completionb st) all_cells) eqn:Hfind.
  - pose proof Hfind as Hfound. apply find_some in Hfound as [Hin Hc].
    pose proof (white_completion_unique_below_seven st c c0 Hquiet Hsmall Hold Hc) as Heq.
    subst c0.
    assert (Heffective : effective_move st (blocking_policy st) = c).
    { unfold blocking_policy, effective_move. rewrite Hfind.
      unfold white_completionb in Hc. apply andb_true_iff in Hc as [Hcl _].
      rewrite Hcl. reflexivity. }
    destruct (legal_move_fresh next c Hlegal) as [_ [_ HnotB]].
    exfalso. apply HnotB.
    change (In c (effective_move st (blocking_policy st) :: black_stones st)).
    rewrite Heffective. left. reflexivity.
  - assert (Hlegal_old : is_legal_move st c = true)
      by (apply legal_before_black_move with (request := blocking_policy st); exact Hlegal).
    destruct (legal_move_fresh st c Hlegal_old) as [Hbound _].
    assert (Hin : In c all_cells) by (apply in_seq; lia).
    pose proof (@find_none cell _ _ Hfind c Hin) as Hnone. congruence.
Qed.

Lemma win_requires_five_stones : forall stones,
  has_win stones = true -> 5 <= length stones.
Proof.
  intros stones Hwin. unfold has_win in Hwin.
  apply existsb_exists in Hwin as [l [Hl Hline]].
  destruct (winning_line_properties l Hl) as [Hlength Hnd].
  assert (Hincl : incl l stones).
  { intros c Hc. unfold has_line in Hline.
    apply forallb_forall with (x := c) in Hline; [apply member_spec; exact Hline|exact Hc]. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hbound. rewrite Hlength in Hbound. exact Hbound.
Qed.

Lemma short_stones_no_win : forall stones,
  length stones < 5 -> has_win stones = false.
Proof.
  intros stones Hlen. destruct (has_win stones) eqn:Hwin; [|reflexivity].
  pose proof (win_requires_five_stones stones Hwin). lia.
Qed.

Lemma initial_white_next_safe : white_next_safe initial_state.
Proof. intros c Hlegal. apply short_stones_no_win. cbn. lia. Qed.

(** A prefix bound: [step_game (2*rounds)] is deliberately truncated.
    Its lack of a White win is NOT a draw conclusion about the full game. *)
Theorem seven_round_blocking_prefix : forall rounds st w,
  length (white_stones st) + rounds <= 7 ->
  2 * rounds + length (history st) <= 125 -> valid_state st ->
  (rounds = 0 \/ white_next_safe st) ->
  outcome (step_game (2 * rounds) true st w blocking_policy) <> WhiteWins.
Proof.
  induction rounds as [|rounds IH]; intros st w Hcount Hlen Hvalid Hsafe;
    [discriminate|].
  destruct Hsafe as [Hzero|Hsafe]; [discriminate|].
  replace (2 * S rounds) with (S (S (2 * rounds))) by lia.
  rewrite step_game_equation. cbn zeta.
  set (after_white := move_state true st (w st)).
  assert (Hwhite_len : length (history after_white) = S (length (history st)))
    by (apply move_state_history).
  assert (Hwhite_count : length (white_stones after_white) = S (length (white_stones st)))
    by reflexivity.
  assert (Hwhite_valid : valid_state after_white) by
    (apply move_preserves_validity; [exact Hvalid|lia]).
  assert (Hwhite_nowin : has_win (white_stones after_white) = false).
  { apply Hsafe, effective_move_is_legal; [exact Hvalid|lia]. }
  unfold move_result at 1. rewrite Hwhite_nowin.
  destruct (length (history after_white) =? 125); [discriminate|].
  rewrite step_game_equation. cbn zeta.
  change (outcome
    (let next := move_state false after_white (blocking_policy after_white) in
     match move_result false next with
     | Some r => make_trace next r
     | None => step_game (2 * rounds) true next w blocking_policy
     end) <> WhiteWins).
  set (after_black := move_state false after_white (blocking_policy after_white)).
  cbv zeta. unfold move_result.
  destruct (has_win (black_stones after_black)); [discriminate|].
  destruct (length (history after_black) =? 125); [discriminate|].
  apply IH.
  - change (length (white_stones after_white) + rounds <= 7). rewrite Hwhite_count. lia.
  - unfold after_black. rewrite move_state_history, Hwhite_len. lia.
  - apply move_preserves_validity; [exact Hwhite_valid|lia].
  - destruct rounds as [|rounds]; [left; reflexivity|]. right.
    apply blocking_policy_removes_unique_completion; [exact Hwhite_nowin|].
    rewrite Hwhite_count. lia.
Qed.

Theorem no_white_win_in_first_fourteen_plies : forall w,
  outcome (step_game 14 true initial_state w blocking_policy) <> WhiteWins.
Proof.
  intros w. apply (seven_round_blocking_prefix 7 initial_state w);
    [reflexivity|cbn; lia|apply initial_state_valid|right; apply initial_white_next_safe].
Qed.

(** General evaluator facts connect a truncated prefix to an actual full play
    without unfolding the 125-ply symbolic tree. *)
Lemma play_history_never_shrinks : forall n turn st w b,
  length (history st) <= length (history (final_state (step_game n turn st w b))).
Proof.
  induction n as [|n IH]; intros turn st w b; [apply Nat.le_refl|].
  rewrite step_game_equation. cbn zeta.
  set (next := move_state turn st (if turn then w st else b st)).
  assert (Hnext : length (history next) = S (length (history st))) by (apply move_state_history).
  destruct (move_result turn next).
  - cbn. lia.
  - specialize (IH (negb turn) next w b). lia.
Qed.

Lemma white_win_visible_or_later : forall short long turn st w b,
  short <= long -> outcome (step_game long turn st w b) = WhiteWins ->
  outcome (step_game short turn st w b) = WhiteWins \/
  S short + length (history st) <= length (history (final_state (step_game long turn st w b))).
Proof.
  induction short as [|short IH]; intros long turn st w b Hdepth Hwin.
  - right. destruct long as [|long]; [discriminate|].
    rewrite step_game_equation. cbn zeta.
    set (next := move_state turn st (if turn then w st else b st)).
    assert (Hnext : length (history next) = S (length (history st))) by (apply move_state_history).
    destruct (move_result turn next).
    + cbn. lia.
    + pose proof (play_history_never_shrinks long (negb turn) next w b). lia.
  - destruct long as [|long]; [lia|].
    rewrite step_game_equation in Hwin |- *. cbn zeta in Hwin |- *.
    set (next := move_state turn st (if turn then w st else b st)) in *.
    assert (Hnext : length (history next) = S (length (history st))) by (apply move_state_history).
    destruct (move_result turn next) as [r|] eqn:Hresult.
    + left. exact Hwin.
    + destruct (IH long (negb turn) next w b ltac:(lia) Hwin) as [Hearly|Hlate].
      * left. exact Hearly.
      * right. rewrite step_game_equation. cbn zeta. fold next. rewrite Hresult. lia.
Qed.

Local Opaque step_game.

Theorem blocking_policy_delays_white_win_until_ply_fifteen : forall w,
  outcome (play w blocking_policy) = WhiteWins ->
  15 <= length (history (final_state (play w blocking_policy))).
Proof.
  intros w Hwin. unfold play in Hwin |- *.
  destruct (white_win_visible_or_later 14 125 true initial_state w blocking_policy
    ltac:(lia) Hwin) as [Hearly|Hlate].
  - exfalso. apply (no_white_win_in_first_fourteen_plies w). exact Hearly.
  - exact Hlate.
Qed.

Definition black_next_safe (st : GameState) : Prop :=
  forall c, is_legal_move st c = true -> has_win (c :: black_stones st) = false.

Lemma legal_cell_implies_space : forall st c,
  valid_state st -> is_legal_move st c = true -> length (history st) < 125.
Proof.
  intros st c Hvalid Hlegal.
  pose proof Hlegal as Hfresh. unfold is_legal_move in Hfresh.
  apply andb_true_iff in Hfresh as [Hrange Hfree].
  apply Nat.ltb_lt in Hrange. apply negb_true_iff in Hfree.
  assert (Hnot : ~ In c (history st)).
  { intros Hin. apply (valid_history_occupied st c Hvalid) in Hin. congruence. }
  assert (Hnd : NoDup (c :: history st)) by (constructor; [exact Hnot|apply history_nodup; exact Hvalid]).
  assert (Hincl : incl (c :: history st) all_cells).
  { intros d [Hd|Hd]; apply in_seq; split; [lia| |lia|].
    - subst d. exact Hrange.
    - pose proof (history_valid st Hvalid) as Hh. rewrite Forall_forall in Hh.
      exact (Hh d Hd). }
  pose proof (NoDup_incl_length Hnd Hincl) as Hbound.
  change (S (length (history st)) <= 125) in Hbound. lia.
Qed.

Lemma completion_survives_different_black_move : forall st request target,
  white_completionb st target = true -> effective_move st request <> target ->
  white_completionb (move_state false st request) target = true.
Proof.
  intros st request target Hcompletion Hneq.
  unfold white_completionb in *. apply andb_true_iff in Hcompletion as [Hlegal Hwin].
  destruct (legal_move_fresh st target Hlegal) as [Hbound [HnotW HnotB]].
  apply andb_true_iff. split; [|exact Hwin].
  unfold is_legal_move. apply andb_true_iff. split; [apply Nat.ltb_lt; exact Hbound|].
  apply negb_true_iff.
  destruct (occupied (move_state false st request) target) eqn:Hocc; [|reflexivity].
  apply occupied_spec in Hocc. apply in_app_iff in Hocc as [Hwhite|Hblack].
  - exfalso. apply HnotW. exact Hwhite.
  - change (In target (effective_move st request :: black_stones st)) in Hblack.
    destruct Hblack as [H|H]; [congruence|contradiction].
Qed.

Lemma existsb_all_false : forall (f : cell -> bool) xs,
  (forall c, In c xs -> f c = false) -> existsb f xs = false.
Proof.
  intros f xs. induction xs as [|c xs IH]; intros H; [reflexivity|].
  cbn. rewrite H by (left; reflexivity). cbn. apply IH.
  intros d Hd. apply H. right. exact Hd.
Qed.

Lemma forallb_false_witness : forall (f : cell -> bool) xs c,
  In c xs -> f c = false -> forallb f xs = false.
Proof.
  intros f xs c Hin Hfalse.
  destruct (forallb f xs) eqn:Hall; [|reflexivity].
  apply forallb_forall with (x := c) in Hall; [congruence|exact Hin].
Qed.

Local Opaque solve.

Lemma completing_white_branch_is_false : forall n st target,
  white_completionb st target = true ->
  branch prevents_white (solve prevents_white false n) true st target = false.
Proof.
  intros n st target H. unfold white_completionb in H.
  apply andb_true_iff in H as [Hlegal Hwin].
  assert (Heff : effective_move st target = target) by
    (unfold effective_move; rewrite Hlegal; reflexivity).
  unfold branch, move_result, move_state. rewrite Heff.
  cbn [white_stones black_stones history]. rewrite Hwin. reflexivity.
Qed.

(** Ignoring a completion cell loses unless Black can win immediately.
    This establishes a sound pruning rule for the FULL remaining horizon. *)
Theorem ignoring_white_completion_loses : forall n st request target,
  S (S n) + length (history st) = 125 -> valid_state st -> black_next_safe st ->
  white_completionb st target = true -> effective_move st request <> target ->
  branch prevents_white (solve prevents_white false (S n)) false st request = false.
Proof.
  intros n st request target Hlen Hvalid Hblack Htarget Hneq.
  set (next := move_state false st request).
  assert (Hnext_valid : valid_state next) by (apply move_preserves_validity; [exact Hvalid|lia]).
  assert (Hcompletion : white_completionb next target = true) by
    (apply completion_survives_different_black_move; assumption).
  pose proof Hcompletion as Hlegal_target. unfold white_completionb in Hlegal_target.
  apply andb_true_iff in Hlegal_target as [Hlegal_target _].
  pose proof (legal_cell_implies_space next target Hnext_valid Hlegal_target) as Hspace.
  assert (Hblack_nowin : has_win (black_stones next) = false).
  { apply Hblack, effective_move_is_legal; [exact Hvalid|lia]. }
  unfold branch at 1. fold next. unfold move_result at 1. rewrite Hblack_nowin.
  assert (Hnotfull : (length (history next) =? 125) = false) by (apply Nat.eqb_neq; lia).
  rewrite Hnotfull.
  change (solve prevents_white false (S n) true next = false).
  rewrite pairing_solve_successor. cbn [Bool.eqb].
  apply forallb_false_witness with (c := canonical_request target);
    [apply canonical_request_in|].
  rewrite branch_canonical. apply completing_white_branch_is_false. exact Hcompletion.
Qed.

Lemma branch_same_effective : forall accept continuation turn st a b,
  effective_move st a = effective_move st b ->
  branch accept continuation turn st a = branch accept continuation turn st b.
Proof.
  intros accept continuation turn st a b Heff.
  unfold branch, move_state. rewrite Heff. reflexivity.
Qed.

(** When Black has no immediate win, the minimax value at a White threat
    is exactly the value of blocking its completion cell. *)
Theorem forced_block_minimax_equality : forall n st target,
  S (S n) + length (history st) = 125 -> valid_state st -> black_next_safe st ->
  white_completionb st target = true ->
  solve prevents_white false (S (S n)) false st =
    branch prevents_white (solve prevents_white false (S n)) false st target.
Proof.
  intros n st target Hlen Hvalid Hblack Htarget.
  rewrite pairing_solve_successor. cbn [Bool.eqb].
  pose proof Htarget as Hlegal. unfold white_completionb in Hlegal.
  apply andb_true_iff in Hlegal as [Hlegal _].
  assert (Heff : effective_move st target = target) by
    (unfold effective_move; rewrite Hlegal; reflexivity).
  destruct (branch prevents_white (solve prevents_white false (S n)) false st target) eqn:Hchosen.
  - apply existsb_exists. exists (canonical_request target).
    split; [apply canonical_request_in|]. rewrite branch_canonical. exact Hchosen.
  - apply existsb_all_false. intros request Hin.
    destruct (Nat.eq_dec (effective_move st request) target) as [Heq|Hneq].
    + rewrite (branch_same_effective prevents_white (solve prevents_white false (S n))
        false st request target ltac:(congruence)). exact Hchosen.
    + apply ignoring_white_completion_loses with (target := target); assumption.
Qed.

Theorem distinct_fork_is_forced_white_win : forall n st c d,
  S (S n) + length (history st) = 125 -> valid_state st -> black_next_safe st ->
  white_completionb st c = true -> white_completionb st d = true -> c <> d ->
  solve prevents_white false (S (S n)) false st = false.
Proof.
  intros n st c d Hlen Hvalid Hblack Hc Hd Hneq.
  rewrite pairing_solve_successor. cbn [Bool.eqb].
  apply existsb_all_false. intros request Hin.
  destruct (Nat.eq_dec (effective_move st request) c) as [Heq|Hne].
  - apply ignoring_white_completion_loses with (target := d); try assumption. congruence.
  - apply ignoring_white_completion_loses with (target := c); assumption.
Qed.

Definition black_next_safeb (st : GameState) : bool :=
  forallb (fun c => negb (is_legal_move st c && has_win (c :: black_stones st))) all_cells.

Definition at_least_two (xs : list cell) : bool :=
  match xs with
  | _ :: _ :: _ => true
  | _ => false
  end.

Lemma at_least_two_sound : forall xs,
  NoDup xs -> at_least_two xs = true ->
  exists c d, In c xs /\ In d xs /\ c <> d.
Proof.
  intros [|c [|d rest]] Hnd H; try discriminate.
  inversion Hnd as [|? ? Hnot _]; subst.
  exists c, d. split; [left; reflexivity|]. split; [right; left; reflexivity|].
  intros Heq. subst d. apply Hnot. left. reflexivity.
Qed.

Definition distinct_white_forkb (st : GameState) : bool :=
  at_least_two (filter (white_completionb st) all_cells).

Local Opaque at_least_two.

Definition fork_cutoffb (st : GameState) : bool :=
  black_next_safeb st && distinct_white_forkb st.

Lemma black_next_safeb_sound : forall st,
  black_next_safeb st = true -> black_next_safe st.
Proof.
  intros st H c Hlegal.
  destruct (legal_move_fresh st c Hlegal) as [Hbound _].
  unfold black_next_safeb in H.
  apply forallb_forall with (x := c) in H; [|apply in_seq; lia].
  rewrite Hlegal in H. cbn in H. apply negb_true_iff in H. exact H.
Qed.

Lemma distinct_white_forkb_sound : forall st,
  distinct_white_forkb st = true ->
  exists c d, white_completionb st c = true /\ white_completionb st d = true /\ c <> d.
Proof.
  intros st H. unfold distinct_white_forkb in H.
  pose proof (NoDup_filter (white_completionb st) (seq_NoDup 125 0)) as Hnd.
  destruct (at_least_two_sound _ Hnd H) as [c [d [Hc [Hd Hneq]]]].
  apply filter_In in Hc as [_ Hc]. apply filter_In in Hd as [_ Hd].
  exists c, d. auto.
Qed.

Theorem checked_fork_minimax : forall n st,
  S (S n) + length (history st) = 125 -> valid_state st -> fork_cutoffb st = true ->
  solve prevents_white false (S (S n)) false st = false.
Proof.
  intros n st Hlen Hvalid Hcheck. unfold fork_cutoffb in Hcheck.
  apply andb_true_iff in Hcheck as [Hblack Hwhite].
  apply black_next_safeb_sound in Hblack.
  apply distinct_white_forkb_sound in Hwhite as [c [d [Hc [Hd Hneq]]]].
  apply distinct_fork_is_forced_white_win with (c := c) (d := d); assumption.
Qed.

Theorem checked_fork_has_total_white_win : forall n st,
  S (S n) + length (history st) = 125 -> valid_state st -> fork_cutoffb st = true ->
  exists w : WhiteStrategy, forall b : BlackStrategy,
    outcome (step_game (S (S n)) false st w b) = WhiteWins.
Proof.
  intros n st Hlen Hvalid Hcheck.
  pose proof (checked_fork_minimax n st Hlen Hvalid Hcheck) as Hsolve.
  exists (search_policy prevents_white false false). intros b.
  pose proof (solve_policy_sound prevents_white false false (S (S n)) false st b Hlen Hsolve) as Hsound.
  cbn [policies Bool.eqb] in Hsound.
  destruct (outcome (step_game (S (S n)) false st
    (search_policy prevents_white false false) b)); cbn in Hsound; congruence.
Qed.

Print Assumptions winning_lines_linear.
Print Assumptions distinct_targets_require_seven_stones.
Print Assumptions blocking_policy_removes_unique_completion.
Print Assumptions no_white_win_in_first_fourteen_plies.
Print Assumptions blocking_policy_delays_white_win_until_ply_fifteen.
Print Assumptions ignoring_white_completion_loses.
Print Assumptions forced_block_minimax_equality.
Print Assumptions distinct_fork_is_forced_white_win.
Print Assumptions checked_fork_minimax.
Print Assumptions checked_fork_has_total_white_win.
