(** Sound pairing leaves for the LOCKED game. A checked leaf supplies a
    complete defensive strategy for every continuation, not just a predicate
    assumed to remain true. This does not prove reachability from empty. *)
From Stdlib Require Import List Arith Bool Lia Permutation.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Minimax RulesFacts.
Import ListNotations.

Definition mate_function := cell -> cell.
Definition well_mated (mate : mate_function) : Prop :=
  forall c, c < 125 -> mate c < 125 /\ mate (mate c) = c.

(** Fixed points are unpaired cells. Nontrivial pairs must be reciprocal. *)
Definition response_invariant (mate : mate_function) (st : GameState) : Prop :=
  forall c, c < 125 -> mate c <> c -> In c (white_stones st) ->
    In (mate c) (black_stones st).

Definition line_coverage (mate : mate_function) (st : GameState) : Prop :=
  forall l, In l all_lines ->
    (exists c, In c l /\ In c (black_stones st)) \/
    (exists c, In c l /\ In (mate c) l /\ mate c <> c).

Definition pairing_safe (mate : mate_function) (st : GameState) : Prop :=
  response_invariant mate st /\ line_coverage mate st.

Lemma locked_line_cell_bound : forall l c,
  In l all_lines -> In c l -> c < 125.
Proof.
  intros l c Hl Hc.
  assert (Hcheck : forallb (fun l => forallb (fun c => c <? 125) l) all_lines = true)
    by reflexivity.
  apply forallb_forall with (x := l) in Hcheck; [|exact Hl].
  apply forallb_forall with (x := c) in Hcheck; [apply Nat.ltb_lt; exact Hcheck|exact Hc].
Qed.

Lemma nodup_app_disjoint : forall (xs ys : list cell),
  NoDup (xs ++ ys) -> forall c, In c xs -> ~ In c ys.
Proof.
  intros xs ys H. induction xs as [|x xs IH]; intros c Hc; [contradiction|].
  inversion H as [|? ? Hnot Htail]; subst.
  destruct Hc as [->|Hc].
  - intros Hin. apply Hnot, in_app_iff. auto.
  - apply IH; assumption.
Qed.

Lemma valid_colors_disjoint : forall st c,
  valid_state st -> In c (white_stones st) -> ~ In c (black_stones st).
Proof.
  intros st c Hvalid.
  apply nodup_app_disjoint.
  eapply Permutation_NoDup; [exact (history_partition st Hvalid)|exact (history_nodup st Hvalid)].
Qed.

Lemma legal_move_fresh : forall st c,
  is_legal_move st c = true ->
  c < 125 /\ ~ In c (white_stones st) /\ ~ In c (black_stones st).
Proof.
  intros st c H. unfold is_legal_move in H.
  apply andb_true_iff in H as [Hbound Hfree].
  apply Nat.ltb_lt in Hbound. apply negb_true_iff in Hfree.
  split; [exact Hbound|]. split; intro Hin;
    assert (Hocc : occupied st c = true) by (apply occupied_spec, in_app_iff; auto);
    congruence.
Qed.

Lemma coverage_monotone : forall mate small large,
  incl (black_stones small) (black_stones large) ->
  line_coverage mate small -> line_coverage mate large.
Proof.
  intros mate small large Hincl H l Hl. destruct (H l Hl) as [[c [Hc Hb]]|Hpair].
  - left. exists c. split; [exact Hc|apply Hincl; exact Hb].
  - right. exact Hpair.
Qed.

Lemma paired_white_move_cannot_win : forall mate st request,
  valid_state st -> length (history st) < 125 ->
  well_mated mate -> pairing_safe mate st ->
  has_win (white_stones (move_state true st request)) = false.
Proof.
  intros mate st request Hvalid Hlen Hmate [Hresponse Hcover].
  set (next := move_state true st request).
  assert (Hnext : valid_state next) by (apply move_preserves_validity; assumption).
  destruct (has_win (white_stones next)) eqn:Hwin; [|reflexivity].
  unfold has_win in Hwin. apply existsb_exists in Hwin as [l [Hl Hline]].
  assert (Hall : forall c, In c l -> In c (white_stones next)).
  { intros c Hc. unfold has_line in Hline.
    apply forallb_forall with (x := c) in Hline; [apply member_spec; exact Hline|exact Hc]. }
  exfalso.
  destruct (Hcover l Hl) as [[c [Hc Hb]]|[c [Hc [Hd Hneq]]]].
  - pose proof (valid_colors_disjoint next c Hnext (Hall c Hc)) as Hbad.
    apply Hbad. exact Hb.
  - pose proof (Hall c Hc) as Hcw. pose proof (Hall (mate c) Hd) as Hdw.
    assert (Hc_bound : c < 125) by (eapply locked_line_cell_bound; eassumption).
    destruct (Hmate c Hc_bound) as [Hd_bound Hinv].
    change (In c (effective_move st request :: white_stones st)) in Hcw.
    change (In (mate c) (effective_move st request :: white_stones st)) in Hdw.
    destruct Hcw as [Hcx|Hcw], Hdw as [Hdx|Hdw].
    + exfalso. apply Hneq. congruence.
    + assert (Hcn : mate (mate c) <> mate c) by congruence.
      pose proof (Hresponse (mate c) Hd_bound Hcn Hdw) as Hblack.
      rewrite Hinv in Hblack.
      apply (valid_colors_disjoint next c Hnext (Hall c Hc)). exact Hblack.
    + pose proof (Hresponse c Hc_bound Hneq Hcw) as Hblack.
      apply (valid_colors_disjoint next (mate c) Hnext (Hall (mate c) Hd)). exact Hblack.
    + pose proof (Hresponse c Hc_bound Hneq Hcw) as Hblack.
      apply (valid_colors_disjoint st (mate c) Hvalid Hdw). exact Hblack.
Qed.

(** An unpaired move, or a pair already blocked by Black, permits any legal
    reply. Otherwise the partner is free and is taken immediately. *)
Definition pairing_reply (mate : mate_function) (after_white : GameState) (x : cell) : cell :=
  if (mate x =? x) || occupied after_white (mate x) then 0 else mate x.

Lemma reply_restores_pairing : forall mate st request,
  valid_state st -> length (history st) < 125 ->
  well_mated mate -> pairing_safe mate st ->
  let x := effective_move st request in
  let after_white := move_state true st request in
  pairing_safe mate
    (move_state false after_white (pairing_reply mate after_white x)).
Proof.
  intros mate st request Hvalid Hlen Hmate [Hresponse Hcover].
  cbv zeta. set (x := effective_move st request).
  set (after_white := move_state true st request).
  set (answer := pairing_reply mate after_white x).
  assert (Hlegal : is_legal_move st x = true) by
    (apply effective_move_is_legal; assumption).
  destruct (legal_move_fresh st x Hlegal) as [Hx_bound [Hx_white Hx_black]].
  destruct (Hmate x Hx_bound) as [Hy_bound Hinv].
  assert (Hpartner_not_white : mate x <> x -> ~ In (mate x) (white_stones after_white)).
  { intros Hneq Hwhite.
    change (In (mate x) (x :: white_stones st)) in Hwhite.
    destruct Hwhite as [Heq|Hwhite]; [congruence|].
    assert (Hother : mate (mate x) <> mate x) by congruence.
    pose proof (Hresponse (mate x) Hy_bound Hother Hwhite) as Hbad.
    rewrite Hinv in Hbad. contradiction. }
  split.
  - intros c Hc_bound Hneq Hwhite.
    change (In c (x :: white_stones st)) in Hwhite.
    change (In (mate c) (effective_move after_white answer :: black_stones st)).
    destruct Hwhite as [Hcx|Hwhite].
    + subst c. destruct (existsb (Nat.eqb (mate x)) (black_stones st)) eqn:Hblack.
      * right. apply member_spec. exact Hblack.
      * assert (Hfree : occupied after_white (mate x) = false).
        { destruct (occupied after_white (mate x)) eqn:Hocc; [|reflexivity].
          apply occupied_spec in Hocc. apply in_app_iff in Hocc as [Hwhite|Hbad].
          - exfalso. apply (Hpartner_not_white Hneq). exact Hwhite.
          - assert (Hyes : existsb (Nat.eqb (mate x)) (black_stones st) = true)
              by (apply member_spec; exact Hbad). congruence. }
        assert (Hanswer : answer = mate x).
        { unfold answer, pairing_reply. rewrite Hfree.
          assert (Hnot : (mate x =? x) = false) by (apply Nat.eqb_neq; exact Hneq).
          rewrite Hnot. reflexivity. }
        assert (Hpartner_legal : is_legal_move after_white (mate x) = true).
        { unfold is_legal_move. apply andb_true_iff. split.
          - apply Nat.ltb_lt. exact Hy_bound.
          - rewrite Hfree. reflexivity. }
        left. unfold effective_move. rewrite Hanswer, Hpartner_legal. reflexivity.
    + right. apply Hresponse; assumption.
  - apply coverage_monotone with (small := st); [|exact Hcover].
    intros c Hc. change (In c (effective_move after_white answer :: black_stones st)).
    right. exact Hc.
Qed.

Lemma pairing_solve_successor : forall accept owner n turn st,
  solve accept owner (S n) turn st =
  if Bool.eqb turn owner
  then existsb (branch accept (solve accept owner n) turn st) requests
  else forallb (branch accept (solve accept owner n) turn st) requests.
Proof. reflexivity. Qed.

Lemma pairing_solve_zero : forall accept owner turn st,
  solve accept owner 0 turn st = accept Draw.
Proof. reflexivity. Qed.

Local Opaque solve.

(** The crucial game-theoretic leaf theorem, including the White move BEFORE
    Black's response and both players' immediate terminal checks. *)
Theorem pairing_safe_minimax : forall n st mate,
  n + length (history st) = 125 -> valid_state st ->
  well_mated mate -> pairing_safe mate st ->
  solve prevents_white false n true st = true.
Proof.
  fix IH 1. intros n st mate Hlen Hvalid Hmate Hsafe.
  destruct n as [|n]; [rewrite pairing_solve_zero; reflexivity|].
  rewrite pairing_solve_successor. cbn [Bool.eqb].
  apply forallb_forall. intros request Hin.
  unfold branch. set (after_white := move_state true st request).
  assert (Hwhite_len : length (history after_white) = S (length (history st)))
    by (apply move_state_history).
  assert (Hwhite_valid : valid_state after_white) by
    (apply move_preserves_validity; [exact Hvalid|lia]).
  assert (Hno_win : has_win (white_stones after_white) = false) by
    (apply paired_white_move_cannot_win with (mate := mate); try assumption; lia).
  unfold move_result. rewrite Hno_win.
  destruct (length (history after_white) =? 125) eqn:Hfull; [reflexivity|].
  apply Nat.eqb_neq in Hfull.
  destruct n as [|n]; [exfalso; apply Hfull; lia|].
  change (solve prevents_white false (S n) false after_white = true).
  rewrite pairing_solve_successor. cbn [Bool.eqb].
  set (answer := pairing_reply mate after_white (effective_move st request)).
  apply existsb_exists. exists (canonical_request answer).
  split; [apply canonical_request_in|]. rewrite branch_canonical.
  unfold branch. set (after_black := move_state false after_white answer).
  assert (Hblack_len : length (history after_black) = S (length (history after_white)))
    by (apply move_state_history).
  assert (Hblack_valid : valid_state after_black) by
    (apply move_preserves_validity; [exact Hwhite_valid|lia]).
  assert (Hblack_safe : pairing_safe mate after_black).
  { apply reply_restores_pairing; try assumption; lia. }
  unfold move_result.
  destruct (has_win (black_stones after_black)); [reflexivity|].
  destruct (length (history after_black) =? 125); [reflexivity|].
  apply (IH n after_black mate); try assumption. lia.
Qed.

Definition static_pairing_policy (mate : mate_function) : BlackStrategy :=
  fun st => match history st with
  | [] => 0
  | x :: _ => pairing_reply mate st x
  end.

(** The efficient policy itself is verified, independently of minimax search.
    At a valid pairing leaf it works against every total White policy. *)
Theorem static_pairing_policy_nonloss : forall n st mate w,
  n + length (history st) = 125 -> valid_state st ->
  well_mated mate -> pairing_safe mate st ->
  outcome (step_game n true st w (static_pairing_policy mate)) <> WhiteWins.
Proof.
  fix IH 1. intros n st mate w Hlen Hvalid Hmate Hsafe.
  destruct n as [|n]; [discriminate|].
  rewrite step_game_equation. cbn zeta.
  set (after_white := move_state true st (w st)).
  assert (Hwhite_len : length (history after_white) = S (length (history st)))
    by (apply move_state_history).
  assert (Hwhite_valid : valid_state after_white) by
    (apply move_preserves_validity; [exact Hvalid|lia]).
  assert (Hno_win : has_win (white_stones after_white) = false) by
    (apply paired_white_move_cannot_win with (mate := mate); try assumption; lia).
  unfold move_result at 1. rewrite Hno_win.
  destruct (length (history after_white) =? 125) eqn:Hfull; [discriminate|].
  apply Nat.eqb_neq in Hfull.
  destruct n as [|n]; [exfalso; apply Hfull; lia|].
  rewrite step_game_equation. cbn zeta.
  assert (Hanswer : static_pairing_policy mate after_white =
    pairing_reply mate after_white (effective_move st (w st))) by reflexivity.
  change (outcome
    (let next := move_state false after_white (static_pairing_policy mate after_white) in
     match move_result false next with
     | Some r => make_trace next r
     | None => step_game n true next w (static_pairing_policy mate)
     end) <> WhiteWins).
  rewrite Hanswer.
  set (after_black := move_state false after_white
    (pairing_reply mate after_white (effective_move st (w st)))).
  cbv zeta.
  assert (Hblack_len : length (history after_black) = S (length (history after_white)))
    by (apply move_state_history).
  assert (Hblack_valid : valid_state after_black) by
    (apply move_preserves_validity; [exact Hwhite_valid|lia]).
  assert (Hblack_safe : pairing_safe mate after_black).
  { apply reply_restores_pairing; try assumption; lia. }
  unfold move_result.
  destruct (has_win (black_stones after_black)); [discriminate|].
  destruct (length (history after_black) =? 125); [discriminate|].
  apply (IH n after_black mate w); try assumption. lia.
Qed.

(** Compact, executable certificates are total partner tables. *)
Definition table_mate (table : list cell) (c : cell) : cell := nth c table c.

Definition mate_tableb (table : list cell) : bool :=
  (length table =? 125) &&
  forallb (fun c => (table_mate table c <? 125) &&
    (table_mate table (table_mate table c) =? c)) all_cells.

Definition responseb (table : list cell) (st : GameState) : bool :=
  forallb (fun c =>
    (table_mate table c =? c) ||
    negb (existsb (Nat.eqb c) (white_stones st)) ||
    existsb (Nat.eqb (table_mate table c)) (black_stones st)) all_cells.

Definition coverageb (table : list cell) (st : GameState) : bool :=
  forallb (fun l =>
    existsb (fun c => existsb (Nat.eqb c) (black_stones st)) l ||
    existsb (fun c => negb (table_mate table c =? c) &&
      existsb (Nat.eqb (table_mate table c)) l) l) all_lines.

Definition pairing_leafb (table : list cell) (st : GameState) : bool :=
  mate_tableb table && responseb table st && coverageb table st.

Lemma mate_tableb_sound : forall table,
  mate_tableb table = true -> well_mated (table_mate table).
Proof.
  intros table H c Hc. unfold mate_tableb in H.
  apply andb_true_iff in H as [_ H].
  apply forallb_forall with (x := c) in H; [|apply in_seq; lia].
  apply andb_true_iff in H as [Hrange Hinv].
  apply Nat.ltb_lt in Hrange. apply Nat.eqb_eq in Hinv. auto.
Qed.

Lemma responseb_sound : forall table st,
  responseb table st = true -> response_invariant (table_mate table) st.
Proof.
  intros table st H c Hc Hneq Hwhite. unfold responseb in H.
  apply forallb_forall with (x := c) in H; [|apply in_seq; lia].
  apply orb_true_iff in H as [H|H]; [|apply member_spec; exact H].
  apply orb_true_iff in H as [H|H].
  - apply Nat.eqb_eq in H. contradiction.
  - apply negb_true_iff in H.
    assert (Hyes : existsb (Nat.eqb c) (white_stones st) = true)
      by (apply member_spec; exact Hwhite). congruence.
Qed.

Lemma coverageb_sound : forall table st,
  coverageb table st = true -> line_coverage (table_mate table) st.
Proof.
  intros table st H l Hl. unfold coverageb in H.
  apply forallb_forall with (x := l) in H; [|exact Hl].
  apply orb_true_iff in H as [H|H]; apply existsb_exists in H as [c [Hc H]].
  - left. exists c. split; [exact Hc|apply member_spec; exact H].
  - right. exists c. apply andb_true_iff in H as [Hneq Hmate].
    apply negb_true_iff, Nat.eqb_neq in Hneq. apply member_spec in Hmate. auto.
Qed.

Theorem checked_pairing_leaf_minimax : forall table st n,
  pairing_leafb table st = true -> valid_state st ->
  n + length (history st) = 125 -> solve prevents_white false n true st = true.
Proof.
  intros table st n H Hvalid Hlen.
  unfold pairing_leafb in H. apply andb_true_iff in H as [H Hcoverage].
  apply andb_true_iff in H as [Hmate Hresponse].
  apply pairing_safe_minimax with (mate := table_mate table); try assumption.
  - apply mate_tableb_sound. exact Hmate.
  - split; [apply responseb_sound|apply coverageb_sound]; assumption.
Qed.

Theorem checked_pairing_leaf_policy : forall table st n,
  pairing_leafb table st = true -> valid_state st ->
  n + length (history st) = 125 ->
  forall w, outcome (step_game n true st w (static_pairing_policy (table_mate table))) <> WhiteWins.
Proof.
  intros table st n H Hvalid Hlen w.
  unfold pairing_leafb in H. apply andb_true_iff in H as [H Hcoverage].
  apply andb_true_iff in H as [Hmate Hresponse].
  apply static_pairing_policy_nonloss; try assumption.
  - apply mate_tableb_sound. exact Hmate.
  - split; [apply responseb_sound|apply coverageb_sound]; assumption.
Qed.

Print Assumptions paired_white_move_cannot_win.
Print Assumptions reply_restores_pairing.
Print Assumptions pairing_safe_minimax.
Print Assumptions static_pairing_policy_nonloss.
Print Assumptions checked_pairing_leaf_minimax.
Print Assumptions checked_pairing_leaf_policy.
