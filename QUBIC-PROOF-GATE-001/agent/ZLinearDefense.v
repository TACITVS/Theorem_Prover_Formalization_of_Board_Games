(** A binary-code / matroid-exchange defense for the exact locked game.
    Two disjoint information sets replace a static pairing. *)
From Stdlib Require Import List Arith Bool Lia NArith.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Minimax RulesFacts SafePairing ZLinearAlgebra.
Import ListNotations.

Definition information (code : list N) (black reserve : list cell) : Prop :=
  forall word, In word code -> zero_on word black -> zero_on word reserve -> zero_board word.
Definition free_reserve (st : GameState) (reserve : list cell) : Prop :=
  forall c, In c reserve -> is_legal_move st c = true.
Definition disjoint_reserves (p q : list cell) : Prop := forall c, In c p -> ~ In c q.
Definition trim (x y : cell) (reserve : list cell) : list cell :=
  remove Nat.eq_dec y (remove Nat.eq_dec x reserve).

Definition code_coverage (code : list N) (st : GameState) : Prop :=
  forall l, In l all_lines ->
    (exists c, In c l /\ In c (black_stones st)) \/
    (exists word, In word code /\ nonzero_board word /\
      (forall c, c < 125 -> bit word c = true -> In c l)).

Record LinearSafe (code : list N) (st : GameState) (p q : list cell) : Prop := {
  reserve0_free : free_reserve st p;
  reserve1_free : free_reserve st q;
  reserves_disjoint : disjoint_reserves p q;
  reserve0_information : information code (black_stones st) p;
  reserve1_information : information code (black_stones st) q;
  winning_lines_coded : code_coverage code st
}.

Lemma legal_after_different_move : forall turn st request c,
  is_legal_move st c = true -> effective_move st request <> c ->
  is_legal_move (move_state turn st request) c = true.
Proof.
  intros turn st request c Hlegal Hneq.
  destruct (legal_move_fresh st c Hlegal) as [Hbound [HnotW HnotB]].
  unfold is_legal_move. apply andb_true_iff. split; [apply Nat.ltb_lt; exact Hbound|].
  apply negb_true_iff.
  destruct (occupied (move_state turn st request) c) eqn:Hocc; [|reflexivity].
  apply occupied_spec in Hocc. apply in_app_iff in Hocc as [Hw|Hb]; destruct turn.
  - change (In c (effective_move st request :: white_stones st)) in Hw. destruct Hw; congruence.
  - exfalso. apply HnotW. exact Hw.
  - exfalso. apply HnotB. exact Hb.
  - change (In c (effective_move st request :: black_stones st)) in Hb. destruct Hb; congruence.
Qed.

Lemma trim_in : forall x y reserve c,
  In c (trim x y reserve) -> In c reserve /\ c <> x /\ c <> y.
Proof.
  intros x y reserve c H. apply in_remove in H as [H Hny].
  apply in_remove in H as [H Hnx]. auto.
Qed.

Lemma reserve_free_after_round : forall st request y reserve,
  free_reserve st reserve -> is_legal_move (move_state true st request) y = true ->
  free_reserve (move_state false (move_state true st request) y)
    (trim (effective_move st request) y reserve).
Proof.
  intros st request y reserve Hfree Hy c Hc.
  apply trim_in in Hc as [Hc [Hnx Hny]].
  apply legal_after_different_move.
  - apply legal_after_different_move; [apply Hfree; exact Hc|congruence].
  - unfold effective_move at 1. rewrite Hy. congruence.
Qed.

Lemma code_coverage_monotone : forall code small large,
  incl (black_stones small) (black_stones large) ->
  code_coverage code small -> code_coverage code large.
Proof.
  intros code small large Hinc Hcover l Hl.
  destruct (Hcover l Hl) as [[c [Hcl Hcb]]|Hword].
  - left. exists c. split; [exact Hcl|apply Hinc; exact Hcb].
  - right. exact Hword.
Qed.

Lemma valid_black_cell_bound : forall st c,
  valid_state st -> In c (black_stones st) -> c < 125.
Proof.
  intros st c Hvalid Hin. pose proof (history_valid st Hvalid) as Hrange.
  rewrite Forall_forall in Hrange. apply Hrange.
  apply (valid_history_occupied st c Hvalid), occupied_spec, in_app_iff. auto.
Qed.

(** One information set untouched by White's move already prevents a win. *)
Lemma information_prevents_white_move : forall code st q request,
  valid_state st -> length (history st) < 125 -> free_reserve st q ->
  information code (black_stones st) q -> code_coverage code st ->
  ~ In (effective_move st request) q ->
  has_win (white_stones (move_state true st request)) = false.
Proof.
  intros code st q request Hvalid Hlen Hfree Hinfo Hcover Hnot.
  set (next := move_state true st request).
  assert (Hnext : valid_state next) by (apply move_preserves_validity; assumption).
  destruct (has_win (white_stones next)) eqn:Hwin; [|reflexivity]. exfalso.
  unfold has_win in Hwin. apply existsb_exists in Hwin as [l [Hl Hline]].
  assert (Hall : forall c, In c l -> In c (white_stones next)).
  { intros c Hc. unfold has_line in Hline.
    apply forallb_forall with (x := c) in Hline; [apply member_spec; exact Hline|exact Hc]. }
  destruct (Hcover l Hl) as [[c [Hc Hb]]|[word [Hword [Hnz Hsupport]]]].
  - apply (valid_colors_disjoint next c Hnext (Hall c Hc)). exact Hb.
  - assert (Hactive : zero_on word (black_stones st)).
    { intros c Hc. destruct (bit word c) eqn:Hbit; [|reflexivity].
      assert (Hbound : c < 125) by (eapply valid_black_cell_bound; eassumption).
      apply Hsupport in Hbit; [|exact Hbound].
      apply Hall in Hbit. exfalso. apply (valid_colors_disjoint next c Hnext Hbit). exact Hc. }
    assert (Hobserved : zero_on word q).
    { intros c Hc. pose proof (Hfree c Hc) as Hlegal.
      destruct (legal_move_fresh st c Hlegal) as [Hbound _].
      assert (Hnewlegal : is_legal_move next c = true).
      { apply legal_after_different_move; [exact Hlegal|]. intro H. subst c. contradiction. }
      destruct (legal_move_fresh next c Hnewlegal) as [_ [Hnotwhite _]].
      destruct (bit word c) eqn:Hbit; [|reflexivity]. exfalso.
      apply Hnotwhite, Hall, Hsupport; assumption. }
    pose proof (Hinfo word Hword Hactive Hobserved) as Hzero.
    destruct Hnz as [c [Hbound Htrue]]. specialize (Hzero c Hbound). congruence.
Qed.

Definition criticalb (black reserve : list cell) (x : cell) (word : N) : bool :=
  zero_onb word black && zero_onb word (remove Nat.eq_dec x reserve) && bit word x.

Lemma repair_without_critical : forall code black reserve x y,
  information code black reserve -> find (criticalb black reserve x) code = None ->
  information code (y :: black) (trim x y reserve).
Proof.
  intros code black reserve x y Hinfo Hnone word Hin Hactive Hzero.
  assert (Hy : bit word y = false) by (apply Hactive; left; reflexivity).
  assert (Hold : zero_on word black) by (intros c Hc; apply Hactive; right; exact Hc).
  assert (Hrest : zero_on word (remove Nat.eq_dec x reserve))
    by (apply zero_on_extend_removed with (removed := y); assumption).
  destruct (bit word x) eqn:Hx.
  - pose proof (@find_none N _ _ Hnone word Hin) as Hbad.
    assert (Hgood : criticalb black reserve x word = true).
    { unfold criticalb. apply andb_true_iff. split; [apply andb_true_iff; split; apply zero_onb_spec; assumption|exact Hx]. }
    congruence.
  - apply Hinfo; try assumption. apply zero_on_extend_removed with (removed := x); assumption.
Qed.

Lemma repair_with_critical : forall code black reserve x y critical,
  xor_closed code -> information code black reserve -> In critical code ->
  zero_on critical black -> zero_on critical (remove Nat.eq_dec x reserve) ->
  bit critical x = true -> bit critical y = true -> y < 125 ->
  information code (y :: black) (trim x y reserve).
Proof.
  intros code black reserve x y critical Hclosed Hinfo Hcritical Hactivec Hrestc Hcx Hcy Hy_bound.
  intros word Hin Hactive Hzero.
  assert (Hy : bit word y = false) by (apply Hactive; left; reflexivity).
  assert (Hold : zero_on word black) by (intros c Hc; apply Hactive; right; exact Hc).
  assert (Hrest : zero_on word (remove Nat.eq_dec x reserve))
    by (apply zero_on_extend_removed with (removed := y); assumption).
  destruct (bit word x) eqn:Hx.
  - assert (Hxor_in : In (N.lxor word critical) code) by (apply Hclosed; assumption).
    assert (Hxor_active : zero_on (N.lxor word critical) black) by (apply zero_on_xor; assumption).
    assert (Hxor_observed : zero_on (N.lxor word critical) reserve).
    { intros c Hc. rewrite bit_xor. destruct (Nat.eq_dec c x) as [->|Hneq].
      - rewrite Hx, Hcx. reflexivity.
      - rewrite Hrest, Hrestc by (apply in_in_remove; assumption). reflexivity. }
    pose proof (Hinfo _ Hxor_in Hxor_active Hxor_observed y Hy_bound) as Hbad.
    rewrite bit_xor, Hy, Hcy in Hbad. discriminate.
  - apply Hinfo; try assumption. apply zero_on_extend_removed with (removed := x); assumption.
Qed.

Lemma repair_untouched_information : forall code black reserve x y,
  information code black reserve -> ~ In x reserve ->
  information code (y :: black) (trim x y reserve).
Proof.
  intros code black reserve x y Hinfo Hnot word Hin Hactive Hzero.
  apply Hinfo; [exact Hin|intros c Hc; apply Hactive; right; exact Hc|].
  assert (Hy : bit word y = false) by (apply Hactive; left; reflexivity).
  assert (Hrest : zero_on word (remove Nat.eq_dec x reserve))
    by (apply zero_on_extend_removed with (removed := y); assumption).
  intros c Hc. apply Hrest, in_in_remove; [intro H; subst c; contradiction|exact Hc].
Qed.

Lemma information_response_exists : forall code st p q request,
  valid_state st -> length (history st) < 124 -> xor_closed code -> LinearSafe code st p q ->
  ~ In (effective_move st request) q ->
  exists y, is_legal_move (move_state true st request) y = true /\
    LinearSafe code (move_state false (move_state true st request) y)
      (trim (effective_move st request) y p) (trim (effective_move st request) y q).
Proof.
  intros code st p q request Hvalid Hspace Hclosed [Hpf Hqf Hdis Hip Hiq Hcover] Hnot.
  set (x := effective_move st request) in *.
  set (after_white := move_state true st request).
  assert (Hwvalid : valid_state after_white) by (apply move_preserves_validity; [exact Hvalid|lia]).
  assert (Hwspace : length (history after_white) < 125) by (unfold after_white; rewrite move_state_history; lia).
  pose proof (effective_move_is_legal st request Hvalid ltac:(lia)) as Hxlegal.
  destruct (legal_move_fresh st x Hxlegal) as [Hx_bound _].
  assert (Hchoice : exists y, is_legal_move after_white y = true /\
    information code (y :: black_stones st) (trim x y p)).
  { destruct (find (criticalb (black_stones st) p x) code) as [critical|] eqn:Hfind.
    - pose proof Hfind as Hfound. apply find_some in Hfound as [Hin Hcrit].
      unfold criticalb in Hcrit. apply andb_true_iff in Hcrit as [Hcrit Hcx].
      apply andb_true_iff in Hcrit as [Hactive Hrest].
      apply zero_onb_spec in Hactive, Hrest.
      destruct (find (bit critical) q) as [y|] eqn:Hyfind.
      + pose proof Hyfind as Hyfound. apply find_some in Hyfound as [Hyq Hcy].
        exists y. split.
        * apply legal_after_different_move; [apply Hqf; exact Hyq|]. intro Heq. subst y. contradiction.
        * apply repair_with_critical with (critical := critical); try assumption.
          destruct (legal_move_fresh st y (Hqf y Hyq)) as [Hybound _]. exact Hybound.
      + assert (Hzq : zero_on critical q).
        { intros c Hc. exact (@find_none cell _ _ Hyfind c Hc). }
        pose proof (Hiq critical Hin Hactive Hzq x Hx_bound). congruence.
    - exists (next_available_cell after_white). split; [apply fallback_is_legal; assumption|].
      apply repair_without_critical; assumption. }
  destruct Hchoice as [y [Hy Hrepair]]. exists y. split; [exact Hy|].
  assert (Heff : effective_move after_white y = y) by (unfold effective_move; rewrite Hy; reflexivity).
  assert (Hblack : black_stones (move_state false after_white y) = y :: black_stones st).
  { unfold move_state. rewrite Heff. reflexivity. }
  constructor.
  - apply reserve_free_after_round; assumption.
  - apply reserve_free_after_round; assumption.
  - intros c Hcp Hcq. apply trim_in in Hcp as [Hcp _]. apply trim_in in Hcq as [Hcq _].
    apply (Hdis c Hcp). exact Hcq.
  - rewrite Hblack. exact Hrepair.
  - rewrite Hblack. apply repair_untouched_information; assumption.
  - apply code_coverage_monotone with (small := st); [|exact Hcover].
    rewrite Hblack. intros c Hc. right. exact Hc.
Qed.

Lemma linear_safe_swap : forall code st p q,
  LinearSafe code st p q -> LinearSafe code st q p.
Proof.
  intros code st p q [Hpf Hqf Hdis Hip Hiq Hcover]. constructor; try assumption.
  intros c Hcq Hcp. apply (Hdis c Hcp). exact Hcq.
Qed.

Local Opaque solve.

(** General exchange theorem. The code is a finite XOR-closed family; the
    proof never enumerates it. Two independent information sets are maintained
    dynamically, and one remains untouched during every White move. *)
Theorem linear_information_minimax : forall n st code p q,
  n + length (history st) = 125 -> valid_state st -> xor_closed code ->
  LinearSafe code st p q -> solve prevents_white false n true st = true.
Proof.
  fix IH 1. intros n st code p q Hlen Hvalid Hclosed Hsafe.
  destruct n as [|n]; [rewrite pairing_solve_zero; reflexivity|].
  rewrite pairing_solve_successor. cbn [Bool.eqb]. apply forallb_forall.
  intros request Hin.
  assert (Horiented : exists p' q', LinearSafe code st p' q' /\ ~ In (effective_move st request) q').
  { destruct (in_dec Nat.eq_dec (effective_move st request) q) as [Hinq|Hnotq].
    - exists q, p. split; [apply linear_safe_swap; exact Hsafe|].
      destruct Hsafe as [_ _ Hdis _ _ _]. intro Hinp. apply (Hdis _ Hinp). exact Hinq.
    - exists p, q. auto. }
  destruct Horiented as [p' [q' [Hsafe' Hnot]]].
  pose proof Hsafe' as Hfields. destruct Hfields as [Hpf Hqf Hdis Hip Hiq Hcover].
  unfold branch. set (after_white := move_state true st request).
  assert (Hwhite_len : length (history after_white) = S (length (history st))) by (apply move_state_history).
  assert (Hwhite_valid : valid_state after_white) by (apply move_preserves_validity; [exact Hvalid|lia]).
  assert (Hwhite_nowin : has_win (white_stones after_white) = false).
  { apply information_prevents_white_move with (code := code) (q := q'); try assumption; lia. }
  unfold move_result at 1. rewrite Hwhite_nowin.
  destruct (length (history after_white) =? 125) eqn:Hfull; [reflexivity|].
  apply Nat.eqb_neq in Hfull. destruct n as [|n]; [exfalso; apply Hfull; lia|].
  change (solve prevents_white false (S n) false after_white = true).
  rewrite pairing_solve_successor. cbn [Bool.eqb].
  destruct (information_response_exists code st p' q' request Hvalid ltac:(lia) Hclosed Hsafe' Hnot)
    as [y [Hy Hnext]].
  apply existsb_exists. exists (canonical_request y). split; [apply canonical_request_in|].
  rewrite branch_canonical. unfold branch.
  set (after_black := move_state false after_white y).
  assert (Hblack_len : length (history after_black) = S (length (history after_white))) by (apply move_state_history).
  assert (Hblack_valid : valid_state after_black) by (apply move_preserves_validity; [exact Hwhite_valid|lia]).
  unfold move_result at 1.
  destruct (has_win (black_stones after_black)); [reflexivity|].
  destruct (length (history after_black) =? 125); [reflexivity|].
  apply (IH n after_black code (trim (effective_move st request) y p')
    (trim (effective_move st request) y q')); try assumption. lia.
Qed.

Fixpoint word_of_cells (cells : list cell) : N :=
  match cells with
  | [] => 0%N
  | c :: rest => N.setbit (word_of_cells rest) (N.of_nat c)
  end.

Lemma bit_word_of_cells : forall cells c,
  bit (word_of_cells cells) c = true <-> In c cells.
Proof.
  induction cells as [|a cells IH]; intros c.
  - rewrite bit_zero. cbn. split; [discriminate|contradiction].
  - unfold word_of_cells; fold word_of_cells. unfold bit at 1.
    rewrite N.setbit_iff. change ((N.of_nat a = N.of_nat c \/ bit (word_of_cells cells) c = true) <-> In c (a :: cells)).
    rewrite IH. cbn. split; intros [H|H]; auto.
    + left. apply Nat2N.inj. exact H.
Qed.

Definition free_line (st : GameState) (l : list cell) : list cell :=
  filter (fun c => negb (existsb (Nat.eqb c) (white_stones st))) l.
Definition residual_rows (st : GameState) : list N :=
  map (fun l => word_of_cells (free_line st l))
    (filter (fun l => negb (existsb (fun c => existsb (Nat.eqb c) (black_stones st)) l)) all_lines).

Lemma residual_code_covers_lines : forall st,
  has_win (white_stones st) = false -> code_coverage (code_words (residual_rows st)) st.
Proof.
  intros st Hquiet l Hl.
  destruct (existsb (fun c => existsb (Nat.eqb c) (black_stones st)) l) eqn:Hblocked.
  - apply existsb_exists in Hblocked as [c [Hcl Hcb]].
    left. exists c. split; [exact Hcl|apply member_spec; exact Hcb].
  - right. exists (word_of_cells (free_line st l)). split.
    + apply generator_in_code_words. unfold residual_rows.
      apply in_map_iff. exists l. split; [reflexivity|].
      apply filter_In. split; [exact Hl|apply negb_true_iff; exact Hblocked].
    + assert (Hnonempty : free_line st l <> []).
      { intro Hempty. assert (Hwin : has_win (white_stones st) = true).
        { unfold has_win. apply existsb_exists. exists l. split; [exact Hl|].
          unfold has_line. apply forallb_forall. intros c Hc.
          destruct (existsb (Nat.eqb c) (white_stones st)) eqn:Hmem; [reflexivity|].
          assert (Hfree : In c (free_line st l)).
          { apply filter_In. split; [exact Hc|rewrite Hmem; reflexivity]. }
          rewrite Hempty in Hfree. contradiction. }
        congruence. }
      split.
      * destruct (free_line st l) as [|c rest] eqn:Hfree; [contradiction|].
        exists c. assert (Hinc : In c (free_line st l)) by (rewrite Hfree; left; reflexivity).
        split.
        -- apply filter_In in Hinc as [Hcl _]. eapply locked_line_cell_bound; eassumption.
        -- apply bit_word_of_cells. left. reflexivity.
      * intros c Hc Hbit. apply bit_word_of_cells in Hbit. apply filter_In in Hbit. tauto.
Qed.

Definition linear_leafb (decoder0 decoder1 : Decoder) (st : GameState) : bool :=
  negb (has_win (white_stones st) || has_win (black_stones st)) &&
  forallb (is_legal_move st) (decoder_cells decoder0 ++ decoder_cells decoder1) &&
  forallb (fun c => negb (existsb (Nat.eqb c) (decoder_cells decoder1))) (decoder_cells decoder0) &&
  forallb (fun row => N.eqb (reconstruct decoder0 row) row &&
    N.eqb (reconstruct decoder1 row) row) (residual_rows st).

Theorem linear_leafb_sound : forall decoder0 decoder1 st,
  linear_leafb decoder0 decoder1 st = true ->
  LinearSafe (code_words (residual_rows st)) st (decoder_cells decoder0) (decoder_cells decoder1).
Proof.
  intros decoder0 decoder1 st H.
  unfold linear_leafb in H. rewrite !andb_true_iff in H.
  destruct H as [[[Hquiet Hfree] Hdis] Hrows].
  apply negb_true_iff, orb_false_iff in Hquiet as [Hw Hb].
  assert (Hd0 : forall row, In row (residual_rows st) -> reconstruct decoder0 row = row).
  { intros row Hr. apply forallb_forall with (x := row) in Hrows; [|exact Hr].
    apply andb_true_iff in Hrows as [Hrow _]. apply N.eqb_eq. exact Hrow. }
  assert (Hd1 : forall row, In row (residual_rows st) -> reconstruct decoder1 row = row).
  { intros row Hr. apply forallb_forall with (x := row) in Hrows; [|exact Hr].
    apply andb_true_iff in Hrows as [_ Hrow]. apply N.eqb_eq. exact Hrow. }
  constructor.
  - intros c Hc. apply forallb_forall with (x := c) in Hfree; [exact Hfree|apply in_app_iff; auto].
  - intros c Hc. apply forallb_forall with (x := c) in Hfree; [exact Hfree|apply in_app_iff; auto].
  - intros c Hc Hbad. apply forallb_forall with (x := c) in Hdis; [|exact Hc].
    apply negb_true_iff in Hdis. apply member_spec in Hbad. congruence.
  - intros word Hin Hactive Hzero. apply (decoder_detects _ _ Hd0 word Hin Hzero).
  - intros word Hin Hactive Hzero. apply (decoder_detects _ _ Hd1 word Hin Hzero).
  - apply residual_code_covers_lines. exact Hw.
Qed.

Theorem checked_linear_leaf_minimax : forall decoder0 decoder1 st n,
  linear_leafb decoder0 decoder1 st = true -> valid_state st ->
  n + length (history st) = 125 -> solve prevents_white false n true st = true.
Proof.
  intros decoder0 decoder1 st n Hcheck Hvalid Hlen.
  apply linear_information_minimax with (code := code_words (residual_rows st))
    (p := decoder_cells decoder0) (q := decoder_cells decoder1); try assumption.
  - apply code_words_closed.
  - apply linear_leafb_sound. exact Hcheck.
Qed.

Theorem checked_linear_leaf_total_defense : forall decoder0 decoder1 st n,
  linear_leafb decoder0 decoder1 st = true -> valid_state st -> n + length (history st) = 125 ->
  exists b : BlackStrategy, forall w : WhiteStrategy,
    outcome (step_game n true st w b) <> WhiteWins.
Proof.
  intros decoder0 decoder1 st n Hcheck Hvalid Hlen.
  pose proof (checked_linear_leaf_minimax decoder0 decoder1 st n Hcheck Hvalid Hlen) as Hsolve.
  exists (search_policy prevents_white false true). intros w.
  pose proof (solve_policy_sound prevents_white false true n true st w Hlen Hsolve) as Hsound.
  cbn [policies Bool.eqb] in Hsound.
  destruct (outcome (step_game n true st w (search_policy prevents_white false true)));
    cbn in Hsound; congruence.
Qed.

Print Assumptions information_response_exists.
Print Assumptions linear_information_minimax.
Print Assumptions linear_leafb_sound.
Print Assumptions checked_linear_leaf_total_defense.
