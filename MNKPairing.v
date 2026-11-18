(** **************************************************************************
    MNKPairing.v: Pairing Strategies and the Draws of (m, n, 3) with
    min(m, n) <= 2

    - A generic pairing-strategy theorem: if the cells can be paired so that
      every winning line contains a complete pair, then whoever moves can
      never force a win, because the opponent always answers in the partner
      cell ([pairing_no_forced_win]); hence the game is a draw
      ([pairing_draw]).
    - Domino pairings (r, 2j) <-> (r, 2j+1) and (2i, c) <-> (2i+1, c).
      On boards with at most 2 rows (resp. 2 columns) every 3-line is
      horizontal (resp. vertical) and contains a domino, so these games are
      draws ([mnk_two_rows_draw], [mnk_two_cols_draw]).
      NOTE: such boards DO have 3-in-a-row lines when the other side is >= 3;
      the draw comes from the pairing strategy, not from an absence of lines.

    Zero axioms, zero admissions (closed under the global context).
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool PeanoNat.
Import ListNotations.
Require Import MNK.MNKBoard.
Require Import MNK.MNKGame.

Section Pairing.

Variable lines : list (list nat).
Variable partner : nat -> nat.
Variable N : nat.
Hypothesis partner_invol : forall x, x < N -> partner (partner x) = x.
Hypothesis partner_range : forall x, x < N -> partner x < N.
Hypothesis line_has_pair : forall L, In L lines ->
  exists x, In x L /\ In (partner x) L /\ partner x <> x.

(** Every paired stone of the attacker [p] has its partner taken by the opponent. *)
Definition pair_inv (p : player) (b : board_t) : Prop :=
  length b = N /\
  forall x, get_cell b x = Some p -> partner x <> x ->
    get_cell b (partner x) = Some (other_player p).

Lemma owned_lt : forall b x p, length b = N -> get_cell b x = Some p -> x < N.
Proof.
  intros b x p Hl H. destruct (lt_dec x N) as [Hx | Hx]; [exact Hx |].
  unfold get_cell in H. rewrite nth_overflow in H by lia. discriminate.
Qed.

Lemma other_neq : forall p, other_player p <> p.
Proof. destruct p; discriminate. Qed.

Theorem pairing_no_forced_win : forall p d b,
  pair_inv p b -> ~ forces_win lines p d b.
Proof.
  intros p d b Hinv H. revert Hinv.
  induction H as [d b m Hm Hw | d b m Hm Hex Hno Hfw IH]; intros [Hlen Hinv].
  - (* Player p completes a line: impossible, the line contains a pair *)
    apply check_win_iff in Hw as [L [HL Hown]].
    destruct (line_has_pair L HL) as [x [Hx [Hpx Hneq]]].
    pose proof (Hown x Hx) as Ox. pose proof (Hown (partner x) Hpx) as Opx.
    pose proof (legal_move_empty b m Hm) as Em.
    destruct (Nat.eq_dec m x) as [<- | Hmx].
    + assert (HmN : m < N) by (rewrite <- Hlen; apply legal_move_lt; exact Hm).
      rewrite get_set_cell_other in Opx by congruence.
      assert (Hpp : partner (partner m) = m) by (apply partner_invol; exact HmN).
      assert (Hne2 : partner (partner m) <> partner m) by (rewrite Hpp; congruence).
      pose proof (Hinv (partner m) Opx Hne2) as Hc. rewrite Hpp in Hc. congruence.
    + rewrite get_set_cell_other in Ox by congruence.
      specialize (Hinv x Ox Hneq).
      destruct (Nat.eq_dec m (partner x)) as [Hmp | Hmp].
      * rewrite <- Hmp in Hinv. congruence.
      * rewrite get_set_cell_other in Opx by exact Hmp.
        rewrite Hinv in Opx. inversion Opx. apply (other_neq p). auto.
  - (* the opponent answers in the partner cell (or anywhere if none) *)
    set (b1 := set_cell b m p) in *.
    pose proof (legal_move_empty b m Hm) as Em.
    pose proof (legal_move_lt b m Hm) as Hmlt.
    assert (Hlen1 : length b1 = N) by (unfold b1; rewrite set_cell_length; exact Hlen).
    assert (Hb1m : get_cell b1 m = Some p) by (unfold b1; apply get_set_cell_same; lia).
    (* choose the reply *)
    assert (Hchoice : exists c, is_legal_move b1 c = true /\
      (partner m <> m -> get_cell (set_cell b1 c (other_player p)) (partner m) =
                         Some (other_player p))).
    { destruct (Nat.eq_dec (partner m) m) as [Hpm | Hpm].
      - destruct Hex as [c Hc]. exists c. split; [exact Hc | intros; contradiction].
      - destruct (get_cell b1 (partner m)) as [q |] eqn:Eq.
        + destruct Hex as [c Hc]. exists c. split; [exact Hc |]. intros _.
          assert (Hcpm : c <> partner m).
          { intros ->. apply legal_move_empty in Hc. congruence. }
          rewrite get_set_cell_other by congruence. rewrite Eq.
          unfold b1 in Eq. rewrite get_set_cell_other in Eq by congruence.
          destruct (player_eqb q p) eqn:Eqp.
          * apply player_eqb_eq in Eqp. subst q.
            assert (HmN : m < N) by lia.
            assert (Hpp : partner (partner m) = m) by (apply partner_invol; exact HmN).
            assert (Hne2 : partner (partner m) <> partner m) by (rewrite Hpp; congruence).
            pose proof (Hinv (partner m) Eq Hne2) as Hc'. rewrite Hpp in Hc'. congruence.
          * destruct p, q; simpl in Eqp; try discriminate; reflexivity.
        + exists (partner m). split.
          * apply legal_move_intro; [rewrite Hlen1; apply partner_range; lia | exact Eq].
          * intros _. apply get_set_cell_same. rewrite Hlen1. apply partner_range. lia. }
    destruct Hchoice as [c [Hc Hcm]].
    apply (IH c Hc). split; [rewrite set_cell_length; exact Hlen1 |].
    intros x Ox Hneq.
    assert (Hxc : x <> c).
    { intros ->. rewrite get_set_cell_same in Ox by (apply legal_move_lt; exact Hc).
      inversion Ox. apply (other_neq p). auto. }
    rewrite get_set_cell_other in Ox by congruence.
    destruct (Nat.eq_dec x m) as [-> | Hxm]; [apply Hcm; exact Hneq |].
    unfold b1 in Ox. rewrite get_set_cell_other in Ox by congruence.
    pose proof (Hinv x Ox Hneq) as Hp.
    assert (Hpm : partner x <> m) by (intros E; rewrite E in Hp; congruence).
    assert (Hpb1 : get_cell b1 (partner x) = Some (other_player p))
      by (unfold b1; rewrite get_set_cell_other by congruence; exact Hp).
    assert (Hpc : partner x <> c) by (intros E; apply legal_move_empty in Hc; congruence).
    rewrite get_set_cell_other by congruence. exact Hpb1.
Qed.

(** A pairing strategy makes the game a draw. *)
Theorem pairing_draw : game_is_draw lines (empty_board N).
Proof.
  split.
  - intros d. apply pairing_no_forced_win. split; [apply empty_board_length |].
    intros x H. rewrite get_cell_empty_board in H. discriminate.
  - intros d [[m Hm] H]. destruct (H m Hm) as [_ Hw].
    revert Hw. apply pairing_no_forced_win.
    split; [rewrite set_cell_length; apply empty_board_length |].
    intros x Hx. destruct (Nat.eq_dec m x) as [-> | Hmx].
    + rewrite get_set_cell_same in Hx by (apply legal_move_lt; exact Hm). discriminate.
    + rewrite get_set_cell_other in Hx by exact Hmx.
      rewrite get_cell_empty_board in Hx. discriminate.
Qed.

End Pairing.

(* ========================================================================= *)
(** * Domino pairings for boards with at most two rows / two columns          *)
(* ========================================================================= *)

Definition partner_row (n x : nat) : nat :=
  if Nat.even (x mod n) then (if x mod n + 1 <? n then x + 1 else x) else x - 1.

Definition partner_col (m n x : nat) : nat :=
  if Nat.even (x / n) then (if x / n + 1 <? m then x + n else x) else x - n.

Lemma decompose : forall n x, 0 < n -> x = (x / n) * n + x mod n /\ x mod n < n.
Proof.
  intros n x Hn. split; [rewrite (Nat.div_mod_eq x n) at 1; lia |].
  apply Nat.mod_upper_bound. lia.
Qed.

Lemma partner_row_spec : forall n r c, c < n ->
  partner_row n (r * n + c) =
    if Nat.even c then (if c + 1 <? n then r * n + c + 1 else r * n + c)
    else r * n + c - 1.
Proof.
  intros n r c Hc. unfold partner_row. rewrite idx_mod by exact Hc. reflexivity.
Qed.

Lemma partner_col_spec : forall m n r c, c < n ->
  partner_col m n (r * n + c) =
    if Nat.even r then (if r + 1 <? m then r * n + c + n else r * n + c)
    else r * n + c - n.
Proof.
  intros m n r c Hc. unfold partner_col. rewrite idx_div by exact Hc. reflexivity.
Qed.

Lemma even_or_odd : forall c, Nat.even c = true \/ (Nat.even c = false /\ 1 <= c).
Proof.
  intros [| c]; [left; reflexivity |].
  destruct (Nat.even (S c)); [left | right]; auto with arith.
Qed.

Theorem mnk_two_rows_draw : forall m n, m <= 2 ->
  game_is_draw (gen_lines m n 3) (empty_board (m * n)).
Proof.
  intros m n Hm.
  apply (pairing_draw (gen_lines m n 3) (partner_row n) (m * n)).
  - (* involution *)
    intros x Hx. assert (Hn : 0 < n) by (destruct n; lia).
    destruct (decompose n x Hn) as [Ex Hc].
    set (r := x / n) in *. set (c := x mod n) in *. rewrite Ex.
    rewrite partner_row_spec by exact Hc.
    destruct (Nat.even c) eqn:Ec.
    + destruct (c + 1 <? n) eqn:Ecn; [| rewrite partner_row_spec, Ec, Ecn by exact Hc; reflexivity].
      apply Nat.ltb_lt in Ecn.
      replace (r * n + c + 1) with (r * n + (c + 1)) by lia.
      rewrite partner_row_spec by exact Ecn.
      rewrite Nat.add_1_r, Nat.even_succ, <- Nat.negb_even, Ec. simpl. lia.
    + assert (H1 : 1 <= c) by (destruct c; [discriminate | lia]).
      replace (r * n + c - 1) with (r * n + (c - 1)) by lia.
      rewrite partner_row_spec by lia.
      replace c with (S (c - 1)) in Ec by lia.
      rewrite Nat.even_succ, <- Nat.negb_even in Ec.
      apply negb_false_iff in Ec. rewrite Ec.
      replace (c - 1 + 1 <? n) with true by (symmetry; apply Nat.ltb_lt; lia). lia.
  - (* range *)
    intros x Hx. assert (Hn : 0 < n) by (destruct n; lia).
    destruct (decompose n x Hn) as [Ex Hc].
    unfold partner_row. destruct (Nat.even (x mod n)); [| lia].
    destruct (x mod n + 1 <? n) eqn:E; [| lia]. apply Nat.ltb_lt in E.
    assert (x / n < m) by (apply Nat.Div0.div_lt_upper_bound; lia). nia.
  - (* every line contains a horizontal domino *)
    intros L HL. apply in_gen_lines in HL as (d & r & c & Hf & ->).
    destruct d; simpl in Hf; try lia.
    destruct Hf as [Hr Hc].
    unfold mkline. simpl.
    destruct (even_or_odd c) as [Ec | [Ec Hc1]].
    + assert (Hpx : partner_row n (r * n + c) = r * n + c + 1).
      { rewrite partner_row_spec by lia. rewrite Ec.
        replace (c + 1 <? n) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
      exists (r * n + c). rewrite Hpx.
      repeat split; [left; lia | right; left; lia | lia].
    + assert (Hpx : partner_row n (r * n + (c + 1)) = r * n + (c + 1) + 1).
      { rewrite partner_row_spec by lia.
        replace (Nat.even (c + 1)) with true
          by (rewrite Nat.add_1_r, Nat.even_succ, <- Nat.negb_even, Ec; reflexivity).
        replace (c + 1 + 1 <? n) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
      exists (r * n + (c + 1)). rewrite Hpx.
      repeat split; [right; left; lia | right; right; left; lia | lia].
Qed.

Theorem mnk_two_cols_draw : forall m n, n <= 2 ->
  game_is_draw (gen_lines m n 3) (empty_board (m * n)).
Proof.
  intros m n Hn2.
  apply (pairing_draw (gen_lines m n 3) (partner_col m n) (m * n)).
  - (* involution *)
    intros x Hx. assert (Hn : 0 < n) by (destruct n; lia).
    destruct (decompose n x Hn) as [Ex Hc].
    assert (Hr : x / n < m) by (apply Nat.Div0.div_lt_upper_bound; lia).
    set (r := x / n) in *. set (c := x mod n) in *. rewrite Ex.
    rewrite partner_col_spec by exact Hc.
    destruct (Nat.even r) eqn:Er.
    + destruct (r + 1 <? m) eqn:Erm; [| rewrite partner_col_spec, Er, Erm by exact Hc; reflexivity].
      apply Nat.ltb_lt in Erm.
      replace (r * n + c + n) with ((r + 1) * n + c) by lia.
      rewrite partner_col_spec by exact Hc.
      rewrite Nat.add_1_r, Nat.even_succ, <- Nat.negb_even, Er. simpl. lia.
    + assert (H1 : 1 <= r) by (destruct r; [discriminate | lia]).
      replace (r * n + c - n) with ((r - 1) * n + c) by nia.
      rewrite partner_col_spec by exact Hc.
      replace r with (S (r - 1)) in Er by lia.
      rewrite Nat.even_succ, <- Nat.negb_even in Er.
      apply negb_false_iff in Er. rewrite Er.
      replace (r - 1 + 1 <? m) with true by (symmetry; apply Nat.ltb_lt; lia). nia.
  - (* range *)
    intros x Hx. assert (Hn : 0 < n) by (destruct n; lia).
    destruct (decompose n x Hn) as [Ex Hc].
    unfold partner_col. destruct (Nat.even (x / n)); [| lia].
    destruct (x / n + 1 <? m) eqn:E; [| lia]. apply Nat.ltb_lt in E. nia.
  - (* every line contains a vertical domino *)
    intros L HL. apply in_gen_lines in HL as (d & r & c & Hf & ->).
    destruct d; simpl in Hf; try lia.
    destruct Hf as [Hr Hc].
    unfold mkline. simpl.
    destruct (even_or_odd r) as [Er | [Er Hr1]].
    + assert (Hpx : partner_col m n (r * n + c) = r * n + c + n).
      { rewrite partner_col_spec by lia. rewrite Er.
        replace (r + 1 <? m) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
      exists (r * n + c). rewrite Hpx.
      repeat split; [left; nia | right; left; nia | nia].
    + assert (Hpx : partner_col m n ((r + 1) * n + c) = (r + 1) * n + c + n).
      { rewrite partner_col_spec by lia.
        replace (Nat.even (r + 1)) with true
          by (rewrite Nat.add_1_r, Nat.even_succ, <- Nat.negb_even, Er; reflexivity).
        replace (r + 1 + 1 <? m) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
      exists ((r + 1) * n + c). rewrite Hpx.
      repeat split; [right; left; nia | right; right; left; nia | nia].
Qed.
