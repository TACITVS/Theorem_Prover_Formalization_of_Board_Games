(** * MNKMakerBreaker.v: From Maker-Breaker Strategies to Game Values

    Three general facts, valid for every board and every family of winning
    lines, that turn a Breaker strategy into game-theoretic values.

    1. [breaker_win_draw]: if Maker (= Player 1) cannot win the Maker-Breaker
       game from the empty board, the strong game is a draw.  Player 2 stops
       Player 1 with the Breaker strategy (a forced win in the strong game is
       in particular a Maker win), and strategy stealing stops Player 2.

    2. [maker_wins_refine]: Maker-Breaker wins are monotone in the family of
       lines.  If every line of [lines'] contains a line of [lines], a Maker
       win for [lines'] is a Maker win for [lines].  Every k'-in-a-row contains
       a k-in-a-row when k <= k' ([mnk_lines_refine]), so a Breaker win for
       k-in-a-row is a Breaker win for every longer line length
       ([mnk_breaker_win_longer_lines]), and all those strong games are draws
       ([mnk_draw_longer_lines]).

    3. [pairing_no_maker_win]: the pairing strategy in the middle of a game.
       If Breaker has answered every paired Maker stone with its partner, and
       every line either carries a Breaker stone or contains a whole pair,
       Maker cannot win.  Unlike [pairing_no_forced_win] (MNKPairing.v), lines
       Breaker has already blocked need no pair, so the rule applies at any
       position reached in play: it is the pairing leaf of draw certificates.

    Zero axioms, zero admits. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From MNK Require Import MNKBoard MNKGame MNKErdosSelfridge MNKStrategyStealing.

Lemma mb_other_neq : forall p, other_player p <> p.
Proof. destruct p; discriminate. Qed.

(* ========================================================================= *)
(** * 1. A Breaker win is a draw of the strong game                         *)
(* ========================================================================= *)

Theorem breaker_win_draw : forall lines N,
  (forall d, ~ maker_wins lines P1 d (empty_board N)) ->
  game_is_draw lines (empty_board N).
Proof.
  intros lines N Hbreaker. split.
  - intros d Hwin. apply (Hbreaker d). apply forces_win_maker_wins. exact Hwin.
  - intros d. apply strategy_stealing.
Qed.

Corollary mnk_breaker_win_draw : forall m n k,
  (forall d, ~ maker_wins (gen_lines m n k) P1 d (empty_board (m * n))) ->
  game_is_draw (gen_lines m n k) (empty_board (m * n)).
Proof. intros m n k. apply breaker_win_draw. Qed.

(* ========================================================================= *)
(** * 2. Maker-Breaker wins are monotone in the family of lines             *)
(* ========================================================================= *)

(** [refines lines lines']: every line of [lines'] contains a line of [lines]. *)
Definition refines (lines lines' : list (list nat)) : Prop :=
  forall L', In L' lines' -> exists L, In L lines /\ incl L L'.

Lemma check_win_refine : forall lines lines' b p,
  refines lines lines' ->
  check_win b p lines' = true -> check_win b p lines = true.
Proof.
  intros lines lines' b p Href Hwin.
  apply check_win_iff in Hwin as [L' [HL' Hown]].
  destruct (Href L' HL') as [L [HL Hincl]].
  apply check_win_iff. exists L. split; [exact HL |].
  intros x Hx. apply Hown. apply Hincl. exact Hx.
Qed.

(** Maker follows the same strategy: each line it completes for [lines']
    contains a line of [lines], completed at the same moment or earlier. *)
Theorem maker_wins_refine : forall lines lines' p d b,
  refines lines lines' ->
  maker_wins lines' p d b -> maker_wins lines p d b.
Proof.
  intros lines lines' p d b Href H.
  induction H as [d b m Hm Hwin | d b m Hm Hex Hnext IH].
  - apply (mw_now lines p d b m Hm). apply (check_win_refine lines lines'); assumption.
  - apply (mw_next lines p d b m Hm Hex). exact IH.
Qed.

(** Every k'-in-a-row of the m x n board contains a k-in-a-row, for k <= k'.
    Horizontal, vertical and diagonal lines contain the k-line with the same
    start; the anti-diagonal one (drawn from bottom-left to top-right inside
    its bounding box) contains the k-line whose box starts k' - k rows lower. *)
Lemma mnk_lines_refine : forall m n k k', k <= k' ->
  refines (gen_lines m n k) (gen_lines m n k').
Proof.
  intros m n k k' Hk L' HL'.
  apply in_gen_lines in HL' as (d & r & c & Hfit & ->).
  set (r0 := match d with DA => r + (k' - k) | _ => r end).
  exists (mkline n k d r0 c). split.
  - apply in_gen_lines. exists d, r0, c. split; [| reflexivity].
    unfold r0. destruct d; simpl in *; lia.
  - intros x Hx. apply in_mkline in Hx as [i [Hi ->]].
    apply in_mkline. exists i. split; [lia |].
    unfold r0. destruct d; simpl; try reflexivity.
    replace (r + (k' - k) + (k - 1 - i)) with (r + (k' - 1 - i)) by lia.
    reflexivity.
Qed.

Theorem mnk_maker_wins_shorter_lines : forall m n k k' p d b, k <= k' ->
  maker_wins (gen_lines m n k') p d b -> maker_wins (gen_lines m n k) p d b.
Proof.
  intros m n k k' p d b Hk. apply maker_wins_refine. apply mnk_lines_refine. exact Hk.
Qed.

(** A Breaker win for k-in-a-row is a Breaker win for every longer line. *)
Corollary mnk_breaker_win_longer_lines : forall m n k k', k <= k' ->
  (forall d, ~ maker_wins (gen_lines m n k) P1 d (empty_board (m * n))) ->
  forall d, ~ maker_wins (gen_lines m n k') P1 d (empty_board (m * n)).
Proof.
  intros m n k k' Hk Hbreaker d Hwin.
  apply (Hbreaker d). apply (mnk_maker_wins_shorter_lines m n k k'); assumption.
Qed.

(** ... and then every one of those strong games is a draw. *)
Corollary mnk_draw_longer_lines : forall m n k k', k <= k' ->
  (forall d, ~ maker_wins (gen_lines m n k) P1 d (empty_board (m * n))) ->
  game_is_draw (gen_lines m n k') (empty_board (m * n)).
Proof.
  intros m n k k' Hk Hbreaker. apply mnk_breaker_win_draw.
  apply (mnk_breaker_win_longer_lines m n k k'); assumption.
Qed.

(* ========================================================================= *)
(** * 3. The pairing strategy in the middle of a Maker-Breaker game         *)
(* ========================================================================= *)

Section MidGamePairing.

Variable lines : list (list nat).
Variable partner : nat -> nat.   (* partner x = x: x is unpaired *)
Variable N : nat.
Hypothesis partner_invol : forall x, x < N -> partner (partner x) = x.
Hypothesis partner_range : forall x, x < N -> partner x < N.

(** Breaker ([other_player p]) has answered every paired stone of Maker [p]. *)
Definition answered (p : player) (b : board_t) : Prop :=
  length b = N /\
  forall x, get_cell b x = Some p -> partner x <> x ->
    get_cell b (partner x) = Some (other_player p).

(** A line is harmless when Breaker already has a stone on it, or when it
    contains a whole pair. *)
Definition harmless (p : player) (b : board_t) (L : list nat) : Prop :=
  (exists y, In y L /\ get_cell b y = Some (other_player p)) \/
  (exists x, In x L /\ In (partner x) L /\ partner x <> x).

(** One Maker move and one Breaker reply keep a line harmless: Breaker's
    stones stay where they are, and pairs do not depend on the board. *)
Lemma harmless_after_moves : forall p b m c L,
  is_legal_move b m = true ->
  is_legal_move (set_cell b m p) c = true ->
  harmless p b L -> harmless p (set_cell (set_cell b m p) c (other_player p)) L.
Proof.
  intros p b m c L Hm Hc [[y [Hy Hby]] | Hpair]; [left | right; exact Hpair].
  exists y. split; [exact Hy |].
  assert (Hym : y <> m) by (intros ->; apply legal_move_empty in Hm; congruence).
  assert (Hyc : y <> c).
  { intros ->. apply legal_move_empty in Hc.
    rewrite get_set_cell_other in Hc by congruence. congruence. }
  rewrite get_set_cell_other by congruence.
  rewrite get_set_cell_other by congruence.
  exact Hby.
Qed.

(** Breaker answers each Maker move in its partner cell (anywhere if the
    partner is unpaired or already taken).  A line Maker completes would have
    no Breaker stone, hence a whole pair, so Maker would own both cells of a
    pair: impossible, since Breaker always takes the second one. *)
Theorem pairing_no_maker_win : forall p d b,
  answered p b ->
  (forall L, In L lines -> harmless p b L) ->
  ~ maker_wins lines p d b.
Proof.
  intros p d b Hanswered Hharmless H. revert Hanswered Hharmless.
  induction H as [d b m Hm Hw | d b m Hm Hex Hnext IH]; intros [Hlen Hinv] Hharmless.
  - (* Maker completes a line L with the move m *)
    apply check_win_iff in Hw as [L [HL Hown]].
    pose proof (legal_move_empty b m Hm) as Em.
    destruct (Hharmless L HL) as [[y [Hy Hby]] | [x [Hx [Hpx Hneq]]]].
    + (* L carries a Breaker stone, which Maker cannot own *)
      pose proof (Hown y Hy) as Oy.
      assert (Hym : m <> y) by (intros ->; congruence).
      rewrite get_set_cell_other in Oy by exact Hym.
      rewrite Hby in Oy. inversion Oy as [Hop]. exact (mb_other_neq p Hop).
    + (* L contains the pair {x, partner x}: Maker cannot own both cells *)
      pose proof (Hown x Hx) as Ox. pose proof (Hown (partner x) Hpx) as Opx.
      destruct (Nat.eq_dec m x) as [<- | Hmx].
      * assert (HmN : m < N) by (rewrite <- Hlen; apply legal_move_lt; exact Hm).
        rewrite get_set_cell_other in Opx by congruence.
        assert (Hpp : partner (partner m) = m) by (apply partner_invol; exact HmN).
        assert (Hne2 : partner (partner m) <> partner m) by (rewrite Hpp; congruence).
        pose proof (Hinv (partner m) Opx Hne2) as Hc. rewrite Hpp in Hc. congruence.
      * rewrite get_set_cell_other in Ox by congruence.
        specialize (Hinv x Ox Hneq).
        destruct (Nat.eq_dec m (partner x)) as [Hmp | Hmp].
        -- rewrite <- Hmp in Hinv. congruence.
        -- rewrite get_set_cell_other in Opx by exact Hmp.
           rewrite Hinv in Opx. inversion Opx as [Hop]. exact (mb_other_neq p Hop).
  - (* Maker plays m and Breaker answers in the partner cell, or anywhere *)
    set (b1 := set_cell b m p) in *.
    pose proof (legal_move_empty b m Hm) as Em.
    pose proof (legal_move_lt b m Hm) as Hmlt.
    assert (Hlen1 : length b1 = N) by (unfold b1; rewrite set_cell_length; exact Hlen).
    assert (Hb1m : get_cell b1 m = Some p) by (unfold b1; apply get_set_cell_same; lia).
    assert (Hchoice : exists c, is_legal_move b1 c = true /\
      (partner m <> m -> get_cell (set_cell b1 c (other_player p)) (partner m) =
                         Some (other_player p))).
    { destruct (Nat.eq_dec (partner m) m) as [Hpm | Hpm].
      - destruct Hex as [c Hc]. exists c. split; [exact Hc | intros; contradiction].
      - destruct (get_cell b1 (partner m)) as [q |] eqn:Eq.
        + (* the partner is taken already; it cannot be Maker's *)
          destruct Hex as [c Hc]. exists c. split; [exact Hc |]. intros _.
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
    apply (IH c Hc).
    + split; [rewrite set_cell_length; exact Hlen1 |].
      intros x Ox Hneq.
      assert (Hxc : x <> c).
      { intros ->. rewrite get_set_cell_same in Ox by (apply legal_move_lt; exact Hc).
        inversion Ox as [Hop]. exact (mb_other_neq p Hop). }
      rewrite get_set_cell_other in Ox by congruence.
      destruct (Nat.eq_dec x m) as [-> | Hxm]; [apply Hcm; exact Hneq |].
      unfold b1 in Ox. rewrite get_set_cell_other in Ox by congruence.
      pose proof (Hinv x Ox Hneq) as Hp.
      assert (Hpm : partner x <> m) by (intros E; rewrite E in Hp; congruence).
      assert (Hpb1 : get_cell b1 (partner x) = Some (other_player p))
        by (unfold b1; rewrite get_set_cell_other by congruence; exact Hp).
      assert (Hpc : partner x <> c) by (intros E; apply legal_move_empty in Hc; congruence).
      rewrite get_set_cell_other by congruence. exact Hpb1.
    + intros L HL. apply harmless_after_moves; [exact Hm | exact Hc |].
      apply Hharmless. exact HL.
Qed.

(** On the empty board: if every line contains a whole pair, Maker never wins,
    whoever moves first. *)
Corollary pairing_no_maker_win_empty : forall p d,
  (forall L, In L lines -> exists x, In x L /\ In (partner x) L /\ partner x <> x) ->
  ~ maker_wins lines p d (empty_board N).
Proof.
  intros p d Hpairs. apply pairing_no_maker_win.
  - split; [apply empty_board_length |].
    intros x Hx. rewrite get_cell_empty_board in Hx. discriminate.
  - intros L HL. right. apply Hpairs. exact HL.
Qed.

End MidGamePairing.
