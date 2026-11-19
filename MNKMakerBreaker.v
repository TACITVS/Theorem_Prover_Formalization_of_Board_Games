(** * MNKMakerBreaker.v: From Maker-Breaker Strategies to Game Values

    General facts, valid for every board and every family of winning lines,
    that turn a Breaker strategy into game-theoretic values.

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

    4. [maker_wins_simulate]: Maker wins transfer along any injective map of
       the cells that sends lines onto lines.  The m' x n' board embeds in the
       m x n board when m' <= m and n' <= n ([mnk_maker_wins_subboard]), and
       every board embeds in its transpose ([mnk_maker_wins_transpose]).  So a
       single Breaker win for (m, n, k) makes every (m', n', k') with the
       board fitting inside m x n, either way round, and k' >= k a draw
       ([mnk_breaker_win_family]).

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

(* ========================================================================= *)
(** * 4. Embeddings: Maker wins transfer to larger boards                   *)
(* ========================================================================= *)

Lemma player_cases : forall p q, q = p \/ q = other_player p.
Proof. destruct p, q; auto. Qed.

(** A bounded search, decided without excluded middle. *)
Lemma bounded_exists_dec : forall (f : nat -> bool) N,
  (exists x, x < N /\ f x = true) \/ (forall x, x < N -> f x = false).
Proof.
  intros f N. induction N as [| N [[x [Hx Hf]] | Hall]].
  - right. intros x Hx. lia.
  - left. exists x. split; [lia | exact Hf].
  - destruct (f N) eqn:E.
    + left. exists N. split; [lia | exact E].
    + right. intros x Hx. destruct (Nat.eq_dec x N) as [-> | Hne]; [exact E |].
      apply Hall. lia.
Qed.

(** An injective map [e] from the cells of a small board into a big board
    such that every small line contains the preimage of a big line.  Maker
    plays the small-board strategy through [e].  A Breaker reply on the image
    of a free cell is copied into the imagined small game; any other reply is
    answered there by an imagined Breaker stone on some free cell, which only
    makes the imagined game harder for Maker. *)
Section Embedding.

Variables small_lines big_lines : list (list nat).
Variables Ns Nb : nat.
Variable e : nat -> nat.
Hypothesis e_range : forall x, x < Ns -> e x < Nb.
Hypothesis e_inj : forall x y, x < Ns -> y < Ns -> e x = e y -> x = y.
Hypothesis small_range : forall L x, In L small_lines -> In x L -> x < Ns.
Hypothesis lines_embed : forall L, In L small_lines ->
  exists L', In L' big_lines /\ forall y, In y L' -> exists x, In x L /\ y = e x.
Variable p : player.

(** The real board [bb] simulates the imagined board [bs]: the same Maker
    stones on the embedded cells, and every real Breaker stone on an embedded
    cell is an imagined one (the imagined board may have more). *)
Definition simulates (bs bb : board_t) : Prop :=
  length bs = Ns /\ length bb = Nb /\
  forall x, x < Ns ->
    (get_cell bs x = Some p <-> get_cell bb (e x) = Some p) /\
    (get_cell bb (e x) = Some (other_player p) -> get_cell bs x = Some (other_player p)).

Lemma simulates_empty : simulates (empty_board Ns) (empty_board Nb).
Proof.
  split; [apply empty_board_length |]. split; [apply empty_board_length |].
  intros x _. rewrite !get_cell_empty_board. split; [split |]; discriminate.
Qed.

Lemma simulates_legal : forall bs bb m,
  simulates bs bb -> is_legal_move bs m = true -> is_legal_move bb (e m) = true.
Proof.
  intros bs bb m [Hls [Hlb Hsim]] Hm.
  pose proof (legal_move_lt bs m Hm) as Hlt. rewrite Hls in Hlt.
  pose proof (legal_move_empty bs m Hm) as Em.
  apply legal_move_intro; [rewrite Hlb; apply e_range; exact Hlt |].
  destruct (get_cell bb (e m)) as [q |] eqn:Eq; [| reflexivity].
  exfalso. destruct (Hsim m Hlt) as [Hp Ho].
  destruct (player_cases p q) as [-> | ->].
  - apply Hp in Eq. congruence.
  - apply Ho in Eq. congruence.
Qed.

Lemma simulates_win : forall bs bb,
  simulates bs bb -> check_win bs p small_lines = true -> check_win bb p big_lines = true.
Proof.
  intros bs bb [_ [_ Hsim]] Hw.
  apply check_win_iff in Hw as [L [HL Hown]].
  destruct (lines_embed L HL) as [L' [HL' Hsub]].
  apply check_win_iff. exists L'. split; [exact HL' |].
  intros y Hy. destruct (Hsub y Hy) as [x [Hx ->]].
  apply (proj1 (Hsim x (small_range L x HL Hx))). apply Hown. exact Hx.
Qed.

Lemma simulates_maker_move : forall bs bb m,
  simulates bs bb -> is_legal_move bs m = true ->
  simulates (set_cell bs m p) (set_cell bb (e m) p).
Proof.
  intros bs bb m Hs Hm.
  pose proof (simulates_legal bs bb m Hs Hm) as Hbm.
  destruct Hs as [Hls [Hlb Hsim]].
  pose proof (legal_move_lt bs m Hm) as Hlt.
  pose proof (legal_move_lt bb (e m) Hbm) as Hblt.
  split; [rewrite set_cell_length; exact Hls |].
  split; [rewrite set_cell_length; exact Hlb |].
  intros x Hx. destruct (Nat.eq_dec x m) as [-> | Hxm].
  - rewrite (get_set_cell_same bs m p Hlt), (get_set_cell_same bb (e m) p Hblt).
    split; [tauto |]. intros H. exfalso. apply (mb_other_neq p). congruence.
  - assert (Hem : e m <> e x).
    { intros E. apply Hxm. symmetry. apply e_inj; [rewrite <- Hls; exact Hlt | exact Hx | exact E]. }
    rewrite (get_set_cell_other bs m x p) by congruence.
    rewrite (get_set_cell_other bb (e m) (e x) p Hem).
    apply Hsim. exact Hx.
Qed.

(** After a real Breaker reply [y], an imagined reply [c] keeps the
    simulation, provided [c] is the free cell mapped to [y] if there is one. *)
Lemma simulates_reply : forall bs bb y c,
  simulates bs bb -> is_legal_move bb y = true -> is_legal_move bs c = true ->
  (forall x, x < Ns -> e x = y -> get_cell bs x = None -> x = c) ->
  simulates (set_cell bs c (other_player p)) (set_cell bb y (other_player p)).
Proof.
  intros bs bb y c [Hls [Hlb Hsim]] Hy Hc Hcover.
  pose proof (legal_move_empty bb y Hy) as Ey.
  pose proof (legal_move_empty bs c Hc) as Ec.
  pose proof (legal_move_lt bb y Hy) as Hylt.
  pose proof (legal_move_lt bs c Hc) as Hclt.
  split; [rewrite set_cell_length; exact Hls |].
  split; [rewrite set_cell_length; exact Hlb |].
  intros x Hx. destruct (Hsim x Hx) as [Hp Ho].
  destruct (Nat.eq_dec x c) as [-> | Hxc].
  - (* the imagined reply itself *)
    rewrite (get_set_cell_same bs c (other_player p) Hclt).
    split; [| reflexivity].
    split; intros H; exfalso.
    + apply (mb_other_neq p). congruence.
    + destruct (Nat.eq_dec y (e c)) as [Hyc | Hyc].
      * rewrite <- Hyc, (get_set_cell_same bb y (other_player p) Hylt) in H.
        apply (mb_other_neq p). congruence.
      * rewrite (get_set_cell_other bb y (e c) _ Hyc) in H.
        apply Hp in H. congruence.
  - rewrite (get_set_cell_other bs c x _ (not_eq_sym Hxc)).
    destruct (Nat.eq_dec y (e x)) as [Hyx | Hyx].
    + (* the real reply lands on e x: the imagined cell x is Breaker's already *)
      rewrite <- Hyx, (get_set_cell_same bb y (other_player p) Hylt).
      assert (Hbx : get_cell bs x = Some (other_player p)).
      { destruct (get_cell bs x) as [q |] eqn:Eq.
        - destruct (player_cases p q) as [-> | ->]; [| reflexivity].
          exfalso. pose proof (proj1 Hp eq_refl) as Hb. rewrite <- Hyx in Hb. congruence.
        - exfalso. apply Hxc. apply Hcover; [exact Hx | symmetry; exact Hyx | exact Eq]. }
      rewrite Hbx. split; [| reflexivity].
      split; intros H; exfalso; apply (mb_other_neq p); congruence.
    + rewrite (get_set_cell_other bb y (e x) _ Hyx). split; [exact Hp | exact Ho].
Qed.

Theorem maker_wins_simulate : forall d bs bb,
  simulates bs bb -> maker_wins small_lines p d bs -> maker_wins big_lines p d bb.
Proof.
  intros d bs bb Hs H. revert bb Hs.
  induction H as [d bs m Hm Hw | d bs m Hm Hex Hnext IH]; intros bb Hs.
  - apply (mw_now big_lines p d bb (e m)); [exact (simulates_legal bs bb m Hs Hm) |].
    apply (simulates_win (set_cell bs m p)); [| exact Hw].
    apply simulates_maker_move; assumption.
  - pose proof (simulates_maker_move bs bb m Hs Hm) as Hs1.
    apply (mw_next big_lines p d bb (e m)); [exact (simulates_legal bs bb m Hs Hm) | |].
    + destruct Hex as [c0 Hc0]. exists (e c0).
      exact (simulates_legal _ _ c0 Hs1 Hc0).
    + intros y Hy. destruct Hex as [c0 Hc0].
      destruct (bounded_exists_dec
                  (fun x => (e x =? y) && is_legal_move (set_cell bs m p) x) Ns)
        as [[x0 [Hx0 Hf]] | Hnone].
      * (* y is the image of a free imagined cell x0: copy the reply *)
        apply andb_true_iff in Hf as [Hey Hleg]. apply Nat.eqb_eq in Hey.
        apply (IH x0 Hleg). apply simulates_reply; [exact Hs1 | exact Hy | exact Hleg |].
        intros x Hx Hxy _. apply e_inj; [exact Hx | exact Hx0 | congruence].
      * (* otherwise the imagined Breaker plays anywhere *)
        apply (IH c0 Hc0). apply simulates_reply; [exact Hs1 | exact Hy | exact Hc0 |].
        intros x Hx Hxy Ex. exfalso.
        assert (Hlx : is_legal_move (set_cell bs m p) x = true).
        { apply legal_move_intro; [| exact Ex].
          destruct Hs1 as [Hl _]. rewrite Hl. exact Hx. }
        specialize (Hnone x Hx). rewrite Hxy, Nat.eqb_refl, Hlx in Hnone.
        discriminate.
Qed.

End Embedding.

(** ** Sub-boards: the m' x n' board sits in the top-left corner of m x n *)

Definition grid_embed (n' n x : nat) : nat := (x / n') * n + x mod n'.

Lemma grid_embed_coords : forall n' n r c, c < n' ->
  grid_embed n' n (r * n' + c) = r * n + c.
Proof. intros n' n r c Hc. unfold grid_embed. rewrite idx_div, idx_mod by lia. reflexivity. Qed.

Lemma grid_embed_range : forall m' n' m n x, m' <= m -> n' <= n -> x < m' * n' ->
  grid_embed n' n x < m * n.
Proof.
  intros m' n' m n x Hm Hn Hx. unfold grid_embed.
  assert (Hn' : n' <> 0) by (intros ->; lia).
  pose proof (Nat.mod_upper_bound x n' Hn') as Hr.
  assert (Hq : x / n' < m') by (apply Nat.Div0.div_lt_upper_bound; lia).
  nia.
Qed.

Lemma grid_embed_inj : forall m' n' n x y, n' <= n -> x < m' * n' -> y < m' * n' ->
  grid_embed n' n x = grid_embed n' n y -> x = y.
Proof.
  intros m' n' n x y Hn Hx Hy E. unfold grid_embed in E.
  assert (Hn' : n' <> 0) by (intros ->; lia).
  pose proof (Nat.mod_upper_bound x n' Hn') as Hrx.
  pose proof (Nat.mod_upper_bound y n' Hn') as Hry.
  assert (Hq : x / n' = y / n').
  { rewrite <- (idx_div n (x / n') (x mod n')) by lia. rewrite E. apply idx_div. lia. }
  assert (Hr : x mod n' = y mod n').
  { rewrite <- (idx_mod n (x / n') (x mod n')) by lia. rewrite E. apply idx_mod. lia. }
  rewrite (Nat.div_mod_eq x n'), (Nat.div_mod_eq y n'), Hq, Hr. reflexivity.
Qed.

Lemma grid_lines_embed : forall m' n' m n k L, m' <= m -> n' <= n ->
  In L (gen_lines m' n' k) ->
  exists L', In L' (gen_lines m n k) /\
    forall y, In y L' -> exists x, In x L /\ y = grid_embed n' n x.
Proof.
  intros m' n' m n k L Hm Hn HL.
  apply in_gen_lines in HL as (d & r & c & Hfit & ->).
  exists (mkline n k d r c). split.
  - apply in_gen_lines. exists d, r, c. split; [| reflexivity]. destruct d; simpl in *; lia.
  - intros y Hy. apply in_mkline in Hy as [i [Hi ->]].
    pose proof (cell_at_bounds m' n' k d r c i Hfit Hi) as B.
    exists (fst (cell_at k d r c i) * n' + snd (cell_at k d r c i)). split.
    + apply in_mkline. exists i. split; [exact Hi | reflexivity].
    + rewrite grid_embed_coords by lia. reflexivity.
Qed.

(** A Maker win on the m' x n' board is a Maker win on every larger board,
    within the same number of moves. *)
Theorem mnk_maker_wins_subboard : forall m' n' m n k p d, m' <= m -> n' <= n ->
  maker_wins (gen_lines m' n' k) p d (empty_board (m' * n')) ->
  maker_wins (gen_lines m n k) p d (empty_board (m * n)).
Proof.
  intros m' n' m n k p d Hm Hn Hw.
  apply (maker_wins_simulate (gen_lines m' n' k) (gen_lines m n k) (m' * n') (m * n)
           (grid_embed n' n)) with (bs := empty_board (m' * n')); [| | | | | exact Hw].
  - intros x Hx. apply (grid_embed_range m'); assumption.
  - intros x y Hx Hy. apply (grid_embed_inj m' n' n); assumption.
  - intros L x HL Hx. exact (gen_lines_in_range m' n' k L x HL Hx).
  - intros L HL. apply (grid_lines_embed m'); assumption.
  - apply simulates_empty.
Qed.

(** ** Transposition: rows become columns *)

Definition transpose_cell (m n x : nat) : nat := (x mod n) * m + x / n.

Definition swap_direction (d : direction) : direction :=
  match d with DH => DV | DV => DH | DD => DD | DA => DA end.

Lemma transpose_coords : forall m n r c, r < m -> c < n ->
  transpose_cell m n (r * n + c) = c * m + r.
Proof. intros m n r c Hr Hc. unfold transpose_cell. rewrite idx_div, idx_mod by lia. reflexivity. Qed.

Lemma transpose_range : forall m n x, x < m * n -> transpose_cell m n x < n * m.
Proof.
  intros m n x Hx. unfold transpose_cell.
  assert (Hn : n <> 0) by (intros ->; lia).
  pose proof (Nat.mod_upper_bound x n Hn) as Hc.
  assert (Hr : x / n < m) by (apply Nat.Div0.div_lt_upper_bound; lia).
  nia.
Qed.

Lemma transpose_inj : forall m n x y, x < m * n -> y < m * n ->
  transpose_cell m n x = transpose_cell m n y -> x = y.
Proof.
  intros m n x y Hx Hy E. unfold transpose_cell in E.
  assert (Hn : n <> 0) by (intros ->; lia).
  assert (Hrx : x / n < m) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hry : y / n < m) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hc : x mod n = y mod n).
  { rewrite <- (idx_div m (x mod n) (x / n)) by lia. rewrite E. apply idx_div. lia. }
  assert (Hr : x / n = y / n).
  { rewrite <- (idx_mod m (x mod n) (x / n)) by lia. rewrite E. apply idx_mod. lia. }
  rewrite (Nat.div_mod_eq x n), (Nat.div_mod_eq y n), Hc, Hr. reflexivity.
Qed.

(** The transpose of a line is a line of the transposed board; an
    anti-diagonal is traversed in the opposite order. *)
Lemma transpose_lines_embed : forall m n k L, In L (gen_lines m n k) ->
  exists L', In L' (gen_lines n m k) /\
    forall y, In y L' -> exists x, In x L /\ y = transpose_cell m n x.
Proof.
  intros m n k L HL. apply in_gen_lines in HL as (d & r & c & Hfit & ->).
  exists (mkline m k (swap_direction d) c r). split.
  - apply in_gen_lines. exists (swap_direction d), c, r. split; [| reflexivity].
    destruct d; simpl in *; lia.
  - intros y Hy. apply in_mkline in Hy as [i [Hi ->]].
    assert (Hj : exists j, j < k /\
      fst (cell_at k (swap_direction d) c r i) * m + snd (cell_at k (swap_direction d) c r i) =
      snd (cell_at k d r c j) * m + fst (cell_at k d r c j)).
    { destruct d; simpl.
      - exists i. split; [exact Hi | reflexivity].
      - exists i. split; [exact Hi | reflexivity].
      - exists i. split; [exact Hi | reflexivity].
      - exists (k - 1 - i). split; [lia |].
        replace (k - 1 - (k - 1 - i)) with i by lia. reflexivity. }
    destruct Hj as [j [Hj Heq]].
    pose proof (cell_at_bounds m n k d r c j Hfit Hj) as B.
    exists (fst (cell_at k d r c j) * n + snd (cell_at k d r c j)). split.
    + apply in_mkline. exists j. split; [exact Hj | reflexivity].
    + rewrite transpose_coords by lia. exact Heq.
Qed.

Theorem mnk_maker_wins_transpose : forall m n k p d,
  maker_wins (gen_lines m n k) p d (empty_board (m * n)) ->
  maker_wins (gen_lines n m k) p d (empty_board (n * m)).
Proof.
  intros m n k p d Hw.
  apply (maker_wins_simulate (gen_lines m n k) (gen_lines n m k) (m * n) (n * m)
           (transpose_cell m n)) with (bs := empty_board (m * n)); [| | | | | exact Hw].
  - apply transpose_range.
  - apply transpose_inj.
  - intros L x HL Hx. exact (gen_lines_in_range m n k L x HL Hx).
  - apply transpose_lines_embed.
  - apply simulates_empty.
Qed.

(** ** Breaker wins and draws for whole families of boards *)

Corollary mnk_breaker_win_subboard : forall m n m' n' k, m' <= m -> n' <= n ->
  (forall d, ~ maker_wins (gen_lines m n k) P1 d (empty_board (m * n))) ->
  forall d, ~ maker_wins (gen_lines m' n' k) P1 d (empty_board (m' * n')).
Proof.
  intros m n m' n' k Hm Hn Hbreaker d Hw.
  apply (Hbreaker d). apply (mnk_maker_wins_subboard m' n'); assumption.
Qed.

Corollary mnk_breaker_win_transpose : forall m n k,
  (forall d, ~ maker_wins (gen_lines m n k) P1 d (empty_board (m * n))) ->
  forall d, ~ maker_wins (gen_lines n m k) P1 d (empty_board (n * m)).
Proof.
  intros m n k Hbreaker d Hw.
  apply (Hbreaker d). apply mnk_maker_wins_transpose. exact Hw.
Qed.

(** One Breaker win settles a whole family: every board that fits inside
    m x n (either way round), with lines at least as long, is a draw. *)
Theorem mnk_breaker_win_family : forall m n k m' n' k',
  ((m' <= m /\ n' <= n) \/ (m' <= n /\ n' <= m)) -> k <= k' ->
  (forall d, ~ maker_wins (gen_lines m n k) P1 d (empty_board (m * n))) ->
  game_is_draw (gen_lines m' n' k') (empty_board (m' * n')).
Proof.
  intros m n k m' n' k' Hfit Hk Hbreaker.
  apply (mnk_draw_longer_lines m' n' k k' Hk).
  destruct Hfit as [[Hm Hn] | [Hm Hn]].
  - apply (mnk_breaker_win_subboard m n); assumption.
  - apply (mnk_breaker_win_subboard n m); [exact Hm | exact Hn |].
    apply mnk_breaker_win_transpose. exact Hbreaker.
Qed.
