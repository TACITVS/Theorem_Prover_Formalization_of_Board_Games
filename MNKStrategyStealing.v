(** * MNKStrategyStealing.v: Strategy Stealing, Machine-Checked

    Nash's strategy-stealing argument for strong positional games: on ANY
    family of winning lines and any board size, the second player can never
    force a win from the empty board.

    Ingredients, all proved here for the inductive semantics [forces_win]:
    - [forces_win_swap]: exchanging the colours of all stones exchanges the
      roles of the players.
    - [steal]: an extra stone of your own colour never hurts - from a
      position where [p] forces a win, adding a [p]-stone either completes a
      line at once or still lets [p] force a win within the same bound.
    - [not_both]: two players cannot both force a win from the same position.

    Consequence ([positional_game_win_or_draw]), proved constructively using
    the verified evaluator [wins_b]: every such game is either a forced
    first-player win or a draw.  In particular this holds for every (m, n, k)
    game ([mnk_value_win_or_draw]).

    Zero axioms, zero admits. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From MNK Require Import MNKBoard MNKGame MNKErdosSelfridge.

(* ========================================================================= *)
(** * 1. Board lemmas                                                        *)
(* ========================================================================= *)

Lemma neq_other : forall p, p <> other_player p.
Proof. destruct p; discriminate. Qed.

Lemma other_neq : forall p, other_player p <> p.
Proof. destruct p; discriminate. Qed.

Lemma set_cell_comm : forall b i j p q, i <> j ->
  set_cell (set_cell b i p) j q = set_cell (set_cell b j q) i p.
Proof.
  induction b as [| a b IH]; intros [| i] [| j] p q Hij; simpl; try reflexivity.
  - congruence.
  - f_equal. apply IH. lia.
Qed.

Lemma legal_set_other : forall b y x r,
  is_legal_move b y = true -> y <> x -> is_legal_move (set_cell b x r) y = true.
Proof.
  intros b y x r Hy Hne. apply legal_move_intro.
  - rewrite set_cell_length. apply legal_move_lt. exact Hy.
  - rewrite get_set_cell_other by congruence. apply legal_move_empty. exact Hy.
Qed.

Lemma legal_after_set_neq : forall b c r y,
  is_legal_move b c = true -> is_legal_move (set_cell b c r) y = true -> y <> c.
Proof.
  intros b c r y Hc Hy Heq. subst y.
  pose proof (legal_move_empty _ _ Hy) as He.
  rewrite get_set_cell_same in He by (apply legal_move_lt; exact Hc). discriminate.
Qed.

Lemma needs_move : forall lines p d b,
  forces_win lines p d b -> exists m, is_legal_move b m = true.
Proof. intros lines p d b H. destruct H; eauto. Qed.

Lemma forallb_ext_all : forall (f g : nat -> bool) l,
  (forall x, f x = g x) -> forallb f l = forallb g l.
Proof.
  intros f g l H. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite H, IH. reflexivity.
Qed.

Lemma existsb_ext_all : forall (f g : list nat -> bool) l,
  (forall x, f x = g x) -> existsb f l = existsb g l.
Proof.
  intros f g l H. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite H, IH. reflexivity.
Qed.

(** A stone of one player is irrelevant to the other player's lines. *)
Lemma check_win_other_stone : forall b x p q lines,
  p <> q -> is_legal_move b x = true ->
  check_win (set_cell b x p) q lines = check_win b q lines.
Proof.
  intros b x p q lines Hpq Hx. unfold check_win. apply existsb_ext_all. intros L.
  unfold line_owned_by. apply forallb_ext_all. intros y.
  rewrite owned_set by (apply legal_move_lt; exact Hx).
  destruct (Nat.eqb_spec y x) as [Heq | _]; [| reflexivity].
  subst y. rewrite owned_empty_cell by (apply legal_move_empty; exact Hx).
  destruct p, q; simpl; congruence.
Qed.

(* ========================================================================= *)
(** * 2. Colour symmetry                                                     *)
(* ========================================================================= *)

Definition swap_board (b : board_t) : board_t := map (option_map other_player) b.

Lemma swap_length : forall b, length (swap_board b) = length b.
Proof. intros b. apply length_map. Qed.

Lemma swap_get : forall b x,
  get_cell (swap_board b) x = option_map other_player (get_cell b x).
Proof.
  intros b x. unfold get_cell, swap_board.
  exact (map_nth (option_map other_player) b None x).
Qed.

Lemma legal_swap : forall b x, is_legal_move (swap_board b) x = is_legal_move b x.
Proof.
  intros b x. unfold is_legal_move, is_cell_empty. rewrite swap_length, swap_get.
  destruct (get_cell b x); reflexivity.
Qed.

Lemma swap_set_cell : forall b x p,
  set_cell (swap_board b) x (other_player p) = swap_board (set_cell b x p).
Proof.
  induction b as [| a b IH]; intros [| x] p; simpl; try reflexivity.
  f_equal. apply IH.
Qed.

Lemma owned_swap : forall b p x,
  cell_owned_by (swap_board b) (other_player p) x = cell_owned_by b p x.
Proof.
  intros b p x. unfold cell_owned_by. rewrite swap_get.
  destruct (get_cell b x) as [q |]; [| reflexivity].
  simpl. destruct p, q; reflexivity.
Qed.

Lemma check_win_swap : forall b p lines,
  check_win (swap_board b) (other_player p) lines = check_win b p lines.
Proof.
  intros b p lines. unfold check_win. apply existsb_ext_all. intros L.
  unfold line_owned_by. apply forallb_ext_all. intros x. apply owned_swap.
Qed.

Lemma swap_empty : forall N, swap_board (empty_board N) = empty_board N.
Proof.
  intros N. unfold swap_board, empty_board.
  induction N as [| N IH]; simpl; [reflexivity | f_equal; exact IH].
Qed.

Theorem forces_win_swap : forall lines p d b,
  forces_win lines p d b -> forces_win lines (other_player p) d (swap_board b).
Proof.
  intros lines p d b H.
  induction H as [d b m Hm Hw | d b m Hm Hex Hno Hfw IH].
  - apply (fw_now _ _ d (swap_board b) m).
    + rewrite legal_swap. exact Hm.
    + rewrite swap_set_cell, check_win_swap. exact Hw.
  - apply (fw_next _ _ d (swap_board b) m).
    + rewrite legal_swap. exact Hm.
    + destruct Hex as [c Hc]. exists c. rewrite swap_set_cell, legal_swap. exact Hc.
    + intros c Hc. rewrite swap_set_cell in Hc |- *. rewrite legal_swap in Hc.
      rewrite swap_set_cell, check_win_swap. apply Hno. exact Hc.
    + intros c Hc. rewrite swap_set_cell in Hc |- *. rewrite legal_swap in Hc.
      rewrite swap_set_cell. apply IH. exact Hc.
Qed.

(* ========================================================================= *)
(** * 3. An extra stone never hurts                                          *)
(* ========================================================================= *)

Lemma steal : forall lines p d b, forces_win lines p d b ->
  forall x, is_legal_move b x = true ->
  check_win (set_cell b x p) p lines = true \/ forces_win lines p d (set_cell b x p).
Proof.
  intros lines p d b H.
  induction H as [d b m Hm Hw | d b m Hm Hex Hno Hfw IH]; intros x Hx.
  - destruct (Nat.eq_dec m x) as [Heq | Hne].
    + subst m. left. exact Hw.
    + right. apply (fw_now _ _ d _ m).
      * apply legal_set_other; [exact Hm | exact Hne].
      * rewrite set_cell_comm by congruence.
        apply extra_stone_preserves_win. exact Hw.
  - right. destruct (Nat.eq_dec m x) as [Heq | Hne].
    + (* The strategy asks for the cell we already own: play a free cell z. *)
      subst x. destruct Hex as [z Hz].
      destruct (check_win (set_cell (set_cell b m p) z p) p lines) eqn:Ew.
      * apply (fw_now _ _ d _ z Hz Ew).
      * apply (fw_next _ _ d _ z Hz).
        -- destruct (needs_move _ _ _ _ (Hfw z Hz)) as [c Hc].
           exists c. apply legal_set_other.
           ++ exact (legal_after_set _ _ _ _ Hz Hc).
           ++ exact (legal_after_set_neq _ _ _ _ Hz Hc).
        -- intros c Hc.
           pose proof (legal_after_set _ _ _ _ Hz Hc) as Hc1.
           pose proof (legal_after_set_neq _ _ _ _ Hz Hc) as Hcz.
           rewrite (set_cell_comm (set_cell b m p) z c p (other_player p)) by congruence.
           rewrite (check_win_other_stone _ z p (other_player p) lines (neq_other p)
                      (legal_set_other _ _ _ _ Hz (not_eq_sym Hcz))).
           apply Hno. exact Hc1.
        -- intros c Hc.
           pose proof (legal_after_set _ _ _ _ Hz Hc) as Hc1.
           pose proof (legal_after_set_neq _ _ _ _ Hz Hc) as Hcz.
           destruct (IH c Hc1 z (legal_set_other _ _ _ _ Hz (not_eq_sym Hcz)))
             as [Hw' | Hf'].
           ++ exfalso.
              rewrite <- (set_cell_comm (set_cell b m p) z c p (other_player p)) in Hw'
                by congruence.
              rewrite (check_win_other_stone _ c (other_player p) p lines (other_neq p) Hc)
                in Hw'.
              congruence.
           ++ rewrite (set_cell_comm (set_cell b m p) z c p (other_player p)) by congruence.
              exact Hf'.
    + (* The strategy move m is still free: play it. *)
      assert (Hm' : is_legal_move (set_cell b x p) m = true)
        by (apply legal_set_other; [exact Hm | exact Hne]).
      assert (Hx1 : is_legal_move (set_cell b m p) x = true)
        by (apply legal_set_other; [exact Hx | congruence]).
      assert (Hcomm : set_cell (set_cell b x p) m p = set_cell (set_cell b m p) x p)
        by (apply set_cell_comm; congruence).
      destruct (check_win (set_cell (set_cell b x p) m p) p lines) eqn:Ew.
      * apply (fw_now _ _ d _ m Hm' Ew).
      * apply (fw_next _ _ d _ m Hm').
        -- destruct (needs_move _ _ _ _ (Hfw x Hx1)) as [c Hc].
           exists c. rewrite Hcomm. apply legal_set_other.
           ++ exact (legal_after_set _ _ _ _ Hx1 Hc).
           ++ exact (legal_after_set_neq _ _ _ _ Hx1 Hc).
        -- intros c Hc. rewrite Hcomm in Hc |- *.
           pose proof (legal_after_set _ _ _ _ Hx1 Hc) as Hc1.
           pose proof (legal_after_set_neq _ _ _ _ Hx1 Hc) as Hcx.
           rewrite (set_cell_comm (set_cell b m p) x c p (other_player p)) by congruence.
           rewrite (check_win_other_stone _ x p (other_player p) lines (neq_other p)
                      (legal_set_other _ _ _ _ Hx1 (not_eq_sym Hcx))).
           apply Hno. exact Hc1.
        -- intros c Hc. rewrite Hcomm in Hc |- *.
           pose proof (legal_after_set _ _ _ _ Hx1 Hc) as Hc1.
           pose proof (legal_after_set_neq _ _ _ _ Hx1 Hc) as Hcx.
           destruct (IH c Hc1 x (legal_set_other _ _ _ _ Hx1 (not_eq_sym Hcx)))
             as [Hw' | Hf'].
           ++ exfalso.
              rewrite <- (set_cell_comm (set_cell b m p) x c p (other_player p)) in Hw'
                by congruence.
              rewrite (check_win_other_stone _ c (other_player p) p lines (other_neq p) Hc)
                in Hw'.
              rewrite <- Hcomm in Hw'. congruence.
           ++ rewrite (set_cell_comm (set_cell b m p) x c p (other_player p)) by congruence.
              exact Hf'.
Qed.

(* ========================================================================= *)
(** * 4. Two players cannot both force a win                                 *)
(* ========================================================================= *)

Lemma not_both : forall lines p d b, forces_win lines p d b ->
  forall d', (forall m, is_legal_move b m = true ->
     check_win (set_cell b m p) p lines = false /\
     forces_win lines (other_player p) d' (set_cell b m p)) -> False.
Proof.
  intros lines p d b H.
  induction H as [d b m Hm Hw | d b m Hm Hex Hno Hfw IH]; intros d' Hopp.
  - destruct (Hopp m Hm) as [Hn _]. congruence.
  - destruct (Hopp m Hm) as [_ Hq].
    inversion Hq as [d1 b1 c Hc Hwq | d1 b1 c Hc Hexq Hnoq Hfwq]; subst.
    + rewrite (Hno c Hc) in Hwq. discriminate.
    + apply (IH c Hc d1). intros m' Hm'.
      rewrite other_player_involutive in Hnoq, Hfwq.
      split; [apply Hnoq | apply Hfwq]; exact Hm'.
Qed.

(* ========================================================================= *)
(** * 5. Strategy stealing                                                   *)
(* ========================================================================= *)

(** On every hypergraph and every board size, the second player has no
    forced win from the empty board. *)
Theorem strategy_stealing : forall lines N d,
  ~ second_forces_win lines d (empty_board N).
Proof.
  intros lines N d [[m0 Hm0] Hall].
  (* By colour symmetry, P1 answering ANY P2 opening as second player wins. *)
  assert (Hsw : forall y, is_legal_move (empty_board N) y = true ->
            check_win (set_cell (empty_board N) y P2) P2 lines = false /\
            forces_win lines P1 d (set_cell (empty_board N) y P2)).
  { intros y Hy. destruct (Hall y Hy) as [Hn Hf].
    pose proof (forces_win_swap _ _ _ _ Hf) as Hs.
    rewrite <- swap_set_cell, swap_empty in Hs.
    split.
    - rewrite <- Hn. rewrite <- (check_win_swap _ P1 lines), <- swap_set_cell, swap_empty.
      reflexivity.
    - exact Hs. }
  (* P1 steals that strategy: open at m0, ignore it, and answer P2's move. *)
  assert (Hwin : forces_win lines P1 (S d) (empty_board N)).
  { destruct (check_win (set_cell (empty_board N) m0 P1) P1 lines) eqn:Ew.
    - exact (fw_now _ _ d _ m0 Hm0 Ew).
    - apply (fw_next _ _ d _ m0 Hm0).
      + destruct (Hall m0 Hm0) as [_ Hf]. exact (needs_move _ _ _ _ Hf).
      + intros y Hy.
        pose proof (legal_after_set _ _ _ _ Hm0 Hy) as Hy0.
        pose proof (legal_after_set_neq _ _ _ _ Hm0 Hy) as Hne.
        change (other_player P1) with P2.
        rewrite (set_cell_comm (empty_board N) m0 y P1 P2) by congruence.
        rewrite (check_win_other_stone _ m0 P1 P2 lines ltac:(discriminate)
                   (legal_set_other _ _ _ _ Hm0 (not_eq_sym Hne))).
        exact (proj1 (Hsw y Hy0)).
      + intros y Hy.
        pose proof (legal_after_set _ _ _ _ Hm0 Hy) as Hy0.
        pose proof (legal_after_set_neq _ _ _ _ Hm0 Hy) as Hne.
        change (other_player P1) with P2.
        destruct (steal _ _ _ _ (proj2 (Hsw y Hy0)) m0
                    (legal_set_other _ _ _ _ Hm0 (not_eq_sym Hne))) as [Hc | Hc].
        * exfalso.
          rewrite <- (set_cell_comm (empty_board N) m0 y P1 P2) in Hc by congruence.
          rewrite (check_win_other_stone _ y P2 P1 lines ltac:(discriminate) Hy) in Hc.
          congruence.
        * rewrite (set_cell_comm (empty_board N) m0 y P1 P2) by congruence. exact Hc. }
  exact (not_both _ _ _ _ Hwin d Hall).
Qed.

(** Every strong positional game from the empty board is either a forced
    first-player win or a draw (constructive: decided by [wins_b]). *)
Theorem positional_game_win_or_draw : forall lines N,
  (exists d, forces_win lines P1 d (empty_board N)) \/ game_is_draw lines (empty_board N).
Proof.
  intros lines N.
  destruct (wins_b lines P1 (length (legal_moves (empty_board N))) (empty_board N)) eqn:E.
  - left. eexists. apply wins_b_spec. exact E.
  - right. split.
    + apply no_forced_win_by_evaluation. exact E.
    + intros d. apply strategy_stealing.
Qed.

(** For (m, n, k) games: the second player never wins ... *)
Corollary mnk_second_player_never_wins : forall m n k d,
  ~ second_forces_win (gen_lines m n k) d (empty_board (m * n)).
Proof. intros m n k d. apply strategy_stealing. Qed.

(** ... so every (m, n, k) game is a first-player win or a draw. *)
Corollary mnk_value_win_or_draw : forall m n k,
  (exists d, forces_win (gen_lines m n k) P1 d (empty_board (m * n))) \/
  game_is_draw (gen_lines m n k) (empty_board (m * n)).
Proof. intros m n k. apply positional_game_win_or_draw. Qed.
