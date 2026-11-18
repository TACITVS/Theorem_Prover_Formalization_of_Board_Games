(** **************************************************************************
    MNKGame.v: Universal State Transitions, Positional Monotonicity,
    and Game-Theoretic Invariants for (m, n, k) Games
    
    Formalizes the turn-based rules of positional maker-maker games:
    - Players P1 (First mover) and P2 (Second mover).
    - Board state as a list of option player.
    - Permanent stone placement (pure addition, no stone removal).
    - Monotonicity Theorem: Extra stones never destroy an existing win.
    - Line ownership and win verification.
    - Game semantics of the strong game: [forces_win] (a player forces a
      completed line within d own moves, the opponent never completing one
      first), [second_forces_win], and [game_is_draw].
    - A verified exhaustive evaluator [wins_b] ([wins_b_spec]) used to prove
      "no forced win" statements by computation.

    Zero unproven axioms, zero admissions (Closed under global context).
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool PeanoNat.
Import ListNotations.
Require Import MNK.MNKBoard.

Section MNKGame.

(** Player definition *)
Inductive player : Type :=
  | P1 : player
  | P2 : player.

Definition other_player (p : player) : player :=
  match p with
  | P1 => P2
  | P2 => P1
  end.

Theorem other_player_involutive : forall p : player,
  other_player (other_player p) = p.
Proof.
  destruct p; reflexivity.
Qed.

Definition player_eqb (p1 p2 : player) : bool :=
  match p1, p2 with
  | P1, P1 => true
  | P2, P2 => true
  | _, _ => false
  end.

Theorem player_eqb_refl : forall p : player,
  player_eqb p p = true.
Proof.
  destruct p; reflexivity.
Qed.

Theorem player_eqb_eq : forall p1 p2 : player,
  player_eqb p1 p2 = true <-> p1 = p2.
Proof.
  destruct p1; destruct p2; simpl; split; intros H;
  try reflexivity; try discriminate.
Qed.

(** Board representation as flat list *)
Definition board_t : Type := list (option player).

Definition empty_board (num_cells : nat) : board_t :=
  repeat None num_cells.

Definition get_cell (b : board_t) (idx : nat) : option player :=
  nth idx b None.

Fixpoint set_cell (b : board_t) (idx : nat) (p : player) : board_t :=
  match b, idx with
  | [], _ => []
  | _ :: tl, 0 => Some p :: tl
  | hd :: tl, S idx' => hd :: set_cell tl idx' p
  end.

Theorem set_cell_length : forall b idx p,
  length (set_cell b idx p) = length b.
Proof.
  induction b as [|hd tl IH]; intros [|idx'] p; simpl; auto.
Qed.

Theorem get_set_cell_same : forall b idx p,
  idx < length b ->
  get_cell (set_cell b idx p) idx = Some p.
Proof.
  induction b as [|hd tl IH]; intros [|idx'] p Hlen; simpl in *.
  - lia.
  - lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Theorem get_set_cell_other : forall b idx idx' p,
  idx <> idx' ->
  get_cell (set_cell b idx p) idx' = get_cell b idx'.
Proof.
  induction b as [|hd tl IH]; intros idx idx' p Hneq.
  - destruct idx, idx'; reflexivity.
  - destruct idx as [|idx], idx' as [|idx']; simpl.
    + congruence.
    + reflexivity.
    + reflexivity.
    + unfold get_cell in *. simpl. apply IH. lia.
Qed.

(** Legal move predicate *)
Definition is_cell_empty (b : board_t) (idx : nat) : bool :=
  match get_cell b idx with
  | None => true
  | Some _ => false
  end.

Definition is_legal_move (b : board_t) (idx : nat) : bool :=
  (idx <? length b) && is_cell_empty b idx.

(** Winning Line Evaluation *)
Definition cell_owned_by (b : board_t) (p : player) (idx : nat) : bool :=
  match get_cell b idx with
  | Some q => player_eqb p q
  | None => false
  end.

Definition line_owned_by (b : board_t) (p : player) (line : list nat) : bool :=
  forallb (cell_owned_by b p) line.

Definition check_win (b : board_t) (p : player) (lines : list (list nat)) : bool :=
  existsb (line_owned_by b p) lines.

(** Board Subsumption / Monotonicity Relation *)
Definition board_sub (b1 b2 : board_t) (p : player) : Prop :=
  forall idx, get_cell b1 idx = Some p -> get_cell b2 idx = Some p.

Theorem board_sub_refl : forall b p,
  board_sub b b p.
Proof.
  intros b p idx H. exact H.
Qed.

Theorem board_sub_trans : forall b1 b2 b3 p,
  board_sub b1 b2 p ->
  board_sub b2 b3 p ->
  board_sub b1 b3 p.
Proof.
  intros b1 b2 b3 p H12 H23 idx H.
  apply H23. apply H12. exact H.
Qed.

Theorem set_cell_preserves_sub : forall b idx p,
  board_sub b (set_cell b idx p) p.
Proof.
  intros b idx p j Hj.
  destruct (Nat.eq_dec idx j) as [Heq | Hneq].
  - subst j.
    destruct (lt_dec idx (length b)) as [Hlt | Hge].
    + rewrite get_set_cell_same; [reflexivity | exact Hlt].
    + unfold get_cell in Hj.
      rewrite nth_overflow in Hj by lia. discriminate.
  - rewrite get_set_cell_other by exact Hneq.
    exact Hj.
Qed.

(** Positional Monotonicity Theorem:
    Winning lines remain winning when additional stones of color p are placed! *)
Theorem cell_owned_monotonic : forall b1 b2 p idx,
  board_sub b1 b2 p ->
  cell_owned_by b1 p idx = true ->
  cell_owned_by b2 p idx = true.
Proof.
  intros b1 b2 p idx Hsub Hc.
  unfold cell_owned_by in *.
  destruct (get_cell b1 idx) as [q|] eqn:H1; [|discriminate].
  apply player_eqb_eq in Hc. subst q.
  assert (H2 : get_cell b2 idx = Some p) by (apply Hsub; exact H1).
  rewrite H2. apply player_eqb_refl.
Qed.

Theorem line_owned_monotonic : forall b1 b2 p line,
  board_sub b1 b2 p ->
  line_owned_by b1 p line = true ->
  line_owned_by b2 p line = true.
Proof.
  intros b1 b2 p line Hsub.
  induction line as [|idx tl IH]; simpl; intros H.
  - reflexivity.
  - apply andb_true_iff in H as [Hhd Htl].
    apply andb_true_iff. split.
    + apply cell_owned_monotonic with (b1 := b1); assumption.
    + apply IH. assumption.
Qed.

Theorem check_win_monotonic : forall b1 b2 p lines,
  board_sub b1 b2 p ->
  check_win b1 p lines = true ->
  check_win b2 p lines = true.
Proof.
  intros b1 b2 p lines Hsub.
  induction lines as [|l ls IH]; simpl; intros H; [discriminate |].
  apply orb_true_iff in H as [Hl | Hls].
  - apply orb_true_iff. left.
    apply line_owned_monotonic with (b1 := b1); assumption.
  - apply orb_true_iff. right.
    apply IH. assumption.
Qed.

(** Corollary: Extra Stone Weak Positivity Theorem *)
Theorem extra_stone_preserves_win : forall b p idx lines,
  check_win b p lines = true ->
  check_win (set_cell b idx p) p lines = true.
Proof.
  intros b p idx lines Hwin.
  apply check_win_monotonic with (b1 := b); [|exact Hwin].
  apply set_cell_preserves_sub.
Qed.

(* ========================================================================= *)
(** * Basic facts about boards, legal moves and winning                       *)
(* ========================================================================= *)

Definition legal_moves (b : board_t) : list nat :=
  filter (is_cell_empty b) (seq 0 (length b)).

Definition nonempty {A : Type} (l : list A) : bool :=
  match l with [] => false | _ => true end.

Lemma nonempty_iff : forall (A : Type) (l : list A),
  nonempty l = true <-> exists x, In x l.
Proof.
  intros A [| x l]; simpl; split.
  - discriminate.
  - intros [x []].
  - intros _. exists x. left. reflexivity.
  - reflexivity.
Qed.

Lemma in_legal_moves : forall b x,
  In x (legal_moves b) <-> is_legal_move b x = true.
Proof.
  intros b x. unfold legal_moves, is_legal_move.
  rewrite filter_In, in_seq, andb_true_iff, Nat.ltb_lt.
  split; intros [H1 H2]; split; auto; lia.
Qed.

Lemma cell_owned_iff : forall b p x,
  cell_owned_by b p x = true <-> get_cell b x = Some p.
Proof.
  intros b p x. unfold cell_owned_by.
  destruct (get_cell b x) as [q|].
  - rewrite player_eqb_eq. split; intros H; congruence.
  - split; discriminate.
Qed.

Lemma check_win_iff : forall b p lines,
  check_win b p lines = true <->
  exists L, In L lines /\ forall x, In x L -> get_cell b x = Some p.
Proof.
  intros b p lines. unfold check_win, line_owned_by.
  rewrite existsb_exists. split.
  - intros [L [HL H]]. exists L. split; [exact HL|].
    intros x Hx. rewrite forallb_forall in H. apply cell_owned_iff. auto.
  - intros [L [HL H]]. exists L. split; [exact HL|].
    rewrite forallb_forall. intros x Hx. apply cell_owned_iff. auto.
Qed.

Lemma empty_board_length : forall N, length (empty_board N) = N.
Proof. intros N. apply repeat_length. Qed.

Lemma get_cell_empty_board : forall N x, get_cell (empty_board N) x = None.
Proof. intros N x. unfold get_cell, empty_board. apply nth_repeat. Qed.

Lemma legal_move_lt : forall b x, is_legal_move b x = true -> x < length b.
Proof.
  intros b x H. unfold is_legal_move in H.
  apply andb_true_iff in H as [H _]. apply Nat.ltb_lt. exact H.
Qed.

Lemma legal_move_empty : forall b x, is_legal_move b x = true -> get_cell b x = None.
Proof.
  intros b x H. unfold is_legal_move, is_cell_empty in H.
  apply andb_true_iff in H as [_ H]. destruct (get_cell b x); congruence.
Qed.

Lemma legal_move_intro : forall b x,
  x < length b -> get_cell b x = None -> is_legal_move b x = true.
Proof.
  intros b x Hx He. unfold is_legal_move, is_cell_empty.
  rewrite He. apply andb_true_iff. split; [apply Nat.ltb_lt; exact Hx | reflexivity].
Qed.

Lemma filter_length_drop_one : forall (l : list nat) (f g : nat -> bool) x,
  NoDup l -> In x l -> f x = true -> g x = false ->
  (forall y, y <> x -> f y = g y) ->
  length (filter f l) = S (length (filter g l)).
Proof.
  induction l as [| a l IH]; intros f g x Hnd Hin Hf Hg Hfg; [destruct Hin |].
  apply NoDup_cons_iff in Hnd as [Hna Hnd].
  destruct (Nat.eq_dec a x) as [-> | Hax].
  - simpl. rewrite Hf, Hg. simpl. f_equal.
    apply f_equal, filter_ext_in. intros y Hy. apply Hfg. intros ->. contradiction.
  - destruct Hin as [Hin | Hin]; [congruence |].
    simpl. rewrite (Hfg a Hax).
    destruct (g a); simpl; rewrite (IH f g x); auto.
Qed.

(** Every move consumes exactly one empty cell. *)
Lemma legal_moves_set_length : forall b x p,
  is_legal_move b x = true ->
  S (length (legal_moves (set_cell b x p))) = length (legal_moves b).
Proof.
  intros b x p Hx. unfold legal_moves. rewrite set_cell_length.
  symmetry. apply filter_length_drop_one with (x := x).
  - apply seq_NoDup.
  - apply in_seq. pose proof (legal_move_lt b x Hx). lia.
  - unfold is_legal_move in Hx. apply andb_true_iff in Hx as [_ Hx]. exact Hx.
  - unfold is_cell_empty. rewrite get_set_cell_same by (apply legal_move_lt; auto).
    reflexivity.
  - intros y Hy. unfold is_cell_empty.
    rewrite get_set_cell_other by congruence. reflexivity.
Qed.

(* ========================================================================= *)
(** * Game semantics of the strong (maker-maker) game                         *)
(* ========================================================================= *)

(** [forces_win lines p d b]: player [p], to move on board [b], has a strategy
    that completes one of [lines] within at most [d] of its own moves, against
    EVERY sequence of legal replies, and the opponent never completes a line
    first.  A move that fills the board without winning is a draw, so a
    continuation must leave the opponent at least one legal reply. *)
Inductive forces_win (lines : list (list nat)) (p : player) : nat -> board_t -> Prop :=
  | fw_now : forall d b m,
      is_legal_move b m = true ->
      check_win (set_cell b m p) p lines = true ->
      forces_win lines p (S d) b
  | fw_next : forall d b m,
      is_legal_move b m = true ->
      (exists c, is_legal_move (set_cell b m p) c = true) ->
      (forall c, is_legal_move (set_cell b m p) c = true ->
         check_win (set_cell (set_cell b m p) c (other_player p))
                   (other_player p) lines = false) ->
      (forall c, is_legal_move (set_cell b m p) c = true ->
         forces_win lines p d (set_cell (set_cell b m p) c (other_player p))) ->
      forces_win lines p (S d) b.

(** Player 2 forces a win: whatever Player 1 opens with (from [b], Player 1 to
    move), Player 1 does not win at once and Player 2 then forces a win. *)
Definition second_forces_win (lines : list (list nat)) (d : nat) (b : board_t) : Prop :=
  (exists m, is_legal_move b m = true) /\
  forall m, is_legal_move b m = true ->
    check_win (set_cell b m P1) P1 lines = false /\
    forces_win lines P2 d (set_cell b m P1).

(** The game value is a draw when neither player can force a win. *)
Definition game_is_draw (lines : list (list nat)) (b : board_t) : Prop :=
  (forall d, ~ forces_win lines P1 d b) /\ (forall d, ~ second_forces_win lines d b).

Theorem forces_win_mono : forall lines p d b,
  forces_win lines p d b -> forall d', d <= d' -> forces_win lines p d' b.
Proof.
  intros lines p d b H.
  induction H as [d b m Hm Hw | d b m Hm Hex Hno Hfw IH]; intros d' Hd.
  - destruct d' as [| d']; [lia |]. eapply fw_now; eauto.
  - destruct d' as [| d']; [lia |]. eapply fw_next; eauto.
    intros c Hc. apply IH; [exact Hc | lia].
Qed.

(** A forced win never needs more own moves than there are empty cells. *)
Theorem forces_win_cap : forall lines p d b,
  forces_win lines p d b -> forces_win lines p (length (legal_moves b)) b.
Proof.
  intros lines p d b H.
  induction H as [d b m Hm Hw | d b m Hm Hex Hno Hfw IH].
  - pose proof (legal_moves_set_length b m p Hm) as E.
    destruct (length (legal_moves b)) as [| e]; [lia |]. eapply fw_now; eauto.
  - pose proof (legal_moves_set_length b m p Hm) as E1.
    destruct Hex as [c0 Hc0].
    pose proof (legal_moves_set_length (set_cell b m p) c0 (other_player p) Hc0) as E2.
    destruct (length (legal_moves b)) as [| [| e]] eqn:Hlen; [lia | lia |].
    eapply fw_next; [exact Hm | exists c0; exact Hc0 | exact Hno |].
    intros c Hc. apply forces_win_mono with (d := length (legal_moves
      (set_cell (set_cell b m p) c (other_player p)))); [apply IH; exact Hc |].
    pose proof (legal_moves_set_length (set_cell b m p) c (other_player p) Hc). lia.
Qed.

(* ========================================================================= *)
(** * A verified exhaustive evaluator                                         *)
(* ========================================================================= *)

Fixpoint wins_b (lines : list (list nat)) (p : player) (d : nat) (b : board_t) : bool :=
  match d with
  | 0 => false
  | S d' =>
      existsb (fun m =>
        let b1 := set_cell b m p in
        check_win b1 p lines ||
        (nonempty (legal_moves b1) &&
         forallb (fun c =>
           let b2 := set_cell b1 c (other_player p) in
           negb (check_win b2 (other_player p) lines) && wins_b lines p d' b2)
         (legal_moves b1)))
      (legal_moves b)
  end.

Theorem wins_b_spec : forall lines p d b,
  wins_b lines p d b = true <-> forces_win lines p d b.
Proof.
  intros lines p d. induction d as [| d IH]; intros b.
  - simpl. split; [discriminate | intros H; inversion H].
  - simpl. rewrite existsb_exists. split.
    + intros [m [Hm H]]. apply in_legal_moves in Hm.
      apply orb_true_iff in H as [H | H].
      * eapply fw_now; eauto.
      * apply andb_true_iff in H as [Hne Hall].
        apply nonempty_iff in Hne as [c Hc].
        rewrite forallb_forall in Hall.
        apply fw_next with (m := m); [exact Hm | exists c; apply in_legal_moves; exact Hc | |].
        -- intros c' Hc'. apply in_legal_moves in Hc'.
           specialize (Hall c' Hc'). apply andb_true_iff in Hall as [Hn _].
           apply negb_true_iff in Hn. exact Hn.
        -- intros c' Hc'. apply in_legal_moves in Hc'.
           specialize (Hall c' Hc'). apply andb_true_iff in Hall as [_ Hw].
           apply IH. exact Hw.
    + intros H. inversion H as [d0 b0 m Hm Hw | d0 b0 m Hm Hex Hno Hfw]; subst.
      * exists m. split; [apply in_legal_moves; exact Hm |].
        rewrite Hw. reflexivity.
      * exists m. split; [apply in_legal_moves; exact Hm |].
        apply orb_true_iff. right. apply andb_true_iff. split.
        -- destruct Hex as [c Hc]. apply nonempty_iff. exists c.
           apply in_legal_moves. exact Hc.
        -- apply forallb_forall. intros c Hc. apply in_legal_moves in Hc.
           apply andb_true_iff. split.
           ++ apply negb_true_iff. apply Hno. exact Hc.
           ++ apply IH. apply Hfw. exact Hc.
Qed.

(** Reduction of the unbounded "no forced win" statements to one evaluation. *)
Theorem no_forced_win_by_evaluation : forall lines p b,
  wins_b lines p (length (legal_moves b)) b = false ->
  forall d, ~ forces_win lines p d b.
Proof.
  intros lines p b Hev d H.
  apply forces_win_cap in H. apply wins_b_spec in H. congruence.
Qed.

End MNKGame.
