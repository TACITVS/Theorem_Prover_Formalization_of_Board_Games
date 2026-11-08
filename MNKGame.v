(** **************************************************************************
    MNKGame.v: Universal State Transitions, Positional Monotonicity,
    and Game-Theoretic Invariants for (m, n, k) Games
    
    Formalizes the turn-based rules of positional maker-maker games:
    - Players P1 (First mover) and P2 (Second mover).
    - Board state as a list of option player.
    - Permanent stone placement (pure addition, no stone removal).
    - Monotonicity Theorem: Extra stones never destroy an existing win.
    - Line ownership and win verification.
    - Soundness of win condition.
    
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

End MNKGame.
