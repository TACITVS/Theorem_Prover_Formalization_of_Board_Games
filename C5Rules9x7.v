(** C5Rules9x7.v: Game Dynamics & Pairing Strategy Invariants for 9x7 Connect-5 **)
From Stdlib Require Import List Arith Lia Bool.
From C5_9x7 Require Import C5Board9x7 C5Pairing9x7.
Import ListNotations.

Inductive Color : Type := White | Black.

Definition other_color (c : Color) : Color :=
  match c with
  | White => Black
  | Black => White
  end.

Definition eq_color (c1 c2 : Color) : bool :=
  match c1, c2 with
  | White, White => true
  | Black, Black => true
  | _, _ => false
  end.

Definition board : Type := list (cell * Color).

Fixpoint cell_color (b : board) (xy : cell) : option Color :=
  match b with
  | [] => None
  | (c, col) :: tl =>
      if eq_cell c xy then Some col else cell_color tl xy
  end.

Fixpoint col_height (b : board) (c : nat) : nat :=
  match b with
  | [] => 0
  | ((col, _), _) :: tl =>
      if Nat.eqb col c then S (col_height tl c) else col_height tl c
  end.

(** The Pairing Defensive Invariant:
    For every pair (c1, c2) in all_31_pairs,
    White never owns both cells of the pair! **)
Definition pair_held_by_white (b : board) (p : cell * cell) : bool :=
  match cell_color b (fst p), cell_color b (snd p) with
  | Some White, Some White => true
  | _, _ => false
  end.

Definition pairing_invariant (b : board) : Prop :=
  forall p, In p all_31_pairs ->
    pair_held_by_white b p = false.

(** Theorem: Empty Board Satisfies the Pairing Invariant **)
Theorem empty_board_invariant : pairing_invariant [].
Proof.
  intros p HIn.
  unfold pair_held_by_white, cell_color.
  destruct (fst p), (snd p).
  reflexivity.
Qed.

(** Strategy Response Function:
    Given White's move w, Black's deterministic reply is black_reply w **)
Definition black_reply (w : cell) : cell :=
  match partner w with
  | Some b => b
  | None => (4, 1) (* If White plays (4, 0), Black plays (4, 1) *)
  end.

(** Theorem: Black Reply to Opening Move (4, 0) is (4, 1) **)
Theorem black_reply_to_opening : black_reply (4, 0) = (4, 1).
Proof.
  unfold black_reply.
  rewrite opening_move_unpaired.
  reflexivity.
Qed.

(** Theorem: Black Reply to Any Other Cell is its Partner **)
Theorem black_reply_partner :
  forall c r p,
    partner (c, r) = Some p ->
    black_reply (c, r) = p.
Proof.
  intros c r p Hpart.
  unfold black_reply.
  rewrite Hpart.
  reflexivity.
Qed.

(** Theorem: Black Reply is Always Strictly Distinct from White's Move **)
Theorem black_reply_distinct :
  forall w, cell_valid w = true -> black_reply w <> w.
Proof.
  intros [c r] Hval Heq.
  unfold black_reply in Heq.
  destruct (partner (c, r)) eqn:Hpart.
  - apply partner_distinct in Hpart.
    symmetry in Heq. contradiction.
  - unfold cell_valid in Hval.
    apply andb_true_iff in Hval. destruct Hval as [Hc Hr].
    apply Nat.ltb_lt in Hc. apply Nat.ltb_lt in Hr.
    apply partner_none_is_4_0 in Hpart; auto.
    inversion Hpart; subst.
    inversion Heq.
Qed.
