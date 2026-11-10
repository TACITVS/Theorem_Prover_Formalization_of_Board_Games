(** Research 026: arithmetic core of the regional Erdos-Selfridge barrier.

    A region with [n] free cells carries [a_s] line fragments of size [s]
    for s = 2..5.  Two hypotheses are extracted from the game in README.md:

    - budget: sum of 2^-s over the fragments is < 1/2, i.e.
        8 a2 + 4 a3 + 2 a4 + a5 <= 15;
    - pairs: distinct fragments share at most one cell, so their cell pairs
      are disjoint: a2 + 3 a3 + 6 a4 + 10 a5 <= n (n-1) / 2.

    Conclusion: 6 * (number of fragments) <= 5 * n.  Summed over disjoint
    regions this gives 6 * lines <= 5 * cells, which fails for 109 lines on
    125 cells.  This file proves only the arithmetic; the link to the game
    is the pen-and-paper argument in README.md. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.

Record region := mk_region { a2 : nat; a3 : nat; a4 : nat; a5 : nat; cells : nat }.

Definition fragments (r : region) : nat := a2 r + a3 r + a4 r + a5 r.

Definition admissible (r : region) : Prop :=
  8 * a2 r + 4 * a3 r + 2 * a4 r + a5 r <= 15 /\
  2 * (a2 r + 3 * a3 r + 6 * a4 r + 10 * a5 r) <= cells r * (cells r - 1).

Definition ok (x2 x3 x4 x5 n : nat) : bool :=
  implb ((8 * x2 + 4 * x3 + 2 * x4 + x5 <=? 15) &&
         (2 * (x2 + 3 * x3 + 6 * x4 + 10 * x5) <=? n * (n - 1)))
        (6 * (x2 + x3 + x4 + x5) <=? 5 * n).

Definition all_ok : bool :=
  forallb (fun x2 => forallb (fun x3 => forallb (fun x4 => forallb (fun x5 =>
  forallb (fun n => ok x2 x3 x4 x5 n) (seq 0 18)) (seq 0 16)) (seq 0 8)) (seq 0 4)) (seq 0 2).

Lemma all_ok_true : all_ok = true.
Proof. vm_compute. reflexivity. Qed.

Theorem region_bound : forall r, admissible r -> 6 * fragments r <= 5 * cells r.
Proof.
  intros [x2 x3 x4 x5 n] [Hb Hp]; unfold fragments; simpl in *.
  destruct (le_lt_dec 18 n) as [Hn | Hn]; [lia|].
  pose proof all_ok_true as H. unfold all_ok in H.
  rewrite forallb_forall in H. specialize (H x2 ltac:(apply in_seq; lia)).
  rewrite forallb_forall in H. specialize (H x3 ltac:(apply in_seq; lia)).
  rewrite forallb_forall in H. specialize (H x4 ltac:(apply in_seq; lia)).
  rewrite forallb_forall in H. specialize (H x5 ltac:(apply in_seq; lia)).
  rewrite forallb_forall in H. specialize (H n ltac:(apply in_seq; lia)).
  unfold ok in H.
  assert (E1 : (8 * x2 + 4 * x3 + 2 * x4 + x5 <=? 15) = true) by (apply Nat.leb_le; lia).
  assert (E2 : (2 * (x2 + 3 * x3 + 6 * x4 + 10 * x5) <=? n * (n - 1)) = true)
    by (apply Nat.leb_le; exact Hp).
  rewrite E1, E2 in H. simpl in H. apply Nat.leb_le in H. exact H.
Qed.

Definition total (f : region -> nat) (rs : list region) : nat :=
  fold_right (fun r acc => f r + acc) 0 rs.

Theorem decomposition_bound : forall rs,
  Forall admissible rs -> 6 * total fragments rs <= 5 * total cells rs.
Proof.
  induction 1 as [| r rs Hr _ IH]; simpl; [lia|].
  pose proof (region_bound r Hr). lia.
Qed.

(** No admissible decomposition accounts for all 109 lines inside 125 cells. *)
Theorem empty_board_barrier : forall rs,
  Forall admissible rs -> total cells rs <= 125 -> total fragments rs <> 109.
Proof.
  intros rs Hrs Hc Hl. pose proof (decomposition_bound rs Hrs). lia.
Qed.

Print Assumptions region_bound.
Print Assumptions decomposition_bound.
Print Assumptions empty_board_barrier.
