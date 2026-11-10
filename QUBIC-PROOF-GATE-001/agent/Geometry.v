(** Independent geometric characterization of the hash-pinned winning lines.
    Each coordinate is constant, increasing 0..4, or decreasing 4..0;
    at least one coordinate must vary. Cell encoding: x + 5*y + 25*z.
    Reversing a line does not change its winning cells. *)
From Stdlib Require Import List Arith Bool Lia.
From QubicTrusted Require Import Rules.
Import ListNotations.

Definition coordinate (mode t : nat) : nat :=
  if mode <? 5 then mode else if mode =? 5 then t else 4 - t.

Definition coordinate_line (x y z : nat) : list cell :=
  map (fun t => coordinate x t + 5 * coordinate y t + 25 * coordinate z t)
    (seq 0 5).

Definition geometric_line (l : list cell) : Prop :=
  exists x y z, x < 7 /\ y < 7 /\ z < 7 /\
    (5 <= x \/ 5 <= y \/ 5 <= z) /\ l = coordinate_line x y z.

Definition mode_triples : list (nat * nat * nat) :=
  flat_map (fun x => flat_map (fun y => map (fun z => (x, y, z)) (seq 0 7))
    (seq 0 7)) (seq 0 7).

Definition varies (m : nat * nat * nat) : bool :=
  let '(x, y, z) := m in negb ((x <? 5) && (y <? 5) && (z <? 5)).

Definition generated_lines : list (list cell) :=
  map (fun '(x, y, z) => coordinate_line x y z) (filter varies mode_triples).

Lemma mode_triples_spec : forall x y z,
  In (x, y, z) mode_triples <-> x < 7 /\ y < 7 /\ z < 7.
Proof.
  intros x y z. unfold mode_triples. split.
  - intros H. apply in_flat_map in H as [a [Ha H]].
    apply in_flat_map in H as [b [Hb H]].
    apply in_map_iff in H as [c [Heq Hc]]. inversion Heq; subst.
    apply in_seq in Ha. apply in_seq in Hb. apply in_seq in Hc. lia.
  - intros [Hx [Hy Hz]]. apply in_flat_map. exists x. split.
    + apply in_seq. lia.
    + apply in_flat_map. exists y. split.
      * apply in_seq. lia.
      * apply in_map. apply in_seq. lia.
Qed.

Lemma varies_spec : forall x y z,
  varies (x, y, z) = true <-> 5 <= x \/ 5 <= y \/ 5 <= z.
Proof.
  intros. unfold varies.
  rewrite negb_true_iff, !andb_false_iff, !Nat.ltb_ge. tauto.
Qed.

Lemma generated_lines_spec : forall l,
  In l generated_lines <-> geometric_line l.
Proof.
  intros l. unfold generated_lines, geometric_line. rewrite in_map_iff. split.
  - intros [[[x y] z] [Heq Hin]]. apply filter_In in Hin as [Hin Hvar].
    apply mode_triples_spec in Hin as [Hx [Hy Hz]].
    apply varies_spec in Hvar. exists x, y, z. auto.
  - intros [x [y [z [Hx [Hy [Hz [Hvar Heq]]]]]]].
    exists (x, y, z). split; [symmetry; exact Heq|].
    apply filter_In. split; [apply mode_triples_spec; auto|apply varies_spec; auto].
Qed.

Fixpoint line_eqb (a b : list cell) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => (x =? y) && line_eqb xs ys
  | _, _ => false
  end.

Lemma line_eqb_spec : forall a b, line_eqb a b = true <-> a = b.
Proof.
  induction a as [|x xs IH]; intros [|y ys]; cbn; try (split; congruence).
  rewrite andb_true_iff, Nat.eqb_eq, IH. split; [intros [-> ->]; reflexivity|].
  intros H. inversion H. auto.
Qed.

Definition contains_line (l : list cell) (ls : list (list cell)) : bool :=
  existsb (line_eqb l) ls.

Lemma contains_line_spec : forall l ls, contains_line l ls = true <-> In l ls.
Proof.
  intros l ls. unfold contains_line. rewrite existsb_exists. split.
  - intros [d [Hd Heq]]. apply line_eqb_spec in Heq. subst. exact Hd.
  - intros H. exists l. split; [exact H|apply line_eqb_spec; reflexivity].
Qed.

Definition oriented_lines := all_lines ++ map (@rev cell) all_lines.

Lemma oriented_lines_spec : forall l,
  In l oriented_lines <-> In l all_lines \/ In (rev l) all_lines.
Proof.
  intros l. unfold oriented_lines. rewrite in_app_iff. split.
  - intros [H|H]; [auto|]. right. apply in_map_iff in H as [d [Hd Hin]].
    subst l. rewrite rev_involutive. exact Hin.
  - intros [H|H]; [auto|]. right. apply in_map_iff.
    exists (rev l). rewrite rev_involutive. auto.
Qed.

Lemma geometry_forward_check :
  forallb (fun l => contains_line l oriented_lines) generated_lines = true.
Proof. vm_compute. reflexivity. Qed.

Lemma geometry_backward_check :
  forallb (fun l => contains_line l generated_lines) oriented_lines = true.
Proof. vm_compute. reflexivity. Qed.

Theorem locked_lines_are_exactly_standard_lines : forall l,
  geometric_line l <-> In l all_lines \/ In (rev l) all_lines.
Proof.
  intros l. rewrite <- generated_lines_spec, <- oriented_lines_spec. split; intro Hin.
  - pose proof geometry_forward_check as H.
    apply forallb_forall with (x := l) in H; [apply contains_line_spec; exact H|exact Hin].
  - pose proof geometry_backward_check as H.
    apply forallb_forall with (x := l) in H; [apply contains_line_spec; exact H|exact Hin].
Qed.

Fixpoint distinct_lines (ls : list (list cell)) : bool :=
  match ls with
  | [] => true
  | l :: rest => negb (contains_line l rest) && distinct_lines rest
  end.

Lemma distinct_lines_sound : forall ls, distinct_lines ls = true -> NoDup ls.
Proof.
  induction ls as [|l ls IH]; cbn; intros H; [constructor|].
  apply andb_true_iff in H as [Hnot Hrest]. apply negb_true_iff in Hnot.
  constructor; [|apply IH; exact Hrest].
  intros Hin. apply contains_line_spec in Hin. congruence.
Qed.

Theorem locked_lines_distinct : NoDup all_lines.
Proof. apply distinct_lines_sound. vm_compute. reflexivity. Qed.

Theorem oriented_standard_line_count : length generated_lines = 218.
Proof. reflexivity. Qed.

Print Assumptions locked_lines_are_exactly_standard_lines.
Print Assumptions locked_lines_distinct.
Print Assumptions oriented_standard_line_count.
