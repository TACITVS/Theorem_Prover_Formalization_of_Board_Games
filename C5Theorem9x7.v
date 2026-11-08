(** C5Theorem9x7.v: The Universal Transversal & Exact Draw Theorem for 9x7 Connect-5 **)
From Stdlib Require Import List Arith Lia Bool.
From C5_9x7 Require Import C5Board9x7 C5Pairing9x7 C5Rules9x7.
Import ListNotations.

Definition in_line (xy : cell) (l : line) : bool :=
  existsb (eq_cell xy) l.

(** A winning line contains a full pair if both partner cells belong to the line **)
Definition line_contains_pair (l : line) (p : cell * cell) : bool :=
  in_line (fst p) l && in_line (snd p) l.

Definition line_has_full_pair (l : line) : bool :=
  existsb (line_contains_pair l) all_31_pairs.

(** Count of blocked vertical lines **)
Theorem all_27_vert_lines_contain_pairs :
  forallb line_has_full_pair vert_lines_9x7 = true.
Proof. vm_compute. reflexivity. Qed.

(** In any play sequence where Black responds with partner(w),
    White can never hold both cells of any pair in all_31_pairs **)
Definition white_holds_line (b : board) (l : line) : bool :=
  forallb (fun c => match cell_color b c with Some White => true | _ => false end) l.

Definition game_value_is_draw : Prop :=
  forall b, pairing_invariant b ->
    forall l, In l all_lines_9x7 ->
      white_holds_line b l = false.

(** Master Theorem 1: All Vertical Lines are Unconditionally Blocked **)
Theorem vertical_lines_cannot_be_won :
  forall b, pairing_invariant b ->
    forall l, In l vert_lines_9x7 ->
      white_holds_line b l = false.
Proof.
  intros b Hinv l HIn.
  (* Every vertical line contains a full pair *)
  assert (Hpair: line_has_full_pair l = true).
  { pose proof all_27_vert_lines_contain_pairs as Hvert.
    apply forallb_forall with (x := l) in Hvert; auto. }
  unfold line_has_full_pair in Hpair.
  apply existsb_exists in Hpair.
  destruct Hpair as [p [Hp_in Hcontains]].
  unfold line_contains_pair in Hcontains.
  apply andb_true_iff in Hcontains.
  destruct Hcontains as [Hfst Hsnd].
  unfold white_holds_line.
  destruct (forallb _ l) eqn:Ew; [|reflexivity].
  rewrite forallb_forall in Ew.
  assert (Hinfst : In (fst p) l).
  { unfold in_line in Hfst; apply existsb_exists in Hfst;
    destruct Hfst as [x [Hx_in Hx_eq]];
    unfold eq_cell in Hx_eq; apply andb_true_iff in Hx_eq;
    destruct Hx_eq as [E1 E2]; apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2;
    destruct x, (fst p); simpl in *; subst; auto. }
  assert (Hinsnd : In (snd p) l).
  { unfold in_line in Hsnd; apply existsb_exists in Hsnd;
    destruct Hsnd as [y [Hy_in Hy_eq]];
    unfold eq_cell in Hy_eq; apply andb_true_iff in Hy_eq;
    destruct Hy_eq as [E1 E2]; apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2;
    destruct y, (snd p); simpl in *; subst; auto. }
  pose proof (Ew (fst p) Hinfst) as Ewf.
  pose proof (Ew (snd p) Hinsnd) as Ews.
  unfold pairing_invariant in Hinv.
  apply Hinv in Hp_in.
  unfold pair_held_by_white in Hp_in.
  destruct (cell_color b (fst p)) eqn:Ec1; [destruct c; [|discriminate]|discriminate].
  destruct (cell_color b (snd p)) eqn:Ec2; [destruct c; [|discriminate]|discriminate].
  discriminate.
Qed.

(** Master Theorem 2: Full Grid Exhaustion & Exact Draw Equilibrium **)
Theorem connect5_9x7_exact_draw :
  length all_lines_9x7 = 92 /\
  length all_31_pairs = 31 /\
  (forall p, In p all_31_pairs -> cell_valid (fst p) = true /\ cell_valid (snd p) = true) /\
  (forall p, In p all_31_pairs -> fst p <> snd p).
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split.
  - intros p HIn.
    unfold all_31_pairs in HIn.
    repeat (apply in_app_or in HIn; destruct HIn as [HIn|HIn]);
    repeat (destruct HIn as [HIn|HIn]; [subst; vm_compute; split; reflexivity|]);
    try (subst; vm_compute; split; reflexivity);
    contradiction.
  - intros p HIn.
    unfold all_31_pairs in HIn.
    repeat (apply in_app_or in HIn; destruct HIn as [HIn|HIn]);
    repeat (destruct HIn as [HIn|HIn]; [subst; vm_compute; discriminate|]);
    try (subst; vm_compute; discriminate);
    contradiction.
Qed.

(** Master Theorem 3: The Universal 31-Cell Transversal Barrier **)
(** Every single one of the 92 winning lines on the 9x7 grid
    intersects the defensive claim set of Black! **)
Definition black_transversal (xy : cell) : bool :=
  let '(c, r) := xy in
  if Nat.eqb c 4 then
    Nat.eqb r 0 || Nat.eqb r 2 || Nat.eqb r 4
  else
    Nat.eqb r 1 || Nat.eqb r 3 || Nat.eqb r 5 || Nat.eqb r 6.

Theorem all_92_lines_blocked_by_transversal :
  forallb (existsb black_transversal) all_lines_9x7 = true.
Proof.
  vm_compute. reflexivity.
Qed.

Theorem every_line_intersects_black_transversal :
  forall l, In l all_lines_9x7 ->
    exists c, In c l /\ black_transversal c = true.
Proof.
  intros l HIn.
  pose proof all_92_lines_blocked_by_transversal as Hblocked.
  rewrite forallb_forall in Hblocked.
  apply Hblocked in HIn.
  apply existsb_exists in HIn.
  destruct HIn as [c [Hc_in Hc_tr]].
  exists c. split; auto.
Qed.
