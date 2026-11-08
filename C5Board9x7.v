(** C5Board9x7.v: Board Geometry & 92 Winning Lines for 9x7 Connect-5 **)
From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.

Definition W : nat := 9.
Definition H : nat := 7.
Definition K : nat := 5.

Definition cell : Type := (nat * nat)%type.
Definition eq_cell (c1 c2 : cell) : bool :=
  Nat.eqb (fst c1) (fst c2) && Nat.eqb (snd c1) (snd c2).

Definition cell_valid (c : cell) : bool :=
  (fst c <? W) && (snd c <? H).

Definition line : Type := list cell.

(** 1. Horizontal Lines (35 lines: 5 spans per row x 7 rows) **)
Definition gen_horiz_line (c r : nat) : line :=
  [(c, r); (c + 1, r); (c + 2, r); (c + 3, r); (c + 4, r)].

Definition horiz_lines_row (r : nat) : list line :=
  [gen_horiz_line 0 r; gen_horiz_line 1 r; gen_horiz_line 2 r;
   gen_horiz_line 3 r; gen_horiz_line 4 r].

Definition horiz_lines_9x7 : list line :=
  horiz_lines_row 0 ++ horiz_lines_row 1 ++ horiz_lines_row 2 ++
  horiz_lines_row 3 ++ horiz_lines_row 4 ++ horiz_lines_row 5 ++
  horiz_lines_row 6.

(** 2. Vertical Lines (27 lines: 3 spans per column x 9 columns) **)
Definition gen_vert_line (c r : nat) : line :=
  [(c, r); (c, r + 1); (c, r + 2); (c, r + 3); (c, r + 4)].

Definition vert_lines_col (c : nat) : list line :=
  [gen_vert_line c 0; gen_vert_line c 1; gen_vert_line c 2].

Definition vert_lines_9x7 : list line :=
  vert_lines_col 0 ++ vert_lines_col 1 ++ vert_lines_col 2 ++
  vert_lines_col 3 ++ vert_lines_col 4 ++ vert_lines_col 5 ++
  vert_lines_col 6 ++ vert_lines_col 7 ++ vert_lines_col 8.

(** 3. Positive Diagonal Lines (slope +1, 15 lines: 5 x 3) **)
Definition gen_pos_diag (c r : nat) : line :=
  [(c, r); (c + 1, r + 1); (c + 2, r + 2); (c + 3, r + 3); (c + 4, r + 4)].

Definition pos_diag_lines_row (r : nat) : list line :=
  [gen_pos_diag 0 r; gen_pos_diag 1 r; gen_pos_diag 2 r;
   gen_pos_diag 3 r; gen_pos_diag 4 r].

Definition pos_diag_lines_9x7 : list line :=
  pos_diag_lines_row 0 ++ pos_diag_lines_row 1 ++ pos_diag_lines_row 2.

(** 4. Negative Diagonal Lines (slope -1, 15 lines: 5 x 3) **)
Definition gen_neg_diag (c r : nat) : line :=
  [(c, r); (c + 1, r - 1); (c + 2, r - 2); (c + 3, r - 3); (c + 4, r - 4)].

Definition neg_diag_lines_row (r : nat) : list line :=
  [gen_neg_diag 0 r; gen_neg_diag 1 r; gen_neg_diag 2 r;
   gen_neg_diag 3 r; gen_neg_diag 4 r].

Definition neg_diag_lines_9x7 : list line :=
  neg_diag_lines_row 4 ++ neg_diag_lines_row 5 ++ neg_diag_lines_row 6.

(** Total Winning Lines on 9x7 Grid **)
Definition all_lines_9x7 : list line :=
  horiz_lines_9x7 ++ vert_lines_9x7 ++ pos_diag_lines_9x7 ++ neg_diag_lines_9x7.

(** Theorems: Exact Line Counts & Geometric Invariants **)
Theorem horiz_lines_count : length horiz_lines_9x7 = 35.
Proof. vm_compute. reflexivity. Qed.

Theorem vert_lines_count : length vert_lines_9x7 = 27.
Proof. vm_compute. reflexivity. Qed.

Theorem pos_diag_lines_count : length pos_diag_lines_9x7 = 15.
Proof. vm_compute. reflexivity. Qed.

Theorem neg_diag_lines_count : length neg_diag_lines_9x7 = 15.
Proof. vm_compute. reflexivity. Qed.

Theorem total_lines_9x7_count : length all_lines_9x7 = 92.
Proof. vm_compute. reflexivity. Qed.

Theorem all_lines_length_5 :
  forall l, In l all_lines_9x7 -> length l = 5.
Proof.
  intros l HIn.
  unfold all_lines_9x7 in HIn.
  repeat (apply in_app_or in HIn; destruct HIn as [HIn|HIn]);
  repeat (destruct HIn as [HIn|HIn]; [subst; vm_compute; reflexivity|]);
  try (subst; vm_compute; reflexivity);
  contradiction.
Qed.

(** Reflection Symmetry across Center Axis: c <-> 8 - c **)
Definition refl_c (c : nat) : nat := 8 - c.
Definition refl_cell (xy : cell) : cell := (refl_c (fst xy), snd xy).

Theorem refl_c_involutive : forall c, c < 9 -> refl_c (refl_c c) = c.
Proof.
  intros c Hc. unfold refl_c. lia.
Qed.

Theorem refl_cell_involutive : forall xy, fst xy < 9 -> refl_cell (refl_cell xy) = xy.
Proof.
  intros [c r] Hc. simpl in *.
  unfold refl_cell. simpl.
  rewrite refl_c_involutive; auto.
Qed.

Theorem center_axis_fixed : refl_c 4 = 4.
Proof. reflexivity. Qed.
