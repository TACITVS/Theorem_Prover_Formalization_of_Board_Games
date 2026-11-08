(**
  C4Board.v: Geometric Foundations of Classic 7x6 Connect-Four (k = 4)
  Formalized in Rocq 9.1 (Calculus of Inductive Constructions).
  Strict Zero-Axiom Standard: 100% Closed under the global context.
*)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.

(** Board Dimensions *)
Definition W : nat := 7.
Definition H : nat := 6.
Definition K : nat := 4.

(** Total board cell count *)
Theorem board_cells_count : W * H = 42.
Proof. reflexivity. Qed.

(** Point representation: (column, row) *)
Definition point : Type := nat * nat.

Definition pt_eq (p1 p2 : point) : bool :=
  match p1, p2 with
  | (c1, r1), (c2, r2) => (c1 =? c2) && (r1 =? r2)
  end.

Theorem pt_eq_refl : forall p, pt_eq p p = true.
Proof.
  destruct p as [c r]. unfold pt_eq.
  rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

(** In-bounds check *)
Definition in_bounds (p : point) : bool :=
  match p with
  | (c, r) => (c <? W) && (r <? H)
  end.

(** Winning Line Definitions (Length K = 4) *)
Definition line : Type := list point.

(** 1. Horizontal Lines: 4 in a row horizontally *)
Definition horiz_line (c0 r : nat) : line :=
  [(c0, r); (c0 + 1, r); (c0 + 2, r); (c0 + 3, r)].

Definition horiz_lines : list line :=
  flat_map (fun r =>
    map (fun c0 => horiz_line c0 r) [0; 1; 2; 3]
  ) [0; 1; 2; 3; 4; 5].

Theorem horiz_lines_length : length horiz_lines = 24.
Proof. reflexivity. Qed.

(** 2. Vertical Lines: 4 in a row vertically *)
Definition vert_line (c r0 : nat) : line :=
  [(c, r0); (c, r0 + 1); (c, r0 + 2); (c, r0 + 3)].

Definition vert_lines : list line :=
  flat_map (fun c =>
    map (fun r0 => vert_line c r0) [0; 1; 2]
  ) [0; 1; 2; 3; 4; 5; 6].

Theorem vert_lines_length : length vert_lines = 21.
Proof. reflexivity. Qed.

(** 3. Positive Diagonals (slope +1): (c0 + i, r0 + i) *)
Definition pos_diag_line (c0 r0 : nat) : line :=
  [(c0, r0); (c0 + 1, r0 + 1); (c0 + 2, r0 + 2); (c0 + 3, r0 + 3)].

Definition pos_diag_lines : list line :=
  flat_map (fun r0 =>
    map (fun c0 => pos_diag_line c0 r0) [0; 1; 2; 3]
  ) [0; 1; 2].

Theorem pos_diag_lines_length : length pos_diag_lines = 12.
Proof. reflexivity. Qed.

(** 4. Negative Diagonals (slope -1): (c0 + i, r0 + 3 - i) *)
Definition neg_diag_line (c0 r0 : nat) : line :=
  [(c0, r0 + 3); (c0 + 1, r0 + 2); (c0 + 2, r0 + 1); (c0 + 3, r0)].

Definition neg_diag_lines : list line :=
  flat_map (fun r0 =>
    map (fun c0 => neg_diag_line c0 r0) [0; 1; 2; 3]
  ) [0; 1; 2].

Theorem neg_diag_lines_length : length neg_diag_lines = 12.
Proof. reflexivity. Qed.

(** Complete set of 69 winning lines *)
Definition all_lines : list line :=
  horiz_lines ++ vert_lines ++ pos_diag_lines ++ neg_diag_lines.

Theorem all_lines_length : length all_lines = 69.
Proof. reflexivity. Qed.

(** Every winning line has exactly 4 cells *)
Theorem all_lines_length_4 :
  forall l, In l all_lines -> length l = 4.
Proof.
  intros l Hl.
  unfold all_lines in Hl.
  apply in_app_or in Hl. destruct Hl as [Hh | Hrest].
  - unfold horiz_lines in Hh.
    apply in_flat_map in Hh. destruct Hh as [r [Hr Hc]].
    apply in_map_iff in Hc. destruct Hc as [c0 [Heq Hin]].
    subst l. reflexivity.
  - apply in_app_or in Hrest. destruct Hrest as [Hv | Hdiag].
    + unfold vert_lines in Hv.
      apply in_flat_map in Hv. destruct Hv as [c [Hc Hr]].
      apply in_map_iff in Hr. destruct Hr as [r0 [Heq Hin]].
      subst l. reflexivity.
    + apply in_app_or in Hdiag. destruct Hdiag as [Hp | Hn].
      * unfold pos_diag_lines in Hp.
        apply in_flat_map in Hp. destruct Hp as [r0 [Hr Hc]].
        apply in_map_iff in Hc. destruct Hc as [c0 [Heq Hin]].
        subst l. reflexivity.
      * unfold neg_diag_lines in Hn.
        apply in_flat_map in Hn. destruct Hn as [r0 [Hr Hc]].
        apply in_map_iff in Hc. destruct Hc as [c0 [Heq Hin]].
        subst l. reflexivity.
Qed.
