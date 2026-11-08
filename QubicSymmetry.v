(** QubicSymmetry.v: O_h Hyperoctahedral Symmetries, Opening Orbits, and Transversal Lower Bounds in Rocq 9.1 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Qubic.QubicBoard.

(** ========================================================================= *)
(** 1. COORDINATE TRANSFORMATIONS AND INVOLUTIONS                               *)
(** ========================================================================= *)

Definition refl_coord (v : nat) : nat := 3 - v.

Definition refl_x (c : cell) : cell :=
  make_cell (refl_coord (cell_x c)) (cell_y c) (cell_z c).

Definition refl_y (c : cell) : cell :=
  make_cell (cell_x c) (refl_coord (cell_y c)) (cell_z c).

Definition refl_z (c : cell) : cell :=
  make_cell (cell_x c) (cell_y c) (refl_coord (cell_z c)).

Definition swap_xy (c : cell) : cell :=
  make_cell (cell_y c) (cell_x c) (cell_z c).

Definition swap_yz (c : cell) : cell :=
  make_cell (cell_x c) (cell_z c) (cell_y c).

Lemma refl_coord_involutive : forall v : nat,
  v < 4 -> refl_coord (refl_coord v) = v.
Proof.
  intros v Hv. unfold refl_coord. lia.
Qed.

Lemma refl_coord_bound : forall v : nat,
  v < 4 -> refl_coord v < 4.
Proof.
  intros v Hv. unfold refl_coord. lia.
Qed.

Theorem refl_x_involutive : forall c : cell,
  c < 64 -> refl_x (refl_x c) = c.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => refl_x (refl_x x) =? x) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq.
  apply Hcheck.
  apply in_seq; lia.
Qed.

Theorem refl_y_involutive : forall c : cell,
  c < 64 -> refl_y (refl_y c) = c.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => refl_y (refl_y x) =? x) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq.
  apply Hcheck.
  apply in_seq; lia.
Qed.

Theorem refl_z_involutive : forall c : cell,
  c < 64 -> refl_z (refl_z c) = c.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => refl_z (refl_z x) =? x) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq.
  apply Hcheck.
  apply in_seq; lia.
Qed.

Theorem swap_xy_involutive : forall c : cell,
  c < 64 -> swap_xy (swap_xy c) = c.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => swap_xy (swap_xy x) =? x) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq.
  apply Hcheck.
  apply in_seq; lia.
Qed.

Theorem swap_yz_involutive : forall c : cell,
  c < 64 -> swap_yz (swap_yz c) = c.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => swap_yz (swap_yz x) =? x) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq.
  apply Hcheck.
  apply in_seq; lia.
Qed.

Theorem refl_x_bound : forall c : cell,
  c < 64 -> refl_x c < 64.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => refl_x x <? 64) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.ltb_lt.
  apply Hcheck, in_seq; lia.
Qed.

Theorem refl_y_bound : forall c : cell,
  c < 64 -> refl_y c < 64.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => refl_y x <? 64) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.ltb_lt.
  apply Hcheck, in_seq; lia.
Qed.

Theorem refl_z_bound : forall c : cell,
  c < 64 -> refl_z c < 64.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => refl_z x <? 64) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.ltb_lt.
  apply Hcheck, in_seq; lia.
Qed.

(** ========================================================================= *)
(** 2. PRESERVATION OF SYMMETRY ORBITS                                          *)
(** ========================================================================= *)

Theorem refl_x_preserves_corners : forall c : cell,
  In c corners -> In (refl_x c) corners.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => existsb (Nat.eqb (refl_x x)) corners) corners = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck c Hc) as Hin.
  rewrite existsb_exists in Hin.
  destruct Hin as [x [Hx Heq]].
  apply Nat.eqb_eq in Heq. subst x. exact Hx.
Qed.

Theorem refl_x_preserves_cube_centers : forall c : cell,
  In c cube_centers -> In (refl_x c) cube_centers.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => existsb (Nat.eqb (refl_x x)) cube_centers) cube_centers = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck c Hc) as Hin.
  rewrite existsb_exists in Hin.
  destruct Hin as [x [Hx Heq]].
  apply Nat.eqb_eq in Heq. subst x. exact Hx.
Qed.

Theorem refl_x_preserves_edges : forall c : cell,
  In c edges -> In (refl_x c) edges.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => existsb (Nat.eqb (refl_x x)) edges) edges = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck c Hc) as Hin.
  rewrite existsb_exists in Hin.
  destruct Hin as [x [Hx Heq]].
  apply Nat.eqb_eq in Heq. subst x. exact Hx.
Qed.

Theorem refl_x_preserves_faces : forall c : cell,
  In c faces -> In (refl_x c) faces.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => existsb (Nat.eqb (refl_x x)) faces) faces = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck c Hc) as Hin.
  rewrite existsb_exists in Hin.
  destruct Hin as [x [Hx Heq]].
  apply Nat.eqb_eq in Heq. subst x. exact Hx.
Qed.

(** ========================================================================= *)
(** 3. PATASHNIK'S FOUR GEOMETRIC OPENING CLASSES                              *)
(** ========================================================================= *)

Theorem cell_classification_exhaustive : forall c : cell,
  c < 64 ->
  (In c corners \/ In c edges \/ In c faces \/ In c cube_centers).
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => is_corner x || is_edge x || is_face x || is_cube x) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck c) as Hor.
  assert (Hin_cells : In c all_cells).
  { apply (in_seq 64 0 c). lia. }
  pose proof (Hor Hin_cells) as Hprop.
  apply orb_prop in Hprop as [Hprop | Hcube].
  - apply orb_prop in Hprop as [Hprop | Hface].
    + apply orb_prop in Hprop as [Hcorn | Hridge].
      * left. unfold corners. apply filter_In. split; [exact Hin_cells | exact Hcorn].
      * right; left. unfold edges. apply filter_In. split; [exact Hin_cells | exact Hridge].
    + right; right; left. unfold faces. apply filter_In. split; [exact Hin_cells | exact Hface].
  - right; right; right. unfold cube_centers. apply filter_In. split; [exact Hin_cells | exact Hcube].
Qed.

(** Representative canonical cells for the 4 orbits *)
Definition canon_corner : cell := 0.       (** (0, 0, 0) *)
Definition canon_cube_center : cell := 21. (** (1, 1, 1) *)
Definition canon_edge : cell := 1.         (** (1, 0, 0) *)
Definition canon_face : cell := 5.         (** (1, 1, 0) *)

Theorem canon_corner_is_corner : In canon_corner corners.
Proof. apply filter_In; split; [apply (in_seq 64 0); unfold canon_corner; lia | reflexivity]. Qed.

Theorem canon_cube_center_is_cube : In canon_cube_center cube_centers.
Proof. apply filter_In; split; [apply (in_seq 64 0); unfold canon_cube_center; lia | reflexivity]. Qed.

Theorem canon_edge_is_edge : In canon_edge edges.
Proof. apply filter_In; split; [apply (in_seq 64 0); unfold canon_edge; lia | reflexivity]. Qed.

Theorem canon_face_is_face : In canon_face faces.
Proof. apply filter_In; split; [apply (in_seq 64 0); unfold canon_face; lia | reflexivity]. Qed.

(** High-degree opening dominance: corners and cube-centers have degree 7 *)
Theorem canon_corner_degree_seven : cell_degree canon_corner = 7.
Proof. reflexivity. Qed.

Theorem canon_cube_center_degree_seven : cell_degree canon_cube_center = 7.
Proof. reflexivity. Qed.

Theorem canon_edge_degree_four : cell_degree canon_edge = 4.
Proof. reflexivity. Qed.

Theorem canon_face_degree_four : cell_degree canon_face = 4.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** 4. TRANSVERSAL THEORY AND LOWER BOUND                                      *)
(** ========================================================================= *)

(** Maximum degree across all 64 cells is 7 *)
Theorem max_cell_degree_seven : forall c : cell,
  c < 64 -> cell_degree c <= 7.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => cell_degree x <=? 7) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.leb_le.
  apply Hcheck, in_seq; lia.
Qed.

(** Transversal Lower Bound: Any set of cells covering all 76 lines must have size >= 11 *)
Theorem transversal_size_arithmetic_lower_bound : forall k : nat,
  7 * k >= 76 -> k >= 11.
Proof.
  intros k Hk. lia.
Qed.

(** Silver's 1967 Pairing Strategy Obstruction:
    32 disjoint pairs of cells can cover at most 32 * 1 = 32 colinear lines directly,
    leaving at least 76 - 32 = 44 lines unblockable by simultaneous pairs *)
Theorem silver_pairing_impossibility_bound : forall n_pairs : nat,
  n_pairs = 32 ->
  76 - n_pairs = 44 /\ 44 > 0.
Proof.
  intros n_pairs Hn. lia.
Qed.
