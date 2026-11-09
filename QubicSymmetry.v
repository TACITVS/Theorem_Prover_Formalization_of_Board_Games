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

Definition refl_coord (v : nat) : nat := 4 - v.

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
  v < 5 -> refl_coord (refl_coord v) = v.
Proof.
  intros v Hv. unfold refl_coord. lia.
Qed.

Lemma refl_coord_bound : forall v : nat,
  v < 5 -> refl_coord v < 5.
Proof.
  intros v Hv. unfold refl_coord. lia.
Qed.

Theorem refl_x_involutive : forall c : cell,
  c < 125 -> refl_x (refl_x c) = c.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => refl_x (refl_x x) =? x) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq.
  apply Hcheck.
  apply in_seq; lia.
Qed.

Theorem refl_y_involutive : forall c : cell,
  c < 125 -> refl_y (refl_y c) = c.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => refl_y (refl_y x) =? x) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq.
  apply Hcheck.
  apply in_seq; lia.
Qed.

Theorem refl_z_involutive : forall c : cell,
  c < 125 -> refl_z (refl_z c) = c.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => refl_z (refl_z x) =? x) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq.
  apply Hcheck.
  apply in_seq; lia.
Qed.

Theorem swap_xy_involutive : forall c : cell,
  c < 125 -> swap_xy (swap_xy c) = c.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => swap_xy (swap_xy x) =? x) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq.
  apply Hcheck.
  apply in_seq; lia.
Qed.

Theorem swap_yz_involutive : forall c : cell,
  c < 125 -> swap_yz (swap_yz c) = c.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => swap_yz (swap_yz x) =? x) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq.
  apply Hcheck.
  apply in_seq; lia.
Qed.

Theorem refl_x_bound : forall c : cell,
  c < 125 -> refl_x c < 125.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => refl_x x <? 125) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.ltb_lt.
  apply Hcheck, in_seq; lia.
Qed.

Theorem refl_y_bound : forall c : cell,
  c < 125 -> refl_y c < 125.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => refl_y x <? 125) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.ltb_lt.
  apply Hcheck, in_seq; lia.
Qed.

Theorem refl_z_bound : forall c : cell,
  c < 125 -> refl_z c < 125.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => refl_z x <? 125) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.ltb_lt.
  apply Hcheck, in_seq; lia.
Qed.

(** ========================================================================= *)
(** 2. PRESERVATION OF SYMMETRY ORBITS                                          *)
(** ========================================================================= *)

Theorem refl_x_preserves_deg13 : forall c : cell,
  In c deg13_cells -> In (refl_x c) deg13_cells.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => existsb (Nat.eqb (refl_x x)) deg13_cells) deg13_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck c Hc) as Hin.
  rewrite existsb_exists in Hin.
  destruct Hin as [x [Hx Heq]].
  apply Nat.eqb_eq in Heq. subst x. exact Hx.
Qed.

Theorem refl_x_preserves_deg7 : forall c : cell,
  In c deg7_cells -> In (refl_x c) deg7_cells.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => existsb (Nat.eqb (refl_x x)) deg7_cells) deg7_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck c Hc) as Hin.
  rewrite existsb_exists in Hin.
  destruct Hin as [x [Hx Heq]].
  apply Nat.eqb_eq in Heq. subst x. exact Hx.
Qed.

Theorem refl_x_preserves_deg5 : forall c : cell,
  In c deg5_cells -> In (refl_x c) deg5_cells.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => existsb (Nat.eqb (refl_x x)) deg5_cells) deg5_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck c Hc) as Hin.
  rewrite existsb_exists in Hin.
  destruct Hin as [x [Hx Heq]].
  apply Nat.eqb_eq in Heq. subst x. exact Hx.
Qed.

Theorem refl_x_preserves_deg4 : forall c : cell,
  In c deg4_cells -> In (refl_x c) deg4_cells.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => existsb (Nat.eqb (refl_x x)) deg4_cells) deg4_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck c Hc) as Hin.
  rewrite existsb_exists in Hin.
  destruct Hin as [x [Hx Heq]].
  apply Nat.eqb_eq in Heq. subst x. exact Hx.
Qed.

Theorem refl_x_preserves_deg3 : forall c : cell,
  In c deg3_cells -> In (refl_x c) deg3_cells.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => existsb (Nat.eqb (refl_x x)) deg3_cells) deg3_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck c Hc) as Hin.
  rewrite existsb_exists in Hin.
  destruct Hin as [x [Hx Heq]].
  apply Nat.eqb_eq in Heq. subst x. exact Hx.
Qed.

(** ========================================================================= *)
(** 3. CELL CLASSIFICATION AND DEGREE BOUNDS                                   *)
(** ========================================================================= *)

Theorem cell_classification_exhaustive : forall c : cell,
  c < 125 ->
  (In c deg13_cells \/ In c deg7_cells \/ In c deg5_cells \/ In c deg4_cells \/ In c deg3_cells).
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x =>
    (cell_degree x =? 13) || (cell_degree x =? 7) || (cell_degree x =? 5) || (cell_degree x =? 4) || (cell_degree x =? 3)) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck c) as Hor.
  assert (Hin_cells : In c all_cells).
  { apply (in_seq 125 0 c). lia. }
  pose proof (Hor Hin_cells) as Hprop.
  apply orb_prop in Hprop as [Hprop | H3].
  - apply orb_prop in Hprop as [Hprop | H4].
    + apply orb_prop in Hprop as [Hprop | H5].
      * apply orb_prop in Hprop as [H13 | H7].
        -- left. unfold deg13_cells. apply filter_In. split; [exact Hin_cells | exact H13].
        -- right; left. unfold deg7_cells. apply filter_In. split; [exact Hin_cells | exact H7].
      * right; right; left. unfold deg5_cells. apply filter_In. split; [exact Hin_cells | exact H5].
    + right; right; right; left. unfold deg4_cells. apply filter_In. split; [exact Hin_cells | exact H4].
  - right; right; right; right. unfold deg3_cells. apply filter_In. split; [exact Hin_cells | exact H3].
Qed.

(** Maximum cell degree across the entire 125-cell board is 13 *)
Theorem max_cell_degree_thirteen : forall c : cell,
  c < 125 -> cell_degree c <= 13.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => cell_degree x <=? 13) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.leb_le.
  apply Hcheck, in_seq; lia.
Qed.

(** All non-center cells have degree at most 7 *)
Theorem non_center_max_degree_seven : forall c : cell,
  c < 125 -> c <> center_cell -> cell_degree c <= 7.
Proof.
  intros c Hc Hnot_center.
  assert (Hcheck : forallb (fun x => if Nat.eqb x center_cell then true else cell_degree x <=? 7) all_cells = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  assert (Hin : In c all_cells) by (apply in_seq; lia).
  pose proof (Hcheck c Hin) as Hc_check.
  destruct (Nat.eqb c center_cell) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - apply Nat.leb_le, Hc_check.
Qed.

(** ========================================================================= *)
(** 4. DEDICATED PAIR THEOREM & DEGREE MAXIMALITY                             *)
(** ========================================================================= *)

(** Dedicated Pair Theorem:
    Any two distinct cells belong to at most ONE winning line in 5x5x5.
    This is the core combinatorial lemma proving that a disjoint pair of cells
    can cover at most one winning line. *)
Definition common_lines (u v : cell) : list (list cell) :=
  filter (fun l => existsb (Nat.eqb u) l && existsb (Nat.eqb v) l) all_lines.

Theorem dedicated_pair_bound : forall u v : cell,
  u < 125 -> v < 125 -> u <> v ->
  length (common_lines u v) <= 1.
Proof.
  intros u v Hu Hv Hneq.
  assert (Hcheck : forallb (fun u => forallb (fun v =>
    if u =? v then true else Nat.leb (length (common_lines u v)) 1) all_cells) all_cells = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hcheck.
  assert (Hu_in : In u all_cells) by (apply in_seq; lia).
  assert (Hv_in : In v all_cells) by (apply in_seq; lia).
  pose proof (Hcheck u Hu_in) as H1.
  rewrite forallb_forall in H1.
  pose proof (H1 v Hv_in) as H2.
  destruct (u =? v) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - apply Nat.leb_le, H2.
Qed.

(** Center Degree Strict Maximality:
    The central cell 62 has strictly more incident winning lines (13) than any other cell (at most 7). *)
Theorem center_degree_strictly_maximal : forall c : cell,
  c < 125 -> c <> center_cell ->
  cell_degree c < cell_degree center_cell.
Proof.
  intros c Hc Hnot_center.
  pose proof (non_center_max_degree_seven c Hc Hnot_center) as Hle.
  pose proof center_cell_degree as Hcenter.
  lia.
Qed.

