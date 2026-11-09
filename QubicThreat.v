(** QubicThreat.v: Threat Spaces, Linear Hypergraph Intersection, and Opening Dominance in Rocq 9.1 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Qubic.QubicBoard.
Require Import Qubic.QubicSymmetry.

(** ========================================================================= *)
(** 1. GAME STATE AND LINE OCCUPANCY                                           *)
(** ========================================================================= *)

Inductive Color : Set :=
  | White : Color
  | Black : Color.

Definition other_color (c : Color) : Color :=
  match c with
  | White => Black
  | Black => White
  end.

Lemma other_color_involutive : forall c : Color,
  other_color (other_color c) = c.
Proof.
  destruct c; reflexivity.
Qed.

Definition Board := cell -> option Color.

Definition empty_board : Board := fun _ => None.

Definition is_line_win (b : Board) (c : Color) (l : list cell) : Prop :=
  forall x : cell, In x l -> b x = Some c.

Definition has_won (b : Board) (c : Color) : Prop :=
  exists l : list cell, In l all_lines /\ is_line_win b c l.

(** ========================================================================= *)
(** 2. LINE INTERSECTION & THE LINEAR HYPERGRAPH THEOREM                       *)
(** ========================================================================= *)

Definition line_intersection (l1 l2 : list cell) : list cell :=
  filter (fun c => existsb (Nat.eqb c) l2) l1.

Definition lines_equal (l1 l2 : list cell) : bool :=
  forallb (fun c => existsb (Nat.eqb c) l2) l1 &&
  forallb (fun c => existsb (Nat.eqb c) l1) l2.

(** THEOREM: Two distinct straight lines in 5x5x5 share at most 1 cell.
    This linear hypergraph property guarantees that threats on distinct lines
    intersect in at most one cell, preventing multi-cell overlaps. *)
Theorem two_lines_intersect_at_most_once : forall l1 l2 : list cell,
  In l1 all_lines ->
  In l2 all_lines ->
  lines_equal l1 l2 = false ->
  length (line_intersection l1 l2) <= 1.
Proof.
  intros l1 l2 Hl1 Hl2 Hneq.
  assert (Hcheck : forallb (fun l1 => forallb (fun l2 =>
    if lines_equal l1 l2 then true else Nat.leb (length (line_intersection l1 l2)) 1) all_lines) all_lines = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck l1 Hl1) as H1.
  rewrite forallb_forall in H1.
  pose proof (H1 l2 Hl2) as H2.
  rewrite Hneq in H2.
  apply Nat.leb_le, H2.
Qed.

(** ========================================================================= *)
(** 3. THREAT DEFINITION & FORK GEOMETRY                                       *)
(** ========================================================================= *)

Definition is_threat (b : Board) (c : Color) (l : list cell) (t : cell) : Prop :=
  In l all_lines /\
  In t l /\
  b t = None /\
  (forall x : cell, In x l -> x <> t -> b x = Some c).

(** Any two distinct lines forming threats intersect in at most one cell *)
Theorem double_threat_intersection_bound : forall (b : Board) (c : Color) (l1 l2 : list cell) (t1 t2 : cell),
  is_threat b c l1 t1 ->
  is_threat b c l2 t2 ->
  lines_equal l1 l2 = false ->
  length (line_intersection l1 l2) <= 1.
Proof.
  intros b c l1 l2 t1 t2 [Hl1 _] [Hl2 _] Hneq.
  apply (two_lines_intersect_at_most_once l1 l2 Hl1 Hl2 Hneq).
Qed.

(** ========================================================================= *)
(** 4. OPENING THREAT DOMINANCE BY GRAPH DEGREE                                *)
(** ========================================================================= *)

Theorem opening_center_lines_count :
  length (filter (fun l => existsb (Nat.eqb 62) l) all_lines) = 13.
Proof. reflexivity. Qed.

Theorem opening_corner_lines_count :
  length (filter (fun l => existsb (Nat.eqb 0) l) all_lines) = 7.
Proof. reflexivity. Qed.

Theorem opening_subcenter_lines_count :
  length (filter (fun l => existsb (Nat.eqb 31) l) all_lines) = 7.
Proof. reflexivity. Qed.

Theorem opening_edge_center_lines_count :
  length (filter (fun l => existsb (Nat.eqb 12) l) all_lines) = 5.
Proof. reflexivity. Qed.

Theorem opening_inner_face_lines_count :
  length (filter (fun l => existsb (Nat.eqb 1) l) all_lines) = 4.
Proof. reflexivity. Qed.

Theorem opening_outer_edge_lines_count :
  length (filter (fun l => existsb (Nat.eqb 7) l) all_lines) = 3.
Proof. reflexivity. Qed.

(** Center opening activates strictly more winning lines (13) than corner opening (7) *)
Theorem opening_center_strictly_dominates_corner :
  cell_degree 62 > cell_degree 0.
Proof.
  unfold cell_degree. simpl. lia.
Qed.

(** Corner opening activates strictly more winning lines (7) than flank edge opening (3) *)
Theorem opening_corner_strictly_dominates_edge :
  cell_degree 0 > cell_degree 7.
Proof.
  unfold cell_degree. simpl. lia.
Qed.
