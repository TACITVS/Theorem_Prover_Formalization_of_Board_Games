(** **************************************************************************
    DAB16Graph.v: 5x5 Dots / 4x4 Boxes Grid Topology & D4 Group Actions in Rocq
    
    This module formalizes the concrete 25-vertex, 40-edge, 16-box planar
    board graph for Dots and Boxes on a 5x5 dot grid (4x4 boxes).
    
    Covers:
    1. Canonical coordinate indexing: 20 horizontal edges, 20 vertical edges.
    2. 16 boxes with exact 4-edge boundaries and pairwise distinctness (NoDup).
    3. Partition into 16 boundary edges and 24 interior edges.
    4. D4 dihedral automorphism group:
       - 90-degree rotation R (order 4)
       - Vertical reflection S (order 2)
       - Dihedral commutation relation: R * S = S * R^3
    5. Invariance of boundary vs. interior classification under D4 actions.
    6. Dual graph 4-regularity for all 16 boxes.
    
    Zero unproven axioms, zero admissions (Closed under global context).
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool.
From DAB Require Import DABUniversal.
Import ListNotations.

Section DAB16.

Definition num_dots : nat := 25.
Definition num_edges : nat := 40.
Definition num_boxes : nat := 16.

(** Edge indexing:
    - Horizontal edges H(r, c) = 4*r + c for r in 0..4, c in 0..3 (indices 0..19)
    - Vertical edges V(r, c) = 20 + 5*r + c for r in 0..3, c in 0..4 (indices 20..39) *)
Definition h_edge (r c : nat) : nat := 4 * r + c.
Definition v_edge (r c : nat) : nat := 20 + 5 * r + c.

(** Box b = 4*r + c has 4 bounding edges:
    top = H(r, c), bottom = H(r+1, c), left = V(r, c), right = V(r, c+1) *)
Definition box_edges (b : nat) : list nat :=
  let r := b / 4 in
  let c := b mod 4 in
  [h_edge r c; h_edge (r + 1) c; v_edge r c; v_edge r (c + 1)].

(** Every box has exactly 4 bounding edges. *)
Theorem box_edges_length : forall b : nat,
  length (box_edges b) = 4.
Proof.
  intros b. unfold box_edges. reflexivity.
Qed.

(** Every box b < 16 has 4 pairwise distinct incident edges. *)
Theorem box_edges_nodup : forall b : nat,
  b < 16 -> NoDup (box_edges b).
Proof.
  intros b Hb.
  do 16 (destruct b as [|b]; [
    unfold box_edges, h_edge, v_edge; simpl;
    repeat (constructor; [simpl; intuition discriminate|]);
    apply NoDup_nil
  |]).
  lia.
Qed.

(** Every incident edge of a box b < 16 is a valid edge index < 40. *)
Theorem box_edges_bound : forall b e : nat,
  b < 16 -> In e (box_edges b) -> e < 40.
Proof.
  intros b e Hb Hin.
  do 16 (destruct b as [|b]; [vm_compute in Hin; intuition lia|]).
  lia.
Qed.

(** **************************************************************************
    1. D4 Dihedral Group Actions on Edges
    ************************************************************************** *)

(** Clockwise 90-degree rotation on edges:
    - H(r, c) -> V(c, 4 - r)
    - V(r, c) -> H(c, 3 - r) *)
Definition rot_edge (e : nat) : nat :=
  if e <? 20 then
    let r := e / 4 in
    let c := e mod 4 in
    20 + 5 * c + (4 - r)
  else
    let v := e - 20 in
    let r := v / 5 in
    let c := v mod 5 in
    4 * c + (3 - r).

(** Vertical axis reflection on edges:
    - H(r, c) -> H(r, 3 - c)
    - V(r, c) -> V(r, 4 - c) *)
Definition refl_edge (e : nat) : nat :=
  if e <? 20 then
    let r := e / 4 in
    let c := e mod 4 in
    4 * r + (3 - c)
  else
    let v := e - 20 in
    let r := v / 5 in
    let c := v mod 5 in
    20 + 5 * r + (4 - c).

(** **************************************************************************
    2. Rotation Order 4 Theorem
    ************************************************************************** *)

Lemma rot_edge_bound : forall e : nat,
  e < 40 -> rot_edge e < 40.
Proof.
  intros e He.
  do 40 (destruct e as [|e]; [vm_compute; lia|]).
  lia.
Qed.

Theorem rot_order_4 : forall e : nat,
  e < 40 ->
  rot_edge (rot_edge (rot_edge (rot_edge e))) = e.
Proof.
  intros e He.
  do 40 (destruct e as [|e]; [vm_compute; reflexivity|]).
  lia.
Qed.

(** **************************************************************************
    3. Reflection Order 2 Theorem
    ************************************************************************** *)

Lemma refl_edge_bound : forall e : nat,
  e < 40 -> refl_edge e < 40.
Proof.
  intros e He.
  do 40 (destruct e as [|e]; [vm_compute; lia|]).
  lia.
Qed.

Theorem refl_order_2 : forall e : nat,
  e < 40 ->
  refl_edge (refl_edge e) = e.
Proof.
  intros e He.
  do 40 (destruct e as [|e]; [vm_compute; reflexivity|]).
  lia.
Qed.

(** **************************************************************************
    4. D4 Dihedral Commutation Relation
    ************************************************************************** *)

Theorem dihedral_relation : forall e : nat,
  e < 40 ->
  rot_edge (refl_edge e) = refl_edge (rot_edge (rot_edge (rot_edge e))).
Proof.
  intros e He.
  do 40 (destruct e as [|e]; [vm_compute; reflexivity|]).
  lia.
Qed.

(** **************************************************************************
    5. Boundary vs. Interior Edge Classification & D4 Invariance
    ************************************************************************** *)

Definition is_boundary_edge (e : nat) : bool :=
  match e with
  | 0 | 1 | 2 | 3 | 16 | 17 | 18 | 19 => true
  | 20 | 24 | 25 | 29 | 30 | 34 | 35 | 39 => true
  | _ => false
  end.

Definition boundary_list : list nat :=
  [0; 1; 2; 3; 16; 17; 18; 19; 20; 24; 25; 29; 30; 34; 35; 39].

Theorem boundary_list_length : length boundary_list = 16.
Proof. reflexivity. Qed.

Theorem boundary_count_matches_universal :
  length boundary_list = boundary_edges 4.
Proof.
  unfold boundary_edges. reflexivity.
Qed.

Theorem interior_count_matches_universal :
  num_edges - length boundary_list = interior_edges 4.
Proof.
  unfold num_edges, boundary_list, interior_edges. simpl. reflexivity.
Qed.

(** 90-degree rotation preserves boundary vs. interior edge classification. *)
Theorem rot_preserves_boundary : forall e : nat,
  e < 40 ->
  is_boundary_edge (rot_edge e) = is_boundary_edge e.
Proof.
  intros e He.
  do 40 (destruct e as [|e]; [vm_compute; reflexivity|]).
  lia.
Qed.

(** Vertical reflection preserves boundary vs. interior edge classification. *)
Theorem refl_preserves_boundary : forall e : nat,
  e < 40 ->
  is_boundary_edge (refl_edge e) = is_boundary_edge e.
Proof.
  intros e He.
  do 40 (destruct e as [|e]; [vm_compute; reflexivity|]).
  lia.
Qed.

(** **************************************************************************
    6. Dual Graph 4-Regularity Theorem
    ************************************************************************** *)

(** In the dual graph, every box is bounded by 4 distinct edges. *)
Theorem dual_box_degree_4 : forall b : nat,
  b < 16 -> length (box_edges b) = 4.
Proof.
  intros b Hb.
  apply box_edges_length.
Qed.

(** Total box-edge incidences on 4x4 grid is 64. *)
Theorem total_box_edge_incidences_16 :
  num_boxes * 4 = 64.
Proof. reflexivity. Qed.

End DAB16.
