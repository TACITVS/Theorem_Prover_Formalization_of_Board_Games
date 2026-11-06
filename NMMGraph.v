(* ============================================================================== *)
(* NMMGraph.v - Formal Graph Theory, Topology & D4 Dihedral Symmetry of Nine Men's Morris *)
(* Verified for Rocq 9.1 with ZERO unproven axioms.                              *)
(* ============================================================================== *)

From Stdlib Require Import List Arith Bool Lia PeanoNat.
Import ListNotations.

Section NMMGraphTheory.

(** Total points on the board: 24 points (3 concentric squares of 8 points) *)
Definition NUM_POINTS : nat := 24.
Definition is_point (p : nat) : bool := p <? NUM_POINTS.

Definition ring_of (p : nat) : nat := p / 8.
Definition pos_of (p : nat) : nat := p mod 8.

Definition is_corner (p : nat) : bool := (pos_of p mod 2 =? 0).
Definition is_midpoint (p : nat) : bool := (pos_of p mod 2 =? 1).

(** Canonical indexing of 24 points:
    Ring 0 (Outer): 0=NW, 1=N, 2=NE, 3=E, 4=SE, 5=S, 6=SW, 7=W
    Ring 1 (Middle): 8=NW, 9=N, 10=NE, 11=E, 12=SE, 13=S, 14=SW, 15=W
    Ring 2 (Inner): 16=NW, 17=N, 18=NE, 19=E, 20=SE, 21=S, 22=SW, 23=W
*)

Definition all_points : list nat :=
  [0; 1; 2; 3; 4; 5; 6; 7;
   8; 9; 10; 11; 12; 13; 14; 15;
   16; 17; 18; 19; 20; 21; 22; 23].

Lemma all_points_length : length all_points = 24.
Proof. reflexivity. Qed.

Lemma all_points_valid : forall p, In p all_points -> is_point p = true.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

(** The 16 Mills of Nine Men's Morris (each strictly sorted: a < b < c) *)
Definition mill : Type := (nat * nat * nat)%type.

Definition all_mills : list mill :=
  [ (* Ring 0 (Outer) Mills *)
    (0, 1, 2); (2, 3, 4); (4, 5, 6); (0, 6, 7);
    (* Ring 1 (Middle) Mills *)
    (8, 9, 10); (10, 11, 12); (12, 13, 14); (8, 14, 15);
    (* Ring 2 (Inner) Mills *)
    (16, 17, 18); (18, 19, 20); (20, 21, 22); (16, 22, 23);
    (* Radial / Cross Mills *)
    (1, 9, 17); (3, 11, 19); (5, 13, 21); (7, 15, 23)
  ].

Lemma all_mills_count : length all_mills = 16.
Proof. reflexivity. Qed.

Definition point_in_mill (p : nat) (m : mill) : bool :=
  let '(a, b, c) := m in
  (p =? a) || (p =? b) || (p =? c).

Definition mills_of_point (p : nat) : list mill :=
  filter (point_in_mill p) all_mills.

(** Theorem: Regularity of Mills - Every vertex belongs to EXACTLY 2 mills *)
Theorem mill_regularity : forall p,
  In p all_points ->
  length (mills_of_point p) = 2.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

(** Adjacency graph on the 24 points: 32 undirected edges *)
Definition is_adjacent (u v : nat) : bool :=
  if (u =? v) then false
  else
    (* Outer Ring Cycle *)
    ((u =? 0) && ((v =? 1) || (v =? 7))) ||
    ((u =? 1) && ((v =? 0) || (v =? 2) || (v =? 9))) ||
    ((u =? 2) && ((v =? 1) || (v =? 3))) ||
    ((u =? 3) && ((v =? 2) || (v =? 4) || (v =? 11))) ||
    ((u =? 4) && ((v =? 3) || (v =? 5))) ||
    ((u =? 5) && ((v =? 4) || (v =? 6) || (v =? 13))) ||
    ((u =? 6) && ((v =? 5) || (v =? 7))) ||
    ((u =? 7) && ((v =? 6) || (v =? 0) || (v =? 15))) ||
    (* Middle Ring Cycle + Radial *)
    ((u =? 8) && ((v =? 9) || (v =? 15))) ||
    ((u =? 9) && ((v =? 8) || (v =? 10) || (v =? 1) || (v =? 17))) ||
    ((u =? 10) && ((v =? 9) || (v =? 11))) ||
    ((u =? 11) && ((v =? 10) || (v =? 12) || (v =? 3) || (v =? 19))) ||
    ((u =? 12) && ((v =? 11) || (v =? 13))) ||
    ((u =? 13) && ((v =? 12) || (v =? 14) || (v =? 5) || (v =? 21))) ||
    ((u =? 14) && ((v =? 13) || (v =? 15))) ||
    ((u =? 15) && ((v =? 14) || (v =? 8) || (v =? 7) || (v =? 23))) ||
    (* Inner Ring Cycle + Radial *)
    ((u =? 16) && ((v =? 17) || (v =? 23))) ||
    ((u =? 17) && ((v =? 16) || (v =? 18) || (v =? 9))) ||
    ((u =? 18) && ((v =? 17) || (v =? 19))) ||
    ((u =? 19) && ((v =? 18) || (v =? 20) || (v =? 11))) ||
    ((u =? 20) && ((v =? 19) || (v =? 21))) ||
    ((u =? 21) && ((v =? 20) || (v =? 22) || (v =? 13))) ||
    ((u =? 22) && ((v =? 21) || (v =? 23))) ||
    ((u =? 23) && ((v =? 22) || (v =? 16) || (v =? 15))).

Definition neighbors (u : nat) : list nat :=
  filter (is_adjacent u) all_points.

Definition degree (u : nat) : nat :=
  length (neighbors u).

(** Symmetry of adjacency *)
Theorem adjacent_sym : forall u v,
  In u all_points -> In v all_points ->
  is_adjacent u v = is_adjacent v u.
Proof.
  intros u v Hu Hv.
  repeat (destruct Hu as [<- | Hu]; [
    repeat (destruct Hv as [<- | Hv]; [reflexivity | ]); contradiction
  | ]); contradiction.
Qed.

Theorem adjacent_irreflexive : forall u,
  is_adjacent u u = false.
Proof.
  intros u. unfold is_adjacent.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** Degree classification:
    - 12 corners have degree 2
    - 8 outer/inner midpoints have degree 3
    - 4 middle midpoints have degree 4
*)
Theorem corner_degree_2 : forall p,
  In p [0; 2; 4; 6; 8; 10; 12; 14; 16; 18; 20; 22] ->
  degree p = 2.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

Theorem outer_inner_midpoint_degree_3 : forall p,
  In p [1; 3; 5; 7; 17; 19; 21; 23] ->
  degree p = 3.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

Theorem middle_midpoint_degree_4 : forall p,
  In p [9; 11; 13; 15] ->
  degree p = 4.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

(** Handshake Lemma: Sum of degrees = 2 * 32 edges = 64 *)
Definition total_degree : nat :=
  fold_right plus 0 (map degree all_points).

Theorem handshake_lemma : total_degree = 64.
Proof.
  unfold total_degree. reflexivity.
Qed.

(** ============================================================================== *)
(** D4 Dihedral Symmetry Group Actions                                             *)
(** ============================================================================== *)

(** Clockwise 90-degree Rotation:
    R acts on ring r by shifting pos by +2 mod 8:
    R(8r + pos) = 8r + (pos + 2) mod 8
*)
Definition rot_pos (pos : nat) : nat :=
  (pos + 2) mod 8.

Definition rot (p : nat) : nat :=
  8 * (ring_of p) + rot_pos (pos_of p).

(** Reflection across vertical axis (N-S midline):
    S acts on ring r by mapping pos to (2 + 8 - pos) mod 8:
    pos 0 (NW) <-> pos 2 (NE)
    pos 1 (N)  <-> pos 1 (N)
    pos 7 (W)  <-> pos 3 (E)
    pos 6 (SW) <-> pos 4 (SE)
    pos 5 (S)  <-> pos 5 (S)
*)
Definition refl_pos (pos : nat) : nat :=
  (10 - (pos mod 8)) mod 8.

Definition refl (p : nat) : nat :=
  8 * (ring_of p) + refl_pos (pos_of p).

(** Preservation of point bounds *)
Lemma rot_preserves_points : forall p,
  In p all_points -> In (rot p) all_points.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [simpl; tauto | ]); contradiction.
Qed.

Lemma refl_preserves_points : forall p,
  In p all_points -> In (refl p) all_points.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [simpl; tauto | ]); contradiction.
Qed.

(** Group properties: R^4 = Id, S^2 = Id, R . S = S . R^3 *)
Theorem rot_order_4 : forall p,
  In p all_points ->
  rot (rot (rot (rot p))) = p.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

Theorem refl_order_2 : forall p,
  In p all_points ->
  refl (refl p) = p.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

Theorem dihedral_relation : forall p,
  In p all_points ->
  rot (refl p) = refl (rot (rot (rot p))).
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

(** Automorphism theorems: R and S preserve graph adjacency *)
Theorem rot_preserves_adjacency : forall u v,
  In u all_points -> In v all_points ->
  is_adjacent (rot u) (rot v) = is_adjacent u v.
Proof.
  intros u v Hu Hv.
  repeat (destruct Hu as [<- | Hu]; [
    repeat (destruct Hv as [<- | Hv]; [reflexivity | ]); contradiction
  | ]); contradiction.
Qed.

Theorem refl_preserves_adjacency : forall u v,
  In u all_points -> In v all_points ->
  is_adjacent (refl u) (refl v) = is_adjacent u v.
Proof.
  intros u v Hu Hv.
  repeat (destruct Hu as [<- | Hu]; [
    repeat (destruct Hv as [<- | Hv]; [reflexivity | ]); contradiction
  | ]); contradiction.
Qed.

(** Canonical representation of a mill *)
Definition sort3 (a b c : nat) : mill :=
  let s1 := if a <=? b then (a, b) else (b, a) in
  let '(x1, x2) := s1 in
  let s2 := if x2 <=? c then (x1, x2, c)
            else if x1 <=? c then (x1, c, x2)
            else (c, x1, x2) in
  s2.

Definition is_canonical_mill (m : mill) : bool :=
  let '(a, b, c) := m in
  existsb (fun m0 =>
    let '(x, y, z) := m0 in
    (a =? x) && (b =? y) && (c =? z)
  ) all_mills.

Definition transform_mill (f : nat -> nat) (m : mill) : mill :=
  let '(a, b, c) := m in
  sort3 (f a) (f b) (f c).

(** Automorphism theorems: R and S preserve the 16 mills *)
Theorem rot_preserves_mills : forall m,
  In m all_mills ->
  is_canonical_mill (transform_mill rot m) = true.
Proof.
  intros m Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

Theorem refl_preserves_mills : forall m,
  In m all_mills ->
  is_canonical_mill (transform_mill refl m) = true.
Proof.
  intros m Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

End NMMGraphTheory.
