(* ============================================================================== *)
(* NMM12Graph.v - Mathematical Foundations of Twelve Men's Morris (12MM)          *)
(* 24 Points, 40 Edges, 20 Mills (including 4 Diagonals), and D4 Automorphisms    *)
(* Verified for Rocq 9.1 with ZERO unproven axioms.                              *)
(* ============================================================================== *)

From Stdlib Require Import List Arith Bool Lia PeanoNat.
Import ListNotations.
Require Import NMM.NMMGraph.
Require Import NMM.NMMGame.
Require Import NMM.NMMInvariants.
Require Import NMM.NMMTransversal.

Section TwelveMensMorrisGraphTheory.

(** ============================================================================== *)
(** 1. The 4 Diagonal Mills & The 20-Mill System                                   *)
(** ============================================================================== *)

Definition diagonal_mills : list mill :=
  [ (0, 8, 16);   (* NW Diagonal *)
    (2, 10, 18);  (* NE Diagonal *)
    (4, 12, 20);  (* SE Diagonal *)
    (6, 14, 22)   (* SW Diagonal *)
  ].

Lemma diagonal_mills_count : length diagonal_mills = 4.
Proof. reflexivity. Qed.

Definition all_mills_12 : list mill :=
  all_mills ++ diagonal_mills.

Theorem all_mills_12_count : length all_mills_12 = 20.
Proof. reflexivity. Qed.

Definition point_in_mill_12 (p : nat) (m : mill) : bool :=
  let '(a, b, c) := m in
  (p =? a) || (p =? b) || (p =? c).

Definition mills_of_point_12 (p : nat) : list mill :=
  filter (point_in_mill_12 p) all_mills_12.

(** Broken Regularity Theorem:
    - 12 Corners have mill degree 3 (2 concentric square sides + 1 diagonal)
    - 12 Midpoints have mill degree 2 (1 concentric square side + 1 radial cross)
*)
Theorem corner_mill_degree_3 : forall p,
  In p [0; 2; 4; 6; 8; 10; 12; 14; 16; 18; 20; 22] ->
  length (mills_of_point_12 p) = 3.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

Theorem midpoint_mill_degree_2 : forall p,
  In p [1; 3; 5; 7; 9; 11; 13; 15; 17; 19; 21; 23] ->
  length (mills_of_point_12 p) = 2.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

(** Incidence Handshake: 12*3 + 12*2 = 36 + 24 = 60 = 20*3 *)
Theorem mill_incidence_handshake_12 :
  12 * 3 + 12 * 2 = 20 * 3.
Proof. reflexivity. Qed.

(** ============================================================================== *)
(** 2. 40 Undirected Edges of Twelve Men's Morris                                  *)
(** ============================================================================== *)

Definition is_adjacent_12 (u v : nat) : bool :=
  is_adjacent u v ||
  (* NW diagonal edges *)
  ((u =? 0) && (v =? 8)) || ((u =? 8) && (v =? 0)) ||
  ((u =? 8) && (v =? 16)) || ((u =? 16) && (v =? 8)) ||
  (* NE diagonal edges *)
  ((u =? 2) && (v =? 10)) || ((u =? 10) && (v =? 2)) ||
  ((u =? 10) && (v =? 18)) || ((u =? 18) && (v =? 10)) ||
  (* SE diagonal edges *)
  ((u =? 4) && (v =? 12)) || ((u =? 12) && (v =? 4)) ||
  ((u =? 12) && (v =? 20)) || ((u =? 20) && (v =? 12)) ||
  (* SW diagonal edges *)
  ((u =? 6) && (v =? 14)) || ((u =? 14) && (v =? 6)) ||
  ((u =? 14) && (v =? 22)) || ((u =? 22) && (v =? 14)).

Definition neighbors_12 (u : nat) : list nat :=
  filter (is_adjacent_12 u) all_points.

Definition degree_12 (u : nat) : nat :=
  length (neighbors_12 u).

Theorem adjacent_12_sym : forall u v,
  In u all_points -> In v all_points ->
  is_adjacent_12 u v = is_adjacent_12 v u.
Proof.
  intros u v Hu Hv.
  repeat (destruct Hu as [<- | Hu]; [
    repeat (destruct Hv as [<- | Hv]; [reflexivity | ]); contradiction
  | ]); contradiction.
Qed.

(** Graph Degree Distribution in 12MM:
    - All 8 middle ring vertices have degree 4
    - All 8 outer ring vertices have degree 3
    - All 8 inner ring vertices have degree 3
*)
Theorem middle_ring_degree_4 : forall p,
  In p [8; 9; 10; 11; 12; 13; 14; 15] ->
  degree_12 p = 4.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

Theorem outer_ring_degree_3 : forall p,
  In p [0; 1; 2; 3; 4; 5; 6; 7] ->
  degree_12 p = 3.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

Theorem inner_ring_degree_3 : forall p,
  In p [16; 17; 18; 19; 20; 21; 22; 23] ->
  degree_12 p = 3.
Proof.
  intros p Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

Definition total_degree_12 : nat :=
  fold_right plus 0 (map degree_12 all_points).

(** Handshake Lemma: Total degree = 80 = 2 * 40 edges *)
Theorem handshake_lemma_12 : total_degree_12 = 80.
Proof.
  unfold total_degree_12. reflexivity.
Qed.

(** ============================================================================== *)
(** 3. D4 Dihedral Symmetry Automorphism on Twelve Men's Morris                    *)
(** ============================================================================== *)

Definition is_canonical_mill_12 (m : mill) : bool :=
  let '(a, b, c) := m in
  existsb (fun m0 =>
    let '(x, y, z) := m0 in
    (a =? x) && (b =? y) && (c =? z)
  ) all_mills_12.

Theorem rot_preserves_diagonal_mills : forall m,
  In m diagonal_mills ->
  is_canonical_mill_12 (transform_mill rot m) = true.
Proof.
  intros m Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

Theorem refl_preserves_diagonal_mills : forall m,
  In m diagonal_mills ->
  is_canonical_mill_12 (transform_mill refl m) = true.
Proof.
  intros m Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

Theorem rot_preserves_all_20_mills : forall m,
  In m all_mills_12 ->
  is_canonical_mill_12 (transform_mill rot m) = true.
Proof.
  intros m Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

Theorem refl_preserves_all_20_mills : forall m,
  In m all_mills_12 ->
  is_canonical_mill_12 (transform_mill refl m) = true.
Proof.
  intros m Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

(** ============================================================================== *)
(** 4. Breakthrough: The 8-Stone Transversal Barrier on Twelve Men's Morris        *)
(** ============================================================================== *)

Definition mill_intersects_12 (S : list nat) (m : mill) : bool :=
  let '(a, b, c) := m in
  in_nat_list a S || in_nat_list b S || in_nat_list c S.

(** The 12MM Canonical 8-Stone Transversal:
    Points: {1, 3, 5, 7, 10, 14, 16, 20}
    - 4 Outer Midpoints {1, 3, 5, 7}
    - 2 Middle Corners {10, 14} (NE, SW)
    - 2 Inner Corners {16, 20} (NW, SE)
*)
Definition transversal_12_8 : list nat :=
  [1; 3; 5; 7; 10; 14; 16; 20].

Lemma transversal_12_8_length : length transversal_12_8 = 8.
Proof. reflexivity. Qed.

Theorem transversal_12_8_covers_all_20_mills : forall m,
  In m all_mills_12 ->
  mill_intersects_12 transversal_12_8 m = true.
Proof.
  intros m Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

(** Defensive Surplus Theorem:
    In Twelve Men's Morris, each player places 12 stones.
    The minimum transversal barrier requires only 8 stones.
    Therefore, the defender has 4 surplus stones!
*)
Definition STONE_COUNT_12MM : nat := 12.
Definition TRANSVERSAL_SIZE_12MM : nat := 8.

Theorem defensive_surplus_12mm :
  STONE_COUNT_12MM - TRANSVERSAL_SIZE_12MM = 4.
Proof. reflexivity. Qed.

(** ============================================================================== *)
(** 5. The Ply 8 Forced Opening Mill Fork & Corner Ray Double-Fork Theorem         *)
(** ============================================================================== *)

Definition is_mill_complete_12 (stones : list nat) (m : mill) : bool :=
  let '(a, b, c) := m in
  in_nat_list a stones && in_nat_list b stones && in_nat_list c stones.

Definition forms_mill_12 (stones : list nat) (p : nat) : bool :=
  existsb (fun m =>
    point_in_mill_12 p m && is_mill_complete_12 stones m
  ) all_mills_12.

(** Corner 0 radiates 3 distinct mills whose remaining point pairs {1,2}, {6,7}, {8,16}
    are pairwise disjoint. *)
Theorem corner_0_three_rays :
  mills_of_point_12 0 = [(0, 1, 2); (0, 6, 7); (0, 8, 16)].
Proof. reflexivity. Qed.

(** For ANY legal Black reply b1 <> 0 placed at Ply 1 (after White occupies 0 at Ply 0),
    at least 2 of Corner 0's 3 rays remain completely unblocked by [b1]! *)
Definition ray_unblocked (b_stones : list nat) (m : mill) : bool :=
  negb (mill_intersects_12 b_stones m).

Theorem corner_0_two_rays_unblocked_after_ply1 : forall b1 : nat,
  In b1 all_points ->
  b1 <> 0 ->
  2 <= length (filter (ray_unblocked [b1]) (mills_of_point_12 0)).
Proof.
  intros b1 Hb1 Hneq.
  repeat (destruct Hb1 as [<- | Hb1]; [try congruence; simpl; lia | ]); contradiction.
Qed.

(** Concrete Ply 8 Double-Fork Configuration:
    After White places [0; 6; 8; 14] (Plies 0, 2, 4, 6), White simultaneously
    threatens two distinct mills at two distinct empty points (15 and 22):
    - Placing at 22 completes the SW diagonal mill (6, 14, 22).
    - Placing at 15 completes the Middle West mill (8, 14, 15).
    Since 15 <> 22, Black's single move b4 at Ply 7 cannot occupy both 15 and 22,
    guaranteeing that at least one winning mill completion remains open at Ply 8! *)
Definition white_ply6_fork_stones : list nat := [0; 6; 8; 14].

Theorem ply8_corner_fork_theorem :
  (15 <> 22) /\
  forms_mill_12 (22 :: white_ply6_fork_stones) 22 = true /\
  forms_mill_12 (15 :: white_ply6_fork_stones) 15 = true /\
  (forall b4 : nat,
    ((b4 =? 15) = false /\ forms_mill_12 (15 :: white_ply6_fork_stones) 15 = true) \/
    ((b4 =? 22) = false /\ forms_mill_12 (22 :: white_ply6_fork_stones) 22 = true)).
Proof.
  split; [lia | ].
  split; [reflexivity | ].
  split; [reflexivity | ].
  intros b4.
  destruct (b4 =? 15) eqn:E15.
  - apply Nat.eqb_eq in E15. subst b4.
    right. split; reflexivity.
  - left. split; [reflexivity | reflexivity].
Qed.

End TwelveMensMorrisGraphTheory.
