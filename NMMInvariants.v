(* ============================================================================== *)
(* NMMInvariants.v - Analytic Invariants, Transversal Theorems, and Bounds       *)
(* Verified for Rocq 9.1 with ZERO unproven axioms.                              *)
(* ============================================================================== *)

From Stdlib Require Import List Arith Bool Lia PeanoNat.
Import ListNotations.
Require Import NMM.NMMGraph.
Require Import NMM.NMMGame.

Section NMMInvariants.

(** Theorem 1: Every Mill contains at least one Midpoint *)
Definition all_midpoints : list nat :=
  [1; 3; 5; 7; 9; 11; 13; 15; 17; 19; 21; 23].

Definition mill_has_midpoint (m : mill) : bool :=
  let '(a, b, c) := m in
  in_nat_list a all_midpoints || in_nat_list b all_midpoints || in_nat_list c all_midpoints.

Theorem all_mills_intersect_midpoints : forall m,
  In m all_mills ->
  mill_has_midpoint m = true.
Proof.
  intros m Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

(** Theorem 2: The 12 corners contain NO radial mills *)
Definition all_corners : list nat :=
  [0; 2; 4; 6; 8; 10; 12; 14; 16; 18; 20; 22].

Definition radial_mills : list mill :=
  [(1, 9, 17); (3, 11, 19); (5, 13, 21); (7, 15, 23)].

Definition mill_in_corners (m : mill) : bool :=
  let '(a, b, c) := m in
  in_nat_list a all_corners && in_nat_list b all_corners && in_nat_list c all_corners.

Theorem radial_mills_disjoint_from_corners : forall m,
  In m radial_mills ->
  mill_in_corners m = false.
Proof.
  intros m Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity | ]); contradiction.
Qed.

(** Theorem 3: Distinct vertices in all 16 mills *)
Theorem all_mills_distinct_vertices : forall m,
  In m all_mills ->
  let '(a, b, c) := m in
  a <> b /\ b <> c /\ a <> c.
Proof.
  intros m Hin.
  repeat (destruct Hin as [<- | Hin]; [
    simpl; repeat split; discriminate
  | ]); contradiction.
Qed.

(** Theorem 4: Minimum stones to complete a mill is at least 3 *)
Theorem empty_board_no_mills : forall m,
  is_mill_complete [] m = false.
Proof.
  intros [ [a b] c ].
  unfold is_mill_complete. simpl. reflexivity.
Qed.

Theorem single_stone_no_mills : forall x m,
  In m all_mills ->
  is_mill_complete [x] m = false.
Proof.
  intros x [ [a b] c ] Hin.
  apply all_mills_distinct_vertices in Hin.
  simpl in Hin. destruct Hin as [Hab Hrest]. destruct Hrest as [Hbc Hac].
  unfold is_mill_complete. simpl.
  destruct (a =? x) eqn:Ea; [| reflexivity ].
  destruct (b =? x) eqn:Eb; [| reflexivity ].
  apply Nat.eqb_eq in Ea.
  apply Nat.eqb_eq in Eb.
  subst. exfalso. apply Hab. reflexivity.
Qed.

Theorem two_stones_no_mills : forall x y m,
  In m all_mills ->
  is_mill_complete [x; y] m = false.
Proof.
  intros x y [ [a b] c ] Hin.
  apply all_mills_distinct_vertices in Hin.
  simpl in Hin. destruct Hin as [Hab Hrest]. destruct Hrest as [Hbc Hac].
  unfold is_mill_complete. simpl.
  destruct (a =? x) eqn:Eax.
  - apply Nat.eqb_eq in Eax; subst.
    destruct (b =? x) eqn:Ebx.
    { apply Nat.eqb_eq in Ebx; subst; exfalso; apply Hab; reflexivity. }
    destruct (b =? y) eqn:Eby; [| reflexivity ].
    apply Nat.eqb_eq in Eby; subst.
    destruct (c =? x) eqn:Ecx.
    { apply Nat.eqb_eq in Ecx; subst; exfalso; apply Hac; reflexivity. }
    destruct (c =? y) eqn:Ecy.
    { apply Nat.eqb_eq in Ecy; subst; exfalso; apply Hbc; reflexivity. }
    reflexivity.
  - destruct (a =? y) eqn:Eay; [| reflexivity ].
    apply Nat.eqb_eq in Eay; subst.
    destruct (b =? x) eqn:Ebx.
    + apply Nat.eqb_eq in Ebx; subst.
      destruct (c =? x) eqn:Ecx.
      { apply Nat.eqb_eq in Ecx; subst; exfalso; apply Hbc; reflexivity. }
      destruct (c =? y) eqn:Ecy.
      { apply Nat.eqb_eq in Ecy; subst; exfalso; apply Hac; reflexivity. }
      reflexivity.
    + destruct (b =? y) eqn:Eby.
      { apply Nat.eqb_eq in Eby; subst; exfalso; apply Hab; reflexivity. }
      reflexivity.
Qed.

Theorem mill_complete_requires_at_least_three : forall stones m,
  In m all_mills ->
  is_mill_complete stones m = true ->
  3 <= length stones.
Proof.
  intros stones m Hin Hcomp.
  destruct stones as [| s1 [| s2 [| s3 rest]]].
  - rewrite empty_board_no_mills in Hcomp. discriminate.
  - rewrite (single_stone_no_mills s1 m Hin) in Hcomp. discriminate.
  - rewrite (two_stones_no_mills s1 s2 m Hin) in Hcomp. discriminate.
  - simpl. lia.
Qed.

(** Theorem 5: In Phase 1 (Placement), neither player can be in terminal loss *)
Theorem phase1_no_terminal_loss : forall s p pw pb,
  current_phase s = PhasePlacement pw pb ->
  is_terminal_loss s p = false.
Proof.
  intros s p pw pb Hphase.
  unfold is_terminal_loss.
  rewrite Hphase. reflexivity.
Qed.

(** Theorem 6: Graph Regularity - Total degree is 64 *)
Theorem total_degrees_correct : total_degree = 64.
Proof.
  apply handshake_lemma.
Qed.

End NMMInvariants.
