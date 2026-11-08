(**
  C4CenterPigeonhole.v: Center Column Pigeonhole & 24-Cell Transversal Theorem
  Formalized in Rocq 9.1.
  Strict Zero-Axiom Standard: 100% Closed under the global context.
*)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
Require Import C4.C4Board.
Require Import C4.C4Claimeven.

(** Mirror Reflection across Center Axis Column 3 *)
Definition refl_c (c : nat) : nat := 6 - c.

Theorem refl_c_fixed_point : refl_c 3 = 3.
Proof. reflexivity. Qed.

Theorem refl_c_involutive : forall c, c <= 6 -> refl_c (refl_c c) = c.
Proof. intros c Hc. unfold refl_c. lia. Qed.

(** Center-Column Window Pigeonhole Theorem *)
Theorem horiz_window_contains_center :
  forall c0, c0 <= 3 -> c0 <= 3 /\ 3 <= c0 + 3.
Proof.
  intros c0 Hc0. lia.
Qed.

Theorem horiz_line_contains_center :
  forall c0 r, c0 <= 3 -> In (3, r) (horiz_line c0 r).
Proof.
  intros c0 r Hc0.
  unfold horiz_line.
  assert (c0 = 0 \/ c0 = 1 \/ c0 = 2 \/ c0 = 3) as [-> | [-> | [-> | ->]]] by lia;
  simpl; auto.
Qed.

(** The 3 Even Center Cells *)
Definition E_center : list point := [(3, 0); (3, 2); (3, 4)].

Theorem center_even_count : length E_center = 3.
Proof. reflexivity. Qed.

(** The 24-Cell Master Defensive Transversal *)
Definition transversal_24 : list point := O_21 ++ E_center.

Theorem transversal_24_count : length transversal_24 = 24.
Proof. reflexivity. Qed.

(** Master Transversal Theorem: Blocks 100% of the 69 Winning Lines *)
Theorem transversal_blocks_all_69_lines :
  forall l, In l all_lines -> line_blocked_by transversal_24 l = true.
Proof.
  intros l Hl.
  assert (Hcheck : forallb (line_blocked_by transversal_24) all_lines = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Hcheck, Hl.
Qed.

(** Even-Row Horizontals Intersect Center Column *)
Theorem all_12_even_horiz_blocked_by_center :
  forall c0 r, In r [0; 2; 4] -> In c0 [0; 1; 2; 3] ->
    line_blocked_by E_center (horiz_line c0 r) = true.
Proof.
  intros c0 r Hr Hc0.
  destruct Hr as [<- | [<- | [<- | []]]];
  destruct Hc0 as [<- | [<- | [<- | [<- | []]]]];
  reflexivity.
Qed.
