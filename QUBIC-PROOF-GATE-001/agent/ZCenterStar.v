(** trusted/agent/ZCenterStar.v: The Center Star Dispersion Theorem
    and Move-1 Center Dominance for 5x5x5 Qubic.
    Branch: agent-qubic-5x5x5 *)

From Stdlib Require Import List Arith Bool Lia.
From QubicTrusted Require Import Rules Goal.
From QubicAgent Require Import Geometry Minimax RulesFacts.
Import ListNotations.

(** 1. Center cell 62 is the unique cell with degree 13 *)

Definition lines_through (c : cell) : list (list cell) :=
  filter (fun l => existsb (Nat.eqb c) l) all_lines.

Lemma center_degree_is_13 : length (lines_through 62) = 13%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma non_center_degree_le_7 :
  forall c, c < 125 -> c <> 62 -> (length (lines_through c) <= 7)%nat.
Proof.
  assert (H : forallb (fun c => (c =? 62) || (length (lines_through c) <=? 7)) all_cells = true)
    by (vm_compute; reflexivity).
  intros c Hc Hneq.
  apply forallb_forall with (x := c) in H; [|apply in_seq; lia].
  apply orb_true_iff in H as [Heq | Hle].
  - apply Nat.eqb_eq in Heq. subst c. exfalso. apply Hneq. reflexivity.
  - apply Nat.leb_le in Hle. exact Hle.
Qed.

Theorem center_uniquely_dominates_degree :
  forall c, c < 125 -> c <> 62 -> (length (lines_through c) < length (lines_through 62))%nat.
Proof.
  intros c Hc Hneq.
  rewrite center_degree_is_13.
  pose proof (non_center_degree_le_7 c Hc Hneq) as Hle.
  lia.
Qed.

(** 2. Center Star Dispersion Theorem:
    Any two distinct lines through 62 intersect ONLY at 62.
    Consequently, any other cell c <> 62 intersects AT MOST ONE line through 62. *)

Definition center_lines := lines_through 62.

Lemma cell_on_line_spec : forall c l,
  In c l <-> existsb (Nat.eqb c) l = true.
Proof.
  intros c l. rewrite existsb_exists. split.
  - intros Hin. exists c. split; [exact Hin | apply Nat.eqb_refl].
  - intros [x [Hin Heq]]. apply Nat.eqb_eq in Heq. subst x. exact Hin.
Qed.

Theorem center_lines_pairwise_disjoint_outside_center :
  forall c, c < 125 -> c <> 62 ->
  (length (filter (fun l => existsb (Nat.eqb c) l) center_lines) <= 1)%nat.
Proof.
  assert (H : forallb (fun c => (c =? 62) ||
    (length (filter (fun l => existsb (Nat.eqb c) l) center_lines) <=? 1)) all_cells = true)
    by (vm_compute; reflexivity).
  intros c Hc Hneq.
  apply forallb_forall with (x := c) in H; [|apply in_seq; lia].
  apply orb_true_iff in H as [Heq | Hle].
  - apply Nat.eqb_eq in Heq. subst c. exfalso. apply Hneq. reflexivity.
  - apply Nat.leb_le in Hle. exact Hle.
Qed.

(** Consequence: Exactly 52 cells belong to a line through 62 (each on exactly 1 line),
    and exactly 72 cells belong to 0 lines through 62. *)

Theorem center_spoke_census :
  length (filter (fun c => length (filter (fun l => existsb (Nat.eqb c) l) center_lines) =? 1) (seq 0 125)) = 52%nat /\
  length (filter (fun c => length (filter (fun l => existsb (Nat.eqb c) l) center_lines) =? 0) (seq 0 125)) = 72%nat.
Proof. vm_compute. split; reflexivity. Qed.

(** 3. Direct line-blocking by Black playing 62 against canonical openings:
    For openings 0 (Corner), 2 (Edge-Center), 12 (Face-Center), cell 62 directly
    shares a winning line with White, neutralizing it immediately. *)

Definition shared_line (c1 c2 : cell) : option (list cell) :=
  find (fun l => existsb (Nat.eqb c1) l && existsb (Nat.eqb c2) l) all_lines.

Lemma shared_line_spec : forall c1 c2 l,
  shared_line c1 c2 = Some l ->
  In l all_lines /\ In c1 l /\ In c2 l.
Proof.
  intros c1 c2 l Hfind.
  unfold shared_line in Hfind.
  apply find_some in Hfind as [Hin Hand].
  apply andb_true_iff in Hand as [H1 H2].
  apply cell_on_line_spec in H1.
  apply cell_on_line_spec in H2.
  auto.
Qed.

Theorem corner_zero_shares_space_diagonal_with_center :
  exists l, shared_line 0 62 = Some l /\ In l all_lines /\ In 0 l /\ In 62 l.
Proof.
  vm_compute. eexists. split; [reflexivity|].
  split; [repeat (try (left; reflexivity); right)|].
  split; [repeat (try (left; reflexivity); right)|].
  repeat (try (left; reflexivity); right).
Qed.

Theorem edge_center_two_shares_diagonal_with_center :
  exists l, shared_line 2 62 = Some l /\ In l all_lines /\ In 2 l /\ In 62 l.
Proof.
  vm_compute. eexists. split; [reflexivity|].
  split; [repeat (try (left; reflexivity); right)|].
  split; [repeat (try (left; reflexivity); right)|].
  repeat (try (left; reflexivity); right).
Qed.

Theorem face_center_twelve_shares_axis_with_center :
  exists l, shared_line 12 62 = Some l /\ In l all_lines /\ In 12 l /\ In 62 l.
Proof.
  vm_compute. eexists. split; [reflexivity|].
  split; [repeat (try (left; reflexivity); right)|].
  split; [repeat (try (left; reflexivity); right)|].
  repeat (try (left; reflexivity); right).
Qed.

Print Assumptions center_uniquely_dominates_degree.
Print Assumptions center_lines_pairwise_disjoint_outside_center.
Print Assumptions center_spoke_census.
Print Assumptions corner_zero_shares_space_diagonal_with_center.
Print Assumptions edge_center_two_shares_diagonal_with_center.
Print Assumptions face_center_twelve_shares_axis_with_center.
