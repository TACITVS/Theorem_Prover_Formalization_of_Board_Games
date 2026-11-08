(** **************************************************************************
    DABGame.v: Operational Semantics & Inductive Game Rules in Rocq 9.1
    
    This module formalizes the inductive transition relation and game rules
    of 4x4 Dots and Boxes (5x5 dot grid, 40 edges, 16 boxes).
    
    Covers:
    1. Game state record: drawn edges, scores, active turn.
    2. Box completion detection function and newly completed box count.
    3. The Double-Turn Rule: capturing a box grants an immediate bonus turn.
    4. Inductive step relation: step s e s'.
    5. Monotonicity of drawn edges: strictly +1 per step.
    6. Single-edge completion bound: at most 2 boxes completed per edge.
    7. Maximum game depth: strictly bounded by 40 moves.
    8. Completed box accounting and terminal state score conservation:
       when all 40 edges are present, all 16 boxes are completed and
       Score1 + Score2 = 16.
    
    Zero unproven axioms, zero admissions (Closed under global context).
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool.
From DAB Require Import DABUniversal DAB16Graph.
Import ListNotations.

Section DABGame.

Record state : Type := mkState {
  s_edges : list nat;
  s_score1 : nat;
  s_score2 : nat;
  s_turn : player
}.

Definition initial_state : state := mkState [] 0 0 White.

Definition all_boxes : list nat := seq 0 16.

Definition is_edge_drawn (s : state) (e : nat) : bool :=
  existsb (Nat.eqb e) (s_edges s).

Definition is_box_completed_in (drawn : list nat) (b : nat) : bool :=
  forallb (fun e => existsb (Nat.eqb e) drawn) (box_edges b).

Definition is_box_completed (s : state) (b : nat) : bool :=
  is_box_completed_in (s_edges s) b.

(** Check whether box b is newly completed by placing edge e *)
Definition box_newly_completed (s : state) (e : nat) (b : nat) : bool :=
  (negb (is_box_completed s b)) &&
  (is_box_completed_in (e :: s_edges s) b).

Definition count_newly_completed (s : state) (e : nat) : nat :=
  count_occ Nat.eq_dec
    (map (fun b => if box_newly_completed s e b then 1 else 0) all_boxes)
    1.

(** Legal move condition *)
Definition legal_move (s : state) (e : nat) : Prop :=
  e < 40 /\ ~ In e (s_edges s).

(** Inductive transition step *)
Inductive step (s : state) (e : nat) (s' : state) : Prop :=
  | Step_Intro :
      legal_move s e ->
      let k := count_newly_completed s e in
      let bonus := (0 <? k) && (length (s_edges s) + 1 <? 40) in
      let next_turn := if bonus then s_turn s else opp (s_turn s) in
      let next_score1 := match s_turn s with White => s_score1 s + k | Black => s_score1 s end in
      let next_score2 := match s_turn s with White => s_score2 s | Black => s_score2 s + k end in
      s' = mkState (e :: s_edges s) next_score1 next_score2 next_turn ->
      step s e s'.

(** **************************************************************************
    1. Monotonicity of Edges & Game Depth
    ************************************************************************** *)

Theorem step_edge_monotonic : forall s e s',
  step s e s' ->
  length (s_edges s') = S (length (s_edges s)).
Proof.
  intros s e s' Hstep.
  destruct Hstep as [Hleg Hdef].
  subst s'. simpl. reflexivity.
Qed.

Theorem step_distinct_edges : forall s e s',
  step s e s' ->
  NoDup (s_edges s) ->
  NoDup (s_edges s').
Proof.
  intros s e s' Hstep Hnodup.
  destruct Hstep as [[Hbound Hnotin] Hdef].
  subst s'. simpl.
  constructor; auto.
Qed.

Theorem initial_state_empty :
  length (s_edges initial_state) = 0 /\
  s_score1 initial_state = 0 /\
  s_score2 initial_state = 0 /\
  s_turn initial_state = White.
Proof.
  unfold initial_state. simpl. auto.
Qed.

(** **************************************************************************
    2. Monotonicity of Scores
    ************************************************************************** *)

Theorem step_score_monotonic : forall s e s',
  step s e s' ->
  s_score1 s' + s_score2 s' >= s_score1 s + s_score2 s.
Proof.
  intros s e s' Hstep.
  destruct Hstep as [Hleg Hdef].
  subst s'. simpl.
  destruct (s_turn s); lia.
Qed.

(** **************************************************************************
    3. Single-Edge Box Completion Bound (At Most 2 Boxes Per Move)
    ************************************************************************** *)

Lemma forallb_completed_nonincident : forall (drawn : list nat) (e : nat) (l : list nat),
  existsb (Nat.eqb e) l = false ->
  forallb (fun x => existsb (Nat.eqb x) (e :: drawn)) l =
  forallb (fun x => existsb (Nat.eqb x) drawn) l.
Proof.
  intros drawn e l Hni.
  induction l as [|a l' IH]; simpl; [reflexivity|].
  simpl in Hni.
  apply orb_false_iff in Hni. destruct Hni as [Hea Hni'].
  rewrite Nat.eqb_sym in Hea.
  rewrite Hea. simpl.
  f_equal. apply IH. exact Hni'.
Qed.

Lemma box_newly_completed_nonincident : forall (s : state) (e b : nat),
  existsb (Nat.eqb e) (box_edges b) = false ->
  box_newly_completed s e b = false.
Proof.
  intros s e b Hni.
  unfold box_newly_completed, is_box_completed, is_box_completed_in.
  rewrite forallb_completed_nonincident by exact Hni.
  destruct (forallb (fun e0 : nat => existsb (Nat.eqb e0) (s_edges s)) (box_edges b)); reflexivity.
Qed.

Lemma count_occ_cons_1 : forall l,
  count_occ Nat.eq_dec (1 :: l) 1 = S (count_occ Nat.eq_dec l 1).
Proof.
  intros l. simpl. destruct (Nat.eq_dec 1 1); [reflexivity | congruence].
Qed.

Lemma count_occ_cons_0 : forall l,
  count_occ Nat.eq_dec (0 :: l) 1 = count_occ Nat.eq_dec l 1.
Proof.
  intros l. simpl. destruct (Nat.eq_dec 0 1); [congruence | reflexivity].
Qed.

Lemma count_occ_newly_completed_le_incident : forall (s : state) (e : nat) (bs : list nat),
  count_occ Nat.eq_dec (map (fun b => if box_newly_completed s e b then 1 else 0) bs) 1 <=
  count_occ Nat.eq_dec (map (fun b => if existsb (Nat.eqb e) (box_edges b) then 1 else 0) bs) 1.
Proof.
  intros s e bs.
  induction bs as [|b bs' IH]; [simpl; lia|].
  cbn [map].
  destruct (existsb (Nat.eqb e) (box_edges b)) eqn:Hinc.
  - rewrite count_occ_cons_1.
    destruct (box_newly_completed s e b).
    + rewrite count_occ_cons_1. lia.
    + rewrite count_occ_cons_0. lia.
  - rewrite box_newly_completed_nonincident by exact Hinc.
    repeat rewrite count_occ_cons_0.
    exact IH.
Qed.

Definition edge_incident_boxes (e : nat) : nat :=
  count_occ Nat.eq_dec
    (map (fun b => if existsb (Nat.eqb e) (box_edges b) then 1 else 0) all_boxes)
    1.

Lemma edge_incident_boxes_le_2 : forall e : nat,
  e < 40 -> edge_incident_boxes e <= 2.
Proof.
  intros e He.
  do 40 (destruct e as [|e]; [vm_compute; lia|]).
  lia.
Qed.

(** Any single legal edge placement completes at most 2 boxes on the 4x4 grid. *)
Theorem max_two_boxes_per_edge : forall (s : state) (e : nat),
  e < 40 ->
  count_newly_completed s e <= 2.
Proof.
  intros s e He.
  unfold count_newly_completed.
  pose proof (count_occ_newly_completed_le_incident s e all_boxes) as Hle.
  pose proof (edge_incident_boxes_le_2 e He) as Hinc.
  unfold edge_incident_boxes in Hinc.
  lia.
Qed.

(** **************************************************************************
    4. Game Termination Invariant
    ************************************************************************** *)

Definition is_terminal (s : state) : Prop :=
  length (s_edges s) = 40.

Theorem max_game_depth_40 : forall s,
  NoDup (s_edges s) ->
  (forall e, In e (s_edges s) -> e < 40) ->
  length (s_edges s) <= 40.
Proof.
  intros s Hnodup Hbound.
  assert (Hsub : incl (s_edges s) (seq 0 40)).
  { intros x Hin. apply in_seq. split; [lia|].
    apply Hbound in Hin. lia. }
  pose proof (NoDup_incl_length Hnodup Hsub) as Hlen.
  rewrite length_seq in Hlen.
  exact Hlen.
Qed.

(** **************************************************************************
    5. Completed Box Accounting & Terminal Score Conservation (Score1 + Score2 = 16)
    ************************************************************************** *)

Theorem step_score_sum : forall s e s',
  step s e s' ->
  s_score1 s' + s_score2 s' = s_score1 s + s_score2 s + count_newly_completed s e.
Proof.
  intros s e s' Hstep.
  destruct Hstep as [Hleg Hdef].
  subst s'. simpl.
  destruct (s_turn s); lia.
Qed.

Lemma is_box_completed_in_cons_mono : forall (drawn : list nat) (e b : nat),
  is_box_completed_in drawn b = true ->
  is_box_completed_in (e :: drawn) b = true.
Proof.
  intros drawn e b Hcomp.
  unfold is_box_completed_in in *.
  apply forallb_forall.
  intros x Hx.
  pose proof (proj1 (forallb_forall _ (box_edges b)) Hcomp x Hx) as Hx_in.
  simpl. rewrite Hx_in. apply orb_true_r.
Qed.

Lemma filter_completed_cons_gen : forall (s : state) (e : nat) (bs : list nat),
  length (filter (is_box_completed_in (e :: s_edges s)) bs) =
  length (filter (is_box_completed s) bs) +
  count_occ Nat.eq_dec (map (fun b => if box_newly_completed s e b then 1 else 0) bs) 1.
Proof.
  intros s e bs.
  induction bs as [|b bs' IH]; [reflexivity|].
  cbn [filter map].
  unfold box_newly_completed at 1.
  destruct (is_box_completed s b) eqn:Hcomp.
  - unfold is_box_completed in Hcomp.
    rewrite (is_box_completed_in_cons_mono (s_edges s) e b Hcomp).
    cbn [length negb andb]. rewrite count_occ_cons_0. lia.
  - cbn [negb andb].
    destruct (is_box_completed_in (e :: s_edges s) b).
    + cbn [length]. rewrite count_occ_cons_1. lia.
    + rewrite count_occ_cons_0. lia.
Qed.

(** Placing an edge increases the filter count of completed boxes by count_newly_completed. *)
Theorem completed_boxes_step : forall (s : state) (e : nat),
  length (filter (is_box_completed_in (e :: s_edges s)) all_boxes) =
  length (filter (is_box_completed s) all_boxes) + count_newly_completed s e.
Proof.
  intros s e.
  unfold count_newly_completed.
  apply filter_completed_cons_gen.
Qed.

(** Every valid game step preserves the invariant that total score equals completed boxes. *)
Theorem step_score_equals_completed_boxes : forall s e s',
  step s e s' ->
  s_score1 s + s_score2 s = length (filter (is_box_completed s) all_boxes) ->
  s_score1 s' + s_score2 s' = length (filter (is_box_completed s') all_boxes).
Proof.
  intros s e s' Hstep Hinv.
  pose proof (step_score_sum s e s' Hstep) as Hsum.
  destruct Hstep as [_ Hdef].
  subst s'. unfold is_box_completed. simpl s_edges.
  rewrite completed_boxes_step.
  lia.
Qed.

Lemma in_edges_existsb : forall (edges : list nat) (e : nat),
  (forall x, x < 40 -> In x edges) ->
  e < 40 ->
  existsb (Nat.eqb e) edges = true.
Proof.
  intros edges e Hall He.
  apply existsb_exists.
  exists e. split.
  - apply Hall. exact He.
  - apply Nat.eqb_refl.
Qed.

Lemma all_edges_box_completed : forall (edges : list nat) (b : nat),
  (forall e, e < 40 -> In e edges) ->
  b < 16 ->
  is_box_completed_in edges b = true.
Proof.
  intros edges b Hall Hb.
  unfold is_box_completed_in.
  apply forallb_forall.
  intros x Hx.
  apply in_edges_existsb; [exact Hall|].
  apply (box_edges_bound b x Hb Hx).
Qed.

Lemma filter_all_true : forall (A : Type) (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = true) ->
  filter f l = l.
Proof.
  intros A f l H.
  induction l as [|a l' IH]; simpl; [reflexivity|].
  rewrite H by (left; reflexivity).
  f_equal. apply IH.
  intros x Hx. apply H. right; exact Hx.
Qed.

(** When all 40 edges are present on the board, all 16 boxes are completed. *)
Theorem all_edges_complete_all_boxes : forall (edges : list nat),
  (forall e, e < 40 -> In e edges) ->
  length (filter (is_box_completed_in edges) all_boxes) = 16.
Proof.
  intros edges Hall.
  rewrite filter_all_true.
  - reflexivity.
  - intros b Hb.
    apply all_edges_box_completed; [exact Hall|].
    unfold all_boxes in Hb. apply in_seq in Hb. lia.
Qed.

(** In any state where all 40 edges have been drawn and the score invariant holds,
    the sum of both players' scores is strictly 16. *)
Theorem terminal_score_sum_16 : forall (s : state),
  s_score1 s + s_score2 s = length (filter (is_box_completed s) all_boxes) ->
  (forall e, e < 40 -> In e (s_edges s)) ->
  s_score1 s + s_score2 s = 16.
Proof.
  intros s Hinv Hall.
  rewrite Hinv.
  unfold is_box_completed.
  apply all_edges_complete_all_boxes.
  exact Hall.
Qed.

End DABGame.
