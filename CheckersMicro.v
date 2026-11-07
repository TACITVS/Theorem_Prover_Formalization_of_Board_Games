(** **************************************************************************
    CheckersMicro.v: 4x4 Micro-Checkers (8-Square Lattice) in Rocq 9.1
    
    This module formalizes:
    1. 4x4 Checkers board topology on 8 dark squares {0 .. 7}.
    2. Rank, file, and dark square parity invariants on 8 squares.
    3. Step and jump transition graphs.
    4. Two-piece-per-player Micro-Checkers initial setup.
    5. Rank advancement and jump distance invariants on 4x4.
    
    Zero unproven axioms, zero admissions (Closed under global context).
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.

Section CheckersMicro.

Definition micro_num_squares : nat := 8.

Definition micro_rank (s : nat) : nat := s / 2.

Definition micro_col (s : nat) : nat :=
  match s with
  | 0 => 1
  | 1 => 3
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 0
  | 7 => 2
  | _ => 0
  end.

(** Theorem 1: All 8 squares lie within 4x4 grid bounds *)
Theorem micro_bounds : forall s : nat,
  s < 8 ->
  micro_rank s < 4 /\ micro_col s < 4.
Proof.
  intros s Hs.
  unfold micro_rank, micro_col.
  destruct s as [|[|[|[|[|[|[|[|?]]]]]]]]; simpl; split; lia.
Qed.

(** Theorem 2: Parity invariant on 4x4 grid *)
Theorem micro_parity : forall s : nat,
  s < 8 ->
  (micro_rank s + micro_col s) mod 2 = 1.
Proof.
  intros s Hs.
  destruct s as [|[|[|[|[|[|[|[|?]]]]]]]]; simpl; try reflexivity; lia.
Qed.

(** Step transitions *)
Definition micro_step_fl (s : nat) : option nat :=
  match s with
  | 0 => Some 2
  | 1 => Some 3
  | 3 => Some 4
  | 4 => Some 6
  | 5 => Some 7
  | _ => None
  end.

Definition micro_step_fr (s : nat) : option nat :=
  match s with
  | 0 => Some 3
  | 2 => Some 4
  | 3 => Some 5
  | 4 => Some 7
  | _ => None
  end.

Definition micro_step_bl (s : nat) : option nat :=
  match s with
  | 2 => Some 0
  | 3 => Some 1
  | 4 => Some 2
  | 6 => Some 4
  | 7 => Some 5
  | _ => None
  end.

Definition micro_step_br (s : nat) : option nat :=
  match s with
  | 3 => Some 0
  | 4 => Some 3
  | 5 => Some 3
  | 7 => Some 4
  | _ => None
  end.

(** Jump transitions *)
Definition micro_jump_fl (s : nat) : option (nat * nat) :=
  match s with
  | 1 => Some (3, 4)
  | 3 => Some (4, 6)
  | _ => None
  end.

Definition micro_jump_fr (s : nat) : option (nat * nat) :=
  match s with
  | 0 => Some (3, 5)
  | 2 => Some (4, 7)
  | _ => None
  end.

Definition micro_jump_bl (s : nat) : option (nat * nat) :=
  match s with
  | 5 => Some (3, 0)
  | 7 => Some (4, 2)
  | _ => None
  end.

Definition micro_jump_br (s : nat) : option (nat * nat) :=
  match s with
  | 4 => Some (3, 1)
  | 6 => Some (4, 3)
  | _ => None
  end.

(** Theorem 3: Forward steps increase micro_rank by exactly 1 *)
Theorem micro_step_fl_rank : forall s dst,
  micro_step_fl s = Some dst ->
  micro_rank dst = micro_rank s + 1.
Proof.
  intros s dst H.
  destruct s as [|[|[|[|[|[|[|[|?]]]]]]]]; simpl in H; try discriminate;
  injection H as Heq; subst dst; reflexivity.
Qed.

Theorem micro_step_fr_rank : forall s dst,
  micro_step_fr s = Some dst ->
  micro_rank dst = micro_rank s + 1.
Proof.
  intros s dst H.
  destruct s as [|[|[|[|[|[|[|[|?]]]]]]]]; simpl in H; try discriminate;
  injection H as Heq; subst dst; reflexivity.
Qed.

(** Theorem 4: Backward steps decrease micro_rank by exactly 1 *)
Theorem micro_step_bl_rank : forall s dst,
  micro_step_bl s = Some dst ->
  micro_rank s = micro_rank dst + 1.
Proof.
  intros s dst H.
  destruct s as [|[|[|[|[|[|[|[|?]]]]]]]]; simpl in H; try discriminate;
  injection H as Heq; subst dst; reflexivity.
Qed.

Theorem micro_step_br_rank : forall s dst,
  micro_step_br s = Some dst ->
  micro_rank s = micro_rank dst + 1.
Proof.
  intros s dst H.
  destruct s as [|[|[|[|[|[|[|[|?]]]]]]]]; simpl in H; try discriminate;
  injection H as Heq; subst dst; reflexivity.
Qed.

(** Theorem 5: All micro jumps strictly change rank by exactly 2 ranks *)
Theorem micro_jump_forward_rank : forall s mid dst,
  (micro_jump_fl s = Some (mid, dst) \/ micro_jump_fr s = Some (mid, dst)) ->
  micro_rank dst = micro_rank s + 2.
Proof.
  intros s mid dst [Hfl | Hfr].
  - destruct s as [|[|[|[|[|[|[|[|?]]]]]]]]; simpl in Hfl; try discriminate;
    injection Hfl as Hm Hd; subst mid dst; reflexivity.
  - destruct s as [|[|[|[|[|[|[|[|?]]]]]]]]; simpl in Hfr; try discriminate;
    injection Hfr as Hm Hd; subst mid dst; reflexivity.
Qed.

Theorem micro_jump_backward_rank : forall s mid dst,
  (micro_jump_bl s = Some (mid, dst) \/ micro_jump_br s = Some (mid, dst)) ->
  micro_rank s = micro_rank dst + 2.
Proof.
  intros s mid dst [Hbl | Hbr].
  - destruct s as [|[|[|[|[|[|[|[|?]]]]]]]]; simpl in Hbl; try discriminate;
    injection Hbl as Hm Hd; subst mid dst; reflexivity.
  - destruct s as [|[|[|[|[|[|[|[|?]]]]]]]]; simpl in Hbr; try discriminate;
    injection Hbr as Hm Hd; subst mid dst; reflexivity.
Qed.

(** Initial state for 4x4 Micro-Checkers: 2 pieces per player *)
Definition micro_initial_white_men : list nat := [0; 1].
Definition micro_initial_black_men : list nat := [6; 7].

Theorem micro_initial_piece_count :
  length micro_initial_white_men = 2 /\ length micro_initial_black_men = 2.
Proof.
  split; reflexivity.
Qed.

End CheckersMicro.
