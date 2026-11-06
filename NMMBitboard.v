(* ============================================================================== *)
(* NMMBitboard.v - Verified 24-Bit Bitboard Representation and Reflection         *)
(* Complete correspondence between list-based semantics and bitmask operations   *)
(* Verified for Rocq 9.1 with ZERO unproven axioms.                              *)
(* ============================================================================== *)

From Stdlib Require Import List Arith Bool Lia PeanoNat NArith.
Import ListNotations.
Require Import NMM.NMMGraph.
Require Import NMM.NMMGame.
Require Import NMM.NMMInvariants.

Section NMMBitboards.

Open Scope N_scope.

(** 16 Precomputed Mill Bitmasks *)
Definition MILL_MASKS : list N :=
  [ 7%N; 28%N; 112%N; 193%N;
    1792%N; 7168%N; 28672%N; 49408%N;
    458752%N; 1835008%N; 7340032%N; 12648448%N;
    131586%N; 526344%N; 2105376%N; 8421504%N
  ].

Lemma mill_masks_count : length MILL_MASKS = 16%nat.
Proof. reflexivity. Qed.

(** Conversion of a mill to its exact bitmask *)
Definition mill_mask_of (m : mill) : N :=
  let '(a, b, c) := m in
  N.lor (N.shiftl 1 (N.of_nat a))
        (N.lor (N.shiftl 1 (N.of_nat b))
               (N.shiftl 1 (N.of_nat c))).

(** Verification of all 16 masks against the analytical definition *)
Theorem mill_masks_exact :
  map mill_mask_of all_mills = MILL_MASKS.
Proof. reflexivity. Qed.

(** Bitboard representation of a list of stone coordinates *)
Fixpoint stones_to_bitboard (stones : list nat) : N :=
  match stones with
  | [] => 0%N
  | p :: rest => N.lor (N.shiftl 1 (N.of_nat p)) (stones_to_bitboard rest)
  end.

Lemma testbit_1 : forall m : N, N.testbit 1 m = (m =? 0)%N.
Proof. destruct m; simpl; reflexivity. Qed.

(** Fundamental Bitboard Lemma: bit n is set iff n is in the stone list *)
Theorem testbit_stones_to_bitboard : forall stones p,
  (p < 24)%nat ->
  N.testbit (stones_to_bitboard stones) (N.of_nat p) = in_nat_list p stones.
Proof.
  intros stones p Hp.
  induction stones as [| s rest IH].
  - simpl. reflexivity.
  - change (stones_to_bitboard (s :: rest)) with
      (N.lor (N.shiftl 1 (N.of_nat s)) (stones_to_bitboard rest)).
    rewrite N.lor_spec.
    rewrite IH.
    simpl in_nat_list.
    destruct (p =? s)%nat eqn:Eps.
    + apply Nat.eqb_eq in Eps; subst.
      rewrite N.shiftl_spec_high'; [| lia].
      rewrite N.sub_diag.
      rewrite testbit_1.
      simpl. reflexivity.
    + apply Nat.eqb_neq in Eps.
      assert (Hbit : N.testbit (N.shiftl 1 (N.of_nat s)) (N.of_nat p) = false).
      {
        destruct (N.of_nat p <? N.of_nat s)%N eqn:Elt.
        - apply N.ltb_lt in Elt.
          apply N.shiftl_spec_low; lia.
        - apply N.ltb_ge in Elt.
          rewrite N.shiftl_spec_high'; [| lia].
          rewrite testbit_1.
          apply N.eqb_neq.
          intros Hzero. apply Eps.
          apply Nat2N.inj. lia.
      }
      rewrite Hbit. simpl. reflexivity.
Qed.

(** Bitboard mill test via testbit *)
Definition bitboard_mill_check (bb : N) (m : mill) : bool :=
  let '(a, b, c) := m in
  N.testbit bb (N.of_nat a) &&
  N.testbit bb (N.of_nat b) &&
  N.testbit bb (N.of_nat c).

(** Exact Soundness and Completeness of Bitboard Mill Checking *)
Theorem bitboard_mill_reflection : forall stones m,
  let '(a, b, c) := m in
  (a < 24 /\ b < 24 /\ c < 24)%nat ->
  is_mill_complete stones m =
  bitboard_mill_check (stones_to_bitboard stones) m.
Proof.
  intros stones [ [a b] c ] [Ha [Hb Hc]].
  unfold is_mill_complete, bitboard_mill_check.
  rewrite (testbit_stones_to_bitboard stones a Ha).
  rewrite (testbit_stones_to_bitboard stones b Hb).
  rewrite (testbit_stones_to_bitboard stones c Hc).
  reflexivity.
Qed.

Close Scope N_scope.

End NMMBitboards.
