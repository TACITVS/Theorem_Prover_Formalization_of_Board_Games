(******************************************************************************)
(* QUBIC-RESEARCH-013 - A genuine nonterminal, 10-round safe leaf                 *)
(* Requires the uploaded QUBIC-FINAL-001 QubicGame.v definitions.              *)
(* No result in this file proves Black can FORCE this position from empty.    *)
(* Rocq 9.1: rocq compile -Q . "" QubicGame.v                               *)
(*           rocq compile -Q . "" QUBIC-RESEARCH-013_safe10.v                     *)
(******************************************************************************)

From Stdlib Require Import List ZArith Bool Arith.
Require Import QubicGame.
Import ListNotations.
Open Scope Z_scope.

Definition Safe10_Black : list Point := [
  (-2, -2, -2);
  (-2, -2, 2);
  (-2, 2, 1);
  (-1, -1, -1);
  (-1, -1, 1);
  (0, 0, 0);
  (1, -1, 2);
  (1, 1, -1);
  (2, -2, -1);
  (2, 2, 2)
].

Definition Safe10_White : list Point := [
  (-1, 2, 2);
  (0, 2, 2);
  (1, -2, 2);
  (1, 2, 2);
  (2, -1, 2);
  (2, 0, 2);
  (2, 1, 1);
  (2, 1, 2);
  (2, 2, -1);
  (2, 2, 0)
].

Definition Safe10_Certificate : PairingCert := [
  (build_line5 (0, -2, 0) (1, 0, 0), ((-2, -2, 0), (2, -2, 0)));
  (build_line5 (0, -2, 1) (1, 0, 0), ((-2, -2, 1), (-1, -2, 1)));
  (build_line5 (0, -1, -2) (1, 0, 0), ((-2, -1, -2), (-1, -1, -2)));
  (build_line5 (0, -1, 0) (1, 0, 0), ((-1, -1, 0), (0, -1, 0)));
  (build_line5 (0, 0, -2) (1, 0, 0), ((0, 0, -2), (1, 0, -2)));
  (build_line5 (0, 0, -1) (1, 0, 0), ((-2, 0, -1), (0, 0, -1)));
  (build_line5 (0, 0, 1) (1, 0, 0), ((-2, 0, 1), (-1, 0, 1)));
  (build_line5 (0, 0, 2) (1, 0, 0), ((0, 0, 2), (1, 0, 2)));
  (build_line5 (0, 1, -2) (1, 0, 0), ((0, 1, -2), (1, 1, -2)));
  (build_line5 (0, 1, 0) (1, 0, 0), ((-2, 1, 0), (0, 1, 0)));
  (build_line5 (0, 1, 1) (1, 0, 0), ((-2, 1, 1), (1, 1, 1)));
  (build_line5 (0, 1, 2) (1, 0, 0), ((-1, 1, 2), (1, 1, 2)));
  (build_line5 (0, 2, -2) (1, 0, 0), ((-1, 2, -2), (1, 2, -2)));
  (build_line5 (0, 2, -1) (1, 0, 0), ((-2, 2, -1), (1, 2, -1)));
  (build_line5 (0, 2, 0) (1, 0, 0), ((-2, 2, 0), (0, 2, 0)));
  (build_line5 (-2, 0, -1) (0, 1, 0), ((-2, -2, -1), (-2, -1, -1)));
  (build_line5 (-2, 0, 0) (0, 1, 0), ((-2, -1, 0), (-2, 0, 0)));
  (build_line5 (-1, 0, -2) (0, 1, 0), ((-1, -2, -2), (-1, 0, -2)));
  (build_line5 (-1, 0, 0) (0, 1, 0), ((-1, 0, 0), (-1, 1, 0)));
  (build_line5 (-1, 0, 2) (0, 1, 0), ((-1, -2, 2), (-1, -1, 2)));
  (build_line5 (0, 0, -2) (0, 1, 0), ((0, -2, -2), (0, 2, -2)));
  (build_line5 (0, 0, -1) (0, 1, 0), ((0, -2, -1), (0, -1, -1)));
  (build_line5 (0, 0, 1) (0, 1, 0), ((0, -2, 1), (0, 0, 1)));
  (build_line5 (0, 0, 2) (0, 1, 0), ((0, -1, 2), (0, 1, 2)));
  (build_line5 (1, 0, -2) (0, 1, 0), ((1, -2, -2), (1, -1, -2)));
  (build_line5 (1, 0, 0) (0, 1, 0), ((1, -1, 0), (1, 1, 0)));
  (build_line5 (1, 0, 1) (0, 1, 0), ((1, -2, 1), (1, -1, 1)));
  (build_line5 (2, 0, -2) (0, 1, 0), ((2, 1, -2), (2, 2, -2)));
  (build_line5 (2, 0, 0) (0, 1, 0), ((2, -1, 0), (2, 0, 0)));
  (build_line5 (2, 0, 1) (0, 1, 0), ((2, -2, 1), (2, 0, 1)));
  (build_line5 (-2, -1, 0) (0, 0, 1), ((-2, -1, 1), (-2, -1, 2)));
  (build_line5 (-2, 0, 0) (0, 0, 1), ((-2, 0, -2), (-2, 0, 2)));
  (build_line5 (-2, 1, 0) (0, 0, 1), ((-2, 1, -1), (-2, 1, 2)));
  (build_line5 (-1, -2, 0) (0, 0, 1), ((-1, -2, -1), (-1, -2, 0)));
  (build_line5 (-1, 0, 0) (0, 0, 1), ((-1, 0, -1), (-1, 0, 2)));
  (build_line5 (-1, 1, 0) (0, 0, 1), ((-1, 1, -2), (-1, 1, 1)));
  (build_line5 (-1, 2, 0) (0, 0, 1), ((-1, 2, -1), (-1, 2, 0)));
  (build_line5 (0, -2, 0) (0, 0, 1), ((0, -2, 0), (0, -2, 2)));
  (build_line5 (0, -1, 0) (0, 0, 1), ((0, -1, -2), (0, -1, 1)));
  (build_line5 (0, 1, 0) (0, 0, 1), ((0, 1, -1), (0, 1, 1)));
  (build_line5 (0, 2, 0) (0, 0, 1), ((0, 2, -1), (0, 2, 1)));
  (build_line5 (1, -2, 0) (0, 0, 1), ((1, -2, -1), (1, -2, 0)));
  (build_line5 (1, 0, 0) (0, 0, 1), ((1, 0, -1), (1, 0, 1)));
  (build_line5 (1, 2, 0) (0, 0, 1), ((1, 2, 0), (1, 2, 1)));
  (build_line5 (2, -1, 0) (0, 0, 1), ((2, -1, -2), (2, -1, -1)));
  (build_line5 (2, 0, 0) (0, 0, 1), ((2, 0, -2), (2, 0, -1)));
  (build_line5 (2, 1, 0) (0, 0, 1), ((2, 1, -1), (2, 1, 0)));
  (build_line5 (0, 0, -2) (1, -1, 0), ((-2, 2, -2), (2, -2, -2)));
  (build_line5 (0, 1, 0) (1, 0, 1), ((-2, 1, -2), (-1, 1, -1)));
  (build_line5 (0, 2, 0) (1, 0, -1), ((-2, 2, 2), (-1, 2, 1)));
  (build_line5 (1, 0, 0) (0, 1, 1), ((1, -1, -1), (1, 0, 0)));
  (build_line5 (2, 0, 0) (0, 1, -1), ((2, -2, 2), (2, -1, 1)))
].

(* Every statement below is a finite equality checked by the Rocq kernel
   once the source has been compiled successfully. *)

Theorem Safe10_Finite_Census :
  length Safe10_Black = 10%nat /\
  length Safe10_White = 10%nat /\
  length Lines109 = 109%nat /\
  length Safe10_Certificate = 52%nat /\
  length (lines_hit_by Safe10_Black Lines109) = 57%nat /\
  length (surviving_lines Safe10_Black Lines109) = 52%nat /\
  length (cert_endpoints Safe10_Certificate) = 104%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem Safe10_Valid_Board :
  nodupb Safe10_Black = true /\
  nodupb Safe10_White = true /\
  nodupb (cert_endpoints Safe10_Certificate) = true /\
  subset_points Safe10_Black V5 = true /\
  subset_points Safe10_White V5 = true /\
  forallb (fun p => negb (mem_point p Safe10_Black)) Safe10_White = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem Safe10_No_Terminal_Win :
  has_winning_line Lines109 Safe10_Black = false /\
  has_winning_line Lines109 Safe10_White = false.
Proof. vm_compute. split; reflexivity. Qed.

Theorem Safe10_Valid_Pairs_Bool :
  forallb (fun '(e,(p,q)) =>
    valid_free_pair_for_line Safe10_White Safe10_Black e p q)
    Safe10_Certificate = true.
Proof. vm_compute. reflexivity. Qed.

Theorem Safe10_Full109_Coverage_Bool :
  forallb (fun e =>
    line_hit_by Safe10_Black e || line_in_cert e Safe10_Certificate)
    Lines109 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem Safe10_ValidPairingState :
  ValidPairingState Safe10_White Safe10_Black Lines109 Safe10_Certificate.
Proof.
  constructor.
  - intros p HpW HpB.
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 Safe10_Valid_Board))))) as Hd.
    rewrite forallb_forall in Hd.
    specialize (Hd p HpW).
    apply mem_point_In in HpB.
    rewrite HpB in Hd; discriminate.
  - intros e p q Hin.
    pose proof Safe10_Valid_Pairs_Bool as Hv.
    rewrite forallb_forall in Hv.
    exact (Hv (e,(p,q)) Hin).
  - apply nodupb_NoDup.
    exact (proj1 (proj2 (proj2 Safe10_Valid_Board))).
  - intros e He.
    pose proof Safe10_Full109_Coverage_Bool as Hcov.
    rewrite forallb_forall in Hcov.
    specialize (Hcov e He).
    apply orb_true_iff in Hcov.
    destruct Hcov as [Hhit | Hfound].
    + left; exact Hhit.
    + right; apply line_in_cert_spec; exact Hfound.
Qed.

Theorem Safe10_Permanent109_Conditional :
  forall n : nat,
    SafeForNRounds n Safe10_White Safe10_Black Lines109.
Proof.
  intros n.
  eapply Permanent_Pairing_Defense_Theorem.
  exact Safe10_ValidPairingState.
Qed.

Theorem Original85_Core_Already_Wins :
  has_winning_line Lines109 OptimalCore17_85 = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions Safe10_Permanent109_Conditional.
Print Assumptions Original85_Core_Already_Wins.
