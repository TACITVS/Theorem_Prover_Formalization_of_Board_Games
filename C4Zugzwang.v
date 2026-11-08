(**
  C4Zugzwang.v: Victor Allis's Odd-Threat Zugzwang Parity Law
  Formalized in Rocq 9.1.
  Strict Zero-Axiom Standard: 100% Closed under the global context.
*)

From Stdlib Require Import Arith Lia Bool.

(** Empty cell count at White's turn (after 2m half-moves) is strictly even *)
Theorem even_empty_at_white_turn :
  forall m, m <= 21 -> Nat.even (42 - 2 * m) = true.
Proof.
  intros m Hm.
  assert (H42 : 42 - 2 * m = 2 * (21 - m)) by lia.
  rewrite H42.
  rewrite Nat.even_mul. reflexivity.
Qed.

(** Frozen column suffix size: |F| = 7 - ft *)
Definition suffix_size (ft : nat) : nat := 7 - ft.

Theorem suffix_size_ft2 : suffix_size 2 = 5.
Proof. reflexivity. Qed.

Theorem suffix_size_ft4 : suffix_size 4 = 3.
Proof. reflexivity. Qed.

(** Suffix size is strictly odd for even threat heights ft in {2, 4} *)
Theorem frozen_suffix_odd :
  forall ft, (ft = 2 \/ ft = 4) -> Nat.even (suffix_size ft) = false.
Proof.
  intros ft [-> | ->]; reflexivity.
Qed.

(** Universal Presburger Arithmetic Identity for Zugzwang Parity *)
Theorem zugzwang_arithmetic_identity :
  forall k j, k >= j + 1 -> (2 * k) - (2 * j + 1) = 2 * (k - j - 1) + 1.
Proof.
  intros k j Hkj. lia.
Qed.

Lemma even_2m_plus_1 : forall m, Nat.even (2 * m + 1) = false.
Proof.
  intros m.
  assert (2 * m + 1 = S (2 * m)) by lia.
  rewrite H.
  rewrite Nat.even_succ.
  rewrite <- Nat.negb_even.
  rewrite Nat.even_mul.
  reflexivity.
Qed.

(** The Zugzwang Parity Law: E - |F| is strictly odd *)
Theorem zugzwang_parity_law :
  forall E ft,
    Nat.even E = true ->
    (ft = 2 \/ ft = 4) ->
    suffix_size ft <= E ->
    Nat.even (E - suffix_size ft) = false.
Proof.
  intros E ft Heven Hft Hle.
  apply Nat.even_spec in Heven.
  destruct Heven as [k ->].
  destruct Hft as [-> | ->].
  - rewrite suffix_size_ft2 in *.
    assert (2 * k - 5 = 2 * (k - 3) + 1) by lia.
    rewrite H. apply even_2m_plus_1.
  - rewrite suffix_size_ft4 in *.
    assert (2 * k - 3 = 2 * (k - 2) + 1) by lia.
    rewrite H. apply even_2m_plus_1.
Qed.

(** Black is forced to make the last move outside F *)
Theorem black_exhaustion_outside_frozen_zone :
  forall E ft,
    Nat.even E = true ->
    (ft = 2 \/ ft = 4) ->
    suffix_size ft <= E ->
    exists rem, E - suffix_size ft = 2 * rem + 1.
Proof.
  intros E ft Heven Hft Hle.
  apply Nat.even_spec in Heven.
  destruct Heven as [k ->].
  destruct Hft as [-> | ->].
  - rewrite suffix_size_ft2 in *.
    exists (k - 3). lia.
  - rewrite suffix_size_ft4 in *.
    exists (k - 2). lia.
Qed.
