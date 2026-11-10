From Stdlib Require Import List Arith Bool Lia.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Minimax RulesFacts SymmetryGame.
Import ListNotations.

Definition represents (c representative : cell) : bool :=
  existsb (fun iso => forward iso c =? representative) cube_symmetries.

Lemma unique_representative_check :
  forallb (fun c => length (filter (represents c) opening_representatives) =? 1) all_cells = true.
Proof. vm_compute. reflexivity. Qed.

Theorem exactly_one_opening_representative : forall c,
  c < 125 -> length (filter (represents c) opening_representatives) = 1.
Proof.
  intros c Hc. pose proof unique_representative_check as H.
  apply forallb_forall with (x := c) in H; [apply Nat.eqb_eq; exact H|apply in_seq; lia].
Qed.

Definition orbit_size (c : cell) : nat :=
  length (filter (fun d => represents c d) all_cells).

Theorem ten_orbit_sizes :
  map orbit_size opening_representatives = [8;24;12;24;24;6;8;12;6;1].
Proof. vm_compute. reflexivity. Qed.

(** Transforming an occupied raw request does NOT transform its fallback.
    The full-game theorem instead transports the effective legal move. *)
Theorem fallback_does_not_commute_with_reflection :
  effective_move (transport rx (opening_state 0)) (forward rx 0) = 0 /\
  forward rx (effective_move (opening_state 0) 0) = 3.
Proof. vm_compute. split; reflexivity. Qed.

Theorem reversing_line_orientation_preserves_win :
  map (forward rx) [0;1;2;3;4] = [4;3;2;1;0] /\
  has_win (map (forward rx) [0;1;2;3;4]) = true.
Proof. vm_compute. split; reflexivity. Qed.
