(** **************************************************************************
    MNKPhaseTransition.v: The (3, n, 3) Sharp Phase Transition and the
    First-Player Wins of the (m, n, 3) Family -- Machine-Checked

    Proves (all statements are about the strong / maker-maker game, in which
    the first player to complete a line wins; see [forces_win] in MNKGame.v):
    1. (3, 3, 3) is a DRAW: neither player can force a win ([mnk_3_3_3_draw]).
    2. (3, 4, 3) is a first-player win in at most 7 plies, and NOT within
       5 plies ([mnk_3_4_3_exactly_7_plies]).  The original 132-node
       certificate is re-checked by the corrected (sound) checker.
    3. The former "Subgrid Monotone Projection" argument is FALSE: replaying the
       3 x 4 strategy on a 3 x 5 board lets Player 2 complete a line that
       crosses the boundary of the 3 x 4 core
       ([subgrid_projection_counterexample_3_5_3]).
    4. Correct replacement via the Window Simulation Theorem (MNKWindow.v):
       - (3, n, 3) is a first-player win within 7 plies for EVERY n >= 4;
       - (m, 3, 3) is a first-player win within 7 plies for EVERY m >= 4;
       - (m, n, 3) is a first-player win within 5 plies for all m, n >= 4.
    5. [sharp_phase_transition_3_n_3], [mnk_k3_first_player_wins] and the
       complete characterization of all (m, n, 3) games
       [mnk_k3_complete_characterization] (draws via MNKPairing.v).

    Zero axioms, zero admissions (closed under the global context).
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool PeanoNat.
Import ListNotations.
Require Import MNK.MNKBoard.
Require Import MNK.MNKGame.
Require Import MNK.MNKCertChecker.
Require Import MNK.MNKWindow.
Require Import MNK.MNKPairing.

(* ========================================================================= *)
(** * 1. (3, 3, 3) is a draw                                                  *)
(* ========================================================================= *)

Theorem mnk_3_3_3_draw : game_is_draw (gen_lines 3 3 3) (empty_board 9).
Proof.
  split.
  - apply no_forced_win_by_evaluation. vm_compute. reflexivity.
  - intros d [_ H].
    destruct (H 4 ltac:(vm_compute; reflexivity)) as [_ Hw].
    revert Hw. apply no_forced_win_by_evaluation. vm_compute. reflexivity.
Qed.

(* ========================================================================= *)
(** * 2. (3, 4, 3): the original 132-node certificate, re-checked soundly     *)
(* ========================================================================= *)

Definition cert_3_4_3 : cert :=
  Br 1
    (BCons 0 (Br 2
      (BCons 3 (Br 5
        (BCons 4 (Imm 8)
        (BCons 6 (Imm 8)
        (BCons 7 (Imm 8)
        (BCons 8 (Imm 9)
        (BCons 9 (Imm 8)
        (BCons 10 (Imm 8)
        (BCons 11 (Imm 8)
        BNil))))))))
      (BCons 4 (Imm 3)
      (BCons 5 (Imm 3)
      (BCons 6 (Imm 3)
      (BCons 7 (Imm 3)
      (BCons 8 (Imm 3)
      (BCons 9 (Imm 3)
      (BCons 10 (Imm 3)
      (BCons 11 (Imm 3)
      BNil))))))))))
    (BCons 2 (Br 5
      (BCons 0 (Imm 9)
      (BCons 3 (Imm 9)
      (BCons 4 (Imm 9)
      (BCons 6 (Imm 9)
      (BCons 7 (Imm 9)
      (BCons 8 (Imm 9)
      (BCons 9 (Br 6
        (BCons 0 (Imm 4)
        (BCons 3 (Imm 4)
        (BCons 4 (Imm 7)
        (BCons 7 (Imm 4)
        (BCons 8 (Imm 4)
        (BCons 10 (Imm 4)
        (BCons 11 (Imm 4)
        BNil))))))))
      (BCons 10 (Imm 9)
      (BCons 11 (Imm 9)
      BNil))))))))))
    (BCons 3 (Br 0
      (BCons 2 (Br 5
        (BCons 4 (Imm 9)
        (BCons 6 (Imm 9)
        (BCons 7 (Imm 9)
        (BCons 8 (Imm 9)
        (BCons 9 (Imm 10)
        (BCons 10 (Imm 9)
        (BCons 11 (Imm 9)
        BNil))))))))
      (BCons 4 (Imm 2)
      (BCons 5 (Imm 2)
      (BCons 6 (Imm 2)
      (BCons 7 (Imm 2)
      (BCons 8 (Imm 2)
      (BCons 9 (Imm 2)
      (BCons 10 (Imm 2)
      (BCons 11 (Imm 2)
      BNil))))))))))
    (BCons 4 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      BNil))))))))))
    (BCons 5 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      BNil))))))))))
    (BCons 6 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      BNil))))))))))
    (BCons 7 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      BNil))))))))))
    (BCons 8 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      BNil))))))))))
    (BCons 9 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      BNil))))))))))
    (BCons 10 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 11 (Imm 0)
      BNil))))))))))
    (BCons 11 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      BNil))))))))))
    BNil))))))))))).

(** Checked under strong-game rules: every P2 reply covered, P2 never
    completes a line, Player 1 wins within 4 of its own moves (7 plies). *)
Theorem win_3_4_3_certified :
  check_cert (gen_lines 3 4 3) P1 4 (initial_board 12) cert_3_4_3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_3_4_3_first_player_win :
  forces_win (gen_lines 3 4 3) P1 4 (empty_board 12).
Proof. exact (check_cert_sound _ _ _ _ _ win_3_4_3_certified). Qed.

(** 7 plies is optimal on 3 x 4: no forced win within 3 own moves (5 plies). *)
Theorem mnk_3_4_3_no_win_within_5_plies :
  ~ forces_win (gen_lines 3 4 3) P1 3 (empty_board 12).
Proof.
  intros H. apply wins_b_spec in H. vm_compute in H. discriminate.
Qed.

Theorem mnk_3_4_3_exactly_7_plies :
  forces_win (gen_lines 3 4 3) P1 4 (empty_board 12) /\
  ~ forces_win (gen_lines 3 4 3) P1 3 (empty_board 12).
Proof.
  split; [exact mnk_3_4_3_first_player_win | exact mnk_3_4_3_no_win_within_5_plies].
Qed.

(* ========================================================================= *)
(** * 3. Refutation of the former "Subgrid Monotone Projection" argument     *)
(* ========================================================================= *)

(** The embedding of 3 x 4 indices into a 3 x n board (unchanged). *)
Definition embed_34_into_3n (n : nat) (idx_34 : nat) : nat :=
  let r := idx_34 / 4 in
  let c := idx_34 mod 4 in
  r * n + c.

Theorem embed_in_bounds : forall n idx,
  4 <= n ->
  idx < 12 ->
  embed_34_into_3n n idx < 3 * n.
Proof.
  intros n idx Hn Hidx.
  unfold embed_34_into_3n.
  assert (Hr : idx / 4 < 3) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hc : idx mod 4 < 4) by (apply Nat.mod_upper_bound; lia).
  nia.
Qed.

Theorem embed_injective : forall n idx1 idx2,
  4 <= n ->
  idx1 < 12 ->
  idx2 < 12 ->
  embed_34_into_3n n idx1 = embed_34_into_3n n idx2 ->
  idx1 = idx2.
Proof.
  intros n idx1 idx2 Hn H1 H2 Heq.
  assert (Hc1 : idx1 mod 4 < n) by (assert (idx1 mod 4 < 4) by (apply Nat.mod_upper_bound; lia); lia).
  assert (Hc2 : idx2 mod 4 < n) by (assert (idx2 mod 4 < 4) by (apply Nat.mod_upper_bound; lia); lia).
  unfold embed_34_into_3n in Heq.
  assert (Hdiv : idx1 / 4 = idx2 / 4).
  { rewrite <- (idx_div n (idx1 / 4) (idx1 mod 4) Hc1).
    rewrite <- (idx_div n (idx2 / 4) (idx2 mod 4) Hc2). rewrite Heq. reflexivity. }
  assert (Hmod : idx1 mod 4 = idx2 mod 4).
  { rewrite <- (idx_mod n (idx1 / 4) (idx1 mod 4) Hc1).
    rewrite <- (idx_mod n (idx2 / 4) (idx2 mod 4) Hc2). rewrite Heq. reflexivity. }
  rewrite (Nat.div_mod_eq idx1 4), (Nat.div_mod_eq idx2 4).
  rewrite Hdiv, Hmod. reflexivity.
Qed.

Definition embed_line (n : nat) (l : list nat) : list nat :=
  map (embed_34_into_3n n) l.

Theorem embed_line_length : forall n l,
  length (embed_line n l) = length l.
Proof.
  intros n l. unfold embed_line. apply length_map.
Qed.

(** Replay a move sequence, rejecting illegal moves. *)
Fixpoint play (b : board_t) (moves : list (nat * player)) : option board_t :=
  match moves with
  | [] => Some b
  | (x, pl) :: rest => if is_legal_move b x then play (set_cell b x pl) rest else None
  end.

(** Board after P1: 1, P2: 3, P1: 0, P2: 2, P1: 6 on 3 x 5, i.e. after Player 1
    follows [cert_3_4_3] (moves 1, 0, 5 on 3 x 4, embedded as 1, 0, 6). *)
Definition projected_board_3_5 : board_t :=
  set_cell (set_cell (set_cell (set_cell (set_cell (empty_board 15)
    1 P1) 3 P2) 0 P1) 2 P2) 6 P1.

(** Counterexample: on 3 x 5, Player 2 answers 6 with cell 4 = (0, 4) and
    completes the line (0,2)-(0,3)-(0,4) at ply 6, BEFORE Player 1's planned
    winning move at ply 7.  Cell (0, 4) lies outside the 3 x 4 core, yet the
    line through it meets the core: exterior moves are not "dummy" moves. *)
Theorem subgrid_projection_counterexample_3_5_3 :
  cert_move cert_3_4_3 [] = Some 1 /\
  cert_move cert_3_4_3 [3] = Some 0 /\
  cert_move cert_3_4_3 [3; 2] = Some 5 /\
  map (embed_34_into_3n 5) [1; 3; 0; 2; 5] = [1; 3; 0; 2; 6] /\
  play (empty_board 15) [(1, P1); (3, P2); (0, P1); (2, P2); (6, P1)] =
    Some projected_board_3_5 /\
  check_win projected_board_3_5 P1 (gen_lines 3 5 3) = false /\
  check_win projected_board_3_5 P2 (gen_lines 3 5 3) = false /\
  is_legal_move projected_board_3_5 4 = true /\
  check_win (set_cell projected_board_3_5 4 P2) P2 (gen_lines 3 5 3) = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Consequently the old certificate does not certify (3, 5, 3): its
    embedding is rejected by the checker. *)
Fixpoint embed_cert (n : nat) (ct : cert) : cert :=
  match ct with
  | Imm m => Imm (embed_34_into_3n n m)
  | Br m bs => Br (embed_34_into_3n n m) (embed_branches n bs)
  end
with embed_branches (n : nat) (bs : branches) : branches :=
  match bs with
  | BNil => BNil
  | BCons c sub rest =>
      BCons (embed_34_into_3n n c) (embed_cert n sub) (embed_branches n rest)
  end.

Theorem projected_cert_rejected_3_5_3 :
  check_cert (gen_lines 3 5 3) P1 4 (empty_board 15) (embed_cert 5 cert_3_4_3) = false.
Proof. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(** * 4. Window certificates and the universal theorems                      *)
(* ========================================================================= *)

(** 3 x 4 window in a 3 x n board; replies in columns >= 4 are "far". *)
Definition cert_strip : cert :=
  Br 1
    (BCons 0 (Br 2
      (BCons 3 (Br 5
        (BCons 4 (Imm 8)
        (BCons 6 (Imm 8)
        (BCons 7 (Imm 8)
        (BCons 8 (Imm 9)
        (BCons 9 (Imm 8)
        (BCons 10 (Imm 8)
        (BCons 11 (Imm 8)
        (BCons 12 (Imm 8)
        BNil)))))))))
      (BCons 4 (Imm 3)
      (BCons 5 (Imm 3)
      (BCons 6 (Imm 3)
      (BCons 7 (Imm 3)
      (BCons 8 (Imm 3)
      (BCons 9 (Imm 3)
      (BCons 10 (Imm 3)
      (BCons 11 (Imm 3)
      (BCons 12 (Imm 3)
      BNil)))))))))))
    (BCons 2 (Br 5
      (BCons 0 (Imm 9)
      (BCons 3 (Imm 9)
      (BCons 4 (Imm 9)
      (BCons 6 (Imm 9)
      (BCons 7 (Imm 9)
      (BCons 8 (Imm 9)
      (BCons 9 (Br 6
        (BCons 0 (Imm 4)
        (BCons 3 (Imm 4)
        (BCons 4 (Imm 7)
        (BCons 7 (Imm 4)
        (BCons 8 (Imm 4)
        (BCons 10 (Imm 4)
        (BCons 11 (Imm 4)
        (BCons 12 (Imm 4)
        BNil)))))))))
      (BCons 10 (Imm 9)
      (BCons 11 (Imm 9)
      (BCons 12 (Imm 9)
      BNil)))))))))))
    (BCons 3 (Br 2
      (BCons 0 (Br 5
        (BCons 4 (Imm 8)
        (BCons 6 (Imm 8)
        (BCons 7 (Imm 8)
        (BCons 8 (Imm 9)
        (BCons 9 (Imm 8)
        (BCons 10 (Imm 8)
        (BCons 11 (Imm 8)
        (BCons 12 (Imm 8)
        BNil)))))))))
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 4 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 5 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 6 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 7 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 8 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 9 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 10 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 11 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 12 (Br 2
      (BCons 0 (Imm 3)
      (BCons 3 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 6 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil))))))))))))
    BNil)))))))))))).

Theorem cert_strip_valid :
  wcheck 3 4 3 false true 4 (empty_board 12) 0 cert_strip = true.
Proof. vm_compute. reflexivity. Qed.

(** 4 x 3 window in an m x 3 board; replies in rows >= 4 are "far". *)
Definition cert_tall : cert :=
  Br 3
    (BCons 0 (Br 4
      (BCons 1 (Imm 5)
      (BCons 2 (Imm 5)
      (BCons 5 (Br 6
        (BCons 1 (Imm 2)
        (BCons 2 (Imm 9)
        (BCons 7 (Imm 2)
        (BCons 8 (Imm 2)
        (BCons 9 (Imm 2)
        (BCons 10 (Imm 2)
        (BCons 11 (Imm 2)
        (BCons 12 (Imm 2)
        BNil)))))))))
      (BCons 6 (Imm 5)
      (BCons 7 (Imm 5)
      (BCons 8 (Imm 5)
      (BCons 9 (Imm 5)
      (BCons 10 (Imm 5)
      (BCons 11 (Imm 5)
      (BCons 12 (Imm 5)
      BNil)))))))))))
    (BCons 1 (Br 6
      (BCons 0 (Imm 9)
      (BCons 2 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 2 (Br 6
      (BCons 0 (Imm 9)
      (BCons 1 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 4 (Br 6
      (BCons 0 (Imm 9)
      (BCons 1 (Imm 0)
      (BCons 2 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 5 (Br 6
      (BCons 0 (Imm 9)
      (BCons 1 (Imm 0)
      (BCons 2 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 6 (Br 4
      (BCons 0 (Imm 5)
      (BCons 1 (Imm 5)
      (BCons 2 (Imm 5)
      (BCons 5 (Br 7
        (BCons 0 (Imm 1)
        (BCons 1 (Imm 10)
        (BCons 2 (Imm 1)
        (BCons 8 (Imm 1)
        (BCons 9 (Imm 1)
        (BCons 10 (Imm 1)
        (BCons 11 (Imm 1)
        (BCons 12 (Imm 1)
        BNil)))))))))
      (BCons 7 (Imm 5)
      (BCons 8 (Imm 5)
      (BCons 9 (Imm 5)
      (BCons 10 (Imm 5)
      (BCons 11 (Imm 5)
      (BCons 12 (Imm 5)
      BNil)))))))))))
    (BCons 7 (Br 6
      (BCons 0 (Imm 9)
      (BCons 1 (Imm 0)
      (BCons 2 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 8 (Br 6
      (BCons 0 (Imm 9)
      (BCons 1 (Imm 0)
      (BCons 2 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 9 (Br 4
      (BCons 0 (Imm 5)
      (BCons 1 (Imm 5)
      (BCons 2 (Imm 5)
      (BCons 5 (Br 7
        (BCons 0 (Imm 1)
        (BCons 1 (Imm 10)
        (BCons 2 (Imm 1)
        (BCons 6 (Imm 1)
        (BCons 8 (Imm 1)
        (BCons 10 (Imm 1)
        (BCons 11 (Imm 1)
        (BCons 12 (Imm 1)
        BNil)))))))))
      (BCons 6 (Imm 5)
      (BCons 7 (Imm 5)
      (BCons 8 (Imm 5)
      (BCons 10 (Imm 5)
      (BCons 11 (Imm 5)
      (BCons 12 (Imm 5)
      BNil)))))))))))
    (BCons 10 (Br 6
      (BCons 0 (Imm 9)
      (BCons 1 (Imm 0)
      (BCons 2 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 11 (Br 6
      (BCons 0 (Imm 9)
      (BCons 1 (Imm 0)
      (BCons 2 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 12 (Imm 0)
      BNil)))))))))))
    (BCons 12 (Br 6
      (BCons 0 (Imm 9)
      (BCons 1 (Imm 0)
      (BCons 2 (Imm 0)
      (BCons 4 (Imm 0)
      (BCons 5 (Imm 0)
      (BCons 7 (Imm 0)
      (BCons 8 (Imm 0)
      (BCons 9 (Imm 0)
      (BCons 10 (Imm 0)
      (BCons 11 (Imm 0)
      (BCons 12 (Imm 0)
      BNil))))))))))))
    BNil)))))))))))).

Theorem cert_tall_valid :
  wcheck 4 3 3 true false 4 (empty_board 12) 0 cert_tall = true.
Proof. vm_compute. reflexivity. Qed.

(** 4 x 4 corner window in an m x n board (m, n >= 4). *)
Definition cert_corner : cert :=
  Br 5
    (BCons 0 (Br 6
      (BCons 1 (Imm 4)
      (BCons 2 (Imm 4)
      (BCons 3 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 8 (Imm 4)
      (BCons 9 (Imm 4)
      (BCons 10 (Imm 4)
      (BCons 11 (Imm 4)
      (BCons 12 (Imm 4)
      (BCons 13 (Imm 4)
      (BCons 14 (Imm 4)
      (BCons 15 (Imm 4)
      (BCons 16 (Imm 4)
      BNil)))))))))))))))
    (BCons 1 (Br 6
      (BCons 0 (Imm 4)
      (BCons 2 (Imm 4)
      (BCons 3 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 8 (Imm 4)
      (BCons 9 (Imm 4)
      (BCons 10 (Imm 4)
      (BCons 11 (Imm 4)
      (BCons 12 (Imm 4)
      (BCons 13 (Imm 4)
      (BCons 14 (Imm 4)
      (BCons 15 (Imm 4)
      (BCons 16 (Imm 4)
      BNil)))))))))))))))
    (BCons 2 (Br 6
      (BCons 0 (Imm 4)
      (BCons 1 (Imm 4)
      (BCons 3 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 8 (Imm 4)
      (BCons 9 (Imm 4)
      (BCons 10 (Imm 4)
      (BCons 11 (Imm 4)
      (BCons 12 (Imm 4)
      (BCons 13 (Imm 4)
      (BCons 14 (Imm 4)
      (BCons 15 (Imm 4)
      (BCons 16 (Imm 4)
      BNil)))))))))))))))
    (BCons 3 (Br 6
      (BCons 0 (Imm 4)
      (BCons 1 (Imm 4)
      (BCons 2 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 8 (Imm 4)
      (BCons 9 (Imm 4)
      (BCons 10 (Imm 4)
      (BCons 11 (Imm 4)
      (BCons 12 (Imm 4)
      (BCons 13 (Imm 4)
      (BCons 14 (Imm 4)
      (BCons 15 (Imm 4)
      (BCons 16 (Imm 4)
      BNil)))))))))))))))
    (BCons 4 (Br 9
      (BCons 0 (Imm 1)
      (BCons 1 (Imm 13)
      (BCons 2 (Imm 1)
      (BCons 3 (Imm 1)
      (BCons 6 (Imm 1)
      (BCons 7 (Imm 1)
      (BCons 8 (Imm 1)
      (BCons 10 (Imm 1)
      (BCons 11 (Imm 1)
      (BCons 12 (Imm 1)
      (BCons 13 (Imm 1)
      (BCons 14 (Imm 1)
      (BCons 15 (Imm 1)
      (BCons 16 (Imm 1)
      BNil)))))))))))))))
    (BCons 6 (Br 9
      (BCons 0 (Imm 1)
      (BCons 1 (Imm 13)
      (BCons 2 (Imm 1)
      (BCons 3 (Imm 1)
      (BCons 4 (Imm 1)
      (BCons 7 (Imm 1)
      (BCons 8 (Imm 1)
      (BCons 10 (Imm 1)
      (BCons 11 (Imm 1)
      (BCons 12 (Imm 1)
      (BCons 13 (Imm 1)
      (BCons 14 (Imm 1)
      (BCons 15 (Imm 1)
      (BCons 16 (Imm 1)
      BNil)))))))))))))))
    (BCons 7 (Br 9
      (BCons 0 (Imm 1)
      (BCons 1 (Imm 13)
      (BCons 2 (Imm 1)
      (BCons 3 (Imm 1)
      (BCons 4 (Imm 1)
      (BCons 6 (Imm 1)
      (BCons 8 (Imm 1)
      (BCons 10 (Imm 1)
      (BCons 11 (Imm 1)
      (BCons 12 (Imm 1)
      (BCons 13 (Imm 1)
      (BCons 14 (Imm 1)
      (BCons 15 (Imm 1)
      (BCons 16 (Imm 1)
      BNil)))))))))))))))
    (BCons 8 (Br 6
      (BCons 0 (Imm 4)
      (BCons 1 (Imm 4)
      (BCons 2 (Imm 4)
      (BCons 3 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 9 (Imm 4)
      (BCons 10 (Imm 4)
      (BCons 11 (Imm 4)
      (BCons 12 (Imm 4)
      (BCons 13 (Imm 4)
      (BCons 14 (Imm 4)
      (BCons 15 (Imm 4)
      (BCons 16 (Imm 4)
      BNil)))))))))))))))
    (BCons 9 (Br 6
      (BCons 0 (Imm 4)
      (BCons 1 (Imm 4)
      (BCons 2 (Imm 4)
      (BCons 3 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 8 (Imm 4)
      (BCons 10 (Imm 4)
      (BCons 11 (Imm 4)
      (BCons 12 (Imm 4)
      (BCons 13 (Imm 4)
      (BCons 14 (Imm 4)
      (BCons 15 (Imm 4)
      (BCons 16 (Imm 4)
      BNil)))))))))))))))
    (BCons 10 (Br 6
      (BCons 0 (Imm 4)
      (BCons 1 (Imm 4)
      (BCons 2 (Imm 4)
      (BCons 3 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 8 (Imm 4)
      (BCons 9 (Imm 4)
      (BCons 11 (Imm 4)
      (BCons 12 (Imm 4)
      (BCons 13 (Imm 4)
      (BCons 14 (Imm 4)
      (BCons 15 (Imm 4)
      (BCons 16 (Imm 4)
      BNil)))))))))))))))
    (BCons 11 (Br 6
      (BCons 0 (Imm 4)
      (BCons 1 (Imm 4)
      (BCons 2 (Imm 4)
      (BCons 3 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 8 (Imm 4)
      (BCons 9 (Imm 4)
      (BCons 10 (Imm 4)
      (BCons 12 (Imm 4)
      (BCons 13 (Imm 4)
      (BCons 14 (Imm 4)
      (BCons 15 (Imm 4)
      (BCons 16 (Imm 4)
      BNil)))))))))))))))
    (BCons 12 (Br 6
      (BCons 0 (Imm 4)
      (BCons 1 (Imm 4)
      (BCons 2 (Imm 4)
      (BCons 3 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 8 (Imm 4)
      (BCons 9 (Imm 4)
      (BCons 10 (Imm 4)
      (BCons 11 (Imm 4)
      (BCons 13 (Imm 4)
      (BCons 14 (Imm 4)
      (BCons 15 (Imm 4)
      (BCons 16 (Imm 4)
      BNil)))))))))))))))
    (BCons 13 (Br 6
      (BCons 0 (Imm 4)
      (BCons 1 (Imm 4)
      (BCons 2 (Imm 4)
      (BCons 3 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 8 (Imm 4)
      (BCons 9 (Imm 4)
      (BCons 10 (Imm 4)
      (BCons 11 (Imm 4)
      (BCons 12 (Imm 4)
      (BCons 14 (Imm 4)
      (BCons 15 (Imm 4)
      (BCons 16 (Imm 4)
      BNil)))))))))))))))
    (BCons 14 (Br 6
      (BCons 0 (Imm 4)
      (BCons 1 (Imm 4)
      (BCons 2 (Imm 4)
      (BCons 3 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 8 (Imm 4)
      (BCons 9 (Imm 4)
      (BCons 10 (Imm 4)
      (BCons 11 (Imm 4)
      (BCons 12 (Imm 4)
      (BCons 13 (Imm 4)
      (BCons 15 (Imm 4)
      (BCons 16 (Imm 4)
      BNil)))))))))))))))
    (BCons 15 (Br 6
      (BCons 0 (Imm 4)
      (BCons 1 (Imm 4)
      (BCons 2 (Imm 4)
      (BCons 3 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 8 (Imm 4)
      (BCons 9 (Imm 4)
      (BCons 10 (Imm 4)
      (BCons 11 (Imm 4)
      (BCons 12 (Imm 4)
      (BCons 13 (Imm 4)
      (BCons 14 (Imm 4)
      (BCons 16 (Imm 4)
      BNil)))))))))))))))
    (BCons 16 (Br 6
      (BCons 0 (Imm 4)
      (BCons 1 (Imm 4)
      (BCons 2 (Imm 4)
      (BCons 3 (Imm 4)
      (BCons 4 (Imm 7)
      (BCons 7 (Imm 4)
      (BCons 8 (Imm 4)
      (BCons 9 (Imm 4)
      (BCons 10 (Imm 4)
      (BCons 11 (Imm 4)
      (BCons 12 (Imm 4)
      (BCons 13 (Imm 4)
      (BCons 14 (Imm 4)
      (BCons 15 (Imm 4)
      (BCons 16 (Imm 4)
      BNil))))))))))))))))
    BNil)))))))))))))))).

Theorem cert_corner_valid :
  wcheck 4 4 3 true true 3 (empty_board 16) 0 cert_corner = true.
Proof. vm_compute. reflexivity. Qed.

(** (3, n, 3): Player 1 forces a win within 7 plies on EVERY 3 x n board, n >= 4. *)
Theorem mnk_3_n_3_first_player_win : forall n, 4 <= n ->
  forces_win (gen_lines 3 n 3) P1 4 (empty_board (3 * n)).
Proof.
  intros n Hn.
  apply (window_certificate_lifts 3 4 3 false true 3 n) with (ct := cert_strip);
    try lia; try (intros; reflexivity); exact cert_strip_valid.
Qed.

(** (m, 3, 3): Player 1 forces a win within 7 plies on EVERY m x 3 board, m >= 4. *)
Theorem mnk_m_3_3_first_player_win : forall m, 4 <= m ->
  forces_win (gen_lines m 3 3) P1 4 (empty_board (m * 3)).
Proof.
  intros m Hm.
  apply (window_certificate_lifts 4 3 3 true false m 3) with (ct := cert_tall);
    try lia; try (intros; reflexivity); exact cert_tall_valid.
Qed.

(** (m, n, 3) with m, n >= 4: Player 1 forces a win within 5 plies. *)
Theorem mnk_m_n_3_first_player_win_5_plies : forall m n, 4 <= m -> 4 <= n ->
  forces_win (gen_lines m n 3) P1 3 (empty_board (m * n)).
Proof.
  intros m n Hm Hn.
  apply (window_certificate_lifts 4 4 3 true true m n) with (ct := cert_corner);
    try lia; try (intros; reflexivity); exact cert_corner_valid.
Qed.

(* ========================================================================= *)
(** * 5. The sharp phase transition and the k = 3 first-player wins          *)
(* ========================================================================= *)

(** Universal Sharp Phase Transition Theorem:
    (3, 3, 3) is a draw, while every 3 x n board with n >= 4 is a forced
    first-player win within 7 plies. *)
Theorem sharp_phase_transition_3_n_3 :
  game_is_draw (gen_lines 3 3 3) (empty_board 9) /\
  (forall n, 4 <= n -> forces_win (gen_lines 3 n 3) P1 4 (empty_board (3 * n))).
Proof.
  split; [exact mnk_3_3_3_draw | exact mnk_3_n_3_first_player_win].
Qed.

(** Every (m, n, 3) game with min(m, n) >= 3 and max(m, n) >= 4 is a forced
    first-player win within 7 plies. *)
Theorem mnk_k3_first_player_wins : forall m n,
  3 <= m -> 3 <= n -> 4 <= Nat.max m n ->
  forces_win (gen_lines m n 3) P1 4 (empty_board (m * n)).
Proof.
  intros m n Hm Hn Hmax.
  destruct (Nat.eq_dec m 3) as [-> | Hm3].
  - apply mnk_3_n_3_first_player_win. lia.
  - destruct (Nat.eq_dec n 3) as [-> | Hn3].
    + apply mnk_m_3_3_first_player_win. lia.
    + apply forces_win_mono with (d := 3); [| lia].
      apply mnk_m_n_3_first_player_win_5_plies; lia.
Qed.

(** Complete Characterization of the (m, n, 3) games (every m, n):
    - DRAW if min(m, n) <= 2 (domino pairing strategy) or (m, n) = (3, 3);
    - forced first-player WIN within 7 plies otherwise. *)
Theorem mnk_k3_complete_characterization : forall m n,
  ((Nat.min m n <= 2 \/ (m = 3 /\ n = 3)) ->
     game_is_draw (gen_lines m n 3) (empty_board (m * n))) /\
  ((3 <= Nat.min m n /\ 4 <= Nat.max m n) ->
     forces_win (gen_lines m n 3) P1 4 (empty_board (m * n))).
Proof.
  intros m n. split.
  - intros [Hmin | [-> ->]].
    + assert (H : m <= 2 \/ n <= 2) by lia.
      destruct H as [H | H]; [apply mnk_two_rows_draw | apply mnk_two_cols_draw]; exact H.
    + exact mnk_3_3_3_draw.
  - intros [H1 H2]. apply mnk_k3_first_player_wins; lia.
Qed.
