(** **************************************************************************
    CheckersCheckAssumptions.v: Global Zero-Axiom Audit Suite in Rocq 9.1
    
    This audit imports every module in the Checkers formalization and
    systematically audits every proven theorem using 'Print Assumptions'.
    
    A successful compile with all 'Closed under the global context' guarantees
    that the formalization relies strictly on the Rocq 9.1 core logic without
    any unproven axioms, admissions, or external hypotheses.
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool.
Require Import Checkers.CheckersBoard.
Require Import Checkers.CheckersGame.
Require Import Checkers.CheckersInvariants.
Require Import Checkers.CheckersMicro.
Require Import Checkers.CheckersShashkiDiff.

(** 1. CheckersBoard Assumptions *)
Print Assumptions sq_bounds.
Print Assumptions dark_square_parity.
Print Assumptions step_fl_rank.
Print Assumptions step_fr_rank.
Print Assumptions step_bl_rank.
Print Assumptions step_br_rank.
Print Assumptions jump_fl_offset.
Print Assumptions jump_fr_offset.
Print Assumptions jump_bl_offset.
Print Assumptions jump_br_offset.
Print Assumptions jump_fl_rank.
Print Assumptions jump_fr_rank.
Print Assumptions jump_bl_rank.
Print Assumptions jump_br_rank.
Print Assumptions rot180_involutive.
Print Assumptions rot180_valid.
Print Assumptions rot180_rank.

(** 2. CheckersGame Assumptions *)
Print Assumptions player_eqb_spec.
Print Assumptions opp_involutive.
Print Assumptions opp_neq.
Print Assumptions remove_sq_length_le.
Print Assumptions remove_sq_notin.
Print Assumptions remove_sq_length_in.
Print Assumptions apply_simple_step_turn.
Print Assumptions step_turn.
Print Assumptions simple_step_preserves_count.

(** 3. CheckersInvariants Assumptions *)
Print Assumptions white_step_advances_rank.
Print Assumptions black_step_decreases_rank.
Print Assumptions white_jump_advances_rank.
Print Assumptions black_jump_decreases_rank.
Print Assumptions white_man_step_delta.
Print Assumptions black_man_step_delta.
Print Assumptions white_man_jump_delta.
Print Assumptions black_man_jump_delta.
Print Assumptions man_simple_step_no_self_loop.
Print Assumptions man_jump_no_self_loop.

(** 4. CheckersMicro Assumptions *)
Print Assumptions micro_bounds.
Print Assumptions micro_parity.
Print Assumptions micro_step_fl_rank.
Print Assumptions micro_step_fr_rank.
Print Assumptions micro_step_bl_rank.
Print Assumptions micro_step_br_rank.
Print Assumptions micro_jump_forward_rank.
Print Assumptions micro_jump_backward_rank.
Print Assumptions micro_initial_piece_count.

(** 5. CheckersShashkiDiff Assumptions *)
Print Assumptions english_white_man_no_backward_jump.
Print Assumptions english_black_man_no_forward_jump.
Print Assumptions english_king_mobility_bounded.
Print Assumptions english_king_jump_bounded.
Print Assumptions shashki_allows_backward_capture.
Print Assumptions shashki_backward_decreases_rank.
