(** **************************************************************************
    CheckAssumptions.v: Strict Axiom & Admission Audit for the MNK Library

    Prints the assumptions of every theorem of MNKBoard.v, MNKGame.v,
    MNKCertChecker.v, MNKWindow.v, MNKPairing.v and MNKPhaseTransition.v.
    build.ps1 fails unless EVERY entry reports
    "Closed under the global context" (zero axioms, zero admissions).
    ************************************************************************** *)

Require Import MNK.MNKBoard.
Require Import MNK.MNKGame.
Require Import MNK.MNKCertChecker.
Require Import MNK.MNKWindow.
Require Import MNK.MNKPairing.
Require Import MNK.MNKPhaseTransition.

(* MNKBoard.v: geometry, verified line generator, counting *)
Print Assumptions coord_to_idx_inv.
Print Assumptions mnk_line_count_formula_closed.
Print Assumptions in_gen_lines.
Print Assumptions gen_lines_count.
Print Assumptions gen_lines_bounding_box.
Print Assumptions gen_lines_in_range.
Print Assumptions gen_lines_uniform.
Print Assumptions gen_lines_nodup.
Print Assumptions mnk_handshaking.
Print Assumptions mnk_3_3_3_lines.
Print Assumptions mnk_3_4_3_lines.
Print Assumptions mnk_4_4_4_lines.
Print Assumptions mnk_5_4_4_lines.
Print Assumptions mnk_6_4_4_lines.
Print Assumptions mnk_7_4_4_lines.
Print Assumptions mnk_8_4_4_lines.
Print Assumptions mnk_5_5_4_lines.
Print Assumptions mnk_8_8_5_lines.
Print Assumptions mnk_15_15_5_gomoku_lines.
Print Assumptions mnk_prime_triple_7_5_3_lines.
Print Assumptions mnk_prime_triple_11_7_5_lines.
Print Assumptions mnk_prime_triple_13_11_7_lines.
Print Assumptions mnk_prime_triple_11_7_7_lines.
Print Assumptions mnk_prime_triple_17_13_11_lines.
Print Assumptions mnk_prime_triple_19_17_13_lines.
Print Assumptions mnk_prime_triple_11_7_7_erdos_bound.
Print Assumptions mnk_prime_triple_17_13_11_erdos_bound.
Print Assumptions mnk_prime_triple_19_17_13_erdos_bound.
Print Assumptions erdos_selfridge_hypothesis_near_square.
Print Assumptions lines_3_3_3_count.
Print Assumptions lines_3_4_3_count.
Print Assumptions lines_3_4_3_all_len_3.
Print Assumptions lines_3_3_3_generated.
Print Assumptions lines_3_4_3_generated.
Print Assumptions strip_width_horizontal_obstruction.
Print Assumptions strip_width_diagonal_obstruction.

(* MNKGame.v: board operations, monotonicity, game semantics, evaluator *)
Print Assumptions other_player_involutive.
Print Assumptions player_eqb_refl.
Print Assumptions player_eqb_eq.
Print Assumptions set_cell_length.
Print Assumptions get_set_cell_same.
Print Assumptions get_set_cell_other.
Print Assumptions board_sub_refl.
Print Assumptions board_sub_trans.
Print Assumptions set_cell_preserves_sub.
Print Assumptions cell_owned_monotonic.
Print Assumptions line_owned_monotonic.
Print Assumptions check_win_monotonic.
Print Assumptions extra_stone_preserves_win.
Print Assumptions check_win_iff.
Print Assumptions legal_moves_set_length.
Print Assumptions forces_win_mono.
Print Assumptions forces_win_cap.
Print Assumptions wins_b_spec.
Print Assumptions no_forced_win_by_evaluation.

(* MNKCertChecker.v: sound certificate checker *)
Print Assumptions check_cert_sound.

(* MNKWindow.v: window simulation theorem *)
Print Assumptions danger_detects.
Print Assumptions wcheck_sound.
Print Assumptions window_certificate_lifts.

(* MNKPairing.v: pairing strategies *)
Print Assumptions pairing_no_forced_win.
Print Assumptions pairing_draw.
Print Assumptions mnk_two_rows_draw.
Print Assumptions mnk_two_cols_draw.

(* MNKPhaseTransition.v: game-theoretic results *)
Print Assumptions mnk_3_3_3_draw.
Print Assumptions win_3_4_3_certified.
Print Assumptions mnk_3_4_3_first_player_win.
Print Assumptions mnk_3_4_3_no_win_within_5_plies.
Print Assumptions mnk_3_4_3_exactly_7_plies.
Print Assumptions embed_in_bounds.
Print Assumptions embed_injective.
Print Assumptions embed_line_length.
Print Assumptions subgrid_projection_counterexample_3_5_3.
Print Assumptions projected_cert_rejected_3_5_3.
Print Assumptions cert_strip_valid.
Print Assumptions cert_tall_valid.
Print Assumptions cert_corner_valid.
Print Assumptions mnk_3_n_3_first_player_win.
Print Assumptions mnk_m_3_3_first_player_win.
Print Assumptions mnk_m_n_3_first_player_win_5_plies.
Print Assumptions sharp_phase_transition_3_n_3.
Print Assumptions mnk_k3_first_player_wins.
Print Assumptions mnk_k3_complete_characterization.

(* Statements of the headline theorems, for the record *)
Check sharp_phase_transition_3_n_3.
Check mnk_k3_complete_characterization.
Check window_certificate_lifts.
