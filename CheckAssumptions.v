(** **************************************************************************
    CheckAssumptions.v: Strict Axiom & Admission Audit for the MNK Library

    Prints the assumptions of every theorem of MNKBoard.v, MNKGame.v,
    MNKCertChecker.v, MNKWindow.v, MNKPairing.v, MNKPhaseTransition.v,
    MNKErdosSelfridge.v, MNKStrategyStealing.v, MNKMakerBreaker.v,
    MNKHalesJewett.v, MNKMakerBreakerCert.v, MNKMakerWins.v,
    MNKBreakerCert.v, MNKExactSpeed.v and MNKBreakerDraws.v.
    build.ps1 fails unless EVERY entry reports
    "Closed under the global context" (zero axioms, zero admissions).
    ************************************************************************** *)

Require Import MNK.MNKBoard.
Require Import MNK.MNKGame.
Require Import MNK.MNKCertChecker.
Require Import MNK.MNKWindow.
Require Import MNK.MNKPairing.
Require Import MNK.MNKPhaseTransition.
Require Import MNK.MNKErdosSelfridge.
Require Import MNK.MNKStrategyStealing.
Require Import MNK.MNKMakerBreaker.
Require Import MNK.MNKHalesJewett.
Require Import MNK.MNKMakerBreakerCert.
Require Import MNK.MNKMakerWins.
Require Import MNK.MNKBreakerCert.
Require Import MNK.MNKExactSpeed.
Require Import MNK.MNKBreakerDraws.

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

(* MNKErdosSelfridge.v: the Erdos-Selfridge theorem *)
Print Assumptions forces_win_maker_wins.
Print Assumptions lw_maker.
Print Assumptions lw_breaker.
Print Assumptions phi_maker.
Print Assumptions phi_breaker.
Print Assumptions wgt_breaker_le.
Print Assumptions phi_full.
Print Assumptions breaker_reply_bound.
Print Assumptions erdos_selfridge_potential.
Print Assumptions erdos_selfridge_breaker_second.
Print Assumptions erdos_selfridge_breaker_first.
Print Assumptions erdos_selfridge_draw.
Print Assumptions mnk_erdos_selfridge_draw.
Print Assumptions mnk_prime_triple_11_7_7_draw.
Print Assumptions mnk_prime_triple_17_13_11_draw.
Print Assumptions mnk_prime_triple_19_17_13_draw.
Print Assumptions mnk_near_square_draw.
Print Assumptions mnk_square_k_draw.
Print Assumptions erdos_selfridge_draw_refined.
Print Assumptions mnk_4_4_4_draw.
Print Assumptions mnk_1_1_1_first_player_win.
Print Assumptions mnk_2_2_2_first_player_win.
Print Assumptions mnk_square_classification.

(* MNKStrategyStealing.v: strategy stealing *)
Print Assumptions set_cell_comm.
Print Assumptions check_win_other_stone.
Print Assumptions forces_win_swap.
Print Assumptions steal.
Print Assumptions not_both.
Print Assumptions strategy_stealing.
Print Assumptions positional_game_win_or_draw.
Print Assumptions mnk_second_player_never_wins.
Print Assumptions mnk_value_win_or_draw.

(* MNKMakerBreaker.v: from Maker-Breaker strategies to game values *)
Print Assumptions breaker_win_draw.
Print Assumptions mnk_breaker_win_draw.
Print Assumptions check_win_refine.
Print Assumptions maker_wins_refine.
Print Assumptions mnk_lines_refine.
Print Assumptions mnk_maker_wins_shorter_lines.
Print Assumptions mnk_breaker_win_longer_lines.
Print Assumptions mnk_draw_longer_lines.
Print Assumptions harmless_after_moves.
Print Assumptions pairing_no_maker_win.
Print Assumptions pairing_no_maker_win_empty.
Print Assumptions maker_wins_simulate.
Print Assumptions mnk_maker_wins_subboard.
Print Assumptions mnk_maker_wins_transpose.
Print Assumptions mnk_breaker_win_subboard.
Print Assumptions mnk_breaker_win_transpose.
Print Assumptions mnk_breaker_win_family.

(* MNKHalesJewett.v: every (m, n, k) game with k >= 9 is a draw *)
Print Assumptions hj_tile_consistent.
Print Assumptions hj_tile_lines.
Print Assumptions hj_partner_invol.
Print Assumptions hj_partner_range.
Print Assumptions hj_line_has_pair.
Print Assumptions mnk_hales_jewett_breaker_wins.
Print Assumptions mnk_hales_jewett_draw.

(* MNKMakerBreakerCert.v: sound checker for Maker-Breaker wins *)
Print Assumptions threat_line_win.
Print Assumptions quick_win_sound.
Print Assumptions check_mb_sound.

(* MNKMakerWins.v: checked Maker wins and the Maker-Breaker / strong-game gap *)
Print Assumptions mnk_3_3_3_maker_wins.
Print Assumptions mnk_5_5_4_maker_wins.
Print Assumptions mnk_tic_tac_toe_gap.
Print Assumptions mnk_5_5_4_no_breaker_win.
Print Assumptions maker_win_spreads.
Print Assumptions mnk_maker_wins_k3_family.
Print Assumptions mnk_maker_wins_k4_family.

(* MNKBreakerCert.v: sound checker for Breaker strategies, bounded or not *)
Print Assumptions short_no_win.
Print Assumptions es_ok_sound.
Print Assumptions pairing_ok_sound.
Print Assumptions check_br_sound.
Print Assumptions check_br_draw.
Print Assumptions check_br_within.
Print Assumptions mnk_no_win_before_k.
Print Assumptions mnk_no_forced_win_before_k.

(* MNKExactSpeed.v: exact winning speeds *)
Print Assumptions mnk_m_n_3_exactly_3_moves.
Print Assumptions mnk_m_n_3_mb_exactly_3_moves.
Print Assumptions mnk_3_n_3_mb_no_win_within_3.
Print Assumptions mnk_3_n_3_exactly_4_moves.
Print Assumptions mnk_3_n_3_mb_exactly_4_moves.
Print Assumptions mnk_3_3_3_mb_exactly_4_moves.
Print Assumptions mnk_5_5_4_mb_exactly_5_moves.

(* MNKBreakerDraws.v: draws from checked Breaker strategies *)
Print Assumptions mnk_5_4_4_breaker_wins.
Print Assumptions mnk_5_4_4_draw.
Print Assumptions mnk_draw_inside_5_4.

(* Statements of the headline theorems, for the record *)
Check sharp_phase_transition_3_n_3.
Check mnk_k3_complete_characterization.
Check window_certificate_lifts.
Check erdos_selfridge_breaker_second.
Check erdos_selfridge_breaker_first.
Check mnk_erdos_selfridge_draw.
Check strategy_stealing.
Check mnk_value_win_or_draw.
Check mnk_square_classification.
Check breaker_win_draw.
Check mnk_draw_longer_lines.
Check pairing_no_maker_win.
Check mnk_breaker_win_family.
Check mnk_hales_jewett_draw.
Check mnk_hales_jewett_breaker_wins.
Check check_mb_sound.
Check mnk_tic_tac_toe_gap.
Check mnk_maker_wins_k4_family.
Check check_br_sound.
Check mnk_no_forced_win_before_k.
Check mnk_m_n_3_exactly_3_moves.
Check mnk_3_n_3_exactly_4_moves.
Check mnk_3_3_3_mb_exactly_4_moves.
Check mnk_5_5_4_mb_exactly_5_moves.
Check mnk_draw_inside_5_4.
