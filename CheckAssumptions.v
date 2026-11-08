(** **************************************************************************
    CheckAssumptions.v: Strict Axiom & Admission Audit for MNK Library
    
    Verifies that all theorems across MNKBoard.v, MNKGame.v, MNKCertChecker.v,
    and MNKPhaseTransition.v are 100% closed under the global context
    with ZERO unproven axioms and ZERO admissions.
    ************************************************************************** *)

Require Import MNK.MNKBoard.
Require Import MNK.MNKGame.
Require Import MNK.MNKCertChecker.
Require Import MNK.MNKPhaseTransition.

Print Assumptions coord_to_idx_inv.
Print Assumptions mnk_line_count_formula_closed.
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
Print Assumptions lines_3_3_3_count.
Print Assumptions lines_3_4_3_count.
Print Assumptions lines_3_4_3_all_len_3.
Print Assumptions strip_width_horizontal_obstruction.
Print Assumptions strip_width_diagonal_obstruction.

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

Print Assumptions win_3_4_3_certified.
Print Assumptions cert_3_4_3_max_plies.
Print Assumptions embed_in_bounds.
Print Assumptions embed_injective.
Print Assumptions embed_line_length.
Print Assumptions sharp_phase_transition_3_n_3.
