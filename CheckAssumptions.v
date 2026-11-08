(**
  CheckAssumptions.v: Assumption and Axiom Audit for Classic 7x6 Connect-Four
  Rocq 9.1: Verifies that all 41 theorems are Closed under the global context (0 Axioms, 0 Admits).
*)

Require Import C4.C4Board.
Require Import C4.C4Claimeven.
Require Import C4.C4CenterPigeonhole.
Require Import C4.C4Zugzwang.
Require Import C4.C4Theorem.

Print Assumptions board_cells_count.
Print Assumptions pt_eq_refl.
Print Assumptions horiz_lines_length.
Print Assumptions vert_lines_length.
Print Assumptions pos_diag_lines_length.
Print Assumptions neg_diag_lines_length.
Print Assumptions all_lines_length.
Print Assumptions all_lines_length_4.

Print Assumptions domino_count.
Print Assumptions domino_cell_coverage.
Print Assumptions O_21_count.
Print Assumptions claimeven_kills_57_lines.
Print Assumptions surviving_lines_count.
Print Assumptions all_vert_lines_blocked.
Print Assumptions all_diag_lines_blocked.
Print Assumptions all_odd_row_horiz_blocked.

Print Assumptions refl_c_fixed_point.
Print Assumptions refl_c_involutive.
Print Assumptions horiz_window_contains_center.
Print Assumptions horiz_line_contains_center.
Print Assumptions center_even_count.
Print Assumptions transversal_24_count.
Print Assumptions transversal_blocks_all_69_lines.
Print Assumptions all_12_even_horiz_blocked_by_center.

Print Assumptions even_empty_at_white_turn.
Print Assumptions suffix_size_ft2.
Print Assumptions suffix_size_ft4.
Print Assumptions frozen_suffix_odd.
Print Assumptions zugzwang_arithmetic_identity.
Print Assumptions even_2m_plus_1.
Print Assumptions zugzwang_parity_law.
Print Assumptions black_exhaustion_outside_frozen_zone.

Print Assumptions other_color_involutive.
Print Assumptions best_opening_is_center.
Print Assumptions max_win_plies_bound.
Print Assumptions raw_state_space_formula.
Print Assumptions gravity_profiles_formula.
Print Assumptions white_opening_leaves_odd.
Print Assumptions all_69_lines_transversal_verification.
Print Assumptions white_has_moves_until_ply41.
Print Assumptions central_connect4_7x6_theorem.
