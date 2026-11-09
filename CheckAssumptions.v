(** CheckAssumptions.v: Strict Global Axiom & Admit Audit for 5x5x5 3D Tic-Tac-Toe in Rocq 9.1 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.

Require Import Qubic.QubicBoard.
Require Import Qubic.QubicSymmetry.
Require Import Qubic.QubicThreat.
Require Import Qubic.QubicTheorem.

(** ========================================================================= *)
(** AUDITING ALL 65 THEOREMS IN QUBIC 5x5x5 FORMALIZATION                      *)
(** ========================================================================= *)

(** 1. QubicBoard.v (27 Theorems) *)
Print Assumptions all_cells_length.
Print Assumptions all_cells_NoDup.
Print Assumptions make_cell_decomp.
Print Assumptions make_cell_bound.
Print Assumptions ortho_x_lines_count.
Print Assumptions ortho_y_lines_count.
Print Assumptions ortho_z_lines_count.
Print Assumptions total_ortho_lines_count.
Print Assumptions diag_xy_lines_count.
Print Assumptions diag_xz_lines_count.
Print Assumptions diag_yz_lines_count.
Print Assumptions total_planar_diag_lines_count.
Print Assumptions space_diag_lines_count.
Print Assumptions all_lines_count.
Print Assumptions all_lines_length_five.
Print Assumptions all_lines_cells_valid.
Print Assumptions all_lines_elements_nodup.
Print Assumptions all_lines_NoDup.
Print Assumptions center_cell_coords.
Print Assumptions center_cell_degree.
Print Assumptions deg13_cells_count.
Print Assumptions deg7_cells_count.
Print Assumptions deg5_cells_count.
Print Assumptions deg4_cells_count.
Print Assumptions deg3_cells_count.
Print Assumptions cell_degree_partition_sum.
Print Assumptions total_incidence_identity.

(** 2. QubicSymmetry.v (20 Theorems) *)
Print Assumptions refl_coord_involutive.
Print Assumptions refl_coord_bound.
Print Assumptions refl_x_involutive.
Print Assumptions refl_y_involutive.
Print Assumptions refl_z_involutive.
Print Assumptions swap_xy_involutive.
Print Assumptions swap_yz_involutive.
Print Assumptions refl_x_bound.
Print Assumptions refl_y_bound.
Print Assumptions refl_z_bound.
Print Assumptions refl_x_preserves_deg13.
Print Assumptions refl_x_preserves_deg7.
Print Assumptions refl_x_preserves_deg5.
Print Assumptions refl_x_preserves_deg4.
Print Assumptions refl_x_preserves_deg3.
Print Assumptions cell_classification_exhaustive.
Print Assumptions max_cell_degree_thirteen.
Print Assumptions non_center_max_degree_seven.
Print Assumptions transversal_size_arithmetic_lower_bound.
Print Assumptions static_pairing_impossibility_bound.

(** 3. QubicThreat.v (11 Theorems) *)
Print Assumptions other_color_involutive.
Print Assumptions double_threat_unblockable.
Print Assumptions double_threat_fork_forces_win.
Print Assumptions opening_center_lines_count.
Print Assumptions opening_corner_lines_count.
Print Assumptions opening_subcenter_lines_count.
Print Assumptions opening_edge_center_lines_count.
Print Assumptions opening_inner_face_lines_count.
Print Assumptions opening_outer_edge_lines_count.
Print Assumptions center_opening_advantage.
Print Assumptions min_moves_for_four_threat.

(** 4. QubicTheorem.v (The Authentic Pairing Verification Theorems) *)
Print Assumptions black_defense_stones_length.
Print Assumptions pairing_schedule_length.
Print Assumptions pairing_cells_length.
Print Assumptions pairing_cells_nodup.
Print Assumptions pairing_cells_disjoint_from_defense.
Print Assumptions all_109_lines_covered.
Print Assumptions line_partition_sum.
Print Assumptions pair_blocks_white_line.
Print Assumptions stone_blocks_white_line.
Print Assumptions white_cannot_win_5x5x5.
