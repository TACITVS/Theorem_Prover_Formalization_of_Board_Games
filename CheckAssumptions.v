(** CheckAssumptions.v: Strict Global Axiom & Admit Audit for Qubic 4x4x4 in Rocq 9.1 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.

Require Import Qubic.QubicBoard.
Require Import Qubic.QubicSymmetry.
Require Import Qubic.QubicThreat.
Require Import Qubic.QubicTheorem.

(** ========================================================================= *)
(** AUDITING ALL 72 THEOREMS IN QUBIC FORMALIZATION                            *)
(** ========================================================================= *)

(** 1. QubicBoard.v (32 Theorems) *)
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
Print Assumptions all_lines_length_four.
Print Assumptions all_lines_cells_valid.
Print Assumptions all_lines_elements_nodup.
Print Assumptions all_lines_NoDup.
Print Assumptions corners_count.
Print Assumptions edges_count.
Print Assumptions faces_count.
Print Assumptions cube_centers_count.
Print Assumptions cell_partition_sum.
Print Assumptions corner_degree_uniform.
Print Assumptions edge_degree_uniform.
Print Assumptions face_degree_uniform.
Print Assumptions cube_center_degree_uniform.
Print Assumptions corner_degree_all.
Print Assumptions edge_degree_all.
Print Assumptions face_degree_all.
Print Assumptions cube_center_degree_all.
Print Assumptions total_incidence_identity.

(** 2. QubicSymmetry.v (26 Theorems) *)
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
Print Assumptions refl_x_preserves_corners.
Print Assumptions refl_x_preserves_cube_centers.
Print Assumptions refl_x_preserves_edges.
Print Assumptions refl_x_preserves_faces.
Print Assumptions cell_classification_exhaustive.
Print Assumptions canon_corner_is_corner.
Print Assumptions canon_cube_center_is_cube.
Print Assumptions canon_edge_is_edge.
Print Assumptions canon_face_is_face.
Print Assumptions canon_corner_degree_seven.
Print Assumptions canon_cube_center_degree_seven.
Print Assumptions canon_edge_degree_four.
Print Assumptions canon_face_degree_four.
Print Assumptions max_cell_degree_seven.
Print Assumptions transversal_size_arithmetic_lower_bound.
Print Assumptions silver_pairing_impossibility_bound.

(** 3. QubicThreat.v (8 Theorems) *)
Print Assumptions other_color_involutive.
Print Assumptions double_threat_unblockable.
Print Assumptions double_threat_fork_forces_win.
Print Assumptions opening_cube_center_lines_count.
Print Assumptions opening_corner_lines_count.
Print Assumptions opening_edge_lines_count.
Print Assumptions opening_face_lines_count.
Print Assumptions opening_advantage_ratio.

(** 4. QubicTheorem.v (6 Theorems) *)
Print Assumptions qubic_master_value_is_win_white.
Print Assumptions max_qubic_plies_bound.
Print Assumptions max_white_moves_bound.
Print Assumptions total_naive_states_Z_computed.
Print Assumptions total_naive_states_lower_bound.
Print Assumptions cells_saturate_uint64.
