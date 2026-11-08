(* ============================================================================== *)
(* CheckAssumptions.v - Verification of Zero Unproven Axioms in 9MM & 12MM        *)
(* ============================================================================== *)

Require Import NMM.NMMGraph.
Require Import NMM.NMMGame.
Require Import NMM.NMMInvariants.
Require Import NMM.NMMBitboard.
Require Import NMM.NMMStrategy.
Require Import NMM.NMMRetrograde.
Require Import NMM.NMMCertChecker.
Require Import NMM.NMMTransversal.

(* Graph Theory & Topology (NMMGraph.v) *)
Print Assumptions all_points_length.
Print Assumptions all_points_valid.
Print Assumptions all_mills_count.
Print Assumptions mill_regularity.
Print Assumptions adjacent_sym.
Print Assumptions adjacent_irreflexive.
Print Assumptions corner_degree_2.
Print Assumptions outer_inner_midpoint_degree_3.
Print Assumptions middle_midpoint_degree_4.
Print Assumptions handshake_lemma.
Print Assumptions rot_order_4.
Print Assumptions refl_order_2.
Print Assumptions dihedral_relation.
Print Assumptions rot_preserves_adjacency.
Print Assumptions refl_preserves_adjacency.
Print Assumptions rot_preserves_mills.
Print Assumptions refl_preserves_mills.

(* Trusted Operational Semantics (NMMGame.v) *)
Print Assumptions opp_involutive.
Print Assumptions opp_neq.
Print Assumptions in_nat_list_iff.
Print Assumptions post_placement_mobility_split.

(* Analytic Invariants & Bounds (NMMInvariants.v) *)
Print Assumptions all_mills_intersect_midpoints.
Print Assumptions radial_mills_disjoint_from_corners.
Print Assumptions all_mills_distinct_vertices.
Print Assumptions empty_board_no_mills.
Print Assumptions single_stone_no_mills.
Print Assumptions two_stones_no_mills.
Print Assumptions mill_complete_requires_at_least_three.
Print Assumptions phase1_no_terminal_loss.
Print Assumptions total_degrees_correct.

(* Verified Bitboards (NMMBitboard.v) *)
Print Assumptions mill_masks_count.
Print Assumptions mill_masks_exact.
Print Assumptions testbit_stones_to_bitboard.
Print Assumptions bitboard_mill_reflection.

(* D4 Equivariance & Strategy (NMMStrategy.v) *)
Print Assumptions rot_preserves_stone_count.
Print Assumptions refl_preserves_stone_count.
Print Assumptions rot_move_order_4.
Print Assumptions refl_move_involutive.
Print Assumptions rot_preserves_terminal_loss.
Print Assumptions refl_preserves_terminal_loss.
Print Assumptions stalemated_defender_not_safe.
Print Assumptions strategy_sound.
Print Assumptions mutual_safety_guarantees_draw.
Print Assumptions mutual_safety_game_value.

(* Retrograde Monotonicity & Horizon (NMMRetrograde.v) *)
Print Assumptions remove_nat_length_le.
Print Assumptions remove_nat_length_eq_or_pred.
Print Assumptions remove_stone_count_le.
Print Assumptions remove_stone_other_count.
Print Assumptions slide_stone_count_preservation.
Print Assumptions slide_other_stone_count_preservation.
Print Assumptions capture_decreases_total_stones.
Print Assumptions max_game_depth_positive.
Print Assumptions zermelo_finite_horizon_applies.

(* Verified Certificate Checker (NMMCertChecker.v) *)
Print Assumptions eq_state_refl.
Print Assumptions initial_state_non_terminal.
Print Assumptions initial_cert_checks.
Print Assumptions opening_move_cert_checks.
Print Assumptions check_cert_non_terminal.

(* 8-Stone Transversal Theorem & Cubic Dual Graph (NMMTransversal.v) *)
Print Assumptions transversal_8_length.
Print Assumptions transversal_8_covers_all_mills.
Print Assumptions transversal_barrier_prevents_attacker_mills.
Print Assumptions dual_graph_handshake.
Print Assumptions mill_coverage_bound.
Print Assumptions sum_mills_covered_eq_twice_length.
Print Assumptions transversal_size_lower_bound.

(* Twelve Men's Morris Foundations & Ply 8 Double-Fork (NMM12Graph.v) *)
Require Import NMM.NMM12Graph.
Print Assumptions diagonal_mills_count.
Print Assumptions all_mills_12_count.
Print Assumptions corner_mill_degree_3.
Print Assumptions midpoint_mill_degree_2.
Print Assumptions mill_incidence_handshake_12.
Print Assumptions adjacent_12_sym.
Print Assumptions middle_ring_degree_4.
Print Assumptions outer_ring_degree_3.
Print Assumptions inner_ring_degree_3.
Print Assumptions handshake_lemma_12.
Print Assumptions rot_preserves_diagonal_mills.
Print Assumptions refl_preserves_diagonal_mills.
Print Assumptions rot_preserves_all_20_mills.
Print Assumptions refl_preserves_all_20_mills.
Print Assumptions transversal_12_8_length.
Print Assumptions transversal_12_8_covers_all_20_mills.
Print Assumptions defensive_surplus_12mm.
Print Assumptions corner_0_three_rays.
Print Assumptions corner_0_two_rays_unblocked_after_ply1.
Print Assumptions ply8_corner_fork_theorem.


