(** **************************************************************************
    DABCheckAssumptions.v: Machine-Checked Zero-Axiom Assumption Auditor
    
    This module audits the global context of every theorem proved in the
    Dots and Boxes formalization suite (Rocq 9.1).
    
    Expected Output:
    "Closed under the global context" for all audited theorems.
    Zero unproven axioms, zero admissions, zero external assumptions.
    ************************************************************************** *)

From DAB Require Import DABUniversal DAB16Graph DABGame.

(** Universal n x n Theorems *)
Print Assumptions euler_characteristic_universal.
Print Assumptions edge_decomposition_universal.
Print Assumptions box_incidence_sum_universal.
Print Assumptions total_box_incidences.
Print Assumptions dual_edges_equal_primal.
Print Assumptions dual_vertices_equal_faces.
Print Assumptions box_regular_degree.
Print Assumptions score_conservation_universal.
Print Assumptions odd_n_strictly_forbids_draw.
Print Assumptions even_n_admits_draw.
Print Assumptions dab_4x4_draw_score.
Print Assumptions tempo_conservation_universal.
Print Assumptions tempo_difference_universal.
Print Assumptions net_tempo_surplus.
Print Assumptions dab_4x4_tempo_surplus.
Print Assumptions berlekamp_double_deal_sacrifice.
Print Assumptions berlekamp_parity_control.

(** 5x5 Dots / 4x4 Boxes Grid Graph Theorems *)
Print Assumptions box_edges_length.
Print Assumptions rot_edge_bound.
Print Assumptions rot_order_4.
Print Assumptions refl_edge_bound.
Print Assumptions refl_order_2.
Print Assumptions dihedral_relation.
Print Assumptions boundary_list_length.
Print Assumptions boundary_count_matches_universal.
Print Assumptions interior_count_matches_universal.
Print Assumptions dual_box_degree_4.
Print Assumptions total_box_edge_incidences_16.

(** Operational Semantics & Inductive Game Invariants *)
Print Assumptions step_edge_monotonic.
Print Assumptions step_distinct_edges.
Print Assumptions initial_state_empty.
Print Assumptions step_score_monotonic.
Print Assumptions step_score_sum.
Print Assumptions max_game_depth_40.
