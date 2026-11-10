(** Solver-discovered data, checked by the exact Rocq game evaluator.
    Source instance 435ef575318860316247aedb0c17bbb301da8d3e262464aad09a7b89320b480f. *)
From Stdlib Require Import List.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Tactics.
Import ListNotations.

Definition attack : WhiteStrategy := fun st =>
  nth (length (white_stones st)) [4;29;54;100;101;102;104;103] 0.

Theorem blocker_counterexample_at_ply_fifteen :
  outcome (step_game 15 true initial_state attack blocking_policy) = WhiteWins.
Proof. vm_compute. reflexivity. Qed.

Theorem blocker_counterexample_in_full_game :
  outcome (play attack blocking_policy) = WhiteWins.
Proof. vm_compute. reflexivity. Qed.

Theorem fourteen_ply_bound_is_tight_for_blocking_policy :
  (forall w, outcome (step_game 14 true initial_state w blocking_policy) <> WhiteWins) /\
  (exists w, outcome (step_game 15 true initial_state w blocking_policy) = WhiteWins).
Proof.
  split; [apply no_white_win_in_first_fourteen_plies|].
  exists attack. exact blocker_counterexample_at_ply_fifteen.
Qed.

Print Assumptions blocker_counterexample_at_ply_fifteen.
Print Assumptions blocker_counterexample_in_full_game.
Print Assumptions fourteen_ply_bound_is_tight_for_blocking_policy.
