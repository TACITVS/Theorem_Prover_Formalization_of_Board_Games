(** Tactical regressions against the exact locked game. The local White
    winning position is not a forced strategy from the initial board. *)
From Stdlib Require Import List Arith Bool Lia.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Minimax RulesFacts SafePairing Tactics.
Import ListNotations.

Definition scheduled_white (cells : list cell) : WhiteStrategy :=
  fun st => nth (length (white_stones st)) cells 0.
Definition scheduled_black (cells : list cell) : BlackStrategy :=
  fun st => nth (length (black_stones st)) cells 0.

Lemma prefix_validity : forall n turn st w b,
  n + length (history st) <= 125 -> valid_state st ->
  valid_state (final_state (step_game n turn st w b)).
Proof.
  induction n as [|n IH]; intros turn st w b Hlen Hvalid; [exact Hvalid|].
  rewrite step_game_equation. cbn zeta.
  set (next := move_state turn st (if turn then w st else b st)).
  assert (Hnext : valid_state next) by (apply move_preserves_validity; [exact Hvalid|lia]).
  destruct (move_result turn next); [exact Hnext|].
  apply IH; [unfold next; rewrite move_state_history; lia|exact Hnext].
Qed.

Definition fork_white : list cell := [0;1;2;3;5;10;15].
Definition fork_black : list cell := [6;7;8;9;11;12].
Definition fork_state : GameState := make_state
  [15;10;5;3;2;1;0] [12;11;9;8;7;6]
  [15;12;10;11;5;9;3;8;2;7;1;6;0].

Theorem true_fork_reachable_prefix :
  final_state (step_game 13 true initial_state
    (scheduled_white fork_white) (scheduled_black fork_black)) = fork_state.
Proof. vm_compute. reflexivity. Qed.

Theorem fork_state_valid : valid_state fork_state.
Proof.
  rewrite <- true_fork_reachable_prefix. apply prefix_validity;
    [cbn; lia|apply initial_state_valid].
Qed.

Theorem true_fork_checks :
  quiet fork_state /\ length (white_stones fork_state) = 7 /\
  white_completionb fork_state 4 = true /\ white_completionb fork_state 20 = true /\
  fork_cutoffb fork_state = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem local_fork_has_total_winning_strategy :
  exists w : WhiteStrategy, forall b : BlackStrategy,
    outcome (step_game 112 false fork_state w b) = WhiteWins.
Proof.
  apply (checked_fork_has_total_white_win 110 fork_state eq_refl fork_state_valid).
  exact (proj2 (proj2 (proj2 (proj2 true_fork_checks)))).
Qed.

Definition shared_state : GameState := make_state
  [112;87;72;67;57;52;37;12] [10;7;6;5;2;1;0]
  [112;10;87;7;72;6;67;5;57;2;52;1;37;0;12].

Theorem shared_target_is_legal_prefix :
  final_state (step_game 15 true initial_state
    (scheduled_white [12;37;52;57;67;72;87;112])
    (scheduled_black [0;1;2;5;6;7;10])) = shared_state.
Proof. vm_compute. reflexivity. Qed.

Theorem shared_target_has_two_threat_lines :
  length (filter (fun l => has_line (62 :: white_stones shared_state) l &&
    negb (has_line (white_stones shared_state) l)) all_lines) = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem shared_target_is_not_a_distinct_fork :
  filter (white_completionb shared_state) all_cells = [62] /\
  distinct_white_forkb shared_state = false /\ blocking_policy shared_state = 62.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition race_state : GameState := make_state
  [15;10;5;3;2;1;0] [31;30;28;27;26;25]
  [15;31;10;30;5;28;3;27;2;26;1;25;0].

Theorem race_is_legal_prefix :
  final_state (step_game 13 true initial_state
    (scheduled_white fork_white) (scheduled_black [25;26;27;28;30;31])) = race_state.
Proof. vm_compute. reflexivity. Qed.

Theorem own_immediate_win_rejects_fork_cutoff :
  distinct_white_forkb race_state = true /\ fork_cutoffb race_state = false.
Proof. vm_compute. split; reflexivity. Qed.

Theorem black_wins_before_white_fork : forall w,
  outcome (step_game 112 false race_state w (fun _ => 29)) = BlackWins.
Proof. intros w. vm_compute. reflexivity. Qed.
