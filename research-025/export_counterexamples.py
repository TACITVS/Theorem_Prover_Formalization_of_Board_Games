"""Export a solver witness as a theorem about the frozen game evaluator."""
import json
from pathlib import Path


def main():
    directory = Path(__file__).resolve().parent
    rows = json.loads((directory / 'results.json').read_text())['results']
    result = next(row for row in rows if row['backend'] == 'kissat-cli' and
                  row['instance'].endswith('two_line_region_with_block4') and row['status'] == 'SAT')
    white = result['witness']['history'][::2]
    white_source = ';'.join(map(str, white))
    source = f'''(** Solver-discovered data, checked by the exact Rocq game evaluator.
    Source instance {result['sha256']}. *)
From Stdlib Require Import List.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Tactics.
Import ListNotations.

Definition attack : WhiteStrategy := fun st =>
  nth (length (white_stones st)) [{white_source}] 0.

Theorem blocker_counterexample_at_ply_fifteen :
  outcome (step_game 15 true initial_state attack blocking_policy) = WhiteWins.
Proof. vm_compute. reflexivity. Qed.

Theorem blocker_counterexample_in_full_game :
  outcome (play attack blocking_policy) = WhiteWins.
Proof. vm_compute. reflexivity. Qed.

Theorem fourteen_ply_bound_is_tight_for_blocking_policy :
  (forall w, outcome (step_game 14 true initial_state w blocking_policy) <> WhiteWins) /\\
  (exists w, outcome (step_game 15 true initial_state w blocking_policy) = WhiteWins).
Proof.
  split; [apply no_white_win_in_first_fourteen_plies|].
  exists attack. exact blocker_counterexample_at_ply_fifteen.
Qed.

Print Assumptions blocker_counterexample_at_ply_fifteen.
Print Assumptions blocker_counterexample_in_full_game.
Print Assumptions fourteen_ply_bound_is_tight_for_blocking_policy.
'''
    (directory / 'Counterexamples.v').write_text(source, encoding='utf-8')
    print('Exported Kissat counterexample, White moves', white)


if __name__ == '__main__':
    main()
