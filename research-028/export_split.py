"""Export a large strategy tree as several Rocq files that check in parallel.

  <Name>Root.v      position, tree data, certificate, and `root_round`
  <Name>Part<k>.v   `root_round x = true` by vm_compute, for a block of requests
  <Name>.v          combines the 126 request lemmas into `linear_treeb ... = true`
                    and the total-defense theorem

Each part is a separate `rocq compile`, so a finished part (.vo) is a checkpoint
and parts can run on separate cores. Python proposes the tree; Rocq checks it.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from export_tree import PRELUDE, plan_text, precompute_leaves, rl
from fragment_search import games

HERE = Path(__file__).resolve().parent


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('tree_json')
    ap.add_argument('--game', required=True)
    ap.add_argument('--round', type=int, required=True)
    ap.add_argument('--name', required=True)
    ap.add_argument('--block', type=int, default=10)
    args = ap.parse_args()
    tree = json.loads(Path(args.tree_json).read_text(encoding='utf-8'))
    tree = {k: ([v['reply'], 'leaf'] if isinstance(v, dict) else v) for k, v in tree.items()}
    if any(v is None or v[0] is None for v in tree.values()):
        raise SystemExit('tree has uncovered White moves; nothing to export')
    white, black = games()[args.game]
    white, black = white[:args.round], black[:args.round]
    hist = [c for pair in zip(white, black) for c in pair]
    plies = len(hist)
    n = args.name
    moves = sorted(int(k) for k in tree)
    precompute_leaves(white, black, tree)
    subplans = []
    for m in moves:
        r, sub = tree[str(m)]
        print(f'  exporting White {m} -> Black {r}', flush=True)
        subplans.append(f'Definition plan_{m} : Plan := '
                        + plan_text(white + [m], black + [r], sub) + '.\n')
    table = '[' + ';\n  '.join(f'({m}, ({tree[str(m)][0]}, plan_{m}))' for m in moves) + ']'
    root = PRELUDE + f'''
Definition white_history : list cell := {rl(white)}.
Definition black_history : list cell := {rl(black)}.
Definition start_state : GameState := make_state
  {rl(reversed(white))} {rl(reversed(black))}
  {rl(reversed(hist))}.

Theorem start_state_is_legal_prefix :
  final_state (step_game {plies} true initial_state
    (scheduled_white white_history) (scheduled_black black_history)) = start_state.
Proof. vm_compute. reflexivity. Qed.

Theorem start_state_valid : valid_state start_state.
Proof.
  rewrite <- start_state_is_legal_prefix. apply prefix_validity;
    [cbn; lia|apply initial_state_valid].
Qed.

{''.join(subplans)}
Definition root_table : list (cell * (cell * Plan)) :=
  {table}.

Definition root_reply (x : cell) : cell := fst (lookup (0, PLeaf 0%N) x root_table).
Definition root_child (x : cell) : LinearDefenseCertificate :=
  to_cert (snd (lookup (0, PLeaf 0%N) x root_table)) (after start_state x (root_reply x)).
Definition certificate : LinearDefenseCertificate := LinearDefenseNode root_reply root_child.
Definition root_round : cell -> bool :=
  roundb (fun c after_black => linear_treeb (root_child c) after_black) root_reply start_state.
'''
    (HERE / f'{n}Root.v').write_text(root, encoding='utf-8')
    parts = []
    for k in range(0, 126, args.block):
        xs = list(range(k, min(126, k + args.block)))
        name = f'{n}Part{k // args.block}'
        parts.append(name)
        lemmas = ''.join(f'Lemma request_{x} : root_round {x} = true.\n'
                         f'Proof. vm_compute. reflexivity. Qed.\n' for x in xs)
        (HERE / f'{name}.v').write_text(
            f'From QubicResearch028 Require Import {n}Root.\n{lemmas}', encoding='utf-8')
    imports = ' '.join(parts)
    rewrites = ', '.join(f'request_{x}' for x in range(126))
    final = f'''(** Combines the per-request checks of {n}Root into the total-defense theorem. *)
From Stdlib Require Import List Arith Bool.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Minimax RulesFacts TreeCertificates ZZLinearTrees.
From QubicResearch028 Require Import {n}Root {imports}.
Import ListNotations.

Theorem certificate_checks : linear_treeb certificate start_state = true.
Proof.
  change (forallb root_round requests = true).
  unfold requests. cbn [seq forallb].
  rewrite {rewrites}.
  reflexivity.
Qed.

(** After this {plies}-ply prefix, Black has a strategy that never loses. *)
Theorem start_state_total_defense : exists b : BlackStrategy, forall w : WhiteStrategy,
  outcome (step_game {125 - plies} true start_state w b) <> WhiteWins.
Proof.
  exact (checked_linear_tree_total_defense certificate start_state {125 - plies}
    certificate_checks start_state_valid eq_refl).
Qed.

Print Assumptions start_state_total_defense.
'''
    (HERE / f'{n}.v').write_text(final, encoding='utf-8')
    print(f'wrote {n}Root.v ({len(root) // 1024} KiB), {len(parts)} parts, {n}.v', flush=True)


if __name__ == '__main__':
    main()
