"""Build polynomial-size XOR decoder certificates from experimental data.
Rocq checks reconstruction identities directly; Python rank is not trusted.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import linear_search as ls


def independent_rows(rows: list[int]) -> list[int]:
    pivots = {}
    result = []
    for original in rows:
        word = original
        while word:
            p = word.bit_length() - 1
            if p in pivots:
                word ^= pivots[p]
            else:
                pivots[p] = word
                result.append(original)
                break
    return result


def decoder(rows: list[int], cells: list[int]) -> list[tuple[int, int]]:
    basis_rows = independent_rows(rows)
    assert len(basis_rows) == len(cells)
    observed = {j: sum((1 << k) for k, c in enumerate(cells) if word >> c & 1)
                for j, word in enumerate(basis_rows)}
    basis = ls.tracking_basis(observed, set(observed))
    result = []
    for j, c in enumerate(cells):
        dependent, expression = ls.reduce_with_expression(1 << j, basis)
        assert dependent
        word = 0
        for i, row in enumerate(basis_rows):
            if expression >> i & 1:
                word ^= row
        result.append((c, word))
    for row in rows:
        recovered = 0
        for c, word in result:
            if row >> c & 1:
                recovered ^= word
        assert recovered == row
    return result


def rocq_list(values) -> str:
    return '[' + ';'.join(map(str, values)) + ']'


def decoder_source(name: str, value) -> str:
    entries = ';\n  '.join(f'({c}, {word}%N)' for c, word in value)
    return f'\nDefinition {name} : Decoder := [\n  {entries}\n].\n'


def generate(data: dict) -> str:
    white, black = data['white'], data['black']
    assert len(white) == len(black) and 0 < len(white) < 62
    plies = 2 * len(white)
    remaining = 125 - plies
    assert not ls.wins(set(white)) and not ls.wins(set(black))
    assert len(set(white + black)) == plies
    rows = ls.residual_rows(set(white), set(black))
    d0 = decoder(rows, data['information_sets'][0])
    d1 = decoder(rows, data['information_sets'][1])
    assert not set(c for c, _ in d0) & set(c for c, _ in d1)
    history = list(itertools.chain.from_iterable(zip(white, black)))
    source = '''(** Generated decoder data. Every claimed game guarantee is checked below.
    The local nonterminal position is not a forced opening strategy. *)
From Stdlib Require Import List Arith Bool Lia NArith.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Minimax RulesFacts SafePairing ZLinearAlgebra ZLinearDefense ZPairingSeparation ZZLinearTrees.
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
'''
    source += f'''
Definition white_history : list cell := {rocq_list(white)}.
Definition black_history : list cell := {rocq_list(black)}.
Definition linear_state : GameState := make_state
  {rocq_list(reversed(white))} {rocq_list(reversed(black))}
  {rocq_list(reversed(history))}.

Theorem linear_state_is_legal_prefix :
  final_state (step_game {plies} true initial_state
    (scheduled_white white_history) (scheduled_black black_history)) = linear_state.
Proof. vm_compute. reflexivity. Qed.

Theorem linear_state_valid : valid_state linear_state.
Proof.
  rewrite <- linear_state_is_legal_prefix. apply prefix_validity;
    [cbn; lia|apply initial_state_valid].
Qed.

Theorem linear_state_nonterminal : quiet linear_state.
Proof. vm_compute. split; reflexivity. Qed.
'''
    source += decoder_source('decoder0', d0) + decoder_source('decoder1', d1)
    source += f'''
Theorem linear_certificate_checks : linear_leafb decoder0 decoder1 linear_state = true.
Proof. vm_compute. reflexivity. Qed.

Theorem linear_state_total_defense : exists b : BlackStrategy, forall w : WhiteStrategy,
  outcome (step_game {remaining} true linear_state w b) <> WhiteWins.
Proof.
  exact (checked_linear_leaf_total_defense decoder0 decoder1 linear_state {remaining}
    linear_certificate_checks linear_state_valid eq_refl).
Qed.

Theorem information_set_sizes :
  length (decoder_cells decoder0) = {len(d0)} /\\ length (decoder_cells decoder1) = {len(d1)}.
Proof. split; reflexivity. Qed.

Theorem pair_capacity_fails :
  length (residual_rows linear_state) = {len(rows)} /\\
  length (filter (is_legal_move linear_state) all_cells) = {remaining} /\\
  2 * length (residual_rows linear_state) > length (filter (is_legal_move linear_state) all_cells).
Proof. vm_compute. repeat split; lia. Qed.

Theorem no_static_pairing_defense_exists : forall mate,
  well_mated mate -> ~ pairing_safe mate linear_state.
Proof.
  intros mate Hmate Hsafe.
  pose proof (every_static_pairing_needs_capacity linear_state mate Hmate Hsafe) as Hcapacity.
  assert (Hlines : length (unblocked_lines linear_state) = {len(rows)}) by (vm_compute; reflexivity).
  assert (Hfree : length (empty_cells linear_state) = {remaining}) by (vm_compute; reflexivity).
  rewrite Hlines, Hfree in Hcapacity. lia.
Qed.

Theorem linear_defense_strictly_beyond_pairing :
  (exists b : BlackStrategy, forall w : WhiteStrategy,
    outcome (step_game {remaining} true linear_state w b) <> WhiteWins) /\\
  (forall mate, well_mated mate -> ~ pairing_safe mate linear_state).
Proof. split; [exact linear_state_total_defense|exact no_static_pairing_defense_exists]. Qed.

Definition local_linear_tree : LinearDefenseCertificate := LinearLeaf decoder0 decoder1.

Theorem local_linear_tree_checks : linear_treeb local_linear_tree linear_state = true.
Proof. exact linear_certificate_checks. Qed.

Theorem local_linear_tree_does_not_check_empty : linear_treeb local_linear_tree initial_state = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions linear_state_total_defense.
Print Assumptions pair_capacity_fails.
Print Assumptions linear_defense_strictly_beyond_pairing.
'''
    return source


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--data', default='linear_leaf.json')
    parser.add_argument('--output', default='Witness.v')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    data = json.loads((root / args.data).read_text(encoding='utf-8'))
    source = generate(data)
    target = root / args.output
    if args.check:
        if target.read_text(encoding='utf-8') != source:
            raise RuntimeError(f'{target.name} differs from the decoder generator')
        print('Decoder certificate reproduced and independently reconstructed all residual rows.')
    else:
        target.write_text(source, encoding='utf-8')
        print(f'Wrote {target}')


if __name__ == '__main__':
    main()
