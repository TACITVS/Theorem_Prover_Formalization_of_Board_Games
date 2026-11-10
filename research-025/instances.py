"""Shared finite Qubic instances. No instance asserts the full game value."""
from __future__ import annotations

import json
from pathlib import Path
import sys

from pysat.card import CardEnc, EncType

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'research-021'))
from linear_search import LINES


class Formula:
    def __init__(self):
        self.nvars = 0
        self.clauses = []

    def variable(self):
        self.nvars += 1
        return self.nvars

    def conjunction(self, literals):
        literals = list(literals)
        result = self.variable()
        self.clauses.extend([[-result, lit] for lit in literals])
        self.clauses.append([result] + [-lit for lit in literals])
        return result

    def disjunction(self, literals):
        return -self.conjunction([-lit for lit in literals])

    def atmost(self, literals, bound):
        encoded = CardEnc.atmost(list(literals), bound=bound, top_id=self.nvars,
                                 encoding=EncType.seqcounter)
        self.nvars = max(self.nvars, encoded.nv)
        self.clauses.extend(encoded.clauses)

    def exactly_one(self, literals):
        self.clauses.append(list(literals))
        self.atmost(literals, 1)

    def data(self, name, kind, **metadata):
        return dict(name=name, kind=kind, nvars=self.nvars,
                    clauses=self.clauses, **metadata)


def coloring():
    f = Formula()
    cells = [f.variable() for _ in range(125)]
    for line in LINES:
        f.clauses.append([cells[c] for c in line])
        f.clauses.append([-cells[c] for c in line])
    return f.data('draw_coloring', 'coloring', cells=cells)


def parity(bound):
    f = Formula()
    selected = [f.variable() for _ in LINES]
    f.atmost(selected, bound)
    for cell in range(125):
        terms = [selected[i] for i, line in enumerate(LINES) if cell in line]
        previous = terms[0]
        for term in terms[1:]:
            result = f.variable()
            f.clauses.extend([[previous, term, -result],
                              [-previous, -term, -result],
                              [previous, -term, result],
                              [-previous, term, result]])
            previous = result
        f.clauses.append([previous if cell == 62 else -previous])
    return f.data(f'center_xor_atmost_{bound}', 'parity', selected=selected,
                  bound=bound)


def pairing(name, white, black):
    f = Formula()
    used = [[] for _ in range(125)]
    pairs = []
    for index, line in enumerate(LINES):
        if set(line) & set(black):
            continue
        free = [c for c in line if c not in white]
        choices = []
        for i, a in enumerate(free):
            for b in free[i + 1:]:
                variable = f.variable()
                choices.append(variable)
                used[a].append(variable)
                used[b].append(variable)
                pairs.append([variable, index, a, b])
        f.exactly_one(choices)
    for incident in used:
        if incident:
            f.atmost(incident, 1)
    return f.data(name, 'pairing', pairs=pairs, white=white, black=black)


def counterexample(policy, plies):
    """Exists a legal trace whose FIRST terminal event is White winning at plies.

    This is a query at an exact depth. Shorter first wins are excluded.
    Black requests either zero, or the lowest White completion cell then zero,
    with the same lowest-free-cell fallback used by the frozen rules.
    """
    assert plies % 2 == 1
    f = Formula()
    false = f.variable()
    f.clauses.append([-false])
    white = [false] * 125
    black = [false] * 125
    moves = []
    for ply in range(1, plies + 1):
        move = [f.variable() for _ in range(125)]
        moves.append(move)
        f.exactly_one(move)
        occupied = [f.disjunction([white[c], black[c]]) for c in range(125)]
        for c in range(125):
            f.clauses.append([-move[c], -occupied[c]])
        if ply % 2 == 0:
            if policy == 'blocker':
                completion = []
                for c in range(125):
                    supports = [f.conjunction(white[d] for d in line if d != c)
                                for line in LINES if c in line]
                    completion.append(f.conjunction([-occupied[c],
                                                      f.disjunction(supports)]))
            else:
                completion = [false] * 125
            any_completion = f.disjunction(completion)
            earlier_completion = false
            earlier_free = false
            for c in range(125):
                # Choose the first completion, otherwise the first free cell.
                f.clauses.append([-move[c], -earlier_completion])
                f.clauses.append([-move[c], completion[c], -any_completion])
                f.clauses.append([-move[c], any_completion, -earlier_free])
                earlier_completion = f.disjunction([earlier_completion, completion[c]])
                earlier_free = f.disjunction([earlier_free, -occupied[c]])
        if ply % 2:
            white = [f.disjunction([white[c], move[c]]) for c in range(125)]
        else:
            black = [f.disjunction([black[c], move[c]]) for c in range(125)]
        if ply < plies:
            for line in LINES:
                f.clauses.append([-white[c] for c in line])
                f.clauses.append([-black[c] for c in line])
        else:
            f.clauses.append([f.conjunction(white[c] for c in line) for line in LINES])
    return f.data(f'{policy}_first_white_win_ply_{plies}', 'trace',
                  policy=policy, plies=plies, moves=moves)


def build_instances():
    root = Path(__file__).resolve().parents[1]
    state = json.loads((root / 'research-021/linear_leaf.json').read_text())
    restricted = counterexample('blocker', 15)
    restricted['name'] += '_two_line_region'
    region = set([100, 101, 102, 103, 104, 105, 110, 115, 120])
    for move in restricted['moves'][::2]:
        restricted['clauses'].extend([[-var] for c, var in enumerate(move) if c not in region])
    restricted['white_region'] = sorted(region)
    blocking_region = counterexample('blocker', 15)
    blocking_region['name'] += '_two_line_region_with_block4'
    region_with_block = set([4, 29, 54, 79, 104, 100, 101, 102, 103])
    for move in blocking_region['moves'][::2]:
        blocking_region['clauses'].extend([[-var] for c, var in enumerate(move)
                                           if c not in region_with_block])
    blocking_region['white_region'] = sorted(region_with_block)
    return [coloring(), parity(19), parity(17),
            pairing('pairing_empty', [], []),
            pairing('pairing_strict_linear_leaf', state['white'], state['black']),
            pairing('pairing_safe10',
                    [121, 122, 103, 123, 109, 114, 94, 119, 49, 74],
                    [0, 100, 95, 31, 81, 62, 108, 43, 29, 124]),
            counterexample('lowest', 9), counterexample('blocker', 13),
            counterexample('blocker', 15), restricted, blocking_region]


def validate_pairing(instance, selected):
    used, protected = set(), set()
    for index, a, b in selected:
        if index not in range(109) or index in protected:
            raise ValueError('Invalid or repeated line index')
        if a == b or a not in LINES[index] or b not in LINES[index]:
            raise ValueError('Invalid line pair')
        if a in used or b in used or {a, b} & set(instance['white'] + instance['black']):
            raise ValueError('Pair reuses an occupied or paired cell')
        used.update([a, b])
        protected.add(index)
    for index, line in enumerate(LINES):
        if not set(line) & set(instance['black']) and index not in protected:
            raise ValueError('Uncovered winning line')
    return dict(selected_pairs=selected)


def validate_model(instance, model):
    values = set(lit for lit in model if lit > 0)
    if not all(any((lit in values) if lit > 0 else (-lit not in values)
                   for lit in clause) for clause in instance['clauses']):
        raise ValueError('Returned assignment violates the CNF')
    kind = instance['kind']
    if kind == 'trace':
        history = [next(c for c, var in enumerate(move) if var in values)
                   for move in instance['moves']]
        witness = dict(history=history)
    elif kind == 'parity':
        witness = dict(selected_lines=[i for i, var in enumerate(instance['selected']) if var in values])
    elif kind == 'coloring':
        witness = dict(white_cells=[c for c, var in enumerate(instance['cells']) if var in values])
    else:
        witness = dict(selected_pairs=[entry[1:] for entry in instance['pairs'] if entry[0] in values])
    return validate_witness(instance, witness)


def validate_witness(instance, witness):
    kind = instance['kind']
    if kind == 'trace':
        history = witness['history']
        if len(history) != instance['plies']:
            raise ValueError('Wrong trace length')
        white, black = set(), set()
        for ply, c in enumerate(history, 1):
            free = set(range(125)) - white - black
            if c not in free:
                raise ValueError('Illegal move in solver trace')
            if ply % 2 and c not in instance.get('white_region', range(125)):
                raise ValueError('White move outside the restricted region')
            if ply % 2 == 0:
                targets = [d for d in sorted(free)
                           if any(set(line) <= white | {d} for line in LINES)]
                expected = targets[0] if instance['policy'] == 'blocker' and targets else min(free)
                if c != expected:
                    raise ValueError('Trace violates fixed Black policy')
            (white if ply % 2 else black).add(c)
            winner = any(set(line) <= white for line in LINES) or any(
                set(line) <= black for line in LINES)
            if winner != (ply == len(history)):
                raise ValueError('Trace has wrong terminal timing')
        return dict(history=history)
    if kind == 'parity':
        indices = witness['selected_lines']
        if len(set(indices)) != len(indices) or any(i not in range(109) for i in indices):
            raise ValueError('Invalid line indices')
        word = 0
        for i in indices:
            word ^= sum(1 << c for c in LINES[i])
        if word != 1 << 62 or len(indices) > instance['bound']:
            raise ValueError('Invalid parity witness')
        return dict(selected_lines=indices)
    if kind == 'coloring':
        white = witness['white_cells']
        if len(set(white)) != len(white) or any(c not in range(125) for c in white):
            raise ValueError('Invalid coloring cells')
        if any(all(c in white for c in line) or all(c not in white for c in line)
               for line in LINES):
            raise ValueError('Monochromatic winning line')
        return dict(white_cells=white)
    return validate_pairing(instance, witness['selected_pairs'])
