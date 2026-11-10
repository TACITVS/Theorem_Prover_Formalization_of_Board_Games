"""Exact binary linear-algebra experiments for Qubic's 109 straight lines.

Search output is evidence, not a Rocq theorem or an empty-board strategy.
The two information sets are certified by independent rank computations.
"""
from __future__ import annotations

import argparse
from collections import deque
import itertools
import json
from pathlib import Path
import random
import time


def geometric_lines() -> list[tuple[int, ...]]:
    def coordinate(mode: int, t: int) -> int:
        return mode if mode < 5 else t if mode == 5 else 4 - t
    result = []
    for modes in itertools.product(range(7), repeat=3):
        if max(modes) < 5:
            continue
        line = tuple(sum(a * coordinate(m, t) for a, m in zip((1, 5, 25), modes)) for t in range(5))
        if line[0] < line[-1]:
            result.append(line)
    assert len(result) == len(set(result)) == 109
    return sorted(result)


LINES = geometric_lines()
MASKS = [sum(1 << c for c in line) for line in LINES]


def bitmask(cells) -> int:
    return sum(1 << c for c in cells)


def wins(cells: set[int]) -> bool:
    occupied = bitmask(cells)
    return any(occupied & line == line for line in MASKS)


def rank(vectors) -> int:
    pivots = {}
    for vector in vectors:
        while vector:
            p = vector.bit_length() - 1
            if p in pivots:
                vector ^= pivots[p]
            else:
                pivots[p] = vector
                break
    return len(pivots)


def residual_rows(white: set[int], black: set[int]) -> list[int]:
    wm, bm = bitmask(white), bitmask(black)
    return [line & ~wm for line in MASKS if not line & bm]


def tracking_basis(columns: dict[int, int], cells: set[int]):
    pivots = {}
    for cell in sorted(cells):
        vector, expression = columns[cell], 1 << cell
        while vector:
            p = vector.bit_length() - 1
            if p in pivots:
                vector ^= pivots[p][0]
                expression ^= pivots[p][1]
            else:
                pivots[p] = (vector, expression)
                break
        else:
            raise AssertionError('Dependent candidate basis')
    return pivots


def reduce_with_expression(vector: int, basis) -> tuple[bool, int]:
    expression = 0
    while vector:
        p = vector.bit_length() - 1
        if p not in basis:
            return False, expression
        vector ^= basis[p][0]
        expression ^= basis[p][1]
    return True, expression


def two_information_sets(rows: list[int], free: list[int]):
    columns = {c: sum(1 << i for i, row in enumerate(rows) if row >> c & 1) for c in free}
    r = rank(columns.values())
    sets: list[set[int]] = [set(), set()]
    for root in free:
        if sum(map(len, sets)) == 2 * r:
            break
        bases = [tracking_basis(columns, part) for part in sets]
        queue, parents, seen, found = deque([root]), {}, {root}, None
        while queue and found is None:
            x = queue.popleft()
            for color in range(2):
                if x in sets[color]:
                    continue
                dependent, expression = reduce_with_expression(columns[x], bases[color])
                if not dependent:
                    found = x, color
                    break
                for y in sorted(sets[color]):
                    if expression >> y & 1 and y not in seen:
                        seen.add(y)
                        parents[y] = x, color
                        queue.append(y)
        if found is not None:
            current, color = found
            sets[color].add(current)
            while current in parents:
                previous, color = parents[current]
                sets[color].remove(current)
                sets[color].add(previous)
                current = previous
            assert not sets[0] & sets[1]
            assert all(rank(columns[c] for c in part) == len(part) for part in sets)
    if sum(map(len, sets)) != 2 * r:
        return None
    # Independent final checks do not depend on the augmenting-path algorithm.
    assert not sets[0] & sets[1]
    assert all(rank(row & bitmask(part) for row in rows) == r for part in sets)
    return [sorted(part) for part in sets]


def search(trials: int, seed: int):
    rng = random.Random(seed)
    start = time.monotonic()
    for trial in range(trials):
        white: list[int] = []
        black: list[int] = []
        for round_number in range(1, 12):
            free = [c for c in range(125) if c not in white + black]
            choices_w = [c for c in free if not wins(set(white + [c]))]
            if not choices_w:
                break
            x = rng.choice(choices_w)
            white.append(x)
            choices_b = []
            for y in free:
                if y == x or wins(set(black + [y])):
                    continue
                rows = residual_rows(set(white), set(black + [y]))
                choices_b.append((rank(rows), len(rows), rng.random(), y))
            if not choices_b:
                break
            black.append(min(choices_b)[3])
            rows = residual_rows(set(white), set(black))
            available = [c for c in range(125) if c not in white + black]
            if 2 * rank(rows) > len(available) or 2 * len(rows) <= len(available):
                continue
            info = two_information_sets(rows, available)
            if info is not None:
                assert not wins(set(white)) and not wins(set(black))
                return {
                    'white': white, 'black': black, 'rounds': round_number,
                    'surviving_lines': len(rows), 'free_cells': len(available),
                    'binary_rank': rank(rows), 'information_sets': info,
                    'static_pairing_capacity_fails': 2 * len(rows) > len(available),
                    'seed': seed, 'trial': trial, 'elapsed_seconds': time.monotonic() - start,
                }
        if trial % 100 == 0:
            print(f'trial={trial} elapsed={time.monotonic()-start:.2f}s', flush=True)
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trials', type=int, default=1000)
    parser.add_argument('--seed', type=int, default=2102)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('linear_leaf.json'))
    args = parser.parse_args()
    result = search(args.trials, args.seed)
    if result is None:
        print('UNKNOWN: no nonterminal strict improvement found in this bounded search.')
        return
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
    print('EXPERIMENTAL: no claim about reachability against every opponent or initial game value.')


if __name__ == '__main__':
    main()
