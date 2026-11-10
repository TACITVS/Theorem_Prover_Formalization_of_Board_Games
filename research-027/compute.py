"""Research 027: numbers behind the certificate programme.

Exact linear algebra and counting only; runs in a few seconds. Nothing here
decides the value of the game, and nothing here is a Rocq theorem.

  1. Rank of the 109 x 125 line/cell incidence matrix over GF(p) and Q.
  2. The same ranks for the 75 axis lines and for the 34 diagonals alone.
  3. Residual capacity after one and two rounds, for every first Black reply
     (up to symmetry of White's opening): pairing needs 2L <= F, the
     regional potential barrier needs 6L <= 5F, and a two-reserve code
     certificate needs 2 * rank <= F.
  4. Rough sizes of an opening tree that stops at activation depth d.
"""
from __future__ import annotations

import itertools
import json
from fractions import Fraction
from math import comb
from pathlib import Path


def cube_lines() -> list[tuple[int, ...]]:
    lines = set()
    dirs = [d for d in itertools.product((-1, 0, 1), repeat=3) if d != (0, 0, 0)]
    for start in itertools.product(range(5), repeat=3):
        for d in dirs:
            cells = [tuple(start[i] + t * d[i] for i in range(3)) for t in range(5)]
            if all(0 <= v < 5 for c in cells for v in c):
                lines.add(tuple(sorted(c[0] + 5 * c[1] + 25 * c[2] for c in cells)))
    return sorted(lines)


LINES = cube_lines()
assert len(LINES) == 109


def is_axis(line: tuple[int, ...]) -> bool:
    coords = [(c % 5, c // 5 % 5, c // 25) for c in line]
    return sum(len({p[i] for p in coords}) == 1 for i in range(3)) == 2


def rank_mod(rows: list[list[int]], p: int | None) -> int:
    """Rank over GF(p), or over Q when p is None."""
    m = [[Fraction(v) if p is None else v % p for v in row] for row in rows]
    rank, ncols = 0, len(m[0]) if m else 0
    for col in range(ncols):
        pivot = next((r for r in range(rank, len(m)) if m[r][col]), None)
        if pivot is None:
            continue
        m[rank], m[pivot] = m[pivot], m[rank]
        inv = 1 / m[rank][col] if p is None else pow(m[rank][col], p - 2, p)
        m[rank] = [v * inv if p is None else v * inv % p for v in m[rank]]
        for r in range(len(m)):
            if r != rank and m[r][col]:
                f = m[r][col]
                m[r] = [a - f * b if p is None else (a - f * b) % p
                        for a, b in zip(m[r], m[rank])]
        rank += 1
    return rank


def rank_gf2(lines, cells) -> int:
    """Fast GF(2) rank with integer bitsets."""
    index = {c: i for i, c in enumerate(cells)}
    basis: dict[int, int] = {}
    rank = 0
    for line in lines:
        v = 0
        for c in line:
            if c in index:
                v |= 1 << index[c]
        while v:
            top = v.bit_length() - 1
            if top in basis:
                v ^= basis[top]
            else:
                basis[top] = v
                rank += 1
                break
    return rank


def incidence(lines, cells) -> list[list[int]]:
    index = {c: i for i, c in enumerate(cells)}
    rows = []
    for line in lines:
        row = [0] * len(cells)
        for c in line:
            if c in index:
                row[index[c]] = 1
        rows.append(row)
    return rows


FIELDS = [2, 3, 5, 7, None]


def field_name(p):
    return 'Q' if p is None else f'GF({p})'


def full_ranks() -> dict:
    cells = list(range(125))
    axis = [l for l in LINES if is_axis(l)]
    diag = [l for l in LINES if not is_axis(l)]
    assert (len(axis), len(diag)) == (75, 34)
    out = {}
    for p in FIELDS:
        out[field_name(p)] = {
            'all_109': rank_mod(incidence(LINES, cells), p),
            'axis_75': rank_mod(incidence(axis, cells), p),
            'diagonal_34': rank_mod(incidence(diag, cells), p),
        }
    return out


def residual(white: list[int], black: list[int]):
    """Live lines (no Black stone) restricted to free cells."""
    occupied = set(white) | set(black)
    free = [c for c in range(125) if c not in occupied]
    live = [l for l in LINES if not set(l) & set(black)]
    residual_rows = [tuple(c for c in l if c not in occupied) for l in live]
    return free, live, residual_rows


def gf2_key(white, black):
    free, live, rows = residual(white, black)
    return rank_gf2(rows, free), len(live)


def capacity(white, black) -> dict:
    free, live, rows = residual(white, black)
    F, L = len(free), len(live)
    ranks = {field_name(p): rank_mod(incidence(rows, free), p) for p in [2, 3, 5, None]}
    assert ranks['GF(2)'] == rank_gf2(rows, free)
    return {
        'white': white, 'black': black, 'free': F, 'live_lines': L,
        'pairing_ok': 2 * L <= F,
        'regional_density_ok': 6 * L <= 5 * F,
        'ranks': ranks,
        'code_capacity_ok': {k: 2 * r <= F for k, r in ranks.items()},
    }


OPENINGS = [0, 1, 2, 7, 12, 62]   # the six opening classes of research 020/022


def round_one() -> list[dict]:
    rows = []
    for w in OPENINGS:
        best = min((gf2_key([w], [b]), b) for b in range(125) if b != w)
        rows.append(capacity([w], [best[1]]))
        print(f'      opening {w} done', flush=True)
    return rows


def round_two_center() -> dict:
    """White 0, Black 62, then the best second Black stone against each White move."""
    worst = None
    for n, w2 in enumerate(c for c in range(125) if c not in (0, 62)):
        best = min((gf2_key([0, w2], [62, b2]), b2)
                   for b2 in range(125) if b2 not in (0, 62, w2))
        if worst is None or best[0] > worst[0]:
            worst = (best[0], w2, best[1])
        if n % 20 == 0:
            print(f'      round two: {n + 1}/123 White moves scanned', flush=True)
    return capacity([0, worst[1]], [62, worst[2]])


def tree_sizes() -> list[dict]:
    # White chooses d cells; Black's replies are fixed by the strategy. Up to
    # the 96 game symmetries, roughly C(125, d) / 96 White move sets survive
    # transposition. A crude order of magnitude only.
    return [{'depth': d, 'white_move_sets': comb(125, d),
             'after_symmetry': comb(125, d) // 96} for d in range(1, 11)]


def main() -> None:
    result = {'full_incidence_ranks': full_ranks()}
    print('[1-2] incidence ranks (rows: lines, columns: 125 cells)', flush=True)
    for k, v in result['full_incidence_ranks'].items():
        print(f'      {k:7s} all 109: {v["all_109"]:3d}   axis 75: {v["axis_75"]:3d}'
              f'   diagonals 34: {v["diagonal_34"]:3d}')
    result['round_one_best_reply'] = round_one()
    print('[3]  after one round, Black reply minimising the GF(2) residual rank')
    for info in result['round_one_best_reply']:
        print(f'      W {info["white"][0]:3d} B {info["black"][0]:3d}: free {info["free"]},'
              f' live {info["live_lines"]}, ranks {info["ranks"]},'
              f' code capacity (2r<=F) {info["code_capacity_ok"]}')
    result['round_two_center_worst_case'] = round_two_center()
    info = result['round_two_center_worst_case']
    print(f'      round two after W0 B62, worst White move with best Black reply: '
          f'W {info["white"]} B {info["black"]}: free {info["free"]}, live {info["live_lines"]},'
          f' ranks {info["ranks"]}')
    result['tree_sizes'] = tree_sizes()
    print('[4]  activation depth d -> about C(125,d)/96 White move sets')
    for row in result['tree_sizes']:
        print(f'      d={row["depth"]:2d}: {row["after_symmetry"]:.3e}')
    out = Path(__file__).with_name('numbers.json')
    out.write_text(json.dumps(result, indent=1), encoding='utf-8')
    print(f'wrote {out.name}')


if __name__ == '__main__':
    main()
