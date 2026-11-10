"""Exact tensor/boundary calculations; these are experiments, not Rocq proofs.

All arithmetic is over F_2, using integer bitsets. Only the original 109
geometric lines are used; affine lines wrapping around the cube are excluded.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import linear_search as ls


def apply_columns(columns: list[int], vector: int) -> int:
    result = 0
    while vector:
        low = vector & -vector
        result ^= columns[low.bit_length() - 1]
        vector ^= low
    return result


def calculate() -> dict:
    # The join of three discrete five-point sets: vertices X,Y,Z; edges XY,
    # XZ,YZ; triangles (x,y,z). A triangle's boundary is its three edges.
    edges = [(a, b) for a in range(15) for b in range(a + 1, 15) if a // 5 != b // 5]
    edge_index = {edge: i for i, edge in enumerate(edges)}
    d1 = [(1 << a) | (1 << b) for a, b in edges]
    d2 = []
    for c in range(125):
        x, y, z = c % 5, (c // 5) % 5, c // 25
        triangle_edges = [(x, 5 + y), (x, 10 + z), (5 + y, 10 + z)]
        d2.append(ls.bitmask(edge_index[edge] for edge in triangle_edges))
    assert all(apply_columns(d1, boundary) == 0 for boundary in d2)
    axis_rows = [ls.bitmask(c for c, boundary in enumerate(d2) if boundary >> i & 1)
                 for i in range(75)]
    assert len(set(axis_rows)) == 75 and set(axis_rows) <= set(ls.MASKS)

    # Tensor basis of ker(d2): (e_i+e_4) tensor (e_j+e_4) tensor (e_k+e_4).
    # These are the eight corners of each {i,4} x {j,4} x {k,4} subbox.
    cycles = [ls.bitmask(x + 5 * y + 25 * z
                        for x, y, z in itertools.product((i, 4), (j, 4), (k, 4)))
              for i, j, k in itertools.product(range(4), repeat=3)]
    assert all(apply_columns(d2, cycle) == 0 for cycle in cycles)
    assert ls.rank(cycles) == 64
    r1, r2 = ls.rank(d1), ls.rank(d2)
    assert (r1, r2) == (14, 61)
    assert 125 - r2 == len(cycles)
    assert 75 - r1 - r2 == 0
    info = ls.two_information_sets(axis_rows, list(range(125)))
    assert info is not None and [len(part) for part in info] == [61, 61]
    full_rank = ls.rank(ls.MASKS)
    assert full_rank == 89
    return {
        'status': 'exact Python calculations, not Rocq theorems',
        'field': 'F_2',
        'tensor_shape': [5, 5, 5],
        'simplices': {'vertices': 15, 'edges': 75, 'triangles': 125},
        'boundary_squared_zero': True,
        'boundary_1_rank': r1,
        'boundary_2_rank': r2,
        'H1_dimension': 75 - r1 - r2,
        'H2_dimension': 125 - r2,
        'independent_eight_corner_cycles': len(cycles),
        'axis_line_count': 75,
        'axis_information_sets': info,
        'all_geometric_lines_count': len(ls.LINES),
        'full_incidence_rank': full_rank,
        'full_incidence_nullity': 125 - full_rank,
        'extra_diagonal_rank': full_rank - r2,
        'full_board_two_information_sets_ruled_out_by_counting': 2 * full_rank > 125,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    report = calculate()
    path = Path(__file__).with_name('tensor_structure.json')
    if args.check:
        if json.loads(path.read_text(encoding='utf-8')) != report:
            raise RuntimeError('Stored tensor report differs from exact recalculation')
        print('REPRODUCED: boundary identities, ranks, 64 tensor cycles, two axis information sets.')
    else:
        path.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
        print(f'Wrote {path}')
    print('EXPERIMENTAL: the 34 diagonals prevent applying this axis-only defense to the full empty board.')


if __name__ == '__main__':
    main()
