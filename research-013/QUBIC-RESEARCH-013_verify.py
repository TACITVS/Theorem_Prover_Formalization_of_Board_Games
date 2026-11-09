"""QUBIC-RESEARCH-013: independent, typed safe-leaf certificate verifier.

Verifies a nonterminal 10-round pairing-safe position and every immediate
White continuation. No global variables or trusted external solver is used.
"""

from __future__ import annotations

import argparse
import json
from itertools import product
from pathlib import Path
from typing import TypeAlias

Point: TypeAlias = tuple[int, int, int]
Line: TypeAlias = tuple[Point, Point, Point, Point, Point]
Pair: TypeAlias = tuple[Point, Point]


def convert_point(values: list[int]) -> Point:
    if len(values) != 3:
        raise ValueError(f"Invalid point: {values!r}")
    return (int(values[0]), int(values[1]), int(values[2]))


def generate_lines() -> tuple[Line, ...]:
    coordinates = range(-2, 3)
    directions: tuple[Point, ...] = (
        (1, 0, 0), (0, 1, 0), (0, 0, 1),
        (1, 1, 0), (1, -1, 0), (1, 0, 1), (1, 0, -1),
        (0, 1, 1), (0, 1, -1),
        (1, 1, 1), (1, 1, -1), (1, -1, 1), (1, -1, -1),
    )
    result: list[Line] = []
    for direction in directions:
        for midpoint in product(coordinates, repeat=3):
            if any(
                delta != 0 and coordinate != 0
                for delta, coordinate in zip(direction, midpoint)
            ):
                continue
            points = tuple(
                tuple(midpoint[axis] + step * direction[axis]
                      for axis in range(3))
                for step in coordinates
            )
            result.append(points)  # type: ignore[arg-type]
    assert len(result) == len(set(result)) == 109
    return tuple(result)


def has_win(stones: set[Point], lines: tuple[Line, ...]) -> bool:
    return any(set(line).issubset(stones) for line in lines)


def verify_certificate(certificate_path: Path) -> None:
    data = json.loads(certificate_path.read_text(encoding="utf-8"))
    all_points = set(product(range(-2, 3), repeat=3))
    lines = generate_lines()
    line_set = set(lines)

    white = [convert_point(point) for point in data["white"]]
    black = [convert_point(point) for point in data["black"]]
    white_set = set(white)
    black_set = set(black)
    assert len(white) == len(white_set) == 10
    assert len(black) == len(black_set) == 10
    assert white_set.isdisjoint(black_set)
    assert white_set | black_set <= all_points

    pair_map: dict[Line, Pair] = {}
    used: set[Point] = set()
    for entry in data["pairs"]:
        line = tuple(convert_point(p) for p in entry["line"])
        assert len(line) == 5 and line in line_set
        point_a, point_b = [convert_point(p) for p in entry["endpoints"]]
        assert point_a != point_b
        assert point_a in line and point_b in line
        assert point_a not in used and point_b not in used
        assert point_a not in white_set | black_set
        assert point_b not in white_set | black_set
        assert line not in pair_map
        pair_map[line] = (point_a, point_b)
        used.update((point_a, point_b))

    surviving = {line for line in lines if black_set.isdisjoint(line)}
    blocked = set(lines) - surviving
    assert surviving == set(pair_map)
    assert len(blocked) == 57
    assert len(surviving) == 52
    assert len(pair_map) == 52
    assert len(used) == 104
    assert not has_win(white_set, lines)
    assert not has_win(black_set, lines)

    remaining = all_points - white_set - black_set
    assert len(remaining) == 105
    assert len(remaining - used) == 1

    # This position is reachable in ten strictly legal, nonterminal rounds:
    # no subset of either player's final stones can already be winning.
    running_white: set[Point] = set()
    running_black: set[Point] = set()
    for white_move, black_move in zip(white, black):
        assert white_move not in running_white | running_black
        running_white.add(white_move)
        assert not has_win(running_white, lines)
        assert black_move not in running_white | running_black
        running_black.add(black_move)
        assert not has_win(running_black, lines)

    # Verify the natural pairing response and updated certificate for every
    # possible legal first White continuation (105 total possibilities).
    for white_move in remaining:
        affected_line = next(
            (line for line, (a, b) in pair_map.items()
             if white_move in (a, b)),
            next(iter(pair_map)),
        )
        pair_a, pair_b = pair_map[affected_line]
        black_reply = pair_a if white_move == pair_b else pair_b
        assert black_reply in remaining and black_reply != white_move
        white_next = white_set | {white_move}
        black_next = black_set | {black_reply}
        assert not has_win(white_next, lines)
        for line in lines:
            if not black_next.isdisjoint(line):
                continue
            assert line in pair_map and line != affected_line
            endpoints = set(pair_map[line])
            assert endpoints.isdisjoint(white_next | black_next)

    print("QUBIC-RESEARCH-013: ALL CHECKS PASSED")
    print("Board: 125 cells; 109 winning lines")
    print("Position: 10 White, 10 Black; both nonterminal")
    print("Black covers 57 lines; 52 surviving lines have 52 disjoint pairs")
    print("104 reserved endpoints and 1 remaining unreserved free cell")
    print("Legal, nonterminal 10-round history verified")
    print("All 105 immediate White continuations safely defended")
    print("This does NOT prove Black can force this position from empty play.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path, help="Path to JSON certificate")
    arguments = parser.parse_args()
    verify_certificate(arguments.certificate)


if __name__ == "__main__":
    main()
