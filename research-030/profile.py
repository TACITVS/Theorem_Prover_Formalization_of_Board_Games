"""Profile the best valid code regions found by density.exe (independent check).

For each checkpoint: re-derive fragments, check two disjoint bases with the
research-028 reference (Edmonds partition), and print F, L, rank, slack
F - 2*rank, dependencies L - rank and the fragment-size histogram.
"""
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'research-028'))
from fragment_search import LINES, columns, two_disjoint_bases  # noqa: E402


def main() -> None:
    lines_sorted = sorted(tuple(sorted(l)) for l in LINES)
    for p in sorted(Path('density_ckpt').glob('seed*.txt'), key=lambda q: int(q.stem[4:])):
        toks = p.read_text().split('\n')
        cells = {int(x) for x in toks[1].split()[1:]}
        S = [int(x) for x in toks[2].split()[1:]]
        frags = [frozenset(c for c in lines_sorted[l] if c in cells) for l in S]
        frags = [f for f in frags if len(f) >= 2]
        masks = [sum(1 << c for c in f) for f in frags]
        ok, r, i0, i1 = two_disjoint_bases(columns(masks, sorted(cells)))
        F, L = len(cells), len(frags)
        hist = dict(sorted(Counter(len(f) for f in frags).items()))
        print(f'{p.stem:7s} F {F:3d} L {L:3d} rank {r:3d} valid {ok and 2 * r == len(i0) + len(i1)} '
              f'slack {F - 2 * r:3d} deps {L - r:3d} 6L-5F {6 * L - 5 * F:5d} sizes {hist}')


if __name__ == '__main__':
    main()
