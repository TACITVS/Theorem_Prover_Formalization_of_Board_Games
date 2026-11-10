"""Re-score saved hybrid layouts with the Python reference evaluator.

Accepts hybrid.py JSON checkpoints or hybrid.c text layouts ("score s" then 125
region ids). Prints the capacity shortfall 2*rank - cells and the exact
shortfall 2*rank - max(|I0| + |I1|). Use --white/--black for game positions.
"""
import argparse
import json
from pathlib import Path

import hybrid
from fragment_search import LINES, columns, two_disjoint_bases


def load(path: str) -> dict:
    text = Path(path).read_text()
    if text.lstrip().startswith('{'):
        return {int(k): v for k, v in json.loads(text)['region'].items()}
    nums = text.split()
    if nums[0] == 'score':
        nums = nums[2:]
    return {c: int(v) for c, v in enumerate(nums[:125])}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('layouts', nargs='+')
    ap.add_argument('--white', default='')
    ap.add_argument('--black', default='')
    args = ap.parse_args()
    white = [int(x) for x in args.white.split(',') if x]
    black = [int(x) for x in args.black.split(',') if x]
    occ = set(white) | set(black)
    free = [c for c in range(125) if c not in occ]
    live = [[c for c in l if c not in occ] for l in LINES if not set(l) & set(black)]
    for path in args.layouts:
        reg = load(path)
        reg = {c: reg[c] for c in free}
        sc, d = hybrid.evaluate(reg, live, free, 64, detail=True)
        ok, r, i0, i1 = two_disjoint_bases(columns(d['masks'], d['ccells']))
        print(f'{path}: penalty {d["penalty"]}, rank {r}, code cells {len(d["ccells"])}, '
              f'capacity shortfall {2 * r - len(d["ccells"])}, '
              f'exact shortfall {2 * r - len(i0) - len(i1)}, '
              f'potential lines {d["potential_lines"]}', flush=True)


if __name__ == '__main__':
    main()
