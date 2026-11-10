"""Independent re-check of a hybrid layout saved by hybrid.py.

It uses research-027's line generator and GF(2) rank, not research-028's. It
re-derives the line assignment from the saved region map with the same rule as
`hybrid.evaluate`, then checks every condition separately and prints the
structure. Capacity only; this is not a certificate.
"""
from __future__ import annotations

import json
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'research-027'))
from compute import LINES, rank_gf2  # noqa: E402

UNITS = {5: 1, 4: 2, 3: 4, 2: 8, 1: 16}


def main(path: str) -> None:
    region = {int(k): v for k, v in json.loads(Path(path).read_text())['region'].items()}
    assert sorted(region) == list(range(125)), 'empty-board layouts only'
    code_cells = [c for c in range(125) if region[c] < 0]
    budget = defaultdict(int)
    holds = defaultdict(list)
    code_rows, optional = [], []
    for l in LINES:                                   # empty board: all lines live
        cfrag = [c for c in l if region[c] < 0]
        per = defaultdict(list)
        for c in l:
            if region[c] >= 0:
                per[region[c]].append(c)
        if len(cfrag) < 2:
            assert per, f'line {l} has no region'
            j, cells = max(per.items(), key=lambda kv: len(kv[1]))
            budget[j] += UNITS[len(cells)]
            holds[j].append(cells)
        else:
            best = max(per.items(), key=lambda kv: len(kv[1]), default=None)
            if best and len(best[1]) >= 3:
                optional.append((UNITS[len(best[1])], l, best[0], best[1], cfrag))
            else:
                code_rows.append(cfrag)
    for u, l, j, cells, cfrag in sorted(optional):
        if budget[j] + u <= 15:
            budget[j] += u
            holds[j].append(cells)
        else:
            code_rows.append(cfrag)
    assert all(b <= 15 for b in budget.values()), budget
    assert all(len(r) >= 2 for r in code_rows)
    # pairwise: fragments in one region are subsets of distinct lines, so they meet in <= 1 cell
    r = rank_gf2(code_rows, code_cells)
    print(f'code region: {len(code_cells)} cells, {len(code_rows)} fragments, '
          f'sizes {sorted(len(x) for x in code_rows)}')
    print(f'code GF(2) rank {r}; shortfall 2*rank - cells = {2 * r - len(code_cells)}')
    coords = lambda c: (c % 5, c // 5 % 5, c // 25)
    print('code cells:', [coords(c) for c in code_cells])
    print(f'potential regions: {len(holds)}, lines held {sum(map(len, holds.values()))}, '
          f'budgets {sorted(budget.values())}')
    sizes = defaultdict(int)
    for j, fr in holds.items():
        for f in fr:
            sizes[len(f)] += 1
    print('potential fragment sizes:', dict(sorted(sizes.items())))
    print('total lines:', len(code_rows) + sum(map(len, holds.values())))


if __name__ == '__main__':
    main(sys.argv[1])
