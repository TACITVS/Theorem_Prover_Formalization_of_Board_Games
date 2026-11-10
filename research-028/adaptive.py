"""Adaptive-depth repair of uncovered branches in a depth-2 tree.

For a White move m at the root position, find a Black reply r such that every
White move m2 at P+m+r has a reply leading to a code leaf (depth 1) or, failing
that, to a depth-1-covered position (depth 2). Results are merged into the tree
JSON (checkpoint per root move). A hard time cap keeps each run short.
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import tree_extend as t
from fragment_search import LINES, games


def blocking_cells(white, black, m):
    """Free cells on lines that m turns into a live line with 3 White stones."""
    occ = set(white) | set(black) | {m}
    out = []
    for l in LINES:
        if m in l and not set(l) & set(black) and len(set(l) & (set(white) | {m})) >= 3:
            out += [c for c in l if c not in occ]
    return list(dict.fromkeys(out))


def repair(white, black, m, deadline, log, prefer=()):
    w2 = white + [m]
    occ = set(w2) | set(black)
    first = [c for c in prefer if c not in occ] + blocking_cells(white, black, m)
    first = list(dict.fromkeys(first))
    rest = [c for c in range(125) if c not in occ and c not in first]
    for i, r in enumerate(first + rest):
        if time.time() > deadline:
            return None, 'time cap'
        b2 = black + [r]
        tree = {}
        ok = True
        for m2 in [c for c in range(125) if c not in occ and c != r]:
            sub = t.reply_subtree(w2, b2, m2, 1, 125)
            if sub is None:
                log(f'      Black {r}: White {m2} needs depth 2 ...')
                sub = t.reply_subtree(w2, b2, m2, 2, 40)
            if sub is None or time.time() > deadline:
                ok = False
                log(f'      Black {r} fails at White {m2}')
                break
            tree[m2] = sub
        if ok:
            return [r, tree], f'Black {r} (candidate {i + 1})'
    return None, 'no reply works'


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('tree_json')
    ap.add_argument('--game', default='r021-witness')
    ap.add_argument('--round', type=int, default=8)
    ap.add_argument('--moves', type=int, nargs='+', required=True)
    ap.add_argument('--minutes', type=float, default=9)
    ap.add_argument('--prefer', type=int, nargs='*', default=[], help='Black replies to try first')
    args = ap.parse_args()
    path = Path(args.tree_json)
    state = json.loads(path.read_text(encoding='utf-8'))
    white, black = games()[args.game]
    white, black = white[:args.round], black[:args.round]
    t0 = time.time()
    deadline = t0 + 60 * args.minutes
    for m in args.moves:
        if state.get(str(m)) is not None:
            print(f'White {m}: already covered', flush=True)
            continue
        print(f'White {m}: candidates {blocking_cells(white, black, m)} first', flush=True)
        sub, why = repair(white, black, m, deadline,
                          lambda s: print(f'{s}  [{time.time() - t0:.0f}s]', flush=True),
                          args.prefer)
        print(f'White {m}: {"COVERED by " if sub else "not covered: "}{why}, '
              f'{time.time() - t0:.0f}s', flush=True)
        if sub:
            state[str(m)] = sub
            tmp = path.with_suffix('.tmp')
            tmp.write_text(json.dumps(state), encoding='utf-8')
            tmp.replace(path)
        if time.time() > deadline:
            print('time cap reached; rerun to continue (covered moves are saved)', flush=True)
            break


if __name__ == '__main__':
    main()
