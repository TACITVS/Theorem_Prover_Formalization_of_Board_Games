"""Research 029: when do Black certificates appear in engine-vs-engine games?

For every White-to-move position of every game in a games.jsonl file, this
records:

- the immediate threats of each side (a line with 4 stones of one colour and
  none of the other);
- whether a pairing exists (each live line has 2 private free cells; max flow);
- whether a whole-line GF(2) code leaf exists (exact matroid partition, as
  research 021/028);
- the capacity numbers: free cells, live lines, GF(2) rank.

A position is *trivial* when Black already threatens to win. This is data, not
proof: a certificate found here must still be exported and checked in Rocq
(research-028/export_tree.py).
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'research-028'))
from fragment_search import (columns, gf2_rank, mask, pairing_feasible,  # noqa: E402
                             residual, two_disjoint_bases)
from tree_extend import white_threats  # noqa: E402


def analyse_position(white, black) -> dict:
    free, live, res = residual(white, black)
    rows = [mask(r) for r in res]
    rank = gf2_rank(rows)
    info = {'free': len(free), 'live': len(live), 'rank': rank,
            'black_threats': len(white_threats(black, white)),
            'white_threats': len(white_threats(white, black)),
            'pairing': pairing_feasible(res, free) if all(len(r) >= 2 for r in res) else False}
    info['code'] = (all(len(r) >= 2 for r in res) and 2 * rank <= len(free)
                    and two_disjoint_bases(columns(rows, free))[0])
    return info


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('games', nargs='+')
    ap.add_argument('--out', default='activation.json')
    args = ap.parse_args()
    games = []
    for path in args.games:
        for line in Path(path).read_text(encoding='utf-8').splitlines():
            g = json.loads(line)
            if g['status'] == 'done':
                games.append(g)
    print(f'{len(games)} games', flush=True)
    t0 = time.time()
    results = []
    for gi, g in enumerate(games):
        mv = g['moves']
        rows = []
        for k in range(1, len(mv) // 2 + 1):
            white, black = mv[0:2 * k:2], mv[1:2 * k:2]
            rows.append({'round': k, **analyse_position(white, black)})
        first = {}
        for key in ('code', 'pairing'):
            hit = [r for r in rows if r[key]]
            first[key] = hit[0]['round'] if hit else None
            nontriv = [r for r in rows if r[key] and r['black_threats'] == 0]
            first[key + '_nontrivial'] = nontriv[0]['round'] if nontriv else None
        first['black_threat'] = next((r['round'] for r in rows if r['black_threats']), None)
        results.append({'id': g['id'], 'result': g['result'], 'first': first, 'rows': rows})
        print(f'  game {g["id"]:3d} ({g["result"]}): first code leaf round {first["code"]} '
              f'(non-trivial {first["code_nontrivial"]}), first pairing {first["pairing"]}, '
              f'first Black threat {first["black_threat"]}  [{time.time() - t0:.0f}s]', flush=True)
    Path(args.out).write_text(json.dumps(results), encoding='utf-8')
    for key in ('code_nontrivial', 'pairing_nontrivial'):
        vals = [r['first'][key] for r in results if r['first'][key] is not None]
        print(f'{key}: {len(vals)}/{len(results)} games, rounds {sorted(vals)}', flush=True)
    # capacity trend: mean over games of (2*rank - free) per round, the code deficit
    by_round: dict = {}
    for r in results:
        for row in r['rows']:
            by_round.setdefault(row['round'], []).append(2 * row['rank'] - row['free'])
    print('mean code deficit 2*rank - free by round (<= 0 needed):',
          {k: round(sum(v) / len(v), 1) for k, v in sorted(by_round.items())}, flush=True)


if __name__ == '__main__':
    main()
