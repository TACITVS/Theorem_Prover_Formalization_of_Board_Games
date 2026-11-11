"""Summary of dfpn.exe output (research 032): per game, the earliest ply at
which each kind of exact Breaker certificate holds, and how search effort grows
going backwards. Runs in under a second.
Usage: python frontier.py DFPN.jsonl [more files]
"""
import json
import sys
from statistics import median


def main():
    for path in sys.argv[1:]:
        recs = [json.loads(l) for l in open(path, encoding='utf-8')]
        done = [r for r in recs if r['status'] == 'done']
        ids = sorted({r['id'] for r in done})
        rows = []
        for g in ids:
            rs = [r for r in done if r['id'] == g]
            solved = [r for r in rs if r['result'] in ('maker', 'breaker')]

            def first(how):
                return min((r['ply'] for r in solved if r['how'] == how), default=None)

            rows.append({'id': g, 'es': first('es'), 'pairing': first('pairing'),
                         'solved': min(r['ply'] for r in solved),
                         'maker': sum(r['result'] == 'maker' for r in solved),
                         'closed': any(r['result'] == 'unknown' for r in rs)})
        print(f'{path}: {len(ids)} games, {sum(r["closed"] for r in rows)} closed by the budget')
        print(f'  positions solved as Maker wins: {sum(r["maker"] for r in rows)}')
        for name, key in (('Erdos-Selfridge', 'es'), ('pairing', 'pairing'), ('df-pn search', 'solved')):
            v = sorted(r[key] for r in rows if r[key] is not None)
            if v:
                print(f'  earliest ply decided by {name:<16}: min {v[0]}, median {median(v)}, max {v[-1]}'
                      f'  ({len(v)} games)')
        gain = sorted(r['pairing'] - r['solved'] for r in rows if r['pairing'] is not None)
        if gain:
            print(f'  plies gained by search over the pairing leaf: min {gain[0]}, median {median(gain)}, '
                  f'max {gain[-1]}')
        # effort by distance (in plies) before the first pairing position
        by = {}
        for r in rows:
            if r['pairing'] is None:
                continue
            for x in done:
                if x['id'] == r['id'] and x['how'] == 'search' and x['ply'] < r['pairing'] \
                        and x['ply'] % 2 == 0 and x['result'] == 'breaker':
                    by.setdefault(r['pairing'] - x['ply'], []).append(x['nodes'])
        for d in sorted(by):
            print(f'    Maker to move, {d:2d} plies before pairing: {len(by[d]):3d} positions, '
                  f'median {median(by[d]):,.0f} nodes, max {max(by[d]):,}')


if __name__ == '__main__':
    main()
