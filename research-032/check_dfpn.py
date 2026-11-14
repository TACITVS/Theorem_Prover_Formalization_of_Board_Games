"""Independent check of dfpn.exe results (research 032).

Shares no code with the C programs. For every solved record it rebuilds the
position from the game file and then:
  - "es":      recomputes the Erdos-Selfridge potential and its threshold;
  - "pairing": finds the pairing itself with a plain augmenting-path matching
               and verifies it cell by cell (two free cells per live line, no
               cell used twice);
  - "threat":  checks Maker's completion cells;
  - "search":  re-solves the position with a simple memoised depth-first solver
               that tries EVERY free cell (so it also tests the C program's
               dead-cell pruning), if that fits in --cap nodes.
Usage: python check_dfpn.py GAMES.jsonl DFPN.jsonl [--cap 20000] [--max-search 40]
Prints progress every 2 s; a normal run takes well under a minute.
"""
import json
import sys
import time
from itertools import product


def build_lines():
    lines = set()
    for x, y, z in product(range(5), repeat=3):
        for d in product((-1, 0, 1), repeat=3):
            if d == (0, 0, 0):
                continue
            cells = [(x + t * d[0], y + t * d[1], z + t * d[2]) for t in range(5)]
            if all(0 <= v <= 4 for c in cells for v in c):
                lines.add(frozenset(a + 5 * b + 25 * c for a, b, c in cells))
    assert len(lines) == 109
    return [(sum(1 << c for c in l), tuple(sorted(l))) for l in sorted(lines, key=sorted)]


LINES = build_lines()
FULL = (1 << 125) - 1


def live(maker, breaker):
    """Live lines as (maker stones on it, free cells)."""
    return [(bin(m & maker).count('1'), [c for c in cs if not (maker >> c) & 1])
            for m, cs in LINES if not m & breaker]


def potential(maker, breaker):
    return sum(1 << k for k, _ in live(maker, breaker))


def find_pairing(maker, breaker):
    """A dict line index -> (cell, cell), or None. Plain augmenting paths (Kuhn)."""
    lv = live(maker, breaker)
    if any(len(free) < 2 for _, free in lv):
        return None
    owner = {}                                   # cell -> slot (line index, copy)

    def augment(slot, seen):
        for c in lv[slot[0]][1]:
            if c in seen:
                continue
            seen.add(c)
            if c not in owner or augment(owner[c], seen):
                owner[c] = slot
                return True
        return False

    for i in range(len(lv)):
        for copy in (0, 1):
            if not augment((i, copy), set()):
                return None
    pairs = {}
    for c, (i, _) in owner.items():
        pairs.setdefault(i, []).append(c)
    # verify the certificate itself, independently of how it was found
    used = [c for cs in pairs.values() for c in cs]
    assert len(pairs) == len(lv) and all(len(cs) == 2 for cs in pairs.values())
    assert len(set(used)) == len(used)
    assert all(set(cs) <= set(lv[i][1]) for i, cs in pairs.items())
    return pairs


class Cap(Exception):
    pass


def maker_wins(maker, breaker, n, memo, budget):
    """Exact value by plain depth-first search over every free cell."""
    key = (maker, breaker)
    if key in memo:
        return memo[key]
    budget[0] -= 1
    if budget[0] < 0:
        raise Cap
    lv = live(maker, breaker)
    wins = {free[0] for k, free in lv if k == 4}
    maker_to_move = n % 2 == 0
    pot = sum(1 << k for k, _ in lv)
    if maker_to_move and wins:
        value = True
    elif not maker_to_move and len(wins) >= 2:
        value = True
    elif pot < (16 if maker_to_move else 32):
        value = False
    elif not wins and 2 * len(lv) <= 125 - n and find_pairing(maker, breaker) is not None:
        value = False
    else:
        weight = {}
        for k, free in lv:
            for c in free:
                weight[c] = weight.get(c, 0) + (1 << k)
        free_cells = [c for c in range(125) if not ((maker | breaker) >> c) & 1]
        free_cells.sort(key=lambda c: -weight.get(c, 0))
        if maker_to_move:
            value = any(maker_wins(maker | 1 << c, breaker, n + 1, memo, budget) for c in free_cells)
        else:
            value = all(maker_wins(maker, breaker | 1 << c, n + 1, memo, budget) for c in free_cells)
    memo[key] = value
    return value


def main():
    args = sys.argv[1:]
    cap = int(args[args.index('--cap') + 1]) if '--cap' in args else 20000
    max_search = int(args[args.index('--max-search') + 1]) if '--max-search' in args else 40
    games = {}
    for line in open(args[0], encoding='utf-8'):
        g = json.loads(line)
        if g['status'] == 'done':
            games[g['id']] = g['moves']
    recs = [json.loads(l) for l in open(args[1], encoding='utf-8')]
    recs = [r for r in recs if r['status'] == 'done' and r['result'] in ('maker', 'breaker')]
    search = sorted((r for r in recs if r['how'] == 'search'), key=lambda r: r['nodes'])[:max_search]
    todo = [r for r in recs if r['how'] != 'search'] + search
    count = {'es': 0, 'pairing': 0, 'threat': 0, 'search': 0, 'search too big': 0}
    t0 = last = time.time()
    for i, r in enumerate(todo):
        moves = games[r['id']][:r['ply']]
        maker = sum(1 << c for c in moves[0::2])
        breaker = sum(1 << c for c in moves[1::2])
        n = r['ply']
        if r['how'] == 'es':
            assert r['result'] == 'breaker' and potential(maker, breaker) < (16 if n % 2 == 0 else 32), r
        elif r['how'] == 'pairing':
            assert r['result'] == 'breaker' and find_pairing(maker, breaker) is not None, r
        elif r['how'] == 'threat':
            wins = {free[0] for k, free in live(maker, breaker) if k == 4}
            assert r['result'] == 'maker' and len(wins) >= (1 if n % 2 == 0 else 2), r
        else:
            try:
                value = maker_wins(maker, breaker, n, {}, [cap])
                assert value == (r['result'] == 'maker'), r
            except Cap:
                count['search too big'] += 1
                continue
        count[r['how']] += 1
        if time.time() - last >= 2:
            last = time.time()
            done = i + 1
            print(f'  [{last - t0:5.1f}s] {done}/{len(todo)} records, '
                  f'ETA ~{(last - t0) / done * (len(todo) - done):.0f}s', flush=True)
    print(f'{args[1]}: {len(recs)} solved records; confirmed independently: '
          f"{count['es']} Erdos-Selfridge, {count['pairing']} pairing (certificate verified), "
          f"{count['threat']} threat, {count['search']} of the {len(search)} smallest searches "
          f"({count['search too big']} exceeded {cap} Python nodes); no disagreement")


if __name__ == '__main__':
    main()
