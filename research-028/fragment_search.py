"""Research 028: do fragment codes appear earlier than existing leaves?

A *fragment code* certificate at a position with White to move chooses, for
each live line (no Black stone), a fragment of at least two of its free cells.
The GF(2) row space of the fragments must have two disjoint information sets
among the free cells: the column matroid needs two disjoint bases.

Soundness for any such code is already the Rocq theorem
`linear_information_minimax` (QUBIC-PROOF-GATE-001/agent/ZLinearDefense.v). That
theorem takes an arbitrary XOR-closed code, with coverage meaning each live
line contains the support of a nonzero codeword. This script only searches. A
success is evidence, not a theorem, until the certificate is exported and
checked.

Subcommands
  smoke     small hypergraphs: exhaustive fragment search versus exact
            Maker-Breaker values; also cross-checks the matroid-partition code.
  backward  walk known games backwards; at each earlier position test pairing,
            whole-line codes and a heuristic fragment-code search. Results are
            checkpointed after every position; --resume skips finished ones.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
import signal
import sys
import time
from collections import deque
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


# ------------------------------------------------------------------ geometry
def cube_lines() -> list[tuple[int, ...]]:
    lines = set()
    dirs = [d for d in itertools.product((-1, 0, 1), repeat=3) if d != (0, 0, 0)]
    for s in itertools.product(range(5), repeat=3):
        for d in dirs:
            cs = [tuple(s[i] + t * d[i] for i in range(3)) for t in range(5)]
            if all(0 <= v < 5 for c in cs for v in c):
                lines.add(tuple(sorted(c[0] + 5 * c[1] + 25 * c[2] for c in cs)))
    return sorted(lines)


LINES = cube_lines()
assert len(LINES) == 109


# ------------------------------------------------------------------ GF(2) matroids
def gf2_rank(rows: list[int]) -> int:
    basis: dict[int, int] = {}
    for v in rows:
        while v:
            t = v.bit_length() - 1
            if t in basis:
                v ^= basis[t]
            else:
                basis[t] = v
                break
    return len(basis)


class Basis:
    """Echelon form of an independent set of column vectors, with combinations."""

    def __init__(self, elems: list[int], col: dict[int, int]):
        self.elems = elems
        self.rows: dict[int, tuple[int, int]] = {}
        for i, e in enumerate(elems):
            v, combo = col[e], 1 << i
            while v:
                t = v.bit_length() - 1
                if t in self.rows:
                    bv, bc = self.rows[t]
                    v ^= bv
                    combo ^= bc
                else:
                    self.rows[t] = (v, combo)
                    break
            else:
                raise ValueError('dependent set given to Basis')

    def circuit(self, v: int) -> list[int] | None:
        """None if v is independent of the set, else the elements expressing v."""
        combo = 0
        while v:
            t = v.bit_length() - 1
            if t not in self.rows:
                return None
            bv, bc = self.rows[t]
            v ^= bv
            combo ^= bc
        return [self.elems[i] for i in range(len(self.elems)) if combo >> i & 1]


def two_disjoint_bases(col: dict[int, int]) -> tuple[bool, int, list[int], list[int]]:
    """Matroid partition (Edmonds) for two copies of a GF(2) column matroid.

    col maps ground elements (cells) to column vectors. Returns (success, rank,
    I0, I1) where success means |I0| = |I1| = rank.
    """
    r = gf2_rank(list(col.values()))
    sets: list[list[int]] = [[], []]
    where: dict[int, int] = {}
    for s in sorted(col):
        if not col[s]:
            continue
        bases = [Basis(sets[0], col), Basis(sets[1], col)]
        parent: dict[int, tuple[int, int]] = {}
        seen = {s}
        queue = deque([s])
        sink = None
        while queue and sink is None:
            x = queue.popleft()
            for j in (0, 1):
                if where.get(x) == j:
                    continue
                circ = bases[j].circuit(col[x])
                if circ is None:
                    sink = (x, j)
                    break
                for y in circ:
                    if y not in seen:
                        seen.add(y)
                        parent[y] = (x, j)
                        queue.append(y)
        if sink is None:
            continue
        x, j = sink
        moves = [(x, j)]
        while x in parent:
            px, pj = parent[x]
            moves.append((px, pj))
            x = px
        for e, j in moves:
            old = where.get(e)
            if old is not None:
                sets[old].remove(e)
            sets[j].append(e)
            where[e] = j
        if len(sets[0]) == r and len(sets[1]) == r:
            break
    ok = len(sets[0]) == r and len(sets[1]) == r
    return ok, r, sorted(sets[0]), sorted(sets[1])


def columns(fragments: list[int], cells: list[int]) -> dict[int, int]:
    col = {c: 0 for c in cells}
    for i, f in enumerate(fragments):
        for c in cells:
            if f >> c & 1:
                col[c] |= 1 << i
    return col


# ------------------------------------------------------------------ positions
def residual(white: list[int], black: list[int]):
    occ = set(white) | set(black)
    free = [c for c in range(125) if c not in occ]
    live = [l for l in LINES if not set(l) & set(black)]
    res = [[c for c in l if c not in occ] for l in live]
    return free, live, res


def mask(cells) -> int:
    m = 0
    for c in cells:
        m |= 1 << c
    return m


def pairing_feasible(res: list[list[int]], free: list[int]) -> bool:
    """Max flow: each live line needs 2 private free cells."""
    match: dict[int, int] = {}            # cell -> line slot

    def augment(slot, seen):
        for c in res[slot // 2]:
            if c in seen:
                continue
            seen.add(c)
            if c not in match or augment(match[c], seen):
                match[c] = slot
                return True
        return False

    return all(augment(slot, set()) for slot in range(2 * len(res)))


def whole_line_code(res, free) -> dict:
    col = columns([mask(r) for r in res], free)
    ok, r, _, _ = two_disjoint_bases(col)
    return {'ok': ok, 'rank': r}


def fragment_search(res, free, seconds: float, seed: int, progress) -> dict:
    """Annealing on fragment choices; objective = GF(2) rank, then partition."""
    rng = random.Random(seed)
    frags = [mask(r) for r in res]
    if any(len(r) < 2 for r in res):
        return {'ok': False, 'reason': 'a live line has fewer than 2 free cells'}
    F = len(free)
    rank = gf2_rank(frags)
    best_rank, best = rank, frags[:]
    if 2 * rank <= F:                       # the whole lines themselves
        ok, r, i0, i1 = two_disjoint_bases(columns(frags, free))
        if ok:
            return {'ok': True, 'rank': r, 'iterations': 0,
                    'fragments': [[c for c in range(125) if f >> c & 1] for f in frags],
                    'information_sets': [i0, i1]}
    tested, checks = set(), 0
    start = time.time()
    last = start
    it = 0
    temperature = 0.6
    while time.time() - start < seconds:
        it += 1
        i = rng.randrange(len(frags))
        cells_i = [c for c in res[i] if frags[i] >> c & 1]
        out_i = [c for c in res[i] if not frags[i] >> c & 1]
        if len(cells_i) > 2 and (not out_i or rng.random() < 0.6):
            new = frags[i] & ~(1 << rng.choice(cells_i))
        elif out_i:
            new = frags[i] | 1 << rng.choice(out_i)
        else:
            continue
        old = frags[i]
        frags[i] = new
        nr = gf2_rank(frags)
        if nr <= rank or rng.random() < temperature ** (nr - rank):
            rank = nr
            if rank < best_rank:
                best_rank, best = rank, frags[:]
            if 2 * rank <= F:
                key = tuple(frags)
                if key not in tested:
                    tested.add(key)
                    checks += 1
                    ok, r, i0, i1 = two_disjoint_bases(columns(frags, free))
                    if ok:
                        return {'ok': True, 'rank': r, 'iterations': it,
                                'fragments': [[c for c in range(125) if f >> c & 1]
                                              for f in frags],
                                'information_sets': [i0, i1]}
        else:
            frags[i] = old
        temperature = max(0.05, temperature * 0.9995)
        now = time.time()
        if now - last > 4:
            progress(f'        search: {it} steps, {it / (now - start):.0f}/s, '
                     f'rank {rank}, best {best_rank}, need <= {F // 2}, '
                     f'partition checks {checks}')
            last = now
    return {'ok': False, 'best_rank': best_rank, 'iterations': it,
            'rank_needed': F // 2, 'partition_checks': checks}


# ------------------------------------------------------------------ games
def r013_game():
    d = json.loads((ROOT / 'research-013' / 'QUBIC-RESEARCH-013_safe10_certificate.json')
                   .read_text(encoding='utf-8'))
    cell = lambda p: (p[0] + 2) + 5 * (p[1] + 2) + 25 * (p[2] + 2)
    return [cell(p) for p in d['white']], [cell(p) for p in d['black']]


def games():
    out = {}
    for name, path in [('r021-witness', 'linear_leaf.json'),
                       ('r021-stronger', 'stronger_linear_leaf.json')]:
        d = json.loads((ROOT / 'research-021' / path).read_text(encoding='utf-8'))
        out[name] = (d['white'], d['black'])
    out['r013-pairing'] = r013_game()
    return out


# ------------------------------------------------------------------ smoke test
def maker_wins(n: int, edges) -> bool:
    full = (1 << n) - 1
    masks = [mask(e) for e in edges]

    @lru_cache(maxsize=None)
    def go(mk: int, br: int) -> bool:
        free = full & ~(mk | br)
        if not free or not any(not m & br for m in masks):
            return False
        for x in range(n):
            if free >> x & 1:
                m2 = mk | 1 << x
                if any(m & m2 == m for m in masks):
                    return True
                rest = free & ~(1 << x)
                if rest and all(go(m2, br | 1 << y) for y in range(n) if rest >> y & 1):
                    return True
        return False

    return go(0, 0)


def brute_two_bases(col: dict[int, int]) -> bool:
    cells = sorted(col)
    r = gf2_rank(list(col.values()))
    for b in itertools.combinations(cells, r):
        if gf2_rank([col[c] for c in b]) == r:
            rest = [c for c in cells if c not in b]
            if gf2_rank([col[c] for c in rest]) == r:
                return True
    return r == 0


def smoke(args) -> None:
    rng = random.Random(args.seed)
    stats = {'hypergraphs': 0, 'fragment_ok': 0, 'fragment_ok_pairing_fails': 0,
             'fragment_ok_es_fails': 0, 'partition_crosschecks': 0}
    start = time.time()
    while stats['hypergraphs'] < args.trials:
        n = rng.randint(4, 9)
        edges: list[tuple[int, ...]] = []
        for _ in range(rng.randint(2, 7)):
            e = tuple(sorted(rng.sample(range(n), rng.randint(2, min(4, n)))))
            if all(len(set(e) & set(f)) <= 1 for f in edges):
                edges.append(e)
        choices = [[m for k in range(2, len(e) + 1) for m in itertools.combinations(e, k)]
                   for e in edges]
        total = 1
        for c in choices:
            total *= len(c)
        if total > 3000:
            continue
        stats['hypergraphs'] += 1
        found = False
        for pick in itertools.product(*choices):
            col = columns([mask(f) for f in pick], list(range(n)))
            ok = two_disjoint_bases(col)[0]
            if stats['partition_crosschecks'] < 3000:
                assert ok == brute_two_bases(col), (n, edges, pick)
                stats['partition_crosschecks'] += 1
            if ok:
                found = True
                break
        mw = maker_wins(n, edges)
        if found:
            stats['fragment_ok'] += 1
            assert not mw, f'SOUNDNESS VIOLATION: {n} {edges}'
            if not pairing_feasible([list(e) for e in edges], list(range(n))):
                stats['fragment_ok_pairing_fails'] += 1
            if sum(2.0 ** -len(e) for e in edges) >= 0.5:
                stats['fragment_ok_es_fails'] += 1
        if stats['hypergraphs'] % 100 == 0:
            print(f'  smoke: {stats["hypergraphs"]}/{args.trials} hypergraphs, '
                  f'{time.time() - start:.0f}s, {stats}', flush=True)
    print('SMOKE OK (no Maker win admits a fragment code):', stats, flush=True)


# ------------------------------------------------------------------ backward walk
def backward(args) -> None:
    out = Path(args.out)
    state = json.loads(out.read_text(encoding='utf-8')) if args.resume and out.exists() else {}
    stop = {'flag': False}

    def handler(signum, frame):
        stop['flag'] = True
        print('  interrupt received; finishing current position and saving', flush=True)
    signal.signal(signal.SIGINT, handler)

    def save():
        tmp = out.with_suffix('.tmp')
        tmp.write_text(json.dumps(state, indent=1), encoding='utf-8')
        tmp.replace(out)

    todo = []
    for name, (white, black) in games().items():
        if args.games and name not in args.games:
            continue
        rounds = len(black)
        for k in range(rounds, args.min_round - 1, -1):
            todo.append((name, k, white[:k], black[:k]))
    print(f'backward walk: {len(todo)} positions, about {args.seconds:.0f}s search each '
          f'(upper bound {len(todo) * (args.seconds + 3) / 60:.1f} min)', flush=True)
    t0 = time.time()
    for idx, (name, k, white, black) in enumerate(todo):
        key = f'{name}@{k}'
        if key in state:
            continue
        if stop['flag']:
            break
        free, live, res = residual(white, black)
        info = {'game': name, 'rounds': k, 'free': len(free), 'live': len(live),
                'pairing': pairing_feasible(res, free),
                'whole_line_code': whole_line_code(res, free)}
        print(f'[{idx + 1}/{len(todo)}] {key}: free {len(free)}, live {len(live)}, '
              f'pairing {info["pairing"]}, whole-line code {info["whole_line_code"]}, '
              f'elapsed {time.time() - t0:.0f}s', flush=True)
        info['fragment_code'] = fragment_search(
            res, free, args.seconds, args.seed + k,
            lambda s: print(s, flush=True))
        fc = info['fragment_code']
        print(f'        fragment code: ok={fc["ok"]} '
              f'{"rank " + str(fc.get("rank")) if fc["ok"] else "best rank " + str(fc.get("best_rank")) + " need <= " + str(fc.get("rank_needed"))}',
              flush=True)
        state[key] = info
        save()
    print(f'done in {time.time() - t0:.0f}s; results in {out}', flush=True)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    s = sub.add_parser('smoke')
    s.add_argument('--trials', type=int, default=600)
    s.add_argument('--seed', type=int, default=28)
    b = sub.add_parser('backward')
    b.add_argument('--games', nargs='*')
    b.add_argument('--min-round', type=int, default=5)
    b.add_argument('--seconds', type=float, default=8)
    b.add_argument('--seed', type=int, default=28)
    b.add_argument('--out', default=str(HERE / 'backward_results.json'))
    b.add_argument('--resume', action='store_true')
    args = ap.parse_args()
    {'smoke': smoke, 'backward': backward}[args.cmd](args)


if __name__ == '__main__':
    main()
