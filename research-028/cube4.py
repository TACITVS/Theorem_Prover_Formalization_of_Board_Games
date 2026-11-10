"""Research 028: 4x4x4 testbed for the certificate classes.

4x4x4 Qubic is a first-player win (Patashnik 1980; Allis 1994), so no
second-player certificate can exist at the empty board or along White's best
play. The 4-cube is therefore a *falsification* testbed, not a smaller copy of
the 5x5x5 question:

  * many games are simulated (greedy Black, greedy-with-noise White);
  * at each White-to-move position we test pairing, whole-line GF(2) codes and
    a heuristic fragment-code search, recording the first round each class
    certifies Black;
  * every certified position is attacked with a White threat-space (VCF)
    search. A forced White win from a certified position would expose a bug.

Results are checkpointed after every game; --resume continues.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
import signal
import time
from functools import lru_cache
from pathlib import Path

from fragment_search import fragment_search, pairing_feasible, whole_line_code

HERE = Path(__file__).resolve().parent
N, K = 64, 4


def cube_lines(k: int):
    lines = set()
    dirs = [d for d in itertools.product((-1, 0, 1), repeat=3) if d != (0, 0, 0)]
    for s in itertools.product(range(k), repeat=3):
        for d in dirs:
            cs = [tuple(s[i] + t * d[i] for i in range(3)) for t in range(k)]
            if all(0 <= v < k for c in cs for v in c):
                lines.add(tuple(sorted(c[0] + k * c[1] + k * k * c[2] for c in cs)))
    return sorted(lines)


LINES = cube_lines(K)
assert len(LINES) == 76
MASKS = [sum(1 << c for c in l) for l in LINES]
THROUGH = [[i for i, l in enumerate(LINES) if c in l] for c in range(N)]


def residual(w: int, b: int):
    free = [c for c in range(N) if not (w | b) >> c & 1]
    res = [[c for c in LINES[i] if not (w | b) >> c & 1]
           for i, m in enumerate(MASKS) if not m & b]
    return free, res


def threats(me: int, opp: int) -> set[int]:
    """Cells completing a line of `me` (lines with K-1 own stones, no opponent)."""
    out = set()
    for m in MASKS:
        if not m & opp and bin(m & me).count('1') == K - 1:
            rest = m & ~me
            out.add(rest.bit_length() - 1)
    return out


def wins(me: int) -> bool:
    return any(m & me == m for m in MASKS)


def score(cell: int, me: int, opp: int) -> float:
    s = 0.0
    for i in THROUGH[cell]:
        m = MASKS[i]
        if not m & opp:
            s += 4 ** bin(m & me).count('1')
        if not m & me:
            s += 0.9 * 4 ** bin(m & opp).count('1')
    return s


def greedy(me: int, opp: int, rng: random.Random, noise: float) -> int:
    free = [c for c in range(N) if not (me | opp) >> c & 1]
    win = threats(me, opp) & set(free)
    if win:
        return min(win)
    block = threats(opp, me) & set(free)
    if block:
        return min(block)
    if rng.random() < noise:
        return rng.choice(free)
    return max(free, key=lambda c: (score(c, me, opp), rng.random()))


def white_vcf(w: int, b: int, depth: int) -> bool:
    """White to move: can White force a win using only threat moves?"""

    @lru_cache(maxsize=None)
    def go(w: int, b: int, d: int) -> bool:
        free = ~(w | b) & ((1 << N) - 1)
        if threats(w, b) & {c for c in range(N) if free >> c & 1}:
            return True
        bt = threats(b, w)
        if len(bt) >= 2:
            return False
        if d == 0:
            return False
        cands = bt if bt else {c for i, m in enumerate(MASKS) if not m & b
                               and bin(m & w).count('1') == K - 2
                               for c in LINES[i] if free >> c & 1}
        for x in cands:
            w2 = w | 1 << x
            t = threats(w2, b)
            if len(t) >= 2:
                return True
            if len(t) == 1:
                y = next(iter(t))
                b2 = b | 1 << y
                if wins(b2):
                    continue
                if go(w2, b2, d - 1):
                    return True
        return False

    return go(w, b, depth)


def play_game(seed: int, args, log) -> dict:
    rng = random.Random(seed)
    w = b = 0
    first = {'pairing': None, 'whole_line': None, 'fragment': None}
    falsified = []
    for rnd in range(0, 30):
        # White-to-move position after `rnd` rounds.
        if rnd >= args.min_round and not threats(w, b):
            free, res = residual(w, b)
            checks = {}
            if first['pairing'] is None:
                checks['pairing'] = pairing_feasible(res, free)
            if first['whole_line'] is None:
                checks['whole_line'] = whole_line_code(res, free)['ok']
            if first['fragment'] is None:
                fc = fragment_search(res, free, args.seconds, seed * 100 + rnd, lambda s: None)
                checks['fragment'] = fc['ok']
            for k, ok in checks.items():
                if ok:
                    first[k] = rnd
                    if white_vcf(w, b, args.vcf_depth):
                        falsified.append({'class': k, 'round': rnd, 'white': w, 'black': b})
                        log(f'   !!! FALSIFIED: {k} certificate at round {rnd} but White has VCF')
        if all(v is not None for v in first.values()):
            break
        x = greedy(w, b, rng, args.noise)
        w |= 1 << x
        if wins(w):
            return {'seed': seed, 'result': 'white', 'round': rnd + 1, 'first': first,
                    'falsified': falsified}
        if not ~(w | b) & ((1 << N) - 1):
            break
        y = greedy(b, w, rng, 0.0)
        b |= 1 << y
        if wins(b):
            return {'seed': seed, 'result': 'black', 'round': rnd + 1, 'first': first,
                    'falsified': falsified}
    return {'seed': seed, 'result': 'open', 'first': first, 'falsified': falsified}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--games', type=int, default=30)
    ap.add_argument('--seconds', type=float, default=0.8, help='fragment search per position')
    ap.add_argument('--noise', type=float, default=0.35, help='White random-move rate')
    ap.add_argument('--min-round', type=int, default=2)
    ap.add_argument('--vcf-depth', type=int, default=10)
    ap.add_argument('--out', default=str(HERE / 'cube4_results.json'))
    ap.add_argument('--resume', action='store_true')
    args = ap.parse_args()
    out = Path(args.out)
    state = json.loads(out.read_text(encoding='utf-8')) if args.resume and out.exists() else {}
    stop = {'flag': False}
    signal.signal(signal.SIGINT, lambda *a: stop.update(flag=True))
    print(f'4x4x4: {len(LINES)} lines; {args.games} games, fragment search '
          f'{args.seconds}s per position (estimate under '
          f'{args.games * 8 * (args.seconds + 0.1) / 60:.1f} min)', flush=True)
    t0 = time.time()
    for g in range(args.games):
        if str(g) in state:
            continue
        if stop['flag']:
            print('interrupted; checkpoint saved', flush=True)
            break
        r = play_game(g, args, lambda s: print(s, flush=True))
        state[str(g)] = r
        tmp = out.with_suffix('.tmp')
        tmp.write_text(json.dumps(state, indent=1), encoding='utf-8')
        tmp.replace(out)
        print(f'[game {g + 1}/{args.games}] {r["result"]:5s} first certificate round: '
              f'{r["first"]}, elapsed {time.time() - t0:.0f}s', flush=True)
    games = list(state.values())
    summary = {'games': len(games),
               'results': {k: sum(g['result'] == k for g in games)
                           for k in ('white', 'black', 'open')},
               'falsified': sum(len(g['falsified']) for g in games)}
    for k in ('pairing', 'whole_line', 'fragment'):
        rs = [g['first'][k] for g in games if g['first'][k] is not None]
        summary[k] = {'certified_games': len(rs),
                      'mean_first_round': round(sum(rs) / len(rs), 2) if rs else None}
    both = [(g['first']['fragment'], g['first']['whole_line']) for g in games
            if g['first']['fragment'] is not None and g['first']['whole_line'] is not None]
    summary['fragment_earlier_than_whole_line'] = sum(f < wl for f, wl in both)
    summary['fragment_gain_rounds'] = [wl - f for f, wl in both]
    fp = [(g['first']['fragment'], g['first']['pairing']) for g in games
          if g['first']['fragment'] is not None and g['first']['pairing'] is not None]
    summary['fragment_gain_over_pairing'] = [p - f for f, p in fp]
    print('SUMMARY', json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
