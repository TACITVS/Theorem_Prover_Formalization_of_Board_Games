"""Research 028: push code-leaf strategy trees backwards from known leaves.

`ZZLinearTrees.v` (`checked_linear_tree_minimax`) proves that a strategy tree
checked by `linear_treeb` is sound. Each node gives, for every White move, a
Black reply and a subtree. Each leaf is a pairing tree or a whole-line
linear-code leaf.

This script only *searches* for such trees. A tree it finds is evidence until
it is exported and accepted by `linear_treeb`. The depth-1 probe asks: at a
position P with White to move, does every White move m have a Black reply r such
that P+m+r has a whole-line code leaf?

The checkpoint is per White move, written to the --out JSON; --resume continues.
"""
from __future__ import annotations

import argparse
import json
import signal
import time
from pathlib import Path

from fragment_search import (LINES, columns, games, gf2_rank, mask, residual,
                             two_disjoint_bases)

HERE = Path(__file__).resolve().parent


def leaf_rows(white, black):
    free, live, res = residual(white, black)
    return free, [mask(r) for r in res], res


def code_leaf(white, black):
    free, rows, res = leaf_rows(white, black)
    if any(len(r) < 2 for r in res):
        return None
    r = gf2_rank(rows)
    if 2 * r > len(free):
        return None
    ok, r, i0, i1 = two_disjoint_bases(columns(rows, free))
    return (i0, i1) if ok else None


def white_threats(white, black):
    occ = set(white) | set(black)
    out = set()
    for l in LINES:
        if not set(l) & set(black):
            empty = [c for c in l if c not in occ]
            if len(empty) == 1:
                out.add(empty[0])
    return out


def black_reply(white, black, m, max_partitions):
    """Find r with a code leaf at white+[m], black+[r]. Returns (r, sets, stats)."""
    w2 = white + [m]
    forced = white_threats(w2, black)
    if len(forced) >= 2:
        return None, None, {'reason': 'double threat'}
    occ = set(w2) | set(black)
    cands = sorted(forced) if forced else [c for c in range(125) if c not in occ]
    scored = []
    for r in cands:
        free, rows, res = leaf_rows(w2, black + [r])
        if any(len(x) < 2 for x in res):
            continue
        rk = gf2_rank(rows)
        if 2 * rk <= len(free):
            scored.append((rk, r))
    scored.sort()
    tries = 0
    for rk, r in scored[:max_partitions]:
        tries += 1
        sets = code_leaf(w2, black + [r])
        if sets:
            return r, sets, {'rank_ok': len(scored), 'partition_tries': tries}
    return None, None, {'rank_ok': len(scored), 'partition_tries': tries}


CACHE: dict = {}
KILLER: dict = {}


def covered(white, black, d, max_tries):
    """Tree of depth d with code leaves from this White-to-move position.

    Returns a nested dict {white_move: [black_reply, subtree]} or 'leaf' or None.
    """
    key = (frozenset(white), frozenset(black), d)
    if key in CACHE:
        return CACHE[key]
    if d == 0:
        res = 'leaf' if code_leaf(white, black) else None
        CACHE[key] = res
        return res
    tree = {}
    occ = set(white) | set(black)
    for m in [c for c in range(125) if c not in occ]:
        sub = reply_subtree(white, black, m, d, max_tries)
        if sub is None:
            CACHE[key] = None
            return None
        tree[m] = sub
    CACHE[key] = tree
    return tree


def reply_subtree(white, black, m, d, max_tries):
    w2 = white + [m]
    wins_now = sorted(white_threats(black, w2) - {m})
    if wins_now:                       # Black completes a line: the game ends here
        return [wins_now[0], 'win']
    forced = white_threats(w2, black)
    if len(forced) >= 2:
        return None
    occ = set(w2) | set(black)
    cands = sorted(forced) if forced else [c for c in range(125) if c not in occ]
    scored = []
    for r in cands:
        free, rows, res = leaf_rows(w2, black + [r])
        if d == 1 and any(len(x) < 2 for x in res):
            continue
        scored.append((gf2_rank(rows) - len(free) / 2, r))
    scored.sort()
    order = [r for _, r in scored[:max_tries]]
    k = KILLER.get(d)
    if k in cands:
        order = [k] + [r for r in order if r != k]
    for r in order:
        sub = covered(w2, black + [r], d - 1, max_tries)
        if sub is not None:
            KILLER[d] = r
            return [r, sub]
    return None


def count_leaves(t):
    if t == 'leaf':
        return 1
    if t == 'win':
        return 0
    return sum(count_leaves(s[1]) for s in t.values())


def deep(args) -> None:
    white, black = games()[args.game]
    white, black = white[:args.round], black[:args.round]
    trivial_guard(white, black, args)
    out = Path(args.out or HERE / f'tree{args.depth}_{args.game}_{args.round}.json')
    state = json.loads(out.read_text(encoding='utf-8')) if args.resume and out.exists() else {}
    stop = {'flag': False}
    signal.signal(signal.SIGINT, lambda *a: stop.update(flag=True))
    occ = set(white) | set(black)
    moves = [c for c in range(125) if c not in occ]
    print(f'depth-{args.depth} search at {args.game}@{args.round}: {len(moves)} White moves; '
          f'Black tries up to {args.max_partitions} replies per node', flush=True)
    t0 = time.time()
    for i, m in enumerate(moves):
        if str(m) in state and not (args.retry_failed and state[str(m)] is None):
            continue
        if stop['flag']:
            print('interrupted; checkpoint saved', flush=True)
            break
        t1 = time.time()
        sub = reply_subtree(white, black, m, args.depth, args.max_partitions)
        state[str(m)] = sub
        tmp = out.with_suffix('.tmp')
        tmp.write_text(json.dumps(state), encoding='utf-8')
        tmp.replace(out)
        el = time.time() - t0
        done = sum(v is not None for v in state.values())
        print(f'  [{i + 1}/{len(moves)}] White {m:3d} -> Black '
              f'{sub[0] if sub else None}, leaves {count_leaves(sub[1]) if sub else 0}, '
              f'{time.time() - t1:.1f}s; covered {done}/{len(state)}; cache {len(CACHE)}; '
              f'{el:.0f}s elapsed, ETA {el / (i + 1) * (len(moves) - i - 1):.0f}s', flush=True)
        if sub is None and not args.keep_going:
            print('  uncovered White move; stopping (use --keep-going to list all)', flush=True)
            break
    fails = sorted(int(k) for k, v in state.items() if v is None)
    total = sum(count_leaves(v[1]) for v in state.values() if v)
    print(f'RESULT {args.game}@{args.round} depth {args.depth}: '
          f'{len(state) - len(fails)}/{len(moves)} White moves covered, {total} code leaves; '
          f'uncovered {fails}', flush=True)


def trivial_guard(white, black, args) -> None:
    """Refuse positions where Black already threatens to complete a line."""
    t = white_threats(black, white)
    if t and not args.allow_trivial:
        raise SystemExit(f'Black already threatens to win at {sorted(t)}; a tree here says '
                         f'little (use --allow-trivial to search anyway)')


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--game', default='r021-witness')
    ap.add_argument('--round', type=int, default=9)
    ap.add_argument('--max-partitions', type=int, default=25)
    ap.add_argument('--out', default=None)
    ap.add_argument('--resume', action='store_true')
    ap.add_argument('--depth', type=int, default=1)
    ap.add_argument('--keep-going', action='store_true')
    ap.add_argument('--retry-failed', action='store_true')
    ap.add_argument('--allow-trivial', action='store_true')
    args = ap.parse_args()
    if args.depth > 1:
        return deep(args)
    white, black = games()[args.game]
    white, black = white[:args.round], black[:args.round]
    trivial_guard(white, black, args)
    out = Path(args.out or HERE / f'tree1_{args.game}_{args.round}.json')
    state = json.loads(out.read_text(encoding='utf-8')) if args.resume and out.exists() else {}
    stop = {'flag': False}
    signal.signal(signal.SIGINT, lambda *a: stop.update(flag=True))
    occ = set(white) | set(black)
    moves = [c for c in range(125) if c not in occ]
    print(f'depth-1 probe at {args.game}@{args.round}: {len(moves)} White moves, '
          f'up to {len(moves) - 1} Black replies each (estimate < 2 min)', flush=True)
    t0 = time.time()
    for i, m in enumerate(moves):
        if str(m) in state:
            continue
        if stop['flag']:
            print('interrupted; checkpoint saved', flush=True)
            break
        r, sets, stats = black_reply(white, black, m, args.max_partitions)
        state[str(m)] = {'reply': r, 'information_sets': sets, **stats}
        tmp = out.with_suffix('.tmp')
        tmp.write_text(json.dumps(state), encoding='utf-8')
        tmp.replace(out)
        done = sum(v['reply'] is not None for v in state.values())
        el = time.time() - t0
        print(f'  [{i + 1}/{len(moves)}] White {m:3d} -> Black {r}  {stats}  '
              f'covered {done}/{len(state)}  {el:.0f}s, '
              f'ETA {el / (i + 1) * (len(moves) - i - 1):.0f}s', flush=True)
    fails = [int(k) for k, v in state.items() if v['reply'] is None]
    print(f'RESULT {args.game}@{args.round}: {len(state) - len(fails)}/{len(state)} White moves '
          f'answered by a code leaf; uncovered: {sorted(fails)}', flush=True)


if __name__ == '__main__':
    main()
