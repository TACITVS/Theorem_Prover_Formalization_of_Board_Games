"""Research 029: capacity test for hybrid regional certificates.

Cells are split into one *code region* C and up to M *potential regions*
P_1..P_M. Black always answers in the region of White's last move. Every live
line (no Black stone) is assigned to one region, and its fragment is its free
cells inside that region.

- **Potential region** (research 026): the fragments assigned there must satisfy
  sum 2^(5 - s) <= 15, where s is the fragment's free size (Erdos-Selfridge for
  the second player). A 2-cell region holding one line is exactly a pairing.
- **Code region** (research 021): fragments need at least 2 free cells, and the
  GF(2) code they span needs two disjoint information sets among C's free cells.
  A necessary condition is the *shortfall* 2 * rank - |C| <= 0.

Annealing moves cells between regions. Lines are assigned greedily: a line
with fewer than 2 cells in C must go to a potential region, the cheapest one,
and other lines move to potential regions while budget remains. The objective
is the code shortfall plus large penalties for violations. Capacity only: a
zero shortfall is necessary, not sufficient, so it is followed by the exact
matroid-partition test. Nothing here is a proof.
"""
from __future__ import annotations

import argparse
import json
import math
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'research-028'))
from fragment_search import LINES, columns, gf2_rank, two_disjoint_bases  # noqa: E402

HERE = Path(__file__).resolve().parent
UNITS = {5: 1, 4: 2, 3: 4, 2: 8, 1: 16}


EXACT = False      # optimise 2*rank - max|I0 u I1| instead of 2*rank - cells


def evaluate(region, live_free, free, m, detail=False):
    """region[c] = -1 for the code region, j >= 0 for potential region j."""
    budget = [0] * m
    crow, penalty, assigned = [], 0, []
    optional = []
    for li, fl in enumerate(live_free):
        cfrag = [c for c in fl if region[c] < 0]
        per = {}
        for c in fl:
            if region[c] >= 0:
                per.setdefault(region[c], []).append(c)
        if len(cfrag) < 2:
            if not per:
                penalty += 100
                continue
            j, cells = max(per.items(), key=lambda kv: len(kv[1]))
            budget[j] += UNITS[len(cells)]
            assigned.append((li, j))
        else:
            best = max(per.items(), key=lambda kv: len(kv[1]), default=None)
            if best and len(best[1]) >= 3:
                optional.append((UNITS[len(best[1])], li, best[0], cfrag))
            else:
                crow.append(cfrag)
    optional.sort()
    for u, li, j, cfrag in optional:
        if budget[j] + u <= 15:
            budget[j] += u
            assigned.append((li, j))
        else:
            crow.append(cfrag)
    over = sum(max(0, b - 15) for b in budget)
    penalty += 50 * over
    masks = [sum(1 << c for c in r) for r in crow]
    ccells = [c for c in free if region[c] < 0]
    rank = gf2_rank(masks)
    short = 2 * rank - len(ccells)
    if EXACT and penalty == 0:
        ok, rank, i0, i1 = two_disjoint_bases(columns(masks, ccells))
        short = 2 * rank - len(i0) - len(i1)
    score = max(0, short) + penalty
    if detail:
        return score, {'shortfall': short, 'rank': rank, 'code_cells': len(ccells),
                       'code_lines': len(crow), 'potential_lines': len(assigned),
                       'penalty': penalty, 'masks': masks, 'ccells': ccells}
    return score, short


def anneal(white, black, seconds, m, seed, log, ckpt=None):
    rng = random.Random(seed)
    occ = set(white) | set(black)
    free = [c for c in range(125) if c not in occ]
    live_free = [[c for c in l if c not in occ] for l in LINES if not set(l) & set(black)]
    region = {c: -1 for c in free}
    base = evaluate(region, live_free, free, m)[1]
    if ckpt and Path(ckpt).exists():
        saved = json.loads(Path(ckpt).read_text())
        region = {int(k): v for k, v in saved['region'].items()}
        log(f'      resumed from {ckpt} (score {saved["score"]})')
    cur, short = evaluate(region, live_free, free, m)
    best, best_region = cur, dict(region)
    t0 = last = last_ckpt = time.time()
    T, it = 3.0, 0
    nbrs = {c: set() for c in free}
    for fl in live_free:
        for a in fl:
            nbrs[a].update(fl)
    while time.time() - t0 < seconds:
        it += 1
        c = rng.choice(free)
        old = region[c]
        r = rng.random()
        if r < 0.3:
            new = -1
        elif r < 0.75:                  # join a neighbour's potential region
            ps = [region[x] for x in nbrs[c] if region[x] >= 0]
            new = rng.choice(ps) if ps else rng.randrange(m)
        else:
            new = rng.randrange(m)
        if new == old:
            continue
        region[c] = new
        sc, _ = evaluate(region, live_free, free, m)
        if sc <= cur or rng.random() < math.exp((cur - sc) / T):
            cur = sc
            if sc < best:
                best, best_region = sc, dict(region)
        else:
            region[c] = old
        T = max(0.2, T * 0.9997)
        if ckpt and time.time() - last_ckpt > 30:
            last_ckpt = time.time()
            tmp = Path(ckpt).with_suffix('.tmp')
            tmp.write_text(json.dumps({'score': best, 'region': best_region}))
            tmp.replace(ckpt)
        if time.time() - last > 5:
            last = time.time()
            log(f'      {it} moves, {it / (last - t0):.0f}/s, current {cur}, best {best} '
                f'(whole-line shortfall {base}), T {T:.2f}')
    if ckpt:
        Path(ckpt).write_text(json.dumps({'score': best, 'region': best_region}))
    score, d = evaluate(best_region, live_free, free, m, detail=True)
    d['exact_code_ok'] = None
    if score == 0:
        d['exact_code_ok'] = bool(two_disjoint_bases(columns(d['masks'], d['ccells']))[0])
    d.pop('masks'), d.pop('ccells')
    d['whole_line_shortfall'] = base
    d['regions_used'] = len({v for v in best_region.values() if v >= 0})
    d['iterations'] = it
    return d


def _empty_job(args):
    seed, seconds, m, ckdir, exact, start = args
    global EXACT
    EXACT = exact
    ck = Path(ckdir) / f'seed{seed}.json'
    if start and not ck.exists():
        ck.write_text(Path(start).read_text())
    logs = []
    d = anneal([], [], seconds, m, seed, logs.append, ckpt=str(ck))
    return seed, d


def empty_search(seeds, seconds, m, exact=False, start=None) -> None:
    """Many independent empty-board searches in parallel, checkpointed per seed."""
    import multiprocessing as mp
    ckdir = HERE / ('hybrid_exact_ckpt' if exact else 'hybrid_ckpt')
    ckdir.mkdir(exist_ok=True)
    print(f'empty-board hybrid search: {len(seeds)} seeds x {seconds:.0f}s in parallel '
          f'(about {seconds / 60:.1f} min wall); checkpoints in {ckdir.name}/', flush=True)
    t0 = time.time()
    results = {}
    with mp.Pool(min(len(seeds), 22)) as pool:
        jobs = [(s, seconds, m, str(ckdir), exact, start) for s in seeds]
        for seed, d in pool.imap_unordered(_empty_job, jobs):
            results[seed] = d
            print(f'  seed {seed}: shortfall {d["shortfall"]} (rank {d["rank"]}, code cells '
                  f'{d["code_cells"]}, code lines {d["code_lines"]}, potential lines '
                  f'{d["potential_lines"]} in {d["regions_used"]} regions), exact '
                  f'{d["exact_code_ok"]}  [{time.time() - t0:.0f}s]', flush=True)
    best = min(results.items(), key=lambda kv: kv[1]['shortfall'])
    print(f'BEST seed {best[0]}: shortfall {best[1]["shortfall"]}', flush=True)
    (HERE / ('hybrid_empty_exact.json' if exact else 'hybrid_empty.json')).write_text(
        json.dumps(results, indent=1))


def main() -> None:
    if len(sys.argv) > 1 and sys.argv[1] == 'empty':
        ap = argparse.ArgumentParser()
        ap.add_argument('cmd')
        ap.add_argument('--seeds', type=int, nargs='+', default=list(range(1, 21)))
        ap.add_argument('--seconds', type=float, default=300)
        ap.add_argument('--regions', type=int, default=40)
        ap.add_argument('--exact', action='store_true')
        ap.add_argument('--start', help='layout checkpoint to start every seed from')
        a = ap.parse_args()
        return empty_search(a.seeds, a.seconds, a.regions, a.exact, a.start)
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--games', default=str(HERE / 'games_cert.jsonl'))
    ap.add_argument('--ids', type=int, nargs='+', default=[0, 1, 2, 3])
    ap.add_argument('--rounds', type=int, nargs='+', default=[4, 6, 8])
    ap.add_argument('--seconds', type=float, default=25)
    ap.add_argument('--regions', type=int, default=30)
    ap.add_argument('--out', default=str(HERE / 'hybrid_results.json'))
    ap.add_argument('--resume', action='store_true')
    args = ap.parse_args()
    games = {g['id']: g['moves'] for g in map(json.loads, Path(args.games).read_text().splitlines())}
    todo = [('empty', [], [])]
    for gid in args.ids:
        mv = games[gid]
        for k in args.rounds:
            todo.append((f'game{gid}@{k}', mv[0:2 * k:2], mv[1:2 * k:2]))
    out = Path(args.out)
    state = json.loads(out.read_text()) if args.resume and out.exists() else {}
    print(f'hybrid capacity search: {len(todo)} positions x {args.seconds:.0f}s '
          f'(about {len(todo) * args.seconds / 60:.1f} min), {args.regions} potential slots',
          flush=True)
    t0 = time.time()
    for i, (key, w, b) in enumerate(todo):
        if key in state:
            continue
        print(f'[{i + 1}/{len(todo)}] {key}', flush=True)
        d = anneal(w, b, args.seconds, args.regions, 29 + i, lambda s: print(s, flush=True))
        state[key] = d
        out.write_text(json.dumps(state, indent=1))
        print(f'    -> shortfall {d["shortfall"]} (whole-line {d["whole_line_shortfall"]}), '
              f'penalty {d["penalty"]}, code lines {d["code_lines"]}, potential lines '
              f'{d["potential_lines"]} in {d["regions_used"]} regions, exact {d["exact_code_ok"]}'
              f'  [{time.time() - t0:.0f}s]', flush=True)


if __name__ == '__main__':
    main()
