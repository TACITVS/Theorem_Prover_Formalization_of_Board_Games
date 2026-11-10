"""Research 026: independent checks for the regional Erdos-Selfridge barrier.

Runs in well under a minute. Nothing here determines the value of the game.

Checks
  1. Geometry: 109 lines, two distinct lines share at most one cell.
  2. Qubic decomposition: 76 lines are a 4x4x4 Qubic line plus one middle
     cell, 33 lines lie inside the three middle planes.
  3. Arithmetic core of the barrier lemma, by exhaustive enumeration.
  4. Soundness smoke test: on random small regions that satisfy the
     regional condition, brute-force minimax confirms Breaker wins as
     second player. (A test of the write-up, not a proof.)
  5. Optionally compiles RegionalBarrier.v and RegionalCertificates.v
     against the hash-pinned rules and audits their assumptions.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import random
import subprocess
import tempfile
import shutil
from functools import lru_cache
from pathlib import Path


def cube_lines() -> list[frozenset[tuple[int, int, int]]]:
    lines = set()
    dirs = [d for d in itertools.product((-1, 0, 1), repeat=3) if d != (0, 0, 0)]
    for start in itertools.product(range(5), repeat=3):
        for d in dirs:
            cells = [tuple(start[i] + t * d[i] for i in range(3)) for t in range(5)]
            if all(0 <= v < 5 for c in cells for v in c):
                lines.add(frozenset(cells))
    return sorted(lines, key=sorted)


def check_geometry() -> list[frozenset]:
    lines = cube_lines()
    assert len(lines) == 109, len(lines)
    assert all(len(a & b) <= 1 for a, b in itertools.combinations(lines, 2))
    degree = {c: sum(c in l for l in lines) for c in itertools.product(range(5), repeat=3)}
    assert sum(degree.values()) == 545 and max(degree.values()) == 13
    print('[1] geometry: 109 lines, pairwise intersections <= 1 cell: OK')
    return lines


def check_qubic_decomposition(lines: list[frozenset]) -> None:
    generic = {c for c in itertools.product(range(5), repeat=3) if 2 not in c}
    assert len(generic) == 64
    qubic, middle = [], []
    for line in lines:
        g = line & generic
        if g:
            assert len(g) == 4 and len(line - generic) == 1
            qubic.append(line)
        else:
            assert any(all(c[i] == 2 for c in line) for i in range(3))
            middle.append(line)
    assert (len(qubic), len(middle)) == (76, 33)
    # The 76 traces are exactly the lines of 4x4x4 Qubic after relabelling
    # levels 0,1,3,4 -> 0,1,2,3.
    relabel = {0: 0, 1: 1, 3: 2, 4: 3}
    traces = {frozenset(tuple(relabel[v] for v in c) for c in l & generic) for l in qubic}
    q4 = set()
    dirs = [d for d in itertools.product((-1, 0, 1), repeat=3) if d != (0, 0, 0)]
    for start in itertools.product(range(4), repeat=3):
        for d in dirs:
            cells = [tuple(start[i] + t * d[i] for i in range(3)) for t in range(4)]
            if all(0 <= v < 4 for c in cells for v in c):
                q4.add(frozenset(cells))
    assert len(q4) == 76 and traces == q4
    # How the 76 lines share their single middle cell.
    load: dict[tuple, int] = {}
    for l in qubic:
        (m,) = l - generic
        load[m] = load.get(m, 0) + 1
    histogram = sorted((sum(1 for c in m if c == 2), k) for m, k in load.items())
    assert histogram == [(1, 1)] * 48 + [(2, 2)] * 12 + [(3, 4)]
    print('[2] Qubic decomposition: 76 = 4x4x4 Qubic lines + one middle cell '
          '(48 private, 12 shared by two, centre shared by four); 33 middle-plane lines: OK')


def check_arithmetic_core() -> None:
    """a_s = number of fragments of size s (2..5) assigned to a region of n cells.

    Budget:  8 a2 + 4 a3 + 2 a4 + a5 <= 15    (sum 2^-s < 1/2)
    Pairs :  a2 + 3 a3 + 6 a4 + 10 a5 <= n(n-1)/2   (fragments share <= 1 cell)
    Claim :  6 (a2+a3+a4+a5) <= 5 n.
    """
    worst = 0.0
    count = 0
    for a2 in range(2):
        for a3 in range(4):
            for a4 in range(8):
                for a5 in range(16):
                    if 8 * a2 + 4 * a3 + 2 * a4 + a5 > 15:
                        continue
                    m = a2 + a3 + a4 + a5
                    pairs = a2 + 3 * a3 + 6 * a4 + 10 * a5
                    n = 0
                    while n * (n - 1) // 2 < pairs:
                        n += 1
                    largest = 5 if a5 else 4 if a4 else 3 if a3 else 2 if a2 else 0
                    n = max(n, largest)
                    count += 1
                    assert 6 * m <= 5 * n, (a2, a3, a4, a5, n)
                    if n:
                        worst = max(worst, m / n)
    assert abs(worst - 5 / 6) < 1e-12
    assert 6 * 109 > 5 * 125
    print(f'[3] arithmetic core: {count} size profiles, max lines/cells = 5/6, '
          f'and 109 > 5*125/6 = {5 * 125 / 6:.2f}: OK')


def breaker_wins_second(n: int, edges: tuple[frozenset[int], ...]) -> bool:
    full = (1 << n) - 1
    masks = [sum(1 << v for v in e) for e in edges]

    @lru_cache(maxsize=None)
    def maker_to_move(maker: int, breaker: int) -> bool:
        """True iff Breaker wins."""
        free = full & ~(maker | breaker)
        if not free:
            return True
        for x in range(n):
            if not free >> x & 1:
                continue
            mk = maker | 1 << x
            if any(m & mk == m for m in masks):
                return False
            rest = free & ~(1 << x)
            if not rest:
                continue
            if not any(maker_to_move(mk, breaker | 1 << y)
                       for y in range(n) if rest >> y & 1):
                return False
        return True

    return maker_to_move(0, 0)


def check_soundness_smoke(trials: int = 400, seed: int = 26) -> None:
    rng = random.Random(seed)
    tested = 0
    while tested < trials:
        n = rng.randint(2, 11)
        edges: list[frozenset[int]] = []
        for _ in range(rng.randint(1, 8)):
            e = frozenset(rng.sample(range(n), rng.randint(2, min(5, n))))
            if all(len(e & f) <= 1 for f in edges):
                edges.append(e)
        if sum(2.0 ** -len(e) for e in edges) >= 0.5:
            continue
        assert 6 * len(edges) <= 5 * n
        assert breaker_wins_second(n, tuple(edges)), (n, edges)
        tested += 1
    # ES is sufficient, not necessary: the complete quadrilateral has
    # sum exactly 1/2 and Breaker still wins as second player.
    quad = tuple(frozenset(e) for e in [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)])
    assert breaker_wins_second(6, quad)
    # Sharpness of the strict inequality: two pairs sharing a cell.
    assert not breaker_wins_second(3, (frozenset((0, 1)), frozenset((0, 2))))
    print(f'[4] soundness smoke test: {tested} random admissible regions, '
          'Breaker wins every one by brute force: OK')


def check_rocq(rocq: str, timeout: float) -> None:
    here = Path(__file__).resolve().parent
    gate = here.parent / 'QUBIC-PROOF-GATE-001'
    hashes = json.loads((gate / 'trusted_hashes.json').read_text(encoding='utf-8'))
    for name, digest in hashes.items():
        if hashlib.sha256((gate / name).read_bytes()).hexdigest() != digest.lower():
            raise RuntimeError(f'Pinned source changed: {name}')
    with tempfile.TemporaryDirectory(prefix='qubic-research-026-') as tmp:
        target = Path(tmp)
        for d in ['trusted', 'agent', 'research']:
            (target / d).mkdir()
        for name in ['Rules', 'Goal']:
            shutil.copy2(gate / 'trusted' / f'{name}.v', target / 'trusted')
        agent = ['Minimax', 'RulesFacts', 'SafePairing', 'Geometry']
        for name in agent:
            shutil.copy2(gate / 'agent' / f'{name}.v', target / 'agent')
        ours = ['RegionalBarrier', 'RegionalCertificates']
        for name in ours:
            shutil.copy2(here / f'{name}.v', target / 'research')
        flags = ['-Q', 'trusted', 'QubicTrusted', '-Q', 'agent', 'QubicAgent',
                 '-Q', 'research', 'QubicResearch026']

        def run(args: list[str]) -> str:
            out = subprocess.run(args, cwd=target, capture_output=True, text=True,
                                 encoding='utf-8', errors='replace', timeout=timeout)
            text = out.stdout + out.stderr
            if out.returncode:
                raise RuntimeError(f'{" ".join(args)} failed:\n{text}')
            return text

        files = ([f'trusted/{n}.v' for n in ['Rules', 'Goal']] +
                 [f'agent/{n}.v' for n in agent] + [f'research/{n}.v' for n in ours])
        audits = {}
        for path in files:
            audits[path] = run([rocq, 'compile', *flags, path])
        for path, expected in [('research/RegionalBarrier.v', 3),
                               ('research/RegionalCertificates.v', 5)]:
            text = audits[path]
            if text.count('Closed under the global context') != expected or 'Axioms:' in text:
                raise RuntimeError(f'assumption audit failed for {path}:\n{text}')
        run([rocq, 'check', '-silent', *flags, 'QubicResearch026.RegionalBarrier',
             'QubicResearch026.RegionalCertificates'])
    print('[5] Rocq: RegionalBarrier.v (3 theorems) and RegionalCertificates.v '
          '(5 theorems) closed under the global context; rocq check passes: OK')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rocq', default=None, help='path to rocq; omit to skip step 5')
    parser.add_argument('--timeout', type=float, default=180)
    args = parser.parse_args()
    lines = check_geometry()
    check_qubic_decomposition(lines)
    check_arithmetic_core()
    check_soundness_smoke()
    if args.rocq:
        check_rocq(args.rocq, args.timeout)
    else:
        print('[5] Rocq step skipped (pass --rocq)')
    print('ALL CHECKS PASSED. The value of the 5x5x5 game remains unresolved.')


if __name__ == '__main__':
    main()
