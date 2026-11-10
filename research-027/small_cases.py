"""Research 027: small exact checks behind the fragment-code questions.

Runs in well under a minute and prints progress. Nothing here is a Rocq
theorem and nothing here decides the value of the 5x5x5 game.

  A. Over GF(5), every polynomial of total degree <= 3 sums to zero along each
     of the 109 lines, giving 20 independent annihilators.
  B. For small linear hypergraphs (finite planes, the complete quadrilateral,
     the 3x3x3 and 4x4x4 cubes): density, incidence rank over GF(2), GF(3) and
     GF(5), whether the column matroid has two disjoint bases (the capacity
     condition of the two-reserve code defence), and, for small ones, the
     exact Maker-Breaker value with Maker moving first.
"""
from __future__ import annotations

import itertools
from functools import lru_cache
from itertools import combinations

from compute import LINES, rank_mod, incidence


# ---------------------------------------------------------------- A
def polynomial_annihilators() -> None:
    cells = list(range(125))
    coords = [(c % 5, c // 5 % 5, c // 25) for c in cells]
    monomials = [(a, b, c) for a in range(4) for b in range(4) for c in range(4)
                 if a + b + c <= 3]
    assert len(monomials) == 20
    vectors = [[pow(x, a, 5) * pow(y, b, 5) * pow(z, c, 5) % 5 for (x, y, z) in coords]
               for (a, b, c) in monomials]
    for v in vectors:
        for line in LINES:
            assert sum(v[c] for c in line) % 5 == 0
    assert rank_mod(vectors, 5) == 20
    # A degree-4 monomial is not an annihilator: x^4 sums to 4 on an x-line.
    x_line = next(l for l in LINES if len({c // 5 for c in l}) == 1)
    assert sum(pow(c % 5, 4, 5) for c in x_line) % 5 == 4
    r5 = rank_mod(incidence(LINES, cells), 5)
    print(f'[A] GF(5): the 20 monomials of degree <= 3 annihilate all 109 lines; '
          f'kernel dimension {125 - r5} (rank {r5})', flush=True)


# ---------------------------------------------------------------- B
def plane_ag(q: int) -> tuple[int, list[tuple[int, ...]]]:
    pts = {(x, y): i for i, (x, y) in enumerate(itertools.product(range(q), repeat=2))}
    lines = set()
    for a, b in [(1, m) for m in range(q)] + [(0, 1)]:
        for c in range(q):
            lines.add(tuple(sorted(pts[(x, y)] for (x, y) in pts if (a * y - b * x) % q == c)
                      if a else sorted(pts[(x, y)] for (x, y) in pts if x == c)))
    return len(pts), sorted(lines)


def plane_pg(q: int) -> tuple[int, list[tuple[int, ...]]]:
    def normal(v):
        for t in v:
            if t:
                inv = pow(t, q - 2, q)
                return tuple(u * inv % q for u in v)
    pts = sorted({normal(v) for v in itertools.product(range(q), repeat=3) if any(v)})
    index = {p: i for i, p in enumerate(pts)}
    lines = sorted({tuple(sorted(index[p] for p in pts
                                 if sum(a * b for a, b in zip(p, h)) % q == 0)) for h in pts})
    return len(pts), lines


def grid_cube(k: int) -> tuple[int, list[tuple[int, ...]]]:
    lines = set()
    dirs = [d for d in itertools.product((-1, 0, 1), repeat=3) if d != (0, 0, 0)]
    for s in itertools.product(range(k), repeat=3):
        for d in dirs:
            cs = [tuple(s[i] + t * d[i] for i in range(3)) for t in range(k)]
            if all(0 <= v < k for c in cs for v in c):
                lines.add(tuple(sorted(c[0] + k * c[1] + k * k * c[2] for c in cs)))
    return k ** 3, sorted(lines)


FANO = (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)])
QUAD = (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)])


def two_disjoint_bases(n: int, lines, p: int) -> bool | None:
    """Does the column matroid of the incidence matrix have two disjoint bases?"""
    rows = incidence(lines, list(range(n)))
    r = rank_mod(rows, p)
    if 2 * r > n:
        return False
    if n > 14:
        return None                     # too large for this brute force
    cols = list(range(n))
    def rank_of(subset):
        return rank_mod([[row[c] for c in subset] for row in rows], p)
    for basis in combinations(cols, r):
        if rank_of(basis) == r:
            rest = [c for c in cols if c not in basis]
            if rank_of(rest) == r:
                return True
    return False


def maker_wins(n: int, lines) -> bool | None:
    if n > 13:
        return None
    full = (1 << n) - 1
    masks = [sum(1 << v for v in l) for l in lines]

    @lru_cache(maxsize=None)
    def maker_to_move(maker: int, breaker: int) -> bool:
        free = full & ~(maker | breaker)
        alive = [m for m in masks if not m & breaker]
        if not alive or not free:
            return False
        for x in range(n):
            if not free >> x & 1:
                continue
            mk = maker | 1 << x
            if any(m & mk == m for m in alive):
                return True
            rest = free & ~(1 << x)
            if rest and all(maker_to_move(mk, breaker | 1 << y)
                            for y in range(n) if rest >> y & 1):
                return True
        return False

    return maker_to_move(0, 0)


def designs() -> None:
    cases = [('complete quadrilateral', QUAD), ('Fano plane PG(2,2)', FANO),
             ('AG(2,3)', plane_ag(3)), ('PG(2,3)', plane_pg(3)),
             ('3x3x3 cube', grid_cube(3)), ('4x4x4 cube', grid_cube(4)),
             ('5x5x5 cube', (125, [tuple(l) for l in LINES]))]
    print('[B] name | cells | lines | lines/cell | rank GF2,GF3,GF5 | '
          '2 disjoint bases GF2,GF3,GF5 | Maker wins (Maker first)', flush=True)
    for name, (n, lines) in cases:
        cells = list(range(n))
        assert all(len(set(a) & set(b)) <= 1 for a, b in combinations(lines, 2)), name
        ranks = [rank_mod(incidence(lines, cells), p) for p in (2, 3, 5)]
        bases = [two_disjoint_bases(n, lines, p) for p in (2, 3, 5)]
        mw = maker_wins(n, lines)
        print(f'    {name:24s} | {n:3d} | {len(lines):3d} | {len(lines) / n:.3f} | '
              f'{ranks} | {bases} | {mw}', flush=True)


# ---------------------------------------------------------------- C
def max_collinear_clique() -> None:
    """Largest set of cube cells that are pairwise on a common winning line.

    A region realising a projective plane needs every two of its cells on a
    common fragment, hence pairwise collinear in the cube.
    """
    adj = {c: set() for c in range(125)}
    for line in LINES:
        for a, b in combinations(line, 2):
            adj[a].add(b)
            adj[b].add(a)
    best: list[int] = []

    def bron_kerbosch(r, p, x):
        nonlocal best
        if not p and not x:
            if len(r) > len(best):
                best = r[:]
            return
        if len(r) + len(p) <= len(best):
            return
        u = max(p | x, key=lambda v: len(adj[v] & p))
        for v in list(p - adj[u]):
            bron_kerbosch(r + [v], p & adj[v], x & adj[v])
            p = p - {v}
            x = x | {v}

    bron_kerbosch([], set(range(125)), set())
    assert len(best) == 9 and sorted(best) == [0, 4, 20, 24, 62, 100, 104, 120, 124]
    print('[C] largest pairwise-collinear cell set: 9 cells (8 corners + centre), '
          'so no 13-point projective plane PG(2,3) sits inside the cube', flush=True)


if __name__ == '__main__':
    polynomial_annihilators()
    designs()
    max_collinear_clique()
