"""Find and check the period-8 pairing used in MNKHalesJewett.v.

The plane is tiled by dominoes in the four line directions so that every row,
column, diagonal and anti-diagonal class (mod 8) carries exactly one domino of
its own direction per period of 8 cells.  Then any 9 consecutive cells of a line
contain a whole domino, which proves the Hales-Jewett draw for k >= 9.

Usage:  python hales_jewett_tile.py [max_side]

1. An exact-cover search (Algorithm X style backtracking) finds an 8 x 8 tile.
2. The pairing is checked by brute force exactly as defined in Rocq (hj_step):
   on every m x n board with m, n <= max_side (default 26) it is an involution
   of the board, and every line with k = 9..12 contains a whole pair.

Cell kinds (the codes of hj_table in MNKHalesJewett.v):
  0 left end of a horizontal domino      partner (r, c + 1)
  1 right end                            partner (r, c - 1)
  2 top end of a vertical domino         partner (r + 1, c)
  3 bottom end                           partner (r - 1, c)
  4 top end of a diagonal domino         partner (r + 1, c + 1)
  5 bottom end                           partner (r - 1, c - 1)
  6 top end of an anti-diagonal domino   partner (r + 1, c - 1)
  7 bottom end                           partner (r - 1, c + 1)
"""

import sys

PERIOD = 8
NAMES = ["H<", "H>", "V^", "Vv", "D^", "Dv", "A^", "Av"]


def find_tile():
    """Return the tile as a flat list of 64 kinds, row by row."""
    candidates = []   # (line constraint, [(cell, kind), (cell, kind)])
    for r in range(PERIOD):
        for a in range(PERIOD):
            candidates.append((("H", r), [((r, a), 0), ((r, (a + 1) % PERIOD), 1)]))
    for c in range(PERIOD):
        for b in range(PERIOD):
            candidates.append((("V", c), [((b, c), 2), (((b + 1) % PERIOD, c), 3)]))
    for r in range(PERIOD):
        for c in range(PERIOD):
            down_right = ((r + 1) % PERIOD, (c + 1) % PERIOD)
            candidates.append((("D", (r - c) % PERIOD), [((r, c), 4), (down_right, 5)]))
            up_right = (r, (c + 1) % PERIOD)
            down_left = ((r + 1) % PERIOD, c)
            candidates.append((("A", (r + c + 1) % PERIOD), [(up_right, 6), (down_left, 7)]))

    kind = {}
    used = set()

    def solve():
        free = [(r, c) for r in range(PERIOD) for c in range(PERIOD) if (r, c) not in kind]
        if not free:
            return True
        cell = free[0]
        for constraint, cells in candidates:
            if constraint in used:
                continue
            if all(x != cell for x, _ in cells) or any(x in kind for x, _ in cells):
                continue
            used.add(constraint)
            for x, k in cells:
                kind[x] = k
            if solve():
                return True
            used.discard(constraint)
            for x, _ in cells:
                del kind[x]
        return False

    if not solve():
        raise SystemExit("no tile exists")
    return [kind[(r, c)] for r in range(PERIOD) for c in range(PERIOD)]


def partner(table, m, n, x):
    """hj_partner of MNKHalesJewett.v."""
    r, c = x // n, x % n
    k = table[PERIOD * (r % PERIOD) + c % PERIOD]
    if k == 0:
        return r * n + (c + 1) if c + 1 < n else x
    if k == 1:
        return r * n + (c - 1) if 1 <= c else x
    if k == 2:
        return (r + 1) * n + c if r + 1 < m else x
    if k == 3:
        return (r - 1) * n + c if 1 <= r else x
    if k == 4:
        return (r + 1) * n + (c + 1) if r + 1 < m and c + 1 < n else x
    if k == 5:
        return (r - 1) * n + (c - 1) if 1 <= r and 1 <= c else x
    if k == 6:
        return (r + 1) * n + (c - 1) if r + 1 < m and 1 <= c else x
    return (r - 1) * n + (c + 1) if 1 <= r and c + 1 < n else x


def lines(m, n, k):
    """gen_lines of MNKBoard.v."""
    out = []
    for r in range(m):
        for c in range(n - k + 1):
            out.append([r * n + c + i for i in range(k)])
    for r in range(m - k + 1):
        for c in range(n):
            out.append([(r + i) * n + c for i in range(k)])
    for r in range(m - k + 1):
        for c in range(n - k + 1):
            out.append([(r + i) * n + c + i for i in range(k)])
            out.append([(r + (k - 1 - i)) * n + c + i for i in range(k)])
    return out


def check(table, max_side):
    checked = 0
    for m in range(max_side + 1):
        for n in range(max_side + 1):
            for x in range(m * n):
                y = partner(table, m, n, x)
                assert 0 <= y < m * n and partner(table, m, n, y) == x, (m, n, x)
            for k in range(9, 13):
                for line in lines(m, n, k):
                    cells = set(line)
                    assert any(partner(table, m, n, x) != x and partner(table, m, n, x) in cells
                               for x in line), (m, n, k, line)
                    checked += 1
    return checked


def main():
    max_side = int(sys.argv[1]) if len(sys.argv) > 1 else 26
    table = find_tile()
    for r in range(PERIOD):
        print(" ".join(NAMES[table[PERIOD * r + c]] for c in range(PERIOD)))
    print("hj_table =", table)
    checked = check(table, max_side)
    print(f"OK: every board up to {max_side} x {max_side}: an involution, and all {checked} "
          f"lines with k = 9..12 contain a whole pair")


if __name__ == "__main__":
    main()
