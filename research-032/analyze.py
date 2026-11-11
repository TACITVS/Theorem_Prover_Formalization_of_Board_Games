"""Independent replay of mb.exe games (research 032).

Rebuilds the 109 lines from scratch, replays every game, and re-derives the
result without trusting the engine:
  - "maker":   Maker owns a full line after its last move, and not earlier;
  - "breaker": the Erdos-Selfridge potential is below the exact threshold for
               the side to move (pot < 32 Breaker to move, pot < 16 Maker to move).
Prints a summary table. Runs in well under a second.
"""
import json
import sys
from itertools import product
from statistics import median


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
    return sorted(lines, key=sorted)


LINES = build_lines()


def potential(maker, breaker):
    return sum(1 << len(l & maker) for l in LINES if not (l & breaker))


def replay(g):
    maker, breaker = set(), set()
    for i, c in enumerate(g['moves']):
        assert 0 <= c < 125 and c not in maker and c not in breaker, 'illegal move'
        assert not any(l <= maker for l in LINES), 'play continued after a Maker line'
        (breaker if i & 1 else maker).add(c)
        assert potential(maker, breaker) == g['pot'][i + 1], 'potential mismatch'
    n = len(g['moves'])
    if any(l <= maker for l in LINES):
        return 'maker'
    pot = potential(maker, breaker)
    if pot < (32 if n & 1 else 16):
        return 'breaker'
    return 'open'


def fours_made(g):
    """How many times a Maker move left a live line with four Maker stones."""
    maker, breaker, n = set(), set(), 0
    for i, c in enumerate(g['moves']):
        (breaker if i & 1 else maker).add(c)
        if not i & 1:
            n += sum(1 for l in LINES if c in l and len(l & maker) == 4 and not (l & breaker))
    return n


def main():
    for path in sys.argv[1:]:
        games = {}
        with open(path, encoding='utf-8') as f:
            for line in f:
                g = json.loads(line)
                games[g['id']] = g        # later records (resume) replace earlier ones
        done = [g for g in games.values() if g['status'] == 'done']
        for g in done:
            got = replay(g)
            assert got == g['result'], f"game {g['id']}: engine says {g['result']}, replay says {got}"
        mk = [g for g in done if g['result'] == 'maker']
        br = [g for g in done if g['result'] == 'breaker']
        print(f'{path}: {len(done)} finished games, all results confirmed by replay')
        print(f'  Maker wins: {len(mk)}' + (f", at plies {sorted(g['plies'] for g in mk)}" if mk else ''))
        if br:
            pl = sorted(g['plies'] for g in br)
            print(f'  Breaker wins (exact Erdos-Selfridge): {len(br)}, '
                  f'at plies {pl[0]}-{pl[-1]}, median {median(pl)}')
        threats = [fours_made(g) for g in done]
        if threats:
            print(f'  Maker threats (live line brought to 4 stones) per game: '
                  f'min {min(threats)}, median {median(threats)}, max {max(threats)}')
        peak = [max(g['pot']) for g in done]
        if peak:
            print(f'  peak potential per game: min {min(peak)}, median {median(peak)}, max {max(peak)} '
                  f'(empty board 109)')


if __name__ == '__main__':
    main()
