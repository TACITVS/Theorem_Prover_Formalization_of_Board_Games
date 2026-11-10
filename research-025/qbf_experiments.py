"""Small alternating-move QBF controls, with a five-second CAQE limit."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time

from instances import Formula, LINES


def encode(white, black):
    assert not set(white) & set(black)
    assert not any(set(line) <= set(white) or set(line) <= set(black) for line in LINES)
    f = Formula()
    first = [f.variable() for _ in range(7)]
    opponent = [f.variable() for _ in range(7)]
    last = [f.variable() for _ in range(7)]
    false = f.variable()
    f.clauses.append([-false])

    def decode(bits):
        return [f.conjunction(bit if c >> i & 1 else -bit for i, bit in enumerate(bits))
                for c in range(125)]

    x, y, z = decode(first), decode(opponent), decode(last)
    free = [c for c in range(125) if c not in white + black]
    legal_first = f.disjunction(x[c] for c in free)
    legal_opponent = f.disjunction(f.conjunction([y[c], -x[c]]) for c in free)
    legal_last = f.disjunction(f.conjunction([z[c], -x[c], -y[c]]) for c in free)
    after_first = [-false if c in white else x[c] for c in range(125)]
    after_opponent = [-false if c in black else y[c] for c in range(125)]
    after_last = [f.disjunction([after_first[c], z[c]]) for c in range(125)]
    first_win = f.disjunction(f.conjunction(after_first[c] for c in line) for line in LINES)
    black_win = f.disjunction(f.conjunction(after_opponent[c] for c in line) for line in LINES)
    last_win = f.disjunction(f.conjunction(after_last[c] for c in line) for line in LINES)
    continuation = f.conjunction([-black_win, legal_last, last_win])
    # Universally quantified illegal requests are ignored. Every effective
    # legal opponent move is represented, and later existential moves depend
    # only on the preceding universal move.
    goal = f.conjunction([legal_first,
                          f.disjunction([first_win, -legal_opponent, continuation])])
    f.clauses.append([goal])
    auxiliary = list(range(22, f.nvars + 1))
    prefix = [('e', first), ('a', opponent), ('e', last + auxiliary)]
    text = f'p cnf {f.nvars} {len(f.clauses)}\n'
    text += ''.join(kind + ' ' + ' '.join(map(str, variables)) + ' 0\n'
                    for kind, variables in prefix)
    text += ''.join(' '.join(map(str, clause)) + ' 0\n' for clause in f.clauses)
    return text, f.nvars, len(f.clauses)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--caqe', default='caqe')
    parser.add_argument('--wsl-distro', default='Ubuntu-26.04')
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    scratch = directory.parent / 'scratch/solver-lab-instances'
    cases = [('empty_two_white_moves', [], [], False),
             ('one_short_of_fork', [101, 102, 103, 105, 110], [6, 17, 28, 39, 50], False),
             ('six_stone_fork_setup', [101, 102, 103, 105, 110, 115],
              [6, 17, 28, 39, 50, 61], True)]
    results = []
    for name, white, black, expected in cases:
        text, nvars, nclauses = encode(white, black)
        path = scratch / (name + '.qdimacs')
        path.write_text(text, encoding='utf-8', newline='\n')
        absolute = path.resolve()
        if os.name == 'nt':
            filename = '/mnt/' + absolute.drive[0].lower() + absolute.as_posix()[2:]
            prefix = ['wsl', '-d', args.wsl_distro, '--']
        else:
            filename, prefix = str(absolute), []
        started = time.perf_counter()
        completed = subprocess.run(prefix + ['timeout', '5', args.caqe, filename],
                                   capture_output=True, text=True, timeout=8)
        status = {10: 'TRUE', 20: 'FALSE', 124: 'TIMEOUT'}.get(completed.returncode, 'ERROR')
        row = dict(instance=name, backend='CAQE 4.0.1', status=status, expected=expected,
                   nvars=nvars, clauses=nclauses, white=white, black=black,
                   exit_code=completed.returncode, stdout=completed.stdout,
                   stderr=completed.stderr,
                   process_wall_seconds=time.perf_counter() - started)
        if status in ['TRUE', 'FALSE'] and (status == 'TRUE') != expected:
            raise RuntimeError(f'QBF control disagreement: {row}')
        results.append(row)
        print(name, status, flush=True)
    (directory / 'qbf_results.json').write_text(json.dumps(dict(
        scope='Three-ply tactical QBF controls; no imported Rocq certificate.',
        quantifiers='exists White move; forall legal Black reply; exists White move',
        results=results), indent=2) + '\n')


if __name__ == '__main__':
    main()
