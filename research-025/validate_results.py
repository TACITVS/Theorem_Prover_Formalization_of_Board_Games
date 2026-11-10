"""Check instance hashes, stored SAT witnesses, and solver agreement."""
import hashlib
import json
from pathlib import Path

from instances import build_instances, validate_witness


def three_ply_white_win(white, black):
    from instances import LINES
    masks = [sum(1 << c for c in line) for line in LINES]
    w = sum(1 << c for c in white)
    b = sum(1 << c for c in black)
    for c in range(125):
        if (w | b) >> c & 1:
            continue
        after = w | (1 << c)
        if any(after & line == line for line in masks):
            return True
        black_targets = [line for line in masks if not line & after and (line & b).bit_count() == 4]
        targets = 0
        for line in masks:
            if not line & b and (line & after).bit_count() == 4:
                targets |= line & ~after
        if not black_targets and targets.bit_count() >= 2:
            return True
    return False


def main():
    directory = Path(__file__).resolve().parent
    instances = {item['name']: item for item in build_instances()}
    results = json.loads((directory / 'results.json').read_text())['results']
    answers, seen = {}, set()
    witnesses = 0
    for row in results:
        instance = instances[row['instance']]
        digest = hashlib.sha256(json.dumps(instance, sort_keys=True).encode()).hexdigest()
        if row['sha256'] != digest:
            raise ValueError(f'Instance hash mismatch: {row["instance"]}')
        key = row['instance'], row['backend']
        if key in seen:
            raise ValueError(f'Duplicate benchmark result: {key}')
        seen.add(key)
        status = row['status']
        if status in ['SAT', 'UNSAT']:
            answers.setdefault(row['instance'], set()).add(status)
        if status == 'SAT':
            validate_witness(instance, row['witness'])
            witnesses += 1
    if any(len(statuses) > 1 for statuses in answers.values()):
        raise ValueError('Solvers disagree on satisfiability')
    qbf = json.loads((directory / 'qbf_results.json').read_text())['results']
    for row in qbf:
        expected = three_ply_white_win(row['white'], row['black'])
        if row['expected'] != expected or row['status'] != ('TRUE' if expected else 'FALSE'):
            raise ValueError('Unresolved or failed QBF control')
    print(f'Validated {len(results)} records, {witnesses} SAT witnesses, and {len(qbf)} QBF controls.')
    print('UNSAT and QBF answers remain external solver claims.')


if __name__ == '__main__':
    main()
