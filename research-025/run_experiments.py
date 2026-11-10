"""Bounded, sequential solver comparisons on shared CNF instances."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from instances import build_instances, validate_model, validate_pairing


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=float, default=6)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('results.json'))
    parser.add_argument('--backends', nargs='+',
                        default=['cadical-cli', 'kissat-cli', 'cryptominisat', 'highs'])
    parser.add_argument('--only', nargs='+')
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    scratch = directory.parent / 'scratch/solver-lab-instances'
    scratch.mkdir(exist_ok=True)
    results = json.loads(args.output.read_text())['results'] if args.resume and args.output.exists() else []
    run_started = time.perf_counter()
    for instance in build_instances():
        if args.only and instance['name'] not in args.only:
            continue
        encoded = json.dumps(instance, sort_keys=True)
        path = scratch / (instance['name'] + '.json')
        path.write_text(encoded)
        path.with_suffix('.cnf').write_text(
            f'p cnf {instance["nvars"]} {len(instance["clauses"])}\n' +
            ''.join(' '.join(map(str, clause)) + ' 0\n' for clause in instance['clauses']))
        for backend in args.backends:
            if backend == 'highs-native' and instance['kind'] != 'pairing':
                continue
            digest = hashlib.sha256(encoded.encode()).hexdigest()
            if any(row['instance'] == instance['name'] and row['backend'] == backend and
                   row['sha256'] == digest for row in results):
                continue
            started = time.perf_counter()
            row = dict(instance=instance['name'], backend=backend,
                       nvars=instance['nvars'], clauses=len(instance['clauses']),
                       sha256=digest)
            try:
                completed = subprocess.run([sys.executable, str(directory / 'worker.py'),
                                            backend, str(path)], capture_output=True,
                                           text=True, timeout=args.timeout)
                if completed.returncode:
                    raise RuntimeError(f'Exit {completed.returncode}: {completed.stderr}')
                answer = json.loads(completed.stdout)
                model = answer.pop('model')
                row.update(answer)
                if row['status'] == 'SAT':
                    native = row.pop('native_witness', None)
                    row['witness'] = (validate_pairing(instance, native) if native is not None
                                      else validate_model(instance, model))
                    row['assignment_verified'] = True
            except subprocess.TimeoutExpired:
                row['status'] = 'TIMEOUT'
            except Exception as error:
                row['status'] = 'ERROR'
                row['error'] = str(error)
            row['process_wall_seconds'] = time.perf_counter() - started
            results.append(row)
            temporary = args.output.with_suffix('.tmp')
            temporary.write_text(json.dumps(dict(
                timeout_seconds=args.timeout, sequential=True,
                scope='Finite instances; UNSAT claims have no imported Rocq proof certificate.',
                results=results), indent=2) + '\n')
            os.replace(temporary, args.output)
            print(instance['name'], backend, row['status'],
                  'ply', instance.get('plies', '-'),
                  'variables', instance['nvars'], 'clauses', len(instance['clauses']),
                  'seconds', round(row['process_wall_seconds'], 3),
                  'completed', len(results), 'elapsed', round(time.perf_counter() - run_started, 2),
                  flush=True)


if __name__ == '__main__':
    main()
