"""One solver per process, with no shared native-library state."""
import json
import os
from pathlib import Path
import subprocess
import sys
import time


def main():
    backend, filename = sys.argv[1:3]
    instance = json.loads(Path(filename).read_text())
    clauses = instance['clauses']
    started = time.perf_counter()
    if backend in ['cadical-cli', 'kissat-cli']:
        program = backend.removesuffix('-cli')
        cnf = Path(filename).with_suffix('.cnf').resolve()
        prefix = []
        if os.name == 'nt':
            prefix = ['wsl', '-d', 'Ubuntu-26.04', '--']
            cnf_name = '/mnt/' + cnf.drive[0].lower() + cnf.as_posix()[2:]
        else:
            cnf_name = str(cnf)
        version = subprocess.check_output(prefix + [program, '--version'], text=True).strip()
        completed = subprocess.run(prefix + ['timeout', '4', program, '-q', cnf_name],
                                   capture_output=True, text=True)
        output = completed.stdout
        if completed.returncode == 10:
            answer = 'SAT'
            model = [int(value) for line in output.splitlines() if line.startswith('v ')
                     for value in line[2:].split() if int(value)]
        elif completed.returncode == 20:
            answer, model = 'UNSAT', None
        elif completed.returncode == 124:
            answer, model = 'TIMEOUT', None
        else:
            raise RuntimeError(f'{program} exit {completed.returncode}: {completed.stderr}')
    elif backend == 'highs-native':
        import highspy
        import numpy as np
        if [] in clauses:
            print(json.dumps(dict(status='UNSAT', model=None,
                                  version=highspy.Highs().version(), solve_wall_seconds=0)))
            return
        solver = highspy.Highs()
        solver.setOptionValue('output_flag', False)
        solver.setOptionValue('threads', 1)
        solver.setOptionValue('time_limit', 4.0)
        pairs = instance['pairs']
        n = len(pairs)
        solver.addVars(n, np.zeros(n), np.ones(n))
        solver.changeColsIntegrality(n, np.arange(n, dtype=np.int32), np.ones(n, dtype=np.uint8))
        groups = [[i for i, entry in enumerate(pairs) if entry[1] == line]
                  for line in range(109) if any(entry[1] == line for entry in pairs)]
        groups += [[i for i, entry in enumerate(pairs) if cell in entry[2:]]
                   for cell in range(125)]
        line_count = len(groups) - 125
        starts, indices = [0], []
        for group in groups:
            indices.extend(group)
            starts.append(len(indices))
        lower = np.array([1.] * line_count + [0.] * 125)
        solver.addRows(len(groups), lower, np.ones(len(groups)), len(indices),
                       np.array(starts, dtype=np.int32), np.array(indices, dtype=np.int32),
                       np.ones(len(indices)))
        solver.run()
        status = solver.getModelStatus()
        solution = solver.getSolution()
        if status == highspy.HighsModelStatus.kOptimal and solution.value_valid:
            selected = [entry[1:] for entry, value in zip(pairs, solution.col_value) if value > .5]
            print(json.dumps(dict(status='SAT', model=None, native_witness=selected,
                                  version=solver.version(),
                                  solve_wall_seconds=time.perf_counter() - started)))
            return
        answer = 'UNSAT' if status == highspy.HighsModelStatus.kInfeasible else 'UNKNOWN'
        model, version = None, solver.version()
    elif backend == 'highs':
        import highspy
        import numpy as np
        solver = highspy.Highs()
        solver.setOptionValue('output_flag', False)
        solver.setOptionValue('threads', 1)
        solver.setOptionValue('time_limit', 4.0)
        n = instance['nvars']
        solver.addVars(n, np.zeros(n), np.ones(n))
        solver.changeColsIntegrality(n, np.arange(n, dtype=np.int32),
                                     np.ones(n, dtype=np.uint8))
        indices, coefficients, starts, lower = [], [], [0], []
        for clause in clauses:
            literals = set(clause)
            if any(-lit in literals for lit in literals):
                continue
            lower.append(1 - sum(lit < 0 for lit in literals))
            indices.extend(abs(lit) - 1 for lit in literals)
            coefficients.extend(1 if lit > 0 else -1 for lit in literals)
            starts.append(len(indices))
        solver.addRows(len(lower), np.array(lower, dtype=float),
                       np.full(len(lower), highspy.kHighsInf), len(indices),
                       np.array(starts, dtype=np.int32),
                       np.array(indices, dtype=np.int32),
                       np.array(coefficients, dtype=float))
        solver.run()
        status = solver.getModelStatus()
        solution = solver.getSolution()
        if solution.value_valid and all(any(
                (solution.col_value[abs(lit) - 1] > .5) == (lit > 0)
                for lit in clause) for clause in clauses):
            answer = 'SAT'
            model = [i + 1 if x > .5 else -i - 1 for i, x in enumerate(solution.col_value)]
        else:
            answer = 'UNSAT' if status == highspy.HighsModelStatus.kInfeasible else 'UNKNOWN'
            model = None
        version = solver.version()
    elif backend == 'cryptominisat':
        import pycryptosat
        solver = pycryptosat.Solver(threads=1)
        for clause in clauses:
            solver.add_clause(clause)
        sat, assignment = solver.solve()
        answer = 'SAT' if sat else 'UNSAT'
        model = [i if value else -i for i, value in enumerate(assignment) if i] if sat else None
        version = pycryptosat.__version__
    else:
        import pysat
        from pysat.solvers import Solver
        with Solver(name=backend, bootstrap_with=clauses) as solver:
            sat = solver.solve()
            answer = 'SAT' if sat else 'UNSAT'
            model = solver.get_model() if sat else None
        version = pysat.__version__
    print(json.dumps(dict(status=answer, model=model, version=version,
                          solve_wall_seconds=time.perf_counter() - started)))


if __name__ == '__main__':
    main()
