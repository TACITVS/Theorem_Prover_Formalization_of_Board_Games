"""Fresh verification of partial research results; NOT the exact-draw gate.

The original trusted files and their manifest are only read. All compilation
is in a temporary directory. No old .vo files can satisfy dependencies.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rocq', default='rocq')
    parser.add_argument('--timeout', type=float, default=120)
    args = parser.parse_args()
    research = Path(__file__).resolve().parent
    gate = research.parent / 'QUBIC-PROOF-GATE-001'
    hashes = json.loads((gate / 'trusted_hashes.json').read_text(encoding='utf-8'))
    expected = {'trusted/Rules.v', 'trusted/Goal.v', 'trusted/Acceptance.v'}
    if set(hashes) != expected:
        raise RuntimeError('Unexpected trusted manifest contents')

    def check_hashes() -> None:
        for name, digest in hashes.items():
            actual = hashlib.sha256((gate / name).read_bytes()).hexdigest()
            if actual != digest.lower():
                raise RuntimeError(f'Pinned source changed: {name}')

    check_hashes()
    helpers = ['Geometry', 'Minimax', 'RulesFacts', 'Stealing', 'Solution']
    with tempfile.TemporaryDirectory(prefix='qubic-research-017-') as temporary:
        target = Path(temporary)
        for directory in ['trusted', 'agent', 'research']:
            (target / directory).mkdir()
        for name in ['Rules', 'Goal']:
            shutil.copy2(gate / 'trusted' / f'{name}.v', target / 'trusted')
        for name in helpers:
            shutil.copy2(gate / 'agent' / f'{name}.v', target / 'agent')
        for name in ['Regressions', 'AuditProgress']:
            shutil.copy2(research / f'{name}.v', target / 'research')
        flags = ['-Q', 'trusted', 'QubicTrusted', '-Q', 'agent', 'QubicAgent',
                 '-Q', 'research', 'QubicResearch']

        def run(arguments: list[str]) -> str:
            print('$', ' '.join(arguments), flush=True)
            completed = subprocess.run(
                arguments, cwd=target, capture_output=True, text=True,
                encoding='utf-8', errors='replace', timeout=args.timeout,
            )
            output = completed.stdout + completed.stderr
            if completed.returncode:
                raise RuntimeError(f'Exit {completed.returncode}:\n{output}')
            if output:
                print(output, end='', flush=True)
            return output

        modules = ['trusted/Rules', 'trusted/Goal']
        modules += [f'agent/{name}' for name in helpers]
        modules += ['research/Regressions', 'research/AuditProgress']
        audit = ''
        for module in modules:
            audit = run([args.rocq, 'compile', *flags, module + '.v'])
        audit_source = (research / 'AuditProgress.v').read_text(encoding='utf-8')
        count = len(re.findall(r'^Print Assumptions ', audit_source, re.MULTILINE))
        if count != 15 or audit.count('Closed under the global context') != count or 'Axioms:' in audit:
            raise RuntimeError('Partial-result assumption audit failed')
        run([args.rocq, 'check', '-silent', *flags,
             'QubicAgent.Geometry', 'QubicAgent.Stealing', 'QubicResearch.AuditProgress'])
    check_hashes()
    print('VERIFIED: 15 selected partial-result theorems have no reported assumptions; kernel recheck passed.')
    print('UNRESOLVED: black_nonloss is still admitted; fairness/unfairness is NOT established.')


if __name__ == '__main__':
    main()
