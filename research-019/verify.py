"""Fresh verification of tactical pruning and the quantified opening bound.

This checks partial results, not a resolution of the empty-board game value.
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
    if set(hashes) != {'trusted/Rules.v', 'trusted/Goal.v', 'trusted/Acceptance.v'}:
        raise RuntimeError('Unexpected trusted-source manifest')

    def check_hashes() -> None:
        for name, digest in hashes.items():
            if hashlib.sha256((gate / name).read_bytes()).hexdigest() != digest.lower():
                raise RuntimeError(f'Pinned source changed: {name}')

    check_hashes()
    helpers = ['Geometry', 'Minimax', 'RulesFacts', 'SafePairing', 'Tactics']
    with tempfile.TemporaryDirectory(prefix='qubic-research-019-') as temporary:
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
                 '-Q', 'research', 'QubicResearch019']

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
        expected = len(re.findall(r'^Print Assumptions ',
            (research / 'AuditProgress.v').read_text(encoding='utf-8'), re.MULTILINE))
        if expected != 15 or audit.count('Closed under the global context') != expected or 'Axioms:' in audit:
            raise RuntimeError('Partial-result assumption audit failed')
        run([args.rocq, 'check', '-silent', *flags, 'QubicResearch019.AuditProgress'])
    check_hashes()
    print('VERIFIED: 15 selected tactical/opening results have no assumptions; kernel recheck passed.')
    print('UNRESOLVED: a delay through ply 14 is not a full-game draw or first-player win proof.')


if __name__ == '__main__':
    main()
