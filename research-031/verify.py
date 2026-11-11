"""Fresh source build and kernel check of research-031 Survival.v.

Checks the pinned trusted-source hashes, builds the trusted rules and agent
helpers in a temporary directory, compiles Survival.v, requires its single
`Print Assumptions` to be closed, and re-checks the module with `rocq check`.
"""
import hashlib
import json
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

HELPERS = ['Geometry', 'Minimax', 'RulesFacts', 'SafePairing', 'Stealing', 'Tactics']
FLAGS = ['-Q', 'trusted', 'QubicTrusted', '-Q', 'agent', 'QubicAgent',
         '-Q', 'research', 'QubicResearch031']


def main() -> None:
    research = Path(__file__).resolve().parent
    gate = research.parent / 'QUBIC-PROOF-GATE-001'
    hashes = json.loads((gate / 'trusted_hashes.json').read_text(encoding='utf-8'))

    def check_hashes() -> None:
        for name, digest in hashes.items():
            if hashlib.sha256((gate / name).read_bytes()).hexdigest() != digest.lower():
                raise RuntimeError(f'Pinned source changed: {name}')

    def run(args, cwd) -> str:
        t = time.time()
        print('$', ' '.join(args), flush=True)
        done = subprocess.run(args, cwd=cwd, capture_output=True, text=True,
                              encoding='utf-8', errors='replace', timeout=600)
        out = done.stdout + done.stderr
        if done.returncode:
            raise RuntimeError(f'Exit {done.returncode}:\n{out}')
        print(f'  ok in {time.time() - t:.1f}s', flush=True)
        return out

    check_hashes()
    with tempfile.TemporaryDirectory(prefix='qubic-research-031-') as tmp:
        target = Path(tmp)
        for d in ['trusted', 'agent', 'research']:
            (target / d).mkdir()
        for name in ['Rules', 'Goal']:
            shutil.copy2(gate / 'trusted' / f'{name}.v', target / 'trusted')
        for name in HELPERS:
            shutil.copy2(gate / 'agent' / f'{name}.v', target / 'agent')
        shutil.copy2(research / 'Survival.v', target / 'research')
        for m in ['trusted/Rules', 'trusted/Goal'] + [f'agent/{h}' for h in HELPERS]:
            run(['rocq', 'compile', *FLAGS, m + '.v'], target)
        out = run(['rocq', 'compile', *FLAGS, 'research/Survival.v'], target)
        print(out.strip())
        if out.count('Closed under the global context') != 1 or 'Axioms:' in out:
            raise RuntimeError('assumption audit failed')
        run(['rocq', 'check', '-silent', *FLAGS, 'QubicResearch031.Survival'], target)
    check_hashes()
    print('VERIFIED: cross_policy_delays_white_win_until_ply_seventeen '
          'is closed under the global context', flush=True)


if __name__ == '__main__':
    main()
