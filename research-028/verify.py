"""Fresh source build and kernel check of the research-028 strategy trees.

Builds the pinned trusted rules and the agent helpers in a temporary directory,
compiles each generated tree file, requires every `Print Assumptions` to be
closed, then runs `rocq check` on each module.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HELPERS = ['Geometry', 'Minimax', 'RulesFacts', 'SafePairing', 'Stealing', 'Tactics',
           'TreeCertificates', 'ZLinearAlgebra', 'ZLinearDefense', 'ZPairingSeparation',
           'ZZLinearTrees']


def split_build(args, research, gate, check_hashes) -> None:
    """Persistent, resumable, parallel build of a split tree (export_split.py)."""
    from concurrent.futures import ThreadPoolExecutor
    n = args.split
    target = research / '_build'
    for d in ['trusted', 'agent', 'research']:
        (target / d).mkdir(parents=True, exist_ok=True)
    flags = ['-Q', 'trusted', 'QubicTrusted', '-Q', 'agent', 'QubicAgent',
             '-Q', 'research', 'QubicResearch028']
    t0 = time.time()

    def stage(src: Path, dst: Path) -> None:
        if not dst.exists() or dst.read_bytes() != src.read_bytes():
            shutil.copy2(src, dst)
            for ext in ('.vo', '.vok', '.vos', '.glob'):
                dst.with_suffix(ext).unlink(missing_ok=True)

    def compile_one(mod: str) -> str:
        vo = target / (mod + '.vo')
        if vo.exists():
            print(f'  [{time.time() - t0:.0f}s] {mod}: up to date (checkpoint)', flush=True)
            return ''
        t = time.time()
        done = subprocess.run([args.rocq, 'compile', *flags, mod + '.v'], cwd=target,
                              capture_output=True, text=True, encoding='utf-8',
                              errors='replace', timeout=args.timeout)
        out = done.stdout + done.stderr
        if done.returncode:
            raise RuntimeError(f'{mod}: exit {done.returncode}\n{out}')
        print(f'  [{time.time() - t0:.0f}s] {mod}: compiled in {time.time() - t:.0f}s', flush=True)
        return out

    def check_one(mod: str) -> None:
        t = time.time()
        logical = 'QubicResearch028.' + mod.split('/')[1]
        done = subprocess.run([args.rocq, 'check', '-silent', *flags, '-norec', logical],
                              cwd=target, capture_output=True, text=True, encoding='utf-8',
                              errors='replace', timeout=args.timeout)
        if done.returncode:
            raise RuntimeError(f'{mod}: rocq check failed\n{done.stdout}{done.stderr}')
        print(f'  [{time.time() - t0:.0f}s] {mod}: kernel recheck ok in {time.time() - t:.0f}s',
              flush=True)

    check_hashes()
    for name in ['Rules', 'Goal']:
        stage(gate / 'trusted' / f'{name}.v', target / 'trusted' / f'{name}.v')
    for name in HELPERS:
        stage(gate / 'agent' / f'{name}.v', target / 'agent' / f'{name}.v')
    parts = sorted((p.stem for p in research.glob(f'{n}Part*.v')),
                   key=lambda s: int(s[len(n) + 4:]))
    for name in [f'{n}Root', *parts, n]:
        stage(research / f'{name}.v', target / 'research' / f'{name}.v')
    for m in ['trusted/Rules', 'trusted/Goal'] + [f'agent/{h}' for h in HELPERS]:
        compile_one(m)
    compile_one(f'research/{n}Root')
    print(f'compiling {len(parts)} parts on {args.jobs} workers', flush=True)
    with ThreadPoolExecutor(args.jobs) as pool:
        list(pool.map(compile_one, [f'research/{p}' for p in parts]))
    (target / 'research' / f'{n}.vo').unlink(missing_ok=True)
    out = compile_one(f'research/{n}')
    if out.count('Closed under the global context') != 1 or 'Axioms:' in out:
        raise RuntimeError(f'{n}: assumption audit failed:\n{out}')
    if not args.skip_recheck:
        with ThreadPoolExecutor(args.jobs) as pool:
            list(pool.map(check_one, [f'research/{p}' for p in [f'{n}Root', *parts, n]]))
    check_hashes()
    print(f'VERIFIED {n}: start_state_total_defense is closed under the global context '
          f'({time.time() - t0:.0f}s)', flush=True)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('modules', nargs='*', help='generated module names, e.g. WitnessDepth1')
    ap.add_argument('--split', help='name of a split tree from export_split.py')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--skip-recheck', action='store_true')
    ap.add_argument('--rocq', default='rocq')
    ap.add_argument('--timeout', type=float, default=600)
    args = ap.parse_args()
    research = Path(__file__).resolve().parent
    gate = research.parent / 'QUBIC-PROOF-GATE-001'
    hashes = json.loads((gate / 'trusted_hashes.json').read_text(encoding='utf-8'))

    def check_hashes() -> None:
        for name, digest in hashes.items():
            if hashlib.sha256((gate / name).read_bytes()).hexdigest() != digest.lower():
                raise RuntimeError(f'Pinned source changed: {name}')

    def run(arguments, cwd) -> str:
        t = time.time()
        print('$', ' '.join(arguments), flush=True)
        done = subprocess.run(arguments, cwd=cwd, capture_output=True, text=True,
                              encoding='utf-8', errors='replace', timeout=args.timeout)
        out = done.stdout + done.stderr
        if done.returncode:
            raise RuntimeError(f'Exit {done.returncode}:\n{out}')
        print(f'  ok in {time.time() - t:.1f}s', flush=True)
        return out

    if args.split:
        return split_build(args, research, gate, check_hashes)
    check_hashes()
    flags = ['-Q', 'trusted', 'QubicTrusted', '-Q', 'agent', 'QubicAgent',
             '-Q', 'research', 'QubicResearch028']
    with tempfile.TemporaryDirectory(prefix='qubic-research-028-') as tmp:
        target = Path(tmp)
        for d in ['trusted', 'agent', 'research']:
            (target / d).mkdir()
        for name in ['Rules', 'Goal']:
            shutil.copy2(gate / 'trusted' / f'{name}.v', target / 'trusted')
        for name in HELPERS:
            shutil.copy2(gate / 'agent' / f'{name}.v', target / 'agent')
        for name in args.modules:
            shutil.copy2(research / f'{name}.v', target / 'research')
        for m in ['trusted/Rules', 'trusted/Goal'] + [f'agent/{h}' for h in HELPERS]:
            run([args.rocq, 'compile', *flags, m + '.v'], target)
        for name in args.modules:
            out = run([args.rocq, 'compile', *flags, f'research/{name}.v'], target)
            if out.count('Closed under the global context') != 1 or 'Axioms:' in out:
                raise RuntimeError(f'{name}: assumption audit failed:\n{out}')
            run([args.rocq, 'check', '-silent', *flags, f'QubicResearch028.{name}'], target)
            print(f'VERIFIED {name}: start_state_total_defense is closed under the global context',
                  flush=True)
    check_hashes()


if __name__ == '__main__':
    main()
