#!/usr/bin/env python3
"""
Standalone verification script for research-034:
  - 5-Pillar Mathematical Research Program for Settling 5x5x5 Qubic
  - Rocq 9.1 Formalization of 2-Core Hypergraph Contraction, Extended Coupled ES
    Gadgets (K3_plus), and 1-Fault-Tolerant Null-Move Lifting (PillarCertificates.v)
  - C++20/OpenMP 5-Pillar Solver (qubic5_pillar_solver.cpp) Milestone 1, 2, 3 &
    Round-by-Round Diagnostic Verification

Rules compliance (AGENTS.md / GEMINI.md Rule 1):
  - Redirects all subprocess output to log files rather than using subprocess.PIPE
    (which causes Windows rocqworker.exe child processes to hang on inherited handles).
  - Streams real-time progress updates every 1-2 seconds during compilation and verification.
  - Cleans up process trees via taskkill /F /T /PID on timeout or interruption.
"""

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path


DEFAULT_ROCQ_CANDIDATES = [
    r"C:\Rocq-Platform~9.1~2026.01\bin\rocq.exe",
    "rocq",
    "coqc",
]


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def verify_trusted_hashes(repo_root: Path) -> None:
    gate_dir = repo_root / "QUBIC-PROOF-GATE-001"
    hashes_path = gate_dir / "trusted_hashes.json"
    if not hashes_path.exists():
        raise RuntimeError(f"Missing trusted hashes file: {hashes_path}")

    expected = json.loads(hashes_path.read_text(encoding="utf-8"))
    for rel_path, exp_hash in expected.items():
        target = gate_dir / rel_path
        if not target.exists():
            raise RuntimeError(f"Missing trusted file: {target}")
        actual_hash = sha256_file(target)
        if actual_hash.lower() != exp_hash.lower():
            raise RuntimeError(
                f"SHA-256 mismatch for {rel_path}:\n"
                f"  expected: {exp_hash}\n"
                f"  actual:   {actual_hash}"
            )
    print(f"[PASS] All {len(expected)} trusted files in QUBIC-PROOF-GATE-001 match SHA-256 hashes.")


def find_rocq_binary(explicit_rocq: str | None) -> str:
    if explicit_rocq:
        if os.path.isfile(explicit_rocq) or shutil.which(explicit_rocq):
            return explicit_rocq
        raise RuntimeError(f"Specified --rocq binary not found: {explicit_rocq}")

    for cand in DEFAULT_ROCQ_CANDIDATES:
        if os.path.isfile(cand):
            return cand
        resolved = shutil.which(cand)
        if resolved:
            return resolved
    raise RuntimeError(
        "Could not locate rocq binary. Pass --rocq <path-to-rocq.exe> explicitly."
    )


def kill_process_tree(pid: int) -> None:
    if os.name == "nt":
        subprocess.run(
            ["taskkill", "/F", "/T", "/PID", str(pid)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
    else:
        try:
            os.kill(pid, 9)
        except OSError:
            pass


def run_redirected_command(
    cmd: list[str],
    cwd: Path,
    step_label: str,
    timeout_sec: float = 300.0,
) -> tuple[str, float]:
    """
    Runs a command with stdout/stderr redirected to a temporary file on disk
    (avoiding Windows pipe inheritance hangs with rocqworker.exe) and prints
    granular real-time progress updates while waiting.
    """
    start_t = time.time()
    with tempfile.NamedTemporaryFile(
        mode="w+", encoding="utf-8", suffix=".log", delete=False
    ) as tmp_log:
        log_path = Path(tmp_log.name)

    try:
        with log_path.open("w", encoding="utf-8") as out_f:
            proc = subprocess.Popen(
                cmd,
                cwd=str(cwd),
                stdout=out_f,
                stderr=subprocess.STDOUT,
            )
            last_report = start_t
            while True:
                ret = proc.poll()
                now = time.time()
                elapsed = now - start_t
                if ret is not None:
                    break
                if elapsed > timeout_sec:
                    kill_process_tree(proc.pid)
                    raise RuntimeError(
                        f"[{step_label}] Timed out after {elapsed:.1f}s: {' '.join(cmd)}"
                    )
                if now - last_report >= 2.0:
                    print(
                        f"  ... [{step_label}] running ({elapsed:.1f}s elapsed)",
                        flush=True,
                    )
                    last_report = now
                time.sleep(0.2)

        output = log_path.read_text(encoding="utf-8", errors="replace")
        total_time = time.time() - start_t
        if proc.returncode != 0:
            raise RuntimeError(
                f"[{step_label}] Command failed (exit code {proc.returncode}, {total_time:.2f}s):\n"
                f"Command: {' '.join(cmd)}\n"
                f"Output:\n{output}"
            )
        return output, total_time
    finally:
        try:
            log_path.unlink(missing_ok=True)
        except OSError:
            pass


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Verify research-034 Rocq 9.1 formalization and 5-Pillar C++20 solver milestones."
    )
    parser.add_argument(
        "--rocq",
        type=str,
        default=None,
        help="Path to rocq executable (defaults to C:\\Rocq-Platform~9.1~2026.01\\bin\\rocq.exe).",
    )
    parser.add_argument(
        "--cxx",
        type=str,
        default="g++",
        help="Path to C++20 compiler (defaults to g++).",
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent
    r033_dir = repo_root / "research-033"
    r034_dir = repo_root / "research-034"
    gate_dir = repo_root / "QUBIC-PROOF-GATE-001"

    overall_start = time.time()
    print("=" * 76)
    print("QUBIC 5x5x5 RESEARCH-034 VERIFICATION SUITE")
    print("5-Pillar Mathematical Research Program & Formal Rocq 9.1 Verification")
    print("=" * 76)

    # 1. Verify trusted hashes before compilation
    verify_trusted_hashes(repo_root)

    # 2. Locate rocq binary
    rocq_bin = find_rocq_binary(args.rocq)
    print(f"[INFO] Using Rocq binary: {rocq_bin}")

    q_flags = [
        "-Q", str(gate_dir / "trusted"), "QubicTrusted",
        "-Q", str(gate_dir / "agent"), "QubicAgent",
        "-Q", str(r033_dir), "QubicResearch033",
        "-Q", str(r034_dir), "QubicResearch034",
    ]

    # 3. Ensure prerequisite .vo files exist (Rules.v, ExactRegionCertificates.v, GadgetCatalog.v)
    prereqs = [
        ("Trusted Rules.v", gate_dir / "trusted" / "Rules.v"),
        ("Research-033 ExactRegionCertificates.v", r033_dir / "ExactRegionCertificates.v"),
        ("Research-033 GadgetCatalog.v", r033_dir / "GadgetCatalog.v"),
    ]
    for label, v_file in prereqs:
        vo_file = v_file.with_suffix(".vo")
        if not vo_file.exists():
            print(f"[STEP] Compiling prerequisite {label}...")
            _, dt = run_redirected_command(
                [rocq_bin, "compile", *q_flags, str(v_file)],
                cwd=repo_root,
                step_label=label,
            )
            print(f"[PASS] {label} compiled in {dt:.2f}s.")
        else:
            print(f"[INFO] Prerequisite {vo_file.name} already present.")

    # 4. Compile research-034/PillarCertificates.v
    pillar_v = r034_dir / "PillarCertificates.v"
    print(f"[STEP] Compiling {pillar_v.relative_to(repo_root)}...")
    out_v, dt_v = run_redirected_command(
        [rocq_bin, "compile", *q_flags, str(pillar_v)],
        cwd=repo_root,
        step_label="PillarCertificates.v",
    )
    print(out_v.strip())

    closed_count = out_v.count("Closed under the global context")
    if "Axioms:" in out_v or closed_count < 4:
        raise RuntimeError(
            f"Expected at least 4 'Closed under the global context' and 0 'Axioms:' "
            f"in PillarCertificates.v output, got {closed_count}."
        )
    print(
        f"[PASS] PillarCertificates.v compiled in {dt_v:.2f}s "
        f"({closed_count}/4 theorems Closed under the global context, 0 axioms)."
    )

    # 5. Run rocq check on QubicResearch034.PillarCertificates
    print("[STEP] Running rocq check on QubicResearch034.PillarCertificates...")
    out_chk, dt_chk = run_redirected_command(
        [
            rocq_bin,
            "check",
            "-silent",
            *q_flags,
            "QubicResearch034.PillarCertificates",
        ],
        cwd=repo_root,
        step_label="rocq check",
    )
    if "Axioms:" in out_chk:
        raise RuntimeError(f"Unexpected axioms reported by rocq check:\n{out_chk}")
    print(f"[PASS] rocq check succeeded in {dt_chk:.2f}s with zero axioms.")

    # 6. Compile C++20 5-Pillar Solver
    cpp_src = r034_dir / "qubic5_pillar_solver.cpp"
    exe_name = "qubic5_pillar_solver.exe" if os.name == "nt" else "qubic5_pillar_solver"
    cpp_exe = r034_dir / exe_name
    compile_cmd = [
        args.cxx,
        "-O3",
        "-march=native",
        "-fopenmp",
        "-std=c++20",
        str(cpp_src),
        "-o",
        str(cpp_exe),
    ]
    print(f"[STEP] Compiling {cpp_src.relative_to(repo_root)}...")
    _, dt_cxx = run_redirected_command(
        compile_cmd,
        cwd=repo_root,
        step_label="C++20 Compile",
    )
    print(f"[PASS] Compiled {cpp_exe.name} in {dt_cxx:.2f}s.")

    # 7. Run Milestones 1, 2, 3 and Round-by-Round Diagnostic
    run_cmd = [
        str(cpp_exe),
        "--milestone1",
        "--milestone2",
        "--milestone3",
        "--diag",
    ]
    print("[STEP] Running Milestone 1, Milestone 2, Milestone 3, and Round Diagnostics...")
    out_run, dt_run = run_redirected_command(
        run_cmd,
        cwd=repo_root,
        step_label="Milestones 1-3 + Diag",
    )
    print(out_run.strip())

    required_markers = [
        "[MILESTONE 1 PASS]",
        "[MILESTONE 2 PASS]",
        "[MILESTONE 3 PASS]",
        "=== DIAGNOSTIC:",
    ]
    for marker in required_markers:
        if marker not in out_run:
            raise RuntimeError(f"Missing expected pass marker in solver output: {marker}")
    print(f"[PASS] All C++ 5-Pillar Milestones & Diagnostics passed in {dt_run:.2f}s.")

    # 8. Re-verify trusted hashes at end of run
    verify_trusted_hashes(repo_root)

    total_elapsed = time.time() - overall_start
    print("=" * 76)
    print(f"[OVERALL PASS] research-034 verified end-to-end in {total_elapsed:.2f}s.")
    print("=" * 76)
    return 0


if __name__ == "__main__":
    sys.exit(main())
