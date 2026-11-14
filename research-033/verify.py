#!/usr/bin/env python3
"""Verify QUBIC-PROOF-GATE-001 trusted hashes and kernel-check research-033 Rocq proofs.

Uses file-redirected subprocesses (never stdout/stderr PIPE) so Windows child
rocqworker processes cannot deadlock or outlive timeouts/interrupts, while
printing real-time progress heartbeats.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GATE_DIR = ROOT / "QUBIC-PROOF-GATE-001"
RESEARCH_DIR = Path(__file__).resolve().parent
DEFAULT_ROCQ = shutil.which("rocq") or r"C:\Rocq-Platform~9.1~2026.01\bin\rocq.exe"

PREREQ_MODULES: list[Path] = [
    GATE_DIR / "trusted" / "Rules.v",
    GATE_DIR / "trusted" / "Goal.v",
    GATE_DIR / "agent" / "Geometry.v",
    GATE_DIR / "agent" / "Minimax.v",
    GATE_DIR / "agent" / "RulesFacts.v",
    GATE_DIR / "agent" / "SafePairing.v",
]

MODULES: list[tuple[Path, int]] = [
    (RESEARCH_DIR / "ExactRegionCertificates.v", 1),
    (RESEARCH_DIR / "GadgetCatalog.v", 2),
    (RESEARCH_DIR / "PackingAndWitnesses.v", 5),
]

ROCQ_Q_FLAGS = [
    "-Q",
    str(GATE_DIR / "trusted"),
    "QubicTrusted",
    "-Q",
    str(GATE_DIR / "agent"),
    "QubicAgent",
    "-Q",
    str(RESEARCH_DIR),
    "QubicResearch033",
]


def verify_trusted_hashes() -> None:
    """Verify SHA-256 hashes of all pinned QUBIC-PROOF-GATE-001 files."""
    hashes_path = GATE_DIR / "trusted_hashes.json"
    hashes: dict[str, str] = json.loads(hashes_path.read_text(encoding="utf-8"))
    for rel_name, expected in hashes.items():
        target = GATE_DIR / rel_name
        actual = hashlib.sha256(target.read_bytes()).hexdigest()
        if actual.lower() != expected.lower():
            raise RuntimeError(
                f"SHA-256 mismatch for {rel_name}: expected {expected}, got {actual}"
            )
    print(
        f"[HASH ] Verified {len(hashes)} pinned files in QUBIC-PROOF-GATE-001/trusted_hashes.json",
        flush=True,
    )


def kill_process_tree(proc: subprocess.Popen[bytes] | subprocess.Popen[str]) -> None:
    """Terminate a child process and its descendants cleanly on Windows/POSIX."""
    if proc.poll() is not None:
        return
    if os.name == "nt":
        subprocess.run(
            ["taskkill", "/F", "/T", "/PID", str(proc.pid)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
    else:
        try:
            proc.terminate()
            proc.wait(timeout=3)
        except subprocess.TimeoutExpired:
            proc.kill()
    try:
        proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass


def run_monitored(
    label: str, cmd: list[str], timeout_s: float, heartbeat_s: float = 2.0
) -> tuple[int, str, float]:
    """Run a command with file-backed output, progress heartbeats, and tree-kill timeout."""
    fd, log_path_str = tempfile.mkstemp(prefix="verify_033_", suffix=".log")
    os.close(fd)
    log_path = Path(log_path_str)
    start = time.monotonic()
    last_report = start
    proc: subprocess.Popen[bytes] | None = None

    def _handle_sig(_signum: int, _frame: object) -> None:
        if proc is not None:
            kill_process_tree(proc)
        raise KeyboardInterrupt

    old_sigint = signal.getsignal(signal.SIGINT)
    signal.signal(signal.SIGINT, _handle_sig)
    try:
        print(f"[START] {label}", flush=True)
        with open(log_path, "wb") as logf:
            proc = subprocess.Popen(
                cmd,
                cwd=str(ROOT),
                stdout=logf,
                stderr=subprocess.STDOUT,
            )
            while True:
                rc = proc.poll()
                now = time.monotonic()
                elapsed = now - start
                if rc is not None:
                    break
                if elapsed > timeout_s:
                    kill_process_tree(proc)
                    out = log_path.read_text(encoding="utf-8", errors="replace")
                    raise TimeoutError(
                        f"{label} timed out after {elapsed:.2f}s\n{out}"
                    )
                if now - last_report >= heartbeat_s:
                    print(
                        f"  ... {label}: running ({elapsed:.1f}s / {timeout_s:.0f}s limit)",
                        flush=True,
                    )
                    last_report = now
                time.sleep(0.25)

        elapsed = time.monotonic() - start
        out = log_path.read_text(encoding="utf-8", errors="replace")
        print(f"[DONE ] {label}: rc={rc} elapsed={elapsed:.2f}s", flush=True)
        return rc, out, elapsed
    finally:
        signal.signal(signal.SIGINT, old_sigint)
        if proc is not None and proc.poll() is None:
            kill_process_tree(proc)
        try:
            log_path.unlink(missing_ok=True)
        except OSError:
            pass


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Verify QUBIC-PROOF-GATE-001 hashes and compile all research-033 proofs."
    )
    parser.add_argument(
        "--rocq",
        default=DEFAULT_ROCQ,
        help=f"Path to rocq executable (default: {DEFAULT_ROCQ})",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=120.0,
        help="Per-step timeout in seconds (default: 120)",
    )
    args = parser.parse_args()

    rocq_bin = args.rocq
    if not Path(rocq_bin).exists() and shutil.which(rocq_bin) is None:
        print(f"ERROR: rocq executable not found: {rocq_bin}", file=sys.stderr)
        return 2

    total_start = time.monotonic()
    verify_trusted_hashes()

    for prereq in PREREQ_MODULES:
        vo = prereq.with_suffix(".vo")
        if not vo.exists() or vo.stat().st_mtime < prereq.stat().st_mtime:
            rel = prereq.relative_to(ROOT).as_posix()
            rc, out, _ = run_monitored(
                rel, [rocq_bin, "compile", *ROCQ_Q_FLAGS, str(prereq)], args.timeout
            )
            if rc != 0:
                print(out.rstrip(), file=sys.stderr)
                return rc

    for mod_path, expected_closed in MODULES:
        rel = mod_path.relative_to(ROOT).as_posix()
        cmd = [rocq_bin, "compile", *ROCQ_Q_FLAGS, str(mod_path)]
        rc, out, _ = run_monitored(rel, cmd, args.timeout)
        if out.strip():
            print(out.rstrip(), flush=True)
        if rc != 0:
            print(f"ERROR: compilation failed for {rel} (rc={rc})", file=sys.stderr)
            return rc
        if "Axioms:" in out:
            print(f"ERROR: unexpected axioms detected in {rel}", file=sys.stderr)
            return 1
        closed_count = out.count("Closed under the global context")
        if closed_count != expected_closed:
            print(
                f"ERROR: expected {expected_closed} 'Closed under the global context' "
                f"checks in {rel}, got {closed_count}",
                file=sys.stderr,
            )
            return 1

    check_cmd = [
        rocq_bin,
        "check",
        "-silent",
        *ROCQ_Q_FLAGS,
        "QubicResearch033.ExactRegionCertificates",
        "QubicResearch033.GadgetCatalog",
        "QubicResearch033.PackingAndWitnesses",
    ]
    rc, chk_out, _ = run_monitored("rocq check QubicResearch033.*", check_cmd, args.timeout)
    if chk_out.strip():
        print(chk_out.rstrip(), flush=True)
    if rc != 0:
        print("ERROR: rocq check failed.", file=sys.stderr)
        return rc

    verify_trusted_hashes()
    total_elapsed = time.monotonic() - total_start
    print(
        f"\nALL RESEARCH-033 CHECKS PASSED (trusted hashes + 3 Rocq modules + kernel check, "
        f"8/8 theorems closed under the global context) in {total_elapsed:.2f}s.",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
