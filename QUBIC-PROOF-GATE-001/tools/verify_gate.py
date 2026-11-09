"""QUBIC-PROOF-GATE-001: fail-closed specification-locked Rocq proof gate.

Requires a separate, human-approved SHA-256 manifest and an independently
reviewed, axiom-free Rules.v. No audit or game-theoretic claim is implied by
this tool alone. Run from a trusted CI workflow, not under an agent's control.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping


@dataclass(frozen=True)
class GateConfig:
    root: Path
    rocq: str
    manifest: Path


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_locked_sources(config: GateConfig) -> dict[str, str]:
    if not config.manifest.is_file():
        raise RuntimeError("No trusted manifest. Human approval and pinning required.")

    raw = json.loads(config.manifest.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise RuntimeError("Trusted manifest must be an object mapping paths to hashes.")

    expected_names = {
        "trusted/Rules.v",
        "trusted/Goal.v",
        "trusted/Acceptance.v",
    }
    if set(raw.keys()) != expected_names:
        raise RuntimeError("Trusted manifest must pin precisely the three trusted .v files.")

    observed_names = {
        path.relative_to(config.root).as_posix()
        for path in (config.root / "trusted").rglob("*.v")
    }
    if observed_names != expected_names:
        raise RuntimeError("Unpinned, missing, or extra trusted .v source detected.")

    verified: dict[str, str] = {}
    for relative_path, expected in raw.items():
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-fA-F]{64}", expected):
            raise RuntimeError(f"Missing SHA-256 approval for {relative_path}.")
        actual = sha256_file(config.root / relative_path)
        if actual.lower() != expected.lower():
            raise RuntimeError(f"Trusted source CHANGED: {relative_path}.")
        verified[relative_path] = actual

    return verified


def verify_snapshot(config: GateConfig, approved: Mapping[str, str]) -> None:
    for name, original_hash in approved.items():
        if sha256_file(config.root / name) != original_hash:
            raise RuntimeError(f"Trusted source modified during verification: {name}")


def run_command(arguments: list[str], cwd: Path) -> str:
    print("$", " ".join(arguments), flush=True)
    completed = subprocess.run(
        arguments,
        cwd=cwd,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    combined = f"{completed.stdout}\n{completed.stderr}"
    if completed.returncode != 0:
        raise RuntimeError(f"Command failed (exit {completed.returncode}):\n{combined}")
    print(combined, flush=True)
    return combined


def validate_agent_sources(root: Path) -> list[str]:
    agent_dir = root / "agent"
    if not (agent_dir / "Solution.v").is_file():
        raise RuntimeError("Missing agent/Solution.v; the global theorem is not proved.")
    helpers = sorted(path.name for path in agent_dir.glob("*.v") if path.name != "Solution.v")
    # For nontrivial dependencies, order helpers via a reviewed build graph.
    return helpers + ["Solution.v"]


def verify(config: GateConfig) -> None:
    approved = check_locked_sources(config)
    agent_sources = validate_agent_sources(config.root)

    with tempfile.TemporaryDirectory(prefix="qubic-proof-gate-") as temporary:
        sandbox = Path(temporary)
        for folder in ("trusted", "agent"):
            (sandbox / folder).mkdir()
            for source in (config.root / folder).glob("*.v"):
                shutil.copy2(source, sandbox / folder / source.name)

        arguments = ["-Q", "trusted", "QubicTrusted", "-Q", "agent", "QubicAgent"]
        rocq = config.rocq

        for source in ("Rules.v", "Goal.v"):
            run_command([rocq, "compile", *arguments, f"trusted/{source}"], sandbox)

        for source in agent_sources:
            run_command([rocq, "compile", *arguments, f"agent/{source}"], sandbox)

        acceptance_output = run_command(
            [rocq, "compile", *arguments, "trusted/Acceptance.v"], sandbox
        )

        # Rocq 9.1's Print Assumptions must report both final theorems as closed.
        # Fail closed if output format changes or assumptions become nonempty.
        closed_count = acceptance_output.count("Closed under the global context")
        if closed_count != 2:
            raise RuntimeError(
                f"Axiom/assumption audit FAILED: expected 2 closed theorems, got {closed_count}."
            )

        # Standalone kernel recheck of all compiled dependencies. Never use
        # -admit or -norec; those weaken recursive verification.
        run_command(
            [rocq, "check", *arguments, "QubicTrusted.Acceptance"], sandbox
        )

    verify_snapshot(config, approved)
    print("ACCEPTED: locked theorem, no reported assumptions, standalone checker passed.")
    print("NOTE: This proves the formalized goal, not that its model matches Qubic rules.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--rocq", default="rocq", help="Path to rocq executable")
    parser.add_argument("--manifest", type=Path, default=None)
    args = parser.parse_args()

    root = args.root.resolve()
    manifest = args.manifest.resolve() if args.manifest else root / "trusted_hashes.json"
    config = GateConfig(root=root, rocq=args.rocq, manifest=manifest)
    try:
        verify(config)
    except (OSError, ValueError, RuntimeError, json.JSONDecodeError) as error:
        print(f"REJECTED: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
