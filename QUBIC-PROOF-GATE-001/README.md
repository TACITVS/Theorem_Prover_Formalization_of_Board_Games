# QUBIC-PROOF-GATE-001 — Specification-Locked Rocq Gate

**Status:** Gate scaffolding. Deliberately **cannot pass** until the independent
`Rules.v` is written, reviewed and frozen, and the agent proves the exact
`Goal.ExactDraw` proposition. NOT a proof of Qubic.

## Security design

- `trusted/Rules.v`: human-reviewed rules (not supplied), complete legal,
  terminal game semantics, nonempty strategy types, verified 109 lines.
- `trusted/Goal.v`: frozen exact specification: Black's nonloss AND White's
  nonloss; neither alone counts as exact draw.
- `trusted/Acceptance.v`: protected proof gate; checks the agent's theorem terms
  against the frozen Goal and prints all assumptions.
- `agent/Solution.v`: only agent-editable work; must supply `black_nonloss` and
  `exact_draw` with exact trusted types.
- `trusted_hashes.json`: NOT supplied. A HUMAN approves SHA-256 values for all
  three trusted `.v` sources and commits the manifest on a protected branch.
- `tools/verify_gate.py`: MUST also be protected from agent edits. Runs fresh
  ordinary `.vo` compilation, checks both `Print Assumptions` reports, and
  uses Rocq 9.1's standalone `rocq check` verifier. It must run in CI under
  rules the agent cannot change.

## Deployment

1. A separate person/model audits and implements `trusted/Rules.v`.
   NEVER use axioms or placeholder `True` definitions for game outcome.
2. Audit `trusted/Goal.v` and `trusted/Acceptance.v`; freeze ALL trusted sources.
3. In protected CI, create `trusted_hashes.json` from the audited source SHA256
   values. The agent must not be able to modify the hashes or CI workflow.
   On PowerShell, for example:
   `(Get-FileHash trusted/Rules.v -Algorithm SHA256).Hash.ToLower()`
4. Rename/create `agent/Solution.v`, with actual proofs of the exact Goal.
5. Run:
   `python tools/verify_gate.py --rocq rocq`

A failure is expected until the actual global game-value theorem is proved.
A compiler exit code 0 for an arbitrary agent module is NOT a pass.
Only the trusted gate's complete verification is a pass.

## Threat model and limits

- An agent able to modify the CI workflow, trusted hashes, trusted files, the
  Rocq binary, or its execution environment can bypass a local gate. Use GitHub
  protected branches, CODEOWNERS, required checks, and a clean pinned CI image.
- The kernel proves the **formal statement**, relative to its assumptions and
  kernel. Humans must still verify correspondence of `Rules.v` with actual
  standard 5x5x5 Qubic. Test all 109 lines and terminal cases independently.
- Make nonvacuity theorems mandatory: actual White and Black strategies exist,
  game starts on an empty board, and all legal positions are representable.
- No `-vos`, `-vok`, `-admit`, or `-norec` in a successful release run.
- The shown skeleton assumes a single `agent/Solution.v` and optional independent
  helper files with simple sorted dependencies. Replace helper build order with
  `rocq makefile` or Dune in a large real project, retaining the same trust gate.
- Never confuse `BlackNonLossFromEmpty` with `ExactDraw`; the latter requires both
  first-player and second-player nonloss (under standard zero-sum rules).
