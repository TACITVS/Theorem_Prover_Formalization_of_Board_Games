# Research Package 013 Provenance & Audit Notes

This directory contains the original raw artifacts from `QUBIC-RESEARCH-013_package.zip`:
- `QUBIC-RESEARCH-013_RESEARCH_NOTES.md`: Theoretical notes from the external contributor.
- `QUBIC-RESEARCH-013_safe10_certificate.json`: The 10-round nonterminal witness data.
- `QUBIC-RESEARCH-013_verify.py`: Independent Python verifier (which passes 100%).
- `QUBIC-RESEARCH-013_safe10.v`: Draft Rocq script that referenced an external `QubicGame.v`.

## Native Compilation in this Repository

The clean, standalone formalization of the 10-round safe leaf (using the project's standard 0..124 cell indexing and 109-line hypergraph) is located in:
- [`QubicAlgebraic.v`](../QubicAlgebraic.v) (24 Theorems, 100% closed under global context, 0 axioms, 0 admits).

Note regarding `QUBIC-RESEARCH-013_safe10.v` (Finding 5):
The raw file `QUBIC-RESEARCH-013_safe10.v` in this archive was an external draft referencing a non-shipped `QubicGame.v`. All verified contents, including the full 10-round nonterminal witness (`safe10_black`, `safe10_white`, 52 disjoint pairs), full 109-line coverage, and conditional line-blocking soundness, are natively formalized, closed, and audited without external dependencies in [`QubicAlgebraic.v`](../QubicAlgebraic.v).

It is compiled and audited automatically by the repository's main build harness:
```powershell
.\build.ps1
```
