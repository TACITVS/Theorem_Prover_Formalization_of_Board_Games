# Research 025: bounded SAT, MIP and QBF experiments

The benchmark records 47 runs on 11 finite instances using CaDiCaL, Kissat,
CryptoMiniSat and HiGHS, plus three CAQE tactical QBF controls. Twenty SAT
witnesses pass independent semantic checks. One solver-discovered game trace
is exported to Rocq and proves that the existing blocking policy's 14-ply
guarantee is tight. The full game's value remains unresolved.

## Recorded outcomes

| Instance | CaDiCaL | Kissat | CryptoMiniSat | HiGHS, CNF as MIP |
| --- | --- | --- | --- | --- |
| Full board coloring without a monochromatic winning line | SAT | SAT | SAT | SAT |
| Center singleton as XOR of at most 19 lines | SAT | SAT | SAT | SAT |
| Center singleton as XOR of at most 17 lines | UNSAT | UNSAT | UNSAT | UNKNOWN |
| Disjoint pairs covering the empty board | UNSAT | TIMEOUT | UNSAT | UNKNOWN |
| Disjoint pairs at the strict linear-code witness | UNSAT | TIMEOUT | UNSAT | UNKNOWN |
| Disjoint pairs at the known safe 10-round position | SAT | SAT | SAT | SAT |
| First White win at ply 9 against lowest-free Black | SAT | SAT | SAT | SAT |
| First White win at ply 13 against the blocking policy | TIMEOUT | TIMEOUT | TIMEOUT | UNKNOWN |
| First White win at ply 15 against the blocking policy | TIMEOUT | TIMEOUT | TIMEOUT | UNKNOWN |
| Ply 15, White restricted to the far two-line region | UNSAT | UNSAT | UNSAT | UNSAT |
| Ply 15, two-line region also containing cell 4 | SAT | SAT | SAT | TIMEOUT |

Limits are four seconds inside Linux CLI solvers and HiGHS, with a six-second
outer process limit. CryptoMiniSat uses the outer limit. UNKNOWN and TIMEOUT
are unresolved runs. Every game instance asks for a first win at its exact
depth, excludes earlier wins by either player, and uses the frozen policy's
lowest-free-cell fallback.

HiGHS also solves equivalent native packing models. It reports the two
infeasible pairing cases in about 0.27–0.32 seconds and finds the known safe
pairing in about 0.21 seconds. The corresponding CNF-as-MIP runs need more time.
This small comparison shows the effect of the representation. Timings include
process setup, use mixed Windows/WSL execution, and do not establish a general
solver ranking. Raw versions, wall times, formula hashes and witnesses are in
`results.json`.

The far-region control is infeasible because White's restricted moves cannot
interrupt Black's early completion of cells 0–4. Adding cell 4 to the allowed
region makes a winning attack possible. Both players' terminal conditions
therefore matter in the encoding.

## Rocq-checked counterexample

Kissat returned the following White moves against `Tactics.blocking_policy`

```text
4, 29, 54, 100, 101, 102, 104, 103
```

Black's responses are `0, 1, 2, 3, 5, 6, 79`. White completes
`[100;101;102;103;104]` at ply 15. `Counterexamples.v` evaluates the exact frozen
game and proves

- White wins at ply 15 against this policy.
- White wins in the full 125-ply evaluator against this policy.
- The previous universal 14-ply bound is tight for this policy.

All three `Print Assumptions` outputs are closed. Compilation and the ordinary
recursive kernel check passed. The SAT assignments establish concrete attacks
against particular policies. The remaining six opening game values are still
undetermined.

## QBF controls

CAQE 4.0.1 solves formulas with the prefix

```text
exists White move, forall Black move, exists White move
```

Illegal universal moves are guarded out, all legal Black moves are covered,
and existential decisions depend only on preceding universal choices.
The empty position and a five-stone position return FALSE. A six-stone fork
setup returns TRUE. An independent tactical enumerator agrees on all three
controls. These are short-horizon controls, with external solver answers and
no imported Rocq QBF proof certificate.

## Reproduce

Python 3.12 and the packages in `requirements.txt` reproduce the instance
generator and Windows CryptoMiniSat/HiGHS runs. On the tested machine, CaDiCaL
2.1.3 and Kissat 4.0.3 run under Ubuntu 26.04 in WSL. The initial Windows
binding probe encountered access violations and is retained in
`windows_binding_probe.json`. The main comparison uses the Linux executables.

```powershell
python -m venv scratch/solver-lab-venv
scratch/solver-lab-venv/Scripts/python.exe -m pip install -r research-025/requirements.txt
wsl -d Ubuntu-26.04 -u root -- apt-get install -y cadical kissat
scratch/solver-lab-venv/Scripts/python.exe research-025/run_experiments.py --resume --backends cadical-cli kissat-cli cryptominisat highs highs-native
scratch/solver-lab-venv/Scripts/python.exe research-025/validate_results.py
python research-025/export_counterexamples.py
rocq compile -Q QUBIC-PROOF-GATE-001/trusted QubicTrusted -Q QUBIC-PROOF-GATE-001/agent QubicAgent -Q research-025 QubicResearch025 research-025/Counterexamples.v
rocq check -silent -Q QUBIC-PROOF-GATE-001/trusted QubicTrusted -Q QUBIC-PROOF-GATE-001/agent QubicAgent -Q research-025 QubicResearch025 QubicResearch025.Counterexamples
```

Each solver call is a bounded, isolated work unit. The driver reports each
completed instance and atomically saves its result immediately. `--resume`
skips completed instance/backend/hash combinations. An interrupted in-flight
call must be rerun because these solver interfaces do not expose persistent
internal search checkpoints. Solver node counters are not recorded.

CAQE was built in WSL from `ltentrup/caqe` with `cargo build --release
--no-default-features` and `CMAKE_POLICY_VERSION_MINIMUM=3.5` for its older
CryptoMiniSat dependency. To rerun the three controls, pass the built binary
path explicitly

```powershell
scratch/solver-lab-venv/Scripts/python.exe research-025/qbf_experiments.py --caqe /home/baianoise/.cache/qubic-solver-lab/caqe/target/release/caqe
```

The CNF instance generator has no Rocq correctness proof. UNSAT, MIP
infeasibility and QBF outcomes remain external claims. The exported concrete
counterexample is checked directly against `Rules.v`, and does not rely on
the correctness of the solver or CNF translation.
