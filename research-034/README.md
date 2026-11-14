# Research-034: 5-Pillar Mathematical Research Program for Settling $5\times 5\times 5$ Qubic

This directory implements, benchmarks, and formally verifies in **Rocq 9.1** the 5-pillar research program proposed in [`mathematical_research_program_for_settling_5x5x5_qubic.md`](../mathematical_research_program_for_settling_5x5x5_qubic.md) on top of [`qubic5_settle.cpp.cpp`](../qubic5_settle.cpp.cpp) and the region-gadget certificate calculus in [`research-033/`](../research-033/README.md).

All proofs compile against the unchanged [`QUBIC-PROOF-GATE-001/trusted/Rules.v`](../QUBIC-PROOF-GATE-001/trusted/Rules.v) specification with **zero axioms** and **zero `Admitted` lemmas**. All C++ solvers comply strictly with [`AGENTS.md`](../AGENTS.md) / [`GEMINI.md`](../GEMINI.md) Rule 1 (granular real-time progress reporting, persistent checkpointing to disk with `--resume`, and upfront complexity estimates).

---

## 1. Architecture of the 5 Pillars

### Pillar 1 — 2-Core Hypergraph Contraction & Colorblind Isomorphism Quotienting (`HyperState`)
Instead of storing full $(X, O)$ bitboards (`Board { u128 x; u128 o; }`), any Maker-Breaker position $B = (X, O)$ induces a residual hypergraph $\mathcal{H}(B) = (V_{\text{free}}, E_{\text{alive}})$ where $V_{\text{free}} = [125] \setminus (X \cup O)$ and $E_{\text{alive}}$ are the winning lines with $L_j \cap O = \emptyset$.

In [`qubic5_pillar_solver.cpp`](qubic5_pillar_solver.cpp):
- **Monotone 2-Core Contraction (`peel_from_hyperstate`):** Iteratively strips isolated vertices ($d(v) = 0$) and peels pendant vertices ($d(v) = 1$) via a private twin pair $\{v, u\}$ ($u \in e \setminus \{v\}$), destroying line $e$ without losing Breaker generality.
- **Degree-2 Twins (`peel2_mask`):** Tracks lines with $|L_j \cap V_{\text{red}}| \le 2$ as immediate private pairs inside the 2-core.
- **Fast 48-Symmetry LUT Canonicalization (`canonicalize_hyperstate`):** Uses precomputed byte-lookup tables (`sym_cell_lut[48][16][256]` and `sym_line_lut[48][14][256]`) to canonicalize `HyperState { u128 e_red; u128 v_red; }` across the full octahedral group $O_h$ ($|O_h| = 48$).

### Pillar 2 — Commutative Opening Breaker & Exact Canonical Level-Set DAG
During the first $t_0 = 4$ rounds (Ply 8), Breaker uses the deterministic, $O_h$-covariant policy `commutative_breaker_move`:
1. **Static Priority Order (`pi_order`) with Regular Tetrahedron A/B Splitting:**
   - Center cell `62` $(2,2,2)$ first (`deg = 13`),
   - Followed by **Tetrahedron A** of the inner $3\times 3\times 3$ cube corners (`31, 43, 83, 91`, which are pairwise non-collinear on orthogonal lines so each of the first 4 Breaker moves destroys 6 fresh lines),
   - Followed by **Tetrahedron B** (`93, 81, 41, 33`),
   - Followed by inner face centers, outer corners, and remaining cells sorted by base line degree.
2. **Maximum-Degree Tie-Breaker:** Breaker selects the first free cell $v_k$ in `pi_order` maximizing current residual line degree `cell_deg[v_k] == max_deg`.

### Pillar 3 — Dulmage–Mendelsohn (DM) Safe-Set Extraction & Multi-Probe Null-Move Lifting
When a residual `HyperState` $S$ is not directly certified by a single Coupled Hales–Jewett + Erdős–Selfridge (HJ+ES) pass:
- Rather than branching blindly on all $m = |V_{\text{red}}|$ Maker moves, `run_null_move_probe(S, y_k)` grants Maker a free piece on probe cell $y_k$ and searches for a **1-fault-tolerant Coupled HJ+ES certificate** $(M^*, L_{\text{ES}})$ on $S^{(y_k)}$.
- Using `compute_dm_reachable_mask`, it extracts the exact Dulmage–Mendelsohn $M^*$-alternating reachable set $R_{\text{HK}}$ from unmatched residual vertices $U_0$, together with the 1-fault-tolerant ES-safe cell set $U_{\text{safe}}$ (`verify_coupled_es` checking both $\hat{\Phi}(L_{\text{ES}} \setminus \{j\}) < 32$ and $\hat{\Phi}(L_{\text{ES}}) + \hat{d}(x) < 32 \wedge \text{verify\_coupled\_es}(L_{\text{ES}}, V_{\text{free}} \setminus \{x\})$).
- **Lifting Theorem:** Every sibling Maker move $x \in \mathcal{S}_1(S, y_k) = Z_0 \cup U_{\text{safe}} \cup R_{\text{HK}}$ is simultaneously certified without further search (`y_k` acts as Breaker's immediate response for $x \in U_{\text{safe}}$, and the $M^*$-alternating swap repairs the matching for $x \in R_{\text{HK}}$).
- Intersecting danger sets across up to $R=8$ top-degree probes reduces the remaining active Maker moves to $D_{\text{active}} = \bigcap_{k=1}^R (V_{\text{red}} \setminus \mathcal{S}_1(S, y_k))$.

### Pillar 4 & Pillar 5 — Extended Coupled ES Gadgets, Stabilizer Quotienting & Lock-Free Checkpointed DFS
- **Extended Coupled ES Gadget (`K3_plus`):** Extends the catalog of verified potential-reducing sub-hypergraphs in [`PillarCertificates.v`](PillarCertificates.v) and `compute_es_obj`.
- **Stabilizer Orbit Quotienting & Poset Dominance (`unpruned_hyper_dfs`):** Quotients remaining Maker branches $x \in D_{\text{active}}$ by the stabilizer subgroup $\text{Aut}_{O_h}(S)$ and prunes degree-1 cells dominated by higher-incident cells on the same line.
- **Lock-Free Seqlock Transposition Cache & Persistent Checkpointing:** `HyperTTSlot` ($2^{21}$ entries) caches certified canonical `HyperState`s across all threads, and `save_checkpoint` / `load_checkpoint` periodically persists both completed root certifications and the full transposition cache to disk (`checkpoint.bin`, resumable via `--resume`).

---

## 2. Verified Milestone & Diagnostic Results

Running [`verify.py`](verify.py) executes all three program milestones and the round-by-round diagnostic suite:

### Milestone 1: Ply-8 Canonical HyperState DAG (`--milestone1`)
- **Round $t=1$ (Ply 2):** `10` canonical `HyperState`s (`2-Core Def=[69,81]`, `Violations = 0`, `0.002s`)
- **Round $t=2$ (Ply 4):** `269` canonical `HyperState`s (`2-Core Def=[59,69]`, `Violations = 0`, `0.003s`)
- **Round $t=3$ (Ply 6):** `19,004` canonical `HyperState`s (`2-Core Def=[49,63]`, `Violations = 0`, `0.016s`)
- **Round $t=4$ (Ply 8):** **`726,504`** canonical `HyperState`s (`2-Core Def=[39,57]`, `Violations = 0`, `0.730s`)
  - *Note:* Tetrahedron A/B splitting in `pi_order` reduces the Ply-8 canonical `HyperState` DAG size well below the $1.2\times 10^6$ target (`726,504` vs `1,032,406` without tetrahedral corner ordering).

### Milestone 2: Zero-False-Positive Audit of Pillar 3 DM Null-Move Lifting (`--milestone2`)
- **Certified Null-Move Probes Tested:** `1,000`
- **Total Safe Sibling Bits Verified:** **`67,215`**
- **False Positives Detected:** **`0` (`0.000%`)**
- Every single bit $x \in \mathcal{S}_1(S, y_k)$ across 1,000 certified probes is independently confirmed to have a valid Breaker certificate after Maker plays $x$.

### Milestone 3: End-to-End Subtree Search Benchmark (`--milestone3`)
On 50 uncertified Round $t=9$ (Ply 18) canonical `HyperState` roots (where direct Coupled HJ+ES fails at the root):
| Metric | Baseline (No Pillar 3) | With Pillar 3 DM Lifting | Improvement |
| :--- | ---: | ---: | ---: |
| **Roots Certified (out of 50)** | `50 / 50` | `50 / 50` | `100%` |
| **Total DFS Nodes Visited** | `167` | `107` | **`1.56x` fewer nodes** |
| **Zero-Branch DM Full Cutoffs** | `0` (`0.0%`) | **`29` (`58.0%`)** | **`58%` solved with 0 child branches** |
| **Maker Moves Pruned by DM** | `0` (`0.0%`) | **`5,155` (`57.3%`)** | **`57.3%` sibling moves pruned** |
| **Maker Moves Branched** | `13,010` | **`3,846`** | **`3.38x` reduction in branching** |
| **Checkpoint Save/Reload (`checkpoint.bin`)** | — | `PASS (25/25 roots + TT)` | **Zero lost progress on resume** |

### Round-by-Round Diagnostic (`--diag`, Rounds $t=8..13$)
- **Round $t=8$ (Ply 16):** `Avg |E_red|=60.1`, `Avg Def=11.2`, `DirectCert%=0.0%`, **`ProbeCert%=68.5%`**, `DM Move Prune%=0.8%`
- **Round $t=9$ (Ply 18):** `Avg |E_red|=56.2`, `Avg Def=5.5`, `DirectCert%=2.0%`, **`ProbeCert%=99.5%`**, `DM Move Prune%=25.6%`
- **Round $t=10$ (Ply 20):** `Avg |E_red|=53.1`, `Avg Def=1.3`, `DirectCert%=84.0%`, **`ProbeCert%=99.5%`**, `DM Move Prune%=99.5%`
- **Round $t=11$ (Ply 22):** `Avg |E_red|=47.5`, `Avg Def=-2.5`, `DirectCert%=99.5%`, **`ProbeCert%=99.5%`**, `DM Move Prune%=99.5%`
- **Round $t=12$ (Ply 24):** `Avg |E_red|=43.3`, `Avg Def=-6.2`, `DirectCert%=99.5%`, **`ProbeCert%=100.0%`**, `DM Move Prune%=99.9%`
- **Round $t=13$ (Ply 26):** `Avg |E_red|=37.4`, `Avg Def=-9.8`, `DirectCert%=100.0%`, **`ProbeCert%=100.0%`**, `DM Move Prune%=99.4%`

---

## 3. Rocq 9.1 Formal Verification ([`PillarCertificates.v`](PillarCertificates.v))

[`PillarCertificates.v`](PillarCertificates.v) extends [`research-033/ExactRegionCertificates.v`](../research-033/ExactRegionCertificates.v) and [`research-033/GadgetCatalog.v`](../research-033/GadgetCatalog.v) with four machine-checked theorems (`Closed under the global context`, 0 axioms):
1. `K3_plus_verified : verify_gadgetb gadget_K3_plus = true` — Formal verification of the 4-fragment, 7-cell `K3_plus` Coupled ES gadget (3 triangle fragments of size 3 at cells `(0,1,2)`, `(2,3,4)`, `(4,5,0)` plus 1 pendant fragment `(0,6)` of size 3, safely absorbing Maker hits with post-response potential $\le 16 < 20$).
2. `K3_333_exact_u_safe_classification` — Proves the exact boundary between 1-fault-tolerant safe cells (`u_safeb = true` on degree-1 vertices `1, 3, 5`) and shared triangle corners (`u_safeb = false` on degree-2 vertices `0, 2, 4`) in the 3-line $(3,3,3)$ triangle `frags_K3_333`, matching the exact condition in `verify_coupled_es` that saved Milestone 2 from false positives.
3. `K4_ext_all_vertices_1fault_safe` — Proves that in the 4-line $(4,4,4,4)$ clique `frags_K4_ext`, every vertex $x \in \{0..9\}$ satisfies `u_safeb frags_K4_ext 32 x = true` (1-fault-tolerant Coupled ES safety).
4. `u_safeb_sound` — Proves the general Pillar 3 Null-Move Lifting soundness theorem for `u_safeb`: for any ES region $F$, budget $B$, and cell $x$ with `u_safeb F B x = true`, removing $x$ from the free set preserves the Coupled ES potential invariant (`region_potential (hit_region F x) <= B` and `hit_region_survivesb F x = true`), certifying that the probe cell $y_k$ serves as a valid immediate Breaker response whenever Maker plays $x \in U_{\text{safe}}$.

---

## 4. Reproduction

Run the standalone verification script from the repository root:

```powershell
python -u research-034/verify.py --rocq "C:\Rocq-Platform~9.1~2026.01\bin\rocq.exe"
```

Or run the C++20 solver directly with any combination of flags (`--milestone1`, `--milestone2`, `--milestone3`, `--diag`, `--checkpoint <file>`, `--resume`):

```powershell
g++ -O3 -march=native -fopenmp -std=c++20 research-034/qubic5_pillar_solver.cpp -o research-034/qubic5_pillar_solver.exe
.\research-034\qubic5_pillar_solver.exe --milestone1 --milestone2 --milestone3 --diag
```
