# research-033: Rocq 9.1 Formalization & Audit of Qubic 5x5x5 Handoffs

Formalizes the finite-state region-gadget pairing-and-reserve calculus in **Rocq 9.1** against the unchanged `QUBIC-PROOF-GATE-001/trusted/Rules.v` specification (`0` axioms, `0` admits), and reproduces/refutes key claims from `5x5x5_QUBIC_HandOff.md` and `5x5x5_QUBIC_HandOff_b.md`.

## Verified Rocq Modules

1. **[ExactRegionCertificates.v](ExactRegionCertificates.v)**
   - Implements bitmask (`N`) line fragments, line weights/potential (`phi`, `gain`), safe regions (`region_safe`, `region_safeb`), gadget compatibility (`gadget_compatb`), and the precomputed certificate checker `hybrid_certificateb`.
   - **`hybrid_certificate_nonloss`**: Proves (`Print Assumptions` -> `Closed under the global context`) that from any reachable `valid_state st0`, if `hybrid_certificateb reg asg gs st0 = true`, then `hybrid_policy reg asg gs` guarantees Black never loses (`outcome (step_game n true st0 w (hybrid_policy reg asg gs)) <> WhiteWins`).

2. **[GadgetCatalog.v](GadgetCatalog.v)**
   - **`K4_no_es_lt16_partition`**: Exhaustive proof (`Closed under the global context`) that no partition of the 16 off-center cells of a planar/diagonal 5x5 slice satisfies `e <= 1` per region without crossing a collinear `K_4`.
   - **`Slice14_verified` & `Slice14_sub_phi_28`**: Verifies `gadget_Slice14` (`verify_gadgetb gadget_Slice14 = true`, `Closed under the global context`) with sub-potential `sub_phi (gs_frags gadget_Slice14) 0%N 0%N = 28`.

3. **[PackingAndWitnesses.v](PackingAndWitnesses.v)** (all 5 theorem groups verified `Closed under the global context`)
   - **Refutation of 7-Slice14 `13/27` packing (`5x5x5_QUBIC_HandOff_b.md`)**:
     - **`pack7_max_residual_pairs_le_9`**: Any residual pairing inside the remaining 27 cells outside 7 disjoint planar `Slice14` gadgets can match at most `9` alive lines (strictly below `13`).
     - **`pack7_uncoordinated_z_slice_loses`**: Explicit 5-move White strategy `w_col0` (`[0; 25; 50; 75; 100]`) forces `WhiteWins` against uncoordinated z-slice defense.
   - **Refutation of unconditional `Phi < 1` (`phi < 32`) soundness (`5x5x5_QUBIC_HandOff.md`)**:
     - **`cex54_valid`, `cex54_props`, `phi_lt_32_unsound`**: Exhibits a reachable quiet 54-ply position `st_cex54` with `phi (fun _ => 0) (fun _ => 0) st_cex54 0 = 16` (`< 32`) from which White (`w_fork54`) forces `WhiteWins`.
   - **Verified Midgame Non-Loss Separation Beyond `ValidPairing`**:
     - **`w26_pairing_impossible` & `res032_id0_ply26_nonloss`** (`res032/mb_equal.jsonl`, `id=0`, ply `26`): `50` alive lines vs `99` empty cells (`ValidPairing` impossible), yet `hybrid_policy` proves non-loss across all `99` remaining plies.
     - **`w24_pairing_impossible` & `res029_id15_ply24_nonloss`** (`res029/games_cert.jsonl`, `id=15`, ply `24`): `55` alive lines vs `101` empty cells (`ValidPairing` impossible), yet `hybrid_policy` proves non-loss across all `101` remaining plies.

## Verification

Run the trusted gate check and compile all three modules with real-time progress and Windows-safe process-tree timeout handling:

```bash
python -u research-033/verify.py --rocq "C:\Rocq-Platform~9.1~2026.01\bin\rocq.exe"
```

## Resumption Notes & Integration with the 5-Pillar Research Program (`mathematical_research_program_for_settling_5x5x5_qubic.md`)

`research-033` provides the kernel-checked leaf certificate engine (`ExactRegionCertificates.v`, `GadgetCatalog.v`) and formal refutations/witnesses (`PackingAndWitnesses.v`). Combining `research-033` with the five reductions in `../mathematical_research_program_for_settling_5x5x5_qubic.md` yields a unified roadmap for closing the Ply 0 $\to$ Ply 14 frontier:

1. **Pillar 1 — Exact 2-Core Hypergraph Quotienting `(E_red, V_red)` + $O_h$ Canonicalization:**
   - Iteratively peeling alive lines with $\ge 2$ degree-1 empty cells into isolated 2-cell pairs (`R_pair`) is confluent and yields the exact identity $\text{mc}(j) = 5 - |l_j \cap V_{\text{red}}|$ for all surviving $j \in E_{\text{red}}$, erasing dead stones and move-order history.
   - *Rocq Lifting Requirement:* In the full `Rules.v` game, Maker can still play outside $V_{\text{red}}$ (into peeled degree-1 pairs or degree-0 dead cells). The `hybrid_policy` wrapper in `ExactRegionCertificates.v` already handles local pair responses (`R_pair`) without disturbing the residual hypergraph $(E_{\text{red}}, V_{\text{red}})$.
2. **Pillar 2 — Commutative Core-Schedule Policy $B_\pi$:**
   - Using a canonical static priority list $\pi$ (center $62$, inner-cube corners $\{1,3\}^3$, inner face-centers/outer corners) makes Breaker's quiet responses history-independent, collapsing $t!$ Maker move permutations into a single canonical `(E_red, V_red)` state.
   - Because Breaker is existentially quantified ($\exists y$), restricting Breaker to $B_\pi$ (and $K \le 4$ null-move probes) is 100% sound.
3. **Pillar 3 — Multi-Probe Null-Move Witness Lifting (Dulmage–Mendelsohn + Coupled ES Slack):**
   - Directly resolves the `phi_lt_32_unsound` counterexample (`st_cex54`): whereas uncoupled $\Phi < 32$ at Maker's turn fails on `st_cex54` ($\Phi = 16$, $\max_z \hat{d}(z) = 16$, sum $32 > 31$), the Coupled ES condition $\delta_k = 31 - (\hat{\Phi}(L_{\text{ES}}) + \max_{z \in V_{\text{free}}} \hat{d}(z)) \ge 0$ (matching the one-step lookahead in `hybrid_certificateb`) rejects `st_cex54` ($\delta_k = -1$) and guarantees that every $x \in U_{\text{safe}}$ with $2\hat{d}(x) \le \delta_k$ preserves $\hat{\Phi}' + \max_z \hat{d}' \le 31$.
   - Note that line weights $w(l) = 32 \cdot 2^{-|l \cap V_{\text{free}}|}$ must be computed strictly from remaining free cells in $V_{\text{free}}$ (not raw global stone counts when cells of $l$ are locked inside $M_{\text{HK}} \cup M_{\text{gad}}$), matching `ExactRegionCertificates.v`'s restricted fragment semantics.
   - Furthermore, the Dulmage–Mendelsohn reverse BFS from $U_{\text{safe}}$ over $(L_{\text{pair}}, M_{\text{HK}} \cup U_{\text{safe}})$ constructively exhibits the flipped 2-matching $M'_{\text{HK}} = (M_{\text{HK}} \setminus \{x\}) \cup \{u\}$ for every $x \in R_{\text{HK}}$, allowing sibling certificates to be verified in Rocq without re-running Hopcroft–Karp.
4. **Pillar 4 — Automorphism Orbits, Degree-1 Poset Dominance, and Disjoint Component Quotienting:**
   - Certified connected components $C_q$ are closed regional traps (`hybrid_certificate_nonloss`), so Maker moves inside $V(C_q)$ are answered locally inside $V(C_q)$ and never affect uncertified components.
5. **Pillar 5 — Breadth-First Canonical Hypergraph DAG (Plies 2–10) + Multi-Probe DFS to Closure:**
   - Next step (`research-034`): implement Milestones 1–3 of the C/C++ `(E_red, V_red)` + Multi-Probe DM solver (with real-time progress reporting and checkpointing per `AGENTS.md`) and export its DAG/certificates to `ExactRegionCertificates.v`.

