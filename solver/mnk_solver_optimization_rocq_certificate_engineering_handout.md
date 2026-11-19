# Engineering & Mathematical Specification: High-Performance $(m, n, k)$-Game Draw Prover and Rocq Certificate Pipeline

**Document Purpose:** Self-contained technical handout and implementation blueprint for an autonomous coding agent.  
**Target Codebase:** `mnk_prover.c` (CPU AND/OR & df-pn solver) and `mnk_proof.cu` (CUDA level-synchronous greedy prover/verifier).  
**Target Formal System:** Rocq (formerly Coq), connecting to existing formalizations `MNKStrategyStealing.v` (`mnk_value_win_or_draw`) and `MNKErdosSelfridge.v` (`es_inv`).  
**Target Hardware:** 24-thread x86-64 CPU (AVX2/BMI2), 32 GB host RAM, 8 GB RTX GPU (`sm_89`, CUDA 12.x under WSL2/WDDM).

---

## 1. Mission, Architecture & Design Invariants

### 1.1 Mathematical Objective
By the already-formalized strategy-stealing theorem (`mnk_value_win_or_draw`), every $(m, n, k)$-game is either a first-player (P1) win or a draw. Proving a draw therefore reduces to proving:

$$\text{"P1 (Maker) cannot force a win from the empty board."}$$

This proof is an **AND/OR DAG** over canonical board states:
- **P1-to-move (Maker) nodes are AND nodes:** every legal/relevant P1 move must be refuted.
- **P2-to-move (Breaker) nodes are OR nodes:** a single sound P2 reply (or leaf certificate) suffices.

### 1.2 Strict Separation: Untrusted Solver vs. Minimal Trusted Rocq Kernel
The coding agent **must** maintain a strict trust boundary:
1. **Untrusted Solver (`mnk_prover.c` / `mnk_proof.cu`):** Free to use aggressive heuristics, df-pn, transposition tables, lock-free concurrency, VCT disproof search, and SIMD/CUDA bit tricks.
2. **Constructive Proof Certificate (`.mnkcert`):** When the solver proves the root, it extracts a compact, topologically sorted DAG of **explicit witnesses** (leaf pairing strategies, ES inequalities, component decompositions, relevance-zone masks, and OR-node reply edges).
3. **Trusted Checker (Standalone C Verifier $\to$ Rocq `native_compute` + `PrimInt63`):** Independently checks every witness locally in $O(1)$ per node without running any search, matching algorithm, or transposition table.

**Corollary for Soundness:** Any pruning rule that discards *disproved* OR branches (such as VCT) never enters the certificate and cannot compromise formal soundness. Any pruning rule that eliminates *AND* branches (such as relevance zones, twin pairs, dominance, or component restriction) **must** emit a machine-checkable witness.

### 1.3 Quantitative Target
The current GPU greedy prover solves $(7,7,5)$ with $1.68 \times 10^9$ P1 nodes in $946\text{ s}$. Published AND/OR solvers using pairings and relevance zones solve $(7,7,5)$ in $\sim 2.5\text{ s}$ and $(8,8,5)$ in $\sim 17\text{ h}$. Closing this gap requires:
- **$10^3\times$--$10^4\times$ reduction in proof DAG size** (algorithmic/mathematical upgrades in Section 3 & Section 4), enabling $(7,7,5)$ proofs of $\sim 10^4$--$10^6$ nodes that fit inside Rocq's `native_compute`.
- **$10\times$--$50\times$ increase in node throughput** (CPU microarchitecture, 24-thread parallelism, and CUDA memory/warp fixes in Section 5 & Section 6).

---

## 2. Codebase Audit & Bottleneck Inventory

| Subsystem | File & Location | Current Defect / Bottleneck | Impact | Target Replacement |
|---|---|---|---|---|
| AND branching | `mnk_prover.c`: `evaluate_maker_to_move`, `dfpn_mid` | Every undominated Maker move in unsafe components is searched independently | $10\times$--$1000\times$ excess proof nodes | Constructive **Relevance Zones** + Null-Move Probe |
| Hypergraph reduction | `mnk_prover.c`: `hypergraph_build`, `undominated_moves` | $O(n^2)$ subsumption over all live lines; mutually dominating twins are only pruned from move list, not paired | High per-node cost; missed instant pairings | $O(n)$ **Collinear Subsumption** + **Fixed-Point Twin-Pair Elimination** |
| Safety test order | `mnk_prover.c`: `component_is_safe`, `pair_cover_safe` | Backtracking `pair_cover_safe` (budget $4000 \times (k-1)$) runs *before* $O(kn)$ `greedy_hybrid_safe`; no abort on 2-line conflicts | Massive wasted recursion on Breaker nodes | Reorder greedy before exact; instant abort if `double_threat_cells != 0`; unit propagation |
| Breaker-first leaf | `mnk_prover.c`: `evaluate_breaker_to_move` | Only tests global $\phi < 2^k$ | Misses immediate 1-ply ES/matching leaves | **1-ply Breaker lookahead** on top 1--2 cells of the single unsafe component |
| Disproof speed | `mnk_prover.c`: `evaluate_maker_to_move` | Only catches 1-ply wins and 2-ply double threats | Wastes df-pn nodes refuting forced Maker wins | Lightweight **Bitboard VCT** (depth 6--8) |
| df-pn search | `mnk_prover.c`: `initial_numbers`, `dfpn_mid` | Pure mobility init; no $1+\varepsilon$ threshold; eager `child_state` for all moves; double `evaluate()` per descent | $20\times$--$40\times$ extra nodes + thrashing | Heuristic PN/DN init; $1+\varepsilon$ ($\varepsilon = 0.25$); lazy child canonicalization; local `child_pn[]` |
| CPU concurrency | `mnk_prover.c`: whole file | Single-threaded on 24-thread CPU; uses `clock()` (sums CPU time) | $10\times$--$18\times$ unused compute | 24-thread parallel df-pn with striped 64B TT + virtual loss + thread-local stats + `CLOCK_MONOTONIC` |
| Symmetry cache | `mnk_prover.c`: `board.symmetry_table[8][8][256]` | 128 KB table exceeds L1d cache; transforms both bitboards even when `maker` loses | Severe L1d misses per child | 16 KB nibble table (or register-only SWAR $D_4$) + early exit on `maker_t > best.maker` |
| Live-line scan & Kuhn | `mnk_prover.c`: `hypergraph_build`, `has_two_matching` | Scalar loop over all lines; recursive Kuhn without greedy bitmask pre-match | Hot inner loop overhead | AVX2 4-wide line filter + bitmask `matched_cells` greedy pre-match |
| CUDA VRAM & spills | `mnk_proof.cu`: `GreedyProofPass`, `expand_level`, `p2_node` | Pass 1 peaks $\sim 7$--$8\text{ GB}$ on 8 GB WDDM GPU (5x PCIe paging slowdown); `uint64_t[64]` weight arrays spill 1.5 KB/thread to local memory | $5\times$ Pass-1 stall + severe stack traffic | `uint16_t`/`uint32_t` weights; warp compaction (drops 400 MB `lost_p2_` and `thrust::remove_if`) |
| CUDA atomics & sort | `mnk_proof.cu`: `expand_level`, `p2_node`, `sort_unique_device` | 5 random 64-bit Bloom atomics/node; rescans all lines per candidate in `p2_node`; `thrust::sort` comparison sort | Bandwidth & divergence bottleneck | Word-blocked 1-atomic Bloom; pre-extracted $(k-2)$-lines; CUB bit-bounded radix sort |

---

## 3. Part I: Mathematical & Game-Theoretic Specifications (`mnk_prover.c`)

### 3.1 Constructive Relevance Zones (Proof-Driven AND-Node Pruning)

#### 3.1.1 Definition and Monotonicity Lemma
Let $Q = (M, B)$ be a board state (Maker stones $M$, Breaker stones $B$, free cells $F = \text{All} \setminus (M \cup B)$). Suppose $T$ is a winning Breaker strategy tree proving that P1 cannot force a win from $Q$ (with Maker to move). Its **relevance zone** $Z(T) \subseteq F$ is a subset of free cells satisfying the invariant:

$$\forall\, m \in F \setminus Z(T),\quad T \text{ remains a valid winning Breaker strategy from } (M \cup \{m\},\, B).$$

**Proof of Invariant (by structural induction on $T$):**
Adding a Maker stone $m \notin Z(T)$ cannot interfere with any cell read, paired, weighted, or played by $T$:
1. **Board full (`LEAF_FULL`):** $Z = \emptyset$.
2. **Maker-first ES leaf (`LEAF_ES_MAKER`):** Let $\mathcal{L}$ be the unsubsumed live Maker lines at $Q$. Define:
   $$Z = \bigcup_{L \in \mathcal{L}} F(L).$$
   If $m \notin Z$, then $m$ lies on no live line in $\mathcal{L}$ (and by subsumption, any subsumed live line $L' \supseteq L$ is still blocked whenever $L$ is blocked), so Maker's potential $\phi$ and weights $w(x)$ on $\mathcal{L}$ are completely unchanged.
3. **Disjoint Pair Cover / 2-Matching leaf (`LEAF_PAIRS`):** Let $P = \{\{u_1, v_1\}, \dots, \{u_r, v_r\}\}$ be pairwise disjoint pairs of free cells such that every live Maker line contains at least one pair $\{u_i, v_i\} \in P$. Define:
   $$Z = \bigcup_{i=1}^{r} \{u_i, v_i\}.$$
   *Crucial gain:* Free cells on live lines that are **not** part of any chosen pair are **excluded** from $Z$. Even if Maker plays on them, every live line still contains an intact Breaker pair.
4. **Pairs + ES Hybrid leaf (`LEAF_PAIRS_ES`):** Let $P$ be the disjoint pairs with cell set $C_P = \bigcup P$, and let $\mathcal{U}$ be the live lines containing no pair in $P$. The leaf holds because Maker-first ES holds on $\{F(L) \setminus C_P : L \in \mathcal{U}\}$. Define:
   $$Z = C_P \cup \bigcup_{L \in \mathcal{U}} (F(L) \setminus C_P).$$
5. **Component Decomposition (`LEAF_COMPONENTS`):** If the unsubsumed hypergraph decomposes into vertex-disjoint components $C_1, \dots, C_s$ with individual winning strategies $T_1, \dots, T_s$, define:
   $$Z = \bigcup_{j=1}^{s} Z(T_j).$$
6. **Breaker-first ES leaf (`LEAF_ES_BREAKER` at a P2-to-move node):** $\phi < 2^k$ on unsubsumed live lines $\mathcal{L}$. Define $Z = \bigcup_{L \in \mathcal{L}} F(L)$.
7. **P2-to-move Internal OR node (`INTERNAL_P2_OR`):** Breaker plays $b \in F$, transitioning to Maker-to-move state $Q' = (M, B \cup \{b\})$ proved by $T'$. Define:
   $$Z = \{b\} \cup Z(T').$$
   (Breaker must still be able to play $b$, so $m \neq b$ is required.)
8. **P1-to-move Internal AND node (`INTERNAL_P1_AND`):** Suppose Maker moves $m_1, \dots, m_d$ are refuted by OR-subtrees $T_1, \dots, T_d$ (covering all relevant moves). Define:
   $$Z = \bigcup_{j=1}^{d} Z(T_j).$$
   *(Note: if a P1 move $m_j$ is refuted by $T_j$, and $m_j$ was forced to be covered because it lay inside a previously computed zone, $m_j$ itself does not need to be added unless a sibling relied on $m_j$ being free—see Section 3.1.2.)*
9. **Strong-Game Extension (`RULES_STRONG`):**
   - If a P2-to-move leaf wins immediately because P2 completes line $L^*$ (`P2_WIN`), then $Z = F(L^*)$ (the single completion cell needed by P2).
   - If a P1-to-move node is proved because P2 has two distinct completion cells $\{c_1, c_2\}$ (`P2_DOUBLE_THREAT`), then $Z = \{c_1, c_2\}$.
   - If a P1-to-move node has a single forced block $c_1$ against P2's threat, then P1 *must* play $c_1$ (proved by $T_1$), so $Z = \{c_1\} \cup Z(T_1)$ (P1 must not already occupy $c_1$? Actually if P1 already had $c_1$, the P2 threat would be dead—so adding $c_1$ to $Z$ is always sound and keeps the Strong-Game induction completely airtight!).
   - **Rule:** Never omit a cell that a P2 winning line or P2 threat relies on from $Z$ in `RULES_STRONG`.

#### 3.1.2 Exact Sibling Pruning Algorithm at Maker (AND) Nodes
At an AND node $P = (M, B)$ (Maker to move) with candidate move set $C$:
1. Suppose we prove Maker move $m_0 \in C$: that is, Breaker has a reply $b_0$ and winning strategy $T_0$ proving $(M \cup \{m_0\},\, B \cup \{b_0\})$ with relevance zone $Z_0 = Z(T_0)$.
2. **Wait—critical soundness check!** In `RULES_MAKER_BREAKER`, removing Maker's stone $m_0$ from $(M \cup \{m_0\},\, B \cup \{b_0\})$ can **only help Breaker** (every Maker line has strictly fewer or equal Maker stones, every pair remains intact, every ES weight shrinks or stays equal). Therefore, $T_0$ also proves $(M,\, B \cup \{b_0\})$ with the **exact same** relevance zone $Z_0$!
   - **Warning for `RULES_STRONG`:** Removing Maker's stone $m_0$ also cannot hurt P2's lines—in fact, freeing $m_0$ can only *unblock* P2 lines. So removing $m_0$ is **also sound in `RULES_STRONG`**, provided $T_0$ did not depend on $m_0$ being occupied (which no Breaker strategy ever does—it only requires cells in $Z_0$ to be free of Maker stones).
3. Consequently, for **every** sibling move $m \in C \setminus (Z_0 \cup \{b_0\})$:
   - Placing Maker stone $m$ on $(M,\, B \cup \{b_0\})$ does not touch $Z_0$, so Breaker replying with $b_0$ and playing $T_0$ refutes $m$ immediately!
4. **Action:** Maintain a bitboard `remaining_moves` initialized to all candidate Maker moves at $P$.
   - Whenever any child $m_i$ is proved with OR-zone $Z_{\text{or}}(m_i) = \{b_i\} \cup Z(T_i)$:
     - **Important symmetry un-mapping:** Since child states are canonicalized via symmetry $t_i$, the zone stored in the TT is in the *child's* canonical coordinates. You **must** apply $t_i^{-1}$ to map $Z_{\text{or}}$ back into parent $P$'s coordinates before intersecting!
     - Let $R_i = t_i^{-1}(Z_{\text{or}}(m_i))$.
     - Immediately prune all siblings outside $R_i$:
       ```c
       remaining_moves &= R_i;
       remaining_moves &= ~cell_bit(m_i);
       ```
     - Record $(m_i, b_i, R_i)$ as the *covering refutation* for every pruned sibling (in the certificate, one "default refutation" $(b_0, T_0, R_0)$ covers all $m \notin R_0$, and only moves inside $R_0$ require explicit child pointers!).
   - When `remaining_moves == 0`, the AND node $P$ is **PROVED**, and its own relevance zone is:
     $$Z(P) = \bigcup_{j \text{ actually used}} R_j.$$

#### 3.1.3 Optional Null-Move Probe at High-Branching AND Nodes
At Maker-to-move nodes with $|C| \ge 8$ and no forced moves:
- Before expanding Maker moves, test the best Breaker reply $b^*$ on $(M,\, B \cup \{b^*\})$ via fast leaf evaluation (`evaluate_maker_to_move` without search, or a shallow probe).
- If $(M,\, B \cup \{b^*\})$ is immediately proved as a leaf with zone $Z^*$, then `remaining_moves` immediately collapses from $|C|$ down to $C \cap (Z^* \cup \{b^*\})$ at **zero search cost**!

---

### 3.2 Fixed-Point Hypergraph Reduction: Collinear $O(n)$ Subsumption + Twin-Pair Elimination

#### 3.2.1 Collinear $O(n)$ Subsumption
**Theorem:** On any 2D $(m, n, k)$ grid, two distinct lines $L_1, L_2$ that are not collinear intersect in at most $1$ cell: $|L_1 \cap L_2| \le 1$. Therefore, if $|F(L_1)| \ge 2$, then $F(L_1) \subseteq F(L_2)$ implies $L_1$ and $L_2$ are collinear.

**Implementation Specification:**
1. In `board_init()`, precompute for every line $i \in \{0, \dots, \text{line\_count}-1\}$:
   ```c
   uint8_t  collinear_count[MAX_LINES];
   uint16_t collinear_nbr[MAX_LINES][MAX_COLLINEAR]; /* MAX_COLLINEAR = 2 * (MAX_K - 1) */
   ```
   Two lines $i \neq j$ are collinear neighbors iff `popcount(board.line[i] & board.line[j]) >= 2`. (For $k=5$, every line has at most $2(k-2) = 6$ neighbors.)
2. In `hypergraph_build(p, h)`:
   - Pass 1 (AVX2-accelerated, Section 5.2): Extract all live lines (`(line[i] & p.breaker) == 0`), storing `free_mask[i] = line[i] & ~occupied` and `free_cnt[i] = popcount(free_mask[i])` in a dense array indexed by original board line ID `i`, plus a compact list `live_ids[0..n-1]`.
   - Early exit: If any live line has `free_cnt[i] == 0` (immediate Maker win already on board) or `free_cnt[i] == 1` (threat), track `threats |= free_mask[i]` right here.
   - Pass 2 (Subsumption, only if `options.subsumption`): For each live line `id = live_ids[idx]` with `free_cnt[id] >= 2`:
     - Loop `q = 0 .. collinear_count[id] - 1`, `nb = collinear_nbr[id][q]`.
     - If `nb` is live and `(free_mask[nb] & ~free_mask[id]) == 0`:
       - If `free_cnt[nb] < free_cnt[id]` OR (`free_cnt[nb] == free_cnt[id]` AND `nb < id`), mark `id` as subsumed and break.
   - Complexity drops from $O(n^2)$ (~3,600--9,000 iterations) to $O(n \cdot 2(k-2))$ (~150--300 bit ops).

#### 3.2.2 Exact Fixed-Point Twin-Pair Elimination
In `RULES_MAKER_BREAKER` (and for Breaker-safe component analysis in both rule sets):
- Let $E(c)$ be the set of live unsubsumed Maker lines passing through free cell $c$.
- If two distinct free cells $u, v$ satisfy $E(u) = E(v) \neq \emptyset$ (mutually dominating **twins**), then $\{u, v\}$ is an **exact unconditional pairing**:
  - If Maker takes $u$, Breaker takes $v$ (and vice versa), killing all lines in $E(u)$ while touching zero other live lines.
- **Fixed-Point Loop (inside `analyse()` before component splitting or inside each component):**
  ```text
  twin_pairs = []
  loop:
      1. Compute E(c) for all active free cells c.
      2. Find disjoint twin pairs {u, v} with E(u) == E(v) != empty.
         (Use a fast 64-bit hash of E(c) or sort cells by E(c) to find twins in O(m log m).)
      3. If no twin pair found: break.
      4. Record {u, v} into twin_pairs.
      5. Delete all lines in E(u) and remove {u, v} from active cells.
      6. (Optional) Re-check collinear subsumption on remaining lines.
  ```
- **Relevance Zone & Certificate Accounting:**
  - Every extracted twin pair $\{u, v\}$ is prepended to the node's pairing witness and adds $\{u, v\}$ to the node's relevance zone $Z$.
  - If deleting twin pairs empties the component ($n = 0$), the component is immediately **SAFE** (`LEAF_PAIRS`) without running ES, Kuhn, or backtracking!
  - Even if lines remain, deleting $E(u)$ frequently splits the remaining hypergraph into disconnected components or drops $\phi + \max w < 2^k$.

---

### 3.3 Leaf-Test Pipeline Fixes, Unit Propagation & VCT Disproofs

#### 3.3.1 Fix `component_is_safe()` Evaluation Order
In current `mnk_prover.c`, `pair_cover_safe()` runs before `greedy_hybrid_safe()`. Reverse this strictly:
```c
static bool component_is_safe(const Component* comp, Witness* w, uint64_t* potential_out)
{
    if (es_maker_first(comp, potential_out))               return true;  /* O(n) */
    if (options.matching && has_two_matching(comp, w))     return true;  /* O(n * cells) bitmask */
    if (options.greedy_hybrid && greedy_hybrid_safe(comp, w)) return true; /* O(k * n) */
    if (options.pair_cover && pair_cover_safe(comp, w))    return true;  /* bounded backtrack */
    return false;
}
```
*Note:* Make `has_two_matching`, `greedy_hybrid_safe`, and `pair_cover_safe` populate a lightweight `Witness` struct (the chosen `PairSet` + uncovered cells) so Relevance Zones and Rocq certificates receive the exact witness for free.

#### 3.3.2 Instant 2-Line Conflict Abort & Unit Propagation in `pair_cover_safe()`
- Every `hot` iteration ($2 \le \text{hot} \le k$) must cover all lines with `sizes[i] == 2`.
- Any 2-cell line $\{u, v\}$ forces the pair $\{u, v\}$.
- **Pre-check before entering `pair_cover_safe`:** If `double_threat_cells(comp) != 0`, two size-2 lines share a cell, so **no disjoint pair cover can exist for any `hot >= 2`**. Return `false` in $O(n)$ without burning $4000 \times (k-1)$ recursion nodes.
- **Unit propagation inside `cover_recurse()`:** Before branching on `best_line`, run a flat `while` loop: whenever any uncovered required line has `free_left == 2`, immediately force its unique pair `{u, v}`, mark all lines containing `{u, v}` covered, and check for conflicts (`free_left < 2`). Only branch when every remaining uncovered required line has `free_left >= 3`.

#### 3.3.3 1-Ply Breaker-First ES / Matching Lookahead
In `evaluate_breaker_to_move()`, when `a.unsafe_components == 1` and `a.breaker_first_fix` ($\phi < 2^k$) is false:
- Identify the top 2 highest-weight free cells $b_1, b_2$ in the single unsafe component.
- For each $b \in \{b_1, b_2\}$: remove all lines through $b$ from the unsafe component and test `es_maker_first` (and `has_two_matching` if enabled).
- If safe, return `STATUS_PROVED` immediately, recording `best_move = b` and relevance zone $Z = \{b\} \cup Z(\text{safe leaf}) \cup Z(\text{other safe components})$.
- This is strictly stronger than $\phi < 2^k$ (the exact refinement already used in `mnk_proof.cu`'s `ExactSolver`) and prunes an entire ply of OR nodes.

#### 3.3.4 Bitboard VCT (Victory by Continuous Threats) for Fast Disproofs
In `evaluate_maker_to_move()` (when `forced == 0` and no immediate win/double-threat exists):
- Run a tiny depth-limited (depth $\le 6$ or $\le 8$, node budget $\le 64$) iterative Maker threat-sequence search:
  1. Maker plays $u$ on any live Maker line with `free_count == 2` (creating a 1-cell threat at partner $v$).
  2. In `RULES_STRONG`, check that $v$ does not complete a P2 line; if it does, discard $u$.
  3. Breaker is forced to play $v$.
  4. Recurse on $(M \cup \{u\},\, B \cup \{v\})$: if Maker now has a double threat (or a 1-cell completion not blocked by $v$), return `STATUS_DISPROVED`!
- **Soundness:** VCT only returns `STATUS_DISPROVED` (P1 wins). In `RULES_STRONG`, ensure Breaker cannot win on $v$ or create a counter-threat before returning `STATUS_DISPROVED` (actually, in `RULES_STRONG` even a false `DISPROVED` only causes an OR node to skip a bad P2 move—it can **never** produce a false `PROVED` draw!). Still, checking `!completes_p2_line(v)` keeps strong-game search sharp.
- VCT never touches `PROVED` states and requires zero Rocq formalization.

---

## 4. Part II: Search Engine Architecture (`mnk_prover.c`)

### 4.1 Heuristic PN/DN Initialization
Replace uniform mobility initialization in `initial_numbers()` with potential-informed initialization from the already-computed `Analysis a`:
- Compute excess potential $\Delta = \max(0,\, \phi_{\text{unsafe}} - 2^k + 1)$ and `max_w` $= \max_{c \in \text{unsafe}} w[c]$.
- Let $h_{\text{es}} = \min\!\big(64,\; 1 + \lfloor \Delta / \max(1, \text{max\_w}) \rfloor\big)$ be an estimate of how many Breaker moves are needed to push the unsafe part below $2^k$.
- **Maker to move (AND node):**
  - `proof = clamp(moves.count * max(1, a.unsafe_components), 1, 256)` (or weighted by $h_{\text{es}}$).
  - `disproof = (has_two_line ? 1 : 2)` (favors exploring disproofs where Maker already has 2-lines).
- **Breaker to move (OR node):**
  - `proof = clamp(a.unsafe_components + h_es - 1, 1, 128)`.
  - `disproof = clamp(moves.count, 1, 256)`.

*(Benchmark against mobility init on $(7,4,4)$ and $(8,4,4)$ using an ablation flag so the coding agent can verify node reduction empirically.)*

### 4.2 $1 + \varepsilon$ Thresholding in `dfpn_mid`
Standard df-pn thrashes between `best` and `second` on every $+1$ step. Modify child threshold calculation to use Pawlewicz & Lew's $1 + \varepsilon$ rule ($\varepsilon = 0.25$ via bit-shift):

```c
static inline uint32_t pn_add_eps(uint32_t second)
{
    if (second >= PN_INFINITY) return PN_INFINITY;
    uint32_t bump = (second >> 2) + 1; /* 1.25 * second + 1 */
    return pn_add(second, bump);
}
```
Use `pn_min(disproof_threshold, pn_add_eps(second))` at AND nodes and `pn_min(proof_threshold, pn_add_eps(second))` at OR nodes.

### 4.3 Eliminating Double `evaluate()` and Eager `child_state()`
Fix two structural inefficiencies in `dfpn_mid()`:
1. **Lazy child generation:** Do not compute `child[0..moves.count-1]` before entering the `for (;;)` loop. Initialize `bool child_ready[MAX_CELLS] = {false};` and compute `child[i] = child_state(...)` (also storing the canonicalizing symmetry `child_sym[i]` for Relevance Zone un-mapping!) only the first time index `i` is accessed. If `child[0]` immediately solves the node (`proof == 0` at OR or `disproof == 0` at AND), $N-1$ canonicalizations are skipped completely.
2. **Local `child_pn[MAX_CELLS]` cache + Relevance-Zone bitmask:** Store each evaluated child's last known `ProofNumbers` locally on the stack of `dfpn_mid`. On subsequent iterations of the `for (;;)` loop:
   - Re-check the TT only for `best_index` (and optionally refresh other children on TT hits without calling `evaluate()` on a TT miss—fall back to `child_pn[i]`!).
   - Maintain `Bitboard active_mask` at AND nodes. Whenever a child `i` returns `PROVED`, fetch its `relevance` bitboard from the TT, apply `inv_sym[child_sym[i]]`, and immediately mask out all siblings outside `R_i` from `active_mask`!
3. **Protect `PROVED` entries from TT eviction:** In `tt_store()`, **never** evict a `PROVED` entry in favor of an `OPEN` entry if any `OPEN` (or empty) slot exists in the bucket. `PROVED` entries carry exact relevance zones and form the final Rocq proof DAG; evicting them forces redundant sub-proofs.

### 4.4 24-Thread Parallel df-pn
Convert `mnk_prover.c` from single-threaded to 24-thread OpenMP parallel df-pn:
1. **Wall-clock timer:** Replace `clock()` with `clock_gettime(CLOCK_MONOTONIC, &ts)`.
2. **Thread-local statistics:** Replace global `static Statistics stats;` with `ThreadLocalStats` (padded to 64 bytes per thread to prevent false sharing). Merge at end of search and poll time limit every 4,096 calls per thread.
3. **Striped Cache-Line Lock / Seqlock Shared TT:**
   - Use a 2-way bucket of two 32-byte `TTEntry` structs = **64 bytes (exact x86-64 cache line)**.
   - Guard buckets with a striped array of atomic spinlocks (`65536` cache-line-padded or byte-packed `atomic_flag` / `uint8_t` locks indexed by `bucket_idx & 65535`), OR pack a 1-bit lock inside `bucket[0].flags`. Holding a lock for ~15 ns across 65,536 stripes produces $< 0.1\%$ contention at 24 threads.
4. **Virtual Loss (Work Divergence):**
   - Add a `uint8_t in_flight` counter (or add `+4` virtual loss to `pn`/`dn` via atomic increment/decrement when entering/leaving `dfpn_mid`) so threads exploring the upper tree naturally spread across different AND children and `second_best` OR children instead of duplicating the exact same path.
   - Terminate all worker threads cleanly as soon as the root entry transitions to `PROVED` or `DISPROVED` (checked via an `_Atomic bool search_done`).

---

## 5. Part III: CPU Microarchitecture & Data-Structure Engineering (`mnk_prover.c`)

### 5.1 L1-Resident Symmetry Canonicalization & Early Exit
Currently, `board.symmetry_table[8][8][256]` occupies **128 KB** ($> 3\times$ L1d cache size) and unconditionally transforms both `maker` and `breaker`.

**Required Changes:**
1. **Early exit on `maker`:**
   ```c
   static Position symmetry_canonical(Position p, uint8_t* sym_out)
   {
       Position best = p;
       uint8_t best_t = 0;
       for (int t = 1; t < board.symmetry_count; t++) {
           const Bitboard m = apply_symmetry(t, p.maker);
           if (m > best.maker) continue;            /* ~50% immediate skip */
           const Bitboard b = apply_symmetry(t, p.breaker);
           if (m < best.maker || b < best.breaker) {
               best.maker = m;
               best.breaker = b;
               best_t = (uint8_t)t;
           }
       }
       if (sym_out) *sym_out = best_t;
       return best;
   }
   ```
   Also precompute `uint8_t inv_sym[MAX_SYMMETRIES]` at `board_init()` (for $D_4$: `inv_sym = {0, 1, 2, 3, 4, 5, 7, 6}`, since rotate-90 and rotate-270 are inverses and all reflections/180 are involutions).
2. **Replace 128 KB byte table with 16 KB nibble table:**
   ```c
   Bitboard symmetry_nibble[MAX_SYMMETRIES][16][16]; /* 8 * 16 * 16 * 8 = 16 KB (fits in L1d) */
   int      nibble_count;                            /* (cell_count + 3) / 4 */
   ```
   Loop only `j = 0 .. board.nibble_count - 1` (e.g., 13 iterations for $(7,7,5)$, 9 for $(6,6,5)$).
3. *(Optional specialization)* For square boards $m = n \le 8$, bit-packing into an $8 \times 8$ stride allows pure-register SWAR $D_4$ flips/transposes (`__builtin_bswap64` + 3 delta swaps) with **zero memory lookups**. Keep nibble tables as the generic path for arbitrary $(m, n)$.

### 5.2 AVX2 Live-Line Extraction
Align `board.line[MAX_LINES]` to 32 bytes (`_Alignas(32)`) and pad `line_count` up to a multiple of 4 using `~0ULL` sentinel masks (which always intersect any non-empty `breaker`, or mask out tail lanes when `breaker == 0`). Under `#ifdef __AVX2__`:

```c
__m256i vbreaker = _mm256_set1_epi64x((long long)p.breaker);
__m256i vzero    = _mm256_setzero_si256();
for (int i = 0; i < board.line_count_padded; i += 4) {
    __m256i vline = _mm256_load_si256((const __m256i*)&board.line[i]);
    __m256i vhit  = _mm256_and_si256(vline, vbreaker);
    int mask = _mm256_movemask_pd(_mm256_castsi256_pd(_mm256_cmpeq_epi64(vhit, vzero)));
    while (mask) {
        int lane = __builtin_ctz(mask);
        mask &= mask - 1;
        int id = i + lane;
        if (id >= board.line_count) break;
        /* process live line id */
    }
}
```
Provide a clean `#else` scalar fallback.

### 5.3 Bitboard-Accelerated Kuhn's 2-Matching
In `has_two_matching(const Component* comp)`:
1. Maintain `Bitboard matched_cells = 0;` alongside `int8_t owner_of_cell[MAX_CELLS]`.
2. **Greedy single-pass pre-match:** First scan all `2 * comp->n` slots; if `(comp->lines[slot / 2] & ~matched_cells)` is non-zero, take its lowest cell immediately (O(1), zero recursion). Queue only the unmatched slots for Kuhn augmentation.
3. **1-cycle free-cell hit inside `matching_augment()`:**
   ```c
   Bitboard candidates = comp->lines[slot >> 1] & ~(*visited);
   Bitboard free_hit   = candidates & ~(*matched_cells);
   if (free_hit) {
       const int c = lowest_cell(free_hit);
       *matched_cells |= cell_bit(c);
       owner_of_cell[c] = (int8_t)slot;
       return true;
   }
   while (candidates) {
       const int c = lowest_cell(candidates);
       candidates &= candidates - 1;
       *visited |= cell_bit(c);
       if (matching_augment(comp, owner_of_cell[c], owner_of_cell, visited, matched_cells)) {
           owner_of_cell[c] = (int8_t)slot;
           return true;
       }
   }
   return false;
   ```

### 5.4 Dynamic `LineSet` Fast Path & Degree-Sorted Dominance
- When `h->count <= 64`, represent `lines_through[c]` as a single `uint64_t` instead of `uint64_t[4]`, eliminating 75% of memory traffic and loop overhead in `undominated_moves()` and `cover_recurse()`.
- In `undominated_moves()`, sort `cells[0..m-1]` by descending `popcount(lines_through[c])`. A cell $u$ can only be dominated by $v$ if $\deg(v) \ge \deg(u)$, cutting the $O(m^2)$ inner loop in half and improving branch predictability.

### 5.5 Cache-Aligned 32-Byte `TTEntry` Layout & Software Prefetching
Pack `TTEntry` into **exact 32 bytes** so a 2-way bucket fits in one 64-byte cache line. Because `relevance` is only valid once a node is `PROVED` (and `proof`/`disproof` are no longer needed then), overlay them in a `union`:

```c
enum {
    TT_EMPTY     = 0,
    TT_OPEN      = 1,
    TT_PROVED    = 2,
    TT_DISPROVED = 3
};

typedef struct __attribute__((aligned(32))) {
    Bitboard maker;
    Bitboard breaker;
    union {
        struct { uint32_t proof; uint32_t disproof; } pn;
        Bitboard relevance;       /* valid iff status == TT_PROVED */
    } u;
    uint32_t work;                /* subtree search calls */
    int8_t   best_move;           /* winning Breaker move (or -1 for leaf/AND) */
    uint8_t  meta;                /* bits 0..1: status; bit 2: turn (0=B,1=M); bits 3..7: leaf_kind */
    uint8_t  in_flight;           /* active worker count for virtual loss */
    uint8_t  sym_hint;            /* optional cached symmetry for certificate export */
} TTEntry;

_Static_assert(sizeof(TTEntry) == 32, "TTEntry must be exactly 32 bytes");
```

In `dfpn_mid()`, when scanning children `i = 0 .. moves.count - 1`, issue `__builtin_prefetch(tt_bucket(child[i + 4], next_turn), 0, 1);` 4 steps ahead whenever children are already materialized.

### 5.6 Recommended Build Flags
```bash
gcc -O3 -march=native -flto -fopenmp -DNDEBUG -Wall -Wextra -o mnk_prover mnk_prover.c -lm
```
For debugging/soundness verification builds:
```bash
gcc -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer -Wall -Wextra -o mnk_prover_san mnk_prover.c -lm
```

---

## 6. Part IV: CUDA / GPU Engineering (`mnk_proof.cu`)

### 6.1 Root Cause of the 5x `(10,5,5)` Pass-1 Slowdown
With default parameters on an 8 GB RTX GPU under WSL2/WDDM:
- `device_bloom` ($2^{34}$ bits): **$2.15\text{ GB}$**
- `level_a_` + `level_b_` ($2 \times 80\text{M} \times 16\text{ B}$): **$2.56\text{ GB}$**
- `replies_` + `lost_p2_` ($2 \times 500\text{K} \times 50 \times 16\text{ B}$): **$0.80\text{ GB}$**
- `thrust::sort` internal merge-sort temporary buffer on $80\text{M} \times 16\text{ B}$: **$\sim 1.3$--$2.5\text{ GB}$**

Total peak allocation hits **$6.8$--$8.0\text{ GB}$**, exceeding usable VRAM after WDDM reservation ($\sim 0.8$--$1.0\text{ GB}$) and triggering silent PCIe paging to host RAM. Freeing `device_bloom` before verification restores physical VRAM residency, explaining the 5x jump.

**Mandatory Guardrail:** Query `cudaMemGetInfo(&free_bytes, &total_bytes)` at startup, reserve a $15\%$ WDDM headroom margin, and auto-cap `level_capacity` and `bloom_log2` so total allocation (including pre-allocated CUB sort workspace) **never** exceeds $85\%$ of `free_bytes`.

### 6.2 Eliminate Local-Memory Spilling (`weight` Arrays)
In `expand_level` and `p2_node`, `uint64_t weight[64]`, `w1[64]`, and `w2[64]` allocate **1,536 bytes/thread** of private arrays, forcing massive local-memory stack spills on `sm_89`.
- **Mathematical bound:** On any $(m, n, k)$ grid, a single cell lies on at most $4k$ lines, each of weight at most $2^{k-1}$. Thus the maximum possible cell weight is:
  $$W_{\max}(k) \le 4k \cdot 2^{k-1} = k \cdot 2^{k+1}.$$
  - For $k \le 8$: $W_{\max}(8) = 4096 < 65536$ $\implies$ **`uint16_t`** is exact (4x smaller!).
  - For $9 \le k \le 16$: $W_{\max}(16) = 2^{21} < 2^{32}$ $\implies$ **`uint32_t`** is exact (2x smaller!).
- Template the kernel on `typename WeightT` (`uint16_t` when $k \le 8$, `uint32_t` when $k \le 16$).

### 6.3 Warp-Aggregated Compaction (`__ballot_sync`) — Delete Markers & `thrust::remove_if`
Current `expand_level` writes uncoalesced `marker_position()` sentinels into `replies[i * F + j]` and `lost_p2[i * F + j]`, allocates 400 MB for `lost_p2_` (which is $99.999\%$ empty), and runs three `thrust::remove_if` passes per sub-batch.

**Replacement:** Use compact device output queues with atomic counters (`d_reply_count`, `d_lost_count`, `d_win_count`) and warp-aggregated insertion:
```cuda
__device__ inline void warp_push(Position* out, unsigned long long* counter,
                                 bool active, Position val)
{
    const unsigned mask = __ballot_sync(0xFFFFFFFFu, active);
    if (mask == 0u) return;
    const int lane   = threadIdx.x & 31;
    const int leader = __ffs(mask) - 1;
    unsigned long long base = 0;
    if (lane == leader) {
        base = atomicAdd(counter, static_cast<unsigned long long>(__popc(mask)));
    }
    base = __shfl_sync(0xFFFFFFFFu, base, leader);
    if (active) {
        const unsigned rank = __popc(mask & ((1u << lane) - 1u));
        out[base + rank] = val;
    }
}
```
**Wins:**
1. Eliminates 100% of `marker_position()` writes.
2. Eliminates all 3 `thrust::remove_if` launches per sub-batch.
3. Shrinks `lost_p2_` from 400 MB to $\sim 4\text{ MB}$ (growable/capped safely).
4. Makes global output writes coalesced within each warp.

### 6.4 Pre-Extract $(k-2)$-Lines Once in `p2_node`
`p2_node` currently loops over all `g.line_count` lines inside the outer loop over up to `cell_count` candidate replies ($O(n \cdot \text{cells})$ per P2 child).

**Replacement:** Before the candidate loop, scan `g.lines` **once** to extract all live P1 lines with exactly $k - 2$ P1 stones into a tiny register/stack array `uint8_t pair_u[32], pair_v[32]; int pair_count;` (overflow fallback to full scan only if `pair_count == 32`, which is astronomically rare).
- If `pair_count <= 1`: **every** candidate is automatically safe—pick `top` immediately in $O(1)$!
- Otherwise, test candidate `c` only against those `pair_count` pairs (typically 2--6 pairs), skipping any pair where `u == c || v == c` (since P2 playing `c` kills that line).

### 6.5 Word-Blocked Single-Atomic Bloom Filter
Replace 5 random 64-bit `atomicOr` operations across 2 GB of VRAM with a **64-bit word-blocked Bloom filter**:
- Use `h1` to select a single 64-bit word index: `word_idx = h1 & d_bloom_word_mask`.
- Derive 5 bit positions inside that 64-bit word from `h2` (e.g., 5 distinct 6-bit slices of `h2` and `mix64(h2)`), combine them into one `uint64_t pattern`, and execute **a single** `atomicOr(&bloom[word_idx], pattern)`.
- **Result:** 5x fewer GPU DRAM atomics during Pass 1 and 5x fewer L3/DRAM cache misses in CPU `HostBloom::contains()`. (False-positive rate at fill $f \approx 0.15$ remains $< 0.002$; if lower FPR is desired, use a 2-word 128-bit block.)

### 6.6 CUB Bit-Bounded Radix Sort (Pre-Allocated Workspace)
Replace `thrust::sort` (comparison-based merge sort on 16-byte structs with hidden dynamic allocation) with two-pass `cub::DeviceRadixSort::SortPairs` / `SortKeys` using a **single pre-allocated workspace buffer**:
- Store `level_a_` and `level_b_` as **Structure of Arrays (SoA)**: `Bitboard* p1`, `Bitboard* p2`.
- Sort by `p2` first (`begin_bit = 0, end_bit = cell_count`), then stably sort by `p1` (`begin_bit = 0, end_bit = cell_count`).
- On $(7,7,5)$, sorting 49 bits instead of 64 avoids 2 radix passes per key, runs $3\times$--$5\times$ faster than `thrust::sort`, and guarantees deterministic VRAM usage.

### 6.7 Two-Kernel Decoupling (Warp Divergence Removal)
In `expand_level`, 1 thread loops over up to 49 free cells while warp-mates that hit an `es_inv` leaf sit masked off. Decouple into:
1. **Kernel 1 (`expand_p1_to_p2`):** 1 thread per P1 node. Runs Bloom insert + P1 leaf check; pushes active canonical P2 children via `warp_push` into a compact P2 queue.
2. **Kernel 2 (`evaluate_p2_replies`):** 1 thread per P2 child. Checks `held` set (sorted binary search), runs `p2_node()`, and pushes `replies` / `lost_p2` via `warp_push`.

All 32 threads in Kernel 2 perform uniform work with minimal divergence.

---

## 7. Part V: Rocq Certificate Format & Trusted Verifier Contract

### 7.1 Architectural Principle
Once `mnk_prover` proves the root (`TT_PROVED`), run a post-order DFS over the transposition table starting from the root to emit every reachable `PROVED` node into a flat, **topologically sorted** DAG array `Node nodes[0 .. N-1]` such that:
- Every child edge satisfies `child_id < node_id` (structural acyclicity—Rocq checks the entire DAG in a single linear pass with zero cycle detection!).
- `nodes[N - 1]` is the root `(0, 0)`.

### 7.2 Binary / Rocq-Extractable Certificate Schema
Each record in the certificate stores:
- `uint64_t p1, p2;` (the canonical board state at this node; `p1 & p2 == 0`)
- `uint8_t turn;` (`0` = P2/Breaker to move, `1` = P1/Maker to move)
- `uint8_t kind;` (witness tag below)
- `uint64_t rz_mask;` (claimed relevance zone bitboard in this node's canonical coordinates; must satisfy `(rz_mask & (p1 | p2)) == 0`)

| Tag (`kind`) | Payload | Exact Local Check Performed by Trusted Verifier / Rocq (`PrimInt63`) |
|---|---|---|
| `LEAF_FULL` | none | `(p1 | p2) == all_cells` and no P1 line completed; `rz_mask == 0` |
| `LEAF_P2_WIN` (SG) | `uint8_t move` | `turn == 0`, `move` free, `p2 | bit(move)` contains a winning line; `bit(move) <= rz_mask` |
| `LEAF_P2_DBL_THREAT` (SG) | `uint8_t c1, c2` | `turn == 1`, `c1 != c2` both free, both complete a P2 line; `(bit(c1) | bit(c2)) <= rz_mask` |
| `LEAF_ES_MAKER` | none | `turn == 1`; compute $\phi, w$ over live P1 lines; verify $\phi + \max_{\text{free}} w < 2^k$ and $\bigcup F(L) \subseteq \text{rz\_mask}$ |
| `LEAF_ES_BREAKER` | none | `turn == 0`; verify $\phi < 2^k$ over live P1 lines and $\bigcup F(L) \subseteq \text{rz\_mask}$ |
| `LEAF_PAIRS_ES` | `uint8_t npairs`, `uint8_t u[npairs], v[npairs]` | Verify all $2 \cdot \text{npairs}$ cells are free and pairwise distinct (mask $C_P$). For every live P1 line $L$ not containing any pair $\{u_i, v_i\}$, restrict $F(L)$ to $F(L) \setminus C_P$ (must be non-empty) and verify Maker-first ES $\phi_{\text{rem}} + \max w_{\text{rem}} < 2^k$. Verify $C_P \cup \bigcup_{L \in \mathcal{U}} (F(L) \setminus C_P) \subseteq \text{rz\_mask}$. (Covers pure 2-matching, exact pair cover, twin pairs, and hybrids in **one unified Rocq lemma**!) |
| `LEAF_COMPONENTS` | `uint8_t ncomp`, `uint64_t comp_mask[ncomp]`, sub-witnesses | Verify `comp_mask[j]` are pairwise disjoint subsets of free cells; verify every live P1 line has $F(L) \subseteq \text{comp\_mask}[j]$ for some $j$; verify each sub-witness on its component; verify $\bigcup_j Z_j \subseteq \text{rz\_mask}$ |
| `INTERNAL_P2_OR` | `uint8_t move`, `uint8_t sym`, `uint32_t child_id` | `turn == 0`, `move` free, `child_id < self`, `nodes[child_id].turn == 1`, `apply_sym(sym, (p1, p2 | bit(move))) == (child.p1, child.p2)`, and `bit(move) | apply_sym(inv_sym[sym], child.rz_mask) <= rz_mask` |
| `INTERNAL_P1_AND_RZ` | `uint8_t def_b`, `uint8_t def_sym`, `uint32_t def_child`, `uint8_t n_explicit`, `(move_j, sym_j, child_j)` | `turn == 1`. First verify default Breaker reply `def_b` (free): `apply_sym(def_sym, (p1, p2 | bit(def_b))) == (def_child.p1, def_child.p2)` with `def_child < self`. Let $R_0 = \text{bit}(\text{def\_b}) \mid \text{apply\_sym}(\text{inv\_sym}[\text{def\_sym}], \text{def\_child.rz\_mask})$. Verify every free cell $m \in R_0$ appears in the explicit list `(move_j, sym_j, child_j)` with `child_j < self` and `apply_sym(sym_j, (p1 | bit(m), p2)) == (child_j.p1, child_j.p2)`. Verify $R_0 \cup \bigcup_j \text{apply\_sym}(\text{inv\_sym}[\text{sym}_j], \text{child}_j.\text{rz\_mask}) \subseteq \text{rz\_mask}$. |

*(Note: For a standard AND node without a default reply—e.g. when `n_explicit` covers all free cells or when a forced P2-threat block exists in SG—set `def_b = 0xFF` and verify all legal moves explicitly. By storing `sym` on every edge, Rocq never computes canonical forms—it checks one single permutation per edge!)*

### 7.3 Standalone C Certificate Verifier (`mnk_verify.c`)
Before writing a single line of Rocq code, the coding agent **must** implement a tiny (< 300 lines), zero-dependency, auditable `mnk_verify.c` that implements **only** the table above and verifies `.mnkcert` files independently. This mirrors the exact logic to be ported to Rocq `PrimInt63` and catches any bug in symmetry un-mapping, relevance zones, or twin-pair extraction immediately.

---

## 8. Part VI: Phased Execution Plan & Verification Matrix

### 8.1 Mandatory Implementation Order (Execute & Benchmark One Phase at a Time)

| Phase | Target File(s) | Scope of Work | Acceptance Gate |
|---|---|---|---|
| **Phase 1** | `mnk_prover.c` | (a) Swap `greedy_hybrid` before `pair_cover`; (b) 2-line conflict abort + unit propagation in `cover_recurse`; (c) Collinear $O(n)$ subsumption; (d) Fixed-point twin-pair elimination; (e) 1-ply Breaker-first ES/matching lookahead; (f) Replace `clock()` with `CLOCK_MONOTONIC` | Identical verdicts across full test matrix; $\ge 5\times$ speedup on $(7,4,4)$ and $(8,4,4)$ |
| **Phase 2** | `mnk_prover.c` | (a) $1 + \varepsilon$ thresholding; (b) Heuristic PN/DN initialization; (c) Lazy `child_state` + local `child_pn[]`; (d) Bitboard VCT disproofs; (e) Protect `PROVED` entries from TT eviction | $\ge 10\times$ additional node reduction on $(8,4,4)$ and $(7,7,5)$; zero sanitizer errors |
| **Phase 3** | `mnk_prover.c` + `mnk_verify.c` | (a) 32-byte `TTEntry` with `relevance` union & `best_move`; (b) Constructive Relevance Zones + symmetry un-mapping + AND-node sibling pruning + Null-Move Probe; (c) Binary `.mnkcert` exporter + standalone `mnk_verify.c` | `mnk_verify` passes $100\%$ of exported draw proofs on $(5,5,4)$, $(6,4,4)$, $(7,4,4)$, $(8,4,4)$, $(6,6,5)$, $(7,7,5)$; $(7,7,5)$ solves in $< 15\text{ s}$ with $< 5 \times 10^6$ certificate nodes |
| **Phase 4** | `mnk_prover.c` | (a) 16 KB nibble symmetry table + `maker` early exit (and SWAR $D_4$ for squares); (b) AVX2 live-line extraction; (c) Bitboard Kuhn pre-match; (d) 1-word `LineSet` fast path + degree-sorted dominance; (e) 24-thread parallel df-pn with striped locks, virtual loss, and thread-local stats | Linear-to-superlinear scaling up to 24 threads; $(7,7,5)$ in $\sim 1$--$3\text{ s}$; verify $(9,5,5)$, $(10,5,5)$, and benchmark $(8,8,5)$ |
| **Phase 5** | `mnk_proof.cu` | (a) `cudaMemGetInfo` VRAM guard; (b) `uint16_t`/`uint32_t` weights; (c) Warp-aggregated compaction (`__ballot_sync`), removing markers/`remove_if`/400 MB `lost_p2_`; (d) Pre-extracted $(k-2)$-lines; (e) Word-blocked 1-atomic Bloom; (f) CUB bit-bounded radix sort + SoA; (g) 2-kernel decoupling | Zero PCIe paging on $(10,5,5)$ and $(7,7,5)$; Pass 1 within $1.3\times$ of Verification pass; $\ge 3\times$ overall GPU throughput gain |

### 8.2 Regression & Soundness Test Matrix
Every phase **must** pass all rows below (both MB and SG where applicable, plus `-fsanitize=address,undefined` on small/medium boards):

| Board $(m,n,k)$ | Expected Value | Role in Verification Suite |
|---|---|---|
| $(3,3,3)$ | Draw | Smoke test + full certificate audit |
| $(4,4,4)$ | Draw | Smoke test (square $D_4$ symmetry) |
| $(4,3,3)$ | P1 win | **Negative soundness test** (must NOT falsely prove draw!) |
| $(6,5,4)$ | P1 win | **Critical negative soundness test** (tests MB & SG pruning soundness) |
| $(6,6,4)$ | P1 win | **Critical negative soundness test** (square $D_4$ + large branching) |
| $(5,5,4)$ | Draw | Fast MB/SG regression + certificate size tracking |
| $(6,4,4)$ | Draw | Rectangular $D_2$ symmetry regression |
| $(7,4,4)$ | Draw | Medium search benchmark (ablation for PN/DN init, $1+\varepsilon$, RZ) |
| $(8,4,4)$ | Draw | Hard $k=4$ benchmark (tests SG vs. MB, twin pairs, VCT) |
| $(6,6,5)$ | Draw | Instant leaf/ES regression |
| $(9,5,5)$ | Draw | Rectangular $k=5$ benchmark |
| $(7,7,5)$ | Draw | **Primary milestone target** (aim: $< 3\text{ s}$, Rocq-tractable certificate) |
| $(10,5,5)$ | Draw | Large 50-cell benchmark (also primary CUDA Pass-1 VRAM test) |
| $(8,8,5)$ | Draw | Stretch research benchmark (64-cell boundary test: verify `cell_count == 64` has zero UB in `1ULL << 64` shifts!) |

### 8.3 Critical Subtle Bugs to Guard Against (64-Bit & Soundness Checklist)
1. **64-cell shift UB (`8x8` boards):** Never evaluate `1ULL << board.cell_count` when `cell_count == 64`. Always guard with `cell_count == 64 ? ~0ULL : (1ULL << cell_count) - 1`.
2. **Symmetry inversion direction:** Verify by unit test that for every symmetry $t$ and random bitboard $b$, `apply_sym(inv_sym[t], apply_sym(t, b)) == b`. Using $t$ instead of $t^{-1}$ when un-mapping relevance zones silently corrupts $(m, n)$ square boards for $t \in \{6, 7\}$ (90/270 rotations).
3. **`reduced_state` vs. Relevance Zones:** If `options.reduced_state` is enabled in `RULES_MAKER_BREAKER`, dead cells are filled with virtual Breaker stones before canonicalization. Ensure that any virtual Breaker stones added by `reduced_state` are **not** accidentally required to be free when checking `INTERNAL_P1_AND_RZ` / `INTERNAL_P2_OR` in the certificate! Simplest clean solution: when exporting certificates (or when Relevance Zones are active), either disable `reduced_state` (Relevance Zones already prune dead cells cleanly!) or track `dead_mask` explicitly in the edge witness.
4. **Strong-Game (`RULES_STRONG`) soundness:** Never apply Maker-only restrictions (`restrict_maker`, `reduced_state`, or Maker dominance) in `RULES_STRONG`, and always include P2 completion/threat cells in `rz_mask` for `LEAF_P2_WIN` / `LEAF_P2_DBL_THREAT` / forced P1 blocks.
5. **Parallel df-pn race on `PROVED` payload:** When writing a `PROVED` entry into the TT, store `relevance`, `best_move`, and `meta` *under the bucket lock* (or before releasing the seqlock) so no reader ever observes `TT_PROVED` paired with stale `pn.proof`/`pn.disproof` bits in the `union`.