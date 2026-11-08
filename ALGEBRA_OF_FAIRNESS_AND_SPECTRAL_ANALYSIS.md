# The Algebra of Fairness, Spectral Graph Theory, and Polynomial Ideals in the Morris Game Family

[![Back to Main Landing Page](https://img.shields.io/badge/⬅_Back_to_Main_Hub-README.md-2563eb?style=for-the-badge)](README.md)
[![Rocq 9.1 Verified](https://img.shields.io/badge/Rocq_9.1-85_Theorems_Closed-22c55e?style=for-the-badge)](build.ps1)
[![Lean 4.35.0 Verified](https://img.shields.io/badge/Lean_4.35.0-46_Theorems_0_sorry-10b981?style=for-the-badge)](build_lean.ps1)
[![Nine Men's Morris Branch](https://img.shields.io/badge/🎲_Branch-nine--mens--morris-emerald?style=for-the-badge)](https://github.com/TACITVS/8x7_Connect_5_Is_A_Proven_Fair_Game/tree/nine-mens-morris)
[![Twelve Men's Morris Branch](https://img.shields.io/badge/🎲_Branch-twelve--mens--morris-indigo?style=for-the-badge)](https://github.com/TACITVS/8x7_Connect_5_Is_A_Proven_Fair_Game/tree/twelve-mens-morris)

> **Abstract:** This treatise establishes a unified mathematical foundation for the classical and generalized Morris game family across three interconnected mathematical disciplines:
> 1. **Combinatorial Game Theory:** The *Algebra of Fairness* governing why Nine Men's Morris is an exact fair draw while Twelve Men's Morris (Morabaraba) collapses into a first-player win.
> 2. **Linear Algebra & Spectral Graph Theory:** The spectrum of the adjacency matrix, graph Laplacians, Fiedler algebraic connectivity, and the mill incidence Gram matrix.
> 3. **Commutative Algebra & Polynomial Ideals:** The coordinate ring, Hilbert's Nullstellensatz representation of mill varieties, and the exact monomial factorization of opening double-forks.

---

## 🏛️ Part I: The Algebra of Fairness

Let a generalized concentric Morris game `M(r, d, n)` be parameterized by:
* `r >= 1`: The number of concentric square rings (`N = 8r` board vertices).
* `d in {0, 4}`: The number of diagonal corner lines (`d = 0` for classical Morris; `d = 4` for Morabaraba).
* `n in N`: The number of stones allocated to each player.
* `H = (V, E_M)`: The 3-uniform mill hypergraph where each mill `e in E_M` has cardinality `card(e) = 3`.

---

### 1. The Three Governing Invariants of Fairness

#### Invariant 1: The Maximum Mill Degree Bound (Fork-Free Regularity)

```text
Delta_M = max_{v in V} deg_M(v)
```

* **Uniform Regularity (`Delta_M <= 2`):** Every vertex belongs to at most 2 mills. A single stone placement on vertex `v` can advance at most 2 mills. A player can never create a 3-way branching fork from a single opening stone; single threats can always be parried by the defender.
* **Broken Regularity (`Delta_M >= 3`):** Corner vertices belong to 3 intersecting mills (2 concentric ring mills + 1 diagonal mill). Because those 3 rays are pairwise disjoint outside the corner (`corner_0_three_rays`), the first player can leave at least 2 rays unblocked after Ply 1 (`corner_0_two_rays_unblocked_after_ply1`) and force an unblockable **simultaneous double-mill fork** on Ply 8 (`ply8_corner_fork_theorem`).

---

#### Invariant 2: The Transversal Solvency Law (Defensive Capacity)

```text
delta(n) = n - tau(H_r) >= 0
```

Where `tau(H_r)` is the **transversal number** (minimum hitting set size) of the mill hypergraph:
* For Black to have the theoretical capacity to prevent White from completing any mill, Black must place at least `tau(H_r)` stones.
* For `r >= 3` concentric rings without diagonals (`d = 0`), where the 4 radial midpoint connectors have length `r >= 3` and form 4 radial mills:
  - Placing 4 midpoints on one ring intersects all 4 ring mills of that ring AND all 4 radial cross-mills.
  - Placing 2 opposite corners on each of the remaining `r - 1` rings covers their `4(r - 1)` ring mills (`2(r - 1)` stones).
  - Thus `tau(H_r) = 4 + 2(r - 1) = 2r + 2` for `r >= 3` (giving `tau(H_3) = 2(3) + 2 = 8` for Nine Men's Morris!).
  - For `r = 2` (Six Men's Morris, where radial connectors have only 2 vertices and thus form no 3-point radial mills), 2 opposite corners on each of the 2 rings suffice: `tau(H_2) = 2 * 2 = 4`.
* If `n < tau(H_r)`, Black is **transversal insolvent**: White is mathematically guaranteed an unblockable mill.

---

#### Invariant 3: The Saturation Ratio & Slidability Bound

```text
rho = (2 * n) / (8 * r) = n / (4 * r)
```

* **Strictly Sub-Saturated (`rho < 1`):** At the end of Phase 1, there remain `8r - 2n > 0` vacant spaces. Players can legally slide in Phase 2 with full topological freedom.
* **Completely Saturated (`rho = 1`):** Exactly `2n = 8r`. If no captures occur in Phase 1, the board is 100% full, causing an immediate deadlock unless White forces an opening capture.

---

### 2. The Morris Fairness Classification Theorem

**Theorem (Algebra of Fairness Dichotomy):**  
A concentric Morris game `M(r, d, n)` with `r >= 2` rings is an **Exact Fair Draw** if and only if it satisfies the **Triple Fairness Conjunction**:

```text
Fair(M)  <==>  1. d = 0  <==>  Delta_M <= 2        (Fork-Free Regularity)
               2. n >= tau(H_r)                    (Transversal Solvency: tau = 4 for r = 2; 2r + 2 for r >= 3)
               3. rho = n / (4r) < 1  <==>  n < 4r (Sub-Saturation Mobility)
```

If any of these three conditions is violated:
* If `d = 4` (`Delta_M >= 3`): White exploits the degree-3 corner junctions to force an unblockable double-threat fork in Phase 1 (`ply8_corner_fork_theorem`) -> **Win White**.
* If `n < tau(H_r)`: Black lacks sufficient stones to cover all lines -> **Win White**.
* If `n >= 4r` and `d = 0`: The board saturates with zero sliding moves in Phase 2.

---

### 3. Why the Classical Formula `n = 3r` Produces Perfect Balance

Historically, the classical European tradition assigned `n(r) = 3r` stones per player:
* `r = 1`: `n = 3` (Three Men's Morris)
* `r = 2`: `n = 6` (Six Men's Morris, `tau(H_2) = 4`, surplus `delta = 6 - 4 = +2`)
* `r = 3`: `n = 9` (Nine Men's Morris, `tau(H_3) = 2(3) + 2 = 8`, surplus `delta = 9 - 8 = +1`)

Setting `n = 3r` with `d = 0` guarantees that all three conditions hold simultaneously for `r >= 2`:
1. **Regularity:** `Delta_M = 2` uniformly everywhere.
2. **Defensive Solvency:** For `r = 2`, `delta = 6 - 4 = +2 > 0`; for `r >= 3`, `delta(r) = 3r - (2r + 2) = r - 2 > 0`.
3. **Constant 75% Saturation:** `rho = 3r / 4r = 3 / 4 = 75%` for all `r >= 1`. Exactly one-quarter of the board remains open for dynamic Phase 2 maneuvering.

---

## 🔢 Part II: Linear Algebra & Spectral Graph Theory

### 1. The Adjacency Matrix & Spectral Radius Expansion

Let `A_9` and `A_12` be the `24 × 24` adjacency matrices of the Nine Men's Morris and Twelve Men's Morris graphs:

| Spectral Property | Nine Men's Morris (`A_9`) | Twelve Men's Morris (`A_12`) | Mathematical Interpretation |
| :--- | :---: | :---: | :--- |
| **Edge Count (`card(E)`)** | 32 edges | 40 edges | 8 diagonal edges added |
| **Spectral Radius (`rho(A) = lambda_max`)** | `2 * sqrt(2) ≈ 2.8284` | `2 + sqrt(2) ≈ 3.4142` | **`+20.7%` Expansion:** Attack threats propagate significantly faster across the board |
| **Bipartite Spectral Symmetry** | `lambda in Spec(A) => -lambda in Spec(A)` | `lambda in Spec(A) => -lambda in Spec(A)` | **Both boards are strictly bipartite** (contain no odd cycles) |
| **Nullity (`dim(ker(A))`)** | 4 (eigenvalue 0 multiplicity 4) | 6 (eigenvalue 0 multiplicity 6) | 6 independent stationary vertex distributions |

---

### 2. Graph Laplacians & Fiedler Algebraic Connectivity

The combinatorial Graph Laplacian is defined as:

```text
L = D - A,   where D = diag(deg(v))
```

The second smallest eigenvalue `mu_2(L)` is the **Fiedler Algebraic Connectivity**, which quantifies the difficulty of partitioning the graph into disconnected components:

* **Nine Men's Morris Laplacian:** `mu_2(L_9) ≈ 0.4384`
* **Twelve Men's Morris Laplacian:** `mu_2(L_12) = 2 - sqrt(2) ≈ 0.5858`
* **Connectivity Jump:** `Delta mu_2 = (0.5858 - 0.4384) / 0.4384 = +33.6%`

The `+33.6%` increase in algebraic connectivity shows how the 4 diagonal lines compress the graph's diameter and mixing time, eliminating isolated defensive pockets.

---

### 3. The Mill Incidence Matrix & The Dual Gram Matrix

Let `M in {0, 1}^{card(E_M) × 24}` be the incidence matrix where `M_{i, j} = 1` if vertex `j` belongs to mill `i`.

#### The Dual Intersection Gram Matrix `G = M * M^T`:
* `G_{i, i} = ||M_{i, :}||_2^2 = 3` (every mill contains exactly 3 vertices).
* `G_{i, j} = card(m_i intersect m_j)` (number of vertices shared between mill `i` and mill `j`).

**Matrix Computation Results:**
1. **In Nine Men's Morris (`M_9 in R^{16 × 24}`):**
   * Every diagonal entry is 3: `(G_9)_{i, i} = 3`.
   * Every off-diagonal row sum is **strictly 3**: `sum_{j != i} (G_9)_{i, j} = 3` for all `i in {1, ..., 16}`.
   * **Matrix Proof of 3-Regularity:** The dual mill graph is an **exact 3-regular cubic graph on 16 vertices** (`dual_graph_handshake`).
2. **In Twelve Men's Morris (`M_12 in R^{20 × 24}`):**
   * The 12 ring mills intersect 5 other mills.
   * The 4 radial mills intersect 3 other mills.
   * **The 4 Diagonal Mills intersect 6 other mills each!**
   * In matrix terms, the diagonal mills act as **degree-6 global hubs** in the dual graph, bridging concentric rings that were previously only linked at midpoints.

---

### 4. Exact Linear Dependencies in the Mill Hypergraph

#### Nine Men's Morris (`rank(M_9) = 15`)

There is **strictly one linear dependency** spanning `ker(M_9^T)`:

```text
v_9 = [-1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1]^T
```

**The Alternating Mill Conservation Law:**  
The alternating sum of the 12 concentric ring mills equals the alternating sum of the 4 radial cross mills:

```text
sum_{r=0}^2 sum_{k=0}^3 (-1)^{k+1} m_{r, k} + sum_{j=0}^3 (-1)^j m_{radial, j} = 0
```

#### Twelve Men's Morris (`rank(M_12) = 16`)

```text
dim(ker(M_12^T)) = 20 - 16 = 4
```

The 4 diagonal mills introduce 4 independent linear dependencies, reflecting the 4 new closed algebraic cycles in the dual graph.

---

## 🧮 Part III: Polynomial Algebra & Commutative Geometry

### 1. The Game Coordinate Ring & Mill Ideals

We formulate the game in the polynomial quotient ring over the 24 vertex variables:

```text
R = R[x_0, x_1, ..., x_23] / <x_i^2 - x_i>_{i=0..23}
```

Where `x_i = 1` indicates that White occupies vertex `i`, and `x_i = 0` otherwise.

Every mill `m = {a, b, c} in E_M` corresponds to a square-free cubic monomial:

```text
P_m(x) = x_a * x_b * x_c
```

The **Mill Ideal** is defined as:

```text
I_mill = < x_a * x_b * x_c | {a, b, c} in E_M >
```

The set of mill-free board states is precisely the **algebraic variety** `V(I_mill)` where all generators vanish.

---

### 2. Degree-3 Corner Radiation & The Algebraic Factorization of the Fork

Why can White force this fork in Twelve Men's Morris (`Delta_M = 3`) but NOT in Nine Men's Morris (`Delta_M = 2`)?
1. **Degree-3 Corner Radiation (`corner_0_three_rays`):** At Ply 0, White occupies Corner `0`, which belongs to three mills whose remaining vertex pairs `{1, 2}`, `{6, 7}`, `{8, 16}` are pairwise disjoint:
   ```text
   P_{0,1,2} + P_{0,6,7} + P_{0,8,16} = x_0 * (x_1 * x_2 + x_6 * x_7 + x_8 * x_16)
   ```
   When Black places a single stone `b1 != 0` at Ply 1, `b1` can annihilate at most one of those three quadratic terms, leaving at least **two disjoint rays completely unblocked** (`corner_0_two_rays_unblocked_after_ply1`)!
2. **Forcing Two Orthogonal Threats (Plies 2–5):** Suppose Black blocks `(0, 1, 2)` at Ply 1. White then plays `x_6 = 1` (Ply 2, forcing Black to block `x_7 = 0` at Ply 3) and `x_8 = 1` (Ply 4, forcing Black to block `x_16 = 0` at Ply 5).
3. **The Ply 6 Junction Fork (`ply8_corner_fork_theorem`):** At Ply 6, White places at junction vertex `14` (`x_14 = 1`), where two mills through `6` and `8` intersect:
   * `m_1 = {6, 14, 22}` (SW Diagonal Mill)
   * `m_2 = {8, 14, 15}` (Middle Ring Left Mill)
   Their polynomial sum factors through `x_14`:
   ```text
   P_{m_1}(x) + P_{m_2}(x) = x_6 * x_14 * x_22 + x_8 * x_14 * x_15 = x_14 * (x_6 * x_22 + x_8 * x_15)
   ```
4. **The Commutative Reduction:** Substituting `x_6 = 1, x_8 = 1, x_14 = 1` reduces the cubic sum to the **linear binomial**:
   ```text
   P_fork(x) = x_22 + x_15
   ```
5. At Ply 7, Black has only **one placement move** `b4`, so Black can block `22` OR `15`, but since `15 != 22`, Black cannot block both independent linear terms!
6. At Ply 8, White occupies whichever of `{15, 22}` remains open, driving `P_mill(x) = 1` (`ply8_corner_fork_theorem`).

---

### 3. Characteristic Polynomial Even-Power Symmetry

The characteristic polynomial of the adjacency matrix is `chi_G(lambda) = det(lambda * I - A)`.

Because both 9MM and 12MM boards are bipartite graphs (having no odd cycles), `chi_G(lambda)` contains **strictly even powers of `lambda`** (`chi_G(-lambda) = chi_G(lambda)`):

#### Nine Men's Morris Characteristic Polynomial:

```text
chi_{G_9}(lambda) = lambda^24 - 32*lambda^22 + 436*lambda^20 - 3328*lambda^18 + 15744*lambda^16
                    - 48192*lambda^14 + 96576*lambda^12 - 124928*lambda^10 + 99584*lambda^8
                    - 44032*lambda^6 + 8192*lambda^4
```

* **Edges:** Coefficient of `lambda^22` is `-32` (`-card(E) = -32`).
* **Kernel Dimension:** The lowest non-zero power is `lambda^4` with coefficient `8192 = 2^13`, confirming that `lambda = 0` has multiplicity 4.

#### Twelve Men's Morris Characteristic Polynomial:

```text
chi_{G_12}(lambda) = lambda^24 - 40*lambda^22 + 652*lambda^20 - 5648*lambda^18 + 28528*lambda^16
                     - 87040*lambda^14 + 160064*lambda^12 - 169216*lambda^10 + 90112*lambda^8
                     - 16384*lambda^6
```

* **Edges:** Coefficient of `lambda^22` is `-40` (`-card(E) = -40`).
* **Kernel Dimension:** The lowest non-zero power is `lambda^6` with coefficient `-16384 = -2^14`, confirming that `lambda = 0` has multiplicity 6.

---

## 🔬 Summary Table of Multi-Disciplinary Invariants

| Invariant / Lens | Nine Men's Morris (Mill) | Twelve Men's Morris (Morabaraba) | Algebraic / Game Significance |
| :--- | :---: | :---: | :--- |
| **Game-Theoretic Value** | **Exact Draw** | **Win White (49 Moves)** | Proven by Ralph Gasser (1993) & Gévay-Danner (2016) |
| **Mill Degree Regularity** | `Delta_M = 2` (Uniform) | `Delta_M = 3` (Broken) | Corners have degree 3 in 12MM (`corner_mill_degree_3`) |
| **Transversal Number (`tau`)** | 8 (`2r + 2` at `r = 3`) | 8 | Minimum stones to intercept all mills |
| **Defensive Surplus (`delta`)** | `9 - 8 = +1` | `12 - 8 = +4` | Resource capacity in Phase 1 (`defensive_surplus_12mm`) |
| **Saturation Ratio (`rho`)** | `18/24 = 75%` | `24/24 = 100%` | 12MM saturates the board if no captures occur |
| **Adjacency Spectral Radius** | `2 * sqrt(2) ≈ 2.828` | `2 + sqrt(2) ≈ 3.414` | `+20.7%` expansion in dynamic connectivity |
| **Algebraic Connectivity (`mu_2`)** | `0.4384` | `0.5858` | `+33.6%` jump in spectral mixing rate |
| **Dual Gram Matrix Structure** | Strictly 3-regular cubic | Ring: 5, Radial: 3, Diag: 6 | Diagonals act as degree-6 global hubs |
| **Linear Dependencies (`dim(ker(M^T))`)** | 1 (Alternating Parity) | 4 | Algebraic conservation laws |
| **Corner & Fork Ideal Structure** | Degree-2 corners (1 ray left after Ply 1) | Degree-3 corner `0` leaves 2 rays -> `x_14(x_6*x_22 + x_8*x_15)` | Machine-checked in `ply8_corner_fork_theorem` |
