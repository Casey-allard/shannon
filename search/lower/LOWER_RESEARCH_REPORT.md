# Lower-Bound Frontier Research Report — Shannon Capacity of the 7-Cycle (`Tracks L1–L4`)

**Milestone:** `M4_LowerFrontier` (Features F9 & F10)  
**Target Graph:** 7-Cycle `SimpleGraph.cycleGraph 7` ($C_7$)  
**Lean 4 Certified Lower Bound (Pure Kernel):** `3258822357711717 / 1000000000000000` (`3.258822357711717`, exact downward truncation at $d = 220$)  
**Trusted Computing Base:** Pure Lean 4.32.2 kernel (`{propext, Classical.choice, Quot.sound}` only — zero `sorry`, zero `admit`, zero `native_decide`, zero `Lean.ofReduceBool`)  
**Open-Problem Status:** The exact value of $\Theta(C_7)$ remains open; a strict interval of width `0.058844...` remains between our certified lower bound `3.258822357711717` and Lovász's upper bound $\vartheta(C_7) \approx 3.317667207394$.

---

## 1. Executive Summary & Certified Frontier Table

Across four computational and algebraic research tracks (`L1`–`L4`), we discovered and formally verified in the pure Lean 4 kernel two structural generalizations beyond M3's `HeteroGadget`:

1. **`AuxPartition` / `PartGadget` & Auxiliary-Upgrading Products (`prodXupg1`, `prodXupg2`):** Decoupling an auxiliary code into three pairwise non-close independent blocks `(O, H, V)` requiring only the four opposite-port avoidance invariants (`O` avoids `P0, P1`; `H` avoids `P1`; `V` avoids `P0`) removes `AuxCode`'s unused `H ⊆ N[P0]` and `V ⊆ N[P1]` restrictions. On the aligned product core `prodAlignedCore(g₁, g₂)`, replacing `(H₁ ∪ V₁) × X₂` by `H₁ × (B₂ ∪ P0₂) ∪ V₁ × (B₂ ∪ P1₂)` (`prodXupg1`, and symmetrically `prodXupg2`) strictly lifts the auxiliary cardinality above the `c_k = 367^k` stagnation barrier:
   $$c_{\text{new}} = d_1 c_2 + (h_1 + v_1) a_2, \qquad d_{\text{new}} = d_1 d_2 + (h_1 + v_1) b_2, \qquad h_{\text{new}} = d_1 h_2 + h_1 (a_2 - b_2), \qquad v_{\text{new}} = d_1 v_2 + v_1 (a_2 - b_2).$$
2. **Six-Vertex Quotient Graph `Γ₆` & `PartGadget` `Γ₆^⊠4` Pullback:** Every `PartGadget G` canonically realizes the 6-vertex quotient graph $\Gamma_6$ (`B, P0, P1, O, H, V`), enabling constructive 4-fold pullbacks (`gamma6Pow4_card_le_cycleGraph7_indepNum`) directly on upgraded `PartGadget`s.

Instantiating a compact **11-node shared `PartGadget` DAG** from M3's locked `baseHetero5D` — forming optimal `prodStd` powers $p_9$ ($d = 45$) and $p_{13}$ ($d = 65$), upgrading $u_{22} = \mathrm{prodXupg1}(p_9, p_{13})$ ($d = 110$, whose auxiliary size strictly exceeds $367^{22}$), and squaring $t_{44} = \mathrm{prodStd}(u_{22}, u_{22})$ ($d = 220$) — constructs an independent set in $C_7^{\boxtimes 220}$ of exact 113-digit cardinality

$$N_{220} = 74705260449010907031291311728445696992339746673817850928852859227950431526005228577975175899699338829613565617217,$$

certifying in `ShannonC7/FrontierLower.lean`:

$$\frac{3258822357711717}{1000000000000000} \le \Theta(C_7), \qquad (3258822357711717)^{220} \le 10^{15 \cdot 220} N_{220} < (3258822357711718)^{220}.$$

This strictly improves upon the M3 homogeneous `ValidTuple.star` baseline of `3.258805369885465` at $d = 200$ (`c7_lower_gt_bpz_v1`) by **`+0.0000169878`** and strictly improves upon our earlier `Γ₆^⊠4` pullback (`3.258821451811711`, $d = 225$) by **`+0.0000009059`** at a smaller dimension ($d = 220$) with zero new 5D trie witnesses. It remains below both the external Aug 10, 2026 `native_decide` benchmark of Buys, Polak, and Zuiddam (`3.258827985920007`, $d = 500$) and the unrefereed Aug 31, 2026 preprint benchmark of Ravi Tandon (`3.258832620353`, $d = 500$).

### Unified Lower-Bound Progression Table

| Construction / Milestone | Power $d$ | Exact Code Size / Digits | Downward-Truncated Bound on $\Theta(C_7)$ | Status |
|---|---:|---|---:|---|
| Single-letter code (`alpha_c7_pow1`) | 1 | `3` | `3.000000000000` | Lean 4 certified (pure kernel) |
| Baumert et al. (`alpha_c7_pow2`) | 2 | `10` | `3.162277660168` | Lean 4 certified (pure kernel) |
| Baumert et al. (`alpha_c7_pow3_ge`) | 3 | `33` | `3.207534329995` | Lean 4 certified (pure kernel) |
| Vesel–Žerovnik (`alpha_c7_pow4_ge`) | 4 | `108` | `3.223709795470` | Lean 4 certified (pure kernel) |
| Polak–Schrijver (`c7_lower_polak_schrijver`) | 5 | `367` | `3.257865966783` | Lean 4 certified (pure kernel) |
| Itty et al. (`c7_lower_itty`, Jul 2026) | 10 | `134,753` | `3.258020737293` | Lean 4 certified (pure kernel) |
| Gao (`c7_lower_gao`, Jul 2026) | 200 | 103 digits | `3.258789153908` | Lean 4 certified (pure kernel) |
| BPZ v1 (`c7_lower_bpz_v1_15`, Jul 31, 2026) | 200 | 103 digits | `3.258805369885465` | Lean 4 certified (pure kernel) |
| M4 Track L2 `Γ₆^⊠4` Pullback (prior M4 pass) | 225 | 116 digits | `3.258821451811711` | Unformalized computational exploration |
| **M4 Track L2 `PartGadget` `prodXupg1` (`c7_lower_frontier`)** | **220** | **113 digits** | **`3.258822357711717`** | **Lean 4 certified (pure kernel)** |
| Buys, Polak & Zuiddam v2 (Aug 10, 2026) | 500 | 257 digits | `3.258827985920007` | External literature benchmark |
| Ravi Tandon preprint (Aug 31, 2026) | 500 | explicit $d=500$ | `3.258832620353` | External literature benchmark |

*(Note: our earlier `Γ₆^⊠4` pullback theorem `gamma6Pow4_card_le_cycleGraph7_indepNum` remains formally proved and generalized to `PartGadget` inside `ShannonC7/FrontierLower.lean`, while the concrete `d = 225` instance was superseded by our strictly higher `d = 220` `PartGadget` certificate.)*

### Upper-Bound Reference Context (Separately Certified in M2)

| Upper Bound | Value | Status |
|---|---:|---|
| Lovász $\vartheta(C_7) = \frac{7\cos(\pi/7)}{1+\cos(\pi/7)}$ (`c7_upper_lovasz`, `c7_upper_rational`) | `< 3.317667207395` (`3.317667207394...`) | Lean 4 certified (pure kernel) |

---

## 2. Track L2 — `AuxPartition` / `PartGadget` & Weighted Quotient Graph $\Gamma_6$

### 2.1 Breaking the `c_k = 367^k` Barrier via `AuxPartition`

In M3's `HeteroGadget`, `AuxCode` required `H = X ∩ N[P0]` and `V = X ∩ N[P1]`, forcing every product auxiliary set to remain `X₁ × X₂` of size `c₁ c₂ = 367^k`. Examining both `prodAlignedCore` and the 6-vertex quotient graph $\Gamma_6$ (`C_5` cycle `B - H - P0 - P1 - V - B` plus pendant leaf `O - B`) reveals that neither construction ever requires `H ⊆ N[P0]` or `V ⊆ N[P1]` — they require ONLY:

1. `O, H, V` are independent sets in `G` that are pairwise non-close (`not_close_OH`, `not_close_OV`, `not_close_HV`), and
2. `O` avoids `N[P0] ∪ N[P1]`, `H` avoids `N[P1]`, and `V` avoids `N[P0]`.

Under `prodAlignedCore(g₁, g₂)` (where $P_0^{\text{new}} = (P_{0,1} \times O_2) \cup (O_1 \times P_{0,2})$ and $P_1^{\text{new}} = (P_{1,1} \times O_2) \cup (O_1 \times P_{1,2})$), this unlocks **579** maximal independent auxiliary partitions inside $(\Gamma_6 \boxtimes \Gamma_6) \setminus F$, highlighted by three clean constructive operators formalized in `ShannonC7/FrontierLower.lean`:

- **`PartGadget.prodStd`:** $O_{\text{new}} = (O_1 \times O_2) \cup (H_1 \cup V_1) \times (H_2 \cup V_2)$, $H_{\text{new}} = (H_1 \times O_2) \cup (O_1 \times H_2)$, $V_{\text{new}} = (V_1 \times O_2) \cup (O_1 \times V_2)$ ($c_{\text{new}} = c_1 c_2$).
- **`PartGadget.prodXupg1`:** $O_{\text{new}} = (O_1 \times O_2) \cup (H_1 \times P_{0,2}) \cup (V_1 \times P_{1,2})$, $H_{\text{new}} = (O_1 \times H_2) \cup (H_1 \times B_2)$, $V_{\text{new}} = (O_1 \times V_2) \cup (V_1 \times B_2)$, upgrading $c_{\text{new}} = d_1 c_2 + (h_1 + v_1) a_2$.
- **`PartGadget.prodXupg2`:** Symmetric right-upgraded counterpart with $c_{\text{new}} = c_1 d_2 + a_1 (h_2 + v_2)$.

### 2.2 SDP Ceilings, Pareto DP Campaign, & Winning Progression

Using `cvxpy` + `Clarabel` on the base gadget `baseHetero5D` (`w_1 = (359, 8, 8, 322, 19, 26)`), we measured the weighted Lovász theta ceilings of the quotient abstractions (upper relaxations of the quotient subgraphs, not lower bounds on $\Theta(C_7)$):

| Quotient Abstraction | Vertices / Edges | Weighted $\vartheta(\Gamma, w)$ | $\vartheta(\Gamma, w)^{1/5}$ Relaxation Ceiling | Status |
|---|---:|---:|---:|---|
| Coarse quotient $\Gamma_6$ (`baseHetero5D`) | 6 / 6 | `367.817754244615` | `3.259316518494` | Unformalized computational exploration |
| Per-port quotient $\Gamma_Q$ (all 8 ports, 23 $X$-signatures) | 40 / 62 | `368.430320307871` | `3.260401413374` | Unformalized computational exploration |

Key structural findings across Track L2:

1. **Pure M3 `HeteroDAG` saturation:** Homogeneous `ValidTuple.star` and M3 `HeteroDAG` (`prod`, `prodAligned`, `flip`, `X_322`, `X_365_333`, `X_359_359`, root `oneSidedTerminal`) all peak at BPZ v1 (`3.258805369885465`, $d = 200$).
2. **Residual complement rigidity & 5D `Y_1` obstruction:** $K_1 = V(C_7^5) \setminus N[O_1]$ (`104` vertices) satisfies $\alpha(K_1) = \chi_f(K_1) = 45$ identically ($\Theta(K_1) = 45$). An exhaustive `14.6 s` C++17 $\operatorname{Aut}(C_7^5)$ scan across all 108 toggles of $R$ proved that all 32 zero-$F_R$ 367-word codes hit $F_X$ at $\ge 8$ vertices, obstructing a direct 5D product $Y_1^k$.
3. **Track L2 Progression (`PartGadget` + `Γ₆^⊠m`):** Exhaustive Pareto DP over all 407 weight-distinct maximal independent sets of $(\Gamma_6 \boxtimes \Gamma_6) \setminus F$ up to $k = 250$ ($d = 1250$) plus CP-SAT exploration of $\Gamma_6^{\boxtimes 3}$ (`d = 15` optimal `49,496,015`, `c = 49,432,527 > 367^3`) and $\Gamma_6^{\boxtimes 4}$ yielded the following hierarchy:

| Track L2 Construction | Power $d$ | DAG Nodes / Terms | Downward-Truncated Rate | Status |
|---|---:|---|---:|---|
| `ValidTuple.star` (`p_20 × p_20`) | 200 | 9 nodes | `3.258805369885465` | Lean 4 certified (pure kernel) |
| `Γ₆^⊠3` optimal pullback (`ks = [12,14,12]`) | 190 | 21 terms | `3.258816562266969` | Unformalized computational exploration |
| `Γ₆^⊠4` pullback (`ks = [14,9,11,11]`) | 225 | 53 terms | `3.258821451811711` | Unformalized computational exploration |
| **`PartGadget` `prodStd(prodXupg1(p_9, p_13), prodXupg1(p_9, p_13))`** | **220** | **11 nodes** | **`3.258822357711717`** | **Lean 4 certified (pure kernel)** |

The winning 11-node `PartGadget` witness is stored in `search/lower/witnesses/frontier_c7_d220_partgadget.json`, reproduced deterministically by `search/lower/track_l2_search.py`, independently verified by `search/lower/verify_witness.py`, and emitted deterministically into `ShannonC7/FrontierLower.lean` by `search/lower/emit_frontier_lean.py`.

---

## 3. Track L1 — Direct $C_7^5$ Search, Circular-Graph Uniqueness & Exact $3^5 = 243$ Manifold

Reproducible C++17 implementations are archived in `search/lower/track_l1_circular.cpp` and `search/lower/track_l1_ils_bfs.cpp` (compiled single-threaded with `g++ -O3 -march=native -std=c++17`). Known peer-reviewed bounds on the fifth power remain $367 \le \alpha(C_7^{\boxtimes 5}) \le 401$. Our campaign (`~6.9 min` single-threaded C++17 + Box-Clique CP-SAT) found no independent set of size 368 and no 5D valid tuple improving upon canonical `(367, 8, 367, 322)`, while establishing four structural results:

1. **Sub-Integer Phase Quantization & Circular-Graph Uniqueness (`track_l1_circular.cpp`):** Exact reproduction of Polak–Schrijver's 367-word code (`core = 327`, `res = 71`, `+40 = 367`, $E_{\text{conf}} = 32.940$, $E_{\text{core}} = 316.120$) requires unified sub-integer phase quantization `c[j] = ((7 * ((t * g[j]) % 382) + sigma[j]) % (7*382)) / 382` with `g = (1, 7, 49, 343, 109)` and `sigma = (283, 100, 283, 100, 283)`. Exhaustive 256-bit 4-set-cover enumeration proved $C_{108, 382}^5$ is the unique exact cyclic subgroup with $n/k \le 3.60$ across $n \in [365, 500]$.
2. **Large-Window Local Rigidity of Polak–Schrijver $R$:** Exact $2^5$-box-clique CP-SAT (`num_search_workers = 1`) proved local optimality at size `367` across all 5 coordinate 2-slices (`drop = 105..107`, `free = 653..719`) and spatial balls up to `K = 130` destroyed words (`free = 1,382`). *(Local neighborhood optimality only; does not establish a global upper bound on $\alpha(C_7^{\boxtimes 5})$.)*
3. **Complete Exact $3^5 = 243$-Code `(1,1)`-Swap Manifold (`track_l1_ils_bfs.cpp`):** Exhaustive `(1,1)`-swap BFS from $R$ terminated completely at exact $3^5 = 243$ labeled 367-word codes (`max b = 10` at the $C_5$-symmetric apex $R_{\{5,7\}}$), with exact `b`-histogram `b=5: 32, b=6: 80, b=7: 80, b=8: 40, b=9: 10, b=10: 1`, collapsing into `51` $\operatorname{Aut}(C_7^5)$ classes.
4. **Exhaustive Auxiliary Obstruction Across Non-PS and $b \in \{9, 10\}$ Classes:** Across `20.6 billion` `(automorphism, bipartition)` pairs, the 7 non-PS classes peak at `(367, 7, 367, 327)` (`3.258677296019`) and `(367, 5, 367, 345)` (`3.258574194777`), while both `b = 9` classes and the unique `b = 10` apex admit zero non-trivial zero-hit auxiliaries.

---

## 4. Track L3 — Fraction-Graph $E_{p/q}$ Cyclic-Subgroup Search ($d = 6, 7, 8, 10$)

Reproducible C++17 verification code is archived in `search/lower/track_l3_lattice.cpp`. Across `127.7M` subgroup evaluations (`168.87 s` single-threaded C++17), all reported sets were independently verified conflict-free in $C_7^{\boxtimes d}$:

| Dim $d$ | Search Domain ($n$, $n/k$) | Subgroup Evals | $C_{k,n}^d$ Hits | Best Verified Size | Exact Floor $\alpha^{1/d}$ | Trivial Product | Status |
|---:|---|---:|---:|---:|---:|---:|---|
| 6 | Prime $n \in [1120, 1340]$ + ILS polish | 77,052,195 | 9 | `1,102` | `3.213884504746` | `1,101` (`367 × 3`) | Unformalized computational exploration |
| 7 | $n \in [3670, 4400]$, $[3.50, 3.60]$ | 39,210,816 | 0 | `3,216` | `3.169896983500` | `3,670` (`367 × 10`) | Unformalized computational exploration |
| 8 | $n \in [12111, 14000]$, $[3.50, 3.60]$ | 8,018,500 | 0 | `7,876` | `3.069292042540` | `12,111` (`367 × 33`) | Unformalized computational exploration |
| 10 | $n \in [134753, 155000]$, $[3.50, 3.58]$ | 3,444,040 | 0 | `52,675` | `2.965926978428` | `134,753` (Itty) | Unformalized computational exploration |

The $d = 6$ prime-order subgroup `n = 1151, g = (1, 170, 267, 94, 329, 274), s = (82, 82, 82, 82, 82, 82)` (`clean = 914`) polished via direct $C_7^6$ tabu-ILS to `1,102` words (`0` conflicts), strictly exceeding `367 × 3 = 1,101`, though far below Polak–Schrijver's capacity threshold (`1,196`). For $d \ge 7$, rank-1 cyclic subgroups hit an exponential uncovered-shift barrier $(k - 1)(2k/n)^{d-1} \in \{35.1, 64.0, 226.4\}$, confirming that Track L2 recursive gadget methods dominate direct lattice search at high dimensions.

---

## 5. Track L4 — Heuristic $C_7^{\boxtimes 4}$ Benchmark Probe

Reproducible C++17 bit-parallel ILS source is archived in `search/lower/track_l4_c7pow4.cpp`. Known published bounds on the fourth strong power remain $108 \le \alpha(C_7^{\boxtimes 4}) \le 115$ (with an unrefereed 2026 exclusion candidate suggesting $112$). Across `130.05 s` of single-threaded search (`85.00 s` mixed ILS with `1,341,242` iterations, `58,296` `(1,2)`-swaps, `188` exact 2-tight-indexed `(2,3)`-swaps discovering `22,769` distinct `108`-word independent sets; `35.05 s` 16-clique CP-SAT LNS proving `18/33` destroyed-slice subproblems locally optimal at `108`; `10.00 s` fresh-only control hitting `108` zero times), all 40 sampled `108`-word sets shared the uniform coordinate-slice histogram `(15, 15, 15, 15, 16, 16, 16)` on every axis.

Heuristic/local search found independent sets of size up to 108 in $C_7^{\boxtimes 4}$ and did not discover a size-109 witness; this heuristic search does not establish an upper bound on $\alpha(C_7^{\boxtimes 4})$.

---

## 6. Reproducibility & Verification Commands

All Feature F9 tooling uses strictly Python 3.12 standard library with zero third-party runtime dependencies:

```bash
# 1. Regenerate canonical Track L2 witness JSON (pure stdlib)
python3 -B search/lower/track_l2_search.py

# 2. Run independent zero-shared-code verifier self-test (75 positive & negative mutation tests)
python3 -B search/lower/verify_witness.py --self-test

# 3. Verify canonical witness JSON & cross-check emitted ShannonC7/FrontierLower.lean
python3 -B search/lower/verify_witness.py \
  --witness search/lower/witnesses/frontier_c7_d220_partgadget.json \
  --verify-lean ShannonC7/FrontierLower.lean

# 4. Verify byte-for-byte deterministic Lean 4 code emission
python3 -B search/lower/emit_frontier_lean.py --out /tmp/FrontierLower_check.lean
diff -u ShannonC7/FrontierLower.lean /tmp/FrontierLower_check.lean && rm -f /tmp/FrontierLower_check.lean

# 5. Pure-kernel Lean 4 build & axiom audit (1 thread, flock-guarded)
flock /tmp/shannon_c7_lake.lock timeout 300 bash -c \
  'cd /home/antigravity/shannon-c7 && LEAN_NUM_THREADS=1 lake build --no-ansi ShannonC7.FrontierLower ShannonC7.Tests.FrontierLowerTests'
flock /tmp/shannon_c7_lake.lock timeout 300 bash -c \
  'cd /home/antigravity/shannon-c7 && LEAN_NUM_THREADS=1 ./scripts/verify_axioms.sh --verbose ShannonC7.FrontierLower ShannonC7.Tests.FrontierLowerTests'
```
