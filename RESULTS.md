# Shannon Capacity of the 7-Cycle ($\Theta(C_7)$) — Verified Results Summary

**Public Lean 4 Entrypoint:** `ShannonC7/Main.lean` (`leanprover/lean4:v4.32.2`, `mathlib4@v4.32.2`)  
**Canonical Target Graph:** `SimpleGraph.cycleGraph 7` with textbook strong powers `strongPowPi` (`Fin d → Fin 7`)  
**Trusted Computing Base (TCB):** Pure Lean 4 kernel — axioms strictly $\subseteq \{\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}\}$ (zero `sorry`, zero `admit`, zero `partial`, zero `native_decide`, zero `Lean.ofReduceBool`)

---

## 1. Open-Problem Status & Certified Sandwich

The exact Shannon capacity $\Theta(C_7)$ remains an open problem. No proof in this repository determines an exact value for $\Theta(C_7)$ or proves $\Theta(C_7) < \vartheta(C_7)$; both questions are stated formally as `OpenQuestion_StrictGap` and `OpenQuestion_ExactValue` in `ShannonC7/Main.lean`.

Our pure-kernel Lean 4 formalization proves the certified sandwich (`c7_shannonCapacity_sandwich` and `c7_upper_rational`):

$$\frac{3258822357711717}{1000000000000000} = 3.258822357711717 \;\le\; \Theta(C_7) \;\le\; \vartheta(C_7) = \frac{7\cos(\pi/7)}{1+\cos(\pi/7)} < \frac{3317667207395}{1000000000000}.$$

The remaining strict gap between our certified lower bound `3.258822357711717` and Lovász's upper bound $\vartheta(C_7) \approx 3.317667207394$ has width approximately `0.05884485`.

---

## 2. Formally Certified Theorems in Lean 4 (Pure Kernel)

### 2.1 Core Theory & Fekete Limit
- **`shannonCapacity` & `strongPowPi`** (`ShannonC7/Defs.lean`): Textbook strong powers on `Fin d → V`, isomorphic to right-nested `strongPow` (`strongPowEquivPi`), and computable `C7` on `ZMod 7` isomorphic to `SimpleGraph.cycleGraph 7` (`c7IsoCycleGraph`).
- **`c7_shannonCapacity_tendsto`** (`ShannonC7/Fekete.lean`, `ShannonC7/Main.lean`): Fekete limit equivalence $\lim_{d \to \infty} \alpha(C_7^{\boxtimes d})^{1/d} = \Theta(C_7)$.

### 2.2 Upper Bounds, Galois Unattainability & Haemers Obstruction
- **`c7_upper_lovasz`** (`ShannonC7/LovaszC7.lean`): $\Theta(C_7) \le \vartheta(C_7) = \frac{7\cos(\pi/7)}{1+\cos(\pi/7)}$, proved via a rank-4 Fourier sum-of-squares `LovaszCert` closed under Kronecker products (`LovaszCert.prod`, `LovaszCert.pow`).
- **`lovaszThetaC7_cubic` & `c7_upper_rational`** (`ShannonC7/CubicBounds.lean`): Minimal cubic $t^3 + 7t^2 - 49t + 49 = 0$ and zero-$\pi$ rational enclosure $\Theta(C_7) < 3317667207395 / 10^{12}$.
- **`c7_lovasz_unattainable`** (`ShannonC7/CubicBounds.lean`): For every $d \ge 1$, $\vartheta(C_7)^d \notin \mathbb{Q}$, hence $\alpha(C_7^{\boxtimes d})^{1/d} < \vartheta(C_7)$ strictly.
- **`shannonCapacity_le_haemers_rank` & `haemers_minrank_c7_ge_four`** (`ShannonC7/Haemers.lean`): General Haemers matrix-rank bound over any field $\mathbb{F}$, plus $\operatorname{minrank}_{\mathbb{F}}(C_7) \ge 4$.
- **Generalizations** (`ShannonC7/Lovasz.lean`, `ShannonC7/LovaszC7.lean`, `ShannonC7/Main.lean`):
  - `c5_shannonCapacity_eq_sqrt_five`: $\Theta(C_5) = \sqrt{5}$.
  - `oddCycle_upper_lovasz`: $\Theta(C_{2k+1}) \le \vartheta(C_{2k+1})$ for all $k \ge 1$.
  - `c7_compl_sandwich`: $17^{1/4} \le \Theta(\overline{C_7}) \le 1 + \sec(\pi/7)$.

### 2.3 Exact Finite Powers & Finite-Power Upper Bounds
| Power $d$ | Lean 4 Certified Result | Primary Declaration(s) |
|---:|---|---|
| 1 | $\alpha(C_7) = 3$ (exact) | `alpha_c7_pow1` |
| 2 | $\alpha(C_7^{\boxtimes 2}) = 10$ (exact) | `alpha_c7_pow2` |
| 3 | $\alpha(C_7^{\boxtimes 3}) = 33$ (exact) | `alpha_c7_pow3`, `alpha_c7_pow3_le` (`AlphaC7Cube.lean`) |
| 4 | $108 \le \alpha(C_7^{\boxtimes 4}) \le 115$ | `alpha_c7_pow4_ge`, `alpha_c7_pow4_le_115` (`FinitePowerUpper.lean`) |
| 5 | $367 \le \alpha(C_7^{\boxtimes 5}) \le 401$ | `alpha_c7_pow5_ge_367` (`Trie7`), `alpha_c7_pow5_le_401` |
| $4 \to 5$ | $\alpha(C_7^{\boxtimes 4}) \le 112 \implies \alpha(C_7^{\boxtimes 5}) \le 392$ (conditional) | `alpha_c7_pow5_le_392_of_pow4_le_112` |

### 2.4 Pure-Kernel Frontier Lower Bound (`d = 220`)
Using a pure-kernel Radix-7 Trie (`TrieVerifier.lean`), exact integer powering (`Decimal.lean`), and the generalized `AuxPartition` / `PartGadget` auxiliary-upgrading product `prodXupg1` (`FrontierLower.lean`), an 11-node DAG constructs an independent set in $C_7^{\boxtimes 220}$ of exact 113-digit cardinality `frontierCard`, proving:

- `c7_lower_num = 3258822357711717`, `c7_lower_den = 1000000000000000`
- `c7_lower_frontier`: `3258822357711717 / 1000000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7)` (`3.258822357711717`), strictly surpassing the homogeneous `ValidTuple.star` peak `3.258805369885465` at $d = 200$ (`c7_lower_gt_bpz_v1`).

---

## 3. External Literature Benchmarks & Computational Research Context

External literature benchmarks (not formalized in this repository) are recorded separately for context:

| Benchmark | Power $d$ | Reported Bound | Status |
|---|---:|---:|---|
| Buys, Polak & Zuiddam v2 (Aug 10, 2026) | 500 | `3.258827985920007` | External literature benchmark |
| Ravi Tandon preprint (Aug 31, 2026) | 500 | `3.258832620353` | External literature benchmark |

Our certified bound `3.258822357711717` lies below both external benchmarks above.

Detailed computational findings are documented in:
- **`search/lower/LOWER_RESEARCH_REPORT.md`:** Tracks L1–L4 (exact $3^5 = 243$-code `(1,1)`-swap manifold in $C_7^{\boxtimes 5}$, `PartGadget` / `Γ₆^⊠4` recursive constructions, fraction-graph lattices in $d = 6, 7, 8, 10$, and $C_7^{\boxtimes 4}$ ILS probe).
- **`search/upper/UPPER_RESEARCH_REPORT.md`:** Tracks U1–U2 (exhaustive 1,016-orbit census of all $16{,}672{,}544$ size-33 sets in $C_7^{\boxtimes 3}$, 4,095-cut LP barrier at $115.0$ for $C_7^{\boxtimes 4}$, and the 4-gate / 8-graph obstruction testbed confirming Bukh–Cox, Bi–Tang, Sason Gilbert-32, Schläfli complement `srg(27,10,1,5)`, and Petz–Rényi barriers). The unrefereed $\alpha(C_7^{\boxtimes 4}) \le 112$ candidate remains open and unproved here.

---

## 4. Independent Verification & Reproducibility

```bash
# 1. Build entire library including ShannonC7.Main
lake build ShannonC7

# 2. Run 3-stage static hygiene + .olean freshness + trustLevel=0 C++ kernel replay & axiom audit
./scripts/verify_axioms.sh --verbose

# 3. Verify lower-bound witness JSON & cross-check FrontierLower.lean
python3 -B search/lower/verify_witness.py --self-test
python3 -B search/lower/verify_witness.py \
  --witness search/lower/witnesses/frontier_c7_d220_partgadget.json \
  --verify-lean ShannonC7/FrontierLower.lean

# 4. Run full opaque-box 4-tier E2E suite (164 tests) & isolated self-tests (18 suites)
bash verify/run_e2e.sh --self-test
bash verify/run_e2e.sh --all --json-out /tmp/e2e_report.json
```
