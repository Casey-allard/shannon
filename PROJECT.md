# Project: Shannon Capacity of the 7-Cycle ($\Theta(C_7)$) in Lean 4

**Status:** Active Execution (Step 0 Survey Complete → Phase 2 Milestones Launched)  
**Project Root:** `/home/antigravity/shannon-c7`  
**Original Request:** `/home/antigravity/.agents/teamwork/ORIGINAL_REQUEST.md`  
**Attached Research Reference:** `/home/antigravity/7-Cycle_Shannon_Capacity_Formalization.md`  
**Last Updated:** 2026-11-26T06:02:00Z

---

## 0. Verified Mathematical Frontier (November 2026)

The exact Shannon capacity of the 7-cycle $\Theta(C_7)$ remains an open problem (70 years since Shannon 1956):
$$3.258827985920007\ldots \text{ (BPZ Aug 2026 Lean 4.32.2, } d=500\text{, } \texttt{native\_decide}\text{)} \;\le\; 3.258832620353\ldots \text{ (Tandon Aug 31, 2026 unrefereed, } d=500\text{)} \;\le\; \Theta(C_7) \;\le\; \vartheta(C_7) = \frac{7\cos(\pi/7)}{1+\cos(\pi/7)} = 3.317667207394096\ldots$$

- **Exact known finite powers:** $\alpha(C_7) = 3$, $\alpha(C_7^{\boxtimes 2}) = 10$, $\alpha(C_7^{\boxtimes 3}) = 33$, $108 \le \alpha(C_7^{\boxtimes 4}) \le 115$ (unrefereed Oct 5, 2026 Evidence Press candidate $\le 112$), $367 \le \alpha(C_7^{\boxtimes 5}) \le 401$ (or $\le 392$ conditional on $\alpha(C_7^{\boxtimes 4}) \le 112$).
- **Galois unattainability:** $t = \vartheta(C_7)$ satisfies irreducible $t^3 + 7t^2 - 49t + 49 = 0$ with three real roots of distinct moduli, so $\forall d \ge 1,\; \alpha(C_7^{\boxtimes d})^{1/d} < \vartheta(C_7)$ strictly.
- **Proven upper-bound obstructions:** Bukh–Cox (2019, Prop. 4 & Cor. 10) blocks all Haemers/fractional-Haemers bounds over all fields and all powers at $\ge 3.5$; Bi–Tang (2019, Thm. 3) + Sason (2025) blocks all product-closed conic PSD tightenings at $\ge \vartheta(C_7)$; Mghirbi–Douglas (Oct 2026) quantum Petz–Rényi spectral points all satisfy $\vartheta_\alpha \ge \vartheta$.
- **Strategic objectives:**
  1. Deliver a **complete, textbook-canonical, zero-`sorry`, pure-kernel** (`{propext, Classical.choice, Quot.sound}` ONLY — zero `native_decide` / `Lean.ofReduceBool`!) Lean 4 formalization of Shannon capacity on Mathlib's `SimpleGraph.cycleGraph 7` and `Fin d → V` strong powers, unifying Lovász's $\vartheta(C_7)$ upper bound (absent from Mathlib and `spectra-research/shannon-capacity-lean`), arbitrary-precision cubic rational enclosure, Galois unattainability, Haemers bound & obstruction, Fekete limit equivalence, exact small powers $\alpha(C_7)=3, \alpha(C_7^2)=10, \alpha(C_7^3)=33$, Radix-7 Trie pure-kernel verification, and constructive `ValidTuple.star` + heterogeneous & multi-port layered substitution theorems.
  2. Execute a disciplined, compiled **C++17/Rust lower-bound frontier campaign** targeting a **new world record strictly beating `3.258832620353`** (via $a=368$ in $C_7^5$, $b \ge 9$ private pairs, $d \ge 324$ auxiliary optimization, heterogeneous Pareto-DP, layered interior-pair auxiliary upgrading, and $C_7^6/C_7^7/C_7^{10}$ fraction-graph lattices), and **formally verify the strongest achieved bound in Lean 4** (strictly surpassing BPZ's Lean record `3.258827985920007` and targeting `> 3.258832620353`).
  3. Execute an **honest, barrier-aware upper-bound campaign**: machine-verify exact $\alpha(C_7^3) = 33$ in Lean 4, independently audit & probe tightening $\alpha(C_7^4) \le 112 \implies \alpha(C_7^5) \le 392$, and evaluate non-conic submultiplicative spectral/tensor-rank/operator-norm candidates against an automated obstruction testbed ($C_5$, Sason's 32-vertex Gilbert graph, $\mathrm{srg}(27,10,1,5)$).

---

## 1. Architecture

### 1.1 Dual-Track Structure
- **Implementation Track (`M1`–`M6`)**:
  - `M1` (Toolchain + Core Theory) → parallel `{M2 (Upper Theory), M3 (Lower Engine & Trie Verifier)}` → parallel `{M4 (Lower Frontier Search & Cert), M5 (Upper Frontier Search, α(C7^3)=33 & α(C7^4) Audit)}` → `M6` (`Main.lean` integration + Phase 1 E2E Tiers 1–4 + Phase 2 Tier 5 Adversarial Hardening).
- **E2E Testing Track (`E2E_Track`)**:
  - Runs in parallel, independently deriving opaque-box 4-tier verification suite from `ORIGINAL_REQUEST.md` and `PROJECT.md` public contracts (`TEST_INFRA.md` → `shannon-c7/verify/` → `TEST_READY.md`).

### 1.2 Hardware, Toolchain & Build Guardrails
- **VM Resources:** 2 Intel Xeon vCPUs (AVX2/FMA/BMI2/POPCNT), 7.8 GiB RAM + 8.0 GiB swap, 85 GiB free disk, no GPU, passwordless `sudo`.
- **Lean 4 Pin:** `leanprover/lean4:v4.32.2` + `mathlib4` `rev = "v4.32.2"`.
- **CRITICAL Mathlib Cache Override:** `mathlib4 v4.32.2` defaults to the retired Azure blob endpoint (HTTP 404). ALWAYS fetch precompiled `.olean`s with:
  ```bash
  MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4-master lake exe cache get
  ```
  **NEVER compile Mathlib from source** on 2 vCPUs.
- **Memory & Concurrency Discipline:** NEVER `import Mathlib` wholesale (use targeted leaf imports only). Use `lake build -j 2` (and `lake build -j 1` on heavy certificate modules) to stay safely inside 7.8 GiB physical RAM.
- **Trusted Computing Base (TCB) Standard:** ALL core theorems, Lovász upper bound, Galois unattainability, small powers, and `Trie7`-based lower-bound certificates MUST verify in the **pure Lean 4 kernel** with axioms strictly $\subseteq \{\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}\}$ — **ZERO `sorry`, ZERO `admit`, ZERO custom `axiom`, ZERO `native_decide` / `Lean.ofReduceBool`**.

---

## 2. Feature Inventory

Every Survey feature is assigned an owning Milestone (ZERO unassigned):

| # | Feature | Description | Milestone | Source |
|---|---------|-------------|-----------|--------|
| F1 | Toolchain & Build/Solver Environment | Install `elan` + Lean `v4.32.2` + cached Mathlib `v4.32.2` (`MATHLIB_CACHE_GET_URL`), init `/home/antigravity/shannon-c7/`, `uv` Python venv + solvers, `scripts/verify_axioms.sh` | M1 | survey (env, spec) |
| F2 | Core Shannon Capacity & Fekete Library | `strongProd` (`⊠`), `strongPow`, `strongPowPi` (`Fin d → V`), `strongPowEquivPi`, computable `C7 ≃g SimpleGraph.cycleGraph 7 ≃g circulantGraph {1}`, `shannonCapacity` (`sSup`, `0 < d`), `BddAbove`, Fekete `sSup = lim` (`shannonCapacity_tendsto`), `sliceDoubleCount` | M1 | survey (spec, math) |
| F3 | Lovász Upper-Bound Engine & Exact $\vartheta(C_7)$ | General Kronecker-multiplicative `LovaszCert` (`W ii ≤ 1`), Orthonormal Rep bridge, $\Theta(C_5) = \sqrt{5}$ warm-up, Rank-4 Fourier SoS proof of $\Theta(C_7) \le \frac{7\cos(\pi/7)}{1+\cos(\pi/7)}$, zero-$\pi$ cubic rational enclosure `< 3317667207395 / 10^12` | M2 | survey (spec, math) |
| F4 | Galois Unattainability & Haemers Obstruction | Irreducible cubic $t^3 + 7t^2 - 49t + 49 = 0$, proof of $\forall d \ge 1,\; \alpha(C_7^d)^{1/d} < \vartheta(C_7)$; general Haemers minrank bound $\Theta(G) \le \operatorname{rank}_{\mathbb{F}}(M)$ + $\operatorname{minrank}_{\mathbb{F}}(C_7) \ge 4$ | M2 | survey (spec, math) |
| F5 | Generalizations (Upper): $\overline{C_7}$ & Odd Cycles $C_{2k+1}$ | Upper bounds $\Theta(\overline{C_7}) \le 1 + \sec(\pi/7)$ and general odd-cycle $\Theta(C_{2k+1}) \le \vartheta(C_{2k+1})$ | M2 | survey (spec) |
| F6 | Pure-Kernel Radix-7 Trie Verifier & Exact Decimal Bridge | `Trie7 d` inductive trie + soundness proofs for `isIndep`, `disjoint`, neighborhood/`ValidTuple` checks (pure kernel, zero `native_decide`); exact integer power lemma `num^d ≤ den^d * N → num/den ≤ Θ(G)` | M3 | survey (math, spec) |
| F7 | Certified Small Powers ($d=1..5$) & $\overline{C_7}$ Lower Bound | Exact $\alpha(C_7)=3$, $\alpha(C_7^2)=10$; lower bounds $\alpha(C_7^3)\ge 33$, $\alpha(C_7^4)\ge 108$, $\alpha(C_7^5)\ge 343$ (linear), $\alpha(C_7^5)\ge 367$ (Polak–Schrijver, pure-kernel `Trie7`); $\alpha(\overline{C_7}^4)\ge 17$ | M3 | survey (spec, math) |
| F8 | Constructive `ValidTuple.star` & Heterogeneous/Layered Engine | Full constructive proof of `ValidTuple.star` (`b≤a ∧ d≤c`, $\Pi(\tau_1\star\tau_2)=\Pi(\tau_1)\star\Pi(\tau_2)$, link to `shannonCapacity`); constructive `HeteroGadget` (asymmetric/terminal recursion) & `PortSystem` (multi-port / layered interior-pair auxiliary upgrading); Itty ($134{,}753$), Gao ($3.258789$), BPZ v1 ($3.258805$) | M3 | survey (spec, math) |
| F9 | Dual Exact Verifier & Automated Lean Certificate Emitter | Independent Python exact-integer verifier (conflicts, privacy, `p^d ≤ N * q^d`) + automatic `Trie7` / `ValidTuple` / `HeteroLayered` Lean 4 codegen | M4 | survey (spec, math) |
| F10 | Frontier Lower-Bound Computational Campaign (Tracks L1–L4) & `FrontierLower.lean` | C++17/Rust search: Track L1 ($C_7^5$ $a=368$, $b\ge 9$, $d\ge 324$), Track L2 (heterogeneous Pareto DP & layered interior-pair upgrading, $d=500\text{--}2000$), Track L3 ($E_{p/q}$ lattices $d=6,7,8,10$), Track L4 ($C_7^4 \ge 109$); pure-kernel Lean 4 proof of strongest bound (target: beat BPZ `3.258827985920007` and Tandon `3.258832620353`) | M4 | survey (spec, math) |
| F11 | Exact $\alpha(C_7^3) = 33$ Lean Proof & $\alpha(C_7^4) \le 112$ Audit | Symmetry-reduced C++17 refutation of size 34 in $C_7^3$ emitted as pure-kernel Lean 4 proof `alpha_c7_pow3 : ... = 33`; independent C++17/ILP/SAT audit & tightening probe of $\alpha(C_7^4) \le 112 \implies \alpha(C_7^5) \le 392$ | M5 | survey (spec, math) |
| F12 | Obstruction-Gated Asymptotic Upper-Bound Research | Automated obstruction testbed ($C_5$, Sason Gilbert-32, $\mathrm{srg}(27,10,1,5)$, $C_7$, $\overline{C_7}$) + structured probes of clique 3-tensor slice rank / Strassen functionals / non-PSD Banach Schur norms / Vrana relaxations (formalize any valid breakthrough; else rigorous negative/barrier report) | M5 | survey (spec, math) |
| F13 | Canonical `Main.lean`, Open-Problem `Prop`s & `RESULTS.md` | Public `ShannonC7/Main.lean` exporting canonical `SimpleGraph.cycleGraph 7` sandwich, Fekete limit, exact small powers, unattainability, generalizations, formal open-problem `Prop`s (`OpenQuestion_StrictGap`, `OpenQuestion_ExactValue`), and executive `RESULTS.md` | M6 | survey (spec, math) |
| F14 | Final Milestone: E2E Tiers 1–4 Pass & Tier 5 Adversarial Hardening | Sequential pass of 100% E2E Tiers 1–4 (`TEST_READY.md`) followed by white-box Tier 5 Challenger-initiated adversarial hardening until zero remaining gaps | M6 | pattern (Project) |
| F15 | Opaque-Box E2E Verification Suite (`verify/`) | Requirement-driven 4-tier E2E test infrastructure (`TEST_INFRA.md`, `verify/e2e_audit.lean`, `#print axioms` gate, static hygiene scan, independent Python witness cross-check, negative-test robustness suite, `TEST_READY.md`) | E2E_Track | pattern (Dual Track), survey (math) |

---

## 3. Milestones

| # | Name | Scope | Dependencies | Sub-Orch Conv ID | Status |
|---|------|-------|--------------|------------------|--------|
| M1 | `M1_Core` | F1, F2 (Toolchain + `Defs`, `Fekete`, `CycleC7`) | none | `5c8280a5b6a05254b28d6acf872473f1` (`gen7`) | IN_PROGRESS (Iter 11 Wave 11 ACTIVE on commit `22dded10`: Closed Positive-Whitelist Fail-Closed Stage 1, 20/20 `ShannonC7/` 0 FP, Stage 2+3 locked `9c01f123...`) |
| M2 | `M2_UpperTheory` | F3, F4, F5 (`Lovasz`, `LovaszC7`, `CubicBounds`, `Haemers`) | M1 | `55a0941919f187de03cf5e7ebb926825` | **DONE** (Iter 1 unanimous 5/5 PASS; 1,713 lines, 0 warnings, 220 decls verified pure kernel) |
| M3 | `M3_LowerEngine` | F6, F7, F8 (`TrieVerifier`, `Decimal`, `SmallPowers`, `ValidTuple`, `HeteroLayered`) | M1 | `53bd6e46538f908d14195f050c0bbe94` (`gen2`) | **DONE** (Unanimous 5/5 PASS; 8,013L across 6 files, 0 warnings, 1,623 decls / 404 pub thms pure kernel; BPZ v1 `3.258805369885465` certified!) |
| M4 | `M4_LowerFrontier` | F9, F10 (C++17/Rust Tracks L1–L4, verifier/codegen, `FrontierLower.lean`) | M3 | `172cf2601e49473fac78d0073503090f` (`gen5`) | IN_PROGRESS (Iter 7: 10/11 deliverables incl. pure-kernel `3.258822357711717` at `d=220` LOCKED 5/5 PASS + Auditor CLEAN 6/6 + both Reviewers APPROVE; Closed Lexical + Syntactic Whitelist `verify_witness.py` → 5/5 PASS!) |
| M5 | `M5_UpperFrontier` | F11, F12 (Tracks U1–U2, `AlphaC7Cube.lean`, `FinitePowerUpper.lean`, obstruction testbed) | M1, M2 | `dd688d159ec61c309600649ba0e15569` | **DONE** (Iter 2 unanimous 5/5 PASS; pure-kernel exact `α(C₇³)=33`, `α(C₇⁴)≤115`, `α(C₇⁵)≤401`, 1,016-orbit census, fail-closed U2 testbed!) |
| M6 | `M6_Final` | F13, F14 (`Main.lean`, `RESULTS.md`, E2E Tiers 1–4, Tier 5 Adversarial Hardening) | M4, M5, E2E_Track | `pending` | PLANNED |
| E2E | `E2E_Track` | F15 (Independent opaque-box E2E suite: `TEST_INFRA.md`, `verify/`, `TEST_READY.md`) | none (runs in parallel; Lean execution checks sync after M1 toolchain) | `49af7901b60f5347eeb297043b329b45` (`gen8`) | IN_PROGRESS (Iter 14: Wave r13 Auditor 13/13 CLEAN + Primary Live-Lean Reviewer APPROVE 0 findings; ~58L final polish → Wave r14 5/5 PASS & `/home/antigravity/TEST_READY.md`) |

---

## 4. Interface Contracts

### 4.1 Core Lean 4 Types & Theorems (`M1` → `M2`, `M3`, `M5`, `M6`, `E2E`)
Namespace: `ShannonC7`

```lean
-- Strong product & strong powers (ShannonC7/Defs.lean)
def strongProd {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W)
infixl:70 " ⊠ " => strongProd

def StrongPowV (V : Type*) : ℕ → Type _
def strongPow {V : Type*} (G : SimpleGraph V) : (d : ℕ) → SimpleGraph (StrongPowV V d)

-- Textbook Fin d → V strong power
def strongPowPi {V : Type*} (G : SimpleGraph V) (d : ℕ) : SimpleGraph (Fin d → V) where
  Adj x y := x ≠ y ∧ ∀ i : Fin d, x i = y i ∨ G.Adj (x i) (y i)

def strongPowEquivPi {V : Type*} (G : SimpleGraph V) (d : ℕ) :
    strongPow G d ≃g strongPowPi G d

def shannonSet {V : Type*} [Fintype V] (G : SimpleGraph V) : Set ℝ
def shannonCapacity {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := sSup (shannonSet G)

theorem shannonCapacity_congr {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    shannonCapacity G = shannonCapacity H

theorem le_shannonCapacity_of_indepSet {V : Type*} [Fintype V] (G : SimpleGraph V)
    {d : ℕ} (hd : 0 < d) {s : Finset (StrongPowV V d)}
    (hs : (strongPow G d).IsIndepSet (s : Set (StrongPowV V d))) :
    (s.card : ℝ) ^ (1 / (d : ℝ)) ≤ shannonCapacity G

theorem shannonCapacity_le {V : Type*} [Fintype V] (G : SimpleGraph V) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ d : ℕ, 0 < d → ((strongPow G d).indepNum : ℝ) ≤ B ^ d) :
    shannonCapacity G ≤ B

-- Fekete limit equivalence (ShannonC7/Fekete.lean)
theorem shannonCapacity_tendsto {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    Filter.Tendsto
      (fun d : ℕ => ((strongPowPi G d).indepNum : ℝ) ^ (1 / (d : ℝ)))
      Filter.atTop (nhds (shannonCapacity G))

-- Computable C7 & Mathlib bridge (ShannonC7/CycleC7.lean)
def C7 : SimpleGraph (ZMod 7)
instance : DecidableRel C7.Adj
def c7IsoCycleGraph : C7 ≃g SimpleGraph.cycleGraph 7
def c7IsoCirculant : C7 ≃g SimpleGraph.circulantGraph ({1} : Set (ZMod 7))

-- Slice double-counting (ShannonC7/CycleC7.lean)
theorem c7_sliceDoubleCount {W : Type*} [Fintype W] (H : SimpleGraph W) :
    2 * (C7 ⊠ H).indepNum ≤ 7 * H.indepNum
```

### 4.2 Upper-Bound Exports (`M2` → `M5`, `M6`)
```lean
-- ShannonC7/Lovasz.lean
structure LovaszCert {V : Type*} [Fintype V] (G : SimpleGraph V) (β : ℝ)
theorem shannonCapacity_le_of_cert {V : Type*} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : LovaszCert G β) : shannonCapacity G ≤ β⁻¹
theorem c5_shannonCapacity_eq_sqrt_five :
    shannonCapacity (SimpleGraph.cycleGraph 5) = Real.sqrt 5

-- ShannonC7/LovaszC7.lean
noncomputable def lovaszThetaC7 : ℝ := (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7))
theorem c7_upper_lovasz : shannonCapacity (SimpleGraph.cycleGraph 7) ≤ lovaszThetaC7
theorem c7_compl_upper_lovasz :
    shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ≤ 1 + (Real.cos (Real.pi / 7))⁻¹
theorem oddCycle_upper_lovasz (k : ℕ) (hk : 1 ≤ k) :
    shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1)) ≤
      ((2 * k + 1 : ℝ) * Real.cos (Real.pi / (2 * k + 1))) /
        (1 + Real.cos (Real.pi / (2 * k + 1)))

-- ShannonC7/CubicBounds.lean
theorem lovaszThetaC7_cubic :
    lovaszThetaC7 ^ 3 + 7 * lovaszThetaC7 ^ 2 - 49 * lovaszThetaC7 + 49 = 0
theorem c7_upper_rational :
    shannonCapacity (SimpleGraph.cycleGraph 7) < (3317667207395 : ℝ) / 1000000000000
theorem c7_lovasz_unattainable (d : ℕ) (hd : 0 < d) :
    ((strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ^ (1 / (d : ℝ)) < lovaszThetaC7

-- ShannonC7/Haemers.lean
theorem shannonCapacity_le_haemers_rank ...
theorem haemers_minrank_c7_ge_four ...
```

### 4.3 Lower-Bound Engine Exports (`M3` → `M4`, `M5`, `M6`)
```lean
-- ShannonC7/TrieVerifier.lean
inductive Trie7 : ℕ → Type
def Trie7.card : {d : ℕ} → Trie7 d → ℕ
def Trie7.isIndep : {d : ℕ} → Trie7 d → Bool
def Trie7.disjoint : {d : ℕ} → Trie7 d → Trie7 d → Bool
theorem Trie7.to_indepSet_of_isIndep ... -- pure-kernel soundness

-- ShannonC7/Decimal.lean
theorem le_shannonCapacity_of_nat_pow {V : Type*} [Fintype V] {G : SimpleGraph V}
    {d N num den : ℕ} (hd : 0 < d) (hden : 0 < den)
    (hN : N ≤ (strongPow G d).indepNum) (hpow : num ^ d ≤ den ^ d * N) :
    (num : ℝ) / (den : ℝ) ≤ shannonCapacity G

-- ShannonC7/SmallPowers.lean
theorem alpha_c7_pow1 : (strongPowPi (SimpleGraph.cycleGraph 7) 1).indepNum = 3
theorem alpha_c7_pow2 : (strongPowPi (SimpleGraph.cycleGraph 7) 2).indepNum = 10
theorem alpha_c7_pow3_ge : 33 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum
theorem alpha_c7_pow4_ge : 108 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum
theorem alpha_c7_pow5_ge_343 : 343 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum
theorem alpha_c7_pow5_ge_367 : 367 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum
theorem c7_compl_lower_17 : (17 : ℝ) ^ (1 / 4 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ

-- ShannonC7/ValidTuple.lean & ShannonC7/HeteroLayered.lean
structure ValidTuple {V : Type*} [Fintype V] (G : SimpleGraph V)
structure Profile where a : ℕ; b : ℕ; c : ℕ; d : ℕ; hba : b ≤ a; hdc : d ≤ c
def ValidTuple.star ... : ValidTuple (G ⊠ H)
theorem ValidTuple.star_profile ...
theorem ValidTuple.card_le_indepNum ...
-- Plus HeteroGadget & PortSystem constructive product/lifting theorems
```

### 4.4 Frontier & Public `Main.lean` Contract (`M4`, `M5`, `M6` ↔ `E2E_Track`)
`ShannonC7/Main.lean` MUST export (under namespace `ShannonC7`, using ONLY `SimpleGraph.cycleGraph 7` and `strongPowPi`, zero `sorry`, axioms $\subseteq \{\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}\}$):
- `c7_shannonCapacity_tendsto`
- `alpha_c7_pow1` (`= 3`), `alpha_c7_pow2` (`= 10`), `alpha_c7_pow3` (`= 33`)
- `c7_upper_lovasz`, `c7_upper_rational` (`< 3317667207395 / 10^12`), `c7_lovasz_unattainable`
- `c7_lower_num : ℕ`, `c7_lower_den : ℕ` (with `c7_lower_den > 0` and `(c7_lower_num : ℝ) / c7_lower_den ≥ 3258805369885 / 10^12` minimum floor, targeting `≥ 3258827985920007 / 10^15` BPZ Lean record and `> 3258832620353 / 10^12` new world record!)
- `c7_lower_frontier : (c7_lower_num : ℝ) / (c7_lower_den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7)`
- `c7_shannonCapacity_sandwich : (c7_lower_num : ℝ) / (c7_lower_den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) ∧ shannonCapacity (SimpleGraph.cycleGraph 7) ≤ lovaszThetaC7`
- `c7_compl_sandwich`, `c5_shannonCapacity_eq_sqrt_five`, `oddCycle_upper_lovasz`
- `OpenQuestion_StrictGap : Prop := shannonCapacity (SimpleGraph.cycleGraph 7) < lovaszThetaC7`
- `OpenQuestion_ExactValue : Prop := ∃ c : ℝ, shannonCapacity (SimpleGraph.cycleGraph 7) = c`

---

## 5. Code Layout & Exclusive Write Ownership

```
/home/antigravity/
├── PROJECT.md                          -- Project Orchestrator (this file)
├── TEST_INFRA.md                       -- E2E_Track
├── TEST_READY.md                       -- E2E_Track (published when E2E suite ready)
└── shannon-c7/                         -- Git repository (initialized by M1)
    ├── lean-toolchain                  -- M1 (leanprover/lean4:v4.32.2)
    ├── lakefile.toml                   -- M1
    ├── lake-manifest.json              -- M1
    ├── RESULTS.md                      -- M6
    ├── ShannonC7/
    │   ├── Defs.lean                   -- M1
    │   ├── Fekete.lean                 -- M1
    │   ├── CycleC7.lean                -- M1
    │   ├── Lovasz.lean                 -- M2
    │   ├── LovaszC7.lean               -- M2
    │   ├── CubicBounds.lean            -- M2
    │   ├── Haemers.lean                -- M2
    │   ├── TrieVerifier.lean           -- M3
    │   ├── Decimal.lean                -- M3
    │   ├── SmallPowers.lean            -- M3
    │   ├── ValidTuple.lean             -- M3
    │   ├── HeteroLayered.lean          -- M3
    │   ├── FrontierLower.lean          -- M4
    │   ├── AlphaC7Cube.lean            -- M5
    │   ├── FinitePowerUpper.lean       -- M5
    │   ├── Main.lean                   -- M6
    │   └── Tests/                      -- Unit tests per milestone (CoreTests, UpperTests, LowerEngineTests)
    ├── scripts/                        -- M1 (setup_env.sh, verify_axioms.sh)
    ├── search/
    │   ├── lower/                      -- M4 (C++17/Rust search, verify_witness.py, codegen, LOWER_RESEARCH_REPORT.md)
    │   └── upper/                      -- M5 (C++17 cube/quad certifier, obstruction_testbed.py, UPPER_RESEARCH_REPORT.md)
    └── verify/                         -- E2E_Track ONLY (e2e_audit.lean, cross_check.py, run_e2e.sh, tiers 1-4)
```

> **Strict Write-Ownership Rule:** Concurrent milestones MUST NEVER edit the same file. Coordination metadata stays strictly under `/home/antigravity/.agents/teamwork/<agent_folder>/`.
