# Upper-Bound Frontier Research Report: $C_7^{\boxtimes 3}$, $C_7^{\boxtimes 4}$, and Asymptotic Obstructions Beyond $\vartheta(C_7)$

> **Status & Scope Integrity Statement.**
> Every mathematical claim in this report is partitioned strictly into three tiers:
> 1. **Formally proved in the pure Lean 4 kernel** (zero `sorry`, zero `native_decide`, zero custom axioms; standard axioms `{propext, Classical.choice, Quot.sound}` only):
>    $\alpha(C_7^{\boxtimes 3}) = 33$, $\alpha(C_7^{\boxtimes 4}) \le 115$, $\alpha(C_7^{\boxtimes 5}) \le 401$, and the general conditional slice double-counting bridge $\alpha(C_7^{\boxtimes 4}) \le k \implies \alpha(C_7^{\boxtimes 5}) \le \lfloor 7k/2 \rfloor$ (including $112 \implies 392$ and $111 \implies 388$).
> 2. **Independently verified computationally** (C++17 / Python / HiGHS / CVXPY; reproducible scripts under `search/upper/`):
>    the exhaustive $\mathrm{Aut}(C_7^{\boxtimes 3})$-orbit census of all $33$-word independent sets of $C_7^{\boxtimes 3}$ ($K_{33} = 1{,}016$ orbits, $16{,}672{,}544$ distinct $33$-sets, $0$ $34$-sets), exact $1$-swap closure ($4{,}689/4{,}689$ moves), exact $D_7$-canonical slice-profile classification for $C_7^{\boxtimes 4}$ at $N \in \{115, 114, 113, 112\}$, the 4,095-cut LP relaxation obstruction at $115.0$, and all six theoretical obstruction probes on asymptotic upper-bound functionals.
> 3. **Open / Unproved:**
>    **We do NOT claim $\Theta(C_7) < \vartheta(C_7) \approx 3.317667207394$.** Likewise, $\alpha(C_7^{\boxtimes 4}) \le 114$, $\alpha(C_7^{\boxtimes 4}) \le 113$, and the October 2026 Evidence Press candidate $\alpha(C_7^{\boxtimes 4}) \le 112$ remain **open** and are NOT claimed as proved here.

---

## Executive Summary

| Result / Investigation | Domain | Outcome | Proof / Verification Tier | Primary Artifact |
| :--- | :--- | :--- | :--- | :--- |
| $\alpha(C_7^{\boxtimes 3}) = 33$ | Finite power ($d=3$) | **Proved** (exact; closes Polak–Schrijver 2019 in pure Lean 4 kernel) | Lean 4 pure kernel | [`ShannonC7/AlphaC7Cube.lean`](file:///home/antigravity/shannon-c7/ShannonC7/AlphaC7Cube.lean) |
| $\alpha(C_7^{\boxtimes 4}) \le 115$ | Finite power ($d=4$) | **Proved** ($\lfloor 7 \cdot 33 / 2 \rfloor = 115 < \lfloor \vartheta(C_7)^4 \rfloor = 121$) | Lean 4 pure kernel | [`ShannonC7/FinitePowerUpper.lean`](file:///home/antigravity/shannon-c7/ShannonC7/FinitePowerUpper.lean) |
| $\alpha(C_7^{\boxtimes 5}) \le 401$ | Finite power ($d=5$) | **Proved** (from `c7LovaszCert.pow 5` + $q = 33177/10000$; beats $\lfloor 7 \cdot 115/2 \rfloor = 402$) | Lean 4 pure kernel | [`ShannonC7/FinitePowerUpper.lean`](file:///home/antigravity/shannon-c7/ShannonC7/FinitePowerUpper.lean) |
| $\alpha(C_7^{\boxtimes 4}) \le k \implies \alpha(C_7^{\boxtimes 5}) \le \lfloor 7k/2 \rfloor$ | Conditional bridge | **Proved** (incl. $112 \implies 392$, $111 \implies 388$) | Lean 4 pure kernel | [`ShannonC7/FinitePowerUpper.lean`](file:///home/antigravity/shannon-c7/ShannonC7/FinitePowerUpper.lean) |
| Census of $\mathcal{I}_{33}(C_7^{\boxtimes 3})$ | Exhaustive enumeration | **$K_{33} = 1{,}016$ orbits, $16{,}672{,}544$ sets**, $0$ $34$-sets (`198.16s`) | C++17 exhaustive + 100% 1-swap & local-search cross-check | [`search/upper/census_c7_cube.cpp`](file:///home/antigravity/shannon-c7/search/upper/census_c7_cube.cpp) |
| $C_7^{\boxtimes 4}$ Audit ($N=115..112$) | LP / MIP / structural audit | Full 4,095-cut LP stuck at $115.5$ (unanchored, exact uniform $33/686$) and $115.0$ (anchored across 15/15 orbits; exact dual bound $\le 115$); phase transition at $N=112$ | C++17 + HiGHS LP/MIP + exact analysis | [`search/upper/audit_c7_quad.cpp`](file:///home/antigravity/shannon-c7/search/upper/audit_c7_quad.cpp), [`audit_c7_quad_mip.py`](file:///home/antigravity/shannon-c7/search/upper/audit_c7_quad_mip.py) |
| Asymptotic functional probes (Track U2) | Spectral / tensor / info-theoretic bounds | **0/13** tested candidates pass all 4 gates (8/8 graphs) and beat $\vartheta(C_7)$ (`1/13 FULL_PASS = lovasz_theta`, `6/13 PARTIAL_CHECKED_PASS` with `all_pass: false`, `6/13 FAIL`); concrete analytical or numerical barrier isolated for every family | Reproducible Python/CVXPY testbed (`20.17 s`, exit 0) | [`search/upper/obstruction_testbed.py`](file:///home/antigravity/shannon-c7/search/upper/obstruction_testbed.py) |

---

## 1. Track U1a: Pure-Kernel Proof of $\alpha(C_7^{\boxtimes 3}) = 33$ & Finite-Power Upper Bounds

### 1.1 Mathematical Proof Architecture (`ShannonC7/AlphaC7Cube.lean`)

The exact bound $\alpha(C_7^{\boxtimes 3}) \le 33$ (first established computationally by Vesel–Žerovnik 2002 and Polak–Schrijver 2019) is formalized from scratch in the pure Lean 4 kernel without `native_decide`, `sorry`, `partial`, or external axioms:

1. **Pure-kernel 49-bit `Nat` bitmasks + SWAR popcount + depth-1 `seqN`:** Every subset of $V(C_7^{\boxtimes 2}) = \mathbb{Z}_7^2$ is encoded as a 49-bit `Nat` (`m < 2^49`), using direct C++ kernel primitives (`Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.beq`, `Nat.add`, `Nat.sub`) with zero infix typeclass unfolding in hot loops, 1-step SWAR popcount (`pop7`/`pop49`), depth-1 call-by-value `seqN` forcing, precomputed 49-entry `sq22` $2\times 2$-clique masks, and precomputed literal bit lists `repBits : Fin 3 → List Nat`. (Benchmarking showed this reduces kernel verification time by $> 30\times$ relative to 49-`Bool` struct masks while staying 100% pure-kernel `by rfl`.)
2. **Exact 3-orbit classification of $\mathcal{I}_{10}(C_7^{\boxtimes 2})$ under $\mathrm{Aut}(C_7^{\boxtimes 2})$ (`|Aut| = 392`):**
   Slice double-counting along rows forces any $10$-element independent set $B \subseteq C_7^{\boxtimes 2}$ to have row counts $(1, 1, 2, 1, 2, 1, 2)$ up to cyclic shift. Normalizing row $0$ to column $0$ (mask $1$) and row $1$ to column $2$ or $3$ (mask $4$ or $8$) yields **exactly 10** canonical candidates (`canon10Candidates`), each explicitly mapped by `canon10Witnesses` into one of the three canonical orbits:
   - `rep 0`: stabilizer size $1$ ($392$ sets),
   - `rep 1`: stabilizer size $1$ ($392$ sets),
   - `rep 2`: stabilizer size $2$, fixed by `(false, true, 4, true, 2)` ($196$ sets),
   giving $392 + 392 + 196 = 980$ total $10$-sets.
3. **Depth-10 `Tree10` common-forbidden tables (`c1Tree`, `c2Tree`) & loop-hoisted verification:**
   For each orbit $k \in \{0, 1, 2\}$ and every $4$-, $5$-, or $6$-subset $X \subseteq \mathrm{rep}(k)$ ($2{,}016$ subsets total), we precompute exact common-forbidden masks:
   $$C_1(X) = \bigcap_{\substack{B \in \mathcal{I}_{10}\\ X \subseteq B}} N[B \setminus X], \qquad C_2(X) = \bigcap_{\substack{B \in \mathcal{I}_{10}\\ X \subseteq B}} C_1(B \setminus X).$$
   Using `Aut2`-equivariance (`c1Tree_equivariant`), loop-hoisted 5-factor enumeration (`forAllAut2` / `forAllFin7`, max recursion depth $\le 10$), and hoisted `checkC2Aux` invariants, all $2{,}016$ entries of both `c1Tree` and `c2Tree` are scatter-verified against all $980$ $10$-sets ($15{,}546$ leaf checks each) in 18 split pure-kernel `by rfl` lemmas (`checkC1_00..22`, `checkC2_00..22`).
4. **Exact 5-profile algebraic reduction for $|S| \ge 34$:**
   With $s_i = |S_i|$ ($i \in \mathbb{Z}_7$) and adjacent band sums $b_i = s_i + s_{i+1} \le \alpha(C_7^{\boxtimes 2}) = 10$, total deficit $D = 70 - 2|S| \in \{0, 2\}$ forces every $|S| \ge 34$ set into one of **4 centered profile families** under cyclic rotation alone (all 5 profiles are palindromic; proved cleanly via `exists_profile_arith`), checked by depth-60 chunked `checkAll4` pure-kernel `by rfl` theorems (`checkP13_0..2`, `checkP2_0..2`, `checkP4_0..2`, `checkP5_0..2`):

| Profile Family | Slice Sizes $(s_0,\dots,s_6)$ | Anchored Band | Canonical Cases | Kernel Certificate Mechanism | Closure Statistics (from `cert_c7_cube` & `gen_alpha_cube_lean.py`) |
| :--- | :--- | :--- | :---: | :--- | :--- |
| **P1 + P3** | $(5,5,5,5,5,5,\ge 4)$ | $B_2 = S_2(5) \sqcup S_3(5)$ | 378 (halved by $(0,3)\in S_2$) | `c2Tree`/`c1Tree` + 3-square clique covers | `pop3 = 319`, `sq3 = 28`, `splitL1 = 31` (`10` globally unique L1 covers / `10` list entries across `6` non-empty `splitL1` nodes; **0 L2**) |
| **P2** | $(4,6,4,6,4,6,4)$ | $B_2 = S_2(4) \sqcup S_3(6)$ | 630 | `c2Tree`/`c1Tree` + 3-square clique covers | `pop3 = 483`, `sq3 = 58`, `splitL1 = 89` (`43` globally unique L1 covers, `48` per-orbit unique / `51` list entries across `35` non-empty `splitL1` nodes; **0 L2**) |
| **P4** | $(4,6,4,6,4,5,5)$ | $B_1 = S_1(6) \sqcup S_2(4)$ | 630 | Sparse integer 2D Farkas dual (`Grid49`, RHS $< 10 D$) | **630 / 630** closed at root (0 branching) |
| **P5** | $(5,5,5,5,4,6,4)$ | $B_1 = S_1(5) \sqcup S_2(5)$ | 378 (halved by $(0,3)\in S_1$) | Sparse integer 3-slice Farkas dual (`Grid49`, RHS $< 14 D$) | `root = 326`, `splitS0 = 52` (`s0_leaf = 432`), **`splitS3 = 0` (`s3_leaf = 0`)** |

5. **Self-contained 33-word lower witness:** `AlphaC7Cube.lean` (`5,684` lines, `674.7 KiB` on disk / `669.2 KiB` generator char-count) directly embeds a 33-word witness (`witness33`, verified by pure-kernel `decide` on all $33^2$ pairs) without importing M3's `SmallPowers`, yielding `alpha_c7_pow3 : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum = 33`.

### 1.2 Finite-Power Upper Bounds (`ShannonC7/FinitePowerUpper.lean`)

Combining `alpha_c7_pow3_le` with M1's `c7_sliceDoubleCount` and M2's `c7LovaszCert` + `lovaszThetaC7_lt_of_cubic_pos`:
- **`alpha_c7_pow4_le_115`:** $\alpha(C_7^{\boxtimes 4}) \le \lfloor 7 \cdot 33 / 2 \rfloor = 115$, strictly tightening the Lovász ceiling $\lfloor \vartheta(C_7)^4 \rfloor = \lfloor 121.152\dots \rfloor = 121$ by $6$.
- **`alpha_c7_pow5_le_401`:** Applying `c7LovaszCert.pow 5` with the rational bound $q = 33177/10000$ (where $q^3 + 7 q^2 - 49 q + 49 > 0$ and $q^5 = 401.962523\dots < 402$) proves $\alpha(C_7^{\boxtimes 5}) \le 401$ without `Real.rpow` or $\pi$, strictly sharpening the slice double-counting bound $\lfloor 7 \cdot 115 / 2 \rfloor = 402$.
- **Conditional $d=4 \to 5$ bridges:** `alpha_c7_pow5_le_of_pow4`, `alpha_c7_pow5_le_392_of_pow4_le_112`, and `alpha_c7_pow5_le_388_of_pow4_le_111` formalize that any future proof of $\alpha(C_7^{\boxtimes 4}) \le 112$ immediately implies $\alpha(C_7^{\boxtimes 5}) \le 392$ (a 9-word gain over Lovász's $401$).

*(Exact Lean 4 build times and `verify_axioms.sh --verbose` audit output are recorded in Section 5 below.)*

---

## 2. Track U1b: Exhaustive 33-Set Census of $C_7^{\boxtimes 3}$ and $C_7^{\boxtimes 4}$ Audit

### 2.1 Exact Exhaustive Census of $\mathcal{I}_{33}(C_7^{\boxtimes 3})$ (`census_c7_cube.cpp`)

Every $33$-element independent set in $C_7^{\boxtimes 3}$ satisfies $3 \le |S_i| \le 7$ on every slice and has band-deficit sum $\sum_{i=0}^6 (10 - b_i) = 70 - 66 = 4$, forcing **at least three** $10$-bands along every coordinate axis. Up to $D_7$ dihedral symmetry on axis $0$ (covering all $\binom{7}{3} = 35$ triples of $10$-bands), every $33$-set (and every hypothetical $\ge 34$-set) falls into one of **four exhaustive triple-$10$-band subcases** with $B_0 = S_0 \sqcup S_1 \in \{\mathrm{rep}(0), \mathrm{rep}(1), \mathrm{rep}(2)\}$:
- **Subcase 1a ($B_0 = B_1 = B_2 = 10$):** consecutive triple of $10$-bands (`127,901` quads, `60,946` unique $(S_0, S_3)$ pairs, `103.66 s`, `raw33 = 4,407`, `864` orbits);
- **Subcase 1b ($B_0 = B_1 = B_3 = 10$, $B_2, B_6 \le 9$):** pair plus gap-1 $10$-band (`24,569` triples, `23,754` unique $(S_0, S_2)$ pairs, `82.51 s`, `raw33 = 1,763`, cumulative `1,014` orbits);
- **Subcase 1c ($B_0 = B_1 = B_4 = 10$, $B_2, B_3, B_5, B_6 \le 9$):** uniquely forcing slice profile $(5,5,5,4,5,5,4)$ (`5,340` triples, `5,118` unique $(S_0, S_2)$ pairs, `5.69 s`, `raw33 = 286`, cumulative `1,016` orbits);
- **Subcase 2 ($B_0 = B_2 = B_4 = 10$, $B_1, B_3, B_5, B_6 \le 9$):** three pairwise non-adjacent $10$-bands, uniquely forcing $(6,4,5,5,4,6,3)$ (`630` roots, `5.44 s`, `raw33 = 287`, cumulative `1,016` orbits).

Running the OpenMP-parallel bitmask census over all four subcases using the precomputed `ext10` extension table (`230,937` keys for $3..7$-subsets of all $980$ $10$-sets) and exact $\mathrm{Aut}(C_7^{\boxtimes 3})$ canonicalization (`census_c7_cube.cpp`, `198.16 s` wall-clock on 2 vCPUs) yields:

| Metric | Exact Verified Value |
| :--- | :--- |
| Exhaustive $34$-word sets found (`raw34`) | **$0$** (independent C++ confirmation of $\alpha(C_7^{\boxtimes 3}) \le 33$) |
| Raw $33$-word hits across 4 subcases (`raw33`) | `6,743` (`1a: 4,407`, `1b: 1,763`, `1c: 286`, `2: 287`) |
| Exact $\mathrm{Aut}(C_7^{\boxtimes 3})$-orbits ($K_{33}$, $|\mathrm{Aut}| = 16{,}464$) | **$1{,}016$** (saved in `search/upper/c7_cube_33_orbits.txt`) |
| Stabilizer size distribution (`|Stab| : count`) | `1 : 1,011`, `2 : 1` (orbit #781), `3 : 3` (orbits #206, #542, #577), `6 : 1` (orbit #467) |
| Exact total $33$-element independent sets $|\mathcal{I}_{33}(C_7^{\boxtimes 3})|$ | **$16{,}672{,}544$** ($\sum_{o} 16{,}464 / |\mathrm{Stab}(o)|$) |

#### Three Independent Completeness & Structural Cross-Checks (`audit_c7_quad.cpp`, `audit_c7_quad_mip.py`)

1. **100% Maximality & 1-Swap Closure (`audit_c7_quad.cpp`, `11.09 s`):**
   - Every single one of the $1{,}016$ orbits dominates all $343$ vertices of $C_7^{\boxtimes 3}$ (`dom[u] >= 1`), confirming every $33$-set is maximal.
   - Generating **all $4{,}689$ valid 1-vertex swaps** across all $1{,}016$ orbit representatives (replacing a vertex $v \in R_o$ by a uniquely dominated neighbor $u \notin R_o$) and canonicalizing each resulting $33$-set lands **100% (`4,689 / 4,689`)** inside the $1{,}016$-orbit census.
   - **1-Swap Quotient Graph Structure:** 1-swap degree per $33$-set lies in $[0, 9]$ (mean `4.62`). The 1-swap quotient graph on the $1{,}016$ orbits decomposes into **5 connected components** of sizes **`(988, 20, 6, 1, 1)`**, with **2 completely rigid (0-swap) orbits**, one of which is the unique highest-symmetry `|Stab| = 6` orbit (**orbit #467**, $|\mathrm{Orbit}| = 2{,}744$).
   - **3-Axis 10-Band Multiplicity Histogram** across all $1{,}016$ orbits (sorted counts of 10-bands along the 3 axes):
     `(3,3,3): 190`, `(3,3,4): 472`, `(3,3,5): 47`, `(3,4,4): 258`, `(3,4,5): 36`, `(4,4,4): 13`. Every $33$-set has $\ge 3$ $10$-bands on **all three axes** simultaneously.
2. **Independent Witness & Randomized Local-Search Cross-Check (`audit_c7_quad_mip.py`, `1.12 s`):**
   - The explicit Explorer-1 33-word witness (`AlphaC7Cube.lean`) canonicalizes to **orbit #44**; 9 additional random $33$-sets found independently via randomized $(1,2)/(1,1)$ + $2$-drop local search canonicalize to orbits `[182, 157, 942, 578, 929, 259, 211, 790, 281]` (**10/10 matched**).

### 2.2 Exact $D_7$-Canonical Profile Taxonomy & Phase Transition at $N = 112$ (`audit_c7_quad.cpp`)

Using $\alpha(C_7^{\boxtimes 3}) = 33$, any independent set $S \subseteq C_7^{\boxtimes 4}$ of size $N$ satisfies $b_i = |S_i| + |S_{i+1}| \le 33$ for $i \in \mathbb{Z}_7$ with total band deficit $\sum_{i=0}^6 (33 - b_i) = 231 - 2N$:

| Target Size $N$ | Total Deficit $231 - 2N$ | $D_7$-Canonical Profiles | `#33-bands` Range | `#33-bands` Histogram | Zero-33-Band Profiles |
| :---: | :---: | :---: | :---: | :--- | :---: |
| **$115$** (Tier 1: $\alpha \le 114$) | $1$ | **1** | $[6, 6]$ | `6:1` — unique $(16,16,17,16,17,16,17)$ | $0$ |
| **$114$** (Tier 2: $\alpha \le 113$) | $3$ | **8** | $[4, 6]$ | `4:4, 5:3, 6:1` | $0$ |
| **$113$** (Tier 3: $\alpha \le 112$) | $5$ | **38** | $[2, 6]$ | `2:3, 3:10, 4:18, 5:6, 6:1` | $0$ |
| **$112$** (Tier 4: $\alpha \le 111$) | $7$ | **133** | $[0, 6]$ | `0:1, 1:3, 2:27, 3:50, 4:42, 5:9, 6:1` | **1** — unique $(16,16,16,16,16,16,16)$ |

**Structural Phase Transition at $N = 112$:** For every $N \ge 113$ (including the Evidence Press threshold $N = 113 \iff \alpha(C_7^{\boxtimes 4}) \le 112$), **every** slice profile is guaranteed to contain at least **two** exact $33$-bands (so anchoring $B_0 = R_o$ over the $1{,}016$ census orbits covers 100% of solutions without loss of generality). At $N = 112$, the balanced profile $(16,16,16,16,16,16,16)$ appears with **zero** $33$-bands ($b_i = 32$ for all $i$), forcing enumeration over $32$-sets ($|\mathcal{I}_{32}(C_7^{\boxtimes 3})| \gg |\mathcal{I}_{33}|$) if one uses pure band-anchoring.

### 2.3 Strengthened 4,095-Cut LP/MIP Audit & Analytical Obstruction (`audit_c7_quad_mip.py`)

We tested whether adding the **complete symmetric geometric cut hierarchy** of $C_7^{\boxtimes 4}$ — all $2{,}401$ $K_2^{\boxtimes 4}$-cliques ($\le 1$), all $1{,}372$ $K_2^{\boxtimes 3} \boxtimes C_7$-tubes ($\le 3$), all $294$ $K_2^{\boxtimes 2} \boxtimes C_7^{\boxtimes 2}$-slabs ($\le 10$), and all $28$ $K_2 \boxtimes C_7^{\boxtimes 3}$-bands ($\le 33$) — breaks the $115.0$ LP ceiling once band $B_0 = R_o$ is anchored to a canonical $33$-set orbit:

| Formulation ($C_7^{\boxtimes 4}$, $2{,}401$ variables) | Cut Count | HiGHS LP Optimum | Solve Time (2 vCPUs) |
| :--- | :---: | :---: | :---: |
| Unanchored: cliques + 7 axis-0 bands | $2{,}408$ | $115.500000$ | `0.56 s` |
| Unanchored: cliques + 28 bands (all 4 axes) | $2{,}429$ | $115.500000$ | `0.73 s` |
| Unanchored: cliques + 28 bands + 294 slabs | $2{,}723$ | $115.500000$ | `1.24 s` |
| Unanchored: cliques + 28 bands + 294 slabs + 1,372 tubes | $4{,}095$ | $115.500000$ | `2.80 s` |
| **Anchored ($B_0 = R_o$, 15 orbits incl. all 5 high-sym `|Stab| > 1`)**, $|S_0| \in [14,16]$ | $4{,}129$ | **$115.000000$ (all 15/15)** | `1.60–3.61 s` / orbit |
| **Anchored ($B_0 = R_o$, same 15 orbits)**, $|S_0| = 16$ ($N=115$ exact) | $4{,}129$ | **$115.000000$ (all 15/15)** | `1.52–2.28 s` / orbit |
| Anchored MIP benchmark (Orbit 0, full 4,129 cuts, 15s cap) | $4{,}129$ | Dual bound $115.000000$ (`0` nodes closed) | `15.18 s` (Time limit) |

#### Analytical Analysis of the $115.5$ Unanchored & $115.0$ Anchored LP Barriers

1. **Exact unanchored optimum ($= 115.5$):**
   The uniform fractional vector $x(t,a,b,c) \equiv \tfrac{33}{686}$ on all $7^4 = 2{,}401$ vertices satisfies **every** cut in the complete 4,095-cut hierarchy:
   - $K_2^{\boxtimes 4}$-cliques ($16$ vertices): $16 \cdot \tfrac{33}{686} = \tfrac{264}{343} \approx 0.7697 \le 1$;
   - $K_2^{\boxtimes 3} \boxtimes C_7$-tubes ($56$ vertices): $56 \cdot \tfrac{33}{686} = \tfrac{132}{49} \approx 2.6939 \le 3$;
   - $K_2^{\boxtimes 2} \boxtimes C_7^{\boxtimes 2}$-slabs ($196$ vertices): $196 \cdot \tfrac{33}{686} = \tfrac{66}{7} \approx 9.4286 \le 10$;
   - $K_2 \boxtimes C_7^{\boxtimes 3}$-bands ($686$ vertices): $686 \cdot \tfrac{33}{686} = 33 \le 33$ (tight).
   Its objective value is $2{,}401 \cdot \tfrac{33}{686} = \tfrac{231}{2} = 115.5$, matching the exact dual upper bound $2 \sum_{t=0}^6 s_t = \sum_{t=0}^6 (s_t + s_{t+1}) \le 7 \cdot 33 = 231 \implies \sum_{t=0}^6 s_t \le 115.5$.

2. **Exact anchored dual upper bound ($\le 115.0$):**
   Once band $B_0 = R_o$ is anchored with $s_0 = |S_0| \le 16$ (valid under both $s_0 \in [14,16]$ and $s_0 = 16$), summing $s_0 \le 16$ with the three disjoint axis-0 band cuts $s_1 + s_2 \le 33$, $s_3 + s_4 \le 33$, and $s_5 + s_6 \le 33$ proves
   $$\sum_{t=0}^6 s_t = s_0 + (s_1 + s_2) + (s_3 + s_4) + (s_5 + s_6) \le 16 + 33 + 33 + 33 = 115.$$
   Hence no anchored feasible point can exceed $115.0$, and any point attaining $115.0$ must have $s_0 = 16$, $s_1 = 17$, and $s_1+s_2 = s_3+s_4 = s_5+s_6 = 33$.

3. **Why translate convex combinations fail under non-axis-0 cuts (94.0% of orbits infeasible):**
   A naive attempt to attain $115.0$ by placing $x(0,v) = \tfrac{16}{33}\mathbf{1}_{R_o}(v)$, $x(1,v) = \tfrac{17}{33}\mathbf{1}_{R_o}(v)$, and a convex combination of translates of $R_o$ with slice totals $(16,17,16,17,16)$ (total slice weight $\sum_{t=0}^6 w_t = \tfrac{115}{33} \approx 3.4848$, $\sum_{t=2}^6 w_t = \tfrac{82}{33} \approx 2.4848$) on slices $t \in \{2,\dots,6\}$ **fails** on non-axis-0 cuts, which sum across all $7$ axis-0 slices rather than an adjacent pair $\{t, t+1\}$:
   - Pure copies of $R_o$ violate non-axis-0 bands ($10 \cdot \tfrac{115}{33} \approx 34.8485 > 33$), slabs ($\tfrac{345}{33} \approx 10.4545 > 10$), and free-$t$ tubes ($\tfrac{115}{33} \approx 3.4848 > 3$).
   - A uniform average over all $343$ translates on $t \in \{2,\dots,6\}$ still violates every $10$-band of $R_o$ along axes $1, 2, 3$: $10 + \tfrac{82}{33}\cdot\tfrac{66}{7} = \tfrac{234}{7} \approx 33.4286 > 33$.
   - Even optimizing over **arbitrary non-uniform convex combinations of translates of $R_o$** on $t \in \{2,\dots,6\}$ is **strictly LP-infeasible on $955$ of the $1{,}016$ census orbits ($94.0\%$, including Orbit 0)** under the 1D axis-band constraints $b_u + \sum_{k=0}^6 p_k b_{u-k} \le 33$ ($\sum p_k = \tfrac{82}{33}$) alone. For instance, on the $4$ orbits with five consecutive $10$-bands $(8,8,10,10,10,10,10)$ along an axis, averaging over three $10$-bands forces $\max_u (b_u + \sum_k p_k b_{u-k}) \ge 10 + \tfrac{82}{33}\cdot\tfrac{28}{3} = 33 + \tfrac{19}{99} \approx 33.1919 > 33$, capping any translate mixture at $\sum p_k \le \tfrac{69}{28}$ (total weight $\le \tfrac{3201}{28} \approx 114.3214 < 115$).

4. **Empirical primal attainment ($= 115.0$) via non-translate fractional densities:**
   Despite the infeasibility of translate convex combinations on $94.0\%$ of orbits, the full 4,129-cut anchored LP **empirically attains exact $115.000000$ across all $15/15$ sampled orbits** (including Orbit 0, all $5$ high-symmetry `|Stab| > 1` orbits, and independently tested 5-ten-band orbits). Rather than mixing translates of $R_o$, HiGHS places **non-translate fractional densities** on slices $t \in \{2,\dots,6\}$ that counter-balance $R_o$'s $10$-bands on axes $1, 2, 3$ and exploit unoccupied cliques of $R_o$ (for Orbit 0, per-slice max $2\times 2\times 2$-clique weights on slices $2..6$ reach `0.80–0.91`, well above $\tfrac{17}{33} \approx 0.5152$), achieving $115.0$ without branching on the binary split $B_0 = S_0 \sqcup S_1$ ($\binom{33}{16} = 1{,}166{,}803{,}110 \approx 1.17 \times 10^9$ balanced splits per orbit).

#### Honest Feasibility & Compute Assessment for Tiers 1–4 ($\alpha(C_7^{\boxtimes 4}) \le 114, 113, 112$)

- **What works now:** Our exact census ($K_{33} = 1{,}016$ orbits) reduces any $N \in \{115, 114, 113\}$ refutation from $16{,}672{,}544$ unquotiented 33-bands to $1{,}016$ orbit subproblems (a $\sim 16{,}410\times$ symmetry reduction).
- **Why full Tier 1–3 refutation exceeds a 2-vCPU VM budget:** Because the full 4,095-cut LP stays pinned at $115.0$ on all sampled orbits and HiGHS MIP closes $0$ branch-and-bound nodes in $15\,\text{s}$ per orbit (due to the $\binom{33}{16}$ split symmetry of $B_0 = S_0 \sqcup S_1$ and remaining $\mathrm{Aut}$ symmetries on slices $2..6$), closing a single orbit for $N \le 114$ requires either (i) specialized CDCL/MIP with odd-cycle/lifted-clique cuts and binary branching on high-degree vertices of $B_0$, or (ii) a cluster-scale sweep ($\sim 10^3$–$10^4$ CPU-hours across $1{,}016$ orbits, consistent with Polak–Schrijver's $C_7^{\boxtimes 3}$ scaling and the computational complexity of $C_7^{\boxtimes 4}$).
- **Status of the Oct 2026 Evidence Press $\alpha(C_7^{\boxtimes 4}) \le 112$ candidate:** Structurally feasible via our $1{,}016$-orbit reduction (since all 38 $D_7$-profiles for $N = 113$ contain $\ge 2$ $33$-bands), **currently open and unproved**; our formal Lean theorem `alpha_c7_pow5_le_392_of_pow4_le_112` stands ready to immediately convert any future verified proof of $\alpha(C_7^{\boxtimes 4}) \le 112$ into $\alpha(C_7^{\boxtimes 5}) \le 392$.

---

## 3. Track U2: Systematic Obstruction Testbed Beyond $\vartheta(C_7)$ (`obstruction_testbed.py`)

We built a self-contained, reproducible diagnostic suite (`search/upper/obstruction_testbed.py --full`, `20.17 s`, exit 0, 0 warnings, results saved to `search/upper/obstruction_testbed_results.json`) implementing **4 mandatory falsification gates** across **8 benchmark graphs** (`K2`, `C5`, `Gilbert32`, `Haemers27`, `Schlafli27`, `C7`, `C7_compl`, `C7_sq`):

- **Gate G1 (Lower-Bound Soundness):** $f(G) \ge \Theta_{\text{known}}(G)$ across all benchmarks: $K_2 \ge 1$, $C_5 \ge \sqrt{5} \approx 2.236068$, $\text{Gilbert32} \ge \sqrt{20} \approx 4.472136$, $\text{Haemers27} \ge 6$, $\text{Schläfli27} \ge 3$, $C_7 \ge \texttt{BPZ\_C7\_LB} = 3.258827985920007 \approx 3.258828$ (BPZ Aug 2026 Lean $d = 500$ lower bound; cf. Polak–Schrijver $367^{1/5} \approx 3.257866$), $\overline{C_7} \ge 17^{1/4} \approx 2.030543$, and $C_7^{\boxtimes 2} \ge \texttt{BPZ\_C7\_LB}^2 \approx 10.619960$.
- **Gate G2 (Strong-Product Submultiplicativity on $C_7^{\boxtimes 2}$):** $\alpha(C_7^{\boxtimes 2}) = 10 \le f(C_7^{\boxtimes 2}) \le f(C_7)^2$ (necessary test of $f(G \boxtimes H) \le f(G) f(H)$ at $G = H = C_7$).
- **Gate G3 (Schläfli / Complement Product Consistency):** $f(\text{Haemers27}) \cdot f(\text{Schläfli27}) \ge 27$ (kills naive non-submultiplicative hybrids like $\min(\vartheta, \text{minrank})$ since $7 \cdot 3 = 21 < 27$).
- **Gate G4 (Complement Product Consistency on $C_7$):** $f(C_7) \cdot f(\overline{C_7}) \ge 7$.
- **Fail-Closed Completeness & Breakthrough Criterion:** A candidate achieves full `FULL_PASS` (`complete_coverage = true`, `all_pass = true`) and can fire `breakthrough_trigger` **only** if all **8/8** required benchmark graphs have finite real (non-`None`, non-`bool`, non-`NaN`/non-`inf`) values, all four gates G1–G4 explicitly pass (`True`), and $f(C_7) < \vartheta(C_7) - 10^{-6}$. Partially evaluated probe functionals with zero failures on their evaluated subset are explicitly labeled `PARTIAL_CHECKED_PASS` (`complete_coverage = false`, `all_checked_pass = true`, `all_pass = false`, `breakthrough_trigger = false`).

### 3.1 Master Gate Evaluation Table (13 Evaluated Functionals)

| Candidate Functional | $C_5$ | Gilbert32 | Haemers27 | Schläfli27 | $C_7$ | $\overline{C_7}$ | Cov | G1 | G2 | G3 | G4 | Gate Status | Beats $\vartheta(C_7)$? | Verdict / Exact Mechanism |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :--- | :---: | :--- |
| **$\vartheta(G)$ (Lovász baseline)** | $2.236068$ | $5.333333$ | $9.000000$ | $3.000000$ | **$3.317667$** | $2.109916$ | 8/8 | PASS | PASS | PASS | PASS | **4/4 PASS (8/8)** | No | Sharp baseline (`3.317667207394`) |
| **$\vartheta'(G)$ (Schrijver)** | $2.236068$ | **$4.000000$** | $9.000000$ | $3.000000$ | $3.317667$ | $2.109916$ | 8/8 | **FAIL** | PASS | PASS | PASS | **FAIL (G1)** | No | Killed by Gilbert-32 ($4 < \sqrt{20}$); $= \vartheta$ on $C_7$ |
| **Lasserre Level-2** | **$2.000000$** | — | — | — | **$3.000000$** | **$2.000000$** | 4/8 | **FAIL** | — | — | **FAIL** | **FAIL (G1, G4)** | Yes* | Non-submultiplicative; killed by $C_5, C_7, \overline{C_7}$ |
| **$\min(\vartheta, \text{minrank})$ hybrid** | $2.236068$ | $5.333333$ | $7.000000$ | $3.000000$ | $3.317667$ | $2.109916$ | 8/8 | PASS | PASS | **FAIL** | PASS | **FAIL (G3)** | No | Killed by Gate G3 ($7 \times 3 = 21 < 27$) |
| **P1: Clique 3-Tensor $F_\theta(T_{\text{cl}})$** | $5.000000$ | — | — | — | $7.000000$ | $7.000000$ | 5/8 | PASS | PASS | — | PASS | PARTIAL (G1, G2, G4 PASS; G3 N/A) | No | Collapses identically to $n$ on cycles (blowup cover $= 3.5$) |
| **P2a: $\beta_{1.5, 3.0}(G)$** | **$2.092333$** | — | — | — | **$3.155676$** | — | 2/8 | **FAIL** | — | — | — | **FAIL (G1)** | Yes* | Bounds OR-product $\Theta_{\text{OR}}$, NOT strong product; killed by $C_5, C_7$ |
| **P2a: $\min\|B\|_{2\to 2}$ (dual-fit)** | $2.236068$ | $8.000000$ | $9.000000$ | $5.400000$ | $3.317667$ | $2.109916$ | 7/8 | PASS | — | PASS | PASS | PARTIAL (G1, G3, G4 PASS; G2 N/A) | No | Equals $\vartheta$ on $C_5, C_7$; strictly looser on Gil32/Schl27 |
| **P2b: $\vartheta_{\gamma_2}(G)$ (asymmetric)** | $2.236068$ | $5.333334$ | $9.000010$ | $3.000000$ | $3.317667$ | $2.109916$ | 7/8 | PASS | — | PASS | PASS | PARTIAL (G1, G3, G4 PASS; G2 N/A) | No | Exact collapse to $\vartheta(G)$ on all 7 graphs (max asym $= 1.54\times 10^{-13} \le 1.6\times 10^{-13}$) |
| **P2b: Schatten $\Psi_{0.05}(G)$** | $3.070530$ | — | **$7.678464$** | — | $4.105795$ | — | 3/8 | PASS | — | — | — | PARTIAL (G1 PASS; G2–G4 N/A) | No | Valid submultiplicative; beats $\vartheta$ on Haemers-27 ($7.68 < 9$), clique-cover/BFGS min $4.11 > 4$ on $C_7$ |
| **P3a: Vrana $\max_P \vartheta(G, P)$** | — | — | — | — | $3.317667$ | — | 1/8 | PASS | — | — | — | PARTIAL (G1 PASS; G2–G4 N/A) | No | Concavity forces uniform $P$ on vertex-transitive $C_7 \implies \vartheta(C_7)$ |
| **P3b: Sibson/Petz ($\alpha = 0.5$)** | $2.834576$ | — | — | — | $4.331798$ | — | 2/8 | PASS | — | — | — | PARTIAL (G1 PASS; G2–G4 N/A) | No | Monotone increasing in $\alpha \in [0, 2]$; minimum at $\alpha \to 0^+$ is $\vartheta$ |
| **P3b: Primal log-det ($\mu = 0.01$)** | **$2.216242$** | — | — | — | **$3.278015$** | — | 2/8 | **FAIL** | — | — | — | **FAIL (G1)** | Yes* | Killed by $C_5$ ($2.2162 < \sqrt{5}$) for every $\mu > 0$ |
| **P3c: Asymmetric $\rho(B)$** | **$1.351606$** | — | — | — | **$2.463160$** | — | 2/8 | **FAIL** | — | — | — | **FAIL (G1)** | Yes* | Non-monotone on principal submatrices; killed by $C_5, C_7$ |

*(Entries marked `Yes*` fail Gate G1 — they drop below $\Theta(C_5) = \sqrt{5}$ or $\Theta(C_7) \ge 3.258828$ and are therefore INVALID as upper bounds on $\Theta(G)$. In `PARTIAL` rows — JSON `verdict: "PARTIAL_CHECKED_PASS"` — `PASS` in G1 indicates zero lower-bound violations on the evaluated benchmark subset while `—` denotes an unevaluated graph/gate, so `complete_coverage = false`, `all_pass = false`, and `breakthrough_trigger = false` under the fail-closed 8-graph completeness rule.)*

### 3.2 Deep Analysis of Each Obstruction Probe

#### Probe 1: Strassen Support Functionals on 3-Tensors (Exact DFT / Sinkhorn Proof)
- On any triangle-free cycle $C_n$ ($n \ge 4$), the clique $3$-tensor $T_{\text{cl}}(C_n)$ is $\mathbb{Z}_n$-circulant, so its unitary 3-mode discrete Fourier transform $\widehat{T}_{\text{cl}}$ is supported on the plane $a + b + c \equiv 0 \pmod n$ with closed-form entries
  $$\widehat{T}_{\text{cl}}(a, b, -a-b) = \frac{1}{\sqrt{n}}\!\left(1 + 2\cos\tfrac{2\pi a}{n} + 2\cos\tfrac{2\pi b}{n} + 2\cos\tfrac{2\pi(a+b)}{n}\right)$$
  (verified to max error $3.28 \times 10^{-15}$ on $C_7$).
- On $C_7$, $\widehat{T}_{\text{cl}}$ has **12** zeros on the plane (permutations of `{1,2,4}` and `{3,5,6}`), leaving $37/49$ nonzero plane entries, **including all 7 diagonal triples $(k, k, -2k)$** with $\min_k |\widehat{T}_{\text{cl}}(k, k, -2k)| = 0.512858 > 0$. Consequently, the 3-marginals are strictly positive and uniform (`Sinkhorn dev = 6.52e-13`), forcing **every** monomial/support-functional bound in the Fourier basis — the Sawin–Tao slice-rank LP $ST$, Strassen's upper support functional $\rho^\theta$, and the quantum functional $F_\theta$ — to collapse identically to $n = 7$ on $C_7$ (and $n = 5$ on $C_5$, and $n^2 = 49$ on $C_7^{\boxtimes 2}$ across all 5 tested circulant $C_7^{\boxtimes 2}$ weightings: unweighted plus 4 non-product edge/triangle weightings).
- Even the refined clique-cover tensor $T_{\text{cc}}(C_7) \cong_{\mathrm{GL}_7} \langle 4 \rangle$ gives $F_\theta = 4.0$, and its 2-fold blowup gives $7/2 = 3.5 = \chi_f(\overline{C_7}) > \vartheta(C_7)$.

#### Probe 2a: $\ell_p \to \ell_q$ Matrix Norms & The OR-Product vs. Strong-Product Pitfall
- **Crucial Fitting-Convention Distinction:** A primal-fitting matrix $W$ with $W_{ii} = 1$ and **$W_{ij} = 0$ on non-edges** ($i \not\sim j$) is Kronecker-closed under the **strong product $\boxtimes$** (because $0 \cdot (\text{anything}) = 0$ whenever either coordinate is a non-edge; cf. `LovaszCert` in `ShannonC7/Lovasz.lean`). By contrast, a **dual-fitting** matrix $B$ with $B_{ii} = 1$ and **$B_{ij} = 1$ on non-edges** (`B = J + (x - 1)A`, implemented in `or_product_counterexample`, `circulant_beta_pq`, and `solve_min_spectral_norm_dual`) is Kronecker-closed under the **OR-product** (disjunctive product), NOT under the strong product $\boxtimes$! We construct an explicit counterexample on $C_5^{\boxtimes 2}$: the optimal dual Lovász matrix $B_5 = J + (e_5 - 1)A_5$ has edge entry $e_5 = (\sqrt{5}-3)/2 \approx -0.381966$, so on the strong-product non-edge $((0,0), (1,2))$ of $C_5^{\boxtimes 2}$ we get $(B_5 \otimes B_5)_{(0,0),(1,2)} = e_5 \cdot 1 = -0.381966 \ne 1$, and $(B_5 \otimes B_5)$ restricted to the 5-element independent set $S_5 \subseteq C_5^{\boxtimes 2}$ has top eigenvalue $(5-\sqrt{5})/2 \approx 1.381966 \ne 5.0$.
- Consequently, optimizing $\beta_{p,q}(G) = \min \|B\|_{p\to q}^{1/(1 - 1/p + 1/q)}$ over dual-fitting $B = J + (x-1)A$ with $p < q$ bounds the OR-product capacity $\Theta_{\text{OR}}(G)$, **not** $\Theta(G)$: at $(p, q) = (1.5, 3.0)$, $\beta_{1.5, 3.0}(C_7) = 3.155676 < \vartheta(C_7)$, **but** $\beta_{1.5, 3.0}(C_5) = 2.092333 < \sqrt{5}$ — instantly falsified by **Gate G1** (because $\Theta_{\text{OR}}(C_5) = 2 < \sqrt{5} = \Theta(C_5)$).
- For **symmetric** exponents **$p = q$**, however, every symmetric dual-fitting matrix $B$ ($B_{ii}=1, B_{ij}=1$ on non-edges) *still* upper-bounds $\Theta(G)$ — not via Kronecker closure under $\boxtimes$, but via **Hölder duality and Riesz–Thorin interpolation** combined with Lovász's dual SDP characterization:
  $$\|B\|_{p\to p} = \|B\|_{p'\to p'} \;\ge\; \|B\|_{2\to 2} \;\ge\; \lambda_{\max}(B) \;\ge\; \vartheta(G) \;\ge\; \Theta(G).$$
  This exact inequality explains all our numerical observations: $\beta_{p,p}$ satisfies exact Hölder duality $\beta_{p,p} = \beta_{p',p'}$ (verified: $\beta_{1.5, 1.5}(C_5) = \beta_{3.0, 3.0}(C_5) = 2.372758$ and $\beta_{1.5, 1.5}(C_7) = \beta_{3.0, 3.0}(C_7) = 3.647728$), achieves its **unique minimum at $p = q = 2$** ($\beta_{2,2}(C_7) = 3.317667 = \vartheta(C_7)$), and $\min \|B\|_{2\to 2}$ (dual-fit) equals $\vartheta$ on $C_5, C_7, \overline{C_7}, \text{Haemers27}$ while becoming strictly looser on Gilbert-32 ($8.000000 > 5.333333$) and Schläfli-27 ($5.400000 > 3.000000$).

#### Probe 2b: Asymmetric $\gamma_2$-Norm & Schatten-$p$ Quasi-Norm ($\Psi_p$)
- **$\gamma_2$-norm collapse (`solve_theta_gamma2` & `solve_shifted_gamma2`):**
  - Optimizing over primal-fitting (possibly **asymmetric**) matrices $W$ ($W_{ii} = 1$, $W_{ij} = 0$ on non-edges) to maximize $\beta$ subject to $\gamma_2(W - \beta J) \le 1 - \beta$ (returning $\vartheta_{\gamma_2}(G) = 1/\beta^*$) collapses **algebraically** to $\vartheta(G)$ for *every* graph: any PSD witness $\bigl(\begin{smallmatrix} P & M \\ M^\top & Q \end{smallmatrix}\bigr) \succeq 0$ for $M = W - \beta J$ with $P_{ii}, Q_{ii} \le 1 - \beta$ admits a Gram factorization $M_{ij} = \langle u_i, v_j \rangle$, so the diagonal equality $1 - \beta = M_{ii} = \langle u_i, v_i \rangle \le \|u_i\|\|v_i\| \le 1 - \beta$ forces $u_i = v_i$ for every $i$ by Cauchy–Schwarz, hence $M = M^\top \succeq 0$! Numerically, this reproduces $\vartheta(G)$ identically on all 7 single-graph benchmarks with $\max \|W - W^\top\|_\infty = 1.539 \times 10^{-13} \le 1.6 \times 10^{-13}$.
  - Likewise, minimizing $g_2(c) = \gamma_2(M)$ over possibly asymmetric $M = (c+1)W - J$ ($M_{ii} = c$, $M_{ij} = -1$ on non-edges, free on edges) and evaluating the implied bound $2(c+1)/(c + 2 - g_2(c))$ reproduces $\vartheta(C_7) = 3.317667$ across all tested shifts $c \in \{0.5, 1.0, 2.0, \vartheta(C_7)-1 \approx 2.317667\}$ (and yields the looser diagonal-floor bound $g_2 = c = 3.0 \implies 4.000000$ at $c = 3.0 > \vartheta(C_7) - 1$; similarly on $C_5$, $c \in \{0.5, 1.0, \sqrt{5}-1\}$ all reproduce $\sqrt{5}$).
- **Schatten-$p$ quasi-norm $\Psi_p(G)$ ($p \in (0, 2)$):** Defined as $\Psi_p(G) = \inf_W \|W\|_{S_p}^p = \inf_W \sum_i \sigma_i(W)^p$ over primal-fitting matrices $W$ ($W_{ii} = 1$, $W_{ij} = 0$ on non-edges), $\Psi_p$ is **provably submultiplicative under $\boxtimes$** (with $\alpha(G) \le \Psi_p(G)$ by singular-value interlacing on $W[S,S] = I_{|S|}$, hence $\Theta(G) \le \Psi_p(G)$) and interpolates between Haemers' real minrank ($p \to 0^+$) and $\text{Frobenius}^2$ ($p = 2$).
  - On **Haemers-27** ($\overline{\text{Schläfli}}$), the explicit primal-fitting matrix $W = I - A$ (singular values $9^1, 6^6, 0^{20}$) gives $\Psi_{0.01} \le 7.131$, $\Psi_{0.05} \le 7.678$, $\Psi_{0.10} \le 8.423$, $\Psi_{0.12} \le 8.741$ — **beating $\vartheta(\text{Haemers27}) = 9.0$** cleanly for every $p \le 0.12$!
  - On **$C_7$**, however, $\lim_{p \to 0^+} \Psi_p(C_7) = \operatorname{minrank}_{\mathbb{R}}(C_7) = 4 > \vartheta(C_7)$ (and every $C_7$-fitting matrix with $\max_{i\sim j}|W_{ij}| \ge 1$ satisfies $\Psi_p(W) \ge 4$ for all $p > 0$ via the $4\times 4$ minor $\det W[\{0,1,3,5\},\{0,2,3,5\}] = W_{1,2}$ and AM–GM). At all tested finite exponents $p \in \{0.01, 0.05, 0.10, 0.12\}$, multi-start BFGS matches the explicit 4-clique-cover matrix $W_{\text{cc}}$ ($3 \cdot 2^p + 1$) with observed minimum $4.0209$ ($p=0.01$), $4.1058$ ($p=0.05$), $4.2153$ ($p=0.10$), and $4.2602$ ($p=0.12$) — strictly above $4 > \vartheta(C_7)$. This sharply explains *why* spectral-rank interpolation beats $\vartheta$ on graphs with $\operatorname{minrank} < \vartheta$ (Haemers-27) while failing to break $\vartheta$ on $C_7$.

#### Probe 3: Information-Theoretic, Rényi, Barrier, and Asymmetric Spectral Bounds
- **Vrana's weighted $\vartheta(G, P)$:** On non-transitive $C_5 \sqcup K_1$, optimizing $P$ lifts the uniform value $3.0684$ to $\vartheta = 3.2361$. On vertex-transitive $C_7$, concavity in $P$ guarantees the maximum over distributions is attained at uniform $P = \mathbf{1}/7$, collapsing to $\vartheta(C_7) = 3.317667$ (peaked $P$ gives $2.9273$, ramp $2.9733$, 3-indep $3.0000$, single-edge $1.0000$).
- **Sibson / Petz quantum Rényi $\alpha$-bounds:** Minimizing the rank-1 circulant PSD spectral family $S_\alpha(W) = \exp(H_{1/\alpha}(W/n))$ over $W(x) = I + xA \succeq 0$ is monotone increasing across $\alpha \in [0, 2]$ on both $C_5$ (`2.2361 → 2.6848 → 2.8346 → 2.9175 → 2.9591`) and $C_7$ (`3.3177 → 4.0238 → 4.3318 → 4.6073 → 4.7886`; $\alpha = -1$ gives $5.0$ and $7.0$); the tightest value is the $\alpha \to 0^+$ limit, which equals $\vartheta(G)$ (consistent with Mghirbi–Douglas Oct 2026).
- **Primal $\log\det$ barrier ($\mu > 0$):** Drops below $\vartheta(C_7)$ at $\mu = 0.01$ ($3.2780$), but because the unique Lovász optimal primal $X^*(0)$ on $C_5$ is rank-deficient (on the PSD boundary), forcing $X^*(\mu) \succ 0$ strictly decreases $\langle J, X^*(\mu) \rangle$ **below $\sqrt{5}$ on $C_5$** ($2.2162 < 2.2361$ at $\mu = 0.01$; $2.235868 < \sqrt{5}$ at $\mu = 10^{-4}$) for every $\mu > 0$, failing Gate G1.
- **Asymmetric spectral radius $\rho(B)$ & nonnegative Perron–Frobenius $B \ge 0$:** Allowing arbitrary real asymmetric dual-fitting $B$ gives $\rho(B) = 1.3516$ on $C_5$ and $2.4632$ on $C_7$ (failing Gate G1 because $\rho$ is not monotone on principal submatrices of non-normal matrices); restoring monotonicity via $B \ge 0$ (Perron–Frobenius, minimized at $B = J - A$) yields $3.0$ on $C_5$ and $5.0$ on $C_7$ (and $17.0 > 3^2$ on $C_5^{\boxtimes 2}$) — far looser than $\vartheta$.

---

## 4. Open Directions & Concrete Roadmap

1. **Finite-Power Frontier ($\alpha(C_7^{\boxtimes 4}) \le 114, 113, 112$):**
   - Our verified $1{,}016$-orbit census (`search/upper/c7_cube_33_orbits.txt`) completely captures all $33$-bands for $N \in \{115, 114, 113\}$.
   - Because all 4,095 clique/tube/slab/band cuts leave the anchored LP at $115.0$, any decisive attack on $N = 115, 114, 113$ must combine **orbit anchoring** with **odd-cycle / lifted-cut MIP or CDCL SAT encoding** that breaks the $\binom{33}{16}$ split symmetry of $B_0 = S_0 \sqcup S_1$ (e.g., branching first on the $10$-bands inside $R_o$, since every $33$-set has $\ge 3$ $10$-bands on every axis!).
   - Any certified refutation of $N = 113$ ($\alpha(C_7^{\boxtimes 4}) \le 112$) plugs directly into our already-proved Lean theorem `alpha_c7_pow5_le_392_of_pow4_le_112` to establish $\alpha(C_7^{\boxtimes 5}) \le 392$.
2. **Asymptotic Frontier ($\Theta(C_7) < \vartheta(C_7)$):**
   - Our 6-probe obstruction audit (`1`, `2a`, `2b`, `3a`, `3b`, `3c`) establishes analytically that none of the tested single-copy PSD/conic or asymmetric-$\gamma_2$ relaxations ($\vartheta, \vartheta', \vartheta_{\gamma_2}$, shifted $\gamma_2$, Vrana, rank-1 Sibson/Petz), symmetric dual-fitting $\ell_p\to\ell_p$ norms ($\beta_{p,p}$), or circulant 3-tensor monomial/support functionals ($ST, \rho^\theta, F_\theta$) can beat $\vartheta(C_7)$ while surviving Gates G1–G4 — and shows both analytically (via $\lim_{p\to 0^+}\Psi_p(C_7) = \operatorname{minrank}_{\mathbb{R}}(C_7) = 4$) and numerically ($p \in \{0.01, 0.05, 0.10, 0.12\}$ BFGS minimum $3\cdot 2^p + 1 > 4$) that Schatten-$p$ rank interpolation remains stuck above $4$ on $C_7$ despite beating $\vartheta$ on Haemers-27.
   - Any genuine asymptotic breakthrough on $\Theta(C_7)$ must therefore exploit **non-monomial / non-product structure across multiple copies** (e.g., genuine asymptotic spectrum points of $C_7$ distinct from $\vartheta$ and $\mathrm{minrank}$, or multi-copy representation-theoretic SDP hierarchies that preserve $\boxtimes$-submultiplicativity — unlike Lasserre level-2 — and respect Gilbert-32's $\sqrt{20}$ lower bound!).

---

## 5. Reproducibility & Verification Commands

All computational artifacts are deterministic and independently reproducible from the repository root `/home/antigravity/shannon-c7`:

```bash
# 1. C++17 alpha(C_7^3) <= 33 certificate verification (1.952 s logged; ~1–2 s)
g++ -O3 -march=native -std=c++17 -Wall -Wextra search/upper/cert_c7_cube.cpp -o search/upper/cert_c7_cube
./search/upper/cert_c7_cube

# 2. C++17 exhaustive 33-set census of C_7^3 (198.16 s logged, 2 vCPUs)
g++ -O3 -march=native -fopenmp -std=c++17 -Wall -Wextra search/upper/census_c7_cube.cpp -o search/upper/census_c7_cube
./search/upper/census_c7_cube

# 3. C++17 structural, profile & 1-swap audit (~11 s)
g++ -O3 -march=native -std=c++17 -Wall -Wextra search/upper/audit_c7_quad.cpp -o search/upper/audit_c7_quad
./search/upper/audit_c7_quad search/upper/c7_cube_33_orbits.txt

# 4. Python/HiGHS strengthened 4,095-cut LP/MIP & local-search audit (76.19 s logged)
/home/antigravity/shannon-c7/.venv/bin/python -u search/upper/audit_c7_quad_mip.py \
    --orbits search/upper/c7_cube_33_orbits.txt --sample-orbits 15 \
    --json-out search/upper/c7_quad_audit_results.json

# 5. Track U2 theoretical obstruction testbed (20.17 s logged, 0 warnings)
/home/antigravity/shannon-c7/.venv/bin/python -u search/upper/obstruction_testbed.py \
    --full --json-out search/upper/obstruction_testbed_results.json

# 6. Pure-kernel Lean 4 generator, build & 3-stage axiom audit
/home/antigravity/shannon-c7/.venv/bin/python -u search/upper/gen_alpha_cube_lean.py --out ShannonC7/AlphaC7Cube.lean
flock /tmp/shannon_c7_lake.lock env LEAN_NUM_THREADS=2 lake build \
    ShannonC7.AlphaC7Cube ShannonC7.FinitePowerUpper ShannonC7.Tests.UpperFrontierTests
flock /tmp/shannon_c7_lake.lock env LEAN_NUM_THREADS=1 ./scripts/verify_axioms.sh --verbose \
    ShannonC7.AlphaC7Cube ShannonC7.FinitePowerUpper ShannonC7.Tests.UpperFrontierTests
```

### Verified Lean 4 Build & 3-Stage Axiom Audit Summary

- **Generator (`gen_alpha_cube_lean.py`):** wrote `ShannonC7/AlphaC7Cube.lean` (`5,684` lines, `674.7 KiB` on disk / `669.2 KiB` generator char-count) in `9.45 s` (`canon10Candidates = 10`, `2,016` C1/C2 tree entries, `P5` certs `root = 326, s0_leaf = 432, s3_leaf = 0`).
- **Build (`lake build`, `LEAN_NUM_THREADS=2` for `AlphaC7Cube`/`FinitePowerUpper`; `LEAN_NUM_THREADS=1` for `UpperFrontierTests`):**
  - `ShannonC7.AlphaC7Cube`: **Built cleanly in `391 s`** (`0` errors, `0` warnings).
  - `ShannonC7.FinitePowerUpper`: **Built cleanly in `10 s`** (`0` errors, `0` warnings).
  - `ShannonC7.Tests.UpperFrontierTests`: **Built cleanly in `8.7 s`** (`0` errors, `0` warnings; `Build completed successfully (2741 jobs)`).
- **3-Stage Axiom Audit (`./scripts/verify_axioms.sh --verbose`, `exit 0`):**
  - Stage 1: `STATIC HYGIENE PASSED: 0 forbidden tokens across 3 file(s).`
  - Stage 2: `All targets up-to-date (2741 jobs).`
  - Stage 3 (`trustLevel := 0` C++ kernel replay): `AXIOM AUDIT PASSED: 1305 total declarations (11 public theorems) across 3 module(s) (replayed 8 local module(s), 1603 constants); axioms ⊆ [propext, Classical.choice, Quot.sound]`
  - All 11 public theorems (`alpha_c7_pow3_le`, `alpha_c7_pow3`, `alpha_c7_pow_succ_le`, `alpha_c7_pow_succ_le_div`, `alpha_c7_pow_le_lovasz_pow`, `alpha_c7_pow_le_of_rational`, `alpha_c7_pow4_le_115`, `alpha_c7_pow5_le_401`, `alpha_c7_pow5_le_of_pow4`, `alpha_c7_pow5_le_392_of_pow4_le_112`, `alpha_c7_pow5_le_388_of_pow4_le_111`) depend strictly on `[propext, Classical.choice, Quot.sound]`.

