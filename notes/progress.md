# Orchestrator Progress (`orchestrator_r2`)

## Current Status
Last visited: 2026-11-27T06:09:45Z

- [x] Record Sentinel crash-recovery dispatch in `DISPATCH.md`
- [x] Reconstruct exact project state from `ORIGINAL_REQUEST.md`, `PROJECT.md`, `orchestrator_r1`, and active sub-orchestrator state folders (`sub_orch_m1_gen5`, `sub_orch_m4_gen2`, `sub_orch_e2e_gen5`)
- [x] Inherited DONE milestones (DO NOT REDO):
  - `M2_UpperTheory` (5/5 Iter 1 PASS — `/home/antigravity/.agents/teamwork/sub_orch_m2/handoff.md`)
  - `M3_LowerEngine` (5/5 PASS — `/home/antigravity/.agents/teamwork/sub_orch_m3_gen2/handoff.md`)
  - `M5_UpperFrontier` (5/5 Iter 2 PASS — `/home/antigravity/.agents/teamwork/sub_orch_m5/handoff.md`)
- [x] Initialize `BRIEFING.md`, `progress.md`, define `teamwork_sub_orchestrator`, prepare fresh successor folders (`sub_orch_m1_gen6`, `sub_orch_m4_gen3`, `sub_orch_e2e_gen6`), and launch all 3 recovered sub-orchestrators in parallel
- [x] **`M1_Core` / Task 1–2 (`scripts/verify_axioms.sh` Wave 12)**: Re-verified full local baseline (`lake build ShannonC7`: 2,756 jobs, 0 errors, 0 warnings in 1m14s; `./scripts/verify_axioms.sh --verbose`: 3,600 decls / 564 public theorems across 20 modules, kernel-replayed with `axioms ⊆ [propext, Classical.choice, Quot.sound]`). Hardened `scripts/verify_axioms.sh` `set_option` check from denylist to closed positive whitelist (`isAllowedOptionName`), verified 15/15 adversarial test cases + unknown-option rejection + full 20-module 3-stage audit PASS.
- [x] **`M4_LowerFrontier` / Task 2 (`search/lower/verify_witness.py` Wave 8)**: Verified Mathematically Closed 7-Gate Positive Whitelist (Stage 7A) + Closed Lexical Whitelist (Stage 7B), `75/75` self-tests PASS, and live paired witness + `ShannonC7/FrontierLower.lean` (`3258822357711717/10^15`, `d=220`, 113 digits) PASS.
- [x] **`E2E_Track` / Task 3**: Fixed `verify/common.py` `lake build` invocation for Lake 5.0.0 (`LEAN_NUM_THREADS=2` instead of unsupported `-j 2`), verified `verify/run_e2e.sh --self-test` (`18/18 PASS`), `--list` (`164 + 18`), zero bytecode pollution, and published `TEST_READY.md`.
- [x] **`M6_Final` / Task 4**: Created `ShannonC7/Main.lean` (exporting all 16 § 4.4 symbols + canonical sandwiches + open-problem `Prop`s) and `RESULTS.md`. Full verification passed: `lake build ShannonC7` (`2757` jobs, 0 errors, 0 warnings), `./scripts/verify_axioms.sh` (`3605` total decls / `567` public theorems across 21 modules, `axioms ⊆ [propext, Classical.choice, Quot.sound]`), `verify/run_e2e.sh --all` (**164/164 PASS**, exit 0), `verify/run_e2e.sh --self-test` (**18/18 PASS**), and `verify_witness.py` PASS.
- [x] **Stretch / Task 5A (`ShannonC7/PortfolioLower.lean`, commit `5ea0af2`)**: Discovered **Decoupled Portfolio Free-J Auxiliary Upgrading** (`AuxPartition.upg1FreeJ`) combined with 3-fold (`Γ₆^⊠3`, 21-term `portfolioPat3`) and 4-fold (`Γ₆^⊠4`, 57-term `portfolioPat4`) pullbacks. Rather than collapsing `PortCore` port density `d/a` via single-aux `prodXupg1`, we keep `PortCore` built via `prodStd` (`d/a ≈ 0.50`) and recursively attach decoupled upgraded auxiliary partitions using arbitrary independent sets `J₂` (`M₂, M₄, M₆, M₉, M₁₄`).
  - **New pure-kernel Lean 4 theorem** `ShannonC7.c7_lower_portfolio` (imported by `ShannonC7/Main.lean`):
    $$\frac{3258827798879807}{1000000000000000} \le \Theta(C_7)$$
    via a 113-digit witness in $C_7^{\boxtimes 220}$ (`portfolioCard = 74732706807043919643697829190664893546186880071325260826072346221160104101520910506260341279794670838950095660097`), plus `c7_lower_portfolio_gt_frontier` proving strict improvement of **`+0.0000054412`** over M4's `c7_lower_frontier` (`3.258822357711717`, `d=220`).
  - Closes **96.7%** of the gap from M4 to BPZ v2 (`3.258827985920007`, `d=500`, `native_decide`) at less than half the dimension ($d=220$ vs $d=500$) and with zero `native_decide`; honestly remains `1.870e-7` below BPZ v2 and `4.821e-6` below Tandon (`3.258832620353`, `d=500`, unrefereed preprint).
  - **Verified clean:** `lake build ShannonC7` (2,758 jobs, 0 errors, 0 warnings), `./scripts/verify_axioms.sh` (**0 forbidden tokens across 22 files; 3,747 total declarations / 609 public theorems kernel-replayed; axioms ⊆ [propext, Classical.choice, Quot.sound]**), `verify/run_e2e.sh --all --no-build` (**164/164 PASS**), `verify/run_e2e.sh --self-test` (**18/18 PASS**), and `verify_witness.py` PASS (locked `FrontierLower.lean` and `RESULTS.md` untouched).
  - **Failed / saturated lower-bound attempts (honest report):** `LayeredTuple` with 5D $b_0 \le 7$ (and even hypothetical $b_X = 8$) peaked at `3.258724`; automatic `LayeredTuple` from `prodXupg1` peaked at `3.25882689`; 3-way `prodCore3` + `Aux3_freeJ` peaked at `3.25882694`; `auxB` (`O=B`) caused Pareto-beam collapse to `3.258742`; $d=10$ surgical port-5/7 unlocking lost more `a₂`/`d₂` than gained; `Γ_Q^2` exact MIP at $d=10$ did not beat `134,753`; higher `Γ₆^⊠5` pullbacks did not exceed `3.258827798879807`. Reaching BPZ v2 / Tandon (`d=500`) requires heterogeneous multi-layer substitution machinery beyond 2-state `Γ₆`.
- [x] **Stretch / Task 5B (`α(C₇⁴) ≤ 112` & `≤ 114` feasibility probe)**: Conducted quantitative computational feasibility benchmarks on $C_7^{\boxtimes 4}$ (`2,401` vertices) anchored on the `1,016` canonical $C_7^{\boxtimes 3}$ 33-set orbits (`search/upper/c7_cube_33_orbits.txt`):
  - **Anchored LP relaxation obstruction:** Even after anchoring Band 0 to a canonical 33-set $R_o$ and adding all `4,830` geometric cuts (`2,401` $K_2^4$-cliques $\le 1$, `1,372` 3-tubes $\le 3$, `1,029` 10-slabs $\le 10$, `28` 33-bands $\le 33$), the exact HiGHS LP optimum remains identically **`115.500000`** on Orbits `#467`, `#0`, and `#100` (witnessed by the fractional point $x_{t,v} = \frac{1}{2} \mathbf{1}_{v \in R_o}$ across all 7 slices). Thus pure LP/Farkas certificates cannot even close $N=115$ ($\alpha \le 114$) without branching or higher-order SDP/Terwilliger cuts.
  - **CP-SAT & CDCL SAT (CaDiCaL 1.9.5) benchmarks:** CP-SAT with all 4,095 cuts on Orbit `#467` ($N=115$) stalled at 60 conflicts in 20.13s (`UNKNOWN`). Pure CaDiCaL 1.9.5 reached `1,000,000` conflicts in 26.49s (`BUDGET`) on Orbit `#467` for $N=115$ (exact profile `(16,17,16,17,16,17,16)`) and `500,000` conflicts in 12.69s (`BUDGET`) for $N=113$ (`(16,17,16,16,16,16,16)`), without refuting a single one of the `1,016` orbits.
  - **Exact 33-band transition branching (`N=115`):** Even under the strict subset `|B₀ ∩ B₁| = 17` (ignoring overlapping non-adjacent slices `|B₀ ∩ B₁| > 17`, up to `B₀ = B₁` with $\binom{33}{17} \approx 1.17 \times 10^9$ splits), Orbit `#467` has `8,484` `R₁` candidates (`3,012` distinct `(S₀,S₁)`) and Orbit `#0` has `3,228` (`1,173` distinct), with exact 128-bit Tomita branching factors `16→17`: avg `7.85–9.91` (max `60–150`) and `17→16`: avg `86.4–120.9` (max `215–309`).
  - **Conclusion:** Direct SAT/MIP/branch-and-bound refutation of $\alpha(C_7^{\boxtimes 4}) \le 114$ or $\le 112$ across all 1,016 orbits (and multi-profile $N=113$) is computationally intractable for direct pure-kernel Lean 4 replay without a dedicated SDP/symmetry-reduction certificate; `ShannonC7.alpha_c7_pow4_le_115` remains our certified pure-kernel upper bound on $C_7^{\boxtimes 4}$.

## Iteration Status
Current iteration: 1 / 32 (QUOTA ALERT on `M1_gen6` escalated to Sentinel at 06:09Z; `M4` Wave 8 & `E2E` Wave r14 still running; exact checkpoint persisted on disk!)

---

## Milestone M3 (`ComplementAndStructural`) — 2026-11-27T20:28:00Z

### Track L2 — Complement $\overline{C_7}$ Lower-Bound Breakthrough (`ShannonC7/ComplementLower.lean`)
- **Finite-power & asymptotic `PartGadget` records (beating Bohman–Holzman $17^{1/4} \approx 2.030543185$):**
  - Direct $d=5$ code (`C35`, `4orb+ext` in $\overline{C_7}^{\boxtimes 5}$): `alpha_c7_compl_pow5_ge_35` ($\alpha(\overline{C_7}^{\boxtimes 5}) \ge 35$) and `c7_compl_lower_35` ($35^{1/5} \le \Theta(\overline{C_7})$, $\approx 2.036168077$).
  - Pure-kernel `PartGadget` `(35, 1, 35, 23, 7, 5)` (`search/lower/compl_witnesses/compl_c7_d5_partgadget.json`) lifted via an 8-node `prodStd` + `prodXupg1` DAG to $d=140$ (`complFrontierCard = 17630403766597908028404660108047961464583300`):
    - `c7_compl_lower_frontier`: `2036581869953041 / 10^15 ≤ shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ` ($\approx 2.036581869953041$).
    - `c7_compl_lower_gt_bh`: `(17 : ℝ) ^ (1 / 4 : ℝ) < shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ`.
    - `c7_compl_lower_gt_35`: `(35 : ℝ) ^ (1 / 5 : ℝ) < shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ`.
- **Supporting search tooling (`search/lower/compl_*`):** `compl_d5_sat.py`, `compl_d4_exact.cpp`, `compl_d5_search.cpp`, `compl_orbit_search.cpp`, `compl_d5_blowup.cpp`, `compl_d5_opt_gadget.cpp`, `compl_gadget_search.cpp`, `compl_gadget_search.py`, `compl_emit_lean.py`.
- **Honest open leads & dead ends:**
  - $d=3$: exact $\alpha(\overline{C_7}^{\boxtimes 3}) = 8$ (`OPTIMAL` via CP-SAT).
  - $d=4$: $K_3$-slice double counting gives $\alpha(\overline{C_7}^{\boxtimes 4}) \le 18$ across 4 canonical profiles; exact `17` vs `18` timed out $>90\text{s}$ on Profile 0, so exact $\alpha(\overline{C_7}^{\boxtimes 4}) \in \{17, 18\}$ remains open (discovered $d=4$ `PartGadget` `(17, 1, 17, 7, 5, 5)` reaching `2.03180354` at $d=64$, superseded by $d=5$).
  - $d=5$: exhaustive 5-orbit canonical scan (28 generators, 6,720 size-35 codes), `2.15M` 4-orbit extensions, 18,270 LNS steps, and 663k ILS steps achieved max `35` (`36..41` remain open). Pure 5-orbit `S35` failed `c=35` in `Aut`-scans and negation-symmetric ILS maxed at `33`/`34`, whereas non-orbit `C35` succeeded.
  - $d=6, 7$: orbit search + LNS reached `70` ($d=6$, `71..88` open) and `140` ($d=7$, `143..186` open).

### Track S1/S2 — Structural, Exact & Barrier Theorems (`ShannonC7/StructuralBounds.lean`, `ShannonC7/Tests/StructuralTests.lean`)
- **General odd-cycle square exactness:** `oddCycle_pow2_indepNum` and `oddCycle_pow2_indepNum_eq_div` prove $\alpha(C_{2k+1}^{\boxtimes 2}) = k^2 + \lfloor k/2 \rfloor = \lfloor k(2k+1)/2 \rfloor$ for all $k \ge 1$ (`1, 5, 10, 18, 27` for $k=1..5$), via `cycleGraph_sliceDoubleCount` and `oddCycle_indepNum` (correcting an earlier draft typo `k(2k+1) + ⌊k/2⌋`).
- **Fractional clique cover, Lovász complement & $\mathbb{Q}(\cos(\pi/7))$, torus packing & Rosenfeld equivalence:**
  - `FracCliqueCover`, `FracIndepSet`, weak duality, `shannonCapacity_le_fracCliqueCoverNum`, `IsVertexTransitive`, `c7_fracCliqueCoverNum` ($7/2$), `c7_compl_fracCliqueCoverNum` ($7/3$), and trig-free upper bounds `c7_upper_fracCliqueCover` ($\Theta(C_7) \le 7/2$) and `c7_compl_upper_fracCliqueCover` ($\Theta(\overline{C_7}) \le 7/3$).
  - `lovaszThetaOddCycle_mul_compl`, `lovaszThetaC7_mul_compl` ($\vartheta(C_7)\vartheta(\overline{C_7}) = 7$), `c7_shannonCapacity_mul_compl_le` ($\Theta(C_7)\Theta(\overline{C_7}) \le 7$), and exact $\mathbb{Q}(\cos(\pi/7))$ polynomial/cubic identities (`cos_pi_div_seven_inv_eq_poly`, `lovaszThetaC7_eq_poly_cos`, `lovaszThetaC7Compl_eq_poly_cos`, `lovaszThetaC7_sub_compl`, `lovaszThetaC7Compl_cubic`).
  - $2^d$-torus box packing (`torusBox`, `c7Pow_isIndepSet_iff_pairwiseDisjoint_boxes`, `c7Pow_volume_bound`, $L_\infty \ge 2$ via `c7Pow_isIndepSet_iff_linf_ge_two`), cohomomorphism monotonicity (`shannonCapacity_mono_cohom`), `c7_prod_compl_shannonCapacity_ge_seven`, clique/disjoint blowups, and Rosenfeld $k$-fold equivalence (`lexIndepBlowup_indepNum`, `fracCliqueCoverNum_le_of_lexBlowup_cliqueCover`, `exists_lexBlowup_cliqueCover_of_fracCliqueCover`).
- **Barrier & obstruction theorems:**
  - Unified primal/dual SDP (`lovaszTheta`, `schrijverTheta`, `SchrijverCert`, `indepNum_le_schrijverTheta`).
  - `Gilbert32` ($\mathrm{Fin}\,32$, Hamming distance $\in \{1,2\}$): `gilbert32_indep_four` ($\alpha = 4$), `gilbert32_sq_indep_twenty` ($\alpha(G_{32}^{\boxtimes 2}) \ge 20$), `gilbert32_schrijverTheta_eq_four` ($\vartheta'(G_{32}) = 4$), `gilbert32_schrijver_fails_submult` ($\vartheta'(G_{32})^2 = 16 < 20$), and `gilbert32_lovaszTheta_eq` ($16/3$).
  - `Haemers27` ($\mathrm{srg}(27,10,1,5)$) & `Schlafli27` ($\mathrm{srg}(27,16,10,8)$): `haemers27_minrank_le_seven` (all fields `F`; `= 7` for `haemers27FittingMatrix` under `[CharZero F]`), `haemers27_lovaszTheta_eq_nine` ($\vartheta = 9$), `haemers27_haemers_beats_lovasz` ($\Theta(H_{27}) \le 7 < 9 = \vartheta(H_{27})$), `schlafli27_exact` ($\alpha = \Theta = \vartheta = 3$), and `haemers27_schlafli27_gate_g3` ($7 \cdot 3 = 21 < 27$).
  - Bukh–Cox fractional Haemers bound (`FracHaemersRep`, `fracHaemers`, `shannonCapacity_le_fracHaemers`): `fracHaemers_oddCycle` ($\mathcal{H}_f^{\mathbb{F}}(C_{2k+1}) = (2k+1)/2$ for $k \ge 2$ over every field `F`), `fracHaemers_c7` ($7/2$), and `lovaszThetaC7_lt_fracHaemers_c7` ($\vartheta(C_7) < \mathcal{H}_f^{\mathbb{F}}(C_7)$).
- **Verified clean:**
  - `LEAN_NUM_THREADS=4 lake build ShannonC7.ComplementLower ShannonC7.StructuralBounds ShannonC7.Tests.StructuralTests`: **0 errors, 0 warnings** (`2752` jobs).
  - `./scripts/verify_axioms.sh --verbose ShannonC7.ComplementLower ShannonC7.StructuralBounds ShannonC7.Tests.StructuralTests`: **PASSED** (`784` total declarations / `117` public theorems across `3` modules; `0` forbidden tokens; `axioms ⊆ [propext, Classical.choice, Quot.sound]`).
  - `find verify -name "__pycache__" -o -name "*.pyc"`: empty.
  - (Pending M4 final integration: importing `ComplementLower` and `StructuralBounds` into `Main.lean` and updating `RESULTS.md`.)

---

## Milestone M1 (`LowerFrontier`) — 2026-11-27T22:15:00Z

### Track L1 — Heterogeneous Multi-Layer Substitution $d=620$ Lower-Bound Breakthrough (`ShannonC7/TandonLower.lean`)
- **New pure-kernel Lean 4 lower bound (`ShannonC7.TandonLower.c7_lower_m1` at $d=620$):**
  $$\frac{3258835618853760}{10^{15}} = 3.258835618853760 \le \Theta(C_7)$$
  certified via a 319-digit witness `m620Card` in $C_7^{\boxtimes 620}$ (`c7_lower_m1_card`, `c7_lower_m1_pow_le`, `c7_lower_m1_sharp`), strictly surpassing:
  - `PortfolioLower.lean` (`3.258827798879807`, $d=220$, `c7_lower_m1_gt_portfolio`),
  - BPZ v2 (`3.258827985920007`, $d=500$, `native_decide`, `c7_lower_m1_gt_bpz_v2`),
  - Tandon (`arXiv:2608.30273`, `3.258832620353266`, $d=500$, `c7_lower_m1_gt_tandon`).
- **New Lean 4 modules (pure kernel, zero `sorry` / `native_decide` / `partial`):**
  - `ShannonC7/LayeredSubstLower.lean`: pure-kernel multi-arity `Subst` / `Code` / `Realisation.multiSubst` infrastructure, `rfl`-certified BPZ substitution/code tables (`T2a_ok`, `T3b_ok`, `C4a_ok`, `S2a`, `S3b`, `K4a`), and `HetLeftInput` / `Realisation.hetGao` / `w_hetGao` / `hetGao_P_O_eq`.
  - `ShannonC7/TandonDataLower.lean`: pure-kernel 5D tries (`tB5`..`tX15`), `T5_fn` / `T5_inv`, 20-set 5D rectangle partition, 4-bit closed-neighborhood signatures, and `Vec16` histogram lemmas.
  - `ShannonC7/TandonLower.lean`: in-kernel certificate proofs of `C₁ = 27,488` (`J10_out_card`), `C₂ = 12,839,823` (`J15_out_card`), and `C₄ = 841,760,069,965,664` (`J30pp_out_card`), building `R40_s0`, `R65_s1`, `R50_s2`, `R155 = S3b(R40_s0, R65_s1, R50_s2)`, and `m620Card_le_pi` (`K4a(R155^4)`).
  - `ShannonC7/Tests/TandonLowerTests.lean`: contract checks, layer weights ($d = 5..155$), strict improvement & sharpness checks, and `#print axioms`.
- **Supporting witness & verification tooling (`search/lower/`):**
  - `search/lower/witnesses/m1_tandon_d620.json`, `search/lower/verify_m1_tandon.py`, `search/lower/M1_SEARCH_NOTES.md`.
- **Honest dead-end summary (`search/lower/M1_SEARCH_NOTES.md`):**
  - Exhaustive `64,538,880`-automorphism `Aut(C_7^5)` 10D `T'` scan peaked at `27,480` (none `> 27,480`).
  - Exhaustive `282,475,249`-vertex 10D `0`/`1`-tight swap scan on `J^+` found `0` improvements beyond `C₁ = 27,488`.
  - Track S1 5D probes (`PortSystem.ofColoring` on `R_{5,7}` / `R_9` peaked at `314`/`313`; `AuxPartition` ILS capped at `322`; `C_7^5` MIS probe peaked at `367`; non-367 `b >= 8 + 11*(367-a)` ILS peaked at `3625 < 4045`).
  - Track S2 `Γ_Q^⊠2` exact CP-SAT optimum `= 134,689 < 134,753 = |I₁₀|`.
  - `S3` / `K4` CP-SAT over `Letter.sep` and `1,036`-point asymmetric `K4a` coordinate polish yielded no improvement over `S3b` + `K4a`.
- **Verified clean:**
  - `LEAN_NUM_THREADS=4 lake build ShannonC7.LayeredSubstLower ShannonC7.TandonDataLower ShannonC7.TandonLower ShannonC7.Tests.TandonLowerTests`: `2059` jobs, `0` errors, `0` warnings.
  - `./scripts/verify_axioms.sh --verbose ShannonC7.LayeredSubstLower ShannonC7.TandonDataLower ShannonC7.TandonLower ShannonC7.Tests.TandonLowerTests`: **PASSED** (`1672` total declarations, `530` public theorems, `0` forbidden tokens, `axioms ⊆ [propext, Classical.choice, Quot.sound]`).
  - `python3 -B search/lower/verify_m1_tandon.py`: **PASSED** (`C1=27488`, `C2=12839823`, `C4=841760069965664`, 319-digit `M620`, `3.258835618853760`).
  - `find verify -name "__pycache__" -o -name "*.pyc"`: empty.
  - (Pending M4 final integration: promoting `ShannonC7.TandonLower.c7_lower_m1` into `ShannonC7/Main.lean`, `RESULTS.md`, and `verify/cross_check.py`, and updating the default `180s` timeout in `verify/` since the full 29-module `./scripts/verify_axioms.sh` audit takes `~224s`.)
