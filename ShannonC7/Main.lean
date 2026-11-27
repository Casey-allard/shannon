import ShannonC7.Defs
import ShannonC7.Fekete
import ShannonC7.CycleC7
import ShannonC7.Lovasz
import ShannonC7.LovaszC7
import ShannonC7.CubicBounds
import ShannonC7.Haemers
import ShannonC7.TrieVerifier
import ShannonC7.Decimal
import ShannonC7.SmallPowers
import ShannonC7.ValidTuple
import ShannonC7.HeteroLayered
import ShannonC7.FrontierLower
import ShannonC7.PortfolioLower
import ShannonC7.AlphaC7Cube
import ShannonC7.FinitePowerUpper

/-!
# Shannon Capacity of the 7-Cycle (`ShannonC7.Main`)

Canonical public entry point unifying the pure-kernel Lean 4 formalization of the Shannon
capacity of the 7-cycle `SimpleGraph.cycleGraph 7`:

- **Core & Fekete limit:** `shannonCapacity`, `strongPowPi`, `c7_shannonCapacity_tendsto`.
- **Exact small powers:** `alpha_c7_pow1` (`= 3`), `alpha_c7_pow2` (`= 10`),
  `alpha_c7_pow3` (`= 33`), plus `alpha_c7_pow4_ge` (`≥ 108`), `alpha_c7_pow4_le_115` (`≤ 115`),
  `alpha_c7_pow5_ge_367` (`≥ 367`), `alpha_c7_pow5_le_401` (`≤ 401`).
- **Upper bounds & obstructions:** `lovaszThetaC7`, `c7_upper_lovasz`, `c7_upper_rational`
  (`< 3317667207395 / 10^12`), `c7_lovasz_unattainable` (Galois cubic unattainability),
  `shannonCapacity_le_haemers_rank`, `haemers_minrank_c7_ge_four`.
- **Frontier lower bound (pure kernel):** `c7_lower_num = 3258822357711717`,
  `c7_lower_den = 1000000000000000`, `c7_lower_frontier`, and `c7_shannonCapacity_sandwich`.
- **Generalizations:** `c7_compl_sandwich`, `c5_shannonCapacity_eq_sqrt_five`,
  `oddCycle_upper_lovasz`.
- **Open-problem propositions:** `OpenQuestion_StrictGap`, `OpenQuestion_ExactValue`.

All theorems verify in the pure Lean 4 kernel with axioms strictly within
`{propext, Classical.choice, Quot.sound}` (zero `sorry`, zero `native_decide`, zero `partial`).
-/

namespace ShannonC7

/-! ## 1. Fekete Limit for `C₇` -/

/-- Fekete limit theorem specialized to Mathlib's `SimpleGraph.cycleGraph 7`. -/
theorem c7_shannonCapacity_tendsto :
    Filter.Tendsto
      (fun d : ℕ => ((strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ^ (1 / (d : ℝ)))
      Filter.atTop (nhds (shannonCapacity (SimpleGraph.cycleGraph 7))) :=
  shannonCapacity_tendsto (SimpleGraph.cycleGraph 7)

/-! ## 2. Canonical Sandwiches for `C₇` and `C₇ᶜ` -/

/-- Canonical pure-kernel sandwich for `Θ(C₇)`:
`3258822357711717 / 10^15 ≤ shannonCapacity (SimpleGraph.cycleGraph 7) ≤ lovaszThetaC7`. -/
theorem c7_shannonCapacity_sandwich :
    (c7_lower_num : ℝ) / (c7_lower_den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) ∧
    shannonCapacity (SimpleGraph.cycleGraph 7) ≤ lovaszThetaC7 :=
  ⟨c7_lower_frontier, c7_upper_lovasz⟩

/-- Canonical pure-kernel sandwich for the complement `C₇ᶜ`:
`17^(1/4) ≤ shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ≤ 1 + (cos (π / 7))⁻¹`. -/
theorem c7_compl_sandwich :
    (17 : ℝ) ^ (1 / 4 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ∧
    shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ≤ 1 + (Real.cos (Real.pi / 7))⁻¹ :=
  ⟨c7_compl_lower_17, c7_compl_upper_lovasz⟩

/-! ## 3. Formal Open-Problem Statements -/

/-- Open question (70 years since Shannon 1956): is `Θ(C₇)` strictly smaller than `ϑ(C₇)`? -/
def OpenQuestion_StrictGap : Prop :=
  shannonCapacity (SimpleGraph.cycleGraph 7) < lovaszThetaC7

/-- Open question: determining the exact real value of `Θ(C₇)`. -/
def OpenQuestion_ExactValue : Prop :=
  ∃ c : ℝ, shannonCapacity (SimpleGraph.cycleGraph 7) = c

end ShannonC7
