import ShannonC7.Defs
import ShannonC7.CycleC7
import ShannonC7.Lovasz
import ShannonC7.LovaszC7
import ShannonC7.CubicBounds
import ShannonC7.AlphaC7Cube
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite-Power Upper Bounds for `C₇` (`ShannonC7/FinitePowerUpper.lean`)

Proves unconditional and conditional finite-power upper bounds on
`(strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum` in the pure Lean 4 kernel:
- General slice double-counting step `alpha_c7_pow_succ_le` (and `Nat` division form)
- General Lovász power bound `alpha_c7_pow_le_lovasz_pow` and cubic-rational helper
  `alpha_c7_pow_le_of_rational`
- Unconditional `alpha_c7_pow4_le_115` (from `alpha_c7_pow3_le` + double counting)
- Unconditional `alpha_c7_pow5_le_401` (from `c7LovaszCert.pow 5` + `q = 33177 / 10000`,
  strictly sharpening the double-counting bound `⌊7 * 115 / 2⌋ = 402`)
- Conditional double-counting bridge `alpha_c7_pow5_le_of_pow4` and explicit corollaries
  `alpha_c7_pow5_le_392_of_pow4_le_112` and `alpha_c7_pow5_le_388_of_pow4_le_111`.
-/

namespace ShannonC7

/-- General slice double-counting step on textbook `Fin d → Fin 7` strong powers of `C₇`:
`2 * α(C₇^⊠(d+1)) ≤ 7 * α(C₇^⊠d)`. -/
theorem alpha_c7_pow_succ_le (d : ℕ) :
    2 * (strongPowPi (SimpleGraph.cycleGraph 7) (d + 1)).indepNum ≤
      7 * (strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum := by
  have h := c7_sliceDoubleCount (strongPow C7 d)
  change 2 * (strongPow C7 (d + 1)).indepNum ≤ 7 * (strongPow C7 d).indepNum at h
  rw [iso_indepNum_eq (strongPowCongr c7IsoCycleGraph (d + 1)),
    iso_indepNum_eq (strongPowCongr c7IsoCycleGraph d),
    strongPow_indepNum_eq_pi, strongPow_indepNum_eq_pi] at h
  exact h

/-- `Nat` division form of slice double-counting: `α(C₇^⊠d) ≤ k → α(C₇^⊠(d+1)) ≤ (7 * k) / 2`. -/
theorem alpha_c7_pow_succ_le_div {d k : ℕ}
    (hk : (strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum ≤ k) :
    (strongPowPi (SimpleGraph.cycleGraph 7) (d + 1)).indepNum ≤ (7 * k) / 2 := by
  have h := alpha_c7_pow_succ_le d
  omega

/-- Finite-power Lovász upper bound directly via Kronecker power certificates (no `Real.rpow`):
`α(C₇^⊠d) ≤ lovaszThetaC7 ^ d` for all `d : ℕ`. -/
theorem alpha_c7_pow_le_lovasz_pow (d : ℕ) :
    ((strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ≤ lovaszThetaC7 ^ d := by
  have h := (c7LovaszCert.pow d).indepNum_le
  rw [strongPow_indepNum_eq_pi, inv_pow, inv_inv] at h
  exact h

/-- Zero-`π` integer ceiling helper from the minimal cubic of `lovaszThetaC7`:
if `3 ≤ q`, `0 < q³ + 7 q² - 49 q + 49`, and `q^d < N + 1`, then `α(C₇^⊠d) ≤ N`. -/
theorem alpha_c7_pow_le_of_rational {d N : ℕ} {q : ℝ} (hq : 3 ≤ q)
    (hpoly : 0 < q ^ 3 + 7 * q ^ 2 - 49 * q + 49)
    (hpow : q ^ d < (N + 1 : ℝ)) :
    (strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum ≤ N := by
  have hα : ((strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ≤ lovaszThetaC7 ^ d :=
    alpha_c7_pow_le_lovasz_pow d
  have hθ_lt : lovaszThetaC7 < q := lovaszThetaC7_lt_of_cubic_pos hq hpoly
  have hθ_nonneg : 0 ≤ lovaszThetaC7 := by linarith [lovaszThetaC7_gt_three]
  have hpow_le : lovaszThetaC7 ^ d ≤ q ^ d :=
    pow_le_pow_left₀ hθ_nonneg hθ_lt.le d
  have hlt_real :
      ((strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) < ((N + 1 : ℕ) : ℝ) := by
    push_cast
    exact lt_of_le_of_lt (hα.trans hpow_le) hpow
  have hlt_nat : (strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum < N + 1 := by
    exact_mod_cast hlt_real
  exact Nat.lt_succ_iff.mp hlt_nat

/-- Unconditional 4th-power upper bound `α(C₇^⊠4) ≤ 115` from `α(C₇^⊠3) ≤ 33` and
slice double-counting (`⌊7 * 33 / 2⌋ = 115`, sharper than Lovász's `⌊ϑ(C₇)^4⌋ = 121`). -/
theorem alpha_c7_pow4_le_115 :
    (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum ≤ 115 :=
  alpha_c7_pow_succ_le_div alpha_c7_pow3_le

/-- Unconditional 5th-power upper bound `α(C₇^⊠5) ≤ 401` from `c7LovaszCert.pow 5` and
`lovaszThetaC7 < 33177 / 10000` (note `(33177 / 10000)^5 = 401.966398... < 402`,
sharper than double-counting `⌊7 * 115 / 2⌋ = 402`). -/
theorem alpha_c7_pow5_le_401 :
    (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum ≤ 401 :=
  alpha_c7_pow_le_of_rational (q := (33177 : ℝ) / 10000) (by norm_num) (by norm_num) (by norm_num)

/-- Conditional slice double-counting bridge from the 4th power to the 5th power:
`α(C₇^⊠4) ≤ k → α(C₇^⊠5) ≤ (7 * k) / 2`. -/
theorem alpha_c7_pow5_le_of_pow4 {k : ℕ}
    (hk : (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum ≤ k) :
    (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum ≤ (7 * k) / 2 :=
  alpha_c7_pow_succ_le_div hk

/-- Conditional corollary matching the Oct 2026 Evidence Press candidate:
`α(C₇^⊠4) ≤ 112 → α(C₇^⊠5) ≤ 392`. -/
theorem alpha_c7_pow5_le_392_of_pow4_le_112
    (h : (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum ≤ 112) :
    (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum ≤ 392 :=
  alpha_c7_pow5_le_of_pow4 h

/-- Conditional corollary for further 4th-power tightening:
`α(C₇^⊠4) ≤ 111 → α(C₇^⊠5) ≤ 388`. -/
theorem alpha_c7_pow5_le_388_of_pow4_le_111
    (h : (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum ≤ 111) :
    (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum ≤ 388 :=
  alpha_c7_pow5_le_of_pow4 h

end ShannonC7
