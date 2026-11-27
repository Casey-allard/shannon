import ShannonC7.AlphaC7Cube
import ShannonC7.FinitePowerUpper

/-!
# Upper-Frontier Unit Tests & Contract Conformance (`ShannonC7/Tests/UpperFrontierTests.lean`)

Validates:
1. Verbatim type-signature conformance with `M5_UpperFrontier` scope (`AlphaC7Cube` & `FinitePowerUpper`).
2. Edge-case and functional sanity checks (`d = 0, 1, 2` instantiations and conditional `d = 4 → 5` bridges).
3. Explicit `#print axioms` checks on every public M5 theorem.
-/

namespace ShannonC7.Tests

open ShannonC7

/-! ## 1. Verbatim Interface Contract Conformance (M5 SCOPE.md) -/

section ContractChecks

-- ShannonC7.AlphaC7Cube
example : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum ≤ 33 := alpha_c7_pow3_le
example : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum = 33 := alpha_c7_pow3

-- ShannonC7.FinitePowerUpper
example (d : ℕ) :
    2 * (strongPowPi (SimpleGraph.cycleGraph 7) (d + 1)).indepNum ≤
      7 * (strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum :=
  alpha_c7_pow_succ_le d

example {d k : ℕ} (hk : (strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum ≤ k) :
    (strongPowPi (SimpleGraph.cycleGraph 7) (d + 1)).indepNum ≤ (7 * k) / 2 :=
  alpha_c7_pow_succ_le_div hk

example (d : ℕ) :
    ((strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ≤ lovaszThetaC7 ^ d :=
  alpha_c7_pow_le_lovasz_pow d

example : (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum ≤ 115 := alpha_c7_pow4_le_115
example : (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum ≤ 401 := alpha_c7_pow5_le_401

example {k : ℕ} (hk : (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum ≤ k) :
    (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum ≤ (7 * k) / 2 :=
  alpha_c7_pow5_le_of_pow4 hk

example (h : (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum ≤ 112) :
    (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum ≤ 392 :=
  alpha_c7_pow5_le_392_of_pow4_le_112 h

example (h : (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum ≤ 111) :
    (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum ≤ 388 :=
  alpha_c7_pow5_le_388_of_pow4_le_111 h

end ContractChecks

/-! ## 2. Edge-Case & Functional Sanity Checks -/

-- d = 0 Lovász power bound: α(C₇^0) ≤ 1
example : ((strongPowPi (SimpleGraph.cycleGraph 7) 0).indepNum : ℝ) ≤ lovaszThetaC7 ^ 0 :=
  alpha_c7_pow_le_lovasz_pow 0

-- d = 1 and d = 2 upper bounds derived purely from `FinitePowerUpper` lemmas (no M3 import):
example : (strongPowPi (SimpleGraph.cycleGraph 7) 1).indepNum ≤ 3 :=
  alpha_c7_pow_le_of_rational (q := (7 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num)

example : (strongPowPi (SimpleGraph.cycleGraph 7) 2).indepNum ≤ 10 :=
  alpha_c7_pow_succ_le_div
    (alpha_c7_pow_le_of_rational (d := 1) (N := 3) (q := (7 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num))

-- Double-counting at d = 4 → 5 with k = 114 and k = 113
example (h : (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum ≤ 114) :
    (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum ≤ 399 :=
  alpha_c7_pow5_le_of_pow4 h

example (h : (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum ≤ 113) :
    (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum ≤ 395 :=
  alpha_c7_pow5_le_of_pow4 h

/-! ## 3. Explicit `#print axioms` Checks on All Public M5 Theorems -/

#print axioms ShannonC7.alpha_c7_pow3_le
#print axioms ShannonC7.alpha_c7_pow3
#print axioms ShannonC7.alpha_c7_pow_succ_le
#print axioms ShannonC7.alpha_c7_pow_succ_le_div
#print axioms ShannonC7.alpha_c7_pow_le_lovasz_pow
#print axioms ShannonC7.alpha_c7_pow_le_of_rational
#print axioms ShannonC7.alpha_c7_pow4_le_115
#print axioms ShannonC7.alpha_c7_pow5_le_401
#print axioms ShannonC7.alpha_c7_pow5_le_of_pow4
#print axioms ShannonC7.alpha_c7_pow5_le_392_of_pow4_le_112
#print axioms ShannonC7.alpha_c7_pow5_le_388_of_pow4_le_111

end ShannonC7.Tests
