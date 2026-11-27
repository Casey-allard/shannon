import ShannonC7.FrontierLower
import ShannonC7.ValidTuple

/-!
# Milestone M4 Unit & Contract Tests (`ShannonC7.Tests.FrontierLowerTests`)

Verifies the verbatim `PROJECT.md § 4.4` and `sub_orch_m4/SCOPE.md` public contract for
`ShannonC7.FrontierLower`, exact GMP floor / ceiling / Lovász cubic / last-digit-tightness
inequalities, live functional tests of `AuxPartition` / `PartGadget` (`prodStd`, `prodXupg1`,
`prodXupg2`, `flip`) and `gamma6Pow4_card_le_cycleGraph7_indepNum`, and exhaustive
`#print axioms` checks confirming pure-kernel axioms `⊆ [propext, Classical.choice, Quot.sound]`.
-/

namespace ShannonC7.Tests

open ShannonC7

/-! ## 1. Verbatim Public Contract & Rational Inequality Checks -/

section ContractChecks

example : ℕ := c7_lower_num
example : ℕ := c7_lower_den
example : 0 < c7_lower_den := c7_lower_den_pos

example :
    (c7_lower_num : ℝ) / (c7_lower_den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  c7_lower_frontier

-- Strictly exceeds M3 BPZ v1 baseline (`3258805369885465 / 10^15`)
example :
    (3258805369885465 : ℝ) / 1000000000000000 < (c7_lower_num : ℝ) / (c7_lower_den : ℝ) :=
  c7_lower_gt_bpz_v1

-- Strictly exceeds previous d = 225 Γ₆^⊠4 pullback (`3258821451811711 / 10^15`)
example : 3258821451811711 * c7_lower_den < c7_lower_num * 1000000000000000 := by decide

-- Exact GMP floor check (`PROJECT.md § 4.4` minimum floor: `3258805369885 / 10^12`)
example : 3258805369885 * c7_lower_den ≤ c7_lower_num * 1000000000000 := by decide

-- Exact GMP ceiling check (`< 3317667207395 / 10^12`)
example : c7_lower_num * 1000000000000 < 3317667207395 * c7_lower_den := by decide

-- Exact Lovász cubic sign check: `p(num/den) = (num/den)^3 + 7(num/den)^2 - 49(num/den) + 49 < 0`
example :
    c7_lower_num ^ 3 + 7 * c7_lower_num ^ 2 * c7_lower_den + 49 * c7_lower_den ^ 3 <
      49 * c7_lower_num * c7_lower_den ^ 2 := by decide

-- Exact last-digit tightness check (`(num + 1)^220 > den^220 * frontierCard`)
set_option exponentiation.threshold 4096 in
example : c7_lower_den ^ 220 * frontierCard < (c7_lower_num + 1) ^ 220 := by decide

end ContractChecks

/-! ## 2. Live Functional Tests of `PartGadget` Operators & `Γ₆^⊠4` Pullback -/

section FunctionalTests

/-- Live check of `PartGadget.prodXupg1` on `frontierNode7` (`k = 9`) and `frontierNode8` (`k = 13`):
strictly lifts `c` above `367^22`! -/
example : frontierProf9.c > 367 ^ 22 := by decide

/-- Live check of `PartGadget.prodXupg2` profile equality on `basePart5D` (`d = 10`). -/
theorem test_prodXupg2_live_d10 :
    (basePart5D.prodXupg2 basePart5D).asymProfile =
      frontierBaseProfile.prodXupg2 frontierBaseProfile := by
  rw [PartGadget.prodXupg2_asymProfile, basePart5D_asymProfile_eq]

/-- Live check of `PartGadget.flip` profile equality on `basePart5D`. -/
theorem test_flip_live_d5 :
    basePart5D.flip.asymProfile = frontierBaseProfile.flip := by
  rw [PartGadget.flip_asymProfile, basePart5D_asymProfile_eq]

/-- Live instantiation of `gamma6Pow4_card_le_cycleGraph7_indepNum` on `PartGadget` (`d = 20`)
with a verified 5-tuple independent set in `Γ₆^⊠4`. -/
def testGamma6Terms : List Gamma6Quad :=
  [(0, 0, 0, 0), (0, 0, 1, 4), (0, 0, 2, 5), (0, 0, 4, 2), (0, 0, 5, 1)]

theorem testGamma6Terms_indep : gamma6QuadListIndepBool testGamma6Terms = true := rfl

theorem test_gamma6Pow4_live_d20 :
    gamma6QuadListWeight frontierBaseProfile frontierBaseProfile
      frontierBaseProfile frontierBaseProfile testGamma6Terms ≤
      (strongPowPi (SimpleGraph.cycleGraph 7) 20).indepNum := by
  have h := gamma6Pow4_card_le_cycleGraph7_indepNum
    basePart5D basePart5D basePart5D basePart5D
    testGamma6Terms testGamma6Terms_indep
  rw [basePart5D_asymProfile_eq] at h
  exact h

end FunctionalTests

/-! ## 3. Comprehensive `#print axioms` Gate -/

#print axioms ShannonC7.PartGadget.ofHeteroGadget
#print axioms ShannonC7.PartGadget.ofHeteroGadget_asymProfile
#print axioms ShannonC7.PartGadget.flip
#print axioms ShannonC7.PartGadget.flip_asymProfile
#print axioms ShannonC7.PartGadget.mapIso
#print axioms ShannonC7.PartGadget.mapIso_asymProfile
#print axioms ShannonC7.PartGadget.prodAlignedCore
#print axioms ShannonC7.PartGadget.prodStd
#print axioms ShannonC7.PartGadget.prodStd_asymProfile
#print axioms ShannonC7.PartGadget.prodXupg1
#print axioms ShannonC7.PartGadget.prodXupg1_asymProfile
#print axioms ShannonC7.PartGadget.prodXupg2
#print axioms ShannonC7.PartGadget.prodXupg2_asymProfile
#print axioms ShannonC7.PartGadget.gamma6Block_card
#print axioms ShannonC7.PartGadget.gamma6Block_isIndepSet
#print axioms ShannonC7.PartGadget.gamma6Block_not_close
#print axioms ShannonC7.gamma6Pow4_weight_le_indepNum
#print axioms ShannonC7.gamma6Pow4_card_le_cycleGraph7_indepNum
#print axioms ShannonC7.basePart5D_asymProfile_eq
#print axioms ShannonC7.frontierTarget_a_eq
#print axioms ShannonC7.frontierCard_le_indepNum
#print axioms ShannonC7.c7_lower_num
#print axioms ShannonC7.c7_lower_den
#print axioms ShannonC7.c7_lower_den_pos
#print axioms ShannonC7.frontier_pow_le
#print axioms ShannonC7.c7_lower_frontier
#print axioms ShannonC7.c7_lower_gt_bpz_v1
#print axioms ShannonC7.Tests.test_prodXupg2_live_d10
#print axioms ShannonC7.Tests.test_flip_live_d5
#print axioms ShannonC7.Tests.test_gamma6Pow4_live_d20

end ShannonC7.Tests
