import ShannonC7.Defs
import ShannonC7.LovaszC7
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Cubic Minimal Polynomial, Rational Enclosure, and Galois Unattainability for `ϑ(C₇)`

This module proves that `cos (π / 7)` satisfies `8 c³ - 4 c² - 4 c + 1 = 0`, deduces the cubic
minimal polynomial `t³ + 7 t² - 49 t + 49 = 0` for `lovaszThetaC7`, derives arbitrary-precision
zero-`π` rational upper bounds (specifically `< 3317667207395 / 10¹²`), and proves the Galois
unattainability dichotomy: for every `d > 0`, `α(C₇^⊠d)^(1/d) < lovaszThetaC7` strictly.
-/

namespace ShannonC7

open Polynomial

/-! ## Cubic Minimal Polynomial of `cos (π / 7)` and `lovaszThetaC7` -/

private lemma cos_cubic_of_cos_three_add_four {x : ℝ}
    (hsum : Real.cos (3 * x) + Real.cos (4 * x) = 0)
    (hne : Real.cos x + 1 ≠ 0) :
    8 * (Real.cos x) ^ 3 - 4 * (Real.cos x) ^ 2 - 4 * Real.cos x + 1 = 0 := by
  have h3 : Real.cos (3 * x) = 4 * (Real.cos x) ^ 3 - 3 * Real.cos x :=
    Real.cos_three_mul x
  have h4 : Real.cos (4 * x) = 2 * (2 * (Real.cos x) ^ 2 - 1) ^ 2 - 1 := by
    rw [show (4 : ℝ) * x = 2 * (2 * x) by ring, Real.cos_two_mul, Real.cos_two_mul]
  have hfac :
      (Real.cos x + 1) * (8 * (Real.cos x) ^ 3 - 4 * (Real.cos x) ^ 2 - 4 * Real.cos x + 1) = 0 := by
    linear_combination hsum - h3 - h4
  exact (mul_eq_zero.mp hfac).resolve_left hne

private lemma lovasz_cubic_of_cos_cubic {c : ℝ}
    (hc : 8 * c ^ 3 - 4 * c ^ 2 - 4 * c + 1 = 0) (hc1 : 1 + c ≠ 0) :
    ((7 * c) / (1 + c)) ^ 3 + 7 * ((7 * c) / (1 + c)) ^ 2 -
      49 * ((7 * c) / (1 + c)) + 49 = 0 := by
  field_simp [hc1]
  linear_combination 49 * hc

private lemma cos_pi_div_seven_gt_three_fourths :
    (3 : ℝ) / 4 < Real.cos (Real.pi / 7) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h6_pos : 0 < Real.cos (Real.pi / 6) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have h6 : (3 : ℝ) / 4 < Real.cos (Real.pi / 6) := by
    nlinarith [Real.sq_cos_pi_div_six, h6_pos]
  have hlt : Real.cos (Real.pi / 6) < Real.cos (Real.pi / 7) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  exact h6.trans hlt

/-- Minimal cubic polynomial identity for `cos (π / 7)`. -/
theorem cos_pi_div_seven_cubic :
    8 * (Real.cos (Real.pi / 7)) ^ 3 - 4 * (Real.cos (Real.pi / 7)) ^ 2 -
      4 * Real.cos (Real.pi / 7) + 1 = 0 := by
  have hsum : Real.cos (3 * (Real.pi / 7)) + Real.cos (4 * (Real.pi / 7)) = 0 := by
    have h4 : 4 * (Real.pi / 7) = Real.pi - 3 * (Real.pi / 7) := by ring
    rw [h4, Real.cos_pi_sub, add_neg_cancel]
  have hne : Real.cos (Real.pi / 7) + 1 ≠ 0 := by
    linarith [cos_pi_div_seven_gt_three_fourths]
  exact cos_cubic_of_cos_three_add_four hsum hne

/-- Minimal cubic polynomial identity for `lovaszThetaC7`: `t³ + 7 t² - 49 t + 49 = 0`. -/
theorem lovaszThetaC7_cubic :
    lovaszThetaC7 ^ 3 + 7 * lovaszThetaC7 ^ 2 - 49 * lovaszThetaC7 + 49 = 0 := by
  have hc1 : 1 + Real.cos (Real.pi / 7) ≠ 0 := by
    linarith [cos_pi_div_seven_gt_three_fourths]
  exact lovasz_cubic_of_cos_cubic cos_pi_div_seven_cubic hc1

/-- `lovaszThetaC7` is strictly greater than `3`. -/
theorem lovaszThetaC7_gt_three : 3 < lovaszThetaC7 := by
  have hc : (3 : ℝ) / 4 < Real.cos (Real.pi / 7) := cos_pi_div_seven_gt_three_fourths
  have hden : 0 < 1 + Real.cos (Real.pi / 7) := by linarith
  rw [lovaszThetaC7, lt_div_iff₀ hden]
  linarith

/-! ## Zero-`π` Rational Upper Bounds -/

/-- Any `q ≥ 3` at which the minimal cubic `q³ + 7 q² - 49 q + 49` is strictly positive
strictly upper-bounds `lovaszThetaC7`. -/
theorem lovaszThetaC7_lt_of_cubic_pos {q : ℝ} (hq : 3 ≤ q)
    (hp : 0 < q ^ 3 + 7 * q ^ 2 - 49 * q + 49) : lovaszThetaC7 < q := by
  have hfac :
      (q - lovaszThetaC7) *
        (q ^ 2 + q * lovaszThetaC7 + lovaszThetaC7 ^ 2 + 7 * (q + lovaszThetaC7) - 49) =
        q ^ 3 + 7 * q ^ 2 - 49 * q + 49 := by
    linear_combination -lovaszThetaC7_cubic
  have hpos :
      0 < q ^ 2 + q * lovaszThetaC7 + lovaszThetaC7 ^ 2 + 7 * (q + lovaszThetaC7) - 49 := by
    nlinarith [lovaszThetaC7_gt_three]
  nlinarith [hfac, hpos]

/-- 12-decimal rational upper bound on `lovaszThetaC7`. -/
theorem lovaszThetaC7_lt_rational :
    lovaszThetaC7 < (3317667207395 : ℝ) / 1000000000000 :=
  lovaszThetaC7_lt_of_cubic_pos (by norm_num) (by norm_num)

/-- Zero-`π` 12-decimal rational upper bound on `Θ(C₇)`. -/
theorem c7_upper_rational :
    shannonCapacity (SimpleGraph.cycleGraph 7) < (3317667207395 : ℝ) / 1000000000000 :=
  lt_of_le_of_lt c7_upper_lovasz lovaszThetaC7_lt_rational

/-! ## Irreducibility & Galois Unattainability -/

private noncomputable def cubicPoly : ℚ[X] :=
  X ^ 3 + C 7 * X ^ 2 - C 49 * X + C 49

private lemma cubicPoly_natDegree : cubicPoly.natDegree = 3 := by
  unfold cubicPoly
  compute_degree!

private lemma cubicPoly_not_isRoot (r : ℚ) : ¬ cubicPoly.IsRoot r := by
  intro hr
  have heval : r ^ 3 + 7 * r ^ 2 - 49 * r + 49 = 0 := by
    simpa [cubicPoly, Polynomial.IsRoot] using hr
  have hden_ne : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  have hr_eq : r = (r.num : ℚ) / (r.den : ℚ) := r.num_div_den.symm
  rw [hr_eq] at heval
  field_simp [hden_ne] at heval
  have hq :
      (r.num : ℚ) ^ 3 + 7 * (r.num : ℚ) ^ 2 * (r.den : ℚ) -
        49 * (r.num : ℚ) * (r.den : ℚ) ^ 2 + 49 * (r.den : ℚ) ^ 3 = 0 := by
    linear_combination heval
  have hz :
      r.num ^ 3 + 7 * r.num ^ 2 * (r.den : ℤ) -
        49 * r.num * (r.den : ℤ) ^ 2 + 49 * (r.den : ℤ) ^ 3 = 0 := by
    exact_mod_cast hq
  have hmod :
      (r.num : ZMod 3) ^ 3 + 7 * (r.num : ZMod 3) ^ 2 * (r.den : ZMod 3) -
        49 * (r.num : ZMod 3) * (r.den : ZMod 3) ^ 2 + 49 * (r.den : ZMod 3) ^ 3 = 0 := by
    have h := congrArg (Int.cast : ℤ → ZMod 3) hz
    push_cast at h
    exact h
  have hzero : ∀ x y : ZMod 3,
      x ^ 3 + 7 * x ^ 2 * y - 49 * x * y ^ 2 + 49 * y ^ 3 = 0 → x = 0 ∧ y = 0 := by
    decide
  obtain ⟨hnum0, hden0⟩ := hzero (r.num : ZMod 3) (r.den : ZMod 3) hmod
  have h3_num : 3 ∣ r.num.natAbs :=
    Int.ofNat_dvd_left.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd r.num 3).mp hnum0)
  have h3_den : 3 ∣ r.den := (ZMod.natCast_eq_zero_iff r.den 3).mp hden0
  have h3_gcd : 3 ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd h3_num h3_den
  rw [r.reduced] at h3_gcd
  omega

private lemma cubicPoly_irreducible : Irreducible cubicPoly :=
  Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [cubicPoly_natDegree]; decide) cubicPoly_not_isRoot

private lemma eval₂_cubicPoly (x : ℝ) :
    cubicPoly.eval₂ (Rat.castHom ℝ) x = x ^ 3 + 7 * x ^ 2 - 49 * x + 49 := by
  simp [cubicPoly, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]

private noncomputable def lovaszThetaC7_conj : ℝ :=
  (7 * Real.cos (3 * Real.pi / 7)) / (1 + Real.cos (3 * Real.pi / 7))

private lemma lovaszThetaC7_conj_bounds :
    0 < lovaszThetaC7_conj ∧ lovaszThetaC7_conj < lovaszThetaC7 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc_pos : 0 < Real.cos (3 * Real.pi / 7) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc_lt : Real.cos (3 * Real.pi / 7) < 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have hden : 0 < 1 + Real.cos (3 * Real.pi / 7) := by linarith
  have hpos : 0 < lovaszThetaC7_conj := div_pos (by linarith) hden
  have hlt3 : lovaszThetaC7_conj < 3 := by
    rw [lovaszThetaC7_conj, div_lt_iff₀ hden]
    linarith
  exact ⟨hpos, hlt3.trans lovaszThetaC7_gt_three⟩

private lemma lovaszThetaC7_conj_cubic :
    lovaszThetaC7_conj ^ 3 + 7 * lovaszThetaC7_conj ^ 2 -
      49 * lovaszThetaC7_conj + 49 = 0 := by
  have hsum : Real.cos (3 * (3 * Real.pi / 7)) + Real.cos (4 * (3 * Real.pi / 7)) = 0 := by
    have h4 : 4 * (3 * Real.pi / 7) = (Real.pi - 3 * (3 * Real.pi / 7)) + 2 * Real.pi := by ring
    rw [h4, Real.cos_add_two_pi, Real.cos_pi_sub, add_neg_cancel]
  have hpos : 0 < Real.cos (3 * Real.pi / 7) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hc := cos_cubic_of_cos_three_add_four hsum (by linarith)
  exact lovasz_cubic_of_cos_cubic hc (by linarith)

/-- No positive integer power of `lovaszThetaC7` is rational (via distinct-modulus Galois conjugates). -/
theorem lovaszThetaC7_pow_ne_rat (d : ℕ) (hd : 0 < d) (r : ℚ) :
    lovaszThetaC7 ^ d ≠ (r : ℝ) := by
  intro heq
  let Q : ℚ[X] := X ^ d - C r
  have hP : cubicPoly.eval₂ (Rat.castHom ℝ) lovaszThetaC7 = 0 := by
    rw [eval₂_cubicPoly, lovaszThetaC7_cubic]
  have hQ : Q.eval₂ (Rat.castHom ℝ) lovaszThetaC7 = 0 := by
    simp [Q, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, heq]
  have hgcd0 :
      (EuclideanDomain.gcd cubicPoly Q).eval₂ (Rat.castHom ℝ) lovaszThetaC7 = 0 :=
    Polynomial.eval₂_gcd_eq_zero hP hQ
  obtain ⟨h, hPh⟩ := EuclideanDomain.gcd_dvd_left cubicPoly Q
  have hdvd : cubicPoly ∣ Q := by
    rcases cubicPoly_irreducible.isUnit_or_isUnit hPh with hgU | hhU
    · obtain ⟨u, hu⟩ := hgU.exists_right_inv
      have h1 := congrArg (Polynomial.eval₂ (Rat.castHom ℝ) lovaszThetaC7) hu
      rw [Polynomial.eval₂_mul, hgcd0, zero_mul, Polynomial.eval₂_one] at h1
      exact absurd h1 zero_ne_one
    · obtain ⟨u, hu⟩ := hhU.exists_right_inv
      have hPg : cubicPoly ∣ EuclideanDomain.gcd cubicPoly Q :=
        ⟨u, by
          calc EuclideanDomain.gcd cubicPoly Q
              = EuclideanDomain.gcd cubicPoly Q * 1 := (mul_one _).symm
            _ = EuclideanDomain.gcd cubicPoly Q * (h * u) := by rw [hu]
            _ = (EuclideanDomain.gcd cubicPoly Q * h) * u := (mul_assoc _ _ _).symm
            _ = cubicPoly * u := by rw [← hPh]⟩
      exact hPg.trans (EuclideanDomain.gcd_dvd_right cubicPoly Q)
  obtain ⟨k, hQk⟩ := hdvd
  have hQconj : Q.eval₂ (Rat.castHom ℝ) lovaszThetaC7_conj = 0 := by
    rw [hQk, Polynomial.eval₂_mul, eval₂_cubicPoly, lovaszThetaC7_conj_cubic, zero_mul]
  have hconj_pow : lovaszThetaC7_conj ^ d = (r : ℝ) := by
    have : lovaszThetaC7_conj ^ d - (r : ℝ) = 0 := by
      simpa [Q, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C] using hQconj
    linarith
  have hlt : lovaszThetaC7_conj ^ d < lovaszThetaC7 ^ d :=
    pow_lt_pow_left₀ lovaszThetaC7_conj_bounds.2 lovaszThetaC7_conj_bounds.1.le hd.ne'
  linarith

/-- Galois unattainability theorem: no finite strong power of `C₇` can attain `lovaszThetaC7`. -/
theorem c7_lovasz_unattainable (d : ℕ) (hd : 0 < d) :
    ((strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ^ (1 / (d : ℝ)) < lovaszThetaC7 := by
  have hle :
      ((strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ^ (1 / (d : ℝ)) ≤
        lovaszThetaC7 := by
    have hmem :
        ((strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ^ (1 / (d : ℝ)) ∈
          shannonSet (SimpleGraph.cycleGraph 7) := by
      rw [shannonSet_eq_pi]
      exact ⟨d, hd, rfl⟩
    exact (le_csSup (shannonSet_bddAbove (SimpleGraph.cycleGraph 7)) hmem).trans c7_upper_lovasz
  refine lt_of_le_of_ne hle fun heq => ?_
  have hpow :
      lovaszThetaC7 ^ d =
        (((strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℚ) : ℝ) := by
    rw [← heq, ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg _), one_div_mul_cancel (Nat.cast_ne_zero.mpr hd.ne'),
      Real.rpow_one, Rat.cast_natCast]
  exact lovaszThetaC7_pow_ne_rat d hd _ hpow

end ShannonC7
