import ShannonC7.Lovasz
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Lovász Upper Bounds for Odd Cycles `C_{2k+1}`, `C₇`, and `C₇ᶜ` (`ShannonC7/LovaszC7.lean`)

This module proves discrete Fourier orthogonality on `Fin n`, constructs explicit Fourier
sum-of-squares Lovász certificates for all odd cycles `SimpleGraph.cycleGraph (2 * k + 1)`,
specializes to `c7_upper_lovasz : shannonCapacity (SimpleGraph.cycleGraph 7) ≤ lovaszThetaC7`,
and constructs explicit rank-2 cosine Lovász certificates for odd-cycle complements,
yielding `c7_compl_upper_lovasz : shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ≤ 1 + (cos (π / 7))⁻¹`.
-/

namespace ShannonC7

/-- The Lovász theta number of the 7-cycle: `ϑ(C₇) = 7 cos(π/7) / (1 + cos(π/7))`. -/
noncomputable def lovaszThetaC7 : ℝ :=
  (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7))

/-! ## Elementary Modular Arithmetic Bridge on `Fin n` -/

private lemma fin_eq_iff_dvd {n : ℕ} (hn : 1 ≤ n) (i j : Fin n) :
    i = j ↔ (n : ℤ) ∣ ((i.val : ℤ) - (j.val : ℤ)) := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨q, hq⟩
    have hi : (i.val : ℤ) < (n : ℤ) := Nat.cast_lt.mpr i.isLt
    have hj : (j.val : ℤ) < (n : ℤ) := Nat.cast_lt.mpr j.isLt
    have hi0 : (0 : ℤ) ≤ i.val := Nat.cast_nonneg _
    have hj0 : (0 : ℤ) ≤ j.val := Nat.cast_nonneg _
    have hn1 : (1 : ℤ) ≤ n := Nat.cast_le.mpr hn
    have hq_lt : q < 1 := by nlinarith
    have hq_gt : -1 < q := by nlinarith
    have hq0 : q = 0 := by omega
    rw [hq0, mul_zero] at hq
    exact Fin.ext (by omega)

private lemma fin_sub_val_eq_one_iff_dvd {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    (i - j).val = 1 ↔ (n : ℤ) ∣ ((i.val : ℤ) - (j.val : ℤ) - 1) := by
  have hi : (i.val : ℤ) < (n : ℤ) := Nat.cast_lt.mpr i.isLt
  have hj : (j.val : ℤ) < (n : ℤ) := Nat.cast_lt.mpr j.isLt
  have hi0 : (0 : ℤ) ≤ i.val := Nat.cast_nonneg _
  have hj0 : (0 : ℤ) ≤ j.val := Nat.cast_nonneg _
  have hn2 : (2 : ℤ) ≤ n := Nat.cast_le.mpr hn
  by_cases hle : j ≤ i
  · have hsub : (i - j).val = i.val - j.val := Fin.coe_sub_iff_le.mpr hle
    have hle_val : j.val ≤ i.val := hle
    constructor
    · intro h
      refine ⟨0, ?_⟩
      omega
    · rintro ⟨q, hq⟩
      have hq_lt : q < 1 := by nlinarith
      have hq_gt : -1 < q := by nlinarith
      have hq0 : q = 0 := by omega
      rw [hq0, mul_zero] at hq
      omega
  · have hlt : i < j := lt_of_not_ge hle
    have hsub : (i - j).val = n + i.val - j.val := Fin.coe_sub_iff_lt.mpr hlt
    have hlt_val : i.val < j.val := hlt
    constructor
    · intro h
      refine ⟨-1, ?_⟩
      omega
    · rintro ⟨q, hq⟩
      have hq_lt : q < 0 := by nlinarith
      have hq_gt : -2 < q := by nlinarith
      have hq1 : q = -1 := by omega
      rw [hq1] at hq
      omega

private lemma fin_sub_val_eq_one_iff_dvd_add {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    (j - i).val = 1 ↔ (n : ℤ) ∣ ((i.val : ℤ) - (j.val : ℤ) + 1) := by
  rw [fin_sub_val_eq_one_iff_dvd hn j i, ← dvd_neg]
  have hneg : -((j.val : ℤ) - (i.val : ℤ) - 1) = (i.val : ℤ) - (j.val : ℤ) + 1 := by ring
  rw [hneg]

private lemma not_dvd_sub_one_of_dvd {n : ℕ} (hn : 3 ≤ n) {d : ℤ} (h : (n : ℤ) ∣ d) :
    ¬ ((n : ℤ) ∣ (d - 1)) := by
  intro h1
  have hdiff : (n : ℤ) ∣ (d - (d - 1)) := dvd_sub h h1
  have hdiv1 : (n : ℤ) ∣ (1 : ℤ) := by simpa using hdiff
  have hle : (n : ℤ) ≤ 1 := Int.le_of_dvd zero_lt_one hdiv1
  omega

private lemma not_dvd_add_one_of_dvd {n : ℕ} (hn : 3 ≤ n) {d : ℤ} (h : (n : ℤ) ∣ d) :
    ¬ ((n : ℤ) ∣ (d + 1)) := by
  intro h1
  have hdiff : (n : ℤ) ∣ ((d + 1) - d) := dvd_sub h1 h
  have hdiv1 : (n : ℤ) ∣ (1 : ℤ) := by simpa using hdiff
  have hle : (n : ℤ) ≤ 1 := Int.le_of_dvd zero_lt_one hdiv1
  omega

private lemma not_dvd_add_one_of_dvd_sub_one {n : ℕ} (hn : 3 ≤ n) {d : ℤ}
    (h : (n : ℤ) ∣ (d - 1)) : ¬ ((n : ℤ) ∣ (d + 1)) := by
  intro h1
  have hdiff : (n : ℤ) ∣ ((d + 1) - (d - 1)) := dvd_sub h1 h
  have hdiv2 : (n : ℤ) ∣ (2 : ℤ) := by
    have heq : (d + 1) - (d - 1) = 2 := by ring
    rwa [heq] at hdiff
  have hle : (n : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdiv2
  omega

/-! ## General Discrete Fourier Orthogonality -/

private lemma sum_cos_two_pi_mul_div (n : ℕ) (hn : 0 < n) (r : ℤ) :
    ∑ m ∈ Finset.range n, Real.cos (2 * Real.pi * (m : ℝ) * (r : ℝ) / (n : ℝ)) =
      if (n : ℤ) ∣ r then (n : ℝ) else 0 := by
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  split_ifs with h
  · rcases h with ⟨q, rfl⟩
    have hterm : ∀ m ∈ Finset.range n,
        Real.cos (2 * Real.pi * (m : ℝ) * (((n : ℤ) * q : ℤ) : ℝ) / (n : ℝ)) = 1 := by
      intro m _
      have harg :
          2 * Real.pi * (m : ℝ) * (((n : ℤ) * q : ℤ) : ℝ) / (n : ℝ) =
            (((m : ℤ) * q : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast
        field_simp [hn_ne]
      rw [harg, Real.cos_int_mul_two_pi]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · have hsin : Real.sin (Real.pi * (r : ℝ) / (n : ℝ)) ≠ 0 := by
      rw [Real.sin_ne_zero_iff]
      intro q hq
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      have h1 : (q : ℝ) * Real.pi * (n : ℝ) = Real.pi * (r : ℝ) := by
        calc (q : ℝ) * Real.pi * (n : ℝ)
            = (Real.pi * (r : ℝ) / (n : ℝ)) * (n : ℝ) := by rw [hq]
          _ = Real.pi * (r : ℝ) := div_mul_cancel₀ _ hn_ne
      have h2 : Real.pi * ((q : ℝ) * (n : ℝ)) = Real.pi * (r : ℝ) := by linarith
      have hqn : (q : ℝ) * (n : ℝ) = (r : ℝ) := mul_left_cancel₀ hpi h2
      have hqz : q * (n : ℤ) = r := by exact_mod_cast hqn
      exact h ⟨q, by linarith⟩
    let f : ℕ → ℝ := fun m => Real.sin ((2 * (m : ℝ) - 1) * Real.pi * (r : ℝ) / (n : ℝ))
    have hterm : ∀ m : ℕ,
        2 * Real.sin (Real.pi * (r : ℝ) / (n : ℝ)) *
          Real.cos (2 * Real.pi * (m : ℝ) * (r : ℝ) / (n : ℝ)) = f (m + 1) - f m := by
      intro m
      rw [Real.two_mul_sin_mul_cos]
      have h1 :
          Real.pi * (r : ℝ) / (n : ℝ) + 2 * Real.pi * (m : ℝ) * (r : ℝ) / (n : ℝ) =
            (2 * ((m + 1 : ℕ) : ℝ) - 1) * Real.pi * (r : ℝ) / (n : ℝ) := by
        push_cast
        ring
      have h2 :
          Real.pi * (r : ℝ) / (n : ℝ) - 2 * Real.pi * (m : ℝ) * (r : ℝ) / (n : ℝ) =
            -((2 * (m : ℝ) - 1) * Real.pi * (r : ℝ) / (n : ℝ)) := by
        ring
      rw [h1, h2, Real.sin_neg]
      simp only [f]
      ring
    have hmul :
        (2 * Real.sin (Real.pi * (r : ℝ) / (n : ℝ))) *
          ∑ m ∈ Finset.range n, Real.cos (2 * Real.pi * (m : ℝ) * (r : ℝ) / (n : ℝ)) = 0 := by
      rw [Finset.mul_sum]
      calc ∑ m ∈ Finset.range n,
              2 * Real.sin (Real.pi * (r : ℝ) / (n : ℝ)) *
                Real.cos (2 * Real.pi * (m : ℝ) * (r : ℝ) / (n : ℝ))
          = ∑ m ∈ Finset.range n, (f (m + 1) - f m) :=
              Finset.sum_congr rfl fun m _ => hterm m
        _ = f n - f 0 := Finset.sum_range_sub f n
        _ = 0 := by
              have hfn : f n = f 0 := by
                simp only [f]
                have harg :
                    (2 * (n : ℝ) - 1) * Real.pi * (r : ℝ) / (n : ℝ) =
                      (2 * ((0 : ℕ) : ℝ) - 1) * Real.pi * (r : ℝ) / (n : ℝ) +
                        (r : ℝ) * (2 * Real.pi) := by
                  push_cast
                  field_simp [hn_ne]
                  ring
                rw [harg, Real.sin_add_int_mul_two_pi]
              rw [hfn, sub_self]
    have h2sin : 2 * Real.sin (Real.pi * (r : ℝ) / (n : ℝ)) ≠ 0 :=
      mul_ne_zero two_ne_zero hsin
    exact (mul_eq_zero.mp hmul).resolve_left h2sin

/-! ## Odd-Cycle Fourier Sum-of-Squares Lovász Certificate -/

private lemma cos_pi_div_odd_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < Real.cos (Real.pi / ((2 * k + 1 : ℕ) : ℝ)) := by
  have hn3 : (3 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
    have : 3 ≤ 2 * k + 1 := by omega
    exact_mod_cast this
  have hn_pos : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have : 0 < Real.pi / ((2 * k + 1 : ℕ) : ℝ) := div_pos hpi hn_pos
    linarith
  · rw [div_lt_div_iff₀ hn_pos two_pos]
    nlinarith

/-- Explicit Fourier sum-of-squares Lovász certificate for the odd cycle `C_{2k+1}` (`k ≥ 1`). -/
noncomputable def oddCycleLovaszCert (k : ℕ) (hk : 1 ≤ k) :
    LovaszCert (SimpleGraph.cycleGraph (2 * k + 1))
      ((1 + Real.cos (Real.pi / (2 * k + 1 : ℝ))) /
        ((2 * k + 1 : ℝ) * Real.cos (Real.pi / (2 * k + 1 : ℝ)))) := by
  let n : ℕ := 2 * k + 1
  have hn3 : 3 ≤ n := by omega
  have hn_pos_nat : 0 < n := by omega
  have hn_cast : (n : ℝ) = (2 * k + 1 : ℝ) := by
    simp only [n]
    push_cast
    ring
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos_nat
  let c : ℝ := Real.cos (Real.pi / (n : ℝ))
  have hc_pos : 0 < c := cos_pi_div_odd_pos k hk
  let β : ℝ := (1 + c) / ((n : ℝ) * c)
  have hβ_eq :
      β = (1 + Real.cos (Real.pi / (2 * k + 1 : ℝ))) /
        ((2 * k + 1 : ℝ) * Real.cos (Real.pi / (2 * k + 1 : ℝ))) := by
    simp only [β, c, hn_cast]
  refine LovaszCert.withBeta (β₁ := β) ?_ hβ_eq
  refine
    { W := Matrix.of fun i j : Fin n =>
        if i = j then (1 : ℝ)
        else if (SimpleGraph.cycleGraph n).Adj i j then (2 * c)⁻¹
        else 0
      hβ := div_pos (by linarith) (mul_pos hn_pos hc_pos)
      symm := Matrix.IsSymm.ext fun i j => by
        simp only [Matrix.of_apply]
        by_cases hij : i = j
        · subst hij
          simp
        · have hji : j ≠ i := Ne.symm hij
          simp only [hij, hji, ↓reduceIte, SimpleGraph.adj_comm]
      diag_le_one := fun i => by
        simp
      nonadj_zero := fun i j hij hadj => by
        change ¬ (SimpleGraph.cycleGraph n).Adj i j at hadj
        simp [hij, hadj]
      psd := ?_ }
  let lam : ℕ → ℝ := fun m =>
    if m = 0 then 0 else (1 + Real.cos (2 * Real.pi * (m : ℝ) / (n : ℝ)) / c) / (n : ℝ)
  have hle_k : ∀ m' : ℕ, 1 ≤ m' → m' ≤ k →
      -c ≤ Real.cos (2 * Real.pi * (m' : ℝ) / (n : ℝ)) := by
    intro m' _ hm'k
    have hpi : 0 < Real.pi := Real.pi_pos
    have hm'_le : 2 * (m' : ℝ) ≤ (n : ℝ) - 1 := by
      have h1 : 2 * m' ≤ 2 * k := by omega
      have h2 : (2 * m' : ℝ) ≤ (2 * k : ℝ) := by exact_mod_cast h1
      have h3 : (n : ℝ) = 2 * (k : ℝ) + 1 := by simp only [n]; push_cast; ring
      linarith
    have hangle_le :
        2 * Real.pi * (m' : ℝ) / (n : ℝ) ≤ Real.pi - Real.pi / (n : ℝ) := by
      have hsub : Real.pi - Real.pi / (n : ℝ) = Real.pi * ((n : ℝ) - 1) / (n : ℝ) := by
        field_simp [hn_pos.ne']
      rw [hsub]
      exact div_le_div_of_nonneg_right (by nlinarith) hn_pos.le
    have hpi_sub_le : Real.pi - Real.pi / (n : ℝ) ≤ Real.pi := by
      have : 0 ≤ Real.pi / (n : ℝ) := div_nonneg hpi.le hn_pos.le
      linarith
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hpi_sub_le hangle_le
    rwa [Real.cos_pi_sub] at hcos
  have hlam_nonneg : ∀ m ∈ Finset.range n, 0 ≤ lam m := by
    intro m hm
    by_cases hm0 : m = 0
    · simp [lam, hm0]
    · simp only [lam, hm0, ↓reduceIte]
      have hm_lt : m < n := Finset.mem_range.mp hm
      have hcos_ge : -c ≤ Real.cos (2 * Real.pi * (m : ℝ) / (n : ℝ)) := by
        by_cases hmk : m ≤ k
        · exact hle_k m (Nat.pos_of_ne_zero hm0) hmk
        · let m' : ℕ := n - m
          have hm'1 : 1 ≤ m' := by omega
          have hm'k : m' ≤ k := by omega
          have harg :
              2 * Real.pi * (m : ℝ) / (n : ℝ) =
                2 * Real.pi - 2 * Real.pi * (m' : ℝ) / (n : ℝ) := by
            have hcast : (m' : ℝ) = (n : ℝ) - (m : ℝ) := by
              simp only [m']
              exact Nat.cast_sub hm_lt.le
            rw [hcast]
            field_simp [hn_pos.ne']
            ring
          rw [harg, Real.cos_two_pi_sub]
          exact hle_k m' hm'1 hm'k
      have hnum : 0 ≤ 1 + Real.cos (2 * Real.pi * (m : ℝ) / (n : ℝ)) / c := by
        have hdiv : -1 ≤ Real.cos (2 * Real.pi * (m : ℝ) / (n : ℝ)) / c := by
          rw [le_div_iff₀ hc_pos]
          linarith
        linarith
      exact div_nonneg hnum hn_pos.le
  have hdecomp :
      Matrix.of (fun i j : Fin n =>
          if i = j then (1 : ℝ)
          else if (SimpleGraph.cycleGraph n).Adj i j then (2 * c)⁻¹
          else 0) -
        β • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) =
        ∑ m ∈ Finset.range n,
          lam m •
            Matrix.of (fun i j : Fin n =>
              Real.cos (2 * Real.pi * (m : ℝ) * (i.val : ℝ) / (n : ℝ) -
                2 * Real.pi * (m : ℝ) * (j.val : ℝ) / (n : ℝ))) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.sum_apply,
      smul_eq_mul, mul_one]
    let d : ℤ := (i.val : ℤ) - (j.val : ℤ)
    have hd_cast : (d : ℝ) = (i.val : ℝ) - (j.val : ℝ) := by
      simp only [d]
      push_cast
      rfl
    let g : ℕ → ℝ := fun m =>
      (1 + Real.cos (2 * Real.pi * (m : ℝ) / (n : ℝ)) / c) / (n : ℝ) *
        Real.cos (2 * Real.pi * (m : ℝ) * (d : ℝ) / (n : ℝ))
    have hg0 : g 0 = β := by
      simp only [g, β, Nat.cast_zero, mul_zero, zero_mul, zero_div, Real.cos_zero, mul_one]
      field_simp [hn_pos.ne', hc_pos.ne']
      ring
    have hsum_lam :
        ∑ m ∈ Finset.range n,
          lam m *
            Real.cos (2 * Real.pi * (m : ℝ) * (i.val : ℝ) / (n : ℝ) -
              2 * Real.pi * (m : ℝ) * (j.val : ℝ) / (n : ℝ)) =
          (∑ m ∈ Finset.range n, g m) - β := by
      have hterm : ∀ m ∈ Finset.range n,
          lam m *
            Real.cos (2 * Real.pi * (m : ℝ) * (i.val : ℝ) / (n : ℝ) -
              2 * Real.pi * (m : ℝ) * (j.val : ℝ) / (n : ℝ)) =
            g m - (if m = 0 then g 0 else 0) := by
        intro m _
        have harg :
            2 * Real.pi * (m : ℝ) * (i.val : ℝ) / (n : ℝ) -
              2 * Real.pi * (m : ℝ) * (j.val : ℝ) / (n : ℝ) =
              2 * Real.pi * (m : ℝ) * (d : ℝ) / (n : ℝ) := by
          rw [hd_cast]
          ring
        rw [harg]
        by_cases hm0 : m = 0
        · subst hm0
          simp [lam]
        · simp [lam, g, hm0]
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_range.mpr hn_pos_nat), hg0]
    have hsum_g :
        ∑ m ∈ Finset.range n, g m =
          (n : ℝ)⁻¹ * (if (n : ℤ) ∣ d then (n : ℝ) else 0) +
            (2 * (n : ℝ) * c)⁻¹ *
              ((if (n : ℤ) ∣ (d - 1) then (n : ℝ) else 0) +
                (if (n : ℤ) ∣ (d + 1) then (n : ℝ) else 0)) := by
      have hg_split : ∀ m ∈ Finset.range n,
          g m =
            (n : ℝ)⁻¹ * Real.cos (2 * Real.pi * (m : ℝ) * (d : ℝ) / (n : ℝ)) +
              (2 * (n : ℝ) * c)⁻¹ *
                (Real.cos (2 * Real.pi * (m : ℝ) * ((d - 1 : ℤ) : ℝ) / (n : ℝ)) +
                  Real.cos (2 * Real.pi * (m : ℝ) * ((d + 1 : ℤ) : ℝ) / (n : ℝ))) := by
        intro m _
        have hprod := Real.two_mul_cos_mul_cos
          (2 * Real.pi * (m : ℝ) * (d : ℝ) / (n : ℝ))
          (2 * Real.pi * (m : ℝ) / (n : ℝ))
        have hsub :
            2 * Real.pi * (m : ℝ) * (d : ℝ) / (n : ℝ) - 2 * Real.pi * (m : ℝ) / (n : ℝ) =
              2 * Real.pi * (m : ℝ) * ((d - 1 : ℤ) : ℝ) / (n : ℝ) := by
          push_cast
          ring
        have hadd :
            2 * Real.pi * (m : ℝ) * (d : ℝ) / (n : ℝ) + 2 * Real.pi * (m : ℝ) / (n : ℝ) =
              2 * Real.pi * (m : ℝ) * ((d + 1 : ℤ) : ℝ) / (n : ℝ) := by
          push_cast
          ring
        rw [hsub, hadd] at hprod
        simp only [g]
        rw [← hprod]
        field_simp [hn_pos.ne', hc_pos.ne']
      rw [Finset.sum_congr rfl hg_split, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, Finset.sum_add_distrib,
        sum_cos_two_pi_mul_div n hn_pos_nat d,
        sum_cos_two_pi_mul_div n hn_pos_nat (d - 1),
        sum_cos_two_pi_mul_div n hn_pos_nat (d + 1)]
    rw [hsum_lam, hsum_g]
    by_cases hij : i = j
    · have hd0 : (n : ℤ) ∣ d := (fin_eq_iff_dvd (by omega) i j).mp hij
      have hdm : ¬ ((n : ℤ) ∣ (d - 1)) := not_dvd_sub_one_of_dvd hn3 hd0
      have hdp : ¬ ((n : ℤ) ∣ (d + 1)) := not_dvd_add_one_of_dvd hn3 hd0
      simp only [hij, ↓reduceIte, hd0, hdm, hdp, add_zero, mul_zero]
      rw [inv_mul_cancel₀ hn_pos.ne']
    · have hnd0 : ¬ ((n : ℤ) ∣ d) := (fin_eq_iff_dvd (by omega) i j).not.mp hij
      by_cases hadj : (SimpleGraph.cycleGraph n).Adj i j
      · simp only [hij, hadj, ↓reduceIte, hnd0, mul_zero, zero_add]
        rcases SimpleGraph.cycleGraph_adj'.mp hadj with h1 | h2
        · have hdm : (n : ℤ) ∣ (d - 1) := (fin_sub_val_eq_one_iff_dvd (by omega) i j).mp h1
          have hdp : ¬ ((n : ℤ) ∣ (d + 1)) := not_dvd_add_one_of_dvd_sub_one hn3 hdm
          simp only [hdm, hdp, ↓reduceIte, add_zero]
          field_simp [hn_pos.ne', hc_pos.ne']
        · have hdp : (n : ℤ) ∣ (d + 1) := (fin_sub_val_eq_one_iff_dvd_add (by omega) i j).mp h2
          have hdm : ¬ ((n : ℤ) ∣ (d - 1)) := fun hm =>
            not_dvd_add_one_of_dvd_sub_one hn3 hm hdp
          simp only [hdm, hdp, ↓reduceIte, zero_add]
          field_simp [hn_pos.ne', hc_pos.ne']
      · have h1 : (i - j).val ≠ 1 := fun h => hadj (SimpleGraph.cycleGraph_adj'.mpr (Or.inl h))
        have h2 : (j - i).val ≠ 1 := fun h => hadj (SimpleGraph.cycleGraph_adj'.mpr (Or.inr h))
        have hdm : ¬ ((n : ℤ) ∣ (d - 1)) :=
          (fin_sub_val_eq_one_iff_dvd (by omega) i j).not.mp h1
        have hdp : ¬ ((n : ℤ) ∣ (d + 1)) :=
          (fin_sub_val_eq_one_iff_dvd_add (by omega) i j).not.mp h2
        simp [hij, hadj, hnd0, hdm, hdp]
  rw [hdecomp]
  exact Matrix.posSemidef_sum (Finset.range n) fun m hm =>
    (posSemidef_cos_sub fun i : Fin n =>
      2 * Real.pi * (m : ℝ) * (i.val : ℝ) / (n : ℝ)).smul (hlam_nonneg m hm)

/-- Explicit Lovász certificate for the 7-cycle achieving `lovaszThetaC7`. -/
noncomputable def c7LovaszCert :
    LovaszCert (SimpleGraph.cycleGraph 7) lovaszThetaC7⁻¹ :=
  (oddCycleLovaszCert 3 (by norm_num)).withBeta (by
    unfold lovaszThetaC7
    rw [inv_div]
    norm_num)

/-- Lovász's odd-cycle upper bound:
`Θ(C_{2k+1}) ≤ (2k + 1) cos(π / (2k + 1)) / (1 + cos(π / (2k + 1)))` for all `k ≥ 1`. -/
theorem oddCycle_upper_lovasz (k : ℕ) (hk : 1 ≤ k) :
    shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1)) ≤
      ((2 * k + 1 : ℝ) * Real.cos (Real.pi / (2 * k + 1))) /
        (1 + Real.cos (Real.pi / (2 * k + 1))) := by
  have h := shannonCapacity_le_of_cert (oddCycleLovaszCert k hk)
  rwa [inv_div] at h

/-- Lovász's upper bound for the 7-cycle: `Θ(C₇) ≤ ϑ(C₇)`. -/
theorem c7_upper_lovasz :
    shannonCapacity (SimpleGraph.cycleGraph 7) ≤ lovaszThetaC7 := by
  have h := shannonCapacity_le_of_cert c7LovaszCert
  rwa [inv_inv] at h

/-! ## Complement Upper Bounds: `C_{2k+1}ᶜ` and `C₇ᶜ` -/

/-- Explicit rank-2 cosine Lovász certificate for the complement of an odd cycle `C_{2k+1}ᶜ`. -/
noncomputable def oddCycleComplLovaszCert (k : ℕ) (hk : 1 ≤ k) :
    LovaszCert (SimpleGraph.cycleGraph (2 * k + 1))ᶜ
      (Real.cos (Real.pi / (2 * k + 1 : ℝ)) / (1 + Real.cos (Real.pi / (2 * k + 1 : ℝ)))) := by
  let n : ℕ := 2 * k + 1
  have hn_cast : (n : ℝ) = (2 * k + 1 : ℝ) := by
    simp only [n]
    push_cast
    ring
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact Nat.cast_pos.mpr this
  have hc_pos : 0 < Real.cos (Real.pi / (n : ℝ)) := cos_pi_div_odd_pos k hk
  let c : ℝ := Real.cos (Real.pi / (n : ℝ))
  let β : ℝ := c / (1 + c)
  have hβ_eq :
      β = Real.cos (Real.pi / (2 * k + 1 : ℝ)) / (1 + Real.cos (Real.pi / (2 * k + 1 : ℝ))) := by
    simp only [β, c, hn_cast]
  refine LovaszCert.withBeta (β₁ := β) ?_ hβ_eq
  refine
    { W := Matrix.of fun i j : Fin n =>
        (c + Real.cos (2 * (k : ℝ) * Real.pi * ((i.val : ℝ) - (j.val : ℝ)) / (n : ℝ))) /
          (1 + c)
      hβ := div_pos hc_pos (by linarith)
      symm := Matrix.IsSymm.ext fun i j => by
        simp only [Matrix.of_apply]
        have harg :
            2 * (k : ℝ) * Real.pi * ((j.val : ℝ) - (i.val : ℝ)) / (n : ℝ) =
              -(2 * (k : ℝ) * Real.pi * ((i.val : ℝ) - (j.val : ℝ)) / (n : ℝ)) := by
          ring
        rw [harg, Real.cos_neg]
      diag_le_one := fun i => by
        have hden : 1 + c ≠ 0 := by linarith
        simp only [Matrix.of_apply, sub_self, mul_zero, zero_div, Real.cos_zero]
        rw [add_comm, div_self hden]
      nonadj_zero := fun i j hij hadj => by
        simp only [Matrix.of_apply]
        have hcycle : (SimpleGraph.cycleGraph n).Adj i j := by
          change ¬ (SimpleGraph.cycleGraph n)ᶜ.Adj i j at hadj
          simp only [SimpleGraph.compl_adj] at hadj
          by_contra hnot
          exact hadj ⟨hij, hnot⟩
        let d : ℤ := (i.val : ℤ) - (j.val : ℤ)
        have hd_cast : (i.val : ℝ) - (j.val : ℝ) = (d : ℝ) := by
          simp only [d]
          push_cast
          rfl
        have hcos :
            Real.cos (2 * (k : ℝ) * Real.pi * ((i.val : ℝ) - (j.val : ℝ)) / (n : ℝ)) = -c := by
          rw [hd_cast]
          rcases SimpleGraph.cycleGraph_adj'.mp hcycle with h1 | h2
          · obtain ⟨q, hq⟩ := (fin_sub_val_eq_one_iff_dvd (by omega) i j).mp h1
            have hd_eq : (d : ℝ) = (n : ℝ) * (q : ℝ) + 1 := by
              have hzq : d = (n : ℤ) * q + 1 := by linarith
              exact_mod_cast hzq
            have harg :
                2 * (k : ℝ) * Real.pi * (d : ℝ) / (n : ℝ) =
                  (Real.pi - Real.pi / (n : ℝ)) + (((k : ℤ) * q : ℤ) : ℝ) * (2 * Real.pi) := by
              rw [hd_eq]
              have hn_lin : (n : ℝ) = 2 * (k : ℝ) + 1 := by simp only [n]; push_cast; ring
              push_cast
              field_simp [hn_pos.ne']
              rw [hn_lin]
              ring
            rw [harg, Real.cos_add_int_mul_two_pi, Real.cos_pi_sub]
          · obtain ⟨q, hq⟩ := (fin_sub_val_eq_one_iff_dvd_add (by omega) i j).mp h2
            have hd_eq : (d : ℝ) = (n : ℝ) * (q : ℝ) - 1 := by
              have hzq : d = (n : ℤ) * q - 1 := by linarith
              exact_mod_cast hzq
            have harg :
                2 * (k : ℝ) * Real.pi * (d : ℝ) / (n : ℝ) =
                  (((k : ℤ) * q : ℤ) : ℝ) * (2 * Real.pi) - (Real.pi - Real.pi / (n : ℝ)) := by
              rw [hd_eq]
              have hn_lin : (n : ℝ) = 2 * (k : ℝ) + 1 := by simp only [n]; push_cast; ring
              push_cast
              field_simp [hn_pos.ne']
              rw [hn_lin]
              ring
            rw [harg, Real.cos_int_mul_two_pi_sub, Real.cos_pi_sub]
        rw [hcos, add_neg_cancel, zero_div]
      psd := ?_ }
  have hdecomp :
      Matrix.of (fun i j : Fin n =>
          (c + Real.cos (2 * (k : ℝ) * Real.pi * ((i.val : ℝ) - (j.val : ℝ)) / (n : ℝ))) /
            (1 + c)) -
        β • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) =
        (1 + c)⁻¹ •
          Matrix.of (fun i j : Fin n =>
            Real.cos (2 * (k : ℝ) * Real.pi * (i.val : ℝ) / (n : ℝ) -
              2 * (k : ℝ) * Real.pi * (j.val : ℝ) / (n : ℝ))) := by
    ext i j
    have harg :
        2 * (k : ℝ) * Real.pi * ((i.val : ℝ) - (j.val : ℝ)) / (n : ℝ) =
          2 * (k : ℝ) * Real.pi * (i.val : ℝ) / (n : ℝ) -
            2 * (k : ℝ) * Real.pi * (j.val : ℝ) / (n : ℝ) := by
      ring
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one,
      β, harg]
    ring
  rw [hdecomp]
  exact (posSemidef_cos_sub fun i : Fin n =>
    2 * (k : ℝ) * Real.pi * (i.val : ℝ) / (n : ℝ)).smul (by positivity)

/-- Lovász upper bound for the complement of an odd cycle:
`Θ(C_{2k+1}ᶜ) ≤ 1 + (cos(π / (2k + 1)))⁻¹`. -/
theorem oddCycle_compl_upper_lovasz (k : ℕ) (hk : 1 ≤ k) :
    shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1))ᶜ ≤
      1 + (Real.cos (Real.pi / (2 * k + 1 : ℝ)))⁻¹ := by
  have h := shannonCapacity_le_of_cert (oddCycleComplLovaszCert k hk)
  have hc_pos : 0 < Real.cos (Real.pi / (2 * k + 1 : ℝ)) := by
    have h1 := cos_pi_div_odd_pos k hk
    push_cast at h1
    exact h1
  have hinv :
      (Real.cos (Real.pi / (2 * k + 1 : ℝ)) /
        (1 + Real.cos (Real.pi / (2 * k + 1 : ℝ))))⁻¹ =
        1 + (Real.cos (Real.pi / (2 * k + 1 : ℝ)))⁻¹ := by
    rw [inv_div, add_div, one_div, div_self hc_pos.ne', add_comm]
  rwa [hinv] at h

/-- Lovász upper bound for the complement of the 7-cycle: `Θ(C₇ᶜ) ≤ 1 + sec(π / 7)`. -/
theorem c7_compl_upper_lovasz :
    shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ≤ 1 + (Real.cos (Real.pi / 7))⁻¹ := by
  have h := oddCycle_compl_upper_lovasz 3 (by norm_num)
  norm_num at h
  exact h

end ShannonC7
