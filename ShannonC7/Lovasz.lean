import ShannonC7.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Lovász Semidefinite Upper-Bound Engine (`ShannonC7/Lovasz.lean`)

This module develops the Kronecker-multiplicative semidefinite certificate `LovaszCert`
proving `shannonCapacity G ≤ β⁻¹`, establishes the general Orthonormal Representation
(Lovász umbrella) bridge over any real inner product space, and proves Lovász's classic
warm-up theorem `shannonCapacity (SimpleGraph.cycleGraph 5) = Real.sqrt 5`.
-/

namespace ShannonC7

open scoped Kronecker

universe u v

/-! ## Positive Semidefinite Matrix Building Blocks -/

/-- The all-ones matrix over `ℝ` is positive semidefinite. -/
theorem posSemidef_allOnes (V : Type*) [Fintype V] :
    (Matrix.of fun _ _ : V => (1 : ℝ)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr (Matrix.IsSymm.ext fun _ _ => rfl)
  · intro x
    have hquad :
        star x ⬝ᵥ (Matrix.of fun _ _ : V => (1 : ℝ)).mulVec x = (∑ i : V, x i) ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Matrix.of_apply,
        one_mul, sq, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hquad]
    exact sq_nonneg _

/-- Any Gram matrix `(⟨w i, w j⟩)` over a real inner product space is positive semidefinite. -/
theorem posSemidef_gram_inner {V E : Type*} [Fintype V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (w : V → E) :
    (Matrix.of fun i j => inner ℝ (w i) (w j)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr
      (Matrix.IsSymm.ext fun i j => real_inner_comm (w i) (w j))
  · intro x
    have hquad :
        star x ⬝ᵥ (Matrix.of fun i j => inner ℝ (w i) (w j)).mulVec x =
          inner ℝ (∑ i : V, x i • w i) (∑ j : V, x j • w j) := by
      rw [sum_inner]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Matrix.of_apply,
        Finset.mul_sum, inner_sum, real_inner_smul_left, real_inner_smul_right]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hquad]
    exact real_inner_self_nonneg

/-- Any rank-2 cosine difference matrix `(cos (θ i - θ j))` is positive semidefinite. -/
theorem posSemidef_cos_sub {V : Type*} [Fintype V] (θ : V → ℝ) :
    (Matrix.of fun i j => Real.cos (θ i - θ j)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr
      (Matrix.IsSymm.ext fun i j => by
        rw [Matrix.of_apply, Matrix.of_apply, ← neg_sub (θ i) (θ j), Real.cos_neg])
  · intro x
    have hquad :
        star x ⬝ᵥ (Matrix.of fun i j => Real.cos (θ i - θ j)).mulVec x =
          (∑ i : V, x i * Real.cos (θ i)) ^ 2 + (∑ i : V, x i * Real.sin (θ i)) ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Matrix.of_apply,
        Real.cos_sub, sq, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hquad]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ## Kronecker-Multiplicative Lovász Certificate -/

set_option linter.unusedFintypeInType false in
/-- A Lovász semidefinite certificate proving `shannonCapacity G ≤ β⁻¹`.
Relaxing diagonal entries to `W i i ≤ 1` ensures exact closure under Kronecker products. -/
structure LovaszCert {V : Type*} [Fintype V] (G : SimpleGraph V) (β : ℝ) where
  W : Matrix V V ℝ
  hβ : 0 < β
  symm : W.IsSymm
  diag_le_one : ∀ i, W i i ≤ 1
  nonadj_zero : ∀ i j, i ≠ j → ¬ G.Adj i j → W i j = 0
  psd : (W - β • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef

theorem LovaszCert.diag_nonneg {V : Type*} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : LovaszCert G β) (i : V) : 0 ≤ cert.W i i := by
  have h := cert.psd.diag_nonneg (i := i)
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one] at h
  linarith [cert.hβ]

theorem LovaszCert.W_psd {V : Type*} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : LovaszCert G β) : cert.W.PosSemidef := by
  have hdecomp :
      cert.W =
        (cert.W - β • Matrix.of (fun _ _ : V => (1 : ℝ))) +
          β • Matrix.of (fun _ _ : V => (1 : ℝ)) :=
    (sub_add_cancel cert.W _).symm
  rw [hdecomp]
  exact cert.psd.add ((posSemidef_allOnes V).smul cert.hβ.le)

theorem LovaszCert.card_le {V : Type*} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : LovaszCert G β) {s : Finset V} (hs : G.IsIndepSet (s : Set V)) :
    (s.card : ℝ) ≤ β⁻¹ := by
  classical
  let x : V → ℝ := fun i => if i ∈ s then 1 else 0
  have hquad := cert.psd.dotProduct_mulVec_nonneg x
  have hlhs :
      star x ⬝ᵥ (cert.W - β • Matrix.of (fun _ _ : V => (1 : ℝ))).mulVec x =
        (∑ i ∈ s, ∑ j ∈ s, cert.W i j) - (s.card : ℝ) * ((s.card : ℝ) * β) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, x, ite_mul, one_mul, zero_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul]
  rw [hlhs] at hquad
  have hdiag_sum : ∑ i ∈ s, ∑ j ∈ s, cert.W i j = ∑ i ∈ s, cert.W i i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    exact Finset.sum_eq_single i
      (fun j hj hji => cert.nonadj_zero i j hji.symm (hs hi hj hji.symm))
      (fun hi' => absurd hi hi')
  have hsum_le : ∑ i ∈ s, cert.W i i ≤ (s.card : ℝ) := by
    calc ∑ i ∈ s, cert.W i i
        ≤ ∑ _i ∈ s, (1 : ℝ) := Finset.sum_le_sum fun i _ => cert.diag_le_one i
      _ = (s.card : ℝ) := by simp
  rw [hdiag_sum] at hquad
  by_cases hcard : s.card = 0
  · rw [hcard, Nat.cast_zero]
    exact inv_nonneg.mpr cert.hβ.le
  · have hpos : (0 : ℝ) < (s.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard)
    have hmul : (s.card : ℝ) * β ≤ 1 := by nlinarith
    have hinv : 0 < β⁻¹ := inv_pos.mpr cert.hβ
    nlinarith [mul_inv_cancel₀ cert.hβ.ne']

theorem LovaszCert.indepNum_le {V : Type*} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : LovaszCert G β) : (G.indepNum : ℝ) ≤ β⁻¹ := by
  obtain ⟨s, hs_indep, hs_card⟩ := G.exists_isNIndepSet_indepNum
  rw [← hs_card]
  exact cert.card_le hs_indep

/-- Re-index the scalar parameter `β` of a `LovaszCert` along an equality `β₁ = β₂`. -/
def LovaszCert.withBeta {V : Type*} [Fintype V] {G : SimpleGraph V} {β₁ β₂ : ℝ}
    (cert : LovaszCert G β₁) (h : β₁ = β₂) : LovaszCert G β₂ where
  W := cert.W
  hβ := h ▸ cert.hβ
  symm := cert.symm
  diag_le_one := cert.diag_le_one
  nonadj_zero := cert.nonadj_zero
  psd := h ▸ cert.psd

/-- Trivial Lovász certificate on the 1-vertex empty graph `⊥` on `PUnit.{u + 1}`. -/
def LovaszCert.unit : LovaszCert (⊥ : SimpleGraph PUnit.{u + 1}) 1 where
  W := Matrix.of fun _ _ => (1 : ℝ)
  hβ := zero_lt_one
  symm := Matrix.IsSymm.ext fun _ _ => rfl
  diag_le_one := fun _ => le_rfl
  nonadj_zero := fun i j hij _ => absurd (Subsingleton.elim i j) hij
  psd := by
    have hzero :
        Matrix.of (fun _ _ : PUnit.{u + 1} => (1 : ℝ)) -
          (1 : ℝ) • Matrix.of (fun _ _ : PUnit.{u + 1} => (1 : ℝ)) = 0 := by
      ext _ _
      simp
    rw [hzero]
    exact Matrix.PosSemidef.zero

/-- Kronecker product closure of Lovász certificates under strong graph products. -/
def LovaszCert.prod {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {β₁ β₂ : ℝ}
    (c₁ : LovaszCert G β₁) (c₂ : LovaszCert H β₂) :
    LovaszCert (G ⊠ H) (β₁ * β₂) where
  W := c₁.W ⊗ₖ c₂.W
  hβ := mul_pos c₁.hβ c₂.hβ
  symm := Matrix.IsSymm.ext fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => by
    simp [c₁.symm.apply, c₂.symm.apply]
  diag_le_one := fun ⟨i₁, i₂⟩ => by
    simpa [Matrix.kronecker_apply] using
      mul_le_one₀ (c₁.diag_le_one i₁) (c₂.diag_nonneg i₂) (c₂.diag_le_one i₂)
  nonadj_zero := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ hne hnadj
    have hnot : ¬ ((u₁, v₁) = (u₂, v₂) ∨ (G ⊠ H).Adj (u₁, v₁) (u₂, v₂)) :=
      not_or.mpr ⟨hne, hnadj⟩
    rw [eq_or_strongProd_adj] at hnot
    simp only [Matrix.kronecker_apply]
    rcases not_and_or.mp hnot with hu | hv
    · rcases not_or.mp hu with ⟨hune, hunadj⟩
      rw [c₁.nonadj_zero u₁ u₂ hune hunadj, zero_mul]
    · rcases not_or.mp hv with ⟨hvne, hvnadj⟩
      rw [c₂.nonadj_zero v₁ v₂ hvne hvnadj, mul_zero]
  psd := by
    have hdecomp :
        c₁.W ⊗ₖ c₂.W - (β₁ * β₂) • Matrix.of (fun _ _ : V × W => (1 : ℝ)) =
          (c₁.W - β₁ • Matrix.of (fun _ _ : V => (1 : ℝ))) ⊗ₖ c₂.W +
            (β₁ • Matrix.of (fun _ _ : V => (1 : ℝ))) ⊗ₖ
              (c₂.W - β₂ • Matrix.of (fun _ _ : W => (1 : ℝ))) := by
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.kronecker_apply, Matrix.of_apply, smul_eq_mul, mul_one]
      ring
    rw [hdecomp]
    exact (c₁.psd.kronecker c₂.W_psd).add
      (((posSemidef_allOnes V).smul c₁.hβ.le).kronecker c₂.psd)

/-- Iterated Kronecker power of a Lovász certificate for `strongPow G d`. -/
def LovaszCert.pow {V : Type u} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : LovaszCert G β) : (d : ℕ) → LovaszCert (strongPow G d) (β ^ d)
  | 0 => LovaszCert.unit.withBeta (pow_zero β).symm
  | d + 1 => (cert.prod (cert.pow d)).withBeta (pow_succ' β d).symm

/-- Master Lovász theorem: any `LovaszCert G β` upper-bounds `shannonCapacity G` by `β⁻¹`. -/
theorem shannonCapacity_le_of_cert {V : Type*} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : LovaszCert G β) : shannonCapacity G ≤ β⁻¹ := by
  refine shannonCapacity_le G (inv_nonneg.mpr cert.hβ.le) fun d _ => ?_
  have h := (cert.pow d).indepNum_le
  rwa [← inv_pow] at h

/-! ## Orthonormal Representation Bridge (Lovász Umbrella Theorem) -/

/-- Construct a `LovaszCert G β` from an orthonormal representation `u : V → E` and unit handle `c`
in any real inner product space `E` (including `EuclideanSpace ℝ (Fin k)`). -/
noncomputable def LovaszCert.ofOrthonormalRep
    {V E : Type*} [Fintype V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : SimpleGraph V} {β : ℝ} (hβ : 0 < β)
    (u : V → E) (c : E)
    (hc : ‖c‖ = 1)
    (hu_unit : ∀ v, ‖u v‖ = 1)
    (hu_orth : ∀ i j, i ≠ j → ¬ G.Adj i j → inner ℝ (u i) (u j) = 0)
    (hhandle : ∀ v, β ≤ (inner ℝ c (u v)) ^ 2) :
    LovaszCert G β where
  W := Matrix.of fun i j =>
    β * inner ℝ (u i) (u j) / (inner ℝ c (u i) * inner ℝ c (u j))
  hβ := hβ
  symm := Matrix.IsSymm.ext fun i j => by
    simp only [Matrix.of_apply, real_inner_comm (u i) (u j), mul_comm (inner ℝ c (u i))]
  diag_le_one := fun i => by
    simp only [Matrix.of_apply, real_inner_self_eq_norm_sq, hu_unit i, one_pow, mul_one, ← sq]
    exact (div_le_one (lt_of_lt_of_le hβ (hhandle i))).mpr (hhandle i)
  nonadj_zero := fun i j hij hadj => by
    simp only [Matrix.of_apply, hu_orth i j hij hadj, mul_zero, zero_div]
  psd := by
    have hcu_ne : ∀ v : V, inner ℝ c (u v) ≠ 0 := fun v hv => by
      have h := hhandle v
      rw [hv] at h
      linarith
    let v : V → E := fun i => (inner ℝ c (u i))⁻¹ • u i
    let w : V → E := fun i => v i - c
    have hdecomp :
        Matrix.of (fun i j =>
          β * inner ℝ (u i) (u j) / (inner ℝ c (u i) * inner ℝ c (u j))) -
          β • Matrix.of (fun _ _ : V => (1 : ℝ)) =
          β • Matrix.of (fun i j => inner ℝ (w i) (w j)) := by
      ext i j
      have hcv : ∀ k : V, inner ℝ c (v k) = 1 := fun k => by
        simp only [v, real_inner_smul_right, inv_mul_cancel₀ (hcu_ne k)]
      have hvc : ∀ k : V, inner ℝ (v k) c = 1 := fun k => by
        rw [real_inner_comm, hcv k]
      have hcc : inner ℝ c c = 1 := by
        rw [real_inner_self_eq_norm_sq, hc, one_pow]
      have hvv : inner ℝ (v i) (v j) =
          inner ℝ (u i) (u j) / (inner ℝ c (u i) * inner ℝ c (u j)) := by
        simp only [v, real_inner_smul_left, real_inner_smul_right]
        field_simp [hcu_ne i, hcu_ne j]
      have hw : inner ℝ (w i) (w j) =
          inner ℝ (u i) (u j) / (inner ℝ c (u i) * inner ℝ c (u j)) - 1 := by
        simp only [w, inner_sub_left, inner_sub_right, hvv, hcv, hvc, hcc]
        ring
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one, hw]
      ring
    rw [hdecomp]
    exact (posSemidef_gram_inner w).smul hβ.le

/-- Lovász umbrella theorem: an orthonormal representation with handle margin `β > 0`
implies `shannonCapacity G ≤ β⁻¹`. -/
theorem shannonCapacity_le_of_orthonormalRep
    {V E : Type*} [Fintype V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : SimpleGraph V} {β : ℝ} (hβ : 0 < β)
    (u : V → E) (c : E)
    (hc : ‖c‖ = 1)
    (hu_unit : ∀ v, ‖u v‖ = 1)
    (hu_orth : ∀ i j, i ≠ j → ¬ G.Adj i j → inner ℝ (u i) (u j) = 0)
    (hhandle : ∀ v, β ≤ (inner ℝ c (u v)) ^ 2) :
    shannonCapacity G ≤ β⁻¹ :=
  shannonCapacity_le_of_cert
    (LovaszCert.ofOrthonormalRep hβ u c hc hu_unit hu_orth hhandle)

/-! ## Warm-Up Theorem: Exact Shannon Capacity of `C₅` -/

private lemma c5_nonadj_diff :
    ∀ i j : Fin 5, i ≠ j → ¬ (SimpleGraph.cycleGraph 5).Adj i j →
      (i.val : ℤ) - (j.val : ℤ) = 2 ∨ (i.val : ℤ) - (j.val : ℤ) = -2 ∨
        (i.val : ℤ) - (j.val : ℤ) = 3 ∨ (i.val : ℤ) - (j.val : ℤ) = -3 := by
  decide

/-- Explicit rank-2 Lovász certificate for the 5-cycle achieving `β⁻¹ = √5`. -/
noncomputable def c5LovaszCert :
    LovaszCert (SimpleGraph.cycleGraph 5)
      (Real.cos (Real.pi / 5) / (1 + Real.cos (Real.pi / 5))) where
  W := Matrix.of fun i j : Fin 5 =>
    (Real.cos (Real.pi / 5) +
      Real.cos (2 * Real.pi * ((i.val : ℝ) - (j.val : ℝ)) / 5)) /
      (1 + Real.cos (Real.pi / 5))
  hβ := by
    rw [Real.cos_pi_div_five]
    positivity
  symm := Matrix.IsSymm.ext fun i j => by
    simp only [Matrix.of_apply]
    have harg :
        2 * Real.pi * ((j.val : ℝ) - (i.val : ℝ)) / 5 =
          -(2 * Real.pi * ((i.val : ℝ) - (j.val : ℝ)) / 5) := by ring
    rw [harg, Real.cos_neg]
  diag_le_one := fun i => by
    have hden : 1 + Real.cos (Real.pi / 5) ≠ 0 := by
      rw [Real.cos_pi_div_five]
      positivity
    simp only [Matrix.of_apply, sub_self, mul_zero, zero_div, Real.cos_zero]
    rw [add_comm, div_self hden]
  nonadj_zero := fun i j hij hadj => by
    simp only [Matrix.of_apply]
    have hdiff_real :
        (i.val : ℝ) - (j.val : ℝ) = 2 ∨ (i.val : ℝ) - (j.val : ℝ) = -2 ∨
          (i.val : ℝ) - (j.val : ℝ) = 3 ∨ (i.val : ℝ) - (j.val : ℝ) = -3 := by
      rcases c5_nonadj_diff i j hij hadj with h | h | h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (Or.inl (by exact_mod_cast h))
      · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast h)))
      · exact Or.inr (Or.inr (Or.inr (by exact_mod_cast h)))
    have hcos :
        Real.cos (2 * Real.pi * ((i.val : ℝ) - (j.val : ℝ)) / 5) = -Real.cos (Real.pi / 5) := by
      rcases hdiff_real with h | h | h | h <;> rw [h]
      · have harg : 2 * Real.pi * (2 : ℝ) / 5 = Real.pi - Real.pi / 5 := by ring
        rw [harg, Real.cos_pi_sub]
      · have harg : 2 * Real.pi * (-2 : ℝ) / 5 = -(Real.pi - Real.pi / 5) := by ring
        rw [harg, Real.cos_neg, Real.cos_pi_sub]
      · have harg : 2 * Real.pi * (3 : ℝ) / 5 = Real.pi / 5 + Real.pi := by ring
        rw [harg, Real.cos_add_pi]
      · have harg : 2 * Real.pi * (-3 : ℝ) / 5 = -(Real.pi / 5 + Real.pi) := by ring
        rw [harg, Real.cos_neg, Real.cos_add_pi]
    rw [hcos, add_neg_cancel, zero_div]
  psd := by
    have hdecomp :
        Matrix.of (fun i j : Fin 5 =>
          (Real.cos (Real.pi / 5) +
            Real.cos (2 * Real.pi * ((i.val : ℝ) - (j.val : ℝ)) / 5)) /
            (1 + Real.cos (Real.pi / 5))) -
          (Real.cos (Real.pi / 5) / (1 + Real.cos (Real.pi / 5))) •
            Matrix.of (fun _ _ : Fin 5 => (1 : ℝ)) =
          (1 + Real.cos (Real.pi / 5))⁻¹ •
            Matrix.of (fun i j : Fin 5 =>
              Real.cos (2 * Real.pi * (i.val : ℝ) / 5 - 2 * Real.pi * (j.val : ℝ) / 5)) := by
      ext i j
      have harg :
          2 * Real.pi * ((i.val : ℝ) - (j.val : ℝ)) / 5 =
            2 * Real.pi * (i.val : ℝ) / 5 - 2 * Real.pi * (j.val : ℝ) / 5 := by ring
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one, harg]
      ring
    rw [hdecomp]
    refine (posSemidef_cos_sub (fun i : Fin 5 => 2 * Real.pi * (i.val : ℝ) / 5)).smul ?_
    rw [Real.cos_pi_div_five]
    positivity

/-- Lovász's theorem (1979): the Shannon capacity of the 5-cycle equals `√5`. -/
theorem c5_shannonCapacity_eq_sqrt_five :
    shannonCapacity (SimpleGraph.cycleGraph 5) = Real.sqrt 5 := by
  apply le_antisymm
  · have hupper := shannonCapacity_le_of_cert c5LovaszCert
    have hinv :
        (Real.cos (Real.pi / 5) / (1 + Real.cos (Real.pi / 5)))⁻¹ = Real.sqrt 5 := by
      rw [inv_div, Real.cos_pi_div_five]
      have hpos : 1 + Real.sqrt 5 ≠ 0 := by positivity
      field_simp [hpos]
      nlinarith [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    rwa [hinv] at hupper
  · let w : Fin 5 → Fin 2 → Fin 5 := fun i k => if k = 0 then i else 2 * i
    have hw_inj : Function.Injective w := by
      intro i j hij
      simpa [w] using congr_fun hij 0
    let s : Finset (Fin 2 → Fin 5) := Finset.univ.image w
    have hcheck : ∀ i j : Fin 5, i ≠ j →
        ¬ (strongPowPi (SimpleGraph.cycleGraph 5) 2).Adj (w i) (w j) := by
      decide
    have hs : (strongPowPi (SimpleGraph.cycleGraph 5) 2).IsIndepSet (s : Set (Fin 2 → Fin 5)) := by
      intro x hx y hy hxy
      simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      rcases hx with ⟨i, rfl⟩
      rcases hy with ⟨j, rfl⟩
      exact hcheck i j fun hij => hxy (congrArg w hij)
    have hcard : s.card = 5 := by
      rw [Finset.card_image_of_injective _ hw_inj, Finset.card_univ, Fintype.card_fin]
    have hlow :=
      le_shannonCapacity_of_indepSet_pi (SimpleGraph.cycleGraph 5) (by norm_num : 0 < 2) hs
    rw [hcard, Nat.cast_ofNat, Nat.cast_ofNat, ← Real.sqrt_eq_rpow] at hlow
    exact hlow

end ShannonC7
