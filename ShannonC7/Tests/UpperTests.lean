import ShannonC7.Lovasz
import ShannonC7.LovaszC7
import ShannonC7.CubicBounds
import ShannonC7.Haemers
import Mathlib.Algebra.Field.ZMod

/-!
# Upper-Bound Unit Tests & Contract Conformance (`ShannonC7/Tests/UpperTests.lean`)

Validates:
1. Verbatim type-signature conformance with `PROJECT.md` §4.2 and `M2_UpperTheory` scope.
2. Edge-case and functional sanity checks for `LovaszCert` (on `⊥`, `⊤`, `PUnit`, `prod`,
   and `EuclideanSpace ℝ (Fin 3)` orthonormal representations), odd-cycle upper bounds
   (`k = 1, 2, 3`), cubic rational enclosure, unattainability instantiations, and Haemers
   minrank over characteristic 0 (`ℚ`, `ℝ`) and positive characteristic (`ZMod 2`).
3. Explicit `#print axioms` checks for every public theorem across `Lovasz`, `LovaszC7`,
   `CubicBounds`, and `Haemers`.
-/

namespace ShannonC7.Tests

open ShannonC7
open scoped Kronecker

/-! ## 1. Verbatim Interface Contract Conformance (`PROJECT.md` §4.2) -/

section ContractChecks

-- ShannonC7.Lovasz
example {V : Type*} [Fintype V] (G : SimpleGraph V) (β : ℝ) : Type _ :=
  LovaszCert G β

example {V : Type*} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : LovaszCert G β) {s : Finset V} (hs : G.IsIndepSet (s : Set V)) :
    (s.card : ℝ) ≤ β⁻¹ :=
  cert.card_le hs

example {V : Type*} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : LovaszCert G β) : (G.indepNum : ℝ) ≤ β⁻¹ :=
  cert.indepNum_le

example : LovaszCert (⊥ : SimpleGraph PUnit) 1 :=
  LovaszCert.unit

example {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    {β₁ β₂ : ℝ} (c₁ : LovaszCert G β₁) (c₂ : LovaszCert H β₂) :
    LovaszCert (G ⊠ H) (β₁ * β₂) :=
  c₁.prod c₂

example {V : Type*} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : LovaszCert G β) (d : ℕ) : LovaszCert (strongPow G d) (β ^ d) :=
  cert.pow d

example {V : Type*} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : LovaszCert G β) : shannonCapacity G ≤ β⁻¹ :=
  shannonCapacity_le_of_cert cert

noncomputable example {V E : Type*} [Fintype V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : SimpleGraph V} {β : ℝ} (hβ : 0 < β)
    (u : V → E) (c : E) (hc : ‖c‖ = 1) (hu_unit : ∀ v, ‖u v‖ = 1)
    (hu_orth : ∀ i j, i ≠ j → ¬ G.Adj i j → inner ℝ (u i) (u j) = 0)
    (hhandle : ∀ v, β ≤ (inner ℝ c (u v)) ^ 2) :
    LovaszCert G β :=
  LovaszCert.ofOrthonormalRep hβ u c hc hu_unit hu_orth hhandle

example : shannonCapacity (SimpleGraph.cycleGraph 5) = Real.sqrt 5 :=
  c5_shannonCapacity_eq_sqrt_five

-- ShannonC7.LovaszC7
noncomputable example : ℝ := lovaszThetaC7

example : shannonCapacity (SimpleGraph.cycleGraph 7) ≤ lovaszThetaC7 :=
  c7_upper_lovasz

example : shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ≤ 1 + (Real.cos (Real.pi / 7))⁻¹ :=
  c7_compl_upper_lovasz

example (k : ℕ) (hk : 1 ≤ k) :
    shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1)) ≤
      ((2 * k + 1 : ℝ) * Real.cos (Real.pi / (2 * k + 1))) /
        (1 + Real.cos (Real.pi / (2 * k + 1))) :=
  oddCycle_upper_lovasz k hk

-- ShannonC7.CubicBounds
example :
    8 * (Real.cos (Real.pi / 7)) ^ 3 - 4 * (Real.cos (Real.pi / 7)) ^ 2 -
      4 * Real.cos (Real.pi / 7) + 1 = 0 :=
  cos_pi_div_seven_cubic

example :
    lovaszThetaC7 ^ 3 + 7 * lovaszThetaC7 ^ 2 - 49 * lovaszThetaC7 + 49 = 0 :=
  lovaszThetaC7_cubic

example {q : ℝ} (hq : 3 ≤ q) (hp : 0 < q ^ 3 + 7 * q ^ 2 - 49 * q + 49) :
    lovaszThetaC7 < q :=
  lovaszThetaC7_lt_of_cubic_pos hq hp

example :
    shannonCapacity (SimpleGraph.cycleGraph 7) < (3317667207395 : ℝ) / 1000000000000 :=
  c7_upper_rational

example (d : ℕ) (hd : 0 < d) :
    ((strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ^ (1 / (d : ℝ)) < lovaszThetaC7 :=
  c7_lovasz_unattainable d hd

-- ShannonC7.Haemers
example {V : Type*} {F : Type*} [Field F] (G : SimpleGraph V) (M : Matrix V V F) : Prop :=
  IsFittingMatrix G M

example {V : Type*} [Fintype V] {F : Type*} [Field F]
    {G : SimpleGraph V} {M : Matrix V V F} (hM : IsFittingMatrix G M) :
    G.indepNum ≤ M.rank :=
  indepNum_le_rank_of_fitting hM

example {l m n p F : Type*} [Fintype m] [Fintype p] [Field F]
    (M : Matrix l m F) (N : Matrix n p F) :
    (M ⊗ₖ N).rank ≤ M.rank * N.rank :=
  rank_kronecker_le M N

example {V : Type*} [Fintype V] {F : Type*} [Field F]
    {G : SimpleGraph V} {M : Matrix V V F} (hM : IsFittingMatrix G M) :
    shannonCapacity G ≤ (M.rank : ℝ) :=
  shannonCapacity_le_haemers_rank hM

example {F : Type*} [Field F]
    (M : Matrix (Fin 7) (Fin 7) F) (hM : IsFittingMatrix (SimpleGraph.cycleGraph 7) M) :
    4 ≤ M.rank :=
  haemers_minrank_c7_ge_four M hM

end ContractChecks

/-! ## 2. Edge-Case & Functional Sanity Checks -/

/-- Complete graph `⊤` admits a `LovaszCert` with `β = 1`, giving `Θ(⊤) ≤ 1`. -/
theorem topGraph_shannonCapacity_le_one {V : Type*} [Fintype V] :
    shannonCapacity (⊤ : SimpleGraph V) ≤ 1 := by
  let cert : LovaszCert (⊤ : SimpleGraph V) 1 :=
    { W := Matrix.of fun _ _ => (1 : ℝ)
      hβ := zero_lt_one
      symm := Matrix.IsSymm.ext fun _ _ => rfl
      diag_le_one := fun _ => le_rfl
      nonadj_zero := fun _ _ hij hadj => absurd hij hadj
      psd := by
        have hzero :
            Matrix.of (fun _ _ : V => (1 : ℝ)) -
              (1 : ℝ) • Matrix.of (fun _ _ : V => (1 : ℝ)) = 0 := by
          ext _ _
          simp
        rw [hzero]
        exact Matrix.PosSemidef.zero }
  simpa using shannonCapacity_le_of_cert cert

/-- Single-vertex empty graph `⊥` on `PUnit` satisfies `Θ(⊥) ≤ 1` via `LovaszCert.unit`. -/
theorem punit_bot_shannonCapacity_le_one :
    shannonCapacity (⊥ : SimpleGraph PUnit) ≤ 1 := by
  simpa using shannonCapacity_le_of_cert LovaszCert.unit

/-- Concrete `EuclideanSpace ℝ (Fin 3)` orthonormal representation test for `⊥` on `Fin 3`. -/
theorem fin3_bot_shannonCapacity_le_three_via_orthonormalRep :
    shannonCapacity (⊥ : SimpleGraph (Fin 3)) ≤ 3 := by
  let u : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
    fun i => WithLp.toLp 2 (fun k : Fin 3 => if k = i then (1 : ℝ) else 0)
  let c : EuclideanSpace ℝ (Fin 3) :=
    WithLp.toLp 2 (fun _ : Fin 3 => (Real.sqrt 3)⁻¹)
  have hsqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcu : ∀ i : Fin 3, inner ℝ c (u i) = (Real.sqrt 3)⁻¹ := by
    intro i
    change dotProduct (fun k : Fin 3 => if k = i then (1 : ℝ) else 0)
        (star fun _ : Fin 3 => (Real.sqrt 3)⁻¹) = (Real.sqrt 3)⁻¹
    simp [dotProduct]
  have hcc : inner ℝ c c = 1 := by
    change dotProduct (fun _ : Fin 3 => (Real.sqrt 3)⁻¹)
        (star fun _ : Fin 3 => (Real.sqrt 3)⁻¹) = 1
    simp only [dotProduct, Pi.star_apply, star_trivial, Fin.sum_univ_three]
    have hsq : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = (3 : ℝ)⁻¹ := by
      rw [← mul_inv, ← sq, hsqrt3]
    rw [hsq]
    norm_num
  have hc : ‖c‖ = 1 := by
    have hsq : ‖c‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hcc]
    nlinarith [norm_nonneg c]
  have hu_unit : ∀ i : Fin 3, ‖u i‖ = 1 := by
    intro i
    have hii : inner ℝ (u i) (u i) = 1 := by
      change dotProduct (fun k : Fin 3 => if k = i then (1 : ℝ) else 0)
          (star fun k : Fin 3 => if k = i then (1 : ℝ) else 0) = 1
      simp only [dotProduct, Pi.star_apply, star_trivial, Fin.sum_univ_three]
      fin_cases i <;> simp
    have hsq : ‖u i‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hii]
    nlinarith [norm_nonneg (u i)]
  have hu_orth : ∀ i j : Fin 3, i ≠ j → ¬ (⊥ : SimpleGraph (Fin 3)).Adj i j →
      inner ℝ (u i) (u j) = 0 := by
    intro i j hij _
    change dotProduct (fun k : Fin 3 => if k = j then (1 : ℝ) else 0)
        (star fun k : Fin 3 => if k = i then (1 : ℝ) else 0) = 0
    simp only [dotProduct, Pi.star_apply, star_trivial, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp_all
  have hhandle : ∀ i : Fin 3, (1 : ℝ) / 3 ≤ (inner ℝ c (u i)) ^ 2 := by
    intro i
    rw [hcu i, inv_pow, hsqrt3]
    norm_num
  have hbound :=
    shannonCapacity_le_of_orthonormalRep (G := (⊥ : SimpleGraph (Fin 3)))
      (β := (1 : ℝ) / 3) (by norm_num) u c hc hu_unit hu_orth hhandle
  norm_num at hbound
  exact hbound

-- Odd-cycle upper bound instantiations at k = 1, 2, 3
example :
    shannonCapacity (SimpleGraph.cycleGraph 3) ≤
      ((2 * (1 : ℕ) + 1 : ℝ) * Real.cos (Real.pi / (2 * (1 : ℕ) + 1))) /
        (1 + Real.cos (Real.pi / (2 * (1 : ℕ) + 1))) :=
  oddCycle_upper_lovasz 1 le_rfl

example :
    shannonCapacity (SimpleGraph.cycleGraph 5) ≤
      ((2 * (2 : ℕ) + 1 : ℝ) * Real.cos (Real.pi / (2 * (2 : ℕ) + 1))) /
        (1 + Real.cos (Real.pi / (2 * (2 : ℕ) + 1))) :=
  oddCycle_upper_lovasz 2 (by norm_num)

example :
    shannonCapacity (SimpleGraph.cycleGraph 7) ≤
      ((2 * (3 : ℕ) + 1 : ℝ) * Real.cos (Real.pi / (2 * (3 : ℕ) + 1))) /
        (1 + Real.cos (Real.pi / (2 * (3 : ℕ) + 1))) :=
  oddCycle_upper_lovasz 3 (by norm_num)

-- Rational enclosure and unattainability instantiations
example : 3 < lovaszThetaC7 := lovaszThetaC7_gt_three

example : lovaszThetaC7 < (331767 : ℝ) / 100000 :=
  lovaszThetaC7_lt_of_cubic_pos (by norm_num) (by norm_num)

example :
    ((strongPowPi (SimpleGraph.cycleGraph 7) 1).indepNum : ℝ) ^ (1 / ((1 : ℕ) : ℝ)) <
      lovaszThetaC7 :=
  c7_lovasz_unattainable 1 Nat.one_pos

example :
    ((strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum : ℝ) ^ (1 / ((5 : ℕ) : ℝ)) <
      lovaszThetaC7 :=
  c7_lovasz_unattainable 5 (by decide)

example : lovaszThetaC7 ^ 1 ≠ ((3317667207395 / 1000000000000 : ℚ) : ℝ) :=
  lovaszThetaC7_pow_ne_rat 1 Nat.one_pos (3317667207395 / 1000000000000)

-- Haemers minrank over characteristic 0 (`ℚ`, `ℝ`) and characteristic 2 (`ZMod 2`)
theorem bot_shannonCapacity_le_card_via_haemers_rat (V : Type*) [Fintype V] [DecidableEq V] :
    shannonCapacity (⊥ : SimpleGraph V) ≤ (Fintype.card V : ℝ) := by
  have hfit : IsFittingMatrix (⊥ : SimpleGraph V) (1 : Matrix V V ℚ) :=
    { diag_ne_zero := fun _ => by simp
      nonadj_zero := fun _ _ hne _ => by simp [hne] }
  have hle := shannonCapacity_le_haemers_rank hfit
  rwa [Matrix.rank_one] at hle

theorem top_shannonCapacity_le_one_via_haemers_zmod2 (V : Type*) [Fintype V] :
    shannonCapacity (⊤ : SimpleGraph V) ≤ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M : Matrix V V (ZMod 2) := Matrix.vecMulVec (fun _ => (1 : ZMod 2)) (fun _ => (1 : ZMod 2))
  have hfit : IsFittingMatrix (⊤ : SimpleGraph V) M :=
    { diag_ne_zero := fun _ => by simp [M, Matrix.vecMulVec_apply]
      nonadj_zero := fun _ _ hij hadj => absurd hij hadj }
  have hrank : M.rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have hle := shannonCapacity_le_haemers_rank hfit
  have hcast : (M.rank : ℝ) ≤ 1 := by exact_mod_cast hrank
  exact hle.trans hcast

example (M : Matrix (Fin 7) (Fin 7) (ZMod 2))
    (hM : IsFittingMatrix (SimpleGraph.cycleGraph 7) M) : 4 ≤ M.rank := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact haemers_minrank_c7_ge_four M hM

example (M : Matrix (Fin 7) (Fin 7) ℚ)
    (hM : IsFittingMatrix (SimpleGraph.cycleGraph 7) M) : 4 ≤ M.rank :=
  haemers_minrank_c7_ge_four M hM

example (M : Matrix (Fin 7) (Fin 7) ℝ)
    (hM : IsFittingMatrix (SimpleGraph.cycleGraph 7) M) : 4 ≤ M.rank :=
  haemers_minrank_c7_ge_four M hM

/-! ## 3. Explicit `#print axioms` Checks on All Public M2 Theorems -/

-- ShannonC7.Lovasz
#print axioms ShannonC7.posSemidef_allOnes
#print axioms ShannonC7.posSemidef_gram_inner
#print axioms ShannonC7.posSemidef_cos_sub
#print axioms ShannonC7.LovaszCert.diag_nonneg
#print axioms ShannonC7.LovaszCert.W_psd
#print axioms ShannonC7.LovaszCert.card_le
#print axioms ShannonC7.LovaszCert.indepNum_le
#print axioms ShannonC7.shannonCapacity_le_of_cert
#print axioms ShannonC7.shannonCapacity_le_of_orthonormalRep
#print axioms ShannonC7.c5_shannonCapacity_eq_sqrt_five

-- ShannonC7.LovaszC7
#print axioms ShannonC7.oddCycle_upper_lovasz
#print axioms ShannonC7.c7_upper_lovasz
#print axioms ShannonC7.oddCycle_compl_upper_lovasz
#print axioms ShannonC7.c7_compl_upper_lovasz

-- ShannonC7.CubicBounds
#print axioms ShannonC7.cos_pi_div_seven_cubic
#print axioms ShannonC7.lovaszThetaC7_cubic
#print axioms ShannonC7.lovaszThetaC7_gt_three
#print axioms ShannonC7.lovaszThetaC7_lt_of_cubic_pos
#print axioms ShannonC7.lovaszThetaC7_lt_rational
#print axioms ShannonC7.c7_upper_rational
#print axioms ShannonC7.lovaszThetaC7_pow_ne_rat
#print axioms ShannonC7.c7_lovasz_unattainable

-- ShannonC7.Haemers
#print axioms ShannonC7.card_le_rank_of_fitting
#print axioms ShannonC7.indepNum_le_rank_of_fitting
#print axioms ShannonC7.exists_mul_eq_of_rank
#print axioms ShannonC7.rank_kronecker_le
#print axioms ShannonC7.IsFittingMatrix.kronecker
#print axioms ShannonC7.kroneckerPow_isFittingMatrix
#print axioms ShannonC7.rank_kroneckerPow_le
#print axioms ShannonC7.shannonCapacity_le_haemers_rank
#print axioms ShannonC7.haemers_minrank_c7_ge_four

end ShannonC7.Tests
