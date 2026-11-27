import ShannonC7.Defs
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Haemers Minrank Bound and Obstruction for `C₇` (`ShannonC7/Haemers.lean`)

This module formalizes Haemers' (1978) matrix-rank upper bound on Shannon capacity over an
arbitrary field `F`: any fitting matrix `M` of `G` satisfies `shannonCapacity G ≤ M.rank`,
proved via Kronecker-product closure and rank submultiplicativity `rank (M ⊗ₖ N) ≤ rank M * rank N`.
It then proves the classic Haemers obstruction for the 7-cycle: every fitting matrix of `C₇`
over any field `F` has rank at least `4` (strictly weaker than `ϑ(C₇) ≈ 3.3177`).
-/

namespace ShannonC7

open scoped Kronecker

universe u v w

/-- A matrix `M` over `F` fits a simple graph `G` if every diagonal entry is nonzero
and every off-diagonal entry between non-adjacent vertices is zero. -/
structure IsFittingMatrix {V : Type u} {F : Type v} [Zero F]
    (G : SimpleGraph V) (M : Matrix V V F) : Prop where
  diag_ne_zero : ∀ i : V, M i i ≠ 0
  nonadj_zero : ∀ i j : V, i ≠ j → ¬ G.Adj i j → M i j = 0

/-- Any independent set in `G` has cardinality bounded above by the rank of any fitting matrix. -/
theorem card_le_rank_of_fitting {V : Type u} [Fintype V] {F : Type v} [Field F]
    {G : SimpleGraph V} {M : Matrix V V F} (hM : IsFittingMatrix G M)
    {s : Finset V} (hs : G.IsIndepSet (s : Set V)) :
    s.card ≤ M.rank := by
  classical
  have hsub :
      M.submatrix (Subtype.val : {x // x ∈ s} → V) Subtype.val =
        Matrix.diagonal (fun i : {x // x ∈ s} => M i.1 i.1) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · have hval : i.1 ≠ j.1 := Subtype.val_injective.ne hij
      simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, hij, ↓reduceIte]
      exact hM.nonadj_zero i.1 j.1 hval (hs i.2 j.2 hval)
  have hcard :
      Fintype.card {i : {x // x ∈ s} // M i.1 i.1 ≠ 0} = s.card := by
    have heq : {i : {x // x ∈ s} // M i.1 i.1 ≠ 0} ≃ {x // x ∈ s} :=
      Equiv.subtypeUnivEquiv (p := fun i : {x // x ∈ s} => M i.1 i.1 ≠ 0)
        (fun i => hM.diag_ne_zero i.1)
    rw [Fintype.card_congr heq, Fintype.card_coe]
  calc s.card
      = Fintype.card {i : {x // x ∈ s} // M i.1 i.1 ≠ 0} := hcard.symm
    _ = (Matrix.diagonal (fun i : {x // x ∈ s} => M i.1 i.1)).rank :=
          (Matrix.rank_diagonal _).symm
    _ = (M.submatrix (Subtype.val : {x // x ∈ s} → V) Subtype.val).rank := by
          rw [hsub]
    _ ≤ M.rank := Matrix.rank_submatrix_le M Subtype.val Subtype.val

/-- The independence number of `G` is bounded above by the rank of any fitting matrix. -/
theorem indepNum_le_rank_of_fitting {V : Type u} [Fintype V] {F : Type v} [Field F]
    {G : SimpleGraph V} {M : Matrix V V F} (hM : IsFittingMatrix G M) :
    G.indepNum ≤ M.rank := by
  obtain ⟨s, hs_indep, hs_card⟩ := G.exists_isNIndepSet_indepNum
  rw [← hs_card]
  exact card_le_rank_of_fitting hM hs_indep

/-- Rank factorization: every matrix `A` over a field `F` factors as `L * R` through `Fin A.rank`. -/
theorem exists_mul_eq_of_rank {m n F : Type*} [Fintype n] [Field F] (A : Matrix m n F) :
    ∃ (L : Matrix m (Fin A.rank) F) (R : Matrix (Fin A.rank) n F), L * R = A := by
  classical
  haveI : Module.Finite F (LinearMap.range A.mulVecLin) :=
    Module.Finite.range A.mulVecLin
  let b : Module.Basis (Fin A.rank) F (LinearMap.range A.mulVecLin) :=
    Module.finBasis F (LinearMap.range A.mulVecLin)
  have hcol : ∀ j : n, A.col j ∈ LinearMap.range A.mulVecLin := fun j => by
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  refine ⟨Matrix.of fun i k => (b k : m → F) i,
          Matrix.of fun k j => b.repr ⟨A.col j, hcol j⟩ k, ?_⟩
  ext i j
  have hrepr :
      ((∑ k : Fin A.rank, (b.repr ⟨A.col j, hcol j⟩ k) • b k : LinearMap.range A.mulVecLin) :
          m → F) i = A i j :=
    congr_fun (congr_arg Subtype.val (b.sum_repr ⟨A.col j, hcol j⟩)) i
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at hrepr
  simpa only [Matrix.mul_apply, Matrix.of_apply, mul_comm] using hrepr

/-- Submultiplicativity of matrix rank under Kronecker products over any field `F`. -/
theorem rank_kronecker_le {l m n p F : Type*} [Fintype m] [Fintype p] [Field F]
    (M : Matrix l m F) (N : Matrix n p F) :
    (M ⊗ₖ N).rank ≤ M.rank * N.rank := by
  obtain ⟨A, B, hM⟩ := exists_mul_eq_of_rank M
  obtain ⟨C, D, hN⟩ := exists_mul_eq_of_rank N
  calc (M ⊗ₖ N).rank
      = ((A * B) ⊗ₖ (C * D)).rank := by rw [hM, hN]
    _ = ((A ⊗ₖ C) * (B ⊗ₖ D)).rank := by rw [Matrix.mul_kronecker_mul]
    _ ≤ (A ⊗ₖ C).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin M.rank × Fin N.rank) := Matrix.rank_le_card_width _
    _ = M.rank * N.rank := by simp

/-- Fitting matrices are closed under Kronecker products with respect to strong graph products. -/
theorem IsFittingMatrix.kronecker {V : Type u} {W : Type w} {F : Type v}
    [MulZeroClass F] [NoZeroDivisors F]
    {G : SimpleGraph V} {H : SimpleGraph W}
    {M : Matrix V V F} {N : Matrix W W F}
    (hM : IsFittingMatrix G M) (hN : IsFittingMatrix H N) :
    IsFittingMatrix (G ⊠ H) (M ⊗ₖ N) where
  diag_ne_zero := fun ⟨i, j⟩ =>
    mul_ne_zero (hM.diag_ne_zero i) (hN.diag_ne_zero j)
  nonadj_zero := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ hne hnadj
    have hnot : ¬ ((u₁, v₁) = (u₂, v₂) ∨ (G ⊠ H).Adj (u₁, v₁) (u₂, v₂)) :=
      not_or.mpr ⟨hne, hnadj⟩
    rw [eq_or_strongProd_adj] at hnot
    simp only [Matrix.kronecker_apply]
    rcases not_and_or.mp hnot with hu | hv
    · rcases not_or.mp hu with ⟨hune, hunadj⟩
      rw [hM.nonadj_zero u₁ u₂ hune hunadj, zero_mul]
    · rcases not_or.mp hv with ⟨hvne, hvnadj⟩
      rw [hN.nonadj_zero v₁ v₂ hvne hvnadj, mul_zero]

/-- Iterated Kronecker power of a square matrix aligned with `StrongPowV V d`. -/
def kroneckerPow {V : Type u} {F : Type v} [Semiring F] (M : Matrix V V F) :
    (d : ℕ) → Matrix (StrongPowV V d) (StrongPowV V d) F
  | 0 => Matrix.of fun _ _ => (1 : F)
  | d + 1 => M ⊗ₖ kroneckerPow M d

/-- Iterated Kronecker powers preserve the fitting-matrix property on `strongPow G d`. -/
theorem kroneckerPow_isFittingMatrix {V : Type u} {F : Type v} [Field F]
    {G : SimpleGraph V} {M : Matrix V V F} (hM : IsFittingMatrix G M) :
    ∀ d : ℕ, IsFittingMatrix (strongPow G d) (kroneckerPow M d)
  | 0 =>
    { diag_ne_zero := fun _ => one_ne_zero
      nonadj_zero := fun ⟨⟩ ⟨⟩ hne _ => absurd rfl hne }
  | d + 1 => hM.kronecker (kroneckerPow_isFittingMatrix hM d)

/-- Rank bound for iterated Kronecker powers: `rank (M^{⊗ d}) ≤ (rank M)^d`. -/
theorem rank_kroneckerPow_le {V : Type u} [Fintype V] {F : Type v} [Field F]
    (M : Matrix V V F) :
    ∀ d : ℕ, (kroneckerPow M d).rank ≤ M.rank ^ d
  | 0 => by
    simpa [StrongPowV] using Matrix.rank_le_card_width (kroneckerPow M 0)
  | d + 1 => by
    change (M ⊗ₖ kroneckerPow M d).rank ≤ M.rank ^ (d + 1)
    calc (M ⊗ₖ kroneckerPow M d).rank
        ≤ M.rank * (kroneckerPow M d).rank := rank_kronecker_le M (kroneckerPow M d)
      _ ≤ M.rank * M.rank ^ d := Nat.mul_le_mul_left _ (rank_kroneckerPow_le M d)
      _ = M.rank ^ (d + 1) := (pow_succ' M.rank d).symm

/-- Haemers' minrank upper bound on Shannon capacity over an arbitrary field `F`. -/
theorem shannonCapacity_le_haemers_rank {V : Type u} [Fintype V] {F : Type v} [Field F]
    {G : SimpleGraph V} {M : Matrix V V F} (hM : IsFittingMatrix G M) :
    shannonCapacity G ≤ (M.rank : ℝ) := by
  refine shannonCapacity_le G (Nat.cast_nonneg _) fun d _ => ?_
  have hle : (strongPow G d).indepNum ≤ M.rank ^ d :=
    (indepNum_le_rank_of_fitting (kroneckerPow_isFittingMatrix hM d)).trans
      (rank_kroneckerPow_le M d)
  exact_mod_cast hle

/-- Haemers obstruction for `C₇`: every fitting matrix of `C₇` over any field `F`
has rank at least `4` (strictly worse than `ϑ(C₇) ≈ 3.3177`). -/
theorem haemers_minrank_c7_ge_four {F : Type v} [Field F]
    (M : Matrix (Fin 7) (Fin 7) F)
    (hM : IsFittingMatrix (SimpleGraph.cycleGraph 7) M) :
    4 ≤ M.rank := by
  let s : Finset (Fin 7 × Fin 7) :=
    {(0, 1), (0, 3), (1, 5), (2, 0), (2, 2), (3, 4), (4, 1), (4, 6), (5, 3), (6, 5)}
  have hs_indep :
      ((SimpleGraph.cycleGraph 7) ⊠ (SimpleGraph.cycleGraph 7)).IsIndepSet
        (s : Set (Fin 7 × Fin 7)) := by
    decide
  have hs_card : s.card = 10 := by decide
  have h10 : 10 ≤ (M ⊗ₖ M).rank := by
    calc 10 = s.card := hs_card.symm
      _ ≤ ((SimpleGraph.cycleGraph 7) ⊠ (SimpleGraph.cycleGraph 7)).indepNum :=
            hs_indep.card_le_indepNum
      _ ≤ (M ⊗ₖ M).rank := indepNum_le_rank_of_fitting (hM.kronecker hM)
  have hsq : 10 ≤ M.rank * M.rank := h10.trans (rank_kronecker_le M M)
  by_contra h
  have h3 : M.rank ≤ 3 := by omega
  have h9 : M.rank * M.rank ≤ 3 * 3 := Nat.mul_le_mul h3 h3
  omega

end ShannonC7
