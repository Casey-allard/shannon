import ShannonC7.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Subadditive
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.OrderClosed

/-!
# Fekete Limit Theorem for Shannon Capacity

This module establishes the structural isomorphisms for strong products (`strongProdComm`,
`strongProdAssoc`, `strongProdPUnitRight`, `strongPowAddEquiv`), proves supermultiplicativity
of `α(G^⊠d)`, and applies Fekete's subadditive lemma (`Mathlib.Analysis.Subadditive`) to prove
that `α(G^⊠d)^(1/d) → shannonCapacity G` as `d → ∞`.
-/

namespace ShannonC7

universe u v w

/-! ## Strong Product Algebraic Isomorphisms -/

/-- Commutativity isomorphism for the strong product. -/
def strongProdComm {V : Type u} {W : Type v} (G : SimpleGraph V) (H : SimpleGraph W) :
    G ⊠ H ≃g H ⊠ G where
  toEquiv := Equiv.prodComm V W
  map_rel_iff' := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, strongProd_adj,
      ne_eq, Prod.mk.injEq]
    tauto

/-- Associativity isomorphism for the strong product. -/
def strongProdAssoc {U : Type u} {V : Type v} {W : Type w}
    (G : SimpleGraph U) (H : SimpleGraph V) (K : SimpleGraph W) :
    (G ⊠ H) ⊠ K ≃g G ⊠ (H ⊠ K) where
  toEquiv := Equiv.prodAssoc U V W
  map_rel_iff' := by
    intro ⟨⟨a₁, b₁⟩, c₁⟩ ⟨⟨a₂, b₂⟩, c₂⟩
    simp only [Equiv.prodAssoc_apply, strongProd_adj, ne_eq, Prod.mk.injEq]
    tauto

/-- Right unit isomorphism for the strong product with the 1-vertex edgeless graph. -/
def strongProdPUnitRight {V : Type u} (G : SimpleGraph V) :
    G ≃g G ⊠ (⊥ : SimpleGraph PUnit.{v + 1}) where
  toEquiv :=
    { toFun := fun x => (x, PUnit.unit)
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, PUnit.unit⟩ => rfl }
  map_rel_iff' := by
    intro a b
    simp only [Equiv.coe_fn_mk, strongProd_adj, SimpleGraph.bot_adj, or_false, and_true,
      ne_eq, Prod.mk.injEq, and_true]
    exact ⟨fun ⟨hne, h⟩ => h.resolve_left hne, fun h => ⟨h.ne, Or.inr h⟩⟩

/-- Additive splitting isomorphism `strongPow G (m + n) ≃g strongPow G m ⊠ strongPow G n`. -/
def strongPowAddEquiv {V : Type*} (G : SimpleGraph V) (m : ℕ) :
    (n : ℕ) → strongPow G (m + n) ≃g strongPow G m ⊠ strongPow G n
  | 0 => strongProdPUnitRight (strongPow G m)
  | n + 1 =>
    (strongProdCongr (.refl) (strongPowAddEquiv G m n)).trans <|
    (strongProdAssoc G (strongPow G m) (strongPow G n)).symm.trans <|
    (strongProdCongr (strongProdComm G (strongPow G m)) (.refl)).trans <|
    strongProdAssoc (strongPow G m) G (strongPow G n)

/-! ## Supermultiplicativity & Fekete's Limit Equivalence -/

theorem strongPow_indepNum_mul_le {V : Type*} [Fintype V] (G : SimpleGraph V) (m n : ℕ) :
    (strongPow G m).indepNum * (strongPow G n).indepNum ≤ (strongPow G (m + n)).indepNum :=
  (indepNum_mul_le (strongPow G m) (strongPow G n)).trans_eq
    (iso_indepNum_eq (strongPowAddEquiv G m n)).symm

theorem strongPowPi_indepNum_mul_le {V : Type*} [Fintype V] (G : SimpleGraph V) (m n : ℕ) :
    (strongPowPi G m).indepNum * (strongPowPi G n).indepNum ≤ (strongPowPi G (m + n)).indepNum := by
  simp_rw [← strongPow_indepNum_eq_pi]
  exact strongPow_indepNum_mul_le G m n

theorem strongPowPi_indepNum_pos {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (d : ℕ) :
    0 < (strongPowPi G d).indepNum := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hind : (strongPowPi G d).IsIndepSet (({fun _ => v₀} : Finset (Fin d → V)) : Set (Fin d → V)) := by
    simp [SimpleGraph.IsIndepSet]
  have h1 : 1 ≤ (strongPowPi G d).indepNum := by
    simpa using hind.card_le_indepNum
  exact Nat.pos_of_ne_zero (by omega)

/-- Fekete's limit theorem for Shannon capacity: for any finite nonempty graph `G`,
the sequence `α(G^⊠d)^(1/d)` converges to `shannonCapacity G = sup_{d > 0} α(G^⊠d)^(1/d)`. -/
theorem shannonCapacity_tendsto {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    Filter.Tendsto
      (fun d : ℕ => ((strongPowPi G d).indepNum : ℝ) ^ (1 / (d : ℝ)))
      Filter.atTop (nhds (shannonCapacity G)) := by
  let α : ℕ → ℝ := fun d => ((strongPowPi G d).indepNum : ℝ)
  let u : ℕ → ℝ := fun d => -Real.log (α d)
  have hpos : ∀ d : ℕ, 0 < α d := fun d =>
    Nat.cast_pos.mpr (strongPowPi_indepNum_pos G d)
  have hu : Subadditive u := by
    intro m n
    have hmul : α m * α n ≤ α (m + n) := by
      dsimp only [α]
      exact_mod_cast strongPowPi_indepNum_mul_le G m n
    have hlog := Real.log_le_log (mul_pos (hpos m) (hpos n)) hmul
    rw [Real.log_mul (hpos m).ne' (hpos n).ne'] at hlog
    show -Real.log (α (m + n)) ≤ -Real.log (α m) + -Real.log (α n)
    linarith
  have hbdd : BddBelow (Set.range fun d : ℕ => u d / (d : ℝ)) := by
    refine ⟨-Real.log (Fintype.card V : ℝ), ?_⟩
    rintro _ ⟨d, rfl⟩
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp only [Nat.cast_zero, div_zero]
      have hnonneg : 0 ≤ Real.log (Fintype.card V : ℝ) := Real.log_natCast_nonneg _
      linarith
    · have hcard : α d ≤ (Fintype.card V : ℝ) ^ d := by
        have hle : (strongPowPi G d).indepNum ≤ (Fintype.card V) ^ d := by
          rw [← strongPow_indepNum_eq_pi]
          exact strongPow_indepNum_le_card_pow G d
        dsimp only [α]
        exact_mod_cast hle
      have hlog := Real.log_le_log (hpos d) hcard
      rw [Real.log_pow] at hlog
      rw [le_div_iff₀ (Nat.cast_pos.mpr hd)]
      show -Real.log (Fintype.card V : ℝ) * (d : ℝ) ≤ -Real.log (α d)
      linarith
  have hlim : Filter.Tendsto (fun d : ℕ => u d / (d : ℝ)) Filter.atTop (nhds hu.lim) :=
    hu.tendsto_lim hbdd
  have hexp :
      Filter.Tendsto (fun d : ℕ => Real.exp (-(u d / (d : ℝ))))
        Filter.atTop (nhds (Real.exp (-hu.lim))) :=
    hlim.neg.rexp
  have h_eq : ∀ d : ℕ, Real.exp (-(u d / (d : ℝ))) = (α d) ^ (1 / (d : ℝ)) := fun d => by
    rw [Real.rpow_def_of_pos (hpos d)]
    congr 1
    simp only [u, div_eq_mul_inv, neg_mul, neg_neg, one_mul]
  have htend :
      Filter.Tendsto (fun d : ℕ => (α d) ^ (1 / (d : ℝ)))
        Filter.atTop (nhds (Real.exp (-hu.lim))) :=
    hexp.congr h_eq
  have hle : Real.exp (-hu.lim) ≤ shannonCapacity G := by
    apply le_of_tendsto htend
    filter_upwards [Filter.eventually_ge_atTop 1] with d hd
    have hmem : (α d) ^ (1 / (d : ℝ)) ∈ shannonSet G := by
      refine ⟨d, hd, ?_⟩
      simp only [α, strongPow_indepNum_eq_pi]
    exact le_csSup (shannonSet_bddAbove G) hmem
  have hge : shannonCapacity G ≤ Real.exp (-hu.lim) := by
    apply csSup_le (shannonSet_nonempty G)
    rintro x ⟨d, hd, rfl⟩
    have hmem : ((strongPow G d).indepNum : ℝ) ^ (1 / (d : ℝ)) = Real.exp (-(u d / (d : ℝ))) := by
      rw [strongPow_indepNum_eq_pi]
      exact (h_eq d).symm
    rw [hmem]
    exact Real.exp_le_exp.mpr (neg_le_neg (hu.lim_le_div hbdd hd.ne'))
  rwa [le_antisymm hle hge] at htend

end ShannonC7
