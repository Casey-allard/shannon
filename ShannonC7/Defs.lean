import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Positivity

/-!
# Core Definitions for Shannon Capacity

This module defines the strong graph product (`⊠`), iterated strong powers in both
nested tuple form (`strongPow`) and textbook function form (`strongPowPi` on `Fin d → V`),
the canonical graph isomorphism between them (`strongPowEquivPi`), isomorphism invariance
of independence number, supermultiplicativity on strong products, and the Shannon capacity
`shannonCapacity G := sSup (shannonSet G)`.
-/

namespace ShannonC7

universe u v

/-! ## Strong Graph Product -/

/-- The strong product `G ⊠ H` of two simple graphs. Two distinct pairs `(u₁, v₁)` and
`(u₂, v₂)` are adjacent iff in each coordinate the vertices are equal or adjacent. -/
def strongProd {V : Type u} {W : Type v} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V × W) where
  Adj x y := x ≠ y ∧ (x.1 = y.1 ∨ G.Adj x.1 y.1) ∧ (x.2 = y.2 ∨ H.Adj x.2 y.2)
  symm := ⟨by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ ⟨hne, h1, h2⟩
    exact ⟨hne.symm, h1.imp Eq.symm SimpleGraph.Adj.symm, h2.imp Eq.symm SimpleGraph.Adj.symm⟩⟩
  loopless := ⟨by
    rintro ⟨u, v⟩ ⟨hne, _, _⟩
    exact hne rfl⟩

infixl:70 " ⊠ " => strongProd

@[simp]
theorem strongProd_adj {V : Type u} {W : Type v} (G : SimpleGraph V) (H : SimpleGraph W)
    (x y : V × W) :
    (G ⊠ H).Adj x y ↔
      x ≠ y ∧ (x.1 = y.1 ∨ G.Adj x.1 y.1) ∧ (x.2 = y.2 ∨ H.Adj x.2 y.2) :=
  Iff.rfl

theorem eq_or_strongProd_adj {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} {x y : V × W} :
    x = y ∨ (G ⊠ H).Adj x y ↔
      (x.1 = y.1 ∨ G.Adj x.1 y.1) ∧ (x.2 = y.2 ∨ H.Adj x.2 y.2) := by
  constructor
  · rintro (rfl | h)
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact h.2
  · rintro ⟨h1, h2⟩
    by_cases hxy : x = y
    · exact Or.inl hxy
    · exact Or.inr ⟨hxy, h1, h2⟩

instance instDecidableRelStrongProd {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G ⊠ H).Adj :=
  fun x y => inferInstanceAs (Decidable
    (x ≠ y ∧ (x.1 = y.1 ∨ G.Adj x.1 y.1) ∧ (x.2 = y.2 ∨ H.Adj x.2 y.2)))

/-! ## Nested Strong Powers -/

/-- Universe-preserving nested tuple vertex type for `strongPow`. -/
def StrongPowV (V : Type u) : ℕ → Type u
  | 0 => PUnit.{u + 1}
  | d + 1 => V × StrongPowV V d

instance instFintypeStrongPowV {V : Type u} [Fintype V] :
    ∀ d, Fintype (StrongPowV V d)
  | 0 => PUnit.fintype
  | d + 1 =>
    letI : Fintype (StrongPowV V d) := instFintypeStrongPowV d
    instFintypeProd V (StrongPowV V d)

instance instDecidableEqStrongPowV {V : Type u} [DecidableEq V] :
    ∀ d, DecidableEq (StrongPowV V d)
  | 0 => inferInstanceAs (DecidableEq PUnit.{u + 1})
  | d + 1 =>
    letI : DecidableEq (StrongPowV V d) := instDecidableEqStrongPowV d
    instDecidableEqProd

instance instNonemptyStrongPowV {V : Type u} [Nonempty V] :
    ∀ d, Nonempty (StrongPowV V d)
  | 0 => ⟨PUnit.unit⟩
  | d + 1 =>
    letI : Nonempty (StrongPowV V d) := instNonemptyStrongPowV d
    inferInstanceAs (Nonempty (V × StrongPowV V d))

theorem card_strongPowV {V : Type u} [Fintype V] (d : ℕ) :
    Fintype.card (StrongPowV V d) = (Fintype.card V) ^ d := by
  induction d with
  | zero => exact Fintype.card_punit
  | succ d ih =>
    change Fintype.card (V × StrongPowV V d) = _
    rw [Fintype.card_prod, ih, pow_succ']

/-- The `d`-fold iterated strong power of `G` on `StrongPowV V d`. -/
def strongPow {V : Type u} (G : SimpleGraph V) : (d : ℕ) → SimpleGraph (StrongPowV V d)
  | 0 => ⊥
  | d + 1 => G ⊠ strongPow G d

instance instDecidableRelStrongPow {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ d, DecidableRel (strongPow G d).Adj
  | 0 => fun _ _ => isFalse id
  | d + 1 =>
    letI : DecidableEq (StrongPowV V d) := instDecidableEqStrongPowV d
    letI : DecidableRel (strongPow G d).Adj := instDecidableRelStrongPow G d
    instDecidableRelStrongProd G (strongPow G d)

/-! ## Textbook `Fin d → V` Strong Power -/

/-- Textbook `d`-fold strong power on `Fin d → V`. -/
def strongPowPi {V : Type u} (G : SimpleGraph V) (d : ℕ) : SimpleGraph (Fin d → V) where
  Adj x y := x ≠ y ∧ ∀ i : Fin d, x i = y i ∨ G.Adj (x i) (y i)
  symm := ⟨by
    intro x y ⟨hne, h⟩
    exact ⟨hne.symm, fun i => (h i).imp Eq.symm SimpleGraph.Adj.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

@[simp]
theorem strongPowPi_adj {V : Type u} (G : SimpleGraph V) (d : ℕ) (x y : Fin d → V) :
    (strongPowPi G d).Adj x y ↔ x ≠ y ∧ ∀ i : Fin d, x i = y i ∨ G.Adj (x i) (y i) :=
  Iff.rfl

theorem eq_or_strongPowPi_adj {V : Type u} {G : SimpleGraph V} {d : ℕ} {x y : Fin d → V} :
    x = y ∨ (strongPowPi G d).Adj x y ↔ ∀ i : Fin d, x i = y i ∨ G.Adj (x i) (y i) := by
  constructor
  · rintro (rfl | ⟨_, h⟩) i
    · exact Or.inl rfl
    · exact h i
  · intro h
    by_cases hxy : x = y
    · exact Or.inl hxy
    · exact Or.inr ⟨hxy, h⟩

instance instDecidableRelStrongPowPi {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    DecidableRel (strongPowPi G d).Adj := fun x y => by
  change Decidable (x ≠ y ∧ ∀ i : Fin d, x i = y i ∨ G.Adj (x i) (y i))
  exact instDecidableAnd

/-- Canonical graph isomorphism between the nested strong power `strongPow G d`
and the textbook function strong power `strongPowPi G d`. -/
def strongPowEquivPi {V : Type u} (G : SimpleGraph V) :
    (d : ℕ) → strongPow G d ≃g strongPowPi G d
  | 0 =>
    { toEquiv :=
        { toFun := fun _ => Fin.elim0
          invFun := fun _ => PUnit.unit
          left_inv := fun _ => rfl
          right_inv := fun f => funext fun i => i.elim0 }
      map_rel_iff' := by
        intro a b
        simp only [strongPow, SimpleGraph.bot_adj, strongPowPi_adj, iff_false, not_and]
        intro hne
        exact absurd (Subsingleton.elim _ _) hne }
  | d + 1 =>
    let ih := strongPowEquivPi G d
    let e : StrongPowV V (d + 1) ≃ (Fin (d + 1) → V) :=
      (Equiv.prodCongr (Equiv.refl V) ih.toEquiv).trans
        (Fin.consEquiv (fun _ : Fin (d + 1) => V))
    { toEquiv := e
      map_rel_iff' := by
        intro ⟨a, u⟩ ⟨b, v⟩
        change (strongPowPi G (d + 1)).Adj (e (a, u)) (e (b, v)) ↔
          (G ⊠ strongPow G d).Adj (a, u) (b, v)
        rw [strongPowPi_adj, strongProd_adj, e.injective.ne_iff]
        refine and_congr_right fun _ => ?_
        have he : ∀ (x : V) (w : StrongPowV V d), e (x, w) = Fin.cons x (ih w) :=
          fun _ _ => rfl
        rw [he a u, he b v, Fin.forall_fin_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        refine and_congr_right fun _ => ?_
        rw [← eq_or_strongPowPi_adj, ih.injective.eq_iff, ih.map_adj_iff] }

/-! ## Isomorphism Invariance & Structural Lemmas -/

theorem isIndepSet_map_iso {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {s : Finset V} (hs : G.IsIndepSet (s : Set V)) :
    H.IsIndepSet ((s.map e.toEquiv.toEmbedding : Finset W) : Set W) := by
  intro x hx y hy hxy hadj
  simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe] at hx hy
  rcases hx with ⟨a, ha, rfl⟩
  rcases hy with ⟨b, hb, rfl⟩
  exact hs ha hb (fun hab => hxy (congrArg e hab)) (e.map_adj_iff.mp hadj)

theorem iso_indepNum_eq {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.indepNum = H.indepNum := by
  unfold SimpleGraph.indepNum
  congr 1
  ext n
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.map e.toEquiv.toEmbedding, isIndepSet_map_iso e hs.isIndepSet, ?_⟩
    rw [Finset.card_map, hs.card_eq]
  · rintro ⟨t, ht⟩
    refine ⟨t.map e.symm.toEquiv.toEmbedding, isIndepSet_map_iso e.symm ht.isIndepSet, ?_⟩
    rw [Finset.card_map, ht.card_eq]

theorem strongPow_indepNum_eq_pi {V : Type u} (G : SimpleGraph V) (d : ℕ) :
    (strongPow G d).indepNum = (strongPowPi G d).indepNum :=
  iso_indepNum_eq (strongPowEquivPi G d)

/-- Congruence of the strong product under graph isomorphisms. -/
def strongProdCongr {V₁ V₂ W₁ W₂ : Type*}
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (eG : G₁ ≃g G₂) (eH : H₁ ≃g H₂) :
    G₁ ⊠ H₁ ≃g G₂ ⊠ H₂ where
  toEquiv := Equiv.prodCongr eG.toEquiv eH.toEquiv
  map_rel_iff' := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    simp only [Equiv.prodCongr_apply, Prod.map_apply, strongProd_adj,
      ne_eq, Prod.mk.injEq, RelIso.coe_fn_toEquiv, eG.injective.eq_iff, eH.injective.eq_iff,
      eG.map_adj_iff, eH.map_adj_iff]

/-- Congruence of nested strong powers under a graph isomorphism. -/
def strongPowCongr {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    (d : ℕ) → strongPow G d ≃g strongPow H d
  | 0 =>
    { toEquiv := Equiv.punitEquivPUnit
      map_rel_iff' := by simp [strongPow] }
  | d + 1 => strongProdCongr e (strongPowCongr e d)

theorem indepNum_le_card {V : Type u} [Fintype V] (G : SimpleGraph V) :
    G.indepNum ≤ Fintype.card V := by
  obtain ⟨s, _, hs_card⟩ := G.exists_isNIndepSet_indepNum
  rw [← hs_card]
  exact Finset.card_le_univ s

theorem strongPow_indepNum_le_card_pow {V : Type u} [Fintype V] (G : SimpleGraph V) (d : ℕ) :
    (strongPow G d).indepNum ≤ (Fintype.card V) ^ d := by
  calc (strongPow G d).indepNum
      ≤ Fintype.card (StrongPowV V d) := indepNum_le_card (strongPow G d)
    _ = (Fintype.card V) ^ d := card_strongPowV d

theorem indepNum_mul_le {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    G.indepNum * H.indepNum ≤ (G ⊠ H).indepNum := by
  obtain ⟨s, hs_indep, hs_card⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨t, ht_indep, ht_card⟩ := H.exists_isNIndepSet_indepNum
  have hprod : (G ⊠ H).IsIndepSet ((s ×ˢ t : Finset (V × W)) : Set (V × W)) := by
    rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ hne ⟨_, hG, hH⟩
    simp only [Finset.mem_coe, Finset.mem_product] at h₁ h₂
    rcases hG with rfl | hGadj
    · have hb : b₁ ≠ b₂ := fun h => hne (by rw [h])
      rcases hH with rfl | hHadj
      · exact hb rfl
      · exact ht_indep h₁.2 h₂.2 hb hHadj
    · exact hs_indep h₁.1 h₂.1 hGadj.ne hGadj
  calc G.indepNum * H.indepNum
      = s.card * t.card := by rw [hs_card, ht_card]
    _ = (s ×ˢ t).card := (Finset.card_product s t).symm
    _ ≤ (G ⊠ H).indepNum := hprod.card_le_indepNum

/-! ## Shannon Capacity -/

set_option linter.unusedFintypeInType false in
/-- The set of `d`-th roots `α(G^⊠d)^(1/d)` for strictly positive exponents `d > 0`. -/
def shannonSet {V : Type*} [Fintype V] (G : SimpleGraph V) : Set ℝ :=
  {x : ℝ | ∃ d : ℕ, 0 < d ∧ x = ((strongPow G d).indepNum : ℝ) ^ (1 / (d : ℝ))}

set_option linter.unusedFintypeInType false in
/-- The Shannon capacity `Θ(G) = sup_{d > 0} α(G^⊠d)^(1/d)`. -/
noncomputable def shannonCapacity {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sSup (shannonSet G)

theorem shannonSet_eq_pi {V : Type*} [Fintype V] (G : SimpleGraph V) :
    shannonSet G =
      {x : ℝ | ∃ d : ℕ, 0 < d ∧ x = ((strongPowPi G d).indepNum : ℝ) ^ (1 / (d : ℝ))} := by
  ext x
  simp only [shannonSet, Set.mem_setOf_eq, strongPow_indepNum_eq_pi]

theorem shannonSet_nonempty {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (shannonSet G).Nonempty :=
  ⟨((strongPow G 1).indepNum : ℝ) ^ (1 / ((1 : ℕ) : ℝ)), 1, Nat.one_pos, rfl⟩

theorem shannonSet_bddAbove {V : Type*} [Fintype V] (G : SimpleGraph V) :
    BddAbove (shannonSet G) := by
  refine ⟨(Fintype.card V : ℝ), ?_⟩
  rintro x ⟨d, hd, rfl⟩
  rw [one_div,
    Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_pos.mpr hd),
    Real.rpow_natCast]
  exact_mod_cast strongPow_indepNum_le_card_pow G d

theorem shannonCapacity_nonneg {V : Type*} [Fintype V] (G : SimpleGraph V) :
    0 ≤ shannonCapacity G :=
  (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans
    (le_csSup (shannonSet_bddAbove G) ⟨1, Nat.one_pos, rfl⟩)

set_option linter.unusedFintypeInType false in
theorem shannonCapacity_congr {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    shannonCapacity G = shannonCapacity H := by
  have hset : shannonSet G = shannonSet H := by
    ext x
    simp only [shannonSet, Set.mem_setOf_eq]
    constructor <;> rintro ⟨d, hd, rfl⟩ <;>
      refine ⟨d, hd, ?_⟩ <;>
      rw [iso_indepNum_eq (strongPowCongr e d)]
  rw [shannonCapacity, shannonCapacity, hset]

theorem le_shannonCapacity_of_indepSet {V : Type*} [Fintype V] (G : SimpleGraph V)
    {d : ℕ} (hd : 0 < d) {s : Finset (StrongPowV V d)}
    (hs : (strongPow G d).IsIndepSet (s : Set (StrongPowV V d))) :
    (s.card : ℝ) ^ (1 / (d : ℝ)) ≤ shannonCapacity G := by
  have hcard : (s.card : ℝ) ≤ ((strongPow G d).indepNum : ℝ) :=
    Nat.cast_le.mpr hs.card_le_indepNum
  refine le_csSup_of_le (shannonSet_bddAbove G) ⟨d, hd, rfl⟩ ?_
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hcard (by positivity)

theorem le_shannonCapacity_of_indepSet_pi {V : Type*} [Fintype V] (G : SimpleGraph V)
    {d : ℕ} (hd : 0 < d) {s : Finset (Fin d → V)}
    (hs : (strongPowPi G d).IsIndepSet (s : Set (Fin d → V))) :
    (s.card : ℝ) ^ (1 / (d : ℝ)) ≤ shannonCapacity G := by
  have hcard : (s.card : ℝ) ≤ ((strongPow G d).indepNum : ℝ) := by
    rw [strongPow_indepNum_eq_pi]
    exact Nat.cast_le.mpr hs.card_le_indepNum
  refine le_csSup_of_le (shannonSet_bddAbove G) ⟨d, hd, rfl⟩ ?_
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hcard (by positivity)

theorem shannonCapacity_le {V : Type*} [Fintype V] (G : SimpleGraph V) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ d : ℕ, 0 < d → ((strongPow G d).indepNum : ℝ) ≤ B ^ d) :
    shannonCapacity G ≤ B := by
  apply csSup_le (shannonSet_nonempty G)
  rintro x ⟨d, hd, rfl⟩
  rw [one_div,
    Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) hB (Nat.cast_pos.mpr hd),
    Real.rpow_natCast]
  exact h d hd

end ShannonC7
