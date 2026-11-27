import ShannonC7.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.ZMod.Basic

/-!
# The 7-Cycle `C7` and 5-Cycle `C5`

This module defines a fast, kernel-computable 7-cycle `C7 : SimpleGraph (ZMod 7)`,
proves its graph isomorphisms to Mathlib's canonical `SimpleGraph.cycleGraph 7` and
`SimpleGraph.circulantGraph ({1} : Set (ZMod 7))`, establishes the slice double-counting
inequality `2 * (C7 ⊠ H).indepNum ≤ 7 * H.indepNum`, and exposes `C5 := SimpleGraph.cycleGraph 5`.
-/

namespace ShannonC7

/-! ## Computable 7-Cycle `C7` -/

/-- Fast, kernel-computable 7-cycle on `ZMod 7`. -/
def C7 : SimpleGraph (ZMod 7) where
  Adj u v := u - v = 1 ∨ v - u = 1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => by
    rcases h with h | h <;> (rw [sub_self] at h; exact absurd h (by decide))⟩

@[simp]
theorem c7_adj (u v : ZMod 7) : C7.Adj u v ↔ u - v = 1 ∨ v - u = 1 := Iff.rfl

instance instDecidableRelC7 : DecidableRel C7.Adj := fun u v =>
  inferInstanceAs (Decidable (u - v = 1 ∨ v - u = 1))

theorem c7_adj_add_one (i : ZMod 7) : C7.Adj i (i + 1) :=
  Or.inr (add_sub_cancel_left i 1)

/-! ## Canonical Mathlib Isomorphisms -/

/-- Graph isomorphism between computable `C7` and Mathlib's `SimpleGraph.cycleGraph 7`. -/
def c7IsoCycleGraph : C7 ≃g SimpleGraph.cycleGraph 7 where
  toEquiv := (ZMod.finEquiv 7).symm.toEquiv
  map_rel_iff' := by
    intro a b
    revert a b
    decide

/-- Graph isomorphism between computable `C7` and `SimpleGraph.circulantGraph {1}`. -/
def c7IsoCirculant : C7 ≃g SimpleGraph.circulantGraph ({1} : Set (ZMod 7)) where
  toEquiv := Equiv.refl (ZMod 7)
  map_rel_iff' := by
    intro a b
    simp only [Equiv.refl_apply, SimpleGraph.circulantGraph_adj, Set.mem_singleton_iff, c7_adj]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rintro rfl
    rcases h with h | h <;> (rw [sub_self] at h; exact absurd h (by decide))

theorem shannonCapacity_c7_eq_cycleGraph :
    shannonCapacity C7 = shannonCapacity (SimpleGraph.cycleGraph 7) :=
  shannonCapacity_congr c7IsoCycleGraph

/-! ## Slice Double-Counting Inequality -/

/-- For any finite graph `H`, every independent set in `C7 ⊠ H` has at most `(7/2) * α(H)`
vertices, proved by double-counting adjacent pairs of `ZMod 7`-slices. -/
theorem c7_sliceDoubleCount {W : Type*} [Fintype W] (H : SimpleGraph W) :
    2 * (C7 ⊠ H).indepNum ≤ 7 * H.indepNum := by
  classical
  obtain ⟨S, hS_indep, hS_card⟩ := (C7 ⊠ H).exists_isNIndepSet_indepNum
  rw [← hS_card]
  let slice : ZMod 7 → Finset W := fun i => (S.filter fun p => p.1 = i).image Prod.snd
  have mem_slice : ∀ (i : ZMod 7) (w : W), w ∈ slice i ↔ (i, w) ∈ S := by
    intro i w
    simp only [slice, Finset.mem_image, Finset.mem_filter, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨hab, rfl⟩, rfl⟩
      exact hab
    · intro h
      exact ⟨i, w, ⟨h, rfl⟩, rfl⟩
  have card_slice : ∀ i : ZMod 7, (slice i).card = (S.filter fun p => p.1 = i).card := by
    intro i
    apply Finset.card_image_of_injOn
    rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ hb
    simp only [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    exact Prod.ext (h₁.2.trans h₂.2.symm) hb
  have hsum_card : ∑ i : ZMod 7, (slice i).card = S.card := by
    simp_rw [card_slice]
    exact (Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := S) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm
  have hadj_bound : ∀ i : ZMod 7, (slice i).card + (slice (i + 1)).card ≤ H.indepNum := by
    intro i
    have hadj : C7.Adj i (i + 1) := c7_adj_add_one i
    have hne : i ≠ i + 1 := hadj.ne
    have hdisj : Disjoint (slice i) (slice (i + 1)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      have h1 : (i, w) ∈ S := (mem_slice i w).mp hw1
      have h2 : (i + 1, w) ∈ S := (mem_slice (i + 1) w).mp hw2
      have hpair_ne : (i, w) ≠ (i + 1, w) := fun h => hne (congrArg Prod.fst h)
      exact hS_indep h1 h2 hpair_ne ⟨hpair_ne, Or.inr hadj, Or.inl rfl⟩
    have hindep : H.IsIndepSet ((slice i ∪ slice (i + 1) : Finset W) : Set W) := by
      intro u hu v hv huv hHadj
      simp only [Finset.mem_coe, Finset.mem_union] at hu hv
      have hu' : ∃ a : ZMod 7, (a = i ∨ a = i + 1) ∧ (a, u) ∈ S := by
        rcases hu with hu | hu
        · exact ⟨i, Or.inl rfl, (mem_slice i u).mp hu⟩
        · exact ⟨i + 1, Or.inr rfl, (mem_slice (i + 1) u).mp hu⟩
      have hv' : ∃ b : ZMod 7, (b = i ∨ b = i + 1) ∧ (b, v) ∈ S := by
        rcases hv with hv | hv
        · exact ⟨i, Or.inl rfl, (mem_slice i v).mp hv⟩
        · exact ⟨i + 1, Or.inr rfl, (mem_slice (i + 1) v).mp hv⟩
      rcases hu' with ⟨a, ha, hau⟩
      rcases hv' with ⟨b, hb, hbv⟩
      have hab : a = b ∨ C7.Adj a b := by
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr hadj
        · exact Or.inr hadj.symm
        · exact Or.inl rfl
      have hpair_ne : (a, u) ≠ (b, v) := fun h => huv (congrArg Prod.snd h)
      exact hS_indep hau hbv hpair_ne ⟨hpair_ne, hab, Or.inr hHadj⟩
    exact (Finset.card_union_of_disjoint hdisj).symm.trans_le hindep.card_le_indepNum
  have hshift : ∑ i : ZMod 7, (slice (i + 1)).card = ∑ i : ZMod 7, (slice i).card := by
    simpa only [Equiv.coe_addRight] using
      Equiv.sum_comp (Equiv.addRight (1 : ZMod 7)) (fun i => (slice i).card)
  calc 2 * S.card
      = S.card + S.card := two_mul S.card
    _ = (∑ i : ZMod 7, (slice i).card) + ∑ i : ZMod 7, (slice (i + 1)).card := by
        rw [hshift, hsum_card]
    _ = ∑ i : ZMod 7, ((slice i).card + (slice (i + 1)).card) := Finset.sum_add_distrib.symm
    _ ≤ ∑ _i : ZMod 7, H.indepNum := Finset.sum_le_sum fun i _ => hadj_bound i
    _ = 7 * H.indepNum := by
        rw [Finset.sum_const_nat fun _ _ => rfl, Finset.card_univ, ZMod.card]

/-! ## Canonical 5-Cycle `C5` -/

/-- Mathlib's 5-cycle `SimpleGraph.cycleGraph 5` on `Fin 5`. -/
def C5 : SimpleGraph (Fin 5) := SimpleGraph.cycleGraph 5

instance instDecidableRelC5 : DecidableRel C5.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.cycleGraph 5).Adj)

end ShannonC7
