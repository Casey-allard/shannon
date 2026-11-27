import ShannonC7.CycleC7
import ShannonC7.Defs
import ShannonC7.Fekete

/-!
# Core Unit Tests & Contract Conformance (`ShannonC7/Tests/CoreTests.lean`)

Validates:
1. Verbatim type-signature conformance with `PROJECT.md` §4.1.
2. Pure-kernel `by decide` computability of `C7.Adj`, `C5.Adj`, `(strongPow C7 2).Adj`,
   and `(strongPowPi C7 2).Adj`.
3. Edge cases: empty graph (`Empty`), `d = 0` strong power (`indepNum = 1`), and
   `c7_sliceDoubleCount` instantiations.
4. Explicit `#print axioms` checks for every public theorem in `Defs`, `Fekete`, and `CycleC7`.
-/

namespace ShannonC7.Tests

open ShannonC7

/-! ## 1. Verbatim Interface Contract Conformance (`PROJECT.md` §4.1) -/

section ContractChecks

example {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) :=
  strongProd G H

example {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) :=
  G ⊠ H

example (V : Type*) : ℕ → Type _ := StrongPowV V

example {V : Type*} (G : SimpleGraph V) : (d : ℕ) → SimpleGraph (StrongPowV V d) :=
  strongPow G

example {V : Type*} (G : SimpleGraph V) (d : ℕ) : SimpleGraph (Fin d → V) :=
  strongPowPi G d

example {V : Type*} (G : SimpleGraph V) (d : ℕ) : strongPow G d ≃g strongPowPi G d :=
  strongPowEquivPi G d

example {V : Type*} [Fintype V] (G : SimpleGraph V) : Set ℝ :=
  shannonSet G

noncomputable example {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  shannonCapacity G

example {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    shannonCapacity G = shannonCapacity H :=
  shannonCapacity_congr e

example {V : Type*} [Fintype V] (G : SimpleGraph V)
    {d : ℕ} (hd : 0 < d) {s : Finset (StrongPowV V d)}
    (hs : (strongPow G d).IsIndepSet (s : Set (StrongPowV V d))) :
    (s.card : ℝ) ^ (1 / (d : ℝ)) ≤ shannonCapacity G :=
  le_shannonCapacity_of_indepSet G hd hs

example {V : Type*} [Fintype V] (G : SimpleGraph V) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ d : ℕ, 0 < d → ((strongPow G d).indepNum : ℝ) ≤ B ^ d) :
    shannonCapacity G ≤ B :=
  shannonCapacity_le G hB h

example {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    Filter.Tendsto
      (fun d : ℕ => ((strongPowPi G d).indepNum : ℝ) ^ (1 / (d : ℝ)))
      Filter.atTop (nhds (shannonCapacity G)) :=
  shannonCapacity_tendsto G

example : SimpleGraph (ZMod 7) := C7
example : DecidableRel C7.Adj := inferInstance
example : C7 ≃g SimpleGraph.cycleGraph 7 := c7IsoCycleGraph
example : C7 ≃g SimpleGraph.circulantGraph ({1} : Set (ZMod 7)) := c7IsoCirculant

example {W : Type*} [Fintype W] (H : SimpleGraph W) :
    2 * (C7 ⊠ H).indepNum ≤ 7 * H.indepNum :=
  c7_sliceDoubleCount H

example : SimpleGraph (Fin 5) := C5
example : DecidableRel C5.Adj := inferInstance

end ContractChecks

/-! ## 2. Pure-Kernel `by decide` Computability Tests -/

example : C7.Adj 0 1 := by decide
example : C7.Adj 0 6 := by decide
example : C7.Adj 6 0 := by decide
example : ¬ C7.Adj 0 0 := by decide
example : ¬ C7.Adj 0 2 := by decide
example : ¬ C7.Adj 0 3 := by decide
example : ¬ C7.Adj 0 4 := by decide

example : C5.Adj 0 1 := by decide
example : C5.Adj 0 4 := by decide
example : ¬ C5.Adj 0 0 := by decide
example : ¬ C5.Adj 0 2 := by decide
example : ¬ C5.Adj 0 3 := by decide

example : (C7 ⊠ C5).Adj (0, 0) (1, 4) := by decide
example : (C7 ⊠ C5).Adj (0, 0) (0, 1) := by decide
example : ¬ (C7 ⊠ C5).Adj (0, 0) (0, 0) := by decide
example : ¬ (C7 ⊠ C5).Adj (0, 0) (2, 1) := by decide

example : (strongPow C7 2).Adj (0, (0, PUnit.unit)) (1, (6, PUnit.unit)) := by decide
example : (strongPow C7 2).Adj (0, (0, PUnit.unit)) (0, (1, PUnit.unit)) := by decide
example : ¬ (strongPow C7 2).Adj (0, (0, PUnit.unit)) (0, (0, PUnit.unit)) := by decide
example : ¬ (strongPow C7 2).Adj (0, (0, PUnit.unit)) (2, (1, PUnit.unit)) := by decide

private def pt00 : Fin 2 → ZMod 7 := fun _ => 0
private def pt16 : Fin 2 → ZMod 7 := fun i => if i = 0 then 1 else 6
private def pt21 : Fin 2 → ZMod 7 := fun i => if i = 0 then 2 else 1

example : (strongPowPi C7 2).Adj pt00 pt16 := by decide
example : ¬ (strongPowPi C7 2).Adj pt00 pt00 := by decide
example : ¬ (strongPowPi C7 2).Adj pt00 pt21 := by decide

/-! ## 3. Edge-Case & Functional Sanity Checks -/

theorem emptyGraph_shannonCapacity_eq_zero :
    shannonCapacity (⊥ : SimpleGraph Empty) = 0 := by
  apply le_antisymm
  · refine shannonCapacity_le (⊥ : SimpleGraph Empty) le_rfl fun d hd => ?_
    have hcard : (strongPow (⊥ : SimpleGraph Empty) d).indepNum ≤ 0 := by
      have h := strongPow_indepNum_le_card_pow (⊥ : SimpleGraph Empty) d
      simpa [Fintype.card_empty, zero_pow hd.ne'] using h
    have hzero : (strongPow (⊥ : SimpleGraph Empty) d).indepNum = 0 := Nat.eq_zero_of_le_zero hcard
    rw [hzero, Nat.cast_zero, zero_pow hd.ne']
  · exact shannonCapacity_nonneg (⊥ : SimpleGraph Empty)

theorem strongPow_c7_zero_indepNum : (strongPow C7 0).indepNum = 1 := by
  apply Nat.le_antisymm
  · have h := strongPow_indepNum_le_card_pow C7 0
    simpa using h
  · let s : Finset (StrongPowV (ZMod 7) 0) := {PUnit.unit}
    have hind : (strongPow C7 0).IsIndepSet (s : Set (StrongPowV (ZMod 7) 0)) := by
      intro _ _ _ _ _ hadj
      exact hadj
    have hcard : s.card ≤ (strongPow C7 0).indepNum := hind.card_le_indepNum
    exact hcard

theorem strongPowPi_c7_zero_indepNum : (strongPowPi C7 0).indepNum = 1 := by
  rw [← strongPow_indepNum_eq_pi]
  exact strongPow_c7_zero_indepNum

example : (shannonSet (⊥ : SimpleGraph Empty)).Nonempty :=
  shannonSet_nonempty (⊥ : SimpleGraph Empty)

example : BddAbove (shannonSet (⊥ : SimpleGraph Empty)) :=
  shannonSet_bddAbove (⊥ : SimpleGraph Empty)

example : 2 * (C7 ⊠ C7).indepNum ≤ 7 * C7.indepNum :=
  c7_sliceDoubleCount C7

example : 2 * (C7 ⊠ (⊥ : SimpleGraph Empty)).indepNum ≤ 7 * (⊥ : SimpleGraph Empty).indepNum :=
  c7_sliceDoubleCount (⊥ : SimpleGraph Empty)

example : shannonCapacity C7 = shannonCapacity (SimpleGraph.cycleGraph 7) :=
  shannonCapacity_c7_eq_cycleGraph

example :
    Filter.Tendsto
      (fun d : ℕ => ((strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ^ (1 / (d : ℝ)))
      Filter.atTop (nhds (shannonCapacity (SimpleGraph.cycleGraph 7))) :=
  shannonCapacity_tendsto (SimpleGraph.cycleGraph 7)

/-! ## 4. Explicit `#print axioms` Checks on All Public Theorems -/

-- ShannonC7.Defs
#print axioms ShannonC7.strongProd_adj
#print axioms ShannonC7.eq_or_strongProd_adj
#print axioms ShannonC7.card_strongPowV
#print axioms ShannonC7.strongPowPi_adj
#print axioms ShannonC7.eq_or_strongPowPi_adj
#print axioms ShannonC7.isIndepSet_map_iso
#print axioms ShannonC7.iso_indepNum_eq
#print axioms ShannonC7.strongPow_indepNum_eq_pi
#print axioms ShannonC7.indepNum_le_card
#print axioms ShannonC7.strongPow_indepNum_le_card_pow
#print axioms ShannonC7.indepNum_mul_le
#print axioms ShannonC7.shannonSet_eq_pi
#print axioms ShannonC7.shannonSet_nonempty
#print axioms ShannonC7.shannonSet_bddAbove
#print axioms ShannonC7.shannonCapacity_nonneg
#print axioms ShannonC7.shannonCapacity_congr
#print axioms ShannonC7.le_shannonCapacity_of_indepSet
#print axioms ShannonC7.le_shannonCapacity_of_indepSet_pi
#print axioms ShannonC7.shannonCapacity_le

-- ShannonC7.Fekete
#print axioms ShannonC7.strongPow_indepNum_mul_le
#print axioms ShannonC7.strongPowPi_indepNum_mul_le
#print axioms ShannonC7.strongPowPi_indepNum_pos
#print axioms ShannonC7.shannonCapacity_tendsto

-- ShannonC7.CycleC7
#print axioms ShannonC7.c7_adj
#print axioms ShannonC7.c7_adj_add_one
#print axioms ShannonC7.shannonCapacity_c7_eq_cycleGraph
#print axioms ShannonC7.c7_sliceDoubleCount

end ShannonC7.Tests
