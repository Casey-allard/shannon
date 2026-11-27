import ShannonC7.FrontierLower
import ShannonC7.PortfolioLower

/-!
# Pure-Kernel Complement Lower Bound on `Θ(C₇ᶜ)`

Certifies:
1. Direct `d = 5` witness (`35` words in `(C₇ᶜ)^⊠5`):
   `alpha_c7_compl_pow5_ge_35` and `c7_compl_lower_35 : (35 : ℝ) ^ (1 / 5 : ℝ) ≤ Θ(C₇ᶜ)`.
2. Pure-kernel `PartGadget` construction on `(C₇ᶜ)^⊠5` with profile `(35, 1, 35, 23, 7, 5)`
   extended to `d = 140`, certifying:
   `c7_compl_lower_frontier : (2036581869953041 : ℝ) / (1000000000000000 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ`,
   strictly beating Bohman–Holzman (`17^(1/4) ≈ 2.030543`) and `35^(1/5) ≈ 2.036168`.

Zero `sorry`, zero `native_decide`, zero `partial`; axioms strictly `{propext, Classical.choice, Quot.sound}`.
-/

namespace ShannonC7

/-! ## 1. Decidable `C₇ᶜ` Closeness Checker & `PartGadget` Constructor -/

private def c7AdjBool (a b : ZMod 7) : Bool :=
  let d := (a.val + 7 - b.val) % 7
  d == 1 || d == 6

private theorem c7Adj_iff_c7AdjBool {a b : ZMod 7} :
    c7AdjBool a b = true ↔ C7.Adj a b := by
  revert a b
  decide

private theorem c7AdjBool_false_iff {a b : ZMod 7} :
    c7AdjBool a b = false ↔ (a = b ∨ C7ᶜ.Adj a b) := by
  have h : c7AdjBool a b = false ↔ ¬ C7.Adj a b := by
    rw [← Bool.not_eq_true, c7Adj_iff_c7AdjBool]
  rw [h]
  constructor
  · intro hna
    by_cases hab : a = b
    · exact Or.inl hab
    · exact Or.inr ⟨hab, hna⟩
  · rintro (rfl | ⟨_, hna⟩)
    · exact fun hadj => hadj.ne rfl
    · exact hna

private def c7ComplCloseBool : {d : ℕ} → StrongPowV (ZMod 7) d → StrongPowV (ZMod 7) d → Bool
  | 0, _, _ => true
  | _ + 1, (a, rx), (b, ry) => !c7AdjBool a b && c7ComplCloseBool rx ry

private theorem c7ComplCloseBool_iff :
    ∀ {d : ℕ} {u v : StrongPowV (ZMod 7) d},
      c7ComplCloseBool u v = true ↔ u = v ∨ (strongPow C7ᶜ d).Adj u v
  | 0, PUnit.unit, PUnit.unit => by
    simp [c7ComplCloseBool]
  | d + 1, (a, rx), (b, ry) => by
    change _ ↔ (a, rx) = (b, ry) ∨ (C7ᶜ ⊠ strongPow C7ᶜ d).Adj (a, rx) (b, ry)
    rw [eq_or_strongProd_adj]
    simp only [c7ComplCloseBool, Bool.and_eq_true, Bool.not_eq_true']
    rw [c7AdjBool_false_iff, c7ComplCloseBool_iff]

private theorem not_close_of_c7ComplCloseBool_false {d : ℕ} {u v : StrongPowV (ZMod 7) d}
    (h : c7ComplCloseBool u v = false) :
    ¬ (u = v ∨ (strongPow C7ᶜ d).Adj u v) := by
  intro hc
  have ht := c7ComplCloseBool_iff.mpr hc
  rw [h] at ht
  exact Bool.noConfusion ht

private theorem not_adj_of_c7ComplCloseBool_false {d : ℕ} {u v : StrongPowV (ZMod 7) d}
    (h : c7ComplCloseBool u v = false) :
    ¬ (strongPow C7ᶜ d).Adj u v :=
  fun hadj => not_close_of_c7ComplCloseBool_false h (Or.inr hadj)

private theorem close_of_c7ComplCloseBool_true {d : ℕ} {u v : StrongPowV (ZMod 7) d}
    (h : c7ComplCloseBool u v = true) :
    u = v ∨ (strongPow C7ᶜ d).Adj u v :=
  c7ComplCloseBool_iff.mp h

private def pairwiseBool {α : Type*} (r : α → α → Bool) : List α → Bool
  | [] => true
  | a :: tl => tl.all (r a) && pairwiseBool r tl

private theorem list_pairwise_of_pairwiseBool {α : Type*} {r : α → α → Bool} {P : α → α → Prop}
    (hr : ∀ a b, r a b = true → P a b) :
    ∀ {l : List α}, pairwiseBool r l = true → l.Pairwise P
  | [], _ => List.Pairwise.nil
  | a :: tl, h => by
    simp only [pairwiseBool, Bool.and_eq_true, List.all_eq_true] at h
    exact List.pairwise_cons.mpr ⟨fun b hb => hr a b (h.1 b hb), list_pairwise_of_pairwiseBool hr h.2⟩

private theorem isIndepSet_of_complList {d : ℕ} {l : List (StrongPowV (ZMod 7) d)}
    (h : pairwiseBool (fun u v => !c7ComplCloseBool u v) l = true) :
    (strongPow C7ᶜ d).IsIndepSet (l.toFinset : Set (StrongPowV (ZMod 7) d)) :=
  isIndepSet_of_pairwise
    (list_pairwise_of_pairwiseBool
      (fun _ _ hc => not_adj_of_c7ComplCloseBool_false (by simpa using hc)) h)

private theorem nodup_of_pairwiseBool {α : Type*} [DecidableEq α] {l : List α}
    (h : pairwiseBool (fun u v => decide (u ≠ v)) l = true) : l.Nodup :=
  list_pairwise_of_pairwiseBool (fun _ _ hc => of_decide_eq_true hc) h

private def allPairsBool {α : Type*} (r : α → α → Bool) (l₁ l₂ : List α) : Bool :=
  l₁.all (fun x => l₂.all (fun y => r x y))

private theorem not_close_of_allPairs {d : ℕ} {l₁ l₂ : List (StrongPowV (ZMod 7) d)}
    (h : allPairsBool (fun x y => !c7ComplCloseBool x y) l₁ l₂ = true) :
    ∀ x ∈ l₁.toFinset, ∀ y ∈ l₂.toFinset, ¬ (x = y ∨ (strongPow C7ᶜ d).Adj x y) := by
  simp only [allPairsBool, List.all_eq_true, Bool.not_eq_true'] at h
  intro x hx y hy
  exact not_close_of_c7ComplCloseBool_false (h x (List.mem_toFinset.mp hx) y (List.mem_toFinset.mp hy))

private noncomputable def complSingletonPortCore {d : ℕ}
    (lI : List (StrongPowV (ZMod 7) d)) (s₀ q₀ : StrongPowV (ZMod 7) d)
    (hIndep : pairwiseBool (fun u v => !c7ComplCloseBool u v) lI = true)
    (hsMem : lI.elem s₀ = true)
    (hqClose : c7ComplCloseBool q₀ s₀ = true)
    (hqPriv : lI.all (fun u => decide (u = s₀) || !c7ComplCloseBool u q₀) = true) :
    PortCore (strongPow C7ᶜ d) where
  I := lI.toFinset
  S := {s₀}
  f0 := fun _ => s₀
  f1 := fun _ => q₀
  indep_I := isIndepSet_of_complList hIndep
  S_sub_I := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact List.mem_toFinset.mpr (List.mem_of_elem_eq_true hsMem)
  priv0 := by
    intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    refine ⟨Or.inl rfl, fun u hu hcl => ?_⟩
    by_contra hne
    rcases hcl with rfl | hadj
    · exact hne rfl
    · exact (isIndepSet_of_complList hIndep) hu
        (List.mem_toFinset.mpr (List.mem_of_elem_eq_true hsMem)) hne hadj
  priv1 := by
    intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    refine ⟨close_of_c7ComplCloseBool_true hqClose, fun u hu hcl => ?_⟩
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hqPriv
    rcases hqPriv u (List.mem_toFinset.mp hu) with rfl | hnc
    · rfl
    · exact absurd hcl (not_close_of_c7ComplCloseBool_false hnc)
  indep_P0 := by
    intro x hx y hy hne
    rcases hx with ⟨a, _, rfl⟩
    rcases hy with ⟨b, _, rfl⟩
    exact absurd rfl hne
  indep_P1 := by
    intro x hx y hy hne
    rcases hx with ⟨a, _, rfl⟩
    rcases hy with ⟨b, _, rfl⟩
    exact absurd rfl hne
  self_mem := by
    intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    exact Or.inl rfl

private noncomputable def complSingletonPartGadget {d : ℕ}
    (lI lO lH lV : List (StrongPowV (ZMod 7) d)) (s₀ q₀ : StrongPowV (ZMod 7) d)
    (hI : pairwiseBool (fun u v => !c7ComplCloseBool u v) lI = true)
    (hsMem : lI.elem s₀ = true)
    (hqClose : c7ComplCloseBool q₀ s₀ = true)
    (hqPriv : lI.all (fun u => decide (u = s₀) || !c7ComplCloseBool u q₀) = true)
    (hO : pairwiseBool (fun u v => !c7ComplCloseBool u v) lO = true)
    (hH : pairwiseBool (fun u v => !c7ComplCloseBool u v) lH = true)
    (hV : pairwiseBool (fun u v => !c7ComplCloseBool u v) lV = true)
    (hOH : allPairsBool (fun x y => !c7ComplCloseBool x y) lO lH = true)
    (hOV : allPairsBool (fun x y => !c7ComplCloseBool x y) lO lV = true)
    (hHV : allPairsBool (fun x y => !c7ComplCloseBool x y) lH lV = true)
    (hP0O : lO.all (fun o => !c7ComplCloseBool s₀ o) = true)
    (hP1O : lO.all (fun o => !c7ComplCloseBool q₀ o) = true)
    (hP1H : lH.all (fun h => !c7ComplCloseBool q₀ h) = true)
    (hP0V : lV.all (fun v => !c7ComplCloseBool s₀ v) = true) :
    PartGadget (strongPow C7ᶜ d) where
  core := complSingletonPortCore lI s₀ q₀ hI hsMem hqClose hqPriv
  aux :=
    { O := lO.toFinset
      H := lH.toFinset
      V := lV.toFinset
      indep_O := isIndepSet_of_complList hO
      indep_H := isIndepSet_of_complList hH
      indep_V := isIndepSet_of_complList hV
      not_close_OH := not_close_of_allPairs hOH
      not_close_OV := not_close_of_allPairs hOV
      not_close_HV := not_close_of_allPairs hHV
      not_close_P0_O := by
        intro p hp o ho
        change p ∈ ({s₀} : Finset _).image (fun _ => s₀) at hp
        simp only [Finset.mem_image, Finset.mem_singleton, exists_eq_left] at hp
        subst hp
        simp only [List.all_eq_true, Bool.not_eq_true'] at hP0O
        exact not_close_of_c7ComplCloseBool_false (hP0O o (List.mem_toFinset.mp ho))
      not_close_P1_O := by
        intro p hp o ho
        change p ∈ ({s₀} : Finset _).image (fun _ => q₀) at hp
        simp only [Finset.mem_image, Finset.mem_singleton, exists_eq_left] at hp
        subst hp
        simp only [List.all_eq_true, Bool.not_eq_true'] at hP1O
        exact not_close_of_c7ComplCloseBool_false (hP1O o (List.mem_toFinset.mp ho))
      not_close_P1_H := by
        intro p hp h hh
        change p ∈ ({s₀} : Finset _).image (fun _ => q₀) at hp
        simp only [Finset.mem_image, Finset.mem_singleton, exists_eq_left] at hp
        subst hp
        simp only [List.all_eq_true, Bool.not_eq_true'] at hP1H
        exact not_close_of_c7ComplCloseBool_false (hP1H h (List.mem_toFinset.mp hh))
      not_close_P0_V := by
        intro p hp v hv
        change p ∈ ({s₀} : Finset _).image (fun _ => s₀) at hp
        simp only [Finset.mem_image, Finset.mem_singleton, exists_eq_left] at hp
        subst hp
        simp only [List.all_eq_true, Bool.not_eq_true'] at hP0V
        exact not_close_of_c7ComplCloseBool_false (hP0V v (List.mem_toFinset.mp hv)) }

/-! ## 2. Base 5D Witness (`α((C₇ᶜ)^⊠5) ≥ 35`) & `PartGadget` -/

private def complBaseI : List (StrongPowV (ZMod 7) 5) :=
[
    (0, 0, 0, 0, 0, PUnit.unit),
    (1, 2, 3, 1, 2, PUnit.unit),
    (2, 4, 6, 2, 4, PUnit.unit),
    (3, 6, 2, 3, 6, PUnit.unit),
    (4, 1, 5, 4, 1, PUnit.unit),
    (5, 3, 1, 5, 3, PUnit.unit),
    (6, 5, 4, 6, 5, PUnit.unit),
    (0, 0, 0, 1, 2, PUnit.unit),
    (1, 2, 3, 2, 4, PUnit.unit),
    (2, 4, 6, 3, 6, PUnit.unit),
    (3, 6, 2, 4, 1, PUnit.unit),
    (4, 1, 5, 5, 3, PUnit.unit),
    (5, 3, 1, 6, 5, PUnit.unit),
    (6, 5, 4, 0, 0, PUnit.unit),
    (0, 1, 0, 4, 2, PUnit.unit),
    (1, 3, 3, 5, 4, PUnit.unit),
    (2, 5, 6, 6, 6, PUnit.unit),
    (3, 0, 2, 0, 1, PUnit.unit),
    (4, 2, 5, 1, 3, PUnit.unit),
    (5, 4, 1, 2, 5, PUnit.unit),
    (6, 6, 4, 3, 0, PUnit.unit),
    (0, 4, 6, 3, 0, PUnit.unit),
    (1, 6, 2, 4, 2, PUnit.unit),
    (2, 1, 5, 5, 4, PUnit.unit),
    (3, 3, 1, 6, 6, PUnit.unit),
    (4, 5, 4, 0, 1, PUnit.unit),
    (5, 0, 0, 1, 3, PUnit.unit),
    (6, 2, 3, 2, 5, PUnit.unit),
    (0, 5, 6, 0, 2, PUnit.unit),
    (1, 0, 2, 1, 4, PUnit.unit),
    (2, 2, 5, 0, 6, PUnit.unit),
    (3, 4, 1, 1, 1, PUnit.unit),
    (4, 6, 4, 2, 3, PUnit.unit),
    (5, 1, 0, 3, 5, PUnit.unit),
    (6, 3, 3, 4, 0, PUnit.unit)
  ]

private def complBaseS0 : StrongPowV (ZMod 7) 5 := (1, 2, 3, 2, 4, PUnit.unit)
private def complBaseQ0 : StrongPowV (ZMod 7) 5 := (3, 4, 1, 0, 6, PUnit.unit)

private def complBaseO : List (StrongPowV (ZMod 7) 5) :=
[
    (3, 5, 6, 1, 1, PUnit.unit),
    (2, 3, 2, 2, 3, PUnit.unit),
    (1, 1, 5, 3, 5, PUnit.unit),
    (0, 6, 1, 4, 0, PUnit.unit),
    (4, 0, 3, 1, 1, PUnit.unit),
    (3, 5, 6, 2, 3, PUnit.unit),
    (2, 3, 2, 3, 5, PUnit.unit),
    (1, 1, 5, 4, 0, PUnit.unit),
    (6, 4, 4, 6, 4, PUnit.unit),
    (5, 1, 0, 3, 6, PUnit.unit),
    (2, 2, 2, 6, 5, PUnit.unit),
    (0, 5, 1, 1, 2, PUnit.unit),
    (6, 3, 4, 2, 4, PUnit.unit),
    (4, 3, 2, 3, 6, PUnit.unit),
    (2, 6, 1, 5, 3, PUnit.unit),
    (1, 4, 4, 6, 5, PUnit.unit),
    (0, 2, 0, 0, 0, PUnit.unit),
    (6, 0, 3, 1, 2, PUnit.unit),
    (4, 2, 2, 0, 1, PUnit.unit),
    (3, 0, 5, 6, 3, PUnit.unit),
    (2, 5, 1, 0, 5, PUnit.unit),
    (1, 3, 4, 1, 0, PUnit.unit),
    (0, 1, 0, 2, 2, PUnit.unit)
  ]

private def complBaseH : List (StrongPowV (ZMod 7) 5) :=
[
    (5, 2, 0, 6, 4, PUnit.unit),
    (4, 0, 3, 0, 6, PUnit.unit),
    (5, 2, 0, 0, 6, PUnit.unit),
    (4, 6, 3, 4, 1, PUnit.unit),
    (1, 0, 5, 0, 0, PUnit.unit),
    (5, 5, 6, 2, 4, PUnit.unit),
    (5, 4, 6, 6, 6, PUnit.unit)
  ]

private def complBaseV : List (StrongPowV (ZMod 7) 5) :=
[
    (6, 4, 4, 5, 2, PUnit.unit),
    (0, 6, 1, 5, 2, PUnit.unit),
    (3, 4, 6, 5, 3, PUnit.unit),
    (3, 1, 5, 4, 1, PUnit.unit),
    (6, 6, 3, 3, 4, PUnit.unit)
  ]

private theorem complBaseI_nodup : complBaseI.Nodup := nodup_of_pairwiseBool rfl
private theorem complBaseO_nodup : complBaseO.Nodup := nodup_of_pairwiseBool rfl
private theorem complBaseH_nodup : complBaseH.Nodup := nodup_of_pairwiseBool rfl
private theorem complBaseV_nodup : complBaseV.Nodup := nodup_of_pairwiseBool rfl

theorem alpha_c7_compl_pow5_ge_35 :
    35 ≤ (strongPowPi (SimpleGraph.cycleGraph 7)ᶜ 5).indepNum := by
  have h1 : complBaseI.length ≤ (strongPow C7ᶜ 5).indepNum :=
    length_le_indepNum_of_list complBaseI_nodup
      (list_pairwise_of_pairwiseBool (r := fun u v => !c7ComplCloseBool u v)
        (fun _ _ hc => not_adj_of_c7ComplCloseBool_false (by simpa using hc)) rfl)
  have h2 : (strongPow C7ᶜ 5).indepNum =
      (strongPowPi (SimpleGraph.cycleGraph 7)ᶜ 5).indepNum := by
    rw [iso_indepNum_eq (strongPowCongr (isoCompl c7IsoCycleGraph) 5), strongPow_indepNum_eq_pi]
  have hlen : complBaseI.length = 35 := rfl
  rw [← h2, ← hlen]
  exact h1

theorem c7_compl_lower_35 :
    (35 : ℝ) ^ (1 / 5 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ := by
  calc (35 : ℝ) ^ (1 / 5 : ℝ)
      ≤ ((strongPowPi (SimpleGraph.cycleGraph 7)ᶜ 5).indepNum : ℝ) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast alpha_c7_compl_pow5_ge_35) (by positivity)
    _ ≤ shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ := by
        rw [← strongPow_indepNum_eq_pi]
        exact le_csSup (shannonSet_bddAbove _) ⟨5, by decide, rfl⟩

private noncomputable def complNode0 : PartGadget (strongPow C7ᶜ 5) :=
  complSingletonPartGadget complBaseI complBaseO complBaseH complBaseV complBaseS0 complBaseQ0
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

private def complProf0 : AsymProfile where
  a := 35
  b := 1
  c := 35
  d := 23
  h := 7
  v := 5
  hba := by decide
  hdhv := by decide

private theorem complNode0_profile : complNode0.asymProfile = complProf0 := by
  apply AsymProfile.ext
  · change complBaseI.toFinset.card = 35
    rw [List.toFinset_card_of_nodup complBaseI_nodup]; rfl
  · change ({complBaseS0} : Finset _).card = 1
    exact Finset.card_singleton _
  · change complBaseO.toFinset.card + complBaseH.toFinset.card + complBaseV.toFinset.card = _
    rw [List.toFinset_card_of_nodup complBaseO_nodup,
        List.toFinset_card_of_nodup complBaseH_nodup,
        List.toFinset_card_of_nodup complBaseV_nodup]
    rfl
  · change complBaseO.toFinset.card = 23
    rw [List.toFinset_card_of_nodup complBaseO_nodup]; rfl
  · change complBaseH.toFinset.card = 7
    rw [List.toFinset_card_of_nodup complBaseH_nodup]; rfl
  · change complBaseV.toFinset.card = 5
    rw [List.toFinset_card_of_nodup complBaseV_nodup]; rfl

/-! ## 3. Shared `PartGadget` DAG Construction -/
private def complProf1 : AsymProfile := complProf0.prodAligned complProf0
private noncomputable def complNode1 : PartGadget (strongPow C7ᶜ 10) :=
  (complNode0.prodStd complNode0).mapIso (strongPowAddEquiv C7ᶜ 5 5).symm
private theorem complNode1_profile : complNode1.asymProfile = complProf1 := by
  rw [complNode1, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile, complNode0_profile]; rfl
private def complProf2 : AsymProfile := complProf0.prodAligned complProf1
private noncomputable def complNode2 : PartGadget (strongPow C7ᶜ 15) :=
  (complNode0.prodStd complNode1).mapIso (strongPowAddEquiv C7ᶜ 5 10).symm
private theorem complNode2_profile : complNode2.asymProfile = complProf2 := by
  rw [complNode2, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    complNode0_profile, complNode1_profile]; rfl
private def complProf3 : AsymProfile := complProf2.prodAligned complProf2
private noncomputable def complNode3 : PartGadget (strongPow C7ᶜ 30) :=
  (complNode2.prodStd complNode2).mapIso (strongPowAddEquiv C7ᶜ 15 15).symm
private theorem complNode3_profile : complNode3.asymProfile = complProf3 := by
  rw [complNode3, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile, complNode2_profile]; rfl
private def complProf4 : AsymProfile := complProf1.prodAligned complProf1
private noncomputable def complNode4 : PartGadget (strongPow C7ᶜ 20) :=
  (complNode1.prodStd complNode1).mapIso (strongPowAddEquiv C7ᶜ 10 10).symm
private theorem complNode4_profile : complNode4.asymProfile = complProf4 := by
  rw [complNode4, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile, complNode1_profile]; rfl
private def complProf5 : AsymProfile := complProf4.prodAligned complProf4
private noncomputable def complNode5 : PartGadget (strongPow C7ᶜ 40) :=
  (complNode4.prodStd complNode4).mapIso (strongPowAddEquiv C7ᶜ 20 20).symm
private theorem complNode5_profile : complNode5.asymProfile = complProf5 := by
  rw [complNode5, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile, complNode4_profile]; rfl
private def complProf6 : AsymProfile := complProf3.prodXupg1 complProf5
private noncomputable def complNode6 : PartGadget (strongPow C7ᶜ 70) :=
  (complNode3.prodXupg1 complNode5).mapIso (strongPowAddEquiv C7ᶜ 30 40).symm
private theorem complNode6_profile : complNode6.asymProfile = complProf6 := by
  rw [complNode6, PartGadget.mapIso_asymProfile, PartGadget.prodXupg1_asymProfile,
    complNode3_profile, complNode5_profile]; rfl
private def complProf7 : AsymProfile := complProf6.prodXupg1 complProf6
private noncomputable def complNode7 : PartGadget (strongPow C7ᶜ 140) :=
  (complNode6.prodXupg1 complNode6).mapIso (strongPowAddEquiv C7ᶜ 70 70).symm
private theorem complNode7_profile : complNode7.asymProfile = complProf7 := by
  rw [complNode7, PartGadget.mapIso_asymProfile, PartGadget.prodXupg1_asymProfile, complNode6_profile]; rfl

/-! ## 4. Certified Pure-Kernel Complement Frontier Bound (`d = 140`) -/

def complFrontierCard : ℕ := 17630403766597908028404660108047961464583300

theorem complFrontierCard_eq : complProf7.a = complFrontierCard := rfl

theorem complFrontierCard_le_indepNum :
    complFrontierCard ≤ (strongPowPi (SimpleGraph.cycleGraph 7)ᶜ 140).indepNum := by
  have h1 : complNode7.asymProfile.a ≤ (strongPow C7ᶜ 140).indepNum :=
    complNode7.card_le_indepNum
  rw [complNode7_profile, complFrontierCard_eq] at h1
  have h2 : (strongPow C7ᶜ 140).indepNum =
      (strongPowPi (SimpleGraph.cycleGraph 7)ᶜ 140).indepNum := by
    rw [iso_indepNum_eq (strongPowCongr (isoCompl c7IsoCycleGraph) 140), strongPow_indepNum_eq_pi]
  omega

def c7_compl_lower_num : ℕ := 2036581869953041
def c7_compl_lower_den : ℕ := 1000000000000000

theorem c7_compl_lower_den_pos : 0 < c7_compl_lower_den := by decide

theorem compl_frontier_pow_le :
    c7_compl_lower_num ^ 140 ≤ c7_compl_lower_den ^ 140 * complFrontierCard :=
  nat_pow_le_of_ble rfl

/-- Certified pure-kernel complement frontier lower bound on `Θ(C₇ᶜ)`:
`2036581869953041 / 1000000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ`. -/
theorem c7_compl_lower_frontier :
    (c7_compl_lower_num : ℝ) / (c7_compl_lower_den : ℝ) ≤
      shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ :=
  le_shannonCapacity_of_nat_pow_pi (by decide) c7_compl_lower_den_pos
    complFrontierCard_le_indepNum compl_frontier_pow_le

/-- Strictly beats Bohman–Holzman (`17^(1/4)`). -/
theorem c7_compl_lower_gt_bh :
    (17 : ℝ) ^ (1 / 4 : ℝ) < shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ := by
  have hden_pos : (0 : ℝ) < (c7_compl_lower_den : ℝ) := by exact_mod_cast c7_compl_lower_den_pos
  have hq : (17 : ℝ) ^ (1 / 4 : ℝ) < (c7_compl_lower_num : ℝ) / (c7_compl_lower_den : ℝ) := by
    have hpow : ((17 : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) < ((c7_compl_lower_num : ℝ) / (c7_compl_lower_den : ℝ)) ^ (4 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num)]
      norm_num
      rw [div_pow, lt_div_iff₀ (pow_pos hden_pos 4)]
      exact_mod_cast (by decide : 17 * c7_compl_lower_den ^ 4 < c7_compl_lower_num ^ 4)
    exact (Real.rpow_lt_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 4)).mp hpow
  exact lt_of_lt_of_le hq c7_compl_lower_frontier

/-- Strictly beats the direct `d = 5` `35^(1/5)` bound. -/
theorem c7_compl_lower_gt_35 :
    (35 : ℝ) ^ (1 / 5 : ℝ) < shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ := by
  have hden_pos : (0 : ℝ) < (c7_compl_lower_den : ℝ) := by exact_mod_cast c7_compl_lower_den_pos
  have hq : (35 : ℝ) ^ (1 / 5 : ℝ) < (c7_compl_lower_num : ℝ) / (c7_compl_lower_den : ℝ) := by
    have hpow : ((35 : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℝ) < ((c7_compl_lower_num : ℝ) / (c7_compl_lower_den : ℝ)) ^ (5 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num)]
      norm_num
      rw [div_pow, lt_div_iff₀ (pow_pos hden_pos 5)]
      exact_mod_cast (by decide : 35 * c7_compl_lower_den ^ 5 < c7_compl_lower_num ^ 5)
    exact (Real.rpow_lt_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 5)).mp hpow
  exact lt_of_lt_of_le hq c7_compl_lower_frontier

end ShannonC7
