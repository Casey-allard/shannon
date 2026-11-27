#!/usr/bin/env python3
"""
Deterministic Lean 4 emitter for ShannonC7/ComplementLower.lean from a verified witness JSON.
"""
import json
import sys
from decimal import Decimal, getcontext

getcontext().prec = 80


def fmt_word5(w):
    return f"({w[0]}, {w[1]}, {w[2]}, {w[3]}, {w[4]}, PUnit.unit)"


def fmt_list5(lst, indent="    "):
    lines = [f"{indent}{fmt_word5(w)}" for w in lst]
    return "[\n" + ",\n".join(lines) + "\n  ]"


def emit_lean(witness_path, out_path):
    with open(witness_path) as f:
        w = json.load(f)

    mode = w["mode"]
    assert mode in ("part_dag", "gamma6_pow3")
    I = w["I"]
    P0 = w["P0"]
    P1 = w["P1"]
    O = w["O"]
    H = w["H"]
    V = w["V"]
    assert len(P0) == 1 and len(P1) == 1
    s0 = P0[0] if tuple(P0[0]) in set(map(tuple, I)) else P1[0]
    q0 = P1[0] if s0 == P0[0] else P0[0]
    assert s0 == P0[0], "Expected f0 s0 = s0"

    base_dim = w["base_dim"]
    assert base_dim == 5
    tot_d = w["total_dim"]
    N = int(w["N"])

    # Compute 15-decimal-digit floor of N^(1/tot_d)
    den = 10**15
    # Binary search largest num such that num^tot_d <= den^tot_d * N
    rhs = (den**tot_d) * N
    lo, hi = 2 * den, 3 * den
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid**tot_d <= rhs:
            lo = mid
        else:
            hi = mid - 1
    num = lo
    assert num**tot_d <= (den**tot_d) * N
    assert (num + 1) ** tot_d > (den**tot_d) * N
    assert 17 * (den**4) < num**4
    assert 35 * (den**5) < num**5

    header = f"""import ShannonC7.FrontierLower
import ShannonC7.PortfolioLower

/-!
# Pure-Kernel Complement Lower Bound on `Θ(C₇ᶜ)`

Certifies:
1. Direct `d = 5` witness (`35` words in `(C₇ᶜ)^⊠5`):
   `alpha_c7_compl_pow5_ge_35` and `c7_compl_lower_35 : (35 : ℝ) ^ (1 / 5 : ℝ) ≤ Θ(C₇ᶜ)`.
2. Pure-kernel `PartGadget` construction on `(C₇ᶜ)^⊠5` with profile `{tuple(w["base_profile"])}`
   extended to `d = {tot_d}`, certifying:
   `c7_compl_lower_frontier : ({num} : ℝ) / ({den} : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ`,
   strictly beating Bohman–Holzman (`17^(1/4) ≈ 2.030543`) and `35^(1/5) ≈ 2.036168`.

Zero `sorry`, zero `native_decide`, zero `partial`; axioms strictly `{{propext, Classical.choice, Quot.sound}}`.
-/

namespace ShannonC7

/-! ## 1. Decidable `C₇ᶜ` Closeness Checker & `PartGadget` Constructor -/

private def c7AdjBool (a b : ZMod 7) : Bool :=
  let d := (a.val + 7 - b.val) % 7
  d == 1 || d == 6

private theorem c7Adj_iff_c7AdjBool {{a b : ZMod 7}} :
    c7AdjBool a b = true ↔ C7.Adj a b := by
  revert a b
  decide

private theorem c7AdjBool_false_iff {{a b : ZMod 7}} :
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

private def c7ComplCloseBool : {{d : ℕ}} → StrongPowV (ZMod 7) d → StrongPowV (ZMod 7) d → Bool
  | 0, _, _ => true
  | _ + 1, (a, rx), (b, ry) => !c7AdjBool a b && c7ComplCloseBool rx ry

private theorem c7ComplCloseBool_iff :
    ∀ {{d : ℕ}} {{u v : StrongPowV (ZMod 7) d}},
      c7ComplCloseBool u v = true ↔ u = v ∨ (strongPow C7ᶜ d).Adj u v
  | 0, PUnit.unit, PUnit.unit => by
    simp [c7ComplCloseBool]
  | d + 1, (a, rx), (b, ry) => by
    change _ ↔ (a, rx) = (b, ry) ∨ (C7ᶜ ⊠ strongPow C7ᶜ d).Adj (a, rx) (b, ry)
    rw [eq_or_strongProd_adj]
    simp only [c7ComplCloseBool, Bool.and_eq_true, Bool.not_eq_true']
    rw [c7AdjBool_false_iff, c7ComplCloseBool_iff]

private theorem not_close_of_c7ComplCloseBool_false {{d : ℕ}} {{u v : StrongPowV (ZMod 7) d}}
    (h : c7ComplCloseBool u v = false) :
    ¬ (u = v ∨ (strongPow C7ᶜ d).Adj u v) := by
  intro hc
  have ht := c7ComplCloseBool_iff.mpr hc
  rw [h] at ht
  exact Bool.noConfusion ht

private theorem not_adj_of_c7ComplCloseBool_false {{d : ℕ}} {{u v : StrongPowV (ZMod 7) d}}
    (h : c7ComplCloseBool u v = false) :
    ¬ (strongPow C7ᶜ d).Adj u v :=
  fun hadj => not_close_of_c7ComplCloseBool_false h (Or.inr hadj)

private theorem close_of_c7ComplCloseBool_true {{d : ℕ}} {{u v : StrongPowV (ZMod 7) d}}
    (h : c7ComplCloseBool u v = true) :
    u = v ∨ (strongPow C7ᶜ d).Adj u v :=
  c7ComplCloseBool_iff.mp h

private def pairwiseBool {{α : Type*}} (r : α → α → Bool) : List α → Bool
  | [] => true
  | a :: tl => tl.all (r a) && pairwiseBool r tl

private theorem list_pairwise_of_pairwiseBool {{α : Type*}} {{r : α → α → Bool}} {{P : α → α → Prop}}
    (hr : ∀ a b, r a b = true → P a b) :
    ∀ {{l : List α}}, pairwiseBool r l = true → l.Pairwise P
  | [], _ => List.Pairwise.nil
  | a :: tl, h => by
    simp only [pairwiseBool, Bool.and_eq_true, List.all_eq_true] at h
    exact List.pairwise_cons.mpr ⟨fun b hb => hr a b (h.1 b hb), list_pairwise_of_pairwiseBool hr h.2⟩

private theorem isIndepSet_of_complList {{d : ℕ}} {{l : List (StrongPowV (ZMod 7) d)}}
    (h : pairwiseBool (fun u v => !c7ComplCloseBool u v) l = true) :
    (strongPow C7ᶜ d).IsIndepSet (l.toFinset : Set (StrongPowV (ZMod 7) d)) :=
  isIndepSet_of_pairwise
    (list_pairwise_of_pairwiseBool
      (fun _ _ hc => not_adj_of_c7ComplCloseBool_false (by simpa using hc)) h)

private theorem nodup_of_pairwiseBool {{α : Type*}} [DecidableEq α] {{l : List α}}
    (h : pairwiseBool (fun u v => decide (u ≠ v)) l = true) : l.Nodup :=
  list_pairwise_of_pairwiseBool (fun _ _ hc => of_decide_eq_true hc) h

private def allPairsBool {{α : Type*}} (r : α → α → Bool) (l₁ l₂ : List α) : Bool :=
  l₁.all (fun x => l₂.all (fun y => r x y))

private theorem not_close_of_allPairs {{d : ℕ}} {{l₁ l₂ : List (StrongPowV (ZMod 7) d)}}
    (h : allPairsBool (fun x y => !c7ComplCloseBool x y) l₁ l₂ = true) :
    ∀ x ∈ l₁.toFinset, ∀ y ∈ l₂.toFinset, ¬ (x = y ∨ (strongPow C7ᶜ d).Adj x y) := by
  simp only [allPairsBool, List.all_eq_true, Bool.not_eq_true'] at h
  intro x hx y hy
  exact not_close_of_c7ComplCloseBool_false (h x (List.mem_toFinset.mp hx) y (List.mem_toFinset.mp hy))

private noncomputable def complSingletonPortCore {{d : ℕ}}
    (lI : List (StrongPowV (ZMod 7) d)) (s₀ q₀ : StrongPowV (ZMod 7) d)
    (hIndep : pairwiseBool (fun u v => !c7ComplCloseBool u v) lI = true)
    (hsMem : lI.elem s₀ = true)
    (hqClose : c7ComplCloseBool q₀ s₀ = true)
    (hqPriv : lI.all (fun u => decide (u = s₀) || !c7ComplCloseBool u q₀) = true) :
    PortCore (strongPow C7ᶜ d) where
  I := lI.toFinset
  S := {{s₀}}
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

private noncomputable def complSingletonPartGadget {{d : ℕ}}
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
    {{ O := lO.toFinset
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
        change p ∈ ({{s₀}} : Finset _).image (fun _ => s₀) at hp
        simp only [Finset.mem_image, Finset.mem_singleton, exists_eq_left] at hp
        subst hp
        simp only [List.all_eq_true, Bool.not_eq_true'] at hP0O
        exact not_close_of_c7ComplCloseBool_false (hP0O o (List.mem_toFinset.mp ho))
      not_close_P1_O := by
        intro p hp o ho
        change p ∈ ({{s₀}} : Finset _).image (fun _ => q₀) at hp
        simp only [Finset.mem_image, Finset.mem_singleton, exists_eq_left] at hp
        subst hp
        simp only [List.all_eq_true, Bool.not_eq_true'] at hP1O
        exact not_close_of_c7ComplCloseBool_false (hP1O o (List.mem_toFinset.mp ho))
      not_close_P1_H := by
        intro p hp h hh
        change p ∈ ({{s₀}} : Finset _).image (fun _ => q₀) at hp
        simp only [Finset.mem_image, Finset.mem_singleton, exists_eq_left] at hp
        subst hp
        simp only [List.all_eq_true, Bool.not_eq_true'] at hP1H
        exact not_close_of_c7ComplCloseBool_false (hP1H h (List.mem_toFinset.mp hh))
      not_close_P0_V := by
        intro p hp v hv
        change p ∈ ({{s₀}} : Finset _).image (fun _ => s₀) at hp
        simp only [Finset.mem_image, Finset.mem_singleton, exists_eq_left] at hp
        subst hp
        simp only [List.all_eq_true, Bool.not_eq_true'] at hP0V
        exact not_close_of_c7ComplCloseBool_false (hP0V v (List.mem_toFinset.mp hv)) }}

/-! ## 2. Base 5D Witness (`α((C₇ᶜ)^⊠5) ≥ 35`) & `PartGadget` -/

private def complBaseI : List (StrongPowV (ZMod 7) 5) :=
{fmt_list5(I)}

private def complBaseS0 : StrongPowV (ZMod 7) 5 := {fmt_word5(s0)}
private def complBaseQ0 : StrongPowV (ZMod 7) 5 := {fmt_word5(q0)}

private def complBaseO : List (StrongPowV (ZMod 7) 5) :=
{fmt_list5(O)}

private def complBaseH : List (StrongPowV (ZMod 7) 5) :=
{fmt_list5(H)}

private def complBaseV : List (StrongPowV (ZMod 7) 5) :=
{fmt_list5(V)}

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
  a := {len(I)}
  b := 1
  c := {len(O) + len(H) + len(V)}
  d := {len(O)}
  h := {len(H)}
  v := {len(V)}
  hba := by decide
  hdhv := by decide

private theorem complNode0_profile : complNode0.asymProfile = complProf0 := by
  apply AsymProfile.ext
  · change complBaseI.toFinset.card = {len(I)}
    rw [List.toFinset_card_of_nodup complBaseI_nodup]; rfl
  · change ({{complBaseS0}} : Finset _).card = 1
    exact Finset.card_singleton _
  · change complBaseO.toFinset.card + complBaseH.toFinset.card + complBaseV.toFinset.card = _
    rw [List.toFinset_card_of_nodup complBaseO_nodup,
        List.toFinset_card_of_nodup complBaseH_nodup,
        List.toFinset_card_of_nodup complBaseV_nodup]
    rfl
  · change complBaseO.toFinset.card = {len(O)}
    rw [List.toFinset_card_of_nodup complBaseO_nodup]; rfl
  · change complBaseH.toFinset.card = {len(H)}
    rw [List.toFinset_card_of_nodup complBaseH_nodup]; rfl
  · change complBaseV.toFinset.card = {len(V)}
    rw [List.toFinset_card_of_nodup complBaseV_nodup]; rfl

/-! ## 3. Shared `PartGadget` DAG Construction -/
"""

    dag_lines = []
    dag = w["dag"]
    for idx, node in enumerate(dag):
        if idx == 0:
            assert node["op"] == "base"
            continue
        op = node["op"]
        l_idx = node["left"]
        r_idx = node["right"]
        k1 = dag[l_idx]["k"]
        k2 = dag[r_idx]["k"]
        d1 = k1 * 5
        d2 = k2 * 5
        dt = node["k"] * 5
        if op == "std":
            p_op = "prodAligned"
            g_op = "prodStd"
            th_op = "prodStd_asymProfile"
        elif op == "x1":
            p_op = "prodXupg1"
            g_op = "prodXupg1"
            th_op = "prodXupg1_asymProfile"
        elif op == "x2":
            p_op = "prodXupg2"
            g_op = "prodXupg2"
            th_op = "prodXupg2_asymProfile"
        else:
            raise ValueError(op)
        dag_lines.append(f"private def complProf{idx} : AsymProfile := complProf{l_idx}.{p_op} complProf{r_idx}")
        dag_lines.append(
            f"private noncomputable def complNode{idx} : PartGadget (strongPow C7ᶜ {dt}) :=\n"
            f"  (complNode{l_idx}.{g_op} complNode{r_idx}).mapIso (strongPowAddEquiv C7ᶜ {d1} {d2}).symm"
        )
        if l_idx == r_idx:
            dag_lines.append(
                f"private theorem complNode{idx}_profile : complNode{idx}.asymProfile = complProf{idx} := by\n"
                f"  rw [complNode{idx}, PartGadget.mapIso_asymProfile, PartGadget.{th_op}, complNode{l_idx}_profile]; rfl"
            )
        else:
            dag_lines.append(
                f"private theorem complNode{idx}_profile : complNode{idx}.asymProfile = complProf{idx} := by\n"
                f"  rw [complNode{idx}, PartGadget.mapIso_asymProfile, PartGadget.{th_op},\n"
                f"    complNode{l_idx}_profile, complNode{r_idx}_profile]; rfl"
            )

    root_idx = w["root"]
    if mode == "part_dag":
        tail = f"""
/-! ## 4. Certified Pure-Kernel Complement Frontier Bound (`d = {tot_d}`) -/

def complFrontierCard : ℕ := {N}

theorem complFrontierCard_eq : complProf{root_idx}.a = complFrontierCard := rfl

theorem complFrontierCard_le_indepNum :
    complFrontierCard ≤ (strongPowPi (SimpleGraph.cycleGraph 7)ᶜ {tot_d}).indepNum := by
  have h1 : complNode{root_idx}.asymProfile.a ≤ (strongPow C7ᶜ {tot_d}).indepNum :=
    complNode{root_idx}.card_le_indepNum
  rw [complNode{root_idx}_profile, complFrontierCard_eq] at h1
  have h2 : (strongPow C7ᶜ {tot_d}).indepNum =
      (strongPowPi (SimpleGraph.cycleGraph 7)ᶜ {tot_d}).indepNum := by
    rw [iso_indepNum_eq (strongPowCongr (isoCompl c7IsoCycleGraph) {tot_d}), strongPow_indepNum_eq_pi]
  omega
"""
    else:
        triples = w["gamma6_triples"]
        d1 = w["k1"] * 5
        triples_str = ",\n    ".join(f"({a}, {b}, {c})" for a, b, c in triples)
        tail = f"""
/-! ## 4. Certified Pure-Kernel Complement Frontier Bound (`Γ₆^⊠3` at `d = {tot_d}`) -/

private def complGamma6Triples : List Gamma6Triple :=
  [ {triples_str} ]

private theorem complGamma6Triples_indep : gamma6TripleListIndepBool complGamma6Triples = true := rfl

def complFrontierCard : ℕ := {N}

theorem complFrontierCard_eq :
    gamma6TripleListWeight complProf{root_idx} complProf{root_idx} complProf{root_idx} complGamma6Triples =
      complFrontierCard := rfl

theorem complFrontierCard_le_indepNum :
    complFrontierCard ≤ (strongPowPi (SimpleGraph.cycleGraph 7)ᶜ {tot_d}).indepNum := by
  have h1 := gamma6Pow3_weight_le_indepNum complNode{root_idx} complNode{root_idx} complNode{root_idx}
    complGamma6Triples complGamma6Triples_indep
  rw [complNode{root_idx}_profile, complFrontierCard_eq] at h1
  have e12 : strongPow C7ᶜ {d1} ⊠ strongPow C7ᶜ {d1} ≃g strongPow C7ᶜ {2 * d1} :=
    (strongPowAddEquiv C7ᶜ {d1} {d1}).symm
  have e123 : (strongPow C7ᶜ {d1} ⊠ strongPow C7ᶜ {d1}) ⊠ strongPow C7ᶜ {d1} ≃g
      strongPow C7ᶜ {tot_d} :=
    (strongPowCongr_left C7ᶜ e12 {d1}).trans (strongPowAddEquiv C7ᶜ {2 * d1} {d1}).symm
  have h2 : (((strongPow C7ᶜ {d1} ⊠ strongPow C7ᶜ {d1}) ⊠ strongPow C7ᶜ {d1}).indepNum) =
      (strongPowPi (SimpleGraph.cycleGraph 7)ᶜ {tot_d}).indepNum := by
    rw [iso_indepNum_eq e123, iso_indepNum_eq (strongPowCongr (isoCompl c7IsoCycleGraph) {tot_d}),
      strongPow_indepNum_eq_pi]
  omega
"""

    thresh = "set_option exponentiation.threshold 4096 in\n" if tot_d > 256 else ""
    footer = f"""
def c7_compl_lower_num : ℕ := {num}
def c7_compl_lower_den : ℕ := {den}

theorem c7_compl_lower_den_pos : 0 < c7_compl_lower_den := by decide

{thresh}theorem compl_frontier_pow_le :
    c7_compl_lower_num ^ {tot_d} ≤ c7_compl_lower_den ^ {tot_d} * complFrontierCard :=
  nat_pow_le_of_ble rfl

/-- Certified pure-kernel complement frontier lower bound on `Θ(C₇ᶜ)`:
`{num} / {den} ≤ shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ`. -/
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
"""

    with open(out_path, "w") as f:
        f.write(header + "\n".join(dag_lines) + "\n" + tail + footer)
    print(f"[emitted] {out_path} (mode={mode}, d={tot_d}, num/den={num}/{den})")


if __name__ == "__main__":
    w_path = sys.argv[1] if len(sys.argv) > 1 else "/home/callard/shannon/search/lower/compl_witnesses/compl_c7_d5_partgadget.json"
    o_path = sys.argv[2] if len(sys.argv) > 2 else "/mnt/nvme2tb/shannon_struct_scratch/compl/ComplementLower.lean"
    emit_lean(w_path, o_path)
