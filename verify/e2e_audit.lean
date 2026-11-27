/-
  Opaque-Box End-to-End Audit for the Shannon Capacity of C₇ Formalization.
  Imports ONLY `ShannonC7.Main` and minimal non-deprecated Mathlib v4.32.2 leaf modules.
  NEVER imports `Mathlib` wholesale or any internal `ShannonC7.*` module.
  Zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`, pure kernel verification only.
-/
import ShannonC7.Main
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Subadditive
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace E2EAudit

/-! ## 1. Independent Textbook Definitions on `Fin 7` and `Fin d → Fin 7` -/

/-- Independent textbook 7-cycle on `Fin 7`: adjacent iff cyclic distance is 1. -/
def c7Textbook : SimpleGraph (Fin 7) where
  Adj u v := (u.val + 1) % 7 = v.val ∨ (v.val + 1) % 7 = u.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => by rcases h with h | h <;> omega⟩

instance : DecidableRel c7Textbook.Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val + 1) % 7 = v.val ∨ (v.val + 1) % 7 = u.val))

/-- Our raw modular 7-cycle equals Mathlib's `SimpleGraph.cycleGraph 7`. -/
theorem c7Textbook_eq_cycleGraph7 : c7Textbook = SimpleGraph.cycleGraph 7 := by
  ext u v
  revert u v
  decide

/-- Independent textbook d-fold strong power on `Fin d → V`. -/
def strongPowTextbook {V : Type*} (G : SimpleGraph V) (d : ℕ) : SimpleGraph (Fin d → V) where
  Adj x y := x ≠ y ∧ ∀ i : Fin d, x i = y i ∨ G.Adj (x i) (y i)
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, fun i => (h i).imp Eq.symm (fun hadj => G.symm.symm _ _ hadj)⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- Independent textbook d-fold strong power of `C₇` on `Fin d → Fin 7`. -/
def strongPowC7Textbook (d : ℕ) : SimpleGraph (Fin d → Fin 7) :=
  strongPowTextbook c7Textbook d

/-- Canonical graph isomorphism between our independent textbook `C₇^⊠d`
    and the project's public `ShannonC7.strongPowPi (SimpleGraph.cycleGraph 7) d`. -/
def strongPowTextbookIsoPi (d : ℕ) :
    strongPowC7Textbook d ≃g ShannonC7.strongPowPi (SimpleGraph.cycleGraph 7) d where
  toEquiv := Equiv.refl (Fin d → Fin 7)
  map_rel_iff' := by
    intro x y
    simp only [Equiv.refl_apply, strongPowC7Textbook, strongPowTextbook,
      ShannonC7.strongPowPi, c7Textbook_eq_cycleGraph7]
    try exact and_congr_right fun _ => forall_congr' fun _ => or_comm

private lemma iso_indepNum_le {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    G.indepNum ≤ H.indepNum := by
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have himg : H.IsIndepSet ((s.map f.toEquiv.toEmbedding : Finset W) : Set W) := by
    intro x hx y hy hxy hadj
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (congrArg f.toEquiv.toEmbedding h)
    exact hs.isIndepSet (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
      (f.map_rel_iff.mp hadj)
  have hcard : (s.map f.toEquiv.toEmbedding).card ≤ H.indepNum := himg.card_le_indepNum
  rw [Finset.card_map, hs.card_eq] at hcard
  exact hcard

/-- Self-contained proof that graph isomorphism preserves `SimpleGraph.indepNum`. -/
theorem iso_indepNum_eq {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.indepNum = H.indepNum :=
  le_antisymm (iso_indepNum_le e) (iso_indepNum_le e.symm)

theorem textbook_indepNum_eq_project (d : ℕ) :
    (strongPowC7Textbook d).indepNum =
      (ShannonC7.strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum :=
  iso_indepNum_eq (strongPowTextbookIsoPi d)

/-- Independent textbook set of d-th roots `{α(C₇^⊠d)^(1/d) | d ≥ 1}` (`d = 0` strictly excluded). -/
def shannonSetTextbook : Set ℝ :=
  {x : ℝ | ∃ d : ℕ, 0 < d ∧ x = ((strongPowC7Textbook d).indepNum : ℝ) ^ (1 / (d : ℝ))}

/-- Independent textbook Shannon capacity `Θ(C₇) = sup_{d ≥ 1} α(C₇^⊠d)^(1/d)`. -/
noncomputable def shannonCapacityTextbook : ℝ :=
  sSup shannonSetTextbook

/-! ## 2. Independent Fekete Proof & Opaque-Box Equivalence (`textbook_eq_project`) -/

private lemma one_le_indepNum_textbook (d : ℕ) :
    1 ≤ (strongPowC7Textbook d).indepNum := by
  let x₀ : Fin d → Fin 7 := fun _ => 0
  have hind : (strongPowC7Textbook d).IsIndepSet (({x₀} : Finset (Fin d → Fin 7)) : Set _) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  have hcard := hind.card_le_indepNum
  simpa using hcard

private lemma indepNum_textbook_le (d : ℕ) :
    (strongPowC7Textbook d).indepNum ≤ 7 ^ d := by
  obtain ⟨s, hs⟩ := (strongPowC7Textbook d).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  calc s.card ≤ Fintype.card (Fin d → Fin 7) := s.card_le_univ
    _ = 7 ^ d := by simp

private lemma append_injective {α : Type*} {m n : ℕ} :
    Function.Injective (fun p : (Fin m → α) × (Fin n → α) => Fin.append p.1 p.2) := by
  rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h
  ext i
  · have := congrFun h (Fin.castAdd n i)
    simpa only [Fin.append_left] using this
  · have := congrFun h (Fin.natAdd m i)
    simpa only [Fin.append_right] using this

private lemma indepNum_textbook_supermult (m n : ℕ) :
    (strongPowC7Textbook m).indepNum * (strongPowC7Textbook n).indepNum ≤
      (strongPowC7Textbook (m + n)).indepNum := by
  obtain ⟨s, hs⟩ := (strongPowC7Textbook m).exists_isNIndepSet_indepNum
  obtain ⟨t, ht⟩ := (strongPowC7Textbook n).exists_isNIndepSet_indepNum
  let emb : (Fin m → Fin 7) × (Fin n → Fin 7) ↪ (Fin (m + n) → Fin 7) :=
    ⟨fun p => Fin.append p.1 p.2, append_injective⟩
  have hind : (strongPowC7Textbook (m + n)).IsIndepSet (((s ×ˢ t).map emb : Finset _) : Set _) := by
    intro x hx y hy hxy hadj
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨⟨u₁, v₁⟩, h₁, rfl⟩ := hx
    obtain ⟨⟨u₂, v₂⟩, h₂, rfl⟩ := hy
    rw [Finset.mem_product] at h₁ h₂
    have hne : u₁ ≠ u₂ ∨ v₁ ≠ v₂ := by
      by_cases hu : u₁ = u₂
      · right; intro hv; exact hxy (congrArg emb (Prod.ext hu hv))
      · left; exact hu
    rcases hne with hu | hv
    · refine hs.isIndepSet (Finset.mem_coe.mpr h₁.1) (Finset.mem_coe.mpr h₂.1) hu ⟨hu, fun i => ?_⟩
      have hi := hadj.2 (Fin.castAdd n i)
      simpa only [emb, Function.Embedding.coeFn_mk, Fin.append_left] using hi
    · refine ht.isIndepSet (Finset.mem_coe.mpr h₁.2) (Finset.mem_coe.mpr h₂.2) hv ⟨hv, fun j => ?_⟩
      have hj := hadj.2 (Fin.natAdd m j)
      simpa only [emb, Function.Embedding.coeFn_mk, Fin.append_right] using hj
  have hcard := hind.card_le_indepNum
  rw [Finset.card_map, Finset.card_product, hs.card_eq, ht.card_eq] at hcard
  exact hcard

private lemma shannonSetTextbook_nonempty : shannonSetTextbook.Nonempty :=
  ⟨((strongPowC7Textbook 1).indepNum : ℝ) ^ (1 / ((1 : ℕ) : ℝ)), 1, Nat.one_pos, rfl⟩

private lemma shannonSetTextbook_bddAbove : BddAbove shannonSetTextbook := by
  refine ⟨(7 : ℝ), ?_⟩
  rintro x ⟨d, hd, rfl⟩
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hle : ((strongPowC7Textbook d).indepNum : ℝ) ≤ (7 : ℝ) ^ d := by
    have h := (Nat.cast_le (α := ℝ)).mpr (indepNum_textbook_le d)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have h7nn : (0 : ℝ) ≤ (7 : ℝ) := Nat.cast_nonneg 7
  calc ((strongPowC7Textbook d).indepNum : ℝ) ^ (1 / (d : ℝ))
      ≤ ((7 : ℝ) ^ d) ^ (1 / (d : ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hle (div_nonneg zero_le_one hd_pos.le)
    _ = ((7 : ℝ) ^ (d : ℝ)) ^ (1 / (d : ℝ)) := by rw [Real.rpow_natCast]
    _ = (7 : ℝ) ^ ((d : ℝ) * (1 / (d : ℝ))) := by rw [← Real.rpow_mul h7nn]
    _ = (7 : ℝ) := by rw [mul_one_div_cancel hd_pos.ne', Real.rpow_one]

/-- Independent Fekete limit theorem for `shannonCapacityTextbook`. -/
theorem textbook_tendsto :
    Filter.Tendsto
      (fun d : ℕ => ((strongPowC7Textbook d).indepNum : ℝ) ^ (1 / (d : ℝ)))
      Filter.atTop (nhds shannonCapacityTextbook) := by
  let u : ℕ → ℝ := fun d => -Real.log ((strongPowC7Textbook d).indepNum : ℝ)
  have hpos : ∀ d : ℕ, (0 : ℝ) < ((strongPowC7Textbook d).indepNum : ℝ) :=
    fun d => Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.one_pos (one_le_indepNum_textbook d))
  have hu : Subadditive u := by
    intro m n
    dsimp only [u]
    have hmul : ((strongPowC7Textbook m).indepNum : ℝ) * ((strongPowC7Textbook n).indepNum : ℝ) ≤
        ((strongPowC7Textbook (m + n)).indepNum : ℝ) := by
      have h := (Nat.cast_le (α := ℝ)).mpr (indepNum_textbook_supermult m n)
      simpa only [Nat.cast_mul] using h
    have hlog := Real.log_le_log (mul_pos (hpos m) (hpos n)) hmul
    rw [Real.log_mul (hpos m).ne' (hpos n).ne'] at hlog
    have hneg := neg_le_neg hlog
    rwa [neg_add] at hneg
  have hbdd : BddBelow (Set.range fun d : ℕ => u d / (d : ℝ)) := by
    refine ⟨-Real.log 7, ?_⟩
    rintro _ ⟨d, rfl⟩
    dsimp only
    by_cases hd : d = 0
    · subst hd
      have h17_nat : (1 : ℕ) ≤ 7 := by decide
      have h17 : (1 : ℝ) ≤ (7 : ℝ) := by
        simpa only [Nat.cast_one, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr h17_nat
      have hlog7 : (0 : ℝ) ≤ Real.log 7 := Real.log_nonneg h17
      simp only [Nat.cast_zero, div_zero]
      exact neg_nonpos.mpr hlog7
    · have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
      have hle : ((strongPowC7Textbook d).indepNum : ℝ) ≤ (7 : ℝ) ^ d := by
        have h := (Nat.cast_le (α := ℝ)).mpr (indepNum_textbook_le d)
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
      have hlog : Real.log ((strongPowC7Textbook d).indepNum : ℝ) ≤ (d : ℝ) * Real.log 7 := by
        calc Real.log ((strongPowC7Textbook d).indepNum : ℝ)
            ≤ Real.log ((7 : ℝ) ^ d) := Real.log_le_log (hpos d) hle
          _ = (d : ℝ) * Real.log 7 := Real.log_pow 7 d
      rw [le_div_iff₀ hd_pos]
      dsimp only [u]
      have hneg : -((d : ℝ) * Real.log 7) ≤ -Real.log ((strongPowC7Textbook d).indepNum : ℝ) :=
        neg_le_neg hlog
      rw [neg_mul, mul_comm]
      exact hneg
  have hlim_u : Filter.Tendsto (fun d : ℕ => u d / (d : ℝ)) Filter.atTop (nhds hu.lim) :=
    hu.tendsto_lim hbdd
  have hlim_exp :
      Filter.Tendsto (fun d : ℕ => Real.exp (-(u d / (d : ℝ))))
        Filter.atTop (nhds (Real.exp (-hu.lim))) :=
    ((Real.continuous_exp.comp continuous_neg).tendsto hu.lim).comp hlim_u
  have hterm : ∀ d : ℕ, 0 < d →
      Real.exp (-(u d / (d : ℝ))) = ((strongPowC7Textbook d).indepNum : ℝ) ^ (1 / (d : ℝ)) := by
    intro d _
    rw [Real.rpow_def_of_pos (hpos d)]
    dsimp only [u]
    rw [neg_div, neg_neg, div_eq_mul_one_div]
  have hlim_f :
      Filter.Tendsto
        (fun d : ℕ => ((strongPowC7Textbook d).indepNum : ℝ) ^ (1 / (d : ℝ)))
        Filter.atTop (nhds (Real.exp (-hu.lim))) :=
    hlim_exp.congr' (Filter.eventually_atTop.mpr ⟨1, fun d hd => hterm d hd⟩)
  have heq : Real.exp (-hu.lim) = shannonCapacityTextbook := by
    apply le_antisymm
    · exact le_of_tendsto hlim_f
        (Filter.eventually_atTop.mpr ⟨1, fun d hd =>
          le_csSup shannonSetTextbook_bddAbove ⟨d, hd, rfl⟩⟩)
    · refine csSup_le shannonSetTextbook_nonempty ?_
      rintro x ⟨d, hd, rfl⟩
      rw [← hterm d hd]
      exact Real.exp_le_exp.mpr (neg_le_neg (hu.lim_le_div hbdd hd.ne'))
  rwa [heq] at hlim_f

/-- Opaque-box equivalence: independent textbook `Θ(C₇)` equals `ShannonC7.shannonCapacity`.
    Never unfolds `ShannonC7.shannonCapacity` or any internal `ShannonC7.*` definition. -/
theorem textbook_eq_project :
    shannonCapacityTextbook = ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7) := by
  have hseq :
      (fun d : ℕ => ((strongPowC7Textbook d).indepNum : ℝ) ^ (1 / (d : ℝ))) =
      (fun d : ℕ => ((ShannonC7.strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ^ (1 / (d : ℝ))) := by
    funext d
    rw [textbook_indepNum_eq_project d]
  exact tendsto_nhds_unique (hseq ▸ textbook_tendsto) ShannonC7.c7_shannonCapacity_tendsto

/-! ## 3. Exact Signature & Anti-Tampering Audits (`PROJECT.md § 4.4`) -/

private lemma ten_pow_12_eq : (10 : ℝ) ^ (12 : ℕ) = (1000000000000 : ℝ) := by
  have h : ((10 ^ 12 : ℕ) : ℝ) = ((1000000000000 : ℕ) : ℝ) :=
    congrArg Nat.cast (rfl : (10 : ℕ) ^ 12 = 1000000000000)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

-- 3.1 Fekete limit export
example :
    Filter.Tendsto
      (fun d : ℕ => ((ShannonC7.strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ^ (1 / (d : ℝ)))
      Filter.atTop (nhds (ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7))) :=
  ShannonC7.c7_shannonCapacity_tendsto

-- 3.2 Exact small powers d = 1, 2, 3 (plus textbook transfer and upper exclusion for d = 3)
example : (ShannonC7.strongPowPi (SimpleGraph.cycleGraph 7) 1).indepNum = 3 :=
  ShannonC7.alpha_c7_pow1
example : (ShannonC7.strongPowPi (SimpleGraph.cycleGraph 7) 2).indepNum = 10 :=
  ShannonC7.alpha_c7_pow2
example : (ShannonC7.strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum = 33 :=
  ShannonC7.alpha_c7_pow3

theorem audit_textbook_alpha_pow1 : (strongPowC7Textbook 1).indepNum = 3 := by
  rw [textbook_indepNum_eq_project]; exact ShannonC7.alpha_c7_pow1
theorem audit_textbook_alpha_pow2 : (strongPowC7Textbook 2).indepNum = 10 := by
  rw [textbook_indepNum_eq_project]; exact ShannonC7.alpha_c7_pow2
theorem audit_textbook_alpha_pow3 : (strongPowC7Textbook 3).indepNum = 33 := by
  rw [textbook_indepNum_eq_project]; exact ShannonC7.alpha_c7_pow3

/-- Explicitly confirms `alpha_c7_pow3 = 33` rules out any size-34 independent set in `C₇^⊠3`. -/
theorem audit_alpha_pow3_not_34 : ¬ (34 ≤ (strongPowC7Textbook 3).indepNum) := by
  rw [audit_textbook_alpha_pow3]
  decide

-- 3.3 Lovász upper bound, alias anti-tampering, rational bound, and unattainability
theorem audit_lovaszThetaC7_formula :
    ShannonC7.lovaszThetaC7 = (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7)) :=
  rfl

example : ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7) ≤ ShannonC7.lovaszThetaC7 :=
  ShannonC7.c7_upper_lovasz

example :
    ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7) ≤
      (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7)) :=
  ShannonC7.c7_upper_lovasz

example :
    ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7) <
      (3317667207395 : ℝ) / 1000000000000 := by
  have h := ShannonC7.c7_upper_rational
  try rw [ten_pow_12_eq] at h
  exact h

example : ∀ d : ℕ, 0 < d →
    ((ShannonC7.strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum : ℝ) ^ (1 / (d : ℝ)) <
      (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7)) :=
  fun d hd => ShannonC7.c7_lovasz_unattainable d hd

-- Boundary instantiations of Galois unattainability at d = 1, 2, 3
example : ((strongPowC7Textbook 1).indepNum : ℝ) ^ (1 / (1 : ℝ)) <
    (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7)) := by
  rw [textbook_indepNum_eq_project, ← audit_lovaszThetaC7_formula]
  simpa only [Nat.cast_one] using ShannonC7.c7_lovasz_unattainable 1 (by decide)

example : ((strongPowC7Textbook 2).indepNum : ℝ) ^ (1 / (2 : ℝ)) <
    (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7)) := by
  rw [textbook_indepNum_eq_project, ← audit_lovaszThetaC7_formula]
  simpa only [Nat.cast_ofNat] using ShannonC7.c7_lovasz_unattainable 2 (by decide)

example : ((strongPowC7Textbook 3).indepNum : ℝ) ^ (1 / (3 : ℝ)) <
    (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7)) := by
  rw [textbook_indepNum_eq_project, ← audit_lovaszThetaC7_formula]
  simpa only [Nat.cast_ofNat] using ShannonC7.c7_lovasz_unattainable 3 (by decide)

-- 3.4 Frontier lower bound, sandwich, and pure-kernel GMP numerical sanity checks
example : ℕ := ShannonC7.c7_lower_num
example : ℕ := ShannonC7.c7_lower_den

example :
    (ShannonC7.c7_lower_num : ℝ) / (ShannonC7.c7_lower_den : ℝ) ≤
      ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7) :=
  ShannonC7.c7_lower_frontier

example :
    (ShannonC7.c7_lower_num : ℝ) / (ShannonC7.c7_lower_den : ℝ) ≤
      ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7) ∧
    ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7) ≤ ShannonC7.lovaszThetaC7 :=
  ShannonC7.c7_shannonCapacity_sandwich

/-- Pure-kernel GMP arithmetic sanity checks on `c7_lower_num / c7_lower_den`. -/
theorem audit_c7_lower_den_pos : 0 < ShannonC7.c7_lower_den := by
  decide

theorem audit_c7_lower_floor :
    3258805369885 * ShannonC7.c7_lower_den ≤ ShannonC7.c7_lower_num * 1000000000000 := by
  decide

theorem audit_c7_lower_lt_upper :
    ShannonC7.c7_lower_num * 1000000000000 < 3317667207395 * ShannonC7.c7_lower_den := by
  decide

/-- End-to-end textbook sandwich theorem mentioning ZERO `ShannonC7` symbols. -/
theorem audit_textbook_sandwich :
    (3258805369885 : ℝ) / 1000000000000 ≤ shannonCapacityTextbook ∧
    shannonCapacityTextbook ≤ (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7)) := by
  rw [textbook_eq_project]
  refine ⟨?_, ShannonC7.c7_upper_lovasz⟩
  have hden_pos : (0 : ℝ) < (ShannonC7.c7_lower_den : ℝ) :=
    Nat.cast_pos.mpr audit_c7_lower_den_pos
  have h10_pos : (0 : ℝ) < (1000000000000 : ℝ) :=
    Nat.cast_pos.mpr (by decide : 0 < 1000000000000)
  have hfloor_real :
      (3258805369885 : ℝ) / 1000000000000 ≤
        (ShannonC7.c7_lower_num : ℝ) / (ShannonC7.c7_lower_den : ℝ) := by
    rw [div_le_iff₀ h10_pos, div_mul_eq_mul_div, le_div_iff₀ hden_pos]
    have hnat : 3258805369885 * ShannonC7.c7_lower_den ≤
        ShannonC7.c7_lower_num * 1000000000000 := audit_c7_lower_floor
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hnat
  exact le_trans hfloor_real ShannonC7.c7_lower_frontier

-- 3.5 Generalizations (`C₇ᶜ`, `C₅`, general odd cycles `C_{2k+1}`)
example :
    (17 : ℝ) ^ (1 / 4 : ℝ) ≤ ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ∧
    ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ≤
      1 + (Real.cos (Real.pi / 7))⁻¹ := by
  simpa only [one_div] using ShannonC7.c7_compl_sandwich

example : ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 5) = Real.sqrt 5 :=
  ShannonC7.c5_shannonCapacity_eq_sqrt_five

private theorem audit_oddCycle_upper_at (k : ℕ) (hk : 1 ≤ k) :
    ShannonC7.shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1)) ≤
      ((2 * (k : ℝ) + 1) * Real.cos (Real.pi / (2 * (k : ℝ) + 1))) /
        (1 + Real.cos (Real.pi / (2 * (k : ℝ) + 1))) := by
  have h := ShannonC7.oddCycle_upper_lovasz k hk
  try simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
  exact h

-- Boundary instantiations of `oddCycle_upper_lovasz` at k = 1, 2, 3, 4 (C₃, C₅, C₇, C₉)
example : ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 3) ≤
    ((2 * (1 : ℝ) + 1) * Real.cos (Real.pi / (2 * (1 : ℝ) + 1))) /
      (1 + Real.cos (Real.pi / (2 * (1 : ℝ) + 1))) := by
  simpa only [Nat.cast_one] using audit_oddCycle_upper_at 1 (by decide)

example : ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 5) ≤
    ((2 * (2 : ℝ) + 1) * Real.cos (Real.pi / (2 * (2 : ℝ) + 1))) /
      (1 + Real.cos (Real.pi / (2 * (2 : ℝ) + 1))) := by
  simpa only [Nat.cast_ofNat] using audit_oddCycle_upper_at 2 (by decide)

example : ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7) ≤
    ((2 * (3 : ℝ) + 1) * Real.cos (Real.pi / (2 * (3 : ℝ) + 1))) /
      (1 + Real.cos (Real.pi / (2 * (3 : ℝ) + 1))) := by
  simpa only [Nat.cast_ofNat] using audit_oddCycle_upper_at 3 (by decide)

example : ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 9) ≤
    ((2 * (4 : ℝ) + 1) * Real.cos (Real.pi / (2 * (4 : ℝ) + 1))) /
      (1 + Real.cos (Real.pi / (2 * (4 : ℝ) + 1))) := by
  simpa only [Nat.cast_ofNat] using audit_oddCycle_upper_at 4 (by decide)

-- 3.6 Formal Open Problem Statements
example : Prop := ShannonC7.OpenQuestion_StrictGap
example : ShannonC7.OpenQuestion_StrictGap ↔
    ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7) <
      (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7)) := Iff.rfl

example : Prop := ShannonC7.OpenQuestion_ExactValue
example : ShannonC7.OpenQuestion_ExactValue ↔
    ∃ c : ℝ, ShannonC7.shannonCapacity (SimpleGraph.cycleGraph 7) = c := Iff.rfl

end E2EAudit

/-! ## 4. Kernel-Evaluated Constant Export (Parsed by `verify/cross_check.py`) -/

#eval IO.println s!"E2E_CONST c7_lower_num={ShannonC7.c7_lower_num}"
#eval IO.println s!"E2E_CONST c7_lower_den={ShannonC7.c7_lower_den}"

/-! ## 5. Exhaustive `#print axioms` Audit — Exact 24 Declarations (Parsed by `verify/cross_check.py`) -/

-- 12 Exported ShannonC7 theorems (PROJECT.md § 4.4)
#print axioms ShannonC7.c7_shannonCapacity_tendsto
#print axioms ShannonC7.alpha_c7_pow1
#print axioms ShannonC7.alpha_c7_pow2
#print axioms ShannonC7.alpha_c7_pow3
#print axioms ShannonC7.c7_upper_lovasz
#print axioms ShannonC7.c7_upper_rational
#print axioms ShannonC7.c7_lovasz_unattainable
#print axioms ShannonC7.c7_lower_frontier
#print axioms ShannonC7.c7_shannonCapacity_sandwich
#print axioms ShannonC7.c7_compl_sandwich
#print axioms ShannonC7.c5_shannonCapacity_eq_sqrt_five
#print axioms ShannonC7.oddCycle_upper_lovasz

-- 7 Exported ShannonC7 definitions / constants (guards against axiomatic defs)
#print axioms ShannonC7.c7_lower_num
#print axioms ShannonC7.c7_lower_den
#print axioms ShannonC7.lovaszThetaC7
#print axioms ShannonC7.shannonCapacity
#print axioms ShannonC7.strongPowPi
#print axioms ShannonC7.OpenQuestion_StrictGap
#print axioms ShannonC7.OpenQuestion_ExactValue

-- 5 Derived E2EAudit opaque-box bridge & pure-kernel numerical sanity theorems
#print axioms E2EAudit.textbook_eq_project
#print axioms E2EAudit.audit_textbook_sandwich
#print axioms E2EAudit.audit_c7_lower_den_pos
#print axioms E2EAudit.audit_c7_lower_floor
#print axioms E2EAudit.audit_c7_lower_lt_upper
