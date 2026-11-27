import ShannonC7.FrontierLower

/-!
# Decoupled Portfolio Free-J Auxiliary Upgrading & `Γ₆^⊠3` Pullback (`d = 220`)

This module extends `ShannonC7/FrontierLower.lean` with two pure-kernel algebraic theorems
(`{propext, Classical.choice, Quot.sound}` only — zero `sorry`, zero `native_decide`, zero `partial`,
and zero new 5D trie witnesses beyond M3's locked `baseHetero5D`):

1. **Decoupled Portfolio Free-J Upgrade (`AuxPartition.upg1FreeJ`):**
   On `prodAlignedCore g₁ g₂`, any secondary auxiliary partition `a₂' : AuxPartition g₂.core`
   (completely decoupled from `g₂.aux` used to form the core ports) paired with *any* independent
   set `J₂` in `H` constructs a valid `AuxPartition (prodAlignedCore g₁ g₂)`:
   - `O_new = g₁.aux.O ×ˢ a₂'.O`
   - `H_new = (g₁.aux.O ×ˢ a₂'.H) ∪ (g₁.aux.H ×ˢ J₂)`
   - `V_new = (g₁.aux.O ×ˢ a₂'.V) ∪ (g₁.aux.V ×ˢ J₂)`
   lifting `c_new = d₁ · c₂' + (h₁ + v₁) · |J₂|` recursively across arbitrary depth while keeping
   every intermediate `PortCore`'s port density `b / a` intact.

2. **Three-Fold Quotient Pullback (`gamma6Pow3_card_le_strongPow_indepNum`):**
   Pulls back any 21-term independent list in `Γ₆^⊠3` on three `PartGadget`s to an explicit
   independent set in `strongPow C7 (d₁ + d₂ + d₃)`, strictly boosting intermediate `J₂` cardinalities
   at `k = 3, 6, 9, 14` (and reusing `gamma6Pow4_weight_le_indepNum` at `k = 4`).

Instantiating a 10-core + 6-pullback DAG on M3's `baseHetero5D` (`d = 220`) certifies the exact
113-digit cardinality `portfolioCard` in `C₇^⊠220` and proves:
`3258827798879807 / 1000000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7)`.
-/

namespace ShannonC7

/-! ## 1. `AuxPartition.mapIso` & Decoupled `AuxPartition.upg1FreeJ` -/

namespace AuxPartition

variable {α β : Type*} [Fintype α] [Fintype β] {G : SimpleGraph α} {H : SimpleGraph β}

/-- Transport an `AuxPartition` along a graph isomorphism `e : G ≃g H`. -/
def mapIso (e : G ≃g H) {c : PortCore G} (a : AuxPartition c) : AuxPartition (c.mapIso e) where
  O := a.O.map e.toEquiv.toEmbedding
  H := a.H.map e.toEquiv.toEmbedding
  V := a.V.map e.toEquiv.toEmbedding
  indep_O := isIndepSet_map_iso e a.indep_O
  indep_H := isIndepSet_map_iso e a.indep_H
  indep_V := isIndepSet_map_iso e a.indep_V
  not_close_OH := by
    intro x hx y hy hc
    rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
    rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
    exact a.not_close_OH x' hx' y' hy' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)
  not_close_OV := by
    intro x hx y hy hc
    rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
    rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
    exact a.not_close_OV x' hx' y' hy' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)
  not_close_HV := by
    intro x hx y hy hc
    rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
    rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
    exact a.not_close_HV x' hx' y' hy' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)
  not_close_P0_O := by
    intro p hp o ho hc
    rcases (portCore_mem_mapIso_P0 e c).mp hp with ⟨p', hp', rfl⟩
    rcases Finset.mem_map.mp ho with ⟨o', ho', rfl⟩
    exact a.not_close_P0_O p' hp' o' ho' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)
  not_close_P1_O := by
    intro p hp o ho hc
    rcases (portCore_mem_mapIso_P1 e c).mp hp with ⟨p', hp', rfl⟩
    rcases Finset.mem_map.mp ho with ⟨o', ho', rfl⟩
    exact a.not_close_P1_O p' hp' o' ho' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)
  not_close_P1_H := by
    intro p hp h hh hc
    rcases (portCore_mem_mapIso_P1 e c).mp hp with ⟨p', hp', rfl⟩
    rcases Finset.mem_map.mp hh with ⟨h', hh', rfl⟩
    exact a.not_close_P1_H p' hp' h' hh' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)
  not_close_P0_V := by
    intro p hp v hv hc
    rcases (portCore_mem_mapIso_P0 e c).mp hp with ⟨p', hp', rfl⟩
    rcases Finset.mem_map.mp hv with ⟨v', hv', rfl⟩
    exact a.not_close_P0_V p' hp' v' hv' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)

theorem mapIso_cards (e : G ≃g H) {c : PortCore G} (a : AuxPartition c) :
    (a.mapIso e).O.card = a.O.card ∧
    (a.mapIso e).H.card = a.H.card ∧
    (a.mapIso e).V.card = a.V.card :=
  ⟨Finset.card_map _, Finset.card_map _, Finset.card_map _⟩

/-- **Decoupled Portfolio Free-J Auxiliary Upgrade:**
Given `g1 : PartGadget G`, `g2 : PartGadget H`, *any* secondary auxiliary partition
`a2' : AuxPartition g2.core` (independent of `g2.aux`), and *any* independent set `J2` in `H`,
constructs a valid `AuxPartition (PartGadget.prodAlignedCore g1 g2)` with:
`O = g1.aux.O ×ˢ a2'.O`, `H = (g1.aux.O ×ˢ a2'.H) ∪ (g1.aux.H ×ˢ J2)`,
`V = (g1.aux.O ×ˢ a2'.V) ∪ (g1.aux.V ×ˢ J2)`. -/
noncomputable def upg1FreeJ (g1 : PartGadget G) (g2 : PartGadget H)
    (a2' : AuxPartition g2.core) (J2 : Finset β) (hJ2 : H.IsIndepSet (J2 : Set β)) :
    AuxPartition (PartGadget.prodAlignedCore g1 g2) := by
  classical
  let O0 := g1.aux.O ×ˢ a2'.O
  let H0 := g1.aux.O ×ˢ a2'.H
  let H1 := g1.aux.H ×ˢ J2
  let V0 := g1.aux.O ×ˢ a2'.V
  let V1 := g1.aux.V ×ˢ J2
  refine
    { O := O0
      H := H0 ∪ H1
      V := V0 ∪ V1
      indep_O := isIndepSet_prod g1.aux.indep_O a2'.indep_O
      indep_H := isIndepSet_union_of_not_close
        (isIndepSet_prod g1.aux.indep_O a2'.indep_H)
        (isIndepSet_prod g1.aux.indep_H hJ2) (by
          rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [H0, H1, Finset.mem_product] at h₁ h₂
          exact not_close_prod_fst (g1.aux.not_close_OH _ h₁.1 _ h₂.1))
      indep_V := isIndepSet_union_of_not_close
        (isIndepSet_prod g1.aux.indep_O a2'.indep_V)
        (isIndepSet_prod g1.aux.indep_V hJ2) (by
          rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [V0, V1, Finset.mem_product] at h₁ h₂
          exact not_close_prod_fst (g1.aux.not_close_OV _ h₁.1 _ h₂.1))
      not_close_OH := ?_, not_close_OV := ?_, not_close_HV := ?_
      not_close_P0_O := ?_, not_close_P1_O := ?_, not_close_P1_H := ?_, not_close_P0_V := ?_ }
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy
    simp only [O0, H0, H1, Finset.mem_union, Finset.mem_product] at hx hy
    rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact not_close_prod_snd (a2'.not_close_OH _ hx.2 _ hy2)
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hx.1 _ hy1)
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy
    simp only [O0, V0, V1, Finset.mem_union, Finset.mem_product] at hx hy
    rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact not_close_prod_snd (a2'.not_close_OV _ hx.2 _ hy2)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hx.1 _ hy1)
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy
    simp only [H0, H1, V0, V1, Finset.mem_union, Finset.mem_product] at hx hy
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;> rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact not_close_prod_snd (a2'.not_close_HV _ hx2 _ hy2)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hx1 _ hy1)
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OH _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_fst (g1.aux.not_close_HV _ hx1 _ hy1)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ ho
    rw [PartGadget.mem_prodAlignedCore_P0] at hp
    simp only [O0, Finset.mem_product] at ho
    rcases hp with ⟨hp1, _⟩ | ⟨_, hp2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P0_O _ hp1 _ ho.1)
    · exact not_close_prod_snd (a2'.not_close_P0_O _ hp2 _ ho.2)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ ho
    rw [PartGadget.mem_prodAlignedCore_P1] at hp
    simp only [O0, Finset.mem_product] at ho
    rcases hp with ⟨hp1, _⟩ | ⟨_, hp2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P1_O _ hp1 _ ho.1)
    · exact not_close_prod_snd (a2'.not_close_P1_O _ hp2 _ ho.2)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ hh
    rw [PartGadget.mem_prodAlignedCore_P1] at hp
    simp only [H0, H1, Finset.mem_union, Finset.mem_product] at hh
    rcases hp with ⟨hp1, _⟩ | ⟨hp1, hp2⟩ <;> rcases hh with ⟨hh1, hh2⟩ | ⟨hh1, _⟩
    · exact not_close_prod_fst (g1.aux.not_close_P1_O _ hp1 _ hh1)
    · exact not_close_prod_fst (g1.aux.not_close_P1_H _ hp1 _ hh1)
    · exact not_close_prod_snd (a2'.not_close_P1_H _ hp2 _ hh2)
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hp1 _ hh1)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ hv
    rw [PartGadget.mem_prodAlignedCore_P0] at hp
    simp only [V0, V1, Finset.mem_union, Finset.mem_product] at hv
    rcases hp with ⟨hp1, _⟩ | ⟨hp1, hp2⟩ <;> rcases hv with ⟨hv1, hv2⟩ | ⟨hv1, _⟩
    · exact not_close_prod_fst (g1.aux.not_close_P0_O _ hp1 _ hv1)
    · exact not_close_prod_fst (g1.aux.not_close_P0_V _ hp1 _ hv1)
    · exact not_close_prod_snd (a2'.not_close_P0_V _ hp2 _ hv2)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hp1 _ hv1)

theorem upg1FreeJ_cards (g1 : PartGadget G) (g2 : PartGadget H)
    (a2' : AuxPartition g2.core) (J2 : Finset β) (hJ2 : H.IsIndepSet (J2 : Set β)) :
    (upg1FreeJ g1 g2 a2' J2 hJ2).O.card = g1.aux.O.card * a2'.O.card ∧
    (upg1FreeJ g1 g2 a2' J2 hJ2).H.card = g1.aux.O.card * a2'.H.card + g1.aux.H.card * J2.card ∧
    (upg1FreeJ g1 g2 a2' J2 hJ2).V.card = g1.aux.O.card * a2'.V.card + g1.aux.V.card * J2.card := by
  classical
  have hO : (upg1FreeJ g1 g2 a2' J2 hJ2).O.card = g1.aux.O.card * a2'.O.card :=
    Finset.card_product _ _
  have hH : (upg1FreeJ g1 g2 a2' J2 hJ2).H.card =
      g1.aux.O.card * a2'.H.card + g1.aux.H.card * J2.card := by
    change ((g1.aux.O ×ˢ a2'.H) ∪ (g1.aux.H ×ˢ J2)).card = _
    have hd : Disjoint (g1.aux.O ×ˢ a2'.H) (g1.aux.H ×ˢ J2) :=
      disjoint_of_not_close (G := G ⊠ H) (by
        rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂
        exact not_close_prod_fst (g1.aux.not_close_OH _ h₁.1 _ h₂.1))
    rw [Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product]
  have hV : (upg1FreeJ g1 g2 a2' J2 hJ2).V.card =
      g1.aux.O.card * a2'.V.card + g1.aux.V.card * J2.card := by
    change ((g1.aux.O ×ˢ a2'.V) ∪ (g1.aux.V ×ˢ J2)).card = _
    have hd : Disjoint (g1.aux.O ×ˢ a2'.V) (g1.aux.V ×ˢ J2) :=
      disjoint_of_not_close (G := G ⊠ H) (by
        rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂
        exact not_close_prod_fst (g1.aux.not_close_OV _ h₁.1 _ h₂.1))
    rw [Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product]
  exact ⟨hO, hH, hV⟩

/-- Helper lifting `M ≤ H.indepNum` into a decoupled `upg1FreeJ` auxiliary partition with lower
bounds `(d_lb, h_lb, v_lb)` transported through `e : G ⊠ H ≃g K`. -/
theorem exists_upg1FreeJ_iso {γ : Type*} [Fintype γ] {K : SimpleGraph γ}
    (g1 : PartGadget G) (g2 : PartGadget H) (e : (G ⊠ H) ≃g K)
    {d1 h1 v1 d2' h2' v2' M2 : ℕ}
    (hd1 : g1.aux.O.card = d1) (hh1 : g1.aux.H.card = h1) (hv1 : g1.aux.V.card = v1)
    (ha2' : ∃ a2' : AuxPartition g2.core, d2' ≤ a2'.O.card ∧ h2' ≤ a2'.H.card ∧ v2' ≤ a2'.V.card)
    (hM2 : M2 ≤ H.indepNum) :
    ∃ a : AuxPartition ((g1.prodStd g2).mapIso e).core,
      d1 * d2' ≤ a.O.card ∧
      d1 * h2' + h1 * M2 ≤ a.H.card ∧
      d1 * v2' + v1 * M2 ≤ a.V.card := by
  rcases ha2' with ⟨a2', hd2', hh2', hv2'⟩
  obtain ⟨J2, hJ2⟩ := H.exists_isNIndepSet_indepNum
  have hJ2_card : M2 ≤ J2.card := by rw [hJ2.card_eq]; exact hM2
  let a0 : AuxPartition (PartGadget.prodAlignedCore g1 g2) :=
    upg1FreeJ g1 g2 a2' J2 hJ2.isIndepSet
  refine ⟨a0.mapIso e, ?_, ?_, ?_⟩
  · have h := (mapIso_cards e a0).1.trans (upg1FreeJ_cards g1 g2 a2' J2 hJ2.isIndepSet).1
    rw [h, hd1]; exact Nat.mul_le_mul_left d1 hd2'
  · have h := (mapIso_cards e a0).2.1.trans (upg1FreeJ_cards g1 g2 a2' J2 hJ2.isIndepSet).2.1
    rw [h, hd1, hh1]
    exact Nat.add_le_add (Nat.mul_le_mul_left d1 hh2') (Nat.mul_le_mul_left h1 hJ2_card)
  · have h := (mapIso_cards e a0).2.2.trans (upg1FreeJ_cards g1 g2 a2' J2 hJ2.isIndepSet).2.2
    rw [h, hd1, hv1]
    exact Nat.add_le_add (Nat.mul_le_mul_left d1 hv2') (Nat.mul_le_mul_left v1 hJ2_card)

end AuxPartition

/-! ## 2. Three-Fold Quotient Pullback `Γ₆^⊠3` on `PartGadget`s -/

abbrev Gamma6Triple := Fin 6 × Fin 6 × Fin 6

def gamma6TripleCloseBool (x y : Gamma6Triple) : Bool :=
  gamma6CloseBool x.1 y.1 && gamma6CloseBool x.2.1 y.2.1 && gamma6CloseBool x.2.2 y.2.2

def gamma6TripleListIndepBool : List Gamma6Triple → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !gamma6TripleCloseBool x y) && gamma6TripleListIndepBool xs

def gamma6TripleWeight (p₁ p₂ p₃ : AsymProfile) (t : Gamma6Triple) : ℕ :=
  p₁.gamma6Weight t.1 * p₂.gamma6Weight t.2.1 * p₃.gamma6Weight t.2.2

def gamma6TripleListWeight (p₁ p₂ p₃ : AsymProfile) (S : List Gamma6Triple) : ℕ :=
  (S.map (gamma6TripleWeight p₁ p₂ p₃)).sum

theorem gamma6TripleCloseBool_symm (x y : Gamma6Triple) :
    gamma6TripleCloseBool x y = gamma6TripleCloseBool y x := by
  have h1 : ∀ a b : Fin 6, gamma6CloseBool a b = gamma6CloseBool b a := by decide
  simp only [gamma6TripleCloseBool, h1]

theorem gamma6TripleCloseBool_refl (x : Gamma6Triple) : gamma6TripleCloseBool x x = true := by
  have h1 : ∀ a : Fin 6, gamma6CloseBool a a = true := by decide
  simp only [gamma6TripleCloseBool, h1, Bool.and_self]

theorem gamma6TripleListIndepBool_spec {S : List Gamma6Triple}
    (h : gamma6TripleListIndepBool S = true) :
    S.Nodup ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → gamma6TripleCloseBool x y = false := by
  induction S with
  | nil => exact ⟨List.nodup_nil, fun _ hx => by cases hx⟩
  | cons a tl ih =>
    simp only [gamma6TripleListIndepBool, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true'] at h
    rcases ih h.2 with ⟨hnd, hpair⟩
    have ha_not : a ∉ tl := by
      intro hmem
      have hc := h.1 a hmem
      rw [gamma6TripleCloseBool_refl] at hc
      exact Bool.noConfusion hc
    refine ⟨List.nodup_cons.mpr ⟨ha_not, hnd⟩, ?_⟩
    intro x hx y hy hne
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hne
    · exact h.1 y hy
    · rw [gamma6TripleCloseBool_symm]; exact h.1 x hx
    · exact hpair x hx y hy hne

noncomputable def gamma6TripleBlock
    {V₁ V₂ V₃ : Type*} [Fintype V₁] [Fintype V₂] [Fintype V₃]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {G₃ : SimpleGraph V₃}
    (g₁ : PartGadget G₁) (g₂ : PartGadget G₂) (g₃ : PartGadget G₃)
    (t : Gamma6Triple) : Finset ((V₁ × V₂) × V₃) :=
  (g₁.gamma6Block t.1 ×ˢ g₂.gamma6Block t.2.1) ×ˢ g₃.gamma6Block t.2.2

theorem gamma6TripleBlock_card
    {V₁ V₂ V₃ : Type*} [Fintype V₁] [Fintype V₂] [Fintype V₃]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {G₃ : SimpleGraph V₃}
    (g₁ : PartGadget G₁) (g₂ : PartGadget G₂) (g₃ : PartGadget G₃) (t : Gamma6Triple) :
    (gamma6TripleBlock g₁ g₂ g₃ t).card =
      gamma6TripleWeight g₁.asymProfile g₂.asymProfile g₃.asymProfile t := by
  simp only [gamma6TripleBlock, Finset.card_product, PartGadget.gamma6Block_card,
    gamma6TripleWeight]

theorem gamma6TripleBlock_isIndepSet
    {V₁ V₂ V₃ : Type*} [Fintype V₁] [Fintype V₂] [Fintype V₃]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {G₃ : SimpleGraph V₃}
    (g₁ : PartGadget G₁) (g₂ : PartGadget G₂) (g₃ : PartGadget G₃) (t : Gamma6Triple) :
    ((G₁ ⊠ G₂) ⊠ G₃).IsIndepSet (gamma6TripleBlock g₁ g₂ g₃ t : Set _) :=
  isIndepSet_prod
    (isIndepSet_prod (g₁.gamma6Block_isIndepSet t.1) (g₂.gamma6Block_isIndepSet t.2.1))
    (g₃.gamma6Block_isIndepSet t.2.2)

theorem gamma6TripleBlock_not_close
    {V₁ V₂ V₃ : Type*} [Fintype V₁] [Fintype V₂] [Fintype V₃]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {G₃ : SimpleGraph V₃}
    (g₁ : PartGadget G₁) (g₂ : PartGadget G₂) (g₃ : PartGadget G₃)
    {t₁ t₂ : Gamma6Triple} (hnc : gamma6TripleCloseBool t₁ t₂ = false)
    {x y : (V₁ × V₂) × V₃}
    (hx : x ∈ gamma6TripleBlock g₁ g₂ g₃ t₁)
    (hy : y ∈ gamma6TripleBlock g₁ g₂ g₃ t₂) :
    ¬ (x = y ∨ ((G₁ ⊠ G₂) ⊠ G₃).Adj x y) := by
  rcases x with ⟨⟨x₁, x₂⟩, x₃⟩
  rcases y with ⟨⟨y₁, y₂⟩, y₃⟩
  simp only [gamma6TripleBlock, Finset.mem_product] at hx hy
  simp only [gamma6TripleCloseBool, Bool.and_eq_false_iff] at hnc
  intro hc
  have h12_3 := eq_or_strongProd_adj.mp hc
  have h1_2 := eq_or_strongProd_adj.mp h12_3.1
  rcases hnc with (h1 | h2) | h3
  · exact g₁.gamma6Block_not_close h1 hx.1.1 hy.1.1 h1_2.1
  · exact g₂.gamma6Block_not_close h2 hx.1.2 hy.1.2 h1_2.2
  · exact g₃.gamma6Block_not_close h3 hx.2 hy.2 h12_3.2

/-- Pullback of any independent list `S` in `Γ₆^⊠3` to `(G₁ ⊠ G₂) ⊠ G₃`. -/
theorem gamma6Pow3_weight_le_indepNum
    {V₁ V₂ V₃ : Type*} [Fintype V₁] [Fintype V₂] [Fintype V₃]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {G₃ : SimpleGraph V₃}
    (g₁ : PartGadget G₁) (g₂ : PartGadget G₂) (g₃ : PartGadget G₃)
    (S : List Gamma6Triple) (hindep : gamma6TripleListIndepBool S = true) :
    gamma6TripleListWeight g₁.asymProfile g₂.asymProfile g₃.asymProfile S ≤
      ((G₁ ⊠ G₂) ⊠ G₃).indepNum := by
  classical
  rcases gamma6TripleListIndepBool_spec hindep with ⟨hnd, hpair⟩
  let U : Finset ((V₁ × V₂) × V₃) := S.toFinset.biUnion (gamma6TripleBlock g₁ g₂ g₃)
  have hU_indep : ((G₁ ⊠ G₂) ⊠ G₃).IsIndepSet (U : Set _) := by
    intro x hx y hy hne hadj
    simp only [U, Finset.mem_coe, Finset.mem_biUnion, List.mem_toFinset] at hx hy
    rcases hx with ⟨t₁, ht₁, hx₁⟩
    rcases hy with ⟨t₂, ht₂, hy₂⟩
    by_cases ht : t₁ = t₂
    · subst ht; exact gamma6TripleBlock_isIndepSet g₁ g₂ g₃ t₁ hx₁ hy₂ hne hadj
    · exact gamma6TripleBlock_not_close g₁ g₂ g₃ (hpair t₁ ht₁ t₂ ht₂ ht) hx₁ hy₂ (Or.inr hadj)
  have hdisj : Set.PairwiseDisjoint (S.toFinset : Set Gamma6Triple) (gamma6TripleBlock g₁ g₂ g₃) := by
    intro t₁ ht₁ t₂ ht₂ hne
    exact disjoint_of_not_close (fun x hx y hy =>
      gamma6TripleBlock_not_close g₁ g₂ g₃
        (hpair t₁ (List.mem_toFinset.mp ht₁) t₂ (List.mem_toFinset.mp ht₂) hne) hx hy)
  have hcard : U.card = gamma6TripleListWeight g₁.asymProfile g₂.asymProfile g₃.asymProfile S := by
    rw [Finset.card_biUnion hdisj]
    simp_rw [gamma6TripleBlock_card]
    rw [gamma6TripleListWeight, List.sum_toFinset _ hnd]
  rw [← hcard]
  exact hU_indep.card_le_indepNum

/-- Direct bridge from 3 `PartGadget`s on `strongPow C7` + independent `Γ₆^⊠3` list
to `(strongPow C7 (d₁ + d₂ + d₃)).indepNum`. -/
theorem gamma6Pow3_card_le_strongPow_indepNum
    {d₁ d₂ d₃ : ℕ}
    (g₁ : PartGadget (strongPow C7 d₁))
    (g₂ : PartGadget (strongPow C7 d₂))
    (g₃ : PartGadget (strongPow C7 d₃))
    (S : List Gamma6Triple) (hindep : gamma6TripleListIndepBool S = true) :
    gamma6TripleListWeight g₁.asymProfile g₂.asymProfile g₃.asymProfile S ≤
      (strongPow C7 (d₁ + d₂ + d₃)).indepNum := by
  have h1 := gamma6Pow3_weight_le_indepNum g₁ g₂ g₃ S hindep
  have e12 : strongPow C7 d₁ ⊠ strongPow C7 d₂ ≃g strongPow C7 (d₁ + d₂) :=
    (strongPowAddEquiv C7 d₁ d₂).symm
  have e123 : (strongPow C7 d₁ ⊠ strongPow C7 d₂) ⊠ strongPow C7 d₃ ≃g
      strongPow C7 (d₁ + d₂ + d₃) :=
    (strongProdCongr e12 SimpleGraph.Iso.refl).trans (strongPowAddEquiv C7 (d₁ + d₂) d₃).symm
  have h_eq : ((strongPow C7 d₁ ⊠ strongPow C7 d₂) ⊠ strongPow C7 d₃).indepNum =
      (strongPow C7 (d₁ + d₂ + d₃)).indepNum :=
    iso_indepNum_eq e123
  omega

/-- Direct bridge from 4 `PartGadget`s on `strongPow C7` + independent `Γ₆^⊠4` list
to `(strongPow C7 (d₁ + d₂ + d₃ + d₄)).indepNum`. -/
theorem gamma6Pow4_card_le_strongPow_indepNum
    {d₁ d₂ d₃ d₄ : ℕ}
    (g₁ : PartGadget (strongPow C7 d₁)) (g₂ : PartGadget (strongPow C7 d₂))
    (g₃ : PartGadget (strongPow C7 d₃)) (g₄ : PartGadget (strongPow C7 d₄))
    (S : List Gamma6Quad) (hindep : gamma6QuadListIndepBool S = true) :
    gamma6QuadListWeight g₁.asymProfile g₂.asymProfile g₃.asymProfile g₄.asymProfile S ≤
      (strongPow C7 (d₁ + d₂ + d₃ + d₄)).indepNum := by
  have h1 := gamma6Pow4_weight_le_indepNum g₁ g₂ g₃ g₄ S hindep
  have e12 : strongPow C7 d₁ ⊠ strongPow C7 d₂ ≃g strongPow C7 (d₁ + d₂) :=
    (strongPowAddEquiv C7 d₁ d₂).symm
  have e123 : (strongPow C7 d₁ ⊠ strongPow C7 d₂) ⊠ strongPow C7 d₃ ≃g
      strongPow C7 (d₁ + d₂ + d₃) :=
    (strongProdCongr e12 SimpleGraph.Iso.refl).trans (strongPowAddEquiv C7 (d₁ + d₂) d₃).symm
  have e1234 : ((strongPow C7 d₁ ⊠ strongPow C7 d₂) ⊠ strongPow C7 d₃) ⊠ strongPow C7 d₄ ≃g
      strongPow C7 (d₁ + d₂ + d₃ + d₄) :=
    (strongProdCongr e123 SimpleGraph.Iso.refl).trans (strongPowAddEquiv C7 (d₁ + d₂ + d₃) d₄).symm
  have h_eq : (((strongPow C7 d₁ ⊠ strongPow C7 d₂) ⊠ strongPow C7 d₃) ⊠ strongPow C7 d₄).indepNum =
      (strongPow C7 (d₁ + d₂ + d₃ + d₄)).indepNum :=
    iso_indepNum_eq e1234
  omega

/-! ## 3. Concrete 10-Core + 6-Pullback Decoupled Portfolio DAG (`d = 220`) -/

/-- Exact 21-term independent list in `Γ₆^⊠3` used at `k = 3, 6, 9, 14`. -/
def portfolioPat3 : List Gamma6Triple :=
  [ (0, 0, 0), (0, 4, 2), (1, 0, 4), (1, 1, 2), (1, 5, 3),
    (2, 0, 5), (2, 3, 3), (2, 4, 3), (3, 1, 3), (3, 1, 4),
    (3, 2, 5), (3, 3, 2), (3, 5, 1), (4, 1, 0), (4, 3, 2),
    (4, 5, 2), (5, 1, 4), (5, 2, 3), (5, 2, 5), (5, 3, 1), (5, 5, 1) ]

theorem portfolioPat3_indep : gamma6TripleListIndepBool portfolioPat3 = true := by decide

/-- Exact 57-term independent list in `Γ₆^⊠4` used at `k = 4` (`d = 20`). -/
def portfolioPat4 : List Gamma6Quad :=
  [ (0, 0, 0, 0), (0, 1, 3, 5), (0, 1, 5, 3), (0, 1, 5, 5), (0, 2, 0, 4), (0, 3, 1, 4),
    (1, 1, 0, 1), (1, 1, 2, 3), (1, 2, 2, 5), (1, 3, 2, 1), (1, 3, 3, 5), (1, 3, 5, 0),
    (1, 5, 0, 3), (1, 5, 0, 5), (2, 3, 3, 3), (2, 3, 3, 4), (2, 3, 4, 0), (2, 4, 0, 0),
    (2, 5, 0, 4), (3, 0, 4, 2), (3, 0, 5, 1), (3, 1, 1, 1), (3, 2, 3, 3), (3, 2, 4, 3),
    (3, 2, 4, 5), (3, 3, 2, 3), (3, 3, 2, 5), (3, 3, 3, 1), (3, 4, 1, 0), (3, 4, 3, 1),
    (3, 5, 1, 4), (3, 5, 2, 3), (3, 5, 2, 5), (3, 5, 3, 2), (4, 0, 0, 1), (4, 0, 1, 3),
    (4, 0, 1, 5), (4, 1, 3, 3), (4, 1, 4, 3), (4, 1, 4, 5), (4, 4, 2, 4), (4, 5, 1, 4),
    (5, 0, 4, 2), (5, 2, 1, 1), (5, 2, 3, 3), (5, 2, 4, 3), (5, 2, 4, 5), (5, 3, 2, 3),
    (5, 3, 2, 5), (5, 3, 3, 2), (5, 3, 5, 1), (5, 4, 1, 0), (5, 4, 3, 1), (5, 4, 5, 1),
    (5, 5, 2, 0), (5, 5, 3, 2), (5, 5, 5, 2) ]

theorem portfolioPat4_indep : gamma6QuadListIndepBool portfolioPat4 = true := by decide

-- 10 standard `prodStd` cores: k = 1, 2, 3, 4, 5, 6, 8, 9, 14, 22
-- Reusing frontierNode0..4 for k = 1, 2, 3, 4, 5!
abbrev portProf1  : AsymProfile := frontierProf0
abbrev portProf2  : AsymProfile := frontierProf1
abbrev portProf3  : AsymProfile := frontierProf2
abbrev portProf4  : AsymProfile := frontierProf3
abbrev portProf5  : AsymProfile := frontierProf4
def portProf6  : AsymProfile := portProf2.prodAligned portProf4
def portProf8  : AsymProfile := portProf4.prodAligned portProf4
def portProf9  : AsymProfile := portProf3.prodAligned portProf6
def portProf14 : AsymProfile := portProf5.prodAligned portProf9
def portProf22 : AsymProfile := portProf8.prodAligned portProf14

noncomputable abbrev portNode1 : PartGadget (strongPow C7 5)  := frontierNode0
noncomputable abbrev portNode2 : PartGadget (strongPow C7 10) := frontierNode1
noncomputable abbrev portNode3 : PartGadget (strongPow C7 15) := frontierNode2
noncomputable abbrev portNode4 : PartGadget (strongPow C7 20) := frontierNode3
noncomputable abbrev portNode5 : PartGadget (strongPow C7 25) := frontierNode4

noncomputable def portNode6 : PartGadget (strongPow C7 30) :=
  (portNode2.prodStd portNode4).mapIso (strongPowAddEquiv C7 10 20).symm

noncomputable def portNode8 : PartGadget (strongPow C7 40) :=
  (portNode4.prodStd portNode4).mapIso (strongPowAddEquiv C7 20 20).symm

noncomputable def portNode9 : PartGadget (strongPow C7 45) :=
  (portNode3.prodStd portNode6).mapIso (strongPowAddEquiv C7 15 30).symm

noncomputable def portNode14 : PartGadget (strongPow C7 70) :=
  (portNode5.prodStd portNode9).mapIso (strongPowAddEquiv C7 25 45).symm

noncomputable def portNode22 : PartGadget (strongPow C7 110) :=
  (portNode8.prodStd portNode14).mapIso (strongPowAddEquiv C7 40 70).symm

theorem portNode1_prof  : portNode1.asymProfile  = portProf1  := frontierNode0_profile
theorem portNode2_prof  : portNode2.asymProfile  = portProf2  := frontierNode1_profile
theorem portNode3_prof  : portNode3.asymProfile  = portProf3  := frontierNode2_profile
theorem portNode4_prof  : portNode4.asymProfile  = portProf4  := frontierNode3_profile
theorem portNode5_prof  : portNode5.asymProfile  = portProf5  := frontierNode4_profile

theorem portNode6_prof : portNode6.asymProfile = portProf6 := by
  rw [portNode6, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    portNode2_prof, portNode4_prof]; rfl

theorem portNode8_prof : portNode8.asymProfile = portProf8 := by
  rw [portNode8, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    portNode4_prof]; rfl

theorem portNode9_prof : portNode9.asymProfile = portProf9 := by
  rw [portNode9, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    portNode3_prof, portNode6_prof]; rfl

theorem portNode14_prof : portNode14.asymProfile = portProf14 := by
  rw [portNode14, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    portNode5_prof, portNode9_prof]; rfl

theorem portNode22_prof : portNode22.asymProfile = portProf22 := by
  rw [portNode22, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    portNode8_prof, portNode14_prof]; rfl

-- Intermediate boosted independence-number lower bounds M2, M4, M6, M9, M14
def portM2  : ℕ := portProf2.a
def portM4  : ℕ := gamma6QuadListWeight portProf1 portProf1 portProf1 portProf1 portfolioPat4
def portM6  : ℕ := gamma6TripleListWeight portProf2 portProf2 portProf2 portfolioPat3
def portM9  : ℕ := gamma6TripleListWeight portProf3 portProf3 portProf3 portfolioPat3
def portM14 : ℕ := gamma6TripleListWeight portProf4 portProf5 portProf5 portfolioPat3

theorem portM2_le : portM2 ≤ (strongPow C7 10).indepNum := by
  have h := portNode2.card_le_indepNum; rwa [portNode2_prof] at h

theorem portM4_le : portM4 ≤ (strongPow C7 20).indepNum := by
  have h := gamma6Pow4_card_le_strongPow_indepNum portNode1 portNode1 portNode1 portNode1
    portfolioPat4 portfolioPat4_indep
  rwa [portNode1_prof] at h

theorem portM6_le : portM6 ≤ (strongPow C7 30).indepNum := by
  have h := gamma6Pow3_card_le_strongPow_indepNum portNode2 portNode2 portNode2
    portfolioPat3 portfolioPat3_indep
  rwa [portNode2_prof] at h

theorem portM9_le : portM9 ≤ (strongPow C7 45).indepNum := by
  have h := gamma6Pow3_card_le_strongPow_indepNum portNode3 portNode3 portNode3
    portfolioPat3 portfolioPat3_indep
  rwa [portNode3_prof] at h

theorem portM14_le : portM14 ≤ (strongPow C7 70).indepNum := by
  have h := gamma6Pow3_card_le_strongPow_indepNum portNode4 portNode5 portNode5
    portfolioPat3 portfolioPat3_indep
  rwa [portNode4_prof, portNode5_prof] at h

-- Decoupled upgraded auxiliary triples `(d, h, v)` via recursive `upg1FreeJ`
def upgTriple (p : AsymProfile) (a : ℕ × ℕ × ℕ) (M : ℕ) : ℕ × ℕ × ℕ :=
  (p.d * a.1, p.d * a.2.1 + p.h * M, p.d * a.2.2 + p.v * M)

def portAux2  : ℕ × ℕ × ℕ := (portProf2.d, portProf2.h, portProf2.v)
def portAux4  : ℕ × ℕ × ℕ := upgTriple portProf2 portAux2  portM2
def portAux6  : ℕ × ℕ × ℕ := upgTriple portProf2 portAux4  portM4
def portAux9  : ℕ × ℕ × ℕ := upgTriple portProf3 portAux6  portM6
def portAux14 : ℕ × ℕ × ℕ := upgTriple portProf5 portAux9  portM9
def portAux22 : ℕ × ℕ × ℕ := upgTriple portProf8 portAux14 portM14

theorem exists_portAux2 :
    ∃ a : AuxPartition portNode2.core,
      portAux2.1 ≤ a.O.card ∧ portAux2.2.1 ≤ a.H.card ∧ portAux2.2.2 ≤ a.V.card :=
  ⟨portNode2.aux,
    le_of_eq (congrArg AsymProfile.d portNode2_prof).symm,
    le_of_eq (congrArg AsymProfile.h portNode2_prof).symm,
    le_of_eq (congrArg AsymProfile.v portNode2_prof).symm⟩

theorem exists_portAux4 :
    ∃ a : AuxPartition portNode4.core,
      portAux4.1 ≤ a.O.card ∧ portAux4.2.1 ≤ a.H.card ∧ portAux4.2.2 ≤ a.V.card :=
  AuxPartition.exists_upg1FreeJ_iso portNode2 portNode2 (strongPowAddEquiv C7 10 10).symm
    (congrArg AsymProfile.d portNode2_prof)
    (congrArg AsymProfile.h portNode2_prof)
    (congrArg AsymProfile.v portNode2_prof)
    exists_portAux2 portM2_le

theorem exists_portAux6 :
    ∃ a : AuxPartition portNode6.core,
      portAux6.1 ≤ a.O.card ∧ portAux6.2.1 ≤ a.H.card ∧ portAux6.2.2 ≤ a.V.card :=
  AuxPartition.exists_upg1FreeJ_iso portNode2 portNode4 (strongPowAddEquiv C7 10 20).symm
    (congrArg AsymProfile.d portNode2_prof)
    (congrArg AsymProfile.h portNode2_prof)
    (congrArg AsymProfile.v portNode2_prof)
    exists_portAux4 portM4_le

theorem exists_portAux9 :
    ∃ a : AuxPartition portNode9.core,
      portAux9.1 ≤ a.O.card ∧ portAux9.2.1 ≤ a.H.card ∧ portAux9.2.2 ≤ a.V.card :=
  AuxPartition.exists_upg1FreeJ_iso portNode3 portNode6 (strongPowAddEquiv C7 15 30).symm
    (congrArg AsymProfile.d portNode3_prof)
    (congrArg AsymProfile.h portNode3_prof)
    (congrArg AsymProfile.v portNode3_prof)
    exists_portAux6 portM6_le

theorem exists_portAux14 :
    ∃ a : AuxPartition portNode14.core,
      portAux14.1 ≤ a.O.card ∧ portAux14.2.1 ≤ a.H.card ∧ portAux14.2.2 ≤ a.V.card :=
  AuxPartition.exists_upg1FreeJ_iso portNode5 portNode9 (strongPowAddEquiv C7 25 45).symm
    (congrArg AsymProfile.d portNode5_prof)
    (congrArg AsymProfile.h portNode5_prof)
    (congrArg AsymProfile.v portNode5_prof)
    exists_portAux9 portM9_le

theorem exists_portAux22 :
    ∃ a : AuxPartition portNode22.core,
      portAux22.1 ≤ a.O.card ∧ portAux22.2.1 ≤ a.H.card ∧ portAux22.2.2 ≤ a.V.card :=
  AuxPartition.exists_upg1FreeJ_iso portNode8 portNode14 (strongPowAddEquiv C7 40 70).symm
    (congrArg AsymProfile.d portNode8_prof)
    (congrArg AsymProfile.h portNode8_prof)
    (congrArg AsymProfile.v portNode8_prof)
    exists_portAux14 portM14_le

/-! ## 4. Certified Pure-Kernel Portfolio Frontier Bound (`d = 220`, 113-Digit Witness) -/

/-- Exact 113-digit cardinality certified in `C₇^⊠220` via Decoupled Portfolio Free-J + `Γ₆^⊠3`/`Γ₆^⊠4`. -/
def portfolioCard : ℕ :=
  74732706807043919643697829190664893546186880071325260826072346221160104101520910506260341279794670838950095660097

def portfolioCardExpr : ℕ :=
  (portProf22.a - portProf22.b) * (portProf22.a - portProf22.b) +
    portProf22.b * (portAux22.1 + portAux22.2.1 + portAux22.2.2) +
    (portAux22.1 + portAux22.2.1 + portAux22.2.2) * portProf22.b

theorem portfolioCardExpr_eq : portfolioCardExpr = portfolioCard := rfl

theorem portfolioCard_le_indepNum :
    portfolioCard ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 220).indepNum := by
  rcases exists_portAux22 with ⟨a22, hd22, hh22, hv22⟩
  let g22 : PartGadget (strongPow C7 110) := ⟨portNode22.core, a22⟩
  let g44 : PartGadget (strongPow C7 220) :=
    (g22.prodStd g22).mapIso (strongPowAddEquiv C7 110 110).symm
  have ha : g22.asymProfile.a = portProf22.a := by
    change portNode22.asymProfile.a = portProf22.a
    exact congrArg AsymProfile.a portNode22_prof
  have hb : g22.asymProfile.b = portProf22.b := by
    change portNode22.asymProfile.b = portProf22.b
    exact congrArg AsymProfile.b portNode22_prof
  have hc : portAux22.1 + portAux22.2.1 + portAux22.2.2 ≤ g22.asymProfile.c := by
    change portAux22.1 + portAux22.2.1 + portAux22.2.2 ≤ a22.O.card + a22.H.card + a22.V.card
    omega
  have hg44_a : g44.asymProfile.a =
      (g22.asymProfile.a - g22.asymProfile.b) * (g22.asymProfile.a - g22.asymProfile.b) +
      g22.asymProfile.b * g22.asymProfile.c + g22.asymProfile.c * g22.asymProfile.b := by
    rw [PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile]
    exact (AsymProfile.prodAligned_eq g22.asymProfile g22.asymProfile).1
  have hle_a : portfolioCard ≤ g44.asymProfile.a := by
    rw [← portfolioCardExpr_eq, portfolioCardExpr, hg44_a, ha, hb]
    have h1 := Nat.mul_le_mul_left portProf22.b hc
    have h2 := Nat.mul_le_mul_right portProf22.b hc
    omega
  have h1 : portfolioCard ≤ (strongPow C7 220).indepNum := hle_a.trans g44.card_le_indepNum
  have h2 : (strongPow C7 220).indepNum =
      (strongPowPi (SimpleGraph.cycleGraph 7) 220).indepNum := by
    rw [iso_indepNum_eq (strongPowCongr c7IsoCycleGraph 220), strongPow_indepNum_eq_pi]
  omega

/-- Numerator of our decoupled-portfolio pure-kernel lower bound on `Θ(C₇)` (`d = 220`). -/
def c7_portfolio_num : ℕ := 3258827798879807

/-- Denominator of our decoupled-portfolio pure-kernel lower bound on `Θ(C₇)`. -/
def c7_portfolio_den : ℕ := 1000000000000000

theorem c7_portfolio_den_pos : 0 < c7_portfolio_den := by decide

set_option exponentiation.threshold 4096 in
theorem portfolio_pow_le :
    c7_portfolio_num ^ 220 ≤ c7_portfolio_den ^ 220 * portfolioCard :=
  nat_pow_le_of_ble rfl

/-- **Pure-Kernel Decoupled Portfolio Lower Bound on `Θ(C₇)` (`d = 220`):**
`3258827798879807 / 1000000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7)`. -/
theorem c7_lower_portfolio :
    (c7_portfolio_num : ℝ) / (c7_portfolio_den : ℝ) ≤
      shannonCapacity (SimpleGraph.cycleGraph 7) :=
  le_shannonCapacity_of_nat_pow_pi (by decide) c7_portfolio_den_pos
    portfolioCard_le_indepNum portfolio_pow_le

/-- Strictly surpasses M4's `c7_lower_frontier` (`3.258822357711717`) by `+5.441e-6` at `d = 220`. -/
theorem c7_lower_portfolio_gt_frontier :
    (c7_lower_num : ℝ) / (c7_lower_den : ℝ) <
      (c7_portfolio_num : ℝ) / (c7_portfolio_den : ℝ) := by
  rw [div_lt_div_iff₀ (by exact_mod_cast c7_lower_den_pos) (by exact_mod_cast c7_portfolio_den_pos)]
  exact_mod_cast (by decide : c7_lower_num * c7_portfolio_den < c7_portfolio_num * c7_lower_den)

end ShannonC7
