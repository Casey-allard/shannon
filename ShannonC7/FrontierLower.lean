import ShannonC7.ValidTuple
import ShannonC7.HeteroLayered
import ShannonC7.Decimal

/-!
# Frontier Pure-Kernel Lower Bound on `Θ(C₇)` via `AuxPartition` / `PartGadget`

Deterministically emitted from verified witness `frontier_c7_d220_partgadget`
(canonical SHA-256: `a39bac075f93dfcac8db163866babf068e13fefd4a7290b1630a664cc63f9e8d`).

100% pure Lean 4 kernel (`{propext, Classical.choice, Quot.sound}` only — zero `sorry`,
zero `native_decide`, zero private-symbol leaks):
- Generalizes `AuxCode` / `HeteroGadget` to `AuxPartition` / `PartGadget`, requiring only
  pairwise non-closeness of `(O, H, V)` and the four avoidance invariants (`O` avoids
  `P0, P1`; `H` avoids `P1`; `V` avoids `P0`).
- Proves exact aligned-product `PartGadget` operators `prodStd`, `prodXupg1`, and
  `prodXupg2`, where `prodXupg1`/`prodXupg2` upgrade `(H ∪ V) × X` to
  `H × (B ∪ P0) ∪ V × (B ∪ P1)`, strictly breaking the `c_k = 367^k` stagnation barrier
  with zero new 5D trie witnesses.
- Generalizes the 6-vertex quotient graph `Γ₆` and 4-fold pullback theorem
  `gamma6Pow4_card_le_cycleGraph7_indepNum` directly to `PartGadget`.
- Instantiates a 11-node shared `PartGadget` DAG from M3 `baseHetero5D` (`d = 220`),
  certifying `3258822357711717 / 1000000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7)`.
-/

namespace ShannonC7

/-! ## 1. Auxiliary Helpers, `AuxPartition`, & `PartGadget` -/

theorem AsymProfile.ext {p q : AsymProfile}
    (ha : p.a = q.a) (hb : p.b = q.b) (hc : p.c = q.c)
    (hd : p.d = q.d) (hh : p.h = q.h) (hv : p.v = q.v) : p = q := by
  cases p; cases q
  simp only [AsymProfile.mk.injEq]
  exact ⟨ha, hb, hc, hd, hh, hv⟩

/-- Fast cardinality of a 3-way pairwise disjoint Finset union. -/
theorem card_union3 {α : Type*} [DecidableEq α] {A0 A1 A2 : Finset α}
    (d01 : Disjoint A0 A1) (d02 : Disjoint A0 A2) (d12 : Disjoint A1 A2) :
    (A0 ∪ A1 ∪ A2).card = A0.card + A1.card + A2.card := by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d02, d12⟩),
      Finset.card_union_of_disjoint d01]

/-- Independence of a 3-way pairwise non-close Finset union. -/
theorem isIndepSet_union3 {α : Type*} [DecidableEq α] {G : SimpleGraph α}
    {A0 A1 A2 : Finset α}
    (i0 : G.IsIndepSet (A0 : Set α)) (i1 : G.IsIndepSet (A1 : Set α))
    (i2 : G.IsIndepSet (A2 : Set α))
    (h01 : ∀ x ∈ A0, ∀ y ∈ A1, ¬ (x = y ∨ G.Adj x y))
    (h02 : ∀ x ∈ A0, ∀ y ∈ A2, ¬ (x = y ∨ G.Adj x y))
    (h12 : ∀ x ∈ A1, ∀ y ∈ A2, ¬ (x = y ∨ G.Adj x y)) :
    G.IsIndepSet ((A0 ∪ A1 ∪ A2 : Finset α) : Set α) := by
  have hi01 := isIndepSet_union_of_not_close i0 i1 h01
  exact isIndepSet_union_of_not_close hi01 i2 fun x hx y hy => by
    rcases Finset.mem_union.mp hx with h | h
    · exact h02 x h y hy
    · exact h12 x h y hy

theorem portCore_mem_mapIso_P0 {α β : Type*} [Fintype α] [Fintype β]
    {G : SimpleGraph α} {H : SimpleGraph β} (e : G ≃g H) (c : PortCore G) {y : β} :
    y ∈ (c.mapIso e).P0 ↔ ∃ p ∈ c.P0, e p = y := by
  simp only [PortCore.mem_P0, PortCore.mapIso, Finset.mem_map,
    Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv]
  constructor
  · rintro ⟨w, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨c.f0 s, ⟨s, hs, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨e s, ⟨s, hs, rfl⟩, by simp⟩

theorem portCore_mem_mapIso_P1 {α β : Type*} [Fintype α] [Fintype β]
    {G : SimpleGraph α} {H : SimpleGraph β} (e : G ≃g H) (c : PortCore G) {y : β} :
    y ∈ (c.mapIso e).P1 ↔ ∃ p ∈ c.P1, e p = y := by
  simp only [PortCore.mem_P1, PortCore.mapIso, Finset.mem_map,
    Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv]
  constructor
  · rintro ⟨w, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨c.f1 s, ⟨s, hs, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨e s, ⟨s, hs, rfl⟩, by simp⟩

set_option linter.unusedFintypeInType false in
/-- Generalized 3-way auxiliary partition `(O, H, V)` compatible with a `PortCore G`.
Unlike `AuxCode`, `H` is not forced into `N[P0]` and `V` is not forced into `N[P1]`;
only pairwise non-closeness of `O, H, V` and avoidance of the opposite ports are required. -/
structure AuxPartition {α : Type*} [Fintype α] {G : SimpleGraph α} (core : PortCore G) where
  O : Finset α
  H : Finset α
  V : Finset α
  indep_O : G.IsIndepSet (O : Set α)
  indep_H : G.IsIndepSet (H : Set α)
  indep_V : G.IsIndepSet (V : Set α)
  not_close_OH : ∀ x ∈ O, ∀ y ∈ H, ¬ (x = y ∨ G.Adj x y)
  not_close_OV : ∀ x ∈ O, ∀ y ∈ V, ¬ (x = y ∨ G.Adj x y)
  not_close_HV : ∀ x ∈ H, ∀ y ∈ V, ¬ (x = y ∨ G.Adj x y)
  not_close_P0_O : ∀ p ∈ core.P0, ∀ o ∈ O, ¬ (p = o ∨ G.Adj p o)
  not_close_P1_O : ∀ p ∈ core.P1, ∀ o ∈ O, ¬ (p = o ∨ G.Adj p o)
  not_close_P1_H : ∀ p ∈ core.P1, ∀ h ∈ H, ¬ (p = h ∨ G.Adj p h)
  not_close_P0_V : ∀ p ∈ core.P0, ∀ v ∈ V, ¬ (p = v ∨ G.Adj p v)

set_option linter.unusedFintypeInType false in
/-- Partitioned gadget pairing a `PortCore G` with an `AuxPartition core`. -/
structure PartGadget {α : Type*} [Fintype α] (G : SimpleGraph α) where
  core : PortCore G
  aux : AuxPartition core

/-- Profile law for `PartGadget.prodXupg1` (left auxiliary upgraded via right core `B ∪ P0/P1`). -/
def AsymProfile.prodXupg1 (p q : AsymProfile) : AsymProfile where
  a := (p.a - p.b) * (q.a - q.b) + p.b * q.c + p.c * q.b
  b := p.b * q.d + p.d * q.b
  c := p.d * q.c + (p.h + p.v) * q.a
  d := p.d * q.d + (p.h + p.v) * q.b
  h := p.d * q.h + p.h * (q.a - q.b)
  v := p.d * q.v + p.v * (q.a - q.b)
  hba := by
    have h1 : p.b * q.d ≤ p.b * q.c := Nat.mul_le_mul_left p.b q.hdc
    have h2 : p.d * q.b ≤ p.c * q.b := Nat.mul_le_mul_right q.b p.hdc
    omega
  hdhv := by
    have hq := q.hdhv; have hqb := q.hba
    have hsub : q.b + (q.a - q.b) = q.a := by omega
    nlinarith

/-- Profile law for `PartGadget.prodXupg2` (right auxiliary upgraded via left core `B ∪ P0/P1`). -/
def AsymProfile.prodXupg2 (p q : AsymProfile) : AsymProfile where
  a := (p.a - p.b) * (q.a - q.b) + p.b * q.c + p.c * q.b
  b := p.b * q.d + p.d * q.b
  c := p.c * q.d + p.a * (q.h + q.v)
  d := p.d * q.d + p.b * (q.h + q.v)
  h := p.h * q.d + (p.a - p.b) * q.h
  v := p.v * q.d + (p.a - p.b) * q.v
  hba := by
    have h1 : p.b * q.d ≤ p.b * q.c := Nat.mul_le_mul_left p.b q.hdc
    have h2 : p.d * q.b ≤ p.c * q.b := Nat.mul_le_mul_right q.b p.hdc
    omega
  hdhv := by
    have hp := p.hdhv; have hpb := p.hba
    have hsub : p.b + (p.a - p.b) = p.a := by omega
    nlinarith

namespace PartGadget

variable {α β : Type*} [Fintype α] [Fintype β] {G : SimpleGraph α} {H : SimpleGraph β}

noncomputable def asymProfile (g : PartGadget G) : AsymProfile where
  a := g.core.I.card
  b := g.core.S.card
  c := g.aux.O.card + g.aux.H.card + g.aux.V.card
  d := g.aux.O.card
  h := g.aux.H.card
  v := g.aux.V.card
  hba := g.core.card_S_le_I
  hdhv := rfl

theorem card_le_indepNum (g : PartGadget G) : g.asymProfile.a ≤ G.indepNum :=
  g.core.indep_I.card_le_indepNum

theorem not_close_S_O (g : PartGadget G) {s o : α}
    (hs : s ∈ g.core.S) (ho : o ∈ g.aux.O) : ¬ (s = o ∨ G.Adj s o) := by
  rcases g.core.self_mem s hs with h0 | h1
  · exact g.aux.not_close_P0_O s (g.core.mem_P0.mpr ⟨s, hs, h0⟩) o ho
  · exact g.aux.not_close_P1_O s (g.core.mem_P1.mpr ⟨s, hs, h1⟩) o ho

theorem not_mem_S_of_mem_O (g : PartGadget G) {x : α} (hx : x ∈ g.aux.O) : x ∉ g.core.S :=
  fun hs => g.not_close_S_O hs hx (Or.inl rfl)

/-- Every `HeteroGadget G` converts canonically into a `PartGadget G` with identical profile. -/
noncomputable def ofHeteroGadget (g : HeteroGadget G) : PartGadget G where
  core := g.core
  aux :=
    { O := g.aux.OSlice
      H := g.aux.HSlice
      V := g.aux.VSlice
      indep_O := isIndepSet_subset g.aux.indep_X (fun _ hx => (g.aux.mem_OSlice.mp hx).1)
      indep_H := isIndepSet_subset g.aux.indep_X (fun _ hx => (g.aux.mem_HSlice.mp hx).1)
      indep_V := isIndepSet_subset g.aux.indep_X (fun _ hx => (g.aux.mem_VSlice.mp hx).1)
      not_close_OH := fun _ ho _ hh => HeteroGadget.not_close_OSlice_HSlice g ho hh
      not_close_OV := fun _ ho _ hv => HeteroGadget.not_close_OSlice_VSlice g ho hv
      not_close_HV := fun _ hh _ hv => HeteroGadget.not_close_HSlice_VSlice g hh hv
      not_close_P0_O := fun _ hp _ ho => HeteroGadget.not_close_P0_OSlice g hp ho
      not_close_P1_O := fun _ hp _ ho => HeteroGadget.not_close_P1_OSlice g hp ho
      not_close_P1_H := fun _ hp _ hh => HeteroGadget.not_close_P1_HSlice g hp hh
      not_close_P0_V := fun _ hp _ hv => HeteroGadget.not_close_P0_VSlice g hp hv }

theorem ofHeteroGadget_asymProfile (g : HeteroGadget G) :
    (ofHeteroGadget g).asymProfile = g.asymProfile :=
  AsymProfile.ext rfl rfl (AuxCode.card_partition g.aux) rfl rfl rfl

/-- Swap ports `P0 ↔ P1` and auxiliary slices `H ↔ V`. -/
def flip (g : PartGadget G) : PartGadget G where
  core := g.core.flip
  aux :=
    { O := g.aux.O, H := g.aux.V, V := g.aux.H
      indep_O := g.aux.indep_O, indep_H := g.aux.indep_V, indep_V := g.aux.indep_H
      not_close_OH := g.aux.not_close_OV
      not_close_OV := g.aux.not_close_OH
      not_close_HV := fun x hx y hy hc => g.aux.not_close_HV y hy x hx (close_symm hc)
      not_close_P0_O := fun p hp o ho =>
        g.aux.not_close_P1_O p (g.core.mem_P1.mpr (g.core.flip.mem_P0.mp hp)) o ho
      not_close_P1_O := fun p hp o ho =>
        g.aux.not_close_P0_O p (g.core.mem_P0.mpr (g.core.flip.mem_P1.mp hp)) o ho
      not_close_P1_H := fun p hp v hv =>
        g.aux.not_close_P0_V p (g.core.mem_P0.mpr (g.core.flip.mem_P1.mp hp)) v hv
      not_close_P0_V := fun p hp h hh =>
        g.aux.not_close_P1_H p (g.core.mem_P1.mpr (g.core.flip.mem_P0.mp hp)) h hh }

theorem flip_asymProfile (g : PartGadget G) : g.flip.asymProfile = g.asymProfile.flip :=
  AsymProfile.ext rfl rfl (by simp only [asymProfile, flip, AsymProfile.flip]; omega) rfl rfl rfl

/-- Transport a `PartGadget G` along a graph isomorphism `e : G ≃g H`. -/
def mapIso (e : G ≃g H) (g : PartGadget G) : PartGadget H where
  core := g.core.mapIso e
  aux :=
    { O := g.aux.O.map e.toEquiv.toEmbedding
      H := g.aux.H.map e.toEquiv.toEmbedding
      V := g.aux.V.map e.toEquiv.toEmbedding
      indep_O := isIndepSet_map_iso e g.aux.indep_O
      indep_H := isIndepSet_map_iso e g.aux.indep_H
      indep_V := isIndepSet_map_iso e g.aux.indep_V
      not_close_OH := fun _ hx _ hy hc => by
        rcases Finset.mem_map.mp hx with ⟨x, hx', rfl⟩
        rcases Finset.mem_map.mp hy with ⟨y, hy', rfl⟩
        exact g.aux.not_close_OH x hx' y hy' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)
      not_close_OV := fun _ hx _ hy hc => by
        rcases Finset.mem_map.mp hx with ⟨x, hx', rfl⟩
        rcases Finset.mem_map.mp hy with ⟨y, hy', rfl⟩
        exact g.aux.not_close_OV x hx' y hy' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)
      not_close_HV := fun _ hx _ hy hc => by
        rcases Finset.mem_map.mp hx with ⟨x, hx', rfl⟩
        rcases Finset.mem_map.mp hy with ⟨y, hy', rfl⟩
        exact g.aux.not_close_HV x hx' y hy' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)
      not_close_P0_O := fun _ hp _ ho hc => by
        rcases (portCore_mem_mapIso_P0 e g.core).mp hp with ⟨p, hp', rfl⟩
        rcases Finset.mem_map.mp ho with ⟨o, ho', rfl⟩
        exact g.aux.not_close_P0_O p hp' o ho' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)
      not_close_P1_O := fun _ hp _ ho hc => by
        rcases (portCore_mem_mapIso_P1 e g.core).mp hp with ⟨p, hp', rfl⟩
        rcases Finset.mem_map.mp ho with ⟨o, ho', rfl⟩
        exact g.aux.not_close_P1_O p hp' o ho' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)
      not_close_P1_H := fun _ hp _ hh hc => by
        rcases (portCore_mem_mapIso_P1 e g.core).mp hp with ⟨p, hp', rfl⟩
        rcases Finset.mem_map.mp hh with ⟨h, hh', rfl⟩
        exact g.aux.not_close_P1_H p hp' h hh' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp)
      not_close_P0_V := fun _ hp _ hv hc => by
        rcases (portCore_mem_mapIso_P0 e g.core).mp hp with ⟨p, hp', rfl⟩
        rcases Finset.mem_map.mp hv with ⟨v, hv', rfl⟩
        exact g.aux.not_close_P0_V p hp' v hv' (hc.imp (fun h => e.injective h) e.map_adj_iff.mp) }

theorem mapIso_asymProfile (e : G ≃g H) (g : PartGadget G) :
    (g.mapIso e).asymProfile = g.asymProfile :=
  AsymProfile.ext (Finset.card_map _) (Finset.card_map _)
    (by simp only [asymProfile, mapIso, Finset.card_map])
    (Finset.card_map _) (Finset.card_map _) (Finset.card_map _)

/-! ### Shared Aligned Product Core (`prodAlignedI`, `prodAlignedCore`) -/

/-- The 7-piece aligned-product main independent set of two `PartGadget`s. -/
noncomputable def prodAlignedI (g1 : PartGadget G) (g2 : PartGadget H) : Finset (α × β) := by
  classical
  exact
    (g1.core.B ×ˢ g2.core.B) ∪
    (g1.core.S ×ˢ g2.aux.O) ∪
    (g1.core.P0 ×ˢ g2.aux.V) ∪
    (g1.core.P1 ×ˢ g2.aux.H) ∪
    (g1.aux.O ×ˢ g2.core.S) ∪
    (g1.aux.H ×ˢ g2.core.P0) ∪
    (g1.aux.V ×ˢ g2.core.P1)

theorem prodAlignedI_indep_and_card (g1 : PartGadget G) (g2 : PartGadget H) :
    (G ⊠ H).IsIndepSet ((prodAlignedI g1 g2 : Finset (α × β)) : Set (α × β)) ∧
    (prodAlignedI g1 g2).card =
      (g1.core.I.card - g1.core.S.card) * (g2.core.I.card - g2.core.S.card) +
      g1.core.S.card * (g2.aux.O.card + g2.aux.H.card + g2.aux.V.card) +
      (g1.aux.O.card + g1.aux.H.card + g1.aux.V.card) * g2.core.S.card := by
  classical
  let A0 := g1.core.B ×ˢ g2.core.B
  let A1 := g1.core.S ×ˢ g2.aux.O
  let A2 := g1.core.P0 ×ˢ g2.aux.V
  let A3 := g1.core.P1 ×ˢ g2.aux.H
  let A4 := g1.aux.O ×ˢ g2.core.S
  let A5 := g1.aux.H ×ˢ g2.core.P0
  let A6 := g1.aux.V ×ˢ g2.core.P1
  have h01 : ∀ x ∈ A0, ∀ y ∈ A1, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A0, A1, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.core.not_close_B_S h₁.1 h₂.1)
  have h02 : ∀ x ∈ A0, ∀ y ∈ A2, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A0, A2, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.core.not_close_B_P0 h₁.1 h₂.1)
  have h03 : ∀ x ∈ A0, ∀ y ∈ A3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A0, A3, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.core.not_close_B_P1 h₁.1 h₂.1)
  have h04 : ∀ x ∈ A0, ∀ y ∈ A4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A0, A4, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (g2.core.not_close_B_S h₁.2 h₂.2)
  have h05 : ∀ x ∈ A0, ∀ y ∈ A5, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A0, A5, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (g2.core.not_close_B_P0 h₁.2 h₂.2)
  have h06 : ∀ x ∈ A0, ∀ y ∈ A6, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A0, A6, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (g2.core.not_close_B_P1 h₁.2 h₂.2)
  have h12 : ∀ x ∈ A1, ∀ y ∈ A2, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A1, A2, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (g2.aux.not_close_OV _ h₁.2 _ h₂.2)
  have h13 : ∀ x ∈ A1, ∀ y ∈ A3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A1, A3, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (g2.aux.not_close_OH _ h₁.2 _ h₂.2)
  have h14 : ∀ x ∈ A1, ∀ y ∈ A4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A1, A4, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.not_close_S_O h₁.1 h₂.1)
  have h15 : ∀ x ∈ A1, ∀ y ∈ A5, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A1, A5, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (fun hc => g2.aux.not_close_P0_O _ h₂.2 _ h₁.2 (close_symm hc))
  have h16 : ∀ x ∈ A1, ∀ y ∈ A6, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A1, A6, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (fun hc => g2.aux.not_close_P1_O _ h₂.2 _ h₁.2 (close_symm hc))
  have h23 : ∀ x ∈ A2, ∀ y ∈ A3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A2, A3, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (fun hc => g2.aux.not_close_HV _ h₂.2 _ h₁.2 (close_symm hc))
  have h24 : ∀ x ∈ A2, ∀ y ∈ A4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A2, A4, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_P0_O _ h₁.1 _ h₂.1)
  have h25 : ∀ x ∈ A2, ∀ y ∈ A5, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A2, A5, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (fun hc => g2.aux.not_close_P0_V _ h₂.2 _ h₁.2 (close_symm hc))
  have h26 : ∀ x ∈ A2, ∀ y ∈ A6, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A2, A6, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_P0_V _ h₁.1 _ h₂.1)
  have h34 : ∀ x ∈ A3, ∀ y ∈ A4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A3, A4, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_P1_O _ h₁.1 _ h₂.1)
  have h35 : ∀ x ∈ A3, ∀ y ∈ A5, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A3, A5, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_P1_H _ h₁.1 _ h₂.1)
  have h36 : ∀ x ∈ A3, ∀ y ∈ A6, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A3, A6, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (fun hc => g2.aux.not_close_P1_H _ h₂.2 _ h₁.2 (close_symm hc))
  have h45 : ∀ x ∈ A4, ∀ y ∈ A5, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A4, A5, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_OH _ h₁.1 _ h₂.1)
  have h46 : ∀ x ∈ A4, ∀ y ∈ A6, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A4, A6, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_OV _ h₁.1 _ h₂.1)
  have h56 : ∀ x ∈ A5, ∀ y ∈ A6, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A5, A6, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_HV _ h₁.1 _ h₂.1)
  refine ⟨?_, ?_⟩
  · exact isIndepSet_union7
      (isIndepSet_prod g1.core.indep_B g2.core.indep_B)
      (isIndepSet_prod g1.core.indep_S g2.aux.indep_O)
      (isIndepSet_prod g1.core.indep_P0_finset g2.aux.indep_V)
      (isIndepSet_prod g1.core.indep_P1_finset g2.aux.indep_H)
      (isIndepSet_prod g1.aux.indep_O g2.core.indep_S)
      (isIndepSet_prod g1.aux.indep_H g2.core.indep_P0_finset)
      (isIndepSet_prod g1.aux.indep_V g2.core.indep_P1_finset)
      h01 h02 h03 h04 h05 h06 h12 h13 h14 h15 h16 h23 h24 h25 h26 h34 h35 h36 h45 h46 h56
  · change (A0 ∪ A1 ∪ A2 ∪ A3 ∪ A4 ∪ A5 ∪ A6).card = _
    rw [card_union7 (disjoint_of_not_close h01) (disjoint_of_not_close h02)
      (disjoint_of_not_close h03) (disjoint_of_not_close h04) (disjoint_of_not_close h05)
      (disjoint_of_not_close h06) (disjoint_of_not_close h12) (disjoint_of_not_close h13)
      (disjoint_of_not_close h14) (disjoint_of_not_close h15) (disjoint_of_not_close h16)
      (disjoint_of_not_close h23) (disjoint_of_not_close h24) (disjoint_of_not_close h25)
      (disjoint_of_not_close h26) (disjoint_of_not_close h34) (disjoint_of_not_close h35)
      (disjoint_of_not_close h36) (disjoint_of_not_close h45) (disjoint_of_not_close h46)
      (disjoint_of_not_close h56)]
    simp only [A0, A1, A2, A3, A4, A5, A6, Finset.card_product,
      g1.core.card_B, g2.core.card_B, g1.core.card_P0, g1.core.card_P1,
      g2.core.card_P0, g2.core.card_P1]
    nlinarith

/-- Common aligned-product `PortCore (G ⊠ H)` shared by `prodStd`, `prodXupg1`, and `prodXupg2`. -/
noncomputable def prodAlignedCore (g1 : PartGadget G) (g2 : PartGadget H) : PortCore (G ⊠ H) := by
  classical
  refine
    { I := prodAlignedI g1 g2
      S := (g1.core.S ×ˢ g2.aux.O) ∪ (g1.aux.O ×ˢ g2.core.S)
      f0 := fun p => if p.1 ∈ g1.core.S then (g1.core.f0 p.1, p.2) else (p.1, g2.core.f0 p.2)
      f1 := fun p => if p.1 ∈ g1.core.S then (g1.core.f1 p.1, p.2) else (p.1, g2.core.f1 p.2)
      indep_I := (prodAlignedI_indep_and_card g1 g2).1
      S_sub_I := ?_
      priv0 := ?_
      priv1 := ?_
      indep_P0 := ?_
      indep_P1 := ?_
      self_mem := ?_ }
  · intro p hp
    simp only [prodAlignedI, Finset.mem_union] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))
    · exact Or.inl (Or.inl (Or.inr hp))
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_product.mp hp with ⟨hs1, ho2⟩
      simp only [hs1, ↓reduceIte]
      refine ⟨eq_or_strongProd_adj.mpr ⟨(g1.core.priv0 p.1 hs1).1, Or.inl rfl⟩, ?_⟩
      intro u hu hcu
      rcases eq_or_strongProd_adj.mp hcu with ⟨hc1, hc2⟩
      have hp0 : g1.core.f0 p.1 ∈ g1.core.P0 := g1.core.mem_P0.mpr ⟨p.1, hs1, rfl⟩
      simp only [prodAlignedI, Finset.mem_union, Finset.mem_product] at hu
      rcases hu with (((((⟨hu1, _⟩ | ⟨hu1, hu2⟩) | ⟨_, hu2⟩) | ⟨_, hu2⟩) | ⟨hu1, _⟩) | ⟨_, hu2⟩) | ⟨_, hu2⟩
      · exact absurd hc1 (g1.core.not_close_B_P0 hu1 hp0)
      · exact Prod.ext ((g1.core.priv0 p.1 hs1).2 u.1 (g1.core.S_sub_I hu1) hc1)
          (isIndepSet_eq_of_close g2.aux.indep_O hu2 ho2 hc2)
      · exact absurd (close_symm hc2) (g2.aux.not_close_OV _ ho2 _ hu2)
      · exact absurd (close_symm hc2) (g2.aux.not_close_OH _ ho2 _ hu2)
      · exact absurd (close_symm hc1) (g1.aux.not_close_P0_O _ hp0 _ hu1)
      · exact absurd hc2 (g2.aux.not_close_P0_O _ hu2 _ ho2)
      · exact absurd hc2 (g2.aux.not_close_P1_O _ hu2 _ ho2)
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      have hns1 : p.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1
      simp only [hns1, ↓reduceIte]
      refine ⟨eq_or_strongProd_adj.mpr ⟨Or.inl rfl, (g2.core.priv0 p.2 hs2).1⟩, ?_⟩
      intro u hu hcu
      rcases eq_or_strongProd_adj.mp hcu with ⟨hc1, hc2⟩
      have hp0 : g2.core.f0 p.2 ∈ g2.core.P0 := g2.core.mem_P0.mpr ⟨p.2, hs2, rfl⟩
      simp only [prodAlignedI, Finset.mem_union, Finset.mem_product] at hu
      rcases hu with (((((⟨_, hu2⟩ | ⟨hu1, _⟩) | ⟨hu1, _⟩) | ⟨hu1, _⟩) | ⟨hu1, hu2⟩) | ⟨hu1, _⟩) | ⟨hu1, _⟩
      · exact absurd hc2 (g2.core.not_close_B_P0 hu2 hp0)
      · exact absurd hc1 (g1.not_close_S_O hu1 ho1)
      · exact absurd hc1 (g1.aux.not_close_P0_O _ hu1 _ ho1)
      · exact absurd hc1 (g1.aux.not_close_P1_O _ hu1 _ ho1)
      · exact Prod.ext (isIndepSet_eq_of_close g1.aux.indep_O hu1 ho1 hc1)
          ((g2.core.priv0 p.2 hs2).2 u.2 (g2.core.S_sub_I hu2) hc2)
      · exact absurd (close_symm hc1) (g1.aux.not_close_OH _ ho1 _ hu1)
      · exact absurd (close_symm hc1) (g1.aux.not_close_OV _ ho1 _ hu1)
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_product.mp hp with ⟨hs1, ho2⟩
      simp only [hs1, ↓reduceIte]
      refine ⟨eq_or_strongProd_adj.mpr ⟨(g1.core.priv1 p.1 hs1).1, Or.inl rfl⟩, ?_⟩
      intro u hu hcu
      rcases eq_or_strongProd_adj.mp hcu with ⟨hc1, hc2⟩
      have hp1 : g1.core.f1 p.1 ∈ g1.core.P1 := g1.core.mem_P1.mpr ⟨p.1, hs1, rfl⟩
      simp only [prodAlignedI, Finset.mem_union, Finset.mem_product] at hu
      rcases hu with (((((⟨hu1, _⟩ | ⟨hu1, hu2⟩) | ⟨_, hu2⟩) | ⟨_, hu2⟩) | ⟨hu1, _⟩) | ⟨_, hu2⟩) | ⟨_, hu2⟩
      · exact absurd hc1 (g1.core.not_close_B_P1 hu1 hp1)
      · exact Prod.ext ((g1.core.priv1 p.1 hs1).2 u.1 (g1.core.S_sub_I hu1) hc1)
          (isIndepSet_eq_of_close g2.aux.indep_O hu2 ho2 hc2)
      · exact absurd (close_symm hc2) (g2.aux.not_close_OV _ ho2 _ hu2)
      · exact absurd (close_symm hc2) (g2.aux.not_close_OH _ ho2 _ hu2)
      · exact absurd (close_symm hc1) (g1.aux.not_close_P1_O _ hp1 _ hu1)
      · exact absurd hc2 (g2.aux.not_close_P0_O _ hu2 _ ho2)
      · exact absurd hc2 (g2.aux.not_close_P1_O _ hu2 _ ho2)
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      have hns1 : p.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1
      simp only [hns1, ↓reduceIte]
      refine ⟨eq_or_strongProd_adj.mpr ⟨Or.inl rfl, (g2.core.priv1 p.2 hs2).1⟩, ?_⟩
      intro u hu hcu
      rcases eq_or_strongProd_adj.mp hcu with ⟨hc1, hc2⟩
      have hp1 : g2.core.f1 p.2 ∈ g2.core.P1 := g2.core.mem_P1.mpr ⟨p.2, hs2, rfl⟩
      simp only [prodAlignedI, Finset.mem_union, Finset.mem_product] at hu
      rcases hu with (((((⟨_, hu2⟩ | ⟨hu1, _⟩) | ⟨hu1, _⟩) | ⟨hu1, _⟩) | ⟨hu1, hu2⟩) | ⟨hu1, _⟩) | ⟨hu1, _⟩
      · exact absurd hc2 (g2.core.not_close_B_P1 hu2 hp1)
      · exact absurd hc1 (g1.not_close_S_O hu1 ho1)
      · exact absurd hc1 (g1.aux.not_close_P0_O _ hu1 _ ho1)
      · exact absurd hc1 (g1.aux.not_close_P1_O _ hu1 _ ho1)
      · exact Prod.ext (isIndepSet_eq_of_close g1.aux.indep_O hu1 ho1 hc1)
          ((g2.core.priv1 p.2 hs2).2 u.2 (g2.core.S_sub_I hu2) hc2)
      · exact absurd (close_symm hc1) (g1.aux.not_close_OH _ ho1 _ hu1)
      · exact absurd (close_symm hc1) (g1.aux.not_close_OV _ ho1 _ hu1)
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne hadj
    rcases eq_or_strongProd_adj.mp (Or.inr hadj) with ⟨hc1, hc2⟩
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · rcases Finset.mem_product.mp hp with ⟨hs1, ho2⟩
      rcases Finset.mem_product.mp hq with ⟨hs1', ho2'⟩
      simp only [hs1, hs1', ↓reduceIte] at hne hc1 hc2
      exact hne (Prod.ext
        (isIndepSet_eq_of_close g1.core.indep_P0_finset
          (g1.core.mem_P0.mpr ⟨p.1, hs1, rfl⟩) (g1.core.mem_P0.mpr ⟨q.1, hs1', rfl⟩) hc1)
        (isIndepSet_eq_of_close g2.aux.indep_O ho2 ho2' hc2))
    · rcases Finset.mem_product.mp hp with ⟨hs1, _⟩
      rcases Finset.mem_product.mp hq with ⟨ho1', _⟩
      have hns1' : q.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1'
      simp only [hs1, hns1', ↓reduceIte] at hc1
      exact g1.aux.not_close_P0_O _ (g1.core.mem_P0.mpr ⟨p.1, hs1, rfl⟩) _ ho1' hc1
    · rcases Finset.mem_product.mp hp with ⟨ho1, _⟩
      rcases Finset.mem_product.mp hq with ⟨hs1', _⟩
      have hns1 : p.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1
      simp only [hns1, hs1', ↓reduceIte] at hc1
      exact g1.aux.not_close_P0_O _ (g1.core.mem_P0.mpr ⟨q.1, hs1', rfl⟩) _ ho1 (close_symm hc1)
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      rcases Finset.mem_product.mp hq with ⟨ho1', hs2'⟩
      have hns1 : p.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1
      have hns1' : q.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1'
      simp only [hns1, hns1', ↓reduceIte] at hne hc1 hc2
      exact hne (Prod.ext (isIndepSet_eq_of_close g1.aux.indep_O ho1 ho1' hc1)
        (isIndepSet_eq_of_close g2.core.indep_P0_finset
          (g2.core.mem_P0.mpr ⟨p.2, hs2, rfl⟩) (g2.core.mem_P0.mpr ⟨q.2, hs2', rfl⟩) hc2))
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne hadj
    rcases eq_or_strongProd_adj.mp (Or.inr hadj) with ⟨hc1, hc2⟩
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · rcases Finset.mem_product.mp hp with ⟨hs1, ho2⟩
      rcases Finset.mem_product.mp hq with ⟨hs1', ho2'⟩
      simp only [hs1, hs1', ↓reduceIte] at hne hc1 hc2
      exact hne (Prod.ext
        (isIndepSet_eq_of_close g1.core.indep_P1_finset
          (g1.core.mem_P1.mpr ⟨p.1, hs1, rfl⟩) (g1.core.mem_P1.mpr ⟨q.1, hs1', rfl⟩) hc1)
        (isIndepSet_eq_of_close g2.aux.indep_O ho2 ho2' hc2))
    · rcases Finset.mem_product.mp hp with ⟨hs1, _⟩
      rcases Finset.mem_product.mp hq with ⟨ho1', _⟩
      have hns1' : q.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1'
      simp only [hs1, hns1', ↓reduceIte] at hc1
      exact g1.aux.not_close_P1_O _ (g1.core.mem_P1.mpr ⟨p.1, hs1, rfl⟩) _ ho1' hc1
    · rcases Finset.mem_product.mp hp with ⟨ho1, _⟩
      rcases Finset.mem_product.mp hq with ⟨hs1', _⟩
      have hns1 : p.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1
      simp only [hns1, hs1', ↓reduceIte] at hc1
      exact g1.aux.not_close_P1_O _ (g1.core.mem_P1.mpr ⟨q.1, hs1', rfl⟩) _ ho1 (close_symm hc1)
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      rcases Finset.mem_product.mp hq with ⟨ho1', hs2'⟩
      have hns1 : p.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1
      have hns1' : q.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1'
      simp only [hns1, hns1', ↓reduceIte] at hne hc1 hc2
      exact hne (Prod.ext (isIndepSet_eq_of_close g1.aux.indep_O ho1 ho1' hc1)
        (isIndepSet_eq_of_close g2.core.indep_P1_finset
          (g2.core.mem_P1.mpr ⟨p.2, hs2, rfl⟩) (g2.core.mem_P1.mpr ⟨q.2, hs2', rfl⟩) hc2))
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_product.mp hp with ⟨hs1, _⟩
      simp only [hs1, ↓reduceIte]
      rcases g1.core.self_mem p.1 hs1 with h0 | h1
      · exact Or.inl (Prod.ext h0 rfl)
      · exact Or.inr (Prod.ext h1 rfl)
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      have hns1 : p.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1
      simp only [hns1, ↓reduceIte]
      rcases g2.core.self_mem p.2 hs2 with h0 | h1
      · exact Or.inl (Prod.ext rfl h0)
      · exact Or.inr (Prod.ext rfl h1)

theorem mem_prodAlignedCore_P0 (g1 : PartGadget G) (g2 : PartGadget H) {x : α × β} :
    x ∈ (prodAlignedCore g1 g2).P0 ↔
      (x.1 ∈ g1.core.P0 ∧ x.2 ∈ g2.aux.O) ∨ (x.1 ∈ g1.aux.O ∧ x.2 ∈ g2.core.P0) := by
  classical
  simp only [PortCore.mem_P0, prodAlignedCore, Finset.mem_union, Finset.mem_product]
  constructor
  · rintro ⟨p, ⟨hs1, ho2⟩ | ⟨ho1, hs2⟩, rfl⟩
    · simp only [hs1, ↓reduceIte]
      exact Or.inl ⟨⟨p.1, hs1, rfl⟩, ho2⟩
    · have hns1 : p.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1
      simp only [hns1, ↓reduceIte]
      exact Or.inr ⟨ho1, ⟨p.2, hs2, rfl⟩⟩
  · rintro (⟨⟨s1, hs1, h1⟩, ho2⟩ | ⟨ho1, ⟨s2, hs2, h2⟩⟩)
    · refine ⟨(s1, x.2), Or.inl ⟨hs1, ho2⟩, ?_⟩
      simp only [hs1, ↓reduceIte]; exact Prod.ext h1 rfl
    · have hns1 : x.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1
      refine ⟨(x.1, s2), Or.inr ⟨ho1, hs2⟩, ?_⟩
      simp only [hns1, ↓reduceIte]; exact Prod.ext rfl h2

theorem mem_prodAlignedCore_P1 (g1 : PartGadget G) (g2 : PartGadget H) {x : α × β} :
    x ∈ (prodAlignedCore g1 g2).P1 ↔
      (x.1 ∈ g1.core.P1 ∧ x.2 ∈ g2.aux.O) ∨ (x.1 ∈ g1.aux.O ∧ x.2 ∈ g2.core.P1) := by
  classical
  simp only [PortCore.mem_P1, prodAlignedCore, Finset.mem_union, Finset.mem_product]
  constructor
  · rintro ⟨p, ⟨hs1, ho2⟩ | ⟨ho1, hs2⟩, rfl⟩
    · simp only [hs1, ↓reduceIte]
      exact Or.inl ⟨⟨p.1, hs1, rfl⟩, ho2⟩
    · have hns1 : p.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1
      simp only [hns1, ↓reduceIte]
      exact Or.inr ⟨ho1, ⟨p.2, hs2, rfl⟩⟩
  · rintro (⟨⟨s1, hs1, h1⟩, ho2⟩ | ⟨ho1, ⟨s2, hs2, h2⟩⟩)
    · refine ⟨(s1, x.2), Or.inl ⟨hs1, ho2⟩, ?_⟩
      simp only [hs1, ↓reduceIte]; exact Prod.ext h1 rfl
    · have hns1 : x.1 ∉ g1.core.S := g1.not_mem_S_of_mem_O ho1
      refine ⟨(x.1, s2), Or.inr ⟨ho1, hs2⟩, ?_⟩
      simp only [hns1, ↓reduceIte]; exact Prod.ext rfl h2

theorem prodAlignedCore_card_S (g1 : PartGadget G) (g2 : PartGadget H) :
    (prodAlignedCore g1 g2).S.card =
      g1.core.S.card * g2.aux.O.card + g1.aux.O.card * g2.core.S.card := by
  classical
  have hdisj : Disjoint (g1.core.S ×ˢ g2.aux.O) (g1.aux.O ×ˢ g2.core.S) :=
    disjoint_of_not_close (G := G ⊠ H) (by
      rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂
      exact not_close_prod_fst (g1.not_close_S_O h₁.1 h₂.1))
  change ((g1.core.S ×ˢ g2.aux.O) ∪ (g1.aux.O ×ˢ g2.core.S)).card = _
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product]

/-! ### Operator 1: `PartGadget.prodStd` (Standard `X₁ × X₂`) -/

noncomputable def prodStd (g1 : PartGadget G) (g2 : PartGadget H) : PartGadget (G ⊠ H) := by
  classical
  let O0 := g1.aux.O ×ˢ g2.aux.O
  let O1 := g1.aux.H ×ˢ g2.aux.H
  let O2 := g1.aux.H ×ˢ g2.aux.V
  let O3 := g1.aux.V ×ˢ g2.aux.H
  let O4 := g1.aux.V ×ˢ g2.aux.V
  let H0 := g1.aux.H ×ˢ g2.aux.O
  let H1 := g1.aux.O ×ˢ g2.aux.H
  let V0 := g1.aux.V ×ˢ g2.aux.O
  let V1 := g1.aux.O ×ˢ g2.aux.V
  have o01 : ∀ x ∈ O0, ∀ y ∈ O1, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O0, O1, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_OH _ h₁.1 _ h₂.1)
  have o02 : ∀ x ∈ O0, ∀ y ∈ O2, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O0, O2, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_OH _ h₁.1 _ h₂.1)
  have o03 : ∀ x ∈ O0, ∀ y ∈ O3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O0, O3, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_OV _ h₁.1 _ h₂.1)
  have o04 : ∀ x ∈ O0, ∀ y ∈ O4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O0, O4, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_OV _ h₁.1 _ h₂.1)
  have o12 : ∀ x ∈ O1, ∀ y ∈ O2, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O1, O2, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (g2.aux.not_close_HV _ h₁.2 _ h₂.2)
  have o13 : ∀ x ∈ O1, ∀ y ∈ O3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O1, O3, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_HV _ h₁.1 _ h₂.1)
  have o14 : ∀ x ∈ O1, ∀ y ∈ O4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O1, O4, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_HV _ h₁.1 _ h₂.1)
  have o23 : ∀ x ∈ O2, ∀ y ∈ O3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O2, O3, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_HV _ h₁.1 _ h₂.1)
  have o24 : ∀ x ∈ O2, ∀ y ∈ O4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O2, O4, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (g1.aux.not_close_HV _ h₁.1 _ h₂.1)
  have o34 : ∀ x ∈ O3, ∀ y ∈ O4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O3, O4, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (g2.aux.not_close_HV _ h₁.2 _ h₂.2)
  refine ⟨prodAlignedCore g1 g2,
    { O := O0 ∪ O1 ∪ O2 ∪ O3 ∪ O4
      H := H0 ∪ H1
      V := V0 ∪ V1
      indep_O := isIndepSet_union5
        (isIndepSet_prod g1.aux.indep_O g2.aux.indep_O)
        (isIndepSet_prod g1.aux.indep_H g2.aux.indep_H)
        (isIndepSet_prod g1.aux.indep_H g2.aux.indep_V)
        (isIndepSet_prod g1.aux.indep_V g2.aux.indep_H)
        (isIndepSet_prod g1.aux.indep_V g2.aux.indep_V)
        o01 o02 o03 o04 o12 o13 o14 o23 o24 o34
      indep_H := isIndepSet_union_of_not_close
        (isIndepSet_prod g1.aux.indep_H g2.aux.indep_O)
        (isIndepSet_prod g1.aux.indep_O g2.aux.indep_H) (by
          rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [H0, H1, Finset.mem_product] at h₁ h₂
          exact not_close_prod_fst (fun hc => g1.aux.not_close_OH _ h₂.1 _ h₁.1 (close_symm hc)))
      indep_V := isIndepSet_union_of_not_close
        (isIndepSet_prod g1.aux.indep_V g2.aux.indep_O)
        (isIndepSet_prod g1.aux.indep_O g2.aux.indep_V) (by
          rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [V0, V1, Finset.mem_product] at h₁ h₂
          exact not_close_prod_fst (fun hc => g1.aux.not_close_OV _ h₂.1 _ h₁.1 (close_symm hc)))
      not_close_OH := ?_, not_close_OV := ?_, not_close_HV := ?_
      not_close_P0_O := ?_, not_close_P1_O := ?_, not_close_P1_H := ?_, not_close_P0_V := ?_ }⟩
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy
    simp only [O0, O1, O2, O3, O4, H0, H1, Finset.mem_union, Finset.mem_product] at hx hy
    rcases hx with (((⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩ <;>
      rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hx1 _ hy1)
    · exact not_close_prod_snd (g2.aux.not_close_OH _ hx2 _ hy2)
    · exact not_close_prod_snd (fun hc => g2.aux.not_close_OH _ hy2 _ hx2 (close_symm hc))
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OH _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_snd (fun hc => g2.aux.not_close_OV _ hy2 _ hx2 (close_symm hc))
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OH _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_HV _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OV _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_HV _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OV _ hy1 _ hx1 (close_symm hc))
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy
    simp only [O0, O1, O2, O3, O4, V0, V1, Finset.mem_union, Finset.mem_product] at hx hy
    rcases hx with (((⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩ <;>
      rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hx1 _ hy1)
    · exact not_close_prod_snd (g2.aux.not_close_OV _ hx2 _ hy2)
    · exact not_close_prod_fst (g1.aux.not_close_HV _ hx1 _ hy1)
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OH _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_fst (g1.aux.not_close_HV _ hx1 _ hy1)
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OH _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_snd (fun hc => g2.aux.not_close_OH _ hy2 _ hx2 (close_symm hc))
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OV _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_snd (fun hc => g2.aux.not_close_OV _ hy2 _ hx2 (close_symm hc))
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OV _ hy1 _ hx1 (close_symm hc))
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy
    simp only [H0, H1, V0, V1, Finset.mem_union, Finset.mem_product] at hx hy
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;> rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact not_close_prod_fst (g1.aux.not_close_HV _ hx1 _ hy1)
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OH _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hx1 _ hy1)
    · exact not_close_prod_snd (g2.aux.not_close_HV _ hx2 _ hy2)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ ho
    rw [mem_prodAlignedCore_P0] at hp
    simp only [O0, O1, O2, O3, O4, Finset.mem_union, Finset.mem_product] at ho
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;>
      rcases ho with (((⟨ho1, ho2⟩ | ⟨ho1, ho2⟩) | ⟨ho1, ho2⟩) | ⟨ho1, ho2⟩) | ⟨ho1, ho2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P0_O _ hp1 _ ho1)
    · exact not_close_prod_snd (g2.aux.not_close_OH _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_OV _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_OH _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_OV _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_P0_O _ hp2 _ ho2)
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hp1 _ ho1)
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hp1 _ ho1)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hp1 _ ho1)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hp1 _ ho1)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ ho
    rw [mem_prodAlignedCore_P1] at hp
    simp only [O0, O1, O2, O3, O4, Finset.mem_union, Finset.mem_product] at ho
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;>
      rcases ho with (((⟨ho1, ho2⟩ | ⟨ho1, ho2⟩) | ⟨ho1, ho2⟩) | ⟨ho1, ho2⟩) | ⟨ho1, ho2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P1_O _ hp1 _ ho1)
    · exact not_close_prod_snd (g2.aux.not_close_OH _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_OV _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_OH _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_OV _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_P1_O _ hp2 _ ho2)
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hp1 _ ho1)
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hp1 _ ho1)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hp1 _ ho1)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hp1 _ ho1)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ hh
    rw [mem_prodAlignedCore_P1] at hp
    simp only [H0, H1, Finset.mem_union, Finset.mem_product] at hh
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hh with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P1_H _ hp1 _ hh1)
    · exact not_close_prod_fst (g1.aux.not_close_P1_O _ hp1 _ hh1)
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hp1 _ hh1)
    · exact not_close_prod_snd (g2.aux.not_close_P1_H _ hp2 _ hh2)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ hv
    rw [mem_prodAlignedCore_P0] at hp
    simp only [V0, V1, Finset.mem_union, Finset.mem_product] at hv
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P0_V _ hp1 _ hv1)
    · exact not_close_prod_fst (g1.aux.not_close_P0_O _ hp1 _ hv1)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hp1 _ hv1)
    · exact not_close_prod_snd (g2.aux.not_close_P0_V _ hp2 _ hv2)

theorem prodStd_asymProfile (g1 : PartGadget G) (g2 : PartGadget H) :
    (g1.prodStd g2).asymProfile = g1.asymProfile.prodAligned g2.asymProfile := by
  classical
  have hI := (prodAlignedI_indep_and_card g1 g2).2
  have hS := prodAlignedCore_card_S g1 g2
  have hO : (g1.prodStd g2).aux.O.card =
      g1.aux.O.card * g2.aux.O.card +
        (g1.aux.H.card + g1.aux.V.card) * (g2.aux.H.card + g2.aux.V.card) := by
    change ((g1.aux.O ×ˢ g2.aux.O) ∪ (g1.aux.H ×ˢ g2.aux.H) ∪ (g1.aux.H ×ˢ g2.aux.V) ∪
      (g1.aux.V ×ˢ g2.aux.H) ∪ (g1.aux.V ×ˢ g2.aux.V)).card = _
    have d01 : Disjoint (g1.aux.O ×ˢ g2.aux.O) (g1.aux.H ×ˢ g2.aux.H) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_OH _ h₁.1 _ h₂.1))
    have d02 : Disjoint (g1.aux.O ×ˢ g2.aux.O) (g1.aux.H ×ˢ g2.aux.V) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_OH _ h₁.1 _ h₂.1))
    have d03 : Disjoint (g1.aux.O ×ˢ g2.aux.O) (g1.aux.V ×ˢ g2.aux.H) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_OV _ h₁.1 _ h₂.1))
    have d04 : Disjoint (g1.aux.O ×ˢ g2.aux.O) (g1.aux.V ×ˢ g2.aux.V) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_OV _ h₁.1 _ h₂.1))
    have d12 : Disjoint (g1.aux.H ×ˢ g2.aux.H) (g1.aux.H ×ˢ g2.aux.V) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_snd (g2.aux.not_close_HV _ h₁.2 _ h₂.2))
    have d13 : Disjoint (g1.aux.H ×ˢ g2.aux.H) (g1.aux.V ×ˢ g2.aux.H) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_HV _ h₁.1 _ h₂.1))
    have d14 : Disjoint (g1.aux.H ×ˢ g2.aux.H) (g1.aux.V ×ˢ g2.aux.V) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_HV _ h₁.1 _ h₂.1))
    have d23 : Disjoint (g1.aux.H ×ˢ g2.aux.V) (g1.aux.V ×ˢ g2.aux.H) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_HV _ h₁.1 _ h₂.1))
    have d24 : Disjoint (g1.aux.H ×ˢ g2.aux.V) (g1.aux.V ×ˢ g2.aux.V) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_HV _ h₁.1 _ h₂.1))
    have d34 : Disjoint (g1.aux.V ×ˢ g2.aux.H) (g1.aux.V ×ˢ g2.aux.V) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_snd (g2.aux.not_close_HV _ h₁.2 _ h₂.2))
    rw [card_union5 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34]
    simp only [Finset.card_product]; ring
  have hH : (g1.prodStd g2).aux.H.card =
      g1.aux.H.card * g2.aux.O.card + g1.aux.O.card * g2.aux.H.card := by
    change ((g1.aux.H ×ˢ g2.aux.O) ∪ (g1.aux.O ×ˢ g2.aux.H)).card = _
    have hd : Disjoint (g1.aux.H ×ˢ g2.aux.O) (g1.aux.O ×ˢ g2.aux.H) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (fun hc => g1.aux.not_close_OH _ h₂.1 _ h₁.1 (close_symm hc)))
    rw [Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product]
  have hV : (g1.prodStd g2).aux.V.card =
      g1.aux.V.card * g2.aux.O.card + g1.aux.O.card * g2.aux.V.card := by
    change ((g1.aux.V ×ˢ g2.aux.O) ∪ (g1.aux.O ×ˢ g2.aux.V)).card = _
    have hd : Disjoint (g1.aux.V ×ˢ g2.aux.O) (g1.aux.O ×ˢ g2.aux.V) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (fun hc => g1.aux.not_close_OV _ h₂.1 _ h₁.1 (close_symm hc)))
    rw [Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product]
  rcases AsymProfile.prodAligned_eq g1.asymProfile g2.asymProfile with ⟨pa, pb, pc, pd, ph, pv⟩
  apply AsymProfile.ext
  · rw [pa]; change (prodAlignedI g1 g2).card = _; rw [hI]; rfl
  · rw [pb]; exact hS
  · rw [pc]
    change (g1.prodStd g2).aux.O.card + (g1.prodStd g2).aux.H.card + (g1.prodStd g2).aux.V.card = _
    rw [hO, hH, hV]; simp only [asymProfile]; ring
  · rw [pd]; exact hO
  · rw [ph]; exact hH
  · rw [pv]; exact hV

/-! ### Operator 2: `PartGadget.prodXupg1` (Left Auxiliary Upgraded via Right Core) -/

/-- Auxiliary-upgrading aligned product (left side): replaces `(H₁ ∪ V₁) × X₂` by
`H₁ × (B₂ ∪ P0₂) ∪ V₁ × (B₂ ∪ P1₂)`, lifting `c_new` from `c₁ c₂` to `d₁ c₂ + (h₁ + v₁) a₂`. -/
noncomputable def prodXupg1 (g1 : PartGadget G) (g2 : PartGadget H) : PartGadget (G ⊠ H) := by
  classical
  let O0 := g1.aux.O ×ˢ g2.aux.O
  let O1 := g1.aux.H ×ˢ g2.core.P0
  let O2 := g1.aux.V ×ˢ g2.core.P1
  let H0 := g1.aux.O ×ˢ g2.aux.H
  let H1 := g1.aux.H ×ˢ g2.core.B
  let V0 := g1.aux.O ×ˢ g2.aux.V
  let V1 := g1.aux.V ×ˢ g2.core.B
  refine ⟨prodAlignedCore g1 g2,
    { O := O0 ∪ O1 ∪ O2
      H := H0 ∪ H1
      V := V0 ∪ V1
      indep_O := isIndepSet_union3
        (isIndepSet_prod g1.aux.indep_O g2.aux.indep_O)
        (isIndepSet_prod g1.aux.indep_H g2.core.indep_P0_finset)
        (isIndepSet_prod g1.aux.indep_V g2.core.indep_P1_finset)
        (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O0, O1, Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_OH _ h₁.1 _ h₂.1))
        (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O0, O2, Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_OV _ h₁.1 _ h₂.1))
        (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O1, O2, Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_HV _ h₁.1 _ h₂.1))
      indep_H := isIndepSet_union_of_not_close
        (isIndepSet_prod g1.aux.indep_O g2.aux.indep_H)
        (isIndepSet_prod g1.aux.indep_H g2.core.indep_B) (by
          rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [H0, H1, Finset.mem_product] at h₁ h₂
          exact not_close_prod_fst (g1.aux.not_close_OH _ h₁.1 _ h₂.1))
      indep_V := isIndepSet_union_of_not_close
        (isIndepSet_prod g1.aux.indep_O g2.aux.indep_V)
        (isIndepSet_prod g1.aux.indep_V g2.core.indep_B) (by
          rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [V0, V1, Finset.mem_product] at h₁ h₂
          exact not_close_prod_fst (g1.aux.not_close_OV _ h₁.1 _ h₂.1))
      not_close_OH := ?_, not_close_OV := ?_, not_close_HV := ?_
      not_close_P0_O := ?_, not_close_P1_O := ?_, not_close_P1_H := ?_, not_close_P0_V := ?_ }⟩
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy
    simp only [O0, O1, O2, H0, H1, Finset.mem_union, Finset.mem_product] at hx hy
    rcases hx with (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩ <;> rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact not_close_prod_snd (g2.aux.not_close_OH _ hx2 _ hy2)
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hx1 _ hy1)
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OH _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_snd (fun hc => g2.core.not_close_B_P0 hy2 hx2 (close_symm hc))
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OV _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_HV _ hy1 _ hx1 (close_symm hc))
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy
    simp only [O0, O1, O2, V0, V1, Finset.mem_union, Finset.mem_product] at hx hy
    rcases hx with (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩ <;> rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact not_close_prod_snd (g2.aux.not_close_OV _ hx2 _ hy2)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hx1 _ hy1)
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OH _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_fst (g1.aux.not_close_HV _ hx1 _ hy1)
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OV _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_snd (fun hc => g2.core.not_close_B_P1 hy2 hx2 (close_symm hc))
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy
    simp only [H0, H1, V0, V1, Finset.mem_union, Finset.mem_product] at hx hy
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;> rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact not_close_prod_snd (g2.aux.not_close_HV _ hx2 _ hy2)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hx1 _ hy1)
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_OH _ hy1 _ hx1 (close_symm hc))
    · exact not_close_prod_fst (g1.aux.not_close_HV _ hx1 _ hy1)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ ho
    rw [mem_prodAlignedCore_P0] at hp
    simp only [O0, O1, O2, Finset.mem_union, Finset.mem_product] at ho
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases ho with (⟨ho1, ho2⟩ | ⟨ho1, ho2⟩) | ⟨ho1, ho2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P0_O _ hp1 _ ho1)
    · exact not_close_prod_snd (fun hc => g2.aux.not_close_P0_O _ ho2 _ hp2 (close_symm hc))
    · exact not_close_prod_fst (g1.aux.not_close_P0_V _ hp1 _ ho1)
    · exact not_close_prod_snd (g2.aux.not_close_P0_O _ hp2 _ ho2)
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hp1 _ ho1)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hp1 _ ho1)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ ho
    rw [mem_prodAlignedCore_P1] at hp
    simp only [O0, O1, O2, Finset.mem_union, Finset.mem_product] at ho
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases ho with (⟨ho1, ho2⟩ | ⟨ho1, ho2⟩) | ⟨ho1, ho2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P1_O _ hp1 _ ho1)
    · exact not_close_prod_fst (g1.aux.not_close_P1_H _ hp1 _ ho1)
    · exact not_close_prod_snd (fun hc => g2.aux.not_close_P1_O _ ho2 _ hp2 (close_symm hc))
    · exact not_close_prod_snd (g2.aux.not_close_P1_O _ hp2 _ ho2)
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hp1 _ ho1)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hp1 _ ho1)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ hh
    rw [mem_prodAlignedCore_P1] at hp
    simp only [H0, H1, Finset.mem_union, Finset.mem_product] at hh
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hh with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P1_O _ hp1 _ hh1)
    · exact not_close_prod_fst (g1.aux.not_close_P1_H _ hp1 _ hh1)
    · exact not_close_prod_snd (g2.aux.not_close_P1_H _ hp2 _ hh2)
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hp1 _ hh1)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ hv
    rw [mem_prodAlignedCore_P0] at hp
    simp only [V0, V1, Finset.mem_union, Finset.mem_product] at hv
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P0_O _ hp1 _ hv1)
    · exact not_close_prod_fst (g1.aux.not_close_P0_V _ hp1 _ hv1)
    · exact not_close_prod_snd (g2.aux.not_close_P0_V _ hp2 _ hv2)
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hp1 _ hv1)

theorem prodXupg1_asymProfile (g1 : PartGadget G) (g2 : PartGadget H) :
    (g1.prodXupg1 g2).asymProfile = g1.asymProfile.prodXupg1 g2.asymProfile := by
  classical
  have hI := (prodAlignedI_indep_and_card g1 g2).2
  have hS := prodAlignedCore_card_S g1 g2
  have hO : (g1.prodXupg1 g2).aux.O.card =
      g1.aux.O.card * g2.aux.O.card + (g1.aux.H.card + g1.aux.V.card) * g2.core.S.card := by
    change ((g1.aux.O ×ˢ g2.aux.O) ∪ (g1.aux.H ×ˢ g2.core.P0) ∪ (g1.aux.V ×ˢ g2.core.P1)).card = _
    have d01 : Disjoint (g1.aux.O ×ˢ g2.aux.O) (g1.aux.H ×ˢ g2.core.P0) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_OH _ h₁.1 _ h₂.1))
    have d02 : Disjoint (g1.aux.O ×ˢ g2.aux.O) (g1.aux.V ×ˢ g2.core.P1) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_OV _ h₁.1 _ h₂.1))
    have d12 : Disjoint (g1.aux.H ×ˢ g2.core.P0) (g1.aux.V ×ˢ g2.core.P1) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_HV _ h₁.1 _ h₂.1))
    rw [card_union3 d01 d02 d12]
    simp only [Finset.card_product, g2.core.card_P0, g2.core.card_P1]; ring
  have hH : (g1.prodXupg1 g2).aux.H.card =
      g1.aux.O.card * g2.aux.H.card + g1.aux.H.card * (g2.core.I.card - g2.core.S.card) := by
    change ((g1.aux.O ×ˢ g2.aux.H) ∪ (g1.aux.H ×ˢ g2.core.B)).card = _
    have hd : Disjoint (g1.aux.O ×ˢ g2.aux.H) (g1.aux.H ×ˢ g2.core.B) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_OH _ h₁.1 _ h₂.1))
    rw [Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product, g2.core.card_B]
  have hV : (g1.prodXupg1 g2).aux.V.card =
      g1.aux.O.card * g2.aux.V.card + g1.aux.V.card * (g2.core.I.card - g2.core.S.card) := by
    change ((g1.aux.O ×ˢ g2.aux.V) ∪ (g1.aux.V ×ˢ g2.core.B)).card = _
    have hd : Disjoint (g1.aux.O ×ˢ g2.aux.V) (g1.aux.V ×ˢ g2.core.B) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_fst (g1.aux.not_close_OV _ h₁.1 _ h₂.1))
    rw [Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product, g2.core.card_B]
  have hsub2 : g2.core.S.card + (g2.core.I.card - g2.core.S.card) = g2.core.I.card := by
    have := g2.core.card_S_le_I; omega
  apply AsymProfile.ext
  · change (prodAlignedI g1 g2).card = _; rw [hI]; rfl
  · exact hS
  · change (g1.prodXupg1 g2).aux.O.card + (g1.prodXupg1 g2).aux.H.card + (g1.prodXupg1 g2).aux.V.card = _
    rw [hO, hH, hV]; simp only [AsymProfile.prodXupg1, asymProfile]; nlinarith
  · exact hO
  · exact hH
  · exact hV

/-! ### Operator 3: `PartGadget.prodXupg2` (Right Auxiliary Upgraded via Left Core) -/

/-- Symmetric auxiliary-upgrading aligned product (right side): replaces `X₁ × (H₂ ∪ V₂)` by
`(B₁ ∪ P0₁) × H₂ ∪ (B₁ ∪ P1₁) × V₂`, lifting `c_new` to `c₁ d₂ + a₁ (h₂ + v₂)`. -/
noncomputable def prodXupg2 (g1 : PartGadget G) (g2 : PartGadget H) : PartGadget (G ⊠ H) := by
  classical
  let O0 := g1.aux.O ×ˢ g2.aux.O
  let O1 := g1.core.P0 ×ˢ g2.aux.H
  let O2 := g1.core.P1 ×ˢ g2.aux.V
  let H0 := g1.aux.H ×ˢ g2.aux.O
  let H1 := g1.core.B ×ˢ g2.aux.H
  let V0 := g1.aux.V ×ˢ g2.aux.O
  let V1 := g1.core.B ×ˢ g2.aux.V
  refine ⟨prodAlignedCore g1 g2,
    { O := O0 ∪ O1 ∪ O2
      H := H0 ∪ H1
      V := V0 ∪ V1
      indep_O := isIndepSet_union3
        (isIndepSet_prod g1.aux.indep_O g2.aux.indep_O)
        (isIndepSet_prod g1.core.indep_P0_finset g2.aux.indep_H)
        (isIndepSet_prod g1.core.indep_P1_finset g2.aux.indep_V)
        (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O0, O1, Finset.mem_product] at h₁ h₂; exact not_close_prod_snd (g2.aux.not_close_OH _ h₁.2 _ h₂.2))
        (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O0, O2, Finset.mem_product] at h₁ h₂; exact not_close_prod_snd (g2.aux.not_close_OV _ h₁.2 _ h₂.2))
        (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [O1, O2, Finset.mem_product] at h₁ h₂; exact not_close_prod_snd (g2.aux.not_close_HV _ h₁.2 _ h₂.2))
      indep_H := isIndepSet_union_of_not_close
        (isIndepSet_prod g1.aux.indep_H g2.aux.indep_O)
        (isIndepSet_prod g1.core.indep_B g2.aux.indep_H) (by
          rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [H0, H1, Finset.mem_product] at h₁ h₂
          exact not_close_prod_snd (g2.aux.not_close_OH _ h₁.2 _ h₂.2))
      indep_V := isIndepSet_union_of_not_close
        (isIndepSet_prod g1.aux.indep_V g2.aux.indep_O)
        (isIndepSet_prod g1.core.indep_B g2.aux.indep_V) (by
          rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [V0, V1, Finset.mem_product] at h₁ h₂
          exact not_close_prod_snd (g2.aux.not_close_OV _ h₁.2 _ h₂.2))
      not_close_OH := ?_, not_close_OV := ?_, not_close_HV := ?_
      not_close_P0_O := ?_, not_close_P1_O := ?_, not_close_P1_H := ?_, not_close_P0_V := ?_ }⟩
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy
    simp only [O0, O1, O2, H0, H1, Finset.mem_union, Finset.mem_product] at hx hy
    rcases hx with (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩ <;> rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact not_close_prod_fst (g1.aux.not_close_OH _ hx1 _ hy1)
    · exact not_close_prod_snd (g2.aux.not_close_OH _ hx2 _ hy2)
    · exact not_close_prod_snd (fun hc => g2.aux.not_close_OH _ hy2 _ hx2 (close_symm hc))
    · exact not_close_prod_fst (fun hc => g1.core.not_close_B_P0 hy1 hx1 (close_symm hc))
    · exact not_close_prod_snd (fun hc => g2.aux.not_close_OV _ hy2 _ hx2 (close_symm hc))
    · exact not_close_prod_snd (fun hc => g2.aux.not_close_HV _ hy2 _ hx2 (close_symm hc))
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy
    simp only [O0, O1, O2, V0, V1, Finset.mem_union, Finset.mem_product] at hx hy
    rcases hx with (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩ <;> rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact not_close_prod_fst (g1.aux.not_close_OV _ hx1 _ hy1)
    · exact not_close_prod_snd (g2.aux.not_close_OV _ hx2 _ hy2)
    · exact not_close_prod_snd (fun hc => g2.aux.not_close_OH _ hy2 _ hx2 (close_symm hc))
    · exact not_close_prod_snd (g2.aux.not_close_HV _ hx2 _ hy2)
    · exact not_close_prod_snd (fun hc => g2.aux.not_close_OV _ hy2 _ hx2 (close_symm hc))
    · exact not_close_prod_fst (fun hc => g1.core.not_close_B_P1 hy1 hx1 (close_symm hc))
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy
    simp only [H0, H1, V0, V1, Finset.mem_union, Finset.mem_product] at hx hy
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;> rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact not_close_prod_fst (g1.aux.not_close_HV _ hx1 _ hy1)
    · exact not_close_prod_snd (g2.aux.not_close_OV _ hx2 _ hy2)
    · exact not_close_prod_snd (fun hc => g2.aux.not_close_OH _ hy2 _ hx2 (close_symm hc))
    · exact not_close_prod_snd (g2.aux.not_close_HV _ hx2 _ hy2)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ ho
    rw [mem_prodAlignedCore_P0] at hp
    simp only [O0, O1, O2, Finset.mem_union, Finset.mem_product] at ho
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases ho with (⟨ho1, ho2⟩ | ⟨ho1, ho2⟩) | ⟨ho1, ho2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P0_O _ hp1 _ ho1)
    · exact not_close_prod_snd (g2.aux.not_close_OH _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_OV _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_P0_O _ hp2 _ ho2)
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_P0_O _ ho1 _ hp1 (close_symm hc))
    · exact not_close_prod_snd (g2.aux.not_close_P0_V _ hp2 _ ho2)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ ho
    rw [mem_prodAlignedCore_P1] at hp
    simp only [O0, O1, O2, Finset.mem_union, Finset.mem_product] at ho
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases ho with (⟨ho1, ho2⟩ | ⟨ho1, ho2⟩) | ⟨ho1, ho2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P1_O _ hp1 _ ho1)
    · exact not_close_prod_snd (g2.aux.not_close_OH _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_OV _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_P1_O _ hp2 _ ho2)
    · exact not_close_prod_snd (g2.aux.not_close_P1_H _ hp2 _ ho2)
    · exact not_close_prod_fst (fun hc => g1.aux.not_close_P1_O _ ho1 _ hp1 (close_symm hc))
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ hh
    rw [mem_prodAlignedCore_P1] at hp
    simp only [H0, H1, Finset.mem_union, Finset.mem_product] at hh
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hh with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P1_H _ hp1 _ hh1)
    · exact not_close_prod_snd (g2.aux.not_close_OH _ hp2 _ hh2)
    · exact not_close_prod_snd (g2.aux.not_close_P1_O _ hp2 _ hh2)
    · exact not_close_prod_snd (g2.aux.not_close_P1_H _ hp2 _ hh2)
  · rintro ⟨_, _⟩ hp ⟨_, _⟩ hv
    rw [mem_prodAlignedCore_P0] at hp
    simp only [V0, V1, Finset.mem_union, Finset.mem_product] at hv
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
    · exact not_close_prod_fst (g1.aux.not_close_P0_V _ hp1 _ hv1)
    · exact not_close_prod_snd (g2.aux.not_close_OV _ hp2 _ hv2)
    · exact not_close_prod_snd (g2.aux.not_close_P0_O _ hp2 _ hv2)
    · exact not_close_prod_snd (g2.aux.not_close_P0_V _ hp2 _ hv2)

theorem prodXupg2_asymProfile (g1 : PartGadget G) (g2 : PartGadget H) :
    (g1.prodXupg2 g2).asymProfile = g1.asymProfile.prodXupg2 g2.asymProfile := by
  classical
  have hI := (prodAlignedI_indep_and_card g1 g2).2
  have hS := prodAlignedCore_card_S g1 g2
  have hO : (g1.prodXupg2 g2).aux.O.card =
      g1.aux.O.card * g2.aux.O.card + g1.core.S.card * (g2.aux.H.card + g2.aux.V.card) := by
    change ((g1.aux.O ×ˢ g2.aux.O) ∪ (g1.core.P0 ×ˢ g2.aux.H) ∪ (g1.core.P1 ×ˢ g2.aux.V)).card = _
    have d01 : Disjoint (g1.aux.O ×ˢ g2.aux.O) (g1.core.P0 ×ˢ g2.aux.H) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_snd (g2.aux.not_close_OH _ h₁.2 _ h₂.2))
    have d02 : Disjoint (g1.aux.O ×ˢ g2.aux.O) (g1.core.P1 ×ˢ g2.aux.V) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_snd (g2.aux.not_close_OV _ h₁.2 _ h₂.2))
    have d12 : Disjoint (g1.core.P0 ×ˢ g2.aux.H) (g1.core.P1 ×ˢ g2.aux.V) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_snd (g2.aux.not_close_HV _ h₁.2 _ h₂.2))
    rw [card_union3 d01 d02 d12]
    simp only [Finset.card_product, g1.core.card_P0, g1.core.card_P1]; ring
  have hH : (g1.prodXupg2 g2).aux.H.card =
      g1.aux.H.card * g2.aux.O.card + (g1.core.I.card - g1.core.S.card) * g2.aux.H.card := by
    change ((g1.aux.H ×ˢ g2.aux.O) ∪ (g1.core.B ×ˢ g2.aux.H)).card = _
    have hd : Disjoint (g1.aux.H ×ˢ g2.aux.O) (g1.core.B ×ˢ g2.aux.H) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_snd (g2.aux.not_close_OH _ h₁.2 _ h₂.2))
    rw [Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product, g1.core.card_B]
  have hV : (g1.prodXupg2 g2).aux.V.card =
      g1.aux.V.card * g2.aux.O.card + (g1.core.I.card - g1.core.S.card) * g2.aux.V.card := by
    change ((g1.aux.V ×ˢ g2.aux.O) ∪ (g1.core.B ×ˢ g2.aux.V)).card = _
    have hd : Disjoint (g1.aux.V ×ˢ g2.aux.O) (g1.core.B ×ˢ g2.aux.V) :=
      disjoint_of_not_close (G := G ⊠ H) (by rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [Finset.mem_product] at h₁ h₂; exact not_close_prod_snd (g2.aux.not_close_OV _ h₁.2 _ h₂.2))
    rw [Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product, g1.core.card_B]
  have hsub1 : g1.core.S.card + (g1.core.I.card - g1.core.S.card) = g1.core.I.card := by
    have := g1.core.card_S_le_I; omega
  apply AsymProfile.ext
  · change (prodAlignedI g1 g2).card = _; rw [hI]; rfl
  · exact hS
  · change (g1.prodXupg2 g2).aux.O.card + (g1.prodXupg2 g2).aux.H.card + (g1.prodXupg2 g2).aux.V.card = _
    rw [hO, hH, hV]; simp only [AsymProfile.prodXupg2, asymProfile]; nlinarith
  · exact hO
  · exact hH
  · exact hV

end PartGadget

/-! ## 2. Six-Vertex Quotient Graph `Γ₆` & General `PartGadget` `Γ₆^⊠4` Pullback -/

/-- Boolean adjacency on `Γ₆` (`0=B, 1=P0, 2=P1, 3=O, 4=H, 5=V`). -/
def gamma6AdjBool (u v : Fin 6) : Bool :=
  match u.val, v.val with
  | 0, 3 | 3, 0 => true
  | 0, 4 | 4, 0 => true
  | 0, 5 | 5, 0 => true
  | 1, 2 | 2, 1 => true
  | 1, 4 | 4, 1 => true
  | 2, 5 | 5, 2 => true
  | _, _ => false

def gamma6CloseBool (u v : Fin 6) : Bool := decide (u = v) || gamma6AdjBool u v

abbrev Gamma6Quad := Fin 6 × Fin 6 × Fin 6 × Fin 6

def gamma6QuadCloseBool (x y : Gamma6Quad) : Bool :=
  gamma6CloseBool x.1 y.1 && gamma6CloseBool x.2.1 y.2.1 &&
    gamma6CloseBool x.2.2.1 y.2.2.1 && gamma6CloseBool x.2.2.2 y.2.2.2

def gamma6QuadListIndepBool : List Gamma6Quad → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !gamma6QuadCloseBool x y) && gamma6QuadListIndepBool xs

def AsymProfile.gamma6Weight (p : AsymProfile) (c : Fin 6) : ℕ :=
  match c.val with
  | 0 => p.a - p.b
  | 1 => p.b
  | 2 => p.b
  | 3 => p.d
  | 4 => p.h
  | _ => p.v

def gamma6QuadWeight (p₁ p₂ p₃ p₄ : AsymProfile) (q : Gamma6Quad) : ℕ :=
  p₁.gamma6Weight q.1 * p₂.gamma6Weight q.2.1 *
    p₃.gamma6Weight q.2.2.1 * p₄.gamma6Weight q.2.2.2

def gamma6QuadListWeight (p₁ p₂ p₃ p₄ : AsymProfile) (S : List Gamma6Quad) : ℕ :=
  (S.map (gamma6QuadWeight p₁ p₂ p₃ p₄)).sum

/-- The six canonical independent blocks `(B, P0, P1, O, H, V)` of any `PartGadget G`. -/
noncomputable def PartGadget.gamma6Block {α : Type*} [Fintype α] {G : SimpleGraph α}
    (g : PartGadget G) (c : Fin 6) : Finset α :=
  match c.val with
  | 0 => g.core.B
  | 1 => g.core.P0
  | 2 => g.core.P1
  | 3 => g.aux.O
  | 4 => g.aux.H
  | _ => g.aux.V

theorem PartGadget.gamma6Block_card {α : Type*} [Fintype α] {G : SimpleGraph α}
    (g : PartGadget G) (c : Fin 6) :
    (g.gamma6Block c).card = g.asymProfile.gamma6Weight c := by
  fin_cases c
  · exact g.core.card_B
  · exact g.core.card_P0
  · exact g.core.card_P1
  · rfl
  · rfl
  · rfl

theorem PartGadget.gamma6Block_isIndepSet {α : Type*} [Fintype α] {G : SimpleGraph α}
    (g : PartGadget G) (c : Fin 6) :
    G.IsIndepSet (g.gamma6Block c : Set α) := by
  fin_cases c
  · exact g.core.indep_B
  · exact g.core.indep_P0_finset
  · exact g.core.indep_P1_finset
  · exact g.aux.indep_O
  · exact g.aux.indep_H
  · exact g.aux.indep_V

theorem PartGadget.gamma6Block_not_close {α : Type*} [Fintype α] {G : SimpleGraph α}
    (g : PartGadget G) {c₁ c₂ : Fin 6} (hnc : gamma6CloseBool c₁ c₂ = false)
    {x y : α} (hx : x ∈ g.gamma6Block c₁) (hy : y ∈ g.gamma6Block c₂) :
    ¬ (x = y ∨ G.Adj x y) := by
  fin_cases c₁ <;> fin_cases c₂ <;> simp [gamma6CloseBool, gamma6AdjBool] at hnc
  · exact g.core.not_close_B_P0 hx hy
  · exact g.core.not_close_B_P1 hx hy
  · exact fun hc => g.core.not_close_B_P0 hy hx (close_symm hc)
  · exact g.aux.not_close_P0_O x hx y hy
  · exact g.aux.not_close_P0_V x hx y hy
  · exact fun hc => g.core.not_close_B_P1 hy hx (close_symm hc)
  · exact g.aux.not_close_P1_O x hx y hy
  · exact g.aux.not_close_P1_H x hx y hy
  · exact fun hc => g.aux.not_close_P0_O y hy x hx (close_symm hc)
  · exact fun hc => g.aux.not_close_P1_O y hy x hx (close_symm hc)
  · exact g.aux.not_close_OH x hx y hy
  · exact g.aux.not_close_OV x hx y hy
  · exact fun hc => g.aux.not_close_P1_H y hy x hx (close_symm hc)
  · exact fun hc => g.aux.not_close_OH y hy x hx (close_symm hc)
  · exact g.aux.not_close_HV x hx y hy
  · exact fun hc => g.aux.not_close_P0_V y hy x hx (close_symm hc)
  · exact fun hc => g.aux.not_close_OV y hy x hx (close_symm hc)
  · exact fun hc => g.aux.not_close_HV y hy x hx (close_symm hc)

theorem gamma6QuadCloseBool_symm (x y : Gamma6Quad) :
    gamma6QuadCloseBool x y = gamma6QuadCloseBool y x := by
  have h1 : ∀ a b : Fin 6, gamma6CloseBool a b = gamma6CloseBool b a := by decide
  simp only [gamma6QuadCloseBool, h1]

theorem gamma6QuadCloseBool_refl (x : Gamma6Quad) : gamma6QuadCloseBool x x = true := by
  have h1 : ∀ a : Fin 6, gamma6CloseBool a a = true := by decide
  simp only [gamma6QuadCloseBool, h1, Bool.and_self]

theorem gamma6QuadListIndepBool_spec {S : List Gamma6Quad}
    (h : gamma6QuadListIndepBool S = true) :
    S.Nodup ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → gamma6QuadCloseBool x y = false := by
  induction S with
  | nil => exact ⟨List.nodup_nil, fun _ hx => by cases hx⟩
  | cons a tl ih =>
    simp only [gamma6QuadListIndepBool, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true'] at h
    rcases ih h.2 with ⟨hnd, hpair⟩
    have ha_not : a ∉ tl := by
      intro hmem
      have hc := h.1 a hmem
      rw [gamma6QuadCloseBool_refl] at hc
      exact Bool.noConfusion hc
    refine ⟨List.nodup_cons.mpr ⟨ha_not, hnd⟩, ?_⟩
    intro x hx y hy hne
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hne
    · exact h.1 y hy
    · rw [gamma6QuadCloseBool_symm]; exact h.1 x hx
    · exact hpair x hx y hy hne

noncomputable def gamma6QuadBlock
    {V₁ V₂ V₃ V₄ : Type*} [Fintype V₁] [Fintype V₂] [Fintype V₃] [Fintype V₄]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {G₃ : SimpleGraph V₃} {G₄ : SimpleGraph V₄}
    (g₁ : PartGadget G₁) (g₂ : PartGadget G₂)
    (g₃ : PartGadget G₃) (g₄ : PartGadget G₄)
    (q : Gamma6Quad) : Finset (((V₁ × V₂) × V₃) × V₄) :=
  ((g₁.gamma6Block q.1 ×ˢ g₂.gamma6Block q.2.1) ×ˢ
    g₃.gamma6Block q.2.2.1) ×ˢ g₄.gamma6Block q.2.2.2

theorem gamma6QuadBlock_card
    {V₁ V₂ V₃ V₄ : Type*} [Fintype V₁] [Fintype V₂] [Fintype V₃] [Fintype V₄]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {G₃ : SimpleGraph V₃} {G₄ : SimpleGraph V₄}
    (g₁ : PartGadget G₁) (g₂ : PartGadget G₂)
    (g₃ : PartGadget G₃) (g₄ : PartGadget G₄) (q : Gamma6Quad) :
    (gamma6QuadBlock g₁ g₂ g₃ g₄ q).card =
      gamma6QuadWeight g₁.asymProfile g₂.asymProfile g₃.asymProfile g₄.asymProfile q := by
  simp only [gamma6QuadBlock, Finset.card_product, PartGadget.gamma6Block_card,
    gamma6QuadWeight]

theorem gamma6QuadBlock_isIndepSet
    {V₁ V₂ V₃ V₄ : Type*} [Fintype V₁] [Fintype V₂] [Fintype V₃] [Fintype V₄]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {G₃ : SimpleGraph V₃} {G₄ : SimpleGraph V₄}
    (g₁ : PartGadget G₁) (g₂ : PartGadget G₂)
    (g₃ : PartGadget G₃) (g₄ : PartGadget G₄) (q : Gamma6Quad) :
    (((G₁ ⊠ G₂) ⊠ G₃) ⊠ G₄).IsIndepSet (gamma6QuadBlock g₁ g₂ g₃ g₄ q : Set _) :=
  isIndepSet_prod
    (isIndepSet_prod
      (isIndepSet_prod (g₁.gamma6Block_isIndepSet q.1) (g₂.gamma6Block_isIndepSet q.2.1))
      (g₃.gamma6Block_isIndepSet q.2.2.1))
    (g₄.gamma6Block_isIndepSet q.2.2.2)

theorem gamma6QuadBlock_not_close
    {V₁ V₂ V₃ V₄ : Type*} [Fintype V₁] [Fintype V₂] [Fintype V₃] [Fintype V₄]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {G₃ : SimpleGraph V₃} {G₄ : SimpleGraph V₄}
    (g₁ : PartGadget G₁) (g₂ : PartGadget G₂)
    (g₃ : PartGadget G₃) (g₄ : PartGadget G₄)
    {q₁ q₂ : Gamma6Quad} (hnc : gamma6QuadCloseBool q₁ q₂ = false)
    {x y : ((V₁ × V₂) × V₃) × V₄}
    (hx : x ∈ gamma6QuadBlock g₁ g₂ g₃ g₄ q₁)
    (hy : y ∈ gamma6QuadBlock g₁ g₂ g₃ g₄ q₂) :
    ¬ (x = y ∨ (((G₁ ⊠ G₂) ⊠ G₃) ⊠ G₄).Adj x y) := by
  rcases x with ⟨⟨⟨x₁, x₂⟩, x₃⟩, x₄⟩
  rcases y with ⟨⟨⟨y₁, y₂⟩, y₃⟩, y₄⟩
  simp only [gamma6QuadBlock, Finset.mem_product] at hx hy
  simp only [gamma6QuadCloseBool, Bool.and_eq_false_iff] at hnc
  intro hc
  have h123_4 := eq_or_strongProd_adj.mp hc
  have h12_3 := eq_or_strongProd_adj.mp h123_4.1
  have h1_2 := eq_or_strongProd_adj.mp h12_3.1
  rcases hnc with ((h1 | h2) | h3) | h4
  · exact g₁.gamma6Block_not_close h1 hx.1.1.1 hy.1.1.1 h1_2.1
  · exact g₂.gamma6Block_not_close h2 hx.1.1.2 hy.1.1.2 h1_2.2
  · exact g₃.gamma6Block_not_close h3 hx.1.2 hy.1.2 h12_3.2
  · exact g₄.gamma6Block_not_close h4 hx.2 hy.2 h123_4.2

/-- Pullback of any independent list `S` in `Γ₆^⊠4` to `((G₁ ⊠ G₂) ⊠ G₃) ⊠ G₄`. -/
theorem gamma6Pow4_weight_le_indepNum
    {V₁ V₂ V₃ V₄ : Type*} [Fintype V₁] [Fintype V₂] [Fintype V₃] [Fintype V₄]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {G₃ : SimpleGraph V₃} {G₄ : SimpleGraph V₄}
    (g₁ : PartGadget G₁) (g₂ : PartGadget G₂)
    (g₃ : PartGadget G₃) (g₄ : PartGadget G₄)
    (S : List Gamma6Quad) (hindep : gamma6QuadListIndepBool S = true) :
    gamma6QuadListWeight g₁.asymProfile g₂.asymProfile g₃.asymProfile g₄.asymProfile S ≤
      (((G₁ ⊠ G₂) ⊠ G₃) ⊠ G₄).indepNum := by
  classical
  rcases gamma6QuadListIndepBool_spec hindep with ⟨hnd, hpair⟩
  let U : Finset (((V₁ × V₂) × V₃) × V₄) :=
    S.toFinset.biUnion (gamma6QuadBlock g₁ g₂ g₃ g₄)
  have hU_indep : (((G₁ ⊠ G₂) ⊠ G₃) ⊠ G₄).IsIndepSet (U : Set _) := by
    intro x hx y hy hne hadj
    simp only [U, Finset.mem_coe, Finset.mem_biUnion, List.mem_toFinset] at hx hy
    rcases hx with ⟨q₁, hq₁, hx₁⟩
    rcases hy with ⟨q₂, hq₂, hy₂⟩
    by_cases hq : q₁ = q₂
    · subst hq
      exact gamma6QuadBlock_isIndepSet g₁ g₂ g₃ g₄ q₁ hx₁ hy₂ hne hadj
    · exact gamma6QuadBlock_not_close g₁ g₂ g₃ g₄ (hpair q₁ hq₁ q₂ hq₂ hq) hx₁ hy₂ (Or.inr hadj)
  have hdisj : Set.PairwiseDisjoint (S.toFinset : Set Gamma6Quad) (gamma6QuadBlock g₁ g₂ g₃ g₄) := by
    intro q₁ hq₁ q₂ hq₂ hne
    have hq₁' : q₁ ∈ S := List.mem_toFinset.mp hq₁
    have hq₂' : q₂ ∈ S := List.mem_toFinset.mp hq₂
    exact disjoint_of_not_close (fun x hx y hy =>
      gamma6QuadBlock_not_close g₁ g₂ g₃ g₄ (hpair q₁ hq₁' q₂ hq₂' hne) hx hy)
  have hcard : U.card =
      gamma6QuadListWeight g₁.asymProfile g₂.asymProfile g₃.asymProfile g₄.asymProfile S := by
    rw [Finset.card_biUnion hdisj]
    simp_rw [gamma6QuadBlock_card]
    rw [gamma6QuadListWeight, List.sum_toFinset _ hnd]
  rw [← hcard]
  exact hU_indep.card_le_indepNum

/-- Direct bridge from 4 strong-power `PartGadget`s on `C7` + independent `Γ₆^⊠4` list
to `(strongPowPi (SimpleGraph.cycleGraph 7) (d₁ + d₂ + d₃ + d₄)).indepNum`. -/
theorem gamma6Pow4_card_le_cycleGraph7_indepNum
    {d₁ d₂ d₃ d₄ : ℕ}
    (g₁ : PartGadget (strongPow C7 d₁)) (g₂ : PartGadget (strongPow C7 d₂))
    (g₃ : PartGadget (strongPow C7 d₃)) (g₄ : PartGadget (strongPow C7 d₄))
    (S : List Gamma6Quad) (hindep : gamma6QuadListIndepBool S = true) :
    gamma6QuadListWeight g₁.asymProfile g₂.asymProfile g₃.asymProfile g₄.asymProfile S ≤
      (strongPowPi (SimpleGraph.cycleGraph 7) (d₁ + d₂ + d₃ + d₄)).indepNum := by
  have h1 := gamma6Pow4_weight_le_indepNum g₁ g₂ g₃ g₄ S hindep
  have e12 : strongPow C7 d₁ ⊠ strongPow C7 d₂ ≃g strongPow C7 (d₁ + d₂) :=
    (strongPowAddEquiv C7 d₁ d₂).symm
  have e123 : (strongPow C7 d₁ ⊠ strongPow C7 d₂) ⊠ strongPow C7 d₃ ≃g
      strongPow C7 (d₁ + d₂ + d₃) :=
    (strongProdCongr e12 SimpleGraph.Iso.refl).trans (strongPowAddEquiv C7 (d₁ + d₂) d₃).symm
  have e1234 : ((strongPow C7 d₁ ⊠ strongPow C7 d₂) ⊠ strongPow C7 d₃) ⊠ strongPow C7 d₄ ≃g
      strongPow C7 (d₁ + d₂ + d₃ + d₄) :=
    (strongProdCongr e123 SimpleGraph.Iso.refl).trans (strongPowAddEquiv C7 (d₁ + d₂ + d₃) d₄).symm
  have h_eq1 : (((strongPow C7 d₁ ⊠ strongPow C7 d₂) ⊠ strongPow C7 d₃) ⊠ strongPow C7 d₄).indepNum =
      (strongPow C7 (d₁ + d₂ + d₃ + d₄)).indepNum :=
    iso_indepNum_eq e1234
  have h_eq2 : (strongPow C7 (d₁ + d₂ + d₃ + d₄)).indepNum =
      (strongPowPi (SimpleGraph.cycleGraph 7) (d₁ + d₂ + d₃ + d₄)).indepNum := by
    rw [iso_indepNum_eq (strongPowCongr c7IsoCycleGraph (d₁ + d₂ + d₃ + d₄)),
      strongPow_indepNum_eq_pi]
  omega

/-! ## 3. Concrete Shared `PartGadget` DAG from M3 `baseHetero5D` -/

/-- Named base asymmetric profile `(367, 8, 367, 322, 19, 26)` (avoids inline `by decide` in types). -/
def frontierBaseProfile : AsymProfile :=
  { a := 367, b := 8, c := 367, d := 322, h := 19, v := 26,
    hba := by decide, hdhv := by decide }

noncomputable def basePart5D : PartGadget (strongPow C7 5) :=
  PartGadget.ofHeteroGadget baseHetero5D

theorem basePart5D_asymProfile_eq : basePart5D.asymProfile = frontierBaseProfile := by
  rw [basePart5D, PartGadget.ofHeteroGadget_asymProfile]
  simp [frontierBaseProfile, baseHetero5D_asymProfile]

def frontierProf0 : AsymProfile := frontierBaseProfile
noncomputable def frontierNode0 : PartGadget (strongPow C7 5) := basePart5D
theorem frontierNode0_profile : frontierNode0.asymProfile = frontierProf0 :=
  basePart5D_asymProfile_eq

def frontierProf1 : AsymProfile := frontierProf0.prodAligned frontierProf0
noncomputable def frontierNode1 : PartGadget (strongPow C7 10) :=
  (frontierNode0.prodStd frontierNode0).mapIso (strongPowAddEquiv C7 5 5).symm
theorem frontierNode1_profile : frontierNode1.asymProfile = frontierProf1 := by
  rw [frontierNode1, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    frontierNode0_profile]; rfl

def frontierProf2 : AsymProfile := frontierProf0.prodAligned frontierProf1
noncomputable def frontierNode2 : PartGadget (strongPow C7 15) :=
  (frontierNode0.prodStd frontierNode1).mapIso (strongPowAddEquiv C7 5 10).symm
theorem frontierNode2_profile : frontierNode2.asymProfile = frontierProf2 := by
  rw [frontierNode2, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    frontierNode0_profile, frontierNode1_profile]; rfl

def frontierProf3 : AsymProfile := frontierProf1.prodAligned frontierProf1
noncomputable def frontierNode3 : PartGadget (strongPow C7 20) :=
  (frontierNode1.prodStd frontierNode1).mapIso (strongPowAddEquiv C7 10 10).symm
theorem frontierNode3_profile : frontierNode3.asymProfile = frontierProf3 := by
  rw [frontierNode3, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    frontierNode1_profile]; rfl

def frontierProf4 : AsymProfile := frontierProf1.prodAligned frontierProf2
noncomputable def frontierNode4 : PartGadget (strongPow C7 25) :=
  (frontierNode1.prodStd frontierNode2).mapIso (strongPowAddEquiv C7 10 15).symm
theorem frontierNode4_profile : frontierNode4.asymProfile = frontierProf4 := by
  rw [frontierNode4, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    frontierNode1_profile, frontierNode2_profile]; rfl

def frontierProf5 : AsymProfile := frontierProf2.prodAligned frontierProf2
noncomputable def frontierNode5 : PartGadget (strongPow C7 30) :=
  (frontierNode2.prodStd frontierNode2).mapIso (strongPowAddEquiv C7 15 15).symm
theorem frontierNode5_profile : frontierNode5.asymProfile = frontierProf5 := by
  rw [frontierNode5, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    frontierNode2_profile]; rfl

def frontierProf6 : AsymProfile := frontierProf2.prodAligned frontierProf3
noncomputable def frontierNode6 : PartGadget (strongPow C7 35) :=
  (frontierNode2.prodStd frontierNode3).mapIso (strongPowAddEquiv C7 15 20).symm
theorem frontierNode6_profile : frontierNode6.asymProfile = frontierProf6 := by
  rw [frontierNode6, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    frontierNode2_profile, frontierNode3_profile]; rfl

def frontierProf7 : AsymProfile := frontierProf3.prodAligned frontierProf4
noncomputable def frontierNode7 : PartGadget (strongPow C7 45) :=
  (frontierNode3.prodStd frontierNode4).mapIso (strongPowAddEquiv C7 20 25).symm
theorem frontierNode7_profile : frontierNode7.asymProfile = frontierProf7 := by
  rw [frontierNode7, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    frontierNode3_profile, frontierNode4_profile]; rfl

def frontierProf8 : AsymProfile := frontierProf5.prodAligned frontierProf6
noncomputable def frontierNode8 : PartGadget (strongPow C7 65) :=
  (frontierNode5.prodStd frontierNode6).mapIso (strongPowAddEquiv C7 30 35).symm
theorem frontierNode8_profile : frontierNode8.asymProfile = frontierProf8 := by
  rw [frontierNode8, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    frontierNode5_profile, frontierNode6_profile]; rfl

def frontierProf9 : AsymProfile := frontierProf7.prodXupg1 frontierProf8
noncomputable def frontierNode9 : PartGadget (strongPow C7 110) :=
  (frontierNode7.prodXupg1 frontierNode8).mapIso (strongPowAddEquiv C7 45 65).symm
theorem frontierNode9_profile : frontierNode9.asymProfile = frontierProf9 := by
  rw [frontierNode9, PartGadget.mapIso_asymProfile, PartGadget.prodXupg1_asymProfile,
    frontierNode7_profile, frontierNode8_profile]; rfl

def frontierProf10 : AsymProfile := frontierProf9.prodAligned frontierProf9
noncomputable def frontierNode10 : PartGadget (strongPow C7 220) :=
  (frontierNode9.prodStd frontierNode9).mapIso (strongPowAddEquiv C7 110 110).symm
theorem frontierNode10_profile : frontierNode10.asymProfile = frontierProf10 := by
  rw [frontierNode10, PartGadget.mapIso_asymProfile, PartGadget.prodStd_asymProfile,
    frontierNode9_profile]; rfl

/-! ## 4. Certified Pure-Kernel Frontier Bound (`d = 220`, 113-Digit Witness) -/

/-- Exact 113-digit cardinality of the constructed independent set in `C₇^⊠220`. -/
def frontierCard : ℕ := 74705260449010907031291311728445696992339746673817850928852859227950431526005228577975175899699338829613565617217

theorem frontierTarget_a_eq : frontierProf10.a = frontierCard := rfl

theorem frontierCard_le_indepNum :
    frontierCard ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 220).indepNum := by
  have h1 : frontierNode10.asymProfile.a ≤ (strongPow C7 220).indepNum :=
    frontierNode10.card_le_indepNum
  rw [frontierNode10_profile, frontierTarget_a_eq] at h1
  have h2 : (strongPow C7 220).indepNum =
      (strongPowPi (SimpleGraph.cycleGraph 7) 220).indepNum := by
    rw [iso_indepNum_eq (strongPowCongr c7IsoCycleGraph 220), strongPow_indepNum_eq_pi]
  omega

/-- Numerator of our pure-kernel certified lower bound on `Θ(C₇)` (`d = 220`). -/
def c7_lower_num : ℕ := 3258822357711717

/-- Denominator of our pure-kernel certified lower bound on `Θ(C₇)`. -/
def c7_lower_den : ℕ := 1000000000000000

theorem c7_lower_den_pos : 0 < c7_lower_den := by decide

set_option exponentiation.threshold 4096 in
theorem frontier_pow_le :
    c7_lower_num ^ 220 ≤ c7_lower_den ^ 220 * frontierCard :=
  nat_pow_le_of_ble rfl

/-- **Main M4 Frontier Theorem (Pure Kernel):**
`3258822357711717 / 1000000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7)`. -/
theorem c7_lower_frontier :
    (c7_lower_num : ℝ) / (c7_lower_den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  le_shannonCapacity_of_nat_pow_pi (by decide) c7_lower_den_pos
    frontierCard_le_indepNum frontier_pow_le

/-- Strictly surpasses BPZ v1 (`3.258805369885465`, homogeneous `ValidTuple.star` peak at `d = 200`). -/
theorem c7_lower_gt_bpz_v1 :
    (3258805369885465 : ℝ) / 1000000000000000 < (c7_lower_num : ℝ) / (c7_lower_den : ℝ) := by
  rw [div_lt_div_iff₀ (by positivity) (by exact_mod_cast c7_lower_den_pos)]
  exact_mod_cast (by decide : 3258805369885465 * c7_lower_den < c7_lower_num * 1000000000000000)

end ShannonC7
