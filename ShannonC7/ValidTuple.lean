import ShannonC7.Fekete
import ShannonC7.SmallPowers

/-!
# Constructive `ValidTuple.star`, Split-Tree Engine & Pure-Kernel `Trie7` Constructor

This module formalizes the Buys–Polak–Zuiddam (2026) / Gao (2026) recursive valid-tuple
framework on arbitrary finite simple graphs `G`:
- `Profile` (`a, b, c, d` with `b ≤ a` and `d ≤ c`) and computable `Profile.star`,
- `ValidTuple G` (decidable-free contract signature matching `PROJECT.md § 4.3`),
- constructive graph-isomorphism transport `ValidTuple.congr` + `congr_profile`,
- **full constructive zero-`sorry` proof** of `ValidTuple.star : ValidTuple G → ValidTuple H → ValidTuple (G ⊠ H)`
  and exact profile law `ValidTuple.star_profile : (τ₁.star τ₂).profile = τ₁.profile.star τ₂.profile`,
- sharing-friendly `SplitTree` (`leaf`, `sq`, `node`), `ValidTuple.evalTree`, `evalTree_profile`,
  and direct `SimpleGraph.cycleGraph 7` Shannon capacity bridges (`evalTree_a_le_cycleGraph7_indepNum`,
  `le_shannonCapacity_cycleGraph7_of_evalTree`, `le_shannonCapacity_cycleGraph7_of_evalTree_profile`),
- pure-kernel radix-7 trie constructor `ValidTuple.ofTrie7` and `ValidTuple.ofTrie7_profile_eq`
  reusing `TrieVerifier.lean` primitives with zero `native_decide`.
-/

namespace ShannonC7

/-! ## Four-Integer Profile & Star Algebra -/

/-- Four-integer profile `Π(τ) = (a, b, c, d)` with structural invariants `b ≤ a` and `d ≤ c`. -/
structure Profile where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  hba : b ≤ a
  hdc : d ≤ c
  deriving DecidableEq, Repr

@[ext]
theorem Profile.ext {p q : Profile}
    (ha : p.a = q.a) (hb : p.b = q.b) (hc : p.c = q.c) (hd : p.d = q.d) : p = q := by
  cases p; cases q
  simp only [mk.injEq]
  exact ⟨ha, hb, hc, hd⟩

/-- Exact profile multiplication law matching `ValidTuple.star`. -/
def Profile.star (p q : Profile) : Profile where
  a := (p.a - p.b) * (q.a - q.b) + p.c * q.b + p.b * q.c
  b := p.d * q.b + p.b * q.d
  c := p.c * q.c
  d := p.d * q.d + (p.c - p.d) * (q.c - q.d)
  hba := by
    have h1 : p.d * q.b ≤ p.c * q.b := Nat.mul_le_mul_right q.b p.hdc
    have h2 : p.b * q.d ≤ p.b * q.c := Nat.mul_le_mul_left p.b q.hdc
    omega
  hdc := by
    have hp : p.c = p.d + (p.c - p.d) := (Nat.add_sub_of_le p.hdc).symm
    have hq : q.c = q.d + (q.c - q.d) := (Nat.add_sub_of_le q.hdc).symm
    have hmul : p.c * q.c =
        p.d * q.d + p.d * (q.c - q.d) + (p.c - p.d) * q.d + (p.c - p.d) * (q.c - q.d) := by
      conv_lhs => rw [hp, hq]
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      omega
    omega

/-! ## Closed-Neighborhood Helpers -/

theorem close_refl {V : Type*} {G : SimpleGraph V} (x : V) :
    x = x ∨ G.Adj x x := Or.inl rfl

theorem close_symm {V : Type*} {G : SimpleGraph V} {x y : V}
    (h : x = y ∨ G.Adj x y) : y = x ∨ G.Adj y x :=
  h.imp Eq.symm SimpleGraph.Adj.symm

theorem isIndepSet_eq_of_close {V : Type*} {G : SimpleGraph V} {A : Set V}
    (hA : G.IsIndepSet A) {x y : V} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : x = y ∨ G.Adj x y) : x = y := by
  rcases hxy with rfl | hadj
  · rfl
  · exact False.elim (hA hx hy hadj.ne hadj)

theorem isIndepSet_not_close_of_ne {V : Type*} {G : SimpleGraph V} {A : Set V}
    (hA : G.IsIndepSet A) {x y : V} (hx : x ∈ A) (hy : y ∈ A) (hne : x ≠ y) :
    ¬ (x = y ∨ G.Adj x y) :=
  fun h => hne (isIndepSet_eq_of_close hA hx hy h)

theorem isIndepSet_prod {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {A : Finset V} {B : Finset W}
    (hA : G.IsIndepSet (A : Set V)) (hB : H.IsIndepSet (B : Set W)) :
    (G ⊠ H).IsIndepSet ((A ×ˢ B : Finset (V × W)) : Set (V × W)) := by
  rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ hne ⟨_, hG, hH⟩
  simp only [Finset.mem_coe, Finset.mem_product] at h₁ h₂
  have ha : a₁ = a₂ := isIndepSet_eq_of_close hA h₁.1 h₂.1 hG
  have hb : b₁ = b₂ := isIndepSet_eq_of_close hB h₁.2 h₂.2 hH
  exact hne (Prod.ext ha hb)

theorem disjoint_of_not_close {V : Type*} {G : SimpleGraph V} {A B : Finset V}
    (h : ∀ a ∈ A, ∀ b ∈ B, ¬ (a = b ∨ G.Adj a b)) : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  exact h x hxA x hxB (Or.inl rfl)

theorem isIndepSet_union_of_not_close {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V}
    (hA : G.IsIndepSet (A : Set V)) (hB : G.IsIndepSet (B : Set V))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ¬ (a = b ∨ G.Adj a b)) :
    G.IsIndepSet ((A ∪ B : Finset V) : Set V) := by
  intro x hx y hy hne hadj
  simp only [Finset.mem_coe, Finset.mem_union] at hx hy
  rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
  · exact hA hxA hyA hne hadj
  · exact hAB x hxA y hyB (Or.inr hadj)
  · exact hAB y hyA x hxB (Or.inr hadj.symm)
  · exact hB hxB hyB hne hadj

/-! ## `ValidTuple` Structure & Derived Sets -/

set_option linter.unusedFintypeInType false in
/-- A Buys–Polak–Zuiddam / Gao valid tuple `(I, S, f0, f1, X)` on a finite graph `G`. -/
structure ValidTuple {V : Type*} [Fintype V] (G : SimpleGraph V) where
  I : Finset V
  S : Finset V
  f0 : V → V
  f1 : V → V
  X : Finset V
  indep_I : G.IsIndepSet (I : Set V)
  sub_S : S ⊆ I
  self_mem : ∀ s ∈ S, f0 s = s ∨ f1 s = s
  priv0 : ∀ s ∈ S, (f0 s = s ∨ G.Adj (f0 s) s) ∧
    ∀ x ∈ I, (x = f0 s ∨ G.Adj x (f0 s)) → x = s
  priv1 : ∀ s ∈ S, (f1 s = s ∨ G.Adj (f1 s) s) ∧
    ∀ x ∈ I, (x = f1 s ∨ G.Adj x (f1 s)) → x = s
  indep_P0 : G.IsIndepSet (f0 '' (S : Set V))
  indep_P1 : G.IsIndepSet (f1 '' (S : Set V))
  indep_X : G.IsIndepSet (X : Set V)
  disj_nbr : ∀ x ∈ X, ¬ ((∃ s ∈ S, x = f0 s ∨ G.Adj x (f0 s)) ∧
    (∃ s ∈ S, x = f1 s ∨ G.Adj x (f1 s)))

namespace ValidTuple

section Basic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

open Classical in
/-- Bulk independent set `B = I \ S`. -/
noncomputable def B (τ : ValidTuple G) : Finset V :=
  τ.I \ τ.S

open Classical in
/-- First private transversal `P0 = f0(S)`. -/
noncomputable def P0 (τ : ValidTuple G) : Finset V :=
  τ.S.image τ.f0

open Classical in
/-- Second private transversal `P1 = f1(S)`. -/
noncomputable def P1 (τ : ValidTuple G) : Finset V :=
  τ.S.image τ.f1

open Classical in
/-- Auxiliary vertices in the closed neighborhood of `P0`: `H = X ∩ N[P0]`. -/
noncomputable def H (τ : ValidTuple G) : Finset V :=
  τ.X.filter fun x => ∃ s ∈ τ.S, x = τ.f0 s ∨ G.Adj x (τ.f0 s)

open Classical in
/-- Auxiliary vertices in the closed neighborhood of `P1`: `Vset = X ∩ N[P1]`. -/
noncomputable def Vset (τ : ValidTuple G) : Finset V :=
  τ.X.filter fun x => ∃ s ∈ τ.S, x = τ.f1 s ∨ G.Adj x (τ.f1 s)

open Classical in
/-- Auxiliary core outside `N[P0] ∪ N[P1]`. -/
noncomputable def O (τ : ValidTuple G) : Finset V :=
  τ.X.filter fun x =>
    (¬ ∃ s ∈ τ.S, x = τ.f0 s ∨ G.Adj x (τ.f0 s)) ∧
    (¬ ∃ s ∈ τ.S, x = τ.f1 s ∨ G.Adj x (τ.f1 s))

@[simp] theorem mem_B {τ : ValidTuple G} {x : V} : x ∈ τ.B ↔ x ∈ τ.I ∧ x ∉ τ.S := by
  classical simp [B]

@[simp] theorem mem_P0 {τ : ValidTuple G} {x : V} : x ∈ τ.P0 ↔ ∃ s ∈ τ.S, τ.f0 s = x := by
  classical simp [P0]

@[simp] theorem mem_P1 {τ : ValidTuple G} {x : V} : x ∈ τ.P1 ↔ ∃ s ∈ τ.S, τ.f1 s = x := by
  classical simp [P1]

@[simp] theorem mem_H {τ : ValidTuple G} {x : V} :
    x ∈ τ.H ↔ x ∈ τ.X ∧ ∃ s ∈ τ.S, x = τ.f0 s ∨ G.Adj x (τ.f0 s) := by
  classical simp [H]

@[simp] theorem mem_Vset {τ : ValidTuple G} {x : V} :
    x ∈ τ.Vset ↔ x ∈ τ.X ∧ ∃ s ∈ τ.S, x = τ.f1 s ∨ G.Adj x (τ.f1 s) := by
  classical simp [Vset]

@[simp] theorem mem_O {τ : ValidTuple G} {x : V} :
    x ∈ τ.O ↔ x ∈ τ.X ∧
      (¬ ∃ s ∈ τ.S, x = τ.f0 s ∨ G.Adj x (τ.f0 s)) ∧
      (¬ ∃ s ∈ τ.S, x = τ.f1 s ∨ G.Adj x (τ.f1 s)) := by
  classical simp [O]

theorem B_subset_I (τ : ValidTuple G) : τ.B ⊆ τ.I := fun _ hx => (mem_B.mp hx).1
theorem H_subset_X (τ : ValidTuple G) : τ.H ⊆ τ.X := fun _ hx => (mem_H.mp hx).1
theorem Vset_subset_X (τ : ValidTuple G) : τ.Vset ⊆ τ.X := fun _ hx => (mem_Vset.mp hx).1
theorem O_subset_X (τ : ValidTuple G) : τ.O ⊆ τ.X := fun _ hx => (mem_O.mp hx).1

/-- Four-integer profile `(a, b, c, d) = (|I|, |S|, |X|, |O|)` of a `ValidTuple`. -/
noncomputable def profile (τ : ValidTuple G) : Profile where
  a := τ.I.card
  b := τ.S.card
  c := τ.X.card
  d := τ.O.card
  hba := Finset.card_le_card τ.sub_S
  hdc := Finset.card_le_card τ.O_subset_X

/-- The main independent set certifies `τ.profile.a ≤ G.indepNum`. -/
theorem card_le_indepNum (τ : ValidTuple G) : τ.profile.a ≤ G.indepNum :=
  τ.indep_I.card_le_indepNum

theorem le_shannonCapacity {m : ℕ} (hm : 0 < m) (τ : ValidTuple (strongPow G m)) :
    (τ.profile.a : ℝ) ^ (1 / (m : ℝ)) ≤ shannonCapacity G :=
  le_shannonCapacity_of_indepSet G hm τ.indep_I

/-- Contract alias matching `SCOPE.md`: direct Shannon capacity lower bound from a `ValidTuple`. -/
theorem to_shannonCapacity {m : ℕ} (hm : 0 < m) (τ : ValidTuple (strongPow G m)) :
    (τ.profile.a : ℝ) ^ (1 / (m : ℝ)) ≤ shannonCapacity G :=
  τ.le_shannonCapacity hm

/-! ### Structural Non-Close, Independence & Cardinality Lemmas -/

theorem indep_B (τ : ValidTuple G) : G.IsIndepSet (τ.B : Set V) :=
  τ.indep_I.mono (Finset.coe_subset.mpr τ.B_subset_I)

theorem indep_S (τ : ValidTuple G) : G.IsIndepSet (τ.S : Set V) :=
  τ.indep_I.mono (Finset.coe_subset.mpr τ.sub_S)

theorem indep_P0_finset (τ : ValidTuple G) : G.IsIndepSet (τ.P0 : Set V) := by
  classical
  simpa [P0, Finset.coe_image] using τ.indep_P0

theorem indep_P1_finset (τ : ValidTuple G) : G.IsIndepSet (τ.P1 : Set V) := by
  classical
  simpa [P1, Finset.coe_image] using τ.indep_P1

theorem indep_H (τ : ValidTuple G) : G.IsIndepSet (τ.H : Set V) :=
  τ.indep_X.mono (Finset.coe_subset.mpr τ.H_subset_X)

theorem indep_Vset (τ : ValidTuple G) : G.IsIndepSet (τ.Vset : Set V) :=
  τ.indep_X.mono (Finset.coe_subset.mpr τ.Vset_subset_X)

theorem indep_O (τ : ValidTuple G) : G.IsIndepSet (τ.O : Set V) :=
  τ.indep_X.mono (Finset.coe_subset.mpr τ.O_subset_X)

theorem f0_injOn (τ : ValidTuple G) : Set.InjOn τ.f0 (τ.S : Set V) := by
  intro s₁ hs₁ s₂ hs₂ heq
  have h1 : s₁ = τ.f0 s₂ ∨ G.Adj s₁ (τ.f0 s₂) := heq ▸ close_symm (τ.priv0 s₁ hs₁).1
  exact (τ.priv0 s₂ hs₂).2 s₁ (τ.sub_S hs₁) h1

theorem f1_injOn (τ : ValidTuple G) : Set.InjOn τ.f1 (τ.S : Set V) := by
  intro s₁ hs₁ s₂ hs₂ heq
  have h1 : s₁ = τ.f1 s₂ ∨ G.Adj s₁ (τ.f1 s₂) := heq ▸ close_symm (τ.priv1 s₁ hs₁).1
  exact (τ.priv1 s₂ hs₂).2 s₁ (τ.sub_S hs₁) h1

theorem card_B (τ : ValidTuple G) : τ.B.card = τ.I.card - τ.S.card := by
  classical
  simp [B, Finset.card_sdiff, Finset.inter_eq_left.mpr τ.sub_S]

theorem card_P0 (τ : ValidTuple G) : τ.P0.card = τ.S.card := by
  classical
  simpa [P0] using Finset.card_image_of_injOn τ.f0_injOn

theorem card_P1 (τ : ValidTuple G) : τ.P1.card = τ.S.card := by
  classical
  simpa [P1] using Finset.card_image_of_injOn τ.f1_injOn

theorem B_not_close_S (τ : ValidTuple G) {b s : V} (hb : b ∈ τ.B) (hs : s ∈ τ.S) :
    ¬ (b = s ∨ G.Adj b s) := by
  rw [mem_B] at hb
  exact isIndepSet_not_close_of_ne τ.indep_I hb.1 (τ.sub_S hs) (fun h => hb.2 (h ▸ hs))

theorem B_not_close_P0 (τ : ValidTuple G) {b p : V} (hb : b ∈ τ.B) (hp : p ∈ τ.P0) :
    ¬ (b = p ∨ G.Adj b p) := by
  rw [mem_B] at hb
  rcases mem_P0.mp hp with ⟨s, hs, rfl⟩
  intro hclose
  exact hb.2 (((τ.priv0 s hs).2 b hb.1 hclose) ▸ hs)

theorem B_not_close_P1 (τ : ValidTuple G) {b p : V} (hb : b ∈ τ.B) (hp : p ∈ τ.P1) :
    ¬ (b = p ∨ G.Adj b p) := by
  rw [mem_B] at hb
  rcases mem_P1.mp hp with ⟨s, hs, rfl⟩
  intro hclose
  exact hb.2 (((τ.priv1 s hs).2 b hb.1 hclose) ▸ hs)

theorem O_not_close_P0 (τ : ValidTuple G) {o p : V} (ho : o ∈ τ.O) (hp : p ∈ τ.P0) :
    ¬ (o = p ∨ G.Adj o p) := by
  rcases mem_P0.mp hp with ⟨s, hs, rfl⟩
  intro hclose
  exact (mem_O.mp ho).2.1 ⟨s, hs, hclose⟩

theorem O_not_close_P1 (τ : ValidTuple G) {o p : V} (ho : o ∈ τ.O) (hp : p ∈ τ.P1) :
    ¬ (o = p ∨ G.Adj o p) := by
  rcases mem_P1.mp hp with ⟨s, hs, rfl⟩
  intro hclose
  exact (mem_O.mp ho).2.2 ⟨s, hs, hclose⟩

theorem O_not_close_S (τ : ValidTuple G) {o s : V} (ho : o ∈ τ.O) (hs : s ∈ τ.S) :
    ¬ (o = s ∨ G.Adj o s) := by
  rcases τ.self_mem s hs with hf0 | hf1
  · exact τ.O_not_close_P0 ho (mem_P0.mpr ⟨s, hs, hf0⟩)
  · exact τ.O_not_close_P1 ho (mem_P1.mpr ⟨s, hs, hf1⟩)

theorem H_not_close_P1 (τ : ValidTuple G) {h p : V} (hh : h ∈ τ.H) (hp : p ∈ τ.P1) :
    ¬ (h = p ∨ G.Adj h p) := by
  rcases mem_H.mp hh with ⟨hx, h0⟩
  rcases mem_P1.mp hp with ⟨s, hs, rfl⟩
  intro h1
  exact τ.disj_nbr h hx ⟨h0, ⟨s, hs, h1⟩⟩

theorem Vset_not_close_P0 (τ : ValidTuple G) {v p : V} (hv : v ∈ τ.Vset) (hp : p ∈ τ.P0) :
    ¬ (v = p ∨ G.Adj v p) := by
  rcases mem_Vset.mp hv with ⟨hx, h1⟩
  rcases mem_P0.mp hp with ⟨s, hs, rfl⟩
  intro h0
  exact τ.disj_nbr v hx ⟨⟨s, hs, h0⟩, h1⟩

theorem O_not_close_H (τ : ValidTuple G) {o h : V} (ho : o ∈ τ.O) (hh : h ∈ τ.H) :
    ¬ (o = h ∨ G.Adj o h) :=
  isIndepSet_not_close_of_ne τ.indep_X (τ.O_subset_X ho) (τ.H_subset_X hh) fun heq =>
    (mem_O.mp ho).2.1 (heq ▸ (mem_H.mp hh).2)

theorem O_not_close_Vset (τ : ValidTuple G) {o v : V} (ho : o ∈ τ.O) (hv : v ∈ τ.Vset) :
    ¬ (o = v ∨ G.Adj o v) :=
  isIndepSet_not_close_of_ne τ.indep_X (τ.O_subset_X ho) (τ.Vset_subset_X hv) fun heq =>
    (mem_O.mp ho).2.2 (heq ▸ (mem_Vset.mp hv).2)

theorem H_not_close_Vset (τ : ValidTuple G) {h v : V} (hh : h ∈ τ.H) (hv : v ∈ τ.Vset) :
    ¬ (h = v ∨ G.Adj h v) :=
  isIndepSet_not_close_of_ne τ.indep_X (τ.H_subset_X hh) (τ.Vset_subset_X hv) fun heq =>
    τ.disj_nbr h (τ.H_subset_X hh) ⟨(mem_H.mp hh).2, heq ▸ (mem_Vset.mp hv).2⟩

theorem not_mem_S_of_mem_O (τ : ValidTuple G) {x : V} (ho : x ∈ τ.O) : x ∉ τ.S :=
  fun hs => τ.O_not_close_S ho hs (Or.inl rfl)

theorem card_X_partition (τ : ValidTuple G) :
    τ.O.card + τ.H.card + τ.Vset.card = τ.X.card := by
  classical
  have hOH : Disjoint τ.O τ.H := disjoint_of_not_close fun o ho h hh => τ.O_not_close_H ho hh
  have hOV : Disjoint τ.O τ.Vset := disjoint_of_not_close fun o ho v hv => τ.O_not_close_Vset ho hv
  have hHV : Disjoint τ.H τ.Vset := disjoint_of_not_close fun h hh v hv => τ.H_not_close_Vset hh hv
  have hunion : τ.O ∪ τ.H ∪ τ.Vset = τ.X := by
    ext x
    simp only [Finset.mem_union, mem_O, mem_H, mem_Vset]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hx
      by_cases h0 : ∃ s ∈ τ.S, x = τ.f0 s ∨ G.Adj x (τ.f0 s)
      · exact Or.inl (Or.inr ⟨hx, h0⟩)
      · by_cases h1 : ∃ s ∈ τ.S, x = τ.f1 s ∨ G.Adj x (τ.f1 s)
        · exact Or.inr ⟨hx, h1⟩
        · exact Or.inl (Or.inl ⟨hx, h0, h1⟩)
  rw [← hunion, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hOV, hHV⟩),
    Finset.card_union_of_disjoint hOH]

open Classical in
theorem card_HV (τ : ValidTuple G) :
    (τ.H ∪ τ.Vset).card = τ.X.card - τ.O.card := by
  have hHV : Disjoint τ.H τ.Vset := disjoint_of_not_close fun h hh v hv => τ.H_not_close_Vset hh hv
  have hpart := τ.card_X_partition
  rw [Finset.card_union_of_disjoint hHV]
  omega

end Basic

/-! ## Constructive Graph-Isomorphism Transport (`ValidTuple.congr`) -/

section Congr

variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

/-- Transport a `ValidTuple` along a graph isomorphism `e : G ≃g H`. -/
def congr (e : G ≃g H) (τ : ValidTuple G) : ValidTuple H where
  I := τ.I.map e.toEquiv.toEmbedding
  S := τ.S.map e.toEquiv.toEmbedding
  f0 := fun y => e (τ.f0 (e.symm y))
  f1 := fun y => e (τ.f1 (e.symm y))
  X := τ.X.map e.toEquiv.toEmbedding
  indep_I := isIndepSet_map_iso e τ.indep_I
  sub_S := Finset.map_subset_map.mpr τ.sub_S
  self_mem := by
    intro y hy
    rcases Finset.mem_map.mp hy with ⟨s, hs, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply]
    exact (τ.self_mem s hs).imp (congrArg e) (congrArg e)
  priv0 := by
    intro y hy
    rcases Finset.mem_map.mp hy with ⟨s, hs, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply]
    refine ⟨(τ.priv0 s hs).1.imp (congrArg e) (fun h => e.map_adj_iff.mpr h), ?_⟩
    intro z hz hclose
    rcases Finset.mem_map.mp hz with ⟨x, hx, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv] at hclose ⊢
    have hxclose : x = τ.f0 s ∨ G.Adj x (τ.f0 s) :=
      hclose.imp (fun h => e.injective h) (fun h => e.map_adj_iff.mp h)
    exact congrArg e ((τ.priv0 s hs).2 x hx hxclose)
  priv1 := by
    intro y hy
    rcases Finset.mem_map.mp hy with ⟨s, hs, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply]
    refine ⟨(τ.priv1 s hs).1.imp (congrArg e) (fun h => e.map_adj_iff.mpr h), ?_⟩
    intro z hz hclose
    rcases Finset.mem_map.mp hz with ⟨x, hx, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv] at hclose ⊢
    have hxclose : x = τ.f1 s ∨ G.Adj x (τ.f1 s) :=
      hclose.imp (fun h => e.injective h) (fun h => e.map_adj_iff.mp h)
    exact congrArg e ((τ.priv1 s hs).2 x hx hxclose)
  indep_P0 := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩ hne hadj
    rcases Finset.mem_map.mp (Finset.mem_coe.mp hy₁) with ⟨s₁, hs₁, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_coe.mp hy₂) with ⟨s₂, hs₂, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply] at hne hadj
    exact τ.indep_P0 ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, rfl⟩ (fun h => hne (congrArg e h)) (e.map_adj_iff.mp hadj)
  indep_P1 := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩ hne hadj
    rcases Finset.mem_map.mp (Finset.mem_coe.mp hy₁) with ⟨s₁, hs₁, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_coe.mp hy₂) with ⟨s₂, hs₂, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply] at hne hadj
    exact τ.indep_P1 ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, rfl⟩ (fun h => hne (congrArg e h)) (e.map_adj_iff.mp hadj)
  indep_X := isIndepSet_map_iso e τ.indep_X
  disj_nbr := by
    intro y hy ⟨⟨t₀, ht₀, hc₀⟩, ⟨t₁, ht₁, hc₁⟩⟩
    rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp ht₀ with ⟨s₀, hs₀, rfl⟩
    rcases Finset.mem_map.mp ht₁ with ⟨s₁, hs₁, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply] at hc₀ hc₁
    exact τ.disj_nbr x hx
      ⟨⟨s₀, hs₀, hc₀.imp (fun h => e.injective h) (fun h => e.map_adj_iff.mp h)⟩,
       ⟨s₁, hs₁, hc₁.imp (fun h => e.injective h) (fun h => e.map_adj_iff.mp h)⟩⟩

theorem congr_O (e : G ≃g H) (τ : ValidTuple G) :
    (τ.congr e).O = τ.O.map e.toEquiv.toEmbedding := by
  ext y
  simp only [mem_O, congr, Finset.mem_map, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, h0, h1⟩
    refine ⟨x, ⟨hx, ?_, ?_⟩, rfl⟩
    · rintro ⟨s, hs, hclose⟩
      exact h0 ⟨e s, ⟨s, hs, rfl⟩, by
        simpa [RelIso.symm_apply_apply] using hclose.imp (congrArg e) (fun h => e.map_adj_iff.mpr h)⟩
    · rintro ⟨s, hs, hclose⟩
      exact h1 ⟨e s, ⟨s, hs, rfl⟩, by
        simpa [RelIso.symm_apply_apply] using hclose.imp (congrArg e) (fun h => e.map_adj_iff.mpr h)⟩
  · rintro ⟨x, ⟨hx, h0, h1⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_, ?_⟩
    · rintro ⟨t, ⟨s, hs, rfl⟩, hclose⟩
      simp only [RelIso.symm_apply_apply] at hclose
      exact h0 ⟨s, hs, hclose.imp (fun h => e.injective h) (fun h => e.map_adj_iff.mp h)⟩
    · rintro ⟨t, ⟨s, hs, rfl⟩, hclose⟩
      simp only [RelIso.symm_apply_apply] at hclose
      exact h1 ⟨s, hs, hclose.imp (fun h => e.injective h) (fun h => e.map_adj_iff.mp h)⟩

@[simp]
theorem congr_profile (e : G ≃g H) (τ : ValidTuple G) :
    (τ.congr e).profile = τ.profile := by
  apply Profile.ext
  · exact Finset.card_map _
  · exact Finset.card_map _
  · exact Finset.card_map _
  · simp only [profile, congr_O, Finset.card_map]

end Congr

/-! ## Constructive Strong Product (`ValidTuple.star`) & Profile Identity -/

section Star

variable {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂] {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}

open Classical in
noncomputable def starM0 (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) : Finset (V₁ × V₂) :=
  τ₁.B ×ˢ τ₂.B

open Classical in
noncomputable def starM1 (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) : Finset (V₁ × V₂) :=
  (τ₁.S ×ˢ τ₂.O) ∪ (τ₁.P0 ×ˢ τ₂.H) ∪ (τ₁.P1 ×ˢ τ₂.Vset)

open Classical in
noncomputable def starM2 (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) : Finset (V₁ × V₂) :=
  (τ₁.O ×ˢ τ₂.S) ∪ (τ₁.H ×ˢ τ₂.P1) ∪ (τ₁.Vset ×ˢ τ₂.P0)

open Classical in
noncomputable def starI (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) : Finset (V₁ × V₂) :=
  starM0 τ₁ τ₂ ∪ starM1 τ₁ τ₂ ∪ starM2 τ₁ τ₂

open Classical in
noncomputable def starS (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) : Finset (V₁ × V₂) :=
  (τ₁.S ×ˢ τ₂.O) ∪ (τ₁.O ×ˢ τ₂.S)

open Classical in
noncomputable def starF0 (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) (p : V₁ × V₂) :
    V₁ × V₂ :=
  if p.1 ∈ τ₁.S then (τ₁.f0 p.1, p.2) else (p.1, τ₂.f0 p.2)

open Classical in
noncomputable def starF1 (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) (p : V₁ × V₂) :
    V₁ × V₂ :=
  if p.1 ∈ τ₁.S then (τ₁.f1 p.1, p.2) else (p.1, τ₂.f1 p.2)

theorem starF0_left (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂)
    {s₁ : V₁} {o₂ : V₂} (hs₁ : s₁ ∈ τ₁.S) :
    starF0 τ₁ τ₂ (s₁, o₂) = (τ₁.f0 s₁, o₂) := by
  classical simp [starF0, hs₁]

theorem starF0_right (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂)
    {o₁ : V₁} {s₂ : V₂} (ho₁ : o₁ ∈ τ₁.O) :
    starF0 τ₁ τ₂ (o₁, s₂) = (o₁, τ₂.f0 s₂) := by
  classical simp [starF0, τ₁.not_mem_S_of_mem_O ho₁]

theorem starF1_left (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂)
    {s₁ : V₁} {o₂ : V₂} (hs₁ : s₁ ∈ τ₁.S) :
    starF1 τ₁ τ₂ (s₁, o₂) = (τ₁.f1 s₁, o₂) := by
  classical simp [starF1, hs₁]

theorem starF1_right (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂)
    {o₁ : V₁} {s₂ : V₂} (ho₁ : o₁ ∈ τ₁.O) :
    starF1 τ₁ τ₂ (o₁, s₂) = (o₁, τ₂.f1 s₂) := by
  classical simp [starF1, τ₁.not_mem_S_of_mem_O ho₁]

theorem starM1_indep (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) :
    (G₁ ⊠ G₂).IsIndepSet (starM1 τ₁ τ₂ : Set (V₁ × V₂)) := by
  classical
  unfold starM1
  refine isIndepSet_union_of_not_close
    (isIndepSet_union_of_not_close
      (isIndepSet_prod τ₁.indep_S τ₂.indep_O)
      (isIndepSet_prod τ₁.indep_P0_finset τ₂.indep_H) ?_)
    (isIndepSet_prod τ₁.indep_P1_finset τ₂.indep_Vset) ?_
  · rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb hclose
    simp only [Finset.mem_product] at ha hb
    exact τ₂.O_not_close_H ha.2 hb.2 (eq_or_strongProd_adj.mp hclose).2
  · rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb hclose
    simp only [Finset.mem_union, Finset.mem_product] at ha hb
    rcases ha with ha | ha
    · exact τ₂.O_not_close_Vset ha.2 hb.2 (eq_or_strongProd_adj.mp hclose).2
    · exact τ₂.H_not_close_Vset ha.2 hb.2 (eq_or_strongProd_adj.mp hclose).2

theorem starM2_indep (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) :
    (G₁ ⊠ G₂).IsIndepSet (starM2 τ₁ τ₂ : Set (V₁ × V₂)) := by
  classical
  unfold starM2
  refine isIndepSet_union_of_not_close
    (isIndepSet_union_of_not_close
      (isIndepSet_prod τ₁.indep_O τ₂.indep_S)
      (isIndepSet_prod τ₁.indep_H τ₂.indep_P1_finset) ?_)
    (isIndepSet_prod τ₁.indep_Vset τ₂.indep_P0_finset) ?_
  · rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb hclose
    simp only [Finset.mem_product] at ha hb
    exact τ₁.O_not_close_H ha.1 hb.1 (eq_or_strongProd_adj.mp hclose).1
  · rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb hclose
    simp only [Finset.mem_union, Finset.mem_product] at ha hb
    rcases ha with ha | ha
    · exact τ₁.O_not_close_Vset ha.1 hb.1 (eq_or_strongProd_adj.mp hclose).1
    · exact τ₁.H_not_close_Vset ha.1 hb.1 (eq_or_strongProd_adj.mp hclose).1

theorem starM0_not_close_M1 (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂)
    {a b : V₁ × V₂} (ha : a ∈ starM0 τ₁ τ₂) (hb : b ∈ starM1 τ₁ τ₂) :
    ¬ (a = b ∨ (G₁ ⊠ G₂).Adj a b) := by
  classical
  simp only [starM0, starM1, Finset.mem_union, Finset.mem_product] at ha hb
  intro hclose
  have h1 := (eq_or_strongProd_adj.mp hclose).1
  rcases hb with (hb | hb) | hb
  · exact τ₁.B_not_close_S ha.1 hb.1 h1
  · exact τ₁.B_not_close_P0 ha.1 hb.1 h1
  · exact τ₁.B_not_close_P1 ha.1 hb.1 h1

theorem starM0_not_close_M2 (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂)
    {a b : V₁ × V₂} (ha : a ∈ starM0 τ₁ τ₂) (hb : b ∈ starM2 τ₁ τ₂) :
    ¬ (a = b ∨ (G₁ ⊠ G₂).Adj a b) := by
  classical
  simp only [starM0, starM2, Finset.mem_union, Finset.mem_product] at ha hb
  intro hclose
  have h2 := (eq_or_strongProd_adj.mp hclose).2
  rcases hb with (hb | hb) | hb
  · exact τ₂.B_not_close_S ha.2 hb.2 h2
  · exact τ₂.B_not_close_P1 ha.2 hb.2 h2
  · exact τ₂.B_not_close_P0 ha.2 hb.2 h2

theorem starM1_not_close_M2 (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂)
    {a b : V₁ × V₂} (ha : a ∈ starM1 τ₁ τ₂) (hb : b ∈ starM2 τ₁ τ₂) :
    ¬ (a = b ∨ (G₁ ⊠ G₂).Adj a b) := by
  classical
  simp only [starM1, starM2, Finset.mem_union, Finset.mem_product] at ha hb
  intro hclose
  rcases eq_or_strongProd_adj.mp hclose with ⟨h1, h2⟩
  rcases ha with (ha | ha) | ha <;> rcases hb with (hb | hb) | hb
  · exact τ₁.O_not_close_S hb.1 ha.1 (close_symm h1)
  · exact τ₂.O_not_close_P1 ha.2 hb.2 h2
  · exact τ₂.O_not_close_P0 ha.2 hb.2 h2
  · exact τ₁.O_not_close_P0 hb.1 ha.1 (close_symm h1)
  · exact τ₂.H_not_close_P1 ha.2 hb.2 h2
  · exact τ₁.Vset_not_close_P0 hb.1 ha.1 (close_symm h1)
  · exact τ₁.O_not_close_P1 hb.1 ha.1 (close_symm h1)
  · exact τ₁.H_not_close_P1 hb.1 ha.1 (close_symm h1)
  · exact τ₂.Vset_not_close_P0 ha.2 hb.2 h2

theorem starI_indep (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) :
    (G₁ ⊠ G₂).IsIndepSet (starI τ₁ τ₂ : Set (V₁ × V₂)) := by
  classical
  unfold starI
  refine isIndepSet_union_of_not_close
    (isIndepSet_union_of_not_close
      (isIndepSet_prod τ₁.indep_B τ₂.indep_B)
      (starM1_indep τ₁ τ₂)
      (fun _ ha _ hb => starM0_not_close_M1 τ₁ τ₂ ha hb))
    (starM2_indep τ₁ τ₂) ?_
  intro a ha b hb
  rcases Finset.mem_union.mp ha with ha0 | ha1
  · exact starM0_not_close_M2 τ₁ τ₂ ha0 hb
  · exact starM1_not_close_M2 τ₁ τ₂ ha1 hb

theorem star_priv_left (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂)
    {s₁ p₁ : V₁} {o₂ : V₂} (ho₂ : o₂ ∈ τ₂.O)
    (hpriv : (p₁ = s₁ ∨ G₁.Adj p₁ s₁) ∧ ∀ x ∈ τ₁.I, (x = p₁ ∨ G₁.Adj x p₁) → x = s₁)
    (hp_in_P : p₁ ∈ τ₁.P0 ∨ p₁ ∈ τ₁.P1) :
    ((p₁, o₂) = (s₁, o₂) ∨ (G₁ ⊠ G₂).Adj (p₁, o₂) (s₁, o₂)) ∧
      ∀ x ∈ starI τ₁ τ₂, (x = (p₁, o₂) ∨ (G₁ ⊠ G₂).Adj x (p₁, o₂)) → x = (s₁, o₂) := by
  classical
  refine ⟨eq_or_strongProd_adj.mpr ⟨hpriv.1, Or.inl rfl⟩, ?_⟩
  intro ⟨x₁, x₂⟩ hx hclose
  rcases eq_or_strongProd_adj.mp hclose with ⟨h1, h2⟩
  simp only [starI, starM0, starM1, starM2, Finset.mem_union, Finset.mem_product] at hx
  rcases hx with ((hx | ((hx | hx) | hx)) | ((hx | hx) | hx))
  · exact False.elim (by
      rcases hp_in_P with hp0 | hp1
      · exact τ₁.B_not_close_P0 hx.1 hp0 h1
      · exact τ₁.B_not_close_P1 hx.1 hp1 h1)
  · exact Prod.ext
      (hpriv.2 x₁ (τ₁.sub_S hx.1) h1)
      (isIndepSet_eq_of_close τ₂.indep_X (τ₂.O_subset_X hx.2) (τ₂.O_subset_X ho₂) h2)
  · exact False.elim (τ₂.O_not_close_H ho₂ hx.2 (close_symm h2))
  · exact False.elim (τ₂.O_not_close_Vset ho₂ hx.2 (close_symm h2))
  · exact False.elim (by
      rcases hp_in_P with hp0 | hp1
      · exact τ₁.O_not_close_P0 hx.1 hp0 h1
      · exact τ₁.O_not_close_P1 hx.1 hp1 h1)
  · exact False.elim (τ₂.O_not_close_P1 ho₂ hx.2 (close_symm h2))
  · exact False.elim (τ₂.O_not_close_P0 ho₂ hx.2 (close_symm h2))

theorem star_priv_right (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂)
    {o₁ : V₁} {s₂ p₂ : V₂} (ho₁ : o₁ ∈ τ₁.O)
    (hpriv : (p₂ = s₂ ∨ G₂.Adj p₂ s₂) ∧ ∀ y ∈ τ₂.I, (y = p₂ ∨ G₂.Adj y p₂) → y = s₂)
    (hp_in_P : p₂ ∈ τ₂.P0 ∨ p₂ ∈ τ₂.P1) :
    ((o₁, p₂) = (o₁, s₂) ∨ (G₁ ⊠ G₂).Adj (o₁, p₂) (o₁, s₂)) ∧
      ∀ x ∈ starI τ₁ τ₂, (x = (o₁, p₂) ∨ (G₁ ⊠ G₂).Adj x (o₁, p₂)) → x = (o₁, s₂) := by
  classical
  refine ⟨eq_or_strongProd_adj.mpr ⟨Or.inl rfl, hpriv.1⟩, ?_⟩
  intro ⟨x₁, x₂⟩ hx hclose
  rcases eq_or_strongProd_adj.mp hclose with ⟨h1, h2⟩
  simp only [starI, starM0, starM1, starM2, Finset.mem_union, Finset.mem_product] at hx
  rcases hx with ((hx | ((hx | hx) | hx)) | ((hx | hx) | hx))
  · exact False.elim (by
      rcases hp_in_P with hp0 | hp1
      · exact τ₂.B_not_close_P0 hx.2 hp0 h2
      · exact τ₂.B_not_close_P1 hx.2 hp1 h2)
  · exact False.elim (by
      rcases hp_in_P with hp0 | hp1
      · exact τ₂.O_not_close_P0 hx.2 hp0 h2
      · exact τ₂.O_not_close_P1 hx.2 hp1 h2)
  · exact False.elim (τ₁.O_not_close_P0 ho₁ hx.1 (close_symm h1))
  · exact False.elim (τ₁.O_not_close_P1 ho₁ hx.1 (close_symm h1))
  · exact Prod.ext
      (isIndepSet_eq_of_close τ₁.indep_X (τ₁.O_subset_X hx.1) (τ₁.O_subset_X ho₁) h1)
      (hpriv.2 x₂ (τ₂.sub_S hx.2) h2)
  · exact False.elim (τ₁.O_not_close_H ho₁ hx.1 (close_symm h1))
  · exact False.elim (τ₁.O_not_close_Vset ho₁ hx.1 (close_symm h1))

theorem star_close_P0_iff (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂)
    {x₁ : V₁} {x₂ : V₂} (hx₁ : x₁ ∈ τ₁.X) (hx₂ : x₂ ∈ τ₂.X) :
    (∃ s ∈ starS τ₁ τ₂, (x₁, x₂) = starF0 τ₁ τ₂ s ∨ (G₁ ⊠ G₂).Adj (x₁, x₂) (starF0 τ₁ τ₂ s)) ↔
      (x₁ ∈ τ₁.H ∧ x₂ ∈ τ₂.O) ∨ (x₁ ∈ τ₁.O ∧ x₂ ∈ τ₂.H) := by
  classical
  constructor
  · rintro ⟨⟨a, b⟩, hs, hclose⟩
    rcases Finset.mem_union.mp hs with hs | hs
    · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
      rw [starF0_left τ₁ τ₂ ha, eq_or_strongProd_adj] at hclose
      have hx2eq : x₂ = b := isIndepSet_eq_of_close τ₂.indep_X hx₂ (τ₂.O_subset_X hb) hclose.2
      exact Or.inl ⟨mem_H.mpr ⟨hx₁, a, ha, hclose.1⟩, hx2eq ▸ hb⟩
    · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
      rw [starF0_right τ₁ τ₂ ha, eq_or_strongProd_adj] at hclose
      have hx1eq : x₁ = a := isIndepSet_eq_of_close τ₁.indep_X hx₁ (τ₁.O_subset_X ha) hclose.1
      exact Or.inr ⟨hx1eq ▸ ha, mem_H.mpr ⟨hx₂, b, hb, hclose.2⟩⟩
  · rintro (⟨hH₁, hO₂⟩ | ⟨hO₁, hH₂⟩)
    · rcases (mem_H.mp hH₁).2 with ⟨s₁, hs₁, hc₁⟩
      refine ⟨(s₁, x₂), Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hs₁, hO₂⟩), ?_⟩
      rw [starF0_left τ₁ τ₂ hs₁, eq_or_strongProd_adj]
      exact ⟨hc₁, Or.inl rfl⟩
    · rcases (mem_H.mp hH₂).2 with ⟨s₂, hs₂, hc₂⟩
      refine ⟨(x₁, s₂), Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hO₁, hs₂⟩), ?_⟩
      rw [starF0_right τ₁ τ₂ hO₁, eq_or_strongProd_adj]
      exact ⟨Or.inl rfl, hc₂⟩

theorem star_close_P1_iff (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂)
    {x₁ : V₁} {x₂ : V₂} (hx₁ : x₁ ∈ τ₁.X) (hx₂ : x₂ ∈ τ₂.X) :
    (∃ s ∈ starS τ₁ τ₂, (x₁, x₂) = starF1 τ₁ τ₂ s ∨ (G₁ ⊠ G₂).Adj (x₁, x₂) (starF1 τ₁ τ₂ s)) ↔
      (x₁ ∈ τ₁.Vset ∧ x₂ ∈ τ₂.O) ∨ (x₁ ∈ τ₁.O ∧ x₂ ∈ τ₂.Vset) := by
  classical
  constructor
  · rintro ⟨⟨a, b⟩, hs, hclose⟩
    rcases Finset.mem_union.mp hs with hs | hs
    · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
      rw [starF1_left τ₁ τ₂ ha, eq_or_strongProd_adj] at hclose
      have hx2eq : x₂ = b := isIndepSet_eq_of_close τ₂.indep_X hx₂ (τ₂.O_subset_X hb) hclose.2
      exact Or.inl ⟨mem_Vset.mpr ⟨hx₁, a, ha, hclose.1⟩, hx2eq ▸ hb⟩
    · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
      rw [starF1_right τ₁ τ₂ ha, eq_or_strongProd_adj] at hclose
      have hx1eq : x₁ = a := isIndepSet_eq_of_close τ₁.indep_X hx₁ (τ₁.O_subset_X ha) hclose.1
      exact Or.inr ⟨hx1eq ▸ ha, mem_Vset.mpr ⟨hx₂, b, hb, hclose.2⟩⟩
  · rintro (⟨hV₁, hO₂⟩ | ⟨hO₁, hV₂⟩)
    · rcases (mem_Vset.mp hV₁).2 with ⟨s₁, hs₁, hc₁⟩
      refine ⟨(s₁, x₂), Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hs₁, hO₂⟩), ?_⟩
      rw [starF1_left τ₁ τ₂ hs₁, eq_or_strongProd_adj]
      exact ⟨hc₁, Or.inl rfl⟩
    · rcases (mem_Vset.mp hV₂).2 with ⟨s₂, hs₂, hc₂⟩
      refine ⟨(x₁, s₂), Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hO₁, hs₂⟩), ?_⟩
      rw [starF1_right τ₁ τ₂ hO₁, eq_or_strongProd_adj]
      exact ⟨Or.inl rfl, hc₂⟩

/-- Constructive strong product `τ₁.star τ₂ : ValidTuple (G₁ ⊠ G₂)`. -/
noncomputable def star (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) : ValidTuple (G₁ ⊠ G₂) where
  I := starI τ₁ τ₂
  S := starS τ₁ τ₂
  f0 := starF0 τ₁ τ₂
  f1 := starF1 τ₁ τ₂
  X := τ₁.X ×ˢ τ₂.X
  indep_I := starI_indep τ₁ τ₂
  sub_S := by
    classical
    intro p hp
    simp only [starS, starI, starM1, starM2, Finset.mem_union] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl (Or.inr (Or.inl (Or.inl hp)))
    · exact Or.inr (Or.inl (Or.inl hp))
  self_mem := by
    classical
    intro ⟨a, b⟩ hs
    rcases Finset.mem_union.mp hs with hs | hs
    · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
      rw [starF0_left τ₁ τ₂ ha, starF1_left τ₁ τ₂ ha]
      exact (τ₁.self_mem a ha).imp (fun h => Prod.ext h rfl) (fun h => Prod.ext h rfl)
    · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
      rw [starF0_right τ₁ τ₂ ha, starF1_right τ₁ τ₂ ha]
      exact (τ₂.self_mem b hb).imp (fun h => Prod.ext rfl h) (fun h => Prod.ext rfl h)
  priv0 := by
    classical
    intro ⟨a, b⟩ hs
    rcases Finset.mem_union.mp hs with hs | hs
    · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
      rw [starF0_left τ₁ τ₂ ha]
      exact star_priv_left τ₁ τ₂ hb (τ₁.priv0 a ha) (Or.inl (mem_P0.mpr ⟨a, ha, rfl⟩))
    · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
      rw [starF0_right τ₁ τ₂ ha]
      exact star_priv_right τ₁ τ₂ ha (τ₂.priv0 b hb) (Or.inl (mem_P0.mpr ⟨b, hb, rfl⟩))
  priv1 := by
    classical
    intro ⟨a, b⟩ hs
    rcases Finset.mem_union.mp hs with hs | hs
    · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
      rw [starF1_left τ₁ τ₂ ha]
      exact star_priv_left τ₁ τ₂ hb (τ₁.priv1 a ha) (Or.inr (mem_P1.mpr ⟨a, ha, rfl⟩))
    · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
      rw [starF1_right τ₁ τ₂ ha]
      exact star_priv_right τ₁ τ₂ ha (τ₂.priv1 b hb) (Or.inr (mem_P1.mpr ⟨b, hb, rfl⟩))
  indep_P0 := by
    classical
    have hsub : starF0 τ₁ τ₂ '' (starS τ₁ τ₂ : Set (V₁ × V₂)) ⊆
        (((τ₁.P0 ×ˢ τ₂.O) ∪ (τ₁.O ×ˢ τ₂.P0) : Finset (V₁ × V₂)) : Set (V₁ × V₂)) := by
      rintro _ ⟨⟨a, b⟩, hs, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_product]
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hs) with hs | hs
      · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
        rw [starF0_left τ₁ τ₂ ha]
        exact Or.inl ⟨mem_P0.mpr ⟨a, ha, rfl⟩, hb⟩
      · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
        rw [starF0_right τ₁ τ₂ ha]
        exact Or.inr ⟨ha, mem_P0.mpr ⟨b, hb, rfl⟩⟩
    refine (isIndepSet_union_of_not_close
      (isIndepSet_prod τ₁.indep_P0_finset τ₂.indep_O)
      (isIndepSet_prod τ₁.indep_O τ₂.indep_P0_finset) ?_).mono hsub
    rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb hclose
    simp only [Finset.mem_product] at ha hb
    exact τ₁.O_not_close_P0 hb.1 ha.1 (close_symm (eq_or_strongProd_adj.mp hclose).1)
  indep_P1 := by
    classical
    have hsub : starF1 τ₁ τ₂ '' (starS τ₁ τ₂ : Set (V₁ × V₂)) ⊆
        (((τ₁.P1 ×ˢ τ₂.O) ∪ (τ₁.O ×ˢ τ₂.P1) : Finset (V₁ × V₂)) : Set (V₁ × V₂)) := by
      rintro _ ⟨⟨a, b⟩, hs, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_product]
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hs) with hs | hs
      · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
        rw [starF1_left τ₁ τ₂ ha]
        exact Or.inl ⟨mem_P1.mpr ⟨a, ha, rfl⟩, hb⟩
      · rcases Finset.mem_product.mp hs with ⟨ha, hb⟩
        rw [starF1_right τ₁ τ₂ ha]
        exact Or.inr ⟨ha, mem_P1.mpr ⟨b, hb, rfl⟩⟩
    refine (isIndepSet_union_of_not_close
      (isIndepSet_prod τ₁.indep_P1_finset τ₂.indep_O)
      (isIndepSet_prod τ₁.indep_O τ₂.indep_P1_finset) ?_).mono hsub
    rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb hclose
    simp only [Finset.mem_product] at ha hb
    exact τ₁.O_not_close_P1 hb.1 ha.1 (close_symm (eq_or_strongProd_adj.mp hclose).1)
  indep_X := isIndepSet_prod τ₁.indep_X τ₂.indep_X
  disj_nbr := by
    rintro ⟨x₁, x₂⟩ hx ⟨h0, h1⟩
    rcases Finset.mem_product.mp hx with ⟨hx₁, hx₂⟩
    rw [star_close_P0_iff τ₁ τ₂ hx₁ hx₂] at h0
    rw [star_close_P1_iff τ₁ τ₂ hx₁ hx₂] at h1
    rcases h0 with ⟨hH₁, hO₂⟩ | ⟨hO₁, hH₂⟩ <;> rcases h1 with ⟨hV₁, _⟩ | ⟨hO₁', hV₂⟩
    · exact τ₁.H_not_close_Vset hH₁ hV₁ (Or.inl rfl)
    · exact τ₁.O_not_close_H hO₁' hH₁ (Or.inl rfl)
    · exact τ₁.O_not_close_Vset hO₁ hV₁ (Or.inl rfl)
    · exact τ₂.H_not_close_Vset hH₂ hV₂ (Or.inl rfl)

/-- Exact profile law: `(τ₁.star τ₂).profile = τ₁.profile.star τ₂.profile`. -/
theorem star_profile (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) :
    (τ₁.star τ₂).profile = τ₁.profile.star τ₂.profile := by
  classical
  apply Profile.ext
  · -- `a`: cardinality of `starI = starM0 ∪ starM1 ∪ starM2`
    show (starI τ₁ τ₂).card =
      (τ₁.I.card - τ₁.S.card) * (τ₂.I.card - τ₂.S.card) +
        τ₁.X.card * τ₂.S.card + τ₁.S.card * τ₂.X.card
    have hd01 : Disjoint (starM0 τ₁ τ₂) (starM1 τ₁ τ₂) :=
      disjoint_of_not_close fun _ ha _ hb => starM0_not_close_M1 τ₁ τ₂ ha hb
    have hd02 : Disjoint (starM0 τ₁ τ₂) (starM2 τ₁ τ₂) :=
      disjoint_of_not_close fun _ ha _ hb => starM0_not_close_M2 τ₁ τ₂ ha hb
    have hd12 : Disjoint (starM1 τ₁ τ₂) (starM2 τ₁ τ₂) :=
      disjoint_of_not_close fun _ ha _ hb => starM1_not_close_M2 τ₁ τ₂ ha hb
    have hM0 : (starM0 τ₁ τ₂).card = (τ₁.I.card - τ₁.S.card) * (τ₂.I.card - τ₂.S.card) := by
      simp [starM0, Finset.card_product, τ₁.card_B, τ₂.card_B]
    have hM1 : (starM1 τ₁ τ₂).card = τ₁.S.card * τ₂.X.card := by
      have hOH : Disjoint (τ₁.S ×ˢ τ₂.O) (τ₁.P0 ×ˢ τ₂.H) :=
        disjoint_of_not_close (G := G₁ ⊠ G₂) fun _ ha _ hb hc =>
          τ₂.O_not_close_H (Finset.mem_product.mp ha).2 (Finset.mem_product.mp hb).2
            (eq_or_strongProd_adj.mp hc).2
      have hOV : Disjoint (τ₁.S ×ˢ τ₂.O) (τ₁.P1 ×ˢ τ₂.Vset) :=
        disjoint_of_not_close (G := G₁ ⊠ G₂) fun _ ha _ hb hc =>
          τ₂.O_not_close_Vset (Finset.mem_product.mp ha).2 (Finset.mem_product.mp hb).2
            (eq_or_strongProd_adj.mp hc).2
      have hHV : Disjoint (τ₁.P0 ×ˢ τ₂.H) (τ₁.P1 ×ˢ τ₂.Vset) :=
        disjoint_of_not_close (G := G₁ ⊠ G₂) fun _ ha _ hb hc =>
          τ₂.H_not_close_Vset (Finset.mem_product.mp ha).2 (Finset.mem_product.mp hb).2
            (eq_or_strongProd_adj.mp hc).2
      unfold starM1
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hOV, hHV⟩),
        Finset.card_union_of_disjoint hOH,
        Finset.card_product, Finset.card_product, Finset.card_product,
        τ₁.card_P0, τ₁.card_P1, ← Nat.mul_add, ← Nat.mul_add, τ₂.card_X_partition]
    have hM2 : (starM2 τ₁ τ₂).card = τ₁.X.card * τ₂.S.card := by
      have hOH : Disjoint (τ₁.O ×ˢ τ₂.S) (τ₁.H ×ˢ τ₂.P1) :=
        disjoint_of_not_close (G := G₁ ⊠ G₂) fun _ ha _ hb hc =>
          τ₁.O_not_close_H (Finset.mem_product.mp ha).1 (Finset.mem_product.mp hb).1
            (eq_or_strongProd_adj.mp hc).1
      have hOV : Disjoint (τ₁.O ×ˢ τ₂.S) (τ₁.Vset ×ˢ τ₂.P0) :=
        disjoint_of_not_close (G := G₁ ⊠ G₂) fun _ ha _ hb hc =>
          τ₁.O_not_close_Vset (Finset.mem_product.mp ha).1 (Finset.mem_product.mp hb).1
            (eq_or_strongProd_adj.mp hc).1
      have hHV : Disjoint (τ₁.H ×ˢ τ₂.P1) (τ₁.Vset ×ˢ τ₂.P0) :=
        disjoint_of_not_close (G := G₁ ⊠ G₂) fun _ ha _ hb hc =>
          τ₁.H_not_close_Vset (Finset.mem_product.mp ha).1 (Finset.mem_product.mp hb).1
            (eq_or_strongProd_adj.mp hc).1
      unfold starM2
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hOV, hHV⟩),
        Finset.card_union_of_disjoint hOH,
        Finset.card_product, Finset.card_product, Finset.card_product,
        τ₂.card_P1, τ₂.card_P0, ← Nat.add_mul, ← Nat.add_mul, τ₁.card_X_partition]
    unfold starI
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd02, hd12⟩),
      Finset.card_union_of_disjoint hd01, hM0, hM1, hM2]
    omega
  · -- `b`: cardinality of `starS = (S₁ × O₂) ∪ (O₁ × S₂)`
    show (starS τ₁ τ₂).card = τ₁.O.card * τ₂.S.card + τ₁.S.card * τ₂.O.card
    have hdisj : Disjoint (τ₁.S ×ˢ τ₂.O) (τ₁.O ×ˢ τ₂.S) :=
      disjoint_of_not_close (G := G₁ ⊠ G₂) fun _ ha _ hb hc =>
        τ₁.O_not_close_S (Finset.mem_product.mp hb).1 (Finset.mem_product.mp ha).1
          (close_symm (eq_or_strongProd_adj.mp hc).1)
    unfold starS
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product]
    omega
  · -- `c`: cardinality of `X₁ × X₂`
    exact Finset.card_product τ₁.X τ₂.X
  · -- `d`: cardinality of `O₁₂ = (O₁ × O₂) ∪ ((H₁ ∪ V₁) × (H₂ ∪ V₂))`
    show (τ₁.star τ₂).O.card =
      τ₁.O.card * τ₂.O.card + (τ₁.X.card - τ₁.O.card) * (τ₂.X.card - τ₂.O.card)
    have hOeq : (τ₁.star τ₂).O =
        (τ₁.O ×ˢ τ₂.O) ∪ ((τ₁.H ∪ τ₁.Vset) ×ˢ (τ₂.H ∪ τ₂.Vset)) := by
      ext ⟨x₁, x₂⟩
      rw [mem_O]
      simp only [star, Finset.mem_union, Finset.mem_product]
      constructor
      · rintro ⟨⟨hx₁, hx₂⟩, hn0, hn1⟩
        rw [star_close_P0_iff τ₁ τ₂ hx₁ hx₂] at hn0
        rw [star_close_P1_iff τ₁ τ₂ hx₁ hx₂] at hn1
        by_cases h1 : x₁ ∈ τ₁.O
        · by_cases h2 : x₂ ∈ τ₂.O
          · exact Or.inl ⟨h1, h2⟩
          · exfalso
            have hx2hv : x₂ ∈ τ₂.H ∨ x₂ ∈ τ₂.Vset := by
              by_cases hc0 : ∃ s ∈ τ₂.S, x₂ = τ₂.f0 s ∨ G₂.Adj x₂ (τ₂.f0 s)
              · exact Or.inl (mem_H.mpr ⟨hx₂, hc0⟩)
              · by_cases hc1 : ∃ s ∈ τ₂.S, x₂ = τ₂.f1 s ∨ G₂.Adj x₂ (τ₂.f1 s)
                · exact Or.inr (mem_Vset.mpr ⟨hx₂, hc1⟩)
                · exact False.elim (h2 (mem_O.mpr ⟨hx₂, hc0, hc1⟩))
            rcases hx2hv with hH₂ | hV₂
            · exact hn0 (Or.inr ⟨h1, hH₂⟩)
            · exact hn1 (Or.inr ⟨h1, hV₂⟩)
        · have hx1hv : x₁ ∈ τ₁.H ∨ x₁ ∈ τ₁.Vset := by
            by_cases hc0 : ∃ s ∈ τ₁.S, x₁ = τ₁.f0 s ∨ G₁.Adj x₁ (τ₁.f0 s)
            · exact Or.inl (mem_H.mpr ⟨hx₁, hc0⟩)
            · by_cases hc1 : ∃ s ∈ τ₁.S, x₁ = τ₁.f1 s ∨ G₁.Adj x₁ (τ₁.f1 s)
              · exact Or.inr (mem_Vset.mpr ⟨hx₁, hc1⟩)
              · exact False.elim (h1 (mem_O.mpr ⟨hx₁, hc0, hc1⟩))
          by_cases h2 : x₂ ∈ τ₂.O
          · exfalso
            rcases hx1hv with hH₁ | hV₁
            · exact hn0 (Or.inl ⟨hH₁, h2⟩)
            · exact hn1 (Or.inl ⟨hV₁, h2⟩)
          · have hx2hv : x₂ ∈ τ₂.H ∨ x₂ ∈ τ₂.Vset := by
              by_cases hc0 : ∃ s ∈ τ₂.S, x₂ = τ₂.f0 s ∨ G₂.Adj x₂ (τ₂.f0 s)
              · exact Or.inl (mem_H.mpr ⟨hx₂, hc0⟩)
              · by_cases hc1 : ∃ s ∈ τ₂.S, x₂ = τ₂.f1 s ∨ G₂.Adj x₂ (τ₂.f1 s)
                · exact Or.inr (mem_Vset.mpr ⟨hx₂, hc1⟩)
                · exact False.elim (h2 (mem_O.mpr ⟨hx₂, hc0, hc1⟩))
            exact Or.inr ⟨hx1hv, hx2hv⟩
      · rintro (⟨hO₁, hO₂⟩ | ⟨hHV₁, hHV₂⟩)
        · have hx₁ := τ₁.O_subset_X hO₁
          have hx₂ := τ₂.O_subset_X hO₂
          refine ⟨⟨hx₁, hx₂⟩, ?_, ?_⟩
          · rw [star_close_P0_iff τ₁ τ₂ hx₁ hx₂]
            rintro (⟨hH₁, _⟩ | ⟨_, hH₂⟩)
            · exact τ₁.O_not_close_H hO₁ hH₁ (Or.inl rfl)
            · exact τ₂.O_not_close_H hO₂ hH₂ (Or.inl rfl)
          · rw [star_close_P1_iff τ₁ τ₂ hx₁ hx₂]
            rintro (⟨hV₁, _⟩ | ⟨_, hV₂⟩)
            · exact τ₁.O_not_close_Vset hO₁ hV₁ (Or.inl rfl)
            · exact τ₂.O_not_close_Vset hO₂ hV₂ (Or.inl rfl)
        · have hx₁ : x₁ ∈ τ₁.X := hHV₁.elim (fun h => τ₁.H_subset_X h) (fun h => τ₁.Vset_subset_X h)
          have hx₂ : x₂ ∈ τ₂.X := hHV₂.elim (fun h => τ₂.H_subset_X h) (fun h => τ₂.Vset_subset_X h)
          refine ⟨⟨hx₁, hx₂⟩, ?_, ?_⟩
          · rw [star_close_P0_iff τ₁ τ₂ hx₁ hx₂]
            rintro (⟨_, hO₂⟩ | ⟨hO₁, _⟩)
            · exact hHV₂.elim (fun h => τ₂.O_not_close_H hO₂ h (Or.inl rfl))
                (fun h => τ₂.O_not_close_Vset hO₂ h (Or.inl rfl))
            · exact hHV₁.elim (fun h => τ₁.O_not_close_H hO₁ h (Or.inl rfl))
                (fun h => τ₁.O_not_close_Vset hO₁ h (Or.inl rfl))
          · rw [star_close_P1_iff τ₁ τ₂ hx₁ hx₂]
            rintro (⟨_, hO₂⟩ | ⟨hO₁, _⟩)
            · exact hHV₂.elim (fun h => τ₂.O_not_close_H hO₂ h (Or.inl rfl))
                (fun h => τ₂.O_not_close_Vset hO₂ h (Or.inl rfl))
            · exact hHV₁.elim (fun h => τ₁.O_not_close_H hO₁ h (Or.inl rfl))
                (fun h => τ₁.O_not_close_Vset hO₁ h (Or.inl rfl))
    have hdisj : Disjoint (τ₁.O ×ˢ τ₂.O) ((τ₁.H ∪ τ₁.Vset) ×ˢ (τ₂.H ∪ τ₂.Vset)) := by
      rw [Finset.disjoint_left]
      intro ⟨a, b⟩ h1 h2
      have haO : a ∈ τ₁.O := (Finset.mem_product.mp h1).1
      have haHV : a ∈ τ₁.H ∪ τ₁.Vset := (Finset.mem_product.mp h2).1
      rcases Finset.mem_union.mp haHV with hH | hV
      · exact τ₁.O_not_close_H haO hH (Or.inl rfl)
      · exact τ₁.O_not_close_Vset haO hV (Or.inl rfl)
    rw [hOeq, Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product,
      τ₁.card_HV, τ₂.card_HV]

end Star

end ValidTuple

/-! ## Recursive Split-Tree Engine (`SplitTree` & `ValidTuple.evalTree`) -/

/-- Binary recursion plan (with sharing-friendly squaring node `.sq`) producing a `k`-fold
iterated `ValidTuple.star` power. -/
inductive SplitTree : ℕ → Type
  | leaf : SplitTree 1
  | sq {k : ℕ} (t : SplitTree k) : SplitTree (k + k)
  | node {k₁ k₂ : ℕ} (left : SplitTree k₁) (right : SplitTree k₂) : SplitTree (k₁ + k₂)

namespace SplitTree

/-- Every `SplitTree k` has strictly positive fold multiplicity `0 < k`. -/
theorem pos : {k : ℕ} → SplitTree k → 0 < k
  | _, .leaf => Nat.one_pos
  | _, .sq t => Nat.add_pos_left t.pos _
  | _, .node t₁ _ => Nat.add_pos_left t₁.pos _

/-- Computable profile evaluator for a `SplitTree`. -/
def evalProfile : {k : ℕ} → SplitTree k → Profile → Profile
  | _, .leaf, p => p
  | _, .sq t, p =>
      let q := t.evalProfile p
      q.star q
  | _, .node t₁ t₂, p => (t₁.evalProfile p).star (t₂.evalProfile p)

end SplitTree

/-- Graph isomorphism cast along an equality of strong-power exponents. -/
def strongPowCast {V : Type*} (G : SimpleGraph V) {m n : ℕ} (h : m = n) :
    strongPow G m ≃g strongPow G n :=
  h ▸ SimpleGraph.Iso.refl

/-- Constructive evaluation of a `SplitTree k` on a base `ValidTuple (strongPow G m)`. -/
noncomputable def ValidTuple.evalTree {V : Type*} [Fintype V] {G : SimpleGraph V} {m : ℕ}
    (τ : ValidTuple (strongPow G m)) : {k : ℕ} → SplitTree k → ValidTuple (strongPow G (m * k))
  | _, .leaf => τ.congr (strongPowCast G (Nat.mul_one m).symm)
  | _, .sq t =>
      let τ' := τ.evalTree t
      (τ'.star τ').congr
        ((strongPowAddEquiv G (m * _) (m * _)).symm.trans
          (strongPowCast G (Nat.mul_add m _ _).symm))
  | _, .node t₁ t₂ =>
      ((τ.evalTree t₁).star (τ.evalTree t₂)).congr
        ((strongPowAddEquiv G (m * _) (m * _)).symm.trans
          (strongPowCast G (Nat.mul_add m _ _).symm))

theorem ValidTuple.evalTree_profile {V : Type*} [Fintype V] {G : SimpleGraph V} {m : ℕ}
    (τ : ValidTuple (strongPow G m)) :
    ∀ {k : ℕ} (t : SplitTree k), (τ.evalTree t).profile = t.evalProfile τ.profile
  | _, .leaf => by
      simp [ValidTuple.evalTree, SplitTree.evalProfile]
  | _, .sq t => by
      simp only [ValidTuple.evalTree, SplitTree.evalProfile, congr_profile, star_profile,
        evalTree_profile τ t]
  | _, .node t₁ t₂ => by
      simp only [ValidTuple.evalTree, SplitTree.evalProfile, congr_profile, star_profile,
        evalTree_profile τ t₁, evalTree_profile τ t₂]

/-- Contract alias for `ValidTuple.evalTree`: recursive split-tree realization of iterated `star`. -/
noncomputable def ValidTuple.splitTree {V : Type*} [Fintype V] {G : SimpleGraph V} {m : ℕ}
    (τ : ValidTuple (strongPow G m)) {k : ℕ} (t : SplitTree k) :
    ValidTuple (strongPow G (m * k)) :=
  τ.evalTree t

theorem ValidTuple.splitTree_profile {V : Type*} [Fintype V] {G : SimpleGraph V} {m : ℕ}
    (τ : ValidTuple (strongPow G m)) {k : ℕ} (t : SplitTree k) :
    (τ.splitTree t).profile = t.evalProfile τ.profile :=
  τ.evalTree_profile t

/-- Direct Shannon capacity lower bound from a `ValidTuple` and a `SplitTree` via exact `Nat`
power comparison. -/
theorem ValidTuple.le_shannonCapacity_of_evalTree {V : Type*} [Fintype V] {G : SimpleGraph V}
    {m k num den : ℕ} (hm : 0 < m) (hden : 0 < den)
    (τ : ValidTuple (strongPow G m)) (t : SplitTree k)
    (hpow : num ^ (m * k) ≤ den ^ (m * k) * (t.evalProfile τ.profile).a) :
    (num : ℝ) / (den : ℝ) ≤ shannonCapacity G := by
  apply le_shannonCapacity_of_nat_pow (Nat.mul_pos hm t.pos) hden _ hpow
  rw [← τ.evalTree_profile t]
  exact (τ.evalTree t).card_le_indepNum

/-- Direct `strongPowPi (SimpleGraph.cycleGraph 7) (m * k)` independence-number lower bound
from a `ValidTuple (strongPow C7 m)` and a `SplitTree k`. -/
theorem ValidTuple.evalTree_a_le_cycleGraph7_indepNum {m k : ℕ}
    (τ : ValidTuple (strongPow C7 m)) (t : SplitTree k) :
    (t.evalProfile τ.profile).a ≤ (strongPowPi (SimpleGraph.cycleGraph 7) (m * k)).indepNum := by
  rw [cycleGraph7_strongPowPi_indepNum_eq, ← τ.evalTree_profile t]
  exact (τ.evalTree t).card_le_indepNum

/-- Direct `SimpleGraph.cycleGraph 7` Shannon capacity lower bound from a `ValidTuple` on
`strongPow C7 m` and a `SplitTree k`. -/
theorem ValidTuple.le_shannonCapacity_cycleGraph7_of_evalTree
    {m k num den : ℕ} (hm : 0 < m) (hden : 0 < den)
    (τ : ValidTuple (strongPow C7 m)) (t : SplitTree k)
    (hpow : num ^ (m * k) ≤ den ^ (m * k) * (t.evalProfile τ.profile).a) :
    (num : ℝ) / (den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) := by
  rw [← shannonCapacity_c7_eq_cycleGraph]
  exact τ.le_shannonCapacity_of_evalTree hm hden t hpow

/-- Convenience wrapper taking an explicit profile equality `τ.profile = p` so callers can pass
`nat_pow_le_of_ble rfl` directly on the computable profile `p`. -/
theorem ValidTuple.le_shannonCapacity_cycleGraph7_of_evalTree_profile
    {m k num den : ℕ} {τ : ValidTuple (strongPow C7 m)} {p : Profile}
    (hm : 0 < m) (hden : 0 < den) (hprof : τ.profile = p) (t : SplitTree k)
    (hpow : num ^ (m * k) ≤ den ^ (m * k) * (t.evalProfile p).a) :
    (num : ℝ) / (den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  τ.le_shannonCapacity_cycleGraph7_of_evalTree hm hden t (hprof ▸ hpow)

/-! ## Canonical Split Trees (`k = 2, 38, 40, 42`) -/

/-- `k = 2` split tree (`d = 10` from 5D base; Itty et al. 2026). -/
def splitTree2 : SplitTree 2 := .sq .leaf

/-- `k = 40` split tree (`1 → 2 → 3 → 5 → 10 → 20 → 40`; `d = 200`, Gao / BPZ v1 2026). -/
def splitTree40 : SplitTree 40 :=
  let t2 : SplitTree 2 := .sq .leaf
  let t3 : SplitTree 3 := .node .leaf t2
  let t5 : SplitTree 5 := .node t2 t3
  let t10 : SplitTree 10 := .sq t5
  let t20 : SplitTree 20 := .sq t10
  .sq t20

/-- `k = 42` optimal split tree (`1→2→3→5,6→10,11→21→42`; `d = 210`, optimal for `d₀ ∈ {323, 324}`). -/
def splitTree42 : SplitTree 42 :=
  let t2 : SplitTree 2 := .sq .leaf
  let t3 : SplitTree 3 := .node .leaf t2
  let t5 : SplitTree 5 := .node t2 t3
  let t6 : SplitTree 6 := .sq t3
  let t10 : SplitTree 10 := .sq t5
  let t11 : SplitTree 11 := .node t5 t6
  let t21 : SplitTree 21 := .node t10 t11
  .sq t21

/-! ## Pure-Kernel `Trie7` Constructor (`ValidTuple.ofTrie7`) -/

/-- Fast structural equality test on `StrongPowV (ZMod 7) d`. -/
def wordEqBool : {d : ℕ} → StrongPowV (ZMod 7) d → StrongPowV (ZMod 7) d → Bool
  | 0, _, _ => true
  | _ + 1, (a, rx), (b, ry) => (a.val == b.val) && wordEqBool rx ry

private theorem zmod7_val_beq_iff (a b : ZMod 7) : (a.val == b.val) = true ↔ a = b := by
  revert a b
  decide

theorem wordEqBool_eq_true_iff : {d : ℕ} → (x y : StrongPowV (ZMod 7) d) →
    (wordEqBool x y = true ↔ x = y)
  | 0, .unit, .unit => ⟨fun _ => rfl, fun _ => rfl⟩
  | _ + 1, (a, rx), (b, ry) =>
      (Iff.of_eq (Bool.and_eq_true _ _)).trans <|
        (and_congr (zmod7_val_beq_iff a b) (wordEqBool_eq_true_iff rx ry)).trans
          ⟨fun ⟨h1, h2⟩ => congrArg₂ Prod.mk h1 h2,
           fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

/-- A port entry `(s, p0, p1)` in `StrongPowV (ZMod 7) d`. -/
abbrev PortEntry (d : ℕ) :=
  StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d

/-- Lookup `f0` value for `x` from a port list (defaulting to `x` outside `S`). -/
def lookupPort0 {d : ℕ} : List (PortEntry d) → StrongPowV (ZMod 7) d → StrongPowV (ZMod 7) d
  | [], x => x
  | (s, p0, _) :: tl, x => if wordEqBool s x then p0 else lookupPort0 tl x

/-- Lookup `f1` value for `x` from a port list (defaulting to `x` outside `S`). -/
def lookupPort1 {d : ℕ} : List (PortEntry d) → StrongPowV (ZMod 7) d → StrongPowV (ZMod 7) d
  | [], x => x
  | (s, _, p1) :: tl, x => if wordEqBool s x then p1 else lookupPort1 tl x

/-- Pure-kernel pairwise distinctness check for port centers `ports.map Prod.fst`. -/
def portsNodupBool {d : ℕ} : List (PortEntry d) → Bool
  | [] => true
  | e :: tl => tl.all (fun e' => !wordEqBool e.1 e'.1) && portsNodupBool tl

/-- Pure-kernel checker for all per-port validity conditions against `tI`, `tP0`, `tP1`. -/
def validPortsBool {d : ℕ} (tI tP0 tP1 : Trie7 d) : List (PortEntry d) → Bool
  | [] => true
  | (s, p0, p1) :: tl =>
      tI.memBool s &&
      (wordEqBool p0 s || wordEqBool p1 s) &&
      Trie7.closeBool s p0 &&
      Trie7.closeBool s p1 &&
      (tI.closedNbrCount p0 == 1) &&
      (tI.closedNbrCount p1 == 1) &&
      tP0.memBool p0 &&
      tP1.memBool p1 &&
      validPortsBool tI tP0 tP1 tl

theorem portsNodup_of_bool {d : ℕ} :
    ∀ {ports : List (PortEntry d)}, portsNodupBool ports = true →
      (ports.map Prod.fst).Nodup
  | [], _ => List.nodup_nil
  | e :: tl, h => by
      simp only [portsNodupBool, Bool.and_eq_true, List.all_eq_true,
        Bool.not_eq_true', Bool.eq_false_iff, ne_eq] at h
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, portsNodup_of_bool h.2⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨e', he', heq⟩
      exact h.1 e' he' ((wordEqBool_eq_true_iff e.1 e'.1).mpr heq.symm)

theorem lookupPort0_of_mem {d : ℕ} :
    ∀ {ports : List (PortEntry d)}, (ports.map Prod.fst).Nodup →
      ∀ {s p0 p1}, (s, p0, p1) ∈ ports → lookupPort0 ports s = p0
  | [], _, _, _, _, hmem => nomatch hmem
  | (s', p0', p1') :: tl, hnd, s, p0, p1, hmem => by
      rw [List.map_cons, List.nodup_cons] at hnd
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | htl
      · cases heq
        simp only [lookupPort0, (wordEqBool_eq_true_iff s' s').mpr rfl, ↓reduceIte]
      · have hne : s' ≠ s := fun h => hnd.1 (List.mem_map.mpr ⟨(s, p0, p1), htl, h.symm⟩)
        have hbf : wordEqBool s' s = false := by
          cases hb : wordEqBool s' s with
          | false => rfl
          | true => exact absurd ((wordEqBool_eq_true_iff s' s).mp hb) hne
        simp only [lookupPort0, hbf, Bool.false_eq_true, ↓reduceIte]
        exact lookupPort0_of_mem hnd.2 htl

theorem lookupPort1_of_mem {d : ℕ} :
    ∀ {ports : List (PortEntry d)}, (ports.map Prod.fst).Nodup →
      ∀ {s p0 p1}, (s, p0, p1) ∈ ports → lookupPort1 ports s = p1
  | [], _, _, _, _, hmem => nomatch hmem
  | (s', p0', p1') :: tl, hnd, s, p0, p1, hmem => by
      rw [List.map_cons, List.nodup_cons] at hnd
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | htl
      · cases heq
        simp only [lookupPort1, (wordEqBool_eq_true_iff s' s').mpr rfl, ↓reduceIte]
      · have hne : s' ≠ s := fun h => hnd.1 (List.mem_map.mpr ⟨(s, p0, p1), htl, h.symm⟩)
        have hbf : wordEqBool s' s = false := by
          cases hb : wordEqBool s' s with
          | false => rfl
          | true => exact absurd ((wordEqBool_eq_true_iff s' s).mp hb) hne
        simp only [lookupPort1, hbf, Bool.false_eq_true, ↓reduceIte]
        exact lookupPort1_of_mem hnd.2 htl

theorem validPorts_spec {d : ℕ} {tI tP0 tP1 : Trie7 d} :
    ∀ {ports : List (PortEntry d)}, validPortsBool tI tP0 tP1 ports = true →
      ∀ {s p0 p1}, (s, p0, p1) ∈ ports →
        tI.memBool s = true ∧
        (p0 = s ∨ p1 = s) ∧
        (s = p0 ∨ (strongPow C7 d).Adj s p0) ∧
        (s = p1 ∨ (strongPow C7 d).Adj s p1) ∧
        tI.closedNbrCount p0 = 1 ∧
        tI.closedNbrCount p1 = 1 ∧
        tP0.memBool p0 = true ∧
        tP1.memBool p1 = true
  | [], _, _, _, _, hmem => nomatch hmem
  | (s', p0', p1') :: tl, h, s, p0, p1, hmem => by
      simp only [validPortsBool, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hmemI, hself⟩, hc0⟩, hc1⟩, hcnt0⟩, hcnt1⟩, hmP0⟩, hmP1⟩, htl⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmemtl
      · cases heq
        exact ⟨hmemI,
          hself.imp (wordEqBool_eq_true_iff _ _).mp (wordEqBool_eq_true_iff _ _).mp,
          (Trie7.closeBool_eq_true_iff _ _).mp hc0,
          (Trie7.closeBool_eq_true_iff _ _).mp hc1,
          hcnt0, hcnt1, hmP0, hmP1⟩
      · exact validPorts_spec htl hmemtl

/-- Pure-kernel `ValidTuple` constructor from certified `Trie7 d` tries and an explicit port list. -/
def ValidTuple.ofTrie7 {d : ℕ}
    (tI tP0 tP1 tX : Trie7 d)
    (ports : List (PortEntry d))
    (hI : tI.isIndep = true)
    (hP0 : tP0.isIndep = true)
    (hP1 : tP1.isIndep = true)
    (hX : tX.isIndep = true)
    (hnodup : portsNodupBool ports = true)
    (hports : validPortsBool tI tP0 tP1 ports = true)
    (hcardP0 : tP0.card = ports.length)
    (hcardP1 : tP1.card = ports.length)
    (hdisj : Trie7.disjointCommonNbr tP0 tP1 tX = true) :
    ValidTuple (strongPow C7 d) :=
  let hnd : (ports.map Prod.fst).Nodup := portsNodup_of_bool hnodup
  let Sset : Finset (StrongPowV (ZMod 7) d) := (ports.map Prod.fst).toFinset
  have hS_iff : ∀ s, s ∈ Sset ↔ ∃ p0 p1, (s, p0, p1) ∈ ports := by
    intro s
    simp only [Sset, List.mem_toFinset, List.mem_map, Prod.exists]
    constructor
    · rintro ⟨a, b, c, hmem, rfl⟩; exact ⟨b, c, hmem⟩
    · rintro ⟨p0, p1, hmem⟩; exact ⟨s, p0, p1, hmem, rfl⟩
  have hpriv0 : ∀ s ∈ Sset,
      (lookupPort0 ports s = s ∨ (strongPow C7 d).Adj (lookupPort0 ports s) s) ∧
      ∀ x ∈ tI.toFinset,
        (x = lookupPort0 ports s ∨ (strongPow C7 d).Adj x (lookupPort0 ports s)) → x = s := by
    intro s hs
    rcases (hS_iff s).mp hs with ⟨p0, p1, hmem⟩
    have hf0 : lookupPort0 ports s = p0 := lookupPort0_of_mem hnd hmem
    rcases validPorts_spec hports hmem with ⟨hmI, _, hc0, _, hcnt0, _, _, _⟩
    rw [hf0]
    refine ⟨close_symm hc0, fun x hx hclose =>
      (Trie7.closedNbr_inter_eq_singleton hcnt0 hmI hc0 x hx).mp hclose⟩
  have hpriv1 : ∀ s ∈ Sset,
      (lookupPort1 ports s = s ∨ (strongPow C7 d).Adj (lookupPort1 ports s) s) ∧
      ∀ x ∈ tI.toFinset,
        (x = lookupPort1 ports s ∨ (strongPow C7 d).Adj x (lookupPort1 ports s)) → x = s := by
    intro s hs
    rcases (hS_iff s).mp hs with ⟨p0, p1, hmem⟩
    have hf1 : lookupPort1 ports s = p1 := lookupPort1_of_mem hnd hmem
    rcases validPorts_spec hports hmem with ⟨hmI, _, _, hc1, _, hcnt1, _, _⟩
    rw [hf1]
    refine ⟨close_symm hc1, fun x hx hclose =>
      (Trie7.closedNbr_inter_eq_singleton hcnt1 hmI hc1 x hx).mp hclose⟩
  have hsubS : Sset ⊆ tI.toFinset := by
    intro s hs
    rcases (hS_iff s).mp hs with ⟨p0, p1, hmem⟩
    exact Trie7.mem_toFinset_iff_memBool.mpr (validPorts_spec hports hmem).1
  have hP0_sub : Sset.image (lookupPort0 ports) ⊆ tP0.toFinset := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨s, hs, rfl⟩
    rcases (hS_iff s).mp hs with ⟨p0, p1, hmem⟩
    rw [lookupPort0_of_mem hnd hmem]
    exact Trie7.mem_toFinset_iff_memBool.mpr (validPorts_spec hports hmem).2.2.2.2.2.2.1
  have hP1_sub : Sset.image (lookupPort1 ports) ⊆ tP1.toFinset := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨s, hs, rfl⟩
    rcases (hS_iff s).mp hs with ⟨p0, p1, hmem⟩
    rw [lookupPort1_of_mem hnd hmem]
    exact Trie7.mem_toFinset_iff_memBool.mpr (validPorts_spec hports hmem).2.2.2.2.2.2.2
  have hP0_eq : Sset.image (lookupPort0 ports) = tP0.toFinset := by
    refine Finset.eq_of_subset_of_card_le hP0_sub ?_
    have hinj : Set.InjOn (lookupPort0 ports) (Sset : Set (StrongPowV (ZMod 7) d)) := by
      intro s₁ hs₁ s₂ hs₂ heq
      have hc : s₁ = lookupPort0 ports s₂ ∨ (strongPow C7 d).Adj s₁ (lookupPort0 ports s₂) :=
        heq ▸ close_symm (hpriv0 s₁ hs₁).1
      exact (hpriv0 s₂ hs₂).2 s₁ (hsubS hs₁) hc
    rw [Finset.card_image_of_injOn hinj, Trie7.toFinset_card, hcardP0,
      List.toFinset_card_of_nodup hnd, List.length_map]
  have hP1_eq : Sset.image (lookupPort1 ports) = tP1.toFinset := by
    refine Finset.eq_of_subset_of_card_le hP1_sub ?_
    have hinj : Set.InjOn (lookupPort1 ports) (Sset : Set (StrongPowV (ZMod 7) d)) := by
      intro s₁ hs₁ s₂ hs₂ heq
      have hc : s₁ = lookupPort1 ports s₂ ∨ (strongPow C7 d).Adj s₁ (lookupPort1 ports s₂) :=
        heq ▸ close_symm (hpriv1 s₁ hs₁).1
      exact (hpriv1 s₂ hs₂).2 s₁ (hsubS hs₁) hc
    rw [Finset.card_image_of_injOn hinj, Trie7.toFinset_card, hcardP1,
      List.toFinset_card_of_nodup hnd, List.length_map]
  { I := tI.toFinset
    S := Sset
    f0 := lookupPort0 ports
    f1 := lookupPort1 ports
    X := tX.toFinset
    indep_I := Trie7.to_indepSet_of_isIndep hI
    sub_S := hsubS
    self_mem := by
      intro s hs
      rcases (hS_iff s).mp hs with ⟨p0, p1, hmem⟩
      rw [lookupPort0_of_mem hnd hmem, lookupPort1_of_mem hnd hmem]
      exact (validPorts_spec hports hmem).2.1
    priv0 := hpriv0
    priv1 := hpriv1
    indep_P0 := by
      rw [← Finset.coe_image, hP0_eq]
      exact Trie7.to_indepSet_of_isIndep hP0
    indep_P1 := by
      rw [← Finset.coe_image, hP1_eq]
      exact Trie7.to_indepSet_of_isIndep hP1
    indep_X := Trie7.to_indepSet_of_isIndep hX
    disj_nbr := by
      intro w hw ⟨⟨s₀, hs₀, hc₀⟩, ⟨s₁, hs₁, hc₁⟩⟩
      exact Trie7.disjointCommonNbr_sound hdisj w hw
        ⟨⟨lookupPort0 ports s₀, hP0_eq ▸ Finset.mem_image_of_mem _ hs₀, close_symm hc₀⟩,
         ⟨lookupPort1 ports s₁, hP1_eq ▸ Finset.mem_image_of_mem _ hs₁, close_symm hc₁⟩⟩ }

/-- Exact equality `τ.P0 = tP0.toFinset` for a `ValidTuple` constructed by `ValidTuple.ofTrie7`. -/
theorem ValidTuple.ofTrie7_P0_eq {d : ℕ}
    {tI tP0 tP1 tX : Trie7 d}
    {ports : List (PortEntry d)}
    {hI : tI.isIndep = true}
    {hP0 : tP0.isIndep = true}
    {hP1 : tP1.isIndep = true}
    {hX : tX.isIndep = true}
    {hnodup : portsNodupBool ports = true}
    {hports : validPortsBool tI tP0 tP1 ports = true}
    {hcardP0 : tP0.card = ports.length}
    {hcardP1 : tP1.card = ports.length}
    {hdisj : Trie7.disjointCommonNbr tP0 tP1 tX = true} :
    (ValidTuple.ofTrie7 tI tP0 tP1 tX ports hI hP0 hP1 hX hnodup hports
      hcardP0 hcardP1 hdisj).P0 = tP0.toFinset := by
  classical
  let τ := ValidTuple.ofTrie7 tI tP0 tP1 tX ports hI hP0 hP1 hX hnodup hports
    hcardP0 hcardP1 hdisj
  have hnd : (ports.map Prod.fst).Nodup := portsNodup_of_bool hnodup
  have hS_iff : ∀ s, s ∈ τ.S ↔ ∃ p0 p1, (s, p0, p1) ∈ ports := by
    intro s
    simp only [τ, ValidTuple.ofTrie7, List.mem_toFinset, List.mem_map, Prod.exists]
    constructor
    · rintro ⟨a, b, c, hmem, rfl⟩; exact ⟨b, c, hmem⟩
    · rintro ⟨p0, p1, hmem⟩; exact ⟨s, p0, p1, hmem, rfl⟩
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    rcases ValidTuple.mem_P0.mp hx with ⟨s, hs, rfl⟩
    rcases (hS_iff s).mp hs with ⟨p0, p1, hmem⟩
    change lookupPort0 ports s ∈ tP0.toFinset
    rw [lookupPort0_of_mem hnd hmem]
    exact Trie7.mem_toFinset_iff_memBool.mpr (validPorts_spec hports hmem).2.2.2.2.2.2.1
  · rw [τ.card_P0, Trie7.toFinset_card, hcardP0]
    change ports.length ≤ (ports.map Prod.fst).toFinset.card
    rw [List.toFinset_card_of_nodup hnd, List.length_map]

/-- Exact equality `τ.P1 = tP1.toFinset` for a `ValidTuple` constructed by `ValidTuple.ofTrie7`. -/
theorem ValidTuple.ofTrie7_P1_eq {d : ℕ}
    {tI tP0 tP1 tX : Trie7 d}
    {ports : List (PortEntry d)}
    {hI : tI.isIndep = true}
    {hP0 : tP0.isIndep = true}
    {hP1 : tP1.isIndep = true}
    {hX : tX.isIndep = true}
    {hnodup : portsNodupBool ports = true}
    {hports : validPortsBool tI tP0 tP1 ports = true}
    {hcardP0 : tP0.card = ports.length}
    {hcardP1 : tP1.card = ports.length}
    {hdisj : Trie7.disjointCommonNbr tP0 tP1 tX = true} :
    (ValidTuple.ofTrie7 tI tP0 tP1 tX ports hI hP0 hP1 hX hnodup hports
      hcardP0 hcardP1 hdisj).P1 = tP1.toFinset := by
  classical
  let τ := ValidTuple.ofTrie7 tI tP0 tP1 tX ports hI hP0 hP1 hX hnodup hports
    hcardP0 hcardP1 hdisj
  have hnd : (ports.map Prod.fst).Nodup := portsNodup_of_bool hnodup
  have hS_iff : ∀ s, s ∈ τ.S ↔ ∃ p0 p1, (s, p0, p1) ∈ ports := by
    intro s
    simp only [τ, ValidTuple.ofTrie7, List.mem_toFinset, List.mem_map, Prod.exists]
    constructor
    · rintro ⟨a, b, c, hmem, rfl⟩; exact ⟨b, c, hmem⟩
    · rintro ⟨p0, p1, hmem⟩; exact ⟨s, p0, p1, hmem, rfl⟩
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    rcases ValidTuple.mem_P1.mp hx with ⟨s, hs, rfl⟩
    rcases (hS_iff s).mp hs with ⟨p0, p1, hmem⟩
    change lookupPort1 ports s ∈ tP1.toFinset
    rw [lookupPort1_of_mem hnd hmem]
    exact Trie7.mem_toFinset_iff_memBool.mpr (validPorts_spec hports hmem).2.2.2.2.2.2.2
  · rw [τ.card_P1, Trie7.toFinset_card, hcardP1]
    change ports.length ≤ (ports.map Prod.fst).toFinset.card
    rw [List.toFinset_card_of_nodup hnd, List.length_map]

/-- Exact computable profile identity for `ValidTuple.ofTrie7` (all trie/proof args implicit!). -/
theorem ValidTuple.ofTrie7_profile_eq {d : ℕ}
    {tI tP0 tP1 tX : Trie7 d}
    {ports : List (PortEntry d)}
    {hI : tI.isIndep = true}
    {hP0 : tP0.isIndep = true}
    {hP1 : tP1.isIndep = true}
    {hX : tX.isIndep = true}
    {hnodup : portsNodupBool ports = true}
    {hports : validPortsBool tI tP0 tP1 ports = true}
    {hcardP0 : tP0.card = ports.length}
    {hcardP1 : tP1.card = ports.length}
    {hdisj : Trie7.disjointCommonNbr tP0 tP1 tX = true}
    {p : Profile}
    (ha : tI.card = p.a) (hb : ports.length = p.b)
    (hc : tX.card = p.c) (hd : Trie7.countOutside tP0 tP1 tX = p.d) :
    (ValidTuple.ofTrie7 tI tP0 tP1 tX ports hI hP0 hP1 hX hnodup hports
      hcardP0 hcardP1 hdisj).profile = p := by
  classical
  let τ := ValidTuple.ofTrie7 tI tP0 tP1 tX ports hI hP0 hP1 hX hnodup hports
    hcardP0 hcardP1 hdisj
  have hnd : (ports.map Prod.fst).Nodup := portsNodup_of_bool hnodup
  have hS_iff : ∀ s, s ∈ τ.S ↔ ∃ p0 p1, (s, p0, p1) ∈ ports := by
    intro s
    simp only [τ, ValidTuple.ofTrie7, List.mem_toFinset, List.mem_map, Prod.exists]
    constructor
    · rintro ⟨a, b, c, hmem, rfl⟩; exact ⟨b, c, hmem⟩
    · rintro ⟨p0, p1, hmem⟩; exact ⟨s, p0, p1, hmem, rfl⟩
  have hP0_eq : τ.P0 = tP0.toFinset := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      rcases ValidTuple.mem_P0.mp hx with ⟨s, hs, rfl⟩
      rcases (hS_iff s).mp hs with ⟨p0, p1, hmem⟩
      change lookupPort0 ports s ∈ tP0.toFinset
      rw [lookupPort0_of_mem hnd hmem]
      exact Trie7.mem_toFinset_iff_memBool.mpr (validPorts_spec hports hmem).2.2.2.2.2.2.1
    · rw [τ.card_P0, Trie7.toFinset_card, hcardP0]
      change ports.length ≤ (ports.map Prod.fst).toFinset.card
      rw [List.toFinset_card_of_nodup hnd, List.length_map]
  have hP1_eq : τ.P1 = tP1.toFinset := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      rcases ValidTuple.mem_P1.mp hx with ⟨s, hs, rfl⟩
      rcases (hS_iff s).mp hs with ⟨p0, p1, hmem⟩
      change lookupPort1 ports s ∈ tP1.toFinset
      rw [lookupPort1_of_mem hnd hmem]
      exact Trie7.mem_toFinset_iff_memBool.mpr (validPorts_spec hports hmem).2.2.2.2.2.2.2
    · rw [τ.card_P1, Trie7.toFinset_card, hcardP1]
      change ports.length ≤ (ports.map Prod.fst).toFinset.card
      rw [List.toFinset_card_of_nodup hnd, List.length_map]
  apply Profile.ext
  · change tI.toFinset.card = p.a
    rw [Trie7.toFinset_card, ha]
  · change (ports.map Prod.fst).toFinset.card = p.b
    rw [List.toFinset_card_of_nodup hnd, List.length_map, hb]
  · change tX.toFinset.card = p.c
    rw [Trie7.toFinset_card, hc]
  · change τ.O.card = p.d
    rw [← hd, Trie7.countOutside_eq]
    congr 1
    ext w
    simp only [ValidTuple.mem_O, Finset.mem_filter]
    refine and_congr Iff.rfl (and_congr ?_ ?_)
    · refine not_congr ⟨?_, ?_⟩
      · rintro ⟨s, hs, hc0⟩
        exact ⟨τ.f0 s, hP0_eq ▸ ValidTuple.mem_P0.mpr ⟨s, hs, rfl⟩, close_symm hc0⟩
      · rintro ⟨u, hu, hc0⟩
        rcases ValidTuple.mem_P0.mp (hP0_eq.symm ▸ hu) with ⟨s, hs, rfl⟩
        exact ⟨s, hs, close_symm hc0⟩
    · refine not_congr ⟨?_, ?_⟩
      · rintro ⟨s, hs, hc1⟩
        exact ⟨τ.f1 s, hP1_eq ▸ ValidTuple.mem_P1.mpr ⟨s, hs, rfl⟩, close_symm hc1⟩
      · rintro ⟨v, hv, hc1⟩
        rcases ValidTuple.mem_P1.mp (hP1_eq.symm ▸ hv) with ⟨s, hs, rfl⟩
        exact ⟨s, hs, close_symm hc1⟩

/-! ## Arithmetic Profile Benchmarks (`d = 10, 200, 210`) -/

def gaoBaseProfile : Profile := ⟨367, 8, 367, 321, by decide, by decide⟩
def bpzBaseProfile : Profile := ⟨367, 8, 367, 322, by decide, by decide⟩

theorem itty_d10_card : (splitTree2.evalProfile gaoBaseProfile).a = 134753 := rfl

theorem itty_d10_decimal :
    3258020737293 ^ 10 ≤ 1000000000000 ^ 10 * (splitTree2.evalProfile gaoBaseProfile).a :=
  nat_pow_le_of_ble rfl

theorem gao_d200_card :
    (splitTree40.evalProfile gaoBaseProfile).a =
      4085567963379990282748597333793399773399910167372462112610203714626938509773125898252337545387866277249 :=
  rfl

theorem gao_d200_decimal :
    3258789153908 ^ 200 ≤ 1000000000000 ^ 200 * (splitTree40.evalProfile gaoBaseProfile).a :=
  nat_pow_le_of_ble rfl

theorem bpz_v1_d200_decimal :
    3258805369885 ^ 200 ≤ 1000000000000 ^ 200 * (splitTree40.evalProfile bpzBaseProfile).a :=
  nat_pow_le_of_ble rfl

def d323BaseProfile : Profile := ⟨367, 8, 367, 323, by decide, by decide⟩
def d324BaseProfile : Profile := ⟨367, 8, 367, 324, by decide, by decide⟩

theorem d323_d210_decimal :
    3258822207584 ^ 210 ≤ 1000000000000 ^ 210 * (splitTree42.evalProfile d323BaseProfile).a :=
  nat_pow_le_of_ble rfl

theorem d324_d210_decimal :
    3258839677706 ^ 210 ≤ 1000000000000 ^ 210 * (splitTree42.evalProfile d324BaseProfile).a :=
  nat_pow_le_of_ble rfl

theorem itty_d10_bpz_card : (splitTree2.evalProfile bpzBaseProfile).a = 134753 := rfl

theorem itty_d10_bpz_decimal :
    3258020737293 ^ 10 ≤ 1000000000000 ^ 10 * (splitTree2.evalProfile bpzBaseProfile).a :=
  nat_pow_le_of_ble rfl

theorem bpz_v1_d200_15_decimal :
    3258805369885465 ^ 200 ≤
      1000000000000000 ^ 200 * (splitTree40.evalProfile bpzBaseProfile).a :=
  nat_pow_le_of_ble rfl

/-! ## Concrete 5D Base `ValidTuple` (`X_322`, `bip = 1`) & Certified 2026 Lower Bounds -/

/-- Explicit 8-port list `(r_j, f0 r_j, f1 r_j)` on unique zero-hit bipartition `bip = 1`
(`J_0 = {0, 1, 6}`, `J_1 = {2, 3, 4, 5, 7}`) for `polakSchrijver367Trie`. -/
def basePorts : List (PortEntry 5) :=
  [ ((0, 3, 5, 6, 5, PUnit.unit), (6, 3, 5, 0, 5, PUnit.unit), (0, 3, 5, 6, 5, PUnit.unit)),
    ((1, 3, 4, 4, 6, PUnit.unit), (2, 3, 5, 4, 6, PUnit.unit), (1, 3, 4, 4, 6, PUnit.unit)),
    ((3, 4, 0, 3, 5, PUnit.unit), (3, 4, 0, 3, 5, PUnit.unit), (2, 4, 6, 3, 5, PUnit.unit)),
    ((4, 4, 6, 1, 6, PUnit.unit), (4, 4, 6, 1, 6, PUnit.unit), (5, 4, 6, 0, 6, PUnit.unit)),
    ((5, 3, 1, 3, 4, PUnit.unit), (5, 3, 1, 3, 4, PUnit.unit), (5, 3, 2, 3, 5, PUnit.unit)),
    ((6, 0, 6, 4, 5, PUnit.unit), (6, 0, 6, 4, 5, PUnit.unit), (6, 1, 6, 5, 5, PUnit.unit)),
    ((6, 4, 3, 4, 0, PUnit.unit), (6, 4, 2, 4, 6, PUnit.unit), (6, 4, 3, 4, 0, PUnit.unit)),
    ((6, 4, 5, 3, 2, PUnit.unit), (6, 4, 5, 3, 2, PUnit.unit), (6, 5, 5, 3, 1, PUnit.unit)) ]

/-- First private transversal `P0 = f0(S)` (`8` words) on `bip = 1`. -/
def baseP0 : Trie7 5 :=
  .node
    .empty .empty
    (.node
      .empty .empty .empty
      (.node
        .empty .empty .empty .empty .empty
        (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty)
        .empty)
      .empty .empty .empty)
    (.node
      .empty .empty .empty .empty
      (.node
        (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty)
        .empty .empty .empty .empty .empty .empty)
      .empty .empty)
    (.node
      .empty .empty .empty .empty
      (.node
        .empty .empty .empty .empty .empty .empty
        (.node .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty))
      .empty .empty)
    (.node
      .empty .empty .empty
      (.node
        .empty
        (.node .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty)
        .empty .empty .empty .empty .empty)
      .empty .empty .empty)
    (.node
      (.node
        .empty .empty .empty .empty .empty .empty
        (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty))
      .empty .empty
      (.node
        .empty .empty .empty .empty .empty
        (.node (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty .empty)
        .empty)
      (.node
        .empty .empty
        (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty)
        .empty .empty
        (.node .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty)
        .empty)
      .empty .empty)

/-- Second private transversal `P1 = f1(S)` (`8` words) on `bip = 1`. -/
def baseP1 : Trie7 5 :=
  .node
    (.node
      .empty .empty .empty
      (.node
        .empty .empty .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty))
        .empty)
      .empty .empty .empty)
    (.node
      .empty .empty .empty
      (.node
        .empty .empty .empty .empty
        (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty)
        .empty .empty)
      .empty .empty .empty)
    (.node
      .empty .empty .empty .empty
      (.node
        .empty .empty .empty .empty .empty .empty
        (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty))
      .empty .empty)
    .empty .empty
    (.node
      .empty .empty .empty
      (.node
        .empty .empty
        (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty)
        .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty .empty .empty
        (.node (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty .empty))
      .empty .empty)
    (.node
      .empty
      (.node
        .empty .empty .empty .empty .empty .empty
        (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty))
      .empty .empty
      (.node
        .empty .empty .empty
        (.node .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty)
        .empty .empty .empty)
      (.node
        .empty .empty .empty .empty .empty
        (.node .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty)
        .empty)
      .empty)

/-- Coordinate-0 slice `0` (55 words) of verified BPZ v1 auxiliary witness `X_322` (`bip = 1`). -/
def baseXSlice0 : Trie7 4 :=
  .node
    (.node
      (.node
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .empty .leaf))
      .empty (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty))
    (.node
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty))
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty .empty) .empty)
    (.node
      (.node
        .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty)
      (.node
        .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty) .empty
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty))
    (.node
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty) .empty
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node
        .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)))
    (.node
      .empty
      (.node
        (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .leaf .empty .leaf) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)))
    (.node
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)) .empty
      (.node
        (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty))
    (.node
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty))
      .empty
      (.node
        (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty))

/-- Coordinate-0 slice `1` (52 words) of verified BPZ v1 auxiliary witness `X_322` (`bip = 1`). -/
def baseXSlice1 : Trie7 4 :=
  .node
    (.node
      (.node
        .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)) .empty
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty))
    (.node
      (.node .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)) .empty
      (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty)
      (.node
        .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty))
    (.node
      .empty
      (.node
        (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty)
      .empty
      (.node
        .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)))
    (.node
      .empty (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)) .empty
      (.node
        (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty))
    (.node
      (.node .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty))
      .empty (.node (.node .empty .empty .empty .empty .leaf .empty .leaf) .empty .empty .empty .empty .empty .empty)
      .empty (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty))
    (.node
      (.node
        .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty)
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty) .empty
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .empty .leaf) .empty)
      (.node
        .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty))
    (.node
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty) .empty
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node
        .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty)) .empty)

/-- Coordinate-0 slice `2` (53 words) of verified BPZ v1 auxiliary witness `X_322` (`bip = 1`). -/
def baseXSlice2 : Trie7 4 :=
  .node
    (.node
      (.node .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty))
      .empty
      (.node
        (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty))
    (.node
      .empty (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .empty .leaf)))
    (.node
      (.node .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty))
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .empty .leaf))
      .empty (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty))
    (.node
      (.node
        .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty) .empty
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty))
    (.node
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)) .empty
      (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty)
      (.node .empty .empty (.node .leaf .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty))
    (.node
      (.node
        (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node
        .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)) .empty)
    (.node
      (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)) .empty
      (.node
        (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty))

/-- Coordinate-0 slice `3` (52 words) of verified BPZ v1 auxiliary witness `X_322` (`bip = 1`). -/
def baseXSlice3 : Trie7 4 :=
  .node
    (.node
      .empty (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node
        .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty)
      (.node
        .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty)
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty))
    (.node
      (.node
        .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)) .empty
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty) .empty
      (.node .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty))
    (.node
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)) .empty
      (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty)
      (.node
        .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty)
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty))
    (.node
      (.node (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty) .empty
      (.node
        .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)) .empty)
    (.node
      (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty) .empty
      (.node
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty))
      .empty)
    (.node
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty))
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .empty .leaf))
      .empty (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty))
    (.node
      (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty)
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty) .empty
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty)))

/-- Coordinate-0 slice `4` (55 words) of verified BPZ v1 auxiliary witness `X_322` (`bip = 1`). -/
def baseXSlice4 : Trie7 4 :=
  .node
    (.node
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)) .empty
      (.node
        (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node
        .empty (.node .empty .empty .empty .empty .empty .leaf .empty)
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty))
    (.node
      (.node .empty .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)) .empty
      (.node
        (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty))
    (.node
      (.node
        (.node .empty .empty .empty .empty .empty .leaf .empty)
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty))
      .empty)
    (.node
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .leaf .empty) .empty)
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .empty .leaf))
      .empty (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty))
    (.node
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)) .empty
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty))
    (.node
      .empty (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty)
      (.node
        .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)))
    (.node
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node
        .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)) .empty
      (.node (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty))

/-- Coordinate-0 slice `5` (50 words) of verified BPZ v1 auxiliary witness `X_322` (`bip = 1`). -/
def baseXSlice5 : Trie7 4 :=
  .node
    (.node
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty) .empty
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty))
      .empty)
    (.node
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node
        .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty)
      (.node
        .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty)
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty) .empty)
    (.node
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)) .empty
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty) .empty
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty))
    (.node
      .empty (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      .empty
      (.node
        .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)))
    (.node
      .empty
      (.node
        (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty) .empty
      (.node .empty .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)))
    (.node
      (.node
        .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      .empty
      (.node
        .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      .empty
      (.node
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty))
      .empty (.node .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty))
    (.node
      (.node
        .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty))
      .empty
      (.node
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .empty .leaf))
      .empty (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty) .empty)

/-- Coordinate-0 slice `6` (50 words) of verified BPZ v1 auxiliary witness `X_322` (`bip = 1`). -/
def baseXSlice6 : Trie7 4 :=
  .node
    (.node
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)) .empty
      (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty) .empty
      (.node
        .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty))
    (.node
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)) .empty
      (.node
        (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty)
      .empty
      (.node
        .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty))
    (.node
      (.node
        (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty)
      .empty (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)) .empty)
    (.node
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty))
      .empty (.node .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty)
      .empty)
    (.node
      (.node
        .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty)
      (.node
        .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty))
      .empty (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      .empty (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty))
    (.node
      .empty (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      .empty (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node
        .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)))
    (.node
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty)
      (.node
        .empty (.node .leaf .empty .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)) .empty
      (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty))

/-- Verified 367-word BPZ v1 auxiliary witness `X_322` (`693` internal nodes, `|O| = 322`, `h = 19`, `v = 26`). -/
def baseX : Trie7 5 :=
  .node baseXSlice0 baseXSlice1 baseXSlice2 baseXSlice3 baseXSlice4 baseXSlice5 baseXSlice6

private theorem baseXSlice0_isIndep : baseXSlice0.isIndep = true := rfl
private theorem baseXSlice1_isIndep : baseXSlice1.isIndep = true := rfl
private theorem baseXSlice2_isIndep : baseXSlice2.isIndep = true := rfl
private theorem baseXSlice3_isIndep : baseXSlice3.isIndep = true := rfl
private theorem baseXSlice4_isIndep : baseXSlice4.isIndep = true := rfl
private theorem baseXSlice5_isIndep : baseXSlice5.isIndep = true := rfl
private theorem baseXSlice6_isIndep : baseXSlice6.isIndep = true := rfl

private theorem baseX_disj01 : baseXSlice0.disjoint baseXSlice1 = true := rfl
private theorem baseX_disj12 : baseXSlice1.disjoint baseXSlice2 = true := rfl
private theorem baseX_disj23 : baseXSlice2.disjoint baseXSlice3 = true := rfl
private theorem baseX_disj34 : baseXSlice3.disjoint baseXSlice4 = true := rfl
private theorem baseX_disj45 : baseXSlice4.disjoint baseXSlice5 = true := rfl
private theorem baseX_disj56 : baseXSlice5.disjoint baseXSlice6 = true := rfl
private theorem baseX_disj60 : baseXSlice6.disjoint baseXSlice0 = true := rfl

/-- Pure-kernel slice-by-slice independence proof for the 367-word BPZ v1 auxiliary trie `baseX`. -/
theorem baseX_isIndep : baseX.isIndep = true :=
  Trie7.isIndep_node
    baseXSlice0_isIndep baseXSlice1_isIndep baseXSlice2_isIndep baseXSlice3_isIndep
    baseXSlice4_isIndep baseXSlice5_isIndep baseXSlice6_isIndep
    baseX_disj01 baseX_disj12 baseX_disj23 baseX_disj34
    baseX_disj45 baseX_disj56 baseX_disj60

/-- Factored pure-kernel certificate: `baseP0` is independent in `C7^⊠5`. -/
theorem baseP0_isIndep : baseP0.isIndep = true := rfl

/-- Factored pure-kernel certificate: `baseP1` is independent in `C7^⊠5`. -/
theorem baseP1_isIndep : baseP1.isIndep = true := rfl

/-- Factored pure-kernel certificate: the 8 port centers in `basePorts` are pairwise distinct. -/
theorem base_nodup : portsNodupBool basePorts = true := rfl

/-- Factored pure-kernel certificate: all 8 ports satisfy privacy, self-membership, and containment. -/
theorem base_ports : validPortsBool polakSchrijver367Trie baseP0 baseP1 basePorts = true := rfl

/-- Factored pure-kernel certificate: `baseP0.card = 8 = basePorts.length`. -/
theorem base_cardP0 : baseP0.card = basePorts.length := rfl

/-- Factored pure-kernel certificate: `baseP1.card = 8 = basePorts.length`. -/
theorem base_cardP1 : baseP1.card = basePorts.length := rfl

/-- Factored pure-kernel certificate: `baseX` avoids `N[baseP0] ∩ N[baseP1]`. -/
theorem base_disj : Trie7.disjointCommonNbr baseP0 baseP1 baseX = true := rfl

/-- Factored pure-kernel certificate: `baseX.card = 367`. -/
theorem baseX_card : baseX.card = 367 := rfl

/-- Factored pure-kernel certificate: `|O| = |baseX \ (N[baseP0] ∪ N[baseP1])| = 322`. -/
theorem base_countOutside : Trie7.countOutside baseP0 baseP1 baseX = 322 := rfl

/-- Concrete 5D base `ValidTuple` on `strongPow C7 5` with exact BPZ v1 profile `(367, 8, 367, 322)`
verified in the pure Lean 4 kernel (zero `native_decide`). -/
def baseTuple5D : ValidTuple (strongPow C7 5) :=
  ValidTuple.ofTrie7 polakSchrijver367Trie baseP0 baseP1 baseX basePorts
    polakSchrijver367Trie_isIndep baseP0_isIndep baseP1_isIndep baseX_isIndep
    base_nodup base_ports base_cardP0 base_cardP1 base_disj

/-- Exact profile of `baseTuple5D`: `(367, 8, 367, 322)`. -/
theorem baseTuple5D_profile : baseTuple5D.profile = bpzBaseProfile :=
  ValidTuple.ofTrie7_profile_eq polakSchrijver367Trie_card rfl baseX_card base_countOutside

/-- Exact `P0` finset equality for `baseTuple5D`. -/
theorem baseTuple5D_P0_eq : baseTuple5D.P0 = baseP0.toFinset :=
  ValidTuple.ofTrie7_P0_eq

/-- Exact `P1` finset equality for `baseTuple5D`. -/
theorem baseTuple5D_P1_eq : baseTuple5D.P1 = baseP1.toFinset :=
  ValidTuple.ofTrie7_P1_eq

/-- Certified Itty et al. (2026) 10th-power independence-number lower bound: `α(C7^⊠10) ≥ 134,753`. -/
theorem alpha_c7_pow10_ge_134753 :
    134753 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 10).indepNum := by
  have h := baseTuple5D.evalTree_a_le_cycleGraph7_indepNum splitTree2
  rw [baseTuple5D_profile, itty_d10_bpz_card] at h
  exact h

/-- Certified Itty et al. (2026) Shannon capacity lower bound: `3.258020737293 ≤ Θ(C7)`. -/
theorem c7_lower_itty :
    (3258020737293 : ℝ) / 1000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  ValidTuple.le_shannonCapacity_cycleGraph7_of_evalTree_profile
    (by decide) (by decide) baseTuple5D_profile splitTree2 itty_d10_bpz_decimal

/-- Certified BPZ v1 (2026) 12-decimal Shannon capacity lower bound: `3.258805369885 ≤ Θ(C7)`. -/
theorem c7_lower_bpz_v1 :
    (3258805369885 : ℝ) / 1000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  ValidTuple.le_shannonCapacity_cycleGraph7_of_evalTree_profile
    (by decide) (by decide) baseTuple5D_profile splitTree40 bpz_v1_d200_decimal

/-- Certified Gao (2026) 12-decimal Shannon capacity lower bound: `3.258789153908 ≤ Θ(C7)`. -/
theorem c7_lower_gao :
    (3258789153908 : ℝ) / 1000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  le_trans (by norm_num) c7_lower_bpz_v1

/-- Certified BPZ v1 (2026) sharpest 15-decimal Shannon capacity lower bound:
`3.258805369885465 ≤ Θ(C7)`. -/
theorem c7_lower_bpz_v1_15 :
    (3258805369885465 : ℝ) / 1000000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  ValidTuple.le_shannonCapacity_cycleGraph7_of_evalTree_profile
    (by decide) (by decide) baseTuple5D_profile splitTree40 bpz_v1_d200_15_decimal

end ShannonC7
