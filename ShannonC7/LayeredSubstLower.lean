import ShannonC7.HeteroLayered
import Mathlib.Algebra.BigOperators.Fin

/-!
# Pure-Kernel Layered Substitutions, 7-Letter Separation System & Heterogeneous Gao (`HetGao`)

This module formalizes the pure-kernel multi-layer substitution machinery of
Buys–Polak–Zuiddam (`Realisation`, `Subst`, `Code`, `multiSubst`, `Letter`, `Letter.sep`,
`Letter.sigma`) together with Tandon's heterogeneous product (`HetGao`, Theorem 1 of
`arXiv:2608.30273`) over `strongPowPi`, with zero `sorry`, `native_decide`, or `partial`.
-/

namespace ShannonC7

open SimpleGraph

section LayeredCore

/-- Two vertex finsets are separated in `G` when no vertex of one conflicts with one of the other. -/
def Sep {V : Type*} (G : SimpleGraph V) (P Q : Finset V) : Prop :=
  ∀ x ∈ P, ∀ y ∈ Q, ¬ (x = y ∨ G.Adj x y)

theorem Sep.symm {V : Type*} {G : SimpleGraph V} {P Q : Finset V} (h : Sep G P Q) :
    Sep G Q P :=
  fun y hy x hx hc => h x hx y hy (hc.imp Eq.symm SimpleGraph.Adj.symm)

theorem Sep.disjoint {V : Type*} [DecidableEq V] {G : SimpleGraph V} {P Q : Finset V}
    (h : Sep G P Q) : Disjoint P Q := by
  rw [Finset.disjoint_left]
  intro x hxP hxQ
  exact h x hxP x hxQ (Or.inl rfl)

theorem Sep.mono_left {V : Type*} {G : SimpleGraph V} {P' P Q : Finset V}
    (hsub : P' ⊆ P) (h : Sep G P Q) : Sep G P' Q :=
  fun x hx y hy => h x (hsub hx) y hy

theorem Sep.mono_right {V : Type*} {G : SimpleGraph V} {P Q' Q : Finset V}
    (hsub : Q' ⊆ Q) (h : Sep G P Q) : Sep G P Q' :=
  fun x hx y hy => h x hx y (hsub hy)

theorem Sep.union_left {V : Type*} [DecidableEq V] {G : SimpleGraph V} {P₁ P₂ Q : Finset V}
    (h1 : Sep G P₁ Q) (h2 : Sep G P₂ Q) : Sep G (P₁ ∪ P₂) Q := by
  intro x hx y hy
  rcases Finset.mem_union.mp hx with hx | hx
  · exact h1 x hx y hy
  · exact h2 x hx y hy

theorem Sep.union_right {V : Type*} [DecidableEq V] {G : SimpleGraph V} {P Q₁ Q₂ : Finset V}
    (h1 : Sep G P Q₁) (h2 : Sep G P Q₂) : Sep G P (Q₁ ∪ Q₂) := by
  intro x hx y hy
  rcases Finset.mem_union.mp hy with hy | hy
  · exact h1 x hx y hy
  · exact h2 x hx y hy

theorem isIndepSet_union_of_sep {V : Type*} [DecidableEq V] {G : SimpleGraph V} {P Q : Finset V}
    (hP : G.IsIndepSet (P : Set V)) (hQ : G.IsIndepSet (Q : Set V)) (hPQ : Sep G P Q) :
    G.IsIndepSet ((P ∪ Q : Finset V) : Set V) := by
  intro x hx y hy hne hadj
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hP hx hy hne hadj
  · exact hPQ x hx y hy (Or.inr hadj)
  · exact hPQ y hy x hx (Or.inr hadj.symm)
  · exact hQ hx hy hne hadj

/-- A realisation of a finite separation system `(A, sep)` by vertex finsets in `G`. -/
structure Realisation (A : Type*) [Fintype A] (sep : A → A → Bool)
    {V : Type*} (G : SimpleGraph V) where
  P : A → Finset V
  hindep : ∀ a, G.IsIndepSet (P a : Set V)
  hsep : ∀ a b, sep a b = true → Sep G (P a) (P b)

/-- The cardinality weight of letter `a` in a realisation `R`. -/
def Realisation.w {A : Type*} [Fintype A] {sep : A → A → Bool}
    {V : Type*} {G : SimpleGraph V} (R : Realisation A sep G) (a : A) : ℕ :=
  (R.P a).card

/-- Reindex a realisation along a `sep`-preserving permutation of the alphabet. -/
def Realisation.reindex {A : Type*} [Fintype A] {sep : A → A → Bool}
    {V : Type*} {G : SimpleGraph V} (R : Realisation A sep G) (e : A ≃ A)
    (he : ∀ a b, sep a b = sep (e a) (e b)) : Realisation A sep G where
  P a := R.P (e a)
  hindep a := R.hindep (e a)
  hsep a b hab := R.hsep (e a) (e b) (by rw [← he a b]; exact hab)

@[simp]
theorem Realisation.w_reindex {A : Type*} [Fintype A] {sep : A → A → Bool}
    {V : Type*} {G : SimpleGraph V} (R : Realisation A sep G) (e : A ≃ A)
    (he : ∀ a b, sep a b = sep (e a) (e b)) (a : A) :
    (R.reindex e he).w a = R.w (e a) := rfl

/-- Transport a realisation forward along a graph isomorphism. -/
def Realisation.mapIso {A : Type*} [Fintype A] {sep : A → A → Bool}
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (R : Realisation A sep G) (f : G ≃g H) :
    Realisation A sep H where
  P a := (R.P a).map f.toEquiv.toEmbedding
  hindep a := isIndepSet_map_iso f (R.hindep a)
  hsep a b hab x hx y hy hc := by
    simp only [Finset.mem_map, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    apply R.hsep a b hab x' hx' y' hy'
    rcases hc with heq | hadj
    · exact Or.inl (f.injective heq)
    · exact Or.inr (f.map_rel_iff.mp hadj)

@[simp]
theorem Realisation.w_mapIso {A : Type*} [Fintype A] {sep : A → A → Bool}
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (R : Realisation A sep G) (f : G ≃g H) (a : A) :
    (R.mapIso f).w a = R.w a :=
  Finset.card_map _

end LayeredCore

section StrongProdHelpers

theorem isIndepSet_strongProd {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {A : Finset V₁} {B : Finset V₂}
    (hA : G₁.IsIndepSet (A : Set V₁)) (hB : G₂.IsIndepSet (B : Set V₂)) :
    (G₁ ⊠ G₂).IsIndepSet ((A ×ˢ B : Finset (V₁ × V₂)) : Set (V₁ × V₂)) := by
  rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ hne ⟨_, hG1, hG2⟩
  simp only [Finset.mem_coe, Finset.mem_product] at h₁ h₂
  rcases hG1 with rfl | hG1adj
  · have hb : b₁ ≠ b₂ := fun h => hne (by rw [h])
    rcases hG2 with rfl | hG2adj
    · exact hb rfl
    · exact hB h₁.2 h₂.2 hb hG2adj
  · exact hA h₁.1 h₂.1 hG1adj.ne hG1adj

theorem sep_prod_left {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {A₁ A₂ : Finset V₁} {B₁ B₂ : Finset V₂} (hA : Sep G₁ A₁ A₂) :
    Sep (G₁ ⊠ G₂) (A₁ ×ˢ B₁) (A₂ ×ˢ B₂) := by
  rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ hc
  simp only [Finset.mem_product] at h₁ h₂
  rcases hc with heq | ⟨_, hG1, _⟩
  · exact hA a₁ h₁.1 a₂ h₂.1 (Or.inl (congrArg Prod.fst heq))
  · exact hA a₁ h₁.1 a₂ h₂.1 hG1

theorem sep_prod_right {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {A₁ A₂ : Finset V₁} {B₁ B₂ : Finset V₂} (hB : Sep G₂ B₁ B₂) :
    Sep (G₁ ⊠ G₂) (A₁ ×ˢ B₁) (A₂ ×ˢ B₂) := by
  rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ hc
  simp only [Finset.mem_product] at h₁ h₂
  rcases hc with heq | ⟨_, _, hG2⟩
  · exact hB b₁ h₁.2 b₂ h₂.2 (Or.inl (congrArg Prod.snd heq))
  · exact hB b₁ h₁.2 b₂ h₂.2 hG2

end StrongProdHelpers

section MultiSubst

/-- An admissible substitution of arity `q` over `(A, sep)`. -/
structure Subst (A : Type*) [Fintype A] (sep : A → A → Bool) (q : ℕ) where
  T : A → Finset (Fin q → A)
  hin : ∀ a, ∀ x ∈ T a, ∀ y ∈ T a, x ≠ y → ∃ i, sep (x i) (y i) = true
  hcross : ∀ a b, sep a b = true → ∀ x ∈ T a, ∀ y ∈ T b, ∃ i, sep (x i) (y i) = true

/-- A terminal code of arity `r` over `(A, sep)`. -/
structure Code (A : Type*) [Fintype A] (sep : A → A → Bool) (r : ℕ) where
  C : Finset (Fin r → A)
  hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ∃ i, sep (x i) (y i) = true

/-- Componentwise strong product of `strongPowPi G (e i)`. -/
def familyStrongPower {V : Type*} (G : SimpleGraph V) {q : ℕ} (e : Fin q → ℕ) :
    SimpleGraph ((i : Fin q) → Fin (e i) → V) where
  Adj f g := f ≠ g ∧ ∀ i, f i = g i ∨ (strongPowPi G (e i)).Adj (f i) (g i)
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, fun i => (h i).imp Eq.symm SimpleGraph.Adj.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- Reindex a tuple of summed length `∑ i, e i` as a dependent tuple of blocks. -/
def sumEquiv {q : ℕ} (e : Fin q → ℕ) (V : Type*) :
    (Fin (∑ i, e i) → V) ≃ ((i : Fin q) → Fin (e i) → V) :=
  (Equiv.piCongrLeft' (fun _ : Fin (∑ i, e i) => V) finSigmaFinEquiv.symm).trans
    (Equiv.piCurry fun _ _ => V)

@[simp]
theorem sumEquiv_apply {q : ℕ} (e : Fin q → ℕ) {V : Type*}
    (f : Fin (∑ i, e i) → V) (i : Fin q) (j : Fin (e i)) :
    sumEquiv e V f i j = f (finSigmaFinEquiv ⟨i, j⟩) := rfl

/-- Summed strong powers are isomorphic to componentwise strong powers. -/
def strongPower_sum_iso {V : Type*} (G : SimpleGraph V) {q : ℕ} (e : Fin q → ℕ) :
    strongPowPi G (∑ i, e i) ≃g familyStrongPower G e where
  toEquiv := sumEquiv e V
  map_rel_iff' := by
    intro f g
    show (_ ≠ _ ∧ ∀ i, _ = _ ∨ _) ↔ (f ≠ g ∧ ∀ k, _)
    constructor
    · rintro ⟨hne, h⟩
      refine ⟨fun hfg => hne (by rw [hfg]), fun k => ?_⟩
      let p := finSigmaFinEquiv.symm k
      have hk : finSigmaFinEquiv p = k := finSigmaFinEquiv.apply_symm_apply k
      rcases p with ⟨i, j⟩
      subst k
      rcases h i with he | ha
      · left; exact congrFun he j
      · exact ha.2 j
    · rintro ⟨hne, h⟩
      refine ⟨fun he => hne ((sumEquiv e V).injective he), fun i => ?_⟩
      by_cases he : sumEquiv e V f i = sumEquiv e V g i
      · exact Or.inl he
      · refine Or.inr ⟨he, fun j => ?_⟩
        simpa only [sumEquiv_apply] using h (finSigmaFinEquiv ⟨i, j⟩)

/-- Canonical isomorphism `(strongPowPi G dL ⊠ strongPowPi G dR) ≃g strongPowPi G (dL + dR)`. -/
def strongProdIsoAdd {V : Type*} (G : SimpleGraph V) (dL dR : ℕ) :
    (strongPowPi G dL ⊠ strongPowPi G dR) ≃g strongPowPi G (dL + dR) where
  toEquiv :=
    { toFun := fun p => Fin.append p.1 p.2
      invFun := fun f => (fun i => f (Fin.castAdd dR i), fun j => f (Fin.natAdd dL j))
      left_inv := fun _ => by
        ext i <;> simp [Fin.append_left, Fin.append_right]
      right_inv := fun f => by
        ext k
        refine Fin.addCases (fun i => by simp) (fun j => by simp) k }
  map_rel_iff' := by
    intro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩
    simp only [strongPowPi_adj, strongProd_adj, ne_eq]
    constructor
    · rintro ⟨hne, h⟩
      refine ⟨fun heq => hne (by cases heq; rfl), ?_, ?_⟩
      · by_cases hf : f₁ = f₂
        · exact Or.inl hf
        · exact Or.inr ⟨hf, fun i => by simpa using h (Fin.castAdd dR i)⟩
      · by_cases hg : g₁ = g₂
        · exact Or.inl hg
        · exact Or.inr ⟨hg, fun j => by simpa using h (Fin.natAdd dL j)⟩
    · rintro ⟨hne, hf, hg⟩
      refine ⟨fun heq => hne ?_, fun k => ?_⟩
      · ext i
        · simpa [Fin.append_left] using congrFun heq (Fin.castAdd dR i)
        · simpa [Fin.append_right] using congrFun heq (Fin.natAdd dL i)
      · refine Fin.addCases (motive := fun k => Fin.append f₁ g₁ k = Fin.append f₂ g₂ k ∨
            G.Adj (Fin.append f₁ g₁ k) (Fin.append f₂ g₂ k)) (fun i => ?_) (fun j => ?_) k
        · simp only [Fin.append_left]
          rcases hf with rfl | ⟨_, hfi⟩
          · exact Or.inl rfl
          · exact hfi i
        · simp only [Fin.append_right]
          rcases hg with rfl | ⟨_, hgj⟩
          · exact Or.inl rfl
          · exact hgj j

section MultiWord
variable {V : Type*} [Fintype V] [DecidableEq V]
  {A : Type*} [Fintype A] {sep : A → A → Bool} {G : SimpleGraph V}

def multiWordSet {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (strongPowPi G (e i)))
    (x : Fin q → A) : Finset ((i : Fin q) → Fin (e i) → V) :=
  Fintype.piFinset (fun i => (R i).P (x i))

omit [Fintype V] [DecidableEq V] in
theorem card_multiWordSet {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (strongPowPi G (e i)))
    (x : Fin q → A) :
    (multiWordSet e R x).card = ∏ i, (R i).w (x i) := by
  simp [multiWordSet, Fintype.card_piFinset, Realisation.w]

omit [Fintype V] [DecidableEq V] in
theorem isIndepSet_multiWordSet {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (strongPowPi G (e i)))
    (x : Fin q → A) :
    (familyStrongPower G e).IsIndepSet (multiWordSet e R x : Set ((i : Fin q) → Fin (e i) → V)) := by
  intro f hf g hg hne hadj
  simp only [Finset.mem_coe, multiWordSet, Fintype.mem_piFinset] at hf hg
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  rcases hadj.2 i with he | ha
  · exact hi he
  · exact (R i).hindep (x i) (hf i) (hg i) hi ha

omit [Fintype V] [DecidableEq V] in
theorem sep_multiWordSet {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (strongPowPi G (e i)))
    {x y : Fin q → A} (h : ∃ i, sep (x i) (y i) = true) :
    Sep (familyStrongPower G e) (multiWordSet e R x) (multiWordSet e R y) := by
  obtain ⟨i, hi⟩ := h
  intro f hf g hg hc
  simp only [multiWordSet, Fintype.mem_piFinset] at hf hg
  apply (R i).hsep _ _ hi (f i) (hf i) (g i) (hg i)
  rcases hc with he | ha
  · exact Or.inl (congrFun he i)
  · exact ha.2 i

def multiSubstSet {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (strongPowPi G (e i)))
    (S : Subst A sep q) (a : A) : Finset ((i : Fin q) → Fin (e i) → V) :=
  (S.T a).biUnion (multiWordSet e R)

omit [Fintype V] in
theorem card_multiSubstSet {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (strongPowPi G (e i)))
    (S : Subst A sep q) (a : A) :
    (multiSubstSet e R S a).card = ∑ x ∈ S.T a, ∏ i, (R i).w (x i) := by
  have hd : ∀ x ∈ S.T a, ∀ y ∈ S.T a, x ≠ y →
      Disjoint (multiWordSet e R x) (multiWordSet e R y) := by
    intro x hx y hy hne
    rw [Finset.disjoint_left]
    intro f hf hf'
    exact sep_multiWordSet e R (S.hin a x hx y hy hne) f hf f hf' (Or.inl rfl)
  rw [multiSubstSet, Finset.card_biUnion hd]
  exact Finset.sum_congr rfl fun x _ => card_multiWordSet e R x

def Realisation.multiSubstFamily {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (strongPowPi G (e i)))
    (S : Subst A sep q) : Realisation A sep (familyStrongPower G e) where
  P := multiSubstSet e R S
  hindep a f hf g hg hne hadj := by
    simp only [Finset.mem_coe, multiSubstSet, Finset.mem_biUnion] at hf hg
    obtain ⟨x, hx, hfx⟩ := hf
    obtain ⟨y, hy, hgy⟩ := hg
    by_cases hxy : x = y
    · subst hxy
      exact isIndepSet_multiWordSet e R x hfx hgy hne hadj
    · exact sep_multiWordSet e R (S.hin a x hx y hy hxy) f hfx g hgy (Or.inr hadj)
  hsep a b hab f hf g hg hc := by
    simp only [multiSubstSet, Finset.mem_biUnion] at hf hg
    obtain ⟨x, hx, hfx⟩ := hf
    obtain ⟨y, hy, hgy⟩ := hg
    exact sep_multiWordSet e R (S.hcross a b hab x hx y hy) f hfx g hgy hc

/-- Multilinear substitution across heterogeneous exponents `e : Fin q → ℕ`. -/
def Realisation.multiSubst {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (strongPowPi G (e i)))
    (S : Subst A sep q) : Realisation A sep (strongPowPi G (∑ i, e i)) :=
  (Realisation.multiSubstFamily e R S).mapIso (strongPower_sum_iso G e).symm

omit [Fintype V] in
@[simp]
theorem w_multiSubst {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (strongPowPi G (e i)))
    (S : Subst A sep q) (a : A) :
    (Realisation.multiSubst e R S).w a = ∑ x ∈ S.T a, ∏ i, (R i).w (x i) := by
  rw [Realisation.multiSubst, Realisation.w_mapIso]
  exact card_multiSubstSet e R S a

def multiCodeSet {r : ℕ} (e : Fin r → ℕ)
    (R : (i : Fin r) → Realisation A sep (strongPowPi G (e i)))
    (K : Code A sep r) : Finset ((i : Fin r) → Fin (e i) → V) :=
  K.C.biUnion (multiWordSet e R)

omit [Fintype V] in
theorem card_multiCodeSet {r : ℕ} (e : Fin r → ℕ)
    (R : (i : Fin r) → Realisation A sep (strongPowPi G (e i)))
    (K : Code A sep r) :
    (multiCodeSet e R K).card = ∑ x ∈ K.C, ∏ i, (R i).w (x i) := by
  have hd : ∀ x ∈ K.C, ∀ y ∈ K.C, x ≠ y →
      Disjoint (multiWordSet e R x) (multiWordSet e R y) := by
    intro x hx y hy hne
    rw [Finset.disjoint_left]
    intro f hf hf'
    exact sep_multiWordSet e R (K.hsep x hx y hy hne) f hf f hf' (Or.inl rfl)
  rw [multiCodeSet, Finset.card_biUnion hd]
  exact Finset.sum_congr rfl fun x _ => card_multiWordSet e R x

omit [Fintype V] in
theorem isIndepSet_multiCodeSet {r : ℕ} (e : Fin r → ℕ)
    (R : (i : Fin r) → Realisation A sep (strongPowPi G (e i)))
    (K : Code A sep r) :
    (familyStrongPower G e).IsIndepSet
      (multiCodeSet e R K : Set ((i : Fin r) → Fin (e i) → V)) := by
  intro f hf g hg hne hadj
  simp only [Finset.mem_coe, multiCodeSet, Finset.mem_biUnion] at hf hg
  obtain ⟨x, hx, hfx⟩ := hf
  obtain ⟨y, hy, hgy⟩ := hg
  by_cases hxy : x = y
  · subst hxy
    exact isIndepSet_multiWordSet e R x hfx hgy hne hadj
  · exact sep_multiWordSet e R (K.hsep x hx y hy hxy) f hfx g hgy (Or.inr hadj)

theorem le_indepNum_multiCode {r : ℕ} (e : Fin r → ℕ)
    (R : (i : Fin r) → Realisation A sep (strongPowPi G (e i)))
    (K : Code A sep r) :
    (∑ x ∈ K.C, ∏ i, (R i).w (x i)) ≤ (strongPowPi G (∑ i, e i)).indepNum := by
  have hiso := (strongPower_sum_iso G e).symm
  have hind := isIndepSet_map_iso hiso (isIndepSet_multiCodeSet e R K)
  have hcard : ((multiCodeSet e R K).map hiso.toEquiv.toEmbedding).card =
      ∑ x ∈ K.C, ∏ i, (R i).w (x i) := by
    rw [Finset.card_map, card_multiCodeSet]
  exact hcard ▸ hind.card_le_indepNum

end MultiWord

end MultiSubst

/-! ## Seven-Letter Separation System (`Letter`, `Letter.sep`, `Letter.sigma`) -/

inductive Letter | B | N | A | D | O | H | V
  deriving DecidableEq, Fintype, Repr

namespace Letter

def sep : Letter → Letter → Bool
  | B, O => true | B, H => true | B, V => true
  | N, A => true | N, D => true | N, O => true | N, H => true | N, V => true
  | A, N => true | A, D => true | A, H => true
  | D, N => true | D, A => true | D, V => true
  | O, B => true | O, N => true
  | H, B => true | H, N => true | H, A => true
  | V, B => true | V, N => true | V, D => true
  | _, _ => false

theorem sep_symm (a b : Letter) : sep a b = sep b a := by cases a <;> cases b <;> rfl
theorem sep_irrefl (a : Letter) : sep a a = false := by cases a <;> rfl

def sigmaFun : Letter → Letter
  | A => D
  | D => A
  | H => V
  | V => H
  | x => x

def sigma : Letter ≃ Letter where
  toFun := sigmaFun
  invFun := sigmaFun
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

theorem sigma_sep (a b : Letter) : sep a b = sep (sigma a) (sigma b) := by
  cases a <;> cases b <;> rfl

def allList : List Letter := [B, N, A, D, O, H, V]

theorem mem_allList (a : Letter) : a ∈ allList := by cases a <;> decide

end Letter

section ListReflect

def wordsSep {q : ℕ} (x y : Fin q → Letter) : Bool :=
  (List.finRange q).any (fun i => Letter.sep (x i) (y i))

theorem wordsSep_iff {q : ℕ} (x y : Fin q → Letter) :
    wordsSep x y = true ↔ ∃ i, Letter.sep (x i) (y i) = true := by
  simp [wordsSep, List.any_eq_true, List.mem_finRange]

def listPairwiseSep {q : ℕ} : List (Fin q → Letter) → Bool
  | [] => true
  | x :: xs => xs.all (fun y => wordsSep x y) && listPairwiseSep xs

theorem listPairwiseSep_sound {q : ℕ} : ∀ {l : List (Fin q → Letter)},
    listPairwiseSep l = true → ∀ x ∈ l, ∀ y ∈ l, x ≠ y → ∃ i, Letter.sep (x i) (y i) = true
  | [], _, x, hx, _, _, _ => by simp at hx
  | a :: rest, h, x, hx, y, hy, hne => by
    simp only [listPairwiseSep, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd rfl hne
      · exact (wordsSep_iff x y).mp (List.all_eq_true.mp h.1 y hy')
    · rcases List.mem_cons.mp hy with rfl | hy'
      · obtain ⟨i, hi⟩ := (wordsSep_iff y x).mp (List.all_eq_true.mp h.1 x hx')
        exact ⟨i, by rwa [Letter.sep_symm]⟩
      · exact listPairwiseSep_sound h.2 x hx' y hy' hne

def listCrossSep {q : ℕ} (xs ys : List (Fin q → Letter)) : Bool :=
  xs.all (fun x => ys.all (fun y => wordsSep x y))

theorem listCrossSep_sound {q : ℕ} {xs ys : List (Fin q → Letter)}
    (h : listCrossSep xs ys = true) :
    ∀ x ∈ xs, ∀ y ∈ ys, ∃ i, Letter.sep (x i) (y i) = true := by
  intro x hx y hy
  exact (wordsSep_iff x y).mp (List.all_eq_true.mp (List.all_eq_true.mp h x hx) y hy)

def substListOK {q : ℕ} (T : Letter → List (Fin q → Letter)) : Bool :=
  Letter.allList.all (fun a => (T a).Nodup && listPairwiseSep (T a)) &&
  Letter.allList.all (fun a => Letter.allList.all (fun b =>
    !(Letter.sep a b) || listCrossSep (T a) (T b)))

def Subst.ofLists {q : ℕ} (T : Letter → List (Fin q → Letter))
    (h : substListOK T = true) : Subst Letter Letter.sep q where
  T a := (T a).toFinset
  hin a x hx y hy hne := by
    have htop := (Bool.and_eq_true _ _).mp h
    have h1 := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp htop.1 a (Letter.mem_allList a))
    exact listPairwiseSep_sound h1.2 x (List.mem_toFinset.mp hx)
      y (List.mem_toFinset.mp hy) hne
  hcross a b hab x hx y hy := by
    have htop := (Bool.and_eq_true _ _).mp h
    have h2 := List.all_eq_true.mp (List.all_eq_true.mp htop.2 a
      (Letter.mem_allList a)) b (Letter.mem_allList b)
    simp only [hab, Bool.not_true, Bool.false_or] at h2
    exact listCrossSep_sound h2 x (List.mem_toFinset.mp hx) y (List.mem_toFinset.mp hy)

theorem w_multiSubst_ofLists {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation Letter Letter.sep (strongPowPi G (e i)))
    (T : Letter → List (Fin q → Letter)) (h : substListOK T = true) (a : Letter) :
    (Realisation.multiSubst e R (Subst.ofLists T h)).w a =
      ((T a).map (fun x => ∏ i, (R i).w (x i))).sum := by
  rw [w_multiSubst]
  have htop := (Bool.and_eq_true _ _).mp h
  have h1 := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp htop.1 a (Letter.mem_allList a))
  have hnd : (T a).Nodup := of_decide_eq_true h1.1
  change ∑ x ∈ (T a).toFinset, ∏ i, (R i).w (x i) = _
  rw [List.sum_toFinset _ hnd]

def codeListOK {r : ℕ} (C : List (Fin r → Letter)) : Bool :=
  C.Nodup && listPairwiseSep C

def Code.ofList {r : ℕ} (C : List (Fin r → Letter)) (h : codeListOK C = true) :
    Code Letter Letter.sep r where
  C := C.toFinset
  hsep x hx y hy hne :=
    listPairwiseSep_sound ((Bool.and_eq_true _ _).mp h).2 x (List.mem_toFinset.mp hx)
      y (List.mem_toFinset.mp hy) hne

theorem le_indepNum_multiCode_ofList {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {r : ℕ} (e : Fin r → ℕ)
    (R : (i : Fin r) → Realisation Letter Letter.sep (strongPowPi G (e i)))
    (C : List (Fin r → Letter)) (h : codeListOK C = true) :
    (C.map (fun x => ∏ i, (R i).w (x i))).sum ≤ (strongPowPi G (∑ i, e i)).indepNum := by
  have hnd : C.Nodup := of_decide_eq_true ((Bool.and_eq_true _ _).mp h).1
  have hsum : (∑ x ∈ (Code.ofList C h).C, ∏ i, (R i).w (x i)) =
      (C.map (fun x => ∏ i, (R i).w (x i))).sum := by
    change ∑ x ∈ C.toFinset, ∏ i, (R i).w (x i) = _
    rw [List.sum_toFinset _ hnd]
  rw [← hsum]
  exact le_indepNum_multiCode e R (Code.ofList C h)

end ListReflect

/-! ## BPZ v2 `Realisation.sigma` & Certified Tables (`S2a, S3b, K4a`) -/

def Realisation.sigma {V : Type*} {G : SimpleGraph V}
    (R : Realisation Letter Letter.sep G) : Realisation Letter Letter.sep G :=
  R.reindex Letter.sigma Letter.sigma_sep

@[simp]
theorem Realisation.w_sigma {V : Type*} {G : SimpleGraph V}
    (R : Realisation Letter Letter.sep G) (a : Letter) :
    R.sigma.w a = R.w (Letter.sigma a) := rfl

namespace BPZTables

open Letter

def T2aList : Letter → List (Fin 2 → Letter)
  | B => [![B, B], ![H, D], ![V, A], ![D, V], ![A, H]]
  | N => [![N, N], ![A, A], ![A, D], ![D, A], ![D, D]]
  | A => [![A, N], ![N, D]]
  | D => [![D, N], ![N, A]]
  | O => [![O, N], ![N, O]]
  | H => [![H, N], ![N, V]]
  | V => [![V, N], ![N, H]]

theorem T2a_ok : substListOK T2aList = true := rfl
def S2a : Subst Letter Letter.sep 2 := Subst.ofLists T2aList T2a_ok

def T3bList : Letter → List (Fin 3 → Letter)
  | B => [![B, B, B], ![B, H, A], ![N, A, V], ![N, D, H], ![N, V, D], ![A, B, H], ![A, H, N],
          ![A, H, D], ![D, B, V], ![D, V, N], ![D, V, D], ![H, N, D], ![H, D, N], ![H, D, D],
          ![V, N, A], ![V, A, B], ![V, D, A]]
  | N => [![B, V, D], ![N, N, N], ![N, V, A], ![A, N, H], ![A, D, H], ![A, H, N], ![D, N, V],
          ![D, D, H], ![D, H, N], ![H, V, D]]
  | A => [![N, B, A], ![N, A, N], ![A, B, B], ![A, A, V], ![A, H, A]]
  | D => [![N, B, D], ![N, D, N], ![D, B, B], ![D, A, V], ![D, H, A]]
  | O => []
  | H => [![N, N, H], ![N, H, N], ![H, N, N], ![H, V, V]]
  | V => [![N, N, V], ![N, V, N], ![V, N, N], ![V, V, V]]

theorem T3b_ok : substListOK T3bList = true := rfl
def S3b : Subst Letter Letter.sep 3 := Subst.ofLists T3bList T3b_ok

def C4aList : List (Fin 4 → Letter) :=
  [![B, B, B, B], ![B, N, V, B], ![B, A, H, B], ![B, D, V, B], ![B, H, N, B], ![B, H, D, B],
   ![B, V, A, B], ![N, B, B, V], ![N, N, V, H], ![N, A, V, H], ![N, D, H, H], ![N, H, N, H],
   ![N, H, A, H], ![N, V, D, V], ![A, B, B, V], ![A, N, H, H], ![A, A, V, H], ![A, D, H, H],
   ![A, H, A, H], ![A, V, N, H], ![A, V, D, H], ![D, B, B, H], ![D, N, V, V], ![D, A, V, V],
   ![D, D, H, V], ![D, H, N, V], ![D, H, A, V], ![D, V, D, V], ![H, B, B, A], ![H, N, V, D],
   ![H, A, H, D], ![H, A, V, N], ![H, D, H, N], ![H, D, V, D], ![H, H, N, N], ![H, H, N, D],
   ![H, H, A, N], ![H, H, D, D], ![H, V, A, D], ![H, V, D, N], ![V, B, B, N], ![V, B, B, D],
   ![V, N, V, N], ![V, N, V, A], ![V, A, H, A], ![V, D, V, A], ![V, H, D, A], ![V, V, N, A],
   ![V, V, A, A]]

theorem C4a_ok : codeListOK C4aList = true := rfl
def K4a : Code Letter Letter.sep 4 := Code.ofList C4aList C4a_ok

end BPZTables

/-! ## Heterogeneous Gao Product (`HetGao`, Tandon `arXiv:2608.30273` Theorem 1) -/

section HetGao

variable {V_L V_R : Type*} [DecidableEq V_L] [DecidableEq V_R]
  {G_L : SimpleGraph V_L} {G_R : SimpleGraph V_R}

/-- Valid heterogeneous auxiliary input on the left factor `R_L`. -/
structure HetLeftInput (R_L : Realisation Letter Letter.sep G_L) where
  J0_N : Finset V_L
  J0_D : Finset V_L
  J0_A : Finset V_L
  JH_out : Finset V_L
  JH_in : Finset V_L
  JV_out : Finset V_L
  JV_in : Finset V_L
  indep_J0_N : G_L.IsIndepSet (J0_N : Set V_L)
  indep_J0_D : G_L.IsIndepSet (J0_D : Set V_L)
  indep_J0_A : G_L.IsIndepSet (J0_A : Set V_L)
  sep_J0_ND : Sep G_L J0_N J0_D
  sep_J0_NA : Sep G_L J0_N J0_A
  sep_J0_DA : Sep G_L J0_D J0_A
  sep_J0_N_O : Sep G_L J0_N (R_L.P .O)
  sep_J0_N_H : Sep G_L J0_N (R_L.P .H)
  sep_J0_N_V : Sep G_L J0_N (R_L.P .V)
  sep_J0_D_V : Sep G_L J0_D (R_L.P .V)
  sep_J0_A_H : Sep G_L J0_A (R_L.P .H)
  indep_JH_out : G_L.IsIndepSet (JH_out : Set V_L)
  indep_JH_in : G_L.IsIndepSet (JH_in : Set V_L)
  sep_JH : Sep G_L JH_out JH_in
  sep_JH_out_N : Sep G_L JH_out (R_L.P .N)
  indep_JV_out : G_L.IsIndepSet (JV_out : Set V_L)
  indep_JV_in : G_L.IsIndepSet (JV_in : Set V_L)
  sep_JV : Sep G_L JV_out JV_in
  sep_JV_out_N : Sep G_L JV_out (R_L.P .N)

/-- Orientation reversal `sigma` on `HetLeftInput` (swaps `J0_D ↔ J0_A`). -/
def HetLeftInput.sigma {R_L : Realisation Letter Letter.sep G_L}
    (inp : HetLeftInput R_L) : HetLeftInput R_L.sigma where
  J0_N := inp.J0_N
  J0_D := inp.J0_A
  J0_A := inp.J0_D
  JH_out := inp.JH_out
  JH_in := inp.JH_in
  JV_out := inp.JV_out
  JV_in := inp.JV_in
  indep_J0_N := inp.indep_J0_N
  indep_J0_D := inp.indep_J0_A
  indep_J0_A := inp.indep_J0_D
  sep_J0_ND := inp.sep_J0_NA
  sep_J0_NA := inp.sep_J0_ND
  sep_J0_DA := inp.sep_J0_DA.symm
  sep_J0_N_O := inp.sep_J0_N_O
  sep_J0_N_H := inp.sep_J0_N_V
  sep_J0_N_V := inp.sep_J0_N_H
  sep_J0_D_V := inp.sep_J0_A_H
  sep_J0_A_H := inp.sep_J0_D_V
  indep_JH_out := inp.indep_JH_out
  indep_JH_in := inp.indep_JH_in
  sep_JH := inp.sep_JH
  sep_JH_out_N := inp.sep_JH_out_N
  indep_JV_out := inp.indep_JV_out
  indep_JV_in := inp.indep_JV_in
  sep_JV := inp.sep_JV
  sep_JV_out_N := inp.sep_JV_out_N

/-- Build a `HetLeftInput` using a sibling `R_sib` sharing `O, H, V` with `R_L` and two
partitioned independent sets `(JH_out, JH_in)` and `(JV_out, JV_in)`. -/
def HetLeftInput.ofSiblingAndParts (R_L R_sib : Realisation Letter Letter.sep G_L)
    (hO : R_sib.P .O = R_L.P .O) (hH : R_sib.P .H = R_L.P .H) (hV : R_sib.P .V = R_L.P .V)
    (JH_out JH_in JV_out JV_in : Finset V_L)
    (hJHo : G_L.IsIndepSet (JH_out : Set V_L)) (hJHi : G_L.IsIndepSet (JH_in : Set V_L))
    (hsJH : Sep G_L JH_out JH_in) (hsJHN : Sep G_L JH_out (R_L.P .N))
    (hJVo : G_L.IsIndepSet (JV_out : Set V_L)) (hJVi : G_L.IsIndepSet (JV_in : Set V_L))
    (hsJV : Sep G_L JV_out JV_in) (hsJVN : Sep G_L JV_out (R_L.P .N)) :
    HetLeftInput R_L where
  J0_N := R_sib.P .N
  J0_D := R_sib.P .D
  J0_A := R_sib.P .A
  JH_out := JH_out
  JH_in := JH_in
  JV_out := JV_out
  JV_in := JV_in
  indep_J0_N := R_sib.hindep .N
  indep_J0_D := R_sib.hindep .D
  indep_J0_A := R_sib.hindep .A
  sep_J0_ND := R_sib.hsep .N .D rfl
  sep_J0_NA := R_sib.hsep .N .A rfl
  sep_J0_DA := R_sib.hsep .D .A rfl
  sep_J0_N_O := hO ▸ R_sib.hsep .N .O rfl
  sep_J0_N_H := hH ▸ R_sib.hsep .N .H rfl
  sep_J0_N_V := hV ▸ R_sib.hsep .N .V rfl
  sep_J0_D_V := hV ▸ R_sib.hsep .D .V rfl
  sep_J0_A_H := hH ▸ R_sib.hsep .A .H rfl
  indep_JH_out := hJHo
  indep_JH_in := hJHi
  sep_JH := hsJH
  sep_JH_out_N := hsJHN
  indep_JV_out := hJVo
  indep_JV_in := hJVi
  sep_JV := hsJV
  sep_JV_out_N := hsJVN

/-- Partition any independent set `J` into `J_out` (separated from `R_L.P .N`) and `J_in := J \ J_out`. -/
def HetLeftInput.ofJ (R_L R_sib : Realisation Letter Letter.sep G_L)
    (hO : R_sib.P .O = R_L.P .O) (hH : R_sib.P .H = R_L.P .H) (hV : R_sib.P .V = R_L.P .V)
    (JH JV : Finset V_L)
    (hJH : G_L.IsIndepSet (JH : Set V_L)) (hJV : G_L.IsIndepSet (JV : Set V_L))
    (JH_out JV_out : Finset V_L)
    (hJH_sub : JH_out ⊆ JH) (hJV_sub : JV_out ⊆ JV)
    (hJH_sep : Sep G_L JH_out (R_L.P .N)) (hJV_sep : Sep G_L JV_out (R_L.P .N)) :
    HetLeftInput R_L :=
  HetLeftInput.ofSiblingAndParts R_L R_sib hO hH hV
    JH_out (JH \ JH_out) JV_out (JV \ JV_out)
    (isIndepSet_subset hJH hJH_sub)
    (isIndepSet_subset hJH Finset.sdiff_subset)
    (fun x hx y hy hc => by
      rw [Finset.mem_sdiff] at hy
      exact isIndepSet_not_close_of_ne hJH (hJH_sub hx) hy.1 (fun heq => hy.2 (heq ▸ hx)) hc)
    hJH_sep
    (isIndepSet_subset hJV hJV_sub)
    (isIndepSet_subset hJV Finset.sdiff_subset)
    (fun x hx y hy hc => by
      rw [Finset.mem_sdiff] at hy
      exact isIndepSet_not_close_of_ne hJV (hJV_sub hx) hy.1 (fun heq => hy.2 (heq ▸ hx)) hc)
    hJV_sep

/-- Auxiliary family definition for `hetGao2` on `G_L ⊠ G_R`. -/
def hetGaoFam (R_L : Realisation Letter Letter.sep G_L)
    (R_R : Realisation Letter Letter.sep G_R) (inp : HetLeftInput R_L) :
    Letter → Finset (V_L × V_R)
  | .B => (R_L.P .B ×ˢ R_R.P .B) ∪ (R_L.P .H ×ˢ R_R.P .D) ∪ (R_L.P .V ×ˢ R_R.P .A) ∪
          (R_L.P .D ×ˢ R_R.P .V) ∪ (R_L.P .A ×ˢ R_R.P .H)
  | .N => (inp.J0_N ×ˢ R_R.P .N) ∪ (inp.JH_out ×ˢ R_R.P .D) ∪ (inp.JV_out ×ˢ R_R.P .A)
  | .A => (inp.J0_A ×ˢ R_R.P .N) ∪ (inp.JH_in ×ˢ R_R.P .D)
  | .D => (inp.J0_D ×ˢ R_R.P .N) ∪ (inp.JV_in ×ˢ R_R.P .A)
  | .O => (R_L.P .O ×ˢ R_R.P .N) ∪ (R_L.P .N ×ˢ R_R.P .O)
  | .H => (R_L.P .H ×ˢ R_R.P .N) ∪ (R_L.P .N ×ˢ R_R.P .V)
  | .V => (R_L.P .V ×ˢ R_R.P .N) ∪ (R_L.P .N ×ˢ R_R.P .H)

/-- Pure-kernel heterogeneous Gao product `hetGao2` on `G_L ⊠ G_R`. -/
def Realisation.hetGao2 (R_L : Realisation Letter Letter.sep G_L)
    (R_R : Realisation Letter Letter.sep G_R) (inp : HetLeftInput R_L) :
    Realisation Letter Letter.sep (G_L ⊠ G_R) where
  P := hetGaoFam R_L R_R inp
  hindep a := by
    have iL := R_L.hindep
    have iR := R_R.hindep
    have sL := R_L.hsep
    have sR := R_R.hsep
    cases a
    · -- B
      refine isIndepSet_union_of_sep
        (isIndepSet_union_of_sep
          (isIndepSet_union_of_sep
            (isIndepSet_union_of_sep (isIndepSet_strongProd (iL .B) (iR .B))
              (isIndepSet_strongProd (iL .H) (iR .D)) (sep_prod_left (sL .B .H rfl)))
            (isIndepSet_strongProd (iL .V) (iR .A))
            (Sep.union_left (sep_prod_left (sL .B .V rfl)) (sep_prod_right (sR .D .A rfl))))
          (isIndepSet_strongProd (iL .D) (iR .V))
          (Sep.union_left
            (Sep.union_left (sep_prod_right (sR .B .V rfl)) (sep_prod_right (sR .D .V rfl)))
            (sep_prod_left (sL .V .D rfl))))
        (isIndepSet_strongProd (iL .A) (iR .H))
        (Sep.union_left
          (Sep.union_left
            (Sep.union_left (sep_prod_right (sR .B .H rfl)) (sep_prod_left (sL .H .A rfl)))
            (sep_prod_right (sR .A .H rfl)))
          (sep_prod_left (sL .D .A rfl)))
    · -- N
      refine isIndepSet_union_of_sep
        (isIndepSet_union_of_sep (isIndepSet_strongProd inp.indep_J0_N (iR .N))
          (isIndepSet_strongProd inp.indep_JH_out (iR .D)) (sep_prod_right (sR .N .D rfl)))
        (isIndepSet_strongProd inp.indep_JV_out (iR .A))
        (Sep.union_left (sep_prod_right (sR .N .A rfl)) (sep_prod_right (sR .D .A rfl)))
    · -- A
      exact isIndepSet_union_of_sep (isIndepSet_strongProd inp.indep_J0_A (iR .N))
        (isIndepSet_strongProd inp.indep_JH_in (iR .D)) (sep_prod_right (sR .N .D rfl))
    · -- D
      exact isIndepSet_union_of_sep (isIndepSet_strongProd inp.indep_J0_D (iR .N))
        (isIndepSet_strongProd inp.indep_JV_in (iR .A)) (sep_prod_right (sR .N .A rfl))
    · -- O
      exact isIndepSet_union_of_sep (isIndepSet_strongProd (iL .O) (iR .N))
        (isIndepSet_strongProd (iL .N) (iR .O)) (sep_prod_left (sL .O .N rfl))
    · -- H
      exact isIndepSet_union_of_sep (isIndepSet_strongProd (iL .H) (iR .N))
        (isIndepSet_strongProd (iL .N) (iR .V)) (sep_prod_left (sL .H .N rfl))
    · -- V
      exact isIndepSet_union_of_sep (isIndepSet_strongProd (iL .V) (iR .N))
        (isIndepSet_strongProd (iL .N) (iR .H)) (sep_prod_left (sL .V .N rfl))
  hsep a b hab := by
    have sL := R_L.hsep
    have sR := R_R.hsep
    cases a <;> cases b <;> simp only [Letter.sep, reduceCtorEq] at hab
    all_goals dsimp only [hetGaoFam]
    · -- B, O
      exact Sep.union_right
        (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
          (sep_prod_left (sL .B .O rfl)) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl))) (sep_prod_right (sR .V .N rfl)))
          (sep_prod_right (sR .H .N rfl)))
        (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .B .O rfl)) (sep_prod_left (sL .H .N rfl)))
          (sep_prod_left (sL .V .N rfl))) (sep_prod_left (sL .D .N rfl)))
          (sep_prod_left (sL .A .N rfl)))
    · -- B, H
      exact Sep.union_right
        (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
          (sep_prod_left (sL .B .H rfl)) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl))) (sep_prod_right (sR .V .N rfl)))
          (sep_prod_right (sR .H .N rfl)))
        (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .B .V rfl)) (sep_prod_left (sL .H .N rfl)))
          (sep_prod_left (sL .V .N rfl))) (sep_prod_left (sL .D .N rfl)))
          (sep_prod_left (sL .A .N rfl)))
    · -- B, V
      exact Sep.union_right
        (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
          (sep_prod_left (sL .B .V rfl)) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl))) (sep_prod_right (sR .V .N rfl)))
          (sep_prod_right (sR .H .N rfl)))
        (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .B .H rfl)) (sep_prod_left (sL .H .N rfl)))
          (sep_prod_left (sL .V .N rfl))) (sep_prod_left (sL .D .N rfl)))
          (sep_prod_left (sL .A .N rfl)))
    · -- N, A
      exact Sep.union_right
        (Sep.union_left (Sep.union_left
          (sep_prod_left inp.sep_J0_NA) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl)))
        (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .N .D rfl)) (sep_prod_left inp.sep_JH))
          (sep_prod_right (sR .A .D rfl)))
    · -- N, D
      exact Sep.union_right
        (Sep.union_left (Sep.union_left
          (sep_prod_left inp.sep_J0_ND) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl)))
        (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .N .A rfl)) (sep_prod_right (sR .D .A rfl)))
          (sep_prod_left inp.sep_JV))
    · -- N, O
      exact Sep.union_right
        (Sep.union_left (Sep.union_left
          (sep_prod_left inp.sep_J0_N_O) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl)))
        (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .N .O rfl)) (sep_prod_left inp.sep_JH_out_N))
          (sep_prod_left inp.sep_JV_out_N))
    · -- N, H
      exact Sep.union_right
        (Sep.union_left (Sep.union_left
          (sep_prod_left inp.sep_J0_N_H) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl)))
        (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .N .V rfl)) (sep_prod_left inp.sep_JH_out_N))
          (sep_prod_left inp.sep_JV_out_N))
    · -- N, V
      exact Sep.union_right
        (Sep.union_left (Sep.union_left
          (sep_prod_left inp.sep_J0_N_V) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl)))
        (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .N .H rfl)) (sep_prod_left inp.sep_JH_out_N))
          (sep_prod_left inp.sep_JV_out_N))
    · -- A, N
      exact (Sep.union_right
        (Sep.union_left (Sep.union_left
          (sep_prod_left inp.sep_J0_NA) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl)))
        (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .N .D rfl)) (sep_prod_left inp.sep_JH))
          (sep_prod_right (sR .A .D rfl)))).symm
    · -- A, D
      exact Sep.union_right
        (Sep.union_left (sep_prod_left inp.sep_J0_DA.symm) (sep_prod_right (sR .D .N rfl)))
        (Sep.union_left (sep_prod_right (sR .N .A rfl)) (sep_prod_right (sR .D .A rfl)))
    · -- A, H
      exact Sep.union_right
        (Sep.union_left (sep_prod_left inp.sep_J0_A_H) (sep_prod_right (sR .D .N rfl)))
        (Sep.union_left (sep_prod_right (sR .N .V rfl)) (sep_prod_right (sR .D .V rfl)))
    · -- D, N
      exact (Sep.union_right
        (Sep.union_left (Sep.union_left
          (sep_prod_left inp.sep_J0_ND) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl)))
        (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .N .A rfl)) (sep_prod_right (sR .D .A rfl)))
          (sep_prod_left inp.sep_JV))).symm
    · -- D, A
      exact (Sep.union_right
        (Sep.union_left (sep_prod_left inp.sep_J0_DA.symm) (sep_prod_right (sR .D .N rfl)))
        (Sep.union_left (sep_prod_right (sR .N .A rfl)) (sep_prod_right (sR .D .A rfl)))).symm
    · -- D, V
      exact Sep.union_right
        (Sep.union_left (sep_prod_left inp.sep_J0_D_V) (sep_prod_right (sR .A .N rfl)))
        (Sep.union_left (sep_prod_right (sR .N .H rfl)) (sep_prod_right (sR .A .H rfl)))
    · -- O, B
      exact (Sep.union_right
        (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
          (sep_prod_left (sL .B .O rfl)) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl))) (sep_prod_right (sR .V .N rfl)))
          (sep_prod_right (sR .H .N rfl)))
        (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .B .O rfl)) (sep_prod_left (sL .H .N rfl)))
          (sep_prod_left (sL .V .N rfl))) (sep_prod_left (sL .D .N rfl)))
          (sep_prod_left (sL .A .N rfl)))).symm
    · -- O, N
      exact (Sep.union_right
        (Sep.union_left (Sep.union_left
          (sep_prod_left inp.sep_J0_N_O) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl)))
        (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .N .O rfl)) (sep_prod_left inp.sep_JH_out_N))
          (sep_prod_left inp.sep_JV_out_N))).symm
    · -- H, B
      exact (Sep.union_right
        (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
          (sep_prod_left (sL .B .H rfl)) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl))) (sep_prod_right (sR .V .N rfl)))
          (sep_prod_right (sR .H .N rfl)))
        (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .B .V rfl)) (sep_prod_left (sL .H .N rfl)))
          (sep_prod_left (sL .V .N rfl))) (sep_prod_left (sL .D .N rfl)))
          (sep_prod_left (sL .A .N rfl)))).symm
    · -- H, N
      exact (Sep.union_right
        (Sep.union_left (Sep.union_left
          (sep_prod_left inp.sep_J0_N_H) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl)))
        (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .N .V rfl)) (sep_prod_left inp.sep_JH_out_N))
          (sep_prod_left inp.sep_JV_out_N))).symm
    · -- H, A
      exact (Sep.union_right
        (Sep.union_left (sep_prod_left inp.sep_J0_A_H) (sep_prod_right (sR .D .N rfl)))
        (Sep.union_left (sep_prod_right (sR .N .V rfl)) (sep_prod_right (sR .D .V rfl)))).symm
    · -- V, B
      exact (Sep.union_right
        (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
          (sep_prod_left (sL .B .V rfl)) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl))) (sep_prod_right (sR .V .N rfl)))
          (sep_prod_right (sR .H .N rfl)))
        (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .B .H rfl)) (sep_prod_left (sL .H .N rfl)))
          (sep_prod_left (sL .V .N rfl))) (sep_prod_left (sL .D .N rfl)))
          (sep_prod_left (sL .A .N rfl)))).symm
    · -- V, N
      exact (Sep.union_right
        (Sep.union_left (Sep.union_left
          (sep_prod_left inp.sep_J0_N_V) (sep_prod_right (sR .D .N rfl)))
          (sep_prod_right (sR .A .N rfl)))
        (Sep.union_left (Sep.union_left
          (sep_prod_right (sR .N .H rfl)) (sep_prod_left inp.sep_JH_out_N))
          (sep_prod_left inp.sep_JV_out_N))).symm
    · -- V, D
      exact (Sep.union_right
        (Sep.union_left (sep_prod_left inp.sep_J0_D_V) (sep_prod_right (sR .A .N rfl)))
        (Sep.union_left (sep_prod_right (sR .N .H rfl)) (sep_prod_right (sR .A .H rfl)))).symm

/-- Exact weight formulas for `hetGao2`. -/
theorem w_hetGao2 (R_L : Realisation Letter Letter.sep G_L)
    (R_R : Realisation Letter Letter.sep G_R) (inp : HetLeftInput R_L) :
    (R_L.hetGao2 R_R inp).w .B =
      R_L.w .B * R_R.w .B + R_L.w .H * R_R.w .D + R_L.w .V * R_R.w .A +
        R_L.w .D * R_R.w .V + R_L.w .A * R_R.w .H ∧
    (R_L.hetGao2 R_R inp).w .N =
      inp.J0_N.card * R_R.w .N + inp.JH_out.card * R_R.w .D + inp.JV_out.card * R_R.w .A ∧
    (R_L.hetGao2 R_R inp).w .A =
      inp.J0_A.card * R_R.w .N + inp.JH_in.card * R_R.w .D ∧
    (R_L.hetGao2 R_R inp).w .D =
      inp.J0_D.card * R_R.w .N + inp.JV_in.card * R_R.w .A ∧
    (R_L.hetGao2 R_R inp).w .O = R_L.w .O * R_R.w .N + R_L.w .N * R_R.w .O ∧
    (R_L.hetGao2 R_R inp).w .H = R_L.w .H * R_R.w .N + R_L.w .N * R_R.w .V ∧
    (R_L.hetGao2 R_R inp).w .V = R_L.w .V * R_R.w .N + R_L.w .N * R_R.w .H := by
  have sL := R_L.hsep
  have sR := R_R.hsep
  have dprod : ∀ {P Q : Finset (V_L × V_R)}, Sep (G_L ⊠ G_R) P Q → Disjoint P Q :=
    fun h => h.disjoint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [Realisation.w, Realisation.hetGao2, hetGaoFam]
  · -- B
    have h12 : Disjoint (R_L.P .B ×ˢ R_R.P .B) (R_L.P .H ×ˢ R_R.P .D) :=
      dprod (sep_prod_left (sL .B .H rfl))
    have h123 : Disjoint ((R_L.P .B ×ˢ R_R.P .B) ∪ (R_L.P .H ×ˢ R_R.P .D)) (R_L.P .V ×ˢ R_R.P .A) :=
      dprod (Sep.union_left (sep_prod_left (sL .B .V rfl)) (sep_prod_right (sR .D .A rfl)))
    have h1234 : Disjoint (((R_L.P .B ×ˢ R_R.P .B) ∪ (R_L.P .H ×ˢ R_R.P .D)) ∪ (R_L.P .V ×ˢ R_R.P .A))
        (R_L.P .D ×ˢ R_R.P .V) :=
      dprod (Sep.union_left (Sep.union_left (sep_prod_right (sR .B .V rfl))
        (sep_prod_right (sR .D .V rfl))) (sep_prod_left (sL .V .D rfl)))
    have h12345 : Disjoint ((((R_L.P .B ×ˢ R_R.P .B) ∪ (R_L.P .H ×ˢ R_R.P .D)) ∪
        (R_L.P .V ×ˢ R_R.P .A)) ∪ (R_L.P .D ×ˢ R_R.P .V)) (R_L.P .A ×ˢ R_R.P .H) :=
      dprod (Sep.union_left (Sep.union_left (Sep.union_left (sep_prod_right (sR .B .H rfl))
        (sep_prod_left (sL .H .A rfl))) (sep_prod_right (sR .A .H rfl)))
        (sep_prod_left (sL .D .A rfl)))
    rw [Finset.card_union_of_disjoint h12345, Finset.card_union_of_disjoint h1234,
        Finset.card_union_of_disjoint h123, Finset.card_union_of_disjoint h12]
    simp [Finset.card_product]
  · -- N
    have h12 : Disjoint (inp.J0_N ×ˢ R_R.P .N) (inp.JH_out ×ˢ R_R.P .D) :=
      dprod (sep_prod_right (sR .N .D rfl))
    have h123 : Disjoint ((inp.J0_N ×ˢ R_R.P .N) ∪ (inp.JH_out ×ˢ R_R.P .D))
        (inp.JV_out ×ˢ R_R.P .A) :=
      dprod (Sep.union_left (sep_prod_right (sR .N .A rfl)) (sep_prod_right (sR .D .A rfl)))
    rw [Finset.card_union_of_disjoint h123, Finset.card_union_of_disjoint h12]
    simp [Finset.card_product]
  · -- A
    have h12 : Disjoint (inp.J0_A ×ˢ R_R.P .N) (inp.JH_in ×ˢ R_R.P .D) :=
      dprod (sep_prod_right (sR .N .D rfl))
    rw [Finset.card_union_of_disjoint h12]
    simp [Finset.card_product]
  · -- D
    have h12 : Disjoint (inp.J0_D ×ˢ R_R.P .N) (inp.JV_in ×ˢ R_R.P .A) :=
      dprod (sep_prod_right (sR .N .A rfl))
    rw [Finset.card_union_of_disjoint h12]
    simp [Finset.card_product]
  · -- O
    have h12 : Disjoint (R_L.P .O ×ˢ R_R.P .N) (R_L.P .N ×ˢ R_R.P .O) :=
      dprod (sep_prod_left (sL .O .N rfl))
    rw [Finset.card_union_of_disjoint h12]
    simp [Finset.card_product]
  · -- H
    have h12 : Disjoint (R_L.P .H ×ˢ R_R.P .N) (R_L.P .N ×ˢ R_R.P .V) :=
      dprod (sep_prod_left (sL .H .N rfl))
    rw [Finset.card_union_of_disjoint h12]
    simp [Finset.card_product]
  · -- V
    have h12 : Disjoint (R_L.P .V ×ˢ R_R.P .N) (R_L.P .N ×ˢ R_R.P .H) :=
      dprod (sep_prod_left (sL .V .N rfl))
    rw [Finset.card_union_of_disjoint h12]
    simp [Finset.card_product]

/-- `hetGao` on `strongPowPi G (dL + dR)`. -/
def Realisation.hetGao {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {dL dR : ℕ} (R_L : Realisation Letter Letter.sep (strongPowPi G dL))
    (R_R : Realisation Letter Letter.sep (strongPowPi G dR))
    (inp : HetLeftInput R_L) :
    Realisation Letter Letter.sep (strongPowPi G (dL + dR)) :=
  (R_L.hetGao2 R_R inp).mapIso (strongProdIsoAdd G dL dR)

theorem w_hetGao {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {dL dR : ℕ} (R_L : Realisation Letter Letter.sep (strongPowPi G dL))
    (R_R : Realisation Letter Letter.sep (strongPowPi G dR))
    (inp : HetLeftInput R_L) :
    (R_L.hetGao R_R inp).w .B =
      R_L.w .B * R_R.w .B + R_L.w .H * R_R.w .D + R_L.w .V * R_R.w .A +
        R_L.w .D * R_R.w .V + R_L.w .A * R_R.w .H ∧
    (R_L.hetGao R_R inp).w .N =
      inp.J0_N.card * R_R.w .N + inp.JH_out.card * R_R.w .D + inp.JV_out.card * R_R.w .A ∧
    (R_L.hetGao R_R inp).w .A =
      inp.J0_A.card * R_R.w .N + inp.JH_in.card * R_R.w .D ∧
    (R_L.hetGao R_R inp).w .D =
      inp.J0_D.card * R_R.w .N + inp.JV_in.card * R_R.w .A ∧
    (R_L.hetGao R_R inp).w .O = R_L.w .O * R_R.w .N + R_L.w .N * R_R.w .O ∧
    (R_L.hetGao R_R inp).w .H = R_L.w .H * R_R.w .N + R_L.w .N * R_R.w .V ∧
    (R_L.hetGao R_R inp).w .V = R_L.w .V * R_R.w .N + R_L.w .N * R_R.w .H := by
  simpa only [Realisation.hetGao, Realisation.w_mapIso] using w_hetGao2 R_L R_R inp

theorem hetGao_P_O_eq {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {dL dR : ℕ} (R_L : Realisation Letter Letter.sep (strongPowPi G dL))
    (R_R : Realisation Letter Letter.sep (strongPowPi G dR))
    (inp₁ inp₂ : HetLeftInput R_L) :
    (R_L.hetGao R_R inp₁).P .O = (R_L.hetGao R_R inp₂).P .O ∧
    (R_L.hetGao R_R inp₁).P .H = (R_L.hetGao R_R inp₂).P .H ∧
    (R_L.hetGao R_R inp₁).P .V = (R_L.hetGao R_R inp₂).P .V :=
  ⟨rfl, rfl, rfl⟩

/-- `HetLeftInput.ofSelf` recovers ordinary `S2a` as a special case of `hetGao`. -/
def HetLeftInput.ofSelf (R_L : Realisation Letter Letter.sep G_L) : HetLeftInput R_L where
  J0_N := R_L.P .N
  J0_D := R_L.P .D
  J0_A := R_L.P .A
  JH_out := R_L.P .D
  JH_in := R_L.P .A ∪ R_L.P .N
  JV_out := R_L.P .A
  JV_in := R_L.P .D ∪ R_L.P .N
  indep_J0_N := R_L.hindep .N
  indep_J0_D := R_L.hindep .D
  indep_J0_A := R_L.hindep .A
  sep_J0_ND := R_L.hsep .N .D rfl
  sep_J0_NA := R_L.hsep .N .A rfl
  sep_J0_DA := R_L.hsep .D .A rfl
  sep_J0_N_O := R_L.hsep .N .O rfl
  sep_J0_N_H := R_L.hsep .N .H rfl
  sep_J0_N_V := R_L.hsep .N .V rfl
  sep_J0_D_V := R_L.hsep .D .V rfl
  sep_J0_A_H := R_L.hsep .A .H rfl
  indep_JH_out := R_L.hindep .D
  indep_JH_in := isIndepSet_union_of_sep (R_L.hindep .A) (R_L.hindep .N) (R_L.hsep .A .N rfl)
  sep_JH := Sep.union_right (R_L.hsep .D .A rfl) (R_L.hsep .D .N rfl)
  sep_JH_out_N := R_L.hsep .D .N rfl
  indep_JV_out := R_L.hindep .A
  indep_JV_in := isIndepSet_union_of_sep (R_L.hindep .D) (R_L.hindep .N) (R_L.hsep .D .N rfl)
  sep_JV := Sep.union_right (R_L.hsep .A .D rfl) (R_L.hsep .A .N rfl)
  sep_JV_out_N := R_L.hsep .A .N rfl

end HetGao

end ShannonC7
