import ShannonC7.ValidTuple
import ShannonC7.Fekete
import ShannonC7.TrieVerifier
import ShannonC7.Decimal

/-!
# Heterogeneous Multi-Role, Multi-Port & Layered Auxiliary-Upgrading Engine

This module generalizes the homogeneous `ValidTuple.star` engine in `ShannonC7/ValidTuple.lean`
with three constructive, pure-kernel (`{propext, Classical.choice, Quot.sound}` only) engines:
1. **Part 1 — Heterogeneous Multi-Role & Terminal Substitution (`PortCore`, `AuxCode`,
   `AsymProfile`, `HeteroGadget`, `HeteroTree`, `HeteroDAG`):** decouples the main code
   `(I, S, f0, f1)` from auxiliary sets `X`, tracks exact 6-parameter `(a, b, c, d, h, v)`
   asymmetric profiles, supports aligned/flipped products, root-level two-sided and one-sided
   terminal substitution, and `O(L)` shared-DAG evaluation.
2. **Part 2 — Generalized Multi-Port Systems (`PortSystem G ι`):** supports arbitrary finite
   port-state spaces `ι` with any derangement `φ : ι ≃ ι` (`PortSystem.prod`, `finShift`,
   `ofColoring`), closing under exact `Profile.star`.
3. **Part 3 — Layered Interior-Pair Auxiliary Upgrading (`LayeredProfile`, `LayeredTuple`):**
   when an auxiliary set `X` carries interior private pairs strictly outside `N[P0] ∪ N[P1]`,
   constructively upgrades `X × X` strictly above `c²` with exact 6-parameter profile law
   (`upgradeProd_asymProfile`) and recursive multi-layer closure (`LayeredTuple.prod`,
   `prod_profile_bounds`).
4. **Part 4 — Pure-Kernel `Trie7` Constructors & Concrete 5D Base Gadget:** `PortCore.ofTrie7`,
   `AuxCode.ofTrie7`, `HeteroGadget.ofTrie7_asymProfile`, `LayeredTuple.ofTrie7`, and
   `baseHetero5D` (`(367, 8, 367, 322, 19, 26)`).
-/

namespace ShannonC7

/-! ## General Strong-Product & Disjoint-Union Helpers -/

theorem not_close_prod_fst {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {x y : V × W} (h : ¬ (x.1 = y.1 ∨ G.Adj x.1 y.1)) :
    ¬ (x = y ∨ (G ⊠ H).Adj x y) :=
  fun hc => h (eq_or_strongProd_adj.mp hc).1

theorem not_close_prod_snd {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {x y : V × W} (h : ¬ (x.2 = y.2 ∨ H.Adj x.2 y.2)) :
    ¬ (x = y ∨ (G ⊠ H).Adj x y) :=
  fun hc => h (eq_or_strongProd_adj.mp hc).2

theorem isIndepSet_subset {V : Type*} {G : SimpleGraph V} {A B : Finset V}
    (hB : G.IsIndepSet (B : Set V)) (hAB : A ⊆ B) :
    G.IsIndepSet (A : Set V) :=
  fun _ hx _ hy hne => hB (hAB hx) (hAB hy) hne

theorem card_sdiff_eq {V : Type*} [DecidableEq V] {A B : Finset V} (h : B ⊆ A) :
    (A \ B).card = A.card - B.card := by
  have hsum := Finset.card_sdiff_add_card_eq_card h
  omega

/-- Fast O(1)-elaboration cardinality of a 5-way disjoint union. -/
theorem card_union5 {α : Type*} [DecidableEq α] {A0 A1 A2 A3 A4 : Finset α}
    (d01 : Disjoint A0 A1) (d02 : Disjoint A0 A2) (d03 : Disjoint A0 A3) (d04 : Disjoint A0 A4)
    (d12 : Disjoint A1 A2) (d13 : Disjoint A1 A3) (d14 : Disjoint A1 A4)
    (d23 : Disjoint A2 A3) (d24 : Disjoint A2 A4) (d34 : Disjoint A3 A4) :
    (A0 ∪ A1 ∪ A2 ∪ A3 ∪ A4).card =
      A0.card + A1.card + A2.card + A3.card + A4.card := by
  have u01_2 : Disjoint (A0 ∪ A1) A2 := Finset.disjoint_union_left.mpr ⟨d02, d12⟩
  have u012_3 : Disjoint (A0 ∪ A1 ∪ A2) A3 :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨d03, d13⟩, d23⟩
  have u0123_4 : Disjoint (A0 ∪ A1 ∪ A2 ∪ A3) A4 :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨d04, d14⟩, d24⟩, d34⟩
  rw [Finset.card_union_of_disjoint u0123_4, Finset.card_union_of_disjoint u012_3,
      Finset.card_union_of_disjoint u01_2, Finset.card_union_of_disjoint d01]

/-- Fast O(1)-elaboration cardinality of a 7-way disjoint union. -/
theorem card_union7 {α : Type*} [DecidableEq α] {A0 A1 A2 A3 A4 A5 A6 : Finset α}
    (d01 : Disjoint A0 A1) (d02 : Disjoint A0 A2) (d03 : Disjoint A0 A3)
    (d04 : Disjoint A0 A4) (d05 : Disjoint A0 A5) (d06 : Disjoint A0 A6)
    (d12 : Disjoint A1 A2) (d13 : Disjoint A1 A3) (d14 : Disjoint A1 A4)
    (d15 : Disjoint A1 A5) (d16 : Disjoint A1 A6)
    (d23 : Disjoint A2 A3) (d24 : Disjoint A2 A4) (d25 : Disjoint A2 A5) (d26 : Disjoint A2 A6)
    (d34 : Disjoint A3 A4) (d35 : Disjoint A3 A5) (d36 : Disjoint A3 A6)
    (d45 : Disjoint A4 A5) (d46 : Disjoint A4 A6) (d56 : Disjoint A5 A6) :
    (A0 ∪ A1 ∪ A2 ∪ A3 ∪ A4 ∪ A5 ∪ A6).card =
      A0.card + A1.card + A2.card + A3.card + A4.card + A5.card + A6.card := by
  have u4 := card_union5 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34
  have u5 : Disjoint (A0 ∪ A1 ∪ A2 ∪ A3 ∪ A4) A5 :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr
          ⟨Finset.disjoint_union_left.mpr ⟨d05, d15⟩, d25⟩, d35⟩, d45⟩
  have u6 : Disjoint (A0 ∪ A1 ∪ A2 ∪ A3 ∪ A4 ∪ A5) A6 :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr
          ⟨Finset.disjoint_union_left.mpr
            ⟨Finset.disjoint_union_left.mpr ⟨d06, d16⟩, d26⟩, d36⟩, d46⟩, d56⟩
  rw [Finset.card_union_of_disjoint u6, Finset.card_union_of_disjoint u5, u4]

/-- Fast independence of a 5-way pairwise non-close union. -/
theorem isIndepSet_union5 {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {A0 A1 A2 A3 A4 : Finset V}
    (i0 : G.IsIndepSet (A0 : Set V)) (i1 : G.IsIndepSet (A1 : Set V))
    (i2 : G.IsIndepSet (A2 : Set V)) (i3 : G.IsIndepSet (A3 : Set V))
    (i4 : G.IsIndepSet (A4 : Set V))
    (h01 : ∀ x ∈ A0, ∀ y ∈ A1, ¬ (x = y ∨ G.Adj x y))
    (h02 : ∀ x ∈ A0, ∀ y ∈ A2, ¬ (x = y ∨ G.Adj x y))
    (h03 : ∀ x ∈ A0, ∀ y ∈ A3, ¬ (x = y ∨ G.Adj x y))
    (h04 : ∀ x ∈ A0, ∀ y ∈ A4, ¬ (x = y ∨ G.Adj x y))
    (h12 : ∀ x ∈ A1, ∀ y ∈ A2, ¬ (x = y ∨ G.Adj x y))
    (h13 : ∀ x ∈ A1, ∀ y ∈ A3, ¬ (x = y ∨ G.Adj x y))
    (h14 : ∀ x ∈ A1, ∀ y ∈ A4, ¬ (x = y ∨ G.Adj x y))
    (h23 : ∀ x ∈ A2, ∀ y ∈ A3, ¬ (x = y ∨ G.Adj x y))
    (h24 : ∀ x ∈ A2, ∀ y ∈ A4, ¬ (x = y ∨ G.Adj x y))
    (h34 : ∀ x ∈ A3, ∀ y ∈ A4, ¬ (x = y ∨ G.Adj x y)) :
    G.IsIndepSet ((A0 ∪ A1 ∪ A2 ∪ A3 ∪ A4 : Finset V) : Set V) := by
  have hi01 := isIndepSet_union_of_not_close i0 i1 h01
  have hi012 := isIndepSet_union_of_not_close hi01 i2 fun x hx y hy => by
    rcases Finset.mem_union.mp hx with h | h; exact h02 x h y hy; exact h12 x h y hy
  have hi0123 := isIndepSet_union_of_not_close hi012 i3 fun x hx y hy => by
    simp only [Finset.mem_union] at hx
    rcases hx with (h | h) | h
    · exact h03 x h y hy
    · exact h13 x h y hy
    · exact h23 x h y hy
  exact isIndepSet_union_of_not_close hi0123 i4 fun x hx y hy => by
    simp only [Finset.mem_union] at hx
    rcases hx with ((h | h) | h) | h
    · exact h04 x h y hy
    · exact h14 x h y hy
    · exact h24 x h y hy
    · exact h34 x h y hy

/-- Fast independence of a 7-way pairwise non-close union. -/
theorem isIndepSet_union7 {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {A0 A1 A2 A3 A4 A5 A6 : Finset V}
    (i0 : G.IsIndepSet (A0 : Set V)) (i1 : G.IsIndepSet (A1 : Set V))
    (i2 : G.IsIndepSet (A2 : Set V)) (i3 : G.IsIndepSet (A3 : Set V))
    (i4 : G.IsIndepSet (A4 : Set V)) (i5 : G.IsIndepSet (A5 : Set V))
    (i6 : G.IsIndepSet (A6 : Set V))
    (h01 : ∀ x ∈ A0, ∀ y ∈ A1, ¬ (x = y ∨ G.Adj x y))
    (h02 : ∀ x ∈ A0, ∀ y ∈ A2, ¬ (x = y ∨ G.Adj x y))
    (h03 : ∀ x ∈ A0, ∀ y ∈ A3, ¬ (x = y ∨ G.Adj x y))
    (h04 : ∀ x ∈ A0, ∀ y ∈ A4, ¬ (x = y ∨ G.Adj x y))
    (h05 : ∀ x ∈ A0, ∀ y ∈ A5, ¬ (x = y ∨ G.Adj x y))
    (h06 : ∀ x ∈ A0, ∀ y ∈ A6, ¬ (x = y ∨ G.Adj x y))
    (h12 : ∀ x ∈ A1, ∀ y ∈ A2, ¬ (x = y ∨ G.Adj x y))
    (h13 : ∀ x ∈ A1, ∀ y ∈ A3, ¬ (x = y ∨ G.Adj x y))
    (h14 : ∀ x ∈ A1, ∀ y ∈ A4, ¬ (x = y ∨ G.Adj x y))
    (h15 : ∀ x ∈ A1, ∀ y ∈ A5, ¬ (x = y ∨ G.Adj x y))
    (h16 : ∀ x ∈ A1, ∀ y ∈ A6, ¬ (x = y ∨ G.Adj x y))
    (h23 : ∀ x ∈ A2, ∀ y ∈ A3, ¬ (x = y ∨ G.Adj x y))
    (h24 : ∀ x ∈ A2, ∀ y ∈ A4, ¬ (x = y ∨ G.Adj x y))
    (h25 : ∀ x ∈ A2, ∀ y ∈ A5, ¬ (x = y ∨ G.Adj x y))
    (h26 : ∀ x ∈ A2, ∀ y ∈ A6, ¬ (x = y ∨ G.Adj x y))
    (h34 : ∀ x ∈ A3, ∀ y ∈ A4, ¬ (x = y ∨ G.Adj x y))
    (h35 : ∀ x ∈ A3, ∀ y ∈ A5, ¬ (x = y ∨ G.Adj x y))
    (h36 : ∀ x ∈ A3, ∀ y ∈ A6, ¬ (x = y ∨ G.Adj x y))
    (h45 : ∀ x ∈ A4, ∀ y ∈ A5, ¬ (x = y ∨ G.Adj x y))
    (h46 : ∀ x ∈ A4, ∀ y ∈ A6, ¬ (x = y ∨ G.Adj x y))
    (h56 : ∀ x ∈ A5, ∀ y ∈ A6, ¬ (x = y ∨ G.Adj x y)) :
    G.IsIndepSet ((A0 ∪ A1 ∪ A2 ∪ A3 ∪ A4 ∪ A5 ∪ A6 : Finset V) : Set V) := by
  have hi04 := isIndepSet_union5 i0 i1 i2 i3 i4 h01 h02 h03 h04 h12 h13 h14 h23 h24 h34
  have hi05 := isIndepSet_union_of_not_close hi04 i5 fun x hx y hy => by
    simp only [Finset.mem_union] at hx
    rcases hx with (((h | h) | h) | h) | h
    · exact h05 x h y hy
    · exact h15 x h y hy
    · exact h25 x h y hy
    · exact h35 x h y hy
    · exact h45 x h y hy
  exact isIndepSet_union_of_not_close hi05 i6 fun x hx y hy => by
    simp only [Finset.mem_union] at hx
    rcases hx with ((((h | h) | h) | h) | h) | h
    · exact h06 x h y hy
    · exact h16 x h y hy
    · exact h26 x h y hy
    · exact h36 x h y hy
    · exact h46 x h y hy
    · exact h56 x h y hy

/-! ============================================================================
    PART 1: `PortCore`, `AuxCode`, `AsymProfile`, `HeteroGadget`,
            `HeteroTree`, `HeteroDAG`, & Root-Level Terminal Substitution
    ============================================================================ -/

set_option linter.unusedFintypeInType false in
/-- Decoupled main independent set `(I, S, f0, f1)` carrying binary private ports,
independent of any auxiliary code `X`. A single `PortCore` can pair with an entire
Pareto portfolio of auxiliary sets `AuxCode core`. -/
structure PortCore {V : Type*} [Fintype V] (G : SimpleGraph V) where
  I : Finset V
  S : Finset V
  f0 : V → V
  f1 : V → V
  indep_I : G.IsIndepSet (I : Set V)
  S_sub_I : S ⊆ I
  priv0 : ∀ s ∈ S, (f0 s = s ∨ G.Adj (f0 s) s) ∧ ∀ u ∈ I, (u = f0 s ∨ G.Adj u (f0 s)) → u = s
  priv1 : ∀ s ∈ S, (f1 s = s ∨ G.Adj (f1 s) s) ∧ ∀ u ∈ I, (u = f1 s ∨ G.Adj u (f1 s)) → u = s
  indep_P0 : G.IsIndepSet (f0 '' (S : Set V))
  indep_P1 : G.IsIndepSet (f1 '' (S : Set V))
  self_mem : ∀ s ∈ S, f0 s = s ∨ f1 s = s

namespace PortCore

variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

def inP0Nbr (c : PortCore G) (x : V) : Prop :=
  ∃ s ∈ c.S, c.f0 s = x ∨ G.Adj (c.f0 s) x

def inP1Nbr (c : PortCore G) (x : V) : Prop :=
  ∃ s ∈ c.S, c.f1 s = x ∨ G.Adj (c.f1 s) x

noncomputable def B (c : PortCore G) : Finset V := by
  classical exact c.I \ c.S

noncomputable def P0 (c : PortCore G) : Finset V := by
  classical exact c.S.image c.f0

noncomputable def P1 (c : PortCore G) : Finset V := by
  classical exact c.S.image c.f1

theorem card_S_le_I (c : PortCore G) : c.S.card ≤ c.I.card :=
  Finset.card_le_card c.S_sub_I

theorem card_B (c : PortCore G) : c.B.card = c.I.card - c.S.card := by
  classical exact card_sdiff_eq c.S_sub_I

theorem mem_B (c : PortCore G) {x : V} : x ∈ c.B ↔ x ∈ c.I ∧ x ∉ c.S := by
  classical simp [B]

theorem mem_P0 (c : PortCore G) {x : V} : x ∈ c.P0 ↔ ∃ s ∈ c.S, c.f0 s = x := by
  classical simp [P0]

theorem mem_P1 (c : PortCore G) {x : V} : x ∈ c.P1 ↔ ∃ s ∈ c.S, c.f1 s = x := by
  classical simp [P1]

theorem injOn_f0 (c : PortCore G) : Set.InjOn c.f0 (c.S : Set V) := by
  intro s₁ hs₁ s₂ hs₂ heq
  have hclose : s₁ = c.f0 s₂ ∨ G.Adj s₁ (c.f0 s₂) := by
    rw [← heq]; exact close_symm (c.priv0 s₁ hs₁).1
  exact (c.priv0 s₂ hs₂).2 s₁ (c.S_sub_I hs₁) hclose

theorem injOn_f1 (c : PortCore G) : Set.InjOn c.f1 (c.S : Set V) := by
  intro s₁ hs₁ s₂ hs₂ heq
  have hclose : s₁ = c.f1 s₂ ∨ G.Adj s₁ (c.f1 s₂) := by
    rw [← heq]; exact close_symm (c.priv1 s₁ hs₁).1
  exact (c.priv1 s₂ hs₂).2 s₁ (c.S_sub_I hs₁) hclose

theorem card_P0 (c : PortCore G) : c.P0.card = c.S.card := by
  classical exact Finset.card_image_of_injOn c.injOn_f0

theorem card_P1 (c : PortCore G) : c.P1.card = c.S.card := by
  classical exact Finset.card_image_of_injOn c.injOn_f1

theorem indep_B (c : PortCore G) : G.IsIndepSet (c.B : Set V) :=
  isIndepSet_subset c.indep_I (fun _ hx => (c.mem_B.mp hx).1)

theorem indep_S (c : PortCore G) : G.IsIndepSet (c.S : Set V) :=
  isIndepSet_subset c.indep_I c.S_sub_I

theorem indep_P0_finset (c : PortCore G) : G.IsIndepSet (c.P0 : Set V) := by
  intro x hx y hy hne hadj
  rcases c.mem_P0.mp hx with ⟨s₁, hs₁, rfl⟩
  rcases c.mem_P0.mp hy with ⟨s₂, hs₂, rfl⟩
  exact c.indep_P0 ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, rfl⟩ hne hadj

theorem indep_P1_finset (c : PortCore G) : G.IsIndepSet (c.P1 : Set V) := by
  intro x hx y hy hne hadj
  rcases c.mem_P1.mp hx with ⟨s₁, hs₁, rfl⟩
  rcases c.mem_P1.mp hy with ⟨s₂, hs₂, rfl⟩
  exact c.indep_P1 ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, rfl⟩ hne hadj

theorem not_close_B_S (c : PortCore G) {b s : V} (hb : b ∈ c.B) (hs : s ∈ c.S) :
    ¬ (b = s ∨ G.Adj b s) := by
  have hb' := c.mem_B.mp hb
  exact isIndepSet_not_close_of_ne c.indep_I hb'.1 (c.S_sub_I hs) (fun h => hb'.2 (h ▸ hs))

theorem not_close_B_P0 (c : PortCore G) {b p : V} (hb : b ∈ c.B) (hp : p ∈ c.P0) :
    ¬ (b = p ∨ G.Adj b p) := by
  have hb' := c.mem_B.mp hb
  rcases c.mem_P0.mp hp with ⟨s, hs, rfl⟩
  intro hc
  exact hb'.2 (((c.priv0 s hs).2 b hb'.1 hc) ▸ hs)

theorem not_close_B_P1 (c : PortCore G) {b p : V} (hb : b ∈ c.B) (hp : p ∈ c.P1) :
    ¬ (b = p ∨ G.Adj b p) := by
  have hb' := c.mem_B.mp hb
  rcases c.mem_P1.mp hp with ⟨s, hs, rfl⟩
  intro hc
  exact hb'.2 (((c.priv1 s hs).2 b hb'.1 hc) ▸ hs)

theorem inP0Nbr_iff_mem_P0 (c : PortCore G) (x : V) :
    c.inP0Nbr x ↔ ∃ p ∈ c.P0, p = x ∨ G.Adj p x := by
  constructor
  · rintro ⟨s, hs, hc⟩; exact ⟨c.f0 s, c.mem_P0.mpr ⟨s, hs, rfl⟩, hc⟩
  · rintro ⟨p, hp, hc⟩; rcases c.mem_P0.mp hp with ⟨s, hs, rfl⟩; exact ⟨s, hs, hc⟩

theorem inP1Nbr_iff_mem_P1 (c : PortCore G) (x : V) :
    c.inP1Nbr x ↔ ∃ p ∈ c.P1, p = x ∨ G.Adj p x := by
  constructor
  · rintro ⟨s, hs, hc⟩; exact ⟨c.f1 s, c.mem_P1.mpr ⟨s, hs, rfl⟩, hc⟩
  · rintro ⟨p, hp, hc⟩; rcases c.mem_P1.mp hp with ⟨s, hs, rfl⟩; exact ⟨s, hs, hc⟩

def flip (c : PortCore G) : PortCore G where
  I := c.I; S := c.S; f0 := c.f1; f1 := c.f0
  indep_I := c.indep_I; S_sub_I := c.S_sub_I
  priv0 := c.priv1; priv1 := c.priv0
  indep_P0 := c.indep_P1; indep_P1 := c.indep_P0
  self_mem := fun s hs => (c.self_mem s hs).symm

def restrictS (c : PortCore G) (S' : Finset V) (hS' : S' ⊆ c.S) : PortCore G where
  I := c.I; S := S'; f0 := c.f0; f1 := c.f1
  indep_I := c.indep_I; S_sub_I := hS'.trans c.S_sub_I
  priv0 := fun s hs => c.priv0 s (hS' hs)
  priv1 := fun s hs => c.priv1 s (hS' hs)
  indep_P0 := by
    rintro x ⟨s₁, hs₁, rfl⟩ y ⟨s₂, hs₂, rfl⟩ hne hadj
    exact c.indep_P0 ⟨s₁, hS' hs₁, rfl⟩ ⟨s₂, hS' hs₂, rfl⟩ hne hadj
  indep_P1 := by
    rintro x ⟨s₁, hs₁, rfl⟩ y ⟨s₂, hs₂, rfl⟩ hne hadj
    exact c.indep_P1 ⟨s₁, hS' hs₁, rfl⟩ ⟨s₂, hS' hs₂, rfl⟩ hne hadj
  self_mem := fun s hs => c.self_mem s (hS' hs)

def mapIso (e : G ≃g H) (c : PortCore G) : PortCore H where
  I := c.I.map e.toEquiv.toEmbedding
  S := c.S.map e.toEquiv.toEmbedding
  f0 := fun w => e (c.f0 (e.symm w))
  f1 := fun w => e (c.f1 (e.symm w))
  indep_I := isIndepSet_map_iso e c.indep_I
  S_sub_I := Finset.map_subset_map.mpr c.S_sub_I
  priv0 := by
    intro w hw
    rcases Finset.mem_map.mp hw with ⟨s, hs, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply]
    refine ⟨(c.priv0 s hs).1.imp (congrArg e) (e.map_adj_iff.mpr), ?_⟩
    intro u hu hc
    rcases Finset.mem_map.mp hu with ⟨v, hv, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv] at hc ⊢
    exact congrArg e ((c.priv0 s hs).2 v hv (hc.imp (fun h => e.injective h) e.map_adj_iff.mp))
  priv1 := by
    intro w hw
    rcases Finset.mem_map.mp hw with ⟨s, hs, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply]
    refine ⟨(c.priv1 s hs).1.imp (congrArg e) (e.map_adj_iff.mpr), ?_⟩
    intro u hu hc
    rcases Finset.mem_map.mp hu with ⟨v, hv, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv] at hc ⊢
    exact congrArg e ((c.priv1 s hs).2 v hv (hc.imp (fun h => e.injective h) e.map_adj_iff.mp))
  indep_P0 := by
    rintro x ⟨w₁, hw₁, rfl⟩ y ⟨w₂, hw₂, rfl⟩ hne hadj
    rcases Finset.mem_map.mp hw₁ with ⟨s₁, hs₁, rfl⟩
    rcases Finset.mem_map.mp hw₂ with ⟨s₂, hs₂, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply] at hne hadj
    exact c.indep_P0 ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, rfl⟩ (fun h => hne (congrArg e h))
      (e.map_adj_iff.mp hadj)
  indep_P1 := by
    rintro x ⟨w₁, hw₁, rfl⟩ y ⟨w₂, hw₂, rfl⟩ hne hadj
    rcases Finset.mem_map.mp hw₁ with ⟨s₁, hs₁, rfl⟩
    rcases Finset.mem_map.mp hw₂ with ⟨s₂, hs₂, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply] at hne hadj
    exact c.indep_P1 ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, rfl⟩ (fun h => hne (congrArg e h))
      (e.map_adj_iff.mp hadj)
  self_mem := by
    intro w hw
    rcases Finset.mem_map.mp hw with ⟨s, hs, rfl⟩
    simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply]
    exact (c.self_mem s hs).imp (congrArg e) (congrArg e)

end PortCore

set_option linter.unusedFintypeInType false in
/-- Auxiliary independent set `X` compatible with a `PortCore G` (avoids `N[P0] ∩ N[P1]`). -/
structure AuxCode {V : Type*} [Fintype V] {G : SimpleGraph V} (core : PortCore G) where
  X : Finset V
  indep_X : G.IsIndepSet (X : Set V)
  disj_nbr : ∀ x ∈ X, ¬ (core.inP0Nbr x ∧ core.inP1Nbr x)

namespace AuxCode

variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

noncomputable def HSlice {core : PortCore G} (aux : AuxCode core) : Finset V := by
  classical exact aux.X.filter (fun x => core.inP0Nbr x)

noncomputable def VSlice {core : PortCore G} (aux : AuxCode core) : Finset V := by
  classical exact aux.X.filter (fun x => core.inP1Nbr x)

noncomputable def OSlice {core : PortCore G} (aux : AuxCode core) : Finset V := by
  classical exact aux.X.filter (fun x => ¬ core.inP0Nbr x ∧ ¬ core.inP1Nbr x)

theorem mem_HSlice {core : PortCore G} (aux : AuxCode core) {x : V} :
    x ∈ aux.HSlice ↔ x ∈ aux.X ∧ core.inP0Nbr x := by
  classical simp [HSlice]

theorem mem_VSlice {core : PortCore G} (aux : AuxCode core) {x : V} :
    x ∈ aux.VSlice ↔ x ∈ aux.X ∧ core.inP1Nbr x := by
  classical simp [VSlice]

theorem mem_OSlice {core : PortCore G} (aux : AuxCode core) {x : V} :
    x ∈ aux.OSlice ↔ x ∈ aux.X ∧ ¬ core.inP0Nbr x ∧ ¬ core.inP1Nbr x := by
  classical simp [OSlice]

theorem card_partition {core : PortCore G} (aux : AuxCode core) :
    aux.OSlice.card + aux.HSlice.card + aux.VSlice.card = aux.X.card := by
  classical
  have hdisj_OH : Disjoint aux.OSlice aux.HSlice := by
    rw [Finset.disjoint_left]; intro x hO hH
    exact (aux.mem_OSlice.mp hO).2.1 (aux.mem_HSlice.mp hH).2
  have hdisj_OH_V : Disjoint (aux.OSlice ∪ aux.HSlice) aux.VSlice := by
    rw [Finset.disjoint_left]; intro x hOH hV
    have hV' := aux.mem_VSlice.mp hV
    rcases Finset.mem_union.mp hOH with hO | hH
    · exact (aux.mem_OSlice.mp hO).2.2 hV'.2
    · exact aux.disj_nbr x hV'.1 ⟨(aux.mem_HSlice.mp hH).2, hV'.2⟩
  have hunion : aux.OSlice ∪ aux.HSlice ∪ aux.VSlice = aux.X := by
    ext x
    simp only [Finset.mem_union, aux.mem_OSlice, aux.mem_HSlice, aux.mem_VSlice]
    by_cases hx : x ∈ aux.X
    · by_cases h0 : core.inP0Nbr x <;> by_cases h1 : core.inP1Nbr x <;> simp [hx, h0, h1]
    · simp [hx]
  rw [← Finset.card_union_of_disjoint hdisj_OH, ← Finset.card_union_of_disjoint hdisj_OH_V, hunion]

def flip {core : PortCore G} (aux : AuxCode core) : AuxCode core.flip where
  X := aux.X; indep_X := aux.indep_X
  disj_nbr := fun x hx ⟨h0, h1⟩ => aux.disj_nbr x hx ⟨h1, h0⟩

def restrictS {core : PortCore G} (aux : AuxCode core) (S' : Finset V) (hS' : S' ⊆ core.S) :
    AuxCode (core.restrictS S' hS') where
  X := aux.X; indep_X := aux.indep_X
  disj_nbr := by
    intro x hx ⟨⟨s₀, hs₀, h0⟩, ⟨s₁, hs₁, h1⟩⟩
    exact aux.disj_nbr x hx ⟨⟨s₀, hS' hs₀, h0⟩, ⟨s₁, hS' hs₁, h1⟩⟩

def mapIso (e : G ≃g H) {core : PortCore G} (aux : AuxCode core) : AuxCode (core.mapIso e) where
  X := aux.X.map e.toEquiv.toEmbedding
  indep_X := isIndepSet_map_iso e aux.indep_X
  disj_nbr := by
    intro y hy ⟨⟨w₀, hw₀, h0⟩, ⟨w₁, hw₁, h1⟩⟩
    rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp hw₀ with ⟨s₀, hs₀, rfl⟩
    rcases Finset.mem_map.mp hw₁ with ⟨s₁, hs₁, rfl⟩
    simp only [PortCore.mapIso, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
      RelIso.symm_apply_apply] at h0 h1
    exact aux.disj_nbr x hx
      ⟨⟨s₀, hs₀, h0.imp (fun h => e.injective h) e.map_adj_iff.mp⟩,
       ⟨s₁, hs₁, h1.imp (fun h => e.injective h) e.map_adj_iff.mp⟩⟩

end AuxCode

/-- Exact 6-parameter asymmetric profile `(a, b, c, d, h, v)` tracking `|H|` and `|V|`
separately with `b ≤ a` and `d + h + v = c`. -/
structure AsymProfile where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  h : ℕ
  v : ℕ
  hba : b ≤ a
  hdhv : d + h + v = c
  deriving DecidableEq

namespace AsymProfile

theorem hdc (p : AsymProfile) : p.d ≤ p.c := by
  have := p.hdhv; omega

def toProfile (p : AsymProfile) : Profile where
  a := p.a; b := p.b; c := p.c; d := p.d; hba := p.hba; hdc := p.hdc

def flip (p : AsymProfile) : AsymProfile where
  a := p.a; b := p.b; c := p.c; d := p.d; h := p.v; v := p.h; hba := p.hba
  hdhv := by have := p.hdhv; omega

def prod (p q : AsymProfile) : AsymProfile where
  a := (p.a - p.b) * (q.a - q.b) + p.b * q.c + p.c * q.b
  b := p.b * q.d + p.d * q.b
  c := p.c * q.c
  d := p.d * q.d + (p.h + p.v) * (q.h + q.v)
  h := p.h * q.d + p.d * q.v
  v := p.v * q.d + p.d * q.h
  hba := by
    have h1 : p.b * q.d ≤ p.b * q.c := Nat.mul_le_mul_left p.b q.hdc
    have h2 : p.d * q.b ≤ p.c * q.b := Nat.mul_le_mul_right q.b p.hdc
    omega
  hdhv := by
    have hp := p.hdhv; have hq := q.hdhv; nlinarith

def prodAligned (p q : AsymProfile) : AsymProfile := p.prod q.flip

theorem prodAligned_eq (p q : AsymProfile) :
    (p.prodAligned q).a = (p.a - p.b) * (q.a - q.b) + p.b * q.c + p.c * q.b ∧
    (p.prodAligned q).b = p.b * q.d + p.d * q.b ∧
    (p.prodAligned q).c = p.c * q.c ∧
    (p.prodAligned q).d = p.d * q.d + (p.h + p.v) * (q.h + q.v) ∧
    (p.prodAligned q).h = p.h * q.d + p.d * q.h ∧
    (p.prodAligned q).v = p.v * q.d + p.d * q.v := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl⟩
  simp only [prodAligned, prod, flip, add_comm q.v q.h]

theorem prod_toProfile (p q : AsymProfile) :
    (p.prod q).toProfile = p.toProfile.star q.toProfile := by
  have hp : p.h + p.v = p.c - p.d := by have := p.hdhv; omega
  have hq : q.h + q.v = q.c - q.d := by have := q.hdhv; omega
  apply Profile.ext
  · show (p.a - p.b) * (q.a - q.b) + p.b * q.c + p.c * q.b =
        (p.a - p.b) * (q.a - q.b) + p.c * q.b + p.b * q.c
    omega
  · show p.b * q.d + p.d * q.b = p.d * q.b + p.b * q.d
    omega
  · rfl
  · show p.d * q.d + (p.h + p.v) * (q.h + q.v) = p.d * q.d + (p.c - p.d) * (q.c - q.d)
    rw [hp, hq]

def terminalSize (p q : AsymProfile) : ℕ :=
  (p.a - p.b) * (q.a - q.b) + p.b * q.c + p.c * q.b

end AsymProfile

set_option linter.unusedFintypeInType false in
/-- A heterogeneous gadget pairing a `PortCore G` with an `AuxCode core`. -/
structure HeteroGadget {V : Type*} [Fintype V] (G : SimpleGraph V) where
  core : PortCore G
  aux : AuxCode core

/-- Convert a homogeneous `ValidTuple G` into a `HeteroGadget G`. -/
def ValidTuple.toHeteroGadget {V : Type*} [Fintype V] {G : SimpleGraph V}
    (τ : ValidTuple G) : HeteroGadget G where
  core :=
    { I := τ.I, S := τ.S, f0 := τ.f0, f1 := τ.f1
      indep_I := τ.indep_I, S_sub_I := τ.sub_S
      priv0 := τ.priv0, priv1 := τ.priv1
      indep_P0 := τ.indep_P0, indep_P1 := τ.indep_P1
      self_mem := τ.self_mem }
  aux :=
    { X := τ.X, indep_X := τ.indep_X
      disj_nbr := by
        intro x hx ⟨⟨s₀, hs₀, h0⟩, ⟨s₁, hs₁, h1⟩⟩
        exact τ.disj_nbr x hx ⟨⟨s₀, hs₀, close_symm h0⟩, ⟨s₁, hs₁, close_symm h1⟩⟩ }

/-- Convert a `HeteroGadget G` back into a homogeneous `ValidTuple G`. -/
def HeteroGadget.toValidTuple {V : Type*} [Fintype V] {G : SimpleGraph V}
    (g : HeteroGadget G) : ValidTuple G where
  I := g.core.I; S := g.core.S; f0 := g.core.f0; f1 := g.core.f1; X := g.aux.X
  indep_I := g.core.indep_I; sub_S := g.core.S_sub_I
  self_mem := g.core.self_mem
  priv0 := g.core.priv0; priv1 := g.core.priv1
  indep_P0 := g.core.indep_P0; indep_P1 := g.core.indep_P1
  indep_X := g.aux.indep_X
  disj_nbr := by
    intro x hx ⟨⟨s₀, hs₀, h0⟩, ⟨s₁, hs₁, h1⟩⟩
    exact g.aux.disj_nbr x hx ⟨⟨s₀, hs₀, close_symm h0⟩, ⟨s₁, hs₁, close_symm h1⟩⟩

namespace HeteroGadget

variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

noncomputable def asymProfile (g : HeteroGadget G) : AsymProfile where
  a := g.core.I.card
  b := g.core.S.card
  c := g.aux.X.card
  d := g.aux.OSlice.card
  h := g.aux.HSlice.card
  v := g.aux.VSlice.card
  hba := g.core.card_S_le_I
  hdhv := g.aux.card_partition

theorem card_le_indepNum (g : HeteroGadget G) : g.asymProfile.a ≤ G.indepNum :=
  g.core.indep_I.card_le_indepNum

def flip (g : HeteroGadget G) : HeteroGadget G where
  core := g.core.flip; aux := g.aux.flip

theorem flip_asymProfile (g : HeteroGadget G) : g.flip.asymProfile = g.asymProfile.flip := by
  classical
  have hO : g.flip.aux.OSlice = g.aux.OSlice := by
    ext x
    simp [AuxCode.mem_OSlice, flip, PortCore.flip, AuxCode.flip, PortCore.inP0Nbr, PortCore.inP1Nbr,
      and_comm]
  have hH : g.flip.aux.HSlice = g.aux.VSlice := by
    ext x
    simp [AuxCode.mem_HSlice, AuxCode.mem_VSlice, flip, PortCore.flip, AuxCode.flip,
      PortCore.inP0Nbr, PortCore.inP1Nbr]
  have hV : g.flip.aux.VSlice = g.aux.HSlice := by
    ext x
    simp [AuxCode.mem_HSlice, AuxCode.mem_VSlice, flip, PortCore.flip, AuxCode.flip,
      PortCore.inP0Nbr, PortCore.inP1Nbr]
  cases g
  simp only [asymProfile, AsymProfile.flip, hO, hH, hV]
  rfl

def withAux (g : HeteroGadget G) (aux' : AuxCode g.core) : HeteroGadget G where
  core := g.core; aux := aux'

def mapIso (e : G ≃g H) (g : HeteroGadget G) : HeteroGadget H where
  core := g.core.mapIso e; aux := g.aux.mapIso e

theorem mapIso_asymProfile (e : G ≃g H) (g : HeteroGadget G) :
    (g.mapIso e).asymProfile = g.asymProfile := by
  classical
  have hin0 : ∀ x, (g.core.mapIso e).inP0Nbr (e x) ↔ g.core.inP0Nbr x := by
    intro x
    constructor
    · rintro ⟨w, hw, hc⟩
      rcases Finset.mem_map.mp hw with ⟨s, hs, rfl⟩
      simp only [PortCore.mapIso, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
        RelIso.symm_apply_apply] at hc
      exact ⟨s, hs, hc.imp (fun h => e.injective h) e.map_adj_iff.mp⟩
    · rintro ⟨s, hs, hc⟩
      refine ⟨e s, Finset.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
      simp only [PortCore.mapIso, RelIso.symm_apply_apply]
      exact hc.imp (congrArg e) e.map_adj_iff.mpr
  have hin1 : ∀ x, (g.core.mapIso e).inP1Nbr (e x) ↔ g.core.inP1Nbr x := by
    intro x
    constructor
    · rintro ⟨w, hw, hc⟩
      rcases Finset.mem_map.mp hw with ⟨s, hs, rfl⟩
      simp only [PortCore.mapIso, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
        RelIso.symm_apply_apply] at hc
      exact ⟨s, hs, hc.imp (fun h => e.injective h) e.map_adj_iff.mp⟩
    · rintro ⟨s, hs, hc⟩
      refine ⟨e s, Finset.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
      simp only [PortCore.mapIso, RelIso.symm_apply_apply]
      exact hc.imp (congrArg e) e.map_adj_iff.mpr
  have hmem : ∀ x, e x ∈ (g.aux.mapIso e).X ↔ x ∈ g.aux.X := fun x =>
    ⟨fun h => by
      rcases Finset.mem_map.mp h with ⟨x', hx', he⟩
      exact e.injective he ▸ hx',
     fun hx => Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hO : (g.mapIso e).aux.OSlice = g.aux.OSlice.map e.toEquiv.toEmbedding := by
    ext y; obtain ⟨x, rfl⟩ := e.surjective y
    simp only [AuxCode.mem_OSlice, mapIso, hmem, hin0, hin1, Finset.mem_map,
      Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv]
    exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨x', hx', hxx⟩ => (e.injective hxx) ▸ hx'⟩
  have hH : (g.mapIso e).aux.HSlice = g.aux.HSlice.map e.toEquiv.toEmbedding := by
    ext y; obtain ⟨x, rfl⟩ := e.surjective y
    simp only [AuxCode.mem_HSlice, mapIso, hmem, hin0, Finset.mem_map,
      Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv]
    exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨x', hx', hxx⟩ => (e.injective hxx) ▸ hx'⟩
  have hV : (g.mapIso e).aux.VSlice = g.aux.VSlice.map e.toEquiv.toEmbedding := by
    ext y; obtain ⟨x, rfl⟩ := e.surjective y
    simp only [AuxCode.mem_VSlice, mapIso, hmem, hin1, Finset.mem_map,
      Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv]
    exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨x', hx', hxx⟩ => (e.injective hxx) ▸ hx'⟩
  have hI : (g.mapIso e).core.I.card = g.core.I.card := Finset.card_map _
  have hS : (g.mapIso e).core.S.card = g.core.S.card := Finset.card_map _
  have hX : (g.mapIso e).aux.X.card = g.aux.X.card := Finset.card_map _
  have hOc : (g.mapIso e).aux.OSlice.card = g.aux.OSlice.card := by rw [hO, Finset.card_map]
  have hHc : (g.mapIso e).aux.HSlice.card = g.aux.HSlice.card := by rw [hH, Finset.card_map]
  have hVc : (g.mapIso e).aux.VSlice.card = g.aux.VSlice.card := by rw [hV, Finset.card_map]
  cases g
  simp only [asymProfile, AsymProfile.mk.injEq]
  exact ⟨hI, hS, hX, hOc, hHc, hVc⟩

/-! ### Shared Non-Close Lemmas & `prodI` (Zero Duplication!) -/

theorem not_close_S_OSlice (g : HeteroGadget G) {s o : V}
    (hs : s ∈ g.core.S) (ho : o ∈ g.aux.OSlice) : ¬ (s = o ∨ G.Adj s o) := by
  have ho' := g.aux.mem_OSlice.mp ho
  rcases g.core.self_mem s hs with h0 | h1
  · exact fun hc => ho'.2.1 ⟨s, hs, h0.symm ▸ hc⟩
  · exact fun hc => ho'.2.2 ⟨s, hs, h1.symm ▸ hc⟩

theorem not_mem_S_of_mem_OSlice (g : HeteroGadget G) {x : V}
    (hx : x ∈ g.aux.OSlice) : x ∉ g.core.S :=
  fun hs => not_close_S_OSlice g hs hx (Or.inl rfl)

theorem not_close_P0_OSlice (g : HeteroGadget G) {p o : V}
    (hp : p ∈ g.core.P0) (ho : o ∈ g.aux.OSlice) : ¬ (p = o ∨ G.Adj p o) :=
  fun hc => (g.aux.mem_OSlice.mp ho).2.1 ((g.core.inP0Nbr_iff_mem_P0 o).mpr ⟨p, hp, hc⟩)

theorem not_close_P1_OSlice (g : HeteroGadget G) {p o : V}
    (hp : p ∈ g.core.P1) (ho : o ∈ g.aux.OSlice) : ¬ (p = o ∨ G.Adj p o) :=
  fun hc => (g.aux.mem_OSlice.mp ho).2.2 ((g.core.inP1Nbr_iff_mem_P1 o).mpr ⟨p, hp, hc⟩)

theorem not_close_P0_VSlice (g : HeteroGadget G) {p v : V}
    (hp : p ∈ g.core.P0) (hv : v ∈ g.aux.VSlice) : ¬ (p = v ∨ G.Adj p v) :=
  fun hc => g.aux.disj_nbr v (g.aux.mem_VSlice.mp hv).1
    ⟨(g.core.inP0Nbr_iff_mem_P0 v).mpr ⟨p, hp, hc⟩, (g.aux.mem_VSlice.mp hv).2⟩

theorem not_close_P1_HSlice (g : HeteroGadget G) {p h : V}
    (hp : p ∈ g.core.P1) (hh : h ∈ g.aux.HSlice) : ¬ (p = h ∨ G.Adj p h) :=
  fun hc => g.aux.disj_nbr h (g.aux.mem_HSlice.mp hh).1
    ⟨(g.aux.mem_HSlice.mp hh).2, (g.core.inP1Nbr_iff_mem_P1 h).mpr ⟨p, hp, hc⟩⟩

theorem not_close_OSlice_HSlice (g : HeteroGadget G) {o h : V}
    (ho : o ∈ g.aux.OSlice) (hh : h ∈ g.aux.HSlice) : ¬ (o = h ∨ G.Adj o h) :=
  isIndepSet_not_close_of_ne g.aux.indep_X (g.aux.mem_OSlice.mp ho).1 (g.aux.mem_HSlice.mp hh).1
    (fun heq => (g.aux.mem_OSlice.mp ho).2.1 (heq ▸ (g.aux.mem_HSlice.mp hh).2))

theorem not_close_OSlice_VSlice (g : HeteroGadget G) {o v : V}
    (ho : o ∈ g.aux.OSlice) (hv : v ∈ g.aux.VSlice) : ¬ (o = v ∨ G.Adj o v) :=
  isIndepSet_not_close_of_ne g.aux.indep_X (g.aux.mem_OSlice.mp ho).1 (g.aux.mem_VSlice.mp hv).1
    (fun heq => (g.aux.mem_OSlice.mp ho).2.2 (heq ▸ (g.aux.mem_VSlice.mp hv).2))

theorem not_close_HSlice_VSlice (g : HeteroGadget G) {h v : V}
    (hh : h ∈ g.aux.HSlice) (hv : v ∈ g.aux.VSlice) : ¬ (h = v ∨ G.Adj h v) :=
  isIndepSet_not_close_of_ne g.aux.indep_X (g.aux.mem_HSlice.mp hh).1 (g.aux.mem_VSlice.mp hv).1
    (fun heq => g.aux.disj_nbr h (g.aux.mem_HSlice.mp hh).1
      ⟨(g.aux.mem_HSlice.mp hh).2, heq ▸ (g.aux.mem_VSlice.mp hv).2⟩)

/-- The 7-piece main independent set of `g1.prod g2` (also used for terminal substitution
and layered interior upgrading!). -/
noncomputable def prodI (g1 : HeteroGadget G) (g2 : HeteroGadget H) : Finset (V × W) := by
  classical
  exact
    (g1.core.B ×ˢ g2.core.B) ∪
    (g1.core.S ×ˢ g2.aux.OSlice) ∪
    (g1.core.P0 ×ˢ g2.aux.HSlice) ∪
    (g1.core.P1 ×ˢ g2.aux.VSlice) ∪
    (g1.aux.OSlice ×ˢ g2.core.S) ∪
    (g1.aux.HSlice ×ˢ g2.core.P1) ∪
    (g1.aux.VSlice ×ˢ g2.core.P0)

/-- Single master theorem proving BOTH independence of `prodI` AND exact filtered cardinality
across all 7 pieces (eliminating all duplicated 21-pair proofs!). -/
theorem prodI_indep_and_filter (g1 : HeteroGadget G) (g2 : HeteroGadget H) :
    (G ⊠ H).IsIndepSet ((prodI g1 g2 : Finset (V × W)) : Set (V × W)) ∧
    ∀ (P : V × W → Prop) [DecidablePred P],
      ((prodI g1 g2).filter P).card =
        ((g1.core.B ×ˢ g2.core.B).filter P).card +
        ((g1.core.S ×ˢ g2.aux.OSlice).filter P).card +
        ((g1.core.P0 ×ˢ g2.aux.HSlice).filter P).card +
        ((g1.core.P1 ×ˢ g2.aux.VSlice).filter P).card +
        ((g1.aux.OSlice ×ˢ g2.core.S).filter P).card +
        ((g1.aux.HSlice ×ˢ g2.core.P1).filter P).card +
        ((g1.aux.VSlice ×ˢ g2.core.P0).filter P).card := by
  classical
  let A0 := g1.core.B ×ˢ g2.core.B
  let A1 := g1.core.S ×ˢ g2.aux.OSlice
  let A2 := g1.core.P0 ×ˢ g2.aux.HSlice
  let A3 := g1.core.P1 ×ˢ g2.aux.VSlice
  let A4 := g1.aux.OSlice ×ˢ g2.core.S
  let A5 := g1.aux.HSlice ×ˢ g2.core.P1
  let A6 := g1.aux.VSlice ×ˢ g2.core.P0
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
    exact not_close_prod_snd (g2.core.not_close_B_P1 h₁.2 h₂.2)
  have h06 : ∀ x ∈ A0, ∀ y ∈ A6, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A0, A6, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (g2.core.not_close_B_P0 h₁.2 h₂.2)
  have h12 : ∀ x ∈ A1, ∀ y ∈ A2, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A1, A2, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (not_close_OSlice_HSlice g2 h₁.2 h₂.2)
  have h13 : ∀ x ∈ A1, ∀ y ∈ A3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A1, A3, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (not_close_OSlice_VSlice g2 h₁.2 h₂.2)
  have h14 : ∀ x ∈ A1, ∀ y ∈ A4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A1, A4, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (not_close_S_OSlice g1 h₁.1 h₂.1)
  have h15 : ∀ x ∈ A1, ∀ y ∈ A5, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A1, A5, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (fun hc => not_close_P1_OSlice g2 h₂.2 h₁.2 (close_symm hc))
  have h16 : ∀ x ∈ A1, ∀ y ∈ A6, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A1, A6, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (fun hc => not_close_P0_OSlice g2 h₂.2 h₁.2 (close_symm hc))
  have h23 : ∀ x ∈ A2, ∀ y ∈ A3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A2, A3, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (not_close_HSlice_VSlice g2 h₁.2 h₂.2)
  have h24 : ∀ x ∈ A2, ∀ y ∈ A4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A2, A4, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (not_close_P0_OSlice g1 h₁.1 h₂.1)
  have h25 : ∀ x ∈ A2, ∀ y ∈ A5, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A2, A5, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (fun hc => not_close_P1_HSlice g2 h₂.2 h₁.2 (close_symm hc))
  have h26 : ∀ x ∈ A2, ∀ y ∈ A6, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A2, A6, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (not_close_P0_VSlice g1 h₁.1 h₂.1)
  have h34 : ∀ x ∈ A3, ∀ y ∈ A4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A3, A4, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (not_close_P1_OSlice g1 h₁.1 h₂.1)
  have h35 : ∀ x ∈ A3, ∀ y ∈ A5, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A3, A5, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (not_close_P1_HSlice g1 h₁.1 h₂.1)
  have h36 : ∀ x ∈ A3, ∀ y ∈ A6, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A3, A6, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (fun hc => not_close_P0_VSlice g2 h₂.2 h₁.2 (close_symm hc))
  have h45 : ∀ x ∈ A4, ∀ y ∈ A5, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A4, A5, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (not_close_OSlice_HSlice g1 h₁.1 h₂.1)
  have h46 : ∀ x ∈ A4, ∀ y ∈ A6, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A4, A6, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (not_close_OSlice_VSlice g1 h₁.1 h₂.1)
  have h56 : ∀ x ∈ A5, ∀ y ∈ A6, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [A5, A6, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (not_close_HSlice_VSlice g1 h₁.1 h₂.1)
  refine ⟨?_, ?_⟩
  · exact isIndepSet_union7
      (isIndepSet_prod g1.core.indep_B g2.core.indep_B)
      (isIndepSet_prod g1.core.indep_S (isIndepSet_subset g2.aux.indep_X (fun _ hx => (g2.aux.mem_OSlice.mp hx).1)))
      (isIndepSet_prod g1.core.indep_P0_finset (isIndepSet_subset g2.aux.indep_X (fun _ hx => (g2.aux.mem_HSlice.mp hx).1)))
      (isIndepSet_prod g1.core.indep_P1_finset (isIndepSet_subset g2.aux.indep_X (fun _ hx => (g2.aux.mem_VSlice.mp hx).1)))
      (isIndepSet_prod (isIndepSet_subset g1.aux.indep_X (fun _ hx => (g1.aux.mem_OSlice.mp hx).1)) g2.core.indep_S)
      (isIndepSet_prod (isIndepSet_subset g1.aux.indep_X (fun _ hx => (g1.aux.mem_HSlice.mp hx).1)) g2.core.indep_P1_finset)
      (isIndepSet_prod (isIndepSet_subset g1.aux.indep_X (fun _ hx => (g1.aux.mem_VSlice.mp hx).1)) g2.core.indep_P0_finset)
      h01 h02 h03 h04 h05 h06 h12 h13 h14 h15 h16 h23 h24 h25 h26 h34 h35 h36 h45 h46 h56
  · intro P _
    have hpeq : prodI g1 g2 = A0 ∪ A1 ∪ A2 ∪ A3 ∪ A4 ∪ A5 ∪ A6 := rfl
    rw [hpeq]
    simp only [Finset.filter_union]
    have df : ∀ {X Y : Finset (V × W)},
        (∀ x ∈ X, ∀ y ∈ Y, ¬ (x = y ∨ (G ⊠ H).Adj x y)) →
        Disjoint (X.filter P) (Y.filter P) :=
      fun h => Finset.disjoint_filter_filter (disjoint_of_not_close h)
    exact card_union7 (df h01) (df h02) (df h03) (df h04) (df h05) (df h06)
      (df h12) (df h13) (df h14) (df h15) (df h16) (df h23) (df h24) (df h25) (df h26)
      (df h34) (df h35) (df h36) (df h45) (df h46) (df h56)

theorem prodI_isIndepSet (g1 : HeteroGadget G) (g2 : HeteroGadget H) :
    (G ⊠ H).IsIndepSet ((prodI g1 g2 : Finset (V × W)) : Set (V × W)) :=
  (prodI_indep_and_filter g1 g2).1

theorem prodI_card (g1 : HeteroGadget G) (g2 : HeteroGadget H) :
    (prodI g1 g2).card =
      (g1.core.I.card - g1.core.S.card) * (g2.core.I.card - g2.core.S.card) +
      g1.core.S.card * g2.aux.X.card + g1.aux.X.card * g2.core.S.card := by
  have hf := (prodI_indep_and_filter g1 g2).2 (fun _ => True)
  simp only [Finset.filter_true, Finset.card_product,
    g1.core.card_B, g2.core.card_B, g1.core.card_P0, g1.core.card_P1,
    g2.core.card_P0, g2.core.card_P1] at hf
  have hp1 := g1.aux.card_partition
  have hp2 := g2.aux.card_partition
  nlinarith

/-- Root-level two-sided terminal substitution. -/
noncomputable def terminalIndepSet (core₁ : PortCore G) (core₂ : PortCore H)
    (aux₁ : AuxCode core₁) (aux₂ : AuxCode core₂) : Finset (V × W) :=
  prodI ⟨core₁, aux₁⟩ ⟨core₂, aux₂⟩

theorem terminalIndepSet_isIndep (core₁ : PortCore G) (core₂ : PortCore H)
    (aux₁ : AuxCode core₁) (aux₂ : AuxCode core₂) :
    (G ⊠ H).IsIndepSet ((terminalIndepSet core₁ core₂ aux₁ aux₂ : Finset (V × W)) : Set (V × W)) :=
  prodI_isIndepSet ⟨core₁, aux₁⟩ ⟨core₂, aux₂⟩

theorem terminalIndepSet_card (core₁ : PortCore G) (core₂ : PortCore H)
    (aux₁ : AuxCode core₁) (aux₂ : AuxCode core₂) :
    (terminalIndepSet core₁ core₂ aux₁ aux₂).card =
      (core₁.I.card - core₁.S.card) * (core₂.I.card - core₂.S.card) +
      core₁.S.card * aux₂.X.card + aux₁.X.card * core₂.S.card :=
  prodI_card ⟨core₁, aux₁⟩ ⟨core₂, aux₂⟩

theorem terminal_card_le_indepNum (core₁ : PortCore G) (core₂ : PortCore H)
    (aux₁ : AuxCode core₁) (aux₂ : AuxCode core₂) :
    (core₁.I.card - core₁.S.card) * (core₂.I.card - core₂.S.card) +
      core₁.S.card * aux₂.X.card + aux₁.X.card * core₂.S.card ≤ (G ⊠ H).indepNum := by
  rw [← terminalIndepSet_card core₁ core₂ aux₁ aux₂]
  exact (terminalIndepSet_isIndep core₁ core₂ aux₁ aux₂).card_le_indepNum

/-- One-sided asymmetric terminal substitution: when `X₁` avoids `N[P₁¹]` (`v₁ = 0`),
`X₂` can be ANY unconstrained independent set in `H` (e.g., `core₂.I` itself of size `a₂`!). -/
noncomputable def oneSidedTerminalIndepSet (core₁ : PortCore G) (core₂ : PortCore H)
    (X₁ : Finset V) (X₂ : Finset W) : Finset (V × W) := by
  classical
  let H₁ := X₁.filter (fun x => core₁.inP0Nbr x)
  let O₁ := X₁.filter (fun x => ¬ core₁.inP0Nbr x)
  let V₂ := X₂.filter (fun y => core₂.inP1Nbr y)
  let U₂ := X₂.filter (fun y => ¬ core₂.inP1Nbr y)
  exact
    (core₁.B ×ˢ core₂.B) ∪
    (core₁.P0 ×ˢ U₂) ∪
    (core₁.P1 ×ˢ V₂) ∪
    (O₁ ×ˢ core₂.S) ∪
    (H₁ ×ˢ core₂.P1)

private theorem oneSidedTerminal_indep_and_card (core₁ : PortCore G) (core₂ : PortCore H)
    {X₁ : Finset V} {X₂ : Finset W}
    (hX₁ : G.IsIndepSet (X₁ : Set V))
    (hX₁_avoid : ∀ x ∈ X₁, ¬ core₁.inP1Nbr x)
    (hX₂ : H.IsIndepSet (X₂ : Set W)) :
    (G ⊠ H).IsIndepSet ((oneSidedTerminalIndepSet core₁ core₂ X₁ X₂ : Finset (V × W)) : Set (V × W)) ∧
    (oneSidedTerminalIndepSet core₁ core₂ X₁ X₂).card =
      (core₁.I.card - core₁.S.card) * (core₂.I.card - core₂.S.card) +
      core₁.S.card * X₂.card + X₁.card * core₂.S.card := by
  classical
  let H₁ := X₁.filter (fun x => core₁.inP0Nbr x)
  let O₁ := X₁.filter (fun x => ¬ core₁.inP0Nbr x)
  let V₂ := X₂.filter (fun y => core₂.inP1Nbr y)
  let U₂ := X₂.filter (fun y => ¬ core₂.inP1Nbr y)
  let T0 := core₁.B ×ˢ core₂.B
  let T1 := core₁.P0 ×ˢ U₂
  let T2 := core₁.P1 ×ˢ V₂
  let T3 := O₁ ×ˢ core₂.S
  let T4 := H₁ ×ˢ core₂.P1
  have h01 : ∀ x ∈ T0, ∀ y ∈ T1, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [T0, T1, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (core₁.not_close_B_P0 h₁.1 h₂.1)
  have h02 : ∀ x ∈ T0, ∀ y ∈ T2, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [T0, T2, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (core₁.not_close_B_P1 h₁.1 h₂.1)
  have h03 : ∀ x ∈ T0, ∀ y ∈ T3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [T0, T3, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (core₂.not_close_B_S h₁.2 h₂.2)
  have h04 : ∀ x ∈ T0, ∀ y ∈ T4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [T0, T4, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (core₂.not_close_B_P1 h₁.2 h₂.2)
  have h12 : ∀ x ∈ T1, ∀ y ∈ T2, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, u₂⟩ h₁ ⟨_, v₂⟩ h₂
    simp only [T1, T2, U₂, V₂, Finset.mem_product, Finset.mem_filter] at h₁ h₂
    exact not_close_prod_snd (isIndepSet_not_close_of_ne hX₂ h₁.2.1 h₂.2.1
      (fun heq => by dsimp only at heq; exact h₁.2.2 (heq ▸ h₂.2.2)))
  have h13 : ∀ x ∈ T1, ∀ y ∈ T3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨p₁, _⟩ h₁ ⟨o₁, _⟩ h₂
    simp only [T1, T3, O₁, Finset.mem_product, Finset.mem_filter] at h₁ h₂
    exact not_close_prod_fst (fun hc => h₂.1.2 ((core₁.inP0Nbr_iff_mem_P0 o₁).mpr ⟨p₁, h₁.1, hc⟩))
  have h14 : ∀ x ∈ T1, ∀ y ∈ T4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, u₂⟩ h₁ ⟨_, p₂⟩ h₂
    simp only [T1, T4, U₂, Finset.mem_product, Finset.mem_filter] at h₁ h₂
    exact not_close_prod_snd (fun hc => h₁.2.2 ((core₂.inP1Nbr_iff_mem_P1 u₂).mpr ⟨p₂, h₂.2, close_symm hc⟩))
  have h23 : ∀ x ∈ T2, ∀ y ∈ T3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨p₁, _⟩ h₁ ⟨o₁, _⟩ h₂
    simp only [T2, T3, O₁, Finset.mem_product, Finset.mem_filter] at h₁ h₂
    exact not_close_prod_fst (fun hc => hX₁_avoid o₁ h₂.1.1 ((core₁.inP1Nbr_iff_mem_P1 o₁).mpr ⟨p₁, h₁.1, hc⟩))
  have h24 : ∀ x ∈ T2, ∀ y ∈ T4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨p₁, _⟩ h₁ ⟨h₁', _⟩ h₂
    simp only [T2, T4, H₁, Finset.mem_product, Finset.mem_filter] at h₁ h₂
    exact not_close_prod_fst (fun hc => hX₁_avoid h₁' h₂.1.1 ((core₁.inP1Nbr_iff_mem_P1 h₁').mpr ⟨p₁, h₁.1, hc⟩))
  have h34 : ∀ x ∈ T3, ∀ y ∈ T4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨o₁, _⟩ h₁ ⟨h₁', _⟩ h₂
    simp only [T3, T4, O₁, H₁, Finset.mem_product, Finset.mem_filter] at h₁ h₂
    exact not_close_prod_fst (isIndepSet_not_close_of_ne hX₁ h₁.1.1 h₂.1.1
      (fun heq => by dsimp only at heq; exact h₁.1.2 (heq ▸ h₂.1.2)))
  refine ⟨?_, ?_⟩
  · exact isIndepSet_union5
      (isIndepSet_prod core₁.indep_B core₂.indep_B)
      (isIndepSet_prod core₁.indep_P0_finset (isIndepSet_subset hX₂ (Finset.filter_subset _ _)))
      (isIndepSet_prod core₁.indep_P1_finset (isIndepSet_subset hX₂ (Finset.filter_subset _ _)))
      (isIndepSet_prod (isIndepSet_subset hX₁ (Finset.filter_subset _ _)) core₂.indep_S)
      (isIndepSet_prod (isIndepSet_subset hX₁ (Finset.filter_subset _ _)) core₂.indep_P1_finset)
      h01 h02 h03 h04 h12 h13 h14 h23 h24 h34
  · change (T0 ∪ T1 ∪ T2 ∪ T3 ∪ T4).card = _
    rw [card_union5 (disjoint_of_not_close h01) (disjoint_of_not_close h02)
      (disjoint_of_not_close h03) (disjoint_of_not_close h04) (disjoint_of_not_close h12)
      (disjoint_of_not_close h13) (disjoint_of_not_close h14) (disjoint_of_not_close h23)
      (disjoint_of_not_close h24) (disjoint_of_not_close h34)]
    simp only [T0, T1, T2, T3, T4, Finset.card_product,
      core₁.card_B, core₂.card_B, core₁.card_P0, core₁.card_P1, core₂.card_P1]
    have hp1 : H₁.card + O₁.card = X₁.card := Finset.card_filter_add_card_filter_not _
    have hp2 : V₂.card + U₂.card = X₂.card := Finset.card_filter_add_card_filter_not _
    nlinarith

theorem oneSidedTerminalIndepSet_isIndep (core₁ : PortCore G) (core₂ : PortCore H)
    {X₁ : Finset V} {X₂ : Finset W}
    (hX₁ : G.IsIndepSet (X₁ : Set V))
    (hX₁_avoid : ∀ x ∈ X₁, ¬ core₁.inP1Nbr x)
    (hX₂ : H.IsIndepSet (X₂ : Set W)) :
    (G ⊠ H).IsIndepSet ((oneSidedTerminalIndepSet core₁ core₂ X₁ X₂ : Finset (V × W)) : Set (V × W)) :=
  (oneSidedTerminal_indep_and_card core₁ core₂ hX₁ hX₁_avoid hX₂).1

theorem oneSidedTerminalIndepSet_card (core₁ : PortCore G) (core₂ : PortCore H)
    {X₁ : Finset V} {X₂ : Finset W}
    (hX₁ : G.IsIndepSet (X₁ : Set V))
    (hX₁_avoid : ∀ x ∈ X₁, ¬ core₁.inP1Nbr x)
    (hX₂ : H.IsIndepSet (X₂ : Set W)) :
    (oneSidedTerminalIndepSet core₁ core₂ X₁ X₂).card =
      (core₁.I.card - core₁.S.card) * (core₂.I.card - core₂.S.card) +
      core₁.S.card * X₂.card + X₁.card * core₂.S.card :=
  (oneSidedTerminal_indep_and_card core₁ core₂ hX₁ hX₁_avoid hX₂).2

theorem oneSidedTerminal_card_le_indepNum (core₁ : PortCore G) (core₂ : PortCore H)
    {X₁ : Finset V} {X₂ : Finset W}
    (hX₁ : G.IsIndepSet (X₁ : Set V))
    (hX₁_avoid : ∀ x ∈ X₁, ¬ core₁.inP1Nbr x)
    (hX₂ : H.IsIndepSet (X₂ : Set W)) :
    (core₁.I.card - core₁.S.card) * (core₂.I.card - core₂.S.card) +
      core₁.S.card * X₂.card + X₁.card * core₂.S.card ≤ (G ⊠ H).indepNum := by
  rw [← oneSidedTerminalIndepSet_card core₁ core₂ hX₁ hX₁_avoid hX₂]
  exact (oneSidedTerminalIndepSet_isIndep core₁ core₂ hX₁ hX₁_avoid hX₂).card_le_indepNum

/-- Product `PortCore` of two `HeteroGadget`s on `G ⊠ H`. -/
noncomputable def prodCore (g1 : HeteroGadget G) (g2 : HeteroGadget H) : PortCore (G ⊠ H) := by
  classical
  refine
    { I := prodI g1 g2
      S := (g1.core.S ×ˢ g2.aux.OSlice) ∪ (g1.aux.OSlice ×ˢ g2.core.S)
      f0 := fun p => if p.1 ∈ g1.core.S then (g1.core.f0 p.1, p.2) else (p.1, g2.core.f1 p.2)
      f1 := fun p => if p.1 ∈ g1.core.S then (g1.core.f1 p.1, p.2) else (p.1, g2.core.f0 p.2)
      indep_I := prodI_isIndepSet g1 g2
      S_sub_I := ?_
      priv0 := ?_
      priv1 := ?_
      indep_P0 := ?_
      indep_P1 := ?_
      self_mem := ?_ }
  · intro p hp
    simp only [prodI, Finset.mem_union] at hp ⊢
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
      simp only [prodI, Finset.mem_union, Finset.mem_product] at hu
      rcases hu with (((((⟨hu1, _⟩ | ⟨hu1, hu2⟩) | ⟨_, hu2⟩) | ⟨_, hu2⟩) | ⟨hu1, _⟩) | ⟨_, hu2⟩) | ⟨_, hu2⟩
      · exact absurd hc1 (g1.core.not_close_B_P0 hu1 hp0)
      · exact Prod.ext ((g1.core.priv0 p.1 hs1).2 u.1 (g1.core.S_sub_I hu1) hc1)
          (isIndepSet_eq_of_close g2.aux.indep_X
            (g2.aux.mem_OSlice.mp hu2).1 (g2.aux.mem_OSlice.mp ho2).1 hc2)
      · exact absurd (close_symm hc2) (not_close_OSlice_HSlice g2 ho2 hu2)
      · exact absurd (close_symm hc2) (not_close_OSlice_VSlice g2 ho2 hu2)
      · exact absurd (close_symm hc1) (not_close_P0_OSlice g1 hp0 hu1)
      · exact absurd hc2 (not_close_P1_OSlice g2 hu2 ho2)
      · exact absurd hc2 (not_close_P0_OSlice g2 hu2 ho2)
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      have hns1 : p.1 ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1
      simp only [hns1, ↓reduceIte]
      refine ⟨eq_or_strongProd_adj.mpr ⟨Or.inl rfl, (g2.core.priv1 p.2 hs2).1⟩, ?_⟩
      intro u hu hcu
      rcases eq_or_strongProd_adj.mp hcu with ⟨hc1, hc2⟩
      have hp1 : g2.core.f1 p.2 ∈ g2.core.P1 := g2.core.mem_P1.mpr ⟨p.2, hs2, rfl⟩
      simp only [prodI, Finset.mem_union, Finset.mem_product] at hu
      rcases hu with (((((⟨_, hu2⟩ | ⟨hu1, _⟩) | ⟨hu1, _⟩) | ⟨hu1, _⟩) | ⟨hu1, hu2⟩) | ⟨hu1, _⟩) | ⟨hu1, _⟩
      · exact absurd hc2 (g2.core.not_close_B_P1 hu2 hp1)
      · exact absurd hc1 (not_close_S_OSlice g1 hu1 ho1)
      · exact absurd hc1 (not_close_P0_OSlice g1 hu1 ho1)
      · exact absurd hc1 (not_close_P1_OSlice g1 hu1 ho1)
      · exact Prod.ext (isIndepSet_eq_of_close g1.aux.indep_X
            (g1.aux.mem_OSlice.mp hu1).1 (g1.aux.mem_OSlice.mp ho1).1 hc1)
          ((g2.core.priv1 p.2 hs2).2 u.2 (g2.core.S_sub_I hu2) hc2)
      · exact absurd (close_symm hc1) (not_close_OSlice_HSlice g1 ho1 hu1)
      · exact absurd (close_symm hc1) (not_close_OSlice_VSlice g1 ho1 hu1)
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_product.mp hp with ⟨hs1, ho2⟩
      simp only [hs1, ↓reduceIte]
      refine ⟨eq_or_strongProd_adj.mpr ⟨(g1.core.priv1 p.1 hs1).1, Or.inl rfl⟩, ?_⟩
      intro u hu hcu
      rcases eq_or_strongProd_adj.mp hcu with ⟨hc1, hc2⟩
      have hp1 : g1.core.f1 p.1 ∈ g1.core.P1 := g1.core.mem_P1.mpr ⟨p.1, hs1, rfl⟩
      simp only [prodI, Finset.mem_union, Finset.mem_product] at hu
      rcases hu with (((((⟨hu1, _⟩ | ⟨hu1, hu2⟩) | ⟨_, hu2⟩) | ⟨_, hu2⟩) | ⟨hu1, _⟩) | ⟨_, hu2⟩) | ⟨_, hu2⟩
      · exact absurd hc1 (g1.core.not_close_B_P1 hu1 hp1)
      · exact Prod.ext ((g1.core.priv1 p.1 hs1).2 u.1 (g1.core.S_sub_I hu1) hc1)
          (isIndepSet_eq_of_close g2.aux.indep_X
            (g2.aux.mem_OSlice.mp hu2).1 (g2.aux.mem_OSlice.mp ho2).1 hc2)
      · exact absurd (close_symm hc2) (not_close_OSlice_HSlice g2 ho2 hu2)
      · exact absurd (close_symm hc2) (not_close_OSlice_VSlice g2 ho2 hu2)
      · exact absurd (close_symm hc1) (not_close_P1_OSlice g1 hp1 hu1)
      · exact absurd hc2 (not_close_P1_OSlice g2 hu2 ho2)
      · exact absurd hc2 (not_close_P0_OSlice g2 hu2 ho2)
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      have hns1 : p.1 ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1
      simp only [hns1, ↓reduceIte]
      refine ⟨eq_or_strongProd_adj.mpr ⟨Or.inl rfl, (g2.core.priv0 p.2 hs2).1⟩, ?_⟩
      intro u hu hcu
      rcases eq_or_strongProd_adj.mp hcu with ⟨hc1, hc2⟩
      have hp0 : g2.core.f0 p.2 ∈ g2.core.P0 := g2.core.mem_P0.mpr ⟨p.2, hs2, rfl⟩
      simp only [prodI, Finset.mem_union, Finset.mem_product] at hu
      rcases hu with (((((⟨_, hu2⟩ | ⟨hu1, _⟩) | ⟨hu1, _⟩) | ⟨hu1, _⟩) | ⟨hu1, hu2⟩) | ⟨hu1, _⟩) | ⟨hu1, _⟩
      · exact absurd hc2 (g2.core.not_close_B_P0 hu2 hp0)
      · exact absurd hc1 (not_close_S_OSlice g1 hu1 ho1)
      · exact absurd hc1 (not_close_P0_OSlice g1 hu1 ho1)
      · exact absurd hc1 (not_close_P1_OSlice g1 hu1 ho1)
      · exact Prod.ext (isIndepSet_eq_of_close g1.aux.indep_X
            (g1.aux.mem_OSlice.mp hu1).1 (g1.aux.mem_OSlice.mp ho1).1 hc1)
          ((g2.core.priv0 p.2 hs2).2 u.2 (g2.core.S_sub_I hu2) hc2)
      · exact absurd (close_symm hc1) (not_close_OSlice_HSlice g1 ho1 hu1)
      · exact absurd (close_symm hc1) (not_close_OSlice_VSlice g1 ho1 hu1)
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne hadj
    rcases eq_or_strongProd_adj.mp (Or.inr hadj) with ⟨hc1, hc2⟩
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · rcases Finset.mem_product.mp hp with ⟨hs1, ho2⟩
      rcases Finset.mem_product.mp hq with ⟨hs1', ho2'⟩
      simp only [hs1, hs1', ↓reduceIte] at hne hc1 hc2
      exact hne (Prod.ext
        (isIndepSet_eq_of_close g1.core.indep_P0_finset
          (g1.core.mem_P0.mpr ⟨p.1, hs1, rfl⟩) (g1.core.mem_P0.mpr ⟨q.1, hs1', rfl⟩) hc1)
        (isIndepSet_eq_of_close g2.aux.indep_X
          (g2.aux.mem_OSlice.mp ho2).1 (g2.aux.mem_OSlice.mp ho2').1 hc2))
    · rcases Finset.mem_product.mp hp with ⟨hs1, _⟩
      rcases Finset.mem_product.mp hq with ⟨ho1', _⟩
      have hns1' : q.1 ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1'
      simp only [hs1, hns1', ↓reduceIte] at hc1
      exact not_close_P0_OSlice g1 (g1.core.mem_P0.mpr ⟨p.1, hs1, rfl⟩) ho1' hc1
    · rcases Finset.mem_product.mp hp with ⟨ho1, _⟩
      rcases Finset.mem_product.mp hq with ⟨hs1', _⟩
      have hns1 : p.1 ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1
      simp only [hns1, hs1', ↓reduceIte] at hc1
      exact not_close_P0_OSlice g1 (g1.core.mem_P0.mpr ⟨q.1, hs1', rfl⟩) ho1 (close_symm hc1)
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      rcases Finset.mem_product.mp hq with ⟨ho1', hs2'⟩
      have hns1 : p.1 ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1
      have hns1' : q.1 ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1'
      simp only [hns1, hns1', ↓reduceIte] at hne hc1 hc2
      exact hne (Prod.ext
        (isIndepSet_eq_of_close g1.aux.indep_X
          (g1.aux.mem_OSlice.mp ho1).1 (g1.aux.mem_OSlice.mp ho1').1 hc1)
        (isIndepSet_eq_of_close g2.core.indep_P1_finset
          (g2.core.mem_P1.mpr ⟨p.2, hs2, rfl⟩) (g2.core.mem_P1.mpr ⟨q.2, hs2', rfl⟩) hc2))
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne hadj
    rcases eq_or_strongProd_adj.mp (Or.inr hadj) with ⟨hc1, hc2⟩
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · rcases Finset.mem_product.mp hp with ⟨hs1, ho2⟩
      rcases Finset.mem_product.mp hq with ⟨hs1', ho2'⟩
      simp only [hs1, hs1', ↓reduceIte] at hne hc1 hc2
      exact hne (Prod.ext
        (isIndepSet_eq_of_close g1.core.indep_P1_finset
          (g1.core.mem_P1.mpr ⟨p.1, hs1, rfl⟩) (g1.core.mem_P1.mpr ⟨q.1, hs1', rfl⟩) hc1)
        (isIndepSet_eq_of_close g2.aux.indep_X
          (g2.aux.mem_OSlice.mp ho2).1 (g2.aux.mem_OSlice.mp ho2').1 hc2))
    · rcases Finset.mem_product.mp hp with ⟨hs1, _⟩
      rcases Finset.mem_product.mp hq with ⟨ho1', _⟩
      have hns1' : q.1 ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1'
      simp only [hs1, hns1', ↓reduceIte] at hc1
      exact not_close_P1_OSlice g1 (g1.core.mem_P1.mpr ⟨p.1, hs1, rfl⟩) ho1' hc1
    · rcases Finset.mem_product.mp hp with ⟨ho1, _⟩
      rcases Finset.mem_product.mp hq with ⟨hs1', _⟩
      have hns1 : p.1 ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1
      simp only [hns1, hs1', ↓reduceIte] at hc1
      exact not_close_P1_OSlice g1 (g1.core.mem_P1.mpr ⟨q.1, hs1', rfl⟩) ho1 (close_symm hc1)
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      rcases Finset.mem_product.mp hq with ⟨ho1', hs2'⟩
      have hns1 : p.1 ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1
      have hns1' : q.1 ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1'
      simp only [hns1, hns1', ↓reduceIte] at hne hc1 hc2
      exact hne (Prod.ext
        (isIndepSet_eq_of_close g1.aux.indep_X
          (g1.aux.mem_OSlice.mp ho1).1 (g1.aux.mem_OSlice.mp ho1').1 hc1)
        (isIndepSet_eq_of_close g2.core.indep_P0_finset
          (g2.core.mem_P0.mpr ⟨p.2, hs2, rfl⟩) (g2.core.mem_P0.mpr ⟨q.2, hs2', rfl⟩) hc2))
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_product.mp hp with ⟨hs1, _⟩
      simp only [hs1, ↓reduceIte]
      rcases g1.core.self_mem p.1 hs1 with h0 | h1
      · exact Or.inl (Prod.ext h0 rfl)
      · exact Or.inr (Prod.ext h1 rfl)
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      have hns1 : p.1 ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1
      simp only [hns1, ↓reduceIte]
      rcases g2.core.self_mem p.2 hs2 with h0 | h1
      · exact Or.inr (Prod.ext rfl h0)
      · exact Or.inl (Prod.ext rfl h1)

theorem prodCore_f0_of_mem_S (g1 : HeteroGadget G) (g2 : HeteroGadget H) {p : V × W}
    (hp : p.1 ∈ g1.core.S) : (prodCore g1 g2).f0 p = (g1.core.f0 p.1, p.2) := by
  classical simp [prodCore, hp]

theorem prodCore_f0_of_not_mem_S (g1 : HeteroGadget G) (g2 : HeteroGadget H) {p : V × W}
    (hp : p.1 ∉ g1.core.S) : (prodCore g1 g2).f0 p = (p.1, g2.core.f1 p.2) := by
  classical simp [prodCore, hp]

theorem prodCore_f1_of_mem_S (g1 : HeteroGadget G) (g2 : HeteroGadget H) {p : V × W}
    (hp : p.1 ∈ g1.core.S) : (prodCore g1 g2).f1 p = (g1.core.f1 p.1, p.2) := by
  classical simp [prodCore, hp]

theorem prodCore_f1_of_not_mem_S (g1 : HeteroGadget G) (g2 : HeteroGadget H) {p : V × W}
    (hp : p.1 ∉ g1.core.S) : (prodCore g1 g2).f1 p = (p.1, g2.core.f0 p.2) := by
  classical simp [prodCore, hp]

theorem prodCore_inP0Nbr_iff (g1 : HeteroGadget G) (g2 : HeteroGadget H) (x : V × W) :
    (prodCore g1 g2).inP0Nbr x ↔
      (g1.core.inP0Nbr x.1 ∧ ∃ o₂ ∈ g2.aux.OSlice, o₂ = x.2 ∨ H.Adj o₂ x.2) ∨
      ((∃ o₁ ∈ g1.aux.OSlice, o₁ = x.1 ∨ G.Adj o₁ x.1) ∧ g2.core.inP1Nbr x.2) := by
  classical
  constructor
  · rintro ⟨⟨a, b⟩, hp, hc⟩
    rcases eq_or_strongProd_adj.mp hc with ⟨hc1, hc2⟩
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_product.mp hp with ⟨hs1, ho2⟩
      simp only [prodCore, hs1, ↓reduceIte] at hc1 hc2
      exact Or.inl ⟨⟨a, hs1, hc1⟩, ⟨b, ho2, hc2⟩⟩
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      have hns1 : a ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1
      simp only [prodCore, hns1, ↓reduceIte] at hc1 hc2
      exact Or.inr ⟨⟨a, ho1, hc1⟩, ⟨b, hs2, hc2⟩⟩
  · rintro (⟨⟨s₁, hs₁, hc1⟩, ⟨o₂, ho₂, hc2⟩⟩ | ⟨⟨o₁, ho₁, hc1⟩, ⟨s₂, hs₂, hc2⟩⟩)
    · refine ⟨(s₁, o₂), Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hs₁, ho₂⟩), ?_⟩
      simp only [prodCore, hs₁, ↓reduceIte]
      exact eq_or_strongProd_adj.mpr ⟨hc1, hc2⟩
    · have hns1 : o₁ ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho₁
      refine ⟨(o₁, s₂), Finset.mem_union_right _ (Finset.mem_product.mpr ⟨ho₁, hs₂⟩), ?_⟩
      simp only [prodCore, hns1, ↓reduceIte]
      exact eq_or_strongProd_adj.mpr ⟨hc1, hc2⟩

theorem prodCore_inP1Nbr_iff (g1 : HeteroGadget G) (g2 : HeteroGadget H) (x : V × W) :
    (prodCore g1 g2).inP1Nbr x ↔
      (g1.core.inP1Nbr x.1 ∧ ∃ o₂ ∈ g2.aux.OSlice, o₂ = x.2 ∨ H.Adj o₂ x.2) ∨
      ((∃ o₁ ∈ g1.aux.OSlice, o₁ = x.1 ∨ G.Adj o₁ x.1) ∧ g2.core.inP0Nbr x.2) := by
  classical
  constructor
  · rintro ⟨⟨a, b⟩, hp, hc⟩
    rcases eq_or_strongProd_adj.mp hc with ⟨hc1, hc2⟩
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_product.mp hp with ⟨hs1, ho2⟩
      simp only [prodCore, hs1, ↓reduceIte] at hc1 hc2
      exact Or.inl ⟨⟨a, hs1, hc1⟩, ⟨b, ho2, hc2⟩⟩
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      have hns1 : a ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho1
      simp only [prodCore, hns1, ↓reduceIte] at hc1 hc2
      exact Or.inr ⟨⟨a, ho1, hc1⟩, ⟨b, hs2, hc2⟩⟩
  · rintro (⟨⟨s₁, hs₁, hc1⟩, ⟨o₂, ho₂, hc2⟩⟩ | ⟨⟨o₁, ho₁, hc1⟩, ⟨s₂, hs₂, hc2⟩⟩)
    · refine ⟨(s₁, o₂), Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hs₁, ho₂⟩), ?_⟩
      simp only [prodCore, hs₁, ↓reduceIte]
      exact eq_or_strongProd_adj.mpr ⟨hc1, hc2⟩
    · have hns1 : o₁ ∉ g1.core.S := not_mem_S_of_mem_OSlice g1 ho₁
      refine ⟨(o₁, s₂), Finset.mem_union_right _ (Finset.mem_product.mpr ⟨ho₁, hs₂⟩), ?_⟩
      simp only [prodCore, hns1, ↓reduceIte]
      exact eq_or_strongProd_adj.mpr ⟨hc1, hc2⟩

theorem prodCore_card_S (g1 : HeteroGadget G) (g2 : HeteroGadget H) :
    (prodCore g1 g2).S.card =
      g1.core.S.card * g2.aux.OSlice.card + g1.aux.OSlice.card * g2.core.S.card := by
  classical
  have hdisj : Disjoint (g1.core.S ×ˢ g2.aux.OSlice) (g1.aux.OSlice ×ˢ g2.core.S) := by
    rw [Finset.disjoint_left]; intro p h1 h2
    exact not_mem_S_of_mem_OSlice g1 (Finset.mem_product.mp h2).1 (Finset.mem_product.mp h1).1
  simp only [prodCore, Finset.card_union_of_disjoint hdisj, Finset.card_product]

theorem mem_OSlice_of_mem_X_close (g : HeteroGadget G) {x : V} (hx : x ∈ g.aux.X) :
    (∃ o ∈ g.aux.OSlice, o = x ∨ G.Adj o x) ↔ x ∈ g.aux.OSlice := by
  constructor
  · rintro ⟨o, ho, hc⟩
    exact (isIndepSet_eq_of_close g.aux.indep_X (g.aux.mem_OSlice.mp ho).1 hx hc) ▸ ho
  · exact fun hxO => ⟨x, hxO, Or.inl rfl⟩

noncomputable def prod (g1 : HeteroGadget G) (g2 : HeteroGadget H) : HeteroGadget (G ⊠ H) where
  core := prodCore g1 g2
  aux :=
    { X := g1.aux.X ×ˢ g2.aux.X
      indep_X := isIndepSet_prod g1.aux.indep_X g2.aux.indep_X
      disj_nbr := by
        intro x hx ⟨h0, h1⟩
        rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
        rw [prodCore_inP0Nbr_iff, mem_OSlice_of_mem_X_close g1 hx1,
          mem_OSlice_of_mem_X_close g2 hx2] at h0
        rw [prodCore_inP1Nbr_iff, mem_OSlice_of_mem_X_close g1 hx1,
          mem_OSlice_of_mem_X_close g2 hx2] at h1
        rcases h0 with ⟨h01, _⟩ | ⟨h01, h02⟩ <;> rcases h1 with ⟨h11, _⟩ | ⟨h11, h12⟩
        · exact g1.aux.disj_nbr x.1 hx1 ⟨h01, h11⟩
        · exact (g1.aux.mem_OSlice.mp h11).2.1 h01
        · exact (g1.aux.mem_OSlice.mp h01).2.2 h11
        · exact g2.aux.disj_nbr x.2 hx2 ⟨h12, h02⟩ }

theorem prod_asymProfile (g1 : HeteroGadget G) (g2 : HeteroGadget H) :
    (g1.prod g2).asymProfile = g1.asymProfile.prod g2.asymProfile := by
  classical
  have hH_eq : (g1.prod g2).aux.HSlice =
      (g1.aux.HSlice ×ˢ g2.aux.OSlice) ∪ (g1.aux.OSlice ×ˢ g2.aux.VSlice) := by
    ext ⟨x₁, x₂⟩
    simp only [AuxCode.mem_HSlice, prod, Finset.mem_union, Finset.mem_product]
    by_cases hx1 : x₁ ∈ g1.aux.X <;> by_cases hx2 : x₂ ∈ g2.aux.X
    · rw [prodCore_inP0Nbr_iff, mem_OSlice_of_mem_X_close g1 hx1, mem_OSlice_of_mem_X_close g2 hx2]
      simp [AuxCode.mem_VSlice, hx1, hx2]
    · simp [AuxCode.mem_OSlice, AuxCode.mem_VSlice, hx1, hx2]
    · simp [AuxCode.mem_OSlice, hx1, hx2]
    · simp [AuxCode.mem_OSlice, hx1, hx2]
  have hV_eq : (g1.prod g2).aux.VSlice =
      (g1.aux.VSlice ×ˢ g2.aux.OSlice) ∪ (g1.aux.OSlice ×ˢ g2.aux.HSlice) := by
    ext ⟨x₁, x₂⟩
    simp only [AuxCode.mem_VSlice, prod, Finset.mem_union, Finset.mem_product]
    by_cases hx1 : x₁ ∈ g1.aux.X <;> by_cases hx2 : x₂ ∈ g2.aux.X
    · rw [prodCore_inP1Nbr_iff, mem_OSlice_of_mem_X_close g1 hx1, mem_OSlice_of_mem_X_close g2 hx2]
      simp [AuxCode.mem_HSlice, hx1, hx2]
    · simp [AuxCode.mem_OSlice, AuxCode.mem_HSlice, hx1, hx2]
    · simp [AuxCode.mem_OSlice, hx1, hx2]
    · simp [AuxCode.mem_OSlice, hx1, hx2]
  have hdH : Disjoint (g1.aux.HSlice ×ˢ g2.aux.OSlice) (g1.aux.OSlice ×ˢ g2.aux.VSlice) := by
    rw [Finset.disjoint_left]; intro p h1 h2
    exact (g1.aux.mem_OSlice.mp (Finset.mem_product.mp h2).1).2.1
      (g1.aux.mem_HSlice.mp (Finset.mem_product.mp h1).1).2
  have hdV : Disjoint (g1.aux.VSlice ×ˢ g2.aux.OSlice) (g1.aux.OSlice ×ˢ g2.aux.HSlice) := by
    rw [Finset.disjoint_left]; intro p h1 h2
    exact (g1.aux.mem_OSlice.mp (Finset.mem_product.mp h2).1).2.2
      (g1.aux.mem_VSlice.mp (Finset.mem_product.mp h1).1).2
  have hH : (g1.prod g2).aux.HSlice.card =
      g1.aux.HSlice.card * g2.aux.OSlice.card + g1.aux.OSlice.card * g2.aux.VSlice.card := by
    rw [hH_eq, Finset.card_union_of_disjoint hdH, Finset.card_product, Finset.card_product]
  have hV : (g1.prod g2).aux.VSlice.card =
      g1.aux.VSlice.card * g2.aux.OSlice.card + g1.aux.OSlice.card * g2.aux.HSlice.card := by
    rw [hV_eq, Finset.card_union_of_disjoint hdV, Finset.card_product, Finset.card_product]
  have hI : (g1.prod g2).core.I.card =
      (g1.core.I.card - g1.core.S.card) * (g2.core.I.card - g2.core.S.card) +
      g1.core.S.card * g2.aux.X.card + g1.aux.X.card * g2.core.S.card := prodI_card g1 g2
  have hS : (g1.prod g2).core.S.card =
      g1.core.S.card * g2.aux.OSlice.card + g1.aux.OSlice.card * g2.core.S.card :=
    prodCore_card_S g1 g2
  have hX : (g1.prod g2).aux.X.card = g1.aux.X.card * g2.aux.X.card := Finset.card_product _ _
  have hO : (g1.prod g2).aux.OSlice.card =
      g1.aux.OSlice.card * g2.aux.OSlice.card +
      (g1.aux.HSlice.card + g1.aux.VSlice.card) * (g2.aux.HSlice.card + g2.aux.VSlice.card) := by
    have hp := (g1.prod g2).aux.card_partition
    have hp1 := g1.aux.card_partition
    have hp2 := g2.aux.card_partition
    rw [hH, hV, hX] at hp
    nlinarith
  simp only [asymProfile, AsymProfile.prod, AsymProfile.mk.injEq]
  exact ⟨hI, hS, hX, hO, hH, hV⟩

noncomputable def prodAligned (g1 : HeteroGadget G) (g2 : HeteroGadget H) :
    HeteroGadget (G ⊠ H) := g1.prod g2.flip

theorem prodAligned_asymProfile (g1 : HeteroGadget G) (g2 : HeteroGadget H) :
    (g1.prodAligned g2).asymProfile = g1.asymProfile.prodAligned g2.asymProfile := by
  rw [prodAligned, prod_asymProfile, flip_asymProfile, AsymProfile.prodAligned]

end HeteroGadget

/-! ### Heterogeneous Split-Tree (`HeteroTree`) & O(L) Shared-DAG Engine (`HeteroDAG`) -/

inductive HeteroTree (n : ℕ) : Type
  | leaf (idx : Fin n) : HeteroTree n
  | flip (t : HeteroTree n) : HeteroTree n
  | prod (left right : HeteroTree n) : HeteroTree n

namespace HeteroTree

def dim {n : ℕ} (dims : Fin n → ℕ) : HeteroTree n → ℕ
  | .leaf i => dims i
  | .flip t => dim dims t
  | .prod l r => dim dims l + dim dims r

def evalProfile {n : ℕ} (profs : Fin n → AsymProfile) : HeteroTree n → AsymProfile
  | .leaf i => profs i
  | .flip t => (evalProfile profs t).flip
  | .prod l r => (evalProfile profs l).prod (evalProfile profs r)

noncomputable def evalGadget {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {dims : Fin n → ℕ}
    (bases : (i : Fin n) → HeteroGadget (strongPow G (dims i))) :
    (t : HeteroTree n) → HeteroGadget (strongPow G (t.dim dims))
  | .leaf i => bases i
  | .flip t => (evalGadget bases t).flip
  | .prod l r =>
    ((evalGadget bases l).prod (evalGadget bases r)).mapIso
      (strongPowAddEquiv G (l.dim dims) (r.dim dims)).symm

theorem evalGadget_asymProfile {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {dims : Fin n → ℕ}
    (bases : (i : Fin n) → HeteroGadget (strongPow G (dims i)))
    (t : HeteroTree n) :
    (evalGadget bases t).asymProfile = evalProfile (fun i => (bases i).asymProfile) t := by
  induction t with
  | leaf i => rfl
  | flip t ih =>
    change (evalGadget bases t).flip.asymProfile = (evalProfile (fun i => (bases i).asymProfile) t).flip
    rw [HeteroGadget.flip_asymProfile, ih]
  | prod l r ihl ihr =>
    change (((evalGadget bases l).prod (evalGadget bases r)).mapIso _).asymProfile = _
    rw [HeteroGadget.mapIso_asymProfile, HeteroGadget.prod_asymProfile, ihl, ihr]
    rfl

theorem evalProfile_le_indepNum {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {dims : Fin n → ℕ} {profs : Fin n → AsymProfile}
    (bases : (i : Fin n) → HeteroGadget (strongPow G (dims i)))
    (hprofs : ∀ i, (bases i).asymProfile = profs i)
    (t : HeteroTree n) :
    (t.evalProfile profs).a ≤ (strongPow G (t.dim dims)).indepNum := by
  have hfun : (fun i => (bases i).asymProfile) = profs := funext hprofs
  rw [← hfun, ← evalGadget_asymProfile bases t]
  exact (evalGadget bases t).card_le_indepNum

end HeteroTree

inductive HeteroOp (n : ℕ) : Type
  | base (idx : Fin n) : HeteroOp n
  | flip (i : ℕ) : HeteroOp n
  | prod (i j : ℕ) : HeteroOp n
  | prodAligned (i j : ℕ) : HeteroOp n

namespace HeteroDAG

def step {n : ℕ} (bases : Fin n → ℕ × AsymProfile) (acc : List (ℕ × AsymProfile)) :
    HeteroOp n → Option (ℕ × AsymProfile)
  | .base idx => some (bases idx)
  | .flip i => (acc[i]?).map (fun p => (p.1, p.2.flip))
  | .prod i j =>
    match acc[i]?, acc[j]? with
    | some p, some q => some (p.1 + q.1, p.2.prod q.2)
    | _, _ => none
  | .prodAligned i j =>
    match acc[i]?, acc[j]? with
    | some p, some q => some (p.1 + q.1, p.2.prodAligned q.2)
    | _, _ => none

def evalAux {n : ℕ} (bases : Fin n → ℕ × AsymProfile) :
    List (ℕ × AsymProfile) → List (HeteroOp n) → Option (List (ℕ × AsymProfile))
  | acc, [] => some acc
  | acc, op :: ops =>
    match step bases acc op with
    | some r => evalAux bases (acc ++ [r]) ops
    | none => none

def eval {n : ℕ} (bases : Fin n → ℕ × AsymProfile) (ops : List (HeteroOp n)) :
    Option (ℕ × AsymProfile) :=
  (evalAux bases [] ops).bind List.getLast?

def Realizable {V : Type*} [Fintype V] (G : SimpleGraph V) (p : ℕ × AsymProfile) : Prop :=
  ∃ g : HeteroGadget (strongPow G p.1), g.asymProfile = p.2

private theorem step_realizable {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {bases : Fin n → ℕ × AsymProfile}
    (hbases : ∀ i, Realizable G (bases i))
    {acc : List (ℕ × AsymProfile)} (hacc : ∀ p ∈ acc, Realizable G p)
    {op : HeteroOp n} {r : ℕ × AsymProfile}
    (hstep : step bases acc op = some r) :
    Realizable G r := by
  cases op with
  | base idx =>
    simp only [step, Option.some.injEq] at hstep
    exact hstep ▸ hbases idx
  | flip i =>
    simp only [step, Option.map_eq_some_iff] at hstep
    rcases hstep with ⟨p, hp, rfl⟩
    obtain ⟨g, hg⟩ := hacc p (List.mem_of_getElem? hp)
    exact ⟨g.flip, by rw [g.flip_asymProfile, hg]⟩
  | prod i j =>
    simp only [step] at hstep
    cases hpi : acc[i]? with
    | none => simp [hpi] at hstep
    | some p =>
      cases hpj : acc[j]? with
      | none => simp [hpi, hpj] at hstep
      | some q =>
        simp only [hpi, hpj, Option.some.injEq] at hstep
        subst hstep
        obtain ⟨gp, hgp⟩ := hacc p (List.mem_of_getElem? hpi)
        obtain ⟨gq, hgq⟩ := hacc q (List.mem_of_getElem? hpj)
        refine ⟨(gp.prod gq).mapIso (strongPowAddEquiv G p.1 q.1).symm, ?_⟩
        rw [HeteroGadget.mapIso_asymProfile, HeteroGadget.prod_asymProfile, hgp, hgq]
  | prodAligned i j =>
    simp only [step] at hstep
    cases hpi : acc[i]? with
    | none => simp [hpi] at hstep
    | some p =>
      cases hpj : acc[j]? with
      | none => simp [hpi, hpj] at hstep
      | some q =>
        simp only [hpi, hpj, Option.some.injEq] at hstep
        subst hstep
        obtain ⟨gp, hgp⟩ := hacc p (List.mem_of_getElem? hpi)
        obtain ⟨gq, hgq⟩ := hacc q (List.mem_of_getElem? hpj)
        refine ⟨(gp.prodAligned gq).mapIso (strongPowAddEquiv G p.1 q.1).symm, ?_⟩
        rw [HeteroGadget.mapIso_asymProfile, HeteroGadget.prodAligned_asymProfile, hgp, hgq]

private theorem evalAux_realizable {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {bases : Fin n → ℕ × AsymProfile}
    (hbases : ∀ i, Realizable G (bases i)) :
    ∀ {acc out : List (ℕ × AsymProfile)} {ops : List (HeteroOp n)},
      (∀ p ∈ acc, Realizable G p) →
      evalAux bases acc ops = some out →
      ∀ p ∈ out, Realizable G p
  | acc, out, [], hacc, hout => by
    simp only [evalAux, Option.some.injEq] at hout; exact hout ▸ hacc
  | acc, out, op :: ops, hacc, hout => by
    simp only [evalAux] at hout
    cases hs : step bases acc op with
    | none => simp [hs] at hout
    | some r =>
      simp only [hs] at hout
      refine evalAux_realizable hbases (acc := acc ++ [r]) (ops := ops) ?_ hout
      intro p hp
      rcases List.mem_append.mp hp with h | h
      · exact hacc p h
      · rw [List.mem_singleton.mp h]; exact step_realizable hbases hacc hs

theorem eval_le_indepNum {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {bases : Fin n → ℕ × AsymProfile}
    (hbases : ∀ i, Realizable G (bases i))
    {ops : List (HeteroOp n)} {d : ℕ} {prof : AsymProfile}
    (heval : eval bases ops = some (d, prof)) :
    prof.a ≤ (strongPow G d).indepNum := by
  simp only [eval, Option.bind_eq_some_iff] at heval
  rcases heval with ⟨out, hout, hlast⟩
  have hmem : (d, prof) ∈ out := List.mem_of_getLast? hlast
  obtain ⟨g, hg⟩ := evalAux_realizable hbases (fun _ h => by simp at h) hout (d, prof) hmem
  dsimp only at hg
  rw [← hg]
  exact g.card_le_indepNum

/-- Root-level terminal substitution combining two realized `HeteroDAG` outputs into an
independent set in `strongPow G (d₁ + d₂)` of size `p₁.terminalSize p₂`. -/
theorem eval_terminal_le_indepNum {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {bases : Fin n → ℕ × AsymProfile}
    (hbases : ∀ i, Realizable G (bases i))
    {ops₁ ops₂ : List (HeteroOp n)} {d₁ d₂ : ℕ} {p₁ p₂ : AsymProfile}
    (heval₁ : eval bases ops₁ = some (d₁, p₁))
    (heval₂ : eval bases ops₂ = some (d₂, p₂)) :
    p₁.terminalSize p₂ ≤ (strongPow G (d₁ + d₂)).indepNum := by
  simp only [eval, Option.bind_eq_some_iff] at heval₁ heval₂
  rcases heval₁ with ⟨out₁, hout₁, hlast₁⟩
  rcases heval₂ with ⟨out₂, hout₂, hlast₂⟩
  obtain ⟨g₁, hg₁⟩ :=
    evalAux_realizable hbases (fun _ h => by simp at h) hout₁ _ (List.mem_of_getLast? hlast₁)
  obtain ⟨g₂, hg₂⟩ :=
    evalAux_realizable hbases (fun _ h => by simp at h) hout₂ _ (List.mem_of_getLast? hlast₂)
  dsimp only at hg₁ hg₂
  rw [← hg₁, ← hg₂, iso_indepNum_eq (strongPowAddEquiv G d₁ d₂)]
  exact HeteroGadget.terminal_card_le_indepNum g₁.core g₂.core g₁.aux g₂.aux

end HeteroDAG

/-! ============================================================================
    PART 2: Generalized Multi-Port Systems (`PortSystem G ι`) for Finite `ι`
    ============================================================================ -/

set_option linter.unusedFintypeInType false in
structure PortSystem {V : Type*} [Fintype V] (G : SimpleGraph V) (ι : Type*) [Fintype ι] where
  I : Finset V
  S : Finset V
  X : Finset V
  port : ι → V → V
  indep_I : G.IsIndepSet (I : Set V)
  S_sub_I : S ⊆ I
  priv : ∀ σ : ι, ∀ s ∈ S,
    (port σ s = s ∨ G.Adj (port σ s) s) ∧
    ∀ u ∈ I, (u = port σ s ∨ G.Adj u (port σ s)) → u = s
  indep_P : ∀ σ : ι, G.IsIndepSet (port σ '' (S : Set V))
  self_mem : ∀ s ∈ S, ∃ σ : ι, port σ s = s
  indep_X : G.IsIndepSet (X : Set V)
  disj_nbr : ∀ x ∈ X, ∀ σ₁ σ₂ : ι, σ₁ ≠ σ₂ →
    ¬ ((∃ s ∈ S, port σ₁ s = x ∨ G.Adj (port σ₁ s) x) ∧
       (∃ s ∈ S, port σ₂ s = x ∨ G.Adj (port σ₂ s) x))

namespace PortSystem

variable {V W ι : Type*} [Fintype V] [Fintype W] [Fintype ι]
variable {G : SimpleGraph V} {H : SimpleGraph W}

def inPNbr (ps : PortSystem G ι) (σ : ι) (x : V) : Prop :=
  ∃ s ∈ ps.S, ps.port σ s = x ∨ G.Adj (ps.port σ s) x

noncomputable def B (ps : PortSystem G ι) : Finset V := by
  classical exact ps.I \ ps.S

noncomputable def P (ps : PortSystem G ι) (σ : ι) : Finset V := by
  classical exact ps.S.image (ps.port σ)

noncomputable def slice (ps : PortSystem G ι) (σ : ι) : Finset V := by
  classical exact ps.X.filter (fun x => ps.inPNbr σ x)

noncomputable def O (ps : PortSystem G ι) : Finset V := by
  classical exact ps.X.filter (fun x => ∀ σ : ι, ¬ ps.inPNbr σ x)

theorem mem_B (ps : PortSystem G ι) {x : V} : x ∈ ps.B ↔ x ∈ ps.I ∧ x ∉ ps.S := by
  classical simp [B]

theorem mem_P (ps : PortSystem G ι) {σ : ι} {x : V} :
    x ∈ ps.P σ ↔ ∃ s ∈ ps.S, ps.port σ s = x := by
  classical simp [P]

theorem mem_slice (ps : PortSystem G ι) {σ : ι} {x : V} :
    x ∈ ps.slice σ ↔ x ∈ ps.X ∧ ps.inPNbr σ x := by
  classical simp [slice]

theorem mem_O (ps : PortSystem G ι) {x : V} :
    x ∈ ps.O ↔ x ∈ ps.X ∧ ∀ σ : ι, ¬ ps.inPNbr σ x := by
  classical simp [O]

theorem injOn_port (ps : PortSystem G ι) (σ : ι) : Set.InjOn (ps.port σ) (ps.S : Set V) := by
  intro s₁ hs₁ s₂ hs₂ heq
  have hc : s₁ = ps.port σ s₂ ∨ G.Adj s₁ (ps.port σ s₂) := by
    rw [← heq]; exact close_symm (ps.priv σ s₁ hs₁).1
  exact (ps.priv σ s₂ hs₂).2 s₁ (ps.S_sub_I hs₁) hc

theorem card_P (ps : PortSystem G ι) (σ : ι) : (ps.P σ).card = ps.S.card := by
  classical exact Finset.card_image_of_injOn (ps.injOn_port σ)

theorem card_B (ps : PortSystem G ι) : ps.B.card = ps.I.card - ps.S.card := by
  classical exact card_sdiff_eq ps.S_sub_I

theorem indep_B (ps : PortSystem G ι) : G.IsIndepSet (ps.B : Set V) :=
  isIndepSet_subset ps.indep_I (fun _ hx => (ps.mem_B.mp hx).1)

theorem indep_S (ps : PortSystem G ι) : G.IsIndepSet (ps.S : Set V) :=
  isIndepSet_subset ps.indep_I ps.S_sub_I

theorem indep_P_finset (ps : PortSystem G ι) (σ : ι) : G.IsIndepSet (ps.P σ : Set V) := by
  intro x hx y hy hne hadj
  rcases ps.mem_P.mp hx with ⟨s₁, hs₁, rfl⟩
  rcases ps.mem_P.mp hy with ⟨s₂, hs₂, rfl⟩
  exact ps.indep_P σ ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, rfl⟩ hne hadj

theorem card_partition (ps : PortSystem G ι) :
    ps.O.card + ∑ σ : ι, (ps.slice σ).card = ps.X.card := by
  classical
  have hpw : Set.PairwiseDisjoint (Set.univ : Set ι) ps.slice := by
    intro σ₁ _ σ₂ _ hne
    change Disjoint (ps.slice σ₁) (ps.slice σ₂)
    rw [Finset.disjoint_left]; intro x h1 h2
    exact ps.disj_nbr x (ps.mem_slice.mp h1).1 σ₁ σ₂ hne
      ⟨(ps.mem_slice.mp h1).2, (ps.mem_slice.mp h2).2⟩
  have hbi : (Finset.univ.biUnion ps.slice).card = ∑ σ : ι, (ps.slice σ).card :=
    Finset.card_biUnion (fun σ₁ _ σ₂ _ hne => hpw (Set.mem_univ σ₁) (Set.mem_univ σ₂) hne)
  have hdisj : Disjoint ps.O (Finset.univ.biUnion ps.slice) := by
    rw [Finset.disjoint_left]; intro x hO hU
    rcases Finset.mem_biUnion.mp hU with ⟨σ, _, hσ⟩
    exact (ps.mem_O.mp hO).2 σ (ps.mem_slice.mp hσ).2
  have hunion : ps.O ∪ Finset.univ.biUnion ps.slice = ps.X := by
    ext x
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
      ps.mem_O, ps.mem_slice]
    by_cases hx : x ∈ ps.X
    · by_cases hex : ∃ σ : ι, ps.inPNbr σ x
      · simp [hx, hex]
      · push Not at hex; simp [hx, hex]
    · simp [hx]
  rw [← hbi, ← Finset.card_union_of_disjoint hdisj, hunion]

noncomputable def profile (ps : PortSystem G ι) : Profile where
  a := ps.I.card; b := ps.S.card; c := ps.X.card; d := ps.O.card
  hba := Finset.card_le_card ps.S_sub_I
  hdc := by have := ps.card_partition; omega

theorem card_le_indepNum (ps : PortSystem G ι) : ps.profile.a ≤ G.indepNum :=
  ps.indep_I.card_le_indepNum

theorem not_close_B_S (ps : PortSystem G ι) {b s : V} (hb : b ∈ ps.B) (hs : s ∈ ps.S) :
    ¬ (b = s ∨ G.Adj b s) :=
  isIndepSet_not_close_of_ne ps.indep_I (ps.mem_B.mp hb).1 (ps.S_sub_I hs)
    (fun h => (ps.mem_B.mp hb).2 (h ▸ hs))

theorem not_close_B_P (ps : PortSystem G ι) {σ : ι} {b p : V}
    (hb : b ∈ ps.B) (hp : p ∈ ps.P σ) : ¬ (b = p ∨ G.Adj b p) := by
  have hb' := ps.mem_B.mp hb
  rcases ps.mem_P.mp hp with ⟨s, hs, rfl⟩
  exact fun hc => hb'.2 (((ps.priv σ s hs).2 b hb'.1 hc) ▸ hs)

theorem not_close_S_O (ps : PortSystem G ι) {s o : V} (hs : s ∈ ps.S) (ho : o ∈ ps.O) :
    ¬ (s = o ∨ G.Adj s o) := by
  rcases ps.self_mem s hs with ⟨σ, hσ⟩
  exact fun hc => (ps.mem_O.mp ho).2 σ ⟨s, hs, hσ.symm ▸ hc⟩

theorem not_mem_S_of_mem_O (ps : PortSystem G ι) {x : V} (hx : x ∈ ps.O) : x ∉ ps.S :=
  fun hs => not_close_S_O ps hs hx (Or.inl rfl)

theorem not_close_P_O (ps : PortSystem G ι) {σ : ι} {p o : V}
    (hp : p ∈ ps.P σ) (ho : o ∈ ps.O) : ¬ (p = o ∨ G.Adj p o) := by
  rcases ps.mem_P.mp hp with ⟨s, hs, rfl⟩
  exact fun hc => (ps.mem_O.mp ho).2 σ ⟨s, hs, hc⟩

theorem not_close_O_slice (ps : PortSystem G ι) {σ : ι} {o x : V}
    (ho : o ∈ ps.O) (hx : x ∈ ps.slice σ) : ¬ (o = x ∨ G.Adj o x) :=
  isIndepSet_not_close_of_ne ps.indep_X (ps.mem_O.mp ho).1 (ps.mem_slice.mp hx).1
    (fun heq => (ps.mem_O.mp ho).2 σ (heq ▸ (ps.mem_slice.mp hx).2))

theorem not_close_slice_slice (ps : PortSystem G ι) {σ₁ σ₂ : ι} (hne : σ₁ ≠ σ₂)
    {x₁ x₂ : V} (hx₁ : x₁ ∈ ps.slice σ₁) (hx₂ : x₂ ∈ ps.slice σ₂) :
    ¬ (x₁ = x₂ ∨ G.Adj x₁ x₂) :=
  isIndepSet_not_close_of_ne ps.indep_X (ps.mem_slice.mp hx₁).1 (ps.mem_slice.mp hx₂).1
    (fun heq => ps.disj_nbr x₁ (ps.mem_slice.mp hx₁).1 σ₁ σ₂ hne
      ⟨(ps.mem_slice.mp hx₁).2, heq ▸ (ps.mem_slice.mp hx₂).2⟩)

theorem not_close_P_slice_ne (ps : PortSystem G ι) {σ τ : ι} (hne : σ ≠ τ)
    {p x : V} (hp : p ∈ ps.P σ) (hx : x ∈ ps.slice τ) : ¬ (p = x ∨ G.Adj p x) := by
  rcases ps.mem_P.mp hp with ⟨s, hs, rfl⟩
  exact fun hc => ps.disj_nbr x (ps.mem_slice.mp hx).1 σ τ hne ⟨⟨s, hs, hc⟩, (ps.mem_slice.mp hx).2⟩

theorem mem_O_of_mem_X_close (ps : PortSystem G ι) {x : V} (hx : x ∈ ps.X) :
    (∃ o ∈ ps.O, o = x ∨ G.Adj o x) ↔ x ∈ ps.O := by
  constructor
  · rintro ⟨o, ho, hc⟩; exact (isIndepSet_eq_of_close ps.indep_X (ps.mem_O.mp ho).1 hx hc) ▸ ho
  · exact fun ho => ⟨x, ho, Or.inl rfl⟩

/-- The 5-piece main independent set of `PortSystem.prod`. -/
noncomputable def prodI (φ : ι ≃ ι) (ps1 : PortSystem G ι) (ps2 : PortSystem H ι) :
    Finset (V × W) := by
  classical
  exact
    (ps1.B ×ˢ ps2.B) ∪
    (ps1.S ×ˢ ps2.O) ∪
    (Finset.univ.biUnion fun σ : ι => ps1.P σ ×ˢ ps2.slice σ) ∪
    (ps1.O ×ˢ ps2.S) ∪
    (Finset.univ.biUnion fun τ : ι => ps1.slice τ ×ˢ ps2.P (φ τ))

/-- Single master theorem proving BOTH independence AND exact cardinality of `PortSystem.prodI`
(zero duplication!). -/
theorem prodI_indep_and_card (φ : ι ≃ ι) (hφ : ∀ σ : ι, φ σ ≠ σ)
    (ps1 : PortSystem G ι) (ps2 : PortSystem H ι) :
    (G ⊠ H).IsIndepSet ((prodI φ ps1 ps2 : Finset (V × W)) : Set (V × W)) ∧
    (prodI φ ps1 ps2).card =
      (ps1.I.card - ps1.S.card) * (ps2.I.card - ps2.S.card) +
      ps1.S.card * ps2.X.card + ps1.X.card * ps2.S.card := by
  classical
  let C0 : Finset (V × W) := ps1.B ×ˢ ps2.B
  let C1 : Finset (V × W) := ps1.S ×ˢ ps2.O
  let C2 : Finset (V × W) := Finset.univ.biUnion (fun σ : ι => ps1.P σ ×ˢ ps2.slice σ)
  let C3 : Finset (V × W) := ps1.O ×ˢ ps2.S
  let C4 : Finset (V × W) := Finset.univ.biUnion (fun τ : ι => ps1.slice τ ×ˢ ps2.P (φ τ))
  have h01 : ∀ x ∈ C0, ∀ y ∈ C1, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [C0, C1, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (not_close_B_S ps1 h₁.1 h₂.1)
  have h02 : ∀ x ∈ C0, ∀ y ∈ C2, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂
    rcases Finset.mem_biUnion.mp h₂ with ⟨σ, _, h2σ⟩
    exact not_close_prod_fst (not_close_B_P ps1 (Finset.mem_product.mp h₁).1 (Finset.mem_product.mp h2σ).1)
  have h03 : ∀ x ∈ C0, ∀ y ∈ C3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [C0, C3, Finset.mem_product] at h₁ h₂
    exact not_close_prod_snd (not_close_B_S ps2 h₁.2 h₂.2)
  have h04 : ∀ x ∈ C0, ∀ y ∈ C4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂
    rcases Finset.mem_biUnion.mp h₂ with ⟨τ, _, h2τ⟩
    exact not_close_prod_snd (not_close_B_P ps2 (Finset.mem_product.mp h₁).2 (Finset.mem_product.mp h2τ).2)
  have h12 : ∀ x ∈ C1, ∀ y ∈ C2, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂
    rcases Finset.mem_biUnion.mp h₂ with ⟨σ, _, h2σ⟩
    exact not_close_prod_snd (not_close_O_slice ps2 (Finset.mem_product.mp h₁).2 (Finset.mem_product.mp h2σ).2)
  have h13 : ∀ x ∈ C1, ∀ y ∈ C3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂; simp only [C1, C3, Finset.mem_product] at h₁ h₂
    exact not_close_prod_fst (not_close_S_O ps1 h₁.1 h₂.1)
  have h14 : ∀ x ∈ C1, ∀ y ∈ C4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂
    rcases Finset.mem_biUnion.mp h₂ with ⟨τ, _, h2τ⟩
    exact not_close_prod_snd (fun hc => not_close_P_O ps2 (Finset.mem_product.mp h2τ).2
      (Finset.mem_product.mp h₁).2 (close_symm hc))
  have h23 : ∀ x ∈ C2, ∀ y ∈ C3, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂
    rcases Finset.mem_biUnion.mp h₁ with ⟨σ, _, h1σ⟩
    exact not_close_prod_fst (not_close_P_O ps1 (Finset.mem_product.mp h1σ).1 (Finset.mem_product.mp h₂).1)
  have h24 : ∀ x ∈ C2, ∀ y ∈ C4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂
    rcases Finset.mem_biUnion.mp h₁ with ⟨σ, _, h1σ⟩
    rcases Finset.mem_biUnion.mp h₂ with ⟨τ, _, h2τ⟩
    by_cases hστ : σ = τ
    · subst hστ
      exact not_close_prod_snd (fun hc =>
        not_close_P_slice_ne ps2 (hφ σ) (Finset.mem_product.mp h2τ).2
          (Finset.mem_product.mp h1σ).2 (close_symm hc))
    · exact not_close_prod_fst (not_close_P_slice_ne ps1 hστ
        (Finset.mem_product.mp h1σ).1 (Finset.mem_product.mp h2τ).1)
  have h34 : ∀ x ∈ C3, ∀ y ∈ C4, ¬ (x = y ∨ (G ⊠ H).Adj x y) := by
    rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂
    rcases Finset.mem_biUnion.mp h₂ with ⟨τ, _, h2τ⟩
    exact not_close_prod_fst (not_close_O_slice ps1 (Finset.mem_product.mp h₁).1 (Finset.mem_product.mp h2τ).1)
  refine ⟨?_, ?_⟩
  · have hiC2 : (G ⊠ H).IsIndepSet (C2 : Set _) := by
      intro x hx y hy hne hadj
      rcases Finset.mem_biUnion.mp hx with ⟨σ₁, _, hx₁⟩
      rcases Finset.mem_biUnion.mp hy with ⟨σ₂, _, hy₂⟩
      rcases Finset.mem_product.mp hx₁ with ⟨hx1, hx2⟩
      rcases Finset.mem_product.mp hy₂ with ⟨hy1, hy2⟩
      rcases eq_or_strongProd_adj.mp (Or.inr hadj) with ⟨hc1, hc2⟩
      by_cases hσ : σ₁ = σ₂
      · subst hσ
        exact hne (Prod.ext (isIndepSet_eq_of_close (ps1.indep_P_finset σ₁) hx1 hy1 hc1)
          (isIndepSet_eq_of_close ps2.indep_X (ps2.mem_slice.mp hx2).1 (ps2.mem_slice.mp hy2).1 hc2))
      · exact not_close_slice_slice ps2 hσ hx2 hy2 hc2
    have hiC4 : (G ⊠ H).IsIndepSet (C4 : Set _) := by
      intro x hx y hy hne hadj
      rcases Finset.mem_biUnion.mp hx with ⟨τ₁, _, hx₁⟩
      rcases Finset.mem_biUnion.mp hy with ⟨τ₂, _, hy₂⟩
      rcases Finset.mem_product.mp hx₁ with ⟨hx1, hx2⟩
      rcases Finset.mem_product.mp hy₂ with ⟨hy1, hy2⟩
      rcases eq_or_strongProd_adj.mp (Or.inr hadj) with ⟨hc1, hc2⟩
      by_cases hτ : τ₁ = τ₂
      · subst hτ
        exact hne (Prod.ext (isIndepSet_eq_of_close ps1.indep_X
            (ps1.mem_slice.mp hx1).1 (ps1.mem_slice.mp hy1).1 hc1)
          (isIndepSet_eq_of_close (ps2.indep_P_finset (φ τ₁)) hx2 hy2 hc2))
      · exact not_close_slice_slice ps1 hτ hx1 hy1 hc1
    exact isIndepSet_union5
      (isIndepSet_prod ps1.indep_B ps2.indep_B)
      (isIndepSet_prod ps1.indep_S (isIndepSet_subset ps2.indep_X (fun _ hx => (ps2.mem_O.mp hx).1)))
      hiC2
      (isIndepSet_prod (isIndepSet_subset ps1.indep_X (fun _ hx => (ps1.mem_O.mp hx).1)) ps2.indep_S)
      hiC4 h01 h02 h03 h04 h12 h13 h14 h23 h24 h34
  · have hC2_card : C2.card = ps1.S.card * ∑ σ : ι, (ps2.slice σ).card := by
      have hpw : ∀ σ₁ ∈ (Finset.univ : Finset ι), ∀ σ₂ ∈ (Finset.univ : Finset ι), σ₁ ≠ σ₂ →
          Disjoint (ps1.P σ₁ ×ˢ ps2.slice σ₁) (ps1.P σ₂ ×ˢ ps2.slice σ₂) := by
        intro σ₁ _ σ₂ _ hne; rw [Finset.disjoint_left]; intro p h1 h2
        exact not_close_slice_slice ps2 hne (Finset.mem_product.mp h1).2
          (Finset.mem_product.mp h2).2 (Or.inl rfl)
      rw [Finset.card_biUnion hpw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.card_product, ps1.card_P σ]
    have hC4_card : C4.card = (∑ τ : ι, (ps1.slice τ).card) * ps2.S.card := by
      have hpw : ∀ τ₁ ∈ (Finset.univ : Finset ι), ∀ τ₂ ∈ (Finset.univ : Finset ι), τ₁ ≠ τ₂ →
          Disjoint (ps1.slice τ₁ ×ˢ ps2.P (φ τ₁)) (ps1.slice τ₂ ×ˢ ps2.P (φ τ₂)) := by
        intro τ₁ _ τ₂ _ hne; rw [Finset.disjoint_left]; intro p h1 h2
        exact not_close_slice_slice ps1 hne (Finset.mem_product.mp h1).1
          (Finset.mem_product.mp h2).1 (Or.inl rfl)
      rw [Finset.card_biUnion hpw, Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.card_product, ps2.card_P (φ τ)]
    change (C0 ∪ C1 ∪ C2 ∪ C3 ∪ C4).card = _
    rw [card_union5 (disjoint_of_not_close h01) (disjoint_of_not_close h02)
      (disjoint_of_not_close h03) (disjoint_of_not_close h04) (disjoint_of_not_close h12)
      (disjoint_of_not_close h13) (disjoint_of_not_close h14) (disjoint_of_not_close h23)
      (disjoint_of_not_close h24) (disjoint_of_not_close h34), hC2_card, hC4_card]
    simp only [C0, C1, C3, Finset.card_product, ps1.card_B, ps2.card_B]
    have hp1 := ps1.card_partition
    have hp2 := ps2.card_partition
    nlinarith

/-- Generalized multi-port product on `G ⊠ H` parameterized by ANY derangement
`φ : ι ≃ ι` (`hφ : ∀ σ, φ σ ≠ σ`). -/
noncomputable def prod (φ : ι ≃ ι) (hφ : ∀ σ : ι, φ σ ≠ σ)
    (ps1 : PortSystem G ι) (ps2 : PortSystem H ι) : PortSystem (G ⊠ H) ι := by
  classical
  let port12 : ι → V × W → V × W :=
    fun σ p => if p.1 ∈ ps1.S then (ps1.port σ p.1, p.2) else (p.1, ps2.port (φ σ) p.2)
  refine
    { I := prodI φ ps1 ps2
      S := (ps1.S ×ˢ ps2.O) ∪ (ps1.O ×ˢ ps2.S)
      X := ps1.X ×ˢ ps2.X
      port := port12
      indep_I := (prodI_indep_and_card φ hφ ps1 ps2).1
      S_sub_I := ?_
      priv := ?_
      indep_P := ?_
      self_mem := ?_
      indep_X := isIndepSet_prod ps1.indep_X ps2.indep_X
      disj_nbr := ?_ }
  · intro p hp
    simp only [prodI, Finset.mem_union] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl (Or.inl (Or.inl (Or.inr hp)))
    · exact Or.inl (Or.inr hp)
  · intro σ p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_product.mp hp with ⟨hs1, ho2⟩
      simp only [port12, hs1, ↓reduceIte]
      refine ⟨eq_or_strongProd_adj.mpr ⟨(ps1.priv σ p.1 hs1).1, Or.inl rfl⟩, ?_⟩
      intro u hu hcu
      rcases eq_or_strongProd_adj.mp hcu with ⟨hc1, hc2⟩
      have hp1 : ps1.port σ p.1 ∈ ps1.P σ := ps1.mem_P.mpr ⟨p.1, hs1, rfl⟩
      simp only [prodI, Finset.mem_union] at hu
      rcases hu with (((hu | hu) | hu) | hu) | hu
      · exact absurd hc1 (not_close_B_P ps1 (Finset.mem_product.mp hu).1 hp1)
      · rcases Finset.mem_product.mp hu with ⟨hu1, hu2⟩
        exact Prod.ext ((ps1.priv σ p.1 hs1).2 u.1 (ps1.S_sub_I hu1) hc1)
          (isIndepSet_eq_of_close ps2.indep_X (ps2.mem_O.mp hu2).1 (ps2.mem_O.mp ho2).1 hc2)
      · rcases Finset.mem_biUnion.mp hu with ⟨τ, _, huτ⟩
        exact absurd (close_symm hc2) (not_close_O_slice ps2 ho2 (Finset.mem_product.mp huτ).2)
      · exact absurd (close_symm hc1) (not_close_P_O ps1 hp1 (Finset.mem_product.mp hu).1)
      · rcases Finset.mem_biUnion.mp hu with ⟨τ, _, huτ⟩
        exact absurd hc2 (not_close_P_O ps2 (Finset.mem_product.mp huτ).2 ho2)
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      have hns1 : p.1 ∉ ps1.S := not_mem_S_of_mem_O ps1 ho1
      simp only [port12, hns1, ↓reduceIte]
      refine ⟨eq_or_strongProd_adj.mpr ⟨Or.inl rfl, (ps2.priv (φ σ) p.2 hs2).1⟩, ?_⟩
      intro u hu hcu
      rcases eq_or_strongProd_adj.mp hcu with ⟨hc1, hc2⟩
      have hp2 : ps2.port (φ σ) p.2 ∈ ps2.P (φ σ) := ps2.mem_P.mpr ⟨p.2, hs2, rfl⟩
      simp only [prodI, Finset.mem_union] at hu
      rcases hu with (((hu | hu) | hu) | hu) | hu
      · exact absurd hc2 (not_close_B_P ps2 (Finset.mem_product.mp hu).2 hp2)
      · exact absurd hc1 (not_close_S_O ps1 (Finset.mem_product.mp hu).1 ho1)
      · rcases Finset.mem_biUnion.mp hu with ⟨τ, _, huτ⟩
        exact absurd hc1 (not_close_P_O ps1 (Finset.mem_product.mp huτ).1 ho1)
      · rcases Finset.mem_product.mp hu with ⟨hu1, hu2⟩
        exact Prod.ext (isIndepSet_eq_of_close ps1.indep_X (ps1.mem_O.mp hu1).1 (ps1.mem_O.mp ho1).1 hc1)
          ((ps2.priv (φ σ) p.2 hs2).2 u.2 (ps2.S_sub_I hu2) hc2)
      · rcases Finset.mem_biUnion.mp hu with ⟨τ, _, huτ⟩
        exact absurd (close_symm hc1) (not_close_O_slice ps1 ho1 (Finset.mem_product.mp huτ).1)
  · rintro σ _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne hadj
    rcases eq_or_strongProd_adj.mp (Or.inr hadj) with ⟨hc1, hc2⟩
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · rcases Finset.mem_product.mp hp with ⟨hs1, ho2⟩
      rcases Finset.mem_product.mp hq with ⟨hs1', ho2'⟩
      simp only [port12, hs1, hs1', ↓reduceIte] at hne hc1 hc2
      exact hne (Prod.ext
        (isIndepSet_eq_of_close (ps1.indep_P_finset σ) (ps1.mem_P.mpr ⟨p.1, hs1, rfl⟩)
          (ps1.mem_P.mpr ⟨q.1, hs1', rfl⟩) hc1)
        (isIndepSet_eq_of_close ps2.indep_X (ps2.mem_O.mp ho2).1 (ps2.mem_O.mp ho2').1 hc2))
    · rcases Finset.mem_product.mp hp with ⟨hs1, _⟩
      rcases Finset.mem_product.mp hq with ⟨ho1', _⟩
      have hns1' : q.1 ∉ ps1.S := not_mem_S_of_mem_O ps1 ho1'
      simp only [port12, hs1, hns1', ↓reduceIte] at hc1
      exact not_close_P_O ps1 (ps1.mem_P.mpr ⟨p.1, hs1, rfl⟩) ho1' hc1
    · rcases Finset.mem_product.mp hp with ⟨ho1, _⟩
      rcases Finset.mem_product.mp hq with ⟨hs1', _⟩
      have hns1 : p.1 ∉ ps1.S := not_mem_S_of_mem_O ps1 ho1
      simp only [port12, hns1, hs1', ↓reduceIte] at hc1
      exact not_close_P_O ps1 (ps1.mem_P.mpr ⟨q.1, hs1', rfl⟩) ho1 (close_symm hc1)
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      rcases Finset.mem_product.mp hq with ⟨ho1', hs2'⟩
      have hns1 : p.1 ∉ ps1.S := not_mem_S_of_mem_O ps1 ho1
      have hns1' : q.1 ∉ ps1.S := not_mem_S_of_mem_O ps1 ho1'
      simp only [port12, hns1, hns1', ↓reduceIte] at hne hc1 hc2
      exact hne (Prod.ext
        (isIndepSet_eq_of_close ps1.indep_X (ps1.mem_O.mp ho1).1 (ps1.mem_O.mp ho1').1 hc1)
        (isIndepSet_eq_of_close (ps2.indep_P_finset (φ σ)) (ps2.mem_P.mpr ⟨p.2, hs2, rfl⟩)
          (ps2.mem_P.mpr ⟨q.2, hs2', rfl⟩) hc2))
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_product.mp hp with ⟨hs1, _⟩
      rcases ps1.self_mem p.1 hs1 with ⟨σ, hσ⟩
      exact ⟨σ, by simp only [port12, hs1, ↓reduceIte, hσ]⟩
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      have hns1 : p.1 ∉ ps1.S := not_mem_S_of_mem_O ps1 ho1
      rcases ps2.self_mem p.2 hs2 with ⟨τ, hτ⟩
      exact ⟨φ.symm τ, by simp only [port12, hns1, ↓reduceIte, Equiv.apply_symm_apply, hτ]⟩
  · intro x hx σ₁ σ₂ hne ⟨⟨p, hp, hcp⟩, ⟨q, hq, hcq⟩⟩
    rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
    rcases eq_or_strongProd_adj.mp hcp with ⟨hp1, hp2⟩
    rcases eq_or_strongProd_adj.mp hcq with ⟨hq1, hq2⟩
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · rcases Finset.mem_product.mp hp with ⟨hs1, _⟩
      rcases Finset.mem_product.mp hq with ⟨hs1', _⟩
      simp only [port12, hs1, hs1', ↓reduceIte] at hp1 hq1
      exact ps1.disj_nbr x.1 hx1 σ₁ σ₂ hne ⟨⟨p.1, hs1, hp1⟩, ⟨q.1, hs1', hq1⟩⟩
    · rcases Finset.mem_product.mp hp with ⟨hs1, _⟩
      rcases Finset.mem_product.mp hq with ⟨ho1', _⟩
      have hns1' : q.1 ∉ ps1.S := not_mem_S_of_mem_O ps1 ho1'
      simp only [port12, hs1, hns1', ↓reduceIte] at hp1 hq1
      exact (ps1.mem_O.mp ((mem_O_of_mem_X_close ps1 hx1).mp ⟨q.1, ho1', hq1⟩)).2 σ₁ ⟨p.1, hs1, hp1⟩
    · rcases Finset.mem_product.mp hp with ⟨ho1, _⟩
      rcases Finset.mem_product.mp hq with ⟨hs1', _⟩
      have hns1 : p.1 ∉ ps1.S := not_mem_S_of_mem_O ps1 ho1
      simp only [port12, hns1, hs1', ↓reduceIte] at hp1 hq1
      exact (ps1.mem_O.mp ((mem_O_of_mem_X_close ps1 hx1).mp ⟨p.1, ho1, hp1⟩)).2 σ₂ ⟨q.1, hs1', hq1⟩
    · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
      rcases Finset.mem_product.mp hq with ⟨ho1', hs2'⟩
      have hns1 : p.1 ∉ ps1.S := not_mem_S_of_mem_O ps1 ho1
      have hns1' : q.1 ∉ ps1.S := not_mem_S_of_mem_O ps1 ho1'
      simp only [port12, hns1, hns1', ↓reduceIte] at hp2 hq2
      exact ps2.disj_nbr x.2 hx2 (φ σ₁) (φ σ₂) (fun h => hne (φ.injective h))
        ⟨⟨p.2, hs2, hp2⟩, ⟨q.2, hs2', hq2⟩⟩

theorem prod_profile (φ : ι ≃ ι) (hφ : ∀ σ : ι, φ σ ≠ σ)
    (ps1 : PortSystem G ι) (ps2 : PortSystem H ι) :
    (prod φ hφ ps1 ps2).profile = ps1.profile.star ps2.profile := by
  classical
  have hI : (prod φ hφ ps1 ps2).I.card =
      (ps1.I.card - ps1.S.card) * (ps2.I.card - ps2.S.card) +
      ps1.S.card * ps2.X.card + ps1.X.card * ps2.S.card :=
    (prodI_indep_and_card φ hφ ps1 ps2).2
  have hS : (prod φ hφ ps1 ps2).S.card =
      ps1.S.card * ps2.O.card + ps1.O.card * ps2.S.card := by
    have hdisj : Disjoint (ps1.S ×ˢ ps2.O) (ps1.O ×ˢ ps2.S) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact not_mem_S_of_mem_O ps1 (Finset.mem_product.mp h2).1 (Finset.mem_product.mp h1).1
    change ((ps1.S ×ˢ ps2.O) ∪ (ps1.O ×ˢ ps2.S)).card = _
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product]
  have hX : (prod φ hφ ps1 ps2).X.card = ps1.X.card * ps2.X.card := Finset.card_product _ _
  have hslice_eq : ∀ σ : ι, (prod φ hφ ps1 ps2).slice σ =
      (ps1.slice σ ×ˢ ps2.O) ∪ (ps1.O ×ˢ ps2.slice (φ σ)) := by
    intro σ
    ext ⟨x₁, x₂⟩
    have hXmem : (x₁, x₂) ∈ (prod φ hφ ps1 ps2).X ↔ x₁ ∈ ps1.X ∧ x₂ ∈ ps2.X := Finset.mem_product
    simp only [mem_slice, hXmem, Finset.mem_union, Finset.mem_product]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, ⟨⟨a, b⟩, hp, hc⟩⟩
      rcases eq_or_strongProd_adj.mp hc with ⟨hc1, hc2⟩
      rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_product.mp hp with ⟨hs1, ho2⟩
        simp only [prod, hs1, ↓reduceIte] at hc1 hc2
        exact Or.inl ⟨⟨hx1, ⟨a, hs1, hc1⟩⟩, (mem_O_of_mem_X_close ps2 hx2).mp ⟨b, ho2, hc2⟩⟩
      · rcases Finset.mem_product.mp hp with ⟨ho1, hs2⟩
        have hns1 : a ∉ ps1.S := not_mem_S_of_mem_O ps1 ho1
        simp only [prod, hns1, ↓reduceIte] at hc1 hc2
        exact Or.inr ⟨(mem_O_of_mem_X_close ps1 hx1).mp ⟨a, ho1, hc1⟩, ⟨hx2, ⟨b, hs2, hc2⟩⟩⟩
    · rintro (⟨⟨hx1, ⟨s₁, hs₁, hc1⟩⟩, ho2⟩ | ⟨ho1, ⟨hx2, ⟨s₂, hs₂, hc2⟩⟩⟩)
      · refine ⟨⟨hx1, (ps2.mem_O.mp ho2).1⟩,
          ⟨(s₁, x₂), Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hs₁, ho2⟩), ?_⟩⟩
        simp only [prod, hs₁, ↓reduceIte]
        exact eq_or_strongProd_adj.mpr ⟨hc1, Or.inl rfl⟩
      · have hns1 : x₁ ∉ ps1.S := not_mem_S_of_mem_O ps1 ho1
        refine ⟨⟨(ps1.mem_O.mp ho1).1, hx2⟩,
          ⟨(x₁, s₂), Finset.mem_union_right _ (Finset.mem_product.mpr ⟨ho1, hs₂⟩), ?_⟩⟩
        simp only [prod, hns1, ↓reduceIte]
        exact eq_or_strongProd_adj.mpr ⟨Or.inl rfl, hc2⟩
  have hslice_card : ∀ σ : ι, ((prod φ hφ ps1 ps2).slice σ).card =
      (ps1.slice σ).card * ps2.O.card + ps1.O.card * (ps2.slice (φ σ)).card := by
    intro σ
    rw [hslice_eq σ]
    have hdisj : Disjoint (ps1.slice σ ×ˢ ps2.O) (ps1.O ×ˢ ps2.slice (φ σ)) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact (ps1.mem_O.mp (Finset.mem_product.mp h2).1).2 σ
        (ps1.mem_slice.mp (Finset.mem_product.mp h1).1).2
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product]
  have hsum_slice : ∑ σ : ι, ((prod φ hφ ps1 ps2).slice σ).card =
      (∑ σ : ι, (ps1.slice σ).card) * ps2.O.card +
      ps1.O.card * (∑ τ : ι, (ps2.slice τ).card) := by
    simp_rw [hslice_card]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      Equiv.sum_comp φ (fun τ => (ps2.slice τ).card)]
  have hO : (prod φ hφ ps1 ps2).O.card =
      ps1.O.card * ps2.O.card + (ps1.X.card - ps1.O.card) * (ps2.X.card - ps2.O.card) := by
    have hp := (prod φ hφ ps1 ps2).card_partition
    have hp1 := ps1.card_partition
    have hp2 := ps2.card_partition
    rw [hsum_slice, hX] at hp
    have h1 : ∑ σ : ι, (ps1.slice σ).card = ps1.X.card - ps1.O.card := by omega
    have h2 : ∑ τ : ι, (ps2.slice τ).card = ps2.X.card - ps2.O.card := by omega
    rw [h1, h2] at hp
    have hle1 : ps1.O.card ≤ ps1.X.card := by omega
    have hle2 : ps2.O.card ≤ ps2.X.card := by omega
    zify [hle1, hle2] at hp ⊢
    nlinarith
  apply Profile.ext
  · show (prod φ hφ ps1 ps2).I.card =
        (ps1.I.card - ps1.S.card) * (ps2.I.card - ps2.S.card) +
          ps1.X.card * ps2.S.card + ps1.S.card * ps2.X.card
    omega
  · show (prod φ hφ ps1 ps2).S.card =
        ps1.O.card * ps2.S.card + ps1.S.card * ps2.O.card
    omega
  · exact hX
  · exact hO

def finShift (k : ℕ) (hk : 2 ≤ k) : Fin k ≃ Fin k where
  toFun := fun i => ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩
  invFun := fun i => ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
  left_inv := by
    intro ⟨i, hi⟩; ext; dsimp only
    by_cases h : i + 1 < k
    · rw [Nat.mod_eq_of_lt h, show i + 1 + k - 1 = i + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hi]
    · have hik : i + 1 = k := by omega
      rw [hik, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
  right_inv := by
    intro ⟨i, hi⟩; ext; dsimp only
    by_cases h : i = 0
    · subst h
      rw [Nat.zero_add, Nat.mod_eq_of_lt (show k - 1 < k by omega),
        show k - 1 + 1 = k by omega, Nat.mod_self]
    · rw [show i + k - 1 = (i - 1) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show i - 1 < k by omega),
        show i - 1 + 1 = i by omega, Nat.mod_eq_of_lt hi]

theorem finShift_ne (k : ℕ) (hk : 2 ≤ k) (i : Fin k) : finShift k hk i ≠ i := by
  intro heq
  rcases i with ⟨i, hi⟩
  have hval : (i + 1) % k = i := congrArg Fin.val heq
  by_cases h : i + 1 < k
  · rw [Nat.mod_eq_of_lt h] at hval; omega
  · have hik : i + 1 = k := by omega
    rw [hik, Nat.mod_self] at hval; omega

def ofColoring {k : ℕ} (hk : 2 ≤ k)
    (I S X : Finset V) (q : V → V) (col : V → Fin k)
    (indep_I : G.IsIndepSet (I : Set V))
    (S_sub_I : S ⊆ I)
    (priv_q : ∀ s ∈ S, (q s = s ∨ G.Adj (q s) s) ∧ ∀ u ∈ I, (u = q s ∨ G.Adj u (q s)) → u = s)
    (proper_col : ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → col s₁ = col s₂ → ¬ G.Adj (q s₁) (q s₂))
    (indep_X : G.IsIndepSet (X : Set V))
    (disj_nbr : ∀ x ∈ X, ∀ σ₁ σ₂ : Fin k, σ₁ ≠ σ₂ →
      ¬ ((∃ s ∈ S, (if col s = σ₁ then q s else s) = x ∨ G.Adj (if col s = σ₁ then q s else s) x) ∧
         (∃ s ∈ S, (if col s = σ₂ then q s else s) = x ∨ G.Adj (if col s = σ₂ then q s else s) x))) :
    PortSystem G (Fin k) where
  I := I; S := S; X := X; port := fun σ s => if col s = σ then q s else s
  indep_I := indep_I; S_sub_I := S_sub_I
  priv := by
    intro σ s hs
    by_cases hc : col s = σ
    · rw [if_pos hc]; exact priv_q s hs
    · rw [if_neg hc]
      exact ⟨Or.inl rfl, fun u hu hcu => isIndepSet_eq_of_close indep_I hu (S_sub_I hs) hcu⟩
  indep_P := by
    rintro σ _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩ hne hadj
    have hsne : s₁ ≠ s₂ := fun h => hne (by rw [h])
    by_cases hc1 : col s₁ = σ <;> by_cases hc2 : col s₂ = σ
    · simp only [hc1, hc2, ↓reduceIte] at hadj
      exact proper_col s₁ hs₁ s₂ hs₂ hsne (hc1.trans hc2.symm) hadj
    · simp only [hc1, hc2, ↓reduceIte] at hadj
      exact hsne ((priv_q s₁ hs₁).2 s₂ (S_sub_I hs₂) (Or.inr hadj.symm)).symm
    · simp only [hc1, hc2, ↓reduceIte] at hadj
      exact hsne ((priv_q s₂ hs₂).2 s₁ (S_sub_I hs₁) (Or.inr hadj))
    · simp only [hc1, hc2, ↓reduceIte] at hadj
      exact indep_I (S_sub_I hs₁) (S_sub_I hs₂) hsne hadj
  self_mem := by
    intro s _
    refine ⟨finShift k hk (col s), ?_⟩
    have hne : col s ≠ finShift k hk (col s) := (finShift_ne k hk (col s)).symm
    simp [hne]
  indep_X := indep_X; disj_nbr := disj_nbr

def ofHeteroGadget (g : HeteroGadget G) : PortSystem G Bool where
  I := g.core.I; S := g.core.S; X := g.aux.X
  port := fun b s => if b then g.core.f1 s else g.core.f0 s
  indep_I := g.core.indep_I; S_sub_I := g.core.S_sub_I
  priv := fun b s hs => by cases b <;> [exact g.core.priv0 s hs; exact g.core.priv1 s hs]
  indep_P := fun b => by cases b <;> [exact g.core.indep_P0; exact g.core.indep_P1]
  self_mem := fun s hs => by rcases g.core.self_mem s hs with h0 | h1; exact ⟨false, h0⟩; exact ⟨true, h1⟩
  indep_X := g.aux.indep_X
  disj_nbr := by
    intro x hx b₁ b₂ hne ⟨h1, h2⟩
    cases b₁ <;> cases b₂
    · exact hne rfl
    · exact g.aux.disj_nbr x hx ⟨h1, h2⟩
    · exact g.aux.disj_nbr x hx ⟨h2, h1⟩
    · exact hne rfl

def toHeteroGadget (ps : PortSystem G Bool) : HeteroGadget G where
  core :=
    { I := ps.I, S := ps.S, f0 := ps.port false, f1 := ps.port true
      indep_I := ps.indep_I, S_sub_I := ps.S_sub_I
      priv0 := ps.priv false, priv1 := ps.priv true
      indep_P0 := ps.indep_P false, indep_P1 := ps.indep_P true
      self_mem := fun s hs => by rcases ps.self_mem s hs with ⟨b, hb⟩; cases b; exact Or.inl hb; exact Or.inr hb }
  aux :=
    { X := ps.X, indep_X := ps.indep_X
      disj_nbr := fun x hx h => ps.disj_nbr x hx false true (by decide) h }

theorem ofHeteroGadget_profile (g : HeteroGadget G) :
    (ofHeteroGadget g).profile = g.asymProfile.toProfile := by
  classical
  have hO : (ofHeteroGadget g).O = g.aux.OSlice := by
    ext x
    simp only [mem_O, AuxCode.mem_OSlice, ofHeteroGadget, inPNbr, PortCore.inP0Nbr,
      PortCore.inP1Nbr, Bool.forall_bool]
    tauto
  apply Profile.ext
  · rfl
  · rfl
  · rfl
  · exact congrArg Finset.card hO

end PortSystem

/-! ============================================================================
    PART 3: Layered Interior-Pair Auxiliary Upgrading (`LayeredTuple G`)
    ============================================================================ -/

structure LayeredProfile where
  outer : AsymProfile
  bX : ℕ
  e : ℕ
  dY : ℕ
  hY : ℕ
  vY : ℕ
  pY : ℕ
  hbXd : bX ≤ outer.d
  hYsum : dY + hY + vY = e
  hpYdY : pY ≤ dY

namespace LayeredProfile

def upgradeProd (p q : LayeredProfile) : AsymProfile where
  a := (p.outer.a - p.outer.b) * (q.outer.a - q.outer.b) +
       p.outer.b * q.outer.c + p.outer.c * q.outer.b
  b := p.outer.b * q.outer.d + p.outer.d * q.outer.b
  c := (p.outer.c - p.bX) * (q.outer.c - q.bX) + p.bX * q.e + p.e * q.bX
  d := (p.outer.d - p.bX) * (q.outer.d - q.bX) +
       (p.outer.h + p.outer.v) * (q.outer.h + q.outer.v) +
       p.bX * q.dY + p.dY * q.bX
  h := p.outer.h * (q.outer.d - q.bX) + (p.outer.d - p.bX) * q.outer.v +
       p.hY * q.bX + p.bX * q.vY
  v := p.outer.v * (q.outer.d - q.bX) + (p.outer.d - p.bX) * q.outer.h +
       p.vY * q.bX + p.bX * q.hY
  hba := by
    have h1 : p.outer.b * q.outer.d ≤ p.outer.b * q.outer.c := Nat.mul_le_mul_left _ q.outer.hdc
    have h2 : p.outer.d * q.outer.b ≤ p.outer.c * q.outer.b := Nat.mul_le_mul_right _ p.outer.hdc
    omega
  hdhv := by
    have hp1 := p.outer.hdhv; have hq1 := q.outer.hdhv
    have hp2 := p.hbXd; have hq2 := q.hbXd
    have hpY := p.hYsum; have hqY := q.hYsum
    have hpc : p.bX ≤ p.outer.c := by omega
    have hqc : q.bX ≤ q.outer.c := by omega
    zify [hp2, hq2, hpc, hqc]; nlinarith

end LayeredProfile

set_option linter.unusedFintypeInType false in
structure LayeredTuple {V : Type*} [Fintype V] (G : SimpleGraph V) where
  outer : HeteroGadget G
  intCore : PortCore G
  intCore_I : intCore.I = outer.aux.X
  intCore_P0_outside : ∀ s ∈ intCore.S,
    ¬ outer.core.inP0Nbr (intCore.f0 s) ∧ ¬ outer.core.inP1Nbr (intCore.f0 s)
  intCore_P1_outside : ∀ s ∈ intCore.S,
    ¬ outer.core.inP0Nbr (intCore.f1 s) ∧ ¬ outer.core.inP1Nbr (intCore.f1 s)
  intAux : AuxCode intCore
  intAux_outer : ∀ y ∈ intAux.X, ¬ (outer.core.inP0Nbr y ∧ outer.core.inP1Nbr y)

namespace LayeredTuple

variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

def intGadget (L : LayeredTuple G) : HeteroGadget G := ⟨L.intCore, L.intAux⟩

def outerAuxY (L : LayeredTuple G) : AuxCode L.outer.core where
  X := L.intAux.X; indep_X := L.intAux.indep_X; disj_nbr := L.intAux_outer

theorem intCore_S_sub_outerO (L : LayeredTuple G) : L.intCore.S ⊆ L.outer.aux.OSlice := by
  intro s hs
  rw [L.outer.aux.mem_OSlice]
  refine ⟨L.intCore_I ▸ L.intCore.S_sub_I hs, ?_⟩
  rcases L.intCore.self_mem s hs with h0 | h1
  · exact h0 ▸ L.intCore_P0_outside s hs
  · exact h1 ▸ L.intCore_P1_outside s hs

noncomputable def pureOY (L : LayeredTuple G) : Finset V := by
  classical
  exact L.intAux.OSlice.filter (fun y => ¬ L.outer.core.inP0Nbr y ∧ ¬ L.outer.core.inP1Nbr y)

theorem mem_pureOY (L : LayeredTuple G) {y : V} :
    y ∈ L.pureOY ↔
      y ∈ L.intAux.OSlice ∧ ¬ L.outer.core.inP0Nbr y ∧ ¬ L.outer.core.inP1Nbr y := by
  classical simp [pureOY]

noncomputable def layeredProfile (L : LayeredTuple G) : LayeredProfile where
  outer := L.outer.asymProfile
  bX := L.intCore.S.card
  e := L.intAux.X.card
  dY := L.outerAuxY.OSlice.card
  hY := L.outerAuxY.HSlice.card
  vY := L.outerAuxY.VSlice.card
  pY := L.pureOY.card
  hbXd := Finset.card_le_card L.intCore_S_sub_outerO
  hYsum := L.outerAuxY.card_partition
  hpYdY := by
    apply Finset.card_le_card; intro y hy
    rcases L.mem_pureOY.mp hy with ⟨hyO, h0, h1⟩
    exact L.outerAuxY.mem_OSlice.mpr ⟨(L.intAux.mem_OSlice.mp hyO).1, h0, h1⟩

theorem intCore_mem_outerO_nbr (L : LayeredTuple G) {x : V}
    (hx : x ∈ L.intCore.S ∨ x ∈ L.intCore.P0 ∨ x ∈ L.intCore.P1) :
    (¬ L.outer.core.inP0Nbr x ∧ ¬ L.outer.core.inP1Nbr x) ∧
    (∃ o ∈ L.outer.aux.OSlice, o = x ∨ G.Adj o x) := by
  rcases hx with hs | hp0 | hp1
  · have ho := L.intCore_S_sub_outerO hs
    exact ⟨(L.outer.aux.mem_OSlice.mp ho).2, ⟨x, ho, Or.inl rfl⟩⟩
  · rcases L.intCore.mem_P0.mp hp0 with ⟨s, hs, rfl⟩
    exact ⟨L.intCore_P0_outside s hs,
      ⟨s, L.intCore_S_sub_outerO hs, close_symm (L.intCore.priv0 s hs).1⟩⟩
  · rcases L.intCore.mem_P1.mp hp1 with ⟨s, hs, rfl⟩
    exact ⟨L.intCore_P1_outside s hs,
      ⟨s, L.intCore_S_sub_outerO hs, close_symm (L.intCore.priv1 s hs).1⟩⟩

noncomputable def upgradedAux (L1 : LayeredTuple G) (L2 : LayeredTuple H) :
    AuxCode (HeteroGadget.prodCore L1.outer L2.outer) where
  X := HeteroGadget.prodI L1.intGadget L2.intGadget
  indep_X := HeteroGadget.prodI_isIndepSet L1.intGadget L2.intGadget
  disj_nbr := by
    intro x hx ⟨h0, h1⟩
    simp only [HeteroGadget.prodI, Finset.mem_union, Finset.mem_product] at hx
    rcases hx with (((((⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩) |
      ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩
    · exact (L1.outer.prod L2.outer).aux.disj_nbr x
        (Finset.mem_product.mpr ⟨L1.intCore_I ▸ (L1.intCore.mem_B.mp hx1).1,
          L2.intCore_I ▸ (L2.intCore.mem_B.mp hx2).1⟩) ⟨h0, h1⟩
    · have h1' := (intCore_mem_outerO_nbr L1 (Or.inl hx1)).1
      rw [HeteroGadget.prodCore_inP0Nbr_iff] at h0; rw [HeteroGadget.prodCore_inP1Nbr_iff] at h1
      rcases h0 with ⟨h0a, _⟩ | ⟨_, h0b⟩
      · exact h1'.1 h0a
      · rcases h1 with ⟨h1a, _⟩ | ⟨_, h1b⟩
        · exact h1'.2 h1a
        · exact L2.intAux_outer x.2 (L2.intAux.mem_OSlice.mp hx2).1 ⟨h1b, h0b⟩
    · have h1' := (intCore_mem_outerO_nbr L1 (Or.inr (Or.inl hx1))).1
      rw [HeteroGadget.prodCore_inP0Nbr_iff] at h0; rw [HeteroGadget.prodCore_inP1Nbr_iff] at h1
      rcases h0 with ⟨h0a, _⟩ | ⟨_, h0b⟩
      · exact h1'.1 h0a
      · rcases h1 with ⟨h1a, _⟩ | ⟨_, h1b⟩
        · exact h1'.2 h1a
        · exact L2.intAux_outer x.2 (L2.intAux.mem_HSlice.mp hx2).1 ⟨h1b, h0b⟩
    · have h1' := (intCore_mem_outerO_nbr L1 (Or.inr (Or.inr hx1))).1
      rw [HeteroGadget.prodCore_inP0Nbr_iff] at h0; rw [HeteroGadget.prodCore_inP1Nbr_iff] at h1
      rcases h0 with ⟨h0a, _⟩ | ⟨_, h0b⟩
      · exact h1'.1 h0a
      · rcases h1 with ⟨h1a, _⟩ | ⟨_, h1b⟩
        · exact h1'.2 h1a
        · exact L2.intAux_outer x.2 (L2.intAux.mem_VSlice.mp hx2).1 ⟨h1b, h0b⟩
    · have h2' := (intCore_mem_outerO_nbr L2 (Or.inl hx2)).1
      rw [HeteroGadget.prodCore_inP0Nbr_iff] at h0; rw [HeteroGadget.prodCore_inP1Nbr_iff] at h1
      rcases h0 with ⟨h0a, _⟩ | ⟨_, h0b⟩
      · rcases h1 with ⟨h1a, _⟩ | ⟨_, h1b⟩
        · exact L1.intAux_outer x.1 (L1.intAux.mem_OSlice.mp hx1).1 ⟨h0a, h1a⟩
        · exact h2'.1 h1b
      · exact h2'.2 h0b
    · have h2' := (intCore_mem_outerO_nbr L2 (Or.inr (Or.inr hx2))).1
      rw [HeteroGadget.prodCore_inP0Nbr_iff] at h0; rw [HeteroGadget.prodCore_inP1Nbr_iff] at h1
      rcases h0 with ⟨h0a, _⟩ | ⟨_, h0b⟩
      · rcases h1 with ⟨h1a, _⟩ | ⟨_, h1b⟩
        · exact L1.intAux_outer x.1 (L1.intAux.mem_HSlice.mp hx1).1 ⟨h0a, h1a⟩
        · exact h2'.1 h1b
      · exact h2'.2 h0b
    · have h2' := (intCore_mem_outerO_nbr L2 (Or.inr (Or.inl hx2))).1
      rw [HeteroGadget.prodCore_inP0Nbr_iff] at h0; rw [HeteroGadget.prodCore_inP1Nbr_iff] at h1
      rcases h0 with ⟨h0a, _⟩ | ⟨_, h0b⟩
      · rcases h1 with ⟨h1a, _⟩ | ⟨_, h1b⟩
        · exact L1.intAux_outer x.1 (L1.intAux.mem_VSlice.mp hx1).1 ⟨h0a, h1a⟩
        · exact h2'.1 h1b
      · exact h2'.2 h0b

noncomputable def upgradeProd (L1 : LayeredTuple G) (L2 : LayeredTuple H) :
    HeteroGadget (G ⊠ H) where
  core := HeteroGadget.prodCore L1.outer L2.outer
  aux := upgradedAux L1 L2

private theorem mem_BX_outerO_sdiff [DecidableEq V] (L : LayeredTuple G) {x : V} :
    x ∈ L.intCore.B ∧ x ∈ L.outer.aux.OSlice ↔ x ∈ L.outer.aux.OSlice \ L.intCore.S := by
  simp only [L.intCore.mem_B, L.intCore_I, Finset.mem_sdiff]
  exact ⟨fun ⟨⟨_, hns⟩, ho⟩ => ⟨ho, hns⟩,
    fun ⟨ho, hns⟩ => ⟨⟨(L.outer.aux.mem_OSlice.mp ho).1, hns⟩, ho⟩⟩

private theorem mem_BX_HSlice (L : LayeredTuple G) {x : V} :
    x ∈ L.intCore.B ∧ L.outer.core.inP0Nbr x ↔ x ∈ L.outer.aux.HSlice := by
  simp only [L.intCore.mem_B, L.intCore_I, L.outer.aux.mem_HSlice]
  refine ⟨fun ⟨⟨hx, _⟩, h0⟩ => ⟨hx, h0⟩, fun ⟨hx, h0⟩ => ⟨⟨hx, ?_⟩, h0⟩⟩
  exact fun hs => (L.outer.aux.mem_OSlice.mp (L.intCore_S_sub_outerO hs)).2.1 h0

private theorem mem_BX_VSlice (L : LayeredTuple G) {x : V} :
    x ∈ L.intCore.B ∧ L.outer.core.inP1Nbr x ↔ x ∈ L.outer.aux.VSlice := by
  simp only [L.intCore.mem_B, L.intCore_I, L.outer.aux.mem_VSlice]
  refine ⟨fun ⟨⟨hx, _⟩, h1⟩ => ⟨hx, h1⟩, fun ⟨hx, h1⟩ => ⟨⟨hx, ?_⟩, h1⟩⟩
  exact fun hs => (L.outer.aux.mem_OSlice.mp (L.intCore_S_sub_outerO hs)).2.2 h1

private theorem intAux_filter_part (L : LayeredTuple G) (Q : V → Prop) [DecidablePred Q] :
    (L.intAux.OSlice.filter Q).card + (L.intAux.HSlice.filter Q).card +
      (L.intAux.VSlice.filter Q).card = (L.intAux.X.filter Q).card := by
  classical
  have hdisj_OH : Disjoint (L.intAux.OSlice.filter Q) (L.intAux.HSlice.filter Q) := by
    rw [Finset.disjoint_left]; intro y hO hH
    exact (L.intAux.mem_OSlice.mp (Finset.mem_filter.mp hO).1).2.1
      (L.intAux.mem_HSlice.mp (Finset.mem_filter.mp hH).1).2
  have hdisj_OH_V : Disjoint (L.intAux.OSlice.filter Q ∪ L.intAux.HSlice.filter Q)
      (L.intAux.VSlice.filter Q) := by
    rw [Finset.disjoint_left]; intro y hOH hV
    have hV' := L.intAux.mem_VSlice.mp (Finset.mem_filter.mp hV).1
    rcases Finset.mem_union.mp hOH with hO | hH
    · exact (L.intAux.mem_OSlice.mp (Finset.mem_filter.mp hO).1).2.2 hV'.2
    · exact L.intAux.disj_nbr y hV'.1
        ⟨(L.intAux.mem_HSlice.mp (Finset.mem_filter.mp hH).1).2, hV'.2⟩
  have hunion : L.intAux.OSlice.filter Q ∪ L.intAux.HSlice.filter Q ∪
      L.intAux.VSlice.filter Q = L.intAux.X.filter Q := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, L.intAux.mem_OSlice,
      L.intAux.mem_HSlice, L.intAux.mem_VSlice]
    by_cases hy : y ∈ L.intAux.X <;> by_cases hQ : Q y
    · by_cases h0 : L.intCore.inP0Nbr y <;> by_cases h1 : L.intCore.inP1Nbr y <;>
        simp [hy, hQ, h0, h1]
    · simp [hy, hQ]
    · simp [hy, hQ]
    · simp [hy, hQ]
  rw [← Finset.card_union_of_disjoint hdisj_OH, ← Finset.card_union_of_disjoint hdisj_OH_V, hunion]

private theorem upgradeProd_HSlice_card (L1 : LayeredTuple G) (L2 : LayeredTuple H) :
    (L1.upgradeProd L2).aux.HSlice.card =
      L1.outer.aux.HSlice.card * (L2.outer.aux.OSlice.card - L2.intCore.S.card) +
      (L1.outer.aux.OSlice.card - L1.intCore.S.card) * L2.outer.aux.VSlice.card +
      L1.outerAuxY.HSlice.card * L2.intCore.S.card +
      L1.intCore.S.card * L2.outerAuxY.VSlice.card := by
  classical
  have hHs : (L1.upgradeProd L2).aux.HSlice =
      (HeteroGadget.prodI L1.intGadget L2.intGadget).filter
        (fun p => (L1.upgradeProd L2).core.inP0Nbr p) := by
    ext p; simp [AuxCode.mem_HSlice, upgradeProd, upgradedAux]
  rw [hHs, (HeteroGadget.prodI_indep_and_filter L1.intGadget L2.intGadget).2]
  have hK0 : ((L1.intCore.B ×ˢ L2.intCore.B).filter
      (fun p => (L1.upgradeProd L2).core.inP0Nbr p)).card =
      L1.outer.aux.HSlice.card * (L2.outer.aux.OSlice.card - L2.intCore.S.card) +
      (L1.outer.aux.OSlice.card - L1.intCore.S.card) * L2.outer.aux.VSlice.card := by
    have heq : (L1.intCore.B ×ˢ L2.intCore.B).filter
        (fun p => (L1.upgradeProd L2).core.inP0Nbr p) =
        (L1.outer.aux.HSlice ×ˢ (L2.outer.aux.OSlice \ L2.intCore.S)) ∪
        ((L1.outer.aux.OSlice \ L1.intCore.S) ×ˢ L2.outer.aux.VSlice) := by
      ext ⟨x₁, x₂⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union, upgradeProd]
      constructor
      · rintro ⟨⟨hb1, hb2⟩, hp0⟩
        have hx1 : x₁ ∈ L1.outer.aux.X := L1.intCore_I ▸ (L1.intCore.mem_B.mp hb1).1
        have hx2 : x₂ ∈ L2.outer.aux.X := L2.intCore_I ▸ (L2.intCore.mem_B.mp hb2).1
        rw [HeteroGadget.prodCore_inP0Nbr_iff,
          HeteroGadget.mem_OSlice_of_mem_X_close L1.outer hx1,
          HeteroGadget.mem_OSlice_of_mem_X_close L2.outer hx2] at hp0
        rcases hp0 with ⟨h01, h02⟩ | ⟨h01, h02⟩
        · exact Or.inl ⟨(mem_BX_HSlice L1).mp ⟨hb1, h01⟩, (mem_BX_outerO_sdiff L2).mp ⟨hb2, h02⟩⟩
        · exact Or.inr ⟨(mem_BX_outerO_sdiff L1).mp ⟨hb1, h01⟩, (mem_BX_VSlice L2).mp ⟨hb2, h02⟩⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rcases (mem_BX_HSlice L1).mpr h1 with ⟨hb1, h01⟩
          rcases (mem_BX_outerO_sdiff L2).mpr h2 with ⟨hb2, h02⟩
          exact ⟨⟨hb1, hb2⟩, (HeteroGadget.prodCore_inP0Nbr_iff _ _ _).mpr
            (Or.inl ⟨h01, ⟨x₂, h02, Or.inl rfl⟩⟩)⟩
        · rcases (mem_BX_outerO_sdiff L1).mpr h1 with ⟨hb1, h01⟩
          rcases (mem_BX_VSlice L2).mpr h2 with ⟨hb2, h02⟩
          exact ⟨⟨hb1, hb2⟩, (HeteroGadget.prodCore_inP0Nbr_iff _ _ _).mpr
            (Or.inr ⟨⟨x₁, h01, Or.inl rfl⟩, h02⟩)⟩
    have hd : Disjoint (L1.outer.aux.HSlice ×ˢ (L2.outer.aux.OSlice \ L2.intCore.S))
        ((L1.outer.aux.OSlice \ L1.intCore.S) ×ˢ L2.outer.aux.VSlice) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact (L1.outer.aux.mem_OSlice.mp (Finset.mem_sdiff.mp (Finset.mem_product.mp h2).1).1).2.1
        (L1.outer.aux.mem_HSlice.mp (Finset.mem_product.mp h1).1).2
    rw [heq, Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product,
      card_sdiff_eq L1.intCore_S_sub_outerO, card_sdiff_eq L2.intCore_S_sub_outerO]
  have hleft : ∀ (A : Finset V) (B : Finset W),
      (∀ x ∈ A, x ∈ L1.intCore.S ∨ x ∈ L1.intCore.P0 ∨ x ∈ L1.intCore.P1) →
      ((A ×ˢ B).filter (fun p => (L1.upgradeProd L2).core.inP0Nbr p)).card =
        A.card * (B.filter (fun y => L2.outer.core.inP1Nbr y)).card := by
    intro A B hA
    have heq : (A ×ˢ B).filter (fun p => (L1.upgradeProd L2).core.inP0Nbr p) =
        A ×ˢ (B.filter (fun y => L2.outer.core.inP1Nbr y)) := by
      ext ⟨x₁, x₂⟩
      simp only [Finset.mem_filter, Finset.mem_product, upgradeProd]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, hp0⟩
        have h1' := intCore_mem_outerO_nbr L1 (hA x₁ hx1)
        rw [HeteroGadget.prodCore_inP0Nbr_iff] at hp0
        rcases hp0 with ⟨h0a, _⟩ | ⟨_, h0b⟩
        · exact absurd h0a h1'.1.1
        · exact ⟨hx1, hx2, h0b⟩
      · rintro ⟨hx1, hx2, h0b⟩
        exact ⟨⟨hx1, hx2⟩, (HeteroGadget.prodCore_inP0Nbr_iff _ _ _).mpr
          (Or.inr ⟨(intCore_mem_outerO_nbr L1 (hA x₁ hx1)).2, h0b⟩)⟩
    rw [heq, Finset.card_product]
  have hright : ∀ (A : Finset V) (B : Finset W),
      (∀ y ∈ B, y ∈ L2.intCore.S ∨ y ∈ L2.intCore.P0 ∨ y ∈ L2.intCore.P1) →
      ((A ×ˢ B).filter (fun p => (L1.upgradeProd L2).core.inP0Nbr p)).card =
        (A.filter (fun x => L1.outer.core.inP0Nbr x)).card * B.card := by
    intro A B hB
    have heq : (A ×ˢ B).filter (fun p => (L1.upgradeProd L2).core.inP0Nbr p) =
        (A.filter (fun x => L1.outer.core.inP0Nbr x)) ×ˢ B := by
      ext ⟨x₁, x₂⟩
      simp only [Finset.mem_filter, Finset.mem_product, upgradeProd]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, hp0⟩
        have h2' := intCore_mem_outerO_nbr L2 (hB x₂ hx2)
        rw [HeteroGadget.prodCore_inP0Nbr_iff] at hp0
        rcases hp0 with ⟨h0a, _⟩ | ⟨_, h0b⟩
        · exact ⟨⟨hx1, h0a⟩, hx2⟩
        · exact absurd h0b h2'.1.2
      · rintro ⟨⟨hx1, h0a⟩, hx2⟩
        exact ⟨⟨hx1, hx2⟩, (HeteroGadget.prodCore_inP0Nbr_iff _ _ _).mpr
          (Or.inl ⟨h0a, (intCore_mem_outerO_nbr L2 (hB x₂ hx2)).2⟩)⟩
    rw [heq, Finset.card_product]
  dsimp only [intGadget]
  rw [hK0,
    hleft _ _ (fun _ h => Or.inl h),
    hleft _ _ (fun _ h => Or.inr (Or.inl h)),
    hleft _ _ (fun _ h => Or.inr (Or.inr h)),
    hright _ _ (fun _ h => Or.inl h),
    hright _ _ (fun _ h => Or.inr (Or.inr h)),
    hright _ _ (fun _ h => Or.inr (Or.inl h)),
    L1.intCore.card_P0, L1.intCore.card_P1, L2.intCore.card_P0, L2.intCore.card_P1]
  have hy1 := intAux_filter_part L1 (fun y => L1.outer.core.inP0Nbr y)
  have hy2 := intAux_filter_part L2 (fun y => L2.outer.core.inP1Nbr y)
  have hY1_eq : (L1.intAux.X.filter (fun y => L1.outer.core.inP0Nbr y)).card =
      L1.outerAuxY.HSlice.card :=
    congrArg Finset.card (by ext y; simp [AuxCode.mem_HSlice, outerAuxY])
  have hY2_eq : (L2.intAux.X.filter (fun y => L2.outer.core.inP1Nbr y)).card =
      L2.outerAuxY.VSlice.card :=
    congrArg Finset.card (by ext y; simp [AuxCode.mem_VSlice, outerAuxY])
  rw [hY1_eq] at hy1; rw [hY2_eq] at hy2
  nlinarith

private theorem upgradeProd_VSlice_card (L1 : LayeredTuple G) (L2 : LayeredTuple H) :
    (L1.upgradeProd L2).aux.VSlice.card =
      L1.outer.aux.VSlice.card * (L2.outer.aux.OSlice.card - L2.intCore.S.card) +
      (L1.outer.aux.OSlice.card - L1.intCore.S.card) * L2.outer.aux.HSlice.card +
      L1.outerAuxY.VSlice.card * L2.intCore.S.card +
      L1.intCore.S.card * L2.outerAuxY.HSlice.card := by
  classical
  have hVs : (L1.upgradeProd L2).aux.VSlice =
      (HeteroGadget.prodI L1.intGadget L2.intGadget).filter
        (fun p => (L1.upgradeProd L2).core.inP1Nbr p) := by
    ext p; simp [AuxCode.mem_VSlice, upgradeProd, upgradedAux]
  rw [hVs, (HeteroGadget.prodI_indep_and_filter L1.intGadget L2.intGadget).2]
  have hK0 : ((L1.intCore.B ×ˢ L2.intCore.B).filter
      (fun p => (L1.upgradeProd L2).core.inP1Nbr p)).card =
      L1.outer.aux.VSlice.card * (L2.outer.aux.OSlice.card - L2.intCore.S.card) +
      (L1.outer.aux.OSlice.card - L1.intCore.S.card) * L2.outer.aux.HSlice.card := by
    have heq : (L1.intCore.B ×ˢ L2.intCore.B).filter
        (fun p => (L1.upgradeProd L2).core.inP1Nbr p) =
        (L1.outer.aux.VSlice ×ˢ (L2.outer.aux.OSlice \ L2.intCore.S)) ∪
        ((L1.outer.aux.OSlice \ L1.intCore.S) ×ˢ L2.outer.aux.HSlice) := by
      ext ⟨x₁, x₂⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union, upgradeProd]
      constructor
      · rintro ⟨⟨hb1, hb2⟩, hp1⟩
        have hx1 : x₁ ∈ L1.outer.aux.X := L1.intCore_I ▸ (L1.intCore.mem_B.mp hb1).1
        have hx2 : x₂ ∈ L2.outer.aux.X := L2.intCore_I ▸ (L2.intCore.mem_B.mp hb2).1
        rw [HeteroGadget.prodCore_inP1Nbr_iff,
          HeteroGadget.mem_OSlice_of_mem_X_close L1.outer hx1,
          HeteroGadget.mem_OSlice_of_mem_X_close L2.outer hx2] at hp1
        rcases hp1 with ⟨h11, h12⟩ | ⟨h11, h12⟩
        · exact Or.inl ⟨(mem_BX_VSlice L1).mp ⟨hb1, h11⟩, (mem_BX_outerO_sdiff L2).mp ⟨hb2, h12⟩⟩
        · exact Or.inr ⟨(mem_BX_outerO_sdiff L1).mp ⟨hb1, h11⟩, (mem_BX_HSlice L2).mp ⟨hb2, h12⟩⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rcases (mem_BX_VSlice L1).mpr h1 with ⟨hb1, h11⟩
          rcases (mem_BX_outerO_sdiff L2).mpr h2 with ⟨hb2, h12⟩
          exact ⟨⟨hb1, hb2⟩, (HeteroGadget.prodCore_inP1Nbr_iff _ _ _).mpr
            (Or.inl ⟨h11, ⟨x₂, h12, Or.inl rfl⟩⟩)⟩
        · rcases (mem_BX_outerO_sdiff L1).mpr h1 with ⟨hb1, h11⟩
          rcases (mem_BX_HSlice L2).mpr h2 with ⟨hb2, h12⟩
          exact ⟨⟨hb1, hb2⟩, (HeteroGadget.prodCore_inP1Nbr_iff _ _ _).mpr
            (Or.inr ⟨⟨x₁, h11, Or.inl rfl⟩, h12⟩)⟩
    have hd : Disjoint (L1.outer.aux.VSlice ×ˢ (L2.outer.aux.OSlice \ L2.intCore.S))
        ((L1.outer.aux.OSlice \ L1.intCore.S) ×ˢ L2.outer.aux.HSlice) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact (L1.outer.aux.mem_OSlice.mp (Finset.mem_sdiff.mp (Finset.mem_product.mp h2).1).1).2.2
        (L1.outer.aux.mem_VSlice.mp (Finset.mem_product.mp h1).1).2
    rw [heq, Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product,
      card_sdiff_eq L1.intCore_S_sub_outerO, card_sdiff_eq L2.intCore_S_sub_outerO]
  have hleft : ∀ (A : Finset V) (B : Finset W),
      (∀ x ∈ A, x ∈ L1.intCore.S ∨ x ∈ L1.intCore.P0 ∨ x ∈ L1.intCore.P1) →
      ((A ×ˢ B).filter (fun p => (L1.upgradeProd L2).core.inP1Nbr p)).card =
        A.card * (B.filter (fun y => L2.outer.core.inP0Nbr y)).card := by
    intro A B hA
    have heq : (A ×ˢ B).filter (fun p => (L1.upgradeProd L2).core.inP1Nbr p) =
        A ×ˢ (B.filter (fun y => L2.outer.core.inP0Nbr y)) := by
      ext ⟨x₁, x₂⟩
      simp only [Finset.mem_filter, Finset.mem_product, upgradeProd]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, hp1⟩
        have h1' := intCore_mem_outerO_nbr L1 (hA x₁ hx1)
        rw [HeteroGadget.prodCore_inP1Nbr_iff] at hp1
        rcases hp1 with ⟨h1a, _⟩ | ⟨_, h1b⟩
        · exact absurd h1a h1'.1.2
        · exact ⟨hx1, hx2, h1b⟩
      · rintro ⟨hx1, hx2, h1b⟩
        exact ⟨⟨hx1, hx2⟩, (HeteroGadget.prodCore_inP1Nbr_iff _ _ _).mpr
          (Or.inr ⟨(intCore_mem_outerO_nbr L1 (hA x₁ hx1)).2, h1b⟩)⟩
    rw [heq, Finset.card_product]
  have hright : ∀ (A : Finset V) (B : Finset W),
      (∀ y ∈ B, y ∈ L2.intCore.S ∨ y ∈ L2.intCore.P0 ∨ y ∈ L2.intCore.P1) →
      ((A ×ˢ B).filter (fun p => (L1.upgradeProd L2).core.inP1Nbr p)).card =
        (A.filter (fun x => L1.outer.core.inP1Nbr x)).card * B.card := by
    intro A B hB
    have heq : (A ×ˢ B).filter (fun p => (L1.upgradeProd L2).core.inP1Nbr p) =
        (A.filter (fun x => L1.outer.core.inP1Nbr x)) ×ˢ B := by
      ext ⟨x₁, x₂⟩
      simp only [Finset.mem_filter, Finset.mem_product, upgradeProd]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, hp1⟩
        have h2' := intCore_mem_outerO_nbr L2 (hB x₂ hx2)
        rw [HeteroGadget.prodCore_inP1Nbr_iff] at hp1
        rcases hp1 with ⟨h1a, _⟩ | ⟨_, h1b⟩
        · exact ⟨⟨hx1, h1a⟩, hx2⟩
        · exact absurd h1b h2'.1.1
      · rintro ⟨⟨hx1, h1a⟩, hx2⟩
        exact ⟨⟨hx1, hx2⟩, (HeteroGadget.prodCore_inP1Nbr_iff _ _ _).mpr
          (Or.inl ⟨h1a, (intCore_mem_outerO_nbr L2 (hB x₂ hx2)).2⟩)⟩
    rw [heq, Finset.card_product]
  dsimp only [intGadget]
  rw [hK0,
    hleft _ _ (fun _ h => Or.inl h),
    hleft _ _ (fun _ h => Or.inr (Or.inl h)),
    hleft _ _ (fun _ h => Or.inr (Or.inr h)),
    hright _ _ (fun _ h => Or.inl h),
    hright _ _ (fun _ h => Or.inr (Or.inr h)),
    hright _ _ (fun _ h => Or.inr (Or.inl h)),
    L1.intCore.card_P0, L1.intCore.card_P1, L2.intCore.card_P0, L2.intCore.card_P1]
  have hy1 := intAux_filter_part L1 (fun y => L1.outer.core.inP1Nbr y)
  have hy2 := intAux_filter_part L2 (fun y => L2.outer.core.inP0Nbr y)
  have hY1_eq : (L1.intAux.X.filter (fun y => L1.outer.core.inP1Nbr y)).card =
      L1.outerAuxY.VSlice.card :=
    congrArg Finset.card (by ext y; simp [AuxCode.mem_VSlice, outerAuxY])
  have hY2_eq : (L2.intAux.X.filter (fun y => L2.outer.core.inP0Nbr y)).card =
      L2.outerAuxY.HSlice.card :=
    congrArg Finset.card (by ext y; simp [AuxCode.mem_HSlice, outerAuxY])
  rw [hY1_eq] at hy1; rw [hY2_eq] at hy2
  nlinarith

private theorem layered_d_alg
    {c1 d1 h1 v1 b1 e1 dY1 hY1 vY1 c2 d2 h2 v2 b2 e2 dY2 hY2 vY2 d12 : ℕ}
    (hp1 : d1 + h1 + v1 = c1) (hp2 : d2 + h2 + v2 = c2)
    (hpY1 : dY1 + hY1 + vY1 = e1) (hpY2 : dY2 + hY2 + vY2 = e2)
    (hb1 : b1 ≤ d1) (hb2 : b2 ≤ d2)
    (hpart : d12 +
      (h1 * (d2 - b2) + (d1 - b1) * v2 + hY1 * b2 + b1 * vY2) +
      (v1 * (d2 - b2) + (d1 - b1) * h2 + vY1 * b2 + b1 * hY2) =
      (c1 - b1) * (c2 - b2) + b1 * e2 + e1 * b2) :
    d12 = (d1 - b1) * (d2 - b2) + (h1 + v1) * (h2 + v2) + b1 * dY2 + dY1 * b2 := by
  have hbc1 : b1 ≤ c1 := by omega
  have hbc2 : b2 ≤ c2 := by omega
  zify [hb1, hb2, hbc1, hbc2] at hpart hp1 hp2 hpY1 hpY2 ⊢
  nlinarith

theorem upgradeProd_asymProfile (L1 : LayeredTuple G) (L2 : LayeredTuple H) :
    (L1.upgradeProd L2).asymProfile =
      L1.layeredProfile.upgradeProd L2.layeredProfile := by
  have hI : (L1.upgradeProd L2).core.I.card =
      (L1.outer.core.I.card - L1.outer.core.S.card) *
        (L2.outer.core.I.card - L2.outer.core.S.card) +
      L1.outer.core.S.card * L2.outer.aux.X.card +
      L1.outer.aux.X.card * L2.outer.core.S.card :=
    HeteroGadget.prodI_card L1.outer L2.outer
  have hS : (L1.upgradeProd L2).core.S.card =
      L1.outer.core.S.card * L2.outer.aux.OSlice.card +
      L1.outer.aux.OSlice.card * L2.outer.core.S.card :=
    HeteroGadget.prodCore_card_S L1.outer L2.outer
  have hX : (L1.upgradeProd L2).aux.X.card =
      (L1.outer.aux.X.card - L1.intCore.S.card) * (L2.outer.aux.X.card - L2.intCore.S.card) +
      L1.intCore.S.card * L2.intAux.X.card + L1.intAux.X.card * L2.intCore.S.card := by
    simpa only [upgradeProd, upgradedAux, intGadget, L1.intCore_I, L2.intCore_I] using
      HeteroGadget.prodI_card L1.intGadget L2.intGadget
  have hH := upgradeProd_HSlice_card L1 L2
  have hV := upgradeProd_VSlice_card L1 L2
  have hO : (L1.upgradeProd L2).aux.OSlice.card =
      (L1.outer.aux.OSlice.card - L1.intCore.S.card) *
        (L2.outer.aux.OSlice.card - L2.intCore.S.card) +
      (L1.outer.aux.HSlice.card + L1.outer.aux.VSlice.card) *
        (L2.outer.aux.HSlice.card + L2.outer.aux.VSlice.card) +
      L1.intCore.S.card * L2.outerAuxY.OSlice.card +
      L1.outerAuxY.OSlice.card * L2.intCore.S.card := by
    have hpart := (L1.upgradeProd L2).aux.card_partition
    rw [hH, hV, hX] at hpart
    exact layered_d_alg
      L1.outer.aux.card_partition L2.outer.aux.card_partition
      L1.outerAuxY.card_partition L2.outerAuxY.card_partition
      (Finset.card_le_card L1.intCore_S_sub_outerO)
      (Finset.card_le_card L2.intCore_S_sub_outerO) hpart
  simp only [HeteroGadget.asymProfile, LayeredProfile.upgradeProd, layeredProfile,
    AsymProfile.mk.injEq]
  exact ⟨hI, hS, hX, hO, hH, hV⟩

noncomputable def prod (L1 : LayeredTuple G) (L2 : LayeredTuple H) :
    LayeredTuple (G ⊠ H) := by
  classical
  let intProd := L1.intGadget.prod L2.intGadget
  let SX_pure : Finset (V × W) :=
    (L1.intCore.S ×ˢ L2.pureOY) ∪ (L1.pureOY ×ˢ L2.intCore.S)
  have hSX_sub : SX_pure ⊆ intProd.core.S := by
    intro p hp
    simp only [SX_pure, intProd, HeteroGadget.prod, HeteroGadget.prodCore,
      Finset.mem_union, Finset.mem_product] at hp ⊢
    rcases hp with ⟨hs1, hy2⟩ | ⟨hy1, hs2⟩
    · exact Or.inl ⟨hs1, (L2.mem_pureOY.mp hy2).1⟩
    · exact Or.inr ⟨(L1.mem_pureOY.mp hy1).1, hs2⟩
  let intCore12 := intProd.core.restrictS SX_pure hSX_sub
  let Y_filt : Finset (V × W) :=
    (L1.intAux.X ×ˢ L2.intAux.X).filter (fun p =>
      ¬ ((HeteroGadget.prodCore L1.outer L2.outer).inP0Nbr p ∧
         (HeteroGadget.prodCore L1.outer L2.outer).inP1Nbr p))
  refine
    { outer := L1.upgradeProd L2
      intCore := intCore12
      intCore_I := rfl
      intCore_P0_outside := ?_
      intCore_P1_outside := ?_
      intAux :=
        { X := Y_filt
          indep_X := isIndepSet_subset (isIndepSet_prod L1.intAux.indep_X L2.intAux.indep_X)
            (Finset.filter_subset _ _)
          disj_nbr := fun y hy =>
            (intProd.aux.restrictS SX_pure hSX_sub).disj_nbr y (Finset.mem_filter.mp hy).1 }
      intAux_outer := fun y hy => (Finset.mem_filter.mp hy).2 }
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_product.mp hp with ⟨hs1, hy2⟩
      have hq1 := L1.intCore_P0_outside p.1 hs1
      have hy2' := L2.mem_pureOY.mp hy2
      have hf : intCore12.f0 p = (L1.intCore.f0 p.1, p.2) :=
        HeteroGadget.prodCore_f0_of_mem_S L1.intGadget L2.intGadget hs1
      rw [hf]
      change ¬ (HeteroGadget.prodCore L1.outer L2.outer).inP0Nbr _ ∧
        ¬ (HeteroGadget.prodCore L1.outer L2.outer).inP1Nbr _
      rw [HeteroGadget.prodCore_inP0Nbr_iff, HeteroGadget.prodCore_inP1Nbr_iff]
      exact ⟨fun h => by rcases h with ⟨h0, _⟩ | ⟨_, h1⟩; exact hq1.1 h0; exact hy2'.2.2 h1,
             fun h => by rcases h with ⟨h0, _⟩ | ⟨_, h1⟩; exact hq1.2 h0; exact hy2'.2.1 h1⟩
    · rcases Finset.mem_product.mp hp with ⟨hy1, hs2⟩
      have hy1' := L1.mem_pureOY.mp hy1
      have hns1 : p.1 ∉ L1.intCore.S :=
        HeteroGadget.not_mem_S_of_mem_OSlice L1.intGadget hy1'.1
      have hq2 := L2.intCore_P1_outside p.2 hs2
      have hf : intCore12.f0 p = (p.1, L2.intCore.f1 p.2) :=
        HeteroGadget.prodCore_f0_of_not_mem_S L1.intGadget L2.intGadget hns1
      rw [hf]
      change ¬ (HeteroGadget.prodCore L1.outer L2.outer).inP0Nbr _ ∧
        ¬ (HeteroGadget.prodCore L1.outer L2.outer).inP1Nbr _
      rw [HeteroGadget.prodCore_inP0Nbr_iff, HeteroGadget.prodCore_inP1Nbr_iff]
      exact ⟨fun h => by rcases h with ⟨h0, _⟩ | ⟨_, h1⟩; exact hy1'.2.1 h0; exact hq2.2 h1,
             fun h => by rcases h with ⟨h0, _⟩ | ⟨_, h1⟩; exact hy1'.2.2 h0; exact hq2.1 h1⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_product.mp hp with ⟨hs1, hy2⟩
      have hq1 := L1.intCore_P1_outside p.1 hs1
      have hy2' := L2.mem_pureOY.mp hy2
      have hf : intCore12.f1 p = (L1.intCore.f1 p.1, p.2) :=
        HeteroGadget.prodCore_f1_of_mem_S L1.intGadget L2.intGadget hs1
      rw [hf]
      change ¬ (HeteroGadget.prodCore L1.outer L2.outer).inP0Nbr _ ∧
        ¬ (HeteroGadget.prodCore L1.outer L2.outer).inP1Nbr _
      rw [HeteroGadget.prodCore_inP0Nbr_iff, HeteroGadget.prodCore_inP1Nbr_iff]
      exact ⟨fun h => by rcases h with ⟨h0, _⟩ | ⟨_, h1⟩; exact hq1.1 h0; exact hy2'.2.2 h1,
             fun h => by rcases h with ⟨h0, _⟩ | ⟨_, h1⟩; exact hq1.2 h0; exact hy2'.2.1 h1⟩
    · rcases Finset.mem_product.mp hp with ⟨hy1, hs2⟩
      have hy1' := L1.mem_pureOY.mp hy1
      have hns1 : p.1 ∉ L1.intCore.S :=
        HeteroGadget.not_mem_S_of_mem_OSlice L1.intGadget hy1'.1
      have hq2 := L2.intCore_P0_outside p.2 hs2
      have hf : intCore12.f1 p = (p.1, L2.intCore.f0 p.2) :=
        HeteroGadget.prodCore_f1_of_not_mem_S L1.intGadget L2.intGadget hns1
      rw [hf]
      change ¬ (HeteroGadget.prodCore L1.outer L2.outer).inP0Nbr _ ∧
        ¬ (HeteroGadget.prodCore L1.outer L2.outer).inP1Nbr _
      rw [HeteroGadget.prodCore_inP0Nbr_iff, HeteroGadget.prodCore_inP1Nbr_iff]
      exact ⟨fun h => by rcases h with ⟨h0, _⟩ | ⟨_, h1⟩; exact hy1'.2.1 h0; exact hq2.2 h1,
             fun h => by rcases h with ⟨h0, _⟩ | ⟨_, h1⟩; exact hy1'.2.2 h0; exact hq2.1 h1⟩

theorem prod_profile_bounds (L1 : LayeredTuple G) (L2 : LayeredTuple H) :
    (L1.prod L2).outer.asymProfile = L1.layeredProfile.upgradeProd L2.layeredProfile ∧
    (L1.prod L2).layeredProfile.bX =
      L1.layeredProfile.bX * L2.layeredProfile.pY +
      L1.layeredProfile.pY * L2.layeredProfile.bX ∧
    L1.layeredProfile.e * L2.layeredProfile.e -
      L1.layeredProfile.hY * L2.layeredProfile.hY -
      L1.layeredProfile.vY * L2.layeredProfile.vY ≤ (L1.prod L2).layeredProfile.e ∧
    L1.layeredProfile.dY * L2.layeredProfile.dY ≤ (L1.prod L2).layeredProfile.dY ∧
    L1.layeredProfile.pY * L2.layeredProfile.pY ≤ (L1.prod L2).layeredProfile.pY := by
  classical
  refine ⟨upgradeProd_asymProfile L1 L2, ?_, ?_, ?_, ?_⟩
  · have hdisj : Disjoint (L1.intCore.S ×ˢ L2.pureOY) (L1.pureOY ×ˢ L2.intCore.S) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact HeteroGadget.not_mem_S_of_mem_OSlice L1.intGadget
        (L1.mem_pureOY.mp (Finset.mem_product.mp h2).1).1 (Finset.mem_product.mp h1).1
    change ((L1.intCore.S ×ˢ L2.pureOY) ∪ (L1.pureOY ×ˢ L2.intCore.S)).card = _
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product]; rfl
  · let bad := (L1.intAux.X ×ˢ L2.intAux.X).filter (fun p =>
      (HeteroGadget.prodCore L1.outer L2.outer).inP0Nbr p ∧
      (HeteroGadget.prodCore L1.outer L2.outer).inP1Nbr p)
    have hbad_sub : bad ⊆
        (L1.outerAuxY.HSlice ×ˢ L2.outerAuxY.HSlice) ∪
        (L1.outerAuxY.VSlice ×ˢ L2.outerAuxY.VSlice) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hmem, h0, h1⟩
      rcases Finset.mem_product.mp hmem with ⟨hy1, hy2⟩
      rw [HeteroGadget.prodCore_inP0Nbr_iff] at h0; rw [HeteroGadget.prodCore_inP1Nbr_iff] at h1
      rcases h0 with ⟨h0a, _⟩ | ⟨_, h0b⟩ <;> rcases h1 with ⟨h1a, _⟩ | ⟨_, h1b⟩
      · exact absurd ⟨h0a, h1a⟩ (L1.intAux_outer p.1 hy1)
      · exact Finset.mem_union_left _ (Finset.mem_product.mpr
          ⟨L1.outerAuxY.mem_HSlice.mpr ⟨hy1, h0a⟩, L2.outerAuxY.mem_HSlice.mpr ⟨hy2, h1b⟩⟩)
      · exact Finset.mem_union_right _ (Finset.mem_product.mpr
          ⟨L1.outerAuxY.mem_VSlice.mpr ⟨hy1, h1a⟩, L2.outerAuxY.mem_VSlice.mpr ⟨hy2, h0b⟩⟩)
      · exact absurd ⟨h1b, h0b⟩ (L2.intAux_outer p.2 hy2)
    have hbad_le : bad.card ≤
        L1.layeredProfile.hY * L2.layeredProfile.hY +
        L1.layeredProfile.vY * L2.layeredProfile.vY := by
      calc bad.card
          ≤ ((L1.outerAuxY.HSlice ×ˢ L2.outerAuxY.HSlice) ∪
              (L1.outerAuxY.VSlice ×ˢ L2.outerAuxY.VSlice)).card := Finset.card_le_card hbad_sub
        _ ≤ (L1.outerAuxY.HSlice ×ˢ L2.outerAuxY.HSlice).card +
            (L1.outerAuxY.VSlice ×ˢ L2.outerAuxY.VSlice).card := Finset.card_union_le _ _
        _ = _ := by rw [Finset.card_product, Finset.card_product]; rfl
    have hsum : bad.card + (L1.prod L2).layeredProfile.e =
        L1.layeredProfile.e * L2.layeredProfile.e := by
      have h := Finset.card_filter_add_card_filter_not
        (s := L1.intAux.X ×ˢ L2.intAux.X)
        (p := fun p =>
          (HeteroGadget.prodCore L1.outer L2.outer).inP0Nbr p ∧
          (HeteroGadget.prodCore L1.outer L2.outer).inP1Nbr p)
      have heq_f : ((L1.intAux.X ×ˢ L2.intAux.X).filter (fun p =>
          ¬ ((HeteroGadget.prodCore L1.outer L2.outer).inP0Nbr p ∧
             (HeteroGadget.prodCore L1.outer L2.outer).inP1Nbr p))).card =
          (L1.prod L2).layeredProfile.e :=
        congrArg Finset.card (by ext p; simp [prod])
      rw [Finset.card_product, heq_f] at h
      exact h
    omega
  · have hsub : L1.outerAuxY.OSlice ×ˢ L2.outerAuxY.OSlice ⊆ (L1.prod L2).outerAuxY.OSlice := by
      intro p hp
      rcases Finset.mem_product.mp hp with ⟨h1, h2⟩
      rcases L1.outerAuxY.mem_OSlice.mp h1 with ⟨hy1, h10, h11⟩
      rcases L2.outerAuxY.mem_OSlice.mp h2 with ⟨hy2, h20, h21⟩
      have hnp0 : ¬ (HeteroGadget.prodCore L1.outer L2.outer).inP0Nbr p := by
        rw [HeteroGadget.prodCore_inP0Nbr_iff]; rintro (⟨ha, _⟩ | ⟨_, hb⟩); exact h10 ha; exact h21 hb
      have hnp1 : ¬ (HeteroGadget.prodCore L1.outer L2.outer).inP1Nbr p := by
        rw [HeteroGadget.prodCore_inP1Nbr_iff]; rintro (⟨ha, _⟩ | ⟨_, hb⟩); exact h11 ha; exact h20 hb
      rw [(L1.prod L2).outerAuxY.mem_OSlice]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy1, hy2⟩, fun h => hnp0 h.1⟩, hnp0, hnp1⟩
    calc L1.layeredProfile.dY * L2.layeredProfile.dY
        = (L1.outerAuxY.OSlice ×ˢ L2.outerAuxY.OSlice).card := (Finset.card_product _ _).symm
      _ ≤ (L1.prod L2).layeredProfile.dY := Finset.card_le_card hsub
  · have hsub : L1.pureOY ×ˢ L2.pureOY ⊆ (L1.prod L2).pureOY := by
      intro p hp
      rcases Finset.mem_product.mp hp with ⟨h1, h2⟩
      rcases L1.mem_pureOY.mp h1 with ⟨hO1, h10, h11⟩
      rcases L2.mem_pureOY.mp h2 with ⟨hO2, h20, h21⟩
      have hy1 : p.1 ∈ L1.intAux.X := (L1.intAux.mem_OSlice.mp hO1).1
      have hy2 : p.2 ∈ L2.intAux.X := (L2.intAux.mem_OSlice.mp hO2).1
      have hnp0 : ¬ (HeteroGadget.prodCore L1.outer L2.outer).inP0Nbr p := by
        rw [HeteroGadget.prodCore_inP0Nbr_iff]; rintro (⟨ha, _⟩ | ⟨_, hb⟩); exact h10 ha; exact h21 hb
      have hnp1 : ¬ (HeteroGadget.prodCore L1.outer L2.outer).inP1Nbr p := by
        rw [HeteroGadget.prodCore_inP1Nbr_iff]; rintro (⟨ha, _⟩ | ⟨_, hb⟩); exact h11 ha; exact h20 hb
      have hnq0 : ¬ (L1.prod L2).intCore.inP0Nbr p := by
        rintro ⟨q, hq, hcq⟩
        rcases eq_or_strongProd_adj.mp hcq with ⟨hc1, hc2⟩
        rcases Finset.mem_union.mp hq with hq | hq
        · rcases Finset.mem_product.mp hq with ⟨hs1, _⟩
          have hf := HeteroGadget.prodCore_f0_of_mem_S L1.intGadget L2.intGadget hs1
          change ((HeteroGadget.prodCore L1.intGadget L2.intGadget).f0 q).1 = p.1 ∨
            G.Adj ((HeteroGadget.prodCore L1.intGadget L2.intGadget).f0 q).1 p.1 at hc1
          rw [hf] at hc1; exact (L1.intAux.mem_OSlice.mp hO1).2.1 ⟨q.1, hs1, hc1⟩
        · rcases Finset.mem_product.mp hq with ⟨hq1, hs2⟩
          have hns1 : q.1 ∉ L1.intCore.S :=
            HeteroGadget.not_mem_S_of_mem_OSlice L1.intGadget (L1.mem_pureOY.mp hq1).1
          have hf := HeteroGadget.prodCore_f0_of_not_mem_S L1.intGadget L2.intGadget hns1
          change ((HeteroGadget.prodCore L1.intGadget L2.intGadget).f0 q).2 = p.2 ∨
            H.Adj ((HeteroGadget.prodCore L1.intGadget L2.intGadget).f0 q).2 p.2 at hc2
          rw [hf] at hc2; exact (L2.intAux.mem_OSlice.mp hO2).2.2 ⟨q.2, hs2, hc2⟩
      have hnq1 : ¬ (L1.prod L2).intCore.inP1Nbr p := by
        rintro ⟨q, hq, hcq⟩
        rcases eq_or_strongProd_adj.mp hcq with ⟨hc1, hc2⟩
        rcases Finset.mem_union.mp hq with hq | hq
        · rcases Finset.mem_product.mp hq with ⟨hs1, _⟩
          have hf := HeteroGadget.prodCore_f1_of_mem_S L1.intGadget L2.intGadget hs1
          change ((HeteroGadget.prodCore L1.intGadget L2.intGadget).f1 q).1 = p.1 ∨
            G.Adj ((HeteroGadget.prodCore L1.intGadget L2.intGadget).f1 q).1 p.1 at hc1
          rw [hf] at hc1; exact (L1.intAux.mem_OSlice.mp hO1).2.2 ⟨q.1, hs1, hc1⟩
        · rcases Finset.mem_product.mp hq with ⟨hq1, hs2⟩
          have hns1 : q.1 ∉ L1.intCore.S :=
            HeteroGadget.not_mem_S_of_mem_OSlice L1.intGadget (L1.mem_pureOY.mp hq1).1
          have hf := HeteroGadget.prodCore_f1_of_not_mem_S L1.intGadget L2.intGadget hns1
          change ((HeteroGadget.prodCore L1.intGadget L2.intGadget).f1 q).2 = p.2 ∨
            H.Adj ((HeteroGadget.prodCore L1.intGadget L2.intGadget).f1 q).2 p.2 at hc2
          rw [hf] at hc2; exact (L2.intAux.mem_OSlice.mp hO2).2.1 ⟨q.2, hs2, hc2⟩
      rw [(L1.prod L2).mem_pureOY, (L1.prod L2).intAux.mem_OSlice]
      exact ⟨⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy1, hy2⟩, fun h => hnp0 h.1⟩,
        hnq0, hnq1⟩, hnp0, hnp1⟩
    calc L1.layeredProfile.pY * L2.layeredProfile.pY
        = (L1.pureOY ×ˢ L2.pureOY).card := (Finset.card_product _ _).symm
      _ ≤ (L1.prod L2).layeredProfile.pY := Finset.card_le_card hsub

end LayeredTuple

/-! ============================================================================
    PART 4: Pure-Kernel `Trie7` Constructors & Smoke Tests
    ============================================================================ -/

section Trie7Constructors

def portLookup0 {W : Type*} [DecidableEq W] (ports : List (W × W × W)) (x : W) : W :=
  match ports.find? (fun t => decide (t.1 = x)) with
  | some (_, p0, _) => p0
  | none => x

def portLookup1 {W : Type*} [DecidableEq W] (ports : List (W × W × W)) (x : W) : W :=
  match ports.find? (fun t => decide (t.1 = x)) with
  | some (_, _, p1) => p1
  | none => x

theorem portLookup_spec {W : Type*} [DecidableEq W] :
    ∀ {ports : List (W × W × W)}, (ports.map Prod.fst).Nodup →
      ∀ {s p0 p1 : W}, (s, p0, p1) ∈ ports →
        portLookup0 ports s = p0 ∧ portLookup1 ports s = p1
  | [], _, _, _, _, h => nomatch h
  | (a, b0, b1) :: tl, hnod, s, p0, p1, hmem => by
    rw [List.map_cons, List.nodup_cons] at hnod
    rcases List.mem_cons.mp hmem with heq | htl
    · rcases Prod.mk.inj heq with ⟨rfl, heq2⟩
      rcases Prod.mk.inj heq2 with ⟨rfl, rfl⟩
      simp [portLookup0, portLookup1]
    · have hne : a ≠ s := fun h => hnod.1 (h ▸ List.mem_map.mpr ⟨(s, p0, p1), htl, rfl⟩)
      have hrec := portLookup_spec hnod.2 htl
      simp only [portLookup0, portLookup1, List.find?_cons, hne] at hrec ⊢
      exact hrec

def checkPortTriples {d : ℕ} (tI tP0 tP1 : Trie7 d)
    (ports : List (StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d)) : Bool :=
  ports.all (fun (s, p0, p1) =>
    tI.memBool s &&
    Trie7.closeBool p0 s && (tI.closedNbrCount p0 == 1) && tP0.memBool p0 &&
    Trie7.closeBool p1 s && (tI.closedNbrCount p1 == 1) && tP1.memBool p1 &&
    (decide (p0 = s) || decide (p1 = s)))

def PortCore.ofTrie7 {d : ℕ} (tI tP0 tP1 : Trie7 d)
    (ports : List (StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d))
    (hI : tI.isIndep = true)
    (hP0 : tP0.isIndep = true)
    (hP1 : tP1.isIndep = true)
    (hnodup : (ports.map Prod.fst).Nodup)
    (hcheck : checkPortTriples tI tP0 tP1 ports = true) :
    PortCore (strongPow C7 d) := by
  have hall : ∀ t ∈ ports,
      tI.memBool t.1 = true ∧
      Trie7.closeBool t.2.1 t.1 = true ∧ tI.closedNbrCount t.2.1 = 1 ∧ tP0.memBool t.2.1 = true ∧
      Trie7.closeBool t.2.2 t.1 = true ∧ tI.closedNbrCount t.2.2 = 1 ∧ tP1.memBool t.2.2 = true ∧
      (t.2.1 = t.1 ∨ t.2.2 = t.1) := by
    intro ⟨s, p0, p1⟩ ht
    have h := List.all_eq_true.mp hcheck (s, p0, p1) ht
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
      h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  refine
    { I := tI.toFinset
      S := (ports.map Prod.fst).toFinset
      f0 := portLookup0 ports
      f1 := portLookup1 ports
      indep_I := Trie7.to_indepSet_of_isIndep hI
      S_sub_I := ?_
      priv0 := ?_
      priv1 := ?_
      indep_P0 := ?_
      indep_P1 := ?_
      self_mem := ?_ }
  · intro s hs
    rcases List.mem_map.mp (List.mem_toFinset.mp hs) with ⟨⟨a, p0, p1⟩, hmem, rfl⟩
    exact Trie7.mem_toFinset_iff_memBool.mpr (hall _ hmem).1
  · intro s hs
    rcases List.mem_map.mp (List.mem_toFinset.mp hs) with ⟨⟨a, p0, p1⟩, hmem, rfl⟩
    have ht := hall _ hmem
    rw [(portLookup_spec hnodup hmem).1]
    have hclose := (Trie7.closeBool_eq_true_iff p0 a).mp ht.2.1
    exact ⟨hclose, fun u hu hcu =>
      (Trie7.closedNbr_inter_eq_singleton ht.2.2.1 ht.1 (close_symm hclose) u hu).mp hcu⟩
  · intro s hs
    rcases List.mem_map.mp (List.mem_toFinset.mp hs) with ⟨⟨a, p0, p1⟩, hmem, rfl⟩
    have ht := hall _ hmem
    rw [(portLookup_spec hnodup hmem).2]
    have hclose := (Trie7.closeBool_eq_true_iff p1 a).mp ht.2.2.2.2.1
    exact ⟨hclose, fun u hu hcu =>
      (Trie7.closedNbr_inter_eq_singleton ht.2.2.2.2.2.1 ht.1 (close_symm hclose) u hu).mp hcu⟩
  · rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩ hne hadj
    rcases List.mem_map.mp (List.mem_toFinset.mp hs₁) with ⟨⟨a₁, p0₁, p1₁⟩, hm1, rfl⟩
    rcases List.mem_map.mp (List.mem_toFinset.mp hs₂) with ⟨⟨a₂, p0₂, p1₂⟩, hm2, rfl⟩
    rw [(portLookup_spec hnodup hm1).1, (portLookup_spec hnodup hm2).1] at hne hadj
    exact Trie7.to_indepSet_of_isIndep hP0
      (Trie7.mem_toFinset_iff_memBool.mpr (hall _ hm1).2.2.2.1)
      (Trie7.mem_toFinset_iff_memBool.mpr (hall _ hm2).2.2.2.1) hne hadj
  · rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩ hne hadj
    rcases List.mem_map.mp (List.mem_toFinset.mp hs₁) with ⟨⟨a₁, p0₁, p1₁⟩, hm1, rfl⟩
    rcases List.mem_map.mp (List.mem_toFinset.mp hs₂) with ⟨⟨a₂, p0₂, p1₂⟩, hm2, rfl⟩
    rw [(portLookup_spec hnodup hm1).2, (portLookup_spec hnodup hm2).2] at hne hadj
    exact Trie7.to_indepSet_of_isIndep hP1
      (Trie7.mem_toFinset_iff_memBool.mpr (hall _ hm1).2.2.2.2.2.2.1)
      (Trie7.mem_toFinset_iff_memBool.mpr (hall _ hm2).2.2.2.2.2.2.1) hne hadj
  · intro s hs
    rcases List.mem_map.mp (List.mem_toFinset.mp hs) with ⟨⟨a, p0, p1⟩, hmem, rfl⟩
    have hlk := portLookup_spec hnodup hmem
    rw [hlk.1, hlk.2]
    exact (hall _ hmem).2.2.2.2.2.2.2

theorem PortCore.ofTrie7_P0_eq {d : ℕ} {tI tP0 tP1 : Trie7 d}
    {ports : List (StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d)}
    {hI : tI.isIndep = true} {hP0 : tP0.isIndep = true} {hP1 : tP1.isIndep = true}
    {hnodup : (ports.map Prod.fst).Nodup}
    {hcheck : checkPortTriples tI tP0 tP1 ports = true}
    (hcard0 : tP0.card = ports.length) :
    (PortCore.ofTrie7 tI tP0 tP1 ports hI hP0 hP1 hnodup hcheck).P0 = tP0.toFinset := by
  let c := PortCore.ofTrie7 tI tP0 tP1 ports hI hP0 hP1 hnodup hcheck
  have hsub : c.P0 ⊆ tP0.toFinset := by
    intro x hx
    rcases c.mem_P0.mp hx with ⟨s, hs, rfl⟩
    rcases List.mem_map.mp (List.mem_toFinset.mp hs) with ⟨⟨a, p0, p1⟩, hmem, rfl⟩
    change portLookup0 ports a ∈ tP0.toFinset
    rw [(portLookup_spec hnodup hmem).1, Trie7.mem_toFinset_iff_memBool]
    have h := List.all_eq_true.mp hcheck (a, p0, p1) hmem
    simp only [Bool.and_eq_true] at h
    exact h.1.1.1.1.2
  have hcard_c : c.P0.card = ports.length := by
    rw [c.card_P0]
    change (ports.map Prod.fst).toFinset.card = ports.length
    rw [List.toFinset_card_of_nodup hnodup, List.length_map]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Trie7.toFinset_card, hcard0, hcard_c])

theorem PortCore.ofTrie7_P1_eq {d : ℕ} {tI tP0 tP1 : Trie7 d}
    {ports : List (StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d)}
    {hI : tI.isIndep = true} {hP0 : tP0.isIndep = true} {hP1 : tP1.isIndep = true}
    {hnodup : (ports.map Prod.fst).Nodup}
    {hcheck : checkPortTriples tI tP0 tP1 ports = true}
    (hcard1 : tP1.card = ports.length) :
    (PortCore.ofTrie7 tI tP0 tP1 ports hI hP0 hP1 hnodup hcheck).P1 = tP1.toFinset := by
  let c := PortCore.ofTrie7 tI tP0 tP1 ports hI hP0 hP1 hnodup hcheck
  have hsub : c.P1 ⊆ tP1.toFinset := by
    intro x hx
    rcases c.mem_P1.mp hx with ⟨s, hs, rfl⟩
    rcases List.mem_map.mp (List.mem_toFinset.mp hs) with ⟨⟨a, p0, p1⟩, hmem, rfl⟩
    change portLookup1 ports a ∈ tP1.toFinset
    rw [(portLookup_spec hnodup hmem).2, Trie7.mem_toFinset_iff_memBool]
    have h := List.all_eq_true.mp hcheck (a, p0, p1) hmem
    simp only [Bool.and_eq_true] at h
    exact h.1.2
  have hcard_c : c.P1.card = ports.length := by
    rw [c.card_P1]
    change (ports.map Prod.fst).toFinset.card = ports.length
    rw [List.toFinset_card_of_nodup hnodup, List.length_map]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Trie7.toFinset_card, hcard1, hcard_c])

def AuxCode.ofTrie7 {d : ℕ} {tI tP0 tP1 : Trie7 d}
    {ports : List (StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d)}
    {hI : tI.isIndep = true} {hP0 : tP0.isIndep = true} {hP1 : tP1.isIndep = true}
    {hnodup : (ports.map Prod.fst).Nodup}
    {hcheck : checkPortTriples tI tP0 tP1 ports = true}
    (hcard0 : tP0.card = ports.length) (hcard1 : tP1.card = ports.length)
    (tX : Trie7 d) (hX : tX.isIndep = true)
    (hdisj : Trie7.disjointCommonNbr tP0 tP1 tX = true) :
    AuxCode (PortCore.ofTrie7 tI tP0 tP1 ports hI hP0 hP1 hnodup hcheck) where
  X := tX.toFinset
  indep_X := Trie7.to_indepSet_of_isIndep hX
  disj_nbr := by
    intro w hw ⟨h0, h1⟩
    rw [PortCore.inP0Nbr_iff_mem_P0, PortCore.ofTrie7_P0_eq hcard0] at h0
    rw [PortCore.inP1Nbr_iff_mem_P1, PortCore.ofTrie7_P1_eq hcard1] at h1
    exact Trie7.disjointCommonNbr_sound hdisj w hw ⟨h0, h1⟩

theorem HeteroGadget.ofTrie7_asymProfile {d : ℕ} {tI tP0 tP1 : Trie7 d}
    {ports : List (StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d × StrongPowV (ZMod 7) d)}
    {hI : tI.isIndep = true} {hP0 : tP0.isIndep = true} {hP1 : tP1.isIndep = true}
    {hnodup : (ports.map Prod.fst).Nodup}
    {hcheck : checkPortTriples tI tP0 tP1 ports = true}
    (hcard0 : tP0.card = ports.length) (hcard1 : tP1.card = ports.length)
    (tX : Trie7 d) (hX : tX.isIndep = true)
    (hdisj : Trie7.disjointCommonNbr tP0 tP1 tX = true) :
    let core := PortCore.ofTrie7 tI tP0 tP1 ports hI hP0 hP1 hnodup hcheck
    let aux := AuxCode.ofTrie7 hcard0 hcard1 tX hX hdisj
    let g : HeteroGadget (strongPow C7 d) := ⟨core, aux⟩
    g.asymProfile.a = tI.card ∧
    g.asymProfile.b = ports.length ∧
    g.asymProfile.c = tX.card ∧
    g.asymProfile.d = Trie7.countOutside tP0 tP1 tX ∧
    g.asymProfile.h = tX.countIf (fun w => tP0.inClosedNbr w) ∧
    g.asymProfile.v = tX.countIf (fun w => tP1.inClosedNbr w) := by
  classical
  dsimp only
  let core := PortCore.ofTrie7 tI tP0 tP1 ports hI hP0 hP1 hnodup hcheck
  have hP0eq : core.P0 = tP0.toFinset := PortCore.ofTrie7_P0_eq hcard0
  have hP1eq : core.P1 = tP1.toFinset := PortCore.ofTrie7_P1_eq hcard1
  refine ⟨Trie7.toFinset_card tI, ?_, Trie7.toFinset_card tX, ?_, ?_, ?_⟩
  · change (ports.map Prod.fst).toFinset.card = ports.length
    rw [List.toFinset_card_of_nodup hnodup, List.length_map]
  · rw [Trie7.countOutside_eq]
    change (tX.toFinset.filter (fun w => ¬ core.inP0Nbr w ∧ ¬ core.inP1Nbr w)).card = _
    congr 1; refine Finset.filter_congr fun w _ => ?_
    rw [core.inP0Nbr_iff_mem_P0, core.inP1Nbr_iff_mem_P1, hP0eq, hP1eq]
  · rw [Trie7.countIf_eq]
    change (tX.toFinset.filter (fun w => core.inP0Nbr w)).card = _
    congr 1; refine Finset.filter_congr fun w _ => ?_
    rw [core.inP0Nbr_iff_mem_P0, hP0eq, Trie7.inClosedNbr_eq_true_iff]
  · rw [Trie7.countIf_eq]
    change (tX.toFinset.filter (fun w => core.inP1Nbr w)).card = _
    congr 1; refine Finset.filter_congr fun w _ => ?_
    rw [core.inP1Nbr_iff_mem_P1, hP1eq, Trie7.inClosedNbr_eq_true_iff]

end Trie7Constructors

/-- Pure-kernel check that every interior port endpoint `(q0, q1)` in `portsInt` avoids
`N[tP0] ∪ N[tP1]`. -/
def checkIntPortsOutside {d : ℕ} (tP0 tP1 : Trie7 d)
    (portsInt : List (PortEntry d)) : Bool :=
  portsInt.all (fun (_, q0, q1) =>
    !tP0.inClosedNbr q0 && !tP1.inClosedNbr q0 &&
    !tP0.inClosedNbr q1 && !tP1.inClosedNbr q1)

/-- Pure-kernel `LayeredTuple` constructor from certified outer and interior `Trie7 d` witnesses
(zero `native_decide`). -/
def LayeredTuple.ofTrie7 {d : ℕ}
    (tI tP0 tP1 tX tQ0 tQ1 tY : Trie7 d)
    (portsOut portsInt : List (PortEntry d))
    (hI : tI.isIndep = true) (hP0 : tP0.isIndep = true) (hP1 : tP1.isIndep = true)
    (hnodupOut : (portsOut.map Prod.fst).Nodup)
    (hcheckOut : checkPortTriples tI tP0 tP1 portsOut = true)
    (hcardP0 : tP0.card = portsOut.length) (hcardP1 : tP1.card = portsOut.length)
    (hX : tX.isIndep = true)
    (hdisjX : Trie7.disjointCommonNbr tP0 tP1 tX = true)
    (hQ0 : tQ0.isIndep = true) (hQ1 : tQ1.isIndep = true)
    (hnodupInt : (portsInt.map Prod.fst).Nodup)
    (hcheckInt : checkPortTriples tX tQ0 tQ1 portsInt = true)
    (hcardQ0 : tQ0.card = portsInt.length) (hcardQ1 : tQ1.card = portsInt.length)
    (hIntOut : checkIntPortsOutside tP0 tP1 portsInt = true)
    (hY : tY.isIndep = true)
    (hdisjY_int : Trie7.disjointCommonNbr tQ0 tQ1 tY = true)
    (hdisjY_out : Trie7.disjointCommonNbr tP0 tP1 tY = true) :
    LayeredTuple (strongPow C7 d) where
  outer :=
    ⟨PortCore.ofTrie7 tI tP0 tP1 portsOut hI hP0 hP1 hnodupOut hcheckOut,
     AuxCode.ofTrie7 hcardP0 hcardP1 tX hX hdisjX⟩
  intCore := PortCore.ofTrie7 tX tQ0 tQ1 portsInt hX hQ0 hQ1 hnodupInt hcheckInt
  intCore_I := rfl
  intCore_P0_outside := by
    intro s hs
    rcases List.mem_map.mp (List.mem_toFinset.mp hs) with ⟨⟨a, q0, q1⟩, hmem, rfl⟩
    have hlk := (portLookup_spec hnodupInt hmem).1
    have hout := List.all_eq_true.mp hIntOut (a, q0, q1) hmem
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hout
    change ¬ (PortCore.ofTrie7 tI tP0 tP1 portsOut hI hP0 hP1 hnodupOut hcheckOut).inP0Nbr
        (portLookup0 portsInt a) ∧
      ¬ (PortCore.ofTrie7 tI tP0 tP1 portsOut hI hP0 hP1 hnodupOut hcheckOut).inP1Nbr
        (portLookup0 portsInt a)
    rw [hlk, PortCore.inP0Nbr_iff_mem_P0, PortCore.ofTrie7_P0_eq hcardP0,
      PortCore.inP1Nbr_iff_mem_P1, PortCore.ofTrie7_P1_eq hcardP1,
      ← Trie7.inClosedNbr_eq_true_iff, ← Trie7.inClosedNbr_eq_true_iff,
      hout.1.1.1, hout.1.1.2]
    exact ⟨Bool.false_ne_true, Bool.false_ne_true⟩
  intCore_P1_outside := by
    intro s hs
    rcases List.mem_map.mp (List.mem_toFinset.mp hs) with ⟨⟨a, q0, q1⟩, hmem, rfl⟩
    have hlk := (portLookup_spec hnodupInt hmem).2
    have hout := List.all_eq_true.mp hIntOut (a, q0, q1) hmem
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hout
    change ¬ (PortCore.ofTrie7 tI tP0 tP1 portsOut hI hP0 hP1 hnodupOut hcheckOut).inP0Nbr
        (portLookup1 portsInt a) ∧
      ¬ (PortCore.ofTrie7 tI tP0 tP1 portsOut hI hP0 hP1 hnodupOut hcheckOut).inP1Nbr
        (portLookup1 portsInt a)
    rw [hlk, PortCore.inP0Nbr_iff_mem_P0, PortCore.ofTrie7_P0_eq hcardP0,
      PortCore.inP1Nbr_iff_mem_P1, PortCore.ofTrie7_P1_eq hcardP1,
      ← Trie7.inClosedNbr_eq_true_iff, ← Trie7.inClosedNbr_eq_true_iff,
      hout.1.2, hout.2]
    exact ⟨Bool.false_ne_true, Bool.false_ne_true⟩
  intAux := AuxCode.ofTrie7 hcardQ0 hcardQ1 tY hY hdisjY_int
  intAux_outer := by
    intro y hy ⟨h0, h1⟩
    rw [PortCore.inP0Nbr_iff_mem_P0, PortCore.ofTrie7_P0_eq hcardP0] at h0
    rw [PortCore.inP1Nbr_iff_mem_P1, PortCore.ofTrie7_P1_eq hcardP1] at h1
    exact Trie7.disjointCommonNbr_sound hdisjY_out y hy ⟨h0, h1⟩

/-- Exact computable profile parameters for `LayeredTuple.ofTrie7`. -/
theorem LayeredTuple.ofTrie7_layeredProfile {d : ℕ}
    {tI tP0 tP1 tX tQ0 tQ1 tY : Trie7 d}
    {portsOut portsInt : List (PortEntry d)}
    {hI : tI.isIndep = true} {hP0 : tP0.isIndep = true} {hP1 : tP1.isIndep = true}
    {hnodupOut : (portsOut.map Prod.fst).Nodup}
    {hcheckOut : checkPortTriples tI tP0 tP1 portsOut = true}
    {hcardP0 : tP0.card = portsOut.length} {hcardP1 : tP1.card = portsOut.length}
    {hX : tX.isIndep = true}
    {hdisjX : Trie7.disjointCommonNbr tP0 tP1 tX = true}
    {hQ0 : tQ0.isIndep = true} {hQ1 : tQ1.isIndep = true}
    {hnodupInt : (portsInt.map Prod.fst).Nodup}
    {hcheckInt : checkPortTriples tX tQ0 tQ1 portsInt = true}
    {hcardQ0 : tQ0.card = portsInt.length} {hcardQ1 : tQ1.card = portsInt.length}
    {hIntOut : checkIntPortsOutside tP0 tP1 portsInt = true}
    {hY : tY.isIndep = true}
    {hdisjY_int : Trie7.disjointCommonNbr tQ0 tQ1 tY = true}
    {hdisjY_out : Trie7.disjointCommonNbr tP0 tP1 tY = true} :
    let L := LayeredTuple.ofTrie7 tI tP0 tP1 tX tQ0 tQ1 tY portsOut portsInt
      hI hP0 hP1 hnodupOut hcheckOut hcardP0 hcardP1 hX hdisjX
      hQ0 hQ1 hnodupInt hcheckInt hcardQ0 hcardQ1 hIntOut hY hdisjY_int hdisjY_out
    L.layeredProfile.outer.a = tI.card ∧
    L.layeredProfile.outer.b = portsOut.length ∧
    L.layeredProfile.outer.c = tX.card ∧
    L.layeredProfile.outer.d = Trie7.countOutside tP0 tP1 tX ∧
    L.layeredProfile.outer.h = tX.countIf (fun w => tP0.inClosedNbr w) ∧
    L.layeredProfile.outer.v = tX.countIf (fun w => tP1.inClosedNbr w) ∧
    L.layeredProfile.bX = portsInt.length ∧
    L.layeredProfile.e = tY.card ∧
    L.layeredProfile.dY = Trie7.countOutside tP0 tP1 tY ∧
    L.layeredProfile.hY = tY.countIf (fun w => tP0.inClosedNbr w) ∧
    L.layeredProfile.vY = tY.countIf (fun w => tP1.inClosedNbr w) := by
  classical
  dsimp only
  have hout := HeteroGadget.ofTrie7_asymProfile
    (tI := tI) (hI := hI) (hP0 := hP0) (hP1 := hP1)
    (hnodup := hnodupOut) (hcheck := hcheckOut) hcardP0 hcardP1 tX hX hdisjX
  have hYout := HeteroGadget.ofTrie7_asymProfile
    (tI := tI) (hI := hI) (hP0 := hP0) (hP1 := hP1)
    (hnodup := hnodupOut) (hcheck := hcheckOut) hcardP0 hcardP1 tY hY hdisjY_out
  dsimp only at hout hYout
  refine ⟨hout.1, hout.2.1, hout.2.2.1, hout.2.2.2.1, hout.2.2.2.2.1, hout.2.2.2.2.2,
    ?_, Trie7.toFinset_card tY, ?_, ?_, ?_⟩
  · change (portsInt.map Prod.fst).toFinset.card = portsInt.length
    rw [List.toFinset_card_of_nodup hnodupInt, List.length_map]
  · exact hYout.2.2.2.1
  · exact hYout.2.2.2.2.1
  · exact hYout.2.2.2.2.2

/-- Converting a `ValidTuple G` to a `HeteroGadget G` preserves the 4-parameter profile. -/
theorem ValidTuple.toHeteroGadget_toProfile {V : Type*} [Fintype V] {G : SimpleGraph V}
    (τ : ValidTuple G) : τ.toHeteroGadget.asymProfile.toProfile = τ.profile := by
  classical
  apply Profile.ext
  · rfl
  · rfl
  · rfl
  · show τ.toHeteroGadget.aux.OSlice.card = τ.O.card
    congr 1
    ext x
    simp only [AuxCode.mem_OSlice, ValidTuple.mem_O, ValidTuple.toHeteroGadget,
      PortCore.inP0Nbr, PortCore.inP1Nbr]
    refine and_congr Iff.rfl (and_congr (not_congr ?_) (not_congr ?_))
    · exact ⟨fun ⟨s, hs, hc⟩ => ⟨s, hs, close_symm hc⟩, fun ⟨s, hs, hc⟩ => ⟨s, hs, close_symm hc⟩⟩
    · exact ⟨fun ⟨s, hs, hc⟩ => ⟨s, hs, close_symm hc⟩, fun ⟨s, hs, hc⟩ => ⟨s, hs, close_symm hc⟩⟩

/-! ## Concrete 5D Base `HeteroGadget` (`baseHetero5D`, `(367, 8, 367, 322, 19, 26)`) -/

/-- Ready-made 5D heterogeneous gadget on `strongPow C7 5` derived from `baseTuple5D`
(`X_322` on unique bipartition `bip = 1`). -/
def baseHetero5D : HeteroGadget (strongPow C7 5) :=
  baseTuple5D.toHeteroGadget

/-- Factored pure-kernel certificate: `|baseX ∩ N[baseP0]| = 19`. -/
theorem baseX_countH : baseX.countIf (fun w => baseP0.inClosedNbr w) = 19 := rfl

/-- Factored pure-kernel certificate: `|baseX ∩ N[baseP1]| = 26`. -/
theorem baseX_countV : baseX.countIf (fun w => baseP1.inClosedNbr w) = 26 := rfl

/-- Exact 6-parameter asymmetric profile of `baseHetero5D`: `(367, 8, 367, 322, 19, 26)`. -/
theorem baseHetero5D_asymProfile :
    baseHetero5D.asymProfile = ⟨367, 8, 367, 322, 19, 26, by decide, by decide⟩ := by
  classical
  have hprof : baseHetero5D.asymProfile.toProfile = bpzBaseProfile := by
    rw [baseHetero5D, ValidTuple.toHeteroGadget_toProfile, baseTuple5D_profile]
  have ha : baseHetero5D.asymProfile.a = 367 := congrArg Profile.a hprof
  have hb : baseHetero5D.asymProfile.b = 8 := congrArg Profile.b hprof
  have hc : baseHetero5D.asymProfile.c = 367 := congrArg Profile.c hprof
  have hd : baseHetero5D.asymProfile.d = 322 := congrArg Profile.d hprof
  have hXeq : baseHetero5D.aux.X = baseX.toFinset := rfl
  have hP0eq : baseHetero5D.core.P0 = baseP0.toFinset := by
    have hEq : baseHetero5D.core.P0 = baseTuple5D.P0 := by
      ext x
      simp [PortCore.mem_P0, ValidTuple.mem_P0, baseHetero5D, ValidTuple.toHeteroGadget]
    rw [hEq, baseTuple5D_P0_eq]
  have hP1eq : baseHetero5D.core.P1 = baseP1.toFinset := by
    have hEq : baseHetero5D.core.P1 = baseTuple5D.P1 := by
      ext x
      simp [PortCore.mem_P1, ValidTuple.mem_P1, baseHetero5D, ValidTuple.toHeteroGadget]
    rw [hEq, baseTuple5D_P1_eq]
  have hh : baseHetero5D.asymProfile.h = 19 := by
    show baseHetero5D.aux.HSlice.card = 19
    rw [← baseX_countH, Trie7.countIf_eq]
    apply congrArg Finset.card
    ext w
    simp only [AuxCode.mem_HSlice, hXeq, Finset.mem_filter]
    refine and_congr Iff.rfl ?_
    rw [baseHetero5D.core.inP0Nbr_iff_mem_P0, hP0eq, Trie7.inClosedNbr_eq_true_iff]
  have hv : baseHetero5D.asymProfile.v = 26 := by
    show baseHetero5D.aux.VSlice.card = 26
    rw [← baseX_countV, Trie7.countIf_eq]
    apply congrArg Finset.card
    ext w
    simp only [AuxCode.mem_VSlice, hXeq, Finset.mem_filter]
    refine and_congr Iff.rfl ?_
    rw [baseHetero5D.core.inP1Nbr_iff_mem_P1, hP1eq, Trie7.inClosedNbr_eq_true_iff]
  cases h : baseHetero5D.asymProfile with
  | mk a b c d h' v hba hdhv =>
    rw [h] at ha hb hc hd hh hv
    simp only [AsymProfile.mk.injEq]
    exact ⟨ha, hb, hc, hd, hh, hv⟩

end ShannonC7
