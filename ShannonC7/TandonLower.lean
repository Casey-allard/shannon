import ShannonC7.TandonDataLower
import ShannonC7.Decimal
import ShannonC7.PortfolioLower

namespace ShannonC7

open SimpleGraph TandonData

section TrieAndIsoHelpers

theorem trieAll_eq_true : {d : ℕ} → (p : StrongPowV (ZMod 7) d → Bool) → (t : Trie7 d) →
    (trieAll p t = true ↔ ∀ w ∈ t.toFinset, p w = true)
  | _, _, .empty => by
    simp [trieAll, Trie7.toFinset_empty]
  | 0, p, .leaf => by
    simp only [trieAll, Trie7.toFinset_leaf, Finset.mem_univ, forall_true_left]
    exact ⟨fun h ⟨⟩ => h, fun h => h PUnit.unit⟩
  | d + 1, p, .node c0 c1 c2 c3 c4 c5 c6 => by
    have ih0 := trieAll_eq_true (fun r => p (0, r)) c0
    have ih1 := trieAll_eq_true (fun r => p (1, r)) c1
    have ih2 := trieAll_eq_true (fun r => p (2, r)) c2
    have ih3 := trieAll_eq_true (fun r => p (3, r)) c3
    have ih4 := trieAll_eq_true (fun r => p (4, r)) c4
    have ih5 := trieAll_eq_true (fun r => p (5, r)) c5
    have ih6 := trieAll_eq_true (fun r => p (6, r)) c6
    simp only [trieAll, Bool.and_eq_true]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ ⟨a, rest⟩ hw
      rw [Trie7.mem_toFinset_iff_memBool, Trie7.memBool_succ] at hw
      have hmem : rest ∈ (Trie7.child (.node c0 c1 c2 c3 c4 c5 c6) a).toFinset :=
        Trie7.mem_toFinset_iff_memBool.mpr hw
      fin_cases a
      · exact ih0.mp h0 rest hmem
      · exact ih1.mp h1 rest hmem
      · exact ih2.mp h2 rest hmem
      · exact ih3.mp h3 rest hmem
      · exact ih4.mp h4 rest hmem
      · exact ih5.mp h5 rest hmem
      · exact ih6.mp h6 rest hmem
    · intro h
      refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact ih0.mpr fun r hr => h (0, r) (Trie7.mem_toFinset_iff_memBool.mpr (by
          rw [Trie7.memBool_succ]; exact Trie7.mem_toFinset_iff_memBool.mp hr))
      · exact ih1.mpr fun r hr => h (1, r) (Trie7.mem_toFinset_iff_memBool.mpr (by
          rw [Trie7.memBool_succ]; exact Trie7.mem_toFinset_iff_memBool.mp hr))
      · exact ih2.mpr fun r hr => h (2, r) (Trie7.mem_toFinset_iff_memBool.mpr (by
          rw [Trie7.memBool_succ]; exact Trie7.mem_toFinset_iff_memBool.mp hr))
      · exact ih3.mpr fun r hr => h (3, r) (Trie7.mem_toFinset_iff_memBool.mpr (by
          rw [Trie7.memBool_succ]; exact Trie7.mem_toFinset_iff_memBool.mp hr))
      · exact ih4.mpr fun r hr => h (4, r) (Trie7.mem_toFinset_iff_memBool.mpr (by
          rw [Trie7.memBool_succ]; exact Trie7.mem_toFinset_iff_memBool.mp hr))
      · exact ih5.mpr fun r hr => h (5, r) (Trie7.mem_toFinset_iff_memBool.mpr (by
          rw [Trie7.memBool_succ]; exact Trie7.mem_toFinset_iff_memBool.mp hr))
      · exact ih6.mpr fun r hr => h (6, r) (Trie7.mem_toFinset_iff_memBool.mpr (by
          rw [Trie7.memBool_succ]; exact Trie7.mem_toFinset_iff_memBool.mp hr))

theorem trieAny_eq_true (p : StrongPowV (ZMod 7) 5 → Bool) (t : Trie7 5) :
    trieAny p t = true ↔ ∃ w ∈ t.toFinset, p w = true := by
  simp only [trieAny, Bool.not_eq_true', Bool.eq_false_iff, ne_eq]
  rw [trieAll_eq_true]
  push Not
  refine ⟨fun ⟨w, hw, hp⟩ => ⟨w, hw, by cases h : p w <;> simp_all⟩,
    fun ⟨w, hw, hp⟩ => ⟨w, hw, by simp [hp]⟩⟩

theorem sep_of_trieDisjoint {d : ℕ} {t₁ t₂ : Trie7 d} (h : t₁.disjoint t₂ = true) :
    Sep (strongPow C7 d) t₁.toFinset t₂.toFinset := by
  intro x hx y hy
  exact Trie7.disjoint_sound h x y
    ((Trie7.mem_toFinset t₁ x).mp hx) ((Trie7.mem_toFinset t₂ y).mp hy)

theorem sep_of_trieAll_not_inNbr {d : ℕ} {t₁ t₂ : Trie7 d}
    (h : trieAll (fun w => !t₂.inClosedNbr w) t₁ = true) :
    Sep (strongPow C7 d) t₁.toFinset t₂.toFinset := by
  intro x hx y hy hxy
  have hnot := (trieAll_eq_true _ t₁).mp h x hx
  simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq] at hnot
  apply hnot
  rw [Trie7.inClosedNbr_eq_true_iff]
  exact ⟨y, hy, hxy.imp Eq.symm SimpleGraph.Adj.symm⟩

theorem c7_close_bool_iff (a b : ZMod 7) :
    (a == b || a - b == 1 || b - a == 1) = true ↔ a = b ∨ C7.Adj a b := by
  revert a b; decide

theorem strongProd_close_iff {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    (u v : V₁ × V₂) :
    (u = v ∨ (G₁ ⊠ G₂).Adj u v) ↔
      (u.1 = v.1 ∨ G₁.Adj u.1 v.1) ∧ (u.2 = v.2 ∨ G₂.Adj u.2 v.2) := by
  simp only [strongProd_adj, Prod.ext_iff]
  by_cases h1 : u.1 = v.1 <;> by_cases h2 : u.2 = v.2 <;> tauto

theorem strongPow_succ_close_iff {V : Type*} (G : SimpleGraph V) (d : ℕ)
    (u v : StrongPowV V (d + 1)) :
    (u = v ∨ (strongPow G (d + 1)).Adj u v) ↔
      (u.1 = v.1 ∨ G.Adj u.1 v.1) ∧ (u.2 = v.2 ∨ (strongPow G d).Adj u.2 v.2) :=
  strongProd_close_iff (G₁ := G) (G₂ := strongPow G d) u v

theorem strongPow0_close_iff {V : Type*} (G : SimpleGraph V) (u v : StrongPowV V 0) :
    u = v ∨ (strongPow G 0).Adj u v := by
  left; cases u; cases v; rfl

theorem strongPow5_close_iff (u v : StrongPowV (ZMod 7) 5) :
    (u = v ∨ (strongPow C7 5).Adj u v) ↔
      (u.1 = v.1 ∨ C7.Adj u.1 v.1) ∧
      (u.2.1 = v.2.1 ∨ C7.Adj u.2.1 v.2.1) ∧
      (u.2.2.1 = v.2.2.1 ∨ C7.Adj u.2.2.1 v.2.2.1) ∧
      (u.2.2.2.1 = v.2.2.2.1 ∨ C7.Adj u.2.2.2.1 v.2.2.2.1) ∧
      (u.2.2.2.2.1 = v.2.2.2.2.1 ∨ C7.Adj u.2.2.2.2.1 v.2.2.2.2.1) := by
  rw [strongPow_succ_close_iff C7 4 u v]
  rw [strongPow_succ_close_iff C7 3 u.2 v.2]
  rw [strongPow_succ_close_iff C7 2 u.2.2 v.2.2]
  rw [strongPow_succ_close_iff C7 1 u.2.2.2 v.2.2.2]
  rw [strongPow_succ_close_iff C7 0 u.2.2.2.2 v.2.2.2.2]
  simp only [strongPow0_close_iff C7, and_true]

theorem word5AdjOrEq_iff (u v : StrongPowV (ZMod 7) 5) :
    word5AdjOrEq u v = true ↔ u = v ∨ (strongPow C7 5).Adj u v := by
  rw [strongPow5_close_iff]
  simp only [word5AdjOrEq, Bool.and_eq_true, c7_close_bool_iff, and_assoc]

theorem c7_close_sub_iff (a b : ZMod 7) :
    (2 - a = 2 - b ∨ C7.Adj (2 - a) (2 - b)) ↔ (a = b ∨ C7.Adj a b) := by
  revert a b; decide

def T5_iso : strongPow C7 5 ≃g strongPow C7 5 where
  toFun := T5_fn
  invFun := T5_inv
  left_inv x := by
    rcases x with ⟨w0, w1, w2, w3, w4, ⟨⟩⟩
    simp [T5_fn, T5_inv]
  right_inv x := by
    rcases x with ⟨u0, u1, u2, u3, u4, ⟨⟩⟩
    simp [T5_fn, T5_inv]
  map_rel_iff' := by
    intro u v
    have hneq : T5_fn u ≠ T5_fn v ↔ u ≠ v := by
      constructor
      · intro h heq; exact h (congrArg T5_fn heq)
      · intro h heq; apply h
        have hi := congrArg T5_inv heq
        rcases u with ⟨u0, u1, u2, u3, u4, ⟨⟩⟩
        rcases v with ⟨v0, v1, v2, v3, v4, ⟨⟩⟩
        simpa [T5_fn, T5_inv] using hi
    have hclose : (T5_fn u = T5_fn v ∨ (strongPow C7 5).Adj (T5_fn u) (T5_fn v)) ↔
        (u = v ∨ (strongPow C7 5).Adj u v) := by
      rw [strongPow5_close_iff, strongPow5_close_iff]
      rcases u with ⟨u0, u1, u2, u3, u4, ⟨⟩⟩
      rcases v with ⟨v0, v1, v2, v3, v4, ⟨⟩⟩
      simp only [T5_fn, c7_close_sub_iff]
      tauto
    constructor
    · intro hadj
      rcases hclose.mp (Or.inr hadj) with heq | h'
      · exact absurd heq (hneq.mp hadj.ne)
      · exact h'
    · intro hadj
      rcases hclose.mpr (Or.inr hadj) with heq | h'
      · exact absurd heq (hneq.mpr hadj.ne)
      · exact h'

def prodCongr {V₁ V₂ W₁ W₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e₁ : G₁ ≃g H₁) (e₂ : G₂ ≃g H₂) : (G₁ ⊠ G₂) ≃g (H₁ ⊠ H₂) where
  toEquiv := Equiv.prodCongr e₁.toEquiv e₂.toEquiv
  map_rel_iff' := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    simp only [Equiv.prodCongr_apply, Prod.map_apply, strongProd_adj, ne_eq, Prod.ext_iff,
      RelIso.coe_fn_toEquiv]
    constructor
    · rintro ⟨hne, h1, h2⟩
      refine ⟨fun ⟨ha, hb⟩ => hne ⟨by rw [ha], by rw [hb]⟩, ?_, ?_⟩
      · rcases h1 with heq | hadj
        · exact Or.inl (e₁.injective heq)
        · exact Or.inr ((e₁.map_rel_iff).mp hadj)
      · rcases h2 with heq | hadj
        · exact Or.inl (e₂.injective heq)
        · exact Or.inr ((e₂.map_rel_iff).mp hadj)
    · rintro ⟨hne, h1, h2⟩
      refine ⟨fun ⟨ha, hb⟩ => hne ⟨e₁.injective ha, e₂.injective hb⟩, ?_, ?_⟩
      · rcases h1 with rfl | hadj
        · exact Or.inl rfl
        · exact Or.inr ((e₁.map_rel_iff).mpr hadj)
      · rcases h2 with rfl | hadj
        · exact Or.inl rfl
        · exact Or.inr ((e₂.map_rel_iff).mpr hadj)

def T5_pi_iso : strongPowPi C7 5 ≃g strongPowPi C7 5 :=
  (strongPowEquivPi C7 5).symm.trans (T5_iso.trans (strongPowEquivPi C7 5))

def T10_pi_iso : strongPowPi C7 10 ≃g strongPowPi C7 10 :=
  (strongProdIsoAdd C7 5 5).symm.trans ((prodCongr T5_pi_iso T5_pi_iso).trans (strongProdIsoAdd C7 5 5))

def T15_pi_iso : strongPowPi C7 15 ≃g strongPowPi C7 15 :=
  (strongProdIsoAdd C7 10 5).symm.trans ((prodCongr T10_pi_iso T5_pi_iso).trans (strongProdIsoAdd C7 10 5))

def T30_pi_iso : strongPowPi C7 30 ≃g strongPowPi C7 30 :=
  (strongProdIsoAdd C7 15 15).symm.trans ((prodCongr T15_pi_iso T15_pi_iso).trans (strongProdIsoAdd C7 15 15))

end TrieAndIsoHelpers

section Base5AndMaps

@[irreducible] def piSet5 (t : Trie7 5) : Finset (Fin 5 → ZMod 7) :=
  t.toFinset.map (strongPowEquivPi C7 5).toEquiv.toEmbedding

theorem piSet5_def (t : Trie7 5) :
    piSet5 t = t.toFinset.map (strongPowEquivPi C7 5).toEquiv.toEmbedding := by
  unfold piSet5; rfl

theorem piSet5_card (t : Trie7 5) : (piSet5 t).card = t.card := by
  rw [piSet5_def, Finset.card_map, Trie7.toFinset_card]

theorem piSet5_map_T5 {t tT : Trie7 5}
    (hmap : trieAll (fun w => tT.memBool (T5_fn w)) t = true)
    (hcard : tT.card = t.card) :
    (piSet5 t).map T5_pi_iso.toEquiv.toEmbedding = piSet5 tT := by
  have hsub : t.toFinset.map T5_iso.toEquiv.toEmbedding ⊆ tT.toFinset := by
    intro y hy
    rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact Trie7.mem_toFinset_iff_memBool.mpr ((trieAll_eq_true _ t).mp hmap x hx)
  have heq : t.toFinset.map T5_iso.toEquiv.toEmbedding = tT.toFinset := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_map, Trie7.toFinset_card, Trie7.toFinset_card, hcard]
  rw [piSet5_def, piSet5_def, ← heq, Finset.map_map, Finset.map_map]
  ext y
  simp only [Finset.mem_map, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
    T5_pi_iso]
  rfl

def baseR5_P : Letter → Finset (StrongPowV (ZMod 7) 5)
  | .B => tB5.toFinset
  | .N => tX05.toFinset
  | .A => tXV5.toFinset
  | .D => tXH5.toFinset
  | .O => tS5.toFinset
  | .H => tPH5.toFinset
  | .V => tPV5.toFinset

private theorem baseR5_pow_hindep (a : Letter) :
    (strongPow C7 5).IsIndepSet (baseR5_P a : Set (StrongPowV (ZMod 7) 5)) := by
  cases a
  · exact Trie7.to_indepSet_of_isIndep tB5_indep
  · exact Trie7.to_indepSet_of_isIndep tX05_indep
  · exact Trie7.to_indepSet_of_isIndep tXV5_indep
  · exact Trie7.to_indepSet_of_isIndep tXH5_indep
  · exact Trie7.to_indepSet_of_isIndep tS5_indep
  · exact Trie7.to_indepSet_of_isIndep tPH5_indep
  · exact Trie7.to_indepSet_of_isIndep tPV5_indep

private theorem baseR5_pow_hsep (a b : Letter) (hab : Letter.sep a b = true) :
    Sep (strongPow C7 5) (baseR5_P a) (baseR5_P b) := by
  cases a <;> cases b <;> simp only [Letter.sep, reduceCtorEq] at hab <;> dsimp only [baseR5_P]
  · exact sep_of_trieAll_not_inNbr tB5_sep_S5
  · exact sep_of_trieAll_not_inNbr tB5_sep_PH5
  · exact sep_of_trieAll_not_inNbr tB5_sep_PV5
  · exact sep_of_trieAll_not_inNbr tX05_sep_XV5
  · exact sep_of_trieAll_not_inNbr tX05_sep_XH5
  · exact sep_of_trieAll_not_inNbr tX05_sep_S5
  · exact sep_of_trieAll_not_inNbr tX05_sep_PH5
  · exact sep_of_trieAll_not_inNbr tX05_sep_PV5
  · exact (sep_of_trieAll_not_inNbr tX05_sep_XV5).symm
  · exact sep_of_trieAll_not_inNbr tXV5_sep_XH5
  · exact sep_of_trieAll_not_inNbr tXV5_sep_PH5
  · exact (sep_of_trieAll_not_inNbr tX05_sep_XH5).symm
  · exact (sep_of_trieAll_not_inNbr tXV5_sep_XH5).symm
  · exact sep_of_trieAll_not_inNbr tXH5_sep_PV5
  · exact (sep_of_trieAll_not_inNbr tB5_sep_S5).symm
  · exact (sep_of_trieAll_not_inNbr tX05_sep_S5).symm
  · exact (sep_of_trieAll_not_inNbr tB5_sep_PH5).symm
  · exact (sep_of_trieAll_not_inNbr tX05_sep_PH5).symm
  · exact (sep_of_trieAll_not_inNbr tXV5_sep_PH5).symm
  · exact (sep_of_trieAll_not_inNbr tB5_sep_PV5).symm
  · exact (sep_of_trieAll_not_inNbr tX05_sep_PV5).symm
  · exact (sep_of_trieAll_not_inNbr tXH5_sep_PV5).symm

def baseR5_pow : Realisation Letter Letter.sep (strongPow C7 5) where
  P := baseR5_P
  hindep := baseR5_pow_hindep
  hsep := baseR5_pow_hsep

@[irreducible] def baseR5 : Realisation Letter Letter.sep (strongPowPi C7 5) :=
  baseR5_pow.mapIso (strongPowEquivPi C7 5)

theorem baseR5_def : baseR5 = baseR5_pow.mapIso (strongPowEquivPi C7 5) := by
  unfold baseR5; rfl

theorem baseR5_P_eq :
    baseR5.P .B = piSet5 tB5 ∧ baseR5.P .N = piSet5 tX05 ∧
    baseR5.P .A = piSet5 tXV5 ∧ baseR5.P .D = piSet5 tXH5 ∧
    baseR5.P .O = piSet5 tS5 ∧ baseR5.P .H = piSet5 tPH5 ∧
    baseR5.P .V = piSet5 tPV5 := by
  rw [baseR5_def]
  simp only [piSet5_def]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem baseR5_w :
    baseR5.w .B = 359 ∧ baseR5.w .N = 322 ∧ baseR5.w .A = 19 ∧ baseR5.w .D = 26 ∧
    baseR5.w .O = 8 ∧ baseR5.w .H = 8 ∧ baseR5.w .V = 8 := by
  rcases baseR5_P_eq with ⟨hB, hN, hA, hD, hO, hH, hV⟩
  simp only [Realisation.w, hB, hN, hA, hD, hO, hH, hV, piSet5_card]
  exact ⟨tB5_card, tX05_card, tXV5_card, tXH5_card, tS5_card, tPH5_card, tPV5_card⟩

end Base5AndMaps

section ProdAndHistAlgebra

def inNbr {V : Type*} (G : SimpleGraph V) (S : Finset V) (x : V) : Prop :=
  ∃ y ∈ S, y = x ∨ G.Adj y x

theorem inNbr_union {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S T : Finset V) (x : V) :
    inNbr G (S ∪ T) x ↔ inNbr G S x ∨ inNbr G T x := by
  simp only [inNbr, Finset.mem_union]
  constructor
  · rintro ⟨y, hy | hy, h⟩
    · exact Or.inl ⟨y, hy, h⟩
    · exact Or.inr ⟨y, hy, h⟩
  · rintro (⟨y, hy, h⟩ | ⟨y, hy, h⟩)
    · exact ⟨y, Or.inl hy, h⟩
    · exact ⟨y, Or.inr hy, h⟩

theorem inNbr_biUnion {V ι : Type*} [DecidableEq V] (G : SimpleGraph V) (I : Finset ι) (f : ι → Finset V) (x : V) :
    inNbr G (I.biUnion f) x ↔ ∃ i ∈ I, inNbr G (f i) x := by
  simp only [inNbr, Finset.mem_biUnion]
  constructor
  · rintro ⟨y, ⟨i, hi, hy⟩, h⟩; exact ⟨i, hi, y, hy, h⟩
  · rintro ⟨i, hi, y, hy, h⟩; exact ⟨y, ⟨i, hi, hy⟩, h⟩

theorem inNbr_mapIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (S : Finset V) (x : V) :
    inNbr H (S.map e.toEquiv.toEmbedding) (e x) ↔ inNbr G S x := by
  simp only [inNbr, Finset.mem_map, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, heq | hadj⟩
    · exact ⟨y, hy, Or.inl (e.injective heq)⟩
    · exact ⟨y, hy, Or.inr ((e.map_rel_iff).mp hadj)⟩
  · rintro ⟨y, hy, rfl | hadj⟩
    · exact ⟨e y, ⟨y, hy, rfl⟩, Or.inl rfl⟩
    · exact ⟨e y, ⟨y, hy, rfl⟩, Or.inr ((e.map_rel_iff).mpr hadj)⟩

theorem inNbr_piSet5 (t : Trie7 5) (w : StrongPowV (ZMod 7) 5) :
    inNbr (strongPowPi C7 5) (piSet5 t) (strongPowEquivPi C7 5 w) ↔ t.inClosedNbr w = true := by
  rw [piSet5_def, inNbr_mapIso (strongPowEquivPi C7 5) t.toFinset w, Trie7.inClosedNbr_eq_true_iff]
  rfl

theorem sep_iff_not_inNbr {V : Type*} {G : SimpleGraph V} {A B : Finset V} :
    Sep G A B ↔ ∀ x ∈ A, ¬ inNbr G B x := by
  constructor
  · intro h x hx ⟨y, hy, hc⟩
    exact h x hx y hy (hc.imp Eq.symm SimpleGraph.Adj.symm)
  · intro h x hx y hy hc
    exact h x hx ⟨y, hy, hc.imp Eq.symm SimpleGraph.Adj.symm⟩

@[irreducible] def prodSet {dL dR : ℕ} (A : Finset (Fin dL → ZMod 7)) (B : Finset (Fin dR → ZMod 7)) :
    Finset (Fin (dL + dR) → ZMod 7) :=
  (A ×ˢ B).map (strongProdIsoAdd C7 dL dR).toEquiv.toEmbedding

theorem prodSet_def {dL dR : ℕ} (A : Finset (Fin dL → ZMod 7)) (B : Finset (Fin dR → ZMod 7)) :
    prodSet A B = (A ×ˢ B).map (strongProdIsoAdd C7 dL dR).toEquiv.toEmbedding := by
  unfold prodSet; rfl

theorem prodSet_card {dL dR : ℕ} (A : Finset (Fin dL → ZMod 7)) (B : Finset (Fin dR → ZMod 7)) :
    (prodSet A B).card = A.card * B.card := by
  rw [prodSet_def, Finset.card_map, Finset.card_product]

theorem prodSet_disjoint {dL dR : ℕ} {A₁ A₂ : Finset (Fin dL → ZMod 7)}
    {B₁ B₂ : Finset (Fin dR → ZMod 7)} (h : Disjoint A₁ A₂ ∨ Disjoint B₁ B₂) :
    Disjoint (prodSet A₁ B₁) (prodSet A₂ B₂) := by
  rw [prodSet_def, prodSet_def, Finset.disjoint_map]
  rw [Finset.disjoint_left]
  intro ⟨x, y⟩ h1 h2
  rw [Finset.mem_product] at h1 h2
  rcases h with hA | hB
  · exact (Finset.disjoint_left.mp hA) h1.1 h2.1
  · exact (Finset.disjoint_left.mp hB) h1.2 h2.2

theorem prodSet_sep {dL dR : ℕ} {A₁ A₂ : Finset (Fin dL → ZMod 7)}
    {B₁ B₂ : Finset (Fin dR → ZMod 7)}
    (h : Sep (strongPowPi C7 dL) A₁ A₂ ∨ Sep (strongPowPi C7 dR) B₁ B₂) :
    Sep (strongPowPi C7 (dL + dR)) (prodSet A₁ B₁) (prodSet A₂ B₂) := by
  intro u hu v hv hc
  rw [prodSet_def] at hu hv
  rcases Finset.mem_map.mp hu with ⟨⟨x₁, y₁⟩, hxy₁, rfl⟩
  rcases Finset.mem_map.mp hv with ⟨⟨x₂, y₂⟩, hxy₂, rfl⟩
  have hc' : (x₁, y₁) = (x₂, y₂) ∨ (strongPowPi C7 dL ⊠ strongPowPi C7 dR).Adj (x₁, y₁) (x₂, y₂) := by
    rcases hc with heq | hadj
    · left; exact (strongProdIsoAdd C7 dL dR).injective heq
    · right; exact ((strongProdIsoAdd C7 dL dR).map_rel_iff).mp hadj
  rcases h with hA | hB
  · exact sep_prod_left hA (x₁, y₁) hxy₁ (x₂, y₂) hxy₂ hc'
  · exact sep_prod_right hB (x₁, y₁) hxy₁ (x₂, y₂) hxy₂ hc'

theorem inNbr_prodSet {dL dR : ℕ} (A : Finset (Fin dL → ZMod 7))
    (B : Finset (Fin dR → ZMod 7)) (x : Fin dL → ZMod 7) (y : Fin dR → ZMod 7) :
    inNbr (strongPowPi C7 (dL + dR)) (prodSet A B) (strongProdIsoAdd C7 dL dR (x, y)) ↔
      inNbr (strongPowPi C7 dL) A x ∧ inNbr (strongPowPi C7 dR) B y := by
  rw [prodSet_def, inNbr_mapIso (strongProdIsoAdd C7 dL dR) (A ×ˢ B) (x, y)]
  simp only [inNbr, Finset.mem_product, strongProd_close_iff]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, h1, h2⟩
    exact ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
  · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
    exact ⟨⟨a, b⟩, ⟨ha, hb⟩, h1, h2⟩

theorem prodSet_map_iso {dL dR : ℕ}
    (eL : strongPowPi C7 dL ≃g strongPowPi C7 dL)
    (eR : strongPowPi C7 dR ≃g strongPowPi C7 dR)
    (A : Finset (Fin dL → ZMod 7)) (B : Finset (Fin dR → ZMod 7)) :
    (prodSet A B).map ((strongProdIsoAdd C7 dL dR).symm.trans
      ((prodCongr eL eR).trans (strongProdIsoAdd C7 dL dR))).toEquiv.toEmbedding =
      prodSet (A.map eL.toEquiv.toEmbedding) (B.map eR.toEquiv.toEmbedding) := by
  ext z
  simp only [prodSet_def, Finset.mem_map, Finset.mem_product, Equiv.coe_toEmbedding,
    RelIso.coe_fn_toEquiv, RelIso.trans_apply]
  constructor
  · rintro ⟨_, ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩, rfl⟩
    refine ⟨(eL x, eR y), ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, ?_⟩
    simp [prodCongr]
  · rintro ⟨⟨x', y'⟩, ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, rfl⟩
    refine ⟨strongProdIsoAdd C7 dL dR (x, y), ⟨(x, y), ⟨hx, hy⟩, rfl⟩, ?_⟩
    simp [prodCongr]

end ProdAndHistAlgebra

section HistAndVec16Algebra

def vec16Eval (x : Vec16) (g : Nat → Nat) : Nat :=
  x.v0 * g 0 + x.v1 * g 1 + x.v2 * g 2 + x.v3 * g 3 +
  x.v4 * g 4 + x.v5 * g 5 + x.v6 * g 6 + x.v7 * g 7 +
  x.v8 * g 8 + x.v9 * g 9 + x.v10 * g 10 + x.v11 * g 11 +
  x.v12 * g 12 + x.v13 * g 13 + x.v14 * g 14 + x.v15 * g 15

theorem vec16Eval_eq_sum (x : Vec16) (g : Nat → Nat) :
    vec16Eval x g = ∑ i ∈ Finset.range 16, Vec16.get x i * g i := by
  simp only [vec16Eval, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Vec16.get]
  omega

theorem vec16Eval_zero (g : Nat → Nat) : vec16Eval ({} : Vec16) g = 0 := by
  simp [vec16Eval]

theorem vec16Eval_add (a b : Vec16) (g : Nat → Nat) :
    vec16Eval (a.add b) g = vec16Eval a g + vec16Eval b g := by
  dsimp [vec16Eval, Vec16.add]
  simp only [Nat.add_mul]
  omega

theorem vec16Eval_addAt (x : Vec16) (i : Fin 16) (val : Nat) (g : Nat → Nat) :
    vec16Eval (x.addAt i.val val) g = vec16Eval x g + val * g i.val := by
  fin_cases i <;>
    (dsimp [vec16Eval, Vec16.addAt]; simp only [Nat.add_mul]; omega)

def histEval (h : List (Nat × Nat)) (g : Nat → Nat) : Nat :=
  (h.map (fun p => p.2 * g p.1)).sum

theorem histEval_addHistCount (k cnt : Nat) (h : List (Nat × Nat)) (g : Nat → Nat) :
    histEval (addHistCount k cnt h) g = cnt * g k + histEval h g := by
  induction h with
  | nil => simp [histEval, addHistCount]
  | cons p rest ih =>
    rcases p with ⟨k', c⟩
    simp only [addHistCount]
    by_cases hkk : (k == k') = true
    · simp only [hkk, ite_true, histEval, List.map_cons, List.sum_cons]
      have heq : k = k' := by simpa using hkk
      subst heq; simp only [Nat.add_mul]; omega
    · have hf : (k == k') = false := Bool.eq_false_iff.mpr hkk
      simp only [hf, Bool.false_eq_true, ite_false, histEval, List.map_cons, List.sum_cons] at *
      rw [ih]; omega

theorem histEval_mergeHist (h₁ h₂ : List (Nat × Nat)) (g : Nat → Nat) :
    histEval (mergeHist h₁ h₂) g = histEval h₁ g + histEval h₂ g := by
  induction h₁ generalizing h₂ with
  | nil => simp [mergeHist, histEval]
  | cons p rest ih =>
    rcases p with ⟨k, cnt⟩
    simp only [mergeHist, List.foldl_cons] at *
    rw [ih (addHistCount k cnt h₂), histEval_addHistCount]
    simp only [histEval, List.map_cons, List.sum_cons]
    omega

def pairEmb {d : ℕ} (a : ZMod 7) : StrongPowV (ZMod 7) d ↪ StrongPowV (ZMod 7) (d + 1) :=
  ⟨fun r => (a, r), fun _ _ h => (Prod.ext_iff.mp h).2⟩

theorem toFinset_node_eq {d : ℕ} (c0 c1 c2 c3 c4 c5 c6 : Trie7 d) :
    (Trie7.node c0 c1 c2 c3 c4 c5 c6).toFinset =
      (Finset.univ : Finset (ZMod 7)).biUnion (fun a =>
        (Trie7.child (.node c0 c1 c2 c3 c4 c5 c6) a).toFinset.map (pairEmb a)) := by
  ext ⟨a, r⟩
  simp only [Trie7.mem_toFinset_iff_memBool, Trie7.memBool_succ, Finset.mem_biUnion,
    Finset.mem_univ, Finset.mem_map, pairEmb, Function.Embedding.coeFn_mk, true_and]
  constructor
  · intro h; exact ⟨a, r, h, rfl⟩
  · rintro ⟨a', r', h', heq⟩
    have ha : a' = a := (Prod.ext_iff.mp heq).1
    have hr : r' = r := (Prod.ext_iff.mp heq).2
    subst ha; subst hr; exact h'

theorem zmod7_sum (f : ZMod 7 → Nat) :
    (∑ a : ZMod 7, f a) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  change (∑ a : Fin 7, f a) = _
  rw [Fin.sum_univ_seven]
  omega

theorem sum_trie_node {d : ℕ} (c0 c1 c2 c3 c4 c5 c6 : Trie7 d)
    (F : StrongPowV (ZMod 7) (d + 1) → Nat) :
    (∑ w ∈ (Trie7.node c0 c1 c2 c3 c4 c5 c6).toFinset, F w) =
      (∑ r ∈ c0.toFinset, F (0, r)) + (∑ r ∈ c1.toFinset, F (1, r)) +
      (∑ r ∈ c2.toFinset, F (2, r)) + (∑ r ∈ c3.toFinset, F (3, r)) +
      (∑ r ∈ c4.toFinset, F (4, r)) + (∑ r ∈ c5.toFinset, F (5, r)) +
      (∑ r ∈ c6.toFinset, F (6, r)) := by
  rw [toFinset_node_eq, Finset.sum_biUnion]
  · simp only [Finset.sum_map, pairEmb, Function.Embedding.coeFn_mk]
    rw [zmod7_sum]
    rfl
  · intro a _ b _ hab
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_map.mp hx with ⟨r₁, _, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨r₂, _, heq⟩
    exact hab (Prod.ext_iff.mp heq).1.symm

theorem sum_punit (f : StrongPowV (ZMod 7) 0 → Nat) :
    (∑ w ∈ (Trie7.leaf).toFinset, f w) = f PUnit.unit := by
  rw [Trie7.toFinset_leaf]
  change ∑ w : PUnit, f w = f PUnit.unit
  have huniv : (Finset.univ : Finset PUnit) = ({PUnit.unit} : Finset PUnit) := by ext ⟨⟩; simp
  rw [huniv, Finset.sum_singleton]

theorem sum_trie_eq_histEval : {d : ℕ} → (f : StrongPowV (ZMod 7) d → Nat) →
    (t : Trie7 d) → (g : Nat → Nat) →
    ∑ w ∈ t.toFinset, g (f w) = histEval (histTrieAux f t) g
  | _, _, .empty, _ => by simp [Trie7.toFinset_empty, histTrieAux, histEval]
  | 0, f, .leaf, g => by
    rw [sum_punit (fun w => g (f w))]
    simp [histTrieAux, histEval]
  | d + 1, f, .node c0 c1 c2 c3 c4 c5 c6, g => by
    rw [sum_trie_node]
    simp only [histTrieAux, histEval_mergeHist]
    rw [sum_trie_eq_histEval (fun r => f (0, r)) c0 g,
        sum_trie_eq_histEval (fun r => f (1, r)) c1 g,
        sum_trie_eq_histEval (fun r => f (2, r)) c2 g,
        sum_trie_eq_histEval (fun r => f (3, r)) c3 g,
        sum_trie_eq_histEval (fun r => f (4, r)) c4 g,
        sum_trie_eq_histEval (fun r => f (5, r)) c5 g,
        sum_trie_eq_histEval (fun r => f (6, r)) c6 g]
    omega

theorem eval_dist5_3Trie : {d : ℕ} → (f : StrongPowV (ZMod 7) d → Nat) →
    (∀ w, f w < 16) → (t : Trie7 d) → (g : Nat → Nat) →
    vec16Eval (dist5_3Trie f t) g = ∑ w ∈ t.toFinset, g (f w)
  | _, _, _, .empty, g => by simp [dist5_3Trie, Trie7.toFinset_empty, vec16Eval_zero]
  | 0, f, hf, .leaf, g => by
    rw [sum_punit (fun w => g (f w))]
    simp only [dist5_3Trie]
    rw [vec16Eval_addAt ({} : Vec16) ⟨f PUnit.unit, hf PUnit.unit⟩ 1 g, vec16Eval_zero, zero_add, one_mul]
  | d + 1, f, hf, .node c0 c1 c2 c3 c4 c5 c6, g => by
    rw [sum_trie_node]
    simp only [dist5_3Trie, vec16Eval_add]
    rw [eval_dist5_3Trie (fun r => f (0, r)) (fun r => hf _) c0 g,
        eval_dist5_3Trie (fun r => f (1, r)) (fun r => hf _) c1 g,
        eval_dist5_3Trie (fun r => f (2, r)) (fun r => hf _) c2 g,
        eval_dist5_3Trie (fun r => f (3, r)) (fun r => hf _) c3 g,
        eval_dist5_3Trie (fun r => f (4, r)) (fun r => hf _) c4 g,
        eval_dist5_3Trie (fun r => f (5, r)) (fun r => hf _) c5 g,
        eval_dist5_3Trie (fun r => f (6, r)) (fun r => hf _) c6 g]
    omega

theorem sig5_3Bool_lt (w : StrongPowV (ZMod 7) 5) : sig5_3Bool w < 8 := by
  dsimp [sig5_3Bool]
  split_ifs <;> omega

theorem eval_dist5_3List (t : Trie7 5) (g : Nat → Nat) :
    vec16Eval (dist5_3List t) g = ∑ w ∈ t.toFinset, g (sig5_3Bool w) :=
  eval_dist5_3Trie sig5_3Bool (fun w => Nat.lt_trans (sig5_3Bool_lt w) (by decide)) t g

theorem nat_shiftRight_and_one_eq_testBit (x i : Nat) :
    ((x >>> i) &&& 1 == 1) = x.testBit i := by
  rw [Nat.and_one_is_mod]
  have hz := Nat.testBit_zero (x >>> i)
  rw [Nat.testBit_shiftRight, add_zero] at hz
  rw [hz]
  have hmod : x >>> i % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases h1 : x >>> i % 2 = 1
  · simp [h1]
  · have h0 : x >>> i % 2 = 0 := by omega
    simp [h0]

theorem nat_testBit_one (k : Nat) : (1 : Nat).testBit k = decide (k = 0) := by
  simpa using (Nat.testBit_two_pow (n := 0) (m := k)).trans (by simp [eq_comm])

theorem nat_and_one_shiftLeft_bne_zero (x i : Nat) :
    (x &&& (1 <<< i) != 0) = x.testBit i := by
  apply Bool.eq_iff_iff.mpr
  rw [bne_iff_ne, ne_eq]
  constructor
  · intro hne
    by_contra hfalse
    apply hne
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_shiftLeft, nat_testBit_one]
    by_cases hk : k = i
    · subst hk; simp [hfalse]
    · by_cases hle : i ≤ k
      · have hne0 : k - i ≠ 0 := by omega
        simp [hne0]
      · simp [hle]
  · intro htrue heq
    have hb := congrArg (fun n => Nat.testBit n i) heq
    rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit] at hb
    simp [htrue] at hb

theorem nat_or_eq_zero_iff (a b : Nat) : (a ||| b = 0) ↔ (a = 0 ∧ b = 0) := by
  constructor
  · intro h
    constructor <;> apply Nat.eq_of_testBit_eq <;> intro k <;>
      have hk := congrArg (fun n => Nat.testBit n k) h <;>
      rw [Nat.testBit_or, Nat.zero_testBit, Bool.or_eq_false_iff] at hk <;>
      simp [hk]
  · rintro ⟨rfl, rfl⟩; rfl

theorem nat_or_bne_zero (a b : Nat) :
    ((a ||| b) != 0) = ((a != 0) || (b != 0)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, Bool.or_eq_true, ne_eq, nat_or_eq_zero_iff, not_and_or]

theorem bit_and_reqMask_foldl (rects : List (Nat × Nat)) (m0 m1 acc : Nat) :
    ((m1 &&& rects.foldl (fun a (ia, ib) => if ((m0 >>> ia) &&& 1 == 1) then a ||| (1 <<< ib) else a) acc) != 0) =
      ((m1 &&& acc != 0) || rects.any (fun (ia, ib) => ((m0 >>> ia) &&& 1 == 1) && ((m1 >>> ib) &&& 1 == 1))) := by
  induction rects generalizing acc with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨ia, ib⟩
    simp only [List.foldl_cons, List.any_cons]
    by_cases h : ((m0 >>> ia) &&& 1 == 1) = true
    · simp only [h, ite_true, Bool.true_and]
      rw [ih, Nat.and_or_distrib_left, nat_or_bne_zero, nat_and_one_shiftLeft_bne_zero,
          nat_shiftRight_and_one_eq_testBit]
      cases (m1 &&& acc != 0) <;> cases m1.testBit ib <;> simp
    · have hf : ((m0 >>> ia) &&& 1 == 1) = false := Bool.eq_false_iff.mpr h
      simp only [hf, Bool.false_eq_true, ite_false, Bool.false_and, Bool.false_or]
      exact ih acc

theorem testBit_maskOf_foldl (ts : List (Nat × Trie7 5)) (w : StrongPowV (ZMod 7) 5) (acc i : Nat) :
    (ts.foldl (fun a (j, t) => if t.inClosedNbr w then a ||| (1 <<< j) else a) acc).testBit i =
      (acc.testBit i || ts.any (fun (j, t) => (j == i) && t.inClosedNbr w)) := by
  induction ts generalizing acc with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨j, t⟩
    simp only [List.foldl_cons, List.any_cons]
    by_cases h : t.inClosedNbr w = true
    · simp only [h, ite_true, Bool.and_true]
      rw [ih, Nat.testBit_or, Nat.testBit_shiftLeft, nat_testBit_one]
      have hbit1 : (decide (i ≥ j) && decide (i - j = 0)) = (j == i) := by
        by_cases hji : j = i
        · subst hji; simp
        · have hne : (j == i) = false := beq_false_of_ne hji
          rw [hne]
          by_cases hle : j ≤ i
          · have hpos : i - j ≠ 0 := by omega
            simp [hpos]
          · simp [hle]
      rw [hbit1]
      cases acc.testBit i <;> cases (j == i) <;> simp
    · have hf : t.inClosedNbr w = false := Bool.eq_false_iff.mpr h
      simp only [hf, Bool.false_eq_true, ite_false, Bool.and_false, Bool.false_or]
      exact ih acc

theorem testBit_maskOf (w : StrongPowV (ZMod 7) 5) (i : Fin 20) :
    (maskOf w).testBit i.val = (rectAt i.val).inClosedNbr w := by
  dsimp only [maskOf]
  rw [testBit_maskOf_foldl, Nat.zero_testBit, Bool.false_or]
  fin_cases i <;> simp [rectTries, rectAt]

theorem keyOf_mod_four (w : StrongPowV (ZMod 7) 5) :
    keyOf w % 4 = sig5Bool w := by
  dsimp only [keyOf]
  have hlt : sig5Bool w < 4 := by
    dsimp [sig5Bool]; split_ifs <;> omega
  omega

theorem keyOf_div_four (w : StrongPowV (ZMod 7) 5) :
    keyOf w / 4 = maskOf w := by
  dsimp only [keyOf]
  have hlt : sig5Bool w < 4 := by
    dsimp [sig5Bool]; split_ifs <;> omega
  omega

theorem inRects_bound : ∀ p ∈ inRects, p.1 < 20 ∧ p.2 < 20 := by decide
theorem outRects_bound : ∀ p ∈ outRects, p.1 < 20 ∧ p.2 < 20 := by decide

def idx10OfKeys (kA kB : Nat) : Nat :=
  let sA := kA % 4; let mA := kA / 4
  let a0 := (sA >>> 1) &&& 1; let a1 := sA &&& 1
  let ro := reqMask outRects mA; let ri := reqMask inRects mA
  let sB := kB % 4; let mB := kB / 4
  let b0 := (sB >>> 1) &&& 1; let b1 := sB &&& 1
  let inX0 := (a0 &&& b0) ||| (a1 &&& b1)
  let inX1 := (a0 &&& b1) ||| (a1 &&& b0)
  let inJo := if (mB &&& ro) != 0 then 1 else 0
  let inJi := if (mB &&& ri) != 0 then 1 else 0
  (inX0 <<< 3) ||| (inX1 <<< 2) ||| (inJo <<< 1) ||| inJi

theorem idx10OfKeys_lt (kA kB : Nat) : idx10OfKeys kA kB < 16 := by
  dsimp [idx10OfKeys]
  have hlt16 : ∀ x0 x1 jo ji : Nat, x0 ≤ 1 → x1 ≤ 1 → jo ≤ 1 → ji ≤ 1 →
      (x0 <<< 3) ||| (x1 <<< 2) ||| (jo <<< 1) ||| ji < 16 := by
    intro x0 x1 jo ji hx0 hx1 hjo hji
    rcases (by omega : x0 = 0 ∨ x0 = 1) with rfl | rfl <;>
    rcases (by omega : x1 = 0 ∨ x1 = 1) with rfl | rfl <;>
    rcases (by omega : jo = 0 ∨ jo = 1) with rfl | rfl <;>
    rcases (by omega : ji = 0 ∨ ji = 1) with rfl | rfl <;> decide
  have hor1 : ∀ p q : Nat, p ≤ 1 → q ≤ 1 → (p ||| q) ≤ 1 := by
    intro p q hp hq
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;>
    rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> decide
  exact hlt16 _ _ _ _
    (hor1 _ _ (Nat.le_trans Nat.and_le_right Nat.and_le_right)
              (Nat.le_trans Nat.and_le_right Nat.and_le_right))
    (hor1 _ _ (Nat.le_trans Nat.and_le_right Nat.and_le_right)
              (Nat.le_trans Nat.and_le_right Nat.and_le_right))
    (by split_ifs <;> omega)
    (by split_ifs <;> omega)

theorem eval_dist10_16_row_go (kA cA : Nat) (hB : List (Nat × Nat)) (acc : Vec16) (g : Nat → Nat) :
    vec16Eval (dist10_16_row.go cA (((kA % 4) >>> 1) &&& 1) ((kA % 4) &&& 1)
      (reqMask outRects (kA / 4)) (reqMask inRects (kA / 4)) hB acc) g =
      vec16Eval acc g + (hB.map (fun (kB, cB) => (cA * cB) * g (idx10OfKeys kA kB))).sum := by
  induction hB generalizing acc with
  | nil => simp [dist10_16_row.go]
  | cons p rest ih =>
    rcases p with ⟨kB, cB⟩
    rw [dist10_16_row.go]
    rw [ih]
    have hlt := idx10OfKeys_lt kA kB
    change vec16Eval (acc.addAt (idx10OfKeys kA kB) (cA * cB)) g + _ = _
    rw [vec16Eval_addAt acc ⟨idx10OfKeys kA kB, hlt⟩ (cA * cB) g]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem eval_dist10_16_hist_go (hA hB : List (Nat × Nat)) (acc : Vec16) (g : Nat → Nat) :
    vec16Eval (dist10_16_hist.go hB hA acc) g =
      vec16Eval acc g +
        (hA.map (fun (kA, cA) => (hB.map (fun (kB, cB) => (cA * cB) * g (idx10OfKeys kA kB))).sum)).sum := by
  induction hA generalizing acc with
  | nil => simp [dist10_16_hist.go]
  | cons p rest ih =>
    rcases p with ⟨kA, cA⟩
    rw [dist10_16_hist.go]
    rw [ih, vec16Eval_add]
    have hrow : dist10_16_row kA cA hB = dist10_16_row.go cA (((kA % 4) >>> 1) &&& 1) ((kA % 4) &&& 1)
        (reqMask outRects (kA / 4)) (reqMask inRects (kA / 4)) hB {} := rfl
    rw [hrow, eval_dist10_16_row_go, vec16Eval_zero, zero_add]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem eval_dist10_16_hist (tA tB : Trie7 5) (g : Nat → Nat) :
    vec16Eval (dist10_16_hist (histOf tA) (histOf tB)) g =
      ∑ u ∈ tA.toFinset, ∑ v ∈ tB.toFinset, g (idx10OfKeys (keyOf u) (keyOf v)) := by
  change vec16Eval (dist10_16_hist.go (histOf tB) (histOf tA) {}) g = _
  rw [eval_dist10_16_hist_go, vec16Eval_zero, zero_add]
  have h1 : ∀ kA, (List.map (fun (kB, cB) => cB * g (idx10OfKeys kA kB)) (histOf tB)).sum =
      ∑ v ∈ tB.toFinset, g (idx10OfKeys kA (keyOf v)) :=
    fun kA => (sum_trie_eq_histEval keyOf tB (fun kB => g (idx10OfKeys kA kB))).symm
  have h2 : (List.map (fun (kA, cA) => (List.map (fun (kB, cB) => (cA * cB) * g (idx10OfKeys kA kB)) (histOf tB)).sum) (histOf tA)).sum =
      (List.map (fun (kA, cA) => cA * ∑ v ∈ tB.toFinset, g (idx10OfKeys kA (keyOf v))) (histOf tA)).sum := by
    congr 1; apply List.map_congr_left; intro ⟨kA, cA⟩ _
    have h1' := h1 kA
    dsimp only at h1' ⊢
    rw [← h1']
    have hmul : (List.map (fun x : ℕ × ℕ => cA * x.2 * g (idx10OfKeys kA x.1)) (histOf tB)) =
        List.map (fun x : ℕ × ℕ => cA * (x.2 * g (idx10OfKeys kA x.1))) (histOf tB) := by
      apply List.map_congr_left; intro ⟨kB, cB⟩ _; dsimp only; ring
    rw [hmul, List.sum_map_mul_left]
  rw [h2]
  exact (sum_trie_eq_histEval keyOf tA (fun kA => ∑ v ∈ tB.toFinset, g (idx10OfKeys kA (keyOf v)))).symm

-- Lift15, countAvoid15, countAvoid30 evaluation lemmas
def idx15OfBits (s10 s5 : Nat) : Nat :=
  let x0 := (s10 >>> 3) &&& 1; let x1 := (s10 >>> 2) &&& 1
  let jo := (s10 >>> 1) &&& 1; let ji := s10 &&& 1
  let w0 := (s5 >>> 2) &&& 1; let wh := (s5 >>> 1) &&& 1; let wv := s5 &&& 1
  let w1 := wh ||| wv
  let u0 := (x0 &&& w0) ||| (x1 &&& w1); let u1 := (x0 &&& w1) ||| (x1 &&& w0)
  let v0 := (x0 &&& w0) ||| (jo &&& wh) ||| (x1 &&& wv)
  let v1 := (x1 &&& w0) ||| (x0 &&& wv) ||| (ji &&& wh)
  (u0 <<< 3) ||| (u1 <<< 2) ||| (v0 <<< 1) ||| v1

theorem idx15OfBits_lt (s10 s5 : Nat) : idx15OfBits s10 s5 < 16 := by
  dsimp [idx15OfBits]
  have hlt16 : ∀ x0 x1 jo ji : Nat, x0 ≤ 1 → x1 ≤ 1 → jo ≤ 1 → ji ≤ 1 →
      (x0 <<< 3) ||| (x1 <<< 2) ||| (jo <<< 1) ||| ji < 16 := by
    intro x0 x1 jo ji hx0 hx1 hjo hji
    rcases (by omega : x0 = 0 ∨ x0 = 1) with rfl | rfl <;>
    rcases (by omega : x1 = 0 ∨ x1 = 1) with rfl | rfl <;>
    rcases (by omega : jo = 0 ∨ jo = 1) with rfl | rfl <;>
    rcases (by omega : ji = 0 ∨ ji = 1) with rfl | rfl <;> decide
  have hor1 : ∀ p q : Nat, p ≤ 1 → q ≤ 1 → (p ||| q) ≤ 1 := by
    intro p q hp hq
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;>
    rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> decide
  refine hlt16 _ _ _ _
    (hor1 _ _ (Nat.le_trans Nat.and_le_right Nat.and_le_right)
              (Nat.le_trans Nat.and_le_right (hor1 _ _ Nat.and_le_right Nat.and_le_right)))
    (hor1 _ _ (Nat.le_trans Nat.and_le_right (hor1 _ _ Nat.and_le_right Nat.and_le_right))
              (Nat.le_trans Nat.and_le_right Nat.and_le_right))
    (hor1 _ _ (hor1 _ _ (Nat.le_trans Nat.and_le_right Nat.and_le_right)
                        (Nat.le_trans Nat.and_le_right Nat.and_le_right))
              (Nat.le_trans Nat.and_le_right Nat.and_le_right))
    (hor1 _ _ (hor1 _ _ (Nat.le_trans Nat.and_le_right Nat.and_le_right)
                        (Nat.le_trans Nat.and_le_right Nat.and_le_right))
              (Nat.le_trans Nat.and_le_right Nat.and_le_right))

theorem list_sum_finRange_eq_univ {n : ℕ} (f : Fin n → ℕ) :
    (List.map f (List.finRange n)).sum = ∑ s : Fin n, f s := by
  rw [← Fin.sum_ofFn]
  congr 1
  rw [List.ofFn_eq_map]

theorem list_sum_finRange_eq_sum_range {n : ℕ} (f : ℕ → ℕ) :
    (List.map (fun s : Fin n => f s.val) (List.finRange n)).sum = ∑ i ∈ Finset.range n, f i := by
  rw [list_sum_finRange_eq_univ (fun s : Fin n => f s.val), Fin.sum_univ_eq_sum_range]

theorem vec16Eval_finRange8_foldl (s10 : Fin 16) (d16 d5t : Vec16)
    (l : List (Fin 8)) (acc : Vec16) (g : Nat → Nat) :
    vec16Eval (l.foldl (fun acc2 s5 =>
      let v5 := Vec16.get d5t s5.val
      if v5 == 0 then acc2 else
      Vec16.addAt acc2 (idx15OfBits s10.val s5.val) (Vec16.get d16 s10.val * v5)) acc) g =
      vec16Eval acc g + (l.map (fun s5 => (Vec16.get d16 s10.val * Vec16.get d5t s5.val) * g (idx15OfBits s10.val s5.val))).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons s5 rest ih =>
    dsimp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    by_cases hv : (Vec16.get d5t s5.val == 0) = true
    · have hv0 : Vec16.get d5t s5.val = 0 := by simpa using hv
      simp [hv0]
    · have hvf : (Vec16.get d5t s5.val == 0) = false := Bool.eq_false_iff.mpr hv
      simp only [hvf, Bool.false_eq_true, ite_false]
      rw [vec16Eval_addAt acc ⟨idx15OfBits s10.val s5.val, idx15OfBits_lt s10.val s5.val⟩ _ g]
      dsimp only
      omega

theorem eval_lift15 (d16 d5t : Vec16) (g : Nat → Nat) :
    vec16Eval (lift15 d16 d5t) g =
      vec16Eval d16 (fun s10 => ∑ s5 : Fin 8, Vec16.get d5t s5.val * g (idx15OfBits s10 s5.val)) := by
  have houter : ∀ (l : List (Fin 16)) (acc : Vec16),
      vec16Eval (l.foldl (fun acc s10 =>
        let v10 := Vec16.get d16 s10.val
        if v10 == 0 then acc else
        (List.finRange 8).foldl (fun acc2 s5 =>
          let v5 := Vec16.get d5t s5.val
          if v5 == 0 then acc2 else
          Vec16.addAt acc2 (idx15OfBits s10.val s5.val) (v10 * v5)) acc) acc) g =
      vec16Eval acc g + (l.map (fun s10 =>
        Vec16.get d16 s10.val * ∑ s5 : Fin 8, Vec16.get d5t s5.val * g (idx15OfBits s10.val s5.val))).sum := by
    intro l acc
    induction l generalizing acc with
    | nil => simp
    | cons s10 rest ih =>
      dsimp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      by_cases hv : (Vec16.get d16 s10.val == 0) = true
      · have hv0 : Vec16.get d16 s10.val = 0 := by simpa using hv
        simp [hv0]
      · have hvf : (Vec16.get d16 s10.val == 0) = false := Bool.eq_false_iff.mpr hv
        simp only [hvf, Bool.false_eq_true, ite_false]
        have hin := vec16Eval_finRange8_foldl s10 d16 d5t (List.finRange 8) acc g
        change vec16Eval ((List.finRange 8).foldl _ acc) g + _ = _
        rw [hin]
        have hsum8 : (List.map (fun s5 : Fin 8 => (Vec16.get d16 s10.val * Vec16.get d5t s5.val) *
            g (idx15OfBits s10.val s5.val)) (List.finRange 8)).sum =
            Vec16.get d16 s10.val * ∑ s5 : Fin 8, Vec16.get d5t s5.val * g (idx15OfBits s10.val s5.val) := by
          rw [list_sum_finRange_eq_univ, Finset.mul_sum]
          congr 1; ext s5; ring
        rw [hsum8]; omega
  have heq := houter (List.finRange 16) {}
  rw [vec16Eval_zero, zero_add] at heq
  have hdef : lift15 d16 d5t = (List.finRange 16).foldl (fun acc s10 =>
      let v10 := Vec16.get d16 s10.val
      if v10 == 0 then acc else
      (List.finRange 8).foldl (fun acc2 s5 =>
        let v5 := Vec16.get d5t s5.val
        if v5 == 0 then acc2 else
        Vec16.addAt acc2 (idx15OfBits s10.val s5.val) (v10 * v5)) acc) {} := rfl
  rw [hdef, heq, vec16Eval_eq_sum]
  exact list_sum_finRange_eq_sum_range (fun s10 => Vec16.get d16 s10 * ∑ s5 : Fin 8, Vec16.get d5t s5.val * g (idx15OfBits s10 s5.val))

theorem countAvoid15_inner (d16 d5t : Vec16) (s10 : Fin 16) (l : List (Fin 8)) (acc : Nat) :
    l.foldl (fun acc2 s5 =>
      let v5 := Vec16.get d5t s5.val
      let w0 := (s5.val >>> 2) &&& 1; let w1 := ((s5.val >>> 1) ||| s5.val) &&& 1
      if ((((s10.val >>> 3) &&& 1) &&& w0) ||| (((s10.val >>> 2) &&& 1) &&& w1)) == 0 then
        acc2 + Vec16.get d16 s10.val * v5
      else acc2) acc =
    acc + Vec16.get d16 s10.val * (l.map (fun s5 => Vec16.get d5t s5.val *
      (if (((((s10.val >>> 3) &&& 1) &&& ((s5.val >>> 2) &&& 1)) |||
            (((s10.val >>> 2) &&& 1) &&& (((s5.val >>> 1) ||| s5.val) &&& 1))) == 0) then 1 else 0))).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons s5 rest ih =>
    dsimp only [List.foldl_cons, List.map_cons, List.sum_cons]
    split_ifs <;> rw [ih] <;> ring

theorem countAvoid15_outer (d16 d5t : Vec16) (l : List (Fin 16)) (acc : Nat) :
    l.foldl (fun acc s10 =>
      (List.finRange 8).foldl (fun acc2 s5 =>
        let v5 := Vec16.get d5t s5.val
        let w0 := (s5.val >>> 2) &&& 1; let w1 := ((s5.val >>> 1) ||| s5.val) &&& 1
        if ((((s10.val >>> 3) &&& 1) &&& w0) ||| (((s10.val >>> 2) &&& 1) &&& w1)) == 0 then
          acc2 + Vec16.get d16 s10.val * v5
        else acc2) acc) acc =
    acc + (l.map (fun s10 => Vec16.get d16 s10.val * ∑ s5 : Fin 8, Vec16.get d5t s5.val *
      (if (((((s10.val >>> 3) &&& 1) &&& ((s5.val >>> 2) &&& 1)) |||
            (((s10.val >>> 2) &&& 1) &&& (((s5.val >>> 1) ||| s5.val) &&& 1))) == 0) then 1 else 0))).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons s10 rest ih =>
    dsimp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, countAvoid15_inner, list_sum_finRange_eq_univ, Nat.add_assoc]

theorem countAvoid15_eq (d16 d5t : Vec16) :
    countAvoid15 d16 d5t =
      vec16Eval d16 (fun s10 => ∑ s5 : Fin 8, Vec16.get d5t s5.val *
        (if (((((s10 >>> 3) &&& 1) &&& ((s5.val >>> 2) &&& 1)) |||
              (((s10 >>> 2) &&& 1) &&& (((s5.val >>> 1) ||| s5.val) &&& 1))) == 0) then 1 else 0)) := by
  have heq := countAvoid15_outer d16 d5t (List.finRange 16) 0
  rw [zero_add] at heq
  change countAvoid15 d16 d5t = _ at heq
  rw [heq, vec16Eval_eq_sum]
  exact list_sum_finRange_eq_sum_range (fun s10 => Vec16.get d16 s10 * ∑ s5 : Fin 8, Vec16.get d5t s5.val *
    (if (((((s10 >>> 3) &&& 1) &&& ((s5.val >>> 2) &&& 1)) |||
          (((s10 >>> 2) &&& 1) &&& (((s5.val >>> 1) ||| s5.val) &&& 1))) == 0) then 1 else 0))

theorem countAvoid30_aux (L4 R4 : Vec16) :
    ((List.finRange 4).foldl (fun acc u => (List.finRange 4).foldl (fun acc2 v =>
      if ((((u.val >>> 1) &&& 1) &&& ((v.val >>> 1) &&& 1)) ||| ((u.val &&& 1) &&& (v.val &&& 1))) == 0 then
        acc2 + Vec16.get L4 u.val * Vec16.get R4 v.val
      else acc2) acc) 0) =
      vec16Eval L4 (fun u => if u < 4 then vec16Eval R4 (fun v => if v < 4 then
        (if ((((u >>> 1) &&& 1) &&& ((v >>> 1) &&& 1)) ||| ((u &&& 1) &&& (v &&& 1))) == 0 then 1 else 0) else 0) else 0) := by
  have hsum4 : ∀ (u : Fin 4) (l : List (Fin 4)) (acc : Nat),
      l.foldl (fun acc2 v =>
        if ((((u.val >>> 1) &&& 1) &&& ((v.val >>> 1) &&& 1)) ||| ((u.val &&& 1) &&& (v.val &&& 1))) == 0 then
          acc2 + Vec16.get L4 u.val * Vec16.get R4 v.val
        else acc2) acc =
      acc + Vec16.get L4 u.val * (l.map (fun v => Vec16.get R4 v.val *
        (if ((((u.val >>> 1) &&& 1) &&& ((v.val >>> 1) &&& 1)) ||| ((u.val &&& 1) &&& (v.val &&& 1))) == 0 then 1 else 0))).sum := by
    intro u l acc
    induction l generalizing acc with
    | nil => simp
    | cons v rest ih =>
      dsimp only [List.foldl_cons, List.map_cons, List.sum_cons]
      split_ifs <;> rw [ih] <;> ring
  have houter4 : ∀ (l : List (Fin 4)) (acc : Nat),
      l.foldl (fun acc u => (List.finRange 4).foldl (fun acc2 v =>
        if ((((u.val >>> 1) &&& 1) &&& ((v.val >>> 1) &&& 1)) ||| ((u.val &&& 1) &&& (v.val &&& 1))) == 0 then
          acc2 + Vec16.get L4 u.val * Vec16.get R4 v.val
        else acc2) acc) acc =
      acc + (l.map (fun u => Vec16.get L4 u.val * ∑ v : Fin 4, Vec16.get R4 v.val *
        (if ((((u.val >>> 1) &&& 1) &&& ((v.val >>> 1) &&& 1)) ||| ((u.val &&& 1) &&& (v.val &&& 1))) == 0 then 1 else 0))).sum := by
    intro l acc
    induction l generalizing acc with
    | nil => simp
    | cons u rest ih =>
      dsimp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, hsum4, list_sum_finRange_eq_univ, Nat.add_assoc]
  have hfin4_sum : ∀ (V : Vec16) (f : Nat → Nat),
      (∑ u : Fin 4, Vec16.get V u.val * f u.val) = vec16Eval V (fun k => if k < 4 then f k else 0) := by
    intro V f
    rw [Fin.sum_univ_four]
    simp [vec16Eval, Vec16.get]
  rw [houter4, zero_add, list_sum_finRange_eq_univ]
  rw [hfin4_sum L4 (fun u => ∑ v : Fin 4, Vec16.get R4 v.val *
    if ((((u >>> 1) &&& 1) &&& ((v.val >>> 1) &&& 1)) ||| ((u &&& 1) &&& (v.val &&& 1))) == 0 then 1 else 0)]
  congr 1; ext u; split_ifs with hu
  · exact hfin4_sum R4 (fun v => if ((((u >>> 1) &&& 1) &&& ((v >>> 1) &&& 1)) ||| ((u &&& 1) &&& (v &&& 1))) == 0 then 1 else 0)
  · rfl

theorem countAvoid30_eq (dL dR : Vec16) :
    countAvoid30 dL dR =
      vec16Eval dL (fun sL => vec16Eval dR (fun sR =>
        if (((((sL >>> 3) &&& 1) &&& ((sR >>> 1) &&& 1)) |||
             (((sL >>> 2) &&& 1) &&& (sR &&& 1))) == 0) then 1 else 0)) := by
  have hprojL : ∀ (l : List (Fin 16)) (acc : Vec16) (g : Nat → Nat),
      vec16Eval (l.foldl (fun acc s => Vec16.addAt acc ((s.val >>> 2) &&& 3) (Vec16.get dL s.val)) acc) g =
      vec16Eval acc g + (l.map (fun s => Vec16.get dL s.val * g ((s.val >>> 2) &&& 3))).sum := by
    intro l acc g
    induction l generalizing acc with
    | nil => simp
    | cons s rest ih =>
      dsimp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      have hlt : (s.val >>> 2) &&& 3 < 16 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
      rw [vec16Eval_addAt acc ⟨(s.val >>> 2) &&& 3, hlt⟩ _ g]
      dsimp only; omega
  have hprojR : ∀ (l : List (Fin 16)) (acc : Vec16) (g : Nat → Nat),
      vec16Eval (l.foldl (fun acc s => Vec16.addAt acc (s.val &&& 3) (Vec16.get dR s.val)) acc) g =
      vec16Eval acc g + (l.map (fun s => Vec16.get dR s.val * g (s.val &&& 3))).sum := by
    intro l acc g
    induction l generalizing acc with
    | nil => simp
    | cons s rest ih =>
      dsimp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      have hlt : s.val &&& 3 < 16 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
      rw [vec16Eval_addAt acc ⟨s.val &&& 3, hlt⟩ _ g]
      dsimp only; omega
  have hL4 : ∀ g, vec16Eval ((List.finRange 16).foldl (fun acc s => Vec16.addAt acc ((s.val >>> 2) &&& 3) (Vec16.get dL s.val)) ({} : Vec16)) g =
      vec16Eval dL (fun sL => g ((sL >>> 2) &&& 3)) := by
    intro g; rw [hprojL, vec16Eval_zero, zero_add, vec16Eval_eq_sum]
    exact list_sum_finRange_eq_sum_range (fun sL => Vec16.get dL sL * g ((sL >>> 2) &&& 3))
  have hR4 : ∀ g, vec16Eval ((List.finRange 16).foldl (fun acc s => Vec16.addAt acc (s.val &&& 3) (Vec16.get dR s.val)) ({} : Vec16)) g =
      vec16Eval dR (fun sR => g (sR &&& 3)) := by
    intro g; rw [hprojR, vec16Eval_zero, zero_add, vec16Eval_eq_sum]
    exact list_sum_finRange_eq_sum_range (fun sR => Vec16.get dR sR * g (sR &&& 3))
  have htb30 : Nat.testBit 3 0 = true := by decide
  have htb31 : Nat.testBit 3 1 = true := by decide
  have hbitsL : ∀ sL : Nat, (((sL >>> 2) &&& 3) >>> 1) &&& 1 = (sL >>> 3) &&& 1 ∧
      ((sL >>> 2) &&& 3) &&& 1 = (sL >>> 2) &&& 1 := by
    intro sL
    constructor
    · apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_and, Nat.testBit_shiftRight, nat_testBit_one]
      by_cases hk : k = 0 <;> simp [hk, htb31]
    · apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_and, nat_testBit_one]
      by_cases hk : k = 0 <;> simp [hk, htb30]
  have hbitsR : ∀ sR : Nat, ((sR &&& 3) >>> 1) &&& 1 = (sR >>> 1) &&& 1 ∧
      (sR &&& 3) &&& 1 = sR &&& 1 := by
    intro sR
    constructor
    · apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_and, Nat.testBit_shiftRight, nat_testBit_one]
      by_cases hk : k = 0 <;> simp [hk, htb31]
    · apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_and, nat_testBit_one]
      by_cases hk : k = 0 <;> simp [hk, htb30]
  have hdef : countAvoid30 dL dR = ((List.finRange 4).foldl (fun acc u => (List.finRange 4).foldl (fun acc2 v =>
      if ((((u.val >>> 1) &&& 1) &&& ((v.val >>> 1) &&& 1)) ||| ((u.val &&& 1) &&& (v.val &&& 1))) == 0 then
        acc2 + Vec16.get ((List.finRange 16).foldl (fun acc s => Vec16.addAt acc ((s.val >>> 2) &&& 3) (Vec16.get dL s.val)) ({} : Vec16)) u.val *
               Vec16.get ((List.finRange 16).foldl (fun acc s => Vec16.addAt acc (s.val &&& 3) (Vec16.get dR s.val)) ({} : Vec16)) v.val
      else acc2) acc) 0) := rfl
  rw [hdef, countAvoid30_aux, hL4]
  congr 1; ext sL
  have hltL : (sL >>> 2) &&& 3 < 4 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [if_pos hltL, hR4]
  congr 1; ext sR
  have hltR : sR &&& 3 < 4 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [if_pos hltR, (hbitsL sL).1, (hbitsL sL).2, (hbitsR sR).1, (hbitsR sR).2]

end HistAndVec16Algebra

section S2aProdAndJ10

def s2aFam {V_L V_R : Type*} [DecidableEq V_L] [DecidableEq V_R]
    {G_L : SimpleGraph V_L} {G_R : SimpleGraph V_R}
    (R_L : Realisation Letter Letter.sep G_L)
    (R_R : Realisation Letter Letter.sep G_R) : Letter → Finset (V_L × V_R)
  | .B => (R_L.P .B ×ˢ R_R.P .B) ∪ (R_L.P .H ×ˢ R_R.P .D) ∪ (R_L.P .V ×ˢ R_R.P .A) ∪
          (R_L.P .D ×ˢ R_R.P .V) ∪ (R_L.P .A ×ˢ R_R.P .H)
  | .N => (R_L.P .N ×ˢ R_R.P .N) ∪ ((R_L.P .A ∪ R_L.P .D) ×ˢ (R_R.P .A ∪ R_R.P .D))
  | .A => (R_L.P .A ×ˢ R_R.P .N) ∪ (R_L.P .N ×ˢ R_R.P .D)
  | .D => (R_L.P .D ×ˢ R_R.P .N) ∪ (R_L.P .N ×ˢ R_R.P .A)
  | .O => (R_L.P .O ×ˢ R_R.P .N) ∪ (R_L.P .N ×ˢ R_R.P .O)
  | .H => (R_L.P .H ×ˢ R_R.P .N) ∪ (R_L.P .N ×ˢ R_R.P .V)
  | .V => (R_L.P .V ×ˢ R_R.P .N) ∪ (R_L.P .N ×ˢ R_R.P .H)

private theorem s2aFam_hindep {V_L V_R : Type*} [DecidableEq V_L] [DecidableEq V_R]
    {G_L : SimpleGraph V_L} {G_R : SimpleGraph V_R}
    (R_L : Realisation Letter Letter.sep G_L)
    (R_R : Realisation Letter Letter.sep G_R) (a : Letter) :
    (G_L ⊠ G_R).IsIndepSet (s2aFam R_L R_R a : Set (V_L × V_R)) := by
  have iL := R_L.hindep; have iR := R_R.hindep
  have sL := R_L.hsep; have sR := R_R.hsep
  have iLAD : G_L.IsIndepSet ((R_L.P .A ∪ R_L.P .D : Finset V_L) : Set V_L) :=
    isIndepSet_union_of_sep (iL .A) (iL .D) (sL .A .D rfl)
  have iRAD : G_R.IsIndepSet ((R_R.P .A ∪ R_R.P .D : Finset V_R) : Set V_R) :=
    isIndepSet_union_of_sep (iR .A) (iR .D) (sR .A .D rfl)
  cases a
  · refine isIndepSet_union_of_sep (isIndepSet_union_of_sep (isIndepSet_union_of_sep
      (isIndepSet_union_of_sep (isIndepSet_strongProd (iL .B) (iR .B))
        (isIndepSet_strongProd (iL .H) (iR .D)) (sep_prod_left (sL .B .H rfl)))
      (isIndepSet_strongProd (iL .V) (iR .A))
      (Sep.union_left (sep_prod_left (sL .B .V rfl)) (sep_prod_right (sR .D .A rfl))))
      (isIndepSet_strongProd (iL .D) (iR .V))
      (Sep.union_left (Sep.union_left (sep_prod_right (sR .B .V rfl)) (sep_prod_right (sR .D .V rfl)))
        (sep_prod_left (sL .V .D rfl))))
      (isIndepSet_strongProd (iL .A) (iR .H))
      (Sep.union_left (Sep.union_left (Sep.union_left (sep_prod_right (sR .B .H rfl))
        (sep_prod_left (sL .H .A rfl))) (sep_prod_right (sR .A .H rfl))) (sep_prod_left (sL .D .A rfl)))
  · exact isIndepSet_union_of_sep (isIndepSet_strongProd (iL .N) (iR .N))
      (isIndepSet_strongProd iLAD iRAD)
      (sep_prod_left (Sep.union_right (sL .N .A rfl) (sL .N .D rfl)))
  · exact isIndepSet_union_of_sep (isIndepSet_strongProd (iL .A) (iR .N))
      (isIndepSet_strongProd (iL .N) (iR .D)) (sep_prod_left (sL .A .N rfl))
  · exact isIndepSet_union_of_sep (isIndepSet_strongProd (iL .D) (iR .N))
      (isIndepSet_strongProd (iL .N) (iR .A)) (sep_prod_left (sL .D .N rfl))
  · exact isIndepSet_union_of_sep (isIndepSet_strongProd (iL .O) (iR .N))
      (isIndepSet_strongProd (iL .N) (iR .O)) (sep_prod_left (sL .O .N rfl))
  · exact isIndepSet_union_of_sep (isIndepSet_strongProd (iL .H) (iR .N))
      (isIndepSet_strongProd (iL .N) (iR .V)) (sep_prod_left (sL .H .N rfl))
  · exact isIndepSet_union_of_sep (isIndepSet_strongProd (iL .V) (iR .N))
      (isIndepSet_strongProd (iL .N) (iR .H)) (sep_prod_left (sL .V .N rfl))

private theorem s2aFam_hsep {V_L V_R : Type*} [DecidableEq V_L] [DecidableEq V_R]
    {G_L : SimpleGraph V_L} {G_R : SimpleGraph V_R}
    (R_L : Realisation Letter Letter.sep G_L)
    (R_R : Realisation Letter Letter.sep G_R) (a b : Letter) (hab : Letter.sep a b = true) :
    Sep (G_L ⊠ G_R) (s2aFam R_L R_R a) (s2aFam R_L R_R b) := by
  have sL := R_L.hsep; have sR := R_R.hsep
  have sLNAD : Sep G_L (R_L.P .N) (R_L.P .A ∪ R_L.P .D) := Sep.union_right (sL .N .A rfl) (sL .N .D rfl)
  have sRNAD : Sep G_R (R_R.P .N) (R_R.P .A ∪ R_R.P .D) := Sep.union_right (sR .N .A rfl) (sR .N .D rfl)
  have sLAD_N : Sep G_L (R_L.P .A ∪ R_L.P .D) (R_L.P .N) := sLNAD.symm
  have sRAD_N : Sep G_R (R_R.P .A ∪ R_R.P .D) (R_R.P .N) := sRNAD.symm
  cases a <;> cases b <;> simp only [Letter.sep, reduceCtorEq] at hab
  all_goals dsimp only [s2aFam]
  · -- B, O
    exact Sep.union_right
      (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
        (sep_prod_left (sL .B .O rfl)) (sep_prod_right (sR .D .N rfl)))
        (sep_prod_right (sR .A .N rfl))) (sep_prod_right (sR .V .N rfl))) (sep_prod_right (sR .H .N rfl)))
      (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
        (sep_prod_right (sR .B .O rfl)) (sep_prod_left (sL .H .N rfl)))
        (sep_prod_left (sL .V .N rfl))) (sep_prod_left (sL .D .N rfl))) (sep_prod_left (sL .A .N rfl)))
  · -- B, H
    exact Sep.union_right
      (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
        (sep_prod_left (sL .B .H rfl)) (sep_prod_right (sR .D .N rfl)))
        (sep_prod_right (sR .A .N rfl))) (sep_prod_right (sR .V .N rfl))) (sep_prod_right (sR .H .N rfl)))
      (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
        (sep_prod_right (sR .B .V rfl)) (sep_prod_left (sL .H .N rfl)))
        (sep_prod_left (sL .V .N rfl))) (sep_prod_left (sL .D .N rfl))) (sep_prod_left (sL .A .N rfl)))
  · -- B, V
    exact Sep.union_right
      (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
        (sep_prod_left (sL .B .V rfl)) (sep_prod_right (sR .D .N rfl)))
        (sep_prod_right (sR .A .N rfl))) (sep_prod_right (sR .V .N rfl))) (sep_prod_right (sR .H .N rfl)))
      (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
        (sep_prod_right (sR .B .H rfl)) (sep_prod_left (sL .H .N rfl)))
        (sep_prod_left (sL .V .N rfl))) (sep_prod_left (sL .D .N rfl))) (sep_prod_left (sL .A .N rfl)))
  · -- N, A
    exact Sep.union_right
      (Sep.union_left (sep_prod_left (sL .N .A rfl)) (sep_prod_right sRAD_N))
      (Sep.union_left (sep_prod_right (sR .N .D rfl)) (sep_prod_left sLAD_N))
  · -- N, D
    exact Sep.union_right
      (Sep.union_left (sep_prod_left (sL .N .D rfl)) (sep_prod_right sRAD_N))
      (Sep.union_left (sep_prod_right (sR .N .A rfl)) (sep_prod_left sLAD_N))
  · -- N, O
    exact Sep.union_right
      (Sep.union_left (sep_prod_left (sL .N .O rfl)) (sep_prod_right sRAD_N))
      (Sep.union_left (sep_prod_right (sR .N .O rfl)) (sep_prod_left sLAD_N))
  · -- N, H
    exact Sep.union_right
      (Sep.union_left (sep_prod_left (sL .N .H rfl)) (sep_prod_right sRAD_N))
      (Sep.union_left (sep_prod_right (sR .N .V rfl)) (sep_prod_left sLAD_N))
  · -- N, V
    exact Sep.union_right
      (Sep.union_left (sep_prod_left (sL .N .V rfl)) (sep_prod_right sRAD_N))
      (Sep.union_left (sep_prod_right (sR .N .H rfl)) (sep_prod_left sLAD_N))
  · -- A, N
    exact (Sep.union_right
      (Sep.union_left (sep_prod_left (sL .N .A rfl)) (sep_prod_right sRAD_N))
      (Sep.union_left (sep_prod_right (sR .N .D rfl)) (sep_prod_left sLAD_N))).symm
  · -- A, D
    exact Sep.union_right
      (Sep.union_left (sep_prod_left (sL .A .D rfl)) (sep_prod_right (sR .D .N rfl)))
      (Sep.union_left (sep_prod_left (sL .A .N rfl)) (sep_prod_right (sR .D .A rfl)))
  · -- A, H
    exact Sep.union_right
      (Sep.union_left (sep_prod_left (sL .A .H rfl)) (sep_prod_right (sR .D .N rfl)))
      (Sep.union_left (sep_prod_right (sR .N .V rfl)) (sep_prod_right (sR .D .V rfl)))
  · -- D, N
    exact (Sep.union_right
      (Sep.union_left (sep_prod_left (sL .N .D rfl)) (sep_prod_right sRAD_N))
      (Sep.union_left (sep_prod_right (sR .N .A rfl)) (sep_prod_left sLAD_N))).symm
  · -- D, A
    exact (Sep.union_right
      (Sep.union_left (sep_prod_left (sL .A .D rfl)) (sep_prod_right (sR .D .N rfl)))
      (Sep.union_left (sep_prod_left (sL .A .N rfl)) (sep_prod_right (sR .D .A rfl)))).symm
  · -- D, V
    exact Sep.union_right
      (Sep.union_left (sep_prod_left (sL .D .V rfl)) (sep_prod_right (sR .A .N rfl)))
      (Sep.union_left (sep_prod_right (sR .N .H rfl)) (sep_prod_right (sR .A .H rfl)))
  · -- O, B
    exact (Sep.union_right
      (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
        (sep_prod_left (sL .B .O rfl)) (sep_prod_right (sR .D .N rfl)))
        (sep_prod_right (sR .A .N rfl))) (sep_prod_right (sR .V .N rfl))) (sep_prod_right (sR .H .N rfl)))
      (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
        (sep_prod_right (sR .B .O rfl)) (sep_prod_left (sL .H .N rfl)))
        (sep_prod_left (sL .V .N rfl))) (sep_prod_left (sL .D .N rfl))) (sep_prod_left (sL .A .N rfl)))).symm
  · -- O, N
    exact (Sep.union_right
      (Sep.union_left (sep_prod_left (sL .N .O rfl)) (sep_prod_right sRAD_N))
      (Sep.union_left (sep_prod_right (sR .N .O rfl)) (sep_prod_left sLAD_N))).symm
  · -- H, B
    exact (Sep.union_right
      (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
        (sep_prod_left (sL .B .H rfl)) (sep_prod_right (sR .D .N rfl)))
        (sep_prod_right (sR .A .N rfl))) (sep_prod_right (sR .V .N rfl))) (sep_prod_right (sR .H .N rfl)))
      (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
        (sep_prod_right (sR .B .V rfl)) (sep_prod_left (sL .H .N rfl)))
        (sep_prod_left (sL .V .N rfl))) (sep_prod_left (sL .D .N rfl))) (sep_prod_left (sL .A .N rfl)))).symm
  · -- H, N
    exact (Sep.union_right
      (Sep.union_left (sep_prod_left (sL .N .H rfl)) (sep_prod_right sRAD_N))
      (Sep.union_left (sep_prod_right (sR .N .V rfl)) (sep_prod_left sLAD_N))).symm
  · -- H, A
    exact (Sep.union_right
      (Sep.union_left (sep_prod_left (sL .A .H rfl)) (sep_prod_right (sR .D .N rfl)))
      (Sep.union_left (sep_prod_right (sR .N .V rfl)) (sep_prod_right (sR .D .V rfl)))).symm
  · -- V, B
    exact (Sep.union_right
      (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
        (sep_prod_left (sL .B .V rfl)) (sep_prod_right (sR .D .N rfl)))
        (sep_prod_right (sR .A .N rfl))) (sep_prod_right (sR .V .N rfl))) (sep_prod_right (sR .H .N rfl)))
      (Sep.union_left (Sep.union_left (Sep.union_left (Sep.union_left
        (sep_prod_right (sR .B .H rfl)) (sep_prod_left (sL .H .N rfl)))
        (sep_prod_left (sL .V .N rfl))) (sep_prod_left (sL .D .N rfl))) (sep_prod_left (sL .A .N rfl)))).symm
  · -- V, N
    exact (Sep.union_right
      (Sep.union_left (sep_prod_left (sL .N .V rfl)) (sep_prod_right sRAD_N))
      (Sep.union_left (sep_prod_right (sR .N .H rfl)) (sep_prod_left sLAD_N))).symm
  · -- V, D
    exact (Sep.union_right
      (Sep.union_left (sep_prod_left (sL .D .V rfl)) (sep_prod_right (sR .A .N rfl)))
      (Sep.union_left (sep_prod_right (sR .N .H rfl)) (sep_prod_right (sR .A .H rfl)))).symm

def s2aProd {V : Type*} [DecidableEq V] {G : SimpleGraph V} {dL dR : ℕ}
    (R_L : Realisation Letter Letter.sep (strongPowPi G dL))
    (R_R : Realisation Letter Letter.sep (strongPowPi G dR)) :
    Realisation Letter Letter.sep (strongPowPi G (dL + dR)) :=
  ({ P := s2aFam R_L R_R
     hindep := s2aFam_hindep R_L R_R
     hsep := s2aFam_hsep R_L R_R } : Realisation Letter Letter.sep (strongPowPi G dL ⊠ strongPowPi G dR)).mapIso
    (strongProdIsoAdd G dL dR)

theorem w_s2aProd {V : Type*} [DecidableEq V] {G : SimpleGraph V} {dL dR : ℕ}
    (R_L : Realisation Letter Letter.sep (strongPowPi G dL))
    (R_R : Realisation Letter Letter.sep (strongPowPi G dR)) :
    (s2aProd R_L R_R).w .B =
      R_L.w .B * R_R.w .B + R_L.w .H * R_R.w .D + R_L.w .V * R_R.w .A +
        R_L.w .D * R_R.w .V + R_L.w .A * R_R.w .H ∧
    (s2aProd R_L R_R).w .N =
      R_L.w .N * R_R.w .N + (R_L.w .A + R_L.w .D) * (R_R.w .A + R_R.w .D) ∧
    (s2aProd R_L R_R).w .A = R_L.w .A * R_R.w .N + R_L.w .N * R_R.w .D ∧
    (s2aProd R_L R_R).w .D = R_L.w .D * R_R.w .N + R_L.w .N * R_R.w .A ∧
    (s2aProd R_L R_R).w .O = R_L.w .O * R_R.w .N + R_L.w .N * R_R.w .O ∧
    (s2aProd R_L R_R).w .H = R_L.w .H * R_R.w .N + R_L.w .N * R_R.w .V ∧
    (s2aProd R_L R_R).w .V = R_L.w .V * R_R.w .N + R_L.w .N * R_R.w .H := by
  have sL := R_L.hsep; have sR := R_R.hsep
  have dprod : ∀ {P Q : Finset ((Fin dL → V) × (Fin dR → V))},
      Sep (strongPowPi G dL ⊠ strongPowPi G dR) P Q → Disjoint P Q := fun h => h.disjoint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [s2aProd, Realisation.w_mapIso] <;> dsimp only [Realisation.w, s2aFam]
  · have h12 : Disjoint (R_L.P .B ×ˢ R_R.P .B) (R_L.P .H ×ˢ R_R.P .D) := dprod (sep_prod_left (sL .B .H rfl))
    have h123 : Disjoint ((R_L.P .B ×ˢ R_R.P .B) ∪ (R_L.P .H ×ˢ R_R.P .D)) (R_L.P .V ×ˢ R_R.P .A) :=
      dprod (Sep.union_left (sep_prod_left (sL .B .V rfl)) (sep_prod_right (sR .D .A rfl)))
    have h1234 : Disjoint (((R_L.P .B ×ˢ R_R.P .B) ∪ (R_L.P .H ×ˢ R_R.P .D)) ∪ (R_L.P .V ×ˢ R_R.P .A))
        (R_L.P .D ×ˢ R_R.P .V) :=
      dprod (Sep.union_left (Sep.union_left (sep_prod_right (sR .B .V rfl)) (sep_prod_right (sR .D .V rfl)))
        (sep_prod_left (sL .V .D rfl)))
    have h12345 : Disjoint ((((R_L.P .B ×ˢ R_R.P .B) ∪ (R_L.P .H ×ˢ R_R.P .D)) ∪
        (R_L.P .V ×ˢ R_R.P .A)) ∪ (R_L.P .D ×ˢ R_R.P .V)) (R_L.P .A ×ˢ R_R.P .H) :=
      dprod (Sep.union_left (Sep.union_left (Sep.union_left (sep_prod_right (sR .B .H rfl))
        (sep_prod_left (sL .H .A rfl))) (sep_prod_right (sR .A .H rfl))) (sep_prod_left (sL .D .A rfl)))
    rw [Finset.card_union_of_disjoint h12345, Finset.card_union_of_disjoint h1234,
        Finset.card_union_of_disjoint h123, Finset.card_union_of_disjoint h12]
    simp [Finset.card_product]
  · have h12 : Disjoint (R_L.P .N ×ˢ R_R.P .N) ((R_L.P .A ∪ R_L.P .D) ×ˢ (R_R.P .A ∪ R_R.P .D)) :=
      dprod (sep_prod_left (Sep.union_right (sL .N .A rfl) (sL .N .D rfl)))
    rw [Finset.card_union_of_disjoint h12, Finset.card_product, Finset.card_product,
        Finset.card_union_of_disjoint (sL .A .D rfl).disjoint,
        Finset.card_union_of_disjoint (sR .A .D rfl).disjoint]
  · rw [Finset.card_union_of_disjoint (dprod (sep_prod_left (sL .A .N rfl)))]; simp [Finset.card_product]
  · rw [Finset.card_union_of_disjoint (dprod (sep_prod_left (sL .D .N rfl)))]; simp [Finset.card_product]
  · rw [Finset.card_union_of_disjoint (dprod (sep_prod_left (sL .O .N rfl)))]; simp [Finset.card_product]
  · rw [Finset.card_union_of_disjoint (dprod (sep_prod_left (sL .H .N rfl)))]; simp [Finset.card_product]
  · rw [Finset.card_union_of_disjoint (dprod (sep_prod_left (sL .V .N rfl)))]; simp [Finset.card_product]

-- Concrete 10D Realisations & J10^+
@[irreducible] def R10 : Realisation Letter Letter.sep (strongPowPi C7 10) := s2aProd baseR5 baseR5
@[irreducible] def R10A : Realisation Letter Letter.sep (strongPowPi C7 10) := s2aProd baseR5.sigma baseR5

theorem R10_def : R10 = s2aProd baseR5 baseR5 := by unfold R10; rfl
theorem R10A_def : R10A = s2aProd baseR5.sigma baseR5 := by unfold R10A; rfl

theorem R10_w :
    R10.w .B = 129601 ∧ R10.w .N = 105709 ∧ R10.w .A = 14490 ∧ R10.w .D = 14490 ∧
    R10.w .O = 5152 ∧ R10.w .H = 5152 ∧ R10.w .V = 5152 := by
  rw [R10_def]
  have hw := w_s2aProd baseR5 baseR5
  rcases baseR5_w with ⟨hB, hN, hA, hD, hO, hH, hV⟩
  rw [hB, hN, hA, hD, hO, hH, hV] at hw
  exact hw

theorem R10A_w :
    R10A.w .B = 129601 ∧ R10A.w .N = 105709 ∧ R10A.w .A = 16744 ∧ R10A.w .D = 12236 ∧
    R10A.w .O = 5152 ∧ R10A.w .H = 5152 ∧ R10A.w .V = 5152 := by
  rw [R10A_def]
  have hw := w_s2aProd baseR5.sigma baseR5
  rcases baseR5_w with ⟨hB, hN, hA, hD, hO, hH, hV⟩
  have sB : baseR5.sigma.w .B = 359 := by rw [Realisation.w_sigma]; exact hB
  have sN : baseR5.sigma.w .N = 322 := by rw [Realisation.w_sigma]; exact hN
  have sA : baseR5.sigma.w .A = 26 := by rw [Realisation.w_sigma]; exact hD
  have sD : baseR5.sigma.w .D = 19 := by rw [Realisation.w_sigma]; exact hA
  have sO : baseR5.sigma.w .O = 8 := by rw [Realisation.w_sigma]; exact hO
  have sH : baseR5.sigma.w .H = 8 := by rw [Realisation.w_sigma]; exact hV
  have sV : baseR5.sigma.w .V = 8 := by rw [Realisation.w_sigma]; exact hH
  rw [sB, sN, sA, sD, sO, sH, sV, hB, hN, hA, hD, hO, hH, hV] at hw
  exact hw

theorem piSet5_X15_eq : piSet5 tX15 = piSet5 tXV5 ∪ piSet5 tXH5 := by
  have hsub : piSet5 tXV5 ∪ piSet5 tXH5 ⊆ piSet5 tX15 := by
    rw [piSet5_def, piSet5_def, piSet5_def]
    apply Finset.union_subset
    · exact Finset.map_subset_map.mpr (Trie7.toFinset_subset_of_isSubset tXV5_sub_X15)
    · exact Finset.map_subset_map.mpr (Trie7.toFinset_subset_of_isSubset tXH5_sub_X15)
  have hdisj : Disjoint (piSet5 tXV5) (piSet5 tXH5) := by
    rw [piSet5_def, piSet5_def, Finset.disjoint_map]
    exact (sep_of_trieDisjoint tXH5_disj_XV5).symm.disjoint
  apply (Finset.eq_of_subset_of_card_le hsub _).symm
  rw [Finset.card_union_of_disjoint hdisj, piSet5_card, piSet5_card, piSet5_card,
      tXV5_card, tXH5_card, tX15_card]

theorem R10_P_map_prodSet {dL dR : ℕ} (R_L : Realisation Letter Letter.sep (strongPowPi C7 dL))
    (R_R : Realisation Letter Letter.sep (strongPowPi C7 dR)) :
    (s2aProd R_L R_R).P .N = prodSet (R_L.P .N) (R_R.P .N) ∪ prodSet (R_L.P .A ∪ R_L.P .D) (R_R.P .A ∪ R_R.P .D) ∧
    (s2aProd R_L R_R).P .A = prodSet (R_L.P .A) (R_R.P .N) ∪ prodSet (R_L.P .N) (R_R.P .D) ∧
    (s2aProd R_L R_R).P .D = prodSet (R_L.P .D) (R_R.P .N) ∪ prodSet (R_L.P .N) (R_R.P .A) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [s2aProd, Realisation.mapIso, s2aFam, Finset.map_union, prodSet_def]

theorem sigma_P_eq {V : Type*} {G : SimpleGraph V}
    (R : Realisation Letter Letter.sep G) (a : Letter) :
    R.sigma.P a = R.P (Letter.sigma.symm a) := rfl

theorem R10A_N_eq_R10_N : R10A.P .N = R10.P .N := by
  rw [R10A_def, R10_def, (R10_P_map_prodSet baseR5.sigma baseR5).1, (R10_P_map_prodSet baseR5 baseR5).1]
  have hsigN : baseR5.sigma.P .N = baseR5.P .N := sigma_P_eq baseR5 .N
  have hsigAD : baseR5.sigma.P .A ∪ baseR5.sigma.P .D = baseR5.P .A ∪ baseR5.P .D := by
    rw [sigma_P_eq, sigma_P_eq]; exact Finset.union_comm _ _
  rw [hsigN, hsigAD]

theorem prodSet_union_left {dL dR : ℕ} (A₁ A₂ : Finset (Fin dL → ZMod 7))
    (B : Finset (Fin dR → ZMod 7)) :
    prodSet (A₁ ∪ A₂) B = prodSet A₁ B ∪ prodSet A₂ B := by
  simp only [prodSet_def, Finset.union_product, Finset.map_union]

theorem prodSet_union_right {dL dR : ℕ} (A : Finset (Fin dL → ZMod 7))
    (B₁ B₂ : Finset (Fin dR → ZMod 7)) :
    prodSet A (B₁ ∪ B₂) = prodSet A B₁ ∪ prodSet A B₂ := by
  simp only [prodSet_def, Finset.product_union, Finset.map_union]

theorem R10_AD_eq : R10.P .A ∪ R10.P .D =
    prodSet (piSet5 tX15) (piSet5 tX05) ∪ prodSet (piSet5 tX05) (piSet5 tX15) := by
  rw [R10_def, (R10_P_map_prodSet baseR5 baseR5).2.1, (R10_P_map_prodSet baseR5 baseR5).2.2,
      baseR5_P_eq.2.1, baseR5_P_eq.2.2.1, baseR5_P_eq.2.2.2.1,
      piSet5_X15_eq, prodSet_union_left, prodSet_union_right]
  ac_rfl

theorem R10A_AD_eq : R10A.P .A ∪ R10A.P .D = R10.P .A ∪ R10.P .D := by
  rw [R10A_def, (R10_P_map_prodSet baseR5.sigma baseR5).2.1, (R10_P_map_prodSet baseR5.sigma baseR5).2.2,
      R10_def, (R10_P_map_prodSet baseR5 baseR5).2.1, (R10_P_map_prodSet baseR5 baseR5).2.2]
  have hsigN : baseR5.sigma.P .N = baseR5.P .N := sigma_P_eq baseR5 .N
  have hsigA : baseR5.sigma.P .A = baseR5.P .D := sigma_P_eq baseR5 .A
  have hsigD : baseR5.sigma.P .D = baseR5.P .A := sigma_P_eq baseR5 .D
  rw [hsigN, hsigA, hsigD]
  ac_rfl

def rectPi10 (ia ib : Nat) : Finset (Fin 10 → ZMod 7) :=
  prodSet (piSet5 (rectAt ia)) (piSet5 (rectAt ib))

def J10_out : Finset (Fin 10 → ZMod 7) :=
  outRects.toFinset.biUnion (fun p => rectPi10 p.1 p.2)

def J10_in : Finset (Fin 10 → ZMod 7) :=
  inRects.toFinset.biUnion (fun p => rectPi10 p.1 p.2)

def X0_10 : Finset (Fin 10 → ZMod 7) :=
  prodSet (piSet5 tX05) (piSet5 tX05) ∪ prodSet (piSet5 tX15) (piSet5 tX15)

def X1_10 : Finset (Fin 10 → ZMod 7) :=
  prodSet (piSet5 tX05) (piSet5 tX15) ∪ prodSet (piSet5 tX15) (piSet5 tX05)

theorem R10_N_eq_X0_10 : R10.P .N = X0_10 := by
  rw [R10_def, (R10_P_map_prodSet baseR5 baseR5).1, baseR5_P_eq.2.1,
      baseR5_P_eq.2.2.1, baseR5_P_eq.2.2.2.1, ← piSet5_X15_eq]
  rfl

theorem R10_AD_eq_X1_10 : R10.P .A ∪ R10.P .D = X1_10 := R10_AD_eq.trans (Finset.union_comm _ _)

theorem rectPi10_disjoint {a₁ b₁ a₂ b₂ : Nat} (h : rectsDisj1 a₁ b₁ a₂ b₂ = true) :
    Disjoint (rectPi10 a₁ b₁) (rectPi10 a₂ b₂) := by
  dsimp only [rectsDisj1] at h
  rw [Bool.or_eq_true] at h
  apply prodSet_disjoint (dL := 5) (dR := 5)
  rcases h with ha | hb
  · left; rw [piSet5_def, piSet5_def, Finset.disjoint_map]; exact (sep_of_trieDisjoint ha).disjoint
  · right; rw [piSet5_def, piSet5_def, Finset.disjoint_map]; exact (sep_of_trieDisjoint hb).disjoint

theorem rectPi10_sep {a₁ b₁ a₂ b₂ : Nat} (h : rectsDisj1 a₁ b₁ a₂ b₂ = true) :
    Sep (strongPowPi C7 10) (rectPi10 a₁ b₁) (rectPi10 a₂ b₂) := by
  dsimp only [rectsDisj1] at h
  rw [Bool.or_eq_true] at h
  apply prodSet_sep (dL := 5) (dR := 5)
  rcases h with ha | hb
  · left; intro x hx y hy
    rw [piSet5_def] at hx hy; rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
    rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
    intro hc
    apply sep_of_trieDisjoint ha x' hx' y' hy'
    rcases hc with heq | hadj
    · left; exact (strongPowEquivPi C7 5).injective heq
    · right; exact ((strongPowEquivPi C7 5).map_rel_iff).mp hadj
  · right; intro x hx y hy
    rw [piSet5_def] at hx hy; rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
    rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
    intro hc
    apply sep_of_trieDisjoint hb x' hx' y' hy'
    rcases hc with heq | hadj
    · left; exact (strongPowEquivPi C7 5).injective heq
    · right; exact ((strongPowEquivPi C7 5).map_rel_iff).mp hadj

theorem card_biUnion_rectPi10 : ∀ (l : List (Nat × Nat)),
    rectListPairwiseDisj l = true →
    (l.toFinset.biUnion (fun p => rectPi10 p.1 p.2)).card =
      (l.map (fun p => (rectAt p.1).card * (rectAt p.2).card)).sum
  | [], _ => by simp
  | (a, b) :: rest, h => by
    simp only [rectListPairwiseDisj, Bool.and_eq_true, List.all_eq_true] at h
    have ih := card_biUnion_rectPi10 rest h.2
    rw [List.toFinset_cons, Finset.biUnion_insert, Finset.card_union_of_disjoint,
        ih, List.map_cons, List.sum_cons, rectPi10, prodSet_card, piSet5_card, piSet5_card]
    rw [Finset.disjoint_biUnion_right]
    intro ⟨a', b'⟩ hm
    exact rectPi10_disjoint (h.1 (a', b') (List.mem_toFinset.mp hm))

theorem J10_out_card : J10_out.card = 27488 :=
  (card_biUnion_rectPi10 outRects outRects_disj).trans outRects_card_sum

theorem J10_in_card : J10_in.card = 107265 :=
  (card_biUnion_rectPi10 inRects inRects_disj).trans inRects_card_sum

theorem J10_out_sep_in : Sep (strongPowPi C7 10) J10_out J10_in := by
  intro x hx y hy
  rw [J10_out, Finset.mem_biUnion] at hx
  rw [J10_in, Finset.mem_biUnion] at hy
  simp only [List.mem_toFinset] at hx hy
  rcases hx with ⟨⟨a₁, b₁⟩, h₁, hx₁⟩
  rcases hy with ⟨⟨a₂, b₂⟩, h₂, hy₂⟩
  have hcd := List.all_eq_true.mp (List.all_eq_true.mp out_in_cross_disj (a₁, b₁) h₁) (a₂, b₂) h₂
  exact rectPi10_sep hcd x hx₁ y hy₂

theorem J10_out_sep_R10N : Sep (strongPowPi C7 10) J10_out (R10.P .N) := by
  rw [R10_N_eq_X0_10, sep_iff_not_inNbr]
  intro z hz
  rw [J10_out, Finset.mem_biUnion] at hz
  rcases hz with ⟨⟨a, b⟩, hab, hz⟩
  rw [List.mem_toFinset] at hab
  change z ∈ rectPi10 a b at hz
  rw [rectPi10, prodSet_def] at hz
  rcases Finset.mem_map.mp hz with ⟨⟨x, y⟩, hxy, rfl⟩
  rw [Finset.mem_product, piSet5_def, piSet5_def] at hxy
  rcases Finset.mem_map.mp hxy.1 with ⟨u, hu, rfl⟩
  rcases Finset.mem_map.mp hxy.2 with ⟨v, hv, rfl⟩
  rw [X0_10, inNbr_union]
  simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv]
  rw [inNbr_prodSet (dL := 5) (dR := 5), inNbr_prodSet (dL := 5) (dR := 5), inNbr_piSet5, inNbr_piSet5, inNbr_piSet5, inNbr_piSet5]
  have hav := List.all_eq_true.mp outRects_avoid_R10N (a, b) hab
  dsimp only [outRectPairAvoids] at hav
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hav
  rintro (⟨h0u, h0v⟩ | ⟨h1u, h1v⟩)
  · rcases hav.1 with ha0 | hb0
    · exact absurd ((trieAny_eq_true _ _).mpr ⟨u, hu, h0u⟩) (by simp [ha0])
    · exact absurd ((trieAny_eq_true _ _).mpr ⟨v, hv, h0v⟩) (by simp [hb0])
  · rcases hav.2 with ha1 | hb1
    · exact absurd ((trieAny_eq_true _ _).mpr ⟨u, hu, h1u⟩) (by simp [ha1])
    · exact absurd ((trieAny_eq_true _ _).mpr ⟨v, hv, h1v⟩) (by simp [hb1])

end S2aProdAndJ10

section J10IndepAndR15

def toPi10 (u v : StrongPowV (ZMod 7) 5) : Fin 10 → ZMod 7 :=
  strongProdIsoAdd C7 5 5 (strongPowEquivPi C7 5 u, strongPowEquivPi C7 5 v)

@[irreducible] def jBlock10 (b : Nat) : Finset (Fin 10 → ZMod 7) :=
  prodSet (piSet5 (jBlockL b)) (piSet5 (jBlockR b))

theorem jBlock10_def (b : Nat) :
    jBlock10 b = prodSet (piSet5 (jBlockL b)) (piSet5 (jBlockR b)) := by
  unfold jBlock10; rfl

theorem T5_pi_map_jBlockL (b : Fin 7) :
    (piSet5 (match b with
      | 0 => tB5 | 1 => tS5 | 2 => tPH5 | 3 => tPV5 | 4 => tX05 | 5 => tXH5 | 6 => tXV5)).map
      T5_pi_iso.toEquiv.toEmbedding = piSet5 (jBlockL b.val) := by
  fin_cases b
  · exact piSet5_map_T5 tTB5_map_ok tTB5_card_eq
  · exact piSet5_map_T5 tTS5_map_ok tTS5_card_eq
  · exact piSet5_map_T5 tTPH5_map_ok tTPH5_card_eq
  · exact piSet5_map_T5 tTPV5_map_ok tTPV5_card_eq
  · exact piSet5_map_T5 tTX05_map_ok tTX05_card_eq
  · exact piSet5_map_T5 tTXH5_map_ok tTXH5_card_eq
  · exact piSet5_map_T5 tTXV5_map_ok tTXV5_card_eq

theorem T5_pi_map_jBlockR (b : Fin 7) :
    (piSet5 (match b with
      | 0 => tB5 | 1 => tX05 | 2 => tXH5 | 3 => tXV5 | 4 => tS5 | 5 => tPV5 | 6 => tPH5)).map
      T5_pi_iso.toEquiv.toEmbedding = piSet5 (jBlockR b.val) := by
  fin_cases b
  · exact piSet5_map_T5 tTB5_map_ok tTB5_card_eq
  · exact piSet5_map_T5 tTX05_map_ok tTX05_card_eq
  · exact piSet5_map_T5 tTXH5_map_ok tTXH5_card_eq
  · exact piSet5_map_T5 tTXV5_map_ok tTXV5_card_eq
  · exact piSet5_map_T5 tTS5_map_ok tTS5_card_eq
  · exact piSet5_map_T5 tTPV5_map_ok tTPV5_card_eq
  · exact piSet5_map_T5 tTPH5_map_ok tTPH5_card_eq

@[irreducible] def J10_base : Finset (Fin 10 → ZMod 7) :=
  (R10.P .B ∪ R10.P .O).map T10_pi_iso.toEquiv.toEmbedding

theorem J10_base_def : J10_base = (R10.P .B ∪ R10.P .O).map T10_pi_iso.toEquiv.toEmbedding := by
  unfold J10_base; rfl

theorem J10_base_indep : (strongPowPi C7 10).IsIndepSet (J10_base : Set (Fin 10 → ZMod 7)) := by
  have hi : (strongPowPi C7 10).IsIndepSet ((R10.P .B ∪ R10.P .O : Finset (Fin 10 → ZMod 7)) : Set (Fin 10 → ZMod 7)) :=
    isIndepSet_union_of_sep (R10.hindep .B) (R10.hindep .O) (R10.hsep .B .O rfl)
  intro x hx y hy hne hadj
  rw [J10_base_def] at hx hy
  rcases Finset.mem_map.mp (Finset.mem_coe.mp hx) with ⟨x', hx', rfl⟩
  rcases Finset.mem_map.mp (Finset.mem_coe.mp hy) with ⟨y', hy', rfl⟩
  exact hi hx' hy' (fun h => hne (congrArg T10_pi_iso h)) ((T10_pi_iso.map_rel_iff).mp hadj)

theorem J10_base_eq_blocks :
    J10_base = jBlock10 0 ∪ jBlock10 1 ∪ jBlock10 2 ∪ jBlock10 3 ∪ jBlock10 4 ∪ jBlock10 5 ∪ jBlock10 6 := by
  have hB : R10.P .B = prodSet (baseR5.P .B) (baseR5.P .B) ∪ prodSet (baseR5.P .H) (baseR5.P .D) ∪
      prodSet (baseR5.P .V) (baseR5.P .A) ∪ prodSet (baseR5.P .D) (baseR5.P .V) ∪
      prodSet (baseR5.P .A) (baseR5.P .H) := by
    simp only [R10_def, s2aProd, Realisation.mapIso, s2aFam, Finset.map_union, prodSet_def]
  have hO : R10.P .O = prodSet (baseR5.P .O) (baseR5.P .N) ∪ prodSet (baseR5.P .N) (baseR5.P .O) := by
    simp only [R10_def, s2aProd, Realisation.mapIso, s2aFam, Finset.map_union, prodSet_def]
  have hm : ∀ A B, (prodSet A B).map T10_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T5_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T5_pi_iso T5_pi_iso A B
  have hv0 : (0 : Fin 7).val = 0 := rfl
  have hv1 : (1 : Fin 7).val = 1 := rfl
  have hv2 : (2 : Fin 7).val = 2 := rfl
  have hv3 : (3 : Fin 7).val = 3 := rfl
  have hv4 : (4 : Fin 7).val = 4 := rfl
  have hv5 : (5 : Fin 7).val = 5 := rfl
  have hv6 : (6 : Fin 7).val = 6 := rfl
  have map_j0 : (prodSet (piSet5 tB5) (piSet5 tB5)).map T10_pi_iso.toEquiv.toEmbedding = jBlock10 0 := by
    rw [hm, jBlock10_def]
    congr 1
    · exact (T5_pi_map_jBlockL 0).trans (by rw [hv0])
    · exact (T5_pi_map_jBlockR 0).trans (by rw [hv0])
  have map_j1 : (prodSet (piSet5 tS5) (piSet5 tX05)).map T10_pi_iso.toEquiv.toEmbedding = jBlock10 1 := by
    rw [hm, jBlock10_def, T5_pi_map_jBlockL 1, T5_pi_map_jBlockR 1, hv1]
  have map_j2 : (prodSet (piSet5 tPH5) (piSet5 tXH5)).map T10_pi_iso.toEquiv.toEmbedding = jBlock10 2 := by
    rw [hm, jBlock10_def, T5_pi_map_jBlockL 2, T5_pi_map_jBlockR 2, hv2]
  have map_j3 : (prodSet (piSet5 tPV5) (piSet5 tXV5)).map T10_pi_iso.toEquiv.toEmbedding = jBlock10 3 := by
    rw [hm, jBlock10_def, T5_pi_map_jBlockL 3, T5_pi_map_jBlockR 3, hv3]
  have map_j4 : (prodSet (piSet5 tX05) (piSet5 tS5)).map T10_pi_iso.toEquiv.toEmbedding = jBlock10 4 := by
    rw [hm, jBlock10_def, T5_pi_map_jBlockL 4, T5_pi_map_jBlockR 4, hv4]
  have map_j5 : (prodSet (piSet5 tXH5) (piSet5 tPV5)).map T10_pi_iso.toEquiv.toEmbedding = jBlock10 5 := by
    rw [hm, jBlock10_def, T5_pi_map_jBlockL 5, T5_pi_map_jBlockR 5, hv5]
  have map_j6 : (prodSet (piSet5 tXV5) (piSet5 tPH5)).map T10_pi_iso.toEquiv.toEmbedding = jBlock10 6 := by
    rw [hm, jBlock10_def, T5_pi_map_jBlockL 6, T5_pi_map_jBlockR 6, hv6]
  rw [J10_base_def, hB, hO]
  simp only [Finset.map_union, baseR5_P_eq]
  rw [map_j0, map_j1, map_j2, map_j3, map_j4, map_j5, map_j6]
  ext z; simp only [Finset.mem_union]
  constructor
  · rintro (((((h | h) | h) | h) | h) | h | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
    · exact Or.inl (Or.inl (Or.inr h))
  · rintro ((((((h | h) | h) | h) | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)

theorem J10_base_card : J10_base.card = 134753 := by
  rw [J10_base_def, Finset.card_map, Finset.card_union_of_disjoint (R10.hsep .B .O rfl).disjoint]
  rw [← Realisation.w, ← Realisation.w, R10_w.1, R10_w.2.2.2.2.1]

def remSet10 : Finset (Fin 10 → ZMod 7) :=
  (swapPairs.map (fun p => toPi10 p.1.1 p.1.2)).toFinset

def insSet10 : Finset (Fin 10 → ZMod 7) :=
  (swapPairs.map (fun p => toPi10 p.2.1 p.2.2)).toFinset

theorem toPi10_inj : Function.Injective (fun p : StrongPowV (ZMod 7) 5 × StrongPowV (ZMod 7) 5 => toPi10 p.1 p.2) := by
  intro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h
  have h1 := (strongProdIsoAdd C7 5 5).injective h
  have ha := (strongPowEquivPi C7 5).injective (Prod.ext_iff.mp h1).1
  have hb := (strongPowEquivPi C7 5).injective (Prod.ext_iff.mp h1).2
  exact Prod.ext ha hb

theorem remSet10_card : remSet10.card = 8 := by
  rw [remSet10, List.toFinset_card_of_nodup]
  · simp [swapPairs]
  · have hmap : swapPairs.map (fun p => toPi10 p.1.1 p.1.2) =
        (swapPairs.map Prod.fst).map (fun p => toPi10 p.1 p.2) := by rfl
    rw [hmap]
    exact rems_nodup.map toPi10_inj

theorem remSet10_sub_base : remSet10 ⊆ J10_base := by
  intro z hz
  simp only [remSet10, List.mem_toFinset, List.mem_map] at hz
  rcases hz with ⟨⟨⟨r₀, r₁⟩, ⟨v₀, v₁⟩⟩, hp, rfl⟩
  have hmem_rem : (r₀, r₁) ∈ remBlocks.map Prod.snd := by
    have : swapPairs.map Prod.fst = remBlocks.map Prod.snd := by decide
    rw [← this, List.mem_map]
    exact ⟨⟨(r₀, r₁), (v₀, v₁)⟩, hp, rfl⟩
  rcases List.mem_map.mp hmem_rem with ⟨⟨b, p⟩, hb, heq⟩
  change p = (r₀, r₁) at heq
  rw [heq] at hb
  have hok := List.all_eq_true.mp remBlocks_mem (b, (r₀, r₁)) hb
  simp only [Bool.and_eq_true] at hok
  have hinB : toPi10 r₀ r₁ ∈ jBlock10 b := by
    rw [toPi10, jBlock10_def, prodSet_def, Finset.mem_map]
    refine ⟨(strongPowEquivPi C7 5 r₀, strongPowEquivPi C7 5 r₁), Finset.mk_mem_product ?_ ?_, rfl⟩
    · rw [piSet5_def, Finset.mem_map]; exact ⟨r₀, Trie7.mem_toFinset_iff_memBool.mpr hok.1, rfl⟩
    · rw [piSet5_def, Finset.mem_map]; exact ⟨r₁, Trie7.mem_toFinset_iff_memBool.mpr hok.2, rfl⟩
  have hb_lt : b < 7 := by
    have : remBlocks.all (fun p => p.1 < 7) = true := by decide
    simpa using List.all_eq_true.mp this (b, (r₀, r₁)) hb
  rw [J10_base_eq_blocks]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hinB)))))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hinB)))))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hinB))))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hinB)))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hinB))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hinB)
  · exact Finset.mem_union_right _ hinB

def J10_outBase : Finset (Fin 10 → ZMod 7) :=
  Finset.biUnion outRectsBase.toFinset (fun p => rectPi10 p.1 p.2)

theorem J10_out_eq_union : J10_out = J10_outBase ∪ insSet10 := by
  have hsplit : outRects = outRectsBase ++ outRects.drop 8 := by decide
  have hdrop : Finset.biUnion (outRects.drop 8).toFinset (fun p => rectPi10 p.1 p.2) = insSet10 := by
    have hmatch := swapIns_match
    have haux : ∀ (vs : List (StrongPowV (ZMod 7) 5 × StrongPowV (ZMod 7) 5)) (rs : List (Nat × Nat)),
        checkInsMatch vs rs = true →
        Finset.biUnion rs.toFinset (fun p => rectPi10 p.1 p.2) = (vs.map (fun p => toPi10 p.1 p.2)).toFinset := by
      intro vs rs hm
      induction vs generalizing rs with
      | nil => cases rs with
        | nil => simp
        | cons _ _ => simp [checkInsMatch] at hm
      | cons v vs' ih => cases rs with
        | nil => simp [checkInsMatch] at hm
        | cons r rs' =>
          simp only [checkInsMatch, Bool.and_eq_true] at hm
          rcases hm with ⟨⟨⟨⟨hc1, hc2⟩, hm1⟩, hm2⟩, hrest⟩
          rw [List.toFinset_cons, Finset.biUnion_insert, ih rs' hrest,
              List.map_cons, List.toFinset_cons]
          have hsing : rectPi10 r.1 r.2 = {toPi10 v.1 v.2} := by
            have hs1 : (piSet5 (rectAt r.1)).card = 1 := by rw [piSet5_card]; simpa using hc1
            have hs2 : (piSet5 (rectAt r.2)).card = 1 := by rw [piSet5_card]; simpa using hc2
            have hmem1 : strongPowEquivPi C7 5 v.1 ∈ piSet5 (rectAt r.1) := by
              rw [piSet5_def, Finset.mem_map]; exact ⟨v.1, Trie7.mem_toFinset_iff_memBool.mpr hm1, rfl⟩
            have hmem2 : strongPowEquivPi C7 5 v.2 ∈ piSet5 (rectAt r.2) := by
              rw [piSet5_def, Finset.mem_map]; exact ⟨v.2, Trie7.mem_toFinset_iff_memBool.mpr hm2, rfl⟩
            rcases Finset.card_eq_one.mp hs1 with ⟨x1, hx1⟩
            rw [hx1, Finset.mem_singleton] at hmem1; subst hmem1
            rcases Finset.card_eq_one.mp hs2 with ⟨x2, hx2⟩
            rw [hx2, Finset.mem_singleton] at hmem2; subst hmem2
            rw [rectPi10, hx1, hx2, prodSet_def, Finset.singleton_product_singleton, Finset.map_singleton]
            rfl
          rw [hsing, Finset.singleton_union]
    exact haux (swapPairs.map Prod.snd) (outRects.drop 8) hmatch
  rw [J10_out, hsplit, List.toFinset_append]
  have hbi : ∀ (s t : Finset (Nat × Nat)) (f : Nat × Nat → Finset (Fin 10 → ZMod 7)),
      Finset.biUnion (s ∪ t) f = Finset.biUnion s f ∪ Finset.biUnion t f := by
    intro s t f; ext z; simp only [Finset.mem_biUnion, Finset.mem_union]
    constructor
    · rintro ⟨a, ha | ha, hz⟩
      · exact Or.inl ⟨a, ha, hz⟩
      · exact Or.inr ⟨a, ha, hz⟩
    · rintro (⟨a, ha, hz⟩ | ⟨a, ha, hz⟩)
      · exact ⟨a, Or.inl ha, hz⟩
      · exact ⟨a, Or.inr ha, hz⟩
  rw [hbi, J10_outBase, hdrop]

theorem J10_outBase_in_eq : J10_outBase ∪ J10_in = J10_base \ remSet10 := by
  have hrect : ∀ (b ia ib : Nat), b < 7 →
      (rectAt ia).isSubset (jBlockL b) = true →
      (rectAt ib).isSubset (jBlockR b) = true →
      (∀ r0 r1, (r0, r1) ∈ swapPairs.map Prod.fst → (!((rectAt ia).memBool r0 && (rectAt ib).memBool r1)) = true) →
      rectPi10 ia ib ⊆ J10_base \ remSet10 := by
    intro b ia ib hblt hsubA hsubB hnoRem z hz
    rw [Finset.mem_sdiff]
    rw [rectPi10, prodSet_def, Finset.mem_map] at hz
    rcases hz with ⟨⟨x, y⟩, hxy, rfl⟩
    rw [Finset.mem_product, piSet5_def, piSet5_def] at hxy
    rcases Finset.mem_map.mp hxy.1 with ⟨u, hu, rfl⟩
    rcases Finset.mem_map.mp hxy.2 with ⟨v, hv, rfl⟩
    constructor
    · have hinB : strongProdIsoAdd C7 5 5 (strongPowEquivPi C7 5 u, strongPowEquivPi C7 5 v) ∈ jBlock10 b := by
        rw [jBlock10_def, prodSet_def, Finset.mem_map]
        refine ⟨(strongPowEquivPi C7 5 u, strongPowEquivPi C7 5 v), Finset.mk_mem_product ?_ ?_, rfl⟩
        · rw [piSet5_def]; exact Finset.mem_map.mpr ⟨u, Trie7.toFinset_subset_of_isSubset hsubA hu, rfl⟩
        · rw [piSet5_def]; exact Finset.mem_map.mpr ⟨v, Trie7.toFinset_subset_of_isSubset hsubB hv, rfl⟩
      rw [J10_base_eq_blocks]
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hinB)))))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hinB)))))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hinB))))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hinB)))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hinB))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hinB)
      · exact Finset.mem_union_right _ hinB
    · intro hrem
      simp only [remSet10, List.mem_toFinset, List.mem_map] at hrem
      rcases hrem with ⟨⟨⟨r0, r1⟩, vs⟩, hp, heq⟩
      have heq' : (fun p : StrongPowV (ZMod 7) 5 × StrongPowV (ZMod 7) 5 => toPi10 p.1 p.2) (r0, r1) =
          (fun p : StrongPowV (ZMod 7) 5 × StrongPowV (ZMod 7) 5 => toPi10 p.1 p.2) (u, v) := heq
      have hpair := toPi10_inj heq'
      rcases Prod.ext_iff.mp hpair with ⟨rfl, rfl⟩
      have hno := hnoRem r0 r1 (List.mem_map.mpr ⟨((r0, r1), vs), hp, rfl⟩)
      have hm1 : (rectAt ia).memBool r0 = true := Trie7.mem_toFinset_iff_memBool.mp hu
      have hm2 : (rectAt ib).memBool r1 = true := Trie7.mem_toFinset_iff_memBool.mp hv
      simp [hm1, hm2] at hno
  have hsub : J10_outBase ∪ J10_in ⊆ J10_base \ remSet10 := by
    apply Finset.union_subset
    · intro z hz
      simp only [J10_outBase, Finset.mem_biUnion, List.mem_toFinset] at hz
      rcases hz with ⟨⟨ia, ib⟩, hmem, hz⟩
      have hidx : ∃ b, (b, (ia, ib)) ∈ outBlocks := by
        have hmap : outBlocks.map Prod.snd = outRectsBase := by decide
        rw [← hmap, List.mem_map] at hmem
        rcases hmem with ⟨⟨b, p⟩, hb, rfl⟩; exact ⟨b, hb⟩
      rcases hidx with ⟨b, hb⟩
      have hblt : b < 7 := by
        have : outBlocks.all (fun p => p.1 < 7) = true := by decide
        simpa using List.all_eq_true.mp this (b, (ia, ib)) hb
      have hsubAB := List.all_eq_true.mp outBlocks_sub (b, (ia, ib)) hb
      simp only [Bool.and_eq_true] at hsubAB
      refine hrect b ia ib hblt hsubAB.1 hsubAB.2 (fun r0 r1 hr => ?_) hz
      have hmap_rem : remBlocks.map Prod.snd = swapPairs.map Prod.fst := by decide
      rw [← hmap_rem, List.mem_map] at hr
      rcases hr with ⟨⟨br, rr⟩, hbr, rfl⟩
      exact List.all_eq_true.mp (List.all_eq_true.mp rems_disj_outBase (br, (r0, r1)) hbr) (ia, ib) hmem
    · intro z hz
      simp only [J10_in, Finset.mem_biUnion, List.mem_toFinset] at hz
      rcases hz with ⟨⟨ia, ib⟩, hmem, hz⟩
      have hidx : ∃ b, (b, (ia, ib)) ∈ inBlocks := by
        have hmap : inBlocks.map Prod.snd = inRects := by decide
        rw [← hmap, List.mem_map] at hmem
        rcases hmem with ⟨⟨b, p⟩, hb, rfl⟩; exact ⟨b, hb⟩
      rcases hidx with ⟨b, hb⟩
      have hblt : b < 7 := by
        have : inBlocks.all (fun p => p.1 < 7) = true := by decide
        simpa using List.all_eq_true.mp this (b, (ia, ib)) hb
      have hsubAB := List.all_eq_true.mp inBlocks_sub (b, (ia, ib)) hb
      simp only [Bool.and_eq_true] at hsubAB
      refine hrect b ia ib hblt hsubAB.1 hsubAB.2 (fun r0 r1 hr => ?_) hz
      have hmap_rem : remBlocks.map Prod.snd = swapPairs.map Prod.fst := by decide
      rw [← hmap_rem, List.mem_map] at hr
      rcases hr with ⟨⟨br, rr⟩, hbr, rfl⟩
      exact List.all_eq_true.mp (List.all_eq_true.mp rems_disj_in (br, (r0, r1)) hbr) (ia, ib) hmem
  have hdisjBase : Disjoint J10_outBase J10_in := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    have h1' : z ∈ J10_out := by rw [J10_out_eq_union]; exact Finset.mem_union_left _ h1
    exact Finset.disjoint_left.mp J10_out_sep_in.disjoint h1' h2
  have houtBase_disj : rectListPairwiseDisj outRectsBase = true := by
    have hsplit : outRects = outRectsBase ++ outRects.drop 8 := by decide
    have h := outRects_disj
    rw [hsplit] at h
    have aux : ∀ l₁ l₂ : List (Nat × Nat), rectListPairwiseDisj (l₁ ++ l₂) = true → rectListPairwiseDisj l₁ = true := by
      intro l₁ l₂; induction l₁ with
      | nil => simp [rectListPairwiseDisj]
      | cons x xs ih =>
        simp only [List.cons_append, rectListPairwiseDisj, Bool.and_eq_true, List.all_append]
        rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, ih h2⟩
    exact aux outRectsBase (outRects.drop 8) h
  have hcard_outBase : J10_outBase.card = (outRectsBase.map (fun p => (rectAt p.1).card * (rectAt p.2).card)).sum :=
    card_biUnion_rectPi10 outRectsBase houtBase_disj
  have hcard_lhs : (J10_outBase ∪ J10_in).card = 134745 := by
    rw [Finset.card_union_of_disjoint hdisjBase, hcard_outBase, J10_in_card]
    have hs := base_out_in_sum
    have hi := inRects_card_sum
    have hfn : (fun p : ℕ × ℕ => (rectAt p.1).card * (rectAt p.2).card) =
        (fun x : ℕ × ℕ => match x with | (a, b) => (rectAt a).card * (rectAt b).card) :=
      funext (fun ⟨_, _⟩ => rfl)
    rw [hfn, hi] at hs
    rw [hfn]
    generalize (List.map (fun x : ℕ × ℕ => match x with | (a, b) => (rectAt a).card * (rectAt b).card) outRectsBase).sum = s at *
    omega
  have hcard_rhs : (J10_base \ remSet10).card = 134745 := by
    rw [Finset.card_sdiff_of_subset remSet10_sub_base, J10_base_card, remSet10_card]
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

theorem J10p_indep : (strongPowPi C7 10).IsIndepSet ((J10_out ∪ J10_in : Finset (Fin 10 → ZMod 7)) : Set (Fin 10 → ZMod 7)) := by
  have heq : J10_out ∪ J10_in = (J10_base \ remSet10) ∪ insSet10 := by
    rw [J10_out_eq_union]
    calc (J10_outBase ∪ insSet10) ∪ J10_in
        = (J10_outBase ∪ J10_in) ∪ insSet10 := by ac_rfl
      _ = (J10_base \ remSet10) ∪ insSet10 := by rw [J10_outBase_in_eq]
  rw [heq]
  have toPi10_close_iff : ∀ u₁ v₁ u₂ v₂ : StrongPowV (ZMod 7) 5,
      (toPi10 u₁ v₁ = toPi10 u₂ v₂ ∨ (strongPowPi C7 10).Adj (toPi10 u₁ v₁) (toPi10 u₂ v₂)) ↔
        (word5AdjOrEq u₁ u₂ = true ∧ word5AdjOrEq v₁ v₂ = true) := by
    intro u₁ v₁ u₂ v₂
    rw [word5AdjOrEq_iff, word5AdjOrEq_iff, toPi10, toPi10]
    have h1 : ∀ a b : Fin 10 → ZMod 7, (a = b ∨ (strongPowPi C7 10).Adj a b) ↔
        ((strongProdIsoAdd C7 5 5).symm a = (strongProdIsoAdd C7 5 5).symm b ∨
         (strongPowPi C7 5 ⊠ strongPowPi C7 5).Adj ((strongProdIsoAdd C7 5 5).symm a) ((strongProdIsoAdd C7 5 5).symm b)) := by
      intro a b
      constructor
      · rintro (rfl | hadj)
        · left; rfl
        · right; exact ((strongProdIsoAdd C7 5 5).symm.map_rel_iff).mpr hadj
      · rintro (heq | hadj)
        · left; exact (strongProdIsoAdd C7 5 5).symm.injective heq
        · right; exact ((strongProdIsoAdd C7 5 5).symm.map_rel_iff).mp hadj
    rw [h1, RelIso.symm_apply_apply, RelIso.symm_apply_apply, strongProd_close_iff]
    simp only [(strongPowEquivPi C7 5).apply_eq_iff_eq, (strongPowEquivPi C7 5).map_rel_iff]
  have hins_indep : (strongPowPi C7 10).IsIndepSet (insSet10 : Set (Fin 10 → ZMod 7)) := by
    intro x hx y hy hne hadj
    simp only [insSet10, Finset.mem_coe, List.mem_toFinset, List.mem_map] at hx hy
    rcases hx with ⟨⟨rx, ⟨vx0, vx1⟩⟩, hpx, rfl⟩
    rcases hy with ⟨⟨ry, ⟨vy0, vy1⟩⟩, hpy, rfl⟩
    have hins_list : ∀ (l : List (StrongPowV (ZMod 7) 5 × StrongPowV (ZMod 7) 5)),
        listPairwiseNotClose10 l = true →
        ∀ (a b : StrongPowV (ZMod 7) 5 × StrongPowV (ZMod 7) 5), a ∈ l → b ∈ l → a ≠ b →
          !(word5AdjOrEq a.1 b.1 && word5AdjOrEq a.2 b.2) = true := by
      intro l hl a b ha hb hab
      induction l generalizing a b with
      | nil => simp at ha
      | cons c rest ih =>
        simp only [listPairwiseNotClose10, Bool.and_eq_true, List.all_eq_true] at hl
        rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd rfl hab
        · simpa using hl.1 b hb'
        · have hc := hl.1 a ha'
          have hsym : word5AdjOrEq a.1 b.1 = word5AdjOrEq b.1 a.1 ∧ word5AdjOrEq a.2 b.2 = word5AdjOrEq b.2 a.2 := by
            constructor <;> apply Bool.eq_iff_iff.mpr <;> simp only [word5AdjOrEq_iff] <;>
              exact ⟨fun h => h.imp Eq.symm SimpleGraph.Adj.symm, fun h => h.imp Eq.symm SimpleGraph.Adj.symm⟩
          simpa [hsym.1, hsym.2] using hc
        · exact ih hl.2 a b ha' hb' hab
    have hneqPair : (vx0, vx1) ≠ (vy0, vy1) := fun h => hne (by rw [h])
    have hnot := hins_list (swapPairs.map Prod.snd) inss_indep_ok (vx0, vx1) (vy0, vy1)
      (List.mem_map.mpr ⟨(rx, (vx0, vx1)), hpx, rfl⟩)
      (List.mem_map.mpr ⟨(ry, (vy0, vy1)), hpy, rfl⟩) hneqPair
    have hclose := (toPi10_close_iff vx0 vx1 vy0 vy1).mp (Or.inr hadj)
    simp [hclose.1, hclose.2] at hnot
  have hcross : ∀ v ∈ insSet10, ∀ u ∈ J10_base \ remSet10, ¬ (v = u ∨ (strongPowPi C7 10).Adj v u) := by
    intro v hv u hu hc
    rw [Finset.mem_sdiff] at hu
    simp only [insSet10, List.mem_toFinset, List.mem_map] at hv
    rcases hv with ⟨⟨⟨r0, r1⟩, ⟨v0, v1⟩⟩, hp, rfl⟩
    have hfind : ∃ i : Fin 8, swapPairs[i.val] = ((r0, r1), (v0, v1)) := by
      rcases List.mem_iff_getElem.mp hp with ⟨i, hi, heq⟩
      exact ⟨⟨i, hi⟩, heq⟩
    rcases hfind with ⟨i, hi⟩
    have hhit : swapHitOK ((r0, r1), (v0, v1)) = true := by
      rw [← hi]
      fin_cases i
      · exact swap_hit_0
      · exact swap_hit_1
      · exact swap_hit_2
      · exact swap_hit_3
      · exact swap_hit_4
      · exact swap_hit_5
      · exact swap_hit_6
      · exact swap_hit_7
    have hu_base := hu.1
    rw [J10_base_eq_blocks] at hu_base
    have hmem_b : ∃ b : Fin 7, u ∈ jBlock10 b.val := by
      simp only [Finset.mem_union] at hu_base
      rcases hu_base with (((((h0 | h1) | h2) | h3) | h4) | h5) | h6
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
      · exact ⟨3, h3⟩
      · exact ⟨4, h4⟩
      · exact ⟨5, h5⟩
      · exact ⟨6, h6⟩
    rcases hmem_b with ⟨b, hb⟩
    rw [jBlock10_def, prodSet_def, Finset.mem_map] at hb
    rcases hb with ⟨⟨xu, yu⟩, hxy, rfl⟩
    rw [Finset.mem_product, piSet5_def, piSet5_def] at hxy
    rcases Finset.mem_map.mp hxy.1 with ⟨u0, hu0, rfl⟩
    rcases Finset.mem_map.mp hxy.2 with ⟨u1, hu1, rfl⟩
    have hclose := (toPi10_close_iff v0 v1 u0 u1).mp hc
    have hb_ok := List.all_eq_true.mp hhit b.val (by fin_cases b <;> decide)
    dsimp only [blockHitsOnly] at hb_ok
    have hu0_ok := (trieAll_eq_true _ (jBlockL b.val)).mp hb_ok u0 hu0
    simp only [hclose.1, Bool.not_true, Bool.false_or] at hu0_ok
    have hu1_ok := (trieAll_eq_true _ (jBlockR b.val)).mp hu0_ok u1 hu1
    simp only [hclose.2, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hu1_ok
    have heq_r0 : u0 = r0 := by simpa using hu1_ok.1
    have heq_r1 : u1 = r1 := by simpa using hu1_ok.2
    subst heq_r0; subst heq_r1
    apply hu.2
    simp only [remSet10, List.mem_toFinset, List.mem_map]
    exact ⟨((u0, u1), (v0, v1)), hp, rfl⟩
  exact isIndepSet_union_of_sep
    (fun x hx y hy hne hadj => J10_base_indep (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hy).1 hne hadj)
    hins_indep
    (fun u hu v hv hc => hcross v hv u hu (hc.imp Eq.symm SimpleGraph.Adj.symm))

theorem J10_out_indep : (strongPowPi C7 10).IsIndepSet (J10_out : Set (Fin 10 → ZMod 7)) :=
  isIndepSet_subset J10p_indep Finset.subset_union_left

theorem J10_in_indep : (strongPowPi C7 10).IsIndepSet (J10_in : Set (Fin 10 → ZMod 7)) :=
  isIndepSet_subset J10p_indep Finset.subset_union_right

end J10IndepAndR15

section SigBridgeAndC2

open scoped Classical

noncomputable def sig5Pi (x : Fin 5 → ZMod 7) : Nat :=
  (if inNbr (strongPowPi C7 5) (piSet5 tX05) x then 2 else 0) +
  (if inNbr (strongPowPi C7 5) (piSet5 tX15) x then 1 else 0)

noncomputable def sig5_3Pi (x : Fin 5 → ZMod 7) : Nat :=
  (if inNbr (strongPowPi C7 5) (piSet5 tX05) x then 4 else 0) +
  (if inNbr (strongPowPi C7 5) (piSet5 tXH5) x then 2 else 0) +
  (if inNbr (strongPowPi C7 5) (piSet5 tXV5) x then 1 else 0)

theorem sig5_3Pi_lt (x : Fin 5 → ZMod 7) : sig5_3Pi x < 8 := by
  dsimp only [sig5_3Pi]; split_ifs <;> omega

theorem sig5_3Bool_eq_sig5_3Pi (w : StrongPowV (ZMod 7) 5) :
    sig5_3Bool w = sig5_3Pi (strongPowEquivPi C7 5 w) := by
  simp only [sig5_3Bool, sig5_3Pi, ← inNbr_piSet5]

theorem eval_dist5_3List_pi (t : Trie7 5) (g : Nat → Nat) :
    vec16Eval (dist5_3List t) g = ∑ x ∈ piSet5 t, g (sig5_3Pi x) := by
  rw [eval_dist5_3List, piSet5_def, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro w _
  rw [sig5_3Bool_eq_sig5_3Pi]
  rfl

noncomputable def sig10Pi (z : Fin 10 → ZMod 7) : Nat :=
  (if inNbr (strongPowPi C7 10) X0_10 z then 8 else 0) +
  (if inNbr (strongPowPi C7 10) X1_10 z then 4 else 0) +
  (if inNbr (strongPowPi C7 10) J10_out z then 2 else 0) +
  (if inNbr (strongPowPi C7 10) J10_in z then 1 else 0)

theorem sig10Pi_lt (z : Fin 10 → ZMod 7) : sig10Pi z < 16 := by
  dsimp only [sig10Pi]; split_ifs <;> omega

private theorem bit2_and1_of_lt4 {b0 b1 : Bool} :
    (((((if b0 then 2 else 0) + (if b1 then 1 else 0)) >>> 1) &&& 1) = if b0 then 1 else 0) ∧
    ((((if b0 then 2 else 0) + (if b1 then 1 else 0)) &&& 1) = if b1 then 1 else 0) := by
  cases b0 <;> cases b1 <;> decide

private theorem bit1_and_or {a0 a1 b0 b1 : Bool} :
    (((if a0 then 1 else 0) &&& (if b0 then 1 else 0)) ||| ((if a1 then 1 else 0) &&& (if b1 then 1 else 0)) =
      if (a0 ∧ b0) ∨ (a1 ∧ b1) then 1 else 0) := by
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> decide

private theorem idx10_pack (c3 c2 c1 c0 : Prop) [Decidable c3] [Decidable c2] [Decidable c1] [Decidable c0] :
    ((if c3 then 1 else 0) <<< 3) ||| ((if c2 then 1 else 0) <<< 2) ||| ((if c1 then 1 else 0) <<< 1) ||| (if c0 then 1 else 0) =
      (if c3 then 8 else 0) + (if c2 then 4 else 0) + (if c1 then 2 else 0) + (if c0 then 1 else 0) := by
  by_cases c3 <;> by_cases c2 <;> by_cases c1 <;> by_cases c0 <;> simp [*]

private theorem inNbr_X0_10_iff (u v : StrongPowV (ZMod 7) 5) :
    inNbr (strongPowPi C7 10) X0_10 (strongProdIsoAdd C7 5 5 (strongPowEquivPi C7 5 u, strongPowEquivPi C7 5 v)) ↔
      ((tX05.inClosedNbr u = true ∧ tX05.inClosedNbr v = true) ∨
       (tX15.inClosedNbr u = true ∧ tX15.inClosedNbr v = true)) := by
  rw [X0_10, inNbr_union, inNbr_prodSet (dL := 5) (dR := 5), inNbr_prodSet (dL := 5) (dR := 5),
      inNbr_piSet5, inNbr_piSet5, inNbr_piSet5, inNbr_piSet5]

private theorem inNbr_X1_10_iff (u v : StrongPowV (ZMod 7) 5) :
    inNbr (strongPowPi C7 10) X1_10 (strongProdIsoAdd C7 5 5 (strongPowEquivPi C7 5 u, strongPowEquivPi C7 5 v)) ↔
      ((tX05.inClosedNbr u = true ∧ tX15.inClosedNbr v = true) ∨
       (tX15.inClosedNbr u = true ∧ tX05.inClosedNbr v = true)) := by
  rw [X1_10, inNbr_union, inNbr_prodSet (dL := 5) (dR := 5), inNbr_prodSet (dL := 5) (dR := 5),
      inNbr_piSet5, inNbr_piSet5, inNbr_piSet5, inNbr_piSet5]

private theorem inNbr_rectList_iff (rs : List (Nat × Nat)) (hb : ∀ p ∈ rs, p.1 < 20 ∧ p.2 < 20)
    (u v : StrongPowV (ZMod 7) 5) :
    inNbr (strongPowPi C7 10) (rs.toFinset.biUnion (fun p => rectPi10 p.1 p.2))
        (strongProdIsoAdd C7 5 5 (strongPowEquivPi C7 5 u, strongPowEquivPi C7 5 v)) ↔
      ((maskOf v &&& reqMask rs (maskOf u) != 0) = true) := by
  rw [inNbr_biUnion]
  have hreq : reqMask rs (maskOf u) =
      rs.foldl (fun a (ia, ib) => if ((maskOf u >>> ia) &&& 1 == 1) then a ||| (1 <<< ib) else a) 0 := rfl
  rw [hreq, bit_and_reqMask_foldl, Nat.and_zero]
  simp only [bne_self_eq_false, Bool.false_or, List.mem_toFinset, List.any_eq_true]
  constructor
  · rintro ⟨⟨ia, ib⟩, hm, hin⟩
    refine ⟨(ia, ib), hm, ?_⟩
    have hbi := hb (ia, ib) hm
    rw [rectPi10, inNbr_prodSet (dL := 5) (dR := 5), inNbr_piSet5, inNbr_piSet5] at hin
    have ha := testBit_maskOf u ⟨ia, hbi.1⟩
    have hb' := testBit_maskOf v ⟨ib, hbi.2⟩
    dsimp only at ha hb' ⊢
    rw [nat_shiftRight_and_one_eq_testBit, nat_shiftRight_and_one_eq_testBit, ha, hb']
    simp [hin.1, hin.2]
  · rintro ⟨⟨ia, ib⟩, hm, h⟩
    refine ⟨(ia, ib), hm, ?_⟩
    have hbi := hb (ia, ib) hm
    rw [rectPi10, inNbr_prodSet (dL := 5) (dR := 5), inNbr_piSet5, inNbr_piSet5]
    have ha := testBit_maskOf u ⟨ia, hbi.1⟩
    have hb' := testBit_maskOf v ⟨ib, hbi.2⟩
    dsimp only at ha hb' h ⊢
    rw [nat_shiftRight_and_one_eq_testBit, nat_shiftRight_and_one_eq_testBit, ha, hb', Bool.and_eq_true] at h
    exact h

theorem idx10OfKeys_eq_sig10Pi (u v : StrongPowV (ZMod 7) 5) :
    idx10OfKeys (keyOf u) (keyOf v) =
      sig10Pi (strongProdIsoAdd C7 5 5 (strongPowEquivPi C7 5 u, strongPowEquivPi C7 5 v)) := by
  dsimp only [idx10OfKeys, sig10Pi]
  rw [keyOf_mod_four u, keyOf_div_four u, keyOf_mod_four v, keyOf_div_four v]
  dsimp only [sig5Bool]
  have hA := bit2_and1_of_lt4 (b0 := tX05.inClosedNbr u) (b1 := tX15.inClosedNbr u)
  have hB := bit2_and1_of_lt4 (b0 := tX05.inClosedNbr v) (b1 := tX15.inClosedNbr v)
  rw [hA.1, hA.2, hB.1, hB.2]
  have hx0 : ((if tX05.inClosedNbr u = true then 1 else 0) &&& (if tX05.inClosedNbr v = true then 1 else 0)) |||
             ((if tX15.inClosedNbr u = true then 1 else 0) &&& (if tX15.inClosedNbr v = true then 1 else 0)) =
      if inNbr (strongPowPi C7 10) X0_10 (strongProdIsoAdd C7 5 5 (strongPowEquivPi C7 5 u, strongPowEquivPi C7 5 v)) then 1 else 0 := by
    rw [bit1_and_or]; simp only [← inNbr_X0_10_iff u v]
  have hx1 : ((if tX05.inClosedNbr u = true then 1 else 0) &&& (if tX15.inClosedNbr v = true then 1 else 0)) |||
             ((if tX15.inClosedNbr u = true then 1 else 0) &&& (if tX05.inClosedNbr v = true then 1 else 0)) =
      if inNbr (strongPowPi C7 10) X1_10 (strongProdIsoAdd C7 5 5 (strongPowEquivPi C7 5 u, strongPowEquivPi C7 5 v)) then 1 else 0 := by
    rw [bit1_and_or]; simp only [← inNbr_X1_10_iff u v]
  have hjo : (if (maskOf v &&& reqMask outRects (maskOf u) != 0) = true then 1 else 0) =
      if inNbr (strongPowPi C7 10) J10_out (strongProdIsoAdd C7 5 5 (strongPowEquivPi C7 5 u, strongPowEquivPi C7 5 v)) then 1 else 0 := by
    have heq : J10_out = outRects.toFinset.biUnion (fun p => rectPi10 p.1 p.2) := rfl
    rw [heq, inNbr_rectList_iff outRects outRects_bound u v]
    by_cases h : (maskOf v &&& reqMask outRects (maskOf u) != 0) = true <;> simp [h]
  have hji : (if (maskOf v &&& reqMask inRects (maskOf u) != 0) = true then 1 else 0) =
      if inNbr (strongPowPi C7 10) J10_in (strongProdIsoAdd C7 5 5 (strongPowEquivPi C7 5 u, strongPowEquivPi C7 5 v)) then 1 else 0 := by
    have heq : J10_in = inRects.toFinset.biUnion (fun p => rectPi10 p.1 p.2) := rfl
    rw [heq, inNbr_rectList_iff inRects inRects_bound u v]
    by_cases h : (maskOf v &&& reqMask inRects (maskOf u) != 0) = true <;> simp [h]
  rw [hx0, hx1, hjo, hji]
  exact idx10_pack _ _ _ _

theorem eval_dist10_16_hist_pi (tA tB : Trie7 5) (g : Nat → Nat) :
    vec16Eval (dist10_16_hist (histOf tA) (histOf tB)) g =
      ∑ z ∈ prodSet (piSet5 tA) (piSet5 tB), g (sig10Pi z) := by
  rw [eval_dist10_16_hist, prodSet_def, Finset.sum_map, Finset.sum_product, piSet5_def, Finset.sum_map]
  apply Finset.sum_congr rfl; intro u _
  rw [piSet5_def, Finset.sum_map]
  apply Finset.sum_congr rfl; intro v _
  exact congrArg g (idx10OfKeys_eq_sig10Pi u v)

private theorem piSet5_map_rectAt_fin (hf : Fin 20) :
    (piSet5 (rectAt hf.val)).map T5_pi_iso.toEquiv.toEmbedding = piSet5 (tRectAt hf.val) := by
  fin_cases hf
  · exact piSet5_map_T5 tTRect0_map_ok tTRect0_card_eq
  · exact piSet5_map_T5 tTRect1_map_ok tTRect1_card_eq
  · exact piSet5_map_T5 tTRect2_map_ok tTRect2_card_eq
  · exact piSet5_map_T5 tTRect3_map_ok tTRect3_card_eq
  · exact piSet5_map_T5 tTRect4_map_ok tTRect4_card_eq
  · exact piSet5_map_T5 tTRect5_map_ok tTRect5_card_eq
  · exact piSet5_map_T5 tTRect6_map_ok tTRect6_card_eq
  · exact piSet5_map_T5 tTRect7_map_ok tTRect7_card_eq
  · exact piSet5_map_T5 tTRect8_map_ok tTRect8_card_eq
  · exact piSet5_map_T5 tTRect9_map_ok tTRect9_card_eq
  · exact piSet5_map_T5 tTRect10_map_ok tTRect10_card_eq
  · exact piSet5_map_T5 tTRect11_map_ok tTRect11_card_eq
  · exact piSet5_map_T5 tTRect12_map_ok tTRect12_card_eq
  · exact piSet5_map_T5 tTRect13_map_ok tTRect13_card_eq
  · exact piSet5_map_T5 tTRect14_map_ok tTRect14_card_eq
  · exact piSet5_map_T5 tTRect15_map_ok tTRect15_card_eq
  · exact piSet5_map_T5 tTRect16_map_ok tTRect16_card_eq
  · exact piSet5_map_T5 tTRect17_map_ok tTRect17_card_eq
  · exact piSet5_map_T5 tTRect18_map_ok tTRect18_card_eq
  · exact piSet5_map_T5 tTRect19_map_ok tTRect19_card_eq

theorem piSet5_map_rectAt (i : Nat) (hi : i < 20) :
    (piSet5 (rectAt i)).map T5_pi_iso.toEquiv.toEmbedding = piSet5 (tRectAt i) :=
  piSet5_map_rectAt_fin ⟨i, hi⟩

theorem vec16_add_zero (v : Vec16) : v.add ({} : Vec16) = v := by
  cases v; rfl

def vec16OfRects : List (Nat × Nat) → Vec16
  | [] => {}
  | (a, b) :: rest => (dist10_16_hist (histOf (tRectAt a)) (histOf (tRectAt b))).add (vec16OfRects rest)

theorem sum_biUnion_rectPi10_map_T10 : ∀ (l : List (Nat × Nat)),
    rectListPairwiseDisj l = true →
    (∀ p ∈ l, p.1 < 20 ∧ p.2 < 20) →
    ∀ (g : Nat → Nat),
    ∑ z ∈ (l.toFinset.biUnion (fun p => rectPi10 p.1 p.2)).map T10_pi_iso.toEquiv.toEmbedding, g (sig10Pi z) =
      vec16Eval (vec16OfRects l) g
  | [], _, _, g => by simp [vec16OfRects, vec16Eval_zero]
  | (a, b) :: rest, hdisj, hbd, g => by
    simp only [rectListPairwiseDisj, Bool.and_eq_true, List.all_eq_true] at hdisj
    have hb_ab := hbd (a, b) (by simp)
    have hbd_rest : ∀ p ∈ rest, p.1 < 20 ∧ p.2 < 20 := fun p hp => hbd p (List.mem_cons_of_mem _ hp)
    have ih := sum_biUnion_rectPi10_map_T10 rest hdisj.2 hbd_rest g
    have hdisj_head : Disjoint (rectPi10 a b) (rest.toFinset.biUnion (fun p => rectPi10 p.1 p.2)) := by
      rw [Finset.disjoint_biUnion_right]
      intro ⟨a', b'⟩ hm
      exact rectPi10_disjoint (hdisj.1 (a', b') (List.mem_toFinset.mp hm))
    have hdisj_map : Disjoint ((rectPi10 a b).map T10_pi_iso.toEquiv.toEmbedding)
        ((rest.toFinset.biUnion (fun p => rectPi10 p.1 p.2)).map T10_pi_iso.toEquiv.toEmbedding) := by
      rw [Finset.disjoint_map]; exact hdisj_head
    rw [List.toFinset_cons, Finset.biUnion_insert, Finset.map_union, Finset.sum_union hdisj_map, ih]
    have hm : ∀ A B, (prodSet A B).map T10_pi_iso.toEquiv.toEmbedding =
        prodSet (A.map T5_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
      fun A B => prodSet_map_iso T5_pi_iso T5_pi_iso A B
    have hmap_head : (rectPi10 a b).map T10_pi_iso.toEquiv.toEmbedding =
        prodSet (piSet5 (tRectAt a)) (piSet5 (tRectAt b)) := by
      rw [rectPi10, hm, piSet5_map_rectAt a hb_ab.1, piSet5_map_rectAt b hb_ab.2]
    rw [hmap_head, ← eval_dist10_16_hist_pi, vec16OfRects, vec16Eval_add]

theorem vec16OfRects_outRects_eq : vec16OfRects outRects = d16_TJout_val := by
  simp only [vec16OfRects, outRects, tRectAt]
  rw [h_tTRect0_eq, h_tTRect1_eq, h_tTRect2_eq, h_tTRect3_eq, h_tTRect6_eq, h_tTRect8_eq,
      h_tTRect9_eq, h_tTRect10_eq, h_tTRect13_eq, h_tTRect14_eq,
      h_tTRect16_eq, h_tTRect17_eq, h_tTRect18_eq, h_tTRect19_eq]
  rw [v_out_0_eq, v_out_1_eq, v_out_2_eq, v_out_3_eq, v_out_4_eq, v_out_5_eq, v_out_6_eq, v_out_7_eq,
      v_out_8_eq, v_out_9_eq, v_out_10_eq, v_out_11_eq, v_out_12_eq, v_out_13_eq, v_out_14_eq, v_out_15_eq]
  rw [vec16_add_zero]
  exact d16_TJout_val_eq

theorem vec16OfRects_inRects_eq : vec16OfRects inRects = d16_TJin_val := by
  simp only [vec16OfRects, inRects, tRectAt]
  rw [h_tTRect0_eq, h_tTRect1_eq, h_tTRect2_eq, h_tTRect3_eq, h_tTRect4_eq, h_tTRect5_eq,
      h_tTRect6_eq, h_tTRect7_eq, h_tTRect8_eq, h_tTRect9_eq, h_tTRect10_eq, h_tTRect11_eq,
      h_tTRect12_eq, h_tTRect13_eq, h_tTRect14_eq, h_tTRect15_eq]
  rw [v_in_0_eq, v_in_1_eq, v_in_2_eq, v_in_3_eq, v_in_4_eq, v_in_5_eq, v_in_6_eq, v_in_7_eq,
      v_in_8_eq, v_in_9_eq, v_in_10_eq, v_in_11_eq, v_in_12_eq, v_in_13_eq, v_in_14_eq, v_in_15_eq,
      v_in_16_eq, v_in_17_eq, v_in_18_eq, v_in_19_eq, v_in_20_eq]
  rw [vec16_add_zero]
  exact d16_TJin_val_eq

theorem sum_TJ10_out (g : Nat → Nat) :
    ∑ z ∈ J10_out.map T10_pi_iso.toEquiv.toEmbedding, g (sig10Pi z) = vec16Eval d16_TJout_val g := by
  rw [J10_out, sum_biUnion_rectPi10_map_T10 outRects outRects_disj outRects_bound g, vec16OfRects_outRects_eq]

theorem sum_TJ10_in (g : Nat → Nat) :
    ∑ z ∈ J10_in.map T10_pi_iso.toEquiv.toEmbedding, g (sig10Pi z) = vec16Eval d16_TJin_val g := by
  rw [J10_in, sum_biUnion_rectPi10_map_T10 inRects inRects_disj inRects_bound g, vec16OfRects_inRects_eq]

theorem sum_T10_P_B (g : Nat → Nat) :
    ∑ z ∈ (R10.P .B).map T10_pi_iso.toEquiv.toEmbedding, g (sig10Pi z) = vec16Eval d16_TB_val g := by
  have sL := baseR5.hsep
  have sR := baseR5.hsep
  have h12 : Disjoint (prodSet (baseR5.P .B) (baseR5.P .B)) (prodSet (baseR5.P .H) (baseR5.P .D)) :=
    (prodSet_sep (dL := 5) (dR := 5) (Or.inl (sL .B .H rfl))).disjoint
  have h123 : Disjoint (prodSet (baseR5.P .B) (baseR5.P .B) ∪ prodSet (baseR5.P .H) (baseR5.P .D))
      (prodSet (baseR5.P .V) (baseR5.P .A)) :=
    (Sep.union_left (prodSet_sep (dL := 5) (dR := 5) (Or.inl (sL .B .V rfl)))
      (prodSet_sep (dL := 5) (dR := 5) (Or.inr (sR .D .A rfl)))).disjoint
  have h1234 : Disjoint ((prodSet (baseR5.P .B) (baseR5.P .B) ∪ prodSet (baseR5.P .H) (baseR5.P .D)) ∪
      prodSet (baseR5.P .V) (baseR5.P .A)) (prodSet (baseR5.P .D) (baseR5.P .V)) :=
    (Sep.union_left (Sep.union_left (prodSet_sep (dL := 5) (dR := 5) (Or.inr (sR .B .V rfl)))
      (prodSet_sep (dL := 5) (dR := 5) (Or.inr (sR .D .V rfl))))
      (prodSet_sep (dL := 5) (dR := 5) (Or.inl (sL .V .D rfl)))).disjoint
  have h12345 : Disjoint (((prodSet (baseR5.P .B) (baseR5.P .B) ∪ prodSet (baseR5.P .H) (baseR5.P .D)) ∪
      prodSet (baseR5.P .V) (baseR5.P .A)) ∪ prodSet (baseR5.P .D) (baseR5.P .V))
      (prodSet (baseR5.P .A) (baseR5.P .H)) :=
    (Sep.union_left (Sep.union_left (Sep.union_left
      (prodSet_sep (dL := 5) (dR := 5) (Or.inr (sR .B .H rfl)))
      (prodSet_sep (dL := 5) (dR := 5) (Or.inl (sL .H .A rfl))))
      (prodSet_sep (dL := 5) (dR := 5) (Or.inr (sR .A .H rfl))))
      (prodSet_sep (dL := 5) (dR := 5) (Or.inl (sL .D .A rfl)))).disjoint
  have hB : R10.P .B = prodSet (baseR5.P .B) (baseR5.P .B) ∪ prodSet (baseR5.P .H) (baseR5.P .D) ∪
      prodSet (baseR5.P .V) (baseR5.P .A) ∪ prodSet (baseR5.P .D) (baseR5.P .V) ∪
      prodSet (baseR5.P .A) (baseR5.P .H) := by
    simp only [R10_def, s2aProd, Realisation.mapIso, s2aFam, Finset.map_union, prodSet_def]
  rw [hB]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12345)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h1234)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h123)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T10_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T5_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T5_pi_iso T5_pi_iso A B
  rw [hm, hm, hm, hm, hm, baseR5_P_eq.1, baseR5_P_eq.2.2.2.2.2.1, baseR5_P_eq.2.2.2.1,
      baseR5_P_eq.2.2.2.2.2.2, baseR5_P_eq.2.2.1]
  rw [piSet5_map_T5 tTB5_map_ok tTB5_card_eq,
      piSet5_map_T5 tTPH5_map_ok tTPH5_card_eq,
      piSet5_map_T5 tTXH5_map_ok tTXH5_card_eq,
      piSet5_map_T5 tTPV5_map_ok tTPV5_card_eq,
      piSet5_map_T5 tTXV5_map_ok tTXV5_card_eq]
  rw [← eval_dist10_16_hist_pi, ← eval_dist10_16_hist_pi, ← eval_dist10_16_hist_pi,
      ← eval_dist10_16_hist_pi, ← eval_dist10_16_hist_pi]
  rw [h_tTB5_eq, h_tTPH5_eq, h_tTXH5_eq, h_tTPV5_eq, h_tTXV5_eq]
  have hr : vec16Eval d16_TB_val g =
      vec16Eval (dist10_16_hist h_tTB5 h_tTB5) g + vec16Eval (dist10_16_hist h_tTPH5 h_tTXH5) g +
      vec16Eval (dist10_16_hist h_tTPV5 h_tTXV5) g + vec16Eval (dist10_16_hist h_tTXH5 h_tTPV5) g +
      vec16Eval (dist10_16_hist h_tTXV5 h_tTPH5) g := by
    rw [← d16_TB_val_eq]; simp only [vec16Eval_add]; omega
  rw [hr]

theorem sum_T10_P_O (g : Nat → Nat) :
    ∑ z ∈ (R10.P .O).map T10_pi_iso.toEquiv.toEmbedding, g (sig10Pi z) = vec16Eval d16_TS_val g := by
  have h12 : Disjoint (prodSet (baseR5.P .O) (baseR5.P .N)) (prodSet (baseR5.P .N) (baseR5.P .O)) :=
    (prodSet_sep (dL := 5) (dR := 5) (Or.inl (baseR5.hsep .O .N rfl))).disjoint
  have hO : R10.P .O = prodSet (baseR5.P .O) (baseR5.P .N) ∪ prodSet (baseR5.P .N) (baseR5.P .O) := by
    simp only [R10_def, s2aProd, Realisation.mapIso, s2aFam, Finset.map_union, prodSet_def]
  rw [hO, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T10_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T5_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T5_pi_iso T5_pi_iso A B
  rw [hm, hm, baseR5_P_eq.2.2.2.2.1, baseR5_P_eq.2.1]
  rw [piSet5_map_T5 tTS5_map_ok tTS5_card_eq, piSet5_map_T5 tTX05_map_ok tTX05_card_eq]
  rw [← eval_dist10_16_hist_pi, ← eval_dist10_16_hist_pi, h_tTS5_eq, h_tTX05_eq, ← vec16Eval_add, d16_TS_val_eq]

theorem sum_T10_P_H (g : Nat → Nat) :
    ∑ z ∈ (R10.P .H).map T10_pi_iso.toEquiv.toEmbedding, g (sig10Pi z) = vec16Eval d16_TPH_val g := by
  have h12 : Disjoint (prodSet (baseR5.P .H) (baseR5.P .N)) (prodSet (baseR5.P .N) (baseR5.P .V)) :=
    (prodSet_sep (dL := 5) (dR := 5) (Or.inl (baseR5.hsep .H .N rfl))).disjoint
  have hH : R10.P .H = prodSet (baseR5.P .H) (baseR5.P .N) ∪ prodSet (baseR5.P .N) (baseR5.P .V) := by
    simp only [R10_def, s2aProd, Realisation.mapIso, s2aFam, Finset.map_union, prodSet_def]
  rw [hH, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T10_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T5_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T5_pi_iso T5_pi_iso A B
  rw [hm, hm, baseR5_P_eq.2.2.2.2.2.1, baseR5_P_eq.2.1, baseR5_P_eq.2.2.2.2.2.2]
  rw [piSet5_map_T5 tTPH5_map_ok tTPH5_card_eq, piSet5_map_T5 tTX05_map_ok tTX05_card_eq,
      piSet5_map_T5 tTPV5_map_ok tTPV5_card_eq]
  rw [← eval_dist10_16_hist_pi, ← eval_dist10_16_hist_pi, h_tTPH5_eq, h_tTX05_eq, h_tTPV5_eq,
      ← vec16Eval_add, d16_TPH_val_eq]

theorem sum_T10_P_V (g : Nat → Nat) :
    ∑ z ∈ (R10.P .V).map T10_pi_iso.toEquiv.toEmbedding, g (sig10Pi z) = vec16Eval d16_TPV_val g := by
  have h12 : Disjoint (prodSet (baseR5.P .V) (baseR5.P .N)) (prodSet (baseR5.P .N) (baseR5.P .H)) :=
    (prodSet_sep (dL := 5) (dR := 5) (Or.inl (baseR5.hsep .V .N rfl))).disjoint
  have hV : R10.P .V = prodSet (baseR5.P .V) (baseR5.P .N) ∪ prodSet (baseR5.P .N) (baseR5.P .H) := by
    simp only [R10_def, s2aProd, Realisation.mapIso, s2aFam, Finset.map_union, prodSet_def]
  rw [hV, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T10_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T5_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T5_pi_iso T5_pi_iso A B
  rw [hm, hm, baseR5_P_eq.2.2.2.2.2.2, baseR5_P_eq.2.1, baseR5_P_eq.2.2.2.2.2.1]
  rw [piSet5_map_T5 tTPV5_map_ok tTPV5_card_eq, piSet5_map_T5 tTX05_map_ok tTX05_card_eq,
      piSet5_map_T5 tTPH5_map_ok tTPH5_card_eq]
  rw [← eval_dist10_16_hist_pi, ← eval_dist10_16_hist_pi, h_tTPV5_eq, h_tTX05_eq, h_tTPH5_eq,
      ← vec16Eval_add, d16_TPV_val_eq]

theorem sum_T10_P_N (g : Nat → Nat) :
    ∑ z ∈ (R10.P .N).map T10_pi_iso.toEquiv.toEmbedding, g (sig10Pi z) = vec16Eval d16_TX0_val g := by
  have hdisj : Disjoint (prodSet (piSet5 tX05) (piSet5 tX05)) (prodSet (piSet5 tX15) (piSet5 tX15)) := by
    apply prodSet_disjoint (dL := 5) (dR := 5); left
    rw [piSet5_X15_eq, Finset.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · have := (baseR5.hsep .N .A rfl).disjoint; rw [baseR5_P_eq.2.1, baseR5_P_eq.2.2.1] at this; exact this
    · have := (baseR5.hsep .N .D rfl).disjoint; rw [baseR5_P_eq.2.1, baseR5_P_eq.2.2.2.1] at this; exact this
  rw [R10_N_eq_X0_10, X0_10, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact hdisj)]
  have hm : ∀ A B, (prodSet A B).map T10_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T5_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T5_pi_iso T5_pi_iso A B
  rw [hm, hm, piSet5_map_T5 tTX05_map_ok tTX05_card_eq, piSet5_map_T5 tTX15_map_ok tTX15_card_eq]
  rw [← eval_dist10_16_hist_pi, ← eval_dist10_16_hist_pi, h_tTX05_eq, h_tTX15_eq, ← vec16Eval_add, d16_TX0_val_eq]

theorem sum_T10_P_D (g : Nat → Nat) :
    ∑ z ∈ (R10.P .D).map T10_pi_iso.toEquiv.toEmbedding, g (sig10Pi z) = vec16Eval d16_TXH_val g := by
  have h12 : Disjoint (prodSet (baseR5.P .D) (baseR5.P .N)) (prodSet (baseR5.P .N) (baseR5.P .A)) :=
    (prodSet_sep (dL := 5) (dR := 5) (Or.inl (baseR5.hsep .D .N rfl))).disjoint
  have hD : R10.P .D = prodSet (baseR5.P .D) (baseR5.P .N) ∪ prodSet (baseR5.P .N) (baseR5.P .A) := by
    simp only [R10_def, s2aProd, Realisation.mapIso, s2aFam, Finset.map_union, prodSet_def]
  rw [hD, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T10_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T5_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T5_pi_iso T5_pi_iso A B
  rw [hm, hm, baseR5_P_eq.2.2.2.1, baseR5_P_eq.2.1, baseR5_P_eq.2.2.1]
  rw [piSet5_map_T5 tTXH5_map_ok tTXH5_card_eq, piSet5_map_T5 tTX05_map_ok tTX05_card_eq,
      piSet5_map_T5 tTXV5_map_ok tTXV5_card_eq]
  rw [← eval_dist10_16_hist_pi, ← eval_dist10_16_hist_pi, h_tTXH5_eq, h_tTX05_eq, h_tTXV5_eq,
      ← vec16Eval_add, d16_TXH_val_eq]

theorem sum_T10_P_A (g : Nat → Nat) :
    ∑ z ∈ (R10.P .A).map T10_pi_iso.toEquiv.toEmbedding, g (sig10Pi z) = vec16Eval d16_TXV_val g := by
  have h12 : Disjoint (prodSet (baseR5.P .A) (baseR5.P .N)) (prodSet (baseR5.P .N) (baseR5.P .D)) :=
    (prodSet_sep (dL := 5) (dR := 5) (Or.inl (baseR5.hsep .A .N rfl))).disjoint
  have hA : R10.P .A = prodSet (baseR5.P .A) (baseR5.P .N) ∪ prodSet (baseR5.P .N) (baseR5.P .D) := by
    simp only [R10_def, s2aProd, Realisation.mapIso, s2aFam, Finset.map_union, prodSet_def]
  rw [hA, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T10_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T5_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T5_pi_iso T5_pi_iso A B
  rw [hm, hm, baseR5_P_eq.2.2.1, baseR5_P_eq.2.1, baseR5_P_eq.2.2.2.1]
  rw [piSet5_map_T5 tTXV5_map_ok tTXV5_card_eq, piSet5_map_T5 tTX05_map_ok tTX05_card_eq,
      piSet5_map_T5 tTXH5_map_ok tTXH5_card_eq]
  rw [← eval_dist10_16_hist_pi, ← eval_dist10_16_hist_pi, h_tTXV5_eq, h_tTX05_eq, h_tTXH5_eq,
      ← vec16Eval_add, d16_TXV_val_eq]

-- Concrete 15D Realisations and J15
@[irreducible] def inp10 : HetLeftInput R10 :=
  HetLeftInput.ofSiblingAndParts R10 R10 rfl rfl rfl
    J10_out J10_in J10_out J10_in
    J10_out_indep J10_in_indep J10_out_sep_in J10_out_sep_R10N
    J10_out_indep J10_in_indep J10_out_sep_in J10_out_sep_R10N

theorem inp10_def : inp10 = HetLeftInput.ofSiblingAndParts R10 R10 rfl rfl rfl
    J10_out J10_in J10_out J10_in
    J10_out_indep J10_in_indep J10_out_sep_in J10_out_sep_R10N
    J10_out_indep J10_in_indep J10_out_sep_in J10_out_sep_R10N := by
  unfold inp10; rfl

@[irreducible] def R15_het : Realisation Letter Letter.sep (strongPowPi C7 15) :=
  R10.hetGao baseR5 inp10

theorem R15_het_def : R15_het = R10.hetGao baseR5 inp10 := by unfold R15_het; rfl

theorem R15_het_w :
    R15_het.w .B = 46990439 ∧ R15_het.w .N = 35275258 ∧ R15_het.w .A = 7454670 ∧
    R15_het.w .D = 6703815 ∧ R15_het.w .O = 2504616 ∧ R15_het.w .H = 2504616 ∧ R15_het.w .V = 2504616 := by
  rw [R15_het_def]
  have hw := w_hetGao R10 baseR5 inp10
  have h10N : inp10.J0_N.card = 105709 := by rw [inp10_def]; exact R10_w.2.1
  have h10A : inp10.J0_A.card = 14490 := by rw [inp10_def]; exact R10_w.2.2.1
  have h10D : inp10.J0_D.card = 14490 := by rw [inp10_def]; exact R10_w.2.2.2.1
  have hJo : inp10.JH_out.card = 27488 := by rw [inp10_def]; exact J10_out_card
  have hJi : inp10.JH_in.card = 107265 := by rw [inp10_def]; exact J10_in_card
  have hJVo : inp10.JV_out.card = 27488 := by rw [inp10_def]; exact J10_out_card
  have hJVi : inp10.JV_in.card = 107265 := by rw [inp10_def]; exact J10_in_card
  rcases R10_w with ⟨lB, lN, lA, lD, lO, lH, lV⟩
  rcases baseR5_w with ⟨rB, rN, rA, rD, rO, rH, rV⟩
  rw [h10N, h10A, h10D, hJo, hJi, hJVo, hJVi, lB, lN, lA, lD, lO, lH, lV, rB, rN, rA, rD, rO, rH, rV] at hw
  exact hw

@[irreducible] def R15_AX : Realisation Letter Letter.sep (strongPowPi C7 15) :=
  s2aProd R10A baseR5

theorem R15_AX_def : R15_AX = s2aProd R10A baseR5 := by unfold R15_AX; rfl

theorem R15_AX_w :
    R15_AX.w .B = 46990439 ∧ R15_AX.w .N = 35342398 ∧ R15_AX.w .A = 8140002 ∧
    R15_AX.w .D = 5948463 ∧ R15_AX.w .O = 2504616 ∧ R15_AX.w .H = 2504616 ∧ R15_AX.w .V = 2504616 := by
  rw [R15_AX_def]
  have hw := w_s2aProd R10A baseR5
  rcases R10A_w with ⟨lB, lN, lA, lD, lO, lH, lV⟩
  rcases baseR5_w with ⟨rB, rN, rA, rD, rO, rH, rV⟩
  rw [lB, lN, lA, lD, lO, lH, lV, rB, rN, rA, rD, rO, rH, rV] at hw
  exact hw

private theorem J10_out_sep_R10AN : Sep (strongPowPi C7 10) J10_out (R10A.P .N) :=
  R10A_N_eq_R10_N ▸ J10_out_sep_R10N

private theorem R10A_AD_indep : (strongPowPi C7 10).IsIndepSet ((R10A.P .A ∪ R10A.P .D : Finset (Fin 10 → ZMod 7)) : Set (Fin 10 → ZMod 7)) :=
  isIndepSet_union_of_sep (R10A.hindep .A) (R10A.hindep .D) (R10A.hsep .A .D rfl)

private theorem R10A_AD_sep_N : Sep (strongPowPi C7 10) (R10A.P .A ∪ R10A.P .D) (R10A.P .N) :=
  Sep.union_left (R10A.hsep .A .N rfl) (R10A.hsep .D .N rfl)

@[irreducible] def inp10A : HetLeftInput R10A :=
  HetLeftInput.ofSiblingAndParts R10A R10A rfl rfl rfl
    J10_out J10_in (R10A.P .A ∪ R10A.P .D) (R10A.P .N)
    J10_out_indep J10_in_indep J10_out_sep_in J10_out_sep_R10AN
    R10A_AD_indep (R10A.hindep .N) R10A_AD_sep_N R10A_AD_sep_N

theorem inp10A_fields :
    inp10A.J0_N = R10A.P .N ∧ inp10A.J0_A = R10A.P .A ∧ inp10A.J0_D = R10A.P .D ∧
    inp10A.JH_out = J10_out ∧ inp10A.JH_in = J10_in ∧
    inp10A.JV_out = R10A.P .A ∪ R10A.P .D ∧ inp10A.JV_in = R10A.P .N := by
  unfold inp10A; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[irreducible] def R15_Ahet : Realisation Letter Letter.sep (strongPowPi C7 15) :=
  R10A.hetGao baseR5 inp10A

theorem R15_Ahet_def : R15_Ahet = R10A.hetGao baseR5 inp10A := by unfold R15_Ahet; rfl

theorem R15_Ahet_w :
    R15_Ahet.w .B = 46990439 ∧ R15_Ahet.w .N = 35303606 ∧ R15_Ahet.w .A = 8180458 ∧
    R15_Ahet.w .D = 5948463 ∧ R15_Ahet.w .O = 2504616 ∧ R15_Ahet.w .H = 2504616 ∧ R15_Ahet.w .V = 2504616 := by
  rw [R15_Ahet_def]
  have hw := w_hetGao R10A baseR5 inp10A
  rcases inp10A_fields with ⟨fN, fA, fD, fHo, fHi, fVo, fVi⟩
  have h10N : inp10A.J0_N.card = 105709 := by rw [fN]; exact R10A_w.2.1
  have h10A : inp10A.J0_A.card = 16744 := by rw [fA]; exact R10A_w.2.2.1
  have h10D : inp10A.J0_D.card = 12236 := by rw [fD]; exact R10A_w.2.2.2.1
  have hJo : inp10A.JH_out.card = 27488 := by rw [fHo]; exact J10_out_card
  have hJi : inp10A.JH_in.card = 107265 := by rw [fHi]; exact J10_in_card
  have hJVo : inp10A.JV_out.card = 28980 := by
    rw [fVo, Finset.card_union_of_disjoint (R10A.hsep .A .D rfl).disjoint, ← Realisation.w, ← Realisation.w,
        R10A_w.2.2.1, R10A_w.2.2.2.1]
  have hJVi : inp10A.JV_in.card = 105709 := by rw [fVi]; exact R10A_w.2.1
  rcases R10A_w with ⟨lB, lN, lA, lD, lO, lH, lV⟩
  rcases baseR5_w with ⟨rB, rN, rA, rD, rO, rH, rV⟩
  rw [h10N, h10A, h10D, hJo, hJi, hJVo, hJVi, lB, lN, lA, lD, lO, lH, lV, rB, rN, rA, rD, rO, rH, rV] at hw
  exact hw

theorem R15_AX_N_eq :
    R15_AX.P .N = prodSet X0_10 (piSet5 tX05) ∪ prodSet X1_10 (piSet5 tX15) := by
  rw [R15_AX_def, (R10_P_map_prodSet R10A baseR5).1, R10A_N_eq_R10_N, R10_N_eq_X0_10,
      R10A_AD_eq, R10_AD_eq_X1_10, baseR5_P_eq.2.1, baseR5_P_eq.2.2.1, baseR5_P_eq.2.2.2.1, ← piSet5_X15_eq]

theorem R15_AX_AD_eq :
    R15_AX.P .A ∪ R15_AX.P .D = prodSet X1_10 (piSet5 tX05) ∪ prodSet X0_10 (piSet5 tX15) := by
  rw [R15_AX_def, (R10_P_map_prodSet R10A baseR5).2.1, (R10_P_map_prodSet R10A baseR5).2.2,
      R10A_N_eq_R10_N, R10_N_eq_X0_10, baseR5_P_eq.2.1, baseR5_P_eq.2.2.1, baseR5_P_eq.2.2.2.1]
  have hu : prodSet (R10A.P .A) (piSet5 tX05) ∪ prodSet X0_10 (piSet5 tXH5) ∪
      (prodSet (R10A.P .D) (piSet5 tX05) ∪ prodSet X0_10 (piSet5 tXV5)) =
      (prodSet (R10A.P .A) (piSet5 tX05) ∪ prodSet (R10A.P .D) (piSet5 tX05)) ∪
      (prodSet X0_10 (piSet5 tXV5) ∪ prodSet X0_10 (piSet5 tXH5)) := by
    ext z; simp only [Finset.mem_union]
    constructor
    · rintro ((h | h) | (h | h))
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
    · rintro ((h | h) | (h | h))
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inr h)
  rw [hu, ← prodSet_union_left, ← prodSet_union_right, R10A_AD_eq, R10_AD_eq_X1_10, ← piSet5_X15_eq]

@[irreducible] def J15 : Finset (Fin 15 → ZMod 7) :=
  (R15_het.P .B ∪ R15_het.P .O).map T15_pi_iso.toEquiv.toEmbedding

theorem J15_def : J15 = (R15_het.P .B ∪ R15_het.P .O).map T15_pi_iso.toEquiv.toEmbedding := by
  unfold J15; rfl

theorem J15_indep : (strongPowPi C7 15).IsIndepSet (J15 : Set (Fin 15 → ZMod 7)) := by
  have hi : (strongPowPi C7 15).IsIndepSet ((R15_het.P .B ∪ R15_het.P .O : Finset (Fin 15 → ZMod 7)) : Set (Fin 15 → ZMod 7)) :=
    isIndepSet_union_of_sep (R15_het.hindep .B) (R15_het.hindep .O) (R15_het.hsep .B .O rfl)
  intro x hx y hy hne hadj
  rw [J15_def] at hx hy
  rcases Finset.mem_map.mp (Finset.mem_coe.mp hx) with ⟨x', hx', rfl⟩
  rcases Finset.mem_map.mp (Finset.mem_coe.mp hy) with ⟨y', hy', rfl⟩
  exact hi hx' hy' (fun h => hne (congrArg T15_pi_iso h)) ((T15_pi_iso.map_rel_iff).mp hadj)

theorem J15_card : J15.card = 49495055 := by
  rw [J15_def, Finset.card_map, Finset.card_union_of_disjoint (R15_het.hsep .B .O rfl).disjoint,
      ← Realisation.w, ← Realisation.w, R15_het_w.1, R15_het_w.2.2.2.2.1]

noncomputable def J15_out : Finset (Fin 15 → ZMod 7) :=
  J15.filter (fun w => ¬ inNbr (strongPowPi C7 15) (R15_AX.P .N) w)

noncomputable def J15_in : Finset (Fin 15 → ZMod 7) :=
  J15 \ J15_out

theorem J15_out_indep : (strongPowPi C7 15).IsIndepSet (J15_out : Set (Fin 15 → ZMod 7)) :=
  isIndepSet_subset J15_indep (Finset.filter_subset _ J15)

theorem J15_in_indep : (strongPowPi C7 15).IsIndepSet (J15_in : Set (Fin 15 → ZMod 7)) :=
  isIndepSet_subset J15_indep Finset.sdiff_subset

theorem J15_out_sep_in : Sep (strongPowPi C7 15) J15_out J15_in :=
  fun _ hx _ hy hc => isIndepSet_not_close_of_ne J15_indep (Finset.filter_subset _ J15 hx)
    (Finset.mem_sdiff.mp hy).1 (fun h => (Finset.mem_sdiff.mp hy).2 (h ▸ hx)) hc

theorem J15_out_sep_R15N : Sep (strongPowPi C7 15) J15_out (R15_AX.P .N) := by
  rw [sep_iff_not_inNbr]
  intro w hw
  exact (Finset.mem_filter.mp hw).2

theorem countAvoid15_eq_vec16 (d16 d5t : Vec16)
    (h0 : d5t.v8 = 0 ∧ d5t.v9 = 0 ∧ d5t.v10 = 0 ∧ d5t.v11 = 0 ∧ d5t.v12 = 0 ∧ d5t.v13 = 0 ∧ d5t.v14 = 0 ∧ d5t.v15 = 0) :
    countAvoid15 d16 d5t = vec16Eval d16 (fun s10 => vec16Eval d5t (fun s5 =>
      if (((((s10 >>> 3) &&& 1) &&& ((s5 >>> 2) &&& 1)) |||
           (((s10 >>> 2) &&& 1) &&& (((s5 >>> 1) ||| s5) &&& 1))) == 0) then 1 else 0)) := by
  rw [countAvoid15_eq]
  congr 1; ext s10
  rw [vec16Eval_eq_sum]
  have hs : ∑ i ∈ Finset.range 16, Vec16.get d5t i *
      (if (((((s10 >>> 3) &&& 1) &&& ((i >>> 2) &&& 1)) |||
            (((s10 >>> 2) &&& 1) &&& (((i >>> 1) ||| i) &&& 1))) == 0) then 1 else 0) =
      ∑ s5 : Fin 8, Vec16.get d5t s5.val *
      (if (((((s10 >>> 3) &&& 1) &&& ((s5.val >>> 2) &&& 1)) |||
            (((s10 >>> 2) &&& 1) &&& (((s5.val >>> 1) ||| s5.val) &&& 1))) == 0) then 1 else 0) := by
    have hv3 : (3 : Fin 8).val = 3 := rfl
    have hv4 : (4 : Fin 8).val = 4 := rfl
    have hv5 : (5 : Fin 8).val = 5 := rfl
    have hv6 : (6 : Fin 8).val = 6 := rfl
    have hv7 : (7 : Fin 8).val = 7 := rfl
    rw [Fin.sum_univ_eight, Fin.val_zero, Fin.val_one, Fin.val_two, hv3, hv4, hv5, hv6, hv7]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    rcases h0 with ⟨h8, h9, h10, h11, h12, h13, h14, h15⟩
    dsimp only [Vec16.get]
    rw [h8, h9, h10, h11, h12, h13, h14, h15]
    simp only [zero_mul, add_zero]
  exact hs.symm

private theorem avoid15_bit_eq (a3 a2 a1 a0 b2 b1 b0 : Prop)
    [Decidable a3] [Decidable a2] [Decidable a1] [Decidable a0] [Decidable b2] [Decidable b1] [Decidable b0] :
    (if ((((((if a3 then 8 else 0) + (if a2 then 4 else 0) + (if a1 then 2 else 0) + (if a0 then 1 else 0)) >>> 3) &&& 1) &&&
           ((((if b2 then 4 else 0) + (if b1 then 2 else 0) + (if b0 then 1 else 0)) >>> 2) &&& 1)) |||
          (((((if a3 then 8 else 0) + (if a2 then 4 else 0) + (if a1 then 2 else 0) + (if a0 then 1 else 0)) >>> 2) &&& 1) &&&
           (((((if b2 then 4 else 0) + (if b1 then 2 else 0) + (if b0 then 1 else 0)) >>> 1) |||
             ((if b2 then 4 else 0) + (if b1 then 2 else 0) + (if b0 then 1 else 0))) &&& 1))) == 0
     then 1 else 0) =
    if ¬ ((a3 ∧ b2) ∨ (a2 ∧ (b0 ∨ b1))) then 1 else 0 := by
  by_cases a3 <;> by_cases a2 <;> by_cases a1 <;> by_cases a0 <;>
  by_cases b2 <;> by_cases b1 <;> by_cases b0 <;> simp [*]

theorem R15_het_P_B_O_eq :
    R15_het.P .B = prodSet (R10.P .B) (baseR5.P .B) ∪ prodSet (R10.P .H) (baseR5.P .D) ∪
      prodSet (R10.P .V) (baseR5.P .A) ∪ prodSet (R10.P .D) (baseR5.P .V) ∪
      prodSet (R10.P .A) (baseR5.P .H) ∧
    R15_het.P .O = prodSet (R10.P .O) (baseR5.P .N) ∪ prodSet (R10.P .N) (baseR5.P .O) := by
  constructor <;> simp only [R15_het_def, Realisation.hetGao, Realisation.mapIso, Realisation.hetGao2, hetGaoFam, Finset.map_union, prodSet_def]

theorem J15_out_card : J15_out.card = 12839823 := by
  rw [J15_out, Finset.card_filter]
  have sL := R10.hsep
  have sR := baseR5.hsep
  have h12 : Disjoint (prodSet (R10.P .B) (baseR5.P .B)) (prodSet (R10.P .H) (baseR5.P .D)) :=
    (prodSet_sep (dL := 10) (dR := 5) (Or.inl (sL .B .H rfl))).disjoint
  have h123 : Disjoint (prodSet (R10.P .B) (baseR5.P .B) ∪ prodSet (R10.P .H) (baseR5.P .D))
      (prodSet (R10.P .V) (baseR5.P .A)) :=
    (Sep.union_left (prodSet_sep (dL := 10) (dR := 5) (Or.inl (sL .B .V rfl)))
      (prodSet_sep (dL := 10) (dR := 5) (Or.inr (sR .D .A rfl)))).disjoint
  have h1234 : Disjoint ((prodSet (R10.P .B) (baseR5.P .B) ∪ prodSet (R10.P .H) (baseR5.P .D)) ∪
      prodSet (R10.P .V) (baseR5.P .A)) (prodSet (R10.P .D) (baseR5.P .V)) :=
    (Sep.union_left (Sep.union_left (prodSet_sep (dL := 10) (dR := 5) (Or.inr (sR .B .V rfl)))
      (prodSet_sep (dL := 10) (dR := 5) (Or.inr (sR .D .V rfl))))
      (prodSet_sep (dL := 10) (dR := 5) (Or.inl (sL .V .D rfl)))).disjoint
  have h12345 : Disjoint (((prodSet (R10.P .B) (baseR5.P .B) ∪ prodSet (R10.P .H) (baseR5.P .D)) ∪
      prodSet (R10.P .V) (baseR5.P .A)) ∪ prodSet (R10.P .D) (baseR5.P .V))
      (prodSet (R10.P .A) (baseR5.P .H)) :=
    (Sep.union_left (Sep.union_left (Sep.union_left
      (prodSet_sep (dL := 10) (dR := 5) (Or.inr (sR .B .H rfl)))
      (prodSet_sep (dL := 10) (dR := 5) (Or.inl (sL .H .A rfl))))
      (prodSet_sep (dL := 10) (dR := 5) (Or.inr (sR .A .H rfl))))
      (prodSet_sep (dL := 10) (dR := 5) (Or.inl (sL .D .A rfl)))).disjoint
  have hO12 : Disjoint (prodSet (R10.P .O) (baseR5.P .N)) (prodSet (R10.P .N) (baseR5.P .O)) :=
    (prodSet_sep (dL := 10) (dR := 5) (Or.inl (sL .O .N rfl))).disjoint
  have hBO : Disjoint (R15_het.P .B) (R15_het.P .O) := (R15_het.hsep .B .O rfl).disjoint
  rw [J15_def, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact hBO)]
  rw [R15_het_P_B_O_eq.1, R15_het_P_B_O_eq.2]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12345)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h1234)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h123)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact hO12)]
  have hm : ∀ A B, (prodSet A B).map T15_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T10_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T10_pi_iso T5_pi_iso A B
  rw [hm, hm, hm, hm, hm, hm, hm,
      baseR5_P_eq.1, baseR5_P_eq.2.2.2.1, baseR5_P_eq.2.2.1, baseR5_P_eq.2.2.2.2.2.2,
      baseR5_P_eq.2.2.2.2.2.1, baseR5_P_eq.2.1, baseR5_P_eq.2.2.2.2.1]
  rw [piSet5_map_T5 tTB5_map_ok tTB5_card_eq,
      piSet5_map_T5 tTXH5_map_ok tTXH5_card_eq,
      piSet5_map_T5 tTXV5_map_ok tTXV5_card_eq,
      piSet5_map_T5 tTPV5_map_ok tTPV5_card_eq,
      piSet5_map_T5 tTPH5_map_ok tTPH5_card_eq,
      piSet5_map_T5 tTX05_map_ok tTX05_card_eq,
      piSet5_map_T5 tTS5_map_ok tTS5_card_eq]
  let f15 : (Fin 15 → ZMod 7) → Nat := fun w => if ¬ inNbr (strongPowPi C7 15) (R15_AX.P .N) w then 1 else 0
  have hprod_sum : ∀ (A : Finset (Fin 10 → ZMod 7)) (B : Finset (Fin 5 → ZMod 7)),
      (∑ w ∈ prodSet A B, f15 w) =
        ∑ z ∈ A, ∑ x ∈ B,
          (if (((((sig10Pi z >>> 3) &&& 1) &&& ((sig5_3Pi x >>> 2) &&& 1)) |||
                (((sig10Pi z >>> 2) &&& 1) &&& (((sig5_3Pi x >>> 1) ||| sig5_3Pi x) &&& 1))) == 0) then 1 else 0) := by
    intro A B
    rw [prodSet_def, Finset.sum_map, Finset.sum_product]
    apply Finset.sum_congr rfl; intro z _
    apply Finset.sum_congr rfl; intro x _
    dsimp only [f15]
    have hin : inNbr (strongPowPi C7 15) (R15_AX.P .N) (strongProdIsoAdd C7 10 5 (z, x)) ↔
        (inNbr (strongPowPi C7 10) X0_10 z ∧ inNbr (strongPowPi C7 5) (piSet5 tX05) x) ∨
        (inNbr (strongPowPi C7 10) X1_10 z ∧
          (inNbr (strongPowPi C7 5) (piSet5 tXV5) x ∨ inNbr (strongPowPi C7 5) (piSet5 tXH5) x)) := by
      rw [R15_AX_N_eq, inNbr_union, inNbr_prodSet (dL := 10) (dR := 5), inNbr_prodSet (dL := 10) (dR := 5),
          piSet5_X15_eq, inNbr_union]
    change (if ¬ inNbr (strongPowPi C7 15) (R15_AX.P .N) (strongProdIsoAdd C7 10 5 (z, x)) then 1 else 0) = _
    simp only [hin, sig10Pi, sig5_3Pi]
    exact (avoid15_bit_eq _ _ _ _ _ _ _).symm
  change (∑ w ∈ prodSet ((R10.P .B).map T10_pi_iso.toEquiv.toEmbedding) (piSet5 tTB5), f15 w) +
         (∑ w ∈ prodSet ((R10.P .H).map T10_pi_iso.toEquiv.toEmbedding) (piSet5 tTXH5), f15 w) +
         (∑ w ∈ prodSet ((R10.P .V).map T10_pi_iso.toEquiv.toEmbedding) (piSet5 tTXV5), f15 w) +
         (∑ w ∈ prodSet ((R10.P .D).map T10_pi_iso.toEquiv.toEmbedding) (piSet5 tTPV5), f15 w) +
         (∑ w ∈ prodSet ((R10.P .A).map T10_pi_iso.toEquiv.toEmbedding) (piSet5 tTPH5), f15 w) +
        ((∑ w ∈ prodSet ((R10.P .O).map T10_pi_iso.toEquiv.toEmbedding) (piSet5 tTX05), f15 w) +
         (∑ w ∈ prodSet ((R10.P .N).map T10_pi_iso.toEquiv.toEmbedding) (piSet5 tTS5), f15 w)) = 12839823
  rw [hprod_sum, hprod_sum, hprod_sum, hprod_sum, hprod_sum, hprod_sum, hprod_sum]
  have h5g : ∀ (t : Trie7 5) (z : Fin 10 → ZMod 7),
      (∑ x ∈ piSet5 t,
        (if (((((sig10Pi z >>> 3) &&& 1) &&& ((sig5_3Pi x >>> 2) &&& 1)) |||
              (((sig10Pi z >>> 2) &&& 1) &&& (((sig5_3Pi x >>> 1) ||| sig5_3Pi x) &&& 1))) == 0) then 1 else 0)) =
      vec16Eval (dist5_3List t) (fun s5 =>
        (if (((((sig10Pi z >>> 3) &&& 1) &&& ((s5 >>> 2) &&& 1)) |||
              (((sig10Pi z >>> 2) &&& 1) &&& (((s5 >>> 1) ||| s5) &&& 1))) == 0) then 1 else 0)) :=
    fun t z => (eval_dist5_3List_pi t (fun s5 =>
      if (((((sig10Pi z >>> 3) &&& 1) &&& ((s5 >>> 2) &&& 1)) |||
            (((sig10Pi z >>> 2) &&& 1) &&& (((s5 >>> 1) ||| s5) &&& 1))) == 0) then 1 else 0)).symm
  simp_rw [h5g]
  rw [d5_TB5_val_eq, d5_TXH5_val_eq, d5_TXV5_val_eq, d5_TPV5_val_eq, d5_TPH5_val_eq, d5_TX05_val_eq, d5_TS5_val_eq]
  let g15 (d5 : Vec16) (s10 : Nat) : Nat := vec16Eval d5 (fun s5 =>
    if (((((s10 >>> 3) &&& 1) &&& ((s5 >>> 2) &&& 1)) |||
          (((s10 >>> 2) &&& 1) &&& (((s5 >>> 1) ||| s5) &&& 1))) == 0) then 1 else 0)
  change (∑ z ∈ (R10.P .B).map T10_pi_iso.toEquiv.toEmbedding, g15 d5_TB5_val (sig10Pi z)) +
         (∑ z ∈ (R10.P .H).map T10_pi_iso.toEquiv.toEmbedding, g15 d5_TXH5_val (sig10Pi z)) +
         (∑ z ∈ (R10.P .V).map T10_pi_iso.toEquiv.toEmbedding, g15 d5_TXV5_val (sig10Pi z)) +
         (∑ z ∈ (R10.P .D).map T10_pi_iso.toEquiv.toEmbedding, g15 d5_TPV5_val (sig10Pi z)) +
         (∑ z ∈ (R10.P .A).map T10_pi_iso.toEquiv.toEmbedding, g15 d5_TPH5_val (sig10Pi z)) +
        ((∑ z ∈ (R10.P .O).map T10_pi_iso.toEquiv.toEmbedding, g15 d5_TX05_val (sig10Pi z)) +
         (∑ z ∈ (R10.P .N).map T10_pi_iso.toEquiv.toEmbedding, g15 d5_TS5_val (sig10Pi z))) = 12839823
  rw [sum_T10_P_B (g15 d5_TB5_val), sum_T10_P_H (g15 d5_TXH5_val), sum_T10_P_V (g15 d5_TXV5_val),
      sum_T10_P_D (g15 d5_TPV5_val), sum_T10_P_A (g15 d5_TPH5_val), sum_T10_P_O (g15 d5_TX05_val),
      sum_T10_P_N (g15 d5_TS5_val)]
  dsimp only [g15]
  rw [← countAvoid15_eq_vec16 d16_TB_val d5_TB5_val ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ← countAvoid15_eq_vec16 d16_TPH_val d5_TXH5_val ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ← countAvoid15_eq_vec16 d16_TPV_val d5_TXV5_val ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ← countAvoid15_eq_vec16 d16_TXH_val d5_TPV5_val ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ← countAvoid15_eq_vec16 d16_TXV_val d5_TPH5_val ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ← countAvoid15_eq_vec16 d16_TS_val d5_TX05_val ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ← countAvoid15_eq_vec16 d16_TX0_val d5_TS5_val ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩]
  rw [c2_0_val_eq, c2_2_val_eq, c2_3_val_eq, c2_5_val_eq, c2_6_val_eq, c2_1_val_eq, c2_4_val_eq]
  rw [← c2_exact_val_eq]; omega

theorem J15_in_card : J15_in.card = 36655232 := by
  rw [J15_in, Finset.card_sdiff_of_subset (by rw [J15_out]; exact Finset.filter_subset _ J15), J15_card, J15_out_card]

end SigBridgeAndC2

section SigBridge15AndC4

open scoped Classical

theorem R15_Ahet_OHV_eq :
    R15_Ahet.P .O = R15_AX.P .O ∧ R15_Ahet.P .H = R15_AX.P .H ∧ R15_Ahet.P .V = R15_AX.P .V := by
  rw [R15_Ahet_def, R15_AX_def]
  exact ⟨rfl, rfl, rfl⟩

theorem R15_Ahet_sigma_N_eq :
    R15_Ahet.sigma.P .N =
      prodSet X0_10 (piSet5 tX05) ∪ prodSet J10_out (piSet5 tXH5) ∪ prodSet X1_10 (piSet5 tXV5) := by
  have hs : R15_Ahet.sigma.P .N = R15_Ahet.P .N := rfl
  rw [hs, R15_Ahet_def]
  simp only [Realisation.hetGao, Realisation.mapIso, Realisation.hetGao2, hetGaoFam, Finset.map_union, prodSet_def]
  have hf : inp10A.J0_N = X0_10 ∧ inp10A.JH_out = J10_out ∧ inp10A.JV_out = X1_10 := by
    rcases inp10A_fields with ⟨fN, _, _, fHo, _, fVo, _⟩
    exact ⟨fN.trans R10A_N_eq_R10_N |>.trans R10_N_eq_X0_10, fHo, fVo.trans R10A_AD_eq |>.trans R10_AD_eq_X1_10⟩
  rw [hf.1, hf.2.1, hf.2.2, baseR5_P_eq.2.1, baseR5_P_eq.2.2.2.1, baseR5_P_eq.2.2.1]

theorem R15_Ahet_sigma_AD_eq :
    R15_Ahet.sigma.P .A ∪ R15_Ahet.sigma.P .D =
      prodSet X1_10 (piSet5 tX05) ∪ prodSet X0_10 (piSet5 tXV5) ∪ prodSet J10_in (piSet5 tXH5) := by
  have hs : R15_Ahet.sigma.P .A ∪ R15_Ahet.sigma.P .D = R15_Ahet.P .D ∪ R15_Ahet.P .A := rfl
  rw [hs, R15_Ahet_def]
  simp only [Realisation.hetGao, Realisation.mapIso, Realisation.hetGao2, hetGaoFam, Finset.map_union]
  simp only [← prodSet_def]
  rcases inp10A_fields with ⟨_, fA, fD, _, fHi, _, fVi⟩
  rw [fA, fD, fHi, fVi, baseR5_P_eq.2.1, baseR5_P_eq.2.2.1, baseR5_P_eq.2.2.2.1,
      R10A_N_eq_R10_N, R10_N_eq_X0_10]
  have hu : (prodSet (R10A.P .D) (piSet5 tX05) ∪ prodSet X0_10 (piSet5 tXV5)) ∪
      (prodSet (R10A.P .A) (piSet5 tX05) ∪ prodSet J10_in (piSet5 tXH5)) =
      (prodSet (R10A.P .A) (piSet5 tX05) ∪ prodSet (R10A.P .D) (piSet5 tX05)) ∪
      prodSet X0_10 (piSet5 tXV5) ∪ prodSet J10_in (piSet5 tXH5) := by
    ext w; simp only [Finset.mem_union]
    constructor
    · rintro ((h | h) | (h | h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
    · rintro (((h | h) | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
  rw [hu, ← prodSet_union_left, R10A_AD_eq, R10_AD_eq_X1_10]

noncomputable def sig15Pi (w : Fin 15 → ZMod 7) : Nat :=
  (if inNbr (strongPowPi C7 15) (R15_AX.P .N) w then 8 else 0) +
  (if inNbr (strongPowPi C7 15) (R15_AX.P .A ∪ R15_AX.P .D) w then 4 else 0) +
  (if inNbr (strongPowPi C7 15) (R15_Ahet.sigma.P .N) w then 2 else 0) +
  (if inNbr (strongPowPi C7 15) (R15_Ahet.sigma.P .A ∪ R15_Ahet.sigma.P .D) w then 1 else 0)

theorem sig15Pi_lt (w : Fin 15 → ZMod 7) : sig15Pi w < 16 := by
  dsimp only [sig15Pi]; split_ifs <;> omega

private theorem idx15_bit_eq (a3 a2 a1 a0 b2 b1 b0 : Prop)
    [Decidable a3] [Decidable a2] [Decidable a1] [Decidable a0]
    [Decidable b2] [Decidable b1] [Decidable b0] :
    idx15OfBits
      ((if a3 then 8 else 0) + (if a2 then 4 else 0) + (if a1 then 2 else 0) + (if a0 then 1 else 0))
      ((if b2 then 4 else 0) + (if b1 then 2 else 0) + (if b0 then 1 else 0)) =
      (if (a3 ∧ b2) ∨ (a2 ∧ (b0 ∨ b1)) then 8 else 0) +
      (if (a2 ∧ b2) ∨ (a3 ∧ (b0 ∨ b1)) then 4 else 0) +
      (if (a3 ∧ b2) ∨ (a1 ∧ b1) ∨ (a2 ∧ b0) then 2 else 0) +
      (if (a2 ∧ b2) ∨ (a3 ∧ b0) ∨ (a0 ∧ b1) then 1 else 0) := by
  dsimp only [idx15OfBits]
  by_cases a3 <;> by_cases a2 <;> by_cases a1 <;> by_cases a0 <;>
  by_cases b2 <;> by_cases b1 <;> by_cases b0 <;> simp [*]

theorem idx15OfBits_eq_sig15Pi (z : Fin 10 → ZMod 7) (x : Fin 5 → ZMod 7) :
    idx15OfBits (sig10Pi z) (sig5_3Pi x) =
      sig15Pi (strongProdIsoAdd C7 10 5 (z, x)) := by
  have hu0 : inNbr (strongPowPi C7 15) (R15_AX.P .N) (strongProdIsoAdd C7 10 5 (z, x)) ↔
      (inNbr (strongPowPi C7 10) X0_10 z ∧ inNbr (strongPowPi C7 5) (piSet5 tX05) x) ∨
      (inNbr (strongPowPi C7 10) X1_10 z ∧
        (inNbr (strongPowPi C7 5) (piSet5 tXV5) x ∨ inNbr (strongPowPi C7 5) (piSet5 tXH5) x)) := by
    rw [R15_AX_N_eq, inNbr_union, inNbr_prodSet (dL := 10) (dR := 5), inNbr_prodSet (dL := 10) (dR := 5),
        piSet5_X15_eq, inNbr_union]
  have hu1 : inNbr (strongPowPi C7 15) (R15_AX.P .A ∪ R15_AX.P .D) (strongProdIsoAdd C7 10 5 (z, x)) ↔
      (inNbr (strongPowPi C7 10) X1_10 z ∧ inNbr (strongPowPi C7 5) (piSet5 tX05) x) ∨
      (inNbr (strongPowPi C7 10) X0_10 z ∧
        (inNbr (strongPowPi C7 5) (piSet5 tXV5) x ∨ inNbr (strongPowPi C7 5) (piSet5 tXH5) x)) := by
    rw [R15_AX_AD_eq, inNbr_union, inNbr_prodSet (dL := 10) (dR := 5), inNbr_prodSet (dL := 10) (dR := 5),
        piSet5_X15_eq, inNbr_union]
  have hv0 : inNbr (strongPowPi C7 15) (R15_Ahet.sigma.P .N) (strongProdIsoAdd C7 10 5 (z, x)) ↔
      (inNbr (strongPowPi C7 10) X0_10 z ∧ inNbr (strongPowPi C7 5) (piSet5 tX05) x) ∨
      (inNbr (strongPowPi C7 10) J10_out z ∧ inNbr (strongPowPi C7 5) (piSet5 tXH5) x) ∨
      (inNbr (strongPowPi C7 10) X1_10 z ∧ inNbr (strongPowPi C7 5) (piSet5 tXV5) x) := by
    rw [R15_Ahet_sigma_N_eq, inNbr_union, inNbr_union,
        inNbr_prodSet (dL := 10) (dR := 5), inNbr_prodSet (dL := 10) (dR := 5), inNbr_prodSet (dL := 10) (dR := 5),
        or_assoc]
  have hv1 : inNbr (strongPowPi C7 15) (R15_Ahet.sigma.P .A ∪ R15_Ahet.sigma.P .D) (strongProdIsoAdd C7 10 5 (z, x)) ↔
      (inNbr (strongPowPi C7 10) X1_10 z ∧ inNbr (strongPowPi C7 5) (piSet5 tX05) x) ∨
      (inNbr (strongPowPi C7 10) X0_10 z ∧ inNbr (strongPowPi C7 5) (piSet5 tXV5) x) ∨
      (inNbr (strongPowPi C7 10) J10_in z ∧ inNbr (strongPowPi C7 5) (piSet5 tXH5) x) := by
    rw [R15_Ahet_sigma_AD_eq, inNbr_union, inNbr_union,
        inNbr_prodSet (dL := 10) (dR := 5), inNbr_prodSet (dL := 10) (dR := 5), inNbr_prodSet (dL := 10) (dR := 5),
        or_assoc]
  dsimp only [sig15Pi]
  simp only [hu0, hu1, hv0, hv1]
  dsimp only [sig10Pi, sig5_3Pi]
  exact idx15_bit_eq _ _ _ _ _ _ _

theorem eval_lift15_vec16 (d16 d5t : Vec16)
    (h0 : d5t.v8 = 0 ∧ d5t.v9 = 0 ∧ d5t.v10 = 0 ∧ d5t.v11 = 0 ∧ d5t.v12 = 0 ∧ d5t.v13 = 0 ∧ d5t.v14 = 0 ∧ d5t.v15 = 0)
    (g : Nat → Nat) :
    vec16Eval (lift15 d16 d5t) g =
      vec16Eval d16 (fun s10 => vec16Eval d5t (fun s5 => g (idx15OfBits s10 s5))) := by
  rw [eval_lift15]
  congr 1; ext s10
  have hv3 : (3 : Fin 8).val = 3 := rfl
  have hv4 : (4 : Fin 8).val = 4 := rfl
  have hv5 : (5 : Fin 8).val = 5 := rfl
  have hv6 : (6 : Fin 8).val = 6 := rfl
  have hv7 : (7 : Fin 8).val = 7 := rfl
  rw [vec16Eval_eq_sum, Fin.sum_univ_eight, Fin.val_zero, Fin.val_one, Fin.val_two, hv3, hv4, hv5, hv6, hv7]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rcases h0 with ⟨h8, h9, h10, h11, h12, h13, h14, h15⟩
  dsimp only [Vec16.get]
  rw [h8, h9, h10, h11, h12, h13, h14, h15]
  simp only [zero_mul, add_zero]

theorem eval_lift15_prod {A : Finset (Fin 10 → ZMod 7)} {t5 : Trie7 5} {d16 d5t : Vec16}
    (hA : ∀ h, ∑ z ∈ A, h (sig10Pi z) = vec16Eval d16 h)
    (hd5 : dist5_3List t5 = d5t)
    (h0 : d5t.v8 = 0 ∧ d5t.v9 = 0 ∧ d5t.v10 = 0 ∧ d5t.v11 = 0 ∧ d5t.v12 = 0 ∧ d5t.v13 = 0 ∧ d5t.v14 = 0 ∧ d5t.v15 = 0)
    (g : Nat → Nat) :
    ∑ w ∈ prodSet A (piSet5 t5), g (sig15Pi w) = vec16Eval (lift15 d16 d5t) g := by
  rw [prodSet_def, Finset.sum_map, Finset.sum_product]
  simp only [Equiv.toEmbedding_apply]
  have h1 : ∀ z, (∑ x ∈ piSet5 t5, g (sig15Pi ((strongProdIsoAdd C7 10 5).toEquiv (z, x)))) =
      vec16Eval d5t (fun s5 => g (idx15OfBits (sig10Pi z) s5)) := by
    intro z
    have hs : ∀ x, g (sig15Pi ((strongProdIsoAdd C7 10 5).toEquiv (z, x))) =
        g (idx15OfBits (sig10Pi z) (sig5_3Pi x)) :=
      fun x => congrArg g (idx15OfBits_eq_sig15Pi z x).symm
    simp_rw [hs]
    rw [← eval_dist5_3List_pi t5 (fun s5 => g (idx15OfBits (sig10Pi z) s5)), hd5]
  rw [Finset.sum_congr rfl (fun z _ => h1 z)]
  exact (hA (fun s10 => vec16Eval d5t (fun s5 => g (idx15OfBits s10 s5)))).trans
    (eval_lift15_vec16 d16 d5t h0 g).symm

theorem sum_T15_P_B (g : Nat → Nat) :
    ∑ w ∈ (R15_het.P .B).map T15_pi_iso.toEquiv.toEmbedding, g (sig15Pi w) = vec16Eval d15_TB_val g := by
  have sL := R10.hsep
  have sR := baseR5.hsep
  have h12 : Disjoint (prodSet (R10.P .B) (baseR5.P .B)) (prodSet (R10.P .H) (baseR5.P .D)) :=
    (prodSet_sep (dL := 10) (dR := 5) (Or.inl (sL .B .H rfl))).disjoint
  have h123 : Disjoint (prodSet (R10.P .B) (baseR5.P .B) ∪ prodSet (R10.P .H) (baseR5.P .D))
      (prodSet (R10.P .V) (baseR5.P .A)) :=
    (Sep.union_left (prodSet_sep (dL := 10) (dR := 5) (Or.inl (sL .B .V rfl)))
      (prodSet_sep (dL := 10) (dR := 5) (Or.inr (sR .D .A rfl)))).disjoint
  have h1234 : Disjoint ((prodSet (R10.P .B) (baseR5.P .B) ∪ prodSet (R10.P .H) (baseR5.P .D)) ∪
      prodSet (R10.P .V) (baseR5.P .A)) (prodSet (R10.P .D) (baseR5.P .V)) :=
    (Sep.union_left (Sep.union_left (prodSet_sep (dL := 10) (dR := 5) (Or.inr (sR .B .V rfl)))
      (prodSet_sep (dL := 10) (dR := 5) (Or.inr (sR .D .V rfl))))
      (prodSet_sep (dL := 10) (dR := 5) (Or.inl (sL .V .D rfl)))).disjoint
  have h12345 : Disjoint (((prodSet (R10.P .B) (baseR5.P .B) ∪ prodSet (R10.P .H) (baseR5.P .D)) ∪
      prodSet (R10.P .V) (baseR5.P .A)) ∪ prodSet (R10.P .D) (baseR5.P .V))
      (prodSet (R10.P .A) (baseR5.P .H)) :=
    (Sep.union_left (Sep.union_left (Sep.union_left
      (prodSet_sep (dL := 10) (dR := 5) (Or.inr (sR .B .H rfl)))
      (prodSet_sep (dL := 10) (dR := 5) (Or.inl (sL .H .A rfl))))
      (prodSet_sep (dL := 10) (dR := 5) (Or.inr (sR .A .H rfl))))
      (prodSet_sep (dL := 10) (dR := 5) (Or.inl (sL .D .A rfl)))).disjoint
  rw [R15_het_P_B_O_eq.1]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12345)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h1234)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h123)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T15_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T10_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T10_pi_iso T5_pi_iso A B
  rw [hm, hm, hm, hm, hm, baseR5_P_eq.1, baseR5_P_eq.2.2.2.1, baseR5_P_eq.2.2.1,
      baseR5_P_eq.2.2.2.2.2.2, baseR5_P_eq.2.2.2.2.2.1]
  rw [piSet5_map_T5 tTB5_map_ok tTB5_card_eq,
      piSet5_map_T5 tTXH5_map_ok tTXH5_card_eq,
      piSet5_map_T5 tTXV5_map_ok tTXV5_card_eq,
      piSet5_map_T5 tTPV5_map_ok tTPV5_card_eq,
      piSet5_map_T5 tTPH5_map_ok tTPH5_card_eq]
  rw [eval_lift15_prod sum_T10_P_B d5_TB5_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      eval_lift15_prod sum_T10_P_H d5_TXH5_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      eval_lift15_prod sum_T10_P_V d5_TXV5_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      eval_lift15_prod sum_T10_P_D d5_TPV5_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      eval_lift15_prod sum_T10_P_A d5_TPH5_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g]
  have hr : vec16Eval d15_TB_val g =
      vec16Eval (lift15 d16_TB_val d5_TB5_val) g + vec16Eval (lift15 d16_TPH_val d5_TXH5_val) g +
      vec16Eval (lift15 d16_TPV_val d5_TXV5_val) g + vec16Eval (lift15 d16_TXH_val d5_TPV5_val) g +
      vec16Eval (lift15 d16_TXV_val d5_TPH5_val) g := by
    rw [← d15_TB_val_eq]; simp only [vec16Eval_add]; omega
  rw [hr]

theorem sum_T15_P_O (g : Nat → Nat) :
    ∑ w ∈ (R15_het.P .O).map T15_pi_iso.toEquiv.toEmbedding, g (sig15Pi w) = vec16Eval d15_TS_val g := by
  have h12 : Disjoint (prodSet (R10.P .O) (baseR5.P .N)) (prodSet (R10.P .N) (baseR5.P .O)) :=
    (prodSet_sep (dL := 10) (dR := 5) (Or.inl (R10.hsep .O .N rfl))).disjoint
  rw [R15_het_P_B_O_eq.2, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T15_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T10_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T10_pi_iso T5_pi_iso A B
  rw [hm, hm, baseR5_P_eq.2.1, baseR5_P_eq.2.2.2.2.1]
  rw [piSet5_map_T5 tTX05_map_ok tTX05_card_eq, piSet5_map_T5 tTS5_map_ok tTS5_card_eq]
  rw [eval_lift15_prod sum_T10_P_O d5_TX05_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      eval_lift15_prod sum_T10_P_N d5_TS5_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      ← vec16Eval_add, d15_TS_val_eq]

theorem sum_T15_P_H (g : Nat → Nat) :
    ∑ w ∈ (R15_het.P .H).map T15_pi_iso.toEquiv.toEmbedding, g (sig15Pi w) = vec16Eval d15_TPH_val g := by
  have h12 : Disjoint (prodSet (R10.P .H) (baseR5.P .N)) (prodSet (R10.P .N) (baseR5.P .V)) :=
    (prodSet_sep (dL := 10) (dR := 5) (Or.inl (R10.hsep .H .N rfl))).disjoint
  have hH : R15_het.P .H = prodSet (R10.P .H) (baseR5.P .N) ∪ prodSet (R10.P .N) (baseR5.P .V) := by
    simp only [R15_het_def, Realisation.hetGao, Realisation.mapIso, Realisation.hetGao2, hetGaoFam, Finset.map_union, prodSet_def]
  rw [hH, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T15_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T10_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T10_pi_iso T5_pi_iso A B
  rw [hm, hm, baseR5_P_eq.2.1, baseR5_P_eq.2.2.2.2.2.2]
  rw [piSet5_map_T5 tTX05_map_ok tTX05_card_eq, piSet5_map_T5 tTPV5_map_ok tTPV5_card_eq]
  rw [eval_lift15_prod sum_T10_P_H d5_TX05_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      eval_lift15_prod sum_T10_P_N d5_TPV5_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      ← vec16Eval_add, d15_TPH_val_eq]

theorem sum_T15_P_V (g : Nat → Nat) :
    ∑ w ∈ (R15_het.P .V).map T15_pi_iso.toEquiv.toEmbedding, g (sig15Pi w) = vec16Eval d15_TPV_val g := by
  have h12 : Disjoint (prodSet (R10.P .V) (baseR5.P .N)) (prodSet (R10.P .N) (baseR5.P .H)) :=
    (prodSet_sep (dL := 10) (dR := 5) (Or.inl (R10.hsep .V .N rfl))).disjoint
  have hV : R15_het.P .V = prodSet (R10.P .V) (baseR5.P .N) ∪ prodSet (R10.P .N) (baseR5.P .H) := by
    simp only [R15_het_def, Realisation.hetGao, Realisation.mapIso, Realisation.hetGao2, hetGaoFam, Finset.map_union, prodSet_def]
  rw [hV, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T15_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T10_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T10_pi_iso T5_pi_iso A B
  rw [hm, hm, baseR5_P_eq.2.1, baseR5_P_eq.2.2.2.2.2.1]
  rw [piSet5_map_T5 tTX05_map_ok tTX05_card_eq, piSet5_map_T5 tTPH5_map_ok tTPH5_card_eq]
  rw [eval_lift15_prod sum_T10_P_V d5_TX05_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      eval_lift15_prod sum_T10_P_N d5_TPH5_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      ← vec16Eval_add, d15_TPV_val_eq]

theorem sum_T15_P_N (g : Nat → Nat) :
    ∑ w ∈ (R15_het.P .N).map T15_pi_iso.toEquiv.toEmbedding, g (sig15Pi w) = vec16Eval d15_TX0_val g := by
  have h12 : Disjoint (prodSet (R10.P .N) (baseR5.P .N)) (prodSet J10_out (piSet5 tX15)) :=
    (prodSet_sep (dL := 10) (dR := 5) (Or.inl J10_out_sep_R10N.symm)).disjoint
  have hN : R15_het.P .N = prodSet (R10.P .N) (baseR5.P .N) ∪ prodSet J10_out (piSet5 tX15) := by
    rw [R15_het_def]
    simp only [Realisation.hetGao, Realisation.mapIso, Realisation.hetGao2, hetGaoFam, Finset.map_union]
    simp only [← prodSet_def]
    have hf : inp10.J0_N = R10.P .N ∧ inp10.JH_out = J10_out ∧ inp10.JV_out = J10_out := by
      unfold inp10; exact ⟨rfl, rfl, rfl⟩
    rw [hf.1, hf.2.1, hf.2.2, baseR5_P_eq.2.2.1, baseR5_P_eq.2.2.2.1, Finset.union_assoc,
        ← prodSet_union_right, Finset.union_comm (piSet5 tXH5), ← piSet5_X15_eq]
  rw [hN, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T15_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T10_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T10_pi_iso T5_pi_iso A B
  rw [hm, hm, baseR5_P_eq.2.1, piSet5_map_T5 tTX05_map_ok tTX05_card_eq, piSet5_map_T5 tTX15_map_ok tTX15_card_eq]
  rw [eval_lift15_prod sum_T10_P_N d5_TX05_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      eval_lift15_prod sum_TJ10_out d5_TX15_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      ← vec16Eval_add, d15_TX0_val_eq]

theorem sum_T15_P_D (g : Nat → Nat) :
    ∑ w ∈ (R15_het.P .D).map T15_pi_iso.toEquiv.toEmbedding, g (sig15Pi w) = vec16Eval d15_TXH_val g := by
  have h12 : Disjoint (prodSet (R10.P .D) (baseR5.P .N)) (prodSet J10_in (baseR5.P .A)) :=
    (prodSet_sep (dL := 10) (dR := 5) (Or.inr (baseR5.hsep .N .A rfl))).disjoint
  have hD : R15_het.P .D = prodSet (R10.P .D) (baseR5.P .N) ∪ prodSet J10_in (baseR5.P .A) := by
    rw [R15_het_def]
    simp only [Realisation.hetGao, Realisation.mapIso, Realisation.hetGao2, hetGaoFam, Finset.map_union, prodSet_def]
    have hf : inp10.J0_D = R10.P .D ∧ inp10.JV_in = J10_in := by unfold inp10; exact ⟨rfl, rfl⟩
    rw [hf.1, hf.2]
  rw [hD, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T15_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T10_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T10_pi_iso T5_pi_iso A B
  rw [hm, hm, baseR5_P_eq.2.1, baseR5_P_eq.2.2.1,
      piSet5_map_T5 tTX05_map_ok tTX05_card_eq, piSet5_map_T5 tTXV5_map_ok tTXV5_card_eq]
  rw [eval_lift15_prod sum_T10_P_D d5_TX05_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      eval_lift15_prod sum_TJ10_in d5_TXV5_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      ← vec16Eval_add, d15_TXH_val_eq]

theorem sum_T15_P_A (g : Nat → Nat) :
    ∑ w ∈ (R15_het.P .A).map T15_pi_iso.toEquiv.toEmbedding, g (sig15Pi w) = vec16Eval d15_TXV_val g := by
  have h12 : Disjoint (prodSet (R10.P .A) (baseR5.P .N)) (prodSet J10_in (baseR5.P .D)) :=
    (prodSet_sep (dL := 10) (dR := 5) (Or.inr (baseR5.hsep .N .D rfl))).disjoint
  have hA : R15_het.P .A = prodSet (R10.P .A) (baseR5.P .N) ∪ prodSet J10_in (baseR5.P .D) := by
    rw [R15_het_def]
    simp only [Realisation.hetGao, Realisation.mapIso, Realisation.hetGao2, hetGaoFam, Finset.map_union, prodSet_def]
    have hf : inp10.J0_A = R10.P .A ∧ inp10.JH_in = J10_in := by unfold inp10; exact ⟨rfl, rfl⟩
    rw [hf.1, hf.2]
  rw [hA, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  have hm : ∀ A B, (prodSet A B).map T15_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T10_pi_iso.toEquiv.toEmbedding) (B.map T5_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T10_pi_iso T5_pi_iso A B
  rw [hm, hm, baseR5_P_eq.2.1, baseR5_P_eq.2.2.2.1,
      piSet5_map_T5 tTX05_map_ok tTX05_card_eq, piSet5_map_T5 tTXH5_map_ok tTXH5_card_eq]
  rw [eval_lift15_prod sum_T10_P_A d5_TX05_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      eval_lift15_prod sum_TJ10_in d5_TXH5_val_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ g,
      ← vec16Eval_add, d15_TXV_val_eq]

-- Concrete 30D Realisations & C4 = 841760069965664
@[irreducible] def R30L : Realisation Letter Letter.sep (strongPowPi C7 30) :=
  s2aProd R15_AX R15_Ahet.sigma

theorem R30L_def : R30L = s2aProd R15_AX R15_Ahet.sigma := by unfold R30L; rfl

theorem R15_Ahet_sigma_w :
    R15_Ahet.sigma.w .B = 46990439 ∧ R15_Ahet.sigma.w .N = 35303606 ∧
    R15_Ahet.sigma.w .A = 5948463 ∧ R15_Ahet.sigma.w .D = 8180458 ∧
    R15_Ahet.sigma.w .O = 2504616 ∧ R15_Ahet.sigma.w .H = 2504616 ∧ R15_Ahet.sigma.w .V = 2504616 := by
  rcases R15_Ahet_w with ⟨hB, hN, hA, hD, hO, hH, hV⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Realisation.w_sigma]
  · exact hB
  · exact hN
  · exact hD
  · exact hA
  · exact hO
  · exact hV
  · exact hH

theorem R30L_w :
    R30L.w .B = 2278775073866497 ∧ R30L.w .N = 1446768903083453 ∧
    R30L.w .A = 576488425905496 ∧ R30L.w .D = 420235140891852 ∧
    R30L.w .O = 176941111954464 ∧ R30L.w .H = 176941111954464 ∧ R30L.w .V = 176941111954464 := by
  rw [R30L_def]
  have hw := w_s2aProd R15_AX R15_Ahet.sigma
  rcases R15_AX_w with ⟨lB, lN, lA, lD, lO, lH, lV⟩
  rcases R15_Ahet_sigma_w with ⟨rB, rN, rA, rD, rO, rH, rV⟩
  rw [lB, lN, lA, lD, lO, lH, lV, rB, rN, rA, rD, rO, rH, rV] at hw
  norm_num at hw
  exact hw

private theorem R15_AX_AD_indep :
    (strongPowPi C7 15).IsIndepSet ((R15_AX.P .A ∪ R15_AX.P .D : Finset (Fin 15 → ZMod 7)) : Set (Fin 15 → ZMod 7)) :=
  isIndepSet_union_of_sep (R15_AX.hindep .A) (R15_AX.hindep .D) (R15_AX.hsep .A .D rfl)

private theorem R15_AX_AD_sep_N :
    Sep (strongPowPi C7 15) (R15_AX.P .A ∪ R15_AX.P .D) (R15_AX.P .N) :=
  Sep.union_left (R15_AX.hsep .A .N rfl) (R15_AX.hsep .D .N rfl)

@[irreducible] noncomputable def inp15 : HetLeftInput R15_AX :=
  HetLeftInput.ofSiblingAndParts R15_AX R15_Ahet
    R15_Ahet_OHV_eq.1 R15_Ahet_OHV_eq.2.1 R15_Ahet_OHV_eq.2.2
    J15_out J15_in (R15_AX.P .A ∪ R15_AX.P .D) (R15_AX.P .N)
    J15_out_indep J15_in_indep J15_out_sep_in J15_out_sep_R15N
    R15_AX_AD_indep (R15_AX.hindep .N) R15_AX_AD_sep_N R15_AX_AD_sep_N

theorem inp15_fields :
    inp15.J0_N = R15_Ahet.P .N ∧ inp15.J0_A = R15_Ahet.P .A ∧ inp15.J0_D = R15_Ahet.P .D ∧
    inp15.JH_out = J15_out ∧ inp15.JH_in = J15_in ∧
    inp15.JV_out = R15_AX.P .A ∪ R15_AX.P .D ∧ inp15.JV_in = R15_AX.P .N := by
  unfold inp15; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[irreducible] noncomputable def R30hat : Realisation Letter Letter.sep (strongPowPi C7 30) :=
  R15_AX.hetGao R15_Ahet.sigma inp15

theorem R30hat_def : R30hat = R15_AX.hetGao R15_Ahet.sigma inp15 := by unfold R30hat; rfl

theorem R30hat_OHV_eq :
    R30hat.P .O = R30L.P .O ∧ R30hat.P .H = R30L.P .H ∧ R30hat.P .V = R30L.P .V := by
  rw [R30hat_def, R30L_def]
  exact ⟨rfl, rfl, rfl⟩

theorem R30hat_w :
    R30hat.w .B = 2278775073866497 ∧ R30hat.w .N = 1435184942161465 ∧
    R30hat.w .A = 588656251987804 ∧ R30hat.w .D = 420235140891852 ∧
    R30hat.w .O = 176941111954464 ∧ R30hat.w .H = 176941111954464 ∧ R30hat.w .V = 176941111954464 := by
  rw [R30hat_def]
  have hw := w_hetGao R15_AX R15_Ahet.sigma inp15
  rcases inp15_fields with ⟨fN, fA, fD, fHo, fHi, fVo, fVi⟩
  have h15N : inp15.J0_N.card = 35303606 := by rw [fN]; exact R15_Ahet_w.2.1
  have h15A : inp15.J0_A.card = 8180458 := by rw [fA]; exact R15_Ahet_w.2.2.1
  have h15D : inp15.J0_D.card = 5948463 := by rw [fD]; exact R15_Ahet_w.2.2.2.1
  have hHo : inp15.JH_out.card = 12839823 := by rw [fHo]; exact J15_out_card
  have hHi : inp15.JH_in.card = 36655232 := by rw [fHi]; exact J15_in_card
  have hVo : inp15.JV_out.card = 14088465 := by
    rw [fVo, Finset.card_union_of_disjoint (R15_AX.hsep .A .D rfl).disjoint, ← Realisation.w, ← Realisation.w,
        R15_AX_w.2.2.1, R15_AX_w.2.2.2.1]
  have hVi : inp15.JV_in.card = 35342398 := by rw [fVi]; exact R15_AX_w.2.1
  rcases R15_AX_w with ⟨lB, lN, lA, lD, lO, lH, lV⟩
  rcases R15_Ahet_sigma_w with ⟨rB, rN, rA, rD, rO, rH, rV⟩
  rw [h15N, h15A, h15D, hHo, hHi, hVo, hVi, lB, lN, lA, lD, lO, lH, lV, rB, rN, rA, rD, rO, rH, rV] at hw
  norm_num at hw
  exact hw

@[irreducible] def R30pp : Realisation Letter Letter.sep (strongPowPi C7 30) :=
  s2aProd R15_het R15_het

theorem R30pp_def : R30pp = s2aProd R15_het R15_het := by unfold R30pp; rfl

theorem R30pp_w :
    R30pp.w .B = 2279024493546241 ∧ R30pp.w .N = 1444806524461789 ∧
    R30pp.w .A = 499444211264130 ∧ R30pp.w .D = 499444211264130 ∧
    R30pp.w .O = 176701951181856 ∧ R30pp.w .H = 176701951181856 ∧ R30pp.w .V = 176701951181856 := by
  rw [R30pp_def]
  have hw := w_s2aProd R15_het R15_het
  rcases R15_het_w with ⟨hB, hN, hA, hD, hO, hH, hV⟩
  rw [hB, hN, hA, hD, hO, hH, hV] at hw
  norm_num at hw
  exact hw

@[irreducible] def J30pp : Finset (Fin 30 → ZMod 7) :=
  (R30pp.P .B ∪ R30pp.P .O).map T30_pi_iso.toEquiv.toEmbedding

theorem J30pp_def : J30pp = (R30pp.P .B ∪ R30pp.P .O).map T30_pi_iso.toEquiv.toEmbedding := by
  unfold J30pp; rfl

theorem J30pp_indep : (strongPowPi C7 30).IsIndepSet (J30pp : Set (Fin 30 → ZMod 7)) := by
  have hi : (strongPowPi C7 30).IsIndepSet ((R30pp.P .B ∪ R30pp.P .O : Finset (Fin 30 → ZMod 7)) : Set (Fin 30 → ZMod 7)) :=
    isIndepSet_union_of_sep (R30pp.hindep .B) (R30pp.hindep .O) (R30pp.hsep .B .O rfl)
  intro x hx y hy hne hadj
  rw [J30pp_def] at hx hy
  rcases Finset.mem_map.mp (Finset.mem_coe.mp hx) with ⟨x', hx', rfl⟩
  rcases Finset.mem_map.mp (Finset.mem_coe.mp hy) with ⟨y', hy', rfl⟩
  exact hi hx' hy' (fun h => hne (congrArg T30_pi_iso h)) ((T30_pi_iso.map_rel_iff).mp hadj)

theorem J30pp_card : J30pp.card = 2455726444728097 := by
  rw [J30pp_def, Finset.card_map, Finset.card_union_of_disjoint (R30pp.hsep .B .O rfl).disjoint,
      ← Realisation.w, ← Realisation.w, R30pp_w.1, R30pp_w.2.2.2.2.1]

noncomputable def J30pp_out : Finset (Fin 30 → ZMod 7) :=
  J30pp.filter (fun w => ¬ inNbr (strongPowPi C7 30) (R30L.P .N) w)

noncomputable def J30pp_in : Finset (Fin 30 → ZMod 7) :=
  J30pp \ J30pp_out

theorem J30pp_out_indep : (strongPowPi C7 30).IsIndepSet (J30pp_out : Set (Fin 30 → ZMod 7)) :=
  isIndepSet_subset J30pp_indep (Finset.filter_subset _ J30pp)

theorem J30pp_in_indep : (strongPowPi C7 30).IsIndepSet (J30pp_in : Set (Fin 30 → ZMod 7)) :=
  isIndepSet_subset J30pp_indep Finset.sdiff_subset

theorem J30pp_out_sep_in : Sep (strongPowPi C7 30) J30pp_out J30pp_in :=
  fun _ hx _ hy hc => isIndepSet_not_close_of_ne J30pp_indep (Finset.filter_subset _ J30pp hx)
    (Finset.mem_sdiff.mp hy).1 (fun h => (Finset.mem_sdiff.mp hy).2 (h ▸ hx)) hc

theorem J30pp_out_sep_R30LN : Sep (strongPowPi C7 30) J30pp_out (R30L.P .N) := by
  rw [sep_iff_not_inNbr]
  intro w hw
  exact (Finset.mem_filter.mp hw).2

private theorem avoid30_bit_eq (a3 a2 a1 a0 b3 b2 b1 b0 : Prop)
    [Decidable a3] [Decidable a2] [Decidable a1] [Decidable a0]
    [Decidable b3] [Decidable b2] [Decidable b1] [Decidable b0] :
    (let xL := (if a3 then 8 else 0) + (if a2 then 4 else 0) + (if a1 then 2 else 0) + (if a0 then 1 else 0)
     let xR := (if b3 then 8 else 0) + (if b2 then 4 else 0) + (if b1 then 2 else 0) + (if b0 then 1 else 0)
     if (((((xL >>> 3) &&& 1) &&& ((xR >>> 1) &&& 1)) ||| (((xL >>> 2) &&& 1) &&& (xR &&& 1))) == 0)
     then 1 else 0) =
    if ¬ ((a3 ∧ b1) ∨ (a2 ∧ b0)) then 1 else 0 := by
  dsimp only
  by_cases a3 <;> by_cases a2 <;> by_cases a1 <;> by_cases a0 <;>
  by_cases b3 <;> by_cases b2 <;> by_cases b1 <;> by_cases b0 <;> simp [*]

theorem R30pp_P_B_O_eq :
    R30pp.P .B = prodSet (R15_het.P .B) (R15_het.P .B) ∪ prodSet (R15_het.P .H) (R15_het.P .D) ∪
      prodSet (R15_het.P .V) (R15_het.P .A) ∪ prodSet (R15_het.P .D) (R15_het.P .V) ∪
      prodSet (R15_het.P .A) (R15_het.P .H) ∧
    R30pp.P .O = prodSet (R15_het.P .O) (R15_het.P .N) ∪ prodSet (R15_het.P .N) (R15_het.P .O) := by
  constructor <;> simp only [R30pp_def, s2aProd, Realisation.mapIso, s2aFam, Finset.map_union, prodSet_def]

theorem R30L_N_eq :
    R30L.P .N = prodSet (R15_AX.P .N) (R15_Ahet.sigma.P .N) ∪
      prodSet (R15_AX.P .A ∪ R15_AX.P .D) (R15_Ahet.sigma.P .A ∪ R15_Ahet.sigma.P .D) := by
  rw [R30L_def, (R10_P_map_prodSet R15_AX R15_Ahet.sigma).1]

theorem J30pp_out_card : J30pp_out.card = 841760069965664 := by
  rw [J30pp_out, Finset.card_filter]
  have sL := R15_het.hsep
  have sR := R15_het.hsep
  have h12 : Disjoint (prodSet (R15_het.P .B) (R15_het.P .B)) (prodSet (R15_het.P .H) (R15_het.P .D)) :=
    (prodSet_sep (dL := 15) (dR := 15) (Or.inl (sL .B .H rfl))).disjoint
  have h123 : Disjoint (prodSet (R15_het.P .B) (R15_het.P .B) ∪ prodSet (R15_het.P .H) (R15_het.P .D))
      (prodSet (R15_het.P .V) (R15_het.P .A)) :=
    (Sep.union_left (prodSet_sep (dL := 15) (dR := 15) (Or.inl (sL .B .V rfl)))
      (prodSet_sep (dL := 15) (dR := 15) (Or.inr (sR .D .A rfl)))).disjoint
  have h1234 : Disjoint ((prodSet (R15_het.P .B) (R15_het.P .B) ∪ prodSet (R15_het.P .H) (R15_het.P .D)) ∪
      prodSet (R15_het.P .V) (R15_het.P .A)) (prodSet (R15_het.P .D) (R15_het.P .V)) :=
    (Sep.union_left (Sep.union_left (prodSet_sep (dL := 15) (dR := 15) (Or.inr (sR .B .V rfl)))
      (prodSet_sep (dL := 15) (dR := 15) (Or.inr (sR .D .V rfl))))
      (prodSet_sep (dL := 15) (dR := 15) (Or.inl (sL .V .D rfl)))).disjoint
  have h12345 : Disjoint (((prodSet (R15_het.P .B) (R15_het.P .B) ∪ prodSet (R15_het.P .H) (R15_het.P .D)) ∪
      prodSet (R15_het.P .V) (R15_het.P .A)) ∪ prodSet (R15_het.P .D) (R15_het.P .V))
      (prodSet (R15_het.P .A) (R15_het.P .H)) :=
    (Sep.union_left (Sep.union_left (Sep.union_left
      (prodSet_sep (dL := 15) (dR := 15) (Or.inr (sR .B .H rfl)))
      (prodSet_sep (dL := 15) (dR := 15) (Or.inl (sL .H .A rfl))))
      (prodSet_sep (dL := 15) (dR := 15) (Or.inr (sR .A .H rfl))))
      (prodSet_sep (dL := 15) (dR := 15) (Or.inl (sL .D .A rfl)))).disjoint
  have hO12 : Disjoint (prodSet (R15_het.P .O) (R15_het.P .N)) (prodSet (R15_het.P .N) (R15_het.P .O)) :=
    (prodSet_sep (dL := 15) (dR := 15) (Or.inl (sL .O .N rfl))).disjoint
  have hBO : Disjoint (R30pp.P .B) (R30pp.P .O) := (R30pp.hsep .B .O rfl).disjoint
  rw [J30pp_def, Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact hBO)]
  rw [R30pp_P_B_O_eq.1, R30pp_P_B_O_eq.2]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12345)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h1234)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h123)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact h12)]
  rw [Finset.map_union, Finset.sum_union (by rw [Finset.disjoint_map]; exact hO12)]
  have hm : ∀ A B, (prodSet A B).map T30_pi_iso.toEquiv.toEmbedding =
      prodSet (A.map T15_pi_iso.toEquiv.toEmbedding) (B.map T15_pi_iso.toEquiv.toEmbedding) :=
    fun A B => prodSet_map_iso T15_pi_iso T15_pi_iso A B
  rw [hm, hm, hm, hm, hm, hm, hm]
  let f30 : (Fin 30 → ZMod 7) → Nat := fun w => if ¬ inNbr (strongPowPi C7 30) (R30L.P .N) w then 1 else 0
  have hprod_sum : ∀ (A B : Finset (Fin 15 → ZMod 7)) (dA dB : Vec16),
      (∀ h, ∑ z ∈ A, h (sig15Pi z) = vec16Eval dA h) →
      (∀ h, ∑ x ∈ B, h (sig15Pi x) = vec16Eval dB h) →
      (∑ w ∈ prodSet A B, f30 w) = countAvoid30 dA dB := by
    intro A B dA dB hA hB
    rw [countAvoid30_eq, prodSet_def, Finset.sum_map, Finset.sum_product]
    simp only [Equiv.toEmbedding_apply]
    have hin : ∀ z x, (f30 ((strongProdIsoAdd C7 15 15).toEquiv (z, x))) =
        (if (((((sig15Pi z >>> 3) &&& 1) &&& ((sig15Pi x >>> 1) &&& 1)) |||
              (((sig15Pi z >>> 2) &&& 1) &&& (sig15Pi x &&& 1))) == 0) then 1 else 0) := by
      intro z x
      dsimp only [f30]
      have hnb : inNbr (strongPowPi C7 30) (R30L.P .N) ((strongProdIsoAdd C7 15 15).toEquiv (z, x)) ↔
          (inNbr (strongPowPi C7 15) (R15_AX.P .N) z ∧ inNbr (strongPowPi C7 15) (R15_Ahet.sigma.P .N) x) ∨
          (inNbr (strongPowPi C7 15) (R15_AX.P .A ∪ R15_AX.P .D) z ∧
            inNbr (strongPowPi C7 15) (R15_Ahet.sigma.P .A ∪ R15_Ahet.sigma.P .D) x) := by
        rw [R30L_N_eq]; exact by
          change inNbr (strongPowPi C7 30) _ (strongProdIsoAdd C7 15 15 (z, x)) ↔ _
          rw [inNbr_union, inNbr_prodSet (dL := 15) (dR := 15), inNbr_prodSet (dL := 15) (dR := 15)]
      simp only [hnb, sig15Pi]
      exact (avoid30_bit_eq _ _ _ _ _ _ _ _).symm
    rw [Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun x _ => hin z x))]
    have hinner : ∀ z, (∑ x ∈ B, (if (((((sig15Pi z >>> 3) &&& 1) &&& ((sig15Pi x >>> 1) &&& 1)) |||
        (((sig15Pi z >>> 2) &&& 1) &&& (sig15Pi x &&& 1))) == 0) then 1 else 0)) =
        vec16Eval dB (fun sR => if (((((sig15Pi z >>> 3) &&& 1) &&& ((sR >>> 1) &&& 1)) |||
        (((sig15Pi z >>> 2) &&& 1) &&& (sR &&& 1))) == 0) then 1 else 0) :=
      fun z => hB (fun sR => if (((((sig15Pi z >>> 3) &&& 1) &&& ((sR >>> 1) &&& 1)) |||
        (((sig15Pi z >>> 2) &&& 1) &&& (sR &&& 1))) == 0) then 1 else 0)
    rw [Finset.sum_congr rfl (fun z _ => hinner z)]
    exact hA (fun sL => vec16Eval dB (fun sR => if (((((sL >>> 3) &&& 1) &&& ((sR >>> 1) &&& 1)) |||
        (((sL >>> 2) &&& 1) &&& (sR &&& 1))) == 0) then 1 else 0))
  change (∑ w ∈ prodSet ((R15_het.P .B).map T15_pi_iso.toEquiv.toEmbedding) ((R15_het.P .B).map T15_pi_iso.toEquiv.toEmbedding), f30 w) +
         (∑ w ∈ prodSet ((R15_het.P .H).map T15_pi_iso.toEquiv.toEmbedding) ((R15_het.P .D).map T15_pi_iso.toEquiv.toEmbedding), f30 w) +
         (∑ w ∈ prodSet ((R15_het.P .V).map T15_pi_iso.toEquiv.toEmbedding) ((R15_het.P .A).map T15_pi_iso.toEquiv.toEmbedding), f30 w) +
         (∑ w ∈ prodSet ((R15_het.P .D).map T15_pi_iso.toEquiv.toEmbedding) ((R15_het.P .V).map T15_pi_iso.toEquiv.toEmbedding), f30 w) +
         (∑ w ∈ prodSet ((R15_het.P .A).map T15_pi_iso.toEquiv.toEmbedding) ((R15_het.P .H).map T15_pi_iso.toEquiv.toEmbedding), f30 w) +
        ((∑ w ∈ prodSet ((R15_het.P .O).map T15_pi_iso.toEquiv.toEmbedding) ((R15_het.P .N).map T15_pi_iso.toEquiv.toEmbedding), f30 w) +
         (∑ w ∈ prodSet ((R15_het.P .N).map T15_pi_iso.toEquiv.toEmbedding) ((R15_het.P .O).map T15_pi_iso.toEquiv.toEmbedding), f30 w)) = 841760069965664
  rw [hprod_sum _ _ d15_TB_val d15_TB_val sum_T15_P_B sum_T15_P_B,
      hprod_sum _ _ d15_TPH_val d15_TXH_val sum_T15_P_H sum_T15_P_D,
      hprod_sum _ _ d15_TPV_val d15_TXV_val sum_T15_P_V sum_T15_P_A,
      hprod_sum _ _ d15_TXH_val d15_TPV_val sum_T15_P_D sum_T15_P_V,
      hprod_sum _ _ d15_TXV_val d15_TPH_val sum_T15_P_A sum_T15_P_H,
      hprod_sum _ _ d15_TS_val d15_TX0_val sum_T15_P_O sum_T15_P_N,
      hprod_sum _ _ d15_TX0_val d15_TS_val sum_T15_P_N sum_T15_P_O]
  rw [c4_0_val_eq, c4_2_val_eq, c4_3_val_eq, c4_5_val_eq, c4_6_val_eq, c4_1_val_eq, c4_4_val_eq]
  rw [← c4_exact_val_eq]; omega

theorem J30pp_in_card : J30pp_in.card = 1613966374762433 := by
  rw [J30pp_in, Finset.card_sdiff_of_subset (by rw [J30pp_out]; exact Finset.filter_subset _ J30pp),
      J30pp_card, J30pp_out_card]

end SigBridge15AndC4

/-! ## Section 7: Higher Layers (d = 20, 35, 40, 50, 65, 155, 620) & Main Bound -/

section HigherLayersAndM620

@[irreducible] noncomputable def inp30 : HetLeftInput R30L :=
  HetLeftInput.ofSiblingAndParts R30L R30hat
    R30hat_OHV_eq.1 R30hat_OHV_eq.2.1 R30hat_OHV_eq.2.2
    J30pp_out J30pp_in J30pp_out J30pp_in
    J30pp_out_indep J30pp_in_indep J30pp_out_sep_in J30pp_out_sep_R30LN
    J30pp_out_indep J30pp_in_indep J30pp_out_sep_in J30pp_out_sep_R30LN

theorem inp30_fields :
    inp30.J0_N = R30hat.P .N ∧ inp30.J0_A = R30hat.P .A ∧ inp30.J0_D = R30hat.P .D ∧
    inp30.JH_out = J30pp_out ∧ inp30.JH_in = J30pp_in ∧
    inp30.JV_out = J30pp_out ∧ inp30.JV_in = J30pp_in := by
  unfold inp30; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem inp30_sigma_fields :
    inp30.sigma.J0_N = R30hat.P .N ∧ inp30.sigma.J0_A = R30hat.P .D ∧ inp30.sigma.J0_D = R30hat.P .A ∧
    inp30.sigma.JH_out = J30pp_out ∧ inp30.sigma.JH_in = J30pp_in ∧
    inp30.sigma.JV_out = J30pp_out ∧ inp30.sigma.JV_in = J30pp_in := by
  rcases inp30_fields with ⟨fN, fA, fD, fHo, fHi, fVo, fVi⟩
  dsimp only [HetLeftInput.sigma]
  exact ⟨fN, fD, fA, fHo, fHi, fVo, fVi⟩

theorem R30L_sigma_w :
    R30L.sigma.w .B = 2278775073866497 ∧ R30L.sigma.w .N = 1446768903083453 ∧
    R30L.sigma.w .A = 420235140891852 ∧ R30L.sigma.w .D = 576488425905496 ∧
    R30L.sigma.w .O = 176941111954464 ∧ R30L.sigma.w .H = 176941111954464 ∧ R30L.sigma.w .V = 176941111954464 := by
  rcases R30L_w with ⟨hB, hN, hA, hD, hO, hH, hV⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Realisation.w_sigma]; exact hB
  · rw [Realisation.w_sigma]; exact hN
  · rw [Realisation.w_sigma]; exact hD
  · rw [Realisation.w_sigma]; exact hA
  · rw [Realisation.w_sigma]; exact hO
  · rw [Realisation.w_sigma]; exact hV
  · rw [Realisation.w_sigma]; exact hH

@[irreducible] noncomputable def R40_s0 : Realisation Letter Letter.sep (strongPowPi C7 40) :=
  R30L.sigma.hetGao R10A inp30.sigma

theorem R40_s0_def : R40_s0 = R30L.sigma.hetGao R10A inp30.sigma := by unfold R40_s0; rfl

theorem R40_s0_w :
    R40_s0.w .B = 305594401588752181313 ∧ R40_s0.w .N = 176106171878551246405 ∧
    R40_s0.w .A = 64171129070129913256 ∧ R40_s0.w .D = 89250516720400951188 ∧
    R40_s0.w .O = 26158021392280384832 ∧ R40_s0.w .H = 26158021392280384832 ∧
    R40_s0.w .V = 26158021392280384832 := by
  rw [R40_s0_def]
  have hw := w_hetGao R30L.sigma R10A inp30.sigma
  rcases inp30_sigma_fields with ⟨fN, fA, fD, fHo, fHi, fVo, fVi⟩
  have hJN : inp30.sigma.J0_N.card = 1435184942161465 := by rw [fN]; exact R30hat_w.2.1
  have hJA : inp30.sigma.J0_A.card = 420235140891852 := by rw [fA]; exact R30hat_w.2.2.2.1
  have hJD : inp30.sigma.J0_D.card = 588656251987804 := by rw [fD]; exact R30hat_w.2.2.1
  have hHo : inp30.sigma.JH_out.card = 841760069965664 := by rw [fHo]; exact J30pp_out_card
  have hHi : inp30.sigma.JH_in.card = 1613966374762433 := by rw [fHi]; exact J30pp_in_card
  have hVo : inp30.sigma.JV_out.card = 841760069965664 := by rw [fVo]; exact J30pp_out_card
  have hVi : inp30.sigma.JV_in.card = 1613966374762433 := by rw [fVi]; exact J30pp_in_card
  rcases R30L_sigma_w with ⟨lB, lN, lA, lD, lO, lH, lV⟩
  rcases R10A_w with ⟨rB, rN, rA, rD, rO, rH, rV⟩
  rw [hJN, hJA, hJD, hHo, hHi, hVo, hVi, lB, lN, lA, lD, lO, lH, lV, rB, rN, rA, rD, rO, rH, rV] at hw
  norm_num at hw
  exact hw

@[irreducible] noncomputable def R35_sub : Realisation Letter Letter.sep (strongPowPi C7 35) :=
  R30L.hetGao baseR5 inp30

theorem R35_sub_def : R35_sub = R30L.hetGao baseR5 inp30 := by unfold R35_sub; rfl

theorem R35_sub_w :
    R35_sub.w .B = 834016390090402087 ∧ R35_sub.w .N = 500008754524446610 ∧
    R35_sub.w .A = 231510438883896146 ∧ R35_sub.w .D = 165981076487662571 ∧
    R35_sub.w .O = 68549189274005032 ∧ R35_sub.w .H = 68549189274005032 ∧
    R35_sub.w .V = 68549189274005032 := by
  rw [R35_sub_def]
  have hw := w_hetGao R30L baseR5 inp30
  rcases inp30_fields with ⟨fN, fA, fD, fHo, fHi, fVo, fVi⟩
  have hJN : inp30.J0_N.card = 1435184942161465 := by rw [fN]; exact R30hat_w.2.1
  have hJA : inp30.J0_A.card = 588656251987804 := by rw [fA]; exact R30hat_w.2.2.1
  have hJD : inp30.J0_D.card = 420235140891852 := by rw [fD]; exact R30hat_w.2.2.2.1
  have hHo : inp30.JH_out.card = 841760069965664 := by rw [fHo]; exact J30pp_out_card
  have hHi : inp30.JH_in.card = 1613966374762433 := by rw [fHi]; exact J30pp_in_card
  have hVo : inp30.JV_out.card = 841760069965664 := by rw [fVo]; exact J30pp_out_card
  have hVi : inp30.JV_in.card = 1613966374762433 := by rw [fVi]; exact J30pp_in_card
  rcases R30L_w with ⟨lB, lN, lA, lD, lO, lH, lV⟩
  rcases baseR5_w with ⟨rB, rN, rA, rD, rO, rH, rV⟩
  rw [hJN, hJA, hJD, hHo, hHi, hVo, hVi, lB, lN, lA, lD, lO, lH, lV, rB, rN, rA, rD, rO, rH, rV] at hw
  norm_num at hw
  exact hw

@[irreducible] noncomputable def R65_s1 : Realisation Letter Letter.sep (strongPowPi C7 65) :=
  R30L.sigma.hetGao R35_sub inp30.sigma

theorem R65_s1_def : R65_s1 = R30L.sigma.hetGao R35_sub inp30.sigma := by unfold R65_s1; rfl

theorem R65_s1_w :
    R65_s1.w .B = 2039192944090686516848487970697063 ∧ R65_s1.w .N = 1052197521232315132063468741776738 ∧
    R65_s1.w .A = 478009125702699127858117749016963 ∧ R65_s1.w .D = 667983343164552345248285763427658 ∧
    R65_s1.w .O = 187646940385734477767608557102536 ∧ R65_s1.w .H = 187646940385734477767608557102536 ∧
    R65_s1.w .V = 187646940385734477767608557102536 := by
  rw [R65_s1_def]
  have hw := w_hetGao R30L.sigma R35_sub inp30.sigma
  rcases inp30_sigma_fields with ⟨fN, fA, fD, fHo, fHi, fVo, fVi⟩
  have hJN : inp30.sigma.J0_N.card = 1435184942161465 := by rw [fN]; exact R30hat_w.2.1
  have hJA : inp30.sigma.J0_A.card = 420235140891852 := by rw [fA]; exact R30hat_w.2.2.2.1
  have hJD : inp30.sigma.J0_D.card = 588656251987804 := by rw [fD]; exact R30hat_w.2.2.1
  have hHo : inp30.sigma.JH_out.card = 841760069965664 := by rw [fHo]; exact J30pp_out_card
  have hHi : inp30.sigma.JH_in.card = 1613966374762433 := by rw [fHi]; exact J30pp_in_card
  have hVo : inp30.sigma.JV_out.card = 841760069965664 := by rw [fVo]; exact J30pp_out_card
  have hVi : inp30.sigma.JV_in.card = 1613966374762433 := by rw [fVi]; exact J30pp_in_card
  rcases R30L_sigma_w with ⟨lB, lN, lA, lD, lO, lH, lV⟩
  rcases R35_sub_w with ⟨rB, rN, rA, rD, rO, rH, rV⟩
  rw [hJN, hJA, hJD, hHo, hHi, hVo, hVi, lB, lN, lA, lD, lO, lH, lV, rB, rN, rA, rD, rO, rH, rV] at hw
  norm_num at hw
  exact hw

@[irreducible] noncomputable def inp15_20 : HetLeftInput R15_AX :=
  HetLeftInput.ofSiblingAndParts R15_AX R15_Ahet
    R15_Ahet_OHV_eq.1 R15_Ahet_OHV_eq.2.1 R15_Ahet_OHV_eq.2.2
    J15_out J15_in J15_out J15_in
    J15_out_indep J15_in_indep J15_out_sep_in J15_out_sep_R15N
    J15_out_indep J15_in_indep J15_out_sep_in J15_out_sep_R15N

theorem inp15_20_fields :
    inp15_20.J0_N = R15_Ahet.P .N ∧ inp15_20.J0_A = R15_Ahet.P .A ∧ inp15_20.J0_D = R15_Ahet.P .D ∧
    inp15_20.JH_out = J15_out ∧ inp15_20.JH_in = J15_in ∧
    inp15_20.JV_out = J15_out ∧ inp15_20.JV_in = J15_in := by
  unfold inp15_20; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[irreducible] noncomputable def R20_sub : Realisation Letter Letter.sep (strongPowPi C7 20) :=
  R15_AX.hetGao baseR5 inp15_20

theorem R20_sub_def : R20_sub = R15_AX.hetGao baseR5 inp15_20 := by unfold R20_sub; rfl

theorem R20_sub_w :
    R20_sub.w .B = 17094983041 ∧ R20_sub.w .N = 11945553167 ∧
    R20_sub.w .A = 3587143508 ∧ R20_sub.w .D = 2611854494 ∧
    R20_sub.w .O = 1089225536 ∧ R20_sub.w .H = 1089225536 ∧ R20_sub.w .V = 1089225536 := by
  rw [R20_sub_def]
  have hw := w_hetGao R15_AX baseR5 inp15_20
  rcases inp15_20_fields with ⟨fN, fA, fD, fHo, fHi, fVo, fVi⟩
  have hJN : inp15_20.J0_N.card = 35303606 := by rw [fN]; exact R15_Ahet_w.2.1
  have hJA : inp15_20.J0_A.card = 8180458 := by rw [fA]; exact R15_Ahet_w.2.2.1
  have hJD : inp15_20.J0_D.card = 5948463 := by rw [fD]; exact R15_Ahet_w.2.2.2.1
  have hHo : inp15_20.JH_out.card = 12839823 := by rw [fHo]; exact J15_out_card
  have hHi : inp15_20.JH_in.card = 36655232 := by rw [fHi]; exact J15_in_card
  have hVo : inp15_20.JV_out.card = 12839823 := by rw [fVo]; exact J15_out_card
  have hVi : inp15_20.JV_in.card = 36655232 := by rw [fVi]; exact J15_in_card
  rcases R15_AX_w with ⟨lB, lN, lA, lD, lO, lH, lV⟩
  rcases baseR5_w with ⟨rB, rN, rA, rD, rO, rH, rV⟩
  rw [hJN, hJA, hJD, hHo, hHi, hVo, hVi, lB, lN, lA, lD, lO, lH, lV, rB, rN, rA, rD, rO, rH, rV] at hw
  norm_num at hw
  exact hw

@[irreducible] noncomputable def R50_s2 : Realisation Letter Letter.sep (strongPowPi C7 50) :=
  R30L.sigma.hetGao R20_sub inp30.sigma

theorem R50_s2_def : R50_s2 = R30L.sigma.hetGao R20_sub inp30.sigma := by unfold R50_s2; rfl

theorem R50_s2_w :
    R50_s2.w .B = 41138135602767342342736833 ∧ R50_s2.w .N = 22362147022948131400712983 ∧
    R50_s2.w .A = 9235386547253502676519186 ∧ R50_s2.w .D = 12821353558566618695810232 ∧
    R50_s2.w .O = 3689517094209355141643296 ∧ R50_s2.w .H = 3689517094209355141643296 ∧
    R50_s2.w .V = 3689517094209355141643296 := by
  rw [R50_s2_def]
  have hw := w_hetGao R30L.sigma R20_sub inp30.sigma
  rcases inp30_sigma_fields with ⟨fN, fA, fD, fHo, fHi, fVo, fVi⟩
  have hJN : inp30.sigma.J0_N.card = 1435184942161465 := by rw [fN]; exact R30hat_w.2.1
  have hJA : inp30.sigma.J0_A.card = 420235140891852 := by rw [fA]; exact R30hat_w.2.2.2.1
  have hJD : inp30.sigma.J0_D.card = 588656251987804 := by rw [fD]; exact R30hat_w.2.2.1
  have hHo : inp30.sigma.JH_out.card = 841760069965664 := by rw [fHo]; exact J30pp_out_card
  have hHi : inp30.sigma.JH_in.card = 1613966374762433 := by rw [fHi]; exact J30pp_in_card
  have hVo : inp30.sigma.JV_out.card = 841760069965664 := by rw [fVo]; exact J30pp_out_card
  have hVi : inp30.sigma.JV_in.card = 1613966374762433 := by rw [fVi]; exact J30pp_in_card
  rcases R30L_sigma_w with ⟨lB, lN, lA, lD, lO, lH, lV⟩
  rcases R20_sub_w with ⟨rB, rN, rA, rD, rO, rH, rV⟩
  rw [hJN, hJA, hJD, hHo, hHi, hVo, hVi, lB, lN, lA, lD, lO, lH, lV, rB, rN, rA, rD, rO, rH, rV] at hw
  norm_num at hw
  exact hw

private def strongPowPiCast {V : Type*} {G : SimpleGraph V} {d₁ d₂ : ℕ} (h : d₁ = d₂) :
    strongPowPi G d₁ ≃g strongPowPi G d₂ where
  toEquiv := Equiv.piCongrLeft (fun _ => V) (Fin.castOrderIso h).toEquiv
  map_rel_iff' := by
    subst h
    intro a b
    rfl

private def e155 : Fin 3 → ℕ
  | ⟨0, _⟩ => 40
  | ⟨1, _⟩ => 65
  | ⟨2, _⟩ => 50

private theorem sum_e155 : (∑ i : Fin 3, e155 i) = 155 := by decide

@[irreducible] noncomputable def R3_155 : (i : Fin 3) → Realisation Letter Letter.sep (strongPowPi C7 (e155 i))
  | ⟨0, _⟩ => R40_s0
  | ⟨1, _⟩ => R65_s1
  | ⟨2, _⟩ => R50_s2

private theorem R3_155_0 : R3_155 0 = R40_s0 := by unfold R3_155; rfl
private theorem R3_155_1 : R3_155 1 = R65_s1 := by unfold R3_155; rfl
private theorem R3_155_2 : R3_155 2 = R50_s2 := by unfold R3_155; rfl

private theorem vec3_0 (a b c : Letter) : ![a, b, c] 0 = a := rfl
private theorem vec3_1 (a b c : Letter) : ![a, b, c] 1 = b := rfl
private theorem vec3_2 (a b c : Letter) : ![a, b, c] 2 = c := rfl
private theorem vec4_0 (a b c d : Letter) : ![a, b, c, d] 0 = a := rfl
private theorem vec4_1 (a b c d : Letter) : ![a, b, c, d] 1 = b := rfl
private theorem vec4_2 (a b c d : Letter) : ![a, b, c, d] 2 = c := rfl
private theorem vec4_3 (a b c d : Letter) : ![a, b, c, d] 3 = d := rfl

@[irreducible] noncomputable def R155 : Realisation Letter Letter.sep (strongPowPi C7 155) :=
  (Realisation.multiSubst e155 R3_155 BPZTables.S3b).mapIso (strongPowPiCast sum_e155)

theorem R155_def :
    R155 = (Realisation.multiSubst e155 R3_155 BPZTables.S3b).mapIso (strongPowPiCast sum_e155) := by
  unfold R155; rfl

theorem R155_w :
    R155.w .B = 31398559828202508413609104503159115620899485238776156841255756564887950260469559 ∧
    R155.w .N = 6864519075128266828154052473694942001832305624325288599943341927666979026806966 ∧
    R155.w .A = 10806622042930967332776601926434811644232005931636574115640622907998435277755623 ∧
    R155.w .D = 15034102001391193006906258706020904137959888787748634254631892845381004209345074 ∧
    R155.w .O = 0 ∧
    R155.w .H = 2056228917234994865989868575360967854522941838326167082476672101800156685704600 ∧
    R155.w .V = 2056228917234994865989868575360967854522941838326167082476672101800156685704600 := by
  rcases R40_s0_w with ⟨w0B, w0N, w0A, w0D, w0O, w0H, w0V⟩
  rcases R65_s1_w with ⟨w1B, w1N, w1A, w1D, w1O, w1H, w1V⟩
  rcases R50_s2_w with ⟨w2B, w2N, w2A, w2D, w2O, w2H, w2V⟩
  have rw_R3_0 : ∀ a, (R3_155 0).w a = match a with
      | .B => 305594401588752181313 | .N => 176106171878551246405
      | .A => 64171129070129913256 | .D => 89250516720400951188
      | .O => 26158021392280384832 | .H => 26158021392280384832
      | .V => 26158021392280384832 := fun a => by
    unfold R3_155; cases a
    · exact w0B
    · exact w0N
    · exact w0A
    · exact w0D
    · exact w0O
    · exact w0H
    · exact w0V
  have rw_R3_1 : ∀ a, (R3_155 1).w a = match a with
      | .B => 2039192944090686516848487970697063 | .N => 1052197521232315132063468741776738
      | .A => 478009125702699127858117749016963 | .D => 667983343164552345248285763427658
      | .O => 187646940385734477767608557102536 | .H => 187646940385734477767608557102536
      | .V => 187646940385734477767608557102536 := fun a => by
    unfold R3_155; cases a
    · exact w1B
    · exact w1N
    · exact w1A
    · exact w1D
    · exact w1O
    · exact w1H
    · exact w1V
  have rw_R3_2 : ∀ a, (R3_155 2).w a = match a with
      | .B => 41138135602767342342736833 | .N => 22362147022948131400712983
      | .A => 9235386547253502676519186 | .D => 12821353558566618695810232
      | .O => 3689517094209355141643296 | .H => 3689517094209355141643296
      | .V => 3689517094209355141643296 := fun a => by
    unfold R3_155; cases a
    · exact w2B
    · exact w2N
    · exact w2A
    · exact w2D
    · exact w2O
    · exact w2H
    · exact w2V
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [R155_def, Realisation.w_mapIso, BPZTables.S3b, w_multiSubst_ofLists e155 R3_155 BPZTables.T3bList BPZTables.T3b_ok .B]
    simp only [Fin.prod_univ_three, BPZTables.T3bList, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, vec3_0, vec3_1, vec3_2, rw_R3_0, rw_R3_1, rw_R3_2]
    rfl
  · rw [R155_def, Realisation.w_mapIso, BPZTables.S3b, w_multiSubst_ofLists e155 R3_155 BPZTables.T3bList BPZTables.T3b_ok .N]
    simp only [Fin.prod_univ_three, BPZTables.T3bList, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, vec3_0, vec3_1, vec3_2, rw_R3_0, rw_R3_1, rw_R3_2]
    rfl
  · rw [R155_def, Realisation.w_mapIso, BPZTables.S3b, w_multiSubst_ofLists e155 R3_155 BPZTables.T3bList BPZTables.T3b_ok .A]
    simp only [Fin.prod_univ_three, BPZTables.T3bList, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, vec3_0, vec3_1, vec3_2, rw_R3_0, rw_R3_1, rw_R3_2]
    rfl
  · rw [R155_def, Realisation.w_mapIso, BPZTables.S3b, w_multiSubst_ofLists e155 R3_155 BPZTables.T3bList BPZTables.T3b_ok .D]
    simp only [Fin.prod_univ_three, BPZTables.T3bList, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, vec3_0, vec3_1, vec3_2, rw_R3_0, rw_R3_1, rw_R3_2]
    rfl
  · rw [R155_def, Realisation.w_mapIso, BPZTables.S3b, w_multiSubst_ofLists e155 R3_155 BPZTables.T3bList BPZTables.T3b_ok .O]
    simp only [BPZTables.T3bList, List.map_nil, List.sum_nil]
  · rw [R155_def, Realisation.w_mapIso, BPZTables.S3b, w_multiSubst_ofLists e155 R3_155 BPZTables.T3bList BPZTables.T3b_ok .H]
    simp only [Fin.prod_univ_three, BPZTables.T3bList, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, vec3_0, vec3_1, vec3_2, rw_R3_0, rw_R3_1, rw_R3_2]
    rfl
  · rw [R155_def, Realisation.w_mapIso, BPZTables.S3b, w_multiSubst_ofLists e155 R3_155 BPZTables.T3bList BPZTables.T3b_ok .V]
    simp only [Fin.prod_univ_three, BPZTables.T3bList, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, vec3_0, vec3_1, vec3_2, rw_R3_0, rw_R3_1, rw_R3_2]
    rfl

private def e620 : Fin 4 → ℕ := fun _ => 155

private theorem sum_e620 : (∑ i : Fin 4, e620 i) = 620 := by decide

def m620Card : ℕ :=
  1255225559166075558997979780220899167599874625641071729583485685368209242063963309040631281011321442698441183882072252485829578545828964333405001741654059914278426870586722886704045933654615465157332497840283119076304968304629064291853373796991015578374231780538249892793391169287500629802195192082788575013510321354561

theorem m620Card_le_pi : m620Card ≤ (strongPowPi C7 620).indepNum := by
  have hcode := le_indepNum_multiCode_ofList e620 (fun _ => R155) BPZTables.C4aList BPZTables.C4a_ok
  have hsum : (BPZTables.C4aList.map fun x => ∏ i : Fin 4, R155.w (x i)).sum = m620Card := by
    rcases R155_w with ⟨wB, wN, wA, wD, wO, wH, wV⟩
    have rw_R155 : ∀ a, R155.w a = match a with
        | .B => 31398559828202508413609104503159115620899485238776156841255756564887950260469559
        | .N => 6864519075128266828154052473694942001832305624325288599943341927666979026806966
        | .A => 10806622042930967332776601926434811644232005931636574115640622907998435277755623
        | .D => 15034102001391193006906258706020904137959888787748634254631892845381004209345074
        | .O => 0
        | .H => 2056228917234994865989868575360967854522941838326167082476672101800156685704600
        | .V => 2056228917234994865989868575360967854522941838326167082476672101800156685704600 := fun a => by
      cases a; exacts [wB, wN, wA, wD, wO, wH, wV]
    simp only [Fin.prod_univ_four, BPZTables.C4aList, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, vec4_0, vec4_1, vec4_2, vec4_3, rw_R155]
    rfl
  exact le_trans (le_trans (le_of_eq hsum.symm) hcode) (le_of_eq (iso_indepNum_eq (strongPowPiCast sum_e620)))

theorem c7_lower_m1_card : m620Card ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 620).indepNum := by
  have h1 := m620Card_le_pi
  have h2 : (strongPowPi C7 620).indepNum = (strongPowPi (SimpleGraph.cycleGraph 7) 620).indepNum := by
    rw [← strongPow_indepNum_eq_pi, iso_indepNum_eq (strongPowCongr c7IsoCycleGraph 620),
        strongPow_indepNum_eq_pi]
  omega

def c7_lower_num_m1 : ℕ := 3258835618853760
def c7_lower_den_m1 : ℕ := 1000000000000000

theorem c7_lower_m1_pow_le : c7_lower_num_m1 ^ 620 ≤ c7_lower_den_m1 ^ 620 * m620Card := by
  set_option exponentiation.threshold 4096 in
  exact nat_pow_le_of_ble rfl

theorem c7_lower_m1 :
    (c7_lower_num_m1 : ℝ) / (c7_lower_den_m1 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) := by
  have hm : m620Card ≤ (strongPow C7 620).indepNum := by
    rw [strongPow_indepNum_eq_pi]; exact m620Card_le_pi
  exact le_shannonCapacity_cycleGraph7_of_nat_pow (d := 620)
    (by decide) (by decide) hm c7_lower_m1_pow_le

theorem c7_lower_m1_gt_portfolio :
    (c7_portfolio_num : ℝ) / (c7_portfolio_den : ℝ) < (c7_lower_num_m1 : ℝ) / (c7_lower_den_m1 : ℝ) := by
  unfold c7_portfolio_num c7_portfolio_den c7_lower_num_m1 c7_lower_den_m1
  norm_num

theorem c7_lower_m1_gt_bpz_v2 :
    (3258827985920007 : ℝ) / (1000000000000000 : ℝ) < (c7_lower_num_m1 : ℝ) / (c7_lower_den_m1 : ℝ) := by
  unfold c7_lower_num_m1 c7_lower_den_m1
  norm_num

theorem c7_lower_m1_gt_tandon :
    (3258832620353266 : ℝ) / (1000000000000000 : ℝ) < (c7_lower_num_m1 : ℝ) / (c7_lower_den_m1 : ℝ) := by
  unfold c7_lower_num_m1 c7_lower_den_m1
  norm_num

theorem c7_lower_m1_sharp :
    c7_lower_den_m1 ^ 620 * m620Card < (c7_lower_num_m1 + 1) ^ 620 := by
  set_option exponentiation.threshold 4096 in
  exact Nat.le_of_ble_eq_true
    (rfl : Nat.ble (c7_lower_den_m1 ^ 620 * m620Card + 1) ((c7_lower_num_m1 + 1) ^ 620) = true)

end HigherLayersAndM620


end ShannonC7
