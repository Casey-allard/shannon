import ShannonC7.TrieVerifier
import ShannonC7.Decimal
import ShannonC7.SmallPowers
import ShannonC7.ValidTuple
import ShannonC7.HeteroLayered

/-!
# Lower-Bound Engine Unit Tests & Contract Conformance (`ShannonC7/Tests/LowerEngineTests.lean`)

Validates all 5 M3 implementation modules (`TrieVerifier`, `Decimal`, `SmallPowers`,
`ValidTuple`, `HeteroLayered`):
1. Verbatim type-signature conformance with `PROJECT.md` §4.3 and `M3_LowerEngine` scope.
2. Functional, edge-case, and concrete non-vacuity checks (including `Trie7` edge cases,
   `Decimal` edge cases, `AsymProfile` / `HeteroDAG` arithmetic, `PortSystem.finShift`,
   `LayeredProfile.upgradeProd` strictly beating `c²` on BPZ and `X_361_323_full8`,
   concrete `Trie7 1` `HeteroGadget` + terminal substitution, and a concrete live
   `Trie7 2` `LayeredTuple.ofTrie7` witness strictly upgrading `c² = 49 → 52` in pure kernel).
3. Comprehensive `#print axioms` checks confirming every key theorem across all 5 M3
   modules depends strictly on `⊆ {propext, Classical.choice, Quot.sound}`.
-/

namespace ShannonC7.Tests

open ShannonC7

/-! ## 1. Verbatim Interface Contract Conformance (`PROJECT.md` §4.3 & `SCOPE.md`) -/

section ContractChecks

-- ShannonC7.TrieVerifier
example (d : ℕ) : Type := Trie7 d
example {d : ℕ} (t : Trie7 d) : ℕ := t.card
example {d : ℕ} (t : Trie7 d) : Bool := t.isIndep
example {d : ℕ} (t₁ t₂ : Trie7 d) : Bool := t₁.disjoint t₂
example {d : ℕ} (t : Trie7 d) : Finset (StrongPowV (ZMod 7) d) := t.toFinset
example {d : ℕ} (t : Trie7 d) : t.toFinset.card = t.card := Trie7.toFinset_card t
example {d : ℕ} {t : Trie7 d} (h : t.isIndep = true) :
    (strongPow C7 d).IsIndepSet (t.toFinset : Set (StrongPowV (ZMod 7) d)) :=
  Trie7.to_indepSet_of_isIndep h
example {d : ℕ} {t : Trie7 d} (h : t.isIndep = true) :
    t.card ≤ (strongPow C7 d).indepNum :=
  Trie7.card_le_indepNum h
example {d : ℕ} {t : Trie7 d} (h : t.isIndep = true) :
    t.card ≤ (strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum :=
  Trie7.card_le_cycleGraph7_indepNum h
example {d : ℕ} (s t : Trie7 d) : Bool := s.isSubset t
example {d : ℕ} {s t : Trie7 d} (h : s.isSubset t = true) : s.toFinset ⊆ t.toFinset :=
  Trie7.toFinset_subset_of_isSubset h
example {d : ℕ} (t : Trie7 d) (w : StrongPowV (ZMod 7) d) :
    t.inClosedNbr w = true ↔ ∃ x ∈ t.toFinset, x = w ∨ (strongPow C7 d).Adj x w :=
  Trie7.inClosedNbr_eq_true_iff t w
example {d : ℕ} (t : Trie7 d) (w : StrongPowV (ZMod 7) d) :
    t.closedNbrCount w = (t.toFinset.filter (fun x => x = w ∨ (strongPow C7 d).Adj x w)).card :=
  Trie7.closedNbrCount_eq t w
example {d : ℕ} {t : Trie7 d} {w s : StrongPowV (ZMod 7) d}
    (hcnt : t.closedNbrCount w = 1) (hs_mem : t.memBool s = true)
    (hs_nbr : s = w ∨ (strongPow C7 d).Adj s w) :
    ∀ x ∈ t.toFinset, (x = w ∨ (strongPow C7 d).Adj x w) ↔ x = s :=
  Trie7.closedNbr_inter_eq_singleton hcnt hs_mem hs_nbr
example {d : ℕ} {p : StrongPowV (ZMod 7) d → Bool} {t : Trie7 d}
    (h : t.allWords p = true) : ∀ x ∈ t.toFinset, p x = true :=
  Trie7.allWords_sound h
example {d : ℕ} (p : StrongPowV (ZMod 7) d → Bool) (t : Trie7 d) :
    t.countIf p = (t.toFinset.filter (fun x => p x = true)).card :=
  Trie7.countIf_eq p t
example {d : ℕ} {p0 p1 x : Trie7 d} (h : Trie7.disjointCommonNbr p0 p1 x = true) :
    ∀ w ∈ x.toFinset,
      ¬ ((∃ u ∈ p0.toFinset, u = w ∨ (strongPow C7 d).Adj u w) ∧
         (∃ v ∈ p1.toFinset, v = w ∨ (strongPow C7 d).Adj v w)) :=
  Trie7.disjointCommonNbr_sound h
example {d : ℕ} (p0 p1 x : Trie7 d) :
    Trie7.countOutside p0 p1 x =
      (x.toFinset.filter (fun w =>
        (¬ ∃ u ∈ p0.toFinset, u = w ∨ (strongPow C7 d).Adj u w) ∧
        (¬ ∃ v ∈ p1.toFinset, v = w ∨ (strongPow C7 d).Adj v w))).card :=
  Trie7.countOutside_eq p0 p1 x

-- ShannonC7.Decimal
example {d N num den : ℕ} (hd : 0 < d) (hden : 0 < den)
    (hpow : num ^ d ≤ den ^ d * N) :
    (num : ℝ) / (den : ℝ) ≤ (N : ℝ) ^ (1 / (d : ℝ)) :=
  le_rpow_of_nat_pow hd hden hpow
example {V : Type*} [Fintype V] {G : SimpleGraph V}
    {d N num den : ℕ} (hd : 0 < d) (hden : 0 < den)
    (hN : N ≤ (strongPow G d).indepNum) (hpow : num ^ d ≤ den ^ d * N) :
    (num : ℝ) / (den : ℝ) ≤ shannonCapacity G :=
  le_shannonCapacity_of_nat_pow hd hden hN hpow
example {V : Type*} [Fintype V] {G : SimpleGraph V}
    {d N num den : ℕ} (hd : 0 < d) (hden : 0 < den)
    (hN : N ≤ (strongPowPi G d).indepNum) (hpow : num ^ d ≤ den ^ d * N) :
    (num : ℝ) / (den : ℝ) ≤ shannonCapacity G :=
  le_shannonCapacity_of_nat_pow_pi hd hden hN hpow
example {d N num den : ℕ} (hd : 0 < d) (hden : 0 < den)
    (hN : N ≤ (strongPow C7 d).indepNum) (hpow : num ^ d ≤ den ^ d * N) :
    (num : ℝ) / (den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  le_shannonCapacity_cycleGraph7_of_nat_pow hd hden hN hpow
example {num den d N : ℕ} (h : Nat.ble (num ^ d) (den ^ d * N) = true) :
    num ^ d ≤ den ^ d * N :=
  nat_pow_le_of_ble h

-- ShannonC7.SmallPowers
example : (strongPowPi (SimpleGraph.cycleGraph 7) 1).indepNum = 3 := alpha_c7_pow1
example : (strongPowPi (SimpleGraph.cycleGraph 7) 2).indepNum = 10 := alpha_c7_pow2
example : 33 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum := alpha_c7_pow3_ge
example : 108 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum := alpha_c7_pow4_ge
example : 343 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum := alpha_c7_pow5_ge_343
example : 367 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum := alpha_c7_pow5_ge_367
example : (17 : ℝ) ^ (1 / 4 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ :=
  c7_compl_lower_17
example : (325786596 : ℝ) / 100000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  c7_lower_polak_schrijver

-- ShannonC7.ValidTuple
example {V : Type*} [Fintype V] (G : SimpleGraph V) : Type _ := ValidTuple G
example : Type := Profile
example (p q : Profile) : Profile := p.star q
noncomputable example {V : Type*} [Fintype V] {G : SimpleGraph V} (τ : ValidTuple G) : Profile :=
  τ.profile
noncomputable example {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) : ValidTuple (G₁ ⊠ G₂) :=
  τ₁.star τ₂
example {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    (τ₁ : ValidTuple G₁) (τ₂ : ValidTuple G₂) :
    (τ₁.star τ₂).profile = τ₁.profile.star τ₂.profile :=
  τ₁.star_profile τ₂
example {V : Type*} [Fintype V] {G : SimpleGraph V} (τ : ValidTuple G) :
    τ.profile.a ≤ G.indepNum :=
  τ.card_le_indepNum
example {V : Type*} [Fintype V] {G : SimpleGraph V} {m : ℕ} (hm : 0 < m)
    (τ : ValidTuple (strongPow G m)) :
    (τ.profile.a : ℝ) ^ (1 / (m : ℝ)) ≤ shannonCapacity G :=
  τ.to_shannonCapacity hm
noncomputable example {V : Type*} [Fintype V] {G : SimpleGraph V} {m k : ℕ}
    (τ : ValidTuple (strongPow G m)) (t : SplitTree k) :
    ValidTuple (strongPow G (m * k)) :=
  τ.splitTree t
example : 134753 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 10).indepNum :=
  alpha_c7_pow10_ge_134753
example : (3258020737293 : ℝ) / 1000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  c7_lower_itty
example : (3258789153908 : ℝ) / 1000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  c7_lower_gao
example : (3258805369885 : ℝ) / 1000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  c7_lower_bpz_v1
example : (3258805369885465 : ℝ) / 1000000000000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  c7_lower_bpz_v1_15

-- ShannonC7.HeteroLayered
example {V : Type*} [Fintype V] (G : SimpleGraph V) : Type _ := PortCore G
example {V : Type*} [Fintype V] {G : SimpleGraph V} (c : PortCore G) : Type _ := AuxCode c
example : Type := AsymProfile
example (p q : AsymProfile) : (p.prod q).toProfile = p.toProfile.star q.toProfile :=
  p.prod_toProfile q
example {V : Type*} [Fintype V] (G : SimpleGraph V) : Type _ := HeteroGadget G
example {V : Type*} [Fintype V] {G : SimpleGraph V} (τ : ValidTuple G) : HeteroGadget G :=
  τ.toHeteroGadget
example {V : Type*} [Fintype V] {G : SimpleGraph V} (g : HeteroGadget G) : ValidTuple G :=
  g.toValidTuple
example {V : Type*} [Fintype V] {G : SimpleGraph V} (g : HeteroGadget G) :
    g.flip.asymProfile = g.asymProfile.flip :=
  g.flip_asymProfile
example {V : Type*} [Fintype V] {G : SimpleGraph V} (g : HeteroGadget G) (aux' : AuxCode g.core) :
    HeteroGadget G :=
  g.withAux aux'
example {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (g₁ : HeteroGadget G) (g₂ : HeteroGadget H) :
    (g₁.prod g₂).asymProfile = g₁.asymProfile.prod g₂.asymProfile :=
  g₁.prod_asymProfile g₂
example {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (g₁ : HeteroGadget G) (g₂ : HeteroGadget H) :
    (g₁.prodAligned g₂).asymProfile = g₁.asymProfile.prodAligned g₂.asymProfile :=
  g₁.prodAligned_asymProfile g₂
example {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (core₁ : PortCore G) (core₂ : PortCore H) (aux₁ : AuxCode core₁) (aux₂ : AuxCode core₂) :
    (core₁.I.card - core₁.S.card) * (core₂.I.card - core₂.S.card) +
      core₁.S.card * aux₂.X.card + aux₁.X.card * core₂.S.card ≤ (G ⊠ H).indepNum :=
  HeteroGadget.terminal_card_le_indepNum core₁ core₂ aux₁ aux₂
example {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (core₁ : PortCore G) (core₂ : PortCore H) {X₁ : Finset V} {X₂ : Finset W}
    (hX₁ : G.IsIndepSet (X₁ : Set V)) (hX₁_avoid : ∀ x ∈ X₁, ¬ core₁.inP1Nbr x)
    (hX₂ : H.IsIndepSet (X₂ : Set W)) :
    (core₁.I.card - core₁.S.card) * (core₂.I.card - core₂.S.card) +
      core₁.S.card * X₂.card + X₁.card * core₂.S.card ≤ (G ⊠ H).indepNum :=
  HeteroGadget.oneSidedTerminal_card_le_indepNum core₁ core₂ hX₁ hX₁_avoid hX₂
example {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {dims : Fin n → ℕ} {profs : Fin n → AsymProfile}
    (bases : (i : Fin n) → HeteroGadget (strongPow G (dims i)))
    (hprofs : ∀ i, (bases i).asymProfile = profs i) (t : HeteroTree n) :
    (t.evalProfile profs).a ≤ (strongPow G (t.dim dims)).indepNum :=
  HeteroTree.evalProfile_le_indepNum bases hprofs t
example {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {bases : Fin n → ℕ × AsymProfile}
    (hbases : ∀ i, HeteroDAG.Realizable G (bases i))
    {ops : List (HeteroOp n)} {d : ℕ} {prof : AsymProfile}
    (heval : HeteroDAG.eval bases ops = some (d, prof)) :
    prof.a ≤ (strongPow G d).indepNum :=
  HeteroDAG.eval_le_indepNum hbases heval
example {V : Type*} [Fintype V] (G : SimpleGraph V) (ι : Type*) [Fintype ι] : Type _ :=
  PortSystem G ι
example {V W ι : Type*} [Fintype V] [Fintype W] [Fintype ι]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : ι ≃ ι) (hφ : ∀ σ : ι, φ σ ≠ σ)
    (ps₁ : PortSystem G ι) (ps₂ : PortSystem H ι) :
    (ps₁.prod φ hφ ps₂).profile = ps₁.profile.star ps₂.profile :=
  PortSystem.prod_profile φ hφ ps₁ ps₂
example (k : ℕ) (hk : 2 ≤ k) (i : Fin k) : PortSystem.finShift k hk i ≠ i :=
  PortSystem.finShift_ne k hk i
example {V : Type*} [Fintype V] {G : SimpleGraph V} (g : HeteroGadget G) :
    (PortSystem.ofHeteroGadget g).profile = g.asymProfile.toProfile :=
  PortSystem.ofHeteroGadget_profile g
example {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (L₁ : LayeredTuple G) (L₂ : LayeredTuple H) :
    (L₁.upgradeProd L₂).asymProfile = L₁.layeredProfile.upgradeProd L₂.layeredProfile :=
  L₁.upgradeProd_asymProfile L₂
example {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (L₁ : LayeredTuple G) (L₂ : LayeredTuple H) :
    (L₁.prod L₂).outer.asymProfile = L₁.layeredProfile.upgradeProd L₂.layeredProfile ∧
    (L₁.prod L₂).layeredProfile.bX =
      L₁.layeredProfile.bX * L₂.layeredProfile.pY +
      L₁.layeredProfile.pY * L₂.layeredProfile.bX ∧
    L₁.layeredProfile.e * L₂.layeredProfile.e -
      L₁.layeredProfile.hY * L₂.layeredProfile.hY -
      L₁.layeredProfile.vY * L₂.layeredProfile.vY ≤ (L₁.prod L₂).layeredProfile.e ∧
    L₁.layeredProfile.dY * L₂.layeredProfile.dY ≤ (L₁.prod L₂).layeredProfile.dY ∧
    L₁.layeredProfile.pY * L₂.layeredProfile.pY ≤ (L₁.prod L₂).layeredProfile.pY :=
  L₁.prod_profile_bounds L₂
example : baseHetero5D.asymProfile = ⟨367, 8, 367, 322, 19, 26, by decide, by decide⟩ :=
  baseHetero5D_asymProfile

end ContractChecks

/-! ## 2. Functional, Edge-Case & Live Concrete Witness Tests -/

section FunctionalTests

-- 2.1 Trie7 edge cases (empty, leaf, negative disjoint, membership, subset, closedNbrCount)
example : (Trie7.empty : Trie7 5).card = 0 := rfl
example : (Trie7.empty : Trie7 5).isIndep = true := rfl
example : Trie7.leaf.card = 1 := rfl
example : Trie7.leaf.toFinset = Finset.univ := Trie7.toFinset_leaf
example : Trie7.leaf.disjoint Trie7.leaf = false := rfl
example :
    (Trie7.node .leaf .empty .empty .empty .empty .empty .empty).disjoint
      (Trie7.node .empty .leaf .empty .empty .empty .empty .empty) = false := rfl
example :
    (Trie7.node .leaf .empty .empty .empty .empty .empty .empty).disjoint
      (Trie7.node .empty .empty .leaf .empty .empty .empty .empty) = true := rfl
example :
    (Trie7.node .leaf .empty .leaf .empty .empty .empty .empty).isSubset
      (Trie7.node .leaf .empty .leaf .empty .leaf .empty .empty) = true := rfl
example :
    (Trie7.node .leaf .empty .leaf .empty .leaf .empty .empty).closedNbrCount (6, PUnit.unit) = 1 :=
  rfl
example :
    ((0, PUnit.unit) : StrongPowV (ZMod 7) 1) ∈
      (Trie7.node .leaf .empty .leaf .empty .leaf .empty .empty).toFinset :=
  Trie7.mem_toFinset_iff_memBool.mpr rfl

-- 2.2 Decimal edge cases (num = 0, N = 0, high-exponent d = 300 > 256)
example : ((0 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ) ^ (1 / ((5 : ℕ) : ℝ)) :=
  le_rpow_of_nat_pow (d := 5) (N := 0) (num := 0) (den := 7) (by decide) (by decide) (by decide)

set_option exponentiation.threshold 4096 in
example : 3 ^ 300 ≤ 1 ^ 300 * 3 ^ 300 :=
  nat_pow_le_of_ble rfl

-- 2.3 AsymProfile, HeteroDAG & PortSystem algebraic checks
private def testBaseBPZ : AsymProfile :=
  { a := 367, b := 8, c := 367, d := 322, h := 19, v := 26,
    hba := by decide, hdhv := by decide }

example : (testBaseBPZ.prod testBaseBPZ).a = 134753 := rfl
example : (testBaseBPZ.prod testBaseBPZ).b = 5152 := rfl
example : (testBaseBPZ.prod testBaseBPZ).c = 134689 := rfl
example : (testBaseBPZ.prod testBaseBPZ).d = 105709 := rfl

private def testZeroV : AsymProfile :=
  { a := 10, b := 2, c := 8, d := 5, h := 3, v := 0,
    hba := by decide, hdhv := by decide }

example : (testZeroV.prodAligned testZeroV).v = 0 := rfl

private def testDag40 : List (HeteroOp 1) :=
  [ .base 0, .prod 0 0, .prod 1 1, .prod 2 2, .prod 3 3, .prod 4 4, .prod 5 3 ]

example :
    (HeteroDAG.eval (fun _ : Fin 1 => (5, testBaseBPZ)) testDag40).map Prod.fst = some 200 :=
  rfl

-- Live HeteroDAG instantiation using `baseHetero5D` on `C7`!
theorem test_heteroDAG_live_d10 :
    134753 ≤ (strongPow C7 10).indepNum := by
  have hreal : ∀ _ : Fin 1, HeteroDAG.Realizable C7 (5, testBaseBPZ) :=
    fun _ => ⟨baseHetero5D, baseHetero5D_asymProfile⟩
  exact HeteroDAG.eval_le_indepNum hreal (ops := [.base 0, .prod 0 0]) (d := 10)
    (prof := testBaseBPZ.prod testBaseBPZ) rfl

-- Live HeteroDAG root-level terminal substitution test!
theorem test_heteroDAG_terminal_live_d10 :
    134753 ≤ (strongPow C7 10).indepNum := by
  have hreal : ∀ _ : Fin 1, HeteroDAG.Realizable C7 (5, testBaseBPZ) :=
    fun _ => ⟨baseHetero5D, baseHetero5D_asymProfile⟩
  exact HeteroDAG.eval_terminal_le_indepNum hreal (ops₁ := [.base 0]) (ops₂ := [.base 0])
    (d₁ := 5) (d₂ := 5) (p₁ := testBaseBPZ) (p₂ := testBaseBPZ) rfl rfl

-- PortSystem cyclic derangement finShift 3 wrap-around
example : PortSystem.finShift 3 (by decide) ⟨0, by decide⟩ = ⟨1, by decide⟩ := rfl
example : PortSystem.finShift 3 (by decide) ⟨1, by decide⟩ = ⟨2, by decide⟩ := rfl
example : PortSystem.finShift 3 (by decide) ⟨2, by decide⟩ = ⟨0, by decide⟩ := rfl

-- 2.4 LayeredProfile.upgradeProd strictly beats homogeneous `c²` (BPZ b_X=6 & X_361_323_full8 b_X=8)
private def testLayeredBPZ : LayeredProfile :=
  { outer := testBaseBPZ, bX := 6, e := 367, dY := 322, hY := 19, vY := 26, pY := 280,
    hbXd := by decide, hYsum := by decide, hpYdY := by decide }

example : (testLayeredBPZ.upgradeProd testLayeredBPZ).a = 134753 := rfl
example : (testLayeredBPZ.upgradeProd testLayeredBPZ).c = 134725 := rfl
example : (testLayeredBPZ.upgradeProd testLayeredBPZ).d = 105745 := rfl
example : 134689 < (testLayeredBPZ.upgradeProd testLayeredBPZ).c := by decide
example : 105709 < (testLayeredBPZ.upgradeProd testLayeredBPZ).d := by decide

private def testLayeredFull8 : LayeredProfile :=
  { outer := ⟨367, 8, 361, 323, 18, 20, by decide, by decide⟩,
    bX := 8, e := 367, dY := 322, hY := 19, vY := 26, pY := 270,
    hbXd := by decide, hYsum := by decide, hpYdY := by decide }

example : (testLayeredFull8.upgradeProd testLayeredFull8).c = 130481 := rfl
example : (testLayeredFull8.upgradeProd testLayeredFull8).d = 105821 := rfl
example : 361 * 361 < (testLayeredFull8.upgradeProd testLayeredFull8).c := by decide
example : 323 * 323 + 38 * 38 < (testLayeredFull8.upgradeProd testLayeredFull8).d := by decide

-- 2.5 Concrete Trie7 1 HeteroGadget + PortSystem.ofHeteroGadget + Terminal Substitution
private def c7_1_I : Trie7 1 := .node .leaf .empty .leaf .empty .leaf .empty .empty
private def c7_1_P0 : Trie7 1 := .node .leaf .empty .empty .empty .empty .empty .empty
private def c7_1_P1 : Trie7 1 := .node .empty .empty .empty .empty .empty .empty .leaf
private def c7_1_X : Trie7 1 := .node .empty .empty .leaf .empty .leaf .empty .empty
private def c7_1_ports : List (PortEntry 1) :=
  [((0, PUnit.unit), (0, PUnit.unit), (6, PUnit.unit))]

private theorem c7_1_nodup : (c7_1_ports.map Prod.fst).Nodup := by decide

private def c7_1_core : PortCore (strongPow C7 1) :=
  PortCore.ofTrie7 c7_1_I c7_1_P0 c7_1_P1 c7_1_ports rfl rfl rfl c7_1_nodup rfl

private def c7_1_aux : AuxCode c7_1_core :=
  AuxCode.ofTrie7 (tI := c7_1_I) (tP0 := c7_1_P0) (tP1 := c7_1_P1) (ports := c7_1_ports)
    (hI := rfl) (hP0 := rfl) (hP1 := rfl) (hnodup := c7_1_nodup) (hcheck := rfl)
    rfl rfl c7_1_X rfl rfl

private def c7_1_gadget : HeteroGadget (strongPow C7 1) := ⟨c7_1_core, c7_1_aux⟩

private theorem c7_1_gadget_profile :
    c7_1_gadget.asymProfile = ⟨3, 1, 2, 2, 0, 0, by decide, by decide⟩ := by
  have h := HeteroGadget.ofTrie7_asymProfile
    (tI := c7_1_I) (tP0 := c7_1_P0) (tP1 := c7_1_P1) (ports := c7_1_ports)
    (hI := rfl) (hP0 := rfl) (hP1 := rfl) (hnodup := c7_1_nodup) (hcheck := rfl)
    rfl rfl c7_1_X rfl rfl
  dsimp only at h
  rcases h with ⟨ha, hb, hc, hd, hh, hv⟩
  change c7_1_gadget.asymProfile.a = 3 at ha
  change c7_1_gadget.asymProfile.b = 1 at hb
  change c7_1_gadget.asymProfile.c = 2 at hc
  change c7_1_gadget.asymProfile.d = 2 at hd
  change c7_1_gadget.asymProfile.h = 0 at hh
  change c7_1_gadget.asymProfile.v = 0 at hv
  cases hp : c7_1_gadget.asymProfile with
  | mk a b c d h' v hba hdhv =>
    rw [hp] at ha hb hc hd hh hv
    simp only [AsymProfile.mk.injEq]
    exact ⟨ha, hb, hc, hd, hh, hv⟩

theorem test_c7_1_gadget_profile :
    ∃ g : HeteroGadget (strongPow C7 1),
      g.asymProfile = ⟨3, 1, 2, 2, 0, 0, by decide, by decide⟩ :=
  ⟨c7_1_gadget, c7_1_gadget_profile⟩

theorem test_c7_1_portSystem_prod :
    ∃ ps : PortSystem (strongPow C7 1 ⊠ strongPow C7 1) Bool, ps.profile.a = 8 := by
  refine ⟨(PortSystem.ofHeteroGadget c7_1_gadget).prod
    (Equiv.swap false true) (by decide) (PortSystem.ofHeteroGadget c7_1_gadget), ?_⟩
  rw [PortSystem.prod_profile, PortSystem.ofHeteroGadget_profile, c7_1_gadget_profile]
  rfl

-- One-sided terminal substitution on `c7_1_gadget` (`v₁ = 0`, unconstrained `X₂ = c7_1_I` of size 3):
-- size = (3-1)*(3-1) + 1*3 + 2*1 = 9 ≤ α(C7^2)
theorem test_c7_1_oneSidedTerminal :
    9 ≤ (strongPow C7 1 ⊠ strongPow C7 1).indepNum := by
  have hcard := HeteroGadget.oneSidedTerminal_card_le_indepNum c7_1_core c7_1_core
    (X₁ := c7_1_aux.X) (X₂ := c7_1_core.I) c7_1_aux.indep_X ?_ c7_1_core.indep_I
  · have ha : c7_1_core.I.card = 3 := by
      have := congrArg AsymProfile.a c7_1_gadget_profile; exact this
    have hb : c7_1_core.S.card = 1 := by
      have := congrArg AsymProfile.b c7_1_gadget_profile; exact this
    have hc : c7_1_aux.X.card = 2 := by
      have := congrArg AsymProfile.c c7_1_gadget_profile; exact this
    rw [ha, hb, hc] at hcard
    exact hcard
  · intro x hx h1
    have hv0 : c7_1_aux.VSlice.card = 0 := congrArg AsymProfile.v c7_1_gadget_profile
    have hxV : x ∈ c7_1_aux.VSlice := c7_1_aux.mem_VSlice.mpr ⟨hx, h1⟩
    exact absurd (Finset.card_pos.mpr ⟨x, hxV⟩) (by omega)

-- 2.6 Concrete live `Trie7 2` `LayeredTuple.ofTrie7` witness strictly upgrading `c² = 49 → 52`!
private def l2d_I : Trie7 2 :=
  .node (.node .leaf .empty .empty .leaf .empty .leaf .empty) .empty
    (.node .leaf .empty .empty .leaf .empty .leaf .empty) .empty
    (.node .leaf .empty .empty .leaf .empty .leaf .empty) .empty .empty

private def l2d_P0 : Trie7 2 :=
  .node (.node .leaf .empty .empty .empty .empty .empty .empty)
    .empty .empty .empty .empty .empty .empty

private def l2d_P1 : Trie7 2 :=
  .node (.node .empty .leaf .empty .empty .empty .empty .empty)
    .empty .empty .empty .empty .empty .empty

private def l2d_X : Trie7 2 :=
  .node (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty
    (.node .leaf .empty .leaf .empty .leaf .empty .empty) .empty
    (.node .leaf .empty .leaf .empty .leaf .empty .empty) .empty

private def l2d_Q0 : Trie7 2 :=
  .node .empty .empty .empty
    (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty

private def l2d_Q1 : Trie7 2 :=
  .node .empty .empty
    (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty

private def l2d_Y : Trie7 2 :=
  .node (.node .empty .empty .empty .leaf .empty .empty .empty)
    (.node .empty .empty .empty .empty .empty .leaf .empty)
    (.node .empty .empty .leaf .empty .empty .empty .empty)
    (.node .empty .empty .empty .empty .leaf .empty .empty)
    (.node .empty .leaf .empty .empty .empty .empty .leaf)
    (.node .empty .empty .empty .leaf .empty .empty .empty)
    (.node .empty .empty .empty .empty .empty .leaf .empty)

private def l2d_portsOut : List (PortEntry 2) :=
  [((0, 0, PUnit.unit), (0, 0, PUnit.unit), (0, 1, PUnit.unit))]

private def l2d_portsInt : List (PortEntry 2) :=
  [((3, 0, PUnit.unit), (3, 0, PUnit.unit), (2, 0, PUnit.unit))]

private theorem l2d_I_indep : l2d_I.isIndep = true := rfl
private theorem l2d_P0_indep : l2d_P0.isIndep = true := rfl
private theorem l2d_P1_indep : l2d_P1.isIndep = true := rfl
private theorem l2d_nodupOut : (l2d_portsOut.map Prod.fst).Nodup := by decide
private theorem l2d_checkOut : checkPortTriples l2d_I l2d_P0 l2d_P1 l2d_portsOut = true := rfl
private theorem l2d_cardP0 : l2d_P0.card = l2d_portsOut.length := rfl
private theorem l2d_cardP1 : l2d_P1.card = l2d_portsOut.length := rfl
private theorem l2d_X_indep : l2d_X.isIndep = true := rfl
private theorem l2d_disjX : Trie7.disjointCommonNbr l2d_P0 l2d_P1 l2d_X = true := rfl
private theorem l2d_Q0_indep : l2d_Q0.isIndep = true := rfl
private theorem l2d_Q1_indep : l2d_Q1.isIndep = true := rfl
private theorem l2d_nodupInt : (l2d_portsInt.map Prod.fst).Nodup := by decide
private theorem l2d_checkInt : checkPortTriples l2d_X l2d_Q0 l2d_Q1 l2d_portsInt = true := rfl
private theorem l2d_cardQ0 : l2d_Q0.card = l2d_portsInt.length := rfl
private theorem l2d_cardQ1 : l2d_Q1.card = l2d_portsInt.length := rfl
private theorem l2d_intOut : checkIntPortsOutside l2d_P0 l2d_P1 l2d_portsInt = true := rfl
private theorem l2d_Y_indep : l2d_Y.isIndep = true := rfl
private theorem l2d_disjY_int : Trie7.disjointCommonNbr l2d_Q0 l2d_Q1 l2d_Y = true := rfl
private theorem l2d_disjY_out : Trie7.disjointCommonNbr l2d_P0 l2d_P1 l2d_Y = true := rfl

private def l2d_layered : LayeredTuple (strongPow C7 2) :=
  LayeredTuple.ofTrie7 l2d_I l2d_P0 l2d_P1 l2d_X l2d_Q0 l2d_Q1 l2d_Y l2d_portsOut l2d_portsInt
    l2d_I_indep l2d_P0_indep l2d_P1_indep l2d_nodupOut l2d_checkOut l2d_cardP0 l2d_cardP1
    l2d_X_indep l2d_disjX l2d_Q0_indep l2d_Q1_indep l2d_nodupInt l2d_checkInt
    l2d_cardQ0 l2d_cardQ1 l2d_intOut l2d_Y_indep l2d_disjY_int l2d_disjY_out

/-- Concrete pure-kernel non-vacuity test: `LayeredTuple (strongPow C7 2)` is inhabited
and strictly upgrades `c² = 49 → 52` and `d² = 49 → 52` on `strongPow C7 2 ⊠ strongPow C7 2`! -/
theorem test_layeredTuple_live_upgrade_2D :
    ∃ L : LayeredTuple (strongPow C7 2),
      L.layeredProfile.outer.c = 7 ∧
      (L.upgradeProd L).asymProfile.c = 52 ∧
      (L.upgradeProd L).asymProfile.d = 52 ∧
      L.layeredProfile.outer.c ^ 2 < (L.upgradeProd L).asymProfile.c := by
  refine ⟨l2d_layered, ?_⟩
  have hp := LayeredTuple.ofTrie7_layeredProfile
    (tI := l2d_I) (tP0 := l2d_P0) (tP1 := l2d_P1) (tX := l2d_X)
    (tQ0 := l2d_Q0) (tQ1 := l2d_Q1) (tY := l2d_Y)
    (portsOut := l2d_portsOut) (portsInt := l2d_portsInt)
    (hI := l2d_I_indep) (hP0 := l2d_P0_indep) (hP1 := l2d_P1_indep)
    (hnodupOut := l2d_nodupOut) (hcheckOut := l2d_checkOut)
    (hcardP0 := l2d_cardP0) (hcardP1 := l2d_cardP1)
    (hX := l2d_X_indep) (hdisjX := l2d_disjX)
    (hQ0 := l2d_Q0_indep) (hQ1 := l2d_Q1_indep)
    (hnodupInt := l2d_nodupInt) (hcheckInt := l2d_checkInt)
    (hcardQ0 := l2d_cardQ0) (hcardQ1 := l2d_cardQ1)
    (hIntOut := l2d_intOut) (hY := l2d_Y_indep)
    (hdisjY_int := l2d_disjY_int) (hdisjY_out := l2d_disjY_out)
  dsimp only at hp
  rcases hp with ⟨_, _, hc, hd, hh, hv, hbX, he, hdY, _, _⟩
  change l2d_layered.layeredProfile.outer.c = 7 at hc
  change l2d_layered.layeredProfile.outer.d = 7 at hd
  change l2d_layered.layeredProfile.outer.h = 0 at hh
  change l2d_layered.layeredProfile.outer.v = 0 at hv
  change l2d_layered.layeredProfile.bX = 1 at hbX
  change l2d_layered.layeredProfile.e = 8 at he
  change l2d_layered.layeredProfile.dY = 8 at hdY
  have hup := l2d_layered.upgradeProd_asymProfile l2d_layered
  have hupc : (l2d_layered.upgradeProd l2d_layered).asymProfile.c = 52 := by
    rw [hup]; simp only [LayeredProfile.upgradeProd, hc, hbX, he]
  have hupd : (l2d_layered.upgradeProd l2d_layered).asymProfile.d = 52 := by
    rw [hup]; simp only [LayeredProfile.upgradeProd, hd, hh, hv, hbX, hdY]
  exact ⟨hc, hupc, hupd, by rw [hc, hupc]; decide⟩

end FunctionalTests

/-! ## 3. Comprehensive `#print axioms` Checks Across All 5 M3 Modules -/

-- ShannonC7.TrieVerifier
#print axioms ShannonC7.Trie7.toFinset_card
#print axioms ShannonC7.Trie7.disjoint_sound
#print axioms ShannonC7.Trie7.to_indepSet_of_isIndep
#print axioms ShannonC7.Trie7.card_le_indepNum
#print axioms ShannonC7.Trie7.card_le_cycleGraph7_indepNum
#print axioms ShannonC7.Trie7.toFinset_subset_of_isSubset
#print axioms ShannonC7.Trie7.inClosedNbr_eq_true_iff
#print axioms ShannonC7.Trie7.closedNbrCount_eq
#print axioms ShannonC7.Trie7.closedNbr_inter_eq_singleton
#print axioms ShannonC7.Trie7.allWords_sound
#print axioms ShannonC7.Trie7.countIf_eq
#print axioms ShannonC7.Trie7.disjointCommonNbr_sound
#print axioms ShannonC7.Trie7.countOutside_eq

-- ShannonC7.Decimal
#print axioms ShannonC7.le_rpow_of_nat_pow
#print axioms ShannonC7.le_shannonCapacity_of_nat_pow
#print axioms ShannonC7.le_shannonCapacity_of_nat_pow_pi
#print axioms ShannonC7.le_shannonCapacity_cycleGraph7_of_nat_pow
#print axioms ShannonC7.nat_pow_le_of_ble

-- ShannonC7.SmallPowers
#print axioms ShannonC7.alpha_c7_pow1
#print axioms ShannonC7.alpha_c7_pow2
#print axioms ShannonC7.alpha_c7_pow3_ge
#print axioms ShannonC7.alpha_c7_pow4_ge
#print axioms ShannonC7.alpha_c7_pow5_ge_343
#print axioms ShannonC7.alpha_c7_pow5_ge_367
#print axioms ShannonC7.c7_compl_lower_17
#print axioms ShannonC7.c7_lower_polak_schrijver

-- ShannonC7.ValidTuple
#print axioms ShannonC7.ValidTuple.congr_profile
#print axioms ShannonC7.ValidTuple.star_profile
#print axioms ShannonC7.ValidTuple.card_le_indepNum
#print axioms ShannonC7.ValidTuple.to_shannonCapacity
#print axioms ShannonC7.ValidTuple.evalTree_profile
#print axioms ShannonC7.ValidTuple.evalTree_a_le_cycleGraph7_indepNum
#print axioms ShannonC7.ValidTuple.le_shannonCapacity_cycleGraph7_of_evalTree
#print axioms ShannonC7.ValidTuple.ofTrie7_profile_eq
#print axioms ShannonC7.baseTuple5D_profile
#print axioms ShannonC7.alpha_c7_pow10_ge_134753
#print axioms ShannonC7.c7_lower_itty
#print axioms ShannonC7.c7_lower_gao
#print axioms ShannonC7.c7_lower_bpz_v1
#print axioms ShannonC7.c7_lower_bpz_v1_15

-- ShannonC7.HeteroLayered
#print axioms ShannonC7.AsymProfile.prod_toProfile
#print axioms ShannonC7.HeteroGadget.flip_asymProfile
#print axioms ShannonC7.HeteroGadget.mapIso_asymProfile
#print axioms ShannonC7.HeteroGadget.prod_asymProfile
#print axioms ShannonC7.HeteroGadget.prodAligned_asymProfile
#print axioms ShannonC7.HeteroGadget.terminal_card_le_indepNum
#print axioms ShannonC7.HeteroGadget.oneSidedTerminal_card_le_indepNum
#print axioms ShannonC7.HeteroTree.evalGadget_asymProfile
#print axioms ShannonC7.HeteroTree.evalProfile_le_indepNum
#print axioms ShannonC7.HeteroDAG.eval_le_indepNum
#print axioms ShannonC7.HeteroDAG.eval_terminal_le_indepNum
#print axioms ShannonC7.PortSystem.prod_profile
#print axioms ShannonC7.PortSystem.finShift_ne
#print axioms ShannonC7.PortSystem.ofColoring
#print axioms ShannonC7.PortSystem.ofHeteroGadget_profile
#print axioms ShannonC7.LayeredTuple.upgradeProd_asymProfile
#print axioms ShannonC7.LayeredTuple.prod_profile_bounds
#print axioms ShannonC7.HeteroGadget.ofTrie7_asymProfile
#print axioms ShannonC7.LayeredTuple.ofTrie7_layeredProfile
#print axioms ShannonC7.baseHetero5D_asymProfile

-- Local test theorems
#print axioms ShannonC7.Tests.test_heteroDAG_live_d10
#print axioms ShannonC7.Tests.test_heteroDAG_terminal_live_d10
#print axioms ShannonC7.Tests.test_c7_1_gadget_profile
#print axioms ShannonC7.Tests.test_c7_1_portSystem_prod
#print axioms ShannonC7.Tests.test_c7_1_oneSidedTerminal
#print axioms ShannonC7.Tests.test_layeredTuple_live_upgrade_2D

end ShannonC7.Tests
