import ShannonC7.CycleC7
import ShannonC7.TrieVerifier
import ShannonC7.Decimal

/-!
# Certified Small Strong Powers of `C7` (`d = 1..5`) and `C7ᶜ` (`d = 4`)

This module proves all 7 small-power theorems in the pure Lean 4 kernel:
1. `alpha_c7_pow1`: `α(C7^⊠1) = 3` (exact via `c7_sliceDoubleCount` + 3-word witness),
2. `alpha_c7_pow2`: `α(C7^⊠2) = 10` (exact via `c7_sliceDoubleCount` + 10-word witness),
3. `alpha_c7_pow3_ge`: `33 ≤ α(C7^⊠3)` (pure-kernel `Trie7 3`),
4. `alpha_c7_pow4_ge`: `108 ≤ α(C7^⊠4)` (pure-kernel `Trie7 4`),
5. `alpha_c7_pow5_ge_343`: `343 ≤ α(C7^⊠5)` (algebraic 3D linear subspace in `𝔽₇⁵`),
6. `alpha_c7_pow5_ge_367`: `367 ≤ α(C7^⊠5)` (canonical 8-private-pair Polak–Schrijver set,
   exported as `polakSchrijver367Trie` and `ps367Slice0..ps367Slice6` for reuse by `ValidTuple`),
7. `c7_compl_lower_17`: `17^(1/4) ≤ Θ(C7ᶜ)` (Bohman–Holzman negation-symmetric 17-word witness).
-/

namespace ShannonC7

/-! ## General Bridge Helpers -/

/-- Bridging `strongPowPi (cycleGraph 7) d` independence number to `strongPow C7 d`. -/
theorem cycleGraph7_strongPowPi_indepNum_eq (d : ℕ) :
    (strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum = (strongPow C7 d).indepNum := by
  rw [← strongPow_indepNum_eq_pi, ← iso_indepNum_eq (strongPowCongr c7IsoCycleGraph d)]

/-- Graph isomorphism induces an isomorphism on graph complements. -/
def isoCompl {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    simp only [SimpleGraph.compl_adj, RelIso.coe_fn_toEquiv, e.injective.ne_iff, e.map_adj_iff]

/-- Pure-kernel soundness of a `List.Pairwise` non-adjacency certificate into `Finset` `IsIndepSet`. -/
theorem isIndepSet_of_pairwise {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {l : List V} (hpw : l.Pairwise (fun u v => ¬ G.Adj u v)) :
    G.IsIndepSet (l.toFinset : Set V) := by
  induction l with
  | nil => simp [SimpleGraph.IsIndepSet]
  | cons a tl ih =>
    rw [List.pairwise_cons] at hpw
    intro u hu v hv huv hadj
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_cons] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact huv rfl
    · exact hpw.1 v hv hadj
    · exact hpw.1 u hu hadj.symm
    · exact ih hpw.2 (by simpa using hu) (by simpa using hv) huv hadj

/-- Pure-kernel lower bound `l.length ≤ G.indepNum` from `List.Nodup` and `List.Pairwise`. -/
theorem length_le_indepNum_of_list {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}
    {l : List V} (hnodup : l.Nodup) (hpw : l.Pairwise (fun u v => ¬ G.Adj u v)) :
    l.length ≤ G.indepNum := by
  rw [← List.toFinset_card_of_nodup hnodup]
  exact (isIndepSet_of_pairwise hpw).card_le_indepNum

/-! ## Exact Power `d = 1`: `α(C7^⊠1) = 3` -/

private def c7Pow1List : List (StrongPowV (ZMod 7) 1) :=
  [(0, PUnit.unit), (2, PUnit.unit), (4, PUnit.unit)]

private theorem c7Pow1_indepNum_eq : (strongPow C7 1).indepNum = 3 := by
  have hle : (strongPow C7 1).indepNum ≤ 3 := by
    have hdc := c7_sliceDoubleCount (⊥ : SimpleGraph PUnit.{1})
    have hbot : (⊥ : SimpleGraph PUnit.{1}).indepNum ≤ 1 := by
      simpa using indepNum_le_card (⊥ : SimpleGraph PUnit.{1})
    change 2 * (strongPow C7 1).indepNum ≤ 7 * (⊥ : SimpleGraph PUnit.{1}).indepNum at hdc
    omega
  have hge : 3 ≤ (strongPow C7 1).indepNum :=
    length_le_indepNum_of_list (l := c7Pow1List) (by decide) (by decide)
  omega

/-- Exact independence number of `C7^⊠1`: `α(C7) = 3`. -/
theorem alpha_c7_pow1 : (strongPowPi (SimpleGraph.cycleGraph 7) 1).indepNum = 3 := by
  rw [cycleGraph7_strongPowPi_indepNum_eq 1, c7Pow1_indepNum_eq]

/-! ## Exact Power `d = 2`: `α(C7^⊠2) = 10` -/

private def c7Pow2List : List (StrongPowV (ZMod 7) 2) :=
  [ (0, 1, PUnit.unit), (0, 3, PUnit.unit), (1, 5, PUnit.unit), (2, 0, PUnit.unit),
    (2, 2, PUnit.unit), (3, 4, PUnit.unit), (4, 1, PUnit.unit), (4, 6, PUnit.unit),
    (5, 3, PUnit.unit), (6, 5, PUnit.unit) ]

private theorem c7Pow2_indepNum_eq : (strongPow C7 2).indepNum = 10 := by
  have hle : (strongPow C7 2).indepNum ≤ 10 := by
    have hdc := c7_sliceDoubleCount (strongPow C7 1)
    change 2 * (strongPow C7 2).indepNum ≤ 7 * (strongPow C7 1).indepNum at hdc
    rw [c7Pow1_indepNum_eq] at hdc
    omega
  have hge : 10 ≤ (strongPow C7 2).indepNum :=
    length_le_indepNum_of_list (l := c7Pow2List) (by decide) (by decide)
  omega

/-- Exact independence number of `C7^⊠2`: `α(C7^⊠2) = 10`. -/
theorem alpha_c7_pow2 : (strongPowPi (SimpleGraph.cycleGraph 7) 2).indepNum = 10 := by
  rw [cycleGraph7_strongPowPi_indepNum_eq 2, c7Pow2_indepNum_eq]

/-! ## Pure-Kernel Radix-7 Trie Witnesses (`d = 3, 4, 5`) -/

/-- Canonical 33-word independent set in `C7^⊠3` as a sparse `Trie7 3`. -/
def c7Pow3Trie : Trie7 3 :=
  .node
    (.node
      .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty
      (.node .empty .empty .leaf .empty .leaf .empty .empty) .empty
      (.node .leaf .empty .empty .empty .empty .leaf .empty))
    (.node
      .empty (.node .empty .empty .empty .empty .leaf .empty .leaf) .empty
      (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty
      (.node .empty .empty .empty .leaf .empty .empty .empty))
    (.node
      .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty
      (.node .empty .empty .empty .leaf .empty .leaf .empty) .empty
      (.node .empty .empty .empty .empty .empty .empty .leaf)
      (.node .empty .leaf .empty .empty .empty .empty .empty))
    (.node
      (.node .empty .empty .empty .empty .leaf .empty .leaf) .empty
      (.node .leaf .empty .empty .empty .empty .empty .empty) .empty
      (.node .empty .leaf .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
    (.node
      (.node .empty .empty .leaf .empty .empty .empty .empty) .empty
      (.node .empty .empty .empty .empty .empty .leaf .empty)
      (.node .empty .empty .empty .leaf .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty)
    (.node
      (.node .empty .empty .empty .empty .empty .leaf .empty)
      (.node .leaf .empty .empty .empty .empty .empty .empty) .empty
      (.node .empty .leaf .empty .empty .empty .empty .empty) .empty
      (.node .empty .empty .leaf .empty .leaf .empty .empty)
      (.node .leaf .empty .empty .empty .empty .empty .empty))
    (.node
      (.node .empty .empty .empty .leaf .empty .empty .empty) .empty
      (.node .empty .empty .empty .leaf .empty .leaf .empty) .empty
      (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty)

/-- Canonical 108-word independent set in `C7^⊠4` as a sparse `Trie7 4`. -/
def c7Pow4Trie : Trie7 4 :=
  .node
    (.node
      (.node
        .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty
        (.node .empty .empty .empty .leaf .empty .empty .empty))
      (.node
        .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty) .empty)
      (.node
        (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty
        (.node .empty .empty .empty .empty .leaf .empty .empty)
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty
        (.node .empty .empty .leaf .empty .empty .empty .empty))
      (.node
        .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty
        (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty))
    (.node
      (.node
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty
        (.node .empty .empty .empty .leaf .empty .empty .empty)
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node
        (.node .leaf .empty .empty .empty .empty .empty .empty) .empty
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty
        (.node .empty .empty .leaf .empty .empty .empty .empty))
      (.node
        .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .empty .leaf) .empty)
      (.node
        (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node
        .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .empty .leaf) .empty))
    (.node
      (.node
        .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node
        .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty)
      (.node
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty
        (.node .empty .empty .leaf .empty .empty .empty .empty)
        (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty)
      (.node
        (.node .empty .empty .empty .empty .empty .empty .leaf) .empty
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty
        (.node .empty .leaf .empty .empty .empty .empty .empty))
      (.node
        .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty
        (.node .empty .leaf .empty .empty .empty .empty .empty)))
    (.node
      (.node
        .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty
        (.node .empty .empty .empty .empty .empty .leaf .empty))
      (.node
        .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty))
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node
        .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty
        (.node .empty .leaf .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty))
      (.node
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .leaf .empty) .empty .empty))
    (.node
      (.node
        .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node
        .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty
        (.node .empty .leaf .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .leaf .empty))
      (.node
        .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty))
      (.node
        .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty)))
    (.node
      (.node
        .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty
        (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node
        .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .empty .leaf))
      (.node
        .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node
        .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty
        (.node .leaf .empty .empty .empty .empty .leaf .empty) .empty .empty .empty)
      (.node
        .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty
        (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty
        (.node .empty .empty .empty .empty .leaf .empty .leaf) .empty .empty))
    (.node
      (.node
        .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty
        (.node .empty .empty .empty .empty .empty .leaf .empty)
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node
        .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty
        (.node .empty .empty .empty .leaf .empty .empty .empty))
      (.node
        .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty
        (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node
        .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty) .empty)
      (.node
        .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      (.node
        .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty
        (.node .empty .empty .empty .empty .empty .empty .leaf)))

/-- Coordinate-0 slice `0` (55 words) of the canonical 8-private-pair Polak–Schrijver 367-word set. -/
def ps367Slice0 : Trie7 4 :=
  .node
    (.node
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty)
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty)
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty))
    (.node
      (.node (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty .empty)
      (.node (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty)
      (.node .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty))
    (.node
      (.node .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty))
      (.node
        .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty))
    (.node
      (.node
        .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)
        (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty)
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty))
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty))
    (.node
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty))
      (.node .empty .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty)))
    (.node
      (.node
        .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty))
    (.node
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)))

/-- Coordinate-0 slice `1` (52 words) of the canonical 8-private-pair Polak–Schrijver 367-word set. -/
def ps367Slice1 : Trie7 4 :=
  .node
    (.node
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty .empty)
      (.node (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty))
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty))
    (.node
      (.node
        .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty))
    (.node
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)
        (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty)
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)))
    (.node
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty))
      (.node .empty .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node
        .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty)
      .empty
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty))
    (.node
      .empty
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node
        .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty)
        (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty)
      (.node .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      .empty)
    (.node
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf))
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .leaf .empty) .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty))
    (.node
      (.node .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty)
      (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty))

/-- Coordinate-0 slice `2` (53 words) of the canonical 8-private-pair Polak–Schrijver 367-word set. -/
def ps367Slice2 : Trie7 4 :=
  .node
    (.node
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)))
    (.node
      (.node (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)
        (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty)
      .empty
      (.node (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty .empty))
    (.node
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty))
      (.node .empty .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty
        (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty))
    (.node
      (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty)
      (.node .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf))
      (.node .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty))
    (.node
      (.node .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf))
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node
        .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty))
    (.node
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty)
      (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty))
    (.node
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty)
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty)
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty .empty)
      (.node (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty))

/-- Coordinate-0 slice `3` (52 words) of the canonical 8-private-pair Polak–Schrijver 367-word set. -/
def ps367Slice3 : Trie7 4 :=
  .node
    (.node
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty)
      (.node .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty))
    (.node
      (.node .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty)
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty))
      (.node .empty .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty))
      (.node .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty))
    (.node
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .leaf) .empty .empty)
      (.node .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty)
      (.node .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty))
    (.node
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf))
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty)
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty)
      .empty
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty)))
    (.node
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty)
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty)
      (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      .empty)
    (.node
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty)
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty)
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)))
    (.node
      (.node (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty .empty))

/-- Coordinate-0 slice `4` (55 words) of the canonical 8-private-pair Polak–Schrijver 367-word set. -/
def ps367Slice4 : Trie7 4 :=
  .node
    (.node
      (.node .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .leaf .empty) .empty .empty)
      (.node .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty)
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty))
    (.node
      (.node .empty .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .leaf) .empty .empty)
      (.node .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty)))
    (.node
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf))
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty)
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty)
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty))
    (.node
      (.node .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty)
      (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node
        .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty
        (.node .leaf .empty .empty .empty .empty .empty .empty) .empty)
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty))
    (.node
      (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty)
      (.node .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty)
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty))
    (.node
      (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty .empty)
      (.node (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty)
      (.node
        .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty))
    (.node
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty))
      (.node .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty))

/-- Coordinate-0 slice `5` (50 words) of the canonical 8-private-pair Polak–Schrijver 367-word set. -/
def ps367Slice5 : Trie7 4 :=
  .node
    (.node
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty))
      (.node .empty .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty))
    (.node
      (.node .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty)
      (.node .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty))
    (.node
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty)
      .empty
      (.node (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty))
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty)
        (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty))
    (.node
      (.node .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty)
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      .empty
      (.node .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      .empty
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty))
    (.node
      (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty)
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty .empty)
      (.node (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty))
      (.node .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty))
    (.node
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty))
    (.node
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)
        (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty .empty))

/-- Coordinate-0 slice `6` (50 words) of the canonical 8-private-pair Polak–Schrijver 367-word set. -/
def ps367Slice6 : Trie7 4 :=
  .node
    (.node
      (.node .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty)
      (.node .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty)
      (.node (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty))
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .leaf .empty) .empty .empty))
    (.node
      (.node .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty)
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty)
      (.node .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty .empty)
      .empty)
    (.node
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty)
      (.node
        .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty)
        (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty)
      (.node (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty))
    (.node
      (.node (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty)
      (.node .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty))
    (.node
      .empty
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty)
      .empty
      (.node
        .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty)
        (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty)
      (.node .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty .empty .empty)
      (.node
        .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf)
        (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty)
      .empty)
    (.node
      (.node (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .leaf .empty .empty .empty .empty .empty .empty))
      (.node .empty .empty .empty .empty .empty (.node .empty .empty .leaf .empty .empty .empty .empty) .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty) .empty .empty)
      (.node .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf) .empty .empty)
      (.node .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty))
    (.node
      (.node .empty .empty (.node .empty .empty .empty .empty .empty .leaf .empty) .empty .empty .empty .empty)
      (.node .empty (.node .leaf .empty .empty .empty .empty .empty .empty) .empty .empty .empty .empty .empty)
      (.node (.node .empty .empty .leaf .empty .empty .empty .empty) .empty .empty .empty .empty .empty .empty)
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .leaf .empty .empty))
      (.node .empty .empty .empty .empty .empty .empty (.node .empty .empty .empty .empty .empty .empty .leaf))
      (.node .empty .empty .empty .empty .empty (.node .empty .leaf .empty .empty .empty .empty .empty) .empty)
      (.node .empty .empty (.node .empty .empty .empty .leaf .empty .empty .empty) .empty .empty .empty .empty))

/-- Canonical 8-private-pair Polak–Schrijver 367-word independent set in `C7^⊠5` (`SHA-256: 0c42fc4c...`). -/
def polakSchrijver367Trie : Trie7 5 :=
  .node ps367Slice0 ps367Slice1 ps367Slice2 ps367Slice3 ps367Slice4 ps367Slice5 ps367Slice6

theorem c7Pow3Trie_isIndep : c7Pow3Trie.isIndep = true := rfl

theorem c7Pow3Trie_card : c7Pow3Trie.card = 33 := rfl

/-- Certified lower bound `α(C7^⊠3) ≥ 33` verified in pure kernel via `Trie7 3`. -/
theorem alpha_c7_pow3_ge : 33 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum := by
  simpa only [c7Pow3Trie_card] using
    Trie7.card_le_cycleGraph7_indepNum c7Pow3Trie_isIndep

theorem c7Pow4Trie_isIndep : c7Pow4Trie.isIndep = true := rfl

theorem c7Pow4Trie_card : c7Pow4Trie.card = 108 := rfl

/-- Certified lower bound `α(C7^⊠4) ≥ 108` verified in pure kernel via `Trie7 4`. -/
theorem alpha_c7_pow4_ge : 108 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 4).indepNum := by
  simpa only [c7Pow4Trie_card] using
    Trie7.card_le_cycleGraph7_indepNum c7Pow4Trie_isIndep

private theorem ps367Slice0_isIndep : ps367Slice0.isIndep = true := rfl
private theorem ps367Slice1_isIndep : ps367Slice1.isIndep = true := rfl
private theorem ps367Slice2_isIndep : ps367Slice2.isIndep = true := rfl
private theorem ps367Slice3_isIndep : ps367Slice3.isIndep = true := rfl
private theorem ps367Slice4_isIndep : ps367Slice4.isIndep = true := rfl
private theorem ps367Slice5_isIndep : ps367Slice5.isIndep = true := rfl
private theorem ps367Slice6_isIndep : ps367Slice6.isIndep = true := rfl

private theorem ps367_disj01 : ps367Slice0.disjoint ps367Slice1 = true := rfl
private theorem ps367_disj12 : ps367Slice1.disjoint ps367Slice2 = true := rfl
private theorem ps367_disj23 : ps367Slice2.disjoint ps367Slice3 = true := rfl
private theorem ps367_disj34 : ps367Slice3.disjoint ps367Slice4 = true := rfl
private theorem ps367_disj45 : ps367Slice4.disjoint ps367Slice5 = true := rfl
private theorem ps367_disj56 : ps367Slice5.disjoint ps367Slice6 = true := rfl
private theorem ps367_disj60 : ps367Slice6.disjoint ps367Slice0 = true := rfl

/-- Pure-kernel slice-by-slice independence proof for the 367-word Polak–Schrijver trie. -/
theorem polakSchrijver367Trie_isIndep : polakSchrijver367Trie.isIndep = true :=
  Trie7.isIndep_node
    ps367Slice0_isIndep ps367Slice1_isIndep ps367Slice2_isIndep ps367Slice3_isIndep
    ps367Slice4_isIndep ps367Slice5_isIndep ps367Slice6_isIndep
    ps367_disj01 ps367_disj12 ps367_disj23 ps367_disj34
    ps367_disj45 ps367_disj56 ps367_disj60

/-- Exact leaf count `367` of the Polak–Schrijver trie. -/
theorem polakSchrijver367Trie_card : polakSchrijver367Trie.card = 367 := rfl

/-- Certified Polak–Schrijver lower bound `α(C7^⊠5) ≥ 367` verified in pure kernel via `Trie7 5`. -/
theorem alpha_c7_pow5_ge_367 : 367 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum := by
  simpa only [polakSchrijver367Trie_card] using
    Trie7.card_le_cycleGraph7_indepNum polakSchrijver367Trie_isIndep

/-- Immediate exact decimal lower bound `3.25786596 ≤ Θ(C7)` from `α(C7^⊠5) ≥ 367`. -/
theorem c7_lower_polak_schrijver :
    (325786596 : ℝ) / 100000000 ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  le_shannonCapacity_cycleGraph7_of_nat_pow (d := 5) (N := 367) (by decide) (by decide)
    (by
      simpa only [polakSchrijver367Trie_card] using
        Trie7.card_le_indepNum polakSchrijver367Trie_isIndep)
    (nat_pow_le_of_ble rfl)

/-! ## Power `d = 5` Algebraic Linear Subspace: `α(C7^⊠5) ≥ 343` -/

private def c7Close (x : ZMod 7) : Prop := x = 0 ∨ x = 1 ∨ x = 6

private instance instDecidableC7Close (x : ZMod 7) : Decidable (c7Close x) :=
  inferInstanceAs (Decidable (x = 0 ∨ x = 1 ∨ x = 6))

private theorem eq_or_c7_adj_iff_c7Close (u v : ZMod 7) :
    (u = v ∨ C7.Adj u v) ↔ c7Close (u - v) := by
  revert u v
  decide

private theorem eq_or_strongPow_succ_adj {V : Type*} {G : SimpleGraph V} {d : ℕ}
    {x y : StrongPowV V (d + 1)} :
    (x = y ∨ (strongPow G (d + 1)).Adj x y) ↔
      (x.1 = y.1 ∨ G.Adj x.1 y.1) ∧ (x.2 = y.2 ∨ (strongPow G d).Adj x.2 y.2) :=
  eq_or_strongProd_adj (G := G) (H := strongPow G d) (x := x) (y := y)

private def linCode5 (p : ZMod 7 × ZMod 7 × ZMod 7) : StrongPowV (ZMod 7) 5 :=
  (-(p.1 + p.2.1 + 3 * p.2.2), -(2 * p.1 + 4 * p.2.1 + p.2.2), p.1, p.2.1, p.2.2, PUnit.unit)

private theorem linCode5_injective : Function.Injective linCode5 := by
  rintro ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ h
  exact Prod.ext (congrArg (fun x => x.2.2.1) h)
    (Prod.ext (congrArg (fun x => x.2.2.2.1) h) (congrArg (fun x => x.2.2.2.2.1) h))

private theorem strongPow5_adj_coords {u v : StrongPowV (ZMod 7) 5}
    (h : (strongPow C7 5).Adj u v) :
    (u.1 = v.1 ∨ C7.Adj u.1 v.1) ∧
    (u.2.1 = v.2.1 ∨ C7.Adj u.2.1 v.2.1) ∧
    (u.2.2.1 = v.2.2.1 ∨ C7.Adj u.2.2.1 v.2.2.1) ∧
    (u.2.2.2.1 = v.2.2.2.1 ∨ C7.Adj u.2.2.2.1 v.2.2.2.1) ∧
    (u.2.2.2.2.1 = v.2.2.2.2.1 ∨ C7.Adj u.2.2.2.2.1 v.2.2.2.2.1) := by
  have h' : u = v ∨ (strongPow C7 5).Adj u v := Or.inr h
  rw [eq_or_strongPow_succ_adj] at h'
  rcases h' with ⟨h0, h1⟩
  rw [eq_or_strongPow_succ_adj] at h1
  rcases h1 with ⟨h1, h2⟩
  rw [eq_or_strongPow_succ_adj] at h2
  rcases h2 with ⟨h2, h3⟩
  rw [eq_or_strongPow_succ_adj] at h3
  rcases h3 with ⟨h3, h4⟩
  rw [eq_or_strongPow_succ_adj] at h4
  exact ⟨h0, h1, h2, h3, h4.1⟩

private theorem linCode5_nonzero_not_all_close :
    ∀ (a b c : ZMod 7), (a, b, c) ≠ (0, 0, 0) →
      ¬ (c7Close (-(a + b + 3 * c)) ∧ c7Close (-(2 * a + 4 * b + c)) ∧
         c7Close a ∧ c7Close b ∧ c7Close c) := by
  intro a b c hne ⟨h0, h1, ha, hb, hc⟩
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    first | exact hne rfl | exact absurd h0 (by decide) | exact absurd h1 (by decide)

/-- Baumert et al. (1971) 3D linear-subspace lower bound `α(C7^⊠5) ≥ 343 = 7³`. -/
theorem alpha_c7_pow5_ge_343 : 343 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum := by
  rw [cycleGraph7_strongPowPi_indepNum_eq 5]
  let s : Finset (StrongPowV (ZMod 7) 5) := Finset.univ.map ⟨linCode5, linCode5_injective⟩
  have hcard : s.card = 343 := by simp [s]
  have hind : (strongPow C7 5).IsIndepSet (s : Set (StrongPowV (ZMod 7) 5)) := by
    intro x hx y hy hxy hadj
    simp only [s, Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image,
      Finset.mem_coe, Finset.mem_univ, true_and] at hx hy
    rcases hx with ⟨⟨a₁, b₁, c₁⟩, rfl⟩
    rcases hy with ⟨⟨a₂, b₂, c₂⟩, rfl⟩
    have hne : (a₁ - a₂, b₁ - b₂, c₁ - c₂) ≠ (0, 0, 0) := by
      intro h0
      simp only [Prod.mk.injEq, sub_eq_zero] at h0
      rcases h0 with ⟨rfl, rfl, rfl⟩
      exact hxy rfl
    rcases strongPow5_adj_coords hadj with ⟨hc0, hc1, hc2, hc3, hc4⟩
    have h0 : -(a₁ + b₁ + 3 * c₁) - -(a₂ + b₂ + 3 * c₂) =
        -(a₁ - a₂ + (b₁ - b₂) + 3 * (c₁ - c₂)) := by ring
    have h1 : -(2 * a₁ + 4 * b₁ + c₁) - -(2 * a₂ + 4 * b₂ + c₂) =
        -(2 * (a₁ - a₂) + 4 * (b₁ - b₂) + (c₁ - c₂)) := by ring
    exact linCode5_nonzero_not_all_close (a₁ - a₂) (b₁ - b₂) (c₁ - c₂) hne
      ⟨h0 ▸ (eq_or_c7_adj_iff_c7Close _ _).mp hc0,
       h1 ▸ (eq_or_c7_adj_iff_c7Close _ _).mp hc1,
       (eq_or_c7_adj_iff_c7Close _ _).mp hc2,
       (eq_or_c7_adj_iff_c7Close _ _).mp hc3,
       (eq_or_c7_adj_iff_c7Close _ _).mp hc4⟩
  rw [← hcard]
  exact hind.card_le_indepNum

/-! ## Complement Lower Bound: `17^(1/4) ≤ Θ(C7ᶜ)` (Bohman–Holzman 2003) -/

private def c7AdjBool (a b : ZMod 7) : Bool :=
  let d := (a.val + 7 - b.val) % 7
  d == 1 || d == 6

private theorem c7Adj_of_c7AdjBool {a b : ZMod 7} (h : c7AdjBool a b = true) : C7.Adj a b := by
  revert a b h
  decide

private def c7Compl4Sep (u v : StrongPowV (ZMod 7) 4) : Bool :=
  c7AdjBool u.1 v.1 || c7AdjBool u.2.1 v.2.1 ||
    c7AdjBool u.2.2.1 v.2.2.1 || c7AdjBool u.2.2.2.1 v.2.2.2.1

private theorem not_strongPow_c7Compl4_adj_of_sep {u v : StrongPowV (ZMod 7) 4}
    (h : c7Compl4Sep u v = true) : ¬ (strongPow C7ᶜ 4).Adj u v := by
  intro hadj
  have h' : u = v ∨ (strongPow C7ᶜ 4).Adj u v := Or.inr hadj
  rw [eq_or_strongPow_succ_adj] at h'
  rcases h' with ⟨h0, h1⟩
  rw [eq_or_strongPow_succ_adj] at h1
  rcases h1 with ⟨h1, h2⟩
  rw [eq_or_strongPow_succ_adj] at h2
  rcases h2 with ⟨h2, h3⟩
  rw [eq_or_strongPow_succ_adj] at h3
  have hnot : ∀ {a b : ZMod 7}, (a = b ∨ C7ᶜ.Adj a b) → ¬ C7.Adj a b := by
    intro a b hab hadjC7
    rcases hab with rfl | hcompl
    · exact hadjC7.ne rfl
    · exact hcompl.2 hadjC7
  simp only [c7Compl4Sep, Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h)
  · exact hnot h0 (c7Adj_of_c7AdjBool h)
  · exact hnot h1 (c7Adj_of_c7AdjBool h)
  · exact hnot h2 (c7Adj_of_c7AdjBool h)
  · exact hnot h3.1 (c7Adj_of_c7AdjBool h)

/-- Canonical negation-symmetric 17-word Bohman–Holzman independent set in `C7ᶜ^⊠4` (`SHA-256: c2e483de...`). -/
private def c7Compl4List : List (StrongPowV (ZMod 7) 4) :=
  [ (0, 0, 0, 0, PUnit.unit),
    (1, 2, 3, 5, PUnit.unit),
    (1, 2, 4, 3, PUnit.unit),
    (2, 2, 1, 3, PUnit.unit),
    (2, 4, 1, 4, PUnit.unit),
    (2, 4, 2, 1, PUnit.unit),
    (3, 1, 5, 5, PUnit.unit),
    (3, 4, 5, 6, PUnit.unit),
    (3, 6, 4, 2, PUnit.unit),
    (4, 1, 3, 5, PUnit.unit),
    (4, 3, 2, 1, PUnit.unit),
    (4, 6, 2, 2, PUnit.unit),
    (5, 3, 5, 6, PUnit.unit),
    (5, 3, 6, 3, PUnit.unit),
    (5, 5, 6, 4, PUnit.unit),
    (6, 5, 3, 4, PUnit.unit),
    (6, 5, 4, 2, PUnit.unit) ]

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

private theorem c7Compl4List_nodup : c7Compl4List.Nodup :=
  list_pairwise_of_pairwiseBool (r := fun u v => decide (u ≠ v))
    (fun _ _ h => of_decide_eq_true h) rfl

private theorem c7Compl4List_pairwise :
    c7Compl4List.Pairwise (fun u v => ¬ (strongPow C7ᶜ 4).Adj u v) :=
  list_pairwise_of_pairwiseBool (fun _ _ => not_strongPow_c7Compl4_adj_of_sep) rfl

/-- Bohman–Holzman (2003) complement lower bound `17^(1/4) ≤ Θ(C7ᶜ)`. -/
theorem c7_compl_lower_17 :
    (17 : ℝ) ^ (1 / 4 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ := by
  rw [← shannonCapacity_congr (isoCompl c7IsoCycleGraph)]
  have hind : (strongPow C7ᶜ 4).IsIndepSet (c7Compl4List.toFinset : Set (StrongPowV (ZMod 7) 4)) :=
    isIndepSet_of_pairwise c7Compl4List_pairwise
  have hcard : c7Compl4List.toFinset.card = 17 :=
    List.toFinset_card_of_nodup c7Compl4List_nodup
  have hcap := le_shannonCapacity_of_indepSet C7ᶜ (d := 4) (by decide) hind
  rw [hcard] at hcap
  simpa using hcap

end ShannonC7
