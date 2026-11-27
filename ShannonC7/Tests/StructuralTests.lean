import ShannonC7.StructuralBounds
import Mathlib.Algebra.Field.ZMod

/-!
# Structural Bounds & Obstruction Unit Tests (`ShannonC7/Tests/StructuralTests.lean`)

Validates:
1. Verbatim type-signature conformance (`ContractChecks`) for all public definitions and
   theorems in `ShannonC7.StructuralBounds` across Parts 1, 2, and 3.
2. Functional and edge-case sanity checks:
   - `oddCycle_pow2_indepNum` at `k = 1..5` (`1, 5, 10, 18, 27`, cross-checked against `alpha_c7_pow2`).
   - `fracCliqueCoverNum` on `⊥ : SimpleGraph Empty` (`0`), `⊥ : SimpleGraph PUnit` (`1`),
     `⊤ : SimpleGraph (Fin 5)` (`1`), `cycleGraph 7` (`7/2`), `(cycleGraph 7)ᶜ` (`7/3`),
     and Rosenfeld `C_7[E_2]` 7-clique cover.
   - `torusBox` packing & `L_∞ ≥ 2` checks on the 10-element `C_7^⊠2` independent set.
   - Complement Lovász & `ℚ(cos(π/7))` identities.
   - `Gilbert32` (`ϑ' = 4 < √20 ≤ Θ(G32)`, `ϑ = 16/3`), `Haemers27`/`Schlafli27`
     (`Θ(H27) ≤ 7 < 9 = ϑ(H27)`, `α = Θ = ϑ = 3` on `S27`, Gate G3 `21 < 27`, `rank = 7` over `ℚ, ℝ`,
     `rank ≤ 7` over `ZMod 2`), and Bukh–Cox fractional Haemers (`7/2 > ϑ(C7)` over `ℚ, ℝ, ZMod 2`).
3. Explicit `#print axioms` checks for every public theorem/definition in `StructuralBounds.lean`.
-/

namespace ShannonC7.Tests

open ShannonC7

section ContractChecks

-- Part 1
example {n : ℕ} (hn : 2 ≤ n) {W : Type*} [Fintype W] (H : SimpleGraph W) :
    2 * (SimpleGraph.cycleGraph n ⊠ H).indepNum ≤ n * H.indepNum :=
  cycleGraph_sliceDoubleCount hn H

example (k : ℕ) (hk : 1 ≤ k) : (SimpleGraph.cycleGraph (2 * k + 1)).indepNum = k :=
  oddCycle_indepNum k hk

example (k : ℕ) (hk : 1 ≤ k) :
    (strongPowPi (SimpleGraph.cycleGraph (2 * k + 1)) 2).indepNum ≤ k ^ 2 + k / 2 :=
  oddCycle_pow2_indepNum_le k hk

example (k : ℕ) (hk : 1 ≤ k) :
    k ^ 2 + k / 2 ≤ (strongPowPi (SimpleGraph.cycleGraph (2 * k + 1)) 2).indepNum :=
  oddCycle_pow2_indepNum_ge k hk

example (k : ℕ) (hk : 1 ≤ k) :
    (strongPowPi (SimpleGraph.cycleGraph (2 * k + 1)) 2).indepNum = k ^ 2 + k / 2 :=
  oddCycle_pow2_indepNum k hk

example (k : ℕ) (hk : 1 ≤ k) :
    (strongPowPi (SimpleGraph.cycleGraph (2 * k + 1)) 2).indepNum = (k * (2 * k + 1)) / 2 :=
  oddCycle_pow2_indepNum_eq_div k hk

-- Part 2A
example {V : Type*} [Fintype V] (G : SimpleGraph V) : Type _ := FracCliqueCover G
noncomputable example {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := fracCliqueCoverNum G
example {V : Type*} [Fintype V] (G : SimpleGraph V) : Type _ := FracIndepSet G
noncomputable example {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := fracIndepNum G

example {V : Type*} [Fintype V] {G : SimpleGraph V}
    (y : FracIndepSet G) (c : FracCliqueCover G) : y.total ≤ c.total :=
  fracIndepSet_le_fracCliqueCover y c

example {V : Type*} [Fintype V] (G : SimpleGraph V) : fracIndepNum G ≤ fracCliqueCoverNum G :=
  fracIndepNum_le_fracCliqueCoverNum G

example {V : Type*} [Fintype V] (G : SimpleGraph V) : (G.indepNum : ℝ) ≤ fracCliqueCoverNum G :=
  indepNum_le_fracCliqueCoverNum G

example {V : Type*} [Fintype V] {G : SimpleGraph V} (c : FracCliqueCover G) :
    fracCliqueCoverNum G ≤ c.total :=
  fracCliqueCoverNum_le_of_cover c

example {V : Type*} [Fintype V] (G : SimpleGraph V) : shannonCapacity G ≤ fracCliqueCoverNum G :=
  shannonCapacity_le_fracCliqueCoverNum G

example {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) :
    ((G ⊠ H).indepNum : ℝ) ≤ fracCliqueCoverNum G * (H.indepNum : ℝ) :=
  fracCliqueCover_prod_bound G H

example {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) :
    fracCliqueCoverNum (G ⊠ H) ≤ fracCliqueCoverNum G * fracCliqueCoverNum H :=
  fracCliqueCoverNum_mul_le G H

-- Part 2B
example {V : Type*} (G : SimpleGraph V) : Prop := IsVertexTransitive G
example (n : ℕ) : IsVertexTransitive (SimpleGraph.cycleGraph n) := cycleGraph_isVertexTransitive n
example {V : Type*} {G : SimpleGraph V} (hG : IsVertexTransitive G) : IsVertexTransitive Gᶜ :=
  isVertexTransitive_compl hG
example {V : Type*} {G : SimpleGraph V} (hG : IsVertexTransitive G) (d : ℕ) :
    IsVertexTransitive (strongPowPi G d) :=
  isVertexTransitive_strongPowPi hG d

example {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V} (hG : IsVertexTransitive G) :
    fracCliqueCoverNum G = (Fintype.card V : ℝ) / (G.cliqueNum : ℝ) :=
  fracCliqueCoverNum_eq_card_div_cliqueNum_of_vertexTransitive hG

example {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V} (hG : IsVertexTransitive G) :
    shannonCapacity G * (G.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) :=
  shannonCapacity_mul_cliqueNum_le_card_of_vertexTransitive hG

example {k : ℕ} (hk : 2 ≤ k) : (SimpleGraph.cycleGraph (2 * k + 1)).cliqueNum = 2 :=
  oddCycle_cliqueNum hk

example {k : ℕ} (hk : 2 ≤ k) :
    fracCliqueCoverNum (SimpleGraph.cycleGraph (2 * k + 1)) = (2 * k + 1 : ℝ) / 2 :=
  oddCycle_fracCliqueCoverNum hk

example : fracCliqueCoverNum (SimpleGraph.cycleGraph 7) = 7 / 2 := c7_fracCliqueCoverNum
example : fracCliqueCoverNum (SimpleGraph.cycleGraph 7)ᶜ = 7 / 3 := c7_compl_fracCliqueCoverNum
example : shannonCapacity (SimpleGraph.cycleGraph 7) ≤ 7 / 2 := c7_upper_fracCliqueCover
example : shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ≤ 7 / 3 := c7_compl_upper_fracCliqueCover

-- Part 2C
noncomputable example (k : ℕ) : ℝ := lovaszThetaOddCycle k
noncomputable example (k : ℕ) : ℝ := lovaszThetaOddCycleCompl k
noncomputable example : ℝ := lovaszThetaC7Compl

example (k : ℕ) (hk : 1 ≤ k) :
    lovaszThetaOddCycle k * lovaszThetaOddCycleCompl k = (2 * k + 1 : ℝ) :=
  lovaszThetaOddCycle_mul_compl k hk

example : lovaszThetaC7 * lovaszThetaC7Compl = 7 := lovaszThetaC7_mul_compl

example (k : ℕ) (hk : 1 ≤ k) :
    shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1)) *
      shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1))ᶜ ≤ (2 * k + 1 : ℝ) :=
  oddCycle_shannonCapacity_mul_compl_le k hk

example :
    shannonCapacity (SimpleGraph.cycleGraph 7) *
      shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ≤ 7 :=
  c7_shannonCapacity_mul_compl_le

example :
    (Real.cos (Real.pi / 7))⁻¹ =
      -8 * (Real.cos (Real.pi / 7)) ^ 2 + 4 * Real.cos (Real.pi / 7) + 4 :=
  cos_pi_div_seven_inv_eq_poly

example :
    lovaszThetaC7 = -8 * (Real.cos (Real.pi / 7)) ^ 2 + 12 * Real.cos (Real.pi / 7) - 1 :=
  lovaszThetaC7_eq_poly_cos

example :
    lovaszThetaC7Compl = -8 * (Real.cos (Real.pi / 7)) ^ 2 + 4 * Real.cos (Real.pi / 7) + 5 :=
  lovaszThetaC7Compl_eq_poly_cos

example : lovaszThetaC7 - lovaszThetaC7Compl = 8 * Real.cos (Real.pi / 7) - 6 :=
  lovaszThetaC7_sub_compl

example : lovaszThetaC7Compl ^ 3 - 7 * lovaszThetaC7Compl ^ 2 + 7 * lovaszThetaC7Compl + 7 = 0 :=
  lovaszThetaC7Compl_cubic

example : Real.cos (Real.pi / 7) = lovaszThetaC7 / (7 - lovaszThetaC7) :=
  cos_pi_div_seven_eq_div_lovaszThetaC7

example : Real.cos (Real.pi / 7) = (lovaszThetaC7Compl - 1)⁻¹ :=
  cos_pi_div_seven_eq_inv_lovaszThetaC7Compl

-- Part 2D
example (n d : ℕ) [NeZero n] (u : Fin d → ZMod n) : Finset (Fin d → ZMod n) := torusBox n d u
example (n d : ℕ) (hn : 2 ≤ n) (u : Fin d → ZMod n) :
    letI : NeZero n := ⟨by omega⟩
    (torusBox n d u).card = 2 ^ d :=
  card_torusBox n d hn u

example {d : ℕ} (S : Finset (Fin d → ZMod 7)) :
    (strongPowPi C7 d).IsIndepSet (S : Set (Fin d → ZMod 7)) ↔
      (S : Set (Fin d → ZMod 7)).PairwiseDisjoint (torusBox 7 d) :=
  c7Pow_isIndepSet_iff_pairwiseDisjoint_boxes S

example (d : ℕ) : 2 ^ d * (strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum ≤ 7 ^ d :=
  c7Pow_volume_bound d

example (n : ℕ) (a b : ZMod n) : ℕ := cyclicDist n a b

example {d : ℕ} (S : Finset (Fin d → ZMod 7)) :
    (strongPowPi C7 d).IsIndepSet (S : Set (Fin d → ZMod 7)) ↔
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∃ i : Fin d, 2 ≤ cyclicDist 7 (u i) (v i) :=
  c7Pow_isIndepSet_iff_linf_ge_two S

example {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : Gᶜ →g Hᶜ) :
    shannonCapacity G ≤ shannonCapacity H :=
  shannonCapacity_mono_cohom f

example {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) :
    shannonCapacity G * shannonCapacity H ≤ shannonCapacity (G ⊠ H) :=
  shannonCapacity_mul_le G H

example {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype.card V ≤ (G ⊠ Gᶜ).indepNum :=
  card_le_prod_compl_indepNum G

example : (7 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7 ⊠ (SimpleGraph.cycleGraph 7)ᶜ) :=
  c7_prod_compl_shannonCapacity_ge_seven

example {V W : Type*} [Fintype V] [Fintype W] [Nonempty W] (G : SimpleGraph V) :
    shannonCapacity (G ⊠ (⊤ : SimpleGraph W)) = shannonCapacity G :=
  shannonCapacity_cliqueBlowup G

example {V : Type*} [Fintype V] (G : SimpleGraph V) (m : ℕ) :
    shannonCapacity (G ⊠ (⊥ : SimpleGraph (Fin m))) = (m : ℝ) * shannonCapacity G :=
  shannonCapacity_disjointBlowup G m

example {V : Type*} (G : SimpleGraph V) (k : ℕ) : SimpleGraph (V × Fin k) := lexIndepBlowup G k
example {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop := HasCliqueCover G m

example {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (lexIndepBlowup G k).indepNum = k * G.indepNum :=
  lexIndepBlowup_indepNum G k

example {V : Type*} [Fintype V] {G : SimpleGraph V} {k m : ℕ}
    (hk : 0 < k) (hc : HasCliqueCover (lexIndepBlowup G k) m) :
    fracCliqueCoverNum G ≤ (m : ℝ) / (k : ℝ) :=
  fracCliqueCoverNum_le_of_lexBlowup_cliqueCover hk hc

example {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) {ε : ℝ} (hε : 0 < ε) :
    ∃ k m : ℕ, 0 < k ∧ HasCliqueCover (lexIndepBlowup G k) m ∧
      (m : ℝ) / (k : ℝ) ≤ fracCliqueCoverNum G + ε :=
  exists_lexBlowup_cliqueCover_of_fracCliqueCover G hε

-- Part 3
noncomputable example {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := lovaszTheta G
noncomputable example {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := schrijverTheta G
example {V : Type*} [Fintype V] (G : SimpleGraph V) (β : ℝ) : Type _ := SchrijverCert G β

example {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    schrijverTheta G ≤ lovaszTheta G :=
  schrijverTheta_le_lovaszTheta G

example {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V} {β : ℝ} (cert : LovaszCert G β) :
    lovaszTheta G ≤ β⁻¹ :=
  lovaszTheta_le_of_cert cert

example {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V} {β : ℝ} (cert : SchrijverCert G β) :
    schrijverTheta G ≤ β⁻¹ :=
  schrijverTheta_le_of_cert cert

example {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    (G.indepNum : ℝ) ≤ schrijverTheta G :=
  indepNum_le_schrijverTheta G

example {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    (G.indepNum : ℝ) ≤ lovaszTheta G :=
  indepNum_le_lovaszTheta G

example : SimpleGraph (Fin 32) := gilbert32
example : gilbert32.indepNum = 4 := gilbert32_indep_four
example : 20 ≤ (strongPowPi gilbert32 2).indepNum := gilbert32_sq_indep_twenty
example : schrijverTheta gilbert32 = 4 := gilbert32_schrijverTheta_eq_four
example :
    schrijverTheta gilbert32 ^ 2 < ((strongPowPi gilbert32 2).indepNum : ℝ) ∧
      schrijverTheta gilbert32 < Real.sqrt 20 ∧
      Real.sqrt 20 ≤ shannonCapacity gilbert32 :=
  gilbert32_schrijver_fails_submult
example : lovaszTheta gilbert32 = 16 / 3 := gilbert32_lovaszTheta_eq

example : SimpleGraph (Fin 27) := haemers27
example : SimpleGraph (Fin 27) := schlafli27
example (F : Type*) [Field F] :
    IsFittingMatrix haemers27 (haemers27FittingMatrix F) ∧
      (haemers27FittingMatrix F).rank ≤ 7 ∧
      shannonCapacity haemers27 ≤ 7 :=
  haemers27_minrank_le_seven F
example (F : Type*) [Field F] [CharZero F] : (haemers27FittingMatrix F).rank = 7 :=
  haemers27_canonical_fitting_rank_eq_seven F
example : lovaszTheta haemers27 = 9 := haemers27_lovaszTheta_eq_nine
example :
    (6 : ℝ) ≤ (haemers27.indepNum : ℝ) ∧
      (haemers27.indepNum : ℝ) ≤ shannonCapacity haemers27 ∧
      shannonCapacity haemers27 ≤ 7 ∧
      (7 : ℝ) < lovaszTheta haemers27 :=
  haemers27_haemers_beats_lovasz
example :
    schlafli27.indepNum = 3 ∧
      shannonCapacity schlafli27 = 3 ∧
      lovaszTheta schlafli27 = 3 :=
  schlafli27_exact
example :
    shannonCapacity haemers27 * shannonCapacity schlafli27 ≤ 21 ∧
      (21 : ℝ) < lovaszTheta haemers27 * lovaszTheta schlafli27 :=
  haemers27_schlafli27_gate_g3

example {V : Type*} (G : SimpleGraph V) (F : Type*) [Field F] (s d : ℕ) : Type _ :=
  FracHaemersRep G F s d
noncomputable example {V : Type*} [Fintype V] (F : Type*) [Field F] (G : SimpleGraph V) : ℝ :=
  fracHaemers F G
example {V : Type*} [Fintype V] (F : Type*) [Field F] (G : SimpleGraph V) :
    shannonCapacity G ≤ fracHaemers F G :=
  shannonCapacity_le_fracHaemers F G
example {V : Type*} [Fintype V] {F : Type*} [Field F]
    {G : SimpleGraph V} {M : Matrix V V F} (hM : IsFittingMatrix G M) :
    fracHaemers F G ≤ (M.rank : ℝ) :=
  fracHaemers_le_rank_of_fitting hM
example (F : Type*) [Field F] {k : ℕ} (hk : 2 ≤ k) :
    fracHaemers F (SimpleGraph.cycleGraph (2 * k + 1)) = (2 * k + 1 : ℝ) / 2 :=
  fracHaemers_oddCycle F hk
example (F : Type*) [Field F] :
    fracHaemers F (SimpleGraph.cycleGraph 7) = 7 / 2 :=
  fracHaemers_c7 F
example (F : Type*) [Field F] :
    lovaszThetaC7 < fracHaemers F (SimpleGraph.cycleGraph 7) :=
  lovaszThetaC7_lt_fracHaemers_c7 F

end ContractChecks

section FunctionalAndEdgeCaseTests

-- Part 1: Odd-cycle square exactness at k = 1..5
example : (strongPowPi (SimpleGraph.cycleGraph 3) 2).indepNum = 1 := by
  simpa using oddCycle_pow2_indepNum 1 (by norm_num)

example : (strongPowPi (SimpleGraph.cycleGraph 5) 2).indepNum = 5 := by
  simpa using oddCycle_pow2_indepNum 2 (by norm_num)

example : (strongPowPi (SimpleGraph.cycleGraph 7) 2).indepNum = 10 := by
  simpa using oddCycle_pow2_indepNum 3 (by norm_num)

example : (strongPowPi (SimpleGraph.cycleGraph 9) 2).indepNum = 18 := by
  simpa using oddCycle_pow2_indepNum 4 (by norm_num)

example : (strongPowPi (SimpleGraph.cycleGraph 11) 2).indepNum = 27 := by
  simpa using oddCycle_pow2_indepNum 5 (by norm_num)

example : (strongPowPi (SimpleGraph.cycleGraph 7) 2).indepNum = (3 * 7) / 2 := by
  simpa using oddCycle_pow2_indepNum_eq_div 3 (by norm_num)

-- Part 2A/B: Fractional clique cover edge cases
theorem empty_fracCliqueCoverNum_eq_zero :
    fracCliqueCoverNum (⊥ : SimpleGraph Empty) = 0 := by
  apply le_antisymm
  · let c : FracCliqueCover (⊥ : SimpleGraph Empty) :=
      { weight := fun _ => 0
        nonneg := fun _ => le_rfl
        clique_of_pos := fun _ h => absurd h (lt_irrefl 0)
        cover := fun x => x.elim }
    have h := fracCliqueCoverNum_le_of_cover c
    simpa [FracCliqueCover.total, c] using h
  · exact fracCliqueCoverNum_nonneg (⊥ : SimpleGraph Empty)

theorem punit_bot_fracCliqueCoverNum_eq_one :
    fracCliqueCoverNum (⊥ : SimpleGraph PUnit) = 1 := by
  have hvt : IsVertexTransitive (⊥ : SimpleGraph PUnit) := fun u v =>
    ⟨{ toEquiv := Equiv.refl PUnit, map_rel_iff' := by simp }, Subsingleton.elim _ _⟩
  have hclq : (⊥ : SimpleGraph PUnit).cliqueNum = 1 := by
    apply le_antisymm
    · obtain ⟨S, _, hS⟩ := (⊥ : SimpleGraph PUnit).exists_isNClique_cliqueNum
      rw [← hS]
      simpa using S.card_le_univ
    · have h1 : (⊥ : SimpleGraph PUnit).IsClique (({PUnit.unit} : Finset PUnit) : Set PUnit) := by
        simp
      simpa using h1.card_le_cliqueNum
  rw [fracCliqueCoverNum_eq_card_div_cliqueNum_of_vertexTransitive hvt, hclq]
  simp

theorem fin5_top_fracCliqueCoverNum_eq_one :
    fracCliqueCoverNum (⊤ : SimpleGraph (Fin 5)) = 1 := by
  have hvt : IsVertexTransitive (⊤ : SimpleGraph (Fin 5)) := fun u v =>
    ⟨{ toEquiv := Equiv.swap u v, map_rel_iff' := by simp }, by simp⟩
  have hclq : (⊤ : SimpleGraph (Fin 5)).cliqueNum = 5 := by
    apply le_antisymm
    · obtain ⟨S, _, hS⟩ := (⊤ : SimpleGraph (Fin 5)).exists_isNClique_cliqueNum
      simpa [← hS] using S.card_le_univ
    · have h5 : (⊤ : SimpleGraph (Fin 5)).IsClique ((Finset.univ : Finset (Fin 5)) : Set (Fin 5)) := by
        intro x _ y _ hxy
        exact hxy
      simpa using h5.card_le_cliqueNum
  rw [fracCliqueCoverNum_eq_card_div_cliqueNum_of_vertexTransitive hvt, hclq]
  simp

-- Rosenfeld C_7[E_2] 7-clique cover giving fracCliqueCoverNum (cycleGraph 7) ≤ 7 / 2
theorem c7_lexBlowup_two_has_seven_clique_cover :
    HasCliqueCover (lexIndepBlowup (SimpleGraph.cycleGraph 7) 2) 7 := by
  let fam : Fin 7 → Finset (Fin 7 × Fin 2) := fun j => {(j, 0), (j + 1, 1)}
  refine ⟨fam, ?_, ?_⟩
  · intro j p₁ hp₁ p₂ hp₂ hne
    simp only [fam, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp₁ hp₂
    have hadj : (SimpleGraph.cycleGraph 7).Adj j (j + 1) := by
      rw [SimpleGraph.cycleGraph_adj']
      right
      rw [add_sub_cancel_left]
      decide
    rcases hp₁ with rfl | rfl <;> rcases hp₂ with rfl | rfl
    · exact absurd rfl hne
    · exact hadj
    · exact hadj.symm
    · exact absurd rfl hne
  · rintro ⟨v, i⟩
    fin_cases i
    · exact ⟨v, by simp [fam]⟩
    · refine ⟨v - 1, ?_⟩
      simp [fam, sub_add_cancel]

example : fracCliqueCoverNum (SimpleGraph.cycleGraph 7) ≤ 7 / 2 := by
  simpa using fracCliqueCoverNum_le_of_lexBlowup_cliqueCover (by norm_num : 0 < 2)
    c7_lexBlowup_two_has_seven_clique_cover

-- Part 2D: TorusBox packing & L_∞ ≥ 2 on canonical 10-word C7^⊠2 independent set
private def c7Pow2ZMod10 : Finset (Fin 2 → ZMod 7) :=
  ([ (0, 1), (0, 3), (1, 5), (2, 0), (2, 2),
     (3, 4), (4, 1), (4, 6), (5, 3), (6, 5) ] : List (ZMod 7 × ZMod 7)).map
    (fun p idx => if idx = 0 then p.1 else p.2) |>.toFinset

example : (c7Pow2ZMod10 : Set (Fin 2 → ZMod 7)).PairwiseDisjoint (torusBox 7 2) :=
  (c7Pow_isIndepSet_iff_pairwiseDisjoint_boxes c7Pow2ZMod10).mp (by decide)

example : ∀ u ∈ c7Pow2ZMod10, ∀ v ∈ c7Pow2ZMod10, u ≠ v →
    ∃ i : Fin 2, 2 ≤ cyclicDist 7 (u i) (v i) :=
  (c7Pow_isIndepSet_iff_linf_ge_two c7Pow2ZMod10).mp (by decide)

example : 2 ^ 2 * (strongPowPi (SimpleGraph.cycleGraph 7) 2).indepNum ≤ 7 ^ 2 :=
  c7Pow_volume_bound 2

-- Part 3: Multi-characteristic Haemers27 & Bukh-Cox instantiations
example : IsFittingMatrix haemers27 (haemers27FittingMatrix (ZMod 2)) ∧
    (haemers27FittingMatrix (ZMod 2)).rank ≤ 7 :=
  ⟨(haemers27_minrank_le_seven (ZMod 2)).1, (haemers27_minrank_le_seven (ZMod 2)).2.1⟩

example : (haemers27FittingMatrix ℚ).rank = 7 :=
  haemers27_canonical_fitting_rank_eq_seven ℚ

example : (haemers27FittingMatrix ℝ).rank = 7 :=
  haemers27_canonical_fitting_rank_eq_seven ℝ

example : lovaszThetaC7 < fracHaemers ℚ (SimpleGraph.cycleGraph 7) :=
  lovaszThetaC7_lt_fracHaemers_c7 ℚ

example : lovaszThetaC7 < fracHaemers ℝ (SimpleGraph.cycleGraph 7) :=
  lovaszThetaC7_lt_fracHaemers_c7 ℝ

example : lovaszThetaC7 < fracHaemers (ZMod 2) (SimpleGraph.cycleGraph 7) :=
  lovaszThetaC7_lt_fracHaemers_c7 (ZMod 2)

end FunctionalAndEdgeCaseTests

section AxiomChecks

-- Part 1
#print axioms ShannonC7.cycleGraph_sliceDoubleCount
#print axioms ShannonC7.oddCycle_indepNum
#print axioms ShannonC7.oddCycle_pow2_indepNum_le
#print axioms ShannonC7.oddCycle_pow2_indepNum_ge
#print axioms ShannonC7.oddCycle_pow2_indepNum
#print axioms ShannonC7.oddCycle_pow2_indepNum_eq_div

-- Part 2A
#print axioms ShannonC7.FracCliqueCover.total
#print axioms ShannonC7.FracCliqueCover.total_nonneg
#print axioms ShannonC7.fracCliqueCoverNum
#print axioms ShannonC7.FracCliqueCover.ofFamily
#print axioms ShannonC7.FracCliqueCover.ofFamily_total
#print axioms ShannonC7.FracCliqueCover.unit
#print axioms ShannonC7.FracCliqueCover.unit_total
#print axioms ShannonC7.FracCliqueCover.prod
#print axioms ShannonC7.FracCliqueCover.prod_total
#print axioms ShannonC7.FracCliqueCover.pow
#print axioms ShannonC7.FracCliqueCover.pow_total
#print axioms ShannonC7.FracIndepSet.total
#print axioms ShannonC7.fracIndepNum
#print axioms ShannonC7.fracIndepSet_le_fracCliqueCover
#print axioms ShannonC7.fracIndepNum_le_fracCliqueCoverNum
#print axioms ShannonC7.fracCliqueCoverNum_nonneg
#print axioms ShannonC7.fracCliqueCoverNum_le_of_cover
#print axioms ShannonC7.indepNum_le_fracCliqueCoverNum
#print axioms ShannonC7.shannonCapacity_le_fracCliqueCoverNum
#print axioms ShannonC7.fracCliqueCover_prod_bound
#print axioms ShannonC7.fracCliqueCoverNum_mul_le

-- Part 2B
#print axioms ShannonC7.IsVertexTransitive
#print axioms ShannonC7.cycleGraph_isVertexTransitive
#print axioms ShannonC7.isVertexTransitive_compl
#print axioms ShannonC7.isVertexTransitive_strongPowPi
#print axioms ShannonC7.fracCliqueCoverNum_eq_card_div_cliqueNum_of_vertexTransitive
#print axioms ShannonC7.shannonCapacity_mul_cliqueNum_le_card_of_vertexTransitive
#print axioms ShannonC7.oddCycle_cliqueNum
#print axioms ShannonC7.oddCycle_fracCliqueCoverNum
#print axioms ShannonC7.c7_fracCliqueCoverNum
#print axioms ShannonC7.c7_upper_fracCliqueCover
#print axioms ShannonC7.c7_compl_fracCliqueCoverNum
#print axioms ShannonC7.c7_compl_upper_fracCliqueCover

-- Part 2C
#print axioms ShannonC7.lovaszThetaOddCycle
#print axioms ShannonC7.lovaszThetaOddCycleCompl
#print axioms ShannonC7.lovaszThetaC7Compl
#print axioms ShannonC7.lovaszThetaOddCycle_mul_compl
#print axioms ShannonC7.lovaszThetaC7_mul_compl
#print axioms ShannonC7.oddCycle_shannonCapacity_mul_compl_le
#print axioms ShannonC7.c7_shannonCapacity_mul_compl_le
#print axioms ShannonC7.cos_pi_div_seven_inv_eq_poly
#print axioms ShannonC7.lovaszThetaC7_eq_poly_cos
#print axioms ShannonC7.lovaszThetaC7Compl_eq_poly_cos
#print axioms ShannonC7.lovaszThetaC7_sub_compl
#print axioms ShannonC7.lovaszThetaC7Compl_cubic
#print axioms ShannonC7.cos_pi_div_seven_eq_div_lovaszThetaC7
#print axioms ShannonC7.cos_pi_div_seven_eq_inv_lovaszThetaC7Compl

-- Part 2D
#print axioms ShannonC7.torusBox
#print axioms ShannonC7.card_torusBox
#print axioms ShannonC7.c7Pow_isIndepSet_iff_pairwiseDisjoint_boxes
#print axioms ShannonC7.c7Pow_volume_bound
#print axioms ShannonC7.cyclicDist
#print axioms ShannonC7.c7Pow_isIndepSet_iff_linf_ge_two
#print axioms ShannonC7.shannonCapacity_mono_cohom
#print axioms ShannonC7.shannonCapacity_mul_le
#print axioms ShannonC7.card_le_prod_compl_indepNum
#print axioms ShannonC7.c7_prod_compl_shannonCapacity_ge_seven
#print axioms ShannonC7.shannonCapacity_cliqueBlowup
#print axioms ShannonC7.shannonCapacity_disjointBlowup
#print axioms ShannonC7.lexIndepBlowup
#print axioms ShannonC7.HasCliqueCover
#print axioms ShannonC7.lexIndepBlowup_indepNum
#print axioms ShannonC7.fracCliqueCoverNum_le_of_lexBlowup_cliqueCover
#print axioms ShannonC7.exists_lexBlowup_cliqueCover_of_fracCliqueCover

-- Part 3
#print axioms ShannonC7.lovaszTheta
#print axioms ShannonC7.schrijverTheta
#print axioms ShannonC7.schrijverTheta_le_lovaszTheta
#print axioms ShannonC7.lovaszTheta_le_of_cert
#print axioms ShannonC7.schrijverTheta_le_of_cert
#print axioms ShannonC7.le_lovaszTheta_of_primal
#print axioms ShannonC7.le_schrijverTheta_of_primal
#print axioms ShannonC7.indepNum_le_schrijverTheta
#print axioms ShannonC7.indepNum_le_lovaszTheta
#print axioms ShannonC7.hammingWeight5
#print axioms ShannonC7.gilbert32
#print axioms ShannonC7.gilbert32_indep_four
#print axioms ShannonC7.gilbert32_sq_indep_twenty
#print axioms ShannonC7.gilbert32_schrijverTheta_eq_four
#print axioms ShannonC7.gilbert32_schrijver_fails_submult
#print axioms ShannonC7.gilbert32_lovaszTheta_eq
#print axioms ShannonC7.haemers27
#print axioms ShannonC7.schlafli27
#print axioms ShannonC7.popcount27
#print axioms ShannonC7.haemers27FittingMatrix
#print axioms ShannonC7.haemers27_minrank_le_seven
#print axioms ShannonC7.haemers27_canonical_fitting_rank_eq_seven
#print axioms ShannonC7.haemers27_lovaszTheta_eq_nine
#print axioms ShannonC7.haemers27_haemers_beats_lovasz
#print axioms ShannonC7.schlafli27_exact
#print axioms ShannonC7.haemers27_schlafli27_gate_g3
#print axioms ShannonC7.fracHaemers
#print axioms ShannonC7.indepNum_mul_le_of_fracHaemersRep
#print axioms ShannonC7.shannonCapacity_le_fracHaemers
#print axioms ShannonC7.fracHaemers_le_rank_of_fitting
#print axioms ShannonC7.fracHaemers_oddCycle
#print axioms ShannonC7.fracHaemers_c7
#print axioms ShannonC7.lovaszThetaC7_lt_fracHaemers_c7

end AxiomChecks

end ShannonC7.Tests
