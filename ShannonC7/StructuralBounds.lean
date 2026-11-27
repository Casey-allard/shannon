import ShannonC7.CycleC7
import ShannonC7.Fekete
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import ShannonC7.LovaszC7
import ShannonC7.CubicBounds
import ShannonC7.SmallPowers
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import ShannonC7.Lovasz
import ShannonC7.Haemers
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases

/-!
# Structural Bounds, Exact Odd-Cycle Squares, and Obstruction Theorems

Formalizes three structural pillars for Shannon capacity and `C_7`:

1. **Part 1 — General Odd-Cycle Square Exactness**:
   Proves the slice double-counting upper bound `2 * α(C_n ⊠ H) ≤ n * α(H)`,
   `α(C_{2k+1}) = k`, and the exact square formula
   `α(C_{2k+1}^{⊠2}) = k^2 + ⌊k/2⌋ = ⌊k(2k+1)/2⌋` for all `k ≥ 1`.
   *(Note on formula correction: an earlier prompt draft wrote `k(2k+1) + ⌊k/2⌋`, which
   already exceeds `7 * 3 = 21` at `k = 3`; the true values for `k = 1..5` are
   `1, 5, 10, 18, 27`, matching `k^2 + ⌊k/2⌋ = ⌊k(2k+1)/2⌋` and `alpha_c7_pow2 = 10`.)*

2. **Part 2 — Fractional Clique Cover, Vertex-Transitive Exactness, Lovász Complement &
   `ℚ(cos(π/7))`, Torus Packing & Blowup / Rosenfeld Equivalences**:
   - `FracCliqueCover`, `FracIndepSet`, weak duality, product/power submultiplicativity, and
     `Θ(G) ≤ χ̄_f(G)`.
   - `IsVertexTransitive`, `χ̄_f(G) = |V| / ω(G)`, `χ̄_f(C_7) = 7/2`, `χ̄_f(C_7ᶜ) = 7/3`,
     and trig-free capacity bounds `Θ(C_7) ≤ 7/2`, `Θ(C_7ᶜ) ≤ 7/3`.
   - Complement identity `ϑ(C_{2k+1}) * ϑ(C_{2k+1}ᶜ) = 2k + 1`, `ϑ(C_7) * ϑ(C_7ᶜ) = 7`,
     `Θ(C_7) * Θ(C_7ᶜ) ≤ 7`, and exact `ℚ(cos(π/7))` polynomial/cubic identities.
   - `2^d`-torus box packing, `L_∞ ≥ 2` equivalence, cohomomorphism monotonicity,
     `Θ(C_7 ⊠ C_7ᶜ) ≥ 7`, clique/disjoint blowups, and Rosenfeld `k`-fold clique-cover
     equivalence for `lexIndepBlowup`.

3. **Part 3 — Barrier & Obstruction Theorems**:
   - Unified primal/dual SDP (`lovaszTheta`, `schrijverTheta`, `SchrijverCert`), Hadamard dual
     upper bound, and `α(G) ≤ ϑ'(G) ≤ ϑ(G)`.
   - `gilbert32` (32-vertex Hamming-distance-`≤ 3` graph on `(Fin 2)^5`):
     `α(G_{32}) = 4`, `α(G_{32}^{⊠2}) ≥ 20`, `ϑ'(G_{32}) = 4` (failing submultiplicativity:
     `ϑ'(G_{32})^2 = 16 < 20`), and `ϑ(G_{32}) = 16 / 3`.
   - `haemers27` (`srg(27, 10, 1, 5)`) and `schlafli27` (`haemers27ᶜ`, `srg(27, 16, 10, 8)`):
     `rk_F(M) ≤ 7` over any field `F` (`= 7` for `haemers27FittingMatrix` over `ℚ, ℝ`),
     `ϑ(H_{27}) = 9`, `Θ(H_{27}) ≤ 7 < 9 = ϑ(H_{27})`, `α(S_{27}) = Θ(S_{27}) = ϑ(S_{27}) = 3`,
     and Gate G3 (`7 * 3 = 21 < 27`).
   - Bukh–Cox fractional Haemers bound (`FracHaemersRep`, `fracHaemers`):
     `Θ(G) ≤ ℋ_f^F(G)`, odd-cycle exactness `ℋ_f^F(C_{2k+1}) = (2k+1)/2` for `k ≥ 2`,
     `ℋ_f^F(C_7) = 7/2`, and `ϑ(C_7) < ℋ_f^F(C_7)` over every field `F`.
-/

namespace ShannonC7

open scoped BigOperators Kronecker

/-! ## Part 1: General Odd-Cycle Square Exactness -/

theorem cycleGraph_sliceDoubleCount {n : ℕ} (hn : 2 ≤ n) {W : Type*} [Fintype W]
    (H : SimpleGraph W) :
    2 * (SimpleGraph.cycleGraph n ⊠ H).indepNum ≤ n * H.indepNum := by
  classical
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨S, hS_indep, hS_card⟩ := (SimpleGraph.cycleGraph n ⊠ H).exists_isNIndepSet_indepNum
  rw [← hS_card]
  let slice : Fin n → Finset W := fun i => (S.filter fun p => p.1 = i).image Prod.snd
  have mem_slice : ∀ (i : Fin n) (w : W), w ∈ slice i ↔ (i, w) ∈ S := by
    intro i w
    simp only [slice, Finset.mem_image, Finset.mem_filter, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨hab, rfl⟩, rfl⟩
      exact hab
    · intro h
      exact ⟨i, w, ⟨h, rfl⟩, rfl⟩
  have card_slice : ∀ i : Fin n, (slice i).card = (S.filter fun p => p.1 = i).card := by
    intro i
    apply Finset.card_image_of_injOn
    rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ hb
    simp only [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    exact Prod.ext (h₁.2.trans h₂.2.symm) hb
  have hsum_card : ∑ i : Fin n, (slice i).card = S.card := by
    simp_rw [card_slice]
    exact (Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := S) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm
  have hadj_add_one : ∀ i : Fin n, (SimpleGraph.cycleGraph n).Adj i (i + 1) := by
    intro i
    rw [SimpleGraph.cycleGraph_adj']
    refine Or.inr ?_
    have h1 : (i + 1) - i = (1 : Fin n) := add_sub_cancel_left i 1
    rw [h1]
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hadj_bound : ∀ i : Fin n, (slice i).card + (slice (i + 1)).card ≤ H.indepNum := by
    intro i
    have hadj : (SimpleGraph.cycleGraph n).Adj i (i + 1) := hadj_add_one i
    have hne : i ≠ i + 1 := hadj.ne
    have hdisj : Disjoint (slice i) (slice (i + 1)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      have h1 : (i, w) ∈ S := (mem_slice i w).mp hw1
      have h2 : (i + 1, w) ∈ S := (mem_slice (i + 1) w).mp hw2
      have hpair_ne : (i, w) ≠ (i + 1, w) := fun h => hne (congrArg Prod.fst h)
      exact hS_indep h1 h2 hpair_ne ⟨hpair_ne, Or.inr hadj, Or.inl rfl⟩
    have hindep : H.IsIndepSet ((slice i ∪ slice (i + 1) : Finset W) : Set W) := by
      intro u hu v hv huv hHadj
      simp only [Finset.mem_coe, Finset.mem_union] at hu hv
      have hu' : ∃ a : Fin n, (a = i ∨ a = i + 1) ∧ (a, u) ∈ S := by
        rcases hu with hu | hu
        · exact ⟨i, Or.inl rfl, (mem_slice i u).mp hu⟩
        · exact ⟨i + 1, Or.inr rfl, (mem_slice (i + 1) u).mp hu⟩
      have hv' : ∃ b : Fin n, (b = i ∨ b = i + 1) ∧ (b, v) ∈ S := by
        rcases hv with hv | hv
        · exact ⟨i, Or.inl rfl, (mem_slice i v).mp hv⟩
        · exact ⟨i + 1, Or.inr rfl, (mem_slice (i + 1) v).mp hv⟩
      rcases hu' with ⟨a, ha, hau⟩
      rcases hv' with ⟨b, hb, hbv⟩
      have hab : a = b ∨ (SimpleGraph.cycleGraph n).Adj a b := by
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr hadj
        · exact Or.inr hadj.symm
        · exact Or.inl rfl
      have hpair_ne : (a, u) ≠ (b, v) := fun h => huv (congrArg Prod.snd h)
      exact hS_indep hau hbv hpair_ne ⟨hpair_ne, hab, Or.inr hHadj⟩
    exact (Finset.card_union_of_disjoint hdisj).symm.trans_le hindep.card_le_indepNum
  have hshift : ∑ i : Fin n, (slice (i + 1)).card = ∑ i : Fin n, (slice i).card := by
    simpa only [Equiv.coe_addRight] using
      Equiv.sum_comp (Equiv.addRight (1 : Fin n)) (fun i => (slice i).card)
  calc 2 * S.card
      = S.card + S.card := two_mul S.card
    _ = (∑ i : Fin n, (slice i).card) + ∑ i : Fin n, (slice (i + 1)).card := by
        rw [hshift, hsum_card]
    _ = ∑ i : Fin n, ((slice i).card + (slice (i + 1)).card) := Finset.sum_add_distrib.symm
    _ ≤ ∑ _i : Fin n, H.indepNum := Finset.sum_le_sum fun i _ => hadj_bound i
    _ = n * H.indepNum := by
        rw [Finset.sum_const_nat fun _ _ => rfl, Finset.card_univ, Fintype.card_fin]

private lemma not_cycleGraph_adj_of_val_diff {n : ℕ} (hn : 3 ≤ n) (a b : Fin n) {δ : ℕ}
    (hδ_lo : 2 ≤ δ) (hδ_hi : δ ≤ n - 2)
    (hdiff : (a.val : ℤ) - (b.val : ℤ) ≡ (δ : ℤ) [ZMOD n] ∨
             (b.val : ℤ) - (a.val : ℤ) ≡ (δ : ℤ) [ZMOD n]) :
    ¬ (a = b ∨ (SimpleGraph.cycleGraph n).Adj a b) := by
  have hsub : ∀ x y : Fin n, (x.val : ℤ) - (y.val : ℤ) ≡ (δ : ℤ) [ZMOD n] →
      x ≠ y ∧ ¬ (SimpleGraph.cycleGraph n).Adj x y := by
    intro x y hmod
    have hx : x.val < n := x.isLt
    have hy : y.val < n := y.isLt
    have hne : x ≠ y := by
      intro h
      subst h
      rw [sub_self] at hmod
      have hdvd : (n : ℤ) ∣ (δ : ℤ) := by
        rw [Int.ModEq, Int.zero_emod] at hmod
        exact Int.dvd_of_emod_eq_zero hmod.symm
      have hle : (n : ℤ) ≤ δ := Int.le_of_dvd (by omega) hdvd
      omega
    refine ⟨hne, ?_⟩
    rw [SimpleGraph.cycleGraph_adj']
    rintro (h1 | h1)
    · have hxy_mod : (x.val : ℤ) - (y.val : ℤ) ≡ (1 : ℤ) [ZMOD n] := by
        by_cases hle : y ≤ x
        · have hcoe : (x - y).val = x.val - y.val := Fin.coe_sub_iff_le.mpr hle
          have : x.val - y.val = 1 := by rw [← hcoe, h1]
          have : (x.val : ℤ) - (y.val : ℤ) = 1 := by omega
          rw [this]
        · have hlt : x < y := lt_of_not_ge hle
          have hcoe : (x - y).val = n + x.val - y.val := Fin.coe_sub_iff_lt.mpr hlt
          have : n + x.val - y.val = 1 := by rw [← hcoe, h1]
          have hzx : (x.val : ℤ) - (y.val : ℤ) = 1 - (n : ℤ) := by omega
          rw [hzx, Int.modEq_iff_dvd]
          exact ⟨1, by ring⟩
      have h1δ : (1 : ℤ) ≡ (δ : ℤ) [ZMOD n] := hxy_mod.symm.trans hmod
      rw [Int.modEq_iff_dvd] at h1δ
      have hdvd : (n : ℤ) ∣ ((δ : ℤ) - 1) := by
        simpa [Int.ModEq] using h1δ
      have hle : (n : ℤ) ≤ (δ : ℤ) - 1 := Int.le_of_dvd (by omega) hdvd
      omega
    · have hyx_mod : (y.val : ℤ) - (x.val : ℤ) ≡ (1 : ℤ) [ZMOD n] := by
        by_cases hle : x ≤ y
        · have hcoe : (y - x).val = y.val - x.val := Fin.coe_sub_iff_le.mpr hle
          have : y.val - x.val = 1 := by rw [← hcoe, h1]
          have : (y.val : ℤ) - (x.val : ℤ) = 1 := by omega
          rw [this]
        · have hlt : y < x := lt_of_not_ge hle
          have hcoe : (y - x).val = n + y.val - x.val := Fin.coe_sub_iff_lt.mpr hlt
          have : n + y.val - x.val = 1 := by rw [← hcoe, h1]
          have hzy : (y.val : ℤ) - (x.val : ℤ) = 1 - (n : ℤ) := by omega
          rw [hzy, Int.modEq_iff_dvd]
          exact ⟨1, by ring⟩
      have hneg : (x.val : ℤ) - (y.val : ℤ) ≡ (-1 : ℤ) [ZMOD n] := by
        simpa using hyx_mod.neg
      have h1δ : (-1 : ℤ) ≡ (δ : ℤ) [ZMOD n] := hneg.symm.trans hmod
      rw [Int.modEq_iff_dvd] at h1δ
      have hdvd : (n : ℤ) ∣ ((δ : ℤ) + 1) := by
        have : (δ : ℤ) - (-1 : ℤ) = (δ : ℤ) + 1 := by ring
        rwa [this] at h1δ
      have hle : (n : ℤ) ≤ (δ : ℤ) + 1 := Int.le_of_dvd (by omega) hdvd
      omega
  rcases hdiff with h | h
  · rcases hsub a b h with ⟨hne, hadj⟩
    exact not_or.mpr ⟨hne, hadj⟩
  · rcases hsub b a h with ⟨hne, hadj⟩
    exact not_or.mpr ⟨hne.symm, fun ha => hadj ha.symm⟩

theorem oddCycle_indepNum (k : ℕ) (hk : 1 ≤ k) :
    (SimpleGraph.cycleGraph (2 * k + 1)).indepNum = k := by
  have hle : (SimpleGraph.cycleGraph (2 * k + 1)).indepNum ≤ k := by
    have hdc := cycleGraph_sliceDoubleCount (n := 2 * k + 1) (by omega) (⊥ : SimpleGraph PUnit.{1})
    have hiso : SimpleGraph.cycleGraph (2 * k + 1) ≃g
        SimpleGraph.cycleGraph (2 * k + 1) ⊠ (⊥ : SimpleGraph PUnit.{1}) :=
      strongProdPUnitRight (SimpleGraph.cycleGraph (2 * k + 1))
    have hbot : (⊥ : SimpleGraph PUnit.{1}).indepNum ≤ 1 := by
      simpa using indepNum_le_card (⊥ : SimpleGraph PUnit.{1})
    rw [← iso_indepNum_eq hiso] at hdc
    have hmul : (2 * k + 1) * (⊥ : SimpleGraph PUnit.{1}).indepNum ≤ 2 * k + 1 := by
      simpa using Nat.mul_le_mul_left (2 * k + 1) hbot
    omega
  have hge : k ≤ (SimpleGraph.cycleGraph (2 * k + 1)).indepNum := by
    let f : Fin k → Fin (2 * k + 1) := fun i => ⟨2 * i.val, by omega⟩
    have hpw : ∀ i j : Fin k, i < j →
        ¬ (f i = f j ∨ (SimpleGraph.cycleGraph (2 * k + 1)).Adj (f i) (f j)) := by
      intro i j hij
      apply not_cycleGraph_adj_of_val_diff (n := 2 * k + 1) (by omega) (f i) (f j)
        (δ := 2 * (j.val - i.val)) (by omega) (by omega)
      right
      have heq : ((f j).val : ℤ) - ((f i).val : ℤ) = ((2 * (j.val - i.val) : ℕ) : ℤ) := by
        simp only [f]
        have : i.val < j.val := hij
        omega
      rw [heq]
    have hinj : Function.Injective f := by
      intro i j hij
      rcases lt_trichotomy i j with h | rfl | h
      · exact absurd (Or.inl hij) (hpw i j h)
      · rfl
      · exact absurd (Or.inl hij.symm) (hpw j i h)
    let S : Finset (Fin (2 * k + 1)) := Finset.univ.image f
    have hind : (SimpleGraph.cycleGraph (2 * k + 1)).IsIndepSet (S : Set (Fin (2 * k + 1))) := by
      intro u hu v hv huv hadj
      simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hu hv
      rcases hu with ⟨i, rfl⟩
      rcases hv with ⟨j, rfl⟩
      rcases lt_trichotomy i j with h | rfl | h
      · exact hpw i j h (Or.inr hadj)
      · exact huv rfl
      · exact hpw j i h (Or.inr hadj.symm)
    have hcard : S.card = k := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    calc k = S.card := hcard.symm
      _ ≤ (SimpleGraph.cycleGraph (2 * k + 1)).indepNum := hind.card_le_indepNum
  omega

theorem oddCycle_pow2_indepNum_le (k : ℕ) (hk : 1 ≤ k) :
    (strongPowPi (SimpleGraph.cycleGraph (2 * k + 1)) 2).indepNum ≤ k ^ 2 + k / 2 := by
  have hdc := cycleGraph_sliceDoubleCount (n := 2 * k + 1) (by omega)
    (SimpleGraph.cycleGraph (2 * k + 1))
  rw [oddCycle_indepNum k hk] at hdc
  have hiso : strongPow (SimpleGraph.cycleGraph (2 * k + 1)) 2 ≃g
      SimpleGraph.cycleGraph (2 * k + 1) ⊠ SimpleGraph.cycleGraph (2 * k + 1) :=
    strongProdCongr (.refl) (strongProdPUnitRight (SimpleGraph.cycleGraph (2 * k + 1))).symm
  rw [← strongPow_indepNum_eq_pi, iso_indepNum_eq hiso]
  have hmul : (2 * k + 1) * k = 2 * (k ^ 2) + k := by ring
  omega

theorem oddCycle_pow2_indepNum_ge (k : ℕ) (hk : 1 ≤ k) :
    k ^ 2 + k / 2 ≤ (strongPowPi (SimpleGraph.cycleGraph (2 * k + 1)) 2).indepNum := by
  let n : ℕ := 2 * k + 1
  let M : ℕ := k ^ 2 + k / 2
  have hksq : k ^ 2 = k * k := sq k
  let xFun : ℕ → ℕ := fun t =>
    if k % 2 = 0 then t / (k / 2)
    else 2 * (t / k) + if k / 2 + 1 ≤ t % k then 1 else 0
  have hxFun_lt : ∀ t : ℕ, t < M → xFun t < n := by
    intro t ht
    by_cases heven : k % 2 = 0
    · have hk2 : 0 < k / 2 := by omega
      have hM : M = n * (k / 2) := by
        have hk_eq : k = 2 * (k / 2) := by omega
        dsimp only [M, n]
        nlinarith
      simp only [xFun, heven, ↓reduceIte]
      rw [Nat.div_lt_iff_lt_mul hk2]
      exact ht.trans_eq hM
    · simp only [xFun, heven, ↓reduceIte]
      have hk0 : 0 < k := by omega
      by_cases hq : t / k < k
      · split_ifs <;> omega
      · have ht_lt : t < k * k + k / 2 := by simpa [M, hksq] using ht
        have hlt_mul : t < (k + 1) * k := by
          have : k / 2 < k := by omega
          nlinarith
        have hq_lt : t / k < k + 1 := (Nat.div_lt_iff_lt_mul hk0).mpr hlt_mul
        have hq_eq : t / k = k := by omega
        have hrem : t % k < k / 2 := by
          have hdiv := Nat.div_add_mod t k
          rw [hq_eq] at hdiv
          omega
        have hnot : ¬ (k / 2 + 1 ≤ t % k) := by omega
        simp only [hq_eq, hnot, ↓reduceIte]
        omega
  let w : Fin M → Fin 2 → Fin n := fun t idx =>
    if idx = 0 then ⟨xFun t.val, hxFun_lt t.val t.isLt⟩
    else ⟨(2 * t.val) % n, Nat.mod_lt _ (by omega)⟩
  have hpw : ∀ t₁ t₂ : Fin M, t₁ < t₂ →
      ¬ (w t₁ = w t₂ ∨ (strongPowPi (SimpleGraph.cycleGraph n) 2).Adj (w t₁) (w t₂)) := by
    intro t₁ t₂ ht hrel
    rw [eq_or_strongPowPi_adj] at hrel
    have h0 := hrel 0
    have h1 := hrel 1
    simp only [w, ↓reduceIte, Fin.one_eq_zero_iff] at h0 h1
    have ht1_lt : t₁.val < k * k + k / 2 := by simpa [M, hksq] using t₁.isLt
    have ht2_lt : t₂.val < k * k + k / 2 := by simpa [M, hksq] using t₂.isLt
    have hx_mono : xFun t₁.val ≤ xFun t₂.val := by
      by_cases heven : k % 2 = 0
      · simp only [xFun, heven, ↓reduceIte]
        exact Nat.div_le_div_right (le_of_lt ht)
      · simp only [xFun, heven, ↓reduceIte]
        have hq_le : t₁.val / k ≤ t₂.val / k := Nat.div_le_div_right (le_of_lt ht)
        rcases eq_or_lt_of_le hq_le with hq_eq | hq_lt
        · have hr1 : t₁.val % k ≤ t₂.val % k := by
            have hd1 := Nat.div_add_mod t₁.val k
            have hd2 := Nat.div_add_mod t₂.val k
            rw [hq_eq] at hd1
            omega
          rw [hq_eq]
          split_ifs <;> omega
        · split_ifs <;> omega
    have hx1_lt : xFun t₁.val < n := hxFun_lt t₁.val t₁.isLt
    have hx2_lt : xFun t₂.val < n := hxFun_lt t₂.val t₂.isLt
    have hcase : xFun t₂.val ≤ xFun t₁.val + 1 ∨ (xFun t₁.val = 0 ∧ xFun t₂.val = 2 * k) := by
      rcases h0 with heq | hadj
      · have : xFun t₁.val = xFun t₂.val := congrArg Fin.val heq
        exact Or.inl (by omega)
      · rw [SimpleGraph.cycleGraph_adj'] at hadj
        rcases hadj with hdiff | hdiff
        · by_cases hle : xFun t₂.val ≤ xFun t₁.val
          · have hsub : ((⟨xFun t₁.val, hx1_lt⟩ : Fin n) - ⟨xFun t₂.val, hx2_lt⟩).val =
                xFun t₁.val - xFun t₂.val :=
              Fin.coe_sub_iff_le.mpr hle
            omega
          · have hlt : (⟨xFun t₁.val, hx1_lt⟩ : Fin n) < ⟨xFun t₂.val, hx2_lt⟩ :=
              lt_of_not_ge hle
            have hsub : ((⟨xFun t₁.val, hx1_lt⟩ : Fin n) - ⟨xFun t₂.val, hx2_lt⟩).val =
                n + xFun t₁.val - xFun t₂.val :=
              Fin.coe_sub_iff_lt.mpr hlt
            rw [hsub] at hdiff
            exact Or.inr ⟨by omega, by omega⟩
        · by_cases hle : xFun t₁.val ≤ xFun t₂.val
          · have hsub : ((⟨xFun t₂.val, hx2_lt⟩ : Fin n) - ⟨xFun t₁.val, hx1_lt⟩).val =
                xFun t₂.val - xFun t₁.val :=
              Fin.coe_sub_iff_le.mpr hle
            omega
          · omega
    rcases hcase with hclose | ⟨hx1_0, hx2_2k⟩
    · have hdt : 1 ≤ t₂.val - t₁.val ∧ t₂.val - t₁.val ≤ k - 1 := by
        refine ⟨by omega, ?_⟩
        by_cases heven : k % 2 = 0
        · simp only [xFun, heven, ↓reduceIte] at hclose
          have hk2 : 0 < k / 2 := by omega
          have hd1 := Nat.div_add_mod t₁.val (k / 2)
          have hd2 := Nat.div_add_mod t₂.val (k / 2)
          have hm1 := Nat.mod_lt t₁.val hk2
          have hm2 := Nat.mod_lt t₂.val hk2
          have hq_le : t₁.val / (k / 2) ≤ t₂.val / (k / 2) :=
            Nat.div_le_div_right (le_of_lt ht)
          have hq_diff : t₂.val / (k / 2) = t₁.val / (k / 2) ∨
              t₂.val / (k / 2) = t₁.val / (k / 2) + 1 := by omega
          rcases hq_diff with hq | hq
          · rw [hq] at hd2
            omega
          · rw [hq, Nat.mul_add, Nat.mul_one] at hd2
            omega
        · simp only [xFun, heven, ↓reduceIte] at hclose
          have hk0 : 0 < k := by omega
          have hd1 := Nat.div_add_mod t₁.val k
          have hd2 := Nat.div_add_mod t₂.val k
          have hm1 := Nat.mod_lt t₁.val hk0
          have hm2 := Nat.mod_lt t₂.val hk0
          have hq_le : t₁.val / k ≤ t₂.val / k := Nat.div_le_div_right (le_of_lt ht)
          have hq_diff : t₂.val / k ≤ t₁.val / k + 1 := by
            by_contra hbad
            have : t₁.val / k + 2 ≤ t₂.val / k := by omega
            split_ifs at hclose <;> omega
          rcases Nat.eq_or_lt_of_le hq_le with hq_eq | hq_lt
          · rw [← hq_eq] at hd2
            omega
          · have hq_succ : t₂.val / k = t₁.val / k + 1 := by omega
            rw [hq_succ, Nat.mul_add, Nat.mul_one] at hd2
            split_ifs at hclose <;> omega
      apply not_cycleGraph_adj_of_val_diff (n := n) (by omega) _ _
        (δ := 2 * (t₂.val - t₁.val)) (by omega) (by omega) _ h1
      right
      have hmod1 : (((2 * t₁.val % n : ℕ) : ℤ)) ≡ (2 * (t₁.val : ℤ)) [ZMOD n] := by
        exact_mod_cast Nat.mod_modEq (2 * t₁.val) n
      have hmod2 : (((2 * t₂.val % n : ℕ) : ℤ)) ≡ (2 * (t₂.val : ℤ)) [ZMOD n] := by
        exact_mod_cast Nat.mod_modEq (2 * t₂.val) n
      have hsub := hmod2.sub hmod1
      have hcast : 2 * (t₂.val : ℤ) - 2 * (t₁.val : ℤ) = ((2 * (t₂.val - t₁.val) : ℕ) : ℤ) := by
        omega
      rwa [hcast] at hsub
    · have hk2 : 2 ≤ k := by
        by_contra hlt
        have hk1 : k = 1 := by omega
        subst hk1
        have : M = 1 := by simp [M]
        omega
      by_cases heven : k % 2 = 0
      · simp only [xFun, heven, ↓reduceIte] at hx1_0 hx2_2k
        have hk2_pos : 0 < k / 2 := by omega
        have ht1_lt : t₁.val < k / 2 := by
          by_contra hge
          have : 1 ≤ t₁.val / (k / 2) := (Nat.le_div_iff_mul_le hk2_pos).mpr (by omega)
          omega
        have ht2_ge : k * k ≤ t₂.val := by
          have hd := (Nat.le_div_iff_mul_le hk2_pos).mp (by omega : 2 * k ≤ t₂.val / (k / 2))
          have hk_eq : k = 2 * (k / 2) := by omega
          have hmul : 2 * k * (k / 2) = k * k := by
            nlinarith
          omega
        let δ : ℕ := k + 2 * t₁.val - 2 * (t₂.val - k * k)
        have hδ_bounds : 2 ≤ δ ∧ δ ≤ n - 2 := by
          have ht2_sub : t₂.val - k * k < k / 2 := by omega
          omega
        apply not_cycleGraph_adj_of_val_diff (n := n) (by omega) _ _
          hδ_bounds.1 hδ_bounds.2 _ h1
        left
        have hmod1 : (((2 * t₁.val % n : ℕ) : ℤ)) ≡ (2 * (t₁.val : ℤ)) [ZMOD n] := by
          exact_mod_cast Nat.mod_modEq (2 * t₁.val) n
        have hmod2 : (((2 * t₂.val % n : ℕ) : ℤ)) ≡ (2 * (t₂.val : ℤ)) [ZMOD n] := by
          exact_mod_cast Nat.mod_modEq (2 * t₂.val) n
        have hsub := hmod1.sub hmod2
        have hdvd : (n : ℤ) ∣ ((δ : ℤ) - (2 * (t₁.val : ℤ) - 2 * (t₂.val : ℤ))) := by
          refine ⟨(k : ℤ), ?_⟩
          have hzn : (n : ℤ) = 2 * (k : ℤ) + 1 := by simp only [n]; push_cast; ring
          have hzδ : (δ : ℤ) = (k : ℤ) + 2 * (t₁.val : ℤ) - 2 * ((t₂.val : ℤ) - (k : ℤ) * (k : ℤ)) := by
            have : t₂.val - k * k ≤ k / 2 := by omega
            omega
          rw [hzn, hzδ]
          ring
        exact hsub.trans ((Int.modEq_iff_dvd).mpr hdvd)
      · simp only [xFun, heven, ↓reduceIte] at hx1_0 hx2_2k
        have hk0 : 0 < k := by omega
        have hd1 := Nat.div_add_mod t₁.val k
        have hq1_0 : t₁.val / k = 0 := by omega
        have ht1_le : t₁.val ≤ k / 2 := by
          have hr1 : t₁.val = t₁.val % k := by rw [hq1_0, mul_zero, zero_add] at hd1; exact hd1.symm
          split_ifs at hx1_0; omega
        have ht2_ge : k * k ≤ t₂.val := by
          have hq2_ge : k ≤ t₂.val / k := by split_ifs at hx2_2k <;> omega
          have hmul : k * k ≤ k * (t₂.val / k) := Nat.mul_le_mul_left k hq2_ge
          exact hmul.trans (Nat.mul_div_le t₂.val k)
        let δ : ℕ := k + 2 * t₁.val - 2 * (t₂.val - k * k)
        have hδ_bounds : 2 ≤ δ ∧ δ ≤ n - 2 := by
          have ht2_sub : t₂.val - k * k < k / 2 := by omega
          omega
        apply not_cycleGraph_adj_of_val_diff (n := n) (by omega) _ _
          hδ_bounds.1 hδ_bounds.2 _ h1
        left
        have hmod1 : (((2 * t₁.val % n : ℕ) : ℤ)) ≡ (2 * (t₁.val : ℤ)) [ZMOD n] := by
          exact_mod_cast Nat.mod_modEq (2 * t₁.val) n
        have hmod2 : (((2 * t₂.val % n : ℕ) : ℤ)) ≡ (2 * (t₂.val : ℤ)) [ZMOD n] := by
          exact_mod_cast Nat.mod_modEq (2 * t₂.val) n
        have hsub := hmod1.sub hmod2
        have hdvd : (n : ℤ) ∣ ((δ : ℤ) - (2 * (t₁.val : ℤ) - 2 * (t₂.val : ℤ))) := by
          refine ⟨(k : ℤ), ?_⟩
          have hzn : (n : ℤ) = 2 * (k : ℤ) + 1 := by simp only [n]; push_cast; ring
          have hzδ : (δ : ℤ) = (k : ℤ) + 2 * (t₁.val : ℤ) - 2 * ((t₂.val : ℤ) - (k : ℤ) * (k : ℤ)) := by
            have : t₂.val - k * k ≤ k / 2 := by omega
            omega
          rw [hzn, hzδ]
          ring
        exact hsub.trans ((Int.modEq_iff_dvd).mpr hdvd)
  have hinj : Function.Injective w := by
    intro t₁ t₂ hij
    rcases lt_trichotomy t₁ t₂ with h | rfl | h
    · exact absurd (Or.inl hij) (hpw t₁ t₂ h)
    · rfl
    · exact absurd (Or.inl hij.symm) (hpw t₂ t₁ h)
  let S : Finset (Fin 2 → Fin n) := Finset.univ.image w
  have hind : (strongPowPi (SimpleGraph.cycleGraph n) 2).IsIndepSet (S : Set (Fin 2 → Fin n)) := by
    intro u hu v hv huv hadj
    simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hu hv
    rcases hu with ⟨t₁, rfl⟩
    rcases hv with ⟨t₂, rfl⟩
    rcases lt_trichotomy t₁ t₂ with h | rfl | h
    · exact hpw t₁ t₂ h (Or.inr hadj)
    · exact huv rfl
    · exact hpw t₂ t₁ h (Or.inr hadj.symm)
  have hcard : S.card = M := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  calc k ^ 2 + k / 2 = M := rfl
    _ = S.card := hcard.symm
    _ ≤ (strongPowPi (SimpleGraph.cycleGraph (2 * k + 1)) 2).indepNum := hind.card_le_indepNum

theorem oddCycle_pow2_indepNum (k : ℕ) (hk : 1 ≤ k) :
    (strongPowPi (SimpleGraph.cycleGraph (2 * k + 1)) 2).indepNum = k ^ 2 + k / 2 :=
  le_antisymm (oddCycle_pow2_indepNum_le k hk) (oddCycle_pow2_indepNum_ge k hk)

theorem oddCycle_pow2_indepNum_eq_div (k : ℕ) (hk : 1 ≤ k) :
    (strongPowPi (SimpleGraph.cycleGraph (2 * k + 1)) 2).indepNum = (k * (2 * k + 1)) / 2 := by
  rw [oddCycle_pow2_indepNum k hk]
  have hmul : k * (2 * k + 1) = 2 * (k ^ 2) + k := by ring
  omega

/-! ## Part 2A: Fractional Clique Cover & Weak Duality -/

section FracCover
open Classical

set_option linter.unusedFintypeInType false in
/-- A fractional clique cover of a finite graph `G`: a non-negative weighting of cliques
covering every vertex with total weight at least `1`. -/
structure FracCliqueCover {V : Type*} [Fintype V] (G : SimpleGraph V) where
  weight : Finset V → ℝ
  nonneg : ∀ C, 0 ≤ weight C
  clique_of_pos : ∀ C, 0 < weight C → G.IsClique (C : Set V)
  cover : ∀ v : V, 1 ≤ ∑ C : Finset V, if v ∈ C then weight C else 0

/-- Total weight of a fractional clique cover. -/
def FracCliqueCover.total {V : Type*} [Fintype V] {G : SimpleGraph V}
    (c : FracCliqueCover G) : ℝ :=
  ∑ C : Finset V, c.weight C

theorem FracCliqueCover.total_nonneg {V : Type*} [Fintype V] {G : SimpleGraph V}
    (c : FracCliqueCover G) : 0 ≤ c.total :=
  Finset.sum_nonneg fun C _ => c.nonneg C

/-- The fractional clique cover number `χ̄_f(G)`. -/
noncomputable def fracCliqueCoverNum {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sInf {x : ℝ | ∃ c : FracCliqueCover G, c.total = x}

/-- Construct a fractional clique cover from an indexed family of cliques with non-negative weights. -/
noncomputable def FracCliqueCover.ofFamily {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) (C : ι → Finset V) (w : ι → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hC_clique : ∀ i, 0 < w i → G.IsClique (C i : Set V))
    (hcover : ∀ v : V, 1 ≤ ∑ i : ι, if v ∈ C i then w i else 0) :
    FracCliqueCover G where
  weight D := ∑ i : ι, if C i = D then w i else 0
  nonneg D := Finset.sum_nonneg fun i _ => by split_ifs; exact hw_nonneg i; exact le_rfl
  clique_of_pos D hD := by
    by_contra hnot
    have hzero : (∑ i : ι, if C i = D then w i else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with hi
      · by_cases hpos : 0 < w i
        · subst hi
          exact absurd (hC_clique i hpos) hnot
        · exact le_antisymm (not_lt.mp hpos) (hw_nonneg i)
      · rfl
    linarith
  cover v := by
    have hsum :
        (∑ D : Finset V, if v ∈ D then ∑ i : ι, if C i = D then w i else 0 else 0) =
          ∑ i : ι, if v ∈ C i then w i else 0 := by
      calc (∑ D : Finset V, if v ∈ D then ∑ i : ι, if C i = D then w i else 0 else 0)
          = ∑ D : Finset V, ∑ i : ι, if C i = D then (if v ∈ D then w i else 0) else 0 := by
              refine Finset.sum_congr rfl fun D _ => ?_
              split_ifs with hv <;> simp
        _ = ∑ i : ι, ∑ D : Finset V, if C i = D then (if v ∈ D then w i else 0) else 0 :=
              Finset.sum_comm
        _ = ∑ i : ι, if v ∈ C i then w i else 0 := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_eq_single (C i)]
              · simp
              · intro D _ hD
                simp [hD.symm]
              · intro hmem
                exact absurd (Finset.mem_univ _) hmem
    rw [hsum]
    exact hcover v

theorem FracCliqueCover.ofFamily_total {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) (C : ι → Finset V) (w : ι → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hC_clique : ∀ i, 0 < w i → G.IsClique (C i : Set V))
    (hcover : ∀ v : V, 1 ≤ ∑ i : ι, if v ∈ C i then w i else 0) :
    (FracCliqueCover.ofFamily G C w hw_nonneg hC_clique hcover).total = ∑ i : ι, w i := by
  unfold FracCliqueCover.total FracCliqueCover.ofFamily
  dsimp only
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (C i)]
  · simp
  · intro D _ hD
    simp [hD.symm]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- Trivial unit fractional clique cover on `⊥ : SimpleGraph PUnit.{u + 1}`. -/
noncomputable def FracCliqueCover.unit.{u} : FracCliqueCover (⊥ : SimpleGraph PUnit.{u + 1}) where
  weight C := if C = Finset.univ then 1 else 0
  nonneg C := by split_ifs <;> norm_num
  clique_of_pos C _ := by
    intro a _ b _ hab
    exact absurd (Subsingleton.elim a b) hab
  cover v := by
    rw [Finset.sum_eq_single (Finset.univ : Finset PUnit.{u + 1})]
    · simp
    · intro D _ hD
      rw [if_neg hD]
      simp
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem

theorem FracCliqueCover.unit_total.{u} : (FracCliqueCover.unit.{u}).total = 1 := by
  unfold FracCliqueCover.total FracCliqueCover.unit
  dsimp only
  rw [Finset.sum_eq_single (Finset.univ : Finset PUnit.{u + 1})]
  · simp
  · intro D _ hD
    rw [if_neg hD]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- Strong product of two fractional clique covers. -/
noncomputable def FracCliqueCover.prod {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (c₁ : FracCliqueCover G) (c₂ : FracCliqueCover H) :
    FracCliqueCover (G ⊠ H) := by
  refine FracCliqueCover.ofFamily (G ⊠ H)
    (fun p : Finset V × Finset W => p.1 ×ˢ p.2)
    (fun p : Finset V × Finset W => c₁.weight p.1 * c₂.weight p.2)
    (fun p => mul_nonneg (c₁.nonneg p.1) (c₂.nonneg p.2))
    ?_ ?_
  · rintro ⟨C₁, C₂⟩ hpos ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ hne
    simp only [Finset.mem_coe, Finset.mem_product] at h₁ h₂
    have hpos1 : 0 < c₁.weight C₁ := by
      by_contra hle
      have h0 : c₁.weight C₁ = 0 := le_antisymm (not_lt.mp hle) (c₁.nonneg C₁)
      rw [h0, zero_mul] at hpos
      exact lt_irrefl 0 hpos
    have hpos2 : 0 < c₂.weight C₂ := by
      by_contra hle
      have h0 : c₂.weight C₂ = 0 := le_antisymm (not_lt.mp hle) (c₂.nonneg C₂)
      rw [h0, mul_zero] at hpos
      exact lt_irrefl 0 hpos
    have hG : u₁ = u₂ ∨ G.Adj u₁ u₂ := by
      by_cases hu : u₁ = u₂
      · exact Or.inl hu
      · exact Or.inr (c₁.clique_of_pos C₁ hpos1 h₁.1 h₂.1 hu)
    have hH : v₁ = v₂ ∨ H.Adj v₁ v₂ := by
      by_cases hv : v₁ = v₂
      · exact Or.inl hv
      · exact Or.inr (c₂.clique_of_pos C₂ hpos2 h₁.2 h₂.2 hv)
    exact ⟨hne, hG, hH⟩
  · rintro ⟨u, v⟩
    have hsum :
        (∑ p : Finset V × Finset W, if (u, v) ∈ p.1 ×ˢ p.2 then c₁.weight p.1 * c₂.weight p.2 else 0) =
          (∑ C₁ : Finset V, if u ∈ C₁ then c₁.weight C₁ else 0) *
            (∑ C₂ : Finset W, if v ∈ C₂ then c₂.weight C₂ else 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      refine Finset.sum_congr rfl fun C₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun C₂ _ => ?_
      simp only [Finset.mem_product]
      by_cases hu : u ∈ C₁ <;> by_cases hv : v ∈ C₂ <;> simp [hu, hv]
    have hmul : 1 ≤ (∑ C₁ : Finset V, if u ∈ C₁ then c₁.weight C₁ else 0) *
        (∑ C₂ : Finset W, if v ∈ C₂ then c₂.weight C₂ else 0) := by
      nlinarith [c₁.cover u, c₂.cover v]
    convert hmul.trans_eq hsum.symm

theorem FracCliqueCover.prod_total {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (c₁ : FracCliqueCover G) (c₂ : FracCliqueCover H) :
    (c₁.prod c₂).total = c₁.total * c₂.total := by
  unfold FracCliqueCover.prod
  rw [FracCliqueCover.ofFamily_total, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rfl

/-- Iterated strong power of a fractional clique cover. -/
noncomputable def FracCliqueCover.pow.{u} {V : Type u} [Fintype V] {G : SimpleGraph V}
    (c : FracCliqueCover G) : (d : ℕ) → FracCliqueCover (strongPow G d)
  | 0 => FracCliqueCover.unit.{u}
  | d + 1 => c.prod (c.pow d)

theorem FracCliqueCover.pow_total.{u} {V : Type u} [Fintype V] {G : SimpleGraph V}
    (c : FracCliqueCover G) : ∀ d : ℕ, (c.pow d).total = c.total ^ d
  | 0 => by
      change FracCliqueCover.unit.{u}.total = c.total ^ 0
      rw [FracCliqueCover.unit_total.{u}, pow_zero]
  | d + 1 => by
      change (c.prod (c.pow d)).total = c.total ^ (d + 1)
      rw [FracCliqueCover.prod_total, c.pow_total d, pow_succ']

set_option linter.unusedFintypeInType false in
/-- A fractional independent set of `G`: vertex weights in `[0, ∞)` summing to `≤ 1` on every clique. -/
structure FracIndepSet {V : Type*} [Fintype V] (G : SimpleGraph V) where
  weight : V → ℝ
  nonneg : ∀ v, 0 ≤ weight v
  clique_le_one : ∀ C : Finset V, G.IsClique (C : Set V) → ∑ v ∈ C, weight v ≤ 1

/-- Total weight of a fractional independent set. -/
def FracIndepSet.total {V : Type*} [Fintype V] {G : SimpleGraph V}
    (y : FracIndepSet G) : ℝ :=
  ∑ v : V, y.weight v

/-- The fractional independence number `α_f(G)`. -/
noncomputable def fracIndepNum {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sSup {x : ℝ | ∃ y : FracIndepSet G, y.total = x}

theorem fracIndepSet_le_fracCliqueCover {V : Type*} [Fintype V] {G : SimpleGraph V}
    (y : FracIndepSet G) (c : FracCliqueCover G) :
    y.total ≤ c.total := by
  have h1 : y.total ≤ ∑ v : V, y.weight v * (∑ C : Finset V, if v ∈ C then c.weight C else 0) := by
    refine Finset.sum_le_sum fun v _ => ?_
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (c.cover v) (y.nonneg v)
  have h2 :
      (∑ v : V, y.weight v * (∑ C : Finset V, if v ∈ C then c.weight C else 0)) =
        ∑ C : Finset V, c.weight C * (∑ v ∈ C, y.weight v) := by
    have h1' :
        (∑ v : V, y.weight v * (∑ C : Finset V, if v ∈ C then c.weight C else 0)) =
          ∑ C : Finset V, ∑ x : V, y.weight x * if x ∈ C then c.weight C else 0 := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    rw [h1']
    refine Finset.sum_congr rfl fun C _ => ?_
    calc (∑ x : V, y.weight x * if x ∈ C then c.weight C else 0)
        = ∑ x : V, if x ∈ C then c.weight C * y.weight x else 0 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            split_ifs <;> ring
      _ = ∑ x ∈ Finset.univ.filter (fun x : V => x ∈ C), c.weight C * y.weight x := by
            rw [Finset.sum_filter]
      _ = ∑ x ∈ C, c.weight C * y.weight x := by
            have hfilt : (Finset.univ.filter fun x : V => x ∈ C) = C := by ext x; simp
            rw [hfilt]
      _ = c.weight C * ∑ x ∈ C, y.weight x := (Finset.mul_sum C _ _).symm
  have h3 : (∑ C : Finset V, c.weight C * (∑ v ∈ C, y.weight v)) ≤ c.total := by
    refine Finset.sum_le_sum fun C _ => ?_
    by_cases hpos : 0 < c.weight C
    · simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (y.clique_le_one C (c.clique_of_pos C hpos)) (c.nonneg C)
    · have h0 : c.weight C = 0 := le_antisymm (not_lt.mp hpos) (c.nonneg C)
      simp [h0]
  exact h1.trans (h2.trans_le h3)

private lemma fracCliqueCover_set_nonempty {V : Type*} [Fintype V] (G : SimpleGraph V) :
    {x : ℝ | ∃ c : FracCliqueCover G, c.total = x}.Nonempty := by
  let c : FracCliqueCover G :=
    FracCliqueCover.ofFamily G (fun v : V => ({v} : Finset V)) (fun _ => 1)
      (fun _ => zero_le_one)
      (fun v _ => by simp)
      (fun v => by
        rw [Finset.sum_eq_single v]
        · simp
        · intro u _ huv
          simp [Ne.symm huv]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem)
  exact ⟨c.total, c, rfl⟩

private lemma fracCliqueCover_set_bddBelow {V : Type*} [Fintype V] (G : SimpleGraph V) :
    BddBelow {x : ℝ | ∃ c : FracCliqueCover G, c.total = x} :=
  ⟨0, by rintro x ⟨c, rfl⟩; exact c.total_nonneg⟩

private lemma fracIndepSet_set_nonempty {V : Type*} [Fintype V] (G : SimpleGraph V) :
    {x : ℝ | ∃ y : FracIndepSet G, y.total = x}.Nonempty :=
  ⟨0, ⟨fun _ => 0, fun _ => le_rfl, fun _ _ => by simp⟩, by simp [FracIndepSet.total]⟩

private lemma fracIndepSet_set_bddAbove {V : Type*} [Fintype V] (G : SimpleGraph V) :
    BddAbove {x : ℝ | ∃ y : FracIndepSet G, y.total = x} := by
  obtain ⟨x, c, rfl⟩ := fracCliqueCover_set_nonempty G
  refine ⟨c.total, ?_⟩
  rintro t ⟨y, rfl⟩
  exact fracIndepSet_le_fracCliqueCover y c

theorem fracIndepNum_le_fracCliqueCoverNum {V : Type*} [Fintype V] (G : SimpleGraph V) :
    fracIndepNum G ≤ fracCliqueCoverNum G := by
  apply csSup_le (fracIndepSet_set_nonempty G)
  rintro x ⟨y, rfl⟩
  apply le_csInf (fracCliqueCover_set_nonempty G)
  rintro z ⟨c, rfl⟩
  exact fracIndepSet_le_fracCliqueCover y c

theorem fracCliqueCoverNum_nonneg {V : Type*} [Fintype V] (G : SimpleGraph V) :
    0 ≤ fracCliqueCoverNum G :=
  le_csInf (fracCliqueCover_set_nonempty G) (by rintro x ⟨c, rfl⟩; exact c.total_nonneg)

theorem fracCliqueCoverNum_le_of_cover {V : Type*} [Fintype V] {G : SimpleGraph V}
    (c : FracCliqueCover G) : fracCliqueCoverNum G ≤ c.total :=
  csInf_le (fracCliqueCover_set_bddBelow G) ⟨c, rfl⟩

theorem indepNum_le_fracCliqueCoverNum {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (G.indepNum : ℝ) ≤ fracCliqueCoverNum G := by
  obtain ⟨S, hS_indep, hS_card⟩ := G.exists_isNIndepSet_indepNum
  let y : FracIndepSet G :=
    { weight := fun v => if v ∈ S then 1 else 0
      nonneg := fun v => by split_ifs <;> norm_num
      clique_le_one := fun C hC => by
        have hsub : (C.filter fun v => v ∈ S).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter] at ha hb
          by_contra hab
          exact hS_indep ha.2 hb.2 hab (hC ha.1 hb.1 hab)
        have hsum : (∑ v ∈ C, if v ∈ S then (1 : ℝ) else 0) = ((C.filter fun v => v ∈ S).card : ℝ) := by
          simp [Finset.card_filter]
        rw [hsum]
        exact_mod_cast hsub }
  have hytot : y.total = (G.indepNum : ℝ) := by
    unfold FracIndepSet.total y
    dsimp only
    rw [← hS_card]
    simp
  have hy_le : y.total ≤ fracIndepNum G :=
    le_csSup (fracIndepSet_set_bddAbove G) ⟨y, rfl⟩
  rw [hytot] at hy_le
  exact hy_le.trans (fracIndepNum_le_fracCliqueCoverNum G)

theorem shannonCapacity_le_fracCliqueCoverNum {V : Type*} [Fintype V] (G : SimpleGraph V) :
    shannonCapacity G ≤ fracCliqueCoverNum G := by
  apply le_csInf (fracCliqueCover_set_nonempty G)
  rintro x ⟨c, rfl⟩
  refine shannonCapacity_le G c.total_nonneg fun d _ => ?_
  have h1 := indepNum_le_fracCliqueCoverNum (strongPow G d)
  have h2 := fracCliqueCoverNum_le_of_cover (c.pow d)
  rw [c.pow_total d] at h2
  exact h1.trans h2

theorem fracCliqueCover_prod_bound {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    ((G ⊠ H).indepNum : ℝ) ≤ fracCliqueCoverNum G * (H.indepNum : ℝ) := by
  obtain ⟨S, hS_indep, hS_card⟩ := (G ⊠ H).exists_isNIndepSet_indepNum
  rw [← hS_card]
  have hbound : ∀ c : FracCliqueCover G, (S.card : ℝ) ≤ c.total * (H.indepNum : ℝ) := by
    intro c
    have hC_bound : ∀ C : Finset V, G.IsClique (C : Set V) →
        ((S.filter fun p : V × W => p.1 ∈ C).card : ℝ) ≤ (H.indepNum : ℝ) := by
      intro C hC
      let T : Finset W := (S.filter fun p : V × W => p.1 ∈ C).image Prod.snd
      have hT_indep : H.IsIndepSet (T : Set W) := by
        intro w₁ hw₁ w₂ hw₂ hwne hadj
        simp only [T, Finset.coe_image, Set.mem_image, Finset.mem_coe,
          Finset.mem_filter, Prod.exists] at hw₁ hw₂
        rcases hw₁ with ⟨u₁, v₁, ⟨h1S, h1C⟩, rfl⟩
        rcases hw₂ with ⟨u₂, v₂, ⟨h2S, h2C⟩, rfl⟩
        have hpair_ne : (u₁, v₁) ≠ (u₂, v₂) := fun h => hwne (congrArg Prod.snd h)
        have hu_rel : u₁ = u₂ ∨ G.Adj u₁ u₂ := by
          by_cases hu : u₁ = u₂
          · exact Or.inl hu
          · exact Or.inr (hC h1C h2C hu)
        exact hS_indep h1S h2S hpair_ne ⟨hpair_ne, hu_rel, Or.inr hadj⟩
      have hcard_eq : (S.filter fun p : V × W => p.1 ∈ C).card = T.card := by
        symm
        apply Finset.card_image_of_injOn
        rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ hv
        simp only [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
        have hv_eq : v₁ = v₂ := hv
        by_contra hpair
        have hu_ne : u₁ ≠ u₂ := fun hu => hpair (Prod.ext hu hv_eq)
        have hadj : G.Adj u₁ u₂ := hC h₁.2 h₂.2 hu_ne
        exact hS_indep h₁.1 h₂.1 hpair ⟨hpair, Or.inr hadj, Or.inl hv_eq⟩
      rw [hcard_eq]
      exact_mod_cast hT_indep.card_le_indepNum
    calc (S.card : ℝ)
        = ∑ _p ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ p ∈ S, ∑ C : Finset V, if p.1 ∈ C then c.weight C else 0 :=
          Finset.sum_le_sum fun p _ => c.cover p.1
      _ = ∑ C : Finset V, c.weight C * ((S.filter fun p : V × W => p.1 ∈ C).card : ℝ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun C _ => ?_
          have hsum_ite :
              (∑ p ∈ S, if p.1 ∈ C then c.weight C else 0) =
                ∑ _p ∈ S.filter (fun p : V × W => p.1 ∈ C), c.weight C := by
            rw [Finset.sum_filter]
          rw [hsum_ite, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ C : Finset V, c.weight C * (H.indepNum : ℝ) := by
          refine Finset.sum_le_sum fun C _ => ?_
          by_cases hpos : 0 < c.weight C
          · exact mul_le_mul_of_nonneg_left (hC_bound C (c.clique_of_pos C hpos)) (c.nonneg C)
          · have h0 : c.weight C = 0 := le_antisymm (not_lt.mp hpos) (c.nonneg C)
            simp [h0]
      _ = c.total * (H.indepNum : ℝ) := by
          rw [← Finset.sum_mul]
          rfl
  by_cases hH : H.indepNum = 0
  · have hbot : (S.card : ℝ) ≤ 0 := by
      obtain ⟨_, c, rfl⟩ := fracCliqueCover_set_nonempty G
      have hc := hbound c
      simpa [hH] using hc
    simpa [hH] using hbot
  · have hHpos : (0 : ℝ) < (H.indepNum : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hH)
    rw [← div_le_iff₀ hHpos]
    apply le_csInf (fracCliqueCover_set_nonempty G)
    rintro x ⟨c, rfl⟩
    exact (div_le_iff₀ hHpos).mpr (hbound c)

theorem fracCliqueCoverNum_mul_le {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    fracCliqueCoverNum (G ⊠ H) ≤ fracCliqueCoverNum G * fracCliqueCoverNum H := by
  have h1 : ∀ c₁ : FracCliqueCover G,
      fracCliqueCoverNum (G ⊠ H) ≤ c₁.total * fracCliqueCoverNum H := by
    intro c₁
    by_cases hc1 : c₁.total = 0
    · obtain ⟨_, c₂, rfl⟩ := fracCliqueCover_set_nonempty H
      have h := fracCliqueCoverNum_le_of_cover (c₁.prod c₂)
      rw [c₁.prod_total c₂, hc1, zero_mul] at h
      simpa [hc1] using h
    · have hc1_pos : 0 < c₁.total := lt_of_le_of_ne c₁.total_nonneg (Ne.symm hc1)
      rw [← div_le_iff₀' hc1_pos]
      apply le_csInf (fracCliqueCover_set_nonempty H)
      rintro y ⟨c₂, rfl⟩
      rw [div_le_iff₀' hc1_pos, ← c₁.prod_total c₂]
      exact fracCliqueCoverNum_le_of_cover (c₁.prod c₂)
  by_cases hH : fracCliqueCoverNum H = 0
  · obtain ⟨_, c₁, rfl⟩ := fracCliqueCover_set_nonempty G
    simpa [hH] using h1 c₁
  · have hHpos : 0 < fracCliqueCoverNum H :=
      lt_of_le_of_ne (fracCliqueCoverNum_nonneg H) (Ne.symm hH)
    rw [← div_le_iff₀ hHpos]
    apply le_csInf (fracCliqueCover_set_nonempty G)
    rintro x ⟨c₁, rfl⟩
    exact (div_le_iff₀ hHpos).mpr (h1 c₁)

end FracCover

/-! ## Part 2B: Vertex-Transitive Graphs & Odd-Cycle Clique Covers -/

/-- A graph `G` is vertex-transitive if its automorphism group acts transitively on vertices. -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ e : G ≃g G, e u = v

theorem cycleGraph_isVertexTransitive (n : ℕ) :
    IsVertexTransitive (SimpleGraph.cycleGraph n) := by
  intro u v
  rcases n with _ | m
  · exact Fin.elim0 u
  · let e : SimpleGraph.cycleGraph (m + 1) ≃g SimpleGraph.cycleGraph (m + 1) :=
      { toEquiv := Equiv.addRight (v - u)
        map_rel_iff' := by
          intro a b
          simp only [Equiv.coe_addRight, SimpleGraph.cycleGraph_adj']
          have h1 : (a + (v - u)) - (b + (v - u)) = a - b := by
            rw [add_sub_add_right_eq_sub]
          have h2 : (b + (v - u)) - (a + (v - u)) = b - a := by
            rw [add_sub_add_right_eq_sub]
          rw [h1, h2] }
    exact ⟨e, by simp [e]⟩

theorem isVertexTransitive_compl {V : Type*} {G : SimpleGraph V}
    (hG : IsVertexTransitive G) : IsVertexTransitive Gᶜ := by
  intro u v
  obtain ⟨e, he⟩ := hG u v
  exact ⟨isoCompl e, he⟩

theorem isVertexTransitive_strongPowPi {V : Type*} {G : SimpleGraph V}
    (hG : IsVertexTransitive G) (d : ℕ) : IsVertexTransitive (strongPowPi G d) := by
  intro u v
  choose f hf using fun i : Fin d => hG (u i) (v i)
  refine ⟨{ toEquiv :=
              { toFun := fun x i => f i (x i)
                invFun := fun x i => (f i).symm (x i)
                left_inv := fun x => funext fun i => (f i).symm_apply_apply (x i)
                right_inv := fun x => funext fun i => (f i).apply_symm_apply (x i) }
            map_rel_iff' := by
              intro a b
              simp only [Equiv.coe_fn_mk, strongPowPi_adj, ne_eq]
              constructor
              · rintro ⟨hne, h⟩
                refine ⟨fun hab => hne (by subst hab; rfl), fun i => ?_⟩
                rcases h i with heq | hadj
                · exact Or.inl ((f i).injective heq)
                · exact Or.inr ((f i).map_adj_iff.mp hadj)
              · rintro ⟨hne, h⟩
                refine ⟨fun hab => hne (funext fun i => (f i).injective (congr_fun hab i)),
                  fun i => ?_⟩
                rcases h i with heq | hadj
                · exact Or.inl (congrArg (f i) heq)
                · exact Or.inr ((f i).map_adj_iff.mpr hadj) }, ?_⟩
  funext i
  exact hf i

theorem fracCliqueCoverNum_eq_card_div_cliqueNum_of_vertexTransitive
    {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    (hG : IsVertexTransitive G) :
    fracCliqueCoverNum G = (Fintype.card V : ℝ) / (G.cliqueNum : ℝ) := by
  classical
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hclq_pos : 0 < G.cliqueNum := by
    have h1 : G.IsClique (({v₀} : Finset V) : Set V) := by simp
    have hle := h1.card_le_cliqueNum
    simp only [Finset.card_singleton] at hle
    exact Nat.pos_of_ne_zero (by omega)
  have hclq_pos_real : (0 : ℝ) < (G.cliqueNum : ℝ) := Nat.cast_pos.mpr hclq_pos
  apply le_antisymm
  · obtain ⟨K, hK_nclq⟩ := G.exists_isNClique_cliqueNum
    have hK_clq : G.IsClique (K : Set V) := hK_nclq.isClique
    have hK_card : K.card = G.cliqueNum := hK_nclq.card_eq
    let auts : Finset (Equiv.Perm V) :=
      Finset.univ.filter fun σ : Equiv.Perm V => ∀ x y : V, G.Adj (σ x) (σ y) ↔ G.Adj x y
    have hauts_nonempty : auts.Nonempty := ⟨1, by
      simp only [auts, Finset.mem_filter, Finset.mem_univ, Equiv.Perm.one_apply, implies_true,
        and_self]⟩
    have hauts_pos : (0 : ℝ) < (auts.card : ℝ) := Nat.cast_pos.mpr hauts_nonempty.card_pos
    have hfiber : ∀ u v : V,
        (auts.filter fun σ : Equiv.Perm V => σ u = v).card =
          (auts.filter fun σ : Equiv.Perm V => σ u = u).card := by
      intro u v
      obtain ⟨e, he⟩ := hG u v
      let σ₀ : Equiv.Perm V := e.toEquiv
      have hσ₀_aut : ∀ x y : V, G.Adj (σ₀ x) (σ₀ y) ↔ G.Adj x y := fun x y => e.map_adj_iff
      refine Finset.card_bij (fun σ _ => σ₀.symm * σ) ?_ ?_ ?_
      · intro σ hσ
        simp only [Finset.mem_filter, auts, Finset.mem_univ, true_and] at hσ ⊢
        refine ⟨fun x y => ?_, ?_⟩
        · simp only [Equiv.Perm.mul_apply]
          rw [← hσ₀_aut (σ₀.symm (σ x)) (σ₀.symm (σ y)), σ₀.apply_symm_apply, σ₀.apply_symm_apply,
            hσ.1]
        · simp only [Equiv.Perm.mul_apply, hσ.2]
          exact σ₀.symm_apply_eq.mpr he.symm
      · intro σ₁ _ σ₂ _ h
        exact mul_left_cancel h
      · intro τ hτ
        simp only [Finset.mem_filter, auts, Finset.mem_univ, true_and] at hτ
        refine ⟨σ₀ * τ, ?_, ?_⟩
        · simp only [Finset.mem_filter, auts, Finset.mem_univ, true_and]
          refine ⟨fun x y => ?_, ?_⟩
          · simp only [Equiv.Perm.mul_apply, hσ₀_aut, hτ.1]
          · simp only [Equiv.Perm.mul_apply, hτ.2]
            exact he
        · change σ₀⁻¹ * (σ₀ * τ) = τ; exact inv_mul_cancel_left _ _
    have hfiber_const : ∀ u v : V,
        Fintype.card V * (auts.filter fun σ : Equiv.Perm V => σ u = v).card = auts.card := by
      intro u v
      have hsum :
          (∑ w : V, (auts.filter fun σ : Equiv.Perm V => σ u = w).card) = auts.card := by
        exact (Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm V => σ u)
          (s := auts) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm
      calc Fintype.card V * (auts.filter fun σ : Equiv.Perm V => σ u = v).card
          = ∑ _w : V, (auts.filter fun σ : Equiv.Perm V => σ u = v).card := by
              rw [Finset.sum_const_nat fun _ _ => rfl, Finset.card_univ]
        _ = ∑ w : V, (auts.filter fun σ : Equiv.Perm V => σ u = w).card := by
              refine Finset.sum_congr rfl fun w _ => ?_
              rw [hfiber u w, hfiber u v]
        _ = auts.card := hsum
    let denom : ℝ := (auts.card : ℝ) * (G.cliqueNum : ℝ)
    have hdenom_pos : 0 < denom := mul_pos hauts_pos hclq_pos_real
    let fam : auts → Finset V := fun σ => K.map σ.1.toEmbedding
    let w : auts → ℝ := fun _ => (Fintype.card V : ℝ) / denom
    have hw_nonneg : ∀ σ : auts, 0 ≤ w σ := fun _ => div_nonneg (Nat.cast_nonneg _) hdenom_pos.le
    have hfam_clq : ∀ σ : auts, 0 < w σ → G.IsClique ((fam σ) : Set V) := by
      rintro ⟨σ, hσ⟩ _
      simp only [auts, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      intro x hx y hy hxy
      simp only [fam, Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe] at hx hy
      rcases hx with ⟨a, ha, rfl⟩
      rcases hy with ⟨b, hb, rfl⟩
      exact (hσ a b).mpr (hK_clq ha hb fun hab => hxy (congrArg σ hab))
    have hcover : ∀ v : V, 1 ≤ ∑ σ : auts, if v ∈ fam σ then w σ else 0 := by
      intro v
      have hind_eq : ∀ σ : Equiv.Perm V,
          (if v ∈ K.map σ.toEmbedding then (1 : ℝ) else 0) =
            ∑ u ∈ K, if σ u = v then (1 : ℝ) else 0 := by
        intro σ
        by_cases hv : v ∈ K.map σ.toEmbedding
        · rw [if_pos hv]
          simp only [Finset.mem_map, Equiv.coe_toEmbedding] at hv
          rcases hv with ⟨u₀, hu₀, hσu₀⟩
          symm
          rw [Finset.sum_eq_single u₀]
          · simp [hσu₀]
          · intro u _ hu_ne
            have hne : σ u ≠ v := fun h => hu_ne (σ.injective (h.trans hσu₀.symm))
            simp [hne]
          · intro hu0_mem
            exact absurd hu₀ hu0_mem
        · rw [if_neg hv]
          symm
          refine Finset.sum_eq_zero fun u hu => ?_
          have hne : σ u ≠ v := fun h => hv (Finset.mem_map.mpr ⟨u, hu, h⟩)
          simp [hne]
      have hcount_sum :
          (∑ σ ∈ auts, if v ∈ K.map σ.toEmbedding then (1 : ℝ) else 0) =
            ∑ u ∈ K, ((auts.filter fun σ : Equiv.Perm V => σ u = v).card : ℝ) := by
        calc (∑ σ ∈ auts, if v ∈ K.map σ.toEmbedding then (1 : ℝ) else 0)
            = ∑ σ ∈ auts, ∑ u ∈ K, if σ u = v then (1 : ℝ) else 0 :=
                Finset.sum_congr rfl fun σ _ => hind_eq σ
          _ = ∑ u ∈ K, ∑ σ ∈ auts, if σ u = v then (1 : ℝ) else 0 := Finset.sum_comm
          _ = ∑ u ∈ K, ((auts.filter fun σ : Equiv.Perm V => σ u = v).card : ℝ) := by
                refine Finset.sum_congr rfl fun u _ => ?_
                rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hscaled :
          (Fintype.card V : ℝ) * (∑ σ ∈ auts, if v ∈ K.map σ.toEmbedding then (1 : ℝ) else 0) =
            denom := by
        rw [hcount_sum, Finset.mul_sum]
        calc ∑ u ∈ K, (Fintype.card V : ℝ) * ((auts.filter fun σ : Equiv.Perm V => σ u = v).card : ℝ)
            = ∑ _u ∈ K, (auts.card : ℝ) := by
                refine Finset.sum_congr rfl fun u _ => ?_
                exact_mod_cast hfiber_const u v
          _ = (K.card : ℝ) * (auts.card : ℝ) := by simp
          _ = denom := by rw [hK_card]; ring
      have hcov_eq :
          (∑ σ : auts, if v ∈ fam σ then w σ else 0) =
            ((Fintype.card V : ℝ) *
              (∑ σ ∈ auts, if v ∈ K.map σ.toEmbedding then (1 : ℝ) else 0)) / denom := by
        have h1 :
            (∑ σ : auts, if v ∈ fam σ then w σ else 0) =
              ∑ σ ∈ auts, if v ∈ K.map σ.toEmbedding then (Fintype.card V : ℝ) / denom else 0 := by
          exact Finset.sum_coe_sort auts
            (fun σ => if v ∈ K.map σ.toEmbedding then (Fintype.card V : ℝ) / denom else 0)
        rw [h1, Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun σ _ => ?_
        split_ifs <;> ring
      rw [hcov_eq, hscaled, div_self hdenom_pos.ne']
    let cov := FracCliqueCover.ofFamily G fam w hw_nonneg hfam_clq hcover
    have hcov_tot : cov.total = (Fintype.card V : ℝ) / (G.cliqueNum : ℝ) := by
      unfold cov
      rw [FracCliqueCover.ofFamily_total]
      simp only [w, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, denom]
      field_simp [hauts_pos.ne', hclq_pos_real.ne']
    exact (fracCliqueCoverNum_le_of_cover cov).trans_eq hcov_tot
  · let y : FracIndepSet G :=
      { weight := fun _ => (G.cliqueNum : ℝ)⁻¹
        nonneg := fun _ => inv_nonneg.mpr hclq_pos_real.le
        clique_le_one := fun C hC => by
          have hcard : (C.card : ℝ) ≤ (G.cliqueNum : ℝ) := by
            exact_mod_cast hC.card_le_cliqueNum
          rw [Finset.sum_const, nsmul_eq_mul]
          calc (C.card : ℝ) * (G.cliqueNum : ℝ)⁻¹
              ≤ (G.cliqueNum : ℝ) * (G.cliqueNum : ℝ)⁻¹ :=
                mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hclq_pos_real.le)
            _ = 1 := mul_inv_cancel₀ hclq_pos_real.ne' }
    have hy_tot : y.total = (Fintype.card V : ℝ) / (G.cliqueNum : ℝ) := by
      simp [FracIndepSet.total, y, div_eq_mul_inv]
    have hy_le : y.total ≤ fracIndepNum G :=
      le_csSup (fracIndepSet_set_bddAbove G) ⟨y, rfl⟩
    rw [hy_tot] at hy_le
    exact hy_le.trans (fracIndepNum_le_fracCliqueCoverNum G)

theorem shannonCapacity_mul_cliqueNum_le_card_of_vertexTransitive
    {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    (hG : IsVertexTransitive G) :
    shannonCapacity G * (G.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hle := (shannonCapacity_le_fracCliqueCoverNum G).trans_eq
    (fracCliqueCoverNum_eq_card_div_cliqueNum_of_vertexTransitive hG)
  have hclq_pos : (0 : ℝ) < (G.cliqueNum : ℝ) := by
    obtain ⟨v₀⟩ := ‹Nonempty V›
    have h1 : G.IsClique (({v₀} : Finset V) : Set V) := by simp
    have hle1 := h1.card_le_cliqueNum
    simp only [Finset.card_singleton] at hle1
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  exact (le_div_iff₀ hclq_pos).mp hle

theorem oddCycle_cliqueNum {k : ℕ} (hk : 2 ≤ k) :
    (SimpleGraph.cycleGraph (2 * k + 1)).cliqueNum = 2 := by
  let n : ℕ := 2 * k + 1
  have hn : 5 ≤ n := by omega
  apply le_antisymm
  · rw [SimpleGraph.cliqueNum]
    refine csSup_le ⟨0, by simp⟩ ?_
    rintro m ⟨C, hC⟩
    by_contra hlt
    have hm3 : 3 ≤ m := by omega
    have hcard : 3 ≤ C.card := by rw [hC.card_eq]; exact hm3
    obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hcard
    rw [Finset.card_eq_three] at ht_card
    rcases ht_card with ⟨a, b, c, hab, hac, hbc, rfl⟩
    have ha : a ∈ C := ht_sub (by simp)
    have hb : b ∈ C := ht_sub (by simp)
    have hc : c ∈ C := ht_sub (by simp)
    have hab_adj := hC.isClique ha hb hab
    have hac_adj := hC.isClique ha hc hac
    have hbc_adj := hC.isClique hb hc hbc
    rw [SimpleGraph.cycleGraph_adj'] at hab_adj hac_adj hbc_adj
    have hstep : ∀ x y : Fin n, (x - y).val = 1 ∨ (y - x).val = 1 →
        (y.val = x.val + 1 ∨ (x.val = n - 1 ∧ y.val = 0)) ∨
          (x.val = y.val + 1 ∨ (y.val = n - 1 ∧ x.val = 0)) := by
      intro x y h
      have hx : x.val < n := x.isLt
      have hy : y.val < n := y.isLt
      rcases h with h | h
      · right
        by_cases hle : y ≤ x
        · have hsub : (x - y).val = x.val - y.val := Fin.coe_sub_iff_le.mpr hle
          exact Or.inl (by omega)
        · have hlt : x < y := lt_of_not_ge hle
          have hsub : (x - y).val = n + x.val - y.val := Fin.coe_sub_iff_lt.mpr hlt
          exact Or.inr ⟨by omega, by omega⟩
      · left
        by_cases hle : x ≤ y
        · have hsub : (y - x).val = y.val - x.val := Fin.coe_sub_iff_le.mpr hle
          exact Or.inl (by omega)
        · have hlt : y < x := lt_of_not_ge hle
          have hsub : (y - x).val = n + y.val - x.val := Fin.coe_sub_iff_lt.mpr hlt
          exact Or.inr ⟨by omega, by omega⟩
    have h1 := hstep a b hab_adj
    have h2 := hstep a c hac_adj
    have h3 := hstep b c hbc_adj
    have ha_lt : a.val < n := a.isLt
    have hb_lt : b.val < n := b.isLt
    have hc_lt : c.val < n := c.isLt
    have hab_val : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have hac_val : a.val ≠ c.val := fun h => hac (Fin.ext h)
    have hbc_val : b.val ≠ c.val := fun h => hbc (Fin.ext h)
    rcases h1 with (h1 | ⟨h1a, h1b⟩) | (h1 | ⟨h1a, h1b⟩) <;>
      rcases h2 with (h2 | ⟨h2a, h2b⟩) | (h2 | ⟨h2a, h2b⟩) <;>
      rcases h3 with (h3 | ⟨h3a, h3b⟩) | (h3 | ⟨h3a, h3b⟩) <;> omega
  · have hadj : (SimpleGraph.cycleGraph n).Adj 0 1 := by
      rw [SimpleGraph.cycleGraph_adj']
      right
      rw [sub_zero]
      change 1 % n = 1
      exact Nat.mod_eq_of_lt (by omega)
    have hclq : (SimpleGraph.cycleGraph n).IsClique (({0, 1} : Finset (Fin n)) : Set (Fin n)) := by
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hadj
      · exact hadj.symm
      · exact absurd rfl hxy
    have hcard : ({0, 1} : Finset (Fin n)).card = 2 := by
      rw [Finset.card_pair]
      exact hadj.ne
    calc 2 = ({0, 1} : Finset (Fin n)).card := hcard.symm
      _ ≤ (SimpleGraph.cycleGraph (2 * k + 1)).cliqueNum := hclq.card_le_cliqueNum

theorem oddCycle_fracCliqueCoverNum {k : ℕ} (hk : 2 ≤ k) :
    fracCliqueCoverNum (SimpleGraph.cycleGraph (2 * k + 1)) = (2 * k + 1 : ℝ) / 2 := by
  have hvt := cycleGraph_isVertexTransitive (2 * k + 1)
  haveI : Nonempty (Fin (2 * k + 1)) := ⟨0⟩
  rw [fracCliqueCoverNum_eq_card_div_cliqueNum_of_vertexTransitive hvt,
    oddCycle_cliqueNum hk, Fintype.card_fin]
  push_cast
  ring

theorem c7_fracCliqueCoverNum :
    fracCliqueCoverNum (SimpleGraph.cycleGraph 7) = 7 / 2 := by
  have h := oddCycle_fracCliqueCoverNum (k := 3) (by omega)
  norm_num at h
  exact h

theorem c7_upper_fracCliqueCover :
    shannonCapacity (SimpleGraph.cycleGraph 7) ≤ 7 / 2 :=
  (shannonCapacity_le_fracCliqueCoverNum (SimpleGraph.cycleGraph 7)).trans_eq c7_fracCliqueCoverNum

theorem c7_compl_fracCliqueCoverNum :
    fracCliqueCoverNum (SimpleGraph.cycleGraph 7)ᶜ = 7 / 3 := by
  have hvt : IsVertexTransitive (SimpleGraph.cycleGraph 7)ᶜ :=
    isVertexTransitive_compl (cycleGraph_isVertexTransitive 7)
  have hclq : (SimpleGraph.cycleGraph 7)ᶜ.cliqueNum = 3 := by
    rw [SimpleGraph.cliqueNum_compl]
    have hiso : (SimpleGraph.cycleGraph 7).indepNum =
        (strongPowPi (SimpleGraph.cycleGraph 7) 1).indepNum := by
      let e : SimpleGraph.cycleGraph 7 ≃g strongPowPi (SimpleGraph.cycleGraph 7) 1 :=
        { toEquiv :=
            { toFun := fun v _ => v
              invFun := fun f => f 0
              left_inv := fun _ => rfl
              right_inv := fun f => funext fun i => by rw [Subsingleton.elim i 0] }
          map_rel_iff' := by
            intro a b
            simp only [Equiv.coe_fn_mk, strongPowPi_adj, ne_eq]
            constructor
            · rintro ⟨hne, h⟩
              exact (h 0).resolve_left fun hab => hne (congrArg (fun x _ => x) hab)
            · intro h
              exact ⟨fun hab => h.ne (congr_fun hab 0), fun _ => Or.inr h⟩ }
      exact iso_indepNum_eq e
    rw [hiso, alpha_c7_pow1]
  rw [fracCliqueCoverNum_eq_card_div_cliqueNum_of_vertexTransitive hvt, hclq, Fintype.card_fin]
  norm_num

theorem c7_compl_upper_fracCliqueCover :
    shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ≤ 7 / 3 :=
  (shannonCapacity_le_fracCliqueCoverNum (SimpleGraph.cycleGraph 7)ᶜ).trans_eq
    c7_compl_fracCliqueCoverNum

/-! ## Part 2C: Complement Lovász Identity & `ℚ(cos(π/7))` Relations -/

/-- The Lovász theta number of the odd cycle `C_{2k+1}`. -/
noncomputable def lovaszThetaOddCycle (k : ℕ) : ℝ :=
  ((2 * k + 1 : ℝ) * Real.cos (Real.pi / (2 * k + 1 : ℝ))) /
    (1 + Real.cos (Real.pi / (2 * k + 1 : ℝ)))

/-- The Lovász theta number of the odd-cycle complement `C_{2k+1}ᶜ`. -/
noncomputable def lovaszThetaOddCycleCompl (k : ℕ) : ℝ :=
  1 + (Real.cos (Real.pi / (2 * k + 1 : ℝ)))⁻¹

/-- The Lovász theta number of `C₇ᶜ`: `1 + sec(π / 7)`. -/
noncomputable def lovaszThetaC7Compl : ℝ :=
  1 + (Real.cos (Real.pi / 7))⁻¹

private lemma cos_pi_div_odd_pos' (k : ℕ) (hk : 1 ≤ k) :
    0 < Real.cos (Real.pi / (2 * k + 1 : ℝ)) := by
  have hn3 : (3 : ℝ) ≤ (2 * k + 1 : ℝ) := by exact_mod_cast (by omega : 3 ≤ 2 * k + 1)
  have hpi : 0 < Real.pi := Real.pi_pos
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have : 0 < Real.pi / (2 * k + 1 : ℝ) := div_pos hpi (by linarith)
    linarith
  · rw [div_lt_div_iff₀ (by linarith) two_pos]
    nlinarith

theorem lovaszThetaOddCycle_mul_compl (k : ℕ) (hk : 1 ≤ k) :
    lovaszThetaOddCycle k * lovaszThetaOddCycleCompl k = (2 * k + 1 : ℝ) := by
  have hc : 0 < Real.cos (Real.pi / (2 * k + 1 : ℝ)) := cos_pi_div_odd_pos' k hk
  have h1c : 1 + Real.cos (Real.pi / (2 * k + 1 : ℝ)) ≠ 0 := by linarith
  unfold lovaszThetaOddCycle lovaszThetaOddCycleCompl
  field_simp [hc.ne', h1c]
  ring

theorem lovaszThetaC7_mul_compl : lovaszThetaC7 * lovaszThetaC7Compl = 7 := by
  have h := lovaszThetaOddCycle_mul_compl 3 (by norm_num)
  unfold lovaszThetaOddCycle lovaszThetaOddCycleCompl at h
  unfold lovaszThetaC7 lovaszThetaC7Compl
  norm_num at h ⊢
  exact h

theorem oddCycle_shannonCapacity_mul_compl_le (k : ℕ) (hk : 1 ≤ k) :
    shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1)) *
      shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1))ᶜ ≤ (2 * k + 1 : ℝ) := by
  have h1 := oddCycle_upper_lovasz k hk
  have h2 := oddCycle_compl_upper_lovasz k hk
  have hnn1 : 0 ≤ shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1)) := shannonCapacity_nonneg _
  have hnn2 : 0 ≤ shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1))ᶜ := shannonCapacity_nonneg _
  have hmul : shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1)) *
      shannonCapacity (SimpleGraph.cycleGraph (2 * k + 1))ᶜ ≤
      lovaszThetaOddCycle k * lovaszThetaOddCycleCompl k :=
    mul_le_mul h1 h2 hnn2 (hnn1.trans h1)
  exact hmul.trans_eq (lovaszThetaOddCycle_mul_compl k hk)

theorem c7_shannonCapacity_mul_compl_le :
    shannonCapacity (SimpleGraph.cycleGraph 7) *
      shannonCapacity (SimpleGraph.cycleGraph 7)ᶜ ≤ 7 := by
  have h := oddCycle_shannonCapacity_mul_compl_le 3 (by norm_num)
  norm_num at h
  exact h

theorem cos_pi_div_seven_inv_eq_poly :
    (Real.cos (Real.pi / 7))⁻¹ =
      -8 * (Real.cos (Real.pi / 7)) ^ 2 + 4 * Real.cos (Real.pi / 7) + 4 := by
  have hc_pos : 0 < Real.cos (Real.pi / 7) := by
    have h := cos_pi_div_odd_pos' 3 (by norm_num)
    norm_num at h
    exact h
  field_simp [hc_pos.ne']
  linear_combination cos_pi_div_seven_cubic

theorem lovaszThetaC7_eq_poly_cos :
    lovaszThetaC7 = -8 * (Real.cos (Real.pi / 7)) ^ 2 + 12 * Real.cos (Real.pi / 7) - 1 := by
  have hc_pos : 0 < Real.cos (Real.pi / 7) := by
    have h := cos_pi_div_odd_pos' 3 (by norm_num)
    norm_num at h
    exact h
  have h1c : 1 + Real.cos (Real.pi / 7) ≠ 0 := by linarith
  unfold lovaszThetaC7
  field_simp [h1c]
  linear_combination cos_pi_div_seven_cubic

theorem lovaszThetaC7Compl_eq_poly_cos :
    lovaszThetaC7Compl = -8 * (Real.cos (Real.pi / 7)) ^ 2 + 4 * Real.cos (Real.pi / 7) + 5 := by
  unfold lovaszThetaC7Compl
  rw [cos_pi_div_seven_inv_eq_poly]
  ring

theorem lovaszThetaC7_sub_compl :
    lovaszThetaC7 - lovaszThetaC7Compl = 8 * Real.cos (Real.pi / 7) - 6 := by
  rw [lovaszThetaC7_eq_poly_cos, lovaszThetaC7Compl_eq_poly_cos]
  ring

theorem lovaszThetaC7Compl_cubic :
    lovaszThetaC7Compl ^ 3 - 7 * lovaszThetaC7Compl ^ 2 + 7 * lovaszThetaC7Compl + 7 = 0 := by
  have hpos : 0 < lovaszThetaC7 := lt_trans (by norm_num) lovaszThetaC7_gt_three
  have hmul : lovaszThetaC7Compl = 7 / lovaszThetaC7 :=
    eq_div_of_mul_eq hpos.ne' (by rw [mul_comm]; exact lovaszThetaC7_mul_compl)
  rw [hmul]
  field_simp [hpos.ne']
  linear_combination 7 * lovaszThetaC7_cubic

theorem cos_pi_div_seven_eq_div_lovaszThetaC7 :
    Real.cos (Real.pi / 7) = lovaszThetaC7 / (7 - lovaszThetaC7) := by
  have hc_pos : 0 < Real.cos (Real.pi / 7) := by
    have h := cos_pi_div_odd_pos' 3 (by norm_num)
    norm_num at h
    exact h
  have h1c : 1 + Real.cos (Real.pi / 7) ≠ 0 := by linarith
  have hne7 : 7 - lovaszThetaC7 ≠ 0 := by
    have hlt7 : lovaszThetaC7 < 7 := lt_trans lovaszThetaC7_lt_rational (by norm_num)
    linarith
  unfold lovaszThetaC7
  field_simp [h1c, hne7]
  ring

theorem cos_pi_div_seven_eq_inv_lovaszThetaC7Compl :
    Real.cos (Real.pi / 7) = (lovaszThetaC7Compl - 1)⁻¹ := by
  unfold lovaszThetaC7Compl
  simp [inv_inv]

/-! ## Part 2D: Torus-Packing, `L_∞ ≥ 2`, Cohomomorphism & Blowup/Rosenfeld Equivalences -/

/-- The `2^d`-element unit-plus-one torus box anchored at `u : Fin d → ZMod n`. -/
def torusBox (n d : ℕ) [NeZero n] (u : Fin d → ZMod n) : Finset (Fin d → ZMod n) :=
  Fintype.piFinset fun i : Fin d => ({u i, u i + 1} : Finset (ZMod n))

theorem card_torusBox (n d : ℕ) (hn : 2 ≤ n) (u : Fin d → ZMod n) :
    letI : NeZero n := ⟨by omega⟩
    (torusBox n d u).card = 2 ^ d := by
  letI : NeZero n := ⟨by omega⟩
  unfold torusBox
  rw [Fintype.card_piFinset]
  have hcard : ∀ i : Fin d, ({u i, u i + 1} : Finset (ZMod n)).card = 2 := by
    intro i
    rw [Finset.card_pair]
    intro heq
    have h1 : (1 : ZMod n) = 0 := by
      have : u i + 1 - u i = u i - u i := congrArg (fun z => z - u i) heq.symm
      simpa using this
    haveI : Fact (1 < n) := ⟨by omega⟩
    have hval : ((1 : ZMod n)).val = 0 := by rw [h1, ZMod.val_zero]
    rw [ZMod.val_one] at hval
    omega
  simp [hcard]

theorem c7Pow_isIndepSet_iff_pairwiseDisjoint_boxes {d : ℕ} (S : Finset (Fin d → ZMod 7)) :
    (strongPowPi C7 d).IsIndepSet (S : Set (Fin d → ZMod 7)) ↔
      (S : Set (Fin d → ZMod 7)).PairwiseDisjoint (torusBox 7 d) := by
  have hbox_inter : ∀ u v : Fin d → ZMod 7,
      (¬ Disjoint (torusBox 7 d u) (torusBox 7 d v)) ↔
        ∀ i : Fin d, u i = v i ∨ C7.Adj (u i) (v i) := by
    intro u v
    rw [Finset.not_disjoint_iff]
    constructor
    · rintro ⟨w, hwu, hwv⟩ i
      simp only [torusBox, Fintype.mem_piFinset, Finset.mem_insert, Finset.mem_singleton] at hwu hwv
      rcases hwu i with hwi | hwi <;> rcases hwv i with hwj | hwj
      · exact Or.inl (hwi.symm.trans hwj)
      · right
        rw [hwi] at hwj
        rw [hwj]
        exact (c7_adj_add_one (v i)).symm
      · right
        rw [hwj] at hwi
        rw [hwi]
        exact c7_adj_add_one (u i)
      · exact Or.inl (by
          have : u i + 1 = v i + 1 := hwi.symm.trans hwj
          exact add_right_cancel this)
    · intro h
      have hex : ∀ i : Fin d, ∃ z : ZMod 7, z ∈ ({u i, u i + 1} : Finset (ZMod 7)) ∧
          z ∈ ({v i, v i + 1} : Finset (ZMod 7)) := by
        intro i
        rcases h i with heq | hadj
        · exact ⟨u i, by simp, by simp [heq]⟩
        · rw [c7_adj] at hadj
          rcases hadj with h1 | h2
          · refine ⟨u i, by simp, ?_⟩
            have : u i = v i + 1 := by
              rw [add_comm]
              exact sub_eq_iff_eq_add.mp h1
            simp [this]
          · refine ⟨v i, ?_, by simp⟩
            have : v i = u i + 1 := by
              rw [add_comm]
              exact sub_eq_iff_eq_add.mp h2
            simp [this]
      choose w hw1 hw2 using hex
      refine ⟨w, ?_, ?_⟩ <;> simp only [torusBox, Fintype.mem_piFinset] <;> [exact hw1; exact hw2]
  constructor
  · intro hind u hu v hv huv
    rw [Function.onFun]
    by_contra hnot
    have hadj := (hbox_inter u v).mp hnot
    exact hind hu hv huv ⟨huv, hadj⟩
  · intro hdisj u hu v hv huv hadj
    have hnot : ¬ Disjoint (torusBox 7 d u) (torusBox 7 d v) :=
      (hbox_inter u v).mpr hadj.2
    exact hnot (hdisj hu hv huv)

theorem c7Pow_volume_bound (d : ℕ) :
    2 ^ d * (strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum ≤ 7 ^ d := by
  have heq : (strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum = (strongPowPi C7 d).indepNum := by
    rw [← strongPow_indepNum_eq_pi, ← strongPow_indepNum_eq_pi,
      iso_indepNum_eq (strongPowCongr c7IsoCycleGraph d)]
  rw [heq]
  obtain ⟨S, hS_indep, hS_card⟩ := (strongPowPi C7 d).exists_isNIndepSet_indepNum
  rw [← hS_card]
  have hdisj := (c7Pow_isIndepSet_iff_pairwiseDisjoint_boxes S).mp hS_indep
  have hsum : (S.biUnion (torusBox 7 d)).card = ∑ u ∈ S, (torusBox 7 d u).card :=
    Finset.card_biUnion (fun u hu v hv huv => hdisj hu hv huv)
  have hbox_card : ∀ u ∈ S, (torusBox 7 d u).card = 2 ^ d := fun u _ =>
    card_torusBox 7 d (by norm_num) u
  have hle_univ : (S.biUnion (torusBox 7 d)).card ≤ Fintype.card (Fin d → ZMod 7) :=
    Finset.card_le_univ _
  rw [hsum, Finset.sum_congr rfl hbox_card, Finset.sum_const, nsmul_eq_mul,
    Fintype.card_fun, Fintype.card_fin, ZMod.card] at hle_univ
  linarith

/-- Cyclic `L₁`-distance on `ZMod n`: `min ((a - b).val) ((b - a).val)`. -/
def cyclicDist (n : ℕ) (a b : ZMod n) : ℕ :=
  min (a - b).val (b - a).val

theorem c7Pow_isIndepSet_iff_linf_ge_two {d : ℕ} (S : Finset (Fin d → ZMod 7)) :
    (strongPowPi C7 d).IsIndepSet (S : Set (Fin d → ZMod 7)) ↔
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∃ i : Fin d, 2 ≤ cyclicDist 7 (u i) (v i) := by
  have hdist : ∀ a b : ZMod 7, cyclicDist 7 a b ≤ 1 ↔ a = b ∨ C7.Adj a b := by
    intro a b
    revert a b
    decide
  constructor
  · intro hind u hu v hv huv
    by_contra hnot
    push Not at hnot
    have hadj : ∀ i : Fin d, u i = v i ∨ C7.Adj (u i) (v i) := fun i =>
      (hdist (u i) (v i)).mp (Nat.lt_succ_iff.mp (hnot i))
    exact hind hu hv huv ⟨huv, hadj⟩
  · intro hlinf u hu v hv huv hadj
    obtain ⟨i, hi⟩ := hlinf u hu v hv huv
    have hle1 : cyclicDist 7 (u i) (v i) ≤ 1 := (hdist (u i) (v i)).mpr (hadj.2 i)
    omega

theorem shannonCapacity_mono_cohom {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : Gᶜ →g Hᶜ) :
    shannonCapacity G ≤ shannonCapacity H := by
  classical
  refine shannonCapacity_le G (shannonCapacity_nonneg H) fun d hd => ?_
  rw [strongPow_indepNum_eq_pi]
  obtain ⟨S, hS_indep, hS_card⟩ := (strongPowPi G d).exists_isNIndepSet_indepNum
  let g : (Fin d → V) → (Fin d → W) := fun x i => f (x i)
  have hg_inj : Set.InjOn g (S : Set (Fin d → V)) := by
    intro x hx y hy hxy
    by_contra hne
    have hnot : ¬ (strongPowPi G d).Adj x y := fun hadj => hS_indep hx hy hne hadj
    rw [strongPowPi_adj] at hnot
    push Not at hnot
    obtain ⟨i, hi_ne, hi_nadj⟩ := hnot hne
    have hfne : f (x i) ≠ f (y i) := by
      have hGcompl : Gᶜ.Adj (x i) (y i) := ⟨hi_ne, hi_nadj⟩
      exact (f.map_rel hGcompl).1
    exact hfne (congr_fun hxy i)
  have hg_indep : (strongPowPi H d).IsIndepSet ((S.image g : Finset (Fin d → W)) : Set (Fin d → W)) := by
    intro a ha b hb hab hHadjs
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    rcases ha with ⟨x, hx, rfl⟩
    rcases hb with ⟨y, hy, rfl⟩
    have hxy_ne : x ≠ y := fun h => hab (congrArg g h)
    have hnot : ¬ (strongPowPi G d).Adj x y := fun hadj => hS_indep hx hy hxy_ne hadj
    rw [strongPowPi_adj] at hnot
    obtain ⟨i, hi_ne, hi_nadj⟩ := by push Not at hnot; exact hnot hxy_ne
    have hHcompl : Hᶜ.Adj (f (x i)) (f (y i)) := f.map_rel ⟨hi_ne, hi_nadj⟩
    rcases hHadjs.2 i with heq | hadj
    · exact hHcompl.1 heq
    · exact hHcompl.2 hadj
  have hcard : S.card ≤ (strongPowPi H d).indepNum := by
    calc S.card = (S.image g).card := (Finset.card_image_of_injOn hg_inj).symm
      _ ≤ (strongPowPi H d).indepNum := hg_indep.card_le_indepNum
  have hle_H : ((strongPowPi H d).indepNum : ℝ) ≤ (shannonCapacity H) ^ d := by
    rw [← strongPow_indepNum_eq_pi]
    have hmem : ((strongPow H d).indepNum : ℝ) ^ (1 / (d : ℝ)) ∈ shannonSet H := ⟨d, hd, rfl⟩
    have hsup : ((strongPow H d).indepNum : ℝ) ^ (1 / (d : ℝ)) ≤ shannonCapacity H :=
      le_csSup (shannonSet_bddAbove H) hmem
    rw [one_div, Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) (shannonCapacity_nonneg H)
      (Nat.cast_pos.mpr hd), Real.rpow_natCast] at hsup
    exact hsup
  rw [← hS_card]
  exact (Nat.cast_le.mpr hcard).trans hle_H

private def strongPowProdEquiv {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    (d : ℕ) → strongPow (G ⊠ H) d ≃g strongPow G d ⊠ strongPow H d
  | 0 =>
    { toEquiv :=
        { toFun := fun _ => (PUnit.unit, PUnit.unit)
          invFun := fun _ => PUnit.unit
          left_inv := fun _ => rfl
          right_inv := fun ⟨_, _⟩ => rfl }
      map_rel_iff' := by simp [strongPow] }
  | d + 1 =>
    (strongProdCongr (.refl) (strongPowProdEquiv G H d)).trans
      ((strongProdAssoc G H (strongPow G d ⊠ strongPow H d)).trans
        ((strongProdCongr (.refl) ((strongProdAssoc H (strongPow G d) (strongPow H d)).symm.trans
          ((strongProdCongr (strongProdComm H (strongPow G d)) (.refl)).trans
            (strongProdAssoc (strongPow G d) H (strongPow H d))))).trans
          (strongProdAssoc G (strongPow G d) (H ⊠ strongPow H d)).symm))

theorem shannonCapacity_mul_le {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    shannonCapacity G * shannonCapacity H ≤ shannonCapacity (G ⊠ H) := by
  by_cases hV : IsEmpty V
  · have hG0 : shannonCapacity G = 0 := by
      apply le_antisymm _ (shannonCapacity_nonneg G)
      refine shannonCapacity_le G le_rfl fun d hd => ?_
      have h0 : (strongPow G d).indepNum ≤ 0 := by
        simpa [Fintype.card_eq_zero, zero_pow hd.ne'] using strongPow_indepNum_le_card_pow G d
      rw [Nat.eq_zero_of_le_zero h0, Nat.cast_zero, zero_pow hd.ne']
    rw [hG0, zero_mul]
    exact shannonCapacity_nonneg _
  · by_cases hW : IsEmpty W
    · have hH0 : shannonCapacity H = 0 := by
        apply le_antisymm _ (shannonCapacity_nonneg H)
        refine shannonCapacity_le H le_rfl fun d hd => ?_
        have h0 : (strongPow H d).indepNum ≤ 0 := by
          simpa [Fintype.card_eq_zero, zero_pow hd.ne'] using strongPow_indepNum_le_card_pow H d
        rw [Nat.eq_zero_of_le_zero h0, Nat.cast_zero, zero_pow hd.ne']
      rw [hH0, mul_zero]
      exact shannonCapacity_nonneg _
    · rw [not_isEmpty_iff] at hV hW
      have hG_tend := shannonCapacity_tendsto G
      have hH_tend := shannonCapacity_tendsto H
      have hGH_tend := shannonCapacity_tendsto (G ⊠ H)
      have hprod_tend := hG_tend.mul hH_tend
      refine le_of_tendsto_of_tendsto hprod_tend hGH_tend ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with d _
      have hmul_nat : (strongPowPi G d).indepNum * (strongPowPi H d).indepNum ≤
          (strongPowPi (G ⊠ H) d).indepNum := by
        simp_rw [← strongPow_indepNum_eq_pi]
        rw [iso_indepNum_eq (strongPowProdEquiv G H d)]
        exact indepNum_mul_le (strongPow G d) (strongPow H d)
      have hmul_real : ((strongPowPi G d).indepNum : ℝ) * ((strongPowPi H d).indepNum : ℝ) ≤
          ((strongPowPi (G ⊠ H) d).indepNum : ℝ) := by
        exact_mod_cast hmul_nat
      rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hmul_real
        (by positivity)

theorem card_le_prod_compl_indepNum {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Fintype.card V ≤ (G ⊠ Gᶜ).indepNum := by
  classical
  let diag : Finset (V × V) := Finset.univ.image fun v : V => (v, v)
  have hdiag_indep : (G ⊠ Gᶜ).IsIndepSet (diag : Set (V × V)) := by
    intro x hx y hy hxy hadj
    simp only [diag, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
    rcases hx with ⟨u, rfl⟩
    rcases hy with ⟨v, rfl⟩
    have huv : u ≠ v := fun h => hxy (by subst h; rfl)
    rcases hadj.2 with ⟨h1, h2⟩
    rcases h1 with rfl | hG
    · exact huv rfl
    · rcases h2 with rfl | hGc
      · exact huv rfl
      · exact hGc.2 hG
  have hcard : diag.card = Fintype.card V := by
    rw [Finset.card_image_of_injective _ (fun u v h => congrArg Prod.fst h), Finset.card_univ]
  exact hcard ▸ hdiag_indep.card_le_indepNum

theorem c7_prod_compl_shannonCapacity_ge_seven :
    (7 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7 ⊠ (SimpleGraph.cycleGraph 7)ᶜ) := by
  have h1 : (7 : ℝ) ≤ ((SimpleGraph.cycleGraph 7 ⊠ (SimpleGraph.cycleGraph 7)ᶜ).indepNum : ℝ) := by
    exact_mod_cast (card_le_prod_compl_indepNum (SimpleGraph.cycleGraph 7)).trans_eq'
      (by simp : Fintype.card (Fin 7) = 7)
  have h2 : ((SimpleGraph.cycleGraph 7 ⊠ (SimpleGraph.cycleGraph 7)ᶜ).indepNum : ℝ) ≤
      shannonCapacity (SimpleGraph.cycleGraph 7 ⊠ (SimpleGraph.cycleGraph 7)ᶜ) := by
    have hiso : (SimpleGraph.cycleGraph 7 ⊠ (SimpleGraph.cycleGraph 7)ᶜ) ≃g
        strongPow (SimpleGraph.cycleGraph 7 ⊠ (SimpleGraph.cycleGraph 7)ᶜ) 1 :=
      strongProdPUnitRight _
    have hmem : ((strongPow (SimpleGraph.cycleGraph 7 ⊠ (SimpleGraph.cycleGraph 7)ᶜ) 1).indepNum : ℝ) ^
        (1 / ((1 : ℕ) : ℝ)) ∈ shannonSet (SimpleGraph.cycleGraph 7 ⊠ (SimpleGraph.cycleGraph 7)ᶜ) :=
      ⟨1, Nat.one_pos, rfl⟩
    have hsup : ((strongPow (SimpleGraph.cycleGraph 7 ⊠ (SimpleGraph.cycleGraph 7)ᶜ) 1).indepNum : ℝ) ^
        (1 / ((1 : ℕ) : ℝ)) ≤
        shannonCapacity (SimpleGraph.cycleGraph 7 ⊠ (SimpleGraph.cycleGraph 7)ᶜ) :=
      le_csSup (shannonSet_bddAbove _) hmem
    simpa [← iso_indepNum_eq hiso] using hsup
  exact h1.trans h2

theorem shannonCapacity_cliqueBlowup {V W : Type*} [Fintype V] [Fintype W] [Nonempty W]
    (G : SimpleGraph V) :
    shannonCapacity (G ⊠ (⊤ : SimpleGraph W)) = shannonCapacity G := by
  obtain ⟨w₀⟩ := ‹Nonempty W›
  let f : (G ⊠ (⊤ : SimpleGraph W))ᶜ →g Gᶜ :=
    { toFun := Prod.fst
      map_rel' := by
        rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ ⟨hne, hnadj⟩
        by_cases hu : u₁ = u₂
        · exfalso
          apply hnadj
          refine ⟨hne, Or.inl hu, ?_⟩
          by_cases hv : v₁ = v₂
          · exact absurd (Prod.ext hu hv) hne
          · exact Or.inr hv
        · refine ⟨hu, fun hG => hnadj ⟨hne, Or.inr hG, ?_⟩⟩
          by_cases hv : v₁ = v₂
          · exact Or.inl hv
          · exact Or.inr hv }
  let g : Gᶜ →g (G ⊠ (⊤ : SimpleGraph W))ᶜ :=
    { toFun := fun u => (u, w₀)
      map_rel' := by
        intro u₁ u₂ ⟨hne, hnadj⟩
        refine ⟨fun h => hne (congrArg Prod.fst h), ?_⟩
        intro hadj
        rcases hadj.2.1 with rfl | hG
        · exact hne rfl
        · exact hnadj hG }
  exact le_antisymm (shannonCapacity_mono_cohom f) (shannonCapacity_mono_cohom g)

theorem shannonCapacity_disjointBlowup {V : Type*} [Fintype V] (G : SimpleGraph V) (m : ℕ) :
    shannonCapacity (G ⊠ (⊥ : SimpleGraph (Fin m))) = (m : ℝ) * shannonCapacity G := by
  rcases m with _ | m
  · have hiso : (G ⊠ (⊥ : SimpleGraph (Fin 0))) ≃g (⊥ : SimpleGraph Empty) :=
      { toEquiv :=
          { toFun := fun p => Fin.elim0 p.2
            invFun := fun x => Empty.elim x
            left_inv := fun p => Fin.elim0 p.2
            right_inv := fun x => Empty.elim x }
        map_rel_iff' := by intro a _; exact Fin.elim0 a.2 }
    have h0 : shannonCapacity (⊥ : SimpleGraph Empty) = 0 := by
      apply le_antisymm _ (shannonCapacity_nonneg _)
      refine shannonCapacity_le _ le_rfl fun d hd => ?_
      have hc : (strongPow (⊥ : SimpleGraph Empty) d).indepNum ≤ 0 := by
        simpa [Fintype.card_empty, zero_pow hd.ne'] using
          strongPow_indepNum_le_card_pow (⊥ : SimpleGraph Empty) d
      have hz : (strongPow (⊥ : SimpleGraph Empty) d).indepNum = 0 := Nat.eq_zero_of_le_zero hc
      rw [hz, Nat.cast_zero, zero_pow hd.ne']
    rw [shannonCapacity_congr hiso, h0, Nat.cast_zero, zero_mul]
  · by_cases hV : IsEmpty V
    · have hG0 : shannonCapacity G = 0 := by
        apply le_antisymm _ (shannonCapacity_nonneg G)
        refine shannonCapacity_le G le_rfl fun d hd => ?_
        have hc : (strongPow G d).indepNum ≤ 0 := by
          simpa [Fintype.card_eq_zero, zero_pow hd.ne'] using strongPow_indepNum_le_card_pow G d
        have hz : (strongPow G d).indepNum = 0 := Nat.eq_zero_of_le_zero hc
        rw [hz, Nat.cast_zero, zero_pow hd.ne']
      have hP0 : shannonCapacity (G ⊠ (⊥ : SimpleGraph (Fin (m + 1)))) = 0 := by
        apply le_antisymm _ (shannonCapacity_nonneg _)
        refine shannonCapacity_le _ le_rfl fun d hd => ?_
        have hc : (strongPow (G ⊠ (⊥ : SimpleGraph (Fin (m + 1)))) d).indepNum ≤ 0 := by
          simpa [Fintype.card_prod, Fintype.card_eq_zero, zero_mul, zero_pow hd.ne'] using
            strongPow_indepNum_le_card_pow (G ⊠ (⊥ : SimpleGraph (Fin (m + 1)))) d
        have hz : (strongPow (G ⊠ (⊥ : SimpleGraph (Fin (m + 1)))) d).indepNum = 0 :=
          Nat.eq_zero_of_le_zero hc
        rw [hz, Nat.cast_zero, zero_pow hd.ne']
      rw [hG0, hP0, mul_zero]
    · rw [not_isEmpty_iff] at hV
      have hbot_indep : (⊥ : SimpleGraph (Fin (m + 1))).indepNum = m + 1 := by
        apply le_antisymm
        · simpa using indepNum_le_card (⊥ : SimpleGraph (Fin (m + 1)))
        · have hind : (⊥ : SimpleGraph (Fin (m + 1))).IsIndepSet
              ((Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))) := by
            intro x _ y _ _ hadj
            exact hadj
          simpa using hind.card_le_indepNum
      have hbot_cap : shannonCapacity (⊥ : SimpleGraph (Fin (m + 1))) = ((m + 1 : ℕ) : ℝ) := by
        apply le_antisymm
        · refine shannonCapacity_le _ (Nat.cast_nonneg _) fun d _ => ?_
          simpa [Fintype.card_fin] using
            (Nat.cast_le (α := ℝ)).mpr (strongPow_indepNum_le_card_pow (⊥ : SimpleGraph (Fin (m + 1))) d)
        · have hiso : (⊥ : SimpleGraph (Fin (m + 1))) ≃g
              strongPow (⊥ : SimpleGraph (Fin (m + 1))) 1 :=
            strongProdPUnitRight _
          have hmem : ((strongPow (⊥ : SimpleGraph (Fin (m + 1))) 1).indepNum : ℝ) ^
              (1 / ((1 : ℕ) : ℝ)) ∈ shannonSet (⊥ : SimpleGraph (Fin (m + 1))) :=
            ⟨1, Nat.one_pos, rfl⟩
          have hsup : ((strongPow (⊥ : SimpleGraph (Fin (m + 1))) 1).indepNum : ℝ) ^
              (1 / ((1 : ℕ) : ℝ)) ≤ shannonCapacity (⊥ : SimpleGraph (Fin (m + 1))) :=
            le_csSup (shannonSet_bddAbove _) hmem
          simpa [← iso_indepNum_eq hiso, hbot_indep] using hsup
      apply le_antisymm
      · refine shannonCapacity_le _ (mul_nonneg (Nat.cast_nonneg _) (shannonCapacity_nonneg G)) fun d hd => ?_
        have hprod_le : ((strongPow G d ⊠ strongPow (⊥ : SimpleGraph (Fin (m + 1))) d).indepNum : ℝ) ≤
            (m + 1 : ℝ) ^ d * ((strongPow G d).indepNum : ℝ) := by
          let baseCov : FracCliqueCover (⊥ : SimpleGraph (Fin (m + 1))) :=
            FracCliqueCover.ofFamily _ (fun i : Fin (m + 1) => ({i} : Finset (Fin (m + 1))))
              (fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp) (fun i => by
                rw [Finset.sum_eq_single i]
                · simp
                · intro j _ hij; simp [Ne.symm hij]
                · intro hm; exact absurd (Finset.mem_univ _) hm)
          let hc := baseCov.pow d
          have hbase_tot : baseCov.total = ((m + 1 : ℕ) : ℝ) := by
            unfold baseCov
            rw [FracCliqueCover.ofFamily_total]
            simp
          have hctot : hc.total = ((m + 1 : ℕ) : ℝ) ^ d := by
            dsimp only [hc]
            rw [FracCliqueCover.pow_total, hbase_tot]
          have h1 := fracCliqueCover_prod_bound (strongPow (⊥ : SimpleGraph (Fin (m + 1))) d) (strongPow G d)
          have h2 : (strongPow G d ⊠ strongPow (⊥ : SimpleGraph (Fin (m + 1))) d).indepNum =
              (strongPow (⊥ : SimpleGraph (Fin (m + 1))) d ⊠ strongPow G d).indepNum :=
            iso_indepNum_eq (strongProdComm _ _)
          rw [h2]
          calc ((strongPow (⊥ : SimpleGraph (Fin (m + 1))) d ⊠ strongPow G d).indepNum : ℝ)
              ≤ fracCliqueCoverNum (strongPow (⊥ : SimpleGraph (Fin (m + 1))) d) *
                  ((strongPow G d).indepNum : ℝ) := h1
            _ ≤ hc.total * ((strongPow G d).indepNum : ℝ) :=
                  mul_le_mul_of_nonneg_right (fracCliqueCoverNum_le_of_cover hc) (Nat.cast_nonneg _)
            _ = (m + 1 : ℝ) ^ d * ((strongPow G d).indepNum : ℝ) := by
                  rw [hctot]; norm_cast
        have hG_le : ((strongPow G d).indepNum : ℝ) ≤ (shannonCapacity G) ^ d := by
          have hmem : ((strongPow G d).indepNum : ℝ) ^ (1 / (d : ℝ)) ∈ shannonSet G := ⟨d, hd, rfl⟩
          have hsup : ((strongPow G d).indepNum : ℝ) ^ (1 / (d : ℝ)) ≤ shannonCapacity G :=
            le_csSup (shannonSet_bddAbove G) hmem
          rwa [one_div, Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) (shannonCapacity_nonneg G)
            (Nat.cast_pos.mpr hd), Real.rpow_natCast] at hsup
        rw [iso_indepNum_eq (strongPowProdEquiv G (⊥ : SimpleGraph (Fin (m + 1))) d)]
        calc ((strongPow G d ⊠ strongPow (⊥ : SimpleGraph (Fin (m + 1))) d).indepNum : ℝ)
            ≤ (m + 1 : ℝ) ^ d * ((strongPow G d).indepNum : ℝ) := hprod_le
          _ ≤ (m + 1 : ℝ) ^ d * (shannonCapacity G) ^ d :=
                mul_le_mul_of_nonneg_left hG_le (by positivity)
          _ = (((m + 1 : ℕ) : ℝ) * shannonCapacity G) ^ d := by
                push_cast; rw [mul_pow]
      · calc (((m + 1 : ℕ) : ℝ) * shannonCapacity G)
            = shannonCapacity G * ((m + 1 : ℕ) : ℝ) := mul_comm _ _
          _ = shannonCapacity G * shannonCapacity (⊥ : SimpleGraph (Fin (m + 1))) := by
                rw [hbot_cap]
          _ ≤ shannonCapacity (G ⊠ (⊥ : SimpleGraph (Fin (m + 1)))) :=
                shannonCapacity_mul_le G _

/-- Lexicographic independent-set blowup `G[E_k]` on `V × Fin k`: vertices `(u, i)` and `(v, j)`
are adjacent iff `G.Adj u v`. -/
def lexIndepBlowup {V : Type*} (G : SimpleGraph V) (k : ℕ) : SimpleGraph (V × Fin k) where
  Adj x y := G.Adj x.1 y.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun x h => G.loopless.irrefl x.1 h⟩

/-- A graph `G` admits an `m`-clique cover. -/
def HasCliqueCover {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ C : Fin m → Finset V, (∀ j, G.IsClique (C j : Set V)) ∧ ∀ v : V, ∃ j, v ∈ C j

theorem lexIndepBlowup_indepNum {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (lexIndepBlowup G k).indepNum = k * G.indepNum := by
  classical
  apply le_antisymm
  · obtain ⟨S, hS_indep, hS_card⟩ := (lexIndepBlowup G k).exists_isNIndepSet_indepNum
    rw [← hS_card]
    let T : Finset V := S.image Prod.fst
    have hT_indep : G.IsIndepSet (T : Set V) := by
      intro u hu v hv huv hadj
      simp only [T, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu hv
      rcases hu with ⟨⟨u', i₁⟩, h1, rfl⟩
      rcases hv with ⟨⟨v', i₂⟩, h2, rfl⟩
      exact hS_indep h1 h2 (fun h => huv (congrArg Prod.fst h)) hadj
    have hsub : S ⊆ T ×ˢ (Finset.univ : Finset (Fin k)) := by
      rintro ⟨u, i⟩ h
      simp only [Finset.mem_product, Finset.mem_univ, and_true, T, Finset.mem_image]
      exact ⟨(u, i), h, rfl⟩
    calc S.card
        ≤ (T ×ˢ (Finset.univ : Finset (Fin k))).card := Finset.card_le_card hsub
      _ = T.card * k := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      _ = k * T.card := mul_comm _ _
      _ ≤ k * G.indepNum := Nat.mul_le_mul_left k hT_indep.card_le_indepNum
  · obtain ⟨T, hT_indep, hT_card⟩ := G.exists_isNIndepSet_indepNum
    let S : Finset (V × Fin k) := T ×ˢ (Finset.univ : Finset (Fin k))
    have hS_indep : (lexIndepBlowup G k).IsIndepSet (S : Set (V × Fin k)) := by
      rintro ⟨u, i₁⟩ h1 ⟨v, i₂⟩ h2 _ hadj
      simp only [S, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ,
        and_true] at h1 h2
      by_cases huv : u = v
      · exact G.loopless.irrefl v (huv ▸ hadj)
      · exact hT_indep h1 h2 huv hadj
    calc k * G.indepNum = T.card * k := by rw [hT_card, mul_comm]
      _ = S.card := by simp [S, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      _ ≤ (lexIndepBlowup G k).indepNum := hS_indep.card_le_indepNum

theorem fracCliqueCoverNum_le_of_lexBlowup_cliqueCover {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k m : ℕ} (hk : 0 < k) (hc : HasCliqueCover (lexIndepBlowup G k) m) :
    fracCliqueCoverNum G ≤ (m : ℝ) / (k : ℝ) := by
  classical
  rcases hc with ⟨C, hC_clq, hC_cov⟩
  let proj : Fin m → Finset V := fun j => (C j).image Prod.fst
  let w : Fin m → ℝ := fun _ => (k : ℝ)⁻¹
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hw_nonneg : ∀ j, 0 ≤ w j := fun _ => inv_nonneg.mpr hk_pos.le
  have hproj_clq : ∀ j, 0 < w j → G.IsClique (proj j : Set V) := by
    intro j _ u hu v hv huv
    simp only [proj, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu hv
    rcases hu with ⟨⟨u', i₁⟩, h1, rfl⟩
    rcases hv with ⟨⟨v', i₂⟩, h2, rfl⟩
    have hne : (u', i₁) ≠ (v', i₂) := fun h => huv (congrArg Prod.fst h)
    exact hC_clq j h1 h2 hne
  have hcover : ∀ v : V, 1 ≤ ∑ j : Fin m, if v ∈ proj j then w j else 0 := by
    intro v
    let J : Finset (Fin m) := Finset.univ.filter fun j => v ∈ proj j
    have hinj : ∀ i : Fin k, ∃ j ∈ J, (v, i) ∈ C j := by
      intro i
      obtain ⟨j, hj⟩ := hC_cov (v, i)
      refine ⟨j, ?_, hj⟩
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, proj, Finset.mem_image]
      exact ⟨(v, i), hj, rfl⟩
    choose φ hφJ hφC using hinj
    have hφ_inj : Function.Injective φ := by
      intro i₁ i₂ heq
      by_contra hne
      have h1 : (v, i₁) ∈ C (φ i₁) := hφC i₁
      have h2 : (v, i₂) ∈ C (φ i₁) := heq ▸ hφC i₂
      have hpair_ne : (v, i₁) ≠ (v, i₂) := fun h => hne (congrArg Prod.snd h)
      exact G.loopless.irrefl v (hC_clq (φ i₁) h1 h2 hpair_ne)
    have hk_le_J : k ≤ J.card := by
      calc k = (Finset.univ : Finset (Fin k)).card := by simp
        _ = ((Finset.univ : Finset (Fin k)).image φ).card :=
              (Finset.card_image_of_injective _ hφ_inj).symm
        _ ≤ J.card := Finset.card_le_card (Finset.image_subset_iff.mpr fun i _ => hφJ i)
    have hsum : (∑ j : Fin m, if v ∈ proj j then w j else 0) = (J.card : ℝ) * (k : ℝ)⁻¹ := by
      rw [← Finset.sum_filter]
      simp [J, w]
    rw [hsum]
    calc (1 : ℝ) = (k : ℝ) * (k : ℝ)⁻¹ := (mul_inv_cancel₀ hk_pos.ne').symm
      _ ≤ (J.card : ℝ) * (k : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk_le_J) (inv_nonneg.mpr hk_pos.le)
  let cov := FracCliqueCover.ofFamily G proj w hw_nonneg hproj_clq hcover
  have hcov_tot : cov.total = (m : ℝ) / (k : ℝ) := by
    unfold cov
    rw [FracCliqueCover.ofFamily_total]
    simp [w, div_eq_mul_inv]
  exact (fracCliqueCoverNum_le_of_cover cov).trans_eq hcov_tot

theorem exists_lexBlowup_cliqueCover_of_fracCliqueCover
    {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) {ε : ℝ} (hε : 0 < ε) :
    ∃ k m : ℕ, 0 < k ∧ HasCliqueCover (lexIndepBlowup G k) m ∧
      (m : ℝ) / (k : ℝ) ≤ fracCliqueCoverNum G + ε := by
  classical
  have hlt : fracCliqueCoverNum G < fracCliqueCoverNum G + ε / 2 := by linarith
  obtain ⟨x, ⟨c, rfl⟩, hc_lt⟩ := exists_lt_of_csInf_lt (fracCliqueCover_set_nonempty G) hlt
  let N : ℕ := Fintype.card (Finset V)
  obtain ⟨k, hk_gt⟩ := exists_nat_gt ((N : ℝ) / (ε / 2))
  have hk_pos : 0 < k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    subst hk0
    have hle : (N : ℝ) / (ε / 2) ≥ 0 := div_nonneg (Nat.cast_nonneg _) (by linarith)
    linarith
  have hk_real : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  have hN_le : (N : ℝ) / (k : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hk_real]
    have hmul := (div_lt_iff₀ (by linarith : 0 < ε / 2)).mp hk_gt
    linarith
  let n : Finset V → ℕ := fun C => Nat.ceil ((k : ℝ) * c.weight C)
  let copies : List (Finset V) := (Finset.univ : Finset (Finset V)).toList.flatMap
    fun C => List.replicate (n C) C
  let m : ℕ := copies.length
  have hn_zero_of_nonpos : ∀ C : Finset V, c.weight C ≤ 0 → n C = 0 := by
    intro C hle
    have h0 : c.weight C = 0 := le_antisymm hle (c.nonneg C)
    simp [n, h0]
  have hn_lt : ∀ C : Finset V, (n C : ℝ) < (k : ℝ) * c.weight C + 1 := by
    intro C
    exact Nat.ceil_lt_add_one (mul_nonneg hk_real.le (c.nonneg C))
  have hm_eq : (m : ℝ) = ∑ C : Finset V, (n C : ℝ) := by
    have hlen : copies.length = ∑ C : Finset V, n C := by
      simp only [copies, List.length_flatMap, List.length_replicate]
      rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList, Multiset.map_coe, Multiset.sum_coe]
    exact_mod_cast hlen
  have hm_bound : (m : ℝ) / (k : ℝ) ≤ fracCliqueCoverNum G + ε := by
    have hm_le : (m : ℝ) ≤ (k : ℝ) * c.total + (N : ℝ) := by
      rw [hm_eq]
      calc ∑ C : Finset V, (n C : ℝ)
          ≤ ∑ C : Finset V, ((k : ℝ) * c.weight C + 1) :=
              Finset.sum_le_sum fun C _ => (hn_lt C).le
        _ = (k : ℝ) * c.total + (N : ℝ) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
              simp [FracCliqueCover.total, N]
    rw [div_le_iff₀ hk_real]
    have hdiv := (div_le_iff₀ hk_real).mp hN_le.le
    nlinarith
  have hcopies_clq : ∀ j : Fin m, G.IsClique ((copies.get j) : Set V) := by
    intro j
    have hmem : copies.get j ∈ copies := List.get_mem copies j
    simp only [copies, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and] at hmem
    rcases hmem with ⟨C, hmemC⟩
    rw [List.mem_replicate] at hmemC
    rcases hmemC with ⟨hne0, hCeq⟩
    rw [hCeq]
    have hpos : 0 < c.weight C := by
      by_contra hle
      exact hne0 (hn_zero_of_nonpos C (not_lt.mp hle))
    exact c.clique_of_pos C hpos
  let idxList : V → List (Fin m) := fun v =>
    (List.finRange m).filter (fun j => decide (v ∈ copies.get j))
  have hidx_nodup : ∀ v : V, (idxList v).Nodup := fun v =>
    (List.nodup_finRange m).filter _
  have hidx_len : ∀ v : V, k ≤ (idxList v).length := by
    intro v
    have hsum_real : (k : ℝ) ≤ ∑ C : Finset V, if v ∈ C then (n C : ℝ) else 0 := by
      calc (k : ℝ)
          = (k : ℝ) * 1 := (mul_one _).symm
        _ ≤ (k : ℝ) * ∑ C : Finset V, if v ∈ C then c.weight C else 0 :=
              mul_le_mul_of_nonneg_left (c.cover v) hk_real.le
        _ = ∑ C : Finset V, if v ∈ C then (k : ℝ) * c.weight C else 0 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun C _ => ?_
              split_ifs <;> ring
        _ ≤ ∑ C : Finset V, if v ∈ C then (n C : ℝ) else 0 := by
              refine Finset.sum_le_sum fun C _ => ?_
              split_ifs
              · exact Nat.le_ceil _
              · exact le_rfl
    have hcount_eq : (idxList v).length = ∑ C : Finset V, if v ∈ C then n C else 0 := by
      have h1 : (idxList v).length = copies.countP (fun C => decide (v ∈ C)) := by
        rw [List.countP_eq_length_filter]
        have hmap : (List.finRange m).map (fun j : Fin m => copies.get j) = copies := by
          apply List.ext_get
          · simp [m]
          · intro i hi1 hi2
            simp
        conv_rhs => rw [← hmap, List.filter_map, List.length_map]
        rfl
      rw [h1]
      simp only [copies, List.countP_flatMap, Function.comp_def, List.countP_replicate]
      rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList, Multiset.map_coe, Multiset.sum_coe]
      refine congrArg List.sum (List.map_congr_left fun C _ => ?_)
      by_cases hv : v ∈ C <;> simp [hv]
    rw [hcount_eq]
    exact_mod_cast hsum_real
  let assign : V → Fin k → Fin m := fun v i =>
    (idxList v).get ⟨i.val, lt_of_lt_of_le i.isLt (hidx_len v)⟩
  let fam : Fin m → Finset (V × Fin k) := fun j =>
    Finset.univ.filter fun p => assign p.1 p.2 = j
  refine ⟨k, m, hk_pos, ⟨fam, ?_, ?_⟩, hm_bound⟩
  · intro j p₁ hp₁ p₂ hp₂ hne
    simp only [fam, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    have hmem1 : j ∈ idxList p₁.1 := hp₁ ▸ List.get_mem (idxList p₁.1) _
    have hmem2 : j ∈ idxList p₂.1 := hp₂ ▸ List.get_mem (idxList p₂.1) _
    simp only [idxList, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hmem1 hmem2
    have hu_ne : p₁.1 ≠ p₂.1 := by
      intro heq
      apply hne
      apply Prod.ext heq
      have hassign : assign p₁.1 p₁.2 = assign p₁.1 p₂.2 := by
        rw [hp₁]
        have hp2' : assign p₁.1 p₂.2 = j := by simpa [heq] using hp₂
        exact hp2'.symm
      have hidx_eq : (⟨p₁.2.val, lt_of_lt_of_le p₁.2.isLt (hidx_len p₁.1)⟩ : Fin (idxList p₁.1).length) =
          ⟨p₂.2.val, lt_of_lt_of_le p₂.2.isLt (hidx_len p₁.1)⟩ :=
        (List.nodup_iff_injective_get.mp (hidx_nodup p₁.1)) hassign
      exact Fin.ext (Fin.mk.inj hidx_eq)
    exact hcopies_clq j hmem1 hmem2 hu_ne
  · rintro ⟨v, i⟩
    refine ⟨assign v i, ?_⟩
    simp [fam]

/-! ## Part 3A: Unified Primal/Dual SDP (`lovaszTheta`, `schrijverTheta`, `SchrijverCert`) -/

section SDP
open Classical

set_option linter.unusedFintypeInType false in
/-- Primal SDP definition of the Lovász theta number `ϑ(G)`. -/
noncomputable def lovaszTheta {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sSup {t : ℝ | ∃ X : Matrix V V ℝ,
    X.PosSemidef ∧ X.trace = 1 ∧ (∀ i j, G.Adj i j → X i j = 0) ∧ t = ∑ i, ∑ j, X i j}

set_option linter.unusedFintypeInType false in
/-- Primal SDP definition of the Schrijver theta number `ϑ'(G)` (nonnegative primal matrix `X`). -/
noncomputable def schrijverTheta {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sSup {t : ℝ | ∃ X : Matrix V V ℝ,
    X.PosSemidef ∧ X.trace = 1 ∧ (∀ i j, G.Adj i j → X i j = 0) ∧
    (∀ i j, 0 ≤ X i j) ∧ t = ∑ i, ∑ j, X i j}

set_option linter.unusedFintypeInType false in
/-- Dual semidefinite certificate for Schrijver's `ϑ'(G) ≤ β⁻¹`, weakening `nonadj_zero` to `nonadj_nonpos`. -/
structure SchrijverCert {V : Type*} [Fintype V] (G : SimpleGraph V) (β : ℝ) where
  W : Matrix V V ℝ
  hβ : 0 < β
  symm : W.IsSymm
  diag_le_one : ∀ i, W i i ≤ 1
  nonadj_nonpos : ∀ i j, i ≠ j → ¬ G.Adj i j → W i j ≤ 0
  psd : (W - β • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef

private lemma lovasz_primal_nonempty {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    {t : ℝ | ∃ X : Matrix V V ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧ (∀ i j, G.Adj i j → X i j = 0) ∧ t = ∑ i, ∑ j, X i j}.Nonempty := by
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let X : Matrix V V ℝ := (Fintype.card V : ℝ)⁻¹ • (1 : Matrix V V ℝ)
  refine ⟨1, X, ?_, ?_, ?_, ?_⟩
  · exact Matrix.PosSemidef.one.smul (inv_nonneg.mpr hcard.le)
  · simp only [X, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, inv_mul_cancel₀ hcard.ne']
  · intro i j hadj
    simp [X, hadj.ne]
  · have hrow : ∀ i : V, ∑ j : V, X i j = (Fintype.card V : ℝ)⁻¹ := fun i => by
      simp only [X, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji.symm]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    simp_rw [hrow]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']

private lemma schrijver_primal_nonempty {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    {t : ℝ | ∃ X : Matrix V V ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧ (∀ i j, G.Adj i j → X i j = 0) ∧
      (∀ i j, 0 ≤ X i j) ∧ t = ∑ i, ∑ j, X i j}.Nonempty := by
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let X : Matrix V V ℝ := (Fintype.card V : ℝ)⁻¹ • (1 : Matrix V V ℝ)
  refine ⟨1, X, ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.PosSemidef.one.smul (inv_nonneg.mpr hcard.le)
  · simp only [X, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, inv_mul_cancel₀ hcard.ne']
  · intro i j hadj
    simp [X, hadj.ne]
  · intro i j
    simp only [X, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]
      exact inv_nonneg.mpr hcard.le
    · simp
  · have hrow : ∀ i : V, ∑ j : V, X i j = (Fintype.card V : ℝ)⁻¹ := fun i => by
      simp only [X, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji.symm]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    simp_rw [hrow]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']

private lemma lovasz_primal_le_of_cert {V : Type*} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : LovaszCert G β) {X : Matrix V V ℝ}
    (hX : X.PosSemidef) (htr : X.trace = 1) (hadj : ∀ i j, G.Adj i j → X i j = 0) :
    ∑ i, ∑ j, X i j ≤ β⁻¹ := by
  have hhad : (X.hadamard (cert.W - β • Matrix.of (fun _ _ => (1 : ℝ)))).PosSemidef :=
    hX.hadamard cert.psd
  have hquad := hhad.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  have hquad_sum :
      0 ≤ ∑ i : V, ∑ j : V, X i j * (cert.W i j - β) := by
    simpa [dotProduct, Matrix.mulVec, Matrix.hadamard_apply] using hquad
  have hWX : ∑ i : V, ∑ j : V, X i j * cert.W i j ≤ 1 := by
    have hsplit :
        ∑ i : V, ∑ j : V, X i j * cert.W i j = ∑ i : V, X i i * cert.W i i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Finset.sum_eq_single i
        (fun j _ hji => by
          by_cases hG : G.Adj i j
          · rw [hadj i j hG, zero_mul]
          · rw [cert.nonadj_zero i j hji.symm hG, mul_zero])
        (fun hi => absurd (Finset.mem_univ i) hi)
    rw [hsplit, ← htr]
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_of_le_one_right (hX.diag_nonneg) (cert.diag_le_one i)
  have hsum_le : β * ∑ i : V, ∑ j : V, X i j ≤ 1 := by
    have hexpand :
        ∑ i : V, ∑ j : V, X i j * (cert.W i j - β) =
          (∑ i : V, ∑ j : V, X i j * cert.W i j) - β * ∑ i : V, ∑ j : V, X i j := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
    linarith
  rw [← one_div, le_div_iff₀ cert.hβ]
  linarith

private lemma schrijver_primal_le_of_cert {V : Type*} [Fintype V] {G : SimpleGraph V} {β : ℝ}
    (cert : SchrijverCert G β) {X : Matrix V V ℝ}
    (hX : X.PosSemidef) (htr : X.trace = 1) (hadj : ∀ i j, G.Adj i j → X i j = 0)
    (hnonneg : ∀ i j, 0 ≤ X i j) :
    ∑ i, ∑ j, X i j ≤ β⁻¹ := by
  have hhad : (X.hadamard (cert.W - β • Matrix.of (fun _ _ => (1 : ℝ)))).PosSemidef :=
    hX.hadamard cert.psd
  have hquad := hhad.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  have hquad_sum :
      0 ≤ ∑ i : V, ∑ j : V, X i j * (cert.W i j - β) := by
    simpa [dotProduct, Matrix.mulVec, Matrix.hadamard_apply] using hquad
  have hWX : ∑ i : V, ∑ j : V, X i j * cert.W i j ≤ 1 := by
    have hdiag : ∀ i : V, ∑ j : V, X i j * cert.W i j ≤ X i i := by
      intro i
      have hterm : ∀ j : V, j ≠ i → X i j * cert.W i j ≤ 0 := by
        intro j hji
        by_cases hG : G.Adj i j
        · rw [hadj i j hG, zero_mul]
        · exact mul_nonpos_of_nonneg_of_nonpos (hnonneg i j) (cert.nonadj_nonpos i j hji.symm hG)
      have herase : ∑ j ∈ Finset.univ.erase i, X i j * cert.W i j ≤ 0 :=
        Finset.sum_nonpos fun j hj => hterm j (Finset.ne_of_mem_erase hj)
      have hsplit : ∑ j : V, X i j * cert.W i j =
          X i i * cert.W i i + ∑ j ∈ Finset.univ.erase i, X i j * cert.W i j :=
        (Finset.add_sum_erase Finset.univ (fun j => X i j * cert.W i j) (Finset.mem_univ i)).symm
      have hdiag1 : X i i * cert.W i i ≤ X i i :=
        mul_le_of_le_one_right (hX.diag_nonneg) (cert.diag_le_one i)
      linarith
    calc ∑ i : V, ∑ j : V, X i j * cert.W i j
        ≤ ∑ i : V, X i i := Finset.sum_le_sum fun i _ => hdiag i
      _ = X.trace := rfl
      _ = 1 := htr
  have hsum_le : β * ∑ i : V, ∑ j : V, X i j ≤ 1 := by
    have hexpand :
        ∑ i : V, ∑ j : V, X i j * (cert.W i j - β) =
          (∑ i : V, ∑ j : V, X i j * cert.W i j) - β * ∑ i : V, ∑ j : V, X i j := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
    linarith
  rw [← one_div, le_div_iff₀ cert.hβ]
  linarith

private noncomputable def trivial_lovaszCert {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    LovaszCert G (Fintype.card V : ℝ)⁻¹ where
  W := 1
  hβ := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  symm := Matrix.IsSymm.ext fun i j => by simp [Matrix.one_apply, eq_comm]
  diag_le_one := fun i => by simp
  nonadj_zero := fun i j hij _ => by simp [hij]
  psd := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact Matrix.isHermitian_iff_isSymm.mpr (Matrix.IsSymm.ext fun i j => by
        simp [Matrix.sub_apply, Matrix.one_apply, eq_comm])
    · intro x
      have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
      have hmul :
          (1 - (Fintype.card V : ℝ)⁻¹ • Matrix.of (fun _ _ : V => (1 : ℝ))).mulVec x =
            fun i => x i - (Fintype.card V : ℝ)⁻¹ * ∑ j : V, x j := by
        ext i
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
      have hquad :
          star x ⬝ᵥ ((1 - (Fintype.card V : ℝ)⁻¹ • Matrix.of (fun _ _ : V => (1 : ℝ))).mulVec x) =
            (∑ i : V, x i ^ 2) - (Fintype.card V : ℝ)⁻¹ * (∑ i : V, x i) ^ 2 := by
        rw [hmul]
        simp only [dotProduct, Pi.star_apply, star_trivial, mul_sub, Finset.sum_sub_distrib]
        have hsq : ∑ i : V, x i * x i = ∑ i : V, x i ^ 2 :=
          Finset.sum_congr rfl fun i _ => (sq (x i)).symm
        have hcross :
            ∑ i : V, x i * ((Fintype.card V : ℝ)⁻¹ * ∑ j : V, x j) =
              (Fintype.card V : ℝ)⁻¹ * (∑ i : V, x i) ^ 2 := by
          rw [← Finset.sum_mul, sq]
          ring
        rw [hsq, hcross]
      rw [hquad]
      have hdiff_nonneg : 0 ≤ ∑ i : V, ∑ j : V, (x i - x j) ^ 2 :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hcs_id :
          ∑ i : V, ∑ j : V, (x i - x j) ^ 2 =
            2 * (Fintype.card V : ℝ) * (∑ i : V, x i ^ 2) - 2 * (∑ i : V, x i) ^ 2 := by
        have hexp : ∀ i j : V, (x i - x j) ^ 2 = x i ^ 2 - 2 * (x i * x j) + x j ^ 2 := fun i j => by
          ring
        simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [sq]
        ring
      have hcs : (∑ i : V, x i) ^ 2 ≤ (Fintype.card V : ℝ) * ∑ i : V, x i ^ 2 := by linarith
      have hcs' : (Fintype.card V : ℝ)⁻¹ * (∑ i : V, x i) ^ 2 ≤ ∑ i : V, x i ^ 2 := by
        rw [inv_mul_le_iff₀ hcard]
        exact hcs
      linarith

private lemma lovasz_primal_bddAbove {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    BddAbove {t : ℝ | ∃ X : Matrix V V ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧ (∀ i j, G.Adj i j → X i j = 0) ∧ t = ∑ i, ∑ j, X i j} := by
  refine ⟨(Fintype.card V : ℝ), ?_⟩
  rintro t ⟨X, hX, htr, hadj, rfl⟩
  have h := lovasz_primal_le_of_cert (trivial_lovaszCert G) hX htr hadj
  simpa using h

private lemma schrijver_primal_bddAbove {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    BddAbove {t : ℝ | ∃ X : Matrix V V ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧ (∀ i j, G.Adj i j → X i j = 0) ∧
      (∀ i j, 0 ≤ X i j) ∧ t = ∑ i, ∑ j, X i j} := by
  refine ⟨(Fintype.card V : ℝ), ?_⟩
  rintro t ⟨X, hX, htr, hadj, _, rfl⟩
  have h := lovasz_primal_le_of_cert (trivial_lovaszCert G) hX htr hadj
  simpa using h

theorem schrijverTheta_le_lovaszTheta {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    schrijverTheta G ≤ lovaszTheta G := by
  apply csSup_le (schrijver_primal_nonempty G)
  rintro t ⟨X, hX, htr, hadj, _, rfl⟩
  exact le_csSup (lovasz_primal_bddAbove G) ⟨X, hX, htr, hadj, rfl⟩

theorem lovaszTheta_le_of_cert {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {β : ℝ} (cert : LovaszCert G β) :
    lovaszTheta G ≤ β⁻¹ := by
  apply csSup_le (lovasz_primal_nonempty G)
  rintro t ⟨X, hX, htr, hadj, rfl⟩
  exact lovasz_primal_le_of_cert cert hX htr hadj

theorem schrijverTheta_le_of_cert {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {β : ℝ} (cert : SchrijverCert G β) :
    schrijverTheta G ≤ β⁻¹ := by
  apply csSup_le (schrijver_primal_nonempty G)
  rintro t ⟨X, hX, htr, hadj, hnonneg, rfl⟩
  exact schrijver_primal_le_of_cert cert hX htr hadj hnonneg

theorem le_lovaszTheta_of_primal {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    (X : Matrix V V ℝ) (hX : X.PosSemidef) (htr : X.trace = 1)
    (hadj : ∀ i j, G.Adj i j → X i j = 0) :
    ∑ i, ∑ j, X i j ≤ lovaszTheta G :=
  le_csSup (lovasz_primal_bddAbove G) ⟨X, hX, htr, hadj, rfl⟩

theorem le_schrijverTheta_of_primal {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    (X : Matrix V V ℝ) (hX : X.PosSemidef) (htr : X.trace = 1)
    (hadj : ∀ i j, G.Adj i j → X i j = 0) (hnonneg : ∀ i j, 0 ≤ X i j) :
    ∑ i, ∑ j, X i j ≤ schrijverTheta G :=
  le_csSup (schrijver_primal_bddAbove G) ⟨X, hX, htr, hadj, hnonneg, rfl⟩

theorem indepNum_le_schrijverTheta {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    (G.indepNum : ℝ) ≤ schrijverTheta G := by
  obtain ⟨S, hS_indep, hS_card⟩ := G.exists_isNIndepSet_indepNum
  have hS_pos : 0 < S.card := by
    obtain ⟨v₀⟩ := ‹Nonempty V›
    have h1 : 1 ≤ G.indepNum := by
      have hind1 : G.IsIndepSet (({v₀} : Finset V) : Set V) := by simp
      simpa using hind1.card_le_indepNum
    omega
  have hS_real : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr hS_pos
  let x : V → ℝ := fun i => if i ∈ S then 1 else 0
  let X : Matrix V V ℝ := (S.card : ℝ)⁻¹ • Matrix.vecMulVec x (star x)
  have hX_psd : X.PosSemidef :=
    (Matrix.posSemidef_vecMulVec_self_star x).smul (inv_nonneg.mpr hS_real.le)
  have hX_tr : X.trace = 1 := by
    have hdiag : ∀ i : V, X i i = (S.card : ℝ)⁻¹ * (if i ∈ S then 1 else 0) := fun i => by
      simp only [X, Matrix.smul_apply, Matrix.vecMulVec_apply, star_trivial,
        smul_eq_mul, x]
      split_ifs <;> ring
    change ∑ i : V, X i i = 1
    simp_rw [hdiag, ← Finset.mul_sum]
    simp [inv_mul_cancel₀ hS_real.ne']
  have hX_adj : ∀ i j, G.Adj i j → X i j = 0 := by
    intro i j hadj
    simp only [X, Matrix.smul_apply, Matrix.vecMulVec_apply, star_trivial, smul_eq_mul, x]
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
    · exact absurd hadj (hS_indep hi hj hadj.ne)
    · simp [hi, hj]
    · simp [hi, hj]
    · simp [hi, hj]
  have hX_nonneg : ∀ i j, 0 ≤ X i j := by
    intro i j
    simp only [X, Matrix.smul_apply, Matrix.vecMulVec_apply, star_trivial, smul_eq_mul, x]
    refine mul_nonneg (inv_nonneg.mpr hS_real.le) (mul_nonneg ?_ ?_) <;> split_ifs <;> norm_num
  have hX_sum : ∑ i, ∑ j, X i j = (G.indepNum : ℝ) := by
    simp only [X, Matrix.smul_apply, Matrix.vecMulVec_apply, star_trivial, smul_eq_mul, x]
    simp_rw [← Finset.mul_sum]
    have hsum1 : ∑ i : V, (if i ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by simp
    have hsum2 : ∑ i : V, (if i ∈ S then (1 : ℝ) else 0) * ∑ j : V, (if j ∈ S then (1 : ℝ) else 0) =
        (S.card : ℝ) * (S.card : ℝ) := by
      simp_rw [hsum1, ← Finset.sum_mul, hsum1]
    rw [hsum2, ← mul_assoc, inv_mul_cancel₀ hS_real.ne', one_mul, hS_card]
  exact hX_sum ▸ le_schrijverTheta_of_primal X hX_psd hX_tr hX_adj hX_nonneg

theorem indepNum_le_lovaszTheta {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    (G.indepNum : ℝ) ≤ lovaszTheta G :=
  (indepNum_le_schrijverTheta G).trans (schrijverTheta_le_lovaszTheta G)

end SDP

/-! ## Part 3B: `Gilbert32` — Schrijver `ϑ'` Non-Submultiplicativity -/

/-- Hamming weight of the lowest 5 bits of `n`. -/
def hammingWeight5 (n : ℕ) : ℕ :=
  (n.testBit 0).toNat + (n.testBit 1).toNat + (n.testBit 2).toNat +
    (n.testBit 3).toNat + (n.testBit 4).toNat

/-- Gilbert's 32-vertex graph on `Fin 32` (`{0,1}^5`), adjacent iff Hamming distance `∈ {1, 2}`. -/
def gilbert32 : SimpleGraph (Fin 32) where
  Adj u v := u ≠ v ∧ let d := hammingWeight5 (u.val ^^^ v.val); d = 1 ∨ d = 2
  symm := ⟨fun _ _ ⟨hne, hd⟩ => ⟨hne.symm, by simpa [Nat.xor_comm] using hd⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

instance instDecidableRelGilbert32 : DecidableRel gilbert32.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ let d := hammingWeight5 (u.val ^^^ v.val); d = 1 ∨ d = 2))

private def gilbert32Indep4 : List (Fin 32) := [0, 7, 25, 30]

private def gilbert32SqIndep20 : List (Fin 2 → Fin 32) :=
  ([(3, 11), (6, 22), (12, 13), (24, 26), (17, 21),
    (5, 24), (10, 17), (20, 3), (9, 6), (18, 12),
    (7, 5), (14, 10), (28, 20), (25, 9), (19, 18),
    (11, 28), (22, 25), (13, 19), (26, 7), (21, 14)] : List (Fin 32 × Fin 32)).map
    fun p idx => if idx = 0 then p.1 else p.2

theorem gilbert32_sq_indep_twenty : 20 ≤ (strongPowPi gilbert32 2).indepNum :=
  length_le_indepNum_of_list (l := gilbert32SqIndep20) (by decide) (by decide)

private def gilbert32SInt (k : Fin 5) (u : Fin 32) : ℤ :=
  if u.val.testBit k.val then -1 else 1

private def gilbert32PInt (u : Fin 32) : ℤ :=
  if hammingWeight5 u.val % 2 = 1 then -1 else 1

private def gilbert32WInt (u v : Fin 32) : ℤ :=
  if u = v then 8
  else if gilbert32.Adj u v then 4
  else if hammingWeight5 (u.val ^^^ v.val) = 5 then -4
  else 0

private lemma gilbert32_schrijver_gram_int :
    ∀ u v : Fin 32, gilbert32WInt u v - 2 =
      (∑ k : Fin 5, gilbert32SInt k u * gilbert32SInt k v) +
        gilbert32PInt u * gilbert32PInt v := by
  decide

theorem gilbert32_schrijverTheta_eq_four : schrijverTheta gilbert32 = 4 := by
  have hge : (4 : ℝ) ≤ gilbert32.indepNum := by
    exact_mod_cast length_le_indepNum_of_list (l := gilbert32Indep4) (by decide) (by decide)
  have hcert : SchrijverCert gilbert32 (1 / 4) :=
    { W := Matrix.of fun u v => (gilbert32WInt u v : ℝ) / 8
      hβ := by norm_num
      symm := Matrix.IsSymm.ext fun u v => by
        simp only [Matrix.of_apply]
        have hsymm : gilbert32WInt u v = gilbert32WInt v u := by
          revert u v; decide
        rw [hsymm]
      diag_le_one := fun u => by
        simp [gilbert32WInt]
      nonadj_nonpos := fun u v huv hnadj => by
        simp only [Matrix.of_apply, gilbert32WInt, huv, hnadj, ↓reduceIte]
        split_ifs <;> norm_num
      psd := by
        let sVec : Fin 5 → Fin 32 → ℝ := fun k u => (gilbert32SInt k u : ℝ)
        let pVec : Fin 32 → ℝ := fun u => (gilbert32PInt u : ℝ)
        have hdecomp :
            Matrix.of (fun u v : Fin 32 => (gilbert32WInt u v : ℝ) / 8) -
              (1 / 4 : ℝ) • Matrix.of (fun _ _ : Fin 32 => (1 : ℝ)) =
              (1 / 8 : ℝ) • ((∑ k : Fin 5, Matrix.vecMulVec (sVec k) (star (sVec k))) +
                Matrix.vecMulVec pVec (star pVec)) := by
          ext u v
          have hid : ((gilbert32WInt u v : ℝ) - 2) =
              (∑ k : Fin 5, (gilbert32SInt k u : ℝ) * (gilbert32SInt k v : ℝ)) +
                (gilbert32PInt u : ℝ) * (gilbert32PInt v : ℝ) := by
            exact_mod_cast gilbert32_schrijver_gram_int u v
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.add_apply,
            Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial, smul_eq_mul,
            mul_one, sVec, pVec]
          linarith
        rw [hdecomp]
        refine Matrix.PosSemidef.smul ?_ (by norm_num)
        exact (Matrix.posSemidef_sum Finset.univ fun k _ =>
          Matrix.posSemidef_vecMulVec_self_star (sVec k)).add
          (Matrix.posSemidef_vecMulVec_self_star pVec) }
  have hle := schrijverTheta_le_of_cert hcert
  norm_num at hle
  exact le_antisymm hle (hge.trans (indepNum_le_schrijverTheta gilbert32))

theorem gilbert32_indep_four : gilbert32.indepNum = 4 := by
  have hge : 4 ≤ gilbert32.indepNum :=
    length_le_indepNum_of_list (l := gilbert32Indep4) (by decide) (by decide)
  have hle : (gilbert32.indepNum : ℝ) ≤ 4 :=
    (indepNum_le_schrijverTheta gilbert32).trans_eq gilbert32_schrijverTheta_eq_four
  have hle_nat : gilbert32.indepNum ≤ 4 := by exact_mod_cast hle
  omega

theorem gilbert32_schrijver_fails_submult :
    schrijverTheta gilbert32 ^ 2 < ((strongPowPi gilbert32 2).indepNum : ℝ) ∧
      schrijverTheta gilbert32 < Real.sqrt 20 ∧
      Real.sqrt 20 ≤ shannonCapacity gilbert32 := by
  have h20 : (20 : ℝ) ≤ ((strongPowPi gilbert32 2).indepNum : ℝ) := by
    exact_mod_cast gilbert32_sq_indep_twenty
  have hcap : Real.sqrt 20 ≤ shannonCapacity gilbert32 := by
    have hlow := le_shannonCapacity_of_indepSet_pi gilbert32 (by norm_num : 0 < 2)
      (isIndepSet_of_pairwise (G := strongPowPi gilbert32 2) (by decide : gilbert32SqIndep20.Pairwise _))
    have hcard : gilbert32SqIndep20.toFinset.card = 20 := by decide
    rw [hcard] at hlow
    simpa [Real.sqrt_eq_rpow] using hlow
  refine ⟨?_, ?_, hcap⟩
  · rw [gilbert32_schrijverTheta_eq_four]
    linarith
  · rw [gilbert32_schrijverTheta_eq_four]
    rw [Real.lt_sqrt (by norm_num)]
    norm_num

private def gilbert32ChiInt (y u : Fin 32) : ℤ :=
  if hammingWeight5 (y.val &&& u.val) % 2 = 1 then -1 else 1

private def gilbert32Wt3List : List (Fin 32) :=
  (List.finRange 32).filter fun y => hammingWeight5 y.val == 3

private def gilbert32Wt15List : List (Fin 32) :=
  (List.finRange 32).filter fun y =>
    let w := hammingWeight5 y.val
    w == 1 || w == 5

private def gilbert32Wt24List : List (Fin 32) :=
  (List.finRange 32).filter fun y =>
    let w := hammingWeight5 y.val
    w == 2 || w == 4

private def gilbert32PrimalInt (u v : Fin 32) : ℤ :=
  2 + (gilbert32Wt3List.map fun y => gilbert32ChiInt y u * gilbert32ChiInt y v).sum

private def gilbert32DualWInt (u v : Fin 32) : ℤ :=
  if u = v then 96 else if gilbert32.Adj u v then 32 else 0

private lemma gilbert32_primal_diag : ∀ u : Fin 32, gilbert32PrimalInt u u = 12 := by
  decide

private lemma gilbert32_primal_adj :
    ∀ u v : Fin 32, gilbert32.Adj u v → gilbert32PrimalInt u v = 0 := by
  decide

private lemma gilbert32_chi_sum_wt3 :
    ∀ y ∈ gilbert32Wt3List, (∑ u : Fin 32, gilbert32ChiInt y u) = 0 := by
  decide

private lemma gilbert32_dual_gram_int :
    ∀ u v : Fin 32, gilbert32DualWInt u v - 18 =
      8 * (gilbert32Wt15List.map fun y => gilbert32ChiInt y u * gilbert32ChiInt y v).sum +
        2 * (gilbert32Wt24List.map fun y => gilbert32ChiInt y u * gilbert32ChiInt y v).sum := by
  decide

private lemma list_vecMulVec_sum_apply {V : Type*} (l : List (Fin 32))
    (v : Fin 32 → V → ℝ) (a b : V) :
    (l.map fun y => Matrix.vecMulVec (v y) (star (v y))).sum a b =
      (l.map fun y => v y a * v y b).sum := by
  induction l with
  | nil => simp
  | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons, Matrix.add_apply, Matrix.vecMulVec_apply]
      rw [ih]
      simp [star_trivial]

private lemma list_vecMulVec_sum_psd {V : Type*} [Fintype V] (l : List (Fin 32))
    (v : Fin 32 → V → ℝ) :
    (l.map fun y => Matrix.vecMulVec (v y) (star (v y))).sum.PosSemidef := by
  induction l with
  | nil => simpa using Matrix.PosSemidef.zero
  | cons y ys ih =>
      simpa using (Matrix.posSemidef_vecMulVec_self_star (v y)).add ih

theorem gilbert32_lovaszTheta_eq : lovaszTheta gilbert32 = 16 / 3 := by
  apply le_antisymm
  · let cert : LovaszCert gilbert32 (3 / 16) :=
      { W := Matrix.of fun u v => (gilbert32DualWInt u v : ℝ) / 96
        hβ := by norm_num
        symm := Matrix.IsSymm.ext fun u v => by
          simp only [Matrix.of_apply]
          have hsym : gilbert32DualWInt u v = gilbert32DualWInt v u := by revert u v; decide
          rw [hsym]
        diag_le_one := fun u => by simp [gilbert32DualWInt]
        nonadj_zero := fun u v huv hnadj => by simp [gilbert32DualWInt, huv, hnadj]
        psd := by
          let chiVec : Fin 32 → Fin 32 → ℝ := fun y u => (gilbert32ChiInt y u : ℝ)
          have hdecomp :
              Matrix.of (fun u v : Fin 32 => (gilbert32DualWInt u v : ℝ) / 96) -
                (3 / 16 : ℝ) • Matrix.of (fun _ _ : Fin 32 => (1 : ℝ)) =
                (8 / 96 : ℝ) • (gilbert32Wt15List.map fun y =>
                    Matrix.vecMulVec (chiVec y) (star (chiVec y))).sum +
                  (2 / 96 : ℝ) • (gilbert32Wt24List.map fun y =>
                    Matrix.vecMulVec (chiVec y) (star (chiVec y))).sum := by
            ext u v
            have hid : (gilbert32DualWInt u v : ℝ) - 18 =
                8 * (gilbert32Wt15List.map fun y =>
                    (gilbert32ChiInt y u : ℝ) * (gilbert32ChiInt y v : ℝ)).sum +
                  2 * (gilbert32Wt24List.map fun y =>
                    (gilbert32ChiInt y u : ℝ) * (gilbert32ChiInt y v : ℝ)).sum := by
              have h := gilbert32_dual_gram_int u v
              have hcast := congrArg (Int.cast : ℤ → ℝ) h
              simpa [List.map_map, Function.comp_def] using hcast
            simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
              smul_eq_mul, mul_one,
              list_vecMulVec_sum_apply gilbert32Wt15List chiVec u v,
              list_vecMulVec_sum_apply gilbert32Wt24List chiVec u v]
            dsimp only [chiVec]
            linarith
          rw [hdecomp]
          exact ((list_vecMulVec_sum_psd gilbert32Wt15List chiVec).smul (by norm_num)).add
            ((list_vecMulVec_sum_psd gilbert32Wt24List chiVec).smul (by norm_num)) }
    have hle := lovaszTheta_le_of_cert cert
    norm_num at hle
    exact hle
  · let chiVec : Fin 32 → Fin 32 → ℝ := fun y u => (gilbert32ChiInt y u : ℝ)
    let X : Matrix (Fin 32) (Fin 32) ℝ :=
      (1 / 384 : ℝ) • ((2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) +
        (gilbert32Wt3List.map fun y => Matrix.vecMulVec (chiVec y) (star (chiVec y))).sum)
    have hX_entry : ∀ u v : Fin 32, X u v = (gilbert32PrimalInt u v : ℝ) / 384 := by
      intro u v
      simp only [X, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul, mul_one,
        list_vecMulVec_sum_apply gilbert32Wt3List chiVec u v, gilbert32PrimalInt]
      push_cast
      simp only [List.map_map, Function.comp_def, Int.cast_mul]
      dsimp only [chiVec]
      ring
    have hX_psd : X.PosSemidef := by
      have hones : (Matrix.of fun _ _ : Fin 32 => (1 : ℝ)).PosSemidef := posSemidef_allOnes (Fin 32)
      exact ((hones.smul (by norm_num)).add (list_vecMulVec_sum_psd gilbert32Wt3List chiVec)).smul
        (by norm_num)
    have hX_tr : X.trace = 1 := by
      simp only [Matrix.trace, Matrix.diag, hX_entry]
      have hdiag : ∀ u : Fin 32, (gilbert32PrimalInt u u : ℝ) = 12 := fun u => by
        exact_mod_cast gilbert32_primal_diag u
      simp_rw [hdiag]
      simp
      norm_num
    have hX_adj : ∀ u v : Fin 32, gilbert32.Adj u v → X u v = 0 := by
      intro u v hadj
      rw [hX_entry]
      have h0 : (gilbert32PrimalInt u v : ℝ) = 0 := by
        exact_mod_cast gilbert32_primal_adj u v hadj
      rw [h0, zero_div]
    have hX_sum : ∑ u : Fin 32, ∑ v : Fin 32, X u v = 16 / 3 := by
      have hlist_sum :
          (∑ u : Fin 32, ∑ v : Fin 32,
            (gilbert32Wt3List.map fun y => Matrix.vecMulVec (chiVec y) (star (chiVec y))).sum u v) = 0 := by
        have hstep : ∀ l : List (Fin 32),
            (∑ u : Fin 32, ∑ v : Fin 32,
              (l.map fun y => Matrix.vecMulVec (chiVec y) (star (chiVec y))).sum u v) =
              (l.map fun y => (∑ u : Fin 32, chiVec y u) * (∑ v : Fin 32, chiVec y v)).sum := by
          intro l
          induction l with
          | nil => simp
          | cons y ys ih =>
              simp only [List.map_cons, List.sum_cons, Matrix.add_apply, Finset.sum_add_distrib, ih]
              congr 1
              simp only [Matrix.vecMulVec_apply, star_trivial, Finset.sum_mul, Finset.mul_sum]
              exact Finset.sum_comm
        rw [hstep gilbert32Wt3List]
        refine List.sum_eq_zero ?_
        intro r hr
        simp only [List.mem_map] at hr
        rcases hr with ⟨y, hy, rfl⟩
        have hz : ∑ u : Fin 32, chiVec y u = 0 := by
          have := congrArg (Int.cast : ℤ → ℝ) (gilbert32_chi_sum_wt3 y hy)
          simpa [chiVec] using this
        rw [hz, zero_mul]
      simp only [X, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul, mul_one,
        ← Finset.mul_sum, Finset.sum_add_distrib, hlist_sum, add_zero]
      simp [Finset.sum_const]
      norm_num
    exact hX_sum ▸ le_lovaszTheta_of_primal X hX_psd hX_tr hX_adj

/-! ## Part 3C: `Haemers27` (`srg(27,10,1,5)`) & `Schlafli27` (`srg(27,16,10,8)`) -/

private def haemers27Masks : Array Nat := #[
  130944, 1974080, 14823104, 52710848, 88640448, 110168000,
  127038, 1970237, 14819387, 52707383, 88637487, 110166047,
  132120771, 119275845, 81396297, 45483089, 23988321,
  117555590, 79798922, 44131474, 23128226,
  68784908, 34952468, 17619236,
  9647640, 4897320,
  2522160
]

private def haemers27Mask (i : Fin 27) : Nat :=
  haemers27Masks[i.val]!

/-- Haemers' 27-vertex strongly regular graph `srg(27, 10, 1, 5)` (the non-intersection graph of
the 27 lines on a smooth cubic surface). -/
def haemers27 : SimpleGraph (Fin 27) where
  Adj i j := (haemers27Mask i).testBit j.val
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance instDecidableRelHaemers27 : DecidableRel haemers27.Adj := fun i j =>
  inferInstanceAs (Decidable ((haemers27Mask i).testBit j.val))

/-- The Schläfli graph `srg(27, 16, 10, 8)`, defined as the complement of `haemers27`. -/
def schlafli27 : SimpleGraph (Fin 27) :=
  haemers27ᶜ

instance instDecidableRelSchlafli27 : DecidableRel schlafli27.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ¬ haemers27.Adj i j))

private def popcountAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, m => (m.testBit k).toNat + popcountAux k m

/-- Bitwise population count over the lowest 27 bits. -/
def popcount27 (m : ℕ) : ℕ :=
  popcountAux 27 m

private lemma sum_mul_testBit_eq_popcountAux (n a b : ℕ) :
    (∑ k : Fin n, (if a.testBit k.val then (1 : ℝ) else 0) *
      (if b.testBit k.val then (1 : ℝ) else 0)) = (popcountAux n (a &&& b) : ℝ) := by
  induction n with
  | zero => simp [popcountAux]
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      have hcast :
          (∑ i : Fin n, (if a.testBit i.castSucc.val then (1 : ℝ) else 0) *
            (if b.testBit i.castSucc.val then (1 : ℝ) else 0)) =
            (∑ k : Fin n, (if a.testBit k.val then (1 : ℝ) else 0) *
              (if b.testBit k.val then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl fun _ _ => rfl
      rw [hcast, ih]
      simp only [Fin.val_last, popcountAux, Nat.testBit_and]
      push_cast
      by_cases ha : a.testBit n <;> by_cases hb : b.testBit n <;> simp [ha, hb, add_comm]

private lemma haemers27_deg_eq_ten : ∀ i : Fin 27, popcount27 (haemers27Mask i) = 10 := by
  decide

private lemma haemers27_srg_popcount :
    ∀ i j : Fin 27, popcount27 (haemers27Mask i &&& haemers27Mask j) =
      if i = j then 10 else if haemers27.Adj i j then 1 else 5 := by
  decide

private def haemers27CPair (t : Fin 15) : Fin 6 × Fin 6 :=
  match t.val with
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (0, 4)
  | 4 => (0, 5)
  | 5 => (1, 2)
  | 6 => (1, 3)
  | 7 => (1, 4)
  | 8 => (1, 5)
  | 9 => (2, 3)
  | 10 => (2, 4)
  | 11 => (2, 5)
  | 12 => (3, 4)
  | 13 => (3, 5)
  | _ => (4, 5)

private def haemers27UInt (i : Fin 27) (k : Fin 7) : ℤ :=
  if hi : i.val < 6 then
    if k.val = i.val then 1 else 0
  else if hi12 : i.val < 12 then
    if k.val < 6 then (if k.val = i.val - 6 then 0 else -1) else 2
  else
    let p := haemers27CPair ⟨i.val - 12, by omega⟩
    if k.val < 6 then (if k.val = p.1.val ∨ k.val = p.2.val then -1 else 0) else 1

private def haemers27VInt (i : Fin 27) (k : Fin 7) : ℤ :=
  if hi : i.val < 6 then
    if k.val = i.val then 1 else 0
  else if hi12 : i.val < 12 then
    if k.val < 6 then (if k.val = i.val - 6 then 0 else -1) else -2
  else
    let p := haemers27CPair ⟨i.val - 12, by omega⟩
    if k.val < 6 then (if k.val = p.1.val ∨ k.val = p.2.val then -1 else 0) else -1

private lemma haemers27_uv_fit_int :
    ∀ i j : Fin 27, (∑ k : Fin 7, haemers27UInt i k * haemers27VInt j k) =
      if i = j then 1 else if haemers27.Adj i j then -1 else 0 := by
  decide

private def haemers27Adj7Int (i j : Fin 7) : ℤ :=
  if i = 0 ∧ j = 0 then -4
  else if i = 0 ∨ j = 0 then 0
  else if i.val < 6 ∧ i = j then -3
  else 1

private lemma haemers27_sub7_adj7_int :
    ∀ i j : Fin 7,
      (∑ m : Fin 7,
        (∑ k : Fin 7, haemers27UInt ⟨i.val, by omega⟩ k * haemers27VInt ⟨m.val, by omega⟩ k) *
          haemers27Adj7Int m j) =
        if i = j then -4 else 0 := by
  decide

/-- Haemers' canonical rank-7 fitting matrix `I - A_H` over an arbitrary field `F`. -/
def haemers27FittingMatrix (F : Type*) [Ring F] : Matrix (Fin 27) (Fin 27) F :=
  Matrix.of fun i j => (∑ k : Fin 7, (haemers27UInt i k : F) * (haemers27VInt j k : F))

theorem haemers27_minrank_le_seven (F : Type*) [Field F] :
    IsFittingMatrix haemers27 (haemers27FittingMatrix F) ∧
      (haemers27FittingMatrix F).rank ≤ 7 ∧
      shannonCapacity haemers27 ≤ 7 := by
  let U : Matrix (Fin 27) (Fin 7) F := Matrix.of fun i k => (haemers27UInt i k : F)
  let V : Matrix (Fin 7) (Fin 27) F := Matrix.of fun k j => (haemers27VInt j k : F)
  have hfact : haemers27FittingMatrix F = U * V := by
    ext i j
    simp [haemers27FittingMatrix, U, V, Matrix.mul_apply]
  have hfit : IsFittingMatrix haemers27 (haemers27FittingMatrix F) :=
    { diag_ne_zero := fun i => by
        have h := congrArg (Int.cast : ℤ → F) (haemers27_uv_fit_int i i)
        simp only [haemers27FittingMatrix, Matrix.of_apply, ↓reduceIte] at h ⊢
        push_cast at h
        rw [h]
        exact one_ne_zero
      nonadj_zero := fun i j hij hnadj => by
        have h := congrArg (Int.cast : ℤ → F) (haemers27_uv_fit_int i j)
        simp only [haemers27FittingMatrix, Matrix.of_apply, hij, hnadj, ↓reduceIte] at h ⊢
        push_cast at h
        exact h }
  have hrank : (haemers27FittingMatrix F).rank ≤ 7 := by
    rw [hfact]
    exact (Matrix.rank_mul_le_left U V).trans (by simpa using Matrix.rank_le_card_width U)
  have hcap : shannonCapacity haemers27 ≤ 7 := by
    have h := shannonCapacity_le_haemers_rank hfit
    exact h.trans (by exact_mod_cast hrank)
  exact ⟨hfit, hrank, hcap⟩

theorem haemers27_canonical_fitting_rank_eq_seven (F : Type*) [Field F] [CharZero F] :
    (haemers27FittingMatrix F).rank = 7 := by
  apply le_antisymm (haemers27_minrank_le_seven F).2.1
  let sub7 : Matrix (Fin 7) (Fin 7) F :=
    (haemers27FittingMatrix F).submatrix (Fin.castLE (by omega)) (Fin.castLE (by omega))
  let inv7 : Matrix (Fin 7) (Fin 7) F :=
    (-4 : F)⁻¹ • Matrix.of fun i j => (haemers27Adj7Int i j : F)
  have hmul : sub7 * inv7 = 1 := by
    ext i j
    have h := congrArg (Int.cast : ℤ → F) (haemers27_sub7_adj7_int i j)
    simp only [sub7, inv7, haemers27FittingMatrix, Matrix.mul_apply, Matrix.submatrix_apply,
      Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply, smul_eq_mul]
    have hsum :
        (∑ m : Fin 7,
          (∑ k : Fin 7, (haemers27UInt ⟨i.val, by omega⟩ k : F) *
            (haemers27VInt ⟨m.val, by omega⟩ k : F)) *
            ((-4 : F)⁻¹ * (haemers27Adj7Int m j : F))) =
          (-4 : F)⁻¹ *
            ∑ m : Fin 7,
              (∑ k : Fin 7, (haemers27UInt ⟨i.val, by omega⟩ k : F) *
                (haemers27VInt ⟨m.val, by omega⟩ k : F)) *
                (haemers27Adj7Int m j : F) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    have hlhs :
        (∑ m : Fin 7,
          (∑ k : Fin 7, (haemers27UInt (Fin.castLE (by omega) i) k : F) *
            (haemers27VInt (Fin.castLE (by omega) m) k : F)) *
            ((-4 : F)⁻¹ * (haemers27Adj7Int m j : F))) =
          ∑ m : Fin 7,
            (∑ k : Fin 7, (haemers27UInt ⟨i.val, by omega⟩ k : F) *
              (haemers27VInt ⟨m.val, by omega⟩ k : F)) *
              ((-4 : F)⁻¹ * (haemers27Adj7Int m j : F)) := rfl
    rw [hlhs, hsum]
    have hcast :
        (∑ m : Fin 7,
          (∑ k : Fin 7, (haemers27UInt ⟨i.val, by omega⟩ k : F) *
            (haemers27VInt ⟨m.val, by omega⟩ k : F)) *
            (haemers27Adj7Int m j : F)) =
          (if i = j then (-4 : F) else 0) := by
      simpa using h
    rw [hcast]
    by_cases hij : i = j
    · subst hij
      have h4 : (-4 : F) ≠ 0 := by norm_num
      rw [if_pos rfl, inv_mul_cancel₀ h4, if_pos rfl]
    · rw [if_neg hij, mul_zero, if_neg hij]
  have hunit : IsUnit sub7 := IsUnit.of_mul_eq_one inv7 hmul
  have hrank_sub : sub7.rank = 7 := by
    rw [Matrix.rank_of_isUnit sub7 hunit, Fintype.card_fin]
  calc 7 = sub7.rank := hrank_sub.symm
    _ ≤ (haemers27FittingMatrix F).rank :=
          Matrix.rank_submatrix_le (haemers27FittingMatrix F) _ _

private lemma posSemidef_of_sq_eq_smul {V : Type*} [Fintype V]
    {M : Matrix V V ℝ} (hSymm : M.IsSymm) {c : ℝ} (hc : 0 < c) (hsq : M * M = c • M) :
    M.PosSemidef := by
  have hHerm : M.IsHermitian := by
    ext i j
    simpa [Matrix.conjTranspose_apply, star_trivial] using congrFun (congrFun hSymm.eq i) j
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun x => ?_
  have hmul : (c : ℝ) * (star x ⬝ᵥ M.mulVec x) = (M.mulVec x) ⬝ᵥ (M.mulVec x) := by
    calc (c : ℝ) * (star x ⬝ᵥ M.mulVec x)
        = star x ⬝ᵥ (c • M).mulVec x := by rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      _ = star x ⬝ᵥ (M * M).mulVec x := by rw [← hsq]
      _ = x ⬝ᵥ M.mulVec (M.mulVec x) := by rw [star_trivial, Matrix.mulVec_mulVec]
      _ = (M.vecMul x) ⬝ᵥ (M.mulVec x) := by rw [Matrix.dotProduct_mulVec]
      _ = ((Matrix.transpose M).mulVec x) ⬝ᵥ (M.mulVec x) := by rw [Matrix.mulVec_transpose]
      _ = (M.mulVec x) ⬝ᵥ (M.mulVec x) := by rw [hSymm.eq]
  have hnonneg : 0 ≤ (M.mulVec x) ⬝ᵥ (M.mulVec x) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hmul_nonneg : 0 ≤ c * (star x ⬝ᵥ M.mulVec x) := hmul ▸ hnonneg
  have hinv : 0 ≤ c⁻¹ * (c * (star x ⬝ᵥ M.mulVec x)) :=
    mul_nonneg (inv_nonneg.mpr hc.le) hmul_nonneg
  rwa [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hinv

private noncomputable def haemers27AdjReal : Matrix (Fin 27) (Fin 27) ℝ :=
  Matrix.of fun i j => if haemers27.Adj i j then 1 else 0

private def allOnes27Real : Matrix (Fin 27) (Fin 27) ℝ :=
  Matrix.of fun _ _ => 1

private lemma haemers27_adj_matrix_sq :
    haemers27AdjReal * haemers27AdjReal =
      (5 : ℝ) • 1 - (4 : ℝ) • haemers27AdjReal + (5 : ℝ) • allOnes27Real := by
  ext i j
  simp only [haemers27AdjReal, allOnes27Real, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul, mul_one]
  have hbit :
      (∑ k : Fin 27, (if haemers27.Adj i k then (1 : ℝ) else 0) *
        (if haemers27.Adj k j then 1 else 0)) =
        (popcount27 (haemers27Mask i &&& haemers27Mask j) : ℝ) := by
    have hsum_eq :
        (∑ k : Fin 27, (if haemers27.Adj i k then (1 : ℝ) else 0) *
          (if haemers27.Adj k j then 1 else 0)) =
          ∑ k : Fin 27, (if (haemers27Mask i).testBit k.val then (1 : ℝ) else 0) *
            (if (haemers27Mask j).testBit k.val then 1 else 0) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hi : haemers27.Adj i k ↔ (haemers27Mask i).testBit k.val = true := Iff.rfl
      have hj : haemers27.Adj k j ↔ (haemers27Mask j).testBit k.val = true :=
        (haemers27.adj_comm k j).trans Iff.rfl
      have hfac1 :
          (if haemers27.Adj i k then (1 : ℝ) else 0) =
            if (haemers27Mask i).testBit k.val then (1 : ℝ) else 0 := by
        by_cases h : haemers27.Adj i k
        · rw [if_pos h, if_pos (hi.mp h)]
        · rw [if_neg h, if_neg (fun h' => h (hi.mpr h'))]
      have hfac2 :
          (if haemers27.Adj k j then (1 : ℝ) else 0) =
            if (haemers27Mask j).testBit k.val then (1 : ℝ) else 0 := by
        by_cases h : haemers27.Adj k j
        · rw [if_pos h, if_pos (hj.mp h)]
        · rw [if_neg h, if_neg (fun h' => h (hj.mpr h'))]
      rw [hfac1, hfac2]
    rw [hsum_eq]
    exact sum_mul_testBit_eq_popcountAux 27 (haemers27Mask i) (haemers27Mask j)
  rw [hbit]
  have hsrg := congrArg (Nat.cast (R := ℝ)) (haemers27_srg_popcount i j)
  push_cast at hsrg
  rw [hsrg]
  by_cases hij : i = j
  · subst hij
    simp
    norm_num
  · by_cases hadj : haemers27.Adj i j
    · simp [hij, hadj]
      norm_num
    · simp [hij, hadj]

private lemma haemers27_adj_mul_allOnes :
    haemers27AdjReal * allOnes27Real = (10 : ℝ) • allOnes27Real ∧
      allOnes27Real * haemers27AdjReal = (10 : ℝ) • allOnes27Real ∧
      allOnes27Real * allOnes27Real = (27 : ℝ) • allOnes27Real := by
  have hrow : ∀ i : Fin 27, ∑ k : Fin 27, (if haemers27.Adj i k then (1 : ℝ) else 0) = 10 := by
    intro i
    have hsum : (∑ k : Fin 27, (if (haemers27Mask i).testBit k.val then (1 : ℝ) else 0) *
        (if (haemers27Mask i).testBit k.val then 1 else 0)) =
        (popcount27 (haemers27Mask i &&& haemers27Mask i) : ℝ) :=
      sum_mul_testBit_eq_popcountAux 27 (haemers27Mask i) (haemers27Mask i)
    have hsq : ∀ k : Fin 27, (if haemers27.Adj i k then (1 : ℝ) else 0) =
        (if (haemers27Mask i).testBit k.val then (1 : ℝ) else 0) *
          (if (haemers27Mask i).testBit k.val then 1 else 0) := fun k => by
      change (if (haemers27Mask i).testBit k.val then (1 : ℝ) else 0) = _
      split_ifs <;> norm_num
    simp_rw [hsq]
    rw [hsum, Nat.and_self, haemers27_deg_eq_ten i]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp [haemers27AdjReal, allOnes27Real, Matrix.mul_apply, hrow i]
  · ext i j
    simp only [haemers27AdjReal, allOnes27Real, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul, one_mul, mul_one]
    have hcomm : ∀ k : Fin 27, haemers27.Adj k j ↔ haemers27.Adj j k := fun k => haemers27.adj_comm k j
    simp_rw [hcomm]
    exact hrow j
  · ext i j
    simp [allOnes27Real, Matrix.mul_apply]

theorem haemers27_lovaszTheta_eq_nine : lovaszTheta haemers27 = 9 := by
  have hAsymm : haemers27AdjReal.IsSymm := Matrix.IsSymm.ext fun i j => by
    simp [haemers27AdjReal, haemers27.adj_comm]
  have hJsymm : allOnes27Real.IsSymm := Matrix.IsSymm.ext fun _ _ => rfl
  have hA2 := haemers27_adj_matrix_sq
  obtain ⟨hAJ, hJA, hJ2⟩ := haemers27_adj_mul_allOnes
  apply le_antisymm
  · let M : Matrix (Fin 27) (Fin 27) ℝ :=
      1 + (1 / 5 : ℝ) • haemers27AdjReal - (1 / 9 : ℝ) • allOnes27Real
    have hMsymm : M.IsSymm :=
      ((Matrix.isSymm_one).add (hAsymm.smul (1 / 5 : ℝ))).sub (hJsymm.smul (1 / 9 : ℝ))
    have hMsq : M * M = (6 / 5 : ℝ) • M := by
      dsimp only [M]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
        Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hA2, hAJ, hJA, hJ2]
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul]
      ring
    have hMpsd : M.PosSemidef := posSemidef_of_sq_eq_smul hMsymm (by norm_num) hMsq
    let cert : LovaszCert haemers27 (1 / 9) :=
      { W := 1 + (1 / 5 : ℝ) • haemers27AdjReal
        hβ := by norm_num
        symm := (Matrix.isSymm_one).add (hAsymm.smul (1 / 5 : ℝ))
        diag_le_one := fun i => by
          simp [haemers27AdjReal]
        nonadj_zero := fun i j hij hnadj => by
          simp [haemers27AdjReal, hij, hnadj]
        psd := hMpsd }
    have hle := lovaszTheta_le_of_cert cert
    norm_num at hle
    exact hle
  · let P0 : Matrix (Fin 27) (Fin 27) ℝ := (1 / 27 : ℝ) • allOnes27Real
    let Pm5 : Matrix (Fin 27) (Fin 27) ℝ :=
      (1 / 6 : ℝ) • (1 - haemers27AdjReal + (1 / 3 : ℝ) • allOnes27Real)
    have hPm5_symm : Pm5.IsSymm :=
      (((Matrix.isSymm_one).sub hAsymm).add (hJsymm.smul (1 / 3 : ℝ))).smul (1 / 6 : ℝ)
    have hPm5_sq : Pm5 * Pm5 = (1 : ℝ) • Pm5 := by
      dsimp only [Pm5]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
        Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hA2, hAJ, hJA, hJ2]
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul]
      ring
    have hPm5_psd : Pm5.PosSemidef := posSemidef_of_sq_eq_smul hPm5_symm one_pos hPm5_sq
    have hP0_psd : P0.PosSemidef := (posSemidef_allOnes (Fin 27)).smul (by norm_num)
    let X : Matrix (Fin 27) (Fin 27) ℝ := (1 / 3 : ℝ) • P0 + (1 / 9 : ℝ) • Pm5
    have hX_eq : X = (1 / 54 : ℝ) • (1 - haemers27AdjReal + allOnes27Real) := by
      ext i j
      simp only [X, P0, Pm5, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, Matrix.of_apply, allOnes27Real, smul_eq_mul]
      ring
    have hX_psd : X.PosSemidef := (hP0_psd.smul (by norm_num)).add (hPm5_psd.smul (by norm_num))
    have hX_tr : X.trace = 1 := by
      rw [hX_eq]
      simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
        Matrix.one_apply, Matrix.of_apply, haemers27AdjReal, allOnes27Real, smul_eq_mul]
      simp
      norm_num
    have hX_adj : ∀ i j : Fin 27, haemers27.Adj i j → X i j = 0 := by
      intro i j hadj
      rw [hX_eq]
      simp [haemers27AdjReal, allOnes27Real, hadj.ne, hadj]
    have hX_sum : ∑ i : Fin 27, ∑ j : Fin 27, X i j = 9 := by
      rw [hX_eq]
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.of_apply, haemers27AdjReal, allOnes27Real, smul_eq_mul, ← Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hsumI : (∑ i : Fin 27, ∑ j : Fin 27, (if i = j then (1 : ℝ) else 0)) = 27 := by
        simp
      have hsumJ : (∑ _i : Fin 27, ∑ _j : Fin 27, (1 : ℝ)) = 729 := by
        simp [Finset.sum_const]
        norm_num
      have hsumA : (∑ i : Fin 27, ∑ j : Fin 27, (if haemers27.Adj i j then (1 : ℝ) else 0)) = 270 := by
        have hrow : ∀ i : Fin 27, ∑ j : Fin 27, (if haemers27.Adj i j then (1 : ℝ) else 0) = 10 := by
          intro i
          have h := congrArg (fun M : Matrix (Fin 27) (Fin 27) ℝ => M i 0) hAJ
          simpa [haemers27AdjReal, allOnes27Real, Matrix.mul_apply] using h
        simp_rw [hrow]
        simp
        norm_num
      rw [hsumI, hsumA, hsumJ]
      norm_num
    exact hX_sum ▸ le_lovaszTheta_of_primal X hX_psd hX_tr hX_adj

theorem haemers27_haemers_beats_lovasz :
    (6 : ℝ) ≤ (haemers27.indepNum : ℝ) ∧
      (haemers27.indepNum : ℝ) ≤ shannonCapacity haemers27 ∧
      shannonCapacity haemers27 ≤ 7 ∧
      (7 : ℝ) < lovaszTheta haemers27 := by
  have h6 : 6 ≤ haemers27.indepNum :=
    length_le_indepNum_of_list (l := ([0, 1, 2, 3, 4, 5] : List (Fin 27))) (by decide) (by decide)
  have hcap_ge : (haemers27.indepNum : ℝ) ≤ shannonCapacity haemers27 := by
    obtain ⟨S, hS_indep, hS_card⟩ := haemers27.exists_isNIndepSet_indepNum
    have hiso : haemers27 ≃g strongPow haemers27 1 := strongProdPUnitRight haemers27
    have hlow := le_shannonCapacity_of_indepSet haemers27 Nat.one_pos
      (isIndepSet_map_iso hiso hS_indep)
    simpa [hS_card] using hlow
  refine ⟨by exact_mod_cast h6, hcap_ge, (haemers27_minrank_le_seven ℚ).2.2, ?_⟩
  rw [haemers27_lovaszTheta_eq_nine]
  norm_num

theorem schlafli27_exact :
    schlafli27.indepNum = 3 ∧
      shannonCapacity schlafli27 = 3 ∧
      lovaszTheta schlafli27 = 3 := by
  have hAsymm : haemers27AdjReal.IsSymm := Matrix.IsSymm.ext fun i j => by
    simp [haemers27AdjReal, haemers27.adj_comm]
  have hJsymm : allOnes27Real.IsSymm := Matrix.IsSymm.ext fun _ _ => rfl
  have hA2 := haemers27_adj_matrix_sq
  obtain ⟨hAJ, hJA, hJ2⟩ := haemers27_adj_mul_allOnes
  let AS : Matrix (Fin 27) (Fin 27) ℝ := allOnes27Real - 1 - haemers27AdjReal
  let MS : Matrix (Fin 27) (Fin 27) ℝ := 1 + (1 / 2 : ℝ) • AS - (1 / 3 : ℝ) • allOnes27Real
  have hMS_eq : MS = (1 / 2 : ℝ) • (1 - haemers27AdjReal + (1 / 3 : ℝ) • allOnes27Real) := by
    ext i j
    simp only [MS, AS, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    ring
  have hMS_symm : MS.IsSymm := by
    rw [hMS_eq]
    exact (((Matrix.isSymm_one).sub hAsymm).add (hJsymm.smul (1 / 3 : ℝ))).smul (1 / 2 : ℝ)
  have hMS_sq : MS * MS = (3 : ℝ) • MS := by
    rw [hMS_eq]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hA2, hAJ, hJA, hJ2]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    ring
  have hMS_psd : MS.PosSemidef := posSemidef_of_sq_eq_smul hMS_symm (by norm_num) hMS_sq
  let cert : LovaszCert schlafli27 (1 / 3) :=
    { W := 1 + (1 / 2 : ℝ) • AS
      hβ := by norm_num
      symm := (Matrix.isSymm_one).add (((hJsymm.sub Matrix.isSymm_one).sub hAsymm).smul (1 / 2 : ℝ))
      diag_le_one := fun i => by
        simp [AS, haemers27AdjReal, allOnes27Real]
      nonadj_zero := fun i j hij hnadj => by
        have hadjH : haemers27.Adj i j := by
          by_contra hnot
          exact hnadj ⟨hij, hnot⟩
        simp [AS, haemers27AdjReal, allOnes27Real, hij, hadjH]
      psd := hMS_psd }
  have hge3 : 3 ≤ schlafli27.indepNum :=
    length_le_indepNum_of_list (l := ([0, 7, 12] : List (Fin 27))) (by decide) (by decide)
  have hlov_le : lovaszTheta schlafli27 ≤ 3 := by
    have h := lovaszTheta_le_of_cert cert
    norm_num at h
    exact h
  have hcap_le : shannonCapacity schlafli27 ≤ 3 := by
    have h := shannonCapacity_le_of_cert cert
    norm_num at h
    exact h
  have hcap_ge : (3 : ℝ) ≤ shannonCapacity schlafli27 := by
    have hiso : schlafli27 ≃g strongPow schlafli27 1 := strongProdPUnitRight schlafli27
    obtain ⟨S, hS_indep, hS_card⟩ := schlafli27.exists_isNIndepSet_indepNum
    have hlow := le_shannonCapacity_of_indepSet schlafli27 Nat.one_pos
      (isIndepSet_map_iso hiso hS_indep)
    have h3 : (3 : ℝ) ≤ ((S.map hiso.toEquiv.toEmbedding).card : ℝ) ^ (1 / ((1 : ℕ) : ℝ)) := by
      simp only [Finset.card_map, Nat.cast_one, div_one, Real.rpow_one]
      exact_mod_cast hS_card.symm ▸ hge3
    exact h3.trans hlow
  have hlov_ge : (3 : ℝ) ≤ lovaszTheta schlafli27 :=
    (by exact_mod_cast hge3 : (3 : ℝ) ≤ (schlafli27.indepNum : ℝ)).trans
      (indepNum_le_lovaszTheta schlafli27)
  have hind_le : schlafli27.indepNum ≤ 3 := by
    have h := (indepNum_le_lovaszTheta schlafli27).trans hlov_le
    exact_mod_cast h
  exact ⟨le_antisymm hind_le hge3, le_antisymm hcap_le hcap_ge, le_antisymm hlov_le hlov_ge⟩

theorem haemers27_schlafli27_gate_g3 :
    shannonCapacity haemers27 * shannonCapacity schlafli27 ≤ 21 ∧
      (21 : ℝ) < lovaszTheta haemers27 * lovaszTheta schlafli27 := by
  have h1 := haemers27_haemers_beats_lovasz.2.2.1
  have h2 := schlafli27_exact.2.1
  have h3 := haemers27_lovaszTheta_eq_nine
  have h4 := schlafli27_exact.2.2
  refine ⟨?_, ?_⟩
  · nlinarith [shannonCapacity_nonneg haemers27, shannonCapacity_nonneg schlafli27]
  · rw [h3, h4]
    norm_num

/-! ## Part 3D: Bukh–Cox Fractional Haemers Bound (`C_{2k+1}` & `C₇`) -/

/-- A fractional Haemers `(s, d)`-representation of `G` over a field `F`. -/
structure FracHaemersRep {V : Type*} (G : SimpleGraph V) (F : Type*) [Field F] (s d : ℕ) where
  hs : 0 < s
  A : V → Matrix (Fin s) (Fin d) F
  B : V → Matrix (Fin d) (Fin s) F
  diag_unit : ∀ v, IsUnit (A v * B v)
  nonadj_zero : ∀ u v, u ≠ v → ¬ G.Adj u v → A u * B v = 0

/-- The fractional Haemers number `ℋ_f^F(G) = inf { d / s | ∃ FracHaemersRep G F s d }`. -/
noncomputable def fracHaemers {V : Type*} [Fintype V] (F : Type*) [Field F]
    (G : SimpleGraph V) : ℝ :=
  sInf {q : ℝ | ∃ s d, ∃ _ : FracHaemersRep G F s d, q = (d : ℝ) / (s : ℝ)}

private def fracHaemersSub {V : Type*} {G : SimpleGraph V} {F : Type*} [Field F] {s d : ℕ}
    (rep : FracHaemersRep G F s d) (v : V) : Submodule F (Fin d → F) :=
  LinearMap.range (rep.B v).mulVecLin

private lemma fracHaemersSub_inj {V : Type*} {G : SimpleGraph V} {F : Type*} [Field F] {s d : ℕ}
    (rep : FracHaemersRep G F s d) (v : V) :
    Function.Injective (rep.B v).mulVecLin := by
  rcases rep.diag_unit v with ⟨U, hU⟩
  intro x y hxy
  let Uinv : Matrix (Fin s) (Fin s) F := ↑(U⁻¹)
  have hinv : (Uinv * rep.A v) * rep.B v = 1 := by
    rw [Matrix.mul_assoc, ← hU]
    exact Units.inv_mul U
  have h1 := congrArg (fun z => (Uinv * rep.A v).mulVec z) hxy
  change (Uinv * rep.A v).mulVec ((rep.B v).mulVec x) =
      (Uinv * rep.A v).mulVec ((rep.B v).mulVec y) at h1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.one_mulVec] at h1
  exact h1

private lemma fracHaemersSub_finrank {V : Type*} {G : SimpleGraph V} {F : Type*} [Field F] {s d : ℕ}
    (rep : FracHaemersRep G F s d) (v : V) :
    Module.finrank F (fracHaemersSub rep v) = s := by
  rw [fracHaemersSub, LinearMap.finrank_range_of_inj (fracHaemersSub_inj rep v),
    Module.finrank_fin_fun]

private lemma fracHaemers_mulVec_eq_zero_of_mem_sub {V : Type*} {G : SimpleGraph V}
    {F : Type*} [Field F] {s d : ℕ} (rep : FracHaemersRep G F s d)
    {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v) {x : Fin d → F}
    (hx : x ∈ fracHaemersSub rep v) :
    (rep.A u).mulVec x = 0 := by
  rcases hx with ⟨y, rfl⟩
  change (rep.A u).mulVec ((rep.B v).mulVec y) = 0
  rw [Matrix.mulVec_mulVec, rep.nonadj_zero u v huv hnadj, Matrix.zero_mulVec]

private lemma fracHaemers_eq_zero_of_mulVec_zero {V : Type*} {G : SimpleGraph V}
    {F : Type*} [Field F] {s d : ℕ} (rep : FracHaemersRep G F s d)
    {v : V} {x : Fin d → F} (hx : x ∈ fracHaemersSub rep v) (hAx : (rep.A v).mulVec x = 0) :
    x = 0 := by
  rcases hx with ⟨y, rfl⟩
  rcases rep.diag_unit v with ⟨U, hU⟩
  let Uinv : Matrix (Fin s) (Fin s) F := ↑(U⁻¹)
  have hABy : (rep.A v * rep.B v).mulVec y = 0 := by
    rw [← Matrix.mulVec_mulVec]
    exact hAx
  have hy : y = 0 := by
    have h1 := congrArg (fun z => Uinv.mulVec z) hABy
    rw [Matrix.mulVec_mulVec, ← hU, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    exact h1
  rw [hy]
  simp

private lemma fracHaemers_sup_finrank_of_indepSet {V : Type*} {G : SimpleGraph V}
    {F : Type*} [Field F] {s d : ℕ} (rep : FracHaemersRep G F s d)
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    Module.finrank F (⨆ (v : V) (_ : v ∈ S), fracHaemersSub rep v : Submodule F (Fin d → F)) =
      S.card * s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | insert a S ha ih =>
      have hS_sub : G.IsIndepSet (S : Set V) := fun u hu v hv huv =>
        hS (Finset.mem_insert_of_mem hu) (Finset.mem_insert_of_mem hv) huv
      have hdisj :
          fracHaemersSub rep a ⊓
            (⨆ (v : V) (_ : v ∈ S), fracHaemersSub rep v : Submodule F (Fin d → F)) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rcases hx with ⟨hxa, hxS⟩
        have hAx : (rep.A a).mulVec x = 0 := by
          have hle :
              (⨆ (v : V) (_ : v ∈ S), fracHaemersSub rep v : Submodule F (Fin d → F)) ≤
                LinearMap.ker (rep.A a).mulVecLin := by
            refine iSup₂_le fun v hv => ?_
            intro z hz
            have hav : a ≠ v := fun h => ha (h ▸ hv)
            have hnadj : ¬ G.Adj a v := hS (Finset.mem_insert_self a S)
              (Finset.mem_insert_of_mem hv) hav
            exact fracHaemers_mulVec_eq_zero_of_mem_sub rep hav hnadj hz
          exact hle hxS
        rw [Submodule.mem_bot]
        exact fracHaemers_eq_zero_of_mulVec_zero rep hxa hAx
      have hsup :
          (⨆ (v : V) (_ : v ∈ insert a S), fracHaemersSub rep v : Submodule F (Fin d → F)) =
            fracHaemersSub rep a ⊔
              (⨆ (v : V) (_ : v ∈ S), fracHaemersSub rep v : Submodule F (Fin d → F)) := by
        simp only [Finset.mem_insert, iSup_or, iSup_sup_eq]
        congr 1
        simp only [iSup_iSup_eq_left]
      rw [hsup]
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq
        (fracHaemersSub rep a)
        (⨆ (v : V) (_ : v ∈ S), fracHaemersSub rep v : Submodule F (Fin d → F))
      rw [hdisj, finrank_bot, add_zero, fracHaemersSub_finrank, ih hS_sub] at hdim
      rw [hdim, Finset.card_insert_of_notMem ha]
      ring

theorem indepNum_mul_le_of_fracHaemersRep {V : Type*} [Fintype V] {G : SimpleGraph V}
    {F : Type*} [Field F] {s d : ℕ} (rep : FracHaemersRep G F s d) :
    G.indepNum * s ≤ d := by
  obtain ⟨S, hS_indep, hS_card⟩ := G.exists_isNIndepSet_indepNum
  rw [← hS_card, ← fracHaemers_sup_finrank_of_indepSet rep hS_indep]
  calc Module.finrank F
          (⨆ (v : V) (_ : v ∈ S), fracHaemersSub rep v : Submodule F (Fin d → F))
      ≤ Module.finrank F (Fin d → F) := Submodule.finrank_le _
    _ = d := Module.finrank_fin_fun F

private lemma matrix_reindex_mul {m n p m' n' p' R : Type*}
    [Fintype n] [Fintype n'] [NonUnitalNonAssocSemiring R]
    (em : m ≃ m') (en : n ≃ n') (ep : p ≃ p')
    (A : Matrix m n R) (B : Matrix n p R) :
    Matrix.reindex em en A * Matrix.reindex en ep B = Matrix.reindex em ep (A * B) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Fintype.sum_equiv en.symm _ _ fun j => by simp

private def FracHaemersRep.unit.{u} (F : Type*) [Field F] :
    FracHaemersRep (⊥ : SimpleGraph PUnit.{u + 1}) F 1 1 where
  hs := Nat.one_pos
  A _ := 1
  B _ := 1
  diag_unit _ := by simp
  nonadj_zero u v huv _ := absurd (Subsingleton.elim u v) huv

private def FracHaemersRep.prod {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {F : Type*} [Field F] {s₁ d₁ s₂ d₂ : ℕ}
    (r₁ : FracHaemersRep G F s₁ d₁) (r₂ : FracHaemersRep H F s₂ d₂) :
    FracHaemersRep (G ⊠ H) F (s₁ * s₂) (d₁ * d₂) where
  hs := Nat.mul_pos r₁.hs r₂.hs
  A p := Matrix.reindex finProdFinEquiv finProdFinEquiv (r₁.A p.1 ⊗ₖ r₂.A p.2)
  B p := Matrix.reindex finProdFinEquiv finProdFinEquiv (r₁.B p.1 ⊗ₖ r₂.B p.2)
  diag_unit p := by
    rcases r₁.diag_unit p.1 with ⟨U₁, hU₁⟩
    rcases r₂.diag_unit p.2 with ⟨U₂, hU₂⟩
    rw [matrix_reindex_mul, ← Matrix.mul_kronecker_mul, ← hU₁, ← hU₂]
    let invM : Matrix (Fin (s₁ * s₂)) (Fin (s₁ * s₂)) F :=
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((↑(U₁⁻¹) : Matrix (Fin s₁) (Fin s₁) F) ⊗ₖ (↑(U₂⁻¹) : Matrix (Fin s₂) (Fin s₂) F))
    refine ⟨⟨Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((↑U₁ : Matrix (Fin s₁) (Fin s₁) F) ⊗ₖ (↑U₂ : Matrix (Fin s₂) (Fin s₂) F)),
      invM, ?_, ?_⟩, rfl⟩
    · dsimp only [invM]
      rw [matrix_reindex_mul, ← Matrix.mul_kronecker_mul, Units.mul_inv, Units.mul_inv,
        Matrix.one_kronecker_one]
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
        Equiv.apply_eq_iff_eq]
    · dsimp only [invM]
      rw [matrix_reindex_mul, ← Matrix.mul_kronecker_mul, Units.inv_mul, Units.inv_mul,
        Matrix.one_kronecker_one]
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
        Equiv.apply_eq_iff_eq]
  nonadj_zero := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ hne hnadj
    have hnot : ¬ ((u₁, v₁) = (u₂, v₂) ∨ (G ⊠ H).Adj (u₁, v₁) (u₂, v₂)) :=
      not_or.mpr ⟨hne, hnadj⟩
    rw [eq_or_strongProd_adj] at hnot
    rw [matrix_reindex_mul, ← Matrix.mul_kronecker_mul]
    rcases not_and_or.mp hnot with hu | hv
    · rcases not_or.mp hu with ⟨hune, hunadj⟩
      rw [r₁.nonadj_zero u₁ u₂ hune hunadj, Matrix.zero_kronecker]
      ext i j; simp
    · rcases not_or.mp hv with ⟨hvne, hvnadj⟩
      rw [r₂.nonadj_zero v₁ v₂ hvne hvnadj, Matrix.kronecker_zero]
      ext i j; simp

private def FracHaemersRep.reidx {V : Type*} {G : SimpleGraph V} {F : Type*} [Field F]
    {s₁ d₁ s₂ d₂ : ℕ} (hs : s₁ = s₂) (hd : d₁ = d₂) (r : FracHaemersRep G F s₁ d₁) :
    FracHaemersRep G F s₂ d₂ where
  hs := hs ▸ r.hs
  A v := Matrix.reindex (finCongr hs) (finCongr hd) (r.A v)
  B v := Matrix.reindex (finCongr hd) (finCongr hs) (r.B v)
  diag_unit v := by
    rcases r.diag_unit v with ⟨U, hU⟩
    rw [matrix_reindex_mul, ← hU]
    let invM : Matrix (Fin s₂) (Fin s₂) F :=
      Matrix.reindex (finCongr hs) (finCongr hs) (↑(U⁻¹) : Matrix (Fin s₁) (Fin s₁) F)
    refine ⟨⟨Matrix.reindex (finCongr hs) (finCongr hs) (↑U : Matrix (Fin s₁) (Fin s₁) F),
      invM, ?_, ?_⟩, rfl⟩
    · dsimp only [invM]
      rw [matrix_reindex_mul, Units.mul_inv]
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
        Equiv.apply_eq_iff_eq]
    · dsimp only [invM]
      rw [matrix_reindex_mul, Units.inv_mul]
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
        Equiv.apply_eq_iff_eq]
  nonadj_zero u v huv hnadj := by
    rw [matrix_reindex_mul, r.nonadj_zero u v huv hnadj]
    ext i j; simp

private def FracHaemersRep.pow.{u} {V : Type u} {G : SimpleGraph V} {F : Type*} [Field F] {s d : ℕ}
    (rep : FracHaemersRep G F s d) : (m : ℕ) → FracHaemersRep (strongPow G m) F (s ^ m) (d ^ m)
  | 0 => FracHaemersRep.unit.{u} F
  | m + 1 => (rep.prod (rep.pow m)).reidx (pow_succ' s m).symm (pow_succ' d m).symm

private lemma fracHaemers_set_nonempty {V : Type*} [Fintype V] (F : Type*) [Field F]
    (G : SimpleGraph V) :
    {q : ℝ | ∃ s d, ∃ _ : FracHaemersRep G F s d, q = (d : ℝ) / (s : ℝ)}.Nonempty := by
  classical
  let n : ℕ := Fintype.card V
  let e : V ≃ Fin n := Fintype.equivFin V
  let rep : FracHaemersRep G F 1 n :=
    { hs := Nat.one_pos
      A := fun v => Matrix.of fun _ j => if j = e v then (1 : F) else 0
      B := fun v => Matrix.of fun j _ => if j = e v then (1 : F) else 0
      diag_unit := fun v => by
        have h1 : (Matrix.of (fun (_ : Fin 1) j => if j = e v then (1 : F) else 0) *
            Matrix.of (fun j (_ : Fin 1) => if j = e v then (1 : F) else 0)) = 1 := by
          ext i j
          simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim i 0, Subsingleton.elim j 0]
        rw [h1]
        exact isUnit_one
      nonadj_zero := fun u v huv _ => by
        ext i j
        have hne : e u ≠ e v := e.injective.ne huv
        simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k = e u
        · subst hk; simp [hne]
        · simp [hk] }
  exact ⟨(n : ℝ) / ((1 : ℕ) : ℝ), 1, n, rep, rfl⟩

private lemma fracHaemers_set_bddBelow {V : Type*} [Fintype V] (F : Type*) [Field F]
    (G : SimpleGraph V) :
    BddBelow {q : ℝ | ∃ s d, ∃ _ : FracHaemersRep G F s d, q = (d : ℝ) / (s : ℝ)} := by
  refine ⟨0, ?_⟩
  rintro q ⟨s, d, _, rfl⟩
  positivity

theorem shannonCapacity_le_fracHaemers {V : Type*} [Fintype V] (F : Type*) [Field F]
    (G : SimpleGraph V) :
    shannonCapacity G ≤ fracHaemers F G := by
  apply le_csInf (fracHaemers_set_nonempty F G)
  rintro q ⟨s, d, rep, rfl⟩
  have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr rep.hs
  refine shannonCapacity_le G (by positivity) fun m _ => ?_
  have hmul := indepNum_mul_le_of_fracHaemersRep (rep.pow m)
  have hmul_real : ((strongPow G m).indepNum : ℝ) * (s : ℝ) ^ m ≤ (d : ℝ) ^ m := by
    exact_mod_cast hmul
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos hs_pos m)).mpr hmul_real

theorem fracHaemers_le_rank_of_fitting {V : Type*} [Fintype V] {F : Type*} [Field F]
    {G : SimpleGraph V} {M : Matrix V V F} (hM : IsFittingMatrix G M) :
    fracHaemers F G ≤ (M.rank : ℝ) := by
  obtain ⟨L, R, hLR⟩ := exists_mul_eq_of_rank M
  let rep : FracHaemersRep G F 1 M.rank :=
    { hs := Nat.one_pos
      A := fun u => L.submatrix (fun _ : Fin 1 => u) id
      B := fun v => R.submatrix id (fun _ : Fin 1 => v)
      diag_unit := fun v => by
        have hM_entry : (L * R) v v = M v v := by rw [hLR]
        have hdiag : (L.submatrix (fun _ : Fin 1 => v) id *
            R.submatrix id (fun _ : Fin 1 => v)) = Matrix.of fun _ _ => M v v := by
          ext i j
          rw [← hM_entry]
          simp [Matrix.mul_apply]
        let invM : Matrix (Fin 1) (Fin 1) F := Matrix.of fun _ _ => (M v v)⁻¹
        have hne : M v v ≠ 0 := hM.diag_ne_zero v
        rw [hdiag]
        refine ⟨⟨Matrix.of fun _ _ => M v v, invM, ?_, ?_⟩, rfl⟩
        · ext i j
          simp [invM, Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim i 0,
            Subsingleton.elim j 0, mul_inv_cancel₀ hne]
        · ext i j
          simp [invM, Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim i 0,
            Subsingleton.elim j 0, inv_mul_cancel₀ hne]
      nonadj_zero := fun u v huv hnadj => by
        ext i j
        have h0 : (L * R) u v = 0 := by rw [hLR]; exact hM.nonadj_zero u v huv hnadj
        simpa [Matrix.mul_apply] using h0 }
  have hmem : ((M.rank : ℝ) / ((1 : ℕ) : ℝ)) ∈
      {q : ℝ | ∃ s d, ∃ _ : FracHaemersRep G F s d, q = (d : ℝ) / (s : ℝ)} :=
    ⟨1, M.rank, rep, rfl⟩
  have hle : fracHaemers F G ≤ (M.rank : ℝ) / ((1 : ℕ) : ℝ) :=
    csInf_le (fracHaemers_set_bddBelow F G) hmem
  simpa using hle

private lemma not_cycleGraph_adj_of_val_diff' {n : ℕ} (hn : 3 ≤ n) (a b : Fin n) {δ : ℕ}
    (hδ_lo : 2 ≤ δ) (hδ_hi : δ ≤ n - 2)
    (hdiff : (a.val : ℤ) - (b.val : ℤ) ≡ (δ : ℤ) [ZMOD n] ∨
             (b.val : ℤ) - (a.val : ℤ) ≡ (δ : ℤ) [ZMOD n]) :
    ¬ (a = b ∨ (SimpleGraph.cycleGraph n).Adj a b) := by
  have hsub : ∀ x y : Fin n, (x.val : ℤ) - (y.val : ℤ) ≡ (δ : ℤ) [ZMOD n] →
      x ≠ y ∧ ¬ (SimpleGraph.cycleGraph n).Adj x y := by
    intro x y hmod
    have hx : x.val < n := x.isLt
    have hy : y.val < n := y.isLt
    have hne : x ≠ y := by
      intro h; subst h; rw [sub_self] at hmod
      have hdvd : (n : ℤ) ∣ (δ : ℤ) := by
        rw [Int.ModEq, Int.zero_emod] at hmod; exact Int.dvd_of_emod_eq_zero hmod.symm
      have := Int.le_of_dvd (by omega) hdvd; omega
    refine ⟨hne, ?_⟩
    rw [SimpleGraph.cycleGraph_adj']
    rintro (h1 | h1)
    · have hxy_mod : (x.val : ℤ) - (y.val : ℤ) ≡ (1 : ℤ) [ZMOD n] := by
        by_cases hle : y ≤ x
        · have hcoe : (x - y).val = x.val - y.val := Fin.coe_sub_iff_le.mpr hle
          have : (x.val : ℤ) - (y.val : ℤ) = 1 := by omega
          rw [this]
        · have hlt : x < y := lt_of_not_ge hle
          have hcoe : (x - y).val = n + x.val - y.val := Fin.coe_sub_iff_lt.mpr hlt
          have hzx : (x.val : ℤ) - (y.val : ℤ) = 1 - (n : ℤ) := by omega
          rw [hzx, Int.modEq_iff_dvd]; exact ⟨1, by ring⟩
      have hdvd := (Int.modEq_iff_dvd).mp (hxy_mod.symm.trans hmod)
      have := Int.le_of_dvd (by omega) hdvd; omega
    · have hyx_mod : (y.val : ℤ) - (x.val : ℤ) ≡ (1 : ℤ) [ZMOD n] := by
        by_cases hle : x ≤ y
        · have hcoe : (y - x).val = y.val - x.val := Fin.coe_sub_iff_le.mpr hle
          have : (y.val : ℤ) - (x.val : ℤ) = 1 := by omega
          rw [this]
        · have hlt : y < x := lt_of_not_ge hle
          have hcoe : (y - x).val = n + y.val - x.val := Fin.coe_sub_iff_lt.mpr hlt
          have hzy : (y.val : ℤ) - (x.val : ℤ) = 1 - (n : ℤ) := by omega
          rw [hzy, Int.modEq_iff_dvd]; exact ⟨1, by ring⟩
      have hneg : (x.val : ℤ) - (y.val : ℤ) ≡ (-1 : ℤ) [ZMOD n] := by
        simpa using hyx_mod.neg
      have hdvd := (Int.modEq_iff_dvd).mp (hneg.symm.trans hmod)
      have : (n : ℤ) ∣ ((δ : ℤ) + 1) := by
        have heq : (δ : ℤ) - (-1 : ℤ) = (δ : ℤ) + 1 := by ring
        simpa [heq] using hdvd
      have := Int.le_of_dvd (by omega) this; omega
  rcases hdiff with h | h
  · rcases hsub a b h with ⟨hne, hadj⟩; exact not_or.mpr ⟨hne, hadj⟩
  · rcases hsub b a h with ⟨hne, hadj⟩; exact not_or.mpr ⟨hne.symm, fun ha => hadj ha.symm⟩

theorem fracHaemers_oddCycle (F : Type*) [Field F] {k : ℕ} (hk : 2 ≤ k) :
    fracHaemers F (SimpleGraph.cycleGraph (2 * k + 1)) = (2 * k + 1 : ℝ) / 2 := by
  let n : ℕ := 2 * k + 1
  have hn5 : 5 ≤ n := by omega
  apply le_antisymm
  · letI : NeZero n := ⟨by omega⟩
    let rep : FracHaemersRep (SimpleGraph.cycleGraph n) F 2 n :=
      { hs := by norm_num
        A := fun i => Matrix.of fun (a : Fin 2) (j : Fin n) =>
          if (a = 0 ∧ j = i - 1) ∨ (a = 1 ∧ j = i) then (1 : F) else 0
        B := fun i => Matrix.of fun (j : Fin n) (b : Fin 2) =>
          if (b = 0 ∧ j = i - 1) ∨ (b = 1 ∧ j = i) then (1 : F) else 0
        diag_unit := fun i => by
          have hne : i - 1 ≠ i := by
            intro h
            have h1 : (1 : Fin n) = 0 := by
              have : i - (i - 1) = i - i := congrArg (fun z => i - z) h
              simpa using this
            have hval : ((1 : Fin n)).val = 0 := by rw [h1]; rfl
            have hval1 : ((1 : Fin n)).val = 1 % n := rfl
            rw [Nat.mod_eq_of_lt (by omega)] at hval1
            omega
          have hprod :
              (Matrix.of (fun (a : Fin 2) (j : Fin n) =>
                if (a = 0 ∧ j = i - 1) ∨ (a = 1 ∧ j = i) then (1 : F) else 0) *
                Matrix.of (fun (j : Fin n) (b : Fin 2) =>
                  if (b = 0 ∧ j = i - 1) ∨ (b = 1 ∧ j = i) then (1 : F) else 0)) = 1 := by
            ext (a : Fin 2) (b : Fin 2)
            fin_cases a <;> fin_cases b
            · simp [Matrix.mul_apply]
            · simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
              norm_num
              exact hne.symm
            · simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
              norm_num
              omega
            · simp [Matrix.mul_apply]
          rw [hprod]
          exact isUnit_one
        nonadj_zero := fun u v huv hnadj => by
          have hnot1 : u - 1 ≠ v := by
            intro h
            apply hnadj
            rw [SimpleGraph.cycleGraph_adj']
            left
            rw [← h, sub_sub_cancel]
            change 1 % n = 1
            exact Nat.mod_eq_of_lt (by omega)
          have hnot2 : v - 1 ≠ u := by
            intro h
            apply hnadj
            rw [SimpleGraph.cycleGraph_adj']
            right
            rw [← h, sub_sub_cancel]
            change 1 % n = 1
            exact Nat.mod_eq_of_lt (by omega)
          have hnot3 : u - 1 ≠ v - 1 := fun h => huv (by
            calc u = u - 1 + 1 := (sub_add_cancel u 1).symm
              _ = v - 1 + 1 := congrArg (· + 1) h
              _ = v := sub_add_cancel v 1)
          ext (a : Fin 2) (b : Fin 2)
          fin_cases a <;> fin_cases b <;>
            simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
          · exact Finset.sum_eq_zero fun j _ => by by_cases hj : j = u - 1 <;> simp [hj, hnot3]
          · exact Finset.sum_eq_zero fun j _ => by by_cases hj : j = u - 1 <;> simp [hj, hnot1]
          · exact Finset.sum_eq_zero fun j _ => by by_cases hj : j = u <;> simp [hj, hnot2.symm]
          · exact Finset.sum_eq_zero fun j _ => by by_cases hj : j = u <;> simp [hj, huv] }
    have hmem : ((n : ℝ) / ((2 : ℕ) : ℝ)) ∈
        {q : ℝ | ∃ s d, ∃ _ : FracHaemersRep (SimpleGraph.cycleGraph n) F s d,
          q = (d : ℝ) / (s : ℝ)} :=
      ⟨2, n, rep, rfl⟩
    have hle : fracHaemers F (SimpleGraph.cycleGraph n) ≤ (n : ℝ) / ((2 : ℕ) : ℝ) :=
      csInf_le (fracHaemers_set_bddBelow F (SimpleGraph.cycleGraph n)) hmem
    simpa [n] using hle
  · apply le_csInf (fracHaemers_set_nonempty F (SimpleGraph.cycleGraph n))
    rintro q ⟨s, d, rep, rfl⟩
    have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr rep.hs
    rw [div_le_div_iff₀ (by norm_num) hs_pos]
    suffices hnat : (2 * k + 1) * s ≤ 2 * d by
      have hreal : ((2 * k + 1 : ℕ) : ℝ) * (s : ℝ) ≤ (2 : ℝ) * (d : ℝ) := by exact_mod_cast hnat
      push_cast at hreal
      linarith
    let Vsub : Fin n → Submodule F (Fin d → F) := fracHaemersSub rep
    let v0 : Fin n := ⟨0, by omega⟩
    let v1 : Fin n := ⟨1, by omega⟩
    let v2k : Fin n := ⟨2 * k, by omega⟩
    let S0 : Finset (Fin n) := (Finset.univ : Finset (Fin k)).image fun m => ⟨2 * (m.val + 1), by omega⟩
    have hS0_card : S0.card = k := by
      rw [Finset.card_image_of_injOn, Finset.card_univ, Fintype.card_fin]
      intro a _ b _ hab
      have hval : 2 * (a.val + 1) = 2 * (b.val + 1) := congrArg Fin.val hab
      exact Fin.ext (by omega)
    have hS0_indep : (SimpleGraph.cycleGraph n).IsIndepSet (S0 : Set (Fin n)) := by
      intro x hx y hy hxy hadj
      simp only [S0, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      rcases hx with ⟨a, rfl⟩
      rcases hy with ⟨b, rfl⟩
      have hab : a ≠ b := fun h => hxy (by subst h; rfl)
      rcases lt_or_gt_of_ne hab with hlt | hlt
      · refine not_cycleGraph_adj_of_val_diff' (by omega) _ _
          (δ := 2 * (b.val - a.val)) (by omega) (by omega) ?_ (Or.inr hadj)
        right
        have : ((2 * (b.val + 1) : ℕ) : ℤ) - ((2 * (a.val + 1) : ℕ) : ℤ) =
            ((2 * (b.val - a.val) : ℕ) : ℤ) := by omega
        simp only [this]
        exact Int.ModEq.refl _
      · refine not_cycleGraph_adj_of_val_diff' (by omega) _ _
          (δ := 2 * (a.val - b.val)) (by omega) (by omega) ?_ (Or.inr hadj)
        left
        have : ((2 * (a.val + 1) : ℕ) : ℤ) - ((2 * (b.val + 1) : ℕ) : ℤ) =
            ((2 * (a.val - b.val) : ℕ) : ℤ) := by omega
        simp only [this]
        exact Int.ModEq.refl _
    have hS0_dim :
        Module.finrank F (⨆ (u : Fin n) (_ : u ∈ S0), Vsub u : Submodule F (Fin d → F)) =
          k * s := by
      rw [fracHaemers_sup_finrank_of_indepSet rep hS0_indep, hS0_card]
    have hv2k_mem : v2k ∈ S0 := by
      simp only [S0, Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨⟨k - 1, by omega⟩, Fin.ext ?_⟩
      dsimp only [v2k]
      omega
    have hinf0 :
        Vsub v0 ⊓ (⨆ (u : Fin n) (_ : u ∈ S0), Vsub u : Submodule F (Fin d → F)) ≤
          Vsub v0 ⊓ Vsub v2k := by
      intro x hx
      rcases hx with ⟨hx0, hxS⟩
      refine ⟨hx0, ?_⟩
      change x ∈ (⨆ (u : Fin n) (_ : u ∈ S0), Vsub u : Submodule F (Fin d → F)) at hxS
      rw [Submodule.mem_iSup_finset_iff_exists_sum] at hxS
      rcases hxS with ⟨g, rfl⟩
      have hg_zero : ∀ u ∈ S0, u ≠ v2k → (g u : Fin d → F) = 0 := by
        intro u hu huv
        have hu_range : ∃ m : Fin k, m.val < k - 1 ∧ u = ⟨2 * (m.val + 1), by omega⟩ := by
          simp only [S0, Finset.mem_image, Finset.mem_univ, true_and] at hu
          rcases hu with ⟨m, rfl⟩
          refine ⟨m, ?_, rfl⟩
          by_contra hm_ge
          have hmk : m.val = k - 1 := by omega
          apply huv
          apply Fin.ext
          dsimp only [v2k]
          omega
        rcases hu_range with ⟨m, hm, rfl⟩
        let um : Fin n := ⟨2 * (m.val + 1), by omega⟩
        have hnon0 : ¬ (um = v0 ∨ (SimpleGraph.cycleGraph n).Adj um v0) := by
          refine not_cycleGraph_adj_of_val_diff' (by omega) um v0
            (δ := 2 * (m.val + 1)) (by omega) (by omega) ?_
          left
          simp [um, v0]
        have hAu_sum : (rep.A um).mulVec (∑ w ∈ S0, (g w : Fin d → F)) = 0 :=
          fracHaemers_mulVec_eq_zero_of_mem_sub rep (fun h => hnon0 (Or.inl h))
            (fun ha => hnon0 (Or.inr ha)) hx0
        have hAu_other : ∀ w ∈ S0, w ≠ um → (rep.A um).mulVec (g w : Fin d → F) = 0 := by
          intro w hw hwu
          exact fracHaemers_mulVec_eq_zero_of_mem_sub rep hwu.symm (hS0_indep hu hw hwu.symm)
            (g w).2
        have hAu_single : (rep.A um).mulVec (g um : Fin d → F) = 0 := by
          have hsum_eq :
              (rep.A um).mulVec (∑ w ∈ S0, (g w : Fin d → F)) =
                (rep.A um).mulVec (g um : Fin d → F) := by
            rw [Matrix.mulVec_sum]
            exact Finset.sum_eq_single um (fun w hw hwu => hAu_other w hw hwu)
              (fun hnot => absurd hu hnot)
          rw [← hsum_eq, hAu_sum]
        exact fracHaemers_eq_zero_of_mulVec_zero rep (g um).2 hAu_single
      have hsum_v2k : ∑ u ∈ S0, (g u : Fin d → F) = (g v2k : Fin d → F) :=
        Finset.sum_eq_single v2k hg_zero (fun hnot => absurd hv2k_mem hnot)
      rw [hsum_v2k]
      exact (g v2k).2
    have hineq0 : s + k * s ≤ d + Module.finrank F (Vsub v0 ⊓ Vsub v2k : Submodule F (Fin d → F)) := by
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq
        (Vsub v0) (⨆ (u : Fin n) (_ : u ∈ S0), Vsub u : Submodule F (Fin d → F))
      rw [fracHaemersSub_finrank, hS0_dim] at hdim
      have hsup_le :
          Module.finrank F
            ((Vsub v0 ⊔ (⨆ (u : Fin n) (_ : u ∈ S0), Vsub u : Submodule F (Fin d → F)) :
              Submodule F (Fin d → F))) ≤ d := by
        calc Module.finrank F
                ((Vsub v0 ⊔ (⨆ (u : Fin n) (_ : u ∈ S0), Vsub u : Submodule F (Fin d → F)) :
                  Submodule F (Fin d → F)))
            ≤ Module.finrank F (Fin d → F) := Submodule.finrank_le _
          _ = d := Module.finrank_fin_fun F
      have hinf_le :
          Module.finrank F
              ((Vsub v0 ⊓ (⨆ (u : Fin n) (_ : u ∈ S0), Vsub u : Submodule F (Fin d → F)) :
                Submodule F (Fin d → F))) ≤
            Module.finrank F (Vsub v0 ⊓ Vsub v2k : Submodule F (Fin d → F)) :=
        Submodule.finrank_mono hinf0
      omega
    let S1 : Finset (Fin n) :=
      (Finset.univ : Finset (Fin k)).image fun m => ⟨(2 * (m.val + 1) + 1) % n, Nat.mod_lt _ (by omega)⟩
    have hS1_card : S1.card = k := by
      rw [Finset.card_image_of_injOn, Finset.card_univ, Fintype.card_fin]
      intro a _ b _ hab
      have hval := congrArg Fin.val hab
      dsimp only at hval
      rcases Nat.lt_or_ge (a.val + 1) k with ha' | ha' <;>
        rcases Nat.lt_or_ge (b.val + 1) k with hb' | hb'
      · have h1 : 2 * (a.val + 1) + 1 < n := by dsimp only [n]; omega
        have h2 : 2 * (b.val + 1) + 1 < n := by dsimp only [n]; omega
        rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval
        exact Fin.ext (by omega)
      · have h1 : 2 * (a.val + 1) + 1 < n := by dsimp only [n]; omega
        have h2 : 2 * (b.val + 1) + 1 = n := by dsimp only [n]; have := b.isLt; omega
        rw [Nat.mod_eq_of_lt h1, h2, Nat.mod_self] at hval
        omega
      · have h1 : 2 * (a.val + 1) + 1 = n := by dsimp only [n]; have := a.isLt; omega
        have h2 : 2 * (b.val + 1) + 1 < n := by dsimp only [n]; omega
        rw [h1, Nat.mod_self, Nat.mod_eq_of_lt h2] at hval
        omega
      · have ha_eq : a.val = k - 1 := by have := a.isLt; omega
        have hb_eq : b.val = k - 1 := by have := b.isLt; omega
        exact Fin.ext (by omega)
    have hv0_mem1 : v0 ∈ S1 := by
      simp only [S1, Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨⟨k - 1, by omega⟩, Fin.ext ?_⟩
      have heq : 2 * ((k - 1) + 1) + 1 = n := by dsimp only [n]; omega
      simp [heq, v0]
    have hS1_indep : (SimpleGraph.cycleGraph n).IsIndepSet (S1 : Set (Fin n)) := by
      intro x hx y hy hxy hadj
      simp only [S1, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      rcases hx with ⟨a, rfl⟩
      rcases hy with ⟨b, rfl⟩
      have hab : a ≠ b := fun h => hxy (by subst h; rfl)
      have hmod_pair : ∀ p q : Fin k, p < q →
          ¬ ((⟨(2 * (p.val + 1) + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) =
              ⟨(2 * (q.val + 1) + 1) % n, Nat.mod_lt _ (by omega)⟩ ∨
            (SimpleGraph.cycleGraph n).Adj
              ⟨(2 * (p.val + 1) + 1) % n, Nat.mod_lt _ (by omega)⟩
              ⟨(2 * (q.val + 1) + 1) % n, Nat.mod_lt _ (by omega)⟩) := by
        intro p q hpq
        rcases Nat.lt_or_ge (q.val + 1) k with hq_lt | hq_ge
        · refine not_cycleGraph_adj_of_val_diff' (by omega) _ _
            (δ := 2 * (q.val - p.val)) (by omega) (by omega) ?_
          right
          have h1 : (2 * (p.val + 1) + 1) < n := by dsimp only [n]; have := hpq; omega
          have h2 : (2 * (q.val + 1) + 1) < n := by dsimp only [n]; omega
          simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
          have : ((2 * (q.val + 1) + 1 : ℕ) : ℤ) - ((2 * (p.val + 1) + 1 : ℕ) : ℤ) =
              ((2 * (q.val - p.val) : ℕ) : ℤ) := by have := hpq; omega
          simp only [this]
          exact Int.ModEq.refl _
        · have h1 : (2 * (p.val + 1) + 1) < n := by dsimp only [n]; have := hpq; have := q.isLt; omega
          have h2 : 2 * (q.val + 1) + 1 = n := by dsimp only [n]; have := q.isLt; omega
          refine not_cycleGraph_adj_of_val_diff' (by omega) _ _
            (δ := 2 * (p.val + 1) + 1) (by omega) (by have := hpq; have := q.isLt; omega) ?_
          left
          simp only [Nat.mod_eq_of_lt h1, h2, Nat.mod_self, Int.ofNat_zero, sub_zero]
          exact Int.ModEq.refl _
      rcases lt_or_gt_of_ne hab with hlt | hlt
      · exact hmod_pair a b hlt (Or.inr hadj)
      · exact hmod_pair b a hlt (Or.inr hadj.symm)
    have hS1_dim :
        Module.finrank F (⨆ (u : Fin n) (_ : u ∈ S1), Vsub u : Submodule F (Fin d → F)) =
          k * s := by
      rw [fracHaemers_sup_finrank_of_indepSet rep hS1_indep, hS1_card]
    have hinf1 :
        Vsub v1 ⊓ (⨆ (u : Fin n) (_ : u ∈ S1), Vsub u : Submodule F (Fin d → F)) ≤
          Vsub v1 ⊓ Vsub v0 := by
      intro x hx
      rcases hx with ⟨hx1, hxS⟩
      refine ⟨hx1, ?_⟩
      change x ∈ (⨆ (u : Fin n) (_ : u ∈ S1), Vsub u : Submodule F (Fin d → F)) at hxS
      rw [Submodule.mem_iSup_finset_iff_exists_sum] at hxS
      rcases hxS with ⟨g, rfl⟩
      have hg_zero : ∀ u ∈ S1, u ≠ v0 → (g u : Fin d → F) = 0 := by
        intro u hu huv
        have hu_range : ∃ m : Fin k, m.val < k - 1 ∧
            u = ⟨(2 * (m.val + 1) + 1) % n, Nat.mod_lt _ (by omega)⟩ := by
          simp only [S1, Finset.mem_image, Finset.mem_univ, true_and] at hu
          rcases hu with ⟨m, rfl⟩
          refine ⟨m, ?_, rfl⟩
          by_contra hm_ge
          have hmk : m.val = k - 1 := by omega
          apply huv
          apply Fin.ext
          have heq : 2 * (m.val + 1) + 1 = n := by dsimp only [n]; omega
          simp [heq, v0]
        rcases hu_range with ⟨m, hm, rfl⟩
        have hlt_n : 2 * (m.val + 1) + 1 < n := by dsimp only [n]; omega
        let um : Fin n := ⟨(2 * (m.val + 1) + 1) % n, Nat.mod_lt _ (by omega)⟩
        have hnon1 : ¬ (um = v1 ∨ (SimpleGraph.cycleGraph n).Adj um v1) := by
          refine not_cycleGraph_adj_of_val_diff' (by omega) um v1
            (δ := 2 * (m.val + 1)) (by omega) (by omega) ?_
          left
          have hum : um.val = 2 * (m.val + 1) + 1 := Nat.mod_eq_of_lt hlt_n
          have hv1 : v1.val = 1 := rfl
          rw [hum, hv1]
          have : ((2 * (m.val + 1) + 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) =
              ((2 * (m.val + 1) : ℕ) : ℤ) := by omega
          rw [this]
        have hAu_sum : (rep.A um).mulVec (∑ w ∈ S1, (g w : Fin d → F)) = 0 :=
          fracHaemers_mulVec_eq_zero_of_mem_sub rep (fun h => hnon1 (Or.inl h))
            (fun ha => hnon1 (Or.inr ha)) hx1
        have hAu_other : ∀ w ∈ S1, w ≠ um → (rep.A um).mulVec (g w : Fin d → F) = 0 := by
          intro w hw hwu
          exact fracHaemers_mulVec_eq_zero_of_mem_sub rep hwu.symm (hS1_indep hu hw hwu.symm)
            (g w).2
        have hAu_single : (rep.A um).mulVec (g um : Fin d → F) = 0 := by
          have hsum_eq :
              (rep.A um).mulVec (∑ w ∈ S1, (g w : Fin d → F)) =
                (rep.A um).mulVec (g um : Fin d → F) := by
            rw [Matrix.mulVec_sum]
            exact Finset.sum_eq_single um (fun w hw hwu => hAu_other w hw hwu)
              (fun hnot => absurd hu hnot)
          rw [← hsum_eq, hAu_sum]
        exact fracHaemers_eq_zero_of_mulVec_zero rep (g um).2 hAu_single
      have hsum_v0 : ∑ u ∈ S1, (g u : Fin d → F) = (g v0 : Fin d → F) :=
        Finset.sum_eq_single v0 hg_zero (fun hnot => absurd hv0_mem1 hnot)
      rw [hsum_v0]
      exact (g v0).2
    have hineq1 : s + k * s ≤ d + Module.finrank F (Vsub v1 ⊓ Vsub v0 : Submodule F (Fin d → F)) := by
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq
        (Vsub v1) (⨆ (u : Fin n) (_ : u ∈ S1), Vsub u : Submodule F (Fin d → F))
      rw [fracHaemersSub_finrank, hS1_dim] at hdim
      have hsup_le :
          Module.finrank F
            ((Vsub v1 ⊔ (⨆ (u : Fin n) (_ : u ∈ S1), Vsub u : Submodule F (Fin d → F)) :
              Submodule F (Fin d → F))) ≤ d := by
        calc Module.finrank F
                ((Vsub v1 ⊔ (⨆ (u : Fin n) (_ : u ∈ S1), Vsub u : Submodule F (Fin d → F)) :
                  Submodule F (Fin d → F)))
            ≤ Module.finrank F (Fin d → F) := Submodule.finrank_le _
          _ = d := Module.finrank_fin_fun F
      have hinf_le :
          Module.finrank F
              ((Vsub v1 ⊓ (⨆ (u : Fin n) (_ : u ∈ S1), Vsub u : Submodule F (Fin d → F)) :
                Submodule F (Fin d → F))) ≤
            Module.finrank F (Vsub v1 ⊓ Vsub v0 : Submodule F (Fin d → F)) :=
        Submodule.finrank_mono hinf1
      omega
    have hnon12k : ¬ (v1 = v2k ∨ (SimpleGraph.cycleGraph n).Adj v1 v2k) := by
      refine not_cycleGraph_adj_of_val_diff' (by omega) v1 v2k
        (δ := 2 * k - 1) (by omega) (by omega) ?_
      right
      have : ((v2k.val : ℕ) : ℤ) - ((v1.val : ℕ) : ℤ) = ((2 * k - 1 : ℕ) : ℤ) := by
        dsimp [v1, v2k]; omega
      simp only [this]
      exact Int.ModEq.refl _
    have hdisj_12k : Vsub v1 ⊓ Vsub v2k = ⊥ := by
      rw [eq_bot_iff]
      intro x ⟨hx1, hx2k⟩
      have hAx : (rep.A v1).mulVec x = 0 :=
        fracHaemers_mulVec_eq_zero_of_mem_sub rep (fun h => hnon12k (Or.inl h))
          (fun ha => hnon12k (Or.inr ha)) hx2k
      rw [Submodule.mem_bot]
      exact fracHaemers_eq_zero_of_mulVec_zero rep hx1 hAx
    have hsum_inf :
        Module.finrank F (Vsub v0 ⊓ Vsub v2k : Submodule F (Fin d → F)) +
          Module.finrank F (Vsub v1 ⊓ Vsub v0 : Submodule F (Fin d → F)) ≤ s := by
      have hdisj_infs : (Vsub v0 ⊓ Vsub v2k) ⊓ (Vsub v1 ⊓ Vsub v0) = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨⟨_, hx2k⟩, ⟨hx1, _⟩⟩
        have hmem : x ∈ Vsub v1 ⊓ Vsub v2k := ⟨hx1, hx2k⟩
        rwa [hdisj_12k] at hmem
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq (Vsub v0 ⊓ Vsub v2k) (Vsub v1 ⊓ Vsub v0)
      rw [hdisj_infs, finrank_bot, add_zero] at hdim
      have hsup_le : (Vsub v0 ⊓ Vsub v2k) ⊔ (Vsub v1 ⊓ Vsub v0) ≤ Vsub v0 :=
        sup_le inf_le_left inf_le_right
      have hfin_le := Submodule.finrank_mono hsup_le
      rw [fracHaemersSub_finrank] at hfin_le
      omega
    have hlin : (2 * k + 1) * s = 2 * (k * s) + s := by ring
    rw [hlin]
    omega

theorem fracHaemers_c7 (F : Type*) [Field F] :
    fracHaemers F (SimpleGraph.cycleGraph 7) = 7 / 2 := by
  have h := fracHaemers_oddCycle F (k := 3) (by omega)
  norm_num at h
  exact h

theorem lovaszThetaC7_lt_fracHaemers_c7 (F : Type*) [Field F] :
    lovaszThetaC7 < fracHaemers F (SimpleGraph.cycleGraph 7) := by
  rw [fracHaemers_c7 F]
  exact lovaszThetaC7_lt_of_cubic_pos (by norm_num) (by norm_num)

end ShannonC7
