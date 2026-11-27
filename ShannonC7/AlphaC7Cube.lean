import ShannonC7.Defs
import ShannonC7.CycleC7
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Exact Independence Number `α(C₇^⊠3) = 33` (`ShannonC7/AlphaC7Cube.lean`)

Pure-kernel Lean 4 proof (zero `sorry`, zero `native_decide`, zero `partial`, standard axioms
`{propext, Classical.choice, Quot.sound}` only) establishing:
- `alpha_c7_pow3_le : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum ≤ 33`
- `alpha_c7_pow3 : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum = 33`
-/

namespace ShannonC7

noncomputable section

/-! ## Section 1: 49-Bit `Nat` Bitsets, SWAR Popcount & Bit-Permutation Primitives -/

private lemma fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ x : Fin 3, P x
  | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2

private lemma fin7_cases {P : Fin 7 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) :
    ∀ x : Fin 7, P x
  | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2 | ⟨3, _⟩ => h3
  | ⟨4, _⟩ => h4 | ⟨5, _⟩ => h5 | ⟨6, _⟩ => h6

private def next7 (x : Fin 7) : Fin 7 :=
  match x.val with
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | _ => 0

private def prev7 (x : Fin 7) : Fin 7 :=
  match x.val with
  | 0 => 6 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | _ => 5

private def neg7 (x : Fin 7) : Fin 7 :=
  match x.val with
  | 0 => 0 | 1 => 6 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2 | _ => 1

private def add7 (x y : Fin 7) : Fin 7 :=
  ⟨(x.val + y.val) % 7, Nat.mod_lt _ (by decide)⟩

private def toZ7 (x : Fin 7) : ZMod 7 := (x.val : ZMod 7)
private def ofZ7 (x : ZMod 7) : Fin 7 := ⟨x.val, x.val_lt⟩

private lemma toZ7_ofZ7 (x : ZMod 7) : toZ7 (ofZ7 x) = x := ZMod.natCast_zmod_val x

private lemma ofZ7_toZ7 : ∀ x : Fin 7, ofZ7 (toZ7 x) = x
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl

private lemma toZ7_injective : Function.Injective toZ7 := by
  intro a b h
  have := congrArg ofZ7 h
  simpa [ofZ7_toZ7] using this

private lemma toZ7_next7 : ∀ x : Fin 7, toZ7 (next7 x) = toZ7 x + 1 := by decide
private lemma toZ7_prev7 : ∀ x : Fin 7, toZ7 (prev7 x) = toZ7 x - 1 := by decide
private lemma toZ7_neg7 : ∀ x : Fin 7, toZ7 (neg7 x) = -toZ7 x := by decide
private lemma toZ7_add7 : ∀ x y : Fin 7, toZ7 (add7 x y) = toZ7 x + toZ7 y := by decide

private lemma c7Close_iff : ∀ a b : Fin 7,
    (toZ7 a = toZ7 b ∨ C7.Adj (toZ7 a) (toZ7 b)) ↔
      (a = prev7 b ∨ a = b ∨ a = next7 b) := by decide

private lemma d7_inv_left (s : Bool) (t x : Fin 7) :
    add7 (if s then neg7 (add7 (if s then neg7 x else x) t) else add7 (if s then neg7 x else x) t)
      (if s then t else neg7 t) = x := by
  apply toZ7_injective
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, toZ7_add7, toZ7_neg7] <;> ring

private lemma d7_inv_right (s : Bool) (t x : Fin 7) :
    add7 (if s then neg7 (add7 (if s then neg7 x else x) (if s then t else neg7 t))
          else add7 (if s then neg7 x else x) (if s then t else neg7 t)) t = x := by
  apply toZ7_injective
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, toZ7_add7, toZ7_neg7] <;> ring

private lemma d7_comp (s1 s2 : Bool) (t1 t2 x : Fin 7) :
    add7 (if s1 then neg7 (add7 (if s2 then neg7 x else x) t2) else add7 (if s2 then neg7 x else x) t2) t1 =
      add7 (if xor s1 s2 then neg7 x else x) (add7 (if s1 then neg7 t2 else t2) t1) := by
  apply toZ7_injective
  cases s1 <;> cases s2 <;> simp [xor, toZ7_add7, toZ7_neg7] <;> ring

private lemma land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
private lemma lor_eq (a b : Nat) : Nat.lor a b = a ||| b := rfl
private lemma xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
private lemma shl_eq (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
private lemma shr_eq (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
private lemma add_eq (a b : Nat) : Nat.add a b = a + b := rfl
private lemma sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
private lemma mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
private lemma beq_eq (a b : Nat) : Nat.beq a b = (a == b) := by
  cases h : Nat.beq a b
  · have hne : a ≠ b := fun heq => by subst heq; simp at h
    exact (beq_false_of_ne hne).symm
  · have heq : a = b := Nat.eq_of_beq_eq_true h
    subst heq; simp

private def ALL49 : Nat := 562949953421311

private def seqN {α : Type} (x : Nat) (k : Nat → α) : α :=
  match Nat.beq x 0 with | true => k 0 | false => k x

private lemma seqN_eq {α : Type} (x : Nat) (k : Nat → α) : seqN x k = k x := by
  unfold seqN; rw [beq_eq]
  cases h : (x == 0)
  · rfl
  · rw [beq_iff_eq.mp h]

private def bit49 (r c : Fin 7) : Nat := Nat.shiftLeft 1 (Nat.add (Nat.mul r.val 7) c.val)
private def get49 (m : Nat) (r c : Fin 7) : Bool := m.testBit (r.val * 7 + c.val)
private def row49 (m : Nat) (r : Fin 7) : Nat := Nat.land (Nat.shiftRight m (Nat.mul r.val 7)) 127
private def not49 (m : Nat) : Nat := Nat.xor ALL49 m
private def diff49 (a b : Nat) : Nat := Nat.land a (Nat.xor ALL49 b)
private def set49 (m : Nat) (r c : Fin 7) : Nat := Nat.lor m (bit49 r c)
private def subset49 (a b : Nat) : Bool := Nat.beq (Nat.land a b) a
private def disjoint49 (a b : Nat) : Bool := Nat.beq (Nat.land a b) 0

private lemma all49_eq : ALL49 = 2 ^ 49 - 1 := rfl

private lemma testBit_all49 (i : Nat) : ALL49.testBit i = decide (i < 49) := by
  rw [all49_eq, Nat.testBit_two_pow_sub_one]

private lemma testBit_all49_lt {i : Nat} (hi : i < 49) : ALL49.testBit i = true := by
  rw [testBit_all49]; exact decide_eq_true hi

private lemma idx_lt49 (r c : Fin 7) : r.val * 7 + c.val < 49 := by omega

private lemma pow2_mono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

private lemma testBit_lt49 {m : Nat} (hm : m < 2 ^ 49) {i : Nat} (hi : 49 ≤ i) :
    m.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (pow2_mono hi))

private lemma ext49 {a b : Nat} (ha : a < 2 ^ 49) (hb : b < 2 ^ 49)
    (h : ∀ r c : Fin 7, get49 a r c = get49 b r c) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 49
  · let r : Fin 7 := ⟨i / 7, Nat.div_lt_of_lt_mul hi⟩
    let c : Fin 7 := ⟨i % 7, Nat.mod_lt _ (by decide)⟩
    have heq : r.val * 7 + c.val = i := by
      dsimp [r, c]; omega
    have hr := h r c
    unfold get49 at hr
    rwa [heq] at hr
  · rw [testBit_lt49 ha (by omega), testBit_lt49 hb (by omega)]

private lemma bit49_lt (r c : Fin 7) : bit49 r c < 2 ^ 49 := by
  unfold bit49
  rw [shl_eq, add_eq, mul_eq, Nat.shiftLeft_eq, one_mul]
  exact Nat.pow_lt_pow_right (by decide) (idx_lt49 r c)

private lemma testBit_bit49 (r c r' c' : Fin 7) :
    (bit49 r c).testBit (r'.val * 7 + c'.val) = decide (r' = r ∧ c' = c) := by
  unfold bit49
  rw [shl_eq, add_eq, mul_eq, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  have hiff : r.val * 7 + c.val = r'.val * 7 + c'.val ↔ r' = r ∧ c' = c := by
    constructor
    · intro h
      have hr : r'.val = r.val := by omega
      have hc : c'.val = c.val := by omega
      exact ⟨Fin.ext hr, Fin.ext hc⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [hiff]

private lemma get49_zero (r c : Fin 7) : get49 0 r c = false := Nat.zero_testBit _
private lemma get49_and (a b : Nat) (r c : Fin 7) : get49 (a &&& b) r c = (get49 a r c && get49 b r c) :=
  Nat.testBit_and a b _
private lemma get49_or (a b : Nat) (r c : Fin 7) : get49 (a ||| b) r c = (get49 a r c || get49 b r c) :=
  Nat.testBit_or a b _
private lemma get49_not (a : Nat) (r c : Fin 7) : get49 (not49 a) r c = !get49 a r c := by
  unfold get49 not49; rw [xor_eq, Nat.testBit_xor, testBit_all49_lt (idx_lt49 r c)]; cases a.testBit _ <;> rfl
private lemma get49_diff (a b : Nat) (r c : Fin 7) : get49 (diff49 a b) r c = (get49 a r c && !get49 b r c) := by
  unfold diff49; rw [land_eq]; change get49 (a &&& not49 b) r c = _; rw [get49_and, get49_not]
private lemma get49_set (a : Nat) (r c r' c' : Fin 7) :
    get49 (set49 a r c) r' c' = (if r' = r ∧ c' = c then true else get49 a r' c') := by
  unfold set49 get49
  rw [lor_eq, Nat.testBit_or, testBit_bit49]
  by_cases h : r' = r ∧ c' = c <;> simp [h]

private lemma and_lt49 {a b : Nat} (hb : b < 2 ^ 49) : a &&& b < 2 ^ 49 := Nat.and_lt_two_pow a hb
private lemma and_lt49_left {a b : Nat} (ha : a < 2 ^ 49) : a &&& b < 2 ^ 49 := by
  rw [Nat.and_comm]; exact Nat.and_lt_two_pow b ha
private lemma or_lt49 {a b : Nat} (ha : a < 2 ^ 49) (hb : b < 2 ^ 49) : a ||| b < 2 ^ 49 :=
  Nat.or_lt_two_pow ha hb
private lemma not49_lt {a : Nat} (ha : a < 2 ^ 49) : not49 a < 2 ^ 49 := by
  unfold not49; rw [xor_eq]; exact Nat.xor_lt_two_pow (by decide) ha
private lemma diff49_lt {a b : Nat} (ha : a < 2 ^ 49) : diff49 a b < 2 ^ 49 := by
  unfold diff49; rw [land_eq]; exact and_lt49_left ha
private lemma set49_lt {a : Nat} (ha : a < 2 ^ 49) (r c : Fin 7) : set49 a r c < 2 ^ 49 := by
  unfold set49; rw [lor_eq]; exact or_lt49 ha (bit49_lt r c)

private lemma subset49_iff {a b : Nat} (ha : a < 2 ^ 49) :
    subset49 a b = true ↔ ∀ r c : Fin 7, get49 a r c = true → get49 b r c = true := by
  unfold subset49
  rw [beq_eq, land_eq, beq_iff_eq]
  constructor
  · intro heq r c h
    have hbit := congrArg (fun x => x.testBit (r.val * 7 + c.val)) heq
    rw [Nat.testBit_and] at hbit
    unfold get49 at h ⊢
    rw [h, Bool.true_and] at hbit
    exact hbit
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < 49
    · let r : Fin 7 := ⟨i / 7, Nat.div_lt_of_lt_mul hi⟩
      let c : Fin 7 := ⟨i % 7, Nat.mod_lt _ (by decide)⟩
      have heq : r.val * 7 + c.val = i := by dsimp [r, c]; omega
      cases ha' : a.testBit i
      · rfl
      · have hb' := h r c (by unfold get49; rwa [heq])
        unfold get49 at hb'; rw [heq] at hb'; rw [hb']; rfl
    · rw [testBit_lt49 ha (by omega)]; rfl

private lemma disjoint49_iff {a b : Nat} (ha : a < 2 ^ 49) :
    disjoint49 a b = true ↔ ∀ r c : Fin 7, get49 a r c = true → get49 b r c = false := by
  unfold disjoint49
  rw [beq_eq, land_eq, beq_iff_eq]
  constructor
  · intro heq r c h
    have hbit := congrArg (fun x => x.testBit (r.val * 7 + c.val)) heq
    rw [Nat.testBit_and, Nat.zero_testBit] at hbit
    unfold get49 at h ⊢
    rw [h, Bool.true_and] at hbit
    exact hbit
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < 49
    · let r : Fin 7 := ⟨i / 7, Nat.div_lt_of_lt_mul hi⟩
      let c : Fin 7 := ⟨i % 7, Nat.mod_lt _ (by decide)⟩
      have heq : r.val * 7 + c.val = i := by dsimp [r, c]; omega
      cases ha' : a.testBit i
      · rfl
      · have hb' := h r c (by unfold get49; rwa [heq])
        unfold get49 at hb'; rw [heq] at hb'; rw [hb']; rfl
    · rw [testBit_lt49 ha (by omega)]; rfl

private lemma subset49_zero_left (b : Nat) : subset49 0 b = true := by
  unfold subset49; rw [beq_eq, land_eq]; simp

private lemma subset49_trans {a b c : Nat} (ha : a < 2 ^ 49) (hb : b < 2 ^ 49)
    (hab : subset49 a b = true) (hbc : subset49 b c = true) : subset49 a c = true := by
  rw [subset49_iff ha] at hab ⊢
  rw [subset49_iff hb] at hbc
  exact fun r col h => hbc r col (hab r col h)

private def pop7 (x : Nat) : Nat :=
  seqN (Nat.sub x (Nat.land (Nat.shiftRight x 1) 0x55)) fun x1 =>
  seqN (Nat.add (Nat.land x1 0x33) (Nat.land (Nat.shiftRight x1 2) 0x33)) fun x2 =>
  Nat.add (Nat.land x2 0x0F) (Nat.shiftRight x2 4)

private def pop49 (m : Nat) : Nat :=
  Nat.add (pop7 (Nat.land m 127))
  (Nat.add (pop7 (Nat.land (Nat.shiftRight m 7) 127))
  (Nat.add (pop7 (Nat.land (Nat.shiftRight m 14) 127))
  (Nat.add (pop7 (Nat.land (Nat.shiftRight m 21) 127))
  (Nat.add (pop7 (Nat.land (Nat.shiftRight m 28) 127))
  (Nat.add (pop7 (Nat.land (Nat.shiftRight m 35) 127))
           (pop7 (Nat.land (Nat.shiftRight m 42) 127)))))))

private lemma pop7_eq_sum {x : Nat} (hx : x < 128) :
    pop7 x = ∑ c : Fin 7, (x.testBit c.val).toNat := by
  have hall : ∀ y : Fin 128, pop7 y.val = ∑ c : Fin 7, (y.val.testBit c.val).toNat := by decide
  exact hall ⟨x, hx⟩

private lemma row49_lt (m : Nat) (r : Fin 7) : row49 m r < 128 := by
  unfold row49; rw [land_eq]; exact Nat.and_lt_two_pow _ (n := 7) (by decide)

private lemma row49_testBit (m : Nat) (r c : Fin 7) :
    (row49 m r).testBit c.val = get49 m r c := by
  unfold row49 get49
  rw [land_eq, shr_eq, mul_eq, Nat.testBit_and, Nat.testBit_shiftRight]
  have h127 : (127 : Nat).testBit c.val = true := by
    change (2 ^ 7 - 1).testBit c.val = true
    rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true c.isLt
  rw [h127, Bool.and_true]

private lemma pop7_row49_eq_sum (m : Nat) (r : Fin 7) :
    pop7 (row49 m r) = ∑ c : Fin 7, (get49 m r c).toNat := by
  rw [pop7_eq_sum (row49_lt m r)]
  exact Finset.sum_congr rfl fun c _ => congrArg Bool.toNat (row49_testBit m r c)

private lemma pop49_eq_rows (m : Nat) :
    pop49 m = pop7 (row49 m 0) + pop7 (row49 m 1) + pop7 (row49 m 2) +
              pop7 (row49 m 3) + pop7 (row49 m 4) + pop7 (row49 m 5) + pop7 (row49 m 6) := by
  have r0 : row49 m 0 = Nat.land m 127 := by unfold row49; simp
  have r1 : row49 m 1 = Nat.land (Nat.shiftRight m 7) 127 := rfl
  have r2 : row49 m 2 = Nat.land (Nat.shiftRight m 14) 127 := rfl
  have r3 : row49 m 3 = Nat.land (Nat.shiftRight m 21) 127 := rfl
  have r4 : row49 m 4 = Nat.land (Nat.shiftRight m 28) 127 := rfl
  have r5 : row49 m 5 = Nat.land (Nat.shiftRight m 35) 127 := rfl
  have r6 : row49 m 6 = Nat.land (Nat.shiftRight m 42) 127 := rfl
  rw [r0, r1, r2, r3, r4, r5, r6]
  unfold pop49; simp only [add_eq]; omega

private lemma pop49_eq_sum (m : Nat) :
    pop49 m = ∑ r : Fin 7, ∑ c : Fin 7, (get49 m r c).toNat := by
  rw [pop49_eq_rows, Fin.sum_univ_seven]
  simp only [pop7_row49_eq_sum, Nat.add_assoc]

private lemma subset49_pop_le {a b : Nat} (ha : a < 2 ^ 49) (h : subset49 a b = true) :
    pop49 a ≤ pop49 b := by
  rw [subset49_iff ha] at h
  rw [pop49_eq_sum, pop49_eq_sum]
  refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun c _ => ?_
  cases ha' : get49 a r c
  · simp
  · simp [h r c ha']

/-! ### Bit-Permutation & Closed-Neighborhood Lemmas via Masked Shifts -/

private lemma bit_and_masked (m mask i src : Nat) (f : Bool)
    (hmask : mask.testBit i = true → i = src)
    (hflag : mask.testBit i = f) :
    (m &&& mask).testBit i = (f && m.testBit src) := by
  rw [Nat.testBit_and, hflag]
  cases hf : f
  · simp
  · rw [hmask (hflag.trans hf), Bool.true_and, Bool.and_true]

private lemma bit_shiftL_masked (m mask k i src : Nat) (f : Bool)
    (hmask : (decide (k ≤ i) && mask.testBit (i - k)) = true → i - k = src)
    (hflag : (decide (k ≤ i) && mask.testBit (i - k)) = f) :
    ((m &&& mask) <<< k).testBit i = (f && m.testBit src) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_and]
  have hge : decide (i ≥ k) = decide (k ≤ i) := rfl
  rw [hge]
  cases h1 : decide (k ≤ i) <;> cases h2 : mask.testBit (i - k)
  · have hf : f = false := by simpa [h1, h2] using hflag.symm
    simp [hf]
  · have hf : f = false := by simpa [h1, h2] using hflag.symm
    simp [hf]
  · have hf : f = false := by simpa [h1, h2] using hflag.symm
    simp [hf]
  · have hsrc := hmask (by simp [h1, h2])
    have hf : f = true := by simpa [h1, h2] using hflag.symm
    rw [hsrc, hf]; simp

private lemma bit_shiftR_masked (m mask k i src : Nat) (f : Bool)
    (hmask : mask.testBit (k + i) = true → k + i = src)
    (hflag : mask.testBit (k + i) = f) :
    ((m &&& mask) >>> k).testBit i = (f && m.testBit src) := by
  rw [Nat.testBit_shiftRight, Nat.testBit_and, hflag]
  cases hf : f
  · simp
  · rw [hmask (hflag.trans hf), Bool.true_and, Bool.and_true]

private lemma shiftL_and_lt49 (m mask k : Nat) (h : ∀ i, 49 ≤ i → ((m &&& mask) <<< k).testBit i = false) :
    (m &&& mask) <<< k < 2 ^ 49 := by
  have h1 : ((m &&& mask) <<< k) = ((m &&& mask) <<< k) &&& ALL49 := by
    apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and, testBit_all49]
    by_cases hi : i < 49
    · simp [hi]
    · simp [hi, h i (by omega)]
  rw [h1]; exact Nat.and_lt_two_pow _ (by decide)

private lemma shiftR_and_lt49 (m mask k : Nat) (hm : mask < 2 ^ 49) :
    (m &&& mask) >>> k < 2 ^ 49 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.and_lt_two_pow m hm)

private def hNbr49 (m : Nat) : Nat :=
  let l1 := Nat.lor (Nat.shiftLeft (Nat.land m 279258638311359) 1) (Nat.shiftRight (Nat.land m 283691315109952) 6)
  let r1 := Nat.lor (Nat.shiftRight (Nat.land m 558517276622718) 1) (Nat.shiftLeft (Nat.land m 4432676798593) 6)
  Nat.lor m (Nat.lor l1 r1)

private def vNbr49 (h : Nat) : Nat :=
  let u1 := Nat.lor (Nat.shiftLeft (Nat.land h 4398046511103) 7) (Nat.shiftRight (Nat.land h 558551906910208) 42)
  let d1 := Nat.lor (Nat.shiftRight (Nat.land h 562949953421184) 7) (Nat.shiftLeft (Nat.land h 127) 42)
  Nat.lor h (Nat.lor u1 d1)

private def closedNbr49 (m : Nat) : Nat :=
  seqN (hNbr49 m) fun h => vNbr49 h

private lemma hNbr49_lt {m : Nat} (hm : m < 2 ^ 49) : hNbr49 m < 2 ^ 49 := by
  unfold hNbr49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  have h1 : (m &&& 279258638311359) <<< 1 < 2 ^ 49 := shiftL_and_lt49 _ _ 1 fun i hi => by
    rw [Nat.testBit_shiftLeft, Nat.testBit_and]
    have hlt : 279258638311359 < 2 ^ 48 := by decide
    have hb : (279258638311359 : Nat).testBit (i - 1) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (by omega)))
    simp [hb]
  have h2 : (m &&& 283691315109952) >>> 6 < 2 ^ 49 := shiftR_and_lt49 _ _ 6 (by decide)
  have h3 : (m &&& 558517276622718) >>> 1 < 2 ^ 49 := shiftR_and_lt49 _ _ 1 (by decide)
  have h4 : (m &&& 4432676798593) <<< 6 < 2 ^ 49 := shiftL_and_lt49 _ _ 6 fun i hi => by
    rw [Nat.testBit_shiftLeft, Nat.testBit_and]
    have hlt : 4432676798593 < 2 ^ 43 := by decide
    have hb : (4432676798593 : Nat).testBit (i - 6) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (by omega)))
    simp [hb]
  exact or_lt49 hm (or_lt49 (or_lt49 h1 h2) (or_lt49 h3 h4))

private lemma vNbr49_lt {h : Nat} (hh : h < 2 ^ 49) : vNbr49 h < 2 ^ 49 := by
  unfold vNbr49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  have h1 : (h &&& 4398046511103) <<< 7 < 2 ^ 49 := shiftL_and_lt49 _ _ 7 fun i hi => by
    rw [Nat.testBit_shiftLeft, Nat.testBit_and]
    have hlt : 4398046511103 < 2 ^ 42 := by decide
    have hb : (4398046511103 : Nat).testBit (i - 7) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (by omega)))
    simp [hb]
  have h2 : (h &&& 558551906910208) >>> 42 < 2 ^ 49 := shiftR_and_lt49 _ _ 42 (by decide)
  have h3 : (h &&& 562949953421184) >>> 7 < 2 ^ 49 := shiftR_and_lt49 _ _ 7 (by decide)
  have h4 : (h &&& 127) <<< 42 < 2 ^ 49 := shiftL_and_lt49 _ _ 42 fun i hi => by
    rw [Nat.testBit_shiftLeft, Nat.testBit_and]
    have hlt : 127 < 2 ^ 7 := by decide
    have hb : (127 : Nat).testBit (i - 42) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (by omega)))
    simp [hb]
  exact or_lt49 hh (or_lt49 (or_lt49 h1 h2) (or_lt49 h3 h4))

private lemma closedNbr49_lt {m : Nat} (hm : m < 2 ^ 49) : closedNbr49 m < 2 ^ 49 := by
  unfold closedNbr49; rw [seqN_eq]; exact vNbr49_lt (hNbr49_lt hm)

private lemma get49_hNbr (m : Nat) (r c : Fin 7) :
    get49 (hNbr49 m) r c = (get49 m r (prev7 c) || get49 m r c || get49 m r (next7 c)) := by
  unfold get49 hNbr49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]
  have e1 := bit_shiftL_masked m 279258638311359 1 (r.val * 7 + c.val) (r.val * 7 + (prev7 c).val) (decide (c ≠ 0))
    ((by decide : ∀ r c : Fin 7, (decide (1 ≤ r.val * 7 + c.val) && (279258638311359 : Nat).testBit (r.val * 7 + c.val - 1)) = true → r.val * 7 + c.val - 1 = r.val * 7 + (prev7 c).val) r c)
    ((by decide : ∀ r c : Fin 7, (decide (1 ≤ r.val * 7 + c.val) && (279258638311359 : Nat).testBit (r.val * 7 + c.val - 1)) = decide (c ≠ 0)) r c)
  have e2 := bit_shiftR_masked m 283691315109952 6 (r.val * 7 + c.val) (r.val * 7 + (prev7 c).val) (decide (c = 0))
    ((by decide : ∀ r c : Fin 7, (283691315109952 : Nat).testBit (6 + (r.val * 7 + c.val)) = true → 6 + (r.val * 7 + c.val) = r.val * 7 + (prev7 c).val) r c)
    ((by decide : ∀ r c : Fin 7, (283691315109952 : Nat).testBit (6 + (r.val * 7 + c.val)) = decide (c = 0)) r c)
  have e3 := bit_shiftR_masked m 558517276622718 1 (r.val * 7 + c.val) (r.val * 7 + (next7 c).val) (decide (c ≠ 6))
    ((by decide : ∀ r c : Fin 7, (558517276622718 : Nat).testBit (1 + (r.val * 7 + c.val)) = true → 1 + (r.val * 7 + c.val) = r.val * 7 + (next7 c).val) r c)
    ((by decide : ∀ r c : Fin 7, (558517276622718 : Nat).testBit (1 + (r.val * 7 + c.val)) = decide (c ≠ 6)) r c)
  have e4 := bit_shiftL_masked m 4432676798593 6 (r.val * 7 + c.val) (r.val * 7 + (next7 c).val) (decide (c = 6))
    ((by decide : ∀ r c : Fin 7, (decide (6 ≤ r.val * 7 + c.val) && (4432676798593 : Nat).testBit (r.val * 7 + c.val - 6)) = true → r.val * 7 + c.val - 6 = r.val * 7 + (next7 c).val) r c)
    ((by decide : ∀ r c : Fin 7, (decide (6 ≤ r.val * 7 + c.val) && (4432676798593 : Nat).testBit (r.val * 7 + c.val - 6)) = decide (c = 6)) r c)
  rw [e1, e2, e3, e4]
  have hbool : ∀ (a b d f0 f6 : Bool),
      (b || (((!f0 && a) || (f0 && a)) || ((!f6 && d) || (f6 && d)))) = (a || b || d) := by decide
  have hf0 : decide (c ≠ 0) = !decide (c = 0) := by by_cases h : c = 0 <;> simp [h]
  have hf6 : decide (c ≠ 6) = !decide (c = 6) := by by_cases h : c = 6 <;> simp [h]
  rw [hf0, hf6]; exact hbool _ _ _ _ _

private lemma get49_vNbr (h : Nat) (r c : Fin 7) :
    get49 (vNbr49 h) r c = (get49 h (prev7 r) c || get49 h r c || get49 h (next7 r) c) := by
  unfold get49 vNbr49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]
  have e1 := bit_shiftL_masked h 4398046511103 7 (r.val * 7 + c.val) ((prev7 r).val * 7 + c.val) (decide (r ≠ 0))
    ((by decide : ∀ r c : Fin 7, (decide (7 ≤ r.val * 7 + c.val) && (4398046511103 : Nat).testBit (r.val * 7 + c.val - 7)) = true → r.val * 7 + c.val - 7 = (prev7 r).val * 7 + c.val) r c)
    ((by decide : ∀ r c : Fin 7, (decide (7 ≤ r.val * 7 + c.val) && (4398046511103 : Nat).testBit (r.val * 7 + c.val - 7)) = decide (r ≠ 0)) r c)
  have e2 := bit_shiftR_masked h 558551906910208 42 (r.val * 7 + c.val) ((prev7 r).val * 7 + c.val) (decide (r = 0))
    ((by decide : ∀ r c : Fin 7, (558551906910208 : Nat).testBit (42 + (r.val * 7 + c.val)) = true → 42 + (r.val * 7 + c.val) = (prev7 r).val * 7 + c.val) r c)
    ((by decide : ∀ r c : Fin 7, (558551906910208 : Nat).testBit (42 + (r.val * 7 + c.val)) = decide (r = 0)) r c)
  have e3 := bit_shiftR_masked h 562949953421184 7 (r.val * 7 + c.val) ((next7 r).val * 7 + c.val) (decide (r ≠ 6))
    ((by decide : ∀ r c : Fin 7, (562949953421184 : Nat).testBit (7 + (r.val * 7 + c.val)) = true → 7 + (r.val * 7 + c.val) = (next7 r).val * 7 + c.val) r c)
    ((by decide : ∀ r c : Fin 7, (562949953421184 : Nat).testBit (7 + (r.val * 7 + c.val)) = decide (r ≠ 6)) r c)
  have e4 := bit_shiftL_masked h 127 42 (r.val * 7 + c.val) ((next7 r).val * 7 + c.val) (decide (r = 6))
    ((by decide : ∀ r c : Fin 7, (decide (42 ≤ r.val * 7 + c.val) && (127 : Nat).testBit (r.val * 7 + c.val - 42)) = true → r.val * 7 + c.val - 42 = (next7 r).val * 7 + c.val) r c)
    ((by decide : ∀ r c : Fin 7, (decide (42 ≤ r.val * 7 + c.val) && (127 : Nat).testBit (r.val * 7 + c.val - 42)) = decide (r = 6)) r c)
  rw [e1, e2, e3, e4]
  have hbool : ∀ (a b d f0 f6 : Bool),
      (b || (((!f0 && a) || (f0 && a)) || ((!f6 && d) || (f6 && d)))) = (a || b || d) := by decide
  have hf0 : decide (r ≠ 0) = !decide (r = 0) := by by_cases h : r = 0 <;> simp [h]
  have hf6 : decide (r ≠ 6) = !decide (r = 6) := by by_cases h : r = 6 <;> simp [h]
  rw [hf0, hf6]; exact hbool _ _ _ _ _

private lemma closedNbr49_get (m : Nat) (r c : Fin 7) :
    get49 (closedNbr49 m) r c = true ↔
      ∃ r' c' : Fin 7, get49 m r' c' = true ∧
        (toZ7 r' = toZ7 r ∨ C7.Adj (toZ7 r') (toZ7 r)) ∧
        (toZ7 c' = toZ7 c ∨ C7.Adj (toZ7 c') (toZ7 c)) := by
  unfold closedNbr49; rw [seqN_eq, get49_vNbr, get49_hNbr, get49_hNbr, get49_hNbr]
  simp only [Bool.or_eq_true, c7Close_iff, or_assoc]
  constructor
  · rintro (h | h | h | h | h | h | h | h | h)
    · exact ⟨prev7 r, prev7 c, h, Or.inl rfl, Or.inl rfl⟩
    · exact ⟨prev7 r, c, h, Or.inl rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨prev7 r, next7 c, h, Or.inl rfl, Or.inr (Or.inr rfl)⟩
    · exact ⟨r, prev7 c, h, Or.inr (Or.inl rfl), Or.inl rfl⟩
    · exact ⟨r, c, h, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩
    · exact ⟨r, next7 c, h, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
    · exact ⟨next7 r, prev7 c, h, Or.inr (Or.inr rfl), Or.inl rfl⟩
    · exact ⟨next7 r, c, h, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
    · exact ⟨next7 r, next7 c, h, Or.inr (Or.inr rfl), Or.inr (Or.inr rfl)⟩
  · rintro ⟨r', c', hm, hr, hc⟩
    rcases hr with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;> simp [hm]

private def mkRowFinset (S : Finset (ZMod 7 × ZMod 7)) (r : ZMod 7) : Nat :=
  (if (r, 0) ∈ S then 1 else 0) ||| (if (r, 1) ∈ S then 2 else 0) |||
  (if (r, 2) ∈ S then 4 else 0) ||| (if (r, 3) ∈ S then 8 else 0) |||
  (if (r, 4) ∈ S then 16 else 0) ||| (if (r, 5) ∈ S then 32 else 0) |||
  (if (r, 6) ∈ S then 64 else 0)

private def ofFinset49 (S : Finset (ZMod 7 × ZMod 7)) : Nat :=
  mkRowFinset S 0 ||| (mkRowFinset S 1 <<< 7) ||| (mkRowFinset S 2 <<< 14) |||
  (mkRowFinset S 3 <<< 21) ||| (mkRowFinset S 4 <<< 28) |||
  (mkRowFinset S 5 <<< 35) ||| (mkRowFinset S 6 <<< 42)

private lemma mkRowFinset_lt (S : Finset (ZMod 7 × ZMod 7)) (r : ZMod 7) :
    mkRowFinset S r < 128 := by
  change mkRowFinset S r < 2 ^ 7
  unfold mkRowFinset
  repeat apply Nat.or_lt_two_pow
  all_goals (split_ifs <;> decide)

private lemma ofFinset49_lt (S : Finset (ZMod 7 × ZMod 7)) : ofFinset49 S < 2 ^ 49 := by
  have hsh : ∀ (r : ZMod 7) (k : Nat), k ≤ 42 → mkRowFinset S r <<< k < 2 ^ 49 := by
    intro r k hk
    rw [Nat.shiftLeft_eq]
    have h1 := mkRowFinset_lt S r
    have h2 : 2 ^ k ≤ 2 ^ 42 := pow2_mono hk
    calc mkRowFinset S r * 2 ^ k < 128 * 2 ^ k := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ ≤ 128 * 2 ^ 42 := Nat.mul_le_mul_left 128 h2
      _ = 2 ^ 49 := by decide
  have h0 : mkRowFinset S 0 < 2 ^ 49 := lt_trans (mkRowFinset_lt S 0) (by decide)
  unfold ofFinset49
  exact or_lt49 (or_lt49 (or_lt49 (or_lt49 (or_lt49 (or_lt49 h0 (hsh 1 7 (by decide)))
    (hsh 2 14 (by decide))) (hsh 3 21 (by decide))) (hsh 4 28 (by decide)))
    (hsh 5 35 (by decide))) (hsh 6 42 (by decide))

private lemma mkRowFinset_testBit (S : Finset (ZMod 7 × ZMod 7)) (r : ZMod 7) (c : Fin 7) :
    (mkRowFinset S r).testBit c.val = decide ((r, toZ7 c) ∈ S) := by
  unfold mkRowFinset
  simp only [Nat.testBit_or]
  have hbit : ∀ (b : ZMod 7) (k v : Nat), ((if (r, b) ∈ S then v else 0).testBit k) =
      (decide ((r, b) ∈ S) && v.testBit k) := by
    intro b k v; by_cases h : (r, b) ∈ S <;> simp [h]
  simp only [hbit]
  revert c
  exact fin7_cases
    (by simp [toZ7, show (1:Nat).testBit 0 = true by decide, show (2:Nat).testBit 0 = false by decide,
              show (4:Nat).testBit 0 = false by decide, show (8:Nat).testBit 0 = false by decide,
              show (16:Nat).testBit 0 = false by decide, show (32:Nat).testBit 0 = false by decide,
              show (64:Nat).testBit 0 = false by decide])
    (by simp [toZ7, show (1:Nat).testBit 1 = false by decide, show (2:Nat).testBit 1 = true by decide,
              show (4:Nat).testBit 1 = false by decide, show (8:Nat).testBit 1 = false by decide,
              show (16:Nat).testBit 1 = false by decide, show (32:Nat).testBit 1 = false by decide,
              show (64:Nat).testBit 1 = false by decide])
    (by simp [toZ7, show (1:Nat).testBit 2 = false by decide, show (2:Nat).testBit 2 = false by decide,
              show (4:Nat).testBit 2 = true by decide, show (8:Nat).testBit 2 = false by decide,
              show (16:Nat).testBit 2 = false by decide, show (32:Nat).testBit 2 = false by decide,
              show (64:Nat).testBit 2 = false by decide])
    (by simp [toZ7, show (1:Nat).testBit 3 = false by decide, show (2:Nat).testBit 3 = false by decide,
              show (4:Nat).testBit 3 = false by decide, show (8:Nat).testBit 3 = true by decide,
              show (16:Nat).testBit 3 = false by decide, show (32:Nat).testBit 3 = false by decide,
              show (64:Nat).testBit 3 = false by decide])
    (by simp [toZ7, show (1:Nat).testBit 4 = false by decide, show (2:Nat).testBit 4 = false by decide,
              show (4:Nat).testBit 4 = false by decide, show (8:Nat).testBit 4 = false by decide,
              show (16:Nat).testBit 4 = true by decide, show (32:Nat).testBit 4 = false by decide,
              show (64:Nat).testBit 4 = false by decide])
    (by simp [toZ7, show (1:Nat).testBit 5 = false by decide, show (2:Nat).testBit 5 = false by decide,
              show (4:Nat).testBit 5 = false by decide, show (8:Nat).testBit 5 = false by decide,
              show (16:Nat).testBit 5 = false by decide, show (32:Nat).testBit 5 = true by decide,
              show (64:Nat).testBit 5 = false by decide])
    (by simp [toZ7, show (1:Nat).testBit 6 = false by decide, show (2:Nat).testBit 6 = false by decide,
              show (4:Nat).testBit 6 = false by decide, show (8:Nat).testBit 6 = false by decide,
              show (16:Nat).testBit 6 = false by decide, show (32:Nat).testBit 6 = false by decide,
              show (64:Nat).testBit 6 = true by decide])

private lemma get49_ofFinset (S : Finset (ZMod 7 × ZMod 7)) (r c : Fin 7) :
    get49 (ofFinset49 S) r c = true ↔ (toZ7 r, toZ7 c) ∈ S := by
  have hhi : ∀ (x : ZMod 7) (i : Nat), 7 ≤ i → (mkRowFinset S x).testBit i = false :=
    fun x i hi => Nat.testBit_lt_two_pow (lt_of_lt_of_le (mkRowFinset_lt S x) (pow2_mono hi))
  unfold get49 ofFinset49
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have hcalc : ((mkRowFinset S 0).testBit (r.val * 7 + c.val) ||
      (decide (r.val * 7 + c.val ≥ 7) && (mkRowFinset S 1).testBit (r.val * 7 + c.val - 7)) ||
      (decide (r.val * 7 + c.val ≥ 14) && (mkRowFinset S 2).testBit (r.val * 7 + c.val - 14)) ||
      (decide (r.val * 7 + c.val ≥ 21) && (mkRowFinset S 3).testBit (r.val * 7 + c.val - 21)) ||
      (decide (r.val * 7 + c.val ≥ 28) && (mkRowFinset S 4).testBit (r.val * 7 + c.val - 28)) ||
      (decide (r.val * 7 + c.val ≥ 35) && (mkRowFinset S 5).testBit (r.val * 7 + c.val - 35)) ||
      (decide (r.val * 7 + c.val ≥ 42) && (mkRowFinset S 6).testBit (r.val * 7 + c.val - 42))) =
      (mkRowFinset S (toZ7 r)).testBit c.val := by
    have hc := c.isLt
    rcases r with ⟨rv, hrv⟩
    have hrv' : rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 ∨ rv = 4 ∨ rv = 5 ∨ rv = 6 := by omega
    rcases hrv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · dsimp only
      simp only [toZ7, Nat.zero_mul, Nat.zero_add, Nat.cast_zero,
        show ¬(c.val ≥ 7) by omega, show ¬(c.val ≥ 14) by omega, show ¬(c.val ≥ 21) by omega,
        show ¬(c.val ≥ 28) by omega, show ¬(c.val ≥ 35) by omega, show ¬(c.val ≥ 42) by omega,
        decide_false, Bool.false_and, Bool.or_false]
    · dsimp only
      simp only [toZ7, Nat.one_mul, Nat.cast_one, hhi 0 (7 + c.val) (by omega),
        show 7 + c.val ≥ 7 by omega, show ¬(7 + c.val ≥ 14) by omega, show ¬(7 + c.val ≥ 21) by omega,
        show ¬(7 + c.val ≥ 28) by omega, show ¬(7 + c.val ≥ 35) by omega, show ¬(7 + c.val ≥ 42) by omega,
        decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]
    · dsimp only
      simp only [toZ7, show (2 : Nat) * 7 = 14 by decide, show ((2 : Nat) : ZMod 7) = 2 by rfl,
        hhi 0 (14 + c.val) (by omega), hhi 1 (14 + c.val - 7) (by omega),
        show 14 + c.val ≥ 7 by omega, show 14 + c.val ≥ 14 by omega, show ¬(14 + c.val ≥ 21) by omega,
        show ¬(14 + c.val ≥ 28) by omega, show ¬(14 + c.val ≥ 35) by omega, show ¬(14 + c.val ≥ 42) by omega,
        decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]
    · dsimp only
      simp only [toZ7, show (3 : Nat) * 7 = 21 by decide, show ((3 : Nat) : ZMod 7) = 3 by rfl,
        hhi 0 (21 + c.val) (by omega), hhi 1 (21 + c.val - 7) (by omega), hhi 2 (21 + c.val - 14) (by omega),
        show 21 + c.val ≥ 7 by omega, show 21 + c.val ≥ 14 by omega, show 21 + c.val ≥ 21 by omega,
        show ¬(21 + c.val ≥ 28) by omega, show ¬(21 + c.val ≥ 35) by omega, show ¬(21 + c.val ≥ 42) by omega,
        decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]
    · dsimp only
      simp only [toZ7, show (4 : Nat) * 7 = 28 by decide, show ((4 : Nat) : ZMod 7) = 4 by rfl,
        hhi 0 (28 + c.val) (by omega), hhi 1 (28 + c.val - 7) (by omega), hhi 2 (28 + c.val - 14) (by omega),
        hhi 3 (28 + c.val - 21) (by omega),
        show 28 + c.val ≥ 7 by omega, show 28 + c.val ≥ 14 by omega, show 28 + c.val ≥ 21 by omega,
        show 28 + c.val ≥ 28 by omega, show ¬(28 + c.val ≥ 35) by omega, show ¬(28 + c.val ≥ 42) by omega,
        decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]
    · dsimp only
      simp only [toZ7, show (5 : Nat) * 7 = 35 by decide, show ((5 : Nat) : ZMod 7) = 5 by rfl,
        hhi 0 (35 + c.val) (by omega), hhi 1 (35 + c.val - 7) (by omega), hhi 2 (35 + c.val - 14) (by omega),
        hhi 3 (35 + c.val - 21) (by omega), hhi 4 (35 + c.val - 28) (by omega),
        show 35 + c.val ≥ 7 by omega, show 35 + c.val ≥ 14 by omega, show 35 + c.val ≥ 21 by omega,
        show 35 + c.val ≥ 28 by omega, show 35 + c.val ≥ 35 by omega, show ¬(35 + c.val ≥ 42) by omega,
        decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]
    · dsimp only
      simp only [toZ7, show (6 : Nat) * 7 = 42 by decide, show ((6 : Nat) : ZMod 7) = 6 by rfl,
        hhi 0 (42 + c.val) (by omega), hhi 1 (42 + c.val - 7) (by omega), hhi 2 (42 + c.val - 14) (by omega),
        hhi 3 (42 + c.val - 21) (by omega), hhi 4 (42 + c.val - 28) (by omega), hhi 5 (42 + c.val - 35) (by omega),
        show 42 + c.val ≥ 7 by omega, show 42 + c.val ≥ 14 by omega, show 42 + c.val ≥ 21 by omega,
        show 42 + c.val ≥ 28 by omega, show 42 + c.val ≥ 35 by omega, show 42 + c.val ≥ 42 by omega,
        decide_true, Bool.true_and, Bool.false_or, Nat.add_sub_cancel_left]
  rw [hcalc, mkRowFinset_testBit, decide_eq_true_iff]

private def fin7SqEquivZ7Sq : (Fin 7 × Fin 7) ≃ (ZMod 7 × ZMod 7) :=
  Equiv.mk
    (fun p => (toZ7 p.1, toZ7 p.2))
    (fun q => (ofZ7 q.1, ofZ7 q.2))
    (fun ⟨a, b⟩ => Prod.ext (ofZ7_toZ7 a) (ofZ7_toZ7 b))
    (fun ⟨a, b⟩ => Prod.ext (toZ7_ofZ7 a) (toZ7_ofZ7 b))

private lemma pop49_ofFinset (S : Finset (ZMod 7 × ZMod 7)) :
    pop49 (ofFinset49 S) = S.card := by
  rw [pop49_eq_sum]
  have h1 : (∑ r : Fin 7, ∑ c : Fin 7, (get49 (ofFinset49 S) r c).toNat) =
      ∑ p : Fin 7 × Fin 7, if fin7SqEquivZ7Sq p ∈ S then 1 else 0 := by
    rw [← Fintype.sum_prod_type']
    refine Finset.sum_congr rfl fun p _ => ?_
    change (get49 (ofFinset49 S) p.1 p.2).toNat = if (toZ7 p.1, toZ7 p.2) ∈ S then 1 else 0
    by_cases hp : (toZ7 p.1, toZ7 p.2) ∈ S
    · simp [hp, (get49_ofFinset S p.1 p.2).mpr hp]
    · have hg : get49 (ofFinset49 S) p.1 p.2 = false :=
        Bool.eq_false_iff.mpr fun h => hp ((get49_ofFinset S p.1 p.2).mp h)
      simp [hp, hg]
  rw [h1]
  have h2 : (∑ p : Fin 7 × Fin 7, if fin7SqEquivZ7Sq p ∈ S then 1 else 0) =
      ∑ q : ZMod 7 × ZMod 7, if q ∈ S then 1 else 0 :=
    Equiv.sum_comp fin7SqEquivZ7Sq (fun q => if q ∈ S then 1 else 0)
  rw [h2]; simp

private lemma ofFinset49_union (A B : Finset (ZMod 7 × ZMod 7)) :
    ofFinset49 (A ∪ B) = ofFinset49 A ||| ofFinset49 B := by
  apply ext49 (ofFinset49_lt _) (or_lt49 (ofFinset49_lt _) (ofFinset49_lt _))
  intro r c
  rw [get49_or, Bool.eq_iff_iff, Bool.or_eq_true, get49_ofFinset, get49_ofFinset, get49_ofFinset, Finset.mem_union]

private lemma ofFinset49_sdiff (A B : Finset (ZMod 7 × ZMod 7)) :
    ofFinset49 (A \ B) = diff49 (ofFinset49 A) (ofFinset49 B) := by
  apply ext49 (ofFinset49_lt _) (diff49_lt (ofFinset49_lt _))
  intro r c
  rw [get49_diff, Bool.eq_iff_iff, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      get49_ofFinset, get49_ofFinset, get49_ofFinset, Finset.mem_sdiff]

private lemma ofFinset49_subset_of_subset {A B : Finset (ZMod 7 × ZMod 7)} (h : A ⊆ B) :
    subset49 (ofFinset49 A) (ofFinset49 B) = true := by
  rw [subset49_iff (ofFinset49_lt _)]
  intro r c ha
  exact (get49_ofFinset B r c).mpr (h ((get49_ofFinset A r c).mp ha))

private lemma disjoint49_closedNbr_of_indep {A B : Finset (ZMod 7 × ZMod 7)}
    (hdisj : Disjoint A B)
    (hind : (C7 ⊠ C7).IsIndepSet ((A ∪ B : Finset (ZMod 7 × ZMod 7)) : Set (ZMod 7 × ZMod 7))) :
    disjoint49 (ofFinset49 B) (closedNbr49 (ofFinset49 A)) = true := by
  rw [disjoint49_iff (ofFinset49_lt _)]
  intro r c hb
  have hb' : (toZ7 r, toZ7 c) ∈ B := (get49_ofFinset B r c).mp hb
  cases hc : get49 (closedNbr49 (ofFinset49 A)) r c
  · rfl
  · exfalso
    obtain ⟨r', c', ha, hr, hc'⟩ := (closedNbr49_get _ r c).mp hc
    have ha' : (toZ7 r', toZ7 c') ∈ A := (get49_ofFinset A r' c').mp ha
    have hne : (toZ7 r', toZ7 c') ≠ (toZ7 r, toZ7 c) := fun heq =>
      Finset.disjoint_left.mp hdisj ha' (heq ▸ hb')
    have hadj : (C7 ⊠ C7).Adj (toZ7 r', toZ7 c') (toZ7 r, toZ7 c) := ⟨hne, hr, hc'⟩
    exact hind (Finset.mem_coe.mpr (Finset.mem_union_left B ha'))
      (Finset.mem_coe.mpr (Finset.mem_union_right A hb')) hne hadj

/-! ## Section 2: `Aut(C₇ ⊠ C₇)` (Order 392) via C++-Speed 49-Bit Permutations -/

private def flipRow49 (m : Nat) : Nat :=
  Nat.lor (Nat.land m 127)
  (Nat.lor (Nat.shiftLeft (Nat.land m 16256) 35)
  (Nat.lor (Nat.shiftLeft (Nat.land m 2080768) 21)
  (Nat.lor (Nat.shiftLeft (Nat.land m 266338304) 7)
  (Nat.lor (Nat.shiftRight (Nat.land m 34091302912) 7)
  (Nat.lor (Nat.shiftRight (Nat.land m 4363686772736) 21)
           (Nat.shiftRight (Nat.land m 558551906910208) 35))))))

private def shiftRow49 (t : Fin 7) (m : Nat) : Nat :=
  match t.val with
  | 0 => m
  | 1 => Nat.lor (Nat.shiftLeft (Nat.land m 4398046511103) 7)  (Nat.shiftRight (Nat.land m 558551906910208) 42)
  | 2 => Nat.lor (Nat.shiftLeft (Nat.land m 34359738367) 14) (Nat.shiftRight (Nat.land m 562915593682944) 35)
  | 3 => Nat.lor (Nat.shiftLeft (Nat.land m 268435455) 21) (Nat.shiftRight (Nat.land m 562949684985856) 28)
  | 4 => Nat.lor (Nat.shiftLeft (Nat.land m 2097151) 28) (Nat.shiftRight (Nat.land m 562949951324160) 21)
  | 5 => Nat.lor (Nat.shiftLeft (Nat.land m 16383) 35) (Nat.shiftRight (Nat.land m 562949953404928) 14)
  | _ => Nat.lor (Nat.shiftLeft (Nat.land m 127) 42) (Nat.shiftRight (Nat.land m 562949953421184) 7)

private def flipCol49 (m : Nat) : Nat :=
  Nat.lor (Nat.land m 4432676798593)
  (Nat.lor (Nat.shiftLeft (Nat.land m 8865353597186) 5)
  (Nat.lor (Nat.shiftLeft (Nat.land m 17730707194372) 3)
  (Nat.lor (Nat.shiftLeft (Nat.land m 35461414388744) 1)
  (Nat.lor (Nat.shiftRight (Nat.land m 70922828777488) 1)
  (Nat.lor (Nat.shiftRight (Nat.land m 141845657554976) 3)
           (Nat.shiftRight (Nat.land m 283691315109952) 5))))))

private def shiftCol49 (t : Fin 7) (m : Nat) : Nat :=
  match t.val with
  | 0 => m
  | 1 => Nat.lor (Nat.shiftLeft (Nat.land m 279258638311359) 1) (Nat.shiftRight (Nat.land m 283691315109952) 6)
  | 2 => Nat.lor (Nat.shiftLeft (Nat.land m 137412980756383) 2) (Nat.shiftRight (Nat.land m 425536972664928) 5)
  | 3 => Nat.lor (Nat.shiftLeft (Nat.land m 66490151978895) 3) (Nat.shiftRight (Nat.land m 496459801442416) 4)
  | 4 => Nat.lor (Nat.shiftLeft (Nat.land m 31028737590151) 4) (Nat.shiftRight (Nat.land m 531921215831160) 3)
  | 5 => Nat.lor (Nat.shiftLeft (Nat.land m 13298030395779) 5) (Nat.shiftRight (Nat.land m 549651923025532) 2)
  | _ => Nat.lor (Nat.shiftLeft (Nat.land m 4432676798593) 6) (Nat.shiftRight (Nat.land m 558517276622718) 1)

private def transpose49 (m : Nat) : Nat :=
  Nat.lor (Nat.land m 282578800148737)
  (Nat.lor (Nat.shiftLeft (Nat.land m 2207646876162) 6)
  (Nat.lor (Nat.shiftLeft (Nat.land m 17247241220) 12)
  (Nat.lor (Nat.shiftLeft (Nat.land m 134744072) 18)
  (Nat.lor (Nat.shiftLeft (Nat.land m 1052688) 24)
  (Nat.lor (Nat.shiftLeft (Nat.land m 8224) 30)
  (Nat.lor (Nat.shiftLeft (Nat.land m 64) 36)
  (Nat.lor (Nat.shiftRight (Nat.land m 141289400074368) 6)
  (Nat.lor (Nat.shiftRight (Nat.land m 70644700037120) 12)
  (Nat.lor (Nat.shiftRight (Nat.land m 35322350010368) 18)
  (Nat.lor (Nat.shiftRight (Nat.land m 17661173956608) 24)
  (Nat.lor (Nat.shiftRight (Nat.land m 8830452760576) 30)
           (Nat.shiftRight (Nat.land m 4398046511104) 36))))))))))))

private lemma shiftL_lt_of_mask {m mask k bound : Nat}
    (hm : mask < 2 ^ bound) (hk : bound + k ≤ 49) : (m &&& mask) <<< k < 2 ^ 49 :=
  shiftL_and_lt49 m mask k fun i hi => by
    rw [Nat.testBit_shiftLeft, Nat.testBit_and]
    have hb : mask.testBit (i - k) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (pow2_mono (by omega)))
    simp [hb]

private lemma flipRow49_lt (m : Nat) : flipRow49 m < 2 ^ 49 := by
  unfold flipRow49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  exact or_lt49 (and_lt49 (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 14) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 21) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 28) (by decide) (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 7 (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 21 (by decide))
             (shiftR_and_lt49 _ _ 35 (by decide)))))))

private lemma shiftRow49_lt (t : Fin 7) {m : Nat} (hm : m < 2 ^ 49) : shiftRow49 t m < 2 ^ 49 := by
  unfold shiftRow49
  revert t
  refine fin7_cases hm ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 42) (by decide) (by decide)) (shiftR_and_lt49 _ _ 42 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 35) (by decide) (by decide)) (shiftR_and_lt49 _ _ 35 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 28) (by decide) (by decide)) (shiftR_and_lt49 _ _ 28 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 21) (by decide) (by decide)) (shiftR_and_lt49 _ _ 21 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 14) (by decide) (by decide)) (shiftR_and_lt49 _ _ 14 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 7)  (by decide) (by decide)) (shiftR_and_lt49 _ _ 7  (by decide))

private lemma flipCol49_lt (m : Nat) : flipCol49 m < 2 ^ 49 := by
  unfold flipCol49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  exact or_lt49 (and_lt49 (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 44) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 45) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 46) (by decide) (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 1 (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 3 (by decide))
             (shiftR_and_lt49 _ _ 5 (by decide)))))))

private lemma shiftCol49_lt (t : Fin 7) {m : Nat} (hm : m < 2 ^ 49) : shiftCol49 t m < 2 ^ 49 := by
  unfold shiftCol49
  revert t
  refine fin7_cases hm ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 48) (by decide) (by decide)) (shiftR_and_lt49 _ _ 6 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 47) (by decide) (by decide)) (shiftR_and_lt49 _ _ 5 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 46) (by decide) (by decide)) (shiftR_and_lt49 _ _ 4 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 45) (by decide) (by decide)) (shiftR_and_lt49 _ _ 3 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 44) (by decide) (by decide)) (shiftR_and_lt49 _ _ 2 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 43) (by decide) (by decide)) (shiftR_and_lt49 _ _ 1 (by decide))

private lemma transpose49_lt (m : Nat) : transpose49 m < 2 ^ 49 := by
  unfold transpose49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  exact or_lt49 (and_lt49 (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 42) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 35) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 28) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 21) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 14) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 7)  (by decide) (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 6  (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 12 (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 18 (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 24 (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 30 (by decide))
             (shiftR_and_lt49 _ _ 36 (by decide)))))))))))))

private lemma get49_flipRow (m : Nat) (r c : Fin 7) :
    get49 (flipRow49 m) (neg7 r) c = get49 m r c := by
  unfold get49 flipRow49
  let dst := (neg7 r).val * 7 + c.val
  let src := r.val * 7 + c.val
  change ((m &&& 127) ||| (((m &&& 16256) <<< 35) ||| (((m &&& 2080768) <<< 21) |||
    (((m &&& 266338304) <<< 7) ||| (((m &&& 34091302912) >>> 7) ||| (((m &&& 4363686772736) >>> 21) |||
    ((m &&& 558551906910208) >>> 35))))))).testBit dst = m.testBit src
  simp only [Nat.testBit_or]
  rw [bit_and_masked m 127 dst src (decide (r = 0))
        ((by decide : ∀ r c : Fin 7, (127 : Nat).testBit ((neg7 r).val * 7 + c.val) = true → (neg7 r).val * 7 + c.val = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (127 : Nat).testBit ((neg7 r).val * 7 + c.val) = decide (r = 0)) r c),
      bit_shiftL_masked m 16256 35 dst src (decide (r = 1))
        ((by decide : ∀ r c : Fin 7, (decide (35 ≤ (neg7 r).val * 7 + c.val) && (16256 : Nat).testBit ((neg7 r).val * 7 + c.val - 35)) = true → (neg7 r).val * 7 + c.val - 35 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (35 ≤ (neg7 r).val * 7 + c.val) && (16256 : Nat).testBit ((neg7 r).val * 7 + c.val - 35)) = decide (r = 1)) r c),
      bit_shiftL_masked m 2080768 21 dst src (decide (r = 2))
        ((by decide : ∀ r c : Fin 7, (decide (21 ≤ (neg7 r).val * 7 + c.val) && (2080768 : Nat).testBit ((neg7 r).val * 7 + c.val - 21)) = true → (neg7 r).val * 7 + c.val - 21 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (21 ≤ (neg7 r).val * 7 + c.val) && (2080768 : Nat).testBit ((neg7 r).val * 7 + c.val - 21)) = decide (r = 2)) r c),
      bit_shiftL_masked m 266338304 7 dst src (decide (r = 3))
        ((by decide : ∀ r c : Fin 7, (decide (7 ≤ (neg7 r).val * 7 + c.val) && (266338304 : Nat).testBit ((neg7 r).val * 7 + c.val - 7)) = true → (neg7 r).val * 7 + c.val - 7 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (7 ≤ (neg7 r).val * 7 + c.val) && (266338304 : Nat).testBit ((neg7 r).val * 7 + c.val - 7)) = decide (r = 3)) r c),
      bit_shiftR_masked m 34091302912 7 dst src (decide (r = 4))
        ((by decide : ∀ r c : Fin 7, (34091302912 : Nat).testBit (7 + ((neg7 r).val * 7 + c.val)) = true → 7 + ((neg7 r).val * 7 + c.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (34091302912 : Nat).testBit (7 + ((neg7 r).val * 7 + c.val)) = decide (r = 4)) r c),
      bit_shiftR_masked m 4363686772736 21 dst src (decide (r = 5))
        ((by decide : ∀ r c : Fin 7, (4363686772736 : Nat).testBit (21 + ((neg7 r).val * 7 + c.val)) = true → 21 + ((neg7 r).val * 7 + c.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (4363686772736 : Nat).testBit (21 + ((neg7 r).val * 7 + c.val)) = decide (r = 5)) r c),
      bit_shiftR_masked m 558551906910208 35 dst src (decide (r = 6))
        ((by decide : ∀ r c : Fin 7, (558551906910208 : Nat).testBit (35 + ((neg7 r).val * 7 + c.val)) = true → 35 + ((neg7 r).val * 7 + c.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (558551906910208 : Nat).testBit (35 + ((neg7 r).val * 7 + c.val)) = decide (r = 6)) r c)]
  revert r; refine fin7_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

private lemma get49_shiftRow_aux (m lo hi : Nat) (t : Fin 7) (kL kR : Nat)
    (h1 : ∀ r c : Fin 7, (decide (kL ≤ (add7 r t).val * 7 + c.val) && lo.testBit ((add7 r t).val * 7 + c.val - kL)) = true →
          (add7 r t).val * 7 + c.val - kL = r.val * 7 + c.val)
    (h2 : ∀ r c : Fin 7, hi.testBit (kR + ((add7 r t).val * 7 + c.val)) = true →
          kR + ((add7 r t).val * 7 + c.val) = r.val * 7 + c.val)
    (h3 : ∀ r c : Fin 7, ((decide (kL ≤ (add7 r t).val * 7 + c.val) && lo.testBit ((add7 r t).val * 7 + c.val - kL)) ||
                          hi.testBit (kR + ((add7 r t).val * 7 + c.val))) = true)
    (r c : Fin 7) :
    get49 (((m &&& lo) <<< kL) ||| ((m &&& hi) >>> kR)) (add7 r t) c = get49 m r c := by
  unfold get49
  rw [Nat.testBit_or,
      bit_shiftL_masked m lo kL ((add7 r t).val * 7 + c.val) (r.val * 7 + c.val) _ (h1 r c) rfl,
      bit_shiftR_masked m hi kR ((add7 r t).val * 7 + c.val) (r.val * 7 + c.val) _ (h2 r c) rfl]
  have hf := h3 r c
  cases a : (decide (kL ≤ (add7 r t).val * 7 + c.val) && lo.testBit ((add7 r t).val * 7 + c.val - kL)) <;>
  cases b : hi.testBit (kR + ((add7 r t).val * 7 + c.val)) <;> simp_all

private lemma get49_shiftRow (t : Fin 7) (m : Nat) (r c : Fin 7) :
    get49 (shiftRow49 t m) (add7 r t) c = get49 m r c := by
  unfold shiftRow49
  revert t
  refine fin7_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have h0 : add7 r 0 = r := (by decide : ∀ x : Fin 7, add7 x 0 = x) r
    rw [h0]; rfl
  · exact get49_shiftRow_aux m 4398046511103 558551906910208 1 7  42 (by decide) (by decide) (by decide) r c
  · exact get49_shiftRow_aux m 34359738367 562915593682944 2 14 35 (by decide) (by decide) (by decide) r c
  · exact get49_shiftRow_aux m 268435455 562949684985856 3 21 28 (by decide) (by decide) (by decide) r c
  · exact get49_shiftRow_aux m 2097151 562949951324160 4 28 21 (by decide) (by decide) (by decide) r c
  · exact get49_shiftRow_aux m 16383 562949953404928 5 35 14 (by decide) (by decide) (by decide) r c
  · exact get49_shiftRow_aux m 127 562949953421184 6 42 7  (by decide) (by decide) (by decide) r c

private lemma get49_flipCol (m : Nat) (r c : Fin 7) :
    get49 (flipCol49 m) r (neg7 c) = get49 m r c := by
  unfold get49 flipCol49
  let dst := r.val * 7 + (neg7 c).val
  let src := r.val * 7 + c.val
  change ((m &&& 4432676798593) ||| (((m &&& 8865353597186) <<< 5) ||| (((m &&& 17730707194372) <<< 3) |||
    (((m &&& 35461414388744) <<< 1) ||| (((m &&& 70922828777488) >>> 1) ||| (((m &&& 141845657554976) >>> 3) |||
    ((m &&& 283691315109952) >>> 5))))))).testBit dst = m.testBit src
  simp only [Nat.testBit_or]
  rw [bit_and_masked m 4432676798593 dst src (decide (c = 0))
        ((by decide : ∀ r c : Fin 7, (4432676798593 : Nat).testBit (r.val * 7 + (neg7 c).val) = true → r.val * 7 + (neg7 c).val = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (4432676798593 : Nat).testBit (r.val * 7 + (neg7 c).val) = decide (c = 0)) r c),
      bit_shiftL_masked m 8865353597186 5 dst src (decide (c = 1))
        ((by decide : ∀ r c : Fin 7, (decide (5 ≤ r.val * 7 + (neg7 c).val) && (8865353597186 : Nat).testBit (r.val * 7 + (neg7 c).val - 5)) = true → r.val * 7 + (neg7 c).val - 5 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (5 ≤ r.val * 7 + (neg7 c).val) && (8865353597186 : Nat).testBit (r.val * 7 + (neg7 c).val - 5)) = decide (c = 1)) r c),
      bit_shiftL_masked m 17730707194372 3 dst src (decide (c = 2))
        ((by decide : ∀ r c : Fin 7, (decide (3 ≤ r.val * 7 + (neg7 c).val) && (17730707194372 : Nat).testBit (r.val * 7 + (neg7 c).val - 3)) = true → r.val * 7 + (neg7 c).val - 3 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (3 ≤ r.val * 7 + (neg7 c).val) && (17730707194372 : Nat).testBit (r.val * 7 + (neg7 c).val - 3)) = decide (c = 2)) r c),
      bit_shiftL_masked m 35461414388744 1 dst src (decide (c = 3))
        ((by decide : ∀ r c : Fin 7, (decide (1 ≤ r.val * 7 + (neg7 c).val) && (35461414388744 : Nat).testBit (r.val * 7 + (neg7 c).val - 1)) = true → r.val * 7 + (neg7 c).val - 1 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (1 ≤ r.val * 7 + (neg7 c).val) && (35461414388744 : Nat).testBit (r.val * 7 + (neg7 c).val - 1)) = decide (c = 3)) r c),
      bit_shiftR_masked m 70922828777488 1 dst src (decide (c = 4))
        ((by decide : ∀ r c : Fin 7, (70922828777488 : Nat).testBit (1 + (r.val * 7 + (neg7 c).val)) = true → 1 + (r.val * 7 + (neg7 c).val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (70922828777488 : Nat).testBit (1 + (r.val * 7 + (neg7 c).val)) = decide (c = 4)) r c),
      bit_shiftR_masked m 141845657554976 3 dst src (decide (c = 5))
        ((by decide : ∀ r c : Fin 7, (141845657554976 : Nat).testBit (3 + (r.val * 7 + (neg7 c).val)) = true → 3 + (r.val * 7 + (neg7 c).val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (141845657554976 : Nat).testBit (3 + (r.val * 7 + (neg7 c).val)) = decide (c = 5)) r c),
      bit_shiftR_masked m 283691315109952 5 dst src (decide (c = 6))
        ((by decide : ∀ r c : Fin 7, (283691315109952 : Nat).testBit (5 + (r.val * 7 + (neg7 c).val)) = true → 5 + (r.val * 7 + (neg7 c).val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (283691315109952 : Nat).testBit (5 + (r.val * 7 + (neg7 c).val)) = decide (c = 6)) r c)]
  revert c; refine fin7_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

private lemma get49_shiftCol_aux (m lo hi : Nat) (t : Fin 7) (kL kR : Nat)
    (h1 : ∀ r c : Fin 7, (decide (kL ≤ r.val * 7 + (add7 c t).val) && lo.testBit (r.val * 7 + (add7 c t).val - kL)) = true →
          r.val * 7 + (add7 c t).val - kL = r.val * 7 + c.val)
    (h2 : ∀ r c : Fin 7, hi.testBit (kR + (r.val * 7 + (add7 c t).val)) = true →
          kR + (r.val * 7 + (add7 c t).val) = r.val * 7 + c.val)
    (h3 : ∀ r c : Fin 7, ((decide (kL ≤ r.val * 7 + (add7 c t).val) && lo.testBit (r.val * 7 + (add7 c t).val - kL)) ||
                          hi.testBit (kR + (r.val * 7 + (add7 c t).val))) = true)
    (r c : Fin 7) :
    get49 (((m &&& lo) <<< kL) ||| ((m &&& hi) >>> kR)) r (add7 c t) = get49 m r c := by
  unfold get49
  rw [Nat.testBit_or,
      bit_shiftL_masked m lo kL (r.val * 7 + (add7 c t).val) (r.val * 7 + c.val) _ (h1 r c) rfl,
      bit_shiftR_masked m hi kR (r.val * 7 + (add7 c t).val) (r.val * 7 + c.val) _ (h2 r c) rfl]
  have hf := h3 r c
  cases a : (decide (kL ≤ r.val * 7 + (add7 c t).val) && lo.testBit (r.val * 7 + (add7 c t).val - kL)) <;>
  cases b : hi.testBit (kR + (r.val * 7 + (add7 c t).val)) <;> simp_all

private lemma get49_shiftCol (t : Fin 7) (m : Nat) (r c : Fin 7) :
    get49 (shiftCol49 t m) r (add7 c t) = get49 m r c := by
  unfold shiftCol49
  revert t
  refine fin7_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have h0 : add7 c 0 = c := (by decide : ∀ x : Fin 7, add7 x 0 = x) c
    rw [h0]; rfl
  · exact get49_shiftCol_aux m 279258638311359 283691315109952 1 1 6 (by decide) (by decide) (by decide) r c
  · exact get49_shiftCol_aux m 137412980756383 425536972664928 2 2 5 (by decide) (by decide) (by decide) r c
  · exact get49_shiftCol_aux m 66490151978895 496459801442416 3 3 4 (by decide) (by decide) (by decide) r c
  · exact get49_shiftCol_aux m 31028737590151 531921215831160 4 4 3 (by decide) (by decide) (by decide) r c
  · exact get49_shiftCol_aux m 13298030395779 549651923025532 5 5 2 (by decide) (by decide) (by decide) r c
  · exact get49_shiftCol_aux m 4432676798593 558517276622718 6 6 1 (by decide) (by decide) (by decide) r c

private lemma get49_transpose (m : Nat) (r c : Fin 7) :
    get49 (transpose49 m) c r = get49 m r c := by
  unfold get49 transpose49
  let dst := c.val * 7 + r.val
  let src := r.val * 7 + c.val
  change ((m &&& 282578800148737) ||| (((m &&& 2207646876162) <<< 6) ||| (((m &&& 17247241220) <<< 12) |||
    (((m &&& 134744072) <<< 18) ||| (((m &&& 1052688) <<< 24) ||| (((m &&& 8224) <<< 30) |||
    (((m &&& 64) <<< 36) ||| (((m &&& 141289400074368) >>> 6) ||| (((m &&& 70644700037120) >>> 12) |||
    (((m &&& 35322350010368) >>> 18) ||| (((m &&& 17661173956608) >>> 24) ||| (((m &&& 8830452760576) >>> 30) |||
    ((m &&& 4398046511104) >>> 36))))))))))))).testBit dst = m.testBit src
  simp only [Nat.testBit_or]
  rw [bit_and_masked m 282578800148737 dst src (decide (r.val = c.val))
        ((by decide : ∀ r c : Fin 7, (282578800148737 : Nat).testBit (c.val * 7 + r.val) = true → c.val * 7 + r.val = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (282578800148737 : Nat).testBit (c.val * 7 + r.val) = decide (r.val = c.val)) r c),
      bit_shiftL_masked m 2207646876162 6 dst src (decide (r.val + 1 = c.val))
        ((by decide : ∀ r c : Fin 7, (decide (6 ≤ c.val * 7 + r.val) && (2207646876162 : Nat).testBit (c.val * 7 + r.val - 6)) = true → c.val * 7 + r.val - 6 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (6 ≤ c.val * 7 + r.val) && (2207646876162 : Nat).testBit (c.val * 7 + r.val - 6)) = decide (r.val + 1 = c.val)) r c),
      bit_shiftL_masked m 17247241220 12 dst src (decide (r.val + 2 = c.val))
        ((by decide : ∀ r c : Fin 7, (decide (12 ≤ c.val * 7 + r.val) && (17247241220 : Nat).testBit (c.val * 7 + r.val - 12)) = true → c.val * 7 + r.val - 12 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (12 ≤ c.val * 7 + r.val) && (17247241220 : Nat).testBit (c.val * 7 + r.val - 12)) = decide (r.val + 2 = c.val)) r c),
      bit_shiftL_masked m 134744072 18 dst src (decide (r.val + 3 = c.val))
        ((by decide : ∀ r c : Fin 7, (decide (18 ≤ c.val * 7 + r.val) && (134744072 : Nat).testBit (c.val * 7 + r.val - 18)) = true → c.val * 7 + r.val - 18 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (18 ≤ c.val * 7 + r.val) && (134744072 : Nat).testBit (c.val * 7 + r.val - 18)) = decide (r.val + 3 = c.val)) r c),
      bit_shiftL_masked m 1052688 24 dst src (decide (r.val + 4 = c.val))
        ((by decide : ∀ r c : Fin 7, (decide (24 ≤ c.val * 7 + r.val) && (1052688 : Nat).testBit (c.val * 7 + r.val - 24)) = true → c.val * 7 + r.val - 24 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (24 ≤ c.val * 7 + r.val) && (1052688 : Nat).testBit (c.val * 7 + r.val - 24)) = decide (r.val + 4 = c.val)) r c),
      bit_shiftL_masked m 8224 30 dst src (decide (r.val + 5 = c.val))
        ((by decide : ∀ r c : Fin 7, (decide (30 ≤ c.val * 7 + r.val) && (8224 : Nat).testBit (c.val * 7 + r.val - 30)) = true → c.val * 7 + r.val - 30 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (30 ≤ c.val * 7 + r.val) && (8224 : Nat).testBit (c.val * 7 + r.val - 30)) = decide (r.val + 5 = c.val)) r c),
      bit_shiftL_masked m 64 36 dst src (decide (r.val + 6 = c.val))
        ((by decide : ∀ r c : Fin 7, (decide (36 ≤ c.val * 7 + r.val) && (64 : Nat).testBit (c.val * 7 + r.val - 36)) = true → c.val * 7 + r.val - 36 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (36 ≤ c.val * 7 + r.val) && (64 : Nat).testBit (c.val * 7 + r.val - 36)) = decide (r.val + 6 = c.val)) r c),
      bit_shiftR_masked m 141289400074368 6 dst src (decide (c.val + 1 = r.val))
        ((by decide : ∀ r c : Fin 7, (141289400074368 : Nat).testBit (6 + (c.val * 7 + r.val)) = true → 6 + (c.val * 7 + r.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (141289400074368 : Nat).testBit (6 + (c.val * 7 + r.val)) = decide (c.val + 1 = r.val)) r c),
      bit_shiftR_masked m 70644700037120 12 dst src (decide (c.val + 2 = r.val))
        ((by decide : ∀ r c : Fin 7, (70644700037120 : Nat).testBit (12 + (c.val * 7 + r.val)) = true → 12 + (c.val * 7 + r.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (70644700037120 : Nat).testBit (12 + (c.val * 7 + r.val)) = decide (c.val + 2 = r.val)) r c),
      bit_shiftR_masked m 35322350010368 18 dst src (decide (c.val + 3 = r.val))
        ((by decide : ∀ r c : Fin 7, (35322350010368 : Nat).testBit (18 + (c.val * 7 + r.val)) = true → 18 + (c.val * 7 + r.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (35322350010368 : Nat).testBit (18 + (c.val * 7 + r.val)) = decide (c.val + 3 = r.val)) r c),
      bit_shiftR_masked m 17661173956608 24 dst src (decide (c.val + 4 = r.val))
        ((by decide : ∀ r c : Fin 7, (17661173956608 : Nat).testBit (24 + (c.val * 7 + r.val)) = true → 24 + (c.val * 7 + r.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (17661173956608 : Nat).testBit (24 + (c.val * 7 + r.val)) = decide (c.val + 4 = r.val)) r c),
      bit_shiftR_masked m 8830452760576 30 dst src (decide (c.val + 5 = r.val))
        ((by decide : ∀ r c : Fin 7, (8830452760576 : Nat).testBit (30 + (c.val * 7 + r.val)) = true → 30 + (c.val * 7 + r.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (8830452760576 : Nat).testBit (30 + (c.val * 7 + r.val)) = decide (c.val + 5 = r.val)) r c),
      bit_shiftR_masked m 4398046511104 36 dst src (decide (c.val + 6 = r.val))
        ((by decide : ∀ r c : Fin 7, (4398046511104 : Nat).testBit (36 + (c.val * 7 + r.val)) = true → 36 + (c.val * 7 + r.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (4398046511104 : Nat).testBit (36 + (c.val * 7 + r.val)) = decide (c.val + 6 = r.val)) r c)]
  have hdisj : ∀ b : Bool, ∀ a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : Bool,
      (a0 || a1 || a2 || a3 || a4 || a5 || a6 || b1 || b2 || b3 || b4 || b5 || b6) = true →
      ((a0 && b) || ((a1 && b) || ((a2 && b) || ((a3 && b) || ((a4 && b) || ((a5 && b) ||
       ((a6 && b) || ((b1 && b) || ((b2 && b) || ((b3 && b) || ((b4 && b) || ((b5 && b) ||
       (b6 && b))))))))))))) = b := by
    intro b a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 h
    cases b
    · simp
    · simp only [Bool.and_true]; simp only [Bool.or_assoc] at h ⊢; exact h
  refine hdisj (m.testBit src) _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
  have hcov : ∀ r c : Fin 7,
      (decide (r.val = c.val) || decide (r.val + 1 = c.val) || decide (r.val + 2 = c.val) ||
       decide (r.val + 3 = c.val) || decide (r.val + 4 = c.val) || decide (r.val + 5 = c.val) ||
       decide (r.val + 6 = c.val) || decide (c.val + 1 = r.val) || decide (c.val + 2 = r.val) ||
       decide (c.val + 3 = r.val) || decide (c.val + 4 = r.val) || decide (c.val + 5 = r.val) ||
       decide (c.val + 6 = r.val)) = true := by decide
  exact hcov r c

private structure Aut2 where
  sw : Bool
  sr : Bool
  tr : Fin 7
  sc : Bool
  tc : Fin 7
  deriving DecidableEq

private def Aut2.applyFin (g : Aut2) (p : Fin 7 × Fin 7) : Fin 7 × Fin 7 :=
  let r1 := if g.sr then neg7 p.1 else p.1
  let r2 := add7 r1 g.tr
  let c1 := if g.sc then neg7 p.2 else p.2
  let c2 := add7 c1 g.tc
  if g.sw then (c2, r2) else (r2, c2)

private def Aut2.inv (g : Aut2) : Aut2 :=
  let tr' := if g.sr then g.tr else neg7 g.tr
  let tc' := if g.sc then g.tc else neg7 g.tc
  if g.sw then ⟨true, g.sc, tc', g.sr, tr'⟩ else ⟨false, g.sr, tr', g.sc, tc'⟩

private lemma Aut2.inv_applyFin (g : Aut2) (p : Fin 7 × Fin 7) :
    g.inv.applyFin (g.applyFin p) = p := by
  rcases g with ⟨sw, sr, tr, sc, tc⟩
  rcases p with ⟨r, c⟩
  cases sw <;> simp only [Aut2.applyFin, Aut2.inv, Bool.false_eq_true, ↓reduceIte, d7_inv_left]

private lemma Aut2.applyFin_inv (g : Aut2) (p : Fin 7 × Fin 7) :
    g.applyFin (g.inv.applyFin p) = p := by
  rcases g with ⟨sw, sr, tr, sc, tc⟩
  rcases p with ⟨r, c⟩
  cases sw <;> simp only [Aut2.applyFin, Aut2.inv, Bool.false_eq_true, ↓reduceIte, d7_inv_right]

private def Aut2.toIso (g : Aut2) : (C7 ⊠ C7) ≃g (C7 ⊠ C7) where
  toEquiv := Equiv.mk
    (fun q => let p := g.applyFin (ofZ7 q.1, ofZ7 q.2); (toZ7 p.1, toZ7 p.2))
    (fun q => let p := g.inv.applyFin (ofZ7 q.1, ofZ7 q.2); (toZ7 p.1, toZ7 p.2))
    (fun ⟨a, b⟩ => by
      dsimp only
      rw [ofZ7_toZ7, ofZ7_toZ7, Prod.mk.eta, g.inv_applyFin, toZ7_ofZ7, toZ7_ofZ7])
    (fun ⟨a, b⟩ => by
      dsimp only
      rw [ofZ7_toZ7, ofZ7_toZ7, Prod.mk.eta, g.applyFin_inv, toZ7_ofZ7, toZ7_ofZ7])
  map_rel_iff' := by
    have hd7_adj : ∀ (s : Bool) (t : Fin 7) (a b : ZMod 7),
        C7.Adj (toZ7 (add7 (if s then neg7 (ofZ7 a) else ofZ7 a) t))
               (toZ7 (add7 (if s then neg7 (ofZ7 b) else ofZ7 b) t)) ↔ C7.Adj a b := by
      intro s t a b
      have hsub : ∀ x y : ZMod 7, C7.Adj x y ↔ (x - y = 1 ∨ y - x = 1) := by
        intro x y; unfold C7; exact SimpleGraph.cycleGraph_adj
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, toZ7_add7, toZ7_neg7, toZ7_ofZ7, hsub]
      · constructor
        · rintro (h | h)
          · left; linear_combination h
          · right; linear_combination h
        · rintro (h | h)
          · left; linear_combination h
          · right; linear_combination h
      · constructor
        · rintro (h | h)
          · right; linear_combination h
          · left; linear_combination h
        · rintro (h | h)
          · right; linear_combination h
          · left; linear_combination h
    have hd7_eq : ∀ (s : Bool) (t : Fin 7) (a b : ZMod 7),
        toZ7 (add7 (if s then neg7 (ofZ7 a) else ofZ7 a) t) =
          toZ7 (add7 (if s then neg7 (ofZ7 b) else ofZ7 b) t) ↔ a = b := by
      intro s t a b
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, toZ7_add7, toZ7_neg7, toZ7_ofZ7]
      · exact add_left_inj _
      · simp
    intro ⟨a1, b1⟩ ⟨a2, b2⟩
    rcases g with ⟨sw, sr, tr, sc, tc⟩
    have hsw : ∀ (P1 P2 Q1 Q2 : Prop),
        (¬(P1 ∧ P2) ∧ (P1 ∨ Q1) ∧ (P2 ∨ Q2)) ↔ (¬(P2 ∧ P1) ∧ (P2 ∨ Q2) ∧ (P1 ∨ Q1)) := by
      intro P1 P2 Q1 Q2
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨fun ⟨a, b⟩ => h1 ⟨b, a⟩, h3, h2⟩,
             fun ⟨h1, h2, h3⟩ => ⟨fun ⟨a, b⟩ => h1 ⟨b, a⟩, h3, h2⟩⟩
    cases sw <;> simp only [Equiv.coe_fn_mk, Aut2.applyFin, Bool.false_eq_true, ↓reduceIte,
      strongProd_adj, ne_eq, Prod.mk.injEq, hd7_eq, hd7_adj]
    · exact hsw _ _ _ _

private def Aut2.applyMask (g : Aut2) (m : Nat) : Nat :=
  seqN (match g.sr with | true => flipRow49 m | false => m) fun m1 =>
  seqN (shiftRow49 g.tr m1) fun m2 =>
  seqN (match g.sc with | true => flipCol49 m2 | false => m2) fun m3 =>
  seqN (shiftCol49 g.tc m3) fun m4 =>
  match g.sw with | true => transpose49 m4 | false => m4

private lemma Aut2.applyMask_lt (g : Aut2) {m : Nat} (hm : m < 2 ^ 49) :
    g.applyMask m < 2 ^ 49 := by
  unfold Aut2.applyMask
  simp only [seqN_eq]
  let m1 := match g.sr with | true => flipRow49 m | false => m
  have h1 : m1 < 2 ^ 49 := by
    dsimp only [m1]; cases g.sr
    · exact hm
    · exact flipRow49_lt m
  have h2 : shiftRow49 g.tr m1 < 2 ^ 49 := shiftRow49_lt g.tr h1
  let m3 := match g.sc with | true => flipCol49 (shiftRow49 g.tr m1) | false => shiftRow49 g.tr m1
  have h3 : m3 < 2 ^ 49 := by
    dsimp only [m3]; cases g.sc
    · exact h2
    · exact flipCol49_lt _
  have h4 : shiftCol49 g.tc m3 < 2 ^ 49 := shiftCol49_lt g.tc h3
  cases g.sw
  · exact h4
  · exact transpose49_lt _

private lemma Aut2.get_applyMask (g : Aut2) (m : Nat) (r c : Fin 7) :
    get49 (g.applyMask m) (g.applyFin (r, c)).1 (g.applyFin (r, c)).2 = get49 m r c := by
  rcases g with ⟨sw, sr, tr, sc, tc⟩
  unfold Aut2.applyMask Aut2.applyFin
  simp only [seqN_eq]
  cases sw <;> cases sr <;> cases sc <;>
    simp only [Bool.false_eq_true, ↓reduceIte, get49_transpose, get49_shiftCol, get49_flipCol,
      get49_shiftRow, get49_flipRow]

private lemma Aut2.get_applyMask_eq (g : Aut2) (m : Nat) (r c : Fin 7) :
    get49 (g.applyMask m) r c = get49 m (g.inv.applyFin (r, c)).1 (g.inv.applyFin (r, c)).2 := by
  have h := g.get_applyMask m (g.inv.applyFin (r, c)).1 (g.inv.applyFin (r, c)).2
  rw [Prod.mk.eta, g.applyFin_inv] at h
  exact h

private lemma Aut2.applyMask_inv_left (g : Aut2) {m : Nat} (hm : m < 2 ^ 49) :
    g.inv.applyMask (g.applyMask m) = m := by
  apply ext49 (g.inv.applyMask_lt (g.applyMask_lt hm)) hm
  intro r c
  rw [g.inv.get_applyMask_eq, g.get_applyMask_eq]
  have hinv : g.inv.inv = g := by
    rcases g with ⟨sw, sr, tr, sc, tc⟩
    have hneg : ∀ x : Fin 7, neg7 (neg7 x) = x := by decide
    cases sw <;> cases sr <;> cases sc <;> simp [Aut2.inv, hneg]
  rw [hinv, Prod.mk.eta, g.inv_applyFin]

private lemma Aut2.applyMask_inv_right (g : Aut2) {m : Nat} (hm : m < 2 ^ 49) :
    g.applyMask (g.inv.applyMask m) = m := by
  have hinv : g.inv.inv = g := by
    rcases g with ⟨sw, sr, tr, sc, tc⟩
    have hneg : ∀ x : Fin 7, neg7 (neg7 x) = x := by decide
    cases sw <;> cases sr <;> cases sc <;> simp [Aut2.inv, hneg]
  have h := g.inv.applyMask_inv_left hm
  rwa [hinv] at h

private lemma Aut2.applyMask_diff (g : Aut2) {a b : Nat} (ha : a < 2 ^ 49) :
    g.applyMask (diff49 a b) = diff49 (g.applyMask a) (g.applyMask b) := by
  apply ext49 (g.applyMask_lt (diff49_lt ha)) (diff49_lt (g.applyMask_lt ha))
  intro r c
  rw [g.get_applyMask_eq, get49_diff, get49_diff, g.get_applyMask_eq, g.get_applyMask_eq]

private lemma Aut2.applyMask_subset {g : Aut2} {a b : Nat} (ha : a < 2 ^ 49)
    (h : subset49 a b = true) : subset49 (g.applyMask a) (g.applyMask b) = true := by
  rw [subset49_iff ha] at h
  rw [subset49_iff (g.applyMask_lt ha)]
  intro r c hga
  rw [g.get_applyMask_eq] at hga ⊢
  exact h _ _ hga

private lemma Aut2.applyMask_ofFinset (g : Aut2) (S : Finset (ZMod 7 × ZMod 7)) :
    g.applyMask (ofFinset49 S) = ofFinset49 (S.map g.toIso.toEquiv.toEmbedding) := by
  apply ext49 (g.applyMask_lt (ofFinset49_lt S)) (ofFinset49_lt _)
  intro r c
  rw [Bool.eq_iff_iff, g.get_applyMask_eq, get49_ofFinset, get49_ofFinset, Finset.mem_map]
  constructor
  · intro h
    refine ⟨(toZ7 (g.inv.applyFin (r, c)).1, toZ7 (g.inv.applyFin (r, c)).2), h, ?_⟩
    simp only [Equiv.coe_toEmbedding, Aut2.toIso, Equiv.coe_fn_mk,
      ofZ7_toZ7, Prod.mk.eta, g.applyFin_inv]
  · rintro ⟨⟨a, b⟩, hab, heq⟩
    simp only [Equiv.coe_toEmbedding, Aut2.toIso, Equiv.coe_fn_mk] at heq
    have h1 := congrArg (fun q : ZMod 7 × ZMod 7 => g.inv.applyFin (ofZ7 q.1, ofZ7 q.2)) heq
    dsimp only at h1
    rw [ofZ7_toZ7, ofZ7_toZ7, ofZ7_toZ7, ofZ7_toZ7, Prod.mk.eta, g.inv_applyFin] at h1
    rw [← h1, toZ7_ofZ7, toZ7_ofZ7]
    exact hab

private lemma Aut2.applyMask_closedNbr (g : Aut2) {m : Nat} (hm : m < 2 ^ 49) :
    g.applyMask (closedNbr49 m) = closedNbr49 (g.applyMask m) := by
  apply ext49 (g.applyMask_lt (closedNbr49_lt hm)) (closedNbr49_lt (g.applyMask_lt hm))
  intro r c
  have hclose : ∀ a1 b1 a2 b2 : Fin 7,
      ((toZ7 a1 = toZ7 a2 ∨ C7.Adj (toZ7 a1) (toZ7 a2)) ∧
       (toZ7 b1 = toZ7 b2 ∨ C7.Adj (toZ7 b1) (toZ7 b2))) ↔
      ((toZ7 (g.applyFin (a1, b1)).1 = toZ7 (g.applyFin (a2, b2)).1 ∨
          C7.Adj (toZ7 (g.applyFin (a1, b1)).1) (toZ7 (g.applyFin (a2, b2)).1)) ∧
       (toZ7 (g.applyFin (a1, b1)).2 = toZ7 (g.applyFin (a2, b2)).2 ∨
          C7.Adj (toZ7 (g.applyFin (a1, b1)).2) (toZ7 (g.applyFin (a2, b2)).2))) := by
    have hpair : ∀ (x1 y1 x2 y2 : ZMod 7),
        ((x1, y1) = (x2, y2) ∨ (C7 ⊠ C7).Adj (x1, y1) (x2, y2)) ↔
        ((x1 = x2 ∨ C7.Adj x1 x2) ∧ (y1 = y2 ∨ C7.Adj y1 y2)) := by
      intro x1 y1 x2 y2
      simp only [Prod.mk.injEq, strongProd_adj, ne_eq]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨_, h1, h2⟩)
        · exact ⟨Or.inl rfl, Or.inl rfl⟩
        · exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        by_cases heq : x1 = x2 ∧ y1 = y2
        · exact Or.inl heq
        · exact Or.inr ⟨heq, h1, h2⟩
    intro a1 b1 a2 b2
    have h := hpair (toZ7 a1) (toZ7 b1) (toZ7 a2) (toZ7 b2)
    have h' := hpair (toZ7 (g.applyFin (a1, b1)).1) (toZ7 (g.applyFin (a1, b1)).2)
                     (toZ7 (g.applyFin (a2, b2)).1) (toZ7 (g.applyFin (a2, b2)).2)
    have hg1 : g.toIso (toZ7 a1, toZ7 b1) = (toZ7 (g.applyFin (a1, b1)).1, toZ7 (g.applyFin (a1, b1)).2) := by
      simp [Aut2.toIso, ofZ7_toZ7]
    have hg2 : g.toIso (toZ7 a2, toZ7 b2) = (toZ7 (g.applyFin (a2, b2)).1, toZ7 (g.applyFin (a2, b2)).2) := by
      simp [Aut2.toIso, ofZ7_toZ7]
    have h'' : g.toIso (toZ7 a1, toZ7 b1) = g.toIso (toZ7 a2, toZ7 b2) ∨
        (C7 ⊠ C7).Adj (g.toIso (toZ7 a1, toZ7 b1)) (g.toIso (toZ7 a2, toZ7 b2)) ↔
        (toZ7 (g.applyFin (a1, b1)).1 = toZ7 (g.applyFin (a2, b2)).1 ∨
          C7.Adj (toZ7 (g.applyFin (a1, b1)).1) (toZ7 (g.applyFin (a2, b2)).1)) ∧
        (toZ7 (g.applyFin (a1, b1)).2 = toZ7 (g.applyFin (a2, b2)).2 ∨
          C7.Adj (toZ7 (g.applyFin (a1, b1)).2) (toZ7 (g.applyFin (a2, b2)).2)) := by
      simpa only [hg1, hg2] using h'
    rw [← h, ← h'', g.toIso.injective.eq_iff, g.toIso.map_adj_iff]
  rw [Bool.eq_iff_iff, g.get_applyMask_eq, closedNbr49_get, closedNbr49_get]
  constructor
  · rintro ⟨r', c', hm', hr, hc⟩
    refine ⟨(g.applyFin (r', c')).1, (g.applyFin (r', c')).2, ?_, ?_⟩
    · rw [g.get_applyMask]; exact hm'
    · have hcl := (hclose r' c' (g.inv.applyFin (r, c)).1 (g.inv.applyFin (r, c)).2).mp ⟨hr, hc⟩
      rw [Prod.mk.eta, g.applyFin_inv] at hcl
      exact hcl
  · rintro ⟨r', c', hm', hr, hc⟩
    rw [g.get_applyMask_eq] at hm'
    refine ⟨(g.inv.applyFin (r', c')).1, (g.inv.applyFin (r', c')).2, hm', ?_⟩
    have hcl := (hclose (g.inv.applyFin (r', c')).1 (g.inv.applyFin (r', c')).2
      (g.inv.applyFin (r, c)).1 (g.inv.applyFin (r, c)).2).mpr
      (by rw [Prod.mk.eta, Prod.mk.eta, g.applyFin_inv, g.applyFin_inv]; exact ⟨hr, hc⟩)
    exact hcl

private lemma isIndepSet_map_iso' {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    H.IsIndepSet ((S.map e.toEquiv.toEmbedding : Finset W) : Set W) := by
  intro x hx y hy hne hadj
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Equiv.coe_toEmbedding,
    RelIso.coe_fn_toEquiv] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact hS ha hb (fun hab => hne (congrArg e hab)) ((e.map_adj_iff).mp hadj)

/-! ## Section 3: Exact 3-Orbit Classification of `I₁₀(C₇ ⊠ C₇)` & Loop-Hoisted Enumeration -/

private def rep (k : Fin 3) : Nat :=
  match k.val with | 0 => 4540058566952 | 1 => 4556965150888 | _ => 4556965675304

private lemma rep_lt (k : Fin 3) : rep k < 2 ^ 49 := by
  revert k; decide

private def repPtsList (k : Fin 3) : List (Fin 7 × Fin 7) :=
  match k.val with
  | 0 => [(0, 3), (0, 5), (1, 1), (2, 4), (2, 6), (3, 2), (4, 0), (4, 4), (5, 2), (6, 0)]
  | 1 => [(0, 3), (0, 5), (1, 0), (2, 3), (2, 5), (3, 1), (4, 4), (4, 6), (5, 2), (6, 0)]
  | _ => [(0, 3), (0, 5), (1, 1), (2, 3), (2, 6), (3, 1), (4, 4), (4, 6), (5, 2), (6, 0)]

private lemma rep_mem_iff : ∀ (k : Fin 3) (r c : Fin 7),
    get49 (rep k) r c = true ↔ (r, c) ∈ repPtsList k := by decide

private lemma repPtsList_nodup : ∀ k : Fin 3, (repPtsList k).Nodup := by decide

private def forAllFin7 (f : Fin 7 → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6

private lemma forAllFin7_sound {f : Fin 7 → Bool} (h : forAllFin7 f = true) :
    ∀ x : Fin 7, f x = true := by
  unfold forAllFin7 at h
  simp only [Bool.and_eq_true] at h
  exact fun
    | ⟨0, _⟩ => h.1.1.1.1.1.1 | ⟨1, _⟩ => h.1.1.1.1.1.2 | ⟨2, _⟩ => h.1.1.1.1.2
    | ⟨3, _⟩ => h.1.1.1.2     | ⟨4, _⟩ => h.1.1.2       | ⟨5, _⟩ => h.1.2
    | ⟨6, _⟩ => h.2

private def foldFin7 {α : Type} (f : Fin 7 → α → α) (acc : α) : α :=
  f 6 (f 5 (f 4 (f 3 (f 2 (f 1 (f 0 acc))))))

private lemma mem_foldFin7 {α : Type} {y : α} {f : Fin 7 → List α → List α}
    (hmono : ∀ (x : Fin 7) (l : List α), y ∈ l → y ∈ f x l)
    (x0 : Fin 7) (hhit : ∀ l : List α, y ∈ f x0 l) (acc : List α) :
    y ∈ foldFin7 f acc := by
  unfold foldFin7
  revert x0 hhit
  exact fun
    | ⟨0, _⟩, h => hmono 6 _ (hmono 5 _ (hmono 4 _ (hmono 3 _ (hmono 2 _ (hmono 1 _ (h _))))))
    | ⟨1, _⟩, h => hmono 6 _ (hmono 5 _ (hmono 4 _ (hmono 3 _ (hmono 2 _ (h _)))))
    | ⟨2, _⟩, h => hmono 6 _ (hmono 5 _ (hmono 4 _ (hmono 3 _ (h _))))
    | ⟨3, _⟩, h => hmono 6 _ (hmono 5 _ (hmono 4 _ (h _)))
    | ⟨4, _⟩, h => hmono 6 _ (hmono 5 _ (h _))
    | ⟨5, _⟩, h => hmono 6 _ (h _)
    | ⟨6, _⟩, h => h _

private lemma mem_foldFin7_mono {α : Type} {y : α} {f : Fin 7 → List α → List α}
    (hmono : ∀ (x : Fin 7) (l : List α), y ∈ l → y ∈ f x l) {acc : List α} (h : y ∈ acc) :
    y ∈ foldFin7 f acc :=
  hmono 6 _ (hmono 5 _ (hmono 4 _ (hmono 3 _ (hmono 2 _ (hmono 1 _ (hmono 0 _ h))))))

private def forAllAut2 (k0 : Fin 3) (half : Bool) (f : Aut2 → Nat → Bool) : Bool :=
  let base := rep k0
  let goSr (sr : Bool) : Bool :=
    seqN (match sr with | true => flipRow49 base | false => base) fun m1 =>
    forAllFin7 fun tr =>
      seqN (shiftRow49 tr m1) fun m2 =>
      let goSc (sc : Bool) : Bool :=
        seqN (match sc with | true => flipCol49 m2 | false => m2) fun m3 =>
        forAllFin7 fun tc =>
          seqN (shiftCol49 tc m3) fun m4 =>
            f ⟨false, sr, tr, sc, tc⟩ m4 &&
            seqN (transpose49 m4) fun m5 => f ⟨true, sr, tr, sc, tc⟩ m5
      goSc false && goSc true
  match half with
  | true => goSr false
  | false => goSr false && goSr true

private lemma forAllAut2_sound {k0 : Fin 3} {half : Bool} {f : Aut2 → Nat → Bool}
    (h : forAllAut2 k0 half f = true) (g : Aut2) (hsr : half = false ∨ g.sr = false) :
    f g (g.applyMask (rep k0)) = true := by
  rcases g with ⟨sw, sr, tr, sc, tc⟩
  unfold forAllAut2 at h
  simp only [seqN_eq] at h
  cases sr
  · have hgoSr : forAllFin7 (fun tr' =>
        let m2 := shiftRow49 tr' (rep k0)
        let goSc (sc' : Bool) : Bool :=
          let m3 := match sc' with | true => flipCol49 m2 | false => m2
          forAllFin7 fun tc' =>
            let m4 := shiftCol49 tc' m3
            f ⟨false, false, tr', sc', tc'⟩ m4 && f ⟨true, false, tr', sc', tc'⟩ (transpose49 m4)
        goSc false && goSc true) = true := by
      cases half
      · exact (Bool.and_eq_true _ _ |>.mp h).1
      · exact h
    have htr := forAllFin7_sound hgoSr tr
    dsimp only at htr; rw [Bool.and_eq_true] at htr
    unfold Aut2.applyMask; simp only [seqN_eq]
    cases sc
    · have htc := forAllFin7_sound htr.1 tc
      rw [Bool.and_eq_true] at htc
      cases sw
      · exact htc.1
      · exact htc.2
    · have htc := forAllFin7_sound htr.2 tc
      rw [Bool.and_eq_true] at htc
      cases sw
      · exact htc.1
      · exact htc.2
  · have hgoSr : forAllFin7 (fun tr' =>
        let m2 := shiftRow49 tr' (flipRow49 (rep k0))
        let goSc (sc' : Bool) : Bool :=
          let m3 := match sc' with | true => flipCol49 m2 | false => m2
          forAllFin7 fun tc' =>
            let m4 := shiftCol49 tc' m3
            f ⟨false, true, tr', sc', tc'⟩ m4 && f ⟨true, true, tr', sc', tc'⟩ (transpose49 m4)
        goSc false && goSc true) = true := by
      cases half
      · exact (Bool.and_eq_true _ _ |>.mp h).2
      · rcases hsr with hbad | hbad <;> cases hbad
    have htr := forAllFin7_sound hgoSr tr
    dsimp only at htr; rw [Bool.and_eq_true] at htr
    unfold Aut2.applyMask; simp only [seqN_eq]
    cases sc
    · have htc := forAllFin7_sound htr.1 tc
      rw [Bool.and_eq_true] at htc
      cases sw
      · exact htc.1
      · exact htc.2
    · have htc := forAllFin7_sound htr.2 tc
      rw [Bool.and_eq_true] at htc
      cases sw
      · exact htc.1
      · exact htc.2

private def collectAut2 (k0 : Fin 3) (half : Bool) (pred : Nat → Bool)
    (acc : List (Fin 3 × Aut2 × Nat)) : List (Fin 3 × Aut2 × Nat) :=
  let base := rep k0
  let goSr (sr : Bool) (a0 : List (Fin 3 × Aut2 × Nat)) :=
    seqN (match sr with | true => flipRow49 base | false => base) fun m1 =>
    foldFin7 (fun tr a1 =>
      seqN (shiftRow49 tr m1) fun m2 =>
      let goSc (sc : Bool) (a2 : List (Fin 3 × Aut2 × Nat)) :=
        seqN (match sc with | true => flipCol49 m2 | false => m2) fun m3 =>
        foldFin7 (fun tc a3 =>
          seqN (shiftCol49 tc m3) fun m4 =>
          let a4 := match pred m4 with
            | true => (k0, Aut2.mk false sr tr sc tc, m4) :: a3
            | false => a3
          seqN (transpose49 m4) fun m5 =>
          match pred m5 with
            | true => (k0, Aut2.mk true sr tr sc tc, m5) :: a4
            | false => a4) a2
      goSc true (goSc false a1)) a0
  match half with
  | true => goSr false acc
  | false => goSr true (goSr false acc)

private lemma mem_collectAut2_mono {k0 : Fin 3} {half : Bool} {pred : Nat → Bool}
    {y : Fin 3 × Aut2 × Nat} {acc : List (Fin 3 × Aut2 × Nat)} (hy : y ∈ acc) :
    y ∈ collectAut2 k0 half pred acc := by
  have hstep : ∀ (a : Fin 3 × Aut2 × Nat) (b : Bool) (l : List (Fin 3 × Aut2 × Nat)),
      y ∈ l → y ∈ (match b with | true => a :: l | false => l) := by
    intro a b l hl; cases b
    · exact hl
    · exact List.mem_cons_of_mem a hl
  have htc : ∀ sr tr sc (m3 : Nat) (a2 : List _), y ∈ a2 →
      y ∈ foldFin7 (fun tc a3 =>
        let m4 := shiftCol49 tc m3
        let a4 := match pred m4 with | true => (k0, Aut2.mk false sr tr sc tc, m4) :: a3 | false => a3
        let m5 := transpose49 m4
        match pred m5 with | true => (k0, Aut2.mk true sr tr sc tc, m5) :: a4 | false => a4) a2 :=
    fun sr tr sc m3 a2 ha2 => mem_foldFin7_mono (fun tc l hl => hstep _ _ _ (hstep _ _ _ hl)) ha2
  have hsr : ∀ sr (a0 : List _), y ∈ a0 →
      y ∈ foldFin7 (fun tr a1 =>
        let m1 := match sr with | true => flipRow49 (rep k0) | false => rep k0
        let m2 := shiftRow49 tr m1
        let goSc (sc : Bool) (a2 : List _) :=
          let m3 := match sc with | true => flipCol49 m2 | false => m2
          foldFin7 (fun tc a3 =>
            let m4 := shiftCol49 tc m3
            let a4 := match pred m4 with | true => (k0, Aut2.mk false sr tr sc tc, m4) :: a3 | false => a3
            let m5 := transpose49 m4
            match pred m5 with | true => (k0, Aut2.mk true sr tr sc tc, m5) :: a4 | false => a4) a2
        goSc true (goSc false a1)) a0 :=
    fun sr a0 ha0 => mem_foldFin7_mono (fun tr l hl => htc sr tr true _ _ (htc sr tr false _ _ hl)) ha0
  unfold collectAut2; simp only [seqN_eq]
  cases half
  · exact hsr true _ (hsr false acc hy)
  · exact hsr false acc hy

private lemma mem_collectAut2 {k0 : Fin 3} {half : Bool} {pred : Nat → Bool}
    (g : Aut2) (hsr : half = false ∨ g.sr = false)
    (hpred : pred (g.applyMask (rep k0)) = true) (acc : List (Fin 3 × Aut2 × Nat)) :
    (k0, g, g.applyMask (rep k0)) ∈ collectAut2 k0 half pred acc := by
  rcases g with ⟨sw, sr, tr, sc, tc⟩
  have hstep : ∀ (y a : Fin 3 × Aut2 × Nat) (b : Bool) (l : List _),
      y ∈ l → y ∈ (match b with | true => a :: l | false => l) := by
    intro y a b l hl; cases b
    · exact hl
    · exact List.mem_cons_of_mem a hl
  have htc_mono : ∀ (y : Fin 3 × Aut2 × Nat) sr' tr' sc' (x3 : Nat) (a2 : List _), y ∈ a2 →
      y ∈ foldFin7 (fun tc' a3 =>
        let x4 := shiftCol49 tc' x3
        let a4 := match pred x4 with | true => (k0, Aut2.mk false sr' tr' sc' tc', x4) :: a3 | false => a3
        let x5 := transpose49 x4
        match pred x5 with | true => (k0, Aut2.mk true sr' tr' sc' tc', x5) :: a4 | false => a4) a2 :=
    fun y sr' tr' sc' x3 a2 ha2 => mem_foldFin7_mono (fun tc' l hl => hstep y _ _ _ (hstep y _ _ _ hl)) ha2
  have hsr_mono : ∀ (y : Fin 3 × Aut2 × Nat) sr' (a0 : List _), y ∈ a0 →
      y ∈ foldFin7 (fun tr' a1 =>
        let x1 := match sr' with | true => flipRow49 (rep k0) | false => rep k0
        let x2 := shiftRow49 tr' x1
        let goSc (sc' : Bool) (a2 : List _) :=
          let x3 := match sc' with | true => flipCol49 x2 | false => x2
          foldFin7 (fun tc' a3 =>
            let x4 := shiftCol49 tc' x3
            let a4 := match pred x4 with | true => (k0, Aut2.mk false sr' tr' sc' tc', x4) :: a3 | false => a3
            let x5 := transpose49 x4
            match pred x5 with | true => (k0, Aut2.mk true sr' tr' sc' tc', x5) :: a4 | false => a4) a2
        goSc true (goSc false a1)) a0 :=
    fun y sr' a0 ha0 => mem_foldFin7_mono (fun tr' l hl => htc_mono y sr' tr' true _ _ (htc_mono y sr' tr' false _ _ hl)) ha0
  have hhit_tc : ∀ (sr1 sc1 sw1 : Bool) (tr1 tc1 : Fin 7) (x3 : Nat) (a2 : List _),
      pred (match sw1 with | true => transpose49 (shiftCol49 tc1 x3) | false => shiftCol49 tc1 x3) = true →
      (k0, Aut2.mk sw1 sr1 tr1 sc1 tc1,
        match sw1 with | true => transpose49 (shiftCol49 tc1 x3) | false => shiftCol49 tc1 x3) ∈
      foldFin7 (fun tc' a3 =>
        let z4 := shiftCol49 tc' x3
        let a4 := match pred z4 with | true => (k0, Aut2.mk false sr1 tr1 sc1 tc', z4) :: a3 | false => a3
        let z5 := transpose49 z4
        match pred z5 with | true => (k0, Aut2.mk true sr1 tr1 sc1 tc', z5) :: a4 | false => a4) a2 := by
    intro sr1 sc1 sw1 tr1 tc1 x3 a2 hp
    refine mem_foldFin7 (fun tc' l' hl' => hstep _ _ _ _ (hstep _ _ _ _ hl')) tc1 (fun l' => ?_) a2
    cases sw1
    · dsimp only at hp ⊢; rw [hp]; cases pred (transpose49 (shiftCol49 tc1 x3)) <;> simp
    · dsimp only at hp ⊢; rw [hp]; exact List.mem_cons_self ..
  have hhit_sr : ∀ (sr1 sc1 sw1 : Bool) (tr1 tc1 : Fin 7) (a0 : List _),
      let x1 := match sr1 with | true => flipRow49 (rep k0) | false => rep k0
      let x2 := shiftRow49 tr1 x1
      let x3 := match sc1 with | true => flipCol49 x2 | false => x2
      let x4 := shiftCol49 tc1 x3
      let m := match sw1 with | true => transpose49 x4 | false => x4
      pred m = true →
      (k0, Aut2.mk sw1 sr1 tr1 sc1 tc1, m) ∈ foldFin7 (fun tr' a1 =>
        let z1 := match sr1 with | true => flipRow49 (rep k0) | false => rep k0
        let z2 := shiftRow49 tr' z1
        let goSc (sc' : Bool) (a2 : List _) :=
          let z3 := match sc' with | true => flipCol49 z2 | false => z2
          foldFin7 (fun tc' a3 =>
            let z4 := shiftCol49 tc' z3
            let a4 := match pred z4 with | true => (k0, Aut2.mk false sr1 tr' sc' tc', z4) :: a3 | false => a3
            let z5 := transpose49 z4
            match pred z5 with | true => (k0, Aut2.mk true sr1 tr' sc' tc', z5) :: a4 | false => a4) a2
        goSc true (goSc false a1)) a0 := by
    intro sr1 sc1 sw1 tr1 tc1 a0
    dsimp only
    intro hp
    refine mem_foldFin7 (fun tr' l hl => htc_mono _ sr1 tr' true _ _ (htc_mono _ sr1 tr' false _ _ hl)) tr1 (fun l => ?_) a0
    cases sc1
    · exact htc_mono _ sr1 tr1 true _ _ (hhit_tc sr1 false sw1 tr1 tc1 _ l hp)
    · exact hhit_tc sr1 true sw1 tr1 tc1 _ _ hp
  unfold Aut2.applyMask at hpred ⊢
  unfold collectAut2
  simp only [seqN_eq] at hpred ⊢
  cases half
  · cases sr
    · exact hsr_mono _ true _ (hhit_sr false sc sw tr tc acc hpred)
    · exact hhit_sr true sc sw tr tc _ hpred
  · cases sr
    · exact hhit_sr false sc sw tr tc acc hpred
    · rcases hsr with hbad | hbad <;> cases hbad

private lemma rep2_stab_flip (g : Aut2) (hsr : g.sr = true) :
    ∃ g' : Aut2, g'.sr = false ∧ g'.applyMask (rep 2) = g.applyMask (rep 2) := by
  rcases g with ⟨sw, sr, tr, sc, tc⟩
  dsimp only at hsr; subst hsr
  let tr' := add7 (neg7 4) tr
  let tc' := if sc then add7 (neg7 2) tc else add7 2 tc
  refine ⟨⟨sw, false, tr', !sc, tc'⟩, rfl, ?_⟩
  have hinner : (Aut2.mk false true 4 true 2).applyMask (rep 2) = rep 2 := by rfl
  have hcomp : ∀ r c : Fin 7,
      (Aut2.mk sw false tr' (!sc) tc').applyFin (r, c) =
        (Aut2.mk sw true tr sc tc).applyFin ((Aut2.mk false true 4 true 2).applyFin (r, c)) := by
    intro r c
    have hr : add7 r tr' = add7 (neg7 (add7 (neg7 r) 4)) tr := (d7_comp true true tr 4 r).symm
    have hc : add7 (if !sc then neg7 c else c) tc' =
        add7 (if sc then neg7 (add7 (neg7 c) 2) else add7 (neg7 c) 2) tc := by
      have := (d7_comp sc true tc 2 c).symm
      cases sc <;> simpa [tc', Bool.xor] using this
    cases sw <;> simp only [Aut2.applyFin, Bool.false_eq_true, ↓reduceIte, hr, hc]
  apply ext49 (Aut2.applyMask_lt _ (rep_lt 2)) (Aut2.applyMask_lt _ (rep_lt 2))
  intro r c
  let g1 := Aut2.mk sw false tr' (!sc) tc'
  let p := g1.inv.applyFin (r, c)
  have h1 := Aut2.get_applyMask g1 (rep 2) p.1 p.2
  rw [Prod.mk.eta, Aut2.applyFin_inv] at h1
  rw [h1, ← hinner]
  have hp := hcomp p.1 p.2
  rw [Prod.mk.eta, Aut2.applyFin_inv] at hp
  have h2 := Aut2.get_applyMask (Aut2.mk sw true tr sc tc)
    ((Aut2.mk false true 4 true 2).applyMask (rep 2))
    ((Aut2.mk false true 4 true 2).applyFin p).1
    ((Aut2.mk false true 4 true 2).applyFin p).2
  rw [Prod.mk.eta, ← hp] at h2
  rw [h2, Aut2.get_applyMask, hinner]

private def nearK (k : Fin 3) (m : Nat) : List (Fin 3 × Aut2 × Nat) :=
  let pred (B : Nat) : Bool := Nat.ble m (pop49 (Nat.land B (rep k)))
  collectAut2 2 true pred (collectAut2 1 false pred (collectAut2 0 false pred []))

private lemma mem_nearK {k : Fin 3} {m : Nat} {k0 : Fin 3} {g : Aut2}
    (hsr : k0 ≠ 2 ∨ g.sr = false) (hpop : m ≤ pop49 ((g.applyMask (rep k0)) &&& (rep k))) :
    (k0, g, g.applyMask (rep k0)) ∈ nearK k m := by
  have hpred : Nat.ble m (pop49 ((g.applyMask (rep k0)) &&& (rep k))) = true := Nat.ble_eq.mpr hpop
  unfold nearK
  match k0, hsr, hpred with
  | ⟨0, _⟩, _, hp => exact mem_collectAut2_mono (mem_collectAut2_mono (mem_collectAut2 g (Or.inl rfl) hp []))
  | ⟨1, _⟩, _, hp => exact mem_collectAut2_mono (mem_collectAut2 g (Or.inl rfl) hp _)
  | ⟨2, _⟩, hsr, hp => exact mem_collectAut2 g (Or.inr (hsr.resolve_left (fun h => h rfl))) hp _

private lemma alpha_c7_le_three {S : Finset (ZMod 7)} (hS : C7.IsIndepSet (S : Set (ZMod 7))) :
    S.card ≤ 3 := by
  have hsum : 2 * S.card ≤ 7 := by
    have hsplit : ∀ i : ZMod 7,
        (if i ∈ S then 1 else 0) + (if i + 1 ∈ S then 1 else 0) ≤ 1 := by
      intro i
      by_cases h1 : i ∈ S <;> by_cases h2 : i + 1 ∈ S
      · exfalso; exact hS h1 h2 (c7_adj_add_one i).ne (c7_adj_add_one i)
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    have hcard : S.card = ∑ i : ZMod 7, if i ∈ S then 1 else 0 := by simp
    have hshift : (∑ i : ZMod 7, if i + 1 ∈ S then 1 else 0) =
        ∑ i : ZMod 7, if i ∈ S then 1 else 0 :=
      Equiv.sum_comp (Equiv.addRight (1 : ZMod 7)) (fun i => if i ∈ S then 1 else 0)
    calc 2 * S.card
        = (∑ i : ZMod 7, if i ∈ S then 1 else 0) + (∑ i : ZMod 7, if i + 1 ∈ S then 1 else 0) := by
          rw [hshift, ← hcard]; omega
      _ = ∑ i : ZMod 7, ((if i ∈ S then 1 else 0) + (if i + 1 ∈ S then 1 else 0)) := by
          rw [Finset.sum_add_distrib]
      _ ≤ ∑ _i : ZMod 7, 1 := Finset.sum_le_sum fun i _ => hsplit i
      _ = 7 := by decide
  omega

private def rowNbr7 (x : Nat) : Nat :=
  x ||| ((((x <<< 1) &&& 127) ||| (x >>> 6)) ||| ((x >>> 1) ||| ((x &&& 1) <<< 6)))

private lemma rowNbr7_testBit {x : Nat} (hx : x < 128) (c : Fin 7) :
    (rowNbr7 x).testBit c.val = true ↔
      x.testBit (prev7 c).val = true ∨ x.testBit c.val = true ∨ x.testBit (next7 c).val = true := by
  have hall : ∀ (y : Fin 128) (col : Fin 7),
      (rowNbr7 y.val).testBit col.val =
        (y.val.testBit (prev7 col).val || y.val.testBit col.val || y.val.testBit (next7 col).val) := by
    decide
  rw [hall ⟨x, hx⟩ c, Bool.or_eq_true, Bool.or_eq_true, or_assoc]

private lemma row_indep_adj {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) (r : Fin 7) :
    ((row49 (ofFinset49 B) r &&& rowNbr7 (row49 (ofFinset49 B) (next7 r))) == 0) = true ∧
    pop7 (row49 (ofFinset49 B) r) + pop7 (row49 (ofFinset49 B) (next7 r)) ≤ 3 := by
  let R (row : Fin 7) : Finset (ZMod 7) := Finset.univ.filter fun c => (toZ7 row, c) ∈ B
  have hmemR : ∀ (row c : Fin 7), (row49 (ofFinset49 B) row).testBit c.val = true ↔ toZ7 c ∈ R row := by
    intro row c
    rw [row49_testBit, get49_ofFinset]
    simp [R]
  have hcardR : ∀ row : Fin 7, pop7 (row49 (ofFinset49 B) row) = (R row).card := by
    intro row
    rw [pop7_row49_eq_sum]
    have h1 : (∑ c : Fin 7, (get49 (ofFinset49 B) row c).toNat) =
        ∑ c : Fin 7, if toZ7 c ∈ R row then 1 else 0 := by
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : toZ7 c ∈ R row
      · have hg : get49 (ofFinset49 B) row c = true := by rw [← row49_testBit]; exact (hmemR row c).mpr hc
        simp [hc, hg]
      · have hg : get49 (ofFinset49 B) row c = false :=
          Bool.eq_false_iff.mpr fun h => hc ((hmemR row c).mp (by rwa [row49_testBit]))
        simp [hc, hg]
    rw [h1]
    let e : Fin 7 ≃ ZMod 7 := Equiv.mk toZ7 ofZ7 ofZ7_toZ7 toZ7_ofZ7
    have h2 : (∑ c : Fin 7, if e c ∈ R row then 1 else 0) = ∑ z : ZMod 7, if z ∈ R row then 1 else 0 :=
      Equiv.sum_comp e (fun z => if z ∈ R row then 1 else 0)
    change (∑ c : Fin 7, if e c ∈ R row then 1 else 0) = (R row).card
    rw [h2]; simp
  have hadjr : C7.Adj (toZ7 r) (toZ7 (next7 r)) := by rw [toZ7_next7]; exact c7_adj_add_one (toZ7 r)
  have hdisjR : Disjoint (R r) (R (next7 r)) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hc1 hc2
    have hne : (toZ7 r, c) ≠ (toZ7 (next7 r), c) := fun h => hadjr.ne (congrArg Prod.fst h)
    exact hB hc1 hc2 hne ⟨hne, Or.inr hadjr, Or.inl rfl⟩
  have hindR : C7.IsIndepSet ((R r ∪ R (next7 r) : Finset (ZMod 7)) : Set (ZMod 7)) := by
    intro x hx y hy hxy hadjc
    simp only [Finset.mem_coe, Finset.mem_union, R, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · have hne : (toZ7 r, x) ≠ (toZ7 r, y) := fun h => hxy (congrArg Prod.snd h)
      exact hB hx hy hne ⟨hne, Or.inl rfl, Or.inr hadjc⟩
    · have hne : (toZ7 r, x) ≠ (toZ7 (next7 r), y) := fun h => hadjr.ne (congrArg Prod.fst h)
      exact hB hx hy hne ⟨hne, Or.inr hadjr, Or.inr hadjc⟩
    · have hne : (toZ7 (next7 r), x) ≠ (toZ7 r, y) := fun h => hadjr.ne.symm (congrArg Prod.fst h)
      exact hB hx hy hne ⟨hne, Or.inr hadjr.symm, Or.inr hadjc⟩
    · have hne : (toZ7 (next7 r), x) ≠ (toZ7 (next7 r), y) := fun h => hxy (congrArg Prod.snd h)
      exact hB hx hy hne ⟨hne, Or.inl rfl, Or.inr hadjc⟩
  constructor
  · rw [beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < 7
    · let c : Fin 7 := ⟨i, hi⟩
      cases hc : (row49 (ofFinset49 B) r).testBit c.val
      · rfl
      · cases hn : (rowNbr7 (row49 (ofFinset49 B) (next7 r))).testBit c.val
        · rfl
        · exfalso
          have hc' : toZ7 c ∈ R r := (hmemR r c).mp hc
          rcases (rowNbr7_testBit (row49_lt _ _) c).mp hn with h | h | h
          · have h' : toZ7 (prev7 c) ∈ R (next7 r) := (hmemR (next7 r) (prev7 c)).mp h
            have hadjc : C7.Adj (toZ7 c) (toZ7 (prev7 c)) := by
              rw [toZ7_prev7]; have q := (c7_adj_add_one (toZ7 c - 1)).symm; rwa [sub_add_cancel] at q
            exact hindR (Finset.mem_coe.mpr (Finset.mem_union_left _ hc'))
              (Finset.mem_coe.mpr (Finset.mem_union_right _ h')) hadjc.ne hadjc
          · exact Finset.disjoint_left.mp hdisjR hc' ((hmemR (next7 r) c).mp h)
          · have h' : toZ7 (next7 c) ∈ R (next7 r) := (hmemR (next7 r) (next7 c)).mp h
            have hadjc : C7.Adj (toZ7 c) (toZ7 (next7 c)) := by rw [toZ7_next7]; exact c7_adj_add_one _
            exact hindR (Finset.mem_coe.mpr (Finset.mem_union_left _ hc'))
              (Finset.mem_coe.mpr (Finset.mem_union_right _ h')) hadjc.ne hadjc
    · have h0 : (row49 (ofFinset49 B) r).testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (row49_lt _ r) (pow2_mono (a := 7) (by omega)))
      rw [h0]; rfl
  · rw [hcardR, hcardR, ← Finset.card_union_of_disjoint hdisjR]
    exact alpha_c7_le_three hindR

private lemma alpha_c7_pow2_le_internal {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) : B.card ≤ 10 := by
  have hpop := pop49_ofFinset B
  have h0 : pop7 (row49 (ofFinset49 B) 0) + pop7 (row49 (ofFinset49 B) 1) ≤ 3 := (row_indep_adj hB 0).2
  have h1 : pop7 (row49 (ofFinset49 B) 1) + pop7 (row49 (ofFinset49 B) 2) ≤ 3 := (row_indep_adj hB 1).2
  have h2 : pop7 (row49 (ofFinset49 B) 2) + pop7 (row49 (ofFinset49 B) 3) ≤ 3 := (row_indep_adj hB 2).2
  have h3 : pop7 (row49 (ofFinset49 B) 3) + pop7 (row49 (ofFinset49 B) 4) ≤ 3 := (row_indep_adj hB 3).2
  have h4 : pop7 (row49 (ofFinset49 B) 4) + pop7 (row49 (ofFinset49 B) 5) ≤ 3 := (row_indep_adj hB 4).2
  have h5 : pop7 (row49 (ofFinset49 B) 5) + pop7 (row49 (ofFinset49 B) 6) ≤ 3 := (row_indep_adj hB 5).2
  have h6 : pop7 (row49 (ofFinset49 B) 6) + pop7 (row49 (ofFinset49 B) 0) ≤ 3 := (row_indep_adj hB 6).2
  rw [← hpop, pop49_eq_rows]
  omega

private def indepRows1 : List Nat := [1, 2, 4, 8, 16, 32, 64]
private def indepRows2 : List Nat := [5, 9, 17, 33, 10, 18, 34, 66, 20, 36, 68, 40, 72, 80]

private def isIndepRow7 (r : Nat) : Bool :=
  (r &&& (((r <<< 1) &&& 127) ||| (r >>> 6))) == 0

private lemma row_mem_indepRows1 {row : Nat} (hlt : row < 128) (hpop : pop7 row = 1) :
    row ∈ indepRows1 := by
  have hall : ∀ x : Fin 128, pop7 x.val = 1 → x.val ∈ indepRows1 := by decide
  exact hall ⟨row, hlt⟩ hpop

private lemma row_mem_indepRows2 {row : Nat} (hlt : row < 128) (hpop : pop7 row = 2)
    (hind : ∀ c : Fin 7, row.testBit c.val = true → row.testBit (next7 c).val = false) :
    row ∈ indepRows2 := by
  have his : isIndepRow7 row = true := by
    unfold isIndepRow7
    rw [beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < 7
    · let c : Fin 7 := ⟨i, hi⟩
      change (row.testBit c.val && ((((row <<< 1) &&& 127) ||| (row >>> 6)).testBit c.val)) = false
      cases hc : row.testBit c.val
      · rfl
      · rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Bool.true_and]
        have hprev : row.testBit (prev7 c).val = false := by
          cases hp : row.testBit (prev7 c).val
          · rfl
          · have hn : next7 (prev7 c) = c := (by decide : ∀ x : Fin 7, next7 (prev7 x) = x) c
            have hcontra := hind (prev7 c) hp
            rw [hn, hc] at hcontra; exact absurd hcontra (by decide)
        have hstep : ∀ x : Fin 7, row.testBit (prev7 x).val = false →
            (((decide (x.val ≥ 1) && row.testBit (x.val - 1)) && (127 : Nat).testBit x.val) ||
              row.testBit (6 + x.val)) = false := by
          intro ⟨xv, hxv⟩ hp
          have hhi : ∀ k : Nat, 7 ≤ k → row.testBit k = false :=
            fun k hk => Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (a := 7) hk))
          have hxv' : xv = 0 ∨ xv = 1 ∨ xv = 2 ∨ xv = 3 ∨ xv = 4 ∨ xv = 5 ∨ xv = 6 := by omega
          rcases hxv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hp
          · dsimp only; rw [hhi 7 (by decide), Bool.or_false]; change row.testBit 0 = false at hp; simp only [show 1 - 1 = 0 by rfl, hp, Bool.and_false, Bool.false_and]
          · dsimp only; rw [hhi 8 (by decide), Bool.or_false]; change row.testBit 1 = false at hp; simp only [show 2 - 1 = 1 by rfl, hp, Bool.and_false, Bool.false_and]
          · dsimp only; rw [hhi 9 (by decide), Bool.or_false]; change row.testBit 2 = false at hp; simp only [show 3 - 1 = 2 by rfl, hp, Bool.and_false, Bool.false_and]
          · dsimp only; rw [hhi 10 (by decide), Bool.or_false]; change row.testBit 3 = false at hp; simp only [show 4 - 1 = 3 by rfl, hp, Bool.and_false, Bool.false_and]
          · dsimp only; rw [hhi 11 (by decide), Bool.or_false]; change row.testBit 4 = false at hp; simp only [show 5 - 1 = 4 by rfl, hp, Bool.and_false, Bool.false_and]
          · dsimp only; rw [hhi 12 (by decide), Bool.or_false]; change row.testBit 5 = false at hp; simp only [show 6 - 1 = 5 by rfl, hp, Bool.and_false, Bool.false_and]
        exact hstep c hprev
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (a := 7) (by omega)))]; rfl
  have hall : ∀ x : Fin 128, pop7 x.val = 2 → isIndepRow7 x.val = true → x.val ∈ indepRows2 := by decide
  exact hall ⟨row, hlt⟩ hpop his

private def packRows (r0 r1 r2 r3 r4 r5 r6 : Nat) : Nat :=
  r0 ||| (r1 <<< 7) ||| (r2 <<< 14) ||| (r3 <<< 21) ||| (r4 <<< 28) ||| (r5 <<< 35) ||| (r6 <<< 42)

private lemma packRows_eq {m : Nat} (hm : m < 2 ^ 49) :
    packRows (row49 m 0) (row49 m 1) (row49 m 2) (row49 m 3) (row49 m 4) (row49 m 5) (row49 m 6) = m := by
  have hlt : packRows (row49 m 0) (row49 m 1) (row49 m 2) (row49 m 3) (row49 m 4) (row49 m 5) (row49 m 6) < 2 ^ 49 := by
    have hsh : ∀ (r : Fin 7) (k : Nat), k ≤ 42 → row49 m r <<< k < 2 ^ 49 := fun r k hk => by
      rw [Nat.shiftLeft_eq]
      calc row49 m r * 2 ^ k < 128 * 2 ^ k := Nat.mul_lt_mul_of_pos_right (row49_lt m r) (by positivity)
        _ ≤ 128 * 2 ^ 42 := Nat.mul_le_mul_left 128 (pow2_mono hk)
        _ = 2 ^ 49 := by decide
    have h0 : row49 m 0 < 2 ^ 49 := lt_trans (row49_lt m 0) (by decide)
    unfold packRows
    exact or_lt49 (or_lt49 (or_lt49 (or_lt49 (or_lt49 (or_lt49 h0 (hsh 1 7 (by decide)))
      (hsh 2 14 (by decide))) (hsh 3 21 (by decide))) (hsh 4 28 (by decide)))
      (hsh 5 35 (by decide))) (hsh 6 42 (by decide))
  apply ext49 hlt hm
  intro r c
  have hhi : ∀ (x : Fin 7) (i : Nat), 7 ≤ i → (row49 m x).testBit i = false :=
    fun x i hi => Nat.testBit_lt_two_pow (lt_of_lt_of_le (row49_lt m x) (pow2_mono (a := 7) hi))
  rw [← row49_testBit m r c]
  unfold get49 packRows
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have hc := c.isLt
  rcases r with ⟨rv, hrv⟩
  have hrv' : rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 ∨ rv = 4 ∨ rv = 5 ∨ rv = 6 := by omega
  rcases hrv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only; simp only [Nat.zero_mul, Nat.zero_add,
      show ¬(c.val ≥ 7) by omega, show ¬(c.val ≥ 14) by omega, show ¬(c.val ≥ 21) by omega,
      show ¬(c.val ≥ 28) by omega, show ¬(c.val ≥ 35) by omega, show ¬(c.val ≥ 42) by omega,
      decide_false, Bool.false_and, Bool.or_false]; rfl
  · dsimp only; simp only [Nat.one_mul, hhi 0 (7 + c.val) (by omega),
      show 7 + c.val ≥ 7 by omega, show ¬(7 + c.val ≥ 14) by omega, show ¬(7 + c.val ≥ 21) by omega,
      show ¬(7 + c.val ≥ 28) by omega, show ¬(7 + c.val ≥ 35) by omega, show ¬(7 + c.val ≥ 42) by omega,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]; rfl
  · dsimp only; simp only [show (2 : Nat) * 7 = 14 by decide, hhi 0 (14 + c.val) (by omega), hhi 1 (14 + c.val - 7) (by omega),
      show 14 + c.val ≥ 7 by omega, show 14 + c.val ≥ 14 by omega, show ¬(14 + c.val ≥ 21) by omega,
      show ¬(14 + c.val ≥ 28) by omega, show ¬(14 + c.val ≥ 35) by omega, show ¬(14 + c.val ≥ 42) by omega,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]; rfl
  · dsimp only; simp only [show (3 : Nat) * 7 = 21 by decide, hhi 0 (21 + c.val) (by omega), hhi 1 (21 + c.val - 7) (by omega),
      hhi 2 (21 + c.val - 14) (by omega), show 21 + c.val ≥ 7 by omega, show 21 + c.val ≥ 14 by omega,
      show 21 + c.val ≥ 21 by omega, show ¬(21 + c.val ≥ 28) by omega, show ¬(21 + c.val ≥ 35) by omega,
      show ¬(21 + c.val ≥ 42) by omega, decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]; rfl
  · dsimp only; simp only [show (4 : Nat) * 7 = 28 by decide, hhi 0 (28 + c.val) (by omega), hhi 1 (28 + c.val - 7) (by omega),
      hhi 2 (28 + c.val - 14) (by omega), hhi 3 (28 + c.val - 21) (by omega), show 28 + c.val ≥ 7 by omega,
      show 28 + c.val ≥ 14 by omega, show 28 + c.val ≥ 21 by omega, show 28 + c.val ≥ 28 by omega,
      show ¬(28 + c.val ≥ 35) by omega, show ¬(28 + c.val ≥ 42) by omega, decide_true, decide_false,
      Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]; rfl
  · dsimp only; simp only [show (5 : Nat) * 7 = 35 by decide, hhi 0 (35 + c.val) (by omega), hhi 1 (35 + c.val - 7) (by omega),
      hhi 2 (35 + c.val - 14) (by omega), hhi 3 (35 + c.val - 21) (by omega), hhi 4 (35 + c.val - 28) (by omega),
      show 35 + c.val ≥ 7 by omega, show 35 + c.val ≥ 14 by omega, show 35 + c.val ≥ 21 by omega,
      show 35 + c.val ≥ 28 by omega, show 35 + c.val ≥ 35 by omega, show ¬(35 + c.val ≥ 42) by omega,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]; rfl
  · dsimp only; simp only [show (6 : Nat) * 7 = 42 by decide, hhi 0 (42 + c.val) (by omega), hhi 1 (42 + c.val - 7) (by omega),
      hhi 2 (42 + c.val - 14) (by omega), hhi 3 (42 + c.val - 21) (by omega), hhi 4 (42 + c.val - 28) (by omega),
      hhi 5 (42 + c.val - 35) (by omega), show 42 + c.val ≥ 7 by omega, show 42 + c.val ≥ 14 by omega,
      show 42 + c.val ≥ 21 by omega, show 42 + c.val ≥ 28 by omega, show 42 + c.val ≥ 35 by omega,
      show 42 + c.val ≥ 42 by omega, decide_true, Bool.true_and, Bool.false_or, Nat.add_sub_cancel_left]; rfl

private def canon10Candidates : List Nat :=
  let r0 := 1
  let r0n := rowNbr7 r0
  ([4, 8]).flatMap fun r1 =>
    let r1n := rowNbr7 r1
    (indepRows2.filter fun r2 => (r2 &&& r1n) == 0).flatMap fun r2 =>
      let r2n := rowNbr7 r2
      (indepRows1.filter fun r3 => (r3 &&& r2n) == 0).flatMap fun r3 =>
        let r3n := rowNbr7 r3
        (indepRows2.filter fun r4 => (r4 &&& r3n) == 0).flatMap fun r4 =>
          let r4n := rowNbr7 r4
          (indepRows1.filter fun r5 => (r5 &&& r4n) == 0).flatMap fun r5 =>
            let r5n := rowNbr7 r5
            (indepRows2.filter fun r6 => ((r6 &&& r5n) == 0) && ((r6 &&& r0n) == 0)).map fun r6 =>
              packRows r0 r1 r2 r3 r4 r5 r6

private def canon10Witnesses : List (Fin 3 × Aut2) := [
  (0, ⟨false, true, 6, false, 0⟩),
  (0, ⟨true, true, 2, true, 6⟩),
  (0, ⟨true, false, 0, false, 2⟩),
  (0, ⟨false, false, 2, true, 2⟩),
  (1, ⟨false, true, 6, false, 0⟩),
  (1, ⟨true, true, 5, true, 2⟩),
  (2, ⟨false, false, 2, true, 2⟩),
  (1, ⟨true, false, 4, false, 6⟩),
  (1, ⟨false, false, 2, true, 2⟩),
  (2, ⟨true, false, 3, false, 3⟩)
]

private def checkAll {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && checkAll f as bs
  | _, _ => false

private lemma checkAll_sound {α β : Type} {f : α → β → Bool}
    {as : List α} {bs : List β} (h : checkAll f as bs = true) :
    ∀ a ∈ as, ∃ b ∈ bs, f a b = true := by
  induction as generalizing bs with
  | nil => intro a ha; cases ha
  | cons a0 as ih =>
    cases bs with
    | nil => simp [checkAll] at h
    | cons b0 bs =>
      simp only [checkAll, Bool.and_eq_true] at h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact ⟨b0, List.mem_cons.mpr (Or.inl rfl), h.1⟩
      · obtain ⟨b, hb, hfb⟩ := ih h.2 a hmem
        exact ⟨b, List.mem_cons.mpr (Or.inr hb), hfb⟩

private def checkAll4 {α β : Type} (f : α → β → Bool) (as : List α) (bs : List β) : Bool :=
  checkAll f (as.take 60) (bs.take 60) &&
  checkAll f ((as.drop 60).take 60) ((bs.drop 60).take 60) &&
  checkAll f ((as.drop 120).take 60) ((bs.drop 120).take 60) &&
  checkAll f (as.drop 180) (bs.drop 180)

private lemma checkAll4_sound {α β : Type} {f : α → β → Bool}
    {as : List α} {bs : List β} (h : checkAll4 f as bs = true) :
    ∀ a ∈ as, ∃ b ∈ bs, f a b = true := by
  unfold checkAll4 at h
  simp only [Bool.and_eq_true] at h
  intro a ha
  have h1 : a ∈ as.take 60 ∨ a ∈ as.drop 60 := by
    rw [← List.mem_append, List.take_append_drop]; exact ha
  rcases h1 with h1 | h1
  · obtain ⟨b, hb, hf⟩ := checkAll_sound h.1.1.1 a h1
    exact ⟨b, List.mem_of_mem_take hb, hf⟩
  · have h2 : a ∈ (as.drop 60).take 60 ∨ a ∈ as.drop 120 := by
      have : (as.drop 60).drop 60 = as.drop 120 := by rw [List.drop_drop]
      rw [← this, ← List.mem_append, List.take_append_drop]; exact h1
    rcases h2 with h2 | h2
    · obtain ⟨b, hb, hf⟩ := checkAll_sound h.1.1.2 a h2
      exact ⟨b, List.mem_of_mem_drop (List.mem_of_mem_take hb), hf⟩
    · have h3 : a ∈ (as.drop 120).take 60 ∨ a ∈ as.drop 180 := by
        have : (as.drop 120).drop 60 = as.drop 180 := by rw [List.drop_drop]
        rw [← this, ← List.mem_append, List.take_append_drop]; exact h2
      rcases h3 with h3 | h3
      · obtain ⟨b, hb, hf⟩ := checkAll_sound h.1.2 a h3
        exact ⟨b, List.mem_of_mem_drop (List.mem_of_mem_take hb), hf⟩
      · obtain ⟨b, hb, hf⟩ := checkAll_sound h.2 a h3
        exact ⟨b, List.mem_of_mem_drop hb, hf⟩

private theorem canon10_in_orbits_ok :
    checkAll (fun m (p : Fin 3 × Aut2) => (p.2.applyMask (rep p.1)) == m)
      canon10Candidates canon10Witnesses = true := by rfl

private lemma tenSet_shift_profile (p0 p1 p2 p3 p4 p5 p6 : Nat)
    (hsum : p0 + p1 + p2 + p3 + p4 + p5 + p6 = 10)
    (b0 : p0 + p1 ≤ 3) (b1 : p1 + p2 ≤ 3) (b2 : p2 + p3 ≤ 3) (b3 : p3 + p4 ≤ 3)
    (b4 : p4 + p5 ≤ 3) (b5 : p5 + p6 ≤ 3) (b6 : p6 + p0 ≤ 3) :
    (p0 = 1 ∧ p1 = 1 ∧ p2 = 2 ∧ p3 = 1 ∧ p4 = 2 ∧ p5 = 1 ∧ p6 = 2) ∨
    (p1 = 1 ∧ p2 = 1 ∧ p3 = 2 ∧ p4 = 1 ∧ p5 = 2 ∧ p6 = 1 ∧ p0 = 2) ∨
    (p2 = 1 ∧ p3 = 1 ∧ p4 = 2 ∧ p5 = 1 ∧ p6 = 2 ∧ p0 = 1 ∧ p1 = 2) ∨
    (p3 = 1 ∧ p4 = 1 ∧ p5 = 2 ∧ p6 = 1 ∧ p0 = 2 ∧ p1 = 1 ∧ p2 = 2) ∨
    (p4 = 1 ∧ p5 = 1 ∧ p6 = 2 ∧ p0 = 1 ∧ p1 = 2 ∧ p2 = 1 ∧ p3 = 2) ∨
    (p5 = 1 ∧ p6 = 1 ∧ p0 = 2 ∧ p1 = 1 ∧ p2 = 2 ∧ p3 = 1 ∧ p4 = 2) ∨
    (p6 = 1 ∧ p0 = 1 ∧ p1 = 2 ∧ p2 = 1 ∧ p3 = 2 ∧ p4 = 1 ∧ p5 = 2) := by
  have hd : (3 - (p0 + p1)) + (3 - (p1 + p2)) + (3 - (p2 + p3)) + (3 - (p3 + p4)) +
      (3 - (p4 + p5)) + (3 - (p5 + p6)) + (3 - (p6 + p0)) = 1 := by omega
  by_cases c0 : p0 + p1 = 2
  · left; omega
  by_cases c1 : p1 + p2 = 2
  · right; left; omega
  by_cases c2 : p2 + p3 = 2
  · right; right; left; omega
  by_cases c3 : p3 + p4 = 2
  · right; right; right; left; omega
  by_cases c4 : p4 + p5 = 2
  · right; right; right; right; left; omega
  by_cases c5 : p5 + p6 = 2
  · right; right; right; right; right; left; omega
  · right; right; right; right; right; right; omega

private lemma row49_shiftRow (t : Fin 7) (m : Nat) (r : Fin 7) :
    row49 (shiftRow49 t m) (add7 r t) = row49 m r := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < 7
  · let c : Fin 7 := ⟨i, hi⟩
    change (row49 (shiftRow49 t m) (add7 r t)).testBit c.val = (row49 m r).testBit c.val
    rw [row49_testBit, row49_testBit, get49_shiftRow]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (row49_lt _ _) (pow2_mono (a := 7) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (row49_lt _ _) (pow2_mono (a := 7) (by omega)))]

private lemma pop7_row49_shiftCol (t : Fin 7) (m : Nat) (r : Fin 7) :
    pop7 (row49 (shiftCol49 t m) r) = pop7 (row49 m r) := by
  rw [pop7_row49_eq_sum, pop7_row49_eq_sum]
  let e : Fin 7 ≃ Fin 7 := Equiv.mk (fun c => add7 c t) (fun c => add7 c (neg7 t))
    (fun c => (by decide : ∀ t c : Fin 7, add7 (add7 c t) (neg7 t) = c) t c)
    (fun c => (by decide : ∀ t c : Fin 7, add7 (add7 c (neg7 t)) t = c) t c)
  rw [← Equiv.sum_comp e (fun c => (get49 (shiftCol49 t m) r c).toNat)]
  exact Finset.sum_congr rfl fun c _ => congrArg Bool.toNat (get49_shiftCol t m r c)

private lemma pop7_row49_flipCol (m : Nat) (r : Fin 7) :
    pop7 (row49 (flipCol49 m) r) = pop7 (row49 m r) := by
  rw [pop7_row49_eq_sum, pop7_row49_eq_sum]
  let e : Fin 7 ≃ Fin 7 := Equiv.mk neg7 neg7 (by decide) (by decide)
  rw [← Equiv.sum_comp e (fun c => (get49 (flipCol49 m) r c).toNat)]
  exact Finset.sum_congr rfl fun c _ => congrArg Bool.toNat (get49_flipCol m r c)

private theorem tenSet_in_three_orbits {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) (hcard : B.card = 10) :
    ∃ (k : Fin 3) (g : Aut2), ofFinset49 B = g.applyMask (rep k) := by
  have hpop : pop49 (ofFinset49 B) = 10 := by rw [pop49_ofFinset, hcard]
  rw [pop49_eq_rows] at hpop
  have h0 := (row_indep_adj hB 0).2; have h1 := (row_indep_adj hB 1).2
  have h2 := (row_indep_adj hB 2).2; have h3 := (row_indep_adj hB 3).2
  have h4 := (row_indep_adj hB 4).2; have h5 := (row_indep_adj hB 5).2
  have h6 := (row_indep_adj hB 6).2
  have hprof := tenSet_shift_profile _ _ _ _ _ _ _ hpop h0 h1 h2 h3 h4 h5 h6
  have hex_shift : ∃ tr : Fin 7,
      let m1 := ofFinset49 (B.map (Aut2.mk false false tr false 0).toIso.toEquiv.toEmbedding)
      pop7 (row49 m1 0) = 1 ∧ pop7 (row49 m1 1) = 1 ∧ pop7 (row49 m1 2) = 2 ∧
      pop7 (row49 m1 3) = 1 ∧ pop7 (row49 m1 4) = 2 ∧ pop7 (row49 m1 5) = 1 ∧ pop7 (row49 m1 6) = 2 := by
    have hshift_eq : ∀ tr : Fin 7,
        ofFinset49 (B.map (Aut2.mk false false tr false 0).toIso.toEquiv.toEmbedding) =
          shiftRow49 tr (ofFinset49 B) := by
      intro tr; rw [← Aut2.applyMask_ofFinset]; unfold Aut2.applyMask; simp only [seqN_eq]; rfl
    have hrow_sh : ∀ (tr r : Fin 7),
        row49 (shiftRow49 tr (ofFinset49 B)) r = row49 (ofFinset49 B) (add7 r (neg7 tr)) := by
      intro tr r
      have hback : add7 (add7 r (neg7 tr)) tr = r := (by decide : ∀ t r : Fin 7, add7 (add7 r (neg7 t)) t = r) tr r
      conv_lhs => rw [← hback]
      exact row49_shiftRow tr (ofFinset49 B) (add7 r (neg7 tr))
    rcases hprof with hp | hp | hp | hp | hp | hp | hp
    · exact ⟨0, by dsimp only; rw [hshift_eq 0]; simp only [hrow_sh]; exact hp⟩
    · exact ⟨6, by dsimp only; rw [hshift_eq 6]; simp only [hrow_sh]; exact hp⟩
    · exact ⟨5, by dsimp only; rw [hshift_eq 5]; simp only [hrow_sh]; exact hp⟩
    · exact ⟨4, by dsimp only; rw [hshift_eq 4]; simp only [hrow_sh]; exact hp⟩
    · exact ⟨3, by dsimp only; rw [hshift_eq 3]; simp only [hrow_sh]; exact hp⟩
    · exact ⟨2, by dsimp only; rw [hshift_eq 2]; simp only [hrow_sh]; exact hp⟩
    · exact ⟨1, by dsimp only; rw [hshift_eq 1]; simp only [hrow_sh]; exact hp⟩
  obtain ⟨tr, htr⟩ := hex_shift
  let gR : Aut2 := ⟨false, false, tr, false, 0⟩
  let B1 := B.map gR.toIso.toEquiv.toEmbedding
  have hB1 : (C7 ⊠ C7).IsIndepSet (B1 : Set (ZMod 7 × ZMod 7)) := isIndepSet_map_iso' gR.toIso hB
  have hr0_mem := row_mem_indepRows1 (row49_lt _ 0) htr.1
  have hex_tc : ∃ tc : Fin 7, row49 (shiftCol49 tc (ofFinset49 B1)) 0 = 1 := by
    have hshift1 : ∀ (m : Nat) (c0 tc : Fin 7), row49 m 0 = 2 ^ c0.val → add7 c0 tc = 0 →
        row49 (shiftCol49 tc m) 0 = 1 := by
      intro m c0 tc hr0 hadd
      apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 7
      · let c : Fin 7 := ⟨i, hi⟩
        have hback : add7 (add7 c (neg7 tc)) tc = c := (by decide : ∀ t c : Fin 7, add7 (add7 c (neg7 t)) t = c) tc c
        change (row49 (shiftCol49 tc m) 0).testBit c.val = (1 : Nat).testBit c.val
        rw [row49_testBit]; conv_lhs => rw [← hback]
        rw [get49_shiftCol, ← row49_testBit, hr0, Nat.testBit_two_pow]
        have h1bit : (1 : Nat).testBit c.val = decide (0 = c.val) := by
          simpa using (Nat.testBit_two_pow (n := 0) (m := c.val))
        rw [h1bit]
        have hiff : c0.val = (add7 c (neg7 tc)).val ↔ 0 = c.val := by
          have h1 : ∀ a b t : Fin 7, add7 a t = 0 → (a = add7 b (neg7 t) ↔ (0 : Fin 7) = b) := by decide
          have := h1 c0 c tc hadd
          constructor
          · intro he; exact congrArg Fin.val (this.mp (Fin.ext he))
          · intro he; exact congrArg Fin.val (this.mpr (Fin.ext he))
        simp only [hiff]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (row49_lt _ 0) (pow2_mono (a := 7) (by omega)))]
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (show (1 : Nat) < 2 ^ 7 by decide) (pow2_mono (a := 7) (by omega)))]
    simp only [indepRows1, List.mem_cons, List.not_mem_nil, or_false] at hr0_mem
    rcases hr0_mem with h | h | h | h | h | h | h
    · exact ⟨0, hshift1 _ 0 0 h rfl⟩
    · exact ⟨6, hshift1 _ 1 6 h rfl⟩
    · exact ⟨5, hshift1 _ 2 5 h rfl⟩
    · exact ⟨4, hshift1 _ 3 4 h rfl⟩
    · exact ⟨3, hshift1 _ 4 3 h rfl⟩
    · exact ⟨2, hshift1 _ 5 2 h rfl⟩
    · exact ⟨1, hshift1 _ 6 1 h rfl⟩
  obtain ⟨tc, htc⟩ := hex_tc
  let gC : Aut2 := ⟨false, false, 0, false, tc⟩
  let B2 := B1.map gC.toIso.toEquiv.toEmbedding
  have hB2 : (C7 ⊠ C7).IsIndepSet (B2 : Set (ZMod 7 × ZMod 7)) := isIndepSet_map_iso' gC.toIso hB1
  have hm2_eq : ofFinset49 B2 = shiftCol49 tc (ofFinset49 B1) := by
    rw [← Aut2.applyMask_ofFinset]; unfold Aut2.applyMask; simp only [seqN_eq]; rfl
  have hr2_pops : row49 (ofFinset49 B2) 0 = 1 ∧
      pop7 (row49 (ofFinset49 B2) 1) = 1 ∧ pop7 (row49 (ofFinset49 B2) 2) = 2 ∧
      pop7 (row49 (ofFinset49 B2) 3) = 1 ∧ pop7 (row49 (ofFinset49 B2) 4) = 2 ∧
      pop7 (row49 (ofFinset49 B2) 5) = 1 ∧ pop7 (row49 (ofFinset49 B2) 6) = 2 := by
    rw [hm2_eq]
    exact ⟨htc, by rw [pop7_row49_shiftCol]; exact htr.2.1, by rw [pop7_row49_shiftCol]; exact htr.2.2.1,
      by rw [pop7_row49_shiftCol]; exact htr.2.2.2.1, by rw [pop7_row49_shiftCol]; exact htr.2.2.2.2.1,
      by rw [pop7_row49_shiftCol]; exact htr.2.2.2.2.2.1, by rw [pop7_row49_shiftCol]; exact htr.2.2.2.2.2.2⟩
  have hr1_disj0 : ((1 &&& rowNbr7 (row49 (ofFinset49 B2) 1)) == 0) = true := by
    have h := (row_indep_adj hB2 0).1
    change ((row49 (ofFinset49 B2) 0 &&& rowNbr7 (row49 (ofFinset49 B2) 1)) == 0) = true at h
    rwa [hr2_pops.1] at h
  have hr1_mem := row_mem_indepRows1 (row49_lt _ 1) hr2_pops.2.1
  have hflip_pow2 : ∀ (m : Nat) (r c0 : Fin 7), row49 m r = 2 ^ c0.val →
      row49 (flipCol49 m) r = 2 ^ (neg7 c0).val := by
    intro m r c0 hv
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < 7
    · let c : Fin 7 := ⟨i, hi⟩
      have hnn : neg7 (neg7 c) = c := (by decide : ∀ x : Fin 7, neg7 (neg7 x) = x) c
      change (row49 (flipCol49 m) r).testBit c.val = (2 ^ (neg7 c0).val).testBit c.val
      rw [row49_testBit]; conv_lhs => rw [← hnn]
      rw [get49_flipCol, ← row49_testBit, hv, Nat.testBit_two_pow, Nat.testBit_two_pow]
      have hiff : c0.val = (neg7 c).val ↔ (neg7 c0).val = c.val := by
        have h1 : ∀ a b : Fin 7, a = neg7 b ↔ neg7 a = b := by decide
        have := h1 c0 c
        constructor
        · intro he; exact congrArg Fin.val (this.mp (Fin.ext he))
        · intro he; exact congrArg Fin.val (this.mpr (Fin.ext he))
      simp only [hiff]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (row49_lt _ r) (pow2_mono (a := 7) (by omega)))]
      have hlt : 2 ^ (neg7 c0).val < 2 ^ 7 := Nat.pow_lt_pow_right (by decide) (neg7 c0).isLt
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (a := 7) (by omega)))]
  have hex_sc : ∃ sc : Bool,
      let r1' := row49 (if sc then flipCol49 (ofFinset49 B2) else ofFinset49 B2) 1
      r1' = 4 ∨ r1' = 8 := by
    simp only [indepRows1, List.mem_cons, List.not_mem_nil, or_false] at hr1_mem
    rcases hr1_mem with h | h | h | h | h | h | h
    · rw [h] at hr1_disj0; exact absurd hr1_disj0 (by decide)
    · rw [h] at hr1_disj0; exact absurd hr1_disj0 (by decide)
    · exact ⟨false, Or.inl h⟩
    · exact ⟨false, Or.inr h⟩
    · exact ⟨true, Or.inr (hflip_pow2 _ 1 4 h)⟩
    · exact ⟨true, Or.inl (hflip_pow2 _ 1 5 h)⟩
    · rw [h] at hr1_disj0; exact absurd hr1_disj0 (by decide)
  obtain ⟨sc, hsc⟩ := hex_sc
  let gF : Aut2 := ⟨false, false, 0, sc, 0⟩
  let B3 := B2.map gF.toIso.toEquiv.toEmbedding
  have hB3 : (C7 ⊠ C7).IsIndepSet (B3 : Set (ZMod 7 × ZMod 7)) := isIndepSet_map_iso' gF.toIso hB2
  have hm3_eq : ofFinset49 B3 = if sc then flipCol49 (ofFinset49 B2) else ofFinset49 B2 := by
    rw [← Aut2.applyMask_ofFinset]; unfold Aut2.applyMask; simp only [seqN_eq]; cases sc <;> rfl
  have hcand : ofFinset49 B3 ∈ canon10Candidates := by
    have hdisj_symm : ∀ {a b : Nat}, a < 128 → b < 128 →
        ((a &&& rowNbr7 b) == 0) = true → ((b &&& rowNbr7 a) == 0) = true := by
      intro a b ha hb h
      rw [beq_iff_eq] at h ⊢
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_and, Nat.zero_testBit]
      by_cases hi : i < 7
      · let c : Fin 7 := ⟨i, hi⟩
        cases hbc : b.testBit c.val
        · rfl
        · cases hna : (rowNbr7 a).testBit c.val
          · rfl
          · exfalso
            have hab0 : ∀ k : Fin 7, (a.testBit k.val && (rowNbr7 b).testBit k.val) = false := fun k => by
              have := congrArg (fun x => x.testBit k.val) h
              simpa [Nat.testBit_and] using this
            rcases (rowNbr7_testBit ha c).mp hna with h1 | h1 | h1
            · have h2 := hab0 (prev7 c)
              have hbn : (rowNbr7 b).testBit (prev7 c).val = true :=
                (rowNbr7_testBit hb (prev7 c)).mpr (Or.inr (Or.inr (by
                  have : next7 (prev7 c) = c := (by decide : ∀ x : Fin 7, next7 (prev7 x) = x) c
                  rwa [this])))
              rw [h1, hbn] at h2; exact absurd h2 (by decide)
            · have h2 := hab0 c
              have hbn : (rowNbr7 b).testBit c.val = true :=
                (rowNbr7_testBit hb c).mpr (Or.inr (Or.inl hbc))
              rw [h1, hbn] at h2; exact absurd h2 (by decide)
            · have h2 := hab0 (next7 c)
              have hbn : (rowNbr7 b).testBit (next7 c).val = true :=
                (rowNbr7_testBit hb (next7 c)).mpr (Or.inl (by
                  have : prev7 (next7 c) = c := (by decide : ∀ x : Fin 7, prev7 (next7 x) = x) c
                  rwa [this]))
              rw [h1, hbn] at h2; exact absurd h2 (by decide)
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (pow2_mono (a := 7) (by omega)))]; rfl
    have d12 := hdisj_symm (row49_lt _ 1) (row49_lt _ 2) (row_indep_adj hB3 1).1
    have d23 := hdisj_symm (row49_lt _ 2) (row49_lt _ 3) (row_indep_adj hB3 2).1
    have d34 := hdisj_symm (row49_lt _ 3) (row49_lt _ 4) (row_indep_adj hB3 3).1
    have d45 := hdisj_symm (row49_lt _ 4) (row49_lt _ 5) (row_indep_adj hB3 4).1
    have d56 := hdisj_symm (row49_lt _ 5) (row49_lt _ 6) (row_indep_adj hB3 5).1
    have d60 : ((row49 (ofFinset49 B3) 6 &&& rowNbr7 (row49 (ofFinset49 B3) 0)) == 0) = true :=
      (row_indep_adj hB3 6).1
    have h0eq : row49 (ofFinset49 B3) 0 = 1 := by
      rw [hm3_eq]; cases sc
      · exact hr2_pops.1
      · exact hflip_pow2 _ 0 0 hr2_pops.1
    have h1eq : row49 (ofFinset49 B3) 1 = 4 ∨ row49 (ofFinset49 B3) 1 = 8 := by
      rw [hm3_eq]; exact hsc
    have hrow_ind : ∀ r : Fin 7, ∀ c : Fin 7,
        (row49 (ofFinset49 B3) r).testBit c.val = true →
        (row49 (ofFinset49 B3) r).testBit (next7 c).val = false := by
      intro r c hc
      cases hn : (row49 (ofFinset49 B3) r).testBit (next7 c).val
      · rfl
      · exfalso
        rw [row49_testBit, get49_ofFinset] at hc hn
        have hadjc : C7.Adj (toZ7 c) (toZ7 (next7 c)) := by rw [toZ7_next7]; exact c7_adj_add_one _
        have hne : (toZ7 r, toZ7 c) ≠ (toZ7 r, toZ7 (next7 c)) := fun h => hadjc.ne (congrArg Prod.snd h)
        exact hB3 hc hn hne ⟨hne, Or.inl rfl, Or.inr hadjc⟩
    have hpop3 : ∀ r : Fin 7, pop7 (row49 (ofFinset49 B3) r) = pop7 (row49 (ofFinset49 B2) r) := by
      intro r; rw [hm3_eq]; cases sc
      · rfl
      · exact pop7_row49_flipCol _ r
    have m2 : row49 (ofFinset49 B3) 2 ∈ indepRows2 :=
      row_mem_indepRows2 (row49_lt _ 2) (by rw [hpop3, hr2_pops.2.2.1]) (hrow_ind 2)
    have m3 : row49 (ofFinset49 B3) 3 ∈ indepRows1 :=
      row_mem_indepRows1 (row49_lt _ 3) (by rw [hpop3, hr2_pops.2.2.2.1])
    have m4 : row49 (ofFinset49 B3) 4 ∈ indepRows2 :=
      row_mem_indepRows2 (row49_lt _ 4) (by rw [hpop3, hr2_pops.2.2.2.2.1]) (hrow_ind 4)
    have m5 : row49 (ofFinset49 B3) 5 ∈ indepRows1 :=
      row_mem_indepRows1 (row49_lt _ 5) (by rw [hpop3, hr2_pops.2.2.2.2.2.1])
    have m6 : row49 (ofFinset49 B3) 6 ∈ indepRows2 :=
      row_mem_indepRows2 (row49_lt _ 6) (by rw [hpop3, hr2_pops.2.2.2.2.2.2]) (hrow_ind 6)
    have hpack := (packRows_eq (ofFinset49_lt B3)).symm
    rw [hpack]
    unfold canon10Candidates
    simp only [List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false, Bool.and_eq_true]
    exact ⟨row49 (ofFinset49 B3) 1, h1eq,
      row49 (ofFinset49 B3) 2, ⟨m2, d12⟩,
      row49 (ofFinset49 B3) 3, ⟨m3, d23⟩,
      row49 (ofFinset49 B3) 4, ⟨m4, d34⟩,
      row49 (ofFinset49 B3) 5, ⟨m5, d45⟩,
      row49 (ofFinset49 B3) 6, ⟨m6, d56, by rwa [h0eq] at d60⟩,
      by rw [h0eq]⟩
  obtain ⟨⟨k, g0⟩, _, hmatch⟩ := checkAll_sound canon10_in_orbits_ok _ hcand
  have hB3_eq : ofFinset49 B3 = g0.applyMask (rep k) := (beq_iff_eq.mp hmatch).symm
  have hcomp_mask : ∀ (a b : Aut2) (m : Nat), m < 2 ^ 49 →
      ∃ c : Aut2, a.applyMask (b.applyMask m) = c.applyMask m := by
    intro a b m hm
    rcases a with ⟨swa, sra, tra, sca, tca⟩
    rcases b with ⟨swb, srb, trb, scb, tcb⟩
    have hgen : ∃ c : Aut2, ∀ p : Fin 7 × Fin 7,
        (Aut2.mk swa sra tra sca tca).applyFin ((Aut2.mk swb srb trb scb tcb).applyFin p) = c.applyFin p := by
      cases swb <;> cases swa
      · refine ⟨⟨false, xor sra srb, add7 (if sra then neg7 trb else trb) tra,
          xor sca scb, add7 (if sca then neg7 tcb else tcb) tca⟩, fun ⟨r, c⟩ => ?_⟩
        simp only [Aut2.applyFin, Bool.false_eq_true, ↓reduceIte, d7_comp]
      · refine ⟨⟨true, xor sra srb, add7 (if sra then neg7 trb else trb) tra,
          xor sca scb, add7 (if sca then neg7 tcb else tcb) tca⟩, fun ⟨r, c⟩ => ?_⟩
        simp only [Aut2.applyFin, Bool.false_eq_true, ↓reduceIte, d7_comp]
      · refine ⟨⟨true, xor sca srb, add7 (if sca then neg7 trb else trb) tca,
          xor sra scb, add7 (if sra then neg7 tcb else tcb) tra⟩, fun ⟨r, c⟩ => ?_⟩
        simp only [Aut2.applyFin, Bool.false_eq_true, ↓reduceIte, d7_comp]
      · refine ⟨⟨false, xor sca srb, add7 (if sca then neg7 trb else trb) tca,
          xor sra scb, add7 (if sra then neg7 tcb else tcb) tra⟩, fun ⟨r, c⟩ => ?_⟩
        simp only [Aut2.applyFin, Bool.false_eq_true, ↓reduceIte, d7_comp]
    obtain ⟨c, hc⟩ := hgen
    refine ⟨c, ?_⟩
    apply ext49 (Aut2.applyMask_lt _ (Aut2.applyMask_lt _ hm)) (Aut2.applyMask_lt _ hm)
    intro r c'
    let p := c.inv.applyFin (r, c')
    have h1 := Aut2.get_applyMask c m p.1 p.2
    rw [Prod.mk.eta, c.applyFin_inv] at h1
    rw [h1]
    have h2 := hc p
    rw [c.applyFin_inv] at h2
    have h3 := Aut2.get_applyMask (Aut2.mk swa sra tra sca tca)
      ((Aut2.mk swb srb trb scb tcb).applyMask m)
      ((Aut2.mk swb srb trb scb tcb).applyFin p).1
      ((Aut2.mk swb srb trb scb tcb).applyFin p).2
    rw [Prod.mk.eta, h2] at h3
    rw [h3, Aut2.get_applyMask]
  have hpull : ofFinset49 B = gR.inv.applyMask (gC.inv.applyMask (gF.inv.applyMask (g0.applyMask (rep k)))) := by
    have h1 : ofFinset49 B3 = gF.applyMask (ofFinset49 B2) := (Aut2.applyMask_ofFinset gF B2).symm
    have h2 : ofFinset49 B2 = gC.applyMask (ofFinset49 B1) := (Aut2.applyMask_ofFinset gC B1).symm
    have h3 : ofFinset49 B1 = gR.applyMask (ofFinset49 B) := (Aut2.applyMask_ofFinset gR B).symm
    rw [← hB3_eq, h1, gF.applyMask_inv_left (ofFinset49_lt _),
        h2, gC.applyMask_inv_left (ofFinset49_lt _),
        h3, gR.applyMask_inv_left (ofFinset49_lt _)]
  obtain ⟨g1, hg1⟩ := hcomp_mask gF.inv g0 (rep k) (rep_lt k)
  obtain ⟨g2, hg2⟩ := hcomp_mask gC.inv g1 (rep k) (rep_lt k)
  obtain ⟨g3, hg3⟩ := hcomp_mask gR.inv g2 (rep k) (rep_lt k)
  refine ⟨k, g3, ?_⟩
  rw [hpull, hg1, hg2, hg3]

private theorem tenSet_canon_half {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) (hcard : B.card = 10) :
    ∃ (k : Fin 3) (g : Aut2), (k ≠ 2 ∨ g.sr = false) ∧ ofFinset49 B = g.applyMask (rep k) := by
  obtain ⟨k, g, hEq⟩ := tenSet_in_three_orbits hB hcard
  revert g hEq; revert k
  refine fin3_cases ?_ ?_ ?_
  · intro g hEq; exact ⟨0, g, Or.inl (by decide), hEq⟩
  · intro g hEq; exact ⟨1, g, Or.inl (by decide), hEq⟩
  · intro g hEq
    cases hsr : g.sr
    · exact ⟨2, g, Or.inr hsr, hEq⟩
    · obtain ⟨g', hg'sr, hg'eq⟩ := rep2_stab_flip g hsr
      exact ⟨2, g', Or.inr hg'sr, by rw [hEq, ← hg'eq]⟩

/-! ## Section 4: `Tree10` & Verified `C1`/`C2` Common-Forbidden Tables (49-Bit `Nat`) -/

private inductive Tree10 where
  | tE : Tree10
  | tL : Nat → Tree10
  | tN : Tree10 → Tree10 → Tree10

private def repBits : Fin 3 → List Nat
  | ⟨0, _⟩ => [8, 32, 256, 262144, 1048576, 8388608, 268435456, 4294967296, 137438953472, 4398046511104]
  | ⟨1, _⟩ => [8, 32, 128, 131072, 524288, 4194304, 4294967296, 17179869184, 137438953472, 4398046511104]
  | ⟨2, _⟩ => [8, 32, 256, 131072, 1048576, 4194304, 4294967296, 17179869184, 137438953472, 4398046511104]

private def ptsToBits : List (Fin 7 × Fin 7) → List Nat
  | [] => []
  | (r, c) :: rest => bit49 r c :: ptsToBits rest

private lemma repBits_eq (k : Fin 3) : repBits k = ptsToBits (repPtsList k) := by
  revert k; exact fin3_cases rfl rfl rfl

open Tree10 in
private def Tree10.getAux : Tree10 → List Nat → Nat → Nat
  | tE, _, _ => 0
  | tL v, _, _ => v
  | tN l r, bit :: rest, m =>
      match Nat.beq (Nat.land m bit) 0 with
      | true => l.getAux rest m
      | false => r.getAux rest m
  | tN _ _, [], _ => 0

private lemma land_bit49_eq_zero (m : Nat) (r c : Fin 7) :
    Nat.beq (Nat.land m (bit49 r c)) 0 = !get49 m r c := by
  rw [beq_eq, land_eq]
  unfold get49
  cases h : m.testBit (r.val * 7 + c.val)
  · rw [Bool.not_false, beq_iff_eq]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    unfold bit49; rw [shl_eq, add_eq, mul_eq, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
    by_cases hi : r.val * 7 + c.val = i
    · rw [← hi, h]; rfl
    · simp [hi]
  · rw [Bool.not_true, Bool.eq_false_iff]
    intro heq
    have h0 := beq_iff_eq.mp heq
    have hb := congrArg (fun x => x.testBit (r.val * 7 + c.val)) h0
    rw [Nat.testBit_and, Nat.zero_testBit, h] at hb
    unfold bit49 at hb; rw [shl_eq, add_eq, mul_eq, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow] at hb
    simp at hb

private def countHits (B : Nat) : List (Fin 7 × Fin 7) → Nat
  | [] => 0
  | (r, c) :: rest => (get49 B r c).toNat + countHits B rest

private lemma pop49_le_add_countHits {B X sub : Nat} (hX : X < 2 ^ 49) (hXB : subset49 X B = true)
    (pts : List (Fin 7 × Fin 7))
    (hcov : ∀ p : Fin 7 × Fin 7, get49 X p.1 p.2 = true → get49 sub p.1 p.2 = true ∨ p ∈ pts) :
    pop49 X ≤ pop49 sub + countHits B pts := by
  have h1 : ∀ l : List (Fin 7 × Fin 7),
      (∑ p : Fin 7 × Fin 7, if p ∈ l then (get49 B p.1 p.2).toNat else 0) ≤ countHits B l := by
    intro l
    induction l with
    | nil => simp [countHits]
    | cons p0 rest ih =>
      simp only [countHits, List.mem_cons]
      have hsplit : (∑ p : Fin 7 × Fin 7, if p = p0 ∨ p ∈ rest then (get49 B p.1 p.2).toNat else 0) ≤
          (get49 B p0.1 p0.2).toNat + ∑ p : Fin 7 × Fin 7, if p ∈ rest then (get49 B p.1 p.2).toNat else 0 := by
        have hstep : (∑ p : Fin 7 × Fin 7, if p = p0 ∨ p ∈ rest then (get49 B p.1 p.2).toNat else 0) ≤
            ∑ p : Fin 7 × Fin 7, ((if p = p0 then (get49 B p.1 p.2).toNat else 0) +
              (if p ∈ rest then (get49 B p.1 p.2).toNat else 0)) := by
          refine Finset.sum_le_sum fun p _ => ?_
          by_cases h1 : p = p0 <;> by_cases h2 : p ∈ rest <;> simp [h1, h2]
        rw [Finset.sum_add_distrib] at hstep
        simpa using hstep
      omega
  rw [pop49_eq_sum, pop49_eq_sum, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  have hle : (∑ p : Fin 7 × Fin 7, (get49 X p.1 p.2).toNat) ≤
      (∑ p : Fin 7 × Fin 7, (get49 sub p.1 p.2).toNat) +
      (∑ p : Fin 7 × Fin 7, if p ∈ pts then (get49 B p.1 p.2).toNat else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    cases hXp : get49 X p.1 p.2
    · simp
    · rcases hcov p hXp with hs | hm
      · simp [hs]
      · have hBp : get49 B p.1 p.2 = true := (subset49_iff hX).mp hXB p.1 p.2 hXp
        simp [hm, hBp]
  exact le_trans hle (Nat.add_le_add_left (h1 pts) _)

private lemma pop49_set49_of_false {sub : Nat} {r c : Fin 7} (h : get49 sub r c = false) :
    pop49 (set49 sub r c) = pop49 sub + 1 := by
  rw [pop49_eq_sum, pop49_eq_sum, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  have hsplit : ∀ f : Fin 7 × Fin 7 → Nat,
      (∑ q : Fin 7 × Fin 7, f q) = f (r, c) + ∑ q ∈ Finset.univ.erase (r, c), f q :=
    fun f => (Finset.add_sum_erase _ f (Finset.mem_univ (r, c))).symm
  rw [hsplit, hsplit]
  have hrest : (∑ q ∈ Finset.univ.erase (r, c), (get49 (set49 sub r c) q.1 q.2).toNat) =
      ∑ q ∈ Finset.univ.erase (r, c), (get49 sub q.1 q.2).toNat := by
    refine Finset.sum_congr rfl fun ⟨r', c'⟩ hq => ?_
    have hne : ¬ (r' = r ∧ c' = c) := fun ⟨h1, h2⟩ => (Finset.mem_erase.mp hq).1 (Prod.ext h1 h2)
    rw [get49_set, if_neg hne]
  rw [hrest, get49_set, if_pos ⟨rfl, rfl⟩, h]; simp [Nat.add_comm]

private lemma countHits_repPtsList (k : Fin 3) (B : Nat) :
    countHits B (repPtsList k) = pop49 (B &&& rep k) := by
  rw [pop49_eq_sum, ← Fintype.sum_prod_type']
  have haux : ∀ (l : List (Fin 7 × Fin 7)), l.Nodup →
      countHits B l = ∑ p : Fin 7 × Fin 7, if p ∈ l then (get49 B p.1 p.2).toNat else 0 := by
    intro l hnd
    induction l with
    | nil => simp [countHits]
    | cons p0 rest ih =>
      have ⟨hp0, hrest⟩ := List.nodup_cons.mp hnd
      simp only [countHits, ih hrest]
      have hsplit := (Finset.add_sum_erase (Finset.univ : Finset (Fin 7 × Fin 7))
        (fun p => if p ∈ p0 :: rest then (get49 B p.1 p.2).toNat else 0) (Finset.mem_univ p0)).symm
      rw [hsplit]
      have hsplit2 := (Finset.add_sum_erase (Finset.univ : Finset (Fin 7 × Fin 7))
        (fun p => if p ∈ rest then (get49 B p.1 p.2).toNat else 0) (Finset.mem_univ p0)).symm
      rw [hsplit2, if_neg hp0, zero_add, if_pos (List.mem_cons_self ..)]
      exact congrArg ((get49 B p0.1 p0.2).toNat + ·) (Finset.sum_congr rfl fun p hp => by
        have hne : p ≠ p0 := (Finset.mem_erase.mp hp).1
        simp [List.mem_cons, hne])
  rw [haux _ (repPtsList_nodup k)]
  refine Finset.sum_congr rfl fun ⟨r, c⟩ _ => ?_
  rw [get49_and]
  by_cases hm : (r, c) ∈ repPtsList k
  · have hrep := (rep_mem_iff k r c).mpr hm
    simp [hm, hrep]
  · have hrep : get49 (rep k) r c = false := Bool.eq_false_iff.mpr fun h => hm ((rep_mem_iff k r c).mp h)
    simp [hm, hrep]

section TreeOps
open Tree10

private def Tree10.checkC1 (B : Nat) :
    Tree10 → List Nat → Nat → Nat → Nat → Bool
  | tE, _, _, _, _ => true
  | tL v, [], sub, _, _ =>
      seqN (Nat.land B (Nat.xor ALL49 sub)) fun d =>
      seqN (closedNbr49 d) fun cn =>
      Nat.beq (Nat.land v cn) v
  | tL _, _ :: _, _, _, _ => false
  | tN l r, bit :: rest, sub, sz, rem =>
      match Nat.beq (Nat.land B bit) 0 with
      | true =>
          match Nat.blt (Nat.add sz rem) 4 with
          | true => true
          | false => l.checkC1 B rest sub sz rem
      | false =>
          let rem1 := Nat.sub rem 1
          let okL := match Nat.blt (Nat.add sz rem1) 4 with
                     | true => true
                     | false => l.checkC1 B rest sub sz rem1
          okL && seqN (Nat.lor sub bit) fun s2 => r.checkC1 B rest s2 (Nat.add sz 1) rem1
  | tN _ _, [], _, _, _ => false

private lemma Tree10.checkC1_sound {B X : Nat} (hX : X < 2 ^ 49) (hXpop4 : 4 ≤ pop49 X)
    (hXB : subset49 X B = true) :
    ∀ (t : Tree10) (pts : List (Fin 7 × Fin 7)) (sub : Nat),
      sub < 2 ^ 49 →
      t.checkC1 B (ptsToBits pts) sub (pop49 sub) (countHits B pts) = true →
      (∀ p, get49 X p.1 p.2 = true → get49 sub p.1 p.2 = true ∨ p ∈ pts) →
      (∀ p, get49 sub p.1 p.2 = true → get49 X p.1 p.2 = true ∧ p ∉ pts) →
      pts.Nodup →
      subset49 (t.getAux (ptsToBits pts) X) (closedNbr49 (diff49 B X)) = true := by
  intro t
  induction t with
  | tE => intro _ _ _ _ _ _ _; exact subset49_zero_left _
  | tL v =>
    intro pts sub hsub_lt hchk hcov hsub _
    cases pts with
    | cons _ _ => simp [ptsToBits, Tree10.checkC1] at hchk
    | nil =>
      simp only [ptsToBits, Tree10.checkC1, seqN_eq] at hchk
      have hXeq : X = sub := by
        apply ext49 hX hsub_lt
        intro r c
        cases hx : get49 X r c
        · cases hs : get49 sub r c
          · rfl
          · exact absurd (hsub (r, c) hs).1 (by simp [hx])
        · rcases hcov (r, c) hx with hs | hnil
          · exact hs.symm
          · cases hnil
      subst hXeq; exact hchk
  | tN l r ihl ihr =>
    intro pts sub hsub_lt hchk hcov hsub hnd
    cases pts with
    | nil => simp [ptsToBits, Tree10.checkC1] at hchk
    | cons p rest =>
      rcases p with ⟨row, col⟩
      have ⟨hp_not_rest, hrest_nd⟩ := List.nodup_cons.mp hnd
      simp only [ptsToBits] at hchk ⊢
      unfold Tree10.checkC1 at hchk
      dsimp only at hchk
      rw [land_bit49_eq_zero B row col] at hchk
      unfold Tree10.getAux
      rw [land_bit49_eq_zero X row col]
      cases hBp : get49 B row col
      · rw [hBp] at hchk
        have hXp : get49 X row col = false := by
          cases hx : get49 X row col
          · rfl
          · exact absurd ((subset49_iff hX).mp hXB row col hx) (by simp [hBp])
        rw [hXp]
        have hcnt : countHits B ((row, col) :: rest) = countHits B rest := by simp [countHits, hBp]
        have hcov' : ∀ q, get49 X q.1 q.2 = true → get49 sub q.1 q.2 = true ∨ q ∈ rest := by
          intro q hq
          rcases hcov q hq with hs | hmem
          · exact Or.inl hs
          · rcases List.mem_cons.mp hmem with rfl | hr
            · exact absurd hq (by simp [hXp])
            · exact Or.inr hr
        have hsub' : ∀ q, get49 sub q.1 q.2 = true → get49 X q.1 q.2 = true ∧ q ∉ rest := by
          intro q hq; have ⟨h1, h2⟩ := hsub q hq
          exact ⟨h1, fun hr => h2 (List.mem_cons_of_mem _ hr)⟩
        have hge4 : 4 ≤ pop49 sub + countHits B rest :=
          hXpop4.trans (pop49_le_add_countHits hX hXB rest hcov')
        have hblt : Nat.blt (pop49 sub + countHits B rest) 4 = false := by
          cases h : Nat.blt (pop49 sub + countHits B rest) 4
          · rfl
          · exfalso; have := Nat.blt_eq.mp h; omega
        simp only [add_eq, Bool.not_false, hcnt, hblt] at hchk
        exact ihl rest sub hsub_lt hchk hcov' hsub' hrest_nd
      · rw [hBp] at hchk
        have hcnt : countHits B ((row, col) :: rest) - 1 = countHits B rest := by simp [countHits, hBp]
        simp only [add_eq, sub_eq, Bool.not_true, Bool.and_eq_true, seqN_eq] at hchk
        cases hXp : get49 X row col
        · have hcov' : ∀ q, get49 X q.1 q.2 = true → get49 sub q.1 q.2 = true ∨ q ∈ rest := by
            intro q hq
            rcases hcov q hq with hs | hmem
            · exact Or.inl hs
            · rcases List.mem_cons.mp hmem with rfl | hr
              · exact absurd hq (by simp [hXp])
              · exact Or.inr hr
          have hsub' : ∀ q, get49 sub q.1 q.2 = true → get49 X q.1 q.2 = true ∧ q ∉ rest := by
            intro q hq; have ⟨h1, h2⟩ := hsub q hq
            exact ⟨h1, fun hr => h2 (List.mem_cons_of_mem _ hr)⟩
          have hge4 : 4 ≤ pop49 sub + countHits B rest :=
            hXpop4.trans (pop49_le_add_countHits hX hXB rest hcov')
          have hblt : Nat.blt (pop49 sub + countHits B rest) 4 = false := by
            cases h : Nat.blt (pop49 sub + countHits B rest) 4
            · rfl
            · exfalso; have := Nat.blt_eq.mp h; omega
          have hL := hchk.1
          rw [hcnt, hblt] at hL
          exact ihl rest sub hsub_lt hL hcov' hsub' hrest_nd
        · have hsub_f : get49 sub row col = false := by
            cases hs : get49 sub row col
            · rfl
            · exact absurd (List.mem_cons_self ..) (hsub (row, col) hs).2
          have hpop_set : pop49 (set49 sub row col) = pop49 sub + 1 := pop49_set49_of_false hsub_f
          have hR := hchk.2
          change r.checkC1 B (ptsToBits rest) (set49 sub row col) (pop49 sub + 1) (countHits B ((row, col) :: rest) - 1) = true at hR
          rw [← hpop_set, hcnt] at hR
          refine ihr rest (set49 sub row col) (set49_lt hsub_lt row col) hR ?_ ?_ hrest_nd
          · intro q hq
            rcases hcov q hq with hs | hmem
            · left; rw [get49_set]; split <;> [rfl; exact hs]
            · rcases List.mem_cons.mp hmem with rfl | hr
              · left; rw [get49_set]; simp
              · exact Or.inr hr
          · intro q hq
            rw [get49_set] at hq
            split at hq
            · rename_i heq
              rcases q with ⟨qr, qc⟩; dsimp only at heq
              rw [heq.1, heq.2]
              exact ⟨hXp, hp_not_rest⟩
            · have ⟨h1, h2⟩ := hsub q hq
              exact ⟨h1, fun hr => h2 (List.mem_cons_of_mem _ hr)⟩

private def c1Tree0_00 : Tree10 := (tN (tN (tN (tN (tN tE (tN tE (tN tE (tN tE (tL 545361657593855))))) (tN (tN tE (tN tE (tN tE (tL 547574494789631)))) (tN (tN tE (tN tE (tL 494243481124863))) (tN (tN tE (tL 554638774370303)) (tN (tL 558551909007359) (tL 545357886914559)))))) (tN (tN (tN tE (tN tE (tN tE (tL 547610476138495)))) (tN (tN tE (tN tE (tL 212771737165758))) (tN (tN tE (tL 554638785896447)) (tN (tL 560857898541055) (tL 545361656537087))))) (tN (tN (tN tE (tN tE (tL 496494447681535))) (tN (tN tE (tL 556889740926975)) (tN (tL 560871712481279) (tL 547608853471231)))) (tN (tN (tN tE (tL 547434502545407)) (tN (tL 509739722072063) (tL 494243480068095))) (tN (tN (tL 561270202818559) (tL 554638773313535)) (tN (tL 560854127861759) (tL 545357885857791))))))) (tN (tN (tN (tN tE (tN tE (tN tE (tL 547576000151551)))) (tN (tN tE (tN tE (tL 547023776120831))) (tN (tN tE (tL 554638686027775)) (tN (tL 560857798672383) (tL 545361556668415))))) (tN (tN (tN tE (tN tE (tL 549236596408319))) (tN (tN tE (tL 556855264411647)) (tN (tL 560871595606015) (tL 547574376955903)))) (tN (tN (tN tE (tL 547435526619135)) (tN (tL 562516230537215) (tL 547019988533247))) (tN (tN (tL 561270086041599) (tL 554638656536575)) (tN (tL 560854011084799) (tL 545357769080831)))))) (tN (tN (tN (tN tE (tN tE (tL 549274658131967))) (tN (tN tE (tL 556889635147775)) (tN (tL 560873217314815) (tL 547610358304767)))) (tN (tN (tN tE (tL 547436024287231)) (tN (tL 562519949430783) (tL 547023707426815))) (tN (tN (tL 561270113947647) (tL 554638684442623)) (tN (tL 560857797087231) (tL 545361555083263))))) (tN (tN (tN (tN tE (tL 549755681886207)) (tN (tL 562533746462719) (tL 549270887452671))) (tN (tN (tL 561285385259007) (tL 556889622564863)) (tN (tL 560871594119167) (tL 547608735109119)))) (tN (tN (tN (tL 562931699912575) (tL 547435457925119)) (tN (tL 562516161843199) (tL 547019919839231))) (tN (tN (tL 561270084456447) (tL 554638654951423)) (tN (tL 560854009499647) tE))))))) (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 547576117984892)))) (tN (tN tE (tN tE (tL 494247251803900))) (tN (tN tE (tL 554638786952956)) (tN (tL 560857899597567) (tL 545361657593596))))) (tN (tN (tN tE (tN tE (tL 496460088901372))) (tN (tN tE (tL 556855382146812)) (tN (tL 534414698118909) (tL 547574494691068)))) (tN (tN (tN tE (tL 547434503503612)) (tN (tL 509739723030271) (tL 494243481026300))) (tN (tN (tL 561270203776767) (tL 554638774271740)) (tN (tL 560854128819967) (tL 545357886815996)))))) (tN (tN (tN (tN tE (tN tE (tL 496498217815676))) (tN (tN tE (tL 556889752964732)) (tN (tL 560873335131775) (tL 547610476121724)))) (tN (tN (tN tE (tL 547436125691516)) (tN (tL 509743492734591) (tL 494247250730620))) (tN (tN (tL 561270215384703) (tL 554638785879676)) (tN (tL 560857898524287) (tL 545361656520316))))) (tN (tN (tN (tN tE (tL 549754189520508)) (tN (tL 509757306576511) (tL 496494447566460))) (tN (tN (tL 561287787323007) (tL 556889740811900)) (tN (tL 560871712366207) (tL 547608853356156)))) (tN (tN (tN (tL 562930744433791) (tL 547434502430332)) (tN (tL 509739721956991) (tL 494243479953020))) (tN (tN (tL 561270202703487) (tL 554638773198460)) (tN (tL 560854127746687) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 549240367087356))) (tN (tN tE (tL 556855276994300)) (tN (tL 560873218899709) (tL 547576000151292)))) (tN (tN (tN tE (tL 547436092980988)) (tN (tL 562520018124543) (tL 547023776120572))) (tN (tN (tL 561270115532543) (tL 554638686027516)) (tN (tL 560857798672127) (tL 545361556668156))))) (tN (tN (tN (tN tE (tL 549652671266556)) (tN (tL 562533815058173) (tL 549236596309756))) (tN (tN (tL 561287670562557) (tL 556855264313084)) (tN (tL 560871595605757) (tL 547574376857340)))) (tN (tN (tN (tL 562931768524031) (tL 547435526520572)) (tN (tL 562516230438655) (tL 547019988434684))) (tN (tN (tL 561270085943039) (tL 554638656438012)) (tN (tL 560854010986239) tE))))) (tN (tN (tN (tN (tN tE (tL 549755694452348)) (tN (tL 562537517125247) (tL 549274658115196))) (tN (tN (tL 561287681642111) (tL 556889635131004)) (tN (tL 560873217298047) (tL 547610358287996)))) (tN (tN (tN (tL 562932266273919) (tL 547436024270460)) (tN (tL 562519949414015) (tL 547023707410044))) (tN (tN (tL 561270113930879) (tL 554638684425852)) (tN (tL 560857797070463) tE)))) (tN (tN (tN (tN (tL 562949821303935) (tL 549755681771132)) (tN (tL 562533746347647) (tL 549270887337596))) (tN (tN (tL 561287668960895) (tL 556889622449788)) (tN (tL 560871594004095) tE))) (tN (tN (tN (tL 562931699813503) (tL 547435457810044)) (tN (tL 562516161728127) tE)) (tN (tN (tL 561270084341375) tE) tE)))))))
private def c1Tree0_01 : Tree10 := (tN (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 55029268479887)))) (tN (tN tE (tN tE (tL 72034923052959))) (tN (tN tE (tL 132426458202015)) (tN (tL 420120547557343) (tL 123149328842655))))) (tN (tN (tN tE (tN tE (tL 74281983672223))) (tN (tN tE (tL 134677276917663)) (tN (tL 420134225182687) (tL 125396389461919)))) (tN (tN (tN tE (tL 125222174850975)) (tN (tL 369002371088351) (tL 72031152373663))) (tN (tN (tL 420532851834847) (tL 132426445619103)) (tN (tL 420116776878047) (tL 123145558163359)))))) (tN (tN (tN (tN tE (tN tE (tL 74285752766367))) (tN (tN tE (tL 134677287915423)) (tN (tL 420135846793183) (tL 125398011072415)))) (tN (tN (tN tE (tL 125223660670876)) (tN (tL 369006004391903) (tL 72034785677215))) (tN (tN (tL 420532727046111) (tL 132426320830367)) (tN (tL 420120410185695) (tL 123149191471007))))) (tN (tN (tN (tN tE (tL 127541724565407)) (tN (tL 369019818332127) (tL 74281982611359))) (tN (tN (tL 420548015267807) (tL 134677275860895)) (tN (tL 420134224125919) (tL 125396388405151)))) (tN (tN (tN (tL 140718279479199) (tL 125222037475231)) (tN (tL 369002233712607) (tL 72031014997919))) (tN (tN (tL 420532714463199) (tL 132426308247455)) (tN (tL 420116639506399) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 127062261759903))) (tN (tN tE (tL 134677238775711)) (tN (tL 420135797653471) (tL 125397961932703)))) (tN (tN (tN tE (tL 125223764230047)) (tN (tL 421782666084319) (tL 124811447369631))) (tN (tN (tL 420532830601183) (tL 132426424385439)) (tN (tL 420120513740767) (tL 123149295026079))))) (tN (tN (tN (tN tE (tL 127543285514143)) (tN (tL 421796326801375) (tL 127058491080607))) (tN (tN (tL 420546423678943) (tL 134677226192799)) (tN (tL 420134174457823) (tL 125396338737055)))) (tN (tN (tN (tL 140719439871903) (tL 125223197867935)) (tN (tL 421778878496735) (tL 124807659782047))) (tN (tN (tL 420532801109983) (tL 132426394894239)) (tN (tL 420116726153183) tE))))) (tN (tN (tN (tN (tN tE (tL 127543229403039)) (tN (tL 421800028786655) (tL 127062193065887))) (tN (tN (tL 420547909486559) (tL 134677170081695)) (tN (tL 420135728959455) (tL 125397893238687)))) (tN (tN (tN (tL 140719801225119) (tL 125223559221151)) (tN (tL 421782461075423) (tL 124811242360735))) (tN (tN (tL 420532625592287) (tL 132426219376543)) (tN (tL 420120308731871) tE)))) (tN (tN (tN (tN (tL 140737220020127) (tL 127543216820127)) (tN (tL 421796258107359) (tL 127058422386591))) (tN (tN (tL 420547896903647) (tL 134677157498783)) (tN (tL 420134105763807) tE))) (tN (tN (tN (tL 140719234863007) (tL 125222992859039)) (tN (tL 421778673487839) tE)) (tN (tN (tL 420532596101087) tE) tE)))))) (tN (tN (tN (tN (tN (tN tE (tN tE (tL 74285754351132))) (tN (tN tE (tL 134677289500188)) (tN (tL 420135848377951) (tL 125398012657180)))) (tN (tN (tN tE (tL 125223798013596)) (tN (tL 369006141767391) (tL 72034923052700))) (tN (tN (tL 420532864417503) (tL 132426458201756)) (tN (tL 420120547557087) (tL 123149328842396))))) (tN (tN (tN (tN tE (tL 127541725527708)) (tN (tL 369019819294431) (tL 74281983573660))) (tN (tN (tL 420547062038044) (tL 134677276819100)) (tN (tL 420134225084127) (tL 125396389363356)))) (tN (tN (tN (tL 140718416756383) (tL 125222174752412)) (tN (tL 369002370989791) (tL 72031152275100))) (tN (tN (tL 420532851736287) (tL 132426445520540)) (tN (tL 420116776779487) tE))))) (tN (tN (tN (tN (tN tE (tL 127543347187228)) (tN (tL 369023588470367) (tL 74285752749596))) (tN (tN (tL 420550311120479) (tL 134677287898652)) (tN (tL 420135846776415) (tL 125398011055644)))) (tN (tN (tN (tL 140719902625311) (tL 125223660621340)) (tN (tL 369006004375135) (tL 72034785660444))) (tN (tN (tL 420532727029343) (tL 132426320813596)) (tN (tL 420120410168927) tE)))) (tN (tN (tN (tN (tL 140735863983647) (tL 127541724450332)) (tN (tL 369019818217055) (tL 74281982496284))) (tN (tN (tL 420550298967647) (tL 134677275745820)) (tN (tL 420134224010847) tE))) (tN (tN (tN (tL 140718279364127) (tL 125222037360156)) (tN (tL 369002233597535) tE)) (tN (tN (tL 420532714348127) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 127543298096796)) (tN (tL 421800097480415) (tL 127062261759644))) (tN (tN (tL 420550261997279) (tL 134677238775452)) (tN (tL 420135797653215) (tL 125397961932444)))) (tN (tN (tN (tL 140720006233759) (tL 125223764229788)) (tN (tL 421782666084063) (tL 124811447369372))) (tN (tN (tL 420532830600927) (tL 132426424385180)) (tN (tL 420120513740511) tE)))) (tN (tN (tN (tN (tL 140737424948895) (tL 127543285415580)) (tN (tL 421796326702815) (tL 127058490982044))) (tN (tN (tL 420550249316063) (tL 134677226094236)) (tN (tL 420134174359263) tE))) (tN (tN (tN (tL 140719439773343) (tL 125223197769372)) (tN (tL 421778878398175) tE)) (tN (tN (tL 420532801011423) tE) tE)))) (tN (tN (tN (tN (tN (tL 140737368919583) (tL 127543229386268)) (tN (tL 421800028769887) (tL 127062193049116))) (tN (tN (tL 420550193286751) (tL 134677170064924)) (tN (tL 420135728942687) tE))) (tN (tN (tN (tL 140719801208351) (tL 125223559204380)) (tN (tL 421782461058655) tE)) (tN (tN (tL 420532625575519) tE) tE))) (tN (tN (tN (tN (tL 140737356238367) (tL 127543216705052)) (tN (tL 421796257992287) tE)) (tN (tN (tL 420550180605535) tE) tE)) (tN (tN (tN (tL 140719234747935) tE) tE) tE))))))
private def c1Tree0_10 : Tree10 := (tN (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 494799559852019)))) (tN (tN tE (tN tE (tL 494247251803127))) (tN (tN tE (tL 554638786953207)) (tN (tL 508081341464567) (tL 492585099460599))))) (tN (tN (tN tE (tN tE (tL 496460088998903))) (tN (tN tE (tL 556855382245367)) (tN (tL 508095155306487) (tL 494797936656375)))) (tN (tN (tN tE (tL 547435577342967)) (tN (tL 509670986677239) (tL 494243481123831))) (tN (tN (tL 561270203875319) (tL 554638774370295)) (tN (tL 508077570785271) (tL 492581328781303)))))) (tN (tN (tN (tN tE (tN tE (tL 496498217831415))) (tN (tN tE (tL 556889752981495)) (tN (tL 508096777015287) (tL 494833918005239)))) (tN (tN (tN tE (tL 547436125740023)) (tN (tL 509743492750327) (tL 494247250746359))) (tN (tN (tL 561270215401463) (tL 554638785896439)) (tN (tL 508081340407799) (tL 492585098403831))))) (tN (tN (tN (tN tE (tL 549755800247287)) (tN (tL 509757306690551) (tL 496494447680503))) (tN (tN (tL 561287787438071) (tL 556889740926967)) (tN (tL 508095154348023) (tL 494832295337975)))) (tN (tN (tN (tL 562931818288103) (tL 547435576286199)) (tN (tL 509739722071031) (tL 494243480067063))) (tN (tN (tL 561270202818551) (tL 554638773313527)) (tN (tL 508077569728503) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 496463808951287))) (tN (tN tE (tL 556855276991479)) (tN (tL 508095587021815) (tL 494799442015223)))) (tN (tN (tN tE (tL 547436092978167)) (tN (tL 509743459988471) (tL 494247217984503))) (tN (tN (tL 561270115529719) (tL 554638686024695)) (tN (tL 508081240536055) (tL 492584998532087))))) (tN (tN (tN (tN tE (tL 549652671362039)) (tN (tL 509757256922103) (tL 496460038271991))) (tN (tN (tL 561287670559735) (tL 556855264408567)) (tN (tL 508095037469687) (tL 494797818819575)))) (tN (tN (tN (tL 562931768620007) (tL 547435526616055)) (tN (tL 509739672400887) (tL 494243430396919))) (tN (tN (tL 561270086038519) (tL 554638656533495)) (tN (tL 508077452948471) tE))))) (tN (tN (tN (tN (tN tE (tL 549755694466039)) (tN (tL 509760959005687) (tL 496498099995639))) (tN (tN (tL 561287681655799) (tL 556889635144695)) (tN (tL 508096659178487) (tL 494833800168439)))) (tN (tN (tN (tL 562932266288103) (tL 547436024284151)) (tN (tL 509743391294455) (tL 494247149290487))) (tN (tN (tL 561270113944567) (tL 554638684439543)) (tN (tL 508081238950903) tE)))) (tN (tN (tN (tN (tL 562949821416423) (tL 549755681883127)) (tN (tL 509757188326391) (tL 496494329316343))) (tN (tN (tL 561287669072887) (tL 556889622561783)) (tN (tL 508095035982839) tE))) (tN (tN (tN (tL 562931699925991) (tL 547435457922039)) (tN (tL 509739603706871) tE)) (tN (tN (tL 561270084453367) tE) tE)))))) (tN (tN (tN (tN (tN (tN tE (tN tE (tL 496463859677296))) (tN (tN tE (tL 556855394827376)) (tN (tL 508096778599536) (tL 494799559851120)))) (tN (tN (tN tE (tL 547436126796016)) (tN (tL 509743493806323) (tL 494247251802352))) (tN (tN (tL 561270216457459) (tL 554638786952432)) (tN (tL 508081341463795) (tL 492585099459824))))) (tN (tN (tN (tN tE (tL 549652721989872)) (tN (tL 509757307648241) (tL 496460088899824))) (tN (tN (tL 561287788395761) (tL 556855382146288)) (tN (tL 508095155305713) (tL 494797936557296)))) (tN (tN (tN (tL 562931819245795) (tL 547435577243888)) (tN (tL 509739723028723) (tL 494243481024752))) (tN (tN (tL 561270203776243) (tL 554638774271216)) (tN (tL 508077570686195) tE))))) (tN (tN (tN (tN (tN tE (tL 549755812284528)) (tN (tL 509761076824179) (tL 496498217814128))) (tN (tN (tL 561287799475315) (tL 556889752964208)) (tN (tL 508096776998003) (tL 494833917987952)))) (tN (tN (tN (tL 562932367724643) (tL 547436125722736)) (tN (tL 509743492733043) (tL 494247250729072))) (tN (tN (tL 561270215384179) (tL 554638785879152)) (tN (tL 508081340390515) tE)))) (tN (tN (tN (tN (tL 562949939662947) (tL 549755800131696)) (tN (tL 509757306574963) (tL 496494447564912))) (tN (tN (tL 561287787322483) (tL 556889740811376)) (tN (tL 508095154232435) tE))) (tN (tN (tN (tL 562931818172515) (tL 547435576170608)) (tN (tL 509739721955443) tE)) (tN (tN (tL 561270202702963) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 549652683944176)) (tN (tL 509761027698929) (tL 496463808950512))) (tN (tN (tL 561287683240177) (tL 556855276990704)) (tN (tL 508096660762865) (tL 494799442014448)))) (tN (tN (tN (tL 562932334981347) (tL 547436092977392)) (tN (tL 509743459987699) (tL 494247217983728))) (tN (tN (tL 561270115528947) (tL 554638686023920)) (tN (tL 508081240535283) tE)))) (tN (tN (tN (tN (tL 562949890011361) (tL 549652671262960)) (tN (tL 509757256921329) (tL 496460038172912))) (tN (tN (tL 561287670558961) (tL 556855264309488)) (tN (tL 508095037468913) tE))) (tN (tN (tN (tL 562931768520931) (tL 547435526516976)) (tN (tL 509739672301811) tE)) (tN (tN (tL 561270085939443) tE) tE)))) (tN (tN (tN (tN (tN (tL 562949833982051) (tL 549755694448752)) (tN (tL 509760958988403) (tL 496498099978352))) (tN (tN (tL 561287681638515) (tL 556889635127408)) (tN (tL 508096659161203) tE))) (tN (tN (tN (tL 562932266270819) (tL 547436024266864)) (tN (tL 509743391277171) tE)) (tN (tN (tL 561270113927283) tE) tE))) (tN (tN (tN (tN (tL 562949821300835) (tL 549755681767536)) (tN (tL 509757188210803) tE)) (tN (tN (tL 561287668957299) tE) tE)) (tN (tN (tN (tL 562931699810403) tE) tE) tE))))))
private def c1Tree0_11 : Tree10 := (tN (tN (tN (tN (tN (tN (tN tE (tN tE (tL 3917010170243))) (tN (tN tE (tL 64308545322883)) (tN (tL 296990546067395) (tL 2252710346627)))) (tN (tN (tN tE (tL 54855053865863)) (tN (tL 298637397586887) (tL 1666178872199))) (tN (tN (tL 350164120240071) (tL 62057714024327)) (tN (tL 296975245246407) (tL 4026531719))))) (tN (tN (tN (tN tE (tL 57174592058247)) (tN (tL 298651075212231) (tL 3913239491463))) (tN (tN (tL 350181555961799) (tL 64308532739975)) (tN (tL 296988922871751) (tL 2251087150983)))) (tN (tN (tN (tL 70350746416007) (tL 54854504412039)) (tN (tL 298633626907591) (tL 1662408192903))) (tN (tN (tL 350164107657159) (tL 62057701441415)) (tN (tL 296971474567111) tE))))) (tN (tN (tN (tN (tN tE (tL 57174603056007)) (tN (tL 298654844306375) (tL 3917008585607))) (tN (tN (tL 350181566959559) (tL 64308543737735)) (tN (tL 296990544482247) (tL 2252708761479)))) (tN (tN (tN (tL 70351158494087) (tL 54854916490119)) (tN (tL 298637260211143) (tL 1666041496455))) (tN (tN (tL 350163982868423) (tL 62057576652679)) (tN (tL 296975107874759) tE)))) (tN (tN (tN (tN (tL 70368730530695) (tL 57174590997383)) (tN (tL 298651074151367) (tL 3913238430599))) (tN (tN (tL 350181554905031) (tL 64308531683207)) (tN (tL 296988921814983) tE))) (tN (tN (tN (tL 70350609040263) (tL 54854367036295)) (tN (tL 298633489531847) tE)) (tN (tN (tL 350163970285511) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 4397995778947)) (tN (tL 298654795166663) (tL 3916959445895))) (tN (tN (tL 314720052700103) (tL 64308494594951)) (tN (tL 296990495339463) (tL 2252659618695)))) (tN (tN (tN (tL 70351262053255) (tL 54855020049287)) (tN (tL 298637363770311) (tL 1666145055623))) (tN (tN (tL 350164086420423) (tL 62057680204679)) (tN (tL 296975211426759) tE)))) (tN (tN (tN (tN (tL 70368680866695) (tL 57174541333383)) (tN (tL 298651024487367) (tL 3913188766599))) (tN (tN (tL 350181505233863) (tL 64308482012039)) (tN (tL 296988872143815) tE))) (tN (tN (tN (tL 70350695691143) (tL 54854453687175)) (tN (tL 298633576182727) tE)) (tN (tN (tL 350164056929223) tE) tE)))) (tN (tN (tN (tN (tN (tL 70368624755591) (tL 57174485222279)) (tN (tL 298654726472647) (tL 3916890751879))) (tN (tN (tL 350181449122759) (tL 64308425900935)) (tN (tL 296990426645447) tE))) (tN (tN (tN (tL 70351057044359) (tL 54854815040391)) (tN (tL 298637158761415) tE)) (tN (tN (tL 350163881411527) tE) tE))) (tN (tN (tN (tN (tL 70368612172679) (tL 57174472639367)) (tN (tL 298650955793351) tE)) (tN (tN (tL 350181436539847) tE) tE)) (tN (tN (tN (tL 70350490682247) tE) tE) tE))))) (tN (tN (tN (tN (tN (tN (tN tE (tL 57174604640256)) (tN (tL 298654845890627) (tL 3917010169856))) (tN (tN (tL 314997196454915) (tL 64308545321984)) (tN (tL 296990546066499) (tL 2252710345728)))) (tN (tN (tN (tL 70351295869059) (tL 54855053865088)) (tN (tL 298637397586115) (tL 1666178871424))) (tN (tN (tL 350164120239299) (tL 62057714023552)) (tN (tL 296975245245635) tE)))) (tN (tN (tN (tN (tL 70368731492483) (tL 57174591959168)) (tN (tL 298651075113155) (tL 3913239392384))) (tN (tN (tL 350181555862723) (tL 64308532640896)) (tN (tL 296988922772675) tE))) (tN (tN (tN (tL 70350746316931) (tL 54854504312960)) (tN (tL 298633626808515) tE)) (tN (tN (tL 350164107558083) tE) tE)))) (tN (tN (tN (tN (tN (tL 70368742572035) (tL 57174603038720)) (tN (tL 298654844289091) (tL 3917008568320))) (tN (tN (tL 350181566942275) (tL 64308543720448)) (tN (tL 296990544464963) tE))) (tN (tN (tN (tL 70351158476803) (tL 54854916472832)) (tN (tL 298637260193859) tE)) (tN (tN (tL 350163982851139) tE) tE))) (tN (tN (tN (tN (tL 70368730415107) (tL 57174590881792)) (tN (tL 298651074035779) tE)) (tN (tN (tL 350181554789443) tE) tE)) (tN (tN (tN (tL 70350608924675) tE) tE) tE)))) (tN (tN (tN (tN (tN (tN (tL 70368693448835) (tL 57174553915520)) (tN (tL 298654795165891) (tL 3916959445120))) (tN (tN (tL 350181517816003) (tL 64308494594176)) (tN (tL 296990495338691) tE))) (tN (tN (tN (tL 70351262052483) (tL 54855020048512)) (tN (tL 298637363769539) tE)) (tN (tN (tL 350164086419651) tE) tE))) (tN (tN (tN (tN (tL 70368680767619) (tL 57174541234304)) (tN (tL 298651024388291) tE)) (tN (tN (tL 350181505134787) tE) tE)) (tN (tN (tN (tL 70350695592067) tE) tE) tE))) (tN (tN (tN (tN (tN (tL 70368624738307) (tL 57174485204992)) (tN (tL 298654726455363) tE)) (tN (tN (tL 350181449105475) tE) tE)) (tN (tN (tN (tL 70351057027075) tE) tE) tE)) (tN (tN (tN (tN (tL 70368612057091) tE) tE) tE) tE)))))
private def c1Tree0 : Tree10 :=
  tN (tN c1Tree0_00 c1Tree0_01) (tN c1Tree0_10 c1Tree0_11)
private def c1Tree1_00 : Tree10 := (tN (tN (tN (tN (tN tE (tN tE (tN tE (tN tE (tL 263884466290687))))) (tN (tN tE (tN tE (tN tE (tL 248229901893631)))) (tN (tN tE (tN tE (tL 265008596385791))) (tN (tN tE (tL 273163730550783)) (tN (tL 560785342332927) (tL 263882843095039)))))) (tN (tN (tN tE (tN tE (tN tE (tL 248231726927871)))) (tN (tN tE (tN tE (tL 267243600990207))) (tN (tN tE (tL 273164012081151)) (tN (tL 558553549492223) (tL 263884735238143))))) (tN (tN (tN tE (tN tE (tL 250480876310527))) (tN (tN tE (tL 274825352826879)) (tN (tL 536336247803903) (tL 248229841588223)))) (tN (tN (tN tE (tL 276522873638911)) (tN (tL 561911102427135) (tL 267241986183167))) (tN (tN (tL 560993118179327) (tL 273163737354239)) (tN (tL 560785349136383) (tL 263882849898495))))))) (tN (tN (tN (tN tE (tN tE (tN tE (tL 265823930941439)))) (tN (tN tE (tN tE (tL 265010168856575))) (tN (tN tE (tL 273163962941439)) (tN (tL 560787185336319) (tL 263884686098431))))) (tN (tN (tN tE (tN tE (tL 265839621767167))) (tN (tN tE (tL 274825899212799)) (tN (tL 562724536385535) (tL 265822037147647)))) (tN (tN (tN tE (tL 274289433051135)) (tN (tL 561911044800511) (tL 265008545595391))) (tN (tN (tL 560993060585471) (tL 273163679760383)) (tN (tL 560785291542527) (tL 263882792304639)))))) (tN (tN (tN (tN tE (tN tE (tL 268074626435071))) (tN (tN tE (tL 274826113697791)) (tN (tL 562726361483263) (tL 265823862245375)))) (tN (tN (tN tE (tL 276522827106303)) (tN (tL 561912666507263) (tL 267243550263295))) (tN (tN (tL 560993342179327) (tL 273163961354239)) (tN (tL 560787183749119) (tL 263884684511231))))) (tN (tN (tN (tN tE (tL 277076865239039)) (tN (tL 562742119417855) (tL 268073003173887))) (tN (tN (tL 562923646797823) (tL 274825830516735)) (tN (tL 562724467689471) (tL 265821968451583)))) (tN (tN (tN (tL 562118812289023) (tL 276522814457855)) (tN (tL 561911043246079) (tL 267241927002111))) (tN (tN (tL 560993058998271) (tL 273163678173183)) (tN (tL 560785289955327) tE))))))) (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 248231795621436)))) (tN (tN tE (tN tE (tL 265010219580988))) (tN (tN tE (tL 273164013665852)) (tN (tL 560787236060799) (tL 263884736822844))))) (tN (tN (tN tE (tN tE (tL 248247494852156))) (tN (tN tE (tL 274825421471292)) (tN (tL 536336316448383) (tL 248229910232636)))) (tN (tN (tN tE (tL 274289492180540)) (tN (tL 561911103962748) (tL 265008604724796))) (tN (tN (tL 560993119714943) (tL 273163738889788)) (tN (tL 560785350671999) (tL 263882851434044)))))) (tN (tN (tN (tN tE (tN tE (tL 250482491117116))) (tN (tN tE (tL 274826164375100)) (tN (tL 536338133143167) (tL 248231726927420)))) (tN (tN (tN tE (tL 276522877832764)) (tN (tL 561912717233791) (tL 267243600989756))) (tN (tN (tL 560993392905855) (tL 273164012080700)) (tN (tL 560787234475647) (tL 263884735237692))))) (tN (tN (tN (tN tE (tL 277076387499580)) (tN (tL 536353899482751) (tL 250480876260924))) (tN (tN (tL 562923169058431) (tL 274825352777276)) (tN (tL 536336247754367) (tL 248229841538620)))) (tN (tN (tN (tL 562118871420543) (tL 276522873589308)) (tN (tL 561911102377599) (tL 267241986133564))) (tN (tN (tL 560993118129791) (tL 273163737304636)) (tN (tL 560785349086847) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 265841278844476))) (tN (tN tE (tL 274826216209980)) (tN (tL 562726463995519) (tL 265823964757564)))) (tN (tN (tN tE (tL 274289445961276)) (tN (tL 561912668356220) (tL 265010169118268))) (tN (tN (tL 560993344028287) (tL 273163963203132)) (tN (tL 560787185598079) (tL 263884686360124))))) (tN (tN (tN (tN tE (tL 274843517599292)) (tN (tL 562742154772092) (tL 265839655534140))) (tN (tN (tL 562923682152063) (tL 274825932979772)) (tN (tL 562724570152575) (tL 265822070914620)))) (tN (tN (tN (tL 562118814088828) (tL 274289433263676)) (tN (tL 561911045045884) (tL 265008545807932))) (tN (tN (tL 560993060798079) (tL 273163679972924)) (tN (tL 560785291755135) tE))))) (tN (tN (tN (tN (tN tE (tL 277076877887036)) (tN (tL 562743742678655) (tL 268074626434620))) (tN (tN (tL 562923929978495) (tL 274826113697340)) (tN (tL 562726361482879) (tL 265823862244924)))) (tN (tN (tN (tL 562118757761151) (tL 276522827105852)) (tN (tL 561912666506879) (tL 267243550262844))) (tN (tN (tL 560993342178943) (tL 273163961353788)) (tN (tL 560787183748735) tE)))) (tN (tN (tN (tN (tL 562949886314111) (tL 277076865189436)) (tN (tL 562742119368319) (tL 268073003124284))) (tN (tN (tL 562923646748287) (tL 274825830467132)) (tN (tL 562724467639935) tE))) (tN (tN (tN (tL 562118812239487) (tL 276522814408252)) (tN (tL 561911043196543) tE)) (tN (tN (tL 560993058948735) tE) tE)))))))
private def c1Tree1_01 : Tree10 := (tN (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 37125428871055)))) (tN (tN tE (tN tE (tL 55029268479887))) (tN (tN tE (tL 62057714024335)) (tN (tL 349749655896015) (tL 52778437181327))))) (tN (tN (tN tE (tN tE (tL 39374636973967))) (tN (tN tE (tL 63718241075087)) (tN (tL 334095022292943) (tL 37123803578255)))) (tN (tN (tN tE (tL 65416634302351)) (tN (tL 350873582567375) (tL 56135746846607))) (tN (tN (tL 347962934820815) (tL 62057699344271)) (tN (tL 349748030603215) (tL 52776811888527)))))) (tN (tN (tN (tN tE (tN tE (tL 39376258582415))) (tN (tN tE (tL 63719931889550)) (tN (tL 334096713107407) (tL 37125494392719)))) (tN (tN (tN tE (tL 65416645300111)) (tN (tL 350875204177871) (tL 56137368457103))) (tN (tN (tL 66490151978895) (tL 62057779548047)) (tN (tL 349749721419727) (tL 52778502705039))))) (tN (tN (tN (tN tE (tL 65970155014031)) (tN (tL 334112479496143) (tL 39374643775375))) (tN (tN (tL 351825526507471) (tL 63719120291727)) (tN (tL 334094827767759) (tL 37123609053071)))) (tN (tN (tN (tL 351289664327631) (tL 65416641105807)) (tN (tL 350873589370831) (tL 56135753650063))) (tN (tN (tL 350163911036879) (tL 62057504821135)) (tN (tL 349747836080079) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 56968395489167))) (tN (tN tE (tL 63720084078479)) (tN (tL 351689051340751) (tL 54717832626063)))) (tN (tN (tN tE (tL 65416596160399)) (tN (tL 350875155038159) (tL 56137319317391))) (tN (tN (tL 350164337950671) (tL 62057931734927)) (tN (tL 349749873606607) (tL 52778654891919))))) (tN (tN (tN (tN tE (tL 65970634293135)) (tN (tL 351704607948751) (tL 56966772227983))) (tN (tN (tL 351826207113167) (tL 63719800897423)) (tN (tL 351687157546959) (tL 54715938832271)))) (tN (tN (tN (tL 351289606733775) (tL 65416583511951)) (tN (tL 350873531776975) (tL 56135696056207))) (tN (tN (tL 350164054769615) (tL 62057648553871)) (tN (tL 349747979812815) tE))))) (tN (tN (tN (tN (tN tE (tL 65970645354383)) (tN (tL 351706229622735) (tL 56968393901967))) (tN (tN (tL 351826287380431) (tL 63719881164687)) (tN (tL 351688848426959) (tL 54717629712271)))) (tN (tN (tN (tL 351289550619023) (tL 65416594573199)) (tN (tL 350875153450959) (tL 56137317730191))) (tN (tN (tL 350164135036879) (tL 62057728821135)) (tN (tL 349749670692815) tE)))) (tN (tN (tN (tN (tL 351843655927759) (tL 65970632705935)) (tN (tL 351704606361551) (tL 56966770640783))) (tN (tN (tL 351826004199375) (tL 63719597983631)) (tN (tL 351686954633167) tE))) (tN (tN (tN (tL 351289605146575) (tL 65416581924751)) (tN (tL 350873530189775) tE)) (tN (tN (tL 350163851855823) tE) tE)))))) (tN (tN (tN (tN (tN (tN tE (tN tE (tL 39376260169228))) (tN (tN tE (tL 63720134753804)) (tN (tL 334096916020815) (tL 37125697306124)))) (tN (tN (tN tE (tL 65416646884876)) (tN (tL 350875205762639) (tL 56137370041868))) (tN (tN (tL 350164388675151) (tL 62057982459404)) (tN (tL 349749924331087) (tL 52778705616396))))) (tN (tN (tN (tN tE (tL 57070984306188)) (tN (tL 334112481033807) (tL 39374645313036))) (tN (tN (tL 351825729371727) (tL 63719323155980)) (tN (tL 334095030632015) (tL 37123811917324)))) (tN (tN (tN (tL 351285899369998) (tL 65416642641420)) (tN (tL 350873590906447) (tL 56135755185676))) (tN (tN (tL 350164113899087) (tL 62057707683340)) (tN (tL 349748038942287) tE))))) (tN (tN (tN (tN (tN tE (tL 65970696029708)) (tN (tL 334114094302799) (tL 39376258582028))) (tN (tN (tL 351826338055759) (tL 63719931840012)) (tN (tL 334096713107023) (tL 37125494392332)))) (tN (tN (tN (tL 351289567593996) (tL 65416645299724)) (tN (tL 350875204177487) (tL 56137368456716))) (tN (tN (tL 350164185763407) (tL 62057779547660)) (tN (tL 349749721419343) tE)))) (tN (tN (tN (tN (tL 351843178186319) (tL 65970154964492)) (tN (tL 334112479446607) (tL 39374643725836))) (tN (tN (tL 351825526457935) (tL 63719120242188)) (tN (tL 334094827718223) tE))) (tN (tN (tN (tL 351289664278095) (tL 65416641056268)) (tN (tL 350873589321295) tE)) (tN (tN (tL 350163910987343) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 65970680757772)) (tN (tL 351706265026127) (tL 56968429305356))) (tN (tN (tL 351826524110415) (tL 63720117894668)) (tN (tL 351689085156943) (tL 54717866442252)))) (tN (tN (tN (tL 351289653131279) (tL 65416629976588)) (tN (tL 350875188854351) (tL 56137353133580))) (tN (tN (tL 350164371766863) (tL 62057965551116)) (tN (tL 349749907422799) tE)))) (tN (tN (tN (tN (tL 351843691281999) (tL 65970668060172)) (tN (tL 351704641715791) (tL 56966805995020))) (tN (tN (tL 351826240880207) (tL 63719834664460)) (tN (tL 351687191313999) tE))) (tN (tN (tN (tL 351289640500815) (tL 65416617278988)) (tN (tL 350873565544015) tE)) (tN (tN (tL 350164088536655) tE) tE)))) (tN (tN (tN (tN (tN (tL 351843601399823) (tL 65970645353996)) (tN (tL 351706229622351) (tL 56968393901580))) (tN (tN (tL 351826287380047) (tL 63719881164300)) (tN (tL 351688848426575) tE))) (tN (tN (tN (tL 351289550618639) (tL 65416594572812)) (tN (tL 350875153450575) tE)) (tN (tN (tL 350164135036495) tE) tE))) (tN (tN (tN (tN (tL 351843655878223) (tL 65970632656396)) (tN (tL 351704606312015) tE)) (tN (tN (tL 351826004149839) tE) tE)) (tN (tN (tN (tL 351289605097039) tE) tE) tE))))))
private def c1Tree1_10 : Tree10 := (tN (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 494522129709555)))) (tN (tN tE (tN tE (tL 494799559852019))) (tN (tN tE (tL 554638719844339)) (tN (tL 508079126872051) (tL 492582884868083))))) (tN (tN (tN tE (tN tE (tL 496737114388979))) (tN (tN tE (tL 556300926712307)) (tN (tL 510016748517875) (tL 494520506513907)))) (tN (tN (tN tE (tL 557963483807731)) (tN (tL 509203256868851) (tL 495906038218739))) (tN (tN (tL 561270136766451) (tL 554638707261427)) (tN (tL 508077503676403) (tL 492581261672435)))))) (tN (tN (tN (tN tE (tN tE (tL 496773095737843))) (tN (tN tE (tL 556301141133811)) (tN (tL 510018573552115) (tL 494522331548147)))) (tN (tN (tN tE (tL 557997854543859)) (tN (tL 509204878577651) (tL 495942019567603))) (tN (tN (tL 561270418296819) (tL 554638988791795)) (tN (tL 508079395819507) (tL 492583153815539))))) (tN (tN (tN (tN tE (tL 558551901129203)) (tN (tL 510034339940851) (tL 496771480930803))) (tN (tN (tL 562932295911923) (tL 556300866406899)) (tN (tL 510016688212467) (tL 494520446208499)))) (tN (tN (tN (tL 562395896860659) (tL 557997850349555)) (tN (tL 509203263770611) (tL 495940404760563))) (tN (tN (tL 561270143569907) (tL 554638714064883)) (tN (tL 508077510479859) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 496738686857715))) (tN (tN tE (tL 556301159100915)) (tN (tL 510018591519219) (tL 494522349515251)))) (tN (tN (tN tE (tL 557963445662195)) (tN (tL 509203755692531) (tL 495907610685939))) (tN (tN (tL 561270369153523) (tL 554638939648499)) (tN (tL 508079346676211) (tL 492583104672243))))) (tN (tN (tN (tN tE (tL 558517483794931)) (tN (tL 510034282312179) (tL 496737063596531))) (tN (tN (tL 562932305424883) (tL 556300875919859)) (tN (tL 510016697725427) (tL 494520455721459)))) (tN (tN (tN (tL 562395839230451) (tL 557963433013747)) (tN (tL 509203206140403) (tL 495905987424755))) (tN (tN (tL 561270085972467) (tL 554638656467443)) (tN (tL 508077452882419) tE))))) (tN (tN (tN (tN (tN tE (tL 558551854596595)) (tN (tL 510035904020979) (tL 496773045010931))) (tN (tN (tL 562932519911923) (tL 556301090406899)) (tN (tL 510018522825203) (tL 494522280821235)))) (tN (tN (tN (tL 456842666885603) (tL 557997803815411)) (tN (tL 509204827849203) (tL 495941968839155))) (tN (tN (tL 561270367568371) (tL 554638938063347)) (tN (tL 508079345091059) tE)))) (tN (tN (tN (tN (tL 562949888459251) (tL 558551841948147)) (tN (tL 510034280759795) (tL 496771421749747))) (tN (tN (tL 562932236730867) (tL 556300807225843)) (tN (tL 510016629031411) tE))) (tN (tN (tN (tL 562395837678067) (tL 557997791166963)) (tN (tL 509203204588019) tE)) (tN (tN (tL 561270084387315) tE) tE)))))) (tN (tN (tN (tN (tN (tN tE (tN tE (tL 496738737584240))) (tN (tN tE (tL 547505116788848)) (tN (tL 510018642245747) (tL 494522400241776)))) (tN (tN (tN tE (tL 557963496390256)) (tN (tL 509204880162416) (tL 495907661414000))) (tN (tN (tL 561270419881587) (tL 554638990376560)) (tN (tL 508079397404275) (tL 492583155400304))))) (tN (tN (tN (tN tE (tL 558517542926448)) (tN (tL 510034341476464) (tL 496737122728048))) (tN (tN (tL 562932364556403) (tL 556300935051376)) (tN (tL 510016756856947) (tL 494520514852976)))) (tN (tN (tN (tL 562395898396272) (tL 557963492146800)) (tN (tL 509203265306224) (tL 495906046557808))) (tN (tN (tL 561270145105523) (tL 554638715600496)) (tN (tL 508077512015475) tE))))) (tN (tN (tN (tN (tN tE (tL 558551905323120)) (tN (tL 510035954747507) (tL 496773095737456))) (tN (tN (tL 562932570638451) (tL 556301141133424)) (tN (tL 510018573551731) (tL 494522331547760)))) (tN (tN (tN (tL 527211428040307) (tL 557997854543472)) (tN (tL 509204878577267) (tL 495942019567216))) (tN (tN (tL 561270418296435) (tL 554638988791408)) (tN (tL 508079395819123) tE)))) (tN (tN (tN (tN (tL 562949947590771) (tL 558551901079664)) (tN (tL 510034339891315) (tL 496771480881264))) (tN (tN (tL 562932295862387) (tL 556300866357360)) (tN (tL 510016688162931) tE))) (tN (tN (tN (tL 562395896811123) (tL 557997850300016)) (tN (tL 509203263721075) tE)) (tN (tN (tL 561270143520371) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 558517530261616)) (tN (tL 510035939424368) (tL 496738720675952))) (tN (tN (tL 562932622424179) (tL 556301192919152)) (tN (tL 510018625337459) (tL 494522383333488)))) (tN (tN (tN (tL 527211480021104) (tL 557963445926000)) (tN (tL 509204829698160) (tL 495907610949744))) (tN (tN (tL 561270369417331) (tL 554638939912304)) (tN (tL 508079346940019) tE)))) (tN (tN (tN (tN (tL 562949923813488) (tL 558517517564016)) (tN (tL 510034316114032) (tL 496737097365616))) (tN (tN (tL 562932339193971) (tL 556300909688944)) (tN (tL 510016731494515) tE))) (tN (tN (tN (tL 562395839477872) (tL 557963433228400)) (tN (tL 509203206387824) tE)) (tN (tN (tL 561270086187123) tE) tE)))) (tN (tN (tN (tN (tN (tL 527765461844083) (tL 558551854596208)) (tN (tL 510035904020595) (tL 496773045010544))) (tN (tN (tL 562932519911539) (tL 556301090406512)) (tN (tL 510018522824819) tE))) (tN (tN (tN (tL 527211411062899) (tL 557997803815024)) (tN (tL 509204827848819) tE)) (tN (tN (tL 561270367567987) tE) tE))) (tN (tN (tN (tN (tL 562949888409715) (tL 558551841898608)) (tN (tL 510034280710259) tE)) (tN (tN (tL 562932236681331) tE) tE)) (tN (tN (tN (tL 562395837628531) tE) tE) tE))))))
private def c1Tree1_11 : Tree10 := (tN (tN (tN (tN (tN (tN (tN tE (tN tE (tL 3917010170243))) (tN (tN tE (tL 63719866364291)) (tN (tL 298912275493315) (tL 1941056778627)))) (tN (tN (tN tE (tL 64308545322883)) (tN (tL 296990546067395) (tL 2252710346627))) (tN (tN (tL 350164120240067) (tL 62057714024323)) (tN (tL 296973097762755) (tL 1879048067))))) (tN (tN (tN (tN tE (tL 65970685079939)) (tN (tL 298928100602307) (tL 4190264881539))) (tN (tN (tL 351826257899971) (tL 63719851684227)) (tN (tL 298910650200515) (tL 1939431485827)))) (tN (tN (tN (tL 351289657524163) (tL 65416634302339)) (tN (tL 298097024434115) (tL 3359188713347))) (tN (tN (tL 350164105560003) (tL 62057699344259)) (tN (tL 296971472469955) tE))))) (tN (tN (tN (tN (tN tE (tL 65970696077699)) (tN (tL 298929722212803) (tL 4191886492035))) (tN (tN (tL 351826338103747) (tL 63719931888003)) (tN (tL 298912341017027) (tL 1941122302339)))) (tN (tN (tN (tL 316105195505539) (tL 65416645300099)) (tN (tL 298098646044611) (tL 3360810323843))) (tN (tN (tL 350164185763779) (tL 62057779548035)) (tN (tL 296973163286467) tE)))) (tN (tN (tN (tN (tL 351843715105219) (tL 65970691883395)) (tN (tL 298928107405763) (tL 4190271684995))) (tN (tN (tL 351826063376835) (tL 63719657161091)) (tN (tL 298910455677379) tE))) (tN (tN (tN (tL 351289664327619) (tL 65416641105795)) (tN (tL 298097031237571) tE)) (tN (tN (tL 350163911036867) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 65970646937987)) (tN (tL 298929673073091) (tL 4191837352323))) (tN (tN (tL 351826490290627) (tL 63720084074883)) (tN (tL 298912493203907) (tL 1941274489219)))) (tN (tN (tN (tL 316105247224195) (tL 65416596156803)) (tN (tL 298098596901315) (tL 3360761180547))) (tN (tN (tL 350164337947075) (tL 62057931731331)) (tN (tL 296973315469763) tE)))) (tN (tN (tN (tN (tL 351843657511363) (tL 65970634289539)) (tN (tL 298928049811907) (tL 4190214091139))) (tN (tN (tL 351826207109571) (tL 63719800893827)) (tN (tL 298910599410115) tE))) (tN (tN (tN (tL 351289606730179) (tL 65416583508355)) (tN (tL 298096973640131) tE)) (tN (tN (tL 350164054766019) tE) tE)))) (tN (tN (tN (tN (tN (tL 316659229311363) (tL 65970645352835)) (tN (tL 298929671487939) (tL 4191835767171))) (tN (tN (tL 351826287378883) (tL 63719881163139)) (tN (tL 298912290292163) tE))) (tN (tN (tN (tL 316105178530179) (tL 65416594571651)) (tN (tL 298098595316163) tE)) (tN (tN (tL 350164135035331) tE) tE))) (tN (tN (tN (tN (tL 351843655926211) (tL 65970632704387)) (tN (tL 298928048226755) tE)) (tN (tN (tL 351826004197827) tE) tE)) (tN (tN (tN (tL 351289605145027) tE) tE) tE))))) (tN (tN (tN (tN (tN (tN (tN tE (tL 4398046494720)) (tN (tL 298929723799619) (tL 4191888078848))) (tN (tN (tL 351826541017155) (tL 63720134801408)) (tN (tL 298912543930435) (tL 1941325215744)))) (tN (tN (tN (tL 315828272619011) (tL 65416646884864)) (tN (tL 298098647629379) (tL 3360811908608))) (tN (tN (tL 350164388675139) (tL 62057982459392)) (tN (tL 296973366197827) tE)))) (tN (tN (tN (tN (tL 351843716642883) (tL 65970693421056)) (tN (tL 298928108943427) (tL 4190273222656))) (tN (tN (tL 351826266241091) (tL 63719860025344)) (tN (tL 298910658541635) tE))) (tN (tN (tN (tL 351289665863235) (tL 65416642641408)) (tN (tL 298097032773187) tE)) (tN (tN (tL 350164113899075) tE) tE)))) (tN (tN (tN (tN (tN (tL 316659246284803) (tL 65970696077312)) (tN (tL 298929722212419) (tL 4191886491648))) (tN (tN (tL 351826338103363) (tL 63719931887616)) (tN (tL 298912341016643) tE))) (tN (tN (tN (tL 316105195505155) (tL 65416645299712)) (tN (tL 298098646044227) tE)) (tN (tN (tL 350164185763395) tE) tE))) (tN (tN (tN (tN (tL 351843715055683) (tL 65970691833856)) (tN (tL 298928107356227) tE)) (tN (tN (tL 351826063327299) tE) tE)) (tN (tN (tN (tL 351289664278083) tE) tE) tE)))) (tN (tN (tN (tN (tN (tN (tL 316659331809283) (tL 65970680756224)) (tN (tL 298929706891331) (tL 4191871170560))) (tN (tN (tL 351826524108867) (tL 63720117893120)) (tN (tL 298912527022147) tE))) (tN (tN (tN (tL 316105281042435) (tL 65416629975040)) (tN (tL 298098630719555) tE)) (tN (tN (tL 350164371765315) tE) tE))) (tN (tN (tN (tN (tL 351843691280451) (tL 65970668058624)) (tN (tL 298928083580995) tE)) (tN (tN (tL 351826240878659) tE) tE)) (tN (tN (tN (tL 351289640499267) tE) tE) tE))) (tN (tN (tN (tN (tN (tL 316659229310979) (tL 65970645352448)) (tN (tL 298929671487555) tE)) (tN (tN (tL 351826287378499) tE) tE)) (tN (tN (tN (tL 316105178529795) tE) tE) tE)) (tN (tN (tN (tN (tL 351843655876675) tE) tE) tE) tE)))))
private def c1Tree1 : Tree10 :=
  tN (tN c1Tree1_00 c1Tree1_01) (tN c1Tree1_10 c1Tree1_11)
private def c1Tree2_00 : Tree10 := (tN (tN (tN (tN (tN tE (tN tE (tN tE (tN tE (tL 263884466290687))))) (tN (tN tE (tN tE (tN tE (tL 248229901893631)))) (tN (tN tE (tN tE (tL 265008596385791))) (tN (tN tE (tL 273163730550783)) (tN (tL 560785342332927) (tL 263882843095039)))))) (tN (tN (tN tE (tN tE (tN tE (tL 529706433105919)))) (tN (tN tE (tN tE (tL 547610476138495))) (tN (tN tE (tL 554638718259199)) (tN (tL 560855683420159) (tL 545359441416191))))) (tN (tN (tN tE (tN tE (tL 531955844632575))) (tN (tN tE (tL 556299247407103)) (tN (tL 545201051914239) (tL 529704809910271)))) (tN (tN (tN tE (tL 557997841960959)) (tN (tL 561979813515263) (tL 548716954505215))) (tN (tN (tL 559068914094079) (tL 554638705676287)) (tN (tL 560854060224511) (tL 545357818220543))))))) (tN (tN (tN (tN tE (tN tE (tN tE (tL 265823930941439)))) (tN (tN tE (tN tE (tL 265010168856575))) (tN (tN tE (tL 273163962941439)) (tN (tL 560787185336319) (tL 263884686098431))))) (tN (tN (tN tE (tN tE (tL 265839621767167))) (tN (tN tE (tL 274825899212799)) (tN (tL 562724536385535) (tL 265822037147647)))) (tN (tN (tN tE (tL 274289433051135)) (tN (tL 561911044800511) (tL 265008545595391))) (tN (tN (tL 560993060585471) (tL 273163679760383)) (tN (tL 560785291542527) (tL 263882792304639)))))) (tN (tN (tN (tN tE (tN tE (tL 549549603147775))) (tN (tN tE (tL 556301090410495)) (tN (tL 562795080962047) (tL 547298838958079)))) (tN (tN (tN tE (tL 557997803819007)) (tN (tL 561981385986047) (tL 548718526975999))) (tN (tN (tL 561270367571967) (tL 554638938066943)) (tN (tL 560855903227903) (tL 545359661223935))))) (tN (tN (tN (tN tE (tL 558551842017279)) (tN (tL 562810838962175) (tL 549547979952127))) (tN (tN (tL 562932236799999) (tL 556300807294975)) (tN (tL 562793187233791) (tL 547296945229823)))) (tN (tN (tN (tL 562395837747199) (tL 557997791236095)) (tN (tL 561979762790399) (tL 548716903780351))) (tN (tN (tL 561270084456447) (tL 554638654951423)) (tN (tL 560854009499647) tE))))))) (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 529706501799548)))) (tN (tN tE (tN tE (tL 547576117984892))) (tN (tN tE (tL 554638719843964)) (tN (tL 560855685004927) (tL 545359443000956))))) (tN (tN (tN tE (tN tE (tL 531921486364284))) (tN (tN tE (tL 556299315986044)) (tN (tL 545201120493183) (tL 529704878489212)))) (tN (tN (tN tE (tL 557963483692668)) (tN (tL 561979814985340) (tL 548682596236924))) (tN (tN (tL 561270136651391) (tL 554638707146364)) (tN (tL 560854061694591) (tL 545357819690620)))))) (tN (tN (tN (tN tE (tN tE (tL 496498217815676))) (tN (tN tE (tL 556300870553212)) (tN (tL 545202675093119) (tL 529706433089148)))) (tN (tN (tN tE (tL 556889752964732)) (tN (tL 560873335131775) (tL 547610476121724))) (tN (tN (tL 561270147747455) (tL 554638718242428)) (tN (tL 560855683403391) (tL 545359441399420))))) (tN (tN (tN (tN tE (tL 558550282014332)) (tN (tL 545218701429881) (tL 531955844517500))) (tN (tN (tL 562930676797055) (tL 556299247292028)) (tN (tL 545201051799167) (tL 529704809795196)))) (tN (tN (tN (tL 562395888356991) (tL 557997841845884)) (tN (tL 561979813400191) (tL 548716954390140))) (tN (tN (tL 561270135066239) (tL 554638705561212)) (tN (tL 560854060109439) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 549515244994172))) (tN (tN tE (tL 556301159104124)) (tN (tL 562795149655679) (tL 547298907651708)))) (tN (tN (tN tE (tL 557963445665404)) (tN (tL 561981387570812) (tL 548684168822396))) (tN (tN (tL 561270369156735) (tL 554638939651708)) (tN (tL 560855904812671) (tL 545359662808700))))) (tN (tN (tN (tN tE (tL 558516676344956)) (tN (tL 562810840432252) (tL 549513621683836))) (tN (tN (tL 562932305378943) (tL 556300875873916)) (tN (tL 562793255812735) (tL 547297013808764)))) (tN (tN (tN (tL 562395839217276) (tL 557963432967804)) (tN (tL 561979764260476) (tL 548682545512060))) (tN (tN (tL 561270085926527) (tL 554638656421500)) (tN (tL 560854010969727) tE))))) (tN (tN (tN (tN (tN tE (tL 558551854599804)) (tN (tL 562812462157439) (tL 549549603147388))) (tN (tN (tL 562932519915135) (tL 556301090410108)) (tN (tL 562795080961663) (tL 547298838957692)))) (tN (tN (tN (tL 562395850329727) (tL 557997803818620)) (tN (tL 561981385985663) (tL 548718526975612))) (tN (tN (tL 561270367571583) (tL 554638938066556)) (tN (tL 560855903227519) tE)))) (tN (tN (tN (tN (tL 562949684985983) (tL 558551841902204)) (tN (tL 562810838847103) (tL 549547979837052))) (tN (tN (tL 562932236684927) (tL 556300807179900)) (tN (tL 562793187118719) tE))) (tN (tN (tN (tL 562395837632127) (tL 557997791121020)) (tN (tL 561979762675327) tE)) (tN (tN (tL 561270084341375) tE) tE)))))))
private def c1Tree2_01 : Tree10 := (tN (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 37125428871055)))) (tN (tN tE (tN tE (tL 55029268479887))) (tN (tN tE (tL 62057714024335)) (tN (tL 349749655896015) (tL 52778437181327))))) (tN (tN (tN tE (tN tE (tL 39374636973967))) (tN (tN tE (tL 63718241075087)) (tN (tL 334095022292943) (tL 37123803578255)))) (tN (tN (tN tE (tL 65416634302351)) (tN (tL 350873582567375) (tL 56135746846607))) (tN (tN (tL 347962934820815) (tL 62057699344271)) (tN (tL 349748030603215) (tL 52776811888527)))))) (tN (tN (tN (tN tE (tN tE (tL 74285752766367))) (tN (tN tE (tL 134088405536670)) (tN (tL 404465186754527) (tL 107493968039839)))) (tN (tN (tN tE (tL 134677287915423)) (tN (tL 420135846793183) (tL 125398011072415))) (tN (tN (tL 418331488653279) (tL 132426253193119)) (tN (tL 420118195064799) (tL 123146976350111))))) (tN (tN (tN (tN tE (tL 136337817063327)) (tN (tL 404481215287263) (tL 109743379566495))) (tN (tN (tL 418886063722463) (tL 134086782341023)) (tN (tL 404463563558879) (tL 107492344844191)))) (tN (tN (tN (tL 421656116301791) (tL 135785376894879)) (tN (tL 421242325159903) (tL 126504489439135))) (tN (tN (tL 418331476070367) (tL 132426240610207)) (tN (tL 420116571869151) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 56968395489167))) (tN (tN tE (tL 63720084078479)) (tN (tL 351689051340751) (tL 54717832626063)))) (tN (tN (tN tE (tL 65416596160399)) (tN (tL 350875155038159) (tL 56137319317391))) (tN (tN (tL 350164337950671) (tL 62057931734927)) (tN (tL 349749873606607) (tL 52778654891919))))) (tN (tN (tN (tN tE (tL 65970634293135)) (tN (tL 351704607948751) (tL 56966772227983))) (tN (tN (tL 351826207113167) (tL 63719800897423)) (tN (tL 351687157546959) (tL 54715938832271)))) (tN (tN (tN (tL 351289606733775) (tL 65416583511951)) (tN (tL 350873531776975) (tL 56135696056207))) (tN (tN (tL 350164054769615) (tL 62057648553871)) (tN (tL 349747979812815) tE))))) (tN (tN (tN (tN (tN tE (tL 136339389534111)) (tN (tL 422074973802463) (tL 127337138081695))) (tN (tN (tL 422195031560159) (tL 134088625344415)) (tN (tL 422057592606687) (tL 125086373891999)))) (tN (tN (tN (tL 421658361974751) (tL 135785338752927)) (tN (tL 421243897630687) (tL 126506061909919))) (tN (tN (tL 420532879216607) (tL 132426473000863)) (tN (tL 420118414872543) tE)))) (tN (tN (tN (tN (tL 422212400173023) (tL 136339376951199)) (tN (tL 422073350606815) (tL 127335514886047))) (tN (tN (tL 422194748444639) (tL 134088342228895)) (tN (tL 422055698878431) tE))) (tN (tN (tN (tL 421658349391839) (tL 135785326170015)) (tN (tL 421242274435039) tE)) (tN (tN (tL 420532596101087) tE) tE)))))) (tN (tN (tN (tN (tN (tN tE (tN tE (tL 74285754351132))) (tN (tN tE (tL 134088610496028)) (tN (tL 404465391763039) (tL 107494173048348)))) (tN (tN (tN tE (tL 134677289500188)) (tN (tL 420135848377951) (tL 125398012657180))) (tN (tN (tL 420532864417375) (tL 132426458201628)) (tN (tL 420118400073311) (tL 123147181358620))))) (tN (tN (tN (tN tE (tL 136337818533404)) (tN (tL 404481216757343) (tL 109743381036572))) (tN (tN (tL 422193391353439) (tL 134086985137692)) (tN (tL 404463766355551) (tL 107492547640860)))) (tN (tN (tN (tL 421658401586783) (tL 135785378364956)) (tN (tL 421242326629983) (tL 126504490909212))) (tN (tN (tL 420532849622623) (tL 132426443406876)) (tN (tL 420116774665823) tE))))) (tN (tN (tN (tN (tN tE (tL 127543347187228)) (tN (tL 369023588470367) (tL 74285752749596))) (tN (tN (tL 422194811702879) (tL 134088405487132)) (tN (tL 404465186737759) (tL 107493968023068)))) (tN (tN (tN (tL 420550311120479) (tL 134677287898652)) (tN (tL 420135846776415) (tL 125398011055644))) (tN (tN (tL 420532659392095) (tL 132426253176348)) (tN (tL 420118195048031) tE)))) (tN (tN (tN (tN (tL 422210840170079) (tL 136337816948252)) (tN (tL 404481215172191) (tL 109743379451420))) (tN (tN (tL 422193188441695) (tL 134086782225948)) (tN (tL 404463563443807) tE))) (tN (tN (tN (tL 421658400001631) (tL 135785376779804)) (tN (tL 421242325044831) tE)) (tN (tN (tL 420532646710879) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 136339391118876)) (tN (tL 422074975387231) (tL 127337139666460))) (tN (tN (tL 422195234471519) (tL 134088828255772)) (tN (tL 422057795518047) (tL 125086576803356)))) (tN (tN (tN (tL 421658363492383) (tL 135785340337692)) (tN (tL 421243899215455) (tL 126506063494684))) (tN (tN (tL 420533082127967) (tL 132426675912220)) (tN (tL 420118617783903) tE)))) (tN (tN (tN (tN (tL 422212401643103) (tL 136339378421276)) (tN (tL 422073352076895) (tL 127335516356124))) (tN (tN (tL 422194951241311) (tL 134088545025564)) (tN (tL 422055901675103) tE))) (tN (tN (tN (tL 421658350861919) (tL 135785327640092)) (tN (tL 421242275905119) tE)) (tN (tN (tL 420532798897759) tE) tE)))) (tN (tN (tN (tN (tN (tL 422212412755551) (tL 136339389533724)) (tN (tL 422074973802079) (tL 127337138081308))) (tN (tN (tL 422195031559775) (tL 134088625344028)) (tN (tL 422057592606303) tE))) (tN (tN (tN (tL 421658361974367) (tL 135785338752540)) (tN (tL 421243897630303) tE)) (tN (tN (tL 420532879216223) tE) tE))) (tN (tN (tN (tN (tL 422212400057951) (tL 136339376836124)) (tN (tL 422073350491743) tE)) (tN (tN (tL 422194748329567) tE) tE)) (tN (tN (tN (tL 421658349276767) tE) tE) tE))))))
private def c1Tree2_10 : Tree10 := (tN (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 494522129709555)))) (tN (tN tE (tN tE (tL 494799559852019))) (tN (tN tE (tL 554638719844339)) (tN (tL 508079126872051) (tL 492582884868083))))) (tN (tN (tN tE (tN tE (tL 496737114388979))) (tN (tN tE (tL 556300926712307)) (tN (tL 510016748517875) (tL 494520506513907)))) (tN (tN (tN tE (tL 557963483807731)) (tN (tL 509203256868851) (tL 495906038218739))) (tN (tN (tL 561270136766451) (tL 554638707261427)) (tN (tL 508077503676403) (tL 492581261672435)))))) (tN (tN (tN (tN tE (tN tE (tL 496498217831415))) (tN (tN tE (tL 556300870601719)) (tN (tL 510018303020023) (tL 494522061016055)))) (tN (tN (tN tE (tL 556889752981495)) (tN (tL 508096777015287) (tL 494833918005239))) (tN (tN (tL 561270147764215) (tL 554638718259191)) (tN (tL 508079125286903) (tL 492582883282935))))) (tN (tN (tN (tN tE (tL 558551892741111)) (tN (tL 510034331552759) (tL 496771472542711))) (tN (tN (tL 562932287523831) (tL 556300858018807)) (tN (tL 510016679824375) (tL 494520437820407)))) (tN (tN (tN (tL 562395888472055) (tL 557997841960951)) (tN (tL 509203255382007) (tL 495940396371959))) (tN (tN (tL 561270135181303) (tL 554638705676279)) (tN (tL 508077502091255) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 496738686857715))) (tN (tN tE (tL 556301159100915)) (tN (tL 510018591519219) (tL 494522349515251)))) (tN (tN (tN tE (tL 557963445662195)) (tN (tL 509203755692531) (tL 495907610685939))) (tN (tN (tL 561270369153523) (tL 554638939648499)) (tN (tL 508079346676211) (tL 492583104672243))))) (tN (tN (tN (tN tE (tL 558517483794931)) (tN (tL 510034282312179) (tL 496737063596531))) (tN (tN (tL 562932305424883) (tL 556300875919859)) (tN (tL 510016697725427) (tL 494520455721459)))) (tN (tN (tN (tL 562395839230451) (tL 557963433013747)) (tN (tL 509203206140403) (tL 495905987424755))) (tN (tN (tL 561270085972467) (tL 554638656467443)) (tN (tL 508077452882419) tE))))) (tN (tN (tN (tN (tN tE (tL 558551854597111)) (tN (tL 510035904021495) (tL 496773045011447))) (tN (tN (tL 562932519912439) (tL 556301090407415)) (tN (tL 510018522825719) (tL 494522280821751)))) (tN (tN (tN (tL 562395850327031) (tL 557997803815927)) (tN (tL 509204827849719) (tL 495941968839671))) (tN (tN (tL 561270367568887) (tL 554638938063863)) (tN (tL 508079345091575) tE)))) (tN (tN (tN (tN (tL 562949888525303) (tL 558551842014199)) (tN (tL 510034280825847) (tL 496771421815799))) (tN (tN (tL 562932236796919) (tL 556300807291895)) (tN (tL 510016629097463) tE))) (tN (tN (tN (tL 562395837744119) (tL 557997791233015)) (tN (tL 509203204654071) tE)) (tN (tN (tL 561270084453367) tE) tE)))))) (tN (tN (tN (tN (tN (tN tE (tN tE (tL 496463859677296))) (tN (tN tE (tL 556300939294832)) (tN (tL 510018371713139) (tL 494522129709168)))) (tN (tN (tN tE (tL 556855394827376)) (tN (tL 508096778599536) (tL 494799559851120))) (tN (tN (tL 561270149348467) (tL 554638719843440)) (tN (tL 508079126871155) (tL 492582884867184))))) (tN (tN (tN (tN tE (tL 558517534472304)) (tN (tL 510034333022320) (tL 496737114273904))) (tN (tN (tL 562932356102259) (tL 556300926597232)) (tN (tL 510016748402803) (tL 494520506398832)))) (tN (tN (tN (tL 562395889941616) (tL 557963483692144)) (tN (tL 509203256851568) (tL 495906038103152))) (tN (tN (tL 561270136650867) (tL 554638707145840)) (tN (tL 508077503560819) tE))))) (tN (tN (tN (tN (tN tE (tL 549755812284528)) (tN (tL 509761076824179) (tL 496498217814128))) (tN (tN (tL 562932300089459) (tL 556300870584432)) (tN (tL 510018303002739) (tL 494522060998768)))) (tN (tN (tN (tL 561287799475315) (tL 556889752964208)) (tN (tL 508096776998003) (tL 494833917987952))) (tN (tN (tL 561270147746931) (tL 554638718241904)) (tN (tL 508079125269619) tE)))) (tN (tN (tN (tN (tL 562949939136627) (tL 558551892625520)) (tN (tL 510034331437171) (tL 496771472427120))) (tN (tN (tL 562932287408243) (tL 556300857903216)) (tN (tL 510016679708787) tE))) (tN (tN (tN (tL 562395888356467) (tL 557997841845360)) (tN (tL 509203255266419) tE)) (tN (tN (tL 561270135065715) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 558517496442992)) (tN (tL 510035905605744) (tL 496738686857328))) (tN (tN (tL 562932588605555) (tL 556301159100528)) (tN (tL 510018591518835) (tL 494522349514864)))) (tN (tN (tN (tL 456842735579232) (tL 557963445661808)) (tN (tL 509204829433968) (tL 495907610685552))) (tN (tN (tL 561270369153139) (tL 554638939648112)) (tN (tL 508079346675827) tE)))) (tN (tN (tN (tN (tL 562949889994864) (tL 558517483745392)) (tN (tL 510034282295408) (tL 496737063546992))) (tN (tN (tL 562932305375347) (tL 556300875870320)) (tN (tL 510016697675891) tE))) (tN (tN (tN (tL 562395839213680) (tL 557963432964208)) (tN (tL 509203206123632) tE)) (tN (tN (tL 561270085922931) tE) tE)))) (tN (tN (tN (tN (tN (tL 562949901107315) (tL 558551854596208)) (tN (tL 510035904020595) (tL 496773045010544))) (tN (tN (tL 562932519911539) (tL 556301090406512)) (tN (tL 510018522824819) tE))) (tN (tN (tN (tL 562395850326131) (tL 557997803815024)) (tN (tL 509204827848819) tE)) (tN (tN (tL 561270367567987) tE) tE))) (tN (tN (tN (tN (tL 562949888409715) (tL 558551841898608)) (tN (tL 510034280710259) tE)) (tN (tN (tL 562932236681331) tE) tE)) (tN (tN (tN (tL 562395837628531) tE) tE) tE))))))
private def c1Tree2_11 : Tree10 := (tN (tN (tN (tN (tN (tN (tN tE (tN tE (tL 3917010170243))) (tN (tN tE (tL 63719866364291)) (tN (tL 298912275493315) (tL 1941056778627)))) (tN (tN (tN tE (tL 64308545322883)) (tN (tL 296990546067395) (tL 2252710346627))) (tN (tN (tL 350164120240067) (tL 62057714024323)) (tN (tL 296973097762755) (tL 1879048067))))) (tN (tN (tN (tN tE (tL 65970685079939)) (tN (tL 298928100602307) (tL 4190264881539))) (tN (tN (tL 351826257899971) (tL 63719851684227)) (tN (tL 298910650200515) (tL 1939431485827)))) (tN (tN (tN (tL 351289657524163) (tL 65416634302339)) (tN (tL 298097024434115) (tL 3359188713347))) (tN (tN (tL 350164105560003) (tL 62057699344259)) (tN (tL 296971472469955) tE))))) (tN (tN (tN (tN (tN tE (tL 57174603056007)) (tN (tL 298654844306375) (tL 3917008585607))) (tN (tN (tL 351826067571655) (tL 63719661355911)) (tN (tL 298912070484935) (tL 1940851770247)))) (tN (tN (tN (tL 350181566959559) (tL 64308543737735)) (tN (tL 296990544482247) (tL 2252708761479))) (tN (tN (tL 350163915231175) (tL 62057509015431)) (tN (tL 296972892753863) tE)))) (tN (tN (tN (tN (tL 351843706717127) (tL 65970683495303)) (tN (tL 298928099017671) (tL 4190263296903))) (tN (tN (tL 351826054988743) (tL 63719648772999)) (tN (tL 298910447289287) tE))) (tN (tN (tN (tL 351289655939015) (tL 65416632717191)) (tN (tL 298097022848967) tE)) (tN (tN (tL 350163902648263) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 65970646937987)) (tN (tL 298929673073091) (tL 4191837352323))) (tN (tN (tL 351826490290627) (tL 63720084074883)) (tN (tL 298912493203907) (tL 1941274489219)))) (tN (tN (tN (tL 316105247224195) (tL 65416596156803)) (tN (tL 298098596901315) (tL 3360761180547))) (tN (tN (tL 350164337947075) (tL 62057931731331)) (tN (tL 296973315469763) tE)))) (tN (tN (tN (tN (tL 351843657511363) (tL 65970634289539)) (tN (tL 298928049811907) (tL 4190214091139))) (tN (tN (tL 351826207109571) (tL 63719800893827)) (tN (tL 298910599410115) tE))) (tN (tN (tN (tL 351289606730179) (tL 65416583508355)) (tN (tL 298096973640131) tE)) (tN (tN (tL 350164054766019) tE) tE)))) (tN (tN (tN (tN (tN (tL 351843668575175) (tL 65970645353351)) (tN (tL 298929671488455) (tL 4191835767687))) (tN (tN (tL 351826287379399) (tL 63719881163655)) (tN (tL 298912290292679) tE))) (tN (tN (tN (tL 351289617793991) (tL 65416594572167)) (tN (tL 298098595316679) tE)) (tN (tN (tL 350164135035847) tE) tE))) (tN (tN (tN (tN (tL 351843655992263) (tL 65970632770439)) (tN (tL 298928048292807) tE)) (tN (tN (tL 351826004263879) tE) tE)) (tN (tN (tN (tL 351289605211079) tE) tE) tE))))) (tN (tN (tN (tN (tN (tN (tN tE (tL 57174604640256)) (tN (tL 298654845890627) (tL 3917010169856))) (tN (tN (tL 351826272579651) (tL 63719866363904)) (tN (tL 298912275492931) (tL 1941056778240)))) (tN (tN (tN (tL 314997196454915) (tL 64308545321984)) (tN (tL 296990546066499) (tL 2252710345728))) (tN (tN (tL 350164120239171) (tL 62057714023424)) (tN (tL 296973097761859) tE)))) (tN (tN (tN (tN (tL 351843708186691) (tL 65970684964864)) (tN (tL 298928100487235) (tL 4190264766464))) (tN (tN (tL 351826257784899) (tL 63719851569152)) (tN (tL 298910650085443) tE))) (tN (tN (tN (tL 351289657408579) (tL 65416634186752)) (tN (tL 298097024318531) tE)) (tN (tN (tL 350164105444419) tE) tE)))) (tN (tN (tN (tN (tN (tL 70368742572035) (tL 57174603038720)) (tN (tL 298654844289091) (tL 3917008568320))) (tN (tN (tL 351826067554371) (tL 63719661338624)) (tN (tL 298912070467651) tE))) (tN (tN (tN (tL 350181566942275) (tL 64308543720448)) (tN (tL 296990544464963) tE)) (tN (tN (tL 350163915213891) tE) tE))) (tN (tN (tN (tN (tL 351843706601539) (tL 65970683379712)) (tN (tL 298928098902083) tE)) (tN (tN (tL 351826054873155) tE) tE)) (tN (tN (tN (tL 351289655823427) tE) tE) tE)))) (tN (tN (tN (tN (tN (tN (tL 316659297992707) (tL 65970646937600)) (tN (tL 298929673072707) (tL 4191837351936))) (tN (tN (tL 351826490290243) (tL 63720084074496)) (tN (tL 298912493203523) tE))) (tN (tN (tN (tL 316105247223811) (tL 65416596156416)) (tN (tL 298098596900931) tE)) (tN (tN (tL 350164337946691) tE) tE))) (tN (tN (tN (tN (tL 351843657461827) (tL 65970634240000)) (tN (tL 298928049762371) tE)) (tN (tN (tL 351826207060035) tE) tE)) (tN (tN (tN (tL 351289606680643) tE) tE) tE))) (tN (tN (tN (tN (tN (tL 351843668574275) (tL 65970645352448)) (tN (tL 298929671487555) tE)) (tN (tN (tL 351826287378499) tE) tE)) (tN (tN (tN (tL 351289617793091) tE) tE) tE)) (tN (tN (tN (tN (tL 351843655876675) tE) tE) tE) tE)))))
private def c1Tree2 : Tree10 :=
  tN (tN c1Tree2_00 c1Tree2_01) (tN c1Tree2_10 c1Tree2_11)

private def c2Tree0_00 : Tree10 := (tN (tN (tN (tN (tN tE (tN tE (tN tE (tN tE (tL 70368612057088))))) (tN (tN tE (tN tE (tN tE (tL 70351040118784)))) (tN (tN tE (tN tE (tL 66505301557248))) (tN (tN tE (tL 298654726455296)) (tN (tL 17763724754944) (tL 70368624738304)))))) (tN (tN (tN tE (tN tE (tN tE (tL 70350559260675)))) (tN (tN tE (tN tE (tL 66486365876353))) (tN (tN tE (tL 298651024388289)) (tN (tL 54872438763648) (tL 70368680767617))))) (tN (tN (tN tE (tN tE (tL 66487718539395))) (tN (tN tE (tL 298637210546371)) (tN (tL 54854866825344) (tL 70351108829315)))) (tN (tN (tN tE (tL 13316428165249)) (tN (tL 53208084410496) (tL 66505303158913))) (tN (tN (tL 1683576451200) (tL 298654795165889)) (tN (tL 54872451444864) (tL 70368693448833))))))) (tN (tN (tN (tN tE (tN tE (tN tE (tL 70350541291520)))) (tN (tN tE (tN tE (tL 66507554816000))) (tN (tN tE (tL 298651074035712)) (tN (tL 54872488411136) (tL 70368730415104))))) (tN (tN (tN tE (tN tE (tL 66489915244544))) (tN (tN tE (tL 298637192560640)) (tN (tL 2077753835520) (tL 70351090843648)))) (tN (tN (tN tE (tL 13316544495616)) (tN (tL 53210348224512) (tL 66507566972928))) (tN (tN (tL 1683625574400) (tL 298654844289024)) (tN (tL 54872500568064) (tL 70368742572032)))))) (tN (tN (tN (tN tE (tN tE (tL 66489367277571))) (tN (tN tE (tL 298633490477123)) (tN (tL 54854367981568) (tL 70350609985539)))) (tN (tN (tN tE (tL 13314922803329)) (tN (tL 53210337144960) (tL 66507555893377))) (tN (tN (tL 1679856398464) (tL 298651075113153)) (tN (tL 54872489488512) (tL 70368731492481))))) (tN (tN (tN (tN tE (tL 13298894368771)) (tN (tL 53192698097664) (tL 66489916846083))) (tN (tN (tL 8185171968) (tL 298637261271107)) (tN (tL 54854917550080) (tL 70351159554051)))) (tN (tN (tN (tL 2147475456) (tL 13316546097152)) (tN (tL 53210349826048) (tL 31323196473344))) (tN (tN (tL 1683627175936) (tL 298654845890624)) (tN (tL 54872502169600) tE))))))) (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 70350490567043)))) (tN (tN tE (tN tE (tL 66503678378887))) (tN (tN tE (tL 298650955694983)) (tN (tL 54872370168711) (tL 70368612074375))))) (tN (tN (tN tE (tN tE (tL 31268985209735))) (tN (tN tE (tL 298633920611207)) (tN (tL 19669884928903) (tL 35166668030855)))) (tN (tN (tN tE (tL 13315218719619)) (tN (tL 53208082924420) (tL 31320795366279))) (tN (tN (tL 1683507757959) (tL 298651505247111)) (tN (tL 54872382751623) (tL 35184252666759)))))) (tN (tN (tN (tN tE (tN tE (tL 66486095376771))) (tN (tN tE (tL 298633439801795)) (tN (tL 54854317306243) (tL 70350559310211)))) (tN (tN (tN tE (tL 13246085481347)) (tN (tL 53206461313927) (tL 66503679964039))) (tN (tN (tL 1679805772679) (tL 298651024389063)) (tN (tL 54872438862727) (tL 70368680768391))))) (tN (tN (tN (tN tE (tL 13264483906435)) (tN (tL 53190499890052) (tL 66453358900103))) (tN (tN (tL 1665991832455) (tL 298637210547143)) (tN (tL 54854866826119) (tL 70351108830087)))) (tN (tN (tN (tL 19208987520) (tL 13315354510211)) (tN (tL 431526372224) (tL 13453866681219))) (tN (tN (tL 1683576451975) (tL 298651573941191)) (tN (tL 2095893308291) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 66489365693319))) (tN (tN tE (tL 298633421783943)) (tN (tL 54854299288455) (tL 70350541292423)))) (tN (tN (tN tE (tL 13314921743239)) (tN (tL 53210336183175) (tL 66507554833287))) (tN (tN (tL 1679855436679) (tL 298651074052999)) (tN (tL 54872488526727) (tL 70368730432391))))) (tN (tN (tN (tN tE (tL 13297819026311)) (tN (tL 18007787537287) (tL 31305543156615))) (tN (tN (tL 1662215750535) (tL 298633971336071)) (tN (tL 19669939880839) (tL 35166718755719)))) (tN (tN (tN (tL 19325747974) (tL 13315470771079)) (tN (tL 53210348241799) (tL 31323194901383))) (tN (tN (tL 1683625591687) (tL 298651623080839)) (tN (tL 54872500585351) tE))))) (tN (tN (tN (tN (tN tE (tL 13297271173507)) (tN (tL 53192148644227) (tL 66489367392643))) (tN (tN (tL 1662271877507) (tL 298633490592195)) (tN (tL 54854368096643) (tL 67052075151747)))) (tN (tN (tN (tL 17687372678) (tL 13314922804103)) (tN (tL 53210337244039) (tL 66507555894151))) (tN (tN (tL 1679856497543) (tL 298651075113927)) (tN (tL 54872489587591) tE)))) (tN (tN (tN (tN (tL 1134551426) (tL 13298894369155)) (tN (tL 53192698098051) (tL 66489916846467))) (tN (tN (tL 1666042556803) (tL 298637261271491)) (tN (tL 53755405922688) tE))) (tN (tN (tN (tL 2147475842) (tL 13315472351619)) (tN (tL 433791689091) tE)) (tN (tN (tL 1683627176323) tE) tE)))))))
private def c2Tree0_01 : Tree10 := (tN (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 562923109875809)))) (tN (tN tE (tN tE (tL 561283910860899))) (tN (tN tE (tL 509757188210803)) (tN (tL 549755681767536) (tL 562949821300835))))) (tN (tN (tN tE (tN tE (tL 559068926181475))) (tN (tN tE (tL 509743374368883)) (tN (tL 547436007358576) (tL 562932249362531)))) (tN (tN (tN tE (tL 437727914885219)) (tN (tL 548091394523248) (tL 561285534056547))) (tN (tN (tL 496498099978352) (tL 509760958988403)) (tN (tL 549755694448752) (tL 562949833982051)))))) (tN (tN (tN (tN tE (tN tE (tL 559067304570979))) (tN (tN tE (tL 509739672285299)) (tN (tL 547435526500464) (tL 562931768504419)))) (tN (tN (tN tE (tL 296920085459169)) (tN (tL 547986693714160) (tL 561283912462561))) (tN (tN (tL 496460038172912) (tL 509757256921329)) (tN (tL 549652671262960) (tL 562949890011361))))) (tN (tN (tN (tN tE (tL 435511308611811)) (tN (tL 545771709034736) (tL 559068927783139))) (tN (tN (tL 493139098984560) (tL 509743443079411)) (tN (tL 547436076069104) (tL 562932318073059)))) (tN (tN (tN (tL 424430697738464) (tL 437727916486881)) (tN (tL 547988316909808) (tL 561285535658209))) (tN (tN (tL 496463808950512) (tL 509761027698929)) (tN (tL 549652683944176) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 559070574936163))) (tN (tN tE (tL 509739654318195)) (tN (tL 547435508533360) (tL 562931750535267)))) (tN (tN (tN tE (tL 437726410051683)) (tN (tL 548093647788144) (tL 561287787319395))) (tN (tN (tL 496494447564912) (tL 509757306574963)) (tN (tL 549755800131696) (tL 562949939662947))))) (tN (tN (tN (tN tE (tL 435511357833315)) (tN (tL 545773905741936) (tL 559071124488291))) (tN (tN (tL 493139081300080) (tL 509743425095795)) (tN (tL 547436058085488) (tL 562932300087395)))) (tN (tN (tN (tL 424465173807200) (tL 437728032817251)) (tN (tL 548093659940976) (tL 561287799472227))) (tN (tN (tL 496498217814128) (tL 509761076824179)) (tN (tL 549755812284528) tE))))) (tN (tN (tN (tN (tN tE (tL 435509736124515)) (tN (tL 545773357774960) (tL 559070576521315))) (tN (tN (tL 493135379314800) (tL 509739723012211)) (tN (tL 547435577227376) (tL 562931819229283)))) (tN (tN (tN (tL 424429192376544) (tL 437726411124961)) (tN (tL 547990569646320) (tL 561287788392673))) (tN (tN (tL 496460088899824) (tL 509757307648241)) (tN (tL 549652721989872) tE)))) (tN (tN (tN (tN (tL 422214090354784) (tL 435511359434851)) (tN (tL 545773907343472) (tL 453518009774179))) (tN (tN (tL 493139150239856) (tL 509743493806195)) (tN (tL 547436126795888) tE))) (tN (tN (tN (tL 424430815670368) (tL 437728034418784)) (tN (tL 547990582327408) tE)) (tN (tN (tL 496463859677296) tE) tE)))))) (tN (tN (tN (tN (tN (tN tE (tN tE (tL 559067303035363))) (tN (tN tE (tL 509739603640819)) (tN (tL 547435457855987) (tL 562931699859939)))) (tN (tN (tN tE (tL 437657438110691)) (tN (tL 548089771443191) (tL 561283910976487))) (tN (tN (tL 496494329316343) (tL 509757188326391)) (tN (tL 549755681883127) (tL 562949821416423))))) (tN (tN (tN (tN tE (tL 435476947387363)) (tN (tL 545771707548660) (tL 559034566558695))) (tN (tN (tL 423878388122083) (tL 509743374386167)) (tN (tL 547436007375863) (tL 562932249379815)))) (tN (tN (tN (tL 424465055990752) (tL 437727780783075)) (tN (tL 548091394638836) (tL 561285399954407))) (tN (tN (tL 496498099995639) (tL 509760959005687)) (tN (tL 549755694466039) tE))))) (tN (tN (tN (tN (tN tE (tL 435406606234083)) (tN (tL 545770085872115) (tL 453239310447075))) (tN (tN (tL 494243430330867) (tL 509739672334835)) (tN (tL 547435526550003) (tL 562931768553955)))) (tN (tN (tN (tL 424429074641888) (tL 296920085459939)) (tN (tL 547986693813239) (tL 455455918289895))) (tN (tN (tL 496460038271991) (tL 509757256922103)) (tN (tL 549652671362039) tE)))) (tN (tN (tN (tN (tL 422214089962464) (tL 435406618883043)) (tN (tL 545771709133812) (tL 453206573970407))) (tN (tN (tL 494247201076215) (tL 509743443080183)) (tN (tL 547436076069879) tE))) (tN (tN (tN (tL 19209516000) (tL 13246098174947)) (tN (tL 70800270554096) tE)) (tN (tN (tL 496463808951287) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 435509734654951)) (tN (tL 545773356305399) (tL 559070575051751))) (tN (tN (tL 494243412429815) (tL 509739654433783)) (tN (tL 547435508648951) (tL 562931750650855)))) (tN (tN (tN (tL 424463551157223) (tL 437726410167271)) (tN (tL 548093647903735) (tL 561287787434983))) (tN (tN (tL 496494447680503) (tL 509757306690551)) (tN (tL 549755800247287) tE)))) (tN (tN (tN (tN (tL 422214139102183) (tL 435511357850599)) (tN (tL 545773905759223) (tL 559071124505575))) (tN (tN (tL 494247183109111) (tL 509743425113079)) (tN (tL 547436058102775) tE))) (tN (tN (tN (tL 424465173824487) (tL 437728032834535)) (tN (tL 548093659958263) tE)) (tN (tN (tL 496498217831415) tE) tE)))) (tN (tN (tN (tN (tN (tL 422212517491171) (tL 435440999789027)) (tN (tL 545773357890035) (tL 453242565489123))) (tN (tN (tL 494243481123315) (tL 509670986676723)) (tN (tL 547435577342451) tE))) (tN (tN (tN (tL 424429192475623) (tL 437657674740711)) (tN (tL 547990569745399) tE)) (tN (tN (tL 496460088998903) tE) tE))) (tN (tN (tN (tN (tL 422214140686819) (tL 435441029345763)) (tN (tL 545773907343859) tE)) (tN (tN (tL 494247251802611) tE) tE)) (tN (tN (tN (tL 19327349219) tE) tE) tE))))))
private def c2Tree0_10 : Tree10 := (tN (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 70350490568204)))) (tN (tN tE (tN tE (tL 66503678365212))) (tN (tN tE (tL 421796257992220)) (tN (tL 125241114234396) (tL 140737356238364))))) (tN (tN (tN tE (tN tE (tL 66487717006876))) (tN (tN tE (tL 421782444150300)) (tN (tL 125223005422108) (tL 140719784300060)))) (tN (tN (tN tE (tL 13316426665500)) (tN (tL 17748832882204) (tL 66505301626396))) (tN (tN (tL 124828810055196) (tL 421800028769820)) (tN (tL 125241126915612) (tL 140737368919580)))))) (tN (tN (tN (tN tE (tN tE (tL 66486095330847))) (tN (tN tE (tL 421778742066783)) (tN (tL 125223061437980) (tL 140719303441951)))) (tN (tN (tN tE (tL 13314804973213)) (tN (tL 53206461218460) (tL 66503679966877))) (tN (tN (tL 124825107988124) (tL 421796326702813)) (tN (tL 125241182944924) (tL 140737424948893))))) (tN (tN (tN (tN tE (tL 13298843647647)) (tN (tL 53190499860124) (tL 66487718608543))) (tN (tN (tL 124811294146204) (tL 421782512860895)) (tN (tL 125223611006620) (tL 140719853010591)))) (tN (tN (tN (tL 19209518232) (tL 13316428267165)) (tN (tL 53208084479644) (tL 66505303228061))) (tN (tN (tL 124828878765724) (tL 421800097480413)) (tN (tL 125241195626140) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 66488291954204))) (tN (tN tE (tL 369002165964316)) (tN (tL 124122458098716) (tL 140718211730972)))) (tN (tN (tN tE (tL 13314921729564)) (tN (tL 53208725458460) (tL 66505944206876))) (tN (tN (tL 72048599502364) (tL 369019818216988)) (tN (tL 125239621979676) (tL 140735863983644))))) (tN (tN (tN (tN tE (tL 13298892770844)) (tN (tL 53192126041628) (tL 66489915215388))) (tN (tN (tL 72030959930908) (tL 369005936741916)) (tN (tL 124123544489500) (tL 140719834992156)))) (tN (tN (tN (tL 19325750296) (tL 13316544499228)) (tN (tL 53210348195356) (tL 66507566943772))) (tN (tN (tL 72052369755676) (tL 369023588470300)) (tN (tL 125241244716572) tE))))) (tN (tN (tN (tN (tN tE (tL 13297271062047)) (tN (tL 53191074790940) (tL 66488293539359))) (tN (tN (tL 72031015943708) (tL 369002234658399)) (tN (tL 125222038421020) (tL 140718280424991)))) (tN (tN (tN (tL 17704058008) (tL 13314922806941)) (tN (tL 53208726535836) (tL 66503781023260))) (tN (tN (tL 72048600579740) (tL 369019819294429)) (tN (tL 125239623057052) tE)))) (tN (tN (tN (tN (tL 1675623448) (tL 13298894372383)) (tN (tL 53192698052124) (tL 66489916800543))) (tN (tN (tL 72034786737692) (tL 369006005452383)) (tN (tL 125223661682204) tE))) (tN (tN (tN (tL 19327351832) (tL 13316546100764)) (tN (tL 53210349780508) tE)) (tN (tN (tL 72052371357212) tE) tE)))))) (tN (tN (tN (tN (tN (tN tE (tN tE (tL 66486093744015))) (tN (tN tE (tL 351409929193359)) (tN (tL 54854248564623) (tL 67043365750671)))) (tN (tN (tN tE (tL 13314803388319)) (tN (tL 53206459731871) (tL 66503542048671))) (tN (tN (tL 124825039392671) (tL 421796258008991)) (tN (tL 125241114349471) (tL 140737219921823))))) (tN (tN (tN (tN tE (tL 13297768304543)) (tN (tL 53189961417628) (tL 66453357298591))) (tN (tN (tL 124807467339679) (tL 421779222925215)) (tN (tL 125223005422495) (tL 137412659479455)))) (tN (tN (tN (tL 19207917342) (tL 13315352940447)) (tN (tL 53208082927516) (tL 66487985472399))) (tN (tN (tL 124828810071967) (tL 421796807561119)) (tN (tL 125241126932383) tE))))) (tN (tN (tN (tN (tN tE (tL 13297220386703)) (tN (tL 53188876631951) (tL 66486094849935))) (tN (tN (tL 54438779223951) (tL 351409997938639)) (tN (tL 54854317309839) (tL 67043433965455)))) (tN (tN (tN (tL 17585799070) (tL 13314804973471)) (tN (tL 53206461317023) (tL 66503679436703))) (tN (tN (tL 124825108086687) (tL 421796326703071)) (tN (tL 125241183043487) tE)))) (tN (tN (tN (tN (tL 1624375198) (tL 13298843647903)) (tN (tL 53190499893148) (tL 66453358372767))) (tN (tN (tL 124811294146463) (tL 421782512861151)) (tN (tL 125223611006879) tE))) (tN (tN (tN (tL 19208988558) (tL 13315354519439)) (tN (tL 53208084506508) tE)) (tN (tN (tL 124828878765983) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 13297269477279)) (tN (tL 53191073206175) (tL 66486094139295))) (tN (tN (tL 72030947250079) (tL 369002165964703)) (tN (tL 125221969727391) (tL 137411086913439)))) (tN (tN (tN (tL 17703079710) (tL 13314921746335)) (tN (tL 53208725573535) (tL 66503610077087))) (tN (tN (tL 72048599617439) (tL 369019818233759)) (tN (tL 125239622094751) tE)))) (tN (tN (tN (tN (tL 63409950) (tL 13194202943391)) (tN (tL 53192126074780) (tL 66384101347231))) (tN (tN (tL 12948311966) (tL 296881087811487)) (tN (tL 53196454596380) tE))) (tN (tN (tN (tL 1944555294) (tL 13298089578399)) (tN (tL 53192967049116) tE)) (tN (tN (tL 34358153118) tE) tE)))) (tN (tN (tN (tN (tN (tL 35651470) (tL 13297271177103)) (tN (tL 53191074905999) (tL 66486095839119))) (tN (tN (tL 1662271881103) (tL 298633490595791)) (tN (tL 54853294358415) tE))) (tN (tN (tN (tL 17687379870) (tL 13314922807199)) (tN (tL 53208726634399) tE)) (tN (tN (tL 72048600678303) tE) tE))) (tN (tN (tN (tN (tL 1134559118) (tL 13195278286735)) (tN (tL 53192161230732) tE)) (tN (tN (tL 16238247822) tE) tE)) (tN (tN (tN (tL 1946150798) tE) tE) tE))))))
private def c2Tree0_11 : Tree10 := (tN (tN (tN (tN (tN (tN (tN tE (tN tE (tL 558792425079935))) (tN (tN tE (tL 562447442249343)) (tN (tL 265960481097276) (tL 562923109876863)))) (tN (tN (tN tE (tL 437726291692671)) (tN (tL 548089771331196) (tL 561283910863999))) (tN (tN (tL 549270887337596) (tL 562533746347647)) (tN (tL 549755681771132) (tL 562949821303935))))) (tN (tN (tN (tN tE (tL 435511307111551)) (tN (tL 545771707502204) (tL 559068926184575))) (tN (tN (tL 547023690501756) (tL 562519932505727)) (tN (tL 547436007362172) (tL 562932249365631)))) (tN (tN (tN (tL 424465055976568) (tL 437727914986623)) (tN (tL 548091394592380) (tL 561285399838847))) (tN (tN (tL 549274658115196) (tL 562537517125247)) (tN (tL 549755694452348) tE))))) (tN (tN (tN (tN (tN tE (tL 435509685402751)) (tN (tL 545770085826172) (tL 559067304574079))) (tN (tN (tL 547019988418172) (tL 562516230422143)) (tN (tL 547435526504060) (tL 562931768507519)))) (tN (tN (tN (tL 424429074545912) (tL 437726293294329)) (tN (tL 547986693717756) (tL 561283912465657))) (tN (tN (tL 549236596309756) (tL 562533815058173)) (tN (tL 549652671266556) tE)))) (tN (tN (tN (tN (tL 422214089964792) (tL 435511308713215)) (tN (tL 545771709103868) (tL 559068927786239))) (tN (tN (tL 547023759212284) (tL 562520001216255)) (tN (tL 547436076072700) tE))) (tN (tN (tN (tL 424430697839864) (tL 437727916588281)) (tN (tL 264314316946684) tE)) (tN (tN (tL 549240367087356) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 13297269476479)) (tN (tL 545772282449532) (tL 559069501197439))) (tN (tN (tL 70922828777596) (tL 509739654319743)) (tN (tL 547434434793084) (tL 562930676796543)))) (tN (tN (tN (tL 424463551044728) (tL 437726410054783)) (tN (tL 548092037176956) (tL 561286176709759))) (tN (tN (tL 496494447566460) (tL 509757306576511)) (tN (tL 549754189520508) tE)))) (tN (tN (tN (tN (tL 422214139087992) (tL 435511357836415)) (tN (tL 545773905710716) (tL 559071124393087))) (tN (tN (tL 494247183093372) (tL 509743425097343)) (tN (tL 547436058054268) tE))) (tN (tN (tN (tL 424465173810296) (tL 437727831493753)) (tN (tL 548093659909756) tE)) (tN (tN (tL 496498217815676) tE) tE)))) (tN (tN (tN (tN (tN (tL 422212517379192) (tL 435509736127615)) (tN (tL 545772284034684) (tL 559069502782591))) (tN (tN (tL 494243481009788) (tL 509739723013759)) (tN (tL 547434503487100) tE))) (tN (tN (tN (tL 424429192379640) (tL 428861581851897)) (tN (tL 547988959035132) tE)) (tN (tN (tL 496460088901372) tE) tE))) (tN (tN (tN (tN (tL 422214140689528) (tL 435511359437951)) (tN (tL 264298389519996) tE)) (tN (tN (tL 494247251803772) tE) tE)) (tN (tN (tN (tL 424430815673464) tE) tE) tE))))) (tN (tN (tN (tN (tN (tN (tN tE (tL 426644871350143)) (tN (tL 264295107577855) (tL 558792425113471))) (tN (tN (tL 247952757015039) (tL 562447442298879)) (tN (tL 265960481146879) (tL 559624575027071)))) (tN (tN (tN (tL 424463432781695) (tL 437726291791743)) (tN (tL 548089771446271) (tL 561283774646143))) (tN (tN (tL 549270887452671) (tL 562533746462719)) (tN (tL 549755681886207) tE)))) (tN (tN (tN (tN (tL 422214088363903) (tL 435511307112319)) (tN (tL 545771707551740) (tL 559034566543231))) (tN (tN (tL 547023690518527) (tL 562519932522495)) (tN (tL 547436007378943) tE))) (tN (tN (tN (tL 424465055977343) (tL 437727914987391)) (tN (tL 548091394641916) tE)) (tN (tN (tL 549274658131967) tE) tE)))) (tN (tN (tN (tN (tN (tL 140737489469439) (tL 426644872429567)) (tN (tL 264295109165055) (tL 453239309920255))) (tN (tN (tL 265545011757055) (tL 562447510994943)) (tN (tL 265960549842943) tE))) (tN (tN (tN (tL 424429074120703) (tL 437657573294079)) (tN (tL 547986693816319) tE)) (tN (tN (tL 549236596408319) tE) tE))) (tN (tN (tN (tN (tL 422214089441279) (tL 435440978100223)) (tN (tL 545771709136892) tE)) (tN (tN (tL 547023759212543) tE) tE)) (tN (tN (tN (tL 19208994815) tE) tE) tE)))) (tN (tN (tN (tN (tN (tN (tL 422212515893119) (tL 435509734641535)) (tN (tL 545772282564607) (tL 559067303481215))) (tN (tN (tL 494243412430847) (tL 509739654434815)) (tN (tL 547434434908159) tE))) (tN (tN (tN (tL 424463551143807) (tL 437726410153855)) (tN (tL 548092037292031) tE)) (tN (tN (tL 496494447681535) tE) tE))) (tN (tN (tN (tN (tL 140738625507134) (tL 435407741751167)) (tN (tL 264298392178620) tE)) (tN (tN (tL 212771669528510) tE) tE)) (tN (tN (tN (tL 142972815904574) tE) tE) tE))) (tN (tN (tN (tN (tN (tL 140737524006911) (tL 426610513477631)) (tN (tL 264297307439103) tE)) (tN (tN (tL 212768504414207) tE) tE)) (tN (tN (tN (tL 424429175701503) tE) tE) tE)) (tN (tN (tN (tN (tL 60817342) tE) tE) tE) tE)))))
private def c2Tree0 : Tree10 :=
  tN (tN c2Tree0_00 c2Tree0_01) (tN c2Tree0_10 c2Tree0_11)
private def c2Tree1_00 : Tree10 := (tN (tN (tN (tN (tN tE (tN tE (tN tE (tN tE (tL 35184237871104))))) (tN (tN tE (tN tE (tN tE (tL 314720051527680)))) (tN (tN tE (tN tE (tL 316633054806016))) (tN (tN tE (tL 289789913956352)) (tN (tL 18588490563584) (tL 35184244195328)))))) (tN (tN (tN tE (tN tE (tN tE (tL 314727086960704)))) (tN (tN tE (tN tE (tL 316633043710017))) (tN (tN tE (tL 290063237263424)) (tN (tL 26628731711488) (tL 316659283275840))))) (tN (tN (tN tE (tN tE (tL 314702739025985))) (tN (tN tE (tL 288134272659520)) (tN (tL 26622303940608) (tL 314728710144000)))) (tN (tN (tN tE (tL 290047546486849)) (tN (tL 27427409096704) (tL 316633326940225))) (tN (tN (tL 858934276096) (tL 290064860573760)) (tN (tL 27453371772928) (tL 316659289604096))))))) (tN (tN (tN (tN tE (tN tE (tN tE (tL 314728746713088)))) (tN (tN tE (tN tE (tL 316633092849664))) (tN (tN tE (tL 290063286403072)) (tN (tL 27453414572032) (tL 316659332415488))))) (tN (tN (tN tE (tN tE (tL 314702517731328))) (tN (tN tE (tL 288125731962880)) (tN (tL 26613763244032) (tL 314720068534272)))) (tN (tN (tN tE (tL 290047257968640)) (tN (tL 1038908620800) (tL 31859593936896))) (tN (tN (tL 584113684480) (tL 289790031790080)) (tN (tL 18588616589312) (tL 31885734674432)))))) (tN (tN (tN (tN tE (tN tE (tL 314702506635329))) (tN (tN tE (tL 288132700188736)) (tN (tL 26622342082560) (tL 314728748298304)))) (tN (tN (tN tE (tL 290045703368769)) (tN (tL 27427176591360) (tL 316633094434881))) (tN (tN (tL 857099612160) (tL 290063287988288)) (tN (tL 27453416157184) (tL 316659334000704))))) (tN (tN (tN (tN tE (tL 288108081836097)) (tN (tL 26596113117184) (tL 314702519332929))) (tN (tN (tL 18253598720) (tL 288125733564480)) (tN (tL 26613764845568) (tL 314720171048960)))) (tN (tN (tN (tL 832751792128) (tL 290047326679105)) (tN (tL 18631095193600) (tL 31859594465345))) (tN (tN (tL 584115539968) (tL 289790033391680)) (tN (tL 996431331328) tE))))))) (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 314727085392259)))) (tN (tN tE (tN tE (tL 316633042125187))) (tN (tN tE (tL 290063235694979)) (tN (tL 27453363896707) (tL 316659281691011))))) (tN (tN (tN tE (tN tE (tL 294911528190339))) (tN (tN tE (tL 288132459184513)) (tN (tL 26622302404994) (tL 297136321249667)))) (tN (tN (tN tE (tL 290045867180419)) (tN (tL 9834953032067) (tL 299041139310979))) (tN (tN (tL 858932691331) (tL 290063248376195)) (tN (tL 27453370188163) (tL 299067034878339)))))) (tN (tN (tN (tN tE (tN tE (tL 314700845347267))) (tN (tN tE (tL 288132649476545)) (tN (tL 26620680794499) (tL 314727086977475)))) (tN (tN (tN tE (tL 290045652693443)) (tN (tL 27427125916035) (tL 316633043759555))) (tN (tN (tL 857048936835) (tL 290063237280195)) (tN (tL 27453365481859) (tL 316659283276227))))) (tN (tN (tN (tN tE (tL 285909278323137)) (tN (tL 26596332859778) (tL 312503715819971))) (tN (tN (tL 26784362880) (tL 288132662092225)) (tN (tL 234024923520) (tL 288340431126913)))) (tN (tN (tN (tL 832971600259) (tL 290047546487235)) (tN (tL 27427409097091) (tL 316633326940611))) (tN (tN (tL 580835144065) (tL 289786224570817)) (tN (tL 1065092706689) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 314702513504643))) (tN (tN tE (tL 288132707074435)) (tN (tL 26622349001091) (tL 314728755184003)))) (tN (tN (tN tE (tL 290045643129219)) (tN (tL 27427183460739) (tL 316633101304195))) (tN (tN (tL 857106530691) (tL 290063294873987)) (tN (tL 27453423075715) (tL 316659340870019))))) (tN (tN (tN (tN tE (tL 288106740171139)) (tN (tL 9003927585155) (tL 297110602236291))) (tN (tN (tL 26841694595) (tL 288132711301507)) (tN (tL 26622353195395) (tL 297136472441219)))) (tN (tN (tN (tL 831141691779) (tL 290045917905283)) (tN (tL 1038910734720) (tL 14267678441859))) (tN (tN (tL 858991608195) (tL 290063299101059)) (tN (tL 18657336082816) tE))))) (tN (tN (tN (tN (tN tE (tL 288106458640835)) (tN (tL 26596100534659) (tL 314702506750403))) (tN (tN (tL 26023555459) (tL 288132700205507)) (tN (tL 26622342197635) (tL 314728748315075)))) (tN (tN (tN (tL 831128584579) (tL 290045703483843)) (tN (tL 27427176706435) (tL 313334559568323))) (tN (tN (tL 857099727235) (tL 289788410097857)) (tN (tL 27453416272259) tE)))) (tN (tN (tN (tN (tL 568324225) (tL 288108081836483)) (tN (tL 26596113117571) (tL 314702519333315))) (tN (tN (tL 18253607041) (tL 288124122952129)) (tN (tL 225485779329) tE))) (tN (tN (tN (tL 832751792515) (tL 290047326679491)) (tN (tL 18631096267136) tE)) (tN (tN (tL 31138508928) tE) tE)))))))
private def c2Tree1_01 : Tree10 := (tN (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 561009032953969)))) (tN (tN tE (tN tE (tL 562923109875809))) (tN (tN tE (tL 500892375711857)) (tN (tL 268280705056816) (tL 562949819203681))))) (tN (tN (tN tE (tN tE (tL 560993071530097))) (tN (tN tE (tL 499231846563953)) (tN (tL 275412510834736) (tL 455457539883105)))) (tN (tN (tN tE (tL 501153439776881)) (tN (tL 274825843146800) (tL 562923659427953))) (tN (tN (tL 214988627214384) (tL 500896146489457)) (tN (tL 268280717738032) (tL 457396709261409)))))) (tN (tN (tN (tN tE (tN tE (tL 560991449919601))) (tN (tN tE (tL 429969647349872)) (tN (tL 274285674901552) (tL 562117203210352)))) (tN (tN (tN tE (tL 501151885176945)) (tN (tL 274825899159600) (tL 562923648331889))) (tN (tN (tL 141869548310560) (tL 501169469796464)) (tN (tL 274843483779120) (tL 562949887897712))))) (tN (tN (tN (tN tE (tL 499214534062193)) (tN (tL 273161815339056) (tL 560993343647857))) (tN (tN (tL 212233610604592) (tL 500340016820336)) (tN (tL 274287298097200) (tL 456565710139488)))) (tN (tN (tN (tL 213047372804144) (tL 501153779019889)) (tN (tL 274826182389808) (tL 562923931562097))) (tN (tN (tL 213064686891056) (tL 501171093106800)) (tN (tL 274843496476720) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 560993109674097))) (tN (tN tE (tL 500338442766449)) (tN (tL 276522865133616) (tL 562118862964849)))) (tN (tN (tN tE (tL 501151867209841)) (tN (tL 274825881192496) (tL 562923697473649))) (tN (tN (tL 215296495716400) (tL 501169518938225)) (tN (tL 277076915914800) (tL 562949937039473))))) (tN (tN (tN (tN tE (tL 499214312769649)) (tN (tL 273163741530160) (tL 560993122355313))) (tN (tN (tL 213358941276208) (tL 499231964498033)) (tN (tL 275414776252464) (tL 455457556891745)))) (tN (tN (tN (tL 213047084288048) (tL 501153490503793)) (tN (tL 274825893873712) (tL 562923710154865))) (tN (tN (tL 215023241103408) (tL 500896264325233)) (tN (tL 268280835573808) tE))))) (tN (tN (tN (tN (tN tE (tL 499212691060849)) (tN (tL 273163730434096) (tL 560993111259249))) (tN (tN (tL 212232038135856) (tL 500338444351600)) (tN (tL 274289483724848) (tL 562118864550000)))) (tN (tN (tN (tL 142676784461856) (tL 501151935903857)) (tN (tL 274825949886512) (tL 562923699058801))) (tN (tN (tL 213063114307632) (tL 501169520523376)) (tN (tL 274843534506032) tE)))) (tN (tN (tN (tN (tL 211107908155440) (tL 499214314371185)) (tN (tL 273163743131696) (tL 455440007673969))) (tN (tN (tL 211125559883824) (tL 499231966099568)) (tN (tL 273181394860080) tE))) (tN (tN (tN (tL 213047152998448) (tL 501153559214193)) (tN (tL 266029868488752) tE)) (tN (tN (tL 212789859711024) tE) tE)))))) (tN (tN (tN (tN (tN (tN tE (tN tE (tL 560991448383987))) (tN (tN tE (tL 500338190762481)) (tN (tL 276519056359923) (tL 562117201674739)))) (tN (tN (tN tE (tL 501151816532467)) (tN (tL 274825830515187) (tL 562923646796275))) (tN (tN (tL 215296445039091) (tL 501169468260851)) (tN (tL 277076865237491) (tL 562949886362099))))) (tN (tN (tN (tN tE (tL 497015509238001)) (tN (tL 273161813803442) (tL 558794318856691))) (tN (tN (tL 214466992062896) (tL 500339813958129)) (tN (tL 276520679555506) (tL 456565507277283)))) (tN (tN (tN (tL 211938931933683) (tL 501153710326259)) (tN (tL 274826113696243) (tL 562923929977331))) (tN (tN (tL 215298068300275) (tL 501171091522035)) (tN (tL 277076877885939) tE))))) (tN (tN (tN (tN (tN tE (tL 496979257389553)) (tN (tL 273159921660403) (tL 560991449969139))) (tN (tN (tL 212231987458480) (tL 429969649463793)) (tN (tL 274285674951155) (tL 562117203227123)))) (tN (tN (tN (tL 142676733735395) (tL 501151885226483)) (tN (tL 274825899209203) (tL 562923648381427))) (tN (tN (tL 213063063630323) (tL 501169469813235)) (tN (tL 274843483828723) tE)))) (tN (tN (tN (tN (tL 211108127895984) (tL 497015510856177)) (tN (tL 273161815388594) (tL 558794320441843))) (tN (tN (tL 26792751536) (tL 288132653707745)) (tN (tL 35693274919344) tE))) (tN (tN (tN (tL 213047372804595) (tL 501153779020275)) (tN (tL 274826182390259) tE)) (tN (tN (tL 212786587759089) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 499212697979379)) (tN (tL 273163737352691) (tL 560993118177779))) (tN (tN (tL 214465428048371) (tL 500338451270131)) (tN (tL 276522873637363) (tL 562118871468531)))) (tN (tN (tN (tL 142676683114979) (tL 501151875713523)) (tN (tL 274825889696243) (tL 562923705977331))) (tN (tN (tL 215296504220147) (tL 501169527441907)) (tN (tL 277076924418547) tE)))) (tN (tN (tN (tN (tL 211108177103347) (tL 499214583319027)) (tN (tL 273164012079603) (tL 560993392904691))) (tN (tN (tL 214467042855411) (tL 500340066077171)) (tN (tL 276522877831667) tE))) (tN (tN (tN (tL 213047354837491) (tL 501153761053171)) (tN (tL 274826164423155) tE)) (tN (tN (tL 215298119027187) tE) tE)))) (tN (tN (tN (tN (tN (tL 35650019) (tL 499212691175923)) (tN (tL 273163730549235) (tL 560993111374323))) (tN (tN (tL 212232038250995) (tL 500338444368371)) (tN (tL 274289483839987) tE))) (tN (tN (tN (tL 142676785625571) (tL 501151936018931)) (tN (tL 274825950001651) tE)) (tN (tN (tL 213063114422771) tE) tE))) (tN (tN (tN (tN (tL 211107908155891) (tL 428843959581171)) (tN (tL 273163743132147) tE)) (tN (tN (tL 18253609457) tE) tE)) (tN (tN (tN (tL 213047152998899) tE) tE) tE))))))
private def c2Tree1_10 : Tree10 := (tN (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 350177678329356)))) (tN (tN tE (tN tE (tL 70350490568204))) (tN (tN tE (tL 351427513812492)) (tN (tL 54872370054668) (tL 70368612058636))))) (tN (tN (tN tE (tN tE (tL 350161716971020))) (tN (tN tE (tL 296990426629644)) (tN (tL 62072895374860) (tL 350179301523468)))) (tN (tN (tN tE (tL 351688577877516)) (tN (tL 54923517592076) (tL 351826016830988))) (tN (tN (tL 54460065875468) (tL 351431284590092)) (tN (tL 54872382735884) (tL 70368624672780)))))) (tN (tN (tN (tN tE (tN tE (tL 350160095297103))) (tN (tN tE (tL 296997461966412)) (tN (tL 62079930744332) (tL 350186336960076)))) (tN (tN (tN tE (tL 351687023279695)) (tN (tL 63719666630156) (tL 351826072845903))) (tN (tN (tL 54733389184524) (tL 351704607899212)) (tN (tL 63737251249676) (tL 351843657465420))))) (tN (tN (tN (tN tE (tL 296973114146383)) (tN (tL 62055582875148) (tL 350161989090895))) (tN (tN (tL 27866562060) (tL 296999085276748)) (tN (tL 62081554005516) (tL 350187960141836)))) (tN (tN (tN (tL 54717698407948) (tL 351688917122639)) (tN (tL 63719949860364) (tL 351826356076111))) (tN (tN (tL 54735012494860) (tL 351706231209548)) (tN (tL 63737263947276) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 350162291918348))) (tN (tN tE (tL 296997511104012)) (tN (tL 62082127365644) (tL 350188533581324)))) (tN (tN (tN tE (tL 334094819264012)) (tN (tL 53272677581836) (tL 351824444261900))) (tN (tN (tL 37141252277772) (tL 334112470992396)) (tN (tL 63735689774604) (tL 351842095990284))))) (tN (tN (tN (tN tE (tL 296972892734988)) (tN (tL 53261382387212) (tL 350163915179532))) (tN (tN (tL 19325748748) (tL 296990544463372)) (tN (tL 62075160692236) (tL 350181465982476)))) (tN (tN (tN (tL 37123613230604) (tL 334096442557964)) (tN (tL 53274300843532) (tL 67052555929100))) (tN (tN (tL 1683625575948) (tL 298654844290572)) (tN (tL 53772988909068) tE))))) (tN (tN (tN (tN (tN tE (tL 296971271028303)) (tN (tL 62055887289868) (tL 350162293505615))) (tN (tN (tL 26293976588) (tL 296997512691276)) (tN (tL 62082128952844) (tL 350186387676684)))) (tN (tN (tN (tL 37123668184584) (tL 334094887960143)) (tN (tL 63718106742284) (tL 351824512958031))) (tN (tN (tL 37141253864972) (tL 334112472579660)) (tN (tL 54870878854668) tE)))) (tN (tN (tN (tN (tL 1675623948) (tL 296972894338639)) (tN (tL 62057510551052) (tL 350163916766799))) (tN (tN (tL 19327352332) (tL 296990546067020)) (tN (tL 62075162279436) tE))) (tN (tN (tN (tL 37125292555788) (tL 334096511270479)) (tN (tL 53824124296716) tE)) (tN (tN (tL 1683627179532) tE) tE)))))) (tN (tN (tN (tN (tN (tN tE (tN tE (tL 350160093710223))) (tN (tN tE (tL 13254740952975)) (tN (tL 62079929206671) (tL 350186335389583)))) (tN (tN (tN tE (tL 351686954583951)) (tN (tL 63719597934479) (tL 351826004150159))) (tN (tN (tL 54733387646863) (tL 351704606328719)) (tN (tL 63737249712015) (tL 351843655894927))))) (tN (tN (tN (tN tE (tL 296972038817679)) (tN (tL 62055312901006) (tL 347962964296591))) (tN (tN (tL 27864975247) (tL 296998009948047)) (tN (tL 62081552467854) (tL 350187757289871)))) (tN (tN (tN (tL 54715750664079) (tL 351687774685071)) (tN (tL 63719612728207) (tL 351826287379343))) (tN (tN (tL 54735010908047) (tL 351705155880847)) (tN (tL 63737262360463) tE))))) (tN (tN (tN (tN (tN tE (tL 296971220352975)) (tN (tL 62053689130895) (tL 350160095346639))) (tN (tN (tL 26243301263) (tL 296997461983183)) (tN (tL 62079930793871) (tL 350186336976847)))) (tN (tN (tN (tL 54715804600719) (tL 351687023329231)) (tN (tL 63719666679695) (tL 351826072895439))) (tN (tN (tL 54733389234063) (tL 351704607915983)) (tN (tL 63737251299215) tE)))) (tN (tN (tN (tN (tL 1895432079) (tL 296973114146767)) (tN (tL 62055582924686) (tL 347962965884879))) (tN (tN (tL 27866562447) (tL 296998011535311)) (tN (tL 62081554055054) tE))) (tN (tN (tN (tL 54717698408335) (tL 351688917123023)) (tN (tL 63719949860751) tE)) (tN (tN (tL 54735012495247) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 296971277895567)) (tN (tL 62056967899023) (tL 350163374114703))) (tN (tN (tL 26300893071) (tL 296997519574927)) (tN (tL 62083209611151) (tL 350189615794063)))) (tN (tN (tN (tL 37123566798735) (tL 334094827718543)) (tN (tL 63719120242575) (tL 351825526458255))) (tN (tN (tL 37141260781455) (tL 334112479463311)) (tN (tL 63736772020111) tE)))) (tN (tN (tN (tN (tL 65521551) (tL 296972089542543)) (tN (tL 62057477556110) (tL 66490151978895))) (tN (tN (tL 27915700111) (tL 296998060672911)) (tN (tL 62083750676366) tE))) (tN (tN (tN (tL 37123615344527) (tL 334095639365519)) (tN (tL 53274302990220) tE)) (tN (tN (tL 37142875588495) tE) tE)))) (tN (tN (tN (tN (tN (tL 35639183) (tL 296971271143375)) (tN (tL 62055887404943) (tL 347961072549839))) (tN (tN (tL 26294091663) (tL 296997512708047)) (tN (tL 62082129067919) tE))) (tN (tN (tN (tL 37123669348239) (tL 334094888075215)) (tN (tL 63718106857359) tE)) (tN (tN (tL 37141253980047) tE) tE))) (tN (tN (tN (tN (tL 1675624335) (tL 296972894339023)) (tN (tL 62057510600590) tE)) (tN (tN (tL 19327352719) tE) tE)) (tN (tN (tN (tL 37125292556175) tE) tE) tE))))))
private def c2Tree1_11 : Tree10 := (tN (tN (tN (tN (tN (tN (tN tE (tN tE (tL 558792425079935))) (tN (tN tE (tL 499230223369855)) (tN (tL 275410887640636) (tL 561009032955519)))) (tN (tN (tN tE (tL 562447442249343)) (tN (tL 265960481097276) (tL 562923109876863))) (tN (tN (tL 267795910624828) (tL 562465026868863)) (tN (tL 268280705058364) (tL 562949684985983))))) (tN (tN (tN (tN tE (tL 499214262044287)) (tN (tL 273161543288380) (tL 560993071597183))) (tN (tN (tL 213358823441980) (tL 499231846663807)) (tN (tL 275412510901820) (tL 561010656149631)))) (tN (tN (tN (tL 265823591695932) (tL 562726090933887)) (tN (tL 274825843148348) (tL 562923659429503))) (tN (tN (tL 267799681402428) (tL 562468797646463)) (tN (tL 268280717739580) tE))))) (tN (tN (tN (tN (tN tE (tL 499212640337535)) (tN (tL 273159921614396) (tL 560991449923199))) (tN (tN (tL 212231987412540) (tL 500338393628284)) (tN (tL 274285674905148) (tL 562117203213948)))) (tN (tN (tN (tL 248229850003512) (tL 562724536335999)) (tN (tL 274825899163196) (tL 562923648335487))) (tN (tN (tL 265839621717564) (tL 562742120955516)) (tN (tL 274842676378684) tE)))) (tN (tN (tN (tN (tL 211108127964732) (tL 499214534180479)) (tN (tL 273161815408188) (tL 560993343716991))) (tN (tN (tL 212233610722876) (tL 500340016938620)) (tN (tL 273187786472508) tE))) (tN (tN (tN (tL 265823930940988) (tL 562726430178943)) (tN (tL 274826182393404) tE)) (tN (tN (tL 265841245027900) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 499212689477247)) (tN (tL 273162118237756) (tL 560991499062911))) (tN (tN (tL 214465419546172) (tL 500338442767999)) (tN (tL 276521254522428) (tL 562117252353663)))) (tN (tN (tN (tL 248229799267896) (tL 536336239300223)) (tN (tL 274824270581308) (tL 562922086862463))) (tN (tN (tL 250480867806780) (tL 536353888930937)) (tN (tL 277075305303612) tE)))) (tN (tN (tN (tN (tL 211107906555452) (tL 499214312771199)) (tN (tL 273163741498940) (tL 560993122324095))) (tN (tN (tL 213358941277756) (tL 499231863836285)) (tN (tL 275414776221244) tE))) (tN (tN (tN (tL 248231456378428) (tL 536337862594175)) (tN (tL 274825893842492) tE)) (tN (tN (tL 215023241104956) tE) tE)))) (tN (tN (tN (tN (tN (tL 70368778665528) (tL 499212691062399)) (tN (tL 273162119822908) (tL 560991500648063))) (tN (tN (tL 212232038137404) (tL 500338444353148)) (tN (tL 274287873113660) tE))) (tN (tN (tN (tL 248229900729912) (tL 536336307994239)) (tN (tL 274824339275324) tE)) (tN (tN (tL 248247486398012) tE) tE))) (tN (tN (tN (tN (tL 211107908156988) (tL 499214314372735)) (tN (tL 273163743084092) tE)) (tN (tN (tL 211125559885372) tE) tE)) (tN (tN (tN (tL 248231525088828) tE) tE) tE))))) (tN (tN (tN (tN (tN (tN (tN tE (tL 4432406266111)) (tN (tL 273159920076799) (tL 560991448385535))) (tN (tN (tL 214465368868863) (tL 500338392090623)) (tN (tL 276519056361471) (tL 562117201676287)))) (tN (tN (tN (tL 247121680843263) (tL 562724467689471)) (tN (tL 274825830516735) (tL 562923646797823))) (tN (tN (tL 268073003173887) (tL 562742119417855)) (tN (tL 277076865239039) tE)))) (tN (tN (tN (tN (tL 211108126377983) (tL 499214532593663)) (tN (tL 273161813870526) (tL 558794318923775))) (tN (tN (tL 214466992130047) (tL 500340015351807)) (tN (tL 276520679622590) tE))) (tN (tN (tN (tL 265823862245375) (tL 562726361483263)) (tN (tL 274826113697791) tE)) (tN (tN (tL 268074626435071) tE) tE)))) (tN (tN (tN (tN (tN (tL 70368745814527) (tL 499212640387071)) (tN (tL 273159921663999) (tL 560991449972735))) (tN (tN (tL 212231987462143) (tL 500338393645055)) (tN (tL 274285674954751) tE))) (tN (tN (tN (tL 248229851101695) (tL 562724536385535)) (tN (tL 274825899212799) tE)) (tN (tN (tL 265839621767167) tE) tE))) (tN (tN (tN (tN (tL 211108127965183) (tL 499214534180863)) (tN (tL 273161815457726) tE)) (tN (tN (tL 26792820735) tE) tE)) (tN (tN (tN (tL 265823930941439) tE) tE) tE)))) (tN (tN (tN (tN (tN (tN (tL 70368744427519) (tL 499212697980927)) (tN (tL 273163200483327) (tL 560992581308415))) (tN (tN (tL 214465428049919) (tL 500338451271679)) (tN (tL 276522336767999) tE))) (tN (tN (tN (tL 248229799383039) (tL 536336247803903)) (tN (tL 274825352826879) tE)) (tN (tN (tL 250480876310527) tE) tE))) (tN (tN (tN (tN (tL 211108177104895) (tL 496980898336767)) (tN (tL 273164012081086) tE)) (tN (tN (tL 214467042856959) tE) tE)) (tN (tN (tN (tL 248231726927871) tE) tE) tE))) (tN (tN (tN (tN (tN (tL 70368779829247) (tL 499212691177471)) (tN (tL 273162119938047) tE)) (tN (tN (tL 212232038252543) tE) tE)) (tN (tN (tN (tL 248229901893631) tE) tE) tE)) (tN (tN (tN (tN (tL 211107908157439) tE) tE) tE) tE)))))
private def c2Tree1 : Tree10 :=
  tN (tN c2Tree1_00 c2Tree1_01) (tN c2Tree1_10 c2Tree1_11)
private def c2Tree2_00 : Tree10 := (tN (tN (tN (tN (tN tE (tN tE (tN tE (tN tE (tL 35184237871104))))) (tN (tN tE (tN tE (tN tE (tL 314720051527680)))) (tN (tN tE (tN tE (tL 316633054806016))) (tN (tN tE (tL 289789913956352)) (tN (tL 18588490563584) (tL 35184244195328)))))) (tN (tN (tN tE (tN tE (tN tE (tL 350177679913024)))) (tN (tN tE (tN tE (tL 70350559260675))) (tN (tN tE (tL 298651024371776)) (tN (tL 54872438747136) (tL 70368680751104))))) (tN (tN (tN tE (tN tE (tL 350161718489155))) (tN (tN tE (tL 296990428115008)) (tN (tL 62072896892928) (tL 314994931007488)))) (tN (tN (tN tE (tL 298912088453187)) (tN (tL 63719679324160) (tL 351826085539907))) (tN (tN (tL 1133820100608) (tL 298654795165760)) (tN (tL 54872451444736) (tL 35184321282048))))))) (tN (tN (tN (tN tE (tN tE (tN tE (tL 314728746713088)))) (tN (tN tE (tN tE (tL 316633092849664))) (tN (tN tE (tL 290063286403072)) (tN (tL 27453414572032) (tL 316659332415488))))) (tN (tN (tN tE (tN tE (tL 314702517731328))) (tN (tN tE (tL 288125731962880)) (tN (tL 26613763244032) (tL 314720068534272)))) (tN (tN (tN tE (tL 290047257968640)) (tN (tL 1038908620800) (tL 31859593936896))) (tN (tN (tL 584113684480) (tL 289790031790080)) (tN (tL 18588616589312) (tL 31885734674432)))))) (tN (tN (tN (tN tE (tN tE (tL 350163904114755))) (tN (tN tE (tL 296997512687680)) (tN (tL 62083739561984) (tL 350190145777728)))) (tN (tN (tN tE (tL 298910515867715)) (tN (tL 63719717351424) (tL 351826123567171))) (tN (tN (tL 1956881772544) (tL 298928100487232)) (tN (tL 63737301970944) (tL 351843708186688))))) (tN (tN (tN (tN tE (tL 296972894335043)) (tN (tL 62057510596608) (tL 350163916812355))) (tN (tN (tL 19327348736) (tL 296990546063424)) (tN (tL 62075162324992) (tL 314997196439552)))) (tN (tN (tN (tL 1940920463360) (tL 298912139178051)) (tN (tL 63719730049024) (tL 351826136264771))) (tN (tN (tL 1683627175936) (tL 298654845890624)) (tN (tL 54872502169600) tE))))))) (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 350177678344579)))) (tN (tN tE (tN tE (tL 70350490567043))) (tN (tN tE (tL 298650955694467)) (tN (tL 54872370102659) (tL 70368612073859))))) (tN (tN (tN tE (tN tE (tL 295151775809923))) (tN (tN tE (tL 296989218619779)) (tN (tL 62072895357314) (tL 297402609222019)))) (tN (tN (tN tE (tL 298910946001283)) (tN (tL 10943052480899) (tL 299049458696579))) (tN (tN (tL 1683507757443) (tL 298651505246595)) (tN (tL 54872382751107) (tL 17592066556291)))))) (tN (tN (tN (tN tE (tN tE (tL 66486095376771))) (tN (tN tE (tL 296920085455299)) (tN (tL 62071273746819) (tL 350177679929795)))) (tN (tN (tN tE (tL 298633439801795)) (tN (tL 54854317306243) (tL 70350559310211))) (tN (tN (tL 1679805706627) (tL 298651024388547)) (tN (tL 54872438796675) (tL 70368680767875))))) (tN (tN (tN (tN tE (tL 294739460551107)) (tN (tL 62054230192514) (tL 347928335544771))) (tN (tN (tL 19209449856) (tL 296989354418627)) (tN (tL 62072896942466) (tL 297127866581379)))) (tN (tN (tN (tL 1940869738883) (tL 298912088453571)) (tN (tL 63719679324547) (tL 351826085540291))) (tN (tN (tL 1683576451459) (tL 298651573940675)) (tN (tL 2095893307779) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 350163902529923))) (tN (tN tE (tL 296997511119235)) (tN (tL 62083738091907) (tL 350190144209283)))) (tN (tN (tN tE (tL 298910447174019)) (tN (tL 63719648657795) (tL 351826054873475))) (tN (tN (tL 1956880302467) (tL 298928098918787)) (tN (tL 63737300500867) (tL 351843706618243))))) (tN (tN (tN (tN tE (tL 296971818991874)) (tN (tL 9280950862211) (tL 297387357077891))) (tN (tN (tL 19325763971) (tL 296989470736771)) (tN (tL 62075160740227) (tL 297404907897219)))) (tN (tN (tN (tL 1939241140611) (tL 298910996726147)) (tN (tL 1047498555776) (tL 14275997827459))) (tN (tN (tL 1683625591171) (tL 298651623080323)) (tN (tL 53772988957056) tE))))) (tN (tN (tN (tN (tN tE (tL 296971271139779)) (tN (tL 62057498014083) (tL 350163904229827))) (tN (tN (tL 26294088067) (tL 296997512704451)) (tN (tL 62083739677059) (tL 350190145794499)))) (tN (tN (tN (tL 1939297268099) (tL 298910515982787)) (tN (tL 63719717466499) (tL 351826123682243))) (tN (tN (tL 1956881887619) (tL 298928100504003)) (tN (tL 63737302086019) tE)))) (tN (tN (tN (tN (tL 543146242) (tL 296972894335427)) (tN (tL 62057510596995) (tL 350163916812739))) (tN (tN (tL 19327349123) (tL 296989472321987)) (tN (tL 62075162325379) tE))) (tN (tN (tN (tL 1940920463747) (tL 298912139178435)) (tN (tL 53824125399424) tE)) (tN (tN (tL 1683627176323) tE) tE)))))))
private def c2Tree2_01 : Tree10 := (tN (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 561009032953969)))) (tN (tN tE (tN tE (tL 562923109875809))) (tN (tN tE (tL 500892375711857)) (tN (tL 268280705056816) (tL 562949819203681))))) (tN (tN (tN tE (tN tE (tL 560993071530097))) (tN (tN tE (tL 499231846563953)) (tN (tL 275412510834736) (tL 455457539883105)))) (tN (tN (tN tE (tL 501153439776881)) (tN (tL 274825843146800) (tL 562923659427953))) (tN (tN (tL 214988627214384) (tL 500896146489457)) (tN (tL 268280717738032) (tL 457396709261409)))))) (tN (tN (tN (tN tE (tN tE (tL 559067304570979))) (tN (tN tE (tL 296920083345520)) (tN (tL 556851506196592) (tL 561283912446064)))) (tN (tN (tN tE (tL 509739672285299)) (tN (tL 547435526500464) (tL 562931768504419))) (tN (tN (tL 496459769192560) (tL 509757256904816)) (tN (tL 549652671246448) (tL 562949889994848))))) (tN (tN (tN (tN tE (tL 508079076028531)) (tN (tL 554636521517168) (tL 561267951022195))) (tN (tN (tL 494799441371248) (tL 508096660648048)) (tN (tL 556853129392240) (tL 455732419375200)))) (tN (tN (tN (tL 493413976891504) (tL 510018320986227)) (tN (tL 556300888567920) (tL 562932318072947))) (tN (tN (tL 496463808422000) (tL 509761027698800)) (tN (tL 549652683944048) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 560993109674097))) (tN (tN tE (tL 500338442766449)) (tN (tL 276522865133616) (tL 562118862964849)))) (tN (tN (tN tE (tL 501151867209841)) (tN (tL 274825881192496) (tL 562923697473649))) (tN (tN (tL 215296495716400) (tL 501169518938225)) (tN (tL 277076915914800) (tL 562949937039473))))) (tN (tN (tN (tN tE (tL 499214312769649)) (tN (tL 273163741530160) (tL 560993122355313))) (tN (tN (tL 213358941276208) (tL 499231964498033)) (tN (tL 275414776252464) (tL 455457556891745)))) (tN (tN (tN (tL 213047084288048) (tL 501153490503793)) (tN (tL 274825893873712) (tL 562923710154865))) (tN (tN (tL 215023241103408) (tL 500896264325233)) (tN (tL 268280835573808) tE))))) (tN (tN (tN (tN (tN tE (tL 508077503559795)) (tN (tL 554638707144816) (tL 561270136649843))) (tN (tN (tL 495906038102128) (tL 509203256850544)) (tN (tL 557963483691120) (tL 562395889940592)))) (tN (tN (tN (tL 494520506398832) (tL 510016748402803)) (tN (tL 556300926597232) (tL 562932356102259))) (tN (tN (tL 496737114273904) (tL 510034333022320)) (tN (tL 558517534472304) tE)))) (tN (tN (tN (tN (tL 492582884866160) (tL 508079126870131)) (tN (tL 554638719842416) (tL 561270149347443))) (tN (tN (tL 494799559850096) (tL 508096778598512)) (tN (tL 556855394826352) tE))) (tN (tN (tN (tL 494522129709168) (tL 510018371713139)) (tN (tL 556300939294832) tE)) (tN (tN (tL 496463859677296) tE) tE)))))) (tN (tN (tN (tN (tN (tN tE (tN tE (tL 559067303035363))) (tN (tN tE (tL 508026182222323)) (tN (tL 556885864399347) (tL 561283910910451)))) (tN (tN (tN tE (tL 509739603640819)) (tN (tL 547435457855987) (tL 562931699859939))) (tN (tN (tL 496494329250291) (tL 509757188260339)) (tN (tL 549755681817075) (tL 562949821350371))))) (tN (tN (tN (tN tE (tL 505845691498995)) (tN (tL 554636519981554) (tL 559034566492659))) (tN (tN (tL 494833800102384) (tL 508096524894707)) (tN (tL 556887487594994) (tL 455732283621859)))) (tN (tN (tN (tL 494522010288627) (tL 510018252292595)) (tN (tL 556300819874291) (tL 562932249379315))) (tN (tN (tL 496498099995123) (tL 509760959005171)) (tN (tL 549755694465523) tE))))) (tN (tN (tN (tN (tN tE (tL 435406606234083)) (tN (tL 545770085872115) (tL 453239310447075))) (tN (tN (tL 494797818753520) (tL 296920085459443)) (tN (tL 556851506246131) (tL 455455918289395)))) (tN (tN (tN (tL 494243430330867) (tL 509739672334835)) (tN (tL 547435526550003) (tL 562931768553955))) (tN (tN (tL 496460038205939) (tL 509757256921587)) (tN (tL 549652671295987) tE)))) (tN (tN (tN (tN (tL 492582834074096) (tL 435406618817011)) (tN (tL 554636521566706) (tL 453206573904371))) (tN (tN (tL 494799441949168) (tL 296920089686499)) (tN (tL 556853129441778) tE))) (tN (tN (tN (tL 494522078982643) (tL 510018320986611)) (tN (tL 556300888568307) tE)) (tN (tN (tL 496463808950771) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 508077502089715)) (tN (tL 554638705674739) (tL 561270135179763))) (tN (tN (tL 495940396370419) (tL 509203255380467)) (tN (tL 557997841959411) (tL 562395888470515)))) (tN (tN (tN (tL 424151659825635) (tL 510016679823859)) (tN (tL 556300858018291) (tL 562932287523315))) (tN (tN (tL 496771472542195) (tL 510034331552243)) (tN (tL 558551892740595) tE)))) (tN (tN (tN (tN (tL 492582883281395) (tL 508079125285363)) (tN (tL 554638718257651) (tL 561270147762675))) (tN (tN (tL 494833918003699) (tL 508096777013747)) (tN (tL 556889752979955) tE))) (tN (tN (tN (tL 494522061015539) (tL 510018303019507)) (tN (tL 556300870601203) tE)) (tN (tN (tL 496498217830899) tE) tE)))) (tN (tN (tN (tN (tN (tL 492581261670899) (tL 508077503674867)) (tN (tL 554638707259891) (tL 561270136764915))) (tN (tN (tL 495906038217203) (tL 509203256867315)) (tN (tL 557963483806195) tE))) (tN (tN (tN (tL 494520506513907) (tL 510016748517875)) (tN (tL 556300926712307) tE)) (tN (tN (tL 496737114388979) tE) tE))) (tN (tN (tN (tN (tL 492582884866547) (tL 437640052603379)) (tN (tL 554638719842803) tE)) (tN (tN (tL 494799559850483) tE) tE)) (tN (tN (tN (tL 494522129709555) tE) tE) tE))))))
private def c2Tree2_10 : Tree10 := (tN (tN (tN (tN (tN (tN tE (tN tE (tN tE (tL 350177678329356)))) (tN (tN tE (tN tE (tL 70350490568204))) (tN (tN tE (tL 351427513812492)) (tN (tL 54872370054668) (tL 70368612058636))))) (tN (tN (tN tE (tN tE (tL 350161716971020))) (tN (tN tE (tL 296990426629644)) (tN (tL 62072895374860) (tL 350179301523468)))) (tN (tN (tN tE (tL 351688577877516)) (tN (tL 54923517592076) (tL 351826016830988))) (tN (tN (tL 54460065875468) (tL 351431284590092)) (tN (tL 54872382735884) (tL 70368624672780)))))) (tN (tN (tN (tN tE (tN tE (tL 66486095330847))) (tN (tN tE (tL 296988804922972)) (tN (tL 62071273700892) (tL 350177679916636)))) (tN (tN (tN tE (tL 421778742066783)) (tN (tL 125223061437980) (tL 140719303441951))) (tN (tN (tL 124825107971612) (tL 421796326686300)) (tN (tL 125241182928412) (tL 140737424932380))))) (tN (tN (tN (tN tE (tL 296972843613791)) (tN (tL 62055312342556) (tL 350161718558303))) (tN (tN (tL 19209518620) (tL 296990428233308)) (tN (tL 62072896962076) (tL 350179303098396)))) (tN (tN (tN (tL 125086172053020) (tL 422057390767711)) (tN (tL 134088423505436) (tL 422194829721183))) (tN (tN (tL 124828878765596) (tL 421800097480284)) (tN (tL 125241195626012) tE)))))) (tN (tN (tN (tN (tN tE (tN tE (tL 350162291918348))) (tN (tN tE (tL 296997511104012)) (tN (tL 62082127365644) (tL 350188533581324)))) (tN (tN (tN tE (tL 334094819264012)) (tN (tL 53272677581836) (tL 351824444261900))) (tN (tN (tL 37141252277772) (tL 334112470992396)) (tN (tL 63735689774604) (tL 351842095990284))))) (tN (tN (tN (tN tE (tL 296972892734988)) (tN (tL 53261382387212) (tL 350163915179532))) (tN (tN (tL 19325748748) (tL 296990544463372)) (tN (tL 62075160692236) (tL 350181465982476)))) (tN (tN (tN (tL 37123613230604) (tL 334096442557964)) (tN (tL 53274300843532) (tL 67052555929100))) (tN (tN (tL 1683625575948) (tL 298654844290572)) (tN (tL 53772988909068) tE))))) (tN (tN (tN (tN (tN tE (tL 296971271028319)) (tN (tL 62055887289884) (tL 350162293505631))) (tN (tN (tL 26293976604) (tL 296997512691292)) (tN (tL 62082128952860) (tL 350188535168604)))) (tN (tN (tN (tL 107492413423132) (tL 404463632137823)) (tN (tL 134086850919964) (tL 422193257135711))) (tN (tN (tL 107509998042652) (tL 404481216757340)) (tN (tL 134104435539484) tE)))) (tN (tN (tN (tN (tL 1675623964) (tL 296972894338655)) (tN (tL 62057510551068) (tL 350163916766815))) (tN (tN (tL 19327352348) (tL 296990546067036)) (tN (tL 62075162279452) tE))) (tN (tN (tN (tL 107494036733468) (tL 404465255448159)) (tN (tL 134088474181148) tE)) (tN (tN (tL 72052371357212) tE) tE)))))) (tN (tN (tN (tN (tN (tN tE (tN tE (tL 66486093744015))) (tN (tN tE (tL 296988803352463)) (tN (tL 62071272163215) (tL 350177542014863)))) (tN (tN (tN tE (tL 351409929193359)) (tN (tL 54854248564623) (tL 67043365750671))) (tN (tN (tL 54456295147407) (tL 351427513829263)) (tN (tL 54872370104207) (tL 70368475744143))))) (tN (tN (tN (tN tE (tL 296971768268687)) (tN (tL 62055310787470) (tL 347928334009231))) (tN (tN (tL 19207931791) (tL 296989352904591)) (tN (tL 62072895424398) (tL 350179165241743)))) (tN (tN (tN (tL 54715748550543) (tL 351687504136079)) (tN (tL 63719610614671) (tL 348518892012431))) (tN (tN (tL 54460065892239) (tL 351428063381391)) (tN (tL 54872382752655) tE))))) (tN (tN (tN (tN (tN tE (tL 13297220386703)) (tN (tL 53188876631951) (tL 66486094849935))) (tN (tN (tL 17586257807) (tL 296988804939727)) (tN (tL 62071273750415) (tL 350177679402959)))) (tN (tN (tN (tL 54438779223951) (tL 351409997938639)) (tN (tL 54854317309839) (tL 67043433965455))) (tN (tN (tL 54456363843471) (tL 351427582525391)) (tN (tL 54871901923215) tE)))) (tN (tN (tN (tN (tL 1624899471) (tL 296972843614159)) (tN (tL 62055312392078) (tL 347928335083471))) (tN (tN (tL 19209518991) (tL 296989354491855)) (tN (tL 62072897011598) tE))) (tN (tN (tN (tL 54717427875727) (tL 351688646590415)) (tN (tL 63719679328143) tE)) (tN (tN (tL 54460134588303) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 296971269441423)) (tN (tL 62055885703055) (tL 347961070847887))) (tN (tN (tL 26292504463) (tL 296997511120783)) (tN (tL 62082127480719) (tL 350186199451535)))) (tN (tN (tN (tL 37123566733199) (tL 334094819264399)) (tN (tL 63718038046607) (tL 348517319444367))) (tN (tN (tL 37141252392847) (tL 298653218899855)) (tN (tL 63735689889679) tE)))) (tN (tN (tN (tN (tL 63408015) (tL 296971818993551)) (tN (tL 62057475442574) (tL 66453357430671))) (tN (tN (tL 19325765519) (tL 296989470738319)) (tN (tL 62075160741774) tE))) (tN (tN (tN (tL 37123613230991) (tL 334095368816527)) (tN (tL 53265710941964) tE)) (tN (tN (tL 34358151054) tE) tE)))) (tN (tN (tN (tN (tN (tL 52428687) (tL 296971271143375)) (tN (tL 62055887404943) (tL 347961072549839))) (tN (tN (tL 26294091663) (tL 296997512708047)) (tN (tL 62082129067919) tE))) (tN (tN (tN (tL 37123669360527) (tL 334094888075215)) (tN (tL 63718106857359) tE)) (tN (tN (tL 37141253980047) tE) tE))) (tN (tN (tN (tN (tL 1675624335) (tL 296972894339023)) (tN (tL 62057510600590) tE)) (tN (tN (tL 19327352719) tE) tE)) (tN (tN (tN (tL 37125292556175) tE) tE) tE))))))
private def c2Tree2_11 : Tree10 := (tN (tN (tN (tN (tN (tN (tN tE (tN tE (tL 558792425079935))) (tN (tN tE (tL 499230223369855)) (tN (tL 275410887640636) (tL 561009032955519)))) (tN (tN (tN tE (tL 562447442249343)) (tN (tL 265960481097276) (tL 562923109876863))) (tN (tN (tL 267795910624828) (tL 562465026868863)) (tN (tL 268280705058364) (tL 562949684985983))))) (tN (tN (tN (tN tE (tL 499214262044287)) (tN (tL 273161543288380) (tL 560993071597183))) (tN (tN (tL 213358823441980) (tL 499231846663807)) (tN (tL 275412510901820) (tL 561010656149631)))) (tN (tN (tN (tL 265823591695932) (tL 562726090933887)) (tN (tL 274825843148348) (tL 562923659429503))) (tN (tN (tL 267799681402428) (tL 562468797646463)) (tN (tL 268280717739580) tE))))) (tN (tN (tN (tN (tN tE (tL 435509685402751)) (tN (tL 545770085826172) (tL 559067304574079))) (tN (tN (tL 494797818707580) (tL 508095037455996)) (tN (tL 556851506200188) (tL 561283912449660)))) (tN (tN (tN (tL 547019988418172) (tL 562516230422143)) (tN (tL 547435526504060) (tL 562931768507519))) (tN (tN (tL 549236596293244) (tL 562533815041660)) (tN (tL 549651863846012) tE)))) (tN (tN (tN (tN (tL 492582834142844) (tL 508079076146815)) (tN (tL 554636521586300) (tL 561267951091327))) (tN (tN (tL 494799442017916) (tL 508096660766332)) (tN (tL 273179129429116) tE))) (tN (tN (tN (tL 547298637119100) (tL 562794879123071)) (tN (tL 556300888571516) tE)) (tN (tN (tL 549240367087228) tE) tE))))) (tN (tN (tN (tN (tN (tN tE (tL 499212689477247)) (tN (tL 273162118237756) (tL 560991499062911))) (tN (tN (tL 214465419546172) (tL 500338442767999)) (tN (tL 276521254522428) (tL 562117252353663)))) (tN (tN (tN (tL 248229799267896) (tL 536336239300223)) (tN (tL 274824270581308) (tL 562922086862463))) (tN (tN (tL 250480867806780) (tL 536353888930937)) (tN (tL 277075305303612) tE)))) (tN (tN (tN (tN (tL 211107906555452) (tL 499214312771199)) (tN (tL 273163741498940) (tL 560993122324095))) (tN (tN (tL 213358941277756) (tL 499231863836285)) (tN (tL 275414776221244) tE))) (tN (tN (tN (tL 248231456378428) (tL 536337862594175)) (tN (tL 274825893842492) tE)) (tN (tN (tL 215023241104956) tE) tE)))) (tN (tN (tN (tN (tN (tL 492581261557372) (tL 508077503561343)) (tN (tL 554637096533628) (tL 561268526038655))) (tN (tN (tL 495906038103676) (tL 509203256852092)) (tN (tL 557961873079932) tE))) (tN (tN (tN (tL 529704878489212) (tL 545201120493183)) (tN (tL 556299315986044) tE)) (tN (tN (tL 531921486364284) tE) tE))) (tN (tN (tN (tN (tL 492582884867708) (tL 508079126871679)) (tN (tL 554638719794812) tE)) (tN (tN (tL 494799559851644) tE) tE)) (tN (tN (tN (tL 529706501799548) tE) tE) tE))))) (tN (tN (tN (tN (tN (tN (tN tE (tL 426644871350143)) (tN (tL 264295107577855) (tL 558792425113471))) (tN (tN (tL 213357200197631) (tL 499230223419391)) (tN (tL 275410887690239) (tL 561008896673791)))) (tN (tN (tN (tL 247952757015039) (tL 562447442298879)) (tN (tL 265960481146879) (tL 559624575027071))) (tN (tN (tL 267795910674431) (tL 562465026918399)) (tN (tL 268280705107967) tE)))) (tN (tN (tN (tN (tL 211107855845375) (tL 499214262061055)) (tN (tL 273161543337918) (tL 558759688636415))) (tN (tN (tL 213358823458815) (tL 499231846680575)) (tN (tL 275412510951358) tE))) (tN (tN (tN (tL 265823591712767) (tL 562726090950655)) (tN (tL 274825843165183) tE)) (tN (tN (tL 267799681419263) tE) tE)))) (tN (tN (tN (tN (tN (tL 140737489469439) (tL 426644872429567)) (tN (tL 264295109165055) (tL 453239309920255))) (tN (tN (tL 211123818790911) (tL 428861480796159)) (tN (tL 273177506283519) tE))) (tN (tN (tN (tL 265545011757055) (tL 562447510994943)) (tN (tL 265960549842943) tE)) (tN (tN (tL 265562596376575) tE) tE))) (tN (tN (tN (tN (tL 211107857432575) (tL 428843908857855)) (tN (tL 273161544925118) tE)) (tN (tN (tL 18135777279) tE) tE)) (tN (tN (tN (tL 265823660408831) tE) tE) tE)))) (tN (tN (tN (tN (tN (tN (tL 70368744427519) (tL 499212689592319)) (tN (tL 273162118352895) (tL 558792425574399))) (tN (tN (tL 214465419661311) (tL 500338442883071)) (tN (tL 276521254637567) tE))) (tN (tN (tN (tL 248229799383039) (tL 536336239415295)) (tN (tL 274824270696447) tE)) (tN (tN (tL 250480867921919) tE) tE))) (tN (tN (tN (tN (tL 211107906572287) (tL 496980896239615)) (tN (tL 273163741548478) tE)) (tN (tN (tL 213358941294591) tE) tE)) (tN (tN (tN (tL 248231456395263) tE) tE) tE))) (tN (tN (tN (tN (tN (tL 211106284961791) (tL 499212691177471)) (tN (tL 273162119938047) tE)) (tN (tN (tL 212232038252543) tE) tE)) (tN (tN (tN (tL 248229901893631) tE) tE) tE)) (tN (tN (tN (tN (tL 211107908157439) tE) tE) tE) tE)))))
private def c2Tree2 : Tree10 :=
  tN (tN c2Tree2_00 c2Tree2_01) (tN c2Tree2_10 c2Tree2_11)

private def c1Tree : Fin 3 → Tree10
  | ⟨0, _⟩ => c1Tree0 | ⟨1, _⟩ => c1Tree1 | ⟨2, _⟩ => c1Tree2

private def c2Tree : Fin 3 → Tree10
  | ⟨0, _⟩ => c2Tree0 | ⟨1, _⟩ => c2Tree1 | ⟨2, _⟩ => c2Tree2

private def Tree10.allLt49 : Tree10 → Bool
  | tE => true
  | tL v => Nat.blt v (2 ^ 49)
  | tN l r => l.allLt49 && r.allLt49

private lemma Tree10.getAux_lt49 {t : Tree10} (ht : t.allLt49 = true) (bits : List Nat) (m : Nat) :
    t.getAux bits m < 2 ^ 49 := by
  induction t generalizing bits with
  | tE => simp [Tree10.getAux]
  | tL v => exact Nat.blt_eq.mp ht
  | tN l r ihl ihr =>
    simp only [Tree10.allLt49, Bool.and_eq_true] at ht
    cases bits with
    | nil => simp [Tree10.getAux]
    | cons bit rest =>
      unfold Tree10.getAux
      cases Nat.beq (Nat.land m bit) 0
      · exact ihr ht.2 rest
      · exact ihl ht.1 rest

private theorem c1Tree_lt49_0 : c1Tree0.allLt49 = true := by rfl
private theorem c1Tree_lt49_1 : c1Tree1.allLt49 = true := by rfl
private theorem c1Tree_lt49_2 : c1Tree2.allLt49 = true := by rfl
private theorem c2Tree_lt49_0 : c2Tree0.allLt49 = true := by rfl
private theorem c2Tree_lt49_1 : c2Tree1.allLt49 = true := by rfl
private theorem c2Tree_lt49_2 : c2Tree2.allLt49 = true := by rfl

private lemma c1Tree_get_lt49 (k : Fin 3) (m : Nat) :
    (c1Tree k).getAux (repBits k) m < 2 ^ 49 := by
  have hall : (c1Tree k).allLt49 = true :=
    match k with | ⟨0, _⟩ => c1Tree_lt49_0 | ⟨1, _⟩ => c1Tree_lt49_1 | ⟨2, _⟩ => c1Tree_lt49_2
  exact Tree10.getAux_lt49 hall _ _

private lemma c2Tree_get_lt49 (k : Fin 3) (m : Nat) :
    (c2Tree k).getAux (repBits k) m < 2 ^ 49 := by
  have hall : (c2Tree k).allLt49 = true :=
    match k with | ⟨0, _⟩ => c2Tree_lt49_0 | ⟨1, _⟩ => c2Tree_lt49_1 | ⟨2, _⟩ => c2Tree_lt49_2
  exact Tree10.getAux_lt49 hall _ _

private def checkC2Aux (rK1 : Nat) (tK1 : Tree10) (bK1 : List Nat) (g1 g1Inv : Aut2) (B1 : Nat) :
    Tree10 → List Nat → Nat → Nat → Nat → Bool
  | tE, _, _, _, _ => true
  | tL v, [], sub, _, _ =>
      seqN (g1Inv.applyMask sub) fun subC =>
      seqN (Nat.land rK1 (Nat.xor ALL49 subC)) fun yCanon =>
      seqN (tK1.getAux bK1 yCanon) fun c1Y =>
      seqN (g1.applyMask c1Y) fun img =>
      Nat.beq (Nat.land v img) v
  | tL _, _ :: _, _, _, _ => false
  | tN l r, bit :: rest, sub, sz, rem =>
      match Nat.beq (Nat.land B1 bit) 0 with
      | true =>
          match Nat.blt (Nat.add sz rem) 4 with
          | true => true
          | false => checkC2Aux rK1 tK1 bK1 g1 g1Inv B1 l rest sub sz rem
      | false =>
          let rem1 := Nat.sub rem 1
          let okL := match Nat.blt (Nat.add sz rem1) 4 with
                     | true => true
                     | false => checkC2Aux rK1 tK1 bK1 g1 g1Inv B1 l rest sub sz rem1
          okL && seqN (Nat.lor sub bit) fun s2 => checkC2Aux rK1 tK1 bK1 g1 g1Inv B1 r rest s2 (Nat.add sz 1) rem1
  | tN _ _, [], _, _, _ => false

private lemma checkC2Aux_sound {k1 : Fin 3} {g1 : Aut2} {B1 X : Nat}
    (hX : X < 2 ^ 49) (hXpop4 : 4 ≤ pop49 X) (hXB : subset49 X B1 = true) :
    ∀ (t : Tree10) (pts : List (Fin 7 × Fin 7)) (sub : Nat),
      sub < 2 ^ 49 →
      checkC2Aux (rep k1) (c1Tree k1) (repBits k1) g1 g1.inv B1 t (ptsToBits pts) sub (pop49 sub) (countHits B1 pts) = true →
      (∀ p, get49 X p.1 p.2 = true → get49 sub p.1 p.2 = true ∨ p ∈ pts) →
      (∀ p, get49 sub p.1 p.2 = true → get49 X p.1 p.2 = true ∧ p ∉ pts) →
      pts.Nodup →
      subset49 (t.getAux (ptsToBits pts) X)
        (g1.applyMask ((c1Tree k1).getAux (repBits k1) (diff49 (rep k1) (g1.inv.applyMask X)))) = true := by
  intro t
  induction t with
  | tE => intro _ _ _ _ _ _ _; exact subset49_zero_left _
  | tL v =>
    intro pts sub hsub_lt hchk hcov hsub _
    cases pts with
    | cons _ _ => simp [ptsToBits, checkC2Aux] at hchk
    | nil =>
      simp only [ptsToBits, checkC2Aux, seqN_eq] at hchk
      have hXeq : X = sub := by
        apply ext49 hX hsub_lt
        intro r c
        cases hx : get49 X r c
        · cases hs : get49 sub r c
          · rfl
          · exact absurd (hsub (r, c) hs).1 (by simp [hx])
        · rcases hcov (r, c) hx with hs | hnil
          · exact hs.symm
          · cases hnil
      subst hXeq; exact hchk
  | tN l r ihl ihr =>
    intro pts sub hsub_lt hchk hcov hsub hnd
    cases pts with
    | nil => simp [ptsToBits, checkC2Aux] at hchk
    | cons p rest =>
      rcases p with ⟨row, col⟩
      have ⟨hp_not_rest, hrest_nd⟩ := List.nodup_cons.mp hnd
      simp only [ptsToBits] at hchk ⊢
      unfold checkC2Aux at hchk
      dsimp only at hchk
      rw [land_bit49_eq_zero B1 row col] at hchk
      conv_lhs => arg 1; unfold Tree10.getAux
      rw [land_bit49_eq_zero X row col]
      cases hBp : get49 B1 row col
      · rw [hBp] at hchk
        have hXp : get49 X row col = false := by
          cases hx : get49 X row col
          · rfl
          · exact absurd ((subset49_iff hX).mp hXB row col hx) (by simp [hBp])
        rw [hXp]
        have hcnt : countHits B1 ((row, col) :: rest) = countHits B1 rest := by simp [countHits, hBp]
        have hcov' : ∀ q, get49 X q.1 q.2 = true → get49 sub q.1 q.2 = true ∨ q ∈ rest := by
          intro q hq
          rcases hcov q hq with hs | hmem
          · exact Or.inl hs
          · rcases List.mem_cons.mp hmem with rfl | hr
            · exact absurd hq (by simp [hXp])
            · exact Or.inr hr
        have hsub' : ∀ q, get49 sub q.1 q.2 = true → get49 X q.1 q.2 = true ∧ q ∉ rest := by
          intro q hq; have ⟨h1, h2⟩ := hsub q hq
          exact ⟨h1, fun hr => h2 (List.mem_cons_of_mem _ hr)⟩
        have hge4 : 4 ≤ pop49 sub + countHits B1 rest :=
          hXpop4.trans (pop49_le_add_countHits hX hXB rest hcov')
        have hblt : Nat.blt (pop49 sub + countHits B1 rest) 4 = false := by
          cases h : Nat.blt (pop49 sub + countHits B1 rest) 4
          · rfl
          · exfalso; have := Nat.blt_eq.mp h; omega
        simp only [add_eq, Bool.not_false, hcnt, hblt] at hchk
        exact ihl rest sub hsub_lt hchk hcov' hsub' hrest_nd
      · rw [hBp] at hchk
        have hcnt : countHits B1 ((row, col) :: rest) - 1 = countHits B1 rest := by simp [countHits, hBp]
        simp only [add_eq, sub_eq, Bool.not_true, Bool.and_eq_true, seqN_eq] at hchk
        cases hXp : get49 X row col
        · have hcov' : ∀ q, get49 X q.1 q.2 = true → get49 sub q.1 q.2 = true ∨ q ∈ rest := by
            intro q hq
            rcases hcov q hq with hs | hmem
            · exact Or.inl hs
            · rcases List.mem_cons.mp hmem with rfl | hr
              · exact absurd hq (by simp [hXp])
              · exact Or.inr hr
          have hsub' : ∀ q, get49 sub q.1 q.2 = true → get49 X q.1 q.2 = true ∧ q ∉ rest := by
            intro q hq; have ⟨h1, h2⟩ := hsub q hq
            exact ⟨h1, fun hr => h2 (List.mem_cons_of_mem _ hr)⟩
          have hge4 : 4 ≤ pop49 sub + countHits B1 rest :=
            hXpop4.trans (pop49_le_add_countHits hX hXB rest hcov')
          have hblt : Nat.blt (pop49 sub + countHits B1 rest) 4 = false := by
            cases h : Nat.blt (pop49 sub + countHits B1 rest) 4
            · rfl
            · exfalso; have := Nat.blt_eq.mp h; omega
          have hL := hchk.1
          rw [hcnt, hblt] at hL
          exact ihl rest sub hsub_lt hL hcov' hsub' hrest_nd
        · have hsub_f : get49 sub row col = false := by
            cases hs : get49 sub row col
            · rfl
            · exact absurd (List.mem_cons_self ..) (hsub (row, col) hs).2
          have hpop_set : pop49 (set49 sub row col) = pop49 sub + 1 := pop49_set49_of_false hsub_f
          have hR := hchk.2
          change checkC2Aux (rep k1) (c1Tree k1) (repBits k1) g1 g1.inv B1 r (ptsToBits rest) (set49 sub row col) (pop49 sub + 1) (countHits B1 ((row, col) :: rest) - 1) = true at hR
          rw [← hpop_set, hcnt] at hR
          refine ihr rest (set49 sub row col) (set49_lt hsub_lt row col) hR ?_ ?_ hrest_nd
          · intro q hq
            rcases hcov q hq with hs | hmem
            · left; rw [get49_set]; split <;> [rfl; exact hs]
            · rcases List.mem_cons.mp hmem with rfl | hr
              · left; rw [get49_set]; simp
              · exact Or.inr hr
          · intro q hq
            rw [get49_set] at hq
            split at hq
            · rename_i heq
              rcases q with ⟨qr, qc⟩; dsimp only at heq
              rw [heq.1, heq.2]
              exact ⟨hXp, hp_not_rest⟩
            · have ⟨h1, h2⟩ := hsub q hq
              exact ⟨h1, fun hr => h2 (List.mem_cons_of_mem _ hr)⟩

end TreeOps

private def checkC1Pair (k k0 : Fin 3) (half : Bool) : Bool :=
  let tK := c1Tree k
  let bK := repBits k
  let rK := rep k
  forAllAut2 k0 half fun _ B =>
    seqN (pop49 (Nat.land B rK)) fun ov =>
    match Nat.blt ov 4 with
    | true => true
    | false => tK.checkC1 B bK 0 0 ov

private def checkC2Pair (k k0 : Fin 3) (half : Bool) : Bool :=
  let rK0 := rep k0
  let tK0 := c1Tree k0
  let bK0 := repBits k0
  let tK  := c2Tree k
  let bK  := repBits k
  let rK  := rep k
  forAllAut2 k0 half fun g1 B1 =>
    seqN (pop49 (Nat.land B1 rK)) fun ov =>
    match Nat.blt ov 4 with
    | true => true
    | false =>
        match g1.inv with
        | g1Inv => checkC2Aux rK0 tK0 bK0 g1 g1Inv B1 tK bK 0 0 ov

private theorem checkC1_00 : checkC1Pair 0 0 false = true := by rfl
private theorem checkC1_01 : checkC1Pair 0 1 false = true := by rfl
private theorem checkC1_02 : checkC1Pair 0 2 true  = true := by rfl
private theorem checkC1_10 : checkC1Pair 1 0 false = true := by rfl
private theorem checkC1_11 : checkC1Pair 1 1 false = true := by rfl
private theorem checkC1_12 : checkC1Pair 1 2 true  = true := by rfl
private theorem checkC1_20 : checkC1Pair 2 0 false = true := by rfl
private theorem checkC1_21 : checkC1Pair 2 1 false = true := by rfl
private theorem checkC1_22 : checkC1Pair 2 2 true  = true := by rfl

private theorem checkC2_00 : checkC2Pair 0 0 false = true := by rfl
private theorem checkC2_01 : checkC2Pair 0 1 false = true := by rfl
private theorem checkC2_02 : checkC2Pair 0 2 true  = true := by rfl
private theorem checkC2_10 : checkC2Pair 1 0 false = true := by rfl
private theorem checkC2_11 : checkC2Pair 1 1 false = true := by rfl
private theorem checkC2_12 : checkC2Pair 1 2 true  = true := by rfl
private theorem checkC2_20 : checkC2Pair 2 0 false = true := by rfl
private theorem checkC2_21 : checkC2Pair 2 1 false = true := by rfl
private theorem checkC2_22 : checkC2Pair 2 2 true  = true := by rfl

private lemma checkC1Pair_all (k k0 : Fin 3) : checkC1Pair k k0 (k0 == 2) = true := by
  revert k k0
  exact fin3_cases
    (fin3_cases checkC1_00 checkC1_01 checkC1_02)
    (fin3_cases checkC1_10 checkC1_11 checkC1_12)
    (fin3_cases checkC1_20 checkC1_21 checkC1_22)

private lemma checkC2Pair_all (k k0 : Fin 3) : checkC2Pair k k0 (k0 == 2) = true := by
  revert k k0
  exact fin3_cases
    (fin3_cases checkC2_00 checkC2_01 checkC2_02)
    (fin3_cases checkC2_10 checkC2_11 checkC2_12)
    (fin3_cases checkC2_20 checkC2_21 checkC2_22)

private lemma c1Tree_sound {k : Fin 3} {X : Nat} {B : Finset (ZMod 7 × ZMod 7)}
    (hX : X < 2 ^ 49) (hXrep : subset49 X (rep k) = true) (hXpop : 4 ≤ pop49 X)
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) (hBcard : B.card = 10)
    (hXB : subset49 X (ofFinset49 B) = true) :
    subset49 ((c1Tree k).getAux (repBits k) X) (closedNbr49 (diff49 (ofFinset49 B) X)) = true := by
  obtain ⟨kB, gB, hsr, hBeq⟩ := tenSet_canon_half hB hBcard
  have hsr' : (kB == 2) = false ∨ gB.sr = false := by
    rcases hsr with hne | h0
    · left; exact beq_false_of_ne hne
    · exact Or.inr h0
  have hpair := checkC1Pair_all k kB
  unfold checkC1Pair at hpair
  dsimp only at hpair
  have hall := forAllAut2_sound hpair gB hsr'
  simp only [seqN_eq, land_eq] at hall
  rw [← hBeq] at hall
  have hpop4 : 4 ≤ pop49 (ofFinset49 B &&& rep k) := by
    have hsub : subset49 X (ofFinset49 B &&& rep k) = true := by
      rw [subset49_iff hX] at hXB hXrep ⊢
      intro r c hx; rw [get49_and, hXB r c hx, hXrep r c hx]; rfl
    exact hXpop.trans (subset49_pop_le hX hsub)
  have hblt : Nat.blt (pop49 (ofFinset49 B &&& rep k)) 4 = false := by
    cases h : Nat.blt (pop49 (ofFinset49 B &&& rep k)) 4
    · rfl
    · exfalso; have := Nat.blt_eq.mp h; omega
  rw [hblt] at hall
  dsimp only at hall
  have hpop0 : pop49 0 = 0 := by decide
  have hall' : (c1Tree k).checkC1 (ofFinset49 B) (ptsToBits (repPtsList k)) 0 (pop49 0)
      (countHits (ofFinset49 B) (repPtsList k)) = true := by
    have heq : (c1Tree k).checkC1 (ofFinset49 B) (ptsToBits (repPtsList k)) 0 (pop49 0)
        (countHits (ofFinset49 B) (repPtsList k)) =
      (c1Tree k).checkC1 (ofFinset49 B) (repBits k) 0 0 (pop49 (ofFinset49 B &&& rep k)) := by
      rw [← repBits_eq k, hpop0, countHits_repPtsList k (ofFinset49 B)]
    rw [heq]; exact hall
  rw [repBits_eq]
  refine Tree10.checkC1_sound hX hXpop hXB (c1Tree k) (repPtsList k) 0 (by decide) hall' ?_ ?_ (repPtsList_nodup k)
  · intro p hp
    exact Or.inr ((rep_mem_iff k p.1 p.2).mp ((subset49_iff hX).mp hXrep p.1 p.2 hp))
  · intro p hp; rw [get49_zero] at hp; exact absurd hp (by decide)

private lemma c1Tree_equivariant {k : Fin 3} {g : Aut2} {X : Nat}
    {B : Finset (ZMod 7 × ZMod 7)}
    (hX : X < 2 ^ 49) (hXrep : subset49 X (rep k) = true) (hXpop : 4 ≤ pop49 X)
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) (hBcard : B.card = 10)
    (hXB : subset49 (g.applyMask X) (ofFinset49 B) = true) :
    subset49 (g.applyMask ((c1Tree k).getAux (repBits k) X))
      (closedNbr49 (diff49 (ofFinset49 B) (g.applyMask X))) = true := by
  let B' := B.map g.inv.toIso.toEquiv.toEmbedding
  have hB' : (C7 ⊠ C7).IsIndepSet (B' : Set (ZMod 7 × ZMod 7)) := isIndepSet_map_iso' g.inv.toIso hB
  have hB'card : B'.card = 10 := by rw [Finset.card_map, hBcard]
  have hB'mask : ofFinset49 B' = g.inv.applyMask (ofFinset49 B) := (Aut2.applyMask_ofFinset g.inv B).symm
  have hXB' : subset49 X (ofFinset49 B') = true := by
    rw [hB'mask, ← Aut2.applyMask_inv_left g hX]
    exact Aut2.applyMask_subset (g.applyMask_lt hX) hXB
  have hsub := c1Tree_sound hX hXrep hXpop hB' hB'card hXB'
  have hsub2 := Aut2.applyMask_subset (g := g) (c1Tree_get_lt49 k X) hsub
  rw [Aut2.applyMask_closedNbr g (diff49_lt (ofFinset49_lt _)),
      Aut2.applyMask_diff g (ofFinset49_lt _),
      hB'mask, Aut2.applyMask_inv_right g (ofFinset49_lt _)] at hsub2
  exact hsub2

private lemma pop49_applyMask (g : Aut2) (m : Nat) : pop49 (g.applyMask m) = pop49 m := by
  rw [pop49_eq_sum, pop49_eq_sum, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let e : (Fin 7 × Fin 7) ≃ (Fin 7 × Fin 7) := Equiv.mk g.applyFin g.inv.applyFin g.inv_applyFin g.applyFin_inv
  rw [← Equiv.sum_comp e (fun p => (get49 (g.applyMask m) p.1 p.2).toNat)]
  refine Finset.sum_congr rfl fun ⟨r, c⟩ _ => by simp [e, Aut2.get_applyMask]

private lemma c2Tree_sound {k : Fin 3} {X : Nat}
    {B1 B0 : Finset (ZMod 7 × ZMod 7)}
    (hX : X < 2 ^ 49) (hXrep : subset49 X (rep k) = true) (hXpop : 4 ≤ pop49 X) (hXle6 : pop49 X ≤ 6)
    (hB1 : (C7 ⊠ C7).IsIndepSet (B1 : Set (ZMod 7 × ZMod 7))) (hB1card : B1.card = 10)
    (hXB1 : subset49 X (ofFinset49 B1) = true)
    (hB0 : (C7 ⊠ C7).IsIndepSet (B0 : Set (ZMod 7 × ZMod 7))) (hB0card : B0.card = 10)
    (hYB0 : subset49 (diff49 (ofFinset49 B1) X) (ofFinset49 B0) = true) :
    subset49 ((c2Tree k).getAux (repBits k) X)
      (closedNbr49 (diff49 (ofFinset49 B0) (diff49 (ofFinset49 B1) X))) = true := by
  obtain ⟨k1, g1, hsr1, hB1eq⟩ := tenSet_canon_half hB1 hB1card
  have hsr1' : (k1 == 2) = false ∨ g1.sr = false := by
    rcases hsr1 with hne | h0
    · left; exact beq_false_of_ne hne
    · exact Or.inr h0
  have hpair := checkC2Pair_all k k1
  unfold checkC2Pair at hpair
  dsimp only at hpair
  have hall := forAllAut2_sound hpair g1 hsr1'
  simp only [seqN_eq, land_eq] at hall
  rw [← hB1eq] at hall
  have hpop4 : 4 ≤ pop49 (ofFinset49 B1 &&& rep k) := by
    have hsub : subset49 X (ofFinset49 B1 &&& rep k) = true := by
      rw [subset49_iff hX] at hXB1 hXrep ⊢
      intro r c hx; rw [get49_and, hXB1 r c hx, hXrep r c hx]; rfl
    exact hXpop.trans (subset49_pop_le hX hsub)
  have hblt : Nat.blt (pop49 (ofFinset49 B1 &&& rep k)) 4 = false := by
    cases h : Nat.blt (pop49 (ofFinset49 B1 &&& rep k)) 4
    · rfl
    · exfalso; have := Nat.blt_eq.mp h; omega
  rw [hblt] at hall
  dsimp only at hall
  have hpop0 : pop49 0 = 0 := by decide
  have hall' : checkC2Aux (rep k1) (c1Tree k1) (repBits k1) g1 g1.inv (ofFinset49 B1)
      (c2Tree k) (ptsToBits (repPtsList k)) 0 (pop49 0)
      (countHits (ofFinset49 B1) (repPtsList k)) = true := by
    have heq : checkC2Aux (rep k1) (c1Tree k1) (repBits k1) g1 g1.inv (ofFinset49 B1)
        (c2Tree k) (ptsToBits (repPtsList k)) 0 (pop49 0)
        (countHits (ofFinset49 B1) (repPtsList k)) =
      checkC2Aux (rep k1) (c1Tree k1) (repBits k1) g1 g1.inv (ofFinset49 B1)
        (c2Tree k) (repBits k) 0 0 (pop49 (ofFinset49 B1 &&& rep k)) := by
      rw [← repBits_eq k, hpop0, countHits_repPtsList k (ofFinset49 B1)]
    rw [heq]; exact hall
  have hstep1 := checkC2Aux_sound hX hXpop hXB1 (c2Tree k) (repPtsList k) 0 (by decide) hall'
    (fun p hp => Or.inr ((rep_mem_iff k p.1 p.2).mp ((subset49_iff hX).mp hXrep p.1 p.2 hp)))
    (fun p hp => by rw [get49_zero] at hp; exact absurd hp (by decide))
    (repPtsList_nodup k)
  rw [← repBits_eq k] at hstep1
  let yCanon := diff49 (rep k1) (g1.inv.applyMask X)
  have hyLt : yCanon < 2 ^ 49 := diff49_lt (rep_lt k1)
  have hyImg : g1.applyMask yCanon = diff49 (ofFinset49 B1) X := by
    rw [Aut2.applyMask_diff g1 (rep_lt k1), ← hB1eq,
        Aut2.applyMask_inv_right g1 hX]
  have hyRep : subset49 yCanon (rep k1) = true := by
    rw [subset49_iff hyLt]; intro r c h
    rw [get49_diff] at h; exact (Bool.and_eq_true _ _ |>.mp h).1
  have hyPop : 4 ≤ pop49 yCanon := by
    have hsum : pop49 (diff49 (ofFinset49 B1) X) + pop49 X = pop49 (ofFinset49 B1) := by
      rw [pop49_eq_sum, pop49_eq_sum, pop49_eq_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [get49_diff]
      cases hx : get49 X r c
      · simp
      · have hbx := (subset49_iff hX).mp hXB1 r c hx
        simp [hbx]
    have hpopB1 : pop49 (ofFinset49 B1) = 10 := by rw [pop49_ofFinset, hB1card]
    have hyEq : pop49 yCanon = pop49 (diff49 (ofFinset49 B1) X) := by
      rw [← pop49_applyMask g1, hyImg]
    omega
  have hstep2 := c1Tree_equivariant (g := g1) hyLt hyRep hyPop hB0 hB0card (by rw [hyImg]; exact hYB0)
  rw [hyImg] at hstep2
  exact subset49_trans (c2Tree_get_lt49 k X) (g1.applyMask_lt (c1Tree_get_lt49 k1 yCanon)) hstep1 hstep2

/-! ## Section 5: Leaf Certificate Soundness (3-Square Cover, 2D & 3D `Grid49` Farkas Duals) -/

private def sq22 (idx : Fin 49) : Nat :=
  match idx.val with
  | 0 => 387
  | 1 => 774
  | 2 => 1548
  | 3 => 3096
  | 4 => 6192
  | 5 => 12384
  | 6 => 8385
  | 7 => 49536
  | 8 => 99072
  | 9 => 198144
  | 10 => 396288
  | 11 => 792576
  | 12 => 1585152
  | 13 => 1073280
  | 14 => 6340608
  | 15 => 12681216
  | 16 => 25362432
  | 17 => 50724864
  | 18 => 101449728
  | 19 => 202899456
  | 20 => 137379840
  | 21 => 811597824
  | 22 => 1623195648
  | 23 => 3246391296
  | 24 => 6492782592
  | 25 => 12985565184
  | 26 => 25971130368
  | 27 => 17584619520
  | 28 => 103884521472
  | 29 => 207769042944
  | 30 => 415538085888
  | 31 => 831076171776
  | 32 => 1662152343552
  | 33 => 3324304687104
  | 34 => 2250831298560
  | 35 => 13297218748416
  | 36 => 26594437496832
  | 37 => 53188874993664
  | 38 => 106377749987328
  | 39 => 212755499974656
  | 40 => 425510999949312
  | 41 => 288106406215680
  | 42 => 13194139533315
  | 43 => 26388279066630
  | 44 => 52776558133260
  | 45 => 105553116266520
  | 46 => 211106232533040
  | 47 => 422212465066080
  | _ => 285873023221825

private lemma sq22_lt (idx : Fin 49) : sq22 idx < 2 ^ 49 := by revert idx; decide

private lemma sq22_get_imp : ∀ (idx : Fin 49) (r' c' : Fin 7),
    get49 (sq22 idx) r' c' = true →
      let r : Fin 7 := ⟨idx.val / 7, Nat.div_lt_of_lt_mul idx.isLt⟩
      let c : Fin 7 := ⟨idx.val % 7, Nat.mod_lt _ (by decide)⟩
      (r' = r ∨ r' = next7 r) ∧ (c' = c ∨ c' = next7 c) := by decide

private lemma sq22_card_le_one (idx : Fin 49) {S : Finset (ZMod 7 × ZMod 7)}
    (hS : (C7 ⊠ C7).IsIndepSet (S : Set (ZMod 7 × ZMod 7))) :
    pop49 (ofFinset49 S &&& sq22 idx) ≤ 1 := by
  let r : Fin 7 := ⟨idx.val / 7, Nat.div_lt_of_lt_mul idx.isLt⟩
  let c : Fin 7 := ⟨idx.val % 7, Nat.mod_lt _ (by decide)⟩
  have hsq := sq22_get_imp idx
  let T := S.filter fun p => get49 (sq22 idx) (ofZ7 p.1) (ofZ7 p.2) = true
  have hpop : pop49 (ofFinset49 S &&& sq22 idx) = T.card := by
    rw [← pop49_ofFinset T]
    congr 1
    apply ext49 (and_lt49 (sq22_lt idx)) (ofFinset49_lt T)
    intro r' c'
    rw [get49_and]
    by_cases h1 : (toZ7 r', toZ7 c') ∈ S <;> by_cases h2 : get49 (sq22 idx) r' c' = true
    · have ht : (toZ7 r', toZ7 c') ∈ T := Finset.mem_filter.mpr ⟨h1, by simpa [ofZ7_toZ7] using h2⟩
      simp [(get49_ofFinset S r' c').mpr h1, h2, (get49_ofFinset T r' c').mpr ht]
    · have h2f : get49 (sq22 idx) r' c' = false := Bool.eq_false_iff.mpr h2
      have hnt : (toZ7 r', toZ7 c') ∉ T := by simp [T, ofZ7_toZ7, h2f]
      have htf : get49 (ofFinset49 T) r' c' = false := Bool.eq_false_iff.mpr fun ht => hnt ((get49_ofFinset T r' c').mp ht)
      simp [h2f, htf]
    · have h1f : get49 (ofFinset49 S) r' c' = false := Bool.eq_false_iff.mpr fun hs => h1 ((get49_ofFinset S r' c').mp hs)
      have hnt : (toZ7 r', toZ7 c') ∉ T := by simp [T, h1]
      have htf : get49 (ofFinset49 T) r' c' = false := Bool.eq_false_iff.mpr fun ht => hnt ((get49_ofFinset T r' c').mp ht)
      simp [h1f, htf]
    · have h1f : get49 (ofFinset49 S) r' c' = false := Bool.eq_false_iff.mpr fun hs => h1 ((get49_ofFinset S r' c').mp hs)
      have hnt : (toZ7 r', toZ7 c') ∉ T := by simp [T, h1]
      have htf : get49 (ofFinset49 T) r' c' = false := Bool.eq_false_iff.mpr fun ht => hnt ((get49_ofFinset T r' c').mp ht)
      simp [h1f, htf]
  rw [hpop]
  refine Finset.card_le_one.mpr fun p hp q hq => ?_
  by_contra hpq
  have ⟨hpS, hpsq⟩ := Finset.mem_filter.mp hp
  have ⟨hqS, hqsq⟩ := Finset.mem_filter.mp hq
  have ⟨hpr, hpc⟩ := hsq (ofZ7 p.1) (ofZ7 p.2) hpsq
  have ⟨hqr, hqc⟩ := hsq (ofZ7 q.1) (ofZ7 q.2) hqsq
  have hclose : ∀ {x y a : Fin 7}, (x = a ∨ x = next7 a) → (y = a ∨ y = next7 a) →
      toZ7 x = toZ7 y ∨ C7.Adj (toZ7 x) (toZ7 y) := by
    intro x y a hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl rfl
    · right; rw [toZ7_next7]; exact c7_adj_add_one _
    · right; rw [toZ7_next7]; exact (c7_adj_add_one _).symm
    · exact Or.inl rfl
  have hr_adj := hclose hpr hqr
  have hc_adj := hclose hpc hqc
  rw [toZ7_ofZ7, toZ7_ofZ7] at hr_adj hc_adj
  exact hS hpS hqS hpq ⟨hpq, hr_adj, hc_adj⟩

private def checkAvailSq3 (avail : Nat) (a b c : Fin 49) : Bool :=
  subset49 avail (Nat.lor (Nat.lor (sq22 a) (sq22 b)) (sq22 c))

private lemma card_le_three_of_sq3_cover {S : Finset (ZMod 7 × ZMod 7)} {avail : Nat}
    {a b c : Fin 49} (hS : (C7 ⊠ C7).IsIndepSet (S : Set (ZMod 7 × ZMod 7)))
    (hsub : subset49 (ofFinset49 S) avail = true) (hcov : checkAvailSq3 avail a b c = true)
    (hav : avail < 2 ^ 49) : S.card ≤ 3 := by
  have hSa := sq22_card_le_one a hS
  have hSb := sq22_card_le_one b hS
  have hSc := sq22_card_le_one c hS
  have hcovS : subset49 (ofFinset49 S) ((sq22 a ||| sq22 b) ||| sq22 c) = true :=
    subset49_trans (ofFinset49_lt S) hav hsub hcov
  rw [subset49_iff (ofFinset49_lt S)] at hcovS
  have hle : pop49 (ofFinset49 S) ≤
      pop49 (ofFinset49 S &&& sq22 a) + pop49 (ofFinset49 S &&& sq22 b) + pop49 (ofFinset49 S &&& sq22 c) := by
    rw [pop49_eq_sum, pop49_eq_sum, pop49_eq_sum, pop49_eq_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun col _ => ?_
    rw [get49_and, get49_and, get49_and]
    cases hs : get49 (ofFinset49 S) r col
    · simp
    · have h3 := hcovS r col hs
      rw [get49_or, get49_or, Bool.or_eq_true, Bool.or_eq_true] at h3
      rcases h3 with (h | h) | h <;> simp [h] <;> omega
  rw [pop49_ofFinset] at hle
  omega

private structure Row7N where
  n0 : Nat
  n1 : Nat
  n2 : Nat
  n3 : Nat
  n4 : Nat
  n5 : Nat
  n6 : Nat

private def Row7N.zero : Row7N := ⟨0, 0, 0, 0, 0, 0, 0⟩
private def Row7N.get (r : Row7N) (c : Fin 7) : Nat :=
  match c.val with | 0 => r.n0 | 1 => r.n1 | 2 => r.n2 | 3 => r.n3 | 4 => r.n4 | 5 => r.n5 | _ => r.n6
private def Row7N.addAll (w : Nat) (r : Row7N) : Row7N :=
  ⟨r.n0+w, r.n1+w, r.n2+w, r.n3+w, r.n4+w, r.n5+w, r.n6+w⟩
private def Row7N.addPair (c : Fin 7) (w : Nat) (r : Row7N) : Row7N :=
  match c.val with
  | 0 => ⟨r.n0+w, r.n1+w, r.n2, r.n3, r.n4, r.n5, r.n6⟩
  | 1 => ⟨r.n0, r.n1+w, r.n2+w, r.n3, r.n4, r.n5, r.n6⟩
  | 2 => ⟨r.n0, r.n1, r.n2+w, r.n3+w, r.n4, r.n5, r.n6⟩
  | 3 => ⟨r.n0, r.n1, r.n2, r.n3+w, r.n4+w, r.n5, r.n6⟩
  | 4 => ⟨r.n0, r.n1, r.n2, r.n3, r.n4+w, r.n5+w, r.n6⟩
  | 5 => ⟨r.n0, r.n1, r.n2, r.n3, r.n4, r.n5+w, r.n6+w⟩
  | _ => ⟨r.n0+w, r.n1, r.n2, r.n3, r.n4, r.n5, r.n6+w⟩
private def Row7N.add (a b : Row7N) : Row7N :=
  ⟨a.n0+b.n0, a.n1+b.n1, a.n2+b.n2, a.n3+b.n3, a.n4+b.n4, a.n5+b.n5, a.n6+b.n6⟩
private def Row7N.geMask (r : Row7N) (fr : Nat) (D : Nat) : Bool :=
  (!Nat.beq (Nat.land fr 1) 0  || Nat.ble D r.n0) &&
  (!Nat.beq (Nat.land fr 2) 0  || Nat.ble D r.n1) &&
  (!Nat.beq (Nat.land fr 4) 0  || Nat.ble D r.n2) &&
  (!Nat.beq (Nat.land fr 8) 0  || Nat.ble D r.n3) &&
  (!Nat.beq (Nat.land fr 16) 0 || Nat.ble D r.n4) &&
  (!Nat.beq (Nat.land fr 32) 0 || Nat.ble D r.n5) &&
  (!Nat.beq (Nat.land fr 64) 0 || Nat.ble D r.n6)

private structure Grid49 where
  r0 : Row7N
  r1 : Row7N
  r2 : Row7N
  r3 : Row7N
  r4 : Row7N
  r5 : Row7N
  r6 : Row7N

private def Grid49.zero : Grid49 :=
  ⟨Row7N.zero, Row7N.zero, Row7N.zero, Row7N.zero, Row7N.zero, Row7N.zero, Row7N.zero⟩
private def Grid49.row (g : Grid49) (r : Fin 7) : Row7N :=
  match r.val with | 0 => g.r0 | 1 => g.r1 | 2 => g.r2 | 3 => g.r3 | 4 => g.r4 | 5 => g.r5 | _ => g.r6
private def Grid49.get (g : Grid49) (r c : Fin 7) : Nat := (g.row r).get c
private def Grid49.add (a b : Grid49) : Grid49 :=
  ⟨a.r0.add b.r0, a.r1.add b.r1, a.r2.add b.r2, a.r3.add b.r3, a.r4.add b.r4, a.r5.add b.r5, a.r6.add b.r6⟩
private def Grid49.addRowPair (r : Fin 7) (f : Row7N → Row7N) (g : Grid49) : Grid49 :=
  match r.val with
  | 0 => ⟨f g.r0, f g.r1, g.r2, g.r3, g.r4, g.r5, g.r6⟩
  | 1 => ⟨g.r0, f g.r1, f g.r2, g.r3, g.r4, g.r5, g.r6⟩
  | 2 => ⟨g.r0, g.r1, f g.r2, f g.r3, g.r4, g.r5, g.r6⟩
  | 3 => ⟨g.r0, g.r1, g.r2, f g.r3, f g.r4, g.r5, g.r6⟩
  | 4 => ⟨g.r0, g.r1, g.r2, g.r3, f g.r4, f g.r5, g.r6⟩
  | 5 => ⟨g.r0, g.r1, g.r2, g.r3, g.r4, f g.r5, f g.r6⟩
  | _ => ⟨f g.r0, g.r1, g.r2, g.r3, g.r4, g.r5, f g.r6⟩
private def Grid49.mapRows (f : Row7N → Row7N) (g : Grid49) : Grid49 :=
  ⟨f g.r0, f g.r1, f g.r2, f g.r3, f g.r4, f g.r5, f g.r6⟩
private def Grid49.geMask (g : Grid49) (F : Nat) (D : Nat) : Bool :=
  g.r0.geMask (Nat.land F 127) D &&
  g.r1.geMask (Nat.land (Nat.shiftRight F 7) 127) D &&
  g.r2.geMask (Nat.land (Nat.shiftRight F 14) 127) D &&
  g.r3.geMask (Nat.land (Nat.shiftRight F 21) 127) D &&
  g.r4.geMask (Nat.land (Nat.shiftRight F 28) 127) D &&
  g.r5.geMask (Nat.land (Nat.shiftRight F 35) 127) D &&
  g.r6.geMask (Nat.land (Nat.shiftRight F 42) 127) D

private inductive Constr2D where
  | sq (r c : Fin 7)
  | row (r : Fin 7)
  | col (c : Fin 7)
  | all

private abbrev cS := Constr2D.sq
private abbrev cR := Constr2D.row
private abbrev cC := Constr2D.col
private abbrev cA := Constr2D.all

private def Constr2D.rhs : Constr2D → Nat
  | .sq _ _ => 1 | .row _ => 3 | .col _ => 3 | .all => 10

private def Constr2D.mem : Constr2D → Fin 7 → Fin 7 → Bool
  | .sq r c, r0, c0 => (r0 == r || r0 == next7 r) && (c0 == c || c0 == next7 c)
  | .row r, r0, _ => r0 == r || r0 == next7 r
  | .col c, _, c0 => c0 == c || c0 == next7 c
  | .all, _, _ => true

private def Grid49.addConstr (ct : Constr2D) (w : Nat) (g : Grid49) : Grid49 :=
  match ct with
  | .sq r c => g.addRowPair r (Row7N.addPair c w)
  | .row r => g.addRowPair r (Row7N.addAll w)
  | .col c => g.mapRows (Row7N.addPair c w)
  | .all => g.mapRows (Row7N.addAll w)

private def accumGrid : List (Constr2D × Nat) → Grid49
  | [] => Grid49.zero
  | (ct, w) :: rest => (accumGrid rest).addConstr ct w

private def rhsSum : List (Constr2D × Nat) → Nat
  | [] => 0
  | (ct, w) :: rest => w * ct.rhs + rhsSum rest

private def checkFarkas2D (F : Nat) (cert : Nat × List (Constr2D × Nat)) : Bool :=
  let (D, terms) := cert
  Nat.blt 0 D && Nat.blt (rhsSum terms) (10 * D) && (accumGrid terms).geMask F D

private def checkFarkas3D (CR CL : Nat)
    (cert : Nat × List (Constr2D × Nat) × List (Constr2D × Nat)) : Bool :=
  let (D, t0, t1) := cert
  let g0 := accumGrid t0
  let g1 := accumGrid t1
  let gMid := g0.add g1
  Nat.blt 0 D && Nat.blt (rhsSum t0 + rhsSum t1) (14 * D) &&
  g0.geMask CR D && gMid.geMask 0 D && g1.geMask CL D

private lemma Row7N.get_zero : ∀ c : Fin 7, Row7N.zero.get c = 0
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl
private lemma Row7N.get_addAll (w : Nat) (row : Row7N) : ∀ c : Fin 7,
    (row.addAll w).get c = row.get c + w
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl
private lemma Row7N.get_add (a b : Row7N) : ∀ c : Fin 7, (a.add b).get c = a.get c + b.get c
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl

private lemma Row7N.get_addPair (c : Fin 7) (w : Nat) (row : Row7N) (c0 : Fin 7) :
    (row.addPair c w).get c0 = row.get c0 + if (c0 == c || c0 == next7 c) then w else 0 := by
  revert c c0
  exact fin7_cases
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl) (fin7_cases rfl rfl rfl rfl rfl rfl rfl)
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl) (fin7_cases rfl rfl rfl rfl rfl rfl rfl)
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl) (fin7_cases rfl rfl rfl rfl rfl rfl rfl)
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl)

private lemma Grid49.get_zero : ∀ r c : Fin 7, Grid49.zero.get r c = 0
  | ⟨0, _⟩, c | ⟨1, _⟩, c | ⟨2, _⟩, c | ⟨3, _⟩, c | ⟨4, _⟩, c | ⟨5, _⟩, c | ⟨6, _⟩, c => Row7N.get_zero c

private lemma Grid49.get_add (a b : Grid49) : ∀ r c : Fin 7,
    (a.add b).get r c = a.get r c + b.get r c
  | ⟨0, _⟩, c | ⟨1, _⟩, c | ⟨2, _⟩, c | ⟨3, _⟩, c | ⟨4, _⟩, c | ⟨5, _⟩, c | ⟨6, _⟩, c => Row7N.get_add _ _ c

private lemma Grid49.row_addRowPair (f : Row7N → Row7N) (g : Grid49) (r r0 : Fin 7) :
    (g.addRowPair r f).row r0 = if (r0 == r || r0 == next7 r) then f (g.row r0) else g.row r0 := by
  revert r r0
  exact fin7_cases
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl) (fin7_cases rfl rfl rfl rfl rfl rfl rfl)
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl) (fin7_cases rfl rfl rfl rfl rfl rfl rfl)
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl) (fin7_cases rfl rfl rfl rfl rfl rfl rfl)
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl)

private lemma Grid49.get_addRowPair (r : Fin 7) (f : Row7N → Row7N) (g : Grid49) (r0 c0 : Fin 7) :
    (g.addRowPair r f).get r0 c0 =
      if (r0 == r || r0 == next7 r) then (f (g.row r0)).get c0 else g.get r0 c0 := by
  simp only [Grid49.get, Grid49.row_addRowPair]
  cases (r0 == r || r0 == next7 r) <;> rfl

private lemma Grid49.get_mapRows (f : Row7N → Row7N) (g : Grid49) : ∀ r0 c0 : Fin 7,
    (g.mapRows f).get r0 c0 = (f (g.row r0)).get c0
  | ⟨0, _⟩, _ | ⟨1, _⟩, _ | ⟨2, _⟩, _ | ⟨3, _⟩, _ | ⟨4, _⟩, _ | ⟨5, _⟩, _ | ⟨6, _⟩, _ => rfl

private lemma Grid49.get_addConstr (ct : Constr2D) (w : Nat) (g : Grid49) (r0 c0 : Fin 7) :
    (g.addConstr ct w).get r0 c0 = g.get r0 c0 + if ct.mem r0 c0 then w else 0 := by
  cases ct with
  | sq r c =>
    rw [Grid49.addConstr, Grid49.get_addRowPair, Row7N.get_addPair, Constr2D.mem]
    change (if (r0 == r || r0 == next7 r) = true then g.get r0 c0 + (if (c0 == c || c0 == next7 c) = true then w else 0) else g.get r0 c0) = _
    cases (r0 == r || r0 == next7 r) <;> cases (c0 == c || c0 == next7 c) <;> simp
  | row r =>
    rw [Grid49.addConstr, Grid49.get_addRowPair, Row7N.get_addAll, Constr2D.mem]
    change (if (r0 == r || r0 == next7 r) = true then g.get r0 c0 + w else g.get r0 c0) = _
    cases (r0 == r || r0 == next7 r) <;> simp
  | col c => rw [Grid49.addConstr, Grid49.get_mapRows, Row7N.get_addPair, Constr2D.mem]; rfl
  | all => rw [Grid49.addConstr, Grid49.get_mapRows, Row7N.get_addAll, Constr2D.mem]; rfl

private lemma Grid49.geMask_sound {g : Grid49} {F : Nat} {D : Nat}
    (h : g.geMask F D = true) (r c : Fin 7) (hF : get49 F r c = false) :
    D ≤ g.get r c := by
  have hbit7 : ∀ (x : Nat) (k : Fin 7), x < 128 →
      (!((x &&& (1 <<< k.val)) == 0)) = x.testBit k.val := by
    intro x k hx
    have hall : ∀ (y : Fin 128) (j : Fin 7), (!((y.val &&& (1 <<< j.val)) == 0)) = y.val.testBit j.val := by
      decide
    exact hall ⟨x, hx⟩ k
  have hrow : ∀ (row : Row7N) (fr : Nat), fr < 128 → row.geMask fr D = true →
      ∀ col : Fin 7, fr.testBit col.val = false → D ≤ row.get col := by
    intro row fr hfr hrg
    cases row
    unfold Row7N.geMask at hrg
    simp only [beq_eq, land_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at hrg
    have step : ∀ {k : Fin 7} {n : Nat},
        ((!((fr &&& (1 <<< k.val)) == 0)) = true ∨ D ≤ n) → fr.testBit k.val = false → D ≤ n := by
      intro k n h1 h2
      rw [hbit7 fr k hfr, h2] at h1
      exact h1.resolve_left (by decide)
    exact fun
      | ⟨0, _⟩ => step (k := 0) hrg.1.1.1.1.1.1 | ⟨1, _⟩ => step (k := 1) hrg.1.1.1.1.1.2
      | ⟨2, _⟩ => step (k := 2) hrg.1.1.1.1.2   | ⟨3, _⟩ => step (k := 3) hrg.1.1.1.2
      | ⟨4, _⟩ => step (k := 4) hrg.1.1.2       | ⟨5, _⟩ => step (k := 5) hrg.1.2
      | ⟨6, _⟩ => step (k := 6) hrg.2
  cases g
  unfold Grid49.geMask at h
  simp only [Bool.and_eq_true] at h
  have hF' : (row49 F r).testBit c.val = false := by rw [row49_testBit]; exact hF
  clear hF
  revert r hF'
  exact fun
    | ⟨0, _⟩ => hrow _ (row49 F 0) (row49_lt F 0) h.1.1.1.1.1.1 c
    | ⟨1, _⟩ => hrow _ (row49 F 1) (row49_lt F 1) h.1.1.1.1.1.2 c
    | ⟨2, _⟩ => hrow _ (row49 F 2) (row49_lt F 2) h.1.1.1.1.2 c
    | ⟨3, _⟩ => hrow _ (row49 F 3) (row49_lt F 3) h.1.1.1.2 c
    | ⟨4, _⟩ => hrow _ (row49 F 4) (row49_lt F 4) h.1.1.2 c
    | ⟨5, _⟩ => hrow _ (row49 F 5) (row49_lt F 5) h.1.2 c
    | ⟨6, _⟩ => hrow _ (row49 F 6) (row49_lt F 6) h.2 c

private lemma constr2D_sq_eq : ∀ r c r0 c0 : Fin 7,
    (Constr2D.sq r c).mem r0 c0 = get49 (sq22 ⟨r.val * 7 + c.val, by omega⟩) r0 c0 := by decide

private lemma constr2D_row_card_le (r : Fin 7) {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) :
    (∑ p ∈ B, if (Constr2D.row r).mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) ≤ 3 := by
  have hle := (row_indep_adj hB r).2
  have hne : r ≠ next7 r := (by decide : ∀ x : Fin 7, x ≠ next7 x) r
  have h1 : (∑ p ∈ B, if (Constr2D.row r).mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) =
      ∑ p : Fin 7 × Fin 7, if p.1 = r ∨ p.1 = next7 r then (get49 (ofFinset49 B) p.1 p.2).toNat else 0 := by
    have h2 : (∑ p ∈ B, if (Constr2D.row r).mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) =
        ∑ q : ZMod 7 × ZMod 7, if q ∈ B then (if (Constr2D.row r).mem (ofZ7 q.1) (ofZ7 q.2) then 1 else 0) else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [h2, ← Equiv.sum_comp fin7SqEquivZ7Sq]
    refine Finset.sum_congr rfl fun ⟨r', c'⟩ _ => ?_
    simp only [fin7SqEquivZ7Sq, Equiv.coe_fn_mk, ofZ7_toZ7, Constr2D.mem, Bool.or_eq_true, beq_iff_eq]
    by_cases hmem : (toZ7 r', toZ7 c') ∈ B
    · have hb' := (get49_ofFinset B r' c').mpr hmem
      by_cases hr : r' = r ∨ r' = next7 r <;> simp [hmem, hb', hr]
    · have hb' : get49 (ofFinset49 B) r' c' = false :=
        Bool.eq_false_iff.mpr fun h => hmem ((get49_ofFinset B r' c').mp h)
      simp [hmem, hb']
  rw [h1, Fintype.sum_prod_type]
  have hstep : (∑ x : Fin 7, ∑ y : Fin 7, if x = r ∨ x = next7 r then (get49 (ofFinset49 B) x y).toNat else 0) =
      ∑ x : Fin 7, if x = r ∨ x = next7 r then (∑ y : Fin 7, (get49 (ofFinset49 B) x y).toNat) else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x = r ∨ x = next7 r <;> simp [hx]
  rw [hstep]
  have hdisj : Disjoint ({r} : Finset (Fin 7)) {next7 r} := Finset.disjoint_singleton.mpr hne
  have hfilt : Finset.univ.filter (fun x : Fin 7 => x = r ∨ x = next7 r) = {r} ∪ {next7 r} := by
    ext x; simp
  rw [← Finset.sum_filter, hfilt, Finset.sum_union hdisj, Finset.sum_singleton, Finset.sum_singleton]
  simpa only [pop7_row49_eq_sum] using hle

private lemma constr2D_card_le (ct : Constr2D) {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) :
    (∑ p ∈ B, if ct.mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) ≤ ct.rhs := by
  cases ct with
  | sq r c =>
    let idx : Fin 49 := ⟨r.val * 7 + c.val, by omega⟩
    have hpop := sq22_card_le_one idx hB
    have hsum_eq : (∑ p ∈ B, if (Constr2D.sq r c).mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) =
        pop49 (ofFinset49 B &&& sq22 idx) := by
      rw [pop49_eq_sum, ← Fintype.sum_prod_type']
      have h1 : (∑ p : Fin 7 × Fin 7, (get49 (ofFinset49 B &&& sq22 idx) p.1 p.2).toNat) =
          ∑ q : ZMod 7 × ZMod 7, if q ∈ B then (if get49 (sq22 idx) (ofZ7 q.1) (ofZ7 q.2) then 1 else 0) else 0 := by
        rw [← Equiv.sum_comp fin7SqEquivZ7Sq]
        refine Finset.sum_congr rfl fun ⟨r', c'⟩ _ => ?_
        rw [get49_and]
        simp only [fin7SqEquivZ7Sq, Equiv.coe_fn_mk, ofZ7_toZ7]
        by_cases hmem : (toZ7 r', toZ7 c') ∈ B
        · have hb' := (get49_ofFinset B r' c').mpr hmem
          cases hsq : get49 (sq22 idx) r' c' <;> simp [hmem, hb']
        · have hb' : get49 (ofFinset49 B) r' c' = false :=
            Bool.eq_false_iff.mpr fun h => hmem ((get49_ofFinset B r' c').mp h)
          simp [hmem, hb']
      rw [h1, Finset.sum_ite_mem, Finset.univ_inter]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [constr2D_sq_eq r c (ofZ7 p.1) (ofZ7 p.2)]
    rw [hsum_eq]; exact hpop
  | row r => exact constr2D_row_card_le r hB
  | col c =>
    let gSw : Aut2 := ⟨true, false, 0, false, 0⟩
    let B' := B.map gSw.toIso.toEquiv.toEmbedding
    have hB' : (C7 ⊠ C7).IsIndepSet (B' : Set (ZMod 7 × ZMod 7)) := isIndepSet_map_iso' gSw.toIso hB
    have hsum_eq : (∑ p ∈ B, if (Constr2D.col c).mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) =
        ∑ q ∈ B', if (Constr2D.row c).mem (ofZ7 q.1) (ofZ7 q.2) then 1 else 0 := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun ⟨a, b⟩ _ => ?_
      have hg : gSw.toIso (a, b) = (b, a) := by
        have h0 : ∀ x : Fin 7, add7 x 0 = x := by decide
        exact Prod.ext
          (by change toZ7 (add7 (ofZ7 b) 0) = b; rw [h0, toZ7_ofZ7])
          (by change toZ7 (add7 (ofZ7 a) 0) = a; rw [h0, toZ7_ofZ7])
      simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, hg, Constr2D.mem]; rfl
    rw [hsum_eq]
    exact constr2D_row_card_le c hB'
  | all =>
    simp only [Constr2D.mem, ↓reduceIte, Finset.sum_const, smul_eq_mul, mul_one, Constr2D.rhs]
    exact alpha_c7_pow2_le_internal hB

private lemma accumGrid_sum_le (terms : List (Constr2D × Nat)) {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) :
    (∑ p ∈ B, (accumGrid terms).get (ofZ7 p.1) (ofZ7 p.2)) ≤ rhsSum terms := by
  induction terms with
  | nil => simp [accumGrid, rhsSum, Grid49.get_zero]
  | cons hd rest ih =>
    rcases hd with ⟨ct, w⟩
    simp only [accumGrid, rhsSum, Grid49.get_addConstr, Finset.sum_add_distrib]
    have hct : (∑ p ∈ B, if ct.mem (ofZ7 p.1) (ofZ7 p.2) then w else 0) =
        w * (∑ p ∈ B, if ct.mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
    rw [hct]
    have hle := Nat.mul_le_mul_left w (constr2D_card_le ct hB)
    omega

private lemma checkFarkas2D_sound {F : Nat} {cert : Nat × List (Constr2D × Nat)}
    {B : Finset (ZMod 7 × ZMod 7)} (hchk : checkFarkas2D F cert = true)
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7)))
    (hdisj : disjoint49 (ofFinset49 B) F = true) : B.card ≤ 9 := by
  rcases cert with ⟨D, terms⟩
  simp only [checkFarkas2D, Bool.and_eq_true, Nat.blt_eq] at hchk
  rcases hchk with ⟨⟨hDpos, hrhs⟩, hge⟩
  rw [disjoint49_iff (ofFinset49_lt B)] at hdisj
  have hlow : B.card * D ≤ ∑ p ∈ B, (accumGrid terms).get (ofZ7 p.1) (ofZ7 p.2) := by
    calc B.card * D = ∑ _p ∈ B, D := by simp
      _ ≤ ∑ p ∈ B, (accumGrid terms).get (ofZ7 p.1) (ofZ7 p.2) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hF : get49 F (ofZ7 p.1) (ofZ7 p.2) = false :=
          hdisj (ofZ7 p.1) (ofZ7 p.2) ((get49_ofFinset B (ofZ7 p.1) (ofZ7 p.2)).mpr (by simpa [toZ7_ofZ7] using hp))
        exact Grid49.geMask_sound hge (ofZ7 p.1) (ofZ7 p.2) hF
  have hup := accumGrid_sum_le terms hB
  have hlt : B.card * D < 10 * D := lt_of_le_of_lt (le_trans hlow hup) hrhs
  have hcard_lt : B.card < 10 := Nat.lt_of_mul_lt_mul_right hlt
  omega

private lemma checkFarkas3D_sound {CR CL : Nat}
    {cert : Nat × List (Constr2D × Nat) × List (Constr2D × Nat)}
    {S4 S5 S6 : Finset (ZMod 7 × ZMod 7)} (hchk : checkFarkas3D CR CL cert = true)
    (hd45 : Disjoint S4 S5) (h45 : (C7 ⊠ C7).IsIndepSet ((S4 ∪ S5 : Finset _) : Set _))
    (hd56 : Disjoint S5 S6) (h56 : (C7 ⊠ C7).IsIndepSet ((S5 ∪ S6 : Finset _) : Set _))
    (hdisj4 : disjoint49 (ofFinset49 S4) CR = true)
    (hdisj6 : disjoint49 (ofFinset49 S6) CL = true) :
    S4.card + S5.card + S6.card ≤ 13 := by
  rcases cert with ⟨D, t0, t1⟩
  simp only [checkFarkas3D, Bool.and_eq_true, Nat.blt_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨hDpos, hrhs⟩, hge0⟩, hgeMid⟩, hge1⟩
  rw [disjoint49_iff (ofFinset49_lt S4)] at hdisj4
  rw [disjoint49_iff (ofFinset49_lt S6)] at hdisj6
  have hup0 := accumGrid_sum_le t0 h45
  have hup1 := accumGrid_sum_le t1 h56
  rw [Finset.sum_union hd45] at hup0
  rw [Finset.sum_union hd56] at hup1
  have hlow4 : S4.card * D ≤ ∑ p ∈ S4, (accumGrid t0).get (ofZ7 p.1) (ofZ7 p.2) := by
    calc S4.card * D = ∑ _p ∈ S4, D := by simp
      _ ≤ _ := Finset.sum_le_sum fun p hp =>
        Grid49.geMask_sound hge0 (ofZ7 p.1) (ofZ7 p.2)
          (hdisj4 _ _ ((get49_ofFinset S4 _ _).mpr (by simpa [toZ7_ofZ7] using hp)))
  have hlow5 : S5.card * D ≤
      (∑ p ∈ S5, (accumGrid t0).get (ofZ7 p.1) (ofZ7 p.2)) +
      (∑ p ∈ S5, (accumGrid t1).get (ofZ7 p.1) (ofZ7 p.2)) := by
    rw [← Finset.sum_add_distrib]
    calc S5.card * D = ∑ _p ∈ S5, D := by simp
      _ ≤ ∑ p ∈ S5, ((accumGrid t0).add (accumGrid t1)).get (ofZ7 p.1) (ofZ7 p.2) :=
        Finset.sum_le_sum fun p _ => Grid49.geMask_sound hgeMid (ofZ7 p.1) (ofZ7 p.2) (get49_zero _ _)
      _ = _ := Finset.sum_congr rfl fun p _ => Grid49.get_add _ _ _ _
  have hlow6 : S6.card * D ≤ ∑ p ∈ S6, (accumGrid t1).get (ofZ7 p.1) (ofZ7 p.2) := by
    calc S6.card * D = ∑ _p ∈ S6, D := by simp
      _ ≤ _ := Finset.sum_le_sum fun p hp =>
        Grid49.geMask_sound hge1 (ofZ7 p.1) (ofZ7 p.2)
          (hdisj6 _ _ ((get49_ofFinset S6 _ _).mpr (by simpa [toZ7_ofZ7] using hp)))
  have htot : (S4.card + S5.card + S6.card) * D < 14 * D := by
    have hsum_le : (S4.card + S5.card + S6.card) * D ≤ rhsSum t0 + rhsSum t1 := by
      have : (S4.card + S5.card + S6.card) * D = S4.card * D + S5.card * D + S6.card * D := by ring
      omega
    exact lt_of_le_of_lt hsum_le hrhs
  have hlt : S4.card + S5.card + S6.card < 14 := Nat.lt_of_mul_lt_mul_right htot
  omega

/-! ## Section 6: Canonical Subset Generators & Certificate Tables (P1+P3, P2, P4, P5) -/

private def subsetsOfList : List (Fin 7 × Fin 7) → Nat → List Nat
  | _, 0 => [0]
  | [], _ + 1 => []
  | (r, c) :: rest, k + 1 =>
      (subsetsOfList rest k).map (fun m => set49 m r c) ++ subsetsOfList rest (k + 1)

private lemma mem_subsetsOfList (pts : List (Fin 7 × Fin 7)) (hnd : pts.Nodup) :
    ∀ (X : Nat), X < 2 ^ 49 → (∀ r c : Fin 7, get49 X r c = true → (r, c) ∈ pts) →
      X ∈ subsetsOfList pts (pop49 X) := by
  induction pts with
  | nil =>
    intro X hX h
    have hX0 : X = 0 := by
      apply ext49 hX (by decide)
      intro r c
      cases hx : get49 X r c
      · exact (get49_zero r c).symm
      · exact absurd (h r c hx) (by simp)
    subst hX0; simp [subsetsOfList, show pop49 0 = 0 by decide]
  | cons p0 rest ih =>
    rcases p0 with ⟨r0, c0⟩
    have ⟨hp0_not_rest, hrest_nd⟩ := List.nodup_cons.mp hnd
    intro X hX hXsub
    cases hXp : get49 X r0 c0
    · have hXrest : ∀ r c : Fin 7, get49 X r c = true → (r, c) ∈ rest := by
        intro r c h
        rcases List.mem_cons.mp (hXsub r c h) with heq | hr
        · injection heq with h1 h2; subst h1 h2; rw [hXp] at h; exact absurd h (by decide)
        · exact hr
      have hmem := ih hrest_nd X hX hXrest
      cases hk : pop49 X
      · rw [hk] at hmem
        simp only [subsetsOfList, List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
        exact hmem
      · rw [hk] at hmem
        exact List.mem_append_right _ hmem
    · let X' := diff49 X (bit49 r0 c0)
      have hX'lt : X' < 2 ^ 49 := diff49_lt hX
      have hX'get : ∀ r c : Fin 7, get49 X' r c = (if r = r0 ∧ c = c0 then false else get49 X r c) := by
        intro r c; unfold X'; rw [get49_diff]
        have hb : get49 (bit49 r0 c0) r c = decide (r = r0 ∧ c = c0) := testBit_bit49 r0 c0 r c
        rw [hb]; split_ifs with h <;> simp [h]
      have hXeq : X = set49 X' r0 c0 := by
        apply ext49 hX (set49_lt hX'lt r0 c0)
        intro r c; rw [get49_set, hX'get]
        split_ifs with h
        · exact h.1 ▸ h.2 ▸ hXp
        · rfl
      have hpop : pop49 X = pop49 X' + 1 := by
        rw [hXeq]; exact pop49_set49_of_false (by rw [hX'get]; simp)
      have hX'rest : ∀ r c : Fin 7, get49 X' r c = true → (r, c) ∈ rest := by
        intro r c h
        rw [hX'get] at h
        split_ifs at h with heq
        rcases List.mem_cons.mp (hXsub r c h) with heq2 | hr
        · injection heq2 with h1 h2; exact absurd ⟨h1, h2⟩ heq
        · exact hr
      have hmem := ih hrest_nd X' hX'lt hX'rest
      rw [hpop]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨X', hmem, hXeq.symm⟩)

private def halves5 (k : Fin 3) : List Nat :=
  (subsetsOfList (repPtsList k).tail 4).map (fun m => set49 m 0 3)

private def subs4 (k : Fin 3) : List Nat :=
  subsetsOfList (repPtsList k) 4

private lemma mem_halves5 {k : Fin 3} {X : Nat} (hX : X < 2 ^ 49)
    (hXrep : subset49 X (rep k) = true) (hXpop : pop49 X = 5) (h03 : get49 X 0 3 = true) :
    X ∈ halves5 k := by
  have hhead : repPtsList k = (0, 3) :: (repPtsList k).tail :=
    match k with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
  have hnd := repPtsList_nodup k
  rw [hhead] at hnd
  have ⟨_, hrest_nd⟩ := List.nodup_cons.mp hnd
  let X' := diff49 X (bit49 0 3)
  have hX'lt : X' < 2 ^ 49 := diff49_lt hX
  have hX'get : ∀ r c : Fin 7, get49 X' r c = (if r = 0 ∧ c = 3 then false else get49 X r c) := by
    intro r c; unfold X'; rw [get49_diff]
    have hb : get49 (bit49 0 3) r c = decide (r = 0 ∧ c = 3) := testBit_bit49 0 3 r c
    rw [hb]; split_ifs with h <;> simp [h]
  have hXeq : X = set49 X' 0 3 := by
    apply ext49 hX (set49_lt hX'lt 0 3)
    intro r c; rw [get49_set, hX'get]
    split_ifs with h
    · exact h.1 ▸ h.2 ▸ h03
    · rfl
  have hX'pop : pop49 X' = 4 := by
    have hpop : pop49 X = pop49 X' + 1 := by
      rw [hXeq]; exact pop49_set49_of_false (by rw [hX'get]; simp)
    omega
  have hX'rest : ∀ r c : Fin 7, get49 X' r c = true → (r, c) ∈ (repPtsList k).tail := by
    intro r c h
    rw [hX'get] at h
    split_ifs at h with heq
    have hmem : (r, c) ∈ repPtsList k := (rep_mem_iff k r c).mp ((subset49_iff hX).mp hXrep r c h)
    rw [hhead] at hmem
    rcases List.mem_cons.mp hmem with heq2 | hr
    · injection heq2 with h1 h2; exact absurd ⟨h1, h2⟩ heq
    · exact hr
  have hmem := mem_subsetsOfList _ hrest_nd X' hX'lt hX'rest
  rw [hX'pop] at hmem
  exact List.mem_map.mpr ⟨X', hmem, hXeq.symm⟩

private lemma mem_subs4 {k : Fin 3} {X : Nat} (hX : X < 2 ^ 49)
    (hXrep : subset49 X (rep k) = true) (hXpop : pop49 X = 4) :
    X ∈ subs4 k := by
  have hmem := mem_subsetsOfList (repPtsList k) (repPtsList_nodup k) X hX
    (fun r c h => (rep_mem_iff k r c).mp ((subset49_iff hX).mp hXrep r c h))
  rw [hXpop] at hmem
  exact hmem

private def near4 (k : Fin 3) : List (Fin 3 × Aut2 × Nat) := nearK k 4
private def near5 (k : Fin 3) : List (Fin 3 × Aut2 × Nat) := nearK k 5
private def near6 (k : Fin 3) : List (Fin 3 × Aut2 × Nat) := nearK k 6

private lemma mem_near_of_subset {k : Fin 3} {m : Nat} {X : Nat}
    {k0 : Fin 3} {g : Aut2} (hX : X < 2 ^ 49) (hsr : k0 ≠ 2 ∨ g.sr = false)
    (hXrep : subset49 X (rep k) = true) (hXB : subset49 X (g.applyMask (rep k0)) = true) (hm : m ≤ pop49 X) :
    (k0, g, g.applyMask (rep k0)) ∈ nearK k m := by
  refine mem_nearK hsr ?_
  have hsub : subset49 X ((g.applyMask (rep k0)) &&& (rep k)) = true := by
    rw [subset49_iff hX] at hXB hXrep ⊢
    intro r c hx; rw [get49_and, hXB r c hx, hXrep r c hx]; rfl
  exact hm.trans (subset49_pop_le hX hsub)

private inductive SqCert where
  | pop3 : SqCert
  | sq3 (a b c : Fin 49) : SqCert
  | splitL1 (covs : List (Fin 49 × Fin 49 × Fin 49)) : SqCert

private def checkSqCase (k : Fin 3) (nL nR : List (Fin 3 × Aut2 × Nat))
    (S2 : Nat) (cert : SqCert) : Bool :=
  seqN (diff49 (rep k) S2) fun S3 =>
  match cert with
  | .pop3 =>
      let CL := (c2Tree k).getAux (repBits k) S2
      let CR := (c2Tree k).getAux (repBits k) S3
      Nat.ble (pop49 (not49 (Nat.lor CL CR))) 3
  | .sq3 a b c =>
      let CL := (c2Tree k).getAux (repBits k) S2
      let CR := (c2Tree k).getAux (repBits k) S3
      seqN (not49 (Nat.lor CL CR)) fun avail => checkAvailSq3 avail a b c
  | .splitL1 covs =>
      let L1 := nL.filter fun t => subset49 S2 t.2.2
      let R4 := nR.filter fun t => subset49 S3 t.2.2
      L1.all fun t1 =>
        seqN (diff49 (rep t1.1) (t1.2.1.inv.applyMask S2)) fun y1Canon =>
        seqN (t1.2.1.applyMask ((c1Tree t1.1).getAux (repBits t1.1) y1Canon)) fun c1L =>
        R4.all fun t4 =>
          seqN (diff49 (rep t4.1) (t4.2.1.inv.applyMask S3)) fun y4Canon =>
          seqN (t4.2.1.applyMask ((c1Tree t4.1).getAux (repBits t4.1) y4Canon)) fun c1R =>
          seqN (not49 (Nat.lor c1L c1R)) fun avail =>
          Nat.ble (pop49 avail) 3 || covs.any fun (a, b, c) => checkAvailSq3 avail a b c

private def checkP4Case (k : Fin 3) (S2 : Nat) (cert : Nat × List (Constr2D × Nat)) : Bool :=
  seqN (diff49 (rep k) S2) fun S1 =>
  let CL := (c1Tree k).getAux (repBits k) S1
  let CR := (c2Tree k).getAux (repBits k) S2
  seqN (Nat.land CL CR) fun F => checkFarkas2D F cert

private inductive P5S0Cert where
  | leaf (f : Nat × List (Constr2D × Nat) × List (Constr2D × Nat))
  | splitS3 (f3s : List (Nat × List (Constr2D × Nat) × List (Constr2D × Nat)))

private inductive P5Cert where
  | root (f : Nat × List (Constr2D × Nat) × List (Constr2D × Nat))
  | splitS0 (f0s : List P5S0Cert)

private def checkP5Case (k : Fin 3) (n5 : List (Fin 3 × Aut2 × Nat))
    (S1 : Nat) (cert : P5Cert) : Bool :=
  seqN (diff49 (rep k) S1) fun S2 =>
  let CL := (c1Tree k).getAux (repBits k) S1
  let CR := (c1Tree k).getAux (repBits k) S2
  match cert with
  | .root f => checkFarkas3D CR CL f
  | .splitS0 f0s =>
      let L0 := n5.filter fun t => subset49 S1 t.2.2
      let R3 := n5.filter fun t => subset49 S2 t.2.2
      checkAll (fun t0 c0 =>
        seqN (diff49 t0.2.2 S1) fun d0 =>
        seqN (closedNbr49 d0) fun n0 =>
        match c0 with
        | .leaf f => checkFarkas3D CR n0 f
        | .splitS3 f3s =>
            checkAll (fun t3 f3 =>
              seqN (diff49 t3.2.2 S2) fun d3 =>
              seqN (closedNbr49 d3) fun n3 =>
              checkFarkas3D n3 n0 f3) R3 f3s) L0 f0s

private def p13Certs0 : List SqCert := [
  .splitL1 [], .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .splitL1 [], .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .splitL1 [], .pop3, .pop3, .splitL1 [],
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .splitL1 [], .splitL1 [], .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .sq3 38 18 21, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .sq3 4 33 1, .pop3, .pop3, .pop3, .pop3,
  .pop3, .sq3 7 20 26, .splitL1 [], .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .sq3 8 18 23, .pop3, .sq3 4 11 18,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .sq3 33 20 20,
  .sq3 32 3 39, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .splitL1 [(39, 28, 28)], .pop3, .pop3, .sq3 28 29 34,
  .pop3, .pop3, .sq3 0 40 18, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .splitL1 [], .pop3, .pop3, .pop3, .pop3
]
private def p13Certs1 : List SqCert := [
  .splitL1 [], .pop3, .sq3 5 11 17, .pop3, .pop3, .pop3,
  .pop3, .sq3 2 10 17, .pop3, .pop3, .splitL1 [], .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .splitL1 [], .splitL1 [], .pop3, .splitL1 [], .pop3,
  .pop3, .sq3 15 32 37, .pop3, .pop3, .pop3, .pop3,
  .pop3, .splitL1 [], .pop3, .pop3, .pop3, .sq3 30 15 32,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .sq3 42 43 37, .pop3, .pop3, .pop3,
  .pop3, .pop3, .splitL1 [(32, 25, 37)], .sq3 21 32 3, .pop3, .sq3 30 3 18,
  .sq3 1 3 32, .sq3 32 25 3, .pop3, .sq3 4 5 45, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .sq3 7 3 5, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .splitL1 [(38, 42, 42)], .pop3, .pop3, .pop3, .pop3, .splitL1 [],
  .sq3 6 3 8, .splitL1 [(0, 6, 8)], .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .sq3 2 3 45, .pop3
]
private def p13Certs2 : List SqCert := [
  .splitL1 [], .pop3, .sq3 18 5 5, .pop3, .pop3, .pop3,
  .pop3, .sq3 17 24 30, .sq3 40 25 37, .pop3, .splitL1 [(33, 11, 11), (38, 39, 10), (38, 11, 11), (33, 38, 11), (33, 39, 11)], .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .splitL1 [], .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .splitL1 [], .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .splitL1 [], .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .splitL1 [], .pop3, .splitL1 [], .pop3, .pop3,
  .splitL1 [], .splitL1 [], .pop3, .pop3, .sq3 11 17 17, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .sq3 5 11 47, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .sq3 38 3 33,
  .splitL1 [(39, 39, 39)], .pop3, .pop3, .pop3, .pop3, .splitL1 [],
  .pop3, .splitL1 [], .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3
]

private def p2Certs0 : List SqCert := [
  .pop3, .pop3, .pop3, .pop3, .splitL1 [], .pop3,
  .splitL1 [], .pop3, .pop3, .pop3, .splitL1 [(40, 33, 33), (40, 32, 32)], .pop3,
  .splitL1 [(40, 39, 39)], .pop3, .pop3, .pop3, .pop3, .pop3,
  .sq3 1 39 39, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .sq3 4 5 40, .pop3, .splitL1 [], .pop3, .pop3,
  .pop3, .sq3 8 18 23, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .splitL1 [],
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .splitL1 [(30, 22, 22)], .pop3, .pop3, .sq3 34 37 30, .pop3,
  .pop3, .sq3 40 29 18, .splitL1 [], .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .splitL1 [], .splitL1 [], .pop3, .sq3 10 16 28,
  .pop3, .pop3, .pop3, .pop3, .pop3, .sq3 46 3 40,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .sq3 16 33 38, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .splitL1 [], .sq3 32 3 3, .splitL1 [(33, 33, 33)],
  .pop3, .pop3, .sq3 11 32 45, .splitL1 [(33, 25, 25), (32, 8, 8), (33, 8, 8)], .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .sq3 32 8 25, .splitL1 [], .pop3, .pop3, .sq3 24 28 28, .splitL1 [],
  .splitL1 [(39, 39, 39), (39, 28, 28)], .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .sq3 32 3 21, .sq3 26 4 4, .splitL1 [], .pop3, .splitL1 [], .pop3,
  .pop3, .pop3, .sq3 22 23 18, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .sq3 8 18 23, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .splitL1 [],
  .sq3 1 38 19, .pop3, .pop3, .pop3, .pop3, .pop3,
  .splitL1 [], .pop3, .pop3, .pop3, .sq3 14 21 18, .pop3,
  .pop3, .sq3 33 4 0, .splitL1 [(32, 6, 6)], .pop3, .pop3, .sq3 34 3 23,
  .pop3, .pop3, .pop3, .pop3, .pop3, .sq3 11 38 33,
  .pop3, .pop3, .splitL1 [(36, 38, 28), (37, 38, 11)], .pop3, .pop3, .pop3,
  .pop3, .pop3, .sq3 39 40 18, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .sq3 34 35 38, .pop3, .splitL1 [(26, 33, 33)],
  .splitL1 [], .splitL1 [(38, 39, 39), (38, 32, 32)], .pop3, .pop3, .pop3, .splitL1 []
]
private def p2Certs1 : List SqCert := [
  .splitL1 [], .splitL1 [(40, 40, 40)], .pop3, .splitL1 [(32, 2, 2)], .splitL1 [], .pop3,
  .splitL1 [(40, 39, 39)], .splitL1 [], .pop3, .splitL1 [(43, 43, 43)], .pop3, .pop3,
  .splitL1 [(37, 15, 15)], .pop3, .splitL1 [], .sq3 37 40 47, .pop3, .splitL1 [],
  .pop3, .splitL1 [], .sq3 0 7 3, .splitL1 [], .sq3 30 3 18, .sq3 42 28 3,
  .pop3, .pop3, .splitL1 [(32, 25, 37)], .splitL1 [], .splitL1 [], .pop3,
  .splitL1 [(7, 45, 45)], .pop3, .pop3, .pop3, .pop3, .splitL1 [],
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .sq3 5 40 12,
  .pop3, .pop3, .splitL1 [], .pop3, .pop3, .pop3,
  .pop3, .pop3, .splitL1 [], .pop3, .pop3, .splitL1 [(32, 42, 42), (38, 42, 42), (39, 42, 42), (1, 42, 32), (1, 8, 42), (1, 39, 42)],
  .splitL1 [], .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .sq3 35 38 18, .pop3, .sq3 39 40 0, .pop3,
  .splitL1 [], .pop3, .splitL1 [], .pop3, .pop3, .pop3,
  .splitL1 [(0, 6, 8)], .splitL1 [(7, 45, 45)], .splitL1 [(48, 0, 0)], .pop3, .splitL1 [(33, 34, 42), (35, 34, 42)], .sq3 13 32 8,
  .pop3, .pop3, .splitL1 [(8, 0, 0)], .pop3, .pop3, .pop3,
  .pop3, .sq3 42 12 19, .pop3, .pop3, .splitL1 [], .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .sq3 7 3 5, .pop3, .pop3, .splitL1 [], .pop3,
  .pop3, .pop3, .sq3 42 38 3, .pop3, .sq3 17 18 20, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .splitL1 [], .splitL1 [(32, 2, 2)], .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .sq3 7 8 5, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .sq3 25 32 37, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .splitL1 [], .splitL1 [], .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .splitL1 [(38, 32, 32)], .pop3, .pop3,
  .pop3, .splitL1 [], .pop3, .pop3, .pop3, .splitL1 []
]
private def p2Certs2 : List SqCert := [
  .splitL1 [(40, 17, 17)], .sq3 18 40 38, .pop3, .sq3 2 3 5, .pop3, .pop3,
  .splitL1 [], .sq3 37 8 18, .pop3, .splitL1 [(18, 18, 18)], .pop3, .pop3,
  .sq3 36 37 4, .pop3, .pop3, .splitL1 [], .pop3, .sq3 33 39 1,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .splitL1 [], .sq3 45 15 18, .pop3,
  .splitL1 [(18, 10, 10), (7, 45, 45)], .pop3, .pop3, .pop3, .pop3, .sq3 45 17 30,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .splitL1 [], .pop3, .pop3, .pop3, .splitL1 [], .splitL1 [(39, 39, 39)],
  .splitL1 [], .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .splitL1 [], .pop3, .pop3, .pop3,
  .sq3 0 3 8, .pop3, .splitL1 [], .pop3, .splitL1 [(34, 3, 39), (33, 3, 39)], .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .sq3 9 20 20, .pop3,
  .pop3, .pop3, .pop3, .sq3 32 11 47, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .splitL1 [], .splitL1 [(11, 18, 18), (32, 8, 8)], .sq3 14 8 3, .pop3, .splitL1 [(11, 11, 11)], .pop3,
  .pop3, .splitL1 [], .splitL1 [(39, 39, 39)], .sq3 32 33 3, .sq3 17 18 20, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .splitL1 [], .pop3, .pop3, .pop3,
  .pop3, .sq3 22 7 18, .pop3, .pop3, .splitL1 [], .pop3,
  .pop3, .sq3 8 7 18, .pop3, .pop3, .pop3, .pop3,
  .pop3, .splitL1 [], .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .pop3, .pop3, .pop3, .pop3,
  .pop3, .pop3, .splitL1 [], .pop3, .pop3, .pop3,
  .pop3, .pop3, .sq3 33 0 3, .pop3, .pop3, .sq3 34 3 7,
  .pop3, .pop3, .pop3, .pop3, .pop3, .sq3 11 38 33,
  .splitL1 [(37, 39, 25), (32, 38, 25)], .pop3, .pop3, .pop3, .pop3, .sq3 38 39 14,
  .pop3, .sq3 38 39 25, .pop3, .splitL1 [(38, 11, 11)], .pop3, .pop3,
  .pop3, .pop3, .pop3, .sq3 35 34 17, .pop3, .pop3,
  .pop3, .splitL1 [], .pop3, .pop3, .pop3, .splitL1 []
]

private def p4Certs0 : List (Nat × List (Constr2D × Nat)) := [
  (1, [(cS 1 0, 1), (cS 1 5, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 1 2, 1), (cS 1 4, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 5 1, 1), (cS 5 2, 1), (cS 5 6, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 2 5, 1), (cS 3 3, 1), (cS 3 4, 1), (cS 4 5, 1), (cS 5 3, 1), (cS 5 4, 1), (cC 0, 1), (cC 1, 1), (cC 2, 1), (cC 6, 1)]),
  (2, [(cS 0 1, 1), (cS 0 2, 1), (cS 1 5, 1), (cS 3 2, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 5 2, 1), (cR 5, 1), (cC 0, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 1 6, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 6 0, 1), (cS 6 3, 1), (cC 1, 1)]),
  (1, [(cC 0, 1), (cC 2, 1), (cC 5, 1)]),
  (3, [(cS 0 4, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 1 5, 1), (cS 4 4, 1), (cS 5 3, 1), (cS 5 6, 1), (cS 6 0, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1), (cC 0, 1), (cC 1, 1), (cC 5, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 0 0, 1), (cS 0 1, 1), (cS 1 2, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 2 6, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cC 0, 1), (cC 2, 1), (cC 4, 1)]),
  (2, [(cS 0 0, 1), (cS 1 1, 1), (cS 2 3, 1), (cS 3 1, 1), (cS 4 2, 1), (cS 5 0, 1), (cS 6 0, 1), (cR 2, 1), (cR 4, 1), (cC 6, 1)]),
  (1, [(cS 1 0, 1), (cS 6 0, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 0 0, 1), (cS 1 6, 1), (cS 5 0, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cS 1 5, 1), (cS 2 3, 1), (cS 3 5, 1), (cS 4 2, 1), (cS 5 5, 1), (cC 0, 1)]),
  (1, [(cS 2 3, 1), (cS 4 3, 1), (cC 0, 1), (cC 5, 1)]),
  (1, [(cS 5 2, 1), (cS 5 4, 1), (cS 5 6, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 1 5, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 4 2, 1), (cC 0, 1)]),
  (1, [(cS 1 5, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 2, 1), (cS 4 4, 1), (cC 0, 1)]),
  (1, [(cS 3 0, 1), (cS 3 2, 1), (cS 3 4, 1), (cS 5 2, 1), (cS 5 4, 1), (cR 1, 1)]),
  (2, [(cS 1 3, 1), (cS 1 4, 1), (cS 2 2, 1), (cS 3 3, 1), (cS 3 4, 1), (cC 0, 1), (cC 1, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cS 5 1, 1), (cS 5 3, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 4 3, 1), (cS 5 5, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 0 6, 1), (cS 6 4, 1), (cR 3, 1), (cR 5, 1)]),
  (3, [(cS 1 5, 1), (cS 1 6, 1), (cS 4 2, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 5 3, 1), (cR 3, 1), (cR 4, 1), (cR 6, 1), (cC 0, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (2, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 0, 1), (cS 3 1, 1), (cS 3 2, 1), (cS 3 4, 1), (cR 4, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cC 0, 1), (cC 2, 1), (cC 5, 1)]),
  (1, [(cS 2 1, 1), (cS 4 1, 1), (cS 6 1, 1), (cC 4, 1), (cC 6, 1)]),
  (2, [(cS 0 5, 1), (cS 6 1, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1)]),
  (1, [(cR 2, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cR 2, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cR 2, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cR 2, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cS 6 1, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 2, 1), (cR 4, 1)]),
  (2, [(cS 0 6, 2), (cS 1 2, 1), (cS 1 3, 1), (cS 2 0, 1), (cS 2 6, 1), (cS 3 3, 2), (cS 5 0, 1), (cS 5 2, 1), (cR 5, 1), (cC 4, 1), (cC 5, 1)]),
  (1, [(cS 1 0, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 4 2, 1), (cS 5 0, 1), (cC 5, 1)]),
  (1, [(cC 0, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 2 2, 1), (cS 4 2, 1), (cS 6 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 2 3, 1), (cS 3 1, 1), (cS 4 2, 1), (cS 5 0, 1), (cC 5, 1)]),
  (1, [(cS 1 3, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 5 0, 1), (cS 5 3, 1), (cC 5, 1)]),
  (1, [(cS 1 1, 1), (cS 3 1, 1), (cS 5 1, 1), (cC 3, 1), (cC 5, 1)]),
  (2, [(cS 0 4, 1), (cS 4 0, 1), (cS 5 4, 1), (cS 6 0, 1), (cR 2, 1), (cC 1, 1), (cC 3, 1), (cC 5, 1), (cC 6, 1)]),
  (2, [(cS 0 3, 1), (cS 0 5, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 5 3, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)]),
  (3, [(cS 2 1, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 4 1, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 1, 1), (cR 2, 1), (cR 4, 1), (cC 3, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 1 1, 1), (cS 2 1, 1), (cR 4, 1), (cR 6, 1)]),
  (3, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 1, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 6 4, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1), (cR 6, 1), (cC 0, 1), (cC 2, 1), (cC 6, 1)]),
  (2, [(cS 2 1, 1), (cS 3 4, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 5 4, 1), (cS 6 4, 1), (cC 0, 1), (cC 1, 1), (cC 5, 1), (cC 6, 1)]),
  (2, [(cS 0 6, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 5 2, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1)]),
  (1, [(cR 1, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cS 4 2, 1), (cS 6 2, 1), (cC 0, 1), (cC 5, 1)]),
  (1, [(cS 3 4, 1), (cS 5 3, 1), (cC 0, 1), (cC 5, 1)]),
  (2, [(cS 0 0, 1), (cS 1 0, 1), (cS 3 3, 1), (cS 3 6, 1), (cS 4 2, 1), (cS 5 2, 1), (cS 5 3, 1), (cS 6 1, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (2, [(cS 0 5, 1), (cS 1 1, 1), (cS 1 6, 1), (cS 2 1, 1), (cS 3 2, 2), (cS 4 0, 1), (cS 5 2, 2), (cS 5 5, 1), (cS 6 0, 1), (cC 0, 1), (cC 5, 1)]),
  (2, [(cS 0 0, 1), (cS 0 5, 2), (cS 1 1, 1), (cS 1 6, 2), (cS 2 1, 1), (cS 3 1, 1), (cS 3 4, 2), (cS 4 1, 1), (cS 5 0, 1), (cS 5 4, 2), (cS 5 6, 2), (cS 6 0, 1)]),
  (1, [(cS 1 0, 1), (cS 1 5, 1), (cS 2 1, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cS 1 1, 1), (cS 3 1, 1), (cC 0, 1), (cC 5, 1)]),
  (2, [(cS 2 1, 1), (cS 4 2, 1), (cS 5 2, 1), (cR 1, 1), (cR 3, 1), (cR 6, 1), (cC 0, 1), (cC 5, 1)]),
  (1, [(cS 1 1, 1), (cS 3 1, 1), (cS 6 1, 1), (cC 4, 1), (cC 6, 1)]),
  (2, [(cS 0 0, 1), (cS 0 1, 1), (cS 1 2, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 6 5, 1), (cR 4, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cS 0 0, 1), (cS 2 3, 1), (cS 3 6, 1), (cS 6 5, 1), (cR 5, 1)]),
  (2, [(cS 0 0, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 4, 1), (cS 6 5, 2), (cR 2, 1), (cC 0, 1), (cC 3, 1)]),
  (1, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 3, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 0 0, 1), (cS 2 1, 1), (cS 2 3, 2), (cS 4 2, 1), (cS 5 6, 1), (cS 6 0, 1), (cS 6 5, 2), (cR 4, 1), (cC 1, 1)]),
  (2, [(cS 1 3, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 2, 1), (cS 3 4, 1), (cS 4 3, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 4, 1), (cS 6 4, 1), (cS 6 5, 1), (cS 6 6, 1), (cC 0, 1), (cC 1, 1)]),
  (1, [(cS 0 5, 1), (cS 3 5, 1), (cS 5 5, 1), (cC 1, 1), (cC 3, 1)]),
  (2, [(cS 0 0, 1), (cS 1 1, 1), (cS 2 3, 1), (cS 3 1, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 6 5, 1), (cR 2, 1), (cC 0, 1), (cC 5, 1)]),
  (1, [(cS 1 0, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 6 5, 1)]),
  (2, [(cS 0 6, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 5 3, 1), (cS 5 5, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1)]),
  (1, [(cS 0 0, 1), (cS 0 5, 1), (cR 2, 1), (cR 5, 1)]),
  (1, [(cC 0, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 0 0, 1), (cS 2 0, 1), (cS 5 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 0 3, 1), (cS 2 3, 1), (cC 0, 1), (cC 5, 1)]),
  (1, [(cS 0 0, 1), (cS 0 5, 1), (cS 3 6, 1), (cS 4 2, 1), (cS 5 4, 1), (cR 2, 1)]),
  (1, [(cS 2 3, 1), (cS 4 3, 1), (cS 6 3, 1), (cC 0, 1), (cC 5, 1)]),
  (1, [(cS 0 0, 1), (cS 0 5, 1), (cS 5 0, 1), (cS 5 5, 1), (cR 2, 1)]),
  (1, [(cS 1 5, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 4 2, 1), (cS 6 5, 1), (cC 0, 1)]),
  (2, [(cS 0 0, 1), (cS 0 5, 1), (cS 5 4, 1), (cS 5 6, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cS 6 1, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 0 1, 1), (cS 0 3, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 0 3, 1), (cS 1 5, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 0 3, 1), (cS 1 5, 1), (cS 3 1, 1), (cS 3 2, 1), (cS 4 4, 1), (cR 5, 1)]),
  (1, [(cS 3 0, 1), (cS 5 0, 1), (cC 2, 1), (cC 5, 1)]),
  (1, [(cS 0 2, 1), (cS 1 5, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 5 6, 1), (cR 3, 1)]),
  (1, [(cS 0 3, 1), (cS 1 5, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 3 5, 1), (cS 4 1, 1), (cS 4 5, 1), (cS 6 1, 1), (cC 0, 1), (cC 2, 1), (cC 3, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 0 0, 1), (cS 3 1, 1), (cS 5 0, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cS 3 6, 1), (cS 5 6, 1), (cC 1, 1), (cC 3, 1)]),
  (2, [(cS 0 2, 1), (cS 0 3, 1), (cS 1 3, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 6, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 5 6, 1), (cR 3, 1), (cC 1, 1)]),
  (3, [(cS 0 1, 1), (cS 0 3, 1), (cS 2 6, 1), (cS 4 0, 1), (cS 4 5, 1), (cS 4 6, 1), (cR 2, 1), (cR 3, 1), (cR 5, 1), (cC 1, 1), (cC 2, 1), (cC 3, 1), (cC 4, 1)]),
  (2, [(cS 1 5, 1), (cS 2 3, 1), (cS 2 5, 1), (cS 3 4, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 4, 1), (cS 6 0, 1), (cS 6 2, 1), (cR 0, 1), (cC 3, 1)]),
  (1, [(cS 0 2, 1), (cS 0 4, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 5 1, 1), (cS 5 3, 1), (cC 6, 1)]),
  (1, [(cS 2 0, 1), (cS 4 0, 1), (cS 6 0, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cC 2, 1), (cC 4, 1), (cC 6, 1)]),
  (2, [(cS 0 3, 1), (cS 1 3, 1), (cS 1 5, 2), (cS 2 4, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 5 0, 2), (cS 5 2, 1), (cC 2, 1)]),
  (1, [(cS 1 5, 1), (cS 2 5, 1), (cS 3 1, 1), (cS 4 4, 1), (cS 5 0, 1), (cC 3, 1)]),
  (1, [(cS 0 1, 1), (cS 3 1, 1), (cS 5 1, 1), (cC 3, 1), (cC 5, 1)]),
  (2, [(cS 0 3, 1), (cS 1 5, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 6, 1), (cR 0, 1), (cR 2, 1), (cC 1, 1)]),
  (2, [(cS 0 1, 1), (cS 0 3, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 5 2, 1), (cR 3, 1), (cC 2, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 2 1, 1), (cS 3 5, 1), (cS 6 0, 1), (cR 0, 1), (cR 4, 1), (cR 5, 1), (cC 1, 1), (cC 3, 1)]),
  (1, [(cS 2 5, 1), (cS 4 5, 1), (cC 0, 1), (cC 2, 1)]),
  (1, [(cS 0 2, 1), (cS 2 1, 1), (cS 2 5, 1), (cS 4 3, 1), (cS 4 5, 1), (cC 0, 1)]),
  (2, [(cS 0 3, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 2 6, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 3, 1), (cR 3, 1), (cC 1, 1), (cC 2, 1), (cC 4, 1)]),
  (2, [(cS 0 0, 1), (cS 0 2, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 3, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cC 0, 1), (cC 2, 1), (cC 5, 1)]),
  (1, [(cS 2 4, 1), (cS 2 6, 1), (cS 4 4, 1), (cS 4 6, 1), (cS 5 0, 1), (cR 0, 1)]),
  (2, [(cS 2 4, 1), (cS 2 6, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 1, 1), (cS 5 4, 1), (cS 6 2, 1), (cS 6 3, 1), (cR 0, 1), (cR 1, 1)]),
  (1, [(cS 1 6, 1), (cC 0, 1), (cC 2, 1)]),
  (1, [(cS 0 2, 1), (cS 1 1, 1), (cS 1 6, 1), (cS 3 1, 1), (cS 4 4, 1), (cS 6 0, 1)]),
  (1, [(cS 1 6, 1), (cS 4 4, 1), (cC 1, 1), (cC 3, 1)]),
  (1, [(cS 0 2, 1), (cS 2 2, 1), (cC 0, 1), (cC 5, 1)]),
  (1, [(cS 1 0, 1), (cS 1 5, 1), (cS 3 0, 1), (cS 3 5, 1), (cC 2, 1)]),
  (2, [(cS 0 2, 1), (cS 1 1, 1), (cS 1 6, 1), (cS 2 1, 1), (cS 2 5, 1), (cS 2 6, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 4 4, 1), (cS 4 6, 2), (cR 0, 1), (cC 4, 1)]),
  (1, [(cC 0, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cS 0 0, 1), (cS 0 2, 1), (cS 1 4, 1), (cS 2 3, 1), (cS 3 6, 1), (cS 4 5, 1), (cS 5 0, 1), (cS 5 2, 1)]),
  (1, [(cS 0 1, 1), (cS 0 3, 1), (cS 6 0, 1), (cR 2, 1), (cR 4, 1)]),
  (2, [(cS 0 1, 1), (cS 1 1, 1), (cS 2 0, 1), (cS 2 5, 1), (cS 3 6, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 1, 1), (cC 2, 1), (cC 3, 1), (cC 4, 1)]),
  (2, [(cS 0 0, 1), (cS 0 2, 1), (cS 0 4, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 4 0, 1), (cS 4 2, 1), (cS 5 0, 1), (cS 5 2, 1), (cS 6 0, 1), (cS 6 2, 1)]),
  (2, [(cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 1 3, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 2 4, 2), (cS 3 2, 1), (cS 4 4, 1), (cS 6 0, 1), (cR 4, 1), (cC 0, 1)]),
  (1, [(cS 3 5, 1), (cS 5 4, 1), (cC 1, 1), (cC 3, 1)]),
  (1, [(cS 0 3, 1), (cS 2 3, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cS 1 0, 1), (cS 1 4, 1), (cR 3, 1), (cC 2, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cS 5 0, 1), (cS 5 2, 1), (cR 0, 1), (cR 2, 1)]),
  (1, [(cS 0 2, 1), (cS 3 2, 1), (cS 3 4, 1), (cS 4 4, 1), (cS 6 0, 1), (cR 1, 1)]),
  (1, [(cS 1 0, 1), (cS 1 5, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cS 2 0, 1), (cS 2 3, 1), (cS 2 5, 1), (cS 4 6, 1), (cS 5 0, 1), (cR 0, 1)]),
  (2, [(cS 0 1, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 3, 1), (cS 2 4, 2), (cS 3 6, 2), (cS 5 2, 1), (cC 2, 1)]),
  (2, [(cS 4 3, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 6 2, 1), (cS 6 4, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)]),
  (1, [(cS 5 0, 1), (cR 0, 1), (cR 2, 1)]),
  (2, [(cS 4 0, 1), (cS 4 2, 1), (cS 5 2, 1), (cS 6 2, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)]),
  (1, [(cS 4 4, 1), (cS 6 2, 1), (cS 6 4, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 6 1, 1), (cS 6 3, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 1, 1), (cR 4, 1), (cR 6, 1)]),
  (2, [(cS 0 3, 1), (cS 1 0, 1), (cS 1 3, 1), (cS 1 5, 1), (cS 2 6, 1), (cS 4 0, 1), (cS 4 2, 1), (cR 3, 1), (cR 5, 1), (cR 6, 1), (cC 5, 1)]),
  (1, [(cC 0, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cC 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 0 3, 1), (cS 0 5, 1), (cS 2 6, 1), (cS 3 1, 1), (cS 3 3, 1), (cR 5, 1)]),
  (1, [(cS 0 3, 1), (cS 0 5, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 3 4, 1), (cR 5, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (2, [(cS 0 3, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 4, 1), (cS 5 0, 2), (cS 6 3, 1), (cS 6 4, 1), (cR 1, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cS 5 2, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 1, 1), (cR 3, 1)]),
  (2, [(cS 0 3, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 4 3, 1), (cS 6 3, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (2, [(cS 1 3, 1), (cS 1 5, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 2, 1), (cS 3 4, 1), (cR 0, 1), (cR 4, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cS 3 6, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 5, 1), (cC 3, 1)]),
  (1, [(cS 0 5, 1), (cS 3 5, 1), (cS 5 5, 1), (cC 0, 1), (cC 3, 1)]),
  (1, [(cC 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 3 1, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 5, 1), (cC 3, 1)]),
  (1, [(cS 3 1, 1), (cS 5 0, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 1 3, 1), (cS 2 3, 1), (cS 3 6, 1), (cS 5 6, 1), (cS 6 3, 1), (cS 6 5, 1), (cC 1, 1)]),
  (1, [(cS 3 0, 1), (cS 3 5, 1), (cC 2, 1), (cC 4, 1)]),
  (2, [(cS 0 6, 1), (cS 1 1, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 4 5, 1), (cS 5 6, 1), (cS 6 1, 1), (cS 6 5, 1), (cC 2, 1), (cC 3, 1), (cC 4, 1)]),
  (1, [(cS 0 3, 1), (cS 0 5, 1), (cS 2 3, 1), (cS 2 5, 1), (cR 5, 1)]),
  (1, [(cS 0 0, 1), (cS 5 0, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 4 1, 1), (cS 6 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cC 0, 1), (cC 3, 1), (cC 5, 1)]),
  (2, [(cS 0 3, 1), (cS 0 5, 2), (cS 1 3, 1), (cS 2 4, 1), (cS 2 6, 1), (cS 3 2, 1), (cS 4 2, 1), (cS 4 6, 2), (cS 5 2, 1), (cS 6 2, 1), (cS 6 4, 2), (cR 2, 1)]),
  (1, [(cS 2 0, 1), (cS 4 0, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 0 3, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 5 0, 1), (cS 5 3, 1), (cC 5, 1)]),
  (2, [(cS 0 5, 1), (cS 1 3, 1), (cS 2 1, 2), (cS 2 5, 1), (cS 3 3, 1), (cS 4 1, 2), (cS 5 2, 1), (cS 6 2, 1), (cS 6 4, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 1 1, 1), (cS 3 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 6 2, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 3 3, 1), (cS 3 5, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 3 4, 1), (cS 3 6, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 3 4, 1), (cS 3 6, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 2 1, 1), (cS 4 0, 1), (cS 4 2, 1), (cS 5 5, 1), (cS 5 6, 1), (cR 0, 1), (cR 6, 1), (cC 1, 1), (cC 3, 1)]),
  (1, [(cS 2 1, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 6 3, 1), (cR 0, 1)]),
  (1, [(cS 4 5, 1), (cS 6 5, 1), (cC 1, 1), (cC 3, 1)]),
  (1, [(cS 0 3, 1), (cS 6 4, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cS 1 0, 1), (cS 1 4, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 6 4, 1), (cC 2, 1)]),
  (1, [(cS 0 2, 1), (cS 1 1, 1), (cS 3 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 1 5, 1), (cS 2 0, 1), (cR 0, 1), (cR 5, 1)]),
  (2, [(cS 0 2, 1), (cS 1 6, 1), (cS 3 3, 1), (cR 0, 1), (cR 5, 1), (cC 0, 1), (cC 4, 1), (cC 5, 1)]),
  (2, [(cS 1 5, 1), (cS 2 0, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 4 5, 1), (cR 0, 1), (cR 1, 1), (cR 5, 1), (cR 6, 1)]),
  (2, [(cS 2 0, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 4 0, 1), (cS 4 5, 1), (cR 0, 1), (cR 1, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cS 2 0, 1), (cS 2 5, 1), (cS 4 6, 1), (cS 5 2, 1), (cS 5 4, 1), (cR 0, 1)]),
  (1, [(cS 0 1, 1), (cS 0 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 1 6, 1), (cS 2 1, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 3 1, 1), (cS 4 2, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cS 2 1, 1), (cS 2 6, 1), (cS 3 4, 1), (cS 5 3, 1), (cS 5 5, 1), (cR 0, 1)]),
  (1, [(cS 3 0, 1), (cS 3 1, 1), (cS 3 5, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cS 2 3, 1), (cR 0, 1), (cR 5, 1)]),
  (2, [(cS 1 1, 1), (cS 1 3, 1), (cS 2 0, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 3, 1), (cS 3 5, 1), (cR 0, 1), (cR 4, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 2 3, 1), (cS 3 6, 1), (cS 5 0, 1), (cS 5 3, 1), (cS 5 5, 1), (cR 0, 1)]),
  (1, [(cS 0 1, 1), (cS 0 3, 1), (cS 2 3, 1), (cS 3 6, 1), (cS 5 2, 1), (cS 6 4, 1)]),
  (2, [(cS 0 1, 1), (cS 1 1, 1), (cS 2 0, 1), (cS 3 6, 1), (cS 4 6, 1), (cS 6 5, 1), (cC 2, 1), (cC 3, 1), (cC 4, 1), (cC 5, 1)]),
  (1, [(cS 2 1, 1), (cS 2 3, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 6 5, 1), (cC 1, 1), (cC 3, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 6, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (1, [(cS 5 2, 1), (cS 5 4, 1), (cR 0, 1), (cR 2, 1)]),
  (2, [(cS 3 2, 1), (cS 3 4, 1), (cS 4 3, 1), (cS 4 5, 1), (cS 5 4, 1), (cS 5 5, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 6, 1)]),
  (1, [(cS 3 6, 1), (cS 5 4, 1), (cS 5 6, 1), (cR 0, 1), (cR 2, 1)]),
  (1, [(cS 5 4, 1), (cS 5 6, 1), (cR 0, 1), (cR 2, 1)])
]
private def p4Certs1 : List (Nat × List (Constr2D × Nat)) := [
  (1, [(cS 1 3, 1), (cS 1 5, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 1 2, 1), (cS 1 4, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 1 3, 1), (cS 1 5, 1), (cS 3 3, 1), (cS 3 5, 1), (cR 5, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 3 1, 1), (cS 3 3, 1), (cR 1, 1), (cR 5, 1)]),
  (1, [(cS 5 4, 1), (cS 5 6, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 0 1, 1), (cS 0 6, 1), (cS 1 1, 1), (cS 1 6, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cS 4 3, 1), (cS 5 2, 1), (cC 0, 1), (cC 5, 1)]),
  (1, [(cS 0 4, 1), (cS 2 4, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cS 1 4, 1), (cS 1 6, 1), (cS 4 3, 1), (cS 6 3, 1), (cS 6 6, 1), (cC 1, 1)]),
  (1, [(cC 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 5 1, 1), (cS 5 3, 1), (cS 5 5, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 0 0, 1), (cS 0 5, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 3 5, 1), (cR 5, 1)]),
  (1, [(cS 1 3, 1), (cS 2 3, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 6, 1)]),
  (1, [(cS 0 0, 1), (cS 6 6, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 0 0, 1), (cS 0 4, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 5 1, 1), (cC 6, 1)]),
  (1, [(cS 1 0, 1), (cS 5 1, 1), (cS 6 0, 1), (cC 3, 1), (cC 5, 1)]),
  (2, [(cS 0 0, 1), (cS 1 3, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 3 3, 1), (cS 4 3, 1), (cC 0, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 1 4, 1), (cS 1 6, 1), (cS 2 3, 1), (cS 3 5, 1), (cS 4 3, 1), (cS 6 6, 1), (cC 1, 1)]),
  (2, [(cS 1 3, 1), (cS 1 4, 1), (cS 2 2, 1), (cS 3 3, 1), (cS 3 4, 1), (cC 0, 1), (cC 1, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cS 5 1, 1), (cS 5 3, 1), (cR 1, 1), (cR 3, 1)]),
  (2, [(cS 4 1, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 5, 1), (cS 6 0, 1), (cS 6 6, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 4 3, 1), (cS 5 5, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 0 3, 1), (cS 0 5, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 0 4, 1), (cS 0 6, 1), (cS 1 3, 1), (cS 1 5, 1), (cS 2 5, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cC 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 0 4, 1), (cS 1 5, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 6 6, 1), (cR 5, 1)]),
  (1, [(cS 1 1, 1), (cS 3 0, 1), (cC 4, 1), (cC 6, 1)]),
  (2, [(cS 0 3, 1), (cS 0 5, 1), (cS 2 0, 1), (cS 2 5, 1), (cS 5 2, 1), (cS 5 4, 1), (cS 6 1, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 1, 1), (cR 3, 1), (cR 4, 1)]),
  (1, [(cS 0 5, 1), (cS 3 5, 1), (cR 5, 1), (cC 3, 1)]),
  (1, [(cS 0 5, 1), (cS 1 2, 1), (cS 2 3, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 4, 1)]),
  (1, [(cS 2 1, 1), (cS 2 3, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cS 6 4, 1), (cS 6 6, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cS 3 0, 1), (cS 3 5, 1), (cC 2, 1), (cC 4, 1)]),
  (2, [(cS 1 3, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 4 1, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 3, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cS 0 5, 1), (cS 2 5, 1), (cR 5, 1), (cC 3, 1)]),
  (1, [(cS 1 2, 1), (cS 3 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 4 1, 1), (cS 6 1, 1), (cC 3, 1), (cC 5, 1)]),
  (4, [(cS 0 3, 1), (cS 0 4, 1), (cS 0 5, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 2 2, 2), (cS 2 3, 1), (cS 3 1, 2), (cS 3 4, 1), (cS 4 1, 1), (cR 2, 1), (cR 5, 2), (cR 6, 1), (cC 1, 1), (cC 4, 1), (cC 6, 2)]),
  (1, [(cS 0 4, 1), (cS 5 4, 1), (cR 2, 1), (cC 6, 1)]),
  (1, [(cS 0 6, 1), (cS 1 4, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 6 4, 1), (cR 2, 1)]),
  (2, [(cS 1 5, 2), (cS 2 1, 1), (cS 2 2, 1), (cS 3 1, 1), (cS 5 6, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 4, 1), (cC 3, 1), (cC 4, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (2, [(cS 0 4, 1), (cS 0 5, 1), (cS 5 4, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 1 4, 1), (cS 6 4, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cS 1 0, 1), (cS 2 1, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cC 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 1 0, 1), (cS 1 2, 1), (cS 4 4, 1), (cS 5 2, 1), (cS 6 4, 1), (cR 3, 1)]),
  (1, [(cC 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cR 1, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cS 1 1, 1), (cS 6 1, 1), (cC 4, 1), (cC 6, 1)]),
  (2, [(cS 0 0, 1), (cS 1 0, 1), (cS 3 0, 1), (cS 4 2, 1), (cS 5 2, 1), (cS 6 1, 1), (cC 3, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cS 1 4, 1), (cS 6 4, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cC 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 1 4, 1), (cS 3 4, 1), (cS 6 4, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cC 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 3 1, 1), (cS 4 2, 1), (cS 4 4, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cS 0 0, 1), (cS 0 5, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 4 1, 1), (cS 4 6, 1), (cC 4, 1)]),
  (1, [(cS 0 0, 1), (cS 2 3, 1), (cS 5 1, 1), (cS 6 4, 1), (cC 6, 1)]),
  (1, [(cS 0 0, 1), (cS 0 6, 1), (cS 1 3, 1), (cS 3 3, 1), (cS 6 4, 1), (cR 5, 1)]),
  (1, [(cC 0, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 0 4, 1), (cS 1 0, 1), (cS 2 3, 1), (cS 3 5, 1), (cS 4 3, 1), (cS 5 2, 1), (cS 5 4, 1)]),
  (1, [(cS 2 3, 1), (cS 6 4, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cS 0 0, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 6 4, 1), (cC 6, 1)]),
  (1, [(cS 1 0, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 6 4, 1)]),
  (1, [(cS 0 0, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cC 0, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cS 4 4, 1), (cS 6 4, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 2 0, 1), (cS 2 3, 1), (cS 2 5, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cC 0, 1), (cC 3, 1), (cC 5, 1)]),
  (3, [(cS 1 0, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 3, 2), (cS 2 5, 1), (cS 3 5, 1), (cS 3 6, 2), (cS 4 0, 1), (cS 4 1, 3), (cS 5 3, 1), (cS 6 0, 1), (cS 6 4, 2), (cS 6 5, 1), (cR 0, 2), (cR 2, 1)]),
  (1, [(cS 0 0, 1), (cS 1 0, 1), (cS 5 6, 1), (cC 3, 1), (cC 5, 1)]),
  (2, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 0, 1), (cS 1 3, 1), (cS 1 6, 1), (cS 2 3, 1), (cS 2 5, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 5 2, 1), (cR 6, 1), (cC 4, 1)]),
  (1, [(cC 0, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (2, [(cS 4 1, 1), (cS 4 2, 1), (cS 5 3, 1), (cS 6 0, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)]),
  (1, [(cS 6 1, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 1, 1), (cR 3, 1)]),
  (2, [(cS 5 4, 1), (cS 6 1, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1)]),
  (1, [(cS 0 2, 1), (cS 0 4, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 0 2, 1), (cS 1 5, 1), (cS 3 3, 1), (cS 3 5, 1), (cR 5, 1)]),
  (1, [(cS 0 2, 1), (cS 1 5, 1), (cS 2 4, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 3, 1)]),
  (1, [(cS 0 2, 1), (cS 1 5, 1), (cS 3 1, 1), (cS 4 3, 1), (cR 5, 1)]),
  (1, [(cS 0 2, 1), (cS 1 5, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 4 4, 1), (cS 5 6, 1)]),
  (1, [(cS 0 2, 1), (cS 1 5, 1), (cS 5 1, 1), (cS 5 3, 1), (cS 5 5, 1), (cR 3, 1)]),
  (2, [(cS 1 2, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 3 5, 2), (cS 6 1, 1), (cS 6 6, 1), (cR 0, 1), (cR 4, 1), (cR 5, 1), (cC 3, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 6, 1)]),
  (1, [(cS 0 6, 1), (cS 5 6, 1), (cC 1, 1), (cC 3, 1)]),
  (1, [(cS 1 2, 1), (cS 1 4, 1), (cS 5 4, 1), (cS 5 6, 1), (cS 6 2, 1), (cR 3, 1)]),
  (2, [(cS 0 1, 1), (cS 0 3, 1), (cS 1 2, 1), (cS 1 4, 1), (cS 6 1, 1), (cS 6 2, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1)]),
  (1, [(cS 0 2, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 3 4, 1), (cS 3 6, 1), (cR 5, 1)]),
  (1, [(cS 1 5, 1), (cS 6 6, 1), (cC 1, 1), (cC 3, 1)]),
  (2, [(cS 1 2, 1), (cS 1 4, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 2 5, 1), (cS 3 3, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 5 6, 1), (cS 6 2, 1), (cR 0, 1), (cC 6, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 1 5, 1), (cS 5 6, 1), (cC 1, 1), (cC 3, 1)]),
  (2, [(cS 0 2, 2), (cS 1 4, 2), (cS 1 6, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 4, 1), (cS 3 5, 1), (cS 5 6, 1), (cC 6, 1)]),
  (1, [(cS 5 1, 1), (cS 6 2, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 0 2, 1), (cS 1 5, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 5 6, 1), (cC 3, 1)]),
  (1, [(cS 1 5, 1), (cS 3 5, 1), (cC 1, 1), (cC 3, 1)]),
  (1, [(cS 4 3, 1), (cS 5 5, 1), (cS 6 2, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 1 3, 1), (cS 6 3, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cS 1 3, 1), (cS 4 3, 1), (cS 6 2, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cS 0 0, 1), (cS 0 2, 1), (cS 2 1, 1), (cS 2 4, 1), (cS 4 4, 1), (cC 6, 1)]),
  (1, [(cS 3 5, 1), (cS 4 4, 1), (cC 0, 1), (cC 2, 1)]),
  (1, [(cS 0 2, 1), (cS 5 2, 1), (cC 0, 1), (cC 5, 1)]),
  (1, [(cR 1, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cS 0 1, 1), (cS 0 2, 1), (cS 0 4, 1), (cS 2 4, 1), (cS 4 4, 1), (cC 6, 1)]),
  (1, [(cS 1 5, 1), (cS 3 5, 1), (cS 4 4, 1), (cC 0, 1), (cC 2, 1)]),
  (1, [(cS 3 1, 1), (cS 5 1, 1), (cR 1, 1), (cR 6, 1)]),
  (2, [(cS 0 2, 1), (cS 1 0, 1), (cS 2 1, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 5 6, 1), (cS 6 0, 1), (cR 0, 1), (cR 2, 1), (cC 5, 1)]),
  (1, [(cS 1 5, 1), (cS 3 5, 1), (cC 0, 1), (cC 2, 1)]),
  (1, [(cS 0 2, 1), (cS 1 0, 1), (cS 1 5, 1), (cS 2 1, 1), (cS 4 4, 1), (cS 6 0, 1), (cS 6 6, 1)]),
  (1, [(cS 4 3, 1), (cS 6 2, 1), (cR 1, 1), (cC 1, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cS 0 1, 1), (cS 5 1, 1), (cC 3, 1), (cC 6, 1)]),
  (1, [(cS 0 6, 1), (cS 2 6, 1), (cS 5 6, 1), (cC 1, 1), (cC 3, 1)]),
  (1, [(cS 4 3, 1), (cS 4 5, 1), (cS 5 6, 1), (cR 0, 1), (cR 2, 1)]),
  (2, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 4, 1), (cS 1 0, 1), (cS 3 5, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 5 0, 1), (cS 5 1, 1), (cR 2, 1), (cC 2, 1), (cC 3, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 6, 1)]),
  (1, [(cS 0 1, 1), (cS 0 3, 1), (cS 2 1, 1), (cS 2 3, 1), (cC 6, 1)]),
  (1, [(cS 0 3, 1), (cS 1 0, 1), (cS 2 3, 1), (cS 3 6, 1), (cS 5 3, 1), (cC 1, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 6, 1)]),
  (1, [(cS 0 6, 1), (cS 2 6, 1), (cC 1, 1), (cC 3, 1)]),
  (2, [(cS 0 0, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 4 3, 1), (cS 5 5, 1), (cS 6 1, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (3, [(cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 1 4, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 4, 1), (cS 4 6, 1), (cS 5 6, 1), (cS 6 0, 1), (cR 0, 1), (cR 2, 1), (cC 5, 1), (cC 6, 1)]),
  (2, [(cS 3 3, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 1, 1), (cS 6 3, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1)]),
  (2, [(cS 0 1, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 3, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 6 0, 1), (cS 6 2, 1), (cS 6 6, 1), (cR 1, 1), (cC 5, 1)]),
  (2, [(cS 1 0, 1), (cS 2 4, 1), (cS 4 0, 1), (cS 4 1, 1), (cS 4 4, 1), (cS 6 1, 2), (cR 1, 1), (cC 2, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cS 5 0, 1), (cS 5 5, 1), (cR 0, 1), (cR 2, 1)]),
  (2, [(cS 0 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 4, 1), (cS 3 5, 1), (cC 0, 1), (cC 1, 1), (cC 2, 1), (cC 3, 1)]),
  (1, [(cS 6 1, 1), (cS 6 3, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 0 2, 1), (cS 0 4, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 2 5, 1), (cS 4 1, 1), (cS 4 4, 1), (cS 4 6, 1), (cR 0, 1), (cR 1, 1), (cR 3, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cR 1, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cS 1 2, 1), (cS 4 2, 1), (cS 6 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (2, [(cS 0 2, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 2 6, 1), (cS 3 0, 1), (cS 3 1, 1), (cR 0, 1), (cR 4, 1), (cR 5, 1), (cR 6, 1)]),
  (2, [(cS 0 2, 1), (cS 0 3, 1), (cS 1 1, 1), (cS 2 0, 1), (cS 3 0, 1), (cS 5 3, 1), (cS 5 6, 1), (cS 6 2, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cS 3 0, 1), (cS 3 5, 1), (cS 4 1, 1), (cS 6 1, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 1, 1)]),
  (2, [(cS 0 2, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 2 0, 2), (cS 2 6, 1), (cS 3 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 6, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (2, [(cS 0 2, 1), (cS 0 3, 1), (cS 1 1, 1), (cS 2 0, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 4 3, 1), (cS 5 3, 1), (cS 6 2, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cS 0 2, 1), (cS 0 3, 1), (cS 0 5, 1), (cS 2 3, 1), (cS 3 5, 1), (cR 5, 1)]),
  (2, [(cS 1 2, 1), (cS 1 4, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 3 1, 1), (cS 3 3, 1), (cR 0, 1), (cR 4, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cC 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (4, [(cS 0 3, 1), (cS 0 4, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 2 3, 2), (cS 3 0, 1), (cS 4 5, 1), (cS 5 0, 1), (cS 5 4, 1), (cS 6 2, 1), (cS 6 3, 1), (cS 6 5, 2), (cR 3, 1), (cR 5, 1), (cC 1, 2), (cC 2, 1), (cC 4, 1), (cC 6, 2)]),
  (2, [(cS 0 2, 1), (cS 0 4, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 4 4, 1), (cS 4 6, 1), (cS 5 4, 1), (cS 5 6, 1), (cS 6 2, 1), (cS 6 3, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 2, 1), (cR 3, 1)]),
  (1, [(cS 1 1, 1), (cS 1 3, 1), (cS 5 1, 1), (cS 6 2, 1), (cS 6 4, 1), (cR 3, 1)]),
  (2, [(cS 0 2, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 4 0, 1), (cS 4 5, 1), (cS 5 6, 1), (cS 6 5, 1), (cS 6 6, 1), (cC 2, 1), (cC 3, 1), (cC 4, 1)]),
  (1, [(cS 0 5, 1), (cS 5 5, 1), (cC 1, 1), (cC 3, 1)]),
  (1, [(cS 3 1, 1), (cS 3 6, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cS 2 2, 1), (cS 2 4, 1), (cS 2 6, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 1 2, 1), (cS 3 2, 1), (cS 6 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cC 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 1 2, 1), (cS 6 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 0 2, 1), (cS 0 4, 1), (cS 0 6, 1), (cR 2, 1), (cR 5, 1)]),
  (1, [(cS 1 5, 1), (cS 6 5, 1), (cC 1, 1), (cC 3, 1)]),
  (2, [(cS 2 2, 1), (cS 3 0, 1), (cS 3 4, 1), (cS 3 5, 1), (cS 4 6, 1), (cS 5 3, 1), (cS 6 2, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1)]),
  (1, [(cS 1 1, 1), (cS 3 1, 1), (cS 6 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 3 0, 1), (cS 3 5, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 3 2, 1), (cS 3 4, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 0 3, 1), (cS 0 4, 1), (cS 4 5, 1), (cS 5 3, 1), (cS 5 4, 1), (cS 6 5, 1), (cC 0, 1), (cC 1, 1), (cC 2, 1), (cC 6, 1)]),
  (2, [(cS 2 1, 1), (cS 3 5, 1), (cS 5 3, 1), (cS 5 5, 1), (cR 0, 1), (cC 0, 1), (cC 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 0 3, 1), (cS 1 0, 1), (cS 3 6, 1), (cS 5 3, 1), (cS 6 4, 1), (cC 1, 1)]),
  (1, [(cS 2 0, 1), (cS 2 1, 1), (cS 3 3, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 0 4, 1), (cS 3 4, 1), (cS 5 4, 1), (cC 0, 1), (cC 2, 1)]),
  (1, [(cS 0 0, 1), (cS 2 0, 1), (cS 3 6, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cS 1 4, 1), (cS 1 6, 1), (cR 0, 1), (cR 5, 1)]),
  (3, [(cS 0 2, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 6 1, 1), (cS 6 2, 1), (cS 6 3, 1), (cR 0, 1), (cR 1, 1), (cR 5, 1), (cC 0, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (2, [(cS 2 4, 1), (cS 2 6, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 4, 1), (cR 0, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cS 4 2, 1), (cS 4 4, 1), (cS 5 6, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cR 1, 1), (cR 4, 1), (cR 6, 1)]),
  (2, [(cS 0 1, 1), (cS 0 2, 1), (cS 3 2, 1), (cS 5 2, 1), (cC 0, 1), (cC 3, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (1, [(cS 3 1, 1), (cS 5 1, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 6, 1)]),
  (2, [(cS 1 5, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 3 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 2, 1), (cS 5 4, 1), (cR 0, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cS 2 2, 1), (cS 2 3, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 2 3, 1), (cS 3 5, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 2 3, 1), (cS 3 5, 1), (cR 0, 1), (cR 5, 1)]),
  (4, [(cS 0 1, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 2 6, 1), (cS 3 3, 1), (cS 4 0, 1), (cS 4 3, 1), (cS 4 5, 2), (cS 4 6, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 0, 1), (cR 1, 1), (cR 5, 1), (cR 6, 1), (cC 0, 1), (cC 2, 1), (cC 3, 1), (cC 4, 1)]),
  (1, [(cS 0 0, 1), (cS 2 0, 1), (cS 5 1, 1), (cC 2, 1), (cC 4, 1)]),
  (2, [(cS 0 0, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 2 6, 1), (cS 3 5, 1), (cS 4 5, 1), (cS 6 1, 1), (cS 6 4, 1), (cC 2, 1), (cC 3, 1), (cC 4, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (1, [(cS 0 0, 1), (cS 2 6, 1), (cS 6 4, 1), (cC 1, 1), (cC 3, 1)]),
  (2, [(cS 0 0, 1), (cS 0 1, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 2 0, 1), (cS 2 2, 1), (cS 3 6, 1), (cS 6 2, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 3, 1), (cC 4, 1)]),
  (1, [(cC 0, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (1, [(cS 2 3, 1), (cS 3 0, 1), (cS 3 5, 1), (cR 1, 1), (cR 6, 1)]),
  (3, [(cS 1 0, 1), (cS 3 3, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 3, 1), (cS 6 0, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 6, 1), (cC 2, 1), (cC 4, 1), (cC 5, 1)]),
  (1, [(cS 5 3, 1), (cS 5 5, 1), (cR 0, 1), (cR 2, 1)])
]
private def p4Certs2 : List (Nat × List (Constr2D × Nat)) := [
  (1, [(cS 1 3, 1), (cS 1 5, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 1 2, 1), (cS 1 4, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 1 3, 1), (cS 1 5, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 5 1, 1), (cS 5 2, 1), (cS 5 6, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 0 0, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 3 4, 1), (cS 3 5, 1), (cR 4, 1), (cR 5, 1), (cC 0, 1), (cC 2, 1)]),
  (1, [(cS 4 3, 1), (cS 5 2, 1), (cC 0, 1), (cC 5, 1)]),
  (1, [(cS 0 4, 1), (cS 2 4, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cS 1 4, 1), (cS 1 6, 1), (cS 4 3, 1), (cS 6 3, 1), (cS 6 6, 1), (cC 1, 1)]),
  (1, [(cC 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 5 1, 1), (cS 5 3, 1), (cS 5 5, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 0 0, 1), (cS 1 3, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 0 0, 1), (cS 1 1, 1), (cS 2 3, 1), (cS 3 1, 1), (cS 4 2, 1), (cS 5 0, 1), (cS 6 0, 1), (cR 2, 1), (cR 4, 1), (cC 6, 1)]),
  (1, [(cS 1 2, 1), (cS 2 4, 1), (cS 3 2, 1), (cS 4 4, 1), (cS 5 2, 1), (cC 0, 1)]),
  (1, [(cS 1 0, 1), (cS 6 0, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 0 0, 1), (cS 0 4, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 5 1, 1), (cC 6, 1)]),
  (1, [(cS 1 0, 1), (cS 5 1, 1), (cS 6 0, 1), (cC 3, 1), (cC 5, 1)]),
  (2, [(cS 0 0, 1), (cS 1 3, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 3 3, 1), (cS 4 3, 1), (cC 0, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 1 4, 1), (cS 1 6, 1), (cS 2 3, 1), (cS 3 5, 1), (cS 4 3, 1), (cS 6 6, 1), (cC 1, 1)]),
  (2, [(cS 1 3, 1), (cS 1 4, 1), (cS 2 2, 1), (cS 3 3, 1), (cS 3 4, 1), (cC 0, 1), (cC 1, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cS 5 1, 1), (cS 5 3, 1), (cR 1, 1), (cR 3, 1)]),
  (2, [(cS 4 1, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 5, 1), (cS 6 0, 1), (cS 6 6, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 4 3, 1), (cS 5 5, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 0 4, 1), (cS 0 6, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 0 4, 1), (cS 0 6, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 4, 1), (cS 2 6, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cC 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 0 3, 1), (cS 1 5, 1), (cS 3 1, 1), (cS 4 3, 1), (cS 6 5, 1), (cR 5, 1)]),
  (1, [(cS 2 1, 1), (cS 4 1, 1), (cC 4, 1), (cC 6, 1)]),
  (2, [(cS 0 6, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 5 2, 1), (cR 1, 1), (cR 3, 1), (cR 4, 1), (cR 6, 1), (cC 4, 1)]),
  (1, [(cS 0 6, 1), (cS 1 3, 1), (cS 6 4, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cR 2, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cR 2, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cR 2, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cS 6 1, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 2, 1), (cR 4, 1)]),
  (2, [(cS 1 0, 1), (cS 1 3, 1), (cS 1 4, 1), (cS 2 3, 1), (cS 4 1, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 4, 2), (cR 3, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cS 5 0, 1), (cS 5 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 1 2, 1), (cS 3 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 1 2, 1), (cS 1 6, 1), (cS 3 2, 1), (cS 3 6, 1), (cS 5 2, 1), (cS 6 6, 1), (cC 4, 1)]),
  (1, [(cS 2 1, 1), (cS 4 1, 1), (cS 5 0, 1), (cC 3, 1), (cC 5, 1)]),
  (2, [(cS 0 4, 1), (cS 4 0, 1), (cS 5 4, 1), (cS 6 0, 1), (cR 2, 1), (cC 1, 1), (cC 3, 1), (cC 5, 1), (cC 6, 1)]),
  (2, [(cS 0 3, 1), (cS 0 5, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 5 3, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)]),
  (2, [(cS 1 5, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 3 1, 1), (cS 4 0, 1), (cS 4 2, 1), (cS 5 6, 1), (cS 6 6, 1), (cC 3, 1), (cC 4, 1), (cC 5, 1)]),
  (1, [(cS 2 1, 1), (cS 4 1, 1), (cS 6 1, 1), (cC 3, 1), (cC 5, 1)]),
  (3, [(cS 2 1, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 4 1, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 1, 1), (cR 2, 1), (cR 4, 1), (cC 3, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cS 0 0, 1), (cS 0 5, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 6 4, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cS 1 0, 1), (cS 2 1, 1), (cR 4, 1), (cR 6, 1)]),
  (2, [(cS 0 0, 1), (cS 1 1, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 3 1, 2), (cS 3 4, 1), (cS 4 6, 1), (cS 5 4, 1), (cS 6 0, 1), (cS 6 5, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 0 4, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 5 2, 1), (cS 5 4, 1), (cR 3, 1)]),
  (1, [(cC 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cR 1, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cS 1 1, 1), (cS 6 1, 1), (cC 4, 1), (cC 6, 1)]),
  (2, [(cS 0 0, 1), (cS 1 0, 1), (cS 3 0, 1), (cS 4 2, 1), (cS 5 2, 1), (cS 6 1, 1), (cC 3, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cS 1 4, 1), (cS 6 4, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cC 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 1 4, 1), (cS 3 4, 1), (cS 6 4, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cC 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 3 1, 1), (cS 4 2, 1), (cS 4 4, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cS 0 0, 1), (cS 0 5, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 4 1, 1), (cS 4 6, 1), (cC 4, 1)]),
  (1, [(cS 0 0, 1), (cS 2 3, 1), (cS 3 6, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 5, 1)]),
  (1, [(cS 0 0, 1), (cS 0 5, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 3 5, 1), (cR 5, 1)]),
  (2, [(cS 0 0, 1), (cS 2 3, 1), (cS 3 5, 1), (cS 4 3, 2), (cS 4 5, 1), (cS 4 6, 1), (cS 5 4, 1), (cS 6 4, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 2, 1), (cC 0, 1)]),
  (1, [(cS 0 0, 1), (cS 0 4, 1), (cS 2 3, 1), (cS 5 2, 1), (cS 5 4, 1), (cR 3, 1)]),
  (1, [(cS 2 1, 1), (cS 2 3, 1), (cS 4 2, 1), (cS 4 5, 1), (cS 6 5, 1), (cC 0, 1)]),
  (2, [(cS 0 0, 1), (cS 1 1, 1), (cS 2 3, 1), (cS 3 1, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 6 5, 1), (cR 2, 1), (cC 0, 1), (cC 5, 1)]),
  (1, [(cS 1 0, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 6 5, 1)]),
  (1, [(cS 0 0, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cC 0, 1), (cC 2, 1), (cC 4, 1)]),
  (2, [(cS 0 6, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 5 3, 1), (cS 5 5, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1)]),
  (1, [(cS 2 0, 1), (cS 2 3, 1), (cS 2 5, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cC 0, 1), (cC 3, 1), (cC 5, 1)]),
  (3, [(cS 1 0, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 3, 2), (cS 2 5, 1), (cS 3 5, 1), (cS 3 6, 2), (cS 4 0, 1), (cS 4 1, 3), (cS 5 3, 1), (cS 6 0, 1), (cS 6 4, 2), (cS 6 5, 1), (cR 0, 2), (cR 2, 1)]),
  (1, [(cS 0 0, 1), (cS 1 0, 1), (cS 5 6, 1), (cC 3, 1), (cC 5, 1)]),
  (2, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 0, 1), (cS 1 3, 1), (cS 1 6, 1), (cS 2 3, 1), (cS 2 5, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 5 2, 1), (cR 6, 1), (cC 4, 1)]),
  (1, [(cC 0, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (2, [(cS 4 1, 1), (cS 4 2, 1), (cS 5 3, 1), (cS 6 0, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)]),
  (1, [(cS 6 1, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 1, 1), (cR 3, 1)]),
  (2, [(cS 5 4, 1), (cS 6 1, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1)]),
  (1, [(cS 0 2, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 0 2, 1), (cS 1 5, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 0 2, 1), (cS 1 5, 1), (cS 2 4, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 3, 1)]),
  (1, [(cS 0 2, 1), (cS 1 5, 1), (cS 3 1, 1), (cS 4 3, 1), (cS 5 0, 1), (cS 5 2, 1)]),
  (1, [(cS 0 2, 1), (cS 1 5, 1), (cS 4 4, 1), (cS 5 6, 1), (cR 3, 1)]),
  (1, [(cS 1 5, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 4 4, 1), (cC 2, 1)]),
  (2, [(cS 0 2, 1), (cS 0 4, 1), (cS 1 3, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 6 0, 2), (cR 2, 1), (cR 4, 1), (cR 5, 1), (cC 2, 1)]),
  (1, [(cS 3 6, 1), (cS 5 6, 1), (cC 1, 1), (cC 3, 1)]),
  (1, [(cC 0, 1), (cC 2, 1), (cC 4, 1)]),
  (2, [(cS 0 2, 1), (cS 0 3, 1), (cS 1 3, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 6, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 5 6, 1), (cR 3, 1), (cC 1, 1)]),
  (3, [(cS 0 1, 1), (cS 0 3, 1), (cS 2 6, 1), (cS 4 0, 1), (cS 4 5, 1), (cS 4 6, 1), (cR 2, 1), (cR 3, 1), (cR 5, 1), (cC 1, 1), (cC 2, 1), (cC 3, 1), (cC 4, 1)]),
  (1, [(cS 5 1, 1), (cS 5 6, 1), (cS 6 2, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 1 5, 1), (cS 4 0, 1), (cS 6 0, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cS 0 2, 1), (cS 2 2, 1), (cS 4 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cC 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 0 3, 1), (cS 1 5, 1), (cS 2 4, 1), (cS 3 0, 1), (cS 5 0, 1), (cC 2, 1)]),
  (2, [(cS 0 3, 1), (cS 1 5, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 6, 1), (cR 0, 1), (cR 2, 1), (cC 1, 1)]),
  (2, [(cS 0 1, 1), (cS 0 3, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 5 2, 1), (cR 3, 1), (cC 2, 1)]),
  (2, [(cS 0 2, 2), (cS 0 3, 1), (cS 1 5, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 1, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 5, 1), (cS 6 0, 2), (cR 1, 1), (cR 3, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cS 0 0, 1), (cS 0 2, 1), (cR 3, 1), (cR 5, 1)]),
  (2, [(cS 0 0, 1), (cS 0 2, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 6, 1), (cS 6 0, 1), (cS 6 2, 1), (cR 5, 1)]),
  (1, [(cS 4 4, 1), (cC 0, 1), (cC 2, 1)]),
  (2, [(cS 0 0, 1), (cS 0 2, 2), (cS 2 1, 1), (cS 3 5, 1), (cS 4 4, 2), (cS 4 6, 1), (cS 5 6, 1), (cR 2, 1), (cC 0, 1)]),
  (1, [(cS 1 0, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 4 4, 1), (cC 2, 1)]),
  (1, [(cS 0 2, 1), (cS 5 2, 1), (cC 0, 1), (cC 5, 1)]),
  (1, [(cR 1, 1), (cR 4, 1), (cR 6, 1)]),
  (1, [(cS 0 1, 1), (cS 0 2, 1), (cS 0 4, 1), (cS 2 4, 1), (cS 4 4, 1), (cC 6, 1)]),
  (1, [(cS 1 5, 1), (cS 3 5, 1), (cS 4 4, 1), (cC 0, 1), (cC 2, 1)]),
  (1, [(cS 3 1, 1), (cS 5 1, 1), (cR 1, 1), (cR 6, 1)]),
  (2, [(cS 0 2, 1), (cS 1 0, 1), (cS 2 1, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 5 6, 1), (cS 6 0, 1), (cR 0, 1), (cR 2, 1), (cC 5, 1)]),
  (1, [(cS 1 5, 1), (cS 3 5, 1), (cC 0, 1), (cC 2, 1)]),
  (1, [(cS 0 2, 1), (cS 1 0, 1), (cS 1 5, 1), (cS 2 1, 1), (cS 4 4, 1), (cS 6 0, 1), (cS 6 6, 1)]),
  (1, [(cS 4 3, 1), (cS 6 2, 1), (cR 1, 1), (cC 1, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cS 0 0, 1), (cS 0 2, 1), (cS 1 4, 1), (cS 2 3, 1), (cS 3 6, 1), (cS 4 5, 1), (cS 5 0, 1), (cS 5 2, 1)]),
  (1, [(cC 0, 1), (cC 2, 1), (cC 4, 1)]),
  (2, [(cS 0 2, 1), (cS 0 3, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 4 3, 1), (cS 4 5, 1), (cS 5 4, 1), (cS 6 1, 1), (cC 0, 1), (cC 6, 1)]),
  (1, [(cS 0 4, 1), (cS 1 0, 1), (cS 2 4, 1), (cS 3 6, 1), (cS 4 4, 1), (cC 2, 1)]),
  (1, [(cS 1 4, 1), (cS 3 4, 1), (cC 0, 1), (cC 2, 1)]),
  (1, [(cS 0 3, 1), (cS 2 3, 1), (cC 1, 1), (cC 6, 1)]),
  (1, [(cS 1 0, 1), (cS 1 4, 1), (cR 3, 1), (cC 2, 1)]),
  (1, [(cS 0 3, 1), (cS 2 4, 1), (cS 4 4, 1), (cC 0, 1), (cC 2, 1)]),
  (1, [(cC 0, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (3, [(cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 1 4, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 4, 1), (cS 4 6, 1), (cS 5 6, 1), (cS 6 0, 1), (cR 0, 1), (cR 2, 1), (cC 5, 1), (cC 6, 1)]),
  (2, [(cS 3 3, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 1, 1), (cS 6 3, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1)]),
  (2, [(cS 0 1, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 3, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 6 0, 1), (cS 6 2, 1), (cS 6 6, 1), (cR 1, 1), (cC 5, 1)]),
  (2, [(cS 1 0, 1), (cS 2 4, 1), (cS 4 0, 1), (cS 4 1, 1), (cS 4 4, 1), (cS 6 1, 2), (cR 1, 1), (cC 2, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cS 5 0, 1), (cS 5 5, 1), (cR 0, 1), (cR 2, 1)]),
  (2, [(cS 0 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 4, 1), (cS 3 5, 1), (cC 0, 1), (cC 1, 1), (cC 2, 1), (cC 3, 1)]),
  (1, [(cS 6 1, 1), (cS 6 3, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 4, 1)]),
  (1, [(cR 0, 1), (cR 3, 1), (cR 5, 1)]),
  (1, [(cS 3 1, 1), (cS 3 6, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 3 1, 1), (cS 3 3, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 5 4, 1), (cS 5 6, 1), (cR 0, 1), (cR 3, 1)]),
  (1, [(cS 0 2, 1), (cS 0 4, 1), (cS 5 2, 1), (cS 5 4, 1), (cR 3, 1)]),
  (2, [(cS 0 2, 1), (cS 0 4, 1), (cS 2 4, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 3 5, 1), (cS 4 1, 1), (cR 1, 1), (cR 5, 1), (cR 6, 1), (cC 6, 1)]),
  (1, [(cS 1 5, 1), (cS 3 5, 1), (cS 4 3, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 0 2, 1), (cS 5 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cC 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 1 5, 1), (cS 3 1, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 0 2, 1), (cS 1 4, 1), (cS 2 1, 1), (cS 3 4, 1), (cS 6 4, 1), (cC 6, 1)]),
  (2, [(cS 0 3, 1), (cS 0 5, 1), (cS 1 0, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 5 4, 1), (cS 6 3, 1), (cS 6 5, 1), (cC 1, 1), (cC 2, 1)]),
  (2, [(cS 0 2, 1), (cS 1 5, 1), (cS 2 1, 2), (cS 2 6, 1), (cS 4 4, 1), (cS 5 3, 1), (cS 5 6, 2), (cS 6 5, 1), (cR 0, 1), (cC 4, 1)]),
  (2, [(cS 0 3, 1), (cS 1 5, 1), (cS 3 1, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 4, 1), (cS 6 2, 1), (cS 6 3, 1), (cS 6 5, 2), (cR 1, 1), (cC 1, 1)]),
  (1, [(cS 0 2, 1), (cS 2 1, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 2 3, 1), (cS 3 6, 1), (cR 0, 1), (cR 5, 1)]),
  (2, [(cS 1 2, 1), (cS 1 3, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 2, 1), (cS 3 4, 1), (cR 0, 1), (cR 4, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cC 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cS 3 6, 1), (cS 5 6, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cS 5 6, 1), (cS 6 5, 1), (cC 1, 1), (cC 3, 1)]),
  (1, [(cS 1 3, 1), (cS 2 3, 1), (cS 3 6, 1), (cS 5 6, 1), (cS 6 3, 1), (cS 6 5, 1), (cC 1, 1)]),
  (1, [(cS 3 0, 1), (cS 3 5, 1), (cC 2, 1), (cC 4, 1)]),
  (2, [(cS 0 2, 2), (cS 2 1, 1), (cS 2 2, 1), (cS 2 5, 1), (cS 3 1, 1), (cS 5 6, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 4, 1), (cC 3, 1), (cC 4, 1)]),
  (1, [(cS 2 0, 1), (cS 4 0, 1), (cC 2, 1), (cC 4, 1)]),
  (2, [(cS 0 6, 1), (cS 1 1, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 4 5, 1), (cS 5 6, 1), (cS 6 1, 1), (cS 6 5, 1), (cC 2, 1), (cC 3, 1), (cC 4, 1)]),
  (1, [(cS 0 1, 1), (cS 0 3, 1), (cS 0 5, 1), (cS 2 3, 1), (cS 2 5, 1), (cR 5, 1)]),
  (1, [(cS 1 2, 1), (cS 3 2, 1), (cS 6 2, 1), (cC 4, 1), (cC 6, 1)]),
  (3, [(cS 0 5, 1), (cS 1 3, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 4, 2), (cS 2 6, 1), (cS 4 6, 1), (cS 5 2, 1), (cS 5 4, 1), (cS 6 4, 2), (cR 0, 1), (cR 3, 1), (cC 2, 2), (cC 6, 1)]),
  (1, [(cS 0 2, 1), (cS 0 6, 1), (cS 2 2, 1), (cS 2 6, 1), (cS 4 2, 1), (cS 5 6, 1), (cC 4, 1)]),
  (1, [(cS 0 5, 1), (cS 2 5, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cC 2, 1), (cC 4, 1), (cC 6, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (1, [(cC 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 6 2, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 1, 1), (cR 3, 1)]),
  (1, [(cS 1 1, 1), (cS 3 1, 1), (cS 6 1, 1), (cC 3, 1), (cC 5, 1)]),
  (1, [(cS 3 6, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 3 3, 1), (cS 3 5, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 3 4, 1), (cS 3 6, 1), (cS 5 4, 1), (cS 5 6, 1), (cR 0, 1)]),
  (1, [(cS 3 2, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 5 2, 1), (cS 5 4, 1), (cR 0, 1)]),
  (2, [(cS 2 1, 1), (cS 2 6, 1), (cS 3 1, 1), (cS 4 1, 1), (cS 5 6, 1), (cR 0, 1), (cR 1, 1), (cR 5, 1), (cR 6, 1)]),
  (1, [(cS 0 1, 1), (cS 0 3, 1), (cS 2 1, 1), (cS 6 4, 1), (cC 6, 1)]),
  (2, [(cS 0 3, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 3 1, 1), (cS 3 6, 2), (cS 5 2, 1), (cS 6 2, 1), (cS 6 4, 2), (cC 1, 1)]),
  (1, [(cS 2 1, 1), (cS 2 6, 1), (cS 3 3, 1), (cS 5 4, 1), (cS 5 6, 1), (cR 0, 1)]),
  (4, [(cS 0 0, 3), (cS 0 3, 1), (cS 0 4, 2), (cS 1 0, 1), (cS 1 1, 1), (cS 1 2, 1), (cS 2 0, 2), (cS 2 6, 1), (cS 3 1, 2), (cS 4 1, 2), (cS 4 3, 2), (cS 4 4, 1), (cS 5 4, 2), (cS 6 2, 1), (cR 6, 1), (cC 2, 2), (cC 4, 1)]),
  (1, [(cS 0 2, 1), (cS 1 0, 1), (cS 2 1, 1), (cS 3 6, 1), (cC 4, 1)]),
  (1, [(cS 1 4, 1), (cS 1 6, 1), (cR 0, 1), (cR 5, 1)]),
  (3, [(cS 0 2, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 6 1, 1), (cS 6 2, 1), (cS 6 3, 1), (cR 0, 1), (cR 1, 1), (cR 5, 1), (cC 0, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (2, [(cS 2 4, 1), (cS 2 6, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 4, 1), (cR 0, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cS 4 2, 1), (cS 4 4, 1), (cS 5 6, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cR 1, 1), (cR 4, 1), (cR 6, 1)]),
  (2, [(cS 0 1, 1), (cS 0 2, 1), (cS 3 2, 1), (cS 5 2, 1), (cC 0, 1), (cC 3, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (1, [(cS 3 1, 1), (cS 5 1, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 6, 1)]),
  (2, [(cS 1 5, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 3 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 2, 1), (cS 5 4, 1), (cR 0, 1), (cR 1, 1), (cR 6, 1)]),
  (1, [(cS 2 3, 1), (cS 2 5, 1), (cR 0, 1), (cR 5, 1)]),
  (1, [(cS 2 3, 1), (cS 3 6, 1), (cS 5 4, 1), (cS 5 6, 1), (cR 0, 1)]),
  (1, [(cS 2 3, 1), (cS 3 6, 1), (cS 5 2, 1), (cS 6 4, 1), (cR 0, 1)]),
  (2, [(cS 1 0, 1), (cS 1 2, 1), (cS 3 2, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 5 6, 2), (cR 0, 1), (cR 2, 1), (cR 6, 1), (cC 4, 1)]),
  (1, [(cS 0 0, 1), (cS 2 0, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cS 1 0, 1), (cS 3 6, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (5, [(cS 0 0, 2), (cS 1 0, 1), (cS 1 1, 1), (cS 2 0, 1), (cS 2 6, 1), (cS 3 0, 1), (cS 3 1, 2), (cS 3 3, 1), (cS 4 1, 2), (cS 5 2, 1), (cS 5 5, 1), (cS 6 5, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 6, 2), (cC 2, 2), (cC 3, 2), (cC 4, 1)]),
  (1, [(cR 1, 1), (cR 3, 1), (cR 6, 1)]),
  (1, [(cS 0 0, 1), (cS 2 0, 1), (cS 4 0, 1), (cC 2, 1), (cC 4, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (1, [(cR 0, 1), (cR 2, 1), (cR 5, 1)]),
  (1, [(cS 2 3, 1), (cS 3 0, 1), (cS 3 5, 1), (cR 1, 1), (cR 6, 1)]),
  (3, [(cS 1 0, 1), (cS 3 3, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 3, 1), (cS 6 0, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 6, 1), (cC 2, 1), (cC 4, 1), (cC 5, 1)]),
  (1, [(cS 5 3, 1), (cS 5 5, 1), (cR 0, 1), (cR 2, 1)])
]

private def p5Certs0 : List P5Cert := [
  .root (5, [(cS 2 1, 1), (cS 3 1, 4), (cS 3 6, 5), (cS 4 2, 2), (cS 4 3, 2), (cS 4 4, 2), (cS 4 5, 2), (cS 5 0, 2), (cS 5 1, 2), (cS 5 6, 2), (cS 6 0, 1), (cR 4, 1)], [(cS 0 2, 1), (cS 0 4, 1), (cS 1 0, 1), (cS 1 6, 1), (cS 2 2, 2), (cS 2 4, 2), (cS 2 5, 3), (cS 3 3, 3), (cS 6 3, 2), (cS 6 5, 2), (cR 0, 1), (cR 1, 3), (cR 6, 3)]),
  .root (6, [(cS 0 6, 2), (cS 1 5, 3), (cS 1 6, 1), (cS 2 6, 2), (cS 3 4, 4), (cS 3 6, 4), (cS 6 0, 2), (cR 4, 2), (cR 5, 4)], [(cS 0 1, 2), (cS 0 2, 2), (cS 1 0, 2), (cS 1 3, 3), (cS 2 1, 2), (cS 2 2, 2), (cS 3 1, 3), (cS 3 3, 4), (cS 6 3, 3), (cS 6 5, 4), (cS 6 6, 1), (cR 1, 1), (cR 6, 1), (cC 1, 1), (cC 4, 2)]),
  .root (10, [(cS 1 5, 5), (cS 1 6, 5), (cS 2 1, 2), (cS 2 2, 2), (cS 3 1, 4), (cS 4 2, 4), (cS 4 4, 4), (cS 5 0, 4), (cS 6 0, 2), (cR 3, 4), (cR 4, 2), (cR 5, 4)], [(cS 0 1, 2), (cS 0 2, 2), (cS 1 0, 2), (cS 1 1, 3), (cS 1 3, 3), (cS 2 3, 2), (cS 2 4, 4), (cS 3 6, 6), (cS 4 6, 4), (cS 6 5, 2), (cS 6 6, 2), (cR 1, 3), (cR 6, 6), (cC 3, 2), (cC 4, 2)]),
  .root (2, [(cS 2 1, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 4 0, 1), (cS 4 2, 1), (cS 5 1, 1), (cS 5 3, 1), (cS 6 0, 1), (cS 6 2, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 4 4, 1), (cS 6 4, 1), (cC 4, 1)]),
  .root (4, [(cS 2 1, 2), (cS 3 0, 1), (cS 3 1, 2), (cS 4 4, 4), (cS 5 0, 1), (cC 0, 1), (cC 5, 2), (cC 6, 2)], [(cS 0 0, 1), (cS 0 1, 2), (cS 1 0, 1), (cS 5 1, 2), (cS 6 5, 2), (cC 2, 2), (cC 3, 2), (cC 4, 2)]),
  .root (2, [(cS 1 5, 1), (cS 1 6, 1), (cS 2 0, 1), (cS 2 5, 1), (cS 3 1, 2), (cS 3 6, 1), (cS 4 2, 1), (cS 4 4, 1), (cR 4, 1)], [(cS 1 1, 1), (cS 1 3, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 4, 1), (cR 0, 1), (cR 5, 1), (cR 6, 1)]),
  .root (20, [(cS 2 3, 10), (cS 2 4, 10), (cS 3 0, 5), (cS 3 3, 5), (cS 3 4, 3), (cS 3 5, 5), (cS 3 6, 13), (cS 4 2, 3), (cS 4 3, 3), (cS 4 4, 3), (cS 4 5, 3), (cS 5 0, 3), (cS 5 1, 3), (cS 5 6, 3), (cS 6 0, 4), (cR 3, 2), (cR 4, 4), (cR 5, 10)], [(cS 0 1, 6), (cS 0 2, 4), (cS 0 4, 3), (cS 1 3, 3), (cS 1 5, 3), (cS 1 6, 6), (cS 2 0, 3), (cS 2 1, 9), (cS 3 1, 9), (cS 3 2, 3), (cS 6 3, 6), (cS 6 4, 7), (cS 6 5, 6), (cS 6 6, 7), (cR 0, 3), (cR 1, 11), (cR 6, 7)]),
  .root (6, [(cS 2 1, 1), (cS 2 2, 1), (cS 2 3, 5), (cS 2 4, 4), (cS 3 0, 1), (cS 3 1, 4), (cS 3 4, 2), (cS 4 2, 3), (cS 4 3, 2), (cS 4 4, 1), (cS 4 5, 2), (cS 5 0, 3), (cS 6 0, 1), (cR 4, 1), (cR 5, 2)], [(cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 0 4, 1), (cS 1 0, 1), (cS 1 5, 1), (cS 3 6, 5), (cS 5 3, 1), (cS 5 4, 1), (cS 6 5, 1), (cR 1, 4), (cR 6, 4), (cC 6, 1)]),
  .root (6, [(cS 1 3, 1), (cS 2 3, 2), (cS 3 1, 2), (cS 4 2, 2), (cS 5 1, 3), (cS 5 2, 1), (cS 5 6, 1), (cS 6 0, 3), (cR 2, 3), (cR 3, 1), (cR 4, 3), (cC 6, 2)], [(cS 0 1, 2), (cS 0 2, 2), (cS 1 0, 1), (cS 1 5, 1), (cS 1 6, 2), (cS 4 4, 4), (cS 6 2, 1), (cS 6 3, 3), (cS 6 5, 3), (cR 1, 3), (cR 6, 1), (cC 4, 2)]),
  .root (6, [(cS 2 2, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 4 3, 1), (cS 4 4, 2), (cS 4 5, 1), (cS 5 6, 2), (cS 6 0, 2), (cS 6 6, 2), (cR 2, 4), (cR 4, 3)], [(cS 0 1, 2), (cS 0 2, 2), (cS 0 3, 2), (cS 1 0, 2), (cS 1 4, 2), (cS 1 5, 2), (cS 1 6, 2), (cS 4 2, 2), (cS 5 1, 2), (cS 5 2, 2), (cS 5 3, 2), (cS 6 4, 2), (cS 6 5, 2), (cR 1, 2), (cR 6, 2)]),
  .root (1, [(cR 2, 1), (cR 4, 1)], [(cR 1, 1), (cR 6, 1)]),
  .splitS0 [.leaf (8, [(cS 0 5, 3), (cS 1 3, 4), (cS 1 4, 4), (cS 1 6, 4), (cS 2 3, 1), (cS 3 3, 4), (cS 3 5, 4), (cS 4 1, 2), (cS 4 2, 3), (cS 4 3, 1), (cS 4 4, 3), (cS 5 0, 1), (cS 5 1, 1), (cS 6 0, 2), (cS 6 6, 1), (cR 2, 3), (cR 5, 4), (cC 5, 1)], [(cS 0 0, 3), (cS 0 1, 1), (cS 0 2, 4), (cS 1 0, 1), (cS 1 1, 3), (cS 2 1, 5), (cS 3 0, 5), (cS 3 1, 3), (cS 4 6, 3), (cS 6 2, 1), (cS 6 3, 1), (cS 6 4, 5), (cS 6 5, 1), (cR 6, 2)]), .leaf (10, [(cS 1 3, 2), (cS 1 5, 4), (cS 2 0, 1), (cS 2 3, 3), (cS 2 6, 2), (cS 3 2, 4), (cS 3 3, 2), (cS 3 4, 5), (cS 3 5, 3), (cS 4 1, 2), (cS 4 2, 1), (cS 4 3, 2), (cS 5 0, 1), (cS 5 1, 1), (cS 5 4, 2), (cS 6 0, 2), (cS 6 6, 1), (cR 1, 4), (cR 5, 6), (cC 3, 1), (cC 5, 2)], [(cS 0 1, 1), (cS 0 3, 1), (cS 0 4, 3), (cS 1 0, 3), (cS 1 2, 3), (cS 2 1, 7), (cS 3 0, 4), (cS 3 1, 3), (cS 3 6, 3), (cS 4 0, 1), (cS 4 6, 2), (cS 6 2, 2), (cR 0, 6), (cR 6, 1)]), .leaf (3, [(cS 1 5, 1), (cS 2 3, 1), (cS 2 6, 1), (cS 3 2, 1), (cS 3 3, 1), (cS 3 4, 1), (cS 3 5, 2), (cS 4 2, 1), (cS 4 4, 1), (cS 5 0, 1), (cR 1, 2), (cR 5, 2)], [(cS 1 1, 1), (cS 2 1, 2), (cS 3 0, 2), (cS 3 1, 1), (cS 4 6, 1), (cR 0, 2), (cR 6, 1)]), .leaf (5, [(cS 1 5, 3), (cS 2 3, 4), (cS 2 6, 1), (cS 3 4, 3), (cS 4 1, 1), (cS 4 2, 3), (cS 4 3, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 4, 2), (cS 6 0, 1), (cS 6 6, 1), (cR 5, 1), (cC 0, 1), (cC 3, 1), (cC 5, 2)], [(cS 0 1, 1), (cS 0 3, 1), (cS 0 4, 3), (cS 1 0, 3), (cS 1 2, 3), (cS 2 1, 2), (cS 3 1, 3), (cS 3 6, 3), (cS 4 6, 2), (cS 6 2, 2), (cR 0, 1), (cR 6, 1)]), .leaf (6, [(cS 1 2, 1), (cS 1 5, 4), (cS 1 6, 1), (cS 2 0, 2), (cS 2 3, 4), (cS 3 3, 2), (cS 3 4, 2), (cS 3 5, 3), (cS 4 2, 3), (cS 5 0, 1), (cS 6 0, 1), (cS 6 2, 1), (cR 1, 1), (cR 4, 1), (cR 5, 4), (cC 4, 1)], [(cS 0 3, 2), (cS 1 1, 2), (cS 2 1, 4), (cS 2 6, 2), (cS 3 0, 1), (cS 3 1, 2), (cS 3 6, 1), (cS 4 0, 3), (cS 4 6, 1), (cS 6 5, 1), (cR 0, 4), (cR 6, 1)]), .leaf (12, [(cS 1 5, 1), (cS 1 6, 1), (cS 2 3, 3), (cS 3 2, 4), (cS 3 3, 3), (cS 3 4, 3), (cS 3 5, 3), (cS 4 1, 2), (cS 4 3, 3), (cS 5 0, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 0, 4), (cS 6 6, 1), (cR 1, 7), (cR 2, 2), (cR 4, 2), (cR 5, 6), (cC 4, 1), (cC 5, 3)], [(cS 0 1, 1), (cS 0 2, 1), (cS 0 4, 1), (cS 1 0, 1), (cS 1 1, 4), (cS 2 1, 8), (cS 2 6, 1), (cS 3 0, 6), (cS 3 1, 4), (cS 3 6, 3), (cS 4 0, 2), (cS 4 6, 1), (cS 6 2, 3), (cS 6 3, 1), (cS 6 4, 3), (cS 6 5, 1), (cR 0, 6), (cR 6, 1)]), .leaf (8, [(cS 1 5, 4), (cS 1 6, 2), (cS 2 2, 2), (cS 2 3, 5), (cS 2 6, 3), (cS 3 2, 1), (cS 3 3, 3), (cS 3 4, 1), (cS 3 5, 3), (cS 4 1, 2), (cS 4 2, 2), (cS 4 3, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 0, 2), (cS 6 6, 1), (cR 5, 4), (cC 3, 1), (cC 4, 2), (cC 5, 2)], [(cS 0 1, 1), (cS 0 3, 1), (cS 0 4, 3), (cS 1 0, 3), (cS 1 2, 3), (cS 2 1, 5), (cS 3 0, 5), (cS 3 1, 3), (cS 4 6, 3), (cS 6 2, 2), (cR 0, 4), (cR 6, 1)]), .leaf (2, [(cS 0 5, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 5 0, 1), (cR 1, 1), (cR 2, 1), (cR 5, 1)], [(cS 1 1, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 4 6, 1), (cR 0, 1), (cR 6, 1)]), .leaf (8, [(cS 0 5, 2), (cS 1 3, 4), (cS 1 4, 3), (cS 1 5, 1), (cS 1 6, 4), (cS 2 2, 3), (cS 2 3, 1), (cS 2 5, 2), (cS 3 2, 2), (cS 3 3, 2), (cS 3 4, 4), (cS 4 2, 1), (cS 4 3, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 0, 3), (cR 4, 2), (cR 5, 4), (cC 4, 1), (cC 5, 1)], [(cS 0 0, 1), (cS 0 1, 1), (cS 0 2, 4), (cS 1 0, 3), (cS 1 1, 3), (cS 2 1, 5), (cS 3 0, 3), (cS 3 1, 3), (cS 3 6, 4), (cS 6 3, 1), (cS 6 4, 4), (cS 6 5, 1), (cR 6, 3), (cC 6, 1)]), .leaf (20, [(cS 1 3, 9), (cS 1 4, 8), (cS 1 5, 8), (cS 1 6, 8), (cS 2 3, 11), (cS 3 2, 6), (cS 3 3, 3), (cS 3 4, 6), (cS 3 5, 10), (cS 4 2, 7), (cS 4 3, 4), (cS 4 4, 7), (cS 5 0, 6), (cS 5 1, 4), (cS 6 0, 4), (cR 5, 10), (cC 5, 4)], [(cS 0 0, 2), (cS 0 1, 7), (cS 0 2, 6), (cS 0 3, 3), (cS 1 0, 5), (cS 1 1, 6), (cS 1 2, 2), (cS 2 1, 13), (cS 3 0, 13), (cS 3 1, 7), (cS 6 3, 4), (cS 6 4, 6), (cS 6 5, 7), (cR 6, 7), (cC 6, 7)]), .leaf (10, [(cS 0 4, 2), (cS 1 3, 2), (cS 1 5, 2), (cS 1 6, 2), (cS 2 3, 4), (cS 3 3, 4), (cS 3 4, 4), (cS 4 1, 3), (cS 4 2, 2), (cS 4 3, 4), (cS 4 4, 2), (cS 5 1, 1), (cS 6 0, 3), (cS 6 6, 1), (cR 1, 2), (cR 2, 2), (cR 5, 4), (cC 0, 2), (cC 5, 4)], [(cS 0 1, 1), (cS 1 0, 2), (cS 1 1, 3), (cS 1 2, 2), (cS 2 1, 5), (cS 3 1, 5), (cS 3 6, 6), (cS 4 6, 4), (cS 6 2, 5), (cS 6 3, 1), (cS 6 4, 5), (cS 6 5, 1), (cR 0, 4)]), .leaf (2, [(cS 0 5, 1), (cS 1 3, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 3, 1), (cS 2 5, 1), (cS 3 2, 1), (cS 3 4, 1), (cS 6 0, 1), (cR 4, 1), (cR 5, 1)], [(cS 0 2, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 3 6, 2), (cS 6 4, 1), (cR 6, 1)])],
  .root (6, [(cS 0 5, 1), (cS 1 3, 2), (cS 1 4, 2), (cS 1 5, 1), (cS 2 3, 1), (cS 2 4, 2), (cS 2 5, 1), (cS 3 0, 1), (cS 3 3, 1), (cS 4 2, 3), (cS 4 5, 1), (cS 5 0, 1), (cS 5 1, 2), (cS 5 2, 1), (cR 3, 1), (cR 5, 1), (cC 0, 2), (cC 3, 1), (cC 5, 2), (cC 6, 2)], [(cS 0 0, 2), (cS 0 1, 2), (cS 0 2, 2), (cS 0 3, 1), (cS 1 1, 2), (cS 2 0, 2), (cS 2 1, 2), (cS 2 2, 2), (cS 3 1, 2), (cS 4 4, 6), (cS 6 2, 2), (cS 6 3, 1), (cS 6 4, 5), (cS 6 5, 1)]),
  .root (1, [(cC 4, 1), (cC 6, 1)], [(cS 6 4, 1), (cC 1, 1), (cC 3, 1)]),
  .root (5, [(cS 1 4, 1), (cS 1 5, 4), (cS 1 6, 1), (cS 2 3, 1), (cS 2 4, 3), (cS 2 6, 1), (cS 3 0, 2), (cS 3 3, 1), (cS 3 5, 2), (cS 3 6, 2), (cS 4 2, 3), (cS 4 4, 4), (cS 5 2, 1), (cR 4, 1)], [(cS 0 3, 1), (cS 0 6, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 2 0, 3), (cS 2 2, 3), (cS 3 1, 1), (cS 5 6, 1), (cS 6 4, 1), (cR 0, 3), (cR 5, 3), (cR 6, 1), (cC 1, 1)]),
  .root (6, [(cS 0 4, 2), (cS 0 6, 1), (cS 1 3, 1), (cS 1 5, 2), (cS 1 6, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 0, 1), (cS 4 0, 2), (cS 4 2, 3), (cS 5 0, 1), (cS 5 1, 3), (cS 5 2, 3), (cS 5 6, 1), (cS 6 0, 2), (cS 6 6, 2), (cR 1, 2), (cR 2, 2), (cR 3, 3)], [(cS 0 0, 1), (cS 0 1, 3), (cS 0 2, 3), (cS 0 3, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 3 6, 1), (cS 4 4, 6), (cS 4 6, 5), (cS 6 3, 3), (cS 6 4, 3), (cS 6 5, 3)]),
  .root (12, [(cS 0 5, 3), (cS 1 5, 5), (cS 1 6, 1), (cS 2 2, 6), (cS 2 3, 6), (cS 2 4, 6), (cS 2 5, 2), (cS 3 1, 4), (cS 3 2, 2), (cS 4 3, 4), (cS 4 4, 8), (cS 6 6, 4), (cC 0, 8), (cC 5, 4)], [(cS 0 1, 6), (cS 0 3, 9), (cS 0 4, 3), (cS 1 0, 3), (cS 1 1, 3), (cS 3 6, 7), (cS 4 2, 3), (cS 4 6, 5), (cS 5 1, 1), (cS 5 2, 2), (cS 5 3, 1), (cS 6 2, 3), (cS 6 4, 8), (cS 6 5, 1), (cR 5, 3), (cC 2, 3)]),
  .splitS0 [.leaf (24, [(cS 0 5, 6), (cS 1 3, 6), (cS 1 4, 4), (cS 1 5, 9), (cS 1 6, 7), (cS 2 2, 3), (cS 2 3, 5), (cS 3 0, 1), (cS 3 1, 5), (cS 3 5, 3), (cS 4 1, 8), (cS 4 2, 6), (cS 4 3, 8), (cS 4 4, 7), (cS 4 5, 1), (cS 5 2, 10), (cS 5 4, 6), (cS 5 5, 7), (cR 1, 2), (cR 2, 8), (cR 3, 10), (cC 4, 3)], [(cS 0 2, 3), (cS 0 3, 1), (cS 1 0, 4), (cS 1 1, 9), (cS 1 2, 4), (cS 3 6, 1), (cS 4 0, 11), (cS 4 6, 7), (cS 5 0, 8), (cS 5 1, 2), (cS 5 5, 7), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 3), (cR 0, 8), (cR 6, 13), (cC 0, 3), (cC 6, 2)]), .leaf (6, [(cS 0 5, 2), (cS 1 5, 2), (cS 2 3, 2), (cS 3 1, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 5 2, 2), (cS 5 4, 2), (cR 1, 2), (cR 2, 2), (cR 3, 4), (cR 4, 1), (cR 5, 2)], [(cS 0 2, 2), (cS 0 3, 2), (cS 0 4, 2), (cS 1 1, 2), (cS 4 0, 1), (cS 4 6, 3), (cS 6 6, 2), (cR 0, 2), (cR 6, 2), (cC 0, 2)]), .leaf (4, [(cS 0 5, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 4 4, 1), (cS 5 1, 2), (cS 5 2, 1), (cS 5 3, 2), (cS 5 4, 1), (cR 1, 2), (cR 2, 1), (cR 3, 2), (cR 4, 1), (cC 5, 1)], [(cS 0 1, 2), (cS 0 3, 2), (cS 0 4, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 4 6, 4), (cS 5 0, 1), (cS 6 5, 1), (cS 6 6, 2), (cR 0, 1), (cR 6, 1)]), .leaf (24, [(cS 0 5, 7), (cS 1 3, 8), (cS 1 5, 8), (cS 1 6, 3), (cS 2 2, 1), (cS 2 3, 3), (cS 3 0, 1), (cS 3 1, 3), (cS 4 1, 7), (cS 4 2, 5), (cS 4 3, 6), (cS 4 4, 5), (cS 5 2, 9), (cS 5 3, 3), (cS 5 4, 4), (cS 5 5, 6), (cR 1, 3), (cR 2, 10), (cR 3, 10), (cR 4, 3), (cC 4, 3), (cC 5, 3)], [(cS 0 1, 1), (cS 0 2, 2), (cS 1 0, 5), (cS 1 1, 8), (cS 1 2, 3), (cS 4 0, 11), (cS 4 6, 10), (cS 5 0, 9), (cS 5 1, 4), (cS 6 4, 1), (cR 0, 10), (cR 6, 13), (cC 6, 3)]), .leaf (24, [(cS 0 5, 7), (cS 1 3, 4), (cS 1 5, 11), (cS 2 3, 6), (cS 3 1, 5), (cS 3 4, 2), (cS 3 5, 3), (cS 4 1, 5), (cS 4 2, 8), (cS 4 3, 2), (cS 4 4, 6), (cS 5 2, 8), (cS 5 3, 5), (cS 5 4, 8), (cS 5 5, 7), (cR 1, 6), (cR 2, 8), (cR 3, 11), (cR 4, 3)], [(cS 0 1, 5), (cS 0 3, 5), (cS 0 4, 5), (cS 1 0, 5), (cS 1 1, 6), (cS 1 2, 5), (cS 1 3, 6), (cS 4 0, 10), (cS 4 6, 8), (cS 5 0, 8), (cS 5 1, 6), (cR 0, 8), (cR 6, 11), (cC 6, 6)]), .leaf (12, [(cS 1 3, 5), (cS 1 5, 7), (cS 1 6, 3), (cS 2 2, 1), (cS 2 3, 2), (cS 3 1, 3), (cS 4 1, 3), (cS 4 2, 2), (cS 4 3, 4), (cS 4 4, 2), (cS 5 1, 1), (cS 5 2, 5), (cS 5 4, 3), (cS 5 5, 1), (cR 2, 4), (cR 3, 5), (cR 4, 1), (cC 4, 2), (cC 5, 3)], [(cS 0 2, 1), (cS 0 4, 1), (cS 1 0, 3), (cS 1 1, 4), (cS 1 2, 3), (cS 3 6, 1), (cS 4 0, 2), (cS 4 6, 7), (cS 5 0, 4), (cR 0, 4), (cR 6, 7), (cC 0, 1), (cC 6, 1)]), .leaf (12, [(cS 0 5, 2), (cS 1 3, 6), (cS 1 4, 6), (cS 1 5, 2), (cS 1 6, 6), (cS 2 2, 1), (cS 2 3, 2), (cS 3 1, 2), (cS 4 3, 3), (cS 4 4, 6), (cS 5 1, 3), (cS 5 2, 6), (cS 5 5, 1), (cR 2, 3), (cR 3, 7), (cR 4, 3), (cC 5, 2)], [(cS 0 0, 2), (cS 0 2, 4), (cS 1 0, 2), (cS 1 1, 7), (cS 1 2, 2), (cS 4 0, 5), (cS 4 6, 5), (cS 6 1, 1), (cS 6 4, 4), (cS 6 6, 3), (cR 6, 8), (cC 0, 1), (cC 6, 1)]), .leaf (24, [(cS 0 5, 7), (cS 1 3, 2), (cS 1 4, 2), (cS 1 5, 2), (cS 1 6, 5), (cS 2 2, 3), (cS 2 3, 3), (cS 3 0, 2), (cS 3 1, 3), (cS 4 2, 2), (cS 4 3, 3), (cS 5 1, 2), (cS 5 2, 7), (cS 5 4, 5), (cR 1, 7), (cR 2, 9), (cR 3, 10), (cR 4, 9), (cR 5, 4), (cC 4, 3), (cC 5, 3)], [(cS 0 1, 6), (cS 0 3, 1), (cS 1 0, 4), (cS 1 1, 5), (cS 1 2, 5), (cS 3 6, 3), (cS 4 6, 21), (cS 5 0, 6), (cS 5 1, 3), (cS 5 6, 3), (cS 6 3, 5), (cS 6 5, 6), (cS 6 6, 6), (cR 0, 9), (cR 6, 9)]), .leaf (3, [(cS 0 5, 1), (cS 1 3, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 4 4, 1), (cS 5 2, 1), (cR 1, 1), (cR 2, 1), (cR 3, 2), (cR 4, 1), (cR 5, 1)], [(cS 0 0, 1), (cS 0 1, 1), (cS 0 2, 1), (cS 1 1, 1), (cS 4 6, 3), (cS 5 0, 1), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 6, 1)])],
  .root (40, [(cS 0 5, 10), (cS 1 3, 25), (cS 1 4, 15), (cS 1 5, 4), (cS 1 6, 4), (cS 2 3, 4), (cS 3 1, 10), (cS 3 3, 6), (cS 4 0, 11), (cS 5 1, 29), (cS 5 6, 18), (cS 6 0, 11), (cR 2, 11), (cR 3, 19), (cC 5, 11), (cC 6, 11)], [(cS 0 0, 18), (cS 0 1, 11), (cS 0 6, 8), (cS 1 0, 14), (cS 1 1, 15), (cS 4 2, 25), (cS 4 4, 40), (cS 6 2, 25), (cS 6 4, 40), (cC 2, 15)]),
  .root (24, [(cS 0 4, 1), (cS 0 5, 9), (cS 1 3, 10), (cS 1 4, 5), (cS 1 5, 9), (cS 1 6, 6), (cS 2 1, 1), (cS 2 2, 3), (cS 2 3, 2), (cS 2 4, 2), (cS 3 0, 3), (cS 3 5, 2), (cS 3 6, 2), (cS 4 1, 1), (cS 4 2, 4), (cS 5 1, 3), (cS 5 2, 11), (cR 2, 9), (cR 3, 11), (cR 4, 9)], [(cS 0 1, 5), (cS 0 6, 7), (cS 1 0, 9), (cS 1 1, 5), (cS 1 2, 6), (cS 4 4, 24), (cS 5 0, 11), (cS 5 5, 7), (cS 5 6, 8), (cS 6 1, 2), (cS 6 3, 7), (cS 6 4, 8), (cR 0, 8), (cR 6, 9)]),
  .root (1, [(cS 4 4, 1), (cR 1, 1), (cR 3, 1)], [(cR 0, 1), (cR 5, 1)]),
  .root (4, [(cS 0 0, 2), (cS 1 1, 2), (cS 3 6, 4), (cS 4 3, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 5 6, 1), (cS 6 0, 2), (cS 6 1, 1), (cR 4, 2)], [(cS 0 2, 2), (cS 1 6, 2), (cS 2 0, 2), (cS 2 2, 2), (cS 3 1, 2), (cS 6 2, 1), (cS 6 6, 2), (cC 3, 2), (cC 4, 2), (cC 5, 2)]),
  .root (4, [(cS 0 0, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 3 2, 2), (cS 4 4, 3), (cS 5 2, 2), (cS 5 6, 1), (cS 6 0, 1), (cR 4, 1), (cC 0, 2), (cC 1, 1), (cC 2, 1)], [(cS 0 2, 2), (cS 1 3, 2), (cS 1 5, 2), (cS 3 4, 2), (cS 3 6, 2), (cS 6 3, 2), (cS 6 5, 2), (cC 4, 2), (cC 6, 2)]),
  .root (5, [(cS 1 1, 1), (cS 2 1, 1), (cS 3 2, 4), (cS 3 6, 2), (cS 4 0, 1), (cS 4 2, 1), (cS 5 2, 1), (cS 5 3, 3), (cS 5 5, 2), (cS 6 0, 1), (cS 6 2, 1), (cC 0, 1), (cC 1, 3), (cC 6, 3)], [(cS 0 2, 1), (cS 0 3, 4), (cS 0 5, 2), (cS 1 5, 2), (cS 1 6, 1), (cS 2 2, 1), (cS 2 3, 4), (cS 2 5, 2), (cS 3 4, 2), (cS 4 4, 2), (cS 5 4, 2), (cS 6 4, 2), (cC 4, 1)]),
  .root (20, [(cS 0 0, 8), (cS 1 1, 3), (cS 2 1, 8), (cS 2 6, 5), (cS 3 1, 3), (cS 3 6, 9), (cS 4 4, 14), (cS 5 6, 8), (cS 6 0, 6), (cR 4, 6), (cC 1, 9), (cC 6, 6)], [(cS 0 3, 5), (cS 0 4, 9), (cS 0 5, 8), (cS 1 6, 9), (cS 2 3, 5), (cS 2 4, 9), (cS 2 5, 8), (cS 4 1, 2), (cS 5 1, 3), (cS 5 2, 6), (cS 5 4, 14), (cS 6 1, 2), (cS 6 5, 3), (cC 2, 9), (cC 3, 6), (cC 5, 3)]),
  .root (2, [(cS 0 0, 1), (cS 1 1, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 4 2, 1), (cS 4 4, 1), (cR 4, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 0 5, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 2 5, 1), (cR 5, 1), (cR 6, 1)]),
  .splitS0 [.leaf (2, [(cS 0 1, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 2 6, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 6 0, 1), (cR 4, 1), (cR 5, 1)], [(cS 0 3, 1), (cS 1 3, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 0, 2), (cS 3 2, 1), (cS 6 2, 1), (cS 6 4, 1), (cS 6 5, 1)]), .leaf (4, [(cS 0 0, 2), (cS 1 0, 2), (cS 1 1, 2), (cS 1 5, 4), (cS 2 6, 2), (cS 3 5, 1), (cS 4 2, 1), (cS 4 3, 2), (cS 4 4, 1), (cS 4 5, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 0, 2), (cR 4, 1), (cR 5, 1)], [(cS 0 2, 1), (cS 1 3, 1), (cS 1 4, 1), (cS 2 2, 2), (cS 2 4, 1), (cS 3 0, 2), (cS 3 1, 1), (cS 3 4, 1), (cS 4 6, 1), (cS 6 5, 1), (cR 0, 1), (cR 3, 1), (cR 6, 2), (cC 3, 1)]), .leaf (24, [(cS 0 0, 4), (cS 0 1, 12), (cS 0 6, 3), (cS 1 0, 15), (cS 1 5, 15), (cS 2 6, 7), (cS 3 4, 2), (cS 4 2, 6), (cS 4 3, 12), (cS 4 4, 4), (cS 4 5, 3), (cS 5 0, 3), (cS 5 1, 10), (cS 6 0, 4), (cS 6 1, 1), (cS 6 6, 11), (cR 4, 6), (cR 5, 3), (cR 6, 1), (cC 0, 2), (cC 5, 9)], [(cS 0 3, 3), (cS 0 4, 12), (cS 1 2, 12), (cS 1 3, 9), (cS 2 1, 7), (cS 2 2, 5), (cS 2 3, 10), (cS 2 4, 5), (cS 3 0, 6), (cS 3 1, 3), (cS 4 0, 6), (cS 4 6, 4), (cS 6 2, 10), (cS 6 3, 11), (cS 6 4, 10), (cS 6 5, 2), (cR 3, 9)]), .leaf (2, [(cS 0 1, 1), (cS 1 0, 1), (cS 1 5, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 1, 1), (cS 6 6, 1), (cC 0, 1), (cC 5, 1)], [(cS 0 4, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 4 6, 1), (cS 6 2, 1), (cS 6 3, 1), (cS 6 4, 1), (cR 3, 1)]), .leaf (20, [(cS 0 0, 5), (cS 0 1, 9), (cS 0 5, 2), (cS 0 6, 3), (cS 1 0, 9), (cS 1 5, 9), (cS 2 4, 2), (cS 2 6, 8), (cS 3 3, 3), (cS 3 4, 6), (cS 4 2, 5), (cS 4 3, 6), (cS 4 4, 2), (cS 5 0, 5), (cS 5 1, 3), (cS 6 0, 6), (cS 6 6, 6), (cR 1, 3), (cR 4, 6), (cR 5, 6), (cC 5, 6)], [(cS 0 2, 2), (cS 0 3, 3), (cS 1 1, 6), (cS 1 3, 17), (cS 2 1, 2), (cS 2 2, 9), (cS 2 3, 3), (cS 3 0, 12), (cS 3 2, 3), (cS 4 6, 3), (cS 6 2, 12), (cS 6 3, 3), (cS 6 4, 17), (cS 6 5, 3), (cR 3, 6)]), .leaf (10, [(cS 0 1, 1), (cS 0 2, 3), (cS 1 0, 7), (cS 1 5, 7), (cS 2 5, 2), (cS 2 6, 2), (cS 3 3, 2), (cS 3 4, 1), (cS 3 5, 4), (cS 4 2, 1), (cS 4 3, 2), (cS 5 1, 4), (cS 5 4, 3), (cS 6 0, 7), (cS 6 2, 3), (cR 0, 2), (cR 4, 4), (cR 5, 2), (cC 2, 1), (cC 4, 1), (cC 6, 1)], [(cS 0 3, 6), (cS 1 1, 3), (cS 1 3, 4), (cS 2 2, 6), (cS 2 3, 4), (cS 2 4, 2), (cS 3 0, 6), (cS 3 1, 4), (cS 3 6, 1), (cS 4 6, 3), (cS 6 3, 4), (cS 6 5, 10)]), .leaf (2, [(cS 0 1, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 1, 1), (cS 6 6, 1), (cC 0, 1), (cC 5, 1)], [(cS 0 4, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 4 6, 1), (cS 6 2, 1), (cS 6 3, 1), (cS 6 4, 1), (cR 3, 1)]), .leaf (24, [(cS 0 0, 2), (cS 0 1, 9), (cS 1 0, 7), (cS 1 2, 1), (cS 1 5, 18), (cS 1 6, 9), (cS 2 6, 2), (cS 3 3, 4), (cS 3 4, 2), (cS 4 3, 7), (cS 4 4, 8), (cS 4 5, 1), (cS 5 1, 9), (cS 5 2, 2), (cS 6 0, 7), (cS 6 6, 9), (cR 4, 7), (cR 5, 2), (cC 0, 6), (cC 2, 6), (cC 5, 6)], [(cS 0 2, 4), (cS 0 3, 6), (cS 1 2, 4), (cS 1 3, 18), (cS 2 1, 12), (cS 2 2, 1), (cS 2 3, 2), (cS 2 4, 4), (cS 3 6, 4), (cS 4 6, 9), (cS 6 2, 5), (cS 6 3, 9), (cS 6 4, 15), (cS 6 5, 9), (cR 3, 12)])],
  .root (4, [(cS 0 0, 1), (cS 0 1, 1), (cS 1 6, 1), (cS 3 6, 1), (cS 4 2, 2), (cS 5 1, 1), (cS 5 3, 1), (cS 6 2, 2), (cR 5, 1), (cC 0, 2), (cC 5, 2), (cC 6, 1)], [(cS 0 2, 1), (cS 0 3, 2), (cS 1 2, 2), (cS 2 1, 2), (cS 2 3, 2), (cS 3 0, 2), (cS 3 2, 2), (cS 4 4, 2), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 1), (cC 4, 2)]),
  .root (4, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 5, 1), (cS 1 1, 1), (cS 1 5, 1), (cS 2 0, 1), (cS 2 5, 1), (cS 3 5, 1), (cS 4 4, 4), (cS 4 6, 1), (cS 5 6, 1), (cS 6 1, 1), (cC 0, 1), (cC 6, 2)], [(cS 2 1, 1), (cS 3 1, 3), (cS 4 0, 1), (cS 5 1, 2), (cS 6 4, 1), (cS 6 5, 1), (cC 2, 2), (cC 3, 2), (cC 4, 2)]),
  .root (10, [(cS 0 1, 6), (cS 0 6, 4), (cS 1 0, 2), (cS 1 1, 2), (cS 1 5, 2), (cS 1 6, 4), (cS 2 0, 1), (cS 2 5, 1), (cS 2 6, 3), (cS 3 0, 1), (cS 3 5, 1), (cS 3 6, 5), (cS 4 2, 1), (cS 4 4, 6), (cS 5 2, 5), (cR 4, 4)], [(cS 0 2, 2), (cS 0 3, 3), (cS 0 5, 3), (cS 1 3, 2), (cS 2 1, 3), (cS 2 2, 3), (cS 2 4, 1), (cS 3 1, 5), (cS 3 3, 2), (cS 5 0, 3), (cS 5 1, 3), (cS 5 6, 3), (cS 6 0, 2), (cS 6 4, 3), (cS 6 6, 2), (cR 2, 2), (cR 6, 2), (cC 3, 3), (cC 4, 2), (cC 5, 3)]),
  .root (5, [(cS 0 5, 1), (cS 1 1, 1), (cS 1 5, 2), (cS 1 6, 1), (cS 2 1, 1), (cS 2 5, 1), (cS 3 2, 3), (cS 4 1, 1), (cS 5 2, 3), (cS 6 0, 1), (cC 0, 3), (cC 1, 1), (cC 2, 2), (cC 6, 1)], [(cS 0 2, 2), (cS 0 3, 1), (cS 1 3, 1), (cS 2 3, 1), (cS 3 4, 1), (cS 3 5, 1), (cS 3 6, 2), (cS 4 4, 1), (cS 4 6, 3), (cS 5 4, 1), (cS 5 5, 1), (cS 6 3, 1), (cS 6 5, 3), (cC 3, 1), (cC 4, 2)]),
  .root (24, [(cS 0 0, 3), (cS 0 1, 5), (cS 0 5, 9), (cS 1 1, 4), (cS 1 5, 1), (cS 1 6, 13), (cS 2 1, 10), (cS 2 2, 6), (cS 2 5, 4), (cS 2 6, 5), (cS 3 1, 2), (cS 3 2, 2), (cS 4 4, 24), (cS 5 6, 3), (cS 6 0, 4), (cS 6 6, 9), (cC 0, 8), (cC 1, 4), (cC 5, 1)], [(cS 0 2, 7), (cS 0 4, 6), (cS 1 3, 5), (cS 1 4, 4), (cS 2 4, 11), (cS 3 0, 1), (cS 3 6, 6), (cS 4 0, 1), (cS 4 1, 3), (cS 4 2, 4), (cS 4 6, 11), (cS 5 1, 7), (cS 5 2, 7), (cS 5 5, 5), (cS 6 2, 5), (cS 6 4, 14), (cS 6 5, 2), (cR 3, 5), (cR 5, 1), (cC 2, 4), (cC 3, 9), (cC 5, 3)]),
  .root (5, [(cS 0 1, 1), (cS 0 6, 1), (cS 1 0, 2), (cS 1 1, 2), (cS 1 5, 2), (cS 1 6, 2), (cS 2 1, 1), (cS 2 2, 2), (cS 2 5, 1), (cS 2 6, 1), (cS 3 0, 3), (cS 3 1, 2), (cS 4 2, 5), (cS 4 4, 5)], [(cS 0 3, 1), (cS 0 5, 1), (cS 1 3, 2), (cS 2 3, 1), (cS 2 4, 2), (cS 3 3, 2), (cS 3 5, 2), (cS 3 6, 1), (cS 4 0, 2), (cS 4 6, 2), (cR 0, 2), (cR 5, 3), (cR 6, 2)]),
  .root (1, [(cC 1, 1), (cC 6, 1)], [(cC 2, 1), (cC 4, 1)]),
  .root (3, [(cS 0 0, 1), (cS 1 1, 1), (cS 1 5, 2), (cS 1 6, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 3 5, 1), (cS 5 2, 1), (cS 6 2, 1), (cR 3, 1), (cR 4, 1), (cC 0, 1), (cC 2, 1)], [(cS 0 2, 1), (cS 2 2, 1), (cS 4 5, 2), (cS 5 0, 1), (cS 6 0, 1), (cS 6 5, 2), (cS 6 6, 1), (cC 3, 2), (cC 4, 1)]),
  .root (6, [(cS 0 0, 2), (cS 0 1, 2), (cS 1 1, 2), (cS 1 5, 2), (cS 1 6, 3), (cS 2 1, 4), (cS 2 6, 2), (cS 3 0, 3), (cS 3 1, 2), (cS 3 5, 3), (cS 4 4, 6), (cS 4 6, 2), (cC 6, 1)], [(cS 0 4, 1), (cS 0 5, 2), (cS 1 3, 1), (cS 1 4, 1), (cS 2 4, 3), (cS 3 2, 1), (cS 4 1, 1), (cS 5 0, 2), (cS 5 1, 2), (cS 5 5, 2), (cS 6 5, 1), (cS 6 6, 1), (cR 5, 1), (cR 6, 2), (cC 2, 2), (cC 3, 3)]),
  .splitS0 [.leaf (20, [(cS 0 0, 7), (cS 0 1, 6), (cS 1 1, 1), (cS 1 2, 2), (cS 1 3, 2), (cS 2 3, 10), (cS 2 4, 1), (cS 2 5, 7), (cS 3 2, 3), (cS 3 3, 7), (cS 3 4, 4), (cS 3 5, 7), (cS 4 2, 3), (cS 4 4, 1), (cS 5 0, 2), (cS 6 0, 7), (cS 6 6, 6), (cR 1, 6), (cR 4, 7), (cR 5, 11), (cC 4, 1)], [(cS 0 2, 5), (cS 0 3, 5), (cS 0 4, 6), (cS 0 5, 2), (cS 1 5, 6), (cS 1 6, 12), (cS 2 1, 13), (cS 2 6, 2), (cS 3 0, 14), (cS 3 1, 7), (cS 3 6, 4), (cS 4 6, 2), (cS 6 2, 10), (cS 6 4, 9), (cS 6 5, 12)]), .leaf (20, [(cS 0 0, 11), (cS 0 1, 3), (cS 1 0, 6), (cS 1 2, 5), (cS 2 3, 9), (cS 2 4, 11), (cS 3 2, 2), (cS 3 3, 3), (cS 3 4, 9), (cS 4 3, 3), (cS 4 5, 5), (cS 5 0, 5), (cS 5 3, 2), (cS 6 1, 3), (cS 6 6, 6), (cR 4, 6), (cR 5, 9), (cR 6, 3), (cC 2, 6)], [(cS 0 2, 6), (cS 0 3, 14), (cS 0 4, 3), (cS 0 5, 8), (cS 1 4, 3), (cS 1 5, 6), (cS 1 6, 6), (cS 2 1, 14), (cS 2 6, 8), (cS 3 0, 8), (cS 3 1, 6), (cS 3 6, 12), (cS 6 4, 6), (cS 6 5, 3)]), .leaf (3, [(cS 0 0, 1), (cS 0 1, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 3, 1), (cS 3 4, 1), (cS 3 5, 1), (cS 5 0, 1), (cS 5 4, 1), (cS 6 0, 1), (cS 6 6, 1), (cR 1, 1), (cR 4, 1), (cR 5, 1), (cC 2, 1)], [(cS 0 3, 2), (cS 0 5, 2), (cS 2 1, 2), (cS 2 5, 1), (cS 2 6, 1), (cS 3 0, 2), (cS 3 1, 1), (cS 6 2, 1), (cS 6 4, 1), (cC 6, 1)]), .leaf (20, [(cS 0 0, 10), (cS 1 0, 8), (cS 1 1, 2), (cS 1 2, 5), (cS 2 3, 9), (cS 2 4, 11), (cS 3 3, 5), (cS 3 4, 3), (cS 3 5, 6), (cS 4 4, 3), (cS 5 0, 5), (cS 5 4, 2), (cS 6 0, 1), (cS 6 1, 1), (cS 6 6, 1), (cR 4, 9), (cR 5, 6), (cR 6, 8), (cC 2, 6)], [(cS 0 2, 6), (cS 0 3, 13), (cS 0 4, 6), (cS 0 5, 5), (cS 1 5, 8), (cS 1 6, 6), (cS 2 1, 9), (cS 2 6, 5), (cS 3 1, 11), (cS 3 6, 15), (cS 4 6, 5), (cS 6 3, 1), (cS 6 4, 3), (cS 6 5, 6), (cR 1, 1)]), .leaf (6, [(cS 0 0, 4), (cS 1 0, 1), (cS 1 1, 1), (cS 1 2, 1), (cS 2 3, 3), (cS 2 4, 3), (cS 3 3, 1), (cS 3 4, 2), (cS 3 5, 1), (cS 4 3, 1), (cS 4 5, 1), (cS 5 0, 2), (cS 5 4, 1), (cS 6 1, 1), (cS 6 6, 1), (cR 4, 2), (cR 5, 2), (cR 6, 1), (cC 2, 2)], [(cS 0 2, 2), (cS 0 3, 4), (cS 0 5, 4), (cS 1 4, 2), (cS 1 6, 1), (cS 2 1, 4), (cS 2 5, 1), (cS 2 6, 3), (cS 3 0, 4), (cS 3 1, 2), (cS 3 6, 1), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 1), (cC 6, 1)]), .leaf (8, [(cS 0 0, 1), (cS 0 1, 4), (cS 0 6, 1), (cS 1 0, 2), (cS 1 2, 2), (cS 1 3, 2), (cS 2 2, 1), (cS 2 3, 2), (cS 2 4, 3), (cS 3 2, 4), (cS 3 3, 1), (cS 3 4, 4), (cS 3 5, 1), (cS 6 0, 3), (cS 6 6, 3), (cR 1, 1), (cR 4, 3), (cR 5, 5)], [(cS 0 2, 1), (cS 0 3, 4), (cS 0 4, 1), (cS 0 5, 4), (cS 1 0, 1), (cS 1 5, 2), (cS 1 6, 2), (cS 2 1, 4), (cS 2 5, 2), (cS 2 6, 2), (cS 3 0, 4), (cS 3 1, 4), (cS 3 6, 4), (cS 6 2, 3), (cS 6 4, 3)]), .leaf (4, [(cS 0 0, 1), (cS 0 1, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 2 3, 2), (cS 2 4, 2), (cS 3 2, 1), (cS 3 4, 2), (cS 4 3, 1), (cS 4 5, 1), (cS 6 6, 1), (cR 4, 1), (cR 5, 2), (cR 6, 1), (cC 0, 1), (cC 2, 1)], [(cS 0 2, 1), (cS 0 3, 3), (cS 0 4, 1), (cS 0 5, 2), (cS 1 5, 1), (cS 1 6, 1), (cS 2 1, 2), (cS 2 5, 1), (cS 2 6, 1), (cS 3 0, 2), (cS 3 1, 2), (cS 3 6, 2), (cS 6 4, 1)]), .leaf (24, [(cS 0 0, 4), (cS 0 1, 12), (cS 0 6, 3), (cS 1 0, 8), (cS 1 2, 9), (cS 1 3, 4), (cS 2 3, 11), (cS 2 4, 9), (cS 3 2, 11), (cS 3 3, 2), (cS 3 4, 13), (cS 3 5, 2), (cS 4 2, 3), (cS 4 4, 2), (cS 5 0, 2), (cS 6 0, 7), (cS 6 1, 1), (cS 6 6, 10), (cR 4, 8), (cR 5, 14)], [(cS 0 2, 3), (cS 0 3, 10), (cS 0 4, 3), (cS 0 5, 11), (cS 1 4, 7), (cS 1 5, 4), (cS 1 6, 9), (cS 2 1, 16), (cS 2 5, 4), (cS 2 6, 7), (cS 3 0, 4), (cS 3 1, 8), (cS 3 6, 13), (cS 4 0, 4), (cS 4 6, 3), (cS 6 2, 10), (cS 6 3, 1), (cS 6 4, 10)]), .leaf (5, [(cS 0 0, 2), (cS 0 1, 2), (cS 0 6, 1), (cS 1 3, 2), (cS 1 4, 2), (cS 2 3, 2), (cS 2 5, 1), (cS 3 2, 2), (cS 3 3, 1), (cS 3 4, 2), (cS 3 5, 2), (cS 4 2, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 6 0, 1), (cS 6 6, 1), (cR 1, 1), (cR 4, 1), (cR 5, 3)], [(cS 0 2, 2), (cS 0 5, 1), (cS 1 5, 1), (cS 1 6, 3), (cS 2 1, 4), (cS 2 6, 1), (cS 3 0, 3), (cS 3 1, 1), (cS 3 6, 1), (cS 4 6, 1), (cS 6 2, 2), (cS 6 3, 1), (cS 6 4, 4), (cS 6 5, 2)]), .leaf (12, [(cS 0 0, 8), (cS 1 1, 1), (cS 1 3, 2), (cS 2 3, 4), (cS 2 4, 2), (cS 2 5, 4), (cS 3 2, 1), (cS 3 3, 4), (cS 3 4, 1), (cS 3 5, 4), (cS 4 4, 2), (cS 5 0, 3), (cS 6 0, 4), (cR 1, 3), (cR 4, 4), (cR 5, 5), (cC 2, 3), (cC 4, 1)], [(cS 0 2, 5), (cS 0 4, 6), (cS 1 5, 2), (cS 1 6, 7), (cS 2 1, 8), (cS 3 0, 8), (cS 3 1, 4), (cS 3 6, 1), (cS 6 2, 4), (cS 6 3, 3), (cS 6 4, 3), (cS 6 5, 9), (cC 6, 3)]), .leaf (4, [(cS 0 0, 1), (cS 0 1, 1), (cS 1 0, 1), (cS 1 3, 2), (cS 2 2, 1), (cS 2 4, 2), (cS 3 2, 2), (cS 3 4, 2), (cS 4 4, 1), (cS 6 1, 1), (cS 6 6, 2), (cR 4, 1), (cR 5, 2), (cC 0, 1), (cC 2, 1)], [(cS 0 2, 2), (cS 0 3, 1), (cS 0 4, 1), (cS 0 5, 1), (cS 1 5, 2), (cS 1 6, 1), (cS 2 1, 2), (cS 2 6, 1), (cS 3 1, 2), (cS 3 6, 3), (cS 4 6, 1), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 1)]), .leaf (8, [(cS 0 0, 2), (cS 1 1, 1), (cS 1 3, 1), (cS 2 2, 2), (cS 2 3, 2), (cS 2 4, 2), (cS 3 3, 4), (cS 3 5, 6), (cS 6 0, 1), (cS 6 1, 3), (cS 6 6, 3), (cR 0, 2), (cR 1, 3), (cR 4, 4), (cR 5, 4)], [(cS 0 2, 2), (cS 0 3, 2), (cS 1 5, 3), (cS 1 6, 5), (cS 2 1, 4), (cS 3 1, 4), (cS 3 6, 8), (cS 6 2, 1), (cS 6 3, 3), (cS 6 4, 5), (cS 6 5, 3)])],
  .root (30, [(cS 0 0, 6), (cS 0 1, 9), (cS 1 1, 8), (cS 2 3, 15), (cS 2 4, 2), (cS 2 5, 1), (cS 2 6, 6), (cS 3 5, 1), (cS 3 6, 8), (cS 4 1, 8), (cS 4 3, 15), (cS 4 5, 1), (cS 4 6, 6), (cS 5 1, 15), (cS 5 6, 9), (cS 6 0, 8), (cC 0, 2), (cC 1, 5), (cC 2, 2), (cC 3, 13), (cC 6, 14)], [(cS 0 2, 6), (cS 0 3, 9), (cS 0 5, 9), (cS 1 5, 13), (cS 1 6, 8), (cS 2 1, 15), (cS 2 5, 9), (cS 3 1, 15), (cS 3 4, 9), (cS 4 4, 13), (cS 5 4, 9), (cS 6 2, 8), (cS 6 3, 7), (cS 6 4, 6), (cS 6 5, 7), (cC 4, 8)]),
  .root (4, [(cS 0 0, 2), (cS 0 1, 1), (cS 1 1, 1), (cS 2 4, 4), (cS 2 6, 1), (cS 3 6, 2), (cS 4 4, 4), (cS 4 6, 1), (cS 5 6, 2), (cS 6 0, 1), (cC 6, 1)], [(cS 0 4, 1), (cS 1 5, 3), (cS 1 6, 1), (cS 2 0, 1), (cS 3 1, 1), (cS 4 0, 1), (cS 5 1, 1), (cS 5 4, 1), (cS 6 5, 3), (cC 1, 2), (cC 2, 1), (cC 3, 3)]),
  .root (6, [(cS 0 0, 1), (cS 0 1, 3), (cS 1 1, 2), (cS 2 3, 1), (cS 2 4, 3), (cS 3 0, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 3 6, 3), (cS 4 2, 2), (cS 4 4, 3), (cS 5 2, 2), (cS 5 4, 1), (cR 2, 2), (cR 4, 2)], [(cS 0 3, 3), (cS 0 5, 1), (cS 0 6, 2), (cS 1 3, 2), (cS 1 5, 4), (cS 1 6, 2), (cS 2 0, 2), (cS 2 1, 1), (cS 2 2, 1), (cS 3 1, 3), (cS 3 2, 1), (cS 5 0, 2), (cS 5 5, 2), (cS 6 4, 2), (cR 0, 1), (cR 5, 2), (cR 6, 2)]),
  .root (20, [(cS 0 0, 2), (cS 0 6, 5), (cS 1 1, 3), (cS 1 3, 2), (cS 2 1, 2), (cS 2 3, 11), (cS 2 4, 6), (cS 3 1, 3), (cS 3 3, 2), (cS 4 0, 2), (cS 4 2, 3), (cS 4 3, 8), (cS 5 0, 3), (cS 5 2, 2), (cS 5 6, 9), (cS 6 0, 3), (cS 6 6, 4), (cC 0, 6), (cC 1, 9), (cC 2, 6), (cC 3, 1)], [(cS 0 2, 2), (cS 0 3, 9), (cS 0 5, 7), (cS 1 5, 6), (cS 1 6, 7), (cS 2 6, 7), (cS 3 4, 5), (cS 3 6, 13), (cS 4 4, 6), (cS 4 6, 7), (cS 5 3, 2), (cS 5 4, 3), (cS 5 5, 4), (cS 6 2, 3), (cS 6 3, 6), (cS 6 5, 4), (cC 4, 9)]),
  .root (4, [(cS 0 1, 1), (cS 0 6, 1), (cS 1 2, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 2 4, 2), (cS 3 2, 1), (cS 3 5, 1), (cS 4 3, 1), (cS 4 4, 2), (cS 5 5, 1), (cS 5 6, 1), (cS 6 6, 1), (cR 2, 1), (cR 4, 1), (cC 0, 2), (cC 1, 1)], [(cS 0 3, 3), (cS 1 5, 3), (cS 2 6, 1), (cS 3 6, 3), (cS 4 2, 1), (cS 4 6, 1), (cS 5 2, 3), (cS 6 4, 3), (cR 0, 1), (cR 6, 1)]),
  .splitS0 [.leaf (30, [(cS 0 0, 18), (cS 0 1, 9), (cS 1 0, 4), (cS 1 1, 11), (cS 1 3, 4), (cS 2 0, 12), (cS 2 2, 9), (cS 2 3, 6), (cS 2 4, 13), (cS 3 0, 3), (cS 3 1, 7), (cS 3 4, 9), (cS 4 1, 1), (cS 4 2, 3), (cS 4 5, 2), (cS 5 2, 5), (cS 5 4, 14), (cR 3, 5), (cR 4, 11), (cC 1, 3), (cC 2, 7), (cC 3, 4), (cC 4, 3)], [(cS 0 3, 15), (cS 0 4, 4), (cS 0 5, 7), (cS 1 5, 16), (cS 1 6, 3), (cS 2 6, 6), (cS 3 0, 5), (cS 3 6, 14), (cS 4 0, 6), (cS 5 0, 19), (cS 5 1, 5), (cS 5 5, 12), (cS 6 2, 4), (cS 6 3, 4), (cS 6 5, 12), (cR 6, 7), (cC 6, 5)]), .leaf (4, [(cS 0 0, 2), (cS 1 0, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 4, 1), (cS 4 5, 1), (cS 5 3, 1), (cS 5 4, 1), (cS 5 5, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1), (cC 1, 2), (cC 2, 1), (cC 3, 1)], [(cS 0 3, 3), (cS 0 4, 1), (cS 0 5, 1), (cS 1 2, 1), (cS 1 5, 2), (cS 2 6, 1), (cS 3 6, 2), (cS 4 0, 1), (cS 5 0, 2), (cS 6 5, 1), (cR 6, 1), (cC 6, 1)]), .leaf (2, [(cS 2 4, 1), (cS 3 5, 1), (cS 4 4, 1), (cS 5 4, 1), (cC 0, 1), (cC 1, 1), (cC 2, 1), (cC 3, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 0 4, 1), (cS 1 5, 1), (cS 3 6, 1), (cS 5 6, 1), (cS 6 5, 1), (cC 6, 1)]), .leaf (16, [(cS 0 0, 9), (cS 0 1, 3), (cS 1 0, 2), (cS 1 1, 3), (cS 2 0, 1), (cS 2 3, 1), (cS 2 4, 3), (cS 3 0, 1), (cS 3 1, 4), (cS 3 4, 4), (cS 3 5, 3), (cS 4 1, 2), (cS 4 2, 2), (cS 4 4, 1), (cS 4 5, 3), (cS 5 4, 5), (cS 5 5, 3), (cR 2, 6), (cR 4, 5), (cC 1, 4), (cC 2, 3), (cC 3, 6)], [(cS 0 2, 3), (cS 0 3, 5), (cS 0 4, 5), (cS 0 5, 3), (cS 1 5, 8), (cS 2 6, 3), (cS 3 6, 8), (cS 4 0, 2), (cS 4 6, 1), (cS 5 0, 9), (cS 5 1, 5), (cS 6 2, 2), (cS 6 3, 4), (cS 6 5, 6), (cR 6, 2), (cC 6, 5)]), .leaf (20, [(cS 0 0, 11), (cS 1 0, 7), (cS 1 1, 1), (cS 1 2, 6), (cS 2 0, 1), (cS 2 3, 10), (cS 2 4, 8), (cS 3 0, 4), (cS 3 1, 4), (cS 3 2, 3), (cS 3 3, 3), (cS 3 4, 10), (cS 4 2, 6), (cS 4 3, 3), (cS 4 4, 1), (cS 4 5, 6), (cS 5 3, 11), (cS 5 4, 2), (cS 5 5, 8), (cR 2, 2), (cR 4, 3), (cC 1, 9), (cC 2, 2)], [(cS 0 2, 2), (cS 0 3, 11), (cS 0 4, 2), (cS 0 5, 8), (cS 1 3, 7), (cS 1 5, 10), (cS 2 6, 8), (cS 3 6, 10), (cS 4 0, 7), (cS 4 6, 1), (cS 5 0, 11), (cS 5 1, 2), (cS 6 5, 3), (cR 6, 7), (cC 6, 2)]), .leaf (8, [(cS 0 0, 3), (cS 0 1, 1), (cS 1 0, 2), (cS 1 1, 1), (cS 1 2, 2), (cS 1 3, 1), (cS 2 3, 2), (cS 2 4, 2), (cS 3 4, 1), (cS 4 2, 2), (cS 4 4, 1), (cS 4 5, 1), (cS 5 2, 2), (cS 5 3, 1), (cS 5 4, 4), (cS 6 0, 1), (cR 2, 2), (cR 3, 3), (cR 4, 2), (cC 1, 3), (cC 3, 1)], [(cS 0 2, 1), (cS 0 3, 3), (cS 0 4, 3), (cS 0 5, 1), (cS 1 5, 4), (cS 2 6, 1), (cS 3 6, 4), (cS 4 6, 1), (cS 5 0, 3), (cS 5 6, 1), (cS 6 2, 2), (cS 6 3, 1), (cS 6 5, 3), (cR 6, 1), (cC 6, 3)]), .leaf (2, [(cS 1 3, 1), (cS 2 2, 1), (cS 3 2, 1), (cS 3 4, 1), (cS 4 2, 1), (cS 5 2, 1), (cS 5 4, 1), (cC 0, 1), (cC 1, 1), (cC 4, 1)], [(cS 0 2, 1), (cS 1 5, 1), (cS 3 6, 1), (cS 5 6, 1), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 1), (cC 6, 1)]), .leaf (4, [(cS 2 2, 1), (cS 2 3, 1), (cS 2 4, 2), (cS 3 5, 2), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 2), (cS 5 4, 2), (cC 0, 2), (cC 1, 2), (cC 2, 1), (cC 3, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 0 4, 2), (cS 1 5, 2), (cS 3 6, 2), (cS 5 6, 2), (cS 6 2, 1), (cS 6 3, 1), (cS 6 5, 2), (cC 6, 2)]), .leaf (2, [(cS 2 2, 1), (cS 2 4, 1), (cS 4 3, 1), (cS 4 4, 1), (cC 0, 1), (cC 1, 1), (cC 2, 1), (cC 4, 1)], [(cS 0 3, 1), (cS 1 5, 1), (cS 3 6, 1), (cS 5 6, 1), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 1), (cC 6, 1)])],
  .root (20, [(cS 0 0, 2), (cS 0 3, 8), (cS 1 1, 3), (cS 1 3, 3), (cS 2 3, 14), (cS 4 1, 2), (cS 4 5, 2), (cS 4 6, 3), (cS 5 0, 3), (cS 6 0, 3), (cR 2, 3), (cR 3, 3), (cC 1, 15), (cC 6, 15)], [(cS 0 3, 6), (cS 1 5, 11), (cS 1 6, 3), (cS 3 4, 5), (cS 4 2, 11), (cS 4 3, 6), (cS 4 4, 6), (cS 5 2, 6), (cS 5 4, 5), (cS 6 2, 11), (cS 6 4, 12), (cC 2, 3), (cC 4, 3), (cC 5, 6)]),
  .root (20, [(cS 0 0, 5), (cS 1 0, 1), (cS 1 1, 5), (cS 1 3, 5), (cS 2 3, 5), (cS 2 6, 6), (cS 3 6, 2), (cS 4 3, 4), (cS 4 6, 6), (cS 5 2, 6), (cR 2, 6), (cR 3, 6), (cR 4, 6), (cC 1, 9), (cC 3, 4)], [(cS 0 2, 6), (cS 0 3, 5), (cS 0 6, 7), (cS 1 5, 13), (cS 1 6, 7), (cS 3 4, 1), (cS 4 4, 12), (cS 5 0, 3), (cS 5 6, 6), (cS 6 3, 3), (cS 6 4, 2), (cS 6 5, 5), (cS 6 6, 3), (cR 5, 2), (cR 6, 6), (cC 4, 7)]),
  .root (24, [(cS 0 0, 5), (cS 0 1, 7), (cS 1 0, 6), (cS 1 1, 6), (cS 2 2, 4), (cS 2 3, 6), (cS 2 4, 4), (cS 3 0, 4), (cS 3 1, 3), (cS 3 5, 3), (cS 3 6, 5), (cS 4 3, 6), (cS 4 4, 8), (cS 4 5, 6), (cS 4 6, 2), (cR 2, 14), (cR 3, 3), (cR 4, 10)], [(cS 0 2, 5), (cS 0 3, 12), (cS 1 4, 5), (cS 1 5, 12), (cS 1 6, 6), (cS 2 5, 7), (cS 4 1, 4), (cS 4 2, 5), (cS 5 0, 6), (cS 5 1, 7), (cS 5 2, 5), (cS 5 3, 7), (cS 6 4, 4), (cS 6 5, 7), (cS 6 6, 6), (cR 0, 7), (cR 5, 7), (cR 6, 6)]),
  .root (30, [(cS 0 1, 6), (cS 1 4, 6), (cS 1 5, 7), (cS 1 6, 6), (cS 2 2, 3), (cS 2 3, 7), (cS 2 5, 9), (cS 3 3, 3), (cS 3 4, 7), (cS 4 2, 18), (cS 5 0, 6), (cS 5 1, 17), (cS 5 2, 9), (cS 5 6, 7), (cS 6 0, 3), (cS 6 6, 7), (cR 0, 14), (cR 1, 3), (cR 2, 14), (cC 0, 7), (cC 2, 3)], [(cS 0 2, 4), (cS 0 3, 7), (cS 2 1, 7), (cS 3 0, 2), (cS 3 1, 21), (cS 3 2, 3), (cS 3 6, 7), (cS 4 3, 3), (cS 4 4, 27), (cS 4 5, 3), (cS 4 6, 21), (cS 6 2, 3), (cS 6 3, 16), (cS 6 4, 14), (cS 6 5, 16)]),
  .splitS0 [.leaf (30, [(cS 0 0, 5), (cS 0 1, 6), (cS 0 5, 5), (cS 1 0, 12), (cS 1 5, 4), (cS 2 2, 3), (cS 2 3, 17), (cS 3 3, 3), (cS 3 4, 2), (cS 3 5, 3), (cS 4 3, 13), (cS 4 4, 7), (cS 5 4, 5), (cS 5 6, 5), (cS 6 0, 14), (cS 6 6, 1), (cR 1, 3), (cR 2, 7), (cC 0, 5), (cC 4, 5), (cC 5, 13), (cC 6, 5)], [(cS 0 2, 9), (cS 0 3, 9), (cS 0 4, 21), (cS 2 1, 5), (cS 3 0, 11), (cS 3 1, 14), (cS 3 6, 3), (cS 4 0, 9), (cS 4 1, 1), (cS 4 2, 3), (cS 4 6, 7), (cS 5 1, 15), (cS 5 3, 16), (cS 6 2, 3), (cS 6 4, 4), (cS 6 5, 6), (cC 2, 12)]), .leaf (10, [(cS 0 0, 2), (cS 0 1, 1), (cS 1 0, 2), (cS 1 6, 1), (cS 2 2, 1), (cS 2 3, 5), (cS 2 6, 2), (cS 3 3, 4), (cS 3 4, 4), (cS 4 3, 1), (cS 5 0, 2), (cS 5 3, 4), (cS 5 4, 4), (cS 6 0, 6), (cS 6 6, 1), (cR 1, 4), (cC 0, 1), (cC 4, 1), (cC 5, 5)], [(cS 0 2, 3), (cS 0 3, 5), (cS 0 4, 5), (cS 2 1, 3), (cS 3 0, 2), (cS 3 1, 5), (cS 3 6, 5), (cS 4 0, 2), (cS 4 1, 1), (cS 4 2, 3), (cS 4 6, 5), (cS 5 1, 4), (cS 6 2, 4), (cS 6 4, 1), (cS 6 5, 4), (cC 2, 2)]), .leaf (4, [(cS 0 0, 1), (cS 1 0, 1), (cS 2 3, 2), (cS 2 6, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 4 4, 3), (cS 5 0, 1), (cS 5 3, 1), (cS 5 6, 1), (cS 6 0, 2), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cC 5, 2)], [(cS 0 2, 1), (cS 0 4, 2), (cS 2 1, 1), (cS 3 0, 2), (cS 3 1, 1), (cS 3 2, 1), (cS 4 0, 1), (cS 4 2, 2), (cS 4 6, 1), (cS 5 1, 2), (cS 5 3, 1), (cS 6 2, 1), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 1), (cC 2, 1)]), .leaf (30, [(cS 0 0, 4), (cS 0 1, 3), (cS 0 5, 1), (cS 1 4, 6), (cS 1 5, 3), (cS 1 6, 3), (cS 2 3, 15), (cS 3 5, 15), (cS 4 4, 30), (cS 5 0, 4), (cS 5 6, 13), (cS 6 0, 7), (cR 0, 13), (cR 1, 7), (cR 2, 15), (cC 0, 3), (cC 6, 3)], [(cS 0 3, 3), (cS 0 4, 2), (cS 2 1, 6), (cS 3 0, 11), (cS 3 1, 13), (cS 3 2, 4), (cS 4 0, 7), (cS 4 2, 19), (cS 4 6, 12), (cS 5 1, 13), (cS 5 3, 1), (cS 6 2, 9), (cS 6 3, 11), (cS 6 4, 15), (cS 6 5, 13), (cR 5, 3), (cC 2, 7)]), .leaf (4, [(cS 0 0, 2), (cS 0 1, 1), (cS 3 3, 2), (cS 4 4, 2), (cS 5 0, 2), (cS 5 3, 2), (cS 6 0, 1), (cS 6 6, 1), (cR 1, 2), (cR 2, 2), (cC 5, 2)], [(cS 0 2, 1), (cS 0 3, 1), (cS 0 4, 1), (cS 3 1, 4), (cS 3 6, 2), (cS 4 2, 2), (cS 4 6, 2), (cS 5 1, 2), (cS 6 2, 2), (cS 6 4, 2), (cS 6 5, 1)]), .leaf (6, [(cS 0 1, 1), (cS 0 4, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 3, 2), (cS 3 5, 2), (cS 4 3, 3), (cS 4 4, 3), (cS 5 0, 2), (cS 5 5, 2), (cS 6 0, 2), (cS 6 6, 1), (cR 0, 2), (cR 1, 2), (cR 2, 2), (cC 0, 1), (cC 5, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 2 1, 1), (cS 3 1, 5), (cS 3 6, 3), (cS 4 1, 1), (cS 4 2, 1), (cS 4 6, 3), (cS 5 1, 2), (cS 5 2, 2), (cS 6 2, 2), (cS 6 3, 2), (cS 6 4, 4), (cS 6 5, 2)])],
  .splitS0 [.leaf (10, [(cS 0 0, 4), (cS 0 1, 3), (cS 0 6, 2), (cS 1 0, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 0, 2), (cS 2 2, 1), (cS 2 3, 5), (cS 2 6, 4), (cS 3 3, 1), (cS 3 4, 1), (cS 3 5, 1), (cS 4 2, 3), (cS 4 3, 4), (cS 4 4, 1), (cS 5 2, 5), (cS 5 4, 2), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cC 2, 2), (cC 4, 3), (cC 5, 4)], [(cS 0 2, 2), (cS 0 3, 5), (cS 2 1, 4), (cS 3 0, 3), (cS 3 1, 5), (cS 4 0, 1), (cS 4 6, 6), (cS 5 0, 7), (cS 5 1, 1), (cS 6 3, 2), (cS 6 4, 2), (cS 6 5, 7), (cS 6 6, 2), (cR 6, 1), (cC 1, 1)]), .leaf (40, [(cS 0 0, 13), (cS 0 1, 3), (cS 0 5, 10), (cS 1 0, 15), (cS 1 5, 12), (cS 1 6, 3), (cS 2 3, 16), (cS 2 4, 12), (cS 2 6, 14), (cS 3 3, 9), (cS 3 4, 19), (cS 4 2, 7), (cS 4 3, 9), (cS 4 5, 12), (cS 5 1, 16), (cS 5 2, 2), (cS 5 3, 15), (cS 5 4, 13), (cS 5 5, 6), (cR 1, 9), (cC 2, 15), (cC 4, 3), (cC 5, 6)], [(cS 0 2, 2), (cS 0 3, 26), (cS 0 4, 2), (cS 2 1, 17), (cS 3 0, 6), (cS 3 1, 23), (cS 3 6, 20), (cS 4 0, 11), (cS 4 6, 3), (cS 5 0, 13), (cS 5 6, 13), (cS 6 0, 3), (cS 6 5, 17), (cS 6 6, 3), (cR 0, 12), (cR 6, 9)]), .leaf (40, [(cS 0 0, 19), (cS 0 1, 2), (cS 0 5, 8), (cS 1 0, 2), (cS 1 5, 19), (cS 1 6, 2), (cS 2 0, 10), (cS 2 3, 10), (cS 2 4, 17), (cS 2 6, 9), (cS 3 3, 11), (cS 3 4, 4), (cS 3 5, 17), (cS 4 1, 4), (cS 4 2, 6), (cS 4 3, 6), (cS 4 4, 17), (cS 5 1, 11), (cS 5 3, 10), (cS 5 4, 22), (cS 6 2, 5), (cR 1, 11), (cC 0, 6), (cC 2, 19), (cC 4, 2)], [(cS 0 2, 1), (cS 0 3, 31), (cS 0 4, 1), (cS 2 1, 11), (cS 3 1, 30), (cS 3 6, 15), (cS 4 6, 25), (cS 5 0, 19), (cS 5 6, 15), (cS 6 5, 25), (cS 6 6, 1), (cR 0, 8), (cR 6, 6)]), .leaf (24, [(cS 0 0, 8), (cS 0 1, 4), (cS 0 5, 4), (cS 1 0, 4), (cS 1 4, 4), (cS 1 5, 8), (cS 1 6, 4), (cS 2 3, 8), (cS 2 6, 2), (cS 3 3, 2), (cS 3 4, 10), (cS 3 5, 2), (cS 4 2, 9), (cS 4 3, 12), (cS 4 5, 12), (cS 5 2, 13), (cS 5 4, 12), (cR 0, 6), (cR 1, 2), (cR 2, 12), (cC 2, 2)], [(cS 0 2, 6), (cS 0 3, 8), (cS 0 4, 5), (cS 2 1, 4), (cS 3 0, 2), (cS 3 1, 16), (cS 3 6, 8), (cS 4 0, 2), (cS 4 6, 12), (cS 5 0, 14), (cS 5 1, 4), (cS 6 3, 8), (cS 6 4, 2), (cS 6 5, 15), (cS 6 6, 8), (cR 6, 2), (cC 1, 4)]), .leaf (20, [(cS 0 0, 11), (cS 0 5, 5), (cS 1 0, 3), (cS 1 5, 9), (cS 2 3, 8), (cS 2 4, 3), (cS 2 6, 8), (cS 3 3, 6), (cS 3 4, 14), (cS 4 2, 11), (cS 4 5, 6), (cS 5 2, 6), (cS 5 3, 11), (cS 5 4, 9), (cS 5 5, 5), (cR 1, 6), (cR 2, 3), (cC 2, 3)], [(cS 0 2, 8), (cS 0 3, 12), (cS 0 4, 8), (cS 0 5, 6), (cS 2 1, 5), (cS 3 1, 12), (cS 3 6, 9), (cS 4 0, 5), (cS 4 6, 6), (cS 5 0, 9), (cS 5 1, 3), (cS 5 6, 3), (cS 6 1, 6), (cS 6 5, 6), (cS 6 6, 9), (cC 1, 3)]), .leaf (4, [(cS 0 0, 2), (cS 0 1, 1), (cS 1 6, 1), (cS 2 0, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 1, 2), (cS 5 3, 1), (cR 1, 1), (cR 2, 1), (cC 2, 1), (cC 4, 1), (cC 5, 2)], [(cS 0 2, 1), (cS 0 3, 1), (cS 0 4, 1), (cS 0 5, 2), (cS 2 1, 2), (cS 3 0, 1), (cS 3 1, 2), (cS 3 6, 1), (cS 4 0, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 6, 1), (cS 6 3, 1), (cS 6 6, 1), (cR 6, 1)]), .leaf (20, [(cS 0 0, 2), (cS 0 1, 3), (cS 1 6, 3), (cS 2 2, 2), (cS 2 3, 3), (cS 2 6, 2), (cS 3 3, 6), (cS 3 5, 6), (cS 4 2, 3), (cS 4 3, 9), (cS 4 5, 6), (cS 5 1, 9), (cS 5 2, 6), (cS 5 4, 6), (cR 0, 9), (cR 1, 6), (cR 2, 9), (cR 4, 2), (cC 4, 3), (cC 5, 3)], [(cS 0 2, 2), (cS 0 3, 3), (cS 2 1, 5), (cS 3 0, 9), (cS 3 1, 15), (cS 4 0, 1), (cS 4 6, 10), (cS 5 0, 9), (cS 6 3, 9), (cS 6 4, 5), (cS 6 5, 9), (cS 6 6, 5), (cR 6, 6)]), .leaf (8, [(cS 0 0, 4), (cS 0 1, 2), (cS 0 5, 2), (cS 0 6, 1), (cS 1 5, 3), (cS 1 6, 1), (cS 2 0, 2), (cS 2 3, 2), (cS 2 4, 1), (cS 2 6, 1), (cS 3 3, 1), (cS 3 5, 3), (cS 4 2, 2), (cS 4 3, 2), (cS 4 4, 3), (cS 5 1, 2), (cS 5 2, 1), (cS 5 4, 3), (cR 1, 1), (cR 2, 2), (cC 0, 1), (cC 2, 3), (cC 4, 2)], [(cS 0 2, 1), (cS 0 3, 3), (cS 0 4, 2), (cS 2 1, 1), (cS 3 1, 6), (cS 3 6, 2), (cS 4 6, 6), (cS 5 0, 4), (cS 5 6, 2), (cS 6 2, 1), (cS 6 3, 3), (cS 6 5, 6), (cS 6 6, 2), (cC 1, 1)]), .leaf (4, [(cS 3 2, 1), (cS 3 4, 1), (cS 4 2, 1), (cS 4 3, 2), (cS 4 4, 3), (cS 5 1, 2), (cS 5 2, 1), (cS 5 4, 1), (cR 0, 3), (cR 1, 1), (cR 2, 3)], [(cS 3 1, 4), (cS 3 6, 1), (cS 4 6, 3), (cS 5 0, 2), (cS 5 6, 1), (cS 6 3, 3), (cS 6 5, 3), (cR 6, 1)])],
  .root (2, [(cS 0 4, 1), (cS 1 2, 1), (cS 2 3, 1), (cS 2 4, 1), (cC 0, 1), (cC 1, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 3, 1), (cS 3 1, 2), (cS 3 3, 1), (cS 4 2, 1), (cS 4 4, 2), (cS 5 2, 1), (cS 6 2, 1), (cS 6 4, 2)]),
  .root (24, [(cS 1 0, 6), (cS 1 4, 1), (cS 1 5, 12), (cS 1 6, 1), (cS 2 3, 8), (cS 2 4, 11), (cS 2 6, 7), (cS 3 4, 1), (cS 3 5, 8), (cS 3 6, 6), (cS 4 1, 3), (cS 4 2, 8), (cS 4 6, 7), (cS 5 2, 16), (cR 0, 7), (cR 1, 4), (cR 3, 4), (cC 0, 7)], [(cS 0 2, 7), (cS 2 1, 14), (cS 3 1, 4), (cS 4 4, 12), (cS 4 5, 12), (cS 5 0, 8), (cS 5 6, 5), (cS 6 3, 1), (cS 6 4, 7), (cS 6 5, 13), (cS 6 6, 7), (cR 6, 4), (cC 1, 6), (cC 3, 12)]),
  .root (4, [(cS 0 0, 2), (cS 1 0, 2), (cS 1 5, 4), (cS 2 4, 4), (cS 2 6, 2), (cS 3 6, 2), (cS 4 4, 4), (cS 4 6, 2)], [(cS 0 4, 1), (cS 3 0, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 5 6, 1), (cS 6 4, 1), (cS 6 5, 2), (cS 6 6, 2), (cC 1, 3), (cC 2, 1), (cC 3, 3)]),
  .root (10, [(cS 5 0, 4), (cS 6 0, 3), (cS 6 1, 3), (cS 6 6, 3), (cR 0, 4), (cR 1, 6), (cR 2, 4), (cR 3, 6)], [(cS 4 4, 5), (cS 4 6, 5), (cS 5 1, 1), (cS 5 2, 6), (cS 6 2, 3), (cS 6 3, 7), (cS 6 4, 3), (cS 6 5, 7), (cR 4, 5)]),
  .root (2, [(cS 4 1, 1), (cS 4 2, 1), (cS 5 2, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)], [(cS 4 4, 2), (cS 4 6, 2), (cS 5 0, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 6, 1)]),
  .root (6, [(cS 0 0, 1), (cS 1 0, 1), (cS 1 5, 2), (cS 2 2, 1), (cS 2 4, 1), (cS 3 1, 1), (cS 4 4, 3), (cS 5 4, 3), (cR 0, 1), (cR 1, 3), (cR 2, 2), (cR 3, 3)], [(cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 5), (cS 0 4, 1), (cS 3 6, 1), (cS 4 2, 1), (cS 4 6, 3), (cS 5 0, 1), (cS 5 1, 2), (cS 5 3, 2), (cS 6 5, 2), (cS 6 6, 1), (cR 4, 2), (cR 5, 1), (cR 6, 3)]),
  .root (1, [(cR 1, 1), (cR 3, 1)], [(cR 4, 1), (cR 6, 1)]),
  .root (1, [(cR 4, 1), (cR 6, 1)], [(cR 0, 1), (cR 2, 1)]),
  .root (16, [(cS 3 1, 16), (cS 3 2, 1), (cS 3 3, 5), (cS 4 2, 7), (cS 4 3, 3), (cS 4 4, 9), (cS 4 5, 7), (cS 5 0, 9), (cS 5 1, 7), (cS 5 2, 2), (cS 5 3, 4), (cS 6 0, 2), (cS 6 4, 5), (cS 6 5, 11), (cS 6 6, 5)], [(cS 3 4, 6), (cS 3 6, 6), (cS 4 6, 10), (cS 6 1, 4), (cS 6 2, 3), (cS 6 3, 7), (cR 0, 10), (cR 1, 6), (cR 2, 10)]),
  .root (20, [(cS 2 1, 8), (cS 3 0, 12), (cS 3 2, 12), (cS 3 6, 2), (cS 4 5, 9), (cS 5 0, 8), (cS 5 2, 8), (cS 6 5, 11), (cR 4, 9), (cR 5, 3), (cR 6, 9)], [(cS 0 2, 8), (cS 1 0, 6), (cS 1 6, 5), (cS 2 2, 6), (cS 2 3, 8), (cS 2 5, 9), (cS 2 6, 3), (cS 3 3, 3), (cS 3 5, 3), (cS 4 4, 11), (cS 5 4, 3), (cR 0, 12), (cR 1, 3), (cR 2, 3), (cC 4, 6)]),
  .root (5, [(cS 2 1, 1), (cS 3 0, 1), (cS 3 1, 3), (cS 3 2, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 4 3, 2), (cS 4 4, 3), (cS 4 5, 2), (cS 4 6, 2), (cS 5 0, 1), (cS 5 6, 1), (cS 6 0, 1), (cS 6 4, 2), (cS 6 5, 3), (cS 6 6, 2)], [(cS 0 1, 1), (cS 1 0, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 5, 1), (cS 3 4, 1), (cS 5 1, 3), (cS 5 2, 1), (cS 5 3, 2), (cR 0, 3), (cR 2, 3), (cC 2, 1), (cC 3, 1)]),
  .root (5, [(cS 2 1, 2), (cS 3 0, 1), (cS 3 1, 1), (cS 3 2, 1), (cS 3 6, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 5 2, 3), (cS 5 3, 1), (cS 5 5, 1), (cS 6 4, 3), (cS 6 5, 2), (cR 3, 1), (cR 4, 2)], [(cS 0 2, 1), (cS 0 4, 1), (cS 1 0, 1), (cS 1 6, 1), (cS 2 2, 2), (cS 2 4, 2), (cS 2 5, 1), (cS 3 3, 1), (cS 5 0, 2), (cS 5 1, 1), (cS 5 6, 1), (cS 6 0, 1), (cR 0, 3), (cR 1, 1), (cR 2, 2), (cR 6, 1)]),
  .root (2, [(cS 0 0, 1), (cS 1 5, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 4, 1), (cS 6 6, 1), (cC 5, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 4 0, 1), (cS 4 5, 1), (cS 6 2, 1), (cS 6 3, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)]),
  .root (2, [(cS 0 5, 1), (cS 1 5, 1), (cS 2 6, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 4 6, 1), (cR 5, 1), (cR 6, 1)], [(cS 0 0, 1), (cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 1 3, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 3 3, 1), (cS 4 4, 2)]),
  .root (1, [(cC 4, 1), (cC 6, 1)], [(cC 1, 1), (cC 3, 1)]),
  .root (20, [(cS 0 5, 7), (cS 1 5, 2), (cS 1 6, 8), (cS 2 6, 7), (cS 3 0, 3), (cS 3 4, 6), (cS 3 6, 10), (cS 4 3, 3), (cS 4 4, 3), (cS 5 2, 12), (cS 5 3, 3), (cS 5 4, 4), (cS 5 5, 3), (cS 6 4, 10), (cR 4, 8), (cC 5, 3)], [(cS 0 0, 5), (cS 0 1, 1), (cS 0 2, 7), (cS 0 3, 5), (cS 1 3, 4), (cS 1 4, 5), (cS 2 1, 7), (cS 2 2, 2), (cS 2 3, 7), (cS 2 4, 9), (cS 3 2, 3), (cS 3 3, 1), (cS 5 0, 9), (cS 5 6, 7), (cS 6 6, 8), (cR 0, 3), (cR 2, 2), (cC 0, 4), (cC 1, 7), (cC 2, 2), (cC 3, 3)]),
  .root (2, [(cS 0 5, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 4 1, 1), (cS 4 3, 1), (cR 5, 1), (cR 6, 1)], [(cS 0 0, 1), (cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 1 3, 1), (cS 2 4, 1), (cS 3 6, 1), (cS 4 4, 2), (cS 4 6, 1), (cR 2, 1)]),
  .root (4, [(cS 1 6, 2), (cS 2 1, 1), (cS 3 1, 3), (cS 4 3, 2), (cS 4 4, 2), (cS 5 0, 2), (cS 6 4, 2), (cS 6 6, 2), (cC 5, 2)], [(cS 0 1, 1), (cS 3 6, 2), (cS 4 6, 2), (cS 5 1, 1), (cS 5 2, 2), (cR 0, 2), (cR 2, 2), (cC 1, 1), (cC 3, 2)]),
  .root (2, [(cS 1 5, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 5 3, 1), (cS 6 4, 1), (cC 5, 1)], [(cS 0 0, 1), (cS 0 1, 1), (cS 0 3, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 2 6, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 2, 1), (cC 6, 1)]),
  .root (20, [(cS 0 4, 2), (cS 0 5, 9), (cS 1 0, 9), (cS 1 5, 9), (cS 2 1, 8), (cS 2 6, 9), (cS 3 1, 12), (cS 3 6, 9), (cS 4 1, 8), (cS 4 6, 9), (cS 5 0, 12), (cS 5 5, 9), (cS 6 0, 8), (cS 6 4, 2), (cS 6 5, 9), (cC 6, 2)], [(cS 0 0, 10), (cS 0 1, 7), (cS 0 3, 7), (cS 1 1, 3), (cS 1 3, 4), (cS 2 3, 3), (cS 2 4, 4), (cS 2 5, 1), (cS 3 2, 4), (cS 3 4, 6), (cS 3 5, 3), (cS 4 2, 3), (cS 4 4, 5), (cS 5 2, 7), (cS 5 4, 9), (cS 6 1, 3), (cC 2, 10), (cC 3, 3), (cC 4, 6)]),
  .splitS0 [.leaf (20, [(cS 0 4, 7), (cS 0 5, 3), (cS 1 6, 2), (cS 2 1, 10), (cS 2 6, 3), (cS 3 0, 10), (cS 3 2, 14), (cS 3 6, 2), (cS 4 0, 4), (cS 4 1, 3), (cS 4 3, 3), (cS 5 1, 2), (cS 5 2, 16), (cS 5 4, 5), (cS 6 3, 2), (cS 6 4, 3), (cR 4, 3), (cR 5, 2), (cC 5, 10), (cC 6, 5)], [(cS 0 0, 3), (cS 0 1, 7), (cS 0 2, 13), (cS 1 0, 10), (cS 1 3, 2), (cS 1 4, 10), (cS 2 2, 10), (cS 3 3, 2), (cS 3 4, 10), (cS 5 0, 6), (cS 5 6, 1), (cS 6 0, 10), (cS 6 6, 3), (cC 3, 8)]), .leaf (30, [(cS 0 5, 13), (cS 1 5, 9), (cS 1 6, 4), (cS 2 1, 16), (cS 2 6, 9), (cS 3 0, 8), (cS 3 1, 6), (cS 3 2, 13), (cS 3 6, 13), (cS 4 0, 5), (cS 4 1, 2), (cS 4 3, 8), (cS 5 1, 5), (cS 5 2, 18), (cS 6 3, 5), (cS 6 4, 16), (cR 4, 9), (cR 5, 7), (cC 5, 8)], [(cS 0 0, 9), (cS 0 1, 4), (cS 0 2, 22), (cS 0 3, 7), (cS 1 0, 13), (cS 1 3, 9), (cS 1 4, 10), (cS 2 2, 10), (cS 2 3, 7), (cS 3 4, 23), (cS 4 4, 7), (cS 5 0, 2), (cS 5 6, 7), (cS 6 0, 13), (cS 6 1, 4), (cS 6 3, 2), (cS 6 6, 9), (cR 1, 4)]), .leaf (24, [(cS 0 4, 3), (cS 0 5, 3), (cS 1 5, 7), (cS 1 6, 3), (cS 2 1, 13), (cS 2 2, 1), (cS 2 6, 10), (cS 3 0, 11), (cS 3 2, 13), (cS 3 6, 3), (cS 4 0, 2), (cS 4 1, 1), (cS 4 3, 1), (cS 5 1, 1), (cS 5 2, 21), (cS 5 4, 1), (cS 6 3, 1), (cS 6 4, 10), (cR 4, 10), (cR 5, 2), (cC 5, 11)], [(cS 0 0, 10), (cS 0 2, 14), (cS 1 0, 11), (cS 1 1, 3), (cS 1 2, 7), (cS 1 3, 6), (cS 1 4, 8), (cS 3 4, 14), (cS 5 0, 8), (cS 5 6, 2), (cS 6 0, 4), (cS 6 1, 10), (cS 6 6, 10), (cC 3, 10)]), .leaf (2, [(cS 0 4, 1), (cS 1 6, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 4 2, 1), (cR 5, 1), (cC 2, 1), (cC 5, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 1 0, 1), (cS 2 4, 1), (cS 4 4, 1), (cS 6 0, 1), (cS 6 6, 1), (cC 3, 1)]), .leaf (6, [(cS 0 4, 1), (cS 0 5, 2), (cS 0 6, 1), (cS 1 0, 1), (cS 1 5, 1), (cS 2 1, 3), (cS 2 6, 3), (cS 3 0, 2), (cS 3 2, 2), (cS 5 2, 5), (cS 5 4, 1), (cS 6 4, 2), (cR 3, 1), (cR 4, 3), (cR 6, 1), (cC 5, 2)], [(cS 0 0, 2), (cS 0 1, 2), (cS 0 2, 4), (cS 1 0, 2), (cS 1 3, 1), (cS 1 4, 3), (cS 2 2, 3), (cS 3 3, 1), (cS 3 4, 3), (cS 5 0, 3), (cS 5 6, 3), (cS 6 0, 2), (cC 3, 2)]), .leaf (2, [(cS 0 4, 1), (cS 1 6, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 4 2, 1), (cS 5 2, 1), (cR 5, 1), (cC 5, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 1 0, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 4 4, 1), (cS 6 0, 1), (cS 6 6, 1), (cC 3, 1)]), .leaf (24, [(cS 0 4, 5), (cS 0 5, 6), (cS 1 5, 2), (cS 1 6, 5), (cS 2 0, 1), (cS 2 1, 12), (cS 2 6, 6), (cS 3 0, 11), (cS 3 2, 16), (cS 3 6, 7), (cS 4 0, 5), (cS 4 1, 2), (cS 4 3, 2), (cS 5 2, 10), (cS 6 2, 7), (cS 6 4, 7), (cR 4, 6), (cR 5, 7), (cC 5, 11)], [(cS 0 0, 4), (cS 0 1, 9), (cS 0 2, 15), (cS 0 6, 3), (cS 1 0, 12), (cS 1 3, 2), (cS 1 4, 10), (cS 2 2, 12), (cS 3 3, 2), (cS 3 4, 11), (cS 5 0, 4), (cS 5 6, 2), (cS 6 0, 13), (cS 6 6, 5), (cC 3, 10), (cC 4, 2)]), .leaf (8, [(cS 0 5, 4), (cS 1 0, 3), (cS 1 5, 4), (cS 2 0, 1), (cS 2 1, 3), (cS 2 2, 1), (cS 2 6, 4), (cS 5 2, 5), (cS 5 4, 2), (cS 6 4, 2), (cS 6 5, 1), (cR 3, 4), (cR 4, 4), (cR 6, 3)], [(cS 0 0, 5), (cS 0 1, 2), (cS 0 2, 5), (cS 0 3, 2), (cS 1 1, 1), (cS 1 3, 4), (cS 1 4, 2), (cS 2 2, 3), (cS 2 4, 2), (cS 3 4, 6), (cS 4 4, 2), (cS 5 0, 4), (cS 5 6, 4), (cS 6 1, 1), (cS 6 3, 1)]), .leaf (2, [(cS 0 4, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 4 1, 1), (cS 4 3, 1), (cS 5 2, 1), (cS 5 4, 1), (cS 6 2, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 1 0, 1), (cS 1 3, 1), (cS 1 4, 1), (cS 2 2, 1), (cS 3 4, 2), (cS 5 0, 1), (cS 6 0, 1), (cS 6 3, 1)]), .leaf (30, [(cS 0 5, 14), (cS 1 5, 10), (cS 2 0, 2), (cS 2 1, 16), (cS 2 2, 2), (cS 2 6, 16), (cS 3 0, 4), (cS 3 2, 6), (cS 4 0, 2), (cS 5 2, 14), (cS 5 4, 4), (cS 6 2, 10), (cS 6 4, 14), (cR 3, 8), (cR 4, 16), (cR 6, 6), (cC 5, 6)], [(cS 0 0, 14), (cS 0 2, 14), (cS 1 3, 6), (cS 1 4, 2), (cS 2 3, 4), (cS 3 3, 4), (cS 3 4, 16), (cS 4 4, 4), (cS 5 0, 12), (cS 5 6, 18), (cS 6 0, 6), (cS 6 1, 6), (cS 6 2, 6), (cR 0, 4), (cR 1, 12), (cC 3, 6)]), .leaf (12, [(cS 0 4, 3), (cS 0 5, 2), (cS 0 6, 1), (cS 1 5, 2), (cS 1 6, 2), (cS 2 1, 7), (cS 2 6, 3), (cS 3 0, 5), (cS 3 2, 7), (cS 3 6, 4), (cS 4 0, 2), (cS 4 1, 1), (cS 4 3, 1), (cS 5 2, 10), (cS 5 5, 1), (cS 6 3, 1), (cS 6 4, 4), (cR 4, 4), (cR 5, 2), (cC 5, 5)], [(cS 0 0, 2), (cS 0 1, 3), (cS 0 2, 7), (cS 1 0, 2), (cS 1 3, 2), (cS 3 4, 7), (cS 5 0, 3), (cS 5 6, 1), (cS 6 0, 5), (cS 6 1, 2), (cS 6 6, 4), (cR 1, 5), (cC 3, 5)]), .leaf (12, [(cS 0 4, 1), (cS 0 5, 2), (cS 1 4, 1), (cS 2 1, 7), (cS 2 6, 2), (cS 3 0, 5), (cS 3 2, 8), (cS 3 6, 3), (cS 4 0, 6), (cS 4 2, 3), (cS 4 6, 1), (cS 5 1, 3), (cS 5 2, 9), (cS 5 5, 2), (cS 6 3, 3), (cS 6 4, 5), (cR 1, 3), (cR 4, 1), (cC 5, 5), (cC 6, 2)], [(cS 0 0, 2), (cS 0 1, 3), (cS 0 2, 9), (cS 0 3, 3), (cS 1 0, 5), (cS 1 1, 2), (cS 1 3, 4), (cS 2 3, 5), (cS 2 4, 3), (cS 3 4, 4), (cS 4 4, 8), (cS 5 0, 2), (cS 5 4, 4), (cS 5 6, 1), (cS 6 0, 7), (cS 6 6, 3)])],
  .root (20, [(cS 0 5, 7), (cS 1 6, 10), (cS 2 0, 3), (cS 2 1, 12), (cS 2 5, 3), (cS 2 6, 4), (cS 3 0, 2), (cS 3 6, 3), (cS 4 3, 2), (cS 4 4, 10), (cS 4 6, 7), (cS 5 4, 8), (cS 6 4, 7), (cS 6 5, 3), (cR 3, 8), (cC 5, 3)], [(cS 0 0, 4), (cS 0 1, 8), (cS 0 3, 6), (cS 1 4, 7), (cS 2 3, 9), (cS 2 4, 7), (cS 4 1, 5), (cS 5 0, 6), (cS 5 1, 2), (cS 5 2, 7), (cS 5 6, 9), (cS 6 0, 5), (cS 6 6, 5), (cR 0, 3), (cR 5, 2), (cC 0, 3), (cC 1, 2), (cC 2, 7), (cC 3, 4)]),
  .root (6, [(cS 2 3, 6), (cS 4 2, 2), (cS 4 3, 2), (cS 4 5, 2), (cS 5 0, 2), (cS 5 1, 2), (cS 6 0, 1), (cS 6 5, 3), (cS 6 6, 2), (cR 4, 2), (cR 6, 1), (cC 4, 2)], [(cS 0 1, 2), (cS 0 3, 2), (cS 1 6, 1), (cS 2 1, 2), (cS 3 0, 3), (cS 3 1, 3), (cS 3 5, 3), (cS 3 6, 1), (cS 4 6, 1), (cS 6 1, 1), (cS 6 2, 2), (cS 6 3, 3), (cR 0, 1), (cR 1, 3), (cR 2, 1), (cC 6, 1)]),
  .root (24, [(cS 0 5, 6), (cS 2 3, 7), (cS 2 4, 11), (cS 3 0, 1), (cS 3 6, 7), (cS 4 0, 2), (cS 4 1, 2), (cS 4 2, 4), (cS 4 6, 7), (cS 5 1, 6), (cS 5 6, 1), (cS 6 0, 11), (cS 6 4, 5), (cS 6 5, 10), (cS 6 6, 5), (cR 4, 7), (cR 5, 7), (cC 3, 6), (cC 5, 3)], [(cS 0 1, 5), (cS 0 3, 3), (cS 1 1, 4), (cS 1 6, 9), (cS 2 1, 9), (cS 2 6, 4), (cS 3 0, 2), (cS 3 1, 4), (cS 3 2, 1), (cS 4 4, 18), (cS 5 4, 6), (cS 6 2, 11), (cS 6 3, 2), (cR 0, 8), (cR 1, 7), (cR 2, 4), (cR 3, 6)]),
  .root (10, [(cS 0 5, 1), (cS 2 4, 5), (cS 3 6, 7), (cS 4 4, 5), (cS 4 6, 3), (cS 5 6, 7), (cS 6 5, 6), (cS 6 6, 3), (cC 4, 5)], [(cS 0 6, 2), (cS 1 5, 5), (cS 1 6, 3), (cS 2 6, 3), (cC 0, 5), (cC 1, 5), (cC 2, 5), (cC 3, 5)]),
  .root (2, [(cS 2 3, 1), (cS 3 6, 1), (cS 5 2, 1), (cS 6 5, 1), (cR 4, 1), (cC 4, 1)], [(cS 1 2, 1), (cS 1 6, 1), (cS 2 0, 1), (cS 2 5, 1), (cS 3 2, 1), (cS 5 6, 1), (cS 6 0, 1), (cS 6 3, 1), (cR 0, 1), (cC 1, 1)]),
  .root (4, [(cS 0 5, 2), (cS 1 3, 2), (cS 2 1, 1), (cS 2 2, 2), (cS 2 4, 2), (cS 3 0, 1), (cS 3 1, 2), (cS 3 3, 2), (cS 4 0, 1), (cS 4 2, 2), (cS 5 1, 1), (cS 6 0, 1), (cS 6 4, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 5, 2)], [(cS 0 1, 1), (cS 1 1, 1), (cS 1 6, 2), (cS 2 0, 2), (cS 2 5, 2), (cS 3 6, 2), (cS 4 4, 4), (cS 4 6, 2), (cS 6 2, 1), (cS 6 3, 1), (cR 0, 2)]),
  .root (8, [(cS 0 5, 1), (cS 1 3, 1), (cS 2 1, 3), (cS 2 2, 3), (cS 2 3, 4), (cS 2 4, 1), (cS 3 1, 5), (cS 3 2, 1), (cS 3 4, 1), (cS 4 3, 5), (cS 4 5, 5), (cS 5 0, 2), (cS 5 4, 1), (cS 5 6, 2), (cS 6 4, 1), (cS 6 5, 4), (cS 6 6, 4), (cC 4, 2)], [(cS 0 1, 3), (cS 0 2, 2), (cS 0 3, 3), (cS 1 5, 3), (cS 1 6, 3), (cS 2 0, 1), (cS 2 5, 1), (cS 3 5, 3), (cS 3 6, 4), (cS 4 2, 1), (cS 4 6, 1), (cS 5 1, 3), (cS 5 2, 3), (cS 5 3, 3), (cS 6 1, 1), (cS 6 3, 1), (cR 0, 1), (cR 1, 1), (cC 0, 3), (cC 2, 1)]),
  .root (5, [(cS 1 3, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 2 3, 2), (cS 3 0, 1), (cS 3 1, 3), (cS 3 3, 1), (cS 4 1, 1), (cS 4 2, 3), (cS 4 4, 4), (cS 5 2, 1), (cS 6 4, 3), (cS 6 5, 1), (cC 3, 1), (cC 4, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 1 2, 3), (cS 2 0, 1), (cS 2 5, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 2, 3), (cR 0, 1), (cC 0, 3), (cC 5, 3), (cC 6, 1)]),
  .root (60, [(cS 1 3, 3), (cS 2 2, 18), (cS 2 3, 20), (cS 2 4, 18), (cS 3 0, 18), (cS 3 1, 20), (cS 4 1, 17), (cS 4 5, 23), (cS 4 6, 37), (cS 5 0, 43), (cS 6 0, 17), (cS 6 4, 25), (cS 6 5, 35), (cS 6 6, 25), (cR 2, 19), (cR 3, 5)], [(cS 0 0, 3), (cS 0 1, 5), (cS 0 6, 5), (cS 1 4, 5), (cS 1 5, 3), (cS 2 5, 10), (cS 2 6, 18), (cS 3 3, 9), (cS 3 5, 9), (cS 4 2, 46), (cS 4 4, 51), (cS 5 2, 9), (cS 5 4, 9), (cS 6 1, 25), (cS 6 2, 21), (cS 6 3, 26), (cR 0, 10), (cR 1, 42), (cC 2, 5)]),
  .root (20, [(cS 1 3, 5), (cS 2 1, 8), (cS 2 2, 6), (cS 2 3, 9), (cS 2 4, 6), (cS 3 0, 6), (cS 4 2, 5), (cS 4 5, 2), (cS 4 6, 3), (cS 5 1, 1), (cS 5 2, 5), (cS 5 3, 1), (cS 6 4, 10), (cS 6 5, 10), (cR 3, 6), (cR 4, 9)], [(cS 0 1, 5), (cS 0 2, 4), (cS 1 0, 5), (cS 1 4, 4), (cS 1 5, 5), (cS 2 5, 5), (cS 2 6, 5), (cS 3 4, 3), (cS 4 4, 17), (cS 5 1, 6), (cS 6 0, 9), (cS 6 2, 6), (cS 6 3, 6), (cS 6 6, 3), (cR 0, 5), (cR 1, 6), (cR 5, 3), (cC 0, 1), (cC 6, 4)]),
  .root (20, [(cS 1 3, 2), (cS 2 1, 6), (cS 2 2, 8), (cS 2 3, 10), (cS 3 0, 8), (cS 3 1, 3), (cS 3 5, 3), (cS 4 3, 7), (cS 4 4, 2), (cS 4 5, 4), (cS 4 6, 10), (cS 5 4, 3), (cS 5 5, 3), (cS 6 5, 12), (cR 3, 3), (cC 4, 8)], [(cS 0 2, 7), (cS 1 0, 5), (cS 1 5, 7), (cS 2 5, 7), (cS 2 6, 7), (cS 4 1, 4), (cS 4 2, 10), (cS 5 0, 4), (cS 5 1, 6), (cS 5 2, 6), (cS 5 3, 1), (cS 6 0, 8), (cS 6 2, 4), (cS 6 3, 4), (cR 0, 7), (cR 1, 6), (cR 5, 3), (cR 6, 2), (cC 0, 3)]),
  .root (8, [(cS 0 4, 4), (cS 0 5, 4), (cS 1 3, 1), (cS 1 6, 4), (cS 2 2, 4), (cS 2 3, 1), (cS 2 4, 4), (cS 2 5, 4), (cS 3 3, 1), (cS 4 0, 2), (cS 4 1, 1), (cS 4 2, 2), (cS 5 1, 1), (cS 6 0, 3), (cS 6 4, 1), (cS 6 5, 3), (cS 6 6, 1), (cR 5, 4), (cC 3, 2)], [(cS 0 0, 4), (cS 0 1, 1), (cS 0 2, 4), (cS 0 3, 1), (cS 1 1, 3), (cS 2 1, 5), (cS 2 6, 4), (cS 3 1, 2), (cS 3 6, 3), (cS 4 4, 5), (cS 4 6, 2), (cS 5 4, 1), (cS 6 2, 3), (cR 3, 1), (cR 4, 2)]),
  .root (3, [(cS 0 5, 1), (cS 1 3, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 2 5, 1), (cS 3 3, 1), (cS 4 4, 1), (cS 5 4, 1), (cS 5 6, 2), (cS 6 6, 1), (cC 4, 1), (cC 5, 1)], [(cS 0 3, 1), (cS 3 6, 3), (cS 4 3, 1), (cS 6 3, 1), (cC 0, 2), (cC 1, 1), (cC 2, 2)]),
  .root (20, [(cS 0 5, 3), (cS 1 5, 3), (cS 1 6, 4), (cS 2 2, 3), (cS 2 3, 9), (cS 2 5, 3), (cS 3 4, 3), (cS 4 2, 10), (cS 4 3, 2), (cS 4 4, 3), (cS 5 2, 10), (cS 5 4, 3), (cS 6 4, 3), (cC 3, 8), (cC 4, 4), (cC 5, 10)], [(cS 0 0, 6), (cS 0 2, 9), (cS 0 3, 8), (cS 1 0, 3), (cS 1 2, 3), (cS 2 1, 6), (cS 2 6, 6), (cS 3 1, 3), (cS 3 6, 7), (cS 4 1, 6), (cS 4 6, 6), (cS 5 0, 3), (cS 5 5, 3), (cS 5 6, 4), (cS 6 0, 7), (cS 6 3, 3), (cC 1, 11), (cC 6, 7)]),
  .root (5, [(cS 0 4, 1), (cS 0 5, 1), (cS 0 6, 1), (cS 1 5, 2), (cS 2 4, 4), (cS 2 6, 1), (cS 3 6, 2), (cS 4 6, 1), (cS 5 0, 5), (cS 5 5, 2), (cS 6 4, 1), (cS 6 5, 1), (cC 4, 1), (cC 6, 2)], [(cS 1 0, 2), (cS 3 1, 2), (cS 4 4, 5), (cS 6 0, 2), (cC 1, 3), (cC 2, 2), (cC 3, 3)]),
  .root (20, [(cS 0 5, 2), (cS 1 5, 3), (cS 1 6, 9), (cS 2 3, 5), (cS 2 4, 6), (cS 2 6, 2), (cS 3 0, 6), (cS 3 6, 12), (cS 4 2, 10), (cS 4 6, 2), (cS 5 2, 10), (cS 5 4, 2), (cS 6 4, 3), (cC 4, 9), (cC 5, 6)], [(cS 0 1, 5), (cS 0 2, 4), (cS 0 3, 5), (cS 0 6, 3), (cS 2 1, 5), (cS 2 2, 4), (cS 4 4, 14), (cS 4 5, 6), (cS 5 0, 5), (cS 5 6, 6), (cS 6 6, 9), (cC 0, 9), (cC 1, 6), (cC 2, 5), (cC 3, 6)]),
  .root (1, [(cC 4, 1), (cC 6, 1)], [(cC 0, 1), (cC 2, 1)]),
  .root (24, [(cS 0 4, 2), (cS 0 6, 4), (cS 1 3, 11), (cS 1 6, 6), (cS 2 1, 2), (cS 2 2, 8), (cS 2 5, 2), (cS 3 0, 3), (cS 3 1, 16), (cS 3 3, 13), (cS 5 0, 13), (cS 5 6, 5), (cS 6 0, 11), (cS 6 4, 3), (cS 6 5, 3), (cS 6 6, 6), (cR 1, 3), (cR 2, 3), (cC 4, 8), (cC 5, 11)], [(cS 0 0, 3), (cS 0 1, 5), (cS 0 2, 11), (cS 1 0, 8), (cS 1 1, 8), (cS 2 6, 5), (cS 3 6, 19), (cS 4 2, 2), (cS 4 3, 3), (cS 4 4, 15), (cS 4 5, 3), (cS 5 1, 5), (cS 5 2, 11), (cS 5 3, 2), (cS 6 1, 5), (cS 6 2, 3), (cS 6 3, 11), (cR 4, 6)]),
  .root (2, [(cS 0 4, 1), (cS 0 6, 1), (cS 3 1, 1), (cS 4 0, 1), (cS 4 2, 1), (cS 5 1, 1), (cS 5 4, 1), (cR 2, 1), (cC 3, 1), (cC 5, 1)], [(cS 0 0, 1), (cS 0 2, 1), (cS 1 1, 1), (cS 2 6, 1), (cS 3 6, 1), (cS 4 4, 2), (cS 4 6, 1), (cS 5 6, 1), (cS 6 0, 1), (cS 6 2, 1)]),
  .root (4, [(cS 0 6, 2), (cS 1 3, 2), (cS 2 0, 2), (cS 2 1, 1), (cS 2 2, 2), (cS 2 6, 2), (cS 3 1, 1), (cS 3 3, 2), (cS 4 3, 2), (cC 4, 2), (cC 5, 2)], [(cS 0 0, 2), (cS 0 1, 1), (cS 0 2, 2), (cS 0 3, 2), (cS 2 6, 2), (cS 3 6, 2), (cS 4 1, 2), (cS 4 6, 2), (cS 5 2, 2), (cS 5 3, 1), (cS 5 6, 1), (cS 6 0, 2), (cR 5, 1), (cC 1, 1)]),
  .root (8, [(cS 0 4, 2), (cS 1 3, 3), (cS 1 4, 2), (cS 1 5, 1), (cS 1 6, 4), (cS 2 0, 1), (cS 2 3, 2), (cS 3 0, 2), (cS 3 1, 2), (cS 3 6, 2), (cS 6 5, 6), (cR 1, 1), (cR 2, 2), (cR 3, 4), (cC 5, 2)], [(cS 0 0, 8), (cS 0 2, 3), (cS 1 1, 4), (cS 3 4, 2), (cS 4 2, 4), (cS 4 3, 3), (cS 4 4, 3), (cS 4 5, 3), (cS 5 0, 5), (cS 5 1, 1), (cS 5 6, 1), (cS 6 2, 4), (cS 6 3, 1), (cS 6 4, 5), (cR 5, 2), (cC 2, 1)]),
  .root (20, [(cS 0 0, 6), (cS 0 1, 6), (cS 0 6, 6), (cS 1 0, 8), (cS 4 2, 6), (cS 4 3, 7), (cS 4 4, 6), (cS 4 5, 7), (cS 5 0, 6), (cS 5 1, 7), (cS 5 6, 6), (cS 6 4, 5), (cS 6 5, 7), (cR 4, 7), (cR 6, 8)], [(cS 0 3, 10), (cS 0 4, 3), (cS 0 5, 2), (cS 1 1, 4), (cS 1 2, 3), (cS 1 5, 8), (cS 1 6, 3), (cS 2 2, 4), (cS 2 3, 7), (cS 2 4, 4), (cS 3 0, 6), (cS 3 1, 7), (cS 3 5, 7), (cS 3 6, 5), (cS 4 6, 2), (cS 6 2, 6), (cS 6 3, 7), (cR 1, 7), (cR 2, 2), (cR 3, 7)]),
  .root (4, [(cS 0 0, 2), (cS 1 0, 1), (cS 1 1, 1), (cS 4 1, 2), (cS 4 2, 2), (cS 4 6, 4), (cS 5 0, 2), (cS 5 2, 2), (cS 6 5, 2), (cR 6, 2)], [(cS 0 2, 2), (cS 0 3, 2), (cS 0 5, 2), (cS 1 3, 1), (cS 1 5, 1), (cS 4 4, 2), (cS 5 4, 2), (cR 1, 1), (cR 2, 2), (cR 3, 2)]),
  .root (5, [(cS 0 0, 1), (cS 0 1, 2), (cS 1 0, 1), (cS 1 1, 1), (cS 4 4, 5), (cS 4 6, 4), (cS 5 0, 1), (cS 6 0, 2), (cS 6 4, 2), (cS 6 5, 3), (cS 6 6, 1), (cC 6, 1)], [(cS 0 3, 1), (cS 0 4, 1), (cS 0 5, 2), (cS 1 3, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 1, 1), (cS 2 4, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 4 1, 2), (cS 4 3, 1), (cS 5 1, 2), (cS 5 3, 2), (cS 6 2, 2), (cR 1, 1), (cR 2, 1), (cR 3, 2), (cC 2, 1), (cC 3, 1)]),
  .root (2, [(cS 0 0, 1), (cS 0 1, 1), (cS 4 4, 1), (cS 4 6, 1), (cS 5 2, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 4, 1)], [(cS 0 3, 1), (cS 1 5, 1), (cS 5 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1), (cR 6, 1)]),
  .root (4, [(cS 0 6, 1), (cS 1 2, 1), (cS 3 2, 1), (cS 4 2, 1), (cS 5 3, 1), (cS 5 6, 1), (cS 6 2, 1), (cS 6 4, 1), (cS 6 5, 3), (cC 0, 3), (cC 1, 1), (cC 2, 2)], [(cS 0 3, 3), (cS 0 5, 1), (cS 1 5, 3), (cS 2 4, 3), (cS 2 6, 1), (cS 3 4, 1), (cS 3 6, 3), (cS 4 4, 2), (cS 4 5, 1), (cS 4 6, 2), (cS 5 4, 1), (cC 3, 1)]),
  .root (2, [(cS 0 0, 1), (cS 2 1, 1), (cS 4 4, 2), (cS 5 6, 1), (cS 6 4, 1), (cS 6 5, 1), (cS 6 6, 1), (cC 1, 1)], [(cS 0 5, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 4, 1), (cS 2 6, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 4 6, 1), (cS 5 1, 1), (cC 2, 1), (cC 3, 1)]),
  .root (2, [(cS 0 0, 1), (cS 1 1, 1), (cS 2 0, 1), (cS 2 2, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 4 4, 2), (cS 5 3, 1), (cS 6 4, 1), (cS 6 5, 1)], [(cS 1 3, 1), (cS 1 5, 1), (cS 2 4, 1), (cS 2 6, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 2, 1), (cR 0, 1)]),
  .root (3, [(cS 0 0, 1), (cS 1 1, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 4 1, 1), (cS 4 6, 2), (cS 5 0, 1), (cS 6 0, 1), (cS 6 4, 1), (cS 6 5, 2), (cC 1, 1), (cC 6, 1)], [(cS 0 3, 1), (cS 0 5, 1), (cS 1 3, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 4, 1), (cS 2 6, 1), (cS 4 4, 1), (cS 5 2, 1), (cS 5 4, 1), (cR 3, 1), (cC 2, 2), (cC 4, 1)]),
  .root (2, [(cS 1 1, 1), (cS 2 1, 1), (cS 3 2, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 4 2, 1), (cS 4 5, 1), (cS 5 2, 1), (cS 6 2, 1), (cS 6 4, 1), (cS 6 5, 1), (cC 0, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 0 5, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 2 5, 1), (cS 4 4, 1), (cS 5 6, 1), (cS 6 0, 1), (cC 4, 1)]),
  .root (4, [(cS 0 0, 1), (cS 0 1, 1), (cS 1 1, 2), (cS 2 1, 2), (cS 2 6, 1), (cS 3 0, 1), (cS 3 1, 2), (cS 3 6, 1), (cS 4 3, 1), (cS 4 4, 3), (cS 4 5, 1), (cS 4 6, 2), (cS 6 4, 2), (cS 6 5, 2)], [(cS 1 4, 2), (cS 1 5, 1), (cS 1 6, 2), (cS 2 3, 1), (cS 2 4, 2), (cS 2 5, 2), (cS 5 0, 1), (cS 5 1, 1), (cS 6 6, 1), (cR 0, 1), (cR 5, 1), (cC 0, 1), (cC 2, 2), (cC 3, 1)]),
  .root (6, [(cS 0 1, 1), (cS 0 2, 1), (cS 1 0, 4), (cS 1 2, 2), (cS 1 5, 6), (cS 4 1, 3), (cS 4 2, 1), (cS 4 3, 1), (cS 5 1, 1), (cS 5 2, 3), (cS 5 3, 1), (cS 6 0, 1), (cS 6 4, 1), (cS 6 5, 3), (cS 6 6, 1), (cR 6, 2), (cC 0, 2)], [(cS 0 2, 2), (cS 0 3, 4), (cS 1 3, 2), (cS 4 3, 2), (cS 4 4, 2), (cS 4 5, 2), (cS 4 6, 4), (cS 5 4, 2), (cR 2, 4), (cR 3, 2)]),
  .root (5, [(cS 0 1, 2), (cS 1 0, 3), (cS 1 5, 2), (cS 4 3, 1), (cS 4 4, 2), (cS 6 0, 3), (cS 6 5, 2), (cC 4, 2), (cC 5, 1), (cC 6, 2)], [(cS 0 3, 1), (cS 1 3, 1), (cS 2 1, 1), (cS 3 6, 3), (cS 4 0, 1), (cS 4 1, 1), (cS 4 6, 2), (cS 5 1, 1), (cS 5 2, 1), (cR 2, 1), (cR 3, 1), (cC 1, 2), (cC 2, 1), (cC 3, 3)]),
  .splitS0 [.leaf (4, [(cS 0 0, 2), (cS 0 6, 1), (cS 1 0, 2), (cS 1 6, 1), (cS 2 6, 1), (cS 4 2, 2), (cS 4 3, 2), (cS 5 2, 2), (cC 4, 2), (cC 5, 2)], [(cS 0 2, 2), (cS 1 3, 2), (cS 2 2, 2), (cS 2 3, 2), (cS 3 0, 2), (cS 3 6, 1), (cS 4 6, 1), (cS 5 0, 2), (cS 5 6, 1), (cS 6 3, 2), (cS 6 6, 1), (cC 1, 2)]), .leaf (16, [(cS 0 0, 3), (cS 0 1, 5), (cS 0 6, 1), (cS 1 0, 4), (cS 1 1, 4), (cS 1 6, 8), (cS 2 0, 1), (cS 2 6, 3), (cS 3 2, 1), (cS 3 3, 6), (cS 4 1, 3), (cS 4 2, 4), (cS 4 3, 5), (cS 5 1, 4), (cS 5 2, 5), (cS 5 3, 3), (cC 4, 8), (cC 5, 8)], [(cS 0 2, 3), (cS 0 3, 3), (cS 1 3, 13), (cS 2 1, 3), (cS 2 2, 6), (cS 2 3, 3), (cS 3 0, 6), (cS 3 1, 4), (cS 3 6, 6), (cS 4 6, 10), (cS 5 0, 5), (cS 5 6, 1), (cS 6 0, 4), (cS 6 2, 4), (cS 6 3, 6), (cS 6 6, 8), (cC 1, 4)]), .leaf (2, [(cS 0 1, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 2 6, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 5 2, 1), (cC 4, 1), (cC 5, 1)], [(cS 0 3, 1), (cS 1 3, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 6 3, 1), (cS 6 6, 1), (cC 1, 1)]), .leaf (20, [(cS 0 0, 3), (cS 0 1, 6), (cS 0 6, 5), (cS 1 0, 9), (cS 1 1, 2), (cS 1 6, 6), (cS 2 6, 5), (cS 3 3, 2), (cS 4 2, 12), (cS 4 3, 6), (cS 5 2, 8), (cS 5 3, 3), (cS 6 6, 3), (cC 4, 12), (cC 5, 9)], [(cS 0 2, 6), (cS 0 3, 6), (cS 1 3, 8), (cS 1 4, 6), (cS 2 0, 4), (cS 2 2, 12), (cS 2 3, 6), (cS 3 0, 10), (cS 3 2, 2), (cS 3 6, 6), (cS 4 0, 1), (cS 4 1, 3), (cS 4 6, 6), (cS 5 0, 7), (cS 5 1, 3), (cS 5 6, 6), (cS 6 0, 5), (cS 6 2, 3), (cS 6 3, 6), (cS 6 6, 4), (cC 1, 6)]), .leaf (2, [(cS 0 1, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 2 6, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 5 2, 1), (cC 4, 1), (cC 5, 1)], [(cS 0 3, 1), (cS 1 3, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 6 3, 1), (cS 6 6, 1), (cC 1, 1)]), .leaf (8, [(cS 0 0, 1), (cS 0 1, 4), (cS 0 6, 1), (cS 1 0, 3), (cS 1 5, 1), (cS 1 6, 1), (cS 2 6, 2), (cS 4 2, 5), (cS 4 3, 3), (cS 4 4, 1), (cS 5 2, 3), (cS 6 4, 1), (cC 4, 4), (cC 5, 3), (cC 6, 2)], [(cS 0 2, 1), (cS 0 3, 3), (cS 1 2, 3), (cS 1 3, 1), (cS 2 1, 5), (cS 2 3, 7), (cS 3 0, 2), (cS 3 1, 2), (cS 3 6, 1), (cS 4 0, 3), (cS 4 6, 1), (cS 5 0, 2), (cS 5 1, 1), (cS 6 0, 2), (cS 6 1, 1), (cS 6 2, 2), (cS 6 3, 2), (cS 6 6, 2), (cR 3, 1), (cR 5, 2)]), .leaf (16, [(cS 0 0, 2), (cS 0 1, 3), (cS 0 6, 3), (cS 1 0, 5), (cS 1 1, 6), (cS 1 6, 6), (cS 2 6, 5), (cS 3 3, 4), (cS 4 2, 9), (cS 4 3, 3), (cS 5 1, 7), (cS 5 3, 4), (cC 4, 9), (cC 5, 8)], [(cS 0 1, 4), (cS 0 2, 1), (cS 0 3, 2), (cS 1 3, 14), (cS 2 2, 8), (cS 2 3, 3), (cS 3 0, 8), (cS 3 1, 1), (cS 3 2, 5), (cS 3 6, 3), (cS 4 6, 5), (cS 5 0, 3), (cS 5 6, 3), (cS 6 2, 8), (cS 6 3, 5), (cS 6 6, 6), (cC 0, 5), (cC 1, 2)]), .leaf (4, [(cS 0 0, 1), (cS 0 1, 2), (cS 0 6, 1), (cS 1 0, 1), (cS 1 6, 1), (cS 2 0, 1), (cS 2 6, 1), (cS 4 2, 2), (cS 4 3, 2), (cS 5 1, 2), (cC 4, 2), (cC 5, 2)], [(cS 1 2, 2), (cS 2 1, 2), (cS 2 3, 2), (cS 3 0, 1), (cS 3 1, 2), (cS 3 6, 1), (cS 4 0, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 6, 1), (cS 6 0, 1), (cS 6 2, 2), (cS 6 6, 1), (cC 3, 2)]), .leaf (4, [(cS 0 0, 2), (cS 0 6, 1), (cS 1 0, 2), (cS 1 6, 1), (cS 2 6, 1), (cS 4 2, 2), (cS 4 3, 2), (cS 5 2, 2), (cC 4, 2), (cC 5, 2)], [(cS 0 2, 2), (cS 1 3, 2), (cS 2 2, 2), (cS 2 3, 2), (cS 3 0, 2), (cS 3 6, 1), (cS 4 6, 1), (cS 5 0, 2), (cS 5 6, 1), (cS 6 3, 2), (cS 6 6, 1), (cC 1, 2)]), .leaf (10, [(cS 0 1, 1), (cS 1 0, 8), (cS 1 1, 1), (cS 1 5, 4), (cS 1 6, 2), (cS 3 3, 4), (cS 4 1, 1), (cS 4 2, 4), (cS 4 4, 4), (cS 5 1, 3), (cS 5 3, 4), (cS 6 4, 3), (cS 6 5, 1), (cC 2, 2), (cC 4, 2), (cC 5, 4)], [(cS 0 2, 2), (cS 0 3, 2), (cS 1 3, 6), (cS 2 1, 1), (cS 3 1, 3), (cS 3 6, 6), (cS 4 0, 4), (cS 4 6, 4), (cS 5 6, 2), (cS 6 0, 5), (cS 6 2, 3), (cS 6 3, 1), (cS 6 6, 3), (cR 0, 2), (cR 2, 4), (cC 1, 2)]), .leaf (24, [(cS 0 0, 1), (cS 0 1, 10), (cS 0 6, 6), (cS 1 0, 4), (cS 1 5, 5), (cS 1 6, 3), (cS 2 6, 9), (cS 4 1, 1), (cS 4 2, 17), (cS 4 3, 7), (cS 4 4, 7), (cS 5 1, 6), (cS 6 4, 5), (cS 6 5, 1), (cR 1, 2), (cC 0, 8), (cC 4, 10), (cC 5, 8)], [(cS 1 2, 10), (cS 1 3, 7), (cS 2 1, 9), (cS 2 3, 10), (cS 3 1, 5), (cS 4 6, 17), (cS 5 0, 6), (cS 5 6, 7), (cS 6 0, 2), (cS 6 2, 15), (cS 6 3, 2), (cS 6 6, 9), (cR 3, 7), (cC 1, 3), (cC 3, 7)]), .leaf (16, [(cS 0 0, 3), (cS 0 1, 5), (cS 0 6, 3), (cS 1 0, 6), (cS 1 1, 2), (cS 1 5, 1), (cS 1 6, 4), (cS 2 0, 1), (cS 2 6, 6), (cS 3 2, 1), (cS 3 3, 3), (cS 4 1, 3), (cS 4 2, 4), (cS 4 3, 8), (cS 4 4, 1), (cS 5 1, 4), (cS 5 2, 5), (cS 6 4, 1), (cC 4, 7), (cC 5, 8)], [(cS 0 2, 3), (cS 0 3, 1), (cS 1 2, 2), (cS 1 3, 10), (cS 2 1, 3), (cS 2 2, 6), (cS 2 3, 6), (cS 2 4, 1), (cS 3 0, 6), (cS 3 1, 4), (cS 3 6, 3), (cS 4 6, 13), (cS 5 0, 5), (cS 5 6, 3), (cS 6 0, 4), (cS 6 2, 4), (cS 6 3, 8), (cS 6 6, 6), (cC 1, 4)])],
  .splitS0 [.leaf (1, [(cC 0, 1), (cC 5, 1)], [(cC 2, 1), (cC 4, 1)]), .leaf (1, [(cC 0, 1), (cC 5, 1)], [(cC 1, 1), (cC 3, 1)]), .leaf (1, [(cC 0, 1), (cC 5, 1)], [(cC 1, 1), (cC 3, 1)]), .leaf (1, [(cC 0, 1), (cC 5, 1)], [(cC 1, 1), (cC 3, 1)]), .leaf (1, [(cC 0, 1), (cC 5, 1)], [(cC 2, 1), (cC 4, 1)]), .leaf (1, [(cC 0, 1), (cC 5, 1)], [(cC 2, 1), (cC 4, 1)]), .leaf (1, [(cC 0, 1), (cC 5, 1)], [(cC 2, 1), (cC 4, 1)]), .leaf (1, [(cC 0, 1), (cC 5, 1)], [(cC 2, 1), (cC 4, 1)]), .leaf (1, [(cC 0, 1), (cC 5, 1)], [(cC 1, 1), (cC 3, 1)]), .leaf (1, [(cC 0, 1), (cC 5, 1)], [(cC 1, 1), (cC 3, 1)]), .leaf (1, [(cC 0, 1), (cC 5, 1)], [(cC 1, 1), (cC 3, 1)]), .leaf (1, [(cC 0, 1), (cC 5, 1)], [(cC 2, 1), (cC 4, 1)])],
  .root (6, [(cS 0 0, 1), (cS 0 1, 2), (cS 0 5, 3), (cS 1 0, 3), (cS 1 5, 3), (cS 1 6, 1), (cS 2 6, 1), (cS 3 6, 4), (cS 4 2, 1), (cS 4 6, 1), (cS 5 2, 5), (cS 5 5, 3), (cS 6 4, 2), (cR 6, 1), (cC 6, 1)], [(cS 0 2, 3), (cS 0 3, 3), (cS 1 2, 1), (cS 1 3, 3), (cS 2 1, 3), (cS 2 2, 2), (cS 2 4, 3), (cS 3 2, 1), (cS 4 0, 2), (cS 4 4, 2), (cS 5 0, 3), (cS 5 4, 3), (cS 6 0, 2), (cS 6 6, 1), (cR 3, 3), (cR 4, 1)]),
  .root (20, [(cS 0 0, 8), (cS 0 1, 3), (cS 0 5, 7), (cS 1 0, 6), (cS 1 1, 3), (cS 1 5, 4), (cS 2 0, 1), (cS 2 5, 3), (cS 2 6, 4), (cS 3 4, 8), (cS 3 6, 6), (cS 4 4, 12), (cS 4 6, 5), (cS 5 4, 8), (cS 6 4, 7), (cS 6 5, 6), (cC 6, 9)], [(cS 0 3, 2), (cS 0 4, 5), (cS 1 3, 3), (cS 1 4, 4), (cS 2 1, 3), (cS 2 3, 2), (cS 2 4, 9), (cS 3 0, 7), (cS 3 1, 3), (cS 3 3, 3), (cS 4 0, 3), (cS 4 2, 2), (cS 5 0, 10), (cS 5 2, 3), (cS 5 6, 6), (cS 6 0, 3), (cS 6 2, 3), (cC 0, 1), (cC 1, 6), (cC 2, 9), (cC 3, 6)]),
  .root (6, [(cS 0 5, 3), (cS 1 1, 1), (cS 1 2, 1), (cS 1 5, 3), (cS 1 6, 3), (cS 2 2, 2), (cS 3 1, 1), (cS 3 2, 3), (cS 5 5, 3), (cS 6 0, 1), (cS 6 4, 2), (cS 6 5, 1), (cS 6 6, 2), (cC 0, 3), (cC 1, 2)], [(cS 0 2, 1), (cS 0 3, 2), (cS 1 3, 2), (cS 2 4, 2), (cS 3 4, 2), (cS 3 6, 6), (cS 5 2, 2), (cS 5 4, 1), (cS 6 2, 2), (cR 4, 2), (cR 5, 1), (cC 2, 1), (cC 4, 2)]),
  .root (5, [(cS 0 5, 1), (cS 0 6, 1), (cS 1 5, 4), (cS 1 6, 1), (cS 3 3, 1), (cS 5 3, 1), (cS 5 4, 1), (cS 6 4, 1), (cS 6 5, 3), (cC 0, 4), (cC 1, 1), (cC 2, 4)], [(cS 0 3, 4), (cS 1 3, 1), (cS 2 4, 4), (cS 3 4, 1), (cS 3 6, 5), (cS 4 4, 4), (cS 5 4, 1), (cS 5 6, 5), (cS 6 3, 1)]),
  .root (4, [(cS 0 0, 1), (cS 0 1, 2), (cS 0 5, 1), (cS 1 1, 1), (cS 1 5, 1), (cS 1 6, 3), (cS 2 0, 1), (cS 2 1, 2), (cS 2 2, 1), (cS 3 1, 1), (cS 3 4, 1), (cS 4 4, 2), (cS 5 4, 1), (cS 6 5, 2), (cC 4, 1)], [(cS 1 3, 1), (cS 2 4, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 3 3, 1), (cS 3 6, 3), (cS 4 1, 2), (cS 4 2, 1), (cS 4 6, 1), (cS 5 1, 2), (cS 5 2, 1), (cS 5 6, 3), (cS 6 0, 2), (cS 6 2, 1), (cR 0, 1), (cC 3, 2)]),
  .splitS0 [.leaf (2, [(cS 0 1, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 2 1, 1), (cS 3 1, 2), (cS 3 6, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 1 3, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 0, 1), (cS 6 2, 1), (cC 3, 1)]), .leaf (6, [(cS 0 4, 2), (cS 1 0, 2), (cS 1 1, 1), (cS 1 4, 1), (cS 2 2, 2), (cS 3 0, 2), (cS 3 1, 2), (cS 3 2, 2), (cS 3 6, 1), (cS 5 4, 2), (cS 6 4, 1), (cS 6 5, 1), (cR 1, 1), (cC 1, 2), (cC 5, 2), (cC 6, 3)], [(cS 0 2, 2), (cS 1 3, 2), (cS 1 4, 2), (cS 3 4, 4), (cS 4 2, 2), (cS 4 4, 2), (cS 5 0, 2), (cS 5 1, 2), (cS 5 2, 2), (cS 5 6, 1), (cS 6 0, 3), (cS 6 1, 1), (cS 6 2, 1), (cS 6 3, 1), (cC 3, 2)]), .leaf (2, [(cS 0 4, 1), (cS 1 0, 1), (cS 2 2, 1), (cS 3 0, 1), (cS 4 2, 1), (cS 5 4, 1), (cC 1, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 1 4, 1), (cS 3 4, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 0, 1), (cC 3, 1)]), .leaf (16, [(cS 0 0, 1), (cS 0 4, 3), (cS 0 5, 2), (cS 1 0, 5), (cS 1 1, 3), (cS 1 5, 2), (cS 2 2, 5), (cS 2 6, 1), (cS 3 0, 5), (cS 3 1, 6), (cS 3 2, 5), (cS 3 6, 3), (cS 4 6, 1), (cS 5 5, 3), (cS 6 4, 6), (cS 6 5, 1), (cR 1, 3), (cC 1, 5), (cC 5, 6), (cC 6, 7)], [(cS 0 2, 6), (cS 1 3, 4), (cS 2 4, 6), (cS 3 4, 4), (cS 4 2, 5), (cS 4 4, 7), (cS 5 0, 8), (cS 5 1, 8), (cS 5 2, 3), (cS 5 3, 3), (cS 6 0, 8), (cS 6 1, 2), (cS 6 2, 3), (cS 6 3, 1), (cC 3, 6)]), .leaf (2, [(cS 0 4, 1), (cS 1 6, 1), (cS 2 1, 1), (cS 3 2, 1), (cS 3 6, 1), (cS 5 4, 1), (cS 6 6, 1), (cC 0, 1), (cC 1, 1), (cC 5, 1)], [(cS 1 4, 1), (cS 3 4, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 6, 1), (cC 2, 1), (cC 3, 1)]), .leaf (24, [(cS 0 0, 2), (cS 0 4, 3), (cS 0 5, 3), (cS 1 1, 10), (cS 1 6, 7), (cS 2 1, 2), (cS 2 6, 2), (cS 3 0, 7), (cS 3 1, 17), (cS 3 6, 5), (cS 4 6, 2), (cS 5 5, 4), (cS 6 4, 5), (cS 6 5, 3), (cR 1, 5), (cC 1, 7), (cC 4, 5), (cC 5, 8), (cC 6, 10)], [(cS 0 2, 5), (cS 2 3, 5), (cS 2 4, 8), (cS 3 4, 3), (cS 4 2, 4), (cS 4 3, 2), (cS 4 4, 8), (cS 5 0, 12), (cS 5 1, 12), (cS 5 3, 3), (cS 6 0, 12), (cS 6 1, 3), (cS 6 2, 2), (cC 2, 8), (cC 3, 11)]), .leaf (2, [(cS 0 1, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 2 1, 1), (cS 3 1, 2), (cS 3 6, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 1 3, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 0, 1), (cS 6 2, 1), (cC 3, 1)]), .leaf (8, [(cS 0 1, 2), (cS 0 4, 2), (cS 0 5, 2), (cS 1 0, 4), (cS 1 1, 4), (cS 1 5, 2), (cS 2 2, 4), (cS 3 0, 2), (cS 3 1, 6), (cS 3 2, 2), (cS 3 6, 2), (cS 5 4, 4), (cS 6 4, 1), (cS 6 5, 1), (cS 6 6, 1), (cC 5, 2), (cC 6, 4)], [(cS 0 2, 2), (cS 0 3, 2), (cS 1 3, 2), (cS 1 4, 2), (cS 2 4, 2), (cS 3 4, 6), (cS 4 2, 2), (cS 5 0, 6), (cS 5 2, 4), (cS 6 0, 3), (cS 6 1, 3), (cS 6 2, 1), (cS 6 3, 1), (cR 4, 2), (cC 3, 2)]), .leaf (16, [(cS 0 4, 6), (cS 1 0, 5), (cS 1 1, 3), (cS 1 5, 1), (cS 2 2, 5), (cS 3 0, 6), (cS 3 1, 5), (cS 3 2, 5), (cS 3 6, 2), (cS 4 1, 1), (cS 5 4, 6), (cS 6 4, 1), (cS 6 5, 3), (cR 1, 3), (cC 1, 5), (cC 5, 6), (cC 6, 8)], [(cS 0 2, 5), (cS 0 3, 2), (cS 1 3, 3), (cS 1 4, 5), (cS 2 4, 2), (cS 3 4, 8), (cS 3 5, 6), (cS 4 2, 5), (cS 4 4, 2), (cS 5 0, 5), (cS 5 1, 3), (cS 5 2, 6), (cS 5 6, 1), (cS 6 0, 8), (cS 6 1, 3), (cS 6 2, 3), (cS 6 3, 1), (cR 5, 2), (cC 3, 6)]), .leaf (12, [(cS 0 1, 2), (cS 0 4, 4), (cS 0 5, 2), (cS 1 0, 3), (cS 1 1, 6), (cS 1 5, 3), (cS 2 2, 6), (cS 3 1, 9), (cS 3 2, 3), (cS 3 6, 3), (cS 5 4, 5), (cS 6 4, 1), (cS 6 5, 3), (cC 0, 3), (cC 5, 3), (cC 6, 6)], [(cS 0 2, 4), (cS 0 3, 2), (cS 1 3, 3), (cS 1 4, 4), (cS 2 4, 2), (cS 3 4, 7), (cS 4 2, 3), (cS 5 0, 8), (cS 5 2, 5), (cS 6 0, 3), (cS 6 1, 4), (cS 6 2, 2), (cS 6 3, 2), (cR 4, 3), (cR 5, 1), (cC 3, 3)]), .leaf (2, [(cS 0 4, 1), (cS 1 0, 1), (cS 2 2, 1), (cS 3 0, 1), (cS 4 2, 1), (cS 5 4, 1), (cC 1, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 1 4, 1), (cS 3 4, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 0, 1), (cC 3, 1)]), .leaf (20, [(cS 0 4, 6), (cS 1 0, 7), (cS 1 1, 5), (cS 1 5, 7), (cS 1 6, 1), (cS 2 1, 4), (cS 2 2, 5), (cS 3 0, 2), (cS 3 1, 7), (cS 3 2, 7), (cS 3 6, 7), (cS 4 0, 3), (cS 4 1, 1), (cS 6 4, 7), (cS 6 5, 9), (cR 1, 3), (cR 3, 2), (cC 0, 2), (cC 1, 3), (cC 5, 4), (cC 6, 7)], [(cS 0 2, 9), (cS 1 3, 8), (cS 2 3, 3), (cS 2 4, 6), (cS 3 4, 8), (cS 4 2, 8), (cS 4 4, 9), (cS 4 5, 3), (cS 5 1, 3), (cS 5 2, 1), (cS 6 0, 12), (cS 6 1, 4), (cS 6 2, 4), (cS 6 3, 4), (cR 5, 8), (cC 3, 3)])],
  .root (8, [(cS 1 1, 3), (cS 2 2, 2), (cS 2 3, 6), (cS 2 4, 2), (cS 4 0, 2), (cS 4 2, 3), (cS 5 0, 1), (cS 5 2, 1), (cS 6 0, 3), (cS 6 5, 4), (cR 0, 4), (cR 5, 4), (cC 0, 1)], [(cS 0 2, 1), (cS 0 3, 4), (cS 1 5, 4), (cS 1 6, 4), (cS 2 0, 1), (cS 2 1, 3), (cS 2 5, 2), (cS 2 6, 2), (cS 3 0, 1), (cS 3 2, 1), (cS 4 4, 4), (cS 4 6, 4), (cS 5 4, 4), (cS 6 2, 3), (cR 3, 4)]),
  .root (24, [(cS 0 0, 12), (cS 0 1, 4), (cS 0 5, 4), (cS 1 1, 8), (cS 2 2, 5), (cS 2 3, 19), (cS 4 4, 18), (cS 5 5, 4), (cS 5 6, 12), (cS 6 0, 4), (cS 6 1, 4), (cS 6 4, 2), (cS 6 5, 12), (cS 6 6, 8), (cC 4, 6)], [(cS 0 2, 2), (cS 0 3, 16), (cS 1 5, 11), (cS 1 6, 10), (cS 2 0, 7), (cS 2 5, 4), (cS 2 6, 4), (cS 3 2, 4), (cS 3 5, 3), (cS 3 6, 2), (cS 4 0, 4), (cS 4 2, 2), (cS 4 6, 4), (cS 5 1, 10), (cS 5 3, 16), (cS 6 2, 5), (cR 1, 3), (cR 3, 11), (cR 4, 4), (cC 1, 6), (cC 2, 3)]),
  .root (6, [(cS 0 0, 3), (cS 0 1, 2), (cS 1 0, 1), (cS 2 2, 2), (cS 2 3, 2), (cS 4 2, 4), (cS 4 4, 2), (cS 4 5, 2), (cS 5 2, 2), (cS 6 4, 2), (cS 6 5, 2), (cC 3, 2), (cC 4, 2)], [(cS 0 2, 2), (cS 0 3, 2), (cS 0 5, 2), (cS 1 2, 2), (cS 1 5, 2), (cS 2 0, 2), (cS 2 1, 2), (cS 2 5, 2), (cS 3 0, 1), (cS 3 1, 4), (cS 3 5, 2), (cS 4 6, 2), (cS 5 0, 1), (cS 5 1, 4), (cS 5 6, 2), (cS 6 2, 2), (cC 0, 1), (cC 6, 2)]),
  .root (2, [(cS 0 0, 1), (cS 0 1, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 4 6, 1), (cS 5 0, 2), (cS 6 4, 1), (cS 6 5, 1), (cC 6, 1)], [(cS 0 3, 1), (cS 1 5, 1), (cS 2 1, 1), (cS 5 2, 1), (cS 5 4, 1), (cS 6 2, 1), (cR 1, 1), (cR 3, 1), (cR 4, 1)]),
  .root (4, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 4, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 2 3, 1), (cS 2 4, 2), (cS 3 3, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 4 2, 2), (cS 4 6, 2), (cS 5 2, 1), (cS 6 4, 2), (cS 6 5, 1), (cR 5, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 0 5, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 2 6, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 4 4, 3), (cS 5 0, 1), (cS 6 0, 1), (cS 6 2, 1), (cS 6 6, 1), (cA, 1)]),
  .root (2, [(cS 0 1, 1), (cS 1 1, 1), (cS 2 4, 1), (cS 3 6, 1), (cS 4 4, 1), (cS 4 6, 1), (cS 6 5, 1), (cC 4, 1)], [(cS 1 5, 1), (cS 3 1, 1), (cS 5 1, 1), (cC 0, 1), (cC 2, 1), (cC 3, 1), (cC 6, 1)]),
  .root (8, [(cS 0 6, 1), (cS 1 1, 3), (cS 1 3, 3), (cS 2 1, 2), (cS 2 2, 1), (cS 2 3, 3), (cS 2 4, 1), (cS 3 1, 3), (cS 3 3, 3), (cS 5 0, 3), (cS 5 5, 3), (cS 5 6, 1), (cS 6 0, 3), (cS 6 4, 1), (cS 6 5, 4), (cR 0, 3), (cR 2, 1), (cC 0, 1), (cC 1, 1)], [(cS 0 2, 1), (cS 0 3, 2), (cS 1 5, 5), (cS 1 6, 3), (cS 2 5, 1), (cS 2 6, 3), (cS 3 0, 1), (cS 3 4, 5), (cS 3 6, 4), (cS 4 2, 2), (cS 4 3, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 1, 1), (cS 5 2, 3), (cS 5 4, 5), (cS 6 2, 4), (cS 6 3, 2), (cR 4, 2)]),
  .root (30, [(cS 0 1, 1), (cS 1 0, 1), (cS 1 1, 8), (cS 2 2, 13), (cS 2 3, 5), (cS 2 4, 7), (cS 3 1, 9), (cS 3 3, 4), (cS 4 0, 4), (cS 4 2, 21), (cS 5 2, 4), (cS 6 4, 9), (cS 6 5, 15), (cR 1, 3), (cR 2, 4), (cC 0, 12), (cC 1, 5), (cC 3, 5), (cC 4, 6)], [(cS 0 2, 6), (cS 0 3, 8), (cS 1 5, 14), (cS 2 5, 4), (cS 2 6, 4), (cS 3 4, 10), (cS 3 6, 18), (cS 4 4, 20), (cS 4 6, 4), (cS 5 6, 7), (cS 6 0, 4), (cS 6 2, 10), (cR 0, 8), (cR 5, 11), (cC 6, 8)]),
  .root (5, [(cS 0 0, 3), (cS 0 1, 1), (cS 1 1, 1), (cS 1 2, 2), (cS 2 0, 2), (cS 2 1, 2), (cS 2 3, 3), (cS 3 1, 1), (cS 3 2, 2), (cS 4 4, 3), (cS 6 4, 2), (cS 6 5, 1), (cC 4, 2)], [(cS 0 2, 2), (cS 0 3, 2), (cS 1 6, 1), (cS 2 6, 1), (cS 3 0, 3), (cS 4 1, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 6, 1), (cS 5 0, 3), (cS 5 1, 1), (cS 5 2, 2), (cS 6 0, 1), (cS 6 2, 2), (cC 3, 1), (cC 5, 3), (cC 6, 1)]),
  .root (30, [(cS 0 1, 14), (cS 1 0, 12), (cS 1 1, 4), (cS 1 2, 10), (cS 1 3, 13), (cS 2 1, 14), (cS 2 3, 15), (cS 3 0, 10), (cS 3 1, 3), (cS 3 5, 10), (cS 4 0, 4), (cS 4 6, 2), (cS 6 4, 14), (cS 6 5, 16), (cS 6 6, 10), (cR 2, 2), (cR 3, 13), (cC 6, 5)], [(cS 0 2, 2), (cS 0 3, 5), (cS 1 4, 12), (cS 1 5, 18), (cS 1 6, 13), (cS 3 4, 5), (cS 4 2, 11), (cS 4 3, 15), (cS 4 4, 6), (cS 4 5, 15), (cS 5 0, 10), (cS 5 1, 11), (cS 6 0, 15), (cS 6 1, 1), (cS 6 2, 13), (cS 6 3, 12), (cR 4, 4), (cR 5, 5)]),
  .root (30, [(cS 0 1, 4), (cS 0 4, 12), (cS 1 0, 14), (cS 1 6, 12), (cS 2 2, 14), (cS 2 3, 16), (cS 2 4, 14), (cS 2 5, 10), (cS 5 0, 12), (cS 5 4, 8), (cS 5 5, 4), (cS 5 6, 4), (cS 6 0, 18), (cS 6 5, 12), (cS 6 6, 4), (cR 0, 8), (cR 1, 4), (cC 5, 6)], [(cS 0 2, 12), (cS 0 3, 6), (cS 2 1, 10), (cS 2 6, 10), (cS 3 6, 2), (cS 4 3, 2), (cS 4 5, 2), (cS 5 1, 2), (cS 5 2, 14), (cS 5 4, 14), (cS 6 2, 8), (cS 6 3, 4), (cR 3, 18), (cR 4, 10), (cR 5, 4), (cC 1, 2)]),
  .root (2, [(cS 0 0, 1), (cS 0 4, 1), (cS 0 5, 1), (cS 1 0, 1), (cS 1 6, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 2 5, 1), (cS 5 1, 1), (cS 5 3, 1), (cS 5 4, 1), (cS 6 5, 1), (cC 2, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 4 4, 1), (cS 5 6, 1), (cS 6 0, 1), (cR 4, 1)]),
  .root (4, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 0, 2), (cS 1 6, 2), (cS 2 2, 2), (cS 2 3, 2), (cS 2 5, 2), (cS 4 4, 2), (cS 6 5, 2), (cR 0, 1), (cC 4, 2)], [(cS 0 2, 1), (cS 0 3, 1), (cS 2 6, 2), (cS 4 5, 2), (cR 3, 2), (cR 5, 2), (cC 0, 2), (cC 2, 2)]),
  .root (2, [(cS 0 0, 1), (cS 1 0, 1), (cS 1 5, 1), (cS 2 4, 1), (cS 3 6, 1), (cS 6 5, 1), (cC 4, 1), (cC 6, 1)], [(cS 3 1, 1), (cS 4 4, 2), (cS 5 0, 1), (cS 5 6, 1), (cC 1, 1), (cC 2, 1), (cC 3, 1)]),
  .root (2, [(cS 5 5, 1), (cS 6 5, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)], [(cS 2 6, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 6 0, 1), (cS 6 2, 1), (cS 6 3, 1), (cR 4, 1), (cR 5, 1)])
]
private def p5Certs1 : List P5Cert := [
  .splitS0 [.leaf (1, [(cR 3, 1), (cR 5, 1)], [(cR 0, 1), (cR 2, 1)]), .leaf (1, [(cR 3, 1), (cR 5, 1)], [(cR 0, 1), (cR 2, 1)]), .leaf (1, [(cR 3, 1), (cR 5, 1)], [(cR 1, 1), (cR 6, 1)]), .leaf (1, [(cR 3, 1), (cR 5, 1)], [(cR 1, 1), (cR 6, 1)])],
  .root (6, [(cS 0 6, 1), (cS 1 4, 3), (cS 2 4, 1), (cS 2 5, 1), (cS 3 3, 2), (cS 3 4, 1), (cS 4 2, 2), (cS 4 3, 1), (cS 4 4, 1), (cS 5 0, 2), (cS 5 1, 2), (cS 5 3, 2), (cS 6 0, 1), (cR 4, 1), (cR 5, 1), (cC 5, 3), (cC 6, 2)], [(cS 0 0, 2), (cS 0 1, 3), (cS 0 3, 3), (cS 1 0, 4), (cS 1 2, 2), (cS 2 0, 2), (cS 2 2, 3), (cS 2 3, 2), (cS 3 0, 3), (cS 3 1, 2), (cS 6 2, 2), (cS 6 4, 6), (cC 2, 1)]),
  .root (8, [(cS 1 4, 2), (cS 1 5, 4), (cS 2 4, 3), (cS 3 0, 2), (cS 3 1, 3), (cS 3 5, 2), (cS 3 6, 1), (cS 4 2, 4), (cS 5 1, 6), (cS 5 6, 4), (cS 6 1, 2), (cR 3, 1), (cC 0, 2), (cC 5, 2), (cC 6, 2)], [(cS 0 1, 1), (cS 0 6, 1), (cS 1 0, 4), (cS 1 1, 2), (cS 1 2, 2), (cS 2 2, 4), (cS 3 3, 1), (cS 4 3, 1), (cS 4 4, 3), (cS 5 4, 3), (cS 6 2, 4), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 4), (cR 0, 3), (cC 3, 3)]),
  .root (8, [(cS 1 4, 2), (cS 1 5, 6), (cS 1 6, 2), (cS 2 0, 3), (cS 3 1, 1), (cS 4 1, 3), (cS 4 3, 4), (cS 5 1, 1), (cS 6 1, 3), (cS 6 6, 4), (cR 3, 4), (cR 5, 4)], [(cS 0 0, 1), (cS 1 0, 3), (cS 1 1, 2), (cS 1 2, 2), (cS 1 3, 2), (cS 2 2, 4), (cS 2 3, 4), (cS 3 5, 4), (cS 3 6, 1), (cS 4 6, 4), (cS 5 4, 4), (cS 6 2, 4), (cS 6 4, 4), (cR 0, 4)]),
  .root (4, [(cS 2 0, 1), (cS 3 0, 2), (cS 3 1, 1), (cS 4 3, 2), (cS 5 0, 2), (cC 4, 2), (cC 5, 2), (cC 6, 2)], [(cS 0 0, 3), (cS 1 0, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 3 3, 1), (cS 5 1, 1), (cS 6 2, 1), (cS 6 4, 3), (cS 6 5, 1), (cC 1, 1), (cC 2, 2), (cC 3, 1)]),
  .root (2, [(cS 0 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 5, 1), (cS 3 0, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1)], [(cS 0 0, 1), (cS 0 2, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 6, 1)]),
  .root (24, [(cS 2 2, 5), (cS 2 3, 19), (cS 2 4, 5), (cS 3 4, 2), (cS 3 5, 11), (cS 3 6, 7), (cS 4 2, 4), (cS 4 3, 8), (cS 4 4, 2), (cS 5 0, 7), (cS 5 1, 6), (cS 5 5, 8), (cS 5 6, 3), (cS 6 0, 3), (cS 6 6, 5), (cR 3, 6), (cR 4, 6), (cR 5, 8)], [(cS 0 0, 2), (cS 0 1, 5), (cS 0 2, 5), (cS 0 3, 2), (cS 1 4, 5), (cS 1 5, 2), (cS 1 6, 5), (cS 2 0, 5), (cS 2 1, 5), (cS 2 5, 3), (cS 3 0, 6), (cS 3 1, 8), (cS 5 4, 1), (cS 6 3, 6), (cS 6 4, 6), (cS 6 5, 6), (cR 0, 3), (cR 1, 14), (cR 6, 11)]),
  .root (60, [(cS 1 2, 23), (cS 1 3, 7), (cS 2 1, 25), (cS 2 3, 45), (cS 3 0, 8), (cS 3 1, 17), (cS 3 5, 8), (cS 3 6, 36), (cS 4 0, 11), (cS 4 1, 4), (cS 4 2, 19), (cS 5 0, 9), (cS 5 1, 25), (cS 5 5, 20), (cS 5 6, 32), (cS 6 0, 22), (cS 6 6, 8), (cR 2, 8), (cR 3, 8), (cR 4, 8), (cC 1, 4)], [(cS 0 0, 4), (cS 0 1, 22), (cS 0 5, 5), (cS 0 6, 18), (cS 1 0, 22), (cS 1 5, 11), (cS 1 6, 14), (cS 2 4, 6), (cS 2 5, 18), (cS 2 6, 13), (cS 3 4, 4), (cS 4 3, 7), (cS 5 3, 8), (cS 6 2, 31), (cS 6 3, 3), (cS 6 5, 29), (cR 0, 8), (cR 1, 4), (cC 3, 18), (cC 4, 32)]),
  .root (6, [(cS 2 1, 3), (cS 2 3, 6), (cS 3 0, 1), (cS 4 2, 1), (cS 4 3, 3), (cS 4 4, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 5 6, 3), (cS 6 0, 2), (cS 6 6, 2), (cR 4, 2), (cC 1, 3)], [(cS 2 4, 3), (cS 2 6, 2), (cS 3 5, 3), (cS 3 6, 3), (cS 5 4, 2), (cS 6 2, 4), (cS 6 3, 2), (cS 6 4, 2), (cS 6 5, 2), (cR 0, 2), (cR 1, 4)]),
  .root (6, [(cS 2 1, 2), (cS 2 2, 2), (cS 2 3, 2), (cS 2 4, 2), (cS 3 0, 2), (cS 3 5, 2), (cS 3 6, 2), (cS 4 3, 2), (cS 4 4, 2), (cS 5 0, 2), (cS 5 5, 2), (cS 5 6, 2), (cS 6 6, 2), (cR 2, 2), (cR 4, 2)], [(cS 0 0, 1), (cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 4 1, 2), (cS 4 2, 2), (cS 5 2, 2), (cS 6 4, 2), (cR 1, 4), (cR 6, 4)]),
  .root (1, [(cR 2, 1), (cR 4, 1)], [(cR 1, 1), (cR 6, 1)]),
  .root (4, [(cS 0 3, 1), (cS 1 2, 1), (cS 1 4, 2), (cS 2 2, 2), (cS 2 3, 1), (cS 2 4, 2), (cS 4 0, 1), (cS 4 2, 1), (cS 5 1, 2), (cS 6 0, 1), (cR 1, 1), (cR 3, 1), (cR 5, 1), (cC 5, 1), (cC 6, 2)], [(cS 0 0, 2), (cS 0 1, 1), (cS 0 2, 1), (cS 1 0, 2), (cS 2 0, 2), (cS 3 1, 2), (cS 4 3, 2), (cS 4 4, 2), (cS 6 2, 2), (cS 6 3, 1), (cS 6 4, 3), (cS 6 5, 1)]),
  .root (16, [(cS 0 6, 2), (cS 1 3, 14), (cS 1 5, 10), (cS 2 2, 8), (cS 2 5, 2), (cS 3 3, 8), (cS 3 4, 6), (cS 4 1, 5), (cS 4 2, 3), (cS 4 3, 5), (cS 4 4, 1), (cS 5 0, 3), (cS 6 0, 1), (cS 6 1, 4), (cS 6 6, 4), (cR 5, 8), (cC 4, 2), (cC 5, 4)], [(cS 0 0, 5), (cS 0 2, 8), (cS 1 0, 11), (cS 1 2, 8), (cS 2 0, 5), (cS 3 0, 3), (cS 3 1, 8), (cS 3 5, 2), (cS 3 6, 8), (cS 4 5, 1), (cS 4 6, 5), (cS 6 1, 2), (cS 6 2, 2), (cS 6 3, 2), (cS 6 4, 10), (cS 6 5, 2), (cR 6, 4)]),
  .root (20, [(cS 1 3, 8), (cS 1 5, 5), (cS 2 2, 9), (cS 3 3, 8), (cS 3 5, 5), (cS 4 0, 2), (cS 4 3, 3), (cS 4 4, 5), (cS 5 0, 3), (cS 5 6, 6), (cS 6 0, 2), (cC 3, 3), (cC 4, 9), (cC 5, 6), (cC 6, 9)], [(cS 0 0, 3), (cS 0 2, 8), (cS 1 0, 8), (cS 1 2, 6), (cS 2 0, 3), (cS 3 1, 8), (cS 4 1, 6), (cS 5 2, 8), (cS 6 4, 14), (cR 6, 6), (cC 0, 9), (cC 2, 6)]),
  .root (2, [(cS 1 3, 1), (cS 1 4, 1), (cS 1 5, 2), (cS 2 3, 1), (cS 2 5, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1)], [(cS 0 0, 1), (cS 0 2, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 6, 1)]),
  .root (30, [(cS 0 3, 9), (cS 0 4, 7), (cS 0 5, 4), (cS 1 5, 5), (cS 1 6, 7), (cS 2 2, 6), (cS 2 3, 7), (cS 2 4, 6), (cS 2 5, 2), (cS 3 0, 6), (cS 4 1, 3), (cS 4 2, 6), (cS 5 0, 16), (cS 5 1, 7), (cS 5 2, 7), (cS 5 6, 11), (cS 6 5, 13), (cS 6 6, 7), (cR 1, 14), (cR 2, 3), (cR 3, 14), (cC 1, 7)], [(cS 0 0, 20), (cS 0 1, 3), (cS 0 2, 7), (cS 0 6, 3), (cS 1 0, 7), (cS 3 5, 5), (cS 3 6, 7), (cS 4 3, 17), (cS 4 4, 13), (cS 4 5, 17), (cS 4 6, 3), (cS 6 2, 20), (cS 6 3, 3), (cS 6 4, 27), (cS 6 5, 3)]),
  .root (5, [(cS 0 3, 1), (cS 1 4, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 4, 1), (cS 5 0, 3), (cS 5 5, 2), (cS 5 6, 1), (cR 1, 3), (cR 3, 3), (cC 5, 1), (cC 6, 1)], [(cS 0 0, 3), (cS 0 1, 1), (cS 0 2, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 4 1, 1), (cS 4 2, 2), (cS 4 3, 3), (cS 4 4, 2), (cS 5 1, 1), (cS 5 2, 1), (cS 6 2, 2), (cS 6 3, 1), (cS 6 4, 3), (cS 6 5, 1), (cR 6, 1)]),
  .root (5, [(cS 0 4, 2), (cS 1 3, 1), (cS 1 5, 1), (cS 1 6, 2), (cS 2 1, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 5 0, 1), (cS 5 1, 2), (cS 5 2, 1), (cR 1, 2), (cR 2, 1), (cR 3, 3), (cR 4, 1)], [(cS 0 0, 2), (cS 0 1, 1), (cS 0 2, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 4 3, 2), (cS 4 4, 3), (cS 5 3, 1), (cS 5 5, 1), (cS 5 6, 3), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 0, 1), (cR 6, 2)]),
  .root (6, [(cS 1 3, 3), (cS 1 5, 3), (cS 1 6, 3), (cS 2 1, 3), (cS 2 2, 3), (cS 2 4, 1), (cS 3 1, 2), (cS 3 2, 1), (cS 3 3, 1), (cS 4 3, 3), (cS 5 0, 1), (cS 5 5, 1), (cS 5 6, 3), (cS 6 6, 2), (cR 3, 1), (cC 4, 3)], [(cS 0 0, 2), (cS 0 2, 5), (cS 1 0, 2), (cS 3 5, 1), (cS 3 6, 4), (cS 4 1, 2), (cS 4 5, 1), (cS 5 1, 1), (cS 5 2, 2), (cS 6 3, 1), (cS 6 4, 2), (cS 6 5, 1), (cR 0, 1), (cR 5, 1), (cR 6, 2), (cC 0, 1)]),
  .root (3, [(cS 1 5, 1), (cS 1 6, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 3 0, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 5 1, 2), (cS 5 3, 1), (cR 1, 1), (cR 3, 1), (cC 3, 1), (cC 4, 1)], [(cS 0 2, 1), (cS 1 0, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 6, 1), (cS 5 4, 2), (cS 5 6, 2), (cR 0, 2), (cR 6, 1)]),
  .root (5, [(cS 0 3, 3), (cS 1 3, 1), (cS 1 4, 1), (cS 1 5, 4), (cS 1 6, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 4 3, 1), (cS 5 3, 1), (cS 5 5, 2), (cR 2, 3), (cR 3, 1), (cR 4, 3)], [(cS 0 0, 4), (cS 0 2, 5), (cS 1 0, 1), (cS 4 1, 1), (cS 5 0, 2), (cS 5 1, 2), (cS 5 2, 2), (cS 6 3, 2), (cS 6 4, 2), (cS 6 5, 2), (cS 6 6, 2), (cR 6, 1)]),
  .splitS0 [.leaf (24, [(cS 0 1, 13), (cS 0 6, 16), (cS 1 0, 5), (cS 1 1, 3), (cS 2 5, 7), (cS 2 6, 1), (cS 3 3, 2), (cS 3 4, 5), (cS 3 5, 3), (cS 3 6, 4), (cS 4 2, 2), (cS 4 3, 3), (cS 5 5, 2), (cS 6 1, 8), (cS 6 6, 8), (cR 3, 9), (cR 4, 8), (cR 5, 14), (cC 0, 3)], [(cS 0 2, 6), (cS 0 3, 7), (cS 1 2, 2), (cS 1 3, 9), (cS 1 4, 8), (cS 1 5, 16), (cS 1 6, 8), (cS 2 0, 7), (cS 2 1, 12), (cS 2 2, 7), (cS 2 3, 8), (cS 3 1, 5), (cS 6 2, 11), (cS 6 4, 24)]), .leaf (4, [(cS 0 1, 2), (cS 0 6, 3), (cS 1 1, 1), (cS 2 5, 1), (cS 3 4, 1), (cS 3 5, 2), (cS 3 6, 1), (cS 4 2, 1), (cS 4 3, 2), (cS 5 5, 1), (cR 4, 1), (cR 5, 2), (cR 6, 1), (cC 0, 1)], [(cS 0 3, 3), (cS 0 4, 1), (cS 0 5, 2), (cS 1 2, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 2, 1), (cS 6 2, 1), (cS 6 4, 1), (cR 2, 2)]), .leaf (1, [(cS 0 0, 1), (cS 0 6, 1), (cR 3, 1), (cR 5, 1)], [(cS 0 2, 1), (cS 0 4, 1), (cR 2, 1)]), .leaf (5, [(cS 0 0, 3), (cS 0 6, 1), (cS 1 0, 1), (cS 2 5, 1), (cS 3 3, 2), (cS 3 4, 2), (cS 3 6, 1), (cS 4 2, 2), (cS 4 4, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 3, 2), (cS 6 1, 1), (cS 6 6, 1), (cR 4, 1), (cR 5, 1), (cC 0, 1), (cC 5, 2), (cC 6, 1)], [(cS 0 2, 3), (cS 1 2, 1), (cS 1 4, 4), (cS 2 0, 1), (cS 2 1, 1), (cS 2 2, 2), (cS 2 3, 1), (cS 3 0, 1), (cS 3 1, 2), (cS 6 2, 2), (cS 6 4, 5), (cR 1, 1)])],
  .splitS0 [.leaf (1, [(cC 1, 1), (cC 6, 1)], [(cC 3, 1), (cC 5, 1)]), .leaf (1, [(cC 1, 1), (cC 6, 1)], [(cC 2, 1), (cC 4, 1)]), .leaf (1, [(cC 1, 1), (cC 6, 1)], [(cC 3, 1), (cC 5, 1)]), .leaf (1, [(cC 1, 1), (cC 6, 1)], [(cC 2, 1), (cC 4, 1)])],
  .splitS0 [.leaf (20, [(cS 0 1, 2), (cS 0 6, 2), (cS 1 0, 3), (cS 2 0, 2), (cS 2 2, 2), (cS 3 1, 3), (cS 3 3, 9), (cS 4 3, 8), (cS 5 3, 6), (cS 6 1, 3), (cS 6 6, 3), (cR 4, 3), (cR 5, 3), (cC 1, 15), (cC 6, 15)], [(cS 0 3, 8), (cS 1 2, 3), (cS 1 3, 9), (cS 1 5, 5), (cS 1 6, 3), (cS 2 3, 9), (cS 3 5, 5), (cS 3 6, 3), (cS 6 3, 12), (cS 6 4, 5), (cC 4, 3), (cC 5, 12)]), .leaf (1, [(cS 3 3, 1), (cS 5 3, 1), (cC 1, 1), (cC 6, 1)], [(cS 0 3, 1), (cS 2 3, 1), (cC 5, 1)]), .leaf (8, [(cS 0 0, 2), (cS 0 5, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 1 6, 2), (cS 2 0, 2), (cS 3 1, 2), (cS 4 2, 1), (cS 4 3, 5), (cS 4 4, 1), (cS 5 5, 1), (cS 5 6, 1), (cS 6 5, 2), (cR 4, 2), (cR 5, 2), (cR 6, 2), (cC 0, 1), (cC 1, 3), (cC 6, 2)], [(cS 0 2, 7), (cS 0 4, 7), (cS 1 2, 1), (cS 1 4, 1), (cS 1 5, 2), (cS 2 2, 3), (cS 2 3, 5), (cS 2 4, 3), (cS 2 5, 2), (cS 3 5, 3), (cS 3 6, 3), (cS 4 5, 2), (cS 6 2, 1), (cS 6 3, 3), (cS 6 4, 1)]), .leaf (5, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 0, 1), (cS 2 0, 1), (cS 3 1, 1), (cS 3 3, 3), (cS 4 3, 1), (cS 5 3, 2), (cS 6 0, 1), (cS 6 5, 1), (cR 4, 1), (cR 5, 1), (cC 1, 3), (cC 6, 3)], [(cS 0 2, 3), (cS 0 4, 1), (cS 1 2, 2), (cS 1 3, 1), (cS 1 4, 2), (cS 1 5, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 2 5, 1), (cS 3 5, 3), (cS 3 6, 1), (cS 4 5, 1), (cS 5 4, 1), (cS 6 2, 2), (cS 6 4, 3), (cC 4, 1)])],
  .splitS0 [.leaf (2, [(cS 2 4, 1), (cS 4 3, 1), (cS 4 4, 1), (cC 0, 1), (cC 1, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 3, 1), (cS 1 3, 1), (cS 1 5, 2), (cS 2 3, 1), (cS 5 2, 1), (cS 6 4, 2), (cC 2, 1)]), .leaf (4, [(cS 0 1, 1), (cS 2 1, 1), (cS 3 4, 2), (cS 4 3, 1), (cS 4 4, 1), (cS 5 3, 1), (cS 5 4, 1), (cC 0, 2), (cC 1, 1), (cC 5, 2), (cC 6, 2)], [(cS 0 3, 1), (cS 0 4, 2), (cS 1 3, 1), (cS 1 5, 4), (cS 2 3, 1), (cS 2 4, 2), (cS 3 3, 1), (cS 4 1, 1), (cS 5 1, 1), (cS 6 2, 1), (cS 6 4, 2), (cC 2, 2)]), .leaf (4, [(cS 0 0, 1), (cS 2 1, 1), (cS 3 4, 2), (cS 4 3, 1), (cS 4 4, 1), (cS 5 3, 1), (cS 5 4, 1), (cC 0, 2), (cC 1, 1), (cC 5, 2), (cC 6, 2)], [(cS 0 2, 1), (cS 0 4, 2), (cS 1 2, 1), (cS 1 4, 2), (cS 2 3, 1), (cS 2 4, 2), (cS 3 3, 1), (cS 4 1, 1), (cS 5 1, 1), (cS 6 2, 1), (cS 6 4, 2), (cC 2, 2)]), .leaf (2, [(cS 2 4, 1), (cS 4 3, 1), (cS 4 4, 1), (cC 0, 1), (cC 1, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 1 4, 2), (cS 2 3, 1), (cS 5 2, 1), (cS 6 4, 2), (cC 2, 1)])],
  .root (2, [(cS 1 0, 2), (cS 2 5, 1), (cS 3 0, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 1 5, 1), (cS 2 1, 1), (cS 2 3, 2), (cS 6 4, 1), (cS 6 6, 1), (cR 1, 1), (cR 6, 1)]),
  .root (6, [(cS 0 0, 2), (cS 0 5, 2), (cS 1 0, 2), (cS 1 5, 2), (cS 2 5, 2), (cS 3 5, 2), (cS 4 1, 2), (cS 4 6, 2), (cS 5 1, 2), (cS 5 2, 2), (cS 5 6, 2), (cS 6 1, 2), (cS 6 6, 2), (cC 0, 2), (cC 5, 2)], [(cS 0 2, 2), (cS 0 4, 1), (cS 1 3, 1), (cS 2 0, 2), (cS 2 1, 2), (cS 2 3, 1), (cS 3 0, 2), (cS 3 3, 1), (cS 4 3, 1), (cS 5 4, 1), (cS 6 4, 1), (cC 2, 4), (cC 4, 4)]),
  .root (3, [(cS 0 0, 2), (cS 1 0, 1), (cS 1 5, 2), (cS 4 1, 1), (cS 4 3, 3), (cS 5 0, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 0, 1), (cS 6 5, 1), (cS 6 6, 1), (cC 5, 1)], [(cS 0 2, 1), (cS 0 4, 1), (cS 1 1, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 2 0, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 2 6, 1), (cS 3 1, 1), (cS 4 6, 2), (cS 5 4, 1), (cS 6 2, 2), (cS 6 4, 1), (cR 3, 1), (cC 4, 1)]),
  .root (8, [(cS 0 0, 3), (cS 0 5, 2), (cS 1 0, 1), (cS 1 5, 2), (cS 2 5, 2), (cS 3 5, 2), (cS 4 3, 4), (cS 4 4, 4), (cS 4 6, 2), (cS 5 6, 2), (cS 6 0, 1), (cS 6 6, 2), (cC 0, 4), (cC 5, 4)], [(cS 0 3, 3), (cS 1 1, 3), (cS 1 3, 3), (cS 2 0, 1), (cS 2 3, 3), (cS 2 6, 2), (cS 3 0, 1), (cS 3 1, 3), (cS 3 3, 3), (cS 4 0, 1), (cS 5 2, 3), (cS 6 2, 3), (cS 6 4, 6), (cC 1, 3), (cC 2, 2), (cC 4, 2)]),
  .splitS0 [.leaf (2, [(cS 0 0, 1), (cS 0 5, 1), (cS 2 5, 1), (cS 3 3, 1), (cS 3 4, 1), (cS 3 6, 1), (cR 1, 1), (cR 4, 1), (cR 5, 1)], [(cS 0 2, 1), (cS 1 3, 2), (cS 2 0, 1), (cS 2 2, 1), (cS 3 1, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 6, 1)]), .leaf (6, [(cS 0 0, 2), (cS 1 0, 1), (cS 1 5, 3), (cS 2 4, 2), (cS 2 5, 1), (cS 3 3, 3), (cS 3 4, 1), (cS 3 5, 2), (cS 3 6, 3), (cR 0, 1), (cR 1, 2), (cR 4, 3), (cR 5, 3)], [(cS 0 2, 2), (cS 0 3, 1), (cS 1 2, 1), (cS 1 3, 2), (cS 2 0, 3), (cS 2 2, 3), (cS 3 1, 3), (cS 6 4, 3), (cS 6 6, 3), (cR 6, 3)]), .leaf (4, [(cS 0 0, 2), (cS 0 5, 1), (cS 1 0, 1), (cS 1 5, 2), (cS 2 4, 1), (cS 2 5, 1), (cS 3 3, 2), (cS 3 5, 2), (cS 3 6, 1), (cR 1, 1), (cR 4, 2), (cR 5, 2)], [(cS 0 2, 2), (cS 0 4, 2), (cS 1 2, 1), (cS 1 3, 1), (cS 2 0, 2), (cS 2 2, 2), (cS 2 3, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 2, 1), (cS 6 6, 2), (cR 6, 2)]), .leaf (10, [(cS 0 0, 5), (cS 0 5, 1), (cS 1 0, 5), (cS 1 4, 2), (cS 1 5, 6), (cS 1 6, 2), (cS 2 4, 3), (cS 2 5, 1), (cS 3 3, 4), (cS 3 5, 5), (cS 3 6, 3), (cS 4 1, 1), (cS 4 2, 1), (cS 4 3, 2), (cS 4 4, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 4, 1), (cR 4, 3), (cR 5, 4), (cC 5, 1)], [(cS 0 1, 1), (cS 0 2, 4), (cS 0 4, 6), (cS 1 1, 1), (cS 1 2, 3), (cS 1 3, 2), (cS 2 0, 3), (cS 2 1, 1), (cS 2 2, 4), (cS 2 3, 3), (cS 3 0, 4), (cS 3 1, 2), (cS 3 2, 2), (cS 5 6, 2), (cS 6 3, 1), (cS 6 6, 4), (cR 6, 4), (cC 2, 1)]), .leaf (6, [(cS 0 0, 2), (cS 0 6, 2), (cS 1 0, 4), (cS 1 5, 2), (cS 2 4, 1), (cS 2 6, 2), (cS 3 3, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 5 0, 1), (cS 5 1, 2), (cS 5 2, 1), (cR 4, 2), (cC 3, 2), (cC 4, 2), (cC 5, 2)], [(cS 0 1, 1), (cS 0 2, 2), (cS 0 3, 1), (cS 1 1, 1), (cS 1 2, 2), (cS 1 3, 1), (cS 2 1, 1), (cS 2 2, 3), (cS 3 0, 3), (cS 3 1, 2), (cS 5 6, 3), (cS 6 4, 3), (cR 6, 3)]), .leaf (3, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 5, 1), (cS 1 0, 2), (cS 1 5, 2), (cS 2 5, 1), (cR 3, 2), (cR 4, 1), (cR 5, 2)], [(cS 0 2, 2), (cS 0 4, 2), (cS 1 3, 1), (cS 2 1, 2), (cS 2 3, 1), (cS 3 3, 1), (cS 6 6, 2), (cR 2, 1), (cR 6, 1)])],
  .root (24, [(cS 0 0, 6), (cS 0 5, 5), (cS 1 0, 7), (cS 1 5, 19), (cS 2 0, 6), (cS 2 5, 5), (cS 3 1, 7), (cS 4 1, 6), (cS 4 2, 4), (cS 5 0, 1), (cS 5 1, 6), (cS 5 2, 4), (cS 5 6, 5), (cS 6 1, 7), (cS 6 5, 5), (cS 6 6, 7), (cC 0, 4), (cC 1, 7), (cC 6, 7)], [(cS 0 1, 1), (cS 0 2, 6), (cS 0 4, 4), (cS 1 2, 7), (cS 1 4, 3), (cS 2 3, 5), (cS 3 3, 6), (cS 3 5, 5), (cS 3 6, 7), (cS 4 3, 3), (cS 4 5, 5), (cS 4 6, 7), (cS 5 4, 5), (cS 6 2, 7), (cS 6 4, 6), (cC 2, 10), (cC 3, 3), (cC 4, 14)]),
  .root (1, [(cC 0, 1), (cC 5, 1)], [(cC 2, 1), (cC 4, 1)]),
  .root (6, [(cS 0 0, 1), (cS 1 0, 3), (cS 1 5, 6), (cS 2 0, 1), (cS 3 0, 2), (cS 3 1, 1), (cS 3 2, 1), (cS 3 5, 6), (cS 3 6, 1), (cS 4 1, 1), (cS 4 2, 3), (cS 4 5, 2), (cS 4 6, 1), (cS 5 1, 3), (cS 5 2, 1), (cS 6 1, 1), (cS 6 2, 1), (cC 0, 2)], [(cS 0 1, 2), (cS 0 2, 2), (cS 0 5, 1), (cS 1 2, 2), (cS 2 2, 4), (cS 5 6, 3), (cS 6 2, 2), (cS 6 5, 2), (cS 6 6, 3), (cC 3, 2), (cC 4, 4)]),
  .root (5, [(cS 0 0, 2), (cS 1 0, 1), (cS 1 5, 4), (cS 2 0, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 3 1, 1), (cS 4 3, 3), (cS 4 4, 2), (cS 6 0, 1), (cS 6 5, 2), (cS 6 6, 2), (cC 0, 2), (cC 5, 1)], [(cS 0 1, 1), (cS 0 3, 2), (cS 0 4, 2), (cS 1 2, 1), (cS 1 4, 1), (cS 2 3, 2), (cS 2 4, 2), (cS 3 3, 1), (cS 3 5, 2), (cS 3 6, 1), (cS 4 1, 1), (cS 4 6, 2), (cS 5 3, 1), (cS 5 5, 1), (cS 6 2, 1), (cS 6 4, 3), (cR 5, 1), (cC 1, 1), (cC 2, 2)]),
  .root (10, [(cS 0 0, 2), (cS 1 0, 7), (cS 1 5, 10), (cS 2 0, 2), (cS 2 1, 4), (cS 2 5, 2), (cS 3 0, 1), (cS 4 1, 6), (cS 4 2, 2), (cS 4 3, 6), (cS 4 4, 2), (cS 5 1, 3), (cS 5 3, 2), (cR 3, 2), (cC 0, 1)], [(cS 0 1, 1), (cS 0 2, 2), (cS 1 2, 2), (cS 1 3, 1), (cS 2 2, 4), (cS 2 3, 5), (cS 3 4, 1), (cS 3 5, 2), (cS 3 6, 4), (cS 4 6, 4), (cS 5 6, 1), (cS 6 2, 1), (cS 6 5, 1), (cS 6 6, 3), (cR 0, 5), (cR 5, 5), (cR 6, 1), (cC 3, 1), (cC 4, 3)]),
  .splitS0 [.leaf (20, [(cS 0 0, 8), (cS 0 1, 3), (cS 0 5, 8), (cS 1 0, 3), (cS 1 5, 3), (cS 3 0, 2), (cS 3 4, 2), (cS 3 6, 3), (cS 4 3, 8), (cS 4 5, 8), (cR 0, 6), (cR 1, 3), (cR 2, 15), (cR 3, 3), (cR 4, 12)], [(cS 0 2, 5), (cS 1 3, 20), (cS 4 1, 3), (cS 5 0, 8), (cS 5 1, 9), (cS 5 2, 5), (cS 6 3, 9), (cS 6 4, 8), (cS 6 5, 9), (cS 6 6, 9), (cR 6, 3), (cC 2, 3)]), .leaf (5, [(cS 0 1, 1), (cS 1 0, 1), (cS 1 5, 2), (cS 1 6, 1), (cS 2 1, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 4 3, 3), (cS 4 5, 2), (cR 0, 2), (cR 2, 2), (cR 3, 1), (cR 4, 2), (cC 0, 1), (cC 5, 1)], [(cS 0 3, 1), (cS 1 2, 1), (cS 1 3, 2), (cS 2 3, 1), (cS 4 1, 1), (cS 5 0, 2), (cS 5 1, 2), (cS 5 2, 1), (cS 6 3, 2), (cS 6 4, 2), (cS 6 5, 2), (cS 6 6, 2), (cR 6, 1), (cC 2, 1)]), .leaf (24, [(cS 0 0, 2), (cS 0 1, 6), (cS 0 6, 3), (cS 1 0, 10), (cS 1 4, 2), (cS 1 5, 6), (cS 1 6, 3), (cS 2 0, 2), (cS 2 1, 3), (cS 2 4, 2), (cS 3 0, 6), (cS 3 6, 3), (cS 4 3, 14), (cS 4 5, 1), (cS 4 6, 3), (cS 5 3, 7), (cS 5 4, 7), (cR 1, 3), (cR 2, 3), (cR 3, 7), (cR 4, 3), (cC 0, 3), (cC 4, 2), (cC 5, 11)], [(cS 0 3, 8), (cS 0 4, 3), (cS 1 2, 3), (cS 2 2, 5), (cS 2 3, 12), (cS 4 1, 7), (cS 5 0, 9), (cS 5 1, 8), (cS 5 2, 2), (cS 5 6, 6), (cS 6 3, 1), (cS 6 5, 8), (cS 6 6, 3), (cR 0, 6), (cR 6, 7), (cC 2, 7)]), .leaf (16, [(cS 0 0, 7), (cS 0 6, 1), (cS 1 0, 9), (cS 1 4, 4), (cS 1 5, 7), (cS 1 6, 3), (cS 2 0, 4), (cS 2 1, 3), (cS 2 4, 4), (cS 2 5, 1), (cS 3 0, 4), (cS 3 5, 1), (cS 3 6, 4), (cS 4 3, 8), (cS 4 5, 2), (cS 5 3, 5), (cS 5 4, 6), (cR 3, 5), (cR 4, 3), (cC 5, 5)], [(cS 0 1, 4), (cS 0 3, 4), (cS 0 4, 8), (cS 1 2, 5), (cS 2 2, 1), (cS 2 3, 8), (cS 4 1, 4), (cS 5 0, 7), (cS 5 1, 5), (cS 5 6, 6), (cS 6 5, 3), (cS 6 6, 3), (cR 6, 5), (cC 2, 7)]), .leaf (2, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 0, 1), (cS 1 5, 1), (cS 4 2, 1), (cS 5 4, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1)], [(cS 0 2, 1), (cS 0 4, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 5 1, 1), (cR 5, 1), (cR 6, 1)]), .leaf (6, [(cS 0 0, 3), (cS 1 0, 3), (cS 1 5, 4), (cS 2 0, 3), (cS 3 0, 1), (cS 3 5, 2), (cS 4 3, 4), (cS 4 6, 3), (cS 5 3, 2), (cS 5 4, 4), (cR 3, 2), (cC 5, 2)], [(cS 0 3, 3), (cS 0 4, 3), (cS 0 5, 1), (cS 1 2, 2), (cS 2 3, 5), (cS 2 4, 1), (cS 5 0, 2), (cS 5 1, 1), (cS 5 2, 1), (cS 5 6, 1), (cS 6 2, 2), (cS 6 5, 2), (cS 6 6, 3), (cC 1, 3), (cC 2, 1)])],
  .root (2, [(cS 0 0, 1), (cS 1 3, 1), (cS 2 3, 1), (cS 3 2, 1), (cS 3 5, 1), (cS 6 5, 1), (cR 5, 1), (cC 1, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 4 3, 1), (cS 6 2, 1), (cS 6 4, 1), (cC 4, 1)]),
  .splitS0 [.leaf (20, [(cS 0 1, 9), (cS 0 6, 9), (cS 1 0, 11), (cS 2 2, 9), (cS 2 3, 11), (cS 3 3, 9), (cS 6 0, 5), (cS 6 1, 6), (cS 6 5, 5), (cS 6 6, 6), (cR 4, 11), (cR 5, 9)], [(cS 0 2, 1), (cS 0 3, 7), (cS 0 4, 3), (cS 0 5, 11), (cS 1 2, 2), (cS 1 3, 2), (cS 1 5, 1), (cS 2 0, 1), (cS 2 1, 2), (cS 2 5, 11), (cS 3 0, 8), (cS 3 1, 9), (cS 3 5, 9), (cS 3 6, 12), (cS 6 2, 6), (cS 6 3, 6), (cS 6 4, 6), (cR 1, 8)]), .leaf (4, [(cS 0 1, 1), (cS 0 6, 3), (cS 1 0, 1), (cS 1 2, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 2, 1), (cS 3 4, 1), (cS 4 3, 1), (cS 5 6, 2), (cS 6 1, 1), (cS 6 6, 1), (cR 4, 1), (cR 5, 1), (cC 1, 2), (cC 3, 1)], [(cS 0 3, 2), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 0, 2), (cS 3 0, 2), (cS 3 6, 2), (cS 6 3, 2), (cS 6 4, 2), (cC 5, 2)]), .leaf (4, [(cS 0 1, 2), (cS 0 6, 2), (cS 1 0, 2), (cS 1 2, 2), (cS 2 3, 2), (cS 3 2, 1), (cS 3 3, 1), (cS 3 4, 1), (cS 6 0, 1), (cS 6 1, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 4, 2), (cR 5, 2)], [(cS 0 3, 2), (cS 0 4, 1), (cS 0 5, 2), (cS 1 4, 1), (cS 1 6, 2), (cS 2 1, 2), (cS 2 4, 1), (cS 2 5, 2), (cS 3 0, 1), (cS 3 1, 1), (cS 3 5, 1), (cS 3 6, 3), (cS 6 2, 1), (cS 6 3, 1), (cS 6 4, 1)]), .leaf (20, [(cS 0 0, 8), (cS 0 5, 8), (cS 0 6, 1), (cS 1 0, 9), (cS 1 2, 8), (cS 2 2, 2), (cS 2 3, 9), (cS 3 2, 2), (cS 3 3, 8), (cS 3 4, 2), (cS 5 3, 2), (cS 5 6, 1), (cS 6 0, 3), (cS 6 1, 6), (cS 6 5, 3), (cS 6 6, 6), (cR 4, 9), (cR 5, 8), (cC 1, 3), (cC 3, 1), (cC 6, 2)], [(cS 0 2, 11), (cS 0 4, 11), (cS 1 4, 5), (cS 1 5, 1), (cS 1 6, 8), (cS 2 0, 1), (cS 2 1, 7), (cS 2 4, 2), (cS 2 5, 9), (cS 3 0, 6), (cS 3 1, 6), (cS 3 5, 6), (cS 3 6, 14), (cS 6 2, 9), (cS 6 4, 6), (cC 4, 3)]), .leaf (4, [(cS 0 0, 2), (cS 0 5, 2), (cS 1 0, 1), (cS 1 2, 1), (cS 3 3, 2), (cS 6 1, 2), (cS 6 6, 2), (cR 1, 1), (cR 2, 2), (cR 4, 2), (cR 5, 2)], [(cS 0 2, 2), (cS 1 4, 3), (cS 1 5, 1), (cS 3 0, 2), (cS 3 1, 2), (cS 3 5, 2), (cS 3 6, 2), (cS 6 2, 2), (cS 6 4, 4)]), .leaf (2, [(cS 0 1, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 6 0, 1), (cS 6 5, 1), (cR 4, 1), (cR 5, 1)], [(cS 0 2, 1), (cS 0 4, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 6 2, 1), (cS 6 4, 1), (cR 1, 1)])],
  .splitS0 [.leaf (24, [(cS 0 0, 4), (cS 0 1, 12), (cS 0 6, 12), (cS 1 0, 8), (cS 1 2, 5), (cS 2 3, 7), (cS 3 3, 5), (cS 3 5, 12), (cS 4 3, 7), (cS 4 4, 8), (cS 4 6, 8), (cS 5 0, 7), (cS 5 4, 1), (cS 5 5, 7), (cS 6 1, 8), (cS 6 6, 12), (cR 2, 12), (cR 4, 4), (cR 5, 5)], [(cS 0 3, 11), (cS 0 4, 6), (cS 1 2, 2), (cS 1 3, 7), (cS 1 5, 24), (cS 2 0, 4), (cS 3 0, 12), (cS 3 1, 8), (cS 4 1, 4), (cS 4 2, 3), (cS 5 1, 5), (cS 5 2, 7), (cS 6 2, 8), (cS 6 4, 18), (cC 2, 5)]), .leaf (24, [(cS 0 1, 8), (cS 0 6, 11), (cS 1 1, 10), (cS 1 2, 3), (cS 1 3, 7), (cS 2 2, 7), (cS 2 3, 4), (cS 2 4, 6), (cS 3 3, 11), (cS 3 5, 15), (cS 4 3, 12), (cS 4 4, 12), (cS 4 6, 5), (cS 5 0, 6), (cS 5 5, 12), (cS 6 0, 4), (cS 6 1, 6), (cS 6 5, 3), (cS 6 6, 3), (cR 2, 3), (cC 0, 6), (cC 6, 7)], [(cS 0 3, 11), (cS 1 4, 3), (cS 1 5, 18), (cS 1 6, 3), (cS 2 0, 3), (cS 3 0, 6), (cS 3 1, 15), (cS 4 1, 8), (cS 4 2, 1), (cS 5 1, 4), (cS 5 2, 11), (cS 6 2, 10), (cS 6 3, 3), (cS 6 4, 24), (cR 1, 3)]), .leaf (6, [(cS 0 0, 2), (cS 0 1, 3), (cS 0 6, 3), (cS 1 0, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 2 3, 1), (cS 3 3, 2), (cS 3 5, 3), (cS 4 3, 1), (cS 4 4, 3), (cS 4 6, 3), (cS 5 0, 1), (cS 5 5, 1), (cS 6 1, 1), (cS 6 6, 3), (cR 2, 3), (cR 5, 2)], [(cS 0 3, 2), (cS 0 4, 2), (cS 1 5, 5), (cS 2 0, 1), (cS 3 0, 3), (cS 3 1, 2), (cS 4 1, 1), (cS 4 2, 2), (cS 5 1, 2), (cS 6 2, 3), (cS 6 4, 4), (cR 1, 1), (cC 2, 1)]), .leaf (20, [(cS 0 0, 11), (cS 0 6, 6), (cS 1 0, 6), (cS 1 2, 10), (cS 2 3, 2), (cS 3 3, 10), (cS 3 5, 9), (cS 4 3, 4), (cS 4 4, 8), (cS 4 6, 9), (cS 5 4, 2), (cS 5 5, 1), (cS 6 0, 6), (cS 6 6, 9), (cR 2, 8), (cR 5, 6), (cC 0, 3), (cC 5, 3), (cC 6, 2)], [(cS 0 2, 10), (cS 0 4, 8), (cS 1 4, 12), (cS 1 5, 9), (cS 2 0, 2), (cS 2 1, 2), (cS 3 0, 6), (cS 3 1, 10), (cS 4 1, 5), (cS 4 2, 6), (cS 5 1, 6), (cS 5 2, 4), (cS 6 2, 10), (cS 6 4, 12)]), .leaf (6, [(cS 0 0, 1), (cS 1 1, 2), (cS 1 2, 2), (cS 1 3, 1), (cS 2 2, 2), (cS 2 3, 1), (cS 3 3, 3), (cS 3 4, 2), (cS 3 5, 1), (cS 4 3, 3), (cS 4 6, 1), (cS 5 4, 3), (cS 6 1, 2), (cS 6 6, 1), (cC 0, 3), (cC 5, 3), (cC 6, 2)], [(cS 0 2, 3), (cS 1 4, 5), (cS 1 5, 1), (cS 2 0, 1), (cS 3 1, 5), (cS 4 1, 1), (cS 5 1, 2), (cS 5 2, 3), (cS 6 2, 3), (cS 6 4, 6)]), .leaf (12, [(cS 0 0, 4), (cS 0 5, 1), (cS 1 0, 3), (cS 1 1, 1), (cS 2 2, 4), (cS 2 3, 8), (cS 2 5, 1), (cS 3 3, 3), (cS 3 4, 1), (cS 3 5, 4), (cS 4 3, 6), (cS 4 4, 2), (cS 4 6, 4), (cS 5 0, 2), (cS 5 4, 3), (cS 6 1, 4), (cS 6 6, 4), (cR 5, 1), (cC 0, 4), (cC 5, 6), (cC 6, 1)], [(cS 0 2, 5), (cS 0 4, 4), (cS 1 2, 4), (cS 1 4, 8), (cS 1 5, 4), (cS 2 0, 4), (cS 3 0, 3), (cS 3 1, 5), (cS 4 1, 4), (cS 5 1, 1), (cS 5 2, 4), (cS 6 2, 4), (cS 6 4, 8), (cC 2, 3)])],
  .root (4, [(cS 0 0, 4), (cS 2 2, 2), (cS 2 3, 2), (cS 3 3, 1), (cS 3 5, 3), (cR 3, 1), (cR 4, 2), (cR 5, 2)], [(cS 0 2, 2), (cS 0 4, 2), (cS 1 5, 2), (cS 2 0, 2), (cS 3 0, 1), (cS 3 1, 1), (cS 5 4, 2), (cS 6 6, 2), (cR 1, 2), (cR 6, 2)]),
  .root (6, [(cS 0 6, 2), (cS 1 0, 2), (cS 2 0, 2), (cS 2 2, 3), (cS 2 3, 2), (cS 4 1, 2), (cS 4 2, 1), (cS 4 5, 2), (cS 4 6, 2), (cS 5 6, 2), (cS 6 0, 2), (cS 6 5, 4), (cC 0, 2), (cC 1, 2), (cC 2, 1)], [(cS 0 2, 3), (cS 0 4, 2), (cS 1 5, 2), (cS 1 6, 2), (cS 3 5, 2), (cS 3 6, 2), (cS 4 3, 2), (cS 5 4, 2), (cS 6 2, 3), (cC 3, 2), (cC 4, 2), (cC 5, 2)]),
  .root (4, [(cS 0 1, 1), (cS 0 6, 1), (cS 1 1, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 2 2, 1), (cS 3 2, 1), (cS 4 5, 1), (cS 5 6, 1), (cS 6 1, 1), (cS 6 6, 1), (cR 2, 1), (cR 3, 1), (cC 0, 2), (cC 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 0 4, 1), (cS 1 3, 1), (cS 1 5, 4), (cS 3 3, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 4 3, 2), (cS 5 1, 1), (cS 5 2, 1), (cS 5 4, 1), (cS 6 2, 3), (cS 6 4, 2), (cC 4, 1)]),
  .root (3, [(cS 0 0, 1), (cS 1 0, 1), (cS 2 2, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 2, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 0 4, 1), (cS 1 5, 2), (cS 4 3, 1), (cS 4 4, 1), (cS 5 4, 1), (cS 5 6, 1), (cS 6 6, 1), (cR 6, 1), (cC 3, 1), (cC 5, 1)]),
  .splitS0 [.leaf (4, [(cS 0 1, 2), (cS 0 6, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 2 3, 2), (cS 3 1, 1), (cS 3 3, 2), (cS 4 3, 1), (cS 5 3, 1), (cS 5 4, 1), (cS 5 6, 1), (cS 6 0, 1), (cS 6 5, 1), (cR 4, 1), (cC 1, 1), (cC 6, 2)], [(cS 0 3, 2), (cS 0 5, 1), (cS 1 3, 2), (cS 1 5, 1), (cS 2 5, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 5 1, 2), (cS 5 2, 1), (cS 6 2, 1), (cS 6 3, 1), (cS 6 4, 1), (cC 5, 2)]), .leaf (6, [(cS 0 1, 2), (cS 0 6, 1), (cS 1 0, 1), (cS 1 3, 3), (cS 2 1, 1), (cS 2 3, 2), (cS 3 3, 3), (cS 4 3, 2), (cS 4 4, 3), (cS 5 6, 1), (cS 6 6, 1), (cR 2, 1), (cR 4, 1), (cC 1, 4), (cC 6, 4)], [(cS 0 3, 3), (cS 1 5, 4), (cS 3 5, 3), (cS 3 6, 1), (cS 4 1, 1), (cS 5 1, 2), (cS 5 2, 3), (cS 6 2, 1), (cS 6 3, 2), (cS 6 4, 4), (cC 5, 2)]), .leaf (6, [(cS 0 1, 2), (cS 1 3, 2), (cS 2 1, 2), (cS 2 3, 3), (cS 3 3, 2), (cS 4 3, 3), (cS 5 4, 2), (cC 1, 4), (cC 3, 1), (cC 6, 6)], [(cS 0 3, 3), (cS 1 5, 2), (cS 3 5, 2), (cS 4 1, 2), (cS 5 1, 2), (cS 5 2, 2), (cS 6 2, 2), (cS 6 3, 1), (cS 6 4, 2), (cC 5, 4)]), .leaf (8, [(cS 0 0, 3), (cS 0 6, 4), (cS 1 0, 2), (cS 1 2, 3), (cS 2 1, 2), (cS 2 2, 1), (cS 2 3, 2), (cS 3 1, 3), (cS 3 3, 3), (cS 3 4, 1), (cS 4 3, 2), (cS 4 4, 1), (cS 4 6, 1), (cS 5 3, 2), (cS 5 4, 2), (cS 5 5, 2), (cS 5 6, 2), (cS 6 0, 1), (cS 6 1, 1), (cS 6 5, 1), (cR 2, 1), (cC 0, 2), (cC 1, 1), (cC 3, 1), (cC 6, 3)], [(cS 0 2, 4), (cS 0 4, 5), (cS 1 4, 2), (cS 1 5, 1), (cS 2 4, 2), (cS 2 5, 3), (cS 3 5, 3), (cS 3 6, 2), (cS 4 1, 2), (cS 4 2, 2), (cS 4 5, 3), (cS 5 1, 3), (cS 5 2, 1), (cS 6 2, 4), (cS 6 4, 3)]), .leaf (24, [(cS 0 5, 2), (cS 0 6, 11), (cS 1 0, 10), (cS 1 3, 10), (cS 2 2, 3), (cS 3 3, 13), (cS 4 3, 5), (cS 4 4, 9), (cS 4 6, 7), (cS 5 4, 7), (cS 5 5, 3), (cS 5 6, 11), (cS 6 1, 10), (cS 6 6, 11), (cR 2, 11), (cR 4, 3), (cC 0, 3), (cC 1, 11)], [(cS 0 2, 14), (cS 0 4, 3), (cS 1 4, 11), (cS 1 5, 11), (cS 2 5, 2), (cS 3 5, 11), (cS 3 6, 11), (cS 4 1, 7), (cS 4 2, 3), (cS 4 5, 2), (cS 5 2, 14), (cS 5 4, 2), (cS 6 2, 10), (cS 6 4, 22)]), .leaf (12, [(cS 0 0, 3), (cS 0 6, 3), (cS 1 0, 1), (cS 1 2, 1), (cS 2 0, 3), (cS 2 2, 5), (cS 2 3, 6), (cS 3 1, 1), (cS 3 3, 6), (cS 4 3, 1), (cS 4 4, 2), (cS 5 3, 3), (cS 5 4, 3), (cS 5 5, 2), (cS 5 6, 1), (cS 6 0, 1), (cS 6 5, 1), (cS 6 6, 2), (cR 4, 3), (cC 0, 2), (cC 1, 6), (cC 6, 6)], [(cS 0 2, 10), (cS 0 4, 6), (cS 1 4, 6), (cS 1 5, 3), (cS 2 5, 3), (cS 3 5, 9), (cS 3 6, 1), (cS 4 5, 2), (cS 5 1, 3), (cS 5 2, 7), (cS 6 4, 6), (cC 2, 2)])],
  .splitS0 [.leaf (4, [(cS 0 0, 1), (cS 1 6, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 3 4, 1), (cS 4 1, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 3, 1), (cS 5 4, 1), (cS 6 6, 1), (cR 2, 1), (cC 0, 2), (cC 1, 1), (cC 2, 2)], [(cS 0 2, 1), (cS 0 3, 2), (cS 0 4, 1), (cS 0 5, 1), (cS 1 3, 1), (cS 1 5, 1), (cS 2 4, 1), (cS 2 5, 1), (cS 3 5, 1), (cS 4 6, 1), (cS 5 4, 1), (cS 5 6, 2), (cR 6, 1), (cC 5, 1), (cC 6, 1)]), .leaf (24, [(cS 0 6, 7), (cS 1 0, 11), (cS 1 2, 3), (cS 2 3, 8), (cS 2 4, 1), (cS 3 1, 3), (cS 3 3, 4), (cS 3 4, 7), (cS 4 1, 4), (cS 4 3, 11), (cS 4 4, 9), (cS 5 1, 3), (cS 5 3, 4), (cS 6 0, 8), (cR 2, 4), (cC 0, 9), (cC 1, 8), (cC 2, 9)], [(cS 0 2, 4), (cS 0 3, 8), (cS 0 4, 5), (cS 0 5, 2), (cS 1 4, 11), (cS 1 5, 3), (cS 2 5, 3), (cS 3 5, 1), (cS 3 6, 1), (cS 4 6, 3), (cS 5 0, 7), (cS 5 4, 7), (cS 5 6, 3), (cS 6 2, 1), (cS 6 3, 8), (cS 6 4, 6), (cR 6, 3), (cC 5, 8), (cC 6, 11)]), .leaf (5, [(cS 0 6, 2), (cS 2 0, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 4, 1), (cR 2, 1), (cC 0, 3), (cC 1, 2), (cC 2, 2), (cC 3, 1), (cC 4, 1)], [(cS 0 2, 1), (cS 0 3, 2), (cS 0 4, 1), (cS 0 5, 1), (cS 1 5, 1), (cS 2 4, 1), (cS 2 5, 1), (cS 3 5, 1), (cS 4 6, 1), (cS 5 0, 2), (cS 5 6, 1), (cS 6 3, 1), (cR 6, 1), (cC 5, 2), (cC 6, 1)]), .leaf (20, [(cS 0 0, 6), (cS 0 6, 7), (cS 1 6, 6), (cS 2 0, 4), (cS 2 2, 7), (cS 2 3, 6), (cS 3 3, 8), (cS 3 4, 2), (cS 4 1, 6), (cS 4 2, 4), (cS 4 3, 4), (cS 4 4, 5), (cS 5 2, 2), (cS 5 3, 6), (cS 5 4, 4), (cR 2, 3), (cC 0, 7), (cC 1, 7), (cC 2, 3), (cC 3, 1)], [(cS 0 2, 11), (cS 0 3, 5), (cS 0 4, 5), (cS 0 5, 2), (cS 1 4, 2), (cS 2 4, 1), (cS 2 5, 6), (cS 3 5, 1), (cS 3 6, 8), (cS 4 6, 6), (cS 5 0, 4), (cS 5 6, 10), (cS 6 2, 6), (cS 6 5, 1), (cS 6 6, 3), (cR 6, 3), (cC 4, 7), (cC 5, 5)]), .leaf (20, [(cS 0 0, 9), (cS 0 6, 7), (cS 1 6, 6), (cS 2 0, 7), (cS 2 2, 8), (cS 2 3, 4), (cS 3 3, 5), (cS 3 4, 5), (cS 4 1, 7), (cS 4 2, 2), (cS 4 3, 6), (cS 4 4, 8), (cS 5 2, 4), (cS 5 3, 1), (cR 2, 3), (cR 4, 2), (cC 0, 4), (cC 1, 7), (cC 2, 2), (cC 3, 3)], [(cS 0 2, 11), (cS 0 3, 4), (cS 0 4, 3), (cS 0 5, 4), (cS 1 4, 10), (cS 2 5, 8), (cS 3 5, 2), (cS 3 6, 7), (cS 4 6, 8), (cS 5 0, 2), (cS 5 4, 7), (cS 5 6, 10), (cS 6 2, 1), (cS 6 3, 2), (cS 6 4, 3), (cR 6, 8), (cC 5, 3)]), .leaf (2, [(cS 0 6, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 5 2, 1), (cS 5 4, 1), (cC 0, 1), (cC 1, 1)], [(cS 0 2, 2), (cS 0 4, 1), (cS 1 4, 1), (cS 2 5, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 5 6, 2), (cS 6 3, 1), (cS 6 5, 1)])],
  .root (5, [(cS 0 0, 4), (cS 1 0, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 0, 1), (cS 3 6, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 4 5, 1), (cR 2, 4), (cR 4, 3)], [(cS 0 2, 5), (cS 0 4, 1), (cS 1 4, 4), (cS 1 5, 5), (cS 4 1, 1), (cS 5 0, 1), (cS 5 1, 2), (cS 5 2, 1), (cS 6 3, 2), (cS 6 4, 1), (cS 6 5, 2), (cS 6 6, 2), (cR 5, 1), (cR 6, 1)]),
  .root (30, [(cS 0 0, 3), (cS 0 1, 17), (cS 0 4, 16), (cS 0 5, 14), (cS 1 0, 10), (cS 1 3, 14), (cS 1 6, 17), (cS 2 2, 9), (cS 2 3, 7), (cS 2 4, 16), (cS 2 5, 14), (cS 3 2, 7), (cS 3 3, 7), (cS 4 1, 10), (cS 5 0, 13), (cS 5 1, 7), (cS 5 2, 13), (cS 5 6, 13), (cS 6 0, 10), (cS 6 6, 17)], [(cS 0 2, 12), (cS 2 0, 3), (cS 2 1, 17), (cS 3 0, 10), (cS 3 1, 10), (cS 3 6, 17), (cS 4 3, 13), (cS 4 4, 17), (cS 4 5, 13), (cS 4 6, 4), (cS 6 2, 14), (cS 6 4, 30), (cC 2, 4)]),
  .root (3, [(cS 0 1, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 1 4, 1), (cS 2 3, 2), (cS 3 5, 1), (cS 4 0, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 6 0, 1), (cR 0, 1), (cR 2, 1), (cC 5, 1), (cC 6, 1)], [(cS 2 1, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 4 1, 1), (cS 4 3, 2), (cS 4 4, 1), (cS 5 1, 1), (cS 6 2, 2), (cS 6 4, 3), (cC 2, 1)]),
  .root (2, [(cS 4 1, 1), (cS 4 6, 1), (cR 0, 2), (cR 2, 2), (cR 4, 1)], [(cS 2 1, 2), (cS 4 3, 1), (cS 4 4, 1), (cR 6, 2)]),
  .splitS0 [.leaf (4, [(cS 0 0, 2), (cS 0 5, 2), (cS 1 1, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 2 5, 2), (cS 3 2, 1), (cS 4 4, 1), (cS 5 6, 2), (cS 6 0, 2), (cS 6 6, 2), (cR 1, 1), (cC 3, 2), (cC 4, 1)], [(cS 0 2, 3), (cS 0 4, 1), (cS 1 2, 1), (cS 2 0, 2), (cS 3 1, 2), (cS 3 6, 2), (cS 4 0, 1), (cS 4 5, 1), (cS 5 1, 2), (cS 5 2, 1), (cS 6 2, 1), (cS 6 4, 3), (cR 4, 1)]), .leaf (24, [(cS 0 0, 2), (cS 0 1, 3), (cS 1 4, 2), (cS 1 6, 3), (cS 2 2, 4), (cS 2 3, 6), (cS 2 4, 1), (cS 2 5, 2), (cS 2 6, 1), (cS 3 3, 3), (cS 3 4, 3), (cS 4 3, 10), (cS 4 4, 11), (cS 5 0, 5), (cS 5 5, 10), (cS 6 0, 8), (cS 6 6, 11), (cR 0, 11), (cR 1, 8), (cR 2, 8), (cC 3, 3), (cC 5, 3)], [(cS 0 2, 2), (cS 2 0, 4), (cS 2 1, 4), (cS 3 0, 8), (cS 3 1, 8), (cS 3 5, 7), (cS 3 6, 3), (cS 4 1, 8), (cS 4 2, 8), (cS 4 6, 14), (cS 5 0, 5), (cS 5 1, 6), (cS 5 2, 3), (cS 6 2, 16), (cS 6 3, 6), (cS 6 4, 24)]), .leaf (3, [(cS 2 2, 1), (cS 2 3, 1), (cS 2 5, 1), (cS 3 4, 1), (cS 4 3, 2), (cS 4 4, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 5 6, 1), (cS 6 1, 1), (cS 6 6, 1), (cR 0, 2), (cR 1, 1), (cR 2, 1)], [(cS 2 0, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 1, 1), (cS 6 2, 2), (cS 6 3, 1), (cS 6 4, 2), (cS 6 5, 1)]), .leaf (10, [(cS 0 0, 3), (cS 0 1, 2), (cS 1 6, 2), (cS 2 2, 4), (cS 2 3, 1), (cS 2 5, 1), (cS 3 3, 1), (cS 3 4, 2), (cS 4 3, 2), (cS 5 0, 3), (cS 5 4, 2), (cS 5 6, 1), (cS 6 0, 3), (cS 6 6, 5), (cR 0, 2), (cR 1, 3), (cR 2, 1), (cR 5, 1), (cC 3, 3), (cC 4, 2), (cC 5, 3)], [(cS 0 2, 3), (cS 0 4, 8), (cS 2 0, 4), (cS 2 1, 2), (cS 3 0, 2), (cS 3 1, 3), (cS 3 5, 1), (cS 3 6, 4), (cS 4 1, 3), (cS 4 2, 2), (cS 4 6, 3), (cS 5 1, 3), (cS 6 2, 7), (cS 6 4, 2), (cR 4, 2)]), .leaf (8, [(cS 0 1, 2), (cS 1 0, 1), (cS 1 4, 2), (cS 1 6, 1), (cS 2 3, 2), (cS 3 3, 1), (cS 4 3, 3), (cS 4 4, 4), (cS 5 0, 2), (cS 5 5, 3), (cS 6 0, 2), (cS 6 6, 3), (cR 0, 4), (cR 1, 1), (cR 2, 4), (cC 3, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 2 1, 2), (cS 3 0, 1), (cS 3 1, 5), (cS 3 5, 3), (cS 3 6, 2), (cS 4 0, 2), (cS 4 2, 2), (cS 4 6, 3), (cS 5 1, 4), (cS 5 2, 1), (cS 6 2, 2), (cS 6 3, 4), (cS 6 4, 4), (cS 6 5, 4), (cC 2, 1)]), .leaf (4, [(cS 0 0, 2), (cS 0 6, 1), (cS 2 2, 2), (cS 2 4, 1), (cS 2 5, 1), (cS 3 3, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 5 6, 1), (cS 6 1, 2), (cS 6 6, 2), (cR 1, 2), (cC 3, 1), (cC 4, 1), (cC 5, 1)], [(cS 0 2, 2), (cS 0 4, 2), (cS 2 0, 2), (cS 3 1, 2), (cS 3 6, 2), (cS 4 1, 1), (cS 4 6, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 2, 2), (cS 6 4, 2), (cR 4, 1)]), .leaf (12, [(cS 0 0, 1), (cS 0 1, 1), (cS 1 3, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 2, 3), (cS 2 4, 2), (cS 2 5, 2), (cS 3 2, 1), (cS 3 3, 4), (cS 3 4, 1), (cS 4 3, 2), (cS 4 4, 5), (cS 5 6, 3), (cS 6 0, 4), (cS 6 5, 5), (cS 6 6, 1), (cR 0, 6), (cR 1, 4), (cR 2, 4), (cR 5, 4), (cC 4, 1)], [(cS 0 2, 1), (cS 2 0, 3), (cS 2 1, 1), (cS 3 0, 5), (cS 3 1, 3), (cS 3 5, 2), (cS 3 6, 4), (cS 4 1, 4), (cS 4 2, 5), (cS 4 5, 3), (cS 4 6, 3), (cS 5 0, 2), (cS 5 1, 2), (cS 5 2, 1), (cS 6 2, 11), (cS 6 4, 12)]), .leaf (2, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 5, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 6 6, 1), (cR 2, 1), (cC 3, 1)], [(cS 0 2, 1), (cS 0 4, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 5, 1), (cS 4 2, 1), (cS 4 6, 1), (cS 5 1, 1), (cS 6 2, 1), (cS 6 4, 1)]), .leaf (6, [(cS 0 0, 2), (cS 3 3, 2), (cS 4 4, 2), (cS 5 4, 1), (cS 5 6, 1), (cS 6 0, 2), (cS 6 6, 2), (cR 0, 2), (cR 1, 2), (cR 2, 2), (cR 5, 1), (cC 3, 2), (cC 5, 2)], [(cS 0 2, 2), (cS 0 3, 2), (cS 0 4, 4), (cS 2 0, 2), (cS 3 1, 4), (cS 3 5, 2), (cS 3 6, 2), (cS 4 0, 2), (cS 4 6, 2), (cS 5 1, 3), (cS 5 2, 1), (cS 6 4, 2), (cC 2, 2)]), .leaf (4, [(cS 0 0, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 2 5, 1), (cS 3 2, 1), (cS 3 3, 1), (cS 3 4, 1), (cS 4 4, 2), (cS 5 3, 1), (cS 5 5, 1), (cS 6 0, 2), (cS 6 6, 2), (cR 0, 1), (cR 1, 2), (cC 3, 1), (cC 5, 1)], [(cS 0 2, 3), (cS 0 4, 2), (cS 1 2, 1), (cS 2 0, 2), (cS 3 1, 2), (cS 3 6, 2), (cS 4 0, 2), (cS 4 2, 1), (cS 4 6, 2), (cS 5 1, 2), (cS 5 2, 1), (cS 6 2, 1), (cS 6 4, 2)]), .leaf (6, [(cS 0 0, 2), (cS 0 1, 1), (cS 0 6, 1), (cS 1 5, 1), (cS 3 2, 1), (cS 3 3, 1), (cS 4 4, 2), (cS 5 6, 1), (cS 6 0, 1), (cS 6 1, 1), (cS 6 6, 3), (cR 0, 1), (cR 1, 2), (cR 2, 2), (cR 5, 1), (cC 3, 2), (cC 4, 1), (cC 5, 1)], [(cS 0 2, 1), (cS 0 3, 3), (cS 0 4, 3), (cS 1 2, 2), (cS 2 0, 2), (cS 3 0, 1), (cS 3 1, 3), (cS 3 5, 2), (cS 3 6, 1), (cS 4 0, 1), (cS 4 2, 1), (cS 4 6, 2), (cS 5 1, 3), (cS 5 2, 1), (cS 6 2, 2), (cS 6 4, 3), (cR 4, 1)]), .leaf (4, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 5, 1), (cS 1 3, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 3 3, 2), (cS 4 4, 2), (cS 6 1, 1), (cS 6 6, 2), (cR 0, 1), (cR 1, 1), (cR 2, 2), (cR 5, 2)], [(cS 0 2, 1), (cS 0 4, 2), (cS 2 1, 1), (cS 3 0, 2), (cS 3 1, 1), (cS 3 5, 2), (cS 4 1, 1), (cS 4 2, 2), (cS 4 6, 2), (cS 5 1, 1), (cS 6 2, 3), (cS 6 4, 2)])],
  .splitS0 [.leaf (4, [(cS 0 0, 2), (cS 0 1, 1), (cS 0 4, 1), (cS 1 3, 1), (cS 1 5, 2), (cS 1 6, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 2, 1), (cS 3 3, 1), (cS 3 4, 1), (cS 4 1, 3), (cS 4 3, 1), (cS 5 1, 1), (cS 5 2, 2), (cS 5 4, 2), (cR 1, 1), (cC 3, 1)], [(cS 0 2, 2), (cS 0 3, 2), (cS 2 0, 1), (cS 2 1, 2), (cS 3 0, 1), (cS 3 5, 2), (cS 3 6, 1), (cS 4 5, 2), (cS 4 6, 1), (cS 5 0, 2), (cS 6 4, 1), (cS 6 5, 2), (cR 6, 1), (cC 6, 1)]), .leaf (20, [(cS 0 0, 2), (cS 0 1, 3), (cS 1 6, 5), (cS 2 3, 8), (cS 2 5, 3), (cS 3 2, 4), (cS 3 3, 2), (cS 3 5, 4), (cS 4 1, 8), (cS 4 2, 3), (cS 4 3, 8), (cS 4 4, 4), (cS 5 1, 9), (cS 5 2, 6), (cR 0, 9), (cR 1, 6), (cR 2, 6), (cR 4, 3), (cC 4, 5)], [(cS 0 2, 2), (cS 0 3, 3), (cS 0 5, 2), (cS 2 0, 3), (cS 2 1, 8), (cS 3 0, 7), (cS 3 1, 2), (cS 3 5, 2), (cS 3 6, 5), (cS 4 5, 5), (cS 4 6, 9), (cS 5 0, 5), (cS 5 4, 3), (cS 5 6, 6), (cS 6 3, 9), (cS 6 4, 3), (cS 6 5, 9), (cS 6 6, 3), (cR 6, 6)]), .leaf (20, [(cS 0 0, 2), (cS 0 1, 3), (cS 1 4, 5), (cS 1 6, 5), (cS 2 2, 5), (cS 2 3, 9), (cS 2 5, 9), (cS 3 2, 4), (cS 3 3, 2), (cS 3 4, 9), (cS 4 1, 8), (cS 4 2, 6), (cS 4 3, 8), (cS 4 4, 9), (cS 5 1, 12), (cS 5 2, 3), (cS 5 3, 3), (cR 0, 9), (cR 1, 6)], [(cS 0 2, 2), (cS 0 3, 3), (cS 2 0, 6), (cS 2 1, 9), (cS 3 0, 4), (cS 3 1, 2), (cS 3 5, 2), (cS 3 6, 7), (cS 4 0, 6), (cS 4 5, 8), (cS 5 0, 2), (cS 5 4, 3), (cS 5 6, 9), (cS 6 3, 9), (cS 6 4, 2), (cS 6 5, 12), (cR 6, 6), (cC 6, 3)]), .leaf (20, [(cS 0 0, 2), (cS 0 1, 3), (cS 1 4, 5), (cS 1 6, 5), (cS 2 2, 9), (cS 2 3, 5), (cS 2 4, 4), (cS 2 5, 9), (cS 3 3, 6), (cS 3 4, 5), (cS 4 1, 8), (cS 4 2, 7), (cS 4 3, 7), (cS 4 4, 7), (cS 5 1, 10), (cS 5 2, 2), (cS 5 3, 2), (cS 5 4, 2), (cR 0, 9), (cR 1, 6), (cR 5, 2)], [(cS 0 2, 2), (cS 0 3, 3), (cS 0 4, 2), (cS 0 5, 2), (cS 2 0, 9), (cS 2 1, 6), (cS 3 0, 1), (cS 3 1, 5), (cS 3 6, 10), (cS 4 0, 6), (cS 4 5, 6), (cS 4 6, 3), (cS 5 0, 2), (cS 5 5, 1), (cS 5 6, 9), (cS 6 3, 9), (cS 6 5, 8), (cS 6 6, 3), (cR 6, 6), (cC 5, 2)]), .leaf (40, [(cS 0 0, 4), (cS 0 1, 6), (cS 1 4, 10), (cS 1 6, 10), (cS 2 2, 10), (cS 2 3, 6), (cS 2 5, 6), (cS 3 2, 9), (cS 3 3, 3), (cS 3 4, 19), (cS 4 3, 13), (cS 4 4, 3), (cS 5 1, 16), (cS 5 2, 3), (cS 5 5, 4), (cR 0, 18), (cR 1, 12), (cR 2, 12), (cR 4, 15), (cR 5, 9)], [(cS 0 2, 4), (cS 0 3, 6), (cS 2 1, 17), (cS 3 0, 2), (cS 3 1, 23), (cS 3 6, 20), (cS 4 6, 12), (cS 5 0, 3), (cS 5 4, 6), (cS 5 6, 19), (cS 6 3, 18), (cS 6 4, 5), (cS 6 5, 20), (cR 6, 12), (cC 5, 3), (cC 6, 6)]), .leaf (2, [(cS 0 0, 1), (cS 0 5, 1), (cS 2 2, 1), (cS 2 5, 1), (cS 3 4, 1), (cS 5 1, 1), (cR 1, 1), (cR 4, 1), (cC 3, 1)], [(cS 0 2, 1), (cS 0 4, 1), (cS 2 0, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 5, 1), (cR 6, 1)]), .leaf (2, [(cS 0 0, 1), (cS 0 6, 1), (cS 2 2, 1), (cS 2 5, 1), (cS 3 3, 1), (cS 5 0, 1), (cS 5 2, 1), (cR 1, 1), (cR 4, 1), (cC 4, 1)], [(cS 0 2, 1), (cS 2 0, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 4 6, 1), (cS 5 6, 1), (cS 6 4, 1), (cR 6, 1)]), .leaf (60, [(cS 0 1, 7), (cS 1 6, 16), (cS 2 2, 16), (cS 2 3, 26), (cS 2 5, 26), (cS 3 3, 18), (cS 4 1, 16), (cS 4 2, 8), (cS 4 3, 34), (cS 4 4, 24), (cS 5 1, 26), (cS 5 2, 9), (cR 0, 26), (cR 1, 18), (cR 5, 9), (cC 0, 9), (cC 4, 18)], [(cS 0 2, 9), (cS 0 3, 7), (cS 0 5, 33), (cS 2 0, 8), (cS 2 1, 26), (cS 3 1, 18), (cS 3 6, 16), (cS 4 6, 17), (cS 5 4, 9), (cS 5 6, 34), (cS 6 3, 26), (cS 6 4, 9), (cR 3, 18), (cR 6, 18), (cC 6, 9)]), .leaf (6, [(cS 0 0, 2), (cS 0 1, 2), (cS 0 5, 1), (cS 1 3, 2), (cS 1 4, 1), (cS 1 5, 2), (cS 1 6, 2), (cS 3 3, 3), (cS 4 1, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 5 1, 1), (cR 1, 1), (cR 2, 1), (cR 5, 3), (cC 0, 1), (cC 2, 1), (cC 3, 1), (cC 4, 1)], [(cS 0 2, 2), (cS 0 3, 4), (cS 0 4, 2), (cS 0 5, 2), (cS 2 1, 3), (cS 4 0, 1), (cS 4 6, 1), (cS 5 6, 3), (cS 6 6, 1), (cR 3, 3), (cR 6, 1), (cC 5, 1), (cC 6, 1)]), .leaf (40, [(cS 0 0, 26), (cS 0 5, 22), (cS 1 0, 5), (cS 1 3, 5), (cS 1 6, 9), (cS 2 2, 2), (cS 2 5, 15), (cS 3 2, 14), (cS 3 4, 9), (cS 4 1, 17), (cS 4 2, 6), (cS 4 3, 3), (cS 4 4, 2), (cS 5 1, 23), (cS 5 2, 8), (cS 5 3, 6), (cS 5 4, 3), (cR 1, 9), (cR 2, 7), (cC 3, 17), (cC 4, 9)], [(cS 0 1, 5), (cS 0 2, 26), (cS 0 3, 5), (cS 0 4, 15), (cS 1 2, 9), (cS 2 0, 5), (cS 2 1, 15), (cS 2 6, 7), (cS 3 0, 17), (cS 3 1, 3), (cS 3 6, 11), (cS 4 0, 3), (cS 4 5, 20), (cS 4 6, 9), (cS 5 0, 10), (cS 5 5, 6), (cS 5 6, 18), (cS 6 4, 11), (cS 6 5, 5), (cS 6 6, 5), (cR 6, 9)]), .leaf (6, [(cS 0 0, 3), (cS 0 1, 2), (cS 1 3, 1), (cS 1 5, 3), (cS 1 6, 2), (cS 2 6, 1), (cS 3 2, 1), (cS 3 3, 1), (cS 4 1, 4), (cS 4 3, 1), (cS 5 1, 2), (cS 5 2, 2), (cS 5 4, 1), (cR 1, 1), (cR 2, 1), (cC 2, 1), (cC 3, 2), (cC 4, 2)], [(cS 0 2, 2), (cS 0 3, 4), (cS 0 4, 2), (cS 2 0, 1), (cS 2 1, 3), (cS 3 0, 2), (cS 3 5, 3), (cS 3 6, 1), (cS 4 5, 3), (cS 4 6, 3), (cS 5 0, 3), (cS 6 5, 3), (cS 6 6, 2), (cR 6, 1)]), .leaf (30, [(cS 0 0, 3), (cS 0 1, 5), (cS 1 6, 8), (cS 2 2, 1), (cS 2 3, 13), (cS 2 5, 6), (cS 3 2, 6), (cS 3 3, 3), (cS 4 1, 4), (cS 4 2, 6), (cS 4 3, 4), (cS 4 4, 3), (cS 5 1, 15), (cS 5 2, 6), (cS 5 3, 3), (cR 0, 13), (cR 1, 9), (cR 2, 7), (cR 4, 11), (cC 4, 9)], [(cS 0 2, 3), (cS 0 3, 5), (cS 0 5, 6), (cS 2 0, 1), (cS 2 1, 13), (cS 3 0, 13), (cS 3 1, 3), (cS 3 5, 5), (cS 3 6, 4), (cS 4 5, 4), (cS 4 6, 9), (cS 5 0, 6), (cS 5 6, 10), (cS 6 3, 13), (cS 6 4, 5), (cS 6 5, 7), (cR 6, 9), (cC 5, 3), (cC 6, 5)])],
  .splitS0 [.leaf (40, [(cS 0 0, 5), (cS 0 1, 22), (cS 0 6, 14), (cS 1 4, 13), (cS 1 6, 8), (cS 2 2, 6), (cS 2 3, 2), (cS 2 5, 8), (cS 3 3, 13), (cS 3 5, 5), (cS 3 6, 8), (cS 4 2, 21), (cS 4 4, 13), (cS 4 5, 11), (cS 4 6, 11), (cS 5 3, 13), (cS 5 4, 2), (cR 1, 13), (cR 2, 13), (cC 3, 6), (cC 4, 8), (cC 5, 6)], [(cS 0 2, 12), (cS 0 3, 28), (cS 0 5, 10), (cS 2 1, 8), (cS 3 0, 11), (cS 3 1, 13), (cS 4 0, 2), (cS 4 1, 6), (cS 5 0, 7), (cS 5 1, 19), (cS 5 2, 15), (cS 5 6, 12), (cS 6 4, 8), (cS 6 5, 16), (cS 6 6, 8), (cR 6, 6), (cC 0, 8)]), .leaf (2, [(cS 2 5, 1), (cS 3 3, 1), (cS 4 3, 1), (cS 4 5, 2), (cS 5 3, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1)], [(cS 3 0, 1), (cS 3 1, 1), (cS 4 0, 1), (cS 4 1, 1), (cS 5 0, 1), (cS 5 2, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 6, 1)]), .leaf (2, [(cS 2 5, 1), (cS 3 3, 1), (cS 4 3, 1), (cS 4 5, 2), (cS 5 3, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1)], [(cS 3 0, 1), (cS 3 1, 1), (cS 4 0, 1), (cS 4 1, 1), (cS 5 0, 1), (cS 5 2, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 6, 1)]), .leaf (2, [(cS 2 3, 1), (cS 3 5, 1), (cS 4 0, 1), (cS 4 3, 2), (cS 4 5, 1), (cS 5 5, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1)], [(cS 3 0, 1), (cS 3 1, 1), (cS 4 1, 1), (cS 5 0, 1), (cS 5 2, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 6, 1)]), .leaf (2, [(cS 4 3, 1), (cS 5 5, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1)], [(cS 3 1, 2), (cS 4 1, 1), (cS 5 0, 1), (cS 5 2, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 6, 1)]), .leaf (6, [(cS 0 0, 2), (cS 0 6, 1), (cS 1 0, 1), (cS 1 3, 1), (cS 1 6, 1), (cS 2 2, 2), (cS 2 5, 1), (cS 3 3, 3), (cS 3 5, 1), (cS 3 6, 2), (cS 4 2, 4), (cS 4 4, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 3, 2), (cS 5 4, 1), (cR 0, 1), (cR 1, 2), (cR 2, 1), (cC 4, 2), (cC 5, 1)], [(cS 0 2, 2), (cS 0 4, 3), (cS 2 0, 1), (cS 3 0, 2), (cS 3 1, 2), (cS 4 1, 2), (cS 4 2, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 1, 2), (cS 5 6, 3), (cS 6 2, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 6, 2), (cC 1, 1)]), .leaf (2, [(cS 2 3, 1), (cS 3 5, 1), (cS 4 3, 2), (cS 4 4, 1), (cS 4 5, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1)], [(cS 3 0, 1), (cS 3 1, 1), (cS 4 0, 1), (cS 4 1, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 2, 1), (cS 6 4, 1), (cR 6, 1)]), .leaf (40, [(cS 0 0, 4), (cS 0 1, 6), (cS 0 4, 10), (cS 1 6, 10), (cS 2 2, 10), (cS 2 4, 10), (cS 3 6, 10), (cS 4 3, 16), (cS 4 5, 22), (cS 5 3, 6), (cR 0, 18), (cR 1, 12), (cR 2, 18), (cR 3, 12), (cR 4, 18)], [(cS 0 2, 4), (cS 0 3, 6), (cS 2 1, 11), (cS 3 1, 29), (cS 4 1, 11), (cS 5 0, 23), (cS 5 1, 6), (cS 5 2, 23), (cS 6 3, 18), (cS 6 4, 5), (cS 6 5, 23), (cS 6 6, 6), (cR 6, 12)]), .leaf (6, [(cS 0 0, 1), (cS 0 1, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 3, 3), (cS 4 5, 2), (cS 5 3, 2), (cS 5 4, 2), (cS 5 5, 1), (cR 0, 2), (cR 1, 2), (cR 2, 2), (cR 3, 2), (cC 3, 1), (cC 4, 1)], [(cS 0 2, 2), (cS 0 3, 4), (cS 0 4, 2), (cS 0 5, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 3 1, 4), (cS 3 2, 1), (cS 4 0, 1), (cS 4 1, 1), (cS 4 6, 2), (cS 5 0, 2), (cS 5 1, 2), (cS 5 2, 3), (cS 5 6, 1), (cS 6 0, 1), (cS 6 1, 1), (cS 6 5, 3), (cS 6 6, 2)]), .leaf (30, [(cS 0 0, 18), (cS 0 4, 2), (cS 0 5, 3), (cS 0 6, 4), (cS 1 0, 9), (cS 1 3, 2), (cS 1 4, 7), (cS 1 6, 11), (cS 2 2, 3), (cS 2 3, 5), (cS 3 5, 4), (cS 3 6, 5), (cS 4 2, 12), (cS 4 4, 7), (cS 4 5, 5), (cS 5 3, 4), (cR 1, 3), (cR 2, 7), (cR 3, 4), (cR 4, 3), (cC 3, 11), (cC 4, 5), (cC 5, 10)], [(cS 0 2, 18), (cS 0 3, 7), (cS 1 2, 5), (cS 2 1, 5), (cS 3 0, 14), (cS 3 1, 4), (cS 4 0, 5), (cS 5 0, 6), (cS 5 1, 12), (cS 5 2, 11), (cS 5 6, 16), (cS 6 4, 18), (cS 6 5, 7), (cS 6 6, 3), (cR 6, 5), (cC 1, 7)]), .leaf (30, [(cS 0 0, 2), (cS 0 1, 15), (cS 0 4, 3), (cS 0 6, 12), (cS 1 5, 3), (cS 1 6, 3), (cS 2 2, 9), (cS 2 5, 7), (cS 3 3, 13), (cS 3 5, 7), (cS 3 6, 11), (cS 4 2, 10), (cS 4 3, 4), (cS 4 5, 12), (cS 5 3, 13), (cS 5 4, 4), (cS 5 5, 3), (cR 1, 13), (cR 2, 5), (cC 3, 3), (cC 4, 11)], [(cS 0 2, 8), (cS 0 3, 22), (cS 0 4, 8), (cS 0 5, 7), (cS 2 0, 9), (cS 2 1, 3), (cS 3 0, 5), (cS 3 1, 13), (cS 4 0, 5), (cS 4 1, 7), (cS 4 6, 9), (cS 5 0, 9), (cS 5 1, 9), (cS 5 2, 14), (cS 5 6, 7), (cS 6 0, 7), (cS 6 1, 7), (cS 6 5, 15), (cS 6 6, 9)]), .leaf (2, [(cS 2 3, 1), (cS 3 5, 1), (cS 4 0, 1), (cS 4 3, 2), (cS 4 5, 1), (cS 5 5, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1)], [(cS 3 0, 1), (cS 3 1, 1), (cS 4 1, 1), (cS 5 0, 1), (cS 5 2, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 6, 1)])],
  .root (1, [(cS 6 1, 1), (cS 6 6, 1), (cR 1, 1), (cR 3, 1)], [(cS 6 2, 1), (cS 6 4, 1), (cR 4, 1)]),
  .root (1, [(cS 4 1, 1), (cS 4 2, 1), (cR 0, 1), (cR 2, 1)], [(cS 4 4, 1), (cS 4 6, 1), (cR 6, 1)]),
  .root (1, [(cR 1, 1), (cR 3, 1)], [(cR 4, 1), (cR 6, 1)]),
  .splitS0 [.leaf (5, [(cS 0 1, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 4 2, 2), (cS 4 3, 2), (cS 5 4, 1), (cR 0, 1), (cR 1, 2), (cR 2, 2), (cR 3, 1), (cC 3, 1), (cC 4, 1), (cC 5, 1)], [(cS 0 2, 1), (cS 0 4, 1), (cS 0 5, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 6, 2), (cS 5 1, 2), (cS 5 6, 1), (cS 6 3, 1), (cS 6 6, 1), (cR 4, 2), (cR 6, 3)]), .leaf (12, [(cS 4 2, 1), (cS 4 3, 4), (cS 4 4, 1), (cS 5 3, 7), (cR 0, 5), (cR 1, 7), (cR 2, 5), (cR 3, 7)], [(cS 0 2, 3), (cS 0 3, 9), (cS 4 0, 1), (cS 4 1, 4), (cS 4 5, 8), (cS 4 6, 4), (cS 5 0, 7), (cS 5 2, 8), (cS 5 4, 3), (cS 6 0, 3), (cS 6 5, 8), (cR 6, 4)]), .leaf (2, [(cS 4 3, 1), (cS 5 3, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)], [(cS 0 3, 1), (cS 0 5, 1), (cS 4 1, 1), (cS 4 5, 1), (cS 4 6, 1), (cR 5, 1), (cR 6, 1)]), .leaf (2, [(cS 4 3, 1), (cS 5 3, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)], [(cS 0 3, 1), (cS 0 5, 1), (cS 4 1, 1), (cS 4 5, 1), (cS 4 6, 1), (cR 5, 1), (cR 6, 1)]), .leaf (3, [(cS 4 2, 1), (cS 4 3, 2), (cS 4 4, 1), (cR 0, 1), (cR 1, 2), (cR 2, 1), (cR 3, 2)], [(cS 0 3, 1), (cS 3 0, 1), (cS 4 5, 1), (cS 4 6, 2), (cS 5 1, 2), (cS 6 5, 1), (cR 5, 1), (cR 6, 2)]), .leaf (2, [(cS 4 3, 1), (cS 5 3, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)], [(cS 0 3, 1), (cS 4 1, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 6 5, 1), (cR 5, 1), (cR 6, 1)]), .leaf (2, [(cS 4 3, 1), (cS 5 3, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)], [(cS 0 3, 1), (cS 0 5, 1), (cS 4 1, 1), (cS 4 5, 1), (cS 4 6, 1), (cR 5, 1), (cR 6, 1)]), .leaf (2, [(cS 4 3, 2), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)], [(cS 4 1, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 2, 1), (cS 6 4, 1), (cR 6, 1)]), .leaf (24, [(cS 0 1, 2), (cS 0 6, 2), (cS 3 1, 2), (cS 3 2, 2), (cS 4 2, 6), (cS 4 3, 5), (cS 4 4, 5), (cS 5 3, 13), (cS 5 4, 5), (cR 0, 8), (cR 1, 14), (cR 2, 11), (cR 3, 11), (cC 4, 3)], [(cS 0 2, 11), (cS 0 3, 13), (cS 0 4, 11), (cS 3 6, 2), (cS 4 0, 8), (cS 4 1, 3), (cS 4 5, 8), (cS 4 6, 14), (cS 5 1, 10), (cS 5 2, 8), (cS 6 0, 11), (cS 6 1, 3), (cS 6 5, 13), (cS 6 6, 11), (cR 5, 3)]), .leaf (2, [(cS 4 3, 2), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)], [(cS 0 2, 1), (cS 0 4, 1), (cS 4 1, 1), (cS 4 5, 1), (cS 4 6, 1), (cR 5, 1), (cR 6, 1)]), .leaf (2, [(cS 4 3, 1), (cS 5 3, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)], [(cS 0 3, 1), (cS 4 1, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 6 5, 1), (cR 5, 1), (cR 6, 1)]), .leaf (16, [(cS 0 0, 1), (cS 0 4, 1), (cS 0 6, 2), (cS 4 3, 6), (cS 5 3, 10), (cR 0, 5), (cR 1, 10), (cR 2, 6), (cR 3, 10)], [(cS 0 2, 4), (cS 0 3, 12), (cS 0 4, 4), (cS 0 5, 2), (cS 4 1, 6), (cS 4 5, 9), (cS 4 6, 7), (cS 5 1, 3), (cS 5 6, 2), (cS 6 0, 3), (cS 6 1, 7), (cS 6 5, 10), (cS 6 6, 5), (cR 5, 7)]), .leaf (16, [(cS 0 0, 1), (cS 0 4, 1), (cS 0 6, 1), (cS 4 2, 3), (cS 4 3, 4), (cS 4 4, 3), (cS 5 3, 9), (cR 0, 6), (cR 1, 9), (cR 2, 7), (cR 3, 9)], [(cS 0 1, 3), (cS 0 2, 13), (cS 0 3, 3), (cS 4 0, 3), (cS 4 1, 4), (cS 4 5, 13), (cS 4 6, 4), (cS 5 0, 1), (cS 5 1, 9), (cS 5 2, 3), (cS 5 6, 8), (cS 6 0, 2), (cS 6 4, 9), (cS 6 5, 3), (cS 6 6, 2), (cR 6, 4)]), .leaf (16, [(cS 0 0, 1), (cS 0 4, 1), (cS 0 6, 2), (cS 4 3, 6), (cS 5 3, 10), (cR 0, 5), (cR 1, 10), (cR 2, 6), (cR 3, 10)], [(cS 0 2, 4), (cS 0 3, 12), (cS 0 4, 4), (cS 0 5, 2), (cS 4 1, 6), (cS 4 5, 9), (cS 4 6, 7), (cS 5 1, 3), (cS 5 6, 2), (cS 6 0, 3), (cS 6 1, 7), (cS 6 5, 10), (cS 6 6, 5), (cR 5, 7)]), .leaf (2, [(cS 4 3, 1), (cS 5 3, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)], [(cS 0 3, 1), (cS 4 1, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 6 5, 1), (cR 5, 1), (cR 6, 1)])],
  .root (1, [(cR 4, 1), (cR 6, 1)], [(cR 0, 1), (cR 2, 1)]),
  .root (60, [(cS 0 3, 7), (cS 0 5, 7), (cS 2 0, 16), (cS 2 1, 18), (cS 3 0, 8), (cS 3 1, 25), (cS 3 2, 17), (cS 3 6, 18), (cS 4 0, 9), (cS 4 5, 7), (cS 4 6, 8), (cS 5 1, 33), (cS 6 4, 35), (cS 6 6, 17), (cR 4, 18), (cR 5, 9), (cR 6, 18), (cC 6, 18)], [(cS 0 0, 8), (cS 0 1, 8), (cS 1 5, 8), (cS 2 2, 34), (cS 2 4, 25), (cS 2 5, 26), (cS 3 3, 17), (cS 3 4, 9), (cS 4 4, 26), (cS 5 3, 25), (cS 6 2, 26), (cR 0, 26), (cR 1, 26), (cC 3, 9)]),
  .root (6, [(cS 2 1, 2), (cS 3 0, 2), (cS 3 1, 2), (cS 3 2, 2), (cS 4 3, 2), (cS 4 4, 2), (cS 5 0, 2), (cS 5 1, 2), (cS 5 2, 2), (cS 6 3, 2), (cS 6 4, 2), (cS 6 5, 2), (cS 6 6, 2), (cR 4, 2), (cR 6, 2)], [(cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 2 3, 2), (cS 2 4, 1), (cS 2 6, 1), (cS 3 5, 2), (cS 4 5, 2), (cS 4 6, 2), (cR 0, 4), (cR 2, 3)]),
  .root (40, [(cS 2 0, 8), (cS 2 1, 23), (cS 3 0, 14), (cS 3 1, 17), (cS 4 3, 13), (cS 4 4, 18), (cS 4 5, 13), (cS 5 0, 13), (cS 6 3, 13), (cS 6 4, 18), (cS 6 5, 13), (cR 4, 9), (cR 6, 9), (cC 6, 18)], [(cS 0 0, 3), (cS 0 1, 5), (cS 1 4, 3), (cS 1 5, 5), (cS 1 6, 5), (cS 2 2, 3), (cS 2 3, 18), (cS 2 4, 17), (cS 2 5, 23), (cS 3 2, 9), (cS 5 1, 18), (cS 5 2, 17), (cS 6 2, 13), (cR 0, 23), (cR 1, 9), (cC 2, 5), (cC 3, 5)]),
  .root (2, [(cS 0 4, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 6 4, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1)], [(cS 2 3, 1), (cS 2 5, 1), (cS 3 3, 1), (cS 6 0, 1), (cS 6 2, 1), (cS 6 6, 1), (cR 0, 1), (cR 1, 1)]),
  .splitS0 [.leaf (10, [(cS 0 3, 1), (cS 0 5, 1), (cS 1 4, 3), (cS 1 6, 2), (cS 2 5, 1), (cS 3 5, 2), (cS 4 1, 6), (cS 4 6, 2), (cS 5 1, 2), (cS 6 1, 4), (cS 6 3, 1), (cR 5, 2), (cR 6, 2), (cC 4, 6), (cC 5, 1), (cC 6, 6)], [(cS 0 0, 4), (cS 0 2, 5), (cS 1 0, 6), (cS 1 2, 3), (cS 2 0, 4), (cS 2 1, 1), (cS 2 2, 4), (cS 2 3, 1), (cS 3 0, 2), (cS 3 1, 3), (cS 3 3, 3), (cS 4 3, 6), (cS 4 4, 1), (cS 6 2, 3), (cC 2, 2)]), .leaf (20, [(cS 0 4, 7), (cS 0 6, 4), (cS 1 3, 3), (cS 1 4, 2), (cS 1 5, 5), (cS 2 5, 4), (cS 3 5, 6), (cS 4 0, 1), (cS 4 1, 13), (cS 4 6, 4), (cS 5 2, 1), (cS 5 4, 1), (cS 6 1, 9), (cR 5, 6), (cR 6, 5), (cC 4, 8), (cC 5, 2), (cC 6, 9)], [(cS 0 0, 6), (cS 0 2, 12), (cS 1 0, 14), (cS 2 0, 6), (cS 2 1, 8), (cS 2 2, 4), (cS 2 3, 8), (cS 3 0, 6), (cS 3 3, 10), (cS 3 4, 2), (cS 4 3, 5), (cS 4 4, 3), (cC 2, 8)]), .leaf (2, [(cS 0 4, 1), (cS 0 6, 1), (cS 1 4, 1), (cS 2 5, 1), (cS 3 5, 1), (cS 4 1, 1), (cS 6 1, 1), (cS 6 4, 1), (cR 5, 1), (cC 6, 1)], [(cS 0 0, 1), (cS 0 2, 1), (cS 1 0, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 3, 1), (cS 4 4, 1), (cC 2, 1)]), .leaf (5, [(cS 0 4, 1), (cS 0 6, 1), (cS 1 3, 1), (cS 1 5, 1), (cS 2 5, 1), (cS 3 5, 1), (cS 4 1, 3), (cS 4 6, 1), (cS 5 1, 1), (cS 6 1, 2), (cR 5, 1), (cR 6, 1), (cC 4, 3), (cC 6, 3)], [(cS 0 0, 2), (cS 0 2, 3), (cS 1 0, 3), (cS 1 2, 1), (cS 2 0, 2), (cS 2 1, 1), (cS 2 2, 2), (cS 2 3, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 4 3, 3), (cS 4 4, 1), (cS 5 3, 1), (cS 6 2, 1), (cC 2, 1)]), .leaf (12, [(cS 0 3, 5), (cS 0 4, 1), (cS 0 5, 5), (cS 1 4, 4), (cS 1 5, 1), (cS 1 6, 3), (cS 2 5, 5), (cS 3 5, 5), (cS 4 1, 4), (cS 4 6, 4), (cS 5 1, 3), (cS 5 4, 1), (cR 5, 5), (cR 6, 4), (cC 4, 2), (cC 6, 3)], [(cS 0 0, 12), (cS 0 2, 9), (cS 1 1, 3), (cS 2 0, 6), (cS 2 1, 3), (cS 2 2, 3), (cS 2 3, 6), (cS 3 0, 3), (cS 3 1, 3), (cS 3 3, 5), (cS 3 4, 1), (cS 4 3, 2), (cS 4 4, 2), (cR 4, 2), (cC 2, 3)])],
  .root (24, [(cS 0 4, 3), (cS 0 6, 2), (cS 1 5, 17), (cS 2 5, 2), (cS 3 3, 2), (cS 4 2, 6), (cS 4 3, 5), (cS 4 4, 1), (cS 5 0, 4), (cS 5 1, 8), (cS 6 3, 5), (cS 6 5, 3), (cS 6 6, 8), (cR 4, 8), (cR 5, 4), (cR 6, 8), (cC 3, 3), (cC 4, 5), (cC 5, 5)], [(cS 0 0, 7), (cS 0 1, 9), (cS 0 2, 9), (cS 0 3, 9), (cS 1 0, 13), (cS 1 2, 2), (cS 2 2, 10), (cS 2 3, 6), (cS 3 0, 5), (cS 3 1, 11), (cS 3 5, 4), (cS 3 6, 12), (cS 4 5, 1), (cS 4 6, 8), (cS 6 2, 6), (cR 1, 4), (cR 2, 8)]),
  .root (1, [(cC 4, 1), (cC 6, 1)], [(cC 0, 1), (cC 2, 1)]),
  .root (5, [(cS 1 5, 2), (cS 3 5, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 2, 2), (cS 4 4, 1), (cS 5 2, 2), (cS 6 4, 1), (cC 3, 3), (cC 4, 1), (cC 5, 3)], [(cS 0 2, 3), (cS 0 3, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 2 0, 1), (cS 2 2, 3), (cS 2 3, 1), (cS 4 6, 1), (cS 5 6, 1), (cS 6 1, 1), (cS 6 6, 1), (cC 0, 3), (cC 1, 1), (cC 2, 1)]),
  .root (5, [(cS 0 3, 1), (cS 0 4, 1), (cS 1 4, 3), (cS 1 5, 2), (cS 2 1, 1), (cS 3 0, 1), (cS 3 1, 2), (cS 4 0, 1), (cS 4 2, 2), (cS 5 1, 2), (cS 5 3, 1), (cS 6 4, 2), (cS 6 5, 1), (cR 5, 1), (cR 6, 1), (cC 1, 1), (cC 6, 3)], [(cS 0 0, 3), (cS 0 2, 3), (cS 1 0, 2), (cS 1 2, 2), (cS 2 3, 2), (cS 3 3, 2), (cS 3 5, 4), (cS 4 3, 1), (cS 4 4, 2), (cS 4 5, 1), (cS 5 4, 2), (cS 6 2, 2), (cR 2, 1)]),
  .root (2, [(cS 0 3, 1), (cS 0 5, 1), (cS 1 4, 1), (cS 2 1, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 4 1, 1), (cS 5 4, 1), (cS 5 6, 1), (cS 6 4, 1), (cC 6, 1)], [(cS 0 0, 1), (cS 0 2, 1), (cS 1 0, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 4 4, 1), (cS 5 1, 1), (cS 5 3, 1), (cS 6 0, 1), (cC 2, 1)]),
  .splitS0 [.leaf (8, [(cS 0 4, 2), (cS 0 6, 3), (cS 1 3, 2), (cS 1 4, 2), (cS 1 5, 1), (cS 2 0, 2), (cS 2 1, 2), (cS 2 5, 3), (cS 3 0, 1), (cS 3 1, 2), (cS 3 5, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 4 1, 3), (cS 4 2, 2), (cS 4 6, 1), (cS 5 1, 4), (cS 5 2, 4), (cS 5 4, 2), (cS 6 3, 1), (cS 6 4, 3), (cR 3, 1), (cC 4, 2), (cC 5, 1), (cC 6, 3)], [(cS 0 0, 4), (cS 0 2, 5), (cS 1 0, 4), (cS 1 2, 3), (cS 2 2, 3), (cS 2 3, 2), (cS 3 3, 3), (cS 4 3, 2), (cS 4 4, 3), (cS 5 6, 3), (cS 6 0, 4), (cS 6 2, 3), (cS 6 6, 1)]), .leaf (20, [(cS 0 4, 5), (cS 0 5, 5), (cS 1 3, 6), (cS 1 5, 3), (cS 2 0, 4), (cS 2 1, 6), (cS 2 5, 5), (cS 3 0, 4), (cS 3 1, 6), (cS 3 5, 3), (cS 3 6, 3), (cS 4 0, 1), (cS 4 1, 9), (cS 4 2, 5), (cS 4 6, 3), (cS 5 1, 8), (cS 5 2, 12), (cS 5 4, 5), (cS 6 3, 3), (cS 6 4, 3), (cC 4, 9), (cC 5, 3), (cC 6, 9)], [(cS 0 0, 10), (cS 0 2, 14), (cS 1 0, 10), (cS 1 2, 6), (cS 2 2, 8), (cS 2 3, 6), (cS 3 3, 12), (cS 3 4, 2), (cS 4 3, 3), (cS 4 4, 3), (cS 5 0, 2), (cS 5 6, 5), (cS 6 0, 10), (cS 6 2, 6), (cS 6 6, 3)]), .leaf (4, [(cS 0 4, 2), (cS 0 5, 2), (cS 1 4, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 2 5, 2), (cS 3 0, 1), (cS 3 1, 1), (cS 3 5, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 4 6, 1), (cS 5 1, 1), (cS 5 2, 3), (cS 5 4, 2), (cS 6 4, 2), (cR 1, 1), (cR 3, 1), (cC 6, 1)], [(cS 0 0, 3), (cS 0 2, 3), (cS 1 0, 1), (cS 1 2, 1), (cS 2 2, 1), (cS 2 3, 2), (cS 3 3, 2), (cS 4 4, 2), (cS 5 0, 2), (cS 5 6, 2), (cR 6, 1)]), .leaf (30, [(cS 0 3, 6), (cS 0 5, 6), (cS 1 3, 10), (cS 1 5, 7), (cS 2 0, 6), (cS 2 1, 7), (cS 2 5, 6), (cS 3 0, 3), (cS 3 1, 7), (cS 4 1, 16), (cS 4 6, 6), (cS 5 1, 8), (cS 5 2, 19), (cS 5 4, 3), (cS 6 3, 3), (cS 6 4, 7), (cR 3, 7), (cR 5, 3), (cC 4, 14), (cC 5, 3), (cC 6, 14)], [(cS 0 0, 13), (cS 0 2, 27), (cS 1 0, 17), (cS 1 2, 3), (cS 2 2, 20), (cS 2 3, 7), (cS 3 3, 3), (cS 4 3, 20), (cS 4 4, 7), (cS 5 0, 3), (cS 5 3, 3), (cS 5 6, 4), (cS 6 0, 17), (cS 6 2, 3), (cS 6 6, 7)])],
  .root (8, [(cS 1 5, 2), (cS 1 6, 2), (cS 2 1, 1), (cS 3 0, 2), (cS 3 1, 5), (cS 4 3, 4), (cS 4 4, 2), (cS 5 0, 4), (cS 6 3, 4), (cS 6 4, 2), (cS 6 6, 4), (cC 4, 2), (cC 5, 4)], [(cS 0 0, 6), (cS 0 1, 1), (cS 0 3, 4), (cS 1 0, 2), (cS 1 1, 5), (cS 1 3, 2), (cS 2 3, 4), (cS 2 6, 4), (cS 3 3, 2), (cS 3 5, 2), (cS 3 6, 2), (cS 4 1, 1), (cS 4 6, 4), (cS 5 1, 3), (cS 5 2, 2), (cS 6 1, 1), (cS 6 2, 4), (cC 2, 2)]),
  .root (2, [(cS 1 5, 1), (cS 1 6, 1), (cS 2 0, 1), (cS 3 1, 1), (cS 4 0, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 5 2, 1), (cS 6 3, 1), (cS 6 5, 1), (cC 4, 1)], [(cS 0 0, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 0 6, 1), (cS 1 1, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 5 6, 1), (cS 6 1, 1)]),
  .root (5, [(cS 1 5, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 3 0, 2), (cS 3 1, 1), (cS 3 5, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 6 3, 1), (cS 6 4, 1), (cC 4, 3), (cC 5, 1), (cC 6, 3)], [(cS 0 0, 2), (cS 1 0, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 4 1, 1), (cS 5 0, 3), (cS 5 2, 1), (cS 5 6, 1), (cS 6 0, 1), (cS 6 2, 1), (cR 0, 1), (cC 0, 1), (cC 2, 3)]),
  .root (24, [(cS 0 4, 2), (cS 1 3, 3), (cS 2 2, 9), (cS 2 3, 12), (cS 2 4, 9), (cS 4 1, 7), (cS 4 2, 7), (cS 4 5, 6), (cS 4 6, 10), (cS 5 0, 7), (cS 5 1, 4), (cS 6 3, 4), (cS 6 4, 7), (cS 6 5, 8), (cS 6 6, 3), (cR 3, 3), (cR 4, 3), (cR 5, 3), (cR 6, 11), (cC 6, 2)], [(cS 0 0, 1), (cS 0 2, 5), (cS 1 0, 4), (cS 1 5, 5), (cS 2 0, 5), (cS 2 1, 8), (cS 2 5, 12), (cS 2 6, 8), (cS 3 0, 7), (cS 3 1, 4), (cS 4 3, 12), (cS 4 4, 12), (cS 6 2, 7), (cR 0, 12), (cR 1, 7)]),
  .root (24, [(cS 2 2, 10), (cS 2 3, 12), (cS 3 2, 3), (cS 4 1, 5), (cS 4 2, 8), (cS 4 4, 4), (cS 5 0, 5), (cS 5 1, 6), (cS 5 2, 2), (cS 6 5, 4), (cS 6 6, 6), (cR 4, 8), (cR 6, 14), (cC 3, 6), (cC 4, 6)], [(cS 0 2, 10), (cS 1 0, 10), (cS 1 5, 4), (cS 3 0, 13), (cS 3 5, 7), (cS 4 6, 11), (cS 6 2, 3), (cR 0, 11), (cR 1, 3), (cR 2, 11), (cC 5, 6)]),
  .root (24, [(cS 2 2, 2), (cS 2 3, 11), (cS 4 4, 10), (cS 4 6, 13), (cS 5 0, 11), (cS 6 4, 4), (cS 6 6, 7), (cR 6, 6), (cC 3, 11), (cC 4, 3), (cC 5, 11)], [(cS 0 0, 4), (cS 1 5, 12), (cS 2 0, 7), (cS 2 1, 3), (cS 2 5, 10), (cS 2 6, 3), (cS 3 0, 6), (cS 3 1, 5), (cS 4 1, 5), (cS 5 2, 5), (cS 6 2, 5), (cR 0, 6), (cR 1, 6), (cC 0, 8), (cC 2, 14)]),
  .root (8, [(cS 2 2, 3), (cS 2 3, 2), (cS 3 2, 1), (cS 3 5, 1), (cS 3 6, 2), (cS 4 2, 1), (cS 4 5, 2), (cS 5 1, 3), (cS 5 2, 1), (cS 6 4, 2), (cS 6 5, 4), (cR 4, 3), (cC 3, 3), (cC 4, 3)], [(cS 0 2, 1), (cS 1 2, 1), (cS 1 5, 2), (cS 2 0, 2), (cS 2 1, 1), (cS 2 5, 4), (cS 2 6, 1), (cS 3 1, 3), (cS 5 6, 3), (cS 6 0, 1), (cS 6 1, 1), (cS 6 2, 4), (cS 6 6, 1), (cR 0, 3), (cR 1, 3), (cC 0, 3)]),
  .root (3, [(cS 2 2, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 5 0, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 2, 1), (cR 6, 1), (cC 1, 1), (cC 3, 1), (cC 6, 1)], [(cS 1 0, 1), (cS 1 5, 1), (cS 2 5, 2), (cS 3 5, 1), (cS 4 3, 1), (cS 4 4, 2), (cS 4 5, 1), (cS 4 6, 1), (cS 6 2, 1), (cR 0, 2)]),
  .root (4, [(cS 1 2, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 4 5, 2), (cS 4 6, 2), (cS 5 0, 2), (cS 6 1, 2), (cS 6 4, 3), (cS 6 5, 2), (cS 6 6, 2), (cR 2, 2), (cC 4, 1)], [(cS 0 0, 1), (cS 1 5, 1), (cS 2 5, 1), (cS 4 1, 2), (cS 4 2, 1), (cS 4 3, 3), (cS 4 4, 1), (cS 5 2, 1), (cS 6 2, 3), (cR 0, 1), (cR 1, 2)]),
  .root (10, [(cS 0 4, 2), (cS 1 2, 2), (cS 1 3, 2), (cS 2 1, 2), (cS 2 2, 1), (cS 2 3, 3), (cS 2 4, 1), (cS 3 0, 3), (cS 3 6, 1), (cS 4 1, 4), (cS 4 2, 3), (cS 4 5, 3), (cS 4 6, 4), (cS 6 3, 3), (cS 6 4, 5), (cS 6 5, 3), (cR 2, 4), (cR 3, 2), (cR 5, 2), (cC 1, 1)], [(cS 0 0, 1), (cS 0 1, 2), (cS 0 2, 2), (cS 0 3, 1), (cS 1 0, 4), (cS 1 4, 2), (cS 1 5, 5), (cS 1 6, 2), (cS 2 5, 3), (cS 4 3, 5), (cS 4 4, 5), (cS 5 0, 3), (cS 5 6, 1), (cS 6 0, 2), (cS 6 1, 2), (cS 6 2, 5), (cS 6 6, 4), (cR 0, 3)]),
  .splitS0 [.leaf (4, [(cS 1 1, 2), (cS 1 2, 1), (cS 2 2, 1), (cS 3 0, 1), (cS 3 1, 2), (cS 3 2, 1), (cS 4 6, 2), (cS 5 0, 1), (cS 6 5, 2), (cS 6 6, 2), (cC 0, 1), (cC 3, 2), (cC 4, 2)], [(cS 0 0, 3), (cS 0 2, 1), (cS 1 0, 1), (cS 1 5, 4), (cS 2 6, 2), (cS 3 5, 2), (cS 4 2, 1), (cS 4 5, 2), (cS 5 1, 2), (cS 5 2, 1), (cS 6 2, 3)]), .leaf (16, [(cS 0 5, 4), (cS 0 6, 2), (cS 1 1, 1), (cS 1 2, 3), (cS 2 0, 1), (cS 2 1, 4), (cS 2 2, 8), (cS 2 3, 1), (cS 3 0, 6), (cS 3 1, 5), (cS 4 3, 1), (cS 5 0, 4), (cS 5 5, 3), (cS 5 6, 4), (cS 6 0, 2), (cS 6 4, 1), (cS 6 5, 4), (cS 6 6, 6), (cC 3, 7), (cC 4, 8)], [(cS 0 0, 3), (cS 0 1, 6), (cS 0 2, 6), (cS 0 3, 1), (cS 1 0, 4), (cS 1 5, 4), (cS 1 6, 6), (cS 2 0, 3), (cS 2 5, 12), (cS 3 5, 4), (cS 3 6, 3), (cS 4 1, 4), (cS 4 2, 8), (cS 4 5, 5), (cS 4 6, 5), (cS 5 1, 5), (cS 6 1, 2), (cS 6 2, 9), (cC 0, 3)]), .leaf (12, [(cS 0 5, 1), (cS 0 6, 2), (cS 1 2, 4), (cS 2 0, 2), (cS 2 1, 4), (cS 2 2, 4), (cS 3 0, 3), (cS 3 1, 3), (cS 3 2, 2), (cS 5 0, 3), (cS 5 6, 4), (cS 6 0, 2), (cS 6 5, 6), (cS 6 6, 3), (cC 3, 6), (cC 4, 6)], [(cS 0 0, 1), (cS 0 1, 5), (cS 0 2, 3), (cS 1 0, 4), (cS 1 5, 5), (cS 1 6, 5), (cS 2 5, 7), (cS 2 6, 1), (cS 3 6, 4), (cS 4 1, 4), (cS 4 2, 4), (cS 4 5, 6), (cS 4 6, 3), (cS 5 1, 3), (cS 5 2, 2), (cS 6 0, 2), (cS 6 2, 7), (cS 6 3, 3), (cC 0, 2)]), .leaf (4, [(cS 0 5, 1), (cS 0 6, 2), (cS 2 1, 2), (cS 2 2, 2), (cS 3 0, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 5 6, 2), (cS 6 5, 1), (cC 0, 1), (cC 3, 2), (cC 4, 2)], [(cS 0 0, 1), (cS 0 2, 2), (cS 1 0, 2), (cS 2 5, 3), (cS 3 5, 1), (cS 3 6, 2), (cS 4 1, 2), (cS 4 2, 1), (cS 4 5, 1), (cS 6 1, 2), (cS 6 2, 1), (cR 1, 1), (cC 2, 1)])],
  .root (24, [(cS 2 1, 13), (cS 2 3, 10), (cS 2 6, 2), (cS 3 0, 11), (cS 4 1, 13), (cS 4 3, 10), (cS 5 2, 4), (cS 6 4, 10), (cS 6 5, 3), (cC 2, 11), (cC 3, 3), (cC 4, 11)], [(cS 0 2, 12), (cS 1 0, 5), (cS 2 5, 4), (cS 3 5, 6), (cS 4 6, 2), (cS 5 0, 5), (cS 5 6, 6), (cS 6 0, 8), (cS 6 1, 3), (cS 6 2, 6), (cR 0, 6), (cR 1, 6), (cC 0, 8), (cC 5, 14), (cC 6, 3)]),
  .root (24, [(cS 1 3, 1), (cS 2 1, 4), (cS 2 2, 6), (cS 3 0, 3), (cS 3 6, 4), (cS 4 3, 7), (cS 4 5, 7), (cS 4 6, 6), (cS 5 5, 3), (cS 6 4, 15), (cS 6 5, 3), (cR 2, 14), (cR 3, 3), (cR 4, 8), (cC 3, 3), (cC 4, 6)], [(cS 0 0, 10), (cS 0 2, 10), (cS 1 5, 10), (cS 2 5, 3), (cS 4 1, 10), (cS 4 2, 3), (cS 5 0, 11), (cS 5 1, 3), (cS 5 2, 8), (cS 6 2, 2), (cS 6 3, 3), (cS 6 5, 4), (cS 6 6, 3), (cR 0, 3), (cR 1, 11), (cR 6, 11)]),
  .splitS0 [.leaf (6, [(cS 0 3, 2), (cS 0 5, 2), (cS 1 3, 1), (cS 1 4, 1), (cS 1 5, 3), (cS 2 2, 1), (cS 2 3, 2), (cS 2 5, 2), (cS 3 3, 2), (cS 4 1, 2), (cS 5 0, 1), (cS 6 0, 1), (cS 6 4, 2), (cS 6 5, 1), (cS 6 6, 2), (cR 5, 2), (cC 1, 2), (cC 3, 2), (cC 5, 1)], [(cS 0 0, 3), (cS 0 2, 4), (cS 1 0, 3), (cS 2 0, 3), (cS 2 1, 3), (cS 3 4, 3), (cS 3 6, 3), (cS 4 4, 1), (cS 4 6, 1), (cS 6 2, 2), (cR 4, 2)]), .leaf (5, [(cS 0 3, 1), (cS 0 4, 2), (cS 0 5, 1), (cS 1 5, 4), (cS 2 3, 3), (cS 4 1, 1), (cS 4 2, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 4, 2), (cS 6 0, 1), (cS 6 5, 1), (cS 6 6, 2), (cR 5, 1), (cC 1, 1), (cC 3, 2), (cC 5, 1)], [(cS 0 0, 3), (cS 0 2, 3), (cS 1 0, 2), (cS 1 1, 1), (cS 2 1, 3), (cS 2 6, 3), (cS 3 0, 1), (cS 3 4, 3), (cS 3 5, 1), (cS 4 6, 2), (cS 6 2, 2), (cR 3, 1), (cR 4, 1)]), .leaf (2, [(cS 0 4, 1), (cS 0 5, 1), (cS 1 3, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 2 5, 1), (cS 3 3, 1), (cS 4 1, 1), (cR 5, 1), (cR 6, 1)], [(cS 0 0, 1), (cS 0 2, 2), (cS 1 0, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 3 6, 1), (cS 4 4, 1), (cR 4, 1)])],
  .root (5, [(cS 0 3, 1), (cS 0 5, 1), (cS 1 1, 1), (cS 1 2, 1), (cS 1 4, 1), (cS 2 2, 2), (cS 2 3, 1), (cS 2 5, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 5 0, 1), (cS 5 4, 1), (cS 5 6, 1), (cS 6 4, 1), (cC 3, 1), (cC 4, 2), (cC 5, 1), (cC 6, 3)], [(cS 0 0, 1), (cS 0 2, 2), (cS 1 0, 2), (cS 2 0, 1), (cS 3 1, 2), (cS 4 1, 2), (cS 4 3, 4), (cS 4 4, 1), (cS 5 2, 2), (cS 6 0, 2), (cS 6 2, 2), (cC 0, 2), (cC 2, 1)]),
  .root (5, [(cS 1 3, 1), (cS 1 5, 3), (cS 2 2, 2), (cS 2 3, 1), (cS 3 5, 1), (cS 3 6, 2), (cS 4 1, 4), (cS 5 1, 1), (cS 6 4, 1), (cC 3, 2), (cC 4, 2), (cC 5, 2)], [(cS 0 1, 2), (cS 0 2, 2), (cS 0 6, 1), (cS 1 0, 1), (cS 2 0, 1), (cS 2 1, 2), (cS 4 3, 4), (cS 4 4, 1), (cS 5 0, 1), (cS 5 6, 1), (cS 6 0, 1), (cS 6 2, 3), (cC 0, 1), (cC 1, 1), (cC 6, 2)]),
  .root (24, [(cS 0 4, 3), (cS 0 6, 1), (cS 1 3, 4), (cS 1 5, 6), (cS 1 6, 2), (cS 2 2, 1), (cS 2 3, 4), (cS 2 5, 1), (cS 3 3, 4), (cS 4 4, 3), (cS 5 0, 7), (cS 5 4, 4), (cS 5 6, 2), (cS 6 0, 7), (cS 6 4, 4), (cS 6 6, 8), (cC 3, 15), (cC 4, 2), (cC 5, 15)], [(cS 0 0, 7), (cS 0 2, 8), (cS 1 0, 10), (cS 1 2, 10), (cS 2 1, 4), (cS 2 6, 7), (cS 3 1, 10), (cS 3 5, 7), (cS 3 6, 10), (cS 4 1, 7), (cS 4 6, 8), (cS 5 2, 8), (cS 6 2, 7), (cS 6 3, 3), (cC 0, 7), (cC 1, 3), (cC 2, 6)]),
  .root (2, [(cS 1 5, 2), (cS 2 2, 1), (cS 4 2, 1), (cS 5 2, 1), (cS 6 5, 1), (cC 3, 1), (cC 4, 1)], [(cS 0 2, 2), (cS 3 5, 1), (cS 4 5, 1), (cC 0, 1), (cC 1, 1), (cC 6, 1)]),
  .root (1, [(cC 3, 1), (cC 5, 1)], [(cC 0, 1), (cC 2, 1)]),
  .splitS0 [.leaf (8, [(cS 0 3, 3), (cS 0 5, 1), (cS 1 1, 2), (cS 1 2, 1), (cS 1 4, 1), (cS 1 5, 2), (cS 2 2, 1), (cS 2 3, 3), (cS 3 0, 2), (cS 3 1, 4), (cS 3 2, 1), (cS 3 3, 2), (cS 5 0, 2), (cS 5 4, 3), (cS 5 6, 1), (cS 6 4, 3), (cS 6 5, 2), (cS 6 6, 2), (cR 1, 2), (cR 2, 1), (cC 1, 1), (cC 4, 2), (cC 6, 3)], [(cS 0 0, 6), (cS 0 2, 2), (cS 1 0, 1), (cS 3 4, 2), (cS 3 5, 3), (cS 3 6, 1), (cS 4 2, 2), (cS 4 3, 6), (cS 4 5, 3), (cS 4 6, 1), (cS 5 1, 4), (cS 5 2, 2), (cS 6 2, 6), (cC 0, 1)]), .leaf (40, [(cS 0 3, 15), (cS 0 4, 6), (cS 0 5, 10), (cS 1 1, 10), (cS 1 2, 10), (cS 1 4, 17), (cS 1 5, 11), (cS 2 1, 2), (cS 2 2, 1), (cS 2 3, 18), (cS 3 0, 1), (cS 3 1, 20), (cS 3 3, 10), (cS 4 6, 4), (cS 5 0, 11), (cS 5 4, 21), (cS 5 5, 11), (cS 6 0, 4), (cS 6 4, 17), (cS 6 5, 5), (cS 6 6, 6), (cR 2, 11), (cC 1, 6), (cC 4, 2), (cC 6, 19)], [(cS 0 0, 30), (cS 0 2, 15), (cS 1 0, 11), (cS 2 5, 4), (cS 3 4, 2), (cS 3 5, 26), (cS 3 6, 2), (cS 4 3, 26), (cS 5 1, 19), (cS 5 2, 15), (cS 6 2, 25), (cR 3, 8), (cR 4, 6)]), .leaf (4, [(cS 0 3, 1), (cS 0 5, 1), (cS 5 4, 1), (cS 5 6, 1), (cS 6 4, 3), (cS 6 6, 3), (cR 1, 3), (cR 2, 1), (cR 3, 3)], [(cS 0 0, 4), (cS 0 2, 1), (cS 4 3, 3), (cS 4 5, 3), (cS 5 0, 2), (cS 5 1, 2), (cS 5 2, 1), (cS 6 2, 3), (cR 4, 1)])],
  .root (2, [(cS 0 5, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 4 2, 1), (cS 5 1, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 1, 1), (cR 2, 1), (cC 3, 1)], [(cS 0 0, 2), (cS 0 2, 1), (cS 3 5, 2), (cS 4 4, 2), (cS 4 6, 1), (cS 5 0, 1), (cS 5 6, 1), (cS 6 2, 1)]),
  .root (20, [(cS 0 3, 6), (cS 0 5, 1), (cS 2 1, 3), (cS 2 2, 5), (cS 2 3, 3), (cS 3 0, 5), (cS 4 6, 1), (cS 5 4, 6), (cS 6 4, 9), (cR 1, 9), (cR 2, 3), (cR 3, 9), (cC 4, 5), (cC 5, 5), (cC 6, 5)], [(cS 0 0, 8), (cS 0 1, 7), (cS 0 2, 5), (cS 0 6, 7), (cS 1 0, 5), (cS 4 1, 6), (cS 4 2, 5), (cS 4 3, 15), (cS 4 4, 5), (cS 5 0, 11), (cS 5 1, 4), (cS 5 2, 5), (cS 5 6, 9), (cS 6 0, 2), (cS 6 1, 3), (cS 6 2, 15), (cS 6 6, 3)]),
  .root (3, [(cS 0 5, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 1, 2), (cS 2 2, 1), (cS 2 5, 1), (cS 3 1, 1), (cS 6 5, 2), (cC 3, 2), (cC 4, 1)], [(cS 0 0, 2), (cS 0 2, 3), (cS 1 0, 1), (cS 2 6, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 2, 1), (cS 6 0, 1), (cS 6 2, 1), (cR 3, 1), (cR 5, 1)]),
  .root (6, [(cS 0 0, 4), (cS 0 5, 2), (cS 1 0, 2), (cS 3 6, 2), (cS 4 1, 1), (cS 4 6, 3), (cS 5 1, 2), (cS 6 4, 4), (cS 6 6, 2), (cR 4, 1), (cR 5, 2), (cR 6, 2)], [(cS 0 2, 2), (cS 1 5, 2), (cS 2 2, 2), (cS 3 1, 2), (cS 4 3, 3), (cS 4 4, 1), (cS 6 2, 2), (cR 0, 2), (cR 1, 2), (cR 2, 2), (cR 3, 2), (cC 4, 2)]),
  .root (5, [(cS 0 0, 5), (cS 4 2, 1), (cS 4 3, 3), (cS 4 4, 1), (cS 4 5, 2), (cS 5 0, 2), (cS 5 1, 3), (cS 6 3, 2), (cS 6 4, 3), (cS 6 5, 2), (cS 6 6, 3), (cR 4, 1)], [(cS 4 0, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 6 2, 3), (cR 0, 2), (cR 1, 3), (cR 2, 2), (cR 3, 3)]),
  .root (4, [(cS 0 0, 4), (cS 4 3, 2), (cS 4 4, 2), (cS 4 5, 2), (cS 4 6, 2), (cS 5 0, 2), (cS 6 3, 2), (cS 6 4, 2), (cS 6 5, 2), (cS 6 6, 2)], [(cS 0 2, 1), (cS 0 3, 1), (cS 0 5, 1), (cS 4 1, 1), (cS 5 1, 1), (cS 5 2, 2), (cS 6 1, 1), (cS 6 2, 2), (cR 1, 3), (cR 2, 1), (cR 3, 3)]),
  .root (6, [(cS 0 0, 5), (cS 1 0, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 2, 1), (cS 4 3, 3), (cS 4 4, 1), (cS 4 5, 2), (cS 5 1, 2), (cS 5 2, 1), (cS 5 5, 1), (cS 6 3, 2), (cS 6 4, 4), (cS 6 5, 2), (cR 4, 2)], [(cS 0 2, 1), (cS 1 3, 1), (cS 1 5, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 5 0, 4), (cS 5 6, 1), (cS 6 2, 3), (cS 6 6, 2), (cR 0, 2), (cR 1, 3), (cR 2, 2), (cR 3, 2)]),
  .root (2, [(cS 0 6, 1), (cS 1 0, 1), (cS 2 0, 1), (cS 4 0, 1), (cS 4 2, 1), (cS 5 6, 1), (cS 6 4, 1), (cR 6, 1), (cC 1, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 3 6, 1), (cC 3, 1), (cC 4, 1), (cC 5, 1)]),
  .root (2, [(cS 1 1, 1), (cS 3 1, 1), (cS 4 5, 1), (cS 6 4, 1), (cR 6, 1), (cC 0, 1), (cC 6, 1)], [(cS 0 1, 1), (cS 0 6, 1), (cS 1 5, 1), (cS 2 5, 1), (cS 5 1, 1), (cC 2, 1), (cC 3, 1), (cC 4, 1)]),
  .root (10, [(cS 1 0, 8), (cS 2 1, 1), (cS 3 0, 4), (cS 3 1, 3), (cS 3 5, 1), (cS 3 6, 4), (cS 4 1, 1), (cS 4 2, 4), (cS 4 5, 3), (cS 5 1, 4), (cS 5 2, 3), (cS 6 4, 9), (cR 6, 1), (cC 1, 2), (cC 6, 2)], [(cS 0 1, 3), (cS 0 6, 1), (cS 1 2, 3), (cS 1 3, 2), (cS 1 4, 1), (cS 1 5, 5), (cS 2 2, 4), (cS 2 4, 4), (cS 2 5, 5), (cS 3 3, 3), (cS 4 4, 7), (cS 5 0, 3), (cS 5 6, 5), (cS 6 2, 3), (cS 6 6, 2), (cR 0, 4), (cC 3, 3)]),
  .splitS0 [.leaf (2, [(cS 0 5, 1), (cS 1 6, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 6, 1), (cS 6 4, 2), (cS 6 6, 1), (cC 0, 1), (cC 1, 1)], [(cS 0 2, 1), (cS 0 4, 2), (cS 2 3, 1), (cS 2 4, 1), (cS 2 5, 1), (cS 3 6, 1), (cS 4 5, 1), (cS 5 2, 1), (cC 2, 1)]), .leaf (4, [(cS 0 1, 1), (cS 0 4, 1), (cS 0 5, 1), (cS 1 1, 1), (cS 1 6, 2), (cS 2 1, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 3, 1), (cS 5 6, 1), (cS 6 4, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 6, 1), (cC 0, 2), (cC 4, 1)], [(cS 1 3, 2), (cS 1 5, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 2 5, 2), (cS 2 6, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 5, 2), (cS 4 6, 1), (cS 5 1, 1), (cS 6 2, 2), (cC 2, 2)]), .leaf (10, [(cS 0 0, 2), (cS 0 1, 2), (cS 0 4, 3), (cS 0 5, 2), (cS 1 1, 1), (cS 1 6, 5), (cS 2 0, 2), (cS 2 1, 2), (cS 3 1, 1), (cS 4 3, 5), (cS 4 4, 5), (cS 5 3, 1), (cS 5 4, 2), (cS 5 6, 2), (cS 6 3, 2), (cS 6 4, 4), (cS 6 5, 3), (cS 6 6, 4), (cR 6, 1), (cC 0, 3), (cC 1, 2)], [(cS 0 3, 5), (cS 1 2, 2), (cS 1 4, 2), (cS 1 5, 3), (cS 2 3, 5), (cS 2 4, 3), (cS 2 5, 4), (cS 2 6, 3), (cS 3 5, 1), (cS 4 1, 2), (cS 4 5, 3), (cS 4 6, 5), (cS 5 1, 4), (cS 5 2, 1), (cS 6 2, 2), (cR 3, 2), (cC 2, 3)]), .leaf (4, [(cS 1 6, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 4 3, 2), (cS 4 4, 2), (cS 5 3, 1), (cS 5 4, 1), (cS 5 6, 2), (cS 6 0, 1), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 2), (cR 0, 2), (cR 1, 1), (cC 0, 1)], [(cS 0 2, 2), (cS 1 2, 1), (cS 1 4, 1), (cS 2 3, 2), (cS 2 4, 1), (cS 2 5, 2), (cS 3 6, 1), (cS 4 1, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 1, 2), (cS 6 2, 1), (cR 3, 1), (cC 2, 1)]), .leaf (2, [(cS 0 5, 1), (cS 1 6, 1), (cS 4 3, 1), (cS 5 6, 1), (cS 6 4, 1), (cS 6 6, 1), (cC 0, 1), (cC 1, 1), (cC 4, 1)], [(cS 0 2, 1), (cS 1 4, 1), (cS 2 3, 1), (cS 2 5, 1), (cS 3 6, 1), (cS 4 5, 1), (cS 5 2, 1), (cC 2, 1)]), .leaf (3, [(cS 0 4, 1), (cS 3 3, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 4, 1), (cS 6 4, 2), (cS 6 6, 1), (cC 0, 1), (cC 1, 2), (cC 6, 2)], [(cS 0 3, 2), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 3, 2), (cS 3 5, 2), (cS 5 2, 2), (cC 2, 1), (cC 5, 1)])],
  .root (2, [(cS 1 0, 1), (cS 3 1, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 2, 1), (cS 6 4, 2), (cC 0, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 0 4, 1), (cS 1 2, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 5 0, 1), (cS 6 2, 1), (cC 5, 1), (cC 6, 1)]),
  .root (4, [(cS 0 0, 2), (cS 1 0, 2), (cS 2 0, 2), (cS 3 0, 1), (cS 3 1, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 3, 1), (cS 4 4, 3), (cS 4 6, 2), (cS 5 5, 1), (cS 6 4, 4)], [(cS 0 3, 1), (cS 0 5, 1), (cS 1 3, 1), (cS 1 5, 1), (cS 2 4, 1), (cS 2 5, 1), (cS 3 3, 2), (cS 5 0, 2), (cS 5 2, 1), (cS 6 2, 1), (cS 6 6, 2), (cR 1, 1), (cC 1, 2), (cC 2, 1), (cC 3, 1), (cC 5, 1)]),
  .splitS0 [.leaf (2, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 3, 1), (cS 0 5, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 5, 1), (cS 5 1, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 5, 1)], [(cS 0 2, 1), (cS 1 2, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 6 2, 1), (cR 3, 1), (cR 4, 1)]), .leaf (5, [(cS 0 0, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 5, 2), (cS 4 0, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 5 1, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 0, 2), (cR 1, 2), (cR 5, 2), (cR 6, 2)], [(cS 0 2, 4), (cS 2 1, 1), (cS 2 3, 2), (cS 3 0, 1), (cS 3 2, 1), (cS 3 6, 1), (cS 4 4, 3), (cS 4 5, 1), (cS 4 6, 1), (cR 2, 2), (cR 3, 1), (cR 4, 1), (cC 3, 1)]), .leaf (20, [(cS 2 5, 8), (cS 4 1, 5), (cS 4 2, 3), (cS 5 1, 3), (cR 0, 8), (cR 1, 9), (cR 5, 9), (cR 6, 9), (cC 0, 3), (cC 3, 3), (cC 5, 3)], [(cS 0 2, 20), (cS 2 0, 8), (cS 2 2, 11), (cS 2 3, 9), (cS 3 0, 3), (cS 4 3, 2), (cS 4 4, 15), (cS 4 5, 2), (cS 4 6, 6), (cR 3, 9), (cR 4, 3)]), .leaf (12, [(cS 0 0, 4), (cS 0 4, 2), (cS 1 0, 4), (cS 1 4, 6), (cS 1 5, 8), (cS 2 5, 2), (cS 2 6, 2), (cS 4 0, 1), (cS 4 1, 3), (cS 4 2, 1), (cS 5 1, 4), (cS 5 4, 2), (cS 6 4, 2), (cS 6 6, 4), (cR 0, 4), (cR 5, 4), (cR 6, 4)], [(cS 0 2, 8), (cS 1 2, 4), (cS 2 1, 2), (cS 2 3, 2), (cS 3 4, 1), (cS 3 5, 1), (cS 3 6, 2), (cS 4 3, 3), (cS 4 5, 2), (cS 4 6, 3), (cS 6 2, 4), (cR 2, 6), (cR 3, 4), (cR 4, 4)]), .leaf (4, [(cS 0 1, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 5, 2), (cS 4 1, 1), (cS 5 1, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 0, 2), (cR 1, 1), (cR 5, 2), (cR 6, 1)], [(cS 0 2, 3), (cS 1 2, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 3 6, 1), (cS 4 4, 2), (cS 6 2, 1), (cR 2, 1), (cR 3, 1), (cR 4, 2)]), .leaf (30, [(cS 0 0, 4), (cS 0 1, 5), (cS 0 4, 1), (cS 1 4, 9), (cS 1 5, 5), (cS 1 6, 5), (cS 2 5, 6), (cS 2 6, 4), (cS 4 1, 3), (cS 4 2, 5), (cS 5 0, 4), (cS 5 1, 12), (cS 5 4, 1), (cS 6 3, 5), (cS 6 4, 4), (cS 6 5, 5), (cS 6 6, 5), (cR 0, 10), (cR 1, 10), (cR 5, 10), (cR 6, 10), (cC 0, 1)], [(cS 0 2, 5), (cS 0 3, 17), (cS 1 3, 8), (cS 2 1, 7), (cS 2 3, 4), (cS 2 4, 1), (cS 3 0, 4), (cS 3 4, 1), (cS 4 4, 2), (cS 4 5, 5), (cS 4 6, 4), (cS 6 2, 2), (cR 2, 12), (cR 3, 10), (cR 4, 12), (cC 2, 1), (cC 3, 5)]), .leaf (6, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 4, 1), (cS 1 4, 1), (cS 1 5, 3), (cS 1 6, 1), (cS 4 0, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 5 1, 2), (cS 5 4, 1), (cS 6 4, 1), (cS 6 6, 2), (cR 0, 2), (cR 1, 2), (cR 5, 2), (cR 6, 2)], [(cS 0 2, 1), (cS 0 3, 3), (cS 1 3, 2), (cS 2 1, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 6 3, 1), (cR 2, 3), (cR 3, 2), (cR 4, 2), (cC 3, 1)]), .leaf (3, [(cS 0 0, 2), (cS 0 4, 2), (cS 0 5, 1), (cS 1 1, 1), (cS 1 4, 1), (cS 1 5, 2), (cS 1 6, 1), (cS 4 1, 1), (cS 5 1, 1), (cS 5 4, 1), (cS 6 6, 1), (cR 5, 1), (cR 6, 1)], [(cS 0 2, 2), (cS 2 0, 1), (cS 2 2, 1), (cS 3 5, 1), (cS 4 6, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1), (cC 3, 1)]), .leaf (20, [(cS 0 0, 11), (cS 0 3, 6), (cS 0 4, 3), (cS 0 5, 6), (cS 1 4, 3), (cS 1 5, 1), (cS 1 6, 3), (cS 2 5, 6), (cS 4 1, 4), (cS 4 2, 2), (cS 5 0, 1), (cS 5 1, 6), (cS 5 4, 1), (cS 6 3, 2), (cS 6 4, 1), (cS 6 6, 4), (cR 1, 8), (cR 5, 8), (cR 6, 8), (cC 0, 1), (cC 5, 2)], [(cS 0 2, 12), (cS 0 3, 4), (cS 2 0, 8), (cS 2 1, 3), (cS 2 2, 9), (cS 2 3, 7), (cS 3 0, 1), (cS 3 4, 2), (cS 3 5, 2), (cS 3 6, 3), (cS 4 4, 1), (cS 4 5, 2), (cS 4 6, 4), (cR 3, 8), (cR 4, 6), (cC 3, 4)])],
  .splitS0 [.leaf (1, [(cS 1 1, 1), (cS 6 1, 1), (cC 4, 1), (cC 6, 1)], [(cS 2 1, 1), (cS 4 1, 1), (cC 3, 1)]), .leaf (4, [(cS 0 3, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 1 4, 1), (cS 2 0, 1), (cS 2 5, 1), (cS 3 5, 1), (cS 4 0, 1), (cS 5 4, 2), (cS 5 6, 1), (cS 6 0, 1), (cS 6 1, 1), (cS 6 3, 1), (cS 6 4, 1), (cR 0, 1), (cC 0, 1), (cC 5, 2), (cC 6, 1)], [(cS 1 2, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 1, 2), (cS 3 3, 1), (cS 3 4, 1), (cS 4 1, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 2, 1), (cC 2, 1), (cC 3, 2)]), .leaf (12, [(cS 0 3, 5), (cS 0 5, 2), (cS 1 0, 2), (cS 1 1, 3), (cS 1 3, 4), (cS 1 4, 2), (cS 2 5, 2), (cS 3 5, 2), (cS 5 3, 2), (cS 5 4, 3), (cS 5 6, 2), (cS 6 0, 5), (cS 6 3, 4), (cS 6 4, 2), (cC 0, 7), (cC 4, 1), (cC 5, 7), (cC 6, 3)], [(cS 0 2, 5), (cS 1 2, 5), (cS 2 1, 5), (cS 2 3, 5), (cS 3 0, 2), (cS 3 1, 5), (cS 3 3, 5), (cS 3 4, 1), (cS 4 1, 5), (cS 4 3, 5), (cS 4 4, 1), (cS 5 2, 5), (cS 6 2, 5), (cC 2, 2)]), .leaf (1, [(cS 1 1, 1), (cS 6 1, 1), (cC 4, 1), (cC 6, 1)], [(cS 3 1, 1), (cS 5 1, 1), (cC 3, 1)]), .leaf (12, [(cS 0 1, 5), (cS 0 3, 2), (cS 1 4, 2), (cS 2 0, 2), (cS 2 1, 6), (cS 2 5, 2), (cS 3 5, 3), (cS 5 4, 5), (cS 5 6, 3), (cS 6 0, 1), (cS 6 3, 1), (cS 6 4, 2), (cR 0, 3), (cR 1, 1), (cC 0, 3), (cC 4, 4), (cC 5, 3), (cC 6, 6)], [(cS 1 2, 1), (cS 2 2, 1), (cS 3 0, 3), (cS 3 1, 9), (cS 4 3, 1), (cS 4 4, 3), (cS 5 1, 9), (cS 6 2, 1), (cC 2, 3), (cC 3, 8)]), .leaf (20, [(cS 0 3, 8), (cS 0 6, 2), (cS 1 0, 2), (cS 1 1, 6), (cS 1 4, 9), (cS 2 5, 2), (cS 3 5, 3), (cS 5 3, 2), (cS 5 4, 6), (cS 5 6, 2), (cS 6 1, 8), (cS 6 3, 3), (cS 6 4, 6), (cC 0, 12), (cC 4, 3), (cC 5, 12), (cC 6, 6)], [(cS 0 2, 8), (cS 1 2, 9), (cS 2 1, 8), (cS 2 3, 8), (cS 3 0, 3), (cS 3 1, 9), (cS 3 3, 9), (cS 3 4, 3), (cS 4 1, 8), (cS 4 3, 9), (cS 5 2, 9), (cS 6 2, 9), (cC 2, 3)]), .leaf (20, [(cS 0 3, 8), (cS 0 6, 2), (cS 1 0, 2), (cS 1 1, 6), (cS 1 4, 9), (cS 2 5, 2), (cS 3 5, 3), (cS 5 3, 2), (cS 5 4, 6), (cS 5 6, 2), (cS 6 1, 8), (cS 6 3, 3), (cS 6 4, 6), (cC 0, 12), (cC 4, 3), (cC 5, 12), (cC 6, 6)], [(cS 0 2, 8), (cS 1 2, 9), (cS 2 1, 8), (cS 2 3, 8), (cS 3 0, 3), (cS 3 1, 9), (cS 3 3, 9), (cS 3 4, 3), (cS 4 1, 8), (cS 4 3, 9), (cS 5 2, 9), (cS 6 2, 9), (cC 2, 3)]), .leaf (1, [(cS 0 1, 1), (cS 2 1, 1), (cC 4, 1), (cC 6, 1)], [(cS 3 1, 1), (cS 5 1, 1), (cC 3, 1)]), .leaf (1, [(cS 1 1, 1), (cS 6 1, 1), (cC 4, 1), (cC 6, 1)], [(cS 3 1, 1), (cS 5 1, 1), (cC 3, 1)]), .leaf (8, [(cS 0 3, 1), (cS 1 0, 4), (cS 1 4, 3), (cS 2 0, 2), (cS 2 5, 2), (cS 4 6, 2), (cS 5 3, 1), (cS 5 4, 2), (cS 5 6, 2), (cS 6 0, 4), (cS 6 3, 3), (cR 0, 2), (cC 0, 2), (cC 4, 2), (cC 5, 4), (cC 6, 2)], [(cS 0 2, 3), (cS 1 2, 3), (cS 2 1, 3), (cS 2 3, 3), (cS 3 0, 2), (cS 3 1, 3), (cS 3 3, 3), (cS 4 1, 3), (cS 4 3, 3), (cS 4 4, 2), (cS 5 1, 3), (cS 5 3, 3), (cS 6 2, 3), (cC 2, 2)]), .leaf (1, [(cS 0 1, 1), (cS 2 1, 1), (cC 4, 1), (cC 6, 1)], [(cS 3 1, 1), (cS 5 1, 1), (cC 3, 1)]), .leaf (4, [(cS 0 3, 1), (cS 1 3, 1), (cS 2 0, 1), (cS 2 5, 1), (cS 3 5, 1), (cS 4 6, 1), (cS 5 4, 2), (cS 5 6, 1), (cS 6 3, 1), (cR 0, 1), (cR 1, 1), (cR 6, 1), (cC 0, 2), (cC 5, 2)], [(cS 0 2, 1), (cS 1 2, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 1, 2), (cS 3 3, 1), (cS 3 4, 1), (cS 4 1, 1), (cS 4 3, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 2, 1), (cC 2, 1), (cC 3, 1)]), .leaf (3, [(cS 0 3, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 5 3, 1), (cS 6 1, 1), (cS 6 3, 1), (cC 0, 2), (cC 4, 1), (cC 5, 2), (cC 6, 1)], [(cS 2 0, 2), (cS 2 1, 1), (cS 3 3, 2), (cS 4 1, 1), (cC 2, 2), (cC 3, 1)]), .leaf (1, [(cS 0 1, 1), (cS 2 1, 1), (cC 4, 1), (cC 6, 1)], [(cS 3 1, 1), (cS 5 1, 1), (cC 3, 1)]), .leaf (4, [(cS 0 3, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 1 4, 1), (cS 2 0, 1), (cS 2 5, 1), (cS 3 5, 1), (cS 4 0, 1), (cS 5 4, 2), (cS 5 6, 1), (cS 6 0, 1), (cS 6 1, 1), (cS 6 3, 1), (cS 6 4, 1), (cR 0, 1), (cC 0, 1), (cC 5, 2), (cC 6, 1)], [(cS 1 2, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 1, 2), (cS 3 3, 1), (cS 3 4, 1), (cS 4 1, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 2, 1), (cC 2, 1), (cC 3, 2)]), .leaf (20, [(cS 0 4, 8), (cS 0 5, 2), (cS 1 0, 2), (cS 1 1, 6), (cS 1 4, 9), (cS 2 5, 2), (cS 3 5, 3), (cS 5 4, 8), (cS 5 6, 2), (cS 6 0, 2), (cS 6 1, 6), (cS 6 3, 9), (cC 0, 12), (cC 4, 3), (cC 5, 12), (cC 6, 6)], [(cS 0 2, 8), (cS 1 2, 9), (cS 2 1, 8), (cS 2 3, 8), (cS 3 0, 3), (cS 3 1, 9), (cS 3 3, 9), (cS 3 4, 3), (cS 4 1, 8), (cS 4 3, 9), (cS 5 2, 9), (cS 6 2, 9), (cC 2, 3)]), .leaf (4, [(cS 0 3, 2), (cS 0 4, 1), (cS 1 1, 1), (cS 1 4, 1), (cS 2 4, 1), (cS 5 3, 2), (cS 5 4, 1), (cS 6 1, 1), (cS 6 3, 1), (cC 0, 3), (cC 5, 3), (cC 6, 1)], [(cS 0 2, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 2 1, 3), (cS 2 3, 1), (cS 3 1, 1), (cS 3 3, 2), (cS 3 4, 1), (cS 4 1, 1), (cS 4 3, 1), (cS 5 2, 1), (cS 6 2, 1), (cC 2, 2)]), .leaf (8, [(cS 0 4, 2), (cS 1 0, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 2 0, 2), (cS 2 5, 2), (cS 3 5, 2), (cS 4 0, 1), (cS 4 6, 2), (cS 5 4, 4), (cS 5 6, 2), (cS 6 0, 1), (cS 6 1, 1), (cS 6 3, 1), (cR 0, 2), (cR 1, 2), (cR 6, 2), (cC 0, 2), (cC 4, 1), (cC 5, 3), (cC 6, 1)], [(cS 1 2, 1), (cS 2 1, 1), (cS 3 0, 3), (cS 3 1, 4), (cS 3 3, 1), (cS 3 4, 2), (cS 4 1, 1), (cS 4 3, 1), (cS 5 1, 4), (cS 6 2, 1), (cC 2, 3), (cC 3, 4)])],
  .splitS0 [.leaf (24, [(cS 0 0, 7), (cS 0 3, 2), (cS 0 4, 4), (cS 0 6, 2), (cS 1 0, 3), (cS 1 4, 8), (cS 1 6, 10), (cS 2 5, 6), (cS 3 5, 5), (cS 3 6, 11), (cS 4 2, 2), (cS 5 1, 4), (cS 5 2, 8), (cS 5 3, 3), (cS 5 4, 7), (cS 6 1, 3), (cS 6 3, 5), (cS 6 4, 3), (cR 0, 4), (cC 1, 10), (cC 4, 6), (cC 5, 8)], [(cS 0 2, 16), (cS 2 0, 11), (cS 2 2, 14), (cS 2 3, 2), (cS 3 0, 3), (cS 3 1, 10), (cS 3 3, 11), (cS 3 4, 3), (cS 4 6, 7), (cS 5 0, 8), (cS 5 6, 6), (cS 6 6, 11), (cR 4, 3), (cC 3, 8)]), .leaf (20, [(cS 0 0, 5), (cS 0 1, 1), (cS 0 6, 3), (cS 1 0, 5), (cS 1 3, 5), (cS 1 6, 4), (cS 2 5, 6), (cS 3 6, 7), (cS 4 1, 4), (cS 4 2, 2), (cS 4 6, 6), (cS 5 1, 5), (cS 5 2, 6), (cS 5 3, 2), (cS 6 1, 8), (cS 6 3, 3), (cS 6 4, 6), (cR 0, 3), (cR 1, 3), (cC 1, 3), (cC 4, 9), (cC 5, 6), (cC 6, 1)], [(cS 0 2, 11), (cS 1 2, 6), (cS 2 0, 7), (cS 2 1, 2), (cS 2 2, 9), (cS 2 3, 3), (cS 3 0, 5), (cS 3 1, 6), (cS 3 3, 8), (cS 4 3, 5), (cS 4 4, 5), (cS 5 0, 6), (cS 5 6, 6), (cS 6 2, 6), (cS 6 6, 8), (cR 4, 2), (cC 2, 3)]), .leaf (2, [(cS 0 1, 1), (cS 1 6, 1), (cS 3 6, 1), (cS 5 1, 1), (cC 1, 1), (cC 4, 2), (cC 6, 1)], [(cS 2 1, 1), (cS 3 1, 1), (cS 5 6, 1), (cS 6 6, 1), (cC 3, 2)]), .leaf (20, [(cS 0 0, 5), (cS 0 1, 3), (cS 0 3, 2), (cS 0 5, 4), (cS 1 0, 2), (cS 1 1, 2), (cS 1 4, 1), (cS 2 5, 5), (cS 3 5, 3), (cS 3 6, 4), (cS 4 1, 8), (cS 4 6, 5), (cS 5 1, 9), (cS 5 2, 3), (cS 5 4, 2), (cS 6 1, 9), (cS 6 3, 3), (cS 6 4, 6), (cR 1, 8), (cC 4, 9), (cC 5, 3), (cC 6, 5)], [(cS 0 2, 5), (cS 2 0, 5), (cS 2 1, 3), (cS 2 2, 5), (cS 3 0, 6), (cS 3 1, 6), (cS 3 2, 3), (cS 4 3, 2), (cS 4 4, 6), (cS 5 0, 3), (cS 5 6, 7), (cS 6 0, 3), (cS 6 6, 8), (cC 2, 3), (cC 3, 12)]), .leaf (6, [(cS 0 0, 2), (cS 0 3, 1), (cS 1 0, 3), (cS 1 4, 2), (cS 1 6, 2), (cS 2 5, 2), (cS 3 6, 2), (cS 4 1, 3), (cS 4 6, 1), (cS 5 1, 1), (cS 5 2, 2), (cS 5 3, 2), (cS 6 1, 3), (cS 6 4, 2), (cR 0, 1), (cC 4, 2), (cC 5, 2), (cC 6, 1)], [(cS 0 2, 4), (cS 1 2, 1), (cS 2 0, 1), (cS 2 1, 2), (cS 2 2, 1), (cS 2 3, 2), (cS 3 0, 2), (cS 3 1, 1), (cS 3 3, 4), (cS 4 4, 2), (cS 5 0, 2), (cS 5 6, 2), (cS 6 6, 2), (cC 2, 2)]), .leaf (12, [(cS 0 0, 5), (cS 0 3, 2), (cS 0 6, 4), (cS 1 0, 6), (cS 1 4, 5), (cS 1 6, 3), (cS 2 5, 3), (cS 2 6, 2), (cS 3 5, 1), (cS 3 6, 7), (cS 4 1, 4), (cS 4 2, 2), (cS 5 1, 2), (cS 5 2, 4), (cS 5 3, 3), (cS 6 1, 6), (cS 6 3, 1), (cS 6 4, 4), (cR 0, 1), (cC 4, 4), (cC 5, 4)], [(cS 0 2, 8), (cS 1 2, 4), (cS 2 0, 1), (cS 2 1, 5), (cS 2 2, 3), (cS 2 3, 5), (cS 3 0, 2), (cS 3 1, 4), (cS 3 3, 7), (cS 4 3, 1), (cS 4 4, 2), (cS 4 6, 1), (cS 5 0, 4), (cS 5 6, 5), (cS 6 2, 4), (cS 6 6, 3), (cR 4, 2)]), .leaf (60, [(cS 0 1, 5), (cS 0 6, 7), (cS 1 0, 5), (cS 1 4, 12), (cS 1 6, 19), (cS 2 5, 14), (cS 2 6, 12), (cS 3 5, 17), (cS 3 6, 28), (cS 4 2, 3), (cS 4 5, 5), (cS 5 1, 21), (cS 5 2, 10), (cS 5 4, 17), (cS 6 1, 5), (cS 6 3, 5), (cS 6 4, 14), (cR 0, 19), (cR 1, 5), (cC 1, 26), (cC 4, 24), (cC 5, 5), (cC 6, 5)], [(cS 0 2, 5), (cS 0 3, 8), (cS 1 3, 5), (cS 2 1, 29), (cS 2 3, 8), (cS 3 1, 26), (cS 3 2, 5), (cS 3 3, 5), (cS 4 0, 3), (cS 4 4, 9), (cS 4 6, 9), (cS 5 0, 5), (cS 5 6, 28), (cS 6 6, 14), (cC 0, 5), (cC 3, 47), (cC 6, 10)]), .leaf (24, [(cS 0 0, 6), (cS 1 0, 12), (cS 1 3, 4), (cS 1 6, 8), (cS 2 5, 6), (cS 3 6, 8), (cS 4 1, 11), (cS 4 6, 6), (cS 5 1, 7), (cS 5 2, 6), (cS 5 3, 4), (cS 6 1, 12), (cS 6 4, 6), (cR 0, 6), (cC 4, 14), (cC 5, 6), (cC 6, 4)], [(cS 0 2, 14), (cS 1 2, 4), (cS 2 0, 6), (cS 2 1, 6), (cS 2 2, 8), (cS 2 3, 6), (cS 3 0, 6), (cS 3 1, 7), (cS 3 3, 4), (cS 4 3, 14), (cS 4 4, 6), (cS 5 0, 6), (cS 5 3, 4), (cS 5 6, 8), (cS 6 2, 4), (cS 6 6, 10), (cC 2, 6)]), .leaf (2, [(cS 0 1, 1), (cS 1 6, 1), (cS 3 6, 1), (cS 5 1, 1), (cC 1, 1), (cC 4, 2), (cC 6, 1)], [(cS 2 1, 1), (cS 3 1, 1), (cS 5 6, 1), (cS 6 6, 1), (cC 3, 2)]), .leaf (2, [(cS 0 1, 1), (cS 1 6, 1), (cS 3 6, 1), (cS 5 1, 1), (cC 1, 1), (cC 4, 2), (cC 6, 1)], [(cS 2 1, 1), (cS 3 1, 1), (cS 5 6, 1), (cS 6 6, 1), (cC 3, 2)]), .leaf (24, [(cS 0 0, 3), (cS 0 3, 2), (cS 0 4, 1), (cS 1 0, 3), (cS 1 4, 4), (cS 1 6, 9), (cS 2 5, 8), (cS 3 5, 2), (cS 3 6, 7), (cS 4 6, 8), (cS 5 1, 7), (cS 5 2, 7), (cS 5 3, 2), (cS 5 4, 9), (cS 6 3, 2), (cS 6 4, 2), (cR 0, 8), (cC 1, 10), (cC 4, 9), (cC 5, 5), (cC 6, 2)], [(cS 0 2, 3), (cS 0 3, 8), (cS 2 0, 9), (cS 2 1, 1), (cS 2 2, 10), (cS 2 3, 1), (cS 3 0, 3), (cS 3 1, 7), (cS 3 3, 7), (cS 3 4, 3), (cS 5 0, 4), (cS 5 6, 7), (cS 6 0, 2), (cS 6 6, 10), (cR 3, 3), (cR 4, 2), (cC 0, 1), (cC 2, 3), (cC 3, 10)]), .leaf (24, [(cS 0 0, 2), (cS 1 0, 3), (cS 1 4, 8), (cS 1 6, 9), (cS 2 5, 9), (cS 3 5, 3), (cS 3 6, 6), (cS 4 6, 9), (cS 5 1, 8), (cS 5 2, 6), (cS 5 3, 2), (cS 5 4, 7), (cS 6 3, 1), (cS 6 4, 7), (cR 0, 9), (cC 1, 10), (cC 4, 7), (cC 5, 5), (cC 6, 1)], [(cS 0 2, 1), (cS 0 3, 8), (cS 2 0, 9), (cS 2 2, 10), (cS 3 0, 4), (cS 3 1, 6), (cS 3 2, 1), (cS 3 3, 4), (cS 4 4, 5), (cS 5 0, 3), (cS 5 6, 8), (cS 6 0, 1), (cS 6 6, 10), (cR 3, 3), (cR 4, 1), (cC 0, 2), (cC 2, 4), (cC 3, 11)])],
  .root (3, [(cS 0 0, 2), (cS 1 0, 1), (cS 1 5, 2), (cS 4 3, 1), (cS 4 4, 2), (cS 5 0, 1), (cS 6 1, 1), (cS 6 4, 3), (cS 6 6, 2), (cC 5, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 2 6, 1), (cS 4 1, 1), (cS 4 6, 2), (cS 5 2, 1), (cS 6 2, 1), (cR 2, 1), (cR 3, 1), (cC 1, 1), (cC 3, 1)]),
  .root (4, [(cS 0 0, 2), (cS 1 0, 2), (cS 1 5, 4), (cS 4 1, 1), (cS 4 2, 1), (cS 4 3, 3), (cS 4 4, 1), (cS 5 2, 2), (cS 6 3, 2), (cS 6 4, 2), (cS 6 5, 2)], [(cS 0 2, 2), (cS 0 3, 2), (cS 1 1, 2), (cS 1 3, 2), (cS 4 0, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 0, 2), (cS 5 5, 2), (cS 6 1, 2), (cS 6 6, 2), (cR 2, 2), (cR 3, 2)]),
  .root (6, [(cS 0 0, 3), (cS 0 5, 2), (cS 1 0, 3), (cS 2 5, 2), (cS 3 6, 2), (cS 4 3, 2), (cS 4 4, 2), (cS 6 4, 4), (cC 4, 2), (cC 5, 2), (cC 6, 2)], [(cS 0 3, 2), (cS 1 2, 2), (cS 1 4, 4), (cS 2 0, 1), (cS 2 3, 2), (cS 3 0, 1), (cS 3 1, 2), (cS 3 3, 2), (cS 3 4, 2), (cS 4 0, 1), (cS 5 0, 3), (cS 5 2, 2), (cS 5 6, 2), (cS 6 0, 1), (cS 6 2, 2), (cC 1, 2), (cC 2, 2)]),
  .splitS0 [.leaf (2, [(cS 0 4, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 5 4, 1), (cS 6 3, 1), (cS 6 5, 1), (cC 0, 1), (cC 1, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 2 3, 1), (cS 3 4, 1), (cS 3 5, 1), (cS 4 3, 1), (cS 4 5, 1), (cS 5 2, 1), (cC 2, 1)]), .leaf (2, [(cS 2 0, 1), (cS 2 5, 1), (cS 3 1, 1), (cS 4 0, 1), (cS 5 4, 1), (cS 5 6, 1), (cR 0, 1), (cR 1, 1), (cR 6, 1)], [(cS 2 4, 1), (cS 3 6, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 5 1, 1), (cC 2, 1), (cC 3, 1)]), .leaf (2, [(cS 1 4, 1), (cS 1 6, 1), (cS 6 4, 1), (cS 6 6, 1), (cC 0, 1), (cC 1, 1), (cC 4, 1), (cC 6, 1)], [(cS 3 5, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 5 1, 1), (cC 2, 1), (cC 3, 1)]), .leaf (2, [(cS 0 3, 1), (cS 1 4, 1), (cS 5 4, 1), (cS 6 4, 1), (cC 0, 1), (cC 1, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 2 3, 1), (cS 3 4, 1), (cS 3 5, 2), (cS 4 3, 1), (cS 5 2, 1), (cC 2, 1)]), .leaf (2, [(cS 1 4, 1), (cS 1 6, 1), (cS 6 4, 1), (cS 6 5, 1), (cC 0, 1), (cC 1, 1), (cC 4, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 2 3, 1), (cS 3 5, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 5 2, 1), (cC 2, 1)]), .leaf (10, [(cS 0 0, 1), (cS 0 3, 2), (cS 0 4, 1), (cS 1 4, 6), (cS 1 5, 3), (cS 1 6, 2), (cS 2 0, 2), (cS 2 5, 1), (cS 3 0, 2), (cS 5 4, 4), (cS 5 6, 1), (cS 6 4, 6), (cS 6 5, 2), (cS 6 6, 3), (cR 0, 1), (cC 0, 2), (cC 1, 6), (cC 6, 4)], [(cS 0 3, 4), (cS 1 3, 4), (cS 2 2, 1), (cS 2 4, 4), (cS 3 3, 4), (cS 3 5, 5), (cS 4 4, 3), (cS 4 5, 2), (cS 4 6, 2), (cS 5 1, 2), (cS 5 2, 4), (cS 6 2, 1), (cR 4, 1), (cC 2, 3), (cC 3, 2)]), .leaf (6, [(cS 0 1, 1), (cS 0 4, 1), (cS 0 5, 1), (cS 1 4, 4), (cS 1 5, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 4 0, 1), (cS 5 4, 1), (cS 5 5, 1), (cS 6 3, 1), (cS 6 4, 3), (cR 1, 1), (cR 6, 1), (cC 0, 1), (cC 1, 3), (cC 6, 4)], [(cS 0 3, 2), (cS 1 3, 2), (cS 2 3, 1), (cS 2 4, 1), (cS 2 6, 1), (cS 3 3, 2), (cS 3 5, 5), (cS 4 2, 1), (cS 4 4, 3), (cS 4 5, 1), (cS 5 1, 1), (cS 5 2, 3), (cS 6 2, 1), (cC 2, 1), (cC 3, 2)]), .leaf (2, [(cS 0 4, 1), (cS 1 4, 1), (cS 5 4, 1), (cS 6 3, 1), (cC 0, 1), (cC 1, 1), (cC 5, 1), (cC 6, 1)], [(cS 3 4, 1), (cS 3 5, 2), (cS 5 2, 1), (cC 2, 1), (cC 3, 1)]), .leaf (10, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 3, 5), (cS 0 5, 1), (cS 1 4, 2), (cS 1 5, 2), (cS 2 0, 1), (cS 2 1, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 3 1, 4), (cS 5 4, 5), (cS 5 6, 1), (cS 6 4, 2), (cS 6 5, 2), (cR 1, 3), (cR 6, 3), (cC 0, 4), (cC 1, 1), (cC 5, 2), (cC 6, 2)], [(cS 0 2, 1), (cS 1 2, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 3 4, 4), (cS 3 5, 3), (cS 3 6, 2), (cS 4 5, 2), (cS 4 6, 2), (cS 5 1, 4), (cS 5 2, 1), (cS 6 2, 1), (cR 4, 1), (cC 2, 4), (cC 3, 4)])],
  .splitS0 [.leaf (4, [(cS 0 4, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 1 4, 2), (cS 1 6, 2), (cS 2 0, 1), (cS 2 5, 2), (cS 3 0, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 5 2, 1), (cS 5 4, 2), (cS 6 4, 1), (cR 0, 1), (cR 6, 1), (cC 1, 2)], [(cS 0 2, 2), (cS 1 2, 1), (cS 2 3, 2), (cS 3 4, 1), (cS 3 6, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 6, 2), (cS 6 2, 1), (cS 6 6, 1), (cR 3, 1), (cC 2, 1)]), .leaf (2, [(cS 0 4, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 4 2, 1), (cS 5 4, 1), (cR 6, 1), (cC 1, 1)], [(cS 0 2, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 6, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 5 0, 1), (cS 5 6, 1), (cC 3, 1)]), .leaf (2, [(cS 0 4, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 1 6, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 4 2, 1), (cR 6, 1), (cC 1, 1), (cC 4, 1)], [(cS 0 2, 1), (cS 2 2, 1), (cS 3 6, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 5 0, 1), (cS 5 6, 1), (cC 3, 1)]), .leaf (20, [(cS 0 0, 2), (cS 0 4, 10), (cS 0 6, 3), (cS 1 0, 8), (cS 1 4, 10), (cS 1 5, 10), (cS 1 6, 7), (cS 2 0, 2), (cS 2 6, 4), (cS 3 0, 6), (cS 3 1, 2), (cS 4 1, 3), (cS 4 2, 5), (cS 4 5, 7), (cS 5 2, 2), (cS 5 4, 10), (cS 6 3, 2), (cS 6 5, 2), (cR 6, 8), (cC 1, 10)], [(cS 0 2, 12), (cS 1 2, 3), (cS 2 2, 3), (cS 2 3, 10), (cS 3 3, 2), (cS 3 4, 8), (cS 3 5, 12), (cS 3 6, 8), (cS 4 3, 8), (cS 4 4, 3), (cS 4 6, 6), (cS 5 0, 7), (cS 5 6, 7), (cS 6 2, 3), (cS 6 6, 7), (cC 2, 5)]), .leaf (12, [(cS 0 0, 1), (cS 0 4, 4), (cS 0 6, 6), (cS 1 0, 4), (cS 1 4, 4), (cS 1 6, 5), (cS 2 0, 2), (cS 2 5, 7), (cS 3 0, 4), (cS 3 2, 4), (cS 4 1, 2), (cS 4 2, 1), (cS 5 2, 4), (cS 5 3, 4), (cS 6 1, 3), (cS 6 4, 5), (cS 6 5, 4), (cR 0, 1), (cC 0, 1), (cC 1, 5), (cC 4, 3)], [(cS 0 2, 8), (cS 1 2, 4), (cS 2 2, 3), (cS 2 3, 5), (cS 3 3, 4), (cS 3 5, 2), (cS 3 6, 5), (cS 4 0, 1), (cS 4 3, 3), (cS 4 4, 9), (cS 4 5, 3), (cS 4 6, 2), (cS 5 0, 3), (cS 5 6, 7), (cS 6 0, 1), (cS 6 2, 4), (cS 6 6, 2)]), .leaf (5, [(cS 0 4, 1), (cS 0 6, 1), (cS 1 4, 2), (cS 1 6, 2), (cS 2 0, 1), (cS 2 5, 2), (cS 2 6, 1), (cS 3 0, 2), (cS 3 2, 1), (cS 4 2, 1), (cS 5 2, 1), (cS 5 4, 2), (cS 6 4, 2), (cR 0, 1), (cR 1, 1), (cR 6, 1), (cC 1, 3)], [(cS 0 3, 2), (cS 2 2, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 4, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 4 4, 1), (cS 4 5, 2), (cS 4 6, 1), (cS 5 0, 1), (cS 5 6, 2), (cS 6 6, 2), (cC 3, 3)]), .leaf (16, [(cS 0 4, 2), (cS 0 6, 3), (cS 1 0, 2), (cS 1 4, 9), (cS 1 5, 2), (cS 1 6, 6), (cS 2 0, 3), (cS 2 5, 3), (cS 2 6, 3), (cS 3 0, 5), (cS 3 1, 1), (cS 3 2, 1), (cS 4 1, 1), (cS 4 2, 4), (cS 4 5, 6), (cS 5 2, 3), (cS 5 4, 5), (cS 6 4, 7), (cR 0, 3), (cR 1, 2), (cR 6, 4), (cC 1, 9)], [(cS 0 2, 2), (cS 0 3, 5), (cS 1 3, 2), (cS 2 2, 5), (cS 2 4, 5), (cS 3 3, 2), (cS 3 5, 11), (cS 3 6, 5), (cS 4 0, 3), (cS 4 4, 5), (cS 4 6, 3), (cS 5 0, 3), (cS 5 6, 7), (cS 6 6, 6), (cC 3, 9)]), .leaf (20, [(cS 0 4, 11), (cS 0 6, 5), (cS 1 0, 9), (cS 1 4, 9), (cS 1 5, 11), (cS 1 6, 6), (cS 2 0, 2), (cS 2 6, 3), (cS 3 0, 6), (cS 4 2, 5), (cS 5 4, 11), (cS 5 5, 3), (cR 4, 3), (cR 6, 9), (cC 1, 12)], [(cS 0 2, 8), (cS 2 2, 5), (cS 3 4, 5), (cS 3 5, 12), (cS 3 6, 6), (cS 4 4, 3), (cS 4 6, 5), (cS 5 0, 6), (cS 5 6, 9), (cS 6 6, 6), (cR 2, 3), (cC 3, 12)]), .leaf (2, [(cS 0 4, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 4 2, 1), (cS 5 4, 1), (cR 6, 1), (cC 1, 1)], [(cS 0 2, 1), (cS 2 2, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 4 5, 1), (cS 5 0, 1), (cS 5 6, 1), (cC 3, 1)])],
  .root (60, [(cS 0 4, 19), (cS 0 6, 19), (cS 1 0, 26), (cS 1 1, 20), (cS 1 4, 27), (cS 2 1, 7), (cS 2 5, 26), (cS 3 0, 33), (cS 3 1, 27), (cS 3 5, 34), (cS 5 4, 26), (cS 6 4, 34), (cR 0, 7), (cR 1, 7), (cC 6, 27)], [(cS 0 1, 32), (cS 0 3, 19), (cS 1 3, 14), (cS 2 3, 19), (cS 3 3, 14), (cS 4 4, 20), (cS 5 0, 26), (cS 5 1, 6), (cS 5 2, 12), (cS 5 6, 20), (cS 6 1, 7), (cS 6 6, 7), (cR 4, 7), (cR 5, 7), (cC 1, 14), (cC 2, 14), (cC 3, 27)]),
  .root (2, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 0, 1), (cS 1 5, 1), (cS 2 0, 1), (cS 2 5, 1), (cS 3 1, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 6 4, 2)], [(cS 0 3, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 6, 1), (cS 6 2, 1), (cS 6 6, 1), (cR 5, 1), (cC 1, 1)]),
  .root (6, [(cS 0 0, 3), (cS 0 4, 2), (cS 0 6, 2), (cS 1 0, 1), (cS 2 2, 3), (cS 2 3, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 5 0, 1), (cS 6 0, 1), (cS 6 4, 2), (cS 6 5, 2), (cS 6 6, 2), (cR 5, 2), (cC 1, 2), (cC 3, 2)], [(cS 0 2, 4), (cS 0 5, 3), (cS 1 4, 2), (cS 1 5, 1), (cS 1 6, 2), (cS 2 0, 2), (cS 2 1, 1), (cS 2 4, 1), (cS 2 5, 2), (cS 2 6, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 4 3, 1), (cS 4 4, 3), (cS 4 6, 3), (cS 5 4, 2), (cS 5 5, 1), (cS 6 2, 2), (cR 3, 2)]),
  .root (6, [(cS 0 0, 1), (cS 0 3, 2), (cS 0 6, 1), (cS 1 0, 1), (cS 1 1, 2), (cS 2 2, 3), (cS 2 3, 3), (cS 3 5, 3), (cS 4 6, 2), (cS 5 0, 1), (cS 5 4, 4), (cS 5 5, 1), (cS 5 6, 2), (cS 6 0, 2), (cS 6 1, 1), (cS 6 4, 2), (cS 6 5, 2), (cR 0, 2), (cC 6, 1)], [(cS 0 2, 2), (cS 1 4, 2), (cS 1 5, 4), (cS 1 6, 2), (cS 2 0, 2), (cS 2 1, 1), (cS 2 4, 1), (cS 3 0, 1), (cS 4 1, 3), (cS 4 2, 1), (cS 4 3, 3), (cS 4 4, 1), (cS 5 1, 2), (cS 5 3, 2), (cS 6 2, 4), (cR 3, 2)]),
  .root (24, [(cS 0 0, 12), (cS 0 4, 15), (cS 0 6, 2), (cS 1 0, 10), (cS 1 1, 2), (cS 1 2, 8), (cS 1 3, 2), (cS 2 2, 4), (cS 2 3, 10), (cS 3 2, 6), (cS 3 3, 3), (cS 3 5, 11), (cS 4 1, 9), (cS 4 2, 3), (cS 4 5, 1), (cS 4 6, 11), (cS 5 1, 1), (cS 5 4, 4), (cS 6 4, 9), (cR 3, 1), (cR 5, 11)], [(cS 0 2, 12), (cS 0 3, 2), (cS 0 5, 7), (cS 1 4, 5), (cS 1 5, 12), (cS 1 6, 1), (cS 2 0, 2), (cS 2 1, 8), (cS 2 4, 8), (cS 2 6, 8), (cS 3 0, 9), (cS 3 1, 3), (cS 3 4, 4), (cS 4 3, 11), (cS 4 4, 9), (cS 5 0, 1), (cS 5 3, 4), (cS 6 0, 10), (cS 6 2, 10), (cS 6 6, 11), (cC 1, 2), (cC 6, 4)]),
  .root (3, [(cS 0 0, 2), (cS 1 0, 1), (cS 2 2, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 6 0, 1), (cS 6 4, 1), (cS 6 5, 2), (cS 6 6, 1), (cC 3, 2)], [(cS 0 2, 1), (cS 0 5, 1), (cS 2 0, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 4 1, 1), (cS 4 6, 1), (cS 6 2, 1), (cR 1, 1), (cR 3, 1), (cR 5, 1), (cC 2, 1), (cC 5, 1)]),
  .root (10, [(cS 0 0, 5), (cS 0 4, 2), (cS 1 0, 5), (cS 1 3, 1), (cS 2 2, 4), (cS 2 3, 2), (cS 3 2, 1), (cS 3 3, 3), (cS 4 1, 3), (cS 4 2, 2), (cS 4 3, 1), (cS 4 4, 3), (cS 5 1, 1), (cS 5 2, 4), (cS 5 4, 3), (cS 6 4, 5), (cS 6 5, 3), (cC 3, 3)], [(cS 0 2, 5), (cS 0 3, 2), (cS 0 5, 1), (cS 1 2, 3), (cS 1 4, 2), (cS 1 5, 3), (cS 2 0, 2), (cS 2 4, 1), (cS 2 5, 1), (cS 3 0, 3), (cS 3 1, 1), (cS 3 5, 2), (cS 3 6, 1), (cS 4 6, 3), (cS 5 0, 4), (cS 5 6, 1), (cS 6 0, 3), (cS 6 2, 3), (cR 2, 1), (cR 3, 1), (cC 1, 2), (cC 5, 4), (cC 6, 2)]),
  .root (6, [(cS 0 0, 3), (cS 1 0, 3), (cS 2 2, 2), (cS 3 5, 2), (cS 3 6, 2), (cS 4 5, 2), (cS 5 5, 2), (cS 6 5, 4), (cC 3, 4), (cC 4, 2)], [(cS 0 2, 2), (cS 0 5, 2), (cS 1 2, 2), (cS 1 5, 4), (cS 2 0, 2), (cS 2 5, 2), (cS 3 0, 1), (cS 3 1, 2), (cS 4 1, 2), (cS 4 6, 2), (cS 5 0, 3), (cS 5 2, 2), (cS 6 0, 2), (cS 6 2, 2), (cC 0, 1), (cC 2, 2)]),
  .root (6, [(cS 1 0, 3), (cS 1 2, 1), (cS 2 0, 2), (cS 2 2, 4), (cS 3 0, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 5 6, 2), (cS 6 4, 3), (cS 6 5, 1), (cS 6 6, 1), (cR 0, 2), (cR 6, 2), (cC 0, 1), (cC 1, 1), (cC 3, 1)], [(cS 0 2, 2), (cS 0 5, 2), (cS 1 4, 3), (cS 1 6, 3), (cS 2 4, 2), (cS 2 5, 2), (cS 3 3, 2), (cS 3 5, 1), (cS 3 6, 2), (cS 4 2, 2), (cS 4 4, 2), (cS 5 1, 1), (cS 5 3, 1), (cS 6 2, 4), (cR 4, 2), (cR 5, 1), (cC 5, 1)]),
  .root (24, [(cS 0 0, 2), (cS 1 0, 16), (cS 1 2, 4), (cS 1 3, 5), (cS 2 0, 2), (cS 2 2, 12), (cS 3 0, 4), (cS 3 1, 4), (cS 3 3, 9), (cS 4 1, 2), (cS 4 2, 10), (cS 5 2, 4), (cS 6 4, 21), (cS 6 5, 3), (cC 0, 6), (cC 1, 8), (cC 3, 3)], [(cS 0 1, 2), (cS 0 2, 7), (cS 0 3, 2), (cS 1 4, 9), (cS 1 5, 2), (cS 2 4, 5), (cS 2 5, 3), (cS 3 4, 5), (cS 3 5, 1), (cS 3 6, 1), (cS 4 3, 2), (cS 4 4, 15), (cS 4 6, 3), (cS 5 0, 8), (cS 5 3, 5), (cS 5 6, 2), (cS 6 0, 3), (cS 6 2, 12), (cR 0, 3), (cC 4, 2), (cC 5, 8), (cC 6, 11)]),
  .root (30, [(cS 0 0, 1), (cS 1 0, 14), (cS 1 1, 8), (cS 1 2, 3), (cS 1 3, 7), (cS 2 0, 5), (cS 2 2, 16), (cS 2 3, 7), (cS 3 0, 10), (cS 3 1, 8), (cS 3 5, 9), (cS 4 6, 9), (cS 5 4, 6), (cS 6 4, 20), (cR 0, 7), (cR 2, 3), (cR 3, 4), (cC 4, 4), (cC 6, 8)], [(cS 0 1, 8), (cS 1 5, 22), (cS 2 5, 4), (cS 3 4, 3), (cS 4 1, 8), (cS 4 2, 10), (cS 4 3, 11), (cS 4 4, 7), (cS 5 0, 10), (cS 5 1, 8), (cS 5 5, 5), (cS 6 0, 8), (cS 6 1, 2), (cS 6 2, 17), (cS 6 6, 9), (cR 0, 4), (cR 5, 4), (cC 3, 9), (cC 5, 4)]),
  .root (4, [(cS 0 0, 1), (cS 0 4, 1), (cS 1 0, 3), (cS 2 0, 1), (cS 2 1, 1), (cS 2 2, 3), (cS 3 0, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 4, 1), (cS 6 4, 2), (cS 6 5, 1), (cC 3, 1)], [(cS 0 1, 1), (cS 0 2, 3), (cS 1 3, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 2 4, 1), (cS 4 1, 2), (cS 4 6, 1), (cS 5 0, 2), (cS 5 2, 2), (cS 6 0, 2), (cS 6 2, 2), (cR 3, 1), (cC 5, 2), (cC 6, 1)]),
  .root (2, [(cS 0 0, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 2 3, 2), (cS 6 4, 1), (cS 6 6, 1), (cR 1, 1), (cR 6, 1)], [(cS 0 2, 1), (cS 2 0, 1), (cS 2 2, 1), (cS 2 5, 1), (cS 6 2, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1)]),
  .root (12, [(cS 0 0, 7), (cS 0 3, 5), (cS 0 4, 1), (cS 0 6, 1), (cS 1 1, 1), (cS 1 5, 7), (cS 2 3, 6), (cS 2 5, 1), (cS 3 3, 4), (cS 4 1, 3), (cS 4 2, 2), (cS 5 1, 7), (cS 5 3, 6), (cS 6 4, 4), (cS 6 5, 8), (cR 1, 4), (cC 3, 2)], [(cS 0 2, 7), (cS 2 1, 2), (cS 2 4, 3), (cS 3 0, 2), (cS 3 1, 3), (cS 3 5, 2), (cS 4 4, 10), (cS 4 6, 3), (cS 5 6, 4), (cS 6 0, 5), (cS 6 2, 5), (cR 2, 5), (cR 3, 2), (cR 4, 2), (cC 6, 3)]),
  .root (4, [(cS 1 0, 1), (cS 1 4, 1), (cS 2 3, 3), (cS 2 5, 1), (cS 3 5, 2), (cS 3 6, 1), (cS 5 4, 2), (cS 6 4, 2), (cR 0, 2), (cR 1, 1), (cR 2, 1), (cC 6, 1)], [(cS 2 1, 1), (cS 3 1, 2), (cS 4 3, 2), (cS 4 4, 1), (cS 5 1, 2), (cS 5 6, 2), (cS 6 2, 2), (cR 4, 1), (cR 6, 1), (cC 0, 1), (cC 2, 1)]),
  .root (24, [(cS 0 0, 3), (cS 0 1, 3), (cS 0 5, 3), (cS 0 6, 5), (cS 1 1, 6), (cS 1 2, 3), (cS 1 6, 4), (cS 2 2, 9), (cS 2 5, 14), (cS 3 3, 6), (cS 3 4, 1), (cS 5 4, 6), (cS 6 5, 9), (cS 6 6, 1), (cR 0, 6), (cR 1, 6), (cC 3, 9), (cC 4, 9)], [(cS 0 2, 15), (cS 2 6, 5), (cS 3 1, 12), (cS 3 5, 4), (cS 3 6, 15), (cS 4 5, 10), (cS 5 0, 1), (cS 5 2, 4), (cS 5 6, 3), (cR 5, 11), (cC 0, 9), (cC 1, 3), (cC 2, 9)]),
  .root (3, [(cS 2 3, 1), (cS 3 1, 1), (cS 5 4, 2), (cS 6 4, 1), (cR 0, 2), (cR 1, 1), (cR 2, 2)], [(cS 3 0, 1), (cS 3 5, 3), (cS 3 6, 2), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 5, 1), (cS 5 6, 1), (cS 6 2, 2), (cR 4, 1), (cR 6, 1)])
]
private def p5Certs2 : List P5Cert := [
  .root (1, [(cR 3, 1), (cR 5, 1)], [(cS 2 3, 1), (cR 1, 1), (cR 6, 1)]),
  .splitS0 [.leaf (16, [(cS 0 5, 6), (cS 1 5, 7), (cS 2 4, 6), (cS 2 6, 3), (cS 3 2, 3), (cS 3 3, 1), (cS 4 3, 2), (cS 4 4, 3), (cS 5 1, 3), (cS 5 2, 3), (cS 5 3, 1), (cS 6 0, 3), (cR 3, 7), (cR 4, 3), (cR 5, 7), (cC 0, 3), (cC 5, 3), (cC 6, 3)], [(cS 0 0, 5), (cS 0 1, 3), (cS 0 2, 9), (cS 0 3, 1), (cS 1 0, 4), (cS 1 1, 3), (cS 1 3, 14), (cS 2 0, 3), (cS 2 1, 10), (cS 2 2, 3), (cS 2 3, 2), (cS 3 1, 3), (cS 5 4, 1), (cS 6 2, 2), (cS 6 3, 2), (cS 6 4, 12), (cS 6 5, 2), (cR 0, 1), (cR 6, 1)]), .leaf (20, [(cS 0 6, 3), (cS 1 4, 7), (cS 1 5, 10), (cS 2 4, 7), (cS 2 6, 3), (cS 3 0, 3), (cS 3 3, 3), (cS 3 4, 2), (cS 3 6, 2), (cS 4 2, 2), (cS 4 3, 3), (cS 4 4, 3), (cS 5 0, 2), (cS 5 1, 4), (cS 5 2, 1), (cS 6 0, 4), (cR 3, 8), (cR 4, 4), (cR 5, 10), (cC 5, 3), (cC 6, 4)], [(cS 0 0, 3), (cS 0 1, 7), (cS 0 2, 1), (cS 0 3, 3), (cS 1 0, 11), (cS 1 2, 6), (cS 1 3, 6), (cS 2 0, 9), (cS 2 1, 5), (cS 2 2, 9), (cS 3 1, 6), (cS 6 2, 6), (cS 6 3, 4), (cS 6 4, 16), (cS 6 5, 4), (cR 0, 6)]), .leaf (12, [(cS 0 6, 1), (cS 1 4, 2), (cS 1 5, 10), (cS 2 4, 3), (cS 2 6, 1), (cS 3 6, 1), (cS 4 3, 1), (cS 4 5, 1), (cS 5 1, 1), (cS 6 0, 2), (cR 3, 9), (cR 4, 2), (cR 5, 9), (cC 6, 1)], [(cS 0 1, 1), (cS 0 2, 2), (cS 0 4, 1), (cS 1 0, 4), (cS 1 2, 2), (cS 1 3, 2), (cS 1 6, 1), (cS 2 0, 7), (cS 2 1, 3), (cS 2 2, 7), (cS 2 3, 5), (cS 3 1, 2), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 0, 7), (cR 6, 2)]), .leaf (5, [(cS 1 5, 3), (cS 3 4, 2), (cS 3 6, 1), (cS 4 2, 2), (cS 4 3, 2), (cS 5 1, 1), (cS 5 4, 1), (cR 3, 1), (cR 5, 2), (cC 0, 2), (cC 5, 2), (cC 6, 1)], [(cS 0 1, 1), (cS 0 4, 2), (cS 1 0, 2), (cS 1 2, 2), (cS 2 1, 3), (cS 2 3, 4), (cS 3 1, 2), (cS 6 2, 2), (cS 6 4, 1), (cR 0, 2), (cC 3, 1)])],
  .root (2, [(cS 1 5, 2), (cS 3 2, 1), (cS 3 5, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 5 5, 1), (cS 5 6, 1), (cR 3, 1), (cC 0, 1)], [(cS 0 1, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 2 2, 1), (cS 6 2, 1), (cS 6 5, 1), (cC 3, 1), (cC 4, 1)]),
  .root (8, [(cS 1 5, 8), (cS 2 0, 2), (cS 2 1, 2), (cS 2 6, 2), (cS 3 1, 4), (cS 4 1, 2), (cS 4 3, 6), (cS 5 0, 1), (cS 5 1, 3), (cS 5 2, 1), (cS 5 6, 1), (cS 6 0, 2), (cS 6 6, 2), (cR 3, 2), (cR 5, 2)], [(cS 0 1, 2), (cS 1 0, 4), (cS 1 2, 2), (cS 1 3, 2), (cS 2 2, 4), (cS 2 3, 4), (cS 3 4, 2), (cS 3 5, 2), (cS 3 6, 2), (cS 4 6, 4), (cS 5 3, 1), (cS 5 4, 3), (cS 5 5, 1), (cS 6 2, 2), (cS 6 3, 2), (cS 6 5, 2), (cR 0, 4), (cC 4, 2)]),
  .root (5, [(cS 0 5, 4), (cS 2 1, 1), (cS 2 5, 2), (cS 3 0, 1), (cS 3 1, 1), (cS 3 2, 1), (cS 3 6, 2), (cS 4 3, 1), (cS 4 4, 3), (cS 4 6, 1), (cS 5 0, 2), (cS 5 6, 2), (cS 6 0, 1), (cR 2, 2), (cR 4, 1), (cC 5, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 2 3, 3), (cS 3 3, 2), (cS 4 1, 2), (cS 5 2, 3), (cS 5 4, 2), (cS 6 4, 1), (cR 0, 2), (cR 1, 2), (cR 6, 2)]),
  .root (3, [(cS 0 5, 1), (cS 1 5, 2), (cS 2 1, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 4 2, 1), (cS 4 4, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 2 3, 3), (cS 6 4, 1), (cS 6 6, 1), (cR 0, 1), (cR 1, 1), (cR 5, 1), (cR 6, 1)]),
  .root (20, [(cS 2 3, 20), (cS 2 5, 2), (cS 3 0, 5), (cS 3 4, 9), (cS 3 5, 9), (cS 3 6, 9), (cS 4 0, 3), (cS 4 2, 8), (cS 4 3, 9), (cS 5 0, 5), (cS 5 5, 8), (cS 6 0, 3), (cS 6 1, 3), (cS 6 6, 3), (cR 4, 3), (cR 5, 9)], [(cS 0 1, 2), (cS 0 2, 6), (cS 0 6, 2), (cS 1 0, 3), (cS 1 4, 5), (cS 1 5, 3), (cS 2 1, 11), (cS 2 6, 6), (cS 3 1, 9), (cS 5 4, 2), (cS 6 3, 3), (cS 6 4, 6), (cS 6 5, 3), (cR 0, 3), (cR 1, 12), (cR 6, 9)]),
  .root (2, [(cS 1 1, 1), (cS 1 3, 1), (cS 4 1, 1), (cS 4 6, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 0, 1), (cS 6 6, 1), (cR 2, 1), (cR 3, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 1 0, 1), (cS 1 6, 1), (cS 4 3, 1), (cS 5 2, 1), (cS 6 3, 1), (cC 4, 1), (cC 5, 1)]),
  .root (60, [(cS 1 1, 8), (cS 2 1, 26), (cS 2 3, 60), (cS 3 1, 8), (cS 4 1, 8), (cS 4 3, 42), (cS 5 0, 8), (cS 5 2, 8), (cS 5 5, 7), (cS 5 6, 35), (cS 6 0, 26), (cS 6 6, 18), (cR 4, 18), (cC 1, 26)], [(cS 0 2, 16), (cS 1 0, 16), (cS 1 6, 18), (cS 2 5, 16), (cS 3 4, 26), (cS 3 6, 60), (cS 5 4, 17), (cS 6 2, 26), (cS 6 3, 26), (cS 6 5, 25), (cR 0, 18), (cR 1, 26), (cC 4, 18)]),
  .root (30, [(cS 2 1, 8), (cS 2 2, 10), (cS 2 3, 8), (cS 2 4, 10), (cS 3 0, 10), (cS 3 5, 8), (cS 3 6, 10), (cS 4 0, 1), (cS 4 1, 4), (cS 4 3, 6), (cS 4 4, 12), (cS 5 0, 5), (cS 5 5, 6), (cS 5 6, 12), (cS 6 0, 1), (cS 6 6, 12), (cR 2, 12), (cR 4, 12)], [(cS 0 1, 9), (cS 0 2, 9), (cS 0 3, 9), (cS 1 0, 9), (cS 1 4, 9), (cS 1 5, 9), (cS 1 6, 9), (cS 4 1, 3), (cS 4 2, 12), (cS 5 1, 5), (cS 5 2, 11), (cS 5 3, 7), (cS 6 0, 5), (cS 6 1, 3), (cS 6 4, 11), (cS 6 5, 7), (cR 1, 12), (cR 6, 12)]),
  .root (1, [(cR 2, 1), (cR 4, 1)], [(cR 1, 1), (cR 6, 1)]),
  .root (40, [(cS 0 4, 14), (cS 0 6, 14), (cS 1 3, 14), (cS 1 4, 4), (cS 1 5, 11), (cS 2 3, 26), (cS 2 5, 14), (cS 4 1, 10), (cS 4 6, 10), (cS 5 0, 11), (cS 5 1, 15), (cS 5 2, 11), (cS 5 6, 11), (cS 6 0, 11), (cR 3, 15), (cR 5, 4), (cC 5, 11), (cC 6, 4)], [(cS 0 0, 11), (cS 0 1, 18), (cS 0 2, 7), (cS 0 3, 8), (cS 1 0, 29), (cS 1 1, 4), (cS 2 1, 25), (cS 2 6, 11), (cS 3 0, 11), (cS 3 1, 4), (cS 4 3, 14), (cS 4 4, 26), (cS 6 2, 4), (cS 6 3, 10), (cS 6 4, 30), (cS 6 5, 11), (cC 2, 11)]),
  .root (2, [(cS 1 5, 2), (cS 2 3, 2), (cS 3 4, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 5 0, 1), (cR 5, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 0 4, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 5, 1), (cS 5 4, 1), (cR 6, 1), (cC 6, 1)]),
  .root (4, [(cS 0 5, 1), (cS 1 5, 2), (cS 2 3, 4), (cS 2 5, 1), (cS 3 5, 2), (cS 4 3, 1), (cS 4 4, 3), (cS 4 6, 1), (cS 5 0, 1), (cS 5 6, 2), (cS 6 6, 1), (cC 5, 1)], [(cS 0 0, 1), (cS 0 3, 1), (cS 0 4, 3), (cS 1 6, 1), (cS 2 0, 1), (cS 3 0, 1), (cS 5 3, 1), (cS 5 4, 3), (cS 6 5, 1), (cC 0, 2), (cC 1, 1), (cC 2, 3)]),
  .root (2, [(cS 1 5, 2), (cS 2 3, 2), (cS 3 4, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 2, 1), (cS 5 4, 1), (cR 4, 1)], [(cS 2 0, 1), (cS 2 1, 1), (cS 3 1, 1), (cR 0, 1), (cR 1, 1), (cR 5, 1), (cR 6, 1)]),
  .root (3, [(cS 0 5, 1), (cS 1 3, 1), (cS 1 5, 2), (cS 2 3, 1), (cS 3 1, 2), (cS 3 3, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 0, 1), (cR 2, 1)], [(cS 0 4, 1), (cS 1 0, 2), (cS 1 2, 2), (cS 3 4, 2), (cS 3 6, 2), (cS 5 3, 1), (cS 5 4, 1), (cS 5 5, 1), (cS 6 2, 1), (cR 0, 1), (cR 4, 1), (cR 6, 1)]),
  .root (6, [(cS 0 5, 2), (cS 1 3, 4), (cS 1 4, 2), (cS 1 5, 2), (cS 1 6, 2), (cS 4 1, 2), (cS 4 6, 3), (cS 5 0, 3), (cS 5 6, 3), (cR 2, 2), (cR 3, 4)], [(cS 0 0, 3), (cS 0 1, 1), (cS 0 6, 1), (cS 1 0, 2), (cS 1 1, 2), (cS 4 2, 3), (cS 4 4, 6), (cS 5 1, 1), (cS 6 3, 1), (cS 6 4, 3), (cS 6 5, 1), (cR 6, 2), (cC 2, 3)]),
  .root (2, [(cS 0 5, 1), (cS 1 3, 1), (cS 1 5, 1), (cS 4 1, 1), (cS 4 2, 1), (cS 4 6, 1), (cR 2, 1), (cR 3, 1)], [(cS 1 0, 1), (cS 1 2, 1), (cS 4 4, 2), (cR 0, 1), (cR 5, 1), (cR 6, 1)]),
  .root (2, [(cS 0 5, 1), (cS 1 5, 1), (cS 2 3, 1), (cS 3 1, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 6, 1), (cS 6 0, 1), (cR 2, 1)], [(cS 0 4, 1), (cS 1 0, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 0, 1), (cS 5 4, 1), (cR 0, 1), (cR 5, 1), (cC 2, 1)]),
  .root (3, [(cS 0 5, 1), (cS 1 5, 2), (cS 2 3, 2), (cS 3 1, 2), (cS 4 1, 1), (cS 4 2, 1), (cS 4 3, 2), (cS 4 4, 1), (cS 5 1, 1), (cR 2, 1)], [(cS 0 3, 1), (cS 1 1, 1), (cS 1 2, 1), (cS 3 5, 1), (cS 4 6, 1), (cS 5 5, 1), (cS 6 2, 1), (cS 6 3, 1), (cR 0, 1), (cR 6, 1), (cC 0, 1), (cC 4, 1), (cC 6, 1)]),
  .root (1, [(cS 4 4, 1), (cR 1, 1), (cR 3, 1)], [(cR 0, 1), (cR 5, 1)]),
  .root (3, [(cS 0 1, 2), (cS 0 6, 2), (cS 3 4, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 5 5, 1), (cR 3, 1), (cR 5, 2), (cC 0, 1)], [(cS 0 3, 2), (cS 0 5, 1), (cS 1 2, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 1, 1), (cS 2 3, 2), (cS 3 1, 1), (cS 5 4, 1), (cS 6 2, 1), (cS 6 4, 2), (cR 2, 1)]),
  .root (1, [(cC 1, 1), (cC 6, 1)], [(cC 3, 1), (cC 5, 1)]),
  .root (2, [(cS 4 3, 1), (cS 4 4, 1), (cC 0, 1), (cC 1, 1), (cC 2, 1), (cC 6, 1)], [(cS 0 3, 1), (cS 1 5, 1), (cS 2 3, 1), (cS 3 5, 1), (cS 6 4, 1), (cC 3, 1), (cC 5, 1)]),
  .root (4, [(cS 0 1, 1), (cS 1 1, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 3 4, 3), (cS 3 5, 1), (cS 4 3, 1), (cS 5 4, 3), (cS 5 5, 1), (cC 0, 1), (cC 1, 2), (cC 6, 3)], [(cS 0 3, 2), (cS 1 3, 1), (cS 1 5, 4), (cS 2 3, 2), (cS 3 3, 1), (cS 4 2, 1), (cS 5 1, 1), (cS 5 2, 2), (cS 6 2, 1), (cS 6 4, 3), (cS 6 5, 1), (cC 3, 1)]),
  .root (2, [(cS 0 6, 1), (cS 1 0, 1), (cS 1 1, 1), (cR 2, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 1 3, 1), (cS 1 5, 2), (cS 2 3, 1), (cS 3 3, 1), (cS 6 4, 1), (cS 6 6, 1), (cR 6, 1)]),
  .root (20, [(cS 0 0, 6), (cS 0 5, 6), (cS 1 0, 3), (cS 1 5, 7), (cS 2 4, 9), (cS 2 6, 3), (cS 3 5, 4), (cS 3 6, 3), (cS 4 2, 2), (cS 4 6, 3), (cS 5 1, 9), (cS 5 2, 9), (cS 5 6, 7), (cS 6 1, 3), (cC 0, 11), (cC 5, 7), (cC 6, 3)], [(cS 0 1, 3), (cS 0 2, 9), (cS 0 4, 3), (cS 1 2, 6), (cS 1 3, 3), (cS 2 1, 10), (cS 2 2, 2), (cS 2 3, 3), (cS 3 1, 10), (cS 3 2, 6), (cS 3 3, 3), (cS 4 3, 3), (cS 5 4, 3), (cS 6 2, 6), (cS 6 4, 3), (cS 6 5, 4), (cC 2, 2), (cC 3, 4), (cC 4, 10)]),
  .root (4, [(cS 1 0, 4), (cS 1 5, 3), (cS 4 3, 1), (cS 5 1, 1), (cS 6 0, 3), (cS 6 1, 1), (cS 6 6, 1), (cR 4, 3), (cC 5, 1)], [(cS 0 2, 2), (cS 1 1, 2), (cS 1 3, 3), (cS 2 1, 1), (cS 3 6, 1), (cS 4 6, 1), (cS 6 2, 2), (cS 6 3, 1), (cS 6 4, 2), (cS 6 5, 2), (cR 2, 1), (cR 3, 2), (cC 3, 1)]),
  .root (3, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 5, 1), (cS 2 5, 1), (cS 2 6, 1), (cS 3 5, 1), (cS 4 3, 1), (cS 4 4, 2), (cS 4 6, 1), (cS 5 6, 1), (cC 0, 2), (cC 5, 1)], [(cS 0 3, 1), (cS 1 2, 1), (cS 1 4, 1), (cS 2 3, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 5 2, 1), (cS 6 2, 1), (cS 6 4, 2), (cS 6 5, 1), (cC 1, 2), (cC 3, 1)]),
  .splitS0 [.leaf (4, [(cS 0 0, 1), (cS 0 1, 2), (cS 0 5, 1), (cS 1 0, 3), (cS 1 5, 3), (cS 2 4, 1), (cS 2 6, 1), (cR 3, 3), (cR 4, 1), (cR 5, 3)], [(cS 0 2, 2), (cS 0 3, 1), (cS 1 3, 3), (cS 2 1, 4), (cS 2 3, 1), (cS 6 4, 3), (cS 6 6, 3), (cR 6, 1)]), .leaf (20, [(cS 0 0, 5), (cS 0 1, 9), (cS 0 5, 7), (cS 1 0, 4), (cS 1 4, 9), (cS 1 5, 2), (cS 1 6, 9), (cS 2 0, 5), (cS 2 5, 8), (cS 3 6, 3), (cS 4 3, 2), (cS 4 4, 3), (cS 5 1, 2), (cS 5 2, 3), (cS 5 5, 2), (cR 1, 2), (cR 3, 12), (cR 4, 6), (cR 5, 9)], [(cS 0 2, 8), (cS 1 2, 2), (cS 1 3, 10), (cS 2 1, 17), (cS 2 3, 8), (cS 3 1, 3), (cS 5 0, 3), (cS 5 6, 3), (cS 6 3, 6), (cS 6 4, 8), (cS 6 5, 6), (cS 6 6, 9), (cR 6, 6)]), .leaf (24, [(cS 0 0, 5), (cS 0 1, 8), (cS 0 4, 1), (cS 0 5, 6), (cS 1 0, 11), (cS 1 4, 6), (cS 1 5, 8), (cS 1 6, 8), (cS 2 4, 7), (cS 2 6, 5), (cS 3 0, 3), (cS 3 4, 6), (cS 3 6, 8), (cS 4 2, 4), (cS 4 3, 6), (cS 4 5, 1), (cR 3, 8), (cR 4, 6), (cR 5, 14), (cC 5, 3)], [(cS 0 2, 8), (cS 0 3, 6), (cS 0 4, 8), (cS 1 2, 8), (cS 1 3, 3), (cS 2 0, 16), (cS 2 2, 16), (cS 2 3, 8), (cS 3 1, 8), (cS 5 0, 5), (cS 6 5, 5), (cS 6 6, 8), (cR 6, 11)]), .leaf (12, [(cS 0 0, 5), (cS 0 5, 2), (cS 1 0, 2), (cS 1 5, 3), (cS 1 6, 3), (cS 2 4, 2), (cS 2 6, 2), (cS 3 3, 4), (cS 3 4, 2), (cS 3 5, 1), (cS 3 6, 5), (cS 4 2, 5), (cS 4 3, 1), (cS 5 1, 4), (cS 5 2, 1), (cS 5 3, 3), (cS 5 4, 3), (cR 4, 2), (cC 0, 5), (cC 4, 3), (cC 5, 4)], [(cS 0 2, 7), (cS 0 4, 9), (cS 1 2, 5), (cS 2 0, 5), (cS 2 1, 2), (cS 2 2, 5), (cS 2 3, 7), (cS 3 1, 5), (cS 5 0, 1), (cS 5 2, 2), (cS 5 6, 6), (cS 6 2, 3), (cS 6 3, 1), (cS 6 5, 1), (cS 6 6, 3), (cR 6, 2)]), .leaf (20, [(cS 0 0, 9), (cS 0 5, 6), (cS 1 0, 5), (cS 1 4, 7), (cS 1 5, 1), (cS 1 6, 7), (cS 2 4, 2), (cS 2 5, 4), (cS 2 6, 2), (cS 3 2, 2), (cS 3 3, 5), (cS 3 6, 4), (cS 4 2, 3), (cS 4 4, 5), (cS 5 1, 6), (cS 5 2, 9), (cS 5 3, 6), (cS 5 4, 7), (cR 3, 8), (cR 4, 2), (cC 0, 6), (cC 5, 6)], [(cS 0 2, 15), (cS 1 2, 2), (cS 1 3, 13), (cS 2 1, 15), (cS 2 3, 5), (cS 3 1, 2), (cS 5 0, 3), (cS 5 6, 12), (cS 6 3, 3), (cS 6 4, 15), (cS 6 5, 3), (cS 6 6, 3), (cR 6, 2), (cC 1, 3)]), .leaf (3, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 5, 1), (cS 1 0, 1), (cS 1 5, 2), (cS 1 6, 1), (cS 2 5, 1), (cS 2 6, 1), (cR 3, 2), (cR 4, 1), (cR 5, 2)], [(cS 0 2, 2), (cS 0 4, 2), (cS 1 3, 1), (cS 2 1, 3), (cS 2 3, 2), (cS 3 3, 1), (cS 6 6, 2), (cR 6, 1)])],
  .root (2, [(cS 1 4, 1), (cS 1 5, 1), (cC 0, 1), (cC 1, 1), (cC 2, 1), (cC 6, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 2 3, 1), (cS 3 5, 1), (cS 4 5, 1), (cS 6 5, 1), (cC 3, 1), (cC 4, 1)]),
  .root (5, [(cS 0 0, 1), (cS 1 1, 1), (cS 1 5, 2), (cS 2 0, 1), (cS 2 1, 4), (cS 3 1, 1), (cS 3 4, 1), (cS 3 5, 1), (cS 4 1, 1), (cS 4 2, 3), (cS 4 6, 1), (cS 6 0, 1), (cC 0, 3), (cC 5, 3), (cC 6, 1)], [(cS 0 1, 1), (cS 0 2, 4), (cS 0 4, 2), (cS 1 3, 2), (cS 2 3, 2), (cS 3 3, 2), (cS 4 3, 2), (cS 5 1, 1), (cS 5 2, 4), (cS 5 4, 2), (cS 6 4, 2), (cS 6 5, 1), (cC 3, 1)]),
  .root (4, [(cS 5 1, 2), (cR 1, 2), (cR 3, 2), (cC 0, 2), (cC 2, 2), (cC 5, 2)], [(cS 0 1, 2), (cS 0 2, 2), (cS 0 4, 1), (cS 1 3, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 4 4, 1), (cS 5 4, 1), (cS 5 6, 2), (cS 6 4, 1), (cS 6 5, 2), (cS 6 6, 2), (cC 3, 2)]),
  .root (2, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 0, 1), (cS 1 5, 1), (cS 2 1, 1), (cS 4 4, 2), (cS 5 6, 1), (cS 6 0, 1), (cR 2, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 1 3, 1), (cS 4 1, 1), (cS 4 6, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 3, 1), (cC 3, 1)]),
  .splitS0 [.leaf (16, [(cS 0 0, 7), (cS 0 5, 5), (cS 0 6, 1), (cS 1 0, 4), (cS 1 5, 6), (cS 1 6, 1), (cS 2 6, 3), (cS 3 0, 4), (cS 3 5, 2), (cS 4 1, 5), (cS 4 3, 9), (cS 4 4, 2), (cS 5 1, 2), (cS 5 2, 1), (cS 5 3, 2), (cS 5 4, 1), (cR 1, 3), (cR 2, 5), (cR 3, 3), (cC 1, 4), (cC 2, 4), (cC 4, 2)], [(cS 0 2, 3), (cS 0 3, 3), (cS 0 4, 3), (cS 0 5, 3), (cS 1 2, 2), (cS 1 3, 10), (cS 2 3, 4), (cS 2 4, 2), (cS 3 5, 2), (cS 3 6, 1), (cS 4 5, 5), (cS 4 6, 8), (cS 5 0, 5), (cS 5 4, 6), (cS 5 6, 3), (cS 6 3, 5), (cS 6 5, 5), (cS 6 6, 3), (cR 6, 5)]), .leaf (10, [(cS 0 0, 4), (cS 0 5, 4), (cS 0 6, 1), (cS 1 0, 2), (cS 1 1, 1), (cS 1 4, 4), (cS 1 5, 2), (cS 1 6, 3), (cS 2 6, 1), (cS 3 0, 3), (cS 3 4, 2), (cS 4 1, 3), (cS 4 2, 1), (cS 4 3, 6), (cS 4 4, 3), (cS 5 2, 1), (cS 5 4, 1), (cR 2, 4), (cR 3, 1), (cC 1, 3), (cC 2, 2)], [(cS 0 2, 1), (cS 0 3, 2), (cS 0 5, 1), (cS 1 2, 3), (cS 1 3, 4), (cS 2 3, 3), (cS 3 6, 1), (cS 4 5, 1), (cS 4 6, 5), (cS 5 0, 4), (cS 5 4, 2), (cS 5 6, 1), (cS 6 3, 3), (cS 6 4, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 6, 4), (cC 5, 3)]), .leaf (2, [(cS 0 0, 1), (cS 1 5, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 4 1, 1), (cS 4 3, 1), (cS 5 2, 1), (cS 5 4, 1), (cR 1, 1), (cR 3, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 2 2, 1), (cS 2 3, 1), (cS 4 6, 1), (cS 5 0, 1), (cR 6, 1), (cC 5, 1)]), .leaf (6, [(cS 0 0, 3), (cS 0 5, 2), (cS 1 1, 1), (cS 1 5, 1), (cS 1 6, 2), (cS 2 1, 3), (cS 2 5, 2), (cS 2 6, 3), (cS 3 0, 3), (cS 3 2, 2), (cS 4 1, 2), (cS 4 2, 1), (cS 4 3, 3), (cS 4 4, 1), (cS 5 2, 2), (cR 1, 1), (cC 1, 1), (cC 4, 2)], [(cS 0 2, 4), (cS 0 4, 3), (cS 1 2, 2), (cS 2 3, 4), (cS 3 2, 2), (cS 3 5, 2), (cS 4 5, 1), (cS 4 6, 3), (cS 5 0, 2), (cS 5 5, 1), (cS 6 3, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 5, 1), (cR 6, 2)]), .leaf (5, [(cS 0 0, 2), (cS 0 5, 2), (cS 1 0, 1), (cS 1 5, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 4 1, 3), (cS 4 3, 3), (cS 4 4, 1), (cS 5 2, 2), (cS 5 3, 1), (cR 1, 2), (cR 2, 2), (cR 3, 1)], [(cS 0 2, 2), (cS 0 4, 1), (cS 1 2, 3), (cS 1 3, 1), (cS 2 3, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 5, 1), (cS 4 6, 2), (cS 5 0, 2), (cS 5 4, 1), (cS 5 5, 1), (cS 5 6, 1), (cR 6, 3), (cC 4, 1)]), .leaf (6, [(cS 0 0, 3), (cS 1 0, 1), (cS 1 1, 2), (cS 1 5, 4), (cS 1 6, 2), (cS 2 0, 1), (cS 2 1, 1), (cS 2 6, 2), (cS 3 0, 1), (cS 4 1, 2), (cS 4 3, 2), (cS 5 2, 1), (cS 5 3, 1), (cS 5 4, 1), (cR 3, 2), (cC 1, 1), (cC 2, 2), (cC 4, 2)], [(cS 0 2, 1), (cS 0 3, 3), (cS 0 4, 1), (cS 1 3, 2), (cS 2 3, 6), (cS 4 5, 1), (cS 4 6, 3), (cS 5 0, 3), (cS 6 5, 1), (cS 6 6, 1), (cR 6, 2), (cC 5, 2)])],
  .splitS0 [.leaf (2, [(cS 4 3, 1), (cS 4 4, 1), (cS 4 6, 1), (cS 5 5, 1), (cR 0, 1), (cR 1, 1), (cR 2, 1), (cR 3, 1)], [(cS 1 3, 2), (cS 4 1, 1), (cS 5 0, 1), (cS 5 2, 1), (cS 6 3, 1), (cS 6 5, 1), (cR 6, 1)]), .leaf (20, [(cS 0 0, 1), (cS 0 5, 5), (cS 1 0, 9), (cS 1 5, 3), (cS 2 1, 2), (cS 2 2, 2), (cS 3 0, 2), (cS 3 4, 2), (cS 3 6, 2), (cS 4 3, 9), (cS 4 4, 11), (cS 4 5, 7), (cS 4 6, 11), (cR 0, 5), (cR 1, 5), (cR 2, 11), (cR 3, 5), (cC 5, 2)], [(cS 1 2, 8), (cS 1 3, 8), (cS 4 0, 2), (cS 4 1, 11), (cS 4 2, 2), (cS 5 0, 7), (cS 5 2, 5), (cS 6 3, 2), (cS 6 4, 2), (cS 6 5, 4), (cS 6 6, 2), (cR 6, 14), (cC 2, 2), (cC 3, 2)]), .leaf (20, [(cS 0 0, 9), (cS 0 1, 4), (cS 0 5, 8), (cS 1 0, 1), (cS 1 5, 2), (cS 1 6, 4), (cS 2 1, 12), (cS 2 5, 6), (cS 2 6, 9), (cS 3 0, 7), (cS 3 1, 3), (cS 3 4, 5), (cS 4 3, 7), (cS 4 4, 1), (cS 4 5, 10), (cS 4 6, 10), (cS 5 3, 3), (cS 5 4, 5), (cR 1, 6), (cR 2, 2), (cR 3, 3), (cC 4, 4)], [(cS 0 3, 9), (cS 0 4, 1), (cS 1 2, 1), (cS 2 3, 9), (cS 3 3, 1), (cS 4 1, 7), (cS 5 0, 10), (cS 5 1, 3), (cS 6 4, 3), (cS 6 5, 9), (cS 6 6, 4), (cR 6, 7), (cC 2, 10)]), .leaf (10, [(cS 0 0, 6), (cS 0 5, 1), (cS 1 0, 3), (cS 1 4, 2), (cS 1 5, 2), (cS 1 6, 3), (cS 2 1, 5), (cS 2 2, 3), (cS 2 6, 2), (cS 3 0, 5), (cS 3 4, 2), (cS 3 5, 2), (cS 3 6, 1), (cS 4 4, 4), (cS 4 6, 1), (cS 5 3, 3), (cR 1, 1), (cR 2, 1), (cR 3, 1), (cR 4, 2), (cC 4, 1), (cC 5, 3)], [(cS 0 1, 2), (cS 0 2, 3), (cS 0 4, 4), (cS 1 2, 2), (cS 2 3, 3), (cS 3 2, 2), (cS 4 1, 2), (cS 5 0, 3), (cS 5 1, 5), (cS 5 6, 4), (cS 6 4, 2), (cS 6 5, 2), (cS 6 6, 2), (cR 6, 2), (cC 2, 3), (cC 3, 2)]), .leaf (24, [(cS 0 0, 9), (cS 0 5, 8), (cS 1 0, 7), (cS 1 5, 5), (cS 2 1, 3), (cS 2 2, 3), (cS 3 0, 3), (cS 3 4, 3), (cS 3 6, 3), (cS 4 3, 6), (cS 4 4, 16), (cS 4 6, 8), (cS 5 5, 3), (cR 1, 8), (cR 2, 10), (cR 3, 8), (cR 4, 2), (cC 5, 3)], [(cS 0 1, 2), (cS 0 2, 6), (cS 0 4, 6), (cS 1 2, 13), (cS 1 3, 8), (cS 2 3, 1), (cS 4 0, 2), (cS 4 1, 9), (cS 4 2, 3), (cS 5 0, 3), (cS 5 1, 2), (cS 5 6, 1), (cS 6 4, 3), (cS 6 5, 2), (cS 6 6, 2), (cR 5, 8), (cR 6, 13), (cC 2, 3), (cC 3, 2)]), .leaf (5, [(cS 0 0, 2), (cS 1 0, 1), (cS 1 1, 2), (cS 1 5, 2), (cS 1 6, 2), (cS 2 1, 2), (cS 2 6, 2), (cS 3 0, 1), (cS 4 3, 1), (cS 4 6, 2), (cS 5 3, 1), (cS 5 4, 1), (cS 5 5, 1), (cR 3, 2), (cC 2, 1), (cC 4, 2), (cC 5, 1)], [(cS 0 2, 1), (cS 0 3, 2), (cS 0 4, 1), (cS 1 3, 1), (cS 2 3, 4), (cS 3 3, 1), (cS 4 1, 2), (cS 5 0, 2), (cS 5 1, 1), (cS 5 2, 2), (cS 5 6, 1), (cS 6 1, 1), (cS 6 5, 2), (cS 6 6, 1), (cR 0, 1), (cR 6, 1)])],
  .root (4, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 6, 1), (cS 1 3, 1), (cS 2 3, 2), (cS 2 4, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 3 6, 2), (cS 4 5, 1), (cS 5 1, 1), (cS 5 6, 1), (cR 5, 1), (cC 0, 1), (cC 1, 1), (cC 2, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 1 5, 2), (cS 1 6, 2), (cS 2 1, 2), (cS 3 1, 2), (cS 4 3, 2), (cS 6 3, 2), (cS 6 5, 2), (cC 4, 2)]),
  .root (30, [(cS 0 0, 2), (cS 0 1, 14), (cS 0 6, 14), (cS 1 0, 14), (cS 2 3, 30), (cS 4 1, 10), (cS 4 2, 1), (cS 4 3, 26), (cS 4 4, 1), (cS 5 0, 10), (cS 5 1, 7), (cS 5 2, 9), (cS 5 6, 17), (cS 6 0, 11), (cS 6 1, 3), (cS 6 6, 3), (cR 4, 3)], [(cS 0 3, 14), (cS 0 5, 3), (cS 1 4, 1), (cS 1 6, 14), (cS 2 1, 14), (cS 2 5, 3), (cS 3 0, 14), (cS 3 1, 3), (cS 3 5, 4), (cS 3 6, 16), (cS 5 3, 5), (cS 5 4, 4), (cS 6 3, 3), (cS 6 4, 5), (cR 1, 3), (cC 2, 13), (cC 4, 13), (cC 5, 10)]),
  .root (4, [(cS 0 0, 1), (cS 0 1, 2), (cS 0 6, 2), (cS 1 0, 1), (cS 2 3, 3), (cS 3 5, 3), (cS 4 3, 1), (cS 4 4, 3), (cS 4 6, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 5 6, 2), (cS 6 0, 1), (cR 2, 1)], [(cS 0 3, 2), (cS 1 4, 1), (cS 1 5, 2), (cS 1 6, 1), (cS 2 1, 1), (cS 3 0, 3), (cS 3 2, 2), (cS 4 1, 1), (cS 5 1, 2), (cS 5 3, 2), (cS 6 2, 1), (cS 6 4, 2), (cS 6 5, 2), (cR 1, 1), (cC 2, 1)]),
  .root (8, [(cS 0 0, 5), (cS 1 0, 3), (cS 1 2, 1), (cS 2 3, 5), (cS 2 4, 3), (cS 2 5, 4), (cS 2 6, 1), (cS 3 0, 1), (cS 3 6, 2), (cS 4 3, 3), (cS 4 4, 2), (cS 4 5, 3), (cS 5 1, 3), (cS 5 2, 1), (cS 5 4, 1), (cR 3, 1), (cR 4, 2), (cC 2, 2)], [(cS 0 2, 3), (cS 1 3, 3), (cS 1 4, 3), (cS 1 5, 4), (cS 2 1, 4), (cS 2 6, 1), (cS 3 1, 4), (cS 5 0, 3), (cS 5 4, 1), (cS 5 6, 1), (cS 6 3, 3), (cS 6 4, 2), (cS 6 5, 3), (cR 0, 1), (cR 1, 1), (cR 6, 2), (cC 6, 2)]),
  .root (2, [(cS 2 3, 2), (cC 0, 1), (cC 1, 1), (cC 2, 1), (cC 6, 1)], [(cS 0 3, 1), (cS 1 5, 1), (cS 3 6, 2), (cS 4 3, 1), (cS 6 3, 1), (cC 4, 1), (cC 5, 1)]),
  .root (5, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 3, 4), (cS 1 1, 1), (cS 1 2, 1), (cS 2 3, 4), (cS 3 1, 2), (cS 3 5, 1), (cS 4 6, 1), (cS 5 6, 1), (cR 2, 1), (cC 0, 1), (cC 1, 2), (cC 6, 3)], [(cS 1 5, 3), (cS 4 2, 3), (cS 4 3, 2), (cS 4 4, 2), (cS 5 1, 2), (cS 6 2, 3), (cS 6 3, 2), (cS 6 4, 2), (cC 4, 1), (cC 5, 2)]),
  .root (24, [(cS 0 0, 4), (cS 0 6, 1), (cS 1 0, 2), (cS 1 3, 7), (cS 1 6, 6), (cS 2 3, 3), (cS 3 3, 7), (cS 3 6, 6), (cS 4 1, 6), (cS 4 2, 2), (cS 4 6, 7), (cS 5 2, 6), (cR 1, 7), (cR 2, 7), (cR 3, 7), (cC 1, 11), (cC 6, 4)], [(cS 0 2, 4), (cS 0 3, 8), (cS 1 5, 14), (cS 2 5, 2), (cS 3 4, 1), (cS 4 3, 8), (cS 4 4, 15), (cS 5 0, 7), (cS 5 3, 8), (cS 5 4, 1), (cS 5 6, 6), (cS 6 3, 3), (cS 6 4, 5), (cS 6 5, 3), (cS 6 6, 6), (cR 0, 2), (cR 6, 7), (cC 5, 8)]),
  .root (4, [(cS 0 1, 1), (cS 0 6, 1), (cS 1 0, 2), (cS 1 2, 2), (cS 2 0, 1), (cS 2 1, 2), (cS 2 3, 4), (cS 3 2, 2), (cS 4 3, 2), (cS 4 4, 2), (cS 5 6, 3), (cS 6 0, 2), (cC 0, 1)], [(cS 0 2, 1), (cS 0 3, 3), (cS 0 4, 1), (cS 0 5, 2), (cS 1 5, 1), (cS 2 5, 2), (cS 3 0, 1), (cS 3 4, 1), (cS 3 6, 3), (cS 4 1, 2), (cS 5 1, 1), (cS 5 2, 1), (cS 5 3, 1), (cS 5 4, 3), (cS 6 2, 2), (cC 5, 1)]),
  .splitS0 [.leaf (2, [(cS 2 2, 1), (cS 2 4, 1), (cS 4 2, 1), (cS 4 4, 1), (cC 0, 2), (cC 2, 1), (cC 4, 1)], [(cS 0 2, 1), (cS 0 4, 1), (cS 6 2, 1), (cS 6 4, 1), (cC 6, 2)]), .leaf (5, [(cS 0 0, 1), (cS 1 6, 1), (cS 2 3, 2), (cS 2 4, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 4 1, 1), (cS 4 3, 2), (cS 4 4, 3), (cS 5 2, 1), (cS 6 0, 2), (cR 1, 1), (cR 2, 1), (cC 0, 2), (cC 1, 1), (cC 2, 2)], [(cS 0 2, 1), (cS 0 3, 2), (cS 0 5, 1), (cS 1 4, 2), (cS 1 5, 1), (cS 2 5, 1), (cS 3 5, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 4, 1), (cS 5 6, 1), (cS 6 3, 1), (cS 6 4, 2), (cR 6, 1), (cC 5, 1), (cC 6, 2)]), .leaf (24, [(cS 0 0, 8), (cS 1 0, 2), (cS 1 4, 7), (cS 2 2, 2), (cS 2 4, 3), (cS 3 1, 8), (cS 3 3, 6), (cS 3 4, 7), (cS 4 1, 8), (cS 4 3, 10), (cS 4 4, 14), (cS 5 1, 2), (cS 5 2, 6), (cS 6 0, 8), (cR 1, 6), (cR 2, 8), (cC 0, 8), (cC 2, 8)], [(cS 0 2, 10), (cS 0 3, 5), (cS 0 4, 6), (cS 0 5, 2), (cS 2 5, 3), (cS 3 6, 5), (cS 5 0, 3), (cS 5 4, 4), (cS 6 2, 6), (cS 6 3, 3), (cS 6 4, 14), (cR 5, 3), (cC 5, 3), (cC 6, 19)]), .leaf (30, [(cS 0 0, 17), (cS 1 2, 5), (cS 1 3, 2), (cS 1 4, 11), (cS 1 6, 6), (cS 2 0, 7), (cS 2 3, 6), (cS 2 4, 4), (cS 3 1, 5), (cS 3 3, 8), (cS 3 4, 5), (cS 4 1, 7), (cS 4 3, 12), (cS 4 4, 15), (cS 5 2, 5), (cS 5 3, 3), (cS 6 0, 3), (cR 2, 7), (cC 0, 10), (cC 1, 8), (cC 2, 10)], [(cS 0 2, 7), (cS 0 3, 12), (cS 0 4, 5), (cS 0 5, 3), (cS 1 5, 5), (cS 2 5, 3), (cS 3 5, 5), (cS 4 6, 3), (cS 5 0, 5), (cS 5 4, 9), (cS 5 6, 5), (cS 6 2, 2), (cS 6 3, 5), (cS 6 4, 11), (cR 6, 5), (cC 5, 6), (cC 6, 17)]), .leaf (2, [(cS 2 4, 1), (cS 4 4, 1), (cC 0, 2), (cC 2, 2), (cC 4, 1)], [(cS 0 3, 2), (cS 0 5, 1), (cS 1 5, 1), (cS 3 6, 1), (cS 5 6, 1), (cS 6 4, 1), (cC 6, 1)]), .leaf (6, [(cS 0 0, 2), (cS 1 2, 1), (cS 2 0, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 1, 2), (cS 3 2, 1), (cS 3 4, 2), (cS 4 1, 2), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 2), (cS 5 2, 1), (cS 5 4, 2), (cS 6 0, 2), (cR 1, 2), (cR 2, 1), (cC 0, 2), (cC 2, 2), (cC 3, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 0 4, 2), (cS 5 0, 2), (cS 6 2, 3), (cS 6 3, 1), (cS 6 4, 2), (cC 5, 2), (cC 6, 4)]), .leaf (6, [(cS 0 0, 2), (cS 1 4, 1), (cS 1 6, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 1, 1), (cS 3 3, 2), (cS 4 1, 1), (cS 4 3, 1), (cS 4 4, 2), (cS 5 2, 1), (cS 5 3, 1), (cS 5 4, 2), (cS 6 0, 1), (cS 6 2, 1), (cR 1, 1), (cR 2, 1), (cC 0, 3), (cC 1, 1), (cC 2, 3), (cC 4, 1)], [(cS 0 2, 1), (cS 0 3, 5), (cS 0 4, 1), (cS 0 5, 2), (cS 1 5, 2), (cS 3 5, 2), (cS 5 0, 1), (cS 5 6, 2), (cS 6 4, 2), (cC 5, 1), (cC 6, 3)]), .leaf (20, [(cS 0 0, 5), (cS 0 6, 3), (cS 1 2, 2), (cS 2 0, 5), (cS 2 3, 11), (cS 2 6, 3), (cS 3 1, 2), (cS 4 1, 3), (cS 4 3, 2), (cS 4 4, 9), (cC 0, 12), (cC 1, 3), (cC 2, 15), (cC 3, 3), (cC 4, 6)], [(cS 0 3, 20), (cS 0 5, 8), (cS 1 5, 9), (cS 2 5, 8), (cS 3 5, 9), (cS 4 6, 8), (cS 5 0, 3), (cS 5 4, 2), (cS 5 6, 9), (cS 6 4, 6), (cS 6 6, 6), (cR 6, 3), (cC 5, 3)]), .leaf (5, [(cS 0 0, 1), (cS 0 6, 1), (cS 1 2, 1), (cS 2 0, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 1, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 2), (cS 5 2, 1), (cS 5 4, 1), (cR 2, 1), (cC 0, 3), (cC 1, 1), (cC 2, 2), (cC 3, 1), (cC 4, 1)], [(cS 0 2, 1), (cS 0 3, 3), (cS 0 5, 2), (cS 1 5, 2), (cS 2 5, 2), (cS 3 5, 2), (cS 4 6, 2), (cS 5 0, 1), (cS 5 6, 2), (cS 6 4, 1), (cS 6 6, 1), (cR 6, 1), (cC 5, 1)])],
  .root (20, [(cS 0 0, 11), (cS 0 1, 3), (cS 1 0, 6), (cS 1 2, 5), (cS 1 6, 3), (cS 2 1, 3), (cS 2 3, 3), (cS 2 4, 5), (cS 3 0, 5), (cS 3 2, 5), (cS 3 5, 3), (cS 3 6, 6), (cS 4 3, 3), (cS 4 4, 8), (cS 4 5, 3), (cR 2, 12), (cR 4, 9)], [(cS 0 2, 12), (cS 0 3, 8), (cS 0 4, 9), (cS 1 4, 3), (cS 1 5, 17), (cS 1 6, 3), (cS 4 0, 3), (cS 4 1, 3), (cS 4 2, 3), (cS 5 1, 5), (cS 5 3, 8), (cS 6 1, 3), (cS 6 5, 8), (cS 6 6, 9), (cR 5, 9), (cR 6, 3)]),
  .root (3, [(cS 0 0, 2), (cS 0 5, 1), (cS 1 5, 1), (cS 2 3, 2), (cS 2 5, 1), (cS 3 3, 1), (cS 4 1, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 0, 1), (cS 6 6, 1), (cR 1, 1)], [(cS 0 2, 2), (cS 0 4, 1), (cS 2 0, 1), (cS 2 1, 2), (cS 5 3, 1), (cS 5 5, 1), (cS 6 2, 1), (cS 6 4, 1), (cR 3, 1), (cR 4, 1), (cC 4, 1), (cC 6, 1)]),
  .root (24, [(cS 0 0, 3), (cS 1 0, 1), (cS 1 4, 4), (cS 2 2, 1), (cS 2 3, 13), (cS 2 5, 2), (cS 3 3, 5), (cS 3 4, 1), (cS 3 5, 8), (cS 4 6, 4), (cS 5 6, 8), (cS 6 0, 6), (cR 0, 7), (cR 1, 5), (cR 2, 5), (cC 0, 8), (cC 5, 8), (cC 6, 4)], [(cS 0 2, 5), (cS 0 4, 8), (cS 2 0, 1), (cS 2 1, 5), (cS 3 0, 8), (cS 3 1, 11), (cS 4 1, 5), (cS 4 3, 16), (cS 4 4, 8), (cS 5 1, 11), (cS 5 4, 8), (cS 6 2, 11), (cS 6 3, 6), (cS 6 4, 10), (cS 6 5, 6), (cC 2, 8)]),
  .root (8, [(cS 0 0, 4), (cS 1 0, 2), (cS 1 5, 6), (cS 2 3, 2), (cS 3 3, 1), (cS 3 5, 3), (cS 4 1, 1), (cS 4 6, 4), (cS 5 1, 6), (cS 5 2, 1), (cR 1, 2), (cR 2, 4), (cR 3, 1)], [(cS 0 1, 3), (cS 0 2, 3), (cS 0 3, 3), (cS 0 4, 3), (cS 2 1, 2), (cS 3 0, 3), (cS 3 1, 3), (cS 3 2, 3), (cS 4 3, 3), (cS 4 4, 5), (cS 5 3, 3), (cS 5 4, 2), (cS 5 6, 3), (cS 6 2, 1), (cS 6 3, 1), (cS 6 5, 4), (cS 6 6, 3), (cR 5, 1), (cR 6, 1)]),
  .root (4, [(cS 0 0, 3), (cS 0 5, 2), (cS 1 0, 1), (cS 1 5, 2), (cS 2 3, 4), (cS 2 5, 2), (cS 4 3, 2), (cS 4 4, 2), (cS 5 0, 1), (cS 5 6, 2), (cS 6 0, 1)], [(cS 0 3, 2), (cS 0 4, 2), (cS 2 0, 1), (cS 2 6, 2), (cS 3 0, 1), (cS 3 5, 2), (cS 4 0, 1), (cS 4 6, 2), (cS 5 3, 2), (cS 5 4, 2), (cS 6 5, 2), (cC 1, 2), (cC 2, 2)]),
  .root (2, [(cS 0 0, 1), (cS 1 0, 1), (cS 1 5, 2), (cS 2 2, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 1, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 0 4, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 5, 1), (cS 5 3, 1), (cS 6 5, 1), (cR 5, 1), (cC 6, 1)]),
  .root (3, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 0, 2), (cS 1 5, 2), (cS 2 3, 2), (cS 3 5, 2), (cS 4 3, 1), (cS 4 4, 2), (cS 4 5, 1), (cR 2, 1)], [(cS 1 3, 2), (cS 3 0, 2), (cS 3 2, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 6 3, 1), (cS 6 4, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 0, 1), (cR 5, 1), (cC 1, 1), (cC 2, 1)]),
  .root (5, [(cS 0 0, 1), (cS 0 5, 1), (cS 2 3, 2), (cS 3 1, 2), (cS 5 0, 1), (cS 5 6, 2), (cS 6 0, 2), (cR 0, 2), (cR 1, 2), (cR 2, 3)], [(cS 0 2, 1), (cS 0 4, 1), (cS 3 0, 1), (cS 3 4, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 5 1, 1), (cS 5 4, 1), (cS 5 5, 1), (cS 6 2, 3), (cS 6 3, 1), (cS 6 4, 2), (cS 6 5, 1), (cR 4, 3), (cR 6, 1)]),
  .root (5, [(cS 0 0, 1), (cS 1 0, 1), (cS 1 5, 2), (cS 2 1, 1), (cS 2 3, 1), (cS 4 1, 2), (cS 4 2, 2), (cS 5 1, 1), (cR 1, 3), (cR 2, 1), (cR 3, 3)], [(cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 0 4, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 4 4, 3), (cS 4 6, 3), (cS 5 3, 1), (cS 6 5, 1), (cS 6 6, 1), (cR 4, 1), (cR 5, 1), (cR 6, 3)]),
  .root (1, [(cR 1, 1), (cR 3, 1)], [(cR 4, 1), (cR 6, 1)]),
  .root (6, [(cS 0 0, 2), (cS 1 0, 1), (cS 1 5, 3), (cS 2 2, 1), (cS 2 4, 1), (cS 3 1, 3), (cS 3 2, 1), (cS 3 3, 1), (cS 3 4, 1), (cS 4 3, 3), (cS 4 4, 3), (cR 1, 3), (cR 2, 2), (cR 3, 1)], [(cS 0 1, 2), (cS 0 2, 3), (cS 0 3, 2), (cS 0 4, 2), (cS 1 4, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 3 6, 2), (cS 4 1, 1), (cS 4 6, 3), (cS 5 1, 2), (cS 6 3, 2), (cS 6 5, 2), (cS 6 6, 2), (cR 0, 1), (cR 5, 3), (cR 6, 1)]),
  .root (1, [(cR 4, 1), (cR 6, 1)], [(cR 0, 1), (cR 2, 1)]),
  .root (10, [(cS 2 0, 4), (cS 2 1, 4), (cS 3 0, 2), (cS 3 1, 6), (cS 3 6, 1), (cS 4 2, 2), (cS 4 5, 2), (cS 4 6, 2), (cS 5 0, 2), (cS 5 1, 6), (cS 5 2, 2), (cS 5 6, 1), (cS 6 3, 3), (cS 6 4, 5), (cS 6 5, 3), (cS 6 6, 2), (cR 4, 2), (cR 6, 2), (cC 6, 3)], [(cS 0 0, 1), (cS 0 1, 1), (cS 0 2, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 2, 4), (cS 2 3, 3), (cS 2 4, 3), (cS 2 5, 6), (cS 3 3, 2), (cS 3 4, 1), (cS 4 3, 3), (cS 4 4, 6), (cS 6 2, 2), (cR 0, 6), (cR 1, 2), (cC 3, 1)]),
  .root (6, [(cS 2 1, 2), (cS 3 0, 2), (cS 3 1, 2), (cS 3 2, 2), (cS 4 3, 2), (cS 4 4, 2), (cS 5 0, 2), (cS 5 1, 2), (cS 5 2, 2), (cS 6 3, 2), (cS 6 4, 2), (cS 6 5, 2), (cS 6 6, 2), (cR 4, 2), (cR 6, 2)], [(cS 0 1, 1), (cS 0 2, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 2, 1), (cS 2 3, 2), (cS 2 4, 1), (cS 2 6, 1), (cS 3 5, 2), (cS 4 5, 2), (cS 4 6, 2), (cR 0, 4), (cR 2, 3)]),
  .root (40, [(cS 2 0, 8), (cS 2 1, 23), (cS 3 0, 14), (cS 3 1, 17), (cS 4 3, 13), (cS 4 4, 18), (cS 4 5, 13), (cS 5 0, 13), (cS 6 3, 13), (cS 6 4, 18), (cS 6 5, 13), (cR 4, 9), (cR 6, 9), (cC 6, 18)], [(cS 0 0, 3), (cS 0 1, 5), (cS 1 4, 3), (cS 1 5, 5), (cS 1 6, 5), (cS 2 2, 3), (cS 2 3, 18), (cS 2 4, 17), (cS 2 5, 23), (cS 3 2, 9), (cS 5 1, 18), (cS 5 2, 17), (cS 6 2, 13), (cR 0, 23), (cR 1, 9), (cC 2, 5), (cC 3, 5)]),
  .root (2, [(cS 0 4, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 6 4, 1), (cR 3, 1), (cR 4, 1), (cR 5, 1)], [(cS 2 3, 1), (cS 2 5, 1), (cS 3 3, 1), (cS 6 0, 1), (cS 6 2, 1), (cS 6 6, 1), (cR 0, 1), (cR 1, 1)]),
  .splitS0 [.leaf (10, [(cS 0 5, 2), (cS 2 5, 2), (cS 3 0, 2), (cS 3 6, 2), (cS 4 1, 2), (cS 4 2, 2), (cS 5 0, 2), (cS 5 1, 4), (cS 5 2, 3), (cS 6 1, 2), (cS 6 4, 1), (cR 5, 2), (cC 4, 5), (cC 5, 3), (cC 6, 6)], [(cS 0 0, 4), (cS 0 1, 4), (cS 0 2, 2), (cS 0 3, 1), (cS 1 0, 6), (cS 1 2, 4), (cS 1 3, 1), (cS 2 1, 4), (cS 2 2, 2), (cS 2 3, 1), (cS 3 1, 6), (cS 3 3, 5), (cS 3 4, 1), (cS 4 4, 1), (cS 6 2, 4), (cC 3, 3)]), .leaf (10, [(cS 4 1, 2), (cS 5 1, 3), (cS 5 2, 5), (cS 6 1, 2), (cC 0, 5), (cC 4, 5), (cC 5, 5), (cC 6, 5)], [(cS 0 1, 3), (cS 0 2, 5), (cS 1 1, 7), (cS 2 1, 3), (cS 2 3, 5), (cS 3 1, 8), (cS 4 3, 5), (cS 6 2, 2), (cC 3, 5)]), .leaf (12, [(cS 0 4, 1), (cS 1 5, 1), (cS 2 4, 1), (cS 2 5, 1), (cS 3 0, 2), (cS 3 6, 2), (cS 4 1, 5), (cS 5 0, 2), (cS 5 1, 3), (cS 5 2, 2), (cS 6 1, 5), (cS 6 5, 1), (cR 5, 2), (cC 4, 7), (cC 5, 3), (cC 6, 8)], [(cS 0 0, 4), (cS 0 1, 3), (cS 0 2, 5), (cS 1 0, 8), (cS 1 2, 1), (cS 2 0, 4), (cS 2 1, 3), (cS 2 2, 5), (cS 3 1, 5), (cS 4 3, 5), (cS 4 4, 3), (cS 6 2, 1), (cC 2, 3), (cC 3, 4)]), .leaf (5, [(cS 4 1, 1), (cS 4 2, 1), (cS 5 1, 2), (cS 5 2, 2), (cS 6 1, 1), (cC 0, 2), (cC 4, 3), (cC 5, 2), (cC 6, 3)], [(cS 0 1, 2), (cS 0 2, 2), (cS 1 1, 3), (cS 1 3, 3), (cS 2 1, 2), (cS 3 1, 3), (cS 3 3, 3), (cS 6 2, 1), (cC 3, 2)]), .leaf (6, [(cS 0 4, 2), (cS 1 4, 1), (cS 1 6, 1), (cS 2 0, 1), (cS 2 4, 2), (cS 4 2, 1), (cS 4 6, 1), (cS 5 1, 4), (cS 5 4, 1), (cR 3, 1), (cR 5, 1), (cR 6, 1), (cC 0, 2), (cC 5, 3), (cC 6, 2)], [(cS 0 0, 1), (cS 0 1, 2), (cS 0 2, 1), (cS 0 3, 1), (cS 1 3, 1), (cS 2 1, 3), (cS 2 3, 1), (cS 3 2, 1), (cS 3 4, 1), (cS 4 4, 1), (cC 1, 3), (cC 3, 4)]), .leaf (5, [(cS 4 1, 1), (cS 4 2, 1), (cS 5 1, 2), (cS 5 2, 2), (cS 6 1, 1), (cC 0, 2), (cC 4, 3), (cC 5, 2), (cC 6, 3)], [(cS 0 1, 2), (cS 0 2, 2), (cS 1 1, 3), (cS 1 3, 3), (cS 2 1, 2), (cS 3 1, 3), (cS 3 3, 3), (cS 6 2, 1), (cC 3, 2)]), .leaf (20, [(cS 0 4, 2), (cS 0 5, 3), (cS 2 4, 2), (cS 2 5, 3), (cS 3 0, 5), (cS 3 1, 15), (cS 3 6, 3), (cS 5 0, 5), (cS 5 1, 12), (cS 5 2, 5), (cS 6 4, 3), (cR 5, 3), (cC 4, 9), (cC 5, 6), (cC 6, 12)], [(cS 0 0, 20), (cS 0 2, 14), (cS 1 3, 3), (cS 2 0, 8), (cS 2 1, 12), (cS 2 2, 2), (cS 2 3, 3), (cS 3 3, 8), (cS 3 4, 3), (cS 4 4, 3), (cC 2, 6), (cC 3, 6)]), .leaf (5, [(cS 4 1, 1), (cS 4 2, 1), (cS 5 1, 2), (cS 5 2, 2), (cS 6 1, 1), (cC 0, 2), (cC 4, 3), (cC 5, 2), (cC 6, 3)], [(cS 0 1, 2), (cS 0 2, 2), (cS 1 1, 3), (cS 1 3, 3), (cS 2 1, 2), (cS 3 1, 3), (cS 3 3, 3), (cS 6 2, 1), (cC 3, 2)]), .leaf (3, [(cS 0 4, 1), (cS 2 4, 1), (cS 3 0, 1), (cS 4 1, 1), (cS 5 1, 1), (cS 6 1, 1), (cR 5, 1), (cC 4, 1), (cC 5, 1), (cC 6, 2)], [(cS 0 0, 1), (cS 0 2, 1), (cS 1 0, 2), (cS 1 2, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 3 4, 1), (cS 6 1, 1), (cC 2, 1), (cC 3, 1)]), .leaf (12, [(cS 1 4, 1), (cS 2 5, 1), (cS 3 0, 2), (cS 3 6, 1), (cS 4 1, 4), (cS 5 0, 3), (cS 5 1, 4), (cS 5 2, 3), (cS 6 1, 4), (cS 6 4, 1), (cR 5, 1), (cC 4, 8), (cC 5, 3), (cC 6, 9)], [(cS 0 0, 4), (cS 0 1, 4), (cS 0 2, 2), (cS 0 3, 1), (cS 1 0, 8), (cS 1 2, 4), (cS 2 0, 4), (cS 2 1, 2), (cS 2 2, 4), (cS 3 1, 6), (cS 3 3, 3), (cS 3 4, 1), (cS 4 3, 4), (cS 4 4, 1), (cS 6 2, 4), (cC 2, 2), (cC 3, 3)])],
  .root (6, [(cS 1 5, 4), (cS 4 2, 1), (cS 4 3, 2), (cS 4 4, 1), (cS 5 0, 2), (cS 5 1, 2), (cS 6 0, 1), (cS 6 4, 3), (cS 6 6, 3), (cR 4, 3), (cR 6, 1), (cC 5, 2)], [(cS 0 0, 1), (cS 0 1, 3), (cS 0 3, 1), (cS 1 6, 2), (cS 2 1, 2), (cS 3 6, 2), (cS 4 6, 1), (cS 6 2, 3), (cR 1, 3), (cR 2, 1), (cR 3, 3), (cC 3, 2)]),
  .root (5, [(cS 0 5, 2), (cS 1 5, 2), (cS 2 5, 2), (cS 3 0, 1), (cS 3 4, 2), (cS 3 6, 4), (cS 4 3, 1), (cS 4 4, 2), (cS 5 0, 1), (cS 5 4, 2), (cS 5 6, 4), (cS 6 5, 2), (cC 5, 1)], [(cS 0 0, 4), (cS 0 3, 2), (cS 1 0, 4), (cS 1 1, 1), (cS 2 0, 1), (cS 2 3, 2), (cS 3 1, 1), (cS 4 1, 1), (cS 6 0, 1), (cS 6 2, 1), (cC 1, 3), (cC 2, 1), (cC 3, 3)]),
  .root (12, [(cS 0 5, 2), (cS 1 5, 4), (cS 2 5, 1), (cS 2 6, 1), (cS 3 0, 6), (cS 3 4, 4), (cS 3 6, 5), (cS 4 2, 5), (cS 4 3, 6), (cS 5 2, 6), (cS 5 4, 4), (cS 6 4, 3), (cR 4, 1), (cC 4, 1), (cC 5, 6)], [(cS 0 0, 1), (cS 2 3, 2), (cS 2 6, 1), (cS 3 1, 2), (cS 5 0, 7), (cS 5 6, 2), (cS 6 0, 1), (cS 6 2, 2), (cS 6 6, 1), (cR 0, 6), (cR 1, 2), (cR 2, 6), (cC 1, 4), (cC 3, 4), (cC 6, 3)]),
  .root (40, [(cS 1 5, 40), (cS 2 1, 13), (cS 3 0, 19), (cS 3 1, 8), (cS 3 2, 19), (cS 4 0, 2), (cS 4 1, 11), (cS 4 2, 3), (cS 5 0, 10), (cS 5 1, 17), (cS 5 2, 24), (cS 5 6, 11), (cS 6 0, 13), (cS 6 4, 5), (cS 6 5, 35), (cS 6 6, 6)], [(cS 0 0, 15), (cS 0 1, 11), (cS 0 2, 19), (cS 1 0, 17), (cS 2 2, 17), (cS 2 5, 7), (cS 2 6, 15), (cS 3 3, 5), (cS 3 5, 10), (cS 3 6, 2), (cS 4 4, 5), (cS 4 5, 12), (cS 4 6, 17), (cS 5 4, 6), (cS 6 2, 4), (cR 0, 6), (cR 1, 4), (cR 2, 6), (cC 3, 13), (cC 4, 17)]),
  .splitS0 [.leaf (16, [(cS 0 5, 2), (cS 1 4, 1), (cS 2 1, 5), (cS 2 5, 3), (cS 3 1, 11), (cS 3 6, 7), (cS 4 1, 5), (cS 5 0, 4), (cS 5 4, 1), (cS 5 6, 3), (cS 6 4, 2), (cC 0, 1), (cC 4, 7), (cC 5, 6), (cC 6, 8)], [(cS 0 0, 8), (cS 0 1, 1), (cS 0 2, 4), (cS 0 3, 1), (cS 1 0, 8), (cS 1 1, 2), (cS 1 2, 4), (cS 1 3, 1), (cS 2 3, 1), (cS 3 3, 6), (cS 3 4, 3), (cS 4 4, 2), (cS 5 1, 6), (cS 5 2, 5), (cS 6 1, 6), (cC 2, 5), (cC 3, 6)]), .leaf (2, [(cS 3 1, 1), (cS 3 2, 1), (cC 0, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 1, 1), (cS 1 1, 1), (cS 2 4, 1), (cS 4 4, 1), (cS 5 1, 1), (cC 2, 1), (cC 3, 1)]), .leaf (16, [(cS 1 4, 6), (cS 1 5, 2), (cS 2 1, 3), (cS 2 4, 1), (cS 3 0, 1), (cS 3 1, 6), (cS 4 1, 3), (cS 5 0, 6), (cS 5 6, 2), (cS 6 4, 7), (cS 6 5, 2), (cR 3, 7), (cC 4, 2), (cC 5, 6), (cC 6, 8)], [(cS 0 0, 8), (cS 0 1, 4), (cS 0 3, 1), (cS 1 0, 9), (cS 1 1, 4), (cS 2 2, 1), (cS 4 3, 1), (cS 4 4, 8), (cS 5 1, 7), (cS 5 2, 1), (cS 6 1, 4), (cC 2, 8), (cC 3, 7)]), .leaf (2, [(cS 3 1, 1), (cS 3 2, 1), (cC 0, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 1, 1), (cS 1 1, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 5 1, 1), (cS 6 2, 1), (cC 3, 1)]), .leaf (1, [(cS 1 2, 1), (cS 3 1, 1), (cC 0, 1), (cC 5, 1)], [(cS 0 1, 1), (cS 5 1, 1), (cC 3, 1)]), .leaf (2, [(cS 3 1, 1), (cS 3 2, 1), (cC 0, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 1, 1), (cS 1 1, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 5 1, 1), (cS 6 2, 1), (cC 3, 1)]), .leaf (5, [(cS 0 5, 1), (cS 2 1, 3), (cS 2 5, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 2, 1), (cS 3 6, 1), (cS 4 1, 3), (cS 5 0, 1), (cS 5 6, 1), (cS 6 4, 1), (cC 4, 3), (cC 5, 1), (cC 6, 3)], [(cS 0 0, 3), (cS 0 2, 3), (cS 1 0, 2), (cS 1 2, 1), (cS 1 3, 1), (cS 2 3, 1), (cS 3 3, 3), (cS 4 4, 1), (cS 5 1, 1), (cS 5 2, 3), (cS 6 0, 2), (cS 6 1, 1), (cC 2, 1), (cC 3, 1)]), .leaf (2, [(cS 3 1, 1), (cS 3 2, 1), (cC 0, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 1, 1), (cS 1 1, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 5 1, 1), (cS 6 2, 1), (cC 3, 1)]), .leaf (16, [(cS 0 5, 2), (cS 1 4, 1), (cS 2 1, 5), (cS 2 5, 3), (cS 3 1, 11), (cS 3 6, 7), (cS 4 1, 5), (cS 5 0, 4), (cS 5 4, 1), (cS 5 6, 3), (cS 6 4, 2), (cC 0, 1), (cC 4, 7), (cC 5, 6), (cC 6, 8)], [(cS 0 0, 8), (cS 0 1, 1), (cS 0 2, 4), (cS 0 3, 1), (cS 1 0, 8), (cS 1 1, 2), (cS 1 2, 4), (cS 1 3, 1), (cS 2 3, 1), (cS 3 3, 6), (cS 3 4, 3), (cS 4 4, 2), (cS 5 1, 6), (cS 5 2, 5), (cS 6 1, 6), (cC 2, 5), (cC 3, 6)]), .leaf (12, [(cS 0 5, 2), (cS 1 4, 2), (cS 2 1, 4), (cS 2 4, 1), (cS 2 5, 3), (cS 3 0, 2), (cS 3 1, 8), (cS 3 6, 3), (cS 4 1, 4), (cS 5 0, 3), (cS 5 4, 1), (cS 5 6, 2), (cS 6 4, 3), (cC 0, 1), (cC 4, 4), (cC 5, 4), (cC 6, 6)], [(cS 0 0, 6), (cS 0 1, 1), (cS 0 2, 3), (cS 0 3, 1), (cS 1 0, 6), (cS 1 1, 1), (cS 1 2, 3), (cS 1 3, 1), (cS 3 3, 4), (cS 3 4, 1), (cS 4 4, 3), (cS 5 1, 4), (cS 5 2, 4), (cS 6 1, 4), (cC 2, 4), (cC 3, 4)])],
  .splitS0 [.leaf (16, [(cS 0 5, 4), (cS 1 6, 8), (cS 2 0, 1), (cS 2 1, 8), (cS 2 5, 4), (cS 3 0, 4), (cS 3 1, 10), (cS 3 6, 11), (cS 4 1, 2), (cS 4 2, 4), (cS 4 6, 1), (cS 5 1, 9), (cS 5 2, 7), (cS 5 4, 2), (cS 6 4, 1), (cS 6 5, 1), (cC 4, 8), (cC 5, 4)], [(cS 0 0, 4), (cS 0 1, 3), (cS 0 2, 5), (cS 0 6, 3), (cS 1 0, 2), (cS 1 2, 6), (cS 1 3, 1), (cS 2 2, 2), (cS 2 3, 2), (cS 3 3, 7), (cS 3 4, 2), (cS 4 4, 2), (cS 4 6, 2), (cS 5 6, 9), (cS 6 1, 2), (cS 6 2, 4), (cS 6 6, 2), (cR 0, 2), (cC 0, 5), (cC 3, 5)]), .leaf (2, [(cS 3 0, 1), (cS 3 2, 1), (cS 4 1, 1), (cS 4 6, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 4, 1), (cR 1, 1), (cR 2, 1), (cC 5, 1)], [(cS 0 0, 1), (cS 0 1, 1), (cS 0 2, 1), (cS 2 3, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 6 6, 1), (cC 3, 1)]), .leaf (5, [(cS 0 4, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 2), (cS 2 0, 1), (cS 2 1, 1), (cS 2 4, 2), (cS 3 0, 1), (cS 3 1, 1), (cS 3 2, 2), (cS 3 6, 2), (cS 4 0, 1), (cS 4 1, 1), (cS 5 1, 2), (cS 5 2, 3), (cS 5 4, 1), (cS 6 4, 2), (cR 3, 1), (cC 5, 2)], [(cS 0 1, 1), (cS 0 2, 2), (cS 0 6, 2), (cS 1 0, 2), (cS 1 1, 1), (cS 2 2, 3), (cS 4 3, 1), (cS 4 4, 2), (cS 5 0, 1), (cS 5 6, 3), (cS 6 0, 2), (cS 6 1, 1), (cR 0, 1), (cC 3, 2)]), .leaf (60, [(cS 0 5, 16), (cS 2 1, 7), (cS 2 5, 16), (cS 3 0, 17), (cS 3 1, 18), (cS 3 6, 17), (cS 4 1, 7), (cS 5 2, 24), (cS 5 4, 7), (cS 6 4, 9), (cC 1, 18), (cC 2, 18), (cC 4, 26), (cC 5, 18), (cC 6, 26)], [(cS 0 0, 34), (cS 0 1, 26), (cS 0 2, 34), (cS 0 3, 8), (cS 1 3, 34), (cS 2 0, 26), (cS 2 2, 8), (cS 3 3, 25), (cS 3 4, 8), (cS 4 4, 9), (cS 5 0, 42), (cS 5 6, 18), (cR 2, 9), (cC 3, 18)]), .leaf (24, [(cS 0 5, 6), (cS 1 6, 11), (cS 2 0, 1), (cS 2 1, 6), (cS 2 6, 4), (cS 3 0, 6), (cS 3 1, 7), (cS 3 2, 6), (cS 3 6, 7), (cS 4 0, 2), (cS 4 1, 9), (cS 4 2, 2), (cS 4 6, 10), (cS 5 1, 8), (cS 5 2, 16), (cS 5 4, 2), (cS 6 4, 4), (cR 2, 6), (cC 4, 11), (cC 5, 7)], [(cS 0 0, 11), (cS 0 1, 2), (cS 0 2, 11), (cS 0 3, 4), (cS 1 1, 9), (cS 1 3, 11), (cS 2 2, 2), (cS 2 3, 4), (cS 3 3, 11), (cS 3 4, 2), (cS 4 4, 4), (cS 5 0, 5), (cS 5 6, 7), (cS 6 0, 2), (cS 6 1, 9), (cS 6 2, 2), (cS 6 6, 11), (cR 1, 2), (cC 3, 7)]), .leaf (30, [(cS 0 5, 8), (cS 1 6, 11), (cS 2 0, 2), (cS 2 1, 4), (cS 2 4, 1), (cS 3 0, 5), (cS 3 1, 9), (cS 3 2, 3), (cS 3 6, 9), (cS 4 0, 2), (cS 4 1, 7), (cS 4 2, 6), (cS 4 6, 7), (cS 5 1, 8), (cS 5 2, 15), (cS 5 4, 3), (cS 6 4, 5), (cR 2, 7), (cC 1, 7), (cC 4, 13), (cC 5, 9), (cC 6, 7)], [(cS 0 0, 9), (cS 0 1, 12), (cS 0 2, 11), (cS 0 3, 3), (cS 1 0, 3), (cS 1 1, 7), (cS 1 3, 18), (cS 2 2, 5), (cS 2 3, 3), (cS 3 3, 13), (cS 3 4, 5), (cS 4 4, 5), (cS 5 0, 6), (cS 5 6, 8), (cS 6 0, 9), (cS 6 2, 7), (cS 6 6, 7), (cC 3, 9)]), .leaf (20, [(cS 0 5, 3), (cS 1 5, 2), (cS 1 6, 9), (cS 2 0, 4), (cS 2 1, 7), (cS 2 5, 4), (cS 3 0, 1), (cS 3 1, 12), (cS 3 6, 14), (cS 4 0, 5), (cS 4 1, 2), (cS 4 2, 6), (cS 5 1, 12), (cS 5 2, 8), (cS 5 4, 3), (cS 6 4, 2), (cR 2, 1), (cC 4, 9), (cC 5, 6)], [(cS 0 0, 5), (cS 0 1, 4), (cS 0 2, 4), (cS 0 6, 6), (cS 1 0, 6), (cS 1 1, 2), (cS 1 2, 6), (cS 1 3, 2), (cS 2 2, 4), (cS 2 3, 2), (cS 3 3, 8), (cS 3 4, 4), (cS 4 4, 2), (cS 5 0, 1), (cS 5 6, 14), (cS 6 0, 5), (cS 6 1, 2), (cS 6 2, 6), (cS 6 6, 1), (cR 0, 4), (cC 3, 6)]), .leaf (20, [(cS 0 5, 4), (cS 1 4, 2), (cS 1 6, 10), (cS 2 0, 4), (cS 2 1, 7), (cS 2 5, 5), (cS 3 0, 6), (cS 3 1, 6), (cS 3 2, 6), (cS 3 6, 9), (cS 4 1, 7), (cS 4 6, 4), (cS 5 1, 7), (cS 5 2, 13), (cS 6 4, 5), (cS 6 5, 1), (cR 3, 1), (cC 4, 8), (cC 5, 6)], [(cS 0 0, 9), (cS 0 1, 2), (cS 0 2, 11), (cS 0 6, 4), (cS 1 0, 6), (cS 1 1, 3), (cS 1 2, 3), (cS 1 3, 3), (cS 2 2, 7), (cS 3 3, 6), (cS 4 4, 7), (cS 5 0, 6), (cS 5 6, 10), (cS 6 0, 2), (cS 6 1, 6), (cS 6 2, 1), (cS 6 6, 4), (cR 0, 1), (cC 3, 7)])],
  .root (30, [(cS 0 5, 9), (cS 1 5, 13), (cS 2 1, 15), (cS 2 5, 9), (cS 3 1, 15), (cS 3 4, 9), (cS 4 3, 8), (cS 4 4, 13), (cS 5 0, 6), (cS 5 4, 9), (cS 5 6, 9), (cS 6 0, 8), (cS 6 4, 7), (cS 6 5, 6), (cS 6 6, 7), (cC 5, 8)], [(cS 0 0, 13), (cS 0 1, 15), (cS 0 3, 9), (cS 1 0, 8), (cS 1 1, 1), (cS 2 3, 8), (cS 2 4, 2), (cS 2 6, 13), (cS 3 3, 6), (cS 3 5, 2), (cS 3 6, 15), (cS 4 1, 8), (cS 4 6, 13), (cS 5 1, 9), (cS 5 2, 6), (cS 6 2, 8), (cR 1, 7), (cC 0, 2), (cC 1, 5), (cC 2, 2), (cC 3, 14)]),
  .root (4, [(cS 0 5, 1), (cS 1 5, 2), (cS 2 1, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 3 1, 2), (cS 3 2, 1), (cS 4 1, 1), (cS 4 3, 3), (cS 4 4, 1), (cS 5 1, 2), (cS 5 2, 1), (cS 5 4, 1), (cS 6 4, 2), (cC 5, 1)], [(cS 0 0, 1), (cS 0 1, 2), (cS 0 3, 2), (cS 1 0, 1), (cS 1 1, 2), (cS 1 3, 2), (cS 2 2, 1), (cS 2 3, 2), (cS 2 6, 1), (cS 3 3, 1), (cS 3 4, 1), (cS 3 5, 1), (cS 4 6, 1), (cS 6 0, 1), (cS 6 2, 2), (cR 5, 1), (cC 6, 2)]),
  .root (2, [(cS 1 6, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 3 0, 1), (cS 3 2, 1), (cS 4 3, 1), (cS 4 6, 1), (cC 4, 1), (cC 5, 1)], [(cS 0 3, 1), (cS 0 6, 1), (cS 2 3, 2), (cS 5 0, 1), (cS 5 2, 1), (cS 5 3, 1), (cS 5 6, 1), (cR 0, 1), (cC 1, 1)]),
  .root (6, [(cS 2 3, 6), (cS 3 0, 2), (cS 4 1, 1), (cS 4 2, 2), (cS 4 5, 2), (cS 4 6, 3), (cS 5 0, 2), (cS 5 1, 2), (cS 6 3, 2), (cS 6 4, 2), (cS 6 5, 2), (cS 6 6, 2), (cR 4, 1), (cR 6, 2)], [(cS 2 1, 4), (cS 2 4, 4), (cS 2 5, 2), (cS 2 6, 4), (cS 3 1, 2), (cS 4 3, 3), (cS 4 4, 3), (cS 6 2, 2), (cR 0, 4), (cR 1, 2)]),
  .root (6, [(cS 2 3, 4), (cS 4 1, 1), (cS 4 2, 3), (cS 4 4, 3), (cS 5 0, 2), (cS 5 1, 2), (cS 6 4, 1), (cS 6 5, 2), (cS 6 6, 1), (cR 4, 1), (cR 6, 3), (cC 3, 2)], [(cS 0 2, 2), (cS 1 0, 2), (cS 2 0, 3), (cS 2 2, 5), (cS 2 5, 3), (cS 3 0, 3), (cS 3 1, 1), (cS 3 5, 1), (cS 4 6, 3), (cS 6 2, 1), (cR 0, 3), (cR 1, 1), (cC 5, 2)]),
  .root (5, [(cS 2 2, 1), (cS 2 3, 2), (cS 4 4, 2), (cS 4 6, 3), (cS 5 0, 2), (cS 6 4, 2), (cS 6 6, 3), (cC 3, 2), (cC 4, 1), (cC 5, 2)], [(cS 0 0, 1), (cS 1 5, 3), (cS 2 0, 1), (cS 2 5, 2), (cS 2 6, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 5 2, 1), (cS 6 3, 1), (cR 0, 1), (cR 1, 1), (cC 0, 2), (cC 1, 1), (cC 2, 3)]),
  .root (20, [(cS 1 3, 1), (cS 2 3, 12), (cS 3 5, 5), (cS 3 6, 4), (cS 4 2, 3), (cS 4 3, 2), (cS 4 4, 4), (cS 4 5, 3), (cS 5 1, 6), (cS 5 2, 5), (cS 5 4, 1), (cS 5 5, 6), (cS 6 4, 13), (cS 6 5, 7), (cR 3, 2), (cR 4, 6), (cC 3, 7)], [(cS 0 2, 4), (cS 0 5, 5), (cS 1 5, 3), (cS 2 1, 4), (cS 2 5, 7), (cS 3 1, 6), (cS 5 6, 5), (cS 6 0, 4), (cS 6 1, 1), (cS 6 2, 6), (cS 6 6, 2), (cR 0, 6), (cR 1, 6), (cR 2, 6), (cC 0, 9), (cC 2, 4)]),
  .root (4, [(cS 2 1, 4), (cS 2 3, 4), (cS 4 0, 2), (cS 4 1, 2), (cS 4 2, 2), (cR 6, 4)], [(cS 0 2, 1), (cS 1 0, 1), (cS 1 6, 1), (cS 2 5, 3), (cS 2 6, 2), (cS 3 6, 2), (cS 4 3, 2), (cS 4 4, 1), (cS 4 5, 2), (cS 4 6, 2), (cR 0, 3), (cC 4, 1)]),
  .splitS0 [.leaf (6, [(cS 0 5, 3), (cS 1 2, 1), (cS 1 4, 1), (cS 2 1, 2), (cS 2 2, 2), (cS 2 3, 1), (cS 2 4, 2), (cS 3 0, 2), (cS 3 6, 2), (cS 4 1, 1), (cS 4 6, 3), (cS 5 0, 3), (cS 5 5, 3), (cS 6 3, 2), (cS 6 4, 3), (cS 6 6, 3), (cR 2, 1), (cR 3, 1), (cC 3, 1)], [(cS 0 1, 3), (cS 0 3, 2), (cS 1 1, 1), (cS 1 6, 4), (cS 3 4, 1), (cS 3 5, 2), (cS 4 1, 2), (cS 4 2, 2), (cS 4 3, 2), (cS 4 4, 3), (cS 5 2, 2), (cS 6 0, 3), (cS 6 2, 4), (cR 1, 2)]), .leaf (24, [(cS 0 5, 2), (cS 1 2, 4), (cS 1 3, 2), (cS 2 2, 7), (cS 2 3, 8), (cS 2 4, 1), (cS 3 0, 7), (cS 3 1, 3), (cS 3 6, 2), (cS 4 5, 7), (cS 4 6, 7), (cS 5 0, 8), (cS 5 4, 2), (cS 5 6, 4), (cS 6 4, 16), (cS 6 6, 14), (cR 2, 7), (cR 3, 2), (cR 6, 2), (cC 1, 6), (cC 4, 6), (cC 6, 6)], [(cS 0 0, 11), (cS 0 1, 1), (cS 0 2, 2), (cS 0 3, 4), (cS 1 5, 4), (cS 1 6, 1), (cS 2 5, 8), (cS 4 1, 6), (cS 4 2, 8), (cS 4 3, 16), (cS 4 4, 9), (cS 5 1, 4), (cS 5 2, 6), (cS 6 1, 4), (cS 6 2, 18), (cR 1, 12)]), .leaf (2, [(cS 0 5, 1), (cS 1 2, 1), (cS 1 4, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 6 0, 1), (cS 6 4, 2), (cS 6 6, 1), (cR 2, 1), (cR 3, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 1 1, 1), (cS 1 6, 2), (cS 4 1, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 2, 1), (cS 6 2, 1)]), .leaf (2, [(cS 0 5, 1), (cS 1 2, 1), (cS 1 4, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 6 0, 1), (cS 6 4, 2), (cS 6 6, 1), (cR 2, 1), (cR 3, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 1 1, 1), (cS 1 6, 2), (cS 4 1, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 2, 1), (cS 6 2, 1)]), .leaf (20, [(cS 0 3, 2), (cS 0 5, 8), (cS 1 2, 3), (cS 1 3, 6), (cS 2 1, 5), (cS 2 2, 6), (cS 2 3, 2), (cS 3 0, 3), (cS 3 6, 5), (cS 4 5, 5), (cS 4 6, 6), (cS 5 0, 8), (cS 5 4, 3), (cS 5 5, 3), (cS 5 6, 6), (cS 6 0, 6), (cS 6 3, 3), (cS 6 4, 6), (cS 6 6, 9), (cR 2, 6), (cR 3, 6), (cR 6, 3), (cC 4, 6)], [(cS 0 0, 2), (cS 0 1, 9), (cS 0 2, 3), (cS 1 1, 3), (cS 1 6, 12), (cS 2 5, 3), (cS 4 1, 11), (cS 4 2, 3), (cS 4 3, 17), (cS 4 4, 3), (cS 5 1, 3), (cS 5 2, 3), (cS 6 2, 17), (cR 1, 6)]), .leaf (24, [(cS 0 5, 7), (cS 1 2, 5), (cS 1 3, 6), (cS 2 1, 5), (cS 2 2, 6), (cS 2 3, 4), (cS 3 0, 5), (cS 3 6, 5), (cS 4 5, 7), (cS 4 6, 8), (cS 5 0, 13), (cS 5 5, 6), (cS 5 6, 3), (cS 6 3, 4), (cS 6 4, 6), (cS 6 6, 9), (cR 2, 8), (cR 3, 6), (cR 6, 8), (cC 4, 6)], [(cS 0 1, 8), (cS 0 3, 2), (cS 1 1, 5), (cS 1 6, 13), (cS 2 5, 5), (cS 4 1, 13), (cS 4 2, 5), (cS 4 3, 19), (cS 4 4, 5), (cS 5 2, 6), (cS 6 0, 3), (cS 6 2, 18), (cR 0, 5), (cR 1, 6)]), .leaf (12, [(cS 0 3, 1), (cS 1 2, 3), (cS 1 3, 1), (cS 2 2, 2), (cS 2 3, 3), (cS 3 0, 3), (cS 3 1, 2), (cS 3 6, 2), (cS 4 5, 6), (cS 4 6, 6), (cS 5 0, 6), (cS 5 4, 1), (cS 6 3, 5), (cS 6 5, 6), (cS 6 6, 2), (cR 2, 6), (cR 3, 1), (cR 6, 4), (cC 1, 1), (cC 4, 2)], [(cS 0 0, 3), (cS 0 1, 1), (cS 1 0, 1), (cS 1 4, 1), (cS 1 5, 4), (cS 1 6, 1), (cS 2 5, 3), (cS 3 3, 3), (cS 4 1, 5), (cS 4 2, 3), (cS 4 3, 6), (cS 4 4, 3), (cS 5 1, 1), (cS 5 2, 3), (cS 6 2, 8), (cS 6 3, 1), (cR 0, 3), (cR 1, 4)]), .leaf (12, [(cS 0 5, 5), (cS 1 2, 5), (cS 1 4, 5), (cS 2 1, 2), (cS 3 0, 2), (cS 4 1, 2), (cS 4 5, 2), (cS 4 6, 5), (cS 5 0, 7), (cS 5 5, 2), (cS 5 6, 3), (cS 6 4, 10), (cS 6 6, 7), (cR 2, 5), (cR 3, 5), (cC 3, 2)], [(cS 0 1, 7), (cS 0 2, 3), (cS 0 3, 4), (cS 0 4, 1), (cS 1 1, 2), (cS 1 5, 1), (cS 1 6, 9), (cS 2 5, 2), (cS 4 2, 5), (cS 4 4, 12), (cS 5 2, 7), (cS 6 0, 2), (cS 6 2, 5), (cC 0, 3)])],
  .root (20, [(cS 1 3, 1), (cS 2 1, 7), (cS 2 2, 8), (cS 2 4, 10), (cS 3 0, 8), (cS 3 6, 7), (cS 4 1, 10), (cS 4 2, 6), (cS 4 6, 11), (cS 5 0, 5), (cS 5 2, 2), (cS 6 4, 14), (cS 6 5, 6), (cR 2, 3), (cR 3, 2), (cC 2, 2), (cC 3, 6)], [(cS 0 1, 9), (cS 0 2, 8), (cS 1 0, 8), (cS 1 4, 10), (cS 1 5, 2), (cS 1 6, 7), (cS 2 5, 1), (cS 4 3, 4), (cS 4 4, 16), (cS 5 1, 5), (cS 5 6, 1), (cS 6 0, 10), (cS 6 2, 11), (cS 6 6, 6), (cR 0, 1), (cR 1, 2), (cC 5, 5), (cC 6, 3)]),
  .splitS0 [.leaf (4, [(cS 0 5, 1), (cS 2 1, 2), (cS 2 2, 2), (cS 3 1, 2), (cS 5 5, 1), (cS 5 6, 2), (cS 6 5, 1), (cS 6 6, 2), (cC 3, 2), (cC 4, 2)], [(cS 0 1, 2), (cS 0 2, 2), (cS 1 5, 1), (cS 1 6, 2), (cS 2 5, 1), (cS 3 5, 1), (cS 3 6, 2), (cS 4 2, 2), (cS 4 5, 1), (cS 5 1, 2), (cS 6 2, 2), (cC 0, 2)]), .leaf (12, [(cS 0 5, 1), (cS 0 6, 2), (cS 1 2, 4), (cS 2 0, 2), (cS 2 1, 4), (cS 2 2, 4), (cS 3 0, 3), (cS 3 1, 3), (cS 3 2, 2), (cS 5 0, 3), (cS 5 6, 4), (cS 6 0, 2), (cS 6 5, 6), (cS 6 6, 3), (cC 3, 6), (cC 4, 6)], [(cS 0 0, 1), (cS 0 1, 5), (cS 0 2, 3), (cS 1 0, 4), (cS 1 5, 5), (cS 1 6, 5), (cS 2 5, 7), (cS 2 6, 1), (cS 3 6, 4), (cS 4 1, 4), (cS 4 2, 4), (cS 4 5, 6), (cS 4 6, 3), (cS 5 1, 3), (cS 5 2, 2), (cS 6 0, 2), (cS 6 2, 7), (cS 6 3, 3), (cC 0, 2)]), .leaf (24, [(cS 0 5, 6), (cS 1 2, 3), (cS 2 1, 14), (cS 2 2, 7), (cS 3 1, 10), (cS 3 2, 4), (cS 4 5, 1), (cS 5 0, 6), (cS 5 5, 7), (cS 5 6, 5), (cS 6 0, 2), (cS 6 5, 7), (cS 6 6, 11), (cC 3, 14), (cC 4, 11)], [(cS 0 1, 15), (cS 0 2, 7), (cS 0 6, 1), (cS 1 1, 2), (cS 1 5, 7), (cS 1 6, 12), (cS 2 0, 1), (cS 2 5, 6), (cS 3 0, 4), (cS 3 5, 7), (cS 3 6, 8), (cS 4 1, 3), (cS 4 2, 7), (cS 4 5, 5), (cS 4 6, 2), (cS 5 1, 9), (cS 5 2, 6), (cS 6 2, 18), (cC 0, 7), (cC 6, 4)]), .leaf (2, [(cS 0 5, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 3 1, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 6 6, 1), (cC 3, 1), (cC 4, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 1 6, 1), (cS 2 5, 1), (cS 3 6, 1), (cS 4 2, 1), (cS 4 5, 1), (cS 5 2, 1), (cS 6 2, 1), (cC 0, 1)]), .leaf (2, [(cS 0 5, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 3 1, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 6 6, 1), (cC 3, 1), (cC 4, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 1 6, 1), (cS 2 5, 1), (cS 3 6, 1), (cS 4 2, 1), (cS 4 5, 1), (cS 5 2, 1), (cS 6 2, 1), (cC 0, 1)]), .leaf (8, [(cS 0 5, 1), (cS 0 6, 1), (cS 2 1, 5), (cS 2 2, 3), (cS 2 3, 1), (cS 3 1, 3), (cS 4 3, 1), (cS 5 0, 4), (cS 5 5, 1), (cS 5 6, 1), (cS 6 4, 1), (cS 6 5, 1), (cS 6 6, 3), (cC 3, 4), (cC 4, 3), (cC 5, 2)], [(cS 0 0, 4), (cS 0 1, 1), (cS 0 2, 6), (cS 0 3, 1), (cS 1 0, 2), (cS 1 5, 1), (cS 1 6, 2), (cS 2 5, 1), (cS 2 6, 3), (cS 3 6, 3), (cS 4 1, 2), (cS 4 5, 1), (cS 4 6, 2), (cS 5 1, 1), (cS 5 2, 4), (cS 6 1, 3), (cS 6 2, 1), (cR 1, 1), (cR 3, 2), (cR 4, 1)]), .leaf (16, [(cS 0 5, 5), (cS 1 2, 4), (cS 2 0, 1), (cS 2 1, 7), (cS 2 2, 5), (cS 3 0, 5), (cS 3 1, 3), (cS 3 2, 2), (cS 4 6, 1), (cS 5 0, 6), (cS 5 5, 3), (cS 5 6, 3), (cS 6 0, 4), (cS 6 5, 6), (cS 6 6, 5), (cC 3, 9), (cC 4, 8)], [(cS 0 1, 9), (cS 0 2, 3), (cS 0 6, 1), (cS 1 1, 5), (cS 1 5, 3), (cS 1 6, 9), (cS 2 5, 5), (cS 3 5, 3), (cS 3 6, 5), (cS 4 1, 6), (cS 4 2, 5), (cS 4 5, 6), (cS 5 1, 3), (cS 5 2, 2), (cS 6 2, 11), (cS 6 3, 3), (cC 0, 3), (cC 6, 3)]), .leaf (4, [(cS 1 1, 2), (cS 1 2, 1), (cS 2 2, 1), (cS 3 0, 1), (cS 3 1, 2), (cS 3 2, 1), (cS 4 6, 2), (cS 5 0, 1), (cS 6 5, 2), (cS 6 6, 2), (cC 0, 1), (cC 3, 2), (cC 4, 2)], [(cS 0 0, 3), (cS 0 2, 1), (cS 1 0, 1), (cS 1 5, 4), (cS 2 6, 2), (cS 3 5, 2), (cS 4 2, 1), (cS 4 5, 2), (cS 5 1, 2), (cS 5 2, 1), (cS 6 2, 3)]), .leaf (4, [(cS 0 5, 1), (cS 2 1, 2), (cS 2 2, 2), (cS 3 0, 2), (cS 5 0, 2), (cS 5 5, 1), (cS 6 5, 1), (cS 6 6, 2), (cC 3, 2), (cC 4, 2)], [(cS 0 1, 2), (cS 0 2, 2), (cS 1 0, 2), (cS 1 5, 1), (cS 2 5, 1), (cS 3 5, 1), (cS 4 1, 2), (cS 4 2, 2), (cS 4 5, 1), (cS 6 1, 2), (cS 6 2, 2), (cC 6, 2)]), .leaf (10, [(cS 0 5, 3), (cS 0 6, 1), (cS 2 1, 4), (cS 2 2, 5), (cS 3 0, 4), (cS 3 1, 1), (cS 5 0, 5), (cS 5 5, 3), (cS 5 6, 1), (cS 6 4, 1), (cS 6 5, 2), (cS 6 6, 4), (cR 2, 1), (cR 4, 1), (cC 3, 5), (cC 4, 4)], [(cS 0 0, 5), (cS 0 2, 7), (cS 1 0, 1), (cS 1 6, 3), (cS 2 5, 2), (cS 2 6, 2), (cS 3 5, 3), (cS 3 6, 3), (cS 4 1, 3), (cS 4 2, 4), (cS 4 5, 2), (cS 4 6, 3), (cS 5 2, 2), (cS 6 1, 4), (cS 6 2, 3), (cR 1, 3), (cC 1, 1)]), .leaf (4, [(cS 0 5, 1), (cS 0 6, 2), (cS 2 1, 2), (cS 2 2, 2), (cS 3 0, 1), (cS 5 0, 1), (cS 5 5, 1), (cS 5 6, 2), (cS 6 5, 1), (cC 0, 1), (cC 3, 2), (cC 4, 2)], [(cS 0 0, 1), (cS 0 2, 2), (cS 1 0, 2), (cS 2 5, 3), (cS 3 5, 1), (cS 3 6, 2), (cS 4 1, 2), (cS 4 2, 1), (cS 4 5, 1), (cS 6 1, 2), (cS 6 2, 1), (cR 1, 1), (cC 2, 1)]), .leaf (16, [(cS 0 5, 4), (cS 0 6, 2), (cS 1 1, 1), (cS 1 2, 3), (cS 2 0, 1), (cS 2 1, 4), (cS 2 2, 8), (cS 2 3, 1), (cS 3 0, 6), (cS 3 1, 5), (cS 4 3, 1), (cS 5 0, 4), (cS 5 5, 3), (cS 5 6, 4), (cS 6 0, 2), (cS 6 4, 1), (cS 6 5, 4), (cS 6 6, 6), (cC 3, 7), (cC 4, 8)], [(cS 0 0, 3), (cS 0 1, 6), (cS 0 2, 6), (cS 0 3, 1), (cS 1 0, 4), (cS 1 5, 4), (cS 1 6, 6), (cS 2 0, 3), (cS 2 5, 12), (cS 3 5, 4), (cS 3 6, 3), (cS 4 1, 4), (cS 4 2, 8), (cS 4 5, 5), (cS 4 6, 5), (cS 5 1, 5), (cS 6 1, 2), (cS 6 2, 9), (cC 0, 3)])],
  .root (20, [(cS 0 4, 2), (cS 1 3, 6), (cS 2 1, 14), (cS 2 2, 3), (cS 2 3, 8), (cS 3 1, 5), (cS 3 3, 6), (cS 4 1, 12), (cS 4 3, 11), (cS 5 2, 6), (cS 5 4, 3), (cS 6 2, 8), (cS 6 4, 12), (cS 6 5, 3), (cC 1, 3), (cC 3, 3), (cC 4, 3)], [(cS 0 2, 14), (cS 2 0, 2), (cS 2 5, 2), (cS 3 4, 3), (cS 3 6, 3), (cS 4 6, 2), (cS 5 6, 3), (cS 6 0, 2), (cS 6 2, 3), (cR 0, 3), (cR 1, 3), (cC 0, 15), (cC 5, 15)]),
  .root (4, [(cS 2 1, 2), (cS 2 2, 2), (cS 2 3, 2), (cS 3 0, 2), (cS 3 6, 2), (cS 4 3, 2), (cS 4 5, 2), (cS 6 4, 2), (cC 4, 2)], [(cS 0 2, 1), (cS 0 5, 1), (cS 1 0, 2), (cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 5, 2), (cS 4 1, 2), (cS 5 0, 1), (cS 5 3, 2), (cS 5 6, 2), (cS 6 1, 2), (cS 6 6, 2), (cR 0, 1), (cC 0, 1), (cC 2, 2)]),
  .root (12, [(cS 1 3, 3), (cS 1 5, 12), (cS 2 3, 9), (cS 3 3, 3), (cS 4 1, 4), (cS 4 2, 1), (cS 5 0, 4), (cS 5 1, 4), (cS 5 2, 3), (cS 5 6, 2), (cS 6 0, 4), (cS 6 4, 2), (cS 6 5, 10), (cS 6 6, 2)], [(cS 0 0, 4), (cS 0 1, 2), (cS 0 2, 3), (cS 0 3, 1), (cS 1 0, 3), (cS 1 1, 2), (cS 1 2, 1), (cS 1 6, 3), (cS 2 1, 7), (cS 2 5, 3), (cS 2 6, 6), (cS 3 0, 3), (cS 4 3, 1), (cS 4 5, 4), (cS 4 6, 4), (cS 5 3, 3), (cS 6 2, 3), (cS 6 3, 1), (cR 0, 2), (cR 3, 3), (cR 4, 2), (cC 2, 2), (cC 4, 6)]),
  .root (20, [(cS 0 4, 5), (cS 0 5, 3), (cS 0 6, 5), (cS 1 4, 9), (cS 2 3, 20), (cS 2 5, 8), (cS 3 5, 9), (cS 5 0, 2), (cS 5 4, 8), (cS 5 6, 9), (cS 6 4, 9), (cC 5, 3), (cC 6, 9)], [(cS 0 0, 8), (cS 0 3, 3), (cS 1 0, 2), (cS 1 2, 2), (cS 2 6, 6), (cS 3 1, 2), (cS 4 3, 5), (cS 4 4, 12), (cS 5 2, 2), (cS 6 2, 3), (cC 0, 12), (cC 1, 6), (cC 2, 12), (cC 3, 3)]),
  .root (2, [(cS 0 4, 1), (cS 1 5, 1), (cS 2 3, 2), (cS 3 5, 1), (cS 4 1, 1), (cS 5 2, 1), (cS 5 4, 1), (cC 5, 1)], [(cS 0 2, 1), (cS 2 2, 1), (cS 4 3, 1), (cC 0, 1), (cC 1, 1), (cC 3, 1), (cC 6, 1)]),
  .root (20, [(cS 0 4, 3), (cS 0 5, 4), (cS 0 6, 1), (cS 1 3, 8), (cS 1 5, 6), (cS 2 3, 12), (cS 2 5, 5), (cS 3 3, 8), (cS 4 3, 6), (cS 4 4, 6), (cS 5 0, 1), (cS 5 4, 8), (cS 5 6, 9), (cS 6 0, 4), (cS 6 4, 4), (cS 6 6, 6), (cC 5, 9)], [(cS 0 0, 3), (cS 0 2, 1), (cS 0 3, 9), (cS 1 0, 2), (cS 1 2, 4), (cS 1 6, 9), (cS 2 1, 3), (cS 2 6, 3), (cS 3 1, 2), (cS 3 5, 6), (cS 3 6, 11), (cS 4 1, 3), (cS 4 6, 4), (cS 5 1, 1), (cS 5 2, 3), (cS 5 3, 5), (cS 6 2, 4), (cS 6 3, 4), (cC 0, 6), (cC 1, 9), (cC 2, 6)]),
  .root (20, [(cS 0 5, 7), (cS 1 3, 5), (cS 1 5, 13), (cS 2 3, 6), (cS 2 5, 7), (cS 3 2, 1), (cS 3 3, 4), (cS 3 4, 4), (cS 4 1, 3), (cS 4 2, 6), (cS 4 4, 3), (cS 5 1, 2), (cS 5 2, 9), (cS 5 4, 8), (cS 6 4, 6), (cS 6 5, 7), (cC 3, 9)], [(cS 0 0, 2), (cS 0 2, 10), (cS 0 3, 6), (cS 1 0, 3), (cS 1 2, 3), (cS 2 1, 10), (cS 2 6, 2), (cS 3 1, 3), (cS 3 5, 9), (cS 3 6, 3), (cS 4 5, 4), (cS 4 6, 2), (cS 5 5, 5), (cS 5 6, 3), (cS 6 0, 3), (cS 6 2, 3), (cC 0, 9), (cC 1, 6), (cC 2, 1), (cC 6, 6)]),
  .root (1, [(cC 3, 1), (cC 5, 1)], [(cC 0, 1), (cC 2, 1)]),
  .root (2, [(cS 1 4, 1), (cS 1 5, 1), (cS 1 6, 1), (cS 2 1, 1), (cS 2 3, 2), (cS 3 1, 1), (cS 5 0, 1), (cS 6 4, 1), (cS 6 5, 1), (cS 6 6, 1)], [(cS 0 0, 1), (cS 0 1, 1), (cS 0 3, 1), (cS 1 0, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 3 4, 1), (cS 3 6, 1), (cS 4 3, 1), (cS 4 5, 1), (cR 5, 1), (cC 2, 1)]),
  .root (4, [(cS 1 3, 2), (cS 1 5, 4), (cS 2 1, 1), (cS 2 3, 2), (cS 3 1, 3), (cS 3 3, 2), (cS 4 1, 1), (cS 5 1, 1), (cS 5 2, 2), (cS 6 4, 2), (cS 6 5, 2)], [(cS 0 1, 1), (cS 0 3, 2), (cS 1 1, 1), (cS 1 2, 2), (cS 3 4, 2), (cS 3 5, 2), (cS 4 3, 2), (cS 5 4, 2), (cS 5 5, 2), (cS 6 1, 1), (cS 6 2, 2), (cC 0, 2), (cC 6, 2)]),
  .root (10, [(cS 0 5, 2), (cS 1 3, 6), (cS 1 4, 3), (cS 1 5, 3), (cS 1 6, 4), (cS 2 2, 1), (cS 2 3, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 6, 1), (cS 4 6, 2), (cS 6 4, 5), (cS 6 5, 3), (cR 2, 2), (cR 3, 6), (cC 4, 1), (cC 5, 1)], [(cS 0 0, 6), (cS 0 1, 2), (cS 0 2, 1), (cS 1 0, 4), (cS 1 1, 4), (cS 4 2, 2), (cS 4 3, 3), (cS 4 4, 5), (cS 4 5, 3), (cS 5 0, 6), (cS 5 1, 2), (cS 5 2, 1), (cS 5 6, 2), (cS 6 2, 2), (cS 6 3, 2), (cS 6 6, 2), (cR 4, 2), (cR 6, 2), (cC 2, 3)]),
  .root (20, [(cS 0 5, 7), (cS 1 3, 7), (cS 1 5, 12), (cS 1 6, 1), (cS 2 2, 2), (cS 2 3, 3), (cS 3 1, 12), (cS 3 2, 3), (cS 3 3, 4), (cS 3 4, 3), (cS 4 3, 10), (cS 5 4, 7), (cS 6 4, 2), (cS 6 5, 8), (cR 2, 8), (cC 4, 3)], [(cS 0 0, 7), (cS 0 1, 4), (cS 0 2, 6), (cS 0 3, 10), (cS 1 1, 4), (cS 1 2, 1), (cS 3 5, 6), (cS 3 6, 8), (cS 4 5, 8), (cS 5 1, 8), (cS 5 2, 4), (cS 5 6, 4), (cS 6 2, 5), (cS 6 3, 5), (cR 5, 3), (cC 0, 7), (cC 1, 2), (cC 2, 3), (cC 6, 6)]),
  .root (3, [(cS 0 0, 1), (cS 0 1, 1), (cS 0 4, 1), (cS 3 5, 1), (cS 4 2, 1), (cS 4 6, 1), (cS 5 1, 1), (cS 6 2, 1), (cS 6 5, 2), (cR 5, 1), (cC 0, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 1 5, 2), (cS 2 1, 1), (cS 2 2, 1), (cS 2 4, 1), (cS 3 1, 1), (cS 4 4, 1), (cS 5 4, 1), (cR 1, 1), (cR 3, 1), (cC 3, 1)]),
  .root (24, [(cS 0 0, 9), (cS 0 1, 8), (cS 0 6, 8), (cS 1 0, 7), (cS 3 3, 1), (cS 4 2, 10), (cS 4 3, 7), (cS 4 4, 10), (cS 4 5, 8), (cS 5 0, 9), (cS 5 1, 9), (cS 5 3, 2), (cS 5 6, 8), (cS 6 4, 8), (cS 6 5, 9), (cR 4, 6), (cR 6, 7)], [(cS 0 2, 1), (cS 0 3, 8), (cS 0 4, 1), (cS 0 5, 1), (cS 1 5, 7), (cS 1 6, 1), (cS 2 1, 3), (cS 2 2, 4), (cS 2 3, 3), (cS 2 4, 4), (cS 3 0, 4), (cS 3 5, 3), (cS 3 6, 4), (cS 4 6, 2), (cS 6 2, 8), (cS 6 3, 7), (cR 1, 15), (cR 2, 2), (cR 3, 15)]),
  .root (24, [(cS 0 0, 11), (cS 0 1, 7), (cS 1 0, 5), (cS 1 1, 1), (cS 3 4, 8), (cS 3 6, 5), (cS 4 3, 6), (cS 4 4, 10), (cS 4 5, 6), (cS 4 6, 11), (cS 5 0, 10), (cS 5 4, 8), (cS 6 0, 6), (cS 6 4, 8), (cS 6 5, 16), (cC 6, 8)], [(cS 0 3, 6), (cS 0 4, 2), (cS 0 5, 4), (cS 1 3, 3), (cS 1 5, 13), (cS 1 6, 2), (cS 2 2, 1), (cS 2 4, 4), (cS 3 1, 4), (cS 4 1, 6), (cS 5 2, 6), (cS 6 2, 6), (cR 1, 5), (cR 2, 5), (cR 3, 7), (cC 1, 8), (cC 2, 4), (cC 3, 8)]),
  .root (8, [(cS 0 0, 2), (cS 0 1, 4), (cS 0 6, 4), (cS 1 0, 2), (cS 3 0, 2), (cS 3 4, 2), (cS 3 5, 4), (cS 3 6, 4), (cS 4 2, 2), (cS 4 3, 4), (cS 5 1, 1), (cS 5 2, 3), (cS 5 3, 1), (cS 5 4, 1), (cS 5 5, 5), (cS 6 4, 6), (cS 6 5, 2), (cR 4, 2)], [(cS 0 3, 4), (cS 0 5, 2), (cS 1 5, 2), (cS 2 1, 2), (cS 2 3, 6), (cS 3 1, 4), (cS 5 0, 5), (cS 5 6, 1), (cS 6 0, 2), (cS 6 2, 4), (cR 1, 4), (cR 2, 2)]),
  .root (2, [(cS 6 4, 1), (cS 6 5, 1), (cC 0, 1), (cC 1, 1), (cC 2, 1), (cC 6, 1)], [(cS 0 3, 1), (cS 1 5, 1), (cS 2 3, 1), (cS 3 5, 1), (cS 4 4, 1), (cC 3, 1), (cC 5, 1)]),
  .root (20, [(cS 0 0, 2), (cS 1 0, 3), (cS 2 2, 5), (cS 3 1, 2), (cS 4 1, 3), (cS 4 6, 2), (cS 5 6, 3), (cS 6 0, 3), (cS 6 4, 11), (cS 6 5, 6), (cR 2, 3), (cR 3, 3), (cC 0, 3), (cC 1, 12), (cC 5, 3), (cC 6, 12)], [(cS 0 3, 8), (cS 1 3, 9), (cS 1 5, 20), (cS 2 4, 8), (cS 3 2, 2), (cS 3 3, 6), (cS 3 4, 3), (cS 4 4, 11), (cS 5 1, 2), (cS 5 2, 9), (cS 5 4, 6), (cC 2, 9), (cC 3, 3)]),
  .root (2, [(cS 1 0, 1), (cS 3 0, 1), (cS 6 4, 1), (cC 1, 1), (cC 2, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 3, 1), (cS 1 5, 2), (cS 2 2, 1), (cS 2 4, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 6 0, 1), (cC 3, 1)]),
  .root (4, [(cS 0 1, 1), (cS 1 2, 1), (cS 2 1, 1), (cS 3 2, 1), (cS 4 3, 1), (cS 4 4, 3), (cS 6 4, 3), (cS 6 5, 1), (cC 0, 1), (cC 1, 2), (cC 6, 3)], [(cS 0 3, 2), (cS 1 3, 1), (cS 1 5, 3), (cS 2 3, 2), (cS 3 3, 1), (cS 3 5, 3), (cS 4 1, 1), (cS 5 1, 1), (cS 5 2, 2), (cS 6 2, 1), (cC 3, 1), (cC 5, 1)]),
  .root (12, [(cS 0 0, 3), (cS 1 0, 6), (cS 1 1, 1), (cS 2 0, 3), (cS 2 1, 3), (cS 3 0, 4), (cS 3 1, 1), (cS 4 1, 3), (cS 4 3, 5), (cS 4 4, 7), (cS 5 2, 1), (cS 6 4, 9), (cS 6 5, 3), (cC 0, 3), (cC 1, 1), (cC 2, 7)], [(cS 0 2, 1), (cS 0 3, 7), (cS 0 5, 3), (cS 1 3, 2), (cS 1 4, 1), (cS 1 5, 3), (cS 2 3, 12), (cS 2 5, 5), (cS 3 5, 4), (cS 3 6, 1), (cS 4 6, 3), (cS 5 0, 3), (cS 5 6, 3), (cS 6 0, 3), (cS 6 2, 1), (cS 6 3, 1), (cR 0, 2), (cR 5, 2), (cC 5, 3), (cC 6, 1)]),
  .root (30, [(cS 0 0, 1), (cS 0 1, 9), (cS 1 0, 20), (cS 1 2, 10), (cS 2 1, 20), (cS 2 6, 1), (cS 3 0, 11), (cS 3 1, 1), (cS 4 3, 10), (cS 4 4, 11), (cS 4 5, 10), (cS 4 6, 2), (cS 5 4, 9), (cS 6 4, 16), (cS 6 5, 14), (cR 3, 9), (cC 6, 9)], [(cS 0 3, 2), (cS 1 3, 11), (cS 1 5, 19), (cS 2 3, 13), (cS 2 4, 11), (cS 2 5, 11), (cS 3 2, 11), (cS 4 1, 9), (cS 5 0, 12), (cS 5 1, 9), (cS 5 2, 14), (cS 5 6, 9), (cS 6 0, 9), (cS 6 2, 11), (cR 0, 11), (cC 3, 6)]),
  .root (60, [(cS 0 0, 8), (cS 0 5, 7), (cS 1 0, 26), (cS 1 4, 8), (cS 1 5, 52), (cS 1 6, 8), (cS 4 1, 25), (cS 4 2, 17), (cS 5 2, 34), (cS 6 0, 8), (cS 6 5, 35), (cR 5, 9), (cR 6, 18), (cC 0, 26)], [(cS 0 2, 60), (cS 0 4, 24), (cS 1 3, 18), (cS 2 1, 16), (cS 2 2, 18), (cS 3 6, 16), (cS 4 3, 25), (cS 4 5, 25), (cS 4 6, 26), (cS 5 4, 17), (cR 2, 26), (cR 3, 18), (cC 4, 18)]),
  .root (1, [(cC 0, 1), (cC 5, 1)], [(cC 1, 1), (cC 3, 1)]),
  .splitS0 [.leaf (2, [(cS 0 0, 1), (cS 1 0, 1), (cS 3 0, 1), (cS 4 2, 1), (cS 5 2, 1), (cS 6 1, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 1 2, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 5 0, 2), (cC 3, 1)]), .leaf (10, [(cS 0 0, 5), (cS 0 5, 2), (cS 1 0, 5), (cS 1 6, 2), (cS 2 5, 2), (cS 3 0, 2), (cS 3 6, 5), (cS 4 1, 3), (cS 5 1, 4), (cS 5 2, 3), (cS 6 1, 3), (cS 6 4, 2), (cC 4, 5), (cC 5, 3), (cC 6, 3)], [(cS 0 1, 2), (cS 0 2, 3), (cS 1 2, 2), (cS 1 3, 2), (cS 2 1, 5), (cS 3 1, 5), (cS 3 3, 4), (cS 4 3, 1), (cS 4 4, 2), (cS 5 0, 3), (cS 5 6, 4), (cS 6 2, 2), (cS 6 6, 3), (cC 2, 3), (cC 3, 3)]), .leaf (2, [(cS 1 0, 1), (cS 3 0, 1), (cS 5 2, 1), (cC 1, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 3 1, 1), (cS 4 3, 1), (cS 5 0, 1), (cS 6 0, 1), (cC 3, 1)]), .leaf (4, [(cS 0 1, 1), (cS 1 0, 2), (cS 1 1, 1), (cS 3 0, 2), (cS 4 1, 1), (cS 5 1, 1), (cS 5 2, 2), (cS 6 1, 1), (cC 4, 2), (cC 5, 2), (cC 6, 2)], [(cS 0 2, 2), (cS 2 1, 1), (cS 2 2, 2), (cS 3 1, 3), (cS 4 3, 2), (cS 5 0, 2), (cS 6 0, 2), (cC 3, 2)]), .leaf (10, [(cS 0 0, 5), (cS 0 5, 2), (cS 1 0, 5), (cS 1 6, 2), (cS 2 5, 2), (cS 3 0, 2), (cS 3 6, 5), (cS 4 1, 1), (cS 5 1, 4), (cS 5 2, 5), (cS 5 4, 1), (cS 6 1, 1), (cS 6 4, 1), (cC 4, 5), (cC 5, 3), (cC 6, 3)], [(cS 0 1, 1), (cS 0 2, 4), (cS 0 3, 1), (cS 1 2, 3), (cS 1 3, 1), (cS 2 1, 5), (cS 2 3, 1), (cS 3 1, 5), (cS 3 3, 5), (cS 3 4, 1), (cS 4 1, 2), (cS 4 4, 1), (cS 5 0, 3), (cS 5 6, 4), (cS 6 1, 3), (cS 6 6, 3), (cC 2, 2), (cC 3, 3)]), .leaf (5, [(cS 0 0, 2), (cS 0 5, 1), (cS 0 6, 1), (cS 1 0, 3), (cS 1 4, 1), (cS 1 6, 1), (cS 2 5, 2), (cS 3 0, 1), (cS 3 6, 3), (cS 4 2, 1), (cS 5 1, 2), (cS 5 2, 2), (cS 5 4, 1), (cS 6 1, 1), (cS 6 4, 1), (cC 4, 2), (cC 5, 1), (cC 6, 1)], [(cS 0 1, 2), (cS 0 2, 1), (cS 0 3, 1), (cS 1 2, 2), (cS 2 1, 2), (cS 2 2, 1), (cS 2 3, 1), (cS 3 1, 3), (cS 3 3, 2), (cS 3 4, 1), (cS 5 0, 2), (cS 5 6, 2), (cS 6 2, 2), (cS 6 6, 1), (cR 4, 1), (cC 3, 1)]), .leaf (2, [(cS 5 2, 1), (cC 0, 1), (cC 1, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 1 3, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 5 0, 2), (cC 3, 1)]), .leaf (16, [(cS 0 0, 6), (cS 0 6, 2), (cS 1 0, 10), (cS 1 5, 1), (cS 1 6, 4), (cS 2 5, 2), (cS 3 0, 4), (cS 3 6, 8), (cS 4 1, 2), (cS 5 1, 9), (cS 5 2, 5), (cS 6 1, 3), (cS 6 5, 1), (cC 4, 10), (cC 5, 5), (cC 6, 4)], [(cS 0 1, 7), (cS 0 2, 4), (cS 2 1, 6), (cS 2 2, 5), (cS 3 1, 10), (cS 4 3, 6), (cS 4 4, 3), (cS 5 0, 5), (cS 5 6, 7), (cS 6 6, 4), (cC 2, 5), (cC 3, 7)]), .leaf (2, [(cS 1 6, 1), (cS 3 6, 1), (cS 5 2, 1), (cC 0, 1), (cC 1, 1), (cC 4, 1), (cC 5, 1)], [(cS 0 2, 1), (cS 1 3, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 5 6, 1), (cS 6 6, 1), (cC 3, 1)]), .leaf (2, [(cS 1 6, 1), (cS 3 6, 1), (cS 5 2, 1), (cC 0, 1), (cC 1, 1), (cC 4, 1), (cC 5, 1)], [(cS 0 2, 1), (cS 1 3, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 5 6, 1), (cS 6 6, 1), (cC 3, 1)]), .leaf (4, [(cS 0 1, 1), (cS 1 0, 2), (cS 3 0, 2), (cS 5 1, 1), (cS 5 2, 2), (cC 1, 1), (cC 4, 2), (cC 5, 2), (cC 6, 2)], [(cS 0 2, 2), (cS 1 2, 2), (cS 2 1, 1), (cS 3 1, 3), (cS 3 3, 2), (cS 5 0, 2), (cS 6 0, 2), (cC 3, 2)]), .leaf (16, [(cS 0 1, 4), (cS 0 6, 2), (cS 1 0, 8), (cS 1 5, 2), (cS 2 6, 2), (cS 3 5, 2), (cS 3 6, 8), (cS 4 6, 2), (cS 5 1, 6), (cS 5 2, 6), (cS 6 1, 1), (cS 6 4, 2), (cC 1, 4), (cC 4, 7), (cC 5, 7), (cC 6, 6)], [(cS 0 2, 3), (cS 0 3, 2), (cS 1 2, 5), (cS 1 3, 2), (cS 2 1, 4), (cS 2 2, 3), (cS 3 1, 12), (cS 3 3, 6), (cS 4 3, 3), (cS 4 4, 2), (cS 5 0, 6), (cS 5 6, 2), (cS 6 0, 7), (cS 6 2, 4), (cS 6 6, 1), (cC 3, 7)])],
  .root (20, [(cS 0 0, 5), (cS 0 5, 5), (cS 1 0, 12), (cS 1 5, 6), (cS 1 6, 6), (cS 2 5, 5), (cS 4 3, 2), (cS 4 4, 12), (cS 4 6, 8), (cS 5 6, 6), (cS 6 0, 12), (cS 6 5, 12), (cC 0, 3), (cC 4, 6), (cC 5, 3)], [(cS 0 2, 2), (cS 1 2, 3), (cS 1 4, 5), (cS 3 6, 14), (cS 4 1, 2), (cS 4 6, 3), (cS 5 2, 3), (cS 6 2, 3), (cR 2, 3), (cR 3, 3), (cC 1, 15), (cC 3, 15)]),
  .splitS0 [.leaf (4, [(cS 0 0, 2), (cS 1 0, 2), (cS 1 6, 2), (cS 3 3, 1), (cS 4 2, 2), (cS 4 3, 1), (cS 5 2, 2), (cS 5 3, 1), (cC 4, 2), (cC 5, 2)], [(cS 0 2, 2), (cS 0 3, 1), (cS 1 3, 1), (cS 2 2, 2), (cS 2 3, 1), (cS 3 0, 2), (cS 3 6, 2), (cS 4 6, 2), (cS 5 0, 2), (cS 6 3, 1), (cS 6 6, 2), (cC 1, 2)]), .leaf (16, [(cS 0 0, 3), (cS 0 1, 5), (cS 0 6, 3), (cS 1 0, 6), (cS 1 1, 2), (cS 1 5, 1), (cS 1 6, 4), (cS 2 0, 1), (cS 2 6, 6), (cS 3 2, 1), (cS 3 3, 3), (cS 4 1, 3), (cS 4 2, 4), (cS 4 3, 8), (cS 4 4, 1), (cS 5 1, 4), (cS 5 2, 5), (cS 6 4, 1), (cC 4, 7), (cC 5, 8)], [(cS 0 2, 3), (cS 0 3, 1), (cS 1 2, 2), (cS 1 3, 10), (cS 2 1, 3), (cS 2 2, 6), (cS 2 3, 6), (cS 2 4, 1), (cS 3 0, 6), (cS 3 1, 4), (cS 3 6, 3), (cS 4 6, 13), (cS 5 0, 5), (cS 5 6, 3), (cS 6 0, 4), (cS 6 2, 4), (cS 6 3, 8), (cS 6 6, 6), (cC 1, 4)]), .leaf (2, [(cS 0 0, 1), (cS 1 0, 1), (cS 1 6, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 5 1, 1), (cS 5 3, 1), (cC 4, 1), (cC 5, 1)], [(cS 0 2, 1), (cS 1 3, 1), (cS 2 2, 1), (cS 3 0, 1), (cS 3 6, 1), (cS 4 6, 1), (cS 5 6, 1), (cS 6 3, 1), (cS 6 6, 1), (cC 1, 1)]), .leaf (16, [(cS 0 1, 7), (cS 0 6, 4), (cS 1 0, 9), (cS 1 6, 3), (cS 2 6, 4), (cS 3 3, 5), (cS 4 2, 5), (cS 4 3, 6), (cS 5 1, 8), (cS 5 2, 3), (cS 5 3, 2), (cC 4, 8), (cC 5, 9)], [(cS 0 2, 2), (cS 0 3, 3), (cS 1 3, 6), (cS 2 0, 4), (cS 2 1, 1), (cS 2 2, 8), (cS 2 3, 3), (cS 3 0, 9), (cS 3 6, 3), (cS 4 1, 5), (cS 4 5, 1), (cS 4 6, 12), (cS 5 0, 1), (cS 5 6, 3), (cS 6 0, 7), (cS 6 3, 6), (cS 6 6, 5), (cC 1, 2), (cC 2, 5)]), .leaf (8, [(cS 0 0, 3), (cS 1 0, 5), (cS 1 5, 1), (cS 1 6, 3), (cS 3 3, 2), (cS 4 2, 3), (cS 4 3, 1), (cS 4 4, 1), (cS 5 1, 4), (cS 5 2, 1), (cS 5 3, 1), (cS 6 5, 1), (cC 3, 2), (cC 4, 3), (cC 5, 4)], [(cS 0 1, 1), (cS 0 2, 3), (cS 1 2, 3), (cS 1 3, 2), (cS 2 1, 2), (cS 2 2, 3), (cS 3 1, 5), (cS 3 6, 7), (cS 4 0, 3), (cS 4 6, 1), (cS 5 0, 1), (cS 5 6, 3), (cS 6 0, 2), (cS 6 1, 1), (cS 6 2, 2), (cS 6 3, 2), (cS 6 6, 2), (cR 0, 1), (cR 2, 1)]), .leaf (20, [(cS 0 0, 8), (cS 0 6, 3), (cS 1 0, 12), (cS 1 6, 5), (cS 2 6, 3), (cS 3 3, 5), (cS 4 2, 9), (cS 4 3, 6), (cS 5 1, 6), (cS 5 2, 5), (cS 5 3, 5), (cS 6 3, 2), (cC 4, 9), (cC 5, 12)], [(cS 0 1, 3), (cS 0 2, 6), (cS 0 3, 5), (cS 1 1, 2), (cS 1 2, 3), (cS 1 3, 6), (cS 2 2, 9), (cS 2 3, 6), (cS 3 0, 14), (cS 3 2, 5), (cS 3 6, 6), (cS 4 5, 6), (cS 4 6, 8), (cS 5 0, 8), (cS 5 6, 6), (cS 6 0, 3), (cS 6 2, 5), (cS 6 3, 4), (cS 6 6, 6), (cC 1, 6)]), .leaf (2, [(cS 0 0, 1), (cS 1 0, 1), (cS 1 6, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 5 1, 1), (cS 5 3, 1), (cC 4, 1), (cC 5, 1)], [(cS 0 2, 1), (cS 1 3, 1), (cS 2 2, 1), (cS 3 0, 1), (cS 3 6, 1), (cS 4 6, 1), (cS 5 6, 1), (cS 6 3, 1), (cS 6 6, 1), (cC 1, 1)]), .leaf (16, [(cS 0 0, 3), (cS 0 1, 5), (cS 0 6, 1), (cS 1 0, 4), (cS 1 1, 4), (cS 1 6, 8), (cS 2 0, 1), (cS 2 6, 3), (cS 3 2, 1), (cS 3 3, 6), (cS 4 1, 3), (cS 4 2, 4), (cS 4 3, 5), (cS 5 1, 4), (cS 5 2, 5), (cS 5 3, 3), (cC 4, 8), (cC 5, 8)], [(cS 0 2, 3), (cS 0 3, 3), (cS 1 3, 13), (cS 2 1, 3), (cS 2 2, 6), (cS 2 3, 3), (cS 3 0, 6), (cS 3 1, 4), (cS 3 6, 6), (cS 4 6, 10), (cS 5 0, 5), (cS 5 6, 1), (cS 6 0, 4), (cS 6 2, 4), (cS 6 3, 6), (cS 6 6, 8), (cC 1, 4)]), .leaf (10, [(cS 0 1, 1), (cS 1 0, 8), (cS 1 1, 1), (cS 1 5, 4), (cS 1 6, 2), (cS 3 3, 4), (cS 4 1, 1), (cS 4 2, 4), (cS 4 4, 4), (cS 5 1, 3), (cS 5 3, 4), (cS 6 4, 3), (cS 6 5, 1), (cC 2, 2), (cC 4, 2), (cC 5, 4)], [(cS 0 2, 2), (cS 0 3, 2), (cS 1 3, 6), (cS 2 1, 1), (cS 3 1, 3), (cS 3 6, 6), (cS 4 0, 4), (cS 4 6, 4), (cS 5 6, 2), (cS 6 0, 5), (cS 6 2, 3), (cS 6 3, 1), (cS 6 6, 3), (cR 0, 2), (cR 2, 4), (cC 1, 2)]), .leaf (24, [(cS 0 0, 1), (cS 0 1, 10), (cS 0 6, 6), (cS 1 0, 4), (cS 1 5, 5), (cS 1 6, 3), (cS 2 6, 9), (cS 4 1, 1), (cS 4 2, 17), (cS 4 3, 7), (cS 4 4, 7), (cS 5 1, 6), (cS 6 4, 5), (cS 6 5, 1), (cR 1, 2), (cC 0, 8), (cC 4, 10), (cC 5, 8)], [(cS 1 2, 10), (cS 1 3, 7), (cS 2 1, 9), (cS 2 3, 10), (cS 3 1, 5), (cS 4 6, 17), (cS 5 0, 6), (cS 5 6, 7), (cS 6 0, 2), (cS 6 2, 15), (cS 6 3, 2), (cS 6 6, 9), (cR 3, 7), (cC 1, 3), (cC 3, 7)]), .leaf (4, [(cS 0 1, 2), (cS 1 0, 2), (cS 1 5, 1), (cS 1 6, 2), (cS 3 2, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 4 3, 1), (cS 4 5, 1), (cS 5 1, 2), (cS 5 2, 1), (cS 5 3, 1), (cS 6 5, 1), (cC 4, 2), (cC 5, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 1 2, 1), (cS 1 3, 1), (cS 2 1, 1), (cS 2 2, 1), (cS 3 1, 2), (cS 3 6, 2), (cS 4 0, 2), (cS 4 6, 1), (cS 6 0, 2), (cS 6 2, 1), (cS 6 3, 1), (cS 6 6, 1), (cR 2, 1), (cC 6, 1)]), .leaf (12, [(cS 0 0, 3), (cS 0 1, 3), (cS 0 5, 1), (cS 1 0, 5), (cS 1 1, 1), (cS 1 6, 6), (cS 2 4, 1), (cS 2 6, 1), (cS 3 2, 1), (cS 3 3, 4), (cS 4 1, 2), (cS 4 2, 4), (cS 4 3, 3), (cS 4 4, 1), (cS 5 1, 3), (cS 5 2, 3), (cS 5 3, 2), (cR 6, 1), (cC 4, 6), (cC 5, 5)], [(cS 0 2, 4), (cS 0 3, 2), (cS 1 2, 1), (cS 1 3, 4), (cS 2 1, 2), (cS 2 2, 5), (cS 2 3, 1), (cS 3 0, 4), (cS 3 1, 2), (cS 3 6, 6), (cS 4 6, 6), (cS 5 0, 3), (cS 5 6, 1), (cS 6 0, 1), (cS 6 2, 2), (cS 6 3, 3), (cS 6 6, 5), (cC 0, 2), (cC 1, 2), (cC 2, 1)])],
  .root (20, [(cS 0 0, 10), (cS 0 5, 3), (cS 1 0, 10), (cS 1 5, 3), (cS 1 6, 2), (cS 2 5, 3), (cS 3 0, 3), (cS 3 4, 3), (cS 3 6, 9), (cS 4 3, 4), (cS 4 4, 3), (cS 5 4, 3), (cS 6 5, 3), (cC 4, 10), (cC 5, 4), (cC 6, 8)], [(cS 0 1, 2), (cS 0 3, 6), (cS 1 1, 7), (cS 1 3, 7), (cS 2 1, 2), (cS 2 3, 6), (cS 3 1, 7), (cS 3 3, 7), (cS 4 0, 2), (cS 4 2, 2), (cS 5 0, 9), (cS 5 2, 7), (cS 5 6, 9), (cS 6 2, 7), (cS 6 6, 2), (cC 1, 11), (cC 3, 7)]),
  .splitS0 [.leaf (2, [(cS 1 4, 1), (cS 1 6, 1), (cS 6 4, 1), (cS 6 6, 1), (cC 1, 2), (cC 4, 1), (cC 6, 1)], [(cS 3 4, 1), (cS 3 6, 1), (cS 4 4, 1), (cS 4 6, 1), (cC 2, 2)]), .leaf (2, [(cS 1 4, 1), (cS 1 5, 1), (cS 2 1, 1), (cS 4 2, 1), (cS 6 4, 1), (cS 6 5, 1), (cC 0, 1), (cC 1, 1), (cC 6, 1)], [(cS 2 4, 1), (cS 3 5, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 5 2, 1), (cC 2, 1), (cC 3, 1)]), .leaf (30, [(cS 0 0, 5), (cS 0 4, 3), (cS 0 5, 6), (cS 1 4, 5), (cS 1 5, 6), (cS 2 1, 6), (cS 2 4, 3), (cS 3 1, 5), (cS 3 2, 8), (cS 4 1, 7), (cS 5 6, 5), (cS 6 0, 7), (cS 6 4, 16), (cS 6 5, 12), (cR 1, 7), (cR 2, 7), (cC 0, 8), (cC 1, 10), (cC 5, 3), (cC 6, 10)], [(cS 0 3, 5), (cS 1 3, 4), (cS 2 3, 4), (cS 3 3, 5), (cS 3 4, 5), (cS 3 5, 12), (cS 3 6, 5), (cS 4 2, 2), (cS 4 4, 14), (cS 4 5, 6), (cS 4 6, 7), (cS 5 1, 6), (cS 5 2, 5), (cS 5 4, 10), (cS 6 2, 3), (cC 2, 17), (cC 3, 6)]), .leaf (2, [(cS 0 0, 1), (cS 0 4, 1), (cS 1 1, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 3 1, 1), (cS 4 1, 1), (cS 5 4, 1), (cS 6 0, 1), (cS 6 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 1 2, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 3 5, 2), (cS 5 2, 1), (cS 6 1, 1), (cS 6 3, 1), (cR 4, 1)]), .leaf (24, [(cS 0 0, 8), (cS 0 4, 7), (cS 0 5, 6), (cS 1 1, 8), (cS 1 4, 11), (cS 1 6, 10), (cS 2 1, 2), (cS 2 4, 7), (cS 3 1, 8), (cS 4 1, 8), (cS 5 0, 2), (cS 5 6, 6), (cS 6 0, 8), (cS 6 4, 14), (cS 6 5, 10), (cR 2, 6), (cC 1, 8), (cC 6, 8)], [(cS 0 1, 2), (cS 0 2, 3), (cS 1 3, 3), (cS 3 3, 2), (cS 3 4, 6), (cS 3 5, 5), (cS 3 6, 10), (cS 4 4, 13), (cS 4 5, 3), (cS 4 6, 6), (cS 5 1, 3), (cS 5 4, 5), (cR 5, 3), (cC 2, 19), (cC 3, 3)]), .leaf (5, [(cS 0 0, 1), (cS 1 2, 2), (cS 1 5, 2), (cS 2 0, 1), (cS 3 1, 2), (cS 3 2, 1), (cS 5 4, 1), (cS 5 6, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 1, 1), (cR 6, 1), (cC 0, 1), (cC 1, 2), (cC 4, 1), (cC 5, 1), (cC 6, 2)], [(cS 0 3, 2), (cS 1 3, 2), (cS 2 3, 2), (cS 3 3, 2), (cS 3 5, 3), (cS 3 6, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 5 1, 1), (cS 5 2, 2), (cS 6 2, 2), (cR 4, 1), (cC 3, 1)]), .leaf (20, [(cS 0 0, 2), (cS 0 5, 2), (cS 1 1, 5), (cS 1 4, 6), (cS 2 5, 2), (cS 2 6, 2), (cS 3 1, 5), (cS 3 2, 3), (cS 5 4, 2), (cS 5 6, 2), (cS 6 0, 3), (cS 6 4, 6), (cS 6 5, 3), (cR 1, 3), (cC 0, 3), (cC 1, 12), (cC 4, 6), (cC 5, 3), (cC 6, 12)], [(cS 0 3, 8), (cS 1 3, 9), (cS 2 3, 8), (cS 3 3, 9), (cS 3 4, 2), (cS 3 5, 18), (cS 3 6, 3), (cS 4 2, 5), (cS 4 4, 3), (cS 5 1, 3), (cS 5 2, 9), (cS 5 4, 3), (cS 6 2, 9), (cR 4, 3), (cC 3, 3)]), .leaf (6, [(cS 0 0, 1), (cS 1 4, 3), (cS 1 5, 1), (cS 2 0, 1), (cS 2 1, 2), (cS 3 1, 2), (cS 5 6, 1), (cS 6 0, 1), (cS 6 4, 3), (cS 6 5, 2), (cR 1, 1), (cR 4, 1), (cC 0, 1), (cC 1, 3), (cC 5, 1), (cC 6, 3)], [(cS 0 3, 2), (cS 2 3, 2), (cS 3 3, 2), (cS 3 4, 1), (cS 3 5, 5), (cS 3 6, 1), (cS 4 4, 2), (cS 5 1, 1), (cS 5 2, 2), (cS 5 4, 2), (cC 2, 3), (cC 3, 1)]), .leaf (6, [(cS 0 0, 2), (cS 0 4, 1), (cS 0 5, 1), (cS 0 6, 1), (cS 1 1, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 2 0, 1), (cS 3 1, 2), (cS 4 1, 2), (cS 5 4, 1), (cS 5 5, 1), (cS 5 6, 1), (cS 6 0, 2), (cS 6 4, 2), (cS 6 5, 1), (cS 6 6, 1), (cR 1, 1), (cR 2, 2), (cC 1, 2), (cC 4, 1), (cC 6, 2)], [(cS 3 4, 2), (cS 3 5, 1), (cS 3 6, 1), (cS 4 4, 2), (cS 4 5, 1), (cS 4 6, 3), (cS 5 1, 2), (cC 2, 4), (cC 3, 2)])],
  .root (4, [(cS 0 6, 2), (cS 1 0, 2), (cS 1 1, 2), (cS 1 4, 2), (cS 1 5, 2), (cS 2 1, 2), (cS 2 6, 2), (cS 3 0, 2), (cS 3 2, 2), (cS 4 1, 2), (cS 5 1, 1), (cS 5 2, 3), (cS 6 4, 2), (cS 6 5, 2)], [(cS 0 1, 2), (cS 0 2, 2), (cS 0 3, 2), (cS 1 3, 2), (cS 2 3, 2), (cS 2 5, 2), (cS 3 3, 2), (cS 3 5, 2), (cS 4 4, 2), (cS 4 6, 2), (cS 5 4, 1), (cS 5 6, 1), (cS 6 0, 2), (cR 5, 1)]),
  .splitS0 [.leaf (3, [(cS 0 0, 1), (cS 0 5, 1), (cS 1 0, 1), (cS 1 2, 2), (cS 2 5, 1), (cS 3 1, 2), (cS 3 6, 1), (cS 6 4, 1), (cC 0, 1), (cC 1, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 1 3, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 4 4, 1), (cS 5 0, 2), (cS 5 1, 1), (cS 5 2, 1), (cS 5 6, 1), (cS 6 2, 1), (cC 3, 1)]), .leaf (16, [(cS 0 0, 1), (cS 0 5, 2), (cS 1 0, 7), (cS 1 1, 8), (cS 1 6, 1), (cS 2 0, 1), (cS 2 1, 8), (cS 2 5, 2), (cS 3 0, 6), (cS 3 1, 16), (cS 3 6, 2), (cS 4 6, 1), (cS 6 4, 1), (cS 6 5, 1), (cC 4, 8), (cC 5, 6), (cC 6, 7)], [(cS 0 1, 7), (cS 0 2, 1), (cS 1 2, 3), (cS 1 3, 1), (cS 3 3, 4), (cS 4 3, 3), (cS 4 4, 2), (cS 5 0, 6), (cS 5 1, 10), (cS 5 2, 1), (cS 5 6, 2), (cS 6 0, 8), (cS 6 2, 3), (cC 2, 5), (cC 3, 7)]), .leaf (2, [(cS 1 0, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 4 2, 1), (cC 1, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 2 3, 1), (cS 4 3, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 2, 1), (cS 6 0, 1), (cC 3, 1)]), .leaf (2, [(cS 0 5, 1), (cS 2 4, 1), (cS 5 5, 1), (cS 6 4, 1), (cR 1, 1), (cR 3, 1), (cC 1, 1), (cC 6, 1)], [(cS 4 4, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 0, 1), (cC 2, 1), (cC 3, 1)]), .leaf (20, [(cS 0 0, 1), (cS 0 5, 2), (cS 1 0, 9), (cS 1 1, 12), (cS 1 6, 1), (cS 2 0, 1), (cS 2 1, 8), (cS 2 5, 2), (cS 3 0, 8), (cS 3 1, 12), (cS 3 6, 2), (cS 4 2, 8), (cS 4 6, 1), (cS 6 4, 1), (cS 6 5, 1), (cC 4, 10), (cC 5, 8), (cC 6, 9)], [(cS 0 1, 9), (cS 0 2, 6), (cS 1 2, 3), (cS 1 3, 1), (cS 2 3, 5), (cS 3 3, 6), (cS 4 1, 3), (cS 4 3, 3), (cS 4 4, 2), (cS 5 0, 8), (cS 5 1, 9), (cS 5 2, 6), (cS 5 6, 2), (cS 6 0, 10), (cS 6 2, 3), (cC 2, 2), (cC 3, 9)]), .leaf (3, [(cS 0 0, 2), (cS 0 5, 1), (cS 1 1, 2), (cS 1 6, 1), (cS 3 1, 3), (cS 3 6, 1), (cS 4 6, 1), (cS 6 5, 1), (cR 2, 1), (cC 4, 2), (cC 6, 1)], [(cS 0 1, 1), (cS 0 2, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 4 4, 1), (cS 5 0, 2), (cS 5 1, 1), (cS 5 2, 1), (cS 5 6, 1), (cC 2, 1), (cC 3, 1)]), .leaf (2, [(cS 1 2, 1), (cS 3 1, 1), (cC 0, 1), (cC 1, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 2, 1), (cS 1 3, 1), (cS 3 3, 1), (cS 5 0, 2), (cS 5 2, 2), (cC 3, 1)]), .leaf (2, [(cS 1 1, 2), (cS 1 6, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 2, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 0 1, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 0, 1), (cC 2, 1), (cC 3, 1)]), .leaf (2, [(cS 1 1, 1), (cS 1 6, 1), (cS 3 1, 1), (cS 3 6, 1), (cC 1, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 1 3, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 0, 1), (cS 6 2, 1), (cC 3, 1)]), .leaf (2, [(cS 1 1, 1), (cS 1 6, 1), (cS 3 1, 1), (cS 3 6, 1), (cC 1, 1), (cC 4, 1), (cC 5, 1), (cC 6, 1)], [(cS 1 3, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 6 0, 1), (cS 6 2, 1), (cC 3, 1)]), .leaf (20, [(cS 0 5, 2), (cS 1 0, 6), (cS 1 1, 3), (cS 1 2, 8), (cS 1 6, 3), (cS 2 4, 2), (cS 3 1, 11), (cS 3 6, 9), (cS 6 4, 2), (cC 0, 2), (cC 1, 9), (cC 4, 9), (cC 5, 9), (cC 6, 9)], [(cS 0 2, 4), (cS 1 2, 1), (cS 1 3, 3), (cS 2 3, 5), (cS 3 3, 6), (cS 4 3, 2), (cS 4 4, 3), (cS 5 0, 7), (cS 5 1, 13), (cS 5 2, 6), (cS 5 6, 3), (cS 6 0, 10), (cS 6 2, 4), (cC 2, 3), (cC 3, 9)]), .leaf (30, [(cS 0 0, 4), (cS 0 5, 4), (cS 1 0, 13), (cS 1 2, 6), (cS 1 6, 2), (cS 2 2, 6), (cS 3 0, 12), (cS 3 2, 6), (cS 3 6, 2), (cS 4 1, 5), (cS 4 2, 6), (cS 4 6, 5), (cS 6 4, 4), (cR 2, 5), (cC 1, 13), (cC 4, 13), (cC 5, 13), (cC 6, 11)], [(cS 1 3, 6), (cS 3 3, 6), (cS 4 3, 6), (cS 4 4, 5), (cS 5 0, 10), (cS 5 1, 20), (cS 5 6, 4), (cS 6 0, 13), (cS 6 2, 6), (cS 6 6, 3), (cC 2, 11), (cC 3, 13)])],
  .root (2, [(cS 0 6, 1), (cS 1 0, 1), (cS 1 1, 1), (cS 1 5, 1), (cS 2 1, 1), (cS 2 6, 1), (cS 3 1, 1), (cS 4 3, 1), (cS 6 5, 1), (cC 4, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 1 1, 1), (cS 1 3, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 3 5, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 4 6, 1), (cS 6 0, 1), (cS 6 2, 1), (cR 5, 1)]),
  .root (8, [(cS 0 0, 4), (cS 1 0, 2), (cS 1 1, 2), (cS 1 2, 2), (cS 2 3, 8), (cS 4 1, 2), (cS 4 2, 2), (cS 5 0, 3), (cS 5 1, 1), (cS 5 2, 1), (cS 5 6, 1), (cS 6 0, 2), (cS 6 5, 6), (cR 0, 2), (cR 5, 2)], [(cS 0 2, 2), (cS 0 3, 2), (cS 0 4, 2), (cS 1 5, 4), (cS 1 6, 4), (cS 2 1, 4), (cS 2 5, 2), (cS 2 6, 2), (cS 3 0, 2), (cS 4 3, 2), (cS 4 5, 2), (cS 4 6, 2), (cS 5 3, 1), (cS 5 4, 3), (cS 5 5, 1), (cS 6 2, 4), (cR 3, 4), (cC 4, 2)]),
  .root (30, [(cS 0 0, 6), (cS 0 1, 8), (cS 0 4, 6), (cS 1 0, 7), (cS 2 3, 23), (cS 3 5, 8), (cS 4 5, 7), (cS 4 6, 7), (cS 5 0, 8), (cS 5 4, 8), (cS 5 5, 5), (cS 5 6, 5), (cS 6 0, 7), (cS 6 5, 16), (cR 0, 7), (cR 2, 7), (cC 0, 2), (cC 4, 1), (cC 6, 8)], [(cS 0 3, 9), (cS 1 5, 23), (cS 2 1, 7), (cS 3 0, 6), (cS 3 1, 9), (cS 3 4, 7), (cS 4 1, 7), (cS 4 3, 15), (cS 4 4, 1), (cS 5 1, 12), (cS 5 2, 3), (cS 5 3, 5), (cS 5 4, 9), (cS 6 2, 7), (cS 6 3, 7), (cR 1, 7), (cR 3, 7), (cC 1, 1), (cC 2, 8)]),
  .root (2, [(cS 0 0, 1), (cS 0 1, 1), (cS 1 0, 1), (cS 2 3, 1), (cS 2 4, 1), (cS 3 0, 1), (cS 3 5, 1), (cS 4 5, 1), (cS 5 1, 1), (cS 6 4, 1), (cS 6 5, 1), (cC 2, 1)], [(cS 0 3, 1), (cS 1 4, 1), (cS 1 5, 1), (cS 2 1, 1), (cS 3 1, 1), (cS 4 3, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 6 3, 1), (cC 6, 1)]),
  .root (4, [(cS 0 0, 2), (cS 0 1, 1), (cS 0 6, 1), (cS 1 0, 1), (cS 1 3, 1), (cS 2 3, 2), (cS 3 3, 1), (cS 4 4, 2), (cS 5 0, 2), (cS 5 4, 1), (cS 5 6, 1), (cS 6 0, 1), (cS 6 4, 1), (cS 6 5, 3), (cC 3, 1)], [(cS 0 3, 1), (cS 0 4, 1), (cS 1 2, 1), (cS 1 5, 3), (cS 1 6, 1), (cS 2 0, 2), (cS 2 1, 1), (cS 2 5, 1), (cS 3 0, 2), (cS 3 1, 1), (cS 3 5, 3), (cS 4 1, 1), (cS 4 6, 2), (cS 6 2, 1), (cR 5, 1), (cC 2, 2)]),
  .root (30, [(cS 0 0, 15), (cS 0 4, 9), (cS 1 0, 15), (cS 1 3, 9), (cS 2 3, 13), (cS 3 3, 9), (cS 4 1, 8), (cS 4 2, 7), (cS 4 3, 6), (cS 4 4, 7), (cS 5 1, 6), (cS 5 2, 9), (cS 5 4, 9), (cS 6 4, 13), (cS 6 5, 8), (cC 3, 8)], [(cS 0 2, 15), (cS 0 3, 2), (cS 0 5, 7), (cS 1 2, 13), (cS 1 4, 2), (cS 1 5, 8), (cS 2 0, 6), (cS 2 1, 8), (cS 3 0, 5), (cS 3 1, 3), (cS 4 0, 5), (cS 4 6, 8), (cS 5 0, 9), (cS 5 5, 1), (cS 5 6, 6), (cS 6 0, 13), (cS 6 2, 13), (cR 2, 7), (cR 3, 10), (cC 1, 2), (cC 5, 13), (cC 6, 2)]),
  .root (4, [(cS 0 0, 2), (cS 1 0, 2), (cS 2 2, 1), (cS 2 3, 3), (cS 3 5, 1), (cS 3 6, 1), (cS 4 3, 2), (cS 4 5, 2), (cS 6 5, 2), (cC 4, 2)], [(cS 0 2, 1), (cS 0 5, 1), (cS 1 3, 1), (cS 1 4, 1), (cS 1 5, 2), (cS 2 5, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 3, 2), (cC 0, 1), (cC 1, 1), (cC 2, 2), (cC 6, 1)]),
  .splitS0 [.leaf (8, [(cS 0 1, 2), (cS 1 2, 2), (cS 1 4, 2), (cS 2 0, 2), (cS 2 1, 2), (cS 2 2, 2), (cS 2 3, 2), (cS 2 4, 2), (cS 3 1, 4), (cS 3 3, 4), (cS 5 0, 1), (cS 5 6, 1), (cS 6 0, 2), (cS 6 4, 3), (cS 6 5, 5), (cR 0, 2), (cR 1, 2), (cC 0, 2), (cC 6, 2)], [(cS 0 3, 1), (cS 1 5, 2), (cS 2 5, 6), (cS 3 4, 2), (cS 3 6, 2), (cS 4 2, 2), (cS 4 3, 3), (cS 4 5, 4), (cS 5 1, 3), (cS 5 2, 1), (cS 5 4, 2), (cS 6 2, 4), (cS 6 3, 2), (cR 4, 2), (cC 3, 1)]), .leaf (6, [(cS 0 1, 2), (cS 0 4, 1), (cS 0 6, 2), (cS 1 0, 2), (cS 1 2, 2), (cS 2 0, 1), (cS 2 1, 1), (cS 2 3, 2), (cS 3 1, 2), (cS 3 2, 1), (cS 3 3, 1), (cS 5 4, 2), (cS 5 6, 3), (cS 6 0, 3), (cS 6 5, 3), (cR 0, 1), (cR 1, 1), (cR 2, 2), (cC 4, 1)], [(cS 0 3, 2), (cS 1 5, 6), (cS 3 0, 1), (cS 3 4, 2), (cS 3 5, 1), (cS 3 6, 5), (cS 4 3, 1), (cS 5 1, 3), (cS 5 3, 2), (cS 6 2, 3), (cS 6 3, 1), (cR 4, 3)]), .leaf (5, [(cS 1 0, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 3 1, 2), (cS 3 3, 2), (cS 5 6, 2), (cS 6 0, 3), (cS 6 4, 2), (cS 6 5, 3), (cR 0, 2), (cR 1, 2), (cR 2, 2)], [(cS 0 2, 1), (cS 0 3, 1), (cS 1 5, 1), (cS 2 5, 1), (cS 2 6, 3), (cS 3 4, 2), (cS 3 6, 2), (cS 5 1, 2), (cS 5 2, 1), (cS 5 3, 1), (cS 5 4, 2), (cS 6 2, 2), (cS 6 3, 1), (cR 4, 3)]), .leaf (10, [(cS 0 1, 3), (cS 1 2, 2), (cS 1 6, 1), (cS 2 1, 3), (cS 2 2, 1), (cS 2 3, 6), (cS 3 1, 3), (cS 3 2, 2), (cS 5 4, 1), (cS 5 6, 1), (cS 6 0, 3), (cS 6 5, 6), (cS 6 6, 1), (cR 0, 1), (cR 1, 3), (cR 2, 1), (cC 0, 3), (cC 4, 3), (cC 6, 2)], [(cS 0 2, 1), (cS 0 3, 2), (cS 1 5, 3), (cS 2 5, 4), (cS 2 6, 3), (cS 3 3, 1), (cS 3 5, 2), (cS 3 6, 1), (cS 4 2, 1), (cS 4 3, 3), (cS 4 4, 1), (cS 4 5, 3), (cS 5 1, 4), (cS 5 2, 1), (cS 5 4, 2), (cS 6 2, 5), (cS 6 3, 3), (cR 4, 4), (cC 3, 1)]), .leaf (2, [(cS 1 0, 1), (cS 1 2, 1), (cS 2 3, 1), (cS 3 1, 1), (cS 5 4, 1), (cS 5 6, 1), (cS 6 0, 1), (cS 6 5, 1), (cR 0, 1), (cR 2, 1)], [(cS 1 5, 2), (cS 3 5, 1), (cS 3 6, 1), (cS 5 1, 1), (cS 6 2, 1), (cR 4, 1), (cC 3, 1)]), .leaf (24, [(cS 0 1, 5), (cS 0 4, 2), (cS 1 0, 7), (cS 1 2, 10), (cS 2 0, 6), (cS 2 1, 6), (cS 2 2, 6), (cS 2 3, 18), (cS 3 1, 10), (cS 5 4, 5), (cS 5 5, 4), (cS 5 6, 4), (cS 6 0, 7), (cS 6 5, 8), (cS 6 6, 2), (cR 0, 7), (cC 0, 3), (cC 1, 2), (cC 4, 7), (cC 6, 8)], [(cS 0 3, 4), (cS 0 5, 6), (cS 1 5, 18), (cS 2 5, 6), (cS 3 4, 3), (cS 3 5, 11), (cS 3 6, 3), (cS 4 2, 2), (cS 4 3, 7), (cS 5 1, 10), (cS 5 2, 3), (cS 6 2, 10), (cS 6 3, 6), (cR 3, 4), (cR 4, 7), (cR 5, 2), (cC 3, 4)])],
  .root (2, [(cS 1 0, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 3 1, 1), (cS 3 3, 1), (cS 4 1, 1), (cS 5 2, 1), (cS 6 0, 1), (cS 6 4, 2), (cR 1, 1)], [(cS 2 5, 1), (cS 3 6, 2), (cS 4 3, 1), (cS 4 4, 1), (cS 5 0, 1), (cS 5 6, 1), (cS 6 2, 1), (cR 0, 1), (cC 5, 1)]),
  .root (6, [(cS 0 0, 2), (cS 0 1, 2), (cS 4 6, 2), (cS 6 4, 3), (cS 6 5, 3), (cR 1, 4), (cR 2, 2), (cR 3, 4)], [(cS 1 3, 2), (cS 1 5, 6), (cS 4 2, 2), (cS 4 3, 2), (cS 4 4, 2), (cS 4 5, 2), (cS 5 0, 2), (cS 5 1, 2), (cS 6 0, 1), (cS 6 2, 3), (cS 6 3, 2), (cS 6 6, 2), (cR 4, 2), (cR 6, 1)]),
  .root (2, [(cS 0 0, 1), (cS 1 0, 1), (cS 1 2, 1), (cS 2 0, 1), (cS 2 1, 1), (cS 2 3, 1), (cS 3 2, 1), (cS 4 3, 1), (cS 6 4, 1), (cC 4, 1)], [(cS 0 2, 1), (cS 0 3, 1), (cS 0 5, 1), (cS 2 5, 1), (cS 3 0, 1), (cS 3 6, 1), (cS 4 1, 1), (cS 5 0, 1), (cS 5 2, 1), (cS 5 6, 1), (cS 6 0, 1), (cS 6 2, 1), (cC 5, 1)]),
  .root (8, [(cS 0 0, 3), (cS 0 1, 1), (cS 1 4, 1), (cS 1 5, 4), (cS 1 6, 1), (cS 2 3, 8), (cS 5 0, 1), (cS 5 6, 1), (cS 6 0, 3), (cS 6 4, 4), (cS 6 5, 4), (cS 6 6, 3), (cR 0, 1), (cR 1, 3)], [(cS 0 2, 1), (cS 0 3, 2), (cS 2 0, 4), (cS 2 1, 3), (cS 2 5, 4), (cS 3 6, 1), (cS 4 5, 1), (cS 5 3, 1), (cS 6 1, 1), (cS 6 2, 4), (cR 3, 3), (cR 4, 4), (cR 5, 2), (cC 1, 1), (cC 2, 1), (cC 4, 1)]),
  .root (2, [(cS 0 0, 1), (cS 1 5, 1), (cS 2 3, 1), (cS 3 3, 1), (cS 4 2, 1), (cS 5 1, 1), (cS 6 4, 1), (cS 6 5, 1), (cR 1, 1)], [(cS 0 1, 1), (cS 0 3, 1), (cS 2 1, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 3 4, 1), (cS 3 5, 1), (cS 4 4, 1), (cS 4 5, 1), (cS 5 0, 1), (cS 5 3, 1), (cS 6 2, 1), (cC 6, 1)]),
  .root (3, [(cS 0 0, 1), (cS 1 0, 1), (cS 1 4, 1), (cS 1 6, 1), (cS 2 3, 2), (cS 3 5, 1), (cS 3 6, 1), (cS 5 4, 1), (cS 6 4, 1), (cR 0, 1), (cR 2, 1), (cC 5, 1)], [(cS 0 3, 1), (cS 3 0, 1), (cS 3 1, 1), (cS 4 3, 2), (cS 4 4, 1), (cS 4 6, 1), (cS 5 0, 1), (cS 5 1, 1), (cS 5 6, 1), (cS 6 2, 1), (cS 6 3, 1), (cS 6 6, 1), (cC 1, 1), (cC 2, 1)]),
  .root (20, [(cS 0 0, 11), (cS 0 4, 3), (cS 0 5, 4), (cS 0 6, 4), (cS 1 0, 1), (cS 1 5, 2), (cS 1 6, 2), (cS 2 2, 2), (cS 2 3, 10), (cS 2 5, 8), (cS 3 3, 8), (cS 4 3, 6), (cS 4 4, 3), (cS 5 4, 8), (cS 6 5, 10), (cR 1, 8), (cC 4, 3)], [(cS 0 2, 9), (cS 0 3, 7), (cS 2 0, 3), (cS 2 6, 1), (cS 3 0, 2), (cS 3 1, 7), (cS 3 5, 7), (cS 3 6, 7), (cS 4 5, 5), (cS 4 6, 4), (cS 5 0, 7), (cS 5 1, 1), (cS 5 2, 7), (cS 5 6, 5), (cS 6 3, 7), (cR 3, 2), (cR 5, 3), (cC 0, 2), (cC 1, 7), (cC 2, 4), (cC 6, 3)]),
  .root (6, [(cS 0 0, 2), (cS 1 4, 2), (cS 1 6, 2), (cS 2 1, 2), (cS 2 3, 4), (cS 3 1, 2), (cS 6 4, 3), (cS 6 5, 3), (cR 0, 2), (cR 1, 2), (cR 2, 2)], [(cS 0 2, 2), (cS 2 0, 2), (cS 3 0, 2), (cS 3 4, 2), (cS 3 5, 4), (cS 3 6, 2), (cS 4 2, 2), (cS 4 3, 2), (cS 4 5, 2), (cS 5 0, 2), (cS 6 0, 1), (cS 6 2, 3), (cR 4, 2), (cR 5, 2), (cR 6, 1)])
]

private def checkP13Orbit (k : Fin 3) (certs : List SqCert) : Bool :=
  let n5 := near5 k
  checkAll4 (checkSqCase k n5 n5) (halves5 k) certs

private def checkP2Orbit (k : Fin 3) (certs : List SqCert) : Bool :=
  let n4 := near4 k
  let n6 := near6 k
  checkAll4 (checkSqCase k n4 n6) (subs4 k) certs

private def checkP5Orbit (k : Fin 3) (certs : List P5Cert) : Bool :=
  let n5 := near5 k
  checkAll4 (checkP5Case k n5) (halves5 k) certs

private theorem checkP13_0_ok : checkP13Orbit 0 p13Certs0 = true := by rfl
private theorem checkP13_1_ok : checkP13Orbit 1 p13Certs1 = true := by rfl
private theorem checkP13_2_ok : checkP13Orbit 2 p13Certs2 = true := by rfl

private theorem checkP2_0_ok : checkP2Orbit 0 p2Certs0 = true := by rfl
private theorem checkP2_1_ok : checkP2Orbit 1 p2Certs1 = true := by rfl
private theorem checkP2_2_ok : checkP2Orbit 2 p2Certs2 = true := by rfl

private theorem checkP4_0_ok : checkAll4 (checkP4Case 0) (subs4 0) p4Certs0 = true := by rfl
private theorem checkP4_1_ok : checkAll4 (checkP4Case 1) (subs4 1) p4Certs1 = true := by rfl
private theorem checkP4_2_ok : checkAll4 (checkP4Case 2) (subs4 2) p4Certs2 = true := by rfl

private theorem checkP5_0_ok : checkP5Orbit 0 p5Certs0 = true := by rfl
private theorem checkP5_1_ok : checkP5Orbit 1 p5Certs1 = true := by rfl
private theorem checkP5_2_ok : checkP5Orbit 2 p5Certs2 = true := by rfl

/-! ## Section 7: Refutation of All 4 Centered Profile Families -/

private structure CubeSlices where
  s : ZMod 7 → Finset (ZMod 7 × ZMod 7)
  disj : ∀ i : ZMod 7, Disjoint (s i) (s (i + 1))
  indep : ∀ i : ZMod 7, (C7 ⊠ C7).IsIndepSet ((s i ∪ s (i + 1) : Finset _) : Set _)

private def CubeSlices.ofIndep {S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))}
    (hS : (C7 ⊠ (C7 ⊠ C7)).IsIndepSet (S : Set _)) : CubeSlices where
  s := fun i => (S.filter fun p => p.1 = i).image Prod.snd
  disj := fun i => by
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [Finset.mem_image, Finset.mem_filter] at h1 h2
    obtain ⟨⟨a1, w1⟩, ⟨h1', ha1⟩, hw1⟩ := h1
    obtain ⟨⟨a2, w2⟩, ⟨h2', ha2⟩, hw2⟩ := h2
    dsimp only at ha1 ha2 hw1 hw2
    rw [ha1, hw1] at h1'
    rw [ha2, hw2] at h2'
    have hadj := c7_adj_add_one i
    have hne : (i, w) ≠ (i + 1, w) := fun h => hadj.ne (congrArg Prod.fst h)
    exact hS h1' h2' hne ⟨hne, Or.inr hadj, Or.inl rfl⟩
  indep := fun i => by
    intro u hu v hv huv hH
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hu hv
    have hu' : ∃ a : ZMod 7, (a = i ∨ a = i + 1) ∧ (a, u) ∈ S := by
      rcases hu with ⟨⟨a, u1⟩, ⟨h, ha⟩, hu1⟩ | ⟨⟨a, u1⟩, ⟨h, ha⟩, hu1⟩
      · dsimp only at ha hu1; subst hu1; exact ⟨a, Or.inl ha, h⟩
      · dsimp only at ha hu1; subst hu1; exact ⟨a, Or.inr ha, h⟩
    have hv' : ∃ b : ZMod 7, (b = i ∨ b = i + 1) ∧ (b, v) ∈ S := by
      rcases hv with ⟨⟨b, v1⟩, ⟨h, hb⟩, hv1⟩ | ⟨⟨b, v1⟩, ⟨h, hb⟩, hv1⟩
      · dsimp only at hb hv1; subst hv1; exact ⟨b, Or.inl hb, h⟩
      · dsimp only at hb hv1; subst hv1; exact ⟨b, Or.inr hb, h⟩
    rcases hu' with ⟨a, ha, hau⟩; rcases hv' with ⟨b, hb, hbv⟩
    have hab : a = b ∨ C7.Adj a b := by
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
      · exact Or.inl rfl
      · exact Or.inr (c7_adj_add_one i)
      · exact Or.inr (c7_adj_add_one i).symm
      · exact Or.inl rfl
    have hne : (a, u) ≠ (b, v) := fun h => huv (congrArg Prod.snd h)
    exact hS hau hbv hne ⟨hne, hab, Or.inr hH⟩

private lemma CubeSlices.sum_card {S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))}
    (hS : (C7 ⊠ (C7 ⊠ C7)).IsIndepSet (S : Set _)) :
    (∑ i : ZMod 7, ((CubeSlices.ofIndep hS).s i).card) = S.card := by
  have hc : ∀ i : ZMod 7, ((CubeSlices.ofIndep hS).s i).card = (S.filter fun p => p.1 = i).card := by
    intro i
    apply Finset.card_image_of_injOn
    rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 hb
    simp only [Finset.mem_coe, Finset.mem_filter] at h1 h2
    exact Prod.ext (h1.2.trans h2.2.symm) hb
  simp_rw [hc]
  exact (Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := S) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)).symm

private def CubeSlices.shift (cs : CubeSlices) (t : ZMod 7) : CubeSlices where
  s := fun i => cs.s (i + t)
  disj := fun i => by simpa [add_assoc, add_comm t 1] using cs.disj (i + t)
  indep := fun i => by simpa [add_assoc, add_comm t 1] using cs.indep (i + t)

private def CubeSlices.rev (cs : CubeSlices) (c : ZMod 7) : CubeSlices where
  s := fun i => cs.s (c - i)
  disj := fun i => by
    have h := cs.disj (c - i - 1)
    rw [sub_add_cancel] at h
    have heq2 : c - (i + 1) = c - i - 1 := by ring
    rw [heq2]; exact h.symm
  indep := fun i => by
    have h := cs.indep (c - i - 1)
    rw [sub_add_cancel] at h
    have heq2 : c - (i + 1) = c - i - 1 := by ring
    rw [heq2, Finset.union_comm]; exact h

private def CubeSlices.mapAut2 (cs : CubeSlices) (g : Aut2) : CubeSlices where
  s := fun i => (cs.s i).map g.toIso.toEquiv.toEmbedding
  disj := fun i => Finset.disjoint_left.mpr fun x h1 h2 => by
    rcases Finset.mem_map.mp h1 with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp h2 with ⟨b, hb, hab⟩
    exact Finset.disjoint_left.mp (cs.disj i) ha ((g.toIso.injective hab) ▸ hb)
  indep := fun i => by
    rw [← Finset.map_union]
    exact isIndepSet_map_iso' g.toIso (cs.indep i)

private lemma CubeSlices.band_card (cs : CubeSlices) (i : ZMod 7) :
    (cs.s i ∪ cs.s (i + 1)).card = (cs.s i).card + (cs.s (i + 1)).card :=
  Finset.card_union_of_disjoint (cs.disj i)

private lemma CubeSlices.band_card_le (cs : CubeSlices) (i : ZMod 7) :
    (cs.s i).card + (cs.s (i + 1)).card ≤ 10 := by
  rw [← cs.band_card i]; exact alpha_c7_pow2_le_internal (cs.indep i)

private lemma CubeSlices.sdiff_eq_other (cs : CubeSlices) (i : ZMod 7) :
    diff49 (ofFinset49 (cs.s i ∪ cs.s (i + 1))) (ofFinset49 (cs.s i)) =
      ofFinset49 (cs.s (i + 1)) := by
  rw [← ofFinset49_sdiff, Finset.union_sdiff_cancel_left (cs.disj i)]

private lemma CubeSlices.sdiff_eq_first (cs : CubeSlices) (i : ZMod 7) :
    diff49 (ofFinset49 (cs.s i ∪ cs.s (i + 1))) (ofFinset49 (cs.s (i + 1))) =
      ofFinset49 (cs.s i) := by
  rw [← ofFinset49_sdiff, Finset.union_sdiff_cancel_right (cs.disj i)]

private lemma CubeSlices.disj' (cs : CubeSlices) (i j : ZMod 7) (hj : i + 1 = j := by decide) :
    Disjoint (cs.s i) (cs.s j) := hj ▸ cs.disj i
private lemma CubeSlices.indep' (cs : CubeSlices) (i j : ZMod 7) (hj : i + 1 = j := by decide) :
    (C7 ⊠ C7).IsIndepSet ((cs.s i ∪ cs.s j : Finset _) : Set _) := hj ▸ cs.indep i
private lemma CubeSlices.band_card' (cs : CubeSlices) (i j : ZMod 7) (hj : i + 1 = j := by decide) :
    (cs.s i ∪ cs.s j).card = (cs.s i).card + (cs.s j).card := hj ▸ cs.band_card i
private lemma CubeSlices.sdiff_other' (cs : CubeSlices) (i j : ZMod 7) (hj : i + 1 = j := by decide) :
    diff49 (ofFinset49 (cs.s i ∪ cs.s j)) (ofFinset49 (cs.s i)) = ofFinset49 (cs.s j) := hj ▸ cs.sdiff_eq_other i
private lemma CubeSlices.sdiff_first' (cs : CubeSlices) (i j : ZMod 7) (hj : i + 1 = j := by decide) :
    diff49 (ofFinset49 (cs.s i ∪ cs.s j)) (ofFinset49 (cs.s j)) = ofFinset49 (cs.s i) := hj ▸ cs.sdiff_eq_first i

private lemma CubeSlices.disj_of_sub_nbr {cs : CubeSlices} {i : ZMod 7} {M : Nat}
    (hMlt : M < 2 ^ 49) (hM : subset49 M (closedNbr49 (ofFinset49 (cs.s i))) = true) :
    disjoint49 (ofFinset49 (cs.s (i + 1))) M = true ∧
    disjoint49 (ofFinset49 (cs.s (i - 1))) M = true := by
  have hd1 := disjoint49_closedNbr_of_indep (cs.disj i) (cs.indep i)
  have hd2 : disjoint49 (ofFinset49 (cs.s (i - 1))) (closedNbr49 (ofFinset49 (cs.s i))) = true := by
    have h := cs.disj (i - 1); have hi := cs.indep (i - 1)
    rw [sub_add_cancel] at h hi
    rw [Finset.union_comm] at hi
    exact disjoint49_closedNbr_of_indep h.symm hi
  have sub_disj : ∀ {A B C : Nat}, A < 2 ^ 49 → B < 2 ^ 49 →
      disjoint49 A C = true → subset49 B C = true → disjoint49 A B = true := by
    intro A B C hAlt hBlt hAC hBC
    rw [disjoint49_iff hAlt] at hAC ⊢
    rw [subset49_iff hBlt] at hBC
    intro r c ha
    cases hb : get49 B r c
    · rfl
    · exact absurd (hBC r c hb) (by simp [hAC r c ha])
  exact ⟨sub_disj (ofFinset49_lt _) hMlt hd1 hM, sub_disj (ofFinset49_lt _) hMlt hd2 hM⟩

private lemma CubeSlices.subset_not_or {S : Finset (ZMod 7 × ZMod 7)} {A B : Nat}
    (hA : disjoint49 (ofFinset49 S) A = true)
    (hB : disjoint49 (ofFinset49 S) B = true) :
    subset49 (ofFinset49 S) (not49 (A ||| B)) = true := by
  rw [disjoint49_iff (ofFinset49_lt S)] at hA hB
  rw [subset49_iff (ofFinset49_lt S)]
  intro r c hS
  rw [get49_not, get49_or, hA r c hS, hB r c hS]; rfl

private lemma refute_sq_core {cs : CubeSlices} {k : Fin 3} {mL mR : Nat}
    (hB2eq : ofFinset49 (cs.s 2 ∪ cs.s 3) = rep k)
    (hmL : mL = (cs.s 2).card) (hmR : mR = (cs.s 3).card)
    (hmL4 : 4 ≤ mL) (hmL6 : mL ≤ 6) (hmR4 : 4 ≤ mR) (hmR6 : mR ≤ 6)
    (hb0 : (cs.s 0).card + (cs.s 1).card = 10)
    (hb1 : (cs.s 1).card + (cs.s 2).card = 10)
    (hb3 : (cs.s 3).card + (cs.s 4).card = 10)
    (hb4 : (cs.s 4).card + (cs.s 5).card = 10)
    (hs6 : 4 ≤ (cs.s 6).card)
    {cert : SqCert}
    (hchk : checkSqCase k (nearK k mL) (nearK k mR)
      (ofFinset49 (cs.s 2)) cert = true) : False := by
  have hS2rep : subset49 (ofFinset49 (cs.s 2)) (rep k) = true := by
    rw [← hB2eq]; exact ofFinset49_subset_of_subset Finset.subset_union_left
  have hS3eq : diff49 (rep k) (ofFinset49 (cs.s 2)) = ofFinset49 (cs.s 3) := by
    rw [← hB2eq]; exact cs.sdiff_other' 2 3
  have hS3rep : subset49 (ofFinset49 (cs.s 3)) (rep k) = true := by
    rw [← hB2eq]; exact ofFinset49_subset_of_subset Finset.subset_union_right
  have hS2pop : pop49 (ofFinset49 (cs.s 2)) = mL := by rw [pop49_ofFinset, hmL]
  have hS3pop : pop49 (ofFinset49 (cs.s 3)) = mR := by rw [pop49_ofFinset, hmR]
  have hB0card : (cs.s 0 ∪ cs.s 1).card = 10 := by rw [cs.band_card' 0 1, hb0]
  have hB1card : (cs.s 1 ∪ cs.s 2).card = 10 := by rw [cs.band_card' 1 2, hb1]
  have hB3card : (cs.s 3 ∪ cs.s 4).card = 10 := by rw [cs.band_card' 3 4, hb3]
  have hB4card : (cs.s 4 ∪ cs.s 5).card = 10 := by rw [cs.band_card' 4 5, hb4]
  have hS6ind : (C7 ⊠ C7).IsIndepSet ((cs.s 6 : Finset _) : Set _) :=
    (cs.indep 6).mono (Finset.coe_subset.mpr Finset.subset_union_left)
  have hCL_sub : subset49 ((c2Tree k).getAux (repBits k) (ofFinset49 (cs.s 2)))
      (closedNbr49 (ofFinset49 (cs.s 0))) = true := by
    have h := c2Tree_sound (ofFinset49_lt _) hS2rep (by omega) (by omega) (cs.indep' 1 2) hB1card
      (ofFinset49_subset_of_subset Finset.subset_union_right)
      (cs.indep' 0 1) hB0card
      (by rw [cs.sdiff_first' 1 2]; exact ofFinset49_subset_of_subset Finset.subset_union_right)
    rwa [cs.sdiff_first' 1 2, cs.sdiff_first' 0 1] at h
  have hCR_sub : subset49 ((c2Tree k).getAux (repBits k) (ofFinset49 (cs.s 3)))
      (closedNbr49 (ofFinset49 (cs.s 5))) = true := by
    have h := c2Tree_sound (ofFinset49_lt _) hS3rep (by omega) (by omega) (cs.indep' 3 4) hB3card
      (ofFinset49_subset_of_subset Finset.subset_union_left)
      (cs.indep' 4 5) hB4card
      (by rw [cs.sdiff_other' 3 4]; exact ofFinset49_subset_of_subset Finset.subset_union_left)
    rwa [cs.sdiff_other' 3 4, cs.sdiff_other' 4 5] at h
  have hdisj6_0 : ∀ {M : Nat}, M < 2 ^ 49 → subset49 M (closedNbr49 (ofFinset49 (cs.s 0))) = true →
      disjoint49 (ofFinset49 (cs.s 6)) M = true := by
    intro M hMlt hM
    have h := (cs.disj_of_sub_nbr (i := 0) hMlt hM).2
    rwa [show (0 : ZMod 7) - 1 = 6 by decide] at h
  have hdisj6_5 : ∀ {M : Nat}, M < 2 ^ 49 → subset49 M (closedNbr49 (ofFinset49 (cs.s 5))) = true →
      disjoint49 (ofFinset49 (cs.s 6)) M = true := by
    intro M hMlt hM
    have h := (cs.disj_of_sub_nbr (i := 5) hMlt hM).1
    rwa [show (5 : ZMod 7) + 1 = 6 by decide] at h
  unfold checkSqCase at hchk
  simp only [seqN_eq] at hchk
  rw [hS3eq] at hchk
  cases cert with
  | pop3 =>
    dsimp only at hchk
    have hle3 : pop49 (not49 ((c2Tree k).getAux (repBits k) (ofFinset49 (cs.s 2)) |||
        (c2Tree k).getAux (repBits k) (ofFinset49 (cs.s 3)))) ≤ 3 := Nat.ble_eq.mp hchk
    have hsub := CubeSlices.subset_not_or
      (hdisj6_0 (c2Tree_get_lt49 k _) hCL_sub) (hdisj6_5 (c2Tree_get_lt49 k _) hCR_sub)
    have hle := subset49_pop_le (ofFinset49_lt _) hsub
    rw [pop49_ofFinset] at hle
    omega
  | sq3 a b c =>
    dsimp only at hchk
    have hsub := CubeSlices.subset_not_or
      (hdisj6_0 (c2Tree_get_lt49 k _) hCL_sub) (hdisj6_5 (c2Tree_get_lt49 k _) hCR_sub)
    have hav : not49 ((c2Tree k).getAux (repBits k) (ofFinset49 (cs.s 2)) |||
        (c2Tree k).getAux (repBits k) (ofFinset49 (cs.s 3))) < 2 ^ 49 :=
      not49_lt (or_lt49 (c2Tree_get_lt49 k _) (c2Tree_get_lt49 k _))
    have hle := card_le_three_of_sq3_cover hS6ind hsub hchk hav
    omega
  | splitL1 covs =>
    dsimp only at hchk
    obtain ⟨k1, g1, hsr1, hB1eq⟩ := tenSet_canon_half (cs.indep' 1 2) hB1card
    obtain ⟨k4, g4, hsr4, hB4eq⟩ := tenSet_canon_half (cs.indep' 3 4) hB3card
    have hL1mem : (k1, g1, ofFinset49 (cs.s 1 ∪ cs.s 2)) ∈
        (nearK k mL).filter fun t => subset49 (ofFinset49 (cs.s 2)) t.2.2 := by
      rw [hB1eq]
      exact List.mem_filter.mpr ⟨mem_near_of_subset (ofFinset49_lt _) hsr1 hS2rep
        (by rw [← hB1eq]; exact ofFinset49_subset_of_subset Finset.subset_union_right) (by omega),
        by rw [← hB1eq]; exact ofFinset49_subset_of_subset Finset.subset_union_right⟩
    have hR4mem : (k4, g4, ofFinset49 (cs.s 3 ∪ cs.s 4)) ∈
        (nearK k mR).filter fun t => subset49 (ofFinset49 (cs.s 3)) t.2.2 := by
      rw [hB4eq]
      exact List.mem_filter.mpr ⟨mem_near_of_subset (ofFinset49_lt _) hsr4 hS3rep
        (by rw [← hB4eq]; exact ofFinset49_subset_of_subset Finset.subset_union_left) (by omega),
        by rw [← hB4eq]; exact ofFinset49_subset_of_subset Finset.subset_union_left⟩
    have hpair := List.all_eq_true.mp (List.all_eq_true.mp hchk _ hL1mem) _ hR4mem
    let y1Canon := diff49 (rep k1) (g1.inv.applyMask (ofFinset49 (cs.s 2)))
    let y4Canon := diff49 (rep k4) (g4.inv.applyMask (ofFinset49 (cs.s 3)))
    have hy1lt : y1Canon < 2 ^ 49 := diff49_lt (rep_lt k1)
    have hy4lt : y4Canon < 2 ^ 49 := diff49_lt (rep_lt k4)
    have hy1img : g1.applyMask y1Canon = ofFinset49 (cs.s 1) := by
      rw [Aut2.applyMask_diff g1 (rep_lt k1), ← hB1eq,
          Aut2.applyMask_inv_right g1 (ofFinset49_lt _), cs.sdiff_first' 1 2]
    have hy4img : g4.applyMask y4Canon = ofFinset49 (cs.s 4) := by
      rw [Aut2.applyMask_diff g4 (rep_lt k4), ← hB4eq,
          Aut2.applyMask_inv_right g4 (ofFinset49_lt _), cs.sdiff_other' 3 4]
    have hy1rep : subset49 y1Canon (rep k1) = true := by
      rw [subset49_iff hy1lt]; intro r c h; rw [get49_diff] at h; exact (Bool.and_eq_true _ _ |>.mp h).1
    have hy4rep : subset49 y4Canon (rep k4) = true := by
      rw [subset49_iff hy4lt]; intro r c h; rw [get49_diff] at h; exact (Bool.and_eq_true _ _ |>.mp h).1
    have hy1pop : 4 ≤ pop49 y1Canon := by
      have : pop49 y1Canon = (cs.s 1).card := by rw [← pop49_applyMask g1, hy1img, pop49_ofFinset]
      omega
    have hy4pop : 4 ≤ pop49 y4Canon := by
      have : pop49 y4Canon = (cs.s 4).card := by rw [← pop49_applyMask g4, hy4img, pop49_ofFinset]
      omega
    have hc1L : subset49 (g1.applyMask ((c1Tree k1).getAux (repBits k1) y1Canon))
        (closedNbr49 (ofFinset49 (cs.s 0))) = true := by
      have h := c1Tree_equivariant (g := g1) hy1lt hy1rep hy1pop (cs.indep' 0 1) hB0card
        (by rw [hy1img]; exact ofFinset49_subset_of_subset Finset.subset_union_right)
      rwa [hy1img, cs.sdiff_first' 0 1] at h
    have hc1R : subset49 (g4.applyMask ((c1Tree k4).getAux (repBits k4) y4Canon))
        (closedNbr49 (ofFinset49 (cs.s 5))) = true := by
      have h := c1Tree_equivariant (g := g4) hy4lt hy4rep hy4pop (cs.indep' 4 5) hB4card
        (by rw [hy4img]; exact ofFinset49_subset_of_subset Finset.subset_union_left)
      rwa [hy4img, cs.sdiff_other' 4 5] at h
    have hsub := CubeSlices.subset_not_or
      (hdisj6_0 (g1.applyMask_lt (c1Tree_get_lt49 k1 y1Canon)) hc1L)
      (hdisj6_5 (g4.applyMask_lt (c1Tree_get_lt49 k4 y4Canon)) hc1R)
    have hav : not49 (g1.applyMask ((c1Tree k1).getAux (repBits k1) y1Canon) |||
        g4.applyMask ((c1Tree k4).getAux (repBits k4) y4Canon)) < 2 ^ 49 :=
      not49_lt (or_lt49 (g1.applyMask_lt (c1Tree_get_lt49 k1 y1Canon)) (g4.applyMask_lt (c1Tree_get_lt49 k4 y4Canon)))
    simp only [lor_eq, Bool.or_eq_true, Nat.ble_eq, List.any_eq_true] at hpair
    rcases hpair with hpop3 | ⟨⟨a, b, c⟩, _, hcov⟩
    · have hle := subset49_pop_le (ofFinset49_lt _) hsub
      rw [pop49_ofFinset] at hle
      have hpop3' : pop49 (not49 (g1.applyMask ((c1Tree k1).getAux (repBits k1) y1Canon) |||
          g4.applyMask ((c1Tree k4).getAux (repBits k4) y4Canon))) ≤ 3 := hpop3
      omega
    · have hle := card_le_three_of_sq3_cover hS6ind hsub hcov hav
      omega

private lemma refute_P13 {cs : CubeSlices}
    (hs0 : (cs.s 0).card = 5) (hs1 : (cs.s 1).card = 5) (hs2 : (cs.s 2).card = 5)
    (hs3 : (cs.s 3).card = 5) (hs4 : (cs.s 4).card = 5) (hs5 : (cs.s 5).card = 5)
    (hs6 : 4 ≤ (cs.s 6).card) : False := by
  have hB2card : (cs.s 2 ∪ cs.s 3).card = 10 := by rw [cs.band_card' 2 3, hs2, hs3]
  obtain ⟨k, g, hB2eq⟩ := tenSet_in_three_orbits (cs.indep' 2 3) hB2card
  let cs1 := cs.mapAut2 g.inv
  have hB2_1 : ofFinset49 (cs1.s 2 ∪ cs1.s 3) = rep k := by
    change ofFinset49 ((cs.s 2).map _ ∪ (cs.s 3).map _) = rep k
    rw [← Finset.map_union, ← Aut2.applyMask_ofFinset, hB2eq, Aut2.applyMask_inv_left g (rep_lt k)]
  have h03 : get49 (rep k) 0 3 = true := (by decide : ∀ j : Fin 3, get49 (rep j) 0 3 = true) k
  have hcard1 : ∀ i, (cs1.s i).card = (cs.s i).card := fun i => Finset.card_map _
  have hex : ∃ cs2 : CubeSlices,
      ofFinset49 (cs2.s 2 ∪ cs2.s 3) = rep k ∧
      get49 (ofFinset49 (cs2.s 2)) 0 3 = true ∧
      (cs2.s 0).card = 5 ∧ (cs2.s 1).card = 5 ∧ (cs2.s 2).card = 5 ∧
      (cs2.s 3).card = 5 ∧ (cs2.s 4).card = 5 ∧ (cs2.s 5).card = 5 ∧
      4 ≤ (cs2.s 6).card := by
    cases hget : get49 (ofFinset49 (cs1.s 2)) 0 3
    · refine ⟨cs1.rev 5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change ofFinset49 (cs1.s (5 - 2) ∪ cs1.s (5 - 3)) = rep k
        rw [show (5 : ZMod 7) - 2 = 3 by decide, show (5 : ZMod 7) - 3 = 2 by decide, Finset.union_comm]
        exact hB2_1
      · change get49 (ofFinset49 (cs1.s (5 - 2))) 0 3 = true
        rw [show (5 : ZMod 7) - 2 = 3 by decide]
        rw [← hB2_1, ofFinset49_union, get49_or, hget] at h03
        simpa using h03
      · change (cs1.s (5 - 0)).card = 5; rw [show (5 : ZMod 7) - 0 = 5 by decide, hcard1, hs5]
      · change (cs1.s (5 - 1)).card = 5; rw [show (5 : ZMod 7) - 1 = 4 by decide, hcard1, hs4]
      · change (cs1.s (5 - 2)).card = 5; rw [show (5 : ZMod 7) - 2 = 3 by decide, hcard1, hs3]
      · change (cs1.s (5 - 3)).card = 5; rw [show (5 : ZMod 7) - 3 = 2 by decide, hcard1, hs2]
      · change (cs1.s (5 - 4)).card = 5; rw [show (5 : ZMod 7) - 4 = 1 by decide, hcard1, hs1]
      · change (cs1.s (5 - 5)).card = 5; rw [show (5 : ZMod 7) - 5 = 0 by decide, hcard1, hs0]
      · change 4 ≤ (cs1.s (5 - 6)).card; rw [show (5 : ZMod 7) - 6 = 6 by decide, hcard1]; exact hs6
    · exact ⟨cs1, hB2_1, hget, by rw [hcard1, hs0], by rw [hcard1, hs1], by rw [hcard1, hs2],
        by rw [hcard1, hs3], by rw [hcard1, hs4], by rw [hcard1, hs5], by rw [hcard1]; exact hs6⟩
  obtain ⟨cs2, hB2, h03_2, c0, c1, c2, c3, c4, c5, c6⟩ := hex
  have hS2rep : subset49 (ofFinset49 (cs2.s 2)) (rep k) = true := by
    rw [← hB2]; exact ofFinset49_subset_of_subset Finset.subset_union_left
  have hmem : ofFinset49 (cs2.s 2) ∈ halves5 k :=
    mem_halves5 (ofFinset49_lt _) hS2rep (by rw [pop49_ofFinset, c2]) h03_2
  have hcert : ∀ j : Fin 3, ∀ m ∈ halves5 j, ∃ cert, checkSqCase j (near5 j) (near5 j) m cert = true :=
    fin3_cases
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP13_0_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP13_1_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP13_2_ok m hm; ⟨c, h⟩)
  obtain ⟨cert, hchk⟩ := hcert k _ hmem
  exact refute_sq_core hB2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) c6 hchk

private lemma refute_P2 {cs : CubeSlices}
    (hs0 : (cs.s 0).card = 4) (hs1 : (cs.s 1).card = 6) (hs2 : (cs.s 2).card = 4)
    (hs3 : (cs.s 3).card = 6) (hs4 : (cs.s 4).card = 4) (hs5 : (cs.s 5).card = 6)
    (hs6 : (cs.s 6).card = 4) : False := by
  have hB2card : (cs.s 2 ∪ cs.s 3).card = 10 := by rw [cs.band_card' 2 3, hs2, hs3]
  obtain ⟨k, g, hB2eq⟩ := tenSet_in_three_orbits (cs.indep' 2 3) hB2card
  let cs1 := cs.mapAut2 g.inv
  have hB2_1 : ofFinset49 (cs1.s 2 ∪ cs1.s 3) = rep k := by
    change ofFinset49 ((cs.s 2).map _ ∪ (cs.s 3).map _) = rep k
    rw [← Finset.map_union, ← Aut2.applyMask_ofFinset, hB2eq, Aut2.applyMask_inv_left g (rep_lt k)]
  have hcard1 : ∀ i, (cs1.s i).card = (cs.s i).card := fun i => Finset.card_map _
  have hS2rep : subset49 (ofFinset49 (cs1.s 2)) (rep k) = true := by
    rw [← hB2_1]; exact ofFinset49_subset_of_subset Finset.subset_union_left
  have hmem : ofFinset49 (cs1.s 2) ∈ subs4 k :=
    mem_subs4 (ofFinset49_lt _) hS2rep (by rw [pop49_ofFinset, hcard1, hs2])
  have hcert : ∀ j : Fin 3, ∀ m ∈ subs4 j, ∃ cert, checkSqCase j (near4 j) (near6 j) m cert = true :=
    fin3_cases
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP2_0_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP2_1_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP2_2_ok m hm; ⟨c, h⟩)
  obtain ⟨cert, hchk⟩ := hcert k _ hmem
  exact refute_sq_core hB2_1 (by rw [hcard1, hs2]) (by rw [hcard1, hs3])
    (by omega) (by omega) (by omega) (by omega)
    (by rw [hcard1, hcard1, hs0, hs1]) (by rw [hcard1, hcard1, hs1, hs2])
    (by rw [hcard1, hcard1, hs3, hs4]) (by rw [hcard1, hcard1, hs4, hs5])
    (by rw [hcard1, hs6]) hchk

private lemma refute_P4 {cs : CubeSlices}
    (hs0 : (cs.s 0).card = 4) (hs1 : (cs.s 1).card = 6) (hs2 : (cs.s 2).card = 4)
    (hs3 : (cs.s 3).card = 6) (hs4 : (cs.s 4).card = 4) (hs5 : (cs.s 5).card = 5)
    (hs6 : (cs.s 6).card = 5) : False := by
  have hB1card : (cs.s 1 ∪ cs.s 2).card = 10 := by rw [cs.band_card' 1 2, hs1, hs2]
  obtain ⟨k, g, hB1eq⟩ := tenSet_in_three_orbits (cs.indep' 1 2) hB1card
  let cs1 := cs.mapAut2 g.inv
  have hB1_1 : ofFinset49 (cs1.s 1 ∪ cs1.s 2) = rep k := by
    change ofFinset49 ((cs.s 1).map _ ∪ (cs.s 2).map _) = rep k
    rw [← Finset.map_union, ← Aut2.applyMask_ofFinset, hB1eq, Aut2.applyMask_inv_left g (rep_lt k)]
  have hcard1 : ∀ i, (cs1.s i).card = (cs.s i).card := fun i => Finset.card_map _
  have hS2rep : subset49 (ofFinset49 (cs1.s 2)) (rep k) = true := by
    rw [← hB1_1]; exact ofFinset49_subset_of_subset Finset.subset_union_right
  have hS1eq : diff49 (rep k) (ofFinset49 (cs1.s 2)) = ofFinset49 (cs1.s 1) := by
    rw [← hB1_1]; exact cs1.sdiff_first' 1 2
  have hS1rep : subset49 (ofFinset49 (cs1.s 1)) (rep k) = true := by
    rw [← hB1_1]; exact ofFinset49_subset_of_subset Finset.subset_union_left
  have hmem : ofFinset49 (cs1.s 2) ∈ subs4 k :=
    mem_subs4 (ofFinset49_lt _) hS2rep (by rw [pop49_ofFinset, hcard1, hs2])
  have hcert : ∀ j : Fin 3, ∀ m ∈ subs4 j, ∃ cert, checkP4Case j m cert = true :=
    fin3_cases
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP4_0_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP4_1_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP4_2_ok m hm; ⟨c, h⟩)
  obtain ⟨cert, hchk⟩ := hcert k _ hmem
  unfold checkP4Case at hchk; simp only [seqN_eq] at hchk; rw [hS1eq] at hchk
  have hCL : subset49 ((c1Tree k).getAux (repBits k) (ofFinset49 (cs1.s 1)))
      (closedNbr49 (ofFinset49 (cs1.s 0))) = true := by
    have h := c1Tree_sound (ofFinset49_lt _) hS1rep (by rw [pop49_ofFinset, hcard1, hs1]; omega)
      (cs1.indep' 0 1) (by rw [cs1.band_card' 0 1, hcard1, hcard1, hs0, hs1])
      (ofFinset49_subset_of_subset Finset.subset_union_right)
    rwa [cs1.sdiff_first' 0 1] at h
  have hCR : subset49 ((c2Tree k).getAux (repBits k) (ofFinset49 (cs1.s 2)))
      (closedNbr49 (ofFinset49 (cs1.s 4))) = true := by
    have h := c2Tree_sound (ofFinset49_lt _) hS2rep (by rw [pop49_ofFinset, hcard1, hs2])
      (by rw [pop49_ofFinset, hcard1, hs2]; omega)
      (cs1.indep' 2 3) (by rw [cs1.band_card' 2 3, hcard1, hcard1, hs2, hs3])
      (ofFinset49_subset_of_subset Finset.subset_union_left)
      (cs1.indep' 3 4) (by rw [cs1.band_card' 3 4, hcard1, hcard1, hs3, hs4])
      (by rw [cs1.sdiff_other' 2 3]; exact ofFinset49_subset_of_subset Finset.subset_union_left)
    rwa [cs1.sdiff_other' 2 3, cs1.sdiff_other' 3 4] at h
  have hd5 : disjoint49 (ofFinset49 (cs1.s 5))
      (((c1Tree k).getAux (repBits k) (ofFinset49 (cs1.s 1))) &&&
       ((c2Tree k).getAux (repBits k) (ofFinset49 (cs1.s 2)))) = true := by
    have h5 := (cs1.disj_of_sub_nbr (i := 4) (c2Tree_get_lt49 k _) hCR).1
    rw [show (4 : ZMod 7) + 1 = 5 by decide] at h5
    rw [disjoint49_iff (ofFinset49_lt _)] at h5 ⊢
    intro r c hm; rw [get49_and, h5 r c hm, Bool.and_false]
  have hd6 : disjoint49 (ofFinset49 (cs1.s 6))
      (((c1Tree k).getAux (repBits k) (ofFinset49 (cs1.s 1))) &&&
       ((c2Tree k).getAux (repBits k) (ofFinset49 (cs1.s 2)))) = true := by
    have h6 := (cs1.disj_of_sub_nbr (i := 0) (c1Tree_get_lt49 k _) hCL).2
    rw [show (0 : ZMod 7) - 1 = 6 by decide] at h6
    rw [disjoint49_iff (ofFinset49_lt _)] at h6 ⊢
    intro r c hm; rw [get49_and, h6 r c hm, Bool.false_and]
  have hd56 : disjoint49 (ofFinset49 (cs1.s 5 ∪ cs1.s 6))
      (((c1Tree k).getAux (repBits k) (ofFinset49 (cs1.s 1))) &&&
       ((c2Tree k).getAux (repBits k) (ofFinset49 (cs1.s 2)))) = true := by
    rw [ofFinset49_union, disjoint49_iff (or_lt49 (ofFinset49_lt _) (ofFinset49_lt _))]
    rw [disjoint49_iff (ofFinset49_lt _)] at hd5 hd6
    intro r c h; rw [get49_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact hd5 r c h
    · exact hd6 r c h
  have hle := checkFarkas2D_sound hchk (cs1.indep' 5 6) hd56
  rw [cs1.band_card' 5 6, hcard1, hcard1, hs5, hs6] at hle
  omega

private lemma refute_P5 {cs : CubeSlices}
    (hs0 : (cs.s 0).card = 5) (hs1 : (cs.s 1).card = 5) (hs2 : (cs.s 2).card = 5)
    (hs3 : (cs.s 3).card = 5) (hs4 : (cs.s 4).card = 4) (hs5 : (cs.s 5).card = 6)
    (hs6 : (cs.s 6).card = 4) : False := by
  have hB1card : (cs.s 1 ∪ cs.s 2).card = 10 := by rw [cs.band_card' 1 2, hs1, hs2]
  obtain ⟨k, g, hB1eq⟩ := tenSet_in_three_orbits (cs.indep' 1 2) hB1card
  let cs1 := cs.mapAut2 g.inv
  have hB1_1 : ofFinset49 (cs1.s 1 ∪ cs1.s 2) = rep k := by
    change ofFinset49 ((cs.s 1).map _ ∪ (cs.s 2).map _) = rep k
    rw [← Finset.map_union, ← Aut2.applyMask_ofFinset, hB1eq, Aut2.applyMask_inv_left g (rep_lt k)]
  have h03 : get49 (rep k) 0 3 = true := (by decide : ∀ j : Fin 3, get49 (rep j) 0 3 = true) k
  have hcard1 : ∀ i, (cs1.s i).card = (cs.s i).card := fun i => Finset.card_map _
  have hex : ∃ cs2 : CubeSlices,
      ofFinset49 (cs2.s 1 ∪ cs2.s 2) = rep k ∧
      get49 (ofFinset49 (cs2.s 1)) 0 3 = true ∧
      (cs2.s 0).card = 5 ∧ (cs2.s 1).card = 5 ∧ (cs2.s 2).card = 5 ∧
      (cs2.s 3).card = 5 ∧ (cs2.s 4).card = 4 ∧ (cs2.s 5).card = 6 ∧
      (cs2.s 6).card = 4 := by
    cases hget : get49 (ofFinset49 (cs1.s 1)) 0 3
    · refine ⟨cs1.rev 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change ofFinset49 (cs1.s (3 - 1) ∪ cs1.s (3 - 2)) = rep k
        rw [show (3 : ZMod 7) - 1 = 2 by decide, show (3 : ZMod 7) - 2 = 1 by decide, Finset.union_comm]
        exact hB1_1
      · change get49 (ofFinset49 (cs1.s (3 - 1))) 0 3 = true
        rw [show (3 : ZMod 7) - 1 = 2 by decide]
        rw [← hB1_1, ofFinset49_union, get49_or, hget] at h03
        simpa using h03
      · change (cs1.s (3 - 0)).card = 5; rw [show (3 : ZMod 7) - 0 = 3 by decide, hcard1, hs3]
      · change (cs1.s (3 - 1)).card = 5; rw [show (3 : ZMod 7) - 1 = 2 by decide, hcard1, hs2]
      · change (cs1.s (3 - 2)).card = 5; rw [show (3 : ZMod 7) - 2 = 1 by decide, hcard1, hs1]
      · change (cs1.s (3 - 3)).card = 5; rw [show (3 : ZMod 7) - 3 = 0 by decide, hcard1, hs0]
      · change (cs1.s (3 - 4)).card = 4; rw [show (3 : ZMod 7) - 4 = 6 by decide, hcard1, hs6]
      · change (cs1.s (3 - 5)).card = 6; rw [show (3 : ZMod 7) - 5 = 5 by decide, hcard1, hs5]
      · change (cs1.s (3 - 6)).card = 4; rw [show (3 : ZMod 7) - 6 = 4 by decide, hcard1, hs4]
    · exact ⟨cs1, hB1_1, hget, by rw [hcard1, hs0], by rw [hcard1, hs1], by rw [hcard1, hs2],
        by rw [hcard1, hs3], by rw [hcard1, hs4], by rw [hcard1, hs5], by rw [hcard1, hs6]⟩
  obtain ⟨cs2, hB1, h03_2, c0, c1, c2, c3, c4, c5, c6⟩ := hex
  have hS1rep : subset49 (ofFinset49 (cs2.s 1)) (rep k) = true := by
    rw [← hB1]; exact ofFinset49_subset_of_subset Finset.subset_union_left
  have hS2eq : diff49 (rep k) (ofFinset49 (cs2.s 1)) = ofFinset49 (cs2.s 2) := by
    rw [← hB1]; exact cs2.sdiff_other' 1 2
  have hS2rep : subset49 (ofFinset49 (cs2.s 2)) (rep k) = true := by
    rw [← hB1]; exact ofFinset49_subset_of_subset Finset.subset_union_right
  have hmem : ofFinset49 (cs2.s 1) ∈ halves5 k :=
    mem_halves5 (ofFinset49_lt _) hS1rep (by rw [pop49_ofFinset, c1]) h03_2
  have hcert : ∀ j : Fin 3, ∀ m ∈ halves5 j, ∃ cert, checkP5Case j (near5 j) m cert = true :=
    fin3_cases
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP5_0_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP5_1_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP5_2_ok m hm; ⟨c, h⟩)
  obtain ⟨cert, hchk⟩ := hcert k _ hmem
  unfold checkP5Case at hchk; simp only [seqN_eq] at hchk; rw [hS2eq] at hchk
  have hB0card : (cs2.s 0 ∪ cs2.s 1).card = 10 := by rw [cs2.band_card' 0 1, c0, c1]
  have hB2card : (cs2.s 2 ∪ cs2.s 3).card = 10 := by rw [cs2.band_card' 2 3, c2, c3]
  have hCL : subset49 ((c1Tree k).getAux (repBits k) (ofFinset49 (cs2.s 1)))
      (closedNbr49 (ofFinset49 (cs2.s 0))) = true := by
    have h := c1Tree_sound (ofFinset49_lt _) hS1rep (by rw [pop49_ofFinset, c1]; omega)
      (cs2.indep' 0 1) hB0card (ofFinset49_subset_of_subset Finset.subset_union_right)
    rwa [cs2.sdiff_first' 0 1] at h
  have hCR : subset49 ((c1Tree k).getAux (repBits k) (ofFinset49 (cs2.s 2)))
      (closedNbr49 (ofFinset49 (cs2.s 3))) = true := by
    have h := c1Tree_sound (ofFinset49_lt _) hS2rep (by rw [pop49_ofFinset, c2]; omega)
      (cs2.indep' 2 3) hB2card (ofFinset49_subset_of_subset Finset.subset_union_left)
    rwa [cs2.sdiff_other' 2 3] at h
  have hd4_CR : disjoint49 (ofFinset49 (cs2.s 4))
      ((c1Tree k).getAux (repBits k) (ofFinset49 (cs2.s 2))) = true := by
    have h := (cs2.disj_of_sub_nbr (i := 3) (c1Tree_get_lt49 k _) hCR).1
    rwa [show (3 : ZMod 7) + 1 = 4 by decide] at h
  have hd6_CL : disjoint49 (ofFinset49 (cs2.s 6))
      ((c1Tree k).getAux (repBits k) (ofFinset49 (cs2.s 1))) = true := by
    have h := (cs2.disj_of_sub_nbr (i := 0) (c1Tree_get_lt49 k _) hCL).2
    rwa [show (0 : ZMod 7) - 1 = 6 by decide] at h
  have hd4_n3 : disjoint49 (ofFinset49 (cs2.s 4)) (closedNbr49 (ofFinset49 (cs2.s 3))) = true :=
    disjoint49_closedNbr_of_indep (cs2.disj' 3 4) (cs2.indep' 3 4)
  have hd6_n0 : disjoint49 (ofFinset49 (cs2.s 6)) (closedNbr49 (ofFinset49 (cs2.s 0))) = true := by
    have h := cs2.disj' 6 0; have hi := cs2.indep' 6 0
    rw [Finset.union_comm] at hi
    exact disjoint49_closedNbr_of_indep h.symm hi
  cases cert with
  | root f =>
    dsimp only at hchk
    have hle := checkFarkas3D_sound hchk (cs2.disj' 4 5) (cs2.indep' 4 5) (cs2.disj' 5 6) (cs2.indep' 5 6) hd4_CR hd6_CL
    omega
  | splitS0 f0s =>
    dsimp only at hchk
    obtain ⟨k0, g0, hsr0, hB0eq⟩ := tenSet_canon_half (cs2.indep' 0 1) hB0card
    have hL0mem : (k0, g0, ofFinset49 (cs2.s 0 ∪ cs2.s 1)) ∈
        (near5 k).filter fun t => subset49 (ofFinset49 (cs2.s 1)) t.2.2 := by
      rw [hB0eq]
      exact List.mem_filter.mpr ⟨mem_near_of_subset (ofFinset49_lt _) hsr0 hS1rep
        (by rw [← hB0eq]; exact ofFinset49_subset_of_subset Finset.subset_union_right)
        (by rw [pop49_ofFinset, c1]),
        by rw [← hB0eq]; exact ofFinset49_subset_of_subset Finset.subset_union_right⟩
    obtain ⟨c0cert, _, hc0chk⟩ := checkAll_sound hchk _ hL0mem
    dsimp only at hc0chk; rw [cs2.sdiff_first' 0 1] at hc0chk
    cases c0cert with
    | leaf f =>
      have hle := checkFarkas3D_sound hc0chk (cs2.disj' 4 5) (cs2.indep' 4 5) (cs2.disj' 5 6) (cs2.indep' 5 6) hd4_CR hd6_n0
      omega
    | splitS3 f3s =>
      obtain ⟨k3, g3, hsr3, hB3eq⟩ := tenSet_canon_half (cs2.indep' 2 3) hB2card
      have hR3mem : (k3, g3, ofFinset49 (cs2.s 2 ∪ cs2.s 3)) ∈
          (near5 k).filter fun t => subset49 (ofFinset49 (cs2.s 2)) t.2.2 := by
        rw [hB3eq]
        exact List.mem_filter.mpr ⟨mem_near_of_subset (ofFinset49_lt _) hsr3 hS2rep
          (by rw [← hB3eq]; exact ofFinset49_subset_of_subset Finset.subset_union_left)
          (by rw [pop49_ofFinset, c2]),
          by rw [← hB3eq]; exact ofFinset49_subset_of_subset Finset.subset_union_left⟩
      obtain ⟨f3, _, hf3chk⟩ := checkAll_sound hc0chk _ hR3mem
      dsimp only at hf3chk; rw [cs2.sdiff_other' 2 3] at hf3chk
      have hle := checkFarkas3D_sound hf3chk (cs2.disj' 4 5) (cs2.indep' 4 5) (cs2.disj' 5 6) (cs2.indep' 5 6) hd4_n3 hd6_n0
      omega

/-! ## Section 8: Exact 5-Profile Algebraic Reduction & Final Theorems -/

private def isProf34 (a0 a1 a2 a3 a4 a5 a6 : Nat) : Prop :=
  (a0 = 5 ∧ a1 = 5 ∧ a2 = 5 ∧ a3 = 5 ∧ a4 = 5 ∧ a5 = 5 ∧ 4 ≤ a6) ∨
  (a0 = 4 ∧ a1 = 6 ∧ a2 = 4 ∧ a3 = 6 ∧ a4 = 4 ∧ a5 = 6 ∧ a6 = 4) ∨
  (a0 = 4 ∧ a1 = 6 ∧ a2 = 4 ∧ a3 = 6 ∧ a4 = 4 ∧ a5 = 5 ∧ a6 = 5) ∨
  (a0 = 5 ∧ a1 = 5 ∧ a2 = 5 ∧ a3 = 5 ∧ a4 = 4 ∧ a5 = 6 ∧ a6 = 4)

private lemma prof_P13 (a0 a1 a2 a3 a4 a5 a6 : Nat)
    (h0 : a0 + a1 = 10) (h1 : a1 + a2 = 10) (h2 : a2 + a3 = 10) (h3 : a3 + a4 = 10)
    (h4 : a4 + a5 = 10) (h5 : a5 + a6 ≤ 10) (h6 : a6 + a0 ≤ 10)
    (hs : 34 ≤ a0 + a1 + a2 + a3 + a4 + a5 + a6) :
    isProf34 a0 a1 a2 a3 a4 a5 a6 ∨ isProf34 a6 a0 a1 a2 a3 a4 a5 := by
  by_cases ha0 : a0 = 5
  · left; left; omega
  · by_cases ha4 : a0 = 4
    · left; right; left; omega
    · right; right; left; omega

private lemma prof_P2 {a0 a1 a2 a3 a4 a5 a6 : Nat}
    (h0 : a0 + a1 = 10) (h1 : a1 + a2 = 10) (h2 : a2 + a3 = 10) (h3 : a3 + a4 = 10)
    (h4 : a4 + a5 = 10) (h5 : a5 + a6 = 10) (h6 : a6 + a0 = 8) :
    isProf34 a0 a1 a2 a3 a4 a5 a6 := by
  right; left; omega

private lemma prof_P4 {a0 a1 a2 a3 a4 a5 a6 : Nat}
    (h0 : a0 + a1 = 10) (h1 : a1 + a2 = 10) (h2 : a2 + a3 = 10) (h3 : a3 + a4 = 10)
    (h4 : a4 + a5 = 9)  (h5 : a5 + a6 = 10) (h6 : a6 + a0 = 9) :
    isProf34 a0 a1 a2 a3 a4 a5 a6 := by
  right; right; left; omega

private lemma prof_P5 {a0 a1 a2 a3 a4 a5 a6 : Nat}
    (h0 : a0 + a1 = 10) (h1 : a1 + a2 = 10) (h2 : a2 + a3 = 10) (h3 : a3 + a4 = 9)
    (h4 : a4 + a5 = 10) (h5 : a5 + a6 = 10) (h6 : a6 + a0 = 9) :
    isProf34 a0 a1 a2 a3 a4 a5 a6 := by
  right; right; right; omega

private lemma exists_profile_arith (s0 s1 s2 s3 s4 s5 s6 : Nat)
    (hsum : 34 ≤ s0 + s1 + s2 + s3 + s4 + s5 + s6)
    (b0 : s0 + s1 ≤ 10) (b1 : s1 + s2 ≤ 10) (b2 : s2 + s3 ≤ 10) (b3 : s3 + s4 ≤ 10)
    (b4 : s4 + s5 ≤ 10) (b5 : s5 + s6 ≤ 10) (b6 : s6 + s0 ≤ 10) :
    isProf34 s0 s1 s2 s3 s4 s5 s6 ∨ isProf34 s1 s2 s3 s4 s5 s6 s0 ∨
    isProf34 s2 s3 s4 s5 s6 s0 s1 ∨ isProf34 s3 s4 s5 s6 s0 s1 s2 ∨
    isProf34 s4 s5 s6 s0 s1 s2 s3 ∨ isProf34 s5 s6 s0 s1 s2 s3 s4 ∨
    isProf34 s6 s0 s1 s2 s3 s4 s5 := by
  let d0 := 10 - (s0 + s1); let d1 := 10 - (s1 + s2); let d2 := 10 - (s2 + s3)
  let d3 := 10 - (s3 + s4); let d4 := 10 - (s4 + s5); let d5 := 10 - (s5 + s6)
  let d6 := 10 - (s6 + s0)
  have hdef : d0 + d1 + d2 + d3 + d4 + d5 + d6 ≤ 2 := by omega
  by_cases h0 : d0 = 0
  · by_cases h1 : d1 = 0
    · by_cases h2 : d2 = 0
      · by_cases h3 : d3 = 0
        · by_cases h4 : d4 = 0
          · rcases prof_P13 s0 s1 s2 s3 s4 s5 s6 (by omega) (by omega) (by omega) (by omega) (by omega) b5 b6 hsum with hp | hp
            · exact Or.inl hp
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp)))))
          · by_cases h5 : d5 = 0
            · by_cases h6 : d6 = 0
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prof_P2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))))
              · exact Or.inl (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
            · rcases prof_P13 s6 s0 s1 s2 s3 s4 s5 (by omega) (by omega) (by omega) (by omega) (by omega) b4 b5 (by omega) with hp | hp
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp)))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))
        · by_cases h4 : d4 = 0
          · by_cases h5 : d5 = 0
            · by_cases h6 : d6 = 0
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prof_P2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))))
              · exact Or.inl (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))))
          · rcases prof_P13 s5 s6 s0 s1 s2 s3 s4 (by omega) (by omega) (by omega) (by omega) (by omega) b3 b4 (by omega) with hp | hp
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))
      · by_cases h3 : d3 = 0
        · by_cases h4 : d4 = 0
          · by_cases h5 : d5 = 0
            · by_cases h6 : d6 = 0
              · exact Or.inr (Or.inr (Or.inr (Or.inl (prof_P2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))))
        · rcases prof_P13 s4 s5 s6 s0 s1 s2 s3 (by omega) (by omega) (by omega) (by omega) (by omega) b2 b3 (by omega) with hp | hp
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
    · by_cases h2 : d2 = 0
      · by_cases h3 : d3 = 0
        · by_cases h4 : d4 = 0
          · by_cases h5 : d5 = 0
            · by_cases h6 : d6 = 0
              · exact Or.inr (Or.inr (Or.inl (prof_P2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))
              · exact Or.inr (Or.inr (Or.inl (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))
            · exact Or.inr (Or.inr (Or.inl (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))))
      · rcases prof_P13 s3 s4 s5 s6 s0 s1 s2 (by omega) (by omega) (by omega) (by omega) (by omega) b1 b2 (by omega) with hp | hp
        · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
        · exact Or.inr (Or.inr (Or.inl hp))
  · by_cases h1 : d1 = 0
    · by_cases h2 : d2 = 0
      · by_cases h3 : d3 = 0
        · by_cases h4 : d4 = 0
          · by_cases h5 : d5 = 0
            · by_cases h6 : d6 = 0
              · exact Or.inr (Or.inl (prof_P2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
              · rcases prof_P13 s1 s2 s3 s4 s5 s6 s0 (by omega) (by omega) (by omega) (by omega) (by omega) b6 b0 (by omega) with hp | hp
                · exact Or.inr (Or.inl hp)
                · exact Or.inl hp
            · exact Or.inr (Or.inl (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
          · exact Or.inr (Or.inl (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))
    · rcases prof_P13 s2 s3 s4 s5 s6 s0 s1 (by omega) (by omega) (by omega) (by omega) (by omega) b0 b1 (by omega) with hp | hp
      · exact Or.inr (Or.inr (Or.inl hp))
      · exact Or.inr (Or.inl hp)

private lemma refute_cubeSlices_prof {cs : CubeSlices}
    (hp : isProf34 (cs.s 0).card (cs.s 1).card (cs.s 2).card (cs.s 3).card
      (cs.s 4).card (cs.s 5).card (cs.s 6).card) : False := by
  rcases hp with ⟨h0, h1, h2, h3, h4, h5, h6⟩ | ⟨h0, h1, h2, h3, h4, h5, h6⟩ |
                 ⟨h0, h1, h2, h3, h4, h5, h6⟩ | ⟨h0, h1, h2, h3, h4, h5, h6⟩
  · exact refute_P13 h0 h1 h2 h3 h4 h5 h6
  · exact refute_P2 h0 h1 h2 h3 h4 h5 h6
  · exact refute_P4 h0 h1 h2 h3 h4 h5 h6
  · exact refute_P5 h0 h1 h2 h3 h4 h5 h6

private lemma no_indep_34_cube {S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))}
    (hS : (C7 ⊠ (C7 ⊠ C7)).IsIndepSet (S : Set _)) (hcard : 34 ≤ S.card) : False := by
  let cs := CubeSlices.ofIndep hS
  have hsum : (cs.s 0).card + (cs.s 1).card + (cs.s 2).card + (cs.s 3).card +
      (cs.s 4).card + (cs.s 5).card + (cs.s 6).card = S.card := by
    have h := CubeSlices.sum_card hS
    let e : Fin 7 ≃ ZMod 7 := Equiv.mk toZ7 ofZ7 ofZ7_toZ7 toZ7_ofZ7
    have h' : (∑ i : Fin 7, (cs.s (e i)).card) = ∑ i : ZMod 7, (cs.s i).card :=
      Equiv.sum_comp e (fun i => (cs.s i).card)
    rw [← h', Fin.sum_univ_seven] at h
    exact h
  have hprof := exists_profile_arith (cs.s 0).card (cs.s 1).card (cs.s 2).card (cs.s 3).card
    (cs.s 4).card (cs.s 5).card (cs.s 6).card (by omega)
    (cs.band_card_le 0) (cs.band_card_le 1) (cs.band_card_le 2) (cs.band_card_le 3)
    (cs.band_card_le 4) (cs.band_card_le 5) (cs.band_card_le 6)
  rcases hprof with h | h | h | h | h | h | h
  · exact refute_cubeSlices_prof (cs := cs) h
  · exact refute_cubeSlices_prof (cs := cs.shift 1) (by
      change isProf34 (cs.s (0 + 1)).card (cs.s (1 + 1)).card (cs.s (2 + 1)).card (cs.s (3 + 1)).card
        (cs.s (4 + 1)).card (cs.s (5 + 1)).card (cs.s (6 + 1)).card
      have e0 : (0 : ZMod 7) + 1 = 1 := by decide
      have e1 : (1 : ZMod 7) + 1 = 2 := by decide
      have e2 : (2 : ZMod 7) + 1 = 3 := by decide
      have e3 : (3 : ZMod 7) + 1 = 4 := by decide
      have e4 : (4 : ZMod 7) + 1 = 5 := by decide
      have e5 : (5 : ZMod 7) + 1 = 6 := by decide
      have e6 : (6 : ZMod 7) + 1 = 0 := by decide
      rw [e0, e1, e2, e3, e4, e5, e6]; exact h)
  · exact refute_cubeSlices_prof (cs := cs.shift 2) (by
      change isProf34 (cs.s (0 + 2)).card (cs.s (1 + 2)).card (cs.s (2 + 2)).card (cs.s (3 + 2)).card
        (cs.s (4 + 2)).card (cs.s (5 + 2)).card (cs.s (6 + 2)).card
      have e0 : (0 : ZMod 7) + 2 = 2 := by decide
      have e1 : (1 : ZMod 7) + 2 = 3 := by decide
      have e2 : (2 : ZMod 7) + 2 = 4 := by decide
      have e3 : (3 : ZMod 7) + 2 = 5 := by decide
      have e4 : (4 : ZMod 7) + 2 = 6 := by decide
      have e5 : (5 : ZMod 7) + 2 = 0 := by decide
      have e6 : (6 : ZMod 7) + 2 = 1 := by decide
      rw [e0, e1, e2, e3, e4, e5, e6]; exact h)
  · exact refute_cubeSlices_prof (cs := cs.shift 3) (by
      change isProf34 (cs.s (0 + 3)).card (cs.s (1 + 3)).card (cs.s (2 + 3)).card (cs.s (3 + 3)).card
        (cs.s (4 + 3)).card (cs.s (5 + 3)).card (cs.s (6 + 3)).card
      have e0 : (0 : ZMod 7) + 3 = 3 := by decide
      have e1 : (1 : ZMod 7) + 3 = 4 := by decide
      have e2 : (2 : ZMod 7) + 3 = 5 := by decide
      have e3 : (3 : ZMod 7) + 3 = 6 := by decide
      have e4 : (4 : ZMod 7) + 3 = 0 := by decide
      have e5 : (5 : ZMod 7) + 3 = 1 := by decide
      have e6 : (6 : ZMod 7) + 3 = 2 := by decide
      rw [e0, e1, e2, e3, e4, e5, e6]; exact h)
  · exact refute_cubeSlices_prof (cs := cs.shift 4) (by
      change isProf34 (cs.s (0 + 4)).card (cs.s (1 + 4)).card (cs.s (2 + 4)).card (cs.s (3 + 4)).card
        (cs.s (4 + 4)).card (cs.s (5 + 4)).card (cs.s (6 + 4)).card
      have e0 : (0 : ZMod 7) + 4 = 4 := by decide
      have e1 : (1 : ZMod 7) + 4 = 5 := by decide
      have e2 : (2 : ZMod 7) + 4 = 6 := by decide
      have e3 : (3 : ZMod 7) + 4 = 0 := by decide
      have e4 : (4 : ZMod 7) + 4 = 1 := by decide
      have e5 : (5 : ZMod 7) + 4 = 2 := by decide
      have e6 : (6 : ZMod 7) + 4 = 3 := by decide
      rw [e0, e1, e2, e3, e4, e5, e6]; exact h)
  · exact refute_cubeSlices_prof (cs := cs.shift 5) (by
      change isProf34 (cs.s (0 + 5)).card (cs.s (1 + 5)).card (cs.s (2 + 5)).card (cs.s (3 + 5)).card
        (cs.s (4 + 5)).card (cs.s (5 + 5)).card (cs.s (6 + 5)).card
      have e0 : (0 : ZMod 7) + 5 = 5 := by decide
      have e1 : (1 : ZMod 7) + 5 = 6 := by decide
      have e2 : (2 : ZMod 7) + 5 = 0 := by decide
      have e3 : (3 : ZMod 7) + 5 = 1 := by decide
      have e4 : (4 : ZMod 7) + 5 = 2 := by decide
      have e5 : (5 : ZMod 7) + 5 = 3 := by decide
      have e6 : (6 : ZMod 7) + 5 = 4 := by decide
      rw [e0, e1, e2, e3, e4, e5, e6]; exact h)
  · exact refute_cubeSlices_prof (cs := cs.shift 6) (by
      change isProf34 (cs.s (0 + 6)).card (cs.s (1 + 6)).card (cs.s (2 + 6)).card (cs.s (3 + 6)).card
        (cs.s (4 + 6)).card (cs.s (5 + 6)).card (cs.s (6 + 6)).card
      have e0 : (0 : ZMod 7) + 6 = 6 := by decide
      have e1 : (1 : ZMod 7) + 6 = 0 := by decide
      have e2 : (2 : ZMod 7) + 6 = 1 := by decide
      have e3 : (3 : ZMod 7) + 6 = 2 := by decide
      have e4 : (4 : ZMod 7) + 6 = 3 := by decide
      have e5 : (5 : ZMod 7) + 6 = 4 := by decide
      have e6 : (6 : ZMod 7) + 6 = 5 := by decide
      rw [e0, e1, e2, e3, e4, e5, e6]; exact h)

private def tripleToFin3 (p : ZMod 7 × (ZMod 7 × ZMod 7)) : Fin 3 → ZMod 7
  | ⟨0, _⟩ => p.1 | ⟨1, _⟩ => p.2.1 | ⟨2, _⟩ => p.2.2

private def c7CubeIsoPi : (C7 ⊠ (C7 ⊠ C7)) ≃g strongPowPi (SimpleGraph.cycleGraph 7) 3 := by
  have hfin3 : ∀ P : Fin 3 → Prop, (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 :=
    fun P => ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ => fin3_cases h0 h1 h2⟩
  have e1 : (C7 ⊠ (C7 ⊠ C7)) ≃g strongPowPi C7 3 :=
    { toEquiv := Equiv.mk
        tripleToFin3
        (fun f => (f 0, f 1, f 2))
        (fun ⟨_, _, _⟩ => rfl)
        (fun f => by ext i; revert i; exact fin3_cases rfl rfl rfl)
      map_rel_iff' := by
        intro ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩
        simp only [Equiv.coe_fn_mk, strongPowPi_adj, strongProd_adj, hfin3,
          tripleToFin3, ne_eq]
        constructor
        · rintro ⟨hne, h0, h1, h2⟩
          refine ⟨fun h => hne (by cases h; rfl), h0, ?_⟩
          by_cases hbc : (b1, c1) = (b2, c2)
          · exact Or.inl hbc
          · exact Or.inr ⟨hbc, h1, h2⟩
        · rintro ⟨hne, h0, hbc⟩
          refine ⟨fun h => hne ?_, h0, ?_, ?_⟩
          · have e0 : a1 = a2 := congrFun h 0
            have e1 : b1 = b2 := congrFun h 1
            have e2 : c1 = c2 := congrFun h 2
            exact Prod.ext e0 (Prod.ext e1 e2)
          · rcases hbc with hbc | ⟨_, h1, _⟩
            · exact Or.inl (congrArg Prod.fst hbc)
            · exact h1
          · rcases hbc with hbc | ⟨_, _, h2⟩
            · exact Or.inl (congrArg Prod.snd hbc)
            · exact h2 }
  have e2 : strongPowPi C7 3 ≃g strongPowPi (SimpleGraph.cycleGraph 7) 3 :=
    (strongPowEquivPi C7 3).symm.trans ((strongPowCongr c7IsoCycleGraph 3).trans (strongPowEquivPi _ 3))
  exact e1.trans e2

/-- Exact upper bound `α(C₇^⊠3) ≤ 33` proved in the pure Lean 4 kernel. -/
theorem alpha_c7_pow3_le : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum ≤ 33 := by
  rw [← iso_indepNum_eq c7CubeIsoPi]
  obtain ⟨S, hS, hScard⟩ := (C7 ⊠ (C7 ⊠ C7)).exists_isNIndepSet_indepNum
  by_contra hgt
  exact no_indep_34_cube hS (by omega)

/-! ## Section 9: Self-Contained 33-Word Witness (`33 ≤ α(C₇^⊠3)`) -/

private def witness33 (i : Fin 33) : Fin 3 → ZMod 7 :=
  match i.val with
  | 0  => ![0, 1, 1] | 1  => ![0, 4, 2] | 2  => ![0, 4, 4]
  | 3  => ![0, 6, 0] | 4  => ![0, 6, 5] | 5  => ![1, 1, 4]
  | 6  => ![1, 1, 6] | 7  => ![1, 3, 0] | 8  => ![1, 6, 3]
  | 9  => ![2, 1, 2] | 10 => ![2, 3, 3] | 11 => ![2, 3, 5]
  | 12 => ![2, 5, 6] | 13 => ![2, 6, 1] | 14 => ![3, 0, 4]
  | 15 => ![3, 0, 6] | 16 => ![3, 2, 0] | 17 => ![3, 4, 1]
  | 18 => ![3, 5, 4] | 19 => ![4, 0, 2] | 20 => ![4, 2, 5]
  | 21 => ![4, 3, 3] | 22 => ![4, 4, 6] | 23 => ![5, 0, 5]
  | 24 => ![5, 1, 0] | 25 => ![5, 3, 1] | 26 => ![5, 5, 2]
  | 27 => ![5, 5, 4] | 28 => ![5, 6, 0] | 29 => ![6, 0, 3]
  | 30 => ![6, 2, 3] | 31 => ![6, 2, 5] | _  => ![6, 4, 6]

private lemma witness33_inj_and_indep :
    (∀ i j : Fin 33, i ≠ j → witness33 i ≠ witness33 j) ∧
    (∀ i j : Fin 33, i ≠ j → ¬ (strongPowPi C7 3).Adj (witness33 i) (witness33 j)) := by
  decide

private theorem alpha_c7_pow3_ge_cube :
    33 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum := by
  have e2 : strongPowPi C7 3 ≃g strongPowPi (SimpleGraph.cycleGraph 7) 3 :=
    (strongPowEquivPi C7 3).symm.trans ((strongPowCongr c7IsoCycleGraph 3).trans (strongPowEquivPi _ 3))
  rw [← iso_indepNum_eq e2]
  let S : Finset (Fin 3 → ZMod 7) := Finset.univ.image witness33
  have hcard : S.card = 33 := by
    rw [Finset.card_image_of_injective _ (fun i j hij => by
      by_contra hne; exact witness33_inj_and_indep.1 i j hne hij)]
    simp
  have hind : (strongPowPi C7 3).IsIndepSet (S : Set (Fin 3 → ZMod 7)) := by
    intro u hu v hv huv hadj
    simp only [S, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and] at hu hv
    obtain ⟨i, rfl⟩ := hu
    obtain ⟨j, rfl⟩ := hv
    exact witness33_inj_and_indep.2 i j (fun h => huv (congrArg witness33 h)) hadj
  calc 33 = S.card := hcard.symm
    _ ≤ (strongPowPi C7 3).indepNum := hind.card_le_indepNum

/-- Exact independence number `α(C₇^⊠3) = 33` proved in the pure Lean 4 kernel. -/
theorem alpha_c7_pow3 : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum = 33 :=
  le_antisymm alpha_c7_pow3_le alpha_c7_pow3_ge_cube

end

end ShannonC7
