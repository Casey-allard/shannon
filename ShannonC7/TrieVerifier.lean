import ShannonC7.CycleC7

/-!
# Pure-Kernel Radix-7 Trie Verifier (`Trie7`)

This module implements an explicit 7-way radix trie `Trie7 d` representing finite subsets
of `StrongPowV (ZMod 7) d`, together with structurally recursive pure-kernel reflection
checkers and soundness theorems for:
- membership (`mem`, `memBool`, `toFinset`),
- exact cardinality (`card`, `toFinset_card`),
- cross-trie non-adjacency in `strongPow C7 d` (`disjoint`, `disjoint_sound`),
- independent-set verification (`isIndep`, `isIndep_node`, `to_indepSet_of_isIndep`,
  `card_le_indepNum`, `card_le_cycleGraph7_indepNum`),
- subset containment (`isSubset`, `toFinset_subset_of_isSubset`),
- closed-neighborhood membership and exact counting (`inClosedNbr`, `closedNbrCount`,
  `closedNbr_inter_eq_singleton`),
- universal predicate checking and filtered counting (`allWords`, `countIf`,
  `disjointCommonNbr`, `countOutside`) for `ValidTuple` and `PortSystem` verification.

All recursive checkers use explicit 7-child constructors with `.empty` short-circuiting
first and pure structural recursion, enabling fast C++ kernel reduction without
`native_decide` or well-founded recursion overhead.
-/

namespace ShannonC7

/-- Explicit 7-child radix trie representing subsets of `StrongPowV (ZMod 7) d`. -/
inductive Trie7 : ℕ → Type
  | empty {d : ℕ} : Trie7 d
  | leaf : Trie7 0
  | node {d : ℕ} (c0 c1 c2 c3 c4 c5 c6 : Trie7 d) : Trie7 (d + 1)

namespace Trie7

/-! ## Internal `ZMod 7` Case-Split & Summation Helpers -/

private theorem zmod7_cases (P : ZMod 7 → Prop)
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) :
    ∀ i : ZMod 7, P i := by
  intro ⟨n, hn⟩
  match n, hn with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6

private theorem sum_zmod7 (f : ZMod 7 → ℕ) :
    (∑ i : ZMod 7, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  have huniv : (Finset.univ : Finset (ZMod 7)) = {0, 1, 2, 3, 4, 5, 6} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  omega

private theorem c7_close_iff (i a : ZMod 7) :
    (i = a ∨ C7.Adj i a) ↔ i = a - 1 ∨ i = a ∨ i = a + 1 := by
  revert i a
  decide

private theorem sum_zmod7_of_not_close {f : ZMod 7 → ℕ} (a : ZMod 7)
    (hzero : ∀ i : ZMod 7, ¬ (i = a ∨ C7.Adj i a) → f i = 0) :
    (∑ i : ZMod 7, f i) = f (a - 1) + f a + f (a + 1) := by
  rw [sum_zmod7]
  revert a
  refine zmod7_cases _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro hzero
  · have h2 := hzero 2 (by decide)
    have h3 := hzero 3 (by decide)
    have h4 := hzero 4 (by decide)
    have h5 := hzero 5 (by decide)
    change f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 = f 6 + f 0 + f 1
    omega
  · have h3 := hzero 3 (by decide)
    have h4 := hzero 4 (by decide)
    have h5 := hzero 5 (by decide)
    have h6 := hzero 6 (by decide)
    change f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 = f 0 + f 1 + f 2
    omega
  · have h0 := hzero 0 (by decide)
    have h4 := hzero 4 (by decide)
    have h5 := hzero 5 (by decide)
    have h6 := hzero 6 (by decide)
    change f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 = f 1 + f 2 + f 3
    omega
  · have h0 := hzero 0 (by decide)
    have h1 := hzero 1 (by decide)
    have h5 := hzero 5 (by decide)
    have h6 := hzero 6 (by decide)
    change f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 = f 2 + f 3 + f 4
    omega
  · have h0 := hzero 0 (by decide)
    have h1 := hzero 1 (by decide)
    have h2 := hzero 2 (by decide)
    have h6 := hzero 6 (by decide)
    change f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 = f 3 + f 4 + f 5
    omega
  · have h0 := hzero 0 (by decide)
    have h1 := hzero 1 (by decide)
    have h2 := hzero 2 (by decide)
    have h3 := hzero 3 (by decide)
    change f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 = f 4 + f 5 + f 6
    omega
  · have h1 := hzero 1 (by decide)
    have h2 := hzero 2 (by decide)
    have h3 := hzero 3 (by decide)
    have h4 := hzero 4 (by decide)
    change f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 = f 5 + f 6 + f 0
    omega

private theorem zmod7_elim (i : ZMod 7) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
  revert i
  decide

private theorem c7_adj_iff_succ (i j : ZMod 7) :
    C7.Adj i j ↔ j = i + 1 ∨ i = j + 1 := by
  revert i j
  decide

private theorem strongPowV_zero_eq (x y : StrongPowV (ZMod 7) 0) : x = y := by
  cases x; cases y; rfl

private def mkSucc {d : ℕ} (i : ZMod 7) (r : StrongPowV (ZMod 7) d) :
    StrongPowV (ZMod 7) (d + 1) := (i, r)

private theorem eq_or_strongPow_succ_adj {d : ℕ} {x y : StrongPowV (ZMod 7) (d + 1)} :
    (x = y ∨ (strongPow C7 (d + 1)).Adj x y) ↔
      (x.1 = y.1 ∨ C7.Adj x.1 y.1) ∧ (x.2 = y.2 ∨ (strongPow C7 d).Adj x.2 y.2) :=
  eq_or_strongProd_adj (G := C7) (H := strongPow C7 d) (x := x) (y := y)

private theorem eq_or_strongPow_succ_adj_mk {d : ℕ} {i j : ZMod 7}
    {rx ry : StrongPowV (ZMod 7) d} :
    (mkSucc i rx = mkSucc j ry ∨ (strongPow C7 (d + 1)).Adj (mkSucc i rx) (mkSucc j ry)) ↔
      (i = j ∨ C7.Adj i j) ∧ (rx = ry ∨ (strongPow C7 d).Adj rx ry) :=
  eq_or_strongProd_adj (G := C7) (H := strongPow C7 d) (x := (i, rx)) (y := (j, ry))

/-! ## Child Selection, Membership & `toFinset` -/

/-- Select the `i`-th child subtrie of a depth `d + 1` trie (dispatching on `i.val`). -/
def child : {d : ℕ} → Trie7 (d + 1) → ZMod 7 → Trie7 d
  | _, .empty, _ => .empty
  | _, .node c0 c1 c2 c3 c4 c5 c6, i =>
    match i.val with
    | 0 => c0
    | 1 => c1
    | 2 => c2
    | 3 => c3
    | 4 => c4
    | 5 => c5
    | _ => c6

@[simp] theorem child_empty {d : ℕ} (i : ZMod 7) :
    (Trie7.empty : Trie7 (d + 1)).child i = .empty := rfl

@[simp] theorem child_node_zero {d : ℕ} (c0 c1 c2 c3 c4 c5 c6 : Trie7 d) :
    (Trie7.node c0 c1 c2 c3 c4 c5 c6).child 0 = c0 := rfl

@[simp] theorem child_node_one {d : ℕ} (c0 c1 c2 c3 c4 c5 c6 : Trie7 d) :
    (Trie7.node c0 c1 c2 c3 c4 c5 c6).child 1 = c1 := rfl

@[simp] theorem child_node_two {d : ℕ} (c0 c1 c2 c3 c4 c5 c6 : Trie7 d) :
    (Trie7.node c0 c1 c2 c3 c4 c5 c6).child 2 = c2 := rfl

@[simp] theorem child_node_three {d : ℕ} (c0 c1 c2 c3 c4 c5 c6 : Trie7 d) :
    (Trie7.node c0 c1 c2 c3 c4 c5 c6).child 3 = c3 := rfl

@[simp] theorem child_node_four {d : ℕ} (c0 c1 c2 c3 c4 c5 c6 : Trie7 d) :
    (Trie7.node c0 c1 c2 c3 c4 c5 c6).child 4 = c4 := rfl

@[simp] theorem child_node_five {d : ℕ} (c0 c1 c2 c3 c4 c5 c6 : Trie7 d) :
    (Trie7.node c0 c1 c2 c3 c4 c5 c6).child 5 = c5 := rfl

@[simp] theorem child_node_six {d : ℕ} (c0 c1 c2 c3 c4 c5 c6 : Trie7 d) :
    (Trie7.node c0 c1 c2 c3 c4 c5 c6).child 6 = c6 := rfl

/-- Propositional membership of a word in a radix-7 trie. -/
def mem : {d : ℕ} → Trie7 d → StrongPowV (ZMod 7) d → Prop
  | _, .empty, _ => False
  | 0, .leaf, _ => True
  | _ + 1, .node c0 c1 c2 c3 c4 c5 c6, (a, rest) =>
    match a.val with
    | 0 => mem c0 rest
    | 1 => mem c1 rest
    | 2 => mem c2 rest
    | 3 => mem c3 rest
    | 4 => mem c4 rest
    | 5 => mem c5 rest
    | _ => mem c6 rest

/-- Computable Boolean membership of a word in a radix-7 trie. -/
def memBool : {d : ℕ} → Trie7 d → StrongPowV (ZMod 7) d → Bool
  | _, .empty, _ => false
  | 0, .leaf, _ => true
  | _ + 1, .node c0 c1 c2 c3 c4 c5 c6, (a, rest) =>
    match a.val with
    | 0 => memBool c0 rest
    | 1 => memBool c1 rest
    | 2 => memBool c2 rest
    | 3 => memBool c3 rest
    | 4 => memBool c4 rest
    | 5 => memBool c5 rest
    | _ => memBool c6 rest

@[simp] theorem mem_empty {d : ℕ} (x : StrongPowV (ZMod 7) d) :
    (Trie7.empty : Trie7 d).mem x ↔ False := by
  cases d <;> rfl

@[simp] theorem mem_leaf (x : StrongPowV (ZMod 7) 0) :
    Trie7.leaf.mem x ↔ True := Iff.rfl

theorem mem_succ {d : ℕ} (t : Trie7 (d + 1)) (a : ZMod 7) (rest : StrongPowV (ZMod 7) d) :
    t.mem (a, rest) ↔ (t.child a).mem rest := by
  cases t with
  | empty => simp [mem_empty]
  | node c0 c1 c2 c3 c4 c5 c6 =>
    revert a
    exact zmod7_cases _ Iff.rfl Iff.rfl Iff.rfl Iff.rfl Iff.rfl Iff.rfl Iff.rfl

@[simp] theorem memBool_empty {d : ℕ} (x : StrongPowV (ZMod 7) d) :
    (Trie7.empty : Trie7 d).memBool x = false := by
  cases d <;> rfl

@[simp] theorem memBool_leaf (x : StrongPowV (ZMod 7) 0) :
    Trie7.leaf.memBool x = true := rfl

theorem memBool_succ {d : ℕ} (t : Trie7 (d + 1)) (a : ZMod 7) (rest : StrongPowV (ZMod 7) d) :
    t.memBool (a, rest) = (t.child a).memBool rest := by
  cases t with
  | empty => simp [memBool_empty]
  | node c0 c1 c2 c3 c4 c5 c6 =>
    revert a
    exact zmod7_cases _ rfl rfl rfl rfl rfl rfl rfl

theorem memBool_eq_true_iff : {d : ℕ} → (t : Trie7 d) → (x : StrongPowV (ZMod 7) d) →
    (t.memBool x = true ↔ t.mem x)
  | _, .empty, x => by simp [memBool_empty, mem_empty]
  | 0, .leaf, _ => by simp [memBool_leaf, mem_leaf]
  | _ + 1, .node c0 c1 c2 c3 c4 c5 c6, (a, rest) => by
    rw [memBool_succ, mem_succ]
    revert a
    exact zmod7_cases _
      (memBool_eq_true_iff c0 rest) (memBool_eq_true_iff c1 rest)
      (memBool_eq_true_iff c2 rest) (memBool_eq_true_iff c3 rest)
      (memBool_eq_true_iff c4 rest) (memBool_eq_true_iff c5 rest)
      (memBool_eq_true_iff c6 rest)

/-- The `Finset` of words stored in a `Trie7 d`. -/
def toFinset {d : ℕ} (t : Trie7 d) : Finset (StrongPowV (ZMod 7) d) :=
  Finset.univ.filter (fun x => t.memBool x = true)

theorem mem_toFinset {d : ℕ} (t : Trie7 d) (x : StrongPowV (ZMod 7) d) :
    x ∈ t.toFinset ↔ t.mem x := by
  simp only [toFinset, Finset.mem_filter, Finset.mem_univ, true_and, memBool_eq_true_iff]

@[simp] theorem toFinset_empty {d : ℕ} :
    (Trie7.empty : Trie7 d).toFinset = ∅ := by
  ext x
  simp [mem_toFinset]

@[simp] theorem toFinset_leaf :
    Trie7.leaf.toFinset = Finset.univ := by
  ext x
  simp [mem_toFinset]

theorem toFinset_leaf_eq_singleton (x : StrongPowV (ZMod 7) 0) :
    Trie7.leaf.toFinset = {x} := by
  ext y
  simp only [toFinset_leaf, Finset.mem_univ, Finset.mem_singleton, true_iff]
  exact strongPowV_zero_eq y x

@[simp] theorem mem_toFinset_iff_memBool {d : ℕ} {t : Trie7 d} {x : StrongPowV (ZMod 7) d} :
    x ∈ t.toFinset ↔ t.memBool x = true := by
  rw [mem_toFinset, ← memBool_eq_true_iff]

private theorem card_filter_succ {d : ℕ} (t : Trie7 (d + 1))
    (P : StrongPowV (ZMod 7) (d + 1) → Prop) [DecidablePred P] :
    (t.toFinset.filter P).card =
      ∑ i : ZMod 7, ((t.child i).toFinset.filter (fun r => P (mkSucc i r))).card := by
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun p : StrongPowV (ZMod 7) (d + 1) => p.1)
    (s := t.toFinset.filter P) (t := (Finset.univ : Finset (ZMod 7)))
    (fun _ _ => Finset.mem_univ _)
  rw [hfib]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro ⟨a, r⟩ hp
    simp only [Finset.mem_filter, mem_toFinset] at hp ⊢
    rcases hp with ⟨⟨hm, hP⟩, rfl⟩
    exact ⟨(mem_succ t a r).mp hm, hP⟩
  · intro ⟨a₁, r₁⟩ h₁ ⟨a₂, r₂⟩ h₂ hr
    simp only [Finset.mem_filter] at h₁ h₂
    exact Prod.ext (h₁.2.trans h₂.2.symm) hr
  · intro r hr
    simp only [Finset.mem_filter, mem_toFinset] at hr
    refine ⟨mkSucc i r, ?_, rfl⟩
    simp only [Finset.mem_filter, mem_toFinset]
    exact ⟨⟨(mem_succ t i r).mpr hr.1, hr.2⟩, rfl⟩

/-! ## Cardinality -/

/-- Exact leaf count (number of stored words) in a `Trie7 d`. -/
def card : {d : ℕ} → Trie7 d → ℕ
  | _, .empty => 0
  | _, .leaf => 1
  | _, .node c0 c1 c2 c3 c4 c5 c6 =>
    card c0 + card c1 + card c2 + card c3 + card c4 + card c5 + card c6

theorem toFinset_card : {d : ℕ} → (t : Trie7 d) → t.toFinset.card = t.card
  | _, .empty => by simp [card]
  | 0, .leaf => by simp [card, card_strongPowV]
  | _ + 1, .node c0 c1 c2 c3 c4 c5 c6 => by
    have h := card_filter_succ (.node c0 c1 c2 c3 c4 c5 c6) (fun _ => True)
    simp only [Finset.filter_true] at h
    rw [h, sum_zmod7]
    simp only [child_node_zero, child_node_one, child_node_two, child_node_three,
      child_node_four, child_node_five, child_node_six, card,
      toFinset_card c0, toFinset_card c1, toFinset_card c2, toFinset_card c3,
      toFinset_card c4, toFinset_card c5, toFinset_card c6]

/-! ## Cross-Trie Non-Adjacency (`disjoint`) & Independence (`isIndep`) -/

/-- Pure-kernel checker returning `true` iff no word in `t₁` is equal or adjacent in
`strongPow C7 d` to any word in `t₂`. Short-circuits on `.empty` and checks only the
21 cyclic-adjacent child pairs `(i, j)` with `(i - j) ∈ {0, 1, 6}`. -/
def disjoint : {d : ℕ} → Trie7 d → Trie7 d → Bool
  | _, .empty, _ => true
  | _, _, .empty => true
  | _, .leaf, .leaf => false
  | _, .node a0 a1 a2 a3 a4 a5 a6, .node b0 b1 b2 b3 b4 b5 b6 =>
    disjoint a0 b6 && disjoint a0 b0 && disjoint a0 b1 &&
    disjoint a1 b0 && disjoint a1 b1 && disjoint a1 b2 &&
    disjoint a2 b1 && disjoint a2 b2 && disjoint a2 b3 &&
    disjoint a3 b2 && disjoint a3 b3 && disjoint a3 b4 &&
    disjoint a4 b3 && disjoint a4 b4 && disjoint a4 b5 &&
    disjoint a5 b4 && disjoint a5 b5 && disjoint a5 b6 &&
    disjoint a6 b5 && disjoint a6 b6 && disjoint a6 b0

theorem disjoint_symm : {d : ℕ} → {t₁ t₂ : Trie7 d} →
    t₁.disjoint t₂ = true → t₂.disjoint t₁ = true
  | _, .empty, .empty, _ => rfl
  | _, .empty, .leaf, _ => rfl
  | _, .empty, .node _ _ _ _ _ _ _, _ => rfl
  | _, .leaf, .empty, _ => rfl
  | _, .node _ _ _ _ _ _ _, .empty, _ => rfl
  | _, .leaf, .leaf, h => h
  | _, .node a0 a1 a2 a3 a4 a5 a6, .node b0 b1 b2 b3 b4 b5 b6, h => by
    simp only [disjoint, Bool.and_eq_true] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h06, h00⟩, h01⟩, h10⟩, h11⟩, h12⟩, h21⟩, h22⟩,
      h23⟩, h32⟩, h33⟩, h34⟩, h43⟩, h44⟩, h45⟩, h54⟩, h55⟩, h56⟩, h65⟩, h66⟩, h60⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨disjoint_symm h60, disjoint_symm h00⟩, disjoint_symm h10⟩,
      disjoint_symm h01⟩, disjoint_symm h11⟩, disjoint_symm h21⟩, disjoint_symm h12⟩,
      disjoint_symm h22⟩, disjoint_symm h32⟩, disjoint_symm h23⟩, disjoint_symm h33⟩,
      disjoint_symm h43⟩, disjoint_symm h34⟩, disjoint_symm h44⟩, disjoint_symm h54⟩,
      disjoint_symm h45⟩, disjoint_symm h55⟩, disjoint_symm h65⟩, disjoint_symm h56⟩,
      disjoint_symm h66⟩, disjoint_symm h06⟩

private theorem disjoint_child_of_close {d : ℕ}
    {a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Trie7 d}
    (h : (Trie7.node a0 a1 a2 a3 a4 a5 a6).disjoint (Trie7.node b0 b1 b2 b3 b4 b5 b6) = true)
    {i j : ZMod 7} (hij : i = j ∨ C7.Adj i j) :
    ((Trie7.node a0 a1 a2 a3 a4 a5 a6).child i).disjoint
      ((Trie7.node b0 b1 b2 b3 b4 b5 b6).child j) = true := by
  simp only [disjoint, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h06, h00⟩, h01⟩, h10⟩, h11⟩, h12⟩, h21⟩, h22⟩,
    h23⟩, h32⟩, h33⟩, h34⟩, h43⟩, h44⟩, h45⟩, h54⟩, h55⟩, h56⟩, h65⟩, h66⟩, h60⟩
  have hji : j = i ∨ C7.Adj j i := hij.imp Eq.symm SimpleGraph.Adj.symm
  rcases zmod7_elim i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (c7_close_iff j _).mp hji with rfl | rfl | rfl
  · exact h06
  · exact h00
  · exact h01
  · exact h10
  · exact h11
  · exact h12
  · exact h21
  · exact h22
  · exact h23
  · exact h32
  · exact h33
  · exact h34
  · exact h43
  · exact h44
  · exact h45
  · exact h54
  · exact h55
  · exact h56
  · exact h65
  · exact h66
  · exact h60

theorem disjoint_sound : {d : ℕ} → {t₁ t₂ : Trie7 d} →
    t₁.disjoint t₂ = true →
    ∀ x y, t₁.mem x → t₂.mem y → ¬ (x = y ∨ (strongPow C7 d).Adj x y)
  | _, .empty, _, _, x, _, hx, _ => fun _ => (mem_empty x).mp hx
  | _, _, .empty, _, _, y, _, hy => fun _ => (mem_empty y).mp hy
  | 0, .leaf, .leaf, h, _, _, _, _ => fun _ => Bool.noConfusion h
  | d + 1, .node a0 a1 a2 a3 a4 a5 a6, .node b0 b1 b2 b3 b4 b5 b6, h, (i, rx), (j, ry),
      hx, hy => by
    intro hxy
    have hxy' : (i = j ∨ C7.Adj i j) ∧ (rx = ry ∨ (strongPow C7 d).Adj rx ry) :=
      eq_or_strongPow_succ_adj_mk.mp hxy
    exact disjoint_sound (d := d) (disjoint_child_of_close h hxy'.1) rx ry
      ((mem_succ (.node a0 a1 a2 a3 a4 a5 a6) i rx).mp hx)
      ((mem_succ (.node b0 b1 b2 b3 b4 b5 b6) j ry).mp hy) hxy'.2

/-- Pure-kernel independent-set checker for `strongPow C7 d`: checks all 7 children
recursively and all 7 cyclic-adjacent pairs `(c0,c1), ..., (c6,c0)`. -/
def isIndep : {d : ℕ} → Trie7 d → Bool
  | _, .empty => true
  | _, .leaf => true
  | _, .node c0 c1 c2 c3 c4 c5 c6 =>
    isIndep c0 && isIndep c1 && isIndep c2 && isIndep c3 &&
    isIndep c4 && isIndep c5 && isIndep c6 &&
    disjoint c0 c1 && disjoint c1 c2 && disjoint c2 c3 &&
    disjoint c3 c4 && disjoint c4 c5 && disjoint c5 c6 &&
    disjoint c6 c0

/-- Modular slice-by-slice constructor lemma for proving `(Trie7.node c0..c6).isIndep = true`
from 7 slice `isIndep` proofs and 7 cyclic-adjacent `disjoint` proofs. -/
theorem isIndep_node {d : ℕ} {c0 c1 c2 c3 c4 c5 c6 : Trie7 d}
    (hi0 : c0.isIndep = true) (hi1 : c1.isIndep = true) (hi2 : c2.isIndep = true)
    (hi3 : c3.isIndep = true) (hi4 : c4.isIndep = true) (hi5 : c5.isIndep = true)
    (hi6 : c6.isIndep = true)
    (hd01 : c0.disjoint c1 = true) (hd12 : c1.disjoint c2 = true)
    (hd23 : c2.disjoint c3 = true) (hd34 : c3.disjoint c4 = true)
    (hd45 : c4.disjoint c5 = true) (hd56 : c5.disjoint c6 = true)
    (hd60 : c6.disjoint c0 = true) :
    (Trie7.node c0 c1 c2 c3 c4 c5 c6).isIndep = true := by
  simp [isIndep, hi0, hi1, hi2, hi3, hi4, hi5, hi6,
    hd01, hd12, hd23, hd34, hd45, hd56, hd60]

private theorem isIndep_child {d : ℕ} {c0 c1 c2 c3 c4 c5 c6 : Trie7 d}
    (h : (Trie7.node c0 c1 c2 c3 c4 c5 c6).isIndep = true) (i : ZMod 7) :
    ((Trie7.node c0 c1 c2 c3 c4 c5 c6).child i).isIndep = true := by
  simp only [isIndep, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hi0, hi1⟩, hi2⟩, hi3⟩, hi4⟩, hi5⟩, hi6⟩,
    _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
  rcases zmod7_elim i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

private theorem isIndep_disjoint_succ {d : ℕ} {c0 c1 c2 c3 c4 c5 c6 : Trie7 d}
    (h : (Trie7.node c0 c1 c2 c3 c4 c5 c6).isIndep = true) (i : ZMod 7) :
    ((Trie7.node c0 c1 c2 c3 c4 c5 c6).child i).disjoint
      ((Trie7.node c0 c1 c2 c3 c4 c5 c6).child (i + 1)) = true := by
  simp only [isIndep, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩,
    hd01⟩, hd12⟩, hd23⟩, hd34⟩, hd45⟩, hd56⟩, hd60⟩
  rcases zmod7_elim i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

private theorem isIndep_sound : {d : ℕ} → {t : Trie7 d} →
    t.isIndep = true →
    ∀ x y, t.mem x → t.mem y → x ≠ y → ¬ (strongPow C7 d).Adj x y
  | _, .empty, _, x, _, hx, _, _ => fun _ => (mem_empty x).mp hx
  | 0, .leaf, _, x, y, _, _, hne => fun _ => hne (strongPowV_zero_eq x y)
  | d + 1, .node c0 c1 c2 c3 c4 c5 c6, h, (i, rx), (j, ry), hx, hy, hne => by
    intro hadj
    have hclose : (i = j ∨ C7.Adj i j) ∧ (rx = ry ∨ (strongPow C7 d).Adj rx ry) :=
      eq_or_strongPow_succ_adj_mk.mp (Or.inr hadj)
    rcases hclose with ⟨hij, hr⟩
    have hx' := (mem_succ (.node c0 c1 c2 c3 c4 c5 c6) i rx).mp hx
    have hy' := (mem_succ (.node c0 c1 c2 c3 c4 c5 c6) j ry).mp hy
    rcases hij with rfl | hC7
    · have hrne : rx ≠ ry := fun heq => hne (Prod.ext rfl heq)
      exact isIndep_sound (d := d) (isIndep_child h i) rx ry hx' hy' hrne (hr.resolve_left hrne)
    · rcases (c7_adj_iff_succ i j).mp hC7 with rfl | rfl
      · exact disjoint_sound (isIndep_disjoint_succ h i) rx ry hx' hy' hr
      · exact disjoint_sound (isIndep_disjoint_succ h j) ry rx hy' hx'
          (hr.imp Eq.symm SimpleGraph.Adj.symm)

/-- Pure-kernel soundness of `Trie7.isIndep`: every certified trie defines a genuine
independent set in `strongPow C7 d`. -/
theorem to_indepSet_of_isIndep {d : ℕ} {t : Trie7 d} (h : t.isIndep = true) :
    (strongPow C7 d).IsIndepSet (t.toFinset : Set (StrongPowV (ZMod 7) d)) := by
  intro x hx y hy hxy
  exact isIndep_sound h x y
    ((mem_toFinset t x).mp (Finset.mem_coe.mp hx))
    ((mem_toFinset t y).mp (Finset.mem_coe.mp hy)) hxy

/-- Pure-kernel lower bound `t.card ≤ (strongPow C7 d).indepNum`. -/
theorem card_le_indepNum {d : ℕ} {t : Trie7 d} (h : t.isIndep = true) :
    t.card ≤ (strongPow C7 d).indepNum := by
  rw [← toFinset_card t]
  exact (to_indepSet_of_isIndep h).card_le_indepNum

/-- Pure-kernel lower bound directly on Mathlib's `strongPowPi (SimpleGraph.cycleGraph 7) d`. -/
theorem card_le_cycleGraph7_indepNum {d : ℕ} {t : Trie7 d} (h : t.isIndep = true) :
    t.card ≤ (strongPowPi (SimpleGraph.cycleGraph 7) d).indepNum := by
  rw [← strongPow_indepNum_eq_pi, ← iso_indepNum_eq (strongPowCongr c7IsoCycleGraph d)]
  exact card_le_indepNum h

/-! ## Subset Containment, Closed Neighborhoods & `ValidTuple` / `PortSystem` Primitives -/

/-- Pure-kernel subset checker on `Trie7 d`. Handles non-canonical empty subtrees cleanly. -/
def isSubset : {d : ℕ} → Trie7 d → Trie7 d → Bool
  | _, .empty, _ => true
  | _, .leaf, .leaf => true
  | _, .leaf, .empty => false
  | _, .node a0 a1 a2 a3 a4 a5 a6, .empty =>
    isSubset a0 .empty && isSubset a1 .empty && isSubset a2 .empty &&
    isSubset a3 .empty && isSubset a4 .empty && isSubset a5 .empty &&
    isSubset a6 .empty
  | _, .node a0 a1 a2 a3 a4 a5 a6, .node b0 b1 b2 b3 b4 b5 b6 =>
    isSubset a0 b0 && isSubset a1 b1 && isSubset a2 b2 &&
    isSubset a3 b3 && isSubset a4 b4 && isSubset a5 b5 &&
    isSubset a6 b6

private theorem isSubset_sound : {d : ℕ} → {s t : Trie7 d} →
    s.isSubset t = true → ∀ x, s.mem x → t.mem x
  | _, .empty, _, _, x, hx => False.elim ((mem_empty x).mp hx)
  | 0, .leaf, .leaf, _, _, _ => trivial
  | 0, .leaf, .empty, h, _, _ => Bool.noConfusion h
  | d + 1, .node a0 a1 a2 a3 a4 a5 a6, .empty, h, (i, r), hx => by
    simp only [isSubset, Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    have hx' := (mem_succ (.node a0 a1 a2 a3 a4 a5 a6) i r).mp hx
    have hbot : (Trie7.empty : Trie7 d).mem r := by
      rcases zmod7_elim i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact isSubset_sound h0 r hx'
      · exact isSubset_sound h1 r hx'
      · exact isSubset_sound h2 r hx'
      · exact isSubset_sound h3 r hx'
      · exact isSubset_sound h4 r hx'
      · exact isSubset_sound h5 r hx'
      · exact isSubset_sound h6 r hx'
    exact False.elim ((mem_empty r).mp hbot)
  | _ + 1, .node a0 a1 a2 a3 a4 a5 a6, .node b0 b1 b2 b3 b4 b5 b6, h, (i, r), hx => by
    simp only [isSubset, Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    have hx' := (mem_succ (.node a0 a1 a2 a3 a4 a5 a6) i r).mp hx
    rw [mem_succ]
    rcases zmod7_elim i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isSubset_sound h0 r hx'
    · exact isSubset_sound h1 r hx'
    · exact isSubset_sound h2 r hx'
    · exact isSubset_sound h3 r hx'
    · exact isSubset_sound h4 r hx'
    · exact isSubset_sound h5 r hx'
    · exact isSubset_sound h6 r hx'

theorem toFinset_subset_of_isSubset {d : ℕ} {s t : Trie7 d} (h : s.isSubset t = true) :
    s.toFinset ⊆ t.toFinset := by
  intro x hx
  exact (mem_toFinset t x).mpr (isSubset_sound h x ((mem_toFinset s x).mp hx))

/-- Fast Boolean check for `x = y ∨ (strongPow C7 d).Adj x y`. -/
def closeBool : {d : ℕ} → StrongPowV (ZMod 7) d → StrongPowV (ZMod 7) d → Bool
  | 0, _, _ => true
  | _ + 1, (a, rx), (b, ry) =>
    let diff := (a.val + 7 - b.val) % 7
    (diff == 0 || diff == 1 || diff == 6) && closeBool rx ry

private theorem zmod7_closeBool_iff (a b : ZMod 7) :
    (let diff := (a.val + 7 - b.val) % 7
     (diff == 0 || diff == 1 || diff == 6) = true) ↔
    (a = b ∨ C7.Adj a b) := by
  revert a b
  decide

theorem closeBool_eq_true_iff : {d : ℕ} → (x y : StrongPowV (ZMod 7) d) →
    (closeBool x y = true ↔ x = y ∨ (strongPow C7 d).Adj x y)
  | 0, x, y => by
    simp [closeBool, strongPowV_zero_eq x y]
  | _ + 1, (a, rx), (b, ry) => by
    rw [closeBool, Bool.and_eq_true, eq_or_strongPow_succ_adj]
    exact and_congr (zmod7_closeBool_iff a b) (closeBool_eq_true_iff rx ry)

/-- Pure-kernel closed-neighborhood membership checker: returns `true` iff some word `x ∈ t`
satisfies `x = w ∨ (strongPow C7 d).Adj x w`, recursing ONLY on the 3 cyclic-adjacent
children `{w - 1, w, w + 1}`. -/
def inClosedNbr : {d : ℕ} → Trie7 d → StrongPowV (ZMod 7) d → Bool
  | _, .empty, _ => false
  | 0, .leaf, _ => true
  | _ + 1, .node c0 c1 c2 c3 c4 c5 c6, (w, rest) =>
    match w.val with
    | 0 => inClosedNbr c6 rest || inClosedNbr c0 rest || inClosedNbr c1 rest
    | 1 => inClosedNbr c0 rest || inClosedNbr c1 rest || inClosedNbr c2 rest
    | 2 => inClosedNbr c1 rest || inClosedNbr c2 rest || inClosedNbr c3 rest
    | 3 => inClosedNbr c2 rest || inClosedNbr c3 rest || inClosedNbr c4 rest
    | 4 => inClosedNbr c3 rest || inClosedNbr c4 rest || inClosedNbr c5 rest
    | 5 => inClosedNbr c4 rest || inClosedNbr c5 rest || inClosedNbr c6 rest
    | _ => inClosedNbr c5 rest || inClosedNbr c6 rest || inClosedNbr c0 rest

private theorem inClosedNbr_succ {d : ℕ} (t : Trie7 (d + 1)) (a : ZMod 7)
    (rw : StrongPowV (ZMod 7) d) :
    t.inClosedNbr (a, rw) =
      ((t.child (a - 1)).inClosedNbr rw || (t.child a).inClosedNbr rw ||
        (t.child (a + 1)).inClosedNbr rw) := by
  cases t with
  | empty => rfl
  | node c0 c1 c2 c3 c4 c5 c6 =>
    revert a
    exact zmod7_cases _ rfl rfl rfl rfl rfl rfl rfl

theorem inClosedNbr_eq_true_iff : {d : ℕ} → (t : Trie7 d) → (w : StrongPowV (ZMod 7) d) →
    (t.inClosedNbr w = true ↔ ∃ x ∈ t.toFinset, x = w ∨ (strongPow C7 d).Adj x w)
  | _, .empty, w => by simp [inClosedNbr]
  | 0, .leaf, w => by
    simp only [inClosedNbr, toFinset_leaf, true_iff]
    exact ⟨w, Finset.mem_univ w, Or.inl rfl⟩
  | _ + 1, .node c0 c1 c2 c3 c4 c5 c6, (a, rw) => by
    rw [inClosedNbr_succ, Bool.or_eq_true, Bool.or_eq_true]
    have ih : ∀ i : ZMod 7,
        ((Trie7.node c0 c1 c2 c3 c4 c5 c6).child i).inClosedNbr rw = true ↔
          ∃ r ∈ ((Trie7.node c0 c1 c2 c3 c4 c5 c6).child i).toFinset,
            r = rw ∨ (strongPow C7 _).Adj r rw :=
      zmod7_cases _
        (inClosedNbr_eq_true_iff c0 rw) (inClosedNbr_eq_true_iff c1 rw)
        (inClosedNbr_eq_true_iff c2 rw) (inClosedNbr_eq_true_iff c3 rw)
        (inClosedNbr_eq_true_iff c4 rw) (inClosedNbr_eq_true_iff c5 rw)
        (inClosedNbr_eq_true_iff c6 rw)
    rw [ih (a - 1), ih a, ih (a + 1)]
    constructor
    · rintro ((⟨r, hr, hclose⟩ | ⟨r, hr, hclose⟩) | ⟨r, hr, hclose⟩)
      · refine ⟨(a - 1, r), (mem_toFinset _ _).mpr ((mem_succ _ _ _).mpr ((mem_toFinset _ _).mp hr)),
          eq_or_strongPow_succ_adj.mpr ⟨(c7_close_iff _ _).mpr (Or.inl rfl), hclose⟩⟩
      · refine ⟨(a, r), (mem_toFinset _ _).mpr ((mem_succ _ _ _).mpr ((mem_toFinset _ _).mp hr)),
          eq_or_strongPow_succ_adj.mpr ⟨Or.inl rfl, hclose⟩⟩
      · refine ⟨(a + 1, r), (mem_toFinset _ _).mpr ((mem_succ _ _ _).mpr ((mem_toFinset _ _).mp hr)),
          eq_or_strongPow_succ_adj.mpr ⟨(c7_close_iff _ _).mpr (Or.inr (Or.inr rfl)), hclose⟩⟩
    · rintro ⟨⟨i, r⟩, hx, hclose⟩
      rw [eq_or_strongPow_succ_adj] at hclose
      have hm : ((Trie7.node c0 c1 c2 c3 c4 c5 c6).child i).mem r :=
        (mem_succ _ i r).mp ((mem_toFinset _ _).mp hx)
      rcases (c7_close_iff i a).mp hclose.1 with rfl | rfl | rfl
      · exact Or.inl (Or.inl ⟨r, (mem_toFinset _ _).mpr hm, hclose.2⟩)
      · exact Or.inl (Or.inr ⟨r, (mem_toFinset _ _).mpr hm, hclose.2⟩)
      · exact Or.inr ⟨r, (mem_toFinset _ _).mpr hm, hclose.2⟩

/-- Exact count of words `x ∈ t` in the closed neighborhood `N[w]` in `strongPow C7 d`,
recursing ONLY on the 3 cyclic-adjacent children `{w - 1, w, w + 1}`. -/
def closedNbrCount : {d : ℕ} → Trie7 d → StrongPowV (ZMod 7) d → ℕ
  | _, .empty, _ => 0
  | 0, .leaf, _ => 1
  | _ + 1, .node c0 c1 c2 c3 c4 c5 c6, (w, rest) =>
    match w.val with
    | 0 => closedNbrCount c6 rest + closedNbrCount c0 rest + closedNbrCount c1 rest
    | 1 => closedNbrCount c0 rest + closedNbrCount c1 rest + closedNbrCount c2 rest
    | 2 => closedNbrCount c1 rest + closedNbrCount c2 rest + closedNbrCount c3 rest
    | 3 => closedNbrCount c2 rest + closedNbrCount c3 rest + closedNbrCount c4 rest
    | 4 => closedNbrCount c3 rest + closedNbrCount c4 rest + closedNbrCount c5 rest
    | 5 => closedNbrCount c4 rest + closedNbrCount c5 rest + closedNbrCount c6 rest
    | _ => closedNbrCount c5 rest + closedNbrCount c6 rest + closedNbrCount c0 rest

private theorem closedNbrCount_succ {d : ℕ} (t : Trie7 (d + 1)) (a : ZMod 7)
    (rw : StrongPowV (ZMod 7) d) :
    t.closedNbrCount (a, rw) =
      (t.child (a - 1)).closedNbrCount rw + (t.child a).closedNbrCount rw +
        (t.child (a + 1)).closedNbrCount rw := by
  cases t with
  | empty => rfl
  | node c0 c1 c2 c3 c4 c5 c6 =>
    revert a
    exact zmod7_cases _ rfl rfl rfl rfl rfl rfl rfl

theorem closedNbrCount_eq : {d : ℕ} → (t : Trie7 d) → (w : StrongPowV (ZMod 7) d) →
    t.closedNbrCount w =
      (t.toFinset.filter (fun x => x = w ∨ (strongPow C7 d).Adj x w)).card
  | _, .empty, w => by simp [closedNbrCount]
  | 0, .leaf, w => by
    simp only [closedNbrCount, toFinset_leaf]
    have h : (Finset.univ : Finset (StrongPowV (ZMod 7) 0)).filter
        (fun x => x = w ∨ (strongPow C7 0).Adj x w) = Finset.univ := by
      ext x
      simp [strongPowV_zero_eq x w]
    simp [h, card_strongPowV]
  | d + 1, .node c0 c1 c2 c3 c4 c5 c6, (a, rw) => by
    let t := Trie7.node c0 c1 c2 c3 c4 c5 c6
    show t.closedNbrCount (mkSucc a rw) =
      (t.toFinset.filter (fun x => x = mkSucc a rw ∨ (strongPow C7 (d + 1)).Adj x (mkSucc a rw))).card
    rw [card_filter_succ t (fun x => x = mkSucc a rw ∨ (strongPow C7 (d + 1)).Adj x (mkSucc a rw))]
    rw [sum_zmod7_of_not_close a]
    · have ih : ∀ i : ZMod 7, (t.child i).closedNbrCount rw =
          ((t.child i).toFinset.filter (fun r => r = rw ∨ (strongPow C7 d).Adj r rw)).card :=
        zmod7_cases _
          (closedNbrCount_eq c0 rw) (closedNbrCount_eq c1 rw)
          (closedNbrCount_eq c2 rw) (closedNbrCount_eq c3 rw)
          (closedNbrCount_eq c4 rw) (closedNbrCount_eq c5 rw)
          (closedNbrCount_eq c6 rw)
      have hterm : ∀ i : ZMod 7, (i = a ∨ C7.Adj i a) →
          ((t.child i).toFinset.filter
            (fun r => mkSucc i r = mkSucc a rw ∨
              (strongPow C7 (d + 1)).Adj (mkSucc i r) (mkSucc a rw))).card =
          (t.child i).closedNbrCount rw := by
        intro i hi
        rw [ih i]
        congr 1
        refine Finset.filter_congr fun r _ => ?_
        rw [eq_or_strongPow_succ_adj_mk]
        exact and_iff_right hi
      rw [show t.closedNbrCount (mkSucc a rw) =
            (t.child (a - 1)).closedNbrCount rw + (t.child a).closedNbrCount rw +
              (t.child (a + 1)).closedNbrCount rw from closedNbrCount_succ t a rw,
        hterm (a - 1) ((c7_close_iff _ _).mpr (Or.inl rfl)),
        hterm a (Or.inl rfl),
        hterm (a + 1) ((c7_close_iff _ _).mpr (Or.inr (Or.inr rfl)))]
    · intro i hnot
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro r _ hclose
      exact hnot (eq_or_strongPow_succ_adj_mk.mp hclose).1

/-- Pure-kernel privacy certificate corollary: if `t.closedNbrCount w = 1`, `s ∈ t`, and
`s ∈ N[w]`, then `N[w] ∩ t = {s}`! Used directly for `ValidTuple` and `PortSystem` privacy. -/
theorem closedNbr_inter_eq_singleton {d : ℕ} {t : Trie7 d} {w s : StrongPowV (ZMod 7) d}
    (hcnt : t.closedNbrCount w = 1)
    (hs_mem : t.memBool s = true)
    (hs_nbr : s = w ∨ (strongPow C7 d).Adj s w) :
    ∀ x ∈ t.toFinset, (x = w ∨ (strongPow C7 d).Adj x w) ↔ x = s := by
  let F := t.toFinset.filter (fun x => x = w ∨ (strongPow C7 d).Adj x w)
  have hFcard : F.card = 1 := by
    rw [← closedNbrCount_eq t w, hcnt]
  have hsF : s ∈ F :=
    Finset.mem_filter.mpr ⟨(mem_toFinset t s).mpr ((memBool_eq_true_iff t s).mp hs_mem), hs_nbr⟩
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hFcard
  have hsy : s = y := Finset.mem_singleton.mp (hy ▸ hsF)
  have hFs : F = {s} := hsy ▸ hy
  intro x hx
  constructor
  · intro hxw
    have hxF : x ∈ F := Finset.mem_filter.mpr ⟨hx, hxw⟩
    exact Finset.mem_singleton.mp (hFs ▸ hxF)
  · rintro rfl
    exact hs_nbr

/-- Universal Boolean predicate checker across every word stored in a `Trie7 d`. -/
def allWords : {d : ℕ} → (StrongPowV (ZMod 7) d → Bool) → Trie7 d → Bool
  | _, _, .empty => true
  | 0, p, .leaf => p PUnit.unit
  | _ + 1, p, .node c0 c1 c2 c3 c4 c5 c6 =>
    allWords (fun r => p (0, r)) c0 &&
    allWords (fun r => p (1, r)) c1 &&
    allWords (fun r => p (2, r)) c2 &&
    allWords (fun r => p (3, r)) c3 &&
    allWords (fun r => p (4, r)) c4 &&
    allWords (fun r => p (5, r)) c5 &&
    allWords (fun r => p (6, r)) c6

theorem allWords_sound : {d : ℕ} → {p : StrongPowV (ZMod 7) d → Bool} → {t : Trie7 d} →
    t.allWords p = true → ∀ x ∈ t.toFinset, p x = true
  | _, _, .empty, _, x, hx => by simp at hx
  | 0, p, .leaf, h, ⟨⟩, _ => h
  | _ + 1, p, .node c0 c1 c2 c3 c4 c5 c6, h, (i, r), hx => by
    simp only [allWords, Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    have hm := (mem_succ (.node c0 c1 c2 c3 c4 c5 c6) i r).mp ((mem_toFinset _ _).mp hx)
    rcases zmod7_elim i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact allWords_sound h0 r ((mem_toFinset c0 r).mpr hm)
    · exact allWords_sound h1 r ((mem_toFinset c1 r).mpr hm)
    · exact allWords_sound h2 r ((mem_toFinset c2 r).mpr hm)
    · exact allWords_sound h3 r ((mem_toFinset c3 r).mpr hm)
    · exact allWords_sound h4 r ((mem_toFinset c4 r).mpr hm)
    · exact allWords_sound h5 r ((mem_toFinset c5 r).mpr hm)
    · exact allWords_sound h6 r ((mem_toFinset c6 r).mpr hm)

/-- Filtered word counter across every word stored in a `Trie7 d`. -/
def countIf : {d : ℕ} → (StrongPowV (ZMod 7) d → Bool) → Trie7 d → ℕ
  | _, _, .empty => 0
  | 0, p, .leaf => if p PUnit.unit then 1 else 0
  | _ + 1, p, .node c0 c1 c2 c3 c4 c5 c6 =>
    countIf (fun r => p (0, r)) c0 +
    countIf (fun r => p (1, r)) c1 +
    countIf (fun r => p (2, r)) c2 +
    countIf (fun r => p (3, r)) c3 +
    countIf (fun r => p (4, r)) c4 +
    countIf (fun r => p (5, r)) c5 +
    countIf (fun r => p (6, r)) c6

theorem countIf_eq : {d : ℕ} → (p : StrongPowV (ZMod 7) d → Bool) → (t : Trie7 d) →
    t.countIf p = (t.toFinset.filter (fun x => p x = true)).card
  | _, _, .empty => by simp [countIf]
  | 0, p, .leaf => by
    simp only [countIf, toFinset_leaf]
    let u : StrongPowV (ZMod 7) 0 := PUnit.unit
    change (if p u = true then 1 else 0) = _
    cases hp : p u with
    | false =>
      have h : (Finset.univ : Finset (StrongPowV (ZMod 7) 0)).filter
          (fun x => p x = true) = ∅ := by
        ext x
        rw [strongPowV_zero_eq x u]
        simp [hp]
      simp [h]
    | true =>
      have h : (Finset.univ : Finset (StrongPowV (ZMod 7) 0)).filter
          (fun x => p x = true) = Finset.univ := by
        ext x
        rw [strongPowV_zero_eq x u]
        simp [hp]
      simp [h, card_strongPowV]
  | _ + 1, p, .node c0 c1 c2 c3 c4 c5 c6 => by
    rw [card_filter_succ (.node c0 c1 c2 c3 c4 c5 c6) (fun x => p x = true), sum_zmod7]
    simp only [child_node_zero, child_node_one, child_node_two, child_node_three,
      child_node_four, child_node_five, child_node_six, countIf, mkSucc,
      countIf_eq (fun r => p (0, r)) c0, countIf_eq (fun r => p (1, r)) c1,
      countIf_eq (fun r => p (2, r)) c2, countIf_eq (fun r => p (3, r)) c3,
      countIf_eq (fun r => p (4, r)) c4, countIf_eq (fun r => p (5, r)) c5,
      countIf_eq (fun r => p (6, r)) c6]

/-- Pure-kernel check that no word `w ∈ x` lies in `N[p0] ∩ N[p1]`. -/
def disjointCommonNbr {d : ℕ} (p0 p1 x : Trie7 d) : Bool :=
  x.allWords (fun w => !(p0.inClosedNbr w && p1.inClosedNbr w))

theorem disjointCommonNbr_sound {d : ℕ} {p0 p1 x : Trie7 d}
    (h : disjointCommonNbr p0 p1 x = true) :
    ∀ w ∈ x.toFinset,
      ¬ ((∃ u ∈ p0.toFinset, u = w ∨ (strongPow C7 d).Adj u w) ∧
         (∃ v ∈ p1.toFinset, v = w ∨ (strongPow C7 d).Adj v w)) := by
  intro w hw ⟨h0, h1⟩
  have hall := allWords_sound h w hw
  have hb0 : p0.inClosedNbr w = true := (inClosedNbr_eq_true_iff p0 w).mpr h0
  have hb1 : p1.inClosedNbr w = true := (inClosedNbr_eq_true_iff p1 w).mpr h1
  simp [hb0, hb1] at hall

/-- Pure-kernel count of words `w ∈ x` outside `N[p0] ∪ N[p1]` (auxiliary core `O`). -/
def countOutside {d : ℕ} (p0 p1 x : Trie7 d) : ℕ :=
  x.countIf (fun w => !p0.inClosedNbr w && !p1.inClosedNbr w)

theorem countOutside_eq {d : ℕ} (p0 p1 x : Trie7 d) :
    countOutside p0 p1 x =
      (x.toFinset.filter (fun w =>
        (¬ ∃ u ∈ p0.toFinset, u = w ∨ (strongPow C7 d).Adj u w) ∧
        (¬ ∃ v ∈ p1.toFinset, v = w ∨ (strongPow C7 d).Adj v w))).card := by
  rw [countOutside, countIf_eq]
  congr 1
  refine Finset.filter_congr fun w _ => ?_
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    inClosedNbr_eq_true_iff]

end Trie7

end ShannonC7
