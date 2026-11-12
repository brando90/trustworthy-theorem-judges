import Mathlib

/-!
# Heap Sort

Formal translation of the Python program `heap_sort`, which sorts a `List[int]` with
the heap sort algorithm: it first builds a *max heap* out of the input
(`build_max_heap` / `heapify`) and then repeatedly extracts the maximum, placing it
at the end of the sorted region.  Inputs that are not lists of integers violate the
pre-condition `pre` and raise `ValueError`.

Modelling choices:

* `Heap` is a binary max-heap: a binary tree whose keys satisfy the heap-order
  property `Heap.Ordered`.  It is the structural counterpart of the array-based heap
  manipulated by the Python code: `Heap.build` is `build_max_heap`, `Heap.insert`
  performs the sift-up of `heapify`, and `Heap.meld` glues the two sub-heaps left
  behind when the root (the maximum) is removed, which is exactly what one
  `heapify(result, i, 0)` step of the extraction loop accomplishes.
* `heapSort` is the functional implementation, `heapSortImp` the imperative one
  (`Id.run do` with mutable state).
* `Pre` is the pre-condition.  The Python check `isinstance(arr, list) and
  all(isinstance(x, int) for x in arr)` is enforced by the Lean type `List Int`, so
  `Pre` holds on the whole declared input domain; the dynamically typed wrapper
  `heapSortDyn` models the `ValueError` branch explicitly.
* `Post_prop` states that the result is a sorted permutation of the input with the
  same length.
-/

namespace heap_sort

/-! ## Implementation (functional) -/

/-- A binary max-heap of integers. -/
inductive Heap where
  | leaf : Heap
  | node : Heap → Int → Heap → Heap

namespace Heap

/-- Number of keys stored in a heap. -/
def size : Heap → Nat
  | leaf => 0
  | node l _ r => size l + size r + 1

@[simp] theorem size_leaf : size leaf = 0 := rfl

@[simp] theorem size_node (l r : Heap) (x : Int) : size (node l x r) = size l + size r + 1 := rfl

/-- The keys of a heap, listed inorder. -/
def elems : Heap → List Int
  | leaf => []
  | node l x r => elems l ++ [x] ++ elems r

@[simp] theorem elems_leaf : elems leaf = [] := rfl

@[simp] theorem elems_node (l r : Heap) (x : Int) :
    elems (node l x r) = elems l ++ [x] ++ elems r := rfl

/-- `Bdd b h` says that every key of `h` is at most `b`. -/
def Bdd (b : Int) (h : Heap) : Prop := ∀ y ∈ elems h, y ≤ b

theorem bdd_leaf (b : Int) : Bdd b leaf := fun _ hy => absurd hy (by simp)

theorem bdd_mono {b c : Int} {h : Heap} (hb : Bdd b h) (hbc : b ≤ c) : Bdd c h :=
  fun y hy => le_trans (hb y hy) hbc

theorem bdd_node {b x : Int} {l r : Heap} :
    Bdd b (node l x r) ↔ (x ≤ b ∧ Bdd b l ∧ Bdd b r) := by
  constructor
  · intro h
    refine ⟨h x (by simp), fun y hy => h y (by simp [hy]), fun y hy => h y (by simp [hy])⟩
  · rintro ⟨hx, hl, hr⟩ y hy
    have h1 : y ∈ elems l ++ [x] ∨ y ∈ elems r := by
      rw [elems_node, List.mem_append] at hy
      exact hy
    rcases h1 with h1 | h1
    · have h2 : y ∈ elems l ∨ y ∈ [x] := by
        rw [List.mem_append] at h1
        exact h1
      rcases h2 with h2 | h2
      · exact hl y h2
      · rw [List.mem_singleton] at h2
        rw [h2]
        exact hx
    · exact hr y h1

/-- The max-heap order property: both sub-heaps are heaps and all of their keys are
bounded by the root key. -/
def Ordered : Heap → Prop
  | leaf => True
  | node l x r => Ordered l ∧ Ordered r ∧ Bdd x l ∧ Bdd x r

theorem ordered_leaf : Ordered leaf := trivial

theorem ordered_node {l r : Heap} {x : Int} :
    Ordered (node l x r) ↔ (Ordered l ∧ Ordered r ∧ Bdd x l ∧ Bdd x r) := Iff.rfl

/-- Insert a key into a heap, restoring the heap-order property.  Iterating `insert`
over the input is `build_max_heap`. -/
def insert : Int → Heap → Heap
  | x, leaf => node leaf x leaf
  | x, node l y r => if x ≤ y then node (insert x l) y r else node (insert y l) x r

theorem insert_leaf (x : Int) : insert x leaf = node leaf x leaf := rfl

theorem insert_node (x y : Int) (l r : Heap) :
    insert x (node l y r) =
      if x ≤ y then node (insert x l) y r else node (insert y l) x r := rfl

theorem size_insert (h : Heap) : ∀ x : Int, size (insert x h) = size h + 1 := by
  induction h with
  | leaf => intro x; simp [insert_leaf, size_node]
  | node l y r ih =>
      intro x
      rw [insert_node]
      by_cases hxy : x ≤ y
      · rw [if_pos hxy]; simp only [size_node, ih x]; omega
      · rw [if_neg hxy]; simp only [size_node, ih y]; omega

theorem coe_elems_insert (h : Heap) : ∀ x : Int,
    (elems (insert x h) : Multiset Int) = {x} + (elems h : Multiset Int) := by
  induction h with
  | leaf =>
      intro x
      show (elems (node leaf x leaf) : Multiset Int) = {x} + (elems leaf : Multiset Int)
      simp [elems_node, elems_leaf, Multiset.coe_nil, Multiset.coe_singleton]
  | node l y r ih =>
      intro x
      rw [insert_node]
      by_cases hxy : x ≤ y
      · rw [if_pos hxy]
        simp only [elems_node, ← Multiset.coe_add, Multiset.coe_singleton]
        rw [ih x]
        abel
      · rw [if_neg hxy]
        simp only [elems_node, ← Multiset.coe_add, Multiset.coe_singleton]
        rw [ih y]
        abel

theorem elems_insert (h : Heap) (x : Int) : List.Perm (elems (insert x h)) (x :: elems h) := by
  rw [← Multiset.coe_eq_coe, coe_elems_insert h x, ← Multiset.cons_coe, ← Multiset.singleton_add]

theorem bdd_insert {b : Int} {h : Heap} (hb : Bdd b h) :
    ∀ x : Int, x ≤ b → Bdd b (insert x h) := by
  intro x hxb y hy
  have hsub := List.Perm.subset (elems_insert h x) hy
  simp only [List.mem_cons] at hsub
  rcases hsub with rfl | hy'
  · exact hxb
  · exact hb y hy'

theorem ordered_insert (h : Heap) : ∀ x : Int, Ordered h → Ordered (insert x h) := by
  induction h with
  | leaf =>
      intro x _
      rw [insert_leaf]
      exact ⟨ordered_leaf, ordered_leaf, bdd_leaf x, bdd_leaf x⟩
  | node l y r ih =>
      intro x ho
      obtain ⟨hol, hor, hbl, hbr⟩ := ho
      rw [insert_node]
      by_cases hxy : x ≤ y
      · rw [if_pos hxy]
        exact ⟨ih x hol, hor, bdd_insert hbl x hxy, hbr⟩
      · rw [if_neg hxy]
        have hyx : y ≤ x := le_of_lt (Int.not_le.mp hxy)
        exact ⟨ih y hol, hor, bdd_insert (bdd_mono hbl hyx) y hyx, bdd_mono hbr hyx⟩

/-- Merge two heaps.  This is the operation performed by `heapify` after the root has
been removed: the two sub-heaps of the removed root are glued back into a heap. -/
def meld : Heap → Heap → Heap
  | leaf, h => h
  | node l x r, leaf => node l x r
  | node l x r, node l' y r' =>
      if x ≤ y then node (meld (node l x r) l') y r'
      else node (meld l (node l' y r')) x r
termination_by a b => size a + size b
decreasing_by all_goals (simp only [size_node]; omega)

@[simp] theorem meld_leaf (h : Heap) : meld leaf h = h := meld.eq_1 h

@[simp] theorem meld_node_leaf (l r : Heap) (x : Int) :
    meld (node l x r) leaf = node l x r := meld.eq_2 l x r

theorem meld_node_node (l r l' r' : Heap) (x y : Int) :
    meld (node l x r) (node l' y r') =
      if x ≤ y then node (meld (node l x r) l') y r'
      else node (meld l (node l' y r')) x r :=
  meld.eq_3 l x r l' y r'

theorem meld_spec (a : Heap) : ∀ b : Heap,
    size (meld a b) = size a + size b ∧
    (elems (meld a b) : Multiset Int) =
      (elems a : Multiset Int) + (elems b : Multiset Int) ∧
    (∀ c : Int, Bdd c a → Bdd c b → Bdd c (meld a b)) ∧
    (Ordered a → Ordered b → Ordered (meld a b)) := by
  induction a with
  | leaf =>
      intro b
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [meld_leaf, size_leaf]
      · simp [meld_leaf, elems_leaf, Multiset.coe_nil]
      · intro c _ hb; rw [meld_leaf]; exact hb
      · intro _ hb; rw [meld_leaf]; exact hb
  | node l x r ih_l ih_r =>
      intro b
      induction b with
      | leaf =>
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp [meld_node_leaf, size_leaf]
          · simp [meld_node_leaf, elems_leaf, Multiset.coe_nil]
          · intro c ha _; rw [meld_node_leaf]; exact ha
          · intro ha _; rw [meld_node_leaf]; exact ha
      | node l' y r' ih_l' ih_r' =>
          rw [meld_node_node]
          by_cases hxy : x ≤ y
          · rw [if_pos hxy]
            obtain ⟨sz, el, bd, od⟩ := ih_l'
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [size_node]; rw [sz]; simp only [size_node]; omega
            · simp only [elems_node, ← Multiset.coe_add, Multiset.coe_singleton]
              rw [el]
              simp only [elems_node, ← Multiset.coe_add, Multiset.coe_singleton]
              abel
            · intro c ha hb
              obtain ⟨hy, hl', hr'⟩ := bdd_node.mp hb
              exact bdd_node.mpr ⟨hy, bd c ha hl', hr'⟩
            · intro ha hb
              have hoa := ha
              obtain ⟨hol', hor', hbl', hbr'⟩ := hb
              obtain ⟨hol, hor, hbl, hbr⟩ := ha
              refine ⟨od hoa hol', hor', ?_, hbr'⟩
              exact bd y (bdd_node.mpr ⟨hxy, bdd_mono hbl hxy, bdd_mono hbr hxy⟩) hbl'
          · rw [if_neg hxy]
            obtain ⟨sz, el, bd, od⟩ := ih_l (node l' y r')
            have hyx : y ≤ x := le_of_lt (Int.not_le.mp hxy)
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [size_node]; rw [sz]; simp only [size_node]; omega
            · simp only [elems_node, ← Multiset.coe_add, Multiset.coe_singleton]
              rw [el]
              simp only [elems_node, ← Multiset.coe_add, Multiset.coe_singleton]
              abel
            · intro c ha hb
              obtain ⟨hx, hl, hr⟩ := bdd_node.mp ha
              exact bdd_node.mpr ⟨hx, bd c hl hb, hr⟩
            · intro ha hb
              have hob := hb
              obtain ⟨hol, hor, hbl, hbr⟩ := ha
              obtain ⟨hol', hor', hbl', hbr'⟩ := hb
              refine ⟨od hol hob, hor, ?_, hbr⟩
              exact bd x hbl (bdd_node.mpr ⟨hyx, bdd_mono hbl' hyx, bdd_mono hbr' hyx⟩)

theorem size_meld (a b : Heap) : size (meld a b) = size a + size b := (meld_spec a b).1

theorem coe_elems_meld (a b : Heap) :
    (elems (meld a b) : Multiset Int) =
      (elems a : Multiset Int) + (elems b : Multiset Int) := (meld_spec a b).2.1

theorem elems_meld (a b : Heap) : List.Perm (elems (meld a b)) (elems a ++ elems b) := by
  rw [← Multiset.coe_eq_coe, coe_elems_meld, ← Multiset.coe_add]

theorem bdd_meld {c : Int} {a b : Heap} (ha : Bdd c a) (hb : Bdd c b) : Bdd c (meld a b) :=
  (meld_spec a b).2.2.1 c ha hb

theorem ordered_meld {a b : Heap} (ha : Ordered a) (hb : Ordered b) : Ordered (meld a b) :=
  (meld_spec a b).2.2.2 ha hb

/-- Strong induction on the size of a heap. -/
theorem size_induction_on {P : Heap → Prop}
    (step : ∀ h : Heap, (∀ h' : Heap, size h' < size h → P h') → P h) : ∀ h : Heap, P h := by
  have key : ∀ n : Nat, ∀ h : Heap, size h = n → P h := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro m ihm h hk
    exact step h (fun h' hh' => ihm (size h') (by rw [← hk]; exact hh') h' rfl)
  intro h
  exact key _ h rfl

theorem coe_cons_add (x : Int) (l : List Int) :
    ((x :: l : List Int) : Multiset Int) = {x} + (l : Multiset Int) := by
  rw [← Multiset.cons_coe, ← Multiset.singleton_add]

/-- The extraction loop: repeatedly remove the root (the maximum, by `Ordered`) and
push it onto the front of the accumulator.  This is the counterpart of the Python
extraction loop `for i in range(n - 1, 0, -1)`: the accumulator plays the role of the
already sorted suffix of the array. -/
def drainGo : Heap → List Int → List Int
  | leaf, acc => acc
  | node l x r, acc => drainGo (meld l r) (x :: acc)
termination_by h _ => size h
decreasing_by all_goals (simp only [size_meld, size_node]; omega)

theorem drainGo_leaf (acc : List Int) : drainGo leaf acc = acc := drainGo.eq_1 acc

theorem drainGo_node (l r : Heap) (x : Int) (acc : List Int) :
    drainGo (node l x r) acc = drainGo (meld l r) (x :: acc) := drainGo.eq_2 acc l x r

theorem coe_drainGo (h : Heap) (acc : List Int) :
    (drainGo h acc : Multiset Int) = (elems h : Multiset Int) + (acc : Multiset Int) := by
  refine size_induction_on (P := fun h => ∀ acc : List Int,
    (drainGo h acc : Multiset Int) = (elems h : Multiset Int) + (acc : Multiset Int)) ?_ h acc
  intro h ih acc
  cases h with
  | leaf => simp [drainGo_leaf, elems_leaf, Multiset.coe_nil]
  | node l x r =>
      have hlt : size (meld l r) < size (node l x r) := by
        simp only [size_meld, size_node]; omega
      rw [drainGo_node, ih (meld l r) hlt (x :: acc), coe_elems_meld]
      simp only [elems_node, ← Multiset.coe_add, Multiset.coe_singleton, coe_cons_add]
      abel

theorem drainGo_sorted : ∀ (h : Heap), ∀ (acc : List Int), Ordered h →
    List.Sorted (· ≤ ·) acc → (∀ z ∈ elems h, ∀ y ∈ acc, z ≤ y) →
    List.Sorted (· ≤ ·) (drainGo h acc) := by
  refine size_induction_on (P := fun h => ∀ (acc : List Int), Ordered h →
    List.Sorted (· ≤ ·) acc → (∀ z ∈ elems h, ∀ y ∈ acc, z ≤ y) →
    List.Sorted (· ≤ ·) (drainGo h acc)) ?_
  intro h ih acc ho ha hba
  cases h with
  | leaf =>
      rw [drainGo_leaf]
      exact ha
  | node l x r =>
      obtain ⟨hol, hor, hbl, hbr⟩ := ho
      have hlt : size (meld l r) < size (node l x r) := by
        simp only [size_meld, size_node]; omega
      rw [drainGo_node]
      refine ih (meld l r) hlt (x :: acc) (ordered_meld hol hor) ?_ ?_
      · exact List.Pairwise.cons (fun y hy => hba x (by simp) y hy) ha
      · intro z hz y hy
        rw [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact bdd_meld hbl hbr z hz
        · have hz2 : z ∈ elems (node l x r) := by
            have hz' := List.Perm.subset (elems_meld l r) hz
            simp only [elems_node, List.mem_append, List.mem_singleton] at hz' ⊢
            tauto
          exact hba z hz2 y hy

theorem drainGo_perm (h : Heap) (acc : List Int) :
    List.Perm (drainGo h acc) (elems h ++ acc) :=
  Multiset.coe_eq_coe.mp (by rw [coe_drainGo h acc, ← Multiset.coe_add])

/-- Build a max-heap from a list of keys by successive insertion: the counterpart of
the Python `build_max_heap`. -/
def build (xs : List Int) : Heap := xs.foldl (fun h x => insert x h) leaf

theorem build_spec (xs : List Int) : ∀ h : Heap, Ordered h →
    Ordered (xs.foldl (fun h x => insert x h) h) ∧
    (elems (xs.foldl (fun h x => insert x h) h) : Multiset Int) =
      (elems h : Multiset Int) + (xs : Multiset Int) := by
  induction xs with
  | nil =>
      intro h ho
      refine ⟨ho, ?_⟩
      simp [Multiset.coe_nil]
  | cons x xs ih =>
      intro h ho
      simp only [List.foldl_cons]
      obtain ⟨ho', he'⟩ := ih (insert x h) (ordered_insert h x ho)
      refine ⟨ho', ?_⟩
      rw [he', coe_elems_insert h x, coe_cons_add]
      abel

theorem ordered_build (xs : List Int) : Ordered (build xs) :=
  (build_spec xs leaf ordered_leaf).1

theorem coe_elems_build (xs : List Int) :
    (elems (build xs) : Multiset Int) = (xs : Multiset Int) := by
  have h := (build_spec xs leaf ordered_leaf).2
  simp only [elems_leaf, Multiset.coe_nil, zero_add] at h
  exact h

theorem elems_build (xs : List Int) : List.Perm (elems (build xs)) xs :=
  Multiset.coe_eq_coe.mp (coe_elems_build xs)

/-- Heap sort: build a max-heap from the input and then repeatedly extract the
maximum.  Each extracted maximum is pushed onto the front of the accumulator, so the
accumulator is kept in increasing order and no final reversal is needed.  This is the
functional counterpart of the Python `heap_sort`. -/
def heapSort (arr : List Int) : List Int := drainGo (build arr) []

theorem heapSort_perm (arr : List Int) : List.Perm (heapSort arr) arr :=
  Multiset.coe_eq_coe.mp (by
    rw [heapSort, coe_drainGo, coe_elems_build, Multiset.coe_nil, add_zero])

theorem heapSort_sorted (arr : List Int) : List.Sorted (· ≤ ·) (heapSort arr) :=
  drainGo_sorted (build arr) [] (ordered_build arr) List.Pairwise.nil (by simp)

theorem heapSort_length (arr : List Int) : (heapSort arr).length = arr.length :=
  List.Perm.length_eq (heapSort_perm arr)

theorem mem_heapSort (y : Int) (arr : List Int) : y ∈ heapSort arr ↔ y ∈ arr :=
  ⟨fun h => List.Perm.subset (heapSort_perm arr) h,
   fun h => List.Perm.subset (heapSort_perm arr).symm h⟩

/-- A sorted permutation of a list of integers is unique; hence `Post_prop` determines
the result of `heapSort` completely. -/
theorem Sorted_Perm_unique {l₁ l₂ : List Int} (h₁ : List.Sorted (· ≤ ·) l₁)
    (h₂ : List.Sorted (· ≤ ·) l₂) (hp : List.Perm l₁ l₂) : l₁ = l₂ := by
  have key : ∀ (l₁ l₂ : List Int), List.Sorted (· ≤ ·) l₁ → List.Sorted (· ≤ ·) l₂ →
      List.Perm l₁ l₂ → l₁ = l₂ := by
    intro l₁
    induction l₁ with
    | nil =>
        intro l₂ _ _ hp
        cases l₂ with
        | nil => rfl
        | cons y t₂ => exact absurd (List.Perm.length_eq hp) (by simp)
    | cons x t₁ ih =>
        intro l₂ h₁ h₂ hp
        cases l₂ with
        | nil => exact absurd (List.Perm.length_eq hp) (by simp)
        | cons y t₂ =>
            have hx : x ≤ y := by
              by_cases h : x = y
              · exact le_of_eq h
              · have hmem : y ∈ (x :: t₁) := List.Perm.subset hp.symm (by simp)
                simp only [List.mem_cons] at hmem
                rcases hmem with rfl | hmem
                · exact absurd rfl h
                · exact (List.pairwise_cons.mp h₁).1 y hmem
            have hy : y ≤ x := by
              by_cases h : y = x
              · exact le_of_eq h
              · have hmem : x ∈ (y :: t₂) := List.Perm.subset hp (by simp)
                simp only [List.mem_cons] at hmem
                rcases hmem with rfl | hmem
                · exact absurd rfl h
                · exact (List.pairwise_cons.mp h₂).1 x hmem
            have hxy : x = y := le_antisymm hx hy
            subst hxy
            rw [ih t₂ (List.pairwise_cons.mp h₁).2 (List.pairwise_cons.mp h₂).2
              ((List.perm_cons x).mp hp)]
  exact key l₁ l₂ h₁ h₂ hp

theorem heapSort_idempotent (arr : List Int) : heapSort (heapSort arr) = heapSort arr :=
  Sorted_Perm_unique (heapSort_sorted (heapSort arr)) (heapSort_sorted arr)
    (heapSort_perm (heapSort arr))

theorem heapSort_nil : heapSort [] = [] :=
  Sorted_Perm_unique (heapSort_sorted []) List.Pairwise.nil (heapSort_perm [])

theorem heapSort_singleton (x : Int) : heapSort [x] = [x] :=
  Sorted_Perm_unique (heapSort_sorted [x])
    (List.pairwise_cons.mpr ⟨by simp, List.Pairwise.nil⟩) (heapSort_perm [x])

end Heap

open Heap

/-! ## Unit tests -/

#eval heapSort [3, 1, 2]
#eval heapSort ([] : List Int)
#eval heapSort [1]
#eval heapSort [5, 2, 4, 6, 1, 3]
#eval heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

example : heapSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSort [] = ([] : List Int) := by native_decide
example : heapSort [1] = [1] := by native_decide
example : heapSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : heapSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSort [2, 1] = [1, 2] := by native_decide
example : heapSort [1, 2] = [1, 2] := by native_decide
example : heapSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : heapSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : heapSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : heapSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : heapSort [-3, 0, -1, 5, -2] = [-3, -2, -1, 0, 5] := by native_decide

/-! ## Pre-condition -/

/-- The Python pre-condition is
`isinstance(arr, list) and all(isinstance(x, int) for x in arr)`.
In Lean both conjuncts are enforced by the input type `List Int` of the declared
domain, so `Pre` holds for every admissible input.  The dynamically typed wrapper
`heapSortDyn` below models the `ValueError` raised when the check fails. -/
def Pre (arr : List Int) : Prop := True

theorem Pre_holds : ∀ arr : List Int, Pre arr := fun _ => trivial

/-- A dynamically typed Python value: either an `int` or something else
(e.g. the `2.5` of the Python negative test). -/
inductive PyVal where
  | int (n : Int)
  | other
  deriving DecidableEq, Repr

def PyVal.toInt : PyVal → Option Int
  | PyVal.int n => some n
  | PyVal.other => none

/-- Executable model of the Python `pre` predicate. -/
def preDyn (arr : List PyVal) : Bool := arr.all fun v => (PyVal.toInt v).isSome

/-- `heap_sort` on dynamically typed input: the `Except.error` branch is the
counterpart of the Python `raise ValueError("Input must be List[int]")`. -/
def heapSortDyn (arr : List PyVal) : Except String (List Int) :=
  if preDyn arr then .ok (heapSort (arr.map fun v => (PyVal.toInt v).getD 0))
  else .error "Input must be List[int]"

theorem preDyn_map_int (ns : List Int) : preDyn (ns.map PyVal.int) = true := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [preDyn, List.map_cons, List.all_cons, PyVal.toInt, Option.isSome_some]
      exact ih

theorem map_toInt_map_int (ns : List Int) :
    (ns.map PyVal.int).map (fun v => (PyVal.toInt v).getD 0) = ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [ih, PyVal.toInt, Option.getD_some]

theorem heapSortDyn_ok (ns : List Int) :
    heapSortDyn (ns.map PyVal.int) = .ok (heapSort ns) := by
  simp only [heapSortDyn, preDyn_map_int ns, ite_true, map_toInt_map_int]

theorem heapSortDyn_err (arr : List PyVal) (h : preDyn arr = false) :
    heapSortDyn arr = .error "Input must be List[int]" := by
  simp [heapSortDyn, h]

#eval heapSortDyn [PyVal.int 3, PyVal.int 1, PyVal.int 2]
#eval heapSortDyn [PyVal.int 1, PyVal.other]

example : heapSortDyn ([3, 1, 2].map PyVal.int) = .ok (heapSort [3, 1, 2]) := heapSortDyn_ok _

example : heapSortDyn ([3, 1, 2].map PyVal.int) = .ok [1, 2, 3] := by
  rw [heapSortDyn_ok]
  congr 1
  native_decide
example : heapSortDyn [PyVal.int 1, PyVal.other] = .error "Input must be List[int]" :=
  heapSortDyn_err _ rfl

/-! ## Properties -/

/-- The output is sorted in non-decreasing order. -/
def sorted_prop (arr : List Int) : Prop := List.Sorted (· ≤ ·) (heapSort arr)

theorem sorted_thm (arr : List Int) : sorted_prop arr := heapSort_sorted arr

/-- The output is a permutation of the input (no element is lost or invented). -/
def perm_prop (arr : List Int) : Prop := List.Perm (heapSort arr) arr

theorem perm_thm (arr : List Int) : perm_prop arr := heapSort_perm arr

/-- Sorting preserves the length. -/
def length_prop (arr : List Int) : Prop := (heapSort arr).length = arr.length

theorem length_thm (arr : List Int) : length_prop arr := heapSort_length arr

/-- Membership is preserved. -/
def mem_prop (y : Int) (arr : List Int) : Prop := (y ∈ heapSort arr ↔ y ∈ arr)

theorem mem_thm (y : Int) (arr : List Int) : mem_prop y arr := mem_heapSort y arr

/-- Sorting is idempotent. -/
def idempotent_prop (arr : List Int) : Prop := heapSort (heapSort arr) = heapSort arr

theorem idempotent_thm (arr : List Int) : idempotent_prop arr := heapSort_idempotent arr

/-- `heapSort arr` is *the* sorted permutation of `arr`. -/
def spec_prop (arr : List Int) : Prop :=
  List.Sorted (· ≤ ·) (heapSort arr) ∧ List.Perm (heapSort arr) arr ∧
    ∀ l : List Int, List.Sorted (· ≤ ·) l → List.Perm l arr → l = heapSort arr

theorem spec_thm (arr : List Int) : spec_prop arr :=
  ⟨heapSort_sorted arr, heapSort_perm arr,
    fun _ hl hp => Sorted_Perm_unique hl (heapSort_sorted arr)
      (List.Perm.trans hp (heapSort_perm arr).symm)⟩

/-- Conjunction of the executable properties of `heapSort`. -/
def heapSort_prop (arr : List Int) : Prop :=
  sorted_prop arr ∧ perm_prop arr ∧ length_prop arr ∧ idempotent_prop arr

theorem heapSort_thm (arr : List Int) : heapSort_prop arr :=
  ⟨heapSort_sorted arr, heapSort_perm arr, heapSort_length arr, heapSort_idempotent arr⟩

/-! ## Post-condition -/

/-- Post-condition of the Python `heap_sort`: the returned list is sorted, is a
permutation of the input, and has the same length. -/
def Post_prop (arr out : List Int) : Prop :=
  List.Sorted (· ≤ ·) out ∧ List.Perm out arr ∧ out.length = arr.length

/-! ## Property-based tests -/

/-- Executable Boolean form of `List.Sorted (· ≤ ·)`. -/
def sortedB (l : List Int) : Bool := decide (List.Sorted (· ≤ ·) l)

/-- Executable Boolean form of `List.Perm`. -/
def permB (l₁ l₂ : List Int) : Bool := decide (List.Perm l₁ l₂)

example : sortedB [1, 2, 3] = true := by native_decide
example : sortedB [2, 1, 3] = false := by native_decide
example : permB [1, 2, 2] [2, 1, 2] = true := by native_decide
example : permB [1, 2] [1, 3] = false := by native_decide

/-- A deterministic family of test inputs of every length. -/
def testList (n : Nat) : List Int :=
  (List.range n).map (fun i => Int.ofNat ((i * i + 3 * i + 7) % 13) - 6)

/-- Fixed test inputs, mirroring the assertions of the Python `check` function. -/
def fixedInputs : List (List Int) :=
  [[], [1], [3, 1, 2], [1, 2, 3], [2, 1, 3], [5, 2, 4, 6, 1, 3], [9, 8, 7, 6, 5, 4, 3, 2, 1],
   [2, 6, 4, 3, 1, 5], [2, 1], [1, 2], [3, 1, 4, 1, 2, 3], [5, 5, 5, 5, 5], [1, 2, 3, 4, 5],
   [5, 4, 3, 2, 1], [3, 7, 1, 9, 2, 8, 4, 6, 5], [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42],
   [-5, 3, -2, 0, 7, -1]]

-- Bounded PBT for `heapSort_prop` / `Post_prop`.
example : (List.range 18).all (fun n =>
    let xs := testList n
    sortedB (heapSort xs) && permB xs (heapSort xs)
      && ((heapSort xs).length == xs.length)
      && (heapSort (heapSort xs) == heapSort xs)) = true := by native_decide

example : fixedInputs.all (fun xs =>
    sortedB (heapSort xs) && permB xs (heapSort xs)
      && ((heapSort xs).length == xs.length)
      && (heapSort (heapSort xs) == heapSort xs)) = true := by native_decide

-- Bounded PBT for the uniqueness clause of `spec_prop` (the clause itself quantifies
-- over all lists, so only a bounded form is executable).
example : fixedInputs.all (fun xs =>
    fixedInputs.all (fun l => !(sortedB l && permB l xs) || (l == heapSort xs))) = true :=
  by native_decide

-- Randomized PBTs.
#eval Plausible.Testable.check (∀ xs : List Int, List.Sorted (· ≤ ·) (heapSort xs))
#eval Plausible.Testable.check (∀ xs : List Int, List.Perm (heapSort xs) xs)
#eval Plausible.Testable.check (∀ xs : List Int, (heapSort xs).length = xs.length)
#eval Plausible.Testable.check (∀ xs : List Int, heapSort (heapSort xs) = heapSort xs)
#eval Plausible.Testable.check (∀ (xs : List Int) (y : Int), (y ∈ heapSort xs ↔ y ∈ xs))
/-- Executable Boolean form of `Post_prop`. -/
def postB (arr out : List Int) : Bool :=
  sortedB out && permB out arr && (out.length == arr.length)

/-- Executable Boolean form of `heapSort_prop`. -/
def heapSortB (arr : List Int) : Bool :=
  postB arr (heapSort arr) && (heapSort (heapSort arr) == heapSort arr)

example : postB [3, 1, 2] (heapSort [3, 1, 2]) = true := by native_decide
example : heapSortB [3, 1, 2] = true := by native_decide
example : heapSortB [5, 5, 5, 5, 5] = true := by native_decide

#eval Plausible.Testable.check (∀ xs : List Int, postB xs (heapSort xs))
#eval Plausible.Testable.check (∀ xs : List Int, heapSortB xs)

/-! ## Correctness -/

theorem heapSort_correct (arr : List Int) : Pre arr → Post_prop arr (heapSort arr) :=
  fun _ => ⟨heapSort_sorted arr, heapSort_perm arr, heapSort_length arr⟩
