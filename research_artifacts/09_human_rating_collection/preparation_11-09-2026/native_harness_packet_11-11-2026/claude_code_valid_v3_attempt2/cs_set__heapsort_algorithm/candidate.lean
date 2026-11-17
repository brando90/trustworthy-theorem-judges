import Mathlib

/-!
# HEAPSORT (CLRS 6.4) on 0-based max-heap arrays

Lean 4 formalization of the Python program `heapsort_algorithm.py`.

* `parent`, `left`, `right` are the 0-based index helpers of the Python file.
* `maxHeapify a i heapSize` is Python's `max_heapify` (the `while True` sift-down loop,
  written as a well-founded recursion on `heapSize - i`).
* `buildMaxHeap` is Python's `build_max_heap`, `heapsort` is Python's `heapsort`;
  both return a fresh (sorted / heapified) copy and never mutate the input.
* The Python precondition `pre(arr)` ("every element is a natural number") is encoded by the
  Lean type `List Nat`; `heapsortChecked` models the `ValueError` path for `List Int` inputs.

We prove that `heapsort` returns a sorted permutation of its input (hence it coincides with
Python's `sorted(arr)`, i.e. `List.mergeSort`), that `buildMaxHeap` really builds a max-heap,
and that an imperative `Id.run do` implementation with `for` loops, `break` and mutable
state computes exactly the same function.
-/

namespace heapsort_algorithm

/-! ## Index helpers (Python `parent`, `left`, `right`) -/

/-- Python `parent(i)`: `0 if i == 0 else (i - 1) // 2`. -/
def parent (i : Nat) : Nat := if i = 0 then 0 else (i - 1) / 2

/-- Python `left(i) = 2 * i + 1`. -/
def left (i : Nat) : Nat := 2 * i + 1

/-- Python `right(i) = 2 * i + 2`. -/
def right (i : Nat) : Nat := 2 * i + 2

theorem parent_lt {j : Nat} (hj : 0 < j) : parent j < j := by
  unfold parent; split_ifs <;> omega

theorem parent_le (j : Nat) : parent j ≤ j := by
  unfold parent; split_ifs <;> omega

theorem parent_mono {j k : Nat} (h : j ≤ k) : parent j ≤ parent k := by
  unfold parent; split_ifs <;> omega

theorem parent_left (i : Nat) : parent (left i) = i := by
  unfold parent left
  rw [if_neg (by omega)]
  omega

theorem parent_right (i : Nat) : parent (right i) = i := by
  unfold parent right
  rw [if_neg (by omega)]
  omega

theorem lt_left (i : Nat) : i < left i := by unfold left; omega

theorem lt_right (i : Nat) : i < right i := by unfold right; omega

/-- The children of `h` are exactly `left h` and `right h`. -/
theorem parent_eq_iff {c h : Nat} (hc : 0 < c) : parent c = h ↔ c = left h ∨ c = right h := by
  unfold parent left right
  constructor
  · intro heq; split_ifs at heq <;> omega
  · intro heq; split_ifs <;> omega

/-! ## Functional implementation -/

/-- The index `largest` computed by the two `if` statements of Python's `max_heapify`:
the position of the largest value among `i`, `left i`, `right i` (children only if they lie
below `heapSize`). -/
def largestOf (a : Array Nat) (i heapSize : Nat) : Nat :=
  let l := left i
  let r := right i
  let largest₁ := if l < heapSize ∧ a[l]! > a[i]! then l else i
  if r < heapSize ∧ a[r]! > a[largest₁]! then r else largest₁

theorem largestOf_ne (a : Array Nat) (i heapSize : Nat) (h : largestOf a i heapSize ≠ i) :
    i < largestOf a i heapSize ∧ largestOf a i heapSize < heapSize := by
  simp only [largestOf, left, right] at *
  split_ifs at * <;> omega

theorem largestOf_cases (a : Array Nat) (i hs : Nat) :
    largestOf a i hs = i ∨ largestOf a i hs = left i ∨ largestOf a i hs = right i := by
  simp only [largestOf, left, right]
  split_ifs <;> simp

theorem le_largestOf_self (a : Array Nat) (i hs : Nat) : a[i]! ≤ a[largestOf a i hs]! := by
  simp only [largestOf, left, right]
  split_ifs <;> omega

theorem le_largestOf_left (a : Array Nat) (i hs : Nat) (h : left i < hs) :
    a[left i]! ≤ a[largestOf a i hs]! := by
  simp only [largestOf, left, right] at *
  split_ifs <;> omega

theorem le_largestOf_right (a : Array Nat) (i hs : Nat) (h : right i < hs) :
    a[right i]! ≤ a[largestOf a i hs]! := by
  simp only [largestOf, left, right] at *
  split_ifs <;> omega

theorem largestOf_of_ge (a : Array Nat) (i hs : Nat) (h : hs ≤ i) : largestOf a i hs = i := by
  simp only [largestOf, left, right]
  split_ifs <;> omega

/-- Python `max_heapify(arr, i, heap_size)`: sift the value at `i` down until the subtree
rooted at `i` is a max-heap. Each iteration of Python's `while True` loop is one recursive call;
the loop variable strictly increases and stays below `heapSize`, which gives termination. -/
def maxHeapify (a : Array Nat) (i heapSize : Nat) : Array Nat :=
  if largestOf a i heapSize = i then a
  else maxHeapify (a.swapIfInBounds i (largestOf a i heapSize)) (largestOf a i heapSize) heapSize
termination_by heapSize - i
decreasing_by
  have := largestOf_ne a i heapSize (by assumption)
  omega

/-- `buildLoop a n k` runs `max_heapify(a, i, n)` for `i = k-1, k-2, …, 0` (in this order). -/
def buildLoop (a : Array Nat) (n : Nat) : Nat → Array Nat
  | 0 => a
  | k + 1 => buildLoop (maxHeapify a k n) n k

/-- Python `build_max_heap(arr)` (on arrays): `for i in range(parent(n-1), -1, -1)`. -/
def buildMaxHeap (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a else buildLoop a a.size (parent (a.size - 1) + 1)

/-- `extractLoop a i` runs `swap(a, 0, i); max_heapify(a, 0, i)` for `i, i-1, …, 1`. -/
def extractLoop (a : Array Nat) : Nat → Array Nat
  | 0 => a
  | i + 1 => extractLoop (maxHeapify (a.swapIfInBounds 0 (i + 1)) 0 (i + 1)) i

/-- Python `heapsort` on arrays. -/
def heapsortArray (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a else extractLoop (buildMaxHeap a) (a.size - 1)

/-- Python `heapsort(arr)`: sort a list of naturals in ascending order using heapsort. -/
def heapsort (arr : List Nat) : List Nat :=
  (heapsortArray arr.toArray).toList

/-- Python `build_max_heap(arr)` on lists. -/
def buildMaxHeapList (arr : List Nat) : List Nat :=
  (buildMaxHeap arr.toArray).toList

/-- Python-facing wrapper: `heapsort` raises `ValueError("Input must be List[Nat]")` unless every
element is a natural number. `none` models the exception. -/
def heapsortChecked (arr : List Int) : Option (List Int) :=
  if arr.all (fun x => 0 ≤ x) then some ((heapsort (arr.map Int.toNat)).map Int.ofNat) else none

/-! ## Unit tests (Python `check`) -/

example : heapsort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsort [] = [] := by native_decide
example : heapsort [42] = [42] := by native_decide
example : heapsort [2, 1] = [1, 2] := by native_decide
example : heapsort [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsort [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : heapsort [2, 1] ≠ [2, 1] := by native_decide
example : (heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]).length = 9 := by native_decide
example : heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4] = [5, 13, 2, 25, 7, 17, 20, 8, 4].mergeSort := by
  native_decide
-- precondition violation: a negative entry raises `ValueError` in Python
example : heapsortChecked [1, -1] = none := by native_decide
example : heapsortChecked [3, 1, 2] = some [1, 2, 3] := by native_decide
-- index helpers
example : parent 0 = 0 ∧ parent 1 = 0 ∧ parent 2 = 0 ∧ parent 3 = 1 ∧ parent 4 = 1 := by
  native_decide
example : left 3 = 7 ∧ right 3 = 8 := by native_decide
-- build_max_heap on the CLRS Figure 6.3 input
example : buildMaxHeapList [4, 1, 3, 2, 16, 9, 10, 14, 8, 7] = [16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by
  native_decide
example : buildMaxHeapList [5, 13, 2, 25, 7, 17, 20, 8, 4] = [25, 13, 20, 8, 7, 17, 2, 5, 4] := by
  native_decide
-- max_heapify on the CLRS Figure 6.2 input (i = 1, heap_size = 10)
example : (maxHeapify #[16, 4, 10, 14, 7, 9, 3, 2, 8, 1] 1 10).toList =
    [16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by native_decide
example : (maxHeapify #[1, 5, 3, 4, 2] 0 5).toList = [5, 4, 3, 1, 2] := by native_decide

#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]
#eval buildMaxHeapList [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]
#eval heapsortChecked [1, -1]

/-! ## Pre-condition -/

/-- Python `pre(arr)`: `arr` is a list whose elements are all natural numbers.  The Lean type
`List Nat` already guarantees this, so the precondition always holds. -/
def Pre (_arr : List Nat) : Prop := True

/-! ## Heap predicates -/

/-- The first `hs` entries of `a` form a max-heap: every non-root node is `≤` its parent. -/
def IsMaxHeap (a : Array Nat) (hs : Nat) : Prop :=
  ∀ j, j < hs → 0 < j → a[j]! ≤ a[parent j]!

instance (a : Array Nat) (hs : Nat) : Decidable (IsMaxHeap a hs) :=
  inferInstanceAs (Decidable (∀ j, j < hs → 0 < j → a[j]! ≤ a[parent j]!))

/-- Heap property restricted to the nodes whose parent index is at least `lo`. -/
def HeapFrom (a : Array Nat) (hs lo : Nat) : Prop :=
  ∀ j, j < hs → 0 < j → lo ≤ parent j → a[j]! ≤ a[parent j]!

theorem isMaxHeap_iff_heapFrom_zero (a : Array Nat) (hs : Nat) :
    IsMaxHeap a hs ↔ HeapFrom a hs 0 := by
  constructor
  · intro h j hj hj0 _; exact h j hj hj0
  · intro h j hj hj0; exact h j hj hj0 (Nat.zero_le _)

/-- In a max-heap the root is the maximum. -/
theorem isMaxHeap_le_root (a : Array Nat) (hs : Nat) (hh : IsMaxHeap a hs) :
    ∀ j, j < hs → a[j]! ≤ a[0]! := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hj0 : j = 0
    · subst hj0; exact le_refl _
    · have hp := parent_lt (Nat.pos_of_ne_zero hj0)
      exact (hh j hj (Nat.pos_of_ne_zero hj0)).trans (ih (parent j) hp (by omega))

/-! ## Lemmas about `Array.swapIfInBounds` -/

theorem getElem!_swapIfInBounds (a : Array Nat) {i j : Nat} (hi : i < a.size) (hj : j < a.size)
    (k : Nat) :
    (a.swapIfInBounds i j)[k]! = if k = i then a[j]! else if k = j then a[i]! else a[k]! := by
  unfold Array.swapIfInBounds
  rw [dif_pos hi, dif_pos hj]
  by_cases hk : k < a.size
  · have hk' : k < (a.swap i j hi hj).size := by rw [Array.size_swap]; exact hk
    rw [getElem!_pos (a.swap i j hi hj) k hk', Array.getElem_swap' hk, getElem!_pos a j hj,
      getElem!_pos a i hi, getElem!_pos a k hk]
  · have hki : k ≠ i := fun h => hk (h ▸ hi)
    have hkj : k ≠ j := fun h => hk (h ▸ hj)
    rw [if_neg hki, if_neg hkj]
    have hk' : ¬ k < (a.swap i j hi hj).size := by rw [Array.size_swap]; exact hk
    rw [getElem!_neg (a.swap i j hi hj) k hk', getElem!_neg a k hk]

theorem getElem!_swapIfInBounds_of_ne (a : Array Nat) {i j k : Nat} (hki : k ≠ i) (hkj : k ≠ j) :
    (a.swapIfInBounds i j)[k]! = a[k]! := by
  unfold Array.swapIfInBounds
  split_ifs with h1 h2
  · by_cases hk : k < a.size
    · have hk' : k < (a.swap i j h1 h2).size := by rw [Array.size_swap]; exact hk
      rw [getElem!_pos (a.swap i j h1 h2) k hk', Array.getElem_swap_of_ne hk hki hkj,
        getElem!_pos a k hk]
    · have hk' : ¬ k < (a.swap i j h1 h2).size := by rw [Array.size_swap]; exact hk
      rw [getElem!_neg (a.swap i j h1 h2) k hk', getElem!_neg a k hk]
  · rfl
  · rfl

theorem perm_swapIfInBounds (a : Array Nat) (i j : Nat) :
    (a.swapIfInBounds i j).toList.Perm a.toList := by
  unfold Array.swapIfInBounds
  split_ifs with h1 h2
  · exact Array.perm_iff_toList_perm.mp (Array.swap_perm h1 h2)
  · exact List.Perm.refl _
  · exact List.Perm.refl _

/-! ## Properties of `maxHeapify` -/

theorem maxHeapify_size (a : Array Nat) (i hs : Nat) : (maxHeapify a i hs).size = a.size := by
  induction a, i using maxHeapify.induct hs with
  | case1 a i h => rw [maxHeapify, if_pos h]
  | case2 a i h ih => rw [maxHeapify, if_neg h, ih, Array.size_swapIfInBounds]

theorem maxHeapify_perm (a : Array Nat) (i hs : Nat) :
    (maxHeapify a i hs).toList.Perm a.toList := by
  induction a, i using maxHeapify.induct hs with
  | case1 a i h => rw [maxHeapify, if_pos h]
  | case2 a i h ih =>
    rw [maxHeapify, if_neg h]
    exact ih.trans (perm_swapIfInBounds a i _)

/-- `max_heapify(a, i, hs)` does not touch positions `≥ hs`. -/
theorem maxHeapify_frame (a : Array Nat) (i hs k : Nat) (hk : hs ≤ k) :
    (maxHeapify a i hs)[k]! = a[k]! := by
  induction a, i using maxHeapify.induct hs with
  | case1 a i h => rw [maxHeapify, if_pos h]
  | case2 a i h ih =>
    rw [maxHeapify, if_neg h, ih]
    have hne := largestOf_ne a i hs h
    exact getElem!_swapIfInBounds_of_ne a (by omega) (by omega)

/-- `max_heapify` keeps every value of the heap part below any bound `B`. -/
theorem maxHeapify_bounded (a : Array Nat) (i hs B : Nat) (hsz : hs ≤ a.size)
    (hb : ∀ k, k < hs → a[k]! ≤ B) : ∀ k, k < hs → (maxHeapify a i hs)[k]! ≤ B := by
  induction a, i using maxHeapify.induct hs with
  | case1 a i h => rw [maxHeapify, if_pos h]; exact hb
  | case2 a i h ih =>
    rw [maxHeapify, if_neg h]
    have hne := largestOf_ne a i hs h
    apply ih
    · rw [Array.size_swapIfInBounds]; exact hsz
    · intro k hk
      rw [getElem!_swapIfInBounds a (by omega) (by omega) k]
      split_ifs
      · exact hb _ hne.2
      · exact hb _ (by omega)
      · exact hb _ hk

/-- Invariant of the sift-down loop started at root `i`, with the "hole" currently at `h`:
every heap constraint below `i` holds except possibly those between `h` and its children, and
(once the hole has moved) the children of `h` are bounded by the parent of `h`. -/
def SiftInv (a : Array Nat) (hs i h : Nat) : Prop :=
  i ≤ h ∧
  (∀ j, j < hs → 0 < j → i ≤ parent j → parent j ≠ h → a[j]! ≤ a[parent j]!) ∧
  (h ≠ i → ∀ j, j < hs → parent j = h → a[j]! ≤ a[parent h]!)

theorem siftInv_step (a : Array Nat) (hs i h : Nat) (hsz : hs ≤ a.size) (inv : SiftInv a hs i h)
    (hne : largestOf a h hs ≠ h) :
    SiftInv (a.swapIfInBounds h (largestOf a h hs)) hs i (largestOf a h hs) := by
  obtain ⟨hih, hA, hB⟩ := inv
  have hlt := largestOf_ne a h hs hne
  have hcases := largestOf_cases a h hs
  have hself := le_largestOf_self a h hs
  have hleft := le_largestOf_left a h hs
  have hright := le_largestOf_right a h hs
  generalize largestOf a h hs = g at *
  have hpg : parent g = h := by
    rcases hcases with h1 | h1 | h1
    · exact absurd h1 hne
    · rw [h1, parent_left]
    · rw [h1, parent_right]
  have hh : h < a.size := by omega
  have hga : g < a.size := by omega
  have hsw := getElem!_swapIfInBounds a hh hga
  refine ⟨by omega, ?_, ?_⟩
  · intro j hj hj0 hij hjg
    rw [hsw j, hsw (parent j)]
    have hpj := parent_lt hj0
    by_cases hjh : j = h
    · subst hjh
      rw [if_pos rfl, if_neg (by omega), if_neg (by omega)]
      have hhi : j ≠ i := by omega
      exact hB hhi g hlt.2 hpg
    · rw [if_neg hjh]
      by_cases hjg' : j = g
      · subst hjg'
        rw [if_pos rfl, hpg, if_pos rfl]
        exact hself
      · rw [if_neg hjg']
        by_cases hpjh : parent j = h
        · rw [if_pos hpjh]
          rcases (parent_eq_iff hj0).mp hpjh with hjl | hjr
          · rw [hjl]; exact hleft (hjl ▸ hj)
          · rw [hjr]; exact hright (hjr ▸ hj)
        · rw [if_neg hpjh, if_neg hjg]
          exact hA j hj hj0 hij hpjh
  · intro _ j hj hpj
    rw [hsw j, hsw (parent g), hpg, if_pos rfl]
    have hj0 : 0 < j := by
      by_contra h0
      have h0' : j = 0 := by omega
      subst h0'
      simp [parent] at hpj
      omega
    have hpjlt := parent_lt hj0
    rw [if_neg (by omega), if_neg (by omega)]
    have := hA j hj hj0 (by omega) (by omega)
    rw [hpj] at this
    exact this

theorem siftInv_done (a : Array Nat) (hs i h : Nat) (inv : SiftInv a hs i h)
    (heq : largestOf a h hs = h) : HeapFrom a hs i := by
  obtain ⟨_, hA, _⟩ := inv
  intro j hj hj0 hij
  by_cases hpjh : parent j = h
  · rw [hpjh]
    rcases (parent_eq_iff hj0).mp hpjh with hjl | hjr
    · have := le_largestOf_left a h hs (hjl ▸ hj)
      rw [heq] at this
      rw [hjl]; exact this
    · have := le_largestOf_right a h hs (hjr ▸ hj)
      rw [heq] at this
      rw [hjr]; exact this
  · exact hA j hj hj0 hij hpjh

/-- Correctness of `max_heapify`: starting from a sift-down invariant it establishes the heap
property on all nodes whose parent is `≥ i`. -/
theorem maxHeapify_heapFrom (hs i : Nat) (a : Array Nat) (h : Nat) (hsz : hs ≤ a.size)
    (inv : SiftInv a hs i h) : HeapFrom (maxHeapify a h hs) hs i := by
  induction a, h using maxHeapify.induct hs with
  | case1 a h heq =>
    rw [maxHeapify, if_pos heq]
    exact siftInv_done a hs i h inv heq
  | case2 a h hne ih =>
    rw [maxHeapify, if_neg hne]
    exact ih (by rw [Array.size_swapIfInBounds]; exact hsz) (siftInv_step a hs i h hsz inv hne)

/-- CLRS-style statement: if the children subtrees are heaps (all constraints with parent `> i`
hold) then after `max_heapify(a, i, hs)` all constraints with parent `≥ i` hold. -/
theorem maxHeapify_heapFrom_of_heapFrom_succ (a : Array Nat) (i hs : Nat) (hsz : hs ≤ a.size)
    (hh : HeapFrom a hs (i + 1)) : HeapFrom (maxHeapify a i hs) hs i := by
  apply maxHeapify_heapFrom hs i a i hsz
  refine ⟨le_refl i, ?_, fun h => absurd rfl h⟩
  intro j hj hj0 hij hne
  exact hh j hj hj0 (by omega)

/-! ## Properties of `buildMaxHeap` -/

theorem buildLoop_size (n : Nat) : ∀ (k : Nat) (a : Array Nat), (buildLoop a n k).size = a.size
  | 0, a => rfl
  | k + 1, a => by rw [buildLoop, buildLoop_size n k, maxHeapify_size]

theorem buildLoop_perm (n : Nat) :
    ∀ (k : Nat) (a : Array Nat), (buildLoop a n k).toList.Perm a.toList
  | 0, a => List.Perm.refl _
  | k + 1, a => by
    rw [buildLoop]
    exact (buildLoop_perm n k _).trans (maxHeapify_perm a k n)

theorem buildLoop_heapFrom (n : Nat) :
    ∀ (k : Nat) (a : Array Nat), n ≤ a.size → HeapFrom a n k → HeapFrom (buildLoop a n k) n 0
  | 0, a, _, hh => hh
  | k + 1, a, hsz, hh => by
    rw [buildLoop]
    apply buildLoop_heapFrom n k
    · rw [maxHeapify_size]; exact hsz
    · exact maxHeapify_heapFrom_of_heapFrom_succ a k n hsz hh

theorem buildMaxHeap_size (a : Array Nat) : (buildMaxHeap a).size = a.size := by
  unfold buildMaxHeap
  split_ifs
  · rfl
  · rw [buildLoop_size]

theorem buildMaxHeap_perm (a : Array Nat) : (buildMaxHeap a).toList.Perm a.toList := by
  unfold buildMaxHeap
  split_ifs
  · exact List.Perm.refl _
  · exact buildLoop_perm _ _ _

/-- `build_max_heap` produces a max-heap on the whole array. -/
theorem buildMaxHeap_isMaxHeap (a : Array Nat) : IsMaxHeap (buildMaxHeap a) a.size := by
  unfold buildMaxHeap
  split_ifs with h1
  · intro j hj hj0; omega
  · rw [isMaxHeap_iff_heapFrom_zero]
    apply buildLoop_heapFrom a.size _ a (le_refl _)
    intro j hj hj0 hpj
    have := parent_mono (show j ≤ a.size - 1 by omega)
    omega

/-! ## Properties of the extraction phase -/

theorem extractLoop_size : ∀ (i : Nat) (a : Array Nat), (extractLoop a i).size = a.size
  | 0, a => rfl
  | i + 1, a => by
    rw [extractLoop, extractLoop_size i, maxHeapify_size, Array.size_swapIfInBounds]

theorem extractLoop_perm : ∀ (i : Nat) (a : Array Nat), (extractLoop a i).toList.Perm a.toList
  | 0, a => List.Perm.refl _
  | i + 1, a => by
    rw [extractLoop]
    exact ((extractLoop_perm i _).trans (maxHeapify_perm _ 0 (i + 1))).trans
      (perm_swapIfInBounds a 0 (i + 1))

/-- Loop invariant of the extraction phase, before the iteration with index `i`:
`a[0..i]` is a max-heap, `a[i+1..n)` is sorted, and every heap entry is `≤ a[i+1]`. -/
def ExtractInv (a : Array Nat) (n i : Nat) : Prop :=
  IsMaxHeap a (i + 1) ∧
  (∀ j k, i + 1 ≤ j → j < k → k < n → a[j]! ≤ a[k]!) ∧
  (∀ j, j ≤ i → i + 1 < n → a[j]! ≤ a[i + 1]!)

theorem extractLoop_inv (n : Nat) :
    ∀ (i : Nat) (a : Array Nat), a.size = n → i < n → ExtractInv a n i →
      ExtractInv (extractLoop a i) n 0
  | 0, a, _, _, inv => inv
  | i + 1, a, hsz, hin, inv => by
    rw [extractLoop]
    obtain ⟨hheap, hsorted, hbound⟩ := inv
    have h0 : 0 < a.size := by omega
    have hi1 : i + 1 < a.size := by omega
    have hsw := getElem!_swapIfInBounds a h0 hi1
    have hmax := isMaxHeap_le_root a (i + 1 + 1) hheap
    have hsz' : (a.swapIfInBounds 0 (i + 1)).size = n := by
      rw [Array.size_swapIfInBounds]; exact hsz
    have hsz'' : (maxHeapify (a.swapIfInBounds 0 (i + 1)) 0 (i + 1)).size = n := by
      rw [maxHeapify_size]; exact hsz'
    apply extractLoop_inv n i _ hsz'' (by omega)
    have hframe : ∀ k, i + 1 ≤ k →
        (maxHeapify (a.swapIfInBounds 0 (i + 1)) 0 (i + 1))[k]! = (a.swapIfInBounds 0 (i + 1))[k]! :=
      fun k hk => maxHeapify_frame _ 0 (i + 1) k hk
    refine ⟨?_, ?_, ?_⟩
    · -- the remaining prefix is again a max-heap
      rw [isMaxHeap_iff_heapFrom_zero]
      apply maxHeapify_heapFrom (i + 1) 0 _ 0 (by omega)
      refine ⟨le_refl 0, ?_, fun h => absurd rfl h⟩
      intro j hj hj0 _ hpj
      rw [hsw j, hsw (parent j)]
      have hpl := parent_lt hj0
      rw [if_neg (by omega), if_neg (by omega), if_neg hpj, if_neg (by omega)]
      exact hheap j (by omega) hj0
    · -- the suffix from `i + 1` is sorted
      intro j k hj hjk hk
      rw [hframe j hj, hframe k (by omega), hsw j, hsw k, if_neg (show ¬ k = 0 by omega),
        if_neg (show ¬ k = i + 1 by omega), if_neg (show ¬ j = 0 by omega)]
      by_cases hji : j = i + 1
      · rw [if_pos hji]
        have h1 : a[0]! ≤ a[i + 1 + 1]! := hbound 0 (by omega) (by omega)
        by_cases hk2 : k = i + 1 + 1
        · rw [hk2]; exact h1
        · exact h1.trans (hsorted (i + 1 + 1) k (le_refl _) (by omega) hk)
      · rw [if_neg hji]
        exact hsorted j k (by omega) hjk hk
    · -- every heap entry is bounded by the new suffix head `a[i+1] = old a[0]`
      intro j hj _
      rw [hframe (i + 1) (le_refl _), hsw (i + 1), if_neg (by omega), if_pos rfl]
      apply maxHeapify_bounded _ 0 (i + 1) a[0]! (by omega)
      · intro k hk
        rw [hsw k]
        split_ifs
        · exact hmax (i + 1) (by omega)
        · exact le_refl _
        · exact hmax k (by omega)
      · omega

/-! ## Correctness of `heapsortArray` -/

theorem heapsortArray_size (a : Array Nat) : (heapsortArray a).size = a.size := by
  unfold heapsortArray
  split_ifs
  · rfl
  · rw [extractLoop_size, buildMaxHeap_size]

theorem heapsortArray_perm (a : Array Nat) : (heapsortArray a).toList.Perm a.toList := by
  unfold heapsortArray
  split_ifs
  · exact List.Perm.refl _
  · exact (extractLoop_perm _ _).trans (buildMaxHeap_perm a)

theorem heapsortArray_sorted (a : Array Nat) :
    ∀ j k, j < k → k < a.size → (heapsortArray a)[j]! ≤ (heapsortArray a)[k]! := by
  unfold heapsortArray
  split_ifs with h1
  · intro j k hjk hk; omega
  · intro j k hjk hk
    have hinv := extractLoop_inv a.size (a.size - 1) (buildMaxHeap a) (buildMaxHeap_size a)
      (by omega) ?_
    · obtain ⟨_, hsorted, hbound⟩ := hinv
      by_cases hj0 : j = 0
      · subst hj0
        have h01 := hbound 0 (le_refl _) (by omega)
        by_cases hk1 : k = 1
        · rw [hk1]; exact h01
        · exact h01.trans (hsorted 1 k (le_refl _) (by omega) hk)
      · exact hsorted j k (by omega) hjk hk
    · refine ⟨?_, ?_, ?_⟩
      · have := buildMaxHeap_isMaxHeap a
        rwa [show a.size - 1 + 1 = a.size by omega]
      · intro j k hj hjk hk; omega
      · intro j hj hlt; omega

/-! ## Properties of `heapsort` -/

theorem heapsort_length (arr : List Nat) : (heapsort arr).length = arr.length := by
  unfold heapsort
  rw [Array.length_toList, heapsortArray_size, List.size_toArray]

theorem heapsort_perm (arr : List Nat) : (heapsort arr).Perm arr := by
  unfold heapsort
  have := heapsortArray_perm arr.toArray
  rwa [List.toList_toArray] at this

theorem heapsort_sorted (arr : List Nat) : List.Sorted (· ≤ ·) (heapsort arr) := by
  unfold heapsort List.Sorted
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [Array.length_toList] at hi hj
  rw [Array.getElem_toList, Array.getElem_toList]
  have hsz : (heapsortArray arr.toArray).size = arr.length := by
    rw [heapsortArray_size, List.size_toArray]
  have := heapsortArray_sorted arr.toArray i j hij (by rw [List.size_toArray]; omega)
  rwa [getElem!_pos (heapsortArray arr.toArray) i hi,
    getElem!_pos (heapsortArray arr.toArray) j hj] at this

theorem heapsort_count (arr : List Nat) (x : Nat) : (heapsort arr).count x = arr.count x :=
  (heapsort_perm arr).count_eq x

theorem heapsort_mem (arr : List Nat) (x : Nat) : x ∈ heapsort arr ↔ x ∈ arr :=
  (heapsort_perm arr).mem_iff

/-- `heapsort` agrees with Python's `sorted(arr)` (the stable merge sort of the library). -/
theorem heapsort_eq_mergeSort (arr : List Nat) : heapsort arr = arr.mergeSort := by
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact (heapsort_perm arr).trans (List.mergeSort_perm arr _).symm
  · exact heapsort_sorted arr
  · exact List.sorted_mergeSort' (· ≤ ·) arr

/-- Sorting an already sorted list returns it unchanged. -/
theorem heapsort_of_sorted (arr : List Nat) (h : List.Sorted (· ≤ ·) arr) : heapsort arr = arr :=
  List.eq_of_perm_of_sorted (heapsort_perm arr) (heapsort_sorted arr) h

theorem buildMaxHeapList_length (arr : List Nat) : (buildMaxHeapList arr).length = arr.length := by
  unfold buildMaxHeapList
  rw [Array.length_toList, buildMaxHeap_size, List.size_toArray]

theorem buildMaxHeapList_perm (arr : List Nat) : (buildMaxHeapList arr).Perm arr := by
  unfold buildMaxHeapList
  have := buildMaxHeap_perm arr.toArray
  rwa [List.toList_toArray] at this

theorem heapsortChecked_none (arr : List Int) (h : ∃ x ∈ arr, x < 0) : heapsortChecked arr = none := by
  unfold heapsortChecked
  rw [if_neg]
  obtain ⟨x, hx, hneg⟩ := h
  simp only [List.all_eq_true, decide_eq_true_eq, not_forall]
  exact ⟨x, hx, by omega⟩

theorem heapsortChecked_some (arr : List Int) (h : ∀ x ∈ arr, 0 ≤ x) :
    heapsortChecked arr = some ((heapsort (arr.map Int.toNat)).map Int.ofNat) := by
  unfold heapsortChecked
  rw [if_pos]
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact h

/-! ## Property propositions and theorems -/

/-- The output is sorted in ascending order. -/
def sorted_prop (arr : List Nat) : Prop := List.Sorted (· ≤ ·) (heapsort arr)

theorem sorted_thm (arr : List Nat) : sorted_prop arr := heapsort_sorted arr

/-- The output is a permutation of the input (`sorted(out) == sorted(arr)`). -/
def perm_prop (arr : List Nat) : Prop := (heapsort arr).Perm arr

theorem perm_thm (arr : List Nat) : perm_prop arr := heapsort_perm arr

/-- The output has the same length as the input (`len(out) == len(arr)`). -/
def length_prop (arr : List Nat) : Prop := (heapsort arr).length = arr.length

theorem length_thm (arr : List Nat) : length_prop arr := heapsort_length arr

/-- Every value occurs equally often in input and output. -/
def count_prop (arr : List Nat) : Prop := ∀ x, (heapsort arr).count x = arr.count x

theorem count_thm (arr : List Nat) : count_prop arr := heapsort_count arr

/-- The output equals Python's `sorted(arr)`, i.e. the (unique) sorted permutation. -/
def eq_sorted_prop (arr : List Nat) : Prop := heapsort arr = arr.mergeSort

theorem eq_sorted_thm (arr : List Nat) : eq_sorted_prop arr := heapsort_eq_mergeSort arr

/-- `build_max_heap` returns a max-heap that is a permutation of the input. -/
def buildMaxHeap_prop (arr : List Nat) : Prop :=
  IsMaxHeap (buildMaxHeap arr.toArray) arr.length ∧ (buildMaxHeapList arr).Perm arr

theorem buildMaxHeap_thm (arr : List Nat) : buildMaxHeap_prop arr := by
  refine ⟨?_, buildMaxHeapList_perm arr⟩
  have := buildMaxHeap_isMaxHeap arr.toArray
  rwa [List.size_toArray] at this

/-- Python's `ValueError`: a negative entry is rejected by the checked wrapper. -/
def checked_error_prop (arr : List Int) : Prop := (∃ x ∈ arr, x < 0) → heapsortChecked arr = none

theorem checked_error_thm (arr : List Int) : checked_error_prop arr := heapsortChecked_none arr

/-! ## Post-condition -/

/-- Post-condition of Python `heapsort`: the result is a sorted permutation of the input, of the
same length and with the same multiplicities, hence equal to `sorted(arr)`. -/
def Post_prop (arr : List Nat) : Prop :=
  sorted_prop arr ∧ perm_prop arr ∧ length_prop arr ∧ count_prop arr ∧ eq_sorted_prop arr

/-! ## Property-based tests -/

-- sorted_prop
#eval Plausible.Testable.check (∀ xs : List Nat, List.Sorted (· ≤ ·) (heapsort xs))
-- perm_prop
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).Perm xs)
-- length_prop
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).length = xs.length)
-- count_prop
#eval Plausible.Testable.check (∀ xs : List Nat, ∀ x : Nat, (heapsort xs).count x = xs.count x)
-- eq_sorted_prop
#eval Plausible.Testable.check (∀ xs : List Nat, heapsort xs = xs.mergeSort)
-- buildMaxHeap_prop
#eval Plausible.Testable.check
  (∀ xs : List Nat, IsMaxHeap (buildMaxHeap xs.toArray) xs.length ∧ (buildMaxHeapList xs).Perm xs)
-- checked_error_prop
#eval Plausible.Testable.check
  (∀ xs : List Int, (∃ x ∈ xs, x < 0) → heapsortChecked xs = none)
-- Post_prop (executable conjunction)
#eval Plausible.Testable.check
  (∀ xs : List Nat, List.Sorted (· ≤ ·) (heapsort xs) ∧ (heapsort xs).Perm xs ∧
    (heapsort xs).length = xs.length ∧ (∀ x : Nat, (heapsort xs).count x = xs.count x) ∧
    heapsort xs = xs.mergeSort)
-- bounded exhaustive tests: all 720 permutations of `[0, …, 5]`, and reversed ranges
example : (List.permutations [0, 1, 2, 3, 4, 5]).all
    (fun l => heapsort l == [0, 1, 2, 3, 4, 5]) = true := by native_decide
example : (List.range 40).all (fun n => heapsort (List.range n).reverse == List.range n) = true := by
  native_decide
example : (List.range 40).all
    (fun n => decide (IsMaxHeap (buildMaxHeap (List.range n).toArray) n)) = true := by native_decide

/-! ## Correctness theorem -/

theorem correctness_thm (arr : List Nat) (_hpre : Pre arr) : Post_prop arr :=
  ⟨sorted_thm arr, perm_thm arr, length_thm arr, count_thm arr, eq_sorted_thm arr⟩

/-! ## Imperative implementation -/

/-- Python `max_heapify` as an imperative loop: `while True` is bounded by `heapSize`
iterations (the index strictly increases and stays below `heapSize`), with `break` for `return`. -/
def maxHeapifyImp (arr : Array Nat) (i heapSize : Nat) : Array Nat := Id.run do
  let mut a := arr
  let mut idx := i
  for _ in [0:heapSize] do
    let l := left idx
    let r := right idx
    let mut largest := idx
    if l < heapSize ∧ a[l]! > a[idx]! then
      largest := l
    if r < heapSize ∧ a[r]! > a[largest]! then
      largest := r
    if largest = idx then
      break
    a := a.swapIfInBounds idx largest
    idx := largest
  return a

/-- Python `build_max_heap` with `for i in range(parent(n - 1), -1, -1)`. -/
def buildMaxHeapImp (arr : Array Nat) : Array Nat := Id.run do
  let mut a := arr
  let n := a.size
  if n ≤ 1 then
    return a
  for k in [0:parent (n - 1) + 1] do
    let i := parent (n - 1) - k
    a := maxHeapifyImp a i n
  return a

/-- Python `heapsort` with `for i in range(len(result) - 1, 0, -1)`. -/
def heapsortImp (arr : List Nat) : List Nat := Id.run do
  if arr.length ≤ 1 then
    return arr
  let mut a := buildMaxHeapImp arr.toArray
  let n := a.size
  for k in [0:n - 1] do
    let i := n - 1 - k
    a := a.swapIfInBounds 0 i
    a := maxHeapifyImp a 0 i
  return a.toList

/-! ## Imperative tests -/

example : heapsortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsortImp [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsortImp [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsortImp [] = [] := by native_decide
example : heapsortImp [42] = [42] := by native_decide
example : heapsortImp [2, 1] = [1, 2] := by native_decide
example : heapsortImp [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapsortImp [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsortImp [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : (buildMaxHeapImp #[4, 1, 3, 2, 16, 9, 10, 14, 8, 7]).toList =
    [16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by native_decide
example : (maxHeapifyImp #[16, 4, 10, 14, 7, 9, 3, 2, 8, 1] 1 10).toList =
    [16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by native_decide
#eval heapsortImp [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval Plausible.Testable.check (∀ xs : List Nat, heapsortImp xs = heapsort xs)
#eval Plausible.Testable.check
  (∀ (xs : List Nat) (i : Nat), maxHeapifyImp xs.toArray i xs.length = maxHeapify xs.toArray i xs.length)

/-! ## Equivalence: functional = imperative -/

/-- Generic sift-down loop lemma: a `for`-loop whose body behaves like one iteration of
`max_heapify` computes `maxHeapify`, provided it has at least `hs - idx` iterations available. -/
theorem maxHeapify_loop (hs : Nat)
    (body : Nat → MProd (Array Nat) Nat → Id (ForInStep (MProd (Array Nat) Nat)))
    (hbody : ∀ x a idx, body x ⟨a, idx⟩ =
        if largestOf a idx hs = idx then pure (ForInStep.done ⟨a, idx⟩)
        else pure (ForInStep.yield
          ⟨a.swapIfInBounds idx (largestOf a idx hs), largestOf a idx hs⟩)) :
    ∀ (fuel s : Nat) (a : Array Nat) (idx : Nat), hs - idx ≤ fuel →
      (forIn (m := Id) (List.range' s fuel) (⟨a, idx⟩ : MProd (Array Nat) Nat) body).run.fst =
        maxHeapify a idx hs := by
  intro fuel
  induction fuel with
  | zero =>
    intro s a idx hle
    simp only [List.range'_zero, List.forIn_nil, Id.run_pure]
    rw [maxHeapify, if_pos (largestOf_of_ge a idx hs (by omega))]
  | succ fuel ih =>
    intro s a idx hle
    rw [List.range'_succ, List.forIn_cons, hbody]
    by_cases h : largestOf a idx hs = idx
    · rw [if_pos h]
      simp only [pure_bind, Id.run_pure]
      rw [maxHeapify, if_pos h]
    · rw [if_neg h]
      simp only [pure_bind]
      have hne := largestOf_ne a idx hs h
      rw [ih (s + 1) _ _ (by omega)]
      conv_rhs => rw [maxHeapify]
      rw [if_neg h]

theorem maxHeapifyImp_eq (arr : Array Nat) (i hs : Nat) :
    maxHeapifyImp arr i hs = maxHeapify arr i hs := by
  unfold maxHeapifyImp
  simp only [Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  rw [Id.run_bind]
  simp only [Id.run_pure]
  apply maxHeapify_loop hs _ _ hs 0 arr i (by omega)
  intro x a idx
  simp only [largestOf, left, right, pure_bind]
  split_ifs <;> first | rfl | omega

/-- The build loop `for k in [s:s+m]` with body index `s + m - 1 - k` is `buildLoop`. -/
theorem buildLoop_eq_forIn (n : Nat) : ∀ (m s : Nat) (a : Array Nat),
    (forIn (m := Id) (List.range' s m) a
      (fun k a => pure (ForInStep.yield (maxHeapify a (s + m - 1 - k) n)))).run = buildLoop a n m
  | 0, s, a => by simp only [List.range'_zero, List.forIn_nil, Id.run_pure, buildLoop]
  | m + 1, s, a => by
    rw [List.range'_succ, List.forIn_cons]
    simp only [pure_bind]
    rw [show s + (m + 1) - 1 - s = m by omega, buildLoop, ← buildLoop_eq_forIn n m (s + 1)]
    congr 1
    funext k a
    rw [show s + (m + 1) - 1 - k = s + 1 + m - 1 - k by omega]

/-- The extraction loop `for k in [s:s+m]` with body index `s + m - k` is `extractLoop`. -/
theorem extractLoop_eq_forIn : ∀ (m s : Nat) (a : Array Nat),
    (forIn (m := Id) (List.range' s m) a
      (fun k a => pure (ForInStep.yield
        (maxHeapify (a.swapIfInBounds 0 (s + m - k)) 0 (s + m - k))))).run = extractLoop a m
  | 0, s, a => by simp only [List.range'_zero, List.forIn_nil, Id.run_pure, extractLoop]
  | m + 1, s, a => by
    rw [List.range'_succ, List.forIn_cons]
    simp only [pure_bind]
    rw [show s + (m + 1) - s = m + 1 by omega, extractLoop, ← extractLoop_eq_forIn m (s + 1)]
    congr 1
    funext k a
    rw [show s + (m + 1) - k = s + 1 + m - k by omega]

theorem buildMaxHeapImp_eq (arr : Array Nat) : buildMaxHeapImp arr = buildMaxHeap arr := by
  unfold buildMaxHeapImp buildMaxHeap
  simp only [Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, maxHeapifyImp_eq]
  split_ifs with h
  · rfl
  · rw [Id.run_bind]
    simp only [Id.run_pure]
    have := buildLoop_eq_forIn arr.size (parent (arr.size - 1) + 1) 0 arr
    simp only [Nat.zero_add, Nat.add_sub_cancel] at this
    exact this

theorem heapsortImp_eq (arr : List Nat) : heapsortImp arr = heapsort arr := by
  unfold heapsortImp heapsort heapsortArray
  simp only [Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, maxHeapifyImp_eq, buildMaxHeapImp_eq, List.size_toArray, buildMaxHeap_size]
  split_ifs with h
  · simp
  · rw [Id.run_bind]
    simp only [Id.run_pure]
    have := extractLoop_eq_forIn (arr.length - 1) 0 (buildMaxHeap arr.toArray)
    simp only [Nat.zero_add] at this
    rw [this]

/-- Functional and imperative implementations agree on every input. -/
theorem equiv_thm (arr : List Nat) : heapsortImp arr = heapsort arr := heapsortImp_eq arr

end heapsort_algorithm
