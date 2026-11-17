import Mathlib

/-!
# Heap sort for a list of integers

Lean 4 formalization of the Python program `heap_sort`.

The Python program builds a max-heap from a copy of the input list, then repeatedly
swaps the root (the maximum of the heap) to the end of the heap region and restores
the heap property with `heapify` (a recursive sift-down).  Empty and single-element
lists are returned as copies.  The `ValueError` raised for non-`List[int]` inputs has
no counterpart here: the Lean type `List Int` already enforces the precondition, so
`Pre` is trivially true.

Contents:
* functional implementation (`largestOf`, `heapify`, `buildMaxHeapAux`, `extractAux`,
  `heapSortArray`, `heap_sort`) mirroring the Python code on `Array Int`;
* unit tests taken from the Python `check` function;
* `Pre`, properties (`sorted`, permutation, length, counts, small inputs, agreement with
  insertion sort), `Post_prop`, property-based tests, and the correctness theorem;
* an imperative implementation `heap_sort_imp` (`Id.run do`, mutable state, `for` loops)
  and the proof that it coincides with the functional one.
-/

namespace heap_sort

/-! ## Functional implementation -/

/-- First step of Python's `heapify`: the larger of `i` and its left child (if it exists). -/
def largest1 (a : Array Int) (n i : Nat) : Nat :=
  if 2 * i + 1 < n ∧ a[2 * i + 1]! > a[i]! then 2 * i + 1 else i

/-- The index `largest` computed by Python's `heapify` before the swap test. -/
def largestOf (a : Array Int) (n i : Nat) : Nat :=
  if 2 * i + 2 < n ∧ a[2 * i + 2]! > a[largest1 a n i]! then 2 * i + 2 else largest1 a n i

theorem largestOf_ne (a : Array Int) (n i : Nat) (h : largestOf a n i ≠ i) :
    i < largestOf a n i ∧ largestOf a n i < n := by
  unfold largestOf largest1 at *
  split_ifs at * <;> omega

set_option linter.unusedVariables false in
/-- `heapify(arr, n, i)`: restore the max-heap property of the heap `arr[0:n]` at node `i`
(recursive sift-down), exactly as in the Python code. -/
def heapify (a : Array Int) (n i : Nat) : Array Int :=
  if h : largestOf a n i ≠ i then
    heapify (a.swapIfInBounds i (largestOf a n i)) n (largestOf a n i)
  else a
termination_by n - i
decreasing_by
  have := largestOf_ne a n i h
  omega

/-- `for i in range(k - 1, -1, -1): heapify(arr, n, i)`. -/
def buildMaxHeapAux (a : Array Int) (n : Nat) : Nat → Array Int
  | 0 => a
  | k + 1 => buildMaxHeapAux (heapify a n k) n k

/-- `build_max_heap`: heapify the nodes `n // 2 - 1, …, 0`. -/
def buildMaxHeap (a : Array Int) : Array Int :=
  buildMaxHeapAux a a.size (a.size / 2)

/-- `for i in range(k, 0, -1): swap(result[0], result[i]); heapify(result, i, 0)`. -/
def extractAux (a : Array Int) : Nat → Array Int
  | 0 => a
  | k + 1 => extractAux (heapify (a.swapIfInBounds 0 (k + 1)) (k + 1) 0) k

/-- Heap sort of an array: build the max-heap, then extract the maxima one by one. -/
def heapSortArray (a : Array Int) : Array Int :=
  extractAux (buildMaxHeap a) (a.size - 1)

set_option linter.dupNamespace false in
/-- `heap_sort`: lists of length `≤ 1` are returned unchanged (Python returns a copy),
otherwise the array-based heap sort is run on a copy of the input. -/
def heap_sort (arr : List Int) : List Int :=
  if arr.length ≤ 1 then arr else (heapSortArray arr.toArray).toList

/-! ## Unit tests (from the Python `check` function) -/

example : heap_sort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heap_sort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heap_sort [2, 1, 3] = [1, 2, 3] := by native_decide
example : heap_sort [] = [] := by native_decide
example : heap_sort [1] = [1] := by native_decide
example : heap_sort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heap_sort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heap_sort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heap_sort [2, 1] = [1, 2] := by native_decide
example : heap_sort [1, 2] = [1, 2] := by native_decide
example : heap_sort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : heap_sort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : heap_sort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heap_sort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : heap_sort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heap_sort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
-- negative numbers (Python `int` is unbounded, as is Lean's `Int`)
example : heap_sort [-3, 5, -10, 0, 2] = [-10, -3, 0, 2, 5] := by native_decide
-- The Python negative test `candidate([1, 2.5])` raises `ValueError`; it is not expressible
-- here because `List Int` already rules out non-integer elements.

#eval heap_sort [3, 1, 2]
#eval heap_sort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
#eval heap_sort [3, 1, 4, 1, 2, 3]
#eval heap_sort ([] : List Int)

/-! ## Pre-condition -/

/-- Python's `pre` checks that the input is a `list` of `int`s; the Lean type `List Int`
already guarantees this, so every input is admissible. -/
def Pre (_arr : List Int) : Prop := True

/-! ## Heap invariants and the proof that `heapify` works -/

/-- `a[0:n]` satisfies the max-heap property at every node whose parent index is `≥ k`
(so `HeapFrom a n 0` is the full max-heap property of `a[0:n]`). -/
def HeapFrom (a : Array Int) (n k : Nat) : Prop :=
  ∀ j, 0 < j → j < n → k ≤ (j - 1) / 2 → a[j]! ≤ a[(j - 1) / 2]!

/-- The region of `a[0:n]` with parents `≥ k` is a max-heap except possibly at node `i`
(whose children may be larger than it), and if `i` has a parent in the region then the
children of `i` are bounded by the parent of `i`. -/
def HeapExceptFrom (a : Array Int) (n k i : Nat) : Prop :=
  (∀ j, 0 < j → j < n → k ≤ (j - 1) / 2 → (j - 1) / 2 ≠ i → a[j]! ≤ a[(j - 1) / 2]!) ∧
  (0 < i → k ≤ (i - 1) / 2 → ∀ j, 0 < j → j < n → (j - 1) / 2 = i → a[j]! ≤ a[(i - 1) / 2]!)

theorem largestOf_spec (a : Array Int) (n i : Nat) :
    i ≤ largestOf a n i ∧
    (largestOf a n i ≠ i →
      largestOf a n i < n ∧ (largestOf a n i = 2 * i + 1 ∨ largestOf a n i = 2 * i + 2)) ∧
    a[i]! ≤ a[largestOf a n i]! ∧
    (2 * i + 1 < n → a[2 * i + 1]! ≤ a[largestOf a n i]!) ∧
    (2 * i + 2 < n → a[2 * i + 2]! ≤ a[largestOf a n i]!) := by
  unfold largestOf largest1
  split_ifs <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> omega

theorem getElem!_swapIfInBounds (a : Array Int) (i c j : Nat) (hi : i < a.size) (hc : c < a.size) :
    (a.swapIfInBounds i c)[j]! = if j = i then a[c]! else if j = c then a[i]! else a[j]! := by
  unfold Array.swapIfInBounds
  rw [dif_pos hi, dif_pos hc]
  by_cases hj : j < a.size
  · have hj' : j < (a.swap i c hi hc).size := by simpa using hj
    rw [getElem!_pos (a.swap i c hi hc) j hj', Array.getElem_swap, getElem!_pos a i hi,
      getElem!_pos a c hc, getElem!_pos a j hj]
  · have hj' : ¬ j < (a.swap i c hi hc).size := by simpa using hj
    rw [getElem!_neg (a.swap i c hi hc) j hj', getElem!_neg a j hj]
    have h1 : j ≠ i := by omega
    have h2 : j ≠ c := by omega
    simp [h1, h2]

theorem swapIfInBounds_perm (a : Array Int) (i c : Nat) (hi : i < a.size) (hc : c < a.size) :
    (a.swapIfInBounds i c).toList.Perm a.toList := by
  unfold Array.swapIfInBounds
  rw [dif_pos hi, dif_pos hc]
  exact Array.perm_iff_toList_perm.mp (Array.swap_perm hi hc)

theorem heapify_size (a : Array Int) (n i : Nat) : (heapify a n i).size = a.size := by
  induction a, i using heapify.induct n with
  | case1 a i h ih => rw [heapify, dif_pos h, ih, Array.size_swapIfInBounds]
  | case2 a i h => rw [heapify, dif_neg h]

theorem heapify_perm (n : Nat) :
    ∀ (a : Array Int) (i : Nat), n ≤ a.size → (heapify a n i).toList.Perm a.toList := by
  intro a i
  induction a, i using heapify.induct n with
  | case1 a i hne ih =>
    intro hn
    rw [heapify, dif_pos hne]
    have hlt := largestOf_ne a n i hne
    exact (ih (by rw [Array.size_swapIfInBounds]; exact hn)).trans
      (swapIfInBounds_perm a i _ (by omega) (by omega))
  | case2 a i hne =>
    intro _
    rw [heapify, dif_neg hne]

/-- `heapify` does not touch the entries outside the heap region `[0, n)`. -/
theorem heapify_getElem!_of_ge (n : Nat) :
    ∀ (a : Array Int) (i j : Nat), n ≤ a.size → n ≤ j → (heapify a n i)[j]! = a[j]! := by
  intro a i
  induction a, i using heapify.induct n with
  | case1 a i hne ih =>
    intro j hn hj
    rw [heapify, dif_pos hne]
    have hlt := largestOf_ne a n i hne
    have hi : i < a.size := by omega
    have hc : largestOf a n i < a.size := by omega
    rw [ih j (by rw [Array.size_swapIfInBounds]; exact hn) hj,
      getElem!_swapIfInBounds a i _ j hi hc, if_neg (by omega), if_neg (by omega)]
  | case2 a i hne =>
    intro j _ _
    rw [heapify, dif_neg hne]

/-- Inside the heap region, `heapify` only permutes entries. -/
theorem heapify_getElem!_of_lt (n : Nat) :
    ∀ (a : Array Int) (i j : Nat), n ≤ a.size → j < n →
      ∃ j', j' < n ∧ (heapify a n i)[j]! = a[j']! := by
  intro a i
  induction a, i using heapify.induct n with
  | case1 a i hne ih =>
    intro j hn hj
    rw [heapify, dif_pos hne]
    have hlt := largestOf_ne a n i hne
    have hi : i < a.size := by omega
    have hc : largestOf a n i < a.size := by omega
    obtain ⟨j', hj', e⟩ := ih j (by rw [Array.size_swapIfInBounds]; exact hn) hj
    rw [e, getElem!_swapIfInBounds a i _ j' hi hc]
    split_ifs
    · exact ⟨_, hlt.2, rfl⟩
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨j', hj', rfl⟩
  | case2 a i hne =>
    intro j _ hj
    rw [heapify, dif_neg hne]
    exact ⟨j, hj, rfl⟩

/-- The main lemma about sift-down: it turns a "heap except at `i`" into a heap. -/
theorem heapify_heapFrom (n k : Nat) :
    ∀ (a : Array Int) (i : Nat), n ≤ a.size → k ≤ i →
      HeapExceptFrom a n k i → HeapFrom (heapify a n i) n k := by
  intro a i
  induction a, i using heapify.induct n with
  | case1 a i hne ih =>
    intro hn hki h
    rw [heapify, dif_pos hne]
    obtain ⟨_, hlt, hself, hleft, hright⟩ := largestOf_spec a n i
    obtain ⟨hmn, hcases⟩ := hlt hne
    have hi : i < a.size := by omega
    have hc : largestOf a n i < a.size := by omega
    have hmi : (largestOf a n i - 1) / 2 = i := by omega
    apply ih
    · rw [Array.size_swapIfInBounds]; exact hn
    · omega
    · constructor
      · intro j hj0 hjn hkj hpm
        rw [getElem!_swapIfInBounds a i _ j hi hc, getElem!_swapIfInBounds a i _ ((j - 1) / 2) hi hc]
        by_cases e1 : j = i
        · have hp1 : (j - 1) / 2 ≠ i := by omega
          rw [if_pos e1, if_neg hp1, if_neg hpm]
          have := h.2 (by omega) (by rw [← e1]; exact hkj) (largestOf a n i) (by omega) hmn hmi
          rw [e1]; exact this
        · by_cases e2 : j = largestOf a n i
          · have hp2 : (j - 1) / 2 = i := by omega
            rw [if_neg e1, if_pos e2, if_pos hp2]
            exact hself
          · rw [if_neg e1, if_neg e2]
            by_cases e3 : (j - 1) / 2 = i
            · rw [if_pos e3]
              have : j = 2 * i + 1 ∨ j = 2 * i + 2 := by omega
              rcases this with e | e
              · rw [e]; exact hleft (by omega)
              · rw [e]; exact hright (by omega)
            · rw [if_neg e3, if_neg hpm]
              exact h.1 j hj0 hjn hkj e3
      · intro _ _ j hj0 hjn hpj
        rw [hmi, getElem!_swapIfInBounds a i _ j hi hc, getElem!_swapIfInBounds a i _ i hi hc]
        have e1 : j ≠ i := by omega
        have e2 : j ≠ largestOf a n i := by omega
        rw [if_neg e1, if_neg e2, if_pos rfl]
        have := h.1 j hj0 hjn (by omega) (by omega)
        rw [hpj] at this
        exact this
  | case2 a i hne =>
    intro _ _ h
    rw [heapify, dif_neg hne]
    push_neg at hne
    intro j hj0 hjn hkj
    by_cases hp : (j - 1) / 2 = i
    · obtain ⟨-, -, -, hleft, hright⟩ := largestOf_spec a n i
      rw [hne] at hleft hright
      have : j = 2 * i + 1 ∨ j = 2 * i + 2 := by omega
      rw [hp]
      rcases this with e | e
      · rw [e]; exact hleft (by omega)
      · rw [e]; exact hright (by omega)
    · exact h.1 j hj0 hjn hkj hp

theorem buildMaxHeapAux_size (n : Nat) :
    ∀ (k : Nat) (a : Array Int), (buildMaxHeapAux a n k).size = a.size := by
  intro k
  induction k with
  | zero => intro a; rfl
  | succ k ih => intro a; rw [buildMaxHeapAux, ih, heapify_size]

theorem buildMaxHeapAux_perm (n : Nat) :
    ∀ (k : Nat) (a : Array Int), n ≤ a.size → (buildMaxHeapAux a n k).toList.Perm a.toList := by
  intro k
  induction k with
  | zero => intro a _; exact List.Perm.refl _
  | succ k ih =>
    intro a hn
    rw [buildMaxHeapAux]
    exact (ih _ (by rw [heapify_size]; exact hn)).trans (heapify_perm n a k hn)

theorem buildMaxHeapAux_heapFrom (n : Nat) :
    ∀ (k : Nat) (a : Array Int), n ≤ a.size → HeapFrom a n k →
      HeapFrom (buildMaxHeapAux a n k) n 0 := by
  intro k
  induction k with
  | zero => intro a _ h; exact h
  | succ k ih =>
    intro a hn h
    rw [buildMaxHeapAux]
    apply ih
    · rw [heapify_size]; exact hn
    · apply heapify_heapFrom n k a k hn le_rfl
      constructor
      · intro j hj0 hjn hkj hpk
        exact h j hj0 hjn (by omega)
      · intro hk0 hkk
        exfalso
        omega

theorem buildMaxHeap_size (a : Array Int) : (buildMaxHeap a).size = a.size :=
  buildMaxHeapAux_size _ _ _

theorem buildMaxHeap_perm (a : Array Int) : (buildMaxHeap a).toList.Perm a.toList :=
  buildMaxHeapAux_perm _ _ _ le_rfl

/-- After `build_max_heap`, the whole array is a max-heap. -/
theorem buildMaxHeap_heapFrom (a : Array Int) : HeapFrom (buildMaxHeap a) a.size 0 := by
  apply buildMaxHeapAux_heapFrom a.size (a.size / 2) a le_rfl
  intro j _ hjn hkj
  exfalso
  omega

/-- The root of a max-heap is its maximum. -/
theorem heapFrom_zero_le (a : Array Int) (n : Nat) (h : HeapFrom a n 0) :
    ∀ j, j < n → a[j]! ≤ a[0]! := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjn
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; exact le_rfl
    · calc a[j]! ≤ a[(j - 1) / 2]! := h j hj hjn (Nat.zero_le _)
        _ ≤ a[0]! := ih ((j - 1) / 2) (by omega) (by omega)

/-- Every entry of `a[m:n]` dominates all entries before it (so `a[m:n]` is sorted and
bounds `a[0:m]`). -/
def SuffixSorted (a : Array Int) (n m : Nat) : Prop :=
  ∀ j, m ≤ j → j < n → ∀ j', j' < j → a[j']! ≤ a[j]!

theorem extractAux_size : ∀ (k : Nat) (a : Array Int), (extractAux a k).size = a.size := by
  intro k
  induction k with
  | zero => intro a; rfl
  | succ k ih => intro a; rw [extractAux, ih, heapify_size, Array.size_swapIfInBounds]

theorem extractAux_perm : ∀ (k : Nat) (a : Array Int), k < a.size →
    (extractAux a k).toList.Perm a.toList := by
  intro k
  induction k with
  | zero => intro a _; exact List.Perm.refl _
  | succ k ih =>
    intro a hk
    rw [extractAux]
    have h0 : 0 < a.size := by omega
    refine (ih _ ?_).trans ((heapify_perm (k + 1) _ 0 ?_).trans (swapIfInBounds_perm a 0 (k + 1) h0 hk))
    · rw [heapify_size, Array.size_swapIfInBounds]; omega
    · rw [Array.size_swapIfInBounds]; omega

/-- The extraction loop invariant: heap of size `k + 1` plus a dominating sorted suffix. -/
theorem extractAux_sorted (n : Nat) :
    ∀ (k : Nat) (a : Array Int), n = a.size → k < n →
      HeapFrom a (k + 1) 0 → SuffixSorted a n (k + 1) → SuffixSorted (extractAux a k) n 0 := by
  intro k
  induction k with
  | zero =>
    intro a _ _ _ hsuf
    intro j _ hjn j' hj'
    exact hsuf j (by omega) hjn j' hj'
  | succ k ih =>
    intro a hn hk hheap hsuf
    rw [extractAux]
    have h0 : 0 < a.size := by omega
    have hk1 : k + 1 < a.size := by omega
    have hmax := heapFrom_zero_le a (k + 2) hheap
    have hsz : k + 1 ≤ (a.swapIfInBounds 0 (k + 1)).size := by
      rw [Array.size_swapIfInBounds]; omega
    -- after the swap, the suffix `[k+1, n)` dominates everything before it
    have hsuf' : SuffixSorted (a.swapIfInBounds 0 (k + 1)) n (k + 1) := by
      intro j hj hjn j' hj'
      rw [getElem!_swapIfInBounds a 0 (k + 1) j h0 hk1, getElem!_swapIfInBounds a 0 (k + 1) j' h0 hk1]
      by_cases ej : j = k + 1
      · rw [if_neg (show ¬ j = 0 by omega), if_pos ej]
        by_cases ej' : j' = 0
        · rw [if_pos ej']; exact hmax (k + 1) (by omega)
        · rw [if_neg ej', if_neg (show ¬ j' = k + 1 by omega)]; exact hmax j' (by omega)
      · rw [if_neg (show ¬ j = 0 by omega), if_neg ej]
        by_cases ej' : j' = 0
        · rw [if_pos ej']; exact hsuf j (by omega) hjn (k + 1) (by omega)
        · rw [if_neg ej']
          by_cases ej'' : j' = k + 1
          · rw [if_pos ej'']; exact hsuf j (by omega) hjn 0 (by omega)
          · rw [if_neg ej'']; exact hsuf j (by omega) hjn j' hj'
    -- the heap of size `k+1` is restored by `heapify`
    have hheap' : HeapFrom (heapify (a.swapIfInBounds 0 (k + 1)) (k + 1) 0) (k + 1) 0 := by
      apply heapify_heapFrom (k + 1) 0 _ 0 hsz le_rfl
      constructor
      · intro j hj0 hjn _ hp
        rw [getElem!_swapIfInBounds a 0 (k + 1) j h0 hk1,
          getElem!_swapIfInBounds a 0 (k + 1) ((j - 1) / 2) h0 hk1,
          if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j = k + 1 by omega), if_neg hp,
          if_neg (show ¬ (j - 1) / 2 = k + 1 by omega)]
        exact hheap j hj0 (by omega) (Nat.zero_le _)
      · intro h; exact absurd h (lt_irrefl 0)
    apply ih
    · rw [heapify_size, Array.size_swapIfInBounds]; exact hn
    · omega
    · exact hheap'
    · intro j hj hjn j' hj'
      rw [heapify_getElem!_of_ge (k + 1) _ 0 j hsz hj]
      by_cases hj'k : j' < k + 1
      · obtain ⟨j'', hj'', e⟩ := heapify_getElem!_of_lt (k + 1) _ 0 j' hsz hj'k
        rw [e]
        exact hsuf' j hj hjn j'' (by omega)
      · rw [heapify_getElem!_of_ge (k + 1) _ 0 j' hsz (by omega)]
        exact hsuf' j hj hjn j' hj'

theorem heapSortArray_size (a : Array Int) : (heapSortArray a).size = a.size := by
  rw [heapSortArray, extractAux_size, buildMaxHeap_size]

theorem heapSortArray_perm (a : Array Int) : (heapSortArray a).toList.Perm a.toList := by
  rw [heapSortArray]
  rcases Nat.eq_zero_or_pos a.size with h0 | hpos
  · rw [h0]
    exact buildMaxHeap_perm a
  · exact (extractAux_perm _ _ (by rw [buildMaxHeap_size]; omega)).trans (buildMaxHeap_perm a)

theorem heapSortArray_suffixSorted (a : Array Int) : SuffixSorted (heapSortArray a) a.size 0 := by
  rw [heapSortArray]
  rcases Nat.eq_zero_or_pos a.size with h0 | hpos
  · intro j _ hjn
    exfalso
    omega
  · apply extractAux_sorted a.size (a.size - 1) (buildMaxHeap a) (buildMaxHeap_size a).symm
      (by omega)
    · have := buildMaxHeap_heapFrom a
      rwa [show a.size - 1 + 1 = a.size by omega]
    · intro j hj hjn
      exfalso
      omega

theorem heapSortArray_sorted (a : Array Int) : List.Sorted (· ≤ ·) (heapSortArray a).toList := by
  rw [List.Sorted, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < (heapSortArray a).size := by simpa using hi
  have hj' : j < (heapSortArray a).size := by simpa using hj
  have h := heapSortArray_suffixSorted a j (Nat.zero_le _) (by rw [← heapSortArray_size]; exact hj') i hij
  rw [getElem!_pos _ i hi', getElem!_pos _ j hj'] at h
  simpa [Array.getElem_toList] using h

/-! ## Properties -/

/-- The output is sorted in non-decreasing order. -/
def sorted_prop (arr : List Int) : Prop := List.Sorted (· ≤ ·) (heap_sort arr)

theorem sorted_thm (arr : List Int) : sorted_prop arr := by
  unfold sorted_prop heap_sort
  split_ifs with h
  · rcases arr with _ | ⟨x, _ | ⟨y, t⟩⟩
    · exact List.sorted_nil
    · exact List.sorted_singleton x
    · simp at h
  · exact heapSortArray_sorted _

/-- The output is a permutation of the input. -/
def perm_prop (arr : List Int) : Prop := (heap_sort arr).Perm arr

theorem perm_thm (arr : List Int) : perm_prop arr := by
  unfold perm_prop heap_sort
  split_ifs with h
  · exact List.Perm.refl _
  · simpa using heapSortArray_perm arr.toArray

/-- The output has the same length as the input. -/
def length_prop (arr : List Int) : Prop := (heap_sort arr).length = arr.length

theorem length_thm (arr : List Int) : length_prop arr :=
  (perm_thm arr).length_eq

/-- Every value occurs in the output exactly as often as in the input. -/
def count_prop (arr : List Int) : Prop := ∀ x : Int, (heap_sort arr).count x = arr.count x

theorem count_thm (arr : List Int) : count_prop arr :=
  fun x => (perm_thm arr).count_eq x

/-- Edge case from the docstring: empty or single-element lists come back unchanged. -/
def small_prop (arr : List Int) : Prop := arr.length ≤ 1 → heap_sort arr = arr

theorem small_thm (arr : List Int) : small_prop arr := by
  intro h
  unfold heap_sort
  rw [if_pos h]

/-- Heap sort agrees with insertion sort (the sorted permutation of a list is unique). -/
def canonical_prop (arr : List Int) : Prop := heap_sort arr = arr.insertionSort (· ≤ ·)

theorem canonical_thm (arr : List Int) : canonical_prop arr :=
  List.eq_of_perm_of_sorted ((perm_thm arr).trans (List.perm_insertionSort (· ≤ ·) arr).symm)
    (sorted_thm arr) (List.sorted_insertionSort (· ≤ ·) arr)

/-! ## Post-condition -/

/-- The post-condition of `heap_sort`: the conjunction of all properties above. -/
def Post_prop (arr : List Int) : Prop :=
  sorted_prop arr ∧ perm_prop arr ∧ length_prop arr ∧ count_prop arr ∧ small_prop arr ∧
    canonical_prop arr

/-! ## Property-based tests -/

-- sorted_prop
#eval Plausible.Testable.check (∀ xs : List Int, List.Sorted (· ≤ ·) (heap_sort xs))
-- perm_prop
#eval Plausible.Testable.check (∀ xs : List Int, (heap_sort xs).Perm xs)
-- length_prop
#eval Plausible.Testable.check (∀ xs : List Int, (heap_sort xs).length = xs.length)
-- count_prop
#eval Plausible.Testable.check (∀ (xs : List Int) (x : Int), (heap_sort xs).count x = xs.count x)
-- small_prop (executable form of the implication, plus the admissible inputs themselves)
#eval Plausible.Testable.check (∀ xs : List Int, 1 < xs.length ∨ heap_sort xs = xs)
#eval Plausible.Testable.check (∀ x : Int, heap_sort [] = [] ∧ heap_sort [x] = [x])
-- canonical_prop
#eval Plausible.Testable.check (∀ xs : List Int, heap_sort xs = xs.insertionSort (· ≤ ·))
-- Post_prop (executable form of the conjunction)
#eval Plausible.Testable.check (∀ xs : List Int,
  List.Sorted (· ≤ ·) (heap_sort xs) ∧ (heap_sort xs).Perm xs ∧
    (heap_sort xs).length = xs.length ∧
    xs.all (fun x => (heap_sort xs).count x == xs.count x) = true ∧
    (1 < xs.length ∨ heap_sort xs = xs) ∧ heap_sort xs = xs.insertionSort (· ≤ ·))

-- bounded / exhaustive PBTs: all permutations of small lists, and all lists over `{0,1,2}`
-- of length ≤ 5
example : ([1, 2, 3, 4, 5, 6].permutations).all
    (fun l => heap_sort l == [1, 2, 3, 4, 5, 6]) = true := by native_decide
example : ([3, 1, 4, 1, 5].permutations).all
    (fun l => heap_sort l == [1, 1, 3, 4, 5]) = true := by native_decide
example : ((List.range 6).flatMap fun k =>
    (List.replicate k [0, 1, 2]).foldr (fun c acc => c.flatMap fun x => acc.map (x :: ·)) [[]]).all
    (fun l => decide (List.Sorted (· ≤ ·) (heap_sort l)) && decide ((heap_sort l).Perm l) &&
      ((heap_sort l).length == l.length) &&
      (decide (l.length ≤ 1) → heap_sort l == l) &&
      (heap_sort l == l.insertionSort (· ≤ ·))) = true := by native_decide
-- small_prop on all lists of length ≤ 1 from a window of integers
example : (([] : List Int) :: (List.range 41).map (fun k => [(k : Int) - 20])).all
    (fun l => heap_sort l == l) = true := by native_decide

/-! ## Correctness theorem -/

theorem heap_sort_correct (arr : List Int) (_h : Pre arr) : Post_prop arr :=
  ⟨sorted_thm arr, perm_thm arr, length_thm arr, count_thm arr, small_thm arr, canonical_thm arr⟩

/-! ## Imperative implementation -/

set_option linter.unusedVariables false in
/-- Imperative `heapify`, following the Python code line by line: `largest` is rebound
(immutably, so that the termination proof can see how it was computed) and the
recursive call is an early `return`. -/
def heapifyImp (arr : Array Int) (n i : Nat) : Array Int := Id.run do
  let left := 2 * i + 1
  let right := 2 * i + 2
  let largest0 := if left < n ∧ arr[left]! > arr[i]! then left else i
  let largest := if right < n ∧ arr[right]! > arr[largest0]! then right else largest0
  if h : largest ≠ i then
    let arr' := arr.swapIfInBounds i largest
    return heapifyImp arr' n largest
  return arr
termination_by n - i
decreasing_by
  simp only [largest, largest0, left, right] at h
  split_ifs at * <;> omega

/-- Imperative heap sort with mutable state and `for` loops, mirroring the Python program:
early return for short lists, `build_max_heap`, then the extraction loop. -/
def heap_sort_imp (arr : List Int) : List Int := Id.run do
  if arr.length ≤ 1 then
    return arr
  let mut result := arr.toArray
  let n := result.size
  -- build max heap: `for i in range(n // 2 - 1, -1, -1): heapify(result, n, i)`
  for t in [0 : n / 2] do
    let i := n / 2 - 1 - t
    result := heapifyImp result n i
  -- extract elements one by one: `for i in range(n - 1, 0, -1)`
  for t in [0 : n - 1] do
    let i := n - 1 - t
    result := result.swapIfInBounds 0 i
    result := heapifyImp result i 0
  return result.toList

/-! ## Imperative tests -/

example : heap_sort_imp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heap_sort_imp [1, 2, 3] = [1, 2, 3] := by native_decide
example : heap_sort_imp [2, 1, 3] = [1, 2, 3] := by native_decide
example : heap_sort_imp [] = [] := by native_decide
example : heap_sort_imp [1] = [1] := by native_decide
example : heap_sort_imp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heap_sort_imp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heap_sort_imp [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heap_sort_imp [2, 1] = [1, 2] := by native_decide
example : heap_sort_imp [1, 2] = [1, 2] := by native_decide
example : heap_sort_imp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : heap_sort_imp [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : heap_sort_imp [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heap_sort_imp [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : heap_sort_imp [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heap_sort_imp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

#eval heap_sort_imp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
#eval Plausible.Testable.check (∀ xs : List Int, heap_sort_imp xs = heap_sort xs)

/-! ## Equivalence of the two implementations -/

theorem heapifyImp_eq_heapify (n : Nat) :
    ∀ (a : Array Int) (i : Nat), heapifyImp a n i = heapify a n i := by
  intro a i
  induction a, i using heapify.induct n with
  | case1 a i hne ih =>
    rw [heapifyImp, heapify, dif_pos hne]
    simp only [Id.run, bind, pure, dite_eq_ite]
    change (if largestOf a n i ≠ i then
      heapifyImp (a.swapIfInBounds i (largestOf a n i)) n (largestOf a n i) else a) = _
    rw [if_pos hne, ih]
  | case2 a i hne =>
    rw [heapifyImp, heapify, dif_neg hne]
    simp only [Id.run, bind, pure, dite_eq_ite]
    change (if largestOf a n i ≠ i then
      heapifyImp (a.swapIfInBounds i (largestOf a n i)) n (largestOf a n i) else a) = _
    rw [if_neg hne]

theorem forIn_range'_build (n N : Nat) :
    ∀ (c s : Nat) (acc : Array Int), s + c = N →
      (forIn (m := Id) (List.range' s c) acc
        fun t r => ForInStep.yield (heapify r n (N - 1 - t))) = buildMaxHeapAux acc n c := by
  intro c
  induction c with
  | zero => intro s acc _; rfl
  | succ c ih =>
    intro s acc hs
    rw [List.range'_succ, List.forIn_cons]
    simp only [bind]
    rw [ih (s + 1) _ (by omega), buildMaxHeapAux, show N - 1 - s = c by omega]

theorem forIn_range'_extract (N : Nat) :
    ∀ (c s : Nat) (acc : Array Int), s + c = N →
      (forIn (m := Id) (List.range' s c) acc
        fun t r => ForInStep.yield (heapify (r.swapIfInBounds 0 (N - t)) (N - t) 0)) =
        extractAux acc c := by
  intro c
  induction c with
  | zero => intro s acc _; rfl
  | succ c ih =>
    intro s acc hs
    rw [List.range'_succ, List.forIn_cons]
    simp only [bind]
    rw [ih (s + 1) _ (by omega), extractAux, show N - s = c + 1 by omega]

theorem forIn_range_build (n N : Nat) (acc : Array Int) :
    (forIn (m := Id) [0:N] acc fun t r => ForInStep.yield (heapify r n (N - 1 - t))) =
      buildMaxHeapAux acc n N := by
  rw [Std.Range.forIn_eq_forIn_range']
  have hsz : ([0:N] : Std.Range).size = N := by simp [Std.Range.size]
  rw [hsz]
  exact forIn_range'_build n N N 0 acc (by omega)

theorem forIn_range_extract (N : Nat) (acc : Array Int) :
    (forIn (m := Id) [0:N] acc
      fun t r => ForInStep.yield (heapify (r.swapIfInBounds 0 (N - t)) (N - t) 0)) =
      extractAux acc N := by
  rw [Std.Range.forIn_eq_forIn_range']
  have hsz : ([0:N] : Std.Range).size = N := by simp [Std.Range.size]
  rw [hsz]
  exact forIn_range'_extract N N 0 acc (by omega)

/-- The imperative implementation computes the same function as the functional one. -/
theorem heap_sort_imp_eq_heap_sort (arr : List Int) : heap_sort_imp arr = heap_sort arr := by
  unfold heap_sort_imp heap_sort
  simp only [Id.run, bind, pure, heapifyImp_eq_heapify, List.size_toArray]
  split_ifs with h
  · rfl
  · rw [heapSortArray, buildMaxHeap, List.size_toArray, forIn_range_build, forIn_range_extract]

end heap_sort
