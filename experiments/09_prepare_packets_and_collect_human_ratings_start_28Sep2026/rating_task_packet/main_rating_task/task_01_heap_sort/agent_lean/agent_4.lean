import Mathlib

/-!
# Heap sort

Lean 4 formalization of the Python program `heap_sort.py`.

The Python program sorts a list of integers with heap sort: it builds a max heap
(array encoded, the children of node `i` are `2*i+1` and `2*i+2`), then repeatedly
swaps the root with the last element of the heap and restores the heap property on
the shrunken heap with `heapify`.

* The Python precondition `pre` only checks that the input is a `list` of `int`s;
  in Lean this is guaranteed by the type `List Int`, so `Pre` is trivially `True`.
* Lists with at most one element are returned unchanged (Python returns a copy).

We give an array based functional implementation (`heapSort`) mirroring the Python
algorithm step by step, prove that its output is a sorted permutation of the input,
and give an imperative implementation (`heapSortImp`) using `Id.run do` with mutable
state and `for` loops, proved equal to the functional one.
-/

namespace heap_sort

/-! ## Functional implementation -/

/-- Index of the parent of node `j` in the array-encoded binary heap. -/
def parent (j : Nat) : Nat := (j - 1) / 2

/-- The index `largest` computed by Python's `heapify` before the swap: `i` itself, or
a child of `i` (inside the heap of size `n`) holding a strictly larger value. -/
def largestIdx (a : Array Int) (n i : Nat) : Nat :=
  let l := 2 * i + 1
  let r := 2 * i + 2
  let c1 := if l < n ∧ a[i]! < a[l]! then l else i
  if r < n ∧ a[c1]! < a[r]! then r else c1

set_option linter.unusedVariables false in
/-- `heapify a n i`: sift the element at `i` down the (max) heap of size `n`
(Python's recursive `heapify(arr, n, i)`). -/
def heapify (a : Array Int) (n i : Nat) : Array Int :=
  if h : i < largestIdx a n i ∧ largestIdx a n i < n then
    heapify (a.swapIfInBounds i (largestIdx a n i)) n (largestIdx a n i)
  else a
termination_by n - i
decreasing_by exact Nat.sub_lt_sub_left (Nat.lt_trans h.1 h.2) h.1

/-- `buildLoop a n k` runs `heapify a n i` for `i = k-1, k-2, ..., 0`
(Python's `build_max_heap` uses `k = n // 2`). -/
def buildLoop (a : Array Int) (n : Nat) : Nat → Array Int
  | 0 => a
  | k + 1 => buildLoop (heapify a n k) n k

/-- `extractLoop a k` runs, for `i = k, k-1, ..., 1`: swap `a[0]` with `a[i]`,
then `heapify a i 0` (Python's extraction loop uses `k = n - 1`). -/
def extractLoop (a : Array Int) : Nat → Array Int
  | 0 => a
  | k + 1 => extractLoop (heapify (a.swapIfInBounds 0 (k + 1)) (k + 1) 0) k

/-- Heap sort on arrays: build a max heap, then extract the maxima one by one. -/
def heapSortArray (a : Array Int) : Array Int :=
  extractLoop (buildLoop a a.size (a.size / 2)) (a.size - 1)

/-- Heap sort on lists (the Python `heap_sort`). -/
def heapSort (xs : List Int) : List Int :=
  if xs.length ≤ 1 then xs else (heapSortArray xs.toArray).toList

/-! ## Unit tests -/

example : heapSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : heapSort [] = [] := by native_decide
example : heapSort [1] = [1] := by native_decide
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
example : heapSort [-3, 7, -1, 0, 7, -3] = [-3, -3, -1, 0, 7, 7] := by native_decide

#eval heapSort [3, 1, 2]
#eval heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

/-! ## Auxiliary lemmas: swaps, `largestIdx` -/

theorem getElem!_swapIfInBounds (a : Array Int) {i j : Nat} (hi : i < a.size) (hj : j < a.size)
    (k : Nat) :
    (a.swapIfInBounds i j)[k]! = if k = i then a[j]! else if k = j then a[i]! else a[k]! := by
  unfold Array.swapIfInBounds
  rw [dif_pos hi, dif_pos hj]
  by_cases hk : k < a.size
  · rw [getElem!_pos (a.swap i j hi hj) k (by simpa using hk), Array.getElem_swap]
    rw [getElem!_pos a j hj, getElem!_pos a i hi, getElem!_pos a k hk]
  · have hki : k ≠ i := by omega
    have hkj : k ≠ j := by omega
    rw [if_neg hki, if_neg hkj, getElem!_neg (a.swap i j hi hj) k (by simpa using hk),
      getElem!_neg a k hk]

theorem swapIfInBounds_perm (a : Array Int) (i j : Nat) :
    (a.swapIfInBounds i j).toList.Perm a.toList := by
  unfold Array.swapIfInBounds
  split
  · split
    · exact Array.perm_iff_toList_perm.mp (Array.swap_perm ‹_› ‹_›)
    · exact List.Perm.refl _
  · exact List.Perm.refl _

theorem largestIdx_cases (a : Array Int) (n i : Nat) :
    largestIdx a n i = i ∨ (largestIdx a n i = 2 * i + 1 ∧ 2 * i + 1 < n) ∨
      (largestIdx a n i = 2 * i + 2 ∧ 2 * i + 2 < n) := by
  simp only [largestIdx]
  split_ifs <;> omega

theorem le_largestIdx_self (a : Array Int) (n i : Nat) : a[i]! ≤ a[largestIdx a n i]! := by
  simp only [largestIdx]
  split_ifs <;> omega

theorem le_largestIdx_left (a : Array Int) (n i : Nat) (h : 2 * i + 1 < n) :
    a[2 * i + 1]! ≤ a[largestIdx a n i]! := by
  simp only [largestIdx]
  split_ifs <;> omega

theorem le_largestIdx_right (a : Array Int) (n i : Nat) (h : 2 * i + 2 < n) :
    a[2 * i + 2]! ≤ a[largestIdx a n i]! := by
  simp only [largestIdx]
  split_ifs <;> omega

theorem largestIdx_lt_of_ne (a : Array Int) (n i : Nat) (h : largestIdx a n i ≠ i) :
    i < largestIdx a n i ∧ largestIdx a n i < n := by
  rcases largestIdx_cases a n i with h1 | h1 | h1 <;> omega


/-! ## Lemmas about `heapify` -/

theorem parent_lt (j : Nat) (h : 0 < j) : parent j < j := by unfold parent; omega

theorem heapify_size (n : Nat) : ∀ (a : Array Int) (i : Nat), (heapify a n i).size = a.size := by
  intro a i
  induction a, i using heapify.induct n with
  | case1 a i h ih => rw [heapify, dif_pos h, ih, Array.size_swapIfInBounds]
  | case2 a i h => rw [heapify, dif_neg h]

theorem heapify_perm (n : Nat) :
    ∀ (a : Array Int) (i : Nat), (heapify a n i).toList.Perm a.toList := by
  intro a i
  induction a, i using heapify.induct n with
  | case1 a i h ih => rw [heapify, dif_pos h]; exact ih.trans (swapIfInBounds_perm _ _ _)
  | case2 a i h => rw [heapify, dif_neg h]

/-- `heapify a n i` only touches indices in `[i, n)`. -/
theorem heapify_getElem!_of_lt (n : Nat) : ∀ (a : Array Int) (i : Nat), n ≤ a.size →
    ∀ j, (j < i ∨ n ≤ j) → (heapify a n i)[j]! = a[j]! := by
  intro a i
  induction a, i using heapify.induct n with
  | case1 a i h ih =>
    intro hn j hj
    rw [heapify, dif_pos h, ih (by rw [Array.size_swapIfInBounds]; exact hn) j (by omega)]
    rw [getElem!_swapIfInBounds a (by omega) (by omega) j]
    rw [if_neg (by omega), if_neg (by omega)]
  | case2 a i h => intro hn j hj; rw [heapify, dif_neg h]

/-- `heapify` preserves an upper bound on the heap elements. -/
theorem heapify_le_of_le (n : Nat) (B : Int) : ∀ (a : Array Int) (i : Nat), n ≤ a.size →
    (∀ j, j < n → a[j]! ≤ B) → ∀ j, j < n → (heapify a n i)[j]! ≤ B := by
  intro a i
  induction a, i using heapify.induct n with
  | case1 a i h ih =>
    intro hn hB j hj
    rw [heapify, dif_pos h]
    apply ih (by rw [Array.size_swapIfInBounds]; exact hn) _ j hj
    intro k hk
    rw [getElem!_swapIfInBounds a (by omega) (by omega) k]
    split_ifs <;> apply hB <;> omega
  | case2 a i h => intro hn hB j hj; rw [heapify, dif_neg h]; exact hB j hj

/-- Main invariant of `heapify`: if the heap property (restricted to nodes whose parent is
`≥ lo`) holds everywhere except possibly between `i` and its children, and the children of
`i` are bounded by the parent of `i`, then after `heapify a n i` the heap property holds for
all nodes whose parent is `≥ lo`. -/
theorem heapify_heap (n : Nat) : ∀ (a : Array Int) (i : Nat), ∀ lo, n ≤ a.size → lo ≤ i →
    (∀ j, 0 < j → j < n → lo ≤ parent j → parent j ≠ i → a[j]! ≤ a[parent j]!) →
    (∀ j, 0 < j → j < n → parent j = i → 0 < i → lo ≤ parent i → a[j]! ≤ a[parent i]!) →
    ∀ j, 0 < j → j < n → lo ≤ parent j →
      (heapify a n i)[j]! ≤ (heapify a n i)[parent j]! := by
  intro a i
  induction a, i using heapify.induct n with
  | case1 a i h ih =>
    intro lo hn hlo H1 H2
    rw [heapify, dif_pos h]
    have hcases := largestIdx_cases a n i
    have hci : a[i]! ≤ a[largestIdx a n i]! := le_largestIdx_self a n i
    have hcl := le_largestIdx_left a n i
    have hcr := le_largestIdx_right a n i
    have hswap := getElem!_swapIfInBounds a (i := i) (j := largestIdx a n i) (by omega) (by omega)
    generalize largestIdx a n i = c at *
    simp only [parent] at *
    apply ih lo (by rw [Array.size_swapIfInBounds]; exact hn) (by omega)
    · intro j hj0 hjn hlo' hjc
      rw [hswap j, hswap ((j - 1) / 2)]
      by_cases hji : j = i
      · subst hji
        have := H2 c (by omega) (by omega) (by omega) hj0 hlo'
        split_ifs <;> omega
      · by_cases hjc' : j = c
        · subst hjc'
          split_ifs <;> omega
        · by_cases hpi : (j - 1) / 2 = i
          · have hj' : j = 2 * i + 1 ∨ j = 2 * i + 2 := by omega
            rcases hj' with rfl | rfl
            · have := hcl (by omega)
              split_ifs; omega
            · have := hcr (by omega)
              split_ifs; omega
          · have := H1 j hj0 hjn hlo' hpi
            split_ifs; omega
    · intro j hj0 hjn hpj hc0 hlo'
      rw [hswap j, hswap ((c - 1) / 2)]
      have := H1 j hj0 hjn (by omega) (by omega)
      rw [hpj] at this
      split_ifs <;> omega
  | case2 a i h =>
    intro lo hn hlo H1 H2 j hj0 hjn hlo'
    rw [heapify, dif_neg h]
    have hcases := largestIdx_cases a n i
    have hcl := le_largestIdx_left a n i
    have hcr := le_largestIdx_right a n i
    generalize largestIdx a n i = c at *
    simp only [parent] at *
    obtain rfl : c = i := by omega
    by_cases hpi : (j - 1) / 2 = c
    · rw [hpi]
      have hj' : j = 2 * c + 1 ∨ j = 2 * c + 2 := by omega
      rcases hj' with rfl | rfl
      · exact hcl (by omega)
      · exact hcr (by omega)
    · exact H1 j hj0 hjn hlo' hpi

/-- In a max heap the root is the maximum. -/
theorem heap_root_max (a : Array Int) (n : Nat)
    (hheap : ∀ j, 0 < j → j < n → a[j]! ≤ a[parent j]!) :
    ∀ j, j < n → a[j]! ≤ a[0]! := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact le_refl _
    · have hp := parent_lt j hj0
      exact (hheap j hj0 hj).trans (ih (parent j) hp (by omega))

/-! ## Lemmas about the two loops -/

theorem buildLoop_size (n : Nat) : ∀ (k : Nat) (a : Array Int), (buildLoop a n k).size = a.size := by
  intro k
  induction k with
  | zero => intro a; rfl
  | succ k ih => intro a; rw [buildLoop, ih, heapify_size]

theorem buildLoop_perm (n : Nat) :
    ∀ (k : Nat) (a : Array Int), (buildLoop a n k).toList.Perm a.toList := by
  intro k
  induction k with
  | zero => intro a; exact List.Perm.refl _
  | succ k ih => intro a; rw [buildLoop]; exact (ih _).trans (heapify_perm n a k)

/-- After `buildLoop a n k`, the heap property holds for every node whose parent is `≥ 0`,
provided it already held for every node whose parent is `≥ k`. -/
theorem buildLoop_heap (n : Nat) : ∀ (k : Nat) (a : Array Int), n ≤ a.size →
    (∀ j, 0 < j → j < n → k ≤ parent j → a[j]! ≤ a[parent j]!) →
    ∀ j, 0 < j → j < n → (buildLoop a n k)[j]! ≤ (buildLoop a n k)[parent j]! := by
  intro k
  induction k with
  | zero => intro a hn H j hj0 hjn; exact H j hj0 hjn (Nat.zero_le _)
  | succ k ih =>
    intro a hn H j hj0 hjn
    rw [buildLoop]
    apply ih (heapify a n k) (by rw [heapify_size]; exact hn) _ j hj0 hjn
    apply heapify_heap n a k k hn (le_refl k)
    · intro j hj0 hjn hk hne; exact H j hj0 hjn (by omega)
    · intro j hj0 hjn hpj hk0 hlo; exfalso; have := parent_lt k hk0; omega

theorem extractLoop_size : ∀ (k : Nat) (a : Array Int), (extractLoop a k).size = a.size := by
  intro k
  induction k with
  | zero => intro a; rfl
  | succ k ih => intro a; rw [extractLoop, ih, heapify_size, Array.size_swapIfInBounds]

theorem extractLoop_perm : ∀ (k : Nat) (a : Array Int), (extractLoop a k).toList.Perm a.toList := by
  intro k
  induction k with
  | zero => intro a; exact List.Perm.refl _
  | succ k ih =>
    intro a
    rw [extractLoop]
    exact (ih _).trans ((heapify_perm _ _ _).trans (swapIfInBounds_perm _ _ _))

/-- Invariant of the extraction loop: `a[0..k+1)` is a max heap, `a[k+1..)` is sorted and
every element of the heap is `≤` every element of the sorted suffix; then the result is
sorted. -/
theorem extractLoop_sorted : ∀ (k : Nat) (a : Array Int), k < a.size →
    (∀ j, 0 < j → j < k + 1 → a[j]! ≤ a[parent j]!) →
    (∀ j l, k + 1 ≤ j → j < l → l < a.size → a[j]! ≤ a[l]!) →
    (∀ j l, j < k + 1 → k + 1 ≤ l → l < a.size → a[j]! ≤ a[l]!) →
    ∀ j l, j < l → l < a.size → (extractLoop a k)[j]! ≤ (extractLoop a k)[l]! := by
  intro k
  induction k with
  | zero =>
    intro a hk hheap hsorted hsplit j l hjl hl
    rw [extractLoop]
    by_cases hj : j = 0
    · subst hj; exact hsplit 0 l (by omega) (by omega) hl
    · exact hsorted j l (by omega) hjl hl
  | succ k ih =>
    intro a hk hheap hsorted hsplit j l hjl hl
    rw [extractLoop]
    have hswap := getElem!_swapIfInBounds a (i := 0) (j := k + 1) (by omega) (by omega)
    have hroot := heap_root_max a (k + 2) hheap
    have hsize' : (a.swapIfInBounds 0 (k + 1)).size = a.size := Array.size_swapIfInBounds
    generalize a.swapIfInBounds 0 (k + 1) = a' at *
    have hsize'' : (heapify a' (k + 1) 0).size = a.size := by rw [heapify_size, hsize']
    have hunch := heapify_getElem!_of_lt (k + 1) a' 0 (by omega)
    have hbound : ∀ j, j < k + 1 → (heapify a' (k + 1) 0)[j]! ≤ a[0]! := by
      apply heapify_le_of_le (k + 1) a[0]! a' 0 (by omega)
      intro j hj
      rw [hswap j]
      split_ifs
      · exact hroot (k + 1) (by omega)
      · omega
      · exact hroot j (by omega)
    refine ih (heapify a' (k + 1) 0) (by omega) ?_ ?_ ?_ j l hjl (by omega)
    · intro j hj0 hjn
      refine heapify_heap (k + 1) a' 0 0 (by omega) (le_refl 0) ?_ ?_ j hj0 hjn (Nat.zero_le _)
      · intro j hj0 hjn hlo hne
        rw [hswap j, hswap (parent j)]
        have := parent_lt j hj0
        rw [if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j = k + 1 by omega),
          if_neg (show ¬ parent j = 0 by omega), if_neg (show ¬ parent j = k + 1 by omega)]
        exact hheap j hj0 (by omega)
      · intro j hj0 hjn hpj h0; exact absurd h0 (lt_irrefl 0)
    · intro j l hj hjl hl
      rw [hsize''] at hl
      rw [hunch j (Or.inr hj), hunch l (Or.inr (by omega)), hswap j, hswap l]
      rw [if_neg (show ¬ j = 0 by omega), if_neg (show ¬ l = 0 by omega),
        if_neg (show ¬ l = k + 1 by omega)]
      by_cases hj' : j = k + 1
      · rw [if_pos hj']
        exact hsplit 0 l (by omega) (by omega) hl
      · rw [if_neg hj']
        exact hsorted j l (by omega) hjl hl
    · intro j l hj hl hlsize
      rw [hsize''] at hlsize
      rw [hunch l (Or.inr hl), hswap l, if_neg (by omega)]
      by_cases hl' : l = k + 1
      · rw [if_pos hl']; exact hbound j hj
      · rw [if_neg hl']; exact (hbound j hj).trans (hsplit 0 l (by omega) (by omega) hlsize)

/-! ## Correctness of `heapSortArray` and `heapSort` -/

theorem heapSortArray_size (a : Array Int) : (heapSortArray a).size = a.size := by
  unfold heapSortArray; rw [extractLoop_size, buildLoop_size]

theorem heapSortArray_perm (a : Array Int) : (heapSortArray a).toList.Perm a.toList := by
  unfold heapSortArray; exact (extractLoop_perm _ _).trans (buildLoop_perm _ _ _)

theorem heapSortArray_sorted (a : Array Int) :
    ∀ j l, j < l → l < a.size → (heapSortArray a)[j]! ≤ (heapSortArray a)[l]! := by
  intro j l hjl hl
  unfold heapSortArray
  have hb := buildLoop_heap a.size (a.size / 2) a (le_refl _)
    (by intro j hj0 hjn hk; exfalso; simp only [parent] at hk; omega)
  have hsize : (buildLoop a a.size (a.size / 2)).size = a.size := buildLoop_size _ _ _
  refine extractLoop_sorted (a.size - 1) _ (by omega) ?_ ?_ ?_ j l hjl (by omega)
  · intro j hj0 hjn; exact hb j hj0 (by omega)
  · intro j l hj hjl hl; omega
  · intro j l hj hl hls; omega

theorem heapSortArray_toList_sorted (a : Array Int) :
    List.Sorted (· ≤ ·) (heapSortArray a).toList := by
  rw [List.Sorted, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hs := heapSortArray_size a
  simp only [Array.length_toList] at hi hj
  rw [Array.getElem_toList, Array.getElem_toList]
  rw [← getElem!_pos (heapSortArray a) i hi, ← getElem!_pos (heapSortArray a) j hj]
  exact heapSortArray_sorted a i j hij (by omega)

theorem heapSort_sorted (xs : List Int) : List.Sorted (· ≤ ·) (heapSort xs) := by
  unfold heapSort
  split_ifs with h
  · rcases xs with _ | ⟨x, _ | ⟨y, zs⟩⟩
    · exact List.sorted_nil
    · exact List.sorted_singleton x
    · simp at h
  · exact heapSortArray_toList_sorted _

theorem heapSort_perm (xs : List Int) : (heapSort xs).Perm xs := by
  unfold heapSort
  split_ifs
  · exact List.Perm.refl xs
  · simpa using heapSortArray_perm xs.toArray

/-! ## Pre-condition -/

/-- Precondition of the Python `heap_sort`: the input must be a `list` of `int`s
(`pre(arr)` in Python).  The Lean type `List Int` already guarantees this, so the
predicate holds for every input; the Python `ValueError` branch is unreachable. -/
def Pre (_xs : List Int) : Prop := True

/-! ## Properties -/

/-- The output is sorted in non-decreasing order. -/
def sorted_prop (xs : List Int) : Prop := List.Sorted (· ≤ ·) (heapSort xs)

theorem sorted_thm (xs : List Int) : sorted_prop xs := heapSort_sorted xs

/-- The output is a permutation of the input (same elements with multiplicities). -/
def perm_prop (xs : List Int) : Prop := (heapSort xs).Perm xs

theorem perm_thm (xs : List Int) : perm_prop xs := heapSort_perm xs

/-- The output has the same length as the input. -/
def length_prop (xs : List Int) : Prop := (heapSort xs).length = xs.length

theorem length_thm (xs : List Int) : length_prop xs := (heapSort_perm xs).length_eq

/-- Every value occurs equally often in the input and in the output. -/
def count_prop (xs : List Int) : Prop := ∀ x : Int, (heapSort xs).count x = xs.count x

theorem count_thm (xs : List Int) : count_prop xs := fun x => (heapSort_perm xs).count_eq x

/-- The output contains exactly the elements of the input. -/
def mem_prop (xs : List Int) : Prop := ∀ x : Int, x ∈ heapSort xs ↔ x ∈ xs

theorem mem_thm (xs : List Int) : mem_prop xs := fun _ => (heapSort_perm xs).mem_iff

/-- Edge case: empty and one-element lists are returned unchanged (a copy in Python). -/
def small_prop (xs : List Int) : Prop := xs.length ≤ 1 → heapSort xs = xs

theorem small_thm (xs : List Int) : small_prop xs := by
  intro h; unfold heapSort; rw [if_pos h]

/-- Characterization: `heapSort` returns *the* sorted permutation of its input, so it agrees
with any other correct sorting algorithm, e.g. insertion sort. -/
def eq_insertionSort_prop (xs : List Int) : Prop :=
  heapSort xs = List.insertionSort (· ≤ ·) xs

theorem eq_insertionSort_thm (xs : List Int) : eq_insertionSort_prop xs :=
  List.eq_of_perm_of_sorted ((heapSort_perm xs).trans (List.perm_insertionSort _ xs).symm)
    (heapSort_sorted xs) (List.sorted_insertionSort _ xs)

/-- Sorting is idempotent. -/
def idempotent_prop (xs : List Int) : Prop := heapSort (heapSort xs) = heapSort xs

theorem idempotent_thm (xs : List Int) : idempotent_prop xs :=
  List.eq_of_perm_of_sorted (heapSort_perm (heapSort xs)) (heapSort_sorted _) (heapSort_sorted xs)

/-- The first element of the output is a minimum of the input. -/
def head_min_prop (xs : List Int) : Prop :=
  ∀ m, (heapSort xs).head? = some m → ∀ x ∈ xs, m ≤ x

theorem head_min_thm (xs : List Int) : head_min_prop xs := by
  intro m hm x hx
  have hs := heapSort_sorted xs
  have hx' : x ∈ heapSort xs := (heapSort_perm xs).mem_iff.mpr hx
  rcases hs' : heapSort xs with _ | ⟨y, ys⟩
  · rw [hs'] at hm; simp at hm
  · rw [hs'] at hm hx' hs
    simp only [List.head?_cons, Option.some.injEq] at hm
    subst hm
    rw [List.sorted_cons] at hs
    rcases List.mem_cons.mp hx' with rfl | hx'
    · exact le_refl _
    · exact hs.1 x hx'

/-! ## Post-condition -/

/-- Post-condition of `heap_sort`: the result is a sorted permutation of the input, with all
the derived properties above. -/
def Post_prop (xs : List Int) : Prop :=
  sorted_prop xs ∧ perm_prop xs ∧ length_prop xs ∧ count_prop xs ∧ mem_prop xs ∧
    small_prop xs ∧ eq_insertionSort_prop xs ∧ idempotent_prop xs ∧ head_min_prop xs

/-! ## Property-based tests -/

-- sorted_prop
#eval Plausible.Testable.check (∀ xs : List Int, List.Sorted (· ≤ ·) (heapSort xs))
-- perm_prop
#eval Plausible.Testable.check (∀ xs : List Int, (heapSort xs).Perm xs)
-- length_prop
#eval Plausible.Testable.check (∀ xs : List Int, (heapSort xs).length = xs.length)
-- count_prop
#eval Plausible.Testable.check (∀ xs : List Int, ∀ x : Int, (heapSort xs).count x = xs.count x)
-- mem_prop
#eval Plausible.Testable.check (∀ xs : List Int, ∀ x : Int, x ∈ heapSort xs ↔ x ∈ xs)
-- small_prop (randomized over the admissible inputs of length ≤ 1)
#eval Plausible.Testable.check (∀ x : Int, heapSort [x] = [x])
-- eq_insertionSort_prop
#eval Plausible.Testable.check (∀ xs : List Int, heapSort xs = List.insertionSort (· ≤ ·) xs)
-- idempotent_prop
#eval Plausible.Testable.check (∀ xs : List Int, heapSort (heapSort xs) = heapSort xs)
-- head_min_prop (executable form)
#eval Plausible.Testable.check
  (∀ xs : List Int, (heapSort xs).head?.all (fun m => xs.all (fun x => m ≤ x)) = true)

/-- Deterministic family of test inputs for bounded property-based tests. -/
def pbtInputs : List (List Int) :=
  [[], [1], [2, 1], [1, 2], [3, 1, 2], [5, 5, 5], [-3, 7, -1, 0, 7, -3],
    [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]] ++
  (List.range 40).map (fun k =>
    (List.range k).map (fun x => (((x * 7919 + 13) % 23 : Nat) : Int) - 11)) ++
  (List.range 20).map (fun k => (List.range k).map (fun x => (x : Int))) ++
  (List.range 20).map (fun k => (List.range k).map (fun x => ((k : Int) - x)))

/-- Executable form of `Post_prop` (with `count_prop`/`mem_prop` checked on the elements of
the input together with the values `0` and `42`). -/
def postCheck (xs : List Int) : Bool :=
  let ys := heapSort xs
  decide (List.Sorted (· ≤ ·) ys) && decide (ys.Perm xs) && (ys.length == xs.length) &&
    (xs ++ [0, 42]).all (fun x => ys.count x == xs.count x) &&
    (xs ++ [0, 42]).all (fun x => decide (x ∈ ys ↔ x ∈ xs)) &&
    (!(xs.length ≤ 1) || ys == xs) &&
    (ys == List.insertionSort (· ≤ ·) xs) && (heapSort ys == ys) &&
    ys.head?.all (fun m => xs.all (fun x => m ≤ x))

example : pbtInputs.all (fun xs => decide (List.Sorted (· ≤ ·) (heapSort xs))) = true := by
  native_decide
example : pbtInputs.all (fun xs => decide ((heapSort xs).Perm xs)) = true := by native_decide
example : pbtInputs.all (fun xs => (heapSort xs).length == xs.length) = true := by native_decide
example : pbtInputs.all (fun xs => xs.all (fun x => (heapSort xs).count x == xs.count x)) =
    true := by native_decide
example : pbtInputs.all (fun xs =>
    (xs ++ [0, 42]).all (fun x => decide (x ∈ heapSort xs ↔ x ∈ xs))) = true := by native_decide
example : pbtInputs.all (fun xs => !(xs.length ≤ 1) || heapSort xs == xs) = true := by
  native_decide
example : pbtInputs.all (fun xs => heapSort xs == List.insertionSort (· ≤ ·) xs) = true := by
  native_decide
example : pbtInputs.all (fun xs => heapSort (heapSort xs) == heapSort xs) = true := by
  native_decide
example : pbtInputs.all (fun xs => (heapSort xs).head?.all (fun m => xs.all (fun x => m ≤ x))) =
    true := by native_decide
-- Post_prop (executable form)
example : pbtInputs.all postCheck = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, postCheck xs = true)

/-! ## Correctness theorem -/

/-- `Pre → Post`: for every admissible input, `heapSort` satisfies the post-condition. -/
theorem correctness_thm (xs : List Int) (_hpre : Pre xs) : Post_prop xs :=
  ⟨sorted_thm xs, perm_thm xs, length_thm xs, count_thm xs, mem_thm xs, small_thm xs,
    eq_insertionSort_thm xs, idempotent_thm xs, head_min_thm xs⟩

/-! ## Imperative implementation -/

set_option linter.unusedVariables false in
/-- Imperative `heapify` with mutable `arr` and `largest`, mirroring the Python code.
The recursive call happens exactly when `largest != i`; since `largest` is then a child
of `i` inside the heap, this is the same as `i < largest ∧ largest < n`, which also
justifies termination. -/
def heapifyImp (a : Array Int) (n i : Nat) : Array Int := Id.run do
  let mut arr := a
  let mut largest := i
  let left := 2 * i + 1
  let right := 2 * i + 2
  if left < n && arr[left]! > arr[largest]! then
    largest := left
  if right < n && arr[right]! > arr[largest]! then
    largest := right
  if h : i < largest ∧ largest < n then
    arr := arr.swapIfInBounds i largest
    arr := heapifyImp arr n largest
  return arr
termination_by n - i
decreasing_by exact Nat.sub_lt_sub_left (Nat.lt_trans h.1 h.2) h.1

/-- Imperative heap sort (Python's `heap_sort`), using `Id.run do`, a mutable array and
`for` loops over the Python ranges `range(n//2 - 1, -1, -1)` and `range(n-1, 0, -1)`. -/
def heapSortImp (xs : List Int) : List Int := Id.run do
  if xs.length ≤ 1 then
    return xs
  let mut result := xs.toArray
  let n := result.size
  -- build max heap
  for i in (List.range (n / 2)).reverse do
    result := heapifyImp result n i
  -- extract elements one by one
  for i in (List.range' 1 (n - 1)).reverse do
    result := result.swapIfInBounds 0 i
    result := heapifyImp result i 0
  return result.toList

/-! ## Imperative tests -/

example : heapSortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSortImp [] = [] := by native_decide
example : heapSortImp [1] = [1] := by native_decide
example : heapSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

example : heapSortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapSortImp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : pbtInputs.all (fun xs => heapSortImp xs == heapSort xs) = true := by native_decide

#eval heapSortImp [3, 7, 1, 9, 2, 8, 4, 6, 5]
#eval Plausible.Testable.check (∀ xs : List Int, heapSortImp xs = heapSort xs)

/-! ## Equivalence of the functional and imperative implementations -/

theorem heapifyImp_unfold (a : Array Int) (n i : Nat) :
    heapifyImp a n i =
      if i < largestIdx a n i ∧ largestIdx a n i < n then
        heapifyImp (a.swapIfInBounds i (largestIdx a n i)) n (largestIdx a n i)
      else a := by
  rw [heapifyImp]
  simp only [Id.run, bind, pure, largestIdx, Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
  split_ifs <;> rfl

theorem heapifyImp_eq (n : Nat) : ∀ (a : Array Int) (i : Nat), heapifyImp a n i = heapify a n i := by
  intro a i
  induction a, i using heapify.induct n with
  | case1 a i h ih => rw [heapifyImp_unfold, heapify, if_pos h, dif_pos h, ih]
  | case2 a i h => rw [heapifyImp_unfold, heapify, if_neg h, dif_neg h]

theorem foldr_range_eq_buildLoop (n : Nat) : ∀ (m : Nat) (a : Array Int),
    List.foldr (fun i r => heapify r n i) a (List.range m) = buildLoop a n m := by
  intro m
  induction m with
  | zero => intro a; rfl
  | succ m ih =>
    intro a
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, buildLoop, ih]

theorem foldr_range'_eq_extractLoop : ∀ (m : Nat) (a : Array Int),
    List.foldr (fun i r => heapify (r.swapIfInBounds 0 i) i 0) a (List.range' 1 m) =
      extractLoop a m := by
  intro m
  induction m with
  | zero => intro a; rfl
  | succ m ih =>
    intro a
    rw [List.range'_concat, List.foldr_append, List.foldr_cons, List.foldr_nil, extractLoop, ih]
    rw [show 1 + 1 * m = m + 1 by omega]

/-- The imperative implementation computes exactly the functional one. -/
theorem heapSortImp_eq_heapSort (xs : List Int) : heapSortImp xs = heapSort xs := by
  unfold heapSortImp heapSort heapSortArray
  simp only [Id.run, bind, heapifyImp_eq]
  simp only [List.forIn_pure_yield_eq_foldl, List.foldl_reverse, foldr_range_eq_buildLoop,
    foldr_range'_eq_extractLoop]
  rfl

/-- Equivalence theorem: functional = imperative. -/
theorem heapSort_eq_imp_thm : ∀ xs : List Int, heapSort xs = heapSortImp xs :=
  fun xs => (heapSortImp_eq_heapSort xs).symm

/-- Consequently the imperative implementation also satisfies the post-condition. -/
theorem heapSortImp_correct (xs : List Int) (_hpre : Pre xs) :
    List.Sorted (· ≤ ·) (heapSortImp xs) ∧ (heapSortImp xs).Perm xs := by
  rw [heapSortImp_eq_heapSort]
  exact ⟨heapSort_sorted xs, heapSort_perm xs⟩

end heap_sort
