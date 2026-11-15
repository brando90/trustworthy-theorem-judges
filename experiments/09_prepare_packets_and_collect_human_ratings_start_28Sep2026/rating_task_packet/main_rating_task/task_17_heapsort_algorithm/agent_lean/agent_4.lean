import Mathlib

/-!
# HEAPSORT (CLRS 6.4) on 0-based max-heap arrays

Translation of the Python program `heapsort_algorithm.py`.

* `parent`, `left`, `right` : index arithmetic of the implicit binary tree.
* `maxHeapify a i n` : sift the element at `i` down inside the heap `a[0..n)`
  (the Python `max_heapify` while-loop, written as well-founded recursion).
* `buildMaxHeap` : heapify the positions `parent (n-1), …, 0`.
* `heapsort` : build a max-heap, then repeatedly move the maximum to the end.

The Python `pre` only checks that the input is a list of natural numbers; in
Lean this is enforced by the type `List Nat`, so `Pre` is trivial.

We prove: the result is sorted, is a permutation of the input, has the same
length, equals `List.mergeSort` (Python's `sorted`), and that an imperative
`Id.run do` version with mutable state computes the same function.
-/

namespace heapsort_algorithm

/-! ## Functional implementation -/

/-- `parent i = (i - 1) / 2`; for `i = 0` natural subtraction gives `0`, as in Python. -/
def parent (i : Nat) : Nat := (i - 1) / 2

/-- left child -/
def left (i : Nat) : Nat := 2 * i + 1

/-- right child -/
def right (i : Nat) : Nat := 2 * i + 2

/-- Index of the largest among `i`, `left i`, `right i` restricted to the heap `[0, heapSize)`.
This is exactly the `largest` computed by the Python loop body. -/
def largestOf (a : Array Nat) (i heapSize : Nat) : Nat :=
  let l := left i
  let r := right i
  let largest := if l < heapSize ∧ a[i]! < a[l]! then l else i
  if r < heapSize ∧ a[largest]! < a[r]! then r else largest

theorem largestOf_spec (a : Array Nat) (i n : Nat) :
    (largestOf a i n = i ∧ (left i < n → a[left i]! ≤ a[i]!) ∧ (right i < n → a[right i]! ≤ a[i]!)) ∨
    (largestOf a i n ≠ i ∧ (largestOf a i n = left i ∨ largestOf a i n = right i) ∧
      largestOf a i n < n ∧ a[i]! < a[largestOf a i n]! ∧
      (left i < n → a[left i]! ≤ a[largestOf a i n]!) ∧
      (right i < n → a[right i]! ≤ a[largestOf a i n]!)) := by
  unfold largestOf left right
  simp only []
  split_ifs with h1 h2 h2
  · right; refine ⟨by omega, Or.inr rfl, h2.1, by omega, fun _ => by omega, fun _ => le_refl _⟩
  · right; refine ⟨by omega, Or.inl rfl, h1.1, h1.2, fun _ => le_refl _, fun hr => ?_⟩
    have := not_and.mp h2 hr; omega
  · right; refine ⟨by omega, Or.inr rfl, h2.1, h2.2, fun hl => ?_, fun _ => le_refl _⟩
    have := not_and.mp h1 hl; omega
  · left; refine ⟨rfl, fun hl => ?_, fun hr => ?_⟩
    · have := not_and.mp h1 hl; omega
    · have := not_and.mp h2 hr; omega

theorem largestOf_ne (a : Array Nat) (i n : Nat) (h : largestOf a i n ≠ i) :
    i < largestOf a i n ∧ largestOf a i n < n := by
  rcases largestOf_spec a i n with ⟨h0, -⟩ | ⟨-, hc, hn, -⟩
  · exact absurd h0 h
  · unfold left right at hc; omega

set_option linter.unusedVariables false in
/-- `max_heapify`: sift the element at index `i` down inside the heap `a[0..heapSize)`. -/
def maxHeapify (a : Array Nat) (i heapSize : Nat) : Array Nat :=
  if h : largestOf a i heapSize = i then a
  else maxHeapify (a.swapIfInBounds i (largestOf a i heapSize)) (largestOf a i heapSize) heapSize
termination_by heapSize - i
decreasing_by
  have := largestOf_ne a i heapSize h
  omega

/-- The loop `for i in range(k, -1, -1): max_heapify(a, i, heapSize)`. -/
def buildLoop (a : Array Nat) (heapSize : Nat) : Nat → Array Nat
  | 0 => maxHeapify a 0 heapSize
  | k + 1 => buildLoop (maxHeapify a (k + 1) heapSize) heapSize k

/-- `build_max_heap` -/
def buildMaxHeap (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a else buildLoop a a.size (parent (a.size - 1))

/-- The loop `for i in range(n-1, 0, -1): swap(0, i); max_heapify(a, 0, i)`;
`extractLoop a k` performs the iterations `i = k, k-1, …, 1`. -/
def extractLoop (a : Array Nat) : Nat → Array Nat
  | 0 => a
  | k + 1 => extractLoop (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)) k

/-- `heapsort` on arrays -/
def heapsortArr (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a else extractLoop (buildMaxHeap a) (a.size - 1)

/-- `heapsort`: sort a list of naturals in ascending order (returns a sorted copy). -/
def heapsort (arr : List Nat) : List Nat := (heapsortArr arr.toArray).toList

/-! ## Unit tests (from the Python `check`) -/

example : heapsort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by native_decide
example : heapsort [] = [] := by native_decide
example : heapsort [42] = [42] := by native_decide
example : heapsort [2, 1] = [1, 2] := by native_decide
example : heapsort [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by native_decide
example : heapsort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsort [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : heapsort [2, 1] ≠ [2, 1] := by native_decide
example : (buildMaxHeap #[4, 1, 3, 2, 16, 9, 10, 14, 8, 7]).toList = [16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by
  native_decide
example : parent 0 = 0 ∧ parent 1 = 0 ∧ parent 2 = 0 ∧ parent 5 = 2 := by decide
example : left 2 = 5 ∧ right 2 = 6 := by decide

#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]


/-! ## Basic lemmas -/

theorem swapIfInBounds_eq (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    a.swapIfInBounds i j = a.swap i j hi hj := by
  simp [Array.swapIfInBounds, hi, hj]

theorem swapIfInBounds_get! (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) (k : Nat) :
    (a.swapIfInBounds i j)[k]! = if k = i then a[j]! else if k = j then a[i]! else a[k]! := by
  rw [swapIfInBounds_eq a i j hi hj]
  by_cases hk : k < a.size
  · have hk' : k < (a.swap i j hi hj).size := by simpa using hk
    rw [getElem!_pos (a.swap i j hi hj) k hk', Array.getElem_swap, getElem!_pos a i hi, getElem!_pos a j hj,
      getElem!_pos a k hk]
  · have h1 : k ≠ i := by omega
    have h2 : k ≠ j := by omega
    have hk' : ¬ k < (a.swap i j hi hj).size := by simpa using hk
    rw [if_neg h1, if_neg h2, getElem!_neg (a.swap i j hi hj) k hk', getElem!_neg a k hk]

theorem swapIfInBounds_perm (a : Array Nat) (i j : Nat) :
    List.Perm (a.swapIfInBounds i j).toList a.toList := by
  unfold Array.swapIfInBounds
  split_ifs with hi hj
  · exact (Array.swap_perm hi hj).toList
  · exact List.Perm.refl _
  · exact List.Perm.refl _

theorem maxHeapify_of_eq {a : Array Nat} {i n : Nat} (h : largestOf a i n = i) :
    maxHeapify a i n = a := by
  rw [maxHeapify, dif_pos h]

theorem maxHeapify_of_ne {a : Array Nat} {i n : Nat} (h : largestOf a i n ≠ i) :
    maxHeapify a i n = maxHeapify (a.swapIfInBounds i (largestOf a i n)) (largestOf a i n) n := by
  conv_lhs => rw [maxHeapify]
  rw [dif_neg h]

theorem maxHeapify_size (a : Array Nat) (i n : Nat) : (maxHeapify a i n).size = a.size := by
  induction a, i using maxHeapify.induct n with
  | case1 a i h => rw [maxHeapify_of_eq h]
  | case2 a i h ih => rw [maxHeapify_of_ne h, ih, Array.size_swapIfInBounds]

theorem maxHeapify_perm (a : Array Nat) (i n : Nat) :
    List.Perm (maxHeapify a i n).toList a.toList := by
  induction a, i using maxHeapify.induct n with
  | case1 a i h => rw [maxHeapify_of_eq h]
  | case2 a i h ih => rw [maxHeapify_of_ne h]; exact ih.trans (swapIfInBounds_perm _ _ _)

/-- `maxHeapify` does not touch positions outside the heap. -/
theorem maxHeapify_get!_of_le (a : Array Nat) (i n : Nat) (hn : n ≤ a.size) (j : Nat) (hj : n ≤ j) :
    (maxHeapify a i n)[j]! = a[j]! := by
  induction a, i using maxHeapify.induct n with
  | case1 a i h => rw [maxHeapify_of_eq h]
  | case2 a i h ih =>
    obtain ⟨hig, hgn⟩ := largestOf_ne a i n h
    rw [maxHeapify_of_ne h, ih (by simpa using hn), swapIfInBounds_get! a i _ (by omega) (by omega),
      if_neg (by omega), if_neg (by omega)]

/-- An upper bound on the heap part is preserved by `maxHeapify`. -/
theorem maxHeapify_get!_le (a : Array Nat) (i n : Nat) (hn : n ≤ a.size) (v : Nat)
    (hv : ∀ j, j < n → a[j]! ≤ v) : ∀ j, j < n → (maxHeapify a i n)[j]! ≤ v := by
  induction a, i using maxHeapify.induct n with
  | case1 a i h => rw [maxHeapify_of_eq h]; exact hv
  | case2 a i h ih =>
    obtain ⟨hig, hgn⟩ := largestOf_ne a i n h
    rw [maxHeapify_of_ne h]
    refine ih (by simpa using hn) ?_
    intro j hj
    rw [swapIfInBounds_get! a i _ (by omega) (by omega)]
    split_ifs
    · exact hv _ hgn
    · exact hv _ (by omega)
    · exact hv _ hj


/-! ## Heap invariants -/

theorem parent_left (i : Nat) : parent (left i) = i := by unfold parent left; omega
theorem parent_right (i : Nat) : parent (right i) = i := by unfold parent right; omega
theorem parent_lt {j : Nat} (h : 0 < j) : parent j < j := by unfold parent; omega
theorem eq_child_of_parent {i j : Nat} (h0 : 0 < j) (h : parent j = i) : j = left i ∨ j = right i := by
  unfold parent at h; unfold left right; omega
theorem parent_mono {j k : Nat} (h : j ≤ k) : parent j ≤ parent k := by unfold parent; omega

/-- Heap property for all nodes `j < n` whose parent is at least `k`. -/
def HeapFrom (a : Array Nat) (n k : Nat) : Prop :=
  ∀ j, 0 < j → j < n → k ≤ parent j → a[j]! ≤ a[parent j]!

/-- `a[0..n)` is a max-heap: every non-root node is at most its parent. -/
def IsHeap (a : Array Nat) (n : Nat) : Prop := HeapFrom a n 0

/-- Invariant of `maxHeapify a i n` (relative to the threshold `k`): the heap property holds for
every node (with parent `≥ k`) whose parent is not `i`, and the children of `i` are bounded by the
parent of `i`. -/
def HeapInv (a : Array Nat) (n k i : Nat) : Prop :=
  (∀ j, 0 < j → j < n → k ≤ parent j → parent j ≠ i → a[j]! ≤ a[parent j]!) ∧
  (∀ j, 0 < j → j < n → parent j = i → 0 < i → k ≤ parent i → a[j]! ≤ a[parent i]!)

theorem maxHeapify_heapFrom (a : Array Nat) (i n k : Nat) (hn : n ≤ a.size) (hinv : HeapInv a n k i) :
    HeapFrom (maxHeapify a i n) n k := by
  induction a, i using maxHeapify.induct n with
  | case1 a i h =>
    rw [maxHeapify_of_eq h]
    intro j hj0 hjn hkj
    by_cases hp : parent j = i
    · rcases largestOf_spec a i n with ⟨-, hl, hr⟩ | ⟨h', -⟩
      · rw [hp]
        rcases eq_child_of_parent hj0 hp with hc | hc
        · rw [hc]; exact hl (hc ▸ hjn)
        · rw [hc]; exact hr (hc ▸ hjn)
      · exact absurd h h'
    · exact hinv.1 j hj0 hjn hkj hp
  | case2 a i h ih =>
    rw [maxHeapify_of_ne h]
    rcases largestOf_spec a i n with ⟨h', -⟩ | ⟨-, hchild, hgn, hgt, hl, hr⟩
    · exact absurd h' h
    obtain ⟨hig, -⟩ := largestOf_ne a i n h
    generalize largestOf a i n = g at *
    have hpg : parent g = i := by
      rcases hchild with hc | hc
      · rw [hc]; exact parent_left i
      · rw [hc]; exact parent_right i
    have hsw := swapIfInBounds_get! a i g (by omega) (by omega)
    refine ih (by simpa using hn) ⟨?_, ?_⟩
    · intro j hj0 hjn hkj hpj
      rw [hsw j, hsw (parent j)]
      by_cases hji : j = i
      · rw [hji] at hj0 hkj ⊢
        have hpi : parent i < i := parent_lt hj0
        rw [if_pos rfl, if_neg (show parent i ≠ i by omega), if_neg (show parent i ≠ g by omega)]
        exact hinv.2 g (by omega) hgn hpg hj0 hkj
      · rw [if_neg hji]
        by_cases hjg : j = g
        · rw [if_pos hjg, hjg, hpg, if_pos rfl]
          exact hgt.le
        · rw [if_neg hjg]
          by_cases hpi : parent j = i
          · rw [if_pos hpi]
            rcases eq_child_of_parent hj0 hpi with hc | hc
            · rw [hc]; exact hl (hc ▸ hjn)
            · rw [hc]; exact hr (hc ▸ hjn)
          · rw [if_neg hpi, if_neg hpj]
            exact hinv.1 j hj0 hjn hkj hpi
    · intro j hj0 hjn hpj hg0 hkg
      rw [hpg] at hkg ⊢
      have hpj' : parent j < j := parent_lt hj0
      rw [hsw j, hsw i, if_neg (show j ≠ i by omega), if_neg (show j ≠ g by omega), if_pos rfl]
      have := hinv.1 j hj0 hjn (by omega) (by omega)
      rwa [hpj] at this

/-- In a max-heap the root is the maximum. -/
theorem IsHeap.le_root {a : Array Nat} {n : Nat} (h : IsHeap a n) : ∀ j, j < n → a[j]! ≤ a[0]! := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact le_refl _
    · exact (h j hj0 hj (Nat.zero_le _)).trans (ih _ (parent_lt hj0) (lt_trans (parent_lt hj0) hj))

/-! ## Building the heap -/

theorem buildLoop_size (a : Array Nat) (n k : Nat) : (buildLoop a n k).size = a.size := by
  induction k generalizing a with
  | zero => exact maxHeapify_size _ _ _
  | succ k ih => rw [buildLoop, ih, maxHeapify_size]

theorem buildLoop_perm (a : Array Nat) (n k : Nat) : List.Perm (buildLoop a n k).toList a.toList := by
  induction k generalizing a with
  | zero => exact maxHeapify_perm _ _ _
  | succ k ih => rw [buildLoop]; exact (ih _).trans (maxHeapify_perm _ _ _)

theorem buildLoop_isHeap (a : Array Nat) (n k : Nat) (hn : n ≤ a.size) (h : HeapFrom a n (k + 1)) :
    IsHeap (buildLoop a n k) n := by
  induction k generalizing a with
  | zero =>
    show HeapFrom (maxHeapify a 0 n) n 0
    apply maxHeapify_heapFrom a 0 n 0 hn
    exact ⟨fun j hj0 hjn _ hpj => h j hj0 hjn (by omega), fun j _ _ _ h0 _ => absurd h0 (lt_irrefl 0)⟩
  | succ k ih =>
    rw [buildLoop]
    apply ih _ (by rw [maxHeapify_size]; exact hn)
    apply maxHeapify_heapFrom a (k + 1) n (k + 1) hn
    refine ⟨fun j hj0 hjn hkj hpj => h j hj0 hjn (by omega), fun j _ _ _ _ hk => ?_⟩
    exact absurd (lt_of_le_of_lt hk (parent_lt (Nat.succ_pos k))) (lt_irrefl _)

theorem buildMaxHeap_size (a : Array Nat) : (buildMaxHeap a).size = a.size := by
  unfold buildMaxHeap
  split_ifs
  · rfl
  · exact buildLoop_size _ _ _

theorem buildMaxHeap_perm (a : Array Nat) : List.Perm (buildMaxHeap a).toList a.toList := by
  unfold buildMaxHeap
  split_ifs
  · exact List.Perm.refl _
  · exact buildLoop_perm _ _ _

/-- `buildMaxHeap` produces a max-heap on the whole array. -/
theorem buildMaxHeap_isHeap (a : Array Nat) : IsHeap (buildMaxHeap a) a.size := by
  unfold buildMaxHeap
  split_ifs with h
  · intro j hj0 hjn _; omega
  · apply buildLoop_isHeap _ _ _ (le_refl _)
    intro j hj0 hjn hk
    exfalso
    have := parent_mono (Nat.le_sub_one_of_lt hjn)
    omega

/-! ## Extraction phase -/

/-- Positions `[m, n)` hold a sorted suffix that dominates the prefix `[0, m)`:
for `j ≤ k < n` with `m ≤ k` we have `a[j] ≤ a[k]`. -/
def SortedSuffix (a : Array Nat) (n m : Nat) : Prop :=
  ∀ j k, j ≤ k → k < n → m ≤ k → a[j]! ≤ a[k]!

theorem extractLoop_size (a : Array Nat) (k : Nat) : (extractLoop a k).size = a.size := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => rw [extractLoop, ih, maxHeapify_size, Array.size_swapIfInBounds]

theorem extractLoop_perm (a : Array Nat) (k : Nat) : List.Perm (extractLoop a k).toList a.toList := by
  induction k generalizing a with
  | zero => exact List.Perm.refl _
  | succ k ih =>
    rw [extractLoop]
    exact (ih _).trans ((maxHeapify_perm _ _ _).trans (swapIfInBounds_perm _ _ _))

theorem extractLoop_sortedSuffix (a : Array Nat) (n k : Nat) (hn : n ≤ a.size) (hk : k + 1 ≤ n)
    (hheap : IsHeap a (k + 1)) (hs : SortedSuffix a n (k + 1)) :
    SortedSuffix (extractLoop a k) n 1 := by
  induction k generalizing a with
  | zero => exact hs
  | succ k ih =>
    rw [extractLoop]
    have hsw := swapIfInBounds_get! a 0 (k + 1) (by omega) (by omega)
    have hroot := hheap.le_root
    have hs' : SortedSuffix (a.swapIfInBounds 0 (k + 1)) n (k + 1) := by
      intro j l hjl hln hkl
      rw [hsw j, hsw l]
      rcases Nat.lt_or_ge (k + 1) l with hl | hl
      · rw [if_neg (show l ≠ 0 by omega), if_neg (show l ≠ k + 1 by omega)]
        split_ifs with h1 h2
        · exact hs (k + 1) l (by omega) hln (by omega)
        · exact hs 0 l (Nat.zero_le _) hln (by omega)
        · exact hs j l hjl hln (by omega)
      · have hl' : l = k + 1 := by omega
        rw [if_neg (show l ≠ 0 by omega), if_pos hl']
        split_ifs with h1 h2
        · exact hroot (k + 1) (by omega)
        · exact le_refl _
        · exact hroot j (by omega)
    have hsz : k + 1 ≤ (a.swapIfInBounds 0 (k + 1)).size := by
      rw [Array.size_swapIfInBounds]; omega
    have hheap' : IsHeap (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)) (k + 1) := by
      apply maxHeapify_heapFrom _ 0 (k + 1) 0 hsz
      refine ⟨fun j hj0 hjn _ hpj => ?_, fun j _ _ _ h0 _ => absurd h0 (lt_irrefl 0)⟩
      have hpj' := parent_lt hj0
      rw [hsw j, hsw (parent j), if_neg (show j ≠ 0 by omega), if_neg (show j ≠ k + 1 by omega),
        if_neg hpj, if_neg (show parent j ≠ k + 1 by omega)]
      exact hheap j hj0 (by omega) (Nat.zero_le _)
    apply ih _ (by rw [maxHeapify_size, Array.size_swapIfInBounds]; exact hn) (by omega) hheap'
    intro j l hjl hln hkl
    rw [maxHeapify_get!_of_le _ 0 (k + 1) hsz l hkl]
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · exact maxHeapify_get!_le _ 0 (k + 1) hsz _ (fun j' hj' => hs' j' l (by omega) hln hkl) j hj
    · rw [maxHeapify_get!_of_le _ 0 (k + 1) hsz j hj]
      exact hs' j l hjl hln hkl

/-! ## Correctness of `heapsortArr` -/

theorem heapsortArr_size (a : Array Nat) : (heapsortArr a).size = a.size := by
  unfold heapsortArr
  split_ifs
  · rfl
  · rw [extractLoop_size, buildMaxHeap_size]

theorem heapsortArr_perm (a : Array Nat) : List.Perm (heapsortArr a).toList a.toList := by
  unfold heapsortArr
  split_ifs
  · exact List.Perm.refl _
  · exact (extractLoop_perm _ _).trans (buildMaxHeap_perm _)

theorem heapsortArr_sortedSuffix (a : Array Nat) : SortedSuffix (heapsortArr a) a.size 1 := by
  unfold heapsortArr
  split_ifs with h
  · intro j l hjl hln hkl; omega
  · apply extractLoop_sortedSuffix _ _ _ (by rw [buildMaxHeap_size]) (by omega)
    · have := buildMaxHeap_isHeap a
      rwa [show a.size - 1 + 1 = a.size by omega]
    · intro j l hjl hln hkl; omega

theorem heapsortArr_sorted (a : Array Nat) : (heapsortArr a).toList.Sorted (· ≤ ·) := by
  have hs := heapsortArr_sortedSuffix a
  have hsz := heapsortArr_size a
  rw [List.Sorted, List.pairwise_iff_getElem]
  intro p q hp hq hpq
  have hp' : p < (heapsortArr a).size := by simpa using hp
  have hq' : q < (heapsortArr a).size := by simpa using hq
  rw [Array.getElem_toList hp', Array.getElem_toList hq']
  rw [← getElem!_pos (heapsortArr a) p hp', ← getElem!_pos (heapsortArr a) q hq']
  exact hs p q hpq.le (by omega) (by omega)


/-! ## Pre-condition -/

/-- Python `pre(arr)`: the input is a list of natural numbers (`isinstance(x, int)`, `x ≥ 0`).
In Lean the type `List Nat` already guarantees this, so the pre-condition is trivially true. -/
def Pre (_arr : List Nat) : Prop := True

/-! ## Properties -/

/-- The output is sorted in non-decreasing order. -/
def heapsort_sorted_prop (arr : List Nat) : Prop := (heapsort arr).Sorted (· ≤ ·)

/-- The output is a permutation of the input (`sorted(out) == sorted(arr)`). -/
def heapsort_perm_prop (arr : List Nat) : Prop := List.Perm (heapsort arr) arr

/-- The output has the same length as the input (`len(out) == len(arr)`). -/
def heapsort_length_prop (arr : List Nat) : Prop := (heapsort arr).length = arr.length

/-- The output equals Python's `sorted(arr)` (modelled by `List.mergeSort`). -/
def heapsort_eq_sorted_prop (arr : List Nat) : Prop := heapsort arr = arr.mergeSort

/-- Inputs of length `≤ 1` are returned unchanged (`return arr.copy()`). -/
def heapsort_short_prop (arr : List Nat) : Prop := arr.length ≤ 1 → heapsort arr = arr

/-- `build_max_heap` returns a max-heap on the whole array. -/
def buildMaxHeap_isHeap_prop (arr : List Nat) : Prop := IsHeap (buildMaxHeap arr.toArray) arr.length

/-- `build_max_heap` returns a permutation of its input. -/
def buildMaxHeap_perm_prop (arr : List Nat) : Prop := List.Perm (buildMaxHeap arr.toArray).toList arr

/-- `parent (left i) = i` and `parent (right i) = i` (index helpers are inverse to each other). -/
def parent_child_prop (i : Nat) : Prop := parent (left i) = i ∧ parent (right i) = i

/-- `max_heapify` only permutes the array (and keeps its length). -/
def maxHeapify_perm_prop (arr : List Nat) (i n : Nat) : Prop :=
  List.Perm (maxHeapify arr.toArray i n).toList arr ∧ (maxHeapify arr.toArray i n).size = arr.length

theorem heapsort_sorted_thm (arr : List Nat) : heapsort_sorted_prop arr := heapsortArr_sorted _

theorem heapsort_perm_thm (arr : List Nat) : heapsort_perm_prop arr := by
  unfold heapsort_perm_prop heapsort
  simpa using heapsortArr_perm arr.toArray

theorem heapsort_length_thm (arr : List Nat) : heapsort_length_prop arr :=
  (heapsort_perm_thm arr).length_eq

theorem heapsort_eq_sorted_thm (arr : List Nat) : heapsort_eq_sorted_prop arr := by
  unfold heapsort_eq_sorted_prop
  apply List.eq_of_perm_of_sorted ((heapsort_perm_thm arr).trans (List.mergeSort_perm arr _).symm)
    (heapsort_sorted_thm arr)
  exact List.sorted_mergeSort' (· ≤ ·) arr

theorem heapsort_short_thm (arr : List Nat) : heapsort_short_prop arr := by
  intro h
  unfold heapsort heapsortArr
  rw [if_pos (by simpa using h)]

theorem buildMaxHeap_isHeap_thm (arr : List Nat) : buildMaxHeap_isHeap_prop arr := by
  unfold buildMaxHeap_isHeap_prop
  simpa using buildMaxHeap_isHeap arr.toArray

theorem buildMaxHeap_perm_thm (arr : List Nat) : buildMaxHeap_perm_prop arr := by
  unfold buildMaxHeap_perm_prop
  simpa using buildMaxHeap_perm arr.toArray

theorem parent_child_thm (i : Nat) : parent_child_prop i := ⟨parent_left i, parent_right i⟩

theorem maxHeapify_perm_thm (arr : List Nat) (i n : Nat) : maxHeapify_perm_prop arr i n := by
  unfold maxHeapify_perm_prop
  constructor
  · simpa using maxHeapify_perm arr.toArray i n
  · simp [maxHeapify_size]

/-! ## Post-condition -/

/-- Post-condition of `heapsort`: a sorted permutation of the input, of the same length, equal to
`sorted(arr)`, and the identity on inputs of length `≤ 1`. -/
def Post_prop (arr : List Nat) : Prop :=
  heapsort_sorted_prop arr ∧ heapsort_perm_prop arr ∧ heapsort_length_prop arr ∧
    heapsort_eq_sorted_prop arr ∧ heapsort_short_prop arr

/-! ## Property-based tests -/

#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).Sorted (· ≤ ·))
#eval Plausible.Testable.check (∀ xs : List Nat, List.Perm (heapsort xs) xs)
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).length = xs.length)
#eval Plausible.Testable.check (∀ xs : List Nat, heapsort xs = xs.mergeSort)
-- `heapsort_short_prop` in executable form (all admissible inputs: `[]` and singletons)
#eval Plausible.Testable.check (∀ x : Nat, heapsort [x] = [x] ∧ heapsort [] = [])
#eval Plausible.Testable.check (∀ xs : List Nat, 1 < xs.length ∨ heapsort xs = xs)
-- `Post_prop` in executable form
#eval Plausible.Testable.check (∀ xs : List Nat,
  (heapsort xs).Sorted (· ≤ ·) ∧ List.Perm (heapsort xs) xs ∧ (heapsort xs).length = xs.length ∧
    heapsort xs = xs.mergeSort ∧ (1 < xs.length ∨ heapsort xs = xs))

-- `buildMaxHeap_isHeap_prop` in executable form
#eval Plausible.Testable.check (∀ xs : List Nat,
  (List.range xs.length).all (fun j =>
    j == 0 || (buildMaxHeap xs.toArray)[j]! ≤ (buildMaxHeap xs.toArray)[parent j]!) = true)
#eval Plausible.Testable.check (∀ xs : List Nat, List.Perm (buildMaxHeap xs.toArray).toList xs)
#eval Plausible.Testable.check (∀ i : Nat, parent (left i) = i ∧ parent (right i) = i)
-- `maxHeapify_perm_prop` for all heap sizes `n ≤ xs.length` and start indices `i ≤ xs.length`
-- (larger `n` would read out of bounds at run time, which `a[i]!` reports as a panic)
#eval Plausible.Testable.check (∀ xs : List Nat,
  (List.range (xs.length + 1)).all (fun n => (List.range (xs.length + 1)).all (fun i =>
    decide (List.Perm (maxHeapify xs.toArray i n).toList xs) &&
      ((maxHeapify xs.toArray i n).size == xs.length))) = true)

/-- all lists of length `len` with entries `< k` -/
def allLists (k : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | len + 1 => (allLists k len).flatMap fun xs => (List.range k).map fun x => x :: xs

-- bounded (exhaustive) PBTs: all permutations of `[0,…,5]`, all lists of length `≤ 4` over `{0,…,3}`
example : (List.permutations [0, 1, 2, 3, 4, 5]).all (fun xs =>
    decide ((heapsort xs).Sorted (· ≤ ·)) && decide (List.Perm (heapsort xs) xs) &&
      ((heapsort xs).length == xs.length) && (heapsort xs == xs.mergeSort)) = true := by
  native_decide
example : ((List.range 5).flatMap (allLists 4)).all (fun xs =>
    decide ((heapsort xs).Sorted (· ≤ ·)) && decide (List.Perm (heapsort xs) xs) &&
      ((heapsort xs).length == xs.length) && (heapsort xs == xs.mergeSort) &&
      (!(xs.length ≤ 1) || (heapsort xs == xs))) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem heapsort_correct (arr : List Nat) (_hpre : Pre arr) : Post_prop arr :=
  ⟨heapsort_sorted_thm arr, heapsort_perm_thm arr, heapsort_length_thm arr,
    heapsort_eq_sorted_thm arr, heapsort_short_thm arr⟩

/-! ## Imperative implementation (`Id.run do` with mutable state) -/

/-- Imperative `max_heapify`, mirroring the Python `while True` loop. The loop is bounded by
`heapSize` iterations, which always suffices since `i` strictly increases in every iteration. -/
def maxHeapifyImp (arr : Array Nat) (i₀ heapSize : Nat) : Array Nat := Id.run do
  let mut a := arr
  let mut i := i₀
  for _ in List.range heapSize do
    let l := left i
    let r := right i
    let mut largest := i
    if l < heapSize ∧ a[i]! < a[l]! then
      largest := l
    if r < heapSize ∧ a[largest]! < a[r]! then
      largest := r
    if largest = i then
      break
    a := a.swapIfInBounds i largest
    i := largest
  return a

/-- Imperative `build_max_heap`: `for i in range(parent(n - 1), -1, -1): max_heapify(a, i, n)`. -/
def buildMaxHeapImp (arr : Array Nat) : Array Nat := Id.run do
  let mut a := arr
  let n := a.size
  if n ≤ 1 then
    return a
  for i in (List.range (parent (n - 1) + 1)).reverse do
    a := maxHeapifyImp a i n
  return a

/-- Imperative `heapsort`: `for i in range(n - 1, 0, -1): swap(0, i); max_heapify(a, 0, i)`. -/
def heapsortImp (arr : List Nat) : List Nat := Id.run do
  if arr.length ≤ 1 then
    return arr
  let mut a := buildMaxHeapImp arr.toArray
  for i in (List.range' 1 (arr.length - 1)).reverse do
    a := a.swapIfInBounds 0 i
    a := maxHeapifyImp a 0 i
  return a.toList

/-! ## Imperative tests -/

example : maxHeapifyImp #[1, 5, 3] 0 3 = #[5, 1, 3] := by native_decide
example : maxHeapifyImp #[1, 5, 3, 7, 2] 0 5 = #[5, 7, 3, 1, 2] := by native_decide
example : buildMaxHeapImp #[4, 1, 3, 2, 16, 9, 10, 14, 8, 7] = #[16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by
  native_decide
example : heapsortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsortImp [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsortImp [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by native_decide
example : heapsortImp [] = [] := by native_decide
example : heapsortImp [42] = [42] := by native_decide
example : heapsortImp [2, 1] = [1, 2] := by native_decide
example : heapsortImp [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapsortImp [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by native_decide
example : heapsortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide

#eval heapsortImp [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval Plausible.Testable.check (∀ xs : List Nat, heapsortImp xs = heapsort xs)
example : ((List.range 5).flatMap (allLists 4)).all (fun xs => heapsortImp xs == heapsort xs) = true := by
  native_decide

/-! ## Equivalence: functional = imperative -/

theorem maxHeapify_of_le {a : Array Nat} {i n : Nat} (h : n ≤ i) : maxHeapify a i n = a := by
  apply maxHeapify_of_eq
  unfold largestOf left right
  simp only []
  rw [if_neg (by omega), if_neg (by omega)]

theorem maxHeapify_step {a : Array Nat} {i n g : Nat} (hg : largestOf a i n = g) (hne : g ≠ i) :
    maxHeapify a i n = maxHeapify (a.swapIfInBounds i g) g n := by
  subst hg; exact maxHeapify_of_ne hne

theorem maxHeapifyImp_eq (a : Array Nat) (i n : Nat) : maxHeapifyImp a i n = maxHeapify a i n := by
  unfold maxHeapifyImp
  have hl : n ≤ i + (List.range n).length := by simp
  generalize List.range n = l at hl ⊢
  induction l generalizing a i with
  | nil =>
    simp only [List.forIn_nil, Id.run_bind, Id.run_pure]
    rw [maxHeapify_of_le (by simpa using hl)]
  | cons x l ih =>
    simp only [Id.run_bind, Id.run_pure, pure_bind, if_true] at ih
    simp only [List.forIn_cons, Id.run_bind, Id.run_pure, pure_bind, if_true]
    simp only [List.length_cons] at hl
    split_ifs
    · rename_i h1 h2 h3; exfalso; simp only [right] at h3; omega
    · rename_i h1 h2 h3
      rw [maxHeapify_step (by simp only [largestOf]; rw [if_pos h1, if_pos h2]) h3]
      exact ih _ _ (by simp only [right]; omega)
    · rename_i h1 h2 h3; exfalso; simp only [left] at h3; omega
    · rename_i h1 h2 h3
      rw [maxHeapify_step (by simp only [largestOf]; rw [if_pos h1, if_neg h2]) h3]
      exact ih _ _ (by simp only [left]; omega)
    · rename_i h1 h2 h3; exfalso; simp only [right] at h3; omega
    · rename_i h1 h2 h3
      rw [maxHeapify_step (by simp only [largestOf]; rw [if_neg h1, if_pos h2]) h3]
      exact ih _ _ (by simp only [right]; omega)
    · rename_i h1 h2; symm; apply maxHeapify_of_eq; simp only [largestOf]; rw [if_neg h1, if_neg h2]

theorem forIn_buildLoop (n : Nat) : ∀ (k : Nat) (a : Array Nat),
    (forIn (List.range (k + 1)).reverse a
      (fun i r => pure (ForInStep.yield (maxHeapify r i n))) : Id (Array Nat)).run = buildLoop a n k := by
  intro k
  induction k with
  | zero =>
    intro a
    simp only [List.range_succ, List.range_zero, List.nil_append, List.reverse_singleton,
      List.forIn_cons, List.forIn_nil, Id.run_pure, pure_bind, buildLoop]
  | succ k ih =>
    intro a
    rw [List.range_succ (n := k + 1), List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.forIn_cons]
    simp only [pure_bind]
    rw [buildLoop]
    exact ih _

theorem forIn_extractLoop : ∀ (k : Nat) (a : Array Nat),
    (forIn (List.range' 1 k).reverse a
      (fun i r => pure (ForInStep.yield (maxHeapify (r.swapIfInBounds 0 i) 0 i))) : Id (Array Nat)).run
      = extractLoop a k := by
  intro k
  induction k with
  | zero => intro a; simp only [List.range'_zero, List.reverse_nil, List.forIn_nil, Id.run_pure, extractLoop]
  | succ k ih =>
    intro a
    rw [List.range'_concat, show 1 + 1 * k = k + 1 by omega, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.forIn_cons]
    simp only [pure_bind]
    rw [extractLoop]
    exact ih _

theorem buildMaxHeapImp_eq (a : Array Nat) : buildMaxHeapImp a = buildMaxHeap a := by
  unfold buildMaxHeapImp buildMaxHeap
  simp only [maxHeapifyImp_eq]
  split_ifs with h
  · rfl
  · simp only [Id.run_bind, Id.run_pure, pure_bind]
    exact forIn_buildLoop a.size (parent (a.size - 1)) a

theorem heapsortImp_eq (arr : List Nat) : heapsortImp arr = heapsort arr := by
  unfold heapsortImp heapsort heapsortArr
  simp only [maxHeapifyImp_eq, buildMaxHeapImp_eq, List.size_toArray]
  split_ifs with h
  · simp
  · simp only [Id.run_bind, Id.run_pure, pure_bind]
    rw [← forIn_extractLoop]

/-- Equivalence of the functional and the imperative implementation. -/
theorem heapsort_eq_heapsortImp_thm (arr : List Nat) : heapsort arr = heapsortImp arr :=
  (heapsortImp_eq arr).symm

end heapsort_algorithm
