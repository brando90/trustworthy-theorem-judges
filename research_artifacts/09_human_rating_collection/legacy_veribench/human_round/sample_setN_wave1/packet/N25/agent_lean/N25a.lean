import Mathlib

set_option linter.dupNamespace false
set_option linter.deprecated false

/-!
# Heap Sort

Formalization of the Python `heap_sort` program in Lean 4.
Sorts a list of integers in ascending order by first building a binary max-heap
and then repeatedly extracting the maximum element to the end of the list.
-/

namespace heap_sort

/-! ## 1. Functional Implementation -/

/-- Swap two elements at indices `i` and `j` in a list of integers. -/
def swap (arr : List Int) (i j : Nat) : List Int :=
  if i < arr.length ∧ j < arr.length then
    let vi := arr[i]!
    let vj := arr[j]!
    (arr.set i vj).set j vi
  else
    arr

/-- Sift-down helper with explicit fuel `fuel` for subtree rooted at `i` within heap size `n`. -/
def heapifyAux : Nat → List Int → Nat → Nat → List Int
  | 0, arr, _, _ => arr
  | fuel + 1, arr, n, i =>
    let left := 2 * i + 1
    let right := 2 * i + 2
    let largest1 := if left < n ∧ arr[left]! > arr[i]! then left else i
    let largest2 := if right < n ∧ arr[right]! > arr[largest1]! then right else largest1
    if largest2 ≠ i then
      heapifyAux fuel (swap arr i largest2) n largest2
    else
      arr

/-- Maintain the max-heap property for the subtree rooted at `i` within heap size `n`. -/
def heapify (arr : List Int) (n i : Nat) : List Int :=
  heapifyAux (n - i) arr n i

/-- Helper loop to heapify non-leaf nodes from `k - 1` down to `0`. -/
def buildMaxHeapLoop (arr : List Int) (n : Nat) : Nat → List Int
  | 0 => arr
  | k + 1 => buildMaxHeapLoop (heapify arr n k) n k

/-- Build a binary max-heap from a list of integers. -/
def build_max_heap (arr : List Int) : List Int :=
  let n := arr.length
  buildMaxHeapLoop arr n (n / 2)

/-- Helper loop to extract the maximum element from the heap `m - 1` down to `1`. -/
def extractMaxLoop (arr : List Int) : Nat → List Int
  | 0 => arr
  | 1 => arr
  | i + 2 => extractMaxLoop (heapify (swap arr 0 (i + 1)) (i + 1) 0) (i + 1)

/-- Sort a list of integers in ascending order using the heap sort algorithm. -/
def heap_sort (arr : List Int) : List Int :=
  if arr.length ≤ 1 then
    arr
  else
    let n := arr.length
    let result := build_max_heap arr
    extractMaxLoop result n

/-! ## 2. Unit Tests -/

#eval heap_sort [3, 1, 2]
#eval heap_sort []
#eval heap_sort [1]
#eval heap_sort [5, 2, 4, 6, 1, 3]
#eval heap_sort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

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
example : heap_sort [-3, 0, -1, 5, 2, -3] = [-3, -3, -1, 0, 2, 5] := by native_decide

/-! ## 3. Pre-condition -/

/-- Executable pre-condition check (all elements are integers in `List Int`). -/
def pre (_arr : List Int) : Bool := true

/-- Pre-condition predicate for `heap_sort`. Any `List Int` is an admissible input. -/
def Pre (_arr : List Int) : Prop := True

/-! ## 4. Helper Lemmas for Heap Invariants, Permutation, and Sortedness -/

theorem length_swap (arr : List Int) (i j : Nat) : (swap arr i j).length = arr.length := by
  unfold swap; split <;> simp

theorem getElem!_eq_getElem (l : List Int) (i : Nat) (h : i < l.length) :
    l[i]! = l[i] := by
  simp [h]

theorem getElem!_set (l : List Int) (i k : Nat) (x : Int) (hk : k < l.length) :
    (l.set i x)[k]! = if i = k then x else l[k]! := by
  have hk' : k < (l.set i x).length := by simp [hk]
  rw [getElem!_eq_getElem _ _ hk', List.getElem_set, getElem!_eq_getElem _ _ hk]

theorem getElem!_swap (arr : List Int) (i j k : Nat)
    (hi : i < arr.length) (hj : j < arr.length) (hk : k < arr.length) :
    (swap arr i j)[k]! = if k = j then arr[i]! else if k = i then arr[j]! else arr[k]! := by
  unfold swap
  rw [if_pos ⟨hi, hj⟩]
  have hk' : k < (arr.set i arr[j]!).length := by simp [hk]
  rw [getElem!_set _ _ _ _ hk', getElem!_set _ _ _ _ hk]
  by_cases hkj : k = j
  · subst hkj; simp
  · by_cases hki : k = i
    · subst hki; simp [hkj, Ne.symm hkj]
    · simp [hkj, hki, Ne.symm hkj, Ne.symm hki]

theorem cons_perm_set (l : List Int) (i : Nat) (hi : i < l.length) (x : Int) :
    l[i] :: l.set i x ~ x :: l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero =>
      simp [List.Perm.swap]
    | succ k =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      simp only [List.getElem_cons_succ, List.set_cons_succ]
      calc as[k] :: a :: as.set k x
        _ ~ a :: as[k] :: as.set k x := List.Perm.swap _ _ _
        _ ~ a :: x :: as := List.Perm.cons a (ih k hi)
        _ ~ x :: a :: as := List.Perm.swap _ _ _

theorem perm_swap (arr : List Int) (i j : Nat) : (swap arr i j).Perm arr := by
  unfold swap
  split
  · rename_i h
    rcases h with ⟨hi, hj⟩
    by_cases hij : i = j
    · subst hij
      simp [getElem!_eq_getElem arr i hi]
    · have h1 := cons_perm_set (arr.set i arr[j]!) j (by simp [hj]) arr[i]!
      have h2 := cons_perm_set arr i hi arr[j]!
      rw [← getElem!_eq_getElem arr i hi] at h2
      have h3 : (arr.set i arr[j]!)[j] = arr[j]! := by
        rw [List.getElem_set, if_neg hij, getElem!_eq_getElem arr j hj]
      rw [h3] at h1
      have h4 : arr[j]! :: (arr.set i arr[j]!).set j arr[i]! ~ arr[j]! :: arr :=
        h1.trans h2
      exact List.Perm.cons_inv h4
  · exact List.Perm.refl _

theorem length_heapifyAux (fuel : Nat) (arr : List Int) (n i : Nat) :
    (heapifyAux fuel arr n i).length = arr.length := by
  induction fuel generalizing arr i with
  | zero => rfl
  | succ fuel ih =>
    unfold heapifyAux
    dsimp only
    split
    · rw [ih, length_swap]
    · rfl

theorem perm_heapifyAux (fuel : Nat) (arr : List Int) (n i : Nat) :
    (heapifyAux fuel arr n i).Perm arr := by
  induction fuel generalizing arr i with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    unfold heapifyAux
    dsimp only
    split
    · exact (ih _ _).trans (perm_swap arr i _)
    · exact List.Perm.refl _

theorem length_heapify (arr : List Int) (n i : Nat) : (heapify arr n i).length = arr.length :=
  length_heapifyAux (n - i) arr n i

theorem perm_heapify (arr : List Int) (n i : Nat) : (heapify arr n i).Perm arr :=
  perm_heapifyAux (n - i) arr n i

theorem child_eq_left_or_right (c i : Nat) (hc : 0 < c) (hp : (c - 1) / 2 = i) :
    c = 2 * i + 1 ∨ c = 2 * i + 2 := by
  omega

theorem heapify_step_bounds (arr : List Int) (n i : Nat) :
    let left := 2 * i + 1
    let right := 2 * i + 2
    let largest1 := if left < n ∧ arr[left]! > arr[i]! then left else i
    let largest2 := if right < n ∧ arr[right]! > arr[largest1]! then right else largest1
    arr[i]! ≤ arr[largest2]! ∧
    (left < n → arr[left]! ≤ arr[largest2]!) ∧
    (right < n → arr[right]! ≤ arr[largest2]!) ∧
    (largest2 ≠ i → 0 < largest2 ∧ largest2 < n ∧ (largest2 - 1) / 2 = i) := by
  intro left right largest1 largest2
  have h1 : arr[i]! ≤ arr[largest1]! := by dsimp [largest1]; split <;> omega
  have h2 : left < n → arr[left]! ≤ arr[largest1]! := by intro hl; dsimp [largest1]; split <;> omega
  have h3 : arr[largest1]! ≤ arr[largest2]! := by dsimp [largest2]; split <;> omega
  have h4 : right < n → arr[right]! ≤ arr[largest2]! := by intro hr; dsimp [largest2]; split <;> omega
  have h5 : largest2 ≠ i → 0 < largest2 ∧ largest2 < n ∧ (largest2 - 1) / 2 = i := by
    dsimp [largest2, largest1, left, right]; split <;> split <;> omega
  exact ⟨by omega, fun hl => by have := h2 hl; omega, h4, h5⟩

theorem getElem!_heapifyAux_of_ge (fuel : Nat) (arr : List Int) (n i k : Nat)
    (hn : n ≤ arr.length) (hk : n ≤ k) (hkl : k < arr.length) :
    (heapifyAux fuel arr n i)[k]! = arr[k]! := by
  induction fuel generalizing arr i with
  | zero => rfl
  | succ fuel ih =>
    unfold heapifyAux
    have hbounds := heapify_step_bounds arr n i
    dsimp only at hbounds ⊢
    split
    · rename_i hne
      rcases hbounds.2.2.2 hne with ⟨hlarg_pos, hlarg_lt, hlarg_p⟩
      have hi_lt : i < arr.length := by omega
      have hlarg_lt_len : _ < arr.length := by omega
      have hn' : n ≤ (swap arr i _).length := by rw [length_swap]; exact hn
      have hkl' : k < (swap arr i _).length := by rw [length_swap]; exact hkl
      rw [ih _ _ hn' hkl', getElem!_swap arr i _ k hi_lt hlarg_lt_len hkl]
      rw [if_neg (by omega), if_neg (by omega)]
    · rfl

theorem getElem!_heapify_of_ge (arr : List Int) (n i k : Nat)
    (hn : n ≤ arr.length) (hk : n ≤ k) (hkl : k < arr.length) :
    (heapify arr n i)[k]! = arr[k]! :=
  getElem!_heapifyAux_of_ge (n - i) arr n i k hn hk hkl

theorem getElem!_heapifyAux_mem (fuel : Nat) (arr : List Int) (n i k : Nat)
    (hn : n ≤ arr.length) (hk : k < n) :
    ∃ j < n, (heapifyAux fuel arr n i)[k]! = arr[j]! := by
  induction fuel generalizing arr i k with
  | zero => exact ⟨k, hk, rfl⟩
  | succ fuel ih =>
    unfold heapifyAux
    have hbounds := heapify_step_bounds arr n i
    dsimp only at hbounds ⊢
    split
    · rename_i hne
      rcases hbounds.2.2.2 hne with ⟨hlarg_pos, hlarg_lt, hlarg_p⟩
      have hi_lt_n : i < n := by omega
      have hi_lt : i < arr.length := by omega
      have hlarg_lt_len : _ < arr.length := by omega
      have hn' : n ≤ (swap arr i _).length := by rw [length_swap]; exact hn
      obtain ⟨j, hj, heq⟩ := ih (swap arr i _) _ k hn' hk
      rw [heq, getElem!_swap arr i _ j hi_lt hlarg_lt_len (by omega)]
      split
      · exact ⟨i, hi_lt_n, rfl⟩
      · split
        · exact ⟨_, hlarg_lt, rfl⟩
        · exact ⟨j, hj, rfl⟩
    · exact ⟨k, hk, rfl⟩

theorem getElem!_heapify_mem (arr : List Int) (n i k : Nat)
    (hn : n ≤ arr.length) (hk : k < n) :
    ∃ j < n, (heapify arr n i)[k]! = arr[j]! :=
  getElem!_heapifyAux_mem (n - i) arr n i k hn hk

/-- Partial max-heap invariant: all nodes `c < n` whose parent `(c - 1) / 2 ≥ start_i`
    satisfy `arr[c]! ≤ arr[(c - 1) / 2]!`. -/
def IsPartialHeap (arr : List Int) (n start_i : Nat) : Prop :=
  ∀ c, 0 < c → c < n → start_i ≤ (c - 1) / 2 → arr[c]! ≤ arr[(c - 1) / 2]!

/-- Floyd's sift-down invariant during `heapify` starting at `start_i` with current node `cur`. -/
def AlmostHeap (arr : List Int) (n start_i cur : Nat) : Prop :=
  start_i ≤ cur ∧
  (∀ c, 0 < c → c < n → start_i ≤ (c - 1) / 2 → (c - 1) / 2 ≠ cur → arr[c]! ≤ arr[(c - 1) / 2]!) ∧
  (∀ d, 0 < d → d < n → (d - 1) / 2 = cur → start_i < cur → arr[d]! ≤ arr[(cur - 1) / 2]!)

theorem almostHeap_swap_step (arr : List Int) (n start_i i largest : Nat)
    (hn : n ≤ arr.length)
    (halmost : AlmostHeap arr n start_i i)
    (hlarg_pos : 0 < largest) (hlarg_lt : largest < n) (hlarg_p : (largest - 1) / 2 = i)
    (hi_le : arr[i]! ≤ arr[largest]!)
    (hchild_le : ∀ c, 0 < c → c < n → (c - 1) / 2 = i → arr[c]! ≤ arr[largest]!) :
    AlmostHeap (swap arr i largest) n start_i largest := by
  rcases halmost with ⟨hstart_le, hheap_other, hgrand⟩
  have hi_lt : i < arr.length := by omega
  have hlarg_lt_len : largest < arr.length := by omega
  refine ⟨by omega, ?_, ?_⟩
  · intro c hc0 hcn hstart_c hne_larg
    have hcl : c < arr.length := by omega
    have hpl : (c - 1) / 2 < arr.length := by omega
    rw [getElem!_swap arr i largest c hi_lt hlarg_lt_len hcl,
        getElem!_swap arr i largest ((c - 1) / 2) hi_lt hlarg_lt_len hpl]
    rw [if_neg hne_larg]
    by_cases hpi : (c - 1) / 2 = i
    · rw [if_pos hpi]
      by_cases hclarg : c = largest
      · rw [if_pos hclarg]; exact hi_le
      · rw [if_neg hclarg, if_neg (by omega)]
        exact hchild_le c hc0 hcn hpi
    · rw [if_neg hpi, if_neg (by omega)]
      by_cases hci : c = i
      · rw [if_pos hci]
        exact hgrand largest hlarg_pos hlarg_lt hlarg_p (by omega)
      · rw [if_neg hci]
        exact hheap_other c hc0 hcn hstart_c hpi
  · intro d hd0 hdn hdp _
    have hdl : d < arr.length := by omega
    have hpl : (largest - 1) / 2 < arr.length := by omega
    rw [getElem!_swap arr i largest d hi_lt hlarg_lt_len hdl,
        getElem!_swap arr i largest ((largest - 1) / 2) hi_lt hlarg_lt_len hpl]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hlarg_p]
    have hother := hheap_other d hd0 hdn (by omega) (by omega)
    rwa [hdp] at hother

theorem heapifyAux_almostHeap (fuel : Nat) (arr : List Int) (n start_i i : Nat)
    (hfuel : n - i ≤ fuel) (hn : n ≤ arr.length) (halmost : AlmostHeap arr n start_i i) :
    IsPartialHeap (heapifyAux fuel arr n i) n start_i := by
  induction fuel generalizing arr i with
  | zero =>
    unfold heapifyAux
    intro c hc0 hcn hstart_c
    have hne : (c - 1) / 2 ≠ i := by omega
    exact halmost.2.1 c hc0 hcn hstart_c hne
  | succ fuel ih =>
    unfold heapifyAux
    have hbounds := heapify_step_bounds arr n i
    dsimp only at hbounds ⊢
    rcases hbounds with ⟨hi_le, hleft_le, hright_le, hlarg_info⟩
    split
    · rename_i hne
      rcases hlarg_info hne with ⟨hlarg_pos, hlarg_lt, hlarg_p⟩
      have hchild_le : ∀ c, 0 < c → c < n → (c - 1) / 2 = i → arr[c]! ≤ _ := by
        intro c hc0 hcn hcp
        rcases child_eq_left_or_right c i hc0 hcp with rfl | rfl
        · exact hleft_le hcn
        · exact hright_le hcn
      have halmost' := almostHeap_swap_step arr n start_i i _ hn halmost
        hlarg_pos hlarg_lt hlarg_p hi_le hchild_le
      have hn' : n ≤ (swap arr i _).length := by rw [length_swap]; exact hn
      exact ih (swap arr i _) _ (by omega) hn' halmost'
    · rename_i hnot_ne
      push_neg at hnot_ne
      intro c hc0 hcn hstart_c
      by_cases hcp : (c - 1) / 2 = i
      · rw [hcp, ← hnot_ne]
        rcases child_eq_left_or_right c i hc0 hcp with rfl | rfl
        · exact hleft_le hcn
        · exact hright_le hcn
      · exact halmost.2.1 c hc0 hcn hstart_c hcp

theorem heapify_isPartialHeap (arr : List Int) (n i : Nat)
    (hn : n ≤ arr.length) (hpart : IsPartialHeap arr n (i + 1)) :
    IsPartialHeap (heapify arr n i) n i := by
  apply heapifyAux_almostHeap (n - i) arr n i i (le_refl _) hn
  refine ⟨le_refl i, ?_, ?_⟩
  · intro c hc0 hcn hi_le hne
    exact hpart c hc0 hcn (by omega)
  · intro d _ _ _ hlt
    omega

theorem length_buildMaxHeapLoop (arr : List Int) (n k : Nat) :
    (buildMaxHeapLoop arr n k).length = arr.length := by
  induction k generalizing arr with
  | zero => rfl
  | succ k ih =>
    simp only [buildMaxHeapLoop, ih, length_heapify]

theorem perm_buildMaxHeapLoop (arr : List Int) (n k : Nat) :
    (buildMaxHeapLoop arr n k).Perm arr := by
  induction k generalizing arr with
  | zero => exact List.Perm.refl _
  | succ k ih =>
    simp only [buildMaxHeapLoop]
    exact (ih (heapify arr n k)).trans (perm_heapify arr n k)

theorem buildMaxHeapLoop_isPartialHeap (arr : List Int) (n k : Nat)
    (hn : n ≤ arr.length) (hpart : IsPartialHeap arr n k) :
    IsPartialHeap (buildMaxHeapLoop arr n k) n 0 := by
  induction k generalizing arr with
  | zero => exact hpart
  | succ k ih =>
    simp only [buildMaxHeapLoop]
    have hpart' := heapify_isPartialHeap arr n k hn hpart
    have hn' : n ≤ (heapify arr n k).length := by rw [length_heapify]; exact hn
    exact ih (heapify arr n k) hn' hpart'

theorem length_build_max_heap (arr : List Int) :
    (build_max_heap arr).length = arr.length :=
  length_buildMaxHeapLoop arr arr.length (arr.length / 2)

theorem perm_build_max_heap (arr : List Int) :
    (build_max_heap arr).Perm arr :=
  perm_buildMaxHeapLoop arr arr.length (arr.length / 2)

theorem build_max_heap_isPartialHeap (arr : List Int) :
    IsPartialHeap (build_max_heap arr) arr.length 0 := by
  apply buildMaxHeapLoop_isPartialHeap arr arr.length (arr.length / 2) (le_refl _)
  intro c hc0 hcn hge
  omega

theorem max_of_isPartialHeap_zero (arr : List Int) (n c : Nat)
    (hheap : IsPartialHeap arr n 0) (hc : c < n) :
    arr[c]! ≤ arr[0]! := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    by_cases hc0 : c = 0
    · subst hc0; exact le_refl _
    · have hc_pos : 0 < c := by omega
      have hp_lt : (c - 1) / 2 < c := by omega
      have hp_lt_n : (c - 1) / 2 < n := by omega
      have h1 := hheap c hc_pos hc (by omega)
      have h2 := ih ((c - 1) / 2) hp_lt hp_lt_n
      exact le_trans h1 h2

theorem length_extractMaxLoop (arr : List Int) (m : Nat) :
    (extractMaxLoop arr m).length = arr.length := by
  induction m generalizing arr with
  | zero => rfl
  | succ m ih =>
    cases m with
    | zero => rfl
    | succ i =>
      simp only [extractMaxLoop, ih, length_heapify, length_swap]

theorem perm_extractMaxLoop (arr : List Int) (m : Nat) :
    (extractMaxLoop arr m).Perm arr := by
  induction m generalizing arr with
  | zero => exact List.Perm.refl _
  | succ m ih =>
    cases m with
    | zero => exact List.Perm.refl _
    | succ i =>
      simp only [extractMaxLoop]
      exact (ih _).trans ((perm_heapify _ _ _).trans (perm_swap arr 0 (i + 1)))

/-- Invariant of the extraction loop: prefix `0..m` is a max-heap, suffix `m..n` is sorted,
    and all elements in `0..m` are `≤` all elements in `m..n`. -/
def ExtractInv (arr : List Int) (m : Nat) : Prop :=
  m ≤ arr.length ∧
  IsPartialHeap arr m 0 ∧
  (∀ a b, m ≤ a → a < b → b < arr.length → arr[a]! ≤ arr[b]!) ∧
  (∀ a b, a < m → m ≤ b → b < arr.length → arr[a]! ≤ arr[b]!)

theorem extractInv_step (arr : List Int) (i : Nat) (hi_pos : 0 < i)
    (hinv : ExtractInv arr (i + 1)) :
    ExtractInv (heapify (swap arr 0 i) i 0) i := by
  rcases hinv with ⟨hlen, hheap, hsorted, hsplit⟩
  set arr1 := swap arr 0 i
  set arr2 := heapify arr1 i 0
  have hlen1 : arr1.length = arr.length := length_swap arr 0 i
  have hlen2 : arr2.length = arr.length := by rw [length_heapify, hlen1]
  have h0_lt : 0 < arr.length := by omega
  have hi_lt : i < arr.length := by omega
  have hpart1 : IsPartialHeap arr1 i 1 := by
    intro c hc0 hci hp1
    have hcl : c < arr.length := by omega
    have hpl : (c - 1) / 2 < arr.length := by omega
    dsimp [arr1]
    rw [getElem!_swap arr 0 i c h0_lt hi_lt hcl,
        getElem!_swap arr 0 i ((c - 1) / 2) h0_lt hi_lt hpl]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hheap c hc0 (by omega) (by omega)
  have hpart2 : IsPartialHeap arr2 i 0 :=
    heapify_isPartialHeap arr1 i 0 (by omega) hpart1
  refine ⟨by omega, hpart2, ?_, ?_⟩
  · intro a b ha hb hbl
    have hbl' : b < arr.length := by omega
    have hal' : a < arr.length := by omega
    have ha2 : arr2[a]! = arr1[a]! := getElem!_heapify_of_ge arr1 i 0 a (by omega) ha (by omega)
    have hb2 : arr2[b]! = arr1[b]! := getElem!_heapify_of_ge arr1 i 0 b (by omega) (by omega) (by omega)
    rw [ha2, hb2]
    dsimp [arr1]
    rw [getElem!_swap arr 0 i a h0_lt hi_lt hal',
        getElem!_swap arr 0 i b h0_lt hi_lt hbl']
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases hai : a = i
    · rw [if_pos hai]
      exact hsplit 0 b (by omega) (by omega) hbl'
    · rw [if_neg hai, if_neg (by omega)]
      exact hsorted a b (by omega) hb hbl'
  · intro a b ha hb hbl
    have hbl' : b < arr.length := by omega
    obtain ⟨j, hj, haj⟩ := getElem!_heapify_mem arr1 i 0 a (by omega) ha
    have hb2 : arr2[b]! = arr1[b]! := getElem!_heapify_of_ge arr1 i 0 b (by omega) hb (by omega)
    rw [haj, hb2]
    have hjl : j < arr.length := by omega
    have h_arr1_j : ∃ k < i + 1, arr1[j]! = arr[k]! := by
      dsimp [arr1]
      rw [getElem!_swap arr 0 i j h0_lt hi_lt hjl]
      rw [if_neg (by omega)]
      by_cases hj0 : j = 0
      · rw [if_pos hj0]; exact ⟨i, by omega, rfl⟩
      · rw [if_neg hj0]; exact ⟨j, by omega, rfl⟩
    rcases h_arr1_j with ⟨k, hk, hkj⟩
    rw [hkj]
    dsimp [arr1]
    rw [getElem!_swap arr 0 i b h0_lt hi_lt hbl']
    by_cases hbi : b = i
    · rw [if_pos hbi]
      exact max_of_isPartialHeap_zero arr (i + 1) k hheap hk
    · rw [if_neg hbi, if_neg (by omega)]
      exact hsplit k b hk (by omega) hbl'

theorem extractMaxLoop_sorted (arr : List Int) (m : Nat) (hinv : ExtractInv arr m) :
    ∀ a b, a < b → b < (extractMaxLoop arr m).length →
      (extractMaxLoop arr m)[a]! ≤ (extractMaxLoop arr m)[b]! := by
  induction m generalizing arr with
  | zero =>
    intro a b hab hbl
    exact hinv.2.2.1 a b (by omega) hab hbl
  | succ m ih =>
    cases m with
    | zero =>
      intro a b hab hbl
      by_cases ha0 : a = 0
      · subst ha0
        exact hinv.2.2.2 0 b (by omega) (by omega) hbl
      · exact hinv.2.2.1 a b (by omega) hab hbl
    | succ i =>
      simp only [extractMaxLoop]
      exact ih _ (extractInv_step arr (i + 1) (by omega) hinv)

theorem eq_of_perm_of_sorted {l₁ l₂ : List Int}
    (hp : l₁.Perm l₂)
    (hs₁ : List.Pairwise (· ≤ ·) l₁)
    (hs₂ : List.Pairwise (· ≤ ·) l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => exact hp.nil_eq
  | cons a as ih =>
    cases l₂ with
    | nil => cases hp.symm.nil_eq
    | cons b bs =>
      have ha_mem : a ∈ b :: bs := hp.subset (by simp)
      have hb_mem : b ∈ a :: as := hp.symm.subset (by simp)
      have hab : a = b := by
        rcases List.mem_cons.mp ha_mem with rfl | ha_bs
        · rfl
        · rcases List.mem_cons.mp hb_mem with rfl | hb_as
          · rfl
          · have h1 : a ≤ b := (List.pairwise_cons.mp hs₁).1 b hb_as
            have h2 : b ≤ a := (List.pairwise_cons.mp hs₂).1 a ha_bs
            omega
      subst hab
      congr 1
      exact ih hp.cons_inv (List.pairwise_cons.mp hs₁).2 (List.pairwise_cons.mp hs₂).2

theorem head_le_of_sorted {l : List Int} (h : l ≠ []) (hs : List.Pairwise (· ≤ ·) l)
    {x : Int} (hx : x ∈ l) : l.head h ≤ x := by
  cases l with
  | nil => contradiction
  | cons a as =>
    simp only [List.head_cons]
    rcases List.mem_cons.mp hx with rfl | hx_as
    · exact le_refl _
    · exact (List.pairwise_cons.mp hs).1 x hx_as

theorem le_getLast_of_sorted {l : List Int} (h : l ≠ []) (hs : List.Pairwise (· ≤ ·) l)
    {x : Int} (hx : x ∈ l) : x ≤ l.getLast h := by
  induction l generalizing x with
  | nil => contradiction
  | cons a as ih =>
    cases as with
    | nil =>
      simp only [List.mem_singleton] at hx
      subst hx
      simp
    | cons b bs =>
      have hne : b :: bs ≠ [] := List.cons_ne_nil b bs
      rw [List.getLast_cons hne]
      rcases List.mem_cons.mp hx with rfl | hx_tail
      · have hab : a ≤ b := (List.pairwise_cons.mp hs).1 b (by simp)
        have hbl : b ≤ (b :: bs).getLast hne := ih hne (List.pairwise_cons.mp hs).2 (by simp)
        exact le_trans hab hbl
      · exact ih hne (List.pairwise_cons.mp hs).2 hx_tail

/-! ## 5. Property Propositions and Theorems -/

/-- Property 1: The output of `heap_sort` is sorted in non-decreasing order. -/
def sorted_prop (arr : List Int) : Prop :=
  List.Pairwise (· ≤ ·) (heap_sort arr)

theorem sorted_thm (arr : List Int) : sorted_prop arr := by
  unfold sorted_prop
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab
  rw [← getElem!_eq_getElem _ a ha, ← getElem!_eq_getElem _ b hb]
  unfold heap_sort at ha hb ⊢
  split
  · rename_i hle
    rw [if_pos hle] at ha hb
    omega
  · rename_i hgt
    rw [if_neg hgt] at hb
    apply extractMaxLoop_sorted (build_max_heap arr) arr.length _ a b hab hb
    refine ⟨by simp [length_build_max_heap], build_max_heap_isPartialHeap arr, ?_, ?_⟩
    · intro x y hx _ hy
      rw [length_build_max_heap] at hy
      omega
    · intro x y _ hy hyl
      rw [length_build_max_heap] at hyl
      omega

/-- Property 2: The output of `heap_sort` is a permutation of the input list. -/
def perm_prop (arr : List Int) : Prop :=
  (heap_sort arr).Perm arr

theorem perm_thm (arr : List Int) : perm_prop arr := by
  unfold perm_prop heap_sort
  split
  · exact List.Perm.refl _
  · exact (perm_extractMaxLoop (build_max_heap arr) arr.length).trans (perm_build_max_heap arr)

/-- Property 3: `heap_sort` preserves the length of the input list. -/
def length_prop (arr : List Int) : Prop :=
  (heap_sort arr).length = arr.length

theorem length_thm (arr : List Int) : length_prop arr :=
  (perm_thm arr).length_eq

/-- Property 4: `heap_sort` preserves element membership. -/
def mem_prop (arr : List Int) : Prop :=
  ∀ x : Int, x ∈ heap_sort arr ↔ x ∈ arr

theorem mem_thm (arr : List Int) : mem_prop arr :=
  fun _ => (perm_thm arr).mem_iff

/-- Property 5: `heap_sort` preserves the multiplicity (count) of every integer. -/
def count_prop (arr : List Int) : Prop :=
  ∀ x : Int, (heap_sort arr).count x = arr.count x

theorem count_thm (arr : List Int) : count_prop arr :=
  fun x => List.perm_iff_count.mp (perm_thm arr) x

/-- Property 6: Lists of length at most 1 are returned unchanged. -/
def base_case_prop (arr : List Int) : Prop :=
  arr.length ≤ 1 → heap_sort arr = arr

theorem base_case_thm (arr : List Int) : base_case_prop arr := by
  intro h
  unfold heap_sort
  exact if_pos h

/-- Property 7: Sorting the empty list yields the empty list. -/
def empty_prop : Prop :=
  heap_sort [] = []

theorem empty_thm : empty_prop := rfl

/-- Property 8: Sorting a single-element list yields the same single-element list. -/
def singleton_prop (x : Int) : Prop :=
  heap_sort [x] = [x]

theorem singleton_thm (x : Int) : singleton_prop x := rfl

/-- Property 9: If the input list is already sorted, `heap_sort` returns it unchanged. -/
def already_sorted_prop (arr : List Int) : Prop :=
  List.Pairwise (· ≤ ·) arr → heap_sort arr = arr

theorem already_sorted_thm (arr : List Int) : already_sorted_prop arr :=
  fun hsorted => eq_of_perm_of_sorted (perm_thm arr) (sorted_thm arr) hsorted

/-- Property 10: `heap_sort` is idempotent. -/
def idempotent_prop (arr : List Int) : Prop :=
  heap_sort (heap_sort arr) = heap_sort arr

theorem idempotent_thm (arr : List Int) : idempotent_prop arr :=
  already_sorted_thm (heap_sort arr) (sorted_thm arr)

/-- Property 11: Permuted inputs produce identical sorted outputs. -/
def perm_invariant_prop (arr₁ arr₂ : List Int) : Prop :=
  arr₁.Perm arr₂ → heap_sort arr₁ = heap_sort arr₂

theorem perm_invariant_thm (arr₁ arr₂ : List Int) : perm_invariant_prop arr₁ arr₂ :=
  fun hperm =>
    eq_of_perm_of_sorted
      ((perm_thm arr₁).trans (hperm.trans (perm_thm arr₂).symm))
      (sorted_thm arr₁)
      (sorted_thm arr₂)

/-- Property 12: For any non-empty result, the first element is the minimum and the last is the maximum. -/
def bounds_prop (arr : List Int) : Prop :=
  ∀ h : heap_sort arr ≠ [], ∀ x ∈ arr,
    (heap_sort arr).head h ≤ x ∧ x ≤ (heap_sort arr).getLast h

theorem bounds_thm (arr : List Int) : bounds_prop arr := by
  intro h x hx
  have hx' : x ∈ heap_sort arr := (mem_thm arr x).mpr hx
  exact ⟨head_le_of_sorted h (sorted_thm arr) hx', le_getLast_of_sorted h (sorted_thm arr) hx'⟩

/-- Property 13: `build_max_heap` produces a valid max-heap that is a permutation of the input. -/
def build_max_heap_prop (arr : List Int) : Prop :=
  (build_max_heap arr).Perm arr ∧
  (build_max_heap arr).length = arr.length ∧
  IsPartialHeap (build_max_heap arr) arr.length 0

theorem build_max_heap_thm (arr : List Int) : build_max_heap_prop arr :=
  ⟨perm_build_max_heap arr, length_build_max_heap arr, build_max_heap_isPartialHeap arr⟩

/-! ## 6. Post-condition -/

/-- Full post-condition conjunction of properties for `heap_sort`. -/
def Post_prop (arr : List Int) : Prop :=
  sorted_prop arr ∧
  perm_prop arr ∧
  length_prop arr ∧
  mem_prop arr ∧
  count_prop arr ∧
  base_case_prop arr ∧
  idempotent_prop arr ∧
  already_sorted_prop arr ∧
  bounds_prop arr ∧
  build_max_heap_prop arr

/-! ## 7. Property-Based Tests -/

/-- Executable check that a list of integers is sorted in non-decreasing order. -/
def isSortedBool : List Int → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a ≤ b) && isSortedBool (b :: rest)

/-- Executable check that two lists are permutations of each other. -/
def isPermBool (l₁ l₂ : List Int) : Bool :=
  l₁.length == l₂.length && l₁.all (fun x => l₁.count x == l₂.count x)

/-- Executable check that `arr` satisfies the max-heap property of size `arr.length`. -/
def isMaxHeapBool (arr : List Int) : Bool :=
  (List.range arr.length).all (fun c =>
    if c == 0 then true else arr[c]! ≤ arr[(c - 1) / 2]!)

-- PBT for `sorted_prop`
#eval Plausible.Testable.check (∀ arr : List Int, isSortedBool (heap_sort arr) = true)

-- PBT for `perm_prop`
#eval Plausible.Testable.check (∀ arr : List Int, isPermBool (heap_sort arr) arr = true)

-- PBT for `length_prop`
#eval Plausible.Testable.check (∀ arr : List Int, (heap_sort arr).length = arr.length)

-- PBT for `mem_prop`
#eval Plausible.Testable.check (∀ (arr : List Int) (x : Int), (x ∈ heap_sort arr) ↔ (x ∈ arr))

-- PBT for `count_prop`
#eval Plausible.Testable.check (∀ (arr : List Int) (x : Int), (heap_sort arr).count x = arr.count x)

-- PBT for `base_case_prop`
#eval Plausible.Testable.check (∀ arr : List Int, (arr.take 1).length ≤ 1 ∧ heap_sort (arr.take 1) = arr.take 1)
example : ([[]] ++ (List.range 20).map (fun n => [Int.ofNat n])).all
    (fun arr => heap_sort arr == arr) = true := by native_decide

-- PBT for `empty_prop`
example : heap_sort [] = [] := by native_decide

-- PBT for `singleton_prop`
#eval Plausible.Testable.check (∀ x : Int, heap_sort [x] = [x])

-- PBT for `already_sorted_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  let s := heap_sort arr; isSortedBool s = true ∧ heap_sort s = s)

-- PBT for `idempotent_prop`
#eval Plausible.Testable.check (∀ arr : List Int, heap_sort (heap_sort arr) = heap_sort arr)

-- PBT for `perm_invariant_prop`
#eval Plausible.Testable.check (∀ arr : List Int, heap_sort arr.reverse = heap_sort arr)

-- PBT for `bounds_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  let s := heap_sort arr
  arr.all (fun x => s.head! ≤ x && x ≤ s.getLast!) = true)

-- PBT for `build_max_heap_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  let h := build_max_heap arr
  isPermBool h arr = true ∧ h.length = arr.length ∧ isMaxHeapBool h = true)

-- PBT for `Post_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  let s := heap_sort arr
  isSortedBool s = true ∧
  isPermBool s arr = true ∧
  s.length = arr.length ∧
  heap_sort s = s ∧
  isMaxHeapBool (build_max_heap arr) = true)

/-! ## 8. Total Correctness Theorem: `Pre → Post_prop` -/

theorem heap_sort_correct (arr : List Int) (_hpre : Pre arr) : Post_prop arr :=
  ⟨sorted_thm arr,
   perm_thm arr,
   length_thm arr,
   mem_thm arr,
   count_thm arr,
   base_case_thm arr,
   idempotent_thm arr,
   already_sorted_thm arr,
   bounds_thm arr,
   build_max_heap_thm arr⟩

/-! ## 9. Imperative Implementation -/

/-- Imperative `heapify` using `Id.run do` with mutable variables. -/
def heapify_imp (arr : List Int) (n i : Nat) : List Int := Id.run do
  let mut a := arr
  let mut cur := i
  for _ in List.range (n - i) do
    let left := 2 * cur + 1
    let right := 2 * cur + 2
    let largest1 := if left < n ∧ a[left]! > a[cur]! then left else cur
    let largest := if right < n ∧ a[right]! > a[largest1]! then right else largest1
    a := if largest ≠ cur then swap a cur largest else a
    cur := if largest ≠ cur then largest else cur
  return a

/-- Imperative `build_max_heap` using `Id.run do` with mutable state. -/
def build_max_heap_imp (arr : List Int) : List Int := Id.run do
  let mut a := arr
  let n := a.length
  for i in (List.range (n / 2)).reverse do
    a := heapify_imp a n i
  return a

/-- Imperative `heap_sort` using `Id.run do` with mutable state. -/
def heap_sort_imp (arr : List Int) : List Int := Id.run do
  if arr.length ≤ 1 then
    return arr
  let mut result := arr
  let n := result.length
  result := build_max_heap_imp result
  for i in ((List.range n).drop 1).reverse do
    result := swap result 0 i
    result := heapify_imp result i 0
  return result

/-! ## 10. Imperative Tests -/

#eval heap_sort_imp [3, 1, 2]
#eval heap_sort_imp []
#eval heap_sort_imp [1]
#eval heap_sort_imp [5, 2, 4, 6, 1, 3]
#eval heap_sort_imp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

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

/-! ## 11. Functional-Imperative Equivalence Theorem -/

def heapifyStep (n : Nat) (s : MProd (List Int) Nat) : MProd (List Int) Nat :=
  let left := 2 * s.snd + 1
  let right := 2 * s.snd + 2
  let largest1 := if left < n ∧ s.fst[left]! > s.fst[s.snd]! then left else s.snd
  let largest := if right < n ∧ s.fst[right]! > s.fst[largest1]! then right else largest1
  ⟨if largest ≠ s.snd then swap s.fst s.snd largest else s.fst,
   if largest ≠ s.snd then largest else s.snd⟩

theorem foldl_heapifyStep_fixed (n : Nat) (s : MProd (List Int) Nat) (xs : List Nat)
    (hfix : heapifyStep n s = s) :
    List.foldl (fun acc _ => heapifyStep n acc) s xs = s := by
  induction xs with
  | nil => rfl
  | cons _ ys ih =>
    simp only [List.foldl_cons, hfix, ih]

theorem foldl_heapifyStep_eq (n : Nat) (xs : List Nat) (arr : List Int) (i : Nat) :
    (List.foldl (fun acc _ => heapifyStep n acc) ⟨arr, i⟩ xs).fst =
      heapifyAux xs.length arr n i := by
  induction xs generalizing arr i with
  | nil => rfl
  | cons _ ys ih =>
    simp only [List.foldl_cons, List.length_cons]
    set left := 2 * i + 1
    set right := 2 * i + 2
    set largest1 := if left < n ∧ arr[left]! > arr[i]! then left else i
    set largest := if right < n ∧ arr[right]! > arr[largest1]! then right else largest1
    have hstep : heapifyStep n ⟨arr, i⟩ =
        ⟨if largest ≠ i then swap arr i largest else arr, if largest ≠ i then largest else i⟩ := rfl
    have haux : heapifyAux (ys.length + 1) arr n i =
        (if largest ≠ i then heapifyAux ys.length (swap arr i largest) n largest else arr) := rfl
    rw [hstep, haux]
    by_cases hne : largest ≠ i
    · rw [if_pos hne, if_pos hne, if_pos hne]
      exact ih (swap arr i largest) largest
    · rw [if_neg hne, if_neg hne, if_neg hne]
      have hfix : heapifyStep n ⟨arr, i⟩ = ⟨arr, i⟩ := by
        rw [hstep, if_neg hne, if_neg hne]
      rw [foldl_heapifyStep_fixed n ⟨arr, i⟩ ys hfix]

theorem heapify_imp_eq (arr : List Int) (n i : Nat) :
    heapify_imp arr n i = heapify arr n i := by
  unfold heapify_imp heapify
  simp only [Id.run, bind, pure, List.forIn_yield_eq_foldl]
  have h := foldl_heapifyStep_eq n (List.range (n - i)) arr i
  rw [List.length_range] at h
  exact h

theorem foldl_buildMaxHeap_eq (arr : List Int) (n k : Nat) :
    List.foldl (fun a i => heapify_imp a n i) arr (List.range k).reverse =
      buildMaxHeapLoop arr n k := by
  induction k generalizing arr with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.foldl_cons, heapify_imp_eq, ih]
    rfl

theorem build_max_heap_imp_eq (arr : List Int) :
    build_max_heap_imp arr = build_max_heap arr := by
  unfold build_max_heap_imp build_max_heap
  simp only [Id.run, bind, pure, List.forIn_yield_eq_foldl]
  exact foldl_buildMaxHeap_eq arr arr.length (arr.length / 2)

theorem drop_one_range_succ (i : Nat) :
    (List.range (i + 2)).drop 1 = (List.range (i + 1)).drop 1 ++ [i + 1] := by
  rw [List.range_succ (n := i + 1), List.drop_append_of_le_length]
  simp

theorem foldl_extractMax_eq (arr : List Int) (m : Nat) :
    List.foldl (fun a i => heapify_imp (swap a 0 i) i 0) arr ((List.range m).drop 1).reverse =
      extractMaxLoop arr m := by
  induction m generalizing arr with
  | zero => rfl
  | succ m ih =>
    cases m with
    | zero => rfl
    | succ i =>
      rw [drop_one_range_succ i, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.foldl_cons, heapify_imp_eq, ih]
      rfl

theorem heap_sort_equiv (arr : List Int) :
    heap_sort arr = heap_sort_imp arr := by
  symm
  unfold heap_sort_imp heap_sort
  split
  · rfl
  · simp only [Id.run, bind, pure, List.forIn_yield_eq_foldl, build_max_heap_imp_eq]
    exact foldl_extractMax_eq (build_max_heap arr) arr.length

end heap_sort
