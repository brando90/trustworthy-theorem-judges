import Mathlib

/-!
# Heap Sort

Translation of the Python `heap_sort` program into Lean 4.
Sorts a list of integers in ascending order using the max-heap sort algorithm:
first building a max-heap in-place, then repeatedly extracting the maximum element
to the end of the active heap prefix.
-/

namespace heap_sort

set_option linter.dupNamespace false

/-- Safe 0-default indexing into a list of integers. -/
def getElemD (arr : List Int) (i : Nat) : Int :=
  match arr, i with
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => getElemD xs i

/-- Swap elements at indices `i` and `j` in a list of integers. -/
def swap (arr : List Int) (i j : Nat) : List Int :=
  let vi := getElemD arr i
  let vj := getElemD arr j
  (arr.set i vj).set j vi

/-- Choose the index of the largest element among parent `i` and its children `2*i+1`, `2*i+2`
within heap bound `n`. -/
def chooseLargest (arr : List Int) (n i : Nat) : Nat :=
  let left := 2 * i + 1
  let right := 2 * i + 2
  let largest := if left < n && getElemD arr left > getElemD arr i then left else i
  let largest := if right < n && getElemD arr right > getElemD arr largest then right else largest
  largest

/-- Maintain the max-heap property for subtree rooted at `i` within heap size `n`,
using `fuel` steps of sift-down. -/
def heapifyAux (fuel : Nat) (arr : List Int) (n i : Nat) : List Int :=
  match fuel with
  | 0 => arr
  | fuel' + 1 =>
    let largest := chooseLargest arr n i
    if largest != i then
      heapifyAux fuel' (swap arr i largest) n largest
    else
      arr

/-- Maintain the max-heap property for subtree rooted at `i` within heap size `n`. -/
def heapify (arr : List Int) (n i : Nat) : List Int :=
  heapifyAux (n - i) arr n i

/-- Loop to build a max-heap from index `k` down to `0`:
when `k = m + 1`, heapifies at index `m` and recurses on `m`. -/
def buildMaxHeapLoop (arr : List Int) (n : Nat) : Nat → List Int
  | 0 => arr
  | m + 1 => buildMaxHeapLoop (heapify arr n m) n m

/-- Build a max-heap from the list `arr`. -/
def build_max_heap (arr : List Int) : List Int :=
  let n := arr.length
  buildMaxHeapLoop arr n (n / 2)

/-- Loop to extract elements from the max-heap one by one:
for `m + 1` from `n - 1` down to `1`, swaps index `0` with `m + 1` and heapifies prefix `m + 1`. -/
def extractMaxLoop (arr : List Int) : Nat → List Int
  | 0 => arr
  | m + 1 =>
    let arr' := swap arr 0 (m + 1)
    let arr'' := heapify arr' (m + 1) 0
    extractMaxLoop arr'' m

/-- Sort a list of integers in non-decreasing order using the heap sort algorithm. -/
def heap_sort (arr : List Int) : List Int :=
  if arr.length ≤ 1 then
    arr
  else
    let n := arr.length
    let heaped := build_max_heap arr
    extractMaxLoop heaped (n - 1)

-- ============================================================================
-- Unit Tests
-- ============================================================================

#eval heap_sort [3, 1, 2]
#eval heap_sort ([] : List Int)
#eval heap_sort [1]
#eval heap_sort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

example : heap_sort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heap_sort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heap_sort [2, 1, 3] = [1, 2, 3] := by native_decide
example : heap_sort ([] : List Int) = [] := by native_decide
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

-- ============================================================================
-- Pre-condition
-- ============================================================================

/-- Pre-condition for `heap_sort`: any `List Int` is valid. -/
def Pre (_arr : List Int) : Prop := True

-- ============================================================================
-- Internal Proof Helpers for Array/Heap Operations
-- ============================================================================

private theorem getElemD_set (arr : List Int) (i k : Nat) (v : Int) (hi : i < arr.length) :
    getElemD (arr.set i v) k = if k = i then v else getElemD arr k := by
  induction arr generalizing i k with
  | nil => contradiction
  | cons a as ih =>
    cases i with
    | zero =>
      cases k with
      | zero => rfl
      | succ k' => rfl
    | succ i' =>
      have hi' : i' < as.length := Nat.lt_of_succ_lt_succ hi
      cases k with
      | zero => rfl
      | succ k' =>
        simp only [List.set, getElemD, ih i' k' hi']
        by_cases h : k' = i'
        · subst h; simp
        · simp [h]

private theorem length_swap (arr : List Int) (i j : Nat) :
    (swap arr i j).length = arr.length := by
  simp [swap]

private theorem getElemD_swap (arr : List Int) (i j k : Nat)
    (hi : i < arr.length) (hj : j < arr.length) :
    getElemD (swap arr i j) k =
      if k = j then getElemD arr i else if k = i then getElemD arr j else getElemD arr k := by
  unfold swap
  have hj' : j < (arr.set i (getElemD arr j)).length := by simp [hj]
  rw [getElemD_set _ j k (getElemD arr i) hj']
  rw [getElemD_set arr i k (getElemD arr j) hi]

private theorem set_perm_cons (as : List Int) (j : Nat) (a : Int) (hj : j < as.length) :
    (getElemD as j :: as.set j a).Perm (a :: as) := by
  induction as generalizing j with
  | nil => contradiction
  | cons b bs ih =>
    cases j with
    | zero =>
      exact List.Perm.swap a b bs
    | succ j' =>
      have hj' : j' < bs.length := Nat.lt_of_succ_lt_succ hj
      simp only [getElemD, List.set]
      have h1 : (getElemD bs j' :: b :: bs.set j' a).Perm (b :: getElemD bs j' :: bs.set j' a) :=
        List.Perm.swap b (getElemD bs j') (bs.set j' a)
      have h2 : (b :: getElemD bs j' :: bs.set j' a).Perm (b :: a :: bs) :=
        List.Perm.cons b (ih j' hj')
      have h3 : (b :: a :: bs).Perm (a :: b :: bs) :=
        List.Perm.swap a b bs
      exact h1.trans (h2.trans h3)

private theorem swap_perm (arr : List Int) (i j : Nat)
    (hi : i < arr.length) (hj : j < arr.length) :
    (swap arr i j).Perm arr := by
  induction arr generalizing i j with
  | nil => contradiction
  | cons a as ih =>
    cases i with
    | zero =>
      cases j with
      | zero =>
        simp [swap, getElemD]
      | succ j' =>
        have hj' : j' < as.length := Nat.lt_of_succ_lt_succ hj
        simp only [swap, getElemD, List.set]
        exact set_perm_cons as j' a hj'
    | succ i' =>
      have hi' : i' < as.length := Nat.lt_of_succ_lt_succ hi
      cases j with
      | zero =>
        simp only [swap, getElemD, List.set]
        exact set_perm_cons as i' a hi'
      | succ j' =>
        have hj' : j' < as.length := Nat.lt_of_succ_lt_succ hj
        simp only [swap, getElemD, List.set]
        exact List.Perm.cons a (ih i' j' hi' hj')

private theorem chooseLargest_cases (arr : List Int) (n i : Nat) :
    chooseLargest arr n i = i ∨
    (chooseLargest arr n i = 2 * i + 1 ∧ 2 * i + 1 < n) ∨
    (chooseLargest arr n i = 2 * i + 2 ∧ 2 * i + 2 < n) := by
  unfold chooseLargest
  dsimp only
  split_ifs with h1 h2 h3
  · simp at h2
    exact Or.inr (Or.inr ⟨rfl, h2.1⟩)
  · simp at h1
    exact Or.inr (Or.inl ⟨rfl, h1.1⟩)
  · simp at h3
    exact Or.inr (Or.inr ⟨rfl, h3.1⟩)
  · exact Or.inl rfl

private theorem chooseLargest_ge_self (arr : List Int) (n i : Nat) :
    getElemD arr i ≤ getElemD arr (chooseLargest arr n i) := by
  unfold chooseLargest
  dsimp only
  split_ifs with h1 h2 h3
  · simp at h1 h2; omega
  · simp at h1; omega
  · simp at h3; omega
  · exact Int.le_refl _

private theorem chooseLargest_ge_left (arr : List Int) (n i : Nat) (h : 2 * i + 1 < n) :
    getElemD arr (2 * i + 1) ≤ getElemD arr (chooseLargest arr n i) := by
  unfold chooseLargest
  dsimp only
  split_ifs with h1 h2 h3
  · simp at h1 h2; omega
  · exact Int.le_refl _
  · simp [h] at h1; simp at h3; omega
  · simp [h] at h1; exact h1

private theorem chooseLargest_ge_right (arr : List Int) (n i : Nat) (h : 2 * i + 2 < n) :
    getElemD arr (2 * i + 2) ≤ getElemD arr (chooseLargest arr n i) := by
  unfold chooseLargest
  dsimp only
  split_ifs with h1 h2 h3
  · exact Int.le_refl _
  · simp [h] at h2; exact h2
  · exact Int.le_refl _
  · simp [h] at h3; exact h3

private theorem length_heapifyAux (fuel : Nat) (arr : List Int) (n i : Nat) :
    (heapifyAux fuel arr n i).length = arr.length := by
  induction fuel generalizing arr i with
  | zero => rfl
  | succ fuel' ih =>
    unfold heapifyAux
    dsimp only
    split_ifs
    · rw [ih, length_swap]
    · rfl

private theorem length_heapify (arr : List Int) (n i : Nat) :
    (heapify arr n i).length = arr.length :=
  length_heapifyAux (n - i) arr n i

private theorem perm_heapifyAux (fuel : Nat) (arr : List Int) (n i : Nat) (hn : n ≤ arr.length) :
    (heapifyAux fuel arr n i).Perm arr := by
  induction fuel generalizing arr i with
  | zero => exact List.Perm.refl arr
  | succ fuel' ih =>
    unfold heapifyAux
    dsimp only
    split_ifs with hne
    · have hne' : chooseLargest arr n i ≠ i := by simpa using hne
      rcases chooseLargest_cases arr n i with h0 | ⟨h1, hlt1⟩ | ⟨h2, hlt2⟩
      · exact absurd h0 hne'
      · have hi : i < arr.length := by omega
        have hl : chooseLargest arr n i < arr.length := by omega
        have hswap_len : n ≤ (swap arr i (chooseLargest arr n i)).length := by
          rw [length_swap]; exact hn
        exact (ih (swap arr i (chooseLargest arr n i)) (chooseLargest arr n i) hswap_len).trans
          (swap_perm arr i (chooseLargest arr n i) hi hl)
      · have hi : i < arr.length := by omega
        have hl : chooseLargest arr n i < arr.length := by omega
        have hswap_len : n ≤ (swap arr i (chooseLargest arr n i)).length := by
          rw [length_swap]; exact hn
        exact (ih (swap arr i (chooseLargest arr n i)) (chooseLargest arr n i) hswap_len).trans
          (swap_perm arr i (chooseLargest arr n i) hi hl)
    · exact List.Perm.refl arr

private theorem perm_heapify (arr : List Int) (n i : Nat) (hn : n ≤ arr.length) :
    (heapify arr n i).Perm arr :=
  perm_heapifyAux (n - i) arr n i hn

private theorem getElemD_heapifyAux_ge (fuel : Nat) (arr : List Int) (n i k : Nat)
    (hn : n ≤ arr.length) (hk : n ≤ k) :
    getElemD (heapifyAux fuel arr n i) k = getElemD arr k := by
  induction fuel generalizing arr i with
  | zero => rfl
  | succ fuel' ih =>
    unfold heapifyAux
    dsimp only
    split_ifs with hne
    · have hne' : chooseLargest arr n i ≠ i := by simpa using hne
      have hbounds : i < n ∧ chooseLargest arr n i < n := by
        rcases chooseLargest_cases arr n i with h0 | ⟨_, hlt1⟩ | ⟨_, hlt2⟩
        · exact absurd h0 hne'
        · omega
        · omega
      have hi : i < arr.length := by omega
      have hl : chooseLargest arr n i < arr.length := by omega
      have hswap_len : n ≤ (swap arr i (chooseLargest arr n i)).length := by
        rw [length_swap]; exact hn
      rw [ih (swap arr i (chooseLargest arr n i)) (chooseLargest arr n i) hswap_len]
      rw [getElemD_swap arr i (chooseLargest arr n i) k hi hl]
      have h1 : k ≠ chooseLargest arr n i := by omega
      have h2 : k ≠ i := by omega
      simp [h1, h2]
    · rfl

private theorem getElemD_heapify_ge (arr : List Int) (n i k : Nat)
    (hn : n ≤ arr.length) (hk : n ≤ k) :
    getElemD (heapify arr n i) k = getElemD arr k :=
  getElemD_heapifyAux_ge (n - i) arr n i k hn hk

private theorem getElemD_heapifyAux_lt_ex (fuel : Nat) (arr : List Int) (n i k : Nat)
    (hn : n ≤ arr.length) (hk : k < n) :
    ∃ k' < n, getElemD (heapifyAux fuel arr n i) k = getElemD arr k' := by
  induction fuel generalizing arr i k with
  | zero => exact ⟨k, hk, rfl⟩
  | succ fuel' ih =>
    unfold heapifyAux
    dsimp only
    split_ifs with hne
    · have hne' : chooseLargest arr n i ≠ i := by simpa using hne
      have hbounds : i < n ∧ chooseLargest arr n i < n := by
        rcases chooseLargest_cases arr n i with h0 | ⟨_, hlt1⟩ | ⟨_, hlt2⟩
        · exact absurd h0 hne'
        · omega
        · omega
      have hi : i < arr.length := by omega
      have hl : chooseLargest arr n i < arr.length := by omega
      have hswap_len : n ≤ (swap arr i (chooseLargest arr n i)).length := by
        rw [length_swap]; exact hn
      rcases ih (swap arr i (chooseLargest arr n i)) (chooseLargest arr n i) k hswap_len hk with
        ⟨k1, hk1, heq1⟩
      rw [heq1, getElemD_swap arr i (chooseLargest arr n i) k1 hi hl]
      split_ifs with c1 c2
      · exact ⟨i, hbounds.1, rfl⟩
      · exact ⟨chooseLargest arr n i, hbounds.2, rfl⟩
      · exact ⟨k1, hk1, rfl⟩
    · exact ⟨k, hk, rfl⟩

private theorem getElemD_heapify_lt_ex (arr : List Int) (n i k : Nat)
    (hn : n ≤ arr.length) (hk : k < n) :
    ∃ k' < n, getElemD (heapify arr n i) k = getElemD arr k' :=
  getElemD_heapifyAux_lt_ex (n - i) arr n i k hn hk

private theorem length_buildMaxHeapLoop (arr : List Int) (n k : Nat) :
    (buildMaxHeapLoop arr n k).length = arr.length := by
  induction k generalizing arr with
  | zero => rfl
  | succ m ih =>
    unfold buildMaxHeapLoop
    rw [ih, length_heapify]

private theorem length_build_max_heap (arr : List Int) :
    (build_max_heap arr).length = arr.length :=
  length_buildMaxHeapLoop arr arr.length (arr.length / 2)

private theorem perm_buildMaxHeapLoop (arr : List Int) (n k : Nat) (hn : n ≤ arr.length) :
    (buildMaxHeapLoop arr n k).Perm arr := by
  induction k generalizing arr with
  | zero => exact List.Perm.refl arr
  | succ m ih =>
    unfold buildMaxHeapLoop
    have hlen : n ≤ (heapify arr n m).length := by rw [length_heapify]; exact hn
    exact (ih (heapify arr n m) hlen).trans (perm_heapify arr n m hn)

private theorem perm_build_max_heap (arr : List Int) :
    (build_max_heap arr).Perm arr :=
  perm_buildMaxHeapLoop arr arr.length (arr.length / 2) (Nat.le_refl _)

private theorem length_extractMaxLoop (arr : List Int) (k : Nat) :
    (extractMaxLoop arr k).length = arr.length := by
  induction k generalizing arr with
  | zero => rfl
  | succ m ih =>
    unfold extractMaxLoop
    rw [ih, length_heapify, length_swap]

private theorem perm_extractMaxLoop (arr : List Int) (k : Nat) (hk : k < arr.length) :
    (extractMaxLoop arr k).Perm arr := by
  induction k generalizing arr with
  | zero => exact List.Perm.refl arr
  | succ m ih =>
    unfold extractMaxLoop
    dsimp only
    have h0 : 0 < arr.length := by omega
    have hm1 : m + 1 < arr.length := hk
    have hswap_perm : (swap arr 0 (m + 1)).Perm arr := swap_perm arr 0 (m + 1) h0 hm1
    have hswap_len : m + 1 ≤ (swap arr 0 (m + 1)).length := by
      rw [length_swap]; omega
    have hheap_perm : (heapify (swap arr 0 (m + 1)) (m + 1) 0).Perm (swap arr 0 (m + 1)) :=
      perm_heapify (swap arr 0 (m + 1)) (m + 1) 0 hswap_len
    have hheap_len : m < (heapify (swap arr 0 (m + 1)) (m + 1) 0).length := by
      rw [length_heapify, length_swap]; omega
    exact (ih _ hheap_len).trans (hheap_perm.trans hswap_perm)

/-- Max-heap node property at index `k` within heap size `n`:
both children (if within bounds `< n`) are `≤` the parent at `k`. -/
def HeapNode (arr : List Int) (n k : Nat) : Prop :=
  (2 * k + 1 < n → getElemD arr (2 * k + 1) ≤ getElemD arr k) ∧
  (2 * k + 2 < n → getElemD arr (2 * k + 2) ≤ getElemD arr k)

/-- Max-heap invariant on `arr` for all indices `k` in `[start, n)`. -/
def IsMaxHeap (arr : List Int) (n start : Nat) : Prop :=
  ∀ k, start ≤ k → k < n → HeapNode arr n k

private def AlmostHeap (arr : List Int) (n start idx : Nat) : Prop :=
  (∀ k, start ≤ k → k < n → k ≠ idx → HeapNode arr n k) ∧
  (∀ p, start ≤ p → p < n → (2 * p + 1 = idx ∨ 2 * p + 2 = idx) →
    (2 * idx + 1 < n → getElemD arr (2 * idx + 1) ≤ getElemD arr p) ∧
    (2 * idx + 2 < n → getElemD arr (2 * idx + 2) ≤ getElemD arr p))

private theorem almostHeap_of_isMaxHeap_succ (arr : List Int) (n start : Nat)
    (h : IsMaxHeap arr n (start + 1)) :
    AlmostHeap arr n start start := by
  refine ⟨?_, ?_⟩
  · intro k hsk hkn hne
    exact h k (by omega) hkn
  · intro p hsp _ hp
    omega

private theorem isMaxHeap_of_almostHeap_eq (arr : List Int) (n start idx : Nat)
    (h : AlmostHeap arr n start idx) (heq : chooseLargest arr n idx = idx) :
    IsMaxHeap arr n start := by
  intro k hsk hkn
  by_cases hk : k = idx
  · subst hk
    refine ⟨?_, ?_⟩
    · intro h1
      have hge := chooseLargest_ge_left arr n k h1
      rwa [heq] at hge
    · intro h2
      have hge := chooseLargest_ge_right arr n k h2
      rwa [heq] at hge
  · exact h.1 k hsk hkn hk

private theorem almostHeap_step (arr : List Int) (n start idx : Nat)
    (hn : n ≤ arr.length) (hstart : start ≤ idx)
    (halm : AlmostHeap arr n start idx) (hne : chooseLargest arr n idx ≠ idx) :
    AlmostHeap (swap arr idx (chooseLargest arr n idx)) n start (chooseLargest arr n idx) := by
  set l := chooseLargest arr n idx with hl_def
  have hl_cases : (l = 2 * idx + 1 ∧ 2 * idx + 1 < n) ∨ (l = 2 * idx + 2 ∧ 2 * idx + 2 < n) := by
    rcases chooseLargest_cases arr n idx with h0 | h1 | h2
    · exact absurd h0 hne
    · exact Or.inl h1
    · exact Or.inr h2
  have hidx_lt_l : idx < l := by omega
  have hl_lt_n : l < n := by omega
  have hidx_len : idx < arr.length := by omega
  have hl_len : l < arr.length := by omega
  refine ⟨?_, ?_⟩
  · intro k hsk hkn hkl
    by_cases hk : k = idx
    · subst hk
      have hroot : getElemD (swap arr k l) k = getElemD arr l := by
        rw [getElemD_swap arr k l k hidx_len hl_len]
        have : k ≠ l := by omega
        simp [this]
      refine ⟨?_, ?_⟩
      · intro hc1
        rw [hroot, getElemD_swap arr k l (2 * k + 1) hidx_len hl_len]
        have hne_k : 2 * k + 1 ≠ k := by omega
        by_cases hc1_l : 2 * k + 1 = l
        · simp only [hc1_l, ↓reduceIte]
          exact chooseLargest_ge_self arr n k
        · simp only [hc1_l, ↓reduceIte, hne_k]
          exact chooseLargest_ge_left arr n k hc1
      · intro hc2
        rw [hroot, getElemD_swap arr k l (2 * k + 2) hidx_len hl_len]
        have hne_k : 2 * k + 2 ≠ k := by omega
        by_cases hc2_l : 2 * k + 2 = l
        · simp only [hc2_l, ↓reduceIte]
          exact chooseLargest_ge_self arr n k
        · simp only [hc2_l, ↓reduceIte, hne_k]
          exact chooseLargest_ge_right arr n k hc2
    · have hk_val : getElemD (swap arr idx l) k = getElemD arr k := by
        rw [getElemD_swap arr idx l k hidx_len hl_len]
        simp [hkl, hk]
      have hk_node := halm.1 k hsk hkn hk
      have hidx_ne_l : idx ≠ l := by omega
      refine ⟨?_, ?_⟩
      · intro hc1
        rw [hk_val, getElemD_swap arr idx l (2 * k + 1) hidx_len hl_len]
        have hc1_ne_l : 2 * k + 1 ≠ l := by omega
        by_cases hc1_idx : 2 * k + 1 = idx
        · simp only [hc1_idx, hidx_ne_l, ↓reduceIte]
          have hp := halm.2 k hsk hkn (Or.inl hc1_idx)
          rcases hl_cases with ⟨hl1, hlt1⟩ | ⟨hl2, hlt2⟩
          · rw [hl1]; exact hp.1 hlt1
          · rw [hl2]; exact hp.2 hlt2
        · simp only [hc1_ne_l, ↓reduceIte, hc1_idx]
          exact hk_node.1 hc1
      · intro hc2
        rw [hk_val, getElemD_swap arr idx l (2 * k + 2) hidx_len hl_len]
        have hc2_ne_l : 2 * k + 2 ≠ l := by omega
        by_cases hc2_idx : 2 * k + 2 = idx
        · simp only [hc2_idx, hidx_ne_l, ↓reduceIte]
          have hp := halm.2 k hsk hkn (Or.inr hc2_idx)
          rcases hl_cases with ⟨hl1, hlt1⟩ | ⟨hl2, hlt2⟩
          · rw [hl1]; exact hp.1 hlt1
          · rw [hl2]; exact hp.2 hlt2
        · simp only [hc2_ne_l, ↓reduceIte, hc2_idx]
          exact hk_node.2 hc2
  · intro p hsp hpn hpl
    have hp_eq : p = idx := by omega
    subst hp_eq
    have hp_val : getElemD (swap arr p l) p = getElemD arr l := by
      rw [getElemD_swap arr p l p hidx_len hl_len]
      have : p ≠ l := by omega
      simp [this]
    have hl_node : HeapNode arr n l := halm.1 l (by omega) hl_lt_n (by omega)
    refine ⟨?_, ?_⟩
    · intro hgc1
      rw [hp_val, getElemD_swap arr p l (2 * l + 1) hidx_len hl_len]
      have h1 : 2 * l + 1 ≠ l := by omega
      have h2 : 2 * l + 1 ≠ p := by omega
      simp only [h1, ↓reduceIte, h2]
      exact hl_node.1 hgc1
    · intro hgc2
      rw [hp_val, getElemD_swap arr p l (2 * l + 2) hidx_len hl_len]
      have h1 : 2 * l + 2 ≠ l := by omega
      have h2 : 2 * l + 2 ≠ p := by omega
      simp only [h1, ↓reduceIte, h2]
      exact hl_node.2 hgc2

private theorem heapifyAux_isMaxHeap (fuel : Nat) (arr : List Int) (n start idx : Nat)
    (hn : n ≤ arr.length) (hstart : start ≤ idx) (hfuel : n - idx ≤ fuel)
    (halm : AlmostHeap arr n start idx) :
    IsMaxHeap (heapifyAux fuel arr n idx) n start := by
  induction fuel generalizing arr idx with
  | zero =>
    unfold heapifyAux
    intro k hsk hkn
    have hk_ne : k ≠ idx := by omega
    exact halm.1 k hsk hkn hk_ne
  | succ fuel' ih =>
    unfold heapifyAux
    dsimp only
    split_ifs with hne
    · have hne' : chooseLargest arr n idx ≠ idx := by simpa using hne
      have hbounds : idx < chooseLargest arr n idx ∧ chooseLargest arr n idx < n := by
        rcases chooseLargest_cases arr n idx with h0 | ⟨_, hlt1⟩ | ⟨_, hlt2⟩
        · exact absurd h0 hne'
        · omega
        · omega
      have hswap_len : n ≤ (swap arr idx (chooseLargest arr n idx)).length := by
        rw [length_swap]; exact hn
      have hstart' : start ≤ chooseLargest arr n idx := by omega
      have hfuel' : n - chooseLargest arr n idx ≤ fuel' := by omega
      have halm' := almostHeap_step arr n start idx hn hstart halm hne'
      exact ih (swap arr idx (chooseLargest arr n idx)) (chooseLargest arr n idx)
        hswap_len hstart' hfuel' halm'
    · have heq : chooseLargest arr n idx = idx := by simpa using hne
      exact isMaxHeap_of_almostHeap_eq arr n start idx halm heq

private theorem heapify_isMaxHeap (arr : List Int) (n start : Nat)
    (hn : n ≤ arr.length) (h : IsMaxHeap arr n (start + 1)) :
    IsMaxHeap (heapify arr n start) n start :=
  heapifyAux_isMaxHeap (n - start) arr n start start hn (Nat.le_refl _) (Nat.le_refl _)
    (almostHeap_of_isMaxHeap_succ arr n start h)

private theorem buildMaxHeapLoop_isMaxHeap (arr : List Int) (n k : Nat)
    (hn : n ≤ arr.length) (h : IsMaxHeap arr n k) :
    IsMaxHeap (buildMaxHeapLoop arr n k) n 0 := by
  induction k generalizing arr with
  | zero => exact h
  | succ m ih =>
    unfold buildMaxHeapLoop
    have hlen : n ≤ (heapify arr n m).length := by rw [length_heapify]; exact hn
    have hheap : IsMaxHeap (heapify arr n m) n m := heapify_isMaxHeap arr n m hn h
    exact ih (heapify arr n m) hlen hheap

private theorem isMaxHeap_half (arr : List Int) (n : Nat) :
    IsMaxHeap arr n (n / 2) := by
  intro k hsk hkn
  refine ⟨?_, ?_⟩ <;> omega

private theorem build_max_heap_isMaxHeap (arr : List Int) :
    IsMaxHeap (build_max_heap arr) arr.length 0 :=
  buildMaxHeapLoop_isMaxHeap arr arr.length (arr.length / 2) (Nat.le_refl _)
    (isMaxHeap_half arr arr.length)

private theorem isMaxHeap_max_root (arr : List Int) (n : Nat) (h : IsMaxHeap arr n 0) :
    ∀ j < n, getElemD arr j ≤ getElemD arr 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hj0 : j = 0
    · subst hj0; exact Int.le_refl _
    · let p := (j - 1) / 2
      have hp_lt_j : p < j := by omega
      have hp_lt_n : p < n := by omega
      have hp_le : getElemD arr p ≤ getElemD arr 0 := ih p hp_lt_j hp_lt_n
      have hp_node : HeapNode arr n p := h p (Nat.zero_le _) hp_lt_n
      have hj_cases : j = 2 * p + 1 ∨ j = 2 * p + 2 := by omega
      rcases hj_cases with hj1 | hj2
      · have hle : getElemD arr j ≤ getElemD arr p := by
          rw [hj1]
          exact hp_node.1 (by omega)
        exact Int.le_trans hle hp_le
      · have hle : getElemD arr j ≤ getElemD arr p := by
          rw [hj2]
          exact hp_node.2 (by omega)
        exact Int.le_trans hle hp_le

private def HeapSuffixLe (arr : List Int) (n k : Nat) : Prop :=
  ∀ i j, i ≤ k → k < j → j < n → getElemD arr i ≤ getElemD arr j

private def SuffixSorted (arr : List Int) (n k : Nat) : Prop :=
  ∀ i j, k < i → i < j → j < n → getElemD arr i ≤ getElemD arr j

private theorem extractMaxLoop_sorted (arr : List Int) (n k : Nat)
    (hn : n ≤ arr.length) (hk : k < n)
    (hheap : IsMaxHeap arr (k + 1) 0)
    (hpref : HeapSuffixLe arr n k)
    (hsuf : SuffixSorted arr n k) :
    ∀ i j, i < j → j < n →
      getElemD (extractMaxLoop arr k) i ≤ getElemD (extractMaxLoop arr k) j := by
  induction k generalizing arr with
  | zero =>
    unfold extractMaxLoop
    intro i j hij hjn
    by_cases hi0 : i = 0
    · subst hi0
      exact hpref 0 j (Nat.le_refl 0) hij hjn
    · exact hsuf i j (by omega) hij hjn
  | succ m ih =>
    unfold extractMaxLoop
    dsimp only
    set arr1 := swap arr 0 (m + 1)
    set arr2 := heapify arr1 (m + 1) 0
    have h0_len : 0 < arr.length := by omega
    have hm1_len : m + 1 < arr.length := by omega
    have hn1 : n ≤ arr1.length := by rw [length_swap]; exact hn
    have hn2 : n ≤ arr2.length := by rw [length_heapify]; exact hn1
    have hheap1 : IsMaxHeap arr1 (m + 1) 1 := by
      intro idx h1idx hidx_lt
      have hidx_val : getElemD arr1 idx = getElemD arr idx := by
        rw [getElemD_swap arr 0 (m + 1) idx h0_len hm1_len]
        have h1 : idx ≠ m + 1 := by omega
        have h2 : idx ≠ 0 := by omega
        simp [h1, h2]
      have hnode := hheap idx (Nat.zero_le _) (by omega)
      refine ⟨?_, ?_⟩
      · intro hc1
        rw [hidx_val, getElemD_swap arr 0 (m + 1) (2 * idx + 1) h0_len hm1_len]
        have h1 : 2 * idx + 1 ≠ m + 1 := by omega
        have h2 : 2 * idx + 1 ≠ 0 := by omega
        simp only [h1, ↓reduceIte, h2]
        exact hnode.1 (by omega)
      · intro hc2
        rw [hidx_val, getElemD_swap arr 0 (m + 1) (2 * idx + 2) h0_len hm1_len]
        have h1 : 2 * idx + 2 ≠ m + 1 := by omega
        have h2 : 2 * idx + 2 ≠ 0 := by omega
        simp only [h1, ↓reduceIte, h2]
        exact hnode.2 (by omega)
    have hheap2 : IsMaxHeap arr2 (m + 1) 0 :=
      heapify_isMaxHeap arr1 (m + 1) 0 (by omega) hheap1
    have hpref1 : HeapSuffixLe arr1 n m := by
      intro i j him hmj hjn
      have hi_ex : ∃ i0 ≤ m + 1, getElemD arr1 i = getElemD arr i0 := by
        rw [getElemD_swap arr 0 (m + 1) i h0_len hm1_len]
        have hi_ne : i ≠ m + 1 := by omega
        by_cases hi0 : i = 0
        · simp only [hi_ne, ↓reduceIte]
          simp only [hi0, ↓reduceIte]
          exact ⟨m + 1, Nat.le_refl _, rfl⟩
        · simp only [hi_ne, ↓reduceIte, hi0]
          exact ⟨i, by omega, rfl⟩
      rcases hi_ex with ⟨i0, hi0_le, hi0_eq⟩
      rw [hi0_eq, getElemD_swap arr 0 (m + 1) j h0_len hm1_len]
      by_cases hj_eq : j = m + 1
      · simp only [hj_eq, ↓reduceIte]
        exact isMaxHeap_max_root arr (m + 2) hheap i0 (by omega)
      · have hj_ne0 : j ≠ 0 := by omega
        simp only [hj_eq, ↓reduceIte, hj_ne0]
        exact hpref i0 j hi0_le (by omega) hjn
    have hsuf1 : SuffixSorted arr1 n m := by
      intro i j hmi hij hjn
      have hj_val : getElemD arr1 j = getElemD arr j := by
        rw [getElemD_swap arr 0 (m + 1) j h0_len hm1_len]
        have h1 : j ≠ m + 1 := by omega
        have h2 : j ≠ 0 := by omega
        simp [h1, h2]
      rw [hj_val, getElemD_swap arr 0 (m + 1) i h0_len hm1_len]
      by_cases hi_eq : i = m + 1
      · simp only [hi_eq, ↓reduceIte]
        exact hpref 0 j (by omega) (by omega) hjn
      · have hi_ne0 : i ≠ 0 := by omega
        simp only [hi_eq, ↓reduceIte, hi_ne0]
        exact hsuf i j (by omega) hij hjn
    have hpref2 : HeapSuffixLe arr2 n m := by
      intro i j him hmj hjn
      rcases getElemD_heapify_lt_ex arr1 (m + 1) 0 i (by omega) (by omega) with
        ⟨i', hi'_lt, hi'_eq⟩
      have hj_eq : getElemD arr2 j = getElemD arr1 j :=
        getElemD_heapify_ge arr1 (m + 1) 0 j (by omega) (by omega)
      rw [hi'_eq, hj_eq]
      exact hpref1 i' j (by omega) hmj hjn
    have hsuf2 : SuffixSorted arr2 n m := by
      intro i j hmi hij hjn
      have hi_eq : getElemD arr2 i = getElemD arr1 i :=
        getElemD_heapify_ge arr1 (m + 1) 0 i (by omega) (by omega)
      have hj_eq : getElemD arr2 j = getElemD arr1 j :=
        getElemD_heapify_ge arr1 (m + 1) 0 j (by omega) (by omega)
      rw [hi_eq, hj_eq]
      exact hsuf1 i j hmi hij hjn
    exact ih arr2 hn2 (by omega) hheap2 hpref2 hsuf2

private theorem mem_iff_getElemD (arr : List Int) (x : Int) :
    x ∈ arr ↔ ∃ i < arr.length, getElemD arr i = x := by
  induction arr with
  | nil =>
    simp
  | cons a as ih =>
    constructor
    · intro hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact ⟨0, by simp, rfl⟩
      · rcases ih.mp hmem with ⟨i, hi, heq⟩
        exact ⟨i + 1, by simp [hi], heq⟩
    · rintro ⟨i, hi, heq⟩
      cases i with
      | zero =>
        simp only [getElemD] at heq
        subst heq
        exact List.mem_cons_self
      | succ i' =>
        have hi' : i' < as.length := Nat.lt_of_succ_lt_succ hi
        simp only [getElemD] at heq
        exact List.mem_cons_of_mem a (ih.mpr ⟨i', hi', heq⟩)

private theorem pairwise_of_getElemD_sorted (arr : List Int)
    (h : ∀ i j, i < j → j < arr.length → getElemD arr i ≤ getElemD arr j) :
    arr.Pairwise (· ≤ ·) := by
  induction arr with
  | nil => exact List.Pairwise.nil
  | cons a as ih =>
    refine List.Pairwise.cons ?_ ?_
    · intro x hx
      rcases (mem_iff_getElemD as x).mp hx with ⟨k, hk, rfl⟩
      exact h 0 (k + 1) (by omega) (by simp; omega)
    · apply ih
      intro i j hij hjn
      exact h (i + 1) (j + 1) (by omega) (by simp; omega)

private theorem eq_of_pairwise_of_perm {l1 l2 : List Int}
    (h1 : l1.Pairwise (· ≤ ·)) (h2 : l2.Pairwise (· ≤ ·)) (hp : l1.Perm l2) :
    l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    exact hp.nil_eq
  | cons a as ih =>
    cases l2 with
    | nil =>
      cases hp.symm.nil_eq
    | cons b bs =>
      rcases List.pairwise_cons.mp h1 with ⟨ha_le, has_pw⟩
      rcases List.pairwise_cons.mp h2 with ⟨hb_le, hbs_pw⟩
      have hb_mem : b ∈ a :: as := hp.symm.subset List.mem_cons_self
      have ha_mem : a ∈ b :: bs := hp.subset List.mem_cons_self
      have hab : a ≤ b := by
        rcases List.mem_cons.mp hb_mem with rfl | hmem
        · exact Int.le_refl _
        · exact ha_le b hmem
      have hba : b ≤ a := by
        rcases List.mem_cons.mp ha_mem with rfl | hmem
        · exact Int.le_refl _
        · exact hb_le a hmem
      have heq : a = b := by omega
      subst heq
      congr 1
      exact ih has_pw hbs_pw hp.cons_inv

-- ============================================================================
-- Property Propositions and Theorems
-- ============================================================================

/-- Property 1: Empty or single-element lists are returned unchanged. -/
def base_case_prop (arr : List Int) : Prop :=
  arr.length ≤ 1 → heap_sort arr = arr

theorem base_case_thm (arr : List Int) (_h : Pre arr) : base_case_prop arr := by
  intro hle
  unfold heap_sort
  simp [hle]

/-- Property 2: The output of `heap_sort` is a permutation of the input list. -/
def perm_prop (arr : List Int) : Prop :=
  (heap_sort arr).Perm arr

theorem perm_thm (arr : List Int) (_h : Pre arr) : perm_prop arr := by
  unfold perm_prop heap_sort
  split_ifs with hle
  · exact List.Perm.refl arr
  · dsimp only
    have hbm_perm : (build_max_heap arr).Perm arr := perm_build_max_heap arr
    have hbm_len : arr.length - 1 < (build_max_heap arr).length := by
      rw [length_build_max_heap]; omega
    exact (perm_extractMaxLoop (build_max_heap arr) (arr.length - 1) hbm_len).trans hbm_perm

/-- Property 3: The output of `heap_sort` has the same length as the input list. -/
def length_prop (arr : List Int) : Prop :=
  (heap_sort arr).length = arr.length

theorem length_thm (arr : List Int) (h : Pre arr) : length_prop arr :=
  (perm_thm arr h).length_eq

/-- Property 4: The output of `heap_sort` contains the exact same elements as the input list. -/
def mem_prop (arr : List Int) : Prop :=
  ∀ x : Int, x ∈ heap_sort arr ↔ x ∈ arr

theorem mem_thm (arr : List Int) (h : Pre arr) : mem_prop arr := by
  intro x
  exact (perm_thm arr h).mem_iff

/-- Property 5: The output of `heap_sort` preserves the count (multiplicity) of each element. -/
def count_prop (arr : List Int) : Prop :=
  ∀ x : Int, (heap_sort arr).count x = arr.count x

theorem count_thm (arr : List Int) (h : Pre arr) : count_prop arr := by
  intro x
  exact (perm_thm arr h).count_eq x

/-- Property 6: The output of `heap_sort` is sorted in non-decreasing order. -/
def sorted_prop (arr : List Int) : Prop :=
  (heap_sort arr).Pairwise (· ≤ ·)

theorem sorted_thm (arr : List Int) (_h : Pre arr) : sorted_prop arr := by
  unfold sorted_prop heap_sort
  split_ifs with hle
  · cases arr with
    | nil => exact List.Pairwise.nil
    | cons a as =>
      cases as with
      | nil => exact List.pairwise_singleton (· ≤ ·) a
      | cons b bs =>
        simp at hle
  · dsimp only
    apply pairwise_of_getElemD_sorted
    rw [length_extractMaxLoop, length_build_max_heap]
    have hlen : arr.length ≤ (build_max_heap arr).length := by
      rw [length_build_max_heap]
    have hk : arr.length - 1 < arr.length := by omega
    have hheap : IsMaxHeap (build_max_heap arr) (arr.length - 1 + 1) 0 := by
      have heq : arr.length - 1 + 1 = arr.length := by omega
      rw [heq]
      exact build_max_heap_isMaxHeap arr
    have hpref : HeapSuffixLe (build_max_heap arr) arr.length (arr.length - 1) := by
      intro i j _ hmj hjn
      omega
    have hsuf : SuffixSorted (build_max_heap arr) arr.length (arr.length - 1) := by
      intro i j hmi _ hjn
      omega
    exact extractMaxLoop_sorted (build_max_heap arr) arr.length (arr.length - 1)
      hlen hk hheap hpref hsuf

/-- Property 7: If the input list is already sorted, `heap_sort` returns it unchanged. -/
def already_sorted_prop (arr : List Int) : Prop :=
  arr.Pairwise (· ≤ ·) → heap_sort arr = arr

theorem already_sorted_thm (arr : List Int) (h : Pre arr) : already_sorted_prop arr := by
  intro hpw
  exact eq_of_pairwise_of_perm (sorted_thm arr h) hpw (perm_thm arr h)

/-- Property 8: `heap_sort` is idempotent: sorting an already sorted output changes nothing. -/
def idempotent_prop (arr : List Int) : Prop :=
  heap_sort (heap_sort arr) = heap_sort arr

theorem idempotent_thm (arr : List Int) (h : Pre arr) : idempotent_prop arr :=
  already_sorted_thm (heap_sort arr) trivial (sorted_thm arr h)

/-- Property 9: Reversing the input list does not change the sorted result. -/
def reverse_prop (arr : List Int) : Prop :=
  heap_sort arr.reverse = heap_sort arr

theorem reverse_thm (arr : List Int) (h : Pre arr) : reverse_prop arr := by
  unfold reverse_prop
  have h1 := sorted_thm arr.reverse trivial
  have h2 := sorted_thm arr h
  have hp1 := perm_thm arr.reverse trivial
  have hp2 := perm_thm arr h
  exact eq_of_pairwise_of_perm h1 h2 (hp1.trans ((List.reverse_perm arr).trans hp2.symm))

/-- Property 10: `build_max_heap` constructs a valid max-heap that is a permutation of `arr`. -/
def max_heap_prop (arr : List Int) : Prop :=
  IsMaxHeap (build_max_heap arr) arr.length 0 ∧ (build_max_heap arr).Perm arr

theorem max_heap_thm (arr : List Int) (_h : Pre arr) : max_heap_prop arr :=
  ⟨build_max_heap_isMaxHeap arr, perm_build_max_heap arr⟩

-- ============================================================================
-- Post-condition
-- ============================================================================

/-- Full post-condition of `heap_sort` combining all core specification properties. -/
def Post_prop (arr : List Int) : Prop :=
  base_case_prop arr ∧
  perm_prop arr ∧
  length_prop arr ∧
  mem_prop arr ∧
  count_prop arr ∧
  sorted_prop arr ∧
  already_sorted_prop arr ∧
  idempotent_prop arr ∧
  reverse_prop arr ∧
  max_heap_prop arr

-- ============================================================================
-- Property-Based Tests (PBTs)
-- ============================================================================

-- PBT for base_case_prop (randomized and bounded on small lists)
#eval Plausible.Testable.check (∀ arr : List Int,
  decide (arr.length ≤ 1 → heap_sort arr = arr))
example : ([ ([] : List Int), [0], [-5], [42] ]).all
    (fun arr => decide (arr.length ≤ 1 → heap_sort arr = arr)) = true := by native_decide

-- PBT for perm_prop
#eval Plausible.Testable.check (∀ arr : List Int,
  decide ((heap_sort arr).Perm arr))

-- PBT for length_prop
#eval Plausible.Testable.check (∀ arr : List Int,
  (heap_sort arr).length == arr.length)

-- PBT for mem_prop
#eval Plausible.Testable.check (∀ (arr : List Int) (x : Int),
  decide (x ∈ heap_sort arr ↔ x ∈ arr))

-- PBT for count_prop
#eval Plausible.Testable.check (∀ (arr : List Int) (x : Int),
  (heap_sort arr).count x == arr.count x)

-- PBT for sorted_prop
#eval Plausible.Testable.check (∀ arr : List Int,
  decide ((heap_sort arr).Pairwise (· ≤ ·)))

-- PBT for already_sorted_prop (randomized on sorted lists and bounded)
#eval Plausible.Testable.check (∀ arr : List Int,
  let s := heap_sort arr
  decide (s.Pairwise (· ≤ ·) → heap_sort s = s))
example : ([ ([] : List Int), [1], [1, 2], [1, 2, 3], [-3, 0, 0, 5] ]).all
    (fun arr => decide (arr.Pairwise (· ≤ ·) → heap_sort arr = arr)) = true := by native_decide

-- PBT for idempotent_prop
#eval Plausible.Testable.check (∀ arr : List Int,
  heap_sort (heap_sort arr) == heap_sort arr)

-- PBT for reverse_prop
#eval Plausible.Testable.check (∀ arr : List Int,
  heap_sort arr.reverse == heap_sort arr)

-- PBT for max_heap_prop
#eval Plausible.Testable.check (∀ arr : List Int,
  let h := build_max_heap arr
  let n := arr.length
  ((List.range n).all (fun k =>
    (if 2 * k + 1 < n then decide (getElemD h (2 * k + 1) ≤ getElemD h k) else true) &&
    (if 2 * k + 2 < n then decide (getElemD h (2 * k + 2) ≤ getElemD h k) else true)) &&
  decide (h.Perm arr)) = true)

-- PBT for Post_prop (executable form across all conjuncts)
#eval Plausible.Testable.check (∀ (arr : List Int) (x : Int),
  let h := build_max_heap arr
  let n := arr.length
  decide ((arr.length ≤ 1 → heap_sort arr = arr) ∧
    (heap_sort arr).Perm arr ∧
    (heap_sort arr).length = arr.length ∧
    (x ∈ heap_sort arr ↔ x ∈ arr) ∧
    (heap_sort arr).count x = arr.count x ∧
    (heap_sort arr).Pairwise (· ≤ ·) ∧
    (arr.Pairwise (· ≤ ·) → heap_sort arr = arr) ∧
    heap_sort (heap_sort arr) = heap_sort arr ∧
    heap_sort arr.reverse = heap_sort arr ∧
    (List.range n).all (fun k =>
      (if 2 * k + 1 < n then decide (getElemD h (2 * k + 1) ≤ getElemD h k) else true) &&
      (if 2 * k + 2 < n then decide (getElemD h (2 * k + 2) ≤ getElemD h k) else true)) = true ∧
    h.Perm arr))

-- ============================================================================
-- Correctness Theorem
-- ============================================================================

/-- Main correctness theorem: for any valid input `arr`, `Pre arr` implies `Post_prop arr`. -/
theorem heap_sort_correct (arr : List Int) (h : Pre arr) : Post_prop arr :=
  ⟨base_case_thm arr h,
   perm_thm arr h,
   length_thm arr h,
   mem_thm arr h,
   count_thm arr h,
   sorted_thm arr h,
   already_sorted_thm arr h,
   idempotent_thm arr h,
   reverse_thm arr h,
   max_heap_thm arr h⟩

-- ============================================================================
-- Imperative Implementation
-- ============================================================================

/-- Imperative sift-down (`heapify`) using mutable state in `Id.run do`. -/
def heapify_imp (arr : List Int) (n i : Nat) : List Int := Id.run do
  let mut result := arr
  let mut curr := i
  let mut active := true
  for _ in (List.range (n - i)).reverse do
    if active then
      let mut largest := curr
      let left := 2 * curr + 1
      let right := 2 * curr + 2
      if left < n && getElemD result left > getElemD result largest then
        largest := left
      if right < n && getElemD result right > getElemD result largest then
        largest := right
      if largest != curr then
        result := swap result curr largest
        curr := largest
      else
        active := false
  return result

/-- Imperative `build_max_heap` using mutable state in `Id.run do`. -/
def build_max_heap_imp (arr : List Int) : List Int := Id.run do
  let mut result := arr
  let n := result.length
  for i in (List.range (n / 2)).reverse do
    result := heapify_imp result n i
  return result

/-- Imperative `heap_sort` using mutable state in `Id.run do`. -/
def heap_sort_imp (arr : List Int) : List Int := Id.run do
  if arr.length ≤ 1 then
    return arr
  let mut result := arr
  let n := result.length
  result := build_max_heap_imp result
  for m in (List.range (n - 1)).reverse do
    let i := m + 1
    result := swap result 0 i
    result := heapify_imp result i 0
  return result

-- ============================================================================
-- Imperative Tests
-- ============================================================================

#eval heap_sort_imp [3, 1, 2]
#eval heap_sort_imp ([] : List Int)
#eval heap_sort_imp [1]
#eval heap_sort_imp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

example : heap_sort_imp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heap_sort_imp [1, 2, 3] = [1, 2, 3] := by native_decide
example : heap_sort_imp [2, 1, 3] = [1, 2, 3] := by native_decide
example : heap_sort_imp ([] : List Int) = [] := by native_decide
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

#eval Plausible.Testable.check (∀ arr : List Int,
  heap_sort arr == heap_sort_imp arr)

-- ============================================================================
-- Equivalence Theorem (Functional = Imperative)
-- ============================================================================

private theorem range_succ_reverse (m : Nat) :
    (List.range (m + 1)).reverse = m :: (List.range m).reverse := by
  rw [List.range_succ, List.reverse_append]
  rfl

private theorem heapify_imp_inactive (fuel : Nat) (arr : List Int) (n curr : Nat) :
    Id.run (do
      let mut result := arr
      let mut curr := curr
      let mut active := false
      for _ in (List.range fuel).reverse do
        if active then
          let mut largest := curr
          let left := 2 * curr + 1
          let right := 2 * curr + 2
          if left < n && getElemD result left > getElemD result largest then
            largest := left
          if right < n && getElemD result right > getElemD result largest then
            largest := right
          if largest != curr then
            result := swap result curr largest
            curr := largest
          else
            active := false
      return result) = arr := by
  induction fuel generalizing arr curr with
  | zero => rfl
  | succ fuel' ih =>
    rw [range_succ_reverse]
    simp only [Id.run, List.forIn_cons, bind, pure, Bool.false_eq_true, ↓reduceIte]
    exact ih arr curr

private theorem heapify_imp_active (fuel : Nat) (arr : List Int) (n curr : Nat) :
    Id.run (do
      let mut result := arr
      let mut curr := curr
      let mut active := true
      for _ in (List.range fuel).reverse do
        if active then
          let mut largest := curr
          let left := 2 * curr + 1
          let right := 2 * curr + 2
          if left < n && getElemD result left > getElemD result largest then
            largest := left
          if right < n && getElemD result right > getElemD result largest then
            largest := right
          if largest != curr then
            result := swap result curr largest
            curr := largest
          else
            active := false
      return result) = heapifyAux fuel arr n curr := by
  induction fuel generalizing arr curr with
  | zero => rfl
  | succ fuel' ih =>
    rw [range_succ_reverse]
    unfold heapifyAux chooseLargest
    dsimp only
    simp only [Id.run, List.forIn_cons, bind, pure, ↓reduceIte]
    split_ifs <;> simp only [Id.run, bind, pure] at *
    all_goals
      first
      | exact ih _ _
      | exact heapify_imp_inactive fuel' arr n curr

private theorem heapify_imp_eq (arr : List Int) (n i : Nat) :
    heapify_imp arr n i = heapify arr n i :=
  heapify_imp_active (n - i) arr n i

private theorem build_max_heap_imp_loop (arr : List Int) (n k : Nat) :
    Id.run (do
      let mut result := arr
      for i in (List.range k).reverse do
        result := heapify_imp result n i
      return result) = buildMaxHeapLoop arr n k := by
  induction k generalizing arr with
  | zero =>
    rfl
  | succ m ih =>
    rw [range_succ_reverse]
    simp only [Id.run, List.forIn_cons, bind, pure]
    rw [heapify_imp_eq]
    exact ih (heapify arr n m)

private theorem build_max_heap_imp_eq (arr : List Int) :
    build_max_heap_imp arr = build_max_heap arr :=
  build_max_heap_imp_loop arr arr.length (arr.length / 2)

private theorem extract_max_imp_loop (arr : List Int) (k : Nat) :
    Id.run (do
      let mut result := arr
      for m in (List.range k).reverse do
        let i := m + 1
        result := swap result 0 i
        result := heapify_imp result i 0
      return result) = extractMaxLoop arr k := by
  induction k generalizing arr with
  | zero =>
    rfl
  | succ m ih =>
    rw [range_succ_reverse]
    simp only [Id.run, List.forIn_cons, bind, pure]
    rw [heapify_imp_eq]
    exact ih (heapify (swap arr 0 (m + 1)) (m + 1) 0)

/-- Equivalence theorem: the functional implementation `heap_sort` and the imperative
implementation `heap_sort_imp` produce identical results on all inputs. -/
theorem heap_sort_equiv (arr : List Int) : heap_sort arr = heap_sort_imp arr := by
  unfold heap_sort heap_sort_imp
  by_cases hle : arr.length ≤ 1
  · simp [hle, Id.run, pure]
  · simp only [hle, ↓reduceIte, Id.run, bind, pure]
    rw [build_max_heap_imp_eq]
    exact (extract_max_imp_loop (build_max_heap arr) (arr.length - 1)).symm

end heap_sort
