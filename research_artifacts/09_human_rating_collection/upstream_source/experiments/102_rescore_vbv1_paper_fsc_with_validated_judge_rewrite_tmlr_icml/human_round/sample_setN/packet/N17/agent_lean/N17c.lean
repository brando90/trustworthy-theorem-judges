import Mathlib

/-!
# Heapsort Algorithm (CLRS 6.4)

Lean 4 formalization of the 0-based max-heap heapsort algorithm translated from Python.
Includes:
1. Functional implementation (`parent`, `left`, `right`, `swap`, `max_heapify`,
   `build_max_heap`, `heapsort`)
2. Unit tests (`example ... := by native_decide` and `#eval`)
3. Pre-condition (`Pre`)
4. Property propositions (`_prop`) and kernel-checked theorems (`_thm`)
5. Post-condition (`Post_prop` and `Post`)
6. Property-based tests (randomized `Plausible.Testable.check` and bounded `native_decide`)
7. Correctness theorem (`Pre → Post_prop`)
8. Imperative implementation (`max_heapify_imp`, `build_max_heap_imp`, `heapsort_imp`)
9. Imperative unit tests
10. Functional-imperative equivalence theorems (`max_heapify_equivalence`,
    `build_max_heap_equivalence`, `heapsort_equivalence`)
-/

namespace heapsort_algorithm

/-! ## 1. Functional Implementation -/

/-- Index of the parent node in a 0-based binary heap. -/
def parent (i : Nat) : Nat :=
  if i = 0 then 0 else (i - 1) / 2

/-- Index of the left child in a 0-based binary heap. -/
def left (i : Nat) : Nat :=
  2 * i + 1

/-- Index of the right child in a 0-based binary heap. -/
def right (i : Nat) : Nat :=
  2 * i + 2

/-- Swap two elements at indices `i` and `j` in a list of natural numbers. -/
def swap (arr : List Nat) (i j : Nat) : List Nat :=
  if i < arr.length ∧ j < arr.length then
    let vi := arr.getD i 0
    let vj := arr.getD j 0
    (arr.set i vj).set j vi
  else
    arr

/-- Maintain the max-heap property for the subtree rooted at index `i` within `heap_size`. -/
def max_heapify (arr : List Nat) (i heap_size : Nat) : List Nat :=
  let l_idx := left i
  let r_idx := right i
  let largest1 :=
    if l_idx < heap_size ∧ arr.getD l_idx 0 > arr.getD i 0 then
      l_idx
    else
      i
  let largest :=
    if r_idx < heap_size ∧ arr.getD r_idx 0 > arr.getD largest1 0 then
      r_idx
    else
      largest1
  if largest = i then
    arr
  else
    max_heapify (swap arr i largest) largest heap_size
termination_by heap_size - i
decreasing_by
  simp +zetaDelta only [left, right] at *
  split_ifs at * <;> omega

/-- Loop helper for building a max-heap from index `i` down to `0`. -/
def build_max_heap_loop (arr : List Nat) (i n : Nat) : List Nat :=
  let arr' := max_heapify arr i n
  match i with
  | 0 => arr'
  | i' + 1 => build_max_heap_loop arr' i' n

/-- Build a max-heap from an unsorted list of natural numbers. -/
def build_max_heap (arr : List Nat) : List Nat :=
  let n := arr.length
  if n ≤ 1 then
    arr
  else
    build_max_heap_loop arr (parent (n - 1)) n

/-- Loop helper for extracting the maximum element from the heap down to index `1`. -/
def extract_loop (arr : List Nat) : Nat → List Nat
  | 0 => arr
  | i + 1 =>
    let arr1 := swap arr 0 (i + 1)
    let arr2 := max_heapify arr1 0 (i + 1)
    extract_loop arr2 i

/-- Sort a list of naturals in ascending order using heapsort. -/
def heapsort (arr : List Nat) : List Nat :=
  if arr.length ≤ 1 then
    arr
  else
    let result := build_max_heap arr
    extract_loop result (result.length - 1)

/-! ## 2. Unit Tests -/

example : parent 0 = 0 := by native_decide
example : parent 1 = 0 := by native_decide
example : parent 2 = 0 := by native_decide
example : parent 3 = 1 := by native_decide
example : parent 4 = 1 := by native_decide
example : left 0 = 1 := by native_decide
example : right 0 = 2 := by native_decide
example : left 1 = 3 := by native_decide
example : right 1 = 4 := by native_decide

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

#eval heapsort [3, 1, 2]
#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]

/-! ## 3. Pre-condition -/

/-- Pre-condition for `heapsort`: any list of natural numbers is valid input. -/
def Pre (_arr : List Nat) : Prop := True

/-! ## 4. Helper Lemmas, Property Propositions, and Theorems -/

/-- Predicate stating that node `k` satisfies the max-heap ordering with its children
within `heap_size`. -/
def is_max_heap_node (arr : List Nat) (heap_size k : Nat) : Prop :=
  (left k < heap_size → arr.getD (left k) 0 ≤ arr.getD k 0) ∧
  (right k < heap_size → arr.getD (right k) 0 ≤ arr.getD k 0)

/-- Predicate stating that all nodes in `[low, heap_size)` satisfy the max-heap condition. -/
def is_max_heap_from (arr : List Nat) (heap_size low : Nat) : Prop :=
  ∀ k, low ≤ k → k < heap_size → is_max_heap_node arr heap_size k

/-- Predicate stating that `arr` forms a max-heap on indices `[0, heap_size)`. -/
def is_max_heap (arr : List Nat) (heap_size : Nat) : Prop :=
  is_max_heap_from arr heap_size 0

/-- Executable Boolean check for whether `arr` is a max-heap of size `heap_size`. -/
def is_max_heap_bool (arr : List Nat) (heap_size : Nat) : Bool :=
  (List.range heap_size).all fun k =>
    let l := left k
    let r := right k
    (!decide (l < heap_size) || decide (arr.getD l 0 ≤ arr.getD k 0)) &&
    (!decide (r < heap_size) || decide (arr.getD r 0 ≤ arr.getD k 0))

/-- Executable Boolean check for whether a list of naturals is sorted in non-decreasing order. -/
def is_sorted_bool (arr : List Nat) : Bool :=
  decide (List.Pairwise (· ≤ ·) arr)

@[simp]
theorem swap_length (arr : List Nat) (i j : Nat) : (swap arr i j).length = arr.length := by
  unfold swap
  split_ifs <;> simp

theorem getD_set_eq (arr : List Nat) (i k v : Nat) (hi : i < arr.length) :
    (arr.set i v).getD k 0 = if k = i then v else arr.getD k 0 := by
  simp only [List.getD, List.getElem?_set]
  split_ifs <;> first | rfl | omega

theorem getD_eq_getElem (arr : List Nat) (i : Nat) (hi : i < arr.length) :
    arr.getD i 0 = arr[i] := by
  simp [List.getD, hi]

theorem getD_swap (arr : List Nat) (i j k : Nat) (hi : i < arr.length) (hj : j < arr.length) :
    (swap arr i j).getD k 0 =
      if k = j then arr.getD i 0 else if k = i then arr.getD j 0 else arr.getD k 0 := by
  simp only [swap, hi, hj, and_self, ↓reduceIte]
  rw [getD_set_eq _ j k _ (by simp [hj])]
  rw [getD_set_eq _ i k _ hi]

theorem getD_swap_ne (arr : List Nat) (i j k : Nat) (hi : k ≠ i) (hj : k ≠ j) :
    (swap arr i j).getD k 0 = arr.getD k 0 := by
  unfold swap
  split_ifs with h
  · rw [getD_set_eq _ j k _ (by simp [h.2]), if_neg hj]
    rw [getD_set_eq _ i k _ h.1, if_neg hi]
  · rfl

theorem count_set_eq (arr : List Nat) (i v x : Nat) (hi : i < arr.length) :
    (arr.set i v).count x + (if arr.getD i 0 = x then 1 else 0) =
      arr.count x + (if v = x then 1 else 0) := by
  induction arr generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.getD_cons_zero, List.count_cons, beq_iff_eq]
      omega
    | succ i' =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      have h := ih i' hi
      simp only [List.set_cons_succ, List.getD_cons_succ, List.count_cons, beq_iff_eq] at h ⊢
      omega

theorem swap_perm (arr : List Nat) (i j : Nat) : (swap arr i j).Perm arr := by
  unfold swap
  dsimp only
  split_ifs with h
  · obtain ⟨hi, hj⟩ := h
    rw [List.perm_iff_count]
    intro x
    by_cases hij : i = j
    · subst hij
      have h1 := count_set_eq (arr.set i (arr.getD i 0)) i (arr.getD i 0) x (by simp [hi])
      have h2 := count_set_eq arr i (arr.getD i 0) x hi
      rw [getD_set_eq arr i i (arr.getD i 0) hi] at h1
      rw [if_pos rfl] at h1
      omega
    · have h1 := count_set_eq (arr.set i (arr.getD j 0)) j (arr.getD i 0) x (by simp [hj])
      have h2 := count_set_eq arr i (arr.getD j 0) x hi
      rw [getD_set_eq arr i j (arr.getD j 0) hi, if_neg (Ne.symm hij)] at h1
      omega
  · exact List.Perm.refl arr

@[simp]
theorem max_heapify_length (arr : List Nat) (i heap_size : Nat) :
    (max_heapify arr i heap_size).length = arr.length := by
  fun_induction max_heapify arr i heap_size with
  | case1 arr i l_idx r_idx largest1 largest h_eq =>
    rfl
  | case2 arr i l_idx r_idx largest1 largest h_ne ih =>
    rw [ih, swap_length]

theorem max_heapify_perm (arr : List Nat) (i heap_size : Nat) :
    (max_heapify arr i heap_size).Perm arr := by
  fun_induction max_heapify arr i heap_size with
  | case1 arr i l_idx r_idx largest1 largest h_eq =>
    exact List.Perm.refl arr
  | case2 arr i l_idx r_idx largest1 largest h_ne ih =>
    exact ih.trans (swap_perm arr i largest)

theorem max_heapify_getD_ge (arr : List Nat) (i heap_size k : Nat) (hk : heap_size ≤ k) :
    (max_heapify arr i heap_size).getD k 0 = arr.getD k 0 := by
  fun_induction max_heapify arr i heap_size with
  | case1 arr i l_idx r_idx largest1 largest h_eq =>
    rfl
  | case2 arr i l_idx r_idx largest1 largest h_ne ih =>
    have h_bounds : i < largest ∧ largest < heap_size := by
      simp +zetaDelta only [left, right] at h_ne ⊢
      split_ifs at h_ne ⊢ <;> omega
    rw [ih, getD_swap_ne arr i largest k (by omega) (by omega)]

theorem max_heapify_getD_lt (arr : List Nat) (i heap_size k : Nat) (hk : k < i) :
    (max_heapify arr i heap_size).getD k 0 = arr.getD k 0 := by
  fun_induction max_heapify arr i heap_size with
  | case1 arr i l_idx r_idx largest1 largest h_eq =>
    rfl
  | case2 arr i l_idx r_idx largest1 largest h_ne ih =>
    have h_bounds : i < largest ∧ largest < heap_size := by
      simp +zetaDelta only [left, right] at h_ne ⊢
      split_ifs at h_ne ⊢ <;> omega
    rw [ih (by omega), getD_swap_ne arr i largest k (by omega) (by omega)]

theorem max_heapify_heap_aux (arr : List Nat) (i heap_size low : Nat)
    (h_size : heap_size ≤ arr.length)
    (h_low : low ≤ i)
    (h_others : ∀ k, low ≤ k → k < heap_size → k ≠ i → is_max_heap_node arr heap_size k)
    (h_anc : ∀ k, low ≤ k → k < heap_size → (left k = i ∨ right k = i) →
      (left i < heap_size → arr.getD (left i) 0 ≤ arr.getD k 0) ∧
      (right i < heap_size → arr.getD (right i) 0 ≤ arr.getD k 0)) :
    is_max_heap_from (max_heapify arr i heap_size) heap_size low := by
  fun_induction max_heapify arr i heap_size with
  | case1 arr i l_idx r_idx largest1 largest h_eq =>
    intro k hk_low hk_lt
    by_cases hki : k = i
    · subst hki
      have h_node : (left k < heap_size → arr.getD (left k) 0 ≤ arr.getD k 0) ∧
          (right k < heap_size → arr.getD (right k) 0 ≤ arr.getD k 0) := by
        simp +zetaDelta only [left, right] at h_eq ⊢
        split_ifs at h_eq <;> omega
      exact h_node
    · exact h_others k hk_low hk_lt hki
  | case2 arr i l_idx r_idx largest1 largest h_ne ih =>
    have h_step : (largest = left i ∨ largest = right i) ∧
        i < largest ∧ largest < heap_size ∧
        arr.getD i 0 < arr.getD largest 0 ∧
        (left i < heap_size → arr.getD (left i) 0 ≤ arr.getD largest 0) ∧
        (right i < heap_size → arr.getD (right i) 0 ≤ arr.getD largest 0) := by
      simp +zetaDelta only [left, right] at h_ne ⊢
      split_ifs at h_ne ⊢ <;> omega
    rcases h_step with ⟨h_lr, h_i_lt, h_larg_lt, h_val_lt, h_le_l, h_le_r⟩
    have hi_len : i < arr.length := by omega
    have hlarg_len : largest < arr.length := by omega
    apply ih
    · rw [swap_length]; exact h_size
    · omega
    · intro k hk_low hk_lt hk_ne_larg
      by_cases hki : k = i
      · subst hki
        constructor <;> intro h_ch
        · have h_le := h_le_l h_ch
          rw [getD_swap arr k largest (left k) hi_len hlarg_len,
              getD_swap arr k largest k hi_len hlarg_len]
          simp only [left, right] at h_lr h_le ⊢
          split_ifs <;> omega
        · have h_le := h_le_r h_ch
          rw [getD_swap arr k largest (right k) hi_len hlarg_len,
              getD_swap arr k largest k hi_len hlarg_len]
          simp only [left, right] at h_lr h_le ⊢
          split_ifs <;> omega
      · have hk_old := h_others k hk_low hk_lt hki
        have hk_val : (swap arr i largest).getD k 0 = arr.getD k 0 :=
          getD_swap_ne arr i largest k hki hk_ne_larg
        have h_lk_ne_larg : left k ≠ largest := by
          simp only [left, right] at h_lr ⊢; omega
        have h_rk_ne_larg : right k ≠ largest := by
          simp only [left, right] at h_lr ⊢; omega
        constructor
        · intro h_lk
          rw [hk_val]
          by_cases h_lki : left k = i
          · rw [h_lki, getD_swap arr i largest i hi_len hlarg_len]
            simp only [Nat.ne_of_lt h_i_lt, ↓reduceIte]
            have h_anc_k := h_anc k hk_low hk_lt (Or.inl h_lki)
            rcases h_lr with h_eq_l | h_eq_r
            · rw [h_eq_l] at h_larg_lt ⊢; exact h_anc_k.1 h_larg_lt
            · rw [h_eq_r] at h_larg_lt ⊢; exact h_anc_k.2 h_larg_lt
          · rw [getD_swap_ne arr i largest (left k) h_lki h_lk_ne_larg]
            exact hk_old.1 h_lk
        · intro h_rk
          rw [hk_val]
          by_cases h_rki : right k = i
          · rw [h_rki, getD_swap arr i largest i hi_len hlarg_len]
            simp only [Nat.ne_of_lt h_i_lt, ↓reduceIte]
            have h_anc_k := h_anc k hk_low hk_lt (Or.inr h_rki)
            rcases h_lr with h_eq_l | h_eq_r
            · rw [h_eq_l] at h_larg_lt ⊢; exact h_anc_k.1 h_larg_lt
            · rw [h_eq_r] at h_larg_lt ⊢; exact h_anc_k.2 h_larg_lt
          · rw [getD_swap_ne arr i largest (right k) h_rki h_rk_ne_larg]
            exact hk_old.2 h_rk
    · intro k hk_low hk_lt h_ch_larg
      have hki : k = i := by
        simp only [left, right] at h_lr h_ch_larg; omega
      subst hki
      have h_larg_old := h_others largest (by omega) h_larg_lt (by omega)
      have h_k_val : (swap arr k largest).getD k 0 = arr.getD largest 0 := by
        rw [getD_swap arr k largest k hi_len hlarg_len]
        simp [Nat.ne_of_lt h_i_lt]
      have h_ll_val : (swap arr k largest).getD (left largest) 0 = arr.getD (left largest) 0 := by
        apply getD_swap_ne <;> (simp only [left, right] at h_lr ⊢; omega)
      have h_rl_val : (swap arr k largest).getD (right largest) 0 = arr.getD (right largest) 0 := by
        apply getD_swap_ne <;> (simp only [left, right] at h_lr ⊢; omega)
      rw [h_k_val, h_ll_val, h_rl_val]
      exact h_larg_old

theorem max_heapify_heap (arr : List Nat) (i heap_size : Nat)
    (h_size : heap_size ≤ arr.length)
    (h_sub : is_max_heap_from arr heap_size (i + 1)) :
    is_max_heap_from (max_heapify arr i heap_size) heap_size i := by
  apply max_heapify_heap_aux arr i heap_size i h_size (Nat.le_refl i)
  · intro k hk_low hk_lt hk_ne
    exact h_sub k (by omega) hk_lt
  · intro k hk_low _ h_ch
    simp only [left, right] at h_ch
    omega

theorem max_heapify_le_bound (arr : List Nat) (i heap_size bound : Nat)
    (h_size : heap_size ≤ arr.length)
    (h_bound : ∀ k, k < heap_size → arr.getD k 0 ≤ bound) :
    ∀ k, k < heap_size → (max_heapify arr i heap_size).getD k 0 ≤ bound := by
  fun_induction max_heapify arr i heap_size with
  | case1 arr i l_idx r_idx largest1 largest h_eq =>
    exact h_bound
  | case2 arr i l_idx r_idx largest1 largest h_ne ih =>
    have h_bounds : i < largest ∧ largest < heap_size := by
      simp +zetaDelta only [left, right] at h_ne ⊢
      split_ifs at h_ne ⊢ <;> omega
    apply ih (by rw [swap_length]; exact h_size)
    intro k hk
    rw [getD_swap arr i largest k (by omega) (by omega)]
    split_ifs
    · exact h_bound i (by omega)
    · exact h_bound largest (by omega)
    · exact h_bound k hk

@[simp]
theorem build_max_heap_loop_length (arr : List Nat) (i n : Nat) :
    (build_max_heap_loop arr i n).length = arr.length := by
  induction i generalizing arr with
  | zero => simp [build_max_heap_loop]
  | succ i' ih => simp [build_max_heap_loop, ih]

theorem build_max_heap_loop_perm (arr : List Nat) (i n : Nat) :
    (build_max_heap_loop arr i n).Perm arr := by
  induction i generalizing arr with
  | zero =>
    simp only [build_max_heap_loop]
    exact max_heapify_perm arr 0 n
  | succ i' ih =>
    simp only [build_max_heap_loop]
    exact (ih (max_heapify arr (i' + 1) n)).trans (max_heapify_perm arr (i' + 1) n)

theorem build_max_heap_loop_heap (arr : List Nat) (i n : Nat)
    (hn : n ≤ arr.length)
    (h_sub : is_max_heap_from arr n (i + 1)) :
    is_max_heap (build_max_heap_loop arr i n) n := by
  induction i generalizing arr with
  | zero =>
    simp only [build_max_heap_loop, is_max_heap]
    exact max_heapify_heap arr 0 n hn h_sub
  | succ i' ih =>
    simp only [build_max_heap_loop]
    apply ih (max_heapify arr (i' + 1) n)
    · rw [max_heapify_length]; exact hn
    · exact max_heapify_heap arr (i' + 1) n hn h_sub

@[simp]
theorem build_max_heap_length (arr : List Nat) :
    (build_max_heap arr).length = arr.length := by
  unfold build_max_heap
  dsimp only
  split_ifs <;> simp

theorem build_max_heap_perm (arr : List Nat) :
    (build_max_heap arr).Perm arr := by
  unfold build_max_heap
  dsimp only
  split_ifs
  · exact List.Perm.refl arr
  · exact build_max_heap_loop_perm arr (parent (arr.length - 1)) arr.length

theorem build_max_heap_heap (arr : List Nat) :
    is_max_heap (build_max_heap arr) arr.length := by
  unfold build_max_heap
  dsimp only
  split_ifs with h
  · intro k _ hk
    constructor <;> (intro h_ch; simp only [left, right] at h_ch; omega)
  · apply build_max_heap_loop_heap arr (parent (arr.length - 1)) arr.length (Nat.le_refl _)
    intro k hk_low hk_lt
    simp only [parent] at hk_low
    constructor <;> (intro h_ch; simp only [left, right] at h_ch; split_ifs at hk_low <;> omega)

theorem is_max_heap_zero_ge (arr : List Nat) (heap_size k : Nat)
    (h_heap : is_max_heap arr heap_size) (hk : k < heap_size) :
    arr.getD k 0 ≤ arr.getD 0 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk0 : k = 0
    · subst hk0; exact Nat.le_refl _
    · let p := (k - 1) / 2
      have hp_lt : p < k := by omega
      have hp_heap : p < heap_size := by omega
      have h_ih := ih p hp_lt hp_heap
      have h_node := h_heap p (Nat.zero_le p) hp_heap
      have h_ch : k = left p ∨ k = right p := by
        simp only [left, right, p]; omega
      rcases h_ch with h_l | h_r
      · rw [h_l] at hk ⊢; exact Nat.le_trans (h_node.1 hk) h_ih
      · rw [h_r] at hk ⊢; exact Nat.le_trans (h_node.2 hk) h_ih

@[simp]
theorem extract_loop_length (arr : List Nat) (m : Nat) :
    (extract_loop arr m).length = arr.length := by
  induction m generalizing arr with
  | zero => rfl
  | succ i ih => simp [extract_loop, ih]

theorem extract_loop_perm (arr : List Nat) (m : Nat) :
    (extract_loop arr m).Perm arr := by
  induction m generalizing arr with
  | zero => exact List.Perm.refl arr
  | succ i ih =>
    simp only [extract_loop]
    exact (ih _).trans ((max_heapify_perm _ 0 (i + 1)).trans (swap_perm arr 0 (i + 1)))

theorem extract_loop_sorted_aux (arr : List Nat) (m : Nat)
    (hm : m < arr.length)
    (h_heap : is_max_heap arr (m + 1))
    (h_part : ∀ k j, k ≤ m → m < j → j < arr.length → arr.getD k 0 ≤ arr.getD j 0)
    (h_suff : ∀ j₁ j₂, m < j₁ → j₁ ≤ j₂ → j₂ < arr.length → arr.getD j₁ 0 ≤ arr.getD j₂ 0) :
    ∀ j₁ j₂, j₁ ≤ j₂ → j₂ < arr.length →
      (extract_loop arr m).getD j₁ 0 ≤ (extract_loop arr m).getD j₂ 0 := by
  induction m generalizing arr with
  | zero =>
    intro j₁ j₂ hj₁₂ hj₂
    simp only [extract_loop]
    by_cases hj₁0 : j₁ = 0
    · subst hj₁0
      by_cases hj₂0 : j₂ = 0
      · subst hj₂0; exact Nat.le_refl _
      · exact h_part 0 j₂ (Nat.le_refl 0) (by omega) hj₂
    · exact h_suff j₁ j₂ (by omega) hj₁₂ hj₂
  | succ i ih =>
    simp only [extract_loop]
    set arr1 := swap arr 0 (i + 1)
    set arr2 := max_heapify arr1 0 (i + 1)
    have h_len1 : arr1.length = arr.length := swap_length arr 0 (i + 1)
    have h_len2 : arr2.length = arr.length := by rw [max_heapify_length, h_len1]
    have h0_len : 0 < arr.length := by omega
    have hi1_len : i + 1 < arr.length := hm
    have h_arr1_i1 : arr1.getD (i + 1) 0 = arr.getD 0 0 := by
      rw [getD_swap arr 0 (i + 1) (i + 1) h0_len hi1_len]
      simp
    have h_arr1_gt : ∀ j, i + 1 < j → arr1.getD j 0 = arr.getD j 0 := by
      intro j hj
      exact getD_swap_ne arr 0 (i + 1) j (by omega) (by omega)
    have h_arr1_bound : ∀ k, k < i + 1 → arr1.getD k 0 ≤ arr.getD 0 0 := by
      intro k hk
      rw [getD_swap arr 0 (i + 1) k h0_len hi1_len]
      split_ifs with h1 h2
      · omega
      · exact is_max_heap_zero_ge arr (i + 2) (i + 1) h_heap (by omega)
      · exact is_max_heap_zero_ge arr (i + 2) k h_heap (by omega)
    have h_arr1_sub : is_max_heap_from arr1 (i + 1) 1 := by
      intro k hk_low hk_lt
      have hk_node := h_heap k (by omega) (by omega)
      have hk_val : arr1.getD k 0 = arr.getD k 0 :=
        getD_swap_ne arr 0 (i + 1) k (by omega) (by omega)
      constructor
      · intro h_lk
        have h_lk_val : arr1.getD (left k) 0 = arr.getD (left k) 0 :=
          getD_swap_ne arr 0 (i + 1) (left k) (by simp [left]) (by omega)
        rw [hk_val, h_lk_val]
        exact hk_node.1 (by omega)
      · intro h_rk
        have h_rk_val : arr1.getD (right k) 0 = arr.getD (right k) 0 :=
          getD_swap_ne arr 0 (i + 1) (right k) (by simp [right]) (by omega)
        rw [hk_val, h_rk_val]
        exact hk_node.2 (by omega)
    have h_arr2_heap : is_max_heap arr2 (i + 1) :=
      max_heapify_heap arr1 0 (i + 1) (by omega) h_arr1_sub
    have h_arr2_bound : ∀ k, k < i + 1 → arr2.getD k 0 ≤ arr.getD 0 0 :=
      max_heapify_le_bound arr1 0 (i + 1) (arr.getD 0 0) (by omega) h_arr1_bound
    have h_arr2_ge : ∀ j, i + 1 ≤ j → arr2.getD j 0 = arr1.getD j 0 :=
      fun j hj => max_heapify_getD_ge arr1 0 (i + 1) j hj
    have h_ih := ih arr2 (by omega) h_arr2_heap
      (by
        intro k j hk hj hj_len
        have hk_le : arr2.getD k 0 ≤ arr.getD 0 0 := h_arr2_bound k (by omega)
        rw [h_arr2_ge j (by omega)]
        by_cases hj_eq : j = i + 1
        · subst hj_eq; rw [h_arr1_i1]; exact hk_le
        · rw [h_arr1_gt j (by omega)]
          exact Nat.le_trans hk_le (h_part 0 j (by omega) (by omega) (by omega)))
      (by
        intro j₁ j₂ hj₁ hj₁₂ hj₂_len
        rw [h_arr2_ge j₁ (by omega), h_arr2_ge j₂ (by omega)]
        by_cases hj₁_eq : j₁ = i + 1
        · subst hj₁_eq
          rw [h_arr1_i1]
          by_cases hj₂_eq : j₂ = i + 1
          · subst hj₂_eq; rw [h_arr1_i1]
          · rw [h_arr1_gt j₂ (by omega)]
            exact h_part 0 j₂ (by omega) (by omega) (by omega)
        · rw [h_arr1_gt j₁ (by omega), h_arr1_gt j₂ (by omega)]
          exact h_suff j₁ j₂ (by omega) hj₁₂ (by omega))
    intro j₁ j₂ hj₁₂ hj₂
    exact h_ih j₁ j₂ hj₁₂ (by omega)

/-- Property: the parent of `left i` is `i`. -/
def parent_left_prop (i : Nat) : Prop :=
  parent (left i) = i

theorem parent_left_thm (i : Nat) : parent_left_prop i := by
  unfold parent_left_prop parent left
  rw [if_neg (by omega)]
  omega

/-- Property: the parent of `right i` is `i`. -/
def parent_right_prop (i : Nat) : Prop :=
  parent (right i) = i

theorem parent_right_thm (i : Nat) : parent_right_prop i := by
  unfold parent_right_prop parent right
  rw [if_neg (by omega)]
  omega

/-- Property: `left i` is strictly greater than `i`. -/
def left_gt_prop (i : Nat) : Prop :=
  i < left i

theorem left_gt_thm (i : Nat) : left_gt_prop i := by
  unfold left_gt_prop left
  omega

/-- Property: `right i` is strictly greater than `i`. -/
def right_gt_prop (i : Nat) : Prop :=
  i < right i

theorem right_gt_thm (i : Nat) : right_gt_prop i := by
  unfold right_gt_prop right
  omega

/-- Property: `build_max_heap` produces a valid max-heap that is a length-preserving
permutation of the input list. -/
def build_max_heap_prop (arr : List Nat) : Prop :=
  is_max_heap (build_max_heap arr) arr.length ∧
  (build_max_heap arr).length = arr.length ∧
  (build_max_heap arr).Perm arr

theorem build_max_heap_thm (arr : List Nat) : build_max_heap_prop arr :=
  ⟨build_max_heap_heap arr, build_max_heap_length arr, build_max_heap_perm arr⟩

/-- Property: `heapsort` returns a list sorted in non-decreasing order. -/
def sorted_prop (arr : List Nat) : Prop :=
  List.Pairwise (· ≤ ·) (heapsort arr)

theorem sorted_thm (arr : List Nat) : sorted_prop arr := by
  unfold sorted_prop
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [← getD_eq_getElem _ i hi, ← getD_eq_getElem _ j hj]
  unfold heapsort at hi hj ⊢
  split_ifs at hi hj ⊢ with h_le
  · omega
  · set result := build_max_heap arr
    have h_res_len : result.length = arr.length := build_max_heap_length arr
    have h_res_heap : is_max_heap result ((result.length - 1) + 1) := by
      rw [Nat.sub_add_cancel (by omega), h_res_len]
      exact build_max_heap_heap arr
    apply extract_loop_sorted_aux result (result.length - 1) (by omega) h_res_heap
    · intro k l _ hl hl_len; omega
    · intro j₁ j₂ hj₁ _ hj₂_len; omega
    · omega
    · rw [extract_loop_length] at hj; exact hj

/-- Property: `heapsort` preserves the length of the input list. -/
def length_prop (arr : List Nat) : Prop :=
  (heapsort arr).length = arr.length

@[simp]
theorem length_thm (arr : List Nat) : length_prop arr := by
  unfold length_prop heapsort
  split_ifs <;> simp

/-- Property: `heapsort` returns a permutation of the input list. -/
def perm_prop (arr : List Nat) : Prop :=
  (heapsort arr).Perm arr

theorem perm_thm (arr : List Nat) : perm_prop arr := by
  unfold perm_prop heapsort
  split_ifs
  · exact List.Perm.refl arr
  · exact (extract_loop_perm (build_max_heap arr) _).trans (build_max_heap_perm arr)

/-- Property: `heapsort` agrees with `List.mergeSort` on every input list. -/
def eq_mergeSort_prop (arr : List Nat) : Prop :=
  heapsort arr = arr.mergeSort

theorem eq_mergeSort_thm (arr : List Nat) : eq_mergeSort_prop arr := by
  unfold eq_mergeSort_prop
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact (perm_thm arr).trans (List.mergeSort_perm arr _).symm
  · exact sorted_thm arr
  · have hp := List.sorted_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (by intro a b c; simp; omega) (by intro a b; simp; omega) arr
    simpa [List.Sorted] using hp

/-- Property: sorting the output of `heapsort` with `List.mergeSort` equals sorting the input. -/
def mergeSort_invariant_prop (arr : List Nat) : Prop :=
  (heapsort arr).mergeSort = arr.mergeSort

theorem mergeSort_invariant_thm (arr : List Nat) : mergeSort_invariant_prop arr := by
  unfold mergeSort_invariant_prop
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact (List.mergeSort_perm (heapsort arr) _).trans
      ((perm_thm arr).trans (List.mergeSort_perm arr _).symm)
  · have hp := List.sorted_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (by intro a b c; simp; omega) (by intro a b; simp; omega) (heapsort arr)
    simpa [List.Sorted] using hp
  · have hp := List.sorted_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (by intro a b c; simp; omega) (by intro a b; simp; omega) arr
    simpa [List.Sorted] using hp

/-- Property: `heapsort` is idempotent. -/
def idempotent_prop (arr : List Nat) : Prop :=
  heapsort (heapsort arr) = heapsort arr

theorem idempotent_thm (arr : List Nat) : idempotent_prop arr := by
  unfold idempotent_prop
  rw [eq_mergeSort_thm (heapsort arr), mergeSort_invariant_thm arr, ← eq_mergeSort_thm arr]

/-! ## 5. Post-condition -/

/-- Relational post-condition for `heapsort` relating input `arr` and output `out`. -/
def Post (arr : List Nat) (out : List Nat) : Prop :=
  List.Pairwise (· ≤ ·) out ∧
  out.length = arr.length ∧
  out.Perm arr ∧
  out = arr.mergeSort ∧
  out.mergeSort = arr.mergeSort

/-- Post-condition predicate as the conjunction of all primary properties of `heapsort`. -/
def Post_prop (arr : List Nat) : Prop :=
  sorted_prop arr ∧
  length_prop arr ∧
  perm_prop arr ∧
  eq_mergeSort_prop arr ∧
  mergeSort_invariant_prop arr ∧
  idempotent_prop arr

/-! ## 6. Property-Based Tests -/

-- Randomized property-based tests via Plausible
#eval Plausible.Testable.check (∀ i : Nat, parent (left i) = i)
#eval Plausible.Testable.check (∀ i : Nat, parent (right i) = i)
#eval Plausible.Testable.check (∀ i : Nat, i < left i)
#eval Plausible.Testable.check (∀ i : Nat, i < right i)
#eval Plausible.Testable.check (∀ arr : List Nat,
  is_max_heap_bool (build_max_heap arr) arr.length = true ∧
  (build_max_heap arr).length = arr.length)
#eval Plausible.Testable.check (∀ arr : List Nat, is_sorted_bool (heapsort arr) = true)
#eval Plausible.Testable.check (∀ arr : List Nat, (heapsort arr).length = arr.length)
#eval Plausible.Testable.check (∀ arr : List Nat, decide ((heapsort arr).Perm arr) = true)
#eval Plausible.Testable.check (∀ arr : List Nat, heapsort arr = arr.mergeSort)
#eval Plausible.Testable.check (∀ arr : List Nat, (heapsort arr).mergeSort = arr.mergeSort)
#eval Plausible.Testable.check (∀ arr : List Nat, heapsort (heapsort arr) = heapsort arr)
#eval Plausible.Testable.check (∀ arr : List Nat,
  is_sorted_bool (heapsort arr) = true ∧
  (heapsort arr).length = arr.length ∧
  heapsort arr = arr.mergeSort ∧
  (heapsort arr).mergeSort = arr.mergeSort ∧
  heapsort (heapsort arr) = heapsort arr)

-- Bounded exhaustive property-based tests via native_decide
example : (List.range 50).all (fun i => decide (parent (left i) = i)) = true := by native_decide
example : (List.range 50).all (fun i => decide (parent (right i) = i)) = true := by native_decide
example : (List.range 50).all (fun i => decide (i < left i ∧ i < right i)) = true := by native_decide
example :
    ([[], [1], [2, 1], [3, 1, 2], [5, 13, 2, 25, 7, 17, 20, 8, 4],
      [9, 8, 7, 6, 5, 4, 3, 2, 1], [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]] : List (List Nat)).all
      (fun arr =>
        is_max_heap_bool (build_max_heap arr) arr.length &&
        is_sorted_bool (heapsort arr) &&
        decide ((heapsort arr).length = arr.length) &&
        decide ((heapsort arr).Perm arr) &&
        decide (heapsort arr = arr.mergeSort) &&
        decide ((heapsort arr).mergeSort = arr.mergeSort) &&
        decide (heapsort (heapsort arr) = heapsort arr)) = true := by
  native_decide

/-! ## 7. Correctness Theorem: `Pre → Post` -/

/-- Main correctness theorem: under `Pre arr`, `heapsort` satisfies `Post_prop arr`. -/
theorem heapsort_correct (arr : List Nat) (_h : Pre arr) : Post_prop arr :=
  ⟨sorted_thm arr,
   length_thm arr,
   perm_thm arr,
   eq_mergeSort_thm arr,
   mergeSort_invariant_thm arr,
   idempotent_thm arr⟩

/-- Relational specification theorem: under `Pre arr`, `heapsort arr` satisfies `Post arr`. -/
theorem heapsort_spec (arr : List Nat) (_h : Pre arr) : Post arr (heapsort arr) :=
  ⟨sorted_thm arr,
   length_thm arr,
   perm_thm arr,
   eq_mergeSort_thm arr,
   mergeSort_invariant_thm arr⟩

/-! ## 8. Imperative Implementation -/

/-- Imperative `max_heapify` using `Id.run do` and mutable state. -/
def max_heapify_imp (arr : List Nat) (i heap_size : Nat) : List Nat := Id.run do
  let mut result := arr
  let mut curr := i
  for _ in List.range (heap_size - i) do
    let l_idx := left curr
    let r_idx := right curr
    let largest1 :=
      if l_idx < heap_size ∧ result.getD l_idx 0 > result.getD curr 0 then
        l_idx
      else
        curr
    let largest :=
      if r_idx < heap_size ∧ result.getD r_idx 0 > result.getD largest1 0 then
        r_idx
      else
        largest1
    result := if largest = curr then result else swap result curr largest
    curr := largest
  return result

/-- Imperative `build_max_heap` using `Id.run do` and mutable state. -/
def build_max_heap_imp (arr : List Nat) : List Nat := Id.run do
  if arr.length ≤ 1 then
    return arr
  let mut result := arr
  let n := result.length
  for i in (List.range (parent (n - 1) + 1)).reverse do
    result := max_heapify_imp result i n
  return result

/-- Imperative `heapsort` using `Id.run do` and mutable state. -/
def heapsort_imp (arr : List Nat) : List Nat := Id.run do
  if arr.length ≤ 1 then
    return arr
  let mut result := build_max_heap_imp arr
  for i in ((List.range (result.length - 1)).map (· + 1)).reverse do
    result := swap result 0 i
    result := max_heapify_imp result 0 i
  return result

/-! ## 9. Imperative Tests -/

example : heapsort_imp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsort_imp [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsort_imp [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by native_decide
example : heapsort_imp [] = [] := by native_decide
example : heapsort_imp [42] = [42] := by native_decide
example : heapsort_imp [2, 1] = [1, 2] := by native_decide
example : heapsort_imp [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsort_imp [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapsort_imp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapsort_imp [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by native_decide
example : heapsort_imp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsort_imp [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : heapsort_imp [2, 1] ≠ [2, 1] := by native_decide

#eval heapsort_imp [3, 1, 2]
#eval heapsort_imp [5, 13, 2, 25, 7, 17, 20, 8, 4]

/-! ## 10. Functional-Imperative Equivalence Theorems -/

/-- Pure transition function for a single step of `max_heapify_imp`. -/
def heapify_step (heap_size : Nat) (st : MProd Nat (List Nat)) : MProd Nat (List Nat) :=
  let curr := st.fst
  let result := st.snd
  let l_idx := left curr
  let r_idx := right curr
  let largest1 := if l_idx < heap_size ∧ result.getD l_idx 0 > result.getD curr 0 then l_idx else curr
  let largest := if r_idx < heap_size ∧ result.getD r_idx 0 > result.getD largest1 0 then r_idx else largest1
  ⟨largest, if largest = curr then result else swap result curr largest⟩

theorem foldl_const_range (f : α → α) (n : Nat) (init : α) :
    (List.range n).foldl (fun acc _ => f acc) init = Nat.repeat f n init := by
  induction n generalizing init with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Nat.repeat]

theorem repeat_fixed (f : α → α) (n : Nat) (x : α) (hx : f x = x) :
    Nat.repeat f n x = x := by
  induction n with
  | zero => rfl
  | succ k ih => simp [Nat.repeat, ih, hx]

theorem repeat_succ_apply (f : α → α) (n : Nat) (x : α) :
    Nat.repeat f (n + 1) x = Nat.repeat f n (f x) := by
  induction n generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [Nat.repeat]
    congr 1
    exact ih x

theorem max_heapify_eq_repeat (arr : List Nat) (i heap_size n : Nat)
    (hn : heap_size - i ≤ n) :
    (Nat.repeat (heapify_step heap_size) n ⟨i, arr⟩).snd = max_heapify arr i heap_size := by
  fun_induction max_heapify arr i heap_size generalizing n with
  | case1 arr i l_idx r_idx largest1 largest h_eq =>
    have h_fix : heapify_step heap_size ⟨i, arr⟩ = ⟨i, arr⟩ := by
      change (⟨largest, if largest = i then arr else swap arr i largest⟩ : MProd Nat (List Nat)) = ⟨i, arr⟩
      rw [if_pos h_eq, h_eq]
    rw [repeat_fixed _ n _ h_fix]
  | case2 arr i l_idx r_idx largest1 largest h_ne ih =>
    have h_bounds : i < largest ∧ largest < heap_size := by
      simp +zetaDelta only [left, right] at h_ne ⊢
      split_ifs at h_ne ⊢ <;> omega
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [repeat_succ_apply]
    have h_step : heapify_step heap_size ⟨i, arr⟩ = ⟨largest, swap arr i largest⟩ := by
      change (⟨largest, if largest = i then arr else swap arr i largest⟩ : MProd Nat (List Nat)) = ⟨largest, swap arr i largest⟩
      rw [if_neg h_ne]
    rw [h_step]
    exact ih k (by omega)

/-- Equivalence between functional `max_heapify` and imperative `max_heapify_imp`. -/
theorem max_heapify_equivalence (arr : List Nat) (i heap_size : Nat) :
    max_heapify arr i heap_size = max_heapify_imp arr i heap_size := by
  have h : max_heapify_imp arr i heap_size =
      ((List.range (heap_size - i)).foldl (fun r _ => heapify_step heap_size r) ⟨i, arr⟩).snd := by
    unfold max_heapify_imp heapify_step
    simp
  rw [h, foldl_const_range, max_heapify_eq_repeat arr i heap_size (heap_size - i) (Nat.le_refl _)]

theorem build_max_heap_loop_eq_foldl (arr : List Nat) (k n : Nat) :
    build_max_heap_loop arr k n =
      (List.range (k + 1)).reverse.foldl (fun acc i => max_heapify_imp acc i n) arr := by
  induction k generalizing arr with
  | zero => simp [build_max_heap_loop, ← max_heapify_equivalence]
  | succ k' ih =>
    simp [build_max_heap_loop, List.range_succ, ih, ← max_heapify_equivalence]

theorem extract_loop_eq_foldl (arr : List Nat) (m : Nat) :
    extract_loop arr m =
      ((List.range m).map (· + 1)).reverse.foldl
        (fun acc i => max_heapify_imp (swap acc 0 i) 0 i) arr := by
  induction m generalizing arr with
  | zero => simp [extract_loop]
  | succ i ih =>
    simp [extract_loop, List.range_succ, ih, ← max_heapify_equivalence]

/-- Equivalence between functional `build_max_heap` and imperative `build_max_heap_imp`. -/
theorem build_max_heap_equivalence (arr : List Nat) :
    build_max_heap arr = build_max_heap_imp arr := by
  unfold build_max_heap build_max_heap_imp
  dsimp only
  split_ifs with h
  · simp
  · simp [build_max_heap_loop_eq_foldl]

/-- Equivalence between functional `heapsort` and imperative `heapsort_imp`. -/
theorem heapsort_equivalence (arr : List Nat) :
    heapsort arr = heapsort_imp arr := by
  unfold heapsort heapsort_imp
  dsimp only
  split_ifs with h
  · simp
  · simp [← build_max_heap_equivalence, extract_loop_eq_foldl]

/-- Imperative correctness theorem derived via functional-imperative equivalence. -/
theorem heapsort_imp_correct (arr : List Nat) (h : Pre arr) : Post arr (heapsort_imp arr) := by
  rw [← heapsort_equivalence]
  exact heapsort_spec arr h

end heapsort_algorithm
