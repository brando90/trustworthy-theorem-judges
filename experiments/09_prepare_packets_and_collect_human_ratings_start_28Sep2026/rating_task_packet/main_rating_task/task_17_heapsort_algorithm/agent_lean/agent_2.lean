import Mathlib

/-!
# Heapsort Algorithm (CLRS 6.4)

Formalization of 0-based max-heap construction (`build_max_heap`), heap maintenance
(`max_heapify`), and in-place extraction sorting (`heapsort`) following CLRS Section 6.4.

This file includes:
1. Functional implementation of `parent`, `left`, `right`, `swap`, `max_heapify`,
   `build_max_heap`, and `heapsort`.
2. Unit tests covering all test cases from the Python specification.
3. Precondition (`Pre`), heap invariants (`HeapNode`, `IsMaxHeapFrom`, `IsMaxHeap`),
   and proved property theorems (`parent_left_thm`, `parent_right_thm`,
   `build_max_heap_thm`, `sorted_thm`, `perm_thm`, `length_thm`, `mem_thm`,
   `count_thm`, `eq_mergeSort_thm`, `idempotent_thm`, `already_sorted_thm`).
4. Postcondition (`Post_prop`), randomized and bounded property-based tests (PBTs),
   and total correctness theorem (`heapsort_correct`).
5. Imperative implementation (`max_heapify_imp`, `build_max_heap_imp`, `heapsort_imp`)
   using `Id.run do` with mutable state, imperative unit tests, and proved functional-imperative
   equivalence theorems (`max_heapify_equiv`, `build_max_heap_equiv`, `heapsort_equiv`).
-/

namespace heapsort_algorithm

/-! ## 1. Functional Implementation -/

/-- Parent index in a 0-based binary heap. -/
def parent (i : Nat) : Nat :=
  if i = 0 then 0 else (i - 1) / 2

/-- Left child index in a 0-based binary heap. -/
def left (i : Nat) : Nat :=
  2 * i + 1

/-- Right child index in a 0-based binary heap. -/
def right (i : Nat) : Nat :=
  2 * i + 2

/-- Swap elements at indices `i` and `j` in a list of natural numbers. -/
def swap (arr : List Nat) (i j : Nat) : List Nat :=
  if i < arr.length ∧ j < arr.length then
    (arr.set i (arr.getD j 0)).set j (arr.getD i 0)
  else
    arr

/-- Select the index of the largest element among node `i` and its valid children `< heap_size`. -/
def choose_largest (arr : List Nat) (i heap_size : Nat) : Nat :=
  let l_idx := left i
  let r_idx := right i
  let largest := if l_idx < heap_size ∧ arr.getD l_idx 0 > arr.getD i 0 then l_idx else i
  if r_idx < heap_size ∧ arr.getD r_idx 0 > arr.getD largest 0 then r_idx else largest

/-- Inductive characterization of `choose_largest arr i heap_size`. -/
inductive LargestSpec (arr : List Nat) (i heap_size : Nat) : Nat → Prop
  | self (hl : left i < heap_size → arr.getD (left i) 0 ≤ arr.getD i 0)
         (hr : right i < heap_size → arr.getD (right i) 0 ≤ arr.getD i 0) :
      LargestSpec arr i heap_size i
  | left_child (hlt : left i < heap_size)
               (hi : arr.getD i 0 < arr.getD (left i) 0)
               (hr : right i < heap_size → arr.getD (right i) 0 ≤ arr.getD (left i) 0) :
      LargestSpec arr i heap_size (left i)
  | right_child (hrt : right i < heap_size)
                (hi : arr.getD i 0 < arr.getD (right i) 0)
                (hl : arr.getD (left i) 0 ≤ arr.getD (right i) 0) :
      LargestSpec arr i heap_size (right i)

theorem choose_largest_spec (arr : List Nat) (i heap_size : Nat) :
    LargestSpec arr i heap_size (choose_largest arr i heap_size) := by
  unfold choose_largest
  dsimp only
  split_ifs with h1 h2 h3
  · apply LargestSpec.right_child h2.1 <;> omega
  · apply LargestSpec.left_child h1.1 h1.2; intro hr; omega
  · apply LargestSpec.right_child h3.1 h3.2
    have : left i < heap_size := by unfold left right at *; omega
    omega
  · apply LargestSpec.self <;> (intro; omega)

/-- Maintain the max-heap property at index `i` for heap prefix of size `heap_size`. -/
def max_heapify (arr : List Nat) (i heap_size : Nat) : List Nat :=
  let largest := choose_largest arr i heap_size
  if largest = i then
    arr
  else
    max_heapify (swap arr i largest) largest heap_size
termination_by heap_size - i
decreasing_by
  rename_i hne
  have hspec := choose_largest_spec arr i heap_size
  generalize hc : choose_largest arr i heap_size = c at hspec
  rcases hspec with _ | ⟨hlt, _, _⟩ | ⟨hrt, _, _⟩
  · exact absurd hc hne
  · unfold left at *; omega
  · unfold right at *; omega

/-- Recursive loop for `build_max_heap`, heapifying from index `k - 1` down to `0`. -/
def build_max_heap_loop (arr : List Nat) : Nat → List Nat
  | 0 => arr
  | i + 1 => build_max_heap_loop (max_heapify arr i arr.length) i

/-- Rearrange a list into a 0-based max-heap following CLRS `BUILD-MAX-HEAP`. -/
def build_max_heap (arr : List Nat) : List Nat :=
  if arr.length ≤ 1 then
    arr
  else
    build_max_heap_loop arr (parent (arr.length - 1) + 1)

/-- Extraction loop for `heapsort`, repeatedly swapping the root maximum with index `i` and heapifying. -/
def heapsort_loop (arr : List Nat) : Nat → List Nat
  | 0 => arr
  | i + 1 =>
    let swapped := swap arr 0 (i + 1)
    let heapified := max_heapify swapped 0 (i + 1)
    heapsort_loop heapified i

/-- Sort a list of natural numbers in ascending order using CLRS 6.4 Heapsort. -/
def heapsort (arr : List Nat) : List Nat :=
  if arr.length ≤ 1 then
    arr
  else
    let result := build_max_heap arr
    heapsort_loop result (result.length - 1)

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

example : build_max_heap [5, 13, 2, 25, 7, 17, 20, 8, 4] = [25, 13, 20, 8, 7, 17, 2, 5, 4] := by
  native_decide

example : heapsort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsort [] = [] := by native_decide
example : heapsort [42] = [42] := by native_decide
example : heapsort [2, 1] = [1, 2] := by native_decide
example : heapsort [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsort [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : heapsort [2, 1] ≠ [2, 1] := by native_decide

#eval heapsort []
#eval heapsort [42]
#eval heapsort [3, 1, 2]
#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1]

/-! ## 3. Pre-condition -/

/-- Precondition for `heapsort`: input is a valid list of natural numbers. -/
def Pre (_arr : List Nat) : Prop := True

instance (arr : List Nat) : Decidable (Pre arr) := isTrue trivial

/-! ## 4. Helper Lemmas & Invariants -/

/-- Local max-heap order condition at index `k` within heap prefix of size `hs`. -/
def HeapNode (arr : List Nat) (hs k : Nat) : Prop :=
  (left k < hs → arr.getD (left k) 0 ≤ arr.getD k 0) ∧
  (right k < hs → arr.getD (right k) 0 ≤ arr.getD k 0)

instance (arr : List Nat) (hs k : Nat) : Decidable (HeapNode arr hs k) := by
  unfold HeapNode; infer_instance

/-- Max-heap invariant holds for all nodes `k` in `[idx, hs)`. -/
def IsMaxHeapFrom (arr : List Nat) (idx hs : Nat) : Prop :=
  ∀ k < hs, idx ≤ k → HeapNode arr hs k

instance (arr : List Nat) (idx hs : Nat) : Decidable (IsMaxHeapFrom arr idx hs) := by
  unfold IsMaxHeapFrom; infer_instance

/-- Full max-heap invariant on prefix `[0, hs)`. -/
def IsMaxHeap (arr : List Nat) (hs : Nat) : Prop :=
  IsMaxHeapFrom arr 0 hs

instance (arr : List Nat) (hs : Nat) : Decidable (IsMaxHeap arr hs) := by
  unfold IsMaxHeap; infer_instance

@[simp]
theorem swap_length (arr : List Nat) (i j : Nat) : (swap arr i j).length = arr.length := by
  unfold swap; split_ifs <;> simp

theorem cons_getElem_set {α : Type*} (l : List α) (i : Nat) (hi : i < l.length) (x : α) :
    (l[i] :: l.set i x).Perm (x :: l) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => exact List.Perm.swap x a as
    | succ k =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      simp only [List.getElem_cons_succ, List.set_cons_succ]
      exact (List.Perm.swap a as[k] (as.set k x)).trans
        ((List.Perm.cons a (ih k hi)).trans (List.Perm.swap x a as))

theorem swap_perm (arr : List Nat) (i j : Nat) : (swap arr i j).Perm arr := by
  unfold swap
  split_ifs with h
  · obtain ⟨hi, hj⟩ := h
    rw [List.getD_eq_getElem arr 0 hi, List.getD_eq_getElem arr 0 hj]
    by_cases hij : i = j
    · subst hij; simp
    · have hj' : j < (arr.set i arr[j]).length := by simp [hj]
      have h1 : ((arr.set i arr[j])[j] :: (arr.set i arr[j]).set j arr[i]).Perm
          (arr[i] :: arr.set i arr[j]) := cons_getElem_set (arr.set i arr[j]) j hj' arr[i]
      rw [List.getElem_set, if_neg hij] at h1
      have h2 : (arr[i] :: arr.set i arr[j]).Perm (arr[j] :: arr) :=
        cons_getElem_set arr i hi arr[j]
      exact List.Perm.cons_inv (h1.trans h2)
  · exact List.Perm.refl arr

theorem getD_set_eq (arr : List Nat) (i k v : Nat) (hi : i < arr.length) :
    (arr.set i v).getD k 0 = if k = i then v else arr.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_set]
  split_ifs with h1 h2 h2 <;> first | rfl | omega

theorem getD_swap (arr : List Nat) (i j k : Nat) (hi : i < arr.length) (hj : j < arr.length) :
    (swap arr i j).getD k 0 =
      if k = j then arr.getD i 0 else if k = i then arr.getD j 0 else arr.getD k 0 := by
  unfold swap
  rw [if_pos ⟨hi, hj⟩]
  have hj' : j < (arr.set i (arr.getD j 0)).length := by simp [hj]
  rw [getD_set_eq _ j k _ hj', getD_set_eq _ i k _ hi]

@[simp]
theorem max_heapify_length (arr : List Nat) (i hs : Nat) :
    (max_heapify arr i hs).length = arr.length := by
  induction arr, i using max_heapify.induct hs with
  | case1 arr i largest h_eq =>
    unfold max_heapify; rw [if_pos h_eq]
  | case2 arr i largest h_ne ih =>
    unfold max_heapify; rw [if_neg h_ne]; rw [ih, swap_length]

theorem max_heapify_perm (arr : List Nat) (i hs : Nat) :
    (max_heapify arr i hs).Perm arr := by
  induction arr, i using max_heapify.induct hs with
  | case1 arr i largest h_eq =>
    unfold max_heapify; rw [if_pos h_eq]
  | case2 arr i largest h_ne ih =>
    unfold max_heapify; rw [if_neg h_ne]
    exact ih.trans (swap_perm arr i largest)

theorem max_heapify_getD_ge (arr : List Nat) (i hs k : Nat)
    (hhs : hs ≤ arr.length) (hk : hs ≤ k) :
    (max_heapify arr i hs).getD k 0 = arr.getD k 0 := by
  induction arr, i using max_heapify.induct hs with
  | case1 arr i largest h_eq =>
    unfold max_heapify; rw [if_pos h_eq]
  | case2 arr i largest h_ne ih =>
    unfold max_heapify; rw [if_neg h_ne]
    change ¬(choose_largest arr i hs = i) at h_ne
    dsimp only [largest] at ih ⊢
    have hspec := choose_largest_spec arr i hs
    generalize hc : choose_largest arr i hs = c at hspec ih ⊢
    rcases hspec with _ | ⟨hlt, _, _⟩ | ⟨hrt, _, _⟩
    · exact absurd hc h_ne
    · rw [ih (by simp [hhs])]
      have hi : i < arr.length := by unfold left at hlt; omega
      have hl : left i < arr.length := by omega
      rw [getD_swap arr i (left i) k hi hl]
      have : k ≠ left i ∧ k ≠ i := by unfold left at *; omega
      rw [if_neg this.1, if_neg this.2]
    · rw [ih (by simp [hhs])]
      have hi : i < arr.length := by unfold right at hrt; omega
      have hr : right i < arr.length := by omega
      rw [getD_swap arr i (right i) k hi hr]
      have : k ≠ right i ∧ k ≠ i := by unfold right at *; omega
      rw [if_neg this.1, if_neg this.2]

theorem max_heapify_le_bound (arr : List Nat) (i hs bound : Nat)
    (hhs : hs ≤ arr.length)
    (hbound : ∀ k < hs, arr.getD k 0 ≤ bound) :
    ∀ k < hs, (max_heapify arr i hs).getD k 0 ≤ bound := by
  induction arr, i using max_heapify.induct hs with
  | case1 arr i largest h_eq =>
    unfold max_heapify; rw [if_pos h_eq]; exact hbound
  | case2 arr i largest h_ne ih =>
    unfold max_heapify; rw [if_neg h_ne]
    change ¬(choose_largest arr i hs = i) at h_ne
    dsimp only [largest] at ih ⊢
    have hspec := choose_largest_spec arr i hs
    generalize hc : choose_largest arr i hs = c at hspec ih ⊢
    rcases hspec with _ | ⟨hlt, _, _⟩ | ⟨hrt, _, _⟩
    · exact absurd hc h_ne
    · apply ih (by simp [hhs])
      intro k hk
      have hi : i < hs := by unfold left at hlt; omega
      rw [getD_swap arr i (left i) k (by omega) (by omega)]
      split_ifs with h1 h2
      · exact hbound i hi
      · exact hbound (left i) hlt
      · exact hbound k hk
    · apply ih (by simp [hhs])
      intro k hk
      have hi : i < hs := by unfold right at hrt; omega
      rw [getD_swap arr i (right i) k (by omega) (by omega)]
      split_ifs with h1 h2
      · exact hbound i hi
      · exact hbound (right i) hrt
      · exact hbound k hk

theorem swap_child_step (arr : List Nat) (idx i c hs : Nat)
    (hhs : hs ≤ arr.length)
    (hidx : idx ≤ i)
    (hchild : c = left i ∨ c = right i)
    (hclt : c < hs)
    (hic : arr.getD i 0 ≤ arr.getD c 0)
    (hlc : left i < hs → arr.getD (left i) 0 ≤ arr.getD c 0)
    (hrc : right i < hs → arr.getD (right i) 0 ≤ arr.getD c 0)
    (hnodes : ∀ k < hs, idx ≤ k → k ≠ i → HeapNode arr hs k)
    (hparent : ∀ p < hs, idx ≤ p → (left p = i ∨ right p = i) →
      (left i < hs → arr.getD (left i) 0 ≤ arr.getD p 0) ∧
      (right i < hs → arr.getD (right i) 0 ≤ arr.getD p 0)) :
    (∀ k < hs, idx ≤ k → k ≠ c → HeapNode (swap arr i c) hs k) ∧
    (∀ p < hs, idx ≤ p → (left p = c ∨ right p = c) →
      (left c < hs → (swap arr i c).getD (left c) 0 ≤ (swap arr i c).getD p 0) ∧
      (right c < hs → (swap arr i c).getD (right c) 0 ≤ (swap arr i c).getD p 0)) := by
  have hi_lt_c : i < c := by unfold left right at hchild; omega
  have hi_len : i < arr.length := by omega
  have hc_len : c < arr.length := by omega
  constructor
  · intro k hk2 hk1 hkc
    by_cases hki : k = i
    · subst hki
      constructor
      · intro hl
        rw [getD_swap arr k c (left k) hi_len hc_len, getD_swap arr k c k hi_len hc_len]
        have : left k ≠ k := by unfold left; omega
        have h1 := hlc hl
        split_ifs <;> omega
      · intro hr
        rw [getD_swap arr k c (right k) hi_len hc_len, getD_swap arr k c k hi_len hc_len]
        have : right k ≠ k := by unfold right; omega
        have h1 := hrc hr
        split_ifs <;> omega
    · have hnode_k := hnodes k hk2 hk1 hki
      have hlk_ne_c : left k ≠ c := by unfold left right at *; omega
      have hrk_ne_c : right k ≠ c := by unfold left right at *; omega
      constructor
      · intro hl
        rw [getD_swap arr i c (left k) hi_len hc_len, getD_swap arr i c k hi_len hc_len]
        rw [if_neg hlk_ne_c, if_neg hkc, if_neg hki]
        split_ifs with hlk_i
        · have hp := hparent k hk2 hk1 (Or.inl hlk_i)
          rcases hchild with rfl | rfl
          · exact hp.1 hclt
          · exact hp.2 hclt
        · exact hnode_k.1 hl
      · intro hr
        rw [getD_swap arr i c (right k) hi_len hc_len, getD_swap arr i c k hi_len hc_len]
        rw [if_neg hrk_ne_c, if_neg hkc, if_neg hki]
        split_ifs with hrk_i
        · have hp := hparent k hk2 hk1 (Or.inr hrk_i)
          rcases hchild with rfl | rfl
          · exact hp.1 hclt
          · exact hp.2 hclt
        · exact hnode_k.2 hr
  · intro p hp2 hp1 hpc
    have hpi : p = i := by unfold left right at hchild hpc; omega
    subst hpi
    have hnode_c := hnodes c hclt (by omega) (by omega)
    rw [getD_swap arr p c (left c) hi_len hc_len,
        getD_swap arr p c (right c) hi_len hc_len,
        getD_swap arr p c p hi_len hc_len]
    have h1 : left c ≠ c := by unfold left; omega
    have h2 : left c ≠ p := by unfold left; omega
    have h3 : right c ≠ c := by unfold right; omega
    have h4 : right c ≠ p := by unfold right; omega
    have h5 : p ≠ c := by omega
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos rfl]
    exact hnode_c

theorem max_heapify_heap_aux (arr : List Nat) (idx i hs : Nat)
    (hhs : hs ≤ arr.length)
    (hidx : idx ≤ i)
    (hnodes : ∀ k < hs, idx ≤ k → k ≠ i → HeapNode arr hs k)
    (hparent : ∀ p < hs, idx ≤ p → (left p = i ∨ right p = i) →
      (left i < hs → arr.getD (left i) 0 ≤ arr.getD p 0) ∧
      (right i < hs → arr.getD (right i) 0 ≤ arr.getD p 0)) :
    IsMaxHeapFrom (max_heapify arr i hs) idx hs := by
  induction arr, i using max_heapify.induct hs with
  | case1 arr i largest h_eq =>
    unfold max_heapify
    rw [if_pos h_eq]
    intro k hk2 hk1
    by_cases hki : k = i
    · subst hki
      have hspec := choose_largest_spec arr k hs
      generalize hc : choose_largest arr k hs = c at hspec
      rcases hspec with ⟨hl, hr⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩
      · exact ⟨hl, hr⟩
      · change choose_largest arr k hs = k at h_eq; unfold left at hc; omega
      · change choose_largest arr k hs = k at h_eq; unfold right at hc; omega
    · exact hnodes k hk2 hk1 hki
  | case2 arr i largest h_ne ih =>
    unfold max_heapify
    rw [if_neg h_ne]
    change ¬(choose_largest arr i hs = i) at h_ne
    dsimp only [largest] at ih ⊢
    have hspec := choose_largest_spec arr i hs
    generalize hc : choose_largest arr i hs = c at hspec ih ⊢
    rcases hspec with _ | ⟨hlt, hi, hr⟩ | ⟨hrt, hi, hl⟩
    · exact absurd hc h_ne
    · have hstep := swap_child_step arr idx i (left i) hs hhs hidx (Or.inl rfl) hlt
        (by omega) (fun _ => le_rfl) hr hnodes hparent
      exact ih (by simp [hhs]) (by unfold left; omega) hstep.1 hstep.2
    · have hstep := swap_child_step arr idx i (right i) hs hhs hidx (Or.inr rfl) hrt
        (by omega) (fun _ => hl) (fun _ => le_rfl) hnodes hparent
      exact ih (by simp [hhs]) (by unfold right; omega) hstep.1 hstep.2

theorem max_heapify_preserves_heap (arr : List Nat) (i hs : Nat)
    (hhs : hs ≤ arr.length)
    (hheap : IsMaxHeapFrom arr (i + 1) hs) :
    IsMaxHeapFrom (max_heapify arr i hs) i hs := by
  apply max_heapify_heap_aux arr i i hs hhs le_rfl
  · intro k hk2 hk1 hne
    exact hheap k hk2 (by omega)
  · intro p _ hp1 hchild
    unfold left right at hchild
    omega

theorem max_of_isMaxHeap (arr : List Nat) (hs : Nat)
    (hheap : IsMaxHeapFrom arr 0 hs) :
    ∀ k < hs, arr.getD k 0 ≤ arr.getD 0 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0; exact le_rfl
    · have hp_lt : (k - 1) / 2 < k := by omega
      have hp_hs : (k - 1) / 2 < hs := by omega
      have hnode := hheap ((k - 1) / 2) hp_hs (Nat.zero_le _)
      have hparent_le := ih ((k - 1) / 2) hp_lt hp_hs
      have hchild : left ((k - 1) / 2) = k ∨ right ((k - 1) / 2) = k := by
        unfold left right; omega
      rcases hchild with hl | hr
      · have h1 := hnode.1 (by rw [hl]; exact hk)
        rw [hl] at h1
        omega
      · have h1 := hnode.2 (by rw [hr]; exact hk)
        rw [hr] at h1
        omega

@[simp]
theorem build_max_heap_loop_length (arr : List Nat) (k : Nat) :
    (build_max_heap_loop arr k).length = arr.length := by
  induction k generalizing arr with
  | zero => rfl
  | succ i ih => simp [build_max_heap_loop, ih]

@[simp]
theorem build_max_heap_length (arr : List Nat) :
    (build_max_heap arr).length = arr.length := by
  unfold build_max_heap
  split_ifs <;> simp

theorem build_max_heap_loop_perm (arr : List Nat) (k : Nat) :
    (build_max_heap_loop arr k).Perm arr := by
  induction k generalizing arr with
  | zero => exact List.Perm.refl arr
  | succ i ih =>
    unfold build_max_heap_loop
    exact (ih (max_heapify arr i arr.length)).trans (max_heapify_perm arr i arr.length)

theorem build_max_heap_perm (arr : List Nat) :
    (build_max_heap arr).Perm arr := by
  unfold build_max_heap
  split_ifs
  · exact List.Perm.refl arr
  · exact build_max_heap_loop_perm arr (parent (arr.length - 1) + 1)

theorem build_max_heap_loop_isMaxHeap (arr : List Nat) (k : Nat)
    (hheap : IsMaxHeapFrom arr k arr.length) :
    IsMaxHeapFrom (build_max_heap_loop arr k) 0 arr.length := by
  induction k generalizing arr with
  | zero => exact hheap
  | succ i ih =>
    unfold build_max_heap_loop
    set arr' := max_heapify arr i arr.length
    have hstep : IsMaxHeapFrom arr' i arr.length :=
      max_heapify_preserves_heap arr i arr.length le_rfl hheap
    have hlen : arr'.length = arr.length := max_heapify_length arr i arr.length
    rw [← hlen] at hstep ⊢
    exact ih arr' hstep

theorem build_max_heap_isMaxHeap (arr : List Nat) :
    IsMaxHeap (build_max_heap arr) (build_max_heap arr).length := by
  rw [build_max_heap_length]
  unfold IsMaxHeap build_max_heap
  split_ifs with h
  · intro k hk _
    unfold HeapNode left right
    constructor <;> (intro; omega)
  · apply build_max_heap_loop_isMaxHeap
    intro k hk2 hk1
    unfold parent at hk1
    unfold HeapNode left right
    split_ifs at hk1 <;> (constructor <;> (intro; omega))

@[simp]
theorem heapsort_loop_length (arr : List Nat) (k : Nat) :
    (heapsort_loop arr k).length = arr.length := by
  induction k generalizing arr with
  | zero => rfl
  | succ i ih => simp [heapsort_loop, ih]

theorem heapsort_loop_perm (arr : List Nat) (k : Nat) :
    (heapsort_loop arr k).Perm arr := by
  induction k generalizing arr with
  | zero => exact List.Perm.refl arr
  | succ i ih =>
    unfold heapsort_loop
    exact (ih _).trans ((max_heapify_perm _ 0 (i + 1)).trans (swap_perm arr 0 (i + 1)))

theorem heapsort_loop_sorted_aux (arr : List Nat) (m : Nat)
    (hm : m < arr.length)
    (hheap : IsMaxHeapFrom arr 0 (m + 1))
    (hsplit : ∀ a b, a ≤ m → m < b → b < arr.length → arr.getD a 0 ≤ arr.getD b 0)
    (hsuffix : ∀ a b, m < a → a ≤ b → b < arr.length → arr.getD a 0 ≤ arr.getD b 0) :
    ∀ a b, a ≤ b → b < arr.length →
      (heapsort_loop arr m).getD a 0 ≤ (heapsort_loop arr m).getD b 0 := by
  induction m generalizing arr with
  | zero =>
    unfold heapsort_loop
    intro a b hab hb
    by_cases ha0 : a = 0
    · subst ha0
      by_cases hb0 : b = 0
      · subst hb0; exact le_rfl
      · exact hsplit 0 b le_rfl (by omega) hb
    · exact hsuffix a b (by omega) hab hb
  | succ i ih =>
    unfold heapsort_loop
    set swapped := swap arr 0 (i + 1)
    set heapified := max_heapify swapped 0 (i + 1)
    have h0_len : 0 < arr.length := by omega
    have hi1_len : i + 1 < arr.length := hm
    have hswapped_len : swapped.length = arr.length := swap_length arr 0 (i + 1)
    have hmax : ∀ k < i + 2, arr.getD k 0 ≤ arr.getD 0 0 :=
      max_of_isMaxHeap arr (i + 2) hheap
    have hswapped_heap : IsMaxHeapFrom swapped 1 (i + 1) := by
      intro k hk2 hk1
      have hnode := hheap k (by omega) (by omega)
      have hk_get : swapped.getD k 0 = arr.getD k 0 := by
        rw [getD_swap arr 0 (i + 1) k h0_len hi1_len]
        have : k ≠ i + 1 ∧ k ≠ 0 := by omega
        rw [if_neg this.1, if_neg this.2]
      constructor
      · intro hl
        have hl_get : swapped.getD (left k) 0 = arr.getD (left k) 0 := by
          rw [getD_swap arr 0 (i + 1) (left k) h0_len hi1_len]
          have : left k ≠ i + 1 ∧ left k ≠ 0 := by unfold left at *; omega
          rw [if_neg this.1, if_neg this.2]
        rw [hl_get, hk_get]
        exact hnode.1 (by omega)
      · intro hr
        have hr_get : swapped.getD (right k) 0 = arr.getD (right k) 0 := by
          rw [getD_swap arr 0 (i + 1) (right k) h0_len hi1_len]
          have : right k ≠ i + 1 ∧ right k ≠ 0 := by unfold right at *; omega
          rw [if_neg this.1, if_neg this.2]
        rw [hr_get, hk_get]
        exact hnode.2 (by omega)
    have hheap' : IsMaxHeapFrom heapified 0 (i + 1) :=
      max_heapify_preserves_heap swapped 0 (i + 1) (by omega) hswapped_heap
    have hge_eq : ∀ b, i + 1 ≤ b → heapified.getD b 0 = swapped.getD b 0 := by
      intro b hb
      exact max_heapify_getD_ge swapped 0 (i + 1) b (by omega) hb
    have hswapped_ge_gt : ∀ b, i + 1 < b → b < arr.length → swapped.getD b 0 = arr.getD b 0 := by
      intro b hb1 _
      rw [getD_swap arr 0 (i + 1) b h0_len hi1_len]
      have : b ≠ i + 1 ∧ b ≠ 0 := by omega
      rw [if_neg this.1, if_neg this.2]
    have hswapped_at_i1 : swapped.getD (i + 1) 0 = arr.getD 0 0 := by
      rw [getD_swap arr 0 (i + 1) (i + 1) h0_len hi1_len, if_pos rfl]
    have hswapped_le_max : ∀ k < i + 1, swapped.getD k 0 ≤ arr.getD 0 0 := by
      intro k hk
      rw [getD_swap arr 0 (i + 1) k h0_len hi1_len]
      have : k ≠ i + 1 := by omega
      rw [if_neg this]
      split_ifs with hk0
      · exact hmax (i + 1) (by omega)
      · exact hmax k (by omega)
    have hheapified_le_max : ∀ k < i + 1, heapified.getD k 0 ≤ arr.getD 0 0 :=
      max_heapify_le_bound swapped 0 (i + 1) (arr.getD 0 0) (by omega) hswapped_le_max
    have hlen_heapified : heapified.length = arr.length :=
      (max_heapify_length swapped 0 (i + 1)).trans hswapped_len
    intro a b hab hb
    apply ih heapified (by omega) hheap'
    · intro x y hx hy1 hy2
      rw [hlen_heapified] at hy2
      have hx_le : heapified.getD x 0 ≤ arr.getD 0 0 := hheapified_le_max x (by omega)
      rw [hge_eq y (by omega)]
      by_cases hy_eq : y = i + 1
      · subst hy_eq
        rw [hswapped_at_i1]
        exact hx_le
      · rw [hswapped_ge_gt y (by omega) hy2]
        have h0_le_y : arr.getD 0 0 ≤ arr.getD y 0 := hsplit 0 y (by omega) (by omega) hy2
        omega
    · intro x y hx1 hxy hy2
      rw [hlen_heapified] at hy2
      rw [hge_eq x (by omega), hge_eq y (by omega)]
      by_cases hx_eq : x = i + 1
      · subst hx_eq
        rw [hswapped_at_i1]
        by_cases hy_eq : y = i + 1
        · subst hy_eq; rw [hswapped_at_i1]
        · rw [hswapped_ge_gt y (by omega) hy2]
          exact hsplit 0 y (by omega) (by omega) hy2
      · rw [hswapped_ge_gt x (by omega) (by omega), hswapped_ge_gt y (by omega) hy2]
        exact hsuffix x y (by omega) hxy hy2
    · exact hab
    · rw [hlen_heapified]; exact hb

theorem sorted_mergeSort_nat (arr : List Nat) : List.Sorted (· ≤ ·) (arr.mergeSort) := by
  have h := List.sorted_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    arr
  simpa [List.Sorted] using h

/-! ## 5. Property Propositions and Theorems -/

/-- Property: the parent of `left i` is `i`. -/
def parent_left_prop (i : Nat) : Prop :=
  parent (left i) = i

theorem parent_left_thm (i : Nat) : parent_left_prop i := by
  unfold parent_left_prop parent left
  split <;> omega

/-- Property: the parent of `right i` is `i`. -/
def parent_right_prop (i : Nat) : Prop :=
  parent (right i) = i

theorem parent_right_thm (i : Nat) : parent_right_prop i := by
  unfold parent_right_prop parent right
  split <;> omega

/-- Property: `build_max_heap` produces a valid max-heap that is a length-preserving permutation of the input. -/
def build_max_heap_prop (arr : List Nat) : Prop :=
  IsMaxHeap (build_max_heap arr) (build_max_heap arr).length ∧
  (build_max_heap arr).Perm arr ∧
  (build_max_heap arr).length = arr.length

instance (arr : List Nat) : Decidable (build_max_heap_prop arr) := by
  unfold build_max_heap_prop; infer_instance

theorem build_max_heap_thm (arr : List Nat) : build_max_heap_prop arr :=
  ⟨build_max_heap_isMaxHeap arr, build_max_heap_perm arr, build_max_heap_length arr⟩

/-- Property: `heapsort` preserves the length of the input list. -/
def length_prop (arr : List Nat) : Prop :=
  (heapsort arr).length = arr.length

instance (arr : List Nat) : Decidable (length_prop arr) := by
  unfold length_prop; infer_instance

@[simp]
theorem length_thm (arr : List Nat) : length_prop arr := by
  unfold length_prop heapsort
  split_ifs <;> simp

/-- Property: `heapsort` produces a permutation of the input list. -/
def perm_prop (arr : List Nat) : Prop :=
  (heapsort arr).Perm arr

instance (arr : List Nat) : Decidable (perm_prop arr) := by
  unfold perm_prop; infer_instance

theorem perm_thm (arr : List Nat) : perm_prop arr := by
  unfold perm_prop heapsort
  split_ifs
  · exact List.Perm.refl arr
  · exact (heapsort_loop_perm (build_max_heap arr) _).trans (build_max_heap_perm arr)

/-- Property: `heapsort` produces a sorted list in non-decreasing order. -/
def sorted_prop (arr : List Nat) : Prop :=
  List.Pairwise (· ≤ ·) (heapsort arr)

instance (arr : List Nat) : Decidable (sorted_prop arr) := by
  unfold sorted_prop; infer_instance

theorem sorted_thm (arr : List Nat) : sorted_prop arr := by
  unfold sorted_prop
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [← List.getD_eq_getElem _ 0 hi, ← List.getD_eq_getElem _ 0 hj]
  have hlen_eq : (heapsort arr).length = arr.length := length_thm arr
  rw [hlen_eq] at hi hj
  unfold heapsort
  split_ifs with hlen
  · omega
  · dsimp only
    set res := build_max_heap arr
    have hres_len : res.length = arr.length := build_max_heap_length arr
    have hres_heap : IsMaxHeapFrom res 0 (res.length - 1 + 1) := by
      have h1 := build_max_heap_isMaxHeap arr
      unfold IsMaxHeap at h1
      have : res.length - 1 + 1 = res.length := by omega
      rw [this]
      exact h1
    apply heapsort_loop_sorted_aux res (res.length - 1) (by omega) hres_heap
    · intro a b _ hb1 hb2; omega
    · intro a b ha1 _ hb2; omega
    · omega
    · omega

/-- Property: `heapsort` preserves element membership. -/
def mem_prop (arr : List Nat) : Prop :=
  ∀ x, x ∈ heapsort arr ↔ x ∈ arr

theorem mem_thm (arr : List Nat) : mem_prop arr :=
  fun _ => (perm_thm arr).mem_iff

/-- Property: `heapsort` preserves element multiplicity (`count`). -/
def count_prop (arr : List Nat) : Prop :=
  ∀ x, (heapsort arr).count x = arr.count x

theorem count_thm (arr : List Nat) : count_prop arr :=
  fun x => (perm_thm arr).count_eq x

/-- Property: `heapsort` agrees with `List.mergeSort`. -/
def eq_mergeSort_prop (arr : List Nat) : Prop :=
  heapsort arr = arr.mergeSort

instance (arr : List Nat) : Decidable (eq_mergeSort_prop arr) := by
  unfold eq_mergeSort_prop; infer_instance

theorem eq_mergeSort_thm (arr : List Nat) : eq_mergeSort_prop arr := by
  unfold eq_mergeSort_prop
  exact List.eq_of_perm_of_sorted
    ((perm_thm arr).trans (List.mergeSort_perm arr _).symm)
    (sorted_thm arr)
    (sorted_mergeSort_nat arr)

/-- Property: `heapsort` leaves an already sorted list unchanged. -/
def already_sorted_prop (arr : List Nat) : Prop :=
  List.Pairwise (· ≤ ·) arr → heapsort arr = arr

instance (arr : List Nat) : Decidable (already_sorted_prop arr) := by
  unfold already_sorted_prop; infer_instance

theorem already_sorted_thm (arr : List Nat) : already_sorted_prop arr := by
  intro hsorted
  exact List.eq_of_perm_of_sorted (perm_thm arr) (sorted_thm arr) hsorted

/-- Property: `heapsort` is idempotent. -/
def idempotent_prop (arr : List Nat) : Prop :=
  heapsort (heapsort arr) = heapsort arr

instance (arr : List Nat) : Decidable (idempotent_prop arr) := by
  unfold idempotent_prop; infer_instance

theorem idempotent_thm (arr : List Nat) : idempotent_prop arr :=
  already_sorted_thm (heapsort arr) (sorted_thm arr)

/-! ## 6. Post-condition -/

/-- Postcondition for `heapsort`: conjunction of all core sorting properties. -/
def Post_prop (arr : List Nat) : Prop :=
  sorted_prop arr ∧
  perm_prop arr ∧
  length_prop arr ∧
  mem_prop arr ∧
  count_prop arr ∧
  eq_mergeSort_prop arr ∧
  already_sorted_prop arr ∧
  idempotent_prop arr

/-! ## 7. Property-Based Tests (PBTs) -/

-- Randomized PBTs using Plausible
#eval Plausible.Testable.check (∀ i : Nat, parent (left i) = i)
#eval Plausible.Testable.check (∀ i : Nat, parent (right i) = i)
#eval Plausible.Testable.check (∀ arr : List Nat, build_max_heap_prop arr)
#eval Plausible.Testable.check (∀ arr : List Nat, length_prop arr)
#eval Plausible.Testable.check (∀ arr : List Nat, perm_prop arr)
#eval Plausible.Testable.check (∀ arr : List Nat, sorted_prop arr)
#eval Plausible.Testable.check (∀ (arr : List Nat) (x : Nat), (x ∈ heapsort arr) ↔ (x ∈ arr))
#eval Plausible.Testable.check (∀ (arr : List Nat) (x : Nat), (heapsort arr).count x = arr.count x)
#eval Plausible.Testable.check (∀ arr : List Nat, eq_mergeSort_prop arr)
#eval Plausible.Testable.check (∀ arr : List Nat, heapsort (arr.mergeSort) = arr.mergeSort)
#eval Plausible.Testable.check (∀ arr : List Nat, idempotent_prop arr)
#eval Plausible.Testable.check (∀ arr : List Nat,
  decide (sorted_prop arr) &&
  decide (perm_prop arr) &&
  decide (length_prop arr) &&
  decide (eq_mergeSort_prop arr) &&
  decide (idempotent_prop arr))

-- Bounded PBTs using native_decide
example : (List.range 50).all (fun i => parent (left i) == i && parent (right i) == i) = true := by
  native_decide

example : (List.range 25).all (fun n =>
    let arr := (List.range n).reverse
    decide (build_max_heap_prop arr) &&
    decide (sorted_prop arr) &&
    decide (perm_prop arr) &&
    decide (length_prop arr) &&
    decide (eq_mergeSort_prop arr) &&
    decide (already_sorted_prop (List.range n)) &&
    decide (idempotent_prop arr)) = true := by
  native_decide

/-! ## 8. Correctness Theorem: Pre -> Post -/

/-- Total correctness theorem for `heapsort`. -/
theorem heapsort_correct (arr : List Nat) (_hpre : Pre arr) : Post_prop arr :=
  ⟨sorted_thm arr,
   perm_thm arr,
   length_thm arr,
   mem_thm arr,
   count_thm arr,
   eq_mergeSort_thm arr,
   already_sorted_thm arr,
   idempotent_thm arr⟩

/-! ## 9. Imperative Implementation -/

/-- Imperative `max_heapify` using `Id.run do` with mutable loop state. -/
def max_heapify_imp (arr : List Nat) (i heap_size : Nat) : List Nat := Id.run do
  let mut result := arr
  let mut curr := i
  for _ in List.replicate (heap_size - i) () do
    let l_idx := left curr
    let r_idx := right curr
    let mut largest := curr
    if l_idx < heap_size ∧ result.getD l_idx 0 > result.getD curr 0 then
      largest := l_idx
    if r_idx < heap_size ∧ result.getD r_idx 0 > result.getD largest 0 then
      largest := r_idx
    if largest = curr then
      break
    result := swap result curr largest
    curr := largest
  return result

/-- Imperative `build_max_heap` using `Id.run do` with mutable state. -/
def build_max_heap_imp (arr : List Nat) : List Nat := Id.run do
  if arr.length ≤ 1 then
    return arr
  let mut result := arr
  let n := result.length
  for i in (List.range (parent (n - 1) + 1)).reverse do
    result := max_heapify_imp result i n
  return result

/-- Imperative `heapsort` using `Id.run do` with mutable state. -/
def heapsort_imp (arr : List Nat) : List Nat := Id.run do
  if arr.length ≤ 1 then
    return arr
  let mut result := build_max_heap_imp arr
  for idx in (List.range (result.length - 1)).reverse do
    let i := idx + 1
    result := swap result 0 i
    result := max_heapify_imp result 0 i
  return result

/-! ## 10. Imperative Tests -/

example : build_max_heap_imp [5, 13, 2, 25, 7, 17, 20, 8, 4] = [25, 13, 20, 8, 7, 17, 2, 5, 4] := by
  native_decide

example : heapsort_imp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsort_imp [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsort_imp [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsort_imp [] = [] := by native_decide
example : heapsort_imp [42] = [42] := by native_decide
example : heapsort_imp [2, 1] = [1, 2] := by native_decide
example : heapsort_imp [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsort_imp [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapsort_imp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapsort_imp [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsort_imp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsort_imp [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : heapsort_imp [2, 1] ≠ [2, 1] := by native_decide

#eval heapsort_imp []
#eval heapsort_imp [42]
#eval heapsort_imp [3, 1, 2]
#eval heapsort_imp [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsort_imp [9, 8, 7, 6, 5, 4, 3, 2, 1]

#eval Plausible.Testable.check (∀ arr : List Nat, heapsort arr = heapsort_imp arr)

/-! ## 11. Equivalence Theorems: Functional = Imperative -/

theorem max_heapify_forIn_eq (fuel : Nat) (arr : List Nat) (curr hs : Nat)
    (hfuel : hs - curr ≤ fuel)
    (F : Unit → MProd Nat (List Nat) → Id (ForInStep (MProd Nat (List Nat))))
    (hF : ∀ x r, F x r =
      let largest := choose_largest r.snd r.fst hs
      if largest = r.fst then pure (ForInStep.done ⟨r.fst, r.snd⟩)
      else pure (ForInStep.yield ⟨largest, swap r.snd r.fst largest⟩)) :
    (forIn (m := Id) (List.replicate fuel ()) ⟨curr, arr⟩ F).run.snd = max_heapify arr curr hs := by
  induction fuel generalizing arr curr with
  | zero =>
    have hge : hs ≤ curr := by omega
    have h_eq : choose_largest arr curr hs = curr := by
      have hspec := choose_largest_spec arr curr hs
      generalize hc : choose_largest arr curr hs = c at hspec
      rcases hspec with _ | ⟨hlt, _, _⟩ | ⟨hrt, _, _⟩
      · rfl
      · unfold left at hlt; omega
      · unfold right at hrt; omega
    unfold max_heapify
    rw [if_pos h_eq]
    rfl
  | succ k ih =>
    rw [List.replicate_succ, List.forIn_cons, hF]
    dsimp only
    by_cases h_eq : choose_largest arr curr hs = curr
    · rw [if_pos h_eq]
      unfold max_heapify
      rw [if_pos h_eq]
      rfl
    · rw [if_neg h_eq]
      unfold max_heapify
      rw [if_neg h_eq]
      have hlt : hs - choose_largest arr curr hs ≤ k := by
        have hspec := choose_largest_spec arr curr hs
        generalize hc : choose_largest arr curr hs = c at hspec
        rcases hspec with _ | ⟨hlt, _, _⟩ | ⟨hrt, _, _⟩
        · exact absurd hc h_eq
        · unfold left at *; omega
        · unfold right at *; omega
      exact ih (swap arr curr (choose_largest arr curr hs)) (choose_largest arr curr hs) hlt

/-- Equivalence between functional `max_heapify` and imperative `max_heapify_imp`. -/
theorem max_heapify_equiv (arr : List Nat) (i hs : Nat) :
    max_heapify arr i hs = max_heapify_imp arr i hs := by
  symm
  unfold max_heapify_imp
  exact max_heapify_forIn_eq (hs - i) arr i hs le_rfl _ (fun x r => by
    unfold choose_largest
    dsimp only
    split_ifs <;> rfl)

theorem build_max_heap_forIn_eq (k n : Nat) (arr : List Nat) (hlen : arr.length = n)
    (F : Nat → List Nat → Id (ForInStep (List Nat)))
    (hF : ∀ i r, F i r = pure (ForInStep.yield (max_heapify_imp r i n))) :
    (forIn (m := Id) (List.range k).reverse arr F).run = build_max_heap_loop arr k := by
  induction k generalizing arr with
  | zero => rfl
  | succ i ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.forIn_cons, hF, ← max_heapify_equiv, ← hlen]
    unfold build_max_heap_loop
    apply ih (max_heapify arr i arr.length)
    rw [max_heapify_length, hlen]

/-- Equivalence between functional `build_max_heap` and imperative `build_max_heap_imp`. -/
theorem build_max_heap_equiv (arr : List Nat) :
    build_max_heap arr = build_max_heap_imp arr := by
  symm
  unfold build_max_heap_imp build_max_heap
  split_ifs with h
  · rfl
  · exact build_max_heap_forIn_eq (parent (arr.length - 1) + 1) arr.length arr rfl _ (fun _ _ => rfl)

theorem heapsort_forIn_eq (k : Nat) (arr : List Nat)
    (F : Nat → List Nat → Id (ForInStep (List Nat)))
    (hF : ∀ idx r, F idx r = pure (ForInStep.yield (max_heapify_imp (swap r 0 (idx + 1)) 0 (idx + 1)))) :
    (forIn (m := Id) (List.range k).reverse arr F).run = heapsort_loop arr k := by
  induction k generalizing arr with
  | zero => rfl
  | succ i ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.forIn_cons, hF, ← max_heapify_equiv]
    unfold heapsort_loop
    exact ih (max_heapify (swap arr 0 (i + 1)) 0 (i + 1))

/-- Equivalence between functional `heapsort` and imperative `heapsort_imp`. -/
theorem heapsort_equiv (arr : List Nat) :
    heapsort arr = heapsort_imp arr := by
  symm
  unfold heapsort_imp heapsort
  split_ifs with h
  · rfl
  · dsimp only
    rw [← build_max_heap_equiv]
    exact heapsort_forIn_eq ((build_max_heap arr).length - 1) (build_max_heap arr) _ (fun _ _ => rfl)

end heapsort_algorithm
