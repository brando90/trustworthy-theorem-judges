import Mathlib

/-!
# HEAPSORT (CLRS 6.4) on 0-based max-heap arrays

A Lean 4 formalization of the Python program `heapsort_algorithm.py`, which implements
HEAPSORT from CLRS 6.4 using 0-based max-heap arrays.

The file contains

* the index helpers `parent`, `left`, `right` of CLRS 6.1 (0-based version),
* `maxHeapify` (CLRS `MAX-HEAPIF`), `buildMaxHeap` (CLRS `BUILD-MAX-HEAP`) and
  `heapsort` (CLRS `HEAPSORT`) as total functions on `Array Nat` / `List Nat`,
* proofs that `heapsort` returns a sorted permutation of its input of the same length
  (the post-condition `Post_prop`),
* an imperative implementation written with `Id.run do` and mutable arrays, together with
  a proof that it agrees with the functional one.

Arrays are read with the total accessor `Array.getD a i 0`, so that all definitions are
computable without bounds proofs; every lemma that needs an actual entry carries the
hypothesis `hs ≤ a.size`, which guarantees `getD` coincides with `a[·]` on `[0, hs)`.
-/

namespace heapsort_algorithm

open List Array

/-! ## Implementation (functional definition, mirroring the Python program) -/

/-- `parent i` is the index of the parent of node `i` in a 0-based heap
(Python `parent`: `0` if `i == 0` else `(i - 1) // 2`). -/
def parent (i : Nat) : Nat := if i = 0 then 0 else (i - 1) / 2

/-- `left i = 2 * i + 1`, the left child of node `i` in a 0-based heap. -/
def left (i : Nat) : Nat := 2 * i + 1

/-- `right i = 2 * i + 2`, the right child of node `i` in a 0-based heap. -/
def right (i : Nat) : Nat := 2 * i + 2


/-- `HeapAt a hs j` says node `j` is at least as large as its in-range children
(the max-heap condition of CLRS 6.1 at a single node). -/
def HeapAt (a : Array Nat) (hs j : Nat) : Prop :=
  (left j < hs → a.getD (left j) 0 ≤ a.getD j 0) ∧
  (right j < hs → a.getD (right j) 0 ≤ a.getD j 0)

/-- All nodes with index in `[i, hs)` satisfy the heap condition. -/
def IsHeapBelow (a : Array Nat) (hs i : Nat) : Prop := ∀ j, i ≤ j → j < hs → HeapAt a hs j

/-- The whole prefix `[0, hs)` of `a` is a max-heap. -/
def IsHeap (a : Array Nat) (hs : Nat) : Prop := IsHeapBelow a hs 0

/-- Index of the largest of node `i` and those of its children that lie inside the heap
`[0, hs)`; this is the variable `largest` of CLRS' `MAX-HEAPIF` (Python `max_heapify`). -/
def largestIdx (a : Array Nat) (i hs : Nat) : Nat :=
  if left i < hs ∧ a.getD (left i) 0 > a.getD i 0 then
    if right i < hs ∧ a.getD (right i) 0 > a.getD (left i) 0 then right i else left i
  else
    if right i < hs ∧ a.getD (right i) 0 > a.getD i 0 then right i else i

/-- The loop form of `MAX-HEAPIF`: `fuel` bounds the number of sift-down steps. -/
def heapifyGo : Nat → Array Nat → Nat → Nat → Array Nat
  | 0, a, _, _ => a
  | fuel + 1, a, i, hs =>
    if i < hs then
      if largestIdx a i hs = i then a
      else heapifyGo fuel (a.swapIfInBounds i (largestIdx a i hs)) (largestIdx a i hs) hs
    else a

/-- `MAX-HEAPIF` (Python `max_heapify`): sift `a[i]` down inside the heap `[0, hs)`.
`hs` iterations always suffice, because the visited index strictly increases while
staying below `hs`. -/
def maxHeapify (a : Array Nat) (i hs : Nat) : Array Nat := heapifyGo hs a i hs

/-- The loop of `BUILD-MAX-HEAP`: heapify the indices `k-1, k-2, …, 0`. -/
def buildLoop : Nat → Array Nat → Nat → Array Nat
  | 0, a, _ => a
  | k + 1, a, hs => buildLoop k (maxHeapify a k hs) hs

/-- `BUILD-MAX-HEAP` (Python `build_max_heap`): heapify `parent (n-1), …, 0`. -/
def buildMaxHeap (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a else buildLoop (parent (a.size - 1) + 1) a a.size

/-- `extractLoop k a` performs the exchanges `i = k, k-1, …, 1` of CLRS' `HEAPSORT`. -/
def extractLoop : Nat → Array Nat → Array Nat
  | 0, a => a
  | k + 1, a => extractLoop k (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1))

/-- The second half of `HEAPSORT`: run the extraction loop unless the array is trivial. -/
def extractSort (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a else extractLoop (a.size - 1) a

/-- `HEAPSORT` on arrays (Python `heapsort` on the array representation). -/
def heapsortArr (a : Array Nat) : Array Nat := extractSort (buildMaxHeap a)

/-- `heapsort` of the Python program: returns a sorted copy of the input list. -/
def heapsort (arr : List Nat) : List Nat := (heapsortArr arr.toArray).toList

/-! ## Unit tests (the ground cases asserted by the Python `check` function) -/

#eval heapsort [3, 1, 2]
#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsort []
#eval heapsort [42]
#eval buildMaxHeap #[5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval maxHeapify #[1, 3, 2] 0 3
#eval (parent 0, parent 1, parent 2, parent 5, parent 8)
#eval (left 3, right 3)

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
example : heapsortArr #[3, 1, 2] = #[1, 2, 3] := by native_decide
example : parent 0 = 0 := by native_decide
example : parent 1 = 0 := by native_decide
example : parent 2 = 0 := by native_decide
example : parent 5 = 2 := by native_decide
example : parent 8 = 3 := by native_decide
example : left 3 = 7 := by native_decide
example : right 3 = 8 := by native_decide
example : maxHeapify #[1, 3, 2] 0 3 = #[3, 1, 2] := by native_decide
example : maxHeapify #[3, 1, 2] 0 3 = #[3, 1, 2] := by native_decide
example : maxHeapify #[] 0 0 = #[] := by native_decide
example : buildMaxHeap #[1, 2, 3] = #[3, 2, 1] := by native_decide
example : buildMaxHeap #[5, 13, 2, 25, 7, 17, 20, 8, 4] =
    #[25, 13, 20, 8, 7, 17, 2, 5, 4] := by native_decide
example : buildMaxHeap #[] = #[] := by native_decide
example : buildMaxHeap #[42] = #[42] := by native_decide
example : extractLoop 2 #[3, 1, 2] = #[1, 2, 3] := by native_decide
example : heapsort [1] = [1] := by native_decide

/-- The `for arr in [[], [1], [2,1], [3,1,2], [5,13,2,25,7,17,20,8,4]]` loop of the Python
`check` function: `out == sorted(arr)` and `len(out) == len(arr)`. -/
example : ([[], [1], [2, 1], [3, 1, 2], [5, 13, 2, 25, 7, 17, 20, 8, 4]] :
    List (List Nat)).all
    (fun arr => decide (heapsort arr = arr.mergeSort (· ≤ ·) ∧
      (heapsort arr).length = arr.length ∧
      Sorted (· ≤ ·) (heapsort arr) ∧ List.Perm (heapsort arr) arr)) = true := by
  native_decide

/-! ## Pre-condition -/

/-- The pre-condition `pre(arr)` of the Python program: every entry of `arr` is a natural
number (`isinstance(x, int) and not isinstance(x, bool) and x >= 0`).  Since the Lean
implementation is typed at `List Nat`, this is enforced by the type itself, and the
predicate below holds for every input. -/
def Pre (arr : List Nat) : Prop := ∀ x ∈ arr, 0 ≤ x

theorem Pre_holds (arr : List Nat) : Pre arr := fun _ _ => Nat.zero_le _

/-- The same pre-condition on the untyped integer representation used by the Python source,
where violating it raises `ValueError`. -/
def PreInt (arr : List Int) : Prop := ∀ x ∈ arr, 0 ≤ x

/-- Guarded entry point mirroring the Python `ValueError` branch: `none` is returned exactly
when the pre-condition is violated. -/
def heapsortChecked (arr : List Int) : Option (List Nat) :=
  if arr.all (fun x => decide (0 ≤ x)) then some (heapsort (arr.map Int.toNat)) else none

theorem ofNat_toNat_of_nonneg {x : Int} (h : 0 ≤ x) : Int.ofNat (Int.toNat x) = x := by
  rcases Int.eq_ofNat_of_zero_le h with ⟨n, rfl⟩
  rfl

theorem all_decide_nonneg (arr : List Int) :
    arr.all (fun x => decide (0 ≤ x)) = true ↔ PreInt arr := by
  simp only [PreInt, List.all_eq_true]
  constructor
  · intro h x hx
    simpa using h x hx
  · intro h x hx
    simpa using h x hx

theorem map_toNat_ofNat (arr : List Int) (h : PreInt arr) :
    (arr.map Int.toNat).map Int.ofNat = arr := by
  induction arr with
  | nil => rfl
  | cons x xs ih =>
    have hxs : PreInt xs := fun y hy => h y (by simp [hy])
    have hx : Int.ofNat (Int.toNat x) = x := ofNat_toNat_of_nonneg (h x (by simp))
    simp only [List.map_cons, hx]
    congr 1
    exact ih hxs

theorem heapsortChecked_some {arr : List Int} (h : PreInt arr) :
    heapsortChecked arr = some (heapsort (arr.map Int.toNat)) := by
  simp only [heapsortChecked, if_pos ((all_decide_nonneg arr).2 h)]

theorem heapsortChecked_none {arr : List Int} (h : ¬ PreInt arr) :
    heapsortChecked arr = none := by
  simp only [heapsortChecked, if_neg (fun h2 => h ((all_decide_nonneg arr).1 h2))]

instance (arr : List Int) : Decidable (PreInt arr) :=
  decidable_of_iff (arr.all (fun x => decide (0 ≤ x)) = true) (all_decide_nonneg arr)


@[simp] theorem left_def (i : Nat) : left i = 2 * i + 1 := rfl
@[simp] theorem right_def (i : Nat) : right i = 2 * i + 2 := rfl

theorem i_lt_left (i : Nat) : i < left i := by simp [left]; omega
theorem i_lt_right (i : Nat) : i < right i := by simp [right]; omega
theorem left_lt_right (i : Nat) : left i < right i := by simp [left, right]

theorem parent_zero : parent 0 = 0 := by simp [parent]

theorem parent_eq (i : Nat) (h : 0 < i) : parent i = (i - 1) / 2 := by
  simp only [parent]
  exact if_neg (Nat.ne_of_gt h)

theorem parent_lt (i : Nat) (h : 0 < i) : parent i < i := by
  rw [parent_eq i h]
  have : (i - 1) / 2 ≤ i - 1 := Nat.div_le_self _ _
  omega

theorem parent_le (i : Nat) : parent i ≤ i := by
  cases Nat.eq_zero_or_pos i with
  | inl h0 => simp [parent, h0]
  | inr h => exact Nat.le_of_lt (parent_lt i h)

theorem parent_mono {i j : Nat} (h : i ≤ j) : parent i ≤ parent j := by
  cases Nat.eq_zero_or_pos i with
  | inl h0 => simp [h0, parent]
  | inr hi =>
    have hj : 0 < j := Nat.lt_of_lt_of_le hi h
    rw [parent_eq i hi, parent_eq j hj]
    exact Nat.div_le_div_right (by omega)

theorem left_parent_le (j : Nat) (h : 0 < j) : left (parent j) ≤ j := by
  rw [parent_eq j h]; simp [left]; omega

theorem le_right_parent (j : Nat) (h : 0 < j) : j ≤ right (parent j) := by
  rw [parent_eq j h]; simp [right]; omega

theorem eq_left_parent_or_eq_right_parent (j : Nat) (h : 0 < j) :
    j = left (parent j) ∨ j = right (parent j) := by
  have h1 := left_parent_le j h
  have h2 := le_right_parent j h
  simp [left, right] at h1 h2 ⊢
  omega

theorem le_parent_of_left_lt {j n : Nat} (h : left j < n) : j ≤ parent (n - 1) := by
  have hn : 0 < n := by simp [left] at h; omega
  have h2 : 0 < n - 1 ∨ n - 1 = 0 := by omega
  cases h2 with
  | inl hp =>
    rw [parent_eq (n - 1) hp]
    simp [left] at h ⊢
    omega
  | inr hz =>
    simp [hz] at hn h ⊢
    omega

theorem getD_eq_getElem {a : Array Nat} {i : Nat} (h : i < a.size) :
    a.getD i 0 = a[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?, dif_pos h]


/-! ## The max-heap predicate -/




theorem HeapAt_of_left_ge {a : Array Nat} {hs j : Nat} (hl : ¬ left j < hs) : HeapAt a hs j :=
  ⟨fun h => absurd h hl,
    fun h => (hl (Nat.lt_of_lt_of_le (left_lt_right j) (Nat.le_of_lt h))).elim⟩

theorem IsHeap_of_le_one {a : Array Nat} {hs : Nat} (h : hs ≤ 1) : IsHeap a hs := by
  intro j _ hj
  exact HeapAt_of_left_ge (by simp only [left] at hj ⊢; omega)

theorem HeapAt_of_parent_lt {a : Array Nat} {n j : Nat} (_hj : j < n) (h : parent (n - 1) < j) :
    HeapAt a n j :=
  HeapAt_of_left_ge (fun hl => by
    have := le_parent_of_left_lt hl
    omega)

/-! ### Swapping two entries of an array -/

theorem getD_swapIfInBounds {a : Array Nat} {i j k : Nat} (hi : i < a.size) (hj : j < a.size) :
    (a.swapIfInBounds i j).getD k 0 =
      if k = i then a.getD j 0 else if k = j then a.getD i 0 else a.getD k 0 := by
  have hswap : a.swapIfInBounds i j = a.swap i j hi hj := by
    simp [Array.swapIfInBounds, hi, hj]
  have hsz : (a.swap i j hi hj).size = a.size := Array.size_swap
  rw [hswap]
  by_cases hk : k < a.size
  · have hk' : k < (a.swap i j hi hj).size := by rwa [hsz]
    rw [getD_eq_getElem hk', getD_eq_getElem hj, getD_eq_getElem hi, getD_eq_getElem hk,
      Array.getElem_swap hi hj hk']
  · have hk' : ¬ k < (a.swap i j hi hj).size := by rwa [hsz]
    have hki : k ≠ i := by omega
    have hkj : k ≠ j := by omega
    rw [if_neg hki, if_neg hkj,
      Array.getD_eq_getD_getElem?, Array.getD_getElem?, dif_neg hk']
    rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?, dif_neg hk]

theorem getD_swapIfInBounds_ne {a : Array Nat} {i j k : Nat} (hi : i < a.size) (hj : j < a.size)
    (hk : k ≠ i) (hk' : k ≠ j) : (a.swapIfInBounds i j).getD k 0 = a.getD k 0 := by
  rw [getD_swapIfInBounds hi hj, if_neg hk, if_neg hk']

theorem getD_swapIfInBounds_self {a : Array Nat} {i k : Nat} (hi : i < a.size) :
    (a.swapIfInBounds i i).getD k 0 = a.getD k 0 := by
  rw [getD_swapIfInBounds hi hi]
  by_cases h : k = i <;> simp [h]

theorem perm_swapIfInBounds (a : Array Nat) (i j : Nat) : Array.Perm (a.swapIfInBounds i j) a := by
  by_cases hi : i < a.size
  · by_cases hj : j < a.size
    · have hswap : a.swapIfInBounds i j = a.swap i j hi hj := by
        simp [Array.swapIfInBounds, hi, hj]
      rw [hswap]
      exact Array.swap_perm hi hj
    · rw [show a.swapIfInBounds i j = a from by simp [Array.swapIfInBounds, hi, hj]]
  · rw [show a.swapIfInBounds i j = a from by simp [Array.swapIfInBounds, hi]]

/-! ## `MAX-HEAPIF` (CLRS 6.4) -/


theorem largestIdx_eq_right_ll {a : Array Nat} {i hs : Nat}
    (h1 : left i < hs ∧ a.getD (left i) 0 > a.getD i 0)
    (h2 : right i < hs ∧ a.getD (right i) 0 > a.getD (left i) 0) :
    largestIdx a i hs = right i := by unfold largestIdx; rw [if_pos h1, if_pos h2]

theorem largestIdx_eq_left_ll {a : Array Nat} {i hs : Nat}
    (h1 : left i < hs ∧ a.getD (left i) 0 > a.getD i 0)
    (h2 : ¬(right i < hs ∧ a.getD (right i) 0 > a.getD (left i) 0)) :
    largestIdx a i hs = left i := by unfold largestIdx; rw [if_pos h1, if_neg h2]

theorem largestIdx_eq_right_rl {a : Array Nat} {i hs : Nat}
    (h1 : ¬(left i < hs ∧ a.getD (left i) 0 > a.getD i 0))
    (h2 : right i < hs ∧ a.getD (right i) 0 > a.getD i 0) :
    largestIdx a i hs = right i := by unfold largestIdx; rw [if_neg h1, if_pos h2]

theorem largestIdx_eq_self_rr {a : Array Nat} {i hs : Nat}
    (h1 : ¬(left i < hs ∧ a.getD (left i) 0 > a.getD i 0))
    (h2 : ¬(right i < hs ∧ a.getD (right i) 0 > a.getD i 0)) :
    largestIdx a i hs = i := by unfold largestIdx; rw [if_neg h1, if_neg h2]

theorem largestIdx_spec {a : Array Nat} {i hs : Nat} :
    (largestIdx a i hs = i ∧
      ¬(left i < hs ∧ a.getD (left i) 0 > a.getD i 0) ∧
      ¬(right i < hs ∧ a.getD (right i) 0 > a.getD i 0)) ∨
    (largestIdx a i hs = left i ∧
      (left i < hs ∧ a.getD (left i) 0 > a.getD i 0) ∧
      ¬(right i < hs ∧ a.getD (right i) 0 > a.getD (left i) 0)) ∨
    (largestIdx a i hs = right i ∧ right i < hs ∧
      ((a.getD (left i) 0 > a.getD i 0 ∧ a.getD (right i) 0 > a.getD (left i) 0) ∨
       (¬(left i < hs ∧ a.getD (left i) 0 > a.getD i 0) ∧
         a.getD (right i) 0 > a.getD i 0))) := by
  by_cases h1 : left i < hs ∧ a.getD (left i) 0 > a.getD i 0
  · by_cases h2 : right i < hs ∧ a.getD (right i) 0 > a.getD (left i) 0
    · right; right
      exact ⟨largestIdx_eq_right_ll h1 h2, h2.1, Or.inl ⟨h1.2, h2.2⟩⟩
    · right; left
      exact ⟨largestIdx_eq_left_ll h1 h2, h1, h2⟩
  · by_cases h2 : right i < hs ∧ a.getD (right i) 0 > a.getD i 0
    · right; right
      exact ⟨largestIdx_eq_right_rl h1 h2, h2.1, Or.inr ⟨h1, h2.2⟩⟩
    · left
      exact ⟨largestIdx_eq_self_rr h1 h2, h1, h2⟩

theorem largestIdx_cases (a : Array Nat) (i hs : Nat) :
    largestIdx a i hs = i ∨ largestIdx a i hs = left i ∨ largestIdx a i hs = right i := by
  rcases @largestIdx_spec a i hs with (⟨e, _, _⟩ | ⟨e, _, _⟩ | ⟨e, _, _⟩)
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)

theorem largestIdx_eq_left_or_right {a : Array Nat} {i hs : Nat} (h : largestIdx a i hs ≠ i) :
    largestIdx a i hs = left i ∨ largestIdx a i hs = right i := by
  rcases largestIdx_cases a i hs with (e | e | e)
  · exact absurd e h
  · exact Or.inl e
  · exact Or.inr e

theorem largestIdx_of_not_lt {a : Array Nat} {i hs : Nat} (h : ¬ i < hs) :
    largestIdx a i hs = i :=
  largestIdx_eq_self_rr
    (fun hc => absurd hc.1 (by have := i_lt_left i; omega))
    (fun hc => absurd hc.1 (by have := i_lt_right i; omega))

theorem largestIdx_eq_self_HeapAt {a : Array Nat} {i hs : Nat} (h : largestIdx a i hs = i) :
    HeapAt a hs i := by
  have h1 : ¬(left i < hs ∧ a.getD (left i) 0 > a.getD i 0) := by
    rcases @largestIdx_spec a i hs with (⟨_, h1, _⟩ | ⟨e, _, _⟩ | ⟨e, _, _⟩)
    · exact h1
    · exact absurd (e.symm.trans h) (by have := i_lt_left i; omega)
    · exact absurd (e.symm.trans h) (by have := i_lt_right i; omega)
  have h2 : ¬(right i < hs ∧ a.getD (right i) 0 > a.getD i 0) := by
    rcases @largestIdx_spec a i hs with (⟨_, _, h2⟩ | ⟨e, _, _⟩ | ⟨e, _, _⟩)
    · exact h2
    · exact absurd (e.symm.trans h) (by have := i_lt_left i; omega)
    · exact absurd (e.symm.trans h) (by have := i_lt_right i; omega)
  constructor
  · intro hl
    by_cases hv : a.getD (left i) 0 > a.getD i 0
    · exact absurd (And.intro hl hv) h1
    · omega
  · intro hr
    by_cases hv : a.getD (right i) 0 > a.getD i 0
    · exact absurd (And.intro hr hv) h2
    · omega

theorem largestIdx_eq_left {a : Array Nat} {i hs : Nat} (h : largestIdx a i hs = left i) :
    left i < hs ∧ a.getD i 0 ≤ a.getD (left i) 0 ∧
      (right i < hs → a.getD (right i) 0 ≤ a.getD (left i) 0) := by
  have hne : right i ≠ left i := by have := left_lt_right i; omega
  have h1 : left i < hs ∧ a.getD (left i) 0 > a.getD i 0 := by
    rcases @largestIdx_spec a i hs with (⟨e, _, _⟩ | ⟨_, h1, _⟩ | ⟨e, _, _⟩)
    · exact absurd (e.symm.trans h) (by have := i_lt_left i; omega)
    · exact h1
    · exact absurd (e.symm.trans h) hne
  have h2 : ¬(right i < hs ∧ a.getD (right i) 0 > a.getD (left i) 0) := by
    rcases @largestIdx_spec a i hs with (⟨e, _, _⟩ | ⟨_, _, h2⟩ | ⟨e, _, _⟩)
    · exact absurd (e.symm.trans h) (by have := i_lt_left i; omega)
    · exact h2
    · exact absurd (e.symm.trans h) hne
  refine ⟨h1.1, Nat.le_of_lt h1.2, ?_⟩
  intro hr
  by_cases hv : a.getD (right i) 0 > a.getD (left i) 0
  · exact absurd (And.intro hr hv) h2
  · omega

theorem largestIdx_eq_right {a : Array Nat} {i hs : Nat} (h : largestIdx a i hs = right i) :
    right i < hs ∧ a.getD i 0 ≤ a.getD (right i) 0 ∧
      (left i < hs → a.getD (left i) 0 ≤ a.getD (right i) 0) := by
  have hne : left i ≠ right i := by have := left_lt_right i; omega
  rcases @largestIdx_spec a i hs with (⟨e, _, _⟩ | ⟨e, _, _⟩ | ⟨e, hhs, h3⟩)
  · exact absurd (e.symm.trans h) (by have := i_lt_right i; omega)
  · exact absurd (e.symm.trans h) hne
  · rcases h3 with (⟨hv1, hv2⟩ | ⟨h1, hv⟩)
    · refine ⟨hhs, by omega, ?_⟩
      intro _
      exact Nat.le_of_lt hv2
    · refine ⟨hhs, Nat.le_of_lt hv, ?_⟩
      intro hl
      have hnv : ¬(a.getD (left i) 0 > a.getD i 0) := fun h2 => h1 (And.intro hl h2)
      omega

theorem largestIdx_ne_self {a : Array Nat} {i hs : Nat} (h : largestIdx a i hs ≠ i) :
    i < largestIdx a i hs ∧ largestIdx a i hs < hs := by
  rcases largestIdx_eq_left_or_right h with (e | e)
  · have hl := largestIdx_eq_left e
    rw [e]
    exact ⟨i_lt_left i, hl.1⟩
  · have hr := largestIdx_eq_right e
    rw [e]
    exact ⟨i_lt_right i, hr.1⟩


theorem heapifyGo_zero (a : Array Nat) (i hs : Nat) : heapifyGo 0 a i hs = a := rfl

theorem heapifyGo_succ (fuel : Nat) (a : Array Nat) (i hs : Nat) :
    heapifyGo (fuel + 1) a i hs =
      if i < hs then
        if largestIdx a i hs = i then a
        else heapifyGo fuel (a.swapIfInBounds i (largestIdx a i hs)) (largestIdx a i hs) hs
      else a := rfl


theorem size_heapifyGo (fuel : Nat) : ∀ (a : Array Nat) (i hs : Nat),
    (heapifyGo fuel a i hs).size = a.size := by
  induction fuel with
  | zero => intro a i hs; rfl
  | succ fuel ih =>
    intro a i hs
    rw [heapifyGo_succ]
    by_cases hi : i < hs
    · rw [if_pos hi]
      by_cases heq : largestIdx a i hs = i
      · rw [if_pos heq]
      · rw [if_neg heq,
          ih (a.swapIfInBounds i (largestIdx a i hs)) (largestIdx a i hs) hs,
          Array.size_swapIfInBounds]
    · rw [if_neg hi]

theorem size_maxHeapify (a : Array Nat) (i hs : Nat) : (maxHeapify a i hs).size = a.size :=
  size_heapifyGo hs a i hs

theorem perm_heapifyGo (fuel : Nat) : ∀ (a : Array Nat) (i hs : Nat),
    Array.Perm (heapifyGo fuel a i hs) a := by
  induction fuel with
  | zero => intro a i hs; exact Array.Perm.refl _
  | succ fuel ih =>
    intro a i hs
    rw [heapifyGo_succ]
    by_cases hi : i < hs
    · rw [if_pos hi]
      by_cases heq : largestIdx a i hs = i
      · rw [if_pos heq]
      · rw [if_neg heq]
        exact Array.Perm.trans
          (ih (a.swapIfInBounds i (largestIdx a i hs)) (largestIdx a i hs) hs)
          (perm_swapIfInBounds a i (largestIdx a i hs))
    · rw [if_neg hi]

theorem perm_maxHeapify (a : Array Nat) (i hs : Nat) : Array.Perm (maxHeapify a i hs) a :=
  perm_heapifyGo hs a i hs

theorem getD_heapifyGo_of_lt (fuel : Nat) : ∀ (a : Array Nat) (i hs p : Nat),
    hs ≤ a.size → p < i → (heapifyGo fuel a i hs).getD p 0 = a.getD p 0 := by
  induction fuel with
  | zero => intro a i hs p _ _; rfl
  | succ fuel ih =>
    intro a i hs p hle hp
    rw [heapifyGo_succ]
    by_cases hi : i < hs
    · rw [if_pos hi]
      by_cases heq : largestIdx a i hs = i
      · rw [if_pos heq]
      · rw [if_neg heq]
        have hlt := largestIdx_ne_self heq
        have hsize : hs ≤ (a.swapIfInBounds i (largestIdx a i hs)).size := by
          rw [Array.size_swapIfInBounds]; exact hle
        have hi' : i < a.size := Nat.lt_of_lt_of_le hi hle
        have hm' : largestIdx a i hs < a.size := Nat.lt_of_lt_of_le hlt.2 hle
        rw [ih (a.swapIfInBounds i (largestIdx a i hs)) (largestIdx a i hs) hs p hsize
            (by omega),
          getD_swapIfInBounds_ne hi' hm' (by omega) (by omega)]
    · rw [if_neg hi]

theorem getD_heapifyGo_of_ge (fuel : Nat) : ∀ (a : Array Nat) (i hs p : Nat),
    hs ≤ a.size → hs ≤ p → (heapifyGo fuel a i hs).getD p 0 = a.getD p 0 := by
  induction fuel with
  | zero => intro a i hs p _ _; rfl
  | succ fuel ih =>
    intro a i hs p hle hp
    rw [heapifyGo_succ]
    by_cases hi : i < hs
    · rw [if_pos hi]
      by_cases heq : largestIdx a i hs = i
      · rw [if_pos heq]
      · rw [if_neg heq]
        have hlt := largestIdx_ne_self heq
        have hsize : hs ≤ (a.swapIfInBounds i (largestIdx a i hs)).size := by
          rw [Array.size_swapIfInBounds]; exact hle
        have hi' : i < a.size := Nat.lt_of_lt_of_le hi hle
        have hm' : largestIdx a i hs < a.size := Nat.lt_of_lt_of_le hlt.2 hle
        rw [ih (a.swapIfInBounds i (largestIdx a i hs)) (largestIdx a i hs) hs p hsize hp,
          getD_swapIfInBounds_ne hi' hm' (by omega) (by omega)]
    · rw [if_neg hi]

theorem getD_heapifyGo_of_between (fuel : Nat) : ∀ (a : Array Nat) (i hs p : Nat),
    hs ≤ a.size → i < p → p < left i → (heapifyGo fuel a i hs).getD p 0 = a.getD p 0 := by
  induction fuel with
  | zero => intro a i hs p _ _ _; rfl
  | succ fuel ih =>
    intro a i hs p hle hp1 hp2
    rw [heapifyGo_succ]
    by_cases hi : i < hs
    · rw [if_pos hi]
      by_cases heq : largestIdx a i hs = i
      · rw [if_pos heq]
      · rw [if_neg heq]
        have hsize : hs ≤ (a.swapIfInBounds i (largestIdx a i hs)).size := by
          rw [Array.size_swapIfInBounds]; exact hle
        have hpl : p < largestIdx a i hs := by
          rcases largestIdx_eq_left_or_right heq with (e | e) <;> rw [e] <;>
            simp only [left, right] at hp2 ⊢ <;> omega
        have hi' : i < a.size := Nat.lt_of_lt_of_le hi hle
        have hm' : largestIdx a i hs < a.size :=
          Nat.lt_of_lt_of_le (largestIdx_ne_self heq).2 hle
        rw [getD_heapifyGo_of_lt fuel (a.swapIfInBounds i (largestIdx a i hs))
            (largestIdx a i hs) hs p hsize hpl,
          getD_swapIfInBounds_ne hi' hm' (by omega) (by omega)]
    · rw [if_neg hi]

theorem HeapAt_swap_of_lt {a : Array Nat} {i m hs j : Nat} (hle : hs ≤ a.size)
    (him : i < m) (hm : m < hs) (_hj : m < j) (_hjs : j < hs) (h : HeapAt a hs j) :
    HeapAt (a.swapIfInBounds i m) hs j := by
  have hi' : i < a.size := Nat.lt_of_lt_of_le (Nat.lt_trans him hm) hle
  have hm' : m < a.size := Nat.lt_of_lt_of_le hm hle
  have h1 : (a.swapIfInBounds i m).getD j 0 = a.getD j 0 :=
    getD_swapIfInBounds_ne hi' hm' (by omega) (by omega)
  have h2 : (a.swapIfInBounds i m).getD (left j) 0 = a.getD (left j) 0 :=
    getD_swapIfInBounds_ne hi' hm' (by have := i_lt_left j; omega)
      (by have := i_lt_left j; omega)
  have h3 : (a.swapIfInBounds i m).getD (right j) 0 = a.getD (right j) 0 :=
    getD_swapIfInBounds_ne hi' hm' (by have := i_lt_right j; omega)
      (by have := i_lt_right j; omega)
  constructor
  · intro hl
    rw [h2, h1]
    exact h.1 hl
  · intro hr
    rw [h3, h1]
    exact h.2 hr

theorem HeapAt_swap_largestIdx {a : Array Nat} {i hs : Nat} (hle : hs ≤ a.size) (hi : i < hs) :
    HeapAt (a.swapIfInBounds i (largestIdx a i hs)) hs i := by
  have hi' : i < a.size := Nat.lt_of_lt_of_le hi hle
  have hm' : largestIdx a i hs < a.size := by
    rcases largestIdx_cases a i hs with (e | e | e)
    · rw [e]; exact hi'
    · rw [e]; exact Nat.lt_of_lt_of_le (largestIdx_eq_left e).1 hle
    · rw [e]; exact Nat.lt_of_lt_of_le (largestIdx_eq_right e).1 hle
  rcases largestIdx_cases a i hs with (e | e | e)
  · have hH := largestIdx_eq_self_HeapAt e
    have h1 : ∀ k, (a.swapIfInBounds i (largestIdx a i hs)).getD k 0 = a.getD k 0 := by
      intro k; rw [e]; exact getD_swapIfInBounds_self hi'
    constructor
    · intro hl
      rw [h1, h1]
      exact hH.1 hl
    · intro hr
      rw [h1, h1]
      exact hH.2 hr
  · have hl := largestIdx_eq_left e
    have hli' : left i < a.size := Nat.lt_of_lt_of_le hl.1 hle
    have hA : (a.swapIfInBounds i (largestIdx a i hs)).getD i 0 = a.getD (left i) 0 := by
      rw [e, getD_swapIfInBounds hi' hli', if_pos rfl]
    have hB : (a.swapIfInBounds i (largestIdx a i hs)).getD (left i) 0 = a.getD i 0 := by
      rw [e, getD_swapIfInBounds hi' hli', if_neg (by have := i_lt_left i; omega), if_pos rfl]
    have hC : (a.swapIfInBounds i (largestIdx a i hs)).getD (right i) 0 = a.getD (right i) 0 := by
      rw [e]
      exact getD_swapIfInBounds_ne hi' hli' (by have := i_lt_right i; omega)
        (by have := left_lt_right i; omega)
    constructor
    · intro _
      rw [hB, hA]
      exact hl.2.1
    · intro hr
      rw [hC, hA]
      exact hl.2.2 hr
  · have hr := largestIdx_eq_right e
    have hri' : right i < a.size := Nat.lt_of_lt_of_le hr.1 hle
    have hA : (a.swapIfInBounds i (largestIdx a i hs)).getD i 0 = a.getD (right i) 0 := by
      rw [e, getD_swapIfInBounds hi' hri', if_pos rfl]
    have hB : (a.swapIfInBounds i (largestIdx a i hs)).getD (right i) 0 = a.getD i 0 := by
      rw [e, getD_swapIfInBounds hi' hri', if_neg (by have := i_lt_right i; omega), if_pos rfl]
    have hC : (a.swapIfInBounds i (largestIdx a i hs)).getD (left i) 0 = a.getD (left i) 0 := by
      rw [e]
      exact getD_swapIfInBounds_ne hi' hri' (by have := i_lt_left i; omega)
        (by have := left_lt_right i; omega)
    constructor
    · intro hlt
      rw [hC, hA]
      exact hr.2.2 hlt
    · intro _
      rw [hB, hA]
      exact hr.2.1

theorem heapifyGo_le (fuel : Nat) : ∀ (a : Array Nat) (i hs B : Nat),
    hs ≤ a.size → (∀ m, i ≤ m → m < hs → a.getD m 0 ≤ B) →
    (∀ m, i ≤ m → m < hs → (heapifyGo fuel a i hs).getD m 0 ≤ B) := by
  induction fuel with
  | zero => intro a i hs B _ h; exact h
  | succ fuel ih =>
    intro a i hs B hle h
    rw [heapifyGo_succ]
    by_cases hi : i < hs
    · rw [if_pos hi]
      by_cases heq : largestIdx a i hs = i
      · rw [if_pos heq]
        exact h
      · rw [if_neg heq]
        have hlt := largestIdx_ne_self heq
        have hsize : hs ≤ (a.swapIfInBounds i (largestIdx a i hs)).size := by
          rw [Array.size_swapIfInBounds]; exact hle
        have hi' : i < a.size := Nat.lt_of_lt_of_le hi hle
        have hm' : largestIdx a i hs < a.size := Nat.lt_of_lt_of_le hlt.2 hle
        have hbound : ∀ m', largestIdx a i hs ≤ m' → m' < hs →
            (a.swapIfInBounds i (largestIdx a i hs)).getD m' 0 ≤ B := by
          intro m' hm'' hm'hs
          by_cases h1 : m' = i
          · omega
          · by_cases h2 : m' = largestIdx a i hs
            · rw [getD_swapIfInBounds hi' hm', if_neg h1, if_pos h2]
              exact h i (Nat.le_refl _) hi
            · rw [getD_swapIfInBounds hi' hm', if_neg h1, if_neg h2]
              exact h m' (by omega) hm'hs
        intro m hm hmhs
        by_cases hcase : largestIdx a i hs ≤ m
        · exact ih (a.swapIfInBounds i (largestIdx a i hs)) (largestIdx a i hs) hs B hsize
            hbound m hcase hmhs
        · have hun : (heapifyGo fuel (a.swapIfInBounds i (largestIdx a i hs))
              (largestIdx a i hs) hs).getD m 0 =
              (a.swapIfInBounds i (largestIdx a i hs)).getD m 0 :=
            getD_heapifyGo_of_lt fuel (a.swapIfInBounds i (largestIdx a i hs))
              (largestIdx a i hs) hs m hsize (by omega)
          rw [hun]
          by_cases h1 : m = i
          · rw [getD_swapIfInBounds hi' hm', if_pos h1]
            exact h (largestIdx a i hs) (by omega) hlt.2
          · rw [getD_swapIfInBounds hi' hm', if_neg h1, if_neg (by omega)]
            exact h m hm hmhs
    · rw [if_neg hi]
      exact h

theorem getD_heapifyGo_self_le (fuel : Nat) : ∀ (a : Array Nat) (i hs B : Nat),
    hs ≤ a.size → i < hs → a.getD i 0 ≤ B →
    (left i < hs → a.getD (left i) 0 ≤ B) → (right i < hs → a.getD (right i) 0 ≤ B) →
    (heapifyGo fuel a i hs).getD i 0 ≤ B := by
  induction fuel with
  | zero => intro a i hs B _ _ h0 _ _; exact h0
  | succ fuel ih =>
    intro a i hs B hle hi h0 hl hr
    rw [heapifyGo_succ, if_pos hi]
    by_cases heq : largestIdx a i hs = i
    · rw [if_pos heq]
      exact h0
    · rw [if_neg heq]
      have hlt := largestIdx_ne_self heq
      obtain ⟨him, hms⟩ := hlt
      have hsize : hs ≤ (a.swapIfInBounds i (largestIdx a i hs)).size := by
        rw [Array.size_swapIfInBounds]; exact hle
      have hi' : i < a.size := Nat.lt_of_lt_of_le hi hle
      have hm' : largestIdx a i hs < a.size := Nat.lt_of_lt_of_le hms hle
      have hswap : (a.swapIfInBounds i (largestIdx a i hs)).getD i 0 =
          a.getD (largestIdx a i hs) 0 := by
        rw [getD_swapIfInBounds hi' hm', if_pos rfl]
      have hle' : a.getD (largestIdx a i hs) 0 ≤ B := by
        rcases largestIdx_eq_left_or_right heq with (e | e)
        · rw [e] at hms ⊢; exact hl hms
        · rw [e] at hms ⊢; exact hr hms
      have hun : (heapifyGo fuel (a.swapIfInBounds i (largestIdx a i hs))
          (largestIdx a i hs) hs).getD i 0 =
          (a.swapIfInBounds i (largestIdx a i hs)).getD i 0 :=
        getD_heapifyGo_of_lt fuel (a.swapIfInBounds i (largestIdx a i hs))
          (largestIdx a i hs) hs i hsize him
      rw [hun, hswap]
      exact hle'

theorem HeapAt_heapifyGo_child (fuel : Nat) {a : Array Nat} {i m hs : Nat}
    (hle : hs ≤ a.size) (him : i < m) (hm : m < hs)
    (hchild : m = left i ∨ m = right i) (hHi : HeapAt a hs i)
    (h0 : a.getD m 0 ≤ a.getD i 0)
    (hl : left m < hs → a.getD (left m) 0 ≤ a.getD i 0)
    (hr : right m < hs → a.getD (right m) 0 ≤ a.getD i 0) :
    HeapAt (heapifyGo fuel a m hs) hs i := by
  have hmi : (heapifyGo fuel a m hs).getD i 0 = a.getD i 0 :=
    getD_heapifyGo_of_lt fuel a m hs i hle him
  have hself : (heapifyGo fuel a m hs).getD m 0 ≤ a.getD i 0 :=
    getD_heapifyGo_self_le fuel a m hs (a.getD i 0) hle hm h0 hl hr
  constructor
  · intro hl'
    rcases hchild with (e | e)
    · rw [← e, hmi]
      exact hself
    · have hlt : left i < m := by rw [e]; have := left_lt_right i; omega
      rw [getD_heapifyGo_of_lt fuel a m hs (left i) hle hlt, hmi]
      exact hHi.1 hl'
  · intro hr'
    rcases hchild with (e | e)
    · have h1 : m < right i := by rw [e]; have := left_lt_right i; omega
      have h2 : right i < left m := by rw [e]; simp only [left, right]; omega
      rw [getD_heapifyGo_of_between fuel a m hs (right i) hle h1 h2, hmi]
      exact hHi.2 hr'
    · rw [← e, hmi]
      exact hself

theorem heapifyGo_HeapAt (fuel : Nat) : ∀ (a : Array Nat) (i hs : Nat),
    hs ≤ a.size → hs - i ≤ fuel →
    (∀ j, i < j → j < hs → HeapAt a hs j) →
    (∀ j, i ≤ j → j < hs → HeapAt (heapifyGo fuel a i hs) hs j) := by
  induction fuel with
  | zero =>
    intro a i hs _ hf _ j hj hjhs
    omega
  | succ fuel ih =>
    intro a i hs hle hf hcond
    rw [heapifyGo_succ]
    by_cases hi : i < hs
    · rw [if_pos hi]
      by_cases heq : largestIdx a i hs = i
      · rw [if_pos heq]
        intro j hj hjhs
        by_cases hj' : j = i
        · rw [hj']
          exact largestIdx_eq_self_HeapAt heq
        · exact hcond j (by omega) hjhs
      · rw [if_neg heq]
        have hlt := largestIdx_ne_self heq
        obtain ⟨him, hms⟩ := hlt
        have hi' : i < a.size := Nat.lt_of_lt_of_le hi hle
        have hm' : largestIdx a i hs < a.size := Nat.lt_of_lt_of_le hms hle
        have hsize : hs ≤ (a.swapIfInBounds i (largestIdx a i hs)).size := by
          rw [Array.size_swapIfInBounds]; exact hle
        have hf' : hs - largestIdx a i hs ≤ fuel := by omega
        have hcond' : ∀ j, largestIdx a i hs < j → j < hs →
            HeapAt (a.swapIfInBounds i (largestIdx a i hs)) hs j := by
          intro j hj hjhs
          exact HeapAt_swap_of_lt hle him hms hj hjhs (hcond j (by omega) hjhs)
        have hres := ih (a.swapIfInBounds i (largestIdx a i hs)) (largestIdx a i hs) hs
          hsize hf' hcond'
        intro j hj hjhs
        rcases Nat.eq_or_lt_of_le hj with (rfl | hj')
        · have hsw1 : (a.swapIfInBounds i (largestIdx a i hs)).getD i 0 =
              a.getD (largestIdx a i hs) 0 := by
            rw [getD_swapIfInBounds hi' hm', if_pos rfl]
          have hsw2 : (a.swapIfInBounds i (largestIdx a i hs)).getD (largestIdx a i hs) 0 =
              a.getD i 0 := by
            rw [getD_swapIfInBounds hi' hm', if_neg (by omega), if_pos rfl]
          have hsw3 : ∀ p, i < p → largestIdx a i hs < p →
              (a.swapIfInBounds i (largestIdx a i hs)).getD p 0 = a.getD p 0 := by
            intro p hp1 hp2
            exact getD_swapIfInBounds_ne hi' hm' (by omega) (by omega)
          have hb0 : (a.swapIfInBounds i (largestIdx a i hs)).getD (largestIdx a i hs) 0 ≤
              (a.swapIfInBounds i (largestIdx a i hs)).getD i 0 := by
            rw [hsw2, hsw1]
            rcases largestIdx_eq_left_or_right heq with (e | e)
            · rw [e]; exact (largestIdx_eq_left e).2.1
            · rw [e]; exact (largestIdx_eq_right e).2.1
          have hHm : HeapAt a hs (largestIdx a i hs) :=
            hcond (largestIdx a i hs) him hms
          have hbl : left (largestIdx a i hs) < hs →
              (a.swapIfInBounds i (largestIdx a i hs)).getD (left (largestIdx a i hs)) 0 ≤
              (a.swapIfInBounds i (largestIdx a i hs)).getD i 0 := by
            intro hl
            rw [hsw3 _ (by have := i_lt_left (largestIdx a i hs); omega)
              (by have := i_lt_left (largestIdx a i hs); omega), hsw1]
            exact hHm.1 hl
          have hbr : right (largestIdx a i hs) < hs →
              (a.swapIfInBounds i (largestIdx a i hs)).getD (right (largestIdx a i hs)) 0 ≤
              (a.swapIfInBounds i (largestIdx a i hs)).getD i 0 := by
            intro hr
            rw [hsw3 _ (by have := i_lt_right (largestIdx a i hs); omega)
              (by have := i_lt_right (largestIdx a i hs); omega), hsw1]
            exact hHm.2 hr
          exact HeapAt_heapifyGo_child fuel hsize him hms
            (largestIdx_eq_left_or_right heq) (HeapAt_swap_largestIdx hle hi) hb0 hbl hbr
        · by_cases hjm : largestIdx a i hs ≤ j
          · exact hres j hjm hjhs
          · have hjl : j < largestIdx a i hs := by omega
            have h1 : (heapifyGo fuel (a.swapIfInBounds i (largestIdx a i hs))
                (largestIdx a i hs) hs).getD j 0 = a.getD j 0 := by
              rw [getD_heapifyGo_of_lt fuel (a.swapIfInBounds i (largestIdx a i hs))
                  (largestIdx a i hs) hs j hsize hjl,
                getD_swapIfInBounds_ne hi' hm' (by omega) (by omega)]
            have hl1 : largestIdx a i hs < left j := by
              rcases largestIdx_eq_left_or_right heq with (e | e) <;>
                rw [e] at hjl ⊢ <;> simp only [left, right] at hjl ⊢ <;> omega
            have hl2 : left j < left (largestIdx a i hs) := by
              rcases largestIdx_eq_left_or_right heq with (e | e) <;>
                rw [e] at hjl ⊢ <;> simp only [left, right] at hjl ⊢ <;> omega
            have h2 : (heapifyGo fuel (a.swapIfInBounds i (largestIdx a i hs))
                (largestIdx a i hs) hs).getD (left j) 0 = a.getD (left j) 0 := by
              rw [getD_heapifyGo_of_between fuel (a.swapIfInBounds i (largestIdx a i hs))
                  (largestIdx a i hs) hs (left j) hsize hl1 hl2,
                getD_swapIfInBounds_ne hi' hm' (by have := i_lt_left j; omega)
                  (by have := i_lt_left j; omega)]
            have hr1 : largestIdx a i hs < right j := by
              rcases largestIdx_eq_left_or_right heq with (e | e) <;>
                rw [e] at hjl ⊢ <;> simp only [left, right] at hjl ⊢ <;> omega
            have hr2 : right j < left (largestIdx a i hs) := by
              rcases largestIdx_eq_left_or_right heq with (e | e) <;>
                rw [e] at hjl ⊢ <;> simp only [left, right] at hjl ⊢ <;> omega
            have h3 : (heapifyGo fuel (a.swapIfInBounds i (largestIdx a i hs))
                (largestIdx a i hs) hs).getD (right j) 0 = a.getD (right j) 0 := by
              rw [getD_heapifyGo_of_between fuel (a.swapIfInBounds i (largestIdx a i hs))
                  (largestIdx a i hs) hs (right j) hsize hr1 hr2,
                getD_swapIfInBounds_ne hi' hm' (by have := i_lt_right j; omega)
                  (by have := i_lt_right j; omega)]
            have hH := hcond j hj' hjhs
            constructor
            · intro hl
              rw [h2, h1]
              exact hH.1 hl
            · intro hr
              rw [h3, h1]
              exact hH.2 hr
    · rw [if_neg hi]
      intro j hj hjhs
      omega

theorem maxHeapify_HeapAt {a : Array Nat} {i hs : Nat} (hle : hs ≤ a.size)
    (hcond : ∀ j, i < j → j < hs → HeapAt a hs j) :
    ∀ j, i ≤ j → j < hs → HeapAt (maxHeapify a i hs) hs j :=
  heapifyGo_HeapAt hs a i hs hle (Nat.sub_le hs i) hcond

theorem maxHeapify_le {a : Array Nat} {i hs B : Nat} (hle : hs ≤ a.size)
    (h : ∀ m, i ≤ m → m < hs → a.getD m 0 ≤ B) :
    ∀ m, i ≤ m → m < hs → (maxHeapify a i hs).getD m 0 ≤ B :=
  heapifyGo_le hs a i hs B hle h

theorem getD_maxHeapify_of_ge {a : Array Nat} {i hs p : Nat} (hle : hs ≤ a.size) (hp : hs ≤ p) :
    (maxHeapify a i hs).getD p 0 = a.getD p 0 :=
  getD_heapifyGo_of_ge hs a i hs p hle hp

theorem getD_maxHeapify_of_lt {a : Array Nat} {i hs p : Nat} (hle : hs ≤ a.size) (hp : p < i) :
    (maxHeapify a i hs).getD p 0 = a.getD p 0 :=
  getD_heapifyGo_of_lt hs a i hs p hle hp

/-! ## The root of a max-heap is the maximum -/

theorem IsHeap_getD_le_root {a : Array Nat} {hs : Nat} (h : IsHeap a hs) {j : Nat}
    (hj : j < hs) : a.getD j 0 ≤ a.getD 0 0 := by
  have key : ∀ j, j < hs → a.getD j 0 ≤ a.getD 0 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases h0 : j = 0
      · rw [h0]
      · have hjp : parent j < j := parent_lt j (Nat.pos_of_ne_zero h0)
        have hjp' : parent j < hs := Nat.lt_of_lt_of_le hjp hj.le
        have hH : HeapAt a hs (parent j) := h (parent j) (Nat.zero_le _) hjp'
        have hrec : a.getD (parent j) 0 ≤ a.getD 0 0 := ih (parent j) hjp hjp'
        rcases eq_left_parent_or_eq_right_parent j (Nat.pos_of_ne_zero h0) with (e | e)
        · have hlt : left (parent j) < hs := by rw [← e]; exact hj
          have hle : a.getD j 0 ≤ a.getD (parent j) 0 := by
            have := hH.1 hlt
            rwa [← e] at this
          exact Nat.le_trans hle hrec
        · have hlt : right (parent j) < hs := by rw [← e]; exact hj
          have hle : a.getD j 0 ≤ a.getD (parent j) 0 := by
            have := hH.2 hlt
            rwa [← e] at this
          exact Nat.le_trans hle hrec
  exact key j hj

/-! ## `BUILD-MAX-HEAP` (CLRS 6.3) -/


theorem size_buildLoop (k : Nat) : ∀ (a : Array Nat) (hs : Nat),
    (buildLoop k a hs).size = a.size := by
  induction k with
  | zero => intro a hs; rfl
  | succ k ih =>
    intro a hs
    show (buildLoop k (maxHeapify a k hs) hs).size = a.size
    rw [ih, size_maxHeapify]

theorem perm_buildLoop (k : Nat) : ∀ (a : Array Nat) (hs : Nat),
    Array.Perm (buildLoop k a hs) a := by
  induction k with
  | zero => intro a hs; exact Array.Perm.refl _
  | succ k ih =>
    intro a hs
    show Array.Perm (buildLoop k (maxHeapify a k hs) hs) a
    exact Array.Perm.trans (ih _ _) (perm_maxHeapify _ _ _)

theorem buildLoop_IsHeap (k : Nat) : ∀ (a : Array Nat) (hs : Nat),
    hs ≤ a.size →
    (∀ j, k ≤ j → j < hs → HeapAt a hs j) →
    (∀ j, j < hs → HeapAt (buildLoop k a hs) hs j) := by
  induction k with
  | zero => intro a hs _ h j hj; exact h j (Nat.zero_le j) hj
  | succ k ih =>
    intro a hs hle h
    have hcond : ∀ j, k ≤ j → j < hs → HeapAt (maxHeapify a k hs) hs j :=
      maxHeapify_HeapAt hle (fun j' hj' hj's => h j' (by omega) hj's)
    exact ih (maxHeapify a k hs) hs (by rw [size_maxHeapify]; exact hle) hcond


theorem size_buildMaxHeap (a : Array Nat) : (buildMaxHeap a).size = a.size := by
  simp only [buildMaxHeap]
  split
  · rfl
  · exact size_buildLoop _ _ _

theorem perm_buildMaxHeap (a : Array Nat) : Array.Perm (buildMaxHeap a) a := by
  simp only [buildMaxHeap]
  split
  · exact Array.Perm.refl _
  · exact perm_buildLoop _ _ _

theorem buildMaxHeap_IsHeap (a : Array Nat) : IsHeap (buildMaxHeap a) a.size := by
  by_cases h : a.size ≤ 1
  · have e : buildMaxHeap a = a := by simp only [buildMaxHeap, if_pos h]
    rw [e, IsHeap, IsHeapBelow]
    intro j _ hj
    exact IsHeap_of_le_one h j (Nat.zero_le j) hj
  · have e : buildMaxHeap a = buildLoop (parent (a.size - 1) + 1) a a.size := by
      simp only [buildMaxHeap, if_neg h]
    rw [e, IsHeap, IsHeapBelow]
    intro j _ hj
    exact buildLoop_IsHeap (parent (a.size - 1) + 1) a (a.size) (Nat.le_refl _)
      (fun j' hj' hj's => HeapAt_of_parent_lt hj's (by omega)) j hj

/-! ## The extraction phase of HEAPSORT (CLRS 6.4) -/


theorem extractLoop_zero (a : Array Nat) : extractLoop 0 a = a := rfl

theorem extractLoop_succ (k : Nat) (a : Array Nat) :
    extractLoop (k + 1) a =
      extractLoop k (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)) := rfl

theorem size_extractLoop (k : Nat) (a : Array Nat) : (extractLoop k a).size = a.size := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [extractLoop_succ, ih, size_maxHeapify, Array.size_swapIfInBounds]

theorem perm_extractLoop (k : Nat) (a : Array Nat) : Array.Perm (extractLoop k a) a := by
  induction k generalizing a with
  | zero => exact Array.Perm.refl _
  | succ k ih =>
    rw [extractLoop_succ]
    exact Array.Perm.trans (ih (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)))
      (Array.Perm.trans (perm_maxHeapify _ _ _) (perm_swapIfInBounds _ _ _))

theorem extractLoop_sorted (k : Nat) : ∀ (a : Array Nat) (n : Nat),
    a.size = n →
    k + 1 ≤ n →
    IsHeap a (k + 1) →
    (∀ j, k < j → j < n → ∀ m, m ≤ k → a.getD m 0 ≤ a.getD j 0) →
    (∀ j₁ j₂, k < j₁ → j₁ < j₂ → j₂ < n → a.getD j₁ 0 ≤ a.getD j₂ 0) →
    ∀ i j, i ≤ j → j < n → (extractLoop k a).getD i 0 ≤ (extractLoop k a).getD j 0 := by
  induction k with
  | zero =>
    intro a n hsize hk hheap hsuf hsort i j hij hjn
    by_cases hi : i = 0
    · rw [hi]
      by_cases hj : j = 0
      · rw [hj]
      · exact hsuf j (by omega) hjn 0 (Nat.zero_le 0)
    · by_cases hij : i = j
      · rw [hij]
      · exact hsort i j (by omega) (by omega) hjn
  | succ k ih =>
    intro a n hsize hk hheap hsuf hsort
    rw [extractLoop_succ]
    have h0 : 0 < a.size := by rw [hsize]; omega
    have hk1 : k + 1 < a.size := by rw [hsize]; omega
    have hsizec : (a.swapIfInBounds 0 (k + 1)).size = a.size := Array.size_swapIfInBounds
    have hlec : k + 1 ≤ (a.swapIfInBounds 0 (k + 1)).size := by rw [hsizec]; omega
    have hc0 : (a.swapIfInBounds 0 (k + 1)).getD 0 0 = a.getD (k + 1) 0 := by
      rw [getD_swapIfInBounds h0 hk1, if_pos rfl]
    have hck1 : (a.swapIfInBounds 0 (k + 1)).getD (k + 1) 0 = a.getD 0 0 := by
      rw [getD_swapIfInBounds h0 hk1, if_neg (by omega), if_pos rfl]
    have hcother : ∀ p, p ≠ 0 → p ≠ k + 1 →
        (a.swapIfInBounds 0 (k + 1)).getD p 0 = a.getD p 0 := by
      intro p hp1 hp2
      exact getD_swapIfInBounds_ne h0 hk1 hp1 hp2
    have hroot : ∀ m, m < k + 2 → a.getD m 0 ≤ a.getD 0 0 := fun m hm =>
      IsHeap_getD_le_root hheap hm
    have hboundc : ∀ m, m ≤ k → (a.swapIfInBounds 0 (k + 1)).getD m 0 ≤ a.getD 0 0 := by
      intro m hm
      by_cases h1 : m = 0
      · rw [h1, hc0]
        exact hroot (k + 1) (by omega)
      · rw [hcother m h1 (by omega)]
        exact hroot m (by omega)
    have hcondc : ∀ j, 0 < j → j < k + 1 →
        HeapAt (a.swapIfInBounds 0 (k + 1)) (k + 1) j := by
      intro j hj0 hj
      have hH : HeapAt a (k + 2) j := hheap j (Nat.zero_le j) (by omega)
      constructor
      · intro hl
        have hl2 : left j < k + 2 := by omega
        have := hH.1 hl2
        rwa [← hcother (left j) (by have := i_lt_left j; omega) (by omega),
          ← hcother j (by omega) (by omega)] at this
      · intro hr
        have hr2 : right j < k + 2 := by omega
        have := hH.2 hr2
        rwa [← hcother (right j) (by have := i_lt_right j; omega) (by omega),
          ← hcother j (by omega) (by omega)] at this
    have hheapb : IsHeap (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)) (k + 1) :=
      maxHeapify_HeapAt hlec hcondc
    have hsizeb : (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)).size = n := by
      rw [size_maxHeapify, hsizec, hsize]
    have hboundb : ∀ m, m ≤ k →
        (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)).getD m 0 ≤ a.getD 0 0 :=
      fun m hm => maxHeapify_le hlec (fun m' _ hm' => hboundc m' (by omega)) m
        (Nat.zero_le m) (by omega)
    have hbge : ∀ p, k + 1 ≤ p →
        (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)).getD p 0 =
        (a.swapIfInBounds 0 (k + 1)).getD p 0 :=
      fun p hp => getD_maxHeapify_of_ge hlec hp
    have hsuf' : ∀ j, k < j → j < n → ∀ m, m ≤ k →
        (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)).getD m 0 ≤
        (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)).getD j 0 := by
      intro j hj hjn m hm
      by_cases hj1 : j = k + 1
      · rw [hj1, hbge (k + 1) (Nat.le_refl _), hck1]
        exact hboundb m hm
      · have hj2 : k + 1 < j := by omega
        rw [hbge j (by omega), hcother j (by omega) (by omega)]
        exact Nat.le_trans (hboundb m hm) (hsuf j hj2 hjn 0 (by omega))
    have hsort' : ∀ j₁ j₂, k < j₁ → j₁ < j₂ → j₂ < n →
        (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)).getD j₁ 0 ≤
        (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)).getD j₂ 0 := by
      intro j₁ j₂ hj1 hj12 hj2n
      by_cases he : j₁ = k + 1
      · rw [he, hbge (k + 1) (Nat.le_refl _), hck1,
          hbge j₂ (by omega), hcother j₂ (by omega) (by omega)]
        exact hsuf j₂ (by omega) hj2n 0 (by omega)
      · have hj1' : k + 1 < j₁ := by omega
        rw [hbge j₁ (by omega), hcother j₁ (by omega) (by omega),
          hbge j₂ (by omega), hcother j₂ (by omega) (by omega)]
        exact hsort j₁ j₂ hj1' hj12 hj2n
    exact ih (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1)) n hsizeb (by omega)
      hheapb hsuf' hsort'

/-! ## HEAPSORT -/




theorem size_extractSort (a : Array Nat) : (extractSort a).size = a.size := by
  simp only [extractSort]
  split
  · rfl
  · exact size_extractLoop _ _

theorem size_heapsortArr (a : Array Nat) : (heapsortArr a).size = a.size := by
  show (extractSort (buildMaxHeap a)).size = a.size
  rw [size_extractSort, size_buildMaxHeap]

theorem size_heapsort_size (arr : List Nat) : (heapsortArr arr.toArray).size = arr.length := by
  rw [size_heapsortArr, List.size_toArray]

theorem perm_extractSort (a : Array Nat) : Array.Perm (extractSort a) a := by
  simp only [extractSort]
  split
  · exact Array.Perm.refl _
  · exact perm_extractLoop _ _

theorem perm_heapsortArr (a : Array Nat) : Array.Perm (heapsortArr a) a :=
  Array.Perm.trans (perm_extractSort (buildMaxHeap a)) (perm_buildMaxHeap a)

theorem heapsortArr_sorted_getD (a : Array Nat) : ∀ i j, i ≤ j → j < a.size →
    (heapsortArr a).getD i 0 ≤ (heapsortArr a).getD j 0 := by
  show ∀ i j, i ≤ j → j < a.size →
    (extractSort (buildMaxHeap a)).getD i 0 ≤ (extractSort (buildMaxHeap a)).getD j 0
  set b := buildMaxHeap a with hb
  have hsizeb : b.size = a.size := by rw [hb, size_buildMaxHeap]
  have hheapb : IsHeap b b.size := by
    rw [hb, size_buildMaxHeap]
    exact buildMaxHeap_IsHeap a
  intro i j hij hj
  have hj' : j < b.size := by rwa [← hsizeb] at hj
  by_cases h : b.size ≤ 1
  · have e : extractSort b = b := by simp only [extractSort, if_pos h]
    rw [e]
    have hz : i = 0 ∧ j = 0 := by omega
    rw [hz.1, hz.2]
  · have e : extractSort b = extractLoop (b.size - 1) b := by
      simp only [extractSort, if_neg h]
    rw [e]
    have hsz : b.size - 1 + 1 = b.size := by omega
    have hheap' : IsHeap b (b.size - 1 + 1) := by rw [hsz]; exact hheapb
    exact extractLoop_sorted (b.size - 1) b b.size rfl (by omega) hheap'
      (fun j hj₁ hj₂ m hm => absurd hj₁ (by omega))
      (fun j₁ j₂ hj₁ hj₁₂ hj₂ => absurd hj₁ (by omega)) i j hij hj'

theorem sorted_of_getD {a : Array Nat}
    (h : ∀ i j, i ≤ j → j < a.size → a.getD i 0 ≤ a.getD j 0) :
    Sorted (· ≤ ·) a.toList := by
  rw [Sorted, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < a.size := by rwa [Array.length_toList] at hi
  have hj' : j < a.size := by rwa [Array.length_toList] at hj
  have h1 : a.toList[i] = a.getD i 0 := by
    rw [Array.getElem_toList hi, ← getD_eq_getElem hi']
  have h2 : a.toList[j] = a.getD j 0 := by
    rw [Array.getElem_toList hj, ← getD_eq_getElem hj']
  rw [h1, h2]
  exact h i j (by omega) hj'

theorem heapsortArr_sorted (a : Array Nat) : Sorted (· ≤ ·) (heapsortArr a).toList :=
  sorted_of_getD (fun i j hij hj =>
    heapsortArr_sorted_getD a i j hij (by rwa [size_heapsortArr] at hj))

theorem heapsort_sorted (arr : List Nat) : Sorted (· ≤ ·) (heapsort arr) :=
  heapsortArr_sorted arr.toArray

theorem heapsort_perm (arr : List Nat) : List.Perm (heapsort arr) arr := by
  have h := perm_heapsortArr arr.toArray
  rw [Array.perm_iff_toList_perm] at h
  rw [List.toList_toArray] at h
  exact h

theorem heapsort_length (arr : List Nat) : (heapsort arr).length = arr.length := by
  have h := size_heapsortArr arr.toArray
  simp only [heapsort, Array.length_toList] at h ⊢
  rw [h, List.size_toArray]

/-! ## Properties of the implementation -/

theorem parent_left (i : Nat) : parent (left i) = i := by
  rw [parent_eq (left i) (by have := i_lt_left i; omega), left]
  omega

theorem parent_right (i : Nat) : parent (right i) = i := by
  rw [parent_eq (right i) (by have := i_lt_right i; omega), right]
  omega

/-- Property: `parent` is the 0-based heap parent of the Python program. -/
def parent_prop : Prop :=
  parent 0 = 0 ∧ (∀ i : Nat, parent i ≤ i) ∧ (∀ i : Nat, 0 < i → parent i < i) ∧
    (∀ i : Nat, parent (left i) = i) ∧ (∀ i : Nat, parent (right i) = i) ∧
    (∀ i j : Nat, i ≤ j → parent i ≤ parent j)

theorem parent_thm : parent_prop :=
  ⟨parent_zero, parent_le, parent_lt, parent_left, parent_right, fun _ _ h => parent_mono h⟩

/-- Property: `left`/`right` are the 0-based child indices of the Python program. -/
def child_prop : Prop :=
  ∀ i : Nat, left i = 2 * i + 1 ∧ right i = 2 * i + 2 ∧ i < left i ∧ i < right i ∧
    left i < right i

theorem child_thm : child_prop :=
  fun i => ⟨left_def i, right_def i, i_lt_left i, i_lt_right i, left_lt_right i⟩

/-- Property: `MAX-HEAPIF` preserves the array size. -/
def maxHeapify_size_prop : Prop :=
  ∀ (a : Array Nat) (i hs : Nat), (maxHeapify a i hs).size = a.size

theorem maxHeapify_size_thm : maxHeapify_size_prop := size_maxHeapify

/-- Property: `MAX-HEAPIF` only permutes the entries (Python `_swap`). -/
def maxHeapify_perm_prop : Prop :=
  ∀ (a : Array Nat) (i hs : Nat), Array.Perm (maxHeapify a i hs) a

theorem maxHeapify_perm_thm : maxHeapify_perm_prop := perm_maxHeapify

/-- Property: `MAX-HEAPIF` restores the max-heap condition at and below `i`
(CLRS Lemma 6.2). -/
def maxHeapify_heap_prop : Prop :=
  ∀ (a : Array Nat) (i hs : Nat), hs ≤ a.size →
    (∀ j, i < j → j < hs → HeapAt a hs j) → IsHeapBelow (maxHeapify a i hs) hs i

theorem maxHeapify_heap_thm : maxHeapify_heap_prop :=
  fun _a _i _hs hle hcond => maxHeapify_HeapAt hle hcond

/-- Property: `MAX-HEAPIF` never raises an entry above the bound valid before the call. -/
def maxHeapify_le_prop : Prop :=
  ∀ (a : Array Nat) (i hs B : Nat), hs ≤ a.size →
    (∀ m, i ≤ m → m < hs → a.getD m 0 ≤ B) →
    (∀ m, i ≤ m → m < hs → (maxHeapify a i hs).getD m 0 ≤ B)

theorem maxHeapify_le_thm : maxHeapify_le_prop :=
  fun _a _i _hs _B hle h => maxHeapify_le hle h

/-- Property: `BUILD-MAX-HEAP` preserves size and entries. -/
def buildMaxHeap_size_prop : Prop := ∀ a : Array Nat, (buildMaxHeap a).size = a.size

theorem buildMaxHeap_size_thm : buildMaxHeap_size_prop := size_buildMaxHeap

def buildMaxHeap_perm_prop : Prop := ∀ a : Array Nat, Array.Perm (buildMaxHeap a) a

theorem buildMaxHeap_perm_thm : buildMaxHeap_perm_prop := perm_buildMaxHeap

/-- Property: `BUILD-MAX-HEAP` produces a max-heap (CLRS Lemma 6.3). -/
def buildMaxHeap_heap_prop : Prop := ∀ a : Array Nat, IsHeap (buildMaxHeap a) a.size

theorem buildMaxHeap_heap_thm : buildMaxHeap_heap_prop := buildMaxHeap_IsHeap

/-- Property: the root of a max-heap dominates the whole heap. -/
def heap_root_max_prop : Prop :=
  ∀ (a : Array Nat) (hs j : Nat), IsHeap a hs → j < hs → a.getD j 0 ≤ a.getD 0 0

theorem heap_root_max_thm : heap_root_max_prop :=
  fun _a _hs _j h hj => IsHeap_getD_le_root h hj

/-- Property: `heapsort` preserves the length (Python `assert len(out) == len(arr)`). -/
def heapsort_length_prop : Prop := ∀ arr : List Nat, (heapsort arr).length = arr.length

theorem heapsort_length_thm : heapsort_length_prop := heapsort_length

/-- Property: `heapsort` returns a permutation of its input
(Python `assert sorted(out) == sorted(arr)`). -/
def heapsort_perm_prop : Prop := ∀ arr : List Nat, List.Perm (heapsort arr) arr

theorem heapsort_perm_thm : heapsort_perm_prop := heapsort_perm

/-- Property: `heapsort` returns an ascending list (Python `assert out == sorted(arr)`). -/
def heapsort_sorted_prop : Prop := ∀ arr : List Nat, Sorted (· ≤ ·) (heapsort arr)

theorem heapsort_sorted_thm : heapsort_sorted_prop := heapsort_sorted

/-- Property: sorting an already sorted list is idempotent. -/
def heapsort_idempotent_prop : Prop :=
  ∀ arr : List Nat, heapsort (heapsort arr) = heapsort arr

theorem heapsort_idempotent_thm : heapsort_idempotent_prop :=
  fun arr => List.eq_of_perm_of_sorted (heapsort_perm (heapsort arr))
    (heapsort_sorted (heapsort arr)) (heapsort_sorted arr)

/-- Property: the guarded `Int` entry point sorts whenever the pre-condition holds. -/
def heapsortChecked_prop : Prop :=
  ∀ arr : List Int, PreInt arr →
    ∃ out : List Nat, heapsortChecked arr = some out ∧ Sorted (· ≤ ·) out ∧
      List.Perm (out.map Int.ofNat) arr ∧ out.length = arr.length

theorem heapsortChecked_thm : heapsortChecked_prop := by
  intro arr h
  refine ⟨heapsort (arr.map Int.toNat), heapsortChecked_some h, heapsort_sorted _, ?_, ?_⟩
  · have h2 : List.Perm ((heapsort (arr.map Int.toNat)).map Int.ofNat)
      ((arr.map Int.toNat).map Int.ofNat) := (heapsort_perm _).map Int.ofNat
    rw [map_toNat_ofNat arr h] at h2
    exact h2
  · rw [heapsort_length, List.length_map]

/-- Property (specification form): `heapsort arr` is *the* ascending permutation of `arr`;
any other ascending permutation of `arr` coincides with it. -/
def heapsort_spec_prop : Prop :=
  ∀ (arr out : List Nat), Sorted (· ≤ ·) out → List.Perm out arr → out = heapsort arr

theorem heapsort_spec_thm : heapsort_spec_prop :=
  fun arr _out hsort hperm =>
    List.eq_of_perm_of_sorted (hperm.trans (heapsort_perm arr).symm) hsort (heapsort_sorted arr)

/-- Property: `heapsort` preserves membership (Python `assert sorted(out) == sorted(arr)`). -/
def heapsort_mem_prop : Prop := ∀ (arr : List Nat) (x : Nat), x ∈ heapsort arr ↔ x ∈ arr

theorem heapsort_mem_thm : heapsort_mem_prop :=
  fun arr _x => List.Perm.mem_iff (heapsort_perm arr)

/-! ## Post-condition -/

/-- The post-condition of the Python `heapsort`: the returned list is sorted in ascending
order, is a permutation of the input, and has the same length. -/
def Post_prop (arr out : List Nat) : Prop :=
  Sorted (· ≤ ·) out ∧ List.Perm out arr ∧ out.length = arr.length

instance (arr out : List Nat) : Decidable (Post_prop arr out) :=
  decidable_of_iff
    (Sorted (· ≤ ·) out ∧ List.Perm out arr ∧ out.length = arr.length) (Iff.rfl)

/-! ## Property-based tests -/

/-- Executable Boolean form of the max-heap predicate, used by the bounded PBTs below. -/
def isHeapBool (a : Array Nat) (hs : Nat) : Bool :=
  (List.range hs).all (fun j =>
    (decide (hs ≤ left j) || decide (a.getD (left j) 0 ≤ a.getD j 0)) &&
    (decide (hs ≤ right j) || decide (a.getD (right j) 0 ≤ a.getD j 0)))

-- Randomized PBTs (Plausible).  Each prints "Unable to find a counter-example"; the file
-- fails to compile if Plausible finds one.
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).length = xs.length)
#eval Plausible.Testable.check (∀ xs : List Nat, Sorted (· ≤ ·) (heapsort xs))
#eval Plausible.Testable.check (∀ xs : List Nat, List.Perm (heapsort xs) xs)
#eval Plausible.Testable.check (∀ xs : List Nat, heapsort (heapsort xs) = heapsort xs)
#eval Plausible.Testable.check (∀ xs : List Nat, Post_prop xs (heapsort xs))
#eval Plausible.Testable.check
  (∀ i : Nat, parent i ≤ i ∧ parent (left i) = i ∧ parent (right i) = i)
#eval Plausible.Testable.check (∀ i : Nat, i < left i ∧ i < right i ∧ left i < right i)
#eval Plausible.Testable.check
  (∀ xs : List Nat, heapsortChecked (xs.map Int.ofNat) = some (heapsort xs))

-- Bounded PBTs: exhaustive checks over small inputs.
example : (List.range 30).all (fun n => heapsort (List.range n) = List.range n) = true := by
  native_decide

example : (List.range 25).all (fun n =>
    let xs := (List.range n).map (fun i => (i * 7 + 3) % 11)
    heapsort xs = xs.mergeSort (· ≤ ·)) = true := by native_decide

example : (List.range 20).all (fun n =>
    isHeapBool (buildMaxHeap (((List.range n).map (fun i => (i * i + 3) % 7)).toArray)) n) =
      true := by native_decide

example : (List.range 20).all (fun n =>
    let a := ((List.range n).map (fun i => (i * 5 + 1) % 9)).toArray
    (maxHeapify a 0 n).toList.mergeSort (· ≤ ·) = a.toList.mergeSort (· ≤ ·)) = true := by
  native_decide

example : (List.range 15).all (fun n =>
    let xs := (List.range n).map (fun i => (i * 3) % 7)
    decide (Post_prop xs (heapsort xs))) = true := by native_decide

example : (List.range 15).all (fun n =>
    let xs := (List.range n).map (fun i => (i * 3) % 7)
    heapsortChecked (xs.map Int.ofNat) = some (heapsort xs)) = true := by native_decide

example : heapsortChecked [1, -1] = none := by native_decide

example : heapsortChecked [3, 1, 2] = some [1, 2, 3] := by native_decide

#eval Plausible.Testable.check
  (∀ (xs : List Nat) (x : Nat), (x ∈ heapsort xs) = (x ∈ xs))

example : (List.range 20).all (fun n =>
    let xs := (List.range n).map (fun i => (i * 7 + 5) % 13)
    decide (Post_prop xs (heapsort xs)) && decide (heapsort xs = xs.mergeSort)) = true := by
  native_decide

-- Bounded PBT for `maxHeapify_heap_prop`: after lowering the root of a heap, one call to
-- `maxHeapify` restores the heap condition everywhere.
example : (List.range 20).all (fun n =>
    let a := ((List.range n).map (fun i => (i * i + 3) % 7)).toArray
    let h := (buildMaxHeap a).setIfInBounds 0 0
    isHeapBool (maxHeapify h 0 n) n) = true := by native_decide

-- Bounded PBT for `maxHeapify_size_prop` and `maxHeapify_le_prop`.
example : (List.range 20).all (fun n =>
    let a := ((List.range n).map (fun i => (i * 3 + 1) % 7)).toArray
    decide ((maxHeapify a 0 n).size = a.size) &&
      (List.range n).all (fun m => decide ((maxHeapify a 0 n).getD m 0 ≤ a.foldl max 0))) =
    true := by native_decide

/-! ## Correctness: `Pre → Post` -/

theorem heapsort_correct (arr : List Nat) (_h : Pre arr) : Post_prop arr (heapsort arr) :=
  ⟨heapsort_sorted arr, heapsort_perm arr, heapsort_length arr⟩

theorem heapsortChecked_correct (arr : List Int) (h : PreInt arr) :
    Post_prop (arr.map Int.toNat) (heapsort (arr.map Int.toNat)) ∧
      heapsortChecked arr = some (heapsort (arr.map Int.toNat)) :=
  ⟨heapsort_correct _ (Pre_holds _), heapsortChecked_some h⟩

/-! ## Imperative implementation (`Id.run do` with mutable state) -/

/-- One sift-down step of `MAX-HEAPIF` on the mutable state `(array, current index)`. -/
def heapifyStep (hs : Nat) (p : Array Nat × Nat) : Array Nat × Nat :=
  let arr := p.1
  let k := p.2
  let m := largestIdx arr k hs
  (if m = k then arr else arr.swapIfInBounds k m, if m = k then k else m)

/-- `fuel` sift-down steps, tracking the array and the current index simultaneously. -/
def heapifyPairGo : Nat → Array Nat → Nat → Nat → Array Nat × Nat
  | 0, a, i, _ => (a, i)
  | fuel + 1, a, i, hs =>
    let m := largestIdx a i hs
    if m = i then (a, i) else heapifyPairGo fuel (a.swapIfInBounds i m) m hs

theorem heapifyPairGo_zero (a : Array Nat) (i hs : Nat) :
    heapifyPairGo 0 a i hs = (a, i) := rfl

theorem heapifyPairGo_succ (fuel : Nat) (a : Array Nat) (i hs : Nat) :
    heapifyPairGo (fuel + 1) a i hs =
      if largestIdx a i hs = i then (a, i)
      else heapifyPairGo fuel (a.swapIfInBounds i (largestIdx a i hs))
        (largestIdx a i hs) hs := rfl

theorem heapifyPairGo_fst (fuel : Nat) : ∀ (a : Array Nat) (i hs : Nat),
    (heapifyPairGo fuel a i hs).1 = heapifyGo fuel a i hs := by
  induction fuel with
  | zero => intro a i hs; rfl
  | succ fuel ih =>
    intro a i hs
    rw [heapifyPairGo_succ, heapifyGo_succ]
    by_cases hi : i < hs
    · rw [if_pos hi]
      by_cases heq : largestIdx a i hs = i
      · rw [if_pos heq, if_pos heq]
      · rw [if_neg heq, if_neg heq, ih]
    · rw [if_neg hi]
      have hm : largestIdx a i hs = i := largestIdx_of_not_lt hi
      rw [hm]
      simp only [if_pos]

theorem heapifyStep_succ (hs : Nat) : ∀ (n : Nat) (a : Array Nat) (i : Nat),
    heapifyStep hs (heapifyPairGo n a i hs) = heapifyPairGo (n + 1) a i hs := by
  intro n
  induction n with
  | zero =>
    intro a i
    by_cases heq : largestIdx a i hs = i
    · simp [heapifyStep, heapifyPairGo_succ, heapifyPairGo_zero, heq]
    · simp [heapifyStep, heapifyPairGo_succ, heapifyPairGo_zero, heq]
  | succ n ih =>
    intro a i
    by_cases heq : largestIdx a i hs = i
    · simp only [heapifyPairGo_succ, if_pos heq]
      simp [heapifyStep, heq]
    · simp only [heapifyPairGo_succ, if_neg heq]
      exact ih (a.swapIfInBounds i (largestIdx a i hs)) (largestIdx a i hs)

/-- The `for` loop of the imperative `MAX-HEAPIF` expressed as a fold. -/
def heapifyFold (n : Nat) (a : Array Nat) (i hs : Nat) : Array Nat :=
  ((List.range n).foldl (fun p _ => heapifyStep hs p) (a, i)).1

theorem heapifyFold_pair (n : Nat) (a : Array Nat) (i hs : Nat) :
    (List.range n).foldl (fun p _ => heapifyStep hs p) (a, i) = heapifyPairGo n a i hs := by
  induction n generalizing a i with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      heapifyStep_succ]

theorem heapifyFold_eq (n : Nat) (a : Array Nat) (i hs : Nat) :
    heapifyFold n a i hs = heapifyGo n a i hs := by
  simp only [heapifyFold, heapifyFold_pair, heapifyPairGo_fst]

/-- Imperative `MAX-HEAPIF` (Python `max_heapify`): a loop with mutable array and index. -/
def maxHeapifyImp (a : Array Nat) (i hs : Nat) : Array Nat := Id.run do
  -- mutable state: the array being sifted together with the current index
  let mut s := (a, i)
  for _ in List.range hs do
    let arr := s.1
    let k := s.2
    let m := largestIdx arr k hs
    s := (if m = k then arr else arr.swapIfInBounds k m, if m = k then k else m)
  return s.1

theorem maxHeapifyImp_fold (a : Array Nat) (i hs : Nat) :
    maxHeapifyImp a i hs = heapifyFold hs a i hs := by
  simp [maxHeapifyImp, heapifyFold, heapifyStep]

theorem maxHeapifyImp_eq (a : Array Nat) (i hs : Nat) :
    maxHeapifyImp a i hs = maxHeapify a i hs := by
  rw [maxHeapifyImp_fold, heapifyFold_eq, maxHeapify]

theorem buildLoop_fold (k : Nat) (a : Array Nat) (hs : Nat) :
    List.foldr (fun j arr => maxHeapify arr j hs) a (List.range k) = buildLoop k a hs := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih]
    rfl

theorem extractLoop_fold (k : Nat) (a : Array Nat) :
    List.foldr (fun j arr => maxHeapify (arr.swapIfInBounds 0 (j + 1)) 0 (j + 1)) a
      (List.range k) = extractLoop k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih]
    rfl

/-- Imperative `BUILD-MAX-HEAP` (Python `build_max_heap`). -/
def buildMaxHeapImp (a : Array Nat) : Array Nat := Id.run do
  let mut arr := a
  let n := arr.size
  if n ≤ 1 then return arr
  for k in (List.range (parent (n - 1) + 1)).reverse do
    arr := maxHeapifyImp arr k n
  return arr

theorem buildMaxHeapImp_eq (a : Array Nat) : buildMaxHeapImp a = buildMaxHeap a := by
  simp [buildMaxHeapImp, buildMaxHeap, maxHeapifyImp_eq, buildLoop_fold]; rfl

/-- Imperative extraction phase of `HEAPSORT`. -/
def extractSortImp (a : Array Nat) : Array Nat := Id.run do
  let mut arr := a
  let n := arr.size
  if n ≤ 1 then return arr
  for j in (List.range (n - 1)).reverse do
    let arr1 := arr.swapIfInBounds 0 (j + 1)
    arr := maxHeapifyImp arr1 0 (j + 1)
  return arr

theorem extractSortImp_eq (a : Array Nat) : extractSortImp a = extractSort a := by
  simp [extractSortImp, extractSort, maxHeapifyImp_eq, extractLoop_fold]; rfl

/-- Imperative `HEAPSORT` (Python `heapsort`), written with `Id.run do` and mutable arrays. -/
def heapsortImp (arr : List Nat) : List Nat := Id.run do
  let mut a := arr.toArray
  a := buildMaxHeapImp a
  a := extractSortImp a
  return a.toList

theorem heapsortImp_eq (arr : List Nat) : heapsortImp arr = heapsort arr := by
  simp [heapsortImp, heapsort, heapsortArr, buildMaxHeapImp_eq, extractSortImp_eq]

/-! ## Imperative tests and functional/imperative equivalence -/

#eval heapsortImp [3, 1, 2]
#eval heapsortImp [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval maxHeapifyImp #[1, 3, 2] 0 3
#eval buildMaxHeapImp #[1, 2, 3]
#eval extractSortImp #[3, 2, 1]

example : heapsortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsortImp [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsortImp [] = [] := by native_decide
example : heapsortImp [42] = [42] := by native_decide
example : heapsortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapsortImp [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsortImp [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : maxHeapifyImp #[1, 3, 2] 0 3 = #[3, 1, 2] := by native_decide
example : buildMaxHeapImp #[1, 2, 3] = #[3, 2, 1] := by native_decide
example : buildMaxHeapImp #[5, 13, 2, 25, 7, 17, 20, 8, 4] =
    #[25, 13, 20, 8, 7, 17, 2, 5, 4] := by native_decide
example : extractSortImp #[3, 2, 1] = #[1, 2, 3] := by native_decide

-- Bounded PBT: the imperative implementation agrees with the functional one.
example : (List.range 12).all (fun n =>
    let xs := (List.range n).map (fun i => (i * 11) % 13)
    heapsortImp xs = heapsort xs) = true := by native_decide

example : (List.range 12).all (fun n =>
    let xs := (List.range n).map (fun i => (i * 11) % 13)
    isHeapBool (buildMaxHeapImp xs.toArray) n) = true := by native_decide

-- Randomized PBT for the equivalence property.
#eval Plausible.Testable.check (∀ xs : List Nat, heapsortImp xs = heapsort xs)

/-- Property: the imperative `MAX-HEAPIF` computes the same array as the functional one. -/
def maxHeapifyImp_eq_prop : Prop :=
  ∀ (a : Array Nat) (i hs : Nat), maxHeapifyImp a i hs = maxHeapify a i hs

theorem maxHeapifyImp_eq_thm : maxHeapifyImp_eq_prop := maxHeapifyImp_eq

/-- Property: the imperative `BUILD-MAX-HEAP` computes the same array. -/
def buildMaxHeapImp_eq_prop : Prop := ∀ a : Array Nat, buildMaxHeapImp a = buildMaxHeap a

theorem buildMaxHeapImp_eq_thm : buildMaxHeapImp_eq_prop := buildMaxHeapImp_eq

/-- Property: the imperative extraction phase computes the same array. -/
def extractSortImp_eq_prop : Prop := ∀ a : Array Nat, extractSortImp a = extractSort a

theorem extractSortImp_eq_thm : extractSortImp_eq_prop := extractSortImp_eq

/-- Property: the imperative `HEAPSORT` computes the same list as the functional one. -/
def heapsortImp_eq_prop : Prop := ∀ arr : List Nat, heapsortImp arr = heapsort arr

theorem heapsortImp_eq_thm : heapsortImp_eq_prop := heapsortImp_eq

end heapsort_algorithm
