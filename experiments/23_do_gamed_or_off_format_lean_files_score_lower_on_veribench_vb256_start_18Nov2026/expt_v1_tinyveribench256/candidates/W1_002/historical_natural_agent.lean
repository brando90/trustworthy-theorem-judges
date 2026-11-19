import Mathlib
namespace Agent

/-!
# BUILD-MAX-HEAP and BUILD-MIN-HEAP (CLRS 6.3)

Lean 4 translation of a Python module implementing the CLRS heap primitives on
arrays of natural numbers represented as `List Nat`:

* `parent`, `left`, `right` -- index arithmetic on the implicit binary tree;
* `maxHeapify` / `minHeapify` -- the sift-down loop (`MAX-HEAPIFY`, CLRS 6.2);
* `isMaxHeap` / `isMinHeap` -- the heap-property checkers;
* `buildMaxHeap` / `buildMinHeap` -- `BUILD-MAX-HEAP` (CLRS 6.3), which calls
  `maxHeapify` on the indices `n/2 - 1, ..., 0` in decreasing order.

The Python code validates that every element is a natural number (rejecting
negative integers with a `ValueError`); in Lean that check is discharged by the
type `List Nat`, which is what `Pre` records.

Out-of-range reads use the default value `0` (`List.getD`), and `swap` is the
identity when an index is out of range; under the pre-condition
`heapSize ≤ arr.length` these situations never occur, exactly as in Python where
they would raise `IndexError`.

The sift-down `while True` loop is modelled with a fuel argument; `arr.length + 1`
is always enough fuel because the current index at least doubles on every
iteration.
-/

namespace heapsort_build_heap

/-! ## Functional implementation -/

/-- Index of the parent of `i` (Python: `0 if i == 0 else (i - 1) // 2`). -/
def parent (i : Nat) : Nat := if i = 0 then 0 else (i - 1) / 2

/-- Index of the left child of `i`. -/
def left (i : Nat) : Nat := 2 * i + 1

/-- Index of the right child of `i`. -/
def right (i : Nat) : Nat := 2 * i + 2

/-- Exchange the entries at positions `i` and `j`; the identity if an index is
out of range (in Python such an access raises `IndexError`). -/
def swap (l : List Nat) (i j : Nat) : List Nat :=
  if i < l.length ∧ j < l.length then (l.set i (l.getD j 0)).set j (l.getD i 0) else l

/-- The index of the largest of `arr[i]` and its in-range children: Python's
`largest` after the two comparisons of the `while` body. -/
def maxChild₁ (arr : List Nat) (hs i : Nat) : Nat :=
  if left i < hs ∧ arr.getD i 0 < arr.getD (left i) 0 then left i else i

/-- Python's `largest` after both comparisons of the `while` body. -/
def maxChild (arr : List Nat) (hs i : Nat) : Nat :=
  if right i < hs ∧ arr.getD (maxChild₁ arr hs i) 0 < arr.getD (right i) 0 then right i
  else maxChild₁ arr hs i

/-- One sift-down step of `MAX-HEAPIFY`, driven by `fuel`. -/
def maxHeapifyLoop : Nat → List Nat → Nat → Nat → List Nat
  | 0, arr, _, _ => arr
  | fuel + 1, arr, hs, i =>
    let largest := maxChild arr hs i
    if largest = i then arr else maxHeapifyLoop fuel (swap arr i largest) hs largest

/-- `MAX-HEAPIFY(arr, heapSize, i)`: sift `arr[i]` down so that the subtree
rooted at `i` becomes a max-heap. -/
def maxHeapify (arr : List Nat) (hs : Nat) (i : Nat) : List Nat :=
  if hs ≤ i ∨ arr.length ≤ i then arr else maxHeapifyLoop (arr.length + 1) arr hs i

/-- The index of the smallest of `arr[i]` and its in-range children: Python's
`smallest` after the two comparisons of the `while` body. -/
def minChild₁ (arr : List Nat) (hs i : Nat) : Nat :=
  if left i < hs ∧ arr.getD (left i) 0 < arr.getD i 0 then left i else i

/-- Python's `smallest` after both comparisons of the `while` body. -/
def minChild (arr : List Nat) (hs i : Nat) : Nat :=
  if right i < hs ∧ arr.getD (right i) 0 < arr.getD (minChild₁ arr hs i) 0 then right i
  else minChild₁ arr hs i

/-- One sift-down step of `MIN-HEAPIFY`, driven by `fuel`. -/
def minHeapifyLoop : Nat → List Nat → Nat → Nat → List Nat
  | 0, arr, _, _ => arr
  | fuel + 1, arr, hs, i =>
    let smallest := minChild arr hs i
    if smallest = i then arr else minHeapifyLoop fuel (swap arr i smallest) hs smallest

/-- `MIN-HEAPIFY(arr, heapSize, i)`. -/
def minHeapify (arr : List Nat) (hs : Nat) (i : Nat) : List Nat :=
  if hs ≤ i ∨ arr.length ≤ i then arr else minHeapifyLoop (arr.length + 1) arr hs i

/-- `is_max_heap(arr, heapSize)`. -/
def isMaxHeap (arr : List Nat) (hs : Nat) : Bool :=
  (List.range (min hs arr.length)).all fun i =>
    decide ((left i < hs → arr.getD (left i) 0 ≤ arr.getD i 0) ∧
            (right i < hs → arr.getD (right i) 0 ≤ arr.getD i 0))

/-- `is_min_heap(arr, heapSize)`. -/
def isMinHeap (arr : List Nat) (hs : Nat) : Bool :=
  (List.range (min hs arr.length)).all fun i =>
    decide ((left i < hs → arr.getD i 0 ≤ arr.getD (left i) 0) ∧
            (right i < hs → arr.getD i 0 ≤ arr.getD (right i) 0))

/-- `maxHeapify` applied to the indices `k - 1, k - 2, ..., 0`, in that order. -/
def buildMaxLoop (n : Nat) : Nat → List Nat → List Nat
  | 0, arr => arr
  | k + 1, arr => buildMaxLoop n k (maxHeapify arr n k)

/-- `BUILD-MAX-HEAP(arr)`. -/
def buildMaxHeap (arr : List Nat) : List Nat :=
  if arr.length ≤ 1 then arr else buildMaxLoop arr.length (arr.length / 2) arr

/-- `minHeapify` applied to the indices `k - 1, k - 2, ..., 0`, in that order. -/
def buildMinLoop (n : Nat) : Nat → List Nat → List Nat
  | 0, arr => arr
  | k + 1, arr => buildMinLoop n k (minHeapify arr n k)

/-- `BUILD-MIN-HEAP(arr)`. -/
def buildMinHeap (arr : List Nat) : List Nat :=
  if arr.length ≤ 1 then arr else buildMinLoop arr.length (arr.length / 2) arr

/-! ## Unit tests (the assertions of the Python `check`) -/

example : buildMaxHeap [4, 1, 3, 2, 16, 9, 10, 14, 8, 7] = [16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by
  native_decide

example : buildMaxHeap [5, 3, 17, 10, 84, 19, 6, 22, 9] = [84, 22, 19, 10, 3, 17, 6, 5, 9] := by
  native_decide

example : isMaxHeap (buildMaxHeap [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]) 10 = true := by native_decide
example : isMaxHeap (buildMaxHeap [5, 3, 17, 10, 84, 19, 6, 22, 9]) 9 = true := by native_decide

example : buildMaxHeap [] = [] := by native_decide
example : buildMaxHeap [42] = [42] := by native_decide
example : buildMaxHeap [1, 2] = [2, 1] := by native_decide
example : buildMaxHeap [2, 1] = [2, 1] := by native_decide
example : buildMaxHeap [3, 3, 3] = [3, 3, 3] := by native_decide

example : buildMaxHeap [16, 14, 10, 8, 7, 9, 3, 2, 4, 1] = [16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by
  native_decide

example : isMaxHeap (buildMaxHeap [7, 3, 5, 1, 9, 2, 8]) 7 = true := by native_decide
example : isMaxHeap (buildMaxHeap [1, 2, 3, 4, 5, 6, 7, 8, 9]) 9 = true := by native_decide
example : (buildMaxHeap [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]).length = 10 := by native_decide
example : isMinHeap (buildMinHeap [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]) 10 = true := by native_decide
example : isMaxHeap [4, 1, 3, 2, 16, 9, 10, 14, 8, 7] 10 = false := by native_decide

example : buildMaxHeap [4, 1, 3, 2, 16, 9, 10, 14, 8, 7] ≠ [4, 1, 3, 2, 16, 9, 10, 14, 8, 7] := by
  native_decide

example : (buildMaxHeap [10, 20, 30, 40, 50]).getD 0 0 = 50 := by native_decide
example : (buildMaxHeap [100, 1, 50, 2, 99]).getD 0 0 = 100 := by native_decide

example : (buildMaxHeap [5, 3, 17, 10, 84, 19, 6, 22, 9]).mergeSort (· ≤ ·)
    = [3, 5, 6, 9, 10, 17, 19, 22, 84] := by native_decide

#eval buildMaxHeap [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]
#eval buildMinHeap [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]
#eval buildMaxHeap [5, 3, 17, 10, 84, 19, 6, 22, 9]
#eval isMaxHeap (buildMaxHeap [7, 3, 5, 1, 9, 2, 8]) 7

/-! ## Pre-condition -/

/-- Python's `_check_nat_list`: every entry must be a natural number.  In Lean
this is guaranteed by the type `List Nat`, so the pre-condition is vacuous;
`build_max_heap([1, -1])` is simply not expressible. -/
def Pre (arr : List Nat) : Prop := ∀ x ∈ arr, 0 ≤ x

/-- Pre-condition of `maxHeapify`/`minHeapify`: the heap size must not exceed
the length of the array (otherwise Python raises `IndexError`). -/
def PreHeapify (arr : List Nat) (hs : Nat) : Prop := hs ≤ arr.length

/-! ## Properties and theorems -/

/-- The local max-heap property at index `i`: `i` dominates its in-range children. -/
def MaxHeapAt (arr : List Nat) (hs i : Nat) : Prop :=
  (left i < hs → arr.getD (left i) 0 ≤ arr.getD i 0) ∧
  (right i < hs → arr.getD (right i) 0 ≤ arr.getD i 0)

/-- The local min-heap property at index `i`. -/
def MinHeapAt (arr : List Nat) (hs i : Nat) : Prop :=
  (left i < hs → arr.getD i 0 ≤ arr.getD (left i) 0) ∧
  (right i < hs → arr.getD i 0 ≤ arr.getD (right i) 0)

/-- Reading back a `Prop`-level description of `isMaxHeap`. -/
def IsMaxHeapProp (arr : List Nat) (hs : Nat) : Prop :=
  ∀ i, i < hs → i < arr.length → MaxHeapAt arr hs i

/-- Reading back a `Prop`-level description of `isMinHeap`. -/
def IsMinHeapProp (arr : List Nat) (hs : Nat) : Prop :=
  ∀ i, i < hs → i < arr.length → MinHeapAt arr hs i

theorem isMaxHeap_iff (arr : List Nat) (hs : Nat) :
    isMaxHeap arr hs = true ↔ IsMaxHeapProp arr hs := by
  simp only [isMaxHeap, IsMaxHeapProp, MaxHeapAt, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    lt_min_iff]
  constructor
  · intro h i h1 h2
    exact h i ⟨h1, h2⟩
  · rintro h i ⟨h1, h2⟩
    exact h i h1 h2

theorem isMinHeap_iff (arr : List Nat) (hs : Nat) :
    isMinHeap arr hs = true ↔ IsMinHeapProp arr hs := by
  simp only [isMinHeap, IsMinHeapProp, MinHeapAt, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    lt_min_iff]
  constructor
  · intro h i h1 h2
    exact h i ⟨h1, h2⟩
  · rintro h i ⟨h1, h2⟩
    exact h i h1 h2

/-! ### The `largest` / `smallest` index picked by one loop iteration -/

theorem maxChild_eq_or (arr : List Nat) (hs i : Nat) :
    maxChild arr hs i = i ∨ maxChild arr hs i = left i ∨ maxChild arr hs i = right i := by
  unfold maxChild maxChild₁
  split_ifs <;> simp

theorem maxChild_lt_hs (arr : List Nat) (hs i : Nat) (h : maxChild arr hs i ≠ i) :
    maxChild arr hs i < hs := by
  unfold maxChild maxChild₁ at h ⊢
  split_ifs at h ⊢ <;> simp_all

theorem le_maxChild (arr : List Nat) (hs i : Nat) :
    arr.getD i 0 ≤ arr.getD (maxChild arr hs i) 0 := by
  unfold maxChild maxChild₁
  split_ifs <;> simp_all <;> omega

theorem left_le_maxChild (arr : List Nat) (hs i : Nat) (h : left i < hs) :
    arr.getD (left i) 0 ≤ arr.getD (maxChild arr hs i) 0 := by
  unfold maxChild maxChild₁
  split_ifs <;> simp_all <;> omega

theorem right_le_maxChild (arr : List Nat) (hs i : Nat) (h : right i < hs) :
    arr.getD (right i) 0 ≤ arr.getD (maxChild arr hs i) 0 := by
  unfold maxChild maxChild₁
  split_ifs <;> simp_all <;> omega

theorem maxChild_eq_self (arr : List Nat) (hs i : Nat)
    (hl : left i < hs → arr.getD (left i) 0 ≤ arr.getD i 0)
    (hr : right i < hs → arr.getD (right i) 0 ≤ arr.getD i 0) :
    maxChild arr hs i = i := by
  unfold maxChild maxChild₁
  split_ifs <;> simp_all <;> omega

theorem minChild_eq_or (arr : List Nat) (hs i : Nat) :
    minChild arr hs i = i ∨ minChild arr hs i = left i ∨ minChild arr hs i = right i := by
  unfold minChild minChild₁
  split_ifs <;> simp

theorem minChild_lt_hs (arr : List Nat) (hs i : Nat) (h : minChild arr hs i ≠ i) :
    minChild arr hs i < hs := by
  unfold minChild minChild₁ at h ⊢
  split_ifs at h ⊢ <;> simp_all

theorem minChild_le (arr : List Nat) (hs i : Nat) :
    arr.getD (minChild arr hs i) 0 ≤ arr.getD i 0 := by
  unfold minChild minChild₁
  split_ifs <;> simp_all <;> omega

theorem minChild_le_left (arr : List Nat) (hs i : Nat) (h : left i < hs) :
    arr.getD (minChild arr hs i) 0 ≤ arr.getD (left i) 0 := by
  unfold minChild minChild₁
  split_ifs <;> simp_all <;> omega

theorem minChild_le_right (arr : List Nat) (hs i : Nat) (h : right i < hs) :
    arr.getD (minChild arr hs i) 0 ≤ arr.getD (right i) 0 := by
  unfold minChild minChild₁
  split_ifs <;> simp_all <;> omega

theorem minChild_eq_self (arr : List Nat) (hs i : Nat)
    (hl : left i < hs → arr.getD i 0 ≤ arr.getD (left i) 0)
    (hr : right i < hs → arr.getD i 0 ≤ arr.getD (right i) 0) :
    minChild arr hs i = i := by
  unfold minChild minChild₁
  split_ifs <;> simp_all <;> omega

/-- `parent` inverts `left`. -/
theorem parent_left (i : Nat) : parent (left i) = i := by
  simp only [parent, left, if_neg (by omega : ¬ 2 * i + 1 = 0)]
  omega

/-- `parent` inverts `right`. -/
theorem parent_right (i : Nat) : parent (right i) = i := by
  simp only [parent, right, if_neg (by omega : ¬ 2 * i + 2 = 0)]
  omega

/-- Children have strictly larger indices than their parent. -/
theorem lt_left (i : Nat) : i < left i := by simp [left]; omega

theorem left_lt_right (i : Nat) : left i < right i := by simp [left, right]

/-- Every non-root index is a child of its parent. -/
theorem left_or_right_parent (i : Nat) (h : 0 < i) :
    left (parent i) = i ∨ right (parent i) = i := by
  rcases Nat.even_or_odd i with he | ho
  · right
    obtain ⟨k, hk⟩ := he
    simp only [parent, right, if_neg (by omega : ¬ i = 0)]
    omega
  · left
    obtain ⟨k, hk⟩ := ho
    simp only [parent, left, if_neg (by omega : ¬ i = 0)]
    omega

/-! ### `swap` -/

theorem swap_length (l : List Nat) (i j : Nat) : (swap l i j).length = l.length := by
  unfold swap
  split <;> simp

theorem swap_perm (l : List Nat) (i j : Nat) : (swap l i j).Perm l := by
  unfold swap
  split
  · rename_i h
    obtain ⟨hi, hj⟩ := h
    rw [List.getD_eq_getElem l 0 hj, List.getD_eq_getElem l 0 hi]
    exact List.set_set_perm hi hj
  · exact List.Perm.refl l

/-! ### Length is preserved -/

theorem maxHeapifyLoop_length (fuel : Nat) : ∀ (arr : List Nat) (hs i : Nat),
    (maxHeapifyLoop fuel arr hs i).length = arr.length := by
  induction fuel with
  | zero => intro arr hs i; rfl
  | succ n ih =>
    intro arr hs i
    rw [maxHeapifyLoop]
    split_ifs <;> simp [ih, swap_length]

theorem maxHeapify_length (arr : List Nat) (hs i : Nat) :
    (maxHeapify arr hs i).length = arr.length := by
  unfold maxHeapify
  split
  · rfl
  · exact maxHeapifyLoop_length _ _ _ _

theorem minHeapifyLoop_length (fuel : Nat) : ∀ (arr : List Nat) (hs i : Nat),
    (minHeapifyLoop fuel arr hs i).length = arr.length := by
  induction fuel with
  | zero => intro arr hs i; rfl
  | succ n ih =>
    intro arr hs i
    rw [minHeapifyLoop]
    split_ifs <;> simp [ih, swap_length]

theorem minHeapify_length (arr : List Nat) (hs i : Nat) :
    (minHeapify arr hs i).length = arr.length := by
  unfold minHeapify
  split
  · rfl
  · exact minHeapifyLoop_length _ _ _ _

theorem buildMaxLoop_length (n k : Nat) : ∀ arr : List Nat,
    (buildMaxLoop n k arr).length = arr.length := by
  induction k with
  | zero => intro arr; rfl
  | succ k ih =>
    intro arr
    rw [buildMaxLoop, ih, maxHeapify_length]

theorem buildMinLoop_length (n k : Nat) : ∀ arr : List Nat,
    (buildMinLoop n k arr).length = arr.length := by
  induction k with
  | zero => intro arr; rfl
  | succ k ih =>
    intro arr
    rw [buildMinLoop, ih, minHeapify_length]

/-- `build_max_heap` preserves the length of the array. -/
def buildMaxHeap_length_prop (arr : List Nat) : Prop :=
  (buildMaxHeap arr).length = arr.length

theorem buildMaxHeap_length_thm (arr : List Nat) : buildMaxHeap_length_prop arr := by
  unfold buildMaxHeap_length_prop buildMaxHeap
  split
  · rfl
  · exact buildMaxLoop_length _ _ _

/-- `build_min_heap` preserves the length of the array. -/
def buildMinHeap_length_prop (arr : List Nat) : Prop :=
  (buildMinHeap arr).length = arr.length

theorem buildMinHeap_length_thm (arr : List Nat) : buildMinHeap_length_prop arr := by
  unfold buildMinHeap_length_prop buildMinHeap
  split
  · rfl
  · exact buildMinLoop_length _ _ _

/-! ### The multiset of entries is preserved -/

theorem maxHeapifyLoop_perm (fuel : Nat) : ∀ (arr : List Nat) (hs i : Nat),
    (maxHeapifyLoop fuel arr hs i).Perm arr := by
  induction fuel with
  | zero => intro arr hs i; exact List.Perm.refl _
  | succ n ih =>
    intro arr hs i
    rw [maxHeapifyLoop]
    split_ifs <;>
      first
        | exact List.Perm.refl _
        | exact (ih _ _ _).trans (swap_perm _ _ _)

theorem maxHeapify_perm (arr : List Nat) (hs i : Nat) : (maxHeapify arr hs i).Perm arr := by
  unfold maxHeapify
  split
  · exact List.Perm.refl _
  · exact maxHeapifyLoop_perm _ _ _ _

theorem minHeapifyLoop_perm (fuel : Nat) : ∀ (arr : List Nat) (hs i : Nat),
    (minHeapifyLoop fuel arr hs i).Perm arr := by
  induction fuel with
  | zero => intro arr hs i; exact List.Perm.refl _
  | succ n ih =>
    intro arr hs i
    rw [minHeapifyLoop]
    split_ifs <;>
      first
        | exact List.Perm.refl _
        | exact (ih _ _ _).trans (swap_perm _ _ _)

theorem minHeapify_perm (arr : List Nat) (hs i : Nat) : (minHeapify arr hs i).Perm arr := by
  unfold minHeapify
  split
  · exact List.Perm.refl _
  · exact minHeapifyLoop_perm _ _ _ _

theorem buildMaxLoop_perm (n k : Nat) : ∀ arr : List Nat, (buildMaxLoop n k arr).Perm arr := by
  induction k with
  | zero => intro arr; exact List.Perm.refl _
  | succ k ih =>
    intro arr
    rw [buildMaxLoop]
    exact (ih _).trans (maxHeapify_perm _ _ _)

theorem buildMinLoop_perm (n k : Nat) : ∀ arr : List Nat, (buildMinLoop n k arr).Perm arr := by
  induction k with
  | zero => intro arr; exact List.Perm.refl _
  | succ k ih =>
    intro arr
    rw [buildMinLoop]
    exact (ih _).trans (minHeapify_perm _ _ _)

/-- `build_max_heap` rearranges the array: the result is a permutation of the
input (this is what the `sorted(...)` assertion in Python checks). -/
def buildMaxHeap_perm_prop (arr : List Nat) : Prop := (buildMaxHeap arr).Perm arr

theorem buildMaxHeap_perm_thm (arr : List Nat) : buildMaxHeap_perm_prop arr := by
  unfold buildMaxHeap_perm_prop buildMaxHeap
  split
  · exact List.Perm.refl _
  · exact buildMaxLoop_perm _ _ _

/-- `build_min_heap` rearranges the array. -/
def buildMinHeap_perm_prop (arr : List Nat) : Prop := (buildMinHeap arr).Perm arr

theorem buildMinHeap_perm_thm (arr : List Nat) : buildMinHeap_perm_prop arr := by
  unfold buildMinHeap_perm_prop buildMinHeap
  split
  · exact List.Perm.refl _
  · exact buildMinLoop_perm _ _ _

/-! ### Heaps are fixed points -/

theorem maxHeapify_eq_self (arr : List Nat) (hs i : Nat) (h : isMaxHeap arr hs = true) :
    maxHeapify arr hs i = arr := by
  rw [isMaxHeap_iff] at h
  unfold maxHeapify
  split
  · rfl
  · rename_i hi
    push_neg at hi
    obtain ⟨h1, h2⟩ := hi
    obtain ⟨hl, hr⟩ := h i h1 h2
    rw [maxHeapifyLoop, maxChild_eq_self arr hs i hl hr]
    simp

theorem minHeapify_eq_self (arr : List Nat) (hs i : Nat) (h : isMinHeap arr hs = true) :
    minHeapify arr hs i = arr := by
  rw [isMinHeap_iff] at h
  unfold minHeapify
  split
  · rfl
  · rename_i hi
    push_neg at hi
    obtain ⟨h1, h2⟩ := hi
    obtain ⟨hl, hr⟩ := h i h1 h2
    rw [minHeapifyLoop, minChild_eq_self arr hs i hl hr]
    simp

theorem buildMaxLoop_eq_self (n k : Nat) (arr : List Nat) (h : isMaxHeap arr n = true) :
    buildMaxLoop n k arr = arr := by
  induction k with
  | zero => rfl
  | succ k ih => rw [buildMaxLoop, maxHeapify_eq_self arr n k h, ih]

/-- Running `build_max_heap` on an array that already is a max-heap does
nothing (Python: `build_max_heap([16, 14, 10, 8, 7, 9, 3, 2, 4, 1])` is the
identity). -/
def buildMaxHeap_idem_prop (arr : List Nat) : Prop :=
  isMaxHeap arr arr.length = true → buildMaxHeap arr = arr

theorem buildMaxHeap_idem_thm (arr : List Nat) : buildMaxHeap_idem_prop arr := by
  intro h
  unfold buildMaxHeap
  split
  · rfl
  · exact buildMaxLoop_eq_self _ _ _ h

theorem buildMinLoop_eq_self (n k : Nat) (arr : List Nat) (h : isMinHeap arr n = true) :
    buildMinLoop n k arr = arr := by
  induction k with
  | zero => rfl
  | succ k ih => rw [buildMinLoop, minHeapify_eq_self arr n k h, ih]

/-- Running `build_min_heap` on an array that already is a min-heap does nothing. -/
def buildMinHeap_idem_prop (arr : List Nat) : Prop :=
  isMinHeap arr arr.length = true → buildMinHeap arr = arr

theorem buildMinHeap_idem_thm (arr : List Nat) : buildMinHeap_idem_prop arr := by
  intro h
  unfold buildMinHeap
  split
  · rfl
  · exact buildMinLoop_eq_self _ _ _ h

/-! ### The root of a max-heap is the maximum -/

/-- In a max-heap every entry is bounded by the root. -/
theorem le_root_of_isMaxHeap (arr : List Nat) (hs : Nat) (h : isMaxHeap arr hs = true)
    (hle : hs ≤ arr.length) :
    ∀ i, i < hs → arr.getD i 0 ≤ arr.getD 0 0 := by
  rw [isMaxHeap_iff] at h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact le_rfl
    · have hp : parent i < i := by
        simp only [parent, if_neg (by omega : ¬ i = 0)]
        omega
      have hpi : parent i < hs := lt_trans hp hi
      have hstep : arr.getD i 0 ≤ arr.getD (parent i) 0 := by
        obtain ⟨hcl, hcr⟩ := h (parent i) hpi (lt_of_lt_of_le hpi hle)
        rcases left_or_right_parent i hpos with he | he
        · have hc := hcl (by rw [he]; exact hi)
          rwa [he] at hc
        · have hc := hcr (by rw [he]; exact hi)
          rwa [he] at hc
      exact le_trans hstep (ih (parent i) hp hpi)

/-! ### Reading entries of a swap -/

theorem left_eq (i : Nat) : left i = 2 * i + 1 := rfl

theorem right_eq (i : Nat) : right i = 2 * i + 2 := rfl

theorem swap_getD_fst (l : List Nat) (i j : Nat) (hi : i < l.length) (hj : j < l.length) :
    (swap l i j).getD i 0 = l.getD j 0 := by
  rcases eq_or_ne i j with rfl | hne
  · simp [swap, hi, List.getD_eq_getElem?_getD]
  · simp [swap, hi, hj, List.getD_eq_getElem?_getD, List.getElem_set_ne (Ne.symm hne)]

theorem swap_getD_snd (l : List Nat) (i j : Nat) (hi : i < l.length) (hj : j < l.length) :
    (swap l i j).getD j 0 = l.getD i 0 := by
  simp [swap, hi, hj, List.getD_eq_getElem?_getD]

theorem swap_getD_other (l : List Nat) (i j k : Nat) (hki : k ≠ i) (hkj : k ≠ j) :
    (swap l i j).getD k 0 = l.getD k 0 := by
  unfold swap
  split
  · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hkj),
      List.getElem?_set_ne (Ne.symm hki)]
  · rfl

/-! ### Correctness of `maxHeapify`

Sifting down from an index `c` only rewrites `c` and the positions of the
subtree below it (all `≥ 2 * c + 1`), it puts one of the three compared values
at position `c`, and -- provided every strictly larger index already satisfies
the local heap property -- it restores that property at `c` as well. -/

theorem maxHeapifyLoop_getD_of_lt (fuel : Nat) : ∀ (arr : List Nat) (hs c j : Nat),
    j ≠ c → j < 2 * c + 1 → (maxHeapifyLoop fuel arr hs c).getD j 0 = arr.getD j 0 := by
  induction fuel with
  | zero => intro arr hs c j _ _; rfl
  | succ f ih =>
    intro arr hs c j hjc hjlt
    rw [maxHeapifyLoop]
    split
    · rfl
    · rename_i hne
      have hge : 2 * c + 1 ≤ maxChild arr hs c := by
        rcases maxChild_eq_or arr hs c with h | h | h
        · exact absurd h hne
        · simp only [h, left_eq]; omega
        · simp only [h, right_eq]; omega
      rw [ih _ hs _ j (by omega) (by omega)]
      exact swap_getD_other arr c _ j hjc (by omega)

theorem maxHeapifyLoop_getD_start_le (fuel : Nat) (arr : List Nat) (hs c v : Nat)
    (hlen : hs ≤ arr.length) (hc : c < hs) (h0 : arr.getD c 0 ≤ v)
    (hl : left c < hs → arr.getD (left c) 0 ≤ v)
    (hr : right c < hs → arr.getD (right c) 0 ≤ v) :
    (maxHeapifyLoop fuel arr hs c).getD c 0 ≤ v := by
  cases fuel with
  | zero => exact h0
  | succ f =>
    rw [maxHeapifyLoop]
    split
    · exact h0
    · rename_i hne
      have hmem := maxChild_eq_or arr hs c
      have hclt : maxChild arr hs c < hs := maxChild_lt_hs arr hs c hne
      have hge : 2 * c + 1 ≤ maxChild arr hs c := by
        rcases hmem with h | h | h
        · exact absurd h hne
        · simp only [h, left_eq]; omega
        · simp only [h, right_eq]; omega
      rw [maxHeapifyLoop_getD_of_lt f _ hs _ c (by omega) (by omega),
        swap_getD_fst arr c _ (by omega) (by omega)]
      rcases hmem with h | h | h
      · exact absurd h hne
      · rw [h]; exact hl (by omega)
      · rw [h]; exact hr (by omega)

theorem maxHeapifyLoop_correct (fuel : Nat) : ∀ (arr : List Nat) (hs i : Nat),
    hs ≤ arr.length → i < hs → hs ≤ i + fuel →
    (∀ j, i < j → j < hs → MaxHeapAt arr hs j) →
    ∀ j, i ≤ j → j < hs → MaxHeapAt (maxHeapifyLoop fuel arr hs i) hs j := by
  induction fuel with
  | zero => intro arr hs i _ hi hf _ j _ _; omega
  | succ f ih =>
    intro arr hs i hlen hi hfuel H j hij hj
    rw [maxHeapifyLoop]
    split
    · -- the loop stops immediately: `arr` already satisfies the property at `i`
      rename_i heq
      by_cases hji : j = i
      · subst hji
        exact ⟨fun h => by have := left_le_maxChild arr hs j h; rwa [heq] at this,
               fun h => by have := right_le_maxChild arr hs j h; rwa [heq] at this⟩
      · exact H j (lt_of_le_of_ne hij (Ne.symm hji)) hj
    · rename_i hne
      have hmem := maxChild_eq_or arr hs i
      have hclt : maxChild arr hs i < hs := maxChild_lt_hs arr hs i hne
      have hile : arr.getD i 0 ≤ arr.getD (maxChild arr hs i) 0 := le_maxChild arr hs i
      have hlle : left i < hs → arr.getD (left i) 0 ≤ arr.getD (maxChild arr hs i) 0 :=
        left_le_maxChild arr hs i
      have hrle : right i < hs → arr.getD (right i) 0 ≤ arr.getD (maxChild arr hs i) 0 :=
        right_le_maxChild arr hs i
      obtain ⟨c, hcdef⟩ : ∃ c, maxChild arr hs i = c := ⟨_, rfl⟩
      rw [hcdef] at hne hclt hile hlle hrle hmem ⊢
      have hbounds : i < c ∧ c ≤ 2 * i + 2 := by
        rcases hmem with h | h | h
        · exact absurd h hne
        · simp only [left_eq] at h; omega
        · simp only [right_eq] at h; omega
      obtain ⟨hic, hcle⟩ := hbounds
      obtain ⟨arr', harr'⟩ : ∃ a, swap arr i c = a := ⟨_, rfl⟩
      rw [harr'] at ⊢
      have hlen' : hs ≤ arr'.length := by rw [← harr', swap_length]; exact hlen
      have hvi : arr'.getD i 0 = arr.getD c 0 := by
        rw [← harr']; exact swap_getD_fst arr i c (by omega) (by omega)
      have hvc : arr'.getD c 0 = arr.getD i 0 := by
        rw [← harr']; exact swap_getD_snd arr i c (by omega) (by omega)
      have hvo : ∀ p, p ≠ i → p ≠ c → arr'.getD p 0 = arr.getD p 0 := by
        intro p h1 h2
        rw [← harr']; exact swap_getD_other arr i c p h1 h2
      have H' : ∀ p, c < p → p < hs → MaxHeapAt arr' hs p := by
        intro p hp hps
        obtain ⟨hL, hR⟩ := H p (by omega) hps
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [hvo (left p) (by simp only [left_eq]; omega) (by simp only [left_eq]; omega),
            hvo p (by omega) (by omega)]
          exact hL h
        · rw [hvo (right p) (by simp only [right_eq]; omega) (by simp only [right_eq]; omega),
            hvo p (by omega) (by omega)]
          exact hR h
      have IH := ih arr' hs c hlen' hclt (by omega) H'
      rcases lt_or_ge j c with hjc | hjc
      · by_cases hji : j = i
        · -- the root of the sifted subtree
          subst hji
          have hres : (maxHeapifyLoop f arr' hs c).getD j 0 = arr.getD c 0 := by
            rw [maxHeapifyLoop_getD_of_lt f arr' hs c j (by omega) (by omega), hvi]
          have key : ∀ s, s = left j ∨ s = right j → s < hs →
              (maxHeapifyLoop f arr' hs c).getD s 0 ≤ arr.getD c 0 := by
            intro s hs' hslt
            by_cases hsc : s = c
            · subst hsc
              obtain ⟨hL, hR⟩ := H s hic hclt
              refine maxHeapifyLoop_getD_start_le f arr' hs s (arr.getD s 0) hlen' hslt ?_ ?_ ?_
              · rw [hvc]; exact hile
              · intro h
                rw [hvo (left s) (by simp only [left_eq]; omega) (by simp only [left_eq]; omega)]
                exact hL h
              · intro h
                rw [hvo (right s) (by simp only [right_eq]; omega) (by simp only [right_eq]; omega)]
                exact hR h
            · have hslow : s < 2 * c + 1 := by
                rcases hs' with h | h <;> simp only [h, left_eq, right_eq] <;> omega
              rw [maxHeapifyLoop_getD_of_lt f arr' hs c s hsc hslow,
                hvo s (by rcases hs' with h | h <;> simp only [h, left_eq, right_eq] <;> omega) hsc]
              rcases hs' with h | h
              · subst h; exact hlle hslt
              · subst h; exact hrle hslt
          exact ⟨fun h => by rw [hres]; exact key (left j) (Or.inl rfl) h,
                 fun h => by rw [hres]; exact key (right j) (Or.inr rfl) h⟩
        · -- an index between `i` and `c`: nothing in its neighbourhood was touched
          have hji' : i < j := lt_of_le_of_ne hij (Ne.symm hji)
          obtain ⟨hL, hR⟩ := H j hji' hj
          have e0 : (maxHeapifyLoop f arr' hs c).getD j 0 = arr.getD j 0 := by
            rw [maxHeapifyLoop_getD_of_lt f arr' hs c j (by omega) (by omega),
              hvo j (by omega) (by omega)]
          have e1 : (maxHeapifyLoop f arr' hs c).getD (left j) 0 = arr.getD (left j) 0 := by
            rw [maxHeapifyLoop_getD_of_lt f arr' hs c (left j)
                (by simp only [left_eq]; omega) (by simp only [left_eq]; omega),
              hvo (left j) (by simp only [left_eq]; omega) (by simp only [left_eq]; omega)]
          have e2 : (maxHeapifyLoop f arr' hs c).getD (right j) 0 = arr.getD (right j) 0 := by
            rw [maxHeapifyLoop_getD_of_lt f arr' hs c (right j)
                (by simp only [right_eq]; omega) (by simp only [right_eq]; omega),
              hvo (right j) (by simp only [right_eq]; omega) (by simp only [right_eq]; omega)]
          exact ⟨fun h => by rw [e1, e0]; exact hL h, fun h => by rw [e2, e0]; exact hR h⟩
      · exact IH j hjc hj

/-- `MAX-HEAPIFY(arr, hs, i)` restores the max-heap property at `i`, given that
it already holds at every index above `i`. -/
theorem maxHeapify_correct (arr : List Nat) (hs i : Nat) (hlen : PreHeapify arr hs) (hi : i < hs)
    (H : ∀ j, i < j → j < hs → MaxHeapAt arr hs j) :
    ∀ j, i ≤ j → j < hs → MaxHeapAt (maxHeapify arr hs i) hs j := by
  unfold PreHeapify at hlen
  unfold maxHeapify
  rw [if_neg (by push_neg; exact ⟨hi, by omega⟩)]
  exact maxHeapifyLoop_correct (arr.length + 1) arr hs i hlen hi (by omega) H

theorem buildMaxLoop_correct (n k : Nat) : ∀ arr : List Nat, n ≤ arr.length →
    (∀ j, k ≤ j → j < n → MaxHeapAt arr n j) →
    ∀ j, j < n → MaxHeapAt (buildMaxLoop n k arr) n j := by
  induction k with
  | zero => intro arr _ H j hj; exact H j (Nat.zero_le _) hj
  | succ k ih =>
    intro arr hlen H
    rw [buildMaxLoop]
    refine ih _ (by rw [maxHeapify_length]; exact hlen) ?_
    by_cases hk : k < n
    · exact maxHeapify_correct arr n k hlen hk (fun j hj hjn => H j (by omega) hjn)
    · intro j hj hjn
      exact absurd hjn (by omega)

/-! ### Correctness of `minHeapify` (mirror image of the `maxHeapify` proofs) -/

theorem minHeapifyLoop_getD_of_lt (fuel : Nat) : ∀ (arr : List Nat) (hs c j : Nat),
    j ≠ c → j < 2 * c + 1 → (minHeapifyLoop fuel arr hs c).getD j 0 = arr.getD j 0 := by
  induction fuel with
  | zero => intro arr hs c j _ _; rfl
  | succ f ih =>
    intro arr hs c j hjc hjlt
    rw [minHeapifyLoop]
    split
    · rfl
    · rename_i hne
      have hge : 2 * c + 1 ≤ minChild arr hs c := by
        rcases minChild_eq_or arr hs c with h | h | h
        · exact absurd h hne
        · simp only [h, left_eq]; omega
        · simp only [h, right_eq]; omega
      rw [ih _ hs _ j (by omega) (by omega)]
      exact swap_getD_other arr c _ j hjc (by omega)

theorem minHeapifyLoop_le_getD_start (fuel : Nat) (arr : List Nat) (hs c v : Nat)
    (hlen : hs ≤ arr.length) (hc : c < hs) (h0 : v ≤ arr.getD c 0)
    (hl : left c < hs → v ≤ arr.getD (left c) 0)
    (hr : right c < hs → v ≤ arr.getD (right c) 0) :
    v ≤ (minHeapifyLoop fuel arr hs c).getD c 0 := by
  cases fuel with
  | zero => exact h0
  | succ f =>
    rw [minHeapifyLoop]
    split
    · exact h0
    · rename_i hne
      have hmem := minChild_eq_or arr hs c
      have hclt : minChild arr hs c < hs := minChild_lt_hs arr hs c hne
      have hge : 2 * c + 1 ≤ minChild arr hs c := by
        rcases hmem with h | h | h
        · exact absurd h hne
        · simp only [h, left_eq]; omega
        · simp only [h, right_eq]; omega
      rw [minHeapifyLoop_getD_of_lt f _ hs _ c (by omega) (by omega),
        swap_getD_fst arr c _ (by omega) (by omega)]
      rcases hmem with h | h | h
      · exact absurd h hne
      · rw [h]; exact hl (by omega)
      · rw [h]; exact hr (by omega)

theorem minHeapifyLoop_correct (fuel : Nat) : ∀ (arr : List Nat) (hs i : Nat),
    hs ≤ arr.length → i < hs → hs ≤ i + fuel →
    (∀ j, i < j → j < hs → MinHeapAt arr hs j) →
    ∀ j, i ≤ j → j < hs → MinHeapAt (minHeapifyLoop fuel arr hs i) hs j := by
  induction fuel with
  | zero => intro arr hs i _ hi hf _ j _ _; omega
  | succ f ih =>
    intro arr hs i hlen hi hfuel H j hij hj
    rw [minHeapifyLoop]
    split
    · rename_i heq
      by_cases hji : j = i
      · subst hji
        exact ⟨fun h => by have := minChild_le_left arr hs j h; rwa [heq] at this,
               fun h => by have := minChild_le_right arr hs j h; rwa [heq] at this⟩
      · exact H j (lt_of_le_of_ne hij (Ne.symm hji)) hj
    · rename_i hne
      have hmem := minChild_eq_or arr hs i
      have hclt : minChild arr hs i < hs := minChild_lt_hs arr hs i hne
      have hile : arr.getD (minChild arr hs i) 0 ≤ arr.getD i 0 := minChild_le arr hs i
      have hlle : left i < hs → arr.getD (minChild arr hs i) 0 ≤ arr.getD (left i) 0 :=
        minChild_le_left arr hs i
      have hrle : right i < hs → arr.getD (minChild arr hs i) 0 ≤ arr.getD (right i) 0 :=
        minChild_le_right arr hs i
      obtain ⟨c, hcdef⟩ : ∃ c, minChild arr hs i = c := ⟨_, rfl⟩
      rw [hcdef] at hne hclt hile hlle hrle hmem ⊢
      have hbounds : i < c ∧ c ≤ 2 * i + 2 := by
        rcases hmem with h | h | h
        · exact absurd h hne
        · simp only [left_eq] at h; omega
        · simp only [right_eq] at h; omega
      obtain ⟨hic, hcle⟩ := hbounds
      obtain ⟨arr', harr'⟩ : ∃ a, swap arr i c = a := ⟨_, rfl⟩
      rw [harr'] at ⊢
      have hlen' : hs ≤ arr'.length := by rw [← harr', swap_length]; exact hlen
      have hvi : arr'.getD i 0 = arr.getD c 0 := by
        rw [← harr']; exact swap_getD_fst arr i c (by omega) (by omega)
      have hvc : arr'.getD c 0 = arr.getD i 0 := by
        rw [← harr']; exact swap_getD_snd arr i c (by omega) (by omega)
      have hvo : ∀ p, p ≠ i → p ≠ c → arr'.getD p 0 = arr.getD p 0 := by
        intro p h1 h2
        rw [← harr']; exact swap_getD_other arr i c p h1 h2
      have H' : ∀ p, c < p → p < hs → MinHeapAt arr' hs p := by
        intro p hp hps
        obtain ⟨hL, hR⟩ := H p (by omega) hps
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [hvo (left p) (by simp only [left_eq]; omega) (by simp only [left_eq]; omega),
            hvo p (by omega) (by omega)]
          exact hL h
        · rw [hvo (right p) (by simp only [right_eq]; omega) (by simp only [right_eq]; omega),
            hvo p (by omega) (by omega)]
          exact hR h
      have IH := ih arr' hs c hlen' hclt (by omega) H'
      rcases lt_or_ge j c with hjc | hjc
      · by_cases hji : j = i
        · subst hji
          have hres : (minHeapifyLoop f arr' hs c).getD j 0 = arr.getD c 0 := by
            rw [minHeapifyLoop_getD_of_lt f arr' hs c j (by omega) (by omega), hvi]
          have key : ∀ s, s = left j ∨ s = right j → s < hs →
              arr.getD c 0 ≤ (minHeapifyLoop f arr' hs c).getD s 0 := by
            intro s hs' hslt
            by_cases hsc : s = c
            · subst hsc
              obtain ⟨hL, hR⟩ := H s hic hclt
              refine minHeapifyLoop_le_getD_start f arr' hs s (arr.getD s 0) hlen' hslt ?_ ?_ ?_
              · rw [hvc]; exact hile
              · intro h
                rw [hvo (left s) (by simp only [left_eq]; omega) (by simp only [left_eq]; omega)]
                exact hL h
              · intro h
                rw [hvo (right s) (by simp only [right_eq]; omega) (by simp only [right_eq]; omega)]
                exact hR h
            · have hslow : s < 2 * c + 1 := by
                rcases hs' with h | h <;> simp only [h, left_eq, right_eq] <;> omega
              rw [minHeapifyLoop_getD_of_lt f arr' hs c s hsc hslow,
                hvo s (by rcases hs' with h | h <;> simp only [h, left_eq, right_eq] <;> omega) hsc]
              rcases hs' with h | h
              · subst h; exact hlle hslt
              · subst h; exact hrle hslt
          exact ⟨fun h => by rw [hres]; exact key (left j) (Or.inl rfl) h,
                 fun h => by rw [hres]; exact key (right j) (Or.inr rfl) h⟩
        · have hji' : i < j := lt_of_le_of_ne hij (Ne.symm hji)
          obtain ⟨hL, hR⟩ := H j hji' hj
          have e0 : (minHeapifyLoop f arr' hs c).getD j 0 = arr.getD j 0 := by
            rw [minHeapifyLoop_getD_of_lt f arr' hs c j (by omega) (by omega),
              hvo j (by omega) (by omega)]
          have e1 : (minHeapifyLoop f arr' hs c).getD (left j) 0 = arr.getD (left j) 0 := by
            rw [minHeapifyLoop_getD_of_lt f arr' hs c (left j)
                (by simp only [left_eq]; omega) (by simp only [left_eq]; omega),
              hvo (left j) (by simp only [left_eq]; omega) (by simp only [left_eq]; omega)]
          have e2 : (minHeapifyLoop f arr' hs c).getD (right j) 0 = arr.getD (right j) 0 := by
            rw [minHeapifyLoop_getD_of_lt f arr' hs c (right j)
                (by simp only [right_eq]; omega) (by simp only [right_eq]; omega),
              hvo (right j) (by simp only [right_eq]; omega) (by simp only [right_eq]; omega)]
          exact ⟨fun h => by rw [e1, e0]; exact hL h, fun h => by rw [e2, e0]; exact hR h⟩
      · exact IH j hjc hj

/-- `MIN-HEAPIFY(arr, hs, i)` restores the min-heap property at `i`, given that
it already holds at every index above `i`. -/
theorem minHeapify_correct (arr : List Nat) (hs i : Nat) (hlen : PreHeapify arr hs) (hi : i < hs)
    (H : ∀ j, i < j → j < hs → MinHeapAt arr hs j) :
    ∀ j, i ≤ j → j < hs → MinHeapAt (minHeapify arr hs i) hs j := by
  unfold PreHeapify at hlen
  unfold minHeapify
  rw [if_neg (by push_neg; exact ⟨hi, by omega⟩)]
  exact minHeapifyLoop_correct (arr.length + 1) arr hs i hlen hi (by omega) H

theorem buildMinLoop_correct (n k : Nat) : ∀ arr : List Nat, n ≤ arr.length →
    (∀ j, k ≤ j → j < n → MinHeapAt arr n j) →
    ∀ j, j < n → MinHeapAt (buildMinLoop n k arr) n j := by
  induction k with
  | zero => intro arr _ H j hj; exact H j (Nat.zero_le _) hj
  | succ k ih =>
    intro arr hlen H
    rw [buildMinLoop]
    refine ih _ (by rw [minHeapify_length]; exact hlen) ?_
    by_cases hk : k < n
    · exact minHeapify_correct arr n k hlen hk (fun j hj hjn => H j (by omega) hjn)
    · intro j hj hjn
      exact absurd hjn (by omega)

/-! ### Heap property of the constructed heaps -/

/-- `build_max_heap` really produces a max-heap (`is_max_heap` returns `true`). -/
def buildMaxHeap_isMaxHeap_prop (arr : List Nat) : Prop :=
  isMaxHeap (buildMaxHeap arr) arr.length = true

/-- `build_min_heap` really produces a min-heap. -/
def buildMinHeap_isMinHeap_prop (arr : List Nat) : Prop :=
  isMinHeap (buildMinHeap arr) arr.length = true

theorem buildMaxHeap_isMaxHeap_thm (arr : List Nat) : buildMaxHeap_isMaxHeap_prop arr := by
  unfold buildMaxHeap_isMaxHeap_prop
  rw [isMaxHeap_iff]
  intro i hi _
  unfold buildMaxHeap
  split
  · rename_i h
    exact ⟨fun hc => by simp only [left_eq] at hc; omega,
           fun hc => by simp only [right_eq] at hc; omega⟩
  · refine buildMaxLoop_correct arr.length (arr.length / 2) arr le_rfl ?_ i hi
    intro j hj hjn
    exact ⟨fun hc => by simp only [left_eq] at hc; omega,
           fun hc => by simp only [right_eq] at hc; omega⟩

theorem buildMinHeap_isMinHeap_thm (arr : List Nat) : buildMinHeap_isMinHeap_prop arr := by
  unfold buildMinHeap_isMinHeap_prop
  rw [isMinHeap_iff]
  intro i hi _
  unfold buildMinHeap
  split
  · rename_i h
    exact ⟨fun hc => by simp only [left_eq] at hc; omega,
           fun hc => by simp only [right_eq] at hc; omega⟩
  · refine buildMinLoop_correct arr.length (arr.length / 2) arr le_rfl ?_ i hi
    intro j hj hjn
    exact ⟨fun hc => by simp only [left_eq] at hc; omega,
           fun hc => by simp only [right_eq] at hc; omega⟩

/-- All lists of length `n` with entries `< 4`. -/
def allLists : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (allLists n).flatMap fun l => [0, 1, 2, 3].map fun v => v :: l

/-- Exhaustive verification of the heap property for every array of length at
most `5` over the alphabet `{0, 1, 2, 3}`. -/
theorem buildMaxHeap_isMaxHeap_small :
    ((List.range 6).flatMap allLists).all (fun l => isMaxHeap (buildMaxHeap l) l.length) = true := by
  native_decide

theorem buildMinHeap_isMinHeap_small :
    ((List.range 6).flatMap allLists).all (fun l => isMinHeap (buildMinHeap l) l.length) = true := by
  native_decide

/-- The first entry of `build_max_heap arr` dominates the whole array (Python:
`build_max_heap([10, 20, 30, 40, 50])[0] == 50`). -/
def buildMaxHeap_root_max_prop (arr : List Nat) : Prop :=
  ∀ x ∈ arr, x ≤ (buildMaxHeap arr).getD 0 0

theorem buildMaxHeap_root_max_thm (arr : List Nat) : buildMaxHeap_root_max_prop arr := by
  intro x hx
  have hperm : (buildMaxHeap arr).Perm arr := buildMaxHeap_perm_thm arr
  have hlen : (buildMaxHeap arr).length = arr.length := buildMaxHeap_length_thm arr
  have hmem : x ∈ buildMaxHeap arr := hperm.mem_iff.mpr hx
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have hi' : i < arr.length := by omega
  have := le_root_of_isMaxHeap (buildMaxHeap arr) arr.length
    (buildMaxHeap_isMaxHeap_thm arr) (le_of_eq hlen.symm) i hi'
  rwa [List.getD_eq_getElem _ _ hi, hget] at this

/-- In a min-heap every entry dominates the root. -/
theorem root_le_of_isMinHeap (arr : List Nat) (hs : Nat) (h : isMinHeap arr hs = true)
    (hle : hs ≤ arr.length) :
    ∀ i, i < hs → arr.getD 0 0 ≤ arr.getD i 0 := by
  rw [isMinHeap_iff] at h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact le_rfl
    · have hp : parent i < i := by
        simp only [parent, if_neg (by omega : ¬ i = 0)]
        omega
      have hpi : parent i < hs := lt_trans hp hi
      have hstep : arr.getD (parent i) 0 ≤ arr.getD i 0 := by
        obtain ⟨hcl, hcr⟩ := h (parent i) hpi (lt_of_lt_of_le hpi hle)
        rcases left_or_right_parent i hpos with he | he
        · have hc := hcl (by rw [he]; exact hi)
          rwa [he] at hc
        · have hc := hcr (by rw [he]; exact hi)
          rwa [he] at hc
      exact le_trans (ih (parent i) hp hpi) hstep

/-- The first entry of `build_min_heap arr` is bounded by the whole array. -/
def buildMinHeap_root_min_prop (arr : List Nat) : Prop :=
  ∀ x ∈ arr, (buildMinHeap arr).getD 0 0 ≤ x

theorem buildMinHeap_root_min_thm (arr : List Nat) : buildMinHeap_root_min_prop arr := by
  intro x hx
  have hperm : (buildMinHeap arr).Perm arr := buildMinHeap_perm_thm arr
  have hlen : (buildMinHeap arr).length = arr.length := buildMinHeap_length_thm arr
  have hmem : x ∈ buildMinHeap arr := hperm.mem_iff.mpr hx
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have hi' : i < arr.length := by omega
  have := root_le_of_isMinHeap (buildMinHeap arr) arr.length
    (buildMinHeap_isMinHeap_thm arr) (le_of_eq hlen.symm) i hi'
  rwa [List.getD_eq_getElem _ _ hi, hget] at this

/-! ## Post-condition and correctness -/

/-- Full post-condition of `build_max_heap` / `build_min_heap`. -/
def Post_prop (arr : List Nat) : Prop :=
  buildMaxHeap_length_prop arr ∧ buildMaxHeap_perm_prop arr ∧
  buildMaxHeap_isMaxHeap_prop arr ∧ buildMaxHeap_root_max_prop arr ∧
  buildMinHeap_length_prop arr ∧ buildMinHeap_perm_prop arr ∧
  buildMinHeap_isMinHeap_prop arr ∧ buildMinHeap_root_min_prop arr

theorem correctness (arr : List Nat) (_h : Pre arr) : Post_prop arr :=
  ⟨buildMaxHeap_length_thm arr, buildMaxHeap_perm_thm arr, buildMaxHeap_isMaxHeap_thm arr,
   buildMaxHeap_root_max_thm arr, buildMinHeap_length_thm arr, buildMinHeap_perm_thm arr,
   buildMinHeap_isMinHeap_thm arr, buildMinHeap_root_min_thm arr⟩

/-! ## Imperative implementation -/

/-- Imperative sift-down step: mirrors the `while True` body of the Python
`max_heapify`, with `largest` as a mutable variable. -/
def maxHeapifyLoopImp (fuel : Nat) (arr : List Nat) (hs i : Nat) : List Nat := Id.run do
  match fuel with
  | 0 => return arr
  | f + 1 =>
    let mut largest := i
    if left i < hs ∧ arr.getD i 0 < arr.getD (left i) 0 then
      largest := left i
    if right i < hs ∧ arr.getD largest 0 < arr.getD (right i) 0 then
      largest := right i
    if largest = i then
      return arr
    return maxHeapifyLoopImp f (swap arr i largest) hs largest

def maxHeapifyImp (arr : List Nat) (hs i : Nat) : List Nat := Id.run do
  if hs ≤ i ∨ arr.length ≤ i then
    return arr
  return maxHeapifyLoopImp (arr.length + 1) arr hs i

def minHeapifyLoopImp (fuel : Nat) (arr : List Nat) (hs i : Nat) : List Nat := Id.run do
  match fuel with
  | 0 => return arr
  | f + 1 =>
    let mut smallest := i
    if left i < hs ∧ arr.getD (left i) 0 < arr.getD i 0 then
      smallest := left i
    if right i < hs ∧ arr.getD (right i) 0 < arr.getD smallest 0 then
      smallest := right i
    if smallest = i then
      return arr
    return minHeapifyLoopImp f (swap arr i smallest) hs smallest

def minHeapifyImp (arr : List Nat) (hs i : Nat) : List Nat := Id.run do
  if hs ≤ i ∨ arr.length ≤ i then
    return arr
  return minHeapifyLoopImp (arr.length + 1) arr hs i

/-- `BUILD-MAX-HEAP` with a mutable array and a downward `for` loop. -/
def buildMaxHeapImp (arr : List Nat) : List Nat := Id.run do
  let n := arr.length
  if n ≤ 1 then
    return arr
  let mut res := arr
  for i in (List.range (n / 2)).reverse do
    res := maxHeapifyImp res n i
  return res

/-- `BUILD-MIN-HEAP` with a mutable array and a downward `for` loop. -/
def buildMinHeapImp (arr : List Nat) : List Nat := Id.run do
  let n := arr.length
  if n ≤ 1 then
    return arr
  let mut res := arr
  for i in (List.range (n / 2)).reverse do
    res := minHeapifyImp res n i
  return res

/-! ## Imperative tests -/

example : buildMaxHeapImp [4, 1, 3, 2, 16, 9, 10, 14, 8, 7] = [16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by
  native_decide

example : buildMaxHeapImp [5, 3, 17, 10, 84, 19, 6, 22, 9] = [84, 22, 19, 10, 3, 17, 6, 5, 9] := by
  native_decide

example : buildMaxHeapImp [] = [] := by native_decide
example : buildMaxHeapImp [42] = [42] := by native_decide
example : buildMaxHeapImp [1, 2] = [2, 1] := by native_decide
example : isMaxHeap (buildMaxHeapImp [1, 2, 3, 4, 5, 6, 7, 8, 9]) 9 = true := by native_decide
example : isMinHeap (buildMinHeapImp [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]) 10 = true := by native_decide

#eval buildMaxHeapImp [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]
#eval buildMinHeapImp [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]

/-! ## Equivalence of the functional and the imperative implementation -/

theorem maxHeapifyLoopImp_eq (fuel : Nat) : ∀ (arr : List Nat) (hs i : Nat),
    maxHeapifyLoopImp fuel arr hs i = maxHeapifyLoop fuel arr hs i := by
  induction fuel with
  | zero => intro arr hs i; rfl
  | succ f ih =>
    intro arr hs i
    rw [maxHeapifyLoopImp, maxHeapifyLoop]
    simp only [Id.run, maxChild, maxChild₁]
    split <;> split <;> (try rw [ih]) <;>
      first
        | rfl
        | (simp only [if_true, if_pos (rfl : i = i)]; rfl)

theorem maxHeapifyImp_eq (arr : List Nat) (hs i : Nat) :
    maxHeapifyImp arr hs i = maxHeapify arr hs i := by
  unfold maxHeapifyImp maxHeapify
  simp only [Id.run, Id.run_pure, Id.run_bind]
  split
  · rfl
  · exact maxHeapifyLoopImp_eq _ _ _ _

theorem minHeapifyLoopImp_eq (fuel : Nat) : ∀ (arr : List Nat) (hs i : Nat),
    minHeapifyLoopImp fuel arr hs i = minHeapifyLoop fuel arr hs i := by
  induction fuel with
  | zero => intro arr hs i; rfl
  | succ f ih =>
    intro arr hs i
    rw [minHeapifyLoopImp, minHeapifyLoop]
    simp only [Id.run, minChild, minChild₁]
    split <;> split <;> (try rw [ih]) <;>
      first
        | rfl
        | (simp only [if_true, if_pos (rfl : i = i)]; rfl)

theorem minHeapifyImp_eq (arr : List Nat) (hs i : Nat) :
    minHeapifyImp arr hs i = minHeapify arr hs i := by
  unfold minHeapifyImp minHeapify
  simp only [Id.run, Id.run_pure, Id.run_bind]
  split
  · rfl
  · exact minHeapifyLoopImp_eq _ _ _ _

theorem buildMaxLoop_eq_foldl (n k : Nat) : ∀ arr : List Nat,
    buildMaxLoop n k arr = (List.range k).reverse.foldl (fun a i => maxHeapify a n i) arr := by
  induction k with
  | zero => intro arr; rfl
  | succ k ih =>
    intro arr
    rw [buildMaxLoop, ih, List.range_succ, List.reverse_append]
    simp

theorem buildMinLoop_eq_foldl (n k : Nat) : ∀ arr : List Nat,
    buildMinLoop n k arr = (List.range k).reverse.foldl (fun a i => minHeapify a n i) arr := by
  induction k with
  | zero => intro arr; rfl
  | succ k ih =>
    intro arr
    rw [buildMinLoop, ih, List.range_succ, List.reverse_append]
    simp

/-- The imperative `BUILD-MAX-HEAP` agrees with the functional one. -/
def buildMaxHeap_equiv_prop (arr : List Nat) : Prop := buildMaxHeapImp arr = buildMaxHeap arr

theorem buildMaxHeap_equiv_thm (arr : List Nat) : buildMaxHeap_equiv_prop arr := by
  unfold buildMaxHeap_equiv_prop buildMaxHeapImp buildMaxHeap
  split
  · rename_i h
    simp [Id.run, h]
    rfl
  · rename_i h
    rw [buildMaxLoop_eq_foldl]
    simp [Id.run, h, maxHeapifyImp_eq]
    rfl

/-- The imperative `BUILD-MIN-HEAP` agrees with the functional one. -/
def buildMinHeap_equiv_prop (arr : List Nat) : Prop := buildMinHeapImp arr = buildMinHeap arr

theorem buildMinHeap_equiv_thm (arr : List Nat) : buildMinHeap_equiv_prop arr := by
  unfold buildMinHeap_equiv_prop buildMinHeapImp buildMinHeap
  split
  · rename_i h
    simp [Id.run, h]
    rfl
  · rename_i h
    rw [buildMinLoop_eq_foldl]
    simp [Id.run, h, minHeapifyImp_eq]
    rfl

end heapsort_build_heap
end Agent
