import Mathlib
namespace Agent

/-!
# Binary search over a sorted array of integers

This file is a Lean 4 formalization of the Python program `binary_search.py`.

The Python function takes a list of integers `arr` that is sorted in non-decreasing
order together with an integer `target`, and returns the index of an occurrence of
`target` in `arr`, or `None` if `target` does not occur.  An empty list yields `None`.
Inputs violating the precondition (non-list, non-integer elements, or an unsorted
list) make the Python function raise `ValueError`; here that precondition is modelled
by the predicate `Pre`, and the correctness statement is `Pre → Post`.

Python's list is modelled by `Array Int` (indices are `Nat`, mirroring Python's
`0 ≤ i < len(arr)` indexing), and `Optional[int]` by `Option Nat`.

The Python loop maintains a closed index interval `[left, right]`; here we use the
equivalent half-open interval `[lo, hi)` with `hi = right + 1`, so that all indices
stay in `Nat`.  With that translation Python's `mid = (left + right) // 2` becomes
`mid lo hi = (lo + hi - 1) / 2`, so the two implementations pick exactly the same
midpoints and therefore return exactly the same index (this matters when the array
contains duplicates).

Contents:
* `go` / `binarySearch` — the functional implementation;
* `Pre` — the precondition (the array is sorted in non-decreasing order);
* `found_prop`, `notFound_prop`, `empty_prop`, `mem_iff_prop` — the individual
  post-conditions, with a theorem for each;
* `Post_prop` and `correctness_thm : Pre → Post`;
* `impLoop` / `binarySearchImp` — an imperative implementation written with
  `Id.run do`, a mutable `lo`/`hi`/`res` state and a bounded loop with `break`;
* `binarySearch_eq_imp` — the functional and imperative versions agree.
-/

namespace binary_search

/-! ## Functional implementation -/

/-- The midpoint Python computes as `(left + right) // 2`, expressed for the
half-open interval `[lo, hi)` (i.e. `right = hi - 1`). -/
def mid (lo hi : Nat) : Nat := (lo + hi - 1) / 2

/-- One "iteration" of Python's `while left <= right` loop, searching for `t`
inside the index window `[lo, hi)` of `a`. -/
def go (a : Array Int) (t : Int) (lo hi : Nat) : Option Nat :=
  if h : lo < hi then
    if a[mid lo hi]! = t then some (mid lo hi)
    else if a[mid lo hi]! < t then go a t (mid lo hi + 1) hi
    else go a t lo (mid lo hi)
  else
    none
termination_by hi - lo
decreasing_by all_goals (simp only [mid]; omega)

/-- Functional counterpart of Python's `binary_search`. -/
def binarySearch (a : Array Int) (t : Int) : Option Nat := go a t 0 a.size

/-! ## Unit tests (mirroring the Python `check` function) -/

-- Basic functionality tests
example : binarySearch #[1, 2, 3, 4, 5] 1 = some 0 := by native_decide
example : binarySearch #[1, 2, 3, 4, 5] 3 = some 2 := by native_decide
example : binarySearch #[1, 2, 3, 4, 5] 5 = some 4 := by native_decide
example : binarySearch #[1, 2, 3, 4, 5] 6 = none := by native_decide
example : binarySearch #[1, 2, 3, 4, 5] 0 = none := by native_decide

-- Edge cases
example : binarySearch #[] 1 = none := by native_decide
example : binarySearch #[5] 5 = some 0 := by native_decide
example : binarySearch #[5] 3 = none := by native_decide

-- Larger arrays
example : binarySearch #[1, 3, 5, 7, 9] 3 = some 1 := by native_decide
example : binarySearch #[1, 3, 5, 7, 9] 7 = some 3 := by native_decide
example : binarySearch #[1, 3, 5, 7, 9] 4 = none := by native_decide
example : binarySearch #[10, 20, 30, 40, 50, 60] 60 = some 5 := by native_decide
example : binarySearch #[10, 20, 30, 40, 50, 60] 10 = some 0 := by native_decide

-- Duplicates: any index `r` with `2 ≤ r ≤ 4` and `arr[r] = 3` is acceptable
/-- The array with duplicates used by the Python test. -/
def dupArr : Array Int := #[1, 2, 3, 3, 3, 4, 5]

example :
    (binarySearch dupArr 3).any (fun r => 2 ≤ r && r ≤ 4 && dupArr[r]! == (3 : Int)) = true := by
  native_decide

-- Large sorted array
example : binarySearch ((Array.range 100).map (fun n : Nat => (n : Int))) 49 = some 49 := by native_decide
example : binarySearch ((Array.range 100).map (fun n : Nat => (n : Int))) 99 = some 99 := by native_decide
example : binarySearch ((Array.range 100).map (fun n : Nat => (n : Int))) 100 = none := by native_decide

-- Two element arrays
example : binarySearch #[1, 2] 1 = some 0 := by native_decide
example : binarySearch #[1, 2] 2 = some 1 := by native_decide
example : binarySearch #[1, 2] 3 = none := by native_decide

#eval binarySearch #[1, 2, 3, 4, 5] 3
#eval binarySearch #[1, 2, 3, 4, 5] 6
#eval binarySearch #[] 1

/-! ## Pre-condition -/

/-- Python's `pre`: the array must be sorted in non-decreasing order.  (The
`isinstance` checks of the Python source are captured by the Lean types
`Array Int` and `Int`.)  A Python call that violates this raises `ValueError`. -/
def Pre (a : Array Int) (_target : Int) : Prop :=
  ∀ i : Nat, (h : i + 1 < a.size) → a[i]'(by omega) ≤ a[i + 1]

-- The precondition holds for a sorted array …
example : Pre #[(1 : Int), 2, 3, 4, 5] 3 := by
  intro i h
  have h4 : i < 4 := by simp at h; omega
  interval_cases i <;> simp

-- … and fails for the unsorted negative test input `[3, 2, 1]`.
example : ¬ Pre #[(3 : Int), 2, 1] 2 := by
  intro h
  have h0 := h 0 (by decide)
  exact absurd h0 (by decide)

/-! ## Auxiliary lemmas -/

theorem mid_lb {lo hi : Nat} (h : lo < hi) : lo ≤ mid lo hi := by sorry

theorem mid_ub {lo hi : Nat} (h : lo < hi) : mid lo hi < hi := by sorry

theorem get!_eq (a : Array Int) (i : Nat) (h : i < a.size) : a[i]! = a[i] := by sorry

/-- Sortedness of adjacent elements upgrades to sortedness of all pairs. -/
theorem Pre_mono {a : Array Int} {t : Int} (hp : Pre a t) :
    ∀ i j : Nat, i ≤ j → j < a.size → a[i]! ≤ a[j]! := by sorry

/-- Soundness of the window search: a returned index lies in the window and
carries the target.  No sortedness assumption is needed. -/
theorem go_sound (a : Array Int) (t : Int) (lo hi : Nat) :
    ∀ i, go a t lo hi = some i → lo ≤ i ∧ i < hi ∧ a[i]! = t := by sorry

/-- Completeness of the window search: on a sorted array, `none` means the target
occurs nowhere in the window. -/
theorem go_complete (a : Array Int) (t : Int) (hp : Pre a t) (lo hi : Nat) :
    hi ≤ a.size → go a t lo hi = none → ∀ i, lo ≤ i → i < hi → a[i]! ≠ t := by sorry

/-! ## Post-condition properties -/

/-- If a result is returned it is a legal index of `a` holding the target
(`arr[result] == target`, as asserted by the Python tests). -/
def found_prop (a : Array Int) (t : Int) : Prop :=
  ∀ i : Nat, binarySearch a t = some i → ∃ h : i < a.size, a[i] = t

/-- If `None` is returned, the target does not occur anywhere in the array. -/
def notFound_prop (a : Array Int) (t : Int) : Prop :=
  binarySearch a t = none → ∀ i : Nat, (h : i < a.size) → a[i] ≠ t

/-- `binary_search([], x)` is `None`. -/
def empty_prop (a : Array Int) (t : Int) : Prop :=
  a.size = 0 → binarySearch a t = none

/-- The search succeeds exactly when the target occurs in the array. -/
def mem_iff_prop (a : Array Int) (t : Int) : Prop :=
  (binarySearch a t).isSome = true ↔ ∃ i : Nat, ∃ h : i < a.size, a[i] = t

theorem found_thm (a : Array Int) (t : Int) : found_prop a t := by sorry

theorem notFound_thm (a : Array Int) (t : Int) (hp : Pre a t) : notFound_prop a t := by sorry

theorem empty_thm (a : Array Int) (t : Int) : empty_prop a t := by sorry

theorem mem_iff_thm (a : Array Int) (t : Int) (hp : Pre a t) : mem_iff_prop a t := by sorry

/-- The full post-condition of the Python function. -/
def Post_prop (a : Array Int) (t : Int) : Prop :=
  found_prop a t ∧ notFound_prop a t ∧ empty_prop a t ∧ mem_iff_prop a t

/-- Correctness: on inputs satisfying the precondition (i.e. those for which the
Python function does not raise `ValueError`), the result satisfies the
post-condition. -/
theorem correctness_thm (a : Array Int) (t : Int) (hp : Pre a t) : Post_prop a t := by sorry

/-! ## Imperative implementation

A direct transcription of the Python `while` loop using `Id.run do` with mutable
`lo`, `hi` and `res` variables and an explicit `break`.  The loop is run over a
`fuel` list; since the window `[lo, hi)` shrinks by at least one index per
iteration, `List.range a.size` supplies more than enough iterations. -/

def impLoop (a : Array Int) (t : Int) (lo0 hi0 : Nat) (fuel : List Nat) : Option Nat := Id.run do
  let mut lo : Nat := lo0
  let mut hi : Nat := hi0
  let mut res : Option Nat := none
  for _ in fuel do
    if lo < hi then
      let m := mid lo hi
      let v := a[m]!
      if v = t then
        res := some m
        break
      else if v < t then
        lo := m + 1
      else
        hi := m
    else
      break
  return res

/-- Imperative counterpart of Python's `binary_search`. -/
def binarySearchImp (a : Array Int) (t : Int) : Option Nat :=
  impLoop a t 0 a.size (List.range a.size)

/-! ## Imperative unit tests -/

example : binarySearchImp #[1, 2, 3, 4, 5] 1 = some 0 := by native_decide
example : binarySearchImp #[1, 2, 3, 4, 5] 3 = some 2 := by native_decide
example : binarySearchImp #[1, 2, 3, 4, 5] 5 = some 4 := by native_decide
example : binarySearchImp #[1, 2, 3, 4, 5] 6 = none := by native_decide
example : binarySearchImp #[1, 2, 3, 4, 5] 0 = none := by native_decide
example : binarySearchImp #[] 1 = none := by native_decide
example : binarySearchImp #[5] 5 = some 0 := by native_decide
example : binarySearchImp #[5] 3 = none := by native_decide
example : binarySearchImp #[1, 3, 5, 7, 9] 3 = some 1 := by native_decide
example : binarySearchImp #[1, 3, 5, 7, 9] 7 = some 3 := by native_decide
example : binarySearchImp #[1, 3, 5, 7, 9] 4 = none := by native_decide
example : binarySearchImp #[10, 20, 30, 40, 50, 60] 60 = some 5 := by native_decide
example : binarySearchImp #[10, 20, 30, 40, 50, 60] 10 = some 0 := by native_decide
example : binarySearchImp ((Array.range 100).map (fun n : Nat => (n : Int))) 49 = some 49 := by
  native_decide
example : binarySearchImp ((Array.range 100).map (fun n : Nat => (n : Int))) 100 = none := by
  native_decide
example : binarySearchImp #[1, 2] 1 = some 0 := by native_decide
example : binarySearchImp #[1, 2] 2 = some 1 := by native_decide
example : binarySearchImp #[1, 2] 3 = none := by native_decide

#eval binarySearchImp #[1, 2, 3, 4, 5] 3
#eval binarySearchImp #[1, 3, 5, 7, 9] 4

/-! ## Equivalence of the functional and imperative implementations -/

theorem impLoop_eq (a : Array Int) (t : Int) :
    ∀ (l : List Nat) (lo hi : Nat), hi - lo ≤ l.length → impLoop a t lo hi l = go a t lo hi := by sorry

/-- The imperative implementation computes exactly the functional one. -/
theorem binarySearch_eq_imp (a : Array Int) (t : Int) :
    binarySearch a t = binarySearchImp a t := by sorry

end binary_search
end Agent
