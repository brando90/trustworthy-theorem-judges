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

theorem mid_lb {lo hi : Nat} (h : lo < hi) : lo ≤ mid lo hi := by simp only [mid]; omega

theorem mid_ub {lo hi : Nat} (h : lo < hi) : mid lo hi < hi := by simp only [mid]; omega

theorem get!_eq (a : Array Int) (i : Nat) (h : i < a.size) : a[i]! = a[i] :=
  getElem!_pos a i h

/-- Sortedness of adjacent elements upgrades to sortedness of all pairs. -/
theorem Pre_mono {a : Array Int} {t : Int} (hp : Pre a t) :
    ∀ i j : Nat, i ≤ j → j < a.size → a[i]! ≤ a[j]! := by
  intro i j hij hj
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst hi; exact le_refl _
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hij with he | hlt
      · subst he; exact le_refl _
      · have hi : i ≤ n := by omega
        have hn : n < a.size := by omega
        have h2 : a[n]! ≤ a[n + 1]! := by
          rw [get!_eq a n hn, get!_eq a (n + 1) hj]
          exact hp n hj
        exact le_trans (ih hi hn) h2

/-- Soundness of the window search: a returned index lies in the window and
carries the target.  No sortedness assumption is needed. -/
theorem go_sound (a : Array Int) (t : Int) (lo hi : Nat) :
    ∀ i, go a t lo hi = some i → lo ≤ i ∧ i < hi ∧ a[i]! = t := by
  induction lo, hi using go.induct a t with
  | case1 lo hi h heq =>
      intro i hs
      rw [go] at hs
      simp only [h, dif_pos, heq, if_pos, Option.some.injEq] at hs
      subst hs
      exact ⟨mid_lb h, mid_ub h, heq⟩
  | case2 lo hi h hne hlt ih =>
      intro i hs
      rw [go] at hs
      simp only [h, dif_pos, hne, if_neg, hlt, if_pos, not_false_eq_true] at hs
      have hh := ih i hs
      have := mid_lb h
      exact ⟨by omega, hh.2.1, hh.2.2⟩
  | case3 lo hi h hne hnlt ih =>
      intro i hs
      rw [go] at hs
      simp only [h, dif_pos, hne, if_neg, hnlt, not_false_eq_true] at hs
      have hh := ih i hs
      have := mid_ub h
      exact ⟨hh.1, by omega, hh.2.2⟩
  | case4 lo hi h =>
      intro i hs
      rw [go] at hs
      simp [h] at hs

/-- Completeness of the window search: on a sorted array, `none` means the target
occurs nowhere in the window. -/
theorem go_complete (a : Array Int) (t : Int) (hp : Pre a t) (lo hi : Nat) :
    hi ≤ a.size → go a t lo hi = none → ∀ i, lo ≤ i → i < hi → a[i]! ≠ t := by
  induction lo, hi using go.induct a t with
  | case1 lo hi h heq =>
      intro _ hs
      rw [go] at hs
      simp only [h, dif_pos, heq, if_pos] at hs
      exact absurd hs (by simp)
  | case2 lo hi h hne hlt ih =>
      intro hsz hs
      rw [go] at hs
      simp only [h, dif_pos, hne, if_neg, hlt, if_pos, not_false_eq_true] at hs
      intro i hi1 hi2
      rcases Nat.lt_or_ge i (mid lo hi + 1) with hc | hc
      · have hms : mid lo hi < a.size := lt_of_lt_of_le (mid_ub h) hsz
        have : a[i]! ≤ a[mid lo hi]! := Pre_mono hp i (mid lo hi) (by omega) hms
        omega
      · exact ih hsz hs i hc hi2
  | case3 lo hi h hne hnlt ih =>
      intro hsz hs
      rw [go] at hs
      simp only [h, dif_pos, hne, if_neg, hnlt, not_false_eq_true] at hs
      intro i hi1 hi2
      rcases Nat.lt_or_ge i (mid lo hi) with hc | hc
      · exact ih (le_of_lt (lt_of_lt_of_le (mid_ub h) hsz)) hs i hi1 hc
      · have his : i < a.size := lt_of_lt_of_le hi2 hsz
        have : a[mid lo hi]! ≤ a[i]! := Pre_mono hp (mid lo hi) i hc his
        omega
  | case4 lo hi h =>
      intro _ _ i hi1 hi2
      omega

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

theorem found_thm (a : Array Int) (t : Int) : found_prop a t := by
  intro i hs
  rw [binarySearch] at hs
  have hh := go_sound a t 0 a.size i hs
  have hi : i < a.size := hh.2.1
  exact ⟨hi, by rw [← get!_eq a i hi]; exact hh.2.2⟩

theorem notFound_thm (a : Array Int) (t : Int) (hp : Pre a t) : notFound_prop a t := by
  intro hs i hi
  rw [binarySearch] at hs
  have hh := go_complete a t hp 0 a.size (le_refl _) hs i (Nat.zero_le i) hi
  rwa [get!_eq a i hi] at hh

theorem empty_thm (a : Array Int) (t : Int) : empty_prop a t := by
  intro h
  rw [binarySearch, go]
  simp [h]

theorem mem_iff_thm (a : Array Int) (t : Int) (hp : Pre a t) : mem_iff_prop a t := by
  constructor
  · intro hs
    rcases Option.isSome_iff_exists.mp hs with ⟨i, hi⟩
    rcases found_thm a t i hi with ⟨hlt, hval⟩
    exact ⟨i, hlt, hval⟩
  · rintro ⟨i, hlt, hval⟩
    rcases hres : binarySearch a t with _ | r
    · exact absurd hval (notFound_thm a t hp hres i hlt)
    · rfl

/-- The full post-condition of the Python function. -/
def Post_prop (a : Array Int) (t : Int) : Prop :=
  found_prop a t ∧ notFound_prop a t ∧ empty_prop a t ∧ mem_iff_prop a t

/-- Correctness: on inputs satisfying the precondition (i.e. those for which the
Python function does not raise `ValueError`), the result satisfies the
post-condition. -/
theorem correctness_thm (a : Array Int) (t : Int) (hp : Pre a t) : Post_prop a t :=
  ⟨found_thm a t, notFound_thm a t hp, empty_thm a t, mem_iff_thm a t hp⟩

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
    ∀ (l : List Nat) (lo hi : Nat), hi - lo ≤ l.length → impLoop a t lo hi l = go a t lo hi := by
  intro l
  induction l with
  | nil =>
      intro lo hi h
      simp only [impLoop, Id.run, List.forIn_nil]
      rw [go]
      simp only [List.length_nil, Nat.le_zero] at h
      have hn : ¬ lo < hi := by omega
      simp [hn]
      rfl
  | cons x xs ih =>
      intro lo hi h
      simp only [impLoop, Id.run, List.forIn_cons] at *
      simp only [List.length_cons] at h
      by_cases hlt : lo < hi
      · have hb1 := mid_lb hlt
        have hb2 := mid_ub hlt
        by_cases he : a[mid lo hi]! = t
        · rw [go]
          simp [hlt, he]
          rfl
        · by_cases hl2 : a[mid lo hi]! < t
          · rw [go]
            simp only [hlt, dif_pos, he, if_neg, hl2, if_pos, not_false_eq_true]
            exact ih (mid lo hi + 1) hi (by omega)
          · rw [go]
            simp only [hlt, dif_pos, he, if_neg, hl2, if_neg, not_false_eq_true]
            exact ih lo (mid lo hi) (by omega)
      · rw [go]
        simp [hlt]
        rfl

/-- The imperative implementation computes exactly the functional one. -/
theorem binarySearch_eq_imp (a : Array Int) (t : Int) :
    binarySearch a t = binarySearchImp a t := by
  rw [binarySearchImp, impLoop_eq a t (List.range a.size) 0 a.size (by simp), binarySearch]

end binary_search
end Agent
