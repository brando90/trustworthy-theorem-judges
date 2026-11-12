import Mathlib

/-!
# HumanEval/35 — `max_element`

Formalization of the Python program

```python
def max_element(l: list):
    m = l[0]
    for e in l:
        if e > m:
            m = e
    return m
```

which returns the maximum element of a (nonempty) list.  The list elements
are modeled as `Int` since the doctests use negative numbers.

The file contains:
* a functional implementation `maxElement` (a fold of `max` over the tail,
  starting from the head — the same result as the Python loop, since
  re-processing the head `x` only computes `max x x = x`),
* unit tests, a pre-condition, property propositions with proofs,
* a post-condition (conjunction of the properties) and property-based tests,
* the correctness theorem `Pre → Post`,
* an imperative implementation `maxElementImp` using `Id.run` with mutable
  state, its tests, and an equivalence proof between the two implementations.
-/

namespace humaneval_35_max_element

/-! ## Functional implementation -/

/-- Return the maximum element of a nonempty list.  For the empty list —
excluded by the pre-condition (Python would crash on `l[0]`) — we return `0`. -/
def maxElement : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

/-! ## Unit tests -/

example : maxElement [1, 2, 3] = 3 := by native_decide
example : maxElement [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : maxElement [7] = 7 := by native_decide
example : maxElement [-3, -7, -1] = -1 := by native_decide

#eval maxElement [1, 2, 3]                          -- 3
#eval maxElement [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]  -- 124

/-! ## Pre-condition -/

/-- The Python program reads `l[0]`, so the list must be nonempty. -/
def Pre (l : List Int) : Prop := l ≠ []

/-! ## Auxiliary lemmas about folding `max` -/

/-- The accumulator is a lower bound for the final fold result. -/
theorem le_foldl_max (l : List Int) (a : Int) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    exact le_trans (le_max_left a x) (ih (max a x))

/-- Every element of the list is bounded by the final fold result. -/
theorem foldl_max_le_of_mem (l : List Int) (a e : Int) (he : e ∈ l) :
    e ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => cases he
  | cons x xs ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp he with h1 | h
    · rw [h1]
      exact le_trans (le_max_right a x) (le_foldl_max xs (max a x))
    · exact ih (max a x) h

/-- The final fold result is either the accumulator or an element of the list. -/
theorem foldl_max_mem (l : List Int) (a : Int) : l.foldl max a ∈ a :: l := by
  induction l generalizing a with
  | nil =>
    rw [List.foldl_nil]
    exact List.mem_cons_self
  | cons x xs ih =>
    rw [List.foldl_cons]
    have h := ih (max a x)
    rcases max_choice a x with hmax | hmax <;> rw [hmax] at h ⊢
    · rcases List.mem_cons.mp h with h1 | h1
      · rw [h1]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1)
    · rcases List.mem_cons.mp h with h1 | h1
      · rw [h1]; exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1)

/-! ## Property propositions and their proofs -/

/-- The result belongs to the input list. -/
def maxElement_mem_prop (l : List Int) : Prop := Pre l → maxElement l ∈ l

/-- The result is an upper bound for all elements of the input list. -/
def maxElement_ge_prop (l : List Int) : Prop :=
  Pre l → ∀ e ∈ l, e ≤ maxElement l

theorem maxElement_mem_thm (l : List Int) : maxElement_mem_prop l := by
  intro h
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => exact foldl_max_mem xs x

theorem maxElement_ge_thm (l : List Int) : maxElement_ge_prop l := by
  intro h
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    intro e he
    show e ≤ xs.foldl max x
    rcases List.mem_cons.mp he with h1 | h2
    · rw [h1]
      exact le_foldl_max xs x
    · exact foldl_max_le_of_mem xs x e h2

/-! ## Post-condition -/

/-- Post-condition: conjunction of the stated properties. -/
def Post_prop (l : List Int) : Prop := maxElement_mem_prop l ∧ maxElement_ge_prop l

/-! ## Property-based tests -/

/-- Executable Boolean form of the post-condition on one list. -/
def checkPost (l : List Int) : Bool :=
  l.contains (maxElement l) && l.all (fun e => decide (e ≤ maxElement l))

-- Randomized PBT (Plausible ships with Mathlib): membership property.
#eval Plausible.Testable.check (∀ l : List Int, l ≠ [] → maxElement l ∈ l)

-- Randomized PBT: upper-bound property.
#eval Plausible.Testable.check (∀ l : List Int, l ≠ [] → ∀ e ∈ l, e ≤ maxElement l)

-- Randomized PBT: the post-condition (both properties together).
#eval Plausible.Testable.check (∀ l : List Int, l ≠ [] →
  maxElement l ∈ l ∧ (∀ e ∈ l, e ≤ maxElement l))

-- Bounded PBT: exhaustive over all lists of length 1–3 with entries in {-2,…,2}.
def atoms : List Int := [-2, -1, 0, 1, 2]
def len1 : List (List Int) := atoms.map (fun a => [a])
def len2 : List (List Int) := len1.flatMap (fun l => atoms.map (fun a => a :: l))
def len3 : List (List Int) := len2.flatMap (fun l => atoms.map (fun a => a :: l))
def smallLists : List (List Int) := len1 ++ len2 ++ len3

example : smallLists.all (fun l => l.contains (maxElement l)) = true := by native_decide
example : smallLists.all (fun l => l.all (fun e => decide (e ≤ maxElement l))) = true := by
  native_decide
example : smallLists.all checkPost = true := by native_decide

/-! ## Correctness theorem: `Pre → Post` -/

theorem maxElement_correct (l : List Int) (_h : Pre l) : Post_prop l :=
  ⟨maxElement_mem_thm l, maxElement_ge_thm l⟩

/-! ## Imperative implementation (`Id.run` with mutable state) -/

/-- Imperative version mirroring the Python loop: start from the head and scan
the tail with a mutable accumulator. -/
def maxElementImp (l : List Int) : Int := Id.run do
  match l with
  | [] => return 0
  | x :: xs =>
    let mut m := x
    for e in xs do
      if e > m then
        m := e
    return m

-- Imperative tests
example : maxElementImp [1, 2, 3] = 3 := by native_decide
example : maxElementImp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide

#eval maxElementImp [1, 2, 3]                          -- 3
#eval maxElementImp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]  -- 124

/-! ## Equivalence of the two implementations -/

/-- One loop step equals `max`. -/
theorem step_eq_max (m e : Int) : (if e > m then e else m) = max m e := by
  by_cases h : m < e
  · rw [if_pos h]; exact (max_eq_right (le_of_lt h)).symm
  · rw [if_neg h]; push_neg at h; exact (max_eq_left h).symm

/-- The mutable `for` loop computes a left fold of the update step. -/
theorem maxElementImp_loop (xs : List Int) (init : Int) :
    (Id.run do
      let mut m := init
      for e in xs do
        if e > m then m := e
      return m) = xs.foldl (fun m e => if e > m then e else m) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons y ys ih =>
    simp only [pure_bind, bind_pure, Id.run]
    rw [List.foldl_cons, List.forIn_cons]
    split_ifs with h
    · simpa only [pure_bind, bind_pure, Id.run] using ih y
    · simpa only [pure_bind, bind_pure, Id.run] using ih init

theorem maxElementImp_eq (l : List Int) : maxElementImp l = maxElement l := by
  cases l with
  | nil => rfl
  | cons x xs =>
    show (Id.run do
        let mut m := x
        for e in xs do
          if e > m then m := e
        return m) = xs.foldl max x
    rw [maxElementImp_loop]
    congr 1
    funext m e
    exact step_eq_max m e

-- Equivalence PBT (bounded).
example : smallLists.all (fun l => maxElementImp l == maxElement l) = true := by native_decide

end humaneval_35_max_element
