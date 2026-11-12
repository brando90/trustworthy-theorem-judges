import Mathlib

/-!
# HumanEval 35: maximum list element

This file formalizes the Python `max_element` routine over lists of integers.
As in Python, meaningful calls require a nonempty list; the total Lean function
uses `0` only to give an explicit value to the otherwise-invalid empty case.
-/

namespace humaneval_35_max_element

/-- Return the greatest integer in a nonempty list. -/
def maxElement : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

example : maxElement [1, 2, 3] = 3 := by native_decide
example : maxElement [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by
  native_decide

#eval maxElement [1, 2, 3]
#eval maxElement [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

/-- The source program's indexing operation requires a nonempty input. -/
def Pre (l : List Int) : Prop := l ≠ []

/-- On a valid input, the returned value is one of the input elements. -/
def result_mem_prop (l : List Int) : Prop := maxElement l ∈ l

/-- Every input element is at most the returned value. -/
def upper_bound_prop (l : List Int) : Prop :=
  ∀ e ∈ l, e ≤ maxElement l

private theorem maxElement_spec (l : List Int) (h : Pre l) :
    result_mem_prop l ∧ upper_bound_prop l := by
  cases l with
  | nil => simp [Pre] at h
  | cons x xs =>
      have hmax : (x :: xs).max? = some (maxElement (x :: xs)) := by
        simp [List.max?, maxElement]
      constructor
      · exact List.max?_mem (fun a b : Int => max_choice a b) hmax
      · exact
          (List.max?_le_iff
            (fun a b c : Int => max_le_iff) hmax).mp (le_refl _)

theorem result_mem_thm (l : List Int) (h : Pre l) : result_mem_prop l := by
  exact (maxElement_spec l h).1

theorem upper_bound_thm (l : List Int) (h : Pre l) : upper_bound_prop l := by
  exact (maxElement_spec l h).2

/-- The full postcondition characterizing the result as a list maximum. -/
def Post_prop (l : List Int) : Prop :=
  result_mem_prop l ∧ upper_bound_prop l

theorem maxElement_correct (l : List Int) : Pre l → Post_prop l := by
  intro h
  exact maxElement_spec l h

/-- An imperative rendition using mutable state inside `Id`. -/
def maxElementImperative (l : List Int) : Int := Id.run do
  match l with
  | [] => return 0
  | x :: xs =>
      let mut m := x
      for e in xs do
        if e > m then
          m := e
      return m

example : maxElementImperative [1, 2, 3] = 3 := by native_decide
example : maxElementImperative [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by
  native_decide

#eval maxElementImperative [1, 2, 3]
#eval maxElementImperative [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

private def maxStep {xs : List Int} (e : Int) (_ : e ∈ xs) (current : Int) :
    Id (ForInStep Int) :=
  if e > current then pure (.yield e) else pure (.yield current)

private theorem forInPrime_max_eq_foldl (xs : List Int) (m : Int) :
    (forIn' xs m (@maxStep xs)).run = xs.foldl max m := by
  induction xs generalizing m with
  | nil => rfl
  | cons e es ih =>
      rw [List.forIn'_cons]
      by_cases h : e > m
      · simp only [maxStep, h, ↓reduceIte]
        change (forIn' es e (@maxStep es)).run = List.foldl max m (e :: es)
        rw [ih]
        simp [max_eq_right (le_of_lt h)]
      · simp only [maxStep, h, ↓reduceIte]
        change (forIn' es m (@maxStep es)).run = List.foldl max m (e :: es)
        rw [ih]
        simp [max_eq_left (le_of_not_gt h)]

private theorem imperativeLoop_eq_foldl (xs : List Int) (m : Int) :
    (Id.run do
      let mut current := m
      for e in xs do
        if e > current then
          current := e
      return current) = xs.foldl max m := by
  change (forIn' xs m (@maxStep xs)).run = xs.foldl max m
  exact forInPrime_max_eq_foldl xs m

theorem functional_eq_imperative (l : List Int) :
    maxElement l = maxElementImperative l := by
  cases l with
  | nil => rfl
  | cons x xs =>
      change
        xs.foldl max x =
          (Id.run do
            let mut m := x
            for e in xs do
              if e > m then
                m := e
            return m)
      exact (imperativeLoop_eq_foldl xs x).symm

end humaneval_35_max_element
