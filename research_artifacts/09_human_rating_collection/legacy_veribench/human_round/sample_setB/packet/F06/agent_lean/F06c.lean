import Mathlib

/-!
# HumanEval/35 -- `max_element`

Translation of the Python program `humaneval_35_max_element.py`:

```python
def max_element(l: list):
    m = l[0]
    for e in l:
        if e > m:
            m = e
    return m
```

The Python function starts with `m = l[0]` (so the list must be non-empty, otherwise an
`IndexError` is raised) and then scans the whole list, replacing `m` whenever a strictly
larger element is found.  Elements are modelled as `Int`.

* `maxElement` is the functional implementation: the loop is a left fold of the loop body
  `step` over the list, starting from the first element.
* `maxElementImp` is the imperative implementation (`Id.run do` with a mutable variable),
  mirroring the Python code line by line.

On the empty list (outside the precondition `Pre`) both implementations return the
default value `0`.
-/

namespace humaneval_35_max_element

/-- One iteration of the Python loop body: `if e > m: m = e`. -/
def step (m e : Int) : Int := if e > m then e else m

/-- Functional implementation of `max_element`.
`m = l[0]` is modelled by `l.headD 0` (the default `0` is only reached on the empty list,
which Python rejects with an `IndexError`), and `for e in l: ...` is a left fold of `step`. -/
def maxElement (l : List Int) : Int :=
  l.foldl step (l.headD 0)

-- Unit tests (docstring examples and the `check` function of the Python file)
example : maxElement [1, 2, 3] = 3 := by native_decide
example : maxElement [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide
example : maxElement [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : maxElement [-7] = -7 := by native_decide
example : maxElement [4, 4, 4] = 4 := by native_decide
#eval maxElement [1, 2, 3]
#eval maxElement [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

/-- Pre-condition: the list is non-empty (Python's `l[0]` raises `IndexError` otherwise). -/
def Pre (l : List Int) : Prop := l ≠ []

/-! ### Helper lemmas about the loop body and its fold -/

theorem step_self (m : Int) : step m m = m := by
  simp [step]

theorem step_eq_max (m e : Int) : step m e = max m e := by
  simp only [step, max_def]
  split_ifs <;> omega

/-- The accumulator never decreases. -/
theorem le_foldl_step (xs : List Int) (m : Int) : m ≤ xs.foldl step m := by
  induction xs generalizing m with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    by_cases h : y > m
    · rw [show step m y = y from if_pos h]
      exact le_trans (le_of_lt h) (ih y)
    · rw [show step m y = m from if_neg h]
      exact ih m

/-- The fold result is the initial accumulator or an element of the list. -/
theorem foldl_step_mem (xs : List Int) (m : Int) :
    xs.foldl step m = m ∨ xs.foldl step m ∈ xs := by
  induction xs generalizing m with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    by_cases h : y > m
    · rw [show step m y = y from if_pos h]
      rcases ih y with h' | h'
      · right; rw [h']; simp
      · right; exact List.mem_cons_of_mem y h'
    · rw [show step m y = m from if_neg h]
      rcases ih m with h' | h'
      · left; exact h'
      · right; exact List.mem_cons_of_mem y h'

/-- Every element of the list is bounded by the fold result. -/
theorem foldl_step_ub (xs : List Int) (m : Int) : ∀ x ∈ xs, x ≤ xs.foldl step m := by
  induction xs generalizing m with
  | nil => simp
  | cons y ys ih =>
    intro x hx
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with hxy | hx
    · subst hxy
      by_cases h : x > m
      · rw [show step m x = x from if_pos h]
        exact le_foldl_step ys x
      · rw [show step m x = m from if_neg h]
        exact le_trans (not_lt.mp h) (le_foldl_step ys m)
    · by_cases h : y > m
      · rw [show step m y = y from if_pos h]
        exact ih y x hx
      · rw [show step m y = m from if_neg h]
        exact ih m x hx

/-- Unfolding `maxElement` on a non-empty list: the first iteration (`e = l[0]`) leaves
`m = l[0]` unchanged. -/
theorem maxElement_cons (x : Int) (xs : List Int) :
    maxElement (x :: xs) = xs.foldl step x := by
  simp only [maxElement, List.headD_cons, List.foldl_cons, step_self]

/-! ### Properties -/

/-- Property: the result is an element of the list. -/
def mem_prop (l : List Int) : Prop := maxElement l ∈ l

theorem mem_thm (l : List Int) (h : Pre l) : mem_prop l := by
  unfold mem_prop
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    rw [maxElement_cons]
    rcases foldl_step_mem xs x with h' | h'
    · rw [h']; simp
    · exact List.mem_cons_of_mem x h'

/-- Property: the result is an upper bound of every element of the list. -/
def upper_bound_prop (l : List Int) : Prop := ∀ x ∈ l, x ≤ maxElement l

theorem upper_bound_thm (l : List Int) (h : Pre l) : upper_bound_prop l := by
  unfold upper_bound_prop
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    rw [maxElement_cons]
    intro y hy
    rcases List.mem_cons.mp hy with hyx | hy
    · subst hyx
      exact le_foldl_step xs _
    · exact foldl_step_ub xs x y hy

/-- Property: the result coincides with the library maximum `List.max?`. -/
def max?_prop (l : List Int) : Prop := l.max? = some (maxElement l)

theorem max?_thm (l : List Int) (h : Pre l) : max?_prop l := by
  unfold max?_prop
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    have hstep : step = max := funext fun m => funext fun e => step_eq_max m e
    rw [maxElement_cons, List.max?_cons', hstep]

/-- Property: the maximum is unique -- any element of the list that bounds all elements is
the result. -/
def unique_prop (l : List Int) : Prop :=
  ∀ m ∈ l, (∀ x ∈ l, x ≤ m) → m = maxElement l

theorem unique_thm (l : List Int) (h : Pre l) : unique_prop l := by
  intro m hm hub
  exact le_antisymm (upper_bound_thm l h m hm) (hub _ (mem_thm l h))

/-- Property: the result also agrees with Mathlib's `List.maximum`. -/
def maximum_prop (l : List Int) : Prop := l.maximum = (maxElement l : WithBot Int)

theorem maximum_thm (l : List Int) (h : Pre l) : maximum_prop l :=
  List.maximum_eq_coe_iff.mpr ⟨mem_thm l h, upper_bound_thm l h⟩

/-- Post-condition: conjunction of all properties. -/
def Post_prop (l : List Int) : Prop :=
  mem_prop l ∧ upper_bound_prop l ∧ max?_prop l ∧ unique_prop l ∧ maximum_prop l

/-! ### Property-based tests -/

-- Randomized PBTs (Plausible).  A non-empty list is written `x :: xs`, so the quantified
-- inputs range over exactly the admissible inputs (`Pre`) and no sample is discarded.
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int), maxElement (x :: xs) ∈ x :: xs)
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int), (x :: xs).all (fun y => decide (y ≤ maxElement (x :: xs))) = true)
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int), (x :: xs).max? = some (maxElement (x :: xs)))
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    (x :: xs).all (fun m =>
      !((x :: xs).all (fun y => decide (y ≤ m))) || decide (m = maxElement (x :: xs))) = true)
-- `maximum_prop` is stated over `WithBot Int`; its executable counterpart is `max?_prop`
-- (`List.max?`), tested above and below.
-- Post-condition (executable Boolean form of the conjunction):
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    (maxElement (x :: xs) ∈ x :: xs ∧
     (x :: xs).all (fun y => decide (y ≤ maxElement (x :: xs))) = true ∧
     (x :: xs).max? = some (maxElement (x :: xs)) ∧
     (x :: xs).all (fun m =>
       !((x :: xs).all (fun y => decide (y ≤ m))) || decide (m = maxElement (x :: xs))) = true))
-- Pre-restricted form of the post-condition (the size-0 sample is the empty list, so
-- Plausible may report one discarded sample; the bounded tests below cover it exhaustively).
#eval Plausible.Testable.check
  (∀ l : List Int, l ≠ [] →
    (maxElement l ∈ l ∧ l.all (fun y => decide (y ≤ maxElement l)) = true ∧
     l.max? = some (maxElement l)))

/-- Bounded, exhaustive-style test data: 40 deterministic pseudo-random non-empty lists. -/
def testLists : List (List Int) :=
  (List.range 40).map fun n =>
    (List.range (n + 1)).map fun i => (((i : Int) * 37 + (n : Int) * 11) % 23) - 11

example : testLists.all (fun l => decide (maxElement l ∈ l)) = true := by native_decide
example : testLists.all (fun l => l.all (fun x => decide (x ≤ maxElement l))) = true := by
  native_decide
example : testLists.all (fun l => decide (l.max? = some (maxElement l))) = true := by
  native_decide
example : testLists.all (fun l =>
    l.all (fun m => !(l.all (fun x => decide (x ≤ m))) || decide (m = maxElement l))) = true := by
  native_decide

/-! ### Correctness -/

theorem correctness_thm (l : List Int) (h : Pre l) : Post_prop l :=
  ⟨mem_thm l h, upper_bound_thm l h, max?_thm l h, unique_thm l h, maximum_thm l h⟩

/-! ### Imperative implementation -/

/-- Imperative implementation mirroring the Python code with a mutable variable `m`. -/
def maxElementImp (l : List Int) : Int := Id.run do
  let mut m : Int := l.headD 0
  for e in l do
    if e > m then
      m := e
  return m

-- Imperative tests
example : maxElementImp [1, 2, 3] = 3 := by native_decide
example : maxElementImp [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide
example : maxElementImp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : maxElementImp [-7] = -7 := by native_decide
#eval maxElementImp [1, 2, 3]
#eval maxElementImp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]
#eval Plausible.Testable.check (∀ l : List Int, maxElement l = maxElementImp l)
example : testLists.all (fun l => decide (maxElement l = maxElementImp l)) = true := by
  native_decide

/-! ### Equivalence -/

/-- The `for` loop of the imperative version (in `Id`) is the fold of `step`. -/
theorem forIn_step_eq_foldl (xs : List Int) (m : Int) :
    (forIn (m := Id) xs m fun e r =>
        if e > r then pure (ForInStep.yield e) else pure (ForInStep.yield r)) =
      xs.foldl step m := by
  induction xs generalizing m with
  | nil => rfl
  | cons y ys ih =>
    rw [List.forIn_cons, List.foldl_cons]
    by_cases h : y > m
    · rw [if_pos h, show step m y = y from if_pos h]
      exact ih y
    · rw [if_neg h, show step m y = m from if_neg h]
      exact ih m

theorem equiv_thm (l : List Int) : maxElement l = maxElementImp l := by
  unfold maxElement maxElementImp
  exact (forIn_step_eq_foldl l (l.headD 0)).symm

end humaneval_35_max_element
