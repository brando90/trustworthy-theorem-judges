import Mathlib

/-!
# HumanEval/35: `max_element`

Translation of the Python program `humaneval_35_max_element.py`:

```python
def max_element(l: list):
    m = l[0]
    for e in l:
        if e > m:
            m = e
    return m
```

The function returns the maximum element of a non-empty list of integers.
Python raises `IndexError` on the empty list; the Lean implementations return
the default value `0` in that (excluded) case, and the precondition `Pre`
requires the list to be non-empty.
-/

namespace humaneval_35_max_element

/-- Functional implementation: start from the first element and fold the
Python loop body `if e > m then m := e` over the remaining elements. -/
def max_element (l : List Int) : Int :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl (fun m e => if e > m then e else m) x

-- Unit tests (from the Python docstring and `check`)
example : max_element [1, 2, 3] = 3 := by native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : max_element [7] = 7 := by native_decide
example : max_element [-3, -1, -2] = -1 := by native_decide
example : max_element [2, 2, 1] = 2 := by native_decide
#eval max_element [1, 2, 3]
#eval max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

/-- Pre-condition: the list must be non-empty (Python's `l[0]` would raise). -/
def Pre (l : List Int) : Prop := l ≠ []

/-- The result is an element of the list. -/
def mem_prop (l : List Int) : Prop := max_element l ∈ l

/-- The result is an upper bound of every element of the list. -/
def upper_bound_prop (l : List Int) : Prop := ∀ x ∈ l, x ≤ max_element l

/-- The result agrees with the library maximum `List.max?`. -/
def max?_prop (l : List Int) : Prop := l.max? = some (max_element l)

/-- Any element that bounds the whole list is the result (uniqueness of the maximum). -/
def unique_prop (l : List Int) : Prop :=
  ∀ m ∈ l, (∀ x ∈ l, x ≤ m) → m = max_element l

/-- The result only depends on the multiset of elements (permutation invariance). -/
def perm_prop (l : List Int) : Prop :=
  ∀ l' : List Int, l.Perm l' → max_element l = max_element l'

/-- Appending a non-empty list takes the larger of the two maxima. -/
def append_prop (l : List Int) : Prop :=
  ∀ l' : List Int, l' ≠ [] → max_element (l ++ l') = max (max_element l) (max_element l')

/-- Helper facts about the fold used by `max_element`, by induction on the list:
the fold is at least the start value, bounds every element, and is either the
start value or one of the elements. -/
theorem foldl_step_spec (xs : List Int) (init : Int) :
    init ≤ xs.foldl (fun m e => if e > m then e else m) init ∧
    (∀ x ∈ xs, x ≤ xs.foldl (fun m e => if e > m then e else m) init) ∧
    (xs.foldl (fun m e => if e > m then e else m) init = init ∨
      xs.foldl (fun m e => if e > m then e else m) init ∈ xs) := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (if x > init then x else init)
    refine ⟨?_, ?_, ?_⟩
    · refine le_trans ?_ h1
      split_ifs <;> omega
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · refine le_trans ?_ h1
        split_ifs <;> omega
      · exact h2 y hy
    · rcases h3 with h3 | h3
      · rw [h3]
        split_ifs
        · right; simp
        · left; rfl
      · right; simp [h3]

theorem mem_thm (l : List Int) (h : Pre l) : mem_prop l := by
  unfold mem_prop
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    simp only [max_element]
    obtain ⟨_, _, h3⟩ := foldl_step_spec xs x
    rcases h3 with h3 | h3
    · rw [h3]; simp
    · simp [h3]

theorem upper_bound_thm (l : List Int) : upper_bound_prop l := by
  unfold upper_bound_prop
  cases l with
  | nil => simp
  | cons x xs =>
    simp only [max_element]
    obtain ⟨h1, h2, _⟩ := foldl_step_spec xs x
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact h1
    · exact h2 y hy

theorem unique_thm (l : List Int) : unique_prop l := by
  intro m hm hbound
  apply le_antisymm
  · exact upper_bound_thm l m hm
  · have hne : Pre l := by
      intro hnil; subst hnil; simp at hm
    exact hbound _ (mem_thm l hne)

theorem perm_thm (l : List Int) : perm_prop l := by
  intro l' hp
  cases l with
  | nil =>
    have := hp.nil_eq
    subst this
    rfl
  | cons x xs =>
    have hne' : l' ≠ [] := by
      intro hnil; subst hnil
      exact absurd hp.eq_nil (List.cons_ne_nil x xs)
    apply le_antisymm
    · exact upper_bound_thm l' _ (hp.mem_iff.mp (mem_thm (x :: xs) (List.cons_ne_nil x xs)))
    · exact upper_bound_thm (x :: xs) _ (hp.mem_iff.mpr (mem_thm l' hne'))

/-- The Python loop body `if e > m then e else m` is the binary `max`. -/
theorem step_eq_max : (fun m e : Int => if e > m then e else m) = fun m e => max m e := by
  funext m e
  rcases lt_trichotomy e m with hlt | heq | hgt
  · simp [not_lt.mpr hlt.le, max_eq_left hlt.le]
  · subst heq; simp
  · simp [hgt, max_eq_right hgt.le]

theorem max?_thm (l : List Int) (h : Pre l) : max?_prop l := by
  unfold max?_prop
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    simp only [max_element, List.max?_cons']
    rw [step_eq_max]

theorem append_thm (l : List Int) (h : Pre l) : append_prop l := by
  intro l' hl'
  symm
  apply unique_thm (l ++ l')
  · rcases le_total (max_element l) (max_element l') with hle | hle
    · rw [max_eq_right hle]
      exact List.mem_append_right _ (mem_thm l' hl')
    · rw [max_eq_left hle]
      exact List.mem_append_left _ (mem_thm l h)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact le_trans (upper_bound_thm l x hx) (le_max_left _ _)
    · exact le_trans (upper_bound_thm l' x hx) (le_max_right _ _)

/-- Post-condition: conjunction of all stated properties. -/
def Post_prop (l : List Int) : Prop :=
  mem_prop l ∧ upper_bound_prop l ∧ max?_prop l ∧ unique_prop l ∧ perm_prop l ∧ append_prop l

-- Property-based tests (randomized, via Plausible). Non-empty lists are
-- generated structurally as `x :: xs` so that every sample is admissible.
-- mem_prop
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int), max_element (x :: xs) ∈ x :: xs)
-- upper_bound_prop
#eval Plausible.Testable.check
  (∀ l : List Int, l.all (fun y => decide (y ≤ max_element l)) = true)
-- max?_prop
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int), (x :: xs).max? = some (max_element (x :: xs)))
-- unique_prop
#eval Plausible.Testable.check
  (∀ l : List Int,
    l.all (fun m => !(l.all (fun y => decide (y ≤ m))) || decide (m = max_element l)) = true)
-- perm_prop (reversal and rotation are permutations)
#eval Plausible.Testable.check (∀ l : List Int, max_element l = max_element l.reverse)
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int), max_element (x :: xs) = max_element (xs ++ [x]))
-- append_prop
#eval Plausible.Testable.check
  (∀ (x y : Int) (xs ys : List Int),
    max_element (x :: xs ++ y :: ys) = max (max_element (x :: xs)) (max_element (y :: ys)))
-- Post_prop (executable Boolean form of its decidable conjuncts)
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    max_element (x :: xs) ∈ x :: xs ∧
    (x :: xs).all (fun y => decide (y ≤ max_element (x :: xs))) = true ∧
    (x :: xs).max? = some (max_element (x :: xs)) ∧
    max_element (x :: xs) = max_element (xs ++ [x]))

/-- Small input space for exhaustive bounded property tests: all lists of
length 1..3 with entries in `[-2, 2]`. -/
def smallLists : List (List Int) :=
  let vals : List Int := [-2, -1, 0, 1, 2]
  (vals.map fun a => [a]) ++
  (vals.flatMap fun a => vals.map fun b => [a, b]) ++
  (vals.flatMap fun a => vals.flatMap fun b => vals.map fun c => [a, b, c])

-- Bounded PBTs (exhaustive on `smallLists`)
example : smallLists.all (fun l => decide (max_element l ∈ l)) = true := by native_decide
example : smallLists.all (fun l => l.all (fun y => decide (y ≤ max_element l))) = true := by
  native_decide
example : smallLists.all (fun l => decide (l.max? = some (max_element l))) = true := by
  native_decide
example : smallLists.all (fun l =>
    l.all (fun m => !(l.all (fun y => decide (y ≤ m))) || decide (m = max_element l))) = true := by
  native_decide
example : smallLists.all (fun l =>
    l.permutations.all (fun l' => decide (max_element l = max_element l'))) = true := by
  native_decide
example : smallLists.all (fun l => smallLists.all (fun l' =>
    decide (max_element (l ++ l') = max (max_element l) (max_element l')))) = true := by
  native_decide
example : smallLists.all (fun l =>
    decide (max_element l ∈ l) && l.all (fun y => decide (y ≤ max_element l)) &&
    decide (l.max? = some (max_element l)) &&
    l.permutations.all (fun l' => decide (max_element l = max_element l'))) = true := by
  native_decide

/-- Correctness: the pre-condition implies the post-condition. -/
theorem correctness (l : List Int) (h : Pre l) : Post_prop l :=
  ⟨mem_thm l h, upper_bound_thm l, max?_thm l h, unique_thm l, perm_thm l, append_thm l h⟩

/-- Imperative implementation mirroring the Python loop with mutable state. -/
def max_element_imp (l : List Int) : Int := Id.run do
  let mut m : Int := l[0]!
  for e in l do
    if e > m then
      m := e
  return m

-- Imperative tests
example : max_element_imp [1, 2, 3] = 3 := by native_decide
example : max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide
example : max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : max_element_imp [7] = 7 := by native_decide
example : max_element_imp [-3, -1, -2] = -1 := by native_decide
#eval max_element_imp [1, 2, 3]
#eval max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]
-- Functional/imperative agreement, randomized and bounded
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int), max_element (x :: xs) = max_element_imp (x :: xs))
example : smallLists.all (fun l => decide (max_element l = max_element_imp l)) = true := by
  native_decide

/-- The `for` loop of the imperative version is the fold of the functional version. -/
theorem forIn_loop_eq_foldl (xs : List Int) (init : Int) :
    (forIn (m := Id) xs init (fun e m => if e > m then pure (ForInStep.yield e)
        else pure (ForInStep.yield m))) =
      xs.foldl (fun m e => if e > m then e else m) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, List.foldl_cons]
    split_ifs with h
    · simpa using ih x
    · simpa using ih init

/-- Equivalence of the functional and the imperative implementation (for every
list; both return `0` on the empty list that Python rejects). -/
theorem max_element_eq_imp (l : List Int) : max_element l = max_element_imp l := by
  cases l with
  | nil => rfl
  | cons x xs =>
    -- The first loop iteration compares `x` with itself and changes nothing.
    simp only [max_element, max_element_imp, List.getElem!_cons_zero, List.forIn_cons,
      lt_self_iff_false, if_false, pure_bind, bind_pure]
    rw [forIn_loop_eq_foldl]
    rfl

/-- Equivalence restricted to the admissible (non-empty) inputs. -/
theorem max_element_eq_imp_of_pre (l : List Int) (_h : Pre l) :
    max_element l = max_element_imp l :=
  max_element_eq_imp l

end humaneval_35_max_element
