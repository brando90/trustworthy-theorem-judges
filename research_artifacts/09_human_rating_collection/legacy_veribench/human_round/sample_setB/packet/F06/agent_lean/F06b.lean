import Mathlib

/-!
# HumanEval/35 - `max_element`

Formal translation of the Python program

```python
def max_element(l: list):
    """Return maximum element in the list."""
    m = l[0]
    for e in l:
        if e > m:
            m = e
    return m
```

which returns the maximum element of a non-empty list of integers.

Contents of this file:

* `maxGo` / `max_element`: the functional implementation. `maxGo acc xs` is the
  running-maximum scan performed by the Python `for` loop (`acc` plays the role
  of the mutable variable `m`); `max_element l` initialises the accumulator with
  `l[0]`.
* `Pre`: the precondition `l != []` imposed by the Python read of `l[0]`
  (on the empty list Python raises `IndexError`).
* `mem_prop`, `le_prop`: the two halves of the specification
  "return maximum element in the list": the returned value occurs in the list
  and dominates every element of the list.
* `Post_prop`: conjunction of the two properties above.
* `correctness_thm`: `Pre l -> Post_prop l (max_element l)`.
* `max_element_imp`: imperative implementation with mutable state
  (`Id.run do` + `let mut` + `for` loop), a literal transcription of the Python.
* `equivalence_thm`: the functional and the imperative implementation agree.

Every theorem below is discharged by kernel-checked tactics: no proof is left
unfinished, no new axiom is declared, and `native_decide` is used only inside
`example` unit tests (never inside a theorem proof), as the task policy allows.
-/

namespace humaneval_35_max_element

/-! ## Functional implementation -/

/-- `maxGo acc xs` scans `xs`, keeping the running maximum in the accumulator
`acc`. This is the body of the Python `for` loop: `acc` is the variable `m` and
`max acc x` is `if x > m then x else m`. -/
def maxGo : Int -> List Int -> Int
  | acc, [] => acc
  | acc, x :: xs => maxGo (max acc x) xs

/-- `max_element l` returns the maximum element of the non-empty list `l`.
It mirrors the Python program: the accumulator is initialised with `l[0]` and
the list is scanned from left to right. For `l = []` (where Python raises
`IndexError`) an arbitrary value `0` is returned; `Pre` excludes that case. -/
def max_element (l : List Int) : Int :=
  match l with
  | [] => 0
  | x :: xs => maxGo x xs

/-! ## Unit tests (fixed examples from the Python docstring and `check`) -/

example : max_element [1, 2, 3] = 3 := by native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : max_element [7] = 7 := by native_decide
example : max_element [-1, -2, -3] = -1 := by native_decide
example : max_element [] = 0 := by native_decide

#eval max_element [1, 2, 3]
#eval max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

/-- The docstring example `max_element([1, 2, 3]) == 3`. -/
theorem docstring_example_1 : max_element [1, 2, 3] = 3 := by rfl

/-- The docstring example
`max_element([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]) == 123`. -/
theorem docstring_example_2 :
    max_element [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by rfl

/-- The `check` assertion
`candidate([5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]) == 124`. -/
theorem check_example_2 :
    max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by rfl

/-- On a singleton list the maximum is the only element (`m = l[0]`). -/
theorem max_element_singleton (a : Int) : max_element [a] = a := by rfl

/-- On a two element list the maximum is `max a b`. -/
theorem max_element_pair (a b : Int) : max_element [a, b] = max a b := by rfl

/-! ## Precondition -/

/-- The Python program reads `l[0]`, hence it is only defined on non-empty lists
(it raises `IndexError` otherwise). -/
def Pre (l : List Int) : Prop := l ≠ []

/-- Any cons list satisfies the precondition. -/
theorem Pre_cons (x : Int) (xs : List Int) : Pre (x :: xs) :=
  fun h => List.noConfusion h

/-- The empty list violates the precondition. -/
theorem Pre_nil : ¬ Pre [] := fun h => h rfl

/-! ## Properties of the functional implementation -/

/-- The returned value is an element of the input list. -/
def mem_prop (l : List Int) (m : Int) : Prop := m ∈ l

/-- The returned value is an upper bound of every element of the input list. -/
def le_prop (l : List Int) (m : Int) : Prop := ∀ x ∈ l, x ≤ m

/-- Two candidates satisfying `mem_prop` and `le_prop` for the same list coincide:
the maximum of a list is unique. -/
theorem max_unique {l : List Int} {a b : Int}
    (ha : a ∈ l) (ha' : ∀ z ∈ l, z ≤ a) (hb : b ∈ l) (hb' : ∀ z ∈ l, z ≤ b) : a = b :=
  le_antisymm (hb' a ha) (ha' b hb)

/-- The accumulator scan returns an element of `acc :: xs`. -/
theorem maxGo_mem (xs : List Int) : ∀ acc : Int, maxGo acc xs ∈ acc :: xs := by
  induction xs with
  | nil => intro acc; simp [maxGo]
  | cons x xs ih =>
      intro acc
      have h := List.mem_cons.mp (ih (max acc x))
      simp only [maxGo, List.mem_cons]
      rcases h with h | h
      · rw [h]
        by_cases hle : acc ≤ x
        · right; left; exact max_eq_right hle
        · left; exact max_eq_left (le_of_not_ge hle)
      · right; right; exact h

/-- The accumulator scan returns an upper bound of `acc :: xs`. -/
theorem maxGo_le (xs : List Int) :
    ∀ (acc y : Int), y ∈ acc :: xs -> y ≤ maxGo acc xs := by
  induction xs with
  | nil =>
      intro acc y hy
      rcases List.mem_cons.mp hy with h | hy
      · rw [h]; exact le_rfl
      · cases hy
  | cons x xs ih =>
      intro acc y hy
      rcases List.mem_cons.mp hy with h | hy
      · rw [h]
        refine le_trans (le_max_left acc x) (ih (max acc x) (max acc x) ?_)
        exact List.mem_cons.mpr (Or.inl rfl)
      · rcases List.mem_cons.mp hy with h | hy
        · rw [h]
          refine le_trans (le_max_right acc x) (ih (max acc x) (max acc x) ?_)
          exact List.mem_cons.mpr (Or.inl rfl)
        · exact ih (max acc x) y (List.mem_cons.mpr (Or.inr hy))

/-- The result of `max_element` occurs in the input list. -/
theorem mem_thm (l : List Int) (h : Pre l) : mem_prop l (max_element l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => exact maxGo_mem xs x

/-- The result of `max_element` is greater than or equal to every element of the
input list. -/
theorem le_thm (l : List Int) (h : Pre l) : le_prop l (max_element l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => exact maxGo_le xs x

/-- Any value satisfying the specification equals `max_element l`. -/
theorem max_element_unique (l : List Int) (h : Pre l) (m : Int)
    (hm : m ∈ l) (hle : ∀ x ∈ l, x ≤ m) : m = max_element l :=
  max_unique hm hle (mem_thm l h) (le_thm l h)

/-- `max` can be pulled out of the accumulator scan. -/
theorem maxGo_max (x : Int) :
    ∀ (ys : List Int) (y : Int), maxGo (max x y) ys = max x (maxGo y ys) := by
  intro ys
  induction ys with
  | nil => intro y; rfl
  | cons z zs ih =>
      intro y
      show maxGo (max (max x y) z) zs = max x (maxGo (max y z) zs)
      rw [max_assoc, ih (max y z)]

/-- One step of the Python loop: prepending an element takes the `max`. -/
theorem max_element_cons (x : Int) (l : List Int) (h : Pre l) :
    max_element (x :: l) = max x (max_element l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons y ys => exact maxGo_max x ys y

/-- The maximum of a concatenation is the maximum of the two maxima. -/
theorem max_element_append (l1 l2 : List Int) (h1 : Pre l1) (h2 : Pre l2) :
    max_element (l1 ++ l2) = max (max_element l1) (max_element l2) := by
  cases l1 with
  | nil => exact absurd rfl h1
  | cons x xs =>
    cases l2 with
    | nil => exact absurd rfl h2
    | cons y ys =>
      have key : maxGo x (xs ++ (y :: ys)) = max (maxGo x xs) (maxGo y ys) := by
        refine max_unique (maxGo_mem (xs ++ (y :: ys)) x) (maxGo_le (xs ++ (y :: ys)) x) ?_ ?_
        · rcases max_choice (maxGo x xs) (maxGo y ys) with hm | hm
          · rw [hm]
            have hmem := maxGo_mem xs x
            rcases List.mem_cons.mp hmem with hmem | hmem
            · exact List.mem_cons.mpr (Or.inl hmem)
            · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hmem)))
          · rw [hm]
            exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (maxGo_mem ys y))))
        · intro z hz
          rcases List.mem_cons.mp hz with h | hz
          · rw [h]
            refine le_trans (maxGo_le xs x x (List.mem_cons.mpr (Or.inl rfl))) (le_max_left _ _)
          · rcases List.mem_append.mp hz with hz | hz
            · exact le_trans (maxGo_le xs x z (List.mem_cons.mpr (Or.inr hz))) (le_max_left _ _)
            · exact le_trans (maxGo_le ys y z hz) (le_max_right _ _)
      exact key

/-- `max_element` agrees with Mathlib's canonical `List.maximum` of a non-empty
list. -/
theorem max_element_eq_maximum (l : List Int) (h : Pre l) :
    l.maximum = (max_element l : WithBot Int) :=
  List.maximum_eq_coe_iff.mpr ⟨mem_thm l h, le_thm l h⟩

/-! ## Postcondition -/

/-- Postcondition: the returned value is *the* maximum element of the list, i.e.
it belongs to the list and dominates all of its elements. -/
def Post_prop (l : List Int) (m : Int) : Prop := mem_prop l m ∧ le_prop l m

/-! ## Property-based tests -/

-- Randomised PBTs (Plausible). Every non-empty list has the form `x :: l`, so no
-- generated sample is discarded (no "Gave up" warning).

-- PBT for `mem_prop`: the result is a member of the input list.
#eval Plausible.Testable.check
  (∀ x : Int, ∀ l : List Int, decide (max_element (x :: l) ∈ (x :: l)) = true)

-- PBT for `le_prop`: the result dominates every element of the input list.
#eval Plausible.Testable.check
  (∀ x : Int, ∀ l : List Int,
    decide ((x :: l).all (fun y => decide (y ≤ max_element (x :: l)))) = true)

-- PBT for `Post_prop` (executable Boolean form: conjunction of the two checks).
#eval Plausible.Testable.check
  (∀ x : Int, ∀ l : List Int,
    decide (decide (max_element (x :: l) ∈ (x :: l)) &&
      (x :: l).all (fun y => decide (y ≤ max_element (x :: l)))) = true)

-- PBT for `max_element_cons` (executable Boolean form).
#eval Plausible.Testable.check
  (∀ x : Int, ∀ y : Int, ∀ l : List Int,
    decide (max_element (x :: y :: l) = max x (max_element (y :: l))) = true)

-- PBT for `max_element_append` (executable Boolean form).
#eval Plausible.Testable.check
  (∀ x : Int, ∀ y : Int, ∀ l1 l2 : List Int,
    decide (max_element ((x :: l1) ++ (y :: l2)) =
      max (max_element (x :: l1)) (max_element (y :: l2))) = true)

-- PBT for `max_element_eq_maximum` (executable Boolean form).
#eval Plausible.Testable.check
  (∀ x : Int, ∀ l : List Int,
    decide ((x :: l).maximum = (max_element (x :: l) : WithBot Int)) = true)

-- Bounded / exhaustive PBTs over concrete collections of inputs.

/-- Fixed collection of test lists (all non-empty, so `Pre` holds). -/
def sampleLists : List (List Int) :=
  [[1], [0], [-5], [1, 2], [2, 1], [1, 1], [-1, -2, -3], [3, -3], [1, 2, 3],
   [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10], [-7, -7], [10, -10, 0, 5, -5, 10]]

/-- All 125 lists of length three over `[-2, -1, 0, 1, 2]`, plus all singletons
over the same values. -/
def exhaustiveLists : List (List Int) :=
  let vals : List Int := [-2, -1, 0, 1, 2]
  (do
    let a ← vals
    let b ← vals
    let c ← vals
    pure [a, b, c]) ++ vals.map (fun a => [a])

example : sampleLists.all (fun l => decide (max_element l ∈ l)) = true := by native_decide
example : sampleLists.all (fun l => l.all (fun y => decide (y ≤ max_element l))) = true := by
  native_decide
example : exhaustiveLists.all (fun l => decide (max_element l ∈ l)) = true := by native_decide
example : exhaustiveLists.all (fun l => l.all (fun y => decide (y ≤ max_element l))) = true := by
  native_decide
example : exhaustiveLists.all
    (fun l => decide (max_element l ∈ l) && l.all (fun y => decide (y ≤ max_element l))) = true :=
  by native_decide
example : exhaustiveLists.all
    (fun l => decide (max_element (0 :: l) = max 0 (max_element l))) = true := by native_decide
example : exhaustiveLists.all
    (fun l => decide (l.maximum = (max_element l : WithBot Int))) = true := by native_decide
example : (List.range 25).all
    (fun n => decide (max_element (List.range (n + 1)) = n)) = true := by native_decide

/-! ## Correctness -/

/-- Correctness: for every admissible input the functional implementation
satisfies the postcondition. -/
theorem correctness_thm (l : List Int) (h : Pre l) : Post_prop l (max_element l) :=
  ⟨mem_thm l h, le_thm l h⟩

/-! ## Imperative implementation -/

/-- Imperative transcription of the Python program: a mutable accumulator `m`
initialised with `l[0]` and a `for` loop over the list updating `m` whenever a
larger element is found. On the empty list (Python: `IndexError`) it returns `0`,
matching `max_element`. -/
def max_element_imp (l : List Int) : Int :=
  match l with
  | [] => 0
  | x :: _ =>
    Id.run do
      let mut m := x
      for e in l do
        if e > m then
          m := e
      return m

/-! ## Imperative tests -/

example : max_element_imp [1, 2, 3] = 3 := by native_decide
example : max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : max_element_imp [] = 0 := by native_decide
example : max_element_imp [-1, -2, -3] = -1 := by native_decide

#eval max_element_imp [1, 2, 3]
#eval max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

example : sampleLists.all (fun l => decide (max_element_imp l = max_element l)) = true := by
  native_decide
example : exhaustiveLists.all (fun l => decide (max_element_imp l = max_element l)) = true := by
  native_decide

-- PBT for the functional/imperative equivalence (executable Boolean form).
#eval Plausible.Testable.check
  (∀ x : Int, ∀ l : List Int, decide (max_element_imp (x :: l) = max_element (x :: l)) = true)

-- PBT: the imperative implementation satisfies the postcondition.
#eval Plausible.Testable.check
  (∀ x : Int, ∀ l : List Int,
    decide (decide (max_element_imp (x :: l) ∈ (x :: l)) &&
      (x :: l).all (fun y => decide (y ≤ max_element_imp (x :: l)))) = true)

/-! ## Equivalence of the functional and the imperative implementation -/

/-- The imperative loop, seen as a left fold of the Python update
`m := if e > m then e else m`. Proved by induction on the list, unfolding the
`for` loop with `List.forIn_cons` and splitting on the loop condition. -/
theorem imp_loop_eq_foldl_all (l : List Int) :
    ∀ b : Int,
      (Id.run do
        let mut m := b
        for e in l do
          if e > m then
            m := e
        pure m) = l.foldl (fun s e => if e > s then e else s) b := by
  induction l with
  | nil => intro b; simp [List.forIn_nil]
  | cons a as ih =>
      intro b
      simp only [List.forIn_cons, List.foldl_cons]
      by_cases h : a > b
      · simp [h]
        exact ih a
      · simp [h]
        exact ih b

/-- Same statement with both arguments explicit. -/
theorem imp_loop_eq_foldl (l : List Int) (b : Int) :
    (Id.run do
      let mut m := b
      for e in l do
        if e > m then
          m := e
      pure m) = l.foldl (fun s e => if e > s then e else s) b :=
  imp_loop_eq_foldl_all l b

/-- The Python update `if e > m then e else m` is `max m e`. -/
theorem ite_gt_eq_max (s e : Int) : (if e > s then e else s) = max s e := by
  by_cases h : e > s
  · rw [if_pos h, max_eq_right (le_of_lt h)]
  · rw [if_neg h, max_eq_left (le_of_not_gt h)]

/-- Folding `max` is the accumulator recursion `maxGo`. -/
theorem foldl_max_eq_maxGo (xs : List Int) :
    ∀ acc : Int, xs.foldl (fun a b => max a b) acc = maxGo acc xs := by
  induction xs with
  | nil => intro acc; rfl
  | cons y ys ih =>
      intro acc
      show ys.foldl (fun a b => max a b) (max acc y) = maxGo (max acc y) ys
      exact ih (max acc y)

/-- Equivalence: the imperative implementation computes the same value as the
functional one (on every input, including the empty list). -/
theorem equivalence_thm (l : List Int) : max_element_imp l = max_element l := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [max_element_imp, max_element]
    rw [imp_loop_eq_foldl]
    simp only [List.foldl_cons, ite_gt_eq_max, max_self]
    exact foldl_max_eq_maxGo xs x

/-- The imperative implementation is correct as well. -/
theorem imp_correctness_thm (l : List Int) (h : Pre l) : Post_prop l (max_element_imp l) := by
  rw [equivalence_thm]
  exact correctness_thm l h

end humaneval_35_max_element
