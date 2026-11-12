import Mathlib

/-!
# HumanEval/35 -- `max_element`

Translation of the Python program

```python
def max_element(l: list):
    m = l[0]
    for e in l:
        if e > m:
            m = e
    return m
```

which returns the maximum element of a (non-empty) list of integers.

The file contains a functional implementation (`maxElement`), unit tests, the
pre-condition (`Pre`: the list is non-empty), the specification properties
(the result is a member of the list, it is an upper bound of the list, and it is
the unique such element -- i.e. it is `List.maximum`), the correctness theorem
`Pre → Post`, an imperative implementation using `Id.run do` with a mutable
accumulator, and the equivalence theorem between the two implementations.
-/

namespace humaneval_35_max_element

/-! ## Implementation -/

/-- One step of the Python loop body: `if e > m then m := e`. -/
def step (m e : Int) : Int := if e > m then e else m

/-- Functional implementation: fold the loop body over the whole list, starting
from the first element (`l[0]` in Python, `0` on the -- excluded -- empty list). -/
def maxElement (l : List Int) : Int :=
  l.foldl step (l.headD 0)

/-! ## Unit tests -/

example : maxElement [1, 2, 3] = 3 := by native_decide

example : maxElement [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide

example : maxElement [-7] = -7 := by native_decide

#eval maxElement [1, 2, 3]
#eval maxElement [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

/-! ## Pre-condition -/

/-- Python evaluates `l[0]`, so the list must be non-empty. -/
def Pre (l : List Int) : Prop := l ≠ []

/-! ## Auxiliary lemmas about the fold -/

theorem le_step (m e : Int) : m ≤ step m e := by
  unfold step; split <;> omega

theorem right_le_step (m e : Int) : e ≤ step m e := by
  unfold step; split <;> omega

/-- The accumulator only ever grows. -/
theorem le_foldl_step (l : List Int) (a : Int) : a ≤ l.foldl step a := by
  induction l generalizing a with
  | nil => simp
  | cons b t ih =>
    rw [List.foldl_cons]
    exact le_trans (le_step a b) (ih (step a b))

/-- Every element of the list is below the result of the fold. -/
theorem mem_le_foldl_step (l : List Int) (a : Int) :
    ∀ e ∈ l, e ≤ l.foldl step a := by
  induction l generalizing a with
  | nil => intro e he; cases he
  | cons b t ih =>
    intro e he
    rw [List.foldl_cons]
    rcases List.mem_cons.mp he with h | h
    · rw [h]
      exact le_trans (right_le_step a b) (le_foldl_step t (step a b))
    · exact ih (step a b) e h

/-- The fold returns either its initial value or one of the list elements. -/
theorem foldl_step_eq_or_mem (l : List Int) (a : Int) :
    l.foldl step a = a ∨ l.foldl step a ∈ l := by
  induction l generalizing a with
  | nil => left; rfl
  | cons b t ih =>
    rw [List.foldl_cons]
    rcases ih (step a b) with h | h
    · rw [h]
      simp only [step]
      by_cases hb : b > a
      · simp [hb]
      · simp [hb]
    · right
      exact List.mem_cons_of_mem b h

/-! ## Properties -/

/-- The returned value is one of the elements of the list. -/
def mem_prop (l : List Int) : Prop := maxElement l ∈ l

/-- The returned value is an upper bound of the list. -/
def ub_prop (l : List Int) : Prop := ∀ e ∈ l, e ≤ maxElement l

/-- The returned value is *the* maximum: any element of the list that is an
upper bound of the list equals the result. -/
def greatest_prop (l : List Int) : Prop :=
  ∀ m ∈ l, (∀ e ∈ l, e ≤ m) → m = maxElement l

/-- The result agrees with `List.maximum`. -/
def maximum_prop (l : List Int) : Prop := l.maximum = (maxElement l : WithBot Int)

/-- On a singleton the result is that element (the `l[0]` initialisation). -/
def singleton_prop (x : Int) : Prop := maxElement [x] = x

theorem mem_thm (l : List Int) (hl : Pre l) : mem_prop l := by
  unfold mem_prop maxElement
  match l, hl with
  | x :: xs, _ =>
    rcases foldl_step_eq_or_mem (x :: xs) ((x :: xs).headD 0) with h | h
    · rw [h]; simp
    · exact h

theorem ub_thm (l : List Int) : ub_prop l := by
  intro e he
  exact mem_le_foldl_step l (l.headD 0) e he

theorem greatest_thm (l : List Int) : greatest_prop l := by
  intro m hm hub
  have h1 : m ≤ maxElement l := ub_thm l m hm
  have h2 : maxElement l ≤ m := by
    have hl : Pre l := by
      intro h; rw [h] at hm; cases hm
    exact hub _ (mem_thm l hl)
  omega

theorem maximum_thm (l : List Int) (hl : Pre l) : maximum_prop l :=
  List.maximum_eq_coe_iff.mpr ⟨mem_thm l hl, fun a ha => ub_thm l a ha⟩

theorem singleton_thm (x : Int) : singleton_prop x := by
  unfold singleton_prop maxElement step
  simp

/-! ## Post-condition and correctness -/

def Post_prop (l : List Int) : Prop :=
  mem_prop l ∧ ub_prop l ∧ greatest_prop l ∧ maximum_prop l

/-- Correctness: on a non-empty list the result is the maximum of the list. -/
theorem correctness (l : List Int) (h : Pre l) : Post_prop l :=
  ⟨mem_thm l h, ub_thm l, greatest_thm l, maximum_thm l h⟩

/-! ## Imperative implementation -/

/-- Literal transcription of the Python loop with a mutable accumulator. -/
def maxElementImp (l : List Int) : Int := Id.run do
  let mut m := l.headD 0
  for e in l do
    if e > m then
      m := e
  return m

/-! ## Imperative unit tests -/

example : maxElementImp [1, 2, 3] = 3 := by native_decide

example : maxElementImp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide

#eval maxElementImp [1, 2, 3]
#eval maxElementImp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

/-! ## Equivalence of the two implementations -/

/-- The `for` loop of the imperative version is exactly the fold of `step`. -/
theorem forIn_step_eq_foldl (l : List Int) (a : Int) :
    (forIn (m := Id) l a fun e r =>
        if r < e then pure (ForInStep.yield e) else pure (ForInStep.yield r))
      = List.foldl step a l := by
  induction l generalizing a with
  | nil => rfl
  | cons b t ih =>
    simp only [List.forIn_cons, List.foldl_cons, step]
    by_cases h : a < b <;> simp [h, ih]

theorem maxElementImp_eq_maxElement (l : List Int) : maxElementImp l = maxElement l := by
  unfold maxElementImp maxElement
  simp only [Id.run, List.headD_eq_head?_getD]
  exact forIn_step_eq_foldl l _

end humaneval_35_max_element
