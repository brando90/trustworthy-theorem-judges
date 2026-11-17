import Mathlib

/-!
# HumanEval/35 — `max_element`

Python source (`humaneval_35_max_element.py`):

```python
def max_element(l: list):
    m = l[0]
    for e in l:
        if e > m:
            m = e
    return m
```

The function returns the largest value in a non-empty list of integers.
The scan starts at `l[0]` and replaces the accumulator only when a strictly
greater element is seen, so equal maxima keep the earlier value. On `Int`
that value is the mathematical maximum.

An empty list makes Python raise `IndexError`. `Pre` is exactly that
non-empty domain. The Lean functions are total so they can be evaluated:
outside `Pre` both return `0`, and no correctness claim is made there.
-/

namespace humaneval_35_max_element

/-! ## Implementation -/

/-- One step of the Python update `if e > m: m = e`. -/
def updateMax (m e : Int) : Int :=
  if e > m then e else m

/-- Maximum element of `l`, written as the Python left fold.

`l.headD 0` is `l[0]` when `l` is non-empty. The fold walks every element,
including the head, matching `for e in l`. -/
def maxElement (l : List Int) : Int :=
  l.foldl updateMax (l.headD 0)

/-! ## Unit tests -/

/-- The Python `check` harness. The second literal is `124`, as in `check`. -/
def check (candidate : List Int → Int) : Bool :=
  candidate [1, 2, 3] == 3 &&
    candidate [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] == 124

example : maxElement [1, 2, 3] = 3 := by native_decide

example : maxElement [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide

example : maxElement [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide

example : maxElement [7] = 7 := by native_decide

example : maxElement [-5, -1, -10] = -1 := by native_decide

example : maxElement [9, 1, 2] = 9 := by native_decide

example : maxElement [2, 2, 2] = 2 := by native_decide

example : check maxElement = true := by native_decide

#eval maxElement [1, 2, 3]

#eval maxElement [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]

#eval maxElement [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

#eval check maxElement

/-! ## Pre-condition -/

/-- The list is non-empty, so `l[0]` is defined in Python. -/
def Pre (l : List Int) : Prop :=
  l ≠ []

/-! ## Properties -/

/-- Comparing a value with itself leaves it unchanged (`e > m` is false). -/
@[simp] theorem updateMax_self (m : Int) : updateMax m m = m := by
  simp only [updateMax]
  exact if_neg (lt_irrefl m)

/-- The strict update returns the same integer as `max`. -/
theorem updateMax_eq_max (m e : Int) : updateMax m e = max m e := by
  simp only [updateMax, Int.max_def]
  by_cases hgt : e > m
  · have hle : m ≤ e := le_of_lt hgt
    simp [hgt, hle]
  · have hle : e ≤ m := Int.le_of_not_gt hgt
    by_cases hle' : m ≤ e
    · have heq : m = e := le_antisymm hle' hle
      simp [heq]
    · simp [hgt, hle']

theorem updateMax_ge_left (m e : Int) : m ≤ updateMax m e := by
  simp only [updateMax]
  split
  · next h => exact le_of_lt h
  · exact le_refl m

theorem updateMax_ge_right (m e : Int) : e ≤ updateMax m e := by
  simp only [updateMax]
  split
  · exact le_refl e
  · next h => exact Int.le_of_not_gt h

theorem foldl_updateMax_acc_le (m : Int) (l : List Int) : m ≤ l.foldl updateMax m := by
  induction l generalizing m with
  | nil => exact le_refl m
  | cons e es ih =>
    simp only [List.foldl_cons]
    exact le_trans (updateMax_ge_left m e) (ih (updateMax m e))

theorem foldl_updateMax_of_mem (m : Int) (l : List Int) :
    ∀ x ∈ l, x ≤ l.foldl updateMax m := by
  induction l generalizing m with
  | nil =>
    intro x hx
    cases hx
  | cons e es ih =>
    intro x hx
    simp only [List.foldl_cons]
    cases hx with
    | head =>
      exact le_trans (updateMax_ge_right m e) (foldl_updateMax_acc_le (updateMax m e) es)
    | tail _ hx =>
      exact ih (updateMax m e) x hx

theorem foldl_updateMax_eq_or_mem (m : Int) (l : List Int) :
    l.foldl updateMax m = m ∨ l.foldl updateMax m ∈ l := by
  induction l generalizing m with
  | nil =>
    left
    rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    rcases ih (updateMax m e) with hEq | hmem
    · rw [hEq]
      by_cases h : e > m
      · right
        have he : updateMax m e = e := by simp only [updateMax, if_pos h]
        rw [he]
        exact List.mem_cons_self
      · left
        simp only [updateMax, if_neg h]
    · right
      exact List.mem_cons_of_mem e hmem

/-- Folding `max` is associative through `updateMax`. -/
theorem foldl_updateMax_assoc (m a : Int) (l : List Int) :
    l.foldl updateMax (updateMax m a) = updateMax m (l.foldl updateMax a) := by
  induction l generalizing m a with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    have hstep : updateMax (updateMax m a) e = updateMax m (updateMax a e) := by
      simp only [updateMax_eq_max, Int.max_assoc]
    rw [hstep]
    exact ih m (updateMax a e)

/-- The full-list fold agrees with a fold of the tail that starts at the head. -/
theorem maxElement_cons (x : Int) (xs : List Int) :
    maxElement (x :: xs) = xs.foldl updateMax x := by
  simp only [maxElement, List.headD, List.foldl_cons, updateMax_self]

theorem foldl_updateMax_eq_max_maxElement (m : Int) (l : List Int) (hl : l ≠ []) :
    l.foldl updateMax m = max m (maxElement l) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons y ys =>
    rw [List.foldl_cons, foldl_updateMax_assoc, updateMax_eq_max, maxElement_cons]

/-- The returned value occurs in the list. -/
def mem_prop (l : List Int) (result : Int) : Prop :=
  result ∈ l

/-- Every element of the list is less than or equal to the result. -/
def upper_bound_prop (l : List Int) (result : Int) : Prop :=
  ∀ x ∈ l, x ≤ result

/-- A one-element list returns that element. -/
def singleton_prop (a : Int) : Prop :=
  maxElement [a] = a

/-- Pushing a new head takes `max` with the maximum of the tail. -/
def cons_max_prop (a : Int) (l : List Int) : Prop :=
  l ≠ [] → maxElement (a :: l) = max a (maxElement l)

/-- The maximum of a concatenation is the max of the maxima. -/
def append_prop (l₁ l₂ : List Int) : Prop :=
  l₁ ≠ [] → l₂ ≠ [] → maxElement (l₁ ++ l₂) = max (maxElement l₁) (maxElement l₂)

/-- The maximum depends only on the multiset of values. -/
def perm_prop (l₁ l₂ : List Int) : Prop :=
  l₁ ≠ [] → List.Perm l₁ l₂ → maxElement l₁ = maxElement l₂

/-- The maximum of a non-empty subset is at most the maximum of the whole list. -/
def mono_prop (l₁ l₂ : List Int) : Prop :=
  l₁ ≠ [] → l₁ ⊆ l₂ → maxElement l₁ ≤ maxElement l₂

/-- The result is Mathlib's list maximum (`⊥` on the empty list). -/
def eq_maximum_prop (l : List Int) : Prop :=
  Pre l → l.maximum = (maxElement l : WithBot Int)

theorem mem_thm (l : List Int) (h : Pre l) : mem_prop l (maxElement l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    rw [maxElement_cons]
    rcases foldl_updateMax_eq_or_mem x xs with hEq | hmem
    · rw [hEq]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem x hmem

theorem upper_bound_thm (l : List Int) (h : Pre l) : upper_bound_prop l (maxElement l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    rw [maxElement_cons]
    intro y hy
    cases hy with
    | head =>
      exact foldl_updateMax_acc_le x xs
    | tail _ hy =>
      exact foldl_updateMax_of_mem x xs y hy

theorem singleton_thm (a : Int) : singleton_prop a := by
  simp [singleton_prop, maxElement_cons]

theorem cons_max_thm (a : Int) (l : List Int) : cons_max_prop a l := by
  intro hl
  rw [maxElement_cons, foldl_updateMax_eq_max_maxElement a l hl]

theorem append_thm (l₁ l₂ : List Int) : append_prop l₁ l₂ := by
  intro h₁ h₂
  cases l₁ with
  | nil => exact absurd rfl h₁
  | cons x xs =>
    have happ : (x :: xs) ++ l₂ = x :: (xs ++ l₂) := rfl
    rw [happ, maxElement_cons x (xs ++ l₂), List.foldl_append]
    rw [← maxElement_cons x xs]
    exact foldl_updateMax_eq_max_maxElement (maxElement (x :: xs)) l₂ h₂

theorem perm_thm (l₁ l₂ : List Int) : perm_prop l₁ l₂ := by
  intro h₁ hp
  have h₂ : l₂ ≠ [] := by
    intro hnil
    subst hnil
    exact h₁ hp.eq_nil
  apply le_antisymm
  · exact upper_bound_thm l₂ h₂ (maxElement l₁) ((hp.mem_iff).mp (mem_thm l₁ h₁))
  · exact upper_bound_thm l₁ h₁ (maxElement l₂) ((hp.mem_iff).mpr (mem_thm l₂ h₂))

theorem mono_thm (l₁ l₂ : List Int) : mono_prop l₁ l₂ := by
  intro h₁ hsub
  have hmem : maxElement l₁ ∈ l₂ := hsub (mem_thm l₁ h₁)
  have h₂ : l₂ ≠ [] := List.ne_nil_of_mem hmem
  exact upper_bound_thm l₂ h₂ (maxElement l₁) hmem

theorem eq_maximum_thm (l : List Int) : eq_maximum_prop l := by
  intro h
  exact (List.maximum_eq_coe_iff).mpr ⟨mem_thm l h, upper_bound_thm l h⟩

/-! ## Post-condition -/

/-- `result` is a greatest element of `l`: it occurs in `l` and bounds every entry. -/
def Post_prop (l : List Int) (result : Int) : Prop :=
  mem_prop l result ∧ upper_bound_prop l result

/-! ## Property-based tests -/

/-- Finite non-empty samples: lengths `1..5`, entries shifted through `-3..3`. -/
def boundedSamples : List (List Int) :=
  (List.range 5).flatMap fun n =>
    let len := n + 1
    (List.range 7).map fun k =>
      (List.range len).map fun i => (Int.ofNat (i + k)) - 3

-- PBT for `mem_prop`
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int), decide (maxElement (x :: xs) ∈ x :: xs) = true)

example : boundedSamples.all (fun l => decide (maxElement l ∈ l)) = true := by
  native_decide

-- PBT for `upper_bound_prop`
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    (x :: xs).all (fun y => decide (y ≤ maxElement (x :: xs))) = true)

example : boundedSamples.all
    (fun l => l.all (fun y => decide (y ≤ maxElement l))) = true := by
  native_decide

-- PBT for `singleton_prop`
#eval Plausible.Testable.check (∀ a : Int, maxElement [a] = a)

example : ((List.range 21).all fun k =>
    maxElement [(Int.ofNat k) - 10] == (Int.ofNat k) - 10) = true := by
  native_decide

-- PBT for `cons_max_prop`
#eval Plausible.Testable.check
  (∀ (a x : Int) (xs : List Int),
    maxElement (a :: x :: xs) = max a (maxElement (x :: xs)))

example : boundedSamples.all (fun l =>
    (List.range 7).all fun k =>
      let a : Int := (Int.ofNat k) - 3
      maxElement (a :: l) == max a (maxElement l)) = true := by
  native_decide

-- PBT for `append_prop`
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int) (y : Int) (ys : List Int),
    maxElement ((x :: xs) ++ (y :: ys)) = max (maxElement (x :: xs)) (maxElement (y :: ys)))

example : boundedSamples.all (fun l₁ =>
    boundedSamples.all fun l₂ =>
      maxElement (l₁ ++ l₂) == max (maxElement l₁) (maxElement l₂)) = true := by
  native_decide

-- PBT for `perm_prop`
#eval Plausible.Testable.check
  (∀ a b c : Int,
    ([a, b, c].permutations.all fun p => maxElement p == maxElement [a, b, c]) = true)

example : boundedSamples.all (fun l =>
    l.permutations.all fun p => maxElement p == maxElement l) = true := by
  native_decide

-- PBT for `mono_prop`
#eval Plausible.Testable.check
  (∀ (x : Int) (xs zs : List Int),
    maxElement (x :: xs) ≤ maxElement (zs ++ (x :: xs)))

example : boundedSamples.all (fun l₁ =>
    boundedSamples.all fun l₂ =>
      ((!decide (l₁ ⊆ l₂)) || decide (maxElement l₁ ≤ maxElement l₂))) = true := by
  native_decide

-- PBT for `eq_maximum_prop`
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    decide ((x :: xs).maximum = (maxElement (x :: xs) : WithBot Int)) = true)

example : boundedSamples.all (fun l =>
    decide (l.maximum = (maxElement l : WithBot Int))) = true := by
  native_decide

-- PBT for `Post_prop`
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    decide (maxElement (x :: xs) ∈ x :: xs) = true ∧
      (x :: xs).all (fun y => decide (y ≤ maxElement (x :: xs))) = true)

example : boundedSamples.all (fun l =>
    (decide (maxElement l ∈ l) &&
      l.all (fun y => decide (y ≤ maxElement l)))) = true := by
  native_decide

/-! ## Correctness -/

/-- Any value satisfying `Post_prop` is the value `maxElement` returns. -/
theorem spec_unique_thm (l : List Int) (a : Int) (h : Post_prop l a) :
    a = maxElement l := by
  have hne : Pre l := List.ne_nil_of_mem h.1
  exact le_antisymm (upper_bound_thm l hne a h.1) (h.2 (maxElement l) (mem_thm l hne))

/-- On the Python domain, `maxElement` returns a greatest element of the list. -/
theorem maxElement_correct_thm (l : List Int) (h : Pre l) : Post_prop l (maxElement l) :=
  ⟨mem_thm l h, upper_bound_thm l h⟩

/-! ## Imperative implementation -/

/-- Direct translation of the Python loop, using mutable state in `Id`.

```python
m = l[0]
for e in l:
    if e > m:
        m = e
return m
```

`l.headD 0` stands in for `l[0]` so the loop is total. Under `Pre` it is `l[0]`. -/
def maxElementImp (l : List Int) : Int :=
  Id.run do
    let mut m := l.headD 0
    for e in l do
      if e > m then
        m := e
    return m

/-! ## Imperative tests -/

example : maxElementImp [1, 2, 3] = 3 := by native_decide

example : maxElementImp [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide

example : maxElementImp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide

example : maxElementImp [-5, -1, -10] = -1 := by native_decide

example : maxElementImp [2, 2, 1] = 2 := by native_decide

example : check maxElementImp = true := by native_decide

example : boundedSamples.all (fun l => maxElement l == maxElementImp l) = true := by
  native_decide

#eval maxElementImp [1, 2, 3]

#eval maxElementImp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

#eval check maxElementImp

/-! ## Equivalence -/

/-- The functional fold and the imperative loop return the same integer on every list. -/
theorem maxElement_equiv_thm (l : List Int) : maxElement l = maxElementImp l := by
  unfold maxElementImp maxElement
  simp only [Id.run_bind, Id.run_pure]
  have hbody : ∀ e r,
      (if e > r then do
          pure PUnit.unit
          pure (ForInStep.yield e)
        else do
          pure PUnit.unit
          pure (ForInStep.yield r) : Id (ForInStep Int)) =
        pure (ForInStep.yield (if e > r then e else r)) := by
    intro e r
    by_cases h : e > r
    · simp [h]
    · simp [h]
  simp only [hbody, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  unfold updateMax
  rfl

/-- On the Python domain the imperative loop meets `Post_prop`. -/
theorem maxElementImp_correct_thm (l : List Int) (h : Pre l) :
    Post_prop l (maxElementImp l) := by
  simpa [maxElement_equiv_thm l] using maxElement_correct_thm l h

end humaneval_35_max_element
