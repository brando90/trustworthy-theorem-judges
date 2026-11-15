import Mathlib

/-!
# HumanEval/35 — `max_element`

Translation of the Python function `max_element`, which returns the maximum
element of a non-empty list.

```python
def max_element(l: list):
    m = l[0]
    for e in l:
        if e > m:
            m = e
    return m
```

Python raises `IndexError` on the empty list because it reads `l[0]`.
The Lean model is total: both implementations return the dummy value `0` on
`[]`, and `Pre` excludes that case. The examples use integers (including
negatives), so the numeric model is `Int`. The update `if e > m: m = e`
keeps the earlier value on ties; the returned *value* is still the unique
mathematical maximum.
-/

namespace humaneval_35_max_element

/-- Python's accumulator update: replace `m` only when `e` is strictly greater. -/
def step (m e : Int) : Int :=
  if e > m then e else m

/-- Functional implementation.

Mirrors the Python scan: start from the head (or `0` if the list is empty)
and fold `step` across every element, including the head. On a non-empty list
this is exactly `m = l[0]; for e in l: if e > m: m = e`. -/
def max_element (l : List Int) : Int :=
  l.foldl step (l.headD 0)

/-! ## Unit tests -/

example : max_element [1, 2, 3] = 3 := by native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : max_element [42] = 42 := by native_decide
example : max_element [-10] = -10 := by native_decide
example : max_element [-5, -1, -3] = -1 := by native_decide
example : max_element [0, 0, 0] = 0 := by native_decide
example : max_element [7, 1, 7] = 7 := by native_decide
example : max_element [3, 2, 1] = 3 := by native_decide
example : max_element [1, 1, 2, 2] = 2 := by native_decide

#eval max_element [1, 2, 3]
#eval max_element [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
#eval max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]
#eval max_element [-5, -1, -3]

/-! ## Pre-condition -/

/-- The list must be non-empty: Python indexes `l[0]`. -/
def Pre (l : List Int) : Prop :=
  l ≠ []

/-! ## Helper lemmas about `step` -/

lemma step_self (m : Int) : step m m = m := by
  simp [step]

lemma step_eq_max (m e : Int) : step m e = max m e := by
  unfold step
  rw [max_def]
  by_cases h : e > m
  · have hle : m ≤ e := le_of_lt h
    simp [h, hle, gt_iff_lt]
  · have hle : e ≤ m := le_of_not_gt h
    simp [h, gt_iff_lt]
    intro h2
    exact le_antisymm h2 hle

lemma foldl_step_eq_foldl_max (init : Int) (l : List Int) :
    l.foldl step init = l.foldl max init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, step_eq_max]
    exact ih (max init x)

lemma foldl_step_eq_or_mem (init : Int) (l : List Int) :
    l.foldl step init = init ∨ l.foldl step init ∈ l := by
  induction l generalizing init with
  | nil =>
    simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases ih (step init y) with h | h
    · rw [h]
      by_cases hgt : y > init
      · right
        unfold step
        simp [hgt]
      · left
        unfold step
        simp [hgt]
    · right
      exact List.mem_cons_of_mem y h

lemma le_step_left (m e : Int) : m ≤ step m e := by
  unfold step
  split_ifs with h
  · exact le_of_lt h
  · exact le_refl m

lemma le_step_right (m e : Int) : e ≤ step m e := by
  unfold step
  split_ifs with h
  · exact le_refl e
  · exact le_of_not_gt h

lemma foldl_step_ge_init (init : Int) (l : List Int) : init ≤ l.foldl step init := by
  induction l generalizing init with
  | nil => exact le_refl init
  | cons y ys ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_step_left init y) (ih (step init y))

lemma foldl_step_ge_mem (init : Int) (l : List Int) {x : Int} (hx : x ∈ l) :
    x ≤ l.foldl step init := by
  induction l generalizing init with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [List.foldl_cons]
    rcases hx with rfl | hx
    · exact le_trans (le_step_right init x) (foldl_step_ge_init (step init x) ys)
    · exact ih (step init y) hx

lemma max_element_cons_fold (x : Int) (xs : List Int) :
    max_element (x :: xs) = xs.foldl max x := by
  unfold max_element
  simp only [List.headD_cons, List.foldl_cons, step_eq_max, max_self]
  exact foldl_step_eq_foldl_max x xs

/-! ## Properties -/

/-- The result is a member of the input list. -/
def mem_prop (l : List Int) : Prop :=
  max_element l ∈ l

theorem mem_thm (l : List Int) (h : Pre l) : mem_prop l := by
  unfold mem_prop max_element Pre at *
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    simp only [List.headD_cons]
    rcases foldl_step_eq_or_mem x (x :: xs) with hEq | hMem
    · rw [hEq]
      exact List.mem_cons_self
    · exact hMem

/-- Every element of the list is `≤` the result.
This holds for the empty list vacuously as well. -/
def upper_bound_prop (l : List Int) : Prop :=
  ∀ x ∈ l, x ≤ max_element l

theorem upper_bound_thm (l : List Int) : upper_bound_prop l := by
  intro x hx
  simpa [upper_bound_prop, max_element] using foldl_step_ge_mem (l.headD 0) l hx

/-- A singleton list returns its only element. -/
def singleton_prop (x : Int) : Prop :=
  max_element [x] = x

theorem singleton_thm (x : Int) : singleton_prop x := by
  simp [singleton_prop, max_element, step]

private lemma eq_maximum_aux (l : List Int) (h : Pre l) :
    (max_element l : WithBot Int) = l.maximum := by
  symm
  rw [List.maximum_eq_coe_iff]
  exact ⟨mem_thm l h, upper_bound_thm l⟩

/-- Recursive characterization: `max_element (x :: xs) = max x (max_element xs)`
when `xs` is non-empty, and `x` when `xs` is empty. -/
def cons_prop (x : Int) (xs : List Int) : Prop :=
  max_element (x :: xs) =
    match xs with
    | [] => x
    | _ => max x (max_element xs)

theorem cons_thm (x : Int) (xs : List Int) : cons_prop x xs := by
  unfold cons_prop
  cases xs with
  | nil =>
    simp [max_element, step]
  | cons y ys =>
    have hy : Pre (y :: ys) := List.cons_ne_nil y ys
    have hx : Pre (x :: y :: ys) := List.cons_ne_nil x (y :: ys)
    rw [← WithBot.coe_inj]
    calc
      (max_element (x :: y :: ys) : WithBot Int)
          = (x :: y :: ys).maximum := eq_maximum_aux (x :: y :: ys) hx
      _ = max (x : WithBot Int) (y :: ys).maximum := List.maximum_cons x (y :: ys)
      _ = max (x : WithBot Int) (max_element (y :: ys) : WithBot Int) := by
            rw [eq_maximum_aux (y :: ys) hy]
      _ = (max x (max_element (y :: ys)) : WithBot Int) := by
            rw [← WithBot.coe_max]

/-- The result agrees with Mathlib's `List.maximum` on non-empty lists. -/
def eq_maximum_prop (l : List Int) : Prop :=
  Pre l → (max_element l : WithBot Int) = l.maximum

theorem eq_maximum_thm (l : List Int) : eq_maximum_prop l :=
  eq_maximum_aux l

/-- The result agrees with the standard-library `List.max?`. -/
def eq_max?_prop (l : List Int) : Prop :=
  Pre l → l.max? = some (max_element l)

theorem eq_max?_thm (l : List Int) : eq_max?_prop l := by
  intro h
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    rw [List.max?_cons']
    congr 1
    symm
    exact max_element_cons_fold x xs

/-- Appending two non-empty lists: the max is the max of the maxes. -/
def append_prop (l₁ l₂ : List Int) : Prop :=
  Pre l₁ → Pre l₂ → max_element (l₁ ++ l₂) = max (max_element l₁) (max_element l₂)

theorem append_thm (l₁ l₂ : List Int) : append_prop l₁ l₂ := by
  intro h1 h2
  have h12 : Pre (l₁ ++ l₂) := by
    intro h
    exact h1 (List.append_eq_nil_iff.mp h).1
  rw [← WithBot.coe_inj]
  calc
    (max_element (l₁ ++ l₂) : WithBot Int)
        = (l₁ ++ l₂).maximum := eq_maximum_thm (l₁ ++ l₂) h12
    _ = max l₁.maximum l₂.maximum := List.maximum_append l₁ l₂
    _ = max (max_element l₁ : WithBot Int) (max_element l₂ : WithBot Int) := by
          rw [eq_maximum_thm l₁ h1, eq_maximum_thm l₂ h2]
    _ = (max (max_element l₁) (max_element l₂) : WithBot Int) := by
          rw [← WithBot.coe_max]

/-- The returned value is invariant under permutation. -/
def perm_prop (l₁ l₂ : List Int) : Prop :=
  l₁.Perm l₂ → Pre l₁ → max_element l₁ = max_element l₂

theorem perm_thm (l₁ l₂ : List Int) : perm_prop l₁ l₂ := by
  intro hperm h1
  have h2 : Pre l₂ := by
    intro hnil
    have : l₁.Perm [] := by simpa [hnil] using hperm
    exact h1 this.eq_nil
  rw [← WithBot.coe_inj]
  rw [eq_maximum_thm l₁ h1, eq_maximum_thm l₂ h2]
  exact le_antisymm (List.maximum_mono hperm.subset) (List.maximum_mono hperm.symm.subset)

/-- Extending the list cannot decrease the maximum. -/
def subset_mono_prop (l₁ l₂ : List Int) : Prop :=
  l₁ ⊆ l₂ → Pre l₁ → Pre l₂ → max_element l₁ ≤ max_element l₂

theorem subset_mono_thm (l₁ l₂ : List Int) : subset_mono_prop l₁ l₂ := by
  intro hsub h1 h2
  have hle : (max_element l₁ : WithBot Int) ≤ max_element l₂ := by
    rw [eq_maximum_thm l₁ h1, eq_maximum_thm l₂ h2]
    exact List.maximum_mono hsub
  exact WithBot.coe_le_coe.mp hle

/-- The maximum value is unique: any member that dominates the list equals the result. -/
def unique_max_prop (l : List Int) (z : Int) : Prop :=
  Pre l → z ∈ l → (∀ x ∈ l, x ≤ z) → z = max_element l

theorem unique_max_thm (l : List Int) (z : Int) : unique_max_prop l z := by
  intro hpre hz hub
  apply le_antisymm
  · exact upper_bound_thm l z hz
  · exact hub (max_element l) (mem_thm l hpre)

/-! ## Post-condition -/

/-- Post-condition: the result is a member of the list and an upper bound. -/
def Post_prop (l : List Int) : Prop :=
  mem_prop l ∧ upper_bound_prop l

/-! ## Property-based tests -/

/-- Non-empty inputs used by exhaustive small-case checks. -/
def boundedInputs : List (List Int) :=
  [[1], [-1], [0], [1, 2, 3], [3, 2, 1],
   [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10],
   [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10],
   [-5, -1, -3], [0, 0, 0], [7, 7, 1], [2, 1], [-10, -10],
   [100, -100, 50], [-8, 4, 4, -3]]
  ++ (List.range 12).map fun n =>
    (List.range (n + 1)).map fun i => (i : Int) - 6

-- mem_prop
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    (x :: xs).elem (max_element (x :: xs)) = true)

example : boundedInputs.all (fun l => decide (max_element l ∈ l)) = true := by
  native_decide

-- upper_bound_prop
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    (x :: xs).all (fun y => y ≤ max_element (x :: xs)) = true)

example : boundedInputs.all (fun l => l.all (fun x => x ≤ max_element l)) = true := by
  native_decide

-- singleton_prop
#eval Plausible.Testable.check (∀ x : Int, max_element [x] = x)

example : (List.range 30).all (fun n =>
    max_element [(n : Int) - 15] == (n : Int) - 15) = true := by
  native_decide

-- cons_prop
#eval Plausible.Testable.check
  (∀ (x y : Int) (ys : List Int),
    max_element (x :: y :: ys) = max x (max_element (y :: ys)))

example : boundedInputs.all (fun l =>
    match l with
    | [] => true
    | x :: xs =>
      max_element (x :: xs) ==
        match xs with
        | [] => x
        | _ => max x (max_element xs)) = true := by
  native_decide

-- append_prop
#eval Plausible.Testable.check
  (∀ (a : Int) (as : List Int) (b : Int) (bs : List Int),
    max_element ((a :: as) ++ (b :: bs)) =
      max (max_element (a :: as)) (max_element (b :: bs)))

example : boundedInputs.all (fun l₁ =>
    boundedInputs.all (fun l₂ =>
      max_element (l₁ ++ l₂) == max (max_element l₁) (max_element l₂))) = true := by
  native_decide

-- perm_prop (reverse and rotation are permutations; full relation is proved)
example : boundedInputs.all (fun l =>
    max_element l == max_element l.reverse &&
    max_element l == max_element (l.drop 1 ++ l.take 1)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (x y : Int) (xs : List Int),
    max_element (x :: y :: xs) = max_element (y :: x :: xs))

-- subset_mono_prop
example : (List.range 8).all (fun n =>
    (List.range 8).all (fun m =>
      let l₂ := (List.range (n + m + 1)).map (fun i => (i : Int) - 3)
      let l₁ := l₂.take (n + 1)
      decide (max_element l₁ ≤ max_element l₂))) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (x : Int) (xs ys : List Int),
    max_element (x :: xs) ≤ max_element (x :: xs ++ ys))

-- unique_max_prop: any list element that dominates the list equals the result.
-- Checking every element of each sample list covers every `z` that can satisfy `z ∈ l`.
example : boundedInputs.all (fun l =>
    l.all (fun z =>
      !(l.elem z && l.all (fun y => y ≤ z)) || z == max_element l)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    let l := x :: xs
    let z := max_element l
    (l.elem z && l.all (fun y => y ≤ z)) = true)

-- eq_maximum_prop
example : boundedInputs.all (fun l =>
    decide ((max_element l : WithBot Int) = l.maximum)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    max_element (x :: xs) =
      (x :: xs).maximum_of_length_pos (Nat.succ_pos xs.length))

-- eq_max?_prop
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int), (x :: xs).max? = some (max_element (x :: xs)))

example : boundedInputs.all (fun l =>
    decide (l.max? = some (max_element l))) = true := by
  native_decide

-- Post_prop
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    ((x :: xs).elem (max_element (x :: xs)) &&
      (x :: xs).all (fun y => y ≤ max_element (x :: xs))) = true)

example : boundedInputs.all (fun l =>
    (l.elem (max_element l) && l.all (fun x => x ≤ max_element l))) = true := by
  native_decide

/-! ## Correctness -/

/-- If the input is non-empty, the result satisfies the post-condition. -/
theorem correctness_thm (l : List Int) (h : Pre l) : Post_prop l := by
  exact ⟨mem_thm l h, upper_bound_thm l⟩

/-! ## Imperative implementation -/

/-- Imperative implementation using mutable state, matching the Python loop.

```python
m = l[0]
for e in l:
    if e > m:
        m = e
return m
```
-/
def max_element_imp (l : List Int) : Int :=
  Id.run do
    let mut m : Int := l.headD 0
    for e in l do
      if e > m then
        m := e
    return m

/-- The `for`-loop that always yields the strict-greater update is a left fold. -/
lemma forIn_step_eq_foldl (l : List Int) (init : Int) :
    forIn (m := Id) l init (fun e r =>
      if r < e then pure (ForInStep.yield e) else pure (ForInStep.yield r))
    = l.foldl step init := by
  induction l generalizing init with
  | nil =>
    rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, List.foldl_cons]
    by_cases h : init < x
    · simp [h, step, gt_iff_lt, ih]
    · simp [h, step, gt_iff_lt, ih]

/-! ## Imperative tests -/

example : max_element_imp [1, 2, 3] = 3 := by native_decide
example : max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide
example : max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : max_element_imp [42] = 42 := by native_decide
example : max_element_imp [-5, -1, -3] = -1 := by native_decide
example : max_element_imp [0, 0, 0] = 0 := by native_decide
example : max_element_imp [7, 1, 7] = 7 := by native_decide

#eval max_element_imp [1, 2, 3]
#eval max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]
#eval max_element_imp [-5, -1, -3]

example : boundedInputs.all (fun l => max_element l == max_element_imp l) = true := by
  native_decide

/-! ## Equivalence -/

/-- The functional scan and the imperative loop return the same value on every list,
including the shared totalization of the empty list. -/
theorem equivalence_thm (l : List Int) : max_element l = max_element_imp l := by
  unfold max_element max_element_imp
  simp only [Id.run, List.headD]
  rw [← forIn_step_eq_foldl]
  rfl

-- PBT: functional = imperative on random lists, including the empty totalization.
#eval Plausible.Testable.check (∀ l : List Int, max_element l = max_element_imp l)

end humaneval_35_max_element
