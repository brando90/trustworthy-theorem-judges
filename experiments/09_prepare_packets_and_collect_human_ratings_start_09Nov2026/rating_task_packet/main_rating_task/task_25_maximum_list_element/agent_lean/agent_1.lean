import Mathlib

/-!
# HumanEval 35: maximum element

This formalizes the Python program on lists of arbitrary-precision integers.
`some m` is a successful return; `none` represents the failed first-element
lookup on an empty list. The precondition is exactly nonemptiness.
The functional version folds `max`; the imperative version follows the
original initialization, full-list traversal, and strict comparison.
-/

namespace humaneval_35_max_element

/-- Return the maximum, or `none` when Python's initial lookup would fail. -/
def max_element : List Int → Option Int
  | [] => none
  | first :: rest => some (rest.foldl max first)

-- Unit tests: both Python tests, the docstring, and boundary cases.
example : max_element [1, 2, 3] = some 3 := by native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = some 124 := by
  native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = some 123 := by
  native_decide
example : max_element [] = none := by native_decide
example : max_element [-7] = some (-7) := by native_decide
example : max_element [-9, -2, -11, -2] = some (-2) := by native_decide
example : max_element [4, 4, 4] = some 4 := by native_decide

#eval max_element [1, 2, 3]
#eval max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

/-- Python's first-element lookup succeeds exactly on nonempty lists. -/
def Pre (xs : List Int) : Prop := xs ≠ []

-- The fold invariant includes the initial accumulator among the candidates.
private theorem fold_max_spec (xs : List Int) (initial : Int) :
    xs.foldl max initial ∈ initial :: xs ∧
      ∀ x ∈ initial :: xs, x ≤ xs.foldl max initial := by
  induction xs generalizing initial with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hmem, hbound⟩ := ih (max initial a)
    simp only [List.foldl_cons]
    constructor
    · rcases List.mem_cons.mp hmem with heq | hmem
      · rw [heq]
        rcases le_total initial a with h | h
        · simp [max_eq_right h]
        · simp [max_eq_left h]
      · exact List.mem_cons_of_mem initial (List.mem_cons_of_mem a hmem)
    · intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · subst x
        exact le_trans (le_max_left initial a) (hbound _ (by simp))
      · rcases List.mem_cons.mp hx with hx | hx
        · subst x
          exact le_trans (le_max_right initial a) (hbound _ (by simp))
        · exact hbound x (List.mem_cons_of_mem _ hx)

/-- A successful maximum is an element of the input; failure is not a result. -/
def membership_prop (xs : List Int) (result : Option Int) : Prop :=
  match result with
  | none => False
  | some m => m ∈ xs

theorem membership_thm (xs : List Int) (h : Pre xs) :
    membership_prop xs (max_element xs) := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons first rest => exact (fold_max_spec rest first).1

/-- Every input element is at most the returned value. -/
def upper_bound_prop (xs : List Int) (result : Option Int) : Prop :=
  match result with
  | none => False
  | some m => ∀ x ∈ xs, x ≤ m

theorem upper_bound_thm (xs : List Int) (h : Pre xs) :
    upper_bound_prop xs (max_element xs) := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons first rest => exact (fold_max_spec rest first).2

/-- The exceptional result occurs exactly for an empty input. -/
def empty_input_prop (xs : List Int) (result : Option Int) : Prop :=
  result = none ↔ xs = []

theorem empty_input_thm (xs : List Int) :
    empty_input_prop xs (max_element xs) := by
  cases xs <;> simp [empty_input_prop, max_element]

/-- Membership and the upper-bound property characterize the maximum exactly. -/
theorem maximum_characterization_thm (xs : List Int) (m : Int) :
    max_element xs = some m ↔ m ∈ xs ∧ ∀ x ∈ xs, x ≤ m := by
  cases xs with
  | nil => simp [max_element]
  | cons first rest =>
    obtain ⟨hmem, hbound⟩ := fold_max_spec rest first
    constructor
    · intro h
      have heq : rest.foldl max first = m := Option.some.inj h
      simpa [heq] using And.intro hmem hbound
    · rintro ⟨hm, hub⟩
      have heq : rest.foldl max first = m := le_antisymm (hub _ hmem) (hbound m hm)
      simp [max_element, heq]

/-- In particular, the returned maximum is the least upper bound. -/
theorem least_upper_bound_thm (xs : List Int) (m bound : Int)
    (hm : max_element xs = some m) (hb : ∀ x ∈ xs, x ≤ bound) : m ≤ bound := by
  exact hb m ((maximum_characterization_thm xs m).mp hm).1

/-- Complete successful-return specification, together with the error domain. -/
def Post_prop (xs : List Int) (result : Option Int) : Prop :=
  membership_prop xs result ∧ upper_bound_prop xs result ∧ empty_input_prop xs result

-- Executable counterparts of the properties, used for property-based tests.
def membershipCheck (xs : List Int) : Bool :=
  match max_element xs with
  | none => false
  | some m => xs.contains m

def upperBoundCheck (xs : List Int) : Bool :=
  match max_element xs with
  | none => false
  | some m => xs.all (fun x => decide (x ≤ m))

def emptyInputCheck (xs : List Int) : Bool :=
  (max_element xs).isNone == xs.isEmpty

def postCheck (xs : List Int) : Bool :=
  membershipCheck xs && upperBoundCheck xs && emptyInputCheck xs

-- PBT for membership_prop: constructing first :: rest covers admissible inputs
-- directly, including arbitrary negative entries, without discarded samples.
#eval Plausible.Testable.check
  (∀ (first : Int) (rest : List Int), membershipCheck (first :: rest) = true)

-- PBT for upper_bound_prop.
#eval Plausible.Testable.check
  (∀ (first : Int) (rest : List Int), upperBoundCheck (first :: rest) = true)

-- PBT for empty_input_prop, including empty inputs.
#eval Plausible.Testable.check (∀ xs : List Int, emptyInputCheck xs = true)

-- PBT for the full Post_prop.
#eval Plausible.Testable.check
  (∀ (first : Int) (rest : List Int), postCheck (first :: rest) = true)

-- PBTs for the exact characterization and least-upper-bound consequences.
#eval Plausible.Testable.check
  (∀ (xs : List Int) (m : Int),
    decide (max_element xs = some m) =
      (xs.contains m && xs.all (fun x => decide (x ≤ m))))

#eval Plausible.Testable.check
  (∀ (xs : List Int) (bound : Int),
    (match max_element xs with
     | none => true
     | some m => !(xs.all (fun x => decide (x ≤ bound))) || decide (m ≤ bound)) = true)

/-- All lists of a fixed length with entries in [-2, 2]. -/
private def smallLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => [-2, -1, 0, 1, 2].flatMap fun x => (smallLists n).map (x :: ·)

/-- All 3,906 lists of lengths zero through five over [-2, 2]. -/
private def boundedInputs : List (List Int) :=
  (List.range 6).flatMap smallLists

-- Exhaustive bounded PBTs for every property and the postcondition.
example : boundedInputs.all (fun xs => xs.isEmpty || membershipCheck xs) = true := by
  native_decide
example : boundedInputs.all (fun xs => xs.isEmpty || upperBoundCheck xs) = true := by
  native_decide
example : boundedInputs.all emptyInputCheck = true := by native_decide
example : boundedInputs.all (fun xs => xs.isEmpty || postCheck xs) = true := by
  native_decide

theorem correctness_thm (xs : List Int) : Pre xs → Post_prop xs (max_element xs) := by
  intro h
  exact ⟨membership_thm xs h, upper_bound_thm xs h, empty_input_thm xs⟩

/-- Literal mutable translation: initialize from the head and visit every entry. -/
def max_element_imperative (xs : List Int) : Option Int := Id.run do
  match xs with
  | [] => return none
  | first :: _ =>
    let mut m := first
    for e in xs do
      if e > m then
        m := e
    return some m

-- Imperative unit tests.
example : max_element_imperative [1, 2, 3] = some 3 := by native_decide
example : max_element_imperative [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = some 124 := by
  native_decide
example : max_element_imperative [] = none := by native_decide
example : max_element_imperative [-7] = some (-7) := by native_decide
example : max_element_imperative [-9, -2, -11, -2] = some (-2) := by native_decide

#eval max_element_imperative [1, 2, 3]
#eval max_element_imperative [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

-- Property-based equivalence also covers the exceptional empty-input case.
#eval Plausible.Testable.check
  (∀ xs : List Int, max_element xs = max_element_imperative xs)
example : boundedInputs.all
    (fun xs => decide (max_element xs = max_element_imperative xs)) = true := by
  native_decide

theorem functional_imperative_equivalence_thm (xs : List Int) :
    max_element xs = max_element_imperative xs := by
  have step (m e : Int) :
      (if m < e then pure (ForInStep.yield e) else pure (ForInStep.yield m) :
        Id (ForInStep Int)) = pure (ForInStep.yield (max m e)) := by
    by_cases h : m < e
    · simp [h, max_eq_right (le_of_lt h)]
    · simp [h, max_eq_left (le_of_not_gt h)]
  cases xs with
  | nil => rfl
  | cons first rest =>
    simp [max_element_imperative, max_element, step]

end humaneval_35_max_element
