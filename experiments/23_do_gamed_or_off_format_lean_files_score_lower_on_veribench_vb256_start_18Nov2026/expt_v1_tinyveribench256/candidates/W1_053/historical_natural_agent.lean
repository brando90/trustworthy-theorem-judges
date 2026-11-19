import Mathlib
namespace Agent

/-!
# Four times the absolute difference, plus three

Translation of the Python function `quadruple_abs_diff_plus_three`.
The arithmetic uses unbounded `Int`, matching Python integer arithmetic.
`Input` additionally models the runtime type check: every non-integer object is
represented by `nonInteger`, with an uninterpreted description. Its contents
are never parsed or coerced. Python booleans, which satisfy `isinstance(x, int)`,
are represented by the integers 0 and 1. Thus the type abstraction preserves
all observations made by this program, including its ValueError message.

The named theorems are kernel proofs. The `native_decide` examples are only
unit tests or bounded property-based tests, and are not used in any proof.
-/

namespace QuadrupleAbsDifferencePlusThree

/-! ## Functional implementation and runtime validation -/

inductive Input where
  | integer (value : Int)
  | nonInteger (description : String)
  deriving DecidableEq, Repr

-- Constructive equality makes success and ValueError outcomes executable in tests.
deriving instance DecidableEq for Except

def pre (a b : Input) : Bool :=
  match a, b with
  | .integer _, .integer _ => true
  | _, _ => false

def quadrupleAbsDiffPlusThree (a b : Int) : Int :=
  4 * |a - b| + 3

/-- `Except.error` represents the Python `ValueError` with its message. -/
def checked (a b : Input) : Except String Int :=
  match a, b with
  | .integer x, .integer y => .ok (quadrupleAbsDiffPlusThree x y)
  | _, _ => .error "Inputs must be integers"

/-! ## Unit tests -/

example : quadrupleAbsDiffPlusThree 7 2 = 23 := by native_decide
example : quadrupleAbsDiffPlusThree 5 5 = 3 := by native_decide
example : quadrupleAbsDiffPlusThree 0 9 = 39 := by native_decide
example : quadrupleAbsDiffPlusThree (-7) (-2) = 23 := by native_decide
example : quadrupleAbsDiffPlusThree (-3) 4 = 31 := by native_decide
example : checked (.integer 7) (.integer 2) = .ok 23 := by native_decide
example : checked (.integer 5) (.integer 5) = .ok 3 := by native_decide
example : checked (.nonInteger "1.5") (.integer 2) =
    .error "Inputs must be integers" := by native_decide
example : checked (.integer 2) (.nonInteger "None") =
    .error "Inputs must be integers" := by native_decide

#eval quadrupleAbsDiffPlusThree 7 2
#eval quadrupleAbsDiffPlusThree 5 5
#eval quadrupleAbsDiffPlusThree 0 9
#eval checked (.nonInteger "1.5") (.integer 2)

/-! ## Precondition -/

/-- Exactly the runtime integer check; no sign or size restriction is imposed. -/
def Pre (a b : Input) : Prop := pre a b = true

/-! ## Properties and kernel-checked proofs -/

def formula_prop (a b : Int) : Prop :=
  quadrupleAbsDiffPlusThree a b = 4 * |a - b| + 3

theorem formula_thm (a b : Int) : formula_prop a b := by
  rfl

def lower_bound_prop (a b : Int) : Prop :=
  3 ≤ quadrupleAbsDiffPlusThree a b

theorem lower_bound_thm (a b : Int) : lower_bound_prop a b := by
  have h : 0 ≤ |a - b| := abs_nonneg _
  dsimp [lower_bound_prop, quadrupleAbsDiffPlusThree]
  omega

def equal_iff_prop (a b : Int) : Prop :=
  quadrupleAbsDiffPlusThree a b = 3 ↔ a = b

theorem equal_iff_thm (a b : Int) : equal_iff_prop a b := by
  unfold equal_iff_prop quadrupleAbsDiffPlusThree
  constructor
  · intro h
    have habs : |a - b| = 0 := by omega
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · intro h
    subst b
    simp

def symmetry_prop (a b : Int) : Prop :=
  quadrupleAbsDiffPlusThree a b = quadrupleAbsDiffPlusThree b a

theorem symmetry_thm (a b : Int) : symmetry_prop a b := by
  unfold symmetry_prop quadrupleAbsDiffPlusThree
  rw [abs_sub_comm a b]

def mod_four_prop (a b : Int) : Prop :=
  quadrupleAbsDiffPlusThree a b % 4 = 3

theorem mod_four_thm (a b : Int) : mod_four_prop a b := by
  dsimp [mod_four_prop, quadrupleAbsDiffPlusThree]
  omega

/-- Valid arguments return precisely the specified integer, without an error. -/
def acceptance_prop (a b : Int) : Prop :=
  checked (.integer a) (.integer b) = .ok (4 * |a - b| + 3)

theorem acceptance_thm (a b : Int) : acceptance_prop a b := by
  rfl

/-- Either argument being non-integer raises the specified ValueError. -/
def rejection_prop (a b : Input) : Prop :=
  ¬ Pre a b → checked a b = .error "Inputs must be integers"

theorem rejection_thm (a b : Input) : rejection_prop a b := by
  cases a <;> cases b <;> simp [rejection_prop, Pre, pre, checked]

/-! ## Postcondition -/

/-- The complete result specification, including the exceptional outcome. -/
def Post_prop (a b : Input) : Prop :=
  rejection_prop a b ∧
    match a, b with
    | .integer x, .integer y =>
        acceptance_prop x y ∧ formula_prop x y ∧ lower_bound_prop x y ∧
        equal_iff_prop x y ∧ symmetry_prop x y ∧ mod_four_prop x y
    | _, _ => True

/-! ## Bounded property-based tests

Each test enumerates a Cartesian product, rather than a single fixed example.
The integer samples cover [-15, 15], including both signs and equal arguments.
The runtime samples also exercise rejection in either or both positions.
The tests below use the executable expansions of the named propositions.
-/

def testInts : List Int := (List.range 31).map (fun n => (n : Int) - 15)

def allIntPairs (p : Int → Int → Bool) : Bool :=
  testInts.all (fun a => testInts.all (fun b => p a b))

def testInputs : List Input :=
  testInts.map Input.integer ++
    [.nonInteger "1.5", .nonInteger "None", .nonInteger "'2'"]

def allInputPairs (p : Input → Input → Bool) : Bool :=
  testInputs.all (fun a => testInputs.all (fun b => p a b))

-- PBT for formula_prop.
example : allIntPairs (fun a b =>
    decide (quadrupleAbsDiffPlusThree a b = 4 * |a - b| + 3)) = true := by
  native_decide

-- PBT for lower_bound_prop.
example : allIntPairs (fun a b =>
    decide (3 ≤ quadrupleAbsDiffPlusThree a b)) = true := by
  native_decide

-- PBT for equal_iff_prop.
example : allIntPairs (fun a b =>
    decide (quadrupleAbsDiffPlusThree a b = 3 ↔ a = b)) = true := by
  native_decide

-- PBT for symmetry_prop.
example : allIntPairs (fun a b =>
    decide (quadrupleAbsDiffPlusThree a b = quadrupleAbsDiffPlusThree b a)) = true := by
  native_decide

-- PBT for mod_four_prop.
example : allIntPairs (fun a b =>
    decide (quadrupleAbsDiffPlusThree a b % 4 = 3)) = true := by
  native_decide

-- PBT for acceptance_prop.
example : allIntPairs (fun a b =>
    decide (checked (.integer a) (.integer b) = .ok (4 * |a - b| + 3))) = true := by
  native_decide

-- PBT for rejection_prop; Pre is expanded to its executable Boolean equality.
example : allInputPairs (fun a b =>
    decide (pre a b ≠ true → checked a b = .error "Inputs must be integers")) = true := by
  native_decide

/-- Executable expansion of every conjunct of Post_prop. -/
def postCheck (a b : Input) : Bool :=
  decide (pre a b ≠ true → checked a b = .error "Inputs must be integers") &&
    match a, b with
    | .integer x, .integer y => decide (
        checked (.integer x) (.integer y) = .ok (4 * |x - y| + 3) ∧
        quadrupleAbsDiffPlusThree x y = 4 * |x - y| + 3 ∧
        3 ≤ quadrupleAbsDiffPlusThree x y ∧
        (quadrupleAbsDiffPlusThree x y = 3 ↔ x = y) ∧
        quadrupleAbsDiffPlusThree x y = quadrupleAbsDiffPlusThree y x ∧
        quadrupleAbsDiffPlusThree x y % 4 = 3)
    | _, _ => true

/-- This establishes that the postcondition test checks exactly the stated Prop. -/
theorem postCheck_iff_thm (a b : Input) : postCheck a b = true ↔ Post_prop a b := by
  cases a <;> cases b <;>
    simp [postCheck, Post_prop, rejection_prop, Pre, pre, acceptance_prop,
      formula_prop, lower_bound_prop, equal_iff_prop, symmetry_prop, mod_four_prop]

-- PBT for Post_prop (including all valid and invalid sampled input pairs).
example : allInputPairs postCheck = true := by native_decide
#eval allInputPairs postCheck

/-! ## Correctness under the precondition -/

theorem correctness_thm (a b : Input) (h : Pre a b) : Post_prop a b := by
  cases a with
  | integer x =>
    cases b with
    | integer y =>
      exact ⟨rejection_thm (.integer x) (.integer y), acceptance_thm x y,
        formula_thm x y, lower_bound_thm x y, equal_iff_thm x y,
        symmetry_thm x y, mod_four_thm x y⟩
    | nonInteger description => simp [Pre, pre] at h
  | nonInteger description => simp [Pre, pre] at h

/-! ## Imperative implementation -/

/-- Absolute value is implemented by a conditional update of a mutable difference. -/
def quadrupleAbsDiffPlusThreeImperative (a b : Int) : Int := Id.run do
  let mut difference := a - b
  if difference < 0 then
    difference := -difference
  let mut result := 4 * difference
  result := result + 3
  return result

/-- Runtime validation precedes evaluation, as in the Python function. -/
def checkedImperative (a b : Input) : Except String Int := Id.run do
  if !pre a b then
    return .error "Inputs must be integers"
  match a, b with
  | .integer x, .integer y =>
    return .ok (quadrupleAbsDiffPlusThreeImperative x y)
  | _, _ => return .error "Inputs must be integers"

/-! ## Imperative tests -/

example : quadrupleAbsDiffPlusThreeImperative 7 2 = 23 := by native_decide
example : quadrupleAbsDiffPlusThreeImperative 5 5 = 3 := by native_decide
example : quadrupleAbsDiffPlusThreeImperative 0 9 = 39 := by native_decide
example : quadrupleAbsDiffPlusThreeImperative (-3) 4 = 31 := by native_decide
example : checkedImperative (.nonInteger "1.5") (.integer 2) =
    .error "Inputs must be integers" := by native_decide
example : checkedImperative (.integer 7) (.integer 2) = .ok 23 := by native_decide
example : allIntPairs (fun a b => decide
    (quadrupleAbsDiffPlusThree a b = quadrupleAbsDiffPlusThreeImperative a b)) = true := by
  native_decide
example : allInputPairs (fun a b => decide
    (checked a b = checkedImperative a b)) = true := by native_decide

#eval quadrupleAbsDiffPlusThreeImperative 0 9
#eval checkedImperative (.integer 5) (.integer 5)
#eval checkedImperative (.nonInteger "1.5") (.integer 2)

/-! ## Functional/imperative equivalence -/

theorem equivalence_thm (a b : Int) :
    quadrupleAbsDiffPlusThree a b = quadrupleAbsDiffPlusThreeImperative a b := by
  by_cases h : a - b < 0
  · simp [quadrupleAbsDiffPlusThree, quadrupleAbsDiffPlusThreeImperative,
      h, abs_of_neg h]
  · simp [quadrupleAbsDiffPlusThree, quadrupleAbsDiffPlusThreeImperative,
      h, abs_of_nonneg (le_of_not_gt h)]

theorem checked_equivalence_thm (a b : Input) :
    checked a b = checkedImperative a b := by
  cases a <;> cases b <;>
    simp [checked, checkedImperative, pre, equivalence_thm]

end QuadrupleAbsDifferencePlusThree
end Agent
