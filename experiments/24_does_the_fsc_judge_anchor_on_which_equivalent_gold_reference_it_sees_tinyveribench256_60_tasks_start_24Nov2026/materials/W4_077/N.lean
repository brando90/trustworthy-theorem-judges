import Mathlib
namespace Agent

/-!
# Safe interval constraint solving

Translation of the safe constraint solver from MIT 6.858 Lecture 11's
symbolic-execution example. A path constrained to the integer interval
`[lower, upper)` is feasible exactly when `lower < upper`. Both bounds are
checked, so reversed and equal bounds are rejected rather than explored.

`Int` models Python's arbitrary-precision signed integers without overflow.
The mathematical specification also characterizes feasibility by an actual
integer witness. There are no restrictions on the input bounds. Bounded
property-based tests supplement, but do not replace, the universal proofs.
-/

namespace «91_unsafeConstraintSolve_safe»

/-! ## Functional implementation and the Python test driver -/

/-- Decide whether the half-open interval is nonempty. -/
def safe_constraint_solve (lower upper : Int) : Bool :=
  decide (lower < upper)

/-- Boolean translation of all assertions in the Python `check` function. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 0 10 &&
  candidate 3 7 &&
  !(candidate 10 3) &&
  !(candidate 5 5) &&
  !(candidate 0 0) &&
  !(candidate 100 0) &&
  (candidate 0 5 != candidate 6 5)

/-! ## Fixed unit tests -/

example : safe_constraint_solve 0 10 = true := by native_decide
example : safe_constraint_solve 3 7 = true := by native_decide
example : safe_constraint_solve 10 3 = false := by native_decide
example : safe_constraint_solve 5 5 = false := by native_decide
example : safe_constraint_solve 0 0 = false := by native_decide
example : safe_constraint_solve 100 0 = false := by native_decide
example : safe_constraint_solve 0 5 ≠ safe_constraint_solve 6 5 := by native_decide
example : check safe_constraint_solve = true := by native_decide

-- Signed and large integer cases, beyond the original Python tests.
example : safe_constraint_solve (-10) (-3) = true := by native_decide
example : safe_constraint_solve (-3) (-10) = false := by native_decide
example : safe_constraint_solve (-5) (-5) = false := by native_decide
example : safe_constraint_solve (-1000000000000000000000000000000)
    1000000000000000000000000000000 = true := by native_decide

#eval safe_constraint_solve 0 10
#eval safe_constraint_solve 10 3
#eval check safe_constraint_solve
#eval if check safe_constraint_solve then "All tests passed." else "Candidate failed tests"

/-! ## Preconditions and proved properties -/

/-- Every pair of Python integers is admissible. -/
def Pre (_lower _upper : Int) : Prop := True

/-- The solver returns true exactly for strictly increasing bounds. -/
def feasible_prop (lower upper : Int) : Prop :=
  safe_constraint_solve lower upper = true ↔ lower < upper

theorem feasible_thm (lower upper : Int) : feasible_prop lower upper := by sorry

/-- Infeasible paths are rejected, including equal bounds. -/
def infeasible_prop (lower upper : Int) : Prop :=
  safe_constraint_solve lower upper = false ↔ upper ≤ lower

theorem infeasible_thm (lower upper : Int) : infeasible_prop lower upper := by sorry

/-- Exact satisfiability of the conjunction defining the whole interval. -/
def nonempty_prop (lower upper : Int) : Prop :=
  safe_constraint_solve lower upper = true ↔
    ∃ x : Int, lower ≤ x ∧ x < upper

theorem nonempty_thm (lower upper : Int) : nonempty_prop lower upper := by sorry

/-- The half-open interval contains nothing when its endpoints coincide. -/
def equal_bounds_prop (bound : Int) : Prop :=
  safe_constraint_solve bound bound = false

theorem equal_bounds_thm (bound : Int) : equal_bounds_prop bound := by sorry

/-- Changing only the lower bound across the upper bound changes feasibility. -/
def lower_bound_sensitivity_prop (lower other upper : Int) : Prop :=
  lower < upper → upper ≤ other →
    safe_constraint_solve lower upper ≠ safe_constraint_solve other upper

theorem lower_bound_sensitivity_thm (lower other upper : Int) :
    lower_bound_sensitivity_prop lower other upper := by sorry

/-! ## Combined postcondition -/

/-- All guarantees, including sensitivity to any alternative lower bound. -/
def Post_prop (lower upper : Int) : Prop :=
  feasible_prop lower upper ∧
  infeasible_prop lower upper ∧
  nonempty_prop lower upper ∧
  equal_bounds_prop upper ∧
  ∀ other : Int, lower_bound_sensitivity_prop lower other upper

/-! ## Bounded, exhaustive property-based tests

Each named property and the postcondition has its own executable test below.
We enumerate all bounds from -20 through 20 (including negative, zero,
equal, increasing, and decreasing cases). Sensitivity checks all triples.
For `nonempty_prop`, witness search uses the same finite set: because every
sampled lower endpoint belongs to it, a nonempty sampled interval always has
its lower endpoint as a witness. Thus this search tests actual satisfiability,
not merely a few arbitrarily selected interior points.

The postcondition's universal alternative bound is sampled over the entire
same set. These finite tests are evidence only; all theorem domains remain Int.
-/

namespace BoundedTests

def values : List Int := (List.range 41).map (fun n => (n : Int) - 20)

/-- Executable iff for `feasible_prop`. -/
def feasible (lower upper : Int) : Bool :=
  (safe_constraint_solve lower upper == true) == decide (lower < upper)

/-- Executable iff for `infeasible_prop`. -/
def infeasible (lower upper : Int) : Bool :=
  (safe_constraint_solve lower upper == false) == decide (upper ≤ lower)

/-- Bounded witness search for `nonempty_prop` on sampled endpoints. -/
def nonempty (lower upper : Int) : Bool :=
  (safe_constraint_solve lower upper == true) ==
    values.any (fun x => decide (lower ≤ x ∧ x < upper))

/-- Executable form of `equal_bounds_prop`. -/
def equalBounds (bound : Int) : Bool :=
  safe_constraint_solve bound bound == false

/-- Decidable implication for `lower_bound_sensitivity_prop`. -/
def sensitivity (lower other upper : Int) : Bool :=
  !(decide (lower < upper ∧ upper ≤ other)) ||
    (safe_constraint_solve lower upper != safe_constraint_solve other upper)

/-- Executable conjunction for `Post_prop`, sampling all alternative bounds. -/
def post (lower upper : Int) : Bool :=
  feasible lower upper &&
  infeasible lower upper &&
  nonempty lower upper &&
  equalBounds upper &&
  values.all (fun other => sensitivity lower other upper)

-- PBT for feasible_prop: 41² pairs.
example : values.all (fun lower => values.all (fun upper =>
    feasible lower upper)) = true := by native_decide

-- PBT for infeasible_prop: 41² pairs.
example : values.all (fun lower => values.all (fun upper =>
    infeasible lower upper)) = true := by native_decide

-- PBT for nonempty_prop: 41² pairs with a finite interval-witness search.
example : values.all (fun lower => values.all (fun upper =>
    nonempty lower upper)) = true := by native_decide

-- PBT for equal_bounds_prop: every sampled bound.
example : values.all equalBounds = true := by native_decide

-- PBT for lower_bound_sensitivity_prop: 41³ triples.
example : values.all (fun lower => values.all (fun other =>
    values.all (fun upper => sensitivity lower other upper))) = true := by native_decide

-- PBT for Post_prop: all properties jointly, on all sampled inputs.
example : values.all (fun lower => values.all (fun upper =>
    post lower upper)) = true := by native_decide

#eval values.all (fun lower => values.all (fun upper => post lower upper))

end BoundedTests

/-! ## Correctness for all admissible inputs -/

theorem correctness_thm (lower upper : Int) : Pre lower upper → Post_prop lower upper := by sorry

/-! ## Imperative implementation with local mutable state -/

def safe_constraint_solve_imperative (lower upper : Int) : Bool := Id.run do
  let mut feasible := false
  if lower < upper then
    feasible := true
  return feasible

/-! ## Imperative tests -/

example : safe_constraint_solve_imperative 0 10 = true := by native_decide
example : safe_constraint_solve_imperative 3 7 = true := by native_decide
example : safe_constraint_solve_imperative 10 3 = false := by native_decide
example : safe_constraint_solve_imperative 5 5 = false := by native_decide
example : safe_constraint_solve_imperative 0 0 = false := by native_decide
example : safe_constraint_solve_imperative 100 0 = false := by native_decide
example : safe_constraint_solve_imperative 0 5 ≠
    safe_constraint_solve_imperative 6 5 := by native_decide
example : check safe_constraint_solve_imperative = true := by native_decide
example : safe_constraint_solve_imperative (-10) (-3) = true := by native_decide
example : safe_constraint_solve_imperative (-3) (-10) = false := by native_decide

#eval check safe_constraint_solve_imperative
#eval if check safe_constraint_solve_imperative then "All tests passed." else "Candidate failed tests"

-- Additional bounded equivalence test, independent of the proof below.
example : BoundedTests.values.all (fun lower => BoundedTests.values.all (fun upper =>
    safe_constraint_solve lower upper == safe_constraint_solve_imperative lower upper)) =
    true := by native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equiv (lower upper : Int) :
    safe_constraint_solve lower upper = safe_constraint_solve_imperative lower upper := by sorry

end «91_unsafeConstraintSolve_safe»
end Agent
