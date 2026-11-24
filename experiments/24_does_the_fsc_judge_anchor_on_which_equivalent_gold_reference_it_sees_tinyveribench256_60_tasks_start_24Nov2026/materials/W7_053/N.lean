import Mathlib
namespace Agent

/-!
# Unsafe constraint solving

Translation of the Python `unsafe_constraint_solve` example from MIT 6.858,
Lecture 11 (symbolic execution with EXE/KLEE).

Python's unbounded signed integers are represented by `Int`. The implementation
intentionally preserves the vulnerability: it tests only `upper > 0`, ignoring
`lower`. Actual feasibility of the integer interval `[lower, upper)` is
`lower < upper`. In particular, positive empty intervals are accepted. Over the
full signed input domain, feasible intervals with nonpositive upper bounds are
also rejected; zero is not the only upper bound producing `false`.

The Boolean `check` function records successful completion of all assertions in
the Python test harness. Bounded property-based tests are executable evidence;
the named theorems are proved separately using kernel-checked proofs.
-/

namespace UnsafeConstraintSolve

/-! ## Functional implementation -/

/-- Preserve the unsafe Python implementation, including ignoring `lower`. -/
def unsafe_constraint_solve (_lower upper : Int) : Bool :=
  decide (upper > 0)

/-- The conjunction of the Python harness's assertions. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 0 10 &&
  candidate 3 7 &&
  candidate 10 3 &&
  candidate 5 5 &&
  !(candidate 0 0) &&
  !(candidate 100 0) &&
  (candidate 0 5 == candidate 1000 5)

/-! ## Unit tests -/

example : unsafe_constraint_solve 0 10 = true := by native_decide
example : unsafe_constraint_solve 3 7 = true := by native_decide
-- Empty and boundary intervals are nevertheless accepted.
example : unsafe_constraint_solve 10 3 = true := by native_decide
example : unsafe_constraint_solve 5 5 = true := by native_decide
example : unsafe_constraint_solve 0 0 = false := by native_decide
example : unsafe_constraint_solve 100 0 = false := by native_decide
example : unsafe_constraint_solve 0 5 = unsafe_constraint_solve 1000 5 := by
  native_decide
example : check unsafe_constraint_solve = true := by native_decide

-- Signed-input regression tests, beyond the original harness.
example : unsafe_constraint_solve (-5) (-1) = false := by native_decide
example : unsafe_constraint_solve (-1) 0 = false := by native_decide
example : unsafe_constraint_solve (-10) 3 = true := by native_decide
-- The unsatisfiable path constraint mentioned in the source's module comment.
example : unsafe_constraint_solve 6 4 = true := by native_decide

#eval unsafe_constraint_solve 10 3
#eval unsafe_constraint_solve 100 0
#eval check unsafe_constraint_solve
#eval if check unsafe_constraint_solve then
  IO.println "All tests passed."
else
  IO.println "Candidate failed tests"

/-! ## Precondition and semantic properties -/

/-- Every pair of Python integers is admissible, even if its interval is empty. -/
def Pre (_lower _upper : Int) : Prop := True

/-- Acceptance is equivalent to a strictly positive upper bound. -/
def accepts_iff_prop (lower upper : Int) : Prop :=
  unsafe_constraint_solve lower upper = true ↔ 0 < upper

theorem accepts_iff_thm (lower upper : Int) : accepts_iff_prop lower upper := by sorry

/-- Rejection occurs exactly for nonpositive upper bounds, not just zero. -/
def rejects_iff_prop (lower upper : Int) : Prop :=
  unsafe_constraint_solve lower upper = false ↔ upper ≤ 0

theorem rejects_iff_thm (lower upper : Int) : rejects_iff_prop lower upper := by sorry

/-- The lower bound is irrelevant for every upper bound, including negative ones. -/
def lower_irrelevance_prop (lower otherLower upper : Int) : Prop :=
  unsafe_constraint_solve lower upper = unsafe_constraint_solve otherLower upper

theorem lower_irrelevance_thm (lower otherLower upper : Int) :
    lower_irrelevance_prop lower otherLower upper := by sorry

/-- Exact characterization of infeasible paths incorrectly accepted by the solver.
This includes both reversed intervals and the `lower = upper` boundary. -/
def false_positive_prop (lower upper : Int) : Prop :=
  (unsafe_constraint_solve lower upper = true ∧ ¬ (lower < upper)) ↔
    (0 < upper ∧ upper ≤ lower)

theorem false_positive_thm (lower upper : Int) : false_positive_prop lower upper := by sorry

/-- Exact characterization of feasible paths incorrectly rejected by the solver. -/
def false_negative_prop (lower upper : Int) : Prop :=
  (unsafe_constraint_solve lower upper = false ∧ lower < upper) ↔
    (upper ≤ 0 ∧ lower < upper)

theorem false_negative_thm (lower upper : Int) : false_negative_prop lower upper := by sorry

/-! ## Postcondition -/

/-- This specifies the unsafe behavior, not the desired safe feasibility check. -/
def Post_prop (lower upper : Int) : Prop :=
  accepts_iff_prop lower upper ∧
  rejects_iff_prop lower upper ∧
  (∀ otherLower : Int, lower_irrelevance_prop lower otherLower upper) ∧
  false_positive_prop lower upper ∧
  false_negative_prop lower upper

/-! ## Bounded property-based tests

Each test checks an executable form of its named property, exhaustively over
signed integers from -12 through 12. No precondition filtering is needed.
The postcondition test also checks every alternative lower bound in that range;
the correctness theorem below establishes the unbounded universal statement.
-/

private def pbtInts : List Int :=
  (List.range 25).map (fun n => (n : Int) - 12)

-- PBT for accepts_iff_prop: 625 signed input pairs.
example : pbtInts.all (fun lower => pbtInts.all (fun upper =>
    decide (unsafe_constraint_solve lower upper = true ↔ 0 < upper))) = true := by
  native_decide

-- PBT for rejects_iff_prop: includes zero and strictly negative upper bounds.
example : pbtInts.all (fun lower => pbtInts.all (fun upper =>
    decide (unsafe_constraint_solve lower upper = false ↔ upper ≤ 0))) = true := by
  native_decide

-- PBT for lower_irrelevance_prop: 15,625 triples, without a positivity restriction.
example : pbtInts.all (fun lower => pbtInts.all (fun otherLower =>
    pbtInts.all (fun upper =>
      unsafe_constraint_solve lower upper ==
        unsafe_constraint_solve otherLower upper))) = true := by
  native_decide

-- PBT for false_positive_prop: includes both empty boundaries and reversed bounds.
example : pbtInts.all (fun lower => pbtInts.all (fun upper =>
    decide ((unsafe_constraint_solve lower upper = true ∧ ¬ (lower < upper)) ↔
      (0 < upper ∧ upper ≤ lower)))) = true := by
  native_decide

-- PBT for false_negative_prop: tests feasible negative and zero-ending intervals.
example : pbtInts.all (fun lower => pbtInts.all (fun upper =>
    decide ((unsafe_constraint_solve lower upper = false ∧ lower < upper) ↔
      (upper ≤ 0 ∧ lower < upper)))) = true := by
  native_decide

-- PBT for Post_prop: executable conjunction, with bounded universal lower bounds.
example : pbtInts.all (fun lower => pbtInts.all (fun upper =>
    decide (unsafe_constraint_solve lower upper = true ↔ 0 < upper) &&
    decide (unsafe_constraint_solve lower upper = false ↔ upper ≤ 0) &&
    pbtInts.all (fun otherLower =>
      unsafe_constraint_solve lower upper == unsafe_constraint_solve otherLower upper) &&
    decide ((unsafe_constraint_solve lower upper = true ∧ ¬ (lower < upper)) ↔
      (0 < upper ∧ upper ≤ lower)) &&
    decide ((unsafe_constraint_solve lower upper = false ∧ lower < upper) ↔
      (upper ≤ 0 ∧ lower < upper)))) = true := by
  native_decide

/-! ## Correctness relative to the unsafe specification -/

theorem correctness_thm (lower upper : Int) :
    Pre lower upper → Post_prop lower upper := by sorry

/-! ## Imperative implementation -/

/-- Mutable-state implementation of the same unsafe upper-bound-only test. -/
def unsafe_constraint_solve_imp (_lower upper : Int) : Bool := Id.run do
  let mut result := false
  if upper > 0 then
    result := true
  return result

/-! ## Imperative tests -/

example : unsafe_constraint_solve_imp 0 10 = true := by native_decide
example : unsafe_constraint_solve_imp 3 7 = true := by native_decide
example : unsafe_constraint_solve_imp 10 3 = true := by native_decide
example : unsafe_constraint_solve_imp 5 5 = true := by native_decide
example : unsafe_constraint_solve_imp 0 0 = false := by native_decide
example : unsafe_constraint_solve_imp 100 0 = false := by native_decide
example : unsafe_constraint_solve_imp 0 5 = unsafe_constraint_solve_imp 1000 5 := by
  native_decide
example : unsafe_constraint_solve_imp (-5) (-1) = false := by native_decide
example : check unsafe_constraint_solve_imp = true := by native_decide

#eval unsafe_constraint_solve_imp 10 3
#eval check unsafe_constraint_solve_imp

/-! ## Functional / imperative equivalence -/

theorem functional_imperative_equivalence_thm (lower upper : Int) :
    unsafe_constraint_solve lower upper = unsafe_constraint_solve_imp lower upper := by sorry

end UnsafeConstraintSolve
end Agent
