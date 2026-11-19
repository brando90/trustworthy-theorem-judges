import Mathlib
namespace Agent

/-!
# Safe dual-variable bounds check

A translation of the fixed bounds check from MIT 6.858 Lecture 11 on symbolic
execution. Access is allowed exactly when both `x < bound` and `y < bound`.
`Int` models Python's arbitrary-precision integers, and the result is a `Bool`.
There is deliberately no lower-bound restriction: negative inputs and negative
bounds are part of the domain. Equality with the bound must be rejected.

The executable Python checks are followed by universal specifications and
kernel-checked proofs. Bounded property-based tests are additional evidence,
not premises of any theorem. The last section gives a short-circuiting mutable
implementation and proves it equivalent to the functional one.
-/

namespace UnsafeDualBoundSafe

/-! ## Functional implementation -/

def safe_dual_bound (x y bound : Int) : Bool :=
  decide (x < bound) && decide (y < bound)

/-- Executable conjunction of the seven assertions in Python's `check`. -/
def check (candidate : Int → Int → Int → Bool) : Bool :=
  (candidate 3 5 10 == true) &&
  (candidate 3 15 10 == false) &&
  (candidate 12 5 10 == false) &&
  (candidate 9 9 10 == true) &&
  (candidate 3 10 10 == false) &&
  (candidate 20 30 10 == false) &&
  (candidate 0 0 0 == false)

/-! ## Original unit tests -/

example : safe_dual_bound 3 5 10 = true := by native_decide
example : safe_dual_bound 3 15 10 = false := by native_decide
example : safe_dual_bound 12 5 10 = false := by native_decide
example : safe_dual_bound 9 9 10 = true := by native_decide
example : safe_dual_bound 3 10 10 = false := by native_decide
example : safe_dual_bound 20 30 10 = false := by native_decide
example : safe_dual_bound 0 0 0 = false := by native_decide
example : check safe_dual_bound = true := by native_decide

-- Extra checks ensure that the full signed domain is preserved.
example : safe_dual_bound (-3) (-2) (-1) = true := by native_decide
example : safe_dual_bound (-3) (-1) (-1) = false := by native_decide
example : safe_dual_bound 10 3 10 = false := by native_decide

#eval check safe_dual_bound
#eval if check safe_dual_bound then IO.println "All tests passed."
  else IO.println "Candidate failed tests"

/-! ## Precondition -/

/-- Every integer triple is admissible; positivity is not required. -/
def Pre (_x _y _bound : Int) : Prop := True

/-! ## Properties and proofs -/

/-- Exact characterization of an allowed access. -/
def allow_iff_prop (x y bound : Int) : Prop :=
  safe_dual_bound x y bound = true ↔ x < bound ∧ y < bound

theorem allow_iff_thm (x y bound : Int) : allow_iff_prop x y bound := by
  simp [allow_iff_prop, safe_dual_bound]

/-- No accepted input violates either upper bound. -/
def safety_prop (x y bound : Int) : Prop :=
  safe_dual_bound x y bound = true → x < bound ∧ y < bound

theorem safety_thm (x y bound : Int) : safety_prop x y bound := by
  intro h
  exact (allow_iff_thm x y bound).mp h

/-- All inputs satisfying both strict inequalities are accepted. -/
def in_range_prop (x y bound : Int) : Prop :=
  x < bound → y < bound → safe_dual_bound x y bound = true

theorem in_range_thm (x y bound : Int) : in_range_prop x y bound := by
  intro hx hy
  exact (allow_iff_thm x y bound).mpr ⟨hx, hy⟩

/-- Either variable being at or above the bound is exactly rejection. -/
def rejection_prop (x y bound : Int) : Prop :=
  safe_dual_bound x y bound = false ↔ bound ≤ x ∨ bound ≤ y

theorem rejection_thm (x y bound : Int) : rejection_prop x y bound := by
  unfold rejection_prop
  by_cases hx : x < bound <;> by_cases hy : y < bound <;>
    simp [safe_dual_bound, hx, hy] <;> omega

/-- Both comparisons are strict, including when only one input is at the bound. -/
def boundary_prop (x y bound : Int) : Prop :=
  (x = bound ∨ y = bound) → safe_dual_bound x y bound = false

theorem boundary_thm (x y bound : Int) : boundary_prop x y bound := by
  intro h
  apply (rejection_thm x y bound).mpr
  rcases h with hx | hy
  · left
    omega
  · right
    omega

/-! ## Postcondition -/

def Post_prop (x y bound : Int) : Prop :=
  allow_iff_prop x y bound ∧
  safety_prop x y bound ∧
  in_range_prop x y bound ∧
  rejection_prop x y bound ∧
  boundary_prop x y bound

/-! ## Property-based tests

Each check exhaustively ranges over all 15,625 triples from `[-12, 12]³`.
In particular, these include negative bounds, zero bounds, equality, and all
four combinations of passing/failing comparisons. Each property and the full
postcondition has a separate executable Boolean test. No theorem uses them.
-/

def testInts : List Int :=
  (List.range 25).map (fun n => (n : Int) - 12)

def allSmallInputs (test : Int → Int → Int → Bool) : Bool :=
  testInts.all (fun x =>
    testInts.all (fun y =>
      testInts.all (fun bound => test x y bound)))

-- PBT for allow_iff_prop.
example : allSmallInputs (fun x y bound =>
    decide (safe_dual_bound x y bound = true ↔ x < bound ∧ y < bound)) = true := by
  native_decide

-- PBT for safety_prop.
example : allSmallInputs (fun x y bound =>
    decide (safe_dual_bound x y bound = true → x < bound ∧ y < bound)) = true := by
  native_decide

-- PBT for in_range_prop.
example : allSmallInputs (fun x y bound =>
    decide (x < bound → y < bound → safe_dual_bound x y bound = true)) = true := by
  native_decide

-- PBT for rejection_prop.
example : allSmallInputs (fun x y bound =>
    decide (safe_dual_bound x y bound = false ↔ bound ≤ x ∨ bound ≤ y)) = true := by
  native_decide

-- PBT for boundary_prop.
example : allSmallInputs (fun x y bound =>
    decide ((x = bound ∨ y = bound) → safe_dual_bound x y bound = false)) = true := by
  native_decide

/-- Executable expansion of the entire postcondition. -/
def postCheck (x y bound : Int) : Bool :=
  decide (
    (safe_dual_bound x y bound = true ↔ x < bound ∧ y < bound) ∧
    (safe_dual_bound x y bound = true → x < bound ∧ y < bound) ∧
    (x < bound → y < bound → safe_dual_bound x y bound = true) ∧
    (safe_dual_bound x y bound = false ↔ bound ≤ x ∨ bound ≤ y) ∧
    ((x = bound ∨ y = bound) → safe_dual_bound x y bound = false))

-- PBT for Post_prop, without requiring a Decidable instance for Post_prop.
example : allSmallInputs postCheck = true := by native_decide
#eval allSmallInputs postCheck

/-! ## Correctness for all admissible inputs -/

theorem correctness_thm (x y bound : Int) : Pre x y bound → Post_prop x y bound := by
  intro _
  exact ⟨allow_iff_thm x y bound, safety_thm x y bound,
    in_range_thm x y bound, rejection_thm x y bound, boundary_thm x y bound⟩

/-! ## Imperative implementation -/

/-- The second comparison is reached only if the first comparison succeeds. -/
def safe_dual_bound_imp (x y bound : Int) : Bool := Id.run do
  let mut allowed := false
  if x < bound then
    if y < bound then
      allowed := true
  return allowed

/-! ## Imperative tests -/

example : safe_dual_bound_imp 3 5 10 = true := by native_decide
example : safe_dual_bound_imp 3 15 10 = false := by native_decide
example : safe_dual_bound_imp 12 5 10 = false := by native_decide
example : safe_dual_bound_imp 9 9 10 = true := by native_decide
example : safe_dual_bound_imp 3 10 10 = false := by native_decide
example : safe_dual_bound_imp 20 30 10 = false := by native_decide
example : safe_dual_bound_imp 0 0 0 = false := by native_decide
example : check safe_dual_bound_imp = true := by native_decide
example : safe_dual_bound_imp (-3) (-2) (-1) = true := by native_decide
example : safe_dual_bound_imp (-3) (-1) (-1) = false := by native_decide
example : safe_dual_bound_imp 10 3 10 = false := by native_decide

#eval check safe_dual_bound_imp

-- Additional bounded comparison of both executable implementations.
example : allSmallInputs (fun x y bound =>
    safe_dual_bound x y bound == safe_dual_bound_imp x y bound) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem equivalence_thm (x y bound : Int) :
    safe_dual_bound x y bound = safe_dual_bound_imp x y bound := by
  by_cases hx : x < bound <;> by_cases hy : y < bound <;>
    simp [safe_dual_bound, safe_dual_bound_imp, hx, hy]

end UnsafeDualBoundSafe
end Agent
