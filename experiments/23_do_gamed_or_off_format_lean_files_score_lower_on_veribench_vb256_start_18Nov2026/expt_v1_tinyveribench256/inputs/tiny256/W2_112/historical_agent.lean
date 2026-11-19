import Mathlib
namespace Agent

/-!
# Safe null-pointer guard

A translation of the Python `safe_ptr_check` program. Python's unbounded
integers are modeled by `Int`: the guard accepts exactly the nonzero values,
including negative integers, and rejects zero. This is a guard only; no memory
is dereferenced or assumed to be mapped. In particular, the result at zero
cannot depend on whether address zero is mapped.

The specifications characterize both possible Boolean results. Tests are
executable evidence; the named theorems are proved separately in Lean.
-/

namespace UnsafeNullPtrDerefSafe

/-! ## Functional implementation -/

/-- Return true exactly when the integer pointer value is non-null. -/
def safe_ptr_check (ptr_val : Int) : Bool :=
  decide (ptr_val ≠ 0)

/-! ## Unit tests -/

example : safe_ptr_check 1 = true := by native_decide
example : safe_ptr_check 0xdeadbeef = true := by native_decide
example : safe_ptr_check 0 = false := by native_decide
example : safe_ptr_check (-1) = true := by native_decide

/-- The three assertions and success message in the Python test driver. -/
def check : IO Unit := do
  unless safe_ptr_check 1 do
    throw (IO.userError "valid ptr rejected")
  unless safe_ptr_check 0xdeadbeef do
    throw (IO.userError "non-null ptr rejected")
  if safe_ptr_check 0 then
    throw (IO.userError "null ptr not blocked")
  IO.println "All tests passed."

#eval check
#eval [safe_ptr_check 1, safe_ptr_check 0xdeadbeef, safe_ptr_check 0,
  safe_ptr_check (-1)]

/-! ## Preconditions and properties -/

/-- Every Python integer is admissible; non-nullness is not a precondition. -/
def Pre (_ptr_val : Int) : Prop := True

/-- Acceptance is both sound and complete for non-null integer values. -/
def nonzero_iff_prop (ptr_val : Int) : Prop :=
  safe_ptr_check ptr_val = true ↔ ptr_val ≠ 0

theorem nonzero_iff_thm (ptr_val : Int) : nonzero_iff_prop ptr_val := by
  simp [nonzero_iff_prop, safe_ptr_check]

/-- Rejection occurs exactly for the null value, not for other integers. -/
def null_iff_prop (ptr_val : Int) : Prop :=
  safe_ptr_check ptr_val = false ↔ ptr_val = 0

theorem null_iff_thm (ptr_val : Int) : null_iff_prop ptr_val := by
  simp [null_iff_prop, safe_ptr_check]

/-- The null address is blocked unconditionally. -/
theorem null_blocked_thm : safe_ptr_check 0 = false := by
  simp [safe_ptr_check]

/-! ## Postcondition -/

/-- The complete characterization of the guard's result. -/
def Post_prop (ptr_val : Int) : Prop :=
  nonzero_iff_prop ptr_val ∧ null_iff_prop ptr_val

/-! ## Property-based tests

Exhaustively test every integer from -256 to 256, together with large positive
and negative pointer values. Each check below uses the executable form of its
named property, rather than requiring a Decidable instance for that definition.
-/

def pointerSamples : List Int :=
  (List.range 513).map (fun n => (n : Int) - 256) ++
    [0xdeadbeef, -(0xdeadbeef : Int)]

-- PBT for nonzero_iff_prop.
example : pointerSamples.all (fun p =>
    decide (safe_ptr_check p = true ↔ p ≠ 0)) = true := by
  native_decide

-- PBT for null_iff_prop.
example : pointerSamples.all (fun p =>
    decide (safe_ptr_check p = false ↔ p = 0)) = true := by
  native_decide

-- PBT for Post_prop: both characterizations must hold on each input.
example : pointerSamples.all (fun p =>
    decide ((safe_ptr_check p = true ↔ p ≠ 0) ∧
      (safe_ptr_check p = false ↔ p = 0))) = true := by
  native_decide

#eval pointerSamples.all (fun p =>
  decide ((safe_ptr_check p = true ↔ p ≠ 0) ∧
    (safe_ptr_check p = false ↔ p = 0)))

/-! ## Correctness -/

theorem correctness_thm (ptr_val : Int) : Pre ptr_val → Post_prop ptr_val := by
  intro _
  exact ⟨nonzero_iff_thm ptr_val, null_iff_thm ptr_val⟩

/-! ## Imperative implementation -/

/-- A mutable local Boolean implements the same non-null guard. -/
def safe_ptr_check_imperative (ptr_val : Int) : Bool := Id.run do
  let mut accepted := false
  if ptr_val ≠ 0 then
    accepted := true
  return accepted

/-! ## Imperative tests -/

example : safe_ptr_check_imperative 1 = true := by native_decide
example : safe_ptr_check_imperative 0xdeadbeef = true := by native_decide
example : safe_ptr_check_imperative 0 = false := by native_decide
example : safe_ptr_check_imperative (-1) = true := by native_decide

#eval [safe_ptr_check_imperative 1, safe_ptr_check_imperative 0xdeadbeef,
  safe_ptr_check_imperative 0, safe_ptr_check_imperative (-1)]

example : pointerSamples.all (fun p =>
    safe_ptr_check p == safe_ptr_check_imperative p) = true := by
  native_decide

/-! ## Functional-imperative equivalence -/

theorem functional_imperative_equivalence_thm (ptr_val : Int) :
    safe_ptr_check ptr_val = safe_ptr_check_imperative ptr_val := by
  by_cases h : ptr_val = 0 <;>
    simp [safe_ptr_check, safe_ptr_check_imperative, h]

end UnsafeNullPtrDerefSafe
end Agent
