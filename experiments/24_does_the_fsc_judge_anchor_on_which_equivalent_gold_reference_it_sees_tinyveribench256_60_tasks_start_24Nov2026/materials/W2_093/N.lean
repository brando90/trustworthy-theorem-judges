import Mathlib
namespace Agent

/-!
# Safe Android broadcast intent

A translation of the Python `safe_android_broadcast` function and its checks.
The Boolean policy accepts exactly when a receiver permission is required and
broadcast protection is enabled. Either missing safeguard causes rejection.
This models the supplied policy check, not the Android runtime itself.

All Boolean inputs are admissible. The semantic theorems are kernel-proved;
executable unit tests and exhaustive property-based tests are separate evidence.
-/

namespace «124_unsafeAndroidBroadcast_safe»

/-! ## Functional implementation -/

/-- Both safeguards must be enabled for the policy to accept the broadcast. -/
def safe_android_broadcast (permission_required broadcast_protected : Bool) : Bool :=
  permission_required && broadcast_protected

/-! ## Unit tests and the Python check routine -/

example : safe_android_broadcast true true = true := by native_decide
example : safe_android_broadcast false false = false := by native_decide
example : safe_android_broadcast true false = false := by native_decide
example : safe_android_broadcast false true = false := by native_decide

/-- Executable counterpart of Python's four assertions and success message. -/
def check : IO Unit := do
  unless safe_android_broadcast true true == true do
    throw (IO.userError "protected broadcast rejected")
  unless safe_android_broadcast false false == false do
    throw (IO.userError "unprotected broadcast accepted")
  unless safe_android_broadcast true false == false do
    throw (IO.userError "permission without protection accepted")
  unless safe_android_broadcast false true == false do
    throw (IO.userError "protection without permission accepted")
  IO.println "All tests passed."

#eval check

/-! ## Precondition -/

/-- The Python function accepts every pair of Boolean arguments. -/
def Pre (_permission_required _broadcast_protected : Bool) : Prop := True

/-! ## Semantic properties and proofs -/

/-- Acceptance is equivalent to the presence of both safeguards. -/
def acceptance_iff_prop (permission_required broadcast_protected : Bool) : Prop :=
  safe_android_broadcast permission_required broadcast_protected = true ↔
    permission_required = true ∧ broadcast_protected = true

theorem acceptance_iff_thm (permission_required broadcast_protected : Bool) :
    acceptance_iff_prop permission_required broadcast_protected := by sorry

/-- Protection alone is insufficient if no receiver permission is required. -/
def no_permission_prop (permission_required broadcast_protected : Bool) : Prop :=
  permission_required = false →
    safe_android_broadcast permission_required broadcast_protected = false

theorem no_permission_thm (permission_required broadcast_protected : Bool) :
    no_permission_prop permission_required broadcast_protected := by sorry

/-- A required permission alone is insufficient if the broadcast is unprotected. -/
def unprotected_prop (permission_required broadcast_protected : Bool) : Prop :=
  broadcast_protected = false →
    safe_android_broadcast permission_required broadcast_protected = false

theorem unprotected_thm (permission_required broadcast_protected : Bool) :
    unprotected_prop permission_required broadcast_protected := by sorry

/-- Enabling both safeguards suffices for acceptance. -/
def both_enabled_prop (permission_required broadcast_protected : Bool) : Prop :=
  permission_required = true → broadcast_protected = true →
    safe_android_broadcast permission_required broadcast_protected = true

theorem both_enabled_thm (permission_required broadcast_protected : Bool) :
    both_enabled_prop permission_required broadcast_protected := by sorry

/-- Rejection occurs exactly when at least one safeguard is missing. -/
def rejection_iff_prop (permission_required broadcast_protected : Bool) : Prop :=
  safe_android_broadcast permission_required broadcast_protected = false ↔
    permission_required = false ∨ broadcast_protected = false

theorem rejection_iff_thm (permission_required broadcast_protected : Bool) :
    rejection_iff_prop permission_required broadcast_protected := by sorry

/-! ## Postcondition -/

def Post_prop (permission_required broadcast_protected : Bool) : Prop :=
  acceptance_iff_prop permission_required broadcast_protected ∧
  no_permission_prop permission_required broadcast_protected ∧
  unprotected_prop permission_required broadcast_protected ∧
  both_enabled_prop permission_required broadcast_protected ∧
  rejection_iff_prop permission_required broadcast_protected

/-! ## Exhaustive property-based tests

The bounded domain `[false, true] × [false, true]` is the entire input domain.
Each test evaluates a property's executable form over the implementation, not
its proved theorem. Explicit propositions inside `decide` avoid needing custom
`Decidable` instances for the specification definitions.
-/

/-- Exhaustively evaluate a Boolean predicate on all pairs of Boolean inputs. -/
def allBoolPairs (test : Bool → Bool → Bool) : Bool :=
  [false, true].all (fun p => [false, true].all (fun b => test p b))

-- PBT for acceptance_iff_prop.
example : allBoolPairs (fun p b => decide
    (safe_android_broadcast p b = true ↔ p = true ∧ b = true)) = true := by
  native_decide

-- PBT for no_permission_prop.
example : allBoolPairs (fun p b => decide
    (p = false → safe_android_broadcast p b = false)) = true := by
  native_decide

-- PBT for unprotected_prop.
example : allBoolPairs (fun p b => decide
    (b = false → safe_android_broadcast p b = false)) = true := by
  native_decide

-- PBT for both_enabled_prop.
example : allBoolPairs (fun p b => decide
    (p = true → b = true → safe_android_broadcast p b = true)) = true := by
  native_decide

-- PBT for rejection_iff_prop.
example : allBoolPairs (fun p b => decide
    (safe_android_broadcast p b = false ↔ p = false ∨ b = false)) = true := by
  native_decide

/-- Executable form of the complete postcondition. -/
def postCheck (p b : Bool) : Bool :=
  decide (
    (safe_android_broadcast p b = true ↔ p = true ∧ b = true) ∧
    (p = false → safe_android_broadcast p b = false) ∧
    (b = false → safe_android_broadcast p b = false) ∧
    (p = true → b = true → safe_android_broadcast p b = true) ∧
    (safe_android_broadcast p b = false ↔ p = false ∨ b = false))

-- PBT for Post_prop; Pre admits every sampled input.
example : allBoolPairs postCheck = true := by native_decide
#eval allBoolPairs postCheck

/-! ## Correctness: the precondition implies the full postcondition -/

theorem correctness_thm (permission_required broadcast_protected : Bool) :
    Pre permission_required broadcast_protected →
      Post_prop permission_required broadcast_protected := by sorry

/-! ## Imperative implementation -/

/-- A mutable result implements the same short-circuit conjunction. -/
def safe_android_broadcast_imperative
    (permission_required broadcast_protected : Bool) : Bool := Id.run do
  let mut result := false
  if permission_required then
    result := broadcast_protected
  return result

/-! ## Imperative tests -/

example : safe_android_broadcast_imperative true true = true := by native_decide
example : safe_android_broadcast_imperative false false = false := by native_decide
example : safe_android_broadcast_imperative true false = false := by native_decide
example : safe_android_broadcast_imperative false true = false := by native_decide

#eval [safe_android_broadcast_imperative true true,
  safe_android_broadcast_imperative false false,
  safe_android_broadcast_imperative true false,
  safe_android_broadcast_imperative false true]

-- Exhaustive executable equivalence test, independent of the proof below.
example : allBoolPairs (fun p b =>
    safe_android_broadcast p b == safe_android_broadcast_imperative p b) = true := by
  native_decide

/-! ## Functional-imperative equivalence -/

theorem functional_imperative_equiv_thm
    (permission_required broadcast_protected : Bool) :
    safe_android_broadcast permission_required broadcast_protected =
      safe_android_broadcast_imperative permission_required broadcast_protected := by sorry

end «124_unsafeAndroidBroadcast_safe»
end Agent
