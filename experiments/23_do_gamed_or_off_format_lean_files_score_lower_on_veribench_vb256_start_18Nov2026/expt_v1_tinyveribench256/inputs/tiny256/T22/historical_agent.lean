import Mathlib
namespace Agent

/-!
# Safe WebAssembly stack-depth checking

This file formalizes a stack guard that permits an operation exactly when the
current stack depth does not exceed its declared maximum.  It includes the
functional and imperative versions, executable tests corresponding to the
Python program, and proofs of the guard's boundary and overflow behavior.
-/

namespace UnsafeWasmStackSafe

/-- Return `true` exactly when `stackDepth` is at most `maxDepth`. -/
def safeWasmStack (stackDepth maxDepth : Int) : Bool :=
  decide (stackDepth ≤ maxDepth)

example : safeWasmStack 5 100 = true := by native_decide
example : safeWasmStack 100 100 = true := by native_decide
example : safeWasmStack 101 100 = false := by native_decide
example : safeWasmStack 9999 10 = false := by native_decide
example : safeWasmStack 0 0 = true := by native_decide

#eval safeWasmStack 5 100
#eval safeWasmStack 100 100
#eval safeWasmStack 101 100
#eval safeWasmStack 9999 10
#eval safeWasmStack 0 0

/-- Stack depths and declared limits are nonnegative. -/
def Pre (stackDepth maxDepth : Int) : Prop :=
  0 ≤ stackDepth ∧ 0 ≤ maxDepth

/-- The Boolean guard precisely represents the stack-depth inequality. -/
def enforcesLimit_prop (stackDepth maxDepth : Int) : Prop :=
  safeWasmStack stackDepth maxDepth = true ↔ stackDepth ≤ maxDepth

theorem enforcesLimit_thm (stackDepth maxDepth : Int) :
    enforcesLimit_prop stackDepth maxDepth := by
  simp [enforcesLimit_prop, safeWasmStack]

/-- A stack exactly at its limit is accepted. -/
def atLimit_prop (maxDepth : Int) : Prop :=
  safeWasmStack maxDepth maxDepth = true

theorem atLimit_thm (maxDepth : Int) : atLimit_prop maxDepth := by
  simp [atLimit_prop, safeWasmStack]

/-- Every stack deeper than its maximum is rejected. -/
def overLimitBlocked_prop (stackDepth maxDepth : Int) : Prop :=
  maxDepth < stackDepth → safeWasmStack stackDepth maxDepth = false

theorem overLimitBlocked_thm (stackDepth maxDepth : Int) :
    overLimitBlocked_prop stackDepth maxDepth := by
  simp [overLimitBlocked_prop, safeWasmStack]

/-- All required behavior of the safe stack guard. -/
def Post_prop (stackDepth maxDepth : Int) : Prop :=
  enforcesLimit_prop stackDepth maxDepth ∧
    (stackDepth = maxDepth → safeWasmStack stackDepth maxDepth = true) ∧
    overLimitBlocked_prop stackDepth maxDepth

/-- For valid stack-depth inputs, the functional guard has the required behavior. -/
theorem safeWasmStack_correct (stackDepth maxDepth : Int) :
    Pre stackDepth maxDepth → Post_prop stackDepth maxDepth := by
  intro _
  refine ⟨enforcesLimit_thm stackDepth maxDepth, ?_,
    overLimitBlocked_thm stackDepth maxDepth⟩
  intro h
  subst stackDepth
  exact atLimit_thm maxDepth

/-- Imperative rendition of the guard, using mutable state as in an executable check. -/
def safeWasmStackImperative (stackDepth maxDepth : Int) : Bool := Id.run do
  let mut allowed := false
  if stackDepth ≤ maxDepth then
    allowed := true
  return allowed

example : safeWasmStackImperative 5 100 = true := by native_decide
example : safeWasmStackImperative 100 100 = true := by native_decide
example : safeWasmStackImperative 101 100 = false := by native_decide
example : safeWasmStackImperative 9999 10 = false := by native_decide
example : safeWasmStackImperative 0 0 = true := by native_decide

#eval safeWasmStackImperative 5 100
#eval safeWasmStackImperative 100 100
#eval safeWasmStackImperative 101 100
#eval safeWasmStackImperative 9999 10
#eval safeWasmStackImperative 0 0

/-- The functional and imperative implementations agree on every Python integer input. -/
theorem safeWasmStack_equiv (stackDepth maxDepth : Int) :
    safeWasmStack stackDepth maxDepth =
      safeWasmStackImperative stackDepth maxDepth := by
  by_cases h : stackDepth ≤ maxDepth <;>
    simp [safeWasmStack, safeWasmStackImperative, h]

end UnsafeWasmStackSafe
end Agent
