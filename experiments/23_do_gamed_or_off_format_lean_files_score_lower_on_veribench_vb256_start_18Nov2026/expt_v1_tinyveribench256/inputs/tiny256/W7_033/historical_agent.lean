import Mathlib
namespace Agent

/-!
# Unsafe XSS echo

Formalization of the Python function `unsafeXSSEcho`. The Boolean input records
whether user-supplied content contains scripts; the Boolean result records whether
that content is rendered. The function ignores the input and always renders it.
Thus script-bearing input is still rendered: this models the unsafe behavior,
not a sanitizing implementation. Both Boolean inputs are admissible.

The tests exhaust the Boolean domain (and all four pairs for independence).
Named theorems use kernel-checked proofs, independently of the executable tests.
Reference: MIT 6.858 Lecture 12, Web Security.
-/

namespace UnsafeXSSEcho

/-- Render the input regardless of whether it contains scripts. -/
def unsafeXSSEcho (_inputHasScript : Bool) : Bool :=
  true

-- Unit tests corresponding to the two assertions in Python's `check`.
example : unsafeXSSEcho false = true := by native_decide
example : unsafeXSSEcho true = true := by native_decide

#eval unsafeXSSEcho false
#eval unsafeXSSEcho true
#eval if unsafeXSSEcho false && unsafeXSSEcho true then
  "All tests passed." else "Test failed."

/-- There is no restriction on the presence of scripts. -/
def Pre (_inputHasScript : Bool) : Prop := True

/-- Every input is rendered. -/
def alwaysRenders_prop (inputHasScript : Bool) : Prop :=
  unsafeXSSEcho inputHasScript = true

theorem alwaysRenders_thm (inputHasScript : Bool) :
    alwaysRenders_prop inputHasScript := by
  rfl

/-- Script-free input is rendered, matching the safe-input assertion. -/
def safeInput_prop (inputHasScript : Bool) : Prop :=
  inputHasScript = false → unsafeXSSEcho inputHasScript = true

theorem safeInput_thm (inputHasScript : Bool) :
    safeInput_prop inputHasScript := by
  intro _
  rfl

/-- The vulnerability: even script-bearing input is rendered. -/
def scriptInput_prop (inputHasScript : Bool) : Prop :=
  inputHasScript = true → unsafeXSSEcho inputHasScript = true

theorem scriptInput_thm (inputHasScript : Bool) :
    scriptInput_prop inputHasScript := by
  intro _
  rfl

/-- Changing the script-presence flag cannot change the rendering decision. -/
def inputIndependent_prop (inputHasScript other : Bool) : Prop :=
  unsafeXSSEcho inputHasScript = unsafeXSSEcho other

theorem inputIndependent_thm (inputHasScript other : Bool) :
    inputIndependent_prop inputHasScript other := by
  rfl

/-- Full behavioral contract, including the deliberately unsafe script case. -/
def Post_prop (inputHasScript : Bool) : Prop :=
  alwaysRenders_prop inputHasScript ∧
  safeInput_prop inputHasScript ∧
  scriptInput_prop inputHasScript ∧
  (∀ other : Bool, inputIndependent_prop inputHasScript other)

-- Property-based tests: exhaustive bounded checks of executable Boolean forms.
-- PBT for alwaysRenders_prop: both inputs must produce true.
example : ([false, true] : List Bool).all
    (fun b => unsafeXSSEcho b == true) = true := by
  native_decide

-- PBT for safeInput_prop: Boolean implication from b = false.
example : ([false, true] : List Bool).all
    (fun b => (!(b == false)) || (unsafeXSSEcho b == true)) = true := by
  native_decide

-- PBT for scriptInput_prop: Boolean implication from b = true.
example : ([false, true] : List Bool).all
    (fun b => (!(b == true)) || (unsafeXSSEcho b == true)) = true := by
  native_decide

-- PBT for inputIndependent_prop: exhaust all four input pairs.
example : ([false, true] : List Bool).all
    (fun b => ([false, true] : List Bool).all
      (fun other => unsafeXSSEcho b == unsafeXSSEcho other)) = true := by
  native_decide

-- PBT for Post_prop: check every conjunct on every admissible input.
-- The finite inner enumeration implements the universal quantifier over Bool.
example : ([false, true] : List Bool).all
    (fun b =>
      (unsafeXSSEcho b == true) &&
      ((!(b == false)) || (unsafeXSSEcho b == true)) &&
      ((!(b == true)) || (unsafeXSSEcho b == true)) &&
      ([false, true] : List Bool).all
        (fun other => unsafeXSSEcho b == unsafeXSSEcho other)) = true := by
  native_decide

/-- Correctness means faithful execution of the unsafe program, not XSS safety. -/
theorem correctness_thm (inputHasScript : Bool) :
    Pre inputHasScript → Post_prop inputHasScript := by
  intro _
  exact ⟨alwaysRenders_thm inputHasScript,
    safeInput_thm inputHasScript,
    scriptInput_thm inputHasScript,
    fun other => inputIndependent_thm inputHasScript other⟩

/-- Mutable-state version: unconditionally set the rendering decision to true. -/
def unsafeXSSEchoImperative (_inputHasScript : Bool) : Bool := Id.run do
  let mut renders := false
  renders := true
  return renders

-- Imperative unit tests.
example : unsafeXSSEchoImperative false = true := by native_decide
example : unsafeXSSEchoImperative true = true := by native_decide

#eval unsafeXSSEchoImperative false
#eval unsafeXSSEchoImperative true

-- Exhaustive executable comparison of the implementations.
example : ([false, true] : List Bool).all
    (fun b => unsafeXSSEcho b == unsafeXSSEchoImperative b) = true := by
  native_decide

/-- The implementations agree on the entire input domain. -/
theorem functional_imperative_equivalence_thm (inputHasScript : Bool) :
    unsafeXSSEcho inputHasScript = unsafeXSSEchoImperative inputHasScript := by
  rfl

end UnsafeXSSEcho
end Agent
