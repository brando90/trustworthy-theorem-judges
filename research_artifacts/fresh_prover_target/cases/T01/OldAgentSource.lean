import Mathlib

/-!
# String length

This file formalizes the Python function that returns the number of characters
in a string.  Since the Lean function accepts a value of type `String`, the
Python precondition check (`isinstance(s, str)`) is enforced by Lean's type
system.
-/

namespace MyStringLength

/-! ## Functional implementation -/

/-- Return the number of characters in `s`. -/
def prog (s : String) : Nat :=
  s.length

/-! ## Functional unit tests -/

example : prog "hello" = 5 := by native_decide

example : prog "" = 0 := by native_decide

#eval prog "hello"
#eval prog ""

/-! ## Specification -/

/-- Every `String` satisfies the source program's string-input precondition. -/
def Pre (_s : String) : Prop :=
  True

/-- The returned value is precisely Lean's character count for the input. -/
def length_prop (s : String) (result : Nat) : Prop :=
  result = s.length

theorem length_thm (s : String) : length_prop s (prog s) := by
  rfl

/-- In particular, the empty string has length zero. -/
def empty_prop (s : String) (result : Nat) : Prop :=
  s = "" → result = 0

theorem empty_thm (s : String) : empty_prop s (prog s) := by
  intro hs
  subst s
  rfl

/-- The complete postcondition combines the general length specification and
the explicitly documented empty-string edge case. -/
def Post_prop (s : String) (result : Nat) : Prop :=
  length_prop s result ∧ empty_prop s result

theorem prog_correct (s : String) : Pre s → Post_prop s (prog s) := by
  intro _
  exact ⟨length_thm s, empty_thm s⟩

/-! ## Imperative implementation -/

/-- An imperative presentation of the same computation. -/
def progImperative (s : String) : Nat := Id.run do
  let mut result := 0
  result := s.length
  return result

/-! ## Imperative unit tests -/

example : progImperative "hello" = 5 := by native_decide

example : progImperative "" = 0 := by native_decide

#eval progImperative "hello"
#eval progImperative ""

theorem functional_eq_imperative (s : String) :
    prog s = progImperative s := by
  rfl

end MyStringLength
