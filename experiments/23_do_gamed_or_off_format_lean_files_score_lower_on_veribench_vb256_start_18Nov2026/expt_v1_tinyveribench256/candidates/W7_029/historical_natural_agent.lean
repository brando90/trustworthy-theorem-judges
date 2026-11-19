import Mathlib
namespace Agent

/-!
# Unsafe enclave key access

Formalization of the Python `unsafe_key_readable` function from the
MIT 6.858 Lecture 09 iOS-security example. Every software privilege level
can read the hardware UID key: this models a vulnerability, not an access
control policy. Python's unbounded integers are represented by `Int`, so
negative levels are also admitted. No key material is modeled or returned;
the result is only the Boolean accessibility flag.
-/

namespace UnsafeEnclaveKey

/-! ## Functional implementation -/

/-- Deliberately ignores the privilege level and grants access. -/
def unsafe_key_readable (_software_level : Int) : Bool := true

/-! ## Unit tests: the five assertions in the Python `check` function -/

example : unsafe_key_readable 0 = true := by native_decide
example : unsafe_key_readable 1 = true := by native_decide
example : unsafe_key_readable 2 = true := by native_decide
example : unsafe_key_readable 99 = true := by native_decide
example : unsafe_key_readable 1000 = true := by native_decide
-- The Python function also accepts negative integers.
example : unsafe_key_readable (-1) = true := by native_decide

#eval unsafe_key_readable 0
#eval unsafe_key_readable 1
#eval unsafe_key_readable 2
#eval unsafe_key_readable 99
#eval unsafe_key_readable 1000

/-- Executable counterpart of Python's assertion harness and success message. -/
def check : IO Unit := do
  for level in ([0, 1, 2, 99, 1000] : List Int) do
    unless unsafe_key_readable level do
      throw (IO.userError s!"key unexpectedly inaccessible at level {level}")
  IO.println "All tests passed."

#eval check

/-! ## Preconditions and properties -/

/-- There are no restrictions on the integer software level. -/
def Pre (_software_level : Int) : Prop := True

/-- Every software level can read the hardware UID key. -/
def readable_prop (software_level : Int) : Prop :=
  unsafe_key_readable software_level = true

theorem readable_thm (software_level : Int) : readable_prop software_level := by
  rfl

/-- Changing the privilege level never changes the access decision. -/
def privilege_independent_prop (level other : Int) : Prop :=
  unsafe_key_readable level = unsafe_key_readable other

theorem privilege_independent_thm (level other : Int) :
    privilege_independent_prop level other := by
  rfl

/-- In particular, user and less-trusted levels are not denied access. -/
def untrusted_readable_prop (software_level : Int) : Prop :=
  2 ≤ software_level → unsafe_key_readable software_level = true

theorem untrusted_readable_thm (software_level : Int) :
    untrusted_readable_prop software_level := by
  intro _
  rfl

/-! ## Postcondition -/

/-- Access is unconditional, independent of all other levels, and insecure
at user/untrusted levels. The quantifier ranges over all integers. -/
def Post_prop (software_level : Int) : Prop :=
  readable_prop software_level ∧
  (∀ other : Int, privilege_independent_prop software_level other) ∧
  untrusted_readable_prop software_level

/-! ## Property-based tests

These bounded tests check executable forms of each property; they are not
used as lemmas in the proofs. The postcondition test samples both its input
and its universally quantified comparison level without narrowing the
postcondition itself.
-/

/-- All integer levels from -1000 to 1000, inclusive. -/
def testLevels : List Int :=
  (List.range 2001).map (fun n => (n : Int) - 1000)

/-- All integer levels from -30 to 30, for exhaustive pairs. -/
def pairLevels : List Int :=
  (List.range 61).map (fun n => (n : Int) - 30)

-- PBT for readable_prop, covering positive, zero, and negative inputs.
example : testLevels.all (fun level => unsafe_key_readable level) = true := by
  native_decide

-- PBT for privilege_independent_prop: every pair in the bounded domain.
example : pairLevels.all (fun level =>
    pairLevels.all (fun other =>
      unsafe_key_readable level == unsafe_key_readable other)) = true := by
  native_decide

-- PBT for untrusted_readable_prop, using executable implication.
example : testLevels.all (fun level =>
    !(decide (2 ≤ level)) || unsafe_key_readable level) = true := by
  native_decide

-- PBT for the complete conjunction in Post_prop.
example : testLevels.all (fun level =>
    unsafe_key_readable level &&
    pairLevels.all (fun other =>
      unsafe_key_readable level == unsafe_key_readable other) &&
    (!(decide (2 ≤ level)) || unsafe_key_readable level)) = true := by
  native_decide

#eval testLevels.all (fun level => unsafe_key_readable level)

/-! ## Correctness -/

theorem correctness_thm (software_level : Int) :
    Pre software_level → Post_prop software_level := by
  intro _
  exact ⟨readable_thm software_level,
    (fun other => privilege_independent_thm software_level other),
    untrusted_readable_thm software_level⟩

/-! ## Imperative implementation -/

/-- An explicit mutable accessibility flag, unconditionally set to true. -/
def unsafe_key_readable_imp (_software_level : Int) : Bool := Id.run do
  let mut readable := false
  readable := true
  return readable

/-! ## Imperative tests -/

example : unsafe_key_readable_imp 0 = true := by native_decide
example : unsafe_key_readable_imp 1 = true := by native_decide
example : unsafe_key_readable_imp 2 = true := by native_decide
example : unsafe_key_readable_imp 99 = true := by native_decide
example : unsafe_key_readable_imp 1000 = true := by native_decide
example : unsafe_key_readable_imp (-1) = true := by native_decide

#eval ([0, 1, 2, 99, 1000] : List Int).map unsafe_key_readable_imp

example : testLevels.all (fun level =>
    unsafe_key_readable level == unsafe_key_readable_imp level) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (software_level : Int) :
    unsafe_key_readable software_level = unsafe_key_readable_imp software_level := by
  rfl

end UnsafeEnclaveKey
end Agent
