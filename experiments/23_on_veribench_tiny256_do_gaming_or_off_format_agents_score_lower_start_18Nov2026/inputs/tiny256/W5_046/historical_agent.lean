import Mathlib
namespace Agent

/-!
# Unsafe Android broadcast

This file translates the Python `unsafe_android_broadcast` function and its
four assertions. The Boolean result models whether the broadcast is sent:
it is always `true`, regardless of either security flag. In particular, the
translation preserves the vulnerability rather than adding a permission check.
It does not model Android receivers or claim to execute an actual broadcast.

Every Boolean input is admissible. The specifications describe unconditional
sending, independence from both flags, and acceptance when permission or
broadcast protection is absent. Exhaustive finite property-based tests cover
the entire Boolean domain; the named theorems are proved separately by kernel
reduction. A mutable-state implementation models the same unconditional send.
-/

namespace «124_unsafeAndroidBroadcast»

/-! ## Functional implementation -/

/-- The Python function ignores both flags and unconditionally returns `True`. -/
def unsafe_android_broadcast
    (_permission_required _broadcast_protected : Bool) : Bool :=
  true

/-! ## Unit tests and the Python test runner -/

example : unsafe_android_broadcast true true = true := by native_decide
example : unsafe_android_broadcast false false = true := by native_decide
example : unsafe_android_broadcast true false = true := by native_decide
example : unsafe_android_broadcast false true = true := by native_decide

/-- The four Python assertions, with their original failure messages. -/
def check : IO Unit := do
  unless unsafe_android_broadcast true true do
    throw (IO.userError "protected broadcast rejected")
  unless unsafe_android_broadcast false false do
    throw (IO.userError "vuln: unprotected broadcast accepted")
  unless unsafe_android_broadcast true false do
    throw (IO.userError "vuln: mixed state accepted")
  unless unsafe_android_broadcast false true do
    throw (IO.userError "vuln: another mixed state accepted")
  IO.println "All tests passed."

#eval check

/-! ## Precondition -/

/-- There are no restrictions on the two Boolean arguments. -/
def Pre (_permission_required _broadcast_protected : Bool) : Prop := True

/-! ## Properties and proofs -/

/-- A broadcast is sent for every combination of flags. -/
def always_sent_prop (permission_required broadcast_protected : Bool) : Prop :=
  unsafe_android_broadcast permission_required broadcast_protected = true

theorem always_sent_thm (permission_required broadcast_protected : Bool) :
    always_sent_prop permission_required broadcast_protected := by
  rfl

/-- Changing either or both flags cannot affect the result. -/
def ignores_flags_prop (permission_required broadcast_protected : Bool) : Prop :=
  ∀ other_permission other_protection : Bool,
    unsafe_android_broadcast permission_required broadcast_protected =
      unsafe_android_broadcast other_permission other_protection

theorem ignores_flags_thm (permission_required broadcast_protected : Bool) :
    ignores_flags_prop permission_required broadcast_protected := by
  intro other_permission other_protection
  rfl

/-- Absence of a receiver-permission requirement never prevents sending. -/
def missing_permission_accepted_prop (broadcast_protected : Bool) : Prop :=
  unsafe_android_broadcast false broadcast_protected = true

theorem missing_permission_accepted_thm (broadcast_protected : Bool) :
    missing_permission_accepted_prop broadcast_protected := by
  rfl

/-- Even an unprotected broadcast is accepted, whatever the permission flag. -/
def unprotected_broadcast_accepted_prop (permission_required : Bool) : Prop :=
  unsafe_android_broadcast permission_required false = true

theorem unprotected_broadcast_accepted_thm (permission_required : Bool) :
    unprotected_broadcast_accepted_prop permission_required := by
  rfl

/-! ## Postcondition -/

/-- The complete behavioral specification, including the unsafe cases. -/
def Post_prop (permission_required broadcast_protected : Bool) : Prop :=
  always_sent_prop permission_required broadcast_protected ∧
  ignores_flags_prop permission_required broadcast_protected ∧
  missing_permission_accepted_prop broadcast_protected ∧
  unprotected_broadcast_accepted_prop permission_required

/-! ## Exhaustive property-based tests

The list `[false, true]` covers all inhabitants of `Bool`. Each test below
checks the corresponding executable Boolean expression, not a `Decidable`
instance synthesized for the specification. These tests are not used by any
named theorem.
-/

-- PBT for always_sent_prop: all four input pairs.
example :
    (([false, true] : List Bool).all fun permission_required =>
      ([false, true] : List Bool).all fun broadcast_protected =>
        unsafe_android_broadcast permission_required broadcast_protected == true) =
      true := by
  native_decide

-- PBT for ignores_flags_prop: all sixteen pairs of input pairs.
example :
    (([false, true] : List Bool).all fun permission_required =>
      ([false, true] : List Bool).all fun broadcast_protected =>
        ([false, true] : List Bool).all fun other_permission =>
          ([false, true] : List Bool).all fun other_protection =>
            unsafe_android_broadcast permission_required broadcast_protected ==
              unsafe_android_broadcast other_permission other_protection) =
      true := by
  native_decide

-- PBT for missing_permission_accepted_prop: both protection states.
example :
    (([false, true] : List Bool).all fun broadcast_protected =>
      unsafe_android_broadcast false broadcast_protected == true) = true := by
  native_decide

-- PBT for unprotected_broadcast_accepted_prop: both permission states.
example :
    (([false, true] : List Bool).all fun permission_required =>
      unsafe_android_broadcast permission_required false == true) = true := by
  native_decide

-- PBT for Post_prop: its complete Boolean conjunction on every input pair.
-- Since Pre is True, every enumerated input is admissible.
example :
    (([false, true] : List Bool).all fun permission_required =>
      ([false, true] : List Bool).all fun broadcast_protected =>
        (unsafe_android_broadcast permission_required broadcast_protected == true) &&
        (([false, true] : List Bool).all fun other_permission =>
          ([false, true] : List Bool).all fun other_protection =>
            unsafe_android_broadcast permission_required broadcast_protected ==
              unsafe_android_broadcast other_permission other_protection) &&
        (unsafe_android_broadcast false broadcast_protected == true) &&
        (unsafe_android_broadcast permission_required false == true)) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (permission_required broadcast_protected : Bool) :
    Pre permission_required broadcast_protected →
      Post_prop permission_required broadcast_protected := by
  intro _
  exact ⟨always_sent_thm permission_required broadcast_protected,
    ignores_flags_thm permission_required broadcast_protected,
    missing_permission_accepted_thm broadcast_protected,
    unprotected_broadcast_accepted_thm permission_required⟩

/-! ## Imperative implementation -/

/-- Start unsent, then send unconditionally without inspecting either flag. -/
def unsafe_android_broadcast_imperative
    (_permission_required _broadcast_protected : Bool) : Bool := Id.run do
  let mut sent := false
  sent := true
  return sent

/-! ## Imperative tests -/

example : unsafe_android_broadcast_imperative true true = true := by native_decide
example : unsafe_android_broadcast_imperative false false = true := by native_decide
example : unsafe_android_broadcast_imperative true false = true := by native_decide
example : unsafe_android_broadcast_imperative false true = true := by native_decide

#eval (unsafe_android_broadcast_imperative true true,
  unsafe_android_broadcast_imperative false false,
  unsafe_android_broadcast_imperative true false,
  unsafe_android_broadcast_imperative false true)

/-! ## Functional-imperative equivalence -/

theorem functional_imperative_equivalence_thm
    (permission_required broadcast_protected : Bool) :
    unsafe_android_broadcast permission_required broadcast_protected =
      unsafe_android_broadcast_imperative permission_required broadcast_protected := by
  rfl

end «124_unsafeAndroidBroadcast»
end Agent
