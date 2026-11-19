import Mathlib
namespace Agent

/-!
# Unsafe TLS ChangeCipherSpec MAC

Translation of `unsafe_change_cipher_spec_mac` and its Python checks.
Python's arbitrary-precision signed integers are modeled by `Int`.  The toy
handshake MAC sums messages 1--5, 7, and 9, ignoring the ChangeCipherSpec (CCS)
messages 6 and 8.  Consequently arbitrary replacements of either CCS message,
including replacing both by zero to represent dropping them, preserve the MAC.
Changing any one covered input while keeping the others fixed changes the MAC.
This last statement is not a claim of collision resistance for the toy sum.

The file formalizes the computation, not a TLS state machine or encryption.
Randomized tests are evidence only; all named theorems have kernel-checked
proofs independent of those tests.
-/

namespace UnsafeChangeCipherSpec

/-! ## Functional implementation -/

/-- The CCS arguments are deliberately unused, matching the unsafe Python MAC. -/
def unsafe_change_cipher_spec_mac
    (messages_1_5 _message_6_ccs message_7 _message_8_ccs message_9 : Int) : Int :=
  messages_1_5 + message_7 + message_9

/-- Boolean translation of the six assertions in Python's `check`. -/
def check (candidate : Int → Int → Int → Int → Int → Int) : Bool :=
  (candidate 15 6 7 8 9 == 15 + 7 + 9) &&
  (candidate 15 6 7 8 9 == candidate 15 999 7 8 9) &&
  (candidate 15 6 7 8 9 == candidate 15 6 7 999 9) &&
  (candidate 15 6 7 8 9 == candidate 15 0 7 0 9) &&
  (candidate 15 6 7 8 9 != candidate 99 6 7 8 9) &&
  (candidate 15 6 7 8 9 != candidate 15 6 99 8 9)

/-! ## Unit tests -/

example : unsafe_change_cipher_spec_mac 15 6 7 8 9 = 15 + 7 + 9 := by
  native_decide

example : unsafe_change_cipher_spec_mac 15 6 7 8 9 =
    unsafe_change_cipher_spec_mac 15 999 7 8 9 := by
  native_decide

example : unsafe_change_cipher_spec_mac 15 6 7 8 9 =
    unsafe_change_cipher_spec_mac 15 6 7 999 9 := by
  native_decide

example : unsafe_change_cipher_spec_mac 15 6 7 8 9 =
    unsafe_change_cipher_spec_mac 15 0 7 0 9 := by
  native_decide

example : unsafe_change_cipher_spec_mac 15 6 7 8 9 ≠
    unsafe_change_cipher_spec_mac 99 6 7 8 9 := by
  native_decide

example : unsafe_change_cipher_spec_mac 15 6 7 8 9 ≠
    unsafe_change_cipher_spec_mac 15 6 99 8 9 := by
  native_decide

example : check unsafe_change_cipher_spec_mac = true := by native_decide
example : unsafe_change_cipher_spec_mac (-15) (-6) 7 (-8) 9 = 1 := by native_decide
example : unsafe_change_cipher_spec_mac 0 999 0 (-999) 0 = 0 := by native_decide
example : unsafe_change_cipher_spec_mac 15 6 7 8 9 ≠
    unsafe_change_cipher_spec_mac 15 6 7 8 99 := by native_decide

#eval unsafe_change_cipher_spec_mac 15 6 7 8 9
#eval check unsafe_change_cipher_spec_mac
#eval if check unsafe_change_cipher_spec_mac then "All tests passed."
      else "Candidate failed tests"

/-! ## Precondition -/

/-- Every tuple of Python integers is admissible; there are no extra assumptions. -/
def Pre (_messages_1_5 _message_6_ccs _message_7 _message_8_ccs _message_9 : Int) : Prop :=
  True

/-! ## Properties and proofs -/

/-- Exact formula, with no contribution from messages 6 or 8. -/
def mac_formula_prop (a c6 b c8 c : Int) : Prop :=
  unsafe_change_cipher_spec_mac a c6 b c8 c = a + b + c

theorem mac_formula_thm (a c6 b c8 c : Int) : mac_formula_prop a c6 b c8 c := by
  rfl

/-- An arbitrary replacement of message 6 is invisible to the MAC. -/
def message6_omission_prop (a c6 b c8 c new6 : Int) : Prop :=
  unsafe_change_cipher_spec_mac a c6 b c8 c =
    unsafe_change_cipher_spec_mac a new6 b c8 c

theorem message6_omission_thm (a c6 b c8 c new6 : Int) :
    message6_omission_prop a c6 b c8 c new6 := by
  rfl

/-- An arbitrary replacement of message 8 is invisible to the MAC. -/
def message8_omission_prop (a c6 b c8 c new8 : Int) : Prop :=
  unsafe_change_cipher_spec_mac a c6 b c8 c =
    unsafe_change_cipher_spec_mac a c6 b new8 c

theorem message8_omission_thm (a c6 b c8 c new8 : Int) :
    message8_omission_prop a c6 b c8 c new8 := by
  rfl

/-- Both CCS inputs may be replaced simultaneously, with no MAC change. -/
def both_ccs_omission_prop (a c6 b c8 c new6 new8 : Int) : Prop :=
  unsafe_change_cipher_spec_mac a c6 b c8 c =
    unsafe_change_cipher_spec_mac a new6 b new8 c

theorem both_ccs_omission_thm (a c6 b c8 c new6 new8 : Int) :
    both_ccs_omission_prop a c6 b c8 c new6 new8 := by
  rfl

/-- Dropping both CCS inputs is represented, as in Python's check, by zeros. -/
def ccs_drop_prop (a c6 b c8 c : Int) : Prop :=
  unsafe_change_cipher_spec_mac a c6 b c8 c =
    unsafe_change_cipher_spec_mac a 0 b 0 c

theorem ccs_drop_thm (a c6 b c8 c : Int) : ccs_drop_prop a c6 b c8 c := by
  exact both_ccs_omission_thm a c6 b c8 c 0 0

/-- Changing the aggregate of messages 1--5 alone changes the MAC. -/
def messages1_5_coverage_prop (a c6 b c8 c newA : Int) : Prop :=
  a ≠ newA → unsafe_change_cipher_spec_mac a c6 b c8 c ≠
    unsafe_change_cipher_spec_mac newA c6 b c8 c

theorem messages1_5_coverage_thm (a c6 b c8 c newA : Int) :
    messages1_5_coverage_prop a c6 b c8 c newA := by
  unfold messages1_5_coverage_prop unsafe_change_cipher_spec_mac
  omega

/-- Changing message 7 alone changes the MAC. -/
def message7_coverage_prop (a c6 b c8 c newB : Int) : Prop :=
  b ≠ newB → unsafe_change_cipher_spec_mac a c6 b c8 c ≠
    unsafe_change_cipher_spec_mac a c6 newB c8 c

theorem message7_coverage_thm (a c6 b c8 c newB : Int) :
    message7_coverage_prop a c6 b c8 c newB := by
  unfold message7_coverage_prop unsafe_change_cipher_spec_mac
  omega

/-- Message 9 is also covered, with the other inputs held fixed. -/
def message9_coverage_prop (a c6 b c8 c newC : Int) : Prop :=
  c ≠ newC → unsafe_change_cipher_spec_mac a c6 b c8 c ≠
    unsafe_change_cipher_spec_mac a c6 b c8 newC

theorem message9_coverage_thm (a c6 b c8 c newC : Int) :
    message9_coverage_prop a c6 b c8 c newC := by
  unfold message9_coverage_prop unsafe_change_cipher_spec_mac
  omega

/-! ## Postcondition -/

/-- The exact computation, CCS vulnerability, and coverage of all other inputs. -/
def Post_prop (a c6 b c8 c : Int) : Prop :=
  mac_formula_prop a c6 b c8 c ∧
  (∀ new6 : Int, message6_omission_prop a c6 b c8 c new6) ∧
  (∀ new8 : Int, message8_omission_prop a c6 b c8 c new8) ∧
  (∀ new6 new8 : Int, both_ccs_omission_prop a c6 b c8 c new6 new8) ∧
  ccs_drop_prop a c6 b c8 c ∧
  (∀ newA : Int, messages1_5_coverage_prop a c6 b c8 c newA) ∧
  (∀ newB : Int, message7_coverage_prop a c6 b c8 c newB) ∧
  (∀ newC : Int, message9_coverage_prop a c6 b c8 c newC)

/-! ## Property-based tests

Each test below expands its named property to executable integer comparisons.
The precondition is `True`, so all signed integer samples are admissible.
The postcondition test samples the replacement inputs as well as the original
inputs; its conjunction checks all eight clauses of `Post_prop` together.
-/

-- PBT: mac_formula_prop
#eval Plausible.Testable.check (∀ a c6 b c8 c : Int,
  unsafe_change_cipher_spec_mac a c6 b c8 c = a + b + c)

-- PBT: message6_omission_prop
#eval Plausible.Testable.check (∀ a c6 b c8 c new6 : Int,
  unsafe_change_cipher_spec_mac a c6 b c8 c =
    unsafe_change_cipher_spec_mac a new6 b c8 c)

-- PBT: message8_omission_prop
#eval Plausible.Testable.check (∀ a c6 b c8 c new8 : Int,
  unsafe_change_cipher_spec_mac a c6 b c8 c =
    unsafe_change_cipher_spec_mac a c6 b new8 c)

-- PBT: both_ccs_omission_prop
#eval Plausible.Testable.check (∀ a c6 b c8 c new6 new8 : Int,
  unsafe_change_cipher_spec_mac a c6 b c8 c =
    unsafe_change_cipher_spec_mac a new6 b new8 c)

-- PBT: ccs_drop_prop
#eval Plausible.Testable.check (∀ a c6 b c8 c : Int,
  unsafe_change_cipher_spec_mac a c6 b c8 c =
    unsafe_change_cipher_spec_mac a 0 b 0 c)

-- PBT: messages1_5_coverage_prop.  Material implication is evaluated as
-- "same input OR different output", so equal inputs are not discarded.
#eval Plausible.Testable.check (∀ a c6 b c8 c newA : Int,
  ((a == newA) || (unsafe_change_cipher_spec_mac a c6 b c8 c !=
    unsafe_change_cipher_spec_mac newA c6 b c8 c)) = true)

-- PBT: message7_coverage_prop
#eval Plausible.Testable.check (∀ a c6 b c8 c newB : Int,
  ((b == newB) || (unsafe_change_cipher_spec_mac a c6 b c8 c !=
    unsafe_change_cipher_spec_mac a c6 newB c8 c)) = true)

-- PBT: message9_coverage_prop
#eval Plausible.Testable.check (∀ a c6 b c8 c newC : Int,
  ((c == newC) || (unsafe_change_cipher_spec_mac a c6 b c8 c !=
    unsafe_change_cipher_spec_mac a c6 b c8 newC)) = true)

/-- Signed small values for exhaustive tests, including zero and negatives. -/
def smallInts : List Int := [-2, -1, 0, 1, 2]

-- Bounded PBT: messages1_5_coverage_prop, all 5^6 input tuples.
-- These exhaustive tests ensure that unequal-input cases are exercised.
example : (smallInts.all fun a =>
    smallInts.all fun c6 =>
    smallInts.all fun b =>
    smallInts.all fun c8 =>
    smallInts.all fun c =>
    smallInts.all fun newA =>
      (a == newA) || (unsafe_change_cipher_spec_mac a c6 b c8 c !=
        unsafe_change_cipher_spec_mac newA c6 b c8 c)) = true := by
  native_decide

-- Bounded PBT: message7_coverage_prop, all 5^6 input tuples.
example : (smallInts.all fun a =>
    smallInts.all fun c6 =>
    smallInts.all fun b =>
    smallInts.all fun c8 =>
    smallInts.all fun c =>
    smallInts.all fun newB =>
      (b == newB) || (unsafe_change_cipher_spec_mac a c6 b c8 c !=
        unsafe_change_cipher_spec_mac a c6 newB c8 c)) = true := by
  native_decide

-- Bounded PBT: message9_coverage_prop, all 5^6 input tuples.
example : (smallInts.all fun a =>
    smallInts.all fun c6 =>
    smallInts.all fun b =>
    smallInts.all fun c8 =>
    smallInts.all fun c =>
    smallInts.all fun newC =>
      (c == newC) || (unsafe_change_cipher_spec_mac a c6 b c8 c !=
        unsafe_change_cipher_spec_mac a c6 b c8 newC)) = true := by
  native_decide

-- PBT: Post_prop. All universally quantified replacements are sampled
-- explicitly. Boolean conjunction and material implication make the entire
-- check executable without a Decidable instance for Post_prop itself.
#eval Plausible.Testable.check (∀ a c6 b c8 c new6 new8 newA newB newC : Int,
  ((unsafe_change_cipher_spec_mac a c6 b c8 c == a + b + c) &&
  (unsafe_change_cipher_spec_mac a c6 b c8 c ==
    unsafe_change_cipher_spec_mac a new6 b c8 c) &&
  (unsafe_change_cipher_spec_mac a c6 b c8 c ==
    unsafe_change_cipher_spec_mac a c6 b new8 c) &&
  (unsafe_change_cipher_spec_mac a c6 b c8 c ==
    unsafe_change_cipher_spec_mac a new6 b new8 c) &&
  (unsafe_change_cipher_spec_mac a c6 b c8 c ==
    unsafe_change_cipher_spec_mac a 0 b 0 c) &&
  ((a == newA) || (unsafe_change_cipher_spec_mac a c6 b c8 c !=
    unsafe_change_cipher_spec_mac newA c6 b c8 c)) &&
  ((b == newB) || (unsafe_change_cipher_spec_mac a c6 b c8 c !=
    unsafe_change_cipher_spec_mac a c6 newB c8 c)) &&
  ((c == newC) || (unsafe_change_cipher_spec_mac a c6 b c8 c !=
    unsafe_change_cipher_spec_mac a c6 b c8 newC))) = true)

/-! ## Correctness -/

theorem correctness_thm (a c6 b c8 c : Int) :
    Pre a c6 b c8 c → Post_prop a c6 b c8 c := by
  intro _
  exact ⟨mac_formula_thm a c6 b c8 c,
    fun new6 => message6_omission_thm a c6 b c8 c new6,
    fun new8 => message8_omission_thm a c6 b c8 c new8,
    fun new6 new8 => both_ccs_omission_thm a c6 b c8 c new6 new8,
    ccs_drop_thm a c6 b c8 c,
    fun newA => messages1_5_coverage_thm a c6 b c8 c newA,
    fun newB => message7_coverage_thm a c6 b c8 c newB,
    fun newC => message9_coverage_thm a c6 b c8 c newC⟩

/-! ## Imperative implementation -/

/-- Accumulate only the covered messages in mutable state. -/
def unsafe_change_cipher_spec_mac_imperative
    (messages_1_5 _message_6_ccs message_7 _message_8_ccs message_9 : Int) : Int :=
  Id.run do
    let mut mac := messages_1_5
    mac := mac + message_7
    mac := mac + message_9
    return mac

/-! ## Imperative tests -/

-- Run all six original Python assertions against the imperative implementation.
example : check unsafe_change_cipher_spec_mac_imperative = true := by native_decide
example : unsafe_change_cipher_spec_mac_imperative 15 6 7 8 9 = 31 := by native_decide
example : unsafe_change_cipher_spec_mac_imperative (-15) (-6) 7 (-8) 9 = 1 := by
  native_decide
example : unsafe_change_cipher_spec_mac_imperative 0 999 0 (-999) 0 = 0 := by
  native_decide

#eval unsafe_change_cipher_spec_mac_imperative 15 6 7 8 9
#eval check unsafe_change_cipher_spec_mac_imperative

-- Additional PBT: the two implementations agree on arbitrary signed integers.
#eval Plausible.Testable.check (∀ a c6 b c8 c : Int,
  unsafe_change_cipher_spec_mac a c6 b c8 c =
    unsafe_change_cipher_spec_mac_imperative a c6 b c8 c)

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (a c6 b c8 c : Int) :
    unsafe_change_cipher_spec_mac a c6 b c8 c =
      unsafe_change_cipher_spec_mac_imperative a c6 b c8 c := by
  rfl

end UnsafeChangeCipherSpec
end Agent
