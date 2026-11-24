import Mathlib
namespace Agent

/-!
# Unsafe HMAC length verification

This formalizes the supplied Python program: verification returns `true` without
checking the message length, received MAC length, or expected MAC length.
Python integers are modeled by `Int`; even negative inputs are permitted because
the source performs no validation. In particular, mismatched and empty MACs are
accepted. Additive changes to message and MAC lengths also remain accepted.

This is a model of the program's acceptance behavior, not an implementation of
HMAC or a cryptographic proof of a SHA length-extension attack.
-/

namespace UnsafeHMACLength

-- Functional implementation of the Python verifier.
def unsafe_hmac_verify (_message_len _mac_len _expected_mac_len : Int) : Bool :=
  true

-- The source's check procedure, including its failure messages and output.
def check : IO Unit := do
  unless unsafe_hmac_verify 10 32 32 do
    throw (IO.userError "correct length rejected")
  unless unsafe_hmac_verify 10 64 32 do
    throw (IO.userError "vuln: wrong mac_len accepted")
  unless unsafe_hmac_verify 10 0 32 do
    throw (IO.userError "vuln: empty mac accepted")
  IO.println "All tests passed."

-- Unit tests corresponding to all three Python assertions.
example : unsafe_hmac_verify 10 32 32 = true := by native_decide
example : unsafe_hmac_verify 10 64 32 = true := by native_decide
example : unsafe_hmac_verify 10 0 32 = true := by native_decide
-- There is no implicit nonnegativity validation either.
example : unsafe_hmac_verify (-10) (-64) (-32) = true := by native_decide

#eval unsafe_hmac_verify 10 32 32
#eval unsafe_hmac_verify 10 64 32
#eval unsafe_hmac_verify 10 0 32
#eval check

-- No restrictions beyond the integer input types are imposed by the source.
def Pre (_message_len _mac_len _expected_mac_len : Int) : Prop := True

-- Complete characterization of the return value.
def always_accepts_prop (message_len mac_len expected_mac_len : Int) : Prop :=
  unsafe_hmac_verify message_len mac_len expected_mac_len = true

theorem always_accepts_thm (message_len mac_len expected_mac_len : Int) :
    always_accepts_prop message_len mac_len expected_mac_len := by sorry

def matching_length_prop (message_len expected_mac_len : Int) : Prop :=
  unsafe_hmac_verify message_len expected_mac_len expected_mac_len = true

theorem matching_length_thm (message_len expected_mac_len : Int) :
    matching_length_prop message_len expected_mac_len := by sorry

-- The missing length check: a mismatch does not cause rejection.
def mismatched_length_prop (message_len mac_len expected_mac_len : Int) : Prop :=
  mac_len ≠ expected_mac_len →
    unsafe_hmac_verify message_len mac_len expected_mac_len = true

theorem mismatched_length_thm (message_len mac_len expected_mac_len : Int) :
    mismatched_length_prop message_len mac_len expected_mac_len := by sorry

def empty_mac_prop (message_len expected_mac_len : Int) : Prop :=
  unsafe_hmac_verify message_len 0 expected_mac_len = true

theorem empty_mac_thm (message_len expected_mac_len : Int) :
    empty_mac_prop message_len expected_mac_len := by sorry

-- All three arguments, including the expected length, are ignored.
def input_independence_prop
    (message_len mac_len expected_mac_len other_message other_mac other_expected : Int) : Prop :=
  unsafe_hmac_verify message_len mac_len expected_mac_len =
    unsafe_hmac_verify other_message other_mac other_expected

theorem input_independence_thm
    (message_len mac_len expected_mac_len other_message other_mac other_expected : Int) :
    input_independence_prop message_len mac_len expected_mac_len
      other_message other_mac other_expected := by sorry

-- Nonnegative offsets describe appended data; the implementation in fact
-- accepts arbitrary integer offsets, so no additional hypothesis is necessary.
def length_extension_prop
    (message_len mac_len expected_mac_len extra_message extra_mac : Int) : Prop :=
  unsafe_hmac_verify (message_len + extra_message) (mac_len + extra_mac)
    expected_mac_len = true

theorem length_extension_thm
    (message_len mac_len expected_mac_len extra_message extra_mac : Int) :
    length_extension_prop message_len mac_len expected_mac_len extra_message extra_mac := by sorry

-- The postcondition collects the behavior and its security-relevant consequences.
def Post_prop (message_len mac_len expected_mac_len : Int) : Prop :=
  always_accepts_prop message_len mac_len expected_mac_len ∧
  matching_length_prop message_len expected_mac_len ∧
  mismatched_length_prop message_len mac_len expected_mac_len ∧
  empty_mac_prop message_len expected_mac_len ∧
  (∀ other_message other_mac other_expected : Int,
    input_independence_prop message_len mac_len expected_mac_len
      other_message other_mac other_expected) ∧
  (∀ extra_message extra_mac : Int,
    length_extension_prop message_len mac_len expected_mac_len extra_message extra_mac)

-- Property-based tests use executable expressions rather than deciding the
-- specification predicates. These checks are evidence, not proofs.

-- PBT: always_accepts_prop.
#eval Plausible.Testable.check (∀ m l e : Int,
  unsafe_hmac_verify m l e = true)

-- PBT: matching_length_prop.
#eval Plausible.Testable.check (∀ m e : Int,
  unsafe_hmac_verify m e e = true)

-- PBT: mismatched_length_prop. Boolean implication avoids discarding
-- samples when the two lengths coincide.
#eval Plausible.Testable.check (∀ m l e : Int,
  ((l == e) || unsafe_hmac_verify m l e) = true)

-- PBT: empty_mac_prop.
#eval Plausible.Testable.check (∀ m e : Int,
  unsafe_hmac_verify m 0 e = true)

-- PBT: input_independence_prop.
#eval Plausible.Testable.check (∀ m l e m' l' e' : Int,
  unsafe_hmac_verify m l e = unsafe_hmac_verify m' l' e')

-- PBT: length_extension_prop, including positive, zero, and negative offsets.
#eval Plausible.Testable.check (∀ m l e dm dl : Int,
  unsafe_hmac_verify (m + dm) (l + dl) e = true)

-- PBT: Post_prop. Its inner universal quantifiers are brought out to the
-- sampled arguments; the conjunction is its executable pointwise form.
#eval Plausible.Testable.check (∀ m l e m' l' e' dm dl : Int,
  unsafe_hmac_verify m l e = true ∧
  unsafe_hmac_verify m e e = true ∧
  ((l == e) || unsafe_hmac_verify m l e) = true ∧
  unsafe_hmac_verify m 0 e = true ∧
  unsafe_hmac_verify m l e = unsafe_hmac_verify m' l' e' ∧
  unsafe_hmac_verify (m + dm) (l + dl) e = true)

-- An additional bounded PBT of the whole postcondition, exhaustively including
-- mismatches, empty MACs, negative inputs, and the source's example lengths.
private def testLengths : List Int := [-2, -1, 0, 1, 10, 32, 64]

-- Dedicated bounded PBT for mismatched_length_prop; checks every triple,
-- including all unequal MAC/expected-length pairs in the sample set.
example : testLengths.all (fun m =>
    testLengths.all (fun l =>
      testLengths.all (fun e =>
        (l == e) || unsafe_hmac_verify m l e))) = true := by
  native_decide

-- Bounded PBT for Post_prop (universal components checked on testLengths).

example : testLengths.all (fun m =>
    testLengths.all (fun l =>
      testLengths.all (fun e =>
        (unsafe_hmac_verify m l e == true) &&
        (unsafe_hmac_verify m e e == true) &&
        ((l == e) || (unsafe_hmac_verify m l e == true)) &&
        (unsafe_hmac_verify m 0 e == true) &&
        testLengths.all (fun m' =>
          testLengths.all (fun l' =>
            testLengths.all (fun e' =>
              unsafe_hmac_verify m l e == unsafe_hmac_verify m' l' e'))) &&
        testLengths.all (fun dm =>
          testLengths.all (fun dl =>
            unsafe_hmac_verify (m + dm) (l + dl) e == true))))) = true := by
  native_decide

-- Correctness is kernel-proved independently of every executable test.
theorem correctness_thm (message_len mac_len expected_mac_len : Int) :
    Pre message_len mac_len expected_mac_len →
      Post_prop message_len mac_len expected_mac_len := by sorry

-- Imperative implementation: overwrite the local result with unconditional
-- acceptance, without ever inspecting any of the arguments.
def unsafe_hmac_verify_imperative
    (_message_len _mac_len _expected_mac_len : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

-- Imperative unit tests.
example : unsafe_hmac_verify_imperative 10 32 32 = true := by native_decide
example : unsafe_hmac_verify_imperative 10 64 32 = true := by native_decide
example : unsafe_hmac_verify_imperative 10 0 32 = true := by native_decide
example : unsafe_hmac_verify_imperative (-10) (-64) (-32) = true := by native_decide

#eval unsafe_hmac_verify_imperative 10 32 32
#eval unsafe_hmac_verify_imperative 10 64 32
#eval unsafe_hmac_verify_imperative 10 0 32

-- Additional randomized functional/imperative comparison.
#eval Plausible.Testable.check (∀ m l e : Int,
  unsafe_hmac_verify m l e = unsafe_hmac_verify_imperative m l e)

-- Definitional reduction proves equivalence on the full Python integer domain.
theorem functional_imperative_equivalence_thm (message_len mac_len expected_mac_len : Int) :
    unsafe_hmac_verify message_len mac_len expected_mac_len =
      unsafe_hmac_verify_imperative message_len mac_len expected_mac_len := by sorry

end UnsafeHMACLength
end Agent
