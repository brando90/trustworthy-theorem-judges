import Mathlib
namespace Agent

/-!
# Unsafe CA certificate verification

A translation of the Python `unsafe_ca_verify` and its checks. Python's
unbounded signed integers are modeled by `Int`. In the simplified signing
model a valid signature equals `ca_pub_key + cert_data`, but this verifier
never performs that check: every certificate is accepted, including forged
and self-signed certificates. The properties describe this vulnerability,
not the security contract of a safe verifier.
-/

namespace UnsafeCAVerify94

/-- Faithful translation: none of the three inputs is inspected. -/
def unsafe_ca_verify (_cert_sig _ca_pub_key _cert_data : Int) : Bool :=
  true

/-- The three assertions and success message from the Python test runner. -/
def check : IO Unit := do
  unless unsafe_ca_verify 15 10 5 do
    throw (IO.userError "normal case failed")
  unless unsafe_ca_verify 0 10 5 do
    throw (IO.userError "vuln: forged sig accepted")
  unless unsafe_ca_verify 999 10 5 do
    throw (IO.userError "vuln: any sig accepted")
  IO.println "All tests passed."

-- Original unit tests.
example : unsafe_ca_verify 15 10 5 = true := by native_decide
example : unsafe_ca_verify 0 10 5 = true := by native_decide
example : unsafe_ca_verify 999 10 5 = true := by native_decide
-- Signed inputs are also admissible Python integers.
example : unsafe_ca_verify (-999) (-10) (-5) = true := by native_decide
#eval unsafe_ca_verify 15 10 5
#eval unsafe_ca_verify 0 10 5
#eval unsafe_ca_verify 999 10 5
#eval check

/-- There is no restriction on signatures, keys, or certificate data. -/
def Pre (_cert_sig _ca_pub_key _cert_data : Int) : Prop := True

/-- The result is always acceptance. -/
def always_accepts_prop (cert_sig ca_pub_key cert_data : Int) : Prop :=
  unsafe_ca_verify cert_sig ca_pub_key cert_data = true

theorem always_accepts_thm (cert_sig ca_pub_key cert_data : Int) :
    always_accepts_prop cert_sig ca_pub_key cert_data := by
  rfl

/-- Correctly signed certificates are accepted in the simplified model. -/
def valid_signature_accepted_prop (cert_sig ca_pub_key cert_data : Int) : Prop :=
  cert_sig = ca_pub_key + cert_data →
    unsafe_ca_verify cert_sig ca_pub_key cert_data = true

theorem valid_signature_accepted_thm (cert_sig ca_pub_key cert_data : Int) :
    valid_signature_accepted_prop cert_sig ca_pub_key cert_data := by
  intro _
  rfl

/-- The vulnerability: every invalid signature is accepted too. -/
def forged_signature_accepted_prop (cert_sig ca_pub_key cert_data : Int) : Prop :=
  cert_sig ≠ ca_pub_key + cert_data →
    unsafe_ca_verify cert_sig ca_pub_key cert_data = true

theorem forged_signature_accepted_thm (cert_sig ca_pub_key cert_data : Int) :
    forged_signature_accepted_prop cert_sig ca_pub_key cert_data := by
  intro _
  rfl

/-- Changing any or all inputs cannot change the verification result. -/
def ignores_inputs_prop (cert_sig ca_pub_key cert_data : Int) : Prop :=
  ∀ other_sig other_key other_data : Int,
    unsafe_ca_verify cert_sig ca_pub_key cert_data =
      unsafe_ca_verify other_sig other_key other_data

theorem ignores_inputs_thm (cert_sig ca_pub_key cert_data : Int) :
    ignores_inputs_prop cert_sig ca_pub_key cert_data := by
  intro other_sig other_key other_data
  rfl

/-- The complete behavior of the unsafe verifier, including its vulnerability. -/
def Post_prop (cert_sig ca_pub_key cert_data : Int) : Prop :=
  always_accepts_prop cert_sig ca_pub_key cert_data ∧
  valid_signature_accepted_prop cert_sig ca_pub_key cert_data ∧
  forged_signature_accepted_prop cert_sig ca_pub_key cert_data ∧
  ignores_inputs_prop cert_sig ca_pub_key cert_data

-- Property-based tests. These are executable checks, not theorem proofs.
-- PBT for always_accepts_prop, with arbitrary signed integer arguments.
#eval Plausible.Testable.check
  (∀ cert_sig ca_pub_key cert_data : Int,
    unsafe_ca_verify cert_sig ca_pub_key cert_data = true)

-- PBT for valid_signature_accepted_prop: construct valid signatures so that
-- every generated case exercises the premise rather than discarding samples.
#eval Plausible.Testable.check
  (∀ ca_pub_key cert_data : Int,
    unsafe_ca_verify (ca_pub_key + cert_data) ca_pub_key cert_data = true)

-- PBT for forged_signature_accepted_prop. Boolean implication avoids
-- discarded samples when a generated signature happens to be valid.
#eval Plausible.Testable.check
  (∀ cert_sig ca_pub_key cert_data : Int,
    ((cert_sig == ca_pub_key + cert_data) ||
      unsafe_ca_verify cert_sig ca_pub_key cert_data) = true)

-- PBT for ignores_inputs_prop: all six inputs are generated independently.
#eval Plausible.Testable.check
  (∀ cert_sig ca_pub_key cert_data other_sig other_key other_data : Int,
    unsafe_ca_verify cert_sig ca_pub_key cert_data =
      unsafe_ca_verify other_sig other_key other_data)

-- PBT for Post_prop: the executable conjunction, with independent samples
-- for the universally quantified comparison inputs in ignores_inputs_prop.
#eval Plausible.Testable.check
  (∀ cert_sig ca_pub_key cert_data other_sig other_key other_data : Int,
    (unsafe_ca_verify cert_sig ca_pub_key cert_data &&
      (!(cert_sig == ca_pub_key + cert_data) ||
        unsafe_ca_verify cert_sig ca_pub_key cert_data) &&
      ((cert_sig == ca_pub_key + cert_data) ||
        unsafe_ca_verify cert_sig ca_pub_key cert_data) &&
      (unsafe_ca_verify cert_sig ca_pub_key cert_data ==
        unsafe_ca_verify other_sig other_key other_data)) = true)

/-- A bounded signed sample including the original examples and negative inputs. -/
def testInputs : List Int := [-999, -15, -10, -5, -1, 0, 1, 5, 10, 15, 999]

-- Exhaustive bounded PBT for the valid-signature implication itself.
example : (testInputs.all fun cert_sig =>
    testInputs.all fun ca_pub_key =>
      testInputs.all fun cert_data =>
        (!(cert_sig == ca_pub_key + cert_data) ||
          unsafe_ca_verify cert_sig ca_pub_key cert_data)) = true := by
  native_decide

-- Exhaustive bounded PBT for invalid signatures, including negative values.
example : (testInputs.all fun cert_sig =>
    testInputs.all fun ca_pub_key =>
      testInputs.all fun cert_data =>
        ((cert_sig == ca_pub_key + cert_data) ||
          unsafe_ca_verify cert_sig ca_pub_key cert_data)) = true := by
  native_decide

/-- Every admissible call satisfies the post-condition; this is not a claim
that the verifier securely authenticates certificates. -/
theorem correctness_thm (cert_sig ca_pub_key cert_data : Int) :
    Pre cert_sig ca_pub_key cert_data → Post_prop cert_sig ca_pub_key cert_data := by
  intro _
  exact ⟨always_accepts_thm cert_sig ca_pub_key cert_data,
    valid_signature_accepted_thm cert_sig ca_pub_key cert_data,
    forged_signature_accepted_thm cert_sig ca_pub_key cert_data,
    ignores_inputs_thm cert_sig ca_pub_key cert_data⟩

/-- Imperative counterpart with mutable state and the same unconditional result. -/
def unsafe_ca_verify_imperative (_cert_sig _ca_pub_key _cert_data : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

-- Imperative unit tests.
example : unsafe_ca_verify_imperative 15 10 5 = true := by native_decide
example : unsafe_ca_verify_imperative 0 10 5 = true := by native_decide
example : unsafe_ca_verify_imperative 999 10 5 = true := by native_decide
example : unsafe_ca_verify_imperative (-999) (-10) (-5) = true := by native_decide
#eval unsafe_ca_verify_imperative 15 10 5
#eval unsafe_ca_verify_imperative 0 10 5
#eval unsafe_ca_verify_imperative 999 10 5

/-- Kernel-checked equivalence for all Python-integer inputs. -/
theorem functional_imperative_equivalence_thm (cert_sig ca_pub_key cert_data : Int) :
    unsafe_ca_verify cert_sig ca_pub_key cert_data =
      unsafe_ca_verify_imperative cert_sig ca_pub_key cert_data := by
  rfl

end UnsafeCAVerify94
end Agent
