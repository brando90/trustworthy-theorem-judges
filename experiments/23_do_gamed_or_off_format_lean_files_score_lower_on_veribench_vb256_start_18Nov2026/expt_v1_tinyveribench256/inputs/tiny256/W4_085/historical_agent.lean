import Mathlib
namespace Agent

/-!
# Safe CA certificate verification

Translation of the Python `safe_ca_verify` and its checks. Python integers are
modeled by unbounded Lean `Int`s. A certificate is accepted exactly when its
signature equals the CA public key plus the certificate data. This is the
source's simplified additive signing model, not a cryptographic unforgeability
claim. There are no restrictions on the signs or magnitudes of the inputs.

The file includes executable tests, specifications and kernel-checked proofs,
and an equivalent implementation using mutable state.
-/

namespace SafeCAVerify

/-! ## Functional implementation -/

def safe_ca_verify (cert_sig ca_pub_key cert_data : Int) : Bool :=
  decide (cert_sig = ca_pub_key + cert_data)

/-! ## Unit tests and the source's check routine -/

example : safe_ca_verify 15 10 5 = true := by native_decide
example : safe_ca_verify 0 10 5 = false := by native_decide
example : safe_ca_verify 999 10 5 = false := by native_decide
example : safe_ca_verify (-3) (-10) 7 = true := by native_decide
example : safe_ca_verify 3 (-10) 7 = false := by native_decide
example : safe_ca_verify 0 0 0 = true := by native_decide

#eval safe_ca_verify 15 10 5
#eval safe_ca_verify 0 10 5
#eval safe_ca_verify 999 10 5

def check : IO Unit := do
  assert! (safe_ca_verify 15 10 5 == true)
  assert! (safe_ca_verify 0 10 5 == false)
  assert! (safe_ca_verify 999 10 5 == false)
  IO.println "All tests passed."

#eval check

/-! ## Preconditions and properties -/

/-- Every triple of Python integers is admissible. -/
def Pre (_cert_sig _ca_pub_key _cert_data : Int) : Prop := True

/-- Acceptance is exactly equality with the additive signature. -/
def exact_verification_prop (cert_sig ca_pub_key cert_data : Int) : Prop :=
  safe_ca_verify cert_sig ca_pub_key cert_data = true ↔
    cert_sig = ca_pub_key + cert_data

theorem exact_verification_thm (cert_sig ca_pub_key cert_data : Int) :
    exact_verification_prop cert_sig ca_pub_key cert_data := by
  simp [exact_verification_prop, safe_ca_verify]

/-- A signature constructed according to the model is always accepted. -/
def valid_signature_prop (ca_pub_key cert_data : Int) : Prop :=
  safe_ca_verify (ca_pub_key + cert_data) ca_pub_key cert_data = true

theorem valid_signature_thm (ca_pub_key cert_data : Int) :
    valid_signature_prop ca_pub_key cert_data := by
  simp [valid_signature_prop, safe_ca_verify]

/-- Every signature different from the expected one is rejected. -/
def forged_signature_prop (cert_sig ca_pub_key cert_data : Int) : Prop :=
  cert_sig ≠ ca_pub_key + cert_data →
    safe_ca_verify cert_sig ca_pub_key cert_data = false

theorem forged_signature_thm (cert_sig ca_pub_key cert_data : Int) :
    forged_signature_prop cert_sig ca_pub_key cert_data := by
  intro h
  simp [safe_ca_verify, h]

/-! ## Postcondition -/

def Post_prop (cert_sig ca_pub_key cert_data : Int) : Prop :=
  exact_verification_prop cert_sig ca_pub_key cert_data ∧
  valid_signature_prop ca_pub_key cert_data ∧
  forged_signature_prop cert_sig ca_pub_key cert_data

/-! ## Property-based tests

These bounded tests exhaustively check all triples from [-10, 10]. They use
executable Boolean forms rather than assuming decidability of the named Prop
definitions. The valid-signature test also constructs signatures outside the
sample interval. The tests are evidence only; none are used in the proofs.
-/

def pbtInputs : List Int :=
  (List.range 21).map (fun n => (n : Int) - 10)

-- PBT for exact_verification_prop.
example : pbtInputs.all (fun s => pbtInputs.all (fun k =>
    pbtInputs.all (fun d =>
      safe_ca_verify s k d == decide (s = k + d)))) = true := by
  native_decide

-- PBT for valid_signature_prop.
example : pbtInputs.all (fun k => pbtInputs.all (fun d =>
    safe_ca_verify (k + d) k d)) = true := by
  native_decide

-- PBT for forged_signature_prop: executable implication.
example : pbtInputs.all (fun s => pbtInputs.all (fun k =>
    pbtInputs.all (fun d =>
      decide (s = k + d) || !(safe_ca_verify s k d)))) = true := by
  native_decide

-- PBT for the complete Post_prop conjunction.
example : pbtInputs.all (fun s => pbtInputs.all (fun k =>
    pbtInputs.all (fun d =>
      (safe_ca_verify s k d == decide (s = k + d)) &&
      safe_ca_verify (k + d) k d &&
      (decide (s = k + d) || !(safe_ca_verify s k d))))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (cert_sig ca_pub_key cert_data : Int) :
    Pre cert_sig ca_pub_key cert_data →
      Post_prop cert_sig ca_pub_key cert_data := by
  intro _
  exact ⟨exact_verification_thm cert_sig ca_pub_key cert_data,
    valid_signature_thm ca_pub_key cert_data,
    forged_signature_thm cert_sig ca_pub_key cert_data⟩

/-! ## Imperative implementation -/

def safe_ca_verify_imp (cert_sig ca_pub_key cert_data : Int) : Bool := Id.run do
  let mut expected_sig := ca_pub_key
  expected_sig := expected_sig + cert_data
  let mut verified := false
  if cert_sig = expected_sig then
    verified := true
  return verified

/-! ## Imperative tests -/

example : safe_ca_verify_imp 15 10 5 = true := by native_decide
example : safe_ca_verify_imp 0 10 5 = false := by native_decide
example : safe_ca_verify_imp 999 10 5 = false := by native_decide
example : safe_ca_verify_imp (-3) (-10) 7 = true := by native_decide
example : safe_ca_verify_imp 3 (-10) 7 = false := by native_decide
example : safe_ca_verify_imp 0 0 0 = true := by native_decide

#eval safe_ca_verify_imp 15 10 5
#eval safe_ca_verify_imp 0 10 5
#eval safe_ca_verify_imp 999 10 5

/-! ## Functional / imperative equivalence -/

theorem functional_imperative_equivalence_thm
    (cert_sig ca_pub_key cert_data : Int) :
    safe_ca_verify cert_sig ca_pub_key cert_data =
      safe_ca_verify_imp cert_sig ca_pub_key cert_data := by
  by_cases h : cert_sig = ca_pub_key + cert_data <;>
    simp [safe_ca_verify, safe_ca_verify_imp, h]

end SafeCAVerify
end Agent
