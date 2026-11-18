import Mathlib
namespace Agent

/-!
# Safe signature permission grants

Formalization of the Python `safeSigPermGrant` function: a requesting app is
allowed a signature-protected permission exactly when its certificate equals
the permission owner's certificate (MIT 6.858, Lecture 10: Android Security).

Certificates are modelled by `Int`, preserving Python's arbitrary-precision,
signed integer domain. There are no restrictions on admissible certificates.
The file includes the four source tests, executable bounded property tests,
and a mutable-state implementation proved equivalent to the functional one.
-/

namespace UnsafeSigPermSafe

/-- Grant a signature-protected permission exactly on a certificate match. -/
def safeSigPermGrant (appCert ownerCert : Int) : Bool :=
  decide (appCert = ownerCert)

-- The four unit tests from Python.
example : safeSigPermGrant 1 1 = true := by native_decide
example : safeSigPermGrant 1 2 = false := by native_decide
example : safeSigPermGrant 0 999 = false := by native_decide
example : safeSigPermGrant 42 42 = true := by native_decide

#eval safeSigPermGrant 1 1
#eval safeSigPermGrant 1 2
#eval safeSigPermGrant 0 999
#eval safeSigPermGrant 42 42

-- Signed certificates are also part of the source input domain.
example : safeSigPermGrant (-42) (-42) = true := by native_decide
example : safeSigPermGrant (-42) 42 = false := by native_decide

/-- All pairs of integer certificates are admissible. -/
def Pre (_appCert _ownerCert : Int) : Prop := True

/-- Matching certificates must be granted permission (completeness). -/
def same_cert_granted_prop (appCert ownerCert : Int) : Prop :=
  appCert = ownerCert → safeSigPermGrant appCert ownerCert = true

theorem same_cert_granted_thm (appCert ownerCert : Int) :
    same_cert_granted_prop appCert ownerCert := by
  intro h
  simp [safeSigPermGrant, h]

/-- Distinct certificates must be denied permission. -/
def different_cert_denied_prop (appCert ownerCert : Int) : Prop :=
  appCert ≠ ownerCert → safeSigPermGrant appCert ownerCert = false

theorem different_cert_denied_thm (appCert ownerCert : Int) :
    different_cert_denied_prop appCert ownerCert := by
  intro h
  simp [safeSigPermGrant, h]

/-- Exact authorization, including the safety direction: only a match grants. -/
def grant_iff_same_cert_prop (appCert ownerCert : Int) : Prop :=
  safeSigPermGrant appCert ownerCert = true ↔ appCert = ownerCert

theorem grant_iff_same_cert_thm (appCert ownerCert : Int) :
    grant_iff_same_cert_prop appCert ownerCert := by
  simp [grant_iff_same_cert_prop, safeSigPermGrant]

/-- The full contract combines positive, negative, and exact authorization. -/
def Post_prop (appCert ownerCert : Int) : Prop :=
  same_cert_granted_prop appCert ownerCert ∧
  different_cert_denied_prop appCert ownerCert ∧
  grant_iff_same_cert_prop appCert ownerCert

/-!
## Property-based tests

Each check exhausts all 961 pairs of certificates in [-15, 15], including
matching certificates, distinct certificates, zero, and negative values.
The tests use executable forms of the properties, not a decidability axiom
for the specification predicates. These tests are evidence only; the named
theorems above and below are ordinary kernel-checked proofs for all integers.
-/

def certificateSamples : List Int :=
  (List.range 31).map (fun n => (n : Int) - 15)

-- PBT for same_cert_granted_prop.
example : certificateSamples.all (fun appCert =>
    certificateSamples.all (fun ownerCert =>
      decide (appCert = ownerCert →
        safeSigPermGrant appCert ownerCert = true))) = true := by
  native_decide

-- PBT for different_cert_denied_prop.
example : certificateSamples.all (fun appCert =>
    certificateSamples.all (fun ownerCert =>
      decide (appCert ≠ ownerCert →
        safeSigPermGrant appCert ownerCert = false))) = true := by
  native_decide

-- PBT for grant_iff_same_cert_prop.
example : certificateSamples.all (fun appCert =>
    certificateSamples.all (fun ownerCert =>
      decide (safeSigPermGrant appCert ownerCert = true ↔
        appCert = ownerCert))) = true := by
  native_decide

-- PBT for Post_prop: test its entire executable conjunction.
example : certificateSamples.all (fun appCert =>
    certificateSamples.all (fun ownerCert =>
      decide ((appCert = ownerCert →
          safeSigPermGrant appCert ownerCert = true) ∧
        (appCert ≠ ownerCert →
          safeSigPermGrant appCert ownerCert = false) ∧
        (safeSigPermGrant appCert ownerCert = true ↔
          appCert = ownerCert)))) = true := by
  native_decide

/-- For every admissible input, the complete authorization contract holds. -/
theorem correctness_thm (appCert ownerCert : Int) :
    Pre appCert ownerCert → Post_prop appCert ownerCert := by
  intro _
  exact ⟨same_cert_granted_thm appCert ownerCert,
    different_cert_denied_thm appCert ownerCert,
    grant_iff_same_cert_thm appCert ownerCert⟩

/-- Imperative version: default to denial, then grant only on a match. -/
def safeSigPermGrantImperative (appCert ownerCert : Int) : Bool := Id.run do
  let mut granted := false
  if appCert = ownerCert then
    granted := true
  return granted

-- Imperative unit tests, including the four source cases.
example : safeSigPermGrantImperative 1 1 = true := by native_decide
example : safeSigPermGrantImperative 1 2 = false := by native_decide
example : safeSigPermGrantImperative 0 999 = false := by native_decide
example : safeSigPermGrantImperative 42 42 = true := by native_decide
example : safeSigPermGrantImperative (-42) (-42) = true := by native_decide
example : safeSigPermGrantImperative (-42) 42 = false := by native_decide

#eval safeSigPermGrantImperative 1 1
#eval safeSigPermGrantImperative 1 2
#eval safeSigPermGrantImperative 0 999
#eval safeSigPermGrantImperative 42 42

-- Additional bounded check of functional/imperative agreement.
example : certificateSamples.all (fun appCert =>
    certificateSamples.all (fun ownerCert =>
      safeSigPermGrant appCert ownerCert ==
        safeSigPermGrantImperative appCert ownerCert)) = true := by
  native_decide

/-- Functional and imperative implementations agree on the full input domain. -/
theorem functional_eq_imperative_thm (appCert ownerCert : Int) :
    safeSigPermGrant appCert ownerCert =
      safeSigPermGrantImperative appCert ownerCert := by
  by_cases h : appCert = ownerCert <;>
    simp [safeSigPermGrant, safeSigPermGrantImperative, h]

end UnsafeSigPermSafe
end Agent
