import Mathlib
namespace Agent

/-!
# Unsafe certificate revocation check

A faithful translation of Python's `unsafe_cert_revoke`: the result is always
`true`. Python integers are modeled by `Int`, and the CRL is a `List Int`.
Neither argument is inspected. In particular, a revoked certificate is accepted;
this file specifies the vulnerability rather than repairing it.

The Python `check` assertions are reproduced below. General claims have
kernel-checked proofs; bounded executable tests provide additional evidence.
-/

namespace UnsafeCertRevoke

/-- The unsafe implementation deliberately does not consult the CRL. -/
def unsafe_cert_revoke (_cert_serial : Int) (_revocation_list : List Int) : Bool :=
  true

-- Unit tests: the first two intentionally reproduce the duplicate Python test.
example : unsafe_cert_revoke 5 [5, 10] = true := by native_decide
example : unsafe_cert_revoke 5 [5, 10] = true := by native_decide
example : unsafe_cert_revoke 99 [] = true := by native_decide
-- Python also permits negative serial numbers and duplicate CRL entries.
example : unsafe_cert_revoke (-5) [-5, -5, 0] = true := by native_decide

/-- Executable counterpart of the Python test harness. -/
def check : IO Unit := do
  unless unsafe_cert_revoke 5 [5, 10] do
    throw (IO.userError "normal case failed")
  unless unsafe_cert_revoke 5 [5, 10] do
    throw (IO.userError "vuln: revoked cert accepted")
  unless unsafe_cert_revoke 99 [] do
    throw (IO.userError "vuln: always accepted")
  IO.println "All tests passed."

#eval unsafe_cert_revoke 5 [5, 10]
#eval unsafe_cert_revoke 99 []
#eval check

/-- All integer serials and all finite CRLs are admissible, without restrictions. -/
def Pre (_cert_serial : Int) (_revocation_list : List Int) : Prop := True

/-- The complete return-value semantics: every certificate is accepted. -/
def always_accepts_prop (cert_serial : Int) (revocation_list : List Int) : Prop :=
  unsafe_cert_revoke cert_serial revocation_list = true

theorem always_accepts_thm (cert_serial : Int) (revocation_list : List Int) :
    always_accepts_prop cert_serial revocation_list := by
  rfl

/-- The security failure: membership in the CRL does not prevent acceptance. -/
def revoked_accepted_prop (cert_serial : Int) (revocation_list : List Int) : Prop :=
  cert_serial ∈ revocation_list → unsafe_cert_revoke cert_serial revocation_list = true

theorem revoked_accepted_thm (cert_serial : Int) (revocation_list : List Int) :
    revoked_accepted_prop cert_serial revocation_list := by
  intro _h_revoked
  rfl

/-- Certificates absent from the CRL are also accepted, including with an empty CRL. -/
def unrevoked_accepted_prop (cert_serial : Int) (revocation_list : List Int) : Prop :=
  cert_serial ∉ revocation_list → unsafe_cert_revoke cert_serial revocation_list = true

theorem unrevoked_accepted_thm (cert_serial : Int) (revocation_list : List Int) :
    unrevoked_accepted_prop cert_serial revocation_list := by
  intro _h_unrevoked
  rfl

/-- Replacing the entire CRL by any other list leaves the result unchanged. -/
def crl_ignored_prop (cert_serial : Int) (revocation_list : List Int) : Prop :=
  ∀ other_list : List Int,
    unsafe_cert_revoke cert_serial revocation_list = unsafe_cert_revoke cert_serial other_list

theorem crl_ignored_thm (cert_serial : Int) (revocation_list : List Int) :
    crl_ignored_prop cert_serial revocation_list := by
  intro _other_list
  rfl

/-- Replacing the certificate serial by any other integer leaves the result unchanged. -/
def serial_ignored_prop (cert_serial : Int) (revocation_list : List Int) : Prop :=
  ∀ other_serial : Int,
    unsafe_cert_revoke cert_serial revocation_list = unsafe_cert_revoke other_serial revocation_list

theorem serial_ignored_thm (cert_serial : Int) (revocation_list : List Int) :
    serial_ignored_prop cert_serial revocation_list := by
  intro _other_serial
  rfl

/-- The postcondition records acceptance, the vulnerability, and independence of both inputs. -/
def Post_prop (cert_serial : Int) (revocation_list : List Int) : Prop :=
  always_accepts_prop cert_serial revocation_list ∧
  revoked_accepted_prop cert_serial revocation_list ∧
  unrevoked_accepted_prop cert_serial revocation_list ∧
  crl_ignored_prop cert_serial revocation_list ∧
  serial_ignored_prop cert_serial revocation_list

/-!
## Bounded property-based tests

Enumerate every serial from -5 through 5 and every CRL of length at most two
on that alphabet. This includes empty lists, duplicates, different orders,
revoked certificates and unrevoked certificates. These bounds apply only to
sampling: all theorems above and below retain the full `Int` / `List Int` domain.
The executable forms use Boolean equality and `contains`; Boolean implication
is `!antecedent || consequent`. The universal comparisons in the independence
properties and postcondition range over the same exhaustive finite samples.
-/

private def serialSamples : List Int :=
  (List.range 11).map (fun n => (n : Int) - 5)

private def crlSamples : List (List Int) :=
  [[]] ++ serialSamples.map (fun x => [x]) ++
    serialSamples.flatMap (fun x => serialSamples.map (fun y => [x, y]))

-- PBT for always_accepts_prop.
example : (serialSamples.all (fun cert =>
    crlSamples.all (fun crl => unsafe_cert_revoke cert crl))) = true := by
  native_decide

-- PBT for revoked_accepted_prop: CRL membership implies acceptance.
example : (serialSamples.all (fun cert =>
    crlSamples.all (fun crl =>
      !crl.contains cert || unsafe_cert_revoke cert crl))) = true := by
  native_decide

-- PBT for unrevoked_accepted_prop: absence from the CRL implies acceptance.
example : (serialSamples.all (fun cert =>
    crlSamples.all (fun crl =>
      crl.contains cert || unsafe_cert_revoke cert crl))) = true := by
  native_decide

-- PBT for crl_ignored_prop, including all pairs of sampled CRLs.
example : (serialSamples.all (fun cert =>
    crlSamples.all (fun crl =>
      crlSamples.all (fun other =>
        unsafe_cert_revoke cert crl == unsafe_cert_revoke cert other)))) = true := by
  native_decide

-- PBT for serial_ignored_prop, including all pairs of sampled serials.
example : (serialSamples.all (fun cert =>
    crlSamples.all (fun crl =>
      serialSamples.all (fun other =>
        unsafe_cert_revoke cert crl == unsafe_cert_revoke other crl)))) = true := by
  native_decide

-- PBT for the complete Post_prop conjunction, not merely its first component.
example : (serialSamples.all (fun cert =>
    crlSamples.all (fun crl =>
      unsafe_cert_revoke cert crl &&
      (!crl.contains cert || unsafe_cert_revoke cert crl) &&
      (crl.contains cert || unsafe_cert_revoke cert crl) &&
      (crlSamples.all (fun other =>
        unsafe_cert_revoke cert crl == unsafe_cert_revoke cert other)) &&
      (serialSamples.all (fun other =>
        unsafe_cert_revoke cert crl == unsafe_cert_revoke other crl))))) = true := by
  native_decide

/-- Correctness relative to the unsafe behavior, not to a secure revocation policy. -/
theorem correctness_thm (cert_serial : Int) (revocation_list : List Int) :
    Pre cert_serial revocation_list → Post_prop cert_serial revocation_list := by
  intro _h_pre
  exact ⟨always_accepts_thm cert_serial revocation_list,
    revoked_accepted_thm cert_serial revocation_list,
    unrevoked_accepted_thm cert_serial revocation_list,
    crl_ignored_thm cert_serial revocation_list,
    serial_ignored_thm cert_serial revocation_list⟩

/-- Mutable-state translation: assign acceptance unconditionally and return it. -/
def unsafe_cert_revoke_imperative
    (_cert_serial : Int) (_revocation_list : List Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

-- Imperative unit tests.
example : unsafe_cert_revoke_imperative 5 [5, 10] = true := by native_decide
example : unsafe_cert_revoke_imperative 5 [5, 10] = true := by native_decide
example : unsafe_cert_revoke_imperative 99 [] = true := by native_decide
example : unsafe_cert_revoke_imperative (-5) [-5, -5, 0] = true := by native_decide

#eval unsafe_cert_revoke_imperative 5 [5, 10]
#eval unsafe_cert_revoke_imperative 99 []

-- Bounded PBT for functional/imperative equivalence.
example : (serialSamples.all (fun cert =>
    crlSamples.all (fun crl =>
      unsafe_cert_revoke cert crl == unsafe_cert_revoke_imperative cert crl))) = true := by
  native_decide

/-- Both implementations agree for every serial and CRL, without a precondition. -/
theorem functional_imperative_equivalence_thm
    (cert_serial : Int) (revocation_list : List Int) :
    unsafe_cert_revoke cert_serial revocation_list =
      unsafe_cert_revoke_imperative cert_serial revocation_list := by
  rfl

end UnsafeCertRevoke
end Agent
