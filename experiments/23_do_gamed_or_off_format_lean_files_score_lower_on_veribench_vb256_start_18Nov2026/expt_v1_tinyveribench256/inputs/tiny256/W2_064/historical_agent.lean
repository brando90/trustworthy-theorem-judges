import Mathlib
namespace Agent

/-!
# Safe phishing certificate check

Translation of the Python `safe_phishing_cert_check` and its test harness.
Host identifiers are `Int`, matching Python's unbounded signed integers. A
certificate matching the URL is not sufficient: that URL must also equal the
user's intended target. No positivity or other input restriction is imposed.

The specification characterizes both acceptance and rejection, including the
valid-certificate phishing attack. Bounded property-based tests are separate
from the kernel-checked proofs. The final implementation uses mutable state
and is proved equivalent to the functional implementation on all integers.
-/

namespace UnsafePhishingValidCertSafe

/-- Both certificate identity and user intent must match. -/
def safe_phishing_cert_check (intended_target url_host cert_host : Int) : Bool :=
  (cert_host == url_host) && (url_host == intended_target)

/-! ## Original unit tests -/

/-- Boolean version of the Python assertion harness; false denotes a failed assertion. -/
def check (candidate : Int → Int → Int → Bool) : Bool :=
  candidate 1 1 1 &&
  candidate 100 100 100 &&
  !(candidate 1 2 2) &&
  !(candidate 100 200 200) &&
  !(candidate 1 2 3) &&
  !(candidate 1 1 2) &&
  candidate 0 0 0 &&
  !(candidate 0 1 1)

example : safe_phishing_cert_check 1 1 1 = true := by native_decide
example : safe_phishing_cert_check 100 100 100 = true := by native_decide
example : safe_phishing_cert_check 1 2 2 = false := by native_decide
example : safe_phishing_cert_check 100 200 200 = false := by native_decide
example : safe_phishing_cert_check 1 2 3 = false := by native_decide
example : safe_phishing_cert_check 1 1 2 = false := by native_decide
example : safe_phishing_cert_check 0 0 0 = true := by native_decide
example : safe_phishing_cert_check 0 1 1 = false := by native_decide
example : check safe_phishing_cert_check = true := by native_decide

-- Signed identifiers are also admissible.
example : safe_phishing_cert_check (-7) (-7) (-7) = true := by native_decide
example : safe_phishing_cert_check (-7) 7 7 = false := by native_decide
example : safe_phishing_cert_check (-7) (-7) 7 = false := by native_decide

#eval safe_phishing_cert_check 1 1 1
#eval safe_phishing_cert_check 1 2 2
#eval check safe_phishing_cert_check
#eval if check safe_phishing_cert_check then "All tests passed." else "Test failure."

/-! ## Preconditions and proved properties -/

/-- The Python function is total on all triples of integers. -/
def Pre (_intended_target _url_host _cert_host : Int) : Prop := True

/-- Exact acceptance criterion: neither of the two comparisons can be omitted. -/
def acceptance_prop (intended_target url_host cert_host : Int) : Prop :=
  safe_phishing_cert_check intended_target url_host cert_host = true ↔
    cert_host = url_host ∧ url_host = intended_target

theorem acceptance_thm (intended_target url_host cert_host : Int) :
    acceptance_prop intended_target url_host cert_host := by
  simp [acceptance_prop, safe_phishing_cert_check]

/-- Exact rejection criterion, covering every failure case. -/
def rejection_prop (intended_target url_host cert_host : Int) : Prop :=
  safe_phishing_cert_check intended_target url_host cert_host = false ↔
    cert_host ≠ url_host ∨ url_host ≠ intended_target

theorem rejection_thm (intended_target url_host cert_host : Int) :
    rejection_prop intended_target url_host cert_host := by
  by_cases hcert : cert_host = url_host <;>
    simp [rejection_prop, safe_phishing_cert_check, hcert]

/-- Correct destination together with a matching certificate is accepted. -/
def correct_destination_prop (intended_target url_host cert_host : Int) : Prop :=
  cert_host = url_host → url_host = intended_target →
    safe_phishing_cert_check intended_target url_host cert_host = true

theorem correct_destination_thm (intended_target url_host cert_host : Int) :
    correct_destination_prop intended_target url_host cert_host := by
  intro hcert htarget
  simp [safe_phishing_cert_check, hcert, htarget]

/-- A valid certificate for a different destination does not defeat the check. -/
def phishing_blocked_prop (intended_target url_host cert_host : Int) : Prop :=
  cert_host = url_host → url_host ≠ intended_target →
    safe_phishing_cert_check intended_target url_host cert_host = false

theorem phishing_blocked_thm (intended_target url_host cert_host : Int) :
    phishing_blocked_prop intended_target url_host cert_host := by
  intro hcert htarget
  simp [safe_phishing_cert_check, hcert, htarget]

/-- A certificate for another host is always rejected, even at the intended URL. -/
def certificate_mismatch_prop (intended_target url_host cert_host : Int) : Prop :=
  cert_host ≠ url_host →
    safe_phishing_cert_check intended_target url_host cert_host = false

theorem certificate_mismatch_thm (intended_target url_host cert_host : Int) :
    certificate_mismatch_prop intended_target url_host cert_host := by
  intro hcert
  simp [safe_phishing_cert_check, hcert]

/-- A wrong destination is rejected regardless of the certificate. -/
def intent_required_prop (intended_target url_host cert_host : Int) : Prop :=
  url_host ≠ intended_target →
    safe_phishing_cert_check intended_target url_host cert_host = false

theorem intent_required_thm (intended_target url_host cert_host : Int) :
    intent_required_prop intended_target url_host cert_host := by
  intro htarget
  simp [safe_phishing_cert_check, htarget]

/-! ## Postcondition -/

/-- All functional and security obligations hold simultaneously. -/
def Post_prop (intended_target url_host cert_host : Int) : Prop :=
  acceptance_prop intended_target url_host cert_host ∧
  rejection_prop intended_target url_host cert_host ∧
  correct_destination_prop intended_target url_host cert_host ∧
  phishing_blocked_prop intended_target url_host cert_host ∧
  certificate_mismatch_prop intended_target url_host cert_host ∧
  intent_required_prop intended_target url_host cert_host

/-! ## Bounded property-based tests

Each test enumerates all triples from a signed range, also including the larger
identifiers used by the Python harness. The executable formulas below are the
Boolean forms of the corresponding propositions, not calls to their proofs.
These bounded tests do not restrict the domains of the universal theorems.
-/

def pbtHosts : List Int :=
  (List.range 11).map (fun n => (n : Int) - 5) ++ [-200, -100, 100, 200]

def allHostTriples (p : Int → Int → Int → Bool) : Bool :=
  pbtHosts.all (fun intended_target =>
    pbtHosts.all (fun url_host =>
      pbtHosts.all (fun cert_host => p intended_target url_host cert_host)))

-- PBT for acceptance_prop.
example : allHostTriples (fun t u c =>
    decide (safe_phishing_cert_check t u c = true ↔ c = u ∧ u = t)) = true := by
  native_decide

-- PBT for rejection_prop.
example : allHostTriples (fun t u c =>
    decide (safe_phishing_cert_check t u c = false ↔ c ≠ u ∨ u ≠ t)) = true := by
  native_decide

-- PBT for correct_destination_prop (including every all-equal triple).
example : allHostTriples (fun t u c =>
    decide (c = u → u = t → safe_phishing_cert_check t u c = true)) = true := by
  native_decide

-- PBT for phishing_blocked_prop (including matching certs at wrong URLs).
example : allHostTriples (fun t u c =>
    decide (c = u → u ≠ t → safe_phishing_cert_check t u c = false)) = true := by
  native_decide

-- PBT for certificate_mismatch_prop.
example : allHostTriples (fun t u c =>
    decide (c ≠ u → safe_phishing_cert_check t u c = false)) = true := by
  native_decide

-- PBT for intent_required_prop.
example : allHostTriples (fun t u c =>
    decide (u ≠ t → safe_phishing_cert_check t u c = false)) = true := by
  native_decide

-- PBT for the entire Post_prop, checking all six executable conjuncts together.
example : allHostTriples (fun t u c => decide (
    (safe_phishing_cert_check t u c = true ↔ c = u ∧ u = t) ∧
    (safe_phishing_cert_check t u c = false ↔ c ≠ u ∨ u ≠ t) ∧
    (c = u → u = t → safe_phishing_cert_check t u c = true) ∧
    (c = u → u ≠ t → safe_phishing_cert_check t u c = false) ∧
    (c ≠ u → safe_phishing_cert_check t u c = false) ∧
    (u ≠ t → safe_phishing_cert_check t u c = false))) = true := by
  native_decide

/-! ## Total correctness -/

theorem correctness_thm (intended_target url_host cert_host : Int) :
    Pre intended_target url_host cert_host →
      Post_prop intended_target url_host cert_host := by
  intro _
  exact ⟨acceptance_thm intended_target url_host cert_host,
    rejection_thm intended_target url_host cert_host,
    correct_destination_thm intended_target url_host cert_host,
    phishing_blocked_thm intended_target url_host cert_host,
    certificate_mismatch_thm intended_target url_host cert_host,
    intent_required_thm intended_target url_host cert_host⟩

/-! ## Imperative implementation and tests -/

/-- Start rejected and update the mutable result only after both comparisons pass. -/
def safe_phishing_cert_check_imperative
    (intended_target url_host cert_host : Int) : Bool := Id.run do
  let mut accepted := false
  if cert_host == url_host then
    if url_host == intended_target then
      accepted := true
  return accepted

example : safe_phishing_cert_check_imperative 1 1 1 = true := by native_decide
example : safe_phishing_cert_check_imperative 100 100 100 = true := by native_decide
example : safe_phishing_cert_check_imperative 1 2 2 = false := by native_decide
example : safe_phishing_cert_check_imperative 100 200 200 = false := by native_decide
example : safe_phishing_cert_check_imperative 1 2 3 = false := by native_decide
example : safe_phishing_cert_check_imperative 1 1 2 = false := by native_decide
example : safe_phishing_cert_check_imperative 0 0 0 = true := by native_decide
example : safe_phishing_cert_check_imperative 0 1 1 = false := by native_decide
example : check safe_phishing_cert_check_imperative = true := by native_decide
example : safe_phishing_cert_check_imperative (-7) (-7) (-7) = true := by native_decide
example : safe_phishing_cert_check_imperative (-7) 7 7 = false := by native_decide
example : safe_phishing_cert_check_imperative (-7) (-7) 7 = false := by native_decide

#eval safe_phishing_cert_check_imperative 1 1 1
#eval safe_phishing_cert_check_imperative 1 2 2
#eval check safe_phishing_cert_check_imperative

-- An additional bounded comparison of the two implementations.
example : allHostTriples (fun t u c =>
    safe_phishing_cert_check t u c == safe_phishing_cert_check_imperative t u c) = true := by
  native_decide

/-! ## Equivalence on the entire integer domain -/

theorem functional_imperative_equivalence_thm (intended_target url_host cert_host : Int) :
    safe_phishing_cert_check intended_target url_host cert_host =
      safe_phishing_cert_check_imperative intended_target url_host cert_host := by
  by_cases hcert : cert_host = url_host
  · subst cert_host
    by_cases htarget : url_host = intended_target <;>
      simp [safe_phishing_cert_check, safe_phishing_cert_check_imperative, htarget]
  · simp [safe_phishing_cert_check, safe_phishing_cert_check_imperative, hcert]

end UnsafePhishingValidCertSafe
end Agent
