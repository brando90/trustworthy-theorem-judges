import Mathlib
namespace Agent

/-!
# Safe hard-fail OCSP revocation checking

Translation of `safe_hard_fail_revocation` and its Python assertion suite.
A certificate is accepted exactly when an OCSP response is present and the
certificate is not revoked. Missing responses are rejected, even for an
unrevoked certificate: blocking the response cannot bypass revocation checking.
The response-presence flag has the same meaning as in the Python source; no
additional OCSP parsing or validation is introduced here.

Both inputs range over all Booleans. The property-based tests exhaust this
entire finite domain. Tests use `native_decide`; all named theorems use only
kernel-checked proofs. An imperative, default-deny version is also verified.
-/

namespace SafeHardFailRevocation

/-! ## Functional implementation -/

def safe_hard_fail_revocation
    (cert_revoked ocsp_response_present : Bool) : Bool :=
  ocsp_response_present && !cert_revoked

/-- Executable counterpart of Python's five assertions, including the repeated
missing-response regression check. -/
def check (candidate : Bool → Bool → Bool) : Bool :=
  (candidate true false == false) &&
  (candidate false false == false) &&
  (candidate true true == false) &&
  (candidate false true == true) &&
  (candidate true false == false)

/-! ## Unit tests -/

example : safe_hard_fail_revocation true false = false := by native_decide
example : safe_hard_fail_revocation false false = false := by native_decide
example : safe_hard_fail_revocation true true = false := by native_decide
example : safe_hard_fail_revocation false true = true := by native_decide
-- Repeated core-fix regression test from the source.
example : safe_hard_fail_revocation true false = false := by native_decide
example : check safe_hard_fail_revocation = true := by native_decide

#eval safe_hard_fail_revocation true false
#eval safe_hard_fail_revocation false false
#eval safe_hard_fail_revocation true true
#eval safe_hard_fail_revocation false true
#eval check safe_hard_fail_revocation
#eval if check safe_hard_fail_revocation then "All tests passed." else "Tests failed."

/-! ## Precondition -/

/-- Every pair of Boolean inputs is admissible, including an absent response. -/
def Pre (_cert_revoked _ocsp_response_present : Bool) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- No OCSP response means rejection, regardless of revocation status. -/
def missing_response_prop (cert_revoked : Bool) : Prop :=
  safe_hard_fail_revocation cert_revoked false = false

theorem missing_response_thm (cert_revoked : Bool) :
    missing_response_prop cert_revoked := by
  cases cert_revoked <;> rfl

/-- A revoked certificate is rejected, whether or not a response is present. -/
def revoked_prop (ocsp_response_present : Bool) : Prop :=
  safe_hard_fail_revocation true ocsp_response_present = false

theorem revoked_thm (ocsp_response_present : Bool) :
    revoked_prop ocsp_response_present := by
  cases ocsp_response_present <;> rfl

/-- With an OCSP response, exactly the unrevoked certificates are accepted. -/
def present_response_prop (cert_revoked : Bool) : Prop :=
  safe_hard_fail_revocation cert_revoked true = !cert_revoked

theorem present_response_thm (cert_revoked : Bool) :
    present_response_prop cert_revoked := by
  cases cert_revoked <;> rfl

/-- Exact necessary and sufficient conditions for acceptance. -/
def acceptance_prop (cert_revoked ocsp_response_present : Bool) : Prop :=
  safe_hard_fail_revocation cert_revoked ocsp_response_present = true ↔
    ocsp_response_present = true ∧ cert_revoked = false

theorem acceptance_thm (cert_revoked ocsp_response_present : Bool) :
    acceptance_prop cert_revoked ocsp_response_present := by
  cases cert_revoked <;> cases ocsp_response_present <;>
    simp [acceptance_prop, safe_hard_fail_revocation]

/-- Exact necessary and sufficient conditions for rejection. -/
def rejection_prop (cert_revoked ocsp_response_present : Bool) : Prop :=
  safe_hard_fail_revocation cert_revoked ocsp_response_present = false ↔
    ocsp_response_present = false ∨ cert_revoked = true

theorem rejection_thm (cert_revoked ocsp_response_present : Bool) :
    rejection_prop cert_revoked ocsp_response_present := by
  cases cert_revoked <;> cases ocsp_response_present <;>
    simp [rejection_prop, safe_hard_fail_revocation]

/-! ## Postcondition -/

def Post_prop (cert_revoked ocsp_response_present : Bool) : Prop :=
  missing_response_prop cert_revoked ∧
  revoked_prop ocsp_response_present ∧
  present_response_prop cert_revoked ∧
  acceptance_prop cert_revoked ocsp_response_present ∧
  rejection_prop cert_revoked ocsp_response_present

/-! ## Exhaustive property-based tests

The bounded domain `[false, true]` is the complete input domain, not a sample.
Each test below checks the executable Boolean form of the indicated property.
Boolean equality represents the logical equivalences in the specifications.
-/

def boolInputs : List Bool := [false, true]

-- PBT for missing_response_prop: both revocation statuses.
example : boolInputs.all (fun r =>
    safe_hard_fail_revocation r false == false) = true := by
  native_decide

-- PBT for revoked_prop: both response-presence statuses.
example : boolInputs.all (fun p =>
    safe_hard_fail_revocation true p == false) = true := by
  native_decide

-- PBT for present_response_prop: both revocation statuses.
example : boolInputs.all (fun r =>
    safe_hard_fail_revocation r true == !r) = true := by
  native_decide

-- PBT for acceptance_prop: all four input pairs.
example : boolInputs.all (fun r => boolInputs.all (fun p =>
    (safe_hard_fail_revocation r p == true) ==
      ((p == true) && (r == false)))) = true := by
  native_decide

-- PBT for rejection_prop: all four input pairs.
example : boolInputs.all (fun r => boolInputs.all (fun p =>
    (safe_hard_fail_revocation r p == false) ==
      ((p == false) || (r == true)))) = true := by
  native_decide

/-- Executable Boolean form of the complete postcondition. -/
def postCheck (r p : Bool) : Bool :=
  (safe_hard_fail_revocation r false == false) &&
  (safe_hard_fail_revocation true p == false) &&
  (safe_hard_fail_revocation r true == !r) &&
  ((safe_hard_fail_revocation r p == true) ==
    ((p == true) && (r == false))) &&
  ((safe_hard_fail_revocation r p == false) ==
    ((p == false) || (r == true)))

-- PBT for Post_prop: all conjuncts on every input pair.
example : boolInputs.all (fun r => boolInputs.all (postCheck r)) = true := by
  native_decide

#eval boolInputs.all (fun r => boolInputs.all (postCheck r))

/-! ## Correctness -/

theorem correctness_thm (cert_revoked ocsp_response_present : Bool) :
    Pre cert_revoked ocsp_response_present →
      Post_prop cert_revoked ocsp_response_present := by
  intro _
  unfold Post_prop
  exact ⟨missing_response_thm cert_revoked,
    revoked_thm ocsp_response_present,
    present_response_thm cert_revoked,
    acceptance_thm cert_revoked ocsp_response_present,
    rejection_thm cert_revoked ocsp_response_present⟩

/-! ## Imperative implementation -/

/-- Start by rejecting. Only a present response and non-revoked certificate can
change the mutable decision to acceptance. -/
def safe_hard_fail_revocation_imperative
    (cert_revoked ocsp_response_present : Bool) : Bool := Id.run do
  let mut accepted := false
  if ocsp_response_present then
    if !cert_revoked then
      accepted := true
  return accepted

/-! ## Imperative tests -/

example : safe_hard_fail_revocation_imperative true false = false := by native_decide
example : safe_hard_fail_revocation_imperative false false = false := by native_decide
example : safe_hard_fail_revocation_imperative true true = false := by native_decide
example : safe_hard_fail_revocation_imperative false true = true := by native_decide
example : safe_hard_fail_revocation_imperative true false = false := by native_decide
example : check safe_hard_fail_revocation_imperative = true := by native_decide

#eval check safe_hard_fail_revocation_imperative

-- Exhaustive executable comparison of the two implementations.
example : boolInputs.all (fun r => boolInputs.all (fun p =>
    safe_hard_fail_revocation r p ==
      safe_hard_fail_revocation_imperative r p)) = true := by
  native_decide

/-! ## Functional-imperative equivalence -/

theorem functional_imperative_equiv_thm
    (cert_revoked ocsp_response_present : Bool) :
    safe_hard_fail_revocation cert_revoked ocsp_response_present =
      safe_hard_fail_revocation_imperative cert_revoked ocsp_response_present := by
  cases cert_revoked <;> cases ocsp_response_present <;> rfl

theorem functional_imperative_eq_thm :
    safe_hard_fail_revocation = safe_hard_fail_revocation_imperative := by
  funext cert_revoked ocsp_response_present
  exact functional_imperative_equiv_thm cert_revoked ocsp_response_present

end SafeHardFailRevocation
end Agent
