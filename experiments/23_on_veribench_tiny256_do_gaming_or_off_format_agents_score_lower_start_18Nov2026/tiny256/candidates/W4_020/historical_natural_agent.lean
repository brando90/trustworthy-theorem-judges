import Mathlib
namespace Agent

/-!
# Safe URI delegation

A translation of the Python `safe_uri_access` program: access is granted exactly
when a delegation exists and has not been revoked. Both inputs range over all
Booleans. The Boolean `check` function represents the Python assertion harness.

The security properties and correctness theorem are proved by kernel-checked
reasoning. Separate executable property-based tests exhaust the entire Boolean
input space. A mutable-state implementation is proved equivalent to the
functional implementation.
-/

namespace UnsafeUriDelegationSafe

/-! ## Functional implementation -/

def safe_uri_access (has_delegation is_revoked : Bool) : Bool :=
  has_delegation && !is_revoked

/-! ## Unit tests and the Python test harness -/

def check (candidate : Bool → Bool → Bool) : Bool :=
  candidate true false &&
    !(candidate true true) &&
    !(candidate false false) &&
    !(candidate false true)

example : safe_uri_access true false = true := by native_decide
example : safe_uri_access true true = false := by native_decide
example : safe_uri_access false false = false := by native_decide
example : safe_uri_access false true = false := by native_decide
example : check safe_uri_access = true := by native_decide

#eval safe_uri_access true false
#eval safe_uri_access true true
#eval safe_uri_access false false
#eval safe_uri_access false true
#eval check safe_uri_access
#eval if check safe_uri_access then "All tests passed." else "Candidate failed tests"

/-! ## Precondition -/

/-- There are no restrictions on the two Boolean inputs. -/
def Pre (_has_delegation _is_revoked : Bool) : Prop := True

/-! ## Semantic properties -/

/-- Access is granted if and only if an active delegation exists. -/
def authorization_prop (has_delegation is_revoked : Bool) : Prop :=
  safe_uri_access has_delegation is_revoked = true ↔
    has_delegation = true ∧ is_revoked = false

theorem authorization_thm (has_delegation is_revoked : Bool) :
    authorization_prop has_delegation is_revoked := by
  cases has_delegation <;> cases is_revoked <;>
    simp [authorization_prop, safe_uri_access]

/-- Revocation denies access, even when a delegation exists. -/
def revoked_denied_prop (has_delegation is_revoked : Bool) : Prop :=
  is_revoked = true → safe_uri_access has_delegation is_revoked = false

theorem revoked_denied_thm (has_delegation is_revoked : Bool) :
    revoked_denied_prop has_delegation is_revoked := by
  cases has_delegation <;> cases is_revoked <;>
    simp [revoked_denied_prop, safe_uri_access]

/-- Absence of a delegation denies access, regardless of revocation status. -/
def no_delegation_denied_prop (has_delegation is_revoked : Bool) : Prop :=
  has_delegation = false → safe_uri_access has_delegation is_revoked = false

theorem no_delegation_denied_thm (has_delegation is_revoked : Bool) :
    no_delegation_denied_prop has_delegation is_revoked := by
  cases has_delegation <;> cases is_revoked <;>
    simp [no_delegation_denied_prop, safe_uri_access]

/-- A delegation that has not been revoked must grant access. -/
def active_allowed_prop (has_delegation is_revoked : Bool) : Prop :=
  has_delegation = true → is_revoked = false →
    safe_uri_access has_delegation is_revoked = true

theorem active_allowed_thm (has_delegation is_revoked : Bool) :
    active_allowed_prop has_delegation is_revoked := by
  cases has_delegation <;> cases is_revoked <;>
    simp [active_allowed_prop, safe_uri_access]

/-! ## Postcondition -/

def Post_prop (has_delegation is_revoked : Bool) : Prop :=
  authorization_prop has_delegation is_revoked ∧
  revoked_denied_prop has_delegation is_revoked ∧
  no_delegation_denied_prop has_delegation is_revoked ∧
  active_allowed_prop has_delegation is_revoked

/-! ## Exhaustive property-based tests

The following Boolean checks mirror each proposition above without needing
Decidable instances for the named propositions. Unlike individual unit cases,
each PBT enumerates the Cartesian product of the entire input domains.
-/

def allBoolPairs (p : Bool → Bool → Bool) : Bool :=
  [false, true].all (fun h => [false, true].all (fun r => p h r))

/-- Executable form of `authorization_prop`. -/
def authorization_check (h r : Bool) : Bool :=
  decide (safe_uri_access h r = true ↔ h = true ∧ r = false)

/-- Executable form of `revoked_denied_prop`. -/
def revoked_denied_check (h r : Bool) : Bool :=
  decide (r = true → safe_uri_access h r = false)

/-- Executable form of `no_delegation_denied_prop`. -/
def no_delegation_denied_check (h r : Bool) : Bool :=
  decide (h = false → safe_uri_access h r = false)

/-- Executable form of `active_allowed_prop`. -/
def active_allowed_check (h r : Bool) : Bool :=
  decide (h = true → r = false → safe_uri_access h r = true)

/-- Executable conjunction corresponding to `Post_prop`. -/
def post_check (h r : Bool) : Bool :=
  authorization_check h r &&
  revoked_denied_check h r &&
  no_delegation_denied_check h r &&
  active_allowed_check h r

-- PBT for authorization_prop.
example : allBoolPairs authorization_check = true := by native_decide
#eval allBoolPairs authorization_check

-- PBT for revoked_denied_prop.
example : allBoolPairs revoked_denied_check = true := by native_decide
#eval allBoolPairs revoked_denied_check

-- PBT for no_delegation_denied_prop.
example : allBoolPairs no_delegation_denied_check = true := by native_decide
#eval allBoolPairs no_delegation_denied_check

-- PBT for active_allowed_prop.
example : allBoolPairs active_allowed_check = true := by native_decide
#eval allBoolPairs active_allowed_check

-- PBT for Post_prop; Pre is True for every tested input.
example : allBoolPairs post_check = true := by native_decide
#eval allBoolPairs post_check

/-! ## Correctness -/

theorem correctness_thm (has_delegation is_revoked : Bool) :
    Pre has_delegation is_revoked → Post_prop has_delegation is_revoked := by
  intro _
  exact ⟨authorization_thm has_delegation is_revoked,
    revoked_denied_thm has_delegation is_revoked,
    no_delegation_denied_thm has_delegation is_revoked,
    active_allowed_thm has_delegation is_revoked⟩

/-! ## Imperative implementation -/

def safe_uri_access_imperative (has_delegation is_revoked : Bool) : Bool := Id.run do
  let mut access := false
  if has_delegation then
    if !is_revoked then
      access := true
  return access

/-! ## Imperative tests -/

example : safe_uri_access_imperative true false = true := by native_decide
example : safe_uri_access_imperative true true = false := by native_decide
example : safe_uri_access_imperative false false = false := by native_decide
example : safe_uri_access_imperative false true = false := by native_decide
example : check safe_uri_access_imperative = true := by native_decide

#eval safe_uri_access_imperative true false
#eval safe_uri_access_imperative true true
#eval safe_uri_access_imperative false false
#eval safe_uri_access_imperative false true
#eval check safe_uri_access_imperative

/-! ## Functional-imperative equivalence -/

theorem functional_imperative_equivalence_thm (has_delegation is_revoked : Bool) :
    safe_uri_access has_delegation is_revoked =
      safe_uri_access_imperative has_delegation is_revoked := by
  cases has_delegation <;> cases is_revoked <;> rfl

end UnsafeUriDelegationSafe
end Agent
