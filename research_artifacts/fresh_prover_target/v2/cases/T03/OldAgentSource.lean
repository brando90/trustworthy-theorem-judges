import Mathlib

/-!
# Safe URI delegation

Translation of the Python module `safe_uri_access` (mitigation for the URI
delegation vulnerability from MIT 6.858 Lecture 10).

Access to a URI is granted only when an active delegation exists **and** that
delegation has not been revoked:

```python
def safe_uri_access(has_delegation: bool, is_revoked: bool) -> bool:
    return has_delegation and not is_revoked
```

This file provides a functional implementation, an imperative
(`Id.run do`) implementation, the unit tests from the Python `check`
function, the safety properties of interest, and proofs that the two
implementations agree.
-/

namespace «61_unsafeUriDelegation_safe»

/-! ## Functional implementation -/

/-- Grant access only when a valid (non-revoked) delegation exists. -/
def safeUriAccess (hasDelegation : Bool) (isRevoked : Bool) : Bool :=
  hasDelegation && !isRevoked

/-! ## Unit tests (the four cases of the Python `check` function) -/

-- 1) Active delegation, not revoked — allowed
example : safeUriAccess true false = true := by native_decide
-- 2) Fix: delegation exists but is revoked — denied
example : safeUriAccess true true = false := by native_decide
-- 3) No delegation, not revoked — denied
example : safeUriAccess false false = false := by native_decide
-- 4) No delegation, revoked — denied
example : safeUriAccess false true = false := by native_decide

#eval safeUriAccess true false
#eval safeUriAccess true true
#eval safeUriAccess false false
#eval safeUriAccess false true

/-! ## Pre-condition -/

/-- Every pair of boolean inputs is admissible: the Python function is total. -/
def Pre (_hasDelegation : Bool) (_isRevoked : Bool) : Prop := True

/-! ## Properties -/

/-- Access is granted exactly on the pair `(true, false)`. -/
def grant_iff_prop (hasDelegation isRevoked : Bool) : Prop :=
  safeUriAccess hasDelegation isRevoked = true ↔ (hasDelegation = true ∧ isRevoked = false)

theorem grant_iff_thm (hasDelegation isRevoked : Bool) :
    grant_iff_prop hasDelegation isRevoked := by
  cases hasDelegation <;> cases isRevoked <;> simp [grant_iff_prop, safeUriAccess]

/-- Revocation always denies access (this is the fix for the vulnerability). -/
def revoked_denies_prop (hasDelegation isRevoked : Bool) : Prop :=
  isRevoked = true → safeUriAccess hasDelegation isRevoked = false

theorem revoked_denies_thm (hasDelegation isRevoked : Bool) :
    revoked_denies_prop hasDelegation isRevoked := by
  cases hasDelegation <;> cases isRevoked <;> simp [revoked_denies_prop, safeUriAccess]

/-- Without a delegation there is no access, whatever the revocation flag says. -/
def no_delegation_denies_prop (hasDelegation isRevoked : Bool) : Prop :=
  hasDelegation = false → safeUriAccess hasDelegation isRevoked = false

theorem no_delegation_denies_thm (hasDelegation isRevoked : Bool) :
    no_delegation_denies_prop hasDelegation isRevoked := by
  cases hasDelegation <;> cases isRevoked <;> simp [no_delegation_denies_prop, safeUriAccess]

/-- Access is granted for at least one configuration: the mitigation is not
vacuous (it does not simply deny everything). -/
def not_always_denied_prop : Prop :=
  safeUriAccess true false = true

theorem not_always_denied_thm : not_always_denied_prop := by
  simp [not_always_denied_prop, safeUriAccess]

/-- The result matches the Python expression `has_delegation and not is_revoked`. -/
def matches_spec_prop (hasDelegation isRevoked : Bool) : Prop :=
  safeUriAccess hasDelegation isRevoked = (hasDelegation && !isRevoked)

theorem matches_spec_thm (hasDelegation isRevoked : Bool) :
    matches_spec_prop hasDelegation isRevoked := by
  simp [matches_spec_prop, safeUriAccess]

/-- The four unit tests of the Python `check` function. -/
def check_prop : Prop :=
  safeUriAccess true false = true ∧
  safeUriAccess true true = false ∧
  safeUriAccess false false = false ∧
  safeUriAccess false true = false

theorem check_thm : check_prop := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [safeUriAccess]

/-! ## Post-condition and correctness -/

/-- Full post-condition: the conjunction of all the properties above. -/
def Post_prop (hasDelegation isRevoked : Bool) : Prop :=
  grant_iff_prop hasDelegation isRevoked ∧
  revoked_denies_prop hasDelegation isRevoked ∧
  no_delegation_denies_prop hasDelegation isRevoked ∧
  matches_spec_prop hasDelegation isRevoked ∧
  not_always_denied_prop ∧
  check_prop

/-- Correctness: the pre-condition implies the post-condition. -/
theorem correctness_thm (hasDelegation isRevoked : Bool) :
    Pre hasDelegation isRevoked → Post_prop hasDelegation isRevoked := by
  intro _
  exact ⟨grant_iff_thm hasDelegation isRevoked,
         revoked_denies_thm hasDelegation isRevoked,
         no_delegation_denies_thm hasDelegation isRevoked,
         matches_spec_thm hasDelegation isRevoked,
         not_always_denied_thm,
         check_thm⟩

/-! ## Imperative implementation -/

/-- Imperative version: start by denying, grant on a delegation, then revoke. -/
def safeUriAccessImp (hasDelegation : Bool) (isRevoked : Bool) : Bool := Id.run do
  let mut granted : Bool := false
  if hasDelegation then
    granted := true
  if isRevoked then
    granted := false
  return granted

/-! ## Imperative unit tests -/

example : safeUriAccessImp true false = true := by native_decide
example : safeUriAccessImp true true = false := by native_decide
example : safeUriAccessImp false false = false := by native_decide
example : safeUriAccessImp false true = false := by native_decide

#eval safeUriAccessImp true false
#eval safeUriAccessImp true true
#eval safeUriAccessImp false false
#eval safeUriAccessImp false true

/-! ## Equivalence of the two implementations -/

def equiv_prop (hasDelegation isRevoked : Bool) : Prop :=
  safeUriAccess hasDelegation isRevoked = safeUriAccessImp hasDelegation isRevoked

theorem equiv_thm (hasDelegation isRevoked : Bool) : equiv_prop hasDelegation isRevoked := by
  cases hasDelegation <;> cases isRevoked <;> rfl

/-- Point-free form of the equivalence theorem. -/
theorem safeUriAccess_eq_imp : safeUriAccess = safeUriAccessImp := by
  funext hasDelegation isRevoked
  exact equiv_thm hasDelegation isRevoked

end «61_unsafeUriDelegation_safe»
