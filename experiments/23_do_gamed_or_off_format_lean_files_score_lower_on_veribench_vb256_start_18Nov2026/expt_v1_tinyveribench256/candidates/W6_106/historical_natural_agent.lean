import Mathlib
namespace Agent

/-!
# Unsafe URI delegation

A translation of the Python `unsafe_uri_access` program from the Android URI
permission example. Access is exactly the delegation flag: the revocation flag
is deliberately ignored. In particular, a revoked delegation still grants
access. This formalizes the vulnerable implementation, not a repaired policy.

Both inputs range over all Booleans. Exhaustive property-based tests therefore
cover the complete input domain, including both possible revocation settings.
The named theorems use kernel-checked proofs; `native_decide` is used only for
executable tests.
-/

namespace UnsafeUriDelegation

-- Functional implementation. The unused argument makes the vulnerability explicit.
def unsafe_uri_access (has_delegation : Bool) (_is_revoked : Bool) : Bool :=
  has_delegation

-- Executable translation of all five groups of assertions in Python's `check`.
def check (candidate : Bool → Bool → Bool) : Bool :=
  candidate true false &&
  candidate true true &&
  !(candidate false false) &&
  !(candidate false true) &&
  [true, false].all (fun revoked => candidate true revoked)

-- Unit tests: the four input combinations and the loop over revocation flags.
example : unsafe_uri_access true false = true := by native_decide
example : unsafe_uri_access true true = true := by native_decide
example : unsafe_uri_access false false = false := by native_decide
example : unsafe_uri_access false true = false := by native_decide
example : [true, false].all (fun revoked => unsafe_uri_access true revoked) = true := by
  native_decide
example : check unsafe_uri_access = true := by native_decide

#eval [unsafe_uri_access true false, unsafe_uri_access true true,
       unsafe_uri_access false false, unsafe_uri_access false true]
#eval check unsafe_uri_access

-- There are no preconditions beyond the Boolean input types.
def Pre (_has_delegation _is_revoked : Bool) : Prop := True

-- Exact return-value semantics for every input.
def returns_delegation_prop (has_delegation is_revoked : Bool) : Prop :=
  unsafe_uri_access has_delegation is_revoked = has_delegation

theorem returns_delegation_thm (has_delegation is_revoked : Bool) :
    returns_delegation_prop has_delegation is_revoked := by
  rfl

-- An active delegation that has not been revoked grants access.
def active_delegation_allowed_prop (has_delegation is_revoked : Bool) : Prop :=
  has_delegation = true → is_revoked = false →
    unsafe_uri_access has_delegation is_revoked = true

theorem active_delegation_allowed_thm (has_delegation is_revoked : Bool) :
    active_delegation_allowed_prop has_delegation is_revoked := by
  unfold active_delegation_allowed_prop
  intro hdelegation _
  simpa only [unsafe_uri_access] using hdelegation

-- The security bug: even an explicitly revoked delegation grants access.
def revoked_delegation_allowed_prop (has_delegation is_revoked : Bool) : Prop :=
  has_delegation = true → is_revoked = true →
    unsafe_uri_access has_delegation is_revoked = true

theorem revoked_delegation_allowed_thm (has_delegation is_revoked : Bool) :
    revoked_delegation_allowed_prop has_delegation is_revoked := by
  unfold revoked_delegation_allowed_prop
  intro hdelegation _
  simpa only [unsafe_uri_access] using hdelegation

-- Without a delegation, access is denied regardless of revocation.
def no_delegation_denied_prop (has_delegation is_revoked : Bool) : Prop :=
  has_delegation = false → unsafe_uri_access has_delegation is_revoked = false

theorem no_delegation_denied_thm (has_delegation is_revoked : Bool) :
    no_delegation_denied_prop has_delegation is_revoked := by
  unfold no_delegation_denied_prop
  intro hdelegation
  simpa only [unsafe_uri_access] using hdelegation

-- Changing the revocation flag never changes the answer, for either delegation flag.
def revocation_ignored_prop (has_delegation is_revoked : Bool) : Prop :=
  ∀ other_revoked : Bool,
    unsafe_uri_access has_delegation is_revoked =
      unsafe_uri_access has_delegation other_revoked

theorem revocation_ignored_thm (has_delegation is_revoked : Bool) :
    revocation_ignored_prop has_delegation is_revoked := by
  intro other_revoked
  rfl

-- The postcondition collects all behavioral properties of the unsafe program.
def Post_prop (has_delegation is_revoked : Bool) : Prop :=
  returns_delegation_prop has_delegation is_revoked ∧
  active_delegation_allowed_prop has_delegation is_revoked ∧
  revoked_delegation_allowed_prop has_delegation is_revoked ∧
  no_delegation_denied_prop has_delegation is_revoked ∧
  revocation_ignored_prop has_delegation is_revoked

/-! ## Exhaustive property-based tests

The list contains every Boolean. Nested `all` checks test all four input pairs,
or all eight triples when comparing two revocation settings. Implications are
encoded as Boolean disjunctions, so no `Decidable` instances for the specification
predicates are needed. In particular, no admissible input is filtered out.
-/

def boolInputs : List Bool := [false, true]

-- PBT for returns_delegation_prop.
example : boolInputs.all (fun has_delegation =>
    boolInputs.all (fun is_revoked =>
      unsafe_uri_access has_delegation is_revoked == has_delegation)) = true := by
  native_decide

-- PBT for active_delegation_allowed_prop: (delegated and not revoked) implies access.
example : boolInputs.all (fun has_delegation =>
    boolInputs.all (fun is_revoked =>
      (!(has_delegation && !is_revoked) ||
        unsafe_uri_access has_delegation is_revoked))) = true := by
  native_decide

-- PBT for revoked_delegation_allowed_prop: (delegated and revoked) still implies access.
example : boolInputs.all (fun has_delegation =>
    boolInputs.all (fun is_revoked =>
      (!(has_delegation && is_revoked) ||
        unsafe_uri_access has_delegation is_revoked))) = true := by
  native_decide

-- PBT for no_delegation_denied_prop: not delegated implies not allowed.
example : boolInputs.all (fun has_delegation =>
    boolInputs.all (fun is_revoked =>
      (has_delegation || !(unsafe_uri_access has_delegation is_revoked)))) = true := by
  native_decide

-- PBT for revocation_ignored_prop, including every alternative revocation flag.
example : boolInputs.all (fun has_delegation =>
    boolInputs.all (fun is_revoked =>
      boolInputs.all (fun other_revoked =>
        unsafe_uri_access has_delegation is_revoked ==
          unsafe_uri_access has_delegation other_revoked))) = true := by
  native_decide

-- Executable Boolean form of the entire conjunction in Post_prop.
def postCheck (has_delegation is_revoked : Bool) : Bool :=
  let result := unsafe_uri_access has_delegation is_revoked
  (result == has_delegation) &&
  (!(has_delegation && !is_revoked) || result) &&
  (!(has_delegation && is_revoked) || result) &&
  (has_delegation || !result) &&
  boolInputs.all (fun other_revoked =>
    result == unsafe_uri_access has_delegation other_revoked)

-- PBT for Post_prop over the entire admissible input domain.
example : boolInputs.all (fun has_delegation =>
    boolInputs.all (fun is_revoked => postCheck has_delegation is_revoked)) = true := by
  native_decide

#eval boolInputs.all (fun has_delegation =>
  boolInputs.all (fun is_revoked => postCheck has_delegation is_revoked))

-- Correctness means faithfully implementing the unsafe behavior, not enforcing revocation.
theorem correctness (has_delegation is_revoked : Bool) :
    Pre has_delegation is_revoked → Post_prop has_delegation is_revoked := by
  intro _
  exact ⟨returns_delegation_thm has_delegation is_revoked,
    active_delegation_allowed_thm has_delegation is_revoked,
    revoked_delegation_allowed_thm has_delegation is_revoked,
    no_delegation_denied_thm has_delegation is_revoked,
    revocation_ignored_thm has_delegation is_revoked⟩

-- Imperative implementation: assign the delegation flag to mutable access state.
-- Revocation is deliberately never consulted here either.
def unsafe_uri_access_imperative (has_delegation : Bool) (_is_revoked : Bool) : Bool := Id.run do
  let mut access := false
  access := has_delegation
  return access

-- Imperative tests reproduce the complete Python check.
example : unsafe_uri_access_imperative true false = true := by native_decide
example : unsafe_uri_access_imperative true true = true := by native_decide
example : unsafe_uri_access_imperative false false = false := by native_decide
example : unsafe_uri_access_imperative false true = false := by native_decide
example : [true, false].all (fun revoked =>
    unsafe_uri_access_imperative true revoked) = true := by native_decide
example : check unsafe_uri_access_imperative = true := by native_decide

#eval [unsafe_uri_access_imperative true false, unsafe_uri_access_imperative true true,
       unsafe_uri_access_imperative false false, unsafe_uri_access_imperative false true]
#eval check unsafe_uri_access_imperative

-- Exhaustive executable equivalence test, in addition to the proof below.
example : boolInputs.all (fun has_delegation =>
    boolInputs.all (fun is_revoked =>
      unsafe_uri_access has_delegation is_revoked ==
        unsafe_uri_access_imperative has_delegation is_revoked)) = true := by
  native_decide

-- Kernel-checked equivalence for all inputs, with no precondition.
theorem functional_imperative_equiv (has_delegation is_revoked : Bool) :
    unsafe_uri_access has_delegation is_revoked =
      unsafe_uri_access_imperative has_delegation is_revoked := by
  rfl

end UnsafeUriDelegation
end Agent
