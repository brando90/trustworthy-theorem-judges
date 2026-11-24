import Mathlib
namespace Agent

/-!
# Safe firmware updates: rollback protection

Translation of the Python `safe_update_accept` function and its assertion-based
checker. An update is accepted exactly when its version is strictly newer.
`Int` models Python's arbitrary-precision signed integers: neither implementation
nor specification assumes that versions are nonnegative. The precondition is
therefore unrestricted. The bounded property-based tests include negative,
zero, and positive versions; universal guarantees are proved separately.
-/

namespace «37_unsafeRollback_safe»

/-! ## Functional implementation -/

def safe_update_accept (new_version current_version : Int) : Bool :=
  decide (new_version > current_version)

/-- Executable counterpart of the nine assertions in the Python checker. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 5 3 &&
  candidate 100 1 &&
  candidate 2 1 &&
  !(candidate 3 3) &&
  !(candidate 1 5) &&
  !(candidate 0 10) &&
  !(candidate 9 10) &&
  candidate 1 0 &&
  !(candidate 0 0)

/-! ## Unit tests -/

example : safe_update_accept 5 3 = true := by native_decide
example : safe_update_accept 100 1 = true := by native_decide
example : safe_update_accept 2 1 = true := by native_decide
example : safe_update_accept 3 3 = false := by native_decide
example : safe_update_accept 1 5 = false := by native_decide
example : safe_update_accept 0 10 = false := by native_decide
example : safe_update_accept 9 10 = false := by native_decide
example : safe_update_accept 1 0 = true := by native_decide
example : safe_update_accept 0 0 = false := by native_decide
example : check safe_update_accept = true := by native_decide

-- Additional tests ensure that the signed Python input domain is retained.
example : safe_update_accept (-1) (-2) = true := by native_decide
example : safe_update_accept (-2) (-1) = false := by native_decide
example : safe_update_accept (-1) (-1) = false := by native_decide
example : safe_update_accept 0 (-1) = true := by native_decide

#eval safe_update_accept 5 3
#eval safe_update_accept 1 5
#eval check safe_update_accept
#eval if check safe_update_accept then "All tests passed." else "Tests failed."

/-! ## Preconditions and universally proved properties -/

/-- Every pair of Python integers is admissible. -/
def Pre (_new_version _current_version : Int) : Prop := True

/-- Exact acceptance semantics, in both directions. -/
def acceptance_prop (new_version current_version : Int) : Prop :=
  safe_update_accept new_version current_version = true ↔
    current_version < new_version

theorem acceptance_thm (new_version current_version : Int) :
    acceptance_prop new_version current_version := by sorry

/-- Every strictly newer version is accepted. -/
def newer_accepted_prop (new_version current_version : Int) : Prop :=
  current_version < new_version →
    safe_update_accept new_version current_version = true

theorem newer_accepted_thm (new_version current_version : Int) :
    newer_accepted_prop new_version current_version := by sorry

/-- Exact rejection semantics: equal and older versions, and no others. -/
def rejection_prop (new_version current_version : Int) : Prop :=
  safe_update_accept new_version current_version = false ↔
    new_version ≤ current_version

theorem rejection_thm (new_version current_version : Int) :
    rejection_prop new_version current_version := by sorry

/-- A no-op update to the same version is rejected. -/
def same_version_prop (version : Int) : Prop :=
  safe_update_accept version version = false

theorem same_version_thm (version : Int) : same_version_prop version := by sorry

/-- Every downgrade is rejected, regardless of its size. -/
def rollback_protection_prop (new_version current_version : Int) : Prop :=
  new_version < current_version →
    safe_update_accept new_version current_version = false

theorem rollback_protection_thm (new_version current_version : Int) :
    rollback_protection_prop new_version current_version := by sorry

/-! ## Postcondition -/

/-- All update-policy guarantees hold together. -/
def Post_prop (new_version current_version : Int) : Prop :=
  acceptance_prop new_version current_version ∧
  newer_accepted_prop new_version current_version ∧
  rejection_prop new_version current_version ∧
  same_version_prop current_version ∧
  rollback_protection_prop new_version current_version

/-! ## Bounded property-based tests

Each check uses the executable Boolean form of the named property, independently
of its proof. Pairwise tests exhaust all 1681 pairs in [-20, 20] × [-20, 20].
These finite tests are evidence, not substitutes for the universal theorems.
-/

def testVersions : List Int :=
  (List.range 41).map (fun n => (n : Int) - 20)

-- PBT for acceptance_prop.
example : (testVersions.all (fun n => testVersions.all (fun c =>
    safe_update_accept n c == decide (c < n)))) = true := by
  native_decide

-- PBT for newer_accepted_prop (decidable implication).
example : (testVersions.all (fun n => testVersions.all (fun c =>
    if c < n then safe_update_accept n c else true))) = true := by
  native_decide

-- PBT for rejection_prop.
example : (testVersions.all (fun n => testVersions.all (fun c =>
    (!(safe_update_accept n c)) == decide (n ≤ c)))) = true := by
  native_decide

-- PBT for same_version_prop.
example : (testVersions.all (fun v =>
    !(safe_update_accept v v))) = true := by
  native_decide

-- PBT for rollback_protection_prop (decidable implication).
example : (testVersions.all (fun n => testVersions.all (fun c =>
    if n < c then !(safe_update_accept n c) else true))) = true := by
  native_decide

-- PBT for the complete Post_prop: the conjunction of all five checks.
example : (testVersions.all (fun n => testVersions.all (fun c =>
    (safe_update_accept n c == decide (c < n)) &&
    (if c < n then safe_update_accept n c else true) &&
    ((!(safe_update_accept n c)) == decide (n ≤ c)) &&
    (!(safe_update_accept c c)) &&
    (if n < c then !(safe_update_accept n c) else true)))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (new_version current_version : Int) :
    Pre new_version current_version → Post_prop new_version current_version := by sorry

/-! ## Imperative implementation -/

/-- Start in the rejecting state, and accept only a strictly newer version. -/
def safe_update_accept_imperative (new_version current_version : Int) : Bool :=
  Id.run do
    let mut accepted : Bool := false
    if new_version > current_version then
      accepted := true
    return accepted

/-! ## Imperative tests -/

example : safe_update_accept_imperative 5 3 = true := by native_decide
example : safe_update_accept_imperative 100 1 = true := by native_decide
example : safe_update_accept_imperative 2 1 = true := by native_decide
example : safe_update_accept_imperative 3 3 = false := by native_decide
example : safe_update_accept_imperative 1 5 = false := by native_decide
example : safe_update_accept_imperative 0 10 = false := by native_decide
example : safe_update_accept_imperative 9 10 = false := by native_decide
example : safe_update_accept_imperative 1 0 = true := by native_decide
example : safe_update_accept_imperative 0 0 = false := by native_decide
example : check safe_update_accept_imperative = true := by native_decide
example : safe_update_accept_imperative (-1) (-2) = true := by native_decide
example : safe_update_accept_imperative (-2) (-1) = false := by native_decide

#eval safe_update_accept_imperative 5 3
#eval safe_update_accept_imperative 1 5
#eval check safe_update_accept_imperative

/-! ## Functional/imperative equivalence -/

theorem equivalence_thm (new_version current_version : Int) :
    safe_update_accept new_version current_version =
      safe_update_accept_imperative new_version current_version := by sorry

end «37_unsafeRollback_safe»
end Agent
