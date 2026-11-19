import Mathlib
namespace Agent

/-!
# Safe UID isolation

Translation of Python's `safe_uid_access` and its six-case check harness.
Access is granted exactly when the requester and owner UIDs coincide. In
particular, UID zero has no override: it can access only resources owned by zero.
`Int` preserves the full Python integer domain, including negative inputs.
The examples and bounded property-based tests are executable evidence; all named
security, correctness, and equivalence theorems have kernel-checked proofs.
-/

namespace UnsafeUidIsolationSafe

/-! ## Functional implementation and the source check harness -/

def safe_uid_access (requester_uid owner_uid : Int) : Bool :=
  decide (requester_uid = owner_uid)

/-- Boolean counterpart of the six assertions in the Python test harness. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 10042 10042 &&
  !(candidate 10043 10042) &&
  candidate 0 0 &&
  !(candidate 0 10042) &&
  !(candidate 10042 0) &&
  !(candidate 1 9999)

/-! ## Unit tests -/

example : safe_uid_access 10042 10042 = true := by native_decide
example : safe_uid_access 10043 10042 = false := by native_decide
example : safe_uid_access 0 0 = true := by native_decide
example : safe_uid_access 0 10042 = false := by native_decide
example : safe_uid_access 10042 0 = false := by native_decide
example : safe_uid_access 1 9999 = false := by native_decide
example : check safe_uid_access = true := by native_decide

#eval [safe_uid_access 10042 10042, safe_uid_access 10043 10042,
  safe_uid_access 0 0, safe_uid_access 0 10042,
  safe_uid_access 10042 0, safe_uid_access 1 9999]
#eval check safe_uid_access

/-! ## Precondition and security properties -/

/-- The source function has no restrictions on its integer arguments. -/
def Pre (_requester_uid _owner_uid : Int) : Prop := True

/-- Exact authorization semantics, in both directions. -/
def access_iff_uid_match_prop (requester_uid owner_uid : Int) : Prop :=
  safe_uid_access requester_uid owner_uid = true ↔ requester_uid = owner_uid

theorem access_iff_uid_match_thm (requester_uid owner_uid : Int) :
    access_iff_uid_match_prop requester_uid owner_uid := by
  simp [access_iff_uid_match_prop, safe_uid_access]

/-- Exact denial semantics, in both directions. -/
def denied_iff_uid_mismatch_prop (requester_uid owner_uid : Int) : Prop :=
  safe_uid_access requester_uid owner_uid = false ↔ requester_uid ≠ owner_uid

theorem denied_iff_uid_mismatch_thm (requester_uid owner_uid : Int) :
    denied_iff_uid_mismatch_prop requester_uid owner_uid := by
  simp [denied_iff_uid_mismatch_prop, safe_uid_access]

/-- An owner is always allowed to access its own resource. -/
def same_uid_allowed_prop (uid : Int) : Prop :=
  safe_uid_access uid uid = true

theorem same_uid_allowed_thm (uid : Int) : same_uid_allowed_prop uid := by
  simp [same_uid_allowed_prop, safe_uid_access]

/-- Distinct UIDs cannot access each other's private resources. -/
def different_uid_denied_prop (requester_uid owner_uid : Int) : Prop :=
  requester_uid ≠ owner_uid → safe_uid_access requester_uid owner_uid = false

theorem different_uid_denied_thm (requester_uid owner_uid : Int) :
    different_uid_denied_prop requester_uid owner_uid := by
  intro h
  simp [safe_uid_access, h]

/-- Equality-based authorization is symmetric in the two UIDs. -/
def access_symmetry_prop (requester_uid owner_uid : Int) : Prop :=
  safe_uid_access requester_uid owner_uid = safe_uid_access owner_uid requester_uid

theorem access_symmetry_thm (requester_uid owner_uid : Int) :
    access_symmetry_prop requester_uid owner_uid := by
  simp [access_symmetry_prop, safe_uid_access, eq_comm]

/-- The Python policy makes no exception for root in either position. -/
def root_no_bypass_prop (uid : Int) : Prop :=
  uid ≠ 0 → safe_uid_access 0 uid = false ∧ safe_uid_access uid 0 = false

theorem root_no_bypass_thm (uid : Int) : root_no_bypass_prop uid := by
  intro h
  have h' : (0 : Int) ≠ uid := Ne.symm h
  simp [safe_uid_access, h, h']

/-! ## Postcondition -/

def Post_prop (requester_uid owner_uid : Int) : Prop :=
  access_iff_uid_match_prop requester_uid owner_uid ∧
  denied_iff_uid_mismatch_prop requester_uid owner_uid ∧
  same_uid_allowed_prop owner_uid ∧
  different_uid_denied_prop requester_uid owner_uid ∧
  access_symmetry_prop requester_uid owner_uid ∧
  root_no_bypass_prop owner_uid

/-! ## Property-based tests

Exhaustive bounded tests cover each property and their postcondition conjunction.
The sample domain includes every integer from -16 through 16, as well as the
large UIDs used by the source harness. The checks below spell out executable
forms directly rather than requiring Decidable instances for the named Props.
-/

def testUIDs : List Int :=
  (List.range 33).map (fun n => (n : Int) - 16) ++ [9999, 10042, 10043]

-- PBT: access_iff_uid_match_prop.
example : testUIDs.all (fun r => testUIDs.all (fun o =>
    decide (safe_uid_access r o = true ↔ r = o))) = true := by
  native_decide

-- PBT: denied_iff_uid_mismatch_prop.
example : testUIDs.all (fun r => testUIDs.all (fun o =>
    decide (safe_uid_access r o = false ↔ r ≠ o))) = true := by
  native_decide

-- PBT: same_uid_allowed_prop.
example : testUIDs.all (fun uid => safe_uid_access uid uid) = true := by
  native_decide

-- PBT: different_uid_denied_prop.
example : testUIDs.all (fun r => testUIDs.all (fun o =>
    decide (r ≠ o → safe_uid_access r o = false))) = true := by
  native_decide

-- PBT: access_symmetry_prop.
example : testUIDs.all (fun r => testUIDs.all (fun o =>
    decide (safe_uid_access r o = safe_uid_access o r))) = true := by
  native_decide

-- PBT: root_no_bypass_prop (zero itself is covered by same_uid_allowed_prop).
example : testUIDs.all (fun uid =>
    decide (uid ≠ 0 → safe_uid_access 0 uid = false ∧
      safe_uid_access uid 0 = false)) = true := by
  native_decide

-- PBT: the complete Post_prop, with its conjunction expanded executably.
example : testUIDs.all (fun r => testUIDs.all (fun o => decide (
    (safe_uid_access r o = true ↔ r = o) ∧
    (safe_uid_access r o = false ↔ r ≠ o) ∧
    safe_uid_access o o = true ∧
    (r ≠ o → safe_uid_access r o = false) ∧
    safe_uid_access r o = safe_uid_access o r ∧
    (o ≠ 0 → safe_uid_access 0 o = false ∧
      safe_uid_access o 0 = false)))) = true := by
  native_decide

-- An additional randomized check of the central authorization property.
#eval Plausible.Testable.check (∀ r o : Int,
  safe_uid_access r o = true ↔ r = o)

/-! ## Correctness -/

theorem safe_uid_access_correct (requester_uid owner_uid : Int) :
    Pre requester_uid owner_uid → Post_prop requester_uid owner_uid := by
  intro _
  exact ⟨access_iff_uid_match_thm requester_uid owner_uid,
    denied_iff_uid_mismatch_thm requester_uid owner_uid,
    same_uid_allowed_thm owner_uid,
    different_uid_denied_thm requester_uid owner_uid,
    access_symmetry_thm requester_uid owner_uid,
    root_no_bypass_thm owner_uid⟩

/-! ## Imperative implementation -/

/-- Start with denial and grant access only after the ownership check succeeds. -/
def safe_uid_access_imperative (requester_uid owner_uid : Int) : Bool := Id.run do
  let mut allowed := false
  if requester_uid = owner_uid then
    allowed := true
  return allowed

/-! ## Imperative tests -/

example : safe_uid_access_imperative 10042 10042 = true := by native_decide
example : safe_uid_access_imperative 10043 10042 = false := by native_decide
example : safe_uid_access_imperative 0 0 = true := by native_decide
example : safe_uid_access_imperative 0 10042 = false := by native_decide
example : safe_uid_access_imperative 10042 0 = false := by native_decide
example : safe_uid_access_imperative 1 9999 = false := by native_decide
example : check safe_uid_access_imperative = true := by native_decide

#eval [safe_uid_access_imperative 10042 10042,
  safe_uid_access_imperative 10043 10042, safe_uid_access_imperative 0 0,
  safe_uid_access_imperative 0 10042, safe_uid_access_imperative 10042 0,
  safe_uid_access_imperative 1 9999]
#eval check safe_uid_access_imperative

-- Bounded equivalence test, including negative UIDs.
example : testUIDs.all (fun r => testUIDs.all (fun o =>
    decide (safe_uid_access r o = safe_uid_access_imperative r o))) = true := by
  native_decide

/-! ## Functional / imperative equivalence -/

theorem safe_uid_access_equiv_thm (requester_uid owner_uid : Int) :
    safe_uid_access requester_uid owner_uid =
      safe_uid_access_imperative requester_uid owner_uid := by
  by_cases h : requester_uid = owner_uid <;>
    simp [safe_uid_access, safe_uid_access_imperative, h]

theorem safe_uid_access_function_eq_thm :
    safe_uid_access = safe_uid_access_imperative := by
  funext requester_uid owner_uid
  exact safe_uid_access_equiv_thm requester_uid owner_uid

end UnsafeUidIsolationSafe
end Agent
