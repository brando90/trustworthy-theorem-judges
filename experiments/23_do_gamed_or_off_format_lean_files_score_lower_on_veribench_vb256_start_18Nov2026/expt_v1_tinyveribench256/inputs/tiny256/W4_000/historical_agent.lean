import Mathlib
namespace Agent

/-!
# Safe TLS MAC verification

Translation of the Python `safe_mac_verify` function and its test suite.
Python integers are modeled by Lean `Int`, including negative and arbitrarily
large values. Verification accepts exactly when the two MAC values agree.
The security guarantee here is rejection of a mismatched MAC; this comparison
alone makes no claim that a cryptographic MAC is collision-free.

All named theorems have kernel-checked proofs. Native evaluation is used only
for executable tests, independently of the proofs.
-/

namespace UnsafeMacVerifySafe

/-! ## Functional implementation -/

/-- Return true exactly when the computed and received MACs agree. -/
def safe_mac_verify (computed_mac received_mac : Int) : Bool :=
  decide (computed_mac = received_mac)

/-- Executable counterpart of all eight assertions in the Python test harness. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 12345 12345 &&
  candidate 0 0 &&
  candidate 99999 99999 &&
  !(candidate 12345 54321) &&
  !(candidate 100 200) &&
  !(candidate 0 1) &&
  candidate 999 999 &&
  !(candidate 999 998)

/-! ## Unit tests -/

example : safe_mac_verify 12345 12345 = true := by native_decide
example : safe_mac_verify 0 0 = true := by native_decide
example : safe_mac_verify 99999 99999 = true := by native_decide
example : safe_mac_verify 12345 54321 = false := by native_decide
example : safe_mac_verify 100 200 = false := by native_decide
example : safe_mac_verify 0 1 = false := by native_decide
example : safe_mac_verify 999 999 = true := by native_decide
example : safe_mac_verify 999 998 = false := by native_decide
example : check safe_mac_verify = true := by native_decide

-- Additional tests exercise the full signed, unbounded integer model.
example : safe_mac_verify (-12345) (-12345) = true := by native_decide
example : safe_mac_verify (-1) 1 = false := by native_decide
example : safe_mac_verify (2 ^ 100) (2 ^ 100) = true := by native_decide
example : safe_mac_verify (2 ^ 100) (2 ^ 100 + 1) = false := by native_decide

#eval safe_mac_verify 12345 12345
#eval safe_mac_verify 12345 54321
#eval check safe_mac_verify
#eval if check safe_mac_verify then "All tests passed." else "Test failure."

/-! ## Preconditions and proved properties -/

/-- Every pair of Python integers is admissible. -/
def Pre (_computed_mac _received_mac : Int) : Prop := True

/-- Acceptance is equivalent to equality, not merely implied by it. -/
def acceptance_prop (computed_mac received_mac : Int) : Prop :=
  safe_mac_verify computed_mac received_mac = true ↔ computed_mac = received_mac

theorem acceptance_thm (computed_mac received_mac : Int) :
    acceptance_prop computed_mac received_mac := by
  simp [acceptance_prop, safe_mac_verify]

/-- Rejection is equivalent to a mismatch. -/
def rejection_prop (computed_mac received_mac : Int) : Prop :=
  safe_mac_verify computed_mac received_mac = false ↔ computed_mac ≠ received_mac

theorem rejection_thm (computed_mac received_mac : Int) :
    rejection_prop computed_mac received_mac := by
  simp [rejection_prop, safe_mac_verify]

/-- Matching MACs are always accepted. -/
def matching_macs_prop (mac : Int) : Prop :=
  safe_mac_verify mac mac = true

theorem matching_macs_thm (mac : Int) : matching_macs_prop mac := by
  simp [matching_macs_prop, safe_mac_verify]

/-- A MAC mismatch, including one caused by tampering, is always rejected. -/
def mismatched_macs_prop (computed_mac received_mac : Int) : Prop :=
  computed_mac ≠ received_mac → safe_mac_verify computed_mac received_mac = false

theorem mismatched_macs_thm (computed_mac received_mac : Int) :
    mismatched_macs_prop computed_mac received_mac := by
  unfold mismatched_macs_prop
  intro h
  simp [safe_mac_verify, h]

/-! ## Postcondition -/

/-- Exact verification behavior and its matching/mismatch consequences. -/
def Post_prop (computed_mac received_mac : Int) : Prop :=
  acceptance_prop computed_mac received_mac ∧
  rejection_prop computed_mac received_mac ∧
  matching_macs_prop computed_mac ∧
  mismatched_macs_prop computed_mac received_mac

/-! ## Property-based tests

Exhaustively check every pair from [-30, 30], with additional larger signed
values. These are executable forms of each property, not proofs of the
universal statements. No domain restriction is imposed on the theorems.
-/

def macSamples : List Int :=
  (List.range 61).map (fun n => (n : Int) - 30) ++
    [-99999, -12345, 12345, 99999]

-- PBT for acceptance_prop.
example :
    macSamples.all (fun computed =>
      macSamples.all (fun received =>
        decide (safe_mac_verify computed received = true ↔ computed = received))) = true := by
  native_decide

-- PBT for rejection_prop.
example :
    macSamples.all (fun computed =>
      macSamples.all (fun received =>
        decide (safe_mac_verify computed received = false ↔ computed ≠ received))) = true := by
  native_decide

-- PBT for matching_macs_prop.
example : macSamples.all (fun mac => safe_mac_verify mac mac) = true := by
  native_decide

-- PBT for mismatched_macs_prop.
example :
    macSamples.all (fun computed =>
      macSamples.all (fun received =>
        decide (computed ≠ received → safe_mac_verify computed received = false))) = true := by
  native_decide

-- PBT for Post_prop: test the complete conjunction in executable form.
example :
    macSamples.all (fun computed =>
      macSamples.all (fun received =>
        decide (
          (safe_mac_verify computed received = true ↔ computed = received) ∧
          (safe_mac_verify computed received = false ↔ computed ≠ received) ∧
          safe_mac_verify computed computed = true ∧
          (computed ≠ received → safe_mac_verify computed received = false)))) = true := by
  native_decide

/-! ## Functional correctness -/

theorem correctness_thm (computed_mac received_mac : Int) :
    Pre computed_mac received_mac → Post_prop computed_mac received_mac := by
  intro _hPre
  exact ⟨acceptance_thm computed_mac received_mac,
    rejection_thm computed_mac received_mac,
    matching_macs_thm computed_mac,
    mismatched_macs_thm computed_mac received_mac⟩

/-! ## Imperative implementation -/

/-- Start with rejection, setting the mutable result only for matching MACs. -/
def safe_mac_verify_imperative (computed_mac received_mac : Int) : Bool := Id.run do
  let mut valid := false
  if computed_mac = received_mac then
    valid := true
  return valid

/-! ## Imperative tests -/

example : safe_mac_verify_imperative 12345 12345 = true := by native_decide
example : safe_mac_verify_imperative 0 0 = true := by native_decide
example : safe_mac_verify_imperative 99999 99999 = true := by native_decide
example : safe_mac_verify_imperative 12345 54321 = false := by native_decide
example : safe_mac_verify_imperative 100 200 = false := by native_decide
example : safe_mac_verify_imperative 0 1 = false := by native_decide
example : safe_mac_verify_imperative 999 999 = true := by native_decide
example : safe_mac_verify_imperative 999 998 = false := by native_decide
example : check safe_mac_verify_imperative = true := by native_decide
example : safe_mac_verify_imperative (-1) (-1) = true := by native_decide
example : safe_mac_verify_imperative (-1) 1 = false := by native_decide

#eval check safe_mac_verify_imperative
#eval safe_mac_verify_imperative 999 998

-- Bounded cross-implementation test, separate from the universal proof below.
example :
    macSamples.all (fun computed =>
      macSamples.all (fun received =>
        safe_mac_verify computed received ==
          safe_mac_verify_imperative computed received)) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (computed_mac received_mac : Int) :
    safe_mac_verify computed_mac received_mac =
      safe_mac_verify_imperative computed_mac received_mac := by
  by_cases h : computed_mac = received_mac <;>
    simp [safe_mac_verify, safe_mac_verify_imperative, h]

end UnsafeMacVerifySafe
end Agent
