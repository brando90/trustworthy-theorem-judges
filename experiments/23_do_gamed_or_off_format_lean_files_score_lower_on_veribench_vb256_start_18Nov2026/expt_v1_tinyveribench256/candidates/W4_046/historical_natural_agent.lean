import Mathlib
namespace Agent

/-!
# Safe sandbox status validation

Translation of `safe_sandbox_status` from the Python RLBox sandboxing example
(MIT 6.858, Lecture 08). A status is accepted exactly when it belongs to the
closed interval given by the two bounds. `Int` models Python's arbitrary-size
signed integers. There is no assumption that the bounds are ordered: reversed
bounds reject every status. The tests are executable evidence; all named
specification, correctness, and equivalence theorems have kernel-checked proofs.
-/

namespace UnsafeSandboxStatusSafe

/-! ## Functional implementation -/

def safe_sandbox_status (status_code min_valid max_valid : Int) : Bool :=
  decide (min_valid ≤ status_code ∧ status_code ≤ max_valid)

/-! ## Unit tests and the Python test driver -/

example : safe_sandbox_status 5 0 10 = true := by native_decide
example : safe_sandbox_status 0 0 10 = true := by native_decide
example : safe_sandbox_status 10 0 10 = true := by native_decide
example : safe_sandbox_status 11 0 10 = false := by native_decide
example : safe_sandbox_status 0 5 10 = false := by native_decide

-- Additional signed, singleton, and reversed-bound examples.
example : safe_sandbox_status (-5) (-10) (-1) = true := by native_decide
example : safe_sandbox_status (-3) (-3) (-3) = true := by native_decide
example : safe_sandbox_status 5 10 0 = false := by native_decide

def check : IO Unit := do
  unless safe_sandbox_status 5 0 10 do
    throw (IO.userError "valid code ok")
  unless safe_sandbox_status 0 0 10 do
    throw (IO.userError "lower bound ok")
  unless safe_sandbox_status 10 0 10 do
    throw (IO.userError "upper bound ok")
  if safe_sandbox_status 11 0 10 then
    throw (IO.userError "above max blocked")
  if safe_sandbox_status 0 5 10 then
    throw (IO.userError "below min blocked")
  IO.println "All tests passed."

#eval check
#eval safe_sandbox_status 5 0 10
#eval safe_sandbox_status 11 0 10

/-! ## Pre-condition -/

-- Python accepts all integer triples, including empty/reversed intervals.
def Pre (_status_code _min_valid _max_valid : Int) : Prop := True

/-! ## Specification properties and proofs -/

/-- Exact acceptance: both comparisons must hold, and that is sufficient. -/
def acceptance_prop (status_code min_valid max_valid : Int) : Prop :=
  safe_sandbox_status status_code min_valid max_valid = true ↔
    min_valid ≤ status_code ∧ status_code ≤ max_valid

theorem acceptance_thm (status_code min_valid max_valid : Int) :
    acceptance_prop status_code min_valid max_valid := by
  simp [acceptance_prop, safe_sandbox_status]

/-- Exact rejection: a violation of either bound, and only that, is rejected. -/
def rejection_prop (status_code min_valid max_valid : Int) : Prop :=
  safe_sandbox_status status_code min_valid max_valid = false ↔
    status_code < min_valid ∨ max_valid < status_code

theorem rejection_thm (status_code min_valid max_valid : Int) :
    rejection_prop status_code min_valid max_valid := by
  unfold rejection_prop safe_sandbox_status
  simp only [decide_eq_false_iff_not]
  omega

/-- The lower endpoint is included whenever the interval is nonempty. -/
def lower_bound_prop (min_valid max_valid : Int) : Prop :=
  min_valid ≤ max_valid → safe_sandbox_status min_valid min_valid max_valid = true

theorem lower_bound_thm (min_valid max_valid : Int) :
    lower_bound_prop min_valid max_valid := by
  intro h
  exact (acceptance_thm min_valid min_valid max_valid).2 ⟨le_rfl, h⟩

/-- The upper endpoint is also included, including singleton intervals. -/
def upper_bound_prop (min_valid max_valid : Int) : Prop :=
  min_valid ≤ max_valid → safe_sandbox_status max_valid min_valid max_valid = true

theorem upper_bound_thm (min_valid max_valid : Int) :
    upper_bound_prop min_valid max_valid := by
  intro h
  exact (acceptance_thm max_valid min_valid max_valid).2 ⟨h, le_rfl⟩

/-- Reversing the bounds cannot accidentally authorize a status. -/
def reversed_bounds_prop (status_code min_valid max_valid : Int) : Prop :=
  max_valid < min_valid → safe_sandbox_status status_code min_valid max_valid = false

theorem reversed_bounds_thm (status_code min_valid max_valid : Int) :
    reversed_bounds_prop status_code min_valid max_valid := by
  intro h
  apply (rejection_thm status_code min_valid max_valid).2
  omega

/-! ## Post-condition -/

def Post_prop (status_code min_valid max_valid : Int) : Prop :=
  acceptance_prop status_code min_valid max_valid ∧
  rejection_prop status_code min_valid max_valid ∧
  lower_bound_prop min_valid max_valid ∧
  upper_bound_prop min_valid max_valid ∧
  reversed_bounds_prop status_code min_valid max_valid

/-! ## Property-based tests

Exhaustive small-domain tests cover every integer from -12 through 12, so they
include negative statuses, endpoints, singleton intervals, and reversed bounds.
Each test below uses the property's executable Boolean form directly, without
requiring a Decidable instance for the named specification definitions. The
implications in endpoint/empty-interval properties are Boolean implications.
-/

def pbtInts : List Int := (List.range 25).map (fun n => (n : Int) - 12)

def allPairs (p : Int → Int → Bool) : Bool :=
  pbtInts.all (fun lo => pbtInts.all (fun hi => p lo hi))

def allTriples (p : Int → Int → Int → Bool) : Bool :=
  pbtInts.all (fun status =>
    pbtInts.all (fun lo => pbtInts.all (fun hi => p status lo hi)))

-- PBT for acceptance_prop: 25^3 triples.
example : allTriples (fun status lo hi =>
    safe_sandbox_status status lo hi == decide (lo ≤ status ∧ status ≤ hi)) = true := by
  native_decide

-- PBT for rejection_prop: 25^3 triples.
example : allTriples (fun status lo hi =>
    (!safe_sandbox_status status lo hi) == decide (status < lo ∨ hi < status)) = true := by
  native_decide

-- PBT for lower_bound_prop: all 25^2 endpoint pairs.
example : allPairs (fun lo hi =>
    (!decide (lo ≤ hi)) || safe_sandbox_status lo lo hi) = true := by
  native_decide

-- PBT for upper_bound_prop: all 25^2 endpoint pairs.
example : allPairs (fun lo hi =>
    (!decide (lo ≤ hi)) || safe_sandbox_status hi lo hi) = true := by
  native_decide

-- PBT for reversed_bounds_prop: 25^3 triples, including all empty intervals.
example : allTriples (fun status lo hi =>
    (!decide (hi < lo)) || (!safe_sandbox_status status lo hi)) = true := by
  native_decide

-- PBT for Post_prop: the conjunction of all five executable properties.
example : allTriples (fun status lo hi =>
    (safe_sandbox_status status lo hi == decide (lo ≤ status ∧ status ≤ hi)) &&
    ((!safe_sandbox_status status lo hi) == decide (status < lo ∨ hi < status)) &&
    ((!decide (lo ≤ hi)) || safe_sandbox_status lo lo hi) &&
    ((!decide (lo ≤ hi)) || safe_sandbox_status hi lo hi) &&
    ((!decide (hi < lo)) || (!safe_sandbox_status status lo hi))) = true := by
  native_decide

#eval allTriples (fun status lo hi =>
  safe_sandbox_status status lo hi == decide (lo ≤ status ∧ status ≤ hi))

/-! ## Correctness -/

theorem correctness_thm (status_code min_valid max_valid : Int) :
    Pre status_code min_valid max_valid → Post_prop status_code min_valid max_valid := by
  intro _
  exact ⟨acceptance_thm status_code min_valid max_valid,
    rejection_thm status_code min_valid max_valid,
    lower_bound_thm min_valid max_valid,
    upper_bound_thm min_valid max_valid,
    reversed_bounds_thm status_code min_valid max_valid⟩

/-! ## Imperative implementation

Start in the rejected state, then authorize only after both checks succeed.
The second comparison is reached only if the first comparison succeeds.
-/

def safe_sandbox_status_imperative (status_code min_valid max_valid : Int) : Bool := Id.run do
  let mut accepted := false
  if min_valid ≤ status_code then
    if status_code ≤ max_valid then
      accepted := true
  return accepted

/-! ## Imperative tests -/

example : safe_sandbox_status_imperative 5 0 10 = true := by native_decide
example : safe_sandbox_status_imperative 0 0 10 = true := by native_decide
example : safe_sandbox_status_imperative 10 0 10 = true := by native_decide
example : safe_sandbox_status_imperative 11 0 10 = false := by native_decide
example : safe_sandbox_status_imperative 0 5 10 = false := by native_decide
example : safe_sandbox_status_imperative (-5) (-10) (-1) = true := by native_decide
example : safe_sandbox_status_imperative 5 10 0 = false := by native_decide

#eval [safe_sandbox_status_imperative 5 0 10,
  safe_sandbox_status_imperative 0 0 10,
  safe_sandbox_status_imperative 10 0 10,
  safe_sandbox_status_imperative 11 0 10,
  safe_sandbox_status_imperative 0 5 10]

-- Additional bounded differential test; the general proof follows below.
example : allTriples (fun status lo hi =>
    safe_sandbox_status status lo hi == safe_sandbox_status_imperative status lo hi) = true := by
  native_decide

/-! ## Functional-imperative equivalence -/

theorem functional_imperative_equivalence_thm (status_code min_valid max_valid : Int) :
    safe_sandbox_status status_code min_valid max_valid =
      safe_sandbox_status_imperative status_code min_valid max_valid := by
  by_cases hlo : min_valid ≤ status_code <;>
    by_cases hhi : status_code ≤ max_valid <;>
    simp [safe_sandbox_status, safe_sandbox_status_imperative, hlo, hhi]

end UnsafeSandboxStatusSafe
end Agent
