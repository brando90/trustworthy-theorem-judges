import Mathlib
namespace Agent

/-!
# Safe Tor circuit hop count

Translation of the Python predicate `safe_circuit_hops`: a circuit is accepted
exactly when its integer hop count is at least three. `Int` preserves Python's
unbounded integer domain, including negative inputs. No input restriction is
needed. The specification concerns this threshold check, not a proof of Tor's
network-level anonymity guarantees.

The file includes the original checks, exact acceptance/rejection properties,
monotonicity, bounded property-based tests, correctness, and equivalence with a
mutable-state implementation.
-/

namespace «40_unsafeCircuitHops_safe»

/-! ## Functional implementation -/

/-- Accept exactly the integer hop counts that meet the three-relay threshold. -/
def safe_circuit_hops (hop_count : Int) : Bool :=
  decide (3 ≤ hop_count)

/-- Executable counterpart of the Python `check` routine. -/
def check : IO Unit := do
  unless safe_circuit_hops 3 == true do
    throw (IO.userError "3-hop circuit rejected")
  unless safe_circuit_hops 5 == true do
    throw (IO.userError "5-hop circuit rejected")
  unless safe_circuit_hops 1 == false do
    throw (IO.userError "1-hop circuit accepted")
  unless safe_circuit_hops 2 == false do
    throw (IO.userError "2-hop circuit accepted")
  IO.println "All tests passed."

/-! ## Unit tests -/

example : safe_circuit_hops 3 = true := by native_decide
example : safe_circuit_hops 5 = true := by native_decide
example : safe_circuit_hops 1 = false := by native_decide
example : safe_circuit_hops 2 = false := by native_decide
example : safe_circuit_hops 0 = false := by native_decide
example : safe_circuit_hops (-7) = false := by native_decide

#eval check
#eval [safe_circuit_hops 3, safe_circuit_hops 5,
       safe_circuit_hops 1, safe_circuit_hops 2]

/-! ## Precondition and properties -/

/-- Every Python integer is an admissible input. -/
def Pre (_hop_count : Int) : Prop := True

/-- Acceptance is equivalent to meeting the threshold, in both directions. -/
def acceptance_prop (hop_count : Int) : Prop :=
  safe_circuit_hops hop_count = true ↔ 3 ≤ hop_count

theorem acceptance_thm (hop_count : Int) : acceptance_prop hop_count := by
  simp [acceptance_prop, safe_circuit_hops]

/-- Rejection occurs exactly below the threshold, including negative inputs. -/
def rejection_prop (hop_count : Int) : Prop :=
  safe_circuit_hops hop_count = false ↔ hop_count < 3

theorem rejection_thm (hop_count : Int) : rejection_prop hop_count := by
  simp [rejection_prop, safe_circuit_hops, not_le]

/-- Adding hops to an accepted circuit cannot make this predicate reject it. -/
def monotonicity_prop (hop_count : Int) : Prop :=
  ∀ larger : Int, hop_count ≤ larger →
    safe_circuit_hops hop_count = true → safe_circuit_hops larger = true

theorem monotonicity_thm (hop_count : Int) : monotonicity_prop hop_count := by
  intro larger hle hsafe
  apply (acceptance_thm larger).2
  exact le_trans ((acceptance_thm hop_count).1 hsafe) hle

/-! ## Postcondition -/

/-- Exact Boolean behavior together with preservation under increasing hops. -/
def Post_prop (hop_count : Int) : Prop :=
  acceptance_prop hop_count ∧ rejection_prop hop_count ∧
    monotonicity_prop hop_count

/-! ## Property-based tests

These bounded PBTs exhaust all integer inputs from -50 through 50. The
monotonicity test exhausts all pairs in this range. The postcondition test
checks the conjunction, sampling its universally quantified second input
through the same range. These are executable checks, not universal proofs.
-/

private def testHops : List Int :=
  (List.range 101).map (fun n => (n : Int) - 50)

-- PBT for acceptance_prop.
example : testHops.all (fun h =>
    decide (safe_circuit_hops h = true ↔ 3 ≤ h)) = true := by
  native_decide

-- PBT for rejection_prop.
example : testHops.all (fun h =>
    decide (safe_circuit_hops h = false ↔ h < 3)) = true := by
  native_decide

-- PBT for monotonicity_prop, with both integers varied independently.
example : testHops.all (fun h =>
    testHops.all (fun larger =>
      decide (h ≤ larger → safe_circuit_hops h = true →
        safe_circuit_hops larger = true))) = true := by
  native_decide

-- PBT for Post_prop: the executable conjunction of all three properties.
example : testHops.all (fun h =>
    decide (safe_circuit_hops h = true ↔ 3 ≤ h) &&
    decide (safe_circuit_hops h = false ↔ h < 3) &&
    testHops.all (fun larger =>
      decide (h ≤ larger → safe_circuit_hops h = true →
        safe_circuit_hops larger = true))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (hop_count : Int) :
    Pre hop_count → Post_prop hop_count := by
  intro _
  exact ⟨acceptance_thm hop_count, rejection_thm hop_count,
    monotonicity_thm hop_count⟩

/-! ## Imperative implementation -/

/-- The same decision expressed using mutable state in `Id.run`. -/
def safe_circuit_hops_imperative (hop_count : Int) : Bool := Id.run do
  let mut safe := false
  if 3 ≤ hop_count then
    safe := true
  return safe

/-! ## Imperative tests -/

example : safe_circuit_hops_imperative 3 = true := by native_decide
example : safe_circuit_hops_imperative 5 = true := by native_decide
example : safe_circuit_hops_imperative 1 = false := by native_decide
example : safe_circuit_hops_imperative 2 = false := by native_decide
example : safe_circuit_hops_imperative 0 = false := by native_decide
example : safe_circuit_hops_imperative (-7) = false := by native_decide

#eval [safe_circuit_hops_imperative 3, safe_circuit_hops_imperative 5,
       safe_circuit_hops_imperative 1, safe_circuit_hops_imperative 2]

/-! ## Functional-imperative equivalence -/

theorem functional_imperative_equivalence_thm :
    safe_circuit_hops = safe_circuit_hops_imperative := by
  funext hop_count
  by_cases h : 3 ≤ hop_count <;>
    simp [safe_circuit_hops, safe_circuit_hops_imperative, h]

end «40_unsafeCircuitHops_safe»
end Agent
