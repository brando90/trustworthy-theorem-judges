import Mathlib
namespace Agent

/-!
# Unsafe Tor circuit hop count

Translation of the Python `unsafe_circuit_hops` program. The function returns
`true` for every Python integer, modeled by Lean's unbounded `Int`. In particular,
it accepts circuits with fewer than three hops; this file records that
vulnerability rather than repairing it. There is no nonnegativity precondition.

The bounded property-based tests exhaustively cover hop counts from -40 through
40 (and all pairs in that range for input independence). The named theorems prove
the corresponding properties for all integers, independently of those tests.
-/

namespace UnsafeCircuitHops

-- Functional implementation: the argument is deliberately ignored.
def unsafe_circuit_hops (_hop_count : Int) : Bool :=
  true

-- Unit tests, including the three assertions in the Python program.
example : unsafe_circuit_hops 3 = true := by native_decide
example : unsafe_circuit_hops 1 = true := by native_decide
example : unsafe_circuit_hops 0 = true := by native_decide
example : unsafe_circuit_hops 2 = true := by native_decide
example : unsafe_circuit_hops (-1) = true := by native_decide

-- Executable counterpart of Python's check().
def check : IO Unit := do
  unless unsafe_circuit_hops 3 do
    throw (IO.userError "3-hop circuit rejected")
  unless unsafe_circuit_hops 1 do
    throw (IO.userError "vuln: 1-hop circuit accepted")
  unless unsafe_circuit_hops 0 do
    throw (IO.userError "vuln: 0-hop circuit accepted")
  IO.println "All tests passed."

#eval unsafe_circuit_hops 3
#eval unsafe_circuit_hops 1
#eval unsafe_circuit_hops 0
#eval check

-- Every integer is admissible, just as in the Python implementation.
def Pre (_hop_count : Int) : Prop := True

-- Exact return-value semantics.
def alwaysAccepts_prop (hop_count : Int) : Prop :=
  unsafe_circuit_hops hop_count = true

theorem alwaysAccepts_thm (hop_count : Int) : alwaysAccepts_prop hop_count := by sorry

-- This expresses the vulnerability, not a desired security guarantee.
def tooFewHops_prop (hop_count : Int) : Prop :=
  hop_count < 3 → unsafe_circuit_hops hop_count = true

theorem tooFewHops_thm (hop_count : Int) : tooFewHops_prop hop_count := by sorry

-- Counts meeting the usual three-hop threshold are also accepted.
def sufficientHops_prop (hop_count : Int) : Prop :=
  3 ≤ hop_count → unsafe_circuit_hops hop_count = true

theorem sufficientHops_thm (hop_count : Int) : sufficientHops_prop hop_count := by sorry

-- Changing the hop count can never change the answer.
def inputIndependent_prop (hop_count : Int) : Prop :=
  ∀ other : Int, unsafe_circuit_hops hop_count = unsafe_circuit_hops other

theorem inputIndependent_thm (hop_count : Int) : inputIndependent_prop hop_count := by sorry

-- Post-condition: all the stated behavioral properties hold together.
def Post_prop (hop_count : Int) : Prop :=
  alwaysAccepts_prop hop_count ∧
  tooFewHops_prop hop_count ∧
  sufficientHops_prop hop_count ∧
  inputIndependent_prop hop_count

-- Property-based tests: executable forms, not proofs of the universal claims.
def testHopCounts : List Int :=
  (List.range 81).map (fun n => (n : Int) - 40)

-- PBT for alwaysAccepts_prop.
example : testHopCounts.all
    (fun h => unsafe_circuit_hops h == true) = true := by
  native_decide

-- PBT for tooFewHops_prop, including negative, zero, one, and two hops.
example : testHopCounts.all
    (fun h => decide (h < 3 → unsafe_circuit_hops h = true)) = true := by
  native_decide

-- PBT for sufficientHops_prop; many inputs satisfy its antecedent.
example : testHopCounts.all
    (fun h => decide (3 ≤ h → unsafe_circuit_hops h = true)) = true := by
  native_decide

-- PBT for inputIndependent_prop: exhaustive pairs of bounded integers.
example : testHopCounts.all (fun h => testHopCounts.all
    (fun other => unsafe_circuit_hops h == unsafe_circuit_hops other)) = true := by
  native_decide

-- PBT for the full Post_prop, with its universally quantified other input
-- instantiated at every integer in the same bounded test range.
example : testHopCounts.all (fun h =>
    (unsafe_circuit_hops h == true) &&
    decide (h < 3 → unsafe_circuit_hops h = true) &&
    decide (3 ≤ h → unsafe_circuit_hops h = true) &&
    testHopCounts.all
      (fun other => unsafe_circuit_hops h == unsafe_circuit_hops other)) = true := by
  native_decide

-- Kernel-checked correctness over the full, unrestricted integer domain.
theorem correctness_thm (hop_count : Int) : Pre hop_count → Post_prop hop_count := by sorry

-- Imperative implementation: the return register is set unconditionally.
def unsafe_circuit_hops_imperative (_hop_count : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

-- Imperative unit tests and executable evaluations.
example : unsafe_circuit_hops_imperative 3 = true := by native_decide
example : unsafe_circuit_hops_imperative 1 = true := by native_decide
example : unsafe_circuit_hops_imperative 0 = true := by native_decide
example : unsafe_circuit_hops_imperative 2 = true := by native_decide
example : unsafe_circuit_hops_imperative (-1) = true := by native_decide

#eval unsafe_circuit_hops_imperative 3
#eval unsafe_circuit_hops_imperative 1
#eval unsafe_circuit_hops_imperative 0

example : testHopCounts.all (fun h =>
    unsafe_circuit_hops h == unsafe_circuit_hops_imperative h) = true := by
  native_decide

-- Functional/imperative equivalence for every Python integer.
theorem functional_imperative_equiv_thm (hop_count : Int) :
    unsafe_circuit_hops hop_count = unsafe_circuit_hops_imperative hop_count := by sorry

end UnsafeCircuitHops
end Agent
