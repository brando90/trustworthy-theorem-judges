import Mathlib
namespace Agent

/-!
# Safe ARP response handling

Translation of the Python `safe_arp_response` and its checks. Python integers
are modeled by unbounded signed `Int` values; there is no restriction to
nonnegative values or to a fixed-width IP representation. The Boolean result
is true exactly when the response IP equals the requested IP.

The specifications describe this equality check only: they do not claim that
checking an IP address authenticates the sender or rules out every ARP attack.
-/

namespace SafeArpResponse

/-- Accept exactly those responses whose IP equals the expected IP. -/
def safe_arp_response (response_ip expected_ip : Int) : Bool :=
  decide (response_ip = expected_ip)

-- Unit tests corresponding to the three assertions in Python's `check`.
example : safe_arp_response 10 10 = true := by native_decide
example : safe_arp_response 99 10 = false := by native_decide
example : safe_arp_response 0 1 = false := by native_decide

-- Signed inputs are also in the original Python function's domain.
example : safe_arp_response (-10) (-10) = true := by native_decide
example : safe_arp_response (-1) 1 = false := by native_decide

#eval safe_arp_response 10 10
#eval safe_arp_response 99 10
#eval safe_arp_response 0 1

/-- Executable counterpart of the Python test driver. -/
def check : IO Unit := do
  unless safe_arp_response 10 10 do
    throw (IO.userError "valid IP rejected")
  if safe_arp_response 99 10 then
    throw (IO.userError "spoofed IP accepted")
  if safe_arp_response 0 1 then
    throw (IO.userError "zero IP vs 1 accepted")
  IO.println "All tests passed."

#eval check

/-- Every pair of Python integers is admissible. -/
def Pre (_response_ip _expected_ip : Int) : Prop := True

/-- Both soundness of acceptance and completeness for matching addresses. -/
def acceptance_prop (response_ip expected_ip : Int) : Prop :=
  safe_arp_response response_ip expected_ip = true ↔ response_ip = expected_ip

theorem acceptance_thm (response_ip expected_ip : Int) :
    acceptance_prop response_ip expected_ip := by
  simp [acceptance_prop, safe_arp_response]

/-- Mismatches are rejected, and a matching address is never rejected. -/
def rejection_prop (response_ip expected_ip : Int) : Prop :=
  safe_arp_response response_ip expected_ip = false ↔ response_ip ≠ expected_ip

theorem rejection_thm (response_ip expected_ip : Int) :
    rejection_prop response_ip expected_ip := by
  simp [rejection_prop, safe_arp_response]

/-- The complete Boolean behavior of the equality check. -/
def Post_prop (response_ip expected_ip : Int) : Prop :=
  acceptance_prop response_ip expected_ip ∧
  rejection_prop response_ip expected_ip

/-!
## Property-based tests

Exhaustively test all 1681 ordered pairs from [-20, 20]. These cover negative,
zero, and positive inputs, including both equality and inequality. The checks
use executable forms of the specifications, without requiring Decidable
instances for the named Prop definitions. They are evidence only; the theorems
above and below prove the properties for all integers.
-/

private def testIPs : List Int :=
  (List.range 41).map (fun n => (n : Int) - 20)

-- PBT for acceptance_prop.
example :
    (testIPs.all fun response_ip =>
      testIPs.all fun expected_ip =>
        decide (safe_arp_response response_ip expected_ip = true ↔
          response_ip = expected_ip)) = true := by
  native_decide

-- PBT for rejection_prop.
example :
    (testIPs.all fun response_ip =>
      testIPs.all fun expected_ip =>
        decide (safe_arp_response response_ip expected_ip = false ↔
          response_ip ≠ expected_ip)) = true := by
  native_decide

-- PBT for Post_prop, checking the conjunction on every pair.
example :
    (testIPs.all fun response_ip =>
      testIPs.all fun expected_ip =>
        decide ((safe_arp_response response_ip expected_ip = true ↔
            response_ip = expected_ip) ∧
          (safe_arp_response response_ip expected_ip = false ↔
            response_ip ≠ expected_ip))) = true := by
  native_decide

/-- Total correctness under the unrestricted input precondition. -/
theorem correctness_thm (response_ip expected_ip : Int) :
    Pre response_ip expected_ip → Post_prop response_ip expected_ip := by
  intro _
  exact ⟨acceptance_thm response_ip expected_ip,
    rejection_thm response_ip expected_ip⟩

/-- Imperative implementation, with a mutable acceptance flag. -/
def safe_arp_response_imperative (response_ip expected_ip : Int) : Bool := Id.run do
  let mut accepted := false
  if response_ip = expected_ip then
    accepted := true
  return accepted

-- Imperative unit tests, including the original three assertions.
example : safe_arp_response_imperative 10 10 = true := by native_decide
example : safe_arp_response_imperative 99 10 = false := by native_decide
example : safe_arp_response_imperative 0 1 = false := by native_decide
example : safe_arp_response_imperative (-10) (-10) = true := by native_decide
example : safe_arp_response_imperative (-1) 1 = false := by native_decide

#eval safe_arp_response_imperative 10 10
#eval safe_arp_response_imperative 99 10
#eval safe_arp_response_imperative 0 1

-- Additional bounded test of functional/imperative agreement.
example :
    (testIPs.all fun response_ip =>
      testIPs.all fun expected_ip =>
        safe_arp_response response_ip expected_ip ==
          safe_arp_response_imperative response_ip expected_ip) = true := by
  native_decide

/-- The two implementations agree on every pair of signed integers. -/
theorem equivalence_thm (response_ip expected_ip : Int) :
    safe_arp_response response_ip expected_ip =
      safe_arp_response_imperative response_ip expected_ip := by
  by_cases h : response_ip = expected_ip <;>
    simp [safe_arp_response, safe_arp_response_imperative, h]

end SafeArpResponse
end Agent
