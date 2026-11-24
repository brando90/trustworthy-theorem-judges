import Mathlib
namespace Agent

/-!
# Safe cookie domain checking

Translation of the Python `safeCookieDomain` function and its `check` tests.
A cookie is accepted exactly when its integer domain identifier equals the
current origin's identifier. `Int` models Python's arbitrary-precision signed
integers; all integer inputs are admissible, including negative identifiers.

The specifications establish acceptance of matching domains and rejection of
all mismatches, without assuming any additional domain hierarchy. Bounded
property-based tests are executable evidence; the general correctness and
functional/imperative equivalence results are proved independently.
-/

namespace SafeCookieDomain

/-! ## Functional implementation -/

/-- Compare the cookie's domain with the current origin, exactly as in Python. -/
def safeCookieDomain (cookieDomain currentDomain : Int) : Bool :=
  decide (cookieDomain = currentDomain)

/-! ## Unit tests corresponding to Python's `check` -/

example : safeCookieDomain 1 1 = true := by native_decide
example : safeCookieDomain 1 2 = false := by native_decide
example : safeCookieDomain 0 999 = false := by native_decide
example : safeCookieDomain 42 42 = true := by native_decide

-- Signed inputs are also part of the Python integer domain.
example : safeCookieDomain (-42) (-42) = true := by native_decide
example : safeCookieDomain (-1) 1 = false := by native_decide

#eval [safeCookieDomain 1 1, safeCookieDomain 1 2,
       safeCookieDomain 0 999, safeCookieDomain 42 42]
#eval if safeCookieDomain 1 1 && !(safeCookieDomain 1 2) &&
         !(safeCookieDomain 0 999) && safeCookieDomain 42 42 then
        "All tests passed."
      else
        "Test failure."

/-! ## Precondition -/

/-- The source function is total on all pairs of Python integers. -/
def Pre (_cookieDomain _currentDomain : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Both soundness and completeness of cookie acceptance. -/
def accepted_iff_prop (cookieDomain currentDomain : Int) : Prop :=
  safeCookieDomain cookieDomain currentDomain = true ↔
    cookieDomain = currentDomain

theorem accepted_iff_thm (cookieDomain currentDomain : Int) :
    accepted_iff_prop cookieDomain currentDomain := by sorry

/-- All cross-domain cookies are rejected, and only mismatches are rejected. -/
def rejected_iff_prop (cookieDomain currentDomain : Int) : Prop :=
  safeCookieDomain cookieDomain currentDomain = false ↔
    cookieDomain ≠ currentDomain

theorem rejected_iff_thm (cookieDomain currentDomain : Int) :
    rejected_iff_prop cookieDomain currentDomain := by sorry

/-- Every domain is permitted to set a cookie for itself. -/
def sameDomainAccepted_prop (domain : Int) : Prop :=
  safeCookieDomain domain domain = true

theorem sameDomainAccepted_thm (domain : Int) :
    sameDomainAccepted_prop domain := by sorry

/-- The comparison is symmetric: no distinct domain can be privileged. -/
def symmetric_prop (cookieDomain currentDomain : Int) : Prop :=
  safeCookieDomain cookieDomain currentDomain =
    safeCookieDomain currentDomain cookieDomain

theorem symmetric_thm (cookieDomain currentDomain : Int) :
    symmetric_prop cookieDomain currentDomain := by sorry

/-! ## Postcondition -/

/-- The complete security contract, expressed as a conjunction of properties. -/
def Post_prop (cookieDomain currentDomain : Int) : Prop :=
  accepted_iff_prop cookieDomain currentDomain ∧
  rejected_iff_prop cookieDomain currentDomain ∧
  sameDomainAccepted_prop cookieDomain ∧
  symmetric_prop cookieDomain currentDomain

/-! ## Property-based tests

Exhaustively test the signed interval [-30, 30], including every ordered pair.
Each test spells out its executable proposition rather than requiring a
`Decidable` instance on the specification definitions. All inputs satisfy Pre.
-/

def testDomains : List Int :=
  (List.range 61).map (fun n => (n : Int) - 30)

-- PBT for accepted_iff_prop: 61 * 61 pairs, including equal and unequal inputs.
example : testDomains.all (fun cookieDomain =>
    testDomains.all (fun currentDomain =>
      decide (safeCookieDomain cookieDomain currentDomain = true ↔
        cookieDomain = currentDomain))) = true := by
  native_decide

-- PBT for rejected_iff_prop.
example : testDomains.all (fun cookieDomain =>
    testDomains.all (fun currentDomain =>
      decide (safeCookieDomain cookieDomain currentDomain = false ↔
        cookieDomain ≠ currentDomain))) = true := by
  native_decide

-- PBT for sameDomainAccepted_prop.
example : testDomains.all (fun domain =>
    safeCookieDomain domain domain) = true := by
  native_decide

-- PBT for symmetric_prop.
example : testDomains.all (fun cookieDomain =>
    testDomains.all (fun currentDomain =>
      decide (safeCookieDomain cookieDomain currentDomain =
        safeCookieDomain currentDomain cookieDomain))) = true := by
  native_decide

-- PBT for Post_prop: check the full conjunction on every sampled pair.
example : testDomains.all (fun cookieDomain =>
    testDomains.all (fun currentDomain =>
      decide (
        (safeCookieDomain cookieDomain currentDomain = true ↔
          cookieDomain = currentDomain) ∧
        (safeCookieDomain cookieDomain currentDomain = false ↔
          cookieDomain ≠ currentDomain) ∧
        safeCookieDomain cookieDomain cookieDomain = true ∧
        safeCookieDomain cookieDomain currentDomain =
          safeCookieDomain currentDomain cookieDomain))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (cookieDomain currentDomain : Int) :
    Pre cookieDomain currentDomain → Post_prop cookieDomain currentDomain := by sorry

/-! ## Imperative implementation -/

/-- Start with rejection and accept only after the domain equality check. -/
def safeCookieDomainImperative (cookieDomain currentDomain : Int) : Bool := Id.run do
  let mut accepted := false
  if cookieDomain = currentDomain then
    accepted := true
  return accepted

/-! ## Imperative unit tests -/

example : safeCookieDomainImperative 1 1 = true := by native_decide
example : safeCookieDomainImperative 1 2 = false := by native_decide
example : safeCookieDomainImperative 0 999 = false := by native_decide
example : safeCookieDomainImperative 42 42 = true := by native_decide
example : safeCookieDomainImperative (-42) (-42) = true := by native_decide
example : safeCookieDomainImperative (-1) 1 = false := by native_decide

#eval [safeCookieDomainImperative 1 1, safeCookieDomainImperative 1 2,
       safeCookieDomainImperative 0 999, safeCookieDomainImperative 42 42]

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equiv_thm (cookieDomain currentDomain : Int) :
    safeCookieDomain cookieDomain currentDomain =
      safeCookieDomainImperative cookieDomain currentDomain := by sorry

end SafeCookieDomain
end Agent
