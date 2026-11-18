import Mathlib
namespace Agent

/-!
# Safe same-origin check

Translation of the Python same-origin guard from MIT 6.858 Lecture 12.
A request is allowed exactly when its origin equals the page's origin;
otherwise it is blocked. Python's arbitrary-precision integer inputs are
modeled by `Int`, including negative origins and zero, without restrictions.

The file includes the original tests, complete authorization specifications,
bounded property-based tests, kernel-checked proofs, and an equivalent
mutable-state implementation. Executable tests are evidence only and are
not used in any theorem proof.
-/

namespace UnsafeSameOriginSafe

/-- Allow a request if and only if its origin equals the page's origin. -/
def safe_same_origin (request_origin page_origin : Int) : Bool :=
  decide (request_origin = page_origin)

/-- Boolean counterpart of the five assertions in the Python test harness. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 100 100 &&
  !(candidate 100 200) &&
  !(candidate 0 999) &&
  candidate 0 0 &&
  !(candidate 42 43)

-- Original unit tests.
example : safe_same_origin 100 100 = true := by native_decide
example : safe_same_origin 100 200 = false := by native_decide
example : safe_same_origin 0 999 = false := by native_decide
example : safe_same_origin 0 0 = true := by native_decide
example : safe_same_origin 42 43 = false := by native_decide
example : check safe_same_origin = true := by native_decide

-- Additional tests ensure that origins are integers, not just naturals.
example : safe_same_origin (-42) (-42) = true := by native_decide
example : safe_same_origin (-42) 42 = false := by native_decide

#eval safe_same_origin 100 100
#eval safe_same_origin 100 200
#eval safe_same_origin 0 999
#eval safe_same_origin 0 0
#eval safe_same_origin 42 43
#eval check safe_same_origin
#eval if check safe_same_origin then "All tests passed." else "Candidate failed tests"

/-- The Python function accepts every pair of integers. -/
def Pre (_request_origin _page_origin : Int) : Prop := True

/-- Every same-origin request is allowed. -/
def same_origin_prop (request_origin page_origin : Int) : Prop :=
  request_origin = page_origin →
    safe_same_origin request_origin page_origin = true

theorem same_origin_thm (request_origin page_origin : Int) :
    same_origin_prop request_origin page_origin := by
  unfold same_origin_prop
  intro h
  simp [safe_same_origin, h]

/-- Every cross-origin request is blocked. -/
def cross_origin_prop (request_origin page_origin : Int) : Prop :=
  request_origin ≠ page_origin →
    safe_same_origin request_origin page_origin = false

theorem cross_origin_thm (request_origin page_origin : Int) :
    cross_origin_prop request_origin page_origin := by
  unfold cross_origin_prop
  intro h
  simp [safe_same_origin, h]

/-- Both Boolean outcomes precisely characterize equality or inequality. -/
def authorization_prop (request_origin page_origin : Int) : Prop :=
  (safe_same_origin request_origin page_origin = true ↔
    request_origin = page_origin) ∧
  (safe_same_origin request_origin page_origin = false ↔
    request_origin ≠ page_origin)

theorem authorization_thm (request_origin page_origin : Int) :
    authorization_prop request_origin page_origin := by
  simp [authorization_prop, safe_same_origin]

/-- Swapping the origins cannot change an equality check. -/
def symmetry_prop (request_origin page_origin : Int) : Prop :=
  safe_same_origin request_origin page_origin =
    safe_same_origin page_origin request_origin

theorem symmetry_thm (request_origin page_origin : Int) :
    symmetry_prop request_origin page_origin := by
  simp [symmetry_prop, safe_same_origin, eq_comm]

/-- The full same-origin policy, as a conjunction of its properties. -/
def Post_prop (request_origin page_origin : Int) : Prop :=
  same_origin_prop request_origin page_origin ∧
  cross_origin_prop request_origin page_origin ∧
  authorization_prop request_origin page_origin ∧
  symmetry_prop request_origin page_origin

/-!
## Bounded property-based tests

The Cartesian product of this domain is checked exhaustively. It contains
all integers from -20 through 20 and every origin in the Python tests.
The tests use executable Boolean forms directly; no `Decidable` instance
for the specification definitions is assumed. Implications are represented
by Boolean disjunction, and the authorization biconditionals by Boolean
equality. Both admissible equality and inequality cases are exercised.
-/

def testOrigins : List Int :=
  (List.range 41).map (fun n => (n : Int) - 20) ++ [100, 200, 999, 42, 43]

def allOriginPairs (test : Int → Int → Bool) : Bool :=
  testOrigins.all (fun request => testOrigins.all (fun page => test request page))

-- Executable form of same_origin_prop: equality implies acceptance.
def sameOriginTest (request page : Int) : Bool :=
  !(decide (request = page)) || safe_same_origin request page

-- Executable form of cross_origin_prop: inequality implies rejection.
def crossOriginTest (request page : Int) : Bool :=
  decide (request = page) || !(safe_same_origin request page)

-- Executable form of both biconditionals in authorization_prop.
def authorizationTest (request page : Int) : Bool :=
  (safe_same_origin request page == decide (request = page)) &&
  (!(safe_same_origin request page) == decide (request ≠ page))

-- Executable form of symmetry_prop.
def symmetryTest (request page : Int) : Bool :=
  safe_same_origin request page == safe_same_origin page request

-- Executable form of the entire Post_prop conjunction.
def postTest (request page : Int) : Bool :=
  sameOriginTest request page &&
  crossOriginTest request page &&
  authorizationTest request page &&
  symmetryTest request page

example : allOriginPairs sameOriginTest = true := by native_decide
example : allOriginPairs crossOriginTest = true := by native_decide
example : allOriginPairs authorizationTest = true := by native_decide
example : allOriginPairs symmetryTest = true := by native_decide
example : allOriginPairs postTest = true := by native_decide

#eval allOriginPairs sameOriginTest
#eval allOriginPairs crossOriginTest
#eval allOriginPairs authorizationTest
#eval allOriginPairs symmetryTest
#eval allOriginPairs postTest

/-- Correctness on the complete Python input domain. -/
theorem correctness_thm (request_origin page_origin : Int) :
    Pre request_origin page_origin → Post_prop request_origin page_origin := by
  intro _hpre
  exact ⟨same_origin_thm request_origin page_origin,
    cross_origin_thm request_origin page_origin,
    authorization_thm request_origin page_origin,
    symmetry_thm request_origin page_origin⟩

/-- Imperative guard: start blocked, and allow only after equality succeeds. -/
def safe_same_origin_imperative (request_origin page_origin : Int) : Bool := Id.run do
  let mut allowed := false
  if request_origin = page_origin then
    allowed := true
  return allowed

-- Imperative unit tests and the original harness.
example : safe_same_origin_imperative 100 100 = true := by native_decide
example : safe_same_origin_imperative 100 200 = false := by native_decide
example : safe_same_origin_imperative 0 999 = false := by native_decide
example : safe_same_origin_imperative 0 0 = true := by native_decide
example : safe_same_origin_imperative 42 43 = false := by native_decide
example : safe_same_origin_imperative (-42) (-42) = true := by native_decide
example : safe_same_origin_imperative (-42) 42 = false := by native_decide
example : check safe_same_origin_imperative = true := by native_decide

#eval safe_same_origin_imperative 100 100
#eval safe_same_origin_imperative 100 200
#eval check safe_same_origin_imperative

-- Bounded differential testing, in addition to the universal proof below.
example : allOriginPairs (fun request page =>
    safe_same_origin request page == safe_same_origin_imperative request page) = true := by
  native_decide

#eval allOriginPairs (fun request page =>
  safe_same_origin request page == safe_same_origin_imperative request page)

/-- Functional and mutable-state implementations agree for every integer pair. -/
theorem functional_imperative_equivalence_thm (request_origin page_origin : Int) :
    safe_same_origin request_origin page_origin =
      safe_same_origin_imperative request_origin page_origin := by
  by_cases h : request_origin = page_origin <;>
    simp [safe_same_origin, safe_same_origin_imperative, h]

end UnsafeSameOriginSafe
end Agent
