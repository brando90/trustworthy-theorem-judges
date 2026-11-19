import Mathlib
namespace Agent

/-!
# Safe Same-Origin Policy check

Translation of the Python `safe_sop_check` from MIT 6.858 Quiz 1, Spring 2017.
A request is permitted exactly when its origin string equals the allowed origin
string. There is no URL parsing, case folding, default-port normalization, or
special treatment of empty strings: every pair of strings is admissible.

The file contains the functional implementation, the original tests, universal
policy proofs, bounded exhaustive property-based tests, and an equivalent
mutable-state implementation. Tests are evidence only; the named theorems use
kernel-checked proofs, not native decision procedures.
-/

namespace UnsafeSameOriginCheckSafe

/-! ## Functional implementation -/

/-- Exact, case-sensitive string equality, as in the Python implementation. -/
def safe_sop_check (request_origin allowed_origin : String) : Bool :=
  request_origin == allowed_origin

/-! ## Unit tests and the Python test driver -/

example : safe_sop_check "https://example.com" "https://example.com" = true := by
  native_decide

example : safe_sop_check "https://evil.com" "https://example.com" = false := by
  native_decide

example : safe_sop_check "" "https://example.com" = false := by
  native_decide

example : safe_sop_check "https://example.com" "https://example.com:8080" = false := by
  native_decide

-- Equality, rather than origin validity or normalization, is the entire policy.
example : safe_sop_check "" "" = true := by native_decide
example : safe_sop_check "https://EXAMPLE.com" "https://example.com" = false := by
  native_decide
example : safe_sop_check "https://example.com:443" "https://example.com" = false := by
  native_decide

#eval safe_sop_check "https://example.com" "https://example.com"
#eval safe_sop_check "https://evil.com" "https://example.com"
#eval safe_sop_check "" "https://example.com"
#eval safe_sop_check "https://example.com" "https://example.com:8080"

/-- The original four assertions and success message, expressed as an IO check. -/
def check : IO Unit := do
  unless safe_sop_check "https://example.com" "https://example.com" do
    throw (IO.userError "same origin rejected")
  if safe_sop_check "https://evil.com" "https://example.com" then
    throw (IO.userError "cross-origin accepted")
  if safe_sop_check "" "https://example.com" then
    throw (IO.userError "empty origin accepted")
  if safe_sop_check "https://example.com" "https://example.com:8080" then
    throw (IO.userError "port mismatch accepted")
  IO.println "All tests passed."

def main : IO Unit := check

#eval main

/-! ## Pre-condition -/

/-- Python accepts all string pairs, including empty strings and non-URLs. -/
def Pre (_request_origin _allowed_origin : String) : Prop := True

/-! ## Policy properties and their proofs -/

/-- Acceptance is both sound and complete for exact string equality. -/
def acceptance_prop (request_origin allowed_origin : String) : Prop :=
  safe_sop_check request_origin allowed_origin = true ↔ request_origin = allowed_origin

theorem acceptance_thm (request_origin allowed_origin : String) :
    acceptance_prop request_origin allowed_origin := by
  simp [acceptance_prop, safe_sop_check]

/-- Every mismatch is rejected, and a rejection implies a mismatch. -/
def rejection_prop (request_origin allowed_origin : String) : Prop :=
  safe_sop_check request_origin allowed_origin = false ↔ request_origin ≠ allowed_origin

theorem rejection_thm (request_origin allowed_origin : String) :
    rejection_prop request_origin allowed_origin := by
  simp [rejection_prop, safe_sop_check]

/-- An origin always matches itself; this includes the empty string. -/
def reflexivity_prop (origin : String) : Prop :=
  safe_sop_check origin origin = true

theorem reflexivity_thm (origin : String) : reflexivity_prop origin := by
  simp [reflexivity_prop, safe_sop_check]

/-- Swapping the two strings cannot change their equality result. -/
def symmetry_prop (request_origin allowed_origin : String) : Prop :=
  safe_sop_check request_origin allowed_origin = safe_sop_check allowed_origin request_origin

theorem symmetry_thm (request_origin allowed_origin : String) :
    symmetry_prop request_origin allowed_origin := by
  by_cases h : request_origin = allowed_origin
  · subst allowed_origin
    rfl
  · have h' : allowed_origin ≠ request_origin := Ne.symm h
    simp [symmetry_prop, safe_sop_check, h, h']

/-! ## Post-condition -/

/-- The exact acceptance/rejection contract, together with its symmetry. -/
def Post_prop (request_origin allowed_origin : String) : Prop :=
  acceptance_prop request_origin allowed_origin ∧
  rejection_prop request_origin allowed_origin ∧
  symmetry_prop request_origin allowed_origin

/-! ## Bounded property-based tests

Each test exhausts the indicated sample space, not merely a single example.
The corpus includes the original inputs, case and scheme changes, explicit
ports, trailing slashes, whitespace, non-URLs, Unicode, and generated hosts.
All pairs are admissible because `Pre` is `True`. The tests use Boolean forms
of the properties, without requiring decidability instances for the named
propositions. They are separate from all universal theorem proofs.
-/

def originSamples : List String :=
  ["", "https://example.com", "https://evil.com", "https://example.com:8080",
   "https://example.com:443", "http://example.com", "https://EXAMPLE.com",
   "HTTPS://example.com", "https://example.com/", "https://example.com.",
   "https://example.com/path", " https://example.com", "https://example.com ",
   "null", "not an origin", "https://例子.com", "https://éxample.com"] ++
  (List.range 16).flatMap (fun n =>
    ["https://host" ++ toString n ++ ".example",
     "http://host" ++ toString n ++ ".example",
     "https://host" ++ toString n ++ ".example:8080"])

/-- Exhaust all ordered pairs of the bounded origin corpus. -/
def allOriginPairs (test : String → String → Bool) : Bool :=
  originSamples.all (fun request_origin =>
    originSamples.all (fun allowed_origin => test request_origin allowed_origin))

-- PBT for acceptance_prop: accepted iff the strings are equal.
example : allOriginPairs (fun r a =>
    (safe_sop_check r a == true) == decide (r = a)) = true := by
  native_decide

-- PBT for rejection_prop: rejected iff the strings differ.
example : allOriginPairs (fun r a =>
    (safe_sop_check r a == false) == decide (r ≠ a)) = true := by
  native_decide

-- PBT for reflexivity_prop, over every sampled string (including "").
example : originSamples.all (fun r => safe_sop_check r r) = true := by
  native_decide

-- PBT for symmetry_prop, including both matches and mismatches.
example : allOriginPairs (fun r a =>
    safe_sop_check r a == safe_sop_check a r) = true := by
  native_decide

-- PBT for the entire Post_prop conjunction.
example : allOriginPairs (fun r a =>
    (((safe_sop_check r a == true) == decide (r = a)) &&
     ((safe_sop_check r a == false) == decide (r ≠ a))) &&
     (safe_sop_check r a == safe_sop_check a r)) = true := by
  native_decide

#eval originSamples.length
#eval allOriginPairs (fun r a =>
  (((safe_sop_check r a == true) == decide (r = a)) &&
   ((safe_sop_check r a == false) == decide (r ≠ a))) &&
   (safe_sop_check r a == safe_sop_check a r))

/-! ## Correctness -/

theorem correctness_thm (request_origin allowed_origin : String) :
    Pre request_origin allowed_origin → Post_prop request_origin allowed_origin := by
  intro _
  exact ⟨acceptance_thm request_origin allowed_origin,
    rejection_thm request_origin allowed_origin,
    symmetry_thm request_origin allowed_origin⟩

/-! ## Imperative implementation -/

/-- Start denied; change the mutable result to permitted only on an exact match. -/
def safe_sop_check_imperative (request_origin allowed_origin : String) : Bool := Id.run do
  let mut permitted := false
  if request_origin == allowed_origin then
    permitted := true
  return permitted

/-! ## Imperative tests -/

example : safe_sop_check_imperative "https://example.com" "https://example.com" = true := by
  native_decide
example : safe_sop_check_imperative "https://evil.com" "https://example.com" = false := by
  native_decide
example : safe_sop_check_imperative "" "https://example.com" = false := by
  native_decide
example : safe_sop_check_imperative "https://example.com" "https://example.com:8080" = false := by
  native_decide
example : safe_sop_check_imperative "" "" = true := by native_decide

#eval safe_sop_check_imperative "https://example.com" "https://example.com"
#eval safe_sop_check_imperative "https://evil.com" "https://example.com"
#eval safe_sop_check_imperative "" "https://example.com"
#eval safe_sop_check_imperative "https://example.com" "https://example.com:8080"

-- Bounded cross-check of the two implementations over all sampled pairs.
example : allOriginPairs (fun r a =>
    safe_sop_check r a == safe_sop_check_imperative r a) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem equivalence_thm (request_origin allowed_origin : String) :
    safe_sop_check request_origin allowed_origin =
      safe_sop_check_imperative request_origin allowed_origin := by
  cases h : (request_origin == allowed_origin) <;>
    simp [safe_sop_check, safe_sop_check_imperative, h]

end UnsafeSameOriginCheckSafe
end Agent
