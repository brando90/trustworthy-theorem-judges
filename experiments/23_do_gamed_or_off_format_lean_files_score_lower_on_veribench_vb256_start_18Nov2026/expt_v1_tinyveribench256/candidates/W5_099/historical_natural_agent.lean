import Mathlib
namespace Agent

/-!
# Unsafe Same-Origin Policy check

A translation of the Python `unsafe_sop_check` and its test runner
(MIT 6.858 Quiz 1, Spring 2017). The function deliberately ignores both
origin strings and returns `true`. This file verifies that unsafe behavior;
it does not repair the implementation or claim that it enforces SOP.

All strings are admissible, including empty and malformed origins. A proper
exact-string comparison agrees with this implementation exactly on matching
origins. The proofs are kernel-checked; `native_decide` is used only for tests.
-/

namespace «143_unsafeSameOriginCheck»

/-! ## Functional implementation -/

/-- Faithful to Python: no parsing, normalization, or comparison is performed. -/
def unsafe_sop_check (_request_origin _allowed_origin : String) : Bool :=
  true

/-! ## Unit tests and the Python test runner -/

example : unsafe_sop_check "https://example.com" "https://example.com" = true := by
  native_decide

example : unsafe_sop_check "https://evil.com" "https://example.com" = true := by
  native_decide

example : unsafe_sop_check "" "https://example.com" = true := by
  native_decide

/-- The three Python assertions, with their original failure messages. -/
def check : IO Unit := do
  unless unsafe_sop_check "https://example.com" "https://example.com" do
    throw (IO.userError "same origin rejected")
  unless unsafe_sop_check "https://evil.com" "https://example.com" do
    throw (IO.userError "vuln: cross-origin accepted")
  unless unsafe_sop_check "" "https://example.com" do
    throw (IO.userError "vuln: empty origin accepted")
  IO.println "All tests passed."

#eval unsafe_sop_check "https://example.com" "https://example.com"
#eval unsafe_sop_check "https://evil.com" "https://example.com"
#eval unsafe_sop_check "" "https://example.com"
#eval check

/-! ## Precondition -/

/-- The Python function imposes no restrictions on either origin string. -/
def Pre (_request_origin _allowed_origin : String) : Prop := True

/-! ## Properties and proofs -/

def always_accepts_prop (request_origin allowed_origin : String) : Prop :=
  unsafe_sop_check request_origin allowed_origin = true

theorem always_accepts_thm (request_origin allowed_origin : String) :
    always_accepts_prop request_origin allowed_origin := by
  rfl

def same_origin_prop (origin : String) : Prop :=
  unsafe_sop_check origin origin = true

theorem same_origin_thm (origin : String) : same_origin_prop origin := by
  rfl

/-- Cross-origin requests are accepted, not rejected: this is the vulnerability. -/
def cross_origin_prop (request_origin allowed_origin : String) : Prop :=
  request_origin ≠ allowed_origin →
    unsafe_sop_check request_origin allowed_origin = true

theorem cross_origin_thm (request_origin allowed_origin : String) :
    cross_origin_prop request_origin allowed_origin := by
  intro _
  rfl

def empty_origin_prop (allowed_origin : String) : Prop :=
  unsafe_sop_check "" allowed_origin = true

theorem empty_origin_thm (allowed_origin : String) :
    empty_origin_prop allowed_origin := by
  rfl

/-- Changing either or both inputs has no effect on the returned Boolean. -/
def input_independence_prop (request_origin allowed_origin : String) : Prop :=
  ∀ request_origin' allowed_origin' : String,
    unsafe_sop_check request_origin allowed_origin =
      unsafe_sop_check request_origin' allowed_origin'

theorem input_independence_thm (request_origin allowed_origin : String) :
    input_independence_prop request_origin allowed_origin := by
  intro request_origin' allowed_origin'
  rfl

/-- Agreement with a proper exact-origin comparison occurs iff the inputs match.
In particular, the unsafe check disagrees with that comparison on every mismatch. -/
def exact_match_agreement_prop (request_origin allowed_origin : String) : Prop :=
  (unsafe_sop_check request_origin allowed_origin = (request_origin == allowed_origin)) ↔
    request_origin = allowed_origin

theorem exact_match_agreement_thm (request_origin allowed_origin : String) :
    exact_match_agreement_prop request_origin allowed_origin := by
  by_cases h : request_origin = allowed_origin <;>
    simp [exact_match_agreement_prop, unsafe_sop_check, h]

/-! ## Postcondition -/

/-- A behavioral contract for the unsafe program, not a security guarantee. -/
def Post_prop (request_origin allowed_origin : String) : Prop :=
  always_accepts_prop request_origin allowed_origin ∧
  same_origin_prop allowed_origin ∧
  cross_origin_prop request_origin allowed_origin ∧
  empty_origin_prop allowed_origin ∧
  input_independence_prop request_origin allowed_origin ∧
  exact_match_agreement_prop request_origin allowed_origin

/-! ## Bounded property-based tests

The corpus contains empty, matching, mismatching, malformed, case/port/path
variants, Unicode, and twelve generated origins. Each binary property is
checked on all 24 × 24 pairs; input independence is checked on all 24^4
quadruples. These finite tests do not restrict any theorem's string domain.
The checks use executable Booleans rather than decidability of the Props.
-/

def pbtOrigins : List String :=
  ["", "https://example.com", "https://evil.com", "http://example.com",
   "https://EXAMPLE.com", "https://example.com:443", "https://example.com/",
   "null", "file://", "https://例.example", " https://example.com", "not an origin"] ++
  (List.range 12).map (fun n => s!"https://host{n}.example")

-- PBT for always_accepts_prop.
example : pbtOrigins.all (fun request =>
    pbtOrigins.all (fun allowed => unsafe_sop_check request allowed)) = true := by
  native_decide

-- PBT for same_origin_prop.
example : pbtOrigins.all (fun origin => unsafe_sop_check origin origin) = true := by
  native_decide

-- PBT for cross_origin_prop: (request ≠ allowed → accepted) as a Boolean.
example : pbtOrigins.all (fun request => pbtOrigins.all (fun allowed =>
    (request == allowed) || unsafe_sop_check request allowed)) = true := by
  native_decide

-- PBT for empty_origin_prop, varying the allowed origin.
example : pbtOrigins.all (fun allowed => unsafe_sop_check "" allowed) = true := by
  native_decide

-- PBT for input_independence_prop, varying all four strings independently.
example : pbtOrigins.all (fun request => pbtOrigins.all (fun allowed =>
    pbtOrigins.all (fun request' => pbtOrigins.all (fun allowed' =>
      unsafe_sop_check request allowed == unsafe_sop_check request' allowed')))) = true := by
  native_decide

-- PBT for exact_match_agreement_prop: Boolean equality encodes the iff.
example : pbtOrigins.all (fun request => pbtOrigins.all (fun allowed =>
    (unsafe_sop_check request allowed == (request == allowed)) ==
      (request == allowed))) = true := by
  native_decide

/-- Executable bounded form of Post_prop. Its universal input-independence
conjunct is sampled over the same corpus, without changing the specification. -/
def sampledPostCheck (request allowed : String) : Bool :=
  unsafe_sop_check request allowed &&
  unsafe_sop_check allowed allowed &&
  ((request == allowed) || unsafe_sop_check request allowed) &&
  unsafe_sop_check "" allowed &&
  (pbtOrigins.all (fun request' => pbtOrigins.all (fun allowed' =>
    unsafe_sop_check request allowed == unsafe_sop_check request' allowed'))) &&
  ((unsafe_sop_check request allowed == (request == allowed)) == (request == allowed))

-- PBT for the entire postcondition. Pre is True, so no inputs are filtered out.
example : pbtOrigins.all (fun request =>
    pbtOrigins.all (fun allowed => sampledPostCheck request allowed)) = true := by
  native_decide

#eval pbtOrigins.all (fun request =>
  pbtOrigins.all (fun allowed => sampledPostCheck request allowed))

/-! ## Correctness relative to the unsafe behavioral specification -/

theorem correctness_thm (request_origin allowed_origin : String) :
    Pre request_origin allowed_origin → Post_prop request_origin allowed_origin := by
  intro _
  exact ⟨always_accepts_thm request_origin allowed_origin,
    same_origin_thm allowed_origin,
    cross_origin_thm request_origin allowed_origin,
    empty_origin_thm allowed_origin,
    input_independence_thm request_origin allowed_origin,
    exact_match_agreement_thm request_origin allowed_origin⟩

/-! ## Imperative implementation -/

/-- An unconditional assignment models the Python return using mutable state. -/
def unsafe_sop_check_imperative (_request_origin _allowed_origin : String) : Bool :=
  Id.run do
    let mut accepted := false
    accepted := true
    return accepted

/-! ## Imperative tests -/

example : unsafe_sop_check_imperative "https://example.com" "https://example.com" = true := by
  native_decide

example : unsafe_sop_check_imperative "https://evil.com" "https://example.com" = true := by
  native_decide

example : unsafe_sop_check_imperative "" "https://example.com" = true := by
  native_decide

#eval unsafe_sop_check_imperative "https://example.com" "https://example.com"
#eval unsafe_sop_check_imperative "https://evil.com" "https://example.com"
#eval unsafe_sop_check_imperative "" "https://example.com"

-- Additional bounded equivalence test, independent of the proof below.
example : pbtOrigins.all (fun request => pbtOrigins.all (fun allowed =>
    unsafe_sop_check request allowed == unsafe_sop_check_imperative request allowed)) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (request_origin allowed_origin : String) :
    unsafe_sop_check request_origin allowed_origin =
      unsafe_sop_check_imperative request_origin allowed_origin := by
  rfl

end «143_unsafeSameOriginCheck»
end Agent
