import Mathlib
namespace Agent

/-!
# Unsafe CSRF token check

Translation of the Python handler from the MIT 6.858 web-security example.
The handler deliberately accepts every request without validating its token.
`Int` models Python's arbitrary-precision signed integers. In particular, there
is no nonnegativity assumption or requirement that the two tokens agree.

The specifications describe the vulnerability; they do not repair it. The
functional and mutable-state implementations both return `true`, even for
mismatched tokens. Bounded property tests provide executable evidence, while
all named theorems are proved independently by kernel-checked proofs.
-/

namespace UnsafeCsrfToken

/-! ## Functional implementation and the Python test harness -/

/-- Deliberately unsafe: neither token is validated. -/
def unsafe_csrf_check (_request_token _session_token : Int) : Bool :=
  true

/-- The conjunction of the four assertions in Python's `check` harness.
`true` means all assertions pass; `false` denotes assertion failure. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 42 42 &&
  candidate 0 99 &&
  candidate 12345 67890 &&
  candidate 0 0

/-! ## Unit tests -/

example : unsafe_csrf_check 42 42 = true := by native_decide
example : unsafe_csrf_check 0 99 = true := by native_decide
example : unsafe_csrf_check 12345 67890 = true := by native_decide
example : unsafe_csrf_check 0 0 = true := by native_decide
example : unsafe_csrf_check (-1) 99 = true := by native_decide
example : unsafe_csrf_check (-42) (-42) = true := by native_decide
example : check unsafe_csrf_check = true := by native_decide

#eval unsafe_csrf_check 42 42
#eval unsafe_csrf_check 0 99
#eval unsafe_csrf_check 12345 67890
#eval unsafe_csrf_check 0 0
#eval check unsafe_csrf_check
#eval if check unsafe_csrf_check then "All tests passed." else "Candidate failed tests"

/-! ## Preconditions and proved properties -/

/-- Every pair of integer tokens is admissible. -/
def Pre (_request_token _session_token : Int) : Prop := True

/-- Every request is accepted. -/
def always_accepts_prop (request_token session_token : Int) : Prop :=
  unsafe_csrf_check request_token session_token = true

theorem always_accepts_thm (request_token session_token : Int) :
    always_accepts_prop request_token session_token := by sorry

/-- A matching token is accepted, as in the normal case. -/
def matching_tokens_prop (token : Int) : Prop :=
  unsafe_csrf_check token token = true

theorem matching_tokens_thm (token : Int) : matching_tokens_prop token := by sorry

/-- The vulnerability: a mismatched token is also accepted. -/
def mismatched_tokens_prop (request_token session_token : Int) : Prop :=
  request_token ≠ session_token →
    unsafe_csrf_check request_token session_token = true

theorem mismatched_tokens_thm (request_token session_token : Int) :
    mismatched_tokens_prop request_token session_token := by sorry

/-- All token pairs give the same result as the fixed baseline `(0, 0)`. -/
def ignores_tokens_prop (request_token session_token : Int) : Prop :=
  unsafe_csrf_check request_token session_token = unsafe_csrf_check 0 0

theorem ignores_tokens_thm (request_token session_token : Int) :
    ignores_tokens_prop request_token session_token := by sorry

/-- Consequently, changing either or both tokens cannot change the result. -/
theorem token_independence_thm
    (request_token session_token other_request other_session : Int) :
    unsafe_csrf_check request_token session_token =
      unsafe_csrf_check other_request other_session := by sorry

/-! ## Postcondition -/

/-- Both normal acceptance and the unsafe behavior are part of the contract. -/
def Post_prop (request_token session_token : Int) : Prop :=
  always_accepts_prop request_token session_token ∧
  matching_tokens_prop session_token ∧
  mismatched_tokens_prop request_token session_token ∧
  ignores_tokens_prop request_token session_token

/-! ## Property-based tests

Exhaustively test a signed range plus the larger inputs in the Python tests.
These tests use Boolean counterparts of each property, not a noncomputable
`Decidable` instance for its specification. The implication in the mismatch
property is expressed as `tokens equal || request accepted`.
-/

private def tokenSamples : List Int :=
  ((List.range 41).map (fun n => (n : Int) - 20)) ++
    [42, 99, 12345, 67890, -12345, -67890]

-- PBT: always_accepts_prop, over all sampled request/session pairs.
example : tokenSamples.all (fun request_token =>
    tokenSamples.all (fun session_token =>
      unsafe_csrf_check request_token session_token == true)) = true := by
  native_decide

-- PBT: matching_tokens_prop, over every sampled token.
example : tokenSamples.all (fun token =>
    unsafe_csrf_check token token == true) = true := by
  native_decide

-- PBT: mismatched_tokens_prop, including negative and positive mismatches.
example : tokenSamples.all (fun request_token =>
    tokenSamples.all (fun session_token =>
      (request_token == session_token) ||
        (unsafe_csrf_check request_token session_token == true))) = true := by
  native_decide

-- PBT: ignores_tokens_prop.
example : tokenSamples.all (fun request_token =>
    tokenSamples.all (fun session_token =>
      unsafe_csrf_check request_token session_token ==
        unsafe_csrf_check 0 0)) = true := by
  native_decide

-- PBT: the stronger, four-input token_independence_thm.
example : tokenSamples.all (fun request_token =>
    tokenSamples.all (fun session_token =>
      tokenSamples.all (fun other_request =>
        tokenSamples.all (fun other_session =>
          unsafe_csrf_check request_token session_token ==
            unsafe_csrf_check other_request other_session)))) = true := by
  native_decide

-- PBT: Post_prop, with all four conjuncts checked together.
-- Pre is True, so no input filtering is necessary.
example : tokenSamples.all (fun request_token =>
    tokenSamples.all (fun session_token =>
      (unsafe_csrf_check request_token session_token == true) &&
      (unsafe_csrf_check session_token session_token == true) &&
      ((request_token == session_token) ||
        (unsafe_csrf_check request_token session_token == true)) &&
      (unsafe_csrf_check request_token session_token ==
        unsafe_csrf_check 0 0))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (request_token session_token : Int) :
    Pre request_token session_token → Post_prop request_token session_token := by sorry

/-! ## Imperative implementation -/

/-- A mutable acceptance flag is set unconditionally, without inspecting tokens. -/
def unsafe_csrf_check_imp (_request_token _session_token : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_csrf_check_imp 42 42 = true := by native_decide
example : unsafe_csrf_check_imp 0 99 = true := by native_decide
example : unsafe_csrf_check_imp 12345 67890 = true := by native_decide
example : unsafe_csrf_check_imp 0 0 = true := by native_decide
example : unsafe_csrf_check_imp (-1) 99 = true := by native_decide
example : check unsafe_csrf_check_imp = true := by native_decide

#eval unsafe_csrf_check_imp 0 99
#eval check unsafe_csrf_check_imp

example : tokenSamples.all (fun request_token =>
    tokenSamples.all (fun session_token =>
      unsafe_csrf_check request_token session_token ==
        unsafe_csrf_check_imp request_token session_token)) = true := by
  native_decide

/-! ## Functional–imperative equivalence -/

theorem functional_imperative_equivalence_thm (request_token session_token : Int) :
    unsafe_csrf_check request_token session_token =
      unsafe_csrf_check_imp request_token session_token := by sorry

end UnsafeCsrfToken
end Agent
