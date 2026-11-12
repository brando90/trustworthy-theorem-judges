import Mathlib

/-!
# Safe same-origin check

This file formalizes a same-origin policy check that accepts a request exactly
when its origin string is identical to the allowed origin string.  It includes
the executable examples from the Python program, a functional specification,
an imperative implementation, and a proof that the two implementations agree.
-/

namespace UnsafeSameOriginCheckSafe

/-- Accept a request exactly when its origin equals the allowed origin. -/
def safeSopCheck (requestOrigin allowedOrigin : String) : Bool :=
  requestOrigin == allowedOrigin

example : safeSopCheck "https://example.com" "https://example.com" = true := by
  native_decide

example : safeSopCheck "https://evil.com" "https://example.com" = false := by
  native_decide

example : safeSopCheck "" "https://example.com" = false := by
  native_decide

example : safeSopCheck "https://example.com" "https://example.com:8080" = false := by
  native_decide

#eval safeSopCheck "https://example.com" "https://example.com"
#eval safeSopCheck "https://evil.com" "https://example.com"
#eval safeSopCheck "" "https://example.com"
#eval safeSopCheck "https://example.com" "https://example.com:8080"

/-- The check is defined for every pair of origin strings. -/
def Pre (_requestOrigin _allowedOrigin : String) : Prop :=
  True

/-- An origin is accepted if it exactly matches the allowed origin. -/
def acceptsExactMatch_prop (requestOrigin allowedOrigin : String) : Prop :=
  requestOrigin = allowedOrigin → safeSopCheck requestOrigin allowedOrigin = true

theorem acceptsExactMatch_thm (requestOrigin allowedOrigin : String) :
    acceptsExactMatch_prop requestOrigin allowedOrigin := by
  intro h
  simp [safeSopCheck, h]

/-- An origin is rejected if it differs from the allowed origin. -/
def rejectsMismatch_prop (requestOrigin allowedOrigin : String) : Prop :=
  requestOrigin ≠ allowedOrigin → safeSopCheck requestOrigin allowedOrigin = false

theorem rejectsMismatch_thm (requestOrigin allowedOrigin : String) :
    rejectsMismatch_prop requestOrigin allowedOrigin := by
  intro h
  simp [safeSopCheck, h]

/-- Acceptance precisely characterizes equality of the two origins. -/
def exactCharacterization_prop (requestOrigin allowedOrigin : String) : Prop :=
  safeSopCheck requestOrigin allowedOrigin = true ↔ requestOrigin = allowedOrigin

theorem exactCharacterization_thm (requestOrigin allowedOrigin : String) :
    exactCharacterization_prop requestOrigin allowedOrigin := by
  simp [exactCharacterization_prop, safeSopCheck]

/-- The complete post-condition combines exact acceptance and safe rejection. -/
def Post_prop (requestOrigin allowedOrigin : String) : Prop :=
  acceptsExactMatch_prop requestOrigin allowedOrigin ∧
    rejectsMismatch_prop requestOrigin allowedOrigin ∧
      exactCharacterization_prop requestOrigin allowedOrigin

/-- The functional implementation satisfies its post-condition for all inputs. -/
theorem safeSopCheck_correct (requestOrigin allowedOrigin : String) :
    Pre requestOrigin allowedOrigin → Post_prop requestOrigin allowedOrigin := by
  intro _
  exact ⟨acceptsExactMatch_thm requestOrigin allowedOrigin,
    rejectsMismatch_thm requestOrigin allowedOrigin,
    exactCharacterization_thm requestOrigin allowedOrigin⟩

/-- Imperative version of `safeSopCheck`, using mutable state in `Id`. -/
def safeSopCheckImperative (requestOrigin allowedOrigin : String) : Bool := Id.run do
  let mut accepted := false
  if requestOrigin == allowedOrigin then
    accepted := true
  return accepted

example : safeSopCheckImperative "https://example.com" "https://example.com" = true := by
  native_decide

example : safeSopCheckImperative "https://evil.com" "https://example.com" = false := by
  native_decide

example : safeSopCheckImperative "" "https://example.com" = false := by
  native_decide

example : safeSopCheckImperative "https://example.com" "https://example.com:8080" = false := by
  native_decide

#eval safeSopCheckImperative "https://example.com" "https://example.com"
#eval safeSopCheckImperative "https://evil.com" "https://example.com"
#eval safeSopCheckImperative "" "https://example.com"
#eval safeSopCheckImperative "https://example.com" "https://example.com:8080"

/-- The functional and imperative implementations return the same result. -/
theorem safeSopCheck_equiv_imperative (requestOrigin allowedOrigin : String) :
    safeSopCheck requestOrigin allowedOrigin =
      safeSopCheckImperative requestOrigin allowedOrigin := by
  by_cases h : requestOrigin = allowedOrigin
  · simp [safeSopCheck, safeSopCheckImperative, h]
  · simp [safeSopCheck, safeSopCheckImperative, h]

end UnsafeSameOriginCheckSafe
