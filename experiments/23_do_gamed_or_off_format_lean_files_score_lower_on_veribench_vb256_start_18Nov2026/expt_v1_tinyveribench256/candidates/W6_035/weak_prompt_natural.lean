/-!
# Unsafe CSRF check

A teaching model for MIT 6.858. It approves the modeled request without
validating `requestToken` and `sessionToken`.

Translated from Python. Python `int` becomes `Int` and `bool` becomes `Bool`.
The Python `check` raises `AssertionError` when a check fails. Here `check`
returns `false` instead.
-/

namespace UnsafeCsrf

/-- Approve the modeled request without validating `requestToken` and
`sessionToken`. The token is not validated, which is the vulnerability. -/
def unsafeCsrfCheck (_requestToken _sessionToken : Int) : Bool :=
  true

/-- Run the fixed examples. Returns `true` exactly when all checks pass. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 42 42 == true &&
  candidate 0 99 == true &&
  candidate 12345 67890 == true &&
  candidate 0 0 == true &&
  candidate 0 1 == true

/-- This mirrors `assert check(unsafe_csrf_check)` in the Python program. -/
theorem check_unsafeCsrfCheck : check unsafeCsrfCheck = true := by
  decide

#eval if check unsafeCsrfCheck then "All tests passed." else "Candidate failed tests"

/-! ## Behavior of the unsafe check -/

/-- The check approves every request. -/
theorem unsafeCsrfCheck_eq_true (requestToken sessionToken : Int) :
    unsafeCsrfCheck requestToken sessionToken = true :=
  rfl

/-- The result does not depend on either token. -/
theorem unsafeCsrfCheck_independent (r s r' s' : Int) :
    unsafeCsrfCheck r s = unsafeCsrfCheck r' s' :=
  rfl

/-- The check approves requests whose tokens do not match. -/
theorem unsafeCsrfCheck_approves_mismatch (r s : Int) (_h : r ≠ s) :
    unsafeCsrfCheck r s = true :=
  rfl

/-- There is a concrete forged request that the check approves. -/
theorem unsafeCsrfCheck_vulnerable :
    ∃ r s : Int, r ≠ s ∧ unsafeCsrfCheck r s = true :=
  ⟨0, 1, by decide, rfl⟩

/-! ## Soundness -/

/-- A CSRF check is sound if it approves a request only when the request
token equals the session token. -/
def SoundCsrfCheck (f : Int → Int → Bool) : Prop :=
  ∀ requestToken sessionToken : Int,
    f requestToken sessionToken = true → requestToken = sessionToken

/-- The unsafe check is not sound. -/
theorem unsafeCsrfCheck_not_sound : ¬ SoundCsrfCheck unsafeCsrfCheck := by
  intro h
  have h01 : (0 : Int) = 1 := h 0 1 rfl
  exact absurd h01 (by decide)

/-- A reference check that compares the two tokens. -/
def safeCsrfCheck (requestToken sessionToken : Int) : Bool :=
  decide (requestToken = sessionToken)

/-- The reference check is sound. -/
theorem safeCsrfCheck_sound : SoundCsrfCheck safeCsrfCheck := by
  intro r s h
  exact of_decide_eq_true h

/-- The reference check fails the fixed examples. The examples therefore
require the vulnerable behavior, such as approving `(0, 99)`. -/
theorem check_rejects_safeCsrfCheck : check safeCsrfCheck = false := by
  decide

end UnsafeCsrf

-- I could not compile this here, so it has not been checked by Lean.
-- TLDR-end: [csrf-lean: translate] Lean 4 translation of the CSRF check. It proves
-- that the check approves every request, including mismatched tokens. It also proves
-- that the check is not sound, while a token-comparing check is sound but fails the
-- fixed examples.
