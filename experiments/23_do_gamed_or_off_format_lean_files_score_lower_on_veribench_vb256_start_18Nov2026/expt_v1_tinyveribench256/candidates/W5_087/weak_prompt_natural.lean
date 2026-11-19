/-!
# Unsafe HMAC verification (length check missing)

A Lean 4 translation of a Python program. The verifier accepts a MAC without
checking that `macLen = expectedMacLen`.

MIT 6.858 Quiz 2, Fall 2014: cryptography / HMAC length extension.

Python's `int` is unbounded and can be negative, so it maps to Lean's `Int`.
-/

namespace UnsafeHmac

/-- Approve the request without checking whether `macLen` equals
`expectedMacLen`. This matches the Python, which always returns `True`. -/
def unsafeHmacVerify (_messageLen _macLen _expectedMacLen : Int) : Bool :=
  true

/-- A reference verifier that performs the missing length check. It models only
the length comparison, not the MAC bytes. -/
def safeHmacVerify (_messageLen macLen expectedMacLen : Int) : Bool :=
  decide (macLen = expectedMacLen)

/-! ## The fixed examples from `check()` -/

example : unsafeHmacVerify 10 32 32 = true := rfl
example : unsafeHmacVerify 10 64 32 = true := rfl
example : unsafeHmacVerify 10 0 32 = true := rfl
example : unsafeHmacVerify 0 0 0 = true := rfl
example : unsafeHmacVerify 1 32 32 = true := rfl

/-- `check()` as a Boolean: `true` exactly when every Python assertion passes. -/
def check : Bool :=
  (unsafeHmacVerify 10 32 32 == true) &&
  (unsafeHmacVerify 10 64 32 == true) &&
  (unsafeHmacVerify 10 0 32 == true) &&
  (unsafeHmacVerify 0 0 0 == true) &&
  (unsafeHmacVerify 1 32 32 == true)

theorem check_passes : check = true := by decide

/-! ## Theorems about the unsafe verifier -/

/-- The unsafe verifier accepts every input. -/
theorem unsafe_always_accepts (m l e : Int) : unsafeHmacVerify m l e = true := rfl

/-- The unsafe verifier never rejects. -/
theorem unsafe_never_rejects (m l e : Int) : unsafeHmacVerify m l e ≠ false := by
  simp [unsafeHmacVerify]

/-- The result does not depend on any argument. -/
theorem unsafe_independent_of_inputs (m l e m' l' e' : Int) :
    unsafeHmacVerify m l e = unsafeHmacVerify m' l' e' := rfl

/-- It accepts any MAC whose length differs from the expected length. -/
theorem unsafe_accepts_length_mismatch (m l e : Int) (_h : l ≠ e) :
    unsafeHmacVerify m l e = true := rfl

/-- A concrete accepted input with mismatched lengths exists. -/
theorem exists_accepted_length_mismatch :
    ∃ m l e : Int, l ≠ e ∧ unsafeHmacVerify m l e = true :=
  ⟨10, 64, 32, by decide, rfl⟩

/-- The unsafe verifier is not sound for the length check: acceptance does not
imply that the lengths match. -/
theorem unsafe_not_length_sound :
    ¬ (∀ m l e : Int, unsafeHmacVerify m l e = true → l = e) := by
  intro h
  have h' := h 10 64 32 rfl
  omega

/-! ## Comparison with the safe verifier -/

/-- The safe verifier accepts exactly when the lengths match. -/
theorem safe_accepts_iff (m l e : Int) : safeHmacVerify m l e = true ↔ l = e := by
  unfold safeHmacVerify
  exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- The unsafe verifier accepts everything the safe verifier accepts. -/
theorem safe_implies_unsafe (m l e : Int) :
    safeHmacVerify m l e = true → unsafeHmacVerify m l e = true :=
  fun _ => rfl

/-- The two verifiers agree exactly on inputs whose lengths match. -/
theorem unsafe_agrees_with_safe_iff (m l e : Int) :
    unsafeHmacVerify m l e = safeHmacVerify m l e ↔ l = e := by
  unfold unsafeHmacVerify safeHmacVerify
  constructor
  · intro h
    exact of_decide_eq_true h.symm
  · intro h
    exact (decide_eq_true h).symm

/-- On a length mismatch, the unsafe verifier accepts and the safe one rejects. -/
theorem mismatch_unsafe_accepts_safe_rejects (m l e : Int) (h : l ≠ e) :
    unsafeHmacVerify m l e = true ∧ safeHmacVerify m l e = false := by
  refine ⟨rfl, ?_⟩
  unfold safeHmacVerify
  exact decide_eq_false h

/-- An extended (too long) MAC, as in a length-extension attack, is accepted by
the unsafe verifier and rejected by the safe one. -/
theorem extended_mac_accepted (m l e : Int) (h : e < l) :
    unsafeHmacVerify m l e = true ∧ safeHmacVerify m l e = false :=
  mismatch_unsafe_accepts_safe_rejects m l e (by omega)

/-- An empty MAC is accepted by the unsafe verifier whenever a nonempty MAC is
expected; the safe verifier rejects it. -/
theorem empty_mac_accepted (m e : Int) (h : 0 < e) :
    unsafeHmacVerify m 0 e = true ∧ safeHmacVerify m 0 e = false :=
  mismatch_unsafe_accepts_safe_rejects m 0 e (by omega)

/-- The verifiers disagree on the Python example `(10, 64, 32)`. -/
theorem disagree_on_example : unsafeHmacVerify 10 64 32 ≠ safeHmacVerify 10 64 32 := by
  decide

end UnsafeHmac

/-- Mirrors `if __name__ == "__main__": check()`. -/
def main : IO Unit := do
  unless UnsafeHmac.check do
    throw <| IO.userError "AssertionError: check failed"

-- TLDR-end: [unsafe-hmac: Lean translation] `unsafeHmacVerify` always returns
-- `true`; the theorems show that it accepts any length mismatch and agrees with
-- a length-checking verifier only when `macLen = expectedMacLen`.
