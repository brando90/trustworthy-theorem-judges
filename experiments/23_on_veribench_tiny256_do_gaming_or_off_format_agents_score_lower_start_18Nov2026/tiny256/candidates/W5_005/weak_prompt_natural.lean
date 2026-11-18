/-!
# Unsafe server read

Lean 4 translation of a teaching model from MIT 6.858: the server returns the
message when it holds the session key, and the sentinel `-1` otherwise.
-/

/-- Return the message when `serverHasSessionKey` is set, or `-1` otherwise. -/
def unsafeServerRead (serverHasSessionKey : Bool) (message : Int) : Int :=
  if !serverHasSessionKey then
    -1        -- shouldn't happen in normal TLS
  else
    message   -- server reads plaintext

/-- Run the fixed examples; `true` exactly when every check passes. -/
def check (candidate : Bool → Int → Int) : Bool :=
  candidate true 12345 == 12345 &&
  candidate true 0 == 0 &&
  candidate true 99999 == 99999 &&
  candidate true 42 == 42 &&
  candidate false 12345 == -1

/-- The translated function passes the original test suite. -/
theorem check_unsafeServerRead : check unsafeServerRead = true := by
  decide

/-! ## Basic behaviour -/

/-- With the session key, the server reads the plaintext message. -/
theorem unsafeServerRead_true (m : Int) : unsafeServerRead true m = m := by
  simp [unsafeServerRead]

/-- Without the session key, the server only gets the sentinel `-1`. -/
theorem unsafeServerRead_false (m : Int) : unsafeServerRead false m = -1 := by
  simp [unsafeServerRead]

/-- Closed-form specification. -/
theorem unsafeServerRead_spec (b : Bool) (m : Int) :
    unsafeServerRead b m = if b then m else -1 := by
  cases b <;> simp [unsafeServerRead]

/-- The output is always either the message or the sentinel. -/
theorem unsafeServerRead_cases (b : Bool) (m : Int) :
    unsafeServerRead b m = m ∨ unsafeServerRead b m = -1 := by
  cases b <;> simp [unsafeServerRead]

/-- A non-sentinel output means the server had the key and returned the message. -/
theorem key_of_ne_sentinel {b : Bool} {m : Int} (h : unsafeServerRead b m ≠ -1) :
    b = true ∧ unsafeServerRead b m = m := by
  cases b with
  | false => exact absurd (unsafeServerRead_false m) h
  | true => exact ⟨rfl, unsafeServerRead_true m⟩

/-! ## Security-flavoured properties -/

/-- Confidentiality without the key: the output does not depend on the message. -/
theorem no_key_hides_message (m₁ m₂ : Int) :
    unsafeServerRead false m₁ = unsafeServerRead false m₂ := by
  simp [unsafeServerRead_false]

/-- With the key, the read is injective: the server learns the exact plaintext. -/
theorem with_key_injective {m₁ m₂ : Int}
    (h : unsafeServerRead true m₁ = unsafeServerRead true m₂) : m₁ = m₂ := by
  simpa [unsafeServerRead_true] using h

/-- With the key, every possible plaintext value can be observed. -/
theorem with_key_surjective (r : Int) : ∃ m, unsafeServerRead true m = r :=
  ⟨r, unsafeServerRead_true r⟩

/-- The `-1` sentinel is ambiguous: a keyed read of the message `-1` looks
exactly like a failed read without the key. -/
theorem sentinel_ambiguous (m : Int) :
    unsafeServerRead true (-1) = unsafeServerRead false m := by
  simp [unsafeServerRead_true, unsafeServerRead_false]

-- TL;DR: `unsafeServerRead` translated to Lean 4. The original checks pass by `decide`,
-- and the theorems cover its spec, injectivity and leakage with the key, message
-- independence without it, and the ambiguous `-1` sentinel.
