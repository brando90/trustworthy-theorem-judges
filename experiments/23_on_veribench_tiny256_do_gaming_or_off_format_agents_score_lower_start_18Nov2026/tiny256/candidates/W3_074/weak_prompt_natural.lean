/-!
# `safe_frozen_read`: Lean 4 translation

Python original:

    def safe_frozen_read(length: int, buf_size: int):
        if length <= buf_size:
            return length
        return None

Translation notes:
* Python `int` has no size limit, so it maps to Lean `Int`. Negative values are compared directly,
  as in Python.
* Python `None` maps to `Option.none`, and a returned value `x` maps to `Option.some x`.
* Python's `check` raises `AssertionError` when a result is wrong. The Lean `check` returns
  `false` instead, and `main` turns that into an `IO` error.
-/

namespace SafeFrozenRead

/-- Return the supplied length when `length ≤ bufSize`; otherwise return `none`.
Negative integers are accepted and compared directly. The same value is both
checked and returned, so there is no second read. -/
def safeFrozenRead (length bufSize : Int) : Option Int :=
  if length ≤ bufSize then some length else none

/-- Run the fixed examples. Returns `true` exactly when every result matches. -/
def check (candidate : Int → Int → Option Int) : Bool :=
  candidate 5 100 == some 5 &&
  candidate 100 100 == some 100 &&
  candidate 101 100 == none &&
  candidate 999 100 == none &&
  candidate 0 0 == some 0

/-! ## Concrete test cases (the Python `check`, proved by the kernel) -/

theorem check_safeFrozenRead : check safeFrozenRead = true := by decide

example : safeFrozenRead 5 100 = some 5 := by decide
example : safeFrozenRead 100 100 = some 100 := by decide
example : safeFrozenRead 101 100 = none := by decide
example : safeFrozenRead 999 100 = none := by decide
example : safeFrozenRead 0 0 = some 0 := by decide
-- Negative integers are compared directly.
example : safeFrozenRead (-3) 0 = some (-3) := by decide
example : safeFrozenRead (-1) (-5) = none := by decide

/-! ## General theorems -/

/-- When the check passes, the input length is returned unchanged. -/
theorem safeFrozenRead_of_le {length bufSize : Int} (h : length ≤ bufSize) :
    safeFrozenRead length bufSize = some length := by
  simp [safeFrozenRead, h]

/-- When the length is larger than the buffer, the result is `none`. -/
theorem safeFrozenRead_of_gt {length bufSize : Int} (h : bufSize < length) :
    safeFrozenRead length bufSize = none := by
  have h' : ¬ length ≤ bufSize := Int.not_le.mpr h
  simp [safeFrozenRead, h']

/-- The function only ever returns `some length` or `none`; it never returns any other value. -/
theorem safeFrozenRead_cases (length bufSize : Int) :
    safeFrozenRead length bufSize = some length ∨
      safeFrozenRead length bufSize = none := by
  by_cases h : length ≤ bufSize
  · exact Or.inl (safeFrozenRead_of_le h)
  · exact Or.inr (safeFrozenRead_of_gt (Int.not_le.mp h))

/-- Full description of a `some` result: it happens exactly when the check passes, and the
returned value is the same `length` that was checked. -/
theorem safeFrozenRead_eq_some_iff {length bufSize v : Int} :
    safeFrozenRead length bufSize = some v ↔ length ≤ bufSize ∧ v = length := by
  unfold safeFrozenRead
  by_cases h : length ≤ bufSize
  · rw [if_pos h]
    constructor
    · intro hs
      exact ⟨h, (Option.some.inj hs).symm⟩
    · intro ⟨_, hv⟩
      rw [hv]
  · rw [if_neg h]
    constructor
    · intro hs
      cases hs
    · intro ⟨hl, _⟩
      exact absurd hl h

/-- Full description of a `none` result. -/
theorem safeFrozenRead_eq_none_iff {length bufSize : Int} :
    safeFrozenRead length bufSize = none ↔ bufSize < length := by
  constructor
  · intro hn
    by_cases h : length ≤ bufSize
    · rw [safeFrozenRead_of_le h] at hn
      cases hn
    · exact Int.not_le.mp h
  · exact fun h => safeFrozenRead_of_gt h

/-- A value is returned exactly when `length ≤ bufSize`. -/
theorem safeFrozenRead_isSome_iff {length bufSize : Int} :
    (safeFrozenRead length bufSize).isSome = true ↔ length ≤ bufSize := by
  by_cases h : length ≤ bufSize
  · simp [safeFrozenRead, h]
  · simp [safeFrozenRead, h]

/-- Safety bound: any returned value fits within the buffer. -/
theorem safeFrozenRead_le_bufSize {length bufSize v : Int}
    (h : safeFrozenRead length bufSize = some v) : v ≤ bufSize := by
  have ⟨hle, hv⟩ := safeFrozenRead_eq_some_iff.mp h
  rw [hv]
  exact hle

/-- Frozen read: any returned value is exactly the input `length`. -/
theorem safeFrozenRead_val_eq {length bufSize v : Int}
    (h : safeFrozenRead length bufSize = some v) : v = length :=
  (safeFrozenRead_eq_some_iff.mp h).2

/-- Boundary case: a length equal to the buffer size is accepted. -/
theorem safeFrozenRead_self (n : Int) : safeFrozenRead n n = some n :=
  safeFrozenRead_of_le (Int.le_refl n)

/-- Monotonicity: a length accepted for buffer `b` is also accepted for any larger buffer `b'`. -/
theorem safeFrozenRead_mono {length b b' : Int} (hb : b ≤ b')
    (h : (safeFrozenRead length b).isSome = true) :
    safeFrozenRead length b' = some length :=
  safeFrozenRead_of_le (Int.le_trans (safeFrozenRead_isSome_iff.mp h) hb)

/-- A negative length is always accepted by a buffer whose size is not negative. -/
theorem safeFrozenRead_neg_length {length bufSize : Int}
    (hl : length < 0) (hb : 0 ≤ bufSize) :
    safeFrozenRead length bufSize = some length :=
  safeFrozenRead_of_le (by omega)

end SafeFrozenRead

open SafeFrozenRead in
def main : IO Unit := do
  if check safeFrozenRead then
    IO.println "All tests passed."
  else
    throw <| IO.userError "Failed: safe_frozen_read"

-- TLDR: `safeFrozenRead` returns `some length` when `length ≤ bufSize` and `none` otherwise. The
-- Python `check` is proved with `decide`. The theorems prove that the result is exactly
-- `some length` or `none` and fits within the buffer, and that acceptance is monotonic in the
-- buffer size. This file has not been compiled with a Lean toolchain.
