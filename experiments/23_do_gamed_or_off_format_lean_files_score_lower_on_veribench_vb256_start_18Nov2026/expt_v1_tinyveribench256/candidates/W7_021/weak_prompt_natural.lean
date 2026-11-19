/-!
# Firmware acceptance model

A Lean 4 translation of a Python program that models firmware acceptance. It
returns whether the supplied `firmwareSize` is positive. The firmware bytes
are ignored: there is no length check, no signature verification and no
installation.
-/

/-- Return `true` if `firmwareSize` is greater than zero, otherwise `false`.
The firmware bytes are ignored without checking their length or signature.
This function only returns an acceptance flag. It does not install firmware. -/
def unsafeFirmwareUpdate (_firmwareData : ByteArray) (firmwareSize : Int) : Bool :=
  if firmwareSize > 0 then
    true   -- Flash without validation: CRITICAL VULNERABILITY
  else
    false

/-- Run the fixed examples. The result is `true` exactly when every check passes. -/
def check (candidate : ByteArray → Int → Bool) : Bool :=
  candidate "fw".toUTF8 2 == true &&
  candidate ByteArray.empty 0 == false &&
  candidate "a".toUTF8 0 == false &&
  candidate ByteArray.empty 1 == true &&
  candidate "a".toUTF8 1 == true

#eval check unsafeFirmwareUpdate  -- expected: true

/-! ## Theorems -/

/-- The fixed test suite passes. -/
theorem check_unsafeFirmwareUpdate : check unsafeFirmwareUpdate = true := by
  decide

/-- The function is the Boolean decision of `firmwareSize > 0`. -/
theorem unsafeFirmwareUpdate_eq_decide (d : ByteArray) (n : Int) :
    unsafeFirmwareUpdate d n = decide (n > 0) := by
  unfold unsafeFirmwareUpdate
  by_cases h : n > 0
  · rw [if_pos h, decide_eq_true h]
  · rw [if_neg h, decide_eq_false h]

/-- Acceptance happens exactly when the claimed size is positive. -/
theorem unsafeFirmwareUpdate_accepts_iff (d : ByteArray) (n : Int) :
    unsafeFirmwareUpdate d n = true ↔ n > 0 := by
  unfold unsafeFirmwareUpdate
  by_cases h : n > 0
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun h' => by cases h', fun h' => absurd h' h⟩

/-- Rejection happens exactly when the claimed size is zero or negative. -/
theorem unsafeFirmwareUpdate_rejects_iff (d : ByteArray) (n : Int) :
    unsafeFirmwareUpdate d n = false ↔ n ≤ 0 := by
  unfold unsafeFirmwareUpdate
  by_cases h : n > 0
  · rw [if_pos h]
    exact ⟨fun h' => by cases h', fun h' => absurd h (by omega)⟩
  · rw [if_neg h]
    exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- The firmware bytes never affect the result. -/
theorem unsafeFirmwareUpdate_ignores_data (d₁ d₂ : ByteArray) (n : Int) :
    unsafeFirmwareUpdate d₁ n = unsafeFirmwareUpdate d₂ n := rfl

/-- Vulnerability: any data, including empty or forged data, is accepted for
any positive claimed size. -/
theorem unsafeFirmwareUpdate_accepts_any_data (d : ByteArray) {n : Int} (h : n > 0) :
    unsafeFirmwareUpdate d n = true :=
  (unsafeFirmwareUpdate_accepts_iff d n).mpr h

/-- Vulnerability: the claimed size need not match the actual data length. -/
theorem unsafeFirmwareUpdate_accepts_size_mismatch :
    ByteArray.empty.size ≠ 1 ∧ unsafeFirmwareUpdate ByteArray.empty 1 = true := by
  decide

/-- A zero size is always rejected. -/
theorem unsafeFirmwareUpdate_zero (d : ByteArray) :
    unsafeFirmwareUpdate d 0 = false :=
  (unsafeFirmwareUpdate_rejects_iff d 0).mpr (by decide)

/-- Negative sizes are always rejected. -/
theorem unsafeFirmwareUpdate_neg (d : ByteArray) {n : Int} (h : n < 0) :
    unsafeFirmwareUpdate d n = false :=
  (unsafeFirmwareUpdate_rejects_iff d n).mpr (by omega)

/-- Every size of the form `k + 1` for a natural number `k` is accepted. -/
theorem unsafeFirmwareUpdate_succ (d : ByteArray) (k : Nat) :
    unsafeFirmwareUpdate d ((k : Int) + 1) = true :=
  (unsafeFirmwareUpdate_accepts_iff d _).mpr (by omega)

/-- Acceptance is monotone in the claimed size, whatever the data. -/
theorem unsafeFirmwareUpdate_mono (d₁ d₂ : ByteArray) {n m : Int} (hnm : n ≤ m)
    (h : unsafeFirmwareUpdate d₁ n = true) : unsafeFirmwareUpdate d₂ m = true := by
  rw [unsafeFirmwareUpdate_accepts_iff] at h ⊢
  omega

/-- The two outcomes are exhaustive and exclusive, decided by the sign of the size. -/
theorem unsafeFirmwareUpdate_dichotomy (d : ByteArray) (n : Int) :
    (unsafeFirmwareUpdate d n = true ∧ n > 0) ∨
    (unsafeFirmwareUpdate d n = false ∧ n ≤ 0) := by
  by_cases h : n > 0
  · exact Or.inl ⟨(unsafeFirmwareUpdate_accepts_iff d n).mpr h, h⟩
  · have h' : n ≤ 0 := by omega
    exact Or.inr ⟨(unsafeFirmwareUpdate_rejects_iff d n).mpr h', h'⟩
