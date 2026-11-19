/-!
# Unsafe heartbeat (Heartbleed-style) model

This file is a Lean 4 translation of a small Python program. The server echoes back
`claimedLen` bytes and never checks that value against the real payload length
`payloadLen`. Like the original, the model returns a byte *count*, not the payload bytes.

Python `int` has no size limit, so the model uses `Int`.
-/

namespace Heartbeat

/-- Return `claimedLen` without checking it against `payloadLen`.
The server copies `claimedLen` bytes whatever the payload length is.
The `payloadLen` argument is deliberately ignored. -/
def unsafeHeartbeat (_payloadLen : Int) (claimedLen : Int) : Int :=
  claimedLen

/-- Run the fixed examples. Returns `true` exactly when every check passes. -/
def check (candidate : Int → Int → Int) : Bool :=
  candidate 3 3 == 3 &&
  candidate 1 65535 == 65535 &&
  candidate 0 1000 == 1000 &&
  candidate 100 5 == 5 &&
  candidate 0 0 == 0

/-! ## Test cases (mirroring the Python `assert`s) -/

example : unsafeHeartbeat 3 3 = 3 := rfl
example : unsafeHeartbeat 1 65535 = 65535 := rfl
example : unsafeHeartbeat 0 1000 = 1000 := rfl
example : unsafeHeartbeat 100 5 = 5 := rfl
example : unsafeHeartbeat 0 0 = 0 := rfl

/-- The candidate passes the whole test suite. -/
theorem check_unsafeHeartbeat : check unsafeHeartbeat = true := by decide

#eval check unsafeHeartbeat  -- true

/-! ## Theorems -/

/-- The result is always the claimed length. -/
theorem unsafeHeartbeat_eq (p c : Int) : unsafeHeartbeat p c = c := rfl

/-- The result does not depend on the real payload length at all. -/
theorem unsafeHeartbeat_payload_irrelevant (p₁ p₂ c : Int) :
    unsafeHeartbeat p₁ c = unsafeHeartbeat p₂ c := rfl

/-- The response stays within the payload exactly when the claim is honest (`c ≤ p`). -/
theorem unsafeHeartbeat_le_payload_iff (p c : Int) :
    unsafeHeartbeat p c ≤ p ↔ c ≤ p := Iff.rfl

/-- Over-read: if the claim is larger than the payload, the response is larger than the payload. -/
theorem unsafeHeartbeat_overread (p c : Int) (h : p < c) :
    p < unsafeHeartbeat p c := h

/-- The over-read amount is exactly `claimedLen - payloadLen`. -/
theorem unsafeHeartbeat_leak_amount (p c : Int) :
    unsafeHeartbeat p c - p = c - p := rfl

/-- The leaked amount is strictly positive whenever the claim is larger than the payload. -/
theorem unsafeHeartbeat_leak_pos (p c : Int) (h : p < c) :
    0 < unsafeHeartbeat p c - p := by
  have h' : unsafeHeartbeat p c = c := rfl
  omega

/-- The function is unsafe: no payload bound holds for every input.
The test case `(1, 65535)` is a counterexample. -/
theorem unsafeHeartbeat_not_bounded :
    ¬ ∀ p c : Int, unsafeHeartbeat p c ≤ p := by
  intro h
  have h1 : (65535 : Int) ≤ 1 := h 1 65535
  omega

/-- Concrete Heartbleed instance: a 1-byte payload claiming 65535 bytes leaks 65534 extra bytes. -/
theorem unsafeHeartbeat_heartbleed_example :
    unsafeHeartbeat 1 65535 - 1 = 65534 := by decide

/-- When the claim is honest (`0 ≤ c ≤ p`), the response is a valid in-bounds length. -/
theorem unsafeHeartbeat_honest_in_bounds (p c : Int) (h0 : 0 ≤ c) (h : c ≤ p) :
    0 ≤ unsafeHeartbeat p c ∧ unsafeHeartbeat p c ≤ p :=
  ⟨h0, h⟩

end Heartbeat
