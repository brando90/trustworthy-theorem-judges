import Mathlib

namespace Gold
namespace UnsafeFirmwareUpdate

def unsafeFirmwareUpdate (_firmwareHash : Nat) (_signature : Nat) (firmwareSize : Nat) : Bool :=
  firmwareSize > 0

example : unsafeFirmwareUpdate 0xABCD 0x1234 1024 = true := by native_decide
example : unsafeFirmwareUpdate 0xABCD 0x1234 0 = false := by native_decide
example : unsafeFirmwareUpdate 0xDEAD 0x0000 5 = true := by native_decide
example : unsafeFirmwareUpdate 0 0 1 = true := by native_decide
example : unsafeFirmwareUpdate 0xABCD 0xABCD 512 = true := by native_decide
example : unsafeFirmwareUpdate 0xABCD 0x0000 512 = true := by native_decide
example : unsafeFirmwareUpdate 1 2 10 = unsafeFirmwareUpdate 3 4 10 := by native_decide
example : unsafeFirmwareUpdate 100 200 0 = false := by native_decide

theorem firmware_update_sig_irrelevant (hash sig1 sig2 size : Nat) :
    unsafeFirmwareUpdate hash sig1 size = unsafeFirmwareUpdate hash sig2 size := rfl

theorem firmware_update_hash_irrelevant (hash1 hash2 sig size : Nat) :
    unsafeFirmwareUpdate hash1 sig size = unsafeFirmwareUpdate hash2 sig size := rfl

theorem firmware_update_accepts_of_pos (hash sig size : Nat) (h : size > 0) :
    unsafeFirmwareUpdate hash sig size = true := by
  simpa [unsafeFirmwareUpdate] using h

example (hash sig size : Nat) (h : size > 0) :
    unsafeFirmwareUpdate hash sig size = true ∧ unsafeFirmwareUpdate hash 0 size = true :=
  ⟨firmware_update_accepts_of_pos hash sig size h, firmware_update_accepts_of_pos hash 0 size h⟩

end UnsafeFirmwareUpdate
end Gold
