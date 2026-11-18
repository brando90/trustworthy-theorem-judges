import Mathlib

namespace Gold
namespace UnsafeHeartbeat

def unsafeHeartbeat (_payloadLen claimedLen : Nat) : Nat :=
  claimedLen

example : unsafeHeartbeat 3 3 = 3 := by native_decide

example : unsafeHeartbeat 1 65535 = 65535 := by native_decide

example : unsafeHeartbeat 0 1000 = 1000 := by native_decide

example : unsafeHeartbeat 0 0 = 0 := by native_decide

example : unsafeHeartbeat 10 10 = 10 := by native_decide

example : unsafeHeartbeat 100 5 = 5 := by native_decide

example : unsafeHeartbeat 0 100 = unsafeHeartbeat 50 100 := by native_decide

theorem heartbeat_returns_claimed (payloadLen claimedLen : Nat) :
    unsafeHeartbeat payloadLen claimedLen = claimedLen := by
  simp [unsafeHeartbeat]

theorem heartbeat_overread_exists :
    ∃ payloadLen claimedLen : Nat,
      claimedLen > payloadLen ∧ unsafeHeartbeat payloadLen claimedLen > payloadLen := by
  exact ⟨1, 65535, by omega, by simp [unsafeHeartbeat]⟩

theorem heartbeat_ignores_payload_len (claimedLen : Nat) :
    ∀ p1 p2 : Nat, unsafeHeartbeat p1 claimedLen = unsafeHeartbeat p2 claimedLen := by
  intro p1 p2
  simp [unsafeHeartbeat]

end UnsafeHeartbeat
end Gold
