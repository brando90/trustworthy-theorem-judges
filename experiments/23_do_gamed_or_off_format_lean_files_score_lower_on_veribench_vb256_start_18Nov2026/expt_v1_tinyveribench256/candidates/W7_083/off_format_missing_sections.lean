import Mathlib

namespace Gold
namespace UnsafeReplayAttack

def unsafeReplayCheck (_messageSeq _lastSeenSeq : Nat) : Bool :=
  true

example : unsafeReplayCheck 5 4 = true := rfl
example : unsafeReplayCheck 3 5 = true := rfl
example : unsafeReplayCheck 5 5 = true := rfl
example : unsafeReplayCheck 0 0 = true := rfl
example : unsafeReplayCheck 1 100 = true := rfl
example : unsafeReplayCheck 100 1 = true := rfl
example : unsafeReplayCheck 10 10 = true := rfl

theorem unsafeReplayCheck_accepts_all (messageSeq lastSeenSeq : Nat) :
    unsafeReplayCheck messageSeq lastSeenSeq = true := rfl

theorem unsafeReplayCheck_ignores_messageSeq (s1 s2 last : Nat) :
    unsafeReplayCheck s1 last = unsafeReplayCheck s2 last := rfl

theorem unsafeReplayCheck_ignores_lastSeenSeq (msg last1 last2 : Nat) :
    unsafeReplayCheck msg last1 = unsafeReplayCheck msg last2 := rfl

theorem unsafeReplayCheck_accepts_replay (messageSeq lastSeenSeq : Nat) :
    messageSeq ≤ lastSeenSeq → unsafeReplayCheck messageSeq lastSeenSeq = true :=
  fun _ => rfl

example (messageSeq lastSeenSeq : Nat) :
    unsafeReplayCheck messageSeq lastSeenSeq = true ∧
    unsafeReplayCheck messageSeq lastSeenSeq = unsafeReplayCheck 0 lastSeenSeq ∧
    unsafeReplayCheck messageSeq lastSeenSeq = unsafeReplayCheck messageSeq 0 ∧
    (messageSeq ≤ lastSeenSeq → unsafeReplayCheck messageSeq lastSeenSeq = true) :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

end UnsafeReplayAttack
end Gold
