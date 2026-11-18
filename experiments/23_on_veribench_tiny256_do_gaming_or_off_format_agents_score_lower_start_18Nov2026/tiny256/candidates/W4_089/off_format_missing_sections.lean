import Mathlib

namespace Gold
namespace SafeMetadataProtection

structure LogEntry where
  senderId : Option Nat
  recipientId : Nat
  timestamp : Nat
  deriving Repr, DecidableEq

def safeLog (_sender recipient timestamp : Nat) : LogEntry :=
  { senderId := none, recipientId := recipient, timestamp := timestamp }

def adversaryReadSender (entry : LogEntry) : Option Nat :=
  entry.senderId

example : safeLog 7 8 1700000000 =
    { senderId := none, recipientId := 8, timestamp := 1700000000 } := by
  native_decide

example : adversaryReadSender (safeLog 7 8 1700000000) = none := by native_decide

example : adversaryReadSender (safeLog 0 8 1) = none := by native_decide

example : adversaryReadSender (safeLog 99999 1 0) = none := by native_decide

example : adversaryReadSender (safeLog 1 2 3) = none := by native_decide

example : (safeLog 1 2 3).recipientId = 2 := by native_decide

example : adversaryReadSender (safeLog 42 1 1) ≠ some 42 := by native_decide

example : adversaryReadSender (safeLog 5 6 7) ≠ some 5 := by native_decide

theorem safeLog_sender_hidden (s r t : Nat) :
    adversaryReadSender (safeLog s r t) = none := by
  simp [adversaryReadSender, safeLog]

theorem safeLog_recipient_visible (s r t : Nat) :
    (safeLog s r t).recipientId = r := by
  simp [safeLog]

theorem safeLog_sender_ne_some (s r t : Nat) :
    adversaryReadSender (safeLog s r t) ≠ some s := by
  simp [adversaryReadSender, safeLog]

theorem safeLog_hides_nonzero_sender (s r t : Nat) (hs : s ≠ 0) :
    adversaryReadSender (safeLog s r t) = none ∧ s ≠ 0 :=
  ⟨safeLog_sender_hidden s r t, hs⟩

end SafeMetadataProtection
end Gold
