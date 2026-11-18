import Mathlib

namespace Gold
namespace UnsafeNonceReuse

def unsafeNonceReuse (_nonce _lastNonce _ciphertextId _expectedId : Nat) : Bool :=
  true

example : unsafeNonceReuse 11 10 42 42 = true := by native_decide

example : unsafeNonceReuse 5 10 42 42 = true := by native_decide

example : unsafeNonceReuse 10 10 42 42 = true := by native_decide

example : unsafeNonceReuse 0 100 1 1 = true := by native_decide

example : unsafeNonceReuse 100 200 7 7 = true := by native_decide

example : unsafeNonceReuse 1 1 0 99 = true := by native_decide

theorem unsafeNonceReuse_accepts_everything (nonce lastNonce ciphertextId expectedId : Nat) :
    unsafeNonceReuse nonce lastNonce ciphertextId expectedId = true := by
  simp [unsafeNonceReuse]

theorem unsafeNonceReuse_stale_replay_witness :
    ∃ nonce lastNonce : Nat, nonce ≤ lastNonce ∧
      unsafeNonceReuse nonce lastNonce 42 42 = true :=
  ⟨5, 10, by omega, by simp [unsafeNonceReuse]⟩

theorem unsafeNonceReuse_accepts_stale_nonce (nonce lastNonce : Nat) :
    nonce ≤ lastNonce → unsafeNonceReuse nonce lastNonce 42 42 = true := by
  intro _
  simp [unsafeNonceReuse]

example (nonce lastNonce ciphertextId expectedId : Nat) (_h : nonce ≤ lastNonce) :
    unsafeNonceReuse nonce lastNonce ciphertextId expectedId = true ∧
    (∃ n l : Nat, n ≤ l ∧ unsafeNonceReuse n l 42 42 = true) ∧
    (nonce ≤ lastNonce → unsafeNonceReuse nonce lastNonce 42 42 = true) :=
  ⟨unsafeNonceReuse_accepts_everything nonce lastNonce ciphertextId expectedId,
   unsafeNonceReuse_stale_replay_witness,
   unsafeNonceReuse_accepts_stale_nonce nonce lastNonce⟩

end UnsafeNonceReuse
end Gold
