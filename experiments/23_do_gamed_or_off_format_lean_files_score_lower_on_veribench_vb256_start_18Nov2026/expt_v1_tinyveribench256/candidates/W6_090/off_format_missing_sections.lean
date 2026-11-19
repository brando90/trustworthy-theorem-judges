import Mathlib

namespace Gold
namespace UnsafeCertChain

def unsafeCertChain (_caSignature : Nat) : Bool :=
  true

example : unsafeCertChain 42 = true := by native_decide
example : unsafeCertChain 0 = true := by native_decide
example : unsafeCertChain 99999 = true := by native_decide
example : unsafeCertChain 1 = true := by native_decide
example : unsafeCertChain 1000 = true := by native_decide

theorem unsafeCertChain_always_true (caSignature : Nat) :
    unsafeCertChain caSignature = true := rfl

theorem unsafeCertChain_accepts_unsigned_witness :
    ∃ caSignature : Nat, caSignature = 0 ∧ unsafeCertChain caSignature = true :=
  ⟨0, rfl, rfl⟩

theorem unsafeCertChain_accepts_when_unsigned :
    ∀ caSignature : Nat, caSignature = 0 → unsafeCertChain caSignature = true :=
  fun _ _ => rfl

example (caSignature : Nat) :
    unsafeCertChain caSignature = true ∧
    (∃ c : Nat, c = 0 ∧ unsafeCertChain c = true) ∧
    (caSignature = 0 → unsafeCertChain caSignature = true) :=
  ⟨rfl, ⟨0, rfl, rfl⟩, fun _ => rfl⟩

end UnsafeCertChain
end Gold
