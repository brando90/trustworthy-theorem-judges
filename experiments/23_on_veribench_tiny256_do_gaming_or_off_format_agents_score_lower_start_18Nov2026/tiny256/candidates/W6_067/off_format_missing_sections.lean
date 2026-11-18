import Mathlib

namespace Gold
namespace UnsafeCircuitHops

def unsafeCircuitHops (_hopCount : Nat) : Bool :=
  true

example : unsafeCircuitHops 3 = true := by native_decide
example : unsafeCircuitHops 0 = true := by native_decide
example : unsafeCircuitHops 1 = true := by native_decide
example : unsafeCircuitHops 2 = true := by native_decide
example : unsafeCircuitHops 10 = true := by native_decide

theorem unsafeCircuitHops_always_true (hopCount : Nat) :
    unsafeCircuitHops hopCount = true := by
  simp [unsafeCircuitHops]

theorem unsafeCircuitHops_accepts_some_insufficient :
    ∃ hopCount : Nat, hopCount < 3 ∧ unsafeCircuitHops hopCount = true :=
  ⟨0, by omega, by simp [unsafeCircuitHops]⟩

theorem unsafeCircuitHops_insufficient_accepted (hopCount : Nat) (_h : hopCount < 3) :
    unsafeCircuitHops hopCount = true := by
  simp [unsafeCircuitHops]

end UnsafeCircuitHops
end Gold
