import Mathlib

namespace UnsafeSeccompFilter

def unsafeSeccompFilter (_syscallId : Nat) (_allowed : List Nat) : Bool :=
  true

example : unsafeSeccompFilter 1 [1, 2, 3] = true := rfl
example : unsafeSeccompFilter 101 [1, 2, 3] = true := rfl
example : unsafeSeccompFilter 1 [] = true := rfl
example : unsafeSeccompFilter 0 [] = true := rfl
example : unsafeSeccompFilter 0x1000 [1, 2, 3] = true := rfl
example : unsafeSeccompFilter 99 [42] = true := rfl
example : unsafeSeccompFilter 999 [] = true := rfl
example : unsafeSeccompFilter 200 [1, 2, 3, 4, 5] = true := rfl

theorem unsafeSeccompFilter_eq_true (syscallId : Nat) (allowed : List Nat) :
    unsafeSeccompFilter syscallId allowed = true := rfl

example : ∃ (syscallId : Nat) (allowed : List Nat),
    allowed.all (fun q => q ≠ syscallId) = true ∧
    unsafeSeccompFilter syscallId allowed = true :=
  ⟨1, [2], by decide, rfl⟩

theorem unsafeSeccompFilter_permits_unlisted (syscallId : Nat) (allowed : List Nat)
    (_h : allowed.all (fun q => q ≠ syscallId) = true) :
    unsafeSeccompFilter syscallId allowed = true := rfl

end UnsafeSeccompFilter
