import Mathlib

namespace UnsafeWepKeystream

def unsafeWepCheck (_iv1 _iv2 : Nat) : Bool :=
  true

example : unsafeWepCheck 1 2 = true := rfl
example : unsafeWepCheck 5 5 = true := rfl
example : unsafeWepCheck 0 0 = true := rfl
example : unsafeWepCheck 999999 999999 = true := rfl
example : unsafeWepCheck 10 20 = true := rfl
example : unsafeWepCheck 7 7 = true := rfl
example : unsafeWepCheck 3 3 = true := rfl

theorem unsafeWepCheck_accepts_all (iv1 iv2 : Nat) :
    unsafeWepCheck iv1 iv2 = true := rfl

theorem unsafeWepCheck_reused_iv_witness :
    ∃ iv1 iv2 : Nat, iv1 = iv2 ∧ unsafeWepCheck iv1 iv2 = true :=
  ⟨5, 5, rfl, rfl⟩

theorem unsafeWepCheck_accepts_reused_iv (iv1 iv2 : Nat) (_h : iv1 = iv2) :
    unsafeWepCheck iv1 iv2 = true := rfl

example (iv : Nat) : unsafeWepCheck iv iv = true := rfl

end UnsafeWepKeystream
