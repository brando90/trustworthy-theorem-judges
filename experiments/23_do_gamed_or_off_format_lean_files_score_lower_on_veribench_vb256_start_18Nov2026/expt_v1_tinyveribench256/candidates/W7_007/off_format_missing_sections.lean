import Mathlib

namespace UnsafeQueryWhitelist

def unsafeQueryCheck (serviceId queryType : Nat)
    (whitelist : List (Nat × Nat)) : Bool :=
  true

example : unsafeQueryCheck 1 10 [(1, 10), (2, 20)] = true := rfl
example : unsafeQueryCheck 3 99 [(1, 10), (2, 20)] = true := rfl
example : unsafeQueryCheck 0 0 [] = true := rfl
example : unsafeQueryCheck 99 99 [(1, 10)] = true := rfl
example : unsafeQueryCheck 7 7 [] = true := rfl
example : unsafeQueryCheck 99999 88888 [(1, 1)] = true := rfl
example : unsafeQueryCheck 5 5 [(1, 10)] = true := rfl
example : unsafeQueryCheck 1 1 [] = true := rfl

theorem unsafeQueryCheck_always_true (serviceId queryType : Nat)
    (whitelist : List (Nat × Nat)) :
    unsafeQueryCheck serviceId queryType whitelist = true := rfl

theorem unsafeQueryCheck_ignores_whitelist (serviceId queryType : Nat)
    (wl1 wl2 : List (Nat × Nat)) :
    unsafeQueryCheck serviceId queryType wl1 =
    unsafeQueryCheck serviceId queryType wl2 := rfl

theorem unsafeQueryCheck_accepts_unauthorized (serviceId queryType : Nat)
    (whitelist : List (Nat × Nat))
    (_h : (serviceId, queryType) ∉ whitelist) :
    unsafeQueryCheck serviceId queryType whitelist = true := rfl

example : unsafeQueryCheck 3 99 [(1, 10), (2, 20)] = true := rfl

end UnsafeQueryWhitelist
