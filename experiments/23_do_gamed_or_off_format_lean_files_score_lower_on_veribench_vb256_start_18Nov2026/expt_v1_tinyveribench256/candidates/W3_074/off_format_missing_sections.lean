import Mathlib
namespace Gold

namespace SafeFrozenRead

def safeFrozenRead (length bufSize : Nat) : Option Nat :=
  if length ≤ bufSize then some length else none

example : safeFrozenRead 5 100 = some 5 := by native_decide
example : safeFrozenRead 200 100 = none := by native_decide
example : safeFrozenRead 100 100 = some 100 := by native_decide
example : safeFrozenRead 101 100 = none := by native_decide
example : safeFrozenRead 0 0 = some 0 := by native_decide
example : safeFrozenRead 0 100 = some 0 := by native_decide
example : safeFrozenRead 999 100 = none := by native_decide
example : safeFrozenRead 1 0 = none := by native_decide

theorem safeFrozenRead_of_le (length bufSize : Nat) (h : length ≤ bufSize) :
    safeFrozenRead length bufSize = some length := by
  simp [safeFrozenRead, h]

theorem safeFrozenRead_of_lt (length bufSize : Nat) (h : bufSize < length) :
    safeFrozenRead length bufSize = none := by
  simp [safeFrozenRead, Nat.not_le.mpr h]

theorem safeFrozenRead_some_le (length bufSize v : Nat)
    (h : safeFrozenRead length bufSize = some v) : v ≤ bufSize := by
  unfold safeFrozenRead at h
  by_cases hlen : length ≤ bufSize
  · simp [hlen] at h; exact h ▸ hlen
  · simp [hlen] at h

theorem safeFrozenRead_some_eq (length bufSize v : Nat)
    (h : safeFrozenRead length bufSize = some v) : v = length := by
  unfold safeFrozenRead at h
  by_cases hlen : length ≤ bufSize
  · simp [hlen] at h; exact h.symm
  · simp [hlen] at h

end SafeFrozenRead
end Gold
