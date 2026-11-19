import Mathlib

namespace Gold
namespace UnsafeBpfOobRead

def unsafeBpfOobRead (offset _length pktLen : Nat) : Bool :=
  offset < pktLen

example : unsafeBpfOobRead 0 4 20 = true := by native_decide

example : unsafeBpfOobRead 18 4 20 = true := by native_decide

example : unsafeBpfOobRead 20 4 20 = false := by native_decide

example : unsafeBpfOobRead 0 100 20 = true := by native_decide

example : unsafeBpfOobRead 5 0 20 = true := by native_decide

example : unsafeBpfOobRead 19 2 20 = true := by native_decide

example : unsafeBpfOobRead 20 0 20 = false := by native_decide

example : unsafeBpfOobRead 16 8 20 = true := by native_decide

theorem unsafeBpfOobRead_length_irrelevant (offset l1 l2 pktLen : Nat) :
    unsafeBpfOobRead offset l1 pktLen = unsafeBpfOobRead offset l2 pktLen := by
  simp [unsafeBpfOobRead]

theorem unsafeBpfOobRead_false_of_offset_ge (offset length pktLen : Nat) :
    offset ≥ pktLen → unsafeBpfOobRead offset length pktLen = false := by
  intro h
  simp [unsafeBpfOobRead, Nat.not_lt.mpr h]

theorem unsafeBpfOobRead_true_on_length_overflow (offset length pktLen : Nat) :
    offset + length > pktLen → offset < pktLen →
    unsafeBpfOobRead offset length pktLen = true := by
  intro _ h
  simp [unsafeBpfOobRead, h]

example (offset length pktLen : Nat)
    (_h1 : offset < pktLen) (_h2 : offset + length > pktLen) :
    (unsafeBpfOobRead offset length length = unsafeBpfOobRead offset length length) ∧
    (offset ≥ pktLen → unsafeBpfOobRead offset length pktLen = false) ∧
    (offset + length > pktLen → offset < pktLen →
      unsafeBpfOobRead offset length pktLen = true) :=
  ⟨unsafeBpfOobRead_length_irrelevant offset length length length,
   unsafeBpfOobRead_false_of_offset_ge offset length pktLen,
   unsafeBpfOobRead_true_on_length_overflow offset length pktLen⟩

end UnsafeBpfOobRead
end Gold
