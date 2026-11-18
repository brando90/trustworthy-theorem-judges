import Mathlib
namespace Gold
namespace UnsafePrivilegeDrop

def unsafePrivilegeDrop (currentUid : Nat) (_initDone : Bool) : Nat :=
  currentUid

example : unsafePrivilegeDrop 0 true = 0 := by native_decide
example : unsafePrivilegeDrop 1000 true = 1000 := by native_decide
example : unsafePrivilegeDrop 0 false = 0 := by native_decide
example : unsafePrivilegeDrop 500 false = 500 := by native_decide
example : unsafePrivilegeDrop 33 true = 33 := by native_decide
example : unsafePrivilegeDrop 65534 false = 65534 := by native_decide
example : unsafePrivilegeDrop 1000 false = 1000 := by native_decide

theorem unsafePrivilegeDrop_eq_self (currentUid : Nat) (initDone : Bool) :
    unsafePrivilegeDrop currentUid initDone = currentUid := by
  simp [unsafePrivilegeDrop]

theorem unsafePrivilegeDrop_never_reaches_other (currentUid : Nat) (initDone : Bool)
    (targetUid : Nat) (h : currentUid ≠ targetUid) :
    unsafePrivilegeDrop currentUid initDone ≠ targetUid := by
  simp only [unsafePrivilegeDrop]
  exact h

theorem root_retained_after_init (currentUid : Nat) (initDone : Bool)
    (hUid : currentUid = 0) (_hInit : initDone = true) :
    unsafePrivilegeDrop currentUid initDone = 0 := by
  simp [unsafePrivilegeDrop, hUid]

example (currentUid : Nat) (initDone : Bool) :
    currentUid = 0 → initDone = true → unsafePrivilegeDrop 0 true = 0 := by
  intro _ _
  simp [unsafePrivilegeDrop]

end UnsafePrivilegeDrop
end Gold
