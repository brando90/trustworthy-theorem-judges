import Mathlib

namespace Gold
namespace SafeHeapSpraying

def safeHeapValidate (addr heapBase heapSize : Nat) : Bool :=
  heapBase ≤ addr && addr < heapBase + heapSize

example : safeHeapValidate 120 100 50 = true := by native_decide
example : safeHeapValidate 0 100 50 = false := by native_decide
example : safeHeapValidate 100 100 50 = true := by native_decide
example : safeHeapValidate 150 100 50 = false := by native_decide
example : safeHeapValidate 125 100 50 = true := by native_decide
example : safeHeapValidate 200 100 50 = false := by native_decide

theorem safeHeapValidate_accepts_in_range (addr heapBase heapSize : Nat)
    (hlo : heapBase ≤ addr) (hhi : addr < heapBase + heapSize) :
    safeHeapValidate addr heapBase heapSize = true := by
  simp [safeHeapValidate, hlo, hhi]

theorem safeHeapValidate_rejects_out_of_range (addr heapBase heapSize : Nat)
    (h : addr < heapBase ∨ addr ≥ heapBase + heapSize) :
    safeHeapValidate addr heapBase heapSize = false := by
  simp [safeHeapValidate]
  omega

theorem safeHeapValidate_eq_true_iff (addr heapBase heapSize : Nat) :
    safeHeapValidate addr heapBase heapSize = true ↔
    (heapBase ≤ addr ∧ addr < heapBase + heapSize) := by
  simp [safeHeapValidate]

end SafeHeapSpraying
end Gold
