import Mathlib

namespace Gold
namespace SafeExecStack

def safeExecStack (addr stackStart stackEnd : Nat) : Bool :=
  !(stackStart ≤ addr && addr < stackEnd)

example : safeExecStack 0x08048000 0x7FFF0000 0x7FFFFFFF = true := by native_decide
#eval safeExecStack 0x08048000 0x7FFF0000 0x7FFFFFFF -- expected: true

example : safeExecStack 0x7FFF1234 0x7FFF0000 0x7FFFFFFF = false := by native_decide
#eval safeExecStack 0x7FFF1234 0x7FFF0000 0x7FFFFFFF -- expected: false

example : safeExecStack 0x7FFF0000 0x7FFF0000 0x7FFFFFFF = false := by native_decide
#eval safeExecStack 0x7FFF0000 0x7FFF0000 0x7FFFFFFF -- expected: false

example : safeExecStack 0x7FFFFFFF 0x7FFF0000 0x7FFFFFFF = true := by native_decide
#eval safeExecStack 0x7FFFFFFF 0x7FFF0000 0x7FFFFFFF -- expected: true

example : safeExecStack 50 100 200 = true := by native_decide
#eval safeExecStack 50 100 200 -- expected: true

example : safeExecStack 250 100 200 = true := by native_decide
#eval safeExecStack 250 100 200 -- expected: true

example : safeExecStack 100 100 200 = false := by native_decide
#eval safeExecStack 100 100 200 -- expected: false

example : safeExecStack 150 100 200 = false := by native_decide
#eval safeExecStack 150 100 200 -- expected: false

theorem safeExecStack_true_of_not_mem (addr stackStart stackEnd : Nat)
    (h : ¬(stackStart ≤ addr ∧ addr < stackEnd)) :
    safeExecStack addr stackStart stackEnd = true := by
  unfold safeExecStack
  cases hle : decide (stackStart ≤ addr) <;> simp_all

theorem safeExecStack_false_of_mem (addr stackStart stackEnd : Nat)
    (h : stackStart ≤ addr ∧ addr < stackEnd) :
    safeExecStack addr stackStart stackEnd = false := by
  obtain ⟨hlo, hhi⟩ := h
  simp [safeExecStack, hlo, hhi]

theorem safeExecStack_eq_true_iff (addr stackStart stackEnd : Nat) :
    safeExecStack addr stackStart stackEnd = true ↔
      ¬(stackStart ≤ addr ∧ addr < stackEnd) := by
  constructor
  · intro h hIn
    have := safeExecStack_false_of_mem addr stackStart stackEnd hIn
    rw [this] at h
    exact absurd h (by decide)
  · exact safeExecStack_true_of_not_mem addr stackStart stackEnd

end SafeExecStack
end Gold
