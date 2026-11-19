import Mathlib
namespace Agent

/-!
# Unsafe stack-canary write

A direct, integer-valued model of the Python program.  A stack frame is the
buffer followed by the initial canary `0xDEAD`.  The write is guarded only by
membership in the *frame*, not membership in the buffer.  Thus writing at the
buffer length overwrites the canary, even when the buffer is empty.  Negative
indices and indices beyond the frame are ignored, as in the explicit Python
guard (not Python's usual negative-index assignment convention).

All integers and all finite integer buffers are admissible.  The specification
will describe the vulnerability, not assert that the canary is always safe.
-/

namespace UnsafeStackCanary

/-- The initial canary, 57005 in decimal. -/
def CANARY_VALUE : Int := 0xDEAD

/-- Functional translation: copy the buffer, append the canary, possibly update
one slot of the frame, and split the last slot back off. -/
def unsafeStackCanary (buf : List Int) (writeIndex value : Int) : List Int × Int :=
  let frame := buf ++ [CANARY_VALUE]
  let written :=
    if 0 ≤ writeIndex ∧ writeIndex < (frame.length : Int) then
      frame.set writeIndex.toNat value
    else frame
  (written.dropLast, written.getLast!)

/-- Boolean rendering of the assertions in Python's `check` harness. -/
def check (candidate : List Int → Int → Int → List Int × Int) : Bool :=
  let r1 := candidate [0, 0, 0] 1 42
  let r2 := candidate [0, 0, 0] 3 0xBEEF
  let r3 := candidate [1, 2, 3] 2 99
  let r4 := candidate [10, 20] 0 7
  let r5 := candidate [] 0 0xFF
  r1.1 == [0, 42, 0] && r1.2 == CANARY_VALUE &&
  r2.2 == 0xBEEF &&
  r3.1 == [1, 2, 99] && r3.2 == CANARY_VALUE &&
  r4.1 == [7, 20] && r4.2 == CANARY_VALUE && r5.2 == 0xFF

example : check unsafeStackCanary = true := by native_decide
#eval if check unsafeStackCanary then "All tests passed." else "Candidate failed tests"

-- The five checks in the Python test harness (including the returned buffers).
example : unsafeStackCanary [0, 0, 0] 1 42 = ([0, 42, 0], CANARY_VALUE) := by
  native_decide
example : unsafeStackCanary [0, 0, 0] 3 0xBEEF = ([0, 0, 0], 0xBEEF) := by
  native_decide
example : unsafeStackCanary [1, 2, 3] 2 99 = ([1, 2, 99], CANARY_VALUE) := by
  native_decide
example : unsafeStackCanary [10, 20] 0 7 = ([7, 20], CANARY_VALUE) := by
  native_decide
example : unsafeStackCanary [] 0 0xFF = ([], 0xFF) := by
  native_decide
-- The Python guard also covers these cases, although its harness omits them.
example : unsafeStackCanary [10, 20] (-1) 7 = ([10, 20], CANARY_VALUE) := by
  native_decide
example : unsafeStackCanary [10, 20] 3 7 = ([10, 20], CANARY_VALUE) := by
  native_decide
example : unsafeStackCanary [] (-1) 7 = ([], CANARY_VALUE) := by
  native_decide
example : unsafeStackCanary [] 1 7 = ([], CANARY_VALUE) := by
  native_decide
#eval unsafeStackCanary [0, 0, 0] 1 42
#eval unsafeStackCanary [0, 0, 0] 3 0xBEEF
#eval unsafeStackCanary [1, 2, 3] 2 99
#eval unsafeStackCanary [10, 20] 0 7
#eval unsafeStackCanary [] 0 0xFF

/-- No safety assumption: the unsafe boundary write is part of the domain. -/
def Pre (_buf : List Int) (_writeIndex _value : Int) : Prop := True

/-- Complete, disjoint description of the program's three cases. -/
def semantics_prop (buf : List Int) (i value : Int) : Prop :=
  unsafeStackCanary buf i value =
    if 0 ≤ i ∧ i < (buf.length : Int) then
      (buf.set i.toNat value, CANARY_VALUE)
    else if i = (buf.length : Int) then (buf, value)
    else (buf, CANARY_VALUE)

theorem semantics_thm (buf : List Int) (i value : Int) :
    semantics_prop buf i value := by
  unfold semantics_prop unsafeStackCanary
  simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
  by_cases hin : 0 ≤ i ∧ i < (buf.length : Int)
  · have hg : 0 ≤ i ∧ i < (buf.length : Int) + 1 := by omega
    have hn : i.toNat < buf.length := by omega
    simp [hin, hg, List.set_append_left, hn]
  · by_cases heq : i = (buf.length : Int)
    · subst i
      simp [List.set_append_right]
    · have hg : ¬ (0 ≤ i ∧ i < (buf.length : Int) + 1) := by omega
      simp [hin, heq, hg]

/-- Exact buffer contents, including unchanged out-of-buffer writes. -/
def buffer_prop (buf : List Int) (i value : Int) : Prop :=
  (unsafeStackCanary buf i value).1 =
    if 0 ≤ i ∧ i < (buf.length : Int) then buf.set i.toNat value else buf

theorem buffer_thm (buf : List Int) (i value : Int) :
    buffer_prop buf i value := by
  have hs := semantics_thm buf i value
  unfold semantics_prop at hs
  unfold buffer_prop
  rw [hs]
  split_ifs <;> rfl

/-- Exact canary value: the vulnerable boundary is the only write that hits it. -/
def canary_prop (buf : List Int) (i value : Int) : Prop :=
  (unsafeStackCanary buf i value).2 =
    if i = (buf.length : Int) then value else CANARY_VALUE

theorem canary_thm (buf : List Int) (i value : Int) :
    canary_prop buf i value := by
  have hs := semantics_thm buf i value
  unfold semantics_prop at hs
  unfold canary_prop
  rw [hs]
  by_cases hin : 0 ≤ i ∧ i < (buf.length : Int)
  · have heq : i ≠ (buf.length : Int) := by omega
    simp [hin, heq]
  · simp only [if_neg hin]
    split_ifs <;> rfl

/-- Writes never change the number of buffer slots. -/
def length_prop (buf : List Int) (i value : Int) : Prop :=
  (unsafeStackCanary buf i value).1.length = buf.length

theorem length_thm (buf : List Int) (i value : Int) :
    length_prop buf i value := by
  have hb := buffer_thm buf i value
  unfold buffer_prop at hb
  unfold length_prop
  rw [hb]
  split_ifs <;> simp

/-- A normal write changes the requested buffer slot and keeps the canary. -/
def inBounds_prop (buf : List Int) (i value : Int) : Prop :=
  0 ≤ i ∧ i < (buf.length : Int) →
    unsafeStackCanary buf i value = (buf.set i.toNat value, CANARY_VALUE)

theorem inBounds_thm (buf : List Int) (i value : Int) :
    inBounds_prop buf i value := by
  intro hin
  simpa [semantics_prop, hin] using semantics_thm buf i value

/-- The vulnerability: index `length` writes the canary, not the buffer.
This remains true for the empty buffer and for any integer write value. -/
def boundary_prop (buf : List Int) (i value : Int) : Prop :=
  i = (buf.length : Int) → unsafeStackCanary buf i value = (buf, value)

theorem boundary_thm (buf : List Int) (i value : Int) :
    boundary_prop buf i value := by
  intro heq
  subst i
  simpa [semantics_prop] using semantics_thm buf (buf.length : Int) value

/-- The explicit Python guard rejects negative and oversized indices. -/
def outOfBounds_prop (buf : List Int) (i value : Int) : Prop :=
  i < 0 ∨ (buf.length : Int) < i →
    unsafeStackCanary buf i value = (buf, CANARY_VALUE)

theorem outOfBounds_thm (buf : List Int) (i value : Int) :
    outOfBounds_prop buf i value := by
  intro hout
  have hin : ¬ (0 ≤ i ∧ i < (buf.length : Int)) := by omega
  have heq : i ≠ (buf.length : Int) := by omega
  simpa [semantics_prop, hin, heq] using semantics_thm buf i value

/-- Reading back a valid buffer write returns the supplied value. -/
def writtenSlot_prop (buf : List Int) (i value : Int) : Prop :=
  0 ≤ i ∧ i < (buf.length : Int) →
    (unsafeStackCanary buf i value).1[i.toNat]? = some value

theorem writtenSlot_thm (buf : List Int) (i value : Int) :
    writtenSlot_prop buf i value := by
  intro hin
  have hb := buffer_thm buf i value
  unfold buffer_prop at hb
  rw [hb]
  have hn : i.toNat < buf.length := by omega
  simp [hin, hn]

/-- Every other buffer slot is unchanged. Optional lookup also covers slots
outside the buffer, so the observer index has no hidden bounds assumption. -/
def otherSlots_prop (buf : List Int) (i value : Int) : Prop :=
  ∀ j : Nat, (j : Int) ≠ i →
    (unsafeStackCanary buf i value).1[j]? = buf[j]?

theorem otherSlots_thm (buf : List Int) (i value : Int) :
    otherSlots_prop buf i value := by
  intro j hji
  have hb := buffer_thm buf i value
  unfold buffer_prop at hb
  rw [hb]
  split_ifs with hin
  · apply List.getElem?_set_ne
    omega
  · rfl

/-- Exact characterization of observable corruption. Writing the original
canary value at the boundary overwrites it but does not change its value. -/
def corruption_prop (buf : List Int) (i value : Int) : Prop :=
  (unsafeStackCanary buf i value).2 ≠ CANARY_VALUE ↔
    i = (buf.length : Int) ∧ value ≠ CANARY_VALUE

theorem corruption_thm (buf : List Int) (i value : Int) :
    corruption_prop buf i value := by
  have hc := canary_thm buf i value
  unfold canary_prop at hc
  unfold corruption_prop
  rw [hc]
  by_cases heq : i = (buf.length : Int) <;> simp [heq]

/-- Full empty-buffer behavior, not just the one concrete exploit test. -/
def empty_prop (buf : List Int) (i value : Int) : Prop :=
  buf = [] → unsafeStackCanary buf i value =
    ([], if i = 0 then value else CANARY_VALUE)

theorem empty_thm (buf : List Int) (i value : Int) :
    empty_prop buf i value := by
  intro heq
  subst buf
  have hs := semantics_thm [] i value
  have hin : ¬ (0 ≤ i ∧ i < (0 : Int)) := by omega
  by_cases hz : i = 0 <;> simpa [semantics_prop, hin, hz] using hs

/-- The postcondition records both normal operation and the unsafe behavior. -/
def Post_prop (buf : List Int) (i value : Int) : Prop :=
  semantics_prop buf i value ∧
  buffer_prop buf i value ∧
  canary_prop buf i value ∧
  length_prop buf i value ∧
  inBounds_prop buf i value ∧
  boundary_prop buf i value ∧
  outOfBounds_prop buf i value ∧
  writtenSlot_prop buf i value ∧
  otherSlots_prop buf i value ∧
  corruption_prop buf i value ∧
  empty_prop buf i value

/-! ## Property-based tests

These are bounded exhaustive tests, not proofs of the general theorems.
We enumerate all buffers of lengths 0 through 4 over `[-2, 0, 3]`, plus the
nonzero buffers in the source tests. For each buffer, we test indices from
`-2` through `length + 2`, as well as `-100` and `100`. Values include negative
integers, ordinary values, the initial canary, and both exploit values.
Every `_prop` above, including `Post_prop`, has its own Boolean-form PBT.
-/

private def buffersOfLength : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => ([-2, 0, 3] : List Int).flatMap fun x =>
      (buffersOfLength n).map (fun xs => x :: xs)

private def testBuffers : List (List Int) :=
  (List.range 5).flatMap buffersOfLength ++ [[1, 2, 3], [10, 20]]

private def testValues : List Int := [-2, -1, 0, 1, 42, 0xFF, CANARY_VALUE, 0xBEEF]

private def allSmallCases (p : List Int → Int → Int → Bool) : Bool :=
  testBuffers.all fun buf =>
    ([-100, 100] ++ (List.range (buf.length + 5)).map (fun n => (n : Int) - 2)).all
      fun i => testValues.all fun value => p buf i value

private def semanticsCheck (buf : List Int) (i value : Int) : Bool :=
  unsafeStackCanary buf i value ==
    (if 0 ≤ i ∧ i < (buf.length : Int) then (buf.set i.toNat value, CANARY_VALUE)
     else if i = (buf.length : Int) then (buf, value) else (buf, CANARY_VALUE))
private def bufferCheck (buf : List Int) (i value : Int) : Bool :=
  (unsafeStackCanary buf i value).1 ==
    (if 0 ≤ i ∧ i < (buf.length : Int) then buf.set i.toNat value else buf)
private def canaryCheck (buf : List Int) (i value : Int) : Bool :=
  (unsafeStackCanary buf i value).2 ==
    (if i = (buf.length : Int) then value else CANARY_VALUE)
private def lengthCheck (buf : List Int) (i value : Int) : Bool :=
  (unsafeStackCanary buf i value).1.length == buf.length
private def inBoundsCheck (buf : List Int) (i value : Int) : Bool :=
  !decide (0 ≤ i ∧ i < (buf.length : Int)) ||
    unsafeStackCanary buf i value == (buf.set i.toNat value, CANARY_VALUE)
private def boundaryCheck (buf : List Int) (i value : Int) : Bool :=
  !(i == (buf.length : Int)) || unsafeStackCanary buf i value == (buf, value)
private def outOfBoundsCheck (buf : List Int) (i value : Int) : Bool :=
  !decide (i < 0 ∨ (buf.length : Int) < i) ||
    unsafeStackCanary buf i value == (buf, CANARY_VALUE)
private def writtenSlotCheck (buf : List Int) (i value : Int) : Bool :=
  !decide (0 ≤ i ∧ i < (buf.length : Int)) ||
    (unsafeStackCanary buf i value).1[i.toNat]? == some value
private def otherSlotsCheck (buf : List Int) (i value : Int) : Bool :=
  -- This PBT bounds the observer index; the theorem quantifies over every Nat.
  (List.range (buf.length + 2)).all fun j =>
    (j : Int) == i || (unsafeStackCanary buf i value).1[j]? == buf[j]?
private def corruptionCheck (buf : List Int) (i value : Int) : Bool :=
  ((unsafeStackCanary buf i value).2 != CANARY_VALUE) ==
    ((i == (buf.length : Int)) && (value != CANARY_VALUE))
private def emptyCheck (buf : List Int) (i value : Int) : Bool :=
  !(buf == []) ||
    unsafeStackCanary buf i value == ([], if i = 0 then value else CANARY_VALUE)
private def postCheck (buf : List Int) (i value : Int) : Bool :=
  semanticsCheck buf i value && bufferCheck buf i value &&
  canaryCheck buf i value && lengthCheck buf i value &&
  inBoundsCheck buf i value && boundaryCheck buf i value &&
  outOfBoundsCheck buf i value && writtenSlotCheck buf i value &&
  otherSlotsCheck buf i value && corruptionCheck buf i value && emptyCheck buf i value

-- PBT: semantics_prop
example : allSmallCases semanticsCheck = true := by native_decide
-- PBT: buffer_prop
example : allSmallCases bufferCheck = true := by native_decide
-- PBT: canary_prop
example : allSmallCases canaryCheck = true := by native_decide
-- PBT: length_prop
example : allSmallCases lengthCheck = true := by native_decide
-- PBT: inBounds_prop
example : allSmallCases inBoundsCheck = true := by native_decide
-- PBT: boundary_prop
example : allSmallCases boundaryCheck = true := by native_decide
-- PBT: outOfBounds_prop
example : allSmallCases outOfBoundsCheck = true := by native_decide
-- PBT: writtenSlot_prop
example : allSmallCases writtenSlotCheck = true := by native_decide
-- PBT: otherSlots_prop
example : allSmallCases otherSlotsCheck = true := by native_decide
-- PBT: corruption_prop
example : allSmallCases corruptionCheck = true := by native_decide
-- PBT: empty_prop
example : allSmallCases emptyCheck = true := by native_decide
-- PBT: Post_prop (the conjunction of all the executable checks above).
example : allSmallCases postCheck = true := by native_decide
#eval ("All bounded postcondition tests passed", allSmallCases postCheck)

/-- Kernel-checked correctness on the full Python input domain. -/
theorem correctness_thm (buf : List Int) (i value : Int) :
    Pre buf i value → Post_prop buf i value := by
  intro _
  exact ⟨semantics_thm buf i value, buffer_thm buf i value,
    canary_thm buf i value, length_thm buf i value,
    inBounds_thm buf i value, boundary_thm buf i value,
    outOfBounds_thm buf i value, writtenSlot_thm buf i value,
    otherSlots_thm buf i value, corruption_thm buf i value, empty_thm buf i value⟩

/-- Imperative translation with the same frame mutation as the Python source. -/
def unsafeStackCanaryImperative (buf : List Int) (writeIndex value : Int) :
    List Int × Int := Id.run do
  let mut frame := buf ++ [CANARY_VALUE]
  if 0 ≤ writeIndex ∧ writeIndex < (frame.length : Int) then
    frame := frame.set writeIndex.toNat value
  let canary := frame.getLast!
  return (frame.dropLast, canary)

example : check unsafeStackCanaryImperative = true := by native_decide
example : unsafeStackCanaryImperative [0, 0, 0] 1 42 =
    ([0, 42, 0], CANARY_VALUE) := by native_decide
example : unsafeStackCanaryImperative [0, 0, 0] 3 0xBEEF =
    ([0, 0, 0], 0xBEEF) := by native_decide
example : unsafeStackCanaryImperative [1, 2, 3] 2 99 =
    ([1, 2, 99], CANARY_VALUE) := by native_decide
example : unsafeStackCanaryImperative [10, 20] 0 7 =
    ([7, 20], CANARY_VALUE) := by native_decide
example : unsafeStackCanaryImperative [] 0 0xFF = ([], 0xFF) := by native_decide
example : unsafeStackCanaryImperative [10, 20] (-1) 7 =
    ([10, 20], CANARY_VALUE) := by native_decide
example : unsafeStackCanaryImperative [10, 20] 3 7 =
    ([10, 20], CANARY_VALUE) := by native_decide
#eval if check unsafeStackCanaryImperative then "All imperative tests passed."
  else "Imperative candidate failed tests"
#eval unsafeStackCanaryImperative [] 0 0xFF
example : allSmallCases (fun buf i value =>
    unsafeStackCanary buf i value == unsafeStackCanaryImperative buf i value) = true := by
  native_decide

/-- Functional and mutable implementations agree for every input, including
negative indices, empty buffers, canary writes, and oversized indices. -/
theorem equivalence_thm (buf : List Int) (i value : Int) :
    unsafeStackCanary buf i value = unsafeStackCanaryImperative buf i value := by
  by_cases hg : 0 ≤ i ∧ i < (buf.length : Int) + 1 <;>
    simp [unsafeStackCanary, unsafeStackCanaryImperative, hg]

end UnsafeStackCanary
end Agent
