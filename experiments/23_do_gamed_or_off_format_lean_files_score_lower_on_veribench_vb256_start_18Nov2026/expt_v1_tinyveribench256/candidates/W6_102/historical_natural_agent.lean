import Mathlib
namespace Agent

/-!
# Unsafe tainted pointer (RLBox sandboxing example)

A raw application pointer is copied verbatim into sandbox-visible memory. This
models the vulnerability, not a sanitizing repair. Python integers are unbounded
`Int`s, and a shared buffer is a `List Int`. Because Lean is pure, both versions
return `(success, finalBuffer)` to expose Python's mutation to the caller.
Negative slots are rejected rather than interpreted as Python negative indices.
All integer pointers and all lists are admissible, including null pointers,
negative pointers, empty buffers and invalid slots. No dereference is modeled.
-/

namespace UnsafeTaintedPtr

abbrev Result := Bool × List Int

/-- Validity of a signed slot, with the comparison performed in `Int`. -/
def ValidSlot (buf : List Int) (slot : Int) : Prop :=
  0 ≤ slot ∧ slot < (buf.length : Int)

instance (buf : List Int) (slot : Int) : Decidable (ValidSlot buf slot) :=
  inferInstanceAs (Decidable (0 ≤ slot ∧ slot < (buf.length : Int)))

/-- Functional translation: the new buffer explicitly represents the side effect. -/
def unsafeTaintedPtr (appPtr : Int) (sharedBuf : List Int) (slot : Int) : Result :=
  if ValidSlot sharedBuf slot then
    (true, sharedBuf.set slot.toNat appPtr)
  else
    (false, sharedBuf)

/-- Executable translation of Python's `check`: conjunction of its assertions.
The updated buffer from the third call is passed into the fourth call, just as
in Python. Buffer observations use `getElem?` to keep this checker total even
for a candidate that returns a buffer of the wrong length. -/
def check (candidate : Int → List Int → Int → Result) : Bool :=
  let appPtr : Int := 0x7FFF4A3B1C00
  let first := candidate appPtr (List.replicate 8 0) 0
  let second := candidate 0xDEADBEEF (List.replicate 4 0) 2
  let third := candidate appPtr (List.replicate 2 0) 5
  let fourth := candidate appPtr third.2 (-1)
  let fifth := candidate appPtr [] 0
  let sixth := candidate 0 (List.replicate 2 0xAA) 1
  first.1 && (first.2[0]? == some appPtr) &&
  second.1 && (second.2[2]? == some 0xDEADBEEF) &&
  (!third.1) && (!fourth.1) && (!fifth.1) &&
  sixth.1 && (sixth.2[1]? == some 0)

/-! ## Fixed tests corresponding to all six branches of the Python checker -/

example : unsafeTaintedPtr 0x7FFF4A3B1C00 (List.replicate 8 0) 0 =
    (true, [0x7FFF4A3B1C00, 0, 0, 0, 0, 0, 0, 0]) := by native_decide
example : unsafeTaintedPtr 0xDEADBEEF (List.replicate 4 0) 2 =
    (true, [0, 0, 0xDEADBEEF, 0]) := by native_decide
example : unsafeTaintedPtr 0x7FFF4A3B1C00 [0, 0] 5 =
    (false, [0, 0]) := by native_decide
example : unsafeTaintedPtr 0x7FFF4A3B1C00 [0, 0] (-1) =
    (false, [0, 0]) := by native_decide
example : unsafeTaintedPtr 0x7FFF4A3B1C00 [] 0 =
    (false, []) := by native_decide
example : unsafeTaintedPtr 0 [0xAA, 0xAA] 1 =
    (true, [0xAA, 0]) := by native_decide
-- Signed pointers are data, not indices, and must not be sanitized either.
example : unsafeTaintedPtr (-123) [1, 2] 0 = (true, [-123, 2]) := by native_decide
-- The upper bound is exclusive.
example : unsafeTaintedPtr 42 [1, 2] 2 = (false, [1, 2]) := by native_decide

example : check unsafeTaintedPtr = true := by native_decide
#eval check unsafeTaintedPtr
#eval if check unsafeTaintedPtr then "All tests passed." else "Candidate failed tests"

#eval unsafeTaintedPtr 0x7FFF4A3B1C00 (List.replicate 8 0) 0
#eval unsafeTaintedPtr 0xDEADBEEF (List.replicate 4 0) 2
#eval unsafeTaintedPtr 0x7FFF4A3B1C00 [0, 0] 5
#eval unsafeTaintedPtr 0x7FFF4A3B1C00 [0, 0] (-1)
#eval unsafeTaintedPtr 0x7FFF4A3B1C00 [] 0
#eval unsafeTaintedPtr 0 [0xAA, 0xAA] 1

/-! ## Preconditions and universally quantified properties -/

/-- There is no caller-side validity assumption: rejection is part of the API. -/
def Pre (_appPtr : Int) (_buf : List Int) (_slot : Int) : Prop := True

/-- Exactly the in-bounds nonnegative slots succeed. -/
def success_prop (appPtr : Int) (buf : List Int) (slot : Int) : Prop :=
  (unsafeTaintedPtr appPtr buf slot).1 = true ↔ ValidSlot buf slot

theorem success_thm (appPtr : Int) (buf : List Int) (slot : Int) :
    success_prop appPtr buf slot := by
  by_cases h : ValidSlot buf slot <;>
    simp [success_prop, unsafeTaintedPtr, h]

/-- Either kind of invalid index returns false without modifying the buffer. -/
def rejected_prop (appPtr : Int) (buf : List Int) (slot : Int) : Prop :=
  (slot < 0 ∨ (buf.length : Int) ≤ slot) →
    unsafeTaintedPtr appPtr buf slot = (false, buf)

theorem rejected_thm (appPtr : Int) (buf : List Int) (slot : Int) :
    rejected_prop appPtr buf slot := by
  intro h
  have hv : ¬ ValidSlot buf slot := by
    unfold ValidSlot
    omega
  simp [unsafeTaintedPtr, hv]

/-- Success writes exactly the original pointer, without zeroing or masking it. -/
def update_prop (appPtr : Int) (buf : List Int) (slot : Int) : Prop :=
  ValidSlot buf slot →
    unsafeTaintedPtr appPtr buf slot = (true, buf.set slot.toNat appPtr)

theorem update_thm (appPtr : Int) (buf : List Int) (slot : Int) :
    update_prop appPtr buf slot := by
  intro h
  simp [unsafeTaintedPtr, h]

/-- The operation never grows or shrinks shared memory. -/
def length_prop (appPtr : Int) (buf : List Int) (slot : Int) : Prop :=
  (unsafeTaintedPtr appPtr buf slot).2.length = buf.length

theorem length_thm (appPtr : Int) (buf : List Int) (slot : Int) :
    length_prop appPtr buf slot := by
  unfold length_prop unsafeTaintedPtr
  split <;> simp

/-- A sandbox reading the written slot obtains the complete raw application pointer. -/
def leak_prop (appPtr : Int) (buf : List Int) (slot : Int) : Prop :=
  ValidSlot buf slot → (unsafeTaintedPtr appPtr buf slot).2[slot.toNat]? = some appPtr

theorem leak_thm (appPtr : Int) (buf : List Int) (slot : Int) :
    leak_prop appPtr buf slot := by
  intro h
  have hn : slot.toNat < buf.length := by
    unfold ValidSlot at h
    omega
  simp [unsafeTaintedPtr, h, hn]

/-- All other cells are unchanged; the statement also covers out-of-range reads. -/
def frame_prop (appPtr : Int) (buf : List Int) (slot : Int) : Prop :=
  ∀ i : Nat, i ≠ slot.toNat →
    (unsafeTaintedPtr appPtr buf slot).2[i]? = buf[i]?

theorem frame_thm (appPtr : Int) (buf : List Int) (slot : Int) :
    frame_prop appPtr buf slot := by
  intro i hi
  unfold unsafeTaintedPtr
  split <;> simp [Ne.symm hi]

/-- Complete observable contract, including the intentionally unsafe disclosure. -/
def Post_prop (appPtr : Int) (buf : List Int) (slot : Int) : Prop :=
  success_prop appPtr buf slot ∧
  rejected_prop appPtr buf slot ∧
  update_prop appPtr buf slot ∧
  length_prop appPtr buf slot ∧
  leak_prop appPtr buf slot ∧
  frame_prop appPtr buf slot

/-! ## Bounded property-based tests

Exhaustive products of short, nonuniform buffers, signed and large pointers, and
slots on both sides of each boundary. The Boolean predicates below are executable
forms of the named properties, not substitutes for their universal proofs. For
the frame property we also sample indices beyond the end of the buffer.
-/

private def buffersOfLength : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (buffersOfLength n).flatMap fun xs =>
      ([-2, 0, 0xAA] : List Int).map fun x => x :: xs

private def testBuffers : List (List Int) :=
  (List.range 5).flatMap buffersOfLength

private def testPointers : List Int :=
  [-0x7FFF4A3B1C00, -1, 0, 1, 0xAA, 0xDEADBEEF, 0x7FFF4A3B1C00]

private def testSlots : List Int :=
  (List.range 11).map fun n => (n : Int) - 3

private def boundedCheck (p : Int → List Int → Int → Bool) : Bool :=
  testPointers.all fun appPtr =>
    testBuffers.all fun buf => testSlots.all fun slot => p appPtr buf slot

private def successCheck (appPtr : Int) (buf : List Int) (slot : Int) : Bool :=
  (unsafeTaintedPtr appPtr buf slot).1 == decide (ValidSlot buf slot)

private def rejectedCheck (appPtr : Int) (buf : List Int) (slot : Int) : Bool :=
  if slot < 0 ∨ (buf.length : Int) ≤ slot then
    unsafeTaintedPtr appPtr buf slot == (false, buf)
  else true

private def updateCheck (appPtr : Int) (buf : List Int) (slot : Int) : Bool :=
  if ValidSlot buf slot then
    unsafeTaintedPtr appPtr buf slot == (true, buf.set slot.toNat appPtr)
  else true

private def lengthCheck (appPtr : Int) (buf : List Int) (slot : Int) : Bool :=
  (unsafeTaintedPtr appPtr buf slot).2.length == buf.length

private def leakCheck (appPtr : Int) (buf : List Int) (slot : Int) : Bool :=
  if ValidSlot buf slot then
    (unsafeTaintedPtr appPtr buf slot).2[slot.toNat]? == some appPtr
  else true

private def frameCheck (appPtr : Int) (buf : List Int) (slot : Int) : Bool :=
  (List.range (buf.length + 3)).all fun i =>
    if i ≠ slot.toNat then (unsafeTaintedPtr appPtr buf slot).2[i]? == buf[i]?
    else true

private def postCheck (appPtr : Int) (buf : List Int) (slot : Int) : Bool :=
  successCheck appPtr buf slot && rejectedCheck appPtr buf slot &&
  updateCheck appPtr buf slot && lengthCheck appPtr buf slot &&
  leakCheck appPtr buf slot && frameCheck appPtr buf slot

-- PBT: success_prop.
example : boundedCheck successCheck = true := by native_decide
-- PBT: rejected_prop (both negative and too-large indices).
example : boundedCheck rejectedCheck = true := by native_decide
-- PBT: update_prop.
example : boundedCheck updateCheck = true := by native_decide
-- PBT: length_prop.
example : boundedCheck lengthCheck = true := by native_decide
-- PBT: leak_prop (including null, negative and address-sized pointers).
example : boundedCheck leakCheck = true := by native_decide
-- PBT: frame_prop, with bounded observation indices.
example : boundedCheck frameCheck = true := by native_decide
-- PBT: the complete Post_prop, with no inputs excluded by Pre.
example : boundedCheck postCheck = true := by native_decide

#eval (boundedCheck successCheck, boundedCheck rejectedCheck,
  boundedCheck updateCheck, boundedCheck lengthCheck,
  boundedCheck leakCheck, boundedCheck frameCheck, boundedCheck postCheck)

/-! ## Correctness on the full Python input domain -/

theorem correctness_thm (appPtr : Int) (buf : List Int) (slot : Int) :
    Pre appPtr buf slot → Post_prop appPtr buf slot := by
  intro _
  exact ⟨success_thm appPtr buf slot, rejected_thm appPtr buf slot,
    update_thm appPtr buf slot, length_thm appPtr buf slot,
    leak_thm appPtr buf slot, frame_thm appPtr buf slot⟩

/-! ## Imperative translation with mutable shared-buffer state -/

/-- Mirrors Python's early rejection followed by a mutable, verbatim store. -/
def unsafeTaintedPtrImperative (appPtr : Int) (sharedBuf : List Int)
    (slot : Int) : Result := Id.run do
  let mut buf := sharedBuf
  if slot < 0 ∨ (buf.length : Int) ≤ slot then
    return (false, buf)
  buf := buf.set slot.toNat appPtr
  return (true, buf)

example : unsafeTaintedPtrImperative 0x7FFF4A3B1C00 (List.replicate 8 0) 0 =
    (true, [0x7FFF4A3B1C00, 0, 0, 0, 0, 0, 0, 0]) := by native_decide
example : unsafeTaintedPtrImperative 0xDEADBEEF (List.replicate 4 0) 2 =
    (true, [0, 0, 0xDEADBEEF, 0]) := by native_decide
example : unsafeTaintedPtrImperative 0x7FFF4A3B1C00 [0, 0] 5 =
    (false, [0, 0]) := by native_decide
example : unsafeTaintedPtrImperative 0x7FFF4A3B1C00 [0, 0] (-1) =
    (false, [0, 0]) := by native_decide
example : unsafeTaintedPtrImperative 0x7FFF4A3B1C00 [] 0 =
    (false, []) := by native_decide
example : unsafeTaintedPtrImperative 0 [0xAA, 0xAA] 1 =
    (true, [0xAA, 0]) := by native_decide

example : check unsafeTaintedPtrImperative = true := by native_decide
#eval check unsafeTaintedPtrImperative

#eval unsafeTaintedPtrImperative 0x7FFF4A3B1C00 (List.replicate 8 0) 0
#eval unsafeTaintedPtrImperative 0 [0xAA, 0xAA] 1
example : boundedCheck (fun p b s =>
    unsafeTaintedPtr p b s == unsafeTaintedPtrImperative p b s) = true := by
  native_decide
#eval boundedCheck (fun p b s =>
  unsafeTaintedPtr p b s == unsafeTaintedPtrImperative p b s)

/-- Equality includes both the return value and the entire final shared buffer. -/
theorem functional_imperative_equiv (appPtr : Int) (buf : List Int) (slot : Int) :
    unsafeTaintedPtr appPtr buf slot = unsafeTaintedPtrImperative appPtr buf slot := by
  by_cases h : ValidSlot buf slot
  · have hn : ¬ (slot < 0 ∨ (buf.length : Int) ≤ slot) := by
      unfold ValidSlot at h
      omega
    simp [unsafeTaintedPtr, unsafeTaintedPtrImperative, h, hn]
  · have hn : slot < 0 ∨ (buf.length : Int) ≤ slot := by
      unfold ValidSlot at h
      omega
    simp [unsafeTaintedPtr, unsafeTaintedPtrImperative, h, hn]

end UnsafeTaintedPtr
end Agent
