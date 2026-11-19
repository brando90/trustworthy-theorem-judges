import Mathlib
namespace Agent

/-!
# Bytewise copying, including buffer overflow

`Buffer` represents a Python bytearray.  `CopyResult.buffer` is its state after
execution; `indexError = true` represents the Python IndexError exception, not a
successful return.  A successful Python call returns None; only its mutation is
recorded here.  In particular, an exception does NOT roll back earlier writes.
Inputs describe the bytearrays at entry; a self-copy also has the same behavior.
-/
namespace UnsafeCopy

abbrev Buffer := List UInt8

@[ext] structure CopyResult where
  buffer : Buffer
  indexError : Bool
  deriving DecidableEq, Repr

/-- Visit successive source bytes, replacing destination bytes until the first
out-of-bounds write. Unvisited destination bytes are left unchanged. -/
def unsafeCopy : Buffer → Buffer → CopyResult
  | dst, [] => ⟨dst, false⟩
  | [], _ :: _ => ⟨[], true⟩
  | _ :: dst, b :: src =>
    let r := unsafeCopy dst src
    ⟨b :: r.buffer, r.indexError⟩

/-- Executable counterpart of Python's `check`: unexpected exceptions fail the
normal cases; the two overflow cases require IndexError. -/
def check (candidate : Buffer → Buffer → CopyResult) : Bool :=
  let r1 := candidate [0, 0, 0] [97, 98, 99]
  let r2 := candidate [0, 0] [120, 121]
  let r3 := candidate [0, 0] [49, 50, 51]
  let r4 := candidate [104, 101, 108, 108, 111] []
  let r5 := candidate [] [122]
  !r1.indexError && r1.buffer == [97, 98, 99] &&
  !r2.indexError && r2.buffer == [120, 121] && r3.indexError &&
  !r4.indexError && r4.buffer == [104, 101, 108, 108, 111] && r5.indexError

-- The five tests from the Python `check` function.
example : unsafeCopy [0, 0, 0] [97, 98, 99] = ⟨[97, 98, 99], false⟩ := by native_decide
example : unsafeCopy [0, 0] [120, 121] = ⟨[120, 121], false⟩ := by native_decide
example : unsafeCopy [0, 0] [49, 50, 51] = ⟨[49, 50], true⟩ := by native_decide
example : unsafeCopy [104, 101, 108, 108, 111] [] =
    ⟨[104, 101, 108, 108, 111], false⟩ := by native_decide
example : unsafeCopy [] [122] = ⟨[], true⟩ := by native_decide
-- Strictly shorter source: the untouched suffix is observable.
example : unsafeCopy [10, 20, 30, 40] [1, 2] = ⟨[1, 2, 30, 40], false⟩ := by native_decide
example : check unsafeCopy = true := by native_decide
#eval if check unsafeCopy then "All tests passed." else "Tests failed."
#eval unsafeCopy [0, 0, 0] [97, 98, 99]
#eval unsafeCopy [0, 0] [49, 50, 51]
#eval unsafeCopy [104, 101, 108, 108, 111] []
#eval unsafeCopy [] [122]

/-- Every pair of bytearrays is admissible; overflow is behavior, not a violated
precondition. UInt8 already restricts every element to a Python byte. -/
def Pre (_dst _src : Buffer) : Prop := True

/-- The resulting buffer contains precisely the writes that were reached. -/
def contents_prop (dst src : Buffer) : Prop :=
  (unsafeCopy dst src).buffer = src.take dst.length ++ dst.drop src.length

/-- IndexError occurs exactly when a source byte has no destination slot. -/
def overflow_prop (dst src : Buffer) : Prop :=
  (unsafeCopy dst src).indexError = decide (dst.length < src.length)

/-- Even an exceptional call cannot change the allocated length. -/
def length_prop (dst src : Buffer) : Prop :=
  (unsafeCopy dst src).buffer.length = dst.length

/-- Successful calls copy the whole source and preserve the remaining suffix. -/
def safe_prop (dst src : Buffer) : Prop :=
  src.length ≤ dst.length →
    unsafeCopy dst src = ⟨src ++ dst.drop src.length, false⟩

/-- On failure, all in-bounds writes precede the first failed write. -/
def failure_prop (dst src : Buffer) : Prop :=
  dst.length < src.length →
    unsafeCopy dst src = ⟨src.take dst.length, true⟩

/-- Copying an empty source never touches the destination. -/
def empty_prop (dst : Buffer) : Prop :=
  unsafeCopy dst [] = ⟨dst, false⟩

/-- An exact fit replaces the destination completely, without an exception. -/
def exact_prop (dst src : Buffer) : Prop :=
  src.length = dst.length → unsafeCopy dst src = ⟨src, false⟩

theorem contents_thm (dst src : Buffer) : contents_prop dst src := by
  unfold contents_prop
  induction dst generalizing src with
  | nil => cases src <;> simp [unsafeCopy]
  | cons d dst ih =>
    cases src with
    | nil => simp [unsafeCopy]
    | cons b src => simpa [unsafeCopy] using congrArg (List.cons b) (ih src)

theorem overflow_thm (dst src : Buffer) : overflow_prop dst src := by
  unfold overflow_prop
  induction dst generalizing src with
  | nil => cases src <;> simp [unsafeCopy]
  | cons d dst ih =>
    cases src with
    | nil => simp [unsafeCopy]
    | cons b src => simpa [unsafeCopy] using ih src

theorem length_thm (dst src : Buffer) : length_prop dst src := by
  unfold length_prop
  have hc := contents_thm dst src
  unfold contents_prop at hc
  rw [hc]
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

theorem safe_thm (dst src : Buffer) : safe_prop dst src := by
  intro h
  apply CopyResult.ext
  · simpa [contents_prop, List.take_of_length_le h] using contents_thm dst src
  · simpa [overflow_prop, Nat.not_lt.mpr h] using overflow_thm dst src

theorem failure_thm (dst src : Buffer) : failure_prop dst src := by
  intro h
  apply CopyResult.ext
  · simpa [contents_prop, List.drop_eq_nil_of_le (Nat.le_of_lt h)] using
      contents_thm dst src
  · simpa [overflow_prop, h] using overflow_thm dst src

theorem empty_thm (dst : Buffer) : empty_prop dst := by
  simp [empty_prop, unsafeCopy]

theorem exact_thm (dst src : Buffer) : exact_prop dst src := by
  intro h
  have hs := safe_thm dst src (Nat.le_of_eq h)
  simpa [List.drop_eq_nil_of_le (Nat.le_of_eq h.symm)] using hs

/-- Total specification: both normal and exceptional executions are covered. -/
def Post_prop (dst src : Buffer) : Prop :=
  contents_prop dst src ∧ overflow_prop dst src ∧ length_prop dst src ∧
  safe_prop dst src ∧ failure_prop dst src ∧ empty_prop dst ∧ exact_prop dst src

/-! ## Property-based tests

Exhaustively enumerate lengths 0 through 3 over four representative bytes,
including both byte endpoints. This gives 85 buffers and 7,225 ordered pairs,
covering success, strict fits, exact fits, and overflow without filtering inputs.
Each check below is the executable Boolean form of the corresponding property.
These finite tests are separate from, and are not used in, the general proofs.
-/
def testAlphabet : Buffer := [0, 1, 97, 255]

def buffersOfLength : Nat → List Buffer
  | 0 => [[]]
  | n + 1 => testAlphabet.flatMap fun b => (buffersOfLength n).map (b :: ·)

def smallBuffers : List Buffer := (List.range 4).flatMap buffersOfLength

def allPairs (p : Buffer → Buffer → Bool) : Bool :=
  smallBuffers.all fun dst => smallBuffers.all fun src => p dst src

def checkContents (dst src : Buffer) : Bool :=
  (unsafeCopy dst src).buffer == src.take dst.length ++ dst.drop src.length

def checkOverflow (dst src : Buffer) : Bool :=
  (unsafeCopy dst src).indexError == decide (dst.length < src.length)

def checkLength (dst src : Buffer) : Bool :=
  (unsafeCopy dst src).buffer.length == dst.length

def checkSafe (dst src : Buffer) : Bool :=
  !(decide (src.length ≤ dst.length)) ||
    unsafeCopy dst src == ⟨src ++ dst.drop src.length, false⟩

def checkFailure (dst src : Buffer) : Bool :=
  !(decide (dst.length < src.length)) ||
    unsafeCopy dst src == ⟨src.take dst.length, true⟩

def checkEmpty (dst : Buffer) : Bool :=
  unsafeCopy dst [] == ⟨dst, false⟩

def checkExact (dst src : Buffer) : Bool :=
  !(decide (src.length = dst.length)) || unsafeCopy dst src == ⟨src, false⟩

def checkPost (dst src : Buffer) : Bool :=
  checkContents dst src && checkOverflow dst src && checkLength dst src &&
  checkSafe dst src && checkFailure dst src && checkEmpty dst && checkExact dst src

-- PBT for contents_prop.
example : allPairs checkContents = true := by native_decide
-- PBT for overflow_prop.
example : allPairs checkOverflow = true := by native_decide
-- PBT for length_prop.
example : allPairs checkLength = true := by native_decide
-- PBT for safe_prop.
example : allPairs checkSafe = true := by native_decide
-- PBT for failure_prop.
example : allPairs checkFailure = true := by native_decide
-- PBT for empty_prop.
example : smallBuffers.all checkEmpty = true := by native_decide
-- PBT for exact_prop.
example : allPairs checkExact = true := by native_decide
-- PBT for the entire Post_prop, with no restriction beyond Pre = True.
example : allPairs checkPost = true := by native_decide
#eval (smallBuffers.length, allPairs checkPost)

theorem correctness_thm (dst src : Buffer) : Pre dst src → Post_prop dst src := by
  intro _
  exact ⟨contents_thm dst src, overflow_thm dst src, length_thm dst src,
    safe_thm dst src, failure_thm dst src, empty_thm dst, exact_thm dst src⟩

/-! ## Imperative implementation

The mutable cursor is a zipper representation of the destination bytearray:
`writtenRev.reverse ++ remaining` is its current contents. A successful write
replaces the head of `remaining` with the next source byte and advances the
cursor. The first absent destination slot sets IndexError and immediately breaks
the loop. Thus no write is silently truncated, and earlier writes survive errors.
-/
structure CopyCursor where
  writtenRev : Buffer
  remaining : Buffer
  indexError : Bool
  deriving Repr

def CopyCursor.finish (st : CopyCursor) : CopyResult :=
  ⟨st.writtenRev.reverse ++ st.remaining, st.indexError⟩

/-- The same imperative loop with an arbitrary incoming cursor, for the loop
invariant used below. -/
def runCursor (src : Buffer) (initial : CopyCursor) : CopyCursor := Id.run do
  let mut st := initial
  for b in src do
    match st.remaining with
    | [] =>
      st := {st with indexError := true}
      break
    | _ :: tail =>
      st := {st with writtenRev := b :: st.writtenRev, remaining := tail}
  return st

/-- Mutable byte-by-byte traversal, starting at destination index zero. -/
def unsafeCopyImperative (dst src : Buffer) : CopyResult := Id.run do
  let mut st : CopyCursor := ⟨[], dst, false⟩
  for b in src do
    match st.remaining with
    | [] =>
      st := {st with indexError := true}
      break
    | _ :: tail =>
      st := {st with writtenRev := b :: st.writtenRev, remaining := tail}
  return st.finish

-- The same five Python tests, now run against the imperative implementation.
example : unsafeCopyImperative [0, 0, 0] [97, 98, 99] =
    ⟨[97, 98, 99], false⟩ := by native_decide
example : unsafeCopyImperative [0, 0] [120, 121] =
    ⟨[120, 121], false⟩ := by native_decide
example : unsafeCopyImperative [0, 0] [49, 50, 51] =
    ⟨[49, 50], true⟩ := by native_decide
example : unsafeCopyImperative [104, 101, 108, 108, 111] [] =
    ⟨[104, 101, 108, 108, 111], false⟩ := by native_decide
example : unsafeCopyImperative [] [122] = ⟨[], true⟩ := by native_decide
example : unsafeCopyImperative [10, 20, 30, 40] [1, 2] =
    ⟨[1, 2, 30, 40], false⟩ := by native_decide
example : check unsafeCopyImperative = true := by native_decide
#eval if check unsafeCopyImperative then "All tests passed." else "Tests failed."
#eval unsafeCopyImperative [0, 0] [49, 50, 51]
-- Additional PBT: both the mutated buffer and exception status must agree.
example : allPairs (fun dst src =>
    unsafeCopy dst src == unsafeCopyImperative dst src) = true := by native_decide
#eval allPairs (fun dst src => unsafeCopy dst src == unsafeCopyImperative dst src)

theorem runCursor_nil (initial : CopyCursor) : runCursor [] initial = initial := by
  simp [runCursor]

theorem runCursor_overflow (p : Buffer) (flag : Bool) (b : UInt8) (src : Buffer) :
    runCursor (b :: src) ⟨p, [], flag⟩ = ⟨p, [], true⟩ := by
  simp [runCursor]

theorem runCursor_write (p : Buffer) (flag : Bool) (d b : UInt8) (dst src : Buffer) :
    runCursor (b :: src) ⟨p, d :: dst, flag⟩ =
      runCursor src ⟨b :: p, dst, flag⟩ := by
  simp [runCursor]

/-- Loop invariant, generalized over both previously written bytes and the
incoming exception flag. It describes the full state, including partial writes. -/
theorem runCursor_spec (src dst p : Buffer) (flag : Bool) :
    (runCursor src ⟨p, dst, flag⟩).finish =
      ⟨p.reverse ++ (unsafeCopy dst src).buffer,
        flag || (unsafeCopy dst src).indexError⟩ := by
  induction src generalizing dst p with
  | nil => simp [runCursor_nil, CopyCursor.finish, unsafeCopy]
  | cons b src ih =>
    cases dst with
    | nil => simp [runCursor_overflow, CopyCursor.finish, unsafeCopy]
    | cons d dst =>
      rw [runCursor_write, ih]
      simp [unsafeCopy, List.reverse_cons, List.append_assoc]

/-- Functional and imperative semantics agree on all inputs, including overflow.
This proof uses the loop invariant, not executable test results. -/
theorem equivalence_thm (dst src : Buffer) :
    unsafeCopy dst src = unsafeCopyImperative dst src := by
  change unsafeCopy dst src = (runCursor src ⟨[], dst, false⟩).finish
  rw [runCursor_spec]
  simp

end UnsafeCopy
end Agent
