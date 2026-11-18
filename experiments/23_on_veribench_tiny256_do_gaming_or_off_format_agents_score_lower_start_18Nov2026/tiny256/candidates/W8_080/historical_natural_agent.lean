import Mathlib
namespace Agent

/-!
# Unchecked access to a memory block

This formalizes the Python `MemoryBlock` class, `unsafe_access_memory`, and
its five test scenarios. `some s` represents a Python string (including the
empty string), and `none` represents Python `None`. Despite its Python return
annotation, the accessor can return either, so its Lean result is `Option String`.

The functional model threads object state explicitly: `free` returns the updated
block, which replaces the old block at the call site. Distinct allocations are
represented by distinct local states. The imperative model uses mutable locals
and performs the two field writes in the same order as Python. No actual pointer
is dereferenced and no exception is raised by the given Python implementation.
The freed flag does not guard access: even inconsistent public-field states are
modeled, without imposing an artificial precondition on the accessor.
-/

namespace UnsafeMemoryAccess

/-! ## Functional implementation -/

structure MemoryBlock where
  data : Option String
  is_freed : Bool
  deriving Repr, DecidableEq

def MemoryBlock.new (data : String) : MemoryBlock :=
  { data := some data, is_freed := false }

def MemoryBlock.free (block : MemoryBlock) : MemoryBlock :=
  { block with is_freed := true, data := none }

def MemoryBlock.is_valid (block : MemoryBlock) : Bool :=
  !block.is_freed

def unsafe_access_memory (block : MemoryBlock) : Option String :=
  block.data

/-- A specification helper for any finite number of reads of the same state. -/
def repeated_access_memory (block : MemoryBlock) : Nat → List (Option String)
  | 0 => []
  | n + 1 => unsafe_access_memory block :: repeated_access_memory block n

/-- The original Python assertions, in order, with `free` updates explicit. -/
def check (candidate : MemoryBlock → Option String) : Bool :=
  let block1 := MemoryBlock.new "hello world"
  let block2 := MemoryBlock.new "test data"
  let block2 := block2.free
  let block3 := MemoryBlock.new "first"
  let block4 := MemoryBlock.new "second"
  let block3 := block3.free
  let block5 := MemoryBlock.new "repeated"
  let block5 := block5.free
  let block6 := MemoryBlock.new ""
  (candidate block1 == some "hello world") &&
    (candidate block2 == none) &&
    (candidate block3 == none) &&
    (candidate block4 == some "second") &&
    (candidate block5 == none) &&
    (candidate block5 == none) &&
    (candidate block6 == some "")

/-! ## Unit tests -/

example : unsafe_access_memory (MemoryBlock.new "hello world") =
    some "hello world" := by native_decide

example : unsafe_access_memory ((MemoryBlock.new "test data").free) =
    none := by native_decide

example :
    let block3 := (MemoryBlock.new "first").free
    let block4 := MemoryBlock.new "second"
    unsafe_access_memory block3 = none ∧
      unsafe_access_memory block4 = some "second" := by native_decide

example :
    let block5 := (MemoryBlock.new "repeated").free
    (unsafe_access_memory block5, unsafe_access_memory block5) =
      (none, none) := by native_decide

example : unsafe_access_memory (MemoryBlock.new "") = some "" := by native_decide

example : (MemoryBlock.new "hello world").is_valid = true ∧
    ((MemoryBlock.new "hello world").free).is_valid = false := by native_decide

-- The flag is deliberately NOT consulted by the accessor.
example : unsafe_access_memory { data := some "present", is_freed := true } =
    some "present" := by native_decide

example : check unsafe_access_memory = true := by native_decide

#eval unsafe_access_memory (MemoryBlock.new "hello world")
#eval unsafe_access_memory ((MemoryBlock.new "test data").free)
#eval repeated_access_memory ((MemoryBlock.new "repeated").free) 5
#eval if check unsafe_access_memory then "All tests passed." else "Candidate failed use-after-free tests"

/-! ## Precondition and universally quantified properties -/

/-- Reading, freeing, and testing validity are defined for every block state. -/
def Pre (_block : MemoryBlock) : Prop := True

/-- Unchecked access returns the data field exactly, regardless of the flag. -/
def access_prop (block : MemoryBlock) : Prop :=
  unsafe_access_memory block = block.data

theorem access_thm (block : MemoryBlock) : access_prop block := by
  rfl

/-- Construction retains every string, sets the flag, and creates valid memory. -/
def allocation_prop (s : String) : Prop :=
  (MemoryBlock.new s).data = some s ∧
  (MemoryBlock.new s).is_freed = false ∧
  (MemoryBlock.new s).is_valid = true ∧
  unsafe_access_memory (MemoryBlock.new s) = some s

theorem allocation_thm (s : String) : allocation_prop s := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Validity is exactly the negation of the freed flag, not a test of the data. -/
def validity_prop (block : MemoryBlock) : Prop :=
  block.is_valid = !block.is_freed

theorem validity_thm (block : MemoryBlock) : validity_prop block := by
  rfl

/-- Free clears the data, sets the flag, invalidates the block, and changes reads. -/
def free_prop (block : MemoryBlock) : Prop :=
  block.free.data = none ∧
  block.free.is_freed = true ∧
  block.free.is_valid = false ∧
  unsafe_access_memory block.free = none

theorem free_thm (block : MemoryBlock) : free_prop block := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Freeing an already freed block has no further effect. -/
def repeated_free_prop (block : MemoryBlock) : Prop :=
  block.free.free = block.free

theorem repeated_free_thm (block : MemoryBlock) : repeated_free_prop block := by
  rfl

/-- Every read after free is `none`, not just the first or the second read. -/
def repeated_access_prop (block : MemoryBlock) (n : Nat) : Prop :=
  repeated_access_memory block.free n = List.replicate n none

theorem repeated_access_thm (block : MemoryBlock) (n : Nat) :
    repeated_access_prop block n := by
  unfold repeated_access_prop
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [repeated_access_memory, unsafe_access_memory, MemoryBlock.free,
        List.replicate_succ] using congrArg (List.cons (none : Option String)) ih

/-- Freeing one allocation does not affect another, including equal strings. -/
def independence_prop (s t : String) : Prop :=
  let left := MemoryBlock.new s
  let right := MemoryBlock.new t
  (unsafe_access_memory left.free, unsafe_access_memory right) = (none, some t) ∧
  right.is_valid = true ∧
  (unsafe_access_memory left.free, unsafe_access_memory right.free) = (none, none)

theorem independence_thm (s t : String) : independence_prop s t := by
  exact ⟨rfl, rfl, rfl⟩

/-- The actual Python check also holds by kernel reduction, independently of tests. -/
theorem python_check_thm : check unsafe_access_memory = true := by
  decide

/-! ## Postcondition -/

/-- Full behavioral contract, with arbitrary states, strings, and read counts. -/
def Post_prop (block : MemoryBlock) (s t : String) (n : Nat) : Prop :=
  access_prop block ∧
  allocation_prop s ∧
  validity_prop block ∧
  free_prop block ∧
  repeated_free_prop block ∧
  repeated_access_prop block n ∧
  independence_prop s t ∧
  check unsafe_access_memory = true

/-! ## Bounded property-based tests

These are executable Boolean counterparts of every `_prop` above, including
`Post_prop`. They are evidence only; none is used in any theorem proof.
The generated domain includes lengths 0..31, decimal strings 0..31, the Python
examples, whitespace, and Unicode. Blocks include BOTH flags with every payload,
plus `none` with BOTH flags, so tests do not assume consistency of public fields.
-/

def testStrings : List String :=
  ["", "hello world", "test data", "first", "second", "repeated", "\n", "λ🙂"] ++
    (List.range 32).map (fun n => String.mk (List.replicate n 'x')) ++
    (List.range 32).map (fun n => toString n)

def testBlocks : List MemoryBlock :=
  [{ data := none, is_freed := false }, { data := none, is_freed := true }] ++
    testStrings.flatMap (fun s =>
      [{ data := some s, is_freed := false }, { data := some s, is_freed := true }])

def accessCheck (block : MemoryBlock) : Bool :=
  unsafe_access_memory block == block.data

def allocationCheck (s : String) : Bool :=
  ((MemoryBlock.new s).data == some s) &&
  ((MemoryBlock.new s).is_freed == false) &&
  ((MemoryBlock.new s).is_valid == true) &&
  (unsafe_access_memory (MemoryBlock.new s) == some s)

def validityCheck (block : MemoryBlock) : Bool :=
  block.is_valid == !block.is_freed

def freeCheck (block : MemoryBlock) : Bool :=
  (block.free.data == none) &&
  (block.free.is_freed == true) &&
  (block.free.is_valid == false) &&
  (unsafe_access_memory block.free == none)

def repeatedFreeCheck (block : MemoryBlock) : Bool :=
  decide (block.free.free = block.free)

def repeatedAccessCheck (block : MemoryBlock) (n : Nat) : Bool :=
  repeated_access_memory block.free n == List.replicate n none

def independenceCheck (s t : String) : Bool :=
  let left := MemoryBlock.new s
  let right := MemoryBlock.new t
  ((unsafe_access_memory left.free, unsafe_access_memory right) == (none, some t)) &&
  (right.is_valid == true) &&
  ((unsafe_access_memory left.free, unsafe_access_memory right.free) == (none, none))

def postCheck (block : MemoryBlock) (s t : String) (n : Nat) : Bool :=
  accessCheck block && allocationCheck s && validityCheck block && freeCheck block &&
  repeatedFreeCheck block && repeatedAccessCheck block n && independenceCheck s t &&
  check unsafe_access_memory

-- PBT for access_prop: all sampled blocks, including inconsistent states.
example : testBlocks.all accessCheck = true := by native_decide

-- PBT for allocation_prop: every generated string, including the empty string.
example : testStrings.all allocationCheck = true := by native_decide

-- PBT for validity_prop: both flags with every sampled payload.
example : testBlocks.all validityCheck = true := by native_decide

-- PBT for free_prop: every sampled initial state, already freed or not.
example : testBlocks.all freeCheck = true := by native_decide

-- PBT for repeated_free_prop: freeing twice versus once on all sampled blocks.
example : testBlocks.all repeatedFreeCheck = true := by native_decide

-- PBT for repeated_access_prop: all sampled blocks and 0..31 successive reads.
example : testBlocks.all (fun block =>
    (List.range 32).all (fun n => repeatedAccessCheck block n)) = true := by
  native_decide

-- PBT for independence_prop: the full Cartesian square, including equal data.
example : testStrings.all (fun s =>
    testStrings.all (fun t => independenceCheck s t)) = true := by native_decide

-- PBT for Post_prop: a Cartesian product of states, string pairs, and counts.
-- Smaller explicit string/count bounds keep this combined test inexpensive.
def postPBT : Bool :=
  testBlocks.all (fun block =>
    (testStrings.take 12).all (fun s =>
      (testStrings.take 12).all (fun t =>
        (List.range 8).all (fun n => postCheck block s t n))))

example : postPBT = true := by native_decide
#eval postPBT

/-! ## Correctness -/

theorem correctness_thm (block : MemoryBlock) (s t : String) (n : Nat) :
    Pre block → Post_prop block s t n := by
  intro _
  exact ⟨access_thm block, allocation_thm s, validity_thm block, free_thm block,
    repeated_free_thm block, repeated_access_thm block n, independence_thm s t,
    python_check_thm⟩

/-! ## Imperative implementation -/

def MemoryBlock.newImperative (s : String) : MemoryBlock := Id.run do
  let mut block : MemoryBlock := { data := none, is_freed := false }
  block := { block with data := some s }
  block := { block with is_freed := false }
  return block

def MemoryBlock.freeImperative (block : MemoryBlock) : MemoryBlock := Id.run do
  let mut state := block
  state := { state with is_freed := true }
  state := { state with data := none }
  return state

def MemoryBlock.isValidImperative (block : MemoryBlock) : Bool := Id.run do
  return !block.is_freed

/-- Just as in Python, reading itself does not modify the block or check its flag. -/
def unsafe_access_memory_imperative (block : MemoryBlock) : Option String := Id.run do
  return block.data

/-- Mutable local blocks translate the original allocations, frees, and assertions. -/
def check_imperative (candidate : MemoryBlock → Option String) : Bool := Id.run do
  let block1 := MemoryBlock.newImperative "hello world"
  let mut passed := candidate block1 == some "hello world"
  let mut block2 := MemoryBlock.newImperative "test data"
  block2 := block2.freeImperative
  passed := passed && (candidate block2 == none)
  let mut block3 := MemoryBlock.newImperative "first"
  let block4 := MemoryBlock.newImperative "second"
  block3 := block3.freeImperative
  passed := passed && (candidate block3 == none)
  passed := passed && (candidate block4 == some "second")
  let mut block5 := MemoryBlock.newImperative "repeated"
  block5 := block5.freeImperative
  passed := passed && (candidate block5 == none)
  passed := passed && (candidate block5 == none)
  let block6 := MemoryBlock.newImperative ""
  passed := passed && (candidate block6 == some "")
  return passed

/-! ## Imperative tests -/

example : unsafe_access_memory_imperative (MemoryBlock.newImperative "hello world") =
    some "hello world" := by native_decide

example : unsafe_access_memory_imperative
    ((MemoryBlock.newImperative "test data").freeImperative) = none := by native_decide

example :
    let block3 := (MemoryBlock.newImperative "first").freeImperative
    let block4 := MemoryBlock.newImperative "second"
    unsafe_access_memory_imperative block3 = none ∧
      unsafe_access_memory_imperative block4 = some "second" := by native_decide

example :
    let block5 := (MemoryBlock.newImperative "repeated").freeImperative
    (unsafe_access_memory_imperative block5, unsafe_access_memory_imperative block5) =
      (none, none) := by native_decide

example : unsafe_access_memory_imperative (MemoryBlock.newImperative "") =
    some "" := by native_decide

example : (MemoryBlock.newImperative "test").isValidImperative = true ∧
    ((MemoryBlock.newImperative "test").freeImperative).isValidImperative = false := by
  native_decide

example : check_imperative unsafe_access_memory_imperative = true := by native_decide
#eval check_imperative unsafe_access_memory_imperative
#eval if check_imperative unsafe_access_memory_imperative then
  "All tests passed." else "Candidate failed use-after-free tests"

/-! ## Functional / imperative equivalence -/

theorem constructor_equivalence_thm (s : String) :
    MemoryBlock.new s = MemoryBlock.newImperative s := by
  rfl

theorem free_equivalence_thm (block : MemoryBlock) :
    block.free = block.freeImperative := by
  rfl

theorem validity_equivalence_thm (block : MemoryBlock) :
    block.is_valid = block.isValidImperative := by
  rfl

theorem equivalence_thm : unsafe_access_memory = unsafe_access_memory_imperative := by
  funext block
  rfl

/-- Equivalence of the complete test workflow for every pure candidate accessor. -/
theorem check_equivalence_thm (candidate : MemoryBlock → Option String) :
    check candidate = check_imperative candidate := by
  simp [check, check_imperative, MemoryBlock.new, MemoryBlock.free,
    MemoryBlock.newImperative, MemoryBlock.freeImperative, Bool.and_assoc]

theorem program_equivalence_thm :
    check unsafe_access_memory = check_imperative unsafe_access_memory_imperative := by
  rw [← equivalence_thm, check_equivalence_thm]

/-- The imperative translation passes the source program's entire test suite. -/
theorem imperative_check_thm :
    check_imperative unsafe_access_memory_imperative = true := by
  rw [← program_equivalence_thm]
  exact python_check_thm

end UnsafeMemoryAccess
end Agent
