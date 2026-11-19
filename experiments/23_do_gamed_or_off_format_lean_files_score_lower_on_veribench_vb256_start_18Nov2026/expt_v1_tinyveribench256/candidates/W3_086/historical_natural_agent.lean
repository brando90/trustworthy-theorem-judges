import Mathlib
namespace Agent

/-!
# Safe memory access

A functional translation of the Python `MemoryBlock` API and
`safe_access_memory`, including the `check` harness.

`Option String` models the nullable `data` attribute: `some s` is a Python
string (including the empty string), and `none` is Python `None`.
`Except String` models `ValueError`, retaining its exact message. The returned
payload is optional because Python's return annotation does not perform a
runtime check: even a manually modified, live block with `data = None` returns
`None`. For blocks constructed by `new`, successful access returns `some s`.
No consistency assumption about the two public fields is needed for safety.

`MemoryInput.other tag` abstracts a non-MemoryBlock Python object; the tag is
only an uninterpreted description. All such objects have identical behavior
under the source program's `isinstance` test. `free` returns the updated state,
not the Python method's implicit `None` return value. Access itself is read-only.

The specification covers all represented inputs, including invalid types and
both consistent and manually modified blocks. Bounded property-based tests
exercise cross-products of data and freed flags; they are separate from the
kernel-checked proofs. The last section uses mutable state in `Id.run`.
-/

namespace UnsafeMemoryAccessSafe

/-! ## Functional implementation -/

structure MemoryBlock where
  data : Option String
  is_freed : Bool
  deriving Repr, DecidableEq, BEq

def MemoryBlock.new (data : String) : MemoryBlock :=
  { data := some data, is_freed := false }

/-- The state transition performed by Python's `free`, including clearing data. -/
def MemoryBlock.free (_block : MemoryBlock) : MemoryBlock :=
  { data := none, is_freed := true }

def MemoryBlock.is_valid (block : MemoryBlock) : Bool :=
  !block.is_freed

inductive MemoryInput where
  | block (value : MemoryBlock)
  | other (tag : String)
  deriving Repr, DecidableEq, BEq

-- Executable equality for exception results, used only by the checks.
deriving instance DecidableEq for Except

abbrev AccessResult := Except String (Option String)

def safe_access_memory (input : MemoryInput) : AccessResult :=
  match input with
  | .other _ => .error "invalid block"
  | .block block =>
      if block.is_valid then
        .ok block.data
      else
        .error "access after free"

def accessSucceeded (result : AccessResult) : Bool :=
  match result with
  | .ok _ => true
  | .error _ => false

/-- The runtime type test followed by the source's validity test. -/
def isLiveBlock (input : MemoryInput) : Bool :=
  match input with
  | .other _ => false
  | .block block => block.is_valid

/-- Boolean summary of the original three assertions. The freed case catches
any ValueError, as Python does; the implementation properties below separately
require the precise error message. -/
def check (candidate : MemoryInput → AccessResult) : Bool :=
  let b1 := MemoryBlock.new "hello"
  let b2 := (MemoryBlock.new "test").free
  let b3 := MemoryBlock.new ""
  decide (candidate (.block b1) = .ok (some "hello")) &&
    !accessSucceeded (candidate (.block b2)) &&
    decide (candidate (.block b3) = .ok (some ""))

/-! ## Unit tests -/

example : safe_access_memory (.block (MemoryBlock.new "hello")) =
    .ok (some "hello") := by native_decide

example : safe_access_memory (.block (MemoryBlock.new "test").free) =
    .error "access after free" := by native_decide

example : safe_access_memory (.block (MemoryBlock.new "")) =
    .ok (some "") := by native_decide

example : safe_access_memory (.other "None") =
    .error "invalid block" := by native_decide

example : (MemoryBlock.new "test").free.data = none ∧
    (MemoryBlock.new "test").free.is_valid = false := by native_decide

-- Even stale, nonempty data cannot bypass the freed flag.
example : safe_access_memory (.block ⟨some "stale", true⟩) =
    .error "access after free" := by native_decide

-- Match Python even if a caller has manually set a live block's data to None.
example : safe_access_memory (.block ⟨none, false⟩) =
    .ok none := by native_decide

example : check safe_access_memory = true := by native_decide

-- The Python harness catches ValueError independently of its message.
example : check (fun input =>
    match input with
    | .other _ => .error "invalid block"
    | .block block =>
        if block.is_valid then .ok block.data else .error "another ValueError") =
    true := by native_decide

#eval safe_access_memory (.block (MemoryBlock.new "hello"))
#eval safe_access_memory (.block (MemoryBlock.new "test").free)
#eval safe_access_memory (.block (MemoryBlock.new ""))
#eval safe_access_memory (.other "42")
#eval check safe_access_memory
#eval if check safe_access_memory then "All tests passed." else "Tests failed."

/-! ## Precondition

The contract is total. In particular, the precondition does not exclude freed
blocks or wrong-type inputs; their ValueErrors are part of the specification.
-/

def Pre : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Construction keeps every string, sets the flag, and permits exact access. -/
def initialized_prop (s : String) : Prop :=
  (MemoryBlock.new s).data = some s ∧
  (MemoryBlock.new s).is_freed = false ∧
  (MemoryBlock.new s).is_valid = true ∧
  safe_access_memory (.block (MemoryBlock.new s)) = .ok (some s)

theorem initialized_thm (s : String) : initialized_prop s := by
  simp [initialized_prop, MemoryBlock.new, MemoryBlock.is_valid, safe_access_memory]

/-- Validity is exactly the negation of the freed flag. -/
def validity_prop (block : MemoryBlock) : Prop :=
  block.is_valid = true ↔ block.is_freed = false

theorem validity_thm (block : MemoryBlock) : validity_prop block := by
  cases h : block.is_freed <;>
    simp [validity_prop, MemoryBlock.is_valid, h]

/-- Free clears the payload, invalidates the block, and is idempotent. -/
def free_state_prop (block : MemoryBlock) : Prop :=
  block.free.data = none ∧
  block.free.is_freed = true ∧
  block.free.is_valid = false ∧
  block.free.free = block.free

theorem free_state_thm (block : MemoryBlock) : free_state_prop block := by
  simp [free_state_prop, MemoryBlock.free, MemoryBlock.is_valid]

/-- Wrong-type objects fail at the first guard, with the exact Python message. -/
def invalid_block_prop (tag : String) : Prop :=
  safe_access_memory (.other tag) = .error "invalid block"

theorem invalid_block_thm (tag : String) : invalid_block_prop tag := by
  rfl

/-- A live block returns its actual payload, without a truthiness test. -/
def live_access_prop (block : MemoryBlock) : Prop :=
  block.is_valid = true →
    safe_access_memory (.block block) = .ok block.data

theorem live_access_thm (block : MemoryBlock) : live_access_prop block := by
  intro h
  simp [safe_access_memory, h]

/-- Any freed block is rejected, regardless of its (possibly stale) payload. -/
def freed_access_prop (block : MemoryBlock) : Prop :=
  block.is_freed = true →
    safe_access_memory (.block block) = .error "access after free"

theorem freed_access_thm (block : MemoryBlock) : freed_access_prop block := by
  intro h
  simp [safe_access_memory, MemoryBlock.is_valid, h]

/-- Calling free followed by access always gives the access-after-free error. -/
def after_free_prop (block : MemoryBlock) : Prop :=
  safe_access_memory (.block block.free) = .error "access after free"

theorem after_free_thm (block : MemoryBlock) : after_free_prop block := by
  rfl

/-- An empty string is a legitimate live payload, not an error. -/
def empty_data_prop (block : MemoryBlock) : Prop :=
  block.is_valid = true → block.data = some "" →
    safe_access_memory (.block block) = .ok (some "")

theorem empty_data_thm (block : MemoryBlock) : empty_data_prop block := by
  intro hvalid hdata
  rw [live_access_thm block hvalid, hdata]

/-- Success occurs exactly for an input that is a live MemoryBlock. -/
def success_iff_prop (input : MemoryInput) : Prop :=
  accessSucceeded (safe_access_memory input) = true ↔ isLiveBlock input = true

theorem success_iff_thm (input : MemoryInput) : success_iff_prop input := by
  cases input with
  | other tag =>
      simp [success_iff_prop, safe_access_memory, accessSucceeded, isLiveBlock]
  | block block =>
      cases block with
      | mk data freed =>
          cases freed <;>
            simp [success_iff_prop, safe_access_memory, accessSucceeded,
              isLiveBlock, MemoryBlock.is_valid]

/-! ## Postcondition

This is the API-wide contract: every string, block state, and runtime input is
quantified, rather than just the three examples from the Python harness.
-/

def Post_prop : Prop :=
  (∀ s : String, initialized_prop s) ∧
  (∀ block : MemoryBlock, validity_prop block) ∧
  (∀ block : MemoryBlock, free_state_prop block) ∧
  (∀ tag : String, invalid_block_prop tag) ∧
  (∀ block : MemoryBlock, live_access_prop block) ∧
  (∀ block : MemoryBlock, freed_access_prop block) ∧
  (∀ block : MemoryBlock, after_free_prop block) ∧
  (∀ block : MemoryBlock, empty_data_prop block) ∧
  (∀ input : MemoryInput, success_iff_prop input)

/-! ## Bounded property-based tests

The data corpus includes empty, whitespace, Unicode, numeric, and varying-length
strings. Every payload (including None) is combined with both freed flags.
Thus the tests include constructor/free states and inconsistent public-field
states. Wrong-type tags are varied too. Each checker is the executable Boolean
form of the named proposition; none of these checks is used as a theorem proof.
-/

def stringSamples : List String :=
  ["", "hello", "test", " ", "\n", "a\nb", "λ", "安全"] ++
    (List.range 64).map (fun n => toString n) ++
    (List.range 32).map (fun n => String.mk (List.replicate n 'x'))

def blockSamples : List MemoryBlock :=
  [false, true].flatMap fun freed =>
    (none :: stringSamples.map some).map fun data =>
      { data := data, is_freed := freed }

def inputSamples : List MemoryInput :=
  blockSamples.map MemoryInput.block ++ stringSamples.map MemoryInput.other

def initializedCheck (s : String) : Bool :=
  let block := MemoryBlock.new s
  (block.data == some s) && (block.is_freed == false) && block.is_valid &&
    decide (safe_access_memory (.block block) = .ok (some s))

def validityCheck (block : MemoryBlock) : Bool :=
  block.is_valid == !block.is_freed

def freeStateCheck (block : MemoryBlock) : Bool :=
  (block.free.data == none) && block.free.is_freed && !block.free.is_valid &&
    (block.free.free == block.free)

def invalidBlockCheck (tag : String) : Bool :=
  decide (safe_access_memory (.other tag) = .error "invalid block")

def liveAccessCheck (block : MemoryBlock) : Bool :=
  !block.is_valid || decide (safe_access_memory (.block block) = .ok block.data)

def freedAccessCheck (block : MemoryBlock) : Bool :=
  !block.is_freed ||
    decide (safe_access_memory (.block block) = .error "access after free")

def afterFreeCheck (block : MemoryBlock) : Bool :=
  decide (safe_access_memory (.block block.free) = .error "access after free")

def emptyDataCheck (block : MemoryBlock) : Bool :=
  !(block.is_valid && (block.data == some "")) ||
    decide (safe_access_memory (.block block) = .ok (some ""))

def successIffCheck (input : MemoryInput) : Bool :=
  accessSucceeded (safe_access_memory input) == isLiveBlock input

-- PBT: initialized_prop, including the normal and empty-string cases.
example : stringSamples.all initializedCheck = true := by native_decide

-- PBT: validity_prop on every payload/flag combination.
example : blockSamples.all validityCheck = true := by native_decide

-- PBT: free_state_prop, including already-freed blocks.
example : blockSamples.all freeStateCheck = true := by native_decide

-- PBT: invalid_block_prop on all wrong-type descriptions in the corpus.
example : stringSamples.all invalidBlockCheck = true := by native_decide

-- PBT: live_access_prop; the corpus contains both live and freed states.
example : blockSamples.all liveAccessCheck = true := by native_decide

-- PBT: freed_access_prop, including stale nonempty and empty payloads.
example : blockSamples.all freedAccessCheck = true := by native_decide

-- PBT: after_free_prop for all starting states in the corpus.
example : blockSamples.all afterFreeCheck = true := by native_decide

-- PBT: empty_data_prop, with live empty strings explicitly in the corpus.
example : blockSamples.all emptyDataCheck = true := by native_decide

-- PBT: success_iff_prop across both runtime input constructors.
example : inputSamples.all successIffCheck = true := by native_decide

/-- The bounded executable counterpart of the whole Post_prop conjunction. -/
def boundedPostCheck : Bool :=
  stringSamples.all initializedCheck &&
  blockSamples.all validityCheck &&
  blockSamples.all freeStateCheck &&
  stringSamples.all invalidBlockCheck &&
  blockSamples.all liveAccessCheck &&
  blockSamples.all freedAccessCheck &&
  blockSamples.all afterFreeCheck &&
  blockSamples.all emptyDataCheck &&
  inputSamples.all successIffCheck

-- PBT: Post_prop, checking every conjunct over its bounded input domain.
example : boundedPostCheck = true := by native_decide

#eval (stringSamples.length, blockSamples.length, inputSamples.length)
#eval boundedPostCheck

/-! ## Correctness -/

theorem correctness_thm : Pre → Post_prop := by
  intro _
  exact ⟨initialized_thm, validity_thm, free_state_thm, invalid_block_thm,
    live_access_thm, freed_access_thm, after_free_thm, empty_data_thm,
    success_iff_thm⟩

/-! ## Imperative implementation -/

/-- The two assignments of Python's free method, in their original order. -/
def MemoryBlock.free_imperative (block : MemoryBlock) : MemoryBlock := Id.run do
  let mut state := block
  state := { state with is_freed := true }
  state := { state with data := none }
  return state

/-- A mutable result register; invalidity is checked before reading the data. -/
def safe_access_memory_imperative (input : MemoryInput) : AccessResult := Id.run do
  let mut result : AccessResult := .error "invalid block"
  match input with
  | .other _ => pure ()
  | .block block =>
      if !block.is_valid then
        result := .error "access after free"
      else
        result := .ok block.data
  return result

/-! ## Imperative tests -/

example : safe_access_memory_imperative (.block (MemoryBlock.new "hello")) =
    .ok (some "hello") := by native_decide

example : safe_access_memory_imperative
    (.block (MemoryBlock.new "test").free_imperative) =
    .error "access after free" := by native_decide

example : safe_access_memory_imperative (.block (MemoryBlock.new "")) =
    .ok (some "") := by native_decide

example : safe_access_memory_imperative (.other "not a block") =
    .error "invalid block" := by native_decide

example : safe_access_memory_imperative (.block ⟨some "stale", true⟩) =
    .error "access after free" := by native_decide

example : safe_access_memory_imperative (.block ⟨none, false⟩) =
    .ok none := by native_decide

example : (MemoryBlock.new "test").free_imperative =
    ({ data := none, is_freed := true } : MemoryBlock) := by native_decide

example : check safe_access_memory_imperative = true := by native_decide

example : inputSamples.all (fun input =>
    decide (safe_access_memory input = safe_access_memory_imperative input)) =
    true := by native_decide

example : blockSamples.all (fun block =>
    decide (block.free = block.free_imperative)) = true := by native_decide

#eval check safe_access_memory_imperative
#eval (MemoryBlock.new "test").free_imperative
#eval safe_access_memory_imperative (.block (MemoryBlock.new "test").free_imperative)

/-! ## Functional/imperative equivalence -/

theorem free_equivalence_thm (block : MemoryBlock) :
    block.free = block.free_imperative := by
  rfl

theorem equivalence_thm (input : MemoryInput) :
    safe_access_memory input = safe_access_memory_imperative input := by
  cases input with
  | other tag => rfl
  | block block =>
      cases block with
      | mk data freed =>
          cases freed <;> rfl

end UnsafeMemoryAccessSafe
end Agent
