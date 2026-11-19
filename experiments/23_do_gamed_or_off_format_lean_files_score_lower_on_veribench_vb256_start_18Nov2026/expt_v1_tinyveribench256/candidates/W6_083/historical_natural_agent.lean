import Mathlib
namespace Agent

/-!
# Unsafe Meltdown speculative kernel read

This formalizes the supplied Python model of CVE-2017-5754: the architectural
read faults, but speculative execution leaves the input value in the cache.
`none` represents Python's `None`, and `some k` represents an observable integer.
We use `Int`, not a bounded byte type: the Python implementation accepts every
integer, including negative integers and integers larger than 255.

The model describes the returned observations, not a processor microarchitecture.
The Boolean `check` below collects the six assertions in the Python checker.
-/

namespace UnsafeMeltdownRead

/-! ## Functional implementation -/

abbrev Observation := Option Int × Option Int

def unsafe_meltdown_read (kernelByte : Int) : Observation :=
  (none, some kernelByte)

/-- Boolean counterpart of the Python assertion-based checker. -/
def check (candidate : Int → Observation) : Bool :=
  let (arch, cache) := candidate 0xCA
  (arch == none) &&
  (cache == some 0xCA) &&
  ((candidate 0).2 == some 0) &&
  ((candidate 0xFF).2 == some 0xFF) &&
  ((candidate 1).2 != (candidate 2).2) &&
  ((candidate 42).2 != none)

/-! ## Unit tests: each original assertion, plus the complete checker -/

example : (unsafe_meltdown_read 0xCA).1 = none := by native_decide
example : (unsafe_meltdown_read 0xCA).2 = some 0xCA := by native_decide
example : (unsafe_meltdown_read 0).2 = some 0 := by native_decide
example : (unsafe_meltdown_read 0xFF).2 = some 0xFF := by native_decide
example : (unsafe_meltdown_read 1).2 ≠ (unsafe_meltdown_read 2).2 := by native_decide
example : (unsafe_meltdown_read 42).2 ≠ none := by native_decide
example : check unsafe_meltdown_read = true := by native_decide
example : unsafe_meltdown_read (-1) = (none, some (-1)) := by native_decide
example : unsafe_meltdown_read 256 = (none, some 256) := by native_decide

#eval unsafe_meltdown_read 0xCA
#eval check unsafe_meltdown_read
#eval if check unsafe_meltdown_read then "All tests passed."
      else "Candidate failed Meltdown leak tests"

/-! ## Preconditions and proved properties -/

/-- No bounds or other restrictions are imposed by the Python function. -/
def Pre (_kernelByte : Int) : Prop := True

/-- A fault prevents an architectural return, for every input. -/
def architecturalReturn_prop (kernelByte : Int) : Prop :=
  (unsafe_meltdown_read kernelByte).1 = none

theorem architecturalReturn_thm (kernelByte : Int) :
    architecturalReturn_prop kernelByte := by
  rfl

/-- The cache contains exactly the input, including zero and 255. -/
def cacheLeak_prop (kernelByte : Int) : Prop :=
  (unsafe_meltdown_read kernelByte).2 = some kernelByte

theorem cacheLeak_thm (kernelByte : Int) : cacheLeak_prop kernelByte := by
  rfl

/-- Distinct integers can be distinguished by their cache observations. -/
def distinguishes_prop (a b : Int) : Prop :=
  a ≠ b → (unsafe_meltdown_read a).2 ≠ (unsafe_meltdown_read b).2

theorem distinguishes_thm (a b : Int) : distinguishes_prop a b := by
  intro different sameCache
  exact different (Option.some.inj sameCache)

/-- The cache observation is never absent, even though the read faults. -/
def cacheNotClean_prop (kernelByte : Int) : Prop :=
  (unsafe_meltdown_read kernelByte).2 ≠ none

theorem cacheNotClean_thm (kernelByte : Int) :
    cacheNotClean_prop kernelByte := by
  simp [cacheNotClean_prop, unsafe_meltdown_read]

/-- The exact original checker also has a kernel-checked proof. -/
theorem check_passes_thm : check unsafe_meltdown_read = true := by
  decide

/-! ## Postcondition -/

/--
The pointwise observations together with the relational side-channel property.
`comparisonByte` is an arbitrary second input for comparing two executions;
it does not restrict the input to the modeled read.
-/
def Post_prop (kernelByte comparisonByte : Int) : Prop :=
  architecturalReturn_prop kernelByte ∧
  cacheLeak_prop kernelByte ∧
  distinguishes_prop kernelByte comparisonByte ∧
  cacheNotClean_prop kernelByte

/-! ## Property-based tests

These bounded tests use executable Boolean forms of every property above.
They cover all 256 byte values, negative values, and values beyond the byte
range. The pairwise tests also cover equal inputs (the vacuous implication)
and unequal inputs. Large integers check that the model does not truncate.
These are tests only; the universal theorems do not rely on them.
-/

def pbtInputs : List Int :=
  (List.range 513).map (fun n => (n : Int) - 256) ++
    [-1000000000000000000000000000000, 1000000000000000000000000000000]

-- PBT for architecturalReturn_prop.
example : pbtInputs.all (fun k =>
    (unsafe_meltdown_read k).1 == none) = true := by
  native_decide

-- PBT for cacheLeak_prop; in particular this includes 0 and 0xFF.
example : pbtInputs.all (fun k =>
    (unsafe_meltdown_read k).2 == some k) = true := by
  native_decide

-- PBT for distinguishes_prop: a = b OR the cache observations differ.
example : pbtInputs.all (fun a => pbtInputs.all (fun b =>
    (a == b) || ((unsafe_meltdown_read a).2 !=
      (unsafe_meltdown_read b).2))) = true := by
  native_decide

-- PBT for cacheNotClean_prop.
example : pbtInputs.all (fun k =>
    (unsafe_meltdown_read k).2 != none) = true := by
  native_decide

-- PBT for the entire Post_prop, over every pair in the bounded sample.
example : pbtInputs.all (fun k => pbtInputs.all (fun other =>
    ((unsafe_meltdown_read k).1 == none) &&
    ((unsafe_meltdown_read k).2 == some k) &&
    ((k == other) || ((unsafe_meltdown_read k).2 !=
      (unsafe_meltdown_read other).2)) &&
    ((unsafe_meltdown_read k).2 != none))) = true := by
  native_decide

#eval pbtInputs.length
#eval pbtInputs.all (fun k => unsafe_meltdown_read k == (none, some k))

/-! ## Correctness -/

theorem correctness_thm (kernelByte comparisonByte : Int) :
    Pre kernelByte → Post_prop kernelByte comparisonByte := by
  intro _
  exact ⟨architecturalReturn_thm kernelByte, cacheLeak_thm kernelByte,
    distinguishes_thm kernelByte comparisonByte, cacheNotClean_thm kernelByte⟩

/-! ## Imperative implementation -/

/--
The speculative load mutates the cache observation. The architectural
observation remains absent because the access faults.
-/
def unsafe_meltdown_read_imperative (kernelByte : Int) : Observation := Id.run do
  let archReturn : Option Int := none
  let mut cacheLeak : Option Int := none
  cacheLeak := some kernelByte
  return (archReturn, cacheLeak)

/-! ## Imperative tests -/

example : (unsafe_meltdown_read_imperative 0xCA).1 = none := by native_decide
example : (unsafe_meltdown_read_imperative 0xCA).2 = some 0xCA := by native_decide
example : (unsafe_meltdown_read_imperative 0).2 = some 0 := by native_decide
example : (unsafe_meltdown_read_imperative 0xFF).2 = some 0xFF := by native_decide
example : (unsafe_meltdown_read_imperative 1).2 ≠
    (unsafe_meltdown_read_imperative 2).2 := by native_decide
example : (unsafe_meltdown_read_imperative 42).2 ≠ none := by native_decide
example : check unsafe_meltdown_read_imperative = true := by native_decide
example : pbtInputs.all (fun k =>
    unsafe_meltdown_read k == unsafe_meltdown_read_imperative k) = true := by
  native_decide

#eval unsafe_meltdown_read_imperative 0xCA
#eval check unsafe_meltdown_read_imperative

/-! ## Functional/imperative equivalence -/

theorem equivalence_thm (kernelByte : Int) :
    unsafe_meltdown_read kernelByte = unsafe_meltdown_read_imperative kernelByte := by
  rfl

end UnsafeMeltdownRead
end Agent
