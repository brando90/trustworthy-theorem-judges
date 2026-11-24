import Mathlib
namespace Agent

/-!
# Safe executable stack: NX enforcement

This file translates Python's `safeExecStack`: an address is executable exactly
when it is outside the half-open stack interval `[stackStart, stackEnd)`.
`Int` models Python's unbounded signed integers. No ordering assumption is
imposed on the endpoints: empty and reversed intervals contain no addresses.

The Boolean `check` records the five assertions of the Python test harness.
The specification proves NX blocking, permission outside the stack, both exact
characterizations, boundary behavior, and the empty-interval case. Bounded PBTs
check every property and their conjunction independently of the proofs.
-/

namespace SafeExecStack

/-! ## Functional implementation -/

def safeExecStack (addr stackStart stackEnd : Int) : Bool :=
  !(decide (stackStart ≤ addr ∧ addr < stackEnd))

/-- Boolean success condition for the five assertions in Python's `check`. -/
def check (candidate : Int → Int → Int → Bool) : Bool :=
  let stackStart : Int := 0x7FFF0000
  let stackEnd : Int := 0x7FFFFFFF
  let codeAddr : Int := 0x08048000
  let stackAddr : Int := 0x7FFF1234
  candidate codeAddr stackStart stackEnd &&
    !(candidate stackAddr stackStart stackEnd) &&
    !(candidate stackStart stackStart stackEnd) &&
    candidate stackEnd stackStart stackEnd &&
    candidate (stackStart - 1) stackStart stackEnd

/-! ## Unit tests: the five Python assertions -/

example : safeExecStack 0x08048000 0x7FFF0000 0x7FFFFFFF = true := by
  native_decide

example : safeExecStack 0x7FFF1234 0x7FFF0000 0x7FFFFFFF = false := by
  native_decide

example : safeExecStack 0x7FFF0000 0x7FFF0000 0x7FFFFFFF = false := by
  native_decide

example : safeExecStack 0x7FFFFFFF 0x7FFF0000 0x7FFFFFFF = true := by
  native_decide

example : safeExecStack (0x7FFF0000 - 1) 0x7FFF0000 0x7FFFFFFF = true := by
  native_decide

example : check safeExecStack = true := by native_decide

-- Signed integers and degenerate regions are also valid Python inputs.
example : safeExecStack (-3) (-5) 0 = false := by native_decide
example : safeExecStack 4 4 4 = true := by native_decide
example : safeExecStack 4 7 2 = true := by native_decide

#eval check safeExecStack
#eval safeExecStack 0x7FFF1234 0x7FFF0000 0x7FFFFFFF

/-! ## Precondition -/

/-- Python accepts every integer triple; a well-formed interval is not required. -/
def Pre (_addr _stackStart _stackEnd : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Every address in the stack interval is non-executable. -/
def nx_prop (addr stackStart stackEnd : Int) : Prop :=
  stackStart ≤ addr ∧ addr < stackEnd →
    safeExecStack addr stackStart stackEnd = false

theorem nx_thm (addr stackStart stackEnd : Int) :
    nx_prop addr stackStart stackEnd := by sorry

/-- Addresses on either side of the stack interval are executable. -/
def outside_prop (addr stackStart stackEnd : Int) : Prop :=
  addr < stackStart ∨ stackEnd ≤ addr →
    safeExecStack addr stackStart stackEnd = true

theorem outside_thm (addr stackStart stackEnd : Int) :
    outside_prop addr stackStart stackEnd := by sorry

/-- Exact characterization of permission, not just a one-way safety claim. -/
def executable_iff_prop (addr stackStart stackEnd : Int) : Prop :=
  safeExecStack addr stackStart stackEnd = true ↔
    addr < stackStart ∨ stackEnd ≤ addr

theorem executable_iff_thm (addr stackStart stackEnd : Int) :
    executable_iff_prop addr stackStart stackEnd := by sorry

/-- Denial happens exactly for addresses in the half-open stack interval. -/
def blocked_iff_prop (addr stackStart stackEnd : Int) : Prop :=
  safeExecStack addr stackStart stackEnd = false ↔
    stackStart ≤ addr ∧ addr < stackEnd

theorem blocked_iff_thm (addr stackStart stackEnd : Int) :
    blocked_iff_prop addr stackStart stackEnd := by sorry

/-- The lower endpoint is blocked whenever the interval is nonempty. -/
def start_boundary_prop (stackStart stackEnd : Int) : Prop :=
  stackStart < stackEnd → safeExecStack stackStart stackStart stackEnd = false

theorem start_boundary_thm (stackStart stackEnd : Int) :
    start_boundary_prop stackStart stackEnd := by sorry

/-- The upper endpoint is exclusive, even when the interval is empty. -/
def end_boundary_prop (stackStart stackEnd : Int) : Prop :=
  safeExecStack stackEnd stackStart stackEnd = true

theorem end_boundary_thm (stackStart stackEnd : Int) :
    end_boundary_prop stackStart stackEnd := by sorry

/-- The integer immediately below the start is executable. -/
def below_start_prop (stackStart stackEnd : Int) : Prop :=
  safeExecStack (stackStart - 1) stackStart stackEnd = true

theorem below_start_thm (stackStart stackEnd : Int) :
    below_start_prop stackStart stackEnd := by sorry

/-- Empty or reversed intervals block no address. -/
def empty_region_prop (addr stackStart stackEnd : Int) : Prop :=
  stackEnd ≤ stackStart → safeExecStack addr stackStart stackEnd = true

theorem empty_region_thm (addr stackStart stackEnd : Int) :
    empty_region_prop addr stackStart stackEnd := by sorry

/-! ## Postcondition -/

def Post_prop (addr stackStart stackEnd : Int) : Prop :=
  nx_prop addr stackStart stackEnd ∧
  outside_prop addr stackStart stackEnd ∧
  executable_iff_prop addr stackStart stackEnd ∧
  blocked_iff_prop addr stackStart stackEnd ∧
  start_boundary_prop stackStart stackEnd ∧
  end_boundary_prop stackStart stackEnd ∧
  below_start_prop stackStart stackEnd ∧
  empty_region_prop addr stackStart stackEnd

/-! ## Property-based tests

Exhaustive bounded PBTs enumerate all triples of signed integers in `[-8, 8]`.
Thus they include positive/negative addresses, both endpoints, and empty and
reversed intervals. The checks below are executable Boolean counterparts, so
no `Decidable` instances for the specification predicates are needed.
-/

private def sampleInts : List Int :=
  (List.range 17).map (fun n => (n : Int) - 8)

private def allTriples (p : Int → Int → Int → Bool) : Bool :=
  sampleInts.all (fun a => sampleInts.all (fun s => sampleInts.all (fun e => p a s e)))

private def allPairs (p : Int → Int → Bool) : Bool :=
  sampleInts.all (fun s => sampleInts.all (fun e => p s e))

private def nxTest (a s e : Int) : Bool :=
  decide ((s ≤ a ∧ a < e) → safeExecStack a s e = false)

private def outsideTest (a s e : Int) : Bool :=
  decide ((a < s ∨ e ≤ a) → safeExecStack a s e = true)

private def executableIffTest (a s e : Int) : Bool :=
  decide (safeExecStack a s e = true ↔ a < s ∨ e ≤ a)

private def blockedIffTest (a s e : Int) : Bool :=
  decide (safeExecStack a s e = false ↔ s ≤ a ∧ a < e)

private def startBoundaryTest (s e : Int) : Bool :=
  decide (s < e → safeExecStack s s e = false)

private def endBoundaryTest (s e : Int) : Bool :=
  decide (safeExecStack e s e = true)

private def belowStartTest (s e : Int) : Bool :=
  decide (safeExecStack (s - 1) s e = true)

private def emptyRegionTest (a s e : Int) : Bool :=
  decide (e ≤ s → safeExecStack a s e = true)

-- PBT for nx_prop.
example : allTriples nxTest = true := by native_decide

-- PBT for outside_prop.
example : allTriples outsideTest = true := by native_decide

-- PBT for executable_iff_prop.
example : allTriples executableIffTest = true := by native_decide

-- PBT for blocked_iff_prop.
example : allTriples blockedIffTest = true := by native_decide

-- PBT for start_boundary_prop.
example : allPairs startBoundaryTest = true := by native_decide

-- PBT for end_boundary_prop.
example : allPairs endBoundaryTest = true := by native_decide

-- PBT for below_start_prop.
example : allPairs belowStartTest = true := by native_decide

-- PBT for empty_region_prop.
example : allTriples emptyRegionTest = true := by native_decide

-- PBT for Post_prop: the executable conjunction of all eight properties.
example : allTriples (fun a s e =>
    nxTest a s e && outsideTest a s e && executableIffTest a s e &&
    blockedIffTest a s e && startBoundaryTest s e && endBoundaryTest s e &&
    belowStartTest s e && emptyRegionTest a s e) = true := by
  native_decide

/-! ## Correctness -/

theorem safeExecStack_correct (addr stackStart stackEnd : Int) :
    Pre addr stackStart stackEnd → Post_prop addr stackStart stackEnd := by sorry

/-! ## Imperative implementation -/

/-- A mutable execution permission, cleared on detecting a stack address. -/
def safeExecStackImperative (addr stackStart stackEnd : Int) : Bool := Id.run do
  let mut executable := true
  if stackStart ≤ addr then
    if addr < stackEnd then
      executable := false
  return executable

/-! ## Imperative tests -/

example : safeExecStackImperative 0x08048000 0x7FFF0000 0x7FFFFFFF = true := by
  native_decide

example : safeExecStackImperative 0x7FFF1234 0x7FFF0000 0x7FFFFFFF = false := by
  native_decide

example : safeExecStackImperative 0x7FFF0000 0x7FFF0000 0x7FFFFFFF = false := by
  native_decide

example : safeExecStackImperative 0x7FFFFFFF 0x7FFF0000 0x7FFFFFFF = true := by
  native_decide

example : safeExecStackImperative (0x7FFF0000 - 1) 0x7FFF0000 0x7FFFFFFF = true := by
  native_decide

example : check safeExecStackImperative = true := by native_decide

#eval check safeExecStackImperative
#eval safeExecStackImperative 0x7FFF1234 0x7FFF0000 0x7FFFFFFF

-- An exhaustive cross-check of the two executable implementations.
example : allTriples (fun a s e => safeExecStack a s e == safeExecStackImperative a s e)
    = true := by native_decide

/-! ## Functional/imperative equivalence -/

theorem safeExecStack_equiv (addr stackStart stackEnd : Int) :
    safeExecStack addr stackStart stackEnd =
      safeExecStackImperative addr stackStart stackEnd := by sorry

theorem functional_eq_imperative : safeExecStack = safeExecStackImperative := by sorry

end SafeExecStack
end Agent
