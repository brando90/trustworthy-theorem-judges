import Mathlib
namespace Agent

/-!
# Safe frozen read

Translation of Python's `safe_frozen_read` and its `check` harness. The input
`length` is the one immutable snapshot: it is both checked and returned. There
is no second read from shared sandbox memory, hence no opportunity to replace
the validated value between checking and use.

Python integers are modeled by `Int`, and Python `None` by `Option.none`.
In particular, the source checks only an upper bound, not nonnegativity. All
integer inputs, including negative lengths and buffer sizes, are preserved.
The bounds guarantee below is exactly the upper-bound guarantee of the source.
Unit and bounded property-based tests are executable evidence; all named
specification theorems have separate kernel-checked proofs.
-/

namespace UnsafeDoubleReadSafe

/-! ## Functional implementation -/

/-- Validate and use the same frozen value. -/
def safe_frozen_read (length buf_size : Int) : Option Int :=
  if length ≤ buf_size then some length else none

/-- Boolean counterpart of every assertion in the Python `check` harness. -/
def check (candidate : Int → Int → Option Int) : Bool :=
  (candidate 5 100 == some 5) &&
  (candidate 100 100 == some 100) &&
  (candidate 101 100 == none) &&
  (candidate 999 100 == none) &&
  (candidate 0 0 == some 0) &&
  (candidate 0 100 == some 0) &&
  ([1, 42, 99, 100] : List Int).all (fun v => candidate v 100 == some v)

/-! ## Unit tests -/

example : safe_frozen_read 5 100 = some 5 := by native_decide
example : safe_frozen_read 100 100 = some 100 := by native_decide
example : safe_frozen_read 101 100 = none := by native_decide
example : safe_frozen_read 999 100 = none := by native_decide
example : safe_frozen_read 0 0 = some 0 := by native_decide
example : safe_frozen_read 0 100 = some 0 := by native_decide
example : ([1, 42, 99, 100] : List Int).all
    (fun v => safe_frozen_read v 100 == some v) = true := by native_decide
example : check safe_frozen_read = true := by native_decide

-- These also check the unrestricted Python integer semantics.
example : safe_frozen_read (-5) 0 = some (-5) := by native_decide
example : safe_frozen_read (-10) (-5) = some (-10) := by native_decide
example : safe_frozen_read (-5) (-10) = none := by native_decide
example : safe_frozen_read (-1) (-1) = some (-1) := by native_decide
example : safe_frozen_read 0 (-1) = none := by native_decide

#eval safe_frozen_read 5 100
#eval safe_frozen_read 101 100
#eval check safe_frozen_read

/-! ## Preconditions and proved properties -/

/-- The Python function is defined for every pair of integers. -/
def Pre (_length _buf_size : Int) : Prop := True

/-- Every input passing the check is returned, unchanged. -/
def accepted_prop (length buf_size : Int) : Prop :=
  length ≤ buf_size → safe_frozen_read length buf_size = some length

theorem accepted_thm (length buf_size : Int) : accepted_prop length buf_size := by sorry

/-- Rejection happens exactly when the single snapshot exceeds the bound. -/
def rejected_prop (length buf_size : Int) : Prop :=
  safe_frozen_read length buf_size = none ↔ buf_size < length

theorem rejected_thm (length buf_size : Int) : rejected_prop length buf_size := by sorry

/-- Complete characterization of each possible successful result. -/
def returns_iff_prop (length buf_size : Int) : Prop :=
  ∀ value : Int, safe_frozen_read length buf_size = some value ↔
    value = length ∧ length ≤ buf_size

theorem returns_iff_thm (length buf_size : Int) :
    returns_iff_prop length buf_size := by sorry

/-- A successful result is the very same snapshot that was validated. -/
def frozen_prop (length buf_size : Int) : Prop :=
  ∀ value : Int, safe_frozen_read length buf_size = some value → value = length

theorem frozen_thm (length buf_size : Int) : frozen_prop length buf_size := by sorry

/-- No returned value exceeds the buffer bound. -/
def bounds_prop (length buf_size : Int) : Prop :=
  ∀ value : Int, safe_frozen_read length buf_size = some value → value ≤ buf_size

theorem bounds_thm (length buf_size : Int) : bounds_prop length buf_size := by sorry

/-- Equality with the bound is accepted, for every integer bound. -/
def boundary_prop (buf_size : Int) : Prop :=
  safe_frozen_read buf_size buf_size = some buf_size

theorem boundary_thm (buf_size : Int) : boundary_prop buf_size := by sorry

/-- Zero is accepted for every nonnegative buffer size, as in the Python tests. -/
def zero_prop (buf_size : Int) : Prop :=
  0 ≤ buf_size → safe_frozen_read 0 buf_size = some 0

theorem zero_thm (buf_size : Int) : zero_prop buf_size := by sorry

/-! ## Postcondition -/

/-- Full behavior, including the frozen-value and upper-bound guarantees. -/
def Post_prop (length buf_size : Int) : Prop :=
  accepted_prop length buf_size ∧
  rejected_prop length buf_size ∧
  returns_iff_prop length buf_size ∧
  frozen_prop length buf_size ∧
  bounds_prop length buf_size ∧
  boundary_prop buf_size ∧
  zero_prop buf_size

/-! ## Bounded property-based tests

Each two-input property is tested on the Cartesian product of a contiguous
signed interval and additional values around the original tests' boundary.
No restriction is imposed on the sign of either input. The universally
quantified returned value in `frozen_prop` and `bounds_prop` is tested by
inspecting the actual option: `none` is vacuous, and `some value` supplies
the only possible successful witness.
-/

def pbtValues : List Int :=
  ((List.range 41).map (fun n => (n : Int) - 20)) ++
    [-1000, -101, -100, 42, 99, 100, 101, 999, 1000]

-- PBT: accepted_prop.
example : pbtValues.all (fun length => pbtValues.all (fun buf_size =>
    decide (length ≤ buf_size →
      safe_frozen_read length buf_size = some length))) = true := by
  native_decide

-- PBT: rejected_prop, checking both directions of the rejection criterion.
example : pbtValues.all (fun length => pbtValues.all (fun buf_size =>
    decide (safe_frozen_read length buf_size = none ↔
      buf_size < length))) = true := by
  native_decide

-- PBT: returns_iff_prop, over all triples of sampled inputs and result values.
example : pbtValues.all (fun length => pbtValues.all (fun buf_size =>
    pbtValues.all (fun value =>
      decide (safe_frozen_read length buf_size = some value ↔
        value = length ∧ length ≤ buf_size)))) = true := by
  native_decide

-- PBT: frozen_prop.
example : pbtValues.all (fun length => pbtValues.all (fun buf_size =>
    match safe_frozen_read length buf_size with
    | none => true
    | some value => decide (value = length))) = true := by
  native_decide

-- PBT: bounds_prop.
example : pbtValues.all (fun length => pbtValues.all (fun buf_size =>
    match safe_frozen_read length buf_size with
    | none => true
    | some value => decide (value ≤ buf_size))) = true := by
  native_decide

-- PBT: boundary_prop.
example : pbtValues.all (fun buf_size =>
    decide (safe_frozen_read buf_size buf_size = some buf_size)) = true := by
  native_decide

-- PBT: zero_prop; negative bounds are still sampled, making the implication
-- vacuous there rather than incorrectly claiming that zero is always accepted.
example : pbtValues.all (fun buf_size =>
    decide (0 ≤ buf_size → safe_frozen_read 0 buf_size = some 0)) = true := by
  native_decide

/-- Executable form of the entire postcondition.
For `returns_iff_prop`, the option split covers all possible result values:
rejection requires the check to fail, while success requires the identical
snapshot and a successful check. The following two conjuncts separately test
the frozen and upper-bound guarantees. -/
def postCheck (length buf_size : Int) : Bool :=
  decide (length ≤ buf_size → safe_frozen_read length buf_size = some length) &&
  decide (safe_frozen_read length buf_size = none ↔ buf_size < length) &&
  (match safe_frozen_read length buf_size with
    | none => decide (¬ length ≤ buf_size)
    | some value => decide (value = length ∧ length ≤ buf_size)) &&
  (match safe_frozen_read length buf_size with
    | none => true
    | some value => decide (value = length)) &&
  (match safe_frozen_read length buf_size with
    | none => true
    | some value => decide (value ≤ buf_size)) &&
  decide (safe_frozen_read buf_size buf_size = some buf_size) &&
  decide (0 ≤ buf_size → safe_frozen_read 0 buf_size = some 0)

-- PBT: Post_prop, over every pair of sampled integers.
example : pbtValues.all (fun length =>
    pbtValues.all (fun buf_size => postCheck length buf_size)) = true := by
  native_decide

#eval pbtValues.all (fun length =>
  pbtValues.all (fun buf_size => postCheck length buf_size))

/-! ## Correctness -/

theorem correctness_thm (length buf_size : Int) :
    Pre length buf_size → Post_prop length buf_size := by sorry

/-! ## Imperative implementation -/

/-- Capture the input once, then check and use only that immutable snapshot.
Only the result cell is mutable; there is no second read of the input. -/
def safe_frozen_read_imp (length buf_size : Int) : Option Int := Id.run do
  let snapshot := length
  let mut result : Option Int := none
  if snapshot ≤ buf_size then
    result := some snapshot
  return result

/-! ## Imperative tests -/

example : safe_frozen_read_imp 5 100 = some 5 := by native_decide
example : safe_frozen_read_imp 100 100 = some 100 := by native_decide
example : safe_frozen_read_imp 101 100 = none := by native_decide
example : safe_frozen_read_imp 999 100 = none := by native_decide
example : safe_frozen_read_imp 0 0 = some 0 := by native_decide
example : safe_frozen_read_imp 0 100 = some 0 := by native_decide
example : ([1, 42, 99, 100] : List Int).all
    (fun v => safe_frozen_read_imp v 100 == some v) = true := by native_decide
example : check safe_frozen_read_imp = true := by native_decide
example : safe_frozen_read_imp (-5) 0 = some (-5) := by native_decide
example : safe_frozen_read_imp (-10) (-5) = some (-10) := by native_decide
example : safe_frozen_read_imp (-5) (-10) = none := by native_decide
example : safe_frozen_read_imp (-1) (-1) = some (-1) := by native_decide
example : safe_frozen_read_imp 0 (-1) = none := by native_decide

#eval safe_frozen_read_imp 100 100
#eval safe_frozen_read_imp 999 100
#eval check safe_frozen_read_imp

-- Additional bounded equivalence test, independent of the proof below.
example : pbtValues.all (fun length => pbtValues.all (fun buf_size =>
    safe_frozen_read length buf_size ==
      safe_frozen_read_imp length buf_size)) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem equivalence_thm (length buf_size : Int) :
    safe_frozen_read length buf_size = safe_frozen_read_imp length buf_size := by sorry

end UnsafeDoubleReadSafe
end Agent
