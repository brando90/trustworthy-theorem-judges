import Mathlib
namespace Agent

/-!
# Unsafe range check

Translation of the Python `unsafe_range_check` example from symbolic execution.
Python integers are modeled by unbounded `Int`. The implementation checks only
`low ≤ value`: the upper bound is deliberately ignored, not repaired.

There are no restrictions on the inputs, including no assumption `low ≤ high`.
The specifications characterize both the lower-bound behavior and the bug:
values above `high` pass whenever they meet the lower bound, and accepted values
above any proposed ceiling exist. The Boolean `check` encodes the conjunction
of the five assertions in the Python test harness.

Bounded property-based tests include signed integers and reversed intervals.
They are executable evidence only; all named theorems have kernel proofs.
-/

namespace UnsafeRangeCheck

/-! ## Functional implementation -/

/-- The parameter `_high` is intentionally unused. -/
def unsafe_range_check (value low _high : Int) : Bool :=
  decide (low ≤ value)

/-- Boolean version of the original assertion-based test harness. -/
def check (candidate : Int → Int → Int → Bool) : Bool :=
  candidate 5 0 10 &&
  candidate 15 0 10 &&
  !(candidate 0 5 10) &&
  candidate 5 5 10 &&
  candidate 1000 0 100

/-! ## Unit tests -/

example : unsafe_range_check 5 0 10 = true := by native_decide
example : unsafe_range_check 15 0 10 = true := by native_decide
example : unsafe_range_check 0 5 10 = false := by native_decide
example : unsafe_range_check 5 5 10 = true := by native_decide
example : unsafe_range_check 1000 0 100 = true := by native_decide
example : check unsafe_range_check = true := by native_decide

-- Signed values, equality at the upper endpoint, and reversed bounds.
example : unsafe_range_check (-5) (-10) (-3) = true := by native_decide
example : unsafe_range_check (-11) (-10) (-3) = false := by native_decide
example : unsafe_range_check 10 0 10 = true := by native_decide
example : unsafe_range_check 5 5 (-100) = true := by native_decide

#eval [unsafe_range_check 5 0 10, unsafe_range_check 15 0 10,
  unsafe_range_check 0 5 10, unsafe_range_check 5 5 10,
  unsafe_range_check 1000 0 100]
#eval check unsafe_range_check
#eval if check unsafe_range_check then "All tests passed." else "Candidate failed tests"

/-! ## Preconditions and properties -/

/-- The Python function is defined for every triple of integers. -/
def Pre (_value _low _high : Int) : Prop := True

/-- Exact characterization of successful checks. -/
def accepts_iff_prop (value low high : Int) : Prop :=
  unsafe_range_check value low high = true ↔ low ≤ value

theorem accepts_iff_thm (value low high : Int) :
    accepts_iff_prop value low high := by
  simp [accepts_iff_prop, unsafe_range_check]

/-- Exact characterization of rejection. -/
def rejects_iff_prop (value low high : Int) : Prop :=
  unsafe_range_check value low high = false ↔ value < low

theorem rejects_iff_thm (value low high : Int) :
    rejects_iff_prop value low high := by
  simp [rejects_iff_prop, unsafe_range_check, not_le]

/-- Changing the upper bound to any other integer never changes the result. -/
def upper_ignored_prop (value low high : Int) : Prop :=
  ∀ otherHigh : Int,
    unsafe_range_check value low high = unsafe_range_check value low otherHigh

theorem upper_ignored_thm (value low high : Int) :
    upper_ignored_prop value low high := by
  intro otherHigh
  rfl

/-- Values inside the intended closed interval are accepted. -/
def in_range_prop (value low high : Int) : Prop :=
  low ≤ value ∧ value ≤ high → unsafe_range_check value low high = true

theorem in_range_thm (value low high : Int) :
    in_range_prop value low high := by
  intro h
  exact (accepts_iff_thm value low high).2 h.1

/-- Equality at the lower bound is accepted, regardless of the upper bound. -/
def at_lower_bound_prop (low high : Int) : Prop :=
  unsafe_range_check low low high = true

theorem at_lower_bound_thm (low high : Int) :
    at_lower_bound_prop low high := by
  exact (accepts_iff_thm low low high).2 (le_refl low)

/-- The vulnerability: exceeding `high` does not block an otherwise valid value. -/
def above_high_prop (value low high : Int) : Prop :=
  low ≤ value → high < value → unsafe_range_check value low high = true

theorem above_high_thm (value low high : Int) :
    above_high_prop value low high := by
  intro hlow _hhigh
  exact (accepts_iff_thm value low high).2 hlow

/-- For every pair of bounds, accepted out-of-range values are unbounded above. -/
def unbounded_prop (low high : Int) : Prop :=
  ∀ bound : Int, ∃ value : Int,
    bound < value ∧ high < value ∧ low ≤ value ∧
      unsafe_range_check value low high = true

theorem unbounded_thm (low high : Int) : unbounded_prop low high := by
  intro bound
  let value : Int := max low (max high bound) + 1
  have hl : low ≤ max low (max high bound) := le_max_left _ _
  have hh : high ≤ max low (max high bound) :=
    le_trans (le_max_left high bound) (le_max_right low (max high bound))
  have hb : bound ≤ max low (max high bound) :=
    le_trans (le_max_right high bound) (le_max_right low (max high bound))
  have hlow : low ≤ value := by
    dsimp [value]
    omega
  refine ⟨value, ?_, ?_, hlow, (accepts_iff_thm value low high).2 hlow⟩
  · dsimp [value]
    omega
  · dsimp [value]
    omega

/-! ## Postcondition -/

/-- This specifies the actual unsafe behavior, not a corrected range check. -/
def Post_prop (value low high : Int) : Prop :=
  accepts_iff_prop value low high ∧
  rejects_iff_prop value low high ∧
  upper_ignored_prop value low high ∧
  in_range_prop value low high ∧
  at_lower_bound_prop low high ∧
  above_high_prop value low high ∧
  unbounded_prop low high

/-! ## Bounded property-based tests

Every executable property above, and the postcondition, has a separate PBT.
The input grid is all integers from -10 through 10, with no ordering assumption
on the bounds. Quantified alternative upper bounds are checked on this grid.
For the unbounded existential property we test its constructive witness
`max low (max high bound) + 1`, for each sampled threshold `bound`; we do not
try to decide an infinite existential or restrict the witness to the grid.
-/

private def testInts : List Int :=
  (List.range 21).map (fun n => (n : Int) - 10)

-- PBT: accepts_iff_prop.
example : testInts.all (fun value => testInts.all (fun low =>
    testInts.all (fun high =>
      decide ((unsafe_range_check value low high = true) ↔ low ≤ value)))) = true := by
  native_decide

-- PBT: rejects_iff_prop.
example : testInts.all (fun value => testInts.all (fun low =>
    testInts.all (fun high =>
      decide ((unsafe_range_check value low high = false) ↔ value < low)))) = true := by
  native_decide

-- PBT: upper_ignored_prop, including every sampled alternative upper bound.
example : testInts.all (fun value => testInts.all (fun low =>
    testInts.all (fun high => testInts.all (fun otherHigh =>
      decide (unsafe_range_check value low high =
        unsafe_range_check value low otherHigh))))) = true := by
  native_decide

-- PBT: in_range_prop, with a decidable implication (no domain restriction).
example : testInts.all (fun value => testInts.all (fun low =>
    testInts.all (fun high =>
      decide (low ≤ value ∧ value ≤ high →
        unsafe_range_check value low high = true)))) = true := by
  native_decide

-- PBT: at_lower_bound_prop, including high < low.
example : testInts.all (fun low => testInts.all (fun high =>
    unsafe_range_check low low high)) = true := by
  native_decide

-- PBT: above_high_prop.
example : testInts.all (fun value => testInts.all (fun low =>
    testInts.all (fun high =>
      decide (low ≤ value → high < value →
        unsafe_range_check value low high = true)))) = true := by
  native_decide

/-- Executable witness check for the existential in `unbounded_prop`. -/
private def unboundedWitnessCheck (low high bound : Int) : Bool :=
  let value := max low (max high bound) + 1
  decide (bound < value ∧ high < value ∧ low ≤ value ∧
    unsafe_range_check value low high = true)

-- PBT: unbounded_prop, testing its witness for every sampled threshold.
example : testInts.all (fun low => testInts.all (fun high =>
    testInts.all (fun bound => unboundedWitnessCheck low high bound))) = true := by
  native_decide

/-- Executable bounded version of every conjunct of `Post_prop`. -/
private def postCheck (value low high : Int) : Bool :=
  decide ((unsafe_range_check value low high = true) ↔ low ≤ value) &&
  decide ((unsafe_range_check value low high = false) ↔ value < low) &&
  testInts.all (fun otherHigh => decide (unsafe_range_check value low high =
    unsafe_range_check value low otherHigh)) &&
  decide (low ≤ value ∧ value ≤ high → unsafe_range_check value low high = true) &&
  unsafe_range_check low low high &&
  decide (low ≤ value → high < value → unsafe_range_check value low high = true) &&
  testInts.all (fun bound => unboundedWitnessCheck low high bound)

-- PBT: Post_prop. Pre is True, so every sampled input is admissible.
example : testInts.all (fun value => testInts.all (fun low =>
    testInts.all (fun high => postCheck value low high))) = true := by
  native_decide

#eval testInts.all (fun value => testInts.all (fun low =>
  testInts.all (fun high => postCheck value low high)))

/-! ## Correctness relative to the deliberately unsafe specification -/

theorem correctness_thm (value low high : Int) :
    Pre value low high → Post_prop value low high := by
  intro _hpre
  exact ⟨accepts_iff_thm value low high,
    rejects_iff_thm value low high,
    upper_ignored_thm value low high,
    in_range_thm value low high,
    at_lower_bound_thm low high,
    above_high_thm value low high,
    unbounded_thm low high⟩

/-! ## Imperative implementation and tests -/

/-- A mutable-state implementation with the same missing upper-bound check. -/
def unsafe_range_check_imp (value low _high : Int) : Bool := Id.run do
  let mut accepted := false
  if low ≤ value then
    accepted := true
  return accepted

example : unsafe_range_check_imp 5 0 10 = true := by native_decide
example : unsafe_range_check_imp 15 0 10 = true := by native_decide
example : unsafe_range_check_imp 0 5 10 = false := by native_decide
example : unsafe_range_check_imp 5 5 10 = true := by native_decide
example : unsafe_range_check_imp 1000 0 100 = true := by native_decide
example : check unsafe_range_check_imp = true := by native_decide
example : unsafe_range_check_imp (-5) (-10) (-3) = true := by native_decide
example : unsafe_range_check_imp 5 5 (-100) = true := by native_decide

#eval [unsafe_range_check_imp 5 0 10, unsafe_range_check_imp 15 0 10,
  unsafe_range_check_imp 0 5 10, unsafe_range_check_imp 5 5 10,
  unsafe_range_check_imp 1000 0 100]
#eval check unsafe_range_check_imp

-- Additional bounded comparison of both implementations.
example : testInts.all (fun value => testInts.all (fun low =>
    testInts.all (fun high => decide (unsafe_range_check value low high =
      unsafe_range_check_imp value low high)))) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem equivalence_thm (value low high : Int) :
    unsafe_range_check value low high = unsafe_range_check_imp value low high := by
  by_cases h : low ≤ value <;>
    simp [unsafe_range_check, unsafe_range_check_imp, h]

end UnsafeRangeCheck
end Agent
