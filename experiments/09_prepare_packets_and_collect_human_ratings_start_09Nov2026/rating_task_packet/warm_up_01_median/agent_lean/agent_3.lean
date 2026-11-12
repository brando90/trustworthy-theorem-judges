/-
# File: humaneval_47_median.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic

namespace HumanEval47

/--
Return median of elements in the list l.
-/
def median (l : List Int) : Float :=
  let sorted := l.sort (· ≤ ·)
  let n := sorted.length
  if n % 2 == 1 then
    sorted[n / 2]!.toFloat
  else
    (sorted[n / 2 - 1]!.toFloat + sorted[n / 2]!.toFloat) / 2.0

/-- Specification for median function -/
def medianSpec (l : List Int) : Float :=
  let sorted := l.sort (· ≤ ·)
  let n := sorted.length
  if n % 2 == 1 then
    sorted[n / 2]!.toFloat
  else
    (sorted[n / 2 - 1]!.toFloat + sorted[n / 2]!.toFloat) / 2.0

/-- Precondition: list must be non-empty -/
def medianPre (l : List Int) : Prop :=
  l.length > 0

/-- Postcondition: result is the median value of the list -/
def medianPost (l : List Int) (result : Float) : Prop :=
  result = medianSpec l

/-- Correctness theorem for median function -/
theorem median_correct (l : List Int) (h : medianPre l) : medianPost l (median l) := by
  sorry

/-- Tests for median function -/
def tests : List (List Int × Float) := [
  ([3, 1, 2, 4, 5], 3.0),
  ([-10, 4, 6, 1000, 10, 20], 8.0),
  ([5], 5.0),
  ([6, 5], 5.5),
  ([8, 1, 3, 9, 9, 2, 7], 7.0)
]

/-- Run all tests -/
def runTests : List Bool :=
  tests.map (fun (input, expected) => median input == expected)

/-- Check if all tests pass -/
theorem allTestsPass : runTests.all id = true := by
  sorry

end HumanEval47
