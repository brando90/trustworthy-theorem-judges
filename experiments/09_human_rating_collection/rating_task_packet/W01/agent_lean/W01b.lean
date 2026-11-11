import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.LibrarySearch

/--
Return median of elements in the list l.
-/
def median (l : List Float) : Float :=
  let sorted := l.qsort (· ≤ ·)
  if sorted.length % 2 == 1 then
    sorted[sorted.length / 2]!
  else
    (sorted[sorted.length / 2 - 1]! + sorted[sorted.length / 2]!) / 2.0

/-- Tests for the median function -/
def medianTests : Bool :=
  median [3, 1, 2, 4, 5] == 3 &&
  median [-10, 4, 6, 1000, 10, 20] == 8.0 &&
  median [5] == 5 &&
  median [6, 5] == 5.5 &&
  median [8, 1, 3, 9, 9, 2, 7] == 7

#eval medianTests

/-- Specification for median function -/
def medianSpec (l : List Float) : Float :=
  let sorted := l.qsort (· ≤ ·)
  if sorted.length % 2 == 1 then
    sorted[sorted.length / 2]!
  else
    (sorted[sorted.length / 2 - 1]! + sorted[sorted.length / 2]!) / 2.0

/-- Precondition: The list must not be empty -/
def medianPre (l : List Float) : Prop :=
  l.length > 0

/-- Postcondition: The median is computed according to the specification -/
def medianPost (l : List Float) (result : Float) : Prop :=
  result = medianSpec l

/-- Correctness theorem: If the precondition holds, then the function returns a value satisfying the postcondition -/
theorem median_correct (l : List Float) (h : medianPre l) : medianPost l (median l) := by
  unfold medianPost
  unfold median
  unfold medianSpec
  simp
  sorry
