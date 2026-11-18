import Std.Data.List.Basic

def median (l: List Int) : Float :=
  let sorted := l.qsort (·<=·)
  if sorted.length % 2 == 1 then
    sorted[sorted.length / 2]!.toFloat
  else
    let mid := sorted.length / 2
    (sorted[mid - 1]!.toFloat + sorted[mid]!.toFloat) / 2.0

def median_spec (l: List Int) : Float :=
  let sorted := l.qsort (·<=·)
  if sorted.length % 2 == 1 then
    sorted[sorted.length / 2]!.toFloat
  else
    let mid := sorted.length / 2
    (sorted[mid - 1]!.toFloat + sorted[mid]!.toFloat) / 2.0

/-- Precondition: The list must not be empty. -/
def median_pre (l: List Int) : Prop :=
  l.length > 0

/-- Postcondition: The result is the median value of the list. -/
def median_post (l: List Int) (result: Float) : Prop :=
  result = median_spec l

theorem median_correct (l: List Int) (h: median_pre l) : median_post l (median l) := by
  sorry

def main : IO Unit := do
  -- Test case 1
  let test1 := [3, 1, 2, 4, 5]
  IO.println s!"median({test1}) = {median test1}"
  assert! median test1 == 3

  -- Test case 2
  let test2 := [-10, 4, 6, 1000, 10, 20]
  IO.println s!"median({test2}) = {median test2}"
  assert! median test2 == 8.0

  -- Test case 3
  let test3 := [5]
  IO.println s!"median({test3}) = {median test3}"
  assert! median test3 == 5

  -- Test case 4
  let test4 := [6, 5]
  IO.println s!"median({test4}) = {median test4}"
  assert! median test4 == 5.5

  -- Test case 5
  let test5 := [8, 1, 3, 9, 9, 2, 7]
  IO.println s!"median({test5}) = {median test5}"
  assert! median test5 == 7

  IO.println "All tests passed!"
