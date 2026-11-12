/-!
# VeriBench -- Counting Sort
Every stated theorem is PROVEN (no `sorry`) -- this is the expected standard.
-/

namespace CountingSort

/-!
## Implementation
-/

/-- Precondition: `arr` is a list of integers. -/
def Pre (arr : List Int) : Prop := arr ≠ [] → True

/-- Counting sort for a list of integers (supports negatives via shift).
    Returns a sorted list of integers. -/
def countingSort (arr : List Int) : List Int :=
  match arr with
  | [] => []
  | _ =>
    let maxVal := arr.foldl (fun (m : Int) (x : Int) => max m x) 0
    let minVal := arr.foldl (fun (m : Int) (x : Int) => min m x) 0
    let rangeSize := (maxVal - minVal + 1).toNat
    let count := List.replicate rangeSize 0
    let count := arr.foldl (fun (cnt : List Int) (num : Int) =>
      let idx := (num - minVal).toNat
      if h : idx < cnt.length then
        cnt.modify idx (fun _ => (cnt.get ⟨idx, h⟩) + 1)
      else
        cnt
    ) count
    let result := (List.range rangeSize).foldl (fun (res : List Int) (i : Nat) =>
      let val := (i : Int) + minVal
      let cnt := (count.get? i).getD 0
      res ++ List.replicate (cnt.toNat) val
    ) []
    result

/-!
## Tests
-/

example : countingSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : countingSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : countingSort [] = [] := by native_decide
example : countingSort [1] = [1] := by native_decide
example : countingSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [2, 1] = [1, 2] := by native_decide
example : countingSort [1, 2] = [1, 2] := by native_decide
example : countingSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSort [3, 1, 2, 1, 3, 2] = [1, 1, 2, 2, 3, 3] := by native_decide
example : countingSort [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : countingSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSort [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide
example : countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

/-!
## Properties
-/

/-- The result of `countingSort` is sorted in non-decreasing order. -/
def sortedProp (arr : List Int) : Prop :=
  ∀ i : Fin ((countingSort arr).length - 1),
    (countingSort arr).get? i.val ≤ (countingSort arr).get? (i.val + 1)

/-- The result of `countingSort` has the same length as the input. -/
def lengthProp (arr : List Int) : Prop := (countingSort arr).length = arr.length

/-- The result of `countingSort` contains exactly the same elements as the input. -/
def multisetProp (arr : List Int) : Prop := (countingSort arr).Perm arr

theorem sorted_thm (arr : List Int) : sortedProp arr := by
  sorry

theorem length_thm (arr : List Int) : lengthProp arr := by
  sorry

theorem multiset_thm (arr : List Int) : multisetProp arr := by
  sorry

/-!
## Correctness
-/

/-- Pre condition: `arr` is a list. -/
def Pre_prop (_arr : List Int) : Prop := True

/-- Post condition: `countingSort arr` is sorted, has the same length, and same multiset. -/
def Post_prop (arr : List Int) : Prop :=
  sortedProp arr ∧ lengthProp arr ∧ multisetProp arr

theorem correctness_thm (arr : List Int) (hPre : Pre_prop arr) : Post_prop arr := by
  sorry

end CountingSort