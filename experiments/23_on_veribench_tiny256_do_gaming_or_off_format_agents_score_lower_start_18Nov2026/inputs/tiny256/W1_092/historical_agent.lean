import Mathlib
namespace Agent

/-!
# HumanEval 26: remove duplicates

Python's unbounded integers are represented by `Int`. An element is retained
precisely when its frequency in the whole input is at most one. Filtering the
original list preserves the order of all retained elements; repeated values
are removed altogether, rather than being kept once.
-/

namespace humaneval_26_remove_duplicates

/-- Functional version of the Counter-based Python list comprehension. -/
def remove_duplicates (numbers : List Int) : List Int :=
  numbers.filter (fun n => decide (numbers.count n ≤ 1))

example : remove_duplicates [] = [] := by native_decide
example : remove_duplicates [1, 2, 3, 4] = [1, 2, 3, 4] := by native_decide
example : remove_duplicates [1, 2, 3, 2, 4, 3, 5] = [1, 4, 5] := by native_decide
example : remove_duplicates [1, 2, 3, 2, 4] = [1, 3, 4] := by native_decide
example : remove_duplicates [-3, 0, -3, 4, 0, -8] = [4, -8] := by native_decide
example : remove_duplicates [7, 7, 7] = [] := by native_decide
#eval remove_duplicates [1, 2, 3, 2, 4]
#eval remove_duplicates [1, 2, 3, 2, 4, 3, 5]

/-- There are no restrictions on lists of Python integers. -/
def Pre (_numbers : List Int) : Prop := True

/-- Exactly the values occurring once in the input survive. -/
def membership_prop (numbers result : List Int) : Prop :=
  ∀ n : Int, n ∈ result ↔ numbers.count n = 1

theorem membership_thm (numbers : List Int) :
    membership_prop numbers (remove_duplicates numbers) := by
  intro n
  simp only [remove_duplicates, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hm, hc⟩
    have hpos := List.count_pos_iff.mpr hm
    omega
  · intro h
    exact ⟨List.count_pos_iff.mp (by omega), by omega⟩

/-- Retained elements occur in their original order. -/
def order_prop (numbers result : List Int) : Prop :=
  result.Sublist numbers

theorem order_thm (numbers : List Int) :
    order_prop numbers (remove_duplicates numbers) := by
  exact List.filter_sublist

/-- A unique input value has output multiplicity one; every other value has zero. -/
def multiplicity_prop (numbers result : List Int) : Prop :=
  ∀ n : Int, result.count n = if numbers.count n = 1 then 1 else 0

theorem multiplicity_thm (numbers : List Int) :
    multiplicity_prop numbers (remove_duplicates numbers) := by
  intro n
  by_cases h : numbers.count n = 1
  · have hp : decide (numbers.count n ≤ 1) = true := by simp [h]
    rw [if_pos h]
    exact (List.count_filter (l := numbers) hp).trans h
  · have hn : n ∉ remove_duplicates numbers := by
      rw [membership_thm numbers n]
      exact h
    simp [h, List.count_eq_zero_of_not_mem hn]

/-- In particular, the output never contains duplicate values. -/
def nodup_prop (_numbers result : List Int) : Prop := result.Nodup

theorem nodup_thm (numbers : List Int) :
    nodup_prop numbers (remove_duplicates numbers) := by
  apply List.nodup_iff_count_le_one.mpr
  intro n
  rw [multiplicity_thm numbers n]
  split <;> omega

/-- Filtering cannot increase the length. -/
def length_prop (numbers result : List Int) : Prop :=
  result.length ≤ numbers.length

theorem length_thm (numbers : List Int) :
    length_prop numbers (remove_duplicates numbers) := by
  exact (order_thm numbers).length_le

/-- A list with no repeated values is returned unchanged. -/
def unchanged_prop (numbers result : List Int) : Prop :=
  numbers.Nodup → result = numbers

theorem unchanged_thm (numbers : List Int) :
    unchanged_prop numbers (remove_duplicates numbers) := by
  intro hn
  apply List.filter_eq_self.mpr
  intro n _hm
  simp only [decide_eq_true_eq]
  exact (List.nodup_iff_count_le_one.mp hn) n

/-- Removing repeated values a second time has no further effect. -/
def idempotent_prop (_numbers result : List Int) : Prop :=
  remove_duplicates result = result

theorem idempotent_thm (numbers : List Int) :
    idempotent_prop numbers (remove_duplicates numbers) := by
  exact unchanged_thm (remove_duplicates numbers) (nodup_thm numbers)

/-- Complete observable behavior: exact values and multiplicities in input order,
with the resulting uniqueness, size, identity, and fixed-point guarantees. -/
def Post_prop (numbers result : List Int) : Prop :=
  membership_prop numbers result ∧
  order_prop numbers result ∧
  multiplicity_prop numbers result ∧
  nodup_prop numbers result ∧
  length_prop numbers result ∧
  unchanged_prop numbers result ∧
  idempotent_prop numbers result

/-! ## Property-based tests
The randomized checks use executable forms of the propositions. Integer
quantifiers in membership and multiplicity are sampled explicitly.
-/

-- PBT for membership_prop.
#eval Plausible.Testable.check (∀ (xs : List Int) (n : Int),
  n ∈ remove_duplicates xs ↔ xs.count n = 1)
-- PBT for order_prop.
#eval Plausible.Testable.check (∀ xs : List Int,
  (remove_duplicates xs).Sublist xs)
-- PBT for multiplicity_prop.
#eval Plausible.Testable.check (∀ (xs : List Int) (n : Int),
  (remove_duplicates xs).count n = if xs.count n = 1 then 1 else 0)
-- PBT for nodup_prop.
#eval Plausible.Testable.check (∀ xs : List Int,
  (remove_duplicates xs).Nodup)
-- PBT for length_prop.
#eval Plausible.Testable.check (∀ xs : List Int,
  (remove_duplicates xs).length ≤ xs.length)
-- PBT for unchanged_prop (no discarded samples: test the Boolean implication).
#eval Plausible.Testable.check (∀ xs : List Int,
  decide (xs.Nodup → remove_duplicates xs = xs) = true)
-- PBT for idempotent_prop.
#eval Plausible.Testable.check (∀ xs : List Int,
  remove_duplicates (remove_duplicates xs) = remove_duplicates xs)

/-- Executable postcondition check. The union of input/output supports suffices:
outside it both counts are zero and output membership is false. -/
def checkPost (xs : List Int) : Bool :=
  let ys := remove_duplicates xs
  (xs ++ ys).all (fun n => decide (n ∈ ys ↔ xs.count n = 1)) &&
  decide (ys.Sublist xs) &&
  (xs ++ ys).all (fun n => decide
    (ys.count n = if xs.count n = 1 then 1 else 0)) &&
  decide ys.Nodup &&
  decide (ys.length ≤ xs.length) &&
  decide (xs.Nodup → ys = xs) &&
  decide (remove_duplicates ys = ys)

-- PBT for Post_prop, checking all conjuncts together.
#eval Plausible.Testable.check (∀ xs : List Int, checkPost xs = true)

/-- All lists of length at most the bound over five signed integer values. -/
def smallInputs : Nat → List (List Int)
  | 0 => [[]]
  | k + 1 => [] :: ([-2, -1, 0, 1, 2] : List Int).flatMap
      (fun n => (smallInputs k).map (n :: ·))

-- Exhaustive PBT for Post_prop: 3,906 inputs, including many repeated values.
-- This also checks every constituent property on every bounded input.
example : (smallInputs 5).all checkPost = true := by native_decide
#eval (smallInputs 5).length

/-- The implementation satisfies the postcondition for every admissible input. -/
theorem correctness_thm (numbers : List Int) :
    Pre numbers → Post_prop numbers (remove_duplicates numbers) := by
  intro _
  exact ⟨membership_thm numbers, order_thm numbers, multiplicity_thm numbers,
    nodup_thm numbers, length_thm numbers, unchanged_thm numbers,
    idempotent_thm numbers⟩

/-- Imperative version. The original input is kept immutable for frequency
queries, while a mutable output is built by traversing the input left to right.
Recomputing a Counter lookup with `count` changes cost, not semantics. -/
def remove_duplicates_imperative (numbers : List Int) : List Int := Id.run do
  let mut result : List Int := []
  for n in numbers do
    if decide (numbers.count n ≤ 1) then
      result := result ++ [n]
  return result

example : remove_duplicates_imperative [] = [] := by native_decide
example : remove_duplicates_imperative [1, 2, 3, 4] = [1, 2, 3, 4] := by native_decide
example : remove_duplicates_imperative [1, 2, 3, 2, 4, 3, 5] = [1, 4, 5] := by native_decide
example : remove_duplicates_imperative [-3, 0, -3, 4, 0, -8] = [4, -8] := by native_decide
#eval remove_duplicates_imperative [1, 2, 3, 2, 4]

example : remove_duplicates_imperative [7, 7, 7] = [] := by native_decide
-- Bounded PBT comparing both implementations on all small inputs.
example : (smallInputs 5).all (fun xs =>
    decide (remove_duplicates xs = remove_duplicates_imperative xs)) = true := by
  native_decide

/-- Loop invariant: an initial accumulator is followed by exactly the accepted
remaining elements, in traversal order. -/
private theorem filter_loop (p : Int → Bool) (rest acc : List Int) :
    (forIn rest acc (fun n result =>
      if p n then pure (ForInStep.yield (result ++ [n]))
      else pure (ForInStep.yield result)) : Id (List Int)) =
    acc ++ rest.filter p := by
  induction rest generalizing acc with
  | nil =>
    simp only [List.forIn_nil, List.filter_nil, List.append_nil]
    rfl
  | cons n rest ih =>
    cases hp : p n <;>
      simp [List.forIn_cons, hp, ih, List.append_assoc]

/-- The functional and mutable implementations agree for every integer list. -/
theorem equivalence_thm (numbers : List Int) :
    remove_duplicates numbers = remove_duplicates_imperative numbers := by
  simpa only [List.nil_append] using
    (filter_loop (fun n => decide (numbers.count n ≤ 1)) numbers []).symm

end humaneval_26_remove_duplicates
end Agent
