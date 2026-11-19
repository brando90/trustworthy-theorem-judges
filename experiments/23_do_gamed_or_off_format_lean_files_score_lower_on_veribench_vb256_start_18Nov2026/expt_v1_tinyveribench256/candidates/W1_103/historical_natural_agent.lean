import Mathlib
namespace Agent

/-!
# HumanEval 34: sorted unique elements

`unique` formalizes Python's `sorted(list(set(l)))` for integer lists.
Lean `Int` models unbounded Python integers, including negative inputs.
There are no restrictions on the input list.  The specification requires
ascending order, no duplicates, and exactly the original elements; it also
records the length bound, idempotence, and invariance under permutation.  The imperative version builds a
finite set with a mutable accumulator before sorting it.
-/

namespace humaneval_34_unique

/-- Convert to a set, then enumerate its elements in ascending order. -/
def unique (xs : List Int) : List Int :=
  xs.toFinset.sort (· ≤ ·)

-- Fixed examples, including the original Python test.
example : unique [5, 3, 5, 2, 3, 3, 9, 0, 123] = [0, 2, 3, 5, 9, 123] := by
  native_decide
example : unique [] = [] := by native_decide
example : unique [7, 7, 7] = [7] := by native_decide
example : unique [-3, 2, -1, -3, 0, 2] = [-3, -1, 0, 2] := by native_decide
#eval unique [5, 3, 5, 2, 3, 3, 9, 0, 123]
#eval unique [-3, 2, -1, -3, 0, 2]

/-- Every integer list is admissible. -/
def Pre (_xs : List Int) : Prop := True

/-- The output is sorted in nondecreasing order. -/
def sorted_prop (xs : List Int) : Prop :=
  (unique xs).Sorted (· ≤ ·)

theorem sorted_thm (xs : List Int) : sorted_prop xs := by
  exact Finset.sort_sorted (· ≤ ·) xs.toFinset

/-- Every output element occurs only once. -/
def nodup_prop (xs : List Int) : Prop := (unique xs).Nodup

theorem nodup_thm (xs : List Int) : nodup_prop xs := by
  exact Finset.sort_nodup (· ≤ ·) xs.toFinset

/-- No input value is lost, and no new value is introduced. -/
def membership_prop (xs : List Int) : Prop :=
  ∀ x : Int, x ∈ unique xs ↔ x ∈ xs

theorem membership_thm (xs : List Int) : membership_prop xs := by
  intro x
  simp [unique]

/-- Removing duplicates never increases length. -/
def length_prop (xs : List Int) : Prop := (unique xs).length ≤ xs.length

theorem length_thm (xs : List Int) : length_prop xs := by
  unfold length_prop unique
  rw [Finset.length_sort]
  exact List.toFinset_card_le xs

/-- Normalizing an already normalized output has no effect. -/
def idempotent_prop (xs : List Int) : Prop := unique (unique xs) = unique xs

theorem idempotent_thm (xs : List Int) : idempotent_prop xs := by
  simp [idempotent_prop, unique]

/-- Reordering the input cannot change the result. -/
def permutation_prop (xs ys : List Int) : Prop :=
  xs.Perm ys → unique xs = unique ys

theorem permutation_thm (xs ys : List Int) : permutation_prop xs ys := by
  intro h
  unfold unique
  rw [List.toFinset_eq_of_perm xs ys h]

/-- The observable result contract, without assuming equality to the implementation. -/
def Post_prop (xs ys : List Int) : Prop :=
  ys.Sorted (· ≤ ·) ∧ ys.Nodup ∧
  (∀ x : Int, x ∈ ys ↔ x ∈ xs) ∧ ys.length ≤ xs.length ∧ unique ys = ys

/-! ## Bounded property-based tests

The corpus exhausts all lists of lengths zero through four over five signed
integers (781 cases).  Membership equivalence is checked executably by two
finite inclusion checks, rather than quantifying over every integer.
-/

private def smallLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => [] :: ([-2, -1, 0, 1, 2] : List Int).flatMap
      (fun x => (smallLists n).map (fun xs => x :: xs))

private def testInputs : List (List Int) := smallLists 4

/-- Executable version of equality of the input and output supports. -/
private def sameElements (xs ys : List Int) : Bool :=
  xs.all (fun x => decide (x ∈ ys)) && ys.all (fun x => decide (x ∈ xs))

-- PBT for sorted_prop.
example : testInputs.all (fun xs => decide ((unique xs).Sorted (· ≤ ·))) = true := by
  native_decide
-- PBT for nodup_prop.
example : testInputs.all (fun xs => decide ((unique xs).Nodup)) = true := by
  native_decide
-- PBT for membership_prop.
example : testInputs.all (fun xs => sameElements xs (unique xs)) = true := by
  native_decide
-- PBT for length_prop.
example : testInputs.all (fun xs => decide ((unique xs).length ≤ xs.length)) = true := by
  native_decide
-- PBT for idempotent_prop.
example : testInputs.all (fun xs => decide (unique (unique xs) = unique xs)) = true := by
  native_decide
-- PBT for permutation_prop: every pair of lists of length at most three.
example : (smallLists 3).all (fun xs => (smallLists 3).all (fun ys =>
    decide (xs.Perm ys → unique xs = unique ys))) = true := by
  native_decide
-- PBT for the full Post_prop, evaluated on the implementation's output.
example : testInputs.all (fun xs =>
    let ys := unique xs
    decide (ys.Sorted (· ≤ ·)) &&
    decide ys.Nodup && sameElements xs ys && decide (ys.length ≤ xs.length) &&
    decide (unique ys = ys)) = true := by
  native_decide
#eval testInputs.length

/-- Total correctness for every admissible input. -/
theorem correctness_thm (xs : List Int) (_h : Pre xs) : Post_prop xs (unique xs) := by
  exact ⟨sorted_thm xs, nodup_thm xs, membership_thm xs,
    length_thm xs, idempotent_thm xs⟩

/-- Imperative translation: build the set by insertion in a mutable loop. -/
def uniqueImperative (xs : List Int) : List Int := Id.run do
  let mut seen : Finset Int := ∅
  for x in xs do
    seen := insert x seen
  return seen.sort (· ≤ ·)

example : uniqueImperative [5, 3, 5, 2, 3, 3, 9, 0, 123] =
    [0, 2, 3, 5, 9, 123] := by native_decide
example : uniqueImperative [] = [] := by native_decide
example : uniqueImperative [-3, 2, -1, -3, 0, 2] = [-3, -1, 0, 2] := by
  native_decide
#eval uniqueImperative [5, 3, 5, 2, 3, 3, 9, 0, 123]

-- Bounded cross-implementation test (all 781 inputs).
example : testInputs.all (fun xs => decide (unique xs = uniqueImperative xs)) = true := by
  native_decide

/-- Loop invariant: insertions add exactly the elements of the remaining input. -/
private theorem collect_eq (xs : List Int) (s : Finset Int) :
    (Id.run do
      let mut seen := s
      for x in xs do
        seen := insert x seen
      return seen) = s ∪ xs.toFinset := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.forIn_cons, List.toFinset_cons]
    dsimp
    simpa only [Finset.union_insert, Finset.insert_union] using ih (insert x s)

/-- The functional and mutable implementations agree on every integer list. -/
theorem equivalence_thm (xs : List Int) : unique xs = uniqueImperative xs := by
  simpa only [unique, uniqueImperative, Finset.empty_union] using
    congrArg (fun s : Finset Int => s.sort (· ≤ ·)) (collect_eq xs ∅).symm

end humaneval_34_unique
end Agent
