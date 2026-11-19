import Mathlib
namespace Agent

/-!
# HumanEval 21: rescale to unit

This file gives an exact rational formalization of the Python routine that
linearly rescales a nonconstant list so that its least element becomes `0`
and its greatest element becomes `1`.
-/

namespace humaneval_21_rescale_to_unit

/-! ## Functional implementation -/

def listMin : List ℚ → ℚ
  | [] => 0
  | [x] => x
  | x :: y :: xs => min x (listMin (y :: xs))

def listMax : List ℚ → ℚ
  | [] => 0
  | [x] => x
  | x :: y :: xs => max x (listMax (y :: xs))

def rescaleToUnit (numbers : List ℚ) : List ℚ :=
  let minNumber := listMin numbers
  let maxNumber := listMax numbers
  numbers.map fun x => (x - minNumber) / (maxNumber - minNumber)

/-! ## Unit tests -/

example : rescaleToUnit [2, 49.9] = [0, 1] := by native_decide
example : rescaleToUnit [100, 49.9] = [1, 0] := by native_decide
example : rescaleToUnit [1, 2, 3, 4, 5] = [0, 0.25, 0.5, 0.75, 1] := by native_decide
example : rescaleToUnit [2, 1, 5, 3, 4] = [0.25, 0, 1, 0.5, 0.75] := by native_decide
example : rescaleToUnit [12, 11, 15, 13, 14] = [0.25, 0, 1, 0.5, 0.75] := by native_decide

#eval rescaleToUnit [1, 2, 3, 4, 5]

/-! ## Specification -/

def Pre (numbers : List ℚ) : Prop :=
  2 ≤ numbers.length ∧ listMin numbers < listMax numbers

def length_preserved_prop (numbers output : List ℚ) : Prop :=
  output.length = numbers.length

def values_in_unit_interval_prop (output : List ℚ) : Prop :=
  ∀ y ∈ output, 0 ≤ y ∧ y ≤ 1

def minimum_becomes_zero_prop (output : List ℚ) : Prop :=
  0 ∈ output

def maximum_becomes_one_prop (output : List ℚ) : Prop :=
  1 ∈ output

private theorem listMin_mem : ∀ {xs : List ℚ}, xs ≠ [] → listMin xs ∈ xs := by
  intro xs hne
  induction xs with
  | nil => exact (hne rfl).elim
  | cons x xs ih =>
      cases xs with
      | nil => simp [listMin]
      | cons y ys =>
          simp only [listMin]
          by_cases hle : x ≤ listMin (y :: ys)
          · rw [min_eq_left hle]
            simp
          · rw [min_eq_right (le_of_not_ge hle)]
            exact List.mem_cons_of_mem x (ih (by simp))

private theorem listMax_mem : ∀ {xs : List ℚ}, xs ≠ [] → listMax xs ∈ xs := by
  intro xs hne
  induction xs with
  | nil => exact (hne rfl).elim
  | cons x xs ih =>
      cases xs with
      | nil => simp [listMax]
      | cons y ys =>
          simp only [listMax]
          by_cases hle : x ≤ listMax (y :: ys)
          · rw [max_eq_right hle]
            exact List.mem_cons_of_mem x (ih (by simp))
          · rw [max_eq_left (le_of_not_ge hle)]
            simp

private theorem listMin_le_of_mem :
    ∀ {xs : List ℚ} {a : ℚ}, xs ≠ [] → a ∈ xs → listMin xs ≤ a := by
  intro xs a hne ha
  induction xs with
  | nil => exact (hne rfl).elim
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp only [List.mem_singleton] at ha
          subst a
          exact le_rfl
      | cons y ys =>
          rw [listMin]
          rcases List.mem_cons.mp ha with rfl | ha
          · exact min_le_left _ _
          · exact (min_le_right _ _).trans (ih (by simp) ha)

private theorem le_listMax_of_mem :
    ∀ {xs : List ℚ} {a : ℚ}, xs ≠ [] → a ∈ xs → a ≤ listMax xs := by
  intro xs a hne ha
  induction xs with
  | nil => exact (hne rfl).elim
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp only [List.mem_singleton] at ha
          subst a
          exact le_rfl
      | cons y ys =>
          rw [listMax]
          rcases List.mem_cons.mp ha with rfl | ha
          · exact le_max_left _ _
          · exact (ih (by simp) ha).trans (le_max_right _ _)

theorem length_preserved_thm (numbers : List ℚ) :
    length_preserved_prop numbers (rescaleToUnit numbers) := by
  simp [length_preserved_prop, rescaleToUnit]

theorem values_in_unit_interval_thm (numbers : List ℚ) (hpre : Pre numbers) :
    values_in_unit_interval_prop (rescaleToUnit numbers) := by
  rcases hpre with ⟨hlen, hgap⟩
  have hne : numbers ≠ [] := by
    intro h
    simp [h] at hlen
  intro y hy
  rw [rescaleToUnit] at hy
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  have hmin : listMin numbers ≤ x := listMin_le_of_mem hne hx
  have hmax : x ≤ listMax numbers := le_listMax_of_mem hne hx
  have hden : 0 < listMax numbers - listMin numbers := sub_pos.mpr hgap
  constructor
  · exact div_nonneg (sub_nonneg.mpr hmin) hden.le
  · apply (div_le_iff₀ hden).2
    linarith

theorem minimum_becomes_zero_thm (numbers : List ℚ) (hpre : Pre numbers) :
    minimum_becomes_zero_prop (rescaleToUnit numbers) := by
  rcases hpre with ⟨hlen, hgap⟩
  have hne : numbers ≠ [] := by
    intro h
    simp [h] at hlen
  rw [minimum_becomes_zero_prop, rescaleToUnit]
  apply List.mem_map.mpr
  exact ⟨listMin numbers, listMin_mem hne, by simp⟩

theorem maximum_becomes_one_thm (numbers : List ℚ) (hpre : Pre numbers) :
    maximum_becomes_one_prop (rescaleToUnit numbers) := by
  rcases hpre with ⟨hlen, hgap⟩
  have hne : numbers ≠ [] := by
    intro h
    simp [h] at hlen
  have hden : listMax numbers - listMin numbers ≠ 0 := ne_of_gt (sub_pos.mpr hgap)
  rw [maximum_becomes_one_prop, rescaleToUnit]
  apply List.mem_map.mpr
  exact ⟨listMax numbers, listMax_mem hne, div_self hden⟩

def Post_prop (numbers output : List ℚ) : Prop :=
  length_preserved_prop numbers output ∧
    values_in_unit_interval_prop output ∧
    minimum_becomes_zero_prop output ∧
    maximum_becomes_one_prop output

theorem rescaleToUnit_correct (numbers : List ℚ) :
    Pre numbers → Post_prop numbers (rescaleToUnit numbers) := by
  intro hpre
  exact ⟨length_preserved_thm numbers,
    values_in_unit_interval_thm numbers hpre,
    minimum_becomes_zero_thm numbers hpre,
    maximum_becomes_one_thm numbers hpre⟩

/-! ## Imperative implementation and equivalence -/

def rescaleToUnitImperative (numbers : List ℚ) : List ℚ := Id.run do
  let minNumber := listMin numbers
  let maxNumber := listMax numbers
  let mut output : List ℚ := []
  for x in numbers do
    output := output ++ [(x - minNumber) / (maxNumber - minNumber)]
  return output

example : rescaleToUnitImperative [2, 49.9] = [0, 1] := by native_decide
example : rescaleToUnitImperative [100, 49.9] = [1, 0] := by native_decide
example : rescaleToUnitImperative [1, 2, 3, 4, 5] = [0, 0.25, 0.5, 0.75, 1] := by
  native_decide
example : rescaleToUnitImperative [2, 1, 5, 3, 4] = [0.25, 0, 1, 0.5, 0.75] := by
  native_decide
example : rescaleToUnitImperative [12, 11, 15, 13, 14] = [0.25, 0, 1, 0.5, 0.75] := by
  native_decide

#eval rescaleToUnitImperative [2, 1, 5, 3, 4]

private theorem flatten_map_singleton_eq_map
    (f : α → β) (xs : List α) :
    (xs.map fun x => [f x]).flatten = xs.map f := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem functional_imperative_equivalent (numbers : List ℚ) :
    rescaleToUnit numbers = rescaleToUnitImperative numbers := by
  simp [rescaleToUnit, rescaleToUnitImperative,
    flatten_map_singleton_eq_map]

end humaneval_21_rescale_to_unit
end Agent
