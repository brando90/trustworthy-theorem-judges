import Mathlib

/-!
# HumanEval/4 — Mean Absolute Deviation

Lean 4 formalization of the Python program

```python
def mean_absolute_deviation(numbers: List[float]) -> float:
    mean = sum(numbers) / len(numbers)
    return sum(abs(x - mean) for x in numbers) / len(numbers)
```

For a given list of input numbers, compute the *Mean Absolute Deviation* around the
mean of the dataset:  `MAD = average |x - x_mean|`.

Numbers are modelled by the rationals `ℚ` (an exact, computable and decidable
ordered field) rather than by `Float`, so that the unit tests below are still
executable while the stated properties can actually be proved.

The file contains, in order: the functional implementation, executable unit tests,
the pre-condition, the individual property propositions with their proofs, the
post-condition, the correctness theorem `Pre → Post`, an imperative
(`Id.run do` + mutable state) implementation with its own tests, and finally the
equivalence theorem between the two implementations.
-/

namespace humaneval_4_mean_absolute_deviation

/-! ## Functional implementation -/

/-- `mean numbers = sum(numbers) / len(numbers)`.  Mirrors the Python `mean` local. -/
def mean (numbers : List ℚ) : ℚ :=
  numbers.sum / (numbers.length : ℚ)

/-- `mean_absolute_deviation numbers = sum(|x - mean| for x in numbers) / len(numbers)`. -/
def meanAbsoluteDeviation (numbers : List ℚ) : ℚ :=
  (numbers.map (fun x => |x - mean numbers|)).sum / (numbers.length : ℚ)

/-! ## Unit tests (mirroring the Python `check` function) -/

example : meanAbsoluteDeviation [1, 2, 3] = 2 / 3 := by native_decide
example : meanAbsoluteDeviation [1, 2, 3, 4] = 1 := by native_decide
example : meanAbsoluteDeviation [1, 2, 3, 4, 5] = 6 / 5 := by native_decide

example : |meanAbsoluteDeviation [1, 2, 3] - 2 / 3| < 1 / 1000000 := by native_decide
example : |meanAbsoluteDeviation [1, 2, 3, 4] - 1| < 1 / 1000000 := by native_decide
example : |meanAbsoluteDeviation [1, 2, 3, 4, 5] - 6 / 5| < 1 / 1000000 := by native_decide

#eval meanAbsoluteDeviation [1, 2, 3]
#eval meanAbsoluteDeviation [1, 2, 3, 4]
#eval meanAbsoluteDeviation [1, 2, 3, 4, 5]

/-! ## Pre-condition

Python divides by `len(numbers)`, which raises `ZeroDivisionError` on an empty
list, so the list must be non-empty. -/

def Pre (numbers : List ℚ) : Prop := numbers ≠ []

/-! ## Auxiliary lemmas -/

theorem length_pos_of_pre {l : List ℚ} (h : Pre l) : (0 : ℚ) < (l.length : ℚ) := by
  have : 0 < l.length := List.length_pos_iff.mpr h
  exact_mod_cast this

theorem length_ne_zero_of_pre {l : List ℚ} (h : Pre l) : ((l.length : ℚ)) ≠ 0 :=
  ne_of_gt (length_pos_of_pre h)

theorem sum_map_add (l : List ℚ) (c : ℚ) :
    (l.map (fun x => x + c)).sum = l.sum + (l.length : ℚ) * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast
    ring

theorem sum_map_mul (l : List ℚ) (c : ℚ) :
    (l.map (fun x => c * x)).sum = c * l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih, mul_add]

/-- Translating every sample by `c` translates the mean by `c`. -/
theorem mean_map_add {l : List ℚ} (h : Pre l) (c : ℚ) :
    mean (l.map (fun x => x + c)) = mean l + c := by
  have hn := length_ne_zero_of_pre h
  simp only [mean, List.length_map, sum_map_add]
  field_simp
  ring

/-- Scaling every sample by `c` scales the mean by `c`. -/
theorem mean_map_mul (l : List ℚ) (c : ℚ) :
    mean (l.map (fun x => c * x)) = c * mean l := by
  simp only [mean, List.length_map, sum_map_mul]
  ring

/-! ## Properties -/

/-- The MAD is never negative (it is an average of absolute values). -/
def nonneg_prop (l : List ℚ) : Prop := 0 ≤ meanAbsoluteDeviation l

theorem nonneg_thm (l : List ℚ) : nonneg_prop l := by
  unfold nonneg_prop meanAbsoluteDeviation
  apply div_nonneg
  · apply List.sum_nonneg
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact abs_nonneg _
  · exact Nat.cast_nonneg _

/-- Defining equation: `MAD * n = Σ |xᵢ - mean|`, i.e. the result really is the
average of the absolute deviations from the mean. -/
def spec_prop (l : List ℚ) : Prop :=
  meanAbsoluteDeviation l * (l.length : ℚ) = (l.map (fun x => |x - mean l|)).sum

theorem spec_thm {l : List ℚ} (h : Pre l) : spec_prop l := by
  unfold spec_prop meanAbsoluteDeviation
  exact div_mul_cancel₀ _ (length_ne_zero_of_pre h)

/-- The MAD is invariant under translation of the whole dataset. -/
def translation_prop (l : List ℚ) : Prop :=
  ∀ c : ℚ, meanAbsoluteDeviation (l.map (fun x => x + c)) = meanAbsoluteDeviation l

theorem translation_thm {l : List ℚ} (h : Pre l) : translation_prop l := by
  intro c
  unfold meanAbsoluteDeviation
  rw [mean_map_add h c]
  simp only [List.length_map, List.map_map, Function.comp_def]
  have hmap : (l.map (fun x => |x + c - (mean l + c)|)) = l.map (fun x => |x - mean l|) := by
    apply List.map_congr_left
    intro x _
    congr 1
    ring
  rw [hmap]

/-- The MAD is absolutely homogeneous: scaling the data by `c` scales it by `|c|`. -/
def scale_prop (l : List ℚ) : Prop :=
  ∀ c : ℚ, meanAbsoluteDeviation (l.map (fun x => c * x)) = |c| * meanAbsoluteDeviation l

theorem scale_thm (l : List ℚ) : scale_prop l := by
  intro c
  unfold meanAbsoluteDeviation
  rw [mean_map_mul l c]
  simp only [List.length_map, List.map_map, Function.comp_def]
  have hmap : (l.map (fun x => |c * x - c * mean l|))
      = l.map (fun x => |c| * |x - mean l|) := by
    apply List.map_congr_left
    intro x _
    rw [← mul_sub, abs_mul]
  have hcomp : (l.map (fun x => |c| * |x - mean l|))
      = (l.map (fun x => |x - mean l|)).map (fun y => |c| * y) := by
    simp [List.map_map, Function.comp_def]
  rw [hmap, hcomp, sum_map_mul (l.map (fun x => |x - mean l|)) |c|]
  ring

/-- A constant dataset has zero deviation. -/
def const_prop (l : List ℚ) : Prop :=
  ∀ c : ℚ, l = List.replicate l.length c → meanAbsoluteDeviation l = 0

theorem const_thm {l : List ℚ} (h : Pre l) : const_prop l := by
  intro c hc
  have hn := length_ne_zero_of_pre h
  have hsum : l.sum = (l.length : ℚ) * c := by
    conv_lhs => rw [hc]
    rw [List.sum_replicate, nsmul_eq_mul]
  have hmean : mean l = c := by
    rw [mean, hsum]
    field_simp
  unfold meanAbsoluteDeviation
  rw [hmean]
  have hzero : (l.map (fun x => |x - c|)).sum = 0 := by
    have : (l.map (fun x => |x - c|)) = l.map (fun _ => (0 : ℚ)) := by
      apply List.map_congr_left
      intro x hx
      have : x = c := by
        rw [hc] at hx
        exact List.eq_of_mem_replicate hx
      simp [this]
    rw [this]
    simp
  rw [hzero, zero_div]

/-- The MAD of a singleton list is `0`. -/
def singleton_prop (a : ℚ) : Prop := meanAbsoluteDeviation [a] = 0

theorem singleton_thm (a : ℚ) : singleton_prop a := by
  simp [singleton_prop, meanAbsoluteDeviation, mean]

/-! ## Post-condition -/

def Post_prop (l : List ℚ) : Prop :=
  nonneg_prop l ∧ spec_prop l ∧ translation_prop l ∧ scale_prop l ∧ const_prop l

/-! ## Correctness theorem -/

theorem correctness (l : List ℚ) (h : Pre l) : Post_prop l :=
  ⟨nonneg_thm l, spec_thm h, translation_thm h, scale_thm l, const_thm h⟩

/-! ## Imperative implementation -/

/-- Imperative version: one accumulator loop for the sum, a second one for the
sum of the absolute deviations. -/
def meanAbsoluteDeviationImp (numbers : List ℚ) : ℚ := Id.run do
  let n : ℚ := (numbers.length : ℚ)
  let mut total : ℚ := 0
  for x in numbers do
    total := total + x
  let m : ℚ := total / n
  let mut acc : ℚ := 0
  for x in numbers do
    acc := acc + |x - m|
  return acc / n

/-! ## Imperative unit tests -/

example : meanAbsoluteDeviationImp [1, 2, 3] = 2 / 3 := by native_decide
example : meanAbsoluteDeviationImp [1, 2, 3, 4] = 1 := by native_decide
example : meanAbsoluteDeviationImp [1, 2, 3, 4, 5] = 6 / 5 := by native_decide

#eval meanAbsoluteDeviationImp [1, 2, 3]
#eval meanAbsoluteDeviationImp [1, 2, 3, 4]
#eval meanAbsoluteDeviationImp [1, 2, 3, 4, 5]

/-! ## Equivalence of the functional and the imperative implementation -/

/-- An accumulator loop that adds `f x` for every element computes `init + Σ f x`. -/
theorem foldl_add (l : List ℚ) (f : ℚ → ℚ) (init : ℚ) :
    l.foldl (fun s x => s + f x) init = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih => simp [ih]; ring

theorem equivalence (l : List ℚ) : meanAbsoluteDeviation l = meanAbsoluteDeviationImp l := by
  simp only [meanAbsoluteDeviationImp, Id.run, Id.pure_eq, Id.bind_eq,
    List.forIn_yield_eq_foldl]
  rw [foldl_add l (fun x => x) 0]
  simp only [List.map_id_fun', id_eq, zero_add]
  rw [foldl_add l (fun x => |x - l.sum / (l.length : ℚ)|) 0, zero_add]
  rfl

end humaneval_4_mean_absolute_deviation
