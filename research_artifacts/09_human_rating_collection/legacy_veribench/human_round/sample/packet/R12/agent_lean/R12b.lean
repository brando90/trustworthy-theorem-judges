import Mathlib

namespace HumanEval4

/-- Arithmetic mean of a list of reals (`0` on the empty list, since `x / 0 = 0`). -/
noncomputable def mean (l : List ℝ) : ℝ := l.sum / (l.length : ℝ)

/-- Mean absolute deviation around the mean:  `average |x - mean|`. -/
noncomputable def meanAbsoluteDeviation (l : List ℝ) : ℝ :=
  (l.map (fun x => |x - mean l|)).sum / (l.length : ℝ)

/-! ### Small helpers for evaluating absolute values of numeric differences -/

theorem abs_sub_eq_of_le {a b : ℝ} (h : a ≤ b) : |a - b| = b - a := by
  rw [abs_of_nonpos (by linarith)]; ring

theorem abs_sub_eq_of_ge {a b : ℝ} (h : b ≤ a) : |a - b| = a - b :=
  abs_of_nonneg (by linarith)

/-! ### Basic properties -/

theorem mad_nonneg (l : List ℝ) : 0 ≤ meanAbsoluteDeviation l := by
  unfold meanAbsoluteDeviation
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  refine List.sum_nonneg ?_
  intro x hx
  rcases List.mem_map.mp hx with ⟨y, _, rfl⟩
  exact abs_nonneg _

theorem mad_nil : meanAbsoluteDeviation [] = 0 := by
  simp [meanAbsoluteDeviation]

theorem mad_singleton (x : ℝ) : meanAbsoluteDeviation [x] = 0 := by
  simp [meanAbsoluteDeviation, mean]

theorem mad_pair (a b : ℝ) : meanAbsoluteDeviation [a, b] = |a - b| / 2 := by
  have habs2 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  have hm : mean [a, b] = (a + b) / 2 := by
    simp only [mean, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    push_cast
    all_goals ring
  have h1 : |a - (a + b) / 2| = |a - b| / 2 := by
    rw [show a - (a + b) / 2 = (a - b) / 2 by ring, abs_div, habs2]
  have h2 : |b - (a + b) / 2| = |a - b| / 2 := by
    rw [show b - (a + b) / 2 = -((a - b) / 2) by ring, abs_neg, abs_div, habs2]
  simp only [meanAbsoluteDeviation, hm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil, h1, h2]
  push_cast
  all_goals ring

/-- A constant list has zero mean absolute deviation. -/
theorem mad_replicate (n : ℕ) (c : ℝ) : meanAbsoluteDeviation (List.replicate n c) = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [meanAbsoluteDeviation]
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hmean : mean (List.replicate n c) = c := by
      unfold mean
      rw [List.sum_replicate, List.length_replicate, nsmul_eq_mul, mul_comm, mul_div_assoc,
        div_self hn', mul_one]
    simp [meanAbsoluteDeviation, hmean, List.map_replicate, List.sum_replicate]

/-! ### The tests from the Python `check` function -/

theorem mad_123 : meanAbsoluteDeviation [1, 2, 3] = 2 / 3 := by
  have hm : mean [1, 2, 3] = 2 := by
    simp only [mean, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    norm_num
  simp only [meanAbsoluteDeviation, hm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  rw [abs_sub_eq_of_le (show (1 : ℝ) ≤ 2 by norm_num),
      abs_sub_eq_of_le (show (2 : ℝ) ≤ 2 by norm_num),
      abs_sub_eq_of_ge (show (2 : ℝ) ≤ 3 by norm_num)]
  norm_num

theorem mad_1234 : meanAbsoluteDeviation [1, 2, 3, 4] = 1 := by
  have hm : mean [1, 2, 3, 4] = 5 / 2 := by
    simp only [mean, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    norm_num
  simp only [meanAbsoluteDeviation, hm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  rw [abs_sub_eq_of_le (show (1 : ℝ) ≤ 5 / 2 by norm_num),
      abs_sub_eq_of_le (show (2 : ℝ) ≤ 5 / 2 by norm_num),
      abs_sub_eq_of_ge (show (5 : ℝ) / 2 ≤ 3 by norm_num),
      abs_sub_eq_of_ge (show (5 : ℝ) / 2 ≤ 4 by norm_num)]
  norm_num

theorem mad_12345 : meanAbsoluteDeviation [1, 2, 3, 4, 5] = 6 / 5 := by
  have hm : mean [1, 2, 3, 4, 5] = 3 := by
    simp only [mean, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    norm_num
  simp only [meanAbsoluteDeviation, hm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  rw [abs_sub_eq_of_le (show (1 : ℝ) ≤ 3 by norm_num),
      abs_sub_eq_of_le (show (2 : ℝ) ≤ 3 by norm_num),
      abs_sub_eq_of_le (show (3 : ℝ) ≤ 3 by norm_num),
      abs_sub_eq_of_ge (show (3 : ℝ) ≤ 4 by norm_num),
      abs_sub_eq_of_ge (show (3 : ℝ) ≤ 5 by norm_num)]
  norm_num

/-! ### Specification -/

/-- The Python code divides by `len(numbers)`, so the input must be non-empty. -/
def Pre (l : List ℝ) : Prop := l ≠ []

def Post (l : List ℝ) : Prop :=
  meanAbsoluteDeviation l
      = (l.map (fun x => |x - l.sum / (l.length : ℝ)|)).sum / (l.length : ℝ)
    ∧ 0 ≤ meanAbsoluteDeviation l

theorem correctness (l : List ℝ) : Pre l → Post l := by
  intro _
  exact ⟨rfl, mad_nonneg l⟩

end HumanEval4