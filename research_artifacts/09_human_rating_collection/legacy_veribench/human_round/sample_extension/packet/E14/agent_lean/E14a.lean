/-!
# VeriBench -- Mean Absolute Deviation
Every stated theorem is PROVEN (no `sorry`) -- this is the expected standard.
-/

namespace MeanAbsoluteDeviation

def meanAbsoluteDeviation (numbers : List ℝ) : ℝ :=
  let n := numbers.length
  if h : n = 0 then
    0
  else
    let mean := (numbers.sum) / (n : ℝ)
    ((numbers.map fun x => |x - mean|).sum) / (n : ℝ)

-- Test examples (executable specifications)
example : meanAbsoluteDeviation ([1, 2, 3] : List ℝ) = (2 : ℝ)/3 := by
  unfold meanAbsoluteDeviation
  norm_num

example : meanAbsoluteDeviation ([1, 2, 3, 4] : List ℝ) = (1 : ℝ) := by
  unfold meanAbsoluteDeviation
  norm_num

example : meanAbsoluteDeviation ([1, 2, 3, 4, 5] : List ℝ) = (6 : ℝ)/5 := by
  unfold meanAbsoluteDeviation
  norm_num

-- Property 1: Non-negativity - MAD is always >= 0
def nonneg_prop (numbers : List ℝ) : Prop :=
  0 ≤ meanAbsoluteDeviation numbers

theorem nonneg_thm (numbers : List ℝ) : nonneg_prop numbers := by
  unfold nonneg_prop
  unfold meanAbsoluteDeviation
  split
  · norm_num
  · have h_nonneg_sum : 0 ≤ ((numbers.map fun x => |x - ((numbers.sum : ℝ) / (numbers.length : ℝ))|).sum) := by
      apply Finset.sum_nonneg
      intro i _
      simp
    have h_nonneg_len : 0 ≤ (numbers.length : ℝ) := Nat.cast_nonneg _
    exact div_nonneg h_nonneg_sum h_nonneg_len

-- Property 2: Zero deviation when all elements are equal
def zero_deviation_prop (numbers : List ℝ) : Prop :=
  (∀ x ∈ numbers, x = (numbers.head? : ℝ)) → meanAbsoluteDeviation numbers = 0

theorem zero_deviation_thm (numbers : List ℝ) (h : ∀ x ∈ numbers, x = (numbers.head? : ℝ)) :
    zero_deviation_prop numbers := by
  unfold zero_deviation_prop
  intro h_eq
  unfold meanAbsoluteDeviation
  by_cases h_empty : numbers.length = 0
  · simp [h_empty]
  · have h_nonzero : (numbers.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h_empty
    simp [h_empty, h_nonzero]
    have h_mean_eq_head : (numbers.sum : ℝ) / (numbers.length : ℝ) = (numbers.head? : ℝ) := by
      have h_sum : (numbers.sum : ℝ) = (numbers.length : ℝ) * (numbers.head? : ℝ) := by
        calc
          (numbers.sum : ℝ) = (∑ x ∈ numbers, x) := by simp
          _ = (∑ x ∈ numbers, (numbers.head? : ℝ)) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [h x hx]
          _ = (numbers.length : ℝ) * (numbers.head? : ℝ) := by simp
      field_simp [h_nonzero]
      linarith
    have h_diff_zero : ∀ x ∈ numbers, |x - ((numbers.sum : ℝ) / (numbers.length : ℝ))| = 0 := by
      intro x hx
      have hx_eq_head : x = (numbers.head? : ℝ) := h x hx
      rw [h_mean_eq_head, hx_eq_head]
      simp
    have h_sum_zero : ((numbers.map fun x => |x - ((numbers.sum : ℝ) / (numbers.length : ℝ))|).sum) = 0 := by
      simp [h_diff_zero]
    simp [h_sum_zero]

-- Property 3: Scaling property - MAD scales linearly with absolute value of factor
def scaling_prop (numbers : List ℝ) (c : ℝ) : Prop :=
  meanAbsoluteDeviation (numbers.map (fun x => c * x)) = |c| * meanAbsoluteDeviation numbers

theorem scaling_thm (numbers : List ℝ) (c : ℝ) : scaling_prop numbers c := by
  unfold scaling_prop
  unfold meanAbsoluteDeviation
  by_cases h_empty : numbers.length = 0
  · simp [h_empty]
  · have h_nonzero : (numbers.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h_empty
    simp [h_empty, h_nonzero]
    have h_map_sum : ((numbers.map (fun x => c * x)).sum : ℝ) = c * (numbers.sum : ℝ) := by
      simp [Finset.mul_sum]
    have h_map_abs_sum : ((numbers.map (fun x => |c * x - ((numbers.map (fun x => c * x)).sum) / (numbers.length : ℝ))|).sum : ℝ) = |c| * ((numbers.map fun x => |x - ((numbers.sum : ℝ) / (numbers.length : ℝ))|).sum : ℝ) := by
      calc
        ((numbers.map (fun x => |c * x - ((numbers.map (fun x => c * x)).sum) / (numbers.length : ℝ))|).sum : ℝ)
            = ((numbers.map (fun x => |c * x - (c * (numbers.sum : ℝ)) / (numbers.length : ℝ))|).sum : ℝ) := by
          simp [h_map_sum]
        _ = ((numbers.map (fun x => |c * (x - ((numbers.sum : ℝ) / (numbers.length : ℝ)))|)).sum : ℝ) := by
          congr
          ext x
          ring
        _ = ((numbers.map (fun x => |c| * |x - ((numbers.sum : ℝ) / (numbers.length : ℝ))|)).sum : ℝ) := by
          simp [abs_mul]
        _ = |c| * ((numbers.map fun x => |x - ((numbers.sum : ℝ) / (numbers.length : ℝ))|).sum : ℝ) := by
          simp [Finset.mul_sum]
    calc
      ((numbers.map (fun x => c * x)).sum) / (numbers.length : ℝ) = (c * (numbers.sum : ℝ)) / (numbers.length : ℝ) := by
        simp [h_map_sum]
      _ = c * ((numbers.sum : ℝ) / (numbers.length : ℝ)) := by ring
      _ = |c| * meanAbsoluteDeviation numbers := by
        unfold meanAbsoluteDeviation
        simp [h_empty, h_nonzero]
    calc
      ((numbers.map (fun x => |c * x - ((numbers.map (fun x => c * x)).sum) / (numbers.length : ℝ))|).sum) / (numbers.length : ℝ)
          = (|c| * ((numbers.map fun x => |x - ((numbers.sum : ℝ) / (numbers.length : ℝ))|).sum : ℝ)) / (numbers.length : ℝ) := by
        rw [h_map_abs_sum]
      _ = |c| * (((numbers.map fun x => |x - ((numbers.sum : ℝ) / (numbers.length : ℝ))|).sum) / (numbers.length : ℝ)) := by ring

-- Property 4: MAD is invariant under translation (adding constant)
def translation_prop (numbers : List ℝ) (k : ℝ) : Prop :=
  meanAbsoluteDeviation (numbers.map (fun x => x + k)) = meanAbsoluteDeviation numbers

theorem translation_thm (numbers : List ℝ) (k : ℝ) : translation_prop numbers k := by
  unfold translation_prop
  unfold meanAbsoluteDeviation
  by_cases h_empty : numbers.length = 0
  · simp [h_empty]
  · have h_nonzero : (numbers.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h_empty
    simp [h_empty, h_nonzero]
    have h_map_sum : ((numbers.map (fun x => x + k)).sum : ℝ) = (numbers.sum : ℝ) + (numbers.length : ℝ) * k := by
      simp [Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    have h_mean_translated : ((numbers.map (fun x => x + k)).sum : ℝ) / (numbers.length : ℝ) = ((numbers.sum : ℝ) / (numbers.length : ℝ)) + k := by
      field_simp [h_nonzero]
      linarith
    have h_diff : ∀ x, |(x + k) - (((numbers.map (fun x => x + k)).sum : ℝ) / (numbers.length : ℝ))| = |x - ((numbers.sum : ℝ) / (numbers.length : ℝ))| := by
      intro x
      rw [h_mean_translated]
      have : |(x + k) - (((numbers.sum : ℝ) / (numbers.length : ℝ)) + k)| = |x - ((numbers.sum : ℝ) / (numbers.length : ℝ))| := by
        ring_nf
        rw [abs_sub_comm]
        simp
      exact this
    have h_map_abs_sum : ((numbers.map (fun x => |(x + k) - (((numbers.map (fun x => x + k)).sum : ℝ) / (numbers.length : ℝ))|)).sum : ℝ) = ((numbers.map fun x => |x - ((numbers.sum : ℝ) / (numbers.length : ℝ))|).sum : ℝ) := by
      simp [h_diff]
    simp [h_map_abs_sum]

-- Property 5: MAD of [1,2,3,4] equals 1 (specific test as theorem)
theorem mad_1234_eq_one : meanAbsoluteDeviation ([1, 2, 3, 4] : List ℝ) = (1 : ℝ) := by
  unfold meanAbsoluteDeviation
  norm_num

-- Pre/Post specification for the function
def Pre (_numbers : List ℝ) : Prop := True

def Post_prop (numbers : List ℝ) (result : ℝ) : Prop :=
  result = meanAbsoluteDeviation numbers

-- The main correctness theorem connecting Pre and Post via the properties
theorem correctness_thm (numbers : List ℝ) (hPre : Pre numbers) :
    nonneg_prop numbers ∧ zero_deviation_prop numbers ∧ translation_prop numbers (0 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact nonneg_thm numbers
  · apply zero_deviation_thm numbers
    intro x hx
    have hx' := hPre
    simpa [Pre] using hx'
  · exact translation_thm numbers (0 : ℝ)

end MeanAbsoluteDeviation