import Mathlib

/-!
# HumanEval/4: Mean Absolute Deviation

Formalization of the Python program `humaneval_4_mean_absolute_deviation.py`:
for a given list of input numbers, calculate the Mean Absolute Deviation (MAD)
around the arithmetic mean of the dataset:
`MAD = average |x - x_mean|`.
-/

namespace humaneval_4_mean_absolute_deviation

/-! ## 1. Implementation (Functional Definition) -/

/-- Executable floating-point arithmetic mean of a list of `Float`s. -/
def mean_float (numbers : List Float) : Float :=
  (numbers.foldl (· + ·) 0.0) / numbers.length.toFloat

/-- Executable floating-point Mean Absolute Deviation around the mean. -/
def mean_absolute_deviation_float (numbers : List Float) : Float :=
  ((numbers.map (fun x => Float.abs (x - mean_float numbers))).foldl (· + ·) 0.0) /
    numbers.length.toFloat

/-- Executable exact rational arithmetic mean of a list of `ℚ`s. -/
def mean_rat (numbers : List ℚ) : ℚ :=
  numbers.sum / (numbers.length : ℚ)

/-- Executable exact rational Mean Absolute Deviation around the mean. -/
def mean_absolute_deviation_rat (numbers : List ℚ) : ℚ :=
  (numbers.map (fun x => |x - mean_rat numbers|)).sum / (numbers.length : ℚ)

/-- Arithmetic mean of a list of real numbers. -/
noncomputable def mean (numbers : List ℝ) : ℝ :=
  numbers.sum / (numbers.length : ℝ)

/-- Mean Absolute Deviation around the mean for a list of real numbers. -/
noncomputable def mean_absolute_deviation (numbers : List ℝ) : ℝ :=
  (numbers.map (fun x => |x - mean numbers|)).sum / (numbers.length : ℝ)

/-! ### Cross-Layer Correspondence (`ℚ` to `ℝ`) -/

theorem sum_map_ratCast (xs : List ℚ) :
    (xs.map (fun q : ℚ => (q : ℝ))).sum = (xs.sum : ℝ) := by
  induction xs with
  | nil => simp only [List.map_nil, List.sum_nil, Rat.cast_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add]
    rw [ih]

theorem mean_map_ratCast (numbers : List ℚ) :
    mean (numbers.map (fun q : ℚ => (q : ℝ))) = (mean_rat numbers : ℝ) := by
  unfold mean mean_rat
  rw [sum_map_ratCast, List.length_map, Rat.cast_div, Rat.cast_natCast]

/-- Exact correspondence theorem connecting the executable `ℚ` implementation to `ℝ`. -/
theorem mean_absolute_deviation_map_ratCast (numbers : List ℚ) :
    mean_absolute_deviation (numbers.map (fun q : ℚ => (q : ℝ))) =
      (mean_absolute_deviation_rat numbers : ℝ) := by
  unfold mean_absolute_deviation mean_absolute_deviation_rat
  rw [mean_map_ratCast]
  have hmap :
      (numbers.map (fun q : ℚ => (q : ℝ))).map (fun x : ℝ => |x - (mean_rat numbers : ℝ)|) =
        (numbers.map (fun x : ℚ => |x - mean_rat numbers|)).map (fun q : ℚ => (q : ℝ)) := by
    rw [List.map_map, List.map_map]
    congr 1
    ext q
    simp [Rat.cast_abs, Rat.cast_sub]
  rw [hmap, sum_map_ratCast, List.length_map, Rat.cast_div, Rat.cast_natCast]

/-! ## 2. Unit Tests -/

example : Float.abs (mean_absolute_deviation_float [1.0, 2.0, 3.0] - 2.0 / 3.0) < 1e-6 := by
  native_decide

example : Float.abs (mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6 := by
  native_decide

example : Float.abs (mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0) < 1e-6 := by
  native_decide

example : mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0] == 1.0 := by
  native_decide

example : mean_absolute_deviation_float [5.0] == 0.0 := by
  native_decide

example : Float.abs (mean_absolute_deviation_float [-2.0, 0.0, 2.0] - 4.0 / 3.0) < 1e-6 := by
  native_decide

#eval mean_absolute_deviation_float [1.0, 2.0, 3.0]
#eval mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0]
#eval mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0, 5.0]

example : mean_absolute_deviation_rat [1, 2, 3] = 2 / 3 := by native_decide
example : mean_absolute_deviation_rat [1, 2, 3, 4] = 1 := by native_decide
example : mean_absolute_deviation_rat [1, 2, 3, 4, 5] = 6 / 5 := by native_decide
example : mean_absolute_deviation_rat [7] = 0 := by native_decide
example : mean_absolute_deviation_rat [-2, 0, 2] = 4 / 3 := by native_decide

#eval mean_absolute_deviation_rat [1, 2, 3]
#eval mean_absolute_deviation_rat [1, 2, 3, 4]
#eval mean_absolute_deviation_rat [1, 2, 3, 4, 5]

theorem test_real_123 : mean_absolute_deviation ([1, 2, 3] : List ℝ) = 2 / 3 := by
  unfold mean_absolute_deviation mean
  norm_num

theorem test_real_1234 : mean_absolute_deviation ([1, 2, 3, 4] : List ℝ) = 1 := by
  unfold mean_absolute_deviation mean
  norm_num [abs_of_pos]

theorem test_real_12345 : mean_absolute_deviation ([1, 2, 3, 4, 5] : List ℝ) = 6 / 5 := by
  unfold mean_absolute_deviation mean
  norm_num

/-! ## 3. Pre-condition -/

/-- Pre-condition: the input list of numbers is non-empty (avoiding division by zero). -/
def Pre (numbers : List ℝ) : Prop :=
  numbers ≠ []

def Pre_rat (numbers : List ℚ) : Prop :=
  numbers ≠ []

def Pre_float (numbers : List Float) : Prop :=
  numbers ≠ []

/-! ## 4. Properties and Theorems -/

theorem length_cast_ne_zero {α : Type*} {xs : List α} (h : xs ≠ []) : (xs.length : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (List.length_eq_zero_iff.not.mpr h)

theorem length_cast_pos {α : Type*} {xs : List α} (h : xs ≠ []) : (0 : ℝ) < (xs.length : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero (List.length_eq_zero_iff.not.mpr h))

theorem list_sum_eq_zero_iff_of_nonneg (xs : List ℝ) (h : ∀ y ∈ xs, 0 ≤ y) :
    xs.sum = 0 ↔ ∀ y ∈ xs, y = 0 := by
  induction xs with
  | nil => simp
  | cons a l ih =>
    have ha : 0 ≤ a := h a (List.mem_cons_self ..)
    have hl_mem : ∀ y ∈ l, 0 ≤ y := fun y hy => h y (List.mem_cons_of_mem a hy)
    have hl_sum : 0 ≤ l.sum := List.sum_nonneg hl_mem
    simp only [List.sum_cons, List.mem_cons, forall_eq_or_imp, ← ih hl_mem]
    constructor
    · intro hsum
      constructor <;> linarith
    · rintro ⟨ha0, hl0⟩
      linarith

theorem sum_map_add_const (numbers : List ℝ) (c : ℝ) :
    (numbers.map (fun x => x + c)).sum = numbers.sum + (numbers.length : ℝ) * c := by
  induction numbers with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem sum_map_mul_const (numbers : List ℝ) (c : ℝ) :
    (numbers.map (fun x => c * x)).sum = c * numbers.sum := by
  induction numbers with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem sum_map_const_eq (numbers : List ℝ) (c : ℝ) (h : ∀ x ∈ numbers, x = c) :
    numbers.sum = (numbers.length : ℝ) * c := by
  induction numbers with
  | nil => simp
  | cons a l ih =>
    have ha : a = c := h a (List.mem_cons_self ..)
    have hl : ∀ x ∈ l, x = c := fun x hx => h x (List.mem_cons_of_mem a hx)
    simp only [List.sum_cons, List.length_cons, ha, ih hl, Nat.cast_add, Nat.cast_one]
    ring

theorem sum_le_length_mul_of_le (numbers : List ℝ) (M : ℝ) (h : ∀ x ∈ numbers, x ≤ M) :
    numbers.sum ≤ (numbers.length : ℝ) * M := by
  induction numbers with
  | nil => simp
  | cons a l ih =>
    have ha : a ≤ M := h a (List.mem_cons_self ..)
    have hl : ∀ x ∈ l, x ≤ M := fun x hx => h x (List.mem_cons_of_mem a hx)
    have ihl := ih hl
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem length_mul_le_sum_of_le (numbers : List ℝ) (m : ℝ) (h : ∀ x ∈ numbers, m ≤ x) :
    (numbers.length : ℝ) * m ≤ numbers.sum := by
  induction numbers with
  | nil => simp
  | cons a l ih =>
    have ha : m ≤ a := h a (List.mem_cons_self ..)
    have hl : ∀ x ∈ l, m ≤ x := fun x hx => h x (List.mem_cons_of_mem a hx)
    have ihl := ih hl
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem sum_map_le_sum_map (xs : List ℝ) (f g : ℝ → ℝ) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a l ih =>
    have ha : f a ≤ g a := h a (List.mem_cons_self ..)
    have hl : ∀ x ∈ l, f x ≤ g x := fun x hx => h x (List.mem_cons_of_mem a hx)
    have ihl := ih hl
    simp only [List.map_cons, List.sum_cons]
    linarith

/-- Property 1: Exact mathematical specification of Mean Absolute Deviation. -/
def spec_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation numbers =
    (numbers.map (fun x => |x - (numbers.sum / (numbers.length : ℝ))|)).sum / (numbers.length : ℝ)

theorem spec_thm (numbers : List ℝ) : spec_prop numbers := by
  rfl

/-- Property 2: Multiplying MAD by length recovers the total absolute deviation when `Pre` holds. -/
def mul_length_prop (numbers : List ℝ) : Prop :=
  Pre numbers →
    mean_absolute_deviation numbers * (numbers.length : ℝ) =
      (numbers.map (fun x => |x - mean numbers|)).sum

theorem mul_length_thm (numbers : List ℝ) : mul_length_prop numbers := by
  intro hpre
  unfold mean_absolute_deviation
  exact div_mul_cancel₀ _ (length_cast_ne_zero hpre)

/-- Property 3: Non-negativity of Mean Absolute Deviation. -/
def nonneg_prop (numbers : List ℝ) : Prop :=
  0 ≤ mean_absolute_deviation numbers

theorem nonneg_thm (numbers : List ℝ) : nonneg_prop numbers := by
  unfold nonneg_prop mean_absolute_deviation
  apply div_nonneg
  · apply List.sum_nonneg
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, _, rfl⟩
    exact abs_nonneg (x - mean numbers)
  · exact Nat.cast_nonneg numbers.length

/-- Property 4: MAD is zero if and only if every element equals the mean. -/
def eq_zero_iff_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation numbers = 0 ↔ ∀ x ∈ numbers, x = mean numbers

theorem eq_zero_iff_thm (numbers : List ℝ) : eq_zero_iff_prop numbers := by
  unfold eq_zero_iff_prop
  by_cases hnil : numbers = []
  · subst hnil
    simp [mean_absolute_deviation]
  · unfold mean_absolute_deviation
    have hlen : (numbers.length : ℝ) ≠ 0 := length_cast_ne_zero hnil
    rw [div_eq_zero_iff, or_iff_left hlen]
    have hnonneg : ∀ y ∈ numbers.map (fun x => |x - mean numbers|), (0 : ℝ) ≤ y := by
      intro y hy
      rcases List.mem_map.mp hy with ⟨x, _, rfl⟩
      exact abs_nonneg _
    rw [list_sum_eq_zero_iff_of_nonneg _ hnonneg]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      abs_eq_zero, sub_eq_zero]

/-- Property 5: A list with all identical elements has Mean Absolute Deviation equal to 0. -/
def const_zero_prop (numbers : List ℝ) (c : ℝ) : Prop :=
  (∀ x ∈ numbers, x = c) → mean_absolute_deviation numbers = 0

theorem const_zero_thm (numbers : List ℝ) (c : ℝ) : const_zero_prop numbers c := by
  intro hconst
  apply (eq_zero_iff_thm numbers).mpr
  intro x hx
  have hnil : numbers ≠ [] := List.ne_nil_of_mem hx
  have hlen : (numbers.length : ℝ) ≠ 0 := length_cast_ne_zero hnil
  have hsum : numbers.sum = (numbers.length : ℝ) * c := sum_map_const_eq numbers c hconst
  unfold mean
  rw [hsum, mul_div_cancel_left₀ c hlen, hconst x hx]

/-- Property 6: Replicated constant list has Mean Absolute Deviation equal to 0. -/
def replicate_zero_prop (n : ℕ) (c : ℝ) : Prop :=
  mean_absolute_deviation (List.replicate n c) = 0

theorem replicate_zero_thm (n : ℕ) (c : ℝ) : replicate_zero_prop n c :=
  const_zero_thm (List.replicate n c) c (fun _ hx => List.eq_of_mem_replicate hx)

/-- Property 7: Singleton list has Mean Absolute Deviation equal to 0. -/
def singleton_zero_prop (c : ℝ) : Prop :=
  mean_absolute_deviation [c] = 0

theorem singleton_zero_thm (c : ℝ) : singleton_zero_prop c :=
  replicate_zero_thm 1 c

/-- Property 8: Translation (shift) invariance of Mean Absolute Deviation. -/
def shift_invariant_prop (numbers : List ℝ) (c : ℝ) : Prop :=
  mean_absolute_deviation (numbers.map (fun x => x + c)) = mean_absolute_deviation numbers

theorem shift_invariant_thm (numbers : List ℝ) (c : ℝ) : shift_invariant_prop numbers c := by
  unfold shift_invariant_prop
  by_cases hnil : numbers = []
  · subst hnil
    simp [mean_absolute_deviation]
  · unfold mean_absolute_deviation mean
    simp only [List.length_map]
    have hlen : (numbers.length : ℝ) ≠ 0 := length_cast_ne_zero hnil
    have hmean : (numbers.map (fun x => x + c)).sum / (numbers.length : ℝ) =
        numbers.sum / (numbers.length : ℝ) + c := by
      rw [sum_map_add_const, add_div, mul_div_cancel_left₀ c hlen]
    rw [hmean, List.map_map]
    congr 2
    ext x
    simp [Function.comp, add_sub_add_right_eq_sub]

/-- Property 9: Scale homogeneity of Mean Absolute Deviation. -/
def scale_homogeneous_prop (numbers : List ℝ) (c : ℝ) : Prop :=
  mean_absolute_deviation (numbers.map (fun x => c * x)) = |c| * mean_absolute_deviation numbers

theorem scale_homogeneous_thm (numbers : List ℝ) (c : ℝ) : scale_homogeneous_prop numbers c := by
  unfold scale_homogeneous_prop mean_absolute_deviation mean
  simp only [List.length_map, sum_map_mul_const]
  have hmean : c * numbers.sum / (numbers.length : ℝ) = c * (numbers.sum / (numbers.length : ℝ)) := by
    exact mul_div_assoc c numbers.sum (numbers.length : ℝ)
  rw [hmean]
  have hmap :
      (numbers.map (fun x => c * x)).map (fun x => |x - c * (numbers.sum / (numbers.length : ℝ))|) =
        (numbers.map (fun x => |x - numbers.sum / (numbers.length : ℝ)|)).map (fun d => |c| * d) := by
    rw [List.map_map, List.map_map]
    congr 1
    ext x
    simp only [Function.comp_apply, ← mul_sub, abs_mul]
  rw [hmap, sum_map_mul_const, mul_div_assoc]

/-- Property 10: Negation (reflection) invariance of Mean Absolute Deviation. -/
def neg_invariant_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation (numbers.map (fun x => -x)) = mean_absolute_deviation numbers

theorem neg_invariant_thm (numbers : List ℝ) : neg_invariant_prop numbers := by
  unfold neg_invariant_prop
  have hmap : numbers.map (fun x : ℝ => -x) = numbers.map (fun x : ℝ => (-1 : ℝ) * x) := by
    congr 1
    ext x
    ring
  rw [hmap, scale_homogeneous_thm numbers (-1), abs_neg, abs_one, one_mul]

/-- Property 11: Permutation invariance of Mean Absolute Deviation. -/
def perm_invariant_prop (numbers₁ numbers₂ : List ℝ) : Prop :=
  numbers₁.Perm numbers₂ → mean_absolute_deviation numbers₁ = mean_absolute_deviation numbers₂

theorem perm_invariant_thm (numbers₁ numbers₂ : List ℝ) :
    perm_invariant_prop numbers₁ numbers₂ := by
  intro hperm
  unfold mean_absolute_deviation mean
  have hsum : numbers₁.sum = numbers₂.sum := hperm.sum_eq
  have hlen : numbers₁.length = numbers₂.length := hperm.length_eq
  rw [hsum, hlen]
  have hmap_perm :
      (numbers₁.map (fun x => |x - numbers₂.sum / (numbers₂.length : ℝ)|)).Perm
        (numbers₂.map (fun x => |x - numbers₂.sum / (numbers₂.length : ℝ)|)) :=
    hperm.map _
  rw [hmap_perm.sum_eq]

/-- Property 12: Reversal invariance of Mean Absolute Deviation. -/
def reverse_invariant_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation numbers.reverse = mean_absolute_deviation numbers

theorem reverse_invariant_thm (numbers : List ℝ) : reverse_invariant_prop numbers :=
  perm_invariant_thm numbers.reverse numbers (List.reverse_perm numbers)

/-- Property 13: Two-element list MAD formula: `MAD([a, b]) = |a - b| / 2`. -/
def two_elem_prop (a b : ℝ) : Prop :=
  mean_absolute_deviation [a, b] = |a - b| / 2

theorem two_elem_thm (a b : ℝ) : two_elem_prop a b := by
  unfold two_elem_prop mean_absolute_deviation mean
  simp only [List.sum_cons, List.sum_nil, add_zero, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.cast_ofNat, List.map_cons, List.map_nil]
  have h1 : a - (a + b) / 2 = (a - b) / 2 := by ring
  have h2 : b - (a + b) / 2 = -(a - b) / 2 := by ring
  rw [h1, h2, neg_div, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring

/-- Property 14: Each element's absolute deviation is bounded by `length * MAD`. -/
def element_deviation_bound_prop (numbers : List ℝ) : Prop :=
  ∀ x ∈ numbers, |x - mean numbers| ≤ (numbers.length : ℝ) * mean_absolute_deviation numbers

theorem element_deviation_bound_thm (numbers : List ℝ) :
    element_deviation_bound_prop numbers := by
  intro x hx
  have hnil : numbers ≠ [] := List.ne_nil_of_mem hx
  have hlen : (numbers.length : ℝ) ≠ 0 := length_cast_ne_zero hnil
  unfold mean_absolute_deviation
  rw [mul_div_cancel₀ _ hlen]
  apply List.single_le_sum
  · intro y hy
    rcases List.mem_map.mp hy with ⟨z, _, rfl⟩
    exact abs_nonneg _
  · exact List.mem_map_of_mem hx

/-- Property 15: Upper bound by interval width `hi - lo` when all elements lie in `[lo, hi]`. -/
def range_bound_prop (numbers : List ℝ) (lo hi : ℝ) : Prop :=
  Pre numbers → (∀ x ∈ numbers, lo ≤ x ∧ x ≤ hi) → mean_absolute_deviation numbers ≤ hi - lo

theorem range_bound_thm (numbers : List ℝ) (lo hi : ℝ) : range_bound_prop numbers lo hi := by
  intro hpre hbounds
  have hlen_pos : (0 : ℝ) < (numbers.length : ℝ) := length_cast_pos hpre
  have hmean_lo : lo ≤ mean numbers := by
    unfold mean
    rw [le_div_iff₀ hlen_pos, mul_comm]
    exact length_mul_le_sum_of_le numbers lo (fun x hx => (hbounds x hx).1)
  have hmean_hi : mean numbers ≤ hi := by
    unfold mean
    rw [div_le_iff₀ hlen_pos, mul_comm]
    exact sum_le_length_mul_of_le numbers hi (fun x hx => (hbounds x hx).2)
  unfold mean_absolute_deviation
  rw [div_le_iff₀ hlen_pos, mul_comm]
  have hdev : ∀ y ∈ numbers.map (fun x => |x - mean numbers|), y ≤ hi - lo := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hx_lo := (hbounds x hx).1
    have hx_hi := (hbounds x hx).2
    rw [abs_le]
    constructor <;> linarith
  have hsum := sum_le_length_mul_of_le (numbers.map (fun x => |x - mean numbers|)) (hi - lo) hdev
  simpa [List.length_map] using hsum

/-- Property 16: Triangle inequality bound around an arbitrary center `c`. -/
def center_triangle_bound_prop (numbers : List ℝ) (c : ℝ) : Prop :=
  Pre numbers →
    mean_absolute_deviation numbers ≤
      (numbers.map (fun x => |x - c|)).sum / (numbers.length : ℝ) + |c - mean numbers|

theorem center_triangle_bound_thm (numbers : List ℝ) (c : ℝ) :
    center_triangle_bound_prop numbers c := by
  intro hpre
  have hlen_pos : (0 : ℝ) < (numbers.length : ℝ) := length_cast_pos hpre
  have hlen_ne : (numbers.length : ℝ) ≠ 0 := length_cast_ne_zero hpre
  unfold mean_absolute_deviation
  have hstep : (numbers.map (fun x => |x - mean numbers|)).sum ≤
      (numbers.map (fun x => |x - c| + |c - mean numbers|)).sum := by
    apply sum_map_le_sum_map
    intro x _
    simpa [sub_add_sub_cancel] using abs_add_le (x - c) (c - mean numbers)
  have hsplit : (numbers.map (fun x => |x - c| + |c - mean numbers|)).sum =
      (numbers.map (fun x => |x - c|)).sum + (numbers.length : ℝ) * |c - mean numbers| := by
    have hmap : numbers.map (fun x => |x - c| + |c - mean numbers|) =
        (numbers.map (fun x => |x - c|)).map (fun y => y + |c - mean numbers|) := by
      rw [List.map_map]; rfl
    rw [hmap, sum_map_add_const, List.length_map]
  rw [hsplit] at hstep
  have hdiv := div_le_div_of_nonneg_right hstep (le_of_lt hlen_pos)
  rwa [add_div, mul_div_cancel_left₀ _ hlen_ne] at hdiv

/-! ## 5. Post-condition -/

/-- Post-condition conjunction of all specification and mathematical properties of MAD. -/
def Post_prop (numbers : List ℝ) : Prop :=
  spec_prop numbers ∧
  mul_length_prop numbers ∧
  nonneg_prop numbers ∧
  eq_zero_iff_prop numbers ∧
  (∀ c : ℝ, const_zero_prop numbers c) ∧
  (∀ c : ℝ, shift_invariant_prop numbers c) ∧
  (∀ c : ℝ, scale_homogeneous_prop numbers c) ∧
  neg_invariant_prop numbers ∧
  (∀ numbers₂ : List ℝ, perm_invariant_prop numbers numbers₂) ∧
  reverse_invariant_prop numbers ∧
  element_deviation_bound_prop numbers ∧
  (∀ lo hi : ℝ, range_bound_prop numbers lo hi) ∧
  (∀ c : ℝ, center_triangle_bound_prop numbers c)

/-! ## 6. Property-Based Tests (PBTs) -/

def intsToRats (xs : List Int) : List ℚ := xs.map Int.cast
def intsToFloats (xs : List Int) : List Float := xs.map Float.ofInt

-- PBT for `spec_prop` (tested via executable `Rat` counterpart; `Real` equality is not computable)
#eval Plausible.Testable.check (∀ xs : List Int,
  decide (let qs := intsToRats xs
    mean_absolute_deviation_rat qs =
      (qs.map (fun x => |x - (qs.sum / (qs.length : ℚ))|)).sum / (qs.length : ℚ)) = true)

-- PBT for `mul_length_prop` (tested via executable `Rat` counterpart)
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int,
  decide (let qs := intsToRats (x :: xs)
    mean_absolute_deviation_rat qs * (qs.length : ℚ) =
      (qs.map (fun y => |y - mean_rat qs|)).sum) = true)

-- PBT for `nonneg_prop` (tested via executable `Rat` and `Float` counterparts)
#eval Plausible.Testable.check (∀ xs : List Int,
  0 ≤ mean_absolute_deviation_rat (intsToRats xs))
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int,
  (0.0 <= mean_absolute_deviation_float (intsToFloats (x :: xs))) = true)

-- PBT for `eq_zero_iff_prop` (tested via executable `Rat` counterpart)
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int,
  (let qs := intsToRats (x :: xs)
   (mean_absolute_deviation_rat qs == 0) == qs.all (fun y => y == mean_rat qs)) = true)

-- PBT for `const_zero_prop` and `replicate_zero_prop` (tested via executable `Rat` counterpart)
#eval Plausible.Testable.check (∀ n : Nat, ∀ c : Int,
  mean_absolute_deviation_rat (List.replicate (n % 20) (c : ℚ)) = 0)

-- PBT for `singleton_zero_prop` (tested via executable `Rat` and `Float` counterparts)
#eval Plausible.Testable.check (∀ c : Int,
  mean_absolute_deviation_rat [(c : ℚ)] = 0)
example : (List.range 25).all (fun n =>
  mean_absolute_deviation_float [Float.ofNat n] == 0.0) = true := by native_decide

-- PBT for `shift_invariant_prop` (tested via executable `Rat` counterpart)
#eval Plausible.Testable.check (∀ xs : List Int, ∀ c : Int,
  decide (let qs := intsToRats xs
    mean_absolute_deviation_rat (qs.map (fun x => x + (c : ℚ))) =
      mean_absolute_deviation_rat qs) = true)

-- PBT for `scale_homogeneous_prop` (tested via executable `Rat` counterpart)
#eval Plausible.Testable.check (∀ xs : List Int, ∀ c : Int,
  decide (let qs := intsToRats xs
    mean_absolute_deviation_rat (qs.map (fun x => (c : ℚ) * x)) =
      |(c : ℚ)| * mean_absolute_deviation_rat qs) = true)

-- PBT for `neg_invariant_prop` (tested via executable `Rat` counterpart)
#eval Plausible.Testable.check (∀ xs : List Int,
  decide (let qs := intsToRats xs
    mean_absolute_deviation_rat (qs.map (fun x => -x)) =
      mean_absolute_deviation_rat qs) = true)

-- PBT for `perm_invariant_prop` and `reverse_invariant_prop` (tested via executable `Rat` counterpart)
#eval Plausible.Testable.check (∀ xs : List Int,
  decide (let qs := intsToRats xs
    mean_absolute_deviation_rat qs.reverse = mean_absolute_deviation_rat qs) = true)

-- PBT for `two_elem_prop` (tested via executable `Rat` counterpart)
#eval Plausible.Testable.check (∀ a b : Int,
  mean_absolute_deviation_rat [(a : ℚ), (b : ℚ)] = |(a : ℚ) - (b : ℚ)| / 2)

-- PBT for `element_deviation_bound_prop` (tested via executable `Rat` counterpart)
#eval Plausible.Testable.check (∀ xs : List Int,
  (let qs := intsToRats xs
   qs.all (fun x => decide (|x - mean_rat qs| ≤ (qs.length : ℚ) * mean_absolute_deviation_rat qs))) = true)

-- PBT for `range_bound_prop` (tested via executable `Rat` counterpart)
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int,
  decide (let qs := intsToRats (x :: xs)
    let lo := qs.foldl min (x : ℚ)
    let hi := qs.foldl max (x : ℚ)
    mean_absolute_deviation_rat qs ≤ hi - lo) = true)

-- PBT for `center_triangle_bound_prop` (tested via executable `Rat` counterpart)
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int, ∀ c : Int,
  decide (let qs := intsToRats (x :: xs)
    mean_absolute_deviation_rat qs ≤
      (qs.map (fun y => |y - (c : ℚ)|)).sum / (qs.length : ℚ) + |(c : ℚ) - mean_rat qs|) = true)

def post_rat_check (qs : List ℚ) (c : ℚ) : Bool :=
  let mad := mean_absolute_deviation_rat qs
  let m := mean_rat qs
  let n : ℚ := qs.length
  decide (mad = (qs.map (fun x => |x - (qs.sum / n)|)).sum / n) &&
  decide (mad * n = (qs.map (fun x => |x - m|)).sum) &&
  decide (0 ≤ mad) &&
  (decide (mad = 0) == qs.all (fun x => decide (x = m))) &&
  decide (mean_absolute_deviation_rat (qs.map (fun x => x + c)) = mad) &&
  decide (mean_absolute_deviation_rat (qs.map (fun x => c * x)) = |c| * mad) &&
  decide (mean_absolute_deviation_rat (qs.map (fun x => -x)) = mad) &&
  decide (mean_absolute_deviation_rat qs.reverse = mad) &&
  qs.all (fun x => decide (|x - m| ≤ n * mad)) &&
  decide (mad ≤ (qs.map (fun x => |x - c|)).sum / n + |c - m|)

-- PBT for `Post_prop` (randomized and bounded executable checks)
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int, ∀ c : Int,
  post_rat_check (intsToRats (x :: xs)) (c : ℚ) = true)

example :
    ([([1, 2, 3] : List ℚ), [1, 2, 3, 4], [1, 2, 3, 4, 5], [5, 5, 5], [-10, 0, 10, 20], [42]].all
      (fun qs => ([-3, 0, 2, 7] : List ℚ).all (fun c => post_rat_check qs c))) = true := by
  native_decide

/-! ## 7. Correctness Theorem (`Pre → Post`) -/

/-- Main correctness theorem: for any input satisfying `Pre`, `Post_prop` holds. -/
theorem correctness_thm (numbers : List ℝ) : Pre numbers → Post_prop numbers := by
  intro _hpre
  refine ⟨spec_thm numbers,
    mul_length_thm numbers,
    nonneg_thm numbers,
    eq_zero_iff_thm numbers,
    const_zero_thm numbers,
    shift_invariant_thm numbers,
    scale_homogeneous_thm numbers,
    neg_invariant_thm numbers,
    perm_invariant_thm numbers,
    reverse_invariant_thm numbers,
    element_deviation_bound_thm numbers,
    range_bound_thm numbers,
    center_triangle_bound_thm numbers⟩

/-! ## 8. Imperative Implementation -/

/-- Imperative implementation over `ℝ` using `Id.run do` with mutable state. -/
noncomputable def mean_absolute_deviation_imp (numbers : List ℝ) : ℝ := Id.run do
  let mut total : ℝ := 0
  for x in numbers do
    total := total + x
  let m : ℝ := total / (numbers.length : ℝ)
  let mut dev_total : ℝ := 0
  for x in numbers do
    dev_total := dev_total + |x - m|
  return dev_total / (numbers.length : ℝ)

/-- Executable imperative implementation over `ℚ` using `Id.run do` with mutable state. -/
def mean_absolute_deviation_rat_imp (numbers : List ℚ) : ℚ := Id.run do
  let mut total : ℚ := 0
  for x in numbers do
    total := total + x
  let m : ℚ := total / (numbers.length : ℚ)
  let mut dev_total : ℚ := 0
  for x in numbers do
    dev_total := dev_total + |x - m|
  return dev_total / (numbers.length : ℚ)

/-- Executable imperative implementation over `Float` using `Id.run do` with mutable state. -/
def mean_absolute_deviation_float_imp (numbers : List Float) : Float := Id.run do
  let mut total : Float := 0.0
  for x in numbers do
    total := total + x
  let m : Float := total / numbers.length.toFloat
  let mut dev_total : Float := 0.0
  for x in numbers do
    dev_total := dev_total + Float.abs (x - m)
  return dev_total / numbers.length.toFloat

/-! ## 9. Imperative Tests -/

example : Float.abs (mean_absolute_deviation_float_imp [1.0, 2.0, 3.0] - 2.0 / 3.0) < 1e-6 := by
  native_decide

example : Float.abs (mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6 := by
  native_decide

example : Float.abs (mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0) < 1e-6 := by
  native_decide

example : mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0] == 1.0 := by
  native_decide

example : mean_absolute_deviation_rat_imp [1, 2, 3] = 2 / 3 := by native_decide
example : mean_absolute_deviation_rat_imp [1, 2, 3, 4] = 1 := by native_decide
example : mean_absolute_deviation_rat_imp [1, 2, 3, 4, 5] = 6 / 5 := by native_decide

#eval mean_absolute_deviation_float_imp [1.0, 2.0, 3.0]
#eval mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0]
#eval mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0, 5.0]

#eval Plausible.Testable.check (∀ xs : List Int,
  decide (let qs := intsToRats xs
    mean_absolute_deviation_rat qs = mean_absolute_deviation_rat_imp qs) = true)

/-! ## 10. Equivalence Theorem (Functional = Imperative) -/

theorem foldl_add_eq_sum {α : Type*} [AddCommMonoid α] (xs : List α) (init : α) :
    xs.foldl (· + ·) init = init + xs.sum := by
  induction xs generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.sum_cons, ih]
    ac_rfl

theorem foldl_add_fn_eq_sum_map {α β : Type*} [AddCommMonoid β] (xs : List α) (f : α → β) (init : β) :
    xs.foldl (fun acc x => acc + f x) init = init + (xs.map f).sum := by
  rw [← List.foldl_map, foldl_add_eq_sum]

/-- Equivalence proposition between functional and imperative `ℝ` implementations. -/
def equiv_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation numbers = mean_absolute_deviation_imp numbers

/-- Functional and imperative `ℝ` implementations are equivalent on all inputs. -/
theorem mean_absolute_deviation_equiv (numbers : List ℝ) :
    mean_absolute_deviation numbers = mean_absolute_deviation_imp numbers := by
  unfold mean_absolute_deviation mean mean_absolute_deviation_imp
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure,
    foldl_add_fn_eq_sum_map, foldl_add_eq_sum, zero_add]
  rfl

theorem equiv_thm (numbers : List ℝ) : equiv_prop numbers :=
  mean_absolute_deviation_equiv numbers

/-- Functional and imperative `ℚ` implementations are equivalent on all inputs. -/
theorem mean_absolute_deviation_rat_equiv (numbers : List ℚ) :
    mean_absolute_deviation_rat numbers = mean_absolute_deviation_rat_imp numbers := by
  unfold mean_absolute_deviation_rat mean_rat mean_absolute_deviation_rat_imp
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure,
    foldl_add_fn_eq_sum_map, foldl_add_eq_sum, zero_add]
  rfl

/-- Functional and imperative `Float` implementations are equivalent on all inputs. -/
theorem mean_absolute_deviation_float_equiv (numbers : List Float) :
    mean_absolute_deviation_float numbers = mean_absolute_deviation_float_imp numbers := by
  unfold mean_absolute_deviation_float mean_float mean_absolute_deviation_float_imp
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure,
    List.foldl_map]
  rfl

end humaneval_4_mean_absolute_deviation
