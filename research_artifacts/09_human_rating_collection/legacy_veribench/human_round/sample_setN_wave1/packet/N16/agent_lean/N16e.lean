import Mathlib
import Plausible

/-!
# HumanEval/4 — Mean Absolute Deviation

Python source (`mean_absolute_deviation`) computes, for a non-empty list of
numbers,

```
MAD = average |x - mean(x)|
    = (sum |x_i - mean|) / n
    where mean = (sum x_i) / n.
```

The Python surface type is `float`. The algorithm itself is the standard
mathematical definition of mean absolute deviation about the arithmetic mean;
it is not a specification of IEEE-754 rounding. This file therefore contains:

* an executable `Float` transcription used for ground unit tests (the Python
  checks use a `1e-6` absolute tolerance);
* an exact implementation over any linear ordered field (`Rat` and `Real`),
  which is the mathematical model of the program. Property, correctness and
  functional/imperative equivalence theorems are stated and proved at that
  level. `Rat` is the executable counterpart used for property-based tests;
  the same definitions instantiate at `Real`.

The Python program divides by `len(numbers)` and therefore requires a
non-empty list. That is the precondition.
-/

namespace humaneval_4_mean_absolute_deviation

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Float layer (Python executable surface) -/

/-- Direct transcription of the Python function on Lean `Float`. -/
def meanAbsoluteDeviationFloat (numbers : List Float) : Float :=
  let mean := numbers.sum / numbers.length.toFloat
  (numbers.map (fun x => (x - mean).abs)).sum / numbers.length.toFloat

/-- Python-facing name. -/
abbrev mean_absolute_deviation := meanAbsoluteDeviationFloat

/-! ## Exact mathematical model -/

section OrderedField

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- Arithmetic mean. On the empty list this is `0 / 0 = 0` in a field;
    the Python program is not called on that input (`Pre`). -/
def listMean (xs : List α) : α :=
  xs.sum / (xs.length : α)

/-- Mean absolute deviation about the arithmetic mean.

    `MAD(xs) = (sum |x - mean(xs)|) / length(xs)`. -/
def meanAbsoluteDeviation (xs : List α) : α :=
  (xs.map (fun x => |x - listMean xs|)).sum / (xs.length : α)

/-! ## Unit tests -/

-- Float ground tests corresponding to `check` in the Python source.
#eval meanAbsoluteDeviationFloat [1.0, 2.0, 3.0]
#eval meanAbsoluteDeviationFloat [1.0, 2.0, 3.0, 4.0]
#eval meanAbsoluteDeviationFloat [1.0, 2.0, 3.0, 4.0, 5.0]

example : (meanAbsoluteDeviationFloat [1.0, 2.0, 3.0] - (2.0 / 3.0)).abs < (1e-6 : Float) := by
  native_decide

example : meanAbsoluteDeviationFloat [1.0, 2.0, 3.0, 4.0] == 1.0 := by
  native_decide

example : (meanAbsoluteDeviationFloat [1.0, 2.0, 3.0, 4.0, 5.0] - (6.0 / 5.0)).abs < (1e-6 : Float) := by
  native_decide

-- Exact Rat counterparts of the same checks (the Python expected values).
#eval meanAbsoluteDeviation ([1, 2, 3] : List Rat)
#eval meanAbsoluteDeviation ([1, 2, 3, 4] : List Rat)
#eval meanAbsoluteDeviation ([1, 2, 3, 4, 5] : List Rat)

example : meanAbsoluteDeviation ([1, 2, 3] : List Rat) = 2 / 3 := by
  native_decide

example : meanAbsoluteDeviation ([1, 2, 3, 4] : List Rat) = 1 := by
  native_decide

example : meanAbsoluteDeviation ([1, 2, 3, 4, 5] : List Rat) = 6 / 5 := by
  native_decide

/-! ## Precondition -/

/-- The Python function divides by `len(numbers)`, so the list must be non-empty. -/
def Pre (xs : List α) : Prop :=
  xs ≠ []

/-! ## Supporting lemmas -/

lemma sum_nonneg_of_mem {xs : List α} (h : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.sum_cons, List.mem_cons, forall_eq_or_imp] at h ⊢
    exact add_nonneg h.1 (ih h.2)

lemma length_cast_ne_zero {xs : List α} (h : xs ≠ []) : (xs.length : α) ≠ 0 := by
  intro h0
  have : xs.length = 0 := by exact_mod_cast h0
  exact h (List.length_eq_zero_iff.mp this)

lemma sum_eq_zero_of_nonneg {xs : List α} (hnn : ∀ x ∈ xs, 0 ≤ x) (hs : xs.sum = 0) :
    ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.sum_cons, List.mem_cons, forall_eq_or_imp] at hnn hs ⊢
    have hxs : 0 ≤ xs.sum := sum_nonneg_of_mem hnn.2
    have ha_le : a ≤ 0 := by
      have hle : a ≤ a + xs.sum := le_add_of_nonneg_right hxs
      simpa [hs] using hle
    have ha0 : a = 0 := le_antisymm ha_le hnn.1
    refine ⟨ha0, ih hnn.2 ?_⟩
    simpa [ha0] using hs

lemma sum_map_add_const (xs : List α) (c : α) :
    (xs.map (fun x => x + c)).sum = xs.sum + (xs.length : α) * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.cast_succ]
    ring

lemma sum_map_mul_const (xs : List α) (c : α) :
    (xs.map (fun x => c * x)).sum = c * xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

lemma sum_map_const_mul (xs : List α) (c : α) (f : α → α) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

lemma sum_eq_card_mul_of_all_eq (xs : List α) (x : α) (h : ∀ y ∈ xs, y = x) :
    xs.sum = (xs.length : α) * x := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.sum_cons, List.length_cons, List.mem_cons, forall_eq_or_imp] at h ⊢
    rw [h.1, ih h.2, Nat.cast_succ]
    ring

lemma mean_add (xs : List α) (c : α) (h : xs ≠ []) :
    listMean (xs.map (fun x => x + c)) = listMean xs + c := by
  unfold listMean
  rw [sum_map_add_const, List.length_map]
  have hn := length_cast_ne_zero (xs := xs) h
  field_simp [hn]
  ring

lemma mean_mul (xs : List α) (c : α) :
    listMean (xs.map (fun x => c * x)) = c * listMean xs := by
  unfold listMean
  rw [sum_map_mul_const, List.length_map, mul_div_assoc]

/-! ## Properties -/

/-- MAD is nonnegative. -/
def nonneg_prop (xs : List α) : Prop :=
  0 ≤ meanAbsoluteDeviation xs

theorem nonneg_thm (xs : List α) (h : Pre xs) : nonneg_prop xs := by
  have _ := h
  unfold nonneg_prop meanAbsoluteDeviation
  apply div_nonneg
  · apply sum_nonneg_of_mem
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨_, -, rfl⟩ := hy
    exact abs_nonneg _
  · exact Nat.cast_nonneg _

/-- MAD is zero iff every element equals the mean. -/
def zero_iff_mean_prop (xs : List α) : Prop :=
  meanAbsoluteDeviation xs = 0 ↔ ∀ x ∈ xs, x = listMean xs

theorem zero_iff_mean_thm (xs : List α) (h : Pre xs) : zero_iff_mean_prop xs := by
  unfold zero_iff_mean_prop
  have hn := length_cast_ne_zero h
  constructor
  · intro hz x hx
    have hsum : (xs.map (fun z => |z - listMean xs|)).sum = 0 := by
      unfold meanAbsoluteDeviation at hz
      rw [div_eq_iff hn] at hz
      simpa using hz
    have hall0 : ∀ z ∈ xs, |z - listMean xs| = 0 := by
      intro z hzmem
      apply sum_eq_zero_of_nonneg (xs := xs.map (fun w => |w - listMean xs|))
      · intro t ht
        simp only [List.mem_map] at ht
        obtain ⟨_, -, rfl⟩ := ht
        exact abs_nonneg _
      · exact hsum
      · exact List.mem_map_of_mem hzmem
    exact sub_eq_zero.mp (abs_eq_zero.mp (hall0 x hx))
  · intro hall
    unfold meanAbsoluteDeviation
    have hsum : (xs.map (fun z => |z - listMean xs|)).sum = 0 := by
      apply List.sum_eq_zero
      intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨z, hz, rfl⟩ := ht
      rw [hall z hz, sub_self, abs_zero]
    rw [hsum, zero_div]

/-- MAD is zero iff all elements are equal. -/
def zero_iff_const_prop (xs : List α) : Prop :=
  meanAbsoluteDeviation xs = 0 ↔ ∀ x ∈ xs, ∀ y ∈ xs, x = y

theorem zero_iff_const_thm (xs : List α) (h : Pre xs) : zero_iff_const_prop xs := by
  unfold zero_iff_const_prop
  have hmean := zero_iff_mean_thm xs h
  unfold zero_iff_mean_prop at hmean
  rw [hmean]
  constructor
  · intro hall x hx y hy
    rw [hall x hx, hall y hy]
  · intro hall x hx
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil xs h
    have hallx : ∀ z ∈ xs, z = y := fun z hz => hall z hz y hy
    have hmean : listMean xs = y := by
      unfold listMean
      rw [sum_eq_card_mul_of_all_eq xs y hallx, mul_div_cancel_left₀ _ (length_cast_ne_zero h)]
    rw [hallx x hx, hmean]

/-- Translating every element by `c` does not change MAD. -/
def translation_invariance_prop (xs : List α) : Prop :=
  ∀ c : α, meanAbsoluteDeviation (xs.map (fun x => x + c)) = meanAbsoluteDeviation xs

theorem translation_invariance_thm (xs : List α) (h : Pre xs) :
    translation_invariance_prop xs := by
  intro c
  unfold meanAbsoluteDeviation
  have hm := mean_add xs c h
  rw [List.length_map]
  have hmap :
      (xs.map (fun x => x + c)).map (fun y => |y - listMean (xs.map (fun x => x + c))|)
        = xs.map (fun x => |x - listMean xs|) := by
    rw [hm, List.map_map]
    refine List.map_congr_left ?_
    intro x _hx
    simp only [Function.comp_apply]
    rw [show x + c - (listMean xs + c) = x - listMean xs by ring]
  rw [hmap]

/-- Scaling every element by `c` scales MAD by `|c|`. -/
def absolute_homogeneity_prop (xs : List α) : Prop :=
  ∀ c : α, meanAbsoluteDeviation (xs.map (fun x => c * x)) = |c| * meanAbsoluteDeviation xs

theorem absolute_homogeneity_thm (xs : List α) (h : Pre xs) :
    absolute_homogeneity_prop xs := by
  have _ := h
  intro c
  unfold meanAbsoluteDeviation
  rw [List.length_map]
  have hm := mean_mul xs c
  have hmap :
      (xs.map (fun x => c * x)).map (fun y => |y - listMean (xs.map (fun x => c * x))|)
        = xs.map (fun x => |c| * |x - listMean xs|) := by
    rw [hm, List.map_map]
    refine List.map_congr_left ?_
    intro x _hx
    simp only [Function.comp_apply]
    rw [show c * x - c * listMean xs = c * (x - listMean xs) by ring, abs_mul]
  rw [hmap, sum_map_const_mul, mul_div_assoc]

/-- The mean is a center: the signed deviations sum to zero. -/
def centered_sum_prop (xs : List α) : Prop :=
  (xs.map (fun x => x - listMean xs)).sum = 0

theorem centered_sum_thm (xs : List α) (h : Pre xs) : centered_sum_prop xs := by
  unfold centered_sum_prop
  have hsum : (xs.map (fun x => x - listMean xs)).sum
      = xs.sum + (xs.length : α) * (-listMean xs) := by
    simp only [sub_eq_add_neg]
    exact sum_map_add_const xs (-listMean xs)
  rw [hsum]
  unfold listMean
  have hn := length_cast_ne_zero h
  field_simp [hn]
  ring

/-- MAD depends only on the multiset of values. -/
def permutation_invariance_prop (xs ys : List α) : Prop :=
  xs.Perm ys → meanAbsoluteDeviation xs = meanAbsoluteDeviation ys

theorem permutation_invariance_thm (xs ys : List α) :
    permutation_invariance_prop xs ys := by
  intro hperm
  have hlen : xs.length = ys.length := hperm.length_eq
  have hsum : xs.sum = ys.sum := hperm.sum_eq
  have hmean : listMean xs = listMean ys := by
    unfold listMean
    rw [hsum, hlen]
  unfold meanAbsoluteDeviation
  rw [hmean, hlen]
  have hp : (xs.map (fun x => |x - listMean ys|)).Perm
      (ys.map (fun y => |y - listMean ys|)) := hperm.map _
  rw [hp.sum_eq]

/-- A singleton has MAD zero. -/
def singleton_zero_prop (a : α) : Prop :=
  meanAbsoluteDeviation [a] = 0

theorem singleton_zero_thm (a : α) : singleton_zero_prop a := by
  unfold singleton_zero_prop meanAbsoluteDeviation listMean
  simp [abs_zero]

/-- The three assertions in the Python `check` function, exactly, over `Rat`. -/
def matches_reference_checks_prop : Prop :=
  meanAbsoluteDeviation ([1, 2, 3] : List Rat) = 2 / 3 ∧
  meanAbsoluteDeviation ([1, 2, 3, 4] : List Rat) = 1 ∧
  meanAbsoluteDeviation ([1, 2, 3, 4, 5] : List Rat) = 6 / 5

theorem matches_reference_checks_thm : matches_reference_checks_prop := by
  unfold matches_reference_checks_prop
  refine ⟨?_, ?_, ?_⟩
  · unfold meanAbsoluteDeviation listMean
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    norm_num
  · unfold meanAbsoluteDeviation listMean
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    norm_num
    have h32 : |(3 : Rat) / 2| = 3 / 2 := abs_of_nonneg (by norm_num)
    have h12 : |(1 : Rat) / 2| = 1 / 2 := abs_of_nonneg (by norm_num)
    simp only [h32, h12]
    norm_num
  · unfold meanAbsoluteDeviation listMean
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    norm_num

/-! ## Post-condition -/

/-- Conjunction of the mathematical obligations of the Python program
    on a non-empty list: nonnegativity, zero-characterization, translation
    invariance, absolute homogeneity, and centering of the mean. -/
def Post_prop (xs : List α) : Prop :=
  nonneg_prop xs ∧
  zero_iff_mean_prop xs ∧
  zero_iff_const_prop xs ∧
  translation_invariance_prop xs ∧
  absolute_homogeneity_prop xs ∧
  centered_sum_prop xs

/-! ## Property-based tests

The properties above are stated for every linear ordered field, including `Real`.
Real equality and order are not computable, so there is no executable PBT at
the `Real` layer. The checks below exercise the executable `Rat` counterpart of
each property (the same algorithm, exact rational arithmetic).
-/

-- nonneg_prop
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    0 ≤ meanAbsoluteDeviation ((x :: xs).map (fun n => (n : Rat))))
  { numInst := 40, maxSize := 8 }

example : (List.range 30).all (fun n =>
    decide (0 ≤ meanAbsoluteDeviation ([(n : Rat), (n + 1 : Rat), (n + 3 : Rat)]))) = true := by
  native_decide

-- zero_iff_mean_prop / zero_iff_const_prop
-- Executable Boolean form: every element equals the head iff MAD is zero.
def ratAllConst (ys : List Rat) : Bool :=
  match ys with
  | [] => true
  | y :: rest => rest.all (fun z => z == y)

def ratAllEqMean (ys : List Rat) : Bool :=
  let m := listMean ys
  ys.all (fun a => a == m)

#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    let ys : List Rat := (x :: xs).map (fun n => (n : Rat))
    ((meanAbsoluteDeviation ys == 0) = ratAllEqMean ys) ∧
      ((meanAbsoluteDeviation ys == 0) = ratAllConst ys))
  { numInst := 40, maxSize := 8 }

example : (List.range 30).all (fun n =>
    decide (meanAbsoluteDeviation (List.replicate (n + 1) (n : Rat)) = 0)) = true := by
  native_decide

example : decide (meanAbsoluteDeviation ([1, 2, 3] : List Rat) ≠ 0) = true := by
  native_decide

-- translation_invariance_prop
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int) (c : Int),
    let ys : List Rat := (x :: xs).map (fun n => (n : Rat))
    meanAbsoluteDeviation (ys.map (fun y => y + (c : Rat))) = meanAbsoluteDeviation ys)
  { numInst := 40, maxSize := 8 }

example : (List.range 20).all (fun n =>
    decide (meanAbsoluteDeviation ([((n : Rat)), n + 1, n + 2].map (fun y => y + 5))
      = meanAbsoluteDeviation [(n : Rat), n + 1, n + 2])) = true := by
  native_decide

-- absolute_homogeneity_prop
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int) (c : Int),
    let ys : List Rat := (x :: xs).map (fun n => (n : Rat))
    meanAbsoluteDeviation (ys.map (fun y => (c : Rat) * y))
      = |(c : Rat)| * meanAbsoluteDeviation ys)
  { numInst := 40, maxSize := 8 }

example : (List.range 15).all (fun n =>
    decide (meanAbsoluteDeviation ([((n : Rat)), n + 1].map (fun y => (-2 : Rat) * y))
      = 2 * meanAbsoluteDeviation [(n : Rat), n + 1])) = true := by
  native_decide

-- centered_sum_prop
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    let ys : List Rat := (x :: xs).map (fun n => (n : Rat))
    (ys.map (fun y => y - listMean ys)).sum = 0)
  { numInst := 40, maxSize := 8 }

example : (List.range 20).all (fun n =>
    decide (([(n : Rat), n + 2, n + 5].map (fun y => y - listMean [(n : Rat), n + 2, n + 5])).sum = 0))
    = true := by
  native_decide

-- permutation_invariance_prop
#eval Plausible.Testable.check
  (∀ (a b c : Int),
    meanAbsoluteDeviation ([(a : Rat), b, c]) = meanAbsoluteDeviation ([(c : Rat), a, b]))
  { numInst := 40, maxSize := 12 }

example : (List.range 20).all (fun n =>
    decide (meanAbsoluteDeviation [(n : Rat), n + 1, n + 2]
      = meanAbsoluteDeviation [(n + 2 : Rat), n, n + 1])) = true := by
  native_decide

-- singleton_zero_prop
#eval Plausible.Testable.check
  (∀ a : Int, meanAbsoluteDeviation [(a : Rat)] = 0)
  { numInst := 40, maxSize := 20 }

example : (List.range 30).all (fun n =>
    decide (meanAbsoluteDeviation [(n : Rat)] = 0)) = true := by
  native_decide

-- matches_reference_checks_prop (closed; executable Boolean form of the three equalities)
example :
    (meanAbsoluteDeviation ([1, 2, 3] : List Rat) == 2 / 3 &&
      meanAbsoluteDeviation ([1, 2, 3, 4] : List Rat) == 1 &&
      meanAbsoluteDeviation ([1, 2, 3, 4, 5] : List Rat) == 6 / 5) = true := by
  native_decide

-- Post_prop, executable counterpart on sampled non-empty integer data
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int) (c : Int),
    let ys : List Rat := (x :: xs).map (fun n => (n : Rat))
    (0 ≤ meanAbsoluteDeviation ys) ∧
      ((meanAbsoluteDeviation ys == 0) = ratAllEqMean ys) ∧
      ((meanAbsoluteDeviation ys == 0) = ratAllConst ys) ∧
      meanAbsoluteDeviation (ys.map (fun y => y + (c : Rat))) = meanAbsoluteDeviation ys ∧
      meanAbsoluteDeviation (ys.map (fun y => (c : Rat) * y))
        = |(c : Rat)| * meanAbsoluteDeviation ys ∧
      (ys.map (fun y => y - listMean ys)).sum = 0)
  { numInst := 30, maxSize := 6 }

example : (List.range 12).all (fun n =>
    let ys : List Rat := [(n : Rat), n + 1, n + 4]
    decide (0 ≤ meanAbsoluteDeviation ys ∧
      meanAbsoluteDeviation (ys.map (fun y => y + 3)) = meanAbsoluteDeviation ys ∧
      meanAbsoluteDeviation (ys.map (fun y => (2 : Rat) * y)) = 2 * meanAbsoluteDeviation ys ∧
      (ys.map (fun y => y - listMean ys)).sum = 0)) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (xs : List α) (h : Pre xs) : Post_prop xs := by
  refine ⟨nonneg_thm xs h, zero_iff_mean_thm xs h, zero_iff_const_thm xs h,
    translation_invariance_thm xs h, absolute_homogeneity_thm xs h, centered_sum_thm xs h⟩

/-! ## Imperative implementation (`Id.run do`, mutable accumulators) -/

/-- Running sum, starting from `acc`. -/
def sumFrom (acc : α) (xs : List α) : α :=
  Id.run do
    let mut s := acc
    for x in xs do
      s := s + x
    return s

/-- Running sum of absolute deviations from a fixed center. -/
def devFrom (acc mean : α) (xs : List α) : α :=
  Id.run do
    let mut a := acc
    for x in xs do
      a := a + |x - mean|
    return a

/-- Imperative MAD: one pass for the mean, one pass for the average absolute
    deviation. Mirrors a straightforward stateful transcription of the Python. -/
def meanAbsoluteDeviationImp (xs : List α) : α :=
  Id.run do
    let mut s : α := 0
    for x in xs do
      s := s + x
    let mean := s / (xs.length : α)
    let mut acc : α := 0
    for x in xs do
      acc := acc + |x - mean|
    return acc / (xs.length : α)

lemma sumFrom_cons (acc a : α) (xs : List α) :
    sumFrom acc (a :: xs) = sumFrom (acc + a) xs := by
  unfold sumFrom
  simp only [Id.run, List.forIn_cons, pure_bind]

lemma sumFrom_eq (acc : α) (xs : List α) : sumFrom acc xs = acc + xs.sum := by
  induction xs generalizing acc with
  | nil => unfold sumFrom; simp
  | cons a xs ih =>
    rw [sumFrom_cons, ih, List.sum_cons]
    abel

lemma devFrom_cons (acc mean a : α) (xs : List α) :
    devFrom acc mean (a :: xs) = devFrom (acc + |a - mean|) mean xs := by
  unfold devFrom
  simp only [Id.run, List.forIn_cons, pure_bind]

lemma devFrom_eq (acc mean : α) (xs : List α) :
    devFrom acc mean xs = acc + (xs.map (fun x => |x - mean|)).sum := by
  induction xs generalizing acc with
  | nil => unfold devFrom; simp
  | cons a xs ih =>
    rw [devFrom_cons, ih, List.map_cons, List.sum_cons]
    abel

lemma imp_eq_helpers (xs : List α) :
    meanAbsoluteDeviationImp xs =
      devFrom 0 (sumFrom 0 xs / (xs.length : α)) xs / (xs.length : α) := by
  unfold meanAbsoluteDeviationImp sumFrom devFrom
  rfl

/-! ## Imperative tests -/

#eval meanAbsoluteDeviationImp ([1, 2, 3] : List Rat)
#eval meanAbsoluteDeviationImp ([1, 2, 3, 4] : List Rat)
#eval meanAbsoluteDeviationImp ([1, 2, 3, 4, 5] : List Rat)

example : meanAbsoluteDeviationImp ([1, 2, 3] : List Rat) = 2 / 3 := by
  native_decide

example : meanAbsoluteDeviationImp ([1, 2, 3, 4] : List Rat) = 1 := by
  native_decide

example : meanAbsoluteDeviationImp ([1, 2, 3, 4, 5] : List Rat) = 6 / 5 := by
  native_decide

example : meanAbsoluteDeviation ([1, 2, 3, 4] : List Rat)
    = meanAbsoluteDeviationImp ([1, 2, 3, 4] : List Rat) := by
  native_decide

end OrderedField

/-- Imperative Float transcription (mutable two-pass loop). -/
def meanAbsoluteDeviationFloatImp (numbers : List Float) : Float :=
  Id.run do
    let mut s : Float := 0.0
    for x in numbers do
      s := s + x
    let mean := s / numbers.length.toFloat
    let mut acc : Float := 0.0
    for x in numbers do
      acc := acc + (x - mean).abs
    return acc / numbers.length.toFloat

#eval meanAbsoluteDeviationFloatImp [1.0, 2.0, 3.0]
#eval meanAbsoluteDeviationFloatImp [1.0, 2.0, 3.0, 4.0]
#eval meanAbsoluteDeviationFloatImp [1.0, 2.0, 3.0, 4.0, 5.0]

example : meanAbsoluteDeviationFloatImp [1.0, 2.0, 3.0, 4.0] == 1.0 := by
  native_decide

example : (meanAbsoluteDeviationFloatImp [1.0, 2.0, 3.0] - (2.0 / 3.0)).abs < (1e-6 : Float) := by
  native_decide

example : meanAbsoluteDeviationFloat [1.0, 2.0, 3.0, 4.0]
    == meanAbsoluteDeviationFloatImp [1.0, 2.0, 3.0, 4.0] := by
  native_decide

example : (meanAbsoluteDeviationFloat [1.0, 2.0, 3.0, 4.0, 5.0]
    - meanAbsoluteDeviationFloatImp [1.0, 2.0, 3.0, 4.0, 5.0]).abs < (1e-6 : Float) := by
  native_decide

/-! ## Equivalence: functional = imperative

Proved for the exact ordered-field model (including `Rat` and `Real`).
Primitive `Float` arithmetic is opaque, so the same identity is checked on the
Python ground examples above rather than proved for arbitrary `Float` lists.
-/

section Equivalence

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem equivalence_thm (xs : List α) :
    meanAbsoluteDeviation xs = meanAbsoluteDeviationImp xs := by
  rw [imp_eq_helpers, devFrom_eq, sumFrom_eq]
  simp [meanAbsoluteDeviation, listMean, zero_add]

end Equivalence


/-! ## Real specializations

The theorems above are polymorphic in any linear ordered field, so they apply
to `Real`. The corollaries below name that instance explicitly. Executable
checks of the same properties are the `Rat` PBTs above (`Real` comparison is
not computable).
-/

theorem nonneg_thm_real (xs : List Real) (h : Pre xs) : nonneg_prop xs :=
  nonneg_thm xs h

theorem zero_iff_mean_thm_real (xs : List Real) (h : Pre xs) : zero_iff_mean_prop xs :=
  zero_iff_mean_thm xs h

theorem zero_iff_const_thm_real (xs : List Real) (h : Pre xs) : zero_iff_const_prop xs :=
  zero_iff_const_thm xs h

theorem translation_invariance_thm_real (xs : List Real) (h : Pre xs) :
    translation_invariance_prop xs :=
  translation_invariance_thm xs h

theorem absolute_homogeneity_thm_real (xs : List Real) (h : Pre xs) :
    absolute_homogeneity_prop xs :=
  absolute_homogeneity_thm xs h

theorem centered_sum_thm_real (xs : List Real) (h : Pre xs) : centered_sum_prop xs :=
  centered_sum_thm xs h

theorem permutation_invariance_thm_real (xs ys : List Real) :
    permutation_invariance_prop xs ys :=
  permutation_invariance_thm xs ys

theorem singleton_zero_thm_real (a : Real) : singleton_zero_prop a :=
  singleton_zero_thm a

theorem correctness_thm_real (xs : List Real) (h : Pre xs) : Post_prop xs :=
  correctness_thm xs h

theorem equivalence_thm_real (xs : List Real) :
    meanAbsoluteDeviation xs = meanAbsoluteDeviationImp xs :=
  equivalence_thm xs

end humaneval_4_mean_absolute_deviation
