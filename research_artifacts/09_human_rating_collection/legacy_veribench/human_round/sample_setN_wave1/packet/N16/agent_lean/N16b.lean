import Mathlib

/-!
# HumanEval/4 -- `mean_absolute_deviation`

Python source that is formalised here:

```python
def mean_absolute_deviation(numbers: List[float]) -> float:
    mean = sum(numbers) / len(numbers)
    return sum(abs(x - mean) for x in numbers) / len(numbers)
```

For a list of numbers the *mean absolute deviation* is the average of the
absolute distances of the elements to the arithmetic mean of the list.

The program divides by `len(numbers)`, therefore its admissible inputs are
exactly the **non-empty** lists of finite numbers; this is the pre-condition
`Pre` used below.

Three numeric layers are provided.

* **Float layer** -- a literal transliteration of the Python source using Lean's
  primitive `Float`.  It carries the ground unit tests taken from HumanEval's
  `check` function and the imperative (`Id.run do`) implementation.
* **Rat layer** -- an exact *computable* rational model of the same formula.  It
  is the executable counterpart used by the property based tests and it also
  carries an imperative implementation.
* **Real layer** -- the mathematical model.  All properties, the pre/post
  conditions and the correctness theorem are stated and proved over `Real`
  (the proofs are carried out once for an arbitrary `LinearOrderedField`).

Because primitive `Float` arithmetic is opaque to the kernel, no general
arithmetic law about `Float` can be proved; the exact mathematical content of
the task is therefore stated over `Real` (and mirrored over `Rat`), while the
`Float` layer keeps the syntactic shape of the Python program and its
functional/imperative equivalence.
-/

namespace humaneval_4_mean_absolute_deviation

/-! ## 1. Float layer: literal transliteration of the Python program -/

/-- Absolute value on primitive `Float`, written out explicitly so that it is
computable (Lean has no `DecidableEq Float` instance and `Float.abs` is opaque). -/
def fabs (x : Float) : Float := if x < 0 then -x else x

/-- `sum` of a list of `Float`s, accumulated left to right exactly like the
imperative loop below does. -/
def fsum (xs : List Float) : Float := xs.foldl (fun b x => b + x) 0.0

/-- `len(numbers)` seen as a `Float` (there is no `NatCast Float` instance). -/
def flen (xs : List Float) : Float := Float.ofNat xs.length

/-- Functional definition: `mean_absolute_deviation` from HumanEval/4. -/
def mean_absolute_deviation (numbers : List Float) : Float :=
  let mean := fsum numbers / flen numbers
  fsum (numbers.map (fun x => fabs (x - mean))) / flen numbers

/-! ### Float unit tests -/
#eval mean_absolute_deviation [1.0, 2.0, 3.0]
#eval mean_absolute_deviation [1.0, 2.0, 3.0, 4.0]
#eval mean_absolute_deviation [1.0, 2.0, 3.0, 4.0, 5.0]

-- HumanEval `check`: `abs(candidate([1.0, 2.0, 3.0]) - 2.0/3.0) < 1e-6`
example : fabs (mean_absolute_deviation [1.0, 2.0, 3.0] - 2.0 / 3.0) < 0.000001 := by
  native_decide

-- HumanEval `check`: `abs(candidate([1.0, 2.0, 3.0, 4.0]) - 1.0) < 1e-6`
example : fabs (mean_absolute_deviation [1.0, 2.0, 3.0, 4.0] - 1.0) < 0.000001 := by
  native_decide

-- HumanEval `check`: `abs(candidate([1.0, 2.0, 3.0, 4.0, 5.0]) - 6.0/5.0) < 1e-6`
example : fabs (mean_absolute_deviation [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0) < 0.000001 := by
  native_decide

-- exact IEEE-754 values (`Float` has no decidable equality, hence `==`)
example : (mean_absolute_deviation [1.0, 2.0, 3.0, 4.0] == 1.0) = true := by native_decide
example : (mean_absolute_deviation [1.0, 2.0, 3.0, 4.0, 5.0] == 1.2) = true := by native_decide
example : (mean_absolute_deviation [4.0] == 0.0) = true := by native_decide

/-! ## 2. Rat layer: exact, computable rational model -/

/-- Arithmetic mean over `Rat`. -/
def meanQ (xs : List Rat) : Rat := xs.sum / (xs.length : Rat)

/-- Mean absolute deviation over `Rat`. -/
def madQ (xs : List Rat) : Rat :=
  (xs.map (fun x => |x - meanQ xs|)).sum / (xs.length : Rat)

/-! ### Rat unit tests (the exact counterparts of the HumanEval assertions) -/

#eval madQ [1, 2, 3]
#eval madQ [1, 2, 3, 4]
#eval madQ [1, 2, 3, 4, 5]

example : madQ [1, 2, 3] = 2 / 3 := by native_decide
example : madQ [1, 2, 3, 4] = 1 := by native_decide
example : madQ [1, 2, 3, 4, 5] = 6 / 5 := by native_decide
example : madQ [7] = 0 := by native_decide
example : madQ [2, 2, 2, 2] = 0 := by native_decide
example : madQ [-1, 1] = 1 := by native_decide

/-! ## 3. Generic exact model over a linearly ordered field

All the mathematical content is proved once for an arbitrary
`LinearOrderedField K`; it is instantiated below at `K = Real` (the layer in
which the specification is stated) and at `K = Rat` (the executable layer used
by the property based tests).
-/

section Generic
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Arithmetic mean of a list of numbers. -/
noncomputable def gmean (xs : List K) : K := xs.sum / (xs.length : K)

/-- Mean absolute deviation of a list around its own mean. -/
noncomputable def gmad (xs : List K) : K :=
  (xs.map (fun x => |x - gmean xs|)).sum / (xs.length : K)

theorem gmean_def (xs : List K) : gmean xs = xs.sum / (xs.length : K) := rfl

theorem gmad_def (xs : List K) :
    gmad xs = (xs.map (fun x => |x - gmean xs|)).sum / (xs.length : K) := rfl

theorem length_cast_ne_zero (xs : List K) (h : xs ≠ []) : (xs.length : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (List.length_pos_iff.mpr h))

/-- Triangle inequality in the form `|a - b| ≤ |a| + |b|`. -/
theorem abs_sub_le_abs_sum (a b : K) : |a - b| ≤ |a| + |b| := by
  have h : a - b = a + (-b) := by ring
  rw [h]
  calc |a + -b| ≤ |a| + |-b| := abs_add a (-b)
    _ = |a| + |b| := by rw [abs_neg]

theorem sum_map_nonneg (xs : List K) (f : K → K) (h : ∀ x ∈ xs, 0 ≤ f x) :
    0 ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (h y (List.mem_cons_self))
      (ih fun x hx => h x (List.mem_cons_of_mem y hx))

theorem sum_map_le (xs : List K) (f g : K → K) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h y (List.mem_cons_self))
      (ih fun x hx => h x (List.mem_cons_of_mem y hx))

theorem sum_map_zero (xs : List K) (f : K → K) (h : ∀ x ∈ xs, f x = 0) :
    (xs.map f).sum = 0 := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, h y (List.mem_cons_self),
      ih (fun x hx => h x (List.mem_cons_of_mem y hx)), zero_add]

theorem sum_map_eq_zero (xs : List K) (f : K → K) (h : ∀ x ∈ xs, 0 ≤ f x)
    (hsum : (xs.map f).sum = 0) : ∀ x ∈ xs, f x = 0 := by
  induction xs with
  | nil => intro x hx; exact absurd hx (List.not_mem_nil)
  | cons y ys ih =>
    have hys : ∀ z ∈ ys, 0 ≤ f z := fun z hz => h z (List.mem_cons_of_mem y hz)
    have hnn : 0 ≤ (ys.map f).sum := sum_map_nonneg ys f hys
    have hy : 0 ≤ f y := h y (List.mem_cons_self)
    have e : f y + (ys.map f).sum = 0 := by
      simpa [List.map_cons, List.sum_cons] using hsum
    have h1 : f y = 0 := by linarith
    have h2 : (ys.map f).sum = 0 := by linarith
    intro x hx
    have hm : x = y ∨ x ∈ ys := List.mem_cons.mp hx
    cases hm with
    | inl hxy => rw [hxy]; exact h1
    | inr hx' => exact ih hys h2 x hx'

theorem sum_map_add (xs : List K) (f g : K → K) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_map_const (xs : List K) (c : K) :
    (xs.map (fun _ => c)).sum = (xs.length : K) * c := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
    ring

theorem sum_map_mul_left (xs : List K) (k : K) (f : K → K) :
    (xs.map (fun x => k * f x)).sum = k * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_replicate_mul (n : Nat) (a : K) :
    (List.replicate n a).sum = (n : K) * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.sum_cons, Nat.cast_add, Nat.cast_one, ih]
    ring

theorem sum_map_add_const (xs : List K) (c : K) :
    (xs.map (fun x => x + c)).sum = xs.sum + (xs.length : K) * c := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
    ring

theorem sum_map_mul_const (xs : List K) (c : K) :
    (xs.map (fun x => x * c)).sum = xs.sum * c := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem gmean_map_add (xs : List K) (c : K) (h : xs ≠ []) :
    gmean (xs.map (fun x => x + c)) = gmean xs + c := by
  have hn := length_cast_ne_zero xs h
  simp only [gmean, List.length_map, sum_map_add_const]
  rw [add_div, mul_div_cancel_left₀ _ hn]

theorem gmean_map_mul (xs : List K) (c : K) :
    gmean (xs.map (fun x => x * c)) = gmean xs * c := by
  simp only [gmean, List.length_map, sum_map_mul_const]
  rw [div_mul_eq_mul_div]

theorem map_abs_sub_add (xs : List K) (c m : K) :
    (xs.map (fun x => x + c)).map (fun x => |x - (m + c)|) =
      xs.map (fun x => |x - m|) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    have key : |y + c - (m + c)| = |y - m| := by congr 1; ring
    simp only [List.map_cons, ih, key]

theorem map_abs_sub_mul (xs : List K) (c m : K) :
    (xs.map (fun x => x * c)).map (fun x => |x - m * c|) =
      xs.map (fun x => |c| * |x - m|) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    have key : |y * c - m * c| = |c| * |y - m| := by
      rw [← abs_mul]
      congr 1
      ring
    simp only [List.map_cons, ih, key]

/-- Shifting every element by a constant leaves the mean absolute deviation
unchanged (the mean shifts by the same constant). -/
theorem gmad_shift (xs : List K) (c : K) (h : xs ≠ []) :
    gmad (xs.map (fun x => x + c)) = gmad xs := by
  have h1 := gmean_map_add xs c h
  have h2 := map_abs_sub_add xs c (gmean xs)
  simp only [gmad, h1, h2, List.length_map]

/-- Scaling every element by `c` scales the mean absolute deviation by `|c|`. -/
theorem gmad_scale (xs : List K) (c : K) :
    gmad (xs.map (fun x => x * c)) = |c| * gmad xs := by
  have h1 := gmean_map_mul xs c
  have h2 := map_abs_sub_mul xs c (gmean xs)
  have h3 := sum_map_mul_left xs (|c|) (fun x => |x - gmean xs|)
  simp only [gmad, h1, h2, h3, List.length_map, mul_div_assoc]

/-- The deviation does not depend on the order of the data. -/
theorem gmad_reverse (xs : List K) : gmad xs.reverse = gmad xs := by
  simp only [gmad, gmean, List.sum_reverse, List.length_reverse, List.map_reverse]

/-- A constant data set has zero deviation. -/
theorem gmad_replicate (n : Nat) (a : K) (h : 0 < n) :
    gmad (List.replicate n a) = 0 := by
  have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  have h1 : gmean (List.replicate n a) = a := by
    simp only [gmean, sum_replicate_mul, List.length_replicate]
    exact mul_div_cancel_left₀ _ hn
  have h2 : (List.replicate n a).map (fun x => |x - gmean (List.replicate n a)|)
      = List.replicate n (0 : K) := by
    rw [h1, List.map_replicate]
    congr 1
    simp
  simp only [gmad, h2, sum_replicate_mul, List.length_replicate, mul_zero, zero_div]

theorem gmad_singleton (a : K) : gmad [a] = 0 := by
  have h : [a] = List.replicate 1 a := by simp
  rw [h]
  exact gmad_replicate 1 a Nat.one_pos

/-- The deviation is zero exactly when every element equals the mean. -/
theorem gmad_eq_zero_iff (xs : List K) (h : xs ≠ []) :
    gmad xs = 0 ↔ ∀ x ∈ xs, x = gmean xs := by
  have hn := length_cast_ne_zero xs h
  constructor
  · intro hz
    have hsum : (xs.map (fun x => |x - gmean xs|)).sum = 0 := by
      have h5 : gmad xs = (xs.map (fun x => |x - gmean xs|)).sum / (xs.length : K) := rfl
      rw [h5, div_eq_mul_inv, mul_eq_zero] at hz
      cases hz with
      | inl hs => exact hs
      | inr hi => exact absurd (inv_eq_zero.mp hi) hn
    have hall := sum_map_eq_zero xs (fun x => |x - gmean xs|)
      (fun _ _ => abs_nonneg _) hsum
    intro x hx
    have h0 : |x - gmean xs| = 0 := hall x hx
    rw [abs_eq_zero, sub_eq_zero] at h0
    exact h0
  · intro hz
    have hs : (xs.map (fun x => |x - gmean xs|)).sum = 0 :=
      sum_map_zero xs _ (fun x hx => by rw [hz x hx]; simp)
    have h5 : gmad xs = (xs.map (fun x => |x - gmean xs|)).sum / (xs.length : K) := rfl
    rw [h5, hs, zero_div]

/-- The deviation is bounded by the mean of the absolute values plus the
absolute value of the mean (triangle inequality). -/
theorem gmad_le (xs : List K) :
    gmad xs ≤ (xs.map (fun x => |x|)).sum / (xs.length : K) + |gmean xs| := by
  by_cases h : xs = []
  · subst h
    simp [gmad, gmean]
  · have hn := length_cast_ne_zero xs h
    have h1 : (xs.map (fun x => |x - gmean xs|)).sum
        ≤ (xs.map (fun x => |x|)).sum + (xs.length : K) * |gmean xs| := by
      have h2 := sum_map_le xs (fun x => |x - gmean xs|)
        (fun x => |x| + |gmean xs|) (fun x _ => abs_sub_le_abs_sum x (gmean xs))
      rw [sum_map_add, sum_map_const] at h2
      exact h2
    have h3 : (xs.map (fun x => |x - gmean xs|)).sum / (xs.length : K)
        ≤ ((xs.map (fun x => |x|)).sum + (xs.length : K) * |gmean xs|) / (xs.length : K) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (Nat.cast_nonneg _))
    have h4 : ((xs.map (fun x => |x|)).sum + (xs.length : K) * |gmean xs|) / (xs.length : K)
        = (xs.map (fun x => |x|)).sum / (xs.length : K) + |gmean xs| := by
      rw [add_div, mul_div_cancel_left₀ (|gmean xs|) hn]
    have h5 : gmad xs = (xs.map (fun x => |x - gmean xs|)).sum / (xs.length : K) := rfl
    rw [h5, ← h4]
    exact h3

end Generic

/-- The mean absolute deviation is always non-negative. -/
theorem gmad_nonneg {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (xs : List K) : 0 ≤ gmad xs := by
  have h5 : gmad xs = (xs.map (fun x => |x - gmean xs|)).sum / (xs.length : K) := rfl
  rw [h5]
  exact div_nonneg (sum_map_nonneg xs _ (fun _ _ => abs_nonneg _)) (Nat.cast_nonneg _)

/-! ## 4. Real layer: the mathematical specification -/

/-- Arithmetic mean over `Real`. -/
noncomputable def meanR (xs : List Real) : Real := xs.sum / (xs.length : Real)

/-- Mean absolute deviation over `Real`: `MAD = average |x - x_mean|`. -/
noncomputable def madR (xs : List Real) : Real :=
  (xs.map (fun x => |x - meanR xs|)).sum / (xs.length : Real)

theorem meanR_eq_gmean (xs : List Real) : meanR xs = gmean xs := rfl
theorem madR_eq_gmad (xs : List Real) : madR xs = gmad xs := rfl
theorem meanQ_eq_gmean (xs : List Rat) : meanQ xs = gmean xs := rfl
theorem madQ_eq_gmad (xs : List Rat) : madQ xs = gmad xs := rfl

/-! ## 5. Pre-condition -/

/-- The Python program divides by `len(numbers)`; the admissible inputs are
exactly the non-empty lists of (finite) numbers.  Finiteness is automatic in the
`Real` model. -/
def Pre (numbers : List Real) : Prop := numbers ≠ []

/-! ## 6. Properties and their proofs -/

/-- The defining formula of the program, with the mean inlined. -/
def mad_def_prop (xs : List Real) : Prop :=
  madR xs = (xs.map (fun x => |x - xs.sum / (xs.length : Real)|)).sum / (xs.length : Real)

/-- `MAD >= 0`. -/
def mad_nonneg_prop (xs : List Real) : Prop := 0 ≤ madR xs

/-- Translating the whole data set does not change the deviation. -/
def mad_shift_prop (xs : List Real) (c : Real) : Prop :=
  xs ≠ [] → madR (xs.map (fun x => x + c)) = madR xs

/-- Scaling the whole data set by `c` scales the deviation by `|c|`. -/
def mad_scale_prop (xs : List Real) (c : Real) : Prop :=
  madR (xs.map (fun x => x * c)) = |c| * madR xs

/-- The deviation does not depend on the order of the data. -/
def mad_reverse_prop (xs : List Real) : Prop := madR xs.reverse = madR xs

/-- A single observation has zero deviation. -/
def mad_singleton_prop (a : Real) : Prop := madR [a] = 0

/-- A constant data set has zero deviation. -/
def mad_const_prop (n : Nat) (a : Real) : Prop :=
  0 < n → madR (List.replicate n a) = 0

/-- The deviation vanishes exactly when every element equals the mean. -/
def mad_eq_zero_iff_prop (xs : List Real) : Prop :=
  xs ≠ [] → (madR xs = 0 ↔ ∀ x ∈ xs, x = meanR xs)

/-- Triangle-inequality bound: `MAD <= mean |x| + |mean x|`. -/
def mad_le_mean_abs_prop (xs : List Real) : Prop :=
  madR xs ≤ (xs.map (fun x => |x|)).sum / (xs.length : Real) + |meanR xs|

theorem mad_def_thm (xs : List Real) : mad_def_prop xs := rfl
theorem mad_nonneg_thm (xs : List Real) : mad_nonneg_prop xs := gmad_nonneg xs
theorem mad_shift_thm (xs : List Real) (c : Real) : mad_shift_prop xs c := gmad_shift xs c
theorem mad_scale_thm (xs : List Real) (c : Real) : mad_scale_prop xs c := gmad_scale xs c
theorem mad_reverse_thm (xs : List Real) : mad_reverse_prop xs := gmad_reverse xs
theorem mad_singleton_thm (a : Real) : mad_singleton_prop a := gmad_singleton a
theorem mad_const_thm (n : Nat) (a : Real) : mad_const_prop n a := gmad_replicate n a
theorem mad_eq_zero_iff_thm (xs : List Real) : mad_eq_zero_iff_prop xs := gmad_eq_zero_iff xs
theorem mad_le_mean_abs_thm (xs : List Real) : mad_le_mean_abs_prop xs := gmad_le xs

/-! ## 7. Post-condition -/

/-- Post-condition: the returned value is the mean absolute deviation of the
input and it satisfies every property proved above. -/
def Post_prop (numbers : List Real) (y : Real) : Prop :=
  y = madR numbers ∧
  mad_def_prop numbers ∧
  mad_nonneg_prop numbers ∧
  mad_le_mean_abs_prop numbers ∧
  mad_reverse_prop numbers ∧
  mad_eq_zero_iff_prop numbers ∧
  (∀ c : Real, mad_scale_prop numbers c) ∧
  (∀ c : Real, madR (numbers.map (fun x => x + c)) = madR numbers)

/-! ## 8. Property based tests

The properties above are stated over `Real`, which is not a computable type, so
they have no executable check.  Each of them is therefore tested through its
executable `Rat` counterpart `madQ` / `meanQ` (the very same formula, see
`madQ_eq_gmad` and `madR_eq_gmad`): exhaustively over a fixed corpus of rational
lists (`pbtLists`, bounded PBTs) and randomly over generated inputs
(`Plausible.Testable.check`).  The untested `Real` property is named in the
comment above each test.
-/

/-- Fixed corpus of rational lists for the bounded property based tests. -/
def pbtLists : List (List Rat) :=
  [ [1, 2, 3],
    [1, 2, 3, 4],
    [1, 2, 3, 4, 5],
    [0],
    [7],
    [5, 5, 5, 5],
    [-1, 2, -3, 4],
    [1/2, -3/4, 5/8, 0, 12],
    [10, -10, 10, -10],
    [-5, -4, -3, -2, -1],
    [100, 1, 2, 3],
    [1/3, 1/3, 1/3, 2/3],
    [0, 0, 0],
    [-1/2, 1/2],
    [2, 4, 4, 4, 5, 5, 7, 9] ]

/-- Scaling / shifting factors used by the bounded tests. -/
def pbtCs : List Rat := [0, 1, -1, 2, -3, 1/2, -5/7, 100]

/-- Constant values used by the bounded tests. -/
def pbtVals : List Rat := [0, 1, -1, 1/2, -7/3, 100]

def chk_def (xs : List Rat) : Bool :=
  if madQ xs = (xs.map (fun x => |x - xs.sum / (xs.length : Rat)|)).sum / (xs.length : Rat)
  then true else false

def chk_nonneg (xs : List Rat) : Bool := if 0 ≤ madQ xs then true else false

def chk_le (xs : List Rat) : Bool :=
  if madQ xs ≤ (xs.map (fun x => |x|)).sum / (xs.length : Rat) + |meanQ xs|
  then true else false

def chk_rev (xs : List Rat) : Bool := if madQ xs.reverse = madQ xs then true else false

def chk_zero (xs : List Rat) : Bool :=
  if xs = [] then true
  else if madQ xs = 0 then (if ∀ x ∈ xs, x = meanQ xs then true else false)
  else if ∀ x ∈ xs, x = meanQ xs then false else true

def chk_scale (xs : List Rat) (c : Rat) : Bool :=
  if madQ (xs.map (fun x => x * c)) = |c| * madQ xs then true else false

def chk_shift (xs : List Rat) (c : Rat) : Bool :=
  if xs = [] then true else if madQ (xs.map (fun x => x + c)) = madQ xs then true else false

def chk_single (a : Rat) : Bool := if madQ [a] = 0 then true else false

def chk_const (n : Nat) (a : Rat) : Bool :=
  if n = 0 then true else if madQ (List.replicate n a) = 0 then true else false

def chk_post (xs : List Rat) : Bool :=
  chk_def xs && chk_nonneg xs && chk_le xs && chk_rev xs && chk_zero xs &&
    pbtCs.all (fun c => chk_scale xs c && chk_shift xs c)

-- PBT for `mad_def_prop` (Real): executable counterpart over `Rat`
example : pbtLists.all chk_def = true := by native_decide

-- PBT for `mad_nonneg_prop` (Real): executable counterpart over `Rat`
example : pbtLists.all chk_nonneg = true := by native_decide

-- PBT for `mad_le_mean_abs_prop` (Real): executable counterpart over `Rat`
example : pbtLists.all chk_le = true := by native_decide

-- PBT for `mad_reverse_prop` (Real): executable counterpart over `Rat`
example : pbtLists.all chk_rev = true := by native_decide

-- PBT for `mad_eq_zero_iff_prop` (Real): executable counterpart over `Rat`
example : pbtLists.all chk_zero = true := by native_decide

-- PBT for `mad_scale_prop` (Real): executable counterpart over `Rat`
example : pbtLists.all (fun xs => pbtCs.all (chk_scale xs)) = true := by native_decide

-- PBT for `mad_shift_prop` (Real): executable counterpart over `Rat`
example : pbtLists.all (fun xs => pbtCs.all (chk_shift xs)) = true := by native_decide

-- PBT for `mad_singleton_prop` (Real): executable counterpart over `Rat`
example : pbtVals.all chk_single = true := by native_decide

-- PBT for `mad_const_prop` (Real): executable counterpart over `Rat`
example : (List.range 8).all (fun n => pbtVals.all (chk_const n)) = true := by native_decide

-- PBT for `Post_prop` (Real): executable counterpart over `Rat`, with the
-- universally quantified scaling/shifting component restricted to `pbtCs`
example : pbtLists.all chk_post = true := by native_decide

-- Randomised PBTs (Plausible).  `madR`-properties over `Real` are not
-- executable; these check the identical formula on the `Rat` layer.
#eval Plausible.Testable.check
  (∀ xs : List Int, 0 ≤ madQ (xs.map (fun n => (n : Rat))))

#eval Plausible.Testable.check
  (∀ xs : List Int,
    madQ ((xs.map (fun n => (n : Rat))).reverse) = madQ (xs.map (fun n => (n : Rat))))

#eval Plausible.Testable.check
  (∀ (xs : List Int) (c : Int),
    madQ ((1 :: xs).map (fun n => (n : Rat) + (c : Rat)))
      = madQ ((1 :: xs).map (fun n => (n : Rat))))

#eval Plausible.Testable.check
  (∀ (xs : List Int) (c : Int),
    madQ (xs.map (fun n => (n : Rat) * (c : Rat)))
      = |(c : Rat)| * madQ (xs.map (fun n => (n : Rat))))

#eval Plausible.Testable.check
  (∀ xs : List Int,
    madQ (xs.map (fun n => (n : Rat)))
      ≤ (xs.map (fun n => |(n : Rat)|)).sum / (xs.length : Rat)
          + |meanQ (xs.map (fun n => (n : Rat)))|)

#eval Plausible.Testable.check
  (∀ xs : List Int,
    decide (madQ ((1 :: xs).map (fun n => (n : Rat))) = 0) =
      ((1 :: xs).map (fun n => (n : Rat))).all
        (fun x => decide (x = meanQ ((1 :: xs).map (fun n => (n : Rat))))))

/-! ## 9. Correctness theorem -/

theorem correctness_thm (numbers : List Real) (h : Pre numbers) :
    Post_prop numbers (madR numbers) :=
  ⟨rfl,
   mad_def_thm numbers,
   mad_nonneg_thm numbers,
   mad_le_mean_abs_thm numbers,
   mad_reverse_thm numbers,
   mad_eq_zero_iff_thm numbers,
   fun c => mad_scale_thm numbers c,
   fun c => gmad_shift numbers c h⟩

/-! ## 10. Imperative implementation (`Id.run do` with mutable state) -/

/-- Imperative transcription of the Python function on the `Float` layer: two
accumulating loops with mutable state, mirroring `sum(numbers)` and
`sum(abs(x - mean) for x in numbers)`. -/
def mean_absolute_deviation_impF (numbers : List Float) : Float := Id.run do
  let mut total : Float := 0.0
  for x in numbers do
    total := total + x
  let mean := total / flen numbers
  let mut dev : Float := 0.0
  for x in numbers do
    dev := dev + fabs (x - mean)
  return dev / flen numbers

/-- Imperative transcription of the Python function on the exact rational layer. -/
def mean_absolute_deviation_imp (numbers : List Rat) : Rat := Id.run do
  let mut total : Rat := 0
  for x in numbers do
    total := total + x
  let mean := total / (numbers.length : Rat)
  let mut dev : Rat := 0
  for x in numbers do
    dev := dev + |x - mean|
  return dev / (numbers.length : Rat)

/-! ### Imperative tests -/

#eval mean_absolute_deviation_impF [1.0, 2.0, 3.0]
#eval mean_absolute_deviation_impF [1.0, 2.0, 3.0, 4.0]
#eval mean_absolute_deviation_impF [1.0, 2.0, 3.0, 4.0, 5.0]
#eval mean_absolute_deviation_imp [1, 2, 3]
#eval mean_absolute_deviation_imp [1, 2, 3, 4]
#eval mean_absolute_deviation_imp [1, 2, 3, 4, 5]

example : (mean_absolute_deviation_impF [1.0, 2.0, 3.0, 4.0] == 1.0) = true := by native_decide
example : (mean_absolute_deviation_impF [1.0, 2.0, 3.0, 4.0, 5.0] == 1.2) = true := by native_decide
example : fabs (mean_absolute_deviation_impF [1.0, 2.0, 3.0] - 2.0 / 3.0) < 0.000001 := by
  native_decide
example : fabs (mean_absolute_deviation_impF [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0) < 0.000001 := by
  native_decide

example : mean_absolute_deviation_imp [1, 2, 3] = 2 / 3 := by native_decide
example : mean_absolute_deviation_imp [1, 2, 3, 4] = 1 := by native_decide
example : mean_absolute_deviation_imp [1, 2, 3, 4, 5] = 6 / 5 := by native_decide
example : mean_absolute_deviation_imp [2, 2, 2, 2] = 0 := by native_decide
example : mean_absolute_deviation_imp [-1, 1] = 1 := by native_decide

/-! ### Property based tests for the equivalence (executable layers) -/

def fLists : List (List Float) :=
  [ [1.0, 2.0, 3.0],
    [1.0, 2.0, 3.0, 4.0],
    [1.0, 2.0, 3.0, 4.0, 5.0],
    [0.0],
    [7.5],
    [5.0, 5.0, 5.0],
    [-1.0, 2.0, -3.0, 4.0],
    [0.5, -0.25, 0.125, 0.0, 12.0],
    [10.0, -10.0, 10.0, -10.0],
    [-5.5, -4.25, -3.125, -2.0, -1.0] ]

example : fLists.all
    (fun xs => mean_absolute_deviation_impF xs == mean_absolute_deviation xs) = true := by
  native_decide

example : pbtLists.all
    (fun xs => decide (mean_absolute_deviation_imp xs = madQ xs)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ xs : List Int,
    mean_absolute_deviation_imp (xs.map (fun n => (n : Rat)))
      = madQ (xs.map (fun n => (n : Rat))))

/-! ## 11. Equivalence: functional = imperative -/

/-- Pushing `map` into a left fold.  No arithmetic law about `Float` is needed:
both sides accumulate in the same order, so the statement is proved purely
structurally. -/
theorem fsum_map (xs : List Float) (f : Float → Float) (a : Float) :
    (xs.map f).foldl (fun b x => b + x) a = xs.foldl (fun b x => b + f x) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, List.foldl_cons]
    exact ih (a + f y)

theorem impF_eq_functional (numbers : List Float) :
    mean_absolute_deviation_impF numbers = mean_absolute_deviation numbers := by
  simp [mean_absolute_deviation_impF, mean_absolute_deviation, fsum, flen, fsum_map]

theorem foldl_add_map (xs : List Rat) (f : Rat → Rat) (a : Rat) :
    xs.foldl (fun b x => b + f x) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih (a + f y)]
    ring

theorem foldl_id_eq_sum (xs : List Rat) : xs.foldl (fun b x => b + x) 0 = xs.sum := by
  have h := foldl_add_map xs id 0
  simpa using h

theorem foldl_map_eq_sum (xs : List Rat) (f : Rat → Rat) :
    xs.foldl (fun b x => b + f x) 0 = (xs.map f).sum := by
  rw [foldl_add_map]
  simp

theorem imp_eq_functional (numbers : List Rat) :
    mean_absolute_deviation_imp numbers = madQ numbers := by
  simp [mean_absolute_deviation_imp, madQ, meanQ, foldl_id_eq_sum, foldl_map_eq_sum]


/-! ## 12. Cross-layer correspondence and exact ground values on `Real`

`madR_cast` says that the executable rational layer and the `Real` specification
layer agree: casting a rational data set into `Real` and applying `madR` yields
exactly the cast of `madQ`.  This is what licenses using the `Rat` layer as the
executable counterpart of the (non-computable) `Real` properties in the property
based tests above, and it lets us evaluate the specification layer exactly on
the HumanEval inputs.
-/

theorem sum_map_castR (xs : List Rat) :
    (xs.map ((↑) : Rat → Real)).sum = (xs.sum : Real) := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp only [List.map_cons, List.sum_cons, Rat.cast_add, ih]

theorem meanR_cast (xs : List Rat) :
    meanR (xs.map ((↑) : Rat → Real)) = (meanQ xs : Real) := by
  simp only [meanR, meanQ, sum_map_castR, List.length_map, Rat.cast_div, Rat.cast_natCast]

theorem map_abs_cast (xs : List Rat) (m : Rat) :
    (xs.map ((↑) : Rat → Real)).map (fun x => |x - (m : Real)|)
      = (xs.map (fun y => |y - m|)).map ((↑) : Rat → Real) := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [List.map_cons, Rat.cast_sub, Rat.cast_abs, ih]

/-- The rational implementation is exactly the `Real` specification restricted
to rational data. -/
theorem madR_cast (xs : List Rat) :
    madR (xs.map ((↑) : Rat → Real)) = (madQ xs : Real) := by
  have hmean := meanR_cast xs
  have hmap := map_abs_cast xs (meanQ xs)
  simp only [madR, madQ, hmean, hmap, List.length_map, sum_map_castR, Rat.cast_div,
    Rat.cast_natCast]

/-- HumanEval doctest: `mean_absolute_deviation([1.0, 2.0, 3.0, 4.0]) == 1.0`,
exactly, on the specification layer. -/
theorem madR_1234 : madR [1, 2, 3, 4] = 1 := by
  have h : ([(1 : Real), 2, 3, 4]) = ([(1 : Rat), 2, 3, 4]).map ((↑) : Rat → Real) := by simp
  have hq : madQ [(1 : Rat), 2, 3, 4] = 1 := by
    simp only [madQ, meanQ]
    norm_num [abs_of_nonneg]
  rw [h, madR_cast, hq]
  norm_num

/-- HumanEval `check`: `candidate([1.0, 2.0, 3.0]) == 2/3`, exactly. -/
theorem madR_123 : madR [1, 2, 3] = 2 / 3 := by
  have h : ([(1 : Real), 2, 3]) = ([(1 : Rat), 2, 3]).map ((↑) : Rat → Real) := by simp
  have hq : madQ [(1 : Rat), 2, 3] = 2 / 3 := by
    simp only [madQ, meanQ]
    norm_num [abs_of_nonneg]
  rw [h, madR_cast, hq]
  norm_num

/-- HumanEval `check`: `candidate([1.0, 2.0, 3.0, 4.0, 5.0]) == 6/5`, exactly. -/
theorem madR_12345 : madR [1, 2, 3, 4, 5] = 6 / 5 := by
  have h : ([(1 : Real), 2, 3, 4, 5]) =
      ([(1 : Rat), 2, 3, 4, 5]).map ((↑) : Rat → Real) := by simp
  have hq : madQ [(1 : Rat), 2, 3, 4, 5] = 6 / 5 := by
    simp only [madQ, meanQ]
    norm_num [abs_of_nonneg]
  rw [h, madR_cast, hq]
  norm_num

end humaneval_4_mean_absolute_deviation
