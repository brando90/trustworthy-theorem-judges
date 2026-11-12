import Mathlib

/-!
# VeriBench — HumanEval/4: Mean Absolute Deviation

Formalization of the Python program

```python
def mean_absolute_deviation(numbers: List[float]) -> float:
    mean = sum(numbers) / len(numbers)
    return sum(abs(x - mean) for x in numbers) / len(numbers)
```

The program computes the mean absolute deviation (MAD) of a dataset:

    MAD = average |x - x_mean|

The intent of the program is the exact mathematical computation rather than
IEEE-754 rounding behaviour, so the specification layer uses exact rational
numbers `Rat`.  We also provide `madFloat`, an executable `Float`
implementation mirroring the Python source, for ground unit tests.

Contents:
* `mad`      — functional specification over `List Rat`
* `madFloat` — executable implementation over `List Float`
* `Pre`      — pre-condition (non-empty input)
* `mad_nonneg_prop`, `mad_const_prop`, `mad_eq_zero_prop` — properties
* `Post_prop` — post-condition (conjunction of the properties)
* `mad_correct` — correctness theorem `Pre → Post`
* `madImp`   — imperative implementation (`Id.run` with mutable state)
* `madImp_eq_mad` — functional/imperative equivalence
-/

namespace humaneval_4_mean_absolute_deviation

/-! ## Functional implementation -/

/-- Mean Absolute Deviation: exact rational model of the Python program. -/
def mad (xs : List Rat) : Rat :=
  let n : Rat := xs.length
  let mean := xs.sum / n
  (xs.map fun x => |x - mean|).sum / n

/-- Executable floating-point implementation, mirroring the Python source. -/
def madFloat (xs : List Float) : Float := Id.run do
  let n := xs.length.toFloat
  let mut s : Float := 0.0
  for x in xs do
    s := s + x
  let mean := s / n
  let mut t : Float := 0.0
  for x in xs do
    t := t + (x - mean).abs
  return t / n

/-! ## Unit tests -/

example : mad [1, 2, 3, 4] = 1 := by native_decide

example : mad [1, 2, 3, 4, 5] = (6 : Rat) / 5 := by native_decide

example : |mad [1, 2, 3] - (2 : Rat) / 3| < (1 : Rat) / 1000000 := by native_decide

example : madFloat [1.0, 2.0, 3.0, 4.0] == 1.0 := by native_decide

example : (madFloat [1.0, 2.0, 3.0] - 2.0 / 3.0).abs < 1e-6 := by native_decide

#eval mad [1, 2, 3, 4]
#eval mad [1, 2, 3, 4, 5]
#eval madFloat [1.0, 2.0, 3.0, 4.0]

/-! ## Pre-condition -/

/-- Pre-condition: the dataset is non-empty.  (The Python program divides by
`len(numbers)`, which raises `ZeroDivisionError` on an empty list.) -/
def Pre (xs : List Rat) : Prop := xs ≠ []

/-! ## Properties and their proofs -/

/-- The MAD is always non-negative. -/
def mad_nonneg_prop (xs : List Rat) : Prop := 0 ≤ mad xs

/-- The MAD of a constant (non-empty) dataset is zero. -/
def mad_const_prop (n : Nat) (c : Rat) : Prop := mad (List.replicate (n + 1) c) = 0

/-- The MAD is zero iff every data point equals the mean. -/
def mad_eq_zero_prop (xs : List Rat) : Prop :=
  mad xs = 0 ↔ ∀ x ∈ xs, x = xs.sum / (xs.length : Rat)

theorem mad_nonneg_thm (xs : List Rat) (_h : Pre xs) : mad_nonneg_prop xs := by
  show 0 ≤ (xs.map fun x => |x - xs.sum / (xs.length : Rat)|).sum / (xs.length : Rat)
  apply div_nonneg
  · apply List.sum_nonneg
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, _, rfl⟩
    exact abs_nonneg _
  · exact Nat.cast_nonneg _

theorem mad_const_thm (n : Nat) (c : Rat) : mad_const_prop n c := by
  have h0 : ((n + 1 : Nat) : Rat) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hmean : (List.replicate (n + 1) c).sum / ((List.replicate (n + 1) c).length : Rat) = c := by
    rw [List.sum_replicate, List.length_replicate, nsmul_eq_mul]
    exact mul_div_cancel_left₀ c h0
  show ((List.replicate (n + 1) c).map fun x =>
        |x - (List.replicate (n + 1) c).sum / ((List.replicate (n + 1) c).length : Rat)|).sum /
          ((List.replicate (n + 1) c).length : Rat) = 0
  rw [hmean, List.map_replicate]
  simp

/-- Helper: a list whose elements are all zero has zero sum. -/
theorem sum_eq_zero_of_all_eq_zero (l : List Rat) (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => simp
  | cons a as ih =>
      rw [List.sum_cons, h a List.mem_cons_self, zero_add]
      exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

theorem mad_eq_zero_thm (xs : List Rat) (h : Pre xs) : mad_eq_zero_prop xs := by
  have hn : (xs.length : Rat) ≠ 0 := by
    have h' : xs.length ≠ 0 := fun hl => h (List.length_eq_zero_iff.mp hl)
    exact_mod_cast h'
  have hnn : ∀ x ∈ xs.map (fun x => |x - xs.sum / (xs.length : Rat)|), 0 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, _, rfl⟩
    exact abs_nonneg _
  show (xs.map fun x => |x - xs.sum / (xs.length : Rat)|).sum / (xs.length : Rat) = 0 ↔
    ∀ x ∈ xs, x = xs.sum / (xs.length : Rat)
  constructor
  · intro hm y hy
    have hsum : (xs.map fun x => |x - xs.sum / (xs.length : Rat)|).sum = 0 := by
      rcases div_eq_zero_iff.mp hm with h1 | h1
      · exact h1
      · exact absurd h1 hn
    have h0 := List.all_zero_of_le_zero_le_of_sum_eq_zero hnn hsum
      (List.mem_map.mpr ⟨y, hy, rfl⟩)
    exact sub_eq_zero.mp (abs_eq_zero.mp h0)
  · intro hm
    have hsum : (xs.map fun x => |x - xs.sum / (xs.length : Rat)|).sum = 0 := by
      apply sum_eq_zero_of_all_eq_zero
      intro x hx
      rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
      rw [hm y hy]
      simp
    rw [hsum, zero_div]

/-! ## Post-condition -/

/-- Post-condition: the conjunction of all stated properties. -/
def Post_prop (xs : List Rat) : Prop :=
  mad_nonneg_prop xs ∧ mad_eq_zero_prop xs ∧
    (∀ (n : Nat) (c : Rat), xs = List.replicate (n + 1) c → mad_const_prop n c)

/-! ## Property-based tests -/

/-- Executable Boolean form of the post-condition, for property-based testing. -/
def postCheck (xs : List Rat) : Bool :=
  let mean := xs.sum / (xs.length : Rat)
  decide (0 ≤ mad xs)
    && (decide (mad xs = 0) == xs.all (fun y => decide (y = mean)))
    && (if xs.all (fun y => decide (y = mean)) then decide (mad xs = 0) else true)

/-- Sample of non-empty rational test lists (constant and non-constant). -/
def sampleLists : List (List Rat) :=
  ((List.range 4).flatMap fun n => (List.range 5).map fun c =>
    List.replicate (n + 1) ((c : Rat) - 2))
  ++
  ((List.range 4).flatMap fun a => (List.range 4).flatMap fun b =>
    (List.range 4).map fun c =>
      [(a : Rat) - 1, (b : Rat) / 2, (c : Rat) - (a : Rat) / 3])

-- Bounded PBT for the post-condition (executable counterpart of `Post_prop`).
example : sampleLists.all postCheck = true := by native_decide

-- Bounded PBT for `mad_nonneg_prop`.
example : sampleLists.all (fun xs => 0 ≤ mad xs) = true := by native_decide

-- Bounded PBT for `mad_const_prop`.
example : (List.range 6).all (fun n => (List.range 6).all (fun c =>
    mad (List.replicate (n + 1) ((c : Rat) - 2)) = 0)) = true := by native_decide

-- Bounded PBT for the executable counterpart of `mad_eq_zero_prop`.
example : sampleLists.all (fun xs =>
    (decide (mad xs = 0) == xs.all (fun y => decide (y = xs.sum / (xs.length : Rat))))) = true :=
  by native_decide

-- Randomized PBT: non-negativity on random datasets.
#eval Plausible.Testable.check (∀ xs : List Nat, xs ≠ [] → 0 ≤ mad (xs.map fun n => (n : Rat)))

-- Randomized PBT: constant datasets have zero MAD.
#eval Plausible.Testable.check (∀ (n : Nat) (c : Int), mad (List.replicate (n + 1) (c : Rat)) = 0)

/-! ## Correctness theorem -/

theorem mad_correct (xs : List Rat) (h : Pre xs) : Post_prop xs :=
  ⟨mad_nonneg_thm xs h,
   mad_eq_zero_thm xs h,
   fun n c _hrep => mad_const_thm n c⟩

/-! ## Imperative implementation -/

/-- Imperative mean absolute deviation: `Id.run` with mutable state,
mirroring the Python program with explicit accumulation loops. -/
def madImp (xs : List Rat) : Rat := Id.run do
  let n : Rat := xs.length
  let mut s1 : Rat := 0
  for x in xs do
    s1 := s1 + x
  let mean := s1 / n
  let mut s2 : Rat := 0
  for x in xs do
    s2 := s2 + |x - mean|
  return s2 / n

/-! ## Imperative tests -/

example : madImp [1, 2, 3, 4] = 1 := by native_decide

example : madImp [1, 2, 3, 4, 5] = (6 : Rat) / 5 := by native_decide

example : madImp [1, 2, 3] = mad [1, 2, 3] := by native_decide

#eval madImp [1, 2, 3, 4]

/-! ## Equivalence of the functional and imperative implementations -/

/-- Generalized sum loop with explicit accumulator (proof auxiliary). -/
def sumAux (xs : List Rat) (init : Rat) : Rat := Id.run do
  let mut s : Rat := init
  for x in xs do
    s := s + x
  return s

/-- Generalized absolute-deviation sum loop (proof auxiliary). -/
def absDevAux (xs : List Rat) (mean init : Rat) : Rat := Id.run do
  let mut s : Rat := init
  for x in xs do
    s := s + |x - mean|
  return s

theorem sumAux_eq (xs : List Rat) (init : Rat) : sumAux xs init = init + xs.sum := by
  induction xs generalizing init with
  | nil => simp only [sumAux, List.forIn_nil, Id.run_pure, Id.run_bind, List.sum_nil, add_zero]
  | cons a as ih =>
      have step : sumAux (a :: as) init = sumAux as (init + a) := by
        simp only [sumAux, List.forIn_cons, Id.run_pure, Id.run_bind]
      rw [step, ih (init + a), List.sum_cons, add_assoc]

theorem absDevAux_eq (xs : List Rat) (mean init : Rat) :
    absDevAux xs mean init = init + (xs.map fun x => |x - mean|).sum := by
  induction xs generalizing init with
  | nil => simp only [absDevAux, List.forIn_nil, Id.run_pure, Id.run_bind, List.map_nil,
      List.sum_nil, add_zero]
  | cons a as ih =>
      have step : absDevAux (a :: as) mean init = absDevAux as mean (init + |a - mean|) := by
        simp only [absDevAux, List.forIn_cons, Id.run_pure, Id.run_bind]
      rw [step, ih (init + |a - mean|), List.map_cons, List.sum_cons, add_assoc]

theorem madImp_eq_mad (xs : List Rat) : madImp xs = mad xs := by
  have e : madImp xs = absDevAux xs (sumAux xs 0 / (xs.length : Rat)) 0 / (xs.length : Rat) := by
    simp only [madImp, sumAux, absDevAux, Id.run_pure, Id.run_bind]
  rw [e, absDevAux_eq, sumAux_eq]
  simp [mad]

end humaneval_4_mean_absolute_deviation
