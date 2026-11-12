import Mathlib

/-!
# Formalization of Python's `statistics.quantiles` (VeriBench task 31)

The Python module divides data into `n` continuous intervals with equal
probability and returns the `n - 1` interpolated cut points (quartiles by
default; deciles for `n = 10`, percentiles for `n = 100`).  Two methods are
supported: `"exclusive"` (sample quantiles) and `"inclusive"` (population
quantiles, where the minimum is the 0th percentile and the maximum the 100th).

## Modelling choices

* Data values are modelled as rationals (`Rat`).  Python accepts `int`,
  `float`, `Fraction` and `Decimal`; every concrete value of those types is a
  rational number, and CPython performs the interpolation with exact integer
  arithmetic before a single final division, so `Rat` reproduces the results
  exactly (the Python floats equal these rationals, e.g. `1.25 = 5/4`).
* The string `method` argument is kept at the checked entry point
  `benchmarkQuantiles` (mirroring `benchmark_quantiles`); the core
  implementation `quantiles` takes a Boolean flag `inclusive`.
* Errors are modelled with `Except String`: like `benchmark_quantiles`,
  `benchmarkQuantiles` returns a `StatisticsError`-style error whenever the
  pre-condition fails (fewer than two data points, `n < 1`, bad method).
-/

namespace «31_statistics_quantiles»

/-! ## Functional implementation -/

/-- Insert a rational into an already sorted list (insertion-sort step). -/
def insertRat (a : Rat) : List Rat → List Rat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertRat a bs

/-- Sort a list of rationals (insertion sort), modelling Python's `sorted`. -/
def sortRat : List Rat → List Rat
  | [] => []
  | a :: as => insertRat a (sortRat as)

/-- The `i`-th cut point (`1 ≤ i ≤ n - 1`) over already-sorted data,
reproducing CPython's exact integer arithmetic for both methods. -/
def cutPoint (sorted : List Rat) (n : Nat) (inclusive : Bool) (i : Nat) : Rat :=
  let ld := sorted.length
  if inclusive then
    let m := ld - 1
    let j := i * m / n
    let delta : Rat := (i * m % n : Nat)
    (sorted.getD j 0 * ((n : Rat) - delta) + sorted.getD (j + 1) 0 * delta) / (n : Rat)
  else
    let m := ld + 1
    let j0 := i * m / n
    let j := if j0 < 1 then 1 else if j0 > ld - 1 then ld - 1 else j0
    let deltaI : Int := (i : Int) * (m : Int) - (j : Int) * (n : Int)
    (sorted.getD (j - 1) 0 * ((n : Rat) - (deltaI : Rat)) + sorted.getD j 0 * (deltaI : Rat)) /
      (n : Rat)

/-- Functional implementation of `statistics.quantiles` on rational data. -/
def quantiles (data : List Rat) (n : Nat) (inclusive : Bool) : List Rat :=
  let sorted := sortRat data
  (List.range' 1 (n - 1)).map (cutPoint sorted n inclusive)

/-- Checked entry point mirroring `benchmark_quantiles`: validates the
pre-condition and raises a `StatisticsError`-style error when it fails. -/
def benchmarkQuantiles (data : List Rat) (n : Nat) (method : String) :
    Except String (List Rat) :=
  if data.length < 2 then
    .error "StatisticsError: must have at least two data points"
  else if n < 1 then
    .error "StatisticsError: n must be at least 1"
  else if !(method == "exclusive" || method == "inclusive") then
    .error "StatisticsError: unknown method"
  else
    .ok (quantiles data n (method == "inclusive"))

/-! ## Unit tests (mirroring the Python `check` function) -/

-- 1. Basic quartiles (default method = exclusive)
example : quantiles ([1, 2, 3, 4] : List Rat) 4 false = [5/4, 5/2, 15/4] := by
  native_decide

-- 2. Deciles
example : (quantiles ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List Rat) 10 false).length = 9 := by
  native_decide

-- 3. Median (n = 2)
example : quantiles ([1, 2, 3, 4, 5] : List Rat) 2 false = [3] := by
  native_decide

-- 4. Inclusive method
example : quantiles ([1, 2, 3, 4] : List Rat) 4 true = [7/4, 5/2, 13/4] := by
  native_decide

-- 5. Exclusive method (default)
example : (quantiles ([1, 2, 3, 4] : List Rat) 4 false).length = 3 := by
  native_decide

-- 6. Larger dataset
example : (quantiles ((List.range' 1 10).map fun k => (k : Rat)) 4 false).length = 3 := by
  native_decide

-- 7. Unsorted input is sorted internally
example : quantiles ([4, 1, 3, 2] : List Rat) 4 false =
    quantiles ([1, 2, 3, 4] : List Rat) 4 false := by
  native_decide

-- 8. Float data (represented exactly as rationals)
example : quantiles ([3/2, 5/2, 7/2, 9/2] : List Rat) 2 false = [3] := by
  native_decide

-- 9. Error cases (mirroring `benchmark_quantiles` raising `StatisticsError`)
example : (match benchmarkQuantiles ([1] : List Rat) 4 "exclusive" with
    | .ok _ => false | .error _ => true) = true := by
  native_decide

example : (match benchmarkQuantiles ([1, 2] : List Rat) 0 "exclusive" with
    | .ok _ => false | .error _ => true) = true := by
  native_decide

example : (match benchmarkQuantiles ([1, 2, 3] : List Rat) 4 "invalid" with
    | .ok _ => false | .error _ => true) = true := by
  native_decide

-- The checked entry point agrees with `quantiles` on valid inputs
example : (benchmarkQuantiles ([1, 2, 3, 4] : List Rat) 4 "exclusive").toOption =
    some [5/4, 5/2, 15/4] := by
  native_decide

#eval quantiles ([1, 2, 3, 4] : List Rat) 4 false
#eval benchmarkQuantiles ([4, 1, 3, 2] : List Rat) 4 "inclusive"

/-! ## Pre-condition -/

/-- Pre-condition: at least two data points, `n ≥ 1`, and a valid method.
(Python also checks that `data` is a list or tuple of numbers and that `n` is
an `int`; this is encoded in the Lean types.) -/
def Pre (data : List Rat) (n : Nat) (method : String) : Prop :=
  2 ≤ data.length ∧ 1 ≤ n ∧ (method = "exclusive" ∨ method = "inclusive")

/-! ## Sorting correctness lemmas -/

theorem mem_insertRat (a b : Rat) (l : List Rat) :
    b ∈ insertRat a l ↔ b = a ∨ b ∈ l := by
  induction l with
  | nil => simp [insertRat]
  | cons x xs ih =>
      by_cases h : a ≤ x
      · simp [insertRat, h]
      · simp [insertRat, h, ih, or_left_comm]

theorem mem_sortRat (b : Rat) (l : List Rat) : b ∈ sortRat l ↔ b ∈ l := by
  induction l with
  | nil => simp [sortRat]
  | cons x xs ih => simp [sortRat, mem_insertRat, ih]

theorem length_insertRat (a : Rat) (l : List Rat) :
    (insertRat a l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : a ≤ x
      · simp [insertRat, h]
      · simp [insertRat, h, ih]

theorem length_sortRat (l : List Rat) : (sortRat l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [sortRat, length_insertRat, ih]

/-! ## Properties and theorems -/

/-- Property: the result always has exactly `n - 1` cut points. -/
def quantiles_length_prop (data : List Rat) (n : Nat) (inclusive : Bool) : Prop :=
  (quantiles data n inclusive).length = n - 1

theorem quantiles_length_thm (data : List Rat) (n : Nat) (inclusive : Bool) :
    quantiles_length_prop data n inclusive := by
  simp [quantiles_length_prop, quantiles]

/-- Property: for `n = 1` the result is empty (Python: `range(1, 1)`). -/
def quantiles_n_one_prop (data : List Rat) (inclusive : Bool) : Prop :=
  quantiles data 1 inclusive = []

theorem quantiles_n_one_thm (data : List Rat) (inclusive : Bool) :
    quantiles_n_one_prop data inclusive := by
  simp [quantiles_n_one_prop, quantiles]

/-- Property: every inclusive-method cut point lies between the extremes of
the data set -- bounded below by some data point and bounded above by some
data point (equivalently, between the minimum and the maximum of the data).
This captures that Python's `inclusive` interpolation stays inside the data
range (unlike the `exclusive` method, which may extrapolate). -/
def quantiles_inclusive_bounds_prop (data : List Rat) (n : Nat) : Prop :=
  ∀ c ∈ quantiles data n true, (∃ lo ∈ data, lo ≤ c) ∧ (∃ hi ∈ data, c ≤ hi)

theorem quantiles_inclusive_bounds_thm (data : List Rat) (n : Nat)
    (hlen : 2 ≤ data.length) (hn : 1 ≤ n) :
    quantiles_inclusive_bounds_prop data n := by
  intro c hc
  set sorted := sortRat data with hsorted
  have hc' : c ∈ (List.range' 1 (n - 1)).map (cutPoint sorted n true) := hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc'
  rw [List.mem_range'_1] at hi
  obtain ⟨hi1, hin⟩ := hi
  have hld : sorted.length = data.length := length_sortRat data
  have hlen' : 2 ≤ sorted.length := hld.symm ▸ hlen
  have hnpos : 0 < n := by omega
  have hilt : i < n := by omega
  have hm : 0 < sorted.length - 1 := by omega
  have hmul : i * (sorted.length - 1) < (sorted.length - 1) * n := by
    rw [Nat.mul_comm (sorted.length - 1) n]
    exact Nat.mul_lt_mul_of_pos_right hilt hm
  have hjlt : i * (sorted.length - 1) / n < sorted.length - 1 :=
    (Nat.div_lt_iff_lt_mul hnpos).mpr hmul
  have hjs : i * (sorted.length - 1) / n < sorted.length := by omega
  have hj1s : i * (sorted.length - 1) / n + 1 < sorted.length := by omega
  set j := i * (sorted.length - 1) / n with hjdef
  set δ := i * (sorted.length - 1) % n with hδdef
  set a := sorted[j]'hjs with ha
  set b := sorted[j + 1]'hj1s with hb
  have haeq : sorted.getD j 0 = a := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjs]
    rfl
  have hbeq : sorted.getD (j + 1) 0 = b := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1s]
    rfl
  have ha_mem : a ∈ data := (mem_sortRat a data).mp (List.getElem_mem hjs)
  have hb_mem : b ∈ data := (mem_sortRat b data).mp (List.getElem_mem hj1s)
  have hcut : cutPoint sorted n true i =
      (sorted.getD j 0 * ((n : Rat) - (δ : Rat)) + sorted.getD (j + 1) 0 * (δ : Rat)) /
        (n : Rat) := rfl
  rw [haeq, hbeq] at hcut
  have hδn : δ < n := Nat.mod_lt _ hnpos
  have hnR : (0 : Rat) < (n : Rat) := by exact_mod_cast hnpos
  have ht0 : (0 : Rat) ≤ (δ : Rat) / (n : Rat) :=
    div_nonneg (by exact_mod_cast Nat.zero_le δ) hnR.le
  have ht1 : (δ : Rat) / (n : Rat) ≤ 1 := by
    rw [div_le_one hnR]
    exact_mod_cast hδn.le
  have hceq : cutPoint sorted n true i =
      a * (1 - (δ : Rat) / (n : Rat)) + b * ((δ : Rat) / (n : Rat)) := by
    rw [hcut]
    field_simp [hnR.ne']
  rw [hceq]
  rcases le_total a b with hab | hab
  · constructor
    · refine ⟨a, ha_mem, ?_⟩
      have h : (0 : Rat) ≤ (b - a) * ((δ : Rat) / (n : Rat)) :=
        mul_nonneg (sub_nonneg.mpr hab) ht0
      linarith
    · refine ⟨b, hb_mem, ?_⟩
      have h : (0 : Rat) ≤ (b - a) * (1 - (δ : Rat) / (n : Rat)) :=
        mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht1)
      linarith
  · constructor
    · refine ⟨b, hb_mem, ?_⟩
      have h : (0 : Rat) ≤ (a - b) * (1 - (δ : Rat) / (n : Rat)) :=
        mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht1)
      linarith
    · refine ⟨a, ha_mem, ?_⟩
      have h : (0 : Rat) ≤ (a - b) * ((δ : Rat) / (n : Rat)) :=
        mul_nonneg (sub_nonneg.mpr hab) ht0
      linarith

/-! ## Post-condition -/

/-- Post-condition: conjunction of the stated properties, together with the
guarantee that the checked entry point succeeds and returns `quantiles`. -/
def Post_prop (data : List Rat) (n : Nat) (method : String) : Prop :=
  quantiles_length_prop data n (method == "inclusive") ∧
  (method = "inclusive" → quantiles_inclusive_bounds_prop data n) ∧
  benchmarkQuantiles data n method = .ok (quantiles data n (method == "inclusive"))

/-! ## Property-based tests -/

/-- Executable (Boolean) form of the length property. -/
def lengthCheck (data : List Rat) (n : Nat) (inclusive : Bool) : Bool :=
  (quantiles data n inclusive).length == n - 1

/-- Executable (Boolean) form of the inclusive-bounds property. -/
def boundsCheck (data : List Rat) (n : Nat) : Bool :=
  (quantiles data n true).all fun c =>
    (data.any fun lo => decide (lo ≤ c)) && (data.any fun hi => decide (c ≤ hi))

/-- Executable (Boolean) form of the pre-condition, used to restrict PBTs to
admissible inputs. -/
def preCheck (data : List Rat) (n : Nat) (method : String) : Bool :=
  decide (2 ≤ data.length) && decide (1 ≤ n) &&
    (method == "exclusive" || method == "inclusive")

/-- Executable (Boolean) form of the post-condition. -/
def postCheck (data : List Rat) (n : Nat) (method : String) : Bool :=
  let incl := method == "inclusive"
  lengthCheck data n incl &&
    (if incl then boundsCheck data n else true) &&
    (match benchmarkQuantiles data n method with
     | .ok r => decide (r = quantiles data n incl)
     | .error _ => false)

-- PBT (length property): bounded-exhaustive over small inputs
example : ([([1, 2, 3, 4] : List Rat), [5, 1, 4, 2, 3], [7, 7],
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]].all fun d =>
    ((List.range 8).all fun n =>
      ([true, false].all fun incl => lengthCheck d n incl))) = true := by
  native_decide

-- PBT (n = 1 property): bounded-exhaustive
example : ([([1, 2] : List Rat), [3, 1, 2], [9, 9, 9, 9]].all fun d =>
    ([true, false].all fun incl => (quantiles d 1 incl).isEmpty)) = true := by
  native_decide

-- PBT (inclusive-bounds property): bounded-exhaustive
example : ([([1, 2, 3, 4] : List Rat), [10, 3, 7, 1, 5], [2, 9], [8, 8, 8]].all fun d =>
    ((List.range' 1 9).all fun n => boundsCheck d n)) = true := by
  native_decide

-- PBT (post-condition): bounded-exhaustive, restricted to admissible inputs
example : ([([1, 2, 3, 4] : List Rat), [10, 3, 7, 1, 5], [2, 9]].all fun d =>
    ((List.range 9).all fun n =>
      ((["exclusive", "inclusive", "bogus"] : List String).all fun m =>
        if preCheck d n m then postCheck d n m else true))) = true := by
  native_decide

/-! ## Correctness theorem: `Pre → Post` -/

theorem quantiles_correct_thm (data : List Rat) (n : Nat) (method : String)
    (hpre : Pre data n method) : Post_prop data n method := by
  obtain ⟨hlen, hn, hm⟩ := hpre
  refine ⟨quantiles_length_thm data n _, fun hincl => ?_, ?_⟩
  · subst hincl
    exact quantiles_inclusive_bounds_thm data n hlen hn
  · have h1 : ¬ data.length < 2 := not_lt.mpr hlen
    have h2 : ¬ n < 1 := not_lt.mpr hn
    have h3 : (method == "exclusive" || method == "inclusive") = true := by
      rcases hm with rfl | rfl <;> rfl
    simp [benchmarkQuantiles, h1, h2, h3]

/-! ## Imperative implementation -/

/-- The `Id` monad is the identity, so its `pure`/`bind`/`run` collapse
(definitionally) to the identity. -/
@[simp] theorem id_pure_eq (x : α) : (pure x : Id α) = x := rfl
@[simp] theorem id_bind_eq (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl
@[simp] theorem id_run_eq (x : Id α) : Id.run x = x := rfl

/-- Loop worker for the imperative implementation: pushes the cut points for
indices `i, i + 1, …, i + fuel - 1` onto the accumulator. -/
def quantilesLoop (sorted : List Rat) (n : Nat) (inclusive : Bool) :
    Nat → Nat → Array Rat → Array Rat
  | 0, _, acc => acc
  | fuel + 1, i, acc =>
      quantilesLoop sorted n inclusive fuel (i + 1) (acc.push (cutPoint sorted n inclusive i))

/-- Imperative implementation using `Id.run` with mutable state: the data is
sorted once, then the cut points are accumulated into a mutable array. -/
def quantilesImperative (data : List Rat) (n : Nat) (inclusive : Bool) : List Rat := Id.run do
  let sorted := sortRat data
  let mut result : Array Rat := #[]
  result := quantilesLoop sorted n inclusive (n - 1) 1 result
  return result.toList

/-! ## Imperative tests -/

example : quantilesImperative ([1, 2, 3, 4] : List Rat) 4 false = [5/4, 5/2, 15/4] := by
  native_decide

example : quantilesImperative ([1, 2, 3, 4] : List Rat) 4 true = [7/4, 5/2, 13/4] := by
  native_decide

example : quantilesImperative ([1, 2, 3, 4, 5] : List Rat) 2 false = [3] := by
  native_decide

example : (quantilesImperative ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List Rat) 10 false).length
    = 9 := by
  native_decide

#eval quantilesImperative ([1, 2, 3, 4] : List Rat) 4 false

/-! ## Equivalence of the functional and imperative implementations -/

theorem quantilesLoop_toList (sorted : List Rat) (n : Nat) (inclusive : Bool)
    (fuel i : Nat) (acc : Array Rat) :
    (quantilesLoop sorted n inclusive fuel i acc).toList =
      acc.toList ++ (List.range' i fuel).map (cutPoint sorted n inclusive) := by
  induction fuel generalizing i acc with
  | zero => simp [quantilesLoop]
  | succ fuel ih =>
      simp [quantilesLoop, ih, Array.toList_push, List.range'_succ, List.map_cons,
        List.append_assoc]

/-- Equivalence property: the imperative implementation returns exactly the
functional one. -/
def quantiles_equiv_prop (data : List Rat) (n : Nat) (inclusive : Bool) : Prop :=
  quantilesImperative data n inclusive = quantiles data n inclusive

theorem quantiles_equiv_thm (data : List Rat) (n : Nat) (inclusive : Bool) :
    quantiles_equiv_prop data n inclusive := by
  unfold quantiles_equiv_prop quantilesImperative quantiles
  show (quantilesLoop (sortRat data) n inclusive (n - 1) 1 #[]).toList =
    (List.range' 1 (n - 1)).map (cutPoint (sortRat data) n inclusive)
  rw [quantilesLoop_toList]
  simp

-- PBT (equivalence property): bounded-exhaustive over small inputs
example : ([([1, 2, 3, 4] : List Rat), [10, 3, 7, 1, 5], [2, 9]].all fun d =>
    ((List.range 8).all fun n =>
      ([true, false].all fun incl =>
        decide (quantilesImperative d n incl = quantiles d n incl)))) = true := by
  native_decide

end «31_statistics_quantiles»
