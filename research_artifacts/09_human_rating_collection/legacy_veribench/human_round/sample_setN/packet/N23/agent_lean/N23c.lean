import Mathlib

/-!
# Quantiles -- translation of Python's `statistics.quantiles`

`benchmark_quantiles(data, n=4, method='exclusive')` divides `data` into `n`
continuous intervals with equal probability and returns the `n - 1` cut points,
linearly interpolated between the *sorted* data points.  Two methods exist:

* `"exclusive"` (default): `m = len(data) + 1`, `j = clamp(i*m // n, 1, len-1)`,
  `delta = i*m - j*n`, cut `= (data[j-1]*(n-delta) + data[j]*delta) / n`;
* `"inclusive"`: `m = len(data) - 1`, `j, delta = divmod(i*m, n)`,
  cut `= (data[j]*(n-delta) + data[j+1]*delta) / n`.

Invalid inputs (fewer than two data points, `n < 1`, or an unknown method) raise
`StatisticsError`; this is modelled by `Except.error`.

Numeric modelling: the main (exact) model uses `Rat` for the data values, so every
property is proved exactly with Mathlib.  A small `FloatLayer` mirrors the Python
floating-point execution for ground tests only.
-/

deriving instance DecidableEq for Except

namespace «31_statistics_quantiles»

/-- Message of the `StatisticsError` raised by `benchmark_quantiles`. -/
def statisticsError : String :=
  "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"

/-! ## Functional implementation (exact `Rat` model) -/

/-- Python `sorted(data)`: the data in non-decreasing order. -/
def sortData (data : List Rat) : List Rat := List.insertionSort (· ≤ ·) data

/-- Python `j = 1 if j < 1 else ld-1 if j > ld-1 else j`. -/
def clampIdx (ld j : Nat) : Nat :=
  if j < 1 then 1 else if j > ld - 1 then ld - 1 else j

/-- Linear interpolation `(a * (n - d) + b * d) / n` (used in specifications). -/
def lerp (a b d n : Rat) : Rat := (a * (n - d) + b * d) / n

/-- Cut point number `i` (`1 ≤ i < n`) of the inclusive method, on sorted data. -/
def inclusiveCut (sorted : List Rat) (n i : Nat) : Rat :=
  let m := sorted.length - 1
  let j := i * m / n
  let delta := i * m % n
  (sorted.getD j 0 * ((n : Rat) - (delta : Rat)) + sorted.getD (j + 1) 0 * (delta : Rat)) / (n : Rat)

/-- Cut point number `i` (`1 ≤ i < n`) of the exclusive method, on sorted data. -/
def exclusiveCut (sorted : List Rat) (n i : Nat) : Rat :=
  let ld := sorted.length
  let m := ld + 1
  let j := clampIdx ld (i * m / n)
  let delta : Int := ((i * m : Nat) : Int) - ((j * n : Nat) : Int)
  (sorted.getD (j - 1) 0 * ((n : Rat) - (delta : Rat)) + sorted.getD j 0 * (delta : Rat)) / (n : Rat)

/-- Python `quantiles(data, n, method)` on valid inputs: the `n - 1` cut points. -/
def quantilesCore (data : List Rat) (n : Nat) (method : String) : List Rat :=
  let sorted := sortData data
  if method = "inclusive" then
    (List.range' 1 (n - 1)).map (inclusiveCut sorted n)
  else
    (List.range' 1 (n - 1)).map (exclusiveCut sorted n)

/-- Executable form of Python `pre(data, n, method)`. -/
def validInputs (data : List Rat) (n : Int) (method : String) : Bool :=
  decide (2 ≤ data.length) && decide (1 ≤ n) && (method == "inclusive" || method == "exclusive")

/-- Python `benchmark_quantiles(data, n, method)`: `StatisticsError` is `Except.error`. -/
def benchmarkQuantiles (data : List Rat) (n : Int) (method : String) :
    Except String (List Rat) :=
  if validInputs data n method then .ok (quantilesCore data n.toNat method)
  else .error statisticsError

/-! ## Float layer (mirrors the Python floating-point execution; tests only)

Primitive `Float` arithmetic is opaque to the kernel, so no theorems are stated about this
layer; the properties, correctness and equivalence theorems below are stated and proved for the
exact `Rat` model, which is the mathematical intent of the Python program (linear interpolation
between sorted data points). -/

namespace FloatLayer

def sortData (data : List Float) : List Float := List.insertionSort (· ≤ ·) data

def inclusiveCut (sorted : List Float) (n i : Nat) : Float :=
  let m := sorted.length - 1
  let j := i * m / n
  let delta := i * m % n
  (sorted.getD j 0 * (n.toFloat - delta.toFloat) + sorted.getD (j + 1) 0 * delta.toFloat) / n.toFloat

def exclusiveCut (sorted : List Float) (n i : Nat) : Float :=
  let ld := sorted.length
  let m := ld + 1
  let j := clampIdx ld (i * m / n)
  let delta : Int := ((i * m : Nat) : Int) - ((j * n : Nat) : Int)
  (sorted.getD (j - 1) 0 * (n.toFloat - Float.ofInt delta) + sorted.getD j 0 * Float.ofInt delta) / n.toFloat

def quantilesCore (data : List Float) (n : Nat) (method : String) : List Float :=
  let sorted := sortData data
  if method = "inclusive" then
    (List.range' 1 (n - 1)).map (inclusiveCut sorted n)
  else
    (List.range' 1 (n - 1)).map (exclusiveCut sorted n)

def validInputs (data : List Float) (n : Int) (method : String) : Bool :=
  decide (2 ≤ data.length) && decide (1 ≤ n) && (method == "inclusive" || method == "exclusive")

def benchmarkQuantiles (data : List Float) (n : Int) (method : String) :
    Except String (List Float) :=
  if validInputs data n method then .ok (quantilesCore data n.toNat method)
  else .error statisticsError

/-- `abs(result[i] - expected) < 1e-9` for all `i`, as in the Python tests. -/
def approxEq (res : Except String (List Float)) (expected : List Float) : Bool :=
  match res with
  | .ok r => r.length == expected.length && (r.zip expected).all (fun p => (p.1 - p.2).abs < 1e-9)
  | .error _ => false

end FloatLayer

/-! ## Unit tests (from the Python `check`) -/

-- 1. Basic quartiles
example : benchmarkQuantiles [1, 2, 3, 4] 4 "exclusive" = .ok [5/4, 5/2, 15/4] := by native_decide
#eval benchmarkQuantiles [1, 2, 3, 4] 4 "exclusive"
-- 2. Deciles
example : (benchmarkQuantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 "exclusive").map List.length
    = .ok 9 := by native_decide
-- 3. Median (n = 2)
example : benchmarkQuantiles [1, 2, 3, 4, 5] 2 "exclusive" = .ok [3] := by native_decide
-- 4. Inclusive method
example : benchmarkQuantiles [1, 2, 3, 4] 4 "inclusive" = .ok [7/4, 5/2, 13/4] := by native_decide
-- 5. Exclusive method (default)
example : (benchmarkQuantiles [1, 2, 3, 4] 4 "exclusive").map List.length = .ok 3 := by native_decide
-- 6. Larger dataset
example : (benchmarkQuantiles ((List.range' 1 10).map (fun k => (k : Rat))) 4 "exclusive").map List.length
    = .ok 3 := by native_decide
example : benchmarkQuantiles ((List.range' 1 10).map (fun k => (k : Rat))) 4 "exclusive"
    = .ok [11/4, 11/2, 33/4] := by native_decide
-- 7. Unsorted input
example : benchmarkQuantiles [4, 1, 3, 2] 4 "exclusive" = .ok [5/4, 5/2, 15/4] := by native_decide
-- 8. Float data (exactly representable, modelled by rationals)
example : benchmarkQuantiles [3/2, 5/2, 7/2, 9/2] 2 "exclusive" = .ok [3] := by native_decide
-- 9. Error cases
example : benchmarkQuantiles [1] 4 "exclusive" = .error statisticsError := by native_decide
example : benchmarkQuantiles [1, 2] 0 "exclusive" = .error statisticsError := by native_decide
example : benchmarkQuantiles [1, 2] (-3) "exclusive" = .error statisticsError := by native_decide
example : benchmarkQuantiles [1, 2, 3] 4 "invalid" = .error statisticsError := by native_decide
-- extrapolation below the minimum is allowed by the exclusive method: quantiles([1, 2]) = [0.75, 1.5, 2.25]
example : benchmarkQuantiles [1, 2] 4 "exclusive" = .ok [3/4, 3/2, 9/4] := by native_decide

-- Float layer ground tests
#eval FloatLayer.benchmarkQuantiles [1, 2, 3, 4] 4 "exclusive"
example : FloatLayer.approxEq (FloatLayer.benchmarkQuantiles [1, 2, 3, 4] 4 "exclusive")
    [1.25, 2.5, 3.75] = true := by native_decide
example : FloatLayer.approxEq (FloatLayer.benchmarkQuantiles [1, 2, 3, 4] 4 "inclusive")
    [1.75, 2.5, 3.25] = true := by native_decide
example : FloatLayer.approxEq (FloatLayer.benchmarkQuantiles [1, 2, 3, 4, 5] 2 "exclusive") [3.0] = true := by
  native_decide
example : FloatLayer.approxEq (FloatLayer.benchmarkQuantiles [1.5, 2.5, 3.5, 4.5] 2 "exclusive") [3.0] = true := by
  native_decide
example : (FloatLayer.benchmarkQuantiles [1.0] 4 "exclusive").toOption.isNone = true := by native_decide

/-! ## Pre-condition -/

/-- Python `pre(data, n, method)`: at least two data points, `n ≥ 1`, known method. -/
def Pre (data : List Rat) (n : Int) (method : String) : Prop :=
  2 ≤ data.length ∧ 1 ≤ n ∧ (method = "inclusive" ∨ method = "exclusive")

instance (data : List Rat) (n : Int) (method : String) : Decidable (Pre data n method) := by
  unfold Pre; infer_instance

theorem validInputs_iff (data : List Rat) (n : Int) (method : String) :
    validInputs data n method = true ↔ Pre data n method := by
  simp [validInputs, Pre, and_assoc]

theorem benchmarkQuantiles_of_pre {data : List Rat} {n : Int} {method : String} (h : Pre data n method) :
    benchmarkQuantiles data n method = .ok (quantilesCore data n.toNat method) := by
  unfold benchmarkQuantiles
  rw [if_pos ((validInputs_iff data n method).2 h)]

theorem benchmarkQuantiles_of_not_pre {data : List Rat} {n : Int} {method : String}
    (h : ¬ Pre data n method) : benchmarkQuantiles data n method = .error statisticsError := by
  unfold benchmarkQuantiles
  rw [if_neg (fun hv => h ((validInputs_iff data n method).1 hv))]


/-! ## Helper lemmas -/

theorem sortData_pairwise (data : List Rat) : (sortData data).Pairwise (· ≤ ·) :=
  List.sorted_insertionSort _ data

theorem sortData_perm (data : List Rat) : (sortData data).Perm data :=
  List.perm_insertionSort _ data

theorem sortData_length (data : List Rat) : (sortData data).length = data.length :=
  List.length_insertionSort _ data

theorem sortData_eq_of_perm {data data' : List Rat} (h : data.Perm data') :
    sortData data = sortData data' :=
  List.eq_of_perm_of_sorted ((sortData_perm data).trans (h.trans (sortData_perm data').symm))
    (List.sorted_insertionSort _ data) (List.sorted_insertionSort _ data')

theorem getD_mono_of_pairwise {s : List Rat} (hs : s.Pairwise (· ≤ ·)) {a b : Nat} (hab : a ≤ b)
    (hb : b < s.length) : s.getD a 0 ≤ s.getD b 0 := by
  rw [List.getD_eq_getElem _ _ (lt_of_le_of_lt hab hb), List.getD_eq_getElem _ _ hb]
  rcases Nat.lt_or_eq_of_le hab with h | h
  · exact List.pairwise_iff_getElem.1 hs a b _ hb h
  · subst h; exact le_rfl

theorem getD_mem {s : List Rat} {a : Nat} (ha : a < s.length) : s.getD a 0 ∈ s := by
  rw [List.getD_eq_getElem _ _ ha]; exact List.getElem_mem ha

theorem lerp_le_right {a b d n : Rat} (hab : a ≤ b) (hn : 0 < n) (hd : d ≤ n) : lerp a b d n ≤ b := by
  unfold lerp
  rw [div_le_iff₀ hn]
  nlinarith

theorem le_lerp_left {a b d n : Rat} (hab : a ≤ b) (hn : 0 < n) (hd : 0 ≤ d) : a ≤ lerp a b d n := by
  unfold lerp
  rw [le_div_iff₀ hn]
  nlinarith

theorem lerp_mono {a b d d' n : Rat} (hab : a ≤ b) (hn : 0 < n) (hd : d ≤ d') :
    lerp a b d n ≤ lerp a b d' n := by
  unfold lerp
  apply div_le_div_of_nonneg_right _ hn.le
  nlinarith

theorem exclusiveCut_eq (s : List Rat) (n i : Nat) :
    exclusiveCut s n i =
      lerp (s.getD (clampIdx s.length (i * (s.length + 1) / n) - 1) 0)
        (s.getD (clampIdx s.length (i * (s.length + 1) / n)) 0)
        ((((i * (s.length + 1) : Nat) : Int) -
          ((clampIdx s.length (i * (s.length + 1) / n) * n : Nat) : Int) : Int) : Rat) n := rfl

theorem inclusiveCut_eq (s : List Rat) (n i : Nat) :
    inclusiveCut s n i =
      lerp (s.getD (i * (s.length - 1) / n) 0) (s.getD (i * (s.length - 1) / n + 1) 0)
        ((i * (s.length - 1) % n : Nat) : Rat) n := rfl

theorem clampIdx_pos {ld : Nat} (h : 2 ≤ ld) (j : Nat) : 1 ≤ clampIdx ld j := by
  unfold clampIdx; split_ifs <;> omega

theorem clampIdx_le {ld : Nat} (h : 2 ≤ ld) (j : Nat) : clampIdx ld j ≤ ld - 1 := by
  unfold clampIdx; split_ifs <;> omega

theorem clampIdx_mono {ld j j' : Nat} (hld : 2 ≤ ld) (h : j ≤ j') :
    clampIdx ld j ≤ clampIdx ld j' := by
  unfold clampIdx; split_ifs <;> omega

theorem clampIdx_lt {ld j j' : Nat} (hld : 2 ≤ ld) (h : clampIdx ld j < clampIdx ld j') :
    j ≤ clampIdx ld j ∧ clampIdx ld j' ≤ j' := by
  unfold clampIdx at h ⊢
  by_cases h1 : j < 1 <;> by_cases h2 : j > ld - 1 <;> by_cases h3 : j' < 1 <;>
    by_cases h4 : j' > ld - 1 <;> simp only [h1, h2, h3, h4, if_true, if_false] at h ⊢ <;> omega

/-- Monotonicity of the exclusive interpolation in the scaled position `q = i * m`. -/
theorem exclusiveAt_mono {s : List Rat} (hs : s.Pairwise (· ≤ ·)) (hlen : 2 ≤ s.length) {n : Nat}
    (hn : 0 < n) {q q' : Nat} (hq : q ≤ q') :
    lerp (s.getD (clampIdx s.length (q / n) - 1) 0) (s.getD (clampIdx s.length (q / n)) 0)
        ((((q : Nat) : Int) - ((clampIdx s.length (q / n) * n : Nat) : Int) : Int) : Rat) n
      ≤ lerp (s.getD (clampIdx s.length (q' / n) - 1) 0) (s.getD (clampIdx s.length (q' / n)) 0)
        ((((q' : Nat) : Int) - ((clampIdx s.length (q' / n) * n : Nat) : Int) : Int) : Rat) n := by
  have hnR : (0 : Rat) < n := by exact_mod_cast hn
  have hdiv : q / n ≤ q' / n := Nat.div_le_div_right hq
  have hq1 : q < q / n * n + n := Nat.lt_div_mul_add hn
  have hq2 : q' / n * n ≤ q' := Nat.div_mul_le_self q' n
  have hj1 : 1 ≤ clampIdx s.length (q / n) := clampIdx_pos hlen _
  have hj1' : 1 ≤ clampIdx s.length (q' / n) := clampIdx_pos hlen _
  have hjle : clampIdx s.length (q / n) ≤ s.length - 1 := clampIdx_le hlen _
  have hjle' : clampIdx s.length (q' / n) ≤ s.length - 1 := clampIdx_le hlen _
  have hjj : clampIdx s.length (q / n) ≤ clampIdx s.length (q' / n) := clampIdx_mono hlen hdiv
  rcases Nat.lt_or_eq_of_le hjj with hlt | heq
  · obtain ⟨hA, hB⟩ := clampIdx_lt hlen hlt
    generalize clampIdx s.length (q / n) = j at *
    generalize clampIdx s.length (q' / n) = j' at *
    have hjn : q / n * n ≤ j * n := Nat.mul_le_mul_right n hA
    have hjn' : j' * n ≤ q' / n * n := Nat.mul_le_mul_right n hB
    have hab : s.getD (j - 1) 0 ≤ s.getD j 0 := getD_mono_of_pairwise hs (Nat.sub_le j 1) (by omega)
    have hab' : s.getD (j' - 1) 0 ≤ s.getD j' 0 := getD_mono_of_pairwise hs (Nat.sub_le j' 1) (by omega)
    have hmid : s.getD j 0 ≤ s.getD (j' - 1) 0 := getD_mono_of_pairwise hs (by omega) (by omega)
    have hd : ((((q : Nat) : Int) - ((j * n : Nat) : Int) : Int) : Rat) ≤ (n : Rat) := by
      have : ((q : Nat) : Int) - ((j * n : Nat) : Int) ≤ (n : Int) := by omega
      exact_mod_cast this
    have hd' : (0 : Rat) ≤ ((((q' : Nat) : Int) - ((j' * n : Nat) : Int) : Int) : Rat) := by
      have : (0 : Int) ≤ ((q' : Nat) : Int) - ((j' * n : Nat) : Int) := by omega
      exact_mod_cast this
    calc _ ≤ s.getD j 0 := lerp_le_right hab hnR hd
      _ ≤ s.getD (j' - 1) 0 := hmid
      _ ≤ _ := le_lerp_left hab' hnR hd'
  · generalize clampIdx s.length (q / n) = j at *
    rw [← heq]
    have hab : s.getD (j - 1) 0 ≤ s.getD j 0 := getD_mono_of_pairwise hs (Nat.sub_le j 1) (by omega)
    apply lerp_mono hab hnR
    have : ((q : Nat) : Int) - ((j * n : Nat) : Int) ≤ ((q' : Nat) : Int) - ((j * n : Nat) : Int) := by
      omega
    exact_mod_cast this

theorem exclusiveCut_mono {s : List Rat} (hs : s.Pairwise (· ≤ ·)) (hlen : 2 ≤ s.length) {n : Nat}
    (hn : 0 < n) (i : Nat) : exclusiveCut s n i ≤ exclusiveCut s n (i + 1) := by
  rw [exclusiveCut_eq, exclusiveCut_eq]
  exact exclusiveAt_mono hs hlen hn (Nat.mul_le_mul_right _ (Nat.le_succ i))

/-- Monotonicity of the inclusive interpolation in the scaled position `q = i * m`. -/
theorem inclusiveAt_mono {s : List Rat} (hs : s.Pairwise (· ≤ ·)) {n : Nat} (hn : 0 < n)
    {q q' : Nat} (hq : q ≤ q') (hq' : q' / n + 1 < s.length) :
    lerp (s.getD (q / n) 0) (s.getD (q / n + 1) 0) ((q % n : Nat) : Rat) n
      ≤ lerp (s.getD (q' / n) 0) (s.getD (q' / n + 1) 0) ((q' % n : Nat) : Rat) n := by
  have hnR : (0 : Rat) < n := by exact_mod_cast hn
  have hdiv : q / n ≤ q' / n := Nat.div_le_div_right hq
  have h1 := Nat.div_add_mod q n
  have h2 := Nat.div_add_mod q' n
  have hm : q % n < n := Nat.mod_lt q hn
  rcases Nat.lt_or_eq_of_le hdiv with hlt | heq
  · have hab : s.getD (q / n) 0 ≤ s.getD (q / n + 1) 0 :=
      getD_mono_of_pairwise hs (Nat.le_succ _) (by omega)
    have hab' : s.getD (q' / n) 0 ≤ s.getD (q' / n + 1) 0 :=
      getD_mono_of_pairwise hs (Nat.le_succ _) hq'
    have hmid : s.getD (q / n + 1) 0 ≤ s.getD (q' / n) 0 := getD_mono_of_pairwise hs hlt (by omega)
    calc _ ≤ s.getD (q / n + 1) 0 := lerp_le_right hab hnR (by exact_mod_cast hm.le)
      _ ≤ s.getD (q' / n) 0 := hmid
      _ ≤ _ := le_lerp_left hab' hnR (by positivity)
  · have hab : s.getD (q / n) 0 ≤ s.getD (q / n + 1) 0 :=
      getD_mono_of_pairwise hs (Nat.le_succ _) (by omega)
    rw [← heq]
    apply lerp_mono hab hnR
    have : q % n ≤ q' % n := by
      rw [← heq] at h2
      omega
    exact_mod_cast this

theorem inclusiveCut_mono {s : List Rat} (hs : s.Pairwise (· ≤ ·)) (hlen : 2 ≤ s.length) {n : Nat}
    (hn : 0 < n) {i : Nat} (hi : i + 1 < n) : inclusiveCut s n i ≤ inclusiveCut s n (i + 1) := by
  rw [inclusiveCut_eq, inclusiveCut_eq]
  apply inclusiveAt_mono hs hn (Nat.mul_le_mul_right _ (Nat.le_add_right i 1))
  have hm : 0 < s.length - 1 := by omega
  have : (i + 1) * (s.length - 1) / n < s.length - 1 := by
    rw [Nat.div_lt_iff_lt_mul hn, Nat.mul_comm (s.length - 1) n]
    exact Nat.mul_lt_mul_of_pos_right hi hm
  omega

/-- A list `map f (range' a k)` is sorted as soon as adjacent values are ordered. -/
theorem pairwise_map_range' (f : Nat → Rat) :
    ∀ (k a : Nat), (∀ i, a ≤ i → i + 1 < a + k → f i ≤ f (i + 1)) →
      List.Pairwise (· ≤ ·) ((List.range' a k).map f)
  | 0, _, _ => by simp
  | 1, _, _ => by simp
  | k + 2, a, h => by
    rw [← List.chain'_iff_pairwise]
    rw [List.range'_succ, List.range'_succ, List.map_cons, List.map_cons, List.chain'_cons_cons]
    refine ⟨h a le_rfl (by omega), ?_⟩
    rw [List.chain'_iff_pairwise]
    have := pairwise_map_range' f (k + 1) (a + 1) (fun i hi hik => h i (by omega) (by omega))
    rw [List.range'_succ, List.map_cons] at this
    exact this

theorem quantilesCore_length (data : List Rat) (n : Nat) (method : String) :
    (quantilesCore data n method).length = n - 1 := by
  simp only [quantilesCore]
  split <;> simp

theorem quantilesCore_pairwise {data : List Rat} (hlen : 2 ≤ data.length) {n : Nat} (hn : 0 < n)
    (method : String) : (quantilesCore data n method).Pairwise (· ≤ ·) := by
  have hs := sortData_pairwise data
  have hl : 2 ≤ (sortData data).length := by rw [sortData_length]; exact hlen
  simp only [quantilesCore]
  split
  · apply pairwise_map_range'
    intro i _ hik
    exact inclusiveCut_mono hs hl hn (by omega)
  · apply pairwise_map_range'
    intro i _ _
    exact exclusiveCut_mono hs hl hn i

theorem inclusiveCut_bounds {data : List Rat} (hlen : 2 ≤ data.length) {n i : Nat} (hi1 : 1 ≤ i)
    (hin : i < n) :
    (∃ a ∈ data, a ≤ inclusiveCut (sortData data) n i) ∧
      (∃ b ∈ data, inclusiveCut (sortData data) n i ≤ b) := by
  have hs := sortData_pairwise data
  have hl : (sortData data).length = data.length := sortData_length data
  have hp := sortData_perm data
  have hn : 0 < n := by omega
  have hnR : (0 : Rat) < n := by exact_mod_cast hn
  rw [inclusiveCut_eq]
  generalize sortData data = s at *
  have hm : 0 < s.length - 1 := by omega
  have hj : i * (s.length - 1) / n < s.length - 1 := by
    rw [Nat.div_lt_iff_lt_mul hn, Nat.mul_comm (s.length - 1) n]
    exact Nat.mul_lt_mul_of_pos_right hin hm
  have hab : s.getD (i * (s.length - 1) / n) 0 ≤ s.getD (i * (s.length - 1) / n + 1) 0 :=
    getD_mono_of_pairwise hs (Nat.le_succ _) (by omega)
  have hmod : ((i * (s.length - 1) % n : Nat) : Rat) ≤ n := by exact_mod_cast (Nat.mod_lt _ hn).le
  refine ⟨⟨s.getD (i * (s.length - 1) / n) 0, ?_, le_lerp_left hab hnR (by positivity)⟩,
    ⟨s.getD (i * (s.length - 1) / n + 1) 0, ?_, lerp_le_right hab hnR hmod⟩⟩
  · exact hp.mem_iff.1 (getD_mem (by omega))
  · exact hp.mem_iff.1 (getD_mem (by omega))

/-- The median of a sorted list: the middle element, or the mean of the two middle elements. -/
def median (s : List Rat) : Rat :=
  if s.length % 2 = 1 then s.getD (s.length / 2) 0
  else (s.getD (s.length / 2 - 1) 0 + s.getD (s.length / 2) 0) / 2

theorem exclusiveCut_two {s : List Rat} (hlen : 2 ≤ s.length) : exclusiveCut s 2 1 = median s := by
  rw [exclusiveCut_eq]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' s.length
  · have hj : clampIdx s.length (1 * (s.length + 1) / 2) = k := by
      unfold clampIdx; split_ifs <;> omega
    have hd : ((1 * (s.length + 1) : Nat) : Int) - ((k * 2 : Nat) : Int) = 1 := by omega
    rw [hj, hd]
    unfold median lerp
    rw [if_neg (by omega)]
    have h2 : s.length / 2 = k := by omega
    rw [h2]
    push_cast
    ring
  · have hj : clampIdx s.length (1 * (s.length + 1) / 2) = k + 1 := by
      unfold clampIdx; split_ifs <;> omega
    have hd : ((1 * (s.length + 1) : Nat) : Int) - (((k + 1) * 2 : Nat) : Int) = 0 := by omega
    rw [hj, hd]
    unfold median lerp
    rw [if_pos (by omega)]
    have h2 : s.length / 2 = k := by omega
    rw [h2, Nat.add_sub_cancel]
    push_cast
    ring

/-! ## Properties -/

/-- Valid inputs never raise: the result is `ok`. -/
def succeeds_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  ∃ r, benchmarkQuantiles data n method = .ok r

/-- Invalid inputs raise `StatisticsError`. -/
def fails_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  ¬ Pre data n method → benchmarkQuantiles data n method = .error statisticsError

/-- Exactly `n - 1` cut points are returned. -/
def length_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  ∀ r, benchmarkQuantiles data n method = .ok r → (r.length : Int) = n - 1

/-- The data is sorted internally: the result is invariant under permutations of the data. -/
def perm_invariant_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  ∀ data' : List Rat, data.Perm data' →
    benchmarkQuantiles data n method = benchmarkQuantiles data' n method

/-- Exclusive method: cut point `k` (0-based) is Python's interpolation formula for `i = k + 1`:
`m = ld + 1`, `j = clamp(i*m // n, 1, ld-1)`, `delta = i*m - j*n`,
`(sorted[j-1]*(n-delta) + sorted[j]*delta) / n`. -/
def exclusive_formula_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  method = "exclusive" → ∀ r, benchmarkQuantiles data n method = .ok r →
    ∀ k (hk : k < r.length), r[k] = exclusiveCut (sortData data) n.toNat (k + 1)

/-- Inclusive method: cut point `k` (0-based) is Python's interpolation formula for `i = k + 1`:
`m = ld - 1`, `j, delta = divmod(i*m, n)`, `(sorted[j]*(n-delta) + sorted[j+1]*delta) / n`. -/
def inclusive_formula_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  method = "inclusive" → ∀ r, benchmarkQuantiles data n method = .ok r →
    ∀ k (hk : k < r.length), r[k] = inclusiveCut (sortData data) n.toNat (k + 1)

/-- Inclusive method: every cut point lies between the minimum and the maximum of the data. -/
def inclusive_bounds_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  method = "inclusive" → ∀ r, benchmarkQuantiles data n method = .ok r →
    ∀ x ∈ r, (∃ a ∈ data, a ≤ x) ∧ (∃ b ∈ data, x ≤ b)

/-- The cut points are returned in non-decreasing order. -/
def sorted_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  ∀ r, benchmarkQuantiles data n method = .ok r → r.Sorted (· ≤ ·)

/-- `n = 2` with the exclusive method yields exactly the median of the data. -/
def median_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  n = 2 → method = "exclusive" → ∀ r, benchmarkQuantiles data n method = .ok r →
    r = [median (sortData data)]

/-! ## Theorems -/

theorem succeeds_thm (data : List Rat) (n : Int) (method : String) (h : Pre data n method) :
    succeeds_prop data n method :=
  ⟨_, benchmarkQuantiles_of_pre h⟩

theorem fails_thm (data : List Rat) (n : Int) (method : String) : fails_prop data n method :=
  fun h => benchmarkQuantiles_of_not_pre h

/-- The computation succeeds exactly on the inputs satisfying the pre-condition. -/
theorem ok_iff_pre_thm (data : List Rat) (n : Int) (method : String) :
    (∃ r, benchmarkQuantiles data n method = .ok r) ↔ Pre data n method := by
  constructor
  · rintro ⟨r, hr⟩
    by_contra hp
    rw [benchmarkQuantiles_of_not_pre hp] at hr
    cases hr
  · exact succeeds_thm data n method

theorem length_thm (data : List Rat) (n : Int) (method : String) (h : Pre data n method) :
    length_prop data n method := by
  intro r hr
  rw [benchmarkQuantiles_of_pre h] at hr
  have := Except.ok.inj hr
  subst this
  rw [quantilesCore_length]
  obtain ⟨_, hn, _⟩ := h
  omega

theorem perm_invariant_thm (data : List Rat) (n : Int) (method : String) :
    perm_invariant_prop data n method := by
  intro data' hp
  unfold benchmarkQuantiles validInputs quantilesCore
  rw [hp.length_eq, sortData_eq_of_perm hp]

theorem exclusive_formula_thm (data : List Rat) (n : Int) (method : String) (h : Pre data n method) :
    exclusive_formula_prop data n method := by
  intro hm r hr k hk
  subst hm
  rw [benchmarkQuantiles_of_pre h] at hr
  have := Except.ok.inj hr
  subst this
  have hne : ("exclusive" : String) ≠ "inclusive" := by decide
  simp only [quantilesCore, hne, ↓reduceIte, List.getElem_map, List.getElem_range']
  congr 1
  omega

theorem inclusive_formula_thm (data : List Rat) (n : Int) (method : String) (h : Pre data n method) :
    inclusive_formula_prop data n method := by
  intro hm r hr k hk
  subst hm
  rw [benchmarkQuantiles_of_pre h] at hr
  have := Except.ok.inj hr
  subst this
  simp only [quantilesCore, ↓reduceIte, List.getElem_map, List.getElem_range']
  congr 1
  omega

theorem inclusive_bounds_thm (data : List Rat) (n : Int) (method : String) (h : Pre data n method) :
    inclusive_bounds_prop data n method := by
  intro hm r hr x hx
  subst hm
  rw [benchmarkQuantiles_of_pre h] at hr
  have := Except.ok.inj hr
  subst this
  obtain ⟨hlen, hn, _⟩ := h
  simp only [quantilesCore, ↓reduceIte, List.mem_map, List.mem_range'_1] at hx
  obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hx
  exact inclusiveCut_bounds hlen hi1 (by omega)

theorem sorted_thm (data : List Rat) (n : Int) (method : String) (h : Pre data n method) :
    sorted_prop data n method := by
  intro r hr
  rw [benchmarkQuantiles_of_pre h] at hr
  have := Except.ok.inj hr
  subst this
  obtain ⟨hlen, hn, _⟩ := h
  exact quantilesCore_pairwise hlen (by omega) method

theorem median_thm (data : List Rat) (n : Int) (method : String) (h : Pre data n method) :
    median_prop data n method := by
  intro hn hm r hr
  subst hn hm
  rw [benchmarkQuantiles_of_pre h] at hr
  have := Except.ok.inj hr
  subst this
  obtain ⟨hlen, _, _⟩ := h
  have hne : ("exclusive" : String) ≠ "inclusive" := by decide
  have hl : 2 ≤ (sortData data).length := by rw [sortData_length]; exact hlen
  simp only [quantilesCore, hne, ↓reduceIte]
  show [exclusiveCut (sortData data) 2 1] = _
  rw [exclusiveCut_two hl]

/-! ## Post-condition -/

def Post_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  succeeds_prop data n method ∧ length_prop data n method ∧ perm_invariant_prop data n method ∧
  exclusive_formula_prop data n method ∧ inclusive_formula_prop data n method ∧
  inclusive_bounds_prop data n method ∧ sorted_prop data n method ∧ median_prop data n method

/-! ## Property-based tests -/

/-- Method string from a Boolean flag (to sample both methods randomly). -/
def methodOf (b : Bool) : String := if b then "inclusive" else "exclusive"

def succeedsCheck (data : List Rat) (n : Int) (method : String) : Bool :=
  (benchmarkQuantiles data n method).toOption.isSome

def failsCheck (data : List Rat) (n : Int) (method : String) : Bool :=
  validInputs data n method || benchmarkQuantiles data n method == .error statisticsError

def lengthCheck (data : List Rat) (n : Int) (method : String) : Bool :=
  match benchmarkQuantiles data n method with
  | .ok r => (r.length : Int) == n - 1
  | .error _ => true

def permCheck (data : List Rat) (n : Int) (method : String) : Bool :=
  benchmarkQuantiles data n method == benchmarkQuantiles data.reverse n method &&
  benchmarkQuantiles data n method == benchmarkQuantiles (data.rotate 1) n method

def exclusiveFormulaCheck (data : List Rat) (n : Int) : Bool :=
  match benchmarkQuantiles data n "exclusive" with
  | .ok r => (List.range r.length).all
      (fun k => r.getD k 0 == exclusiveCut (sortData data) n.toNat (k + 1))
  | .error _ => true

def inclusiveFormulaCheck (data : List Rat) (n : Int) : Bool :=
  match benchmarkQuantiles data n "inclusive" with
  | .ok r => (List.range r.length).all
      (fun k => r.getD k 0 == inclusiveCut (sortData data) n.toNat (k + 1))
  | .error _ => true

def inclusiveBoundsCheck (data : List Rat) (n : Int) : Bool :=
  match benchmarkQuantiles data n "inclusive" with
  | .ok r => r.all (fun x => data.any (· ≤ x) && data.any (x ≤ ·))
  | .error _ => true

def sortedCheck (data : List Rat) (n : Int) (method : String) : Bool :=
  match benchmarkQuantiles data n method with
  | .ok r => decide (r.Pairwise (· ≤ ·))
  | .error _ => true

def medianCheck (data : List Rat) : Bool :=
  benchmarkQuantiles data 2 "exclusive" == .ok [median (sortData data)]

/-- Executable form of `Post_prop` (for valid inputs). -/
def postCheck (data : List Rat) (n : Int) (method : String) : Bool :=
  succeedsCheck data n method && lengthCheck data n method && permCheck data n method &&
  (method != "exclusive" || exclusiveFormulaCheck data n) &&
  (method != "inclusive" || inclusiveFormulaCheck data n) &&
  (method != "inclusive" || inclusiveBoundsCheck data n) &&
  sortedCheck data n method &&
  (n != 2 || method != "exclusive" || medianCheck data)

-- succeeds_prop
#eval Plausible.Testable.check (∀ (data : List Rat) (x y : Rat) (n : Nat) (b : Bool),
  succeedsCheck (x :: y :: data) (n + 1) (methodOf b) = true)
-- fails_prop (arbitrary method strings, arbitrary integers)
#eval Plausible.Testable.check (∀ (data : List Rat) (n : Int) (s : String), failsCheck data n s = true)
#eval Plausible.Testable.check (∀ (data : List Rat) (n : Int) (b : Bool), failsCheck data n (methodOf b) = true)
-- length_prop
#eval Plausible.Testable.check (∀ (data : List Rat) (n : Int) (b : Bool), lengthCheck data n (methodOf b) = true)
-- perm_invariant_prop
#eval Plausible.Testable.check (∀ (data : List Rat) (n : Int) (b : Bool), permCheck data n (methodOf b) = true)
-- exclusive_formula_prop / inclusive_formula_prop
#eval Plausible.Testable.check (∀ (data : List Rat) (n : Int), exclusiveFormulaCheck data n = true)
#eval Plausible.Testable.check (∀ (data : List Rat) (n : Int), inclusiveFormulaCheck data n = true)
-- inclusive_bounds_prop
#eval Plausible.Testable.check (∀ (data : List Rat) (n : Int), inclusiveBoundsCheck data n = true)
-- sorted_prop
#eval Plausible.Testable.check (∀ (data : List Rat) (n : Int) (b : Bool), sortedCheck data n (methodOf b) = true)
-- median_prop
#eval Plausible.Testable.check (∀ (data : List Rat) (x y : Rat), medianCheck (x :: y :: data) = true)
-- Post_prop
#eval Plausible.Testable.check (∀ (data : List Rat) (x y : Rat) (n : Nat) (b : Bool),
  postCheck (x :: y :: data) (n + 1) (methodOf b) = true)
#eval Plausible.Testable.check (∀ (data : List Rat) (n : Int) (b : Bool),
  !(validInputs data n (methodOf b)) || postCheck data n (methodOf b) = true)

-- Bounded exhaustive checks on small integer data sets, both methods, n = 0 .. 11
def sampleData (len seed : Nat) : List Rat :=
  (List.range len).map (fun k => (((k * 7 + seed) % 5 : Nat) : Rat) - 2)

example : (List.range 12).all (fun n => (List.range 7).all (fun len => (List.range 3).all (fun seed =>
    !(validInputs (sampleData len seed) n "exclusive") || postCheck (sampleData len seed) n "exclusive")))
    = true := by native_decide
example : (List.range 12).all (fun n => (List.range 7).all (fun len => (List.range 3).all (fun seed =>
    !(validInputs (sampleData len seed) n "inclusive") || postCheck (sampleData len seed) n "inclusive")))
    = true := by native_decide
example : (List.range 12).all (fun n => (List.range 4).all (fun len =>
    failsCheck (sampleData len 0) n "exclusive" && failsCheck (sampleData len 0) n "other")) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem correctness_thm (data : List Rat) (n : Int) (method : String) :
    Pre data n method → Post_prop data n method := fun h =>
  ⟨succeeds_thm data n method h, length_thm data n method h, perm_invariant_thm data n method,
   exclusive_formula_thm data n method h, inclusive_formula_thm data n method h,
   inclusive_bounds_thm data n method h, sorted_thm data n method h, median_thm data n method h⟩

/-! ## Imperative implementation -/

/-- Imperative version of Python `quantiles` (loops with mutable state). -/
def quantilesCoreImp (data : List Rat) (n : Nat) (method : String) : List Rat := Id.run do
  let sorted := sortData data
  let ld := sorted.length
  let mut result : List Rat := []
  if method = "inclusive" then
    let m := ld - 1
    for i in [1:n] do
      let j := i * m / n
      let delta := i * m % n
      let interpolated :=
        (sorted.getD j 0 * ((n : Rat) - (delta : Rat)) + sorted.getD (j + 1) 0 * (delta : Rat)) / (n : Rat)
      result := result ++ [interpolated]
  else
    let m := ld + 1
    for i in [1:n] do
      let mut j := i * m / n
      if j < 1 then
        j := 1
      else if j > ld - 1 then
        j := ld - 1
      let delta : Int := ((i * m : Nat) : Int) - ((j * n : Nat) : Int)
      let interpolated :=
        (sorted.getD (j - 1) 0 * ((n : Rat) - (delta : Rat)) + sorted.getD j 0 * (delta : Rat)) / (n : Rat)
      result := result ++ [interpolated]
  return result

/-- Imperative version of Python `benchmark_quantiles`. -/
def benchmarkQuantilesImp (data : List Rat) (n : Int) (method : String) :
    Except String (List Rat) := Id.run do
  if !(validInputs data n method) then
    return .error statisticsError
  return .ok (quantilesCoreImp data n.toNat method)

/-! ## Imperative tests -/

example : benchmarkQuantilesImp [1, 2, 3, 4] 4 "exclusive" = .ok [5/4, 5/2, 15/4] := by native_decide
#eval benchmarkQuantilesImp [1, 2, 3, 4] 4 "exclusive"
example : (benchmarkQuantilesImp [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 "exclusive").map List.length
    = .ok 9 := by native_decide
example : benchmarkQuantilesImp [1, 2, 3, 4, 5] 2 "exclusive" = .ok [3] := by native_decide
example : benchmarkQuantilesImp [1, 2, 3, 4] 4 "inclusive" = .ok [7/4, 5/2, 13/4] := by native_decide
example : benchmarkQuantilesImp [4, 1, 3, 2] 4 "exclusive" = .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmarkQuantilesImp [3/2, 5/2, 7/2, 9/2] 2 "exclusive" = .ok [3] := by native_decide
example : benchmarkQuantilesImp [1] 4 "exclusive" = .error statisticsError := by native_decide
example : benchmarkQuantilesImp [1, 2] 0 "exclusive" = .error statisticsError := by native_decide
example : benchmarkQuantilesImp [1, 2, 3] 4 "invalid" = .error statisticsError := by native_decide
example : benchmarkQuantilesImp [1, 2] 4 "exclusive" = .ok [3/4, 3/2, 9/4] := by native_decide
-- functional and imperative agree on random inputs
#eval Plausible.Testable.check (∀ (data : List Rat) (n : Int) (b : Bool),
  (benchmarkQuantiles data n (methodOf b) == benchmarkQuantilesImp data n (methodOf b)) = true)

/-! ## Equivalence: functional = imperative -/

theorem forIn_yield_append {β : Type} (f : Nat → β) (g : Nat → List β → Id (ForInStep (List β)))
    (hg : ∀ i r, g i r = pure (ForInStep.yield (r ++ [f i]))) :
    ∀ (l : List Nat) (acc : List β), forIn l acc g = (pure (acc ++ l.map f) : Id (List β))
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.forIn_cons, hg]
    simp only [pure_bind]
    rw [forIn_yield_append f g hg xs (acc ++ [f x])]
    simp

theorem quantilesCoreImp_eq (data : List Rat) (n : Nat) (method : String) :
    quantilesCoreImp data n method = quantilesCore data n method := by
  unfold quantilesCoreImp quantilesCore
  by_cases hm : method = "inclusive"
  · simp only [hm, ↓reduceIte, Std.Range.forIn_eq_forIn_range', Std.Range.size]
    rw [forIn_yield_append (f := inclusiveCut (sortData data) n)]
    · simp
    · intro i r
      rfl
  · simp only [hm, ↓reduceIte, Std.Range.forIn_eq_forIn_range', Std.Range.size]
    rw [forIn_yield_append (f := exclusiveCut (sortData data) n)]
    · simp
    · intro i r
      simp only [exclusiveCut, clampIdx]
      split_ifs <;> rfl

theorem equivalence_thm (data : List Rat) (n : Int) (method : String) :
    benchmarkQuantiles data n method = benchmarkQuantilesImp data n method := by
  unfold benchmarkQuantiles benchmarkQuantilesImp
  by_cases hv : validInputs data n method = true
  · simp [hv, quantilesCoreImp_eq]
  · simp [hv]

end «31_statistics_quantiles»
