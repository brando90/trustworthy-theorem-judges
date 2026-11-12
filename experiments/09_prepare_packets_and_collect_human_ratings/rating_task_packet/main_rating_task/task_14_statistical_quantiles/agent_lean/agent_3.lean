import Mathlib

/-!
# Statistics quantiles

Translation of Python's `quantiles` and checked `benchmark_quantiles`.
Lists represent the accepted list/tuple sequences; `Int` represents Python's
integer parameter and strings retain invalid method names. Dynamic non-sequence
and non-integer arguments are excluded by these static argument types.

`Rat` is the exact mathematical numeric layer, representing integers, fractions,
and the exact values of finite decimal and binary floating-point inputs.
`FloatLayer` executes the same control flow with primitive floating-point
arithmetic (including its special values). Exact rational arithmetic theorems
are not assertions of IEEE or Decimal-context rounding equivalence. The shared structural and
functional/imperative proofs apply to both layers without a finiteness premise.

In particular, exclusive interpolation uses *signed* integer weights: for small
samples its cuts can lie outside the sample's minimum and maximum.
-/

namespace StatisticsQuantiles

inductive QuantileError where
  | statisticsError (message : String)
  | valueError (message : String)
  deriving Repr, DecidableEq, BEq

deriving instance DecidableEq, BEq for Except

def preMessage : String :=
  "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"

def validMethod (method : String) : Bool :=
  method == "inclusive" || method == "exclusive"

def preCheck (data : List α) (n : Int) (method : String) : Bool :=
  decide (2 ≤ data.length) && decide (1 ≤ n) && validMethod method

/-- The operations that vary between exact arithmetic and primitive floats. -/
structure NumericOps (α : Type) where
  zero : α
  le : α → α → Bool
  interpolate : α → α → Int → Int → α

def ratOps : NumericOps ℚ where
  zero := 0
  le := fun a b => decide (a ≤ b)
  interpolate := fun a b n delta => (a * (n - delta : Int) + b * delta) / n

def floatOps : NumericOps Float where
  zero := 0
  le := fun a b => a ≤ b
  interpolate := fun a b n delta =>
    (a * Float.ofInt (n - delta) + b * Float.ofInt delta) / Float.ofInt n

/-- A zero-based left endpoint, together with the signed right-hand weight. -/
def cutIndex (ld n : Nat) (method : String) (i : Nat) : Nat :=
  if method == "inclusive" then i * (ld - 1) / n
  else max 1 (min (i * (ld + 1) / n) (ld - 1)) - 1

def cutDelta (ld n : Nat) (method : String) (i : Nat) : Int :=
  if method == "inclusive" then (i * (ld - 1) % n : Nat)
  else (i : Int) * ((ld : Int) + 1) - ((cutIndex ld n method i : Int) + 1) * n

/-- One cut of an already sorted sample. The fallback is unreachable on valid inputs. -/
def cutWith (ops : NumericOps α) (sorted : List α) (n : Nat)
    (method : String) (i : Nat) : α :=
  let j := cutIndex sorted.length n method i
  ops.interpolate (sorted.getD j ops.zero) (sorted.getD (j + 1) ops.zero)
    n (cutDelta sorted.length n method i)

def cutsWith (ops : NumericOps α) (data : List α) (n : Nat)
    (method : String) : List α :=
  let sorted := data.mergeSort ops.le
  (List.range (n - 1)).map fun k => cutWith ops sorted n method (k + 1)

def quantilesWith (ops : NumericOps α) (data : List α) (n : Int := 4)
    (method : String := "exclusive") : Except QuantileError (List α) :=
  if n < 1 then .error (.statisticsError "n must be at least 1")
  else if data.length < 2 then
    .error (.statisticsError "must have at least two data points")
  else if validMethod method then .ok (cutsWith ops data n.toNat method)
  else .error (.valueError ("Unknown method: '" ++ method ++ "'"))

def benchmarkWith (ops : NumericOps α) (data : List α) (n : Int := 4)
    (method : String := "exclusive") : Except QuantileError (List α) :=
  if preCheck data n method then quantilesWith ops data n method
  else .error (.statisticsError preMessage)

def quantiles (data : List ℚ) (n : Int := 4)
    (method : String := "exclusive") := quantilesWith ratOps data n method

def benchmark_quantiles (data : List ℚ) (n : Int := 4)
    (method : String := "exclusive") : Except QuantileError (List ℚ) :=
  benchmarkWith ratOps data n method

namespace FloatLayer

def quantiles (data : List Float) (n : Int := 4) (method : String := "exclusive") :=
  quantilesWith floatOps data n method

def benchmark_quantiles (data : List Float) (n : Int := 4)
    (method : String := "exclusive") := benchmarkWith floatOps data n method

end FloatLayer

-- Unit tests, including the source examples and boundary extrapolation.
example : benchmark_quantiles [1, 2, 3, 4] = .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmark_quantiles [1, 2, 3, 4] 4 "inclusive" =
    .ok [7/4, 5/2, 13/4] := by native_decide
example : benchmark_quantiles [1, 2, 3, 4, 5] 2 = .ok [3] := by native_decide
example : benchmark_quantiles [4, 1, 3, 2] = .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmark_quantiles [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] =
    .ok [11/4, 11/2, 33/4] := by native_decide
example : (benchmark_quantiles ((List.range 11).map fun k => (k : ℚ)) 10).toOption.map
    List.length = some 9 := by native_decide
example : benchmark_quantiles [3/2, 5/2, 7/2, 9/2] 2 = .ok [3] := by native_decide
example : benchmark_quantiles [0, 10] = .ok [-5/2, 5, 25/2] := by native_decide
example : benchmark_quantiles [9, 1] 1 = .ok [] := by native_decide
example : benchmark_quantiles [1] = .error (.statisticsError preMessage) := by native_decide
example : benchmark_quantiles [1, 2] 0 = .error (.statisticsError preMessage) := by native_decide
example : benchmark_quantiles [1, 2] (-3) = .error (.statisticsError preMessage) := by native_decide
example : benchmark_quantiles [1, 2, 3] 4 "invalid" =
    .error (.statisticsError preMessage) := by native_decide
example : quantiles [1, 2] 4 "invalid" =
    .error (.valueError "Unknown method: 'invalid'") := by native_decide
example : FloatLayer.benchmark_quantiles [1, 2, 3, 4] == .ok [1.25, 2.5, 3.75] := by
  native_decide
example : FloatLayer.benchmark_quantiles [1.5, 2.5, 3.5, 4.5] 2 == .ok [3.0] := by
  native_decide
#eval benchmark_quantiles [1, 2, 3, 4]
#eval FloatLayer.benchmark_quantiles [1, 2, 3, 4] 4 "inclusive"

/-- The source precondition, with container and parameter types checked statically. -/
def Pre (data : List α) (n : Int := 4) (method : String := "exclusive") : Prop :=
  2 ≤ data.length ∧ 1 ≤ n ∧ (method = "inclusive" ∨ method = "exclusive")

theorem preCheck_iff {data : List α} {n : Int} {method : String} :
    preCheck data n method = true ↔ Pre data n method := by
  simp [preCheck, validMethod, Pre, and_assoc]

theorem benchmarkWith_success (ops : NumericOps α) {data : List α} {n : Int}
    {method : String} (h : Pre data n method) :
    benchmarkWith ops data n method = .ok (cutsWith ops data n.toNat method) := by
  have hc := preCheck_iff.mpr h
  have hm : validMethod method = true := by
    rcases h.2.2 with h | h <;> simp [validMethod, h]
  simp [benchmarkWith, hc, quantilesWith, not_lt.mpr h.1, not_lt.mpr h.2.1, hm]

/-- All admissible calls return exactly n-1 cut points. This also covers Float. -/
def length_prop (ops : NumericOps α) (data : List α) (n : Int) (method : String) : Prop :=
  (benchmarkWith ops data n method).toOption.map List.length = some (n.toNat - 1)

theorem length_thm (ops : NumericOps α) {data : List α} {n : Int} {method : String}
    (h : Pre data n method) : length_prop ops data n method := by
  simp [length_prop, benchmarkWith_success ops h, cutsWith, Except.toOption]

/-- Invalid calls to the benchmark raise its StatisticsError, including invalid methods. -/
def error_prop (ops : NumericOps α) (data : List α) (n : Int) (method : String) : Prop :=
  ¬ Pre data n method → benchmarkWith ops data n method =
    .error (.statisticsError preMessage)

theorem error_thm (ops : NumericOps α) (data : List α) (n : Int) (method : String) :
    error_prop ops data n method := by
  intro h
  have hc : preCheck data n method = false := by
    cases he : preCheck data n method <;> simp_all [preCheck_iff]
  simp [benchmarkWith, hc]

/-- A single interval has no separating cuts, but still requires two observations. -/
def one_interval_prop (ops : NumericOps α) (data : List α) (method : String) : Prop :=
  benchmarkWith ops data 1 method = .ok []

theorem one_interval_thm (ops : NumericOps α) {data : List α} {method : String}
    (h : Pre data 1 method) : one_interval_prop ops data method := by
  simp [one_interval_prop, benchmarkWith_success ops h, cutsWith]

/-- Explicit source interpolation formula, independent of `cutIndex`/`cutDelta`. -/
def sourceCut (ops : NumericOps α) (s : List α) (n : Nat) (method : String)
    (i : Nat) : α :=
  if method == "inclusive" then
    let m := s.length - 1
    let j := i * m / n
    let delta : Int := (i * m % n : Nat)
    ops.interpolate (s.getD j ops.zero) (s.getD (j + 1) ops.zero) n delta
  else
    let m := s.length + 1
    let j := max 1 (min (i * m / n) (s.length - 1))
    let delta : Int := (i : Int) * m - (j : Int) * n
    ops.interpolate (s.getD (j - 1) ops.zero) (s.getD j ops.zero) n delta

theorem cutWith_sourceCut (ops : NumericOps α) (s : List α) (n : Nat)
    (method : String) (i : Nat) : cutWith ops s n method i = sourceCut ops s n method i := by
  by_cases hm : method == "inclusive"
  · simp [cutWith, sourceCut, cutIndex, cutDelta, hm]
  · have hj : 1 ≤ max 1 (min (i * (s.length + 1) / n) (s.length - 1)) := le_max_left _ _
    have he : max 1 (min (i * (s.length + 1) / n) (s.length - 1)) - 1 + 1 =
        max 1 (min (i * (s.length + 1) / n) (s.length - 1)) := by omega
    simp [cutWith, sourceCut, cutIndex, cutDelta, hm, he, Nat.cast_add,
      Nat.cast_one]

/-- Each returned element obeys the appropriate divmod or clamped formula. -/
def interpolation_prop (ops : NumericOps α) (data : List α) (n : Int)
    (method : String) : Prop :=
  ∀ k < n.toNat - 1,
    (benchmarkWith ops data n method).toOption.bind (fun xs => xs[k]?) =
      some (sourceCut ops (data.mergeSort ops.le) n.toNat method (k + 1))

theorem interpolation_thm (ops : NumericOps α) {data : List α} {n : Int}
    {method : String} (h : Pre data n method) : interpolation_prop ops data n method := by
  intro k hk
  simp [benchmarkWith_success ops h, cutsWith, Except.toOption, List.getElem?_range hk,
    cutWith_sourceCut]

/-- Both sample accesses used by every cut are within bounds. -/
def indices_prop (data : List α) (n : Int) (method : String) : Prop :=
  ∀ i, 1 ≤ i → i < n.toNat → cutIndex data.length n.toNat method i + 1 < data.length

theorem indices_thm {data : List α} {n : Int} {method : String}
    (h : Pre data n method) : indices_prop data n method := by
  intro i hi hin
  rcases h with ⟨hld, hn0, hm0⟩
  have hn : 0 < n.toNat := by omega
  by_cases hm : method == "inclusive"
  · simp only [cutIndex, hm, ↓reduceIte]
    have hmpos : 0 < data.length - 1 := by omega
    have hlt : i * (data.length - 1) < (data.length - 1) * n.toNat := by
      simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hin hmpos
    have hd := (Nat.div_lt_iff_lt_mul hn).mpr hlt
    omega
  · simp only [cutIndex, hm, Bool.false_eq_true, ↓reduceIte]
    have hb : min (i * (data.length + 1) / n.toNat) (data.length - 1) ≤
        data.length - 1 := min_le_right _ _
    have hl : 1 ≤ data.length - 1 := by omega
    have hu := max_le hl hb
    have hlo : 1 ≤ max 1 (min (i * (data.length + 1) / n.toNat) (data.length - 1)) :=
      le_max_left _ _
    omega

/-- Sorting makes exact-rational answers invariant under all input permutations. -/
def permutation_prop (data other : List ℚ) (n : Int) (method : String) : Prop :=
  data.Perm other → benchmark_quantiles data n method = benchmark_quantiles other n method

theorem permutation_thm (data other : List ℚ) (n : Int) (method : String) :
    permutation_prop data other n method := by
  intro hp
  have hs : data.mergeSort ratOps.le = other.mergeSort ratOps.le :=
    List.eq_of_perm_of_sorted
      (((List.mergeSort_perm data ratOps.le).trans hp).trans
        (List.mergeSort_perm other ratOps.le).symm)
      (List.sorted_mergeSort' (· ≤ ·) data) (List.sorted_mergeSort' (· ≤ ·) other)
  simp only [benchmark_quantiles, benchmarkWith, preCheck, hp.length_eq, quantilesWith,
    cutsWith, hs]

/-- The inclusive method interpolates between its two adjacent observations. -/
def inclusive_bounds_prop (data : List ℚ) (n : Int) : Prop :=
  let s := data.mergeSort ratOps.le
  ∀ i, 1 ≤ i → i < n.toNat →
    let j := cutIndex s.length n.toNat "inclusive" i
    s.getD j 0 ≤ cutWith ratOps s n.toNat "inclusive" i ∧
      cutWith ratOps s n.toNat "inclusive" i ≤ s.getD (j + 1) 0

theorem sorted_getD_mono {s : List ℚ} (hs : s.Sorted (· ≤ ·))
    {j k : Nat} (hjk : j ≤ k) (hk : k < s.length) : s.getD j 0 ≤ s.getD k 0 := by
  have hj := lt_of_le_of_lt hjk hk
  rw [List.getD_eq_getElem s 0 hj, List.getD_eq_getElem s 0 hk]
  exact hs.rel_get_of_le (a := ⟨j, hj⟩) (b := ⟨k, hk⟩) hjk

theorem interpolate_lower {a b : ℚ} {n d : Int} (hab : a ≤ b)
    (hn : 0 < n) (hd : 0 ≤ d) : a ≤ ratOps.interpolate a b n d := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hdq : (0 : ℚ) ≤ d := by exact_mod_cast hd
  change a ≤ (a * ((n - d : Int) : ℚ) + b * (d : ℚ)) / (n : ℚ)
  apply (le_div_iff₀ hnq).mpr
  push_cast
  nlinarith

theorem interpolate_upper {a b : ℚ} {n d : Int} (hab : a ≤ b)
    (hn : 0 < n) (hd : d ≤ n) : ratOps.interpolate a b n d ≤ b := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hdq : (d : ℚ) ≤ n := by exact_mod_cast hd
  change (a * ((n - d : Int) : ℚ) + b * (d : ℚ)) / (n : ℚ) ≤ b
  apply (div_le_iff₀ hnq).mpr
  push_cast
  nlinarith

theorem inclusive_bounds_thm {data : List ℚ} {n : Int}
    (h : Pre data n "inclusive") : inclusive_bounds_prop data n := by
  intro i hi hin
  let s := data.mergeSort ratOps.le
  have hs : s.Sorted (· ≤ ·) := List.sorted_mergeSort' (· ≤ ·) data
  have hlen : s.length = data.length := List.length_mergeSort data
  have hb := indices_thm h i hi hin
  rw [← hlen] at hb
  have hab := sorted_getD_mono hs (Nat.le_succ (cutIndex s.length n.toNat "inclusive" i)) hb
  have hn : 0 < n.toNat := by omega
  have hnz : (0 : Int) < (n.toNat : Int) := by exact_mod_cast hn
  have hd0 : 0 ≤ cutDelta s.length n.toNat "inclusive" i := by
    change (0 : Int) ≤ ((i * (s.length - 1) % n.toNat : Nat) : Int)
    exact Int.natCast_nonneg _
  have hdn : cutDelta s.length n.toNat "inclusive" i ≤ (n.toNat : Int) := by
    simp only [cutDelta, BEq.rfl, ↓reduceIte]
    exact_mod_cast (Nat.mod_lt (i * (s.length - 1)) hn).le
  exact ⟨interpolate_lower hab hnz hd0, interpolate_upper hab hnz hdn⟩

/-- Constant samples remain constant, including extrapolated exclusive cuts. -/
def constant_prop (value : ℚ) (ld : Nat) (n : Int) (method : String) : Prop :=
  benchmark_quantiles (List.replicate ld value) n method =
    .ok (List.replicate (n.toNat - 1) value)

theorem constant_thm (value : ℚ) {ld : Nat} {n : Int} {method : String}
    (h : Pre (List.replicate ld value) n method) : constant_prop value ld n method := by
  have hs : (List.replicate ld value).mergeSort ratOps.le = List.replicate ld value :=
    List.mergeSort_eq_self (· ≤ ·) (by simp [List.sorted_replicate])
  have hn : (n.toNat : ℚ) ≠ 0 := by
    have : 0 < n.toNat := by have := h.2.1; omega
    exact_mod_cast this.ne'
  unfold constant_prop benchmark_quantiles
  rw [benchmarkWith_success ratOps h]
  congr 1
  simp only [cutsWith, hs]
  conv_rhs => rw [← List.length_range (n := n.toNat - 1)]
  apply List.map_eq_replicate_iff.mpr
  intro k hk
  have hk' := List.mem_range.mp hk
  have hb := indices_thm h (k + 1) (by omega) (by omega)
  simp only [List.length_replicate] at hb
  simp only [cutWith, List.length_replicate]
  rw [List.getD_replicate value (by omega), List.getD_replicate value hb]
  simp only [ratOps]
  push_cast
  field_simp [hn]
  ring

/-- Clamping leaves a nonnegative weight away from the first segment, and a
weight at most n away from the last segment. No false convexity assumption is
made about exclusive extrapolation. -/
theorem exclusive_weight_bounds (ld n i : Nat) (hld : 2 ≤ ld) (hn : 0 < n) :
    (0 < cutIndex ld n "exclusive" i → 0 ≤ cutDelta ld n "exclusive" i) ∧
    (cutIndex ld n "exclusive" i + 2 < ld → cutDelta ld n "exclusive" i ≤ (n : Int)) := by
  let q := i * (ld + 1) / n
  let j := cutIndex ld n "exclusive" i
  have hqlo : q * n ≤ i * (ld + 1) := Nat.div_mul_le_self _ _
  have hqhi : i * (ld + 1) < n * (q + 1) := Nat.lt_mul_div_succ _ hn
  have hnz : (0 : Int) < n := by exact_mod_cast hn
  have hloz : (q : Int) * n ≤ (i : Int) * ((ld : Int) + 1) := by exact_mod_cast hqlo
  have hhiz : (i : Int) * ((ld : Int) + 1) < (n : Int) * ((q : Int) + 1) := by
    exact_mod_cast hqhi
  constructor
  · intro hj
    have hqj : j + 1 ≤ q := by
      dsimp [j, cutIndex, q] at *
      omega
    have hqjz : (j : Int) + 1 ≤ (q : Int) := by exact_mod_cast hqj
    change 0 ≤ (i : Int) * ((ld : Int) + 1) - ((j : Int) + 1) * n
    nlinarith
  · intro hj
    have hjq : q ≤ j + 1 := by
      dsimp [j, cutIndex, q] at *
      omega
    have hjqz : (q : Int) ≤ (j : Int) + 1 := by exact_mod_cast hjq
    change (i : Int) * ((ld : Int) + 1) - ((j : Int) + 1) * n ≤ (n : Int)
    nlinarith

theorem cutIndex_mono (ld n : Nat) (method : String) {i k : Nat} (hik : i ≤ k) :
    cutIndex ld n method i ≤ cutIndex ld n method k := by
  have ha := Nat.div_le_div_right (c := n) (Nat.mul_le_mul_right (ld - 1) hik)
  have hb := Nat.div_le_div_right (c := n) (Nat.mul_le_mul_right (ld + 1) hik)
  unfold cutIndex
  split <;> omega

theorem cutDelta_mono_same_index (ld n : Nat) (method : String) {i k : Nat}
    (hik : i ≤ k) (hj : cutIndex ld n method i = cutIndex ld n method k) :
    cutDelta ld n method i ≤ cutDelta ld n method k := by
  by_cases hm : method == "inclusive"
  · have hprod := Nat.mul_le_mul_right (ld - 1) hik
    have hi := Nat.mod_add_div (i * (ld - 1)) n
    have hk := Nat.mod_add_div (k * (ld - 1)) n
    simp only [cutIndex, hm, ↓reduceIte] at hj
    rw [hj] at hi
    have hmod : i * (ld - 1) % n ≤ k * (ld - 1) % n := by omega
    simp only [cutDelta, hm, ↓reduceIte]
    exact_mod_cast hmod
  · have hikz : (i : Int) ≤ k := by exact_mod_cast hik
    simp only [cutDelta, hm, Bool.false_eq_true, ↓reduceIte, hj]
    have : (0 : Int) ≤ ld := Int.natCast_nonneg _
    nlinarith

theorem interpolate_mono_delta {a b : ℚ} {n d e : Int} (hab : a ≤ b)
    (hn : 0 < n) (hde : d ≤ e) :
    ratOps.interpolate a b n d ≤ ratOps.interpolate a b n e := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hdeq : (d : ℚ) ≤ e := by exact_mod_cast hde
  change (a * ((n - d : Int) : ℚ) + b * (d : ℚ)) / (n : ℚ) ≤
    (a * ((n - e : Int) : ℚ) + b * (e : ℚ)) / (n : ℚ)
  apply div_le_div_of_nonneg_right _ hnq.le
  push_cast
  nlinarith

theorem cutWith_mono {s : List ℚ} {n : Nat} {method : String}
    (hs : s.Sorted (· ≤ ·)) (hld : 2 ≤ s.length) (hn : 0 < n)
    (hmeth : method = "inclusive" ∨ method = "exclusive")
    {i k : Nat} (hi : 1 ≤ i) (hik : i ≤ k) (hkn : k < n) :
    cutWith ratOps s n method i ≤ cutWith ratOps s n method k := by
  have hp : Pre s (n : Int) method := ⟨hld, by omega, hmeth⟩
  have hbi := indices_thm hp i hi (by simpa using lt_of_le_of_lt hik hkn)
  have hbk := indices_thm hp k (by omega) (by simpa using hkn)
  simp only [Int.toNat_natCast] at hbi hbk
  have hj := cutIndex_mono s.length n method hik
  have hnz : (0 : Int) < n := by exact_mod_cast hn
  have hai := sorted_getD_mono hs (Nat.le_succ _) hbi
  have hak := sorted_getD_mono hs (Nat.le_succ _) hbk
  rcases hj.eq_or_lt with he | hlt
  · unfold cutWith
    rw [he]
    exact interpolate_mono_delta hak hnz (cutDelta_mono_same_index _ _ _ hik he)
  · have hdi : cutDelta s.length n method i ≤ (n : Int) := by
      rcases hmeth with hm | hm
      · subst method
        change ((i * (s.length - 1) % n : Nat) : Int) ≤ (n : Int)
        exact_mod_cast (Nat.mod_lt _ hn).le
      · subst method
        exact (exclusive_weight_bounds _ _ _ hld hn).2 (by omega)
    have hdk : 0 ≤ cutDelta s.length n method k := by
      rcases hmeth with hm | hm
      · subst method
        change (0 : Int) ≤ ((k * (s.length - 1) % n : Nat) : Int)
        exact Int.natCast_nonneg _
      · subst method
        exact (exclusive_weight_bounds _ _ _ hld hn).1 (by omega)
    exact (interpolate_upper hai hnz hdi).trans
      ((sorted_getD_mono hs (by omega : cutIndex s.length n method i + 1 ≤
        cutIndex s.length n method k) (by omega)).trans (interpolate_lower hak hnz hdk))

/-- Cuts are nondecreasing for both methods, even when exclusive cuts extrapolate. -/
def monotone_prop (data : List ℚ) (n : Int) (method : String) : Prop :=
  ∃ xs, benchmark_quantiles data n method = .ok xs ∧ xs.Pairwise (· ≤ ·)

theorem monotone_thm {data : List ℚ} {n : Int} {method : String}
    (h : Pre data n method) : monotone_prop data n method := by
  refine ⟨cutsWith ratOps data n.toNat method, benchmarkWith_success ratOps h, ?_⟩
  unfold cutsWith
  apply List.pairwise_iff_getElem.mpr
  intro a b ha hb hab
  simp only [List.length_map, List.length_range] at ha hb
  simp only [List.getElem_map, List.getElem_range]
  apply cutWith_mono (List.sorted_mergeSort' (· ≤ ·) data)
    (by simpa using h.1) (by omega) h.2.2 (by omega) (by omega) (by omega)

/-- For n=2, both methods return the usual median (the mean of the middle two
observations in an even sample). -/
def median_prop (data : List ℚ) (method : String) : Prop :=
  let s := data.mergeSort ratOps.le
  benchmark_quantiles data 2 method =
    .ok [(s.getD ((s.length - 1) / 2) 0 + s.getD (s.length / 2) 0) / 2]

theorem cutWith_median (s : List ℚ) (method : String) (hld : 2 ≤ s.length) :
    cutWith ratOps s 2 method 1 =
      (s.getD ((s.length - 1) / 2) 0 + s.getD (s.length / 2) 0) / 2 := by
  have hj : cutIndex s.length 2 method 1 = (s.length - 1) / 2 := by
    unfold cutIndex
    split
    · simp only [one_mul]
    · simp only [one_mul]
      omega
  have hd : cutDelta s.length 2 method 1 = (((s.length - 1) % 2 : Nat) : Int) := by
    unfold cutDelta
    split
    · simp
    · rw [hj]
      push_cast
      omega
  unfold cutWith
  rw [hj, hd]
  dsimp only
  by_cases he : s.length % 2 = 0
  · have hj' : (s.length - 1) / 2 + 1 = s.length / 2 := by omega
    have hd' : (s.length - 1) % 2 = 1 := by omega
    rw [hj', hd']
    norm_num [ratOps]
  · have hj' : (s.length - 1) / 2 = s.length / 2 := by omega
    have hd' : (s.length - 1) % 2 = 0 := by omega
    rw [hd', hj']
    norm_num [ratOps]

theorem median_thm {data : List ℚ} {method : String} (h : Pre data 2 method) :
    median_prop data method := by
  unfold median_prop benchmark_quantiles
  rw [benchmarkWith_success ratOps h]
  simp only [cutsWith]
  change Except.ok [cutWith ratOps (data.mergeSort ratOps.le) 2 method 1] = _
  rw [cutWith_median _ _ (by simpa using h.1)]

/-- The full successful-result contract, with exact numeric assertions at Rat. -/
def Post_prop (data : List ℚ) (n : Int) (method : String) : Prop :=
  length_prop ratOps data n method ∧
  interpolation_prop ratOps data n method ∧
  indices_prop data n method ∧
  monotone_prop data n method ∧
  (method = "inclusive" → inclusive_bounds_prop data n) ∧
  (n = 1 → one_interval_prop ratOps data method) ∧
  (n = 2 → median_prop data method) ∧
  (∀ other, permutation_prop data other n method)

/-! Property-based tests. Each `_prop` above has an executable check below.
The bounded family contains every list of length 0 through 4 over four rational
values (341 lists), parameters -2 through 12, and both valid and invalid methods.
The permutation checks enumerate *all* permutations of each tested list.
-/

def words (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => alphabet.flatMap fun x => (words alphabet k).map (x :: ·)

def pbtValues : List ℚ := [-3, -1/2, 0, 2]
def pbtSamples : List (List ℚ) := (List.range 5).flatMap (words pbtValues)
def pbtParameters : List Int := (List.range 15).map fun k => (k : Int) - 2
def pbtMethods : List String := ["inclusive", "exclusive", "invalid", ""]

def allCases (test : List ℚ → Int → String → Bool) : Bool :=
  pbtSamples.all fun data => pbtParameters.all fun n => pbtMethods.all (test data n)

def admissibleCases (test : List ℚ → Int → String → Bool) : Bool :=
  allCases fun data n method => !preCheck data n method || test data n method

def lengthCheck (ops : NumericOps α) (data : List α) (n : Int) (method : String) : Bool :=
  (benchmarkWith ops data n method).toOption.map List.length == some (n.toNat - 1)

def errorCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  preCheck data n method || benchmark_quantiles data n method ==
    .error (.statisticsError preMessage)

def oneIntervalCheck (data : List ℚ) (method : String) : Bool :=
  benchmark_quantiles data 1 method == .ok []

def interpolationCheck [BEq α] (ops : NumericOps α) (data : List α)
    (n : Int) (method : String) : Bool :=
  (List.range (n.toNat - 1)).all fun k =>
    (benchmarkWith ops data n method).toOption.bind (fun xs => xs[k]?) ==
      some (sourceCut ops (data.mergeSort ops.le) n.toNat method (k + 1))

def indicesCheck (data : List α) (n : Int) (method : String) : Bool :=
  (List.range (n.toNat - 1)).all fun k =>
    decide (cutIndex data.length n.toNat method (k + 1) + 1 < data.length)

def permutationCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  let result := benchmark_quantiles data n method
  data.permutations.all fun other => result == benchmark_quantiles other n method

def inclusiveBoundsCheck (data : List ℚ) (n : Int) : Bool :=
  let s := data.mergeSort ratOps.le
  match benchmark_quantiles data n "inclusive" with
  | .error _ => false
  | .ok xs => (List.range (n.toNat - 1)).all fun k =>
      let j := cutIndex s.length n.toNat "inclusive" (k + 1)
      match xs[k]? with
      | none => false
      | some x => decide (s.getD j 0 ≤ x ∧ x ≤ s.getD (j + 1) 0)

def constantCheck (value : ℚ) (ld : Nat) (n : Int) (method : String) : Bool :=
  benchmark_quantiles (List.replicate ld value) n method ==
    .ok (List.replicate (n.toNat - 1) value)

def monotoneCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  match benchmark_quantiles data n method with
  | .error _ => false
  | .ok xs => decide (xs.Pairwise (· ≤ ·))

def medianCheck (data : List ℚ) (method : String) : Bool :=
  let s := data.mergeSort ratOps.le
  benchmark_quantiles data 2 method ==
    .ok [(s.getD ((s.length - 1) / 2) 0 + s.getD (s.length / 2) 0) / 2]

/-- Boolean counterpart of every conjunct of `Post_prop`; its universally
quantified permutation conjunct is bounded by enumerating the input's permutations. -/
def postCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  lengthCheck ratOps data n method && interpolationCheck ratOps data n method &&
  indicesCheck data n method && monotoneCheck data n method &&
  (method != "inclusive" || inclusiveBoundsCheck data n) &&
  (n != 1 || oneIntervalCheck data method) &&
  (n != 2 || medianCheck data method) && permutationCheck data n method

-- PBT: length_prop.
example : admissibleCases (lengthCheck ratOps) = true := by native_decide
-- PBT: error_prop, including empty/singleton lists, negative n, and invalid methods.
example : allCases errorCheck = true := by native_decide
-- PBT: one_interval_prop.
example : pbtSamples.all (fun data => pbtMethods.all (fun method =>
    !preCheck data 1 method || oneIntervalCheck data method)) = true := by native_decide
-- PBT: interpolation_prop, for every cut of every admissible case.
example : admissibleCases (interpolationCheck ratOps) = true := by native_decide
-- PBT: indices_prop.
example : admissibleCases indicesCheck = true := by native_decide
-- PBT: permutation_prop (also checks invalid calls).
example : allCases permutationCheck = true := by native_decide
-- PBT: inclusive_bounds_prop, checking the returned values themselves.
example : pbtSamples.all (fun data => pbtParameters.all (fun n =>
    !preCheck data n "inclusive" || inclusiveBoundsCheck data n)) = true := by native_decide
-- PBT: constant_prop, lengths 2 through 8 and all valid sampled parameters/methods.
example : pbtValues.all (fun value => (List.range 7).all (fun k =>
    pbtParameters.all (fun n => pbtMethods.all (fun method =>
      !preCheck (List.replicate (k + 2) value) n method ||
        constantCheck value (k + 2) n method)))) = true := by native_decide
-- PBT: monotone_prop, including repeated values and extrapolation.
example : admissibleCases monotoneCheck = true := by native_decide
-- PBT: median_prop, both odd and even sample lengths and both methods.
example : pbtSamples.all (fun data => pbtMethods.all (fun method =>
    !preCheck data 2 method || medianCheck data method)) = true := by native_decide
-- PBT: Post_prop, all its conjuncts checked together.
example : admissibleCases postCheck = true := by native_decide

-- PBT: the shared executable structural properties also hold in the Float layer.
example : admissibleCases (fun data n method =>
    let floats := data.map fun q => Float.ofInt q.num / Float.ofNat q.den
    lengthCheck floatOps floats n method &&
      interpolationCheck floatOps floats n method && indicesCheck floats n method) = true := by
  native_decide

-- Randomized PBT of the whole postcondition. Construction guarantees admissibility;
-- generated integer values are unrestricted, and n ranges from 1 through 20.
#eval Plausible.Testable.check (∀ (xs : List Int) (k : Nat) (inclusive : Bool),
  let data : List ℚ := (0 :: 1 :: xs.take 2).map fun x => (x : ℚ)
  let n : Int := (k % 20 + 1 : Nat)
  let method := if inclusive then "inclusive" else "exclusive"
  postCheck data n method = true)

-- Additional bounded PBT for percentile-scale interpolation and extrapolation.
example : (words pbtValues 2).all (fun data =>
    ["inclusive", "exclusive"].all (fun method => postCheck data 100 method)) = true := by
  native_decide

/-- Correctness for every admissible exact mathematical input. -/
theorem correctness_thm {data : List ℚ} {n : Int} {method : String} :
    Pre data n method → Post_prop data n method := by
  intro h
  refine ⟨length_thm ratOps h, interpolation_thm ratOps h, indices_thm h,
    monotone_thm h, ?_, ?_, ?_, ?_⟩
  · intro hm
    subst method
    exact inclusive_bounds_thm h
  · intro hn
    subst n
    exact one_interval_thm ratOps h
  · intro hn
    subst n
    exact median_thm h
  · intro other
    exact permutation_thm data other n method

/-- Imperative cut collection, using a mutable result and the source formula. -/
def cutsImperativeWith (ops : NumericOps α) (data : List α) (n : Nat)
    (method : String) : List α := Id.run do
  let sorted := data.mergeSort ops.le
  let mut result : List α := []
  for k in List.range (n - 1) do
    let interpolated := sourceCut ops sorted n method (k + 1)
    result := result ++ [interpolated]
  return result

def quantilesImperativeWith (ops : NumericOps α) (data : List α) (n : Int := 4)
    (method : String := "exclusive") : Except QuantileError (List α) := Id.run do
  if n < 1 then
    return .error (.statisticsError "n must be at least 1")
  if data.length < 2 then
    return .error (.statisticsError "must have at least two data points")
  if !validMethod method then
    return .error (.valueError ("Unknown method: '" ++ method ++ "'"))
  return .ok (cutsImperativeWith ops data n.toNat method)

def benchmarkImperativeWith (ops : NumericOps α) (data : List α) (n : Int := 4)
    (method : String := "exclusive") : Except QuantileError (List α) := Id.run do
  if !preCheck data n method then
    return .error (.statisticsError preMessage)
  return quantilesImperativeWith ops data n method

def benchmark_quantiles_imperative (data : List ℚ) (n : Int := 4)
    (method : String := "exclusive") : Except QuantileError (List ℚ) :=
  benchmarkImperativeWith ratOps data n method

namespace FloatLayer

def benchmark_quantiles_imperative (data : List Float) (n : Int := 4)
    (method : String := "exclusive") := benchmarkImperativeWith floatOps data n method

end FloatLayer

-- Imperative unit and property-based tests.
example : benchmark_quantiles_imperative [1, 2, 3, 4] =
    .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmark_quantiles_imperative [4, 1, 3, 2] 4 "inclusive" =
    .ok [7/4, 5/2, 13/4] := by native_decide
example : benchmark_quantiles_imperative [0, 10] = .ok [-5/2, 5, 25/2] := by native_decide
example : benchmark_quantiles_imperative [1] =
    .error (.statisticsError preMessage) := by native_decide
example : FloatLayer.benchmark_quantiles_imperative [1, 2, 3, 4] ==
    .ok [1.25, 2.5, 3.75] := by native_decide
example : allCases (fun data n method => benchmark_quantiles data n method ==
    benchmark_quantiles_imperative data n method) = true := by native_decide
#eval benchmark_quantiles_imperative [1, 2, 3, 4]
#eval FloatLayer.benchmark_quantiles_imperative [1, 2, 3, 4] 4 "inclusive"

/-- Loop invariant: after visiting ks, the accumulator contains its old prefix
followed by exactly one interpolated value per visited index. -/
theorem foldl_append_eq (f : Nat → α) (ks : List Nat) (acc : List α) :
    ks.foldl (fun result k => result ++ [f k]) acc = acc ++ ks.map f := by
  induction ks generalizing acc with
  | nil => simp only [List.foldl_nil, List.map_nil, List.append_nil]
  | cons k ks ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.append_assoc, List.singleton_append]

theorem cuts_equivalence_thm (ops : NumericOps α) (data : List α) (n : Nat)
    (method : String) : cutsWith ops data n method = cutsImperativeWith ops data n method := by
  let f := fun k => sourceCut ops (data.mergeSort ops.le) n method (k + 1)
  have hloop : cutsImperativeWith ops data n method = (List.range (n - 1)).map f := by
    change (forIn (List.range (n - 1)) [] fun k result =>
      (pure (.yield (result ++ [f k])) : Id (ForInStep (List α)))).run = _
    rw [List.forIn_pure_yield_eq_foldl]
    change (List.range (n - 1)).foldl (fun result k => result ++ [f k]) [] = _
    rw [foldl_append_eq]
    rfl
  rw [hloop]
  simp only [cutsWith, cutWith_sourceCut, f]

theorem quantiles_equivalence_thm (ops : NumericOps α) (data : List α) (n : Int)
    (method : String) : quantilesWith ops data n method =
      quantilesImperativeWith ops data n method := by
  unfold quantilesWith quantilesImperativeWith
  by_cases hn : n < 1
  · simp [hn]
  · by_cases hd : data.length < 2
    · simp [hn, hd]
    · cases validMethod method <;> simp [hn, hd, cuts_equivalence_thm]

/-- Equivalence is unconditional: it includes rejected calls and arbitrary numeric
operations. Consequently it also holds for primitive Float, including special values. -/
theorem benchmark_equivalence_thm (ops : NumericOps α) (data : List α) (n : Int)
    (method : String) : benchmarkWith ops data n method =
      benchmarkImperativeWith ops data n method := by
  unfold benchmarkWith benchmarkImperativeWith
  cases preCheck data n method <;> simp [quantiles_equivalence_thm]

theorem equivalence_thm (data : List ℚ) (n : Int) (method : String) :
    benchmark_quantiles data n method = benchmark_quantiles_imperative data n method :=
  benchmark_equivalence_thm ratOps data n method

namespace FloatLayer

theorem equivalence_thm (data : List Float) (n : Int) (method : String) :
    benchmark_quantiles data n method = benchmark_quantiles_imperative data n method :=
  benchmark_equivalence_thm floatOps data n method

end FloatLayer

end StatisticsQuantiles
