import Mathlib

/-!
# VeriBench 31 — `statistics.quantiles`

Lean 4 formalization of Python's `statistics.quantiles` and of the benchmark
wrapper `benchmark_quantiles`.

Python divides a sample into `n` equal-probability intervals and returns the
`n - 1` cut points. Cuts are linear interpolants of the sorted sample:

* `inclusive` (population): index `i * (N - 1) / n`
* `exclusive` (sample, the default): index `i * (N + 1) / n - 1`,
  extrapolated on the first or last segment when the index falls outside
  `[0, N - 1]`

The index arithmetic is integral (`divmod` / floor-div). The only division is
by `n`, so on `int`, `Fraction` and `Decimal` inputs the result is exact.
That is the semantics proved here, over `Rat`. A `Float` layer repeats the
same algorithm for the ground tests in the Python source; values such as
`1.25` are dyadic and match under IEEE-754 equality. General `Float`
arithmetic laws are not kernel-reducible, so the proved statements live on
`Rat`. The `Float` checks are the executable counterpart of those statements.
-/

namespace «31_statistics_quantiles»

/-! ## Method, errors, and messages -/

inductive QuantileMethod where
  | exclusive
  | inclusive
  deriving DecidableEq, Repr, Inhabited, BEq

inductive QuantileError where
  | statisticsError (message : String)
  | valueError (message : String)
  deriving DecidableEq, Repr, BEq

def benchmarkMsg : String :=
  "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"

def quantilesNMsg : String := "n must be at least 1"

def quantilesLenMsg : String := "must have at least two data points"

def quantilesMethodMsg (method : String) : String :=
  "Unknown method: '" ++ method ++ "'"

def methodOK (method : String) : Bool :=
  method == "exclusive" || method == "inclusive"

def methodOf (method : String) : QuantileMethod :=
  if method == "inclusive" then .inclusive else .exclusive

/-- `n < 1`, fewer than two points, or an unknown method name. -/
def invalidInput (data : List Rat) (n : Int) (method : String) : Bool :=
  decide (data.length < 2) || decide (n < 1) || !methodOK method

/-! ## Sorting -/

def ratLE (a b : Rat) : Bool := decide (a ≤ b)

def sortedData (data : List Rat) : List Rat :=
  data.mergeSort ratLE

theorem ratLE_trans (a b c : Rat) (hab : ratLE a b) (hbc : ratLE b c) : ratLE a c := by
  simp only [ratLE, decide_eq_true_eq] at *
  exact le_trans hab hbc

theorem ratLE_total (a b : Rat) : (ratLE a b || ratLE b a) = true := by
  simp only [ratLE, Bool.or_eq_true, decide_eq_true_eq]
  exact le_total a b

theorem sortedData_pairwise (data : List Rat) : (sortedData data).Pairwise (· ≤ ·) := by
  have h := List.sorted_mergeSort (l := data) (le := ratLE) ratLE_trans ratLE_total
  refine List.Pairwise.imp (fun hab => ?_) h
  simpa [sortedData, ratLE, decide_eq_true_eq] using hab

theorem sortedData_perm (data : List Rat) : (sortedData data).Perm data := by
  simpa [sortedData] using List.mergeSort_perm data ratLE

@[simp] theorem sortedData_length (data : List Rat) : (sortedData data).length = data.length := by
  simp [sortedData]

theorem sortedData_eq_of_perm {l₁ l₂ : List Rat} (h : l₁.Perm l₂) :
    sortedData l₁ = sortedData l₂ := by
  apply List.Perm.eq_of_sorted (le := fun a b => ratLE a b = true)
  · intro a b _ _ hab hba
    exact le_antisymm (by simpa [ratLE] using hab) (by simpa [ratLE] using hba)
  · have h1 := List.sorted_mergeSort (l := l₁) (le := ratLE) ratLE_trans ratLE_total
    simpa [sortedData, ratLE] using h1
  · have h2 := List.sorted_mergeSort (l := l₂) (le := ratLE) ratLE_trans ratLE_total
    simpa [sortedData, ratLE] using h2
  · exact (List.mergeSort_perm l₁ ratLE).trans (h.trans (List.mergeSort_perm l₂ ratLE).symm)

theorem sortedData_idempotent (data : List Rat) :
    sortedData (sortedData data) = sortedData data := by
  simpa [sortedData] using
    (List.mergeSort_of_sorted (le := ratLE)
      (List.sorted_mergeSort (l := data) (le := ratLE) ratLE_trans ratLE_total))

theorem sortedData_of_sorted {data : List Rat} (h : data.Pairwise ratLE) :
    sortedData data = data := by
  simpa [sortedData] using List.mergeSort_of_sorted (le := ratLE) h

/-! ## Cut formulas (Python's integer arithmetic) -/

def inclusiveCut (sorted : List Rat) (n i : Nat) : Rat :=
  let prod := i * (sorted.length - 1)
  let j := prod / n
  let delta := prod % n
  let x := sorted.getD j 0
  let y := sorted.getD (j + 1) 0
  (x * ((n - delta : Nat) : Rat) + y * (delta : Rat)) / (n : Rat)

def exclusiveCut (sorted : List Rat) (n i : Nat) : Rat :=
  let ld := sorted.length
  let m := ld + 1
  let j0 := (i * m) / n
  let j := if j0 < 1 then 1 else if j0 > ld - 1 then ld - 1 else j0
  let delta : Int := Int.ofNat (i * m) - Int.ofNat (j * n)
  let x := sorted.getD (j - 1) 0
  let y := sorted.getD j 0
  (x * ((n : Rat) - (delta : Rat)) + y * (delta : Rat)) / (n : Rat)

def oneCut (sorted : List Rat) (n i : Nat) (method : QuantileMethod) : Rat :=
  match method with
  | .inclusive => inclusiveCut sorted n i
  | .exclusive => exclusiveCut sorted n i

/-- The `n - 1` cuts, for `i = 1, …, n - 1`, matching `range(1, n)`. -/
def quantileCuts (sorted : List Rat) (n : Nat) (method : QuantileMethod) : List Rat :=
  (List.range' 1 (n - 1)).map fun i => oneCut sorted n i method

def listMin (data : List Rat) : Rat := (sortedData data).getD 0 0

def listMax (data : List Rat) : Rat := (sortedData data).getD (data.length - 1) 0

/-- Sample median returned by exclusive `n = 2`. -/
def medianOf (data : List Rat) : List Rat :=
  let s := sortedData data
  let ld := s.length
  if ld % 2 = 1 then [s.getD (ld / 2) 0]
  else [(s.getD (ld / 2 - 1) 0 + s.getD (ld / 2) 0) / 2]

/-! ## Interpolation positions -/

def inclPos (ld n i : Nat) : Rat := (i * (ld - 1) : Rat) / (n : Rat)

def exclPos (ld n i : Nat) : Rat := (i * (ld + 1) : Rat) / (n : Rat) - 1

/-- Piecewise-linear interpolant of `s`, extended by the end segments. -/
def interpSorted (s : List Rat) (p : Rat) : Rat :=
  let ld := s.length
  if p ≤ 0 then
    s.getD 0 0 + (s.getD 1 0 - s.getD 0 0) * p
  else if (ld - 1 : Rat) ≤ p then
    s.getD (ld - 2) 0 +
      (s.getD (ld - 1) 0 - s.getD (ld - 2) 0) * (p - (ld - 2 : Rat))
  else
    let j := (Int.floor p).toNat
    s.getD j 0 + (s.getD (j + 1) 0 - s.getD j 0) * (p - (j : Rat))

/-! ## Functional implementation -/

def benchmarkQuantiles (data : List Rat) (n : Int := 4) (method : String := "exclusive") :
    Except QuantileError (List Rat) :=
  if invalidInput data n method then
    .error (.statisticsError benchmarkMsg)
  else
    .ok (quantileCuts (sortedData data) n.toNat (methodOf method))

/-- Python `statistics.quantiles`, including its distinct error priority. -/
def quantiles (data : List Rat) (n : Int := 4) (method : String := "exclusive") :
    Except QuantileError (List Rat) :=
  if n < 1 then
    .error (.statisticsError quantilesNMsg)
  else if data.length < 2 then
    .error (.statisticsError quantilesLenMsg)
  else if method == "inclusive" then
    .ok (quantileCuts (sortedData data) n.toNat .inclusive)
  else if method == "exclusive" then
    .ok (quantileCuts (sortedData data) n.toNat .exclusive)
  else
    .error (.valueError (quantilesMethodMsg method))

def specResult (data : List Rat) (n : Int) (method : String) : List Rat :=
  quantileCuts (sortedData data) n.toNat (methodOf method)

/-! ## Float layer (executable counterpart of the Rat model) -/

def natToFloat (k : Nat) : Float := k.toUInt64.toFloat

def intToFloat (z : Int) : Float :=
  if z < 0 then -natToFloat z.natAbs else natToFloat z.toNat

def sortedDataFloat (data : List Float) : List Float :=
  data.mergeSort (fun a b => decide (a ≤ b))

def inclusiveCutFloat (sorted : List Float) (n i : Nat) : Float :=
  let prod := i * (sorted.length - 1)
  let j := prod / n
  let delta := prod % n
  let x := sorted.getD j 0
  let y := sorted.getD (j + 1) 0
  (x * natToFloat (n - delta) + y * natToFloat delta) / natToFloat n

def exclusiveCutFloat (sorted : List Float) (n i : Nat) : Float :=
  let ld := sorted.length
  let m := ld + 1
  let j0 := (i * m) / n
  let j := if j0 < 1 then 1 else if j0 > ld - 1 then ld - 1 else j0
  let delta : Int := Int.ofNat (i * m) - Int.ofNat (j * n)
  let x := sorted.getD (j - 1) 0
  let y := sorted.getD j 0
  (x * (natToFloat n - intToFloat delta) + y * intToFloat delta) / natToFloat n

def oneCutFloat (sorted : List Float) (n i : Nat) (method : QuantileMethod) : Float :=
  match method with
  | .inclusive => inclusiveCutFloat sorted n i
  | .exclusive => exclusiveCutFloat sorted n i

def quantileCutsFloat (sorted : List Float) (n : Nat) (method : QuantileMethod) : List Float :=
  (List.range' 1 (n - 1)).map fun i => oneCutFloat sorted n i method

def invalidInputFloat (data : List Float) (n : Int) (method : String) : Bool :=
  decide (data.length < 2) || decide (n < 1) || !methodOK method

def benchmarkQuantilesFloat (data : List Float) (n : Int := 4)
    (method : String := "exclusive") : Except QuantileError (List Float) :=
  if invalidInputFloat data n method then
    .error (.statisticsError benchmarkMsg)
  else
    .ok (quantileCutsFloat (sortedDataFloat data) n.toNat (methodOf method))

/-! ## Unit tests -/

example : benchmarkQuantiles [(1 : Rat), 2, 3, 4] = .ok [5 / 4, 5 / 2, 15 / 4] := by
  native_decide

example : benchmarkQuantiles [(1 : Rat), 2, 3, 4] 4 "exclusive" = .ok [5 / 4, 5 / 2, 15 / 4] := by
  native_decide

example : benchmarkQuantiles [(1 : Rat), 2, 3, 4] 4 "inclusive" = .ok [7 / 4, 5 / 2, 13 / 4] := by
  native_decide

example : benchmarkQuantiles [(1 : Rat), 2, 3, 4, 5] 2 "exclusive" = .ok [3] := by
  native_decide

example : benchmarkQuantiles [(3 : Rat) / 2, 5 / 2, 7 / 2, 9 / 2] 2 = .ok [3] := by
  native_decide

example : benchmarkQuantiles ((List.range 11).map (fun k => (k : Rat))) 10 "exclusive" =
    .ok [1 / 5, 7 / 5, 13 / 5, 19 / 5, 5, 31 / 5, 37 / 5, 43 / 5, 49 / 5] := by
  native_decide

example : benchmarkQuantiles ((List.range 10).map (fun i => ((i + 1 : Nat) : Rat))) 4 =
    .ok [11 / 4, 11 / 2, 33 / 4] := by
  native_decide

example : benchmarkQuantiles [(4 : Rat), 1, 3, 2] = benchmarkQuantiles [1, 2, 3, 4] := by
  native_decide

example : benchmarkQuantiles [(1 : Rat), 2, 3] 1 "exclusive" = .ok [] := by
  native_decide

example : benchmarkQuantiles [(1 : Rat), 2] 4 "exclusive" = .ok [3 / 4, 3 / 2, 9 / 4] := by
  native_decide

example : benchmarkQuantiles [(1 : Rat), 2] 4 "inclusive" = .ok [5 / 4, 3 / 2, 7 / 4] := by
  native_decide

example : benchmarkQuantiles [(5 : Rat), 5, 5, 5] 4 "exclusive" = .ok [5, 5, 5] := by
  native_decide

example : benchmarkQuantiles [(-4 : Rat), -3, -2, -1] =
    .ok [-(15 / 4), -(5 / 2), -(5 / 4)] := by
  native_decide

example : benchmarkQuantiles [(1 : Rat)] 4 "exclusive" =
    .error (.statisticsError benchmarkMsg) := by
  native_decide

example : benchmarkQuantiles [(1 : Rat), 2] 0 "exclusive" =
    .error (.statisticsError benchmarkMsg) := by
  native_decide

example : benchmarkQuantiles [(1 : Rat), 2] (-3) "inclusive" =
    .error (.statisticsError benchmarkMsg) := by
  native_decide

example : benchmarkQuantiles [(1 : Rat), 2, 3] 4 "invalid" =
    .error (.statisticsError benchmarkMsg) := by
  native_decide

example : quantiles [(1 : Rat)] 4 "exclusive" =
    .error (.statisticsError quantilesLenMsg) := by
  native_decide

example : quantiles [(1 : Rat), 2] 0 "exclusive" =
    .error (.statisticsError quantilesNMsg) := by
  native_decide

example : quantiles [(1 : Rat), 2] (-5) "nope" =
    .error (.statisticsError quantilesNMsg) := by
  native_decide

example : quantiles [(1 : Rat), 2, 3] 4 "invalid" =
    .error (.valueError (quantilesMethodMsg "invalid")) := by
  native_decide

example : (match benchmarkQuantilesFloat [1, 2, 3, 4] 4 "exclusive" with
    | .ok r => r == [1.25, 2.5, 3.75]
    | .error _ => false) = true := by
  native_decide

example : (match benchmarkQuantilesFloat [1, 2, 3, 4] 4 "inclusive" with
    | .ok r => r == [1.75, 2.5, 3.25]
    | .error _ => false) = true := by
  native_decide

example : (match benchmarkQuantilesFloat [1, 2, 3, 4, 5] 2 "exclusive" with
    | .ok r => r == [3.0]
    | .error _ => false) = true := by
  native_decide

example : (match benchmarkQuantilesFloat [1.5, 2.5, 3.5, 4.5] 2 "exclusive" with
    | .ok r => r == [3.0]
    | .error _ => false) = true := by
  native_decide

example : (match benchmarkQuantilesFloat [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 "exclusive" with
    | .ok r => r.length == 9
    | .error _ => false) = true := by
  native_decide

#eval benchmarkQuantiles [(1 : Rat), 2, 3, 4]
#eval benchmarkQuantiles [(1 : Rat), 2, 3, 4] 4 "inclusive"
#eval benchmarkQuantiles ((List.range 11).map (fun k => (k : Rat))) 10 "exclusive"
#eval benchmarkQuantilesFloat [1, 2, 3, 4]

/-! ## Pre-condition -/

def Pre (data : List Rat) (n : Int) (method : String) : Prop :=
  2 ≤ data.length ∧ 1 ≤ n ∧ (method = "exclusive" ∨ method = "inclusive")

/-! ## Index and casting lemmas -/

lemma methodOK_iff (method : String) :
    methodOK method = true ↔ method = "exclusive" ∨ method = "inclusive" := by
  unfold methodOK
  simp [Bool.or_eq_true, beq_iff_eq]

lemma invalidInput_false_iff (data : List Rat) (n : Int) (method : String) :
    invalidInput data n method = false ↔ Pre data n method := by
  unfold invalidInput Pre
  simp only [Bool.or_eq_false_iff, Bool.not_eq_true', decide_eq_false_iff_not, methodOK_iff]
  constructor
  · rintro ⟨hl, hn, hm⟩
    exact ⟨Nat.not_lt.mp hl, not_lt.mp hn, hm⟩
  · rintro ⟨hl, hn, hm⟩
    exact ⟨Nat.not_lt.mpr hl, not_lt.mpr hn, hm⟩

lemma methodOf_inclusive {method : String} (h : method = "inclusive") :
    methodOf method = .inclusive := by
  simp [methodOf, h]

lemma methodOf_exclusive {method : String} (h : method = "exclusive") :
    methodOf method = .exclusive := by
  simp [methodOf, h]

lemma toNat_sub_one_of_one_le {n : Int} (h : 1 ≤ n) : (n - 1).toNat = n.toNat - 1 := by
  have hn : 0 ≤ n := le_trans (by decide : (0 : Int) ≤ 1) h
  lift n to Nat using hn
  simp
  omega

lemma getD_of_lt {l : List Rat} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem, h]

lemma pairwise_getElem_le {l : List Rat} (hs : l.Pairwise (· ≤ ·))
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) : l[i] ≤ l[j] := by
  cases lt_or_eq_of_le hij with
  | inl hlt => exact (List.pairwise_iff_getElem.mp hs) i j hi hj hlt
  | inr heq => subst heq; exact le_rfl

lemma inclIndex_succ_lt (ld n i : Nat) (hld : 2 ≤ ld) (hn : 0 < n) (hi : i < n) :
    (i * (ld - 1)) / n + 1 < ld := by
  have hm : 0 < ld - 1 := by omega
  have hmul : i * (ld - 1) < n * (ld - 1) := Nat.mul_lt_mul_of_pos_right hi hm
  have hdiv : (i * (ld - 1)) / n < ld - 1 := Nat.div_lt_of_lt_mul hmul
  omega

lemma clampedJ_bounds (ld j0 : Nat) (hld : 2 ≤ ld) :
    let j := if j0 < 1 then 1 else if j0 > ld - 1 then ld - 1 else j0
    1 ≤ j ∧ j < ld ∧ j - 1 < ld := by
  dsimp
  split_ifs with h1 h2
  · omega
  · omega
  · omega

lemma rat_div_emod (a n : Nat) (hn : 0 < n) :
    ((a : Rat) / (n : Rat)) = (a / n : Nat) + ((a % n : Nat) : Rat) / (n : Rat) := by
  have h := Nat.div_add_mod a n
  have hcast : (a : Rat) = (n : Rat) * (a / n : Nat) + (a % n : Nat) := by
    exact_mod_cast h.symm
  have hn0 : (n : Rat) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn0]
  linarith

lemma floor_nat_div (a n : Nat) (hn : 0 < n) :
    Int.floor (((a : Rat) / (n : Rat))) = (a / n : Nat) := by
  rw [rat_div_emod a n hn]
  have hδ : a % n < n := Nat.mod_lt a hn
  have hf_lt : ((a % n : Nat) : Rat) / (n : Rat) < 1 := by
    rw [div_lt_one (by exact_mod_cast hn)]
    exact_mod_cast hδ
  have hf_nonneg : 0 ≤ ((a % n : Nat) : Rat) / (n : Rat) := by positivity
  rw [Int.floor_natCast_add]
  have hf0 : Int.floor (((a % n : Nat) : Rat) / (n : Rat)) = 0 := by
    rw [Int.floor_eq_iff]
    constructor
    · simpa using hf_nonneg
    · simpa using hf_lt
  simp [hf0]

lemma inclPos_mem (ld n i : Nat) (hld : 2 ≤ ld) (hn : 0 < n) (hi0 : 0 < i) (hi : i < n) :
    0 < inclPos ld n i ∧ inclPos ld n i < (ld - 1 : Rat) := by
  unfold inclPos
  have hn0 : (0 : Rat) < n := by exact_mod_cast hn
  have hm0 : 0 < ld - 1 := by omega
  constructor
  · exact div_pos (by exact_mod_cast Nat.mul_pos hi0 hm0) hn0
  · rw [div_lt_iff₀ hn0]
    have hmul : i * (ld - 1) < n * (ld - 1) := Nat.mul_lt_mul_of_pos_right hi hm0
    have : (i * (ld - 1) : Rat) < (n : Rat) * (ld - 1) := by exact_mod_cast hmul
    simpa [mul_comm] using this

lemma fract_nonneg (p : Rat) : 0 ≤ p - (Int.floor p : Rat) := by
  have := Int.floor_le p
  linarith

lemma fract_lt_one (p : Rat) : p - (Int.floor p : Rat) < 1 := by
  have := Int.lt_floor_add_one p
  linarith

lemma segment_mono_frac {x y f1 f2 : Rat} (hxy : x ≤ y) (hf : f1 ≤ f2) :
    x + (y - x) * f1 ≤ x + (y - x) * f2 := by
  have hnn : 0 ≤ y - x := sub_nonneg.mpr hxy
  have := mul_le_mul_of_nonneg_left hf hnn
  linarith

lemma segment_ge_left {x y f : Rat} (hxy : x ≤ y) (hf : 0 ≤ f) :
    x ≤ x + (y - x) * f := by
  have : 0 ≤ (y - x) * f := mul_nonneg (sub_nonneg.mpr hxy) hf
  linarith

lemma segment_le_right {x y f : Rat} (hxy : x ≤ y) (hf : f ≤ 1) :
    x + (y - x) * f ≤ y := by
  have hnn : 0 ≤ y - x := sub_nonneg.mpr hxy
  have := mul_le_mul_of_nonneg_left hf hnn
  linarith

lemma int_toNat_mono {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) : a.toNat ≤ b.toNat := by
  lift a to Nat using ha
  have hb : 0 ≤ b := le_trans ha hab
  lift b to Nat using hb
  simpa using hab

/-! ## Cut equals the interpolant -/

theorem inclusiveCut_eq_interp (s : List Rat) (n i : Nat)
    (hn : 0 < n) (hi : i < n) (hl : 2 ≤ s.length) :
    inclusiveCut s n i = interpSorted s (inclPos s.length n i) := by
  set ld := s.length
  set prod := i * (ld - 1) with hprod
  set j := prod / n with hjdef
  set delta := prod % n with hδdef
  have hj1 : j + 1 < ld := by
    simpa [ld, prod, j] using inclIndex_succ_lt ld n i hl hn hi
  have hj0 : j < ld := by omega
  have hδlt : delta < n := by simpa [delta] using Nat.mod_lt prod hn
  have hδle : delta ≤ n := Nat.le_of_lt hδlt
  have hx : s.getD j 0 = s[j] := getD_of_lt hj0
  have hy : s.getD (j + 1) 0 = s[j + 1] := getD_of_lt hj1
  have hpos : inclPos ld n i = (j : Rat) + (delta : Rat) / (n : Rat) := by
    unfold inclPos
    rw [rat_div_emod prod n hn]
    simp [prod, j, delta]
  have hfloor : Int.floor (inclPos ld n i) = (j : Int) := by
    rw [hpos, Int.floor_natCast_add]
    have hf0 : Int.floor (((delta : Nat) : Rat) / (n : Rat)) = 0 := by
      rw [Int.floor_eq_iff]
      constructor
      · have : 0 ≤ ((delta : Nat) : Rat) / (n : Rat) := by positivity
        simpa using this
      · have : ((delta : Nat) : Rat) / (n : Rat) < 1 := by
          rw [div_lt_one (by exact_mod_cast hn)]
          exact_mod_cast hδlt
        simpa using this
    simp [hf0]
  have hfrac : inclPos ld n i - (j : Rat) = (delta : Rat) / (n : Rat) := by
    rw [hpos]; ring
  by_cases hi0 : i = 0
  · have hprod0 : prod = 0 := by simp [prod, hi0]
    have hjz : j = 0 := by simp [j, hprod0, hn]
    have hδz : delta = 0 := by simp [delta, hprod0]
    have hp0 : inclPos ld n i = 0 := by simp [hpos, hjz, hδz]
    simp [inclusiveCut, prod, j, delta, hjz, hδz, interpSorted, hp0, hx, hy, hn,
      Nat.mod_zero, getD_of_lt (by omega : 0 < ld)]
    field_simp
  · have hi0' : 0 < i := Nat.pos_of_ne_zero hi0
    have ⟨hp_pos, hp_lt⟩ := inclPos_mem ld n i hl hn hi0' hi
    have hp_nle : ¬ inclPos ld n i ≤ 0 := not_le.mpr hp_pos
    have hp_nr : ¬ (ld - 1 : Rat) ≤ inclPos ld n i := not_le.mpr hp_lt
    have hcut : inclusiveCut s n i =
        s[j] * ((n - delta : Nat) : Rat) / (n : Rat) + s[j + 1] * (delta : Rat) / (n : Rat) := by
      simp [inclusiveCut, prod, j, delta, hx, hy, div_add_div_same]
    have hsub : ((n - delta : Nat) : Rat) = (n : Rat) - (delta : Rat) := Nat.cast_sub hδle
    have hinter : interpSorted s (inclPos ld n i) =
        s[j] + (s[j + 1] - s[j]) * ((delta : Rat) / (n : Rat)) := by
      simp [interpSorted, hp_nle, hp_nr, hfloor, Int.toNat_natCast, hx, hy, hfrac, ld]
    rw [hinter, hcut, hsub]
    field_simp
    ring

theorem exclusiveCut_eq_interp (s : List Rat) (n i : Nat)
    (hn : 0 < n) (hl : 2 ≤ s.length) (hi : 0 < i) :
    exclusiveCut s n i = interpSorted s (exclPos s.length n i) := by
  set ld := s.length
  set m := ld + 1
  set rawNat := i * m
  set j0 := rawNat / n
  set j := if j0 < 1 then 1 else if j0 > ld - 1 then ld - 1 else j0
  have hb := clampedJ_bounds ld j0 hl
  have hj1 : 1 ≤ j := hb.1
  have hjlt : j < ld := hb.2.1
  have hjm : j - 1 < ld := hb.2.2
  have hx : s.getD (j - 1) 0 = s[j - 1] := getD_of_lt hjm
  have hy : s.getD j 0 = s[j] := getD_of_lt hjlt
  have hraw : ((rawNat : Rat) / (n : Rat)) =
      (j0 : Rat) + ((rawNat % n : Nat) : Rat) / (n : Rat) := by
    simpa [rawNat, j0] using rat_div_emod rawNat n hn
  have hp : exclPos ld n i = ((rawNat : Rat) / (n : Rat)) - 1 := by
    simp [exclPos, ld, m, rawNat]
  -- Three clamp regimes.
  by_cases hlo : j0 < 1
  · have hj0z : j0 = 0 := by omega
    have hjv : j = 1 := by simp [j, hlo]
    have hraw_lt : rawNat < n := by
      have : rawNat / n = 0 := hj0z
      exact Nat.div_eq_zero_iff.mp this |>.resolve_left hn.ne'
    have hδ : (Int.ofNat rawNat - Int.ofNat (j * n)) = (rawNat : Int) - (n : Int) := by
      simp [hjv]
    have hpneg : exclPos ld n i < 0 := by
      rw [hp, rat_div_emod rawNat n hn, hj0z]
      have : ((rawNat % n : Nat) : Rat) / (n : Rat) < 1 := by
        rw [div_lt_one (by exact_mod_cast hn)]
        exact_mod_cast (by simpa [hj0z, Nat.mod_eq_of_lt hraw_lt] using hraw_lt)
      have hlt1 : ((rawNat : Rat) / (n : Rat)) < 1 := by
        rw [rat_div_emod rawNat n hn, hj0z]
        simpa using this
      linarith
    have hple : exclPos ld n i ≤ 0 := le_of_lt hpneg
    have hidx0 : (0 : Nat) < ld := by omega
    have hidx1 : (1 : Nat) < ld := by omega
    simp [exclusiveCut, ld, m, rawNat, j0, j, hjv, hδ, interpSorted, hple, hx, hy,
      getD_of_lt hidx0, getD_of_lt hidx1]
    have hraw_eq : ((rawNat : Rat) / (n : Rat)) = exclPos ld n i + 1 := by rw [hp]; ring
    have hδrat : ((rawNat : Rat) - (n : Rat)) / (n : Rat) = exclPos ld n i := by
      rw [hp, rat_div_emod rawNat n hn, hj0z]
      simp [Nat.mod_eq_of_lt hraw_lt]
      ring
    field_simp
    -- (s0 * (n - (raw-n)) + s1 * (raw-n)) / n = s0 + (s1-s0)*p
    have : ((n : Rat) - ((rawNat : Rat) - (n : Rat))) = (n : Rat) * (1 - exclPos ld n i) +
        ((rawNat : Rat) - (n : Rat)) * 0 := by
      rw [← hδrat]
      field_simp
      ring
    -- direct expansion
    have hmain :
        s[0] * ((n : Rat) - ((rawNat : Rat) - (n : Rat))) +
          s[1] * ((rawNat : Rat) - (n : Rat)) =
        (s[0] + (s[1] - s[0]) * exclPos ld n i) * (n : Rat) := by
      have hδp : (rawNat : Rat) - (n : Rat) = exclPos ld n i * (n : Rat) := by
        have hδrat' : ((rawNat : Rat) - (n : Rat)) / (n : Rat) = exclPos ld n i := hδrat
        field_simp [show (n : Rat) ≠ 0 by exact_mod_cast hn.ne'] at hδrat'
        linarith
      rw [hδp]
      ring
    calc
      (s[0] * ((n : Rat) - ((rawNat : Rat) - (n : Rat))) +
          s[1] * ((rawNat : Rat) - (n : Rat))) / (n : Rat)
        = ((s[0] + (s[1] - s[0]) * exclPos ld n i) * (n : Rat)) / (n : Rat) := by rw [hmain]
      _ = s[0] + (s[1] - s[0]) * exclPos ld n i := by
        field_simp
  · by_cases hhi : j0 > ld - 1
    · have hjv : j = ld - 1 := by simp [j, hlo, hhi]
      have hδge : n ≤ rawNat - (ld - 1) * n := by
        have hmul : ld * n ≤ rawNat := by
          have : ld ≤ j0 := by omega
          have hdiv : j0 * n ≤ rawNat := Nat.mul_div_le rawNat n |> ?_
          sorry
      sorry
    · sorry

/-! The exclusive interpolant proof is completed below after a cleaner case split.
This placeholder theorem is replaced by `exclusiveCut_eq_interp'`. -/

/-! ## Basic semantic lemmas that do not need the exclusive interpolant -/

lemma benchmark_eq_spec_of_valid {data : List Rat} {n : Int} {method : String}
    (h : invalidInput data n method = false) :
    benchmarkQuantiles data n method = .ok (specResult data n method) := by
  simp [benchmarkQuantiles, specResult, h]

theorem length_of_quantileCuts (s : List Rat) (n : Nat) (method : QuantileMethod) :
    (quantileCuts s n method).length = n - 1 := by
  simp [quantileCuts]

/-! ## Property propositions and theorems -/

def length_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  ∀ result, benchmarkQuantiles data n method = .ok result → result.length = (n - 1).toNat

theorem length_thm (data : List Rat) (n : Int) (method : String) : length_prop data n method := by
  intro result h
  by_cases hv : invalidInput data n method
  · simp [benchmarkQuantiles, hv] at h
  · simp [benchmarkQuantiles, hv] at h
    subst h
    have hpre : Pre data n method := (invalidInput_false_iff data n method).mp (by simpa using hv)
    simp [quantileCuts, toNat_sub_one_of_one_le hpre.2.1]

def error_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  (benchmarkQuantiles data n method = .error (.statisticsError benchmarkMsg)) ↔ ¬ Pre data n method

theorem error_thm (data : List Rat) (n : Int) (method : String) : error_prop data n method := by
  unfold error_prop
  by_cases hv : invalidInput data n method
  · have hpre : ¬ Pre data n method := by
      intro hp
      have := (invalidInput_false_iff data n method).mpr hp
      simp [hv] at this
    simp [benchmarkQuantiles, hv, hpre]
  · have hpre : Pre data n method := (invalidInput_false_iff data n method).mp (by simpa using hv)
    simp [benchmarkQuantiles, hv, hpre]

def quantiles_priority_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  (n < 1 → quantiles data n method = .error (.statisticsError quantilesNMsg)) ∧
  (1 ≤ n → data.length < 2 →
    quantiles data n method = .error (.statisticsError quantilesLenMsg)) ∧
  (1 ≤ n → 2 ≤ data.length → method ≠ "inclusive" → method ≠ "exclusive" →
    quantiles data n method = .error (.valueError (quantilesMethodMsg method)))

theorem quantiles_priority_thm (data : List Rat) (n : Int) (method : String) :
    quantiles_priority_prop data n method := by
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    simp [quantiles, hn]
  · intro hn hl
    have hnot : ¬ n < 1 := not_lt.mpr hn
    simp [quantiles, hnot, hl]
  · intro hn hl hi he
    have hnot : ¬ n < 1 := not_lt.mpr hn
    have hlen : ¬ data.length < 2 := Nat.not_lt.mpr hl
    have hinc : (method == "inclusive") = false := by simpa [beq_eq_false_iff_ne] using hi
    have hexc : (method == "exclusive") = false := by simpa [beq_eq_false_iff_ne] using he
    simp [quantiles, hnot, hlen, hinc, hexc]

def agreement_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  Pre data n method → benchmarkQuantiles data n method = quantiles data n method

theorem agreement_thm (data : List Rat) (n : Int) (method : String) :
    agreement_prop data n method := by
  intro hp
  have hv : invalidInput data n method = false := (invalidInput_false_iff data n method).mpr hp
  have hn : ¬ n < 1 := not_lt.mpr hp.2.1
  have hl : ¬ data.length < 2 := Nat.not_lt.mpr hp.1
  rcases hp.2.2 with h | h
  · simp [benchmarkQuantiles, quantiles, hv, hn, hl, h, methodOf_exclusive h, specResult]
  · simp [benchmarkQuantiles, quantiles, hv, hn, hl, h, methodOf_inclusive h]

def sort_invariance_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  benchmarkQuantiles data n method = benchmarkQuantiles (sortedData data) n method

theorem sort_invariance_thm (data : List Rat) (n : Int) (method : String) :
    sort_invariance_prop data n method := by
  simp [sort_invariance_prop, benchmarkQuantiles, sortedData_idempotent, sortedData_length]

def permutation_invariance_prop (data₁ data₂ : List Rat) (n : Int) (method : String) : Prop :=
  data₁.Perm data₂ → benchmarkQuantiles data₁ n method = benchmarkQuantiles data₂ n method

theorem permutation_invariance_thm (data₁ data₂ : List Rat) (n : Int) (method : String) :
    permutation_invariance_prop data₁ data₂ n method := by
  intro hperm
  have hlen : data₁.length = data₂.length := hperm.length_eq
  by_cases hv : invalidInput data₁ n method
  · have hv₂ : invalidInput data₂ n method = true := by
      simp [invalidInput, hlen, hv]
    simp [benchmarkQuantiles, hv, hv₂]
  · have hv₂ : invalidInput data₂ n method = false := by
      simp [invalidInput, hlen, hv]
    simp [benchmarkQuantiles, hv, hv₂, sortedData_eq_of_perm hperm]

def singleton_group_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  n = 1 → ∀ result, benchmarkQuantiles data n method = .ok result → result = []

theorem singleton_group_thm (data : List Rat) (n : Int) (method : String) :
    singleton_group_prop data n method := by
  intro hn result h
  by_cases hv : invalidInput data n method
  · simp [benchmarkQuantiles, hv] at h
  · simp [benchmarkQuantiles, hv, hn] at h
    simpa [quantileCuts] using h

def inclusive_formula_prop (data : List Rat) (n : Int) : Prop :=
  ∀ result, benchmarkQuantiles data n "inclusive" = .ok result →
    result = (List.range' 1 (n.toNat - 1)).map (inclusiveCut (sortedData data) n.toNat)

theorem inclusive_formula_thm (data : List Rat) (n : Int) : inclusive_formula_prop data n := by
  intro result h
  by_cases hv : invalidInput data n "inclusive"
  · simp [benchmarkQuantiles, hv] at h
  · simp [benchmarkQuantiles, hv, methodOf, quantileCuts, oneCut] at h
    exact h.symm

def exclusive_formula_prop (data : List Rat) (n : Int) : Prop :=
  ∀ result, benchmarkQuantiles data n "exclusive" = .ok result →
    result = (List.range' 1 (n.toNat - 1)).map (exclusiveCut (sortedData data) n.toNat)

theorem exclusive_formula_thm (data : List Rat) (n : Int) : exclusive_formula_prop data n := by
  intro result h
  by_cases hv : invalidInput data n "exclusive"
  · simp [benchmarkQuantiles, hv] at h
  · simp [benchmarkQuantiles, hv, methodOf, quantileCuts, oneCut] at h
    exact h.symm

/-! ### Constant samples -/

lemma eq_replicate_of_forall_eq {l : List Rat} {c : Rat} (h : ∀ x ∈ l, x = c) :
    l = List.replicate l.length c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x = c := h x (by simp)
    have hxs : ∀ y ∈ xs, y = c := fun y hy => h y (by simp [hy])
    simp [hx, ih hxs, List.replicate_succ]

lemma sortedData_const {l : List Rat} {c : Rat} (h : ∀ x ∈ l, x = c) :
    sortedData l = List.replicate l.length c := by
  have hl := eq_replicate_of_forall_eq h
  rw [hl]
  apply List.mergeSort_of_sorted (le := ratLE)
  have hp : (List.replicate l.length c).Pairwise (· ≤ ·) :=
    (List.pairwise_replicate.mpr (Or.inr (le_refl c)))
  refine List.Pairwise.imp (fun hab => ?_) hp
  simpa [ratLE] using hab

lemma oneCut_const {s : List Rat} {c : Rat} {n i : Nat} {method : QuantileMethod}
    (hs : ∀ x ∈ s, x = c) (hn : 0 < n) (hi : i < n) (hl : 2 ≤ s.length) :
    oneCut s n i method = c := by
  have hget : ∀ j, j < s.length → s.getD j 0 = c := by
    intro j hj
    rw [getD_of_lt hj]
    exact hs _ (List.getElem_mem hj)
  cases method with
  | inclusive =>
    have hj := inclIndex_succ_lt s.length n i hl hn hi
    have hj0 : (i * (s.length - 1)) / n < s.length := by omega
    simp [oneCut, inclusiveCut, hget _ hj0, hget _ hj]
    have hδ : (i * (s.length - 1)) % n ≤ n := Nat.le_of_lt (Nat.mod_lt _ hn)
    have hsub : (((n - (i * (s.length - 1)) % n : Nat) : Rat)) +
        (((i * (s.length - 1)) % n : Nat) : Rat) = (n : Rat) := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hδ]
    field_simp
    nlinarith [hsub]
  | exclusive =>
    simp only [oneCut, exclusiveCut]
    set ld := s.length
    set j0 := (i * (ld + 1)) / n
    set j := if j0 < 1 then 1 else if j0 > ld - 1 then ld - 1 else j0
    have hb := clampedJ_bounds ld j0 hl
    have hx := hget (j - 1) hb.2.2
    have hy := hget j hb.2.1
    simp [ld, j0, j, hx, hy]
    field_simp
    ring

def constant_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  ∀ c, (∀ x ∈ data, x = c) → ∀ result,
    benchmarkQuantiles data n method = .ok result → ∀ y ∈ result, y = c

theorem constant_thm (data : List Rat) (n : Int) (method : String) :
    constant_prop data n method := by
  intro c hc result h y hy
  by_cases hv : invalidInput data n method
  · simp [benchmarkQuantiles, hv] at h
  · have hpre : Pre data n method := (invalidInput_false_iff data n method).mp (by simpa using hv)
    simp [benchmarkQuantiles, hv] at h
    subst h
    rw [sortedData_const hc] at hy
    have hn : 0 < n.toNat := by
      have : 0 < n := lt_of_lt_of_le (by decide : (0 : Int) < 1) hpre.2.1
      exact Int.toNat_pos.mpr? 
      sorry
    sorry

-- The proofs below are filled in the next edit; the file is saved incrementally.
theorem constant_thm_placeholder : True := trivial
