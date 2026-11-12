import Mathlib

/-!
# VeriBench 31: statistics.quantiles

Formalization of Python's `statistics.quantiles` and the `benchmark_quantiles` wrapper.

The mathematical intent is exact linear interpolation of sample (exclusive) or population
(inclusive) quantiles, as in Python `Fraction` / `Decimal` inputs — not IEEE-754 rounding.
Theorems are stated over `Rat`. `FloatLayer` repeats the algorithm for ground checks against
CPython's documented float outputs.

Inclusive: `m = length - 1`, cut `i` uses `divmod(i * m, n)`.
Exclusive (default): `m = length + 1`, raw index `(i * m) // n` is clamped to `1 .. length - 1`,
and `delta = i*m - j*n` may be negative, so cuts may extrapolate past the data range.
-/

namespace «31_statistics_quantiles»

/-! ## Implementation -/

inductive QuantileMethod
  | exclusive
  | inclusive
  deriving DecidableEq, Repr, BEq, Inhabited

def benchmarkErrorMsg : String :=
  "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"

def errNTooSmall : String := "n must be at least 1"

def errInsufficient : String := "must have at least two data points"

def errUnknownMethod (method : String) : String :=
  "Unknown method: '" ++ method ++ "'"

def sortData (data : List Rat) : List Rat :=
  data.mergeSort (· ≤ ·)

/-- Python `j, delta = divmod(i * (len(data) - 1), n)`. -/
def inclJ (data : List Rat) (n i : Nat) : Nat :=
  (i * (data.length - 1)) / n

def inclDelta (data : List Rat) (n i : Nat) : Nat :=
  (i * (data.length - 1)) % n

def inclusiveCut (data : List Rat) (n i : Nat) : Rat :=
  (data.getD (inclJ data n i) 0 * ((n - inclDelta data n i : Nat) : Rat) +
    data.getD (inclJ data n i + 1) 0 * ((inclDelta data n i : Nat) : Rat)) / (n : Rat)

/-- Clamp Python's raw exclusive index into `1 .. ld - 1`. -/
def clampIndex (ld jRaw : Nat) : Nat :=
  if jRaw < 1 then 1 else if jRaw > ld - 1 then ld - 1 else jRaw

def exclJ (data : List Rat) (n i : Nat) : Nat :=
  clampIndex data.length ((i * (data.length + 1)) / n)

def exclDelta (data : List Rat) (n i : Nat) : Int :=
  (i * (data.length + 1) : Int) - (exclJ data n i : Int) * (n : Int)

def exclusiveCut (data : List Rat) (n i : Nat) : Rat :=
  (data.getD (exclJ data n i - 1) 0 * ((n : Rat) - (exclDelta data n i : Rat)) +
    data.getD (exclJ data n i) 0 * (exclDelta data n i : Rat)) / (n : Rat)

def cutAt (data : List Rat) (n : Nat) (method : QuantileMethod) (i : Nat) : Rat :=
  match method with
  | .inclusive => inclusiveCut data n i
  | .exclusive => exclusiveCut data n i

def cuts (data : List Rat) (n : Nat) (method : QuantileMethod) : List Rat :=
  (List.range' 1 (n - 1)).map (cutAt data n method)

def quantiles (data : List Rat) (n : Nat := 4) (method : QuantileMethod := .exclusive) : List Rat :=
  cuts (sortData data) n method

def decodeMethod (method : String) : QuantileMethod :=
  if method = "inclusive" then .inclusive else .exclusive

def preBool (data : List Rat) (n : Int) (method : String) : Bool :=
  decide (2 ≤ data.length) && decide (1 ≤ n) &&
    (decide (method = "exclusive") || decide (method = "inclusive"))

def benchmarkQuantiles (data : List Rat) (n : Int := 4) (method : String := "exclusive") :
    Except String (List Rat) :=
  if preBool data n method then
    .ok (quantiles data n.toNat (decodeMethod method))
  else
    .error benchmarkErrorMsg

/-- Python `quantiles` error order: `n`, then length, then method. -/
def quantilesChecked (data : List Rat) (n : Int) (method : String) : Except String (List Rat) :=
  if n < 1 then
    .error errNTooSmall
  else if data.length < 2 then
    .error errInsufficient
  else if method = "inclusive" then
    .ok (quantiles data n.toNat .inclusive)
  else if method = "exclusive" then
    .ok (quantiles data n.toNat .exclusive)
  else
    .error (errUnknownMethod method)

/-- Sample median used by exclusive `n = 2`: average of the two central points if the
length is even, otherwise the middle point. -/
def sampleMedian (data : List Rat) : Rat :=
  let s := sortData data
  let mid := s.length / 2
  if s.length % 2 = 0 then (s.getD (mid - 1) 0 + s.getD mid 0) / 2 else s.getD mid 0

instance : DecidableEq (Except String (List Rat)) := fun a b =>
  match a, b with
  | .error x, .error y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (fun h' => by cases h'; exact h rfl)
  | .ok x, .ok y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (fun h' => by cases h'; exact h rfl)
  | .error _, .ok _ => isFalse (fun h => by cases h)
  | .ok _, .error _ => isFalse (fun h => by cases h)

namespace FloatLayer

def floatLE (a b : Float) : Bool := decide (a ≤ b)

def floatOfInt (z : Int) : Float :=
  if z < 0 then -Float.ofNat z.natAbs else Float.ofNat z.toNat

def getF (data : List Float) (i : Nat) : Float :=
  data.getD i 0.0

def inclusiveCut (data : List Float) (n i : Nat) : Float :=
  let m := data.length - 1
  let prod := i * m
  let j := prod / n
  let delta := prod % n
  (getF data j * Float.ofNat (n - delta) + getF data (j + 1) * Float.ofNat delta) / Float.ofNat n

def exclusiveCut (data : List Float) (n i : Nat) : Float :=
  let ld := data.length
  let m := ld + 1
  let jRaw := (i * m) / n
  let j := if jRaw < 1 then 1 else if jRaw > ld - 1 then ld - 1 else jRaw
  let delta : Int := (i * m : Int) - (j : Int) * (n : Int)
  (getF data (j - 1) * floatOfInt ((n : Int) - delta) + getF data j * floatOfInt delta) / Float.ofNat n

def quantiles (data : List Float) (n : Nat := 4) (method : QuantileMethod := .exclusive) : List Float :=
  let sorted := data.mergeSort floatLE
  (List.range' 1 (n - 1)).map fun i =>
    match method with
    | .inclusive => inclusiveCut sorted n i
    | .exclusive => exclusiveCut sorted n i

def floatAbs (x : Float) : Float :=
  if x < 0 then -x else x

def floatsClose (a b : Float) : Bool :=
  floatAbs (a - b) < 1e-9

def listsClose (xs ys : List Float) : Bool :=
  xs.length == ys.length && (xs.zip ys).all (fun p => floatsClose p.1 p.2)

def ratToFloat (q : Rat) : Float :=
  floatOfInt q.num / Float.ofNat q.den

end FloatLayer

/-! ## Unit tests -/

example : quantiles [1, 2, 3, 4] = [5/4, 5/2, 15/4] := by native_decide
example : quantiles [1, 2, 3, 4] 4 .exclusive = [5/4, 5/2, 15/4] := by native_decide
example : quantiles [1, 2, 3, 4] 4 .inclusive = [7/4, 5/2, 13/4] := by native_decide
example : quantiles [1, 2, 3, 4, 5] 2 .exclusive = [3] := by native_decide
example : quantiles [1, 2, 3, 4, 5, 6] 2 .exclusive = [7/2] := by native_decide
example : quantiles [1, 2] 4 .exclusive = [3/4, 3/2, 9/4] := by native_decide
example : quantiles [1, 2] 4 .inclusive = [5/4, 3/2, 7/4] := by native_decide
example : quantiles [4, 1, 3, 2] 4 = quantiles [1, 2, 3, 4] := by native_decide
example : quantiles ((List.range 11).map (fun k => (k : Rat))) 10 .exclusive =
    [1/5, 7/5, 13/5, 19/5, 5, 31/5, 37/5, 43/5, 49/5] := by native_decide
example : quantiles ((List.range' 1 10).map (fun k => (k : Rat))) 4 .exclusive =
    [11/4, 11/2, 33/4] := by native_decide
example : quantiles [3/2, 5/2, 7/2, 9/2] 2 .exclusive = [3] := by native_decide
example : quantiles [1, 2, 3] 3 .exclusive = [4/3, 8/3] := by native_decide
example : quantiles [1, 2, 3] 3 .inclusive = [5/3, 7/3] := by native_decide
example : quantiles [5, 5, 5, 5] 4 .exclusive = [5, 5, 5] := by native_decide
example : quantiles [1, 2, 3, 4] 1 .exclusive = [] := by native_decide
example : (quantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10).length = 9 := by native_decide
example : benchmarkQuantiles [1] 4 "exclusive" = .error benchmarkErrorMsg := by native_decide
example : benchmarkQuantiles [1, 2] 0 "exclusive" = .error benchmarkErrorMsg := by native_decide
example : benchmarkQuantiles [1, 2] (-3) "inclusive" = .error benchmarkErrorMsg := by native_decide
example : benchmarkQuantiles [1, 2, 3] 4 "invalid" = .error benchmarkErrorMsg := by native_decide
example : benchmarkQuantiles [1, 2, 3, 4] 4 "exclusive" = .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmarkQuantiles [1, 2, 3, 4] 4 "inclusive" = .ok [7/4, 5/2, 13/4] := by native_decide
example : quantilesChecked [1, 2] 0 "exclusive" = .error errNTooSmall := by native_decide
example : quantilesChecked [1] 4 "exclusive" = .error errInsufficient := by native_decide
example : quantilesChecked [1, 2, 3] 4 "invalid" = .error (errUnknownMethod "invalid") := by native_decide
example : quantilesChecked [1, 2, 3, 4] 4 "exclusive" = .ok [5/4, 5/2, 15/4] := by native_decide

#eval quantiles [1, 2, 3, 4]
#eval quantiles [1, 2, 3, 4] 4 .inclusive
#eval quantiles [1, 2, 3, 4, 5] 2
#eval benchmarkQuantiles [1] 4 "exclusive"
#eval FloatLayer.quantiles [1, 2, 3, 4] 4 .exclusive
#eval FloatLayer.quantiles [1, 2, 3, 4] 4 .inclusive
#eval FloatLayer.quantiles [1.5, 2.5, 3.5, 4.5] 2 .exclusive

example : FloatLayer.listsClose (FloatLayer.quantiles [1, 2, 3, 4] 4 .exclusive) [1.25, 2.5, 3.75] = true := by
  native_decide
example : FloatLayer.listsClose (FloatLayer.quantiles [1, 2, 3, 4] 4 .inclusive) [1.75, 2.5, 3.25] = true := by
  native_decide
example : FloatLayer.listsClose (FloatLayer.quantiles [1, 2, 3, 4, 5] 2 .exclusive) [3.0] = true := by
  native_decide
example : FloatLayer.listsClose (FloatLayer.quantiles [1.5, 2.5, 3.5, 4.5] 2) [3.0] = true := by
  native_decide
example : FloatLayer.listsClose (FloatLayer.quantiles [1, 2, 3, 4] 4 .exclusive)
    ((quantiles [1, 2, 3, 4] 4 .exclusive).map FloatLayer.ratToFloat) = true := by native_decide

-- Float universal laws are not kernel-reducible. The examples above are the executable
-- Float-layer checks of Python's documented outputs and of the Rat model.

/-! ## Pre-condition -/

/-- Python `pre`: at least two points, `n >= 1`, and method in {exclusive, inclusive}. -/
def Pre (data : List Rat) (n : Int) (method : String) : Prop :=
  2 ≤ data.length ∧ 1 ≤ n ∧ (method = "exclusive" ∨ method = "inclusive")


theorem preBool_iff_Pre (data : List Rat) (n : Int) (method : String) :
    preBool data n method = true ↔ Pre data n method := by
  unfold preBool Pre
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h11, h12⟩ := h1
    exact ⟨h11, h12, h2⟩
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨⟨h1, h2⟩, h3⟩

/-! ## Properties and theorems -/

theorem sortData_sorted (data : List Rat) : (sortData data).Sorted (· ≤ ·) :=
  List.sorted_mergeSort' (· ≤ ·) data

theorem sortData_perm (data : List Rat) : List.Perm (sortData data) data := by
  simpa [sortData] using List.mergeSort_perm data (fun a b => decide (a ≤ b))

theorem sortData_length (data : List Rat) : (sortData data).length = data.length := by
  simp [sortData, List.length_mergeSort]

theorem sortData_idem (data : List Rat) : sortData (sortData data) = sortData data := by
  simpa [sortData] using
    (List.mergeSort_eq_self (r := (· ≤ ·)) (List.sorted_mergeSort' (· ≤ ·) data))

theorem sortData_of_sorted (data : List Rat) (hs : data.Sorted (· ≤ ·)) :
    sortData data = data := by
  simpa [sortData] using List.mergeSort_eq_self (r := (· ≤ ·)) hs

theorem sorted_getElem_le {data : List Rat} (hs : data.Sorted (· ≤ ·))
    {i j : Nat} (hij : i ≤ j) (hj : j < data.length) :
    data[i]'(Nat.lt_of_le_of_lt hij hj) ≤ data[j] := by
  have hi : i < data.length := Nat.lt_of_le_of_lt hij hj
  have hfin : (⟨i, hi⟩ : Fin data.length) ≤ ⟨j, hj⟩ := by
    simp [Fin.le_def, hij]
  simpa using hs.rel_get_of_le hfin

theorem getD_le_getD {data : List Rat} (hs : data.Sorted (· ≤ ·))
    {i j : Nat} (hij : i ≤ j) (hj : j < data.length) :
    data.getD i 0 ≤ data.getD j 0 := by
  rw [List.getD_eq_getElem data 0 (Nat.lt_of_le_of_lt hij hj), List.getD_eq_getElem data 0 hj]
  exact sorted_getElem_le hs hij hj

theorem get_of_const (data : List Rat) (c : Rat) (i : Nat)
    (hall : ∀ x ∈ data, x = c) (hi : i < data.length) : data[i] = c :=
  hall _ (List.getElem_mem hi)

theorem inclusive_j_succ_lt (ld n i : Nat) (hld : 2 ≤ ld) (hn : 0 < n) (hi : i < n) :
    (i * (ld - 1)) / n + 1 < ld := by
  have hm : 0 < ld - 1 := by omega
  have hmul : i * (ld - 1) < n * (ld - 1) := Nat.mul_lt_mul_of_pos_right hi hm
  have hj : (i * (ld - 1)) / n < ld - 1 := Nat.div_lt_of_lt_mul hmul
  omega

theorem nat_weighted_const (c : Rat) (n delta : Nat) (hn : 0 < n) (hd : delta ≤ n) :
    (c * ((n - delta : Nat) : Rat) + c * (delta : Rat)) / (n : Rat) = c := by
  have hn0 : (n : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [Nat.cast_sub hd]
  field_simp [hn0]
  ring

theorem int_weighted_const (c : Rat) (n : Nat) (delta : Int) (hn : 0 < n) :
    (c * ((n : Rat) - (delta : Rat)) + c * (delta : Rat)) / (n : Rat) = c := by
  have hn0 : (n : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0]
  ring

theorem inclusiveCut_const (data : List Rat) (c : Rat) (n i : Nat)
    (hn : 0 < n) (hld : 2 ≤ data.length) (hi : i < n) (hall : ∀ x ∈ data, x = c) :
    inclusiveCut data n i = c := by
  have hjs : inclJ data n i + 1 < data.length := by
    simpa [inclJ] using inclusive_j_succ_lt data.length n i hld hn hi
  have hj : inclJ data n i < data.length := by omega
  unfold inclusiveCut
  rw [List.getD_eq_getElem data 0 hj, List.getD_eq_getElem data 0 hjs]
  rw [get_of_const data c _ hall hj, get_of_const data c _ hall hjs]
  exact nat_weighted_const c n (inclDelta data n i) hn
    (Nat.le_of_lt (by simpa [inclDelta] using Nat.mod_lt (i * (data.length - 1)) hn))

theorem clampIndex_bounds (ld jRaw : Nat) (hld : 2 ≤ ld) :
    1 ≤ clampIndex ld jRaw ∧ clampIndex ld jRaw ≤ ld - 1 := by
  unfold clampIndex
  split_ifs <;> omega

theorem clampIndex_of_lt_one (ld jRaw : Nat) (h : jRaw < 1) :
    clampIndex ld jRaw = 1 := by
  simp [clampIndex, h]

theorem clampIndex_of_gt (ld jRaw : Nat) (hlo : ¬ jRaw < 1) (hhi : jRaw > ld - 1) :
    clampIndex ld jRaw = ld - 1 := by
  simp [clampIndex, hlo, hhi]

theorem clampIndex_of_in (ld jRaw : Nat) (hlo : ¬ jRaw < 1) (hhi : ¬ jRaw > ld - 1) :
    clampIndex ld jRaw = jRaw := by
  simp [clampIndex, hlo, hhi]

theorem exclusiveCut_const (data : List Rat) (c : Rat) (n i : Nat)
    (hn : 0 < n) (hld : 2 ≤ data.length) (hall : ∀ x ∈ data, x = c) :
    exclusiveCut data n i = c := by
  have hb := clampIndex_bounds data.length ((i * (data.length + 1)) / n) hld
  have hj : exclJ data n i < data.length := by
    simpa [exclJ] using Nat.lt_of_le_of_lt hb.2 (by omega)
  have hjm : exclJ data n i - 1 < data.length := by
    have h1 : 1 ≤ exclJ data n i := by simpa [exclJ] using hb.1
    omega
  unfold exclusiveCut
  rw [List.getD_eq_getElem data 0 hjm, List.getD_eq_getElem data 0 hj]
  rw [get_of_const data c _ hall hjm, get_of_const data c _ hall hj]
  exact int_weighted_const c n _ hn

theorem exclJ_even (data : List Rat) (h : 2 ≤ data.length) (hpar : data.length % 2 = 0) :
    exclJ data 2 1 = data.length / 2 := by
  have heven : data.length = 2 * (data.length / 2) := by
    have hdiv := Nat.div_add_mod data.length 2
    rw [hpar] at hdiv
    omega
  set mid := data.length / 2
  have hjraw : (1 * (data.length + 1)) / 2 = mid := by
    have : data.length + 1 = 2 * mid + 1 := by omega
    rw [this]
    omega
  unfold exclJ clampIndex
  rw [hjraw]
  rw [if_neg (by omega : ¬ mid < 1)]
  rw [if_neg (by omega : ¬ mid > data.length - 1)]

theorem exclDelta_even (data : List Rat) (h : 2 ≤ data.length) (hpar : data.length % 2 = 0) :
    exclDelta data 2 1 = 1 := by
  unfold exclDelta
  rw [exclJ_even data h hpar]
  have heven : data.length = 2 * (data.length / 2) := by
    have hdiv := Nat.div_add_mod data.length 2
    rw [hpar] at hdiv
    omega
  omega

theorem exclusiveCut_median_even (data : List Rat) (h : 2 ≤ data.length) (hpar : data.length % 2 = 0) :
    exclusiveCut data 2 1 =
      (data.getD (data.length / 2 - 1) 0 + data.getD (data.length / 2) 0) / 2 := by
  unfold exclusiveCut
  rw [exclJ_even data h hpar, exclDelta_even data h hpar]
  ring

theorem exclJ_odd (data : List Rat) (h : 2 ≤ data.length) (hpar : data.length % 2 = 1) :
    exclJ data 2 1 = data.length / 2 + 1 := by
  have hodd_eq : data.length = 2 * (data.length / 2) + 1 := by
    have hdiv := Nat.div_add_mod data.length 2
    rw [hpar] at hdiv
    omega
  set mid := data.length / 2
  have hjraw : (1 * (data.length + 1)) / 2 = mid + 1 := by
    have hlen : data.length + 1 = 2 * (mid + 1) := by omega
    rw [hlen]
    have hone : 1 * (2 * (mid + 1)) = 2 * (mid + 1) := by ring
    rw [hone]
    exact Nat.mul_div_cancel_left (mid + 1) (by decide)
  unfold exclJ clampIndex
  rw [hjraw]
  rw [if_neg (by omega : ¬ mid + 1 < 1)]
  rw [if_neg (by omega : ¬ mid + 1 > data.length - 1)]

theorem exclDelta_odd (data : List Rat) (h : 2 ≤ data.length) (hpar : data.length % 2 = 1) :
    exclDelta data 2 1 = 0 := by
  unfold exclDelta
  rw [exclJ_odd data h hpar]
  have hodd_eq : data.length = 2 * (data.length / 2) + 1 := by
    have hdiv := Nat.div_add_mod data.length 2
    rw [hpar] at hdiv
    omega
  omega

theorem exclusiveCut_median_odd (data : List Rat) (h : 2 ≤ data.length) (hpar : data.length % 2 = 1) :
    exclusiveCut data 2 1 = data.getD (data.length / 2) 0 := by
  unfold exclusiveCut
  rw [exclJ_odd data h hpar, exclDelta_odd data h hpar]
  have hidx : data.length / 2 + 1 - 1 = data.length / 2 := by omega
  simp only [hidx]
  ring

theorem exclusiveCut_median (data : List Rat) (h : 2 ≤ data.length) :
    exclusiveCut data 2 1 =
      if data.length % 2 = 0 then
        (data.getD (data.length / 2 - 1) 0 + data.getD (data.length / 2) 0) / 2
      else data.getD (data.length / 2) 0 := by
  by_cases hpar : data.length % 2 = 0
  · simp [hpar, exclusiveCut_median_even data h hpar]
  · have hodd : data.length % 2 = 1 := by
      have hlt : data.length % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    simp [hpar, exclusiveCut_median_odd data h hodd]

theorem convex_bounds (a b : Rat) (n delta : Nat) (hn : 0 < n) (hd : delta ≤ n) (hab : a ≤ b) :
    a ≤ (a * ((n - delta : Nat) : Rat) + b * (delta : Rat)) / (n : Rat) ∧
      (a * ((n - delta : Nat) : Rat) + b * (delta : Rat)) / (n : Rat) ≤ b := by
  rw [Nat.cast_sub hd]
  have hn0 : (n : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnpos : 0 < (n : Rat) := by exact_mod_cast hn
  constructor
  · have hdiff : (a * ((n : Rat) - delta) + b * (delta : Rat)) / (n : Rat) - a
        = ((b - a) * (delta : Rat)) / (n : Rat) := by
      field_simp [hn0]; ring
    have hnonneg : 0 ≤ ((b - a) * (delta : Rat)) / (n : Rat) := by
      apply div_nonneg
      · exact mul_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)
      · exact le_of_lt hnpos
    linarith
  · have hdiff : b - (a * ((n : Rat) - delta) + b * (delta : Rat)) / (n : Rat)
        = ((b - a) * ((n : Rat) - delta)) / (n : Rat) := by
      field_simp [hn0]; ring
    have hnonneg : 0 ≤ ((b - a) * ((n : Rat) - delta)) / (n : Rat) := by
      apply div_nonneg
      · exact mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr (by exact_mod_cast hd))
      · exact le_of_lt hnpos
    linarith

theorem lerp_mono_delta (a b : Rat) (n d1 d2 : Nat)
    (hn : 0 < n) (hd1 : d1 ≤ n) (hd2 : d2 ≤ n) (hdd : d1 ≤ d2) (hab : a ≤ b) :
    (a * ((n - d1 : Nat) : Rat) + b * (d1 : Rat)) / (n : Rat) ≤
      (a * ((n - d2 : Nat) : Rat) + b * (d2 : Rat)) / (n : Rat) := by
  rw [Nat.cast_sub hd1, Nat.cast_sub hd2]
  have hn0 : (n : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnpos : 0 < (n : Rat) := by exact_mod_cast hn
  have hdiff :
      (a * ((n : Rat) - d2) + b * (d2 : Rat)) / (n : Rat) -
        (a * ((n : Rat) - d1) + b * (d1 : Rat)) / (n : Rat)
        = ((b - a) * ((d2 : Rat) - d1)) / (n : Rat) := by
    field_simp [hn0]; ring
  have hnonneg : 0 ≤ ((b - a) * ((d2 : Rat) - d1)) / (n : Rat) := by
    apply div_nonneg
    · exact mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr (by exact_mod_cast hdd))
    · exact le_of_lt hnpos
  linarith

theorem inclusiveCut_le (data : List Rat) (n i k : Nat)
    (hld : 2 ≤ data.length) (hn : 0 < n) (hs : data.Sorted (· ≤ ·))
    (hi : i < n) (hk : k < n) (hik : i ≤ k) :
    inclusiveCut data n i ≤ inclusiveCut data n k := by
  have hj1 : inclJ data n i + 1 < data.length := by
    simpa [inclJ] using inclusive_j_succ_lt data.length n i hld hn hi
  have hj2 : inclJ data n k + 1 < data.length := by
    simpa [inclJ] using inclusive_j_succ_lt data.length n k hld hn hk
  have hd1 : inclDelta data n i ≤ n :=
    Nat.le_of_lt (by simpa [inclDelta] using Nat.mod_lt (i * (data.length - 1)) hn)
  have hd2 : inclDelta data n k ≤ n :=
    Nat.le_of_lt (by simpa [inclDelta] using Nat.mod_lt (k * (data.length - 1)) hn)
  have hab1 : data.getD (inclJ data n i) 0 ≤ data.getD (inclJ data n i + 1) 0 :=
    getD_le_getD hs (Nat.le_succ _) hj1
  have hab2 : data.getD (inclJ data n k) 0 ≤ data.getD (inclJ data n k + 1) 0 :=
    getD_le_getD hs (Nat.le_succ _) hj2
  have hjle : inclJ data n i ≤ inclJ data n k := by
    unfold inclJ
    exact Nat.div_le_div_right (Nat.mul_le_mul_right _ hik)
  unfold inclusiveCut
  rcases lt_or_eq_of_le hjle with hlt | heq
  · have hleft := (convex_bounds _ _ n (inclDelta data n i) hn hd1 hab1).2
    have hright := (convex_bounds _ _ n (inclDelta data n k) hn hd2 hab2).1
    have hmid : data.getD (inclJ data n i + 1) 0 ≤ data.getD (inclJ data n k) 0 :=
      getD_le_getD hs (by omega) (by omega)
    exact le_trans (le_trans hleft hmid) hright
  · have hdle : inclDelta data n i ≤ inclDelta data n k := by
      have h1 : n * inclJ data n i + inclDelta data n i = i * (data.length - 1) := by
        simpa [inclJ, inclDelta] using Nat.div_add_mod (i * (data.length - 1)) n
      have h2 : n * inclJ data n k + inclDelta data n k = k * (data.length - 1) := by
        simpa [inclJ, inclDelta] using Nat.div_add_mod (k * (data.length - 1)) n
      have hmul : i * (data.length - 1) ≤ k * (data.length - 1) := Nat.mul_le_mul_right _ hik
      rw [heq] at h1
      omega
    rw [heq]
    exact lerp_mono_delta _ _ n (inclDelta data n i) (inclDelta data n k) hn hd1 hd2 hdle hab2

theorem range'_sorted (s count : Nat) : (List.range' s count).Sorted (· ≤ ·) := by
  induction count generalizing s with
  | zero => simp
  | succ count ih =>
    rw [List.range'_succ, List.sorted_cons]
    refine ⟨?_, ih (s + 1)⟩
    intro y hy
    rcases List.mem_range'.1 hy with ⟨i, _, rfl⟩
    omega

theorem mem_range'_bounds (s count i : Nat) (h : i ∈ List.range' s count) :
    s ≤ i ∧ i < s + count := by
  rcases List.mem_range'.1 h with ⟨k, hk, rfl⟩
  constructor <;> omega

theorem map_mono_sorted (l : List Nat) (f : Nat → Rat)
    (hl : l.Sorted (· ≤ ·))
    (hf : ∀ a b, a ∈ l → b ∈ l → a ≤ b → f a ≤ f b) :
    (l.map f).Sorted (· ≤ ·) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.sorted_cons] at hl
    obtain ⟨hhead, htail⟩ := hl
    rw [List.map_cons, List.sorted_cons]
    constructor
    · intro y hy
      rcases List.mem_map.1 hy with ⟨b, hb, rfl⟩
      exact hf x b (List.mem_cons.2 (Or.inl rfl)) (List.mem_cons.2 (Or.inr hb)) (hhead b hb)
    · exact ih htail (fun a b ha hb hab =>
        hf a b (List.mem_cons.2 (Or.inr ha)) (List.mem_cons.2 (Or.inr hb)) hab)


theorem lerp_mono_int (a b : Rat) (n : Nat) (d1 d2 : Int)
    (hn : 0 < n) (hdd : d1 ≤ d2) (hab : a ≤ b) :
    (a * ((n : Rat) - d1) + b * d1) / (n : Rat) ≤
      (a * ((n : Rat) - d2) + b * d2) / (n : Rat) := by
  have hn0 : (n : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnpos : 0 < (n : Rat) := by exact_mod_cast hn
  have hdiff :
      (a * ((n : Rat) - d2) + b * d2) / (n : Rat) -
        (a * ((n : Rat) - d1) + b * d1) / (n : Rat)
        = ((b - a) * (d2 - d1)) / (n : Rat) := by
    field_simp [hn0]; ring
  have hnonneg : 0 ≤ ((b - a) * (d2 - d1)) / (n : Rat) := by
    apply div_nonneg
    · exact mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr (by exact_mod_cast hdd))
    · exact le_of_lt hnpos
  linarith

theorem lerp_le_left_int (a b : Rat) (n : Nat) (delta : Int)
    (hn : 0 < n) (hd : delta ≤ 0) (hab : a ≤ b) :
    (a * ((n : Rat) - delta) + b * delta) / (n : Rat) ≤ a := by
  have hn0 : (n : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnpos : 0 < (n : Rat) := by exact_mod_cast hn
  have hdiff : a - (a * ((n : Rat) - delta) + b * delta) / (n : Rat)
      = ((b - a) * (-delta)) / (n : Rat) := by
    field_simp [hn0]; ring
  have hnonneg : 0 ≤ ((b - a) * (-delta)) / (n : Rat) := by
    apply div_nonneg
    · exact mul_nonneg (sub_nonneg.mpr hab) (neg_nonneg.mpr (by exact_mod_cast hd))
    · exact le_of_lt hnpos
  linarith

theorem lerp_ge_left_int (a b : Rat) (n : Nat) (delta : Int)
    (hn : 0 < n) (hd : 0 ≤ delta) (hab : a ≤ b) :
    a ≤ (a * ((n : Rat) - delta) + b * delta) / (n : Rat) := by
  have hn0 : (n : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnpos : 0 < (n : Rat) := by exact_mod_cast hn
  have hdiff : (a * ((n : Rat) - delta) + b * delta) / (n : Rat) - a
      = ((b - a) * delta) / (n : Rat) := by
    field_simp [hn0]; ring
  have hnonneg : 0 ≤ ((b - a) * delta) / (n : Rat) := by
    apply div_nonneg
    · exact mul_nonneg (sub_nonneg.mpr hab) (by exact_mod_cast hd)
    · exact le_of_lt hnpos
  linarith

theorem lerp_le_right_int (a b : Rat) (n : Nat) (delta : Int)
    (hn : 0 < n) (hd : delta ≤ (n : Int)) (hab : a ≤ b) :
    (a * ((n : Rat) - delta) + b * delta) / (n : Rat) ≤ b := by
  have hn0 : (n : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnpos : 0 < (n : Rat) := by exact_mod_cast hn
  have hdiff : b - (a * ((n : Rat) - delta) + b * delta) / (n : Rat)
      = ((b - a) * ((n : Rat) - delta)) / (n : Rat) := by
    field_simp [hn0]; ring
  have hnonneg : 0 ≤ ((b - a) * ((n : Rat) - delta)) / (n : Rat) := by
    apply div_nonneg
    · exact mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr (by exact_mod_cast hd))
    · exact le_of_lt hnpos
  linarith

theorem nat_sub_div (a n : Nat) : a - n * (a / n) = a % n := by
  have h := Nat.div_add_mod a n
  conv =>
    lhs
    lhs
    rw [← h]
  exact Nat.add_sub_cancel_left (n * (a / n)) (a % n)

theorem int_sub_div (a n : Nat) :
    (a : Int) - ((a / n : Nat) : Int) * (n : Int) = ((a % n : Nat) : Int) := by
  have hnat := nat_sub_div a n
  have hle : n * (a / n) ≤ a := by
    have hle' : n * (a / n) ≤ n * (a / n) + a % n := Nat.le_add_right _ _
    simpa [Nat.div_add_mod a n] using hle'
  have hcast : ((a - n * (a / n) : Nat) : Int) =
      (a : Int) - ((n * (a / n) : Nat) : Int) := Nat.cast_sub hle
  rw [hnat] at hcast
  have hcomm : ((n * (a / n) : Nat) : Int) = ((a / n : Nat) : Int) * (n : Int) := by
    rw [Nat.cast_mul]
    exact Int.mul_comm _ _
  rw [← hcomm]
  exact hcast.symm


theorem clampIndex_mono (ld a b : Nat) (hld : 2 ≤ ld) (hab : a ≤ b) :
    clampIndex ld a ≤ clampIndex ld b := by
  unfold clampIndex
  split_ifs <;> omega

theorem exclJ_mono (data : List Rat) (n i k : Nat) (hld : 2 ≤ data.length) (hik : i ≤ k) :
    exclJ data n i ≤ exclJ data n k := by
  unfold exclJ
  refine clampIndex_mono _ _ _ hld ?_
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ hik)

theorem exclJ_bounds (data : List Rat) (n i : Nat) (hld : 2 ≤ data.length) :
    1 ≤ exclJ data n i ∧ exclJ data n i ≤ data.length - 1 ∧ exclJ data n i < data.length := by
  have hb := clampIndex_bounds data.length ((i * (data.length + 1)) / n) hld
  have h1 : 1 ≤ exclJ data n i := by simpa [exclJ] using hb.1
  have h2 : exclJ data n i ≤ data.length - 1 := by simpa [exclJ] using hb.2
  exact ⟨h1, h2, by omega⟩

theorem excl_adj_le (data : List Rat) (n i : Nat)
    (hld : 2 ≤ data.length) (hs : data.Sorted (· ≤ ·)) :
    data.getD (exclJ data n i - 1) 0 ≤ data.getD (exclJ data n i) 0 := by
  have hb := exclJ_bounds data n i hld
  exact getD_le_getD hs (by omega) hb.2.2

theorem cast_prod (i ld : Nat) :
    (i : Int) * ((ld : Int) + 1) = ((i * (ld + 1) : Nat) : Int) := by
  simp [Nat.cast_mul, Nat.cast_add]

theorem exclDelta_neg_of_up (data : List Rat) (n i : Nat) (hn : 0 < n)
    (hup : (i * (data.length + 1)) / n < 1) :
    exclDelta data n i < 0 := by
  have hj : exclJ data n i = 1 := by
    unfold exclJ
    exact clampIndex_of_lt_one _ _ hup
  have hdiv0 : (i * (data.length + 1)) / n = 0 := by
    have hlt : (i * (data.length + 1)) / n < Nat.succ 0 := by simpa using hup
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
  have hmod := Nat.div_add_mod (i * (data.length + 1)) n
  rw [hdiv0] at hmod
  simp at hmod
  have hlt : i * (data.length + 1) < n := by
    simpa [hmod] using Nat.mod_lt (i * (data.length + 1)) hn
  unfold exclDelta
  rw [hj, cast_prod i data.length]
  omega

theorem exclDelta_nonneg_of_not_up (data : List Rat) (n i : Nat)
    (hn : 0 < n) (hld : 2 ≤ data.length)
    (hnot : ¬ (i * (data.length + 1)) / n < 1) :
    0 ≤ exclDelta data n i := by
  unfold exclDelta exclJ
  by_cases hhi : (i * (data.length + 1)) / n > data.length - 1
  · have hclamp := clampIndex_of_gt data.length ((i * (data.length + 1)) / n) hnot hhi
    rw [hclamp, cast_prod i data.length]
    have hsucc : data.length ≤ (i * (data.length + 1)) / n := by
      have hs := Nat.succ_le_of_lt hhi
      simpa [Nat.sub_add_cancel (show 1 ≤ data.length by omega)] using hs
    have h1 : n * data.length ≤ n * ((i * (data.length + 1)) / n) :=
      Nat.mul_le_mul_left _ hsucc
    have h2 : n * ((i * (data.length + 1)) / n) ≤ i * (data.length + 1) := by
      have hle' : n * ((i * (data.length + 1)) / n) ≤
          n * ((i * (data.length + 1)) / n) + (i * (data.length + 1)) % n :=
        Nat.le_add_right _ _
      simpa [Nat.div_add_mod (i * (data.length + 1)) n] using hle'
    have hprod : ((n * data.length : Nat) : Int) ≤ ((i * (data.length + 1) : Nat) : Int) := by
      exact_mod_cast (le_trans h1 h2)
    have hsplit : (n : Int) * data.length - ((data.length - 1 : Nat) : Int) * n = n := by
      have hlen : (data.length : Int) = ((data.length - 1 : Nat) : Int) + 1 := by omega
      calc
        (n : Int) * data.length - ((data.length - 1 : Nat) : Int) * n
            = n * (((data.length - 1 : Nat) : Int) + 1) -
                ((data.length - 1 : Nat) : Int) * n := by rw [← hlen]
        _ = n := by ring
    have hmul : ((n * data.length : Nat) : Int) = (n : Int) * data.length := by
      simp [Nat.cast_mul]
    linarith
  · have hclamp := clampIndex_of_in data.length ((i * (data.length + 1)) / n) hnot hhi
    rw [hclamp, cast_prod i data.length, int_sub_div (i * (data.length + 1)) n]
    exact_mod_cast (Nat.zero_le ((i * (data.length + 1)) % n))

theorem exclDelta_le_n_of_in_range (data : List Rat) (n i : Nat) (hn : 0 < n)
    (hin : 1 ≤ (i * (data.length + 1)) / n)
    (hhi : (i * (data.length + 1)) / n ≤ data.length - 1) :
    exclDelta data n i ≤ (n : Int) := by
  have hnot : ¬ (i * (data.length + 1)) / n < 1 := by omega
  have hnotgt : ¬ (i * (data.length + 1)) / n > data.length - 1 := by omega
  unfold exclDelta exclJ
  rw [clampIndex_of_in _ _ hnot hnotgt, cast_prod i data.length,
    int_sub_div (i * (data.length + 1)) n]
  exact_mod_cast Nat.le_of_lt (Nat.mod_lt (i * (data.length + 1)) hn)

theorem exclDelta_mono_same_j (data : List Rat) (n i k : Nat) (hik : i ≤ k)
    (hj : exclJ data n i = exclJ data n k) :
    exclDelta data n i ≤ exclDelta data n k := by
  unfold exclDelta
  rw [hj, cast_prod i data.length, cast_prod k data.length]
  have hmul : ((i * (data.length + 1) : Nat) : Int) ≤ ((k * (data.length + 1) : Nat) : Int) := by
    exact_mod_cast Nat.mul_le_mul_right _ hik
  exact Int.sub_le_sub_right hmul _

theorem not_clamp_down_of_lt (data : List Rat) (n i k : Nat) (hld : 2 ≤ data.length)
    (hlt : exclJ data n i < exclJ data n k) :
    (i * (data.length + 1)) / n ≤ data.length - 1 := by
  by_contra hgt
  have hgt' : (i * (data.length + 1)) / n > data.length - 1 := by omega
  have hnot : ¬ (i * (data.length + 1)) / n < 1 := by omega
  have hj : exclJ data n i = data.length - 1 := by
    unfold exclJ
    exact clampIndex_of_gt _ _ hnot hgt'
  have hk : exclJ data n k ≤ data.length - 1 := (exclJ_bounds data n k hld).2.1
  omega

theorem exclusiveCut_le (data : List Rat) (n i k : Nat)
    (hld : 2 ≤ data.length) (hn : 0 < n) (hs : data.Sorted (· ≤ ·)) (hik : i ≤ k) :
    exclusiveCut data n i ≤ exclusiveCut data n k := by
  have hjm := exclJ_mono data n i k hld hik
  have hbi := exclJ_bounds data n i hld
  have hbk := exclJ_bounds data n k hld
  have habi := excl_adj_le data n i hld hs
  have habk := excl_adj_le data n k hld hs
  rcases lt_or_eq_of_le hjm with hlt | heq
  · have hnot_up_k : ¬ (k * (data.length + 1)) / n < 1 := by
      intro hup
      have hjk : exclJ data n k = 1 := by
        unfold exclJ
        exact clampIndex_of_lt_one _ _ hup
      omega
    have hdkn := exclDelta_nonneg_of_not_up data n k hn hld hnot_up_k
    have hright : data.getD (exclJ data n k - 1) 0 ≤ exclusiveCut data n k := by
      unfold exclusiveCut
      exact lerp_ge_left_int _ _ n _ hn hdkn habk
    by_cases hup : (i * (data.length + 1)) / n < 1
    · have hj : exclJ data n i = 1 := by
        unfold exclJ
        exact clampIndex_of_lt_one _ _ hup
      have hdneg := exclDelta_neg_of_up data n i hn hup
      have hleft : exclusiveCut data n i ≤ data.getD (exclJ data n i - 1) 0 := by
        unfold exclusiveCut
        exact lerp_le_left_int _ _ n _ hn (le_of_lt hdneg) habi
      have hchain : data.getD (exclJ data n i - 1) 0 ≤ data.getD (exclJ data n k - 1) 0 := by
        rw [hj]
        exact getD_le_getD hs (by omega) (by omega)
      exact le_trans (le_trans hleft hchain) hright
    · have hraw_le := not_clamp_down_of_lt data n i k hld hlt
      have hraw_ge : 1 ≤ (i * (data.length + 1)) / n := by omega
      have hdle := exclDelta_le_n_of_in_range data n i hn hraw_ge hraw_le
      have hd0 := exclDelta_nonneg_of_not_up data n i hn hld hup
      have hleft : exclusiveCut data n i ≤ data.getD (exclJ data n i) 0 := by
        unfold exclusiveCut
        exact lerp_le_right_int _ _ n _ hn hdle habi
      have hmid : data.getD (exclJ data n i) 0 ≤ data.getD (exclJ data n k - 1) 0 :=
        getD_le_getD hs (by omega) (by omega)
      exact le_trans (le_trans hleft hmid) hright
  · have hdle := exclDelta_mono_same_j data n i k hik heq
    unfold exclusiveCut
    rw [heq]
    exact lerp_mono_int _ _ n _ _ hn hdle habk

theorem cutAt_le (data : List Rat) (n : Nat) (method : QuantileMethod)
    (hld : 2 ≤ data.length) (hn : 0 < n) (hs : data.Sorted (· ≤ ·))
    (i k : Nat) (hi : i < n) (hk : k < n) (hik : i ≤ k) :
    cutAt data n method i ≤ cutAt data n method k := by
  cases method with
  | inclusive => simpa [cutAt] using inclusiveCut_le data n i k hld hn hs hi hk hik
  | exclusive => simpa [cutAt] using exclusiveCut_le data n i k hld hn hs hik

theorem cuts_sorted (data : List Rat) (n : Nat) (method : QuantileMethod)
    (hld : 2 ≤ data.length) (hn : 0 < n) (hs : data.Sorted (· ≤ ·)) :
    (cuts data n method).Sorted (· ≤ ·) := by
  unfold cuts
  refine map_mono_sorted (List.range' 1 (n - 1)) (cutAt data n method) (range'_sorted _ _) ?_
  intro a b ha hb hab
  have ha' : a < n := by
    have h := (mem_range'_bounds 1 (n - 1) a ha).2
    omega
  have hb' : b < n := by
    have h := (mem_range'_bounds 1 (n - 1) b hb).2
    omega
  exact cutAt_le data n method hld hn hs a b ha' hb' hab

theorem cuts_length (data : List Rat) (n : Nat) (method : QuantileMethod) :
    (cuts data n method).length = n - 1 := by
  simp [cuts]

def quantiles_length_prop (data : List Rat) (n : Nat) (method : QuantileMethod) : Prop :=
  (quantiles data n method).length = n - 1

theorem quantiles_length_thm (data : List Rat) (n : Nat) (method : QuantileMethod) :
    quantiles_length_prop data n method := by
  simp [quantiles_length_prop, quantiles, cuts_length]

def quantiles_sort_invariant_prop (data : List Rat) (n : Nat) (method : QuantileMethod) : Prop :=
  quantiles data n method = quantiles (sortData data) n method

theorem quantiles_sort_invariant_thm (data : List Rat) (n : Nat) (method : QuantileMethod) :
    quantiles_sort_invariant_prop data n method := by
  simp [quantiles_sort_invariant_prop, quantiles, sortData_idem]

def quantiles_perm_prop (data data' : List Rat) (n : Nat) (method : QuantileMethod) : Prop :=
  List.Perm data data' → quantiles data n method = quantiles data' n method

theorem quantiles_perm_thm (data data' : List Rat) (n : Nat) (method : QuantileMethod) :
    quantiles_perm_prop data data' n method := by
  intro h
  unfold quantiles
  congr 1
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact (sortData_perm data).trans (h.trans (sortData_perm data').symm)
  · exact sortData_sorted data
  · exact sortData_sorted data'

def quantiles_const_prop (data : List Rat) (n : Nat) (method : QuantileMethod) (c : Rat) : Prop :=
  2 ≤ data.length → 0 < n → (∀ x ∈ data, x = c) → ∀ y ∈ quantiles data n method, y = c

theorem quantiles_const_thm (data : List Rat) (n : Nat) (method : QuantileMethod) (c : Rat) :
    quantiles_const_prop data n method c := by
  intro hld hn hall y hy
  unfold quantiles cuts at hy
  rcases List.mem_map.1 hy with ⟨i, hi, rfl⟩
  have hi' : i < n := by
    have hb := (mem_range'_bounds 1 (n - 1) i hi).2
    omega
  have hall' : ∀ x ∈ sortData data, x = c := by
    intro x hx
    exact hall x ((List.Perm.mem_iff (sortData_perm data)).1 hx)
  have hlen : 2 ≤ (sortData data).length := by simpa [sortData_length] using hld
  cases method with
  | inclusive =>
      simpa [cutAt] using inclusiveCut_const (sortData data) c n i hn hlen hi' hall'
  | exclusive =>
      simpa [cutAt] using exclusiveCut_const (sortData data) c n i hn hlen hall'

def inclusive_bounds_prop (data : List Rat) (n : Nat) : Prop :=
  2 ≤ data.length → 0 < n →
    ∀ y ∈ quantiles data n .inclusive,
      (sortData data).getD 0 0 ≤ y ∧
        y ≤ (sortData data).getD ((sortData data).length - 1) 0

theorem inclusiveCut_bounds (data : List Rat) (n i : Nat)
    (hld : 2 ≤ data.length) (hn : 0 < n) (hi : i < n) (hs : data.Sorted (· ≤ ·)) :
    data.getD 0 0 ≤ inclusiveCut data n i ∧
      inclusiveCut data n i ≤ data.getD (data.length - 1) 0 := by
  have hj1 : inclJ data n i + 1 < data.length := by
    simpa [inclJ] using inclusive_j_succ_lt data.length n i hld hn hi
  have hj : inclJ data n i < data.length := by omega
  have hd : inclDelta data n i ≤ n :=
    Nat.le_of_lt (by simpa [inclDelta] using Nat.mod_lt (i * (data.length - 1)) hn)
  have hab : data.getD (inclJ data n i) 0 ≤ data.getD (inclJ data n i + 1) 0 :=
    getD_le_getD hs (Nat.le_succ _) hj1
  have hconv := convex_bounds (data.getD (inclJ data n i) 0)
      (data.getD (inclJ data n i + 1) 0) n (inclDelta data n i) hn hd hab
  have hlo : data.getD 0 0 ≤ data.getD (inclJ data n i) 0 :=
    getD_le_getD hs (Nat.zero_le _) hj
  have hhi : data.getD (inclJ data n i + 1) 0 ≤ data.getD (data.length - 1) 0 :=
    getD_le_getD hs (by omega) (by omega)
  unfold inclusiveCut
  exact ⟨le_trans hlo hconv.1, le_trans hconv.2 hhi⟩

theorem inclusive_bounds_thm (data : List Rat) (n : Nat) : inclusive_bounds_prop data n := by
  intro hld hn y hy
  have hs := sortData_sorted data
  have hlen : 2 ≤ (sortData data).length := by simpa [sortData_length] using hld
  unfold quantiles cuts at hy
  rcases List.mem_map.1 hy with ⟨i, hi, rfl⟩
  have hi' : i < n := by
    have hb := (mem_range'_bounds 1 (n - 1) i hi).2
    omega
  simpa [cutAt] using inclusiveCut_bounds (sortData data) n i hlen hn hi' hs


def inclusive_adjacent_prop (data : List Rat) (n i : Nat) : Prop :=
  2 ≤ data.length → 0 < n → i < n → data.Sorted (· ≤ ·) →
    data.getD (inclJ data n i) 0 ≤ inclusiveCut data n i ∧
      inclusiveCut data n i ≤ data.getD (inclJ data n i + 1) 0

theorem inclusive_adjacent_thm (data : List Rat) (n i : Nat) :
    inclusive_adjacent_prop data n i := by
  intro hld hn hi hs
  have hj1 : inclJ data n i + 1 < data.length := by
    simpa [inclJ] using inclusive_j_succ_lt data.length n i hld hn hi
  have hd : inclDelta data n i ≤ n :=
    Nat.le_of_lt (by simpa [inclDelta] using Nat.mod_lt (i * (data.length - 1)) hn)
  have hab := getD_le_getD hs (Nat.le_succ (inclJ data n i)) hj1
  unfold inclusiveCut
  exact convex_bounds _ _ n _ hn hd hab

def exclusive_segment_prop (data : List Rat) (n i : Nat) : Prop :=
  2 ≤ data.length → 0 < n → data.Sorted (· ≤ ·) →
    0 ≤ exclDelta data n i → exclDelta data n i ≤ (n : Int) →
      data.getD (exclJ data n i - 1) 0 ≤ exclusiveCut data n i ∧
        exclusiveCut data n i ≤ data.getD (exclJ data n i) 0

theorem exclusive_segment_thm (data : List Rat) (n i : Nat) :
    exclusive_segment_prop data n i := by
  intro hld hn hs hd0 hdn
  have hab := excl_adj_le data n i hld hs
  unfold exclusiveCut
  exact ⟨lerp_ge_left_int _ _ n _ hn hd0 hab, lerp_le_right_int _ _ n _ hn hdn hab⟩

def quantiles_mono_prop (data : List Rat) (n : Nat) (method : QuantileMethod) : Prop :=
  2 ≤ data.length → 0 < n → (quantiles data n method).Sorted (· ≤ ·)

theorem quantiles_mono_thm (data : List Rat) (n : Nat) (method : QuantileMethod) :
    quantiles_mono_prop data n method := by
  intro hld hn
  unfold quantiles
  exact cuts_sorted (sortData data) n method (by simpa [sortData_length] using hld) hn
    (sortData_sorted data)

def exclusive_median_prop (data : List Rat) : Prop :=
  2 ≤ data.length → quantiles data 2 .exclusive = [sampleMedian data]

theorem exclusive_median_thm (data : List Rat) : exclusive_median_prop data := by
  intro h
  have hlen : (sortData data).length = data.length := sortData_length data
  have h2 : 2 ≤ (sortData data).length := by simpa [hlen] using h
  have hr : List.range' 1 (2 - 1) = [1] := by decide
  unfold quantiles cuts sampleMedian
  simp [hr, cutAt, exclusiveCut_median (sortData data) h2, hlen]

def inclusive_formula_prop (data : List Rat) (n i : Nat) : Prop :=
  inclusiveCut data n i =
    (data.getD ((i * (data.length - 1)) / n) 0 *
        ((n - (i * (data.length - 1)) % n : Nat) : Rat) +
      data.getD ((i * (data.length - 1)) / n + 1) 0 *
        (((i * (data.length - 1)) % n : Nat) : Rat)) / (n : Rat)

theorem inclusive_formula_thm (data : List Rat) (n i : Nat) :
    inclusive_formula_prop data n i := by
  simp [inclusive_formula_prop, inclusiveCut, inclJ, inclDelta]

def exclusive_formula_prop (data : List Rat) (n i : Nat) : Prop :=
  exclusiveCut data n i =
    (data.getD (clampIndex data.length ((i * (data.length + 1)) / n) - 1) 0 *
        ((n : Rat) - (((i * (data.length + 1) : Int) -
          (clampIndex data.length ((i * (data.length + 1)) / n) : Int) * (n : Int)) : Rat)) +
      data.getD (clampIndex data.length ((i * (data.length + 1)) / n)) 0 *
        (((i * (data.length + 1) : Int) -
          (clampIndex data.length ((i * (data.length + 1)) / n) : Int) * (n : Int) : Rat))) /
      (n : Rat)

theorem exclusive_formula_thm (data : List Rat) (n i : Nat) :
    exclusive_formula_prop data n i := by
  simp [exclusive_formula_prop, exclusiveCut, exclJ, exclDelta]

def benchmark_spec_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  (Pre data n method ∧
      benchmarkQuantiles data n method =
        .ok (quantiles data n.toNat (decodeMethod method))) ∨
    (¬ Pre data n method ∧ benchmarkQuantiles data n method = .error benchmarkErrorMsg)

theorem benchmark_spec_thm (data : List Rat) (n : Int) (method : String) :
    benchmark_spec_prop data n method := by
  unfold benchmark_spec_prop benchmarkQuantiles
  by_cases h : preBool data n method
  · left
    refine ⟨(preBool_iff_Pre data n method).1 h, ?_⟩
    simp [h]
  · right
    refine ⟨?_, ?_⟩
    · intro hp
      exact h ((preBool_iff_Pre data n method).2 hp)
    · simp [h]

def quantilesChecked_spec_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  quantilesChecked data n method =
    if n < 1 then .error errNTooSmall
    else if data.length < 2 then .error errInsufficient
    else if method = "inclusive" then .ok (quantiles data n.toNat .inclusive)
    else if method = "exclusive" then .ok (quantiles data n.toNat .exclusive)
    else .error (errUnknownMethod method)

theorem quantilesChecked_spec_thm (data : List Rat) (n : Int) (method : String) :
    quantilesChecked_spec_prop data n method := by
  unfold quantilesChecked_spec_prop quantilesChecked
  split_ifs <;> rfl

def Post_prop (data : List Rat) (n : Int) (method : String) : Prop :=
  benchmarkQuantiles data n method = .ok (quantiles data n.toNat (decodeMethod method)) ∧
    (quantiles data n.toNat (decodeMethod method)).length = n.toNat - 1 ∧
    (quantiles data n.toNat (decodeMethod method)).Sorted (· ≤ ·) ∧
    (∀ c, (∀ x ∈ data, x = c) → ∀ y ∈ quantiles data n.toNat (decodeMethod method), y = c) ∧
    (method = "inclusive" →
      ∀ y ∈ quantiles data n.toNat .inclusive,
        (sortData data).getD 0 0 ≤ y ∧
          y ≤ (sortData data).getD ((sortData data).length - 1) 0) ∧
    (n = 2 ∧ method = "exclusive" → quantiles data 2 .exclusive = [sampleMedian data]) ∧
    quantiles data n.toNat (decodeMethod method) =
      quantiles (sortData data) n.toNat (decodeMethod method)

/-! ## Property-based tests -/

def listSortedBool : List Rat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a ≤ b) && listSortedBool (b :: rest)

def lengthOk (xs : List Nat) (n : Nat) (inclusive : Bool) : Bool :=
  let method := if inclusive then QuantileMethod.inclusive else QuantileMethod.exclusive
  (quantiles (xs.map (fun k => (k : Rat))) n method).length == n - 1

def sortInvOk (xs : List Nat) (n : Nat) : Bool :=
  let data := xs.map (fun k => (k : Rat))
  quantiles data n .exclusive == quantiles (sortData data) n .exclusive &&
    quantiles data n .inclusive == quantiles (sortData data) n .inclusive

def permOk (xs : List Nat) (n : Nat) : Bool :=
  let data := xs.map (fun k => (k : Rat))
  quantiles data n == quantiles data.reverse n &&
    quantiles data n .inclusive == quantiles data.reverse n .inclusive

def constOk (c k n : Nat) : Bool :=
  let data := List.replicate (k + 2) (c : Rat)
  (quantiles data (n + 1) .exclusive).all (· == (c : Rat)) &&
    (quantiles data (n + 1) .inclusive).all (· == (c : Rat))

def boundsOk (xs : List Nat) (n : Nat) : Bool :=
  if xs.length < 2 then true else
    let data := xs.map (fun k => (k : Rat))
    let s := sortData data
    (quantiles data (n + 1) .inclusive).all
      (fun y => s.getD 0 0 ≤ y && y ≤ s.getD (s.length - 1) 0)

def adjacentOk (xs : List Rat) (n i : Nat) : Bool :=
  if xs.length < 2 || n = 0 || n ≤ i || decide (xs.Sorted (· ≤ ·)) = false then true else
    let y := inclusiveCut xs n i
    decide (xs.getD (inclJ xs n i) 0 ≤ y) && decide (y ≤ xs.getD (inclJ xs n i + 1) 0)

def segmentOk (xs : List Rat) (n i : Nat) : Bool :=
  if xs.length < 2 || n = 0 || decide (xs.Sorted (· ≤ ·)) = false then true else
    let d := exclDelta xs n i
    if d < 0 || (n : Int) < d then true else
      let y := exclusiveCut xs n i
      decide (xs.getD (exclJ xs n i - 1) 0 ≤ y) && decide (y ≤ xs.getD (exclJ xs n i) 0)

def monoOk (xs : List Nat) (n : Nat) (inclusive : Bool) : Bool :=
  if xs.length < 2 then true else
    let method := if inclusive then QuantileMethod.inclusive else QuantileMethod.exclusive
    listSortedBool (quantiles (xs.map (fun k => (k : Rat))) (n + 1) method)

def medianOk (xs : List Nat) : Bool :=
  if xs.length < 2 then true else
    quantiles (xs.map (fun k => (k : Rat))) 2 .exclusive ==
      [sampleMedian (xs.map (fun k => (k : Rat)))]

def formulaOk (xs : List Rat) (n i : Nat) : Bool :=
  inclusiveCut xs n i ==
      (xs.getD ((i * (xs.length - 1)) / n) 0 *
          ((n - (i * (xs.length - 1)) % n : Nat) : Rat) +
        xs.getD ((i * (xs.length - 1)) / n + 1) 0 *
          (((i * (xs.length - 1)) % n : Nat) : Rat)) / (n : Rat) &&
    exclusiveCut xs n i ==
      (xs.getD (clampIndex xs.length ((i * (xs.length + 1)) / n) - 1) 0 *
          ((n : Rat) - (((i * (xs.length + 1) : Int) -
            (clampIndex xs.length ((i * (xs.length + 1)) / n) : Int) * (n : Int)) : Rat)) +
        xs.getD (clampIndex xs.length ((i * (xs.length + 1)) / n)) 0 *
          (((i * (xs.length + 1) : Int) -
            (clampIndex xs.length ((i * (xs.length + 1)) / n) : Int) * (n : Int) : Rat))) /
        (n : Rat)

def benchmarkOk (xs : List Nat) (n : Int) (method : String) : Bool :=
  let data := xs.map (fun k => (k : Rat))
  benchmarkQuantiles data n method ==
    if preBool data n method then .ok (quantiles data n.toNat (decodeMethod method))
    else .error benchmarkErrorMsg

def checkedOk (xs : List Nat) (n : Int) (method : String) : Bool :=
  let data := xs.map (fun k => (k : Rat))
  quantilesChecked data n method ==
    if n < 1 then .error errNTooSmall
    else if data.length < 2 then .error errInsufficient
    else if method = "inclusive" then .ok (quantiles data n.toNat .inclusive)
    else if method = "exclusive" then .ok (quantiles data n.toNat .exclusive)
    else .error (errUnknownMethod method)

def postOk (xs : List Nat) (n : Int) (method : String) : Bool :=
  let data := xs.map (fun k => (k : Rat))
  if preBool data n method = false then true else
    match benchmarkQuantiles data n method with
    | .error _ => false
    | .ok result =>
        result.length == n.toNat - 1 &&
        listSortedBool result &&
        result == quantiles (sortData data) n.toNat (decodeMethod method) &&
        (if method = "inclusive" then
          let s := sortData data
          result.all (fun y => s.getD 0 0 ≤ y && y ≤ s.getD (s.length - 1) 0)
        else true) &&
        (if n == 2 && method == "exclusive" then result == [sampleMedian data] else true) &&
        (match data with
          | c :: _ => if data.all (· == c) then result.all (· == c) else true
          | [] => true)

def smallLists : List (List Nat) :=
  [[], [0], [1, 2], [4, 1, 3, 2], [0, 0, 0], [1, 2, 3, 4, 5], [9, 1, 8, 2], [5, 5, 5, 5]]

example : (List.range 12).all (fun n =>
    smallLists.all (fun xs => lengthOk xs n true && lengthOk xs n false)) = true := by
  native_decide

example : (List.range 8).all (fun n => smallLists.all (fun xs => sortInvOk xs n)) = true := by
  native_decide

example : (List.range 8).all (fun n => smallLists.all (fun xs => permOk xs n)) = true := by
  native_decide

example : (List.range 5).all (fun c => (List.range 4).all (fun k =>
    (List.range 6).all (fun n => constOk c k n))) = true := by
  native_decide

example : (List.range 6).all (fun n => smallLists.all (fun xs => boundsOk xs n)) = true := by
  native_decide

example : (List.range 5).all (fun n => (List.range 5).all (fun i =>
    smallLists.all (fun xs =>
      adjacentOk (xs.map (fun k => (k : Rat))) n i &&
      segmentOk ((xs.map (fun k => (k : Rat))).mergeSort (· ≤ ·)) n i))) = true := by
  native_decide

example : (List.range 6).all (fun n => smallLists.all (fun xs =>
    monoOk xs n true && monoOk xs n false)) = true := by
  native_decide

example : smallLists.all medianOk = true := by native_decide

example : (List.range 5).all (fun n => (List.range 5).all (fun i =>
    smallLists.all (fun xs => formulaOk (xs.map (fun k => (k : Rat))) n i))) = true := by
  native_decide

def benchInputs : List (List Nat × Int × String) :=
  smallLists.flatMap fun xs =>
    [0, 1, 2, 4, -1].flatMap fun n =>
      ["exclusive", "inclusive", "invalid"].map fun m => (xs, n, m)

example : benchInputs.all (fun t => benchmarkOk t.1 t.2.1 t.2.2) = true := by native_decide
example : benchInputs.all (fun t => checkedOk t.1 t.2.1 t.2.2) = true := by native_decide
example : benchInputs.all (fun t => postOk t.1 t.2.1 t.2.2) = true := by native_decide

#eval Plausible.Testable.check (∀ xs : List Nat, ∀ n : Nat, ∀ b : Bool, lengthOk xs n b = true)
#eval Plausible.Testable.check (∀ xs : List Nat, ∀ n : Nat, sortInvOk xs n = true)
#eval Plausible.Testable.check (∀ xs : List Nat, ∀ n : Nat, permOk xs n = true)
#eval Plausible.Testable.check (∀ c k n : Nat, constOk c k n = true)
#eval Plausible.Testable.check (∀ xs : List Nat, ∀ n : Nat, boundsOk xs n = true)
#eval Plausible.Testable.check (∀ xs : List Nat, ∀ n : Nat, ∀ b : Bool, monoOk xs n b = true)
#eval Plausible.Testable.check (∀ xs : List Nat, medianOk xs = true)

-- PBT for inclusive_adjacent_prop / exclusive_segment_prop / formula props / benchmark specs /
-- Post_prop: the bounded `native_decide` checks above are the executable counterparts.
-- Real-valued restatements are not used; the Rat layer is the mathematical model.


theorem correctness_thm (data : List Rat) (n : Int) (method : String)
    (hpre : Pre data n method) : Post_prop data n method := by
  have hlen2 : 2 ≤ data.length := hpre.1
  have hn1 : 1 ≤ n := hpre.2.1
  have hmeth : method = "exclusive" ∨ method = "inclusive" := hpre.2.2
  have hnpos : 0 ≤ n := le_trans (by decide : (0 : Int) ≤ 1) hn1
  have heqN : (n.toNat : Int) = n := Int.toNat_of_nonneg hnpos
  have hnposN : 0 < n.toNat := by
    have : (1 : Int) ≤ (n.toNat : Int) := by simpa [heqN] using hn1
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases benchmark_spec_thm data n method with ⟨_, hok⟩ | ⟨hnot, _⟩
    · exact hok
    · exact absurd hpre hnot
  · simpa [quantiles_length_prop] using quantiles_length_thm data n.toNat (decodeMethod method)
  · exact quantiles_mono_thm data n.toNat (decodeMethod method) hlen2 hnposN
  · intro c hall y hy
    exact quantiles_const_thm data n.toNat (decodeMethod method) c hlen2 hnposN hall y hy
  · intro hinc
    have hdec : decodeMethod method = .inclusive := by simp [decodeMethod, hinc]
    intro y hy
    have hbounds := inclusive_bounds_thm data n.toNat hlen2 hnposN
    simpa [hdec] using hbounds y hy
  · intro h2
    have hn2 : n = 2 := h2.1
    have hex : method = "exclusive" := h2.2
    have hdec : decodeMethod method = .exclusive := by simp [decodeMethod, hex]
    have hnt : n.toNat = 2 := by
      have : (n.toNat : Int) = 2 := by simpa [heqN] using hn2
      exact_mod_cast this
    simpa [hnt, hdec] using exclusive_median_thm data hlen2
  · simpa [quantiles_sort_invariant_prop] using
      quantiles_sort_invariant_thm data n.toNat (decodeMethod method)



/-! ## Imperative implementation -/

theorem map_singleton_flatten (f : Nat → Rat) (xs : List Nat) :
    (xs.map (fun x => [f x])).flatten = xs.map f := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem forIn_append (f : Nat → Rat) (xs : List Nat) (acc : List Rat) :
    (Id.run do
      let mut acc := acc
      for i in xs do
        acc := acc ++ [f i]
      return acc) = acc ++ xs.map f := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [map_singleton_flatten]

/-- Imperative quantiles: sort once, then accumulate interpolated cuts in a mutable list. -/
def quantilesImp (data : List Rat) (n : Nat := 4) (method : QuantileMethod := .exclusive) : List Rat :=
  let sorted := sortData data
  Id.run do
    let mut acc : List Rat := []
    for i in List.range' 1 (n - 1) do
      acc := acc ++ [cutAt sorted n method i]
    return acc

def benchmarkQuantilesImp (data : List Rat) (n : Int := 4) (method : String := "exclusive") :
    Except String (List Rat) :=
  Id.run do
    if preBool data n method then
      return .ok (quantilesImp data n.toNat (decodeMethod method))
    else
      return .error benchmarkErrorMsg

/-! ## Imperative tests -/

example : quantilesImp [1, 2, 3, 4] = [5/4, 5/2, 15/4] := by native_decide
example : quantilesImp [1, 2, 3, 4] 4 .inclusive = [7/4, 5/2, 13/4] := by native_decide
example : quantilesImp [4, 1, 3, 2] = quantilesImp [1, 2, 3, 4] := by native_decide
example : quantilesImp [1, 2, 3, 4, 5] 2 = [3] := by native_decide
example : quantilesImp [1, 2] 4 .exclusive = [3/4, 3/2, 9/4] := by native_decide
example : quantilesImp [1] 4 = quantiles [1] 4 := by native_decide
example : benchmarkQuantilesImp [1, 2, 3, 4] 4 "exclusive" = .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmarkQuantilesImp [1] 4 "exclusive" = .error benchmarkErrorMsg := by native_decide
example : quantilesImp [1, 2, 3, 4] = quantiles [1, 2, 3, 4] := by native_decide
example : quantilesImp [1, 2, 3, 4] 4 .inclusive = quantiles [1, 2, 3, 4] 4 .inclusive := by native_decide

#eval quantilesImp [1, 2, 3, 4]
#eval quantilesImp [1, 2, 3, 4] 4 .inclusive

theorem quantiles_eq_imp (data : List Rat) (n : Nat) (method : QuantileMethod) :
    quantiles data n method = quantilesImp data n method := by
  unfold quantiles quantilesImp cuts
  have h := forIn_append (cutAt (sortData data) n method) (List.range' 1 (n - 1)) []
  simpa [List.append_nil] using h.symm

theorem benchmark_eq_imp (data : List Rat) (n : Int) (method : String) :
    benchmarkQuantiles data n method = benchmarkQuantilesImp data n method := by
  unfold benchmarkQuantiles benchmarkQuantilesImp
  by_cases h : preBool data n method
  · simp [h, quantiles_eq_imp]
  · simp [h]

end «31_statistics_quantiles»
