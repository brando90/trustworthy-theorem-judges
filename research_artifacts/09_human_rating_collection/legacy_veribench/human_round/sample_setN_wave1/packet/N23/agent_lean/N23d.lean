import Mathlib

/-!
# Statistics quantiles

A translation of `statistics.quantiles` and its checked benchmark wrapper.
Lists represent Python lists/tuples of numbers; `Int` preserves the signed input
`n`, and strings preserve invalid method names. Invalid benchmark arguments
return `Except.error statisticsError` (including invalid methods, as in `pre`).

The algorithm is parameterized by numeric operations. `FloatLayer` executes
floating-point arithmetic, `RatLayer` provides exact executable arithmetic, and
`RealLayer` is the mathematical interpretation of interpolation. In particular,
exclusive interpolation uses a **signed** delta and permits extrapolation.
The Real theorems are mathematical, not assertions that rounded Float arithmetic
is exact. Structural and imperative-equivalence theorems apply to every layer,
including Float, without finiteness assumptions. Non-numeric Python objects are
outside the typed numeric API, rather than silently coerced to numbers.
-/

namespace StatisticsQuantiles

deriving instance DecidableEq for Except

structure Numeric (α : Type) where
  zero : α
  le : α → α → Bool
  ofInt : Int → α
  add : α → α → α
  mul : α → α → α
  div : α → α → α

inductive Error where
  | statisticsError
  | unknownMethod
  deriving Repr, DecidableEq

/-- The two adjacent subscripts and the signed interpolation numerator. -/
def parameters (ld n i : Nat) (inclusive : Bool) : Nat × Nat × Int :=
  if inclusive then
    let j := i * (ld - 1) / n
    (j, j + 1, ((i * (ld - 1) % n : Nat) : Int))
  else
    let j := max 1 (min (ld - 1) (i * (ld + 1) / n))
    (j - 1, j, ((i * (ld + 1) : Nat) : Int) - ((j * n : Nat) : Int))

def interpolate (O : Numeric α) (a b : α) (n : Nat) (delta : Int) : α :=
  O.div (O.add (O.mul a (O.ofInt ((n : Int) - delta)))
    (O.mul b (O.ofInt delta))) (O.ofInt ((n : Int)))

/-- Out-of-range defaults make this helper total; `indices_thm` proves they
are never used by an admissible call. -/
def cut (O : Numeric α) (sorted : List α) (n : Nat) (inclusive : Bool) (i : Nat) : α :=
  let p := parameters sorted.length n i inclusive
  interpolate O (sorted.getD p.1 O.zero) (sorted.getD p.2.1 O.zero) n p.2.2

def core (O : Numeric α) (data : List α) (n : Nat) (inclusive : Bool) : List α :=
  let sorted := data.mergeSort O.le
  (List.range (n - 1)).map (fun k => cut O sorted n inclusive (k + 1))

/-- The library entry point, including the distinction between its two errors. -/
def quantiles (O : Numeric α) (data : List α) (n : Int := 4)
    (method : String := "exclusive") : Except Error (List α) :=
  if n < 1 then .error .statisticsError
  else if data.length < 2 then .error .statisticsError
  else if method = "inclusive" then .ok (core O data n.toNat true)
  else if method = "exclusive" then .ok (core O data n.toNat false)
  else .error .unknownMethod

/-- The benchmark wrapper checks all three conditions before calling the library. -/
def benchmark (O : Numeric α) (data : List α) (n : Int := 4)
    (method : String := "exclusive") : Except Error (List α) :=
  if data.length ≥ 2 ∧ n ≥ 1 ∧ (method = "inclusive" ∨ method = "exclusive") then
    quantiles O data n method
  else .error .statisticsError

namespace FloatLayer
def ops : Numeric Float :=
  ⟨0, fun a b => decide (a ≤ b), Float.ofInt, (· + ·), (· * ·), (· / ·)⟩
def benchmark_quantiles (data : List Float) (n : Int := 4) (method : String := "exclusive") :=
  benchmark ops data n method
end FloatLayer

namespace RatLayer
def ops : Numeric ℚ :=
  ⟨0, fun a b => decide (a ≤ b), fun z => z, (· + ·), (· * ·), (· / ·)⟩
def benchmark_quantiles (data : List ℚ) (n : Int := 4) (method : String := "exclusive") :=
  benchmark ops data n method
end RatLayer

namespace RealLayer
noncomputable def ops : Numeric ℝ :=
  ⟨0, fun a b => decide (a ≤ b), fun z => z, (· + ·), (· * ·), (· / ·)⟩
noncomputable def benchmark_quantiles (data : List ℝ) (n : Int := 4) (method : String := "exclusive") :=
  benchmark ops data n method
end RealLayer

-- Fixed tests: the Python examples, sorting, extrapolation, and signed n.
example : RatLayer.benchmark_quantiles [1, 2, 3, 4] = .ok [5/4, 5/2, 15/4] := by native_decide
example : RatLayer.benchmark_quantiles [1, 2, 3, 4] 4 "inclusive" =
    .ok [7/4, 5/2, 13/4] := by native_decide
example : (RatLayer.benchmark_quantiles ((List.range 11).map Nat.cast) 10).map List.length =
    .ok 9 := by native_decide
example : (RatLayer.benchmark_quantiles [1, 2, 3, 4] 100).map List.length = .ok 99 := by native_decide
example : RatLayer.benchmark_quantiles [1, 2, 3, 4, 5] 2 = .ok [3] := by native_decide
example : RatLayer.benchmark_quantiles [4, 1, 3, 2] = .ok [5/4, 5/2, 15/4] := by native_decide
example : (RatLayer.benchmark_quantiles ((List.range' 1 10).map Nat.cast)).map List.length =
    .ok 3 := by native_decide
example : RatLayer.benchmark_quantiles [0, 10] 4 = .ok [-5/2, 5, 25/2] := by native_decide
example : RatLayer.benchmark_quantiles [1, 2] 1 = .ok [] := by native_decide
example : RatLayer.benchmark_quantiles [1] = .error .statisticsError := by native_decide
example : RatLayer.benchmark_quantiles [1, 2] 0 = .error .statisticsError := by native_decide
example : RatLayer.benchmark_quantiles [1, 2] (-3) = .error .statisticsError := by native_decide
example : RatLayer.benchmark_quantiles [1, 2, 3] 4 "invalid" =
    .error .statisticsError := by native_decide
example : quantiles RatLayer.ops [1, 2, 3] 4 "invalid" = .error .unknownMethod := by native_decide
example : ((FloatLayer.benchmark_quantiles [1.5, 2.5, 3.5, 4.5] 2).toOption ==
    some [3.0]) = true := by native_decide
example : ((FloatLayer.benchmark_quantiles [1, 2, 3, 4]).toOption ==
    some [1.25, 2.5, 3.75]) = true := by native_decide
example : ((FloatLayer.benchmark_quantiles [1, 2, 3, 4] 4 "inclusive").toOption ==
    some [1.75, 2.5, 3.25]) = true := by native_decide
#eval FloatLayer.benchmark_quantiles [4, 1, 3, 2]
#eval RatLayer.benchmark_quantiles [0, 10] 4

/-- The typed counterpart of Python's precondition. -/
def Pre (data : List α) (n : Int) (method : String) : Prop :=
  data.length ≥ 2 ∧ n ≥ 1 ∧ (method = "inclusive" ∨ method = "exclusive")

instance : Decidable (Pre data n method) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem benchmark_valid (O : Numeric α) {data : List α} {n : Int} {method : String}
    (h : Pre data n method) :
    benchmark O data n method = .ok (core O data n.toNat (method == "inclusive")) := by
  rcases h with ⟨hl, hn, hm⟩
  rcases hm with rfl | rfl <;>
    simp [benchmark, quantiles, hl, hn, show ¬n < 1 by omega,
      show ¬data.length < 2 by omega]

def error_prop (O : Numeric α) (data : List α) (n : Int) (method : String) : Prop :=
  ¬ Pre data n method → benchmark O data n method = .error .statisticsError

theorem error_thm (O : Numeric α) (data : List α) (n : Int) (method : String) :
    error_prop O data n method := by
  intro h
  exact if_neg h

def length_prop (O : Numeric α) (data : List α) (n : Int) (method : String) : Prop :=
  (benchmark O data n method).map List.length = .ok (n.toNat - 1)

theorem length_thm (O : Numeric α) {data : List α} {n : Int} {method : String}
    (h : Pre data n method) : length_prop O data n method := by
  unfold length_prop
  rw [benchmark_valid O h]
  simp [core, Except.map]

/-- Every returned entry follows the divmod/clamped interpolation formula. -/
def formula_prop (O : Numeric α) (data : List α) (n : Int) (method : String) : Prop :=
  ∀ k < n.toNat - 1,
    (benchmark O data n method).toOption.bind (fun ys => ys[k]?) =
      some (cut O (data.mergeSort O.le) n.toNat (method == "inclusive") (k + 1))

theorem formula_thm (O : Numeric α) {data : List α} {n : Int} {method : String}
    (h : Pre data n method) : formula_prop O data n method := by
  intro k hk
  rw [benchmark_valid O h]
  simp [core, Except.toOption, hk]

/-- Both reads are in bounds; inclusive interpolation is convex, whereas
exclusive interpolation intentionally has no such restriction on delta. -/
def indices_prop (data : List α) (n : Int) (method : String) : Prop :=
  ∀ k < n.toNat - 1,
    let p := parameters data.length n.toNat (k + 1) (method == "inclusive")
    p.1 < data.length ∧ p.2.1 < data.length ∧ p.2.1 = p.1 + 1 ∧
      (method = "inclusive" → 0 ≤ p.2.2 ∧ p.2.2 < n)

theorem parameters_safe {ld n i : Nat} (hl : 2 ≤ ld) (hn : 0 < n)
    (_hi : 1 ≤ i) (hi' : i < n) (b : Bool) :
    let p := parameters ld n i b
    p.1 < ld ∧ p.2.1 < ld ∧ p.2.1 = p.1 + 1 ∧
      (b = true → 0 ≤ p.2.2 ∧ p.2.2 < (n : Int)) := by
  cases b with
  | false =>
    have hlow : 1 ≤ max 1 (min (ld - 1) (i * (ld + 1) / n)) := le_max_left _ _
    have hupp : max 1 (min (ld - 1) (i * (ld + 1) / n)) ≤ ld - 1 :=
      max_le (by omega) (min_le_left _ _)
    simp only [parameters, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro hb
    cases hb
  | true =>
    have hm : i * (ld - 1) < n * (ld - 1) :=
      Nat.mul_lt_mul_of_pos_right hi' (by omega)
    have hd : i * (ld - 1) / n < ld - 1 :=
      (Nat.div_lt_iff_lt_mul hn).mpr (by nlinarith)
    have hr := Nat.mod_lt (i * (ld - 1)) hn
    simp only [parameters, ↓reduceIte]
    refine ⟨by omega, by omega, trivial, ?_⟩
    intro _
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast hr⟩

theorem indices_thm {data : List α} {n : Int} {method : String}
    (h : Pre data n method) : indices_prop data n method := by
  intro k hk
  have hn : 0 < n.toNat := by have := h.2.1; omega
  have hs := parameters_safe h.1 hn (by omega : 1 ≤ k + 1)
    (by omega : k + 1 < n.toNat) (method == "inclusive")
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩
  intro hm
  have hb : (method == "inclusive") = true := by simp [hm]
  have := hs.2.2.2 hb
  have := h.2.1
  omega

def one_prop (O : Numeric α) (data : List α) (n : Int) (method : String) : Prop :=
  n = 1 → benchmark O data n method = .ok []

theorem one_thm (O : Numeric α) {data : List α} {n : Int} {method : String}
    (h : Pre data n method) : one_prop O data n method := by
  intro hn
  rw [benchmark_valid O h, hn]
  simp [core]


/-- Sorting is canonical for a linear order, so input order is irrelevant. -/
def permutation_prop (O : Numeric α) (data : List α) (n : Int) (method : String) : Prop :=
  ∀ other, data.Perm other → benchmark O data n method = benchmark O other n method

theorem permutation_thm [LinearOrder α] (O : Numeric α)
    (ho : O.le = fun a b => decide (a ≤ b)) (data : List α) (n : Int) (method : String) :
    permutation_prop O data n method := by
  intro other hp
  have hs : data.mergeSort O.le = other.mergeSort O.le := by
    rw [ho]
    exact List.eq_of_perm_of_sorted
      ((List.mergeSort_perm _ _).trans (hp.trans (List.mergeSort_perm _ _).symm))
      (List.sorted_mergeSort' (· ≤ ·) _) (List.sorted_mergeSort' (· ≤ ·) _)
  simp only [benchmark, quantiles, core, hp.length_eq, hs]

/-- Access in a sorted list is monotone wherever the subscripts are valid. -/
theorem sorted_getD_mono {xs : List ℝ} (hs : xs.Sorted (· ≤ ·))
    {a b : Nat} (ha : a < xs.length) (hb : b < xs.length) (hab : a ≤ b) :
    xs.getD a 0 ≤ xs.getD b 0 := by
  rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]
  exact hs.rel_get_of_le (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) hab

theorem real_sorted (data : List ℝ) : (data.mergeSort RealLayer.ops.le).Sorted (· ≤ ·) :=
  List.sorted_mergeSort' (· ≤ ·) data

theorem interpolate_bounds {a b : ℝ} {n : Nat} {d : Int}
    (hab : a ≤ b) (hn : 0 < n) (hd : 0 ≤ d) (hdn : d ≤ (n : Int)) :
    a ≤ interpolate RealLayer.ops a b n d ∧ interpolate RealLayer.ops a b n d ≤ b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hdnR : (d : ℝ) ≤ n := by exact_mod_cast hdn
  simp only [interpolate, RealLayer.ops, Int.cast_sub, Int.cast_natCast]
  constructor
  · apply (le_div_iff₀ hnR).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) hdR]
  · apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hdnR)]

/-- Inclusive cut points lie between the sample minimum and maximum. -/
def inclusive_bounds_prop (O : Numeric α) (data : List α) (n : Int) (method : String)
    [LE α] : Prop :=
  method = "inclusive" → ∀ ys, benchmark O data n method = .ok ys →
    ∀ z ∈ ys, (data.mergeSort O.le).getD 0 O.zero ≤ z ∧
      z ≤ (data.mergeSort O.le).getD (data.length - 1) O.zero

theorem inclusive_bounds_thm {data : List ℝ} {n : Int} {method : String}
    (h : Pre data n method) : inclusive_bounds_prop RealLayer.ops data n method := by
  intro hm ys hy z hz
  subst method
  rw [benchmark_valid RealLayer.ops h] at hy
  cases hy
  simp only [core, List.mem_map] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  have hk' : k < n.toNat - 1 := List.mem_range.mp hk
  have hp := indices_thm h k hk'
  simp only [beq_self_eq_true] at hp ⊢
  let xs := data.mergeSort RealLayer.ops.le
  let p := parameters data.length n.toNat (k + 1) true
  have hlen : xs.length = data.length := List.length_mergeSort _
  have ha : p.1 < xs.length := by simpa [p, hlen] using hp.1
  have hb : p.2.1 < xs.length := by simpa [p, hlen] using hp.2.1
  have hab : p.1 ≤ p.2.1 := by dsimp [p]; omega
  have hn : 0 < n.toNat := by have := h.2.1; omega
  have hd : 0 ≤ p.2.2 ∧ p.2.2 ≤ (n.toNat : Int) := by
    have hd := hp.2.2.2 trivial
    have := h.2.1
    dsimp [p]
    omega
  have hi := interpolate_bounds (sorted_getD_mono (real_sorted data) ha hb hab) hn hd.1 hd.2
  have hlo := sorted_getD_mono (real_sorted data) (by omega : 0 < xs.length) ha (Nat.zero_le _)
  have hhi := sorted_getD_mono (real_sorted data) hb
    (by have := h.1; omega : data.length - 1 < xs.length) (by omega)
  change xs.getD 0 0 ≤ cut RealLayer.ops xs n.toNat true (k + 1) ∧
    cut RealLayer.ops xs n.toNat true (k + 1) ≤ xs.getD (data.length - 1) 0
  simpa only [cut, hlen, ← show parameters data.length n.toNat (k + 1) true = p from rfl]
    using And.intro (hlo.trans hi.1) (hi.2.trans hhi)

def constant_prop (O : Numeric α) (data : List α) (n : Int) (method : String) : Prop :=
  ∀ x, data = List.replicate data.length x →
    benchmark O data n method = .ok (List.replicate (n.toNat - 1) x)

theorem interpolate_constant (x : ℝ) {n : Nat} (hn : 0 < n) (d : Int) :
    interpolate RealLayer.ops x x n d = x := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [interpolate, RealLayer.ops, Int.cast_sub, Int.cast_natCast]
  apply (div_eq_iff hnR).mpr
  ring

theorem constant_thm {data : List ℝ} {n : Int} {method : String}
    (h : Pre data n method) : constant_prop RealLayer.ops data n method := by
  intro x hx
  rw [benchmark_valid RealLayer.ops h]
  congr 1
  unfold core
  have hc : ∀ j < (data.mergeSort RealLayer.ops.le).length,
      (data.mergeSort RealLayer.ops.le).getD j 0 = x := by
    intro j hj
    rw [List.getD_eq_getElem _ _ hj]
    have hm := (List.mergeSort_perm data RealLayer.ops.le).mem_iff.mp (List.getElem_mem hj)
    have hm' : (data.mergeSort RealLayer.ops.le)[j] ∈ List.replicate data.length x :=
      hx ▸ hm
    exact (List.mem_replicate.mp hm').2
  have hn : 0 < n.toNat := by have := h.2.1; omega
  have he : ∀ k ∈ List.range (n.toNat - 1),
      cut RealLayer.ops (data.mergeSort RealLayer.ops.le) n.toNat (method == "inclusive") (k+1) = x := by
    intro k hk
    have hp := indices_thm h k (List.mem_range.mp hk)
    simp only [cut, List.length_mergeSort]
    change interpolate RealLayer.ops
      ((data.mergeSort RealLayer.ops.le).getD _ 0)
      ((data.mergeSort RealLayer.ops.le).getD _ 0) _ _ = x
    rw [hc _ (by simpa using hp.1), hc _ (by simpa using hp.2.1)]
    exact interpolate_constant x hn _
  rw [List.map_congr_left he]
  simp


/-- Exact correspondence, not a renaming of numeric layers. -/
theorem interpolate_rat_real (a b : ℚ) (n : Nat) (d : Int) :
    ((interpolate RatLayer.ops a b n d : ℚ) : ℝ) =
      interpolate RealLayer.ops (a : ℝ) (b : ℝ) n d := by
  simp [interpolate, RatLayer.ops, RealLayer.ops]

theorem getD_rat_real (xs : List ℚ) (i : Nat) :
    (xs.map (fun q : ℚ => (q : ℝ))).getD i 0 = ((xs.getD i 0 : ℚ) : ℝ) := by
  simpa using List.getD_map xs (0 : ℚ) (n := i) (fun q : ℚ => (q : ℝ))

theorem core_rat_real (xs : List ℚ) (n : Nat) (b : Bool) :
    (core RatLayer.ops xs n b).map (fun q : ℚ => (q : ℝ)) =
      core RealLayer.ops (xs.map (fun q : ℚ => (q : ℝ))) n b := by
  have hs : (xs.mergeSort RatLayer.ops.le).map (fun q : ℚ => (q : ℝ)) =
      (xs.map (fun q : ℚ => (q : ℝ))).mergeSort RealLayer.ops.le := by
    apply List.map_mergeSort
    intro a _ b _
    simp [RatLayer.ops, RealLayer.ops]
  simp only [core, List.map_map, ← hs]
  apply List.map_congr_left
  intro k _
  dsimp only [Function.comp_def, cut]
  simp only [List.length_map]
  change ((interpolate RatLayer.ops _ _ _ _ : ℚ) : ℝ) = interpolate RealLayer.ops
    (((xs.mergeSort RatLayer.ops.le).map (fun q : ℚ => (q : ℝ))).getD _ 0)
    (((xs.mergeSort RatLayer.ops.le).map (fun q : ℚ => (q : ℝ))).getD _ 0) _ _
  rw [getD_rat_real, getD_rat_real, interpolate_rat_real]
  rfl

theorem benchmark_rat_real (xs : List ℚ) (n : Int) (method : String) :
    (benchmark RatLayer.ops xs n method).map (List.map (fun q : ℚ => (q : ℝ))) =
      benchmark RealLayer.ops (xs.map (fun q : ℚ => (q : ℝ))) n method := by
  simp only [benchmark, quantiles, List.length_map]
  split_ifs <;> simp_all [Except.map, core_rat_real]

/-- As rank increases, the adjacent pair moves right. Between different pairs,
the earlier cut is no farther right than its right endpoint and the later cut
is no farther left than its left endpoint, even in the exclusive method. -/
theorem parameters_order {ld n i j : Nat} (hl : 2 ≤ ld) (hn : 0 < n)
    (hij : i ≤ j) (inc : Bool) :
    let p := parameters ld n i inc
    let q := parameters ld n j inc
    p.1 ≤ q.1 ∧ (p.1 = q.1 → p.2.2 ≤ q.2.2) ∧
      (p.1 < q.1 → p.2.2 ≤ (n : Int) ∧ 0 ≤ q.2.2) := by
  cases inc with
  | true =>
    have hm := Nat.mul_le_mul_right (ld - 1) hij
    have hd := Nat.div_le_div_right hm (c := n)
    have hr := Nat.mod_lt (i * (ld - 1)) hn
    simp only [parameters, ↓reduceIte]
    refine ⟨hd, ?_, ?_⟩
    · intro he
      have hmi := Nat.mod_add_div (i * (ld - 1)) n
      have hmj := Nat.mod_add_div (j * (ld - 1)) n
      rw [he] at hmi
      exact_mod_cast (show i * (ld - 1) % n ≤ j * (ld - 1) % n by omega)
    · intro _
      exact ⟨by exact_mod_cast (Nat.le_of_lt hr), Int.natCast_nonneg _⟩
  | false =>
    let a := max 1 (min (ld - 1) (i * (ld + 1) / n))
    let b := max 1 (min (ld - 1) (j * (ld + 1) / n))
    have ha : 1 ≤ a := le_max_left _ _
    have hb : 1 ≤ b := le_max_left _ _
    have hau : a ≤ ld - 1 := max_le (by omega) (min_le_left _ _)
    have hbu : b ≤ ld - 1 := max_le (by omega) (min_le_left _ _)
    have hm := Nat.mul_le_mul_right (ld + 1) hij
    have hd := Nat.div_le_div_right hm (c := n)
    have hab : a ≤ b := max_le_max le_rfl (min_le_min_left _ hd)
    change a - 1 ≤ b - 1 ∧
      (a - 1 = b - 1 → ((i * (ld + 1) : Nat) : Int) - ↑(a * n) ≤ ↑(j * (ld + 1)) - ↑(b * n)) ∧
      (a - 1 < b - 1 → ((i * (ld + 1) : Nat) : Int) - ↑(a * n) ≤ ↑n ∧
        0 ≤ ((j * (ld + 1) : Nat) : Int) - ↑(b * n))
    refine ⟨by omega, ?_, ?_⟩
    · intro he
      have he' : a = b := by omega
      rw [he']
      exact sub_le_sub_right (by exact_mod_cast hm) _
    · intro hlt
      have hqa : i * (ld + 1) / n ≤ a := by dsimp [a, b] at *; omega
      have hqb : b ≤ j * (ld + 1) / n := by dsimp [a, b] at *; omega
      have htA : i * (ld + 1) < (a + 1) * n :=
        (Nat.div_lt_iff_lt_mul hn).mp (by omega)
      have htB : b * n ≤ j * (ld + 1) := (Nat.le_div_iff_mul_le hn).mp hqb
      have htAR : ((i * (ld + 1) : Nat) : Int) < ((a : Int) + 1) * (n : Int) := by
        exact_mod_cast htA
      have htBR : (b : Int) * (n : Int) ≤ ((j * (ld + 1) : Nat) : Int) := by
        exact_mod_cast htB
      constructor
      · push_cast at htAR ⊢
        nlinarith
      · push_cast at htBR ⊢
        linarith

theorem interpolate_mono_delta {a b : ℝ} {n : Nat} {d e : Int}
    (hab : a ≤ b) (hn : 0 < n) (hde : d ≤ e) :
    interpolate RealLayer.ops a b n d ≤ interpolate RealLayer.ops a b n e := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdeR : (d : ℝ) ≤ e := by exact_mod_cast hde
  simp only [interpolate, RealLayer.ops, Int.cast_sub, Int.cast_natCast]
  apply (div_le_div_iff_of_pos_right hnR).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hdeR)]

theorem interpolate_le_right {a b : ℝ} {n : Nat} {d : Int}
    (hab : a ≤ b) (hn : 0 < n) (hd : d ≤ (n : Int)) :
    interpolate RealLayer.ops a b n d ≤ b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (d : ℝ) ≤ n := by exact_mod_cast hd
  simp only [interpolate, RealLayer.ops, Int.cast_sub, Int.cast_natCast]
  apply (div_le_iff₀ hnR).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hdR)]

theorem left_le_interpolate {a b : ℝ} {n : Nat} {d : Int}
    (hab : a ≤ b) (hn : 0 < n) (hd : 0 ≤ d) :
    a ≤ interpolate RealLayer.ops a b n d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
  simp only [interpolate, RealLayer.ops, Int.cast_sub, Int.cast_natCast]
  apply (le_div_iff₀ hnR).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) hdR]

theorem cut_mono {xs : List ℝ} (hs : xs.Sorted (· ≤ ·)) (hl : 2 ≤ xs.length)
    {n i j : Nat} (hn : 0 < n) (hi : 1 ≤ i) (hj : j < n) (hij : i ≤ j) (inc : Bool) :
    cut RealLayer.ops xs n inc i ≤ cut RealLayer.ops xs n inc j := by
  have hp := parameters_safe hl hn hi (by omega : i < n) inc
  have hq := parameters_safe hl hn (by omega : 1 ≤ j) hj inc
  have ho := parameters_order hl hn hij inc
  let p := parameters xs.length n i inc
  let q := parameters xs.length n j inc
  have hpa : p.2.1 = p.1 + 1 := hp.2.2.1
  have hqa : q.2.1 = q.1 + 1 := hq.2.2.1
  have hpq : p.1 ≤ q.1 := ho.1
  change interpolate RealLayer.ops (xs.getD p.1 0) (xs.getD p.2.1 0) n p.2.2 ≤
    interpolate RealLayer.ops (xs.getD q.1 0) (xs.getD q.2.1 0) n q.2.2
  have hpab := sorted_getD_mono hs hp.1 hp.2.1 (by omega : p.1 ≤ p.2.1)
  have hqab := sorted_getD_mono hs hq.1 hq.2.1 (by omega : q.1 ≤ q.2.1)
  by_cases he : p.1 = q.1
  · have he' : p.2.1 = q.2.1 := by omega
    rw [he, he']
    exact interpolate_mono_delta hqab hn (ho.2.1 he)
  · have hlt : p.1 < q.1 := by omega
    have hd := ho.2.2 hlt
    have hbridge : p.2.1 ≤ q.1 := by omega
    exact (interpolate_le_right hpab hn hd.1).trans
      ((sorted_getD_mono hs hp.2.1 hq.1 hbridge).trans (left_le_interpolate hqab hn hd.2))

/-- The returned cuts are nondecreasing for both methods. -/
def monotone_prop (O : Numeric α) [LE α] (data : List α) (n : Int) (method : String) : Prop :=
  ∀ ys, benchmark O data n method = .ok ys → ys.Pairwise (· ≤ ·)

theorem monotone_thm {data : List ℝ} {n : Int} {method : String}
    (h : Pre data n method) : monotone_prop RealLayer.ops data n method := by
  intro ys hy
  rw [benchmark_valid RealLayer.ops h] at hy
  cases hy
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [core, List.length_map, List.length_range] at hi hj
  simp only [core, List.getElem_map, List.getElem_range]
  apply cut_mono (real_sorted data) (by simpa using h.1)
    (by have := h.2.1; omega) (by omega) (by omega) (by omega)

/-- Successful output size, the exact interpolation rule, safe reads, edge case,
order independence, population bounds, constant-sample preservation, and
nondecreasing cut points. -/
def Post_prop (O : Numeric α) [LE α] (data : List α) (n : Int) (method : String) : Prop :=
  length_prop O data n method ∧ formula_prop O data n method ∧
  indices_prop data n method ∧ one_prop O data n method ∧
  permutation_prop O data n method ∧ inclusive_bounds_prop O data n method ∧
  constant_prop O data n method ∧ monotone_prop O data n method ∧ error_prop O data n method

/-! ## Bounded property-based tests

Real comparisons are noncomputable. The inclusive-bounds, monotonicity, and constant-data
properties, and the mathematical postcondition, are tested on the exact Rat
counterpart, not by approximating Real comparisons. These checks are evidence;
none is used to prove a theorem. All lists of length ≤ 3 over {-2,-1,0,1,2},
all counts from -2 through 11, and all three method strings are included.
-/

def smallSamples : List (List ℚ) :=
  (List.range 4).flatMap fun len =>
    (List.range (5 ^ len)).map fun code =>
      (List.range len).map fun j => ((code / 5 ^ j % 5 : Nat) : ℚ) - 2

def testCases : List (List ℚ × Int × String) :=
  smallSamples.flatMap fun xs => (List.range 14).flatMap fun k =>
    ["inclusive", "exclusive", "invalid"].map fun m => (xs, (k : Int) - 2, m)

def errorCheck (xs : List ℚ) (n : Int) (m : String) : Bool :=
  if Pre xs n m then true else decide (benchmark RatLayer.ops xs n m = .error .statisticsError)

def lengthCheck (xs : List ℚ) (n : Int) (m : String) : Bool :=
  if Pre xs n m then
    decide ((benchmark RatLayer.ops xs n m).map List.length = .ok (n.toNat - 1))
  else true

def formulaCheck (xs : List ℚ) (n : Int) (m : String) : Bool :=
  if Pre xs n m then (List.range (n.toNat - 1)).all fun k =>
    decide ((benchmark RatLayer.ops xs n m).toOption.bind (fun ys => ys[k]?) =
      some (cut RatLayer.ops (xs.mergeSort RatLayer.ops.le) n.toNat (m == "inclusive") (k+1)))
  else true

def indicesCheck (xs : List ℚ) (n : Int) (m : String) : Bool :=
  if Pre xs n m then (List.range (n.toNat - 1)).all fun k =>
    let p := parameters xs.length n.toNat (k+1) (m == "inclusive")
    decide (p.1 < xs.length ∧ p.2.1 < xs.length ∧ p.2.1 = p.1 + 1 ∧
      (m = "inclusive" → 0 ≤ p.2.2 ∧ p.2.2 < n))
  else true

def oneCheck (xs : List ℚ) (n : Int) (m : String) : Bool :=
  if Pre xs n m ∧ n = 1 then decide (benchmark RatLayer.ops xs n m = .ok []) else true

def permutationCheck (xs : List ℚ) (n : Int) (m : String) : Bool :=
  xs.permutations.all fun ys => decide (benchmark RatLayer.ops xs n m = benchmark RatLayer.ops ys n m)

def boundsCheck (xs : List ℚ) (n : Int) (m : String) : Bool :=
  if Pre xs n m ∧ m = "inclusive" then
    match benchmark RatLayer.ops xs n m with
    | .error _ => false
    | .ok ys => ys.all fun z => decide ((xs.mergeSort RatLayer.ops.le).getD 0 0 ≤ z ∧
        z ≤ (xs.mergeSort RatLayer.ops.le).getD (xs.length - 1) 0)
  else true

def constantCheck (xs : List ℚ) (n : Int) (m : String) : Bool :=
  if Pre xs n m then
    match xs with
    | [] => false
    | x :: _ => if xs = List.replicate xs.length x then
        decide (benchmark RatLayer.ops xs n m = .ok (List.replicate (n.toNat - 1) x))
      else true
  else true

-- Executable exact counterpart of the Real monotonicity property.
def monotoneCheck (xs : List ℚ) (n : Int) (m : String) : Bool :=
  if Pre xs n m then
    match benchmark RatLayer.ops xs n m with
    | .error _ => false
    | .ok ys => decide (ys.Pairwise (· ≤ ·))
  else true

def postCheck (xs : List ℚ) (n : Int) (m : String) : Bool :=
  errorCheck xs n m && lengthCheck xs n m && formulaCheck xs n m &&
  indicesCheck xs n m && oneCheck xs n m && permutationCheck xs n m &&
  boundsCheck xs n m && constantCheck xs n m && monotoneCheck xs n m

-- One PBT per property, followed by the conjunction/postcondition PBT.
example : testCases.all (fun (xs, n, m) => errorCheck xs n m) = true := by native_decide
example : testCases.all (fun (xs, n, m) => lengthCheck xs n m) = true := by native_decide
example : testCases.all (fun (xs, n, m) => formulaCheck xs n m) = true := by native_decide
example : testCases.all (fun (xs, n, m) => indicesCheck xs n m) = true := by native_decide
example : testCases.all (fun (xs, n, m) => oneCheck xs n m) = true := by native_decide
example : testCases.all (fun (xs, n, m) => permutationCheck xs n m) = true := by native_decide
example : testCases.all (fun (xs, n, m) => boundsCheck xs n m) = true := by native_decide
example : testCases.all (fun (xs, n, m) => constantCheck xs n m) = true := by native_decide
example : testCases.all (fun (xs, n, m) => monotoneCheck xs n m) = true := by native_decide
example : testCases.all (fun (xs, n, m) => postCheck xs n m) = true := by native_decide
#eval testCases.length

/-- Mathematical correctness; structural conjuncts also hold for Float. -/
theorem correctness {data : List ℝ} {n : Int} {method : String} :
    Pre data n method → Post_prop RealLayer.ops data n method := by
  intro h
  exact ⟨length_thm _ h, formula_thm _ h, indices_thm h, one_thm _ h,
    permutation_thm _ rfl _ _ _, inclusive_bounds_thm h, constant_thm h, monotone_thm h,
    error_thm _ _ _ _⟩

/-! ## Imperative implementation -/

def appendLoop (f : Nat → α) (ks : List Nat) (acc : List α) : List α := Id.run do
  let mut result := acc
  for k in ks do
    result := result ++ [f k]
  return result

def coreImperative (O : Numeric α) (data : List α) (n : Nat) (inclusive : Bool) : List α := Id.run do
  let sorted := data.mergeSort O.le
  let mut result := []
  for k in List.range (n - 1) do
    let p := parameters sorted.length n (k + 1) inclusive
    let interpolated := interpolate O (sorted.getD p.1 O.zero) (sorted.getD p.2.1 O.zero) n p.2.2
    result := result ++ [interpolated]
  return result

def benchmarkImperative (O : Numeric α) (data : List α) (n : Int := 4)
    (method : String := "exclusive") : Except Error (List α) := Id.run do
  if ¬ (data.length ≥ 2 ∧ n ≥ 1 ∧ (method = "inclusive" ∨ method = "exclusive")) then
    return .error .statisticsError
  let mut result := []
  if method = "inclusive" then
    result := coreImperative O data n.toNat true
  else
    result := coreImperative O data n.toNat false
  return .ok result

example : benchmarkImperative RatLayer.ops [1, 2, 3, 4] = .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmarkImperative RatLayer.ops [1, 2, 3, 4] 4 "inclusive" =
    .ok [7/4, 5/2, 13/4] := by native_decide
example : benchmarkImperative RatLayer.ops [1, 2] 0 = .error .statisticsError := by native_decide
example : benchmarkImperative RatLayer.ops [1, 2] 4 "bad" = .error .statisticsError := by native_decide
example : testCases.all (fun (xs, n, m) =>
    decide (benchmarkImperative RatLayer.ops xs n m = benchmark RatLayer.ops xs n m)) = true := by native_decide
#eval benchmarkImperative FloatLayer.ops [1.5, 2.5, 3.5, 4.5] 2

/-- The loop invariant holds for an arbitrary prefix accumulator. -/
theorem appendLoop_eq (f : Nat → α) (ks : List Nat) (acc : List α) :
    appendLoop f ks acc = acc ++ ks.map f := by
  induction ks generalizing acc with
  | nil => simp [appendLoop]
  | cons k ks ih =>
    simp only [appendLoop, List.forIn_cons, Id.run, bind, pure] at *
    rw [ih]
    simp

theorem core_equivalence (O : Numeric α) (data : List α) (n : Nat) (b : Bool) :
    core O data n b = coreImperative O data n b := by
  change _ = appendLoop (fun k => cut O (data.mergeSort O.le) n b (k+1)) (List.range (n-1)) []
  rw [appendLoop_eq]
  simp [core]

/-- Equality includes errors and holds for any numeric operations, thus also
for the actual Float execution layer. No Real-to-Float exactness is assumed. -/
theorem equivalence (O : Numeric α) (data : List α) (n : Int) (method : String) :
    benchmark O data n method = benchmarkImperative O data n method := by
  by_cases h : Pre data n method
  · rw [benchmark_valid O h]
    rcases h with ⟨hl, hn, hm⟩
    rcases hm with rfl | rfl <;>
      simp [benchmarkImperative, hl, hn, core_equivalence]
  · have he := error_thm O data n method h
    rw [he]
    have h' : ¬ (data.length ≥ 2 ∧ n ≥ 1 ∧
        (method = "inclusive" ∨ method = "exclusive")) := h
    simp [benchmarkImperative, h']

end StatisticsQuantiles
