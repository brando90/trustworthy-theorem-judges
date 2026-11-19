import Mathlib
namespace Agent

/-!
# Median of numerical data

The mathematical layer works over any linearly ordered field, in particular `ℝ`:
inputs are not restricted to rationals. Lists model both Python lists and tuples;
the element type supplies the numeric part of the precondition. `Except` models
`StatisticsError`, including the separate precondition and empty-median errors.
The exact executable tests use `ℚ` (including fractions and finite decimals).
`FloatLayer` retains machine floating-point arithmetic for the float examples.
The field theorems are mathematical statements, not assertions that IEEE
arithmetic is exact. Python's sorting of non-orderable numbers (e.g. complex
numbers), dynamic type errors, and mixed-type coercion are not field operations.
-/

namespace StatisticsMedian

inductive StatisticsError where
  | noMedian
  | requiresNumbers
  deriving DecidableEq, Repr

/-- The two exception constructors retain the original Python messages. -/
def StatisticsError.message : StatisticsError → String
  | .noMedian => "no median for empty data"
  | .requiresNumbers => "benchmark_median requires a non-empty list/tuple of numbers"

deriving instance DecidableEq for Except

abbrev Result (α : Type*) := Except StatisticsError α

/-- Select from already sorted data, with the same parity branches as Python. -/
def middle {α : Type*} [Inhabited α] [Add α] [Div α] [OfNat α 2]
    (data : List α) : Result α :=
  let n := data.length
  if n = 0 then .error .noMedian
  else if n % 2 = 1 then .ok (data.getD (n / 2) default)
  else
    let i := n / 2
    .ok ((data.getD (i - 1) default + data.getD i default) / 2)

def sorted {α : Type*} [LinearOrder α] (data : List α) : List α :=
  data.mergeSort (fun a b => decide (a ≤ b))

/-- The library median, before the benchmark's precondition check. -/
def median {α : Type*} [LinearOrder α] [Inhabited α] [Add α] [Div α] [OfNat α 2]
    (data : List α) : Result α := middle (sorted data)

/-- Typed translation of `benchmark_median`. -/
def benchmarkMedian {α : Type*} [LinearOrder α] [Inhabited α]
    [Add α] [Div α] [OfNat α 2] (data : List α) : Result α :=
  if data.length = 0 then .error .requiresNumbers else median data

namespace FloatLayer

def median (data : List Float) : Result Float :=
  middle (data.mergeSort (fun a b => a ≤ b))

def benchmarkMedian (data : List Float) : Result Float :=
  if data.length = 0 then .error .requiresNumbers else median data

end FloatLayer

/-- Repeat each observation twice, preserving its position. -/
def duplicate {α : Type*} : List α → List α
  | [] => []
  | x :: xs => x :: x :: duplicate xs

/-! The dynamic boundary records container and element validation separately
from numerical operations. `none` represents a non-number; `some x` a number.
All rejected Python object types can be represented by `Input.other`. -/
namespace Dynamic

inductive Input (α : Type*) where
  | list (items : List (Option α))
  | tuple (items : List (Option α))
  | other
  deriving Repr

def payload {α : Type*} : Input α → List (Option α)
  | .list xs | .tuple xs => xs
  | .other => []

/-- Literal Boolean translation of the source precondition. -/
def pre {α : Type*} : Input α → Bool
  | .list xs | .tuple xs => !xs.isEmpty && xs.all Option.isSome
  | .other => false

def numbers {α : Type*} [Inhabited α] (input : Input α) : List α :=
  (payload input).map (fun x => x.getD default)

def benchmarkMedian {α : Type*} [LinearOrder α] [Inhabited α]
    [Add α] [Div α] [OfNat α 2] (input : Input α) : Result α :=
  if pre input then StatisticsMedian.benchmarkMedian (numbers input)
  else .error .requiresNumbers

end Dynamic

-- Fixed tests: odd/even lengths, fractions, decimal values, singleton, unsorted,
-- duplication, and the two distinct error paths.
example : benchmarkMedian ([1, 2, 3, 4, 5, 6, 9] : List ℚ) = .ok 4 := by native_decide
example : benchmarkMedian ([1/7, 2/7, 3/7] : List ℚ) = .ok (2/7) := by native_decide
example : benchmarkMedian ([1, 2, 3, 4, 5, 6] : List ℚ) = .ok (7/2) := by native_decide
example : benchmarkMedian ([1, 3, 5, 7] : List ℚ) = .ok 4 := by native_decide
example : benchmarkMedian ([25/10, 31/10, 42/10] : List ℚ) = .ok (31/10) := by native_decide
example : benchmarkMedian ([42] : List ℚ) = .ok 42 := by native_decide
example : benchmarkMedian ([9, 1, 6, 2, 5, 4, 3] : List ℚ) = .ok 4 := by native_decide
example : benchmarkMedian ([3/2, 3/2, 5/2, 5/2, 39/4, 39/4] : List ℚ) =
    benchmarkMedian ([3/2, 5/2, 39/4] : List ℚ) := by native_decide
example : benchmarkMedian ([] : List ℚ) = .error .requiresNumbers := by native_decide
example : median ([] : List ℚ) = .error .noMedian := by native_decide
example : (match FloatLayer.benchmarkMedian [1.0, 2.0, 3.0, 4.0, 5.0, 6.0] with
    | .ok x => x == 3.5 | .error _ => false) = true := by native_decide
example : (match FloatLayer.benchmarkMedian [2.5, 3.1, 4.2] with
    | .ok x => x == 3.1 | .error _ => false) = true := by native_decide
#eval benchmarkMedian ([9, 1, 6, 2, 5, 4, 3] : List ℚ)
#eval FloatLayer.benchmarkMedian [1.0, 3.0, 5.0, 7.0]

example : Dynamic.benchmarkMedian (.tuple [some 1, some 3, some 5, some 7] : Dynamic.Input ℚ) =
    .ok 4 := by native_decide
example : Dynamic.benchmarkMedian (.list [some 1, none] : Dynamic.Input ℚ) =
    .error .requiresNumbers := by native_decide
example : Dynamic.benchmarkMedian (.other : Dynamic.Input ℚ) =
    .error .requiresNumbers := by native_decide
example : Dynamic.benchmarkMedian (.tuple [] : Dynamic.Input ℚ) =
    .error .requiresNumbers := by native_decide
example : (match FloatLayer.benchmarkMedian [1.5, 1.5, 2.5, 2.5, 9.75, 9.75],
    FloatLayer.benchmarkMedian [1.5, 2.5, 9.75] with
    | .ok x, .ok y => x == y | _, _ => false) = true := by native_decide
example : (match FloatLayer.benchmarkMedian [42.0] with
    | .ok x => x == 42.0 | .error _ => false) = true := by native_decide
#eval Dynamic.pre (.list [some (1 : ℚ), none])

/-- In the typed numeric domain, precisely the non-emptiness check remains. -/
def Pre {α : Type*} (data : List α) : Prop := data ≠ []



/-- Source-style precondition on untyped containers and possibly nonnumeric elements. -/
def InputPre {α : Type*} : Dynamic.Input α → Prop
  | .list xs | .tuple xs => xs ≠ [] ∧ ∀ x ∈ xs, x.isSome = true
  | .other => False

theorem input_pre_decides {α : Type*} (input : Dynamic.Input α) :
    Dynamic.pre input = true ↔ InputPre input := by
  cases input <;> simp [Dynamic.pre, InputPre, List.all_eq_true]

theorem input_numbers_pre {α : Type*} [Inhabited α] (input : Dynamic.Input α)
    (h : InputPre input) : Pre (Dynamic.numbers input) := by
  cases input <;> simp_all [InputPre, Pre, Dynamic.numbers, Dynamic.payload]

section Sorting
variable {α : Type*} [LinearOrder α]

theorem sorted_perm (xs : List α) : (sorted xs).Perm xs :=
  List.mergeSort_perm _ _

@[simp] theorem sorted_length (xs : List α) : (sorted xs).length = xs.length :=
  (sorted_perm xs).length_eq

theorem sorted_ordered (xs : List α) : (sorted xs).Sorted (· ≤ ·) :=
  List.sorted_mergeSort' _ _

theorem sorted_of_perm {xs ys : List α} (h : xs.Perm ys) : sorted xs = sorted ys :=
  List.eq_of_perm_of_sorted ((sorted_perm xs).trans (h.trans (sorted_perm ys).symm))
    (sorted_ordered xs) (sorted_ordered ys)

theorem sorted_eq_self {xs : List α} (h : xs.Sorted (· ≤ ·)) : sorted xs = xs :=
  List.eq_of_perm_of_sorted (sorted_perm xs) (sorted_ordered xs) h

end Sorting

section DuplicationLemmas
variable {α : Type*}

@[simp] theorem duplicate_length (xs : List α) : (duplicate xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [duplicate, ih]; omega

@[simp] theorem mem_duplicate (a : α) (xs : List α) : a ∈ duplicate xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [duplicate]
  | cons x xs ih => simp [duplicate, ih]

theorem duplicate_eq_flatMap (xs : List α) : duplicate xs = xs.flatMap (fun x => [x, x]) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [duplicate, ih]

theorem duplicate_perm {xs ys : List α} (h : xs.Perm ys) :
    (duplicate xs).Perm (duplicate ys) := by
  simpa only [duplicate_eq_flatMap] using
    (h.flatMap (f := fun x => [x, x]) (g := fun x => [x, x]) (fun _ _ => List.Perm.refl _))

theorem duplicate_ordered [LinearOrder α] {xs : List α} (h : xs.Sorted (· ≤ ·)) :
    (duplicate xs).Sorted (· ≤ ·) := by
  induction xs with
  | nil => simp [duplicate]
  | cons x xs ih =>
    obtain ⟨hh, ht⟩ := List.sorted_cons.mp h
    have hd : ∀ b ∈ duplicate xs, x ≤ b := fun b hb => hh b ((mem_duplicate b xs).mp hb)
    simpa only [duplicate, List.sorted_cons, List.mem_cons, forall_eq_or_imp] using
      And.intro (And.intro (le_refl x) hd) (And.intro hd (ih ht))

theorem sorted_duplicate [LinearOrder α] (xs : List α) :
    sorted (duplicate xs) = duplicate (sorted xs) := by
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact (sorted_perm _).trans (duplicate_perm (sorted_perm xs)).symm
  · exact sorted_ordered _
  · exact duplicate_ordered (sorted_ordered xs)

theorem getD_duplicate (xs : List α) (i : ℕ) (d : α) :
    (duplicate xs).getD i d = xs.getD (i / 2) d := by
  induction xs generalizing i with
  | nil => simp [duplicate]
  | cons x xs ih =>
    cases i with
    | zero => simp [duplicate, List.getD]
    | succ i =>
      cases i with
      | zero => simp [duplicate, List.getD]
      | succ i =>
        have he : (i + 1 + 1) / 2 = i / 2 + 1 := by omega
        simpa [duplicate, he, List.getD] using ih i

end DuplicationLemmas

section Properties
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Inhabited α]

/-- Both error paths occur exactly on empty input. -/
def error_prop (xs : List α) : Prop :=
  (benchmarkMedian xs = .error .requiresNumbers ↔ xs = []) ∧
  (median xs = .error .noMedian ↔ xs = [])

omit [IsStrictOrderedRing α] in
theorem error_thm (xs : List α) : error_prop xs := by
  unfold error_prop benchmarkMedian median middle
  simp only [sorted_length]
  by_cases h : xs.length = 0
  · simp [List.length_eq_zero_iff.mp h]
  · have hn : xs ≠ [] := by simpa using h
    by_cases ho : xs.length % 2 = 1 <;> simp [h, hn, ho]

/-- Every admissible input returns a number, not an exception. -/
def success_prop (xs : List α) : Prop := ∃ m, benchmarkMedian xs = .ok m

omit [IsStrictOrderedRing α] in
theorem success_thm (xs : List α) (h : Pre xs) : success_prop xs := by
  have hn : xs.length ≠ 0 := by simpa [Pre] using h
  unfold success_prop benchmarkMedian median middle
  simp only [sorted_length, hn, ↓reduceIte]
  split <;> exact ⟨_, rfl⟩

/-- The middle observation of sorted odd-length data is returned exactly. -/
def odd_prop (xs : List α) : Prop :=
  xs.length % 2 = 1 →
    benchmarkMedian xs = .ok ((sorted xs).getD (xs.length / 2) default)

omit [IsStrictOrderedRing α] in
theorem odd_thm (xs : List α) : odd_prop xs := by
  intro ho
  have hn : xs.length ≠ 0 := by omega
  simp [benchmarkMedian, median, middle, hn, ho]

/-- The average of the two central order statistics for even-length data. -/
def even_prop (xs : List α) : Prop :=
  xs.length % 2 = 0 → benchmarkMedian xs =
    .ok (((sorted xs).getD (xs.length / 2 - 1) default +
      (sorted xs).getD (xs.length / 2) default) / 2)

omit [IsStrictOrderedRing α] in
theorem even_thm (xs : List α) (h : Pre xs) : even_prop xs := by
  intro he
  have hn : xs.length ≠ 0 := by simpa [Pre] using h
  simp [benchmarkMedian, median, middle, hn, he]

omit [Field α] [IsStrictOrderedRing α] [Inhabited α] in
/-- All accessed indices really are in range; the default is never observed. -/
theorem middle_indices (xs : List α) (h : Pre xs) :
    xs.length / 2 < (sorted xs).length ∧
    (xs.length % 2 = 0 → 0 < xs.length / 2 ∧
      xs.length / 2 - 1 < (sorted xs).length) := by
  have hn : xs.length ≠ 0 := by simpa [Pre] using h
  rw [sorted_length]
  omega

/-- For odd length, the result is one of the original observations. -/
def odd_mem_prop (xs : List α) : Prop :=
  xs.length % 2 = 1 → ∃ m ∈ xs, benchmarkMedian xs = .ok m

omit [IsStrictOrderedRing α] in
theorem odd_mem_thm (xs : List α) : odd_mem_prop xs := by
  intro ho
  have hi : xs.length / 2 < (sorted xs).length := by rw [sorted_length]; omega
  refine ⟨(sorted xs).getD (xs.length / 2) default, ?_, odd_thm xs ho⟩
  rw [List.getD_eq_getElem _ _ hi]
  exact (sorted_perm xs).mem_iff.mp (List.getElem_mem hi)

/-- A singleton is returned unchanged. -/
def singleton_prop (xs : List α) : Prop :=
  ∀ x, xs = [x] → benchmarkMedian xs = .ok x

omit [IsStrictOrderedRing α] in
theorem singleton_thm (xs : List α) : singleton_prop xs := by
  rintro x rfl
  have hs : sorted [x] = [x] := sorted_eq_self (by simp)
  simp [benchmarkMedian, median, hs, middle, List.getD]

/-- Reordering inputs cannot affect the answer (including errors). -/
def permutation_prop (xs : List α) : Prop :=
  ∀ ys, xs.Perm ys → benchmarkMedian xs = benchmarkMedian ys

omit [IsStrictOrderedRing α] in
theorem permutation_thm (xs : List α) : permutation_prop xs := by
  intro ys hp
  simp only [benchmarkMedian, median, hp.length_eq, sorted_of_perm hp]

/-- The median lies in every closed interval containing all observations. -/
def bounds_prop (xs : List α) : Prop :=
  ∀ lo hi, (∀ x ∈ xs, lo ≤ x ∧ x ≤ hi) →
    ∀ m, benchmarkMedian xs = .ok m → lo ≤ m ∧ m ≤ hi

theorem bounds_thm (xs : List α) : bounds_prop xs := by
  intro lo hi hb m hm
  by_cases hz : xs.length = 0
  · simp [benchmarkMedian, hz] at hm
  have hget (i : ℕ) (hidx : i < (sorted xs).length) :
      lo ≤ (sorted xs).getD i default ∧ (sorted xs).getD i default ≤ hi := by
    rw [List.getD_eq_getElem _ _ hidx]
    exact hb _ ((sorted_perm xs).mem_iff.mp (List.getElem_mem hidx))
  have hi : xs.length / 2 < (sorted xs).length := by rw [sorted_length]; omega
  have hj : xs.length / 2 - 1 < (sorted xs).length := by rw [sorted_length]; omega
  simp only [benchmarkMedian, hz, ↓reduceIte, median, middle, sorted_length] at hm
  split_ifs at hm with ho
  · cases hm
    exact hget _ hi
  · cases hm
    obtain ⟨ha, hb⟩ := hget _ hj
    obtain ⟨hc, hd⟩ := hget _ hi
    constructor
    · apply (le_div_iff₀ (by norm_num : (0 : α) < 2)).2
      linarith
    · apply (div_le_iff₀ (by norm_num : (0 : α) < 2)).2
      linarith

/-- Repeating every observation twice leaves the median unchanged. -/
def duplication_prop (xs : List α) : Prop :=
  benchmarkMedian (duplicate xs) = benchmarkMedian xs

theorem middle_duplicate (xs : List α) : middle (duplicate xs) = middle xs := by
  by_cases hz : xs.length = 0
  · have hx := List.length_eq_zero_iff.mp hz
    simp [hx, duplicate]
  have hz2 : 2 * xs.length ≠ 0 := by omega
  have hdiv : 2 * xs.length / 2 = xs.length := by omega
  have hmod : (2 * xs.length) % 2 = 0 := by omega
  simp only [middle, duplicate_length, hz2, hz, ↓reduceIte, hdiv, hmod]
  simp only [show ¬ (0 : ℕ) = 1 by decide, ↓reduceIte, getD_duplicate]
  by_cases ho : xs.length % 2 = 1
  · have hi : (xs.length - 1) / 2 = xs.length / 2 := by omega
    simp only [ho, ↓reduceIte, hi]
    congr 1
    ring
  · have hi : (xs.length - 1) / 2 = xs.length / 2 - 1 := by omega
    simp [ho, hi]

theorem duplication_thm (xs : List α) : duplication_prop xs := by
  unfold duplication_prop benchmarkMedian
  by_cases hz : xs.length = 0
  · simp [duplicate_length, hz]
  · have hz2 : 2 * xs.length ≠ 0 := by omega
    simp [duplicate_length, hz, hz2, median, sorted_duplicate, middle_duplicate]

/-- The dynamic validation boundary rejects exactly the inadmissible inputs. -/
def validation_prop (input : Dynamic.Input α) : Prop :=
  Dynamic.benchmarkMedian input = .error .requiresNumbers ↔ ¬ InputPre input

omit [IsStrictOrderedRing α] in
theorem validation_thm (input : Dynamic.Input α) : validation_prop input := by
  by_cases h : Dynamic.pre input = true
  · have hp := (input_pre_decides input).mp h
    have hn : Dynamic.numbers input ≠ [] := input_numbers_pre input hp
    simp [validation_prop, Dynamic.benchmarkMedian, h, hp, (error_thm _).1, hn]
  · have hp : ¬ InputPre input := fun hp => h ((input_pre_decides input).mpr hp)
    simp [validation_prop, Dynamic.benchmarkMedian, h, hp]

omit [IsStrictOrderedRing α] in
theorem input_list_refinement_thm (xs : List α) :
    Dynamic.benchmarkMedian (.list (xs.map some)) = benchmarkMedian xs := by
  by_cases h : xs = []
  · subst xs
    simp [Dynamic.benchmarkMedian, Dynamic.pre, benchmarkMedian]
  · simp [Dynamic.benchmarkMedian, Dynamic.pre, Dynamic.numbers, Dynamic.payload,
      h, List.map_map, Function.comp_def]

omit [IsStrictOrderedRing α] in
theorem input_tuple_refinement_thm (xs : List α) :
    Dynamic.benchmarkMedian (.tuple (xs.map some)) = benchmarkMedian xs := by
  exact input_list_refinement_thm xs

/-- Complete contract, with both structural and numerical guarantees. -/
def Post_prop (xs : List α) : Prop :=
  error_prop xs ∧ success_prop xs ∧ odd_prop xs ∧ even_prop xs ∧
  odd_mem_prop xs ∧ singleton_prop xs ∧ permutation_prop xs ∧
  bounds_prop xs ∧ duplication_prop xs

/-- Contract for an admissible dynamic input, connected to the typed model. -/
def InputPost_prop (input : Dynamic.Input α) : Prop :=
  validation_prop input ∧ Post_prop (Dynamic.numbers input) ∧
    Dynamic.benchmarkMedian input = benchmarkMedian (Dynamic.numbers input)

end Properties


/-!
## Property-based tests

Each executable check below names its corresponding property. The generic
properties include `ℝ`, whose comparisons are not executable. These are their
exact rational executable counterparts; the field theorems above retain their
original domain. The finite generator exhausts lengths 0 through 4 over five
rational observations, including negative, zero, fractional and repeated data.
Permutation checks enumerate *all* permutations of each generated list.
The bounds check varies both endpoints as well as the data.
-/
namespace PBT

def alphabet : List ℚ := [-3/2, -1/7, 0, 2/7, 5/2]

def words : ℕ → List (List ℚ)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun x => (words n).map (x :: ·)

def samples : List (List ℚ) := (List.range 5).flatMap words

def admissible : List (List ℚ) := samples.filter (fun xs => !xs.isEmpty)

def errorCheck (xs : List ℚ) : Bool :=
  decide ((benchmarkMedian xs = .error .requiresNumbers ↔ xs = []) ∧
    (median xs = .error .noMedian ↔ xs = []))

def successCheck (xs : List ℚ) : Bool :=
  match benchmarkMedian xs with | .ok _ => true | .error _ => false

def oddCheck (xs : List ℚ) : Bool :=
  decide (xs.length % 2 = 1 →
    benchmarkMedian xs = .ok ((sorted xs).getD (xs.length / 2) 0))

def evenCheck (xs : List ℚ) : Bool :=
  decide (xs.length % 2 = 0 → benchmarkMedian xs =
    .ok (((sorted xs).getD (xs.length / 2 - 1) 0 +
      (sorted xs).getD (xs.length / 2) 0) / 2))

def oddMemCheck (xs : List ℚ) : Bool :=
  if xs.length % 2 = 1 then
    match benchmarkMedian xs with | .ok x => decide (x ∈ xs) | .error _ => false
  else true

def singletonCheck (xs : List ℚ) : Bool :=
  match xs with
  | [x] => decide (benchmarkMedian xs = .ok x)
  | _ => true

def permutationCheck (xs : List ℚ) : Bool :=
  xs.permutations.all (fun ys => decide (benchmarkMedian xs = benchmarkMedian ys))

def endpoints : List ℚ := [-2, -3/2, -1/7, 0, 2/7, 5/2, 3]

def boundsCheck (xs : List ℚ) : Bool :=
  endpoints.all fun lo => endpoints.all fun hi =>
    if xs.all (fun x => decide (lo ≤ x ∧ x ≤ hi)) then
      match benchmarkMedian xs with
      | .ok m => decide (lo ≤ m ∧ m ≤ hi)
      | .error _ => true
    else true

def duplicationCheck (xs : List ℚ) : Bool :=
  decide (benchmarkMedian (duplicate xs) = benchmarkMedian xs)

def postCheck (xs : List ℚ) : Bool :=
  errorCheck xs && successCheck xs && oddCheck xs && evenCheck xs &&
  oddMemCheck xs && singletonCheck xs && permutationCheck xs &&
  boundsCheck xs && duplicationCheck xs

-- PBT for error_prop.
example : samples.all errorCheck = true := by native_decide
-- PBT for success_prop, on precisely admissible samples.
example : admissible.all successCheck = true := by native_decide
-- PBT for odd_prop.
example : samples.all oddCheck = true := by native_decide
-- PBT for even_prop, on precisely admissible samples.
example : admissible.all evenCheck = true := by native_decide
-- PBT for odd_mem_prop.
example : samples.all oddMemCheck = true := by native_decide
-- PBT for singleton_prop.
example : samples.all singletonCheck = true := by native_decide
-- PBT for permutation_prop.
example : samples.all permutationCheck = true := by native_decide
-- PBT for bounds_prop (also enumerating interval endpoints).
example : samples.all boundsCheck = true := by native_decide
-- PBT for duplication_prop.
example : samples.all duplicationCheck = true := by native_decide
-- PBT for Pre → Post_prop.
example : admissible.all postCheck = true := by native_decide
#eval (samples.length, admissible.length, admissible.all postCheck)

-- Additional randomized PBT; no rejection sampling or strengthened precondition.
#eval Plausible.Testable.check (∀ xs : List Int,
  benchmarkMedian (duplicate (xs.map (fun x => (x : ℚ)))) =
    benchmarkMedian (xs.map (fun x => (x : ℚ))))

-- Include every container case and systematically inject nonnumeric elements.
def inputSamples : List (Dynamic.Input ℚ) :=
  [.other] ++ samples.flatMap (fun xs =>
    [.list (xs.map some), .tuple (xs.map some),
     .list (none :: xs.map some), .tuple (none :: xs.map some)])

def validationCheck (input : Dynamic.Input ℚ) : Bool :=
  decide (Dynamic.benchmarkMedian input = .error .requiresNumbers ↔
    Dynamic.pre input = false)

def inputPostCheck (input : Dynamic.Input ℚ) : Bool :=
  validationCheck input && postCheck (Dynamic.numbers input) &&
    decide (Dynamic.benchmarkMedian input = benchmarkMedian (Dynamic.numbers input))

-- PBT for validation_prop, including invalid containers and elements.
example : inputSamples.all validationCheck = true := by native_decide
-- PBT for InputPre → InputPost_prop.
example : (inputSamples.filter Dynamic.pre).all inputPostCheck = true := by native_decide
#eval (inputSamples.length, inputSamples.all validationCheck)

end PBT

section Correctness
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Inhabited α]

/-- Kernel-checked correctness; PBTs are evidence and are not used in this proof. -/
theorem correctness_thm (xs : List α) : Pre xs → Post_prop xs := by
  intro h
  exact ⟨error_thm xs, success_thm xs h, odd_thm xs, even_thm xs h,
    odd_mem_thm xs, singleton_thm xs, permutation_thm xs, bounds_thm xs,
    duplication_thm xs⟩

theorem input_correctness_thm (input : Dynamic.Input α) :
    InputPre input → InputPost_prop input := by
  intro h
  refine ⟨validation_thm input, correctness_thm _ (input_numbers_pre input h), ?_⟩
  simp [Dynamic.benchmarkMedian, (input_pre_decides input).mpr h]

end Correctness

/-- Explicitly instantiate the full contract on arbitrary real observations. -/
theorem real_correctness_thm (xs : List ℝ) : Pre xs → Post_prop xs :=
  correctness_thm xs

/-! ## Mutable-state implementation -/

/-- Sorting followed by mutable length, index and result variables.
The comparator is explicit so this code also applies to primitive Float. -/
def medianImperativeWith {α : Type*} [Inhabited α] [Add α] [Div α] [OfNat α 2]
    (le : α → α → Bool) (input : List α) : Result α := Id.run do
  let mut data := input
  data := data.mergeSort le
  let mut n := 0
  n := data.length
  if n = 0 then
    return .error .noMedian
  let mut i := n / 2
  let mut answer := data.getD i default
  if n % 2 = 1 then
    return .ok answer
  i := i - 1
  answer := (data.getD i default + answer) / 2
  return .ok answer

def benchmarkMedianImperative {α : Type*} [LinearOrder α] [Inhabited α]
    [Add α] [Div α] [OfNat α 2] (data : List α) : Result α := Id.run do
  let mut result : Result α := .error .requiresNumbers
  if data.length ≠ 0 then
    result := medianImperativeWith (fun a b => decide (a ≤ b)) data
  return result

namespace FloatLayer

def benchmarkMedianImperative (data : List Float) : Result Float := Id.run do
  let mut result : Result Float := .error .requiresNumbers
  if data.length ≠ 0 then
    result := medianImperativeWith (fun a b => a ≤ b) data
  return result

end FloatLayer

def Dynamic.benchmarkMedianImperative {α : Type*} [LinearOrder α] [Inhabited α]
    [Add α] [Div α] [OfNat α 2] (input : Dynamic.Input α) : Result α := Id.run do
  let mut result : Result α := .error .requiresNumbers
  if Dynamic.pre input then
    result := StatisticsMedian.benchmarkMedianImperative (Dynamic.numbers input)
  return result

-- Imperative fixed tests and exhaustive cross-implementation checks.
example : benchmarkMedianImperative ([9, 1, 6, 2, 5, 4, 3] : List ℚ) = .ok 4 := by native_decide
example : benchmarkMedianImperative ([1, 2, 3, 4, 5, 6] : List ℚ) = .ok (7/2) := by native_decide
example : benchmarkMedianImperative ([1/7, 2/7, 3/7] : List ℚ) = .ok (2/7) := by native_decide
example : benchmarkMedianImperative ([25/10, 31/10, 42/10] : List ℚ) = .ok (31/10) := by native_decide
example : benchmarkMedianImperative ([42] : List ℚ) = .ok 42 := by native_decide
example : benchmarkMedianImperative ([] : List ℚ) = .error .requiresNumbers := by native_decide
example : (match FloatLayer.benchmarkMedianImperative [1.0, 3.0, 5.0, 7.0] with
    | .ok x => x == 4.0 | .error _ => false) = true := by native_decide
example : PBT.samples.all (fun xs =>
    decide (benchmarkMedian xs = benchmarkMedianImperative xs)) = true := by native_decide
#eval benchmarkMedianImperative ([3/2, 5/2, 39/4] : List ℚ)
#eval FloatLayer.benchmarkMedianImperative [9.0, 1.0, 6.0, 2.0, 5.0, 4.0, 3.0]

-- Bounded executable Float equivalence check. This checks operational agreement,
-- not exact-field laws for floating-point addition or division.
example : PBT.samples.all (fun xs =>
    let fs := xs.map Rat.toFloat
    match FloatLayer.benchmarkMedian fs, FloatLayer.benchmarkMedianImperative fs with
    | .ok x, .ok y => x == y
    | .error e, .error f => decide (e = f)
    | _, _ => false) = true := by native_decide

example : PBT.inputSamples.all (fun input =>
    decide (Dynamic.benchmarkMedian input = Dynamic.benchmarkMedianImperative input)) =
    true := by native_decide

/-- Structural equivalence needs no arithmetic laws and no order assumptions. -/
theorem middle_eq_imperativeWith {α : Type*} [Inhabited α] [Add α] [Div α] [OfNat α 2]
    (le : α → α → Bool) (xs : List α) :
    middle (xs.mergeSort le) = medianImperativeWith le xs := by
  simp [middle, medianImperativeWith]
  rfl

/-- Functional and imperative benchmark implementations agree on all inputs,
not only inputs satisfying the precondition. -/
theorem functional_eq_imperative_thm {α : Type*} [LinearOrder α] [Inhabited α]
    [Add α] [Div α] [OfNat α 2] (xs : List α) :
    benchmarkMedian xs = benchmarkMedianImperative xs := by
  by_cases h : xs.length = 0 <;>
    simp [benchmarkMedian, benchmarkMedianImperative, h, median, sorted,
      middle_eq_imperativeWith]

/-- Float equivalence also holds for nonfinite values: this is an operational,
not a field-arithmetic, statement and imposes no finiteness hypothesis. -/
theorem float_functional_eq_imperative_thm (xs : List Float) :
    FloatLayer.benchmarkMedian xs = FloatLayer.benchmarkMedianImperative xs := by
  by_cases h : xs.length = 0 <;>
    simp [FloatLayer.benchmarkMedian, FloatLayer.benchmarkMedianImperative,
      FloatLayer.median, h, middle_eq_imperativeWith]

theorem input_functional_eq_imperative_thm {α : Type*} [LinearOrder α] [Inhabited α]
    [Add α] [Div α] [OfNat α 2] (input : Dynamic.Input α) :
    Dynamic.benchmarkMedian input = Dynamic.benchmarkMedianImperative input := by
  by_cases h : Dynamic.pre input = true <;>
    simp [Dynamic.benchmarkMedian, Dynamic.benchmarkMedianImperative, h,
      functional_eq_imperative_thm]

end StatisticsMedian
end Agent
