import Mathlib

/-!
# Low median

A translation of `statistics.median_low` and its validating benchmark wrapper.
The mathematical implementation is polymorphic over a linearly ordered numeric
carrier: in particular the same definitions and proofs apply to `Int`, `Rat`,
and `Real`. No arithmetic is performed on the observations and even samples
return an observation, rather than an average. Executable tests use integers
and rationals, including negative and fractional observations and repetitions.

`Except StatisticsError` models the two source error messages. In the typed
entry point, `List α` represents either a Python list or a tuple of numbers;
`PythonInput` additionally represents the runtime container and numeric checks.
The ordering interface models the mathematical numeric intent of `sorted`.
Python's wider `numbers.Number` test also accepts complex values and NaNs,
for which Python sorting does not provide a mathematical linear order; no
linear-order or IEEE-754 correspondence for those values is asserted here.
-/

namespace StatisticsMedianLow

inductive StatisticsError where
  | noMedian
  | invalidInput
  deriving DecidableEq, Repr

deriving instance DecidableEq for Except

def StatisticsError.message : StatisticsError → String
  | .noMedian => "no median for empty data"
  | .invalidInput =>
      "benchmark_median_low requires a non-empty list/tuple of numbers"

/-- Convert a checked list access to the source function's result type. -/
def fromLookup {α : Type*} : Option α → Except StatisticsError α
  | some x => .ok x
  | none => .error .noMedian

/-- Zero-based position of the lower of the middle observations. -/
def lowIndex (n : Nat) : Nat := (n - 1) / 2

def sortedData {α : Type*} [LinearOrder α] (data : List α) : List α :=
  data.mergeSort (fun a b => decide (a ≤ b))

/-- Functional form; the parity branches are combined into `(n - 1) / 2`. -/
def median_low {α : Type*} [LinearOrder α] (data : List α) :
    Except StatisticsError α :=
  let sorted := sortedData data
  fromLookup sorted[lowIndex sorted.length]?

def benchmark_median_low {α : Type*} [LinearOrder α] (data : List α) :
    Except StatisticsError α :=
  if data.isEmpty then .error .invalidInput else median_low data

/-- `none` is a nonnumeric element; `other` is a non-list/tuple container. -/
inductive PythonInput (α : Type*) where
  | list (elements : List (Option α))
  | tuple (elements : List (Option α))
  | other
  deriving DecidableEq, Repr

def PythonInput.decode {α : Type*} : PythonInput α → Option (List α)
  | .list xs | .tuple xs => xs.mapM id
  | .other => none

def benchmark_input {α : Type*} [LinearOrder α] (input : PythonInput α) :
    Except StatisticsError α :=
  match input.decode with
  | some data => benchmark_median_low data
  | none => .error .invalidInput

-- Unit tests from the Python program.
example : benchmark_median_low ([1, 3, 5] : List Int) = .ok 3 := by native_decide
example : benchmark_median_low ([1, 2, 3, 4, 5, 6, 9] : List Int) = .ok 4 := by
  native_decide
example : benchmark_median_low ([1, 3, 5, 7] : List Int) = .ok 3 := by native_decide
example : benchmark_median_low ([1, 2, 3, 4, 5, 6] : List Int) = .ok 3 := by
  native_decide
example : benchmark_median_low ([42] : List Int) = .ok 42 := by native_decide
example : benchmark_median_low ([10, 20] : List Int) = .ok 10 := by native_decide
example : benchmark_median_low ([9, 1, 6, 2, 5, 4, 3] : List Int) = .ok 4 := by
  native_decide
example : benchmark_median_low ([-5, -1, 0, 3, 7] : List Int) = .ok 0 := by
  native_decide
example : benchmark_median_low ([-10, -5, 5, 10] : List Int) = .ok (-5) := by
  native_decide
example : benchmark_median_low ([] : List Int) = .error .invalidInput := by
  native_decide
example : median_low ([] : List Int) = .error .noMedian := by native_decide
example : benchmark_median_low ([3/2, -1/2, 1/3, 1/3] : List Rat) = .ok (1/3) := by
  native_decide
example : benchmark_input (.tuple [some (7 : Rat), some 2]) = .ok 2 := by
  native_decide
example : benchmark_input (.list [some (7 : Rat), none]) = .error .invalidInput := by
  native_decide
example : benchmark_input (.other : PythonInput Rat) = .error .invalidInput := by
  native_decide
#eval benchmark_median_low ([9, 1, 6, 2, 5, 4, 3] : List Int)
#eval benchmark_median_low ([] : List Rat)
#eval StatisticsError.invalidInput.message

/-- Container and element checks are supplied by the typed input representation. -/
def Pre {α : Type*} (data : List α) : Prop := data ≠ []

/-- The dynamic precondition: a list/tuple of numbers, with at least one element. -/
def InputPre {α : Type*} (input : PythonInput α) : Prop :=
  ∃ data, input.decode = some data ∧ Pre data

section Proofs
variable {α : Type*} [LinearOrder α]

@[simp] theorem sortedData_length (data : List α) :
    (sortedData data).length = data.length := List.length_mergeSort _

theorem sortedData_perm (data : List α) : (sortedData data).Perm data :=
  List.mergeSort_perm _ _

theorem sortedData_sorted (data : List α) : (sortedData data).Sorted (· ≤ ·) :=
  List.sorted_mergeSort' (· ≤ ·) data

theorem lowIndex_lt {n : Nat} (hn : 0 < n) : lowIndex n < n := by
  unfold lowIndex
  omega

theorem lowIndex_odd {n : Nat} (hn : n % 2 = 1) : lowIndex n = n / 2 := by
  unfold lowIndex
  omega

theorem lowIndex_even {n : Nat} (hn : n % 2 = 0) : lowIndex n = n / 2 - 1 := by
  unfold lowIndex
  omega

theorem benchmark_eq_median {data : List α} (h : Pre data) :
    benchmark_median_low data = median_low data := by
  have hn : data ≠ [] := h
  simp [benchmark_median_low, hn]

theorem benchmark_eq_lookup {data : List α} (h : Pre data) :
    benchmark_median_low data = fromLookup (sortedData data)[lowIndex data.length]? := by
  rw [benchmark_eq_median h]
  simp [median_low]

/-- The exact order statistic, expressed using a safe zero-based lookup. -/
def selection_prop (data : List α) (result : Except StatisticsError α) : Prop :=
  ∃ m, result = .ok m ∧ (sortedData data)[lowIndex data.length]? = some m

theorem selection_thm {data : List α} (h : Pre data) :
    selection_prop data (benchmark_median_low data) := by
  have hn : 0 < data.length := List.length_pos_iff.mpr h
  have hk : lowIndex data.length < (sortedData data).length := by
    simpa using lowIndex_lt hn
  refine ⟨(sortedData data)[lowIndex data.length], ?_, List.getElem?_eq_getElem hk⟩
  rw [benchmark_eq_lookup h, List.getElem?_eq_getElem hk]
  rfl

/-- The returned value is one of the original observations (multiplicities allowed). -/
def membership_prop (data : List α) (result : Except StatisticsError α) : Prop :=
  ∀ m, result = .ok m → m ∈ data

theorem membership_thm {data : List α} (h : Pre data) :
    membership_prop data (benchmark_median_low data) := by
  obtain ⟨m, hm, hget⟩ := selection_thm h
  intro x hx
  have : m = x := Except.ok.inj (hm.symm.trans hx)
  subst x
  exact (sortedData_perm data).mem_iff.mp (List.mem_of_getElem? hget)

/-- On odd samples the middle position is `n / 2`. -/
def odd_prop (data : List α) (result : Except StatisticsError α) : Prop :=
  data.length % 2 = 1 → result = fromLookup (sortedData data)[data.length / 2]?

theorem odd_thm {data : List α} (h : Pre data) :
    odd_prop data (benchmark_median_low data) := by
  intro hn
  rw [benchmark_eq_lookup h, lowIndex_odd hn]

/-- On even nonempty samples the selected position is `n / 2 - 1`. -/
def even_prop (data : List α) (result : Except StatisticsError α) : Prop :=
  data.length % 2 = 0 → result = fromLookup (sortedData data)[data.length / 2 - 1]?

theorem even_thm {data : List α} (h : Pre data) :
    even_prop data (benchmark_median_low data) := by
  intro hn
  rw [benchmark_eq_lookup h, lowIndex_even hn]

/-- An implementation-independent partition specification of the low median. -/
def partition_prop (data : List α) (result : Except StatisticsError α) : Prop :=
  ∃ m lower upper, result = .ok m ∧ data.Perm (lower ++ m :: upper) ∧
    lower.length = lowIndex data.length ∧
    (∀ x ∈ lower, x ≤ m) ∧ (∀ x ∈ upper, m ≤ x)

theorem partition_thm {data : List α} (h : Pre data) :
    partition_prop data (benchmark_median_low data) := by
  obtain ⟨m, hm, hget⟩ := selection_thm h
  obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hget
  let s := sortedData data
  let k := lowIndex data.length
  have hs : s.Sorted (· ≤ ·) := sortedData_sorted data
  have hdecomp : s.take k ++ m :: s.drop (k + 1) = s := by
    rw [← heq, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
  refine ⟨m, s.take k, s.drop (k + 1), hm, ?_, ?_, ?_, ?_⟩
  · rw [hdecomp]
    exact (sortedData_perm data).symm
  · simp only [List.length_take]
    exact Nat.min_eq_left (Nat.le_of_lt hk)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_take, ← heq]
    apply hs.rel_get_of_le
    simp only [List.length_take] at hi
    exact Nat.le_of_lt (Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _))
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_drop, ← heq]
    apply hs.rel_get_of_le
    change k ≤ k + 1 + i
    omega

/-- Rank inequalities distinguish the *low* median, even with duplicate values. -/
def rank_prop (data : List α) (result : Except StatisticsError α) : Prop :=
  ∀ m, result = .ok m →
    data.countP (fun x => decide (x < m)) ≤ lowIndex data.length ∧
    lowIndex data.length < data.countP (fun x => decide (x ≤ m))

theorem rank_thm {data : List α} (h : Pre data) :
    rank_prop data (benchmark_median_low data) := by
  obtain ⟨m, lower, upper, hm, hp, hlen, hlo, hup⟩ := partition_thm h
  intro x hx
  have heq : m = x := Except.ok.inj (hm.symm.trans hx)
  subst x
  have hu : upper.countP (fun x => decide (x < m)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro x hx
    simpa using not_lt_of_ge (hup x hx)
  have hl : lower.countP (fun x => decide (x ≤ m)) = lower.length := by
    apply List.countP_eq_length.mpr
    intro x hx
    simpa using hlo x hx
  rw [hp.countP_eq (fun x => decide (x < m)),
    hp.countP_eq (fun x => decide (x ≤ m))]
  simp only [List.countP_append, List.countP_cons, lt_self_iff_false,
    decide_false, Bool.false_eq_true, ↓reduceIte, le_refl, decide_true,
    hu, hl, Nat.add_zero]
  constructor
  · rw [← hlen]
    exact List.countP_le_length
  · omega

/-- Reordering the input cannot change the result. -/
def permutation_prop (data other : List α) : Prop :=
  data.Perm other → benchmark_median_low data = benchmark_median_low other

theorem permutation_thm (data other : List α) : permutation_prop data other := by
  intro hp
  have hs : sortedData data = sortedData other :=
    List.eq_of_perm_of_sorted
      ((sortedData_perm data).trans (hp.trans (sortedData_perm other).symm))
      (sortedData_sorted data) (sortedData_sorted other)
  have he : data.isEmpty = other.isEmpty := by
    have := hp.length_eq
    cases data <;> cases other <;> simp_all
  simp [benchmark_median_low, he, median_low, hs]

/-- The validating wrapper raises its error exactly on empty typed input. -/
def error_prop (data : List α) : Prop :=
  (benchmark_median_low data = .error .invalidInput ↔ data = []) ∧
  (median_low ([] : List α) = .error .noMedian)

theorem error_thm (data : List α) : error_prop data := by
  refine ⟨?_, by simp [median_low, sortedData, lowIndex, fromLookup]⟩
  by_cases h : data = []
  · simp [h, benchmark_median_low]
  · obtain ⟨m, hm, _⟩ := selection_thm h
    simp [hm, h]

/-- The dynamic wrapper rejects precisely inputs failing its runtime precondition. -/
def validation_prop (input : PythonInput α) : Prop :=
  benchmark_input input = .error .invalidInput ↔ ¬ InputPre input

theorem validation_thm (input : PythonInput α) : validation_prop input := by
  unfold validation_prop benchmark_input InputPre
  cases hd : input.decode with
  | none => simp
  | some data =>
    simp only [Option.some.injEq, exists_eq_left', Pre, not_not]
    exact (error_thm data).1

/-- Full successful-result contract, including a sorting-independent rank condition. -/
def Post_prop (data : List α) (result : Except StatisticsError α) : Prop :=
  selection_prop data result ∧ membership_prop data result ∧
  odd_prop data result ∧ even_prop data result ∧
  partition_prop data result ∧ rank_prop data result

end Proofs

/-!
Property-based tests. Every `_prop` above has its own executable check below;
the postcondition checks their conjunction. The generic theorems also apply to
`Real`, whose comparisons are noncomputable. These PBTs exercise the executable
`Rat`/`Int` instances of the same definitions; they do not execute Real comparisons.
-/

section PropertyTests

variable {α : Type*} [LinearOrder α]

def selectionCheck (data : List α) : Bool :=
  match benchmark_median_low data with
  | .ok m => decide ((sortedData data)[lowIndex data.length]? = some m)
  | .error _ => false

def membershipCheck (data : List α) : Bool :=
  match benchmark_median_low data with
  | .ok m => decide (m ∈ data)
  | .error _ => true

def oddCheck (data : List α) : Bool :=
  data.length % 2 != 1 ||
    decide (benchmark_median_low data = fromLookup (sortedData data)[data.length / 2]?)

def evenCheck (data : List α) : Bool :=
  data.length % 2 != 0 ||
    decide (benchmark_median_low data = fromLookup (sortedData data)[data.length / 2 - 1]?)

/-- Exhibit and check the witnesses of `partition_prop`, including multiplicity. -/
def partitionCheck (data : List α) : Bool :=
  match benchmark_median_low data with
  | .error _ => false
  | .ok m =>
    let k := lowIndex data.length
    let sorted := sortedData data
    let lower := sorted.take k
    let upper := sorted.drop (k + 1)
    decide (data.Perm (lower ++ m :: upper)) &&
      decide (lower.length = k) &&
      lower.all (fun x => decide (x ≤ m)) && upper.all (fun x => decide (m ≤ x))

def rankCheck (data : List α) : Bool :=
  match benchmark_median_low data with
  | .error _ => true
  | .ok m =>
    decide (data.countP (fun x => decide (x < m)) ≤ lowIndex data.length) &&
    decide (lowIndex data.length < data.countP (fun x => decide (x ≤ m)))

def permutationCheck (data other : List α) : Bool :=
  !decide (data.Perm other) ||
    decide (benchmark_median_low data = benchmark_median_low other)

def errorCheck (data : List α) : Bool :=
  decide ((benchmark_median_low data = .error .invalidInput ↔ data = []) ∧
    median_low ([] : List α) = .error .noMedian)

/-- Direct execution of the Python precondition on the tagged input. -/
def inputPreCheck (input : PythonInput α) : Bool :=
  match input with
  | .list xs | .tuple xs => !xs.isEmpty && xs.all Option.isSome
  | .other => false

def validationCheck (input : PythonInput α) : Bool :=
  decide (benchmark_input input = .error .invalidInput) == !inputPreCheck input

def postCheck (data : List α) : Bool :=
  selectionCheck data && membershipCheck data && oddCheck data && evenCheck data &&
    partitionCheck data && rankCheck data

/-- All lists of length at most `n` over an alphabet: exhaustive, including repeats. -/
def listsUpTo {β : Type*} (alphabet : List β) : Nat → List (List β)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun x => (listsUpTo alphabet n).map (x :: ·))

/-- 19,531 cases, with both parities, ties, negatives, and exact fractions. -/
def samples : List (List Rat) := listsUpTo [-2, -1/2, 0, 1/2, 2] 6

example : samples.length = 19531 := by native_decide

-- PBT for selection_prop.
example : samples.all (fun xs => xs.isEmpty || selectionCheck xs) = true := by
  native_decide
-- PBT for membership_prop.
example : samples.all (fun xs => xs.isEmpty || membershipCheck xs) = true := by
  native_decide
-- PBT for odd_prop.
example : samples.all (fun xs => xs.isEmpty || oddCheck xs) = true := by
  native_decide
-- PBT for even_prop (the theorem assumes nonempty input).
example : samples.all (fun xs => xs.isEmpty || evenCheck xs) = true := by
  native_decide
-- PBT for partition_prop.
example : samples.all (fun xs => xs.isEmpty || partitionCheck xs) = true := by
  native_decide
-- PBT for rank_prop.
example : samples.all (fun xs => xs.isEmpty || rankCheck xs) = true := by
  native_decide
-- PBT for permutation_prop: reversal, rotation, and an independent insertion sort.
example : samples.all (fun xs =>
    permutationCheck xs xs.reverse && permutationCheck xs (xs.rotate 1) &&
    permutationCheck xs (xs.insertionSort (· ≤ ·))) = true := by native_decide
-- PBT for error_prop, including the inadmissible empty list.
example : samples.all errorCheck = true := by native_decide
-- PBT for validation_prop: 1,563 tagged cases, including invalid numeric elements.
example : (PythonInput.other ::
    (listsUpTo [none, some (-1 : Rat), some 0, some (1/2), some 2] 4).flatMap
      (fun xs => [PythonInput.list xs, PythonInput.tuple xs])).all validationCheck = true := by
  native_decide
-- PBT for Post_prop.
example : samples.all (fun xs => xs.isEmpty || postCheck xs) = true := by
  native_decide

-- Random lists supplement the exhaustive rational domain with larger integer values.
-- Every generated tail is made admissible by a head, so there are no discarded cases.
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  postCheck (x :: xs) = true) (cfg := { numInst := 200 })
#eval Plausible.Testable.check (∀ xs : List Int,
  permutationCheck xs xs.reverse = true ∧ errorCheck xs = true)

end PropertyTests

/-- Successful execution satisfies all six semantic properties. -/
theorem correctness {α : Type*} [LinearOrder α] (data : List α) :
    Pre data → Post_prop data (benchmark_median_low data) := by
  intro h
  exact ⟨selection_thm h, membership_thm h, odd_thm h, even_thm h,
    partition_thm h, rank_thm h⟩

/-- The checked dynamic entry point has exactly the same successful contract. -/
theorem input_correctness {α : Type*} [LinearOrder α] (input : PythonInput α) :
    InputPre input → ∃ data, input.decode = some data ∧
      Post_prop data (benchmark_input input) := by
  rintro ⟨data, hd, h⟩
  refine ⟨data, hd, ?_⟩
  simpa [benchmark_input, hd] using correctness data h

/-- Imperative translation retaining the source's mutable data and parity branch. -/
def median_low_imperative {α : Type*} [LinearOrder α] (data : List α) :
    Except StatisticsError α := Id.run do
  let mut values := data
  values := sortedData values
  let n := values.length
  if n = 0 then
    return .error .noMedian
  let mut index := n / 2
  if n % 2 ≠ 1 then
    index := index - 1
  return fromLookup values[index]?

def benchmark_median_low_imperative {α : Type*} [LinearOrder α] (data : List α) :
    Except StatisticsError α := Id.run do
  let mut result := Except.error StatisticsError.invalidInput
  if !data.isEmpty then
    result := median_low_imperative data
  return result

def benchmark_input_imperative {α : Type*} [LinearOrder α] (input : PythonInput α) :
    Except StatisticsError α := Id.run do
  match input.decode with
  | none => return .error .invalidInput
  | some data => return benchmark_median_low_imperative data

-- Imperative unit tests repeat the source's success and error cases.
example : benchmark_median_low_imperative ([1, 3, 5] : List Int) = .ok 3 := by
  native_decide
example : benchmark_median_low_imperative ([1, 2, 3, 4, 5, 6, 9] : List Int) = .ok 4 := by
  native_decide
example : benchmark_median_low_imperative ([1, 3, 5, 7] : List Int) = .ok 3 := by
  native_decide
example : benchmark_median_low_imperative ([1, 2, 3, 4, 5, 6] : List Int) = .ok 3 := by
  native_decide
example : benchmark_median_low_imperative ([42] : List Int) = .ok 42 := by
  native_decide
example : benchmark_median_low_imperative ([10, 20] : List Int) = .ok 10 := by
  native_decide
example : benchmark_median_low_imperative ([9, 1, 6, 2, 5, 4, 3] : List Int) = .ok 4 := by
  native_decide
example : benchmark_median_low_imperative ([-5, -1, 0, 3, 7] : List Int) = .ok 0 := by
  native_decide
example : benchmark_median_low_imperative ([-10, -5, 5, 10] : List Int) = .ok (-5) := by
  native_decide
example : benchmark_median_low_imperative ([] : List Int) = .error .invalidInput := by
  native_decide
example : median_low_imperative ([] : List Int) = .error .noMedian := by native_decide
example : benchmark_input_imperative (.tuple [some (7 : Rat), some 2]) = .ok 2 := by
  native_decide
example : benchmark_input_imperative (.list [some (7 : Rat), none]) = .error .invalidInput := by
  native_decide
#eval benchmark_median_low_imperative ([3/2, -1/2, 1/3, 1/3] : List Rat)
#eval benchmark_median_low_imperative ([] : List Int)

-- Exhaustive and randomized equivalence checks also exercise the empty-input paths.
example : samples.all (fun xs =>
    decide (median_low xs = median_low_imperative xs) &&
    decide (benchmark_median_low xs = benchmark_median_low_imperative xs)) = true := by
  native_decide
#eval Plausible.Testable.check (∀ xs : List Int,
  benchmark_median_low xs = benchmark_median_low_imperative xs)

/-- The index normalization agrees with both original parity branches, on all inputs. -/
theorem median_low_equivalence {α : Type*} [LinearOrder α] (data : List α) :
    median_low data = median_low_imperative data := by
  by_cases he : data = []
  · subst data
    simp [median_low, median_low_imperative, sortedData, lowIndex, fromLookup]
  · have hn : data.length ≠ 0 := Nat.ne_of_gt (List.length_pos_iff.mpr he)
    by_cases ho : data.length % 2 = 1
    · simp [median_low, median_low_imperative, hn, ho, lowIndex_odd ho]
    · have hev : data.length % 2 = 0 := by omega
      simp [median_low, median_low_imperative, hn, ho, lowIndex_even hev]

/-- Functional and imperative wrappers agree even when the precondition fails. -/
theorem equivalence {α : Type*} [LinearOrder α] (data : List α) :
    benchmark_median_low data = benchmark_median_low_imperative data := by
  by_cases h : data = [] <;>
    simp [benchmark_median_low, benchmark_median_low_imperative, h, median_low_equivalence]

/-- Equivalence also preserves rejected containers and nonnumeric elements. -/
theorem input_equivalence {α : Type*} [LinearOrder α] (input : PythonInput α) :
    benchmark_input input = benchmark_input_imperative input := by
  cases hd : input.decode <;>
    simp [benchmark_input, benchmark_input_imperative, hd, equivalence]

end StatisticsMedianLow
