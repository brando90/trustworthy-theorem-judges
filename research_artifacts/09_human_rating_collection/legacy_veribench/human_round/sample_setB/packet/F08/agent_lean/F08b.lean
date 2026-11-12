import Mathlib

/-!
# Low median

A translation of `statistics.median_low` and its checked wrapper. The only
numeric operation is comparison, so the mathematical implementation is
polymorphic over a linearly ordered type. In particular it applies to `ℚ`
and `ℝ`, rather than restricting the specification to integral inputs.
The executable examples use exact rationals. Lists represent the contents
of either a Python list or tuple; their numeric element type is static.
`Except` represents the two `StatisticsError` paths.

This is the mathematical ordered-number model: it does not assert an
IEEE-754/NaN correspondence or an ordering for Python complex numbers.
-/

namespace StatisticsMedianLow

deriving instance DecidableEq for Except

inductive StatisticsError where
  | noMedian
  | invalidInput
  deriving Repr, DecidableEq

def StatisticsError.message : StatisticsError → String
  | .noMedian => "no median for empty data"
  | .invalidInput => "benchmark_median_low requires a non-empty list/tuple of numbers"

variable {α : Type*} [LinearOrder α]

def sortedData (data : List α) : List α :=
  data.mergeSort (fun a b => decide (a ≤ b))

def lowIndex (n : Nat) : Nat :=
  if n % 2 = 1 then n / 2 else n / 2 - 1

def readMedian (data : List α) (i : Nat) : Except StatisticsError α :=
  match data[i]? with
  | some x => .ok x
  | none => .error .noMedian

def medianLow (data : List α) : Except StatisticsError α :=
  let data := sortedData data
  let n := data.length
  if n = 0 then .error .noMedian else readMedian data (lowIndex n)

def benchmarkMedianLow (data : List α) : Except StatisticsError α :=
  if data.length = 0 then .error .invalidInput else medianLow data

-- All examples from the Python test suite, including its exception case.
example : benchmarkMedianLow ([1, 3, 5] : List ℚ) = .ok 3 := by native_decide
example : benchmarkMedianLow ([1, 2, 3, 4, 5, 6, 9] : List ℚ) = .ok 4 := by native_decide
example : benchmarkMedianLow ([1, 3, 5, 7] : List ℚ) = .ok 3 := by native_decide
example : benchmarkMedianLow ([1, 2, 3, 4, 5, 6] : List ℚ) = .ok 3 := by native_decide
example : benchmarkMedianLow ([42] : List ℚ) = .ok 42 := by native_decide
example : benchmarkMedianLow ([10, 20] : List ℚ) = .ok 10 := by native_decide
example : benchmarkMedianLow ([9, 1, 6, 2, 5, 4, 3] : List ℚ) = .ok 4 := by native_decide
example : benchmarkMedianLow ([-5, -1, 0, 3, 7] : List ℚ) = .ok 0 := by native_decide
example : benchmarkMedianLow ([-10, -5, 5, 10] : List ℚ) = .ok (-5) := by native_decide
example : benchmarkMedianLow ([] : List ℚ) = .error .invalidInput := by native_decide
example : medianLow ([] : List ℚ) = .error .noMedian := by native_decide
example : benchmarkMedianLow ([3/2, -1/2, 2/3, 2/3] : List ℚ) = .ok (2/3) := by native_decide
#eval benchmarkMedianLow ([9, 1, 6, 2, 5, 4, 3] : List ℚ)
#eval benchmarkMedianLow ([] : List ℚ)

def Pre (data : List α) : Prop := 0 < data.length

-- Sorting and index facts used by all the mathematical proofs.
@[simp] theorem sortedData_length (data : List α) :
    (sortedData data).length = data.length := List.length_mergeSort data

theorem sortedData_perm (data : List α) : (sortedData data).Perm data :=
  List.mergeSort_perm _ _

theorem sortedData_sorted (data : List α) : (sortedData data).Sorted (· ≤ ·) :=
  List.sorted_mergeSort' (· ≤ ·) data

theorem lowIndex_eq (n : Nat) : lowIndex n = (n - 1) / 2 := by
  unfold lowIndex
  split <;> omega

theorem medianIndex_lt (data : List α) (h : Pre data) :
    (data.length - 1) / 2 < (sortedData data).length := by
  rw [sortedData_length]
  unfold Pre at h
  omega

theorem medianLow_nonempty (data : List α) (h : Pre data) :
    medianLow data = .ok ((sortedData data)[(data.length - 1) / 2]'(medianIndex_lt data h)) := by
  have hn : data.length ≠ 0 := Nat.ne_of_gt h
  simp [medianLow, hn, lowIndex_eq, readMedian,
    List.getElem?_eq_getElem (medianIndex_lt data h)]

theorem benchmark_nonempty (data : List α) (h : Pre data) :
    benchmarkMedianLow data =
      .ok ((sortedData data)[(data.length - 1) / 2]'(medianIndex_lt data h)) := by
  have hn : data.length ≠ 0 := Nat.ne_of_gt h
  simp [benchmarkMedianLow, hn, medianLow_nonempty data h]

/-- Exact zero-based lower-middle index, not an average of two values. -/
def selection_prop (data : List α) : Prop :=
  benchmarkMedianLow data = readMedian (sortedData data) ((data.length - 1) / 2)

theorem selection_thm (data : List α) (h : Pre data) : selection_prop data := by
  have hn : data.length ≠ 0 := Nat.ne_of_gt h
  simp [selection_prop, benchmarkMedianLow, medianLow, hn, lowIndex_eq]

def odd_prop (data : List α) : Prop :=
  data.length % 2 = 1 →
    benchmarkMedianLow data = readMedian (sortedData data) (data.length / 2)

theorem odd_thm (data : List α) (h : Pre data) : odd_prop data := by
  intro ho
  have hi : (data.length - 1) / 2 = data.length / 2 := by omega
  simpa [selection_prop, hi] using selection_thm data h

def even_prop (data : List α) : Prop :=
  data.length % 2 = 0 →
    benchmarkMedianLow data = readMedian (sortedData data) (data.length / 2 - 1)

theorem even_thm (data : List α) (h : Pre data) : even_prop data := by
  intro he
  have hi : (data.length - 1) / 2 = data.length / 2 - 1 := by omega
  simpa [selection_prop, hi] using selection_thm data h

/-- A successful median is an original observation, including with duplicates. -/
def membership_prop (data : List α) : Prop :=
  ∀ m, benchmarkMedianLow data = .ok m → m ∈ data

theorem membership_thm (data : List α) : membership_prop data := by
  intro m hm
  by_cases h : Pre data
  · rw [benchmark_nonempty data h] at hm
    have he := Except.ok.inj hm
    rw [← he]
    exact (sortedData_perm data).mem_iff.mp (List.getElem_mem (medianIndex_lt data h))
  · have hn : data.length = 0 := by unfold Pre at h; omega
    simp [benchmarkMedianLow, hn] at hm

/-- The low median has exactly the lower-middle rank, with inequalities
allowing repeated observations on either side. -/
def orderStatistic_prop (data : List α) : Prop :=
  ∃ (lo : List α) (m : α) (hi : List α),
    benchmarkMedianLow data = .ok m ∧
    data.Perm (lo ++ m :: hi) ∧
    lo.length = (data.length - 1) / 2 ∧
    hi.length = data.length / 2 ∧
    (∀ x ∈ lo, x ≤ m) ∧ (∀ x ∈ hi, m ≤ x)

theorem orderStatistic_thm (data : List α) (h : Pre data) :
    orderStatistic_prop data := by
  let s := sortedData data
  let k := (data.length - 1) / 2
  have hk : k < s.length := medianIndex_lt data h
  let m := s[k]
  have hs : s.take k ++ m :: s.drop (k + 1) = s := by
    dsimp [m]
    rw [← List.drop_eq_getElem_cons hk]
    exact List.take_append_drop k s
  have hp : List.Pairwise (· ≤ ·) (s.take k ++ m :: s.drop (k + 1)) := by
    rw [hs]
    exact sortedData_sorted data
  have parts := List.pairwise_append.mp hp
  refine ⟨s.take k, m, s.drop (k + 1), benchmark_nonempty data h, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]
    exact (sortedData_perm data).symm
  · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    rfl
  · simp only [List.length_drop]
    dsimp [s, k]
    rw [sortedData_length]
    unfold Pre at h
    omega
  · intro x hx
    exact parts.2.2 x hx m (by simp)
  · exact (List.pairwise_cons.mp parts.2.1).1

/-- Both error paths occur exactly on empty input. -/
def errors_prop (data : List α) : Prop :=
  (medianLow data = .error .noMedian ↔ data = []) ∧
  (benchmarkMedianLow data = .error .invalidInput ↔ data = [])

theorem errors_thm (data : List α) : errors_prop data := by
  by_cases h : Pre data
  · have he : data ≠ [] := by
      intro he
      subst data
      simp [Pre] at h
    simp [errors_prop, medianLow_nonempty data h, benchmark_nonempty data h, he]
  · have hn : data.length = 0 := by unfold Pre at h; omega
    have he : data = [] := List.length_eq_zero_iff.mp hn
    subst data
    simp [errors_prop, medianLow, benchmarkMedianLow]

/-- Permuting the input does not change the result (also for empty input). -/
def permutation_prop (data other : List α) : Prop :=
  data.Perm other → benchmarkMedianLow data = benchmarkMedianLow other

theorem permutation_thm (data other : List α) : permutation_prop data other := by
  intro hp
  have hs : sortedData data = sortedData other :=
    List.eq_of_perm_of_sorted
      ((sortedData_perm data).trans (hp.trans (sortedData_perm other).symm))
      (sortedData_sorted data) (sortedData_sorted other)
  simp [benchmarkMedianLow, medianLow, hp.length_eq, hs]

/-- On sorted input no reordering is necessary. -/
def sortedInput_prop (data : List α) : Prop :=
  data.Sorted (· ≤ ·) → benchmarkMedianLow data = readMedian data ((data.length - 1) / 2)

theorem sortedInput_thm (data : List α) (h : Pre data) : sortedInput_prop data := by
  intro hs
  have he : sortedData data = data := List.mergeSort_eq_self (· ≤ ·) hs
  simpa [selection_prop, he] using selection_thm data h

/-- The successful wrapper's full contract. Errors and permutation invariance
are also proved unconditionally in their separate theorems. -/
def Post_prop (data : List α) : Prop :=
  selection_prop data ∧ odd_prop data ∧ even_prop data ∧
  membership_prop data ∧ orderStatistic_prop data ∧ errors_prop data ∧
  sortedInput_prop data

/-! ## Property-based tests

The proofs above quantify over every linearly ordered type, including `ℝ`.
Real comparisons cannot be evaluated. The following exact-rational checks
are executable counterparts of each property and of the whole postcondition;
they do not narrow any theorem's domain. The existential rank property is
checked using the same explicit take/drop witnesses constructed in its proof.
-/

private def alphabet : List ℚ := [-2, -1/2, 0, 2/3, 3]

private def listsOfLength : Nat → List (List ℚ)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun a => (listsOfLength n).map (a :: ·)

-- All 3906 lists of lengths 0 through 5 over the rational alphabet.
private def smallInputs : List (List ℚ) :=
  (List.range 6).flatMap listsOfLength

private def selectionCheck (xs : List ℚ) : Bool :=
  decide (benchmarkMedianLow xs = readMedian (sortedData xs) ((xs.length - 1) / 2))

private def oddCheck (xs : List ℚ) : Bool :=
  decide (xs.length % 2 = 1 →
    benchmarkMedianLow xs = readMedian (sortedData xs) (xs.length / 2))

private def evenCheck (xs : List ℚ) : Bool :=
  decide (xs.length % 2 = 0 →
    benchmarkMedianLow xs = readMedian (sortedData xs) (xs.length / 2 - 1))

private def membershipCheck (xs : List ℚ) : Bool :=
  match benchmarkMedianLow xs with
  | .error _ => true
  | .ok m => decide (m ∈ xs)

private def orderStatisticCheck (xs : List ℚ) : Bool :=
  match benchmarkMedianLow xs with
  | .error _ => false
  | .ok m =>
    let k := (xs.length - 1) / 2
    let lo := (sortedData xs).take k
    let hi := (sortedData xs).drop (k + 1)
    decide (xs.Perm (lo ++ m :: hi)) &&
      decide (lo.length = k ∧ hi.length = xs.length / 2) &&
      lo.all (fun x => decide (x ≤ m)) && hi.all (fun x => decide (m ≤ x))

private def errorsCheck (xs : List ℚ) : Bool :=
  decide ((medianLow xs = .error .noMedian ↔ xs = []) ∧
    (benchmarkMedianLow xs = .error .invalidInput ↔ xs = []))

private def sortedInputCheck (xs : List ℚ) : Bool :=
  decide (xs.Sorted (· ≤ ·) →
    benchmarkMedianLow xs = readMedian xs ((xs.length - 1) / 2))

private def postCheck (xs : List ℚ) : Bool :=
  selectionCheck xs && oddCheck xs && evenCheck xs && membershipCheck xs &&
    orderStatisticCheck xs && errorsCheck xs && sortedInputCheck xs

-- PBT for selection_prop.
example : smallInputs.all (fun xs => xs.isEmpty || selectionCheck xs) = true := by native_decide
-- PBT for odd_prop.
example : smallInputs.all (fun xs => xs.isEmpty || oddCheck xs) = true := by native_decide
-- PBT for even_prop, excluding the inadmissible empty input.
example : smallInputs.all (fun xs => xs.isEmpty || evenCheck xs) = true := by native_decide
-- PBT for membership_prop, including the vacuous unsuccessful case.
example : smallInputs.all membershipCheck = true := by native_decide
-- PBT for orderStatistic_prop: explicitly verify its witnesses.
example : smallInputs.all (fun xs => xs.isEmpty || orderStatisticCheck xs) = true := by native_decide
-- PBT for errors_prop, including empty input for both entry points.
example : smallInputs.all errorsCheck = true := by native_decide
-- PBT for sortedInput_prop.
example : smallInputs.all (fun xs => xs.isEmpty || sortedInputCheck xs) = true := by native_decide
-- Also exercise only sorted admissible inputs, without a sparse antecedent.
example : smallInputs.all (fun xs => xs.isEmpty || sortedInputCheck (sortedData xs)) = true := by
  native_decide
-- PBT for permutation_prop: all permutations of all lists of lengths 0..4.
example : ((List.range 5).flatMap listsOfLength).all
    (fun xs => xs.permutations.all
      (fun ys => decide (benchmarkMedianLow xs = benchmarkMedianLow ys))) = true := by
  native_decide
-- PBT for the entire Post_prop.
example : smallInputs.all (fun xs => xs.isEmpty || postCheck xs) = true := by native_decide
#eval (smallInputs.length, smallInputs.all (fun xs => xs.isEmpty || postCheck xs))

/-- Total correctness of the checked wrapper on its precondition. -/
theorem correctness_thm (data : List α) : Pre data → Post_prop data := by
  intro h
  exact ⟨selection_thm data h, odd_thm data h, even_thm data h,
    membership_thm data, orderStatistic_thm data h, errors_thm data,
    sortedInput_thm data h⟩

/-! ## Imperative implementation

The mutable variable initially holds the input, is replaced by its sorted
copy, and the mutable index is decremented precisely in the even branch.
The functional selector `lowIndex` is not used in this implementation.
-/

def medianLowImperative (input : List α) : Except StatisticsError α := Id.run do
  let mut data := input
  data := sortedData data
  let n := data.length
  if n = 0 then
    return .error .noMedian
  let mut i := n / 2
  if n % 2 ≠ 1 then
    i := i - 1
  match data[i]? with
  | some m => return .ok m
  | none => return .error .noMedian

def benchmarkMedianLowImperative (input : List α) : Except StatisticsError α := Id.run do
  if input.length = 0 then
    return .error .invalidInput
  return medianLowImperative input

-- Imperative regression tests: odd, even, singleton, negatives, fractions,
-- duplicate values, and both empty-input exception paths.
example : benchmarkMedianLowImperative ([1, 3, 5] : List ℚ) = .ok 3 := by native_decide
example : benchmarkMedianLowImperative ([1, 2, 3, 4, 5, 6, 9] : List ℚ) = .ok 4 := by native_decide
example : benchmarkMedianLowImperative ([1, 3, 5, 7] : List ℚ) = .ok 3 := by native_decide
example : benchmarkMedianLowImperative ([1, 2, 3, 4, 5, 6] : List ℚ) = .ok 3 := by native_decide
example : benchmarkMedianLowImperative ([42] : List ℚ) = .ok 42 := by native_decide
example : benchmarkMedianLowImperative ([10, 20] : List ℚ) = .ok 10 := by native_decide
example : benchmarkMedianLowImperative ([9, 1, 6, 2, 5, 4, 3] : List ℚ) = .ok 4 := by native_decide
example : benchmarkMedianLowImperative ([-5, -1, 0, 3, 7] : List ℚ) = .ok 0 := by native_decide
example : benchmarkMedianLowImperative ([-10, -5, 5, 10] : List ℚ) = .ok (-5) := by native_decide
example : benchmarkMedianLowImperative ([3/2, -1/2, 2/3, 2/3] : List ℚ) = .ok (2/3) := by native_decide
example : benchmarkMedianLowImperative ([] : List ℚ) = .error .invalidInput := by native_decide
example : medianLowImperative ([] : List ℚ) = .error .noMedian := by native_decide
#eval benchmarkMedianLowImperative ([-10, -5, 5, 10] : List ℚ)
example : smallInputs.all (fun xs =>
    decide (benchmarkMedianLow xs = benchmarkMedianLowImperative xs)) = true := by native_decide

/-- Unconditional equivalence, including the core's empty-input error. -/
theorem medianLow_equivalence_thm (data : List α) :
    medianLow data = medianLowImperative data := by
  unfold medianLow medianLowImperative
  dsimp only [Id.run, Bind.bind, Pure.pure]
  by_cases hz : (sortedData data).length = 0
  · simp only [if_pos hz]
  · simp only [if_neg hz]
    unfold lowIndex readMedian
    by_cases ho : (sortedData data).length % 2 = 1
    · simp only [if_pos ho, if_neg (not_not_intro ho)]
      rfl
    · simp only [if_neg ho, if_pos ho]
      rfl

/-- The functional and imperative checked entry points agree on all inputs. -/
theorem equivalence_thm (data : List α) :
    benchmarkMedianLow data = benchmarkMedianLowImperative data := by
  unfold benchmarkMedianLow benchmarkMedianLowImperative
  dsimp only [Id.run, Bind.bind, Pure.pure]
  simp only [medianLow_equivalence_thm]

end StatisticsMedianLow
