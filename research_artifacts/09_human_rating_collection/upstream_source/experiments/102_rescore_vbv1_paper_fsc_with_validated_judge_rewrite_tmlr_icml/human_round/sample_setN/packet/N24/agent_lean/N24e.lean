import Mathlib

/-!
# Low median of numeric data (`statistics.median_low`)

Translation of Python's `statistics.median_low` (CPython `Lib/statistics.py`).

The Python program sorts the data and returns the middle value when the
number of data points is odd, and the smaller of the two middle values when it
is even.  The empty list raises `StatisticsError`; we model that error case by
returning `none`.

The data is modelled as a `List α` for an arbitrary linear order `α : Type`
(Python accepts any totally ordered `numbers.Number` values, e.g. `Int`, `Rat`,
`Real`); all ground tests are run at `α := Int`.
-/

namespace «28_statistics_median_low»

variable {α : Type} [LinearOrder α]

/-! ## Functional implementation -/

/-- Low median: sort the data, then take the middle element (odd length) or
the smaller of the two middle elements (even length).  Returns `none` for the
empty list (Python raises `StatisticsError`). -/
def medianLow (data : List α) : Option α :=
  let sorted := List.insertionSort (· ≤ ·) data
  let n := sorted.length
  if n = 0 then none
  else if n % 2 = 1 then sorted[n / 2]?
  else sorted[n / 2 - 1]?

/-! ## Unit tests (mirroring the Python `check` function) -/

-- 1. Odd number of elements (returns middle value)
example : medianLow ([1, 3, 5] : List Int) = some 3 := by native_decide
example : medianLow ([1, 2, 3, 4, 5, 6, 9] : List Int) = some 4 := by native_decide
-- 2. Even number of elements (returns smaller of two middle values)
example : medianLow ([1, 3, 5, 7] : List Int) = some 3 := by native_decide
example : medianLow ([1, 2, 3, 4, 5, 6] : List Int) = some 3 := by native_decide
-- 3. Single value
example : medianLow ([42] : List Int) = some 42 := by native_decide
-- 4. Two values
example : medianLow ([10, 20] : List Int) = some 10 := by native_decide
-- 5. Unsorted input
example : medianLow ([9, 1, 6, 2, 5, 4, 3] : List Int) = some 4 := by native_decide
-- 6. Negative values
example : medianLow ([-5, -1, 0, 3, 7] : List Int) = some 0 := by native_decide
example : medianLow ([-10, -5, 5, 10] : List Int) = some (-5) := by native_decide
-- 7. Error case: empty data
example : medianLow ([] : List Int) = none := by native_decide

#eval medianLow ([1, 3, 5] : List Int)            -- some 3
#eval medianLow ([1, 3, 5, 7] : List Int)         -- some 3
#eval medianLow ([9, 1, 6, 2, 5, 4, 3] : List Int) -- some 4
#eval medianLow ([-10, -5, 5, 10] : List Int)     -- some (-5)
#eval medianLow ([] : List Int)                   -- none

/-! ## Pre-condition -/

/-- Pre-condition: the data is a non-empty list (of numbers). -/
def Pre (data : List α) : Prop := data ≠ []

/-! ## Properties -/

/-- The result is always the element at index `(n - 1) / 2` of the sorted data
(this is the same as `n / 2` for odd `n` and `n / 2 - 1` for even `n`). -/
theorem medianLow_eq (data : List α) :
    medianLow data = (List.insertionSort (· ≤ ·) data)[(data.length - 1) / 2]? := by
  unfold medianLow
  simp only [List.length_insertionSort]
  split
  · rename_i h
    rw [List.length_eq_zero_iff.mp h]
    rfl
  · rename_i h0
    split
    · rename_i h1
      have : data.length / 2 = (data.length - 1) / 2 := by omega
      rw [this]
    · rename_i h1
      have : data.length / 2 - 1 = (data.length - 1) / 2 := by omega
      rw [this]

/-- The sorted permutation of a list is unique, so `medianLow` can be read off
any sorted permutation of the data. -/
theorem insertionSort_eq_of_perm_of_sorted (data s : List α) (hperm : s.Perm data)
    (hsorted : s.Sorted (· ≤ ·)) : List.insertionSort (· ≤ ·) data = s :=
  List.eq_of_perm_of_sorted ((List.perm_insertionSort _ data).trans hperm.symm)
    (List.sorted_insertionSort _ data) hsorted

/-- Property: for every sorted permutation `s` of the data, the low median is
the element of `s` at index `(n - 1) / 2`. -/
def medianLow_sorted_index_prop (data : List α) : Prop :=
  ∀ s : List α, s.Perm data → s.Sorted (· ≤ ·) →
    medianLow data = s[(data.length - 1) / 2]?

theorem medianLow_sorted_index_thm (data : List α) : medianLow_sorted_index_prop data := by
  intro s hperm hsorted
  rw [medianLow_eq, insertionSort_eq_of_perm_of_sorted data s hperm hsorted]

/-- Corollary: on already sorted data, the low median is simply the element at
index `(n - 1) / 2`. -/
theorem medianLow_of_sorted (data : List α) (hsorted : data.Sorted (· ≤ ·)) :
    medianLow data = data[(data.length - 1) / 2]? :=
  medianLow_sorted_index_thm data data (List.Perm.refl data) hsorted

/-- Property (odd case of the Python program): when the number of data points is
odd, the middle value `s[n / 2]` of the sorted data is returned. -/
def medianLow_odd_prop (data : List α) : Prop :=
  data.length % 2 = 1 →
    ∀ s : List α, s.Perm data → s.Sorted (· ≤ ·) →
      medianLow data = s[data.length / 2]?

theorem medianLow_odd_thm (data : List α) : medianLow_odd_prop data := by
  intro hodd s hperm hsorted
  rw [medianLow_sorted_index_thm data s hperm hsorted]
  have : (data.length - 1) / 2 = data.length / 2 := by omega
  rw [this]

/-- Property (even case of the Python program): when the number of data points is
even (and non-zero), the smaller of the two middle values, `s[n / 2 - 1]`, is
returned. -/
def medianLow_even_prop (data : List α) : Prop :=
  data.length % 2 = 0 →
    ∀ s : List α, s.Perm data → s.Sorted (· ≤ ·) →
      medianLow data = s[data.length / 2 - 1]?

theorem medianLow_even_thm (data : List α) : medianLow_even_prop data := by
  intro heven s hperm hsorted
  rw [medianLow_sorted_index_thm data s hperm hsorted]
  by_cases h0 : data.length = 0
  · have hs : s = [] := by
      have := hperm.length_eq
      exact List.length_eq_zero_iff.mp (by omega)
    subst hs
    simp
  · have : (data.length - 1) / 2 = data.length / 2 - 1 := by omega
    rw [this]

/-- Even case, phrased as in the docstring: the smaller (`min`) of the two middle
values of the sorted data. -/
theorem medianLow_even_min (data : List α) (heven : data.length % 2 = 0) (h0 : data ≠ [])
    (s : List α) (hperm : s.Perm data) (hsorted : s.Sorted (· ≤ ·)) :
    ∃ (h₁ : data.length / 2 - 1 < s.length) (h₂ : data.length / 2 < s.length),
      medianLow data = some (min s[data.length / 2 - 1] s[data.length / 2]) := by
  have hlen := hperm.length_eq
  have hpos := List.length_pos_of_ne_nil h0
  have h₁ : data.length / 2 - 1 < s.length := by omega
  have h₂ : data.length / 2 < s.length := by omega
  refine ⟨h₁, h₂, ?_⟩
  rw [medianLow_even_thm data heven s hperm hsorted, List.getElem?_eq_getElem h₁]
  congr 1
  have hle : s[data.length / 2 - 1] ≤ s[data.length / 2] := by
    have := List.pairwise_iff_getElem.mp hsorted (data.length / 2 - 1) (data.length / 2) h₁ h₂
      (by omega)
    exact this
  exact (min_eq_left hle).symm

/-- Property: for non-empty data the result is `some m` with `m` an element of the data. -/
def medianLow_mem_prop (data : List α) : Prop :=
  ∃ m, medianLow data = some m ∧ m ∈ data

theorem medianLow_mem_thm (data : List α) (h : Pre data) : medianLow_mem_prop data := by
  rw [medianLow_mem_prop, medianLow_eq]
  have hlen : (data.length - 1) / 2 < (List.insertionSort (· ≤ ·) data).length := by
    rw [List.length_insertionSort]
    have := List.length_pos_of_ne_nil h
    omega
  refine ⟨_, List.getElem?_eq_getElem hlen, ?_⟩
  exact (List.perm_insertionSort _ data).mem_iff.mp (List.getElem_mem hlen)

/-- Property: `medianLow` fails (`none`) exactly on the empty list -- the
`StatisticsError` case of the Python program. -/
def medianLow_none_iff_prop (data : List α) : Prop :=
  medianLow data = none ↔ data = []

theorem medianLow_none_iff_thm (data : List α) : medianLow_none_iff_prop data := by
  unfold medianLow_none_iff_prop
  constructor
  · intro hnone
    by_contra hne
    obtain ⟨m, hm, _⟩ := medianLow_mem_thm data hne
    rw [hm] at hnone
    exact Option.some_ne_none m hnone
  · rintro rfl
    rfl

theorem medianLow_nil : medianLow ([] : List α) = none := rfl

/-- Property: the low median is invariant under permutation of the data (the
Python program sorts the data first). -/
def medianLow_perm_prop (data : List α) : Prop :=
  ∀ data' : List α, data'.Perm data → medianLow data' = medianLow data

theorem medianLow_perm_thm (data : List α) : medianLow_perm_prop data := by
  intro data' hperm
  rw [medianLow_eq data', medianLow_eq data, hperm.length_eq]
  congr 1
  exact List.eq_of_perm_of_sorted
    (((List.perm_insertionSort _ data').trans hperm).trans (List.perm_insertionSort _ data).symm)
    (List.sorted_insertionSort _ data') (List.sorted_insertionSort _ data)

/-! ### Counting characterisation of the low median -/

/-- In a sorted list, at least `k + 1` elements are `≤ s[k]`. -/
theorem countP_le_of_sorted (s : List α) (hs : s.Sorted (· ≤ ·)) (k : ℕ) (hk : k < s.length) :
    k + 1 ≤ s.countP (· ≤ s[k]) := by
  have hsplit : s = s.take k ++ (s[k] :: s.drop (k + 1)) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hs' : (s.take k ++ (s[k] :: s.drop (k + 1))).Sorted (· ≤ ·) :=
    Eq.mp (congrArg (List.Sorted (· ≤ ·)) hsplit) hs
  unfold List.Sorted at hs'
  rw [List.pairwise_append] at hs'
  obtain ⟨_, _, h3⟩ := hs'
  have htake : (s.take k).countP (· ≤ s[k]) = (s.take k).length := by
    rw [List.countP_eq_length]
    intro a ha
    simpa using h3 a ha s[k] (List.mem_cons_self ..)
  have hcons : 1 ≤ (s[k] :: s.drop (k + 1)).countP (· ≤ s[k]) := by
    rw [List.countP_cons_of_pos (by simp)]
    omega
  have htotal : s.countP (· ≤ s[k]) =
      (s.take k).countP (· ≤ s[k]) + (s[k] :: s.drop (k + 1)).countP (· ≤ s[k]) := by
    rw [← List.countP_append, ← hsplit]
  have hlen : (s.take k).length = k := by
    rw [List.length_take]
    omega
  omega

/-- In a sorted list, at least `s.length - k` elements are `≥ s[k]`. -/
theorem countP_ge_of_sorted (s : List α) (hs : s.Sorted (· ≤ ·)) (k : ℕ) (hk : k < s.length) :
    s.length - k ≤ s.countP (fun x => s[k] ≤ x) := by
  have hsplit : s = s.take k ++ (s[k] :: s.drop (k + 1)) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hs' : (s.take k ++ (s[k] :: s.drop (k + 1))).Sorted (· ≤ ·) :=
    Eq.mp (congrArg (List.Sorted (· ≤ ·)) hsplit) hs
  unfold List.Sorted at hs'
  rw [List.pairwise_append] at hs'
  obtain ⟨_, h2, _⟩ := hs'
  rw [List.pairwise_cons] at h2
  obtain ⟨h2, _⟩ := h2
  have hcons : (s[k] :: s.drop (k + 1)).countP (fun x => s[k] ≤ x) =
      (s[k] :: s.drop (k + 1)).length := by
    rw [List.countP_eq_length]
    intro a ha
    rw [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp
    · simpa using h2 a ha
  have htotal : s.countP (fun x => s[k] ≤ x) =
      (s.take k).countP (fun x => s[k] ≤ x) + (s[k] :: s.drop (k + 1)).countP (fun x => s[k] ≤ x) := by
    rw [← List.countP_append, ← hsplit]
  have hlen : (s[k] :: s.drop (k + 1)).length = s.length - k := by
    rw [List.length_cons, List.length_drop]
    omega
  omega

/-- Property: at least `⌈n / 2⌉ = (n + 1) / 2` of the data points are `≤` the low median. -/
def medianLow_count_le_prop (data : List α) : Prop :=
  ∀ m, medianLow data = some m → (data.length + 1) / 2 ≤ data.countP (· ≤ m)

theorem medianLow_count_le_thm (data : List α) : medianLow_count_le_prop data := by
  intro m hm
  rw [medianLow_eq, List.getElem?_eq_some_iff] at hm
  obtain ⟨hk, rfl⟩ := hm
  rw [← (List.perm_insertionSort (· ≤ ·) data).countP_eq]
  have := countP_le_of_sorted _ (List.sorted_insertionSort (· ≤ ·) data) _ hk
  rw [List.length_insertionSort] at hk
  omega

/-- Property: at least `n / 2 + 1` of the data points are `≥` the low median
(so the low median never exceeds the high median). -/
def medianLow_count_ge_prop (data : List α) : Prop :=
  ∀ m, medianLow data = some m → data.length / 2 + 1 ≤ data.countP (fun x => m ≤ x)

theorem medianLow_count_ge_thm (data : List α) : medianLow_count_ge_prop data := by
  intro m hm
  rw [medianLow_eq, List.getElem?_eq_some_iff] at hm
  obtain ⟨hk, rfl⟩ := hm
  rw [← (List.perm_insertionSort (· ≤ ·) data).countP_eq]
  have := countP_ge_of_sorted _ (List.sorted_insertionSort (· ≤ ·) data) _ hk
  rw [List.length_insertionSort] at this hk
  omega

/-! ## Post-condition -/

/-- Post-condition: conjunction of all the properties above. -/
def Post_prop (data : List α) : Prop :=
  medianLow_mem_prop data ∧
  medianLow_sorted_index_prop data ∧
  medianLow_odd_prop data ∧
  medianLow_even_prop data ∧
  medianLow_count_le_prop data ∧
  medianLow_count_ge_prop data ∧
  medianLow_perm_prop data ∧
  medianLow_none_iff_prop data

/-! ## Property-based tests (executable Boolean forms at `α := Int`) -/

/-- Executable form of `medianLow_mem_prop`. -/
def memCheck (xs : List Int) : Bool :=
  match medianLow xs with
  | some m => m ∈ xs
  | none => false

/-- Executable form of `medianLow_count_le_prop`. -/
def countLeCheck (xs : List Int) : Bool :=
  (medianLow xs).all (fun m => (xs.length + 1) / 2 ≤ xs.countP (· ≤ m))

/-- Executable form of `medianLow_count_ge_prop`. -/
def countGeCheck (xs : List Int) : Bool :=
  (medianLow xs).all (fun m => xs.length / 2 + 1 ≤ xs.countP (fun x => m ≤ x))

/-- Executable form of the sorted-index / odd / even properties, using the
independent core `List.mergeSort` as the sorted permutation. -/
def sortedIndexCheck (xs : List Int) : Bool :=
  let s := xs.mergeSort
  let n := xs.length
  medianLow xs == s[(n - 1) / 2]? &&
  (n % 2 = 1 → medianLow xs = s[n / 2]?) &&
  (n % 2 = 0 → medianLow xs = s[n / 2 - 1]?)

/-- Executable form of the permutation-invariance property (reverse and rotations). -/
def permCheck (xs ys : List Int) : Bool :=
  medianLow xs.reverse == medianLow xs && medianLow (xs ++ ys) == medianLow (ys ++ xs)

/-- Executable form of `medianLow_none_iff_prop`. -/
def noneIffCheck (xs : List Int) : Bool :=
  ((medianLow xs).isNone == xs.isEmpty)

/-- Executable form of `Post_prop` (for non-empty input). -/
def postCheck (xs ys : List Int) : Bool :=
  memCheck xs && countLeCheck xs && countGeCheck xs && sortedIndexCheck xs &&
  permCheck xs ys && noneIffCheck xs

-- Randomized PBTs
#eval Plausible.Testable.check (∀ xs : List Int, (xs.isEmpty || memCheck xs) = true)
#eval Plausible.Testable.check (∀ xs : List Int, countLeCheck xs = true)
#eval Plausible.Testable.check (∀ xs : List Int, countGeCheck xs = true)
#eval Plausible.Testable.check (∀ xs : List Int, sortedIndexCheck xs = true)
#eval Plausible.Testable.check (∀ xs ys : List Int, permCheck xs ys = true)
#eval Plausible.Testable.check (∀ xs : List Int, noneIffCheck xs = true)
#eval Plausible.Testable.check (∀ xs ys : List Int, (xs.isEmpty || postCheck xs ys) = true)
#eval Plausible.Testable.check
  (∀ xs : List Int, medianLow xs = (List.insertionSort (· ≤ ·) xs)[(xs.length - 1) / 2]?)

-- Bounded / exhaustive PBTs on small inputs
example : (List.range 40).all (fun n =>
    let xs : List Int := (List.range n).map Int.ofNat
    n = 0 || (memCheck xs && countLeCheck xs && countGeCheck xs && sortedIndexCheck xs &&
      noneIffCheck xs && permCheck xs.reverse xs)) = true := by native_decide

example : (List.range 40).all (fun n =>
    let xs : List Int := (List.range n).map Int.ofNat
    n = 0 || medianLow xs == some (((n : Int) - 1) / 2)) = true := by native_decide

example : (List.range 40).all (fun n =>
    let xs : List Int := (List.range n).map (fun i => (Int.ofNat i) * 7 % 11 - 5)
    n = 0 || postCheck xs xs.reverse) = true := by native_decide

-- low median of a constant list is that constant
example : (List.range 30).all (fun n =>
    n = 0 || medianLow (List.replicate n (7 : Int)) == some 7) = true := by native_decide

/-! ## Correctness theorem: `Pre → Post` -/

theorem medianLow_correct (data : List α) (h : Pre data) : Post_prop data :=
  ⟨medianLow_mem_thm data h, medianLow_sorted_index_thm data, medianLow_odd_thm data,
    medianLow_even_thm data, medianLow_count_le_thm data, medianLow_count_ge_thm data,
    medianLow_perm_thm data, medianLow_none_iff_thm data⟩

/-! ## Imperative implementation -/

/-- Imperative linear scan through `l` with a position counter starting at `i`,
remembering the element found at position `idx` (initially `acc`).  The start
state is a parameter so that the loop invariant can be stated and proved. -/
def scanNth (l : List α) (idx : ℕ) (i : ℕ) (acc : Option α) : Option α := Id.run do
  let mut i := i
  let mut result := acc
  for x in l do
    result := if i = idx then some x else result
    i := i + 1
  return result

omit [LinearOrder α] in
/-- Loop invariant of `scanNth`. -/
theorem scanNth_eq (l : List α) (idx i : ℕ) (acc : Option α) :
    scanNth l idx i acc = if i ≤ idx ∧ idx < i + l.length then l[idx - i]? else acc := by
  induction l generalizing i acc with
  | nil => simp [scanNth]
  | cons x xs ih =>
    unfold scanNth at ih ⊢
    simp only [List.forIn_cons, Id.run, bind, pure] at ih ⊢
    rw [ih]
    simp only [List.length_cons]
    by_cases h : i = idx
    · subst h
      have h2 : i ≤ i ∧ i < i + (xs.length + 1) := by omega
      simp [h2]
    · by_cases h3 : i + 1 ≤ idx ∧ idx < i + 1 + xs.length
      · have h4 : i ≤ idx ∧ idx < i + (xs.length + 1) := by omega
        rw [if_pos h3, if_pos h4]
        have : idx - i = (idx - (i + 1)) + 1 := by omega
        rw [this, List.getElem?_cons_succ]
      · have h4 : ¬ (i ≤ idx ∧ idx < i + (xs.length + 1)) := by omega
        rw [if_neg h3, if_neg h4, if_neg h]

omit [LinearOrder α] in
/-- Scanning from position `0` computes `l[idx]?`. -/
theorem scanNth_zero (l : List α) (idx : ℕ) : scanNth l idx 0 none = l[idx]? := by
  rw [scanNth_eq]
  split
  · simp
  · rename_i hn
    symm
    rw [List.getElem?_eq_none_iff]
    omega

/-- Imperative version of `median_low`, following the control flow of the Python
program: sort, check for emptiness (error → `none`), choose the index with a
mutable variable, then walk through the sorted data with a counter to fetch the
element at that index. -/
def medianLowImp (data : List α) : Option α := Id.run do
  let sorted := List.insertionSort (· ≤ ·) data
  let n := sorted.length
  if n = 0 then
    return none
  let mut idx : ℕ := 0
  if n % 2 = 1 then
    idx := n / 2
  else
    idx := n / 2 - 1
  -- walk through the sorted data to fetch the element at position `idx`
  let mut i : ℕ := 0
  let mut result : Option α := none
  for x in sorted do
    result := if i = idx then some x else result
    i := i + 1
  return result

/-! ### Imperative tests -/

example : medianLowImp ([1, 3, 5] : List Int) = some 3 := by native_decide
example : medianLowImp ([1, 2, 3, 4, 5, 6, 9] : List Int) = some 4 := by native_decide
example : medianLowImp ([1, 3, 5, 7] : List Int) = some 3 := by native_decide
example : medianLowImp ([1, 2, 3, 4, 5, 6] : List Int) = some 3 := by native_decide
example : medianLowImp ([42] : List Int) = some 42 := by native_decide
example : medianLowImp ([10, 20] : List Int) = some 10 := by native_decide
example : medianLowImp ([9, 1, 6, 2, 5, 4, 3] : List Int) = some 4 := by native_decide
example : medianLowImp ([-5, -1, 0, 3, 7] : List Int) = some 0 := by native_decide
example : medianLowImp ([-10, -5, 5, 10] : List Int) = some (-5) := by native_decide
example : medianLowImp ([] : List Int) = none := by native_decide
example : scanNth ([5, 6, 7] : List Int) 1 0 none = some 6 := by native_decide
example : scanNth ([5, 6, 7] : List Int) 3 0 none = none := by native_decide

#eval medianLowImp ([9, 1, 6, 2, 5, 4, 3] : List Int) -- some 4
#eval medianLowImp ([] : List Int)                    -- none

-- PBTs for the imperative layer
#eval Plausible.Testable.check (∀ (xs : List Int) (i : ℕ), scanNth xs i 0 none = xs[i]?)
#eval Plausible.Testable.check (∀ xs : List Int, medianLowImp xs = medianLow xs)
example : (List.range 25).all (fun n =>
    let xs : List Int := (List.range n).map (fun i => (Int.ofNat i) * 5 % 7 - 3)
    medianLowImp xs == medianLow xs) = true := by native_decide

/-! ## Equivalence theorem: functional = imperative -/

theorem medianLowImp_eq_medianLow (data : List α) : medianLowImp data = medianLow data := by
  -- the loop in `medianLowImp` is definitionally `scanNth sorted idx 0 none`
  have h : medianLowImp data =
      (let sorted := List.insertionSort (· ≤ ·) data
       let n := sorted.length
       if n = 0 then none
       else if n % 2 = 1 then scanNth sorted (n / 2) 0 none
       else scanNth sorted (n / 2 - 1) 0 none) := by
    unfold medianLowImp scanNth
    rfl
  rw [h]
  simp only [scanNth_zero]
  rfl

end «28_statistics_median_low»
