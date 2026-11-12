import Mathlib

/-!
# Task 28 — Python `statistics.median_low` formalized in Lean 4

This file formalizes CPython's `statistics.median_low` (`Lib/statistics.py`):
the *low median* of numeric data.  When the number of data points is odd, the
middle value of the sorted data is returned; when it is even, the smaller of
the two middle values is returned.  Empty input raises `StatisticsError` in
Python and is modelled here by `none`.

**Model.**
* Input data is modelled as `List Int`; the Python pre-condition "data is a
  list/tuple of numbers" is captured by typing, so `Pre` retains the remaining
  requirement that the input be non-empty.
* `medianLow` sorts a copy of the input (insertion sort, modelling the fresh
  list returned by Python's `sorted`) and picks the low middle element.
* Proved properties: the result is the correct order statistic of the sorted
  data (`medianLow_prop_value`), it is an element of the input
  (`medianLow_prop_mem`), at least half of the data lies on each side of it
  (`medianLow_prop_balanced`), and the function is total on non-empty input
  (`medianLow_prop_total`).  An imperative implementation using `Id.run` with
  mutable state is shown to coincide with the functional one.
-/

namespace statistics_median_low

/-! ## 1. Functional implementation -/

/-- Insert `x` into a sorted list, keeping it sorted (stable: `x` is placed
before the first element that is `≥ x`). -/
def insertSorted (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- Insertion sort: the executable model of Python's `sorted(data)`, which
returns a new sorted list. -/
def insertionSort (data : List Int) : List Int :=
  data.foldl (fun acc x => insertSorted x acc) []

/-- Low median of an already-sorted list; `none` on empty input (Python raises
`StatisticsError`). -/
def medianLowSorted (s : List Int) : Option Int :=
  if s.length = 0 then none
  else if s.length % 2 = 1 then s[s.length / 2]?
  else s[s.length / 2 - 1]?

/-- The benchmark function: the low median of `data`. -/
def medianLow (data : List Int) : Option Int :=
  medianLowSorted (insertionSort data)

/-! ## 2. Unit tests -/

example : medianLow [1, 3, 5] = some 3 := by native_decide
example : medianLow [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide
example : medianLow [1, 3, 5, 7] = some 3 := by native_decide
example : medianLow [1, 2, 3, 4, 5, 6] = some 3 := by native_decide
example : medianLow [42] = some 42 := by native_decide
example : medianLow [10, 20] = some 10 := by native_decide
example : medianLow [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide
example : medianLow [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : medianLow [-10, -5, 5, 10] = some (-5) := by native_decide
example : medianLow ([] : List Int) = none := by native_decide

#eval medianLow [1, 3, 5]          -- some 3
#eval medianLow [1, 3, 5, 7]       -- some 3
#eval medianLow [9, 1, 6, 2, 5, 4, 3]  -- some 4
#eval medianLow ([] : List Int)    -- none (Python raises StatisticsError)

/-! ## 3. Pre-condition -/

/-- Python `pre data`: `data` must be a non-empty list/tuple of numbers.
Modelling numbers as `Int` makes the "numbers" part hold by typing. -/
def Pre (data : List Int) : Prop := data ≠ []

/-! ## 4. Auxiliary lemmas about the sorting functions -/

theorem mem_insertSorted {x a : Int} {xs : List Int} :
    a ∈ insertSorted x xs ↔ a = x ∨ a ∈ xs := by
  induction xs with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    simp only [insertSorted]
    by_cases hxy : x ≤ y
    · simp [hxy]
    · simp only [if_neg hxy, List.mem_cons, ih]
      tauto

theorem perm_insertSorted (x : Int) (xs : List Int) :
    List.Perm (insertSorted x xs) (x :: xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    simp only [insertSorted]
    by_cases hxy : x ≤ y
    · rw [if_pos hxy]
    · rw [if_neg hxy]
      exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

theorem foldl_insertSorted_perm (data acc : List Int) :
    List.Perm (data.foldl (fun s x => insertSorted x s) acc) (data.reverse ++ acc) := by
  induction data generalizing acc with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    have h1 : List.Perm (List.foldl (fun s x => insertSorted x s) (insertSorted y acc) ys)
        (ys.reverse ++ (y :: acc)) :=
      (ih _).trans (List.Perm.append_left _ (perm_insertSorted y acc))
    have h2 : ys.reverse ++ (y :: acc) = (y :: ys).reverse ++ acc := by
      rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact h2 ▸ h1

theorem perm_insertionSort (data : List Int) : List.Perm (insertionSort data) data := by
  have h := foldl_insertSorted_perm data []
  rw [List.append_nil] at h
  exact h.trans (List.reverse_perm data)

theorem length_insertionSort (data : List Int) :
    (insertionSort data).length = data.length :=
  (perm_insertionSort data).length_eq

theorem mem_insertionSort {a : Int} {xs : List Int} :
    a ∈ insertionSort xs ↔ a ∈ xs :=
  (perm_insertionSort xs).mem_iff

theorem sorted_insertSorted (x : Int) : ∀ {xs : List Int}, xs.Sorted (· ≤ ·) →
    (insertSorted x xs).Sorted (· ≤ ·) := by
  intro xs
  induction xs with
  | nil =>
    intro _
    exact List.sorted_singleton x
  | cons y ys ih =>
    intro h
    rw [List.sorted_cons] at h
    simp only [insertSorted]
    by_cases hxy : x ≤ y
    · rw [if_pos hxy, List.sorted_cons]
      constructor
      · intro b hb
        rw [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact hxy
        · exact le_trans hxy (h.1 b hb)
      · exact List.sorted_cons.mpr h
    · rw [if_neg hxy, List.sorted_cons]
      constructor
      · intro b hb
        rw [mem_insertSorted] at hb
        rcases hb with rfl | hb
        · exact le_of_not_ge hxy
        · exact h.1 b hb
      · exact ih h.2

theorem sorted_foldl_insertSorted (data acc : List Int) (h : acc.Sorted (· ≤ ·)) :
    (data.foldl (fun s x => insertSorted x s) acc).Sorted (· ≤ ·) := by
  induction data generalizing acc with
  | nil => exact h
  | cons y ys ih => exact ih _ (sorted_insertSorted y h)

theorem sorted_insertionSort (data : List Int) : (insertionSort data).Sorted (· ≤ ·) :=
  sorted_foldl_insertSorted data [] List.sorted_nil

/-! ## 5. Counting lemmas for sorted lists -/

/-- Every element of `s.take (k+1)` is at most `s[k]` in a sorted list. -/
theorem mem_take_le_getElem {s : List Int} (hs : s.Sorted (· ≤ ·)) {k : Nat}
    (hk : k < s.length) :
    ∀ a ∈ s.take (k + 1), a ≤ s[k]'hk := by
  intro a ha
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨hil, -⟩ := List.getElem?_eq_some_iff.mp hi
  rw [List.length_take] at hil
  have hk1 : i < k + 1 := lt_of_lt_of_le hil (Nat.min_le_left _ _)
  have hk2 : i < s.length := lt_of_lt_of_le hil (Nat.min_le_right _ _)
  rw [List.getElem?_take, if_pos hk1] at hi
  obtain ⟨_, hval⟩ := List.getElem?_eq_some_iff.mp hi
  have hle : s.get ⟨i, hk2⟩ ≤ s.get ⟨k, hk⟩ :=
    hs.rel_get_of_le (show (⟨i, hk2⟩ : Fin s.length) ≤ ⟨k, hk⟩ from Nat.le_of_lt_succ hk1)
  simp only [List.get_eq_getElem] at hle
  exact hval ▸ hle

/-- Every element of `s.drop k` is at least `s[k]` in a sorted list. -/
theorem mem_drop_ge_getElem {s : List Int} (hs : s.Sorted (· ≤ ·)) {k : Nat}
    (hk : k < s.length) :
    ∀ a ∈ s.drop k, s[k]'hk ≤ a := by
  intro a ha
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
  rw [List.getElem?_drop] at hi
  obtain ⟨hki, hval⟩ := List.getElem?_eq_some_iff.mp hi
  have hle : s.get ⟨k, hk⟩ ≤ s.get ⟨k + i, hki⟩ :=
    hs.rel_get_of_le (show (⟨k, hk⟩ : Fin s.length) ≤ ⟨k + i, hki⟩ from Nat.le_add_right k i)
  simp only [List.get_eq_getElem] at hle
  exact hval ▸ hle

/-- In a list whose first `k+1` elements are all `≤ m`, at least `k+1`
elements are `≤ m`. -/
theorem filter_le_length_of_sorted {s : List Int} {k : Nat} (hk : k < s.length) (m : Int)
    (hall : ∀ a ∈ s.take (k + 1), a ≤ m) :
    k + 1 ≤ (s.filter fun x => decide (x ≤ m)).length := by
  have h1 : (s.take (k + 1)).filter (fun x => decide (x ≤ m)) = s.take (k + 1) := by
    rw [List.filter_eq_self]
    intro a ha
    simp only [decide_eq_true_eq]
    exact hall a ha
  have h2 : (s.filter fun x => decide (x ≤ m)).length =
      ((s.take (k + 1)).filter fun x => decide (x ≤ m)).length +
      ((s.drop (k + 1)).filter fun x => decide (x ≤ m)).length := by
    conv_lhs => rw [← List.take_append_drop (k + 1) s]
    rw [List.filter_append, List.length_append]
  rw [h2, h1, List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt hk)]
  omega

/-- In a list whose elements from position `k` on are all `≥ m`, at least
`length - k` elements are `≥ m`. -/
theorem filter_ge_length_of_sorted {s : List Int} {k : Nat} (_hk : k < s.length) (m : Int)
    (hall : ∀ a ∈ s.drop k, m ≤ a) :
    s.length - k ≤ (s.filter fun x => decide (m ≤ x)).length := by
  have h1 : (s.drop k).filter (fun x => decide (m ≤ x)) = s.drop k := by
    rw [List.filter_eq_self]
    intro a ha
    simp only [decide_eq_true_eq]
    exact hall a ha
  have h2 : (s.filter fun x => decide (m ≤ x)).length =
      ((s.take k).filter fun x => decide (m ≤ x)).length + (s.drop k).length := by
    conv_lhs => rw [← List.take_append_drop k s]
    rw [List.filter_append, List.length_append, h1]
  rw [h2, List.length_drop]
  omega

theorem filter_le_getElem_length {s : List Int} (hs : s.Sorted (· ≤ ·)) {k : Nat}
    (hk : k < s.length) :
    k + 1 ≤ (s.filter fun x => decide (x ≤ s[k]'hk)).length :=
  filter_le_length_of_sorted hk _ (mem_take_le_getElem hs hk)

theorem filter_ge_getElem_length {s : List Int} (hs : s.Sorted (· ≤ ·)) {k : Nat}
    (hk : k < s.length) :
    s.length - k ≤ (s.filter fun x => decide (s[k]'hk ≤ x)).length :=
  filter_ge_length_of_sorted hk _ (mem_drop_ge_getElem hs hk)

/-! ## 6. Property propositions and their theorems -/

/-- The result is the correct order statistic of the sorted data: the middle
element for odd lengths and the lower of the two middle elements for even
lengths. -/
def medianLow_prop_value (data : List Int) : Prop :=
  let s := insertionSort data
  s.length ≠ 0 →
    (s.length % 2 = 1 → medianLow data = s[s.length / 2]?) ∧
    (s.length % 2 ≠ 1 → medianLow data = s[s.length / 2 - 1]?)

/-- The low median is always an element of the input data. -/
def medianLow_prop_mem (data : List Int) : Prop :=
  ∀ m, medianLow data = some m → m ∈ data

/-- The median property: at least half of the data is `≤` the low median and
at least half is `≥` the low median. -/
def medianLow_prop_balanced (data : List Int) : Prop :=
  ∀ m, medianLow data = some m →
    (data.length + 1) / 2 ≤ (data.filter fun x => decide (x ≤ m)).length ∧
    (data.length + 1) / 2 ≤ (data.filter fun x => decide (m ≤ x)).length

/-- Totality: non-empty input always yields a result (the `StatisticsError`
only fires for empty data). -/
def medianLow_prop_total (data : List Int) : Prop :=
  data ≠ [] → ∃ m, medianLow data = some m

theorem medianLowSorted_odd {s : List Int} (h0 : s.length ≠ 0) (h1 : s.length % 2 = 1) :
    medianLowSorted s = s[s.length / 2]? := by
  simp only [medianLowSorted, if_neg h0, if_pos h1]

theorem medianLowSorted_even {s : List Int} (h0 : s.length ≠ 0) (h1 : s.length % 2 ≠ 1) :
    medianLowSorted s = s[s.length / 2 - 1]? := by
  simp only [medianLowSorted, if_neg h0, if_neg h1]

theorem medianLow_thm_value (data : List Int) : medianLow_prop_value data := by
  intro h0
  constructor
  · intro hodd
    exact medianLowSorted_odd h0 hodd
  · intro heven
    exact medianLowSorted_even h0 heven

theorem medianLow_thm_mem (data : List Int) : medianLow_prop_mem data := by
  intro m hm
  unfold medianLow medianLowSorted at hm
  split at hm
  · simp at hm
  · next _ =>
    split at hm
    · next _ =>
      apply mem_insertionSort.mp
      obtain ⟨hk, hval⟩ := List.getElem?_eq_some_iff.mp hm
      rw [← hval]
      exact List.get_mem _ _
    · next _ =>
      apply mem_insertionSort.mp
      obtain ⟨hk, hval⟩ := List.getElem?_eq_some_iff.mp hm
      rw [← hval]
      exact List.get_mem _ _

theorem medianLow_thm_balanced (data : List Int) : medianLow_prop_balanced data := by
  intro m hm
  have hperm : List.Perm (insertionSort data) data := perm_insertionSort data
  have hlen : (insertionSort data).length = data.length := hperm.length_eq
  have hs : (insertionSort data).Sorted (· ≤ ·) := sorted_insertionSort data
  unfold medianLow medianLowSorted at hm
  split at hm
  · simp at hm
  · next h0 =>
    split at hm
    · next hodd =>
      obtain ⟨hk, hval⟩ := List.getElem?_eq_some_iff.mp hm
      have hcle := filter_le_getElem_length hs hk
      have hcge := filter_ge_getElem_length hs hk
      rw [hval] at hcle hcge
      have hple := (hperm.filter fun x => decide (x ≤ m)).length_eq
      have hpge := (hperm.filter fun x => decide (m ≤ x)).length_eq
      constructor <;> omega
    · next heven =>
      obtain ⟨hk, hval⟩ := List.getElem?_eq_some_iff.mp hm
      have hcle := filter_le_getElem_length hs hk
      have hcge := filter_ge_getElem_length hs hk
      rw [hval] at hcle hcge
      have hple := (hperm.filter fun x => decide (x ≤ m)).length_eq
      have hpge := (hperm.filter fun x => decide (m ≤ x)).length_eq
      constructor <;> omega

theorem medianLow_thm_total (data : List Int) : medianLow_prop_total data := by
  intro hne
  have h0 : (insertionSort data).length ≠ 0 := by
    intro h
    have hlen : (insertionSort data).length = data.length := (perm_insertionSort data).length_eq
    rw [hlen] at h
    exact hne (List.length_eq_zero_iff.mp h)
  by_cases hpar : (insertionSort data).length % 2 = 1
  · have hk : (insertionSort data).length / 2 < (insertionSort data).length :=
      Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
    refine ⟨(insertionSort data)[(insertionSort data).length / 2]'hk, ?_⟩
    have e1 : medianLow data = (insertionSort data)[(insertionSort data).length / 2]? :=
      medianLowSorted_odd h0 hpar
    rw [e1]
    exact List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩
  · have hk : (insertionSort data).length / 2 - 1 < (insertionSort data).length := by
      have hpos : 0 < (insertionSort data).length := Nat.pos_of_ne_zero h0
      omega
    refine ⟨(insertionSort data)[(insertionSort data).length / 2 - 1]'hk, ?_⟩
    have e1 : medianLow data = (insertionSort data)[(insertionSort data).length / 2 - 1]? :=
      medianLowSorted_even h0 hpar
    rw [e1]
    exact List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩

/-! ## 7. Post-condition -/

/-- The post-condition: the conjunction of all proved properties of
`medianLow`. -/
def Post_prop (data : List Int) : Prop :=
  medianLow_prop_value data ∧ medianLow_prop_mem data ∧
    medianLow_prop_balanced data ∧ medianLow_prop_total data

/-! ## 8. Property-based tests -/

/-- Executable Boolean form of `medianLow_prop_value`. -/
def checkValue (data : List Int) : Bool :=
  let s := insertionSort data
  if s.length = 0 then true
  else if s.length % 2 = 1 then medianLow data == s[s.length / 2]?
  else medianLow data == s[s.length / 2 - 1]?

/-- Executable Boolean form of `medianLow_prop_mem`. -/
def checkMem (data : List Int) : Bool :=
  match medianLow data with
  | none => true
  | some m => data.contains m

/-- Executable Boolean form of `medianLow_prop_balanced`. -/
def checkBalanced (data : List Int) : Bool :=
  match medianLow data with
  | none => true
  | some m =>
    decide ((data.length + 1) / 2 ≤ (data.filter fun x => decide (x ≤ m)).length) &&
    decide ((data.length + 1) / 2 ≤ (data.filter fun x => decide (m ≤ x)).length)

/-- Executable Boolean form of `medianLow_prop_total`. -/
def checkTotal (data : List Int) : Bool :=
  if data.isEmpty then true else (medianLow data).isSome

/-- Executable Boolean form of `Post_prop`. -/
def checkPost (data : List Int) : Bool :=
  checkValue data && checkMem data && checkBalanced data && checkTotal data

-- Randomized PBTs (Plausible ships with Mathlib; a counterexample fails compilation)
#eval Plausible.Testable.check (∀ data : List Int, checkValue data = true)
#eval Plausible.Testable.check (∀ data : List Int, checkMem data = true)
#eval Plausible.Testable.check (∀ data : List Int, checkBalanced data = true)
#eval Plausible.Testable.check (∀ data : List Int, checkTotal data = true)
#eval Plausible.Testable.check (∀ data : List Int, checkPost data = true)

/-- All lists of length `n` with entries from `[-2, -1, 0, 1, 2]`, for
exhaustive small-case checks. -/
def smallLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (smallLists n).flatMap fun xs => [-2, -1, 0, 1, 2].map fun x => x :: xs

-- Bounded (exhaustive) PBTs: every property and the post-condition, checked on
-- all 781 lists of length at most 4 over `{-2, -1, 0, 1, 2}`.
example : (List.range 5).all (fun n => (smallLists n).all checkValue) = true := by
  native_decide
example : (List.range 5).all (fun n => (smallLists n).all checkMem) = true := by
  native_decide
example : (List.range 5).all (fun n => (smallLists n).all checkBalanced) = true := by
  native_decide
example : (List.range 5).all (fun n => (smallLists n).all checkTotal) = true := by
  native_decide
example : (List.range 5).all (fun n => (smallLists n).all checkPost) = true := by
  native_decide

/-! ## 9. Correctness theorem: `Pre → Post` -/

theorem medianLow_correct (data : List Int) : Pre data → Post_prop data := by
  intro _
  exact ⟨medianLow_thm_value data, medianLow_thm_mem data,
    medianLow_thm_balanced data, medianLow_thm_total data⟩

/-! ## 10. Imperative implementation (mutable state in `Id.run`) -/

/-- Mutable insertion-sort loop: every element of `data` is inserted into a
mutable accumulator that is kept sorted. -/
def sortImp (data : List Int) : List Int := Id.run do
  let mut sorted : List Int := []
  for x in data do
    sorted := insertSorted x sorted
  return sorted

/-- Imperative low median: sorts with a mutable accumulator inside `Id.run`
and picks the low middle element. -/
def medianLowImp (data : List Int) : Option Int := Id.run do
  let mut sorted : List Int := []
  for x in data do
    sorted := insertSorted x sorted
  let n := sorted.length
  if n = 0 then
    return none
  else if n % 2 = 1 then
    return sorted[n / 2]?
  else
    return sorted[n / 2 - 1]?

/-! ## 11. Imperative tests -/

example : medianLowImp [1, 3, 5] = some 3 := by native_decide
example : medianLowImp [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide
example : medianLowImp [1, 3, 5, 7] = some 3 := by native_decide
example : medianLowImp [1, 2, 3, 4, 5, 6] = some 3 := by native_decide
example : medianLowImp [42] = some 42 := by native_decide
example : medianLowImp [10, 20] = some 10 := by native_decide
example : medianLowImp [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide
example : medianLowImp [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : medianLowImp [-10, -5, 5, 10] = some (-5) := by native_decide
example : medianLowImp ([] : List Int) = none := by native_decide

#eval medianLowImp [1, 2, 3, 4, 5, 6]   -- some 3
#eval medianLowImp [-10, -5, 5, 10]     -- some (-5)

/-! ## 12. Equivalence: functional = imperative -/

/-- The mutable loop computes the left fold of `insertSorted`. -/
theorem sortLoop_eq (data acc : List Int) :
    Id.run (forIn data acc fun x s => ForInStep.yield (insertSorted x s)) =
      data.foldl (fun s x => insertSorted x s) acc := by
  induction data generalizing acc with
  | nil => rfl
  | cons y ys ih =>
    rw [List.forIn_cons]
    simp only [Id.pure_eq, Id.bind_eq]
    rw [ih]
    rw [List.foldl_cons]

theorem sortImp_eq_insertionSort (data : List Int) : sortImp data = insertionSort data := by
  show Id.run (forIn data [] fun x s => ForInStep.yield (insertSorted x s)) = insertionSort data
  rw [sortLoop_eq data []]
  rfl

theorem medianLow_imp_eq (data : List Int) : medianLowImp data = medianLow data := by
  show medianLowSorted (sortImp data) = medianLowSorted (insertionSort data)
  rw [sortImp_eq_insertionSort data]

-- PBT for the equivalence theorem
#eval Plausible.Testable.check (∀ data : List Int, medianLowImp data = medianLow data)

end statistics_median_low
