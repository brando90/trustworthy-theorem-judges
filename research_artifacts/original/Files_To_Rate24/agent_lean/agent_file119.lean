import Mathlib

/-!
# Low Median of Numeric Data (`statistics.median_low`)

This module formalizes Python's `statistics.median_low` and `benchmark_median_low` functions
from the standard `statistics` library.

When the number of data points is odd, the middle value of the sorted data is returned.
When the number of data points is even, the smaller of the two middle values is returned.
When the input list is empty, `none` is returned (corresponding to raising `StatisticsError`).
-/

namespace «28_statistics_median_low»

/-! ## 1. Functional Implementation -/

/-- Return the low median of numeric data.
    When the number of data points is odd, the middle value is returned.
    When it is even, the smaller of the two middle values is returned.
    Returns `none` on empty data (modeling `StatisticsError`). -/
def median_low (data : List Int) : Option Int :=
  let sorted := data.mergeSort
  let n := sorted.length
  if n == 0 then
    none
  else if n % 2 == 1 then
    sorted[n / 2]?
  else
    sorted[n / 2 - 1]?

/-- Executable Boolean precondition check corresponding to Python's `pre(data)`. -/
def pre_check (data : List Int) : Bool :=
  !data.isEmpty

/-- Main function to be verified: checks the precondition and delegates to `median_low`. -/
def benchmark_median_low (data : List Int) : Option Int :=
  if !pre_check data then
    none
  else
    median_low data

/-! ## 2. Unit Tests -/

-- 1. Odd number of elements (returns middle value)
example : median_low [1, 3, 5] = some 3 := by native_decide
example : median_low [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide
example : benchmark_median_low [1, 3, 5] = some 3 := by native_decide
example : benchmark_median_low [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide

-- 2. Even number of elements (returns smaller of two middle values)
example : median_low [1, 3, 5, 7] = some 3 := by native_decide
example : median_low [1, 2, 3, 4, 5, 6] = some 3 := by native_decide
example : benchmark_median_low [1, 3, 5, 7] = some 3 := by native_decide
example : benchmark_median_low [1, 2, 3, 4, 5, 6] = some 3 := by native_decide

-- 3. Single value
example : median_low [42] = some 42 := by native_decide
example : benchmark_median_low [42] = some 42 := by native_decide

-- 4. Two values
example : median_low [10, 20] = some 10 := by native_decide
example : benchmark_median_low [10, 20] = some 10 := by native_decide

-- 5. Unsorted input
example : median_low [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide
example : benchmark_median_low [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide

-- 6. Negative values
example : median_low [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : median_low [-10, -5, 5, 10] = some (-5) := by native_decide
example : benchmark_median_low [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : benchmark_median_low [-10, -5, 5, 10] = some (-5) := by native_decide

-- 7. Error cases (empty list returns `none`)
example : median_low [] = none := by native_decide
example : benchmark_median_low [] = none := by native_decide

#eval median_low [1, 3, 5]
#eval median_low [1, 3, 5, 7]
#eval median_low [9, 1, 6, 2, 5, 4, 3]
#eval median_low [-10, -5, 5, 10]
#eval median_low []
#eval benchmark_median_low [1, 3, 5]
#eval benchmark_median_low []

/-! ## 3. Pre-condition -/

/-- Pre-condition: `data` is a non-empty list of integers. -/
def Pre (data : List Int) : Prop :=
  data ≠ []

theorem Pre_iff_pre_check (data : List Int) : Pre data ↔ pre_check data = true := by
  cases data <;> simp [Pre, pre_check]

theorem Pre_iff_length_pos (data : List Int) : Pre data ↔ 0 < data.length :=
  List.length_pos_iff.symm

/-! ## 4. Helper Lemmas & Properties -/

theorem benchmark_median_low_eq_median_low (data : List Int) :
    benchmark_median_low data = median_low data := by
  cases data with
  | nil => simp [benchmark_median_low, pre_check, median_low]
  | cons x xs => rfl

theorem mergeSort_eq_of_perm {l₁ l₂ : List Int} (h : l₁.Perm l₂) :
    l₁.mergeSort = l₂.mergeSort :=
  List.eq_of_perm_of_sorted
    ((List.mergeSort_perm l₁ _).trans (h.trans (List.mergeSort_perm l₂ _).symm))
    (List.sorted_mergeSort' (· ≤ ·) l₁)
    (List.sorted_mergeSort' (· ≤ ·) l₂)

theorem mergeSort_map_of_monotone (data : List Int) (f : Int → Int) (hf : Monotone f) :
    (data.map f).mergeSort = data.mergeSort.map f := by
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact (List.mergeSort_perm (data.map f) _).trans ((List.mergeSort_perm data _).symm.map f)
  · exact List.sorted_mergeSort' (· ≤ ·) (data.map f)
  · rw [List.Sorted, List.pairwise_map]
    exact (List.sorted_mergeSort' (· ≤ ·) data).imp (@fun a b hab => hf hab)

theorem sorted_getElem_le_getElem (data : List Int) {i j : Nat}
    (hi : i < data.mergeSort.length) (hj : j < data.mergeSort.length) (hij : i ≤ j) :
    data.mergeSort[i]'hi ≤ data.mergeSort[j]'hj := by
  have hsort : List.Sorted (· ≤ ·) data.mergeSort := List.sorted_mergeSort' (· ≤ ·) data
  exact hsort.rel_get_of_le (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij

theorem median_low_eq_sorted_getElem (data : List Int) (h : Pre data) :
    ∃ (hlt : (data.length - 1) / 2 < data.mergeSort.length),
      median_low data = some (data.mergeSort[(data.length - 1) / 2]'hlt) := by
  have hlen : data.mergeSort.length = data.length := List.length_mergeSort data
  have hpos : 0 < data.length := List.length_pos_iff.mpr h
  have hlt : (data.length - 1) / 2 < data.mergeSort.length := by omega
  refine ⟨hlt, ?_⟩
  unfold median_low
  simp only [hlen]
  split_ifs with h0 hodd
  · rw [beq_iff_eq] at h0; omega
  · rw [beq_iff_eq] at hodd
    have hidx : data.length / 2 = (data.length - 1) / 2 := by omega
    simp [hidx, List.getElem?_eq_getElem hlt]
  · rw [beq_iff_eq] at hodd
    have hidx : data.length / 2 - 1 = (data.length - 1) / 2 := by omega
    simp [hidx, List.getElem?_eq_getElem hlt]

/-- Property 1: `median_low` returns `none` if and only if the input list is empty. -/
def empty_none_prop (data : List Int) : Prop :=
  data = [] ↔ median_low data = none

theorem empty_none_thm (data : List Int) : empty_none_prop data := by
  unfold empty_none_prop
  constructor
  · intro h
    subst h
    simp [median_low]
  · intro hnone
    by_contra hne
    obtain ⟨_, heq⟩ := median_low_eq_sorted_getElem data hne
    rw [heq] at hnone
    cases hnone

/-- Property 2: Under `Pre data`, `median_low data` always returns `some` value. -/
def nonempty_some_prop (data : List Int) : Prop :=
  Pre data → (median_low data).isSome = true

theorem nonempty_some_thm (data : List Int) : nonempty_some_prop data := by
  intro h
  obtain ⟨_, heq⟩ := median_low_eq_sorted_getElem data h
  simp [heq]

/-- Property 3: When `data.length` is odd, `median_low` returns the middle element `sorted[n / 2]`. -/
def odd_length_prop (data : List Int) : Prop :=
  Pre data → data.length % 2 = 1 → median_low data = data.mergeSort[data.length / 2]?

theorem odd_length_thm (data : List Int) : odd_length_prop data := by
  intro h hodd
  obtain ⟨hlt, heq⟩ := median_low_eq_sorted_getElem data h
  have hidx : data.length / 2 = (data.length - 1) / 2 := by omega
  rw [heq, hidx, List.getElem?_eq_getElem hlt]

/-- Property 4: When `data.length` is even and positive, `median_low` returns `sorted[n / 2 - 1]`. -/
def even_length_prop (data : List Int) : Prop :=
  Pre data → data.length % 2 = 0 → median_low data = data.mergeSort[data.length / 2 - 1]?

theorem even_length_thm (data : List Int) : even_length_prop data := by
  intro h heven
  have hpos : 0 < data.length := List.length_pos_iff.mpr h
  obtain ⟨hlt, heq⟩ := median_low_eq_sorted_getElem data h
  have hidx : data.length / 2 - 1 = (data.length - 1) / 2 := by omega
  rw [heq, hidx, List.getElem?_eq_getElem hlt]

/-- Property 5: When `data.length` is even and positive, the returned low median is less than or equal
    to the upper middle element `sorted[n / 2]` (the smaller of the two middle values is returned). -/
def even_smaller_middle_prop (data : List Int) : Prop :=
  Pre data → data.length % 2 = 0 →
    ∀ m hi, median_low data = some m → data.mergeSort[data.length / 2]? = some hi → m ≤ hi

theorem even_smaller_middle_thm (data : List Int) : even_smaller_middle_prop data := by
  intro h heven m hi hm hhi
  have hlen : data.mergeSort.length = data.length := List.length_mergeSort data
  have hpos : 0 < data.length := List.length_pos_iff.mpr h
  have hlt2 : data.length / 2 < data.mergeSort.length := by omega
  obtain ⟨hlt, heq⟩ := median_low_eq_sorted_getElem data h
  rw [heq, Option.some.injEq] at hm
  rw [List.getElem?_eq_getElem hlt2, Option.some.injEq] at hhi
  rw [← hm, ← hhi]
  exact sorted_getElem_le_getElem data hlt hlt2 (by omega)

/-- Property 6: Unified index characterization in the sorted data: `sorted[(n - 1) / 2]?`. -/
def sorted_index_prop (data : List Int) : Prop :=
  Pre data → median_low data = data.mergeSort[(data.length - 1) / 2]?

theorem sorted_index_thm (data : List Int) : sorted_index_prop data := by
  intro h
  obtain ⟨hlt, heq⟩ := median_low_eq_sorted_getElem data h
  rw [heq, List.getElem?_eq_getElem hlt]

/-- Property 7: The low median is always an element of the input list `data`. -/
def mem_prop (data : List Int) : Prop :=
  Pre data → ∀ m, median_low data = some m → m ∈ data

theorem mem_thm (data : List Int) : mem_prop data := by
  intro h m hm
  obtain ⟨hlt, heq⟩ := median_low_eq_sorted_getElem data h
  rw [heq, Option.some.injEq] at hm
  subst hm
  exact List.mem_mergeSort.mp (List.getElem_mem hlt)

/-- Property 8: Partition of the sorted list around the low median index `(n - 1) / 2`. -/
def partition_sorted_prop (data : List Int) : Prop :=
  Pre data → ∀ m, median_low data = some m →
    (∀ x ∈ data.mergeSort.take ((data.length - 1) / 2 + 1), x ≤ m) ∧
    (∀ x ∈ data.mergeSort.drop ((data.length - 1) / 2), m ≤ x)

theorem partition_sorted_thm (data : List Int) : partition_sorted_prop data := by
  intro h m hm
  obtain ⟨hlt, heq⟩ := median_low_eq_sorted_getElem data h
  rw [heq, Option.some.injEq] at hm
  have hlen : data.mergeSort.length = data.length := List.length_mergeSort data
  constructor
  · intro x hx
    rw [List.mem_take_iff_getElem] at hx
    rcases hx with ⟨i, hi, rfl⟩
    rw [← hm]
    exact sorted_getElem_le_getElem data (by omega) hlt (by omega)
  · intro x hx
    rw [List.mem_drop_iff_getElem] at hx
    rcases hx with ⟨i, hi, rfl⟩
    rw [← hm]
    exact sorted_getElem_le_getElem data hlt (by omega) (by omega)

/-- Property 9: Order-independent rank / quantile characterization of `median_low`:
    `m` is the low median of `data` iff at least `(n + 1) / 2` elements of `data` are `≤ m`
    and at least `n / 2 + 1` elements of `data` are `≥ m`. -/
def rank_counts_prop (data : List Int) : Prop :=
  Pre data → ∀ m, median_low data = some m ↔
    (data.length + 1) / 2 ≤ (data.filter (fun x => decide (x ≤ m))).length ∧
    data.length / 2 + 1 ≤ (data.filter (fun x => decide (m ≤ x))).length

theorem lower_half_count_lemma (data : List Int) (h : Pre data) :
    ∀ m, median_low data = some m →
      (data.length + 1) / 2 ≤ (data.filter (fun x => decide (x ≤ m))).length := by
  intro m hm
  obtain ⟨hlt, heq⟩ := median_low_eq_sorted_getElem data h
  rw [heq, Option.some.injEq] at hm
  have hlen : data.mergeSort.length = data.length := List.length_mergeSort data
  have hpos : 0 < data.length := List.length_pos_iff.mpr h
  let k := (data.length - 1) / 2
  let p : Int → Bool := fun x => decide (x ≤ m)
  have hperm : (data.mergeSort.filter p).Perm (data.filter p) :=
    (List.mergeSort_perm data _).filter p
  rw [← hperm.length_eq]
  have hfilter_take : (data.mergeSort.take (k + 1)).filter p = data.mergeSort.take (k + 1) := by
    rw [List.filter_eq_self]
    intro a ha
    rw [List.mem_take_iff_getElem] at ha
    rcases ha with ⟨i, hi, rfl⟩
    simp only [p, decide_eq_true_eq, ← hm]
    exact sorted_getElem_le_getElem data (by omega) hlt (by omega)
  have hsplit : data.mergeSort.filter p =
      (data.mergeSort.take (k + 1)).filter p ++ (data.mergeSort.drop (k + 1)).filter p := by
    rw [← List.filter_append, List.take_append_drop]
  have hlen_filter : (data.mergeSort.take (k + 1)).length ≤ (data.mergeSort.filter p).length := by
    rw [hsplit, hfilter_take, List.length_append]
    omega
  rw [List.length_take] at hlen_filter
  omega

theorem upper_half_count_lemma (data : List Int) (h : Pre data) :
    ∀ m, median_low data = some m →
      data.length / 2 + 1 ≤ (data.filter (fun x => decide (m ≤ x))).length := by
  intro m hm
  obtain ⟨hlt, heq⟩ := median_low_eq_sorted_getElem data h
  rw [heq, Option.some.injEq] at hm
  have hlen : data.mergeSort.length = data.length := List.length_mergeSort data
  have hpos : 0 < data.length := List.length_pos_iff.mpr h
  let k := (data.length - 1) / 2
  let p : Int → Bool := fun x => decide (m ≤ x)
  have hperm : (data.mergeSort.filter p).Perm (data.filter p) :=
    (List.mergeSort_perm data _).filter p
  rw [← hperm.length_eq]
  have hfilter_drop : (data.mergeSort.drop k).filter p = data.mergeSort.drop k := by
    rw [List.filter_eq_self]
    intro a ha
    rw [List.mem_drop_iff_getElem] at ha
    rcases ha with ⟨i, hi, rfl⟩
    simp only [p, decide_eq_true_eq, ← hm]
    exact sorted_getElem_le_getElem data hlt (by omega) (by omega)
  have hsplit : data.mergeSort.filter p =
      (data.mergeSort.take k).filter p ++ (data.mergeSort.drop k).filter p := by
    rw [← List.filter_append, List.take_append_drop]
  have hlen_filter : (data.mergeSort.drop k).length ≤ (data.mergeSort.filter p).length := by
    rw [hsplit, hfilter_drop, List.length_append]
    omega
  rw [List.length_drop] at hlen_filter
  omega

theorem rank_counts_thm (data : List Int) : rank_counts_prop data := by
  intro h m
  constructor
  · intro hm
    exact ⟨lower_half_count_lemma data h m hm, upper_half_count_lemma data h m hm⟩
  · rintro ⟨h_le, h_ge⟩
    obtain ⟨hlt, heq⟩ := median_low_eq_sorted_getElem data h
    rw [heq, Option.some.injEq]
    have hlen : data.mergeSort.length = data.length := List.length_mergeSort data
    have hpos : 0 < data.length := List.length_pos_iff.mpr h
    have h_sk_le_m : data.mergeSort[(data.length - 1) / 2]'hlt ≤ m := by
      by_contra hlt_m
      push_neg at hlt_m
      have hperm : (data.mergeSort.filter (fun x => decide (x ≤ m))).Perm
          (data.filter (fun x => decide (x ≤ m))) :=
        (List.mergeSort_perm data _).filter _
      have hfilter_drop :
          (data.mergeSort.drop ((data.length - 1) / 2)).filter (fun x => decide (x ≤ m)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        rw [List.mem_drop_iff_getElem] at ha
        rcases ha with ⟨i, hi, rfl⟩
        simp only [decide_eq_true_eq, not_le]
        exact lt_of_lt_of_le hlt_m (sorted_getElem_le_getElem data hlt (by omega) (by omega))
      have hsplit : data.mergeSort.filter (fun x => decide (x ≤ m)) =
          (data.mergeSort.take ((data.length - 1) / 2)).filter (fun x => decide (x ≤ m)) ++
          (data.mergeSort.drop ((data.length - 1) / 2)).filter (fun x => decide (x ≤ m)) := by
        rw [← List.filter_append, List.take_append_drop]
      have hlen_ub : (data.filter (fun x => decide (x ≤ m))).length ≤ (data.length - 1) / 2 := by
        rw [← hperm.length_eq, hsplit, hfilter_drop, List.append_nil]
        have htake := List.length_filter_le (fun x => decide (x ≤ m))
          (data.mergeSort.take ((data.length - 1) / 2))
        rw [List.length_take] at htake
        omega
      omega
    have h_m_le_sk : m ≤ data.mergeSort[(data.length - 1) / 2]'hlt := by
      by_contra hgt_m
      push_neg at hgt_m
      have hperm : (data.mergeSort.filter (fun x => decide (m ≤ x))).Perm
          (data.filter (fun x => decide (m ≤ x))) :=
        (List.mergeSort_perm data _).filter _
      have hfilter_take :
          (data.mergeSort.take ((data.length - 1) / 2 + 1)).filter (fun x => decide (m ≤ x)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        rw [List.mem_take_iff_getElem] at ha
        rcases ha with ⟨i, hi, rfl⟩
        simp only [decide_eq_true_eq, not_le]
        exact lt_of_le_of_lt (sorted_getElem_le_getElem data (by omega) hlt (by omega)) hgt_m
      have hsplit : data.mergeSort.filter (fun x => decide (m ≤ x)) =
          (data.mergeSort.take ((data.length - 1) / 2 + 1)).filter (fun x => decide (m ≤ x)) ++
          (data.mergeSort.drop ((data.length - 1) / 2 + 1)).filter (fun x => decide (m ≤ x)) := by
        rw [← List.filter_append, List.take_append_drop]
      have hlen_ub :
          (data.filter (fun x => decide (m ≤ x))).length ≤
            data.length - ((data.length - 1) / 2 + 1) := by
        rw [← hperm.length_eq, hsplit, hfilter_take, List.nil_append]
        have hdrop := List.length_filter_le (fun x => decide (m ≤ x))
          (data.mergeSort.drop ((data.length - 1) / 2 + 1))
        rw [List.length_drop] at hdrop
        omega
      omega
    exact le_antisymm h_sk_le_m h_m_le_sk

/-- Property 10: Any lower bound of `data` is `≤` the low median, and any upper bound is `≥` it. -/
def bounds_prop (data : List Int) : Prop :=
  Pre data → ∀ m, median_low data = some m →
    (∀ lo, (∀ x ∈ data, lo ≤ x) → lo ≤ m) ∧
    (∀ hi, (∀ x ∈ data, x ≤ hi) → m ≤ hi)

theorem bounds_thm (data : List Int) : bounds_prop data := by
  intro h m hm
  have hmem : m ∈ data := mem_thm data h m hm
  exact ⟨fun lo hlo => hlo m hmem, fun hi hhi => hhi m hmem⟩

/-- Property 11: `median_low` is invariant under arbitrary permutations of the input list. -/
def perm_invariant_prop (data₁ data₂ : List Int) : Prop :=
  data₁.Perm data₂ → median_low data₁ = median_low data₂

theorem perm_invariant_thm (data₁ data₂ : List Int) : perm_invariant_prop data₁ data₂ := by
  intro hperm
  have hsort : data₁.mergeSort = data₂.mergeSort := mergeSort_eq_of_perm hperm
  unfold median_low
  dsimp only
  rw [hsort]

/-- Property 12: Sorting the input before calling `median_low` leaves the result unchanged. -/
def sort_invariant_prop (data : List Int) : Prop :=
  median_low data.mergeSort = median_low data

theorem sort_invariant_thm (data : List Int) : sort_invariant_prop data := by
  unfold sort_invariant_prop
  exact perm_invariant_thm _ data (List.mergeSort_perm data _)

/-- Property 13: Reversing the input list leaves `median_low` unchanged. -/
def reverse_invariant_prop (data : List Int) : Prop :=
  median_low data.reverse = median_low data

theorem reverse_invariant_thm (data : List Int) : reverse_invariant_prop data :=
  perm_invariant_thm data.reverse data (List.reverse_perm data)

/-- Property 14: On a singleton list `[x]`, `median_low` returns `some x`. -/
def singleton_prop (x : Int) : Prop :=
  median_low [x] = some x

theorem singleton_thm (x : Int) : singleton_prop x := by
  unfold singleton_prop
  have h : Pre [x] := List.cons_ne_nil x []
  rw [rank_counts_thm [x] h x]
  simp

/-- Property 15: On a two-element list `[x, y]`, `median_low` returns `some (min x y)`. -/
def pair_prop (x y : Int) : Prop :=
  median_low [x, y] = some (min x y)

theorem pair_thm (x y : Int) : pair_prop x y := by
  unfold pair_prop
  have h : Pre [x, y] := List.cons_ne_nil x [y]
  rw [rank_counts_thm [x, y] h (min x y)]
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy]
    simp [hxy]
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [min_eq_right hyx]
    simp [hxy, hyx]

/-- Property 16: If all elements of a non-empty list equal `c`, `median_low` returns `some c`. -/
def const_prop (data : List Int) (c : Int) : Prop :=
  Pre data → (∀ x ∈ data, x = c) → median_low data = some c

theorem const_thm (data : List Int) (c : Int) : const_prop data c := by
  intro h hconst
  obtain ⟨hlt, heq⟩ := median_low_eq_sorted_getElem data h
  rw [heq, Option.some.injEq]
  exact hconst _ (List.mem_mergeSort.mp (List.getElem_mem hlt))

/-- Property 17: On `List.replicate n x` for `n > 0`, `median_low` returns `some x`. -/
def replicate_prop (n : Nat) (x : Int) : Prop :=
  0 < n → median_low (List.replicate n x) = some x

theorem replicate_thm (n : Nat) (x : Int) : replicate_prop n x := by
  intro hn
  have hpre : Pre (List.replicate n x) := by
    simp [Pre]
    omega
  exact const_thm (List.replicate n x) x hpre (fun _ hy => List.eq_of_mem_replicate hy)

/-- Property 18: Monotone map equivariance: applying any monotone `f : Int → Int`
    commutes with `median_low`. -/
def monotone_map_prop (data : List Int) (f : Int → Int) : Prop :=
  Monotone f → median_low (data.map f) = (median_low data).map f

theorem monotone_map_thm (data : List Int) (f : Int → Int) : monotone_map_prop data f := by
  intro hf
  unfold median_low
  dsimp only
  rw [mergeSort_map_of_monotone data f hf, List.length_map]
  split_ifs <;> simp

/-- Property 19: Translation equivariance: shifting every element by `c` shifts `median_low` by `c`. -/
def shift_prop (data : List Int) (c : Int) : Prop :=
  median_low (data.map (· + c)) = (median_low data).map (· + c)

theorem shift_thm (data : List Int) (c : Int) : shift_prop data c :=
  monotone_map_thm data (· + c) (fun _ _ hab => Int.add_le_add_right hab c)

/-- Property 20: Non-negative scaling equivariance: scaling every element by `c ≥ 0`
    scales `median_low` by `c`. -/
def scale_nonneg_prop (data : List Int) (c : Int) : Prop :=
  0 ≤ c → median_low (data.map (c * ·)) = (median_low data).map (c * ·)

theorem scale_nonneg_thm (data : List Int) (c : Int) : scale_nonneg_prop data c := by
  intro hc
  exact monotone_map_thm data (c * ·) (fun _ _ hab => Int.mul_le_mul_of_nonneg_left hab hc)

/-! ## 5. Post-condition -/

/-- Post-condition for `median_low` (and `benchmark_median_low`) as a conjunction of its properties. -/
def Post_prop (data : List Int) : Prop :=
  (median_low data).isSome = true ∧
  (data.length % 2 = 1 → median_low data = data.mergeSort[data.length / 2]?) ∧
  (data.length % 2 = 0 → median_low data = data.mergeSort[data.length / 2 - 1]?) ∧
  (data.length % 2 = 0 → ∀ m hi, median_low data = some m →
    data.mergeSort[data.length / 2]? = some hi → m ≤ hi) ∧
  median_low data = data.mergeSort[(data.length - 1) / 2]? ∧
  (∀ m, median_low data = some m → m ∈ data) ∧
  (∀ m, median_low data = some m →
    (∀ x ∈ data.mergeSort.take ((data.length - 1) / 2 + 1), x ≤ m) ∧
    (∀ x ∈ data.mergeSort.drop ((data.length - 1) / 2), m ≤ x)) ∧
  (∀ m, median_low data = some m ↔
    (data.length + 1) / 2 ≤ (data.filter (fun x => decide (x ≤ m))).length ∧
    data.length / 2 + 1 ≤ (data.filter (fun x => decide (m ≤ x))).length) ∧
  (∀ m, median_low data = some m →
    (∀ lo, (∀ x ∈ data, lo ≤ x) → lo ≤ m) ∧
    (∀ hi, (∀ x ∈ data, x ≤ hi) → m ≤ hi)) ∧
  median_low data.mergeSort = median_low data ∧
  median_low data.reverse = median_low data ∧
  (∀ c : Int, median_low (data.map (· + c)) = (median_low data).map (· + c))

/-! ## 6. Property-Based Tests -/

-- PBT for `empty_none_prop`
#eval Plausible.Testable.check
  (∀ data : List Int, (data == []) = (median_low data == none))

-- PBT for `nonempty_some_prop`
#eval Plausible.Testable.check
  (∀ x : Int, ∀ xs : List Int, (median_low (x :: xs)).isSome = true)

-- PBT for `odd_length_prop` (randomized + bounded)
#eval Plausible.Testable.check
  (∀ x : Int, ∀ xs : List Int,
    let data := if (x :: xs).length % 2 == 1 then x :: xs else x :: x :: xs
    median_low data = data.mergeSort[data.length / 2]?)

example : (List.range 15).all (fun k =>
  let n := 2 * k + 1
  let data := ((List.range n).map (fun i => Int.ofNat ((i * 7 + 3) % 23)))
  median_low data == data.mergeSort[n / 2]?) = true := by native_decide

-- PBT for `even_length_prop` (randomized + bounded)
#eval Plausible.Testable.check
  (∀ x y : Int, ∀ xs : List Int,
    let data := if (x :: y :: xs).length % 2 == 0 then x :: y :: xs else x :: x :: y :: xs
    median_low data = data.mergeSort[data.length / 2 - 1]?)

example : (List.range 15).all (fun k =>
  let n := 2 * (k + 1)
  let data := ((List.range n).map (fun i => Int.ofNat ((i * 11 + 5) % 29)))
  median_low data == data.mergeSort[n / 2 - 1]?) = true := by native_decide

-- PBT for `even_smaller_middle_prop` (randomized + bounded)
#eval Plausible.Testable.check
  (∀ x y : Int, ∀ xs : List Int,
    let data := if (x :: y :: xs).length % 2 == 0 then x :: y :: xs else x :: x :: y :: xs
    (match median_low data, data.mergeSort[data.length / 2]? with
     | some m, some hi => decide (m ≤ hi)
     | _, _ => false) = true)

example : (List.range 15).all (fun k =>
  let n := 2 * (k + 1)
  let data := ((List.range n).map (fun i => Int.ofNat ((i * 13 + 2) % 31)))
  match median_low data, data.mergeSort[n / 2]? with
  | some m, some hi => decide (m ≤ hi)
  | _, _ => false) = true := by native_decide

-- PBT for `sorted_index_prop`
#eval Plausible.Testable.check
  (∀ x : Int, ∀ xs : List Int,
    let data := x :: xs
    median_low data = data.mergeSort[(data.length - 1) / 2]?)

-- PBT for `mem_prop`
#eval Plausible.Testable.check
  (∀ x : Int, ∀ xs : List Int,
    let data := x :: xs
    (match median_low data with
     | some m => decide (m ∈ data)
     | none => false) = true)

-- PBT for `partition_sorted_prop`
#eval Plausible.Testable.check
  (∀ x : Int, ∀ xs : List Int,
    let data := x :: xs
    (match median_low data with
     | some m =>
       (data.mergeSort.take ((data.length - 1) / 2 + 1)).all (fun z => decide (z ≤ m)) &&
       (data.mergeSort.drop ((data.length - 1) / 2)).all (fun z => decide (m ≤ z))
     | none => false) = true)

-- PBT for `rank_counts_prop`
#eval Plausible.Testable.check
  (∀ x : Int, ∀ xs : List Int,
    let data := x :: xs
    (match median_low data with
     | some m =>
       decide ((data.length + 1) / 2 ≤ (data.filter (fun z => decide (z ≤ m))).length) &&
       decide (data.length / 2 + 1 ≤ (data.filter (fun z => decide (m ≤ z))).length)
     | none => false) = true)

-- PBT for `bounds_prop`
#eval Plausible.Testable.check
  (∀ x : Int, ∀ xs : List Int,
    let data := x :: xs
    let lo := data.foldl min x
    let hi := data.foldl max x
    (match median_low data with
     | some m => decide (lo ≤ m ∧ m ≤ hi)
     | none => false) = true)

-- PBT for `perm_invariant_prop`
#eval Plausible.Testable.check
  (∀ data : List Int,
    ((data.take 5).permutations.all (fun p => median_low p == median_low (data.take 5))) = true)

-- PBT for `sort_invariant_prop`
#eval Plausible.Testable.check
  (∀ data : List Int, median_low data.mergeSort = median_low data)

-- PBT for `reverse_invariant_prop`
#eval Plausible.Testable.check
  (∀ data : List Int, median_low data.reverse = median_low data)

-- PBT for `singleton_prop`
#eval Plausible.Testable.check
  (∀ x : Int, median_low [x] = some x)

-- PBT for `pair_prop`
#eval Plausible.Testable.check
  (∀ x y : Int, median_low [x, y] = some (min x y))

-- PBT for `const_prop` and `replicate_prop`
#eval Plausible.Testable.check
  (∀ n : Nat, ∀ x : Int,
    let k := n % 30 + 1
    median_low (List.replicate k x) = some x)

example : (List.range 20).all (fun n =>
  median_low (List.replicate (n + 1) (-7)) == some (-7)) = true := by native_decide

-- PBT for `monotone_map_prop`, `shift_prop`, and `scale_nonneg_prop`
#eval Plausible.Testable.check
  (∀ data : List Int, ∀ c : Int,
    median_low (data.map (· + c)) = (median_low data).map (· + c))

#eval Plausible.Testable.check
  (∀ data : List Int, ∀ k : Nat,
    let c : Int := Int.ofNat k
    median_low (data.map (c * ·)) = (median_low data).map (c * ·))

-- PBT for `Post_prop` (executable Boolean counterpart on non-empty inputs)
def check_post (data : List Int) : Bool :=
  match median_low data with
  | none => false
  | some m =>
    let s := data.mergeSort
    let n := data.length
    (if n % 2 == 1 then some m == s[n / 2]? else some m == s[n / 2 - 1]?) &&
    (if n % 2 == 0 then match s[n / 2]? with | some hi => decide (m ≤ hi) | none => false else true) &&
    (some m == s[(n - 1) / 2]?) &&
    decide (m ∈ data) &&
    (s.take ((n - 1) / 2 + 1)).all (fun x => decide (x ≤ m)) &&
    (s.drop ((n - 1) / 2)).all (fun x => decide (m ≤ x)) &&
    decide ((n + 1) / 2 ≤ (data.filter (fun x => decide (x ≤ m))).length) &&
    decide (n / 2 + 1 ≤ (data.filter (fun x => decide (m ≤ x))).length) &&
    (median_low s == some m) &&
    (median_low data.reverse == some m) &&
    (median_low (data.map (· + 5)) == some (m + 5))

#eval Plausible.Testable.check
  (∀ x : Int, ∀ xs : List Int, check_post (x :: xs) = true)

example : (List.range 25).all (fun n =>
  let data := (List.range (n + 1)).map (fun i => Int.ofNat ((i * 9 + 4) % 17) - 8)
  check_post data && check_post data.reverse) = true := by native_decide

/-! ## 7. Correctness Theorem (`Pre → Post`) -/

theorem median_low_correct (data : List Int) (h : Pre data) : Post_prop data :=
  ⟨nonempty_some_thm data h,
   odd_length_thm data h,
   even_length_thm data h,
   even_smaller_middle_thm data h,
   sorted_index_thm data h,
   mem_thm data h,
   partition_sorted_thm data h,
   rank_counts_thm data h,
   bounds_thm data h,
   sort_invariant_thm data,
   reverse_invariant_thm data,
   shift_thm data⟩

theorem benchmark_median_low_correct (data : List Int) (h : Pre data) : Post_prop data :=
  median_low_correct data h

/-! ## 8. Imperative Implementation -/

/-- Imperative implementation of `median_low` using `Id.run do` and mutable state,
    mirroring the Python implementation. -/
def median_low_imp (data : List Int) : Option Int := Id.run do
  let mut sorted := data.mergeSort
  let n := sorted.length
  if n == 0 then
    return none
  let mut result : Option Int := none
  if n % 2 == 1 then
    result := sorted[n / 2]?
  else
    result := sorted[n / 2 - 1]?
  return result

/-- Imperative implementation of `benchmark_median_low` using `Id.run do` and mutable state. -/
def benchmark_median_low_imp (data : List Int) : Option Int := Id.run do
  if !pre_check data then
    return none
  let mut sorted := data.mergeSort
  let n := sorted.length
  if n == 0 then
    return none
  let mut result : Option Int := none
  if n % 2 == 1 then
    result := sorted[n / 2]?
  else
    result := sorted[n / 2 - 1]?
  return result

/-! ## 9. Imperative Tests -/

example : median_low_imp [1, 3, 5] = some 3 := by native_decide
example : median_low_imp [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide
example : median_low_imp [1, 3, 5, 7] = some 3 := by native_decide
example : median_low_imp [1, 2, 3, 4, 5, 6] = some 3 := by native_decide
example : median_low_imp [42] = some 42 := by native_decide
example : median_low_imp [10, 20] = some 10 := by native_decide
example : median_low_imp [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide
example : median_low_imp [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : median_low_imp [-10, -5, 5, 10] = some (-5) := by native_decide
example : median_low_imp [] = none := by native_decide

example : benchmark_median_low_imp [1, 3, 5] = some 3 := by native_decide
example : benchmark_median_low_imp [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide
example : benchmark_median_low_imp [1, 3, 5, 7] = some 3 := by native_decide
example : benchmark_median_low_imp [1, 2, 3, 4, 5, 6] = some 3 := by native_decide
example : benchmark_median_low_imp [42] = some 42 := by native_decide
example : benchmark_median_low_imp [10, 20] = some 10 := by native_decide
example : benchmark_median_low_imp [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide
example : benchmark_median_low_imp [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : benchmark_median_low_imp [-10, -5, 5, 10] = some (-5) := by native_decide
example : benchmark_median_low_imp [] = none := by native_decide

#eval median_low_imp [1, 3, 5]
#eval median_low_imp [1, 3, 5, 7]
#eval median_low_imp [9, 1, 6, 2, 5, 4, 3]
#eval median_low_imp [-10, -5, 5, 10]
#eval median_low_imp []

-- PBT for functional-imperative equivalence
#eval Plausible.Testable.check
  (∀ data : List Int, median_low data = median_low_imp data)

#eval Plausible.Testable.check
  (∀ data : List Int, benchmark_median_low data = benchmark_median_low_imp data)

/-! ## 10. Equivalence Theorem: Functional = Imperative -/

theorem median_low_equiv (data : List Int) :
    median_low data = median_low_imp data := by
  simp only [median_low, median_low_imp, Id.run, bind, pure]

theorem benchmark_median_low_equiv (data : List Int) :
    benchmark_median_low data = benchmark_median_low_imp data := by
  simp only [benchmark_median_low, median_low, benchmark_median_low_imp, Id.run, bind, pure]

end «28_statistics_median_low»
