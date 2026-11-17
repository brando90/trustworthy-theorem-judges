import Mathlib

/-!
# Low Median of Numeric Data (`statistics.median_low`)

Formalization and verification of Python's `statistics.median_low` function in Lean 4.

When the number of data points is odd, the middle value of the sorted data is returned.
When the number of data points is even, the smaller of the two middle values is returned.
When the input list is empty, `none` is returned (representing `StatisticsError`).
-/

namespace «28_statistics_median_low»

-- ============================================================================
-- 4. Implementation (functional definition)
-- ============================================================================

/-- Executable Boolean pre-condition: `true` iff `data` is non-empty. -/
@[reducible]
def pre (data : List Int) : Bool :=
  !data.isEmpty

/-- Return the low median of numeric data.
    When the number of data points is odd, the middle value is returned.
    When it is even, the smaller of the two middle values is returned.
    Returns `none` for empty data (modeling `StatisticsError`). -/
def median_low (data : List Int) : Option Int :=
  let sorted := data.mergeSort (· ≤ ·)
  let n := sorted.length
  if n = 0 then
    none
  else if n % 2 = 1 then
    sorted[n / 2]?
  else
    sorted[n / 2 - 1]?

/-- Main function to be verified: checks `pre` and returns the low median of `data`,
    or `none` (modeling `StatisticsError`) if `pre data` fails. -/
def benchmark_median_low (data : List Int) : Option Int :=
  if !pre data then
    none
  else
    median_low data

-- ============================================================================
-- 5. Unit tests
-- ============================================================================

-- 1. Odd number of elements (returns middle value)
example : benchmark_median_low [1, 3, 5] = some 3 := by native_decide
example : benchmark_median_low [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide

-- 2. Even number of elements (returns smaller of two middle values)
example : benchmark_median_low [1, 3, 5, 7] = some 3 := by native_decide
example : benchmark_median_low [1, 2, 3, 4, 5, 6] = some 3 := by native_decide

-- 3. Single value
example : benchmark_median_low [42] = some 42 := by native_decide

-- 4. Two values
example : benchmark_median_low [10, 20] = some 10 := by native_decide

-- 5. Unsorted input
example : benchmark_median_low [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide

-- 6. Negative values
example : benchmark_median_low [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : benchmark_median_low [-10, -5, 5, 10] = some (-5) := by native_decide

-- 7. Error cases (empty list raises StatisticsError / returns none)
example : benchmark_median_low [] = none := by native_decide
example : median_low [] = none := by native_decide

#eval benchmark_median_low [1, 3, 5]
#eval benchmark_median_low [1, 2, 3, 4, 5, 6, 9]
#eval benchmark_median_low [1, 3, 5, 7]
#eval benchmark_median_low [1, 2, 3, 4, 5, 6]
#eval benchmark_median_low [42]
#eval benchmark_median_low [10, 20]
#eval benchmark_median_low [9, 1, 6, 2, 5, 4, 3]
#eval benchmark_median_low [-5, -1, 0, 3, 7]
#eval benchmark_median_low [-10, -5, 5, 10]
#eval benchmark_median_low []

-- ============================================================================
-- 6. Pre-condition predicate (`def Pre`)
-- ============================================================================

/-- Pre-condition proposition: `data` is a non-empty list of integers. -/
@[reducible]
def Pre (data : List Int) : Prop :=
  data ≠ []

theorem pre_iff_Pre (data : List Int) : pre data = true ↔ Pre data := by
  simp [pre, Pre]

-- ============================================================================
-- 7. Property propositions (`def <name>_prop`) and theorems (`theorem <name>_thm`)
-- ============================================================================

/-! ### Helper Lemmas for Sorting and Order Statistics -/

/-- Decidable instance for bounded option universal quantification `∀ m, o = some m → P m`. -/
instance instDecidableForallOptionSome {α : Type*} {o : Option α} {P : α → Prop}
    [DecidablePred P] : Decidable (∀ m, o = some m → P m) :=
  match o with
  | none => isTrue (by intro m h; cases h)
  | some x =>
    if hx : P x then
      isTrue (by intro m h; cases h; exact hx)
    else
      isFalse (by intro h; exact hx (h x rfl))

theorem benchmark_eq_median_low (data : List Int) :
    benchmark_median_low data = median_low data := by
  unfold benchmark_median_low median_low pre
  cases data <;> simp

lemma pairwise_mergeSort_int (l : List Int) :
    List.Pairwise (· ≤ ·) (l.mergeSort (· ≤ ·)) := by
  have h := List.sorted_mergeSort (le := fun a b : Int => decide (a ≤ b))
    (by intro a b c; simp; omega)
    (by intro a b; simp; omega)
    l
  simpa using h

lemma mergeSort_eq_of_perm {l₁ l₂ : List Int} (h : l₁.Perm l₂) :
    l₁.mergeSort (· ≤ ·) = l₂.mergeSort (· ≤ ·) := by
  apply List.Perm.eq_of_sorted (le := (· ≤ ·))
  · intro a b _ _ hab hba; omega
  · exact pairwise_mergeSort_int l₁
  · exact pairwise_mergeSort_int l₂
  · exact (List.mergeSort_perm l₁ _).trans (h.trans (List.mergeSort_perm l₂ _).symm)

lemma mergeSort_eq_self_of_sorted {l : List Int} (hs : List.Pairwise (· ≤ ·) l) :
    l.mergeSort (· ≤ ·) = l := by
  apply List.Perm.eq_of_sorted (le := (· ≤ ·))
  · intro a b _ _ hab hba; omega
  · exact pairwise_mergeSort_int l
  · exact hs
  · exact List.mergeSort_perm l _

lemma mergeSort_map_of_monotone (l : List Int) (f : Int → Int) (hf : Monotone f) :
    (l.map f).mergeSort (· ≤ ·) = (l.mergeSort (· ≤ ·)).map f := by
  apply List.Perm.eq_of_sorted (le := (· ≤ ·))
  · intro a b _ _ hab hba; omega
  · exact pairwise_mergeSort_int (l.map f)
  · exact (pairwise_mergeSort_int l).map f (fun a b hab => hf hab)
  · exact (List.mergeSort_perm (l.map f) _).trans ((List.mergeSort_perm l _).symm.map f)

lemma sorted_getElem_mono {l : List Int} (hs : List.Pairwise (· ≤ ·) l)
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    l[i] ≤ l[j] := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact (List.pairwise_iff_getElem.mp hs) i j hi hj hlt

lemma countP_le_of_sorted {l : List Int} (hs : List.Pairwise (· ≤ ·) l)
    {k : Nat} (hk : k < l.length) :
    k + 1 ≤ l.countP (fun x => decide (x ≤ l[k])) := by
  have hsplit : l = l.take (k + 1) ++ l.drop (k + 1) := (List.take_append_drop (k + 1) l).symm
  have hcount : l.countP (fun x => decide (x ≤ l[k])) =
      (l.take (k + 1)).countP (fun x => decide (x ≤ l[k])) +
      (l.drop (k + 1)).countP (fun x => decide (x ≤ l[k])) :=
    (congrArg (List.countP (fun x => decide (x ≤ l[k]))) hsplit).trans List.countP_append
  have htake_all : (l.take (k + 1)).countP (fun x => decide (x ≤ l[k])) = (l.take (k + 1)).length := by
    rw [List.countP_eq_length]
    intro x hx
    rw [List.mem_iff_getElem] at hx
    rcases hx with ⟨i, hi, rfl⟩
    simp only [List.length_take] at hi
    rw [List.getElem_take]
    simp only [decide_eq_true_eq]
    exact sorted_getElem_mono hs (by omega) hk (by omega)
  have hlen : (l.take (k + 1)).length = k + 1 := by simp; omega
  omega

lemma countP_ge_of_sorted {l : List Int} (hs : List.Pairwise (· ≤ ·) l)
    {k : Nat} (hk : k < l.length) :
    l.length - k ≤ l.countP (fun x => decide (l[k] ≤ x)) := by
  have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  have hcount : l.countP (fun x => decide (l[k] ≤ x)) =
      (l.take k).countP (fun x => decide (l[k] ≤ x)) +
      (l.drop k).countP (fun x => decide (l[k] ≤ x)) :=
    (congrArg (List.countP (fun x => decide (l[k] ≤ x))) hsplit).trans List.countP_append
  have hdrop_all : (l.drop k).countP (fun x => decide (l[k] ≤ x)) = (l.drop k).length := by
    rw [List.countP_eq_length]
    intro x hx
    rw [List.mem_iff_getElem] at hx
    rcases hx with ⟨i, hi, rfl⟩
    simp only [List.length_drop] at hi
    rw [List.getElem_drop]
    simp only [decide_eq_true_eq]
    exact sorted_getElem_mono hs hk (by omega) (by omega)
  have hlen : (l.drop k).length = l.length - k := by simp
  omega

/-! ### Named Properties and Theorems -/

/-- Property 1: On empty input, both `benchmark_median_low` and `median_low` return `none`. -/
@[reducible]
def empty_none_prop (data : List Int) : Prop :=
  data = [] → benchmark_median_low data = none ∧ median_low data = none

theorem empty_none_thm (data : List Int) : empty_none_prop data := by
  intro h
  subst h
  simp [benchmark_median_low, median_low, pre]

/-- Property 2: For non-empty input, `benchmark_median_low` returns the element at index
    `(data.length - 1) / 2` of the sorted list. -/
@[reducible]
def unified_index_prop (data : List Int) : Prop :=
  let sorted := data.mergeSort (· ≤ ·)
  benchmark_median_low data = sorted[(data.length - 1) / 2]?

theorem unified_index_thm (data : List Int) (h : Pre data) :
    unified_index_prop data := by
  unfold unified_index_prop
  rw [benchmark_eq_median_low]
  unfold median_low
  dsimp only
  have hlen_eq : (data.mergeSort (· ≤ ·)).length = data.length := List.length_mergeSort data
  have hpos : 0 < data.length := List.length_pos_of_ne_nil h
  rw [hlen_eq]
  split_ifs with h0 hodd
  · omega
  · congr 1; omega
  · congr 1; omega

/-- Property 3: For non-empty input, `benchmark_median_low` always succeeds (`isSome = true`)
    and agrees with `median_low`. -/
@[reducible]
def nonempty_isSome_prop (data : List Int) : Prop :=
  (benchmark_median_low data).isSome = true ∧ benchmark_median_low data = median_low data

theorem nonempty_isSome_thm (data : List Int) (h : Pre data) :
    nonempty_isSome_prop data := by
  refine ⟨?_, benchmark_eq_median_low data⟩
  rw [unified_index_thm data h]
  have hpos : 0 < data.length := List.length_pos_of_ne_nil h
  have hlen_eq : (data.mergeSort (· ≤ ·)).length = data.length := List.length_mergeSort data
  have hlt : (data.length - 1) / 2 < (data.mergeSort (· ≤ ·)).length := by omega
  rw [List.getElem?_eq_getElem hlt]
  rfl

/-- Property 4: When the number of data points is odd, the middle value `sorted[n / 2]` is returned. -/
@[reducible]
def odd_length_prop (data : List Int) : Prop :=
  let sorted := data.mergeSort (· ≤ ·)
  data.length % 2 = 1 →
    benchmark_median_low data = sorted[data.length / 2]?

theorem odd_length_thm (data : List Int) (h : Pre data) :
    odd_length_prop data := by
  intro hodd
  rw [unified_index_thm data h]
  congr 1
  omega

/-- Property 5: When the number of data points is even, the lower middle value `sorted[n / 2 - 1]`
    is returned, and it is less than or equal to the upper middle value `sorted[n / 2]`. -/
@[reducible]
def even_length_prop (data : List Int) : Prop :=
  let sorted := data.mergeSort (· ≤ ·)
  data.length % 2 = 0 →
    benchmark_median_low data = sorted[data.length / 2 - 1]? ∧
    (∀ m, benchmark_median_low data = some m → ∀ u, sorted[data.length / 2]? = some u → m ≤ u)

theorem even_length_thm (data : List Int) (h : Pre data) :
    even_length_prop data := by
  intro heven
  have hpos : 0 < data.length := List.length_pos_of_ne_nil h
  have hlen_eq : (data.mergeSort (· ≤ ·)).length = data.length := List.length_mergeSort data
  have hidx : (data.length - 1) / 2 = data.length / 2 - 1 := by omega
  have heq : benchmark_median_low data = (data.mergeSort (· ≤ ·))[data.length / 2 - 1]? := by
    rw [unified_index_thm data h, hidx]
  refine ⟨heq, ?_⟩
  intro m hm u hu
  rw [heq] at hm
  have hlt1 : data.length / 2 - 1 < (data.mergeSort (· ≤ ·)).length := by omega
  have hlt2 : data.length / 2 < (data.mergeSort (· ≤ ·)).length := by omega
  rw [List.getElem?_eq_getElem hlt1, Option.some.injEq] at hm
  rw [List.getElem?_eq_getElem hlt2, Option.some.injEq] at hu
  subst hm hu
  exact sorted_getElem_mono (pairwise_mergeSort_int data) hlt1 hlt2 (by omega)

/-- Property 6: The returned low median is always an element of the original input list `data`. -/
@[reducible]
def mem_prop (data : List Int) : Prop :=
  ∀ m, benchmark_median_low data = some m → m ∈ data

theorem mem_thm (data : List Int) (h : Pre data) :
    mem_prop data := by
  intro m hm
  rw [unified_index_thm data h] at hm
  have hmem_sorted : m ∈ data.mergeSort (· ≤ ·) := List.mem_of_getElem? hm
  exact (List.mergeSort_perm data _).subset hmem_sorted

/-- Property 7: At least `(data.length + 1) / 2` elements in `data` are `≤` the low median `m`. -/
@[reducible]
def lower_half_prop (data : List Int) : Prop :=
  ∀ m, benchmark_median_low data = some m →
    (data.length + 1) / 2 ≤ data.countP (fun x => decide (x ≤ m))

theorem lower_half_thm (data : List Int) (h : Pre data) :
    lower_half_prop data := by
  intro m hm
  rw [unified_index_thm data h] at hm
  have hpos : 0 < data.length := List.length_pos_of_ne_nil h
  have hlen_eq : (data.mergeSort (· ≤ ·)).length = data.length := List.length_mergeSort data
  have hk : (data.length - 1) / 2 < (data.mergeSort (· ≤ ·)).length := by omega
  rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hm
  subst hm
  have hperm_count : data.countP (fun x => decide (x ≤ (data.mergeSort (· ≤ ·))[(data.length - 1) / 2])) =
      (data.mergeSort (· ≤ ·)).countP (fun x => decide (x ≤ (data.mergeSort (· ≤ ·))[(data.length - 1) / 2])) :=
    (List.mergeSort_perm data _).symm.countP_eq _
  rw [hperm_count]
  have hle := countP_le_of_sorted (pairwise_mergeSort_int data) hk
  omega

/-- Property 8: At least `data.length / 2 + 1` elements in `data` are `≥` the low median `m`. -/
@[reducible]
def upper_half_prop (data : List Int) : Prop :=
  ∀ m, benchmark_median_low data = some m →
    data.length / 2 + 1 ≤ data.countP (fun x => decide (m ≤ x))

theorem upper_half_thm (data : List Int) (h : Pre data) :
    upper_half_prop data := by
  intro m hm
  rw [unified_index_thm data h] at hm
  have hpos : 0 < data.length := List.length_pos_of_ne_nil h
  have hlen_eq : (data.mergeSort (· ≤ ·)).length = data.length := List.length_mergeSort data
  have hk : (data.length - 1) / 2 < (data.mergeSort (· ≤ ·)).length := by omega
  rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hm
  subst hm
  have hperm_count : data.countP (fun x => decide ((data.mergeSort (· ≤ ·))[(data.length - 1) / 2] ≤ x)) =
      (data.mergeSort (· ≤ ·)).countP (fun x => decide ((data.mergeSort (· ≤ ·))[(data.length - 1) / 2] ≤ x)) :=
    (List.mergeSort_perm data _).symm.countP_eq _
  rw [hperm_count]
  have hge := countP_ge_of_sorted (pairwise_mergeSort_int data) hk
  omega

/-- Property 9: The low median is bounded below by the minimum (first sorted element)
    and bounded above by the maximum (last sorted element) of `data`. -/
@[reducible]
def bounds_prop (data : List Int) : Prop :=
  let sorted := data.mergeSort (· ≤ ·)
  ∀ m, benchmark_median_low data = some m →
    (∀ a, sorted[0]? = some a → a ≤ m) ∧
    (∀ b, sorted[data.length - 1]? = some b → m ≤ b)

theorem bounds_thm (data : List Int) (h : Pre data) :
    bounds_prop data := by
  intro m hm
  rw [unified_index_thm data h] at hm
  have hpos : 0 < data.length := List.length_pos_of_ne_nil h
  have hlen_eq : (data.mergeSort (· ≤ ·)).length = data.length := List.length_mergeSort data
  have hk : (data.length - 1) / 2 < (data.mergeSort (· ≤ ·)).length := by omega
  have h0 : 0 < (data.mergeSort (· ≤ ·)).length := by omega
  have hlast : data.length - 1 < (data.mergeSort (· ≤ ·)).length := by omega
  rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hm
  subst hm
  refine ⟨?_, ?_⟩
  · intro a ha
    rw [List.getElem?_eq_getElem h0, Option.some.injEq] at ha
    subst ha
    exact sorted_getElem_mono (pairwise_mergeSort_int data) h0 hk (by omega)
  · intro b hb
    rw [List.getElem?_eq_getElem hlast, Option.some.injEq] at hb
    subst hb
    exact sorted_getElem_mono (pairwise_mergeSort_int data) hk hlast (by omega)

/-- Property 10: Sorting the input before calling `benchmark_median_low` leaves the result unchanged. -/
@[reducible]
def sorted_idempotent_prop (data : List Int) : Prop :=
  benchmark_median_low (data.mergeSort (· ≤ ·)) = benchmark_median_low data

theorem sorted_idempotent_thm (data : List Int) :
    sorted_idempotent_prop data := by
  unfold sorted_idempotent_prop
  rw [benchmark_eq_median_low, benchmark_eq_median_low]
  unfold median_low
  rw [mergeSort_eq_self_of_sorted (pairwise_mergeSort_int data)]

/-- Property 11: `benchmark_median_low` is invariant under list permutations. -/
@[reducible]
def perm_invariant_prop (data₁ data₂ : List Int) : Prop :=
  data₁.Perm data₂ → benchmark_median_low data₁ = benchmark_median_low data₂

theorem perm_invariant_thm (data₁ data₂ : List Int) :
    perm_invariant_prop data₁ data₂ := by
  intro hperm
  rw [benchmark_eq_median_low, benchmark_eq_median_low]
  unfold median_low
  rw [mergeSort_eq_of_perm hperm]

/-- Property 12: On a single-element list `[x]`, `benchmark_median_low` returns `some x`. -/
@[reducible]
def singleton_prop (x : Int) : Prop :=
  benchmark_median_low [x] = some x

theorem singleton_thm (x : Int) : singleton_prop x := by
  simp [singleton_prop, benchmark_median_low, median_low, pre]

/-- Property 13: On a two-element list `[x, y]`, `benchmark_median_low` returns `some (min x y)`. -/
@[reducible]
def pair_prop (x y : Int) : Prop :=
  benchmark_median_low [x, y] = some (min x y)

theorem pair_thm (x y : Int) : pair_prop x y := by
  unfold pair_prop benchmark_median_low median_low pre
  simp only [List.isEmpty_cons, Bool.not_false, Bool.not_true]
  change (let sorted := [x, y].mergeSort (fun a b : Int => decide (a ≤ b));
    let n := sorted.length;
    if n = 0 then none else if n % 2 = 1 then sorted[n / 2]? else sorted[n / 2 - 1]?) = some (min x y)
  by_cases hxy : x ≤ y
  · have hd : decide (x ≤ y) = true := decide_eq_true hxy
    simp [List.mergeSort, hd, min_eq_left hxy]
  · have hd : decide (x ≤ y) = false := decide_eq_false hxy
    have hyx : y ≤ x := by omega
    simp [List.mergeSort, hd, min_eq_right hyx]

/-- Property 14: On a non-empty constant list `List.replicate n v`, `benchmark_median_low` returns `some v`. -/
@[reducible]
def replicate_prop (n : Nat) (v : Int) : Prop :=
  0 < n → benchmark_median_low (List.replicate n v) = some v

theorem replicate_thm (n : Nat) (v : Int) :
    replicate_prop n v := by
  intro hn
  have hpre : Pre (List.replicate n v) := by
    simp [Pre]
    omega
  have hisSome := (nonempty_isSome_thm (List.replicate n v) hpre).1
  rw [Option.isSome_iff_exists] at hisSome
  rcases hisSome with ⟨m, hm⟩
  have hmem := mem_thm (List.replicate n v) hpre m hm
  rw [List.mem_replicate] at hmem
  rcases hmem with ⟨_, rfl⟩
  exact hm

/-- Property 15: Translation equivariance: shifting every element by `c` shifts the low median by `c`. -/
@[reducible]
def shift_equivariant_prop (data : List Int) (c : Int) : Prop :=
  benchmark_median_low (data.map (· + c)) = (benchmark_median_low data).map (· + c)

theorem shift_equivariant_thm (data : List Int) (c : Int) :
    shift_equivariant_prop data c := by
  unfold shift_equivariant_prop
  rw [benchmark_eq_median_low, benchmark_eq_median_low]
  unfold median_low
  dsimp only
  have hmono : Monotone (fun x : Int => x + c) := fun a b hab => by dsimp; omega
  rw [mergeSort_map_of_monotone data (· + c) hmono]
  simp only [List.length_map]
  split_ifs with h0 hodd
  · rfl
  · exact List.getElem?_map
  · exact List.getElem?_map

/-- Property 16: Non-negative scaling equivariance: scaling every element by `c ≥ 0`
    scales the low median by `c`. -/
@[reducible]
def scale_nonneg_equivariant_prop (data : List Int) (c : Int) : Prop :=
  0 ≤ c → benchmark_median_low (data.map (c * ·)) = (benchmark_median_low data).map (c * ·)

theorem scale_nonneg_equivariant_thm (data : List Int) (c : Int) :
    scale_nonneg_equivariant_prop data c := by
  intro hc
  rw [benchmark_eq_median_low, benchmark_eq_median_low]
  unfold median_low
  dsimp only
  have hmono : Monotone (fun x : Int => c * x) := fun a b hab =>
    Int.mul_le_mul_of_nonneg_left hab hc
  rw [mergeSort_map_of_monotone data (c * ·) hmono]
  simp only [List.length_map]
  split_ifs with h0 hodd
  · rfl
  · exact List.getElem?_map
  · exact List.getElem?_map

/-- Property 17: If `data` is already sorted in non-decreasing order, `benchmark_median_low`
    directly returns `data[(data.length - 1) / 2]?`. -/
@[reducible]
def already_sorted_prop (data : List Int) : Prop :=
  List.Pairwise (· ≤ ·) data →
    benchmark_median_low data = data[(data.length - 1) / 2]?

theorem already_sorted_thm (data : List Int) (h : Pre data) :
    already_sorted_prop data := by
  intro hsorted
  rw [unified_index_thm data h, mergeSort_eq_self_of_sorted hsorted]

-- ============================================================================
-- 8. Post-condition (`def Post_prop`) as conjunction of properties
-- ============================================================================

/-- Complete post-condition for `benchmark_median_low` on non-empty input `data`. -/
@[reducible]
def Post_prop (data : List Int) : Prop :=
  nonempty_isSome_prop data ∧
  unified_index_prop data ∧
  odd_length_prop data ∧
  even_length_prop data ∧
  mem_prop data ∧
  lower_half_prop data ∧
  upper_half_prop data ∧
  bounds_prop data ∧
  sorted_idempotent_prop data ∧
  already_sorted_prop data

-- ============================================================================
-- 9. Property-based tests (PBTs)
-- ============================================================================

/-- Sample datasets for bounded exhaustive/regression PBTs. -/
def pbtTestLists : List (List Int) :=
  [ [1, 3, 5],
    [1, 2, 3, 4, 5, 6, 9],
    [1, 3, 5, 7],
    [1, 2, 3, 4, 5, 6],
    [42],
    [10, 20],
    [20, 10],
    [9, 1, 6, 2, 5, 4, 3],
    [-5, -1, 0, 3, 7],
    [-10, -5, 5, 10],
    [0, 0, 0, 0],
    [5, 4, 3, 2, 1, 0, -1, -2] ]

-- PBT for empty_none_prop
#eval Plausible.Testable.check (∀ data : List Int, empty_none_prop data)
example : empty_none_prop [] := by native_decide

-- PBT for unified_index_prop
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int, unified_index_prop (x :: xs))
example : pbtTestLists.all (fun data => decide (unified_index_prop data)) = true := by native_decide

-- PBT for nonempty_isSome_prop
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int, nonempty_isSome_prop (x :: xs))
example : pbtTestLists.all (fun data => decide (nonempty_isSome_prop data)) = true := by native_decide

-- PBT for odd_length_prop
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int, odd_length_prop (x :: xs))
example : pbtTestLists.all (fun data => decide (odd_length_prop data)) = true := by native_decide

-- PBT for even_length_prop
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int, even_length_prop (x :: xs))
example : pbtTestLists.all (fun data => decide (even_length_prop data)) = true := by native_decide

-- PBT for mem_prop
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int, mem_prop (x :: xs))
example : pbtTestLists.all (fun data => decide (mem_prop data)) = true := by native_decide

-- PBT for lower_half_prop
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int, lower_half_prop (x :: xs))
example : pbtTestLists.all (fun data => decide (lower_half_prop data)) = true := by native_decide

-- PBT for upper_half_prop
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int, upper_half_prop (x :: xs))
example : pbtTestLists.all (fun data => decide (upper_half_prop data)) = true := by native_decide

-- PBT for bounds_prop
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int, bounds_prop (x :: xs))
example : pbtTestLists.all (fun data => decide (bounds_prop data)) = true := by native_decide

-- PBT for sorted_idempotent_prop
#eval Plausible.Testable.check (∀ data : List Int, sorted_idempotent_prop data)
example : pbtTestLists.all (fun data => decide (sorted_idempotent_prop data)) = true := by native_decide

-- PBT for perm_invariant_prop (testing reverse and mergeSort permutations)
#eval Plausible.Testable.check (∀ data : List Int, benchmark_median_low data.reverse = benchmark_median_low data)
example : pbtTestLists.all (fun data => decide (perm_invariant_prop data data.reverse)) = true := by native_decide

-- PBT for singleton_prop
#eval Plausible.Testable.check (∀ x : Int, singleton_prop x)
example : (List.range 20).all (fun n => decide (singleton_prop (Int.ofNat n - 10))) = true := by native_decide

-- PBT for pair_prop
#eval Plausible.Testable.check (∀ x y : Int, pair_prop x y)
example : (List.range 10).all (fun n => decide (pair_prop (Int.ofNat n) (5 - Int.ofNat n))) = true := by native_decide

-- PBT for replicate_prop
#eval Plausible.Testable.check (∀ n : Nat, ∀ v : Int, replicate_prop (n + 1) v)
example : (List.range 10).all (fun n => decide (replicate_prop (n + 1) (Int.ofNat n - 5))) = true := by native_decide

-- PBT for shift_equivariant_prop
#eval Plausible.Testable.check (∀ data : List Int, ∀ c : Int, shift_equivariant_prop data c)
example : pbtTestLists.all (fun data => decide (shift_equivariant_prop data 7)) = true := by native_decide

-- PBT for scale_nonneg_equivariant_prop
#eval Plausible.Testable.check (∀ data : List Int, ∀ n : Nat, scale_nonneg_equivariant_prop data (Int.ofNat n))
example : pbtTestLists.all (fun data => decide (scale_nonneg_equivariant_prop data 3)) = true := by native_decide

-- PBT for already_sorted_prop
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int, already_sorted_prop (x :: xs))
example : pbtTestLists.all (fun data => decide (already_sorted_prop data)) = true := by native_decide

-- PBT for Post_prop
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int, Post_prop (x :: xs))
example : pbtTestLists.all (fun data => decide (Post_prop data)) = true := by native_decide

-- ============================================================================
-- 10. Correctness theorem: `Pre -> Post`
-- ============================================================================

/-- Main correctness theorem: for any input `data` satisfying `Pre data`,
    `Post_prop data` holds. -/
theorem benchmark_median_low_correct (data : List Int) (h : Pre data) :
    Post_prop data :=
  ⟨nonempty_isSome_thm data h,
   unified_index_thm data h,
   odd_length_thm data h,
   even_length_thm data h,
   mem_thm data h,
   lower_half_thm data h,
   upper_half_thm data h,
   bounds_thm data h,
   sorted_idempotent_thm data,
   already_sorted_thm data h⟩

-- ============================================================================
-- 11. Imperative implementation using `Id.run do` with mutable state
-- ============================================================================

/-- Imperative implementation of `median_low` using `Id.run do` and mutable state. -/
def median_low_imp (data : List Int) : Option Int := Id.run do
  let mut sorted : List Int := data.mergeSort (· ≤ ·)
  let mut n : Nat := sorted.length
  let mut result : Option Int := none
  if n = 0 then
    result := none
  else if n % 2 = 1 then
    result := sorted[n / 2]?
  else
    result := sorted[n / 2 - 1]?
  return result

/-- Imperative implementation of `benchmark_median_low` using `Id.run do` and mutable state. -/
def benchmark_median_low_imp (data : List Int) : Option Int := Id.run do
  let mut valid : Bool := pre data
  let mut result : Option Int := none
  if !valid then
    result := none
  else
    result := median_low_imp data
  return result

-- ============================================================================
-- 12. Imperative tests
-- ============================================================================

-- 1. Odd number of elements
example : benchmark_median_low_imp [1, 3, 5] = some 3 := by native_decide
example : benchmark_median_low_imp [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide

-- 2. Even number of elements
example : benchmark_median_low_imp [1, 3, 5, 7] = some 3 := by native_decide
example : benchmark_median_low_imp [1, 2, 3, 4, 5, 6] = some 3 := by native_decide

-- 3. Single value
example : benchmark_median_low_imp [42] = some 42 := by native_decide

-- 4. Two values
example : benchmark_median_low_imp [10, 20] = some 10 := by native_decide

-- 5. Unsorted input
example : benchmark_median_low_imp [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide

-- 6. Negative values
example : benchmark_median_low_imp [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : benchmark_median_low_imp [-10, -5, 5, 10] = some (-5) := by native_decide

-- 7. Error cases
example : benchmark_median_low_imp [] = none := by native_decide
example : median_low_imp [] = none := by native_decide

#eval benchmark_median_low_imp [1, 3, 5]
#eval benchmark_median_low_imp [1, 3, 5, 7]
#eval benchmark_median_low_imp [9, 1, 6, 2, 5, 4, 3]
#eval benchmark_median_low_imp [-10, -5, 5, 10]
#eval benchmark_median_low_imp []

#eval Plausible.Testable.check (∀ data : List Int, benchmark_median_low data = benchmark_median_low_imp data)

-- ============================================================================
-- 13. Equivalence theorem: functional = imperative
-- ============================================================================

/-- Equivalence theorem between functional `median_low` and imperative `median_low_imp`. -/
theorem median_low_equiv (data : List Int) :
    median_low data = median_low_imp data := by
  rfl

/-- Equivalence theorem between functional `benchmark_median_low` and imperative `benchmark_median_low_imp`. -/
theorem benchmark_median_low_equiv (data : List Int) :
    benchmark_median_low data = benchmark_median_low_imp data := by
  rfl

end «28_statistics_median_low»
