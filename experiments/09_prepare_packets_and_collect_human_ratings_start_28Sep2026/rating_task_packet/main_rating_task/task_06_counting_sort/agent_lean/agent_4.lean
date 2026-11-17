import Mathlib

/-!
# Counting sort

Counting sort for a list of integers. The algorithm counts occurrences of each
value and rebuilds the list in non-decreasing order. Negative values are handled
by shifting indices by the minimum, so the count array is indexed from zero.

Edge cases:
- The empty list returns the empty list.
- Python rejects non-integer elements with `ValueError`. At type `List Int`
  every element is already an integer, so that check is discharged by the type
  and `Pre` holds for every input.
-/

namespace counting_sort

/-- Index of `num` in a count array whose slot `0` represents `minVal`. -/
def shiftIndex (minVal num : Int) : Nat := (num - minVal).toNat

def incrAt (counts : List Nat) (i : Nat) : List Nat :=
  if h : i < counts.length then
    counts.set i (counts[i] + 1)
  else
    counts

def tally (arr : List Int) (minVal : Int) (rangeSize : Nat) : List Nat :=
  arr.foldl (fun cnt num => incrAt cnt (shiftIndex minVal num)) (List.replicate rangeSize 0)

def expandCounts : Int → List Nat → List Int
  | _, [] => []
  | v, c :: cs => List.replicate c v ++ expandCounts (v + 1) cs

def countIndex (minVal : Int) (i : Nat) : List Int → Nat
  | [] => 0
  | x :: xs => (if shiftIndex minVal x = i then 1 else 0) + countIndex minVal i xs

/--
Sort `arr` by counting occurrences.

Mirrors the Python implementation: on the empty list return `[]`; otherwise
shift by `min(arr)` so that index `i` stands for `min(arr) + i`, count each
element, then emit `min(arr) + i` exactly `count[i]` times.
-/
def countingSort (arr : List Int) : List Int :=
  match arr.min?, arr.max? with
  | some minVal, some maxVal =>
    let rangeSize := (maxVal - minVal).toNat + 1
    expandCounts minVal (tally arr minVal rangeSize)
  | _, _ => []


-- Unit tests (the Python `check` examples, plus negatives supported by the shift).

example : countingSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : countingSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : countingSort ([] : List Int) = [] := by native_decide
example : countingSort [1] = [1] := by native_decide
example : countingSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [2, 1] = [1, 2] := by native_decide
example : countingSort [1, 2] = [1, 2] := by native_decide
example : countingSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSort [3, 1, 2, 1, 3, 2] = [1, 1, 2, 2, 3, 3] := by native_decide
example : countingSort [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : countingSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSort [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide
example : countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : countingSort [-1, -3, -2] = [-3, -2, -1] := by native_decide
example : countingSort [2, -1, 0, -1, 3] = [-1, -1, 0, 2, 3] := by native_decide
example : countingSort [-5, -5, 0] = [-5, -5, 0] := by native_decide

#eval countingSort [3, 1, 2]
#eval countingSort ([] : List Int)
#eval countingSort [2, -1, 0, -1, 3]
#eval countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

-- Python `candidate([1, 2.5])` raises `ValueError` because `2.5` is not an `int`.
-- That value is not a `List Int`, so the case is excluded by the type of `countingSort`.


/--
Python `pre`: the input is a list of integers.
Every `List Int` satisfies that check, so the predicate is `True`.
-/
def Pre (_arr : List Int) : Prop := True

/-! ## Supporting lemmas -/

theorem incrAt_length (counts : List Nat) (i : Nat) :
    (incrAt counts i).length = counts.length := by
  unfold incrAt
  split <;> simp

theorem foldl_incr_length (arr : List Int) (counts : List Nat) (minVal : Int) :
    (arr.foldl (fun cnt num => incrAt cnt (shiftIndex minVal num)) counts).length
      = counts.length := by
  induction arr generalizing counts with
  | nil => simp
  | cons _ xs ih =>
    simp only [List.foldl_cons]
    rw [ih, incrAt_length]

theorem tally_length (arr : List Int) (minVal : Int) (rangeSize : Nat) :
    (tally arr minVal rangeSize).length = rangeSize := by
  unfold tally
  rw [foldl_incr_length, List.length_replicate]

theorem incrAt_get (counts : List Nat) (j i : Nat) (hi : i < counts.length) :
    (incrAt counts j)[i]'(by rw [incrAt_length]; exact hi) =
      if j = i then counts[i] + 1 else counts[i] := by
  unfold incrAt
  split
  · rename_i hj
    by_cases h : j = i
    · subst h
      simp
    · have hi' : i < (counts.set j (counts[j] + 1)).length := by
        simpa [List.length_set] using hi
      rw [List.getElem_set_ne h hi']
      simp [h]
  · rename_i hj
    have hne : j ≠ i := by
      intro eq
      exact hj (eq ▸ hi)
    simp [hne]

theorem incrAt_getD (counts : List Nat) (j i : Nat) (hi : i < counts.length) :
    (incrAt counts j).getD i 0 = counts.getD i 0 + if j = i then 1 else 0 := by
  have hi' : i < (incrAt counts j).length := by rw [incrAt_length]; exact hi
  have hL : (incrAt counts j).getD i 0 = (incrAt counts j)[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    simp
  have hR : counts.getD i 0 = counts[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp
  rw [hL, hR, incrAt_get _ _ _ hi]
  by_cases h : j = i <;> simp [h]

theorem foldl_tally_getD (arr : List Int) (counts : List Nat) (minVal : Int) (i : Nat)
    (hi : i < counts.length) :
    (arr.foldl (fun cnt num => incrAt cnt (shiftIndex minVal num)) counts).getD i 0 =
      counts.getD i 0 + countIndex minVal i arr := by
  induction arr generalizing counts with
  | nil => simp [countIndex]
  | cons x xs ih =>
    simp only [List.foldl_cons, countIndex]
    have hi1 : i < (incrAt counts (shiftIndex minVal x)).length := by
      rw [incrAt_length]; exact hi
    rw [ih (incrAt counts (shiftIndex minVal x)) hi1, incrAt_getD _ _ _ hi]
    by_cases h : shiftIndex minVal x = i
    · simp [h, Nat.add_assoc, Nat.add_left_comm]
    · simp [h]

theorem shiftIndex_add (minVal : Int) (i : Nat) :
    shiftIndex minVal (minVal + i) = i := by
  unfold shiftIndex
  have : minVal + (i : Int) - minVal = (i : Int) := by omega
  simp [this]

theorem of_shiftIndex {minVal x : Int} {i : Nat}
    (hle : minVal ≤ x) (hs : shiftIndex minVal x = i) : x = minVal + i := by
  unfold shiftIndex at hs
  have hcast : ((x - minVal).toNat : Int) = x - minVal := Int.toNat_sub_of_le hle
  have : x - minVal = (i : Int) := by
    have : ((x - minVal).toNat : Int) = (i : Int) := by simp [hs]
    rwa [hcast] at this
  omega

theorem countIndex_eq_count {arr : List Int} {minVal : Int} {i : Nat}
    (hall : ∀ x ∈ arr, minVal ≤ x) :
    countIndex minVal i arr = arr.count (minVal + i) := by
  induction arr with
  | nil => simp [countIndex]
  | cons x xs ih =>
    have hx : minVal ≤ x := hall x List.mem_cons_self
    have hxs : ∀ y ∈ xs, minVal ≤ y := fun y hy => hall y (List.mem_cons_of_mem _ hy)
    simp only [countIndex, List.count_cons, ih hxs]
    by_cases h : x = minVal + i
    · simp [h, shiftIndex_add, Nat.add_comm]
    · have hs : shiftIndex minVal x ≠ i := by
        intro heq
        exact h (of_shiftIndex hx heq)
      simp [h, hs, beq_iff_eq]

theorem tally_getD (arr : List Int) (minVal : Int) (rangeSize : Nat) (i : Nat)
    (hi : i < rangeSize) (hall : ∀ x ∈ arr, minVal ≤ x) :
    (tally arr minVal rangeSize).getD i 0 = arr.count (minVal + i) := by
  unfold tally
  have hi0 : i < (List.replicate rangeSize 0).length := by simpa using hi
  rw [foldl_tally_getD _ _ _ _ hi0, countIndex_eq_count hall]
  simp [List.getD_eq_getElem?_getD, hi]

theorem expandCounts_mem_ge {v x : Int} {counts : List Nat}
    (hx : x ∈ expandCounts v counts) : v ≤ x := by
  induction counts generalizing v with
  | nil => simp [expandCounts] at hx
  | cons c cs ih =>
    simp only [expandCounts, List.mem_append, List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩ | hx
    · exact le_rfl
    · exact le_trans (by omega : v ≤ v + 1) (ih hx)

theorem expandCounts_mem_lt {v x : Int} {counts : List Nat}
    (hx : x ∈ expandCounts v counts) : x < v + counts.length := by
  induction counts generalizing v with
  | nil => simp [expandCounts] at hx
  | cons c cs ih =>
    simp only [expandCounts, List.mem_append, List.mem_replicate, List.length_cons] at hx ⊢
    rcases hx with ⟨_, rfl⟩ | hx
    · omega
    · have := ih hx
      omega

theorem expandCounts_sorted (v : Int) (counts : List Nat) :
    List.Sorted (· ≤ ·) (expandCounts v counts) := by
  induction counts generalizing v with
  | nil =>
    change List.Pairwise (· ≤ ·) []
    exact List.Pairwise.nil
  | cons c cs ih =>
    change List.Pairwise (· ≤ ·) (List.replicate c v ++ expandCounts (v + 1) cs)
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact List.sorted_le_replicate c v
    · exact ih (v + 1)
    · intro a ha b hb
      rcases List.mem_replicate.mp ha with ⟨_, rfl⟩
      have hb' := expandCounts_mem_ge hb
      omega

theorem expandCounts_count_of_lt {v x : Int} {counts : List Nat} (hx : x < v) :
    (expandCounts v counts).count x = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro hmem
  have := expandCounts_mem_ge hmem
  omega

theorem expandCounts_count_of_ge {v x : Int} {counts : List Nat}
    (hx : v + counts.length ≤ x) : (expandCounts v counts).count x = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro hmem
  have := expandCounts_mem_lt hmem
  omega

theorem expandCounts_count (v : Int) (counts : List Nat) (k : Nat) (hk : k < counts.length) :
    (expandCounts v counts).count (v + k) = counts.getD k 0 := by
  induction counts generalizing v k with
  | nil => simp at hk
  | cons c cs ih =>
    cases k with
    | zero =>
      rw [expandCounts, List.count_append, List.getD_cons_zero, Nat.cast_zero, Int.add_zero,
        List.count_replicate_self]
      have hrest : (expandCounts (v + 1) cs).count v = 0 :=
        expandCounts_count_of_lt (by omega)
      simp [hrest]
    | succ k =>
      rw [expandCounts, List.count_append]
      have hk' : k < cs.length := by
        simp [List.length_cons] at hk
        omega
      simp only [Nat.cast_add, Nat.cast_one, List.getD_eq_getElem?_getD]
      have hrep : (List.replicate c v).count (v + ((k : Int) + 1)) = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        rcases List.mem_replicate.mp hmem with ⟨_, heq⟩
        omega
      have hrest :
          (expandCounts (v + 1) cs).count (v + ((k : Int) + 1)) = (cs[k]?).getD 0 := by
        have hv : (v + 1) + (k : Int) = v + ((k : Int) + 1) := by omega
        have hih := ih (v + 1) k hk'
        rw [List.getD_eq_getElem?_getD] at hih
        simpa [hv] using hih
      exact by simp [hrep, hrest]

theorem int_min?_iff {xs : List Int} {a : Int} :
    xs.min? = some a ↔ a ∈ xs ∧ ∀ b ∈ xs, a ≤ b := by
  apply List.min?_eq_some_iff
  · exact fun _ => le_rfl
  · intro x y
    rcases le_total x y with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)
  · intro x y z
    exact le_min_iff
  · intro x y _ _ h1 h2
    exact le_antisymm h1 h2

theorem int_max?_iff {xs : List Int} {a : Int} :
    xs.max? = some a ↔ a ∈ xs ∧ ∀ b ∈ xs, b ≤ a := by
  letI : Std.Antisymm (· ≤ · : Int → Int → Prop) := ⟨fun a b hab hba => le_antisymm hab hba⟩
  apply List.max?_eq_some_iff
  · exact fun _ => le_rfl
  · intro x y
    rcases le_total x y with h | h
    · exact Or.inr (max_eq_right h)
    · exact Or.inl (max_eq_left h)
  · intro x y z
    exact max_le_iff

theorem countingSort_count (arr : List Int) (v : Int) :
    (countingSort arr).count v = arr.count v := by
  unfold countingSort
  cases hmin : arr.min? with
  | none =>
    have hempty : arr = [] := List.min?_eq_none_iff.mp hmin
    subst hempty
    simp
  | some minVal =>
    have hmaxN : arr.max? ≠ none := by
      intro h
      have : arr = [] := List.max?_eq_none_iff.mp h
      simp [this] at hmin
    cases hmax : arr.max? with
    | none => exact absurd hmax hmaxN
    | some maxVal =>
      have hMin := (int_min?_iff (xs := arr) (a := minVal)).mp hmin
      have hMax := (int_max?_iff (xs := arr) (a := maxVal)).mp hmax
      have hleMM : minVal ≤ maxVal := hMax.2 minVal hMin.1
      have hall : ∀ x ∈ arr, minVal ≤ x := fun x hx => hMin.2 x hx
      let rangeSize : Nat := (maxVal - minVal).toNat + 1
      have hlen : (tally arr minVal rangeSize).length = rangeSize := tally_length _ _ _
      by_cases hlo : v < minVal
      · rw [expandCounts_count_of_lt (counts := tally arr minVal rangeSize) hlo]
        exact (List.count_eq_zero_of_not_mem (fun hv => by
          have := hMin.2 v hv
          omega)).symm
      · by_cases hhi : minVal + (rangeSize : Int) ≤ v
        · have hge : minVal + ↑(tally arr minVal rangeSize).length ≤ v := by
            simpa [hlen] using hhi
          rw [expandCounts_count_of_ge hge]
          exact (List.count_eq_zero_of_not_mem (fun hv => by
            have hvM : v ≤ maxVal := hMax.2 v hv
            have hcast : ((maxVal - minVal).toNat : Int) = maxVal - minVal :=
              Int.toNat_sub_of_le hleMM
            dsimp [rangeSize] at hhi
            omega)).symm
        · have hvge : minVal ≤ v := le_of_not_gt hlo
          have hvlt : v < minVal + (rangeSize : Int) := lt_of_not_ge hhi
          have hk : shiftIndex minVal v < rangeSize := by
            unfold shiftIndex
            have hcast : ((v - minVal).toNat : Int) = v - minVal := Int.toNat_sub_of_le hvge
            have hlt : v - minVal < (rangeSize : Int) := by omega
            have : ((v - minVal).toNat : Int) < (rangeSize : Int) := by rwa [hcast]
            exact Int.ofNat_lt.mp this
          have hvk : v = minVal + shiftIndex minVal v := of_shiftIndex hvge rfl
          have hk' : shiftIndex minVal v < (tally arr minVal rangeSize).length := by
            simpa [hlen] using hk
          rw [hvk, expandCounts_count _ _ _ hk', tally_getD _ _ _ _ hk hall]

theorem countingSort_perm (arr : List Int) : List.Perm (countingSort arr) arr := by
  rw [List.perm_iff_count]
  intro a
  exact countingSort_count arr a

theorem countingSort_sorted (arr : List Int) :
    List.Sorted (· ≤ ·) (countingSort arr) := by
  unfold countingSort
  cases arr.min? <;> cases arr.max?
  · change List.Pairwise (· ≤ ·) []
    exact List.Pairwise.nil
  · change List.Pairwise (· ≤ ·) []
    exact List.Pairwise.nil
  · change List.Pairwise (· ≤ ·) []
    exact List.Pairwise.nil
  · exact expandCounts_sorted _ _

theorem countingSort_nil : countingSort ([] : List Int) = [] := by
  simp [countingSort, List.min?_nil, List.max?_nil]

theorem countingSort_length (arr : List Int) :
    (countingSort arr).length = arr.length :=
  (countingSort_perm arr).length_eq

theorem countingSort_singleton (a : Int) : countingSort [a] = [a] := by
  apply List.eq_of_perm_of_sorted (countingSort_perm [a]) (countingSort_sorted [a])
  simp [List.Sorted]

theorem countingSort_min? (arr : List Int) : (countingSort arr).min? = arr.min? := by
  cases h : arr.min? with
  | none =>
    have : arr = [] := List.min?_eq_none_iff.mp h
    subst this
    simp [countingSort_nil, List.min?_nil]
  | some m =>
    have hp := countingSort_perm arr
    have hchar := (int_min?_iff (xs := arr) (a := m)).mp h
    have hmem : m ∈ countingSort arr := hp.mem_iff.mpr hchar.1
    have hall : ∀ b ∈ countingSort arr, m ≤ b := by
      intro b hb
      exact hchar.2 b (hp.mem_iff.mp hb)
    exact (int_min?_iff (xs := countingSort arr) (a := m)).mpr ⟨hmem, hall⟩

theorem countingSort_max? (arr : List Int) : (countingSort arr).max? = arr.max? := by
  cases h : arr.max? with
  | none =>
    have : arr = [] := List.max?_eq_none_iff.mp h
    subst this
    simp [countingSort_nil, List.max?_nil]
  | some m =>
    have hp := countingSort_perm arr
    have hchar := (int_max?_iff (xs := arr) (a := m)).mp h
    have hmem : m ∈ countingSort arr := hp.mem_iff.mpr hchar.1
    have hall : ∀ b ∈ countingSort arr, b ≤ m := by
      intro b hb
      exact hchar.2 b (hp.mem_iff.mp hb)
    exact (int_max?_iff (xs := countingSort arr) (a := m)).mpr ⟨hmem, hall⟩

theorem countingSort_idem (arr : List Int) :
    countingSort (countingSort arr) = countingSort arr := by
  apply List.eq_of_perm_of_sorted
    (countingSort_perm (countingSort arr))
    (countingSort_sorted (countingSort arr))
    (countingSort_sorted arr)

theorem countingSort_of_sorted {arr : List Int} (h : List.Sorted (· ≤ ·) arr) :
    countingSort arr = arr :=
  List.eq_of_perm_of_sorted (countingSort_perm arr) (countingSort_sorted arr) h

theorem countingSort_bounds (arr : List Int) :
    match arr.min?, arr.max? with
    | some lo, some hi => ∀ x ∈ countingSort arr, lo ≤ x ∧ x ≤ hi
    | _, _ => countingSort arr = [] := by
  cases hmin : arr.min? <;> cases hmax : arr.max?
  · simp [countingSort, hmin, hmax]
  · simp [countingSort, hmin]
  · simp [countingSort, hmax]
  · intro x hx
    have hMin := (int_min?_iff (xs := arr)).mp hmin
    have hMax := (int_max?_iff (xs := arr)).mp hmax
    have hxarr : x ∈ arr := (countingSort_perm arr).mem_iff.mp hx
    exact ⟨hMin.2 x hxarr, hMax.2 x hxarr⟩

theorem countingSort_mergeSort (arr : List Int) :
    countingSort arr = arr.mergeSort (fun a b => decide (a ≤ b)) := by
  have hs : List.Sorted (· ≤ ·) (arr.mergeSort (fun a b => decide (a ≤ b))) := by
    have hpw :=
      List.sorted_mergeSort
        (le := fun a b : Int => decide (a ≤ b))
        (fun a b c hab hbc => by
          simp only [decide_eq_true_eq] at hab hbc
          simpa [decide_eq_true_eq] using (le_trans hab hbc))
        (fun a b => by
          rcases le_total a b with h | h <;> simp [h])
        arr
    refine List.Pairwise.imp (fun hab => ?_) hpw
    exact of_decide_eq_true hab
  exact List.eq_of_perm_of_sorted
    ((countingSort_perm arr).trans (List.mergeSort_perm arr _).symm)
    (countingSort_sorted arr) hs


/-! ## Properties -/

def sorted_prop (arr : List Int) : Prop :=
  List.Sorted (· ≤ ·) (countingSort arr)

def perm_prop (arr : List Int) : Prop :=
  List.Perm (countingSort arr) arr

def length_prop (arr : List Int) : Prop :=
  (countingSort arr).length = arr.length

def count_prop (arr : List Int) : Prop :=
  ∀ v : Int, (countingSort arr).count v = arr.count v

def empty_prop : Prop :=
  countingSort ([] : List Int) = []

def singleton_prop (a : Int) : Prop :=
  countingSort [a] = [a]

/-- Every output element lies between the input minimum and maximum. -/
def bounds_prop (arr : List Int) : Prop :=
  match arr.min?, arr.max? with
  | some lo, some hi => ∀ x ∈ countingSort arr, lo ≤ x ∧ x ≤ hi
  | _, _ => countingSort arr = []

def min_preserved_prop (arr : List Int) : Prop :=
  (countingSort arr).min? = arr.min?

def max_preserved_prop (arr : List Int) : Prop :=
  (countingSort arr).max? = arr.max?

def idempotent_prop (arr : List Int) : Prop :=
  countingSort (countingSort arr) = countingSort arr

def sorted_fixed_prop (arr : List Int) : Prop :=
  List.Sorted (· ≤ ·) arr → countingSort arr = arr

def mergeSort_prop (arr : List Int) : Prop :=
  countingSort arr = arr.mergeSort (fun a b => decide (a ≤ b))

theorem sorted_thm (arr : List Int) : sorted_prop arr :=
  countingSort_sorted arr

theorem perm_thm (arr : List Int) : perm_prop arr :=
  countingSort_perm arr

theorem length_thm (arr : List Int) : length_prop arr :=
  countingSort_length arr

theorem count_thm (arr : List Int) : count_prop arr :=
  countingSort_count arr

theorem empty_thm : empty_prop :=
  countingSort_nil

theorem singleton_thm (a : Int) : singleton_prop a :=
  countingSort_singleton a

theorem bounds_thm (arr : List Int) : bounds_prop arr :=
  countingSort_bounds arr

theorem min_preserved_thm (arr : List Int) : min_preserved_prop arr :=
  countingSort_min? arr

theorem max_preserved_thm (arr : List Int) : max_preserved_prop arr :=
  countingSort_max? arr

theorem idempotent_thm (arr : List Int) : idempotent_prop arr :=
  countingSort_idem arr

theorem sorted_fixed_thm (arr : List Int) : sorted_fixed_prop arr :=
  countingSort_of_sorted

theorem mergeSort_thm (arr : List Int) : mergeSort_prop arr :=
  countingSort_mergeSort arr

/--
Post-condition: `countingSort` returns the non-decreasing rearrangement of its
input. The conjuncts are the observable content of the Python function:
sorted order, the same multiset (hence the same counts and length), min/max
and bounds preserved by the shift, idempotence, the empty and singleton
edge cases, and agreement with merge sort.
-/
def Post_prop (arr : List Int) : Prop :=
  sorted_prop arr ∧
  perm_prop arr ∧
  length_prop arr ∧
  count_prop arr ∧
  bounds_prop arr ∧
  min_preserved_prop arr ∧
  max_preserved_prop arr ∧
  idempotent_prop arr ∧
  sorted_fixed_prop arr ∧
  mergeSort_prop arr ∧
  (arr = [] → empty_prop) ∧
  (∀ a, arr = [a] → singleton_prop a)


/-! ## Property-based tests

Executable checks of each `_prop` and of `Post_prop`. A passing check is
evidence, not a proof; the theorems above are proved separately.
-/

/-- Adjacent non-decreasing order. For a total order this matches `List.Sorted (· ≤ ·)`. -/
def isSorted : List Int → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a ≤ b) && isSorted (b :: rest)

/-- Same length and the same multiplicity for every input element. -/
def sameMultiset (xs ys : List Int) : Bool :=
  xs.length == ys.length && xs.all (fun v => xs.count v == ys.count v)

def boundsOk (arr : List Int) : Bool :=
  match arr.min?, arr.max? with
  | some lo, some hi => (countingSort arr).all (fun x => (lo ≤ x) && (x ≤ hi))
  | _, _ => countingSort arr == []

/-- Boolean form of `Post_prop`. -/
def postOk (arr : List Int) : Bool :=
  isSorted (countingSort arr) &&
  sameMultiset (countingSort arr) arr &&
  ((countingSort arr).length == arr.length) &&
  (arr.all (fun v => (countingSort arr).count v == arr.count v)) &&
  boundsOk arr &&
  ((countingSort arr).min? == arr.min?) &&
  ((countingSort arr).max? == arr.max?) &&
  (countingSort (countingSort arr) == countingSort arr) &&
  (countingSort arr == arr.mergeSort (fun a b => decide (a ≤ b))) &&
  (!(isSorted arr) || countingSort arr == arr) &&
  (!(arr == []) || countingSort arr == []) &&
  (arr.length != 1 || countingSort arr == arr)

-- PBT for sorted_prop
#eval Plausible.Testable.check (∀ arr : List Int, isSorted (countingSort arr) = true)

-- PBT for perm_prop and count_prop
#eval Plausible.Testable.check
  (∀ arr : List Int, sameMultiset (countingSort arr) arr = true)

-- PBT for length_prop
#eval Plausible.Testable.check
  (∀ arr : List Int, (countingSort arr).length = arr.length)

-- PBT for count_prop (each input value keeps its multiplicity)
#eval Plausible.Testable.check
  (∀ arr : List Int, arr.all (fun v => (countingSort arr).count v == arr.count v) = true)

-- PBT for bounds_prop
#eval Plausible.Testable.check (∀ arr : List Int, boundsOk arr = true)

-- PBT for min_preserved_prop
#eval Plausible.Testable.check
  (∀ arr : List Int, (countingSort arr).min? == arr.min?)

-- PBT for max_preserved_prop
#eval Plausible.Testable.check
  (∀ arr : List Int, (countingSort arr).max? == arr.max?)

-- PBT for idempotent_prop
#eval Plausible.Testable.check
  (∀ arr : List Int, countingSort (countingSort arr) = countingSort arr)

-- PBT for sorted_fixed_prop, on the sorted lists produced by merge sort
#eval Plausible.Testable.check
  (∀ arr : List Int, countingSort (arr.mergeSort) = arr.mergeSort)

-- PBT for mergeSort_prop
#eval Plausible.Testable.check
  (∀ arr : List Int, countingSort arr = arr.mergeSort (fun a b => decide (a ≤ b)))

-- PBT for singleton_prop
#eval Plausible.Testable.check (∀ a : Int, countingSort [a] = [a])

-- PBT for Post_prop
#eval Plausible.Testable.check (∀ arr : List Int, postOk arr = true)

/-- All lists of length `n` with entries in `{-2, -1, 0, 1, 2}`. -/
def enumLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (enumLists n).flatMap fun xs => ([-2, -1, 0, 1, 2]).map fun v => v :: xs

def smallInputs : List (List Int) :=
  enumLists 0 ++ enumLists 1 ++ enumLists 2 ++ enumLists 3

-- Bounded PBT for Post_prop, including negatives and the empty list.
example : smallInputs.all postOk = true := by native_decide

-- Bounded PBT for empty_prop.
example : (List.replicate 8 ([] : List Int)).all (fun xs => countingSort xs == []) = true := by
  native_decide

-- Bounded PBT for sorted_fixed_prop on already sorted inputs (avoids a "Gave up" sample).
example : (List.range 20).all (fun n =>
    let xs : List Int := (List.range n).map fun i => (i : Int) - 5
    countingSort xs == xs) = true := by native_decide

-- Bounded PBT for singleton_prop.
example : (List.range 21).all (fun n =>
    countingSort [(n : Int) - 10] == [(n : Int) - 10]) = true := by native_decide

theorem correctness_thm (arr : List Int) (_h : Pre arr) : Post_prop arr := by
  unfold Post_prop
  refine ⟨sorted_thm arr, perm_thm arr, length_thm arr, count_thm arr, bounds_thm arr,
    min_preserved_thm arr, max_preserved_thm arr, idempotent_thm arr, sorted_fixed_thm arr,
    mergeSort_thm arr, ?_, ?_⟩
  · intro h
    subst h
    exact empty_thm
  · intro a h
    subst h
    exact singleton_thm a


/-! ## Imperative implementation

The loop state matches the Python program: a mutable count array shifted by the
minimum, then a mutable result filled by repeating each shifted value.
-/

def countingSortImp (arr : List Int) : List Int :=
  Id.run do
    match arr.min?, arr.max? with
    | some minVal, some maxVal =>
      let rangeSize := (maxVal - minVal).toNat + 1
      let mut counts : List Nat := List.replicate rangeSize 0
      for num in arr do
        counts := incrAt counts (shiftIndex minVal num)
      let mut result : List Int := []
      let mut value : Int := minVal
      for c in counts do
        result := result ++ List.replicate c value
        value := value + 1
      return result
    | _, _ =>
      return []

example : countingSortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSortImp ([] : List Int) = [] := by native_decide
example : countingSortImp [1] = [1] := by native_decide
example : countingSortImp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSortImp [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : countingSortImp [2, -1, 0, -1, 3] = [-1, -1, 0, 2, 3] := by native_decide
example : countingSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

#eval countingSortImp [3, 1, 2]
#eval countingSortImp [9, 8, 7, 6, 5, 4, 3, 2, 1]
#eval countingSortImp [-5, -5, 0]


theorem expand_foldl (acc : List Int) (v : Int) (counts : List Nat) :
    (counts.foldl
        (fun (b : MProd (List Int) Int) (a : Nat) =>
          (⟨b.fst ++ List.replicate a b.snd, b.snd + 1⟩ : MProd (List Int) Int))
        (⟨acc, v⟩ : MProd (List Int) Int)).fst =
      acc ++ expandCounts v counts := by
  induction counts generalizing acc v with
  | nil => simp [expandCounts]
  | cons c cs ih =>
    simp only [List.foldl_cons, expandCounts]
    simpa [List.append_assoc] using ih (acc ++ List.replicate c v) (v + 1)

theorem equivalence_thm (arr : List Int) : countingSort arr = countingSortImp arr := by
  symm
  unfold countingSortImp countingSort
  cases arr.min? <;> cases arr.max?
  · simp [Id.run_pure]
  · simp [Id.run_pure]
  · simp [Id.run_pure]
  · rename_i minVal maxVal
    simp [tally, Id.run_pure, List.forIn_pure_yield_eq_foldl]
    simpa [List.append_nil] using
      expand_foldl [] minVal
        (List.foldl (fun b a => incrAt b (shiftIndex minVal a))
          (List.replicate ((maxVal - minVal).toNat + 1) 0) arr)

-- PBT for functional / imperative equivalence.
#eval Plausible.Testable.check (∀ arr : List Int, countingSort arr = countingSortImp arr)

example : smallInputs.all (fun arr => countingSort arr == countingSortImp arr) = true := by
  native_decide


end counting_sort
