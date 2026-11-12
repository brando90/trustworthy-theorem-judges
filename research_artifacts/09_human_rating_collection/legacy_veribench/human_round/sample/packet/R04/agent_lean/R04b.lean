import Mathlib

/-!
# Counting sort

Lean 4 translation of a Python implementation of *counting sort* on lists of
integers (negative values are supported by shifting the whole range so that the
smallest element maps to bucket `0`).

The Python program

* raises `ValueError` when the input is not a `List[int]` — in Lean this is
  enforced by the type `List Int`, so the pre-condition is vacuously true;
* returns `[]` on the empty list;
* otherwise computes `min`/`max`, allocates a bucket array of size
  `max - min + 1`, counts occurrences and concatenates, for each bucket index
  `i` in increasing order, `count[i]` copies of `min + i`.

This file contains

* a functional implementation (`countingSort`),
* the specification (`Pre`, the individual property predicates and `Post_prop`)
  together with proofs that the implementation is sorted, is a permutation of
  its input and preserves length,
* an imperative implementation (`countingSortImp`) written with `Id.run do` and
  mutable state (`let mut`, `for` loops, an explicit mutable bucket list),
* a proof that both implementations agree on every input.
-/

namespace counting_sort

/-! ## Functional implementation -/

/-- `lmin a l` is the minimum of `a :: l`; it mirrors Python's `min(arr)`
(the fold is the one performed by the imperative loop below). -/
def lmin (a : Int) (l : List Int) : Int :=
  l.foldl (fun m x => if x < m then x else m) a

/-- `lmax a l` is the maximum of `a :: l`; it mirrors Python's `max(arr)`. -/
def lmax (a : Int) (l : List Int) : Int :=
  l.foldl (fun m x => if m < x then x else m) a

/-- `build mn arr n` concatenates, for every bucket index `i < n` in increasing
order, `(number of occurrences of mn + i in arr)` copies of `mn + i`.
This is the `for i in range(range_size): result.extend(...)` loop. -/
def build (mn : Int) (arr : List Int) : Nat → List Int
  | 0 => []
  | n + 1 => build mn arr n ++ List.replicate (arr.count (mn + (n : Int))) (mn + (n : Int))

/-- Counting sort. -/
def countingSort (arr : List Int) : List Int :=
  match arr with
  | [] => []
  | a :: as =>
      let mn := lmin a as
      let mx := lmax a as
      build mn (a :: as) (mx - mn + 1).toNat

/-! ## Unit tests (mirroring the Python `check` function) -/

#eval countingSort [3, 1, 2]
#eval countingSort ([] : List Int)
#eval countingSort [3, 1, 4, 1, 2, 3]
#eval countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

example : countingSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : countingSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : countingSort ([] : List Int) = [] := by native_decide
example : countingSort [1] = [1] := by native_decide
example : countingSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : countingSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [2, 1] = [1, 2] := by native_decide
example : countingSort [1, 2] = [1, 2] := by native_decide
example : countingSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSort [3, 1, 2, 1, 3, 2] = [1, 1, 2, 2, 3, 3] := by native_decide
example : countingSort [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : countingSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : countingSort [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide
example :
    countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
      = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
-- negative numbers (the shift by `min_val` in the Python code)
example : countingSort [3, -1, 2, -5, 0] = [-5, -1, 0, 2, 3] := by native_decide

/-! ## Auxiliary lemmas about `lmin` / `lmax` -/

theorem lmin_le : ∀ (a : Int) (l : List Int), lmin a l ≤ a := by
  intro a l
  induction l generalizing a with
  | nil => exact le_refl a
  | cons b bs ih =>
      have h := ih (if b < a then b else a)
      have e : lmin a (b :: bs) = lmin (if b < a then b else a) bs := rfl
      rw [e]
      split_ifs at h ⊢ <;> omega

theorem le_lmax : ∀ (a : Int) (l : List Int), a ≤ lmax a l := by
  intro a l
  induction l generalizing a with
  | nil => exact le_refl a
  | cons b bs ih =>
      have h := ih (if a < b then b else a)
      have e : lmax a (b :: bs) = lmax (if a < b then b else a) bs := rfl
      rw [e]
      split_ifs at h ⊢ <;> omega

theorem lmin_le_of_mem : ∀ (a : Int) (l : List Int) (x : Int), x ∈ l → lmin a l ≤ x := by
  intro a l
  induction l generalizing a with
  | nil => intro x hx; cases hx
  | cons b bs ih =>
      intro x hx
      have e : lmin a (b :: bs) = lmin (if b < a then b else a) bs := rfl
      have h := lmin_le (if b < a then b else a) bs
      rw [e]
      rcases List.mem_cons.mp hx with rfl | hmem
      · split_ifs at h ⊢ <;> omega
      · exact ih _ x hmem

theorem le_lmax_of_mem : ∀ (a : Int) (l : List Int) (x : Int), x ∈ l → x ≤ lmax a l := by
  intro a l
  induction l generalizing a with
  | nil => intro x hx; cases hx
  | cons b bs ih =>
      intro x hx
      have e : lmax a (b :: bs) = lmax (if a < b then b else a) bs := rfl
      have h := le_lmax (if a < b then b else a) bs
      rw [e]
      rcases List.mem_cons.mp hx with rfl | hmem
      · split_ifs at h ⊢ <;> omega
      · exact ih _ x hmem

/-- Every element of a non-empty list lies in the bucket range determined by its
minimum and maximum. -/
theorem mem_range_of_mem (a : Int) (as : List Int) (y : Int) (hy : y ∈ a :: as) :
    lmin a as ≤ y ∧ y < lmin a as + (((lmax a as - lmin a as + 1).toNat : Nat) : Int) := by
  have hma : lmin a as ≤ a := lmin_le a as
  have ham : a ≤ lmax a as := le_lmax a as
  have hcast : (((lmax a as - lmin a as + 1).toNat : Nat) : Int)
      = lmax a as - lmin a as + 1 := Int.toNat_of_nonneg (by omega)
  rw [hcast]
  rcases List.mem_cons.mp hy with rfl | hmem
  · omega
  · have h1 := lmin_le_of_mem a as y hmem
    have h2 := le_lmax_of_mem a as y hmem
    omega

/-! ## Auxiliary lemmas about `build` -/

theorem count_replicate_int (k : Nat) (v x : Int) :
    (List.replicate k v).count x = if x = v then k else 0 := by
  by_cases h : x = v
  · subst h; simp
  · rw [if_neg h]
    exact List.count_eq_zero.mpr (fun hm => h (List.eq_of_mem_replicate hm))

theorem sorted_replicate (k : Nat) (v : Int) : (List.replicate k v).Sorted (· ≤ ·) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ]
      refine List.sorted_cons.mpr ⟨?_, ih⟩
      intro b hb
      exact le_of_eq (List.eq_of_mem_replicate hb).symm

/-- Every element produced by `build` lies in the bucket range. -/
theorem mem_build {mn : Int} {arr : List Int} {n : Nat} {x : Int}
    (hx : x ∈ build mn arr n) : mn ≤ x ∧ x < mn + (n : Int) := by
  induction n with
  | zero => simp [build] at hx
  | succ n ih =>
      rw [build, List.mem_append] at hx
      rcases hx with h | h
      · have := ih h; push_cast; omega
      · have hxv := List.eq_of_mem_replicate h
        subst hxv
        push_cast
        omega

theorem count_build_eq_zero (mn : Int) (arr : List Int) (n : Nat) (x : Int)
    (h : ¬ (mn ≤ x ∧ x < mn + (n : Int))) : (build mn arr n).count x = 0 :=
  List.count_eq_zero.mpr (fun hm => h (mem_build hm))

theorem count_build_of_mem (mn : Int) (arr : List Int) : ∀ (n : Nat) (x : Int),
    mn ≤ x → x < mn + (n : Int) → (build mn arr n).count x = arr.count x := by
  intro n
  induction n with
  | zero => intro x h1 h2; exfalso; push_cast at h2; omega
  | succ n ih =>
      intro x h1 h2
      by_cases hB : x = mn + (n : Int)
      · subst hB
        rw [build, List.count_append, count_replicate_int, if_pos rfl,
            count_build_eq_zero mn arr n _ (by rintro ⟨-, h⟩; omega)]
        omega
      · have h2' : x < mn + (n : Int) := by push_cast at h2; omega
        rw [build, List.count_append, count_replicate_int, if_neg hB, ih x h1 h2']
        omega

theorem sorted_build (mn : Int) (arr : List Int) (n : Nat) :
    (build mn arr n).Sorted (· ≤ ·) := by
  induction n with
  | zero => simp [build]
  | succ n ih =>
      rw [build]
      refine List.pairwise_append.mpr ⟨ih, sorted_replicate _ _, ?_⟩
      intro y hy z hz
      have h1 := mem_build hy
      have h2 := List.eq_of_mem_replicate hz
      subst h2
      omega

/-! ## Main properties of the functional implementation -/

theorem countingSort_sorted (arr : List Int) : (countingSort arr).Sorted (· ≤ ·) := by
  cases arr with
  | nil => simp [countingSort]
  | cons a as => exact sorted_build _ _ _

theorem countingSort_perm (arr : List Int) : (countingSort arr).Perm arr := by
  cases arr with
  | nil => simp [countingSort]
  | cons a as =>
      show (build (lmin a as) (a :: as) ((lmax a as - lmin a as + 1).toNat)).Perm (a :: as)
      rw [List.perm_iff_count]
      intro x
      by_cases hx : lmin a as ≤ x ∧
          x < lmin a as + (((lmax a as - lmin a as + 1).toNat : Nat) : Int)
      · exact count_build_of_mem _ _ _ x hx.1 hx.2
      · rw [count_build_eq_zero _ _ _ x hx]
        symm
        exact List.count_eq_zero.mpr (fun hm => hx (mem_range_of_mem a as x hm))

theorem countingSort_length (arr : List Int) : (countingSort arr).length = arr.length :=
  (countingSort_perm arr).length_eq

/-! ## Pre-condition, properties and post-condition -/

/-- Python's `pre`: the argument must be a list of integers.  In Lean this is
guaranteed by the type `List Int`, so the pre-condition holds always (the
`ValueError` branch of the Python program is unreachable here). -/
def Pre (_arr : List Int) : Prop := True

/-- The result is sorted in non-decreasing order. -/
def sorted_prop (_arr result : List Int) : Prop := result.Sorted (· ≤ ·)

/-- The result is a permutation of the input (same elements with multiplicity). -/
def perm_prop (arr result : List Int) : Prop := result.Perm arr

/-- The result has the same length as the input. -/
def length_prop (arr result : List Int) : Prop := result.length = arr.length

/-- Every value occurs in the result as often as it occurs in the input. -/
def count_prop (arr result : List Int) : Prop := ∀ x : Int, result.count x = arr.count x

/-- The empty list is mapped to the empty list. -/
def nil_prop : Prop := countingSort [] = []

theorem sorted_thm (arr : List Int) : sorted_prop arr (countingSort arr) :=
  countingSort_sorted arr

theorem perm_thm (arr : List Int) : perm_prop arr (countingSort arr) :=
  countingSort_perm arr

theorem length_thm (arr : List Int) : length_prop arr (countingSort arr) :=
  countingSort_length arr

theorem count_thm (arr : List Int) : count_prop arr (countingSort arr) :=
  fun x => (List.perm_iff_count.mp (countingSort_perm arr)) x

theorem nil_thm : nil_prop := rfl

/-- Post-condition: the output is a sorted permutation of the input of the same
length, with the same multiplicities. -/
def Post_prop (arr result : List Int) : Prop :=
  sorted_prop arr result ∧ perm_prop arr result ∧ length_prop arr result ∧
    count_prop arr result

/-- Correctness: the pre-condition implies the post-condition. -/
theorem countingSort_correct_thm (arr : List Int) (_h : Pre arr) :
    Post_prop arr (countingSort arr) :=
  ⟨sorted_thm arr, perm_thm arr, length_thm arr, count_thm arr⟩

/-! ## Imperative implementation -/

/-- Increment the `i`-th entry of a bucket list (out-of-range indices are
ignored); this is `count[i] += 1`. -/
def incAt : List Nat → Nat → List Nat
  | [], _ => []
  | c :: cs, 0 => (c + 1) :: cs
  | c :: cs, i + 1 => c :: incAt cs i

/-- `min(arr)` as an imperative loop over `a :: as`. -/
def minLoop (a : Int) (as : List Int) : Int := Id.run do
  let mut mn := a
  for x in as do
    if x < mn then
      mn := x
  return mn

/-- `max(arr)` as an imperative loop over `a :: as`. -/
def maxLoop (a : Int) (as : List Int) : Int := Id.run do
  let mut mx := a
  for x in as do
    if mx < x then
      mx := x
  return mx

/-- The counting loop `for num in arr: count[num - min_val] += 1`. -/
def countLoop (mn : Int) (n : Nat) (arr : List Int) : List Nat := Id.run do
  let mut count : List Nat := List.replicate n 0
  for x in arr do
    count := incAt count (x - mn).toNat
  return count

/-- The output loop `for i in range(range_size): result.extend([i + min_val] * count[i])`. -/
def buildLoop (mn : Int) (count : List Nat) (n : Nat) : List Int := Id.run do
  let mut result : List Int := []
  for i in List.range n do
    result := result ++ List.replicate (count.getD i 0) (mn + (i : Int))
  return result

/-- Imperative counting sort, following the Python code statement by statement. -/
def countingSortImp (arr : List Int) : List Int := Id.run do
  match arr with
  | [] => return []
  | a :: as =>
      let mn := minLoop a as
      let mx := maxLoop a as
      let rangeSize := (mx - mn + 1).toNat
      let count := countLoop mn rangeSize (a :: as)
      return buildLoop mn count rangeSize

/-! ## Imperative unit tests -/

#eval countingSortImp [3, 1, 2]
#eval countingSortImp ([] : List Int)
#eval countingSortImp [3, 1, 4, 1, 2, 3]

example : countingSortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSortImp ([] : List Int) = [] := by native_decide
example : countingSortImp [1] = [1] := by native_decide
example : countingSortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSortImp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSortImp [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : countingSortImp [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example :
    countingSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
      = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : countingSortImp [3, -1, 2, -5, 0] = [-5, -1, 0, 2, 3] := by native_decide

/-! ## The imperative loops compute the functional operations -/

theorem minLoop_eq (a : Int) (as : List Int) : minLoop a as = lmin a as := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih =>
      have h : minLoop a (b :: bs) = minLoop (if b < a then b else a) bs := by
        simp only [minLoop, Id.run, List.forIn_cons, bind_pure_comp, map_pure]
        split <;> rfl
      rw [h, ih]
      rfl

theorem maxLoop_eq (a : Int) (as : List Int) : maxLoop a as = lmax a as := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih =>
      have h : maxLoop a (b :: bs) = maxLoop (if a < b then b else a) bs := by
        simp only [maxLoop, Id.run, List.forIn_cons, bind_pure_comp, map_pure]
        split <;> rfl
      rw [h, ih]
      rfl

theorem countLoop_eq (mn : Int) (n : Nat) (arr : List Int) :
    countLoop mn n arr
      = arr.foldl (fun c x => incAt c (x - mn).toNat) (List.replicate n 0) := by
  have gen : ∀ (l : List Int) (c : List Nat),
      (Id.run (forIn l c (fun x r => pure (ForInStep.yield (incAt r (x - mn).toNat)))))
        = l.foldl (fun c x => incAt c (x - mn).toNat) c := by
    intro l
    induction l with
    | nil => intro c; rfl
    | cons b bs ih =>
        intro c
        simp only [Id.run, List.forIn_cons, List.foldl_cons] at *
        exact ih _
  exact gen arr _

theorem buildLoop_eq (mn : Int) (count : List Nat) (n : Nat) :
    buildLoop mn count n
      = (List.range n).foldl
          (fun r i => r ++ List.replicate (count.getD i 0) (mn + (i : Int))) [] := by
  have gen : ∀ (l : List Nat) (r0 : List Int),
      (Id.run (forIn l r0 (fun i r =>
          pure (ForInStep.yield (r ++ List.replicate (count.getD i 0) (mn + (i : Int)))))))
        = l.foldl (fun r i => r ++ List.replicate (count.getD i 0) (mn + (i : Int))) r0 := by
    intro l
    induction l with
    | nil => intro r0; rfl
    | cons b bs ih =>
        intro r0
        simp only [Id.run, List.forIn_cons, List.foldl_cons] at *
        exact ih _
  exact gen _ _

/-! ## The bucket list computed by the imperative loop -/

theorem incAt_length (l : List Nat) (i : Nat) : (incAt l i).length = l.length := by
  induction l generalizing i with
  | nil => rfl
  | cons c cs ih =>
      cases i with
      | zero => rfl
      | succ i => simp [incAt, ih]

theorem getD_incAt (l : List Nat) (i j : Nat) :
    (incAt l i).getD j 0 = l.getD j 0 + (if i = j ∧ j < l.length then 1 else 0) := by
  induction l generalizing i j with
  | nil => simp [incAt]
  | cons c cs ih =>
      cases i with
      | zero =>
          cases j with
          | zero => simp [incAt]
          | succ j => simp [incAt]
      | succ i =>
          cases j with
          | zero => simp [incAt]
          | succ j => simpa [incAt] using ih i j

theorem getD_countFold (mn : Int) : ∀ (arr : List Int) (c : List Nat) (i : Nat),
    i < c.length → (∀ x ∈ arr, mn ≤ x ∧ (x - mn).toNat < c.length) →
    (arr.foldl (fun c x => incAt c (x - mn).toNat) c).getD i 0
      = c.getD i 0 + arr.count (mn + (i : Int)) := by
  intro arr
  induction arr with
  | nil => intro c i _ _; simp
  | cons y ys ih =>
      intro c i hi hmem
      have hy := hmem y (List.mem_cons_self ..)
      have hlen : (incAt c (y - mn).toNat).length = c.length := incAt_length _ _
      have hi' : i < (incAt c (y - mn).toNat).length := by omega
      have hmem' : ∀ x ∈ ys, mn ≤ x ∧ (x - mn).toNat < (incAt c (y - mn).toNat).length := by
        intro x hx
        have := hmem x (List.mem_cons_of_mem _ hx)
        omega
      rw [List.foldl_cons, ih _ i hi' hmem', getD_incAt]
      have hcount : (y :: ys).count (mn + (i : Int))
          = ys.count (mn + (i : Int)) + (if y = mn + (i : Int) then 1 else 0) := by
        simp [List.count_cons]
      rw [hcount]
      by_cases hEq : y = mn + (i : Int)
      · rw [if_pos hEq, if_pos (⟨by omega, hi⟩ : (y - mn).toNat = i ∧ i < c.length)]
        omega
      · rw [if_neg hEq, if_neg (fun (h : (y - mn).toNat = i ∧ i < c.length) => hEq (by omega))]
        omega

/-! ## Equivalence of the two implementations -/

theorem buildLoop_eq_build (mn : Int) (arr : List Int) (count : List Nat) :
    ∀ (n : Nat), (∀ i < n, count.getD i 0 = arr.count (mn + (i : Int))) →
      buildLoop mn count n = build mn arr n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hc
      have hstep : buildLoop mn count (n + 1)
          = buildLoop mn count n ++ List.replicate (count.getD n 0) (mn + (n : Int)) := by
        rw [buildLoop_eq, buildLoop_eq, List.range_succ, List.foldl_append]
        rfl
      rw [hstep, ih (fun i hi => hc i (by omega)), build, hc n (by omega)]

theorem countingSortImp_eq (arr : List Int) : countingSortImp arr = countingSort arr := by
  cases arr with
  | nil => rfl
  | cons a as =>
      have hmin : minLoop a as = lmin a as := minLoop_eq a as
      have hmax : maxLoop a as = lmax a as := maxLoop_eq a as
      set mn := lmin a as with hmn
      set n := (lmax a as - mn + 1).toNat with hn
      have himp : countingSortImp (a :: as)
          = buildLoop mn (countLoop mn n (a :: as)) n := by
        simp only [countingSortImp, Id.run, hmin, hmax]
        rfl
      have hfun : countingSort (a :: as) = build mn (a :: as) n := rfl
      have hrange : ∀ x ∈ (a :: as), mn ≤ x ∧ (x - mn).toNat < (List.replicate n 0).length := by
        intro x hx
        have := mem_range_of_mem a as x hx
        rw [List.length_replicate]
        omega
      have hcount : ∀ i < n, (countLoop mn n (a :: as)).getD i 0
          = (a :: as).count (mn + (i : Int)) := by
        intro i hi
        rw [countLoop_eq,
          getD_countFold mn (a :: as) (List.replicate n 0) i (by simpa using hi) hrange]
        simp
      rw [himp, hfun, buildLoop_eq_build mn (a :: as) _ n hcount]

/-- Equivalence theorem: the functional and the imperative implementations agree. -/
theorem equiv_thm : ∀ arr : List Int, countingSort arr = countingSortImp arr :=
  fun arr => (countingSortImp_eq arr).symm

/-- The imperative implementation therefore also satisfies the post-condition. -/
theorem countingSortImp_correct_thm (arr : List Int) (h : Pre arr) :
    Post_prop arr (countingSortImp arr) := by
  rw [← equiv_thm arr]
  exact countingSort_correct_thm arr h

end counting_sort
