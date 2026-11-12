import Mathlib

/-!
# Counting Sort — Lean 4 formalization

Formalization of the Python `counting_sort` program (sorting `List[int]`, supporting
negative values via a shift by the minimum element).

The functional model `countingSort` sorts a `List Int` by counting, for every value
`v` in the range `[min, max]`, the occurrences of `v` in the input and emitting that
many copies in increasing order — exactly the semantics of the Python code.

We prove:
* `sorted_thm` — the output is sorted;
* `perm_thm` — the output is a permutation of the input (hence `length_thm`);
* `correctness_thm` — the precondition implies the postcondition;
* `equivalence_thm` — the imperative `Id.run` implementation agrees with the functional one.

Note on the Python precondition `pre`: it only checks the *dynamic* type of the input
(`isinstance(arr, list) and all(isinstance(x, int))`). In Lean the input has type
`List Int`, so the precondition is statically guaranteed and `Pre` is `True`.
Consequently the `ValueError` path of the Python program is unreachable in the Lean
model: the input `[1, 2.5]` of the Python negative test is ill-typed here.
-/

namespace counting_sort

/-- Number of occurrences of `v` in `xs` (own definition, for full definitional control). -/
def countOcc (v : Int) : List Int → Nat
  | [] => 0
  | x :: xs => (if x = v then 1 else 0) + countOcc v xs

/-- Minimum of a nonempty list (`0` default for the empty list). -/
def listMin : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl min x

/-- Maximum of a nonempty list (`0` default for the empty list). -/
def listMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

/-- Functional counting sort, mirroring the Python program:
shift by `min` so negatives are supported, count occurrences of each value in
`[min, max]`, then emit `count` copies of each value in increasing order. -/
def countingSort (xs : List Int) : List Int :=
  if xs = [] then []
  else (List.range ((listMax xs - listMin xs + 1).toNat)).flatMap
    (fun i : Nat => List.replicate (countOcc (listMin xs + (i : Int)) xs) (listMin xs + (i : Int)))

/-- Executable sortedness checker (Boolean counterpart of `List.Sorted (· ≤ ·)`). -/
def checkSorted : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => decide (x ≤ y) && checkSorted (y :: xs)

/-! ## Unit tests (mirroring the Python test suite) -/

example : countingSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : countingSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : countingSort ([] : List Int) = ([] : List Int) := by native_decide
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
example : countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
    = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : countingSort [-3, -1, -2] = [-3, -2, -1] := by native_decide
example : countingSort [-2, 3, -2, 0] = [-2, -2, 0, 3] := by native_decide

#eval countingSort [3, 1, 2]
#eval countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
#eval countingSort [-5, 3, -5, 0, 2]

/-! ## Precondition -/

/-- The Python `pre` checks `isinstance(arr, list) and all(isinstance(x, int))`.
For a Lean `List Int` this is statically guaranteed, so `Pre` holds trivially. -/
def Pre (_xs : List Int) : Prop := True

/-! ## Properties and their theorems -/

/-- The output of `countingSort xs` is sorted. -/
def sorted_prop (xs : List Int) : Prop := (countingSort xs).Sorted (· ≤ ·)

/-- The output of `countingSort xs` is a permutation of `xs`. -/
def perm_prop (xs : List Int) : Prop := List.Perm (countingSort xs) xs

/-- The output of `countingSort xs` has the same length as `xs`. -/
def length_prop (xs : List Int) : Prop := (countingSort xs).length = xs.length

/-- `foldl min` starting from the head bounds every element from below. -/
theorem foldl_min_le : ∀ (xs : List Int) (x y : Int), y ∈ x :: xs → xs.foldl min x ≤ y := by
  intro xs
  induction xs with
  | nil =>
    intro x y hy
    rw [List.mem_singleton] at hy
    subst hy
    exact le_refl _
  | cons z zs ih =>
    intro x y hy
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hy with h1 | h1
    · rw [h1]
      exact le_trans (ih (min x z) (min x z) List.mem_cons_self) (min_le_left x z)
    · rcases List.mem_cons.mp h1 with h2 | h2
      · rw [h2]
        exact le_trans (ih (min x z) (min x z) List.mem_cons_self) (min_le_right x z)
      · exact ih (min x z) y (List.mem_cons_of_mem _ h2)

/-- `foldl max` starting from the head bounds every element from above. -/
theorem le_foldl_max : ∀ (xs : List Int) (x y : Int), y ∈ x :: xs → y ≤ xs.foldl max x := by
  intro xs
  induction xs with
  | nil =>
    intro x y hy
    rw [List.mem_singleton] at hy
    subst hy
    exact le_refl _
  | cons z zs ih =>
    intro x y hy
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hy with h1 | h1
    · rw [h1]
      exact le_trans (le_max_left x z) (ih (max x z) (max x z) List.mem_cons_self)
    · rcases List.mem_cons.mp h1 with h2 | h2
      · rw [h2]
        exact le_trans (le_max_right x z) (ih (max x z) (max x z) List.mem_cons_self)
      · exact ih (max x z) y (List.mem_cons_of_mem _ h2)

theorem countOcc_append (v : Int) (l₁ l₂ : List Int) :
    countOcc v (l₁ ++ l₂) = countOcc v l₁ + countOcc v l₂ := by
  induction l₁ with
  | nil => simp [countOcc]
  | cons x xs ih =>
    simp only [List.cons_append, countOcc]
    rw [ih]
    by_cases h : x = v
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

theorem countOcc_replicate (a v : Int) (k : Nat) :
    countOcc a (List.replicate k v) = if a = v then k else 0 := by
  induction k with
  | zero =>
    by_cases h : a = v
    · rw [if_pos h]
      exact rfl
    · rw [if_neg h]
      exact rfl
  | succ k ih =>
    by_cases h : a = v
    · rw [List.replicate_succ, if_pos h]
      simp only [countOcc]
      rw [if_pos h.symm, ih, if_pos h]
      omega
    · rw [List.replicate_succ, if_neg h]
      simp only [countOcc]
      rw [if_neg (fun hh => h hh.symm), ih, if_neg h]

theorem countOcc_eq_zero (a : Int) (xs : List Int) : countOcc a xs = 0 ↔ a ∉ xs := by
  induction xs with
  | nil => simp [countOcc]
  | cons x xs ih =>
    simp only [countOcc, List.mem_cons]
    by_cases h : x = a
    · rw [if_pos h]
      constructor
      · intro hh; exfalso; omega
      · intro hh; exact absurd (Or.inl h.symm) hh
    · rw [if_neg h, Nat.zero_add, ih]
      constructor
      · intro hna hdisj
        rcases hdisj with h1 | h2
        · exact h h1.symm
        · exact hna h2
      · intro hnn ha
        exact hnn (Or.inr ha)

/-- Counting in the block-list: value `a` occurs iff it lies in `[s, s + n)`, and then
it occurs `c (a - s).toNat` times. -/
theorem countOcc_flatMap_replicate (c : Nat → Nat) (s : Int) :
    ∀ (n : Nat) (a : Int),
      countOcc a ((List.range n).flatMap (fun i => List.replicate (c i) (s + (i : Int)))) =
        if s ≤ a ∧ (a - s).toNat < n then c (a - s).toNat else 0 := by
  intro n
  induction n with
  | zero =>
    intro a
    rw [if_neg (fun hh => Nat.not_lt_zero _ hh.2)]
    exact rfl
  | succ m ih =>
    intro a
    have hm : ((m : Int)).toNat = m := Int.toNat_natCast m
    rw [List.range_succ, List.flatMap_append, countOcc_append, List.flatMap_singleton,
      ih a, countOcc_replicate]
    by_cases h1 : s ≤ a
    · by_cases h2 : (a - s).toNat < m
      · have h3 : a ≠ s + (m : Int) := fun hh => by omega
        have h5 : (a - s).toNat < m + 1 := by omega
        rw [if_pos ⟨h1, h2⟩, if_neg h3, if_pos ⟨h1, h5⟩]
        omega
      · by_cases h3 : a = s + (m : Int)
        · rw [if_neg (fun hh => h2 hh.2), if_pos h3]
          subst h3
          have hb1 : s ≤ s + (m : Int) := by omega
          have hb2 : (s + (m : Int) - s).toNat < m + 1 := by omega
          rw [if_pos ⟨hb1, hb2⟩]
          have e : s + (m : Int) - s = (m : Int) := by ring
          rw [e, Int.toNat_natCast, Nat.zero_add]
        · rw [if_neg (fun hh => h2 hh.2), if_neg h3, if_neg (fun hh => by omega)]
    · have h3 : a ≠ s + (m : Int) := fun hh => by omega
      rw [if_neg (fun hh => h1 hh.1), if_neg h3, if_neg (fun hh => h1 hh.1)]

theorem countOcc_eq_List_count (a : Int) (xs : List Int) : countOcc a xs = List.count a xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [countOcc]
    rw [List.count_cons]
    by_cases h : x = a
    · rw [if_pos h, if_pos (beq_iff_eq.mpr h)]
      omega
    · rw [if_neg h, if_neg (fun hb => h (beq_iff_eq.mp hb))]
      omega

theorem sorted_replicate' (k : Nat) (v : Int) : (List.replicate k v).Sorted (· ≤ ·) := by
  induction k with
  | zero => exact List.sorted_nil
  | succ k ih =>
    rw [List.replicate_succ, List.sorted_cons]
    refine ⟨fun b hb => ?_, ih⟩
    rw [List.eq_of_mem_replicate hb]

theorem sorted_append' {l₁ l₂ : List Int} :
    l₁.Sorted (· ≤ ·) → l₂.Sorted (· ≤ ·) → (∀ a ∈ l₁, ∀ b ∈ l₂, a ≤ b) →
      (l₁ ++ l₂).Sorted (· ≤ ·) := by
  induction l₁ with
  | nil => intro _ h2 _; exact h2
  | cons x xs ih =>
    intro h1 h2 h3
    rw [List.cons_append, List.sorted_cons]
    rw [List.sorted_cons] at h1
    refine ⟨fun b hb => ?_, ih h1.2 h2 (fun a ha b hb => h3 a (List.mem_cons_of_mem _ ha) b hb)⟩
    rw [List.mem_append] at hb
    rcases hb with hb | hb
    · exact h1.1 b hb
    · exact h3 x List.mem_cons_self b hb

/-- The block-list is sorted, and every element lies in `[s, s + n]`. -/
theorem sorted_flatMap_replicate (c : Nat → Nat) (s : Int) (n : Nat) :
    ((List.range n).flatMap (fun i => List.replicate (c i) (s + (i : Int)))).Sorted (· ≤ ·) ∧
    ∀ a : Int, a ∈ (List.range n).flatMap (fun i => List.replicate (c i) (s + (i : Int))) →
      s ≤ a ∧ a ≤ s + (n : Int) := by
  induction n with
  | zero =>
    constructor
    · rw [List.range_zero]
      exact List.sorted_nil
    · intro a ha
      rw [List.range_zero] at ha
      simp at ha
  | succ m ih =>
    obtain ⟨ihs, ihb⟩ := ih
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    constructor
    · exact sorted_append' ihs (sorted_replicate' (c m) (s + (m : Int)))
        (fun a ha b hb => by
          obtain rfl := List.eq_of_mem_replicate hb
          obtain ⟨ha1, ha2⟩ := ihb a ha
          omega)
    · intro a ha
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · obtain ⟨ha1, ha2⟩ := ihb a ha
        exact ⟨ha1, by omega⟩
      · obtain rfl := List.eq_of_mem_replicate ha
        exact ⟨by omega, by omega⟩

theorem countingSort_sorted (xs : List Int) : (countingSort xs).Sorted (· ≤ ·) := by
  by_cases h : xs = []
  · subst h
    unfold countingSort
    rw [if_pos rfl]
    exact List.sorted_nil
  · unfold countingSort
    rw [if_neg h]
    exact (sorted_flatMap_replicate (fun i => countOcc (listMin xs + (i : Int)) xs)
      (listMin xs) _).1

/-- The output contains exactly as many copies of every value as the input does. -/
theorem countingSort_countOcc (xs : List Int) (a : Int) :
    countOcc a (countingSort xs) = countOcc a xs := by
  by_cases h : xs = []
  · subst h
    unfold countingSort
    rw [if_pos rfl]
  · obtain ⟨x, xs', hxs⟩ := List.exists_cons_of_ne_nil h
    subst hxs
    have hmin : ∀ y ∈ x :: xs', listMin (x :: xs') ≤ y := fun y hy => foldl_min_le xs' x y hy
    have hmax : ∀ y ∈ x :: xs', y ≤ listMax (x :: xs') := fun y hy => le_foldl_max xs' x y hy
    unfold countingSort
    rw [if_neg h]
    rw [countOcc_flatMap_replicate]
    by_cases hin : listMin (x :: xs') ≤ a ∧
      (a - listMin (x :: xs')).toNat < (listMax (x :: xs') - listMin (x :: xs') + 1).toNat
    · rw [if_pos hin]
      show countOcc (listMin (x :: xs') + ((a - listMin (x :: xs')).toNat : Int)) (x :: xs')
        = countOcc a (x :: xs')
      have h0 : 0 ≤ a - listMin (x :: xs') := by omega
      have e : ((a - listMin (x :: xs')).toNat : Int) = a - listMin (x :: xs') :=
        Int.toNat_of_nonneg h0
      have e2 : listMin (x :: xs') + ((a - listMin (x :: xs')).toNat : Int) = a := by omega
      rw [e2]
    · rw [if_neg hin]
      symm
      rw [countOcc_eq_zero]
      intro ha
      have hb1 := hmin a ha
      have hb2 := hmax a ha
      exact hin ⟨hb1, by omega⟩

theorem countingSort_perm (xs : List Int) : List.Perm (countingSort xs) xs := by
  rw [List.perm_iff_count]
  intro a
  rw [← countOcc_eq_List_count a xs, ← countOcc_eq_List_count a (countingSort xs)]
  exact countingSort_countOcc xs a

theorem sorted_thm (xs : List Int) : sorted_prop xs := countingSort_sorted xs

theorem perm_thm (xs : List Int) : perm_prop xs := countingSort_perm xs

theorem length_thm (xs : List Int) : length_prop xs := (countingSort_perm xs).length_eq

/-! ## Postcondition -/

/-- Postcondition of `countingSort`: the output is sorted, is a permutation of the
input, and has the same length as the input. -/
def Post_prop (xs : List Int) : Prop :=
  sorted_prop xs ∧ perm_prop xs ∧ length_prop xs

/-! ## Property-based tests -/

-- PBT for `sorted_prop` (executable form via `checkSorted`)
#eval Plausible.Testable.check (∀ xs : List Int, checkSorted (countingSort xs) = true)
-- PBT for `perm_prop` (executable form: equal occurrence counts for every value)
#eval Plausible.Testable.check (∀ xs : List Int, ∀ v : Int,
  countOcc v (countingSort xs) = countOcc v xs)
-- PBT for `length_prop`
#eval Plausible.Testable.check (∀ xs : List Int, (countingSort xs).length = xs.length)
-- PBT for the postcondition `Post_prop` (executable form)
#eval Plausible.Testable.check (∀ xs : List Int,
  (checkSorted (countingSort xs) && ((countingSort xs).length == xs.length)) = true)

-- Bounded PBTs (exhaustive small cases) for `sorted_prop`, `length_prop` and `Post_prop`
example : (List.range 30).all (fun n =>
    let xs := (List.range n).map (fun k => (k : Int) % 7 - 3)
    checkSorted (countingSort xs)) = true := by native_decide

example : (List.range 30).all (fun n =>
    let xs := (List.range n).map (fun k => (k : Int) % 7 - 3)
    (checkSorted (countingSort xs) && ((countingSort xs).length == xs.length) &&
      (List.range 8).all (fun v =>
        countOcc ((v : Int) - 4) (countingSort xs) == countOcc ((v : Int) - 4) xs))) = true := by
  native_decide

/-! ## Correctness theorem: Pre → Post -/

theorem correctness_thm (xs : List Int) : Pre xs → Post_prop xs := by
  intro _
  exact ⟨sorted_thm xs, perm_thm xs, length_thm xs⟩

/-! ## Imperative implementation (`Id.run` with mutable state) -/

/-- Emit `c` copies of `v` using a mutable accumulator inside `Id.run`
(mirrors the Python `result.extend([i + min_val] * count[i])` step). -/
def mkBlock (c : Nat) (v : Int) : List Int :=
  Id.run do
    let mut block : List Int := []
    for _ in List.range c do
      block := block ++ [v]
    return block

/-- Imperative counting sort: mutable accumulation of the result inside `Id.run`. -/
def countingSortImp (xs : List Int) : List Int :=
  if xs = [] then []
  else Id.run do
    let mut out : List Int := []
    for i in List.range ((listMax xs - listMin xs + 1).toNat) do
      out := out ++ mkBlock (countOcc (listMin xs + (i : Int)) xs) (listMin xs + (i : Int))
    return out

/-! ## Imperative tests -/

example : countingSortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSortImp ([] : List Int) = ([] : List Int) := by native_decide
example : countingSortImp [1] = [1] := by native_decide
example : countingSortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSortImp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSortImp [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : countingSortImp [-3, -1, -2] = [-3, -2, -1] := by native_decide
example : countingSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
    = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

#eval countingSortImp [3, 7, 1, 9, 2, 8, 4, 6, 5]
#eval countingSortImp [0, 3, 1, 0, 2]

/-! ## Equivalence of functional and imperative implementations -/

/-- A `for` loop over a list in `Id`, accumulating with `g`, is exactly `List.foldl`. -/
theorem id_for_foldl {α β : Type} (xs : List α) (g : β → α → β) (init : β) :
    (Id.run do
      let mut acc := init
      for x in xs do
        acc := g acc x
      return acc) = xs.foldl g init := by
  induction xs generalizing init with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, List.forIn_cons, Id.run_bind, Id.run_pure]
    exact ih _

theorem foldl_append_eq_flatMap {α β : Type} (f : α → List β) (l : List α) (init : List β) :
    l.foldl (fun acc x => acc ++ f x) init = init ++ l.flatMap f := by
  induction l generalizing init with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, List.flatMap_cons]
    rw [ih, List.append_assoc]

theorem flatMap_const_replicate (c : Nat) (v : Int) :
    ((List.range c).flatMap fun _ => [v]) = List.replicate c v := by
  induction c with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih,
      List.replicate_add, List.replicate_one]

theorem mkBlock_eq (c : Nat) (v : Int) : mkBlock c v = List.replicate c v := by
  unfold mkBlock
  rw [id_for_foldl, foldl_append_eq_flatMap, List.nil_append, flatMap_const_replicate]

theorem equivalence_thm (xs : List Int) : countingSortImp xs = countingSort xs := by
  by_cases h : xs = []
  · subst h
    unfold countingSortImp countingSort
    rw [if_pos rfl, if_pos rfl]
  · unfold countingSortImp countingSort
    rw [if_neg h, if_neg h, id_for_foldl, foldl_append_eq_flatMap, List.nil_append]
    simp only [mkBlock_eq]

end counting_sort
