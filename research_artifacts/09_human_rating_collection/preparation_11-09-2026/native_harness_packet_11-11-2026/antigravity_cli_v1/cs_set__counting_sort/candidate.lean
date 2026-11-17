import Mathlib

/-!
# Counting Sort Formalization

This module formalizes the Python `counting_sort` algorithm for a list of integers (`List Int`),
including support for negative integers via range shifting (`min_val` offset).

It includes:
1. Functional implementation (`counting_sort`) faithfully modeling the shift and count array logic.
2. Unit tests covering basic cases, edge cases, duplicates, negative integers, and larger inputs.
3. Pre-condition (`Pre`) and formal properties (`empty_prop`, `count_prop`, `perm_prop`,
   `sorted_prop`, `chain_sorted_prop`, `index_sorted_prop`, `length_prop`, `mem_prop`,
   `empty_iff_prop`, `bounds_prop`, `head_min_prop`, `getLast_max_prop`, `already_sorted_prop`,
   `singleton_prop`, `idempotent_prop`, `perm_invariant_prop`, `reverse_prop`, `replicate_prop`,
   `shift_prop`, `eq_mergeSort_prop`) with complete machine-checked proofs.
4. Post-condition (`Post_prop`) and property-based tests (randomized via `Plausible` and bounded exhaustive checks).
5. Main correctness theorem (`Pre arr → Post_prop arr`).
6. Imperative implementation (`counting_sort_imp`) using `Id.run do` and mutable state,
   imperative unit tests, and a complete equivalence proof (`counting_sort arr = counting_sort_imp arr`).
-/

set_option linter.dupNamespace false

namespace counting_sort

/-! ## 1. Functional Implementation -/

/-- Helper step that increments the count at index `(num - min_val).toNat`. -/
def countStep (min_val : Int) (c : List Nat) (num : Int) : List Nat :=
  let idx := (num - min_val).toNat
  c.set idx (c.getD idx 0 + 1)

/-- Functional implementation of counting sort for a list of integers (supports negatives via shift). -/
def counting_sort (arr : List Int) : List Int :=
  match arr with
  | [] => []
  | x :: xs =>
    let max_val := xs.foldl max x
    let min_val := xs.foldl min x
    let range_size := (max_val - min_val + 1).toNat
    let count := (x :: xs).foldl (countStep min_val) (List.replicate range_size 0)
    (List.range range_size).flatMap (fun i =>
      List.replicate (count.getD i 0) ((i : Int) + min_val))

/-! ## 2. Unit Tests -/

-- Basic functionality tests
example : counting_sort [3, 1, 2] = [1, 2, 3] := by native_decide
example : counting_sort [1, 2, 3] = [1, 2, 3] := by native_decide
example : counting_sort [2, 1, 3] = [1, 2, 3] := by native_decide

-- Edge cases
example : counting_sort [] = [] := by native_decide
example : counting_sort [1] = [1] := by native_decide

-- Larger arrays
example : counting_sort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : counting_sort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : counting_sort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide

-- Two elements
example : counting_sort [2, 1] = [1, 2] := by native_decide
example : counting_sort [1, 2] = [1, 2] := by native_decide

-- Duplicates
example : counting_sort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : counting_sort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : counting_sort [3, 1, 2, 1, 3, 2] = [1, 1, 2, 2, 3, 3] := by native_decide
example : counting_sort [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide

-- Already sorted and reverse sorted
example : counting_sort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : counting_sort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide

-- Random order and with zeros
example : counting_sort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : counting_sort [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide

-- Larger test case
example : counting_sort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

-- Negative numbers tests (shift support)
example : counting_sort [-3, -1, -2] = [-3, -2, -1] := by native_decide
example : counting_sort [-5, 0, 3, -2, 1, -5] = [-5, -5, -2, 0, 1, 3] := by native_decide

#eval counting_sort [3, 1, 2]
#eval counting_sort ([] : List Int)
#eval counting_sort [1]
#eval counting_sort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
#eval counting_sort [-5, 0, 3, -2, 1, -5]

/-! ## 3. Pre-condition -/

/-- Executable boolean precondition check (always `true` for statically typed `List Int`). -/
def pre (_arr : List Int) : Bool := true

/-- Pre-condition predicate: in Lean's static type system, `arr : List Int` guarantees
that the input is a list of integers. -/
def Pre (_arr : List Int) : Prop := True

@[simp]
theorem Pre_trivial (arr : List Int) : Pre arr := trivial

/-! ## 4. Structural Lemmas for Counting Sort -/

theorem getD_set_eq (c : List Nat) (idx val i : Nat) (hi : i < c.length) :
    (c.set idx val).getD i 0 = if idx = i then val else c.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with h1 h2
  · subst h1; simp
  · omega
  · rfl

theorem getD_replicate_zero (n i : Nat) :
    (List.replicate n 0).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

theorem countStep_length (min_val : Int) (c : List Nat) (num : Int) :
    (countStep min_val c num).length = c.length := by
  simp [countStep]

theorem foldl_countStep_length (min_val : Int) (l : List Int) (c : List Nat) :
    (l.foldl (countStep min_val) c).length = c.length := by
  induction l generalizing c with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, countStep_length]

theorem foldl_countStep_getD (min_val : Int) (l : List Int) (c : List Nat) (i : Nat)
    (hi : i < c.length) (hmin : ∀ x ∈ l, min_val ≤ x) :
    (l.foldl (countStep min_val) c).getD i 0 =
      c.getD i 0 + l.count ((i : Int) + min_val) := by
  induction l generalizing c with
  | nil => simp
  | cons x xs ih =>
    have hx : min_val ≤ x := hmin x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, min_val ≤ y := fun y hy => hmin y (List.mem_cons_of_mem x hy)
    simp only [List.foldl_cons, List.count_cons, beq_iff_eq]
    rw [ih (countStep min_val c x) (by rw [countStep_length]; exact hi) hxs]
    unfold countStep
    rw [getD_set_eq c _ _ i hi]
    split_ifs with h1 h2 h2
    · subst h1; omega
    · exfalso; apply h2; omega
    · exfalso; apply h1; omega
    · omega

theorem flatMap_range_count (min_val : Int) (f : Nat → Nat) (n : Nat) (v : Int) :
    ((List.range n).flatMap (fun i => List.replicate (f i) ((i : Int) + min_val))).count v =
      if min_val ≤ v ∧ v < min_val + (n : Int) then f (v - min_val).toNat else 0 := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.flatMap_nil, List.count_nil, Nat.cast_zero, add_zero]
    split_ifs with h <;> omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.count_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_replicate,
      beq_iff_eq, Nat.cast_add, Nat.cast_one]
    split_ifs with h1 h2 h3
    · exfalso; omega
    · exfalso; omega
    · omega
    · exfalso; omega
    · have : (v - min_val).toNat = n := by omega
      rw [this]; omega
    · exfalso; omega
    · exfalso; omega
    · rfl

theorem flatMap_range_sorted (min_val : Int) (f : Nat → Nat) (n : Nat) :
    List.Sorted (· ≤ ·) ((List.range n).flatMap (fun i => List.replicate (f i) ((i : Int) + min_val))) := by
  induction n with
  | zero => simp [List.Sorted]
  | succ n ih =>
    rw [List.Sorted, List.range_succ, List.flatMap_append, List.pairwise_append]
    refine ⟨ih, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.pairwise_replicate.mpr (Or.inr (Int.le_refl _))
    · intro a ha b hb
      simp only [List.mem_flatMap, List.mem_range, List.mem_replicate, List.flatMap_cons,
        List.flatMap_nil, List.append_nil] at ha hb
      rcases ha with ⟨i, hi, _, rfl⟩
      rcases hb with ⟨_, rfl⟩
      omega

theorem foldl_min_le_init (l : List Int) (init : Int) :
    l.foldl min init ≤ init := by
  induction l generalizing init with
  | nil => exact Int.le_refl _
  | cons y ys ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (ih (min init y)) (min_le_left init y)

theorem foldl_min_le_mem (l : List Int) (init : Int) (z : Int) (hz : z ∈ l) :
    l.foldl min init ≤ z := by
  induction l generalizing init with
  | nil => contradiction
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hz with rfl | hmem
    · exact Int.le_trans (foldl_min_le_init ys (min init z)) (min_le_right init z)
    · exact ih (min init y) hmem

theorem init_le_foldl_max (l : List Int) (init : Int) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact Int.le_refl _
  | cons y ys ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (le_max_left init y) (ih (max init y))

theorem mem_le_foldl_max (l : List Int) (init : Int) (z : Int) (hz : z ∈ l) :
    z ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => contradiction
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hz with rfl | hmem
    · exact Int.le_trans (le_max_right init z) (init_le_foldl_max ys (max init z))
    · exact ih (max init y) hmem

theorem mem_cons_bounds (x : Int) (xs : List Int) (z : Int) (hz : z ∈ x :: xs) :
    xs.foldl min x ≤ z ∧ z ≤ xs.foldl max x := by
  rcases List.mem_cons.mp hz with rfl | hmem
  · exact ⟨foldl_min_le_init xs z, init_le_foldl_max xs z⟩
  · exact ⟨foldl_min_le_mem xs x z hmem, mem_le_foldl_max xs x z hmem⟩

theorem foldl_min_mem (l : List Int) (x : Int) :
    l.foldl min x ∈ x :: l := by
  induction l generalizing x with
  | nil => exact List.mem_cons_self ..
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp (ih (min x y)) with heq | hmem
    · rw [heq]
      rcases min_choice x y with hmin | hmin <;> rw [hmin]
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem x (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem x (List.mem_cons_of_mem y hmem)

theorem foldl_max_mem (l : List Int) (x : Int) :
    l.foldl max x ∈ x :: l := by
  induction l generalizing x with
  | nil => exact List.mem_cons_self ..
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp (ih (max x y)) with heq | hmem
    · rw [heq]
      rcases max_choice x y with hmax | hmax <;> rw [hmax]
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem x (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem x (List.mem_cons_of_mem y hmem)

theorem sorted_head_le {l : List Int} (hs : List.Sorted (· ≤ ·) l) (hne : l ≠ [])
    {z : Int} (hz : z ∈ l) : l.head hne ≤ z := by
  cases l with
  | nil => contradiction
  | cons a t =>
    simp only [List.head_cons]
    rw [List.Sorted, List.pairwise_cons] at hs
    rcases List.mem_cons.mp hz with rfl | hmem
    · exact Int.le_refl _
    · exact hs.1 z hmem

theorem sorted_le_getLast {l : List Int} (hs : List.Sorted (· ≤ ·) l) (hne : l ≠ [])
    {z : Int} (hz : z ∈ l) : z ≤ l.getLast hne := by
  induction l with
  | nil => contradiction
  | cons a t ih =>
    cases t with
    | nil =>
      simp only [List.mem_singleton] at hz
      simp [hz]
    | cons b bs =>
      have hne' : b :: bs ≠ [] := List.cons_ne_nil b bs
      rw [List.getLast_cons hne']
      rw [List.Sorted, List.pairwise_cons] at hs
      rcases List.mem_cons.mp hz with rfl | hmem
      · exact hs.1 ((b :: bs).getLast hne') (List.getLast_mem hne')
      · exact ih hs.2 hne' hmem

/-! ## 5. Property Propositions and Theorems -/

/-- Property 1: Sorting the empty list yields the empty list. -/
def empty_prop : Prop :=
  counting_sort [] = []

theorem empty_thm : empty_prop := rfl

/-- Property 2: `counting_sort` preserves the occurrence count of every integer. -/
def count_prop (arr : List Int) : Prop :=
  ∀ v : Int, (counting_sort arr).count v = arr.count v

theorem count_thm (arr : List Int) : count_prop arr := by
  intro v
  cases arr with
  | nil => rfl
  | cons x xs =>
    unfold counting_sort
    dsimp only
    rw [flatMap_range_count]
    have hmin_x : xs.foldl min x ≤ x := foldl_min_le_init xs x
    have hmax_x : x ≤ xs.foldl max x := init_le_foldl_max xs x
    have hmin_all : ∀ z ∈ x :: xs, xs.foldl min x ≤ z :=
      fun z hz => (mem_cons_bounds x xs z hz).1
    split_ifs with h
    · have hi : (v - xs.foldl min x).toNat < (xs.foldl max x - xs.foldl min x + 1).toNat := by omega
      have hlen : (v - xs.foldl min x).toNat <
          (List.replicate (xs.foldl max x - xs.foldl min x + 1).toNat 0).length := by
        simp [hi]
      rw [foldl_countStep_getD (xs.foldl min x) (x :: xs) _ _ hlen hmin_all]
      rw [getD_replicate_zero, Nat.zero_add]
      congr 1
      omega
    · symm
      rw [List.count_eq_zero]
      intro hv
      have hb := mem_cons_bounds x xs v hv
      omega

/-- Property 3: The output of `counting_sort` is a permutation of the input list. -/
def perm_prop (arr : List Int) : Prop :=
  (counting_sort arr).Perm arr

theorem perm_thm (arr : List Int) : perm_prop arr := by
  rw [perm_prop, List.perm_iff_count]
  exact count_thm arr

/-- Property 4: The output of `counting_sort` is sorted in non-decreasing order (`List.Sorted (· ≤ ·)`). -/
def sorted_prop (arr : List Int) : Prop :=
  List.Sorted (· ≤ ·) (counting_sort arr)

theorem sorted_thm (arr : List Int) : sorted_prop arr := by
  cases arr with
  | nil => simp [sorted_prop, counting_sort, List.Sorted]
  | cons x xs =>
    unfold sorted_prop counting_sort
    dsimp only
    exact flatMap_range_sorted _ _ _

/-- Property 5: Adjacent elements in `counting_sort arr` are in non-decreasing order (`List.Chain' (· ≤ ·)`). -/
def chain_sorted_prop (arr : List Int) : Prop :=
  List.Chain' (· ≤ ·) (counting_sort arr)

theorem chain_sorted_thm (arr : List Int) : chain_sorted_prop arr :=
  (sorted_thm arr).chain'

/-- Property 6: Any two valid indices `i ≤ j` in `counting_sort arr` satisfy `(counting_sort arr)[i] ≤ (counting_sort arr)[j]`. -/
def index_sorted_prop (arr : List Int) : Prop :=
  ∀ (i j : Nat) (hi : i < (counting_sort arr).length) (hj : j < (counting_sort arr).length),
    i ≤ j → (counting_sort arr)[i] ≤ (counting_sort arr)[j]

theorem index_sorted_thm (arr : List Int) : index_sorted_prop arr := by
  intro i j hi hj hij
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Int.le_refl _
  · exact List.pairwise_iff_getElem.mp (sorted_thm arr) i j hi hj hlt

/-- Property 7: `counting_sort` preserves the length of the input list. -/
def length_prop (arr : List Int) : Prop :=
  (counting_sort arr).length = arr.length

theorem length_thm (arr : List Int) : length_prop arr :=
  (perm_thm arr).length_eq

/-- Property 8: `counting_sort` preserves element membership. -/
def mem_prop (arr : List Int) : Prop :=
  ∀ x : Int, x ∈ counting_sort arr ↔ x ∈ arr

theorem mem_thm (arr : List Int) : mem_prop arr :=
  fun _ => (perm_thm arr).mem_iff

/-- Property 9: The sorted result is empty if and only if the input list is empty. -/
def empty_iff_prop (arr : List Int) : Prop :=
  counting_sort arr = [] ↔ arr = []

theorem empty_iff_thm (arr : List Int) : empty_iff_prop arr := by
  rw [empty_iff_prop, ← List.length_eq_zero_iff, ← List.length_eq_zero_iff, length_thm]

/-- Property 10: For any non-empty input `x :: xs`, every element of `counting_sort (x :: xs)`
lies between the minimum (`xs.foldl min x`) and maximum (`xs.foldl max x`) of the input. -/
def bounds_prop (arr : List Int) : Prop :=
  match arr with
  | [] => counting_sort arr = []
  | x :: xs => ∀ y ∈ counting_sort (x :: xs), xs.foldl min x ≤ y ∧ y ≤ xs.foldl max x

theorem bounds_thm (arr : List Int) : bounds_prop arr := by
  cases arr with
  | nil => rfl
  | cons x xs =>
    intro y hy
    rw [mem_thm (x :: xs) y] at hy
    exact mem_cons_bounds x xs y hy

/-- Property 11: The first element (`head?`) of `counting_sort arr` is the minimum element of `arr`. -/
def head_min_prop (arr : List Int) : Prop :=
  match arr with
  | [] => (counting_sort arr).head? = none
  | x :: xs => (counting_sort (x :: xs)).head? = some (xs.foldl min x)

theorem head_min_thm (arr : List Int) : head_min_prop arr := by
  cases arr with
  | nil => rfl
  | cons x xs =>
    dsimp only [head_min_prop]
    have hne : counting_sort (x :: xs) ≠ [] := by
      intro h
      exact List.cons_ne_nil x xs ((empty_iff_thm (x :: xs)).mp h)
    rw [List.head?_eq_some_head hne, Option.some.injEq]
    have hle1 : xs.foldl min x ≤ (counting_sort (x :: xs)).head hne :=
      (bounds_thm (x :: xs) _ (List.head_mem hne)).1
    have hmem : xs.foldl min x ∈ counting_sort (x :: xs) :=
      (mem_thm (x :: xs) _).mpr (foldl_min_mem xs x)
    have hle2 : (counting_sort (x :: xs)).head hne ≤ xs.foldl min x :=
      sorted_head_le (sorted_thm (x :: xs)) hne hmem
    omega

/-- Property 12: The last element (`getLast?`) of `counting_sort arr` is the maximum element of `arr`. -/
def getLast_max_prop (arr : List Int) : Prop :=
  match arr with
  | [] => (counting_sort arr).getLast? = none
  | x :: xs => (counting_sort (x :: xs)).getLast? = some (xs.foldl max x)

theorem getLast_max_thm (arr : List Int) : getLast_max_prop arr := by
  cases arr with
  | nil => rfl
  | cons x xs =>
    dsimp only [getLast_max_prop]
    have hne : counting_sort (x :: xs) ≠ [] := by
      intro h
      exact List.cons_ne_nil x xs ((empty_iff_thm (x :: xs)).mp h)
    rw [List.getLast?_eq_some_getLast hne, Option.some.injEq]
    have hle1 : (counting_sort (x :: xs)).getLast hne ≤ xs.foldl max x :=
      (bounds_thm (x :: xs) _ (List.getLast_mem hne)).2
    have hmem : xs.foldl max x ∈ counting_sort (x :: xs) :=
      (mem_thm (x :: xs) _).mpr (foldl_max_mem xs x)
    have hle2 : xs.foldl max x ≤ (counting_sort (x :: xs)).getLast hne :=
      sorted_le_getLast (sorted_thm (x :: xs)) hne hmem
    omega

/-- Property 13: If the input list is already sorted, `counting_sort` returns it unchanged. -/
def already_sorted_prop (arr : List Int) : Prop :=
  List.Sorted (· ≤ ·) arr → counting_sort arr = arr

theorem already_sorted_thm (arr : List Int) : already_sorted_prop arr :=
  fun h => List.eq_of_perm_of_sorted (perm_thm arr) (sorted_thm arr) h

/-- Property 14: Sorting a singleton list returns the same singleton list. -/
def singleton_prop (x : Int) : Prop :=
  counting_sort [x] = [x]

theorem singleton_thm (x : Int) : singleton_prop x :=
  already_sorted_thm [x] (List.sorted_singleton x)

/-- Property 15: `counting_sort` is idempotent. -/
def idempotent_prop (arr : List Int) : Prop :=
  counting_sort (counting_sort arr) = counting_sort arr

theorem idempotent_thm (arr : List Int) : idempotent_prop arr :=
  already_sorted_thm (counting_sort arr) (sorted_thm arr)

/-- Property 16: Permuting the input list does not change the output of `counting_sort`. -/
def perm_invariant_prop (arr₁ arr₂ : List Int) : Prop :=
  arr₁.Perm arr₂ → counting_sort arr₁ = counting_sort arr₂

theorem perm_invariant_thm (arr₁ arr₂ : List Int) : perm_invariant_prop arr₁ arr₂ := by
  intro hperm
  have hp : (counting_sort arr₁).Perm (counting_sort arr₂) :=
    (perm_thm arr₁).trans (hperm.trans (perm_thm arr₂).symm)
  exact List.eq_of_perm_of_sorted hp (sorted_thm arr₁) (sorted_thm arr₂)

/-- Property 17: Sorting the reverse of a list yields the same result as sorting the original list. -/
def reverse_prop (arr : List Int) : Prop :=
  counting_sort arr.reverse = counting_sort arr

theorem reverse_thm (arr : List Int) : reverse_prop arr :=
  perm_invariant_thm arr.reverse arr (List.reverse_perm arr)

/-- Property 18: Sorting a list of `n` identical elements returns it unchanged. -/
def replicate_prop (n : Nat) (x : Int) : Prop :=
  counting_sort (List.replicate n x) = List.replicate n x

theorem replicate_thm (n : Nat) (x : Int) : replicate_prop n x :=
  already_sorted_thm (List.replicate n x) (List.pairwise_replicate.mpr (Or.inr (Int.le_refl x)))

/-- Property 19: Shifting all elements by an integer offset `k` shifts the sorted output by `k`. -/
def shift_prop (arr : List Int) (k : Int) : Prop :=
  counting_sort (arr.map (· + k)) = (counting_sort arr).map (· + k)

theorem shift_thm (arr : List Int) (k : Int) : shift_prop arr k := by
  have hp : (counting_sort (arr.map (· + k))).Perm ((counting_sort arr).map (· + k)) :=
    (perm_thm (arr.map (· + k))).trans ((perm_thm arr).symm.map (· + k))
  have hs : List.Sorted (· ≤ ·) ((counting_sort arr).map (· + k)) := by
    apply List.Pairwise.map (· + k) (fun a b hab => Int.add_le_add_right hab k) (sorted_thm arr)
  exact List.eq_of_perm_of_sorted hp (sorted_thm (arr.map (· + k))) hs

/-- Property 20: `counting_sort` agrees with Mathlib's `List.mergeSort (· ≤ ·)`. -/
def eq_mergeSort_prop (arr : List Int) : Prop :=
  counting_sort arr = arr.mergeSort (· ≤ ·)

theorem eq_mergeSort_thm (arr : List Int) : eq_mergeSort_prop arr := by
  have hp : (counting_sort arr).Perm (arr.mergeSort (· ≤ ·)) :=
    (perm_thm arr).trans (List.mergeSort_perm arr (· ≤ ·)).symm
  have hs : List.Sorted (· ≤ ·) (arr.mergeSort (· ≤ ·)) := by
    have h := List.sorted_mergeSort
      (le := (· ≤ ·))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact Int.le_trans hab hbc)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total a b)
      arr
    exact h.imp (by intro a b hab; exact of_decide_eq_true hab)
  exact List.eq_of_perm_of_sorted hp (sorted_thm arr) hs

/-! ## 6. Post-condition -/

/-- Post-condition combining the specification properties of `counting_sort`. -/
def Post_prop (arr : List Int) : Prop :=
  sorted_prop arr ∧
  chain_sorted_prop arr ∧
  index_sorted_prop arr ∧
  perm_prop arr ∧
  count_prop arr ∧
  length_prop arr ∧
  mem_prop arr ∧
  bounds_prop arr ∧
  head_min_prop arr ∧
  getLast_max_prop arr ∧
  already_sorted_prop arr ∧
  idempotent_prop arr ∧
  reverse_prop arr ∧
  eq_mergeSort_prop arr ∧
  empty_iff_prop arr

/-! ## 7. Property-Based Tests (PBTs) -/

/-- Executable Boolean check for `index_sorted_prop`. -/
def check_index_sorted (arr : List Int) : Bool :=
  let s := counting_sort arr
  (List.range s.length).all fun i =>
    (List.range s.length).all fun j =>
      !(decide (i ≤ j)) || decide (s.getD i 0 ≤ s.getD j 0)

/-- Executable Boolean check for `bounds_prop`. -/
def check_bounds (arr : List Int) : Bool :=
  match arr with
  | [] => counting_sort arr == []
  | x :: xs =>
    let min_val := xs.foldl min x
    let max_val := xs.foldl max x
    (counting_sort (x :: xs)).all fun y => decide (min_val ≤ y ∧ y ≤ max_val)

/-- Executable Boolean check for `head_min_prop`. -/
def check_head_min (arr : List Int) : Bool :=
  match arr with
  | [] => (counting_sort arr).head? == none
  | x :: xs => (counting_sort (x :: xs)).head? == some (xs.foldl min x)

/-- Executable Boolean check for `getLast_max_prop`. -/
def check_getLast_max (arr : List Int) : Bool :=
  match arr with
  | [] => (counting_sort arr).getLast? == none
  | x :: xs => (counting_sort (x :: xs)).getLast? == some (xs.foldl max x)

/-- Executable Boolean check for `count_prop` on all elements present in `arr` and its sorted output. -/
def check_count (arr : List Int) : Bool :=
  let s := counting_sort arr
  (arr ++ s).all fun v => s.count v == arr.count v

/-- Executable Boolean check for `mem_prop` on all elements and boundary candidates. -/
def check_mem (arr : List Int) : Bool :=
  let s := counting_sort arr
  (0 :: -1 :: 1 :: arr ++ s).all fun v => (v ∈ s) == (v ∈ arr)

/-- Executable Boolean check for `Post_prop`. -/
def check_post (arr : List Int) : Bool :=
  let s := counting_sort arr
  decide (List.Sorted (· ≤ ·) s) &&
  decide (List.Chain' (· ≤ ·) s) &&
  check_index_sorted arr &&
  decide (s.Perm arr) &&
  check_count arr &&
  (s.length == arr.length) &&
  check_mem arr &&
  check_bounds arr &&
  check_head_min arr &&
  check_getLast_max arr &&
  (!(decide (List.Sorted (· ≤ ·) arr)) || (s == arr)) &&
  (counting_sort s == s) &&
  (counting_sort arr.reverse == s) &&
  (s == arr.mergeSort (· ≤ ·)) &&
  ((s == []) == (arr == []))

-- Randomized PBTs via Plausible (covering every `_prop` and `Post_prop`)
#eval Plausible.Testable.check (counting_sort [] = [])
#eval Plausible.Testable.check (∀ (arr : List Int) (v : Int), (counting_sort arr).count v = arr.count v)
#eval Plausible.Testable.check (∀ arr : List Int, (counting_sort arr).Perm arr)
#eval Plausible.Testable.check (∀ arr : List Int, List.Sorted (· ≤ ·) (counting_sort arr))
#eval Plausible.Testable.check (∀ arr : List Int, List.Chain' (· ≤ ·) (counting_sort arr))
#eval Plausible.Testable.check (∀ arr : List Int, check_index_sorted arr = true)
#eval Plausible.Testable.check (∀ arr : List Int, (counting_sort arr).length = arr.length)
#eval Plausible.Testable.check (∀ (arr : List Int) (v : Int), v ∈ counting_sort arr ↔ v ∈ arr)
#eval Plausible.Testable.check (∀ arr : List Int, counting_sort arr = [] ↔ arr = [])
#eval Plausible.Testable.check (∀ arr : List Int, check_bounds arr = true)
#eval Plausible.Testable.check (∀ arr : List Int, check_head_min arr = true)
#eval Plausible.Testable.check (∀ arr : List Int, check_getLast_max arr = true)
#eval Plausible.Testable.check (∀ arr : List Int, !(decide (List.Sorted (· ≤ ·) arr)) || counting_sort arr == arr)
#eval Plausible.Testable.check (∀ arr : List Int, counting_sort (arr.mergeSort (· ≤ ·)) = arr.mergeSort (· ≤ ·))
#eval Plausible.Testable.check (∀ x : Int, counting_sort [x] = [x])
#eval Plausible.Testable.check (∀ arr : List Int, counting_sort (counting_sort arr) = counting_sort arr)
#eval Plausible.Testable.check (∀ (arr : List Int) (k : Nat), counting_sort (arr.drop k ++ arr.take k) = counting_sort arr)
#eval Plausible.Testable.check (∀ arr : List Int, counting_sort arr.reverse = counting_sort arr)
#eval Plausible.Testable.check (∀ (n : Nat) (x : Int), counting_sort (List.replicate n x) = List.replicate n x)
#eval Plausible.Testable.check (∀ (arr : List Int) (k : Int), counting_sort (arr.map (· + k)) = (counting_sort arr).map (· + k))
#eval Plausible.Testable.check (∀ arr : List Int, counting_sort arr = arr.mergeSort (· ≤ ·))
#eval Plausible.Testable.check (∀ arr : List Int, check_post arr = true)

-- Bounded exhaustive PBTs over a corpus of test lists
def pbt_corpus : List (List Int) :=
  [ [],
    [0], [1], [-1], [42],
    [1, 2], [2, 1], [-1, -2], [-2, -1], [0, 0],
    [3, 1, 2], [1, 2, 3], [2, 1, 3], [-3, 0, 2], [5, -5, 0],
    [3, 1, 4, 1, 2, 3], [5, 5, 5, 5, 5], [1, 0, 2, 0, 1, 0],
    [9, 8, 7, 6, 5, 4, 3, 2, 1],
    [-10, 5, -3, 0, 5, -10, 2, -1] ]

example : pbt_corpus.all check_post = true := by native_decide
example : pbt_corpus.all (fun arr => counting_sort (arr.map (· + (-7))) == (counting_sort arr).map (· + (-7))) = true := by native_decide
example : (List.range 15).all (fun n => counting_sort (List.replicate n (-3)) == List.replicate n (-3)) = true := by native_decide

/-! ## 8. Main Correctness Theorem: `Pre -> Post` -/

/-- Main correctness theorem: for any integer list `arr` satisfying `Pre arr`, `Post_prop arr` holds. -/
theorem counting_sort_correct (arr : List Int) (_hpre : Pre arr) : Post_prop arr :=
  ⟨sorted_thm arr,
   chain_sorted_thm arr,
   index_sorted_thm arr,
   perm_thm arr,
   count_thm arr,
   length_thm arr,
   mem_thm arr,
   bounds_thm arr,
   head_min_thm arr,
   getLast_max_thm arr,
   already_sorted_thm arr,
   idempotent_thm arr,
   reverse_thm arr,
   eq_mergeSort_thm arr,
   empty_iff_thm arr⟩

theorem correctness_thm (arr : List Int) (hpre : Pre arr) : Post_prop arr :=
  counting_sort_correct arr hpre

/-! ## 9. Imperative Implementation -/

/-- Imperative implementation of `counting_sort` using `Id.run do` and mutable variables. -/
def counting_sort_imp (arr : List Int) : List Int := Id.run do
  match arr with
  | [] => return []
  | x :: xs =>
    let mut max_val : Int := x
    let mut min_val : Int := x
    for num in xs do
      max_val := max max_val num
      min_val := min min_val num
    let range_size : Nat := (max_val - min_val + 1).toNat
    let mut count : List Nat := List.replicate range_size 0
    for num in x :: xs do
      let idx := (num - min_val).toNat
      count := count.set idx (count.getD idx 0 + 1)
    let mut result : List Int := []
    for i in List.range range_size do
      result := result ++ List.replicate (count.getD i 0) ((i : Int) + min_val)
    return result

/-! ## 10. Imperative Tests -/

example : counting_sort_imp [3, 1, 2] = [1, 2, 3] := by native_decide
example : counting_sort_imp [1, 2, 3] = [1, 2, 3] := by native_decide
example : counting_sort_imp [2, 1, 3] = [1, 2, 3] := by native_decide
example : counting_sort_imp [] = [] := by native_decide
example : counting_sort_imp [1] = [1] := by native_decide
example : counting_sort_imp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : counting_sort_imp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : counting_sort_imp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : counting_sort_imp [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : counting_sort_imp [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : counting_sort_imp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : counting_sort_imp [-5, 0, 3, -2, 1, -5] = [-5, -5, -2, 0, 1, 3] := by native_decide
example : pbt_corpus.all (fun arr => counting_sort_imp arr == counting_sort arr) = true := by native_decide

#eval counting_sort_imp [3, 1, 2]
#eval counting_sort_imp ([] : List Int)
#eval counting_sort_imp [-5, 0, 3, -2, 1, -5]
#eval Plausible.Testable.check (∀ arr : List Int, counting_sort arr = counting_sort_imp arr)

/-! ## 11. Functional = Imperative Equivalence Theorem -/

theorem foldl_prod_max_min (l : List Int) (a b : Int) :
    l.foldl (fun (p : MProd Int Int) num => ⟨max p.fst num, min p.snd num⟩) ⟨a, b⟩ =
      ⟨l.foldl max a, l.foldl min b⟩ := by
  induction l generalizing a b with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, ih]

/-- Proposition stating that the functional and imperative implementations are equivalent. -/
def equiv_prop (arr : List Int) : Prop :=
  counting_sort arr = counting_sort_imp arr

/-- Equivalence theorem: `counting_sort` and `counting_sort_imp` produce identical results for all inputs. -/
theorem equiv_thm (arr : List Int) : equiv_prop arr := by
  cases arr with
  | nil => rfl
  | cons x xs =>
    unfold equiv_prop counting_sort countStep
    simp [counting_sort_imp, foldl_prod_max_min, List.flatMap_def]

theorem counting_sort_equiv (arr : List Int) :
    counting_sort arr = counting_sort_imp arr :=
  equiv_thm arr

end counting_sort
