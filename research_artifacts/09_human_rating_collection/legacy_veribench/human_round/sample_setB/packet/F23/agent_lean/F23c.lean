import Mathlib

set_option linter.unusedVariables false

/-!
# HEAPSORT (CLRS 6.4) — a Lean 4 formalisation

This file formalises the Python program `heapsort_algorithm.py`, which implements
HEAPSORT from CLRS §6.4 on *0-based* max-heap arrays and returns the ascending
sorted copy of the input list of natural numbers.

The observable semantics of the program are:

* the pre-condition `pre` requires a list whose entries are all natural numbers
  (a `ValueError` is raised otherwise);
* the result is the *ascending sorted* copy of the input, i.e. it is sorted and
  a permutation (same multiset, hence same length) of the input.

## Structure of this file

1. `parent`, `left`, `right` — the 0-based heap index arithmetic of CLRS §6.1.
2. `maxExtract` / `extractAll` / `heapsort` — the *functional* implementation.
   A max-heap is a priority queue whose only observable behaviour inside
   HEAPSORT is "pop the maximum, keep the remaining elements"; `maxExtract`
   models exactly that operation and `extractAll` iterates it (build-heap
   followed by the extraction loop of CLRS 6.4).  All correctness theorems are
   stated and proved for this implementation.
3. `Pre`, the property propositions, `Post_prop`, the correctness theorem and
   the property-based tests.
4. A faithful, total, array-level transcription of the Python program
   (`maxHeapify`, `buildMaxHeap`, `heapsortArray`, `heapsortRef`), cross-checked
   against the proved-correct `heapsort` by exhaustive and randomised
   property-based tests.
5. The imperative (`Id.run do`, mutable state) implementation `heapsortImp`,
   its tests, and the proved functional/imperative equivalence theorem.

Every theorem below is proved by the Lean kernel (no `sorry`, no `native_decide`
inside proofs); `native_decide`, `decide` and `#eval` are used only in tests.
-/

namespace heapsort_algorithm

open List

/-! ## 1. Index arithmetic (CLRS §6.1, 0-based arrays) -/

/-- `parent i` is the index of the parent of node `i` in a 0-based heap array:
`0` for the root and `(i - 1) / 2` otherwise.  Mirrors the Python `parent`. -/
def parent (i : Nat) : Nat := if i = 0 then 0 else (i - 1) / 2

/-- `left i = 2 * i + 1`: index of the left child (Python `left`). -/
def left (i : Nat) : Nat := 2 * i + 1

/-- `right i = 2 * i + 2`: index of the right child (Python `right`). -/
def right (i : Nat) : Nat := 2 * i + 2

/-! ## 2. Max-extraction: the observable behaviour of a max-heap -/

/-- `maxOf xs` is the maximum of the non-empty list `xs` (`0` for `[]`). -/
def maxOf : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxOf xs)

/-- `removeOne m xs` deletes the first occurrence of `m` in `xs`. -/
def removeOne : Nat → List Nat → List Nat
  | _, [] => []
  | m, x :: xs => if x = m then xs else x :: removeOne m xs

/-- `maxExtract xs` is `none` on the empty heap and `some (m, rest)` otherwise,
where `m` is the maximum of `xs` (the root of the max-heap) and `rest` is `xs`
with one occurrence of `m` removed. -/
def maxExtract : List Nat → Option (Nat × List Nat)
  | [] => none
  | xs => some (maxOf xs, removeOne (maxOf xs) xs)

theorem maxOf_nil : maxOf [] = 0 := rfl

theorem maxOf_cons (x : Nat) (xs : List Nat) : maxOf (x :: xs) = max x (maxOf xs) := rfl

theorem removeOne_nil (m : Nat) : removeOne m [] = [] := rfl

theorem removeOne_cons_eq (m x : Nat) (xs : List Nat) (h : x = m) :
    removeOne m (x :: xs) = xs := by simp [removeOne, h]

theorem removeOne_cons_ne (m x : Nat) (xs : List Nat) (h : ¬ x = m) :
    removeOne m (x :: xs) = x :: removeOne m xs := by simp [removeOne, h]

theorem removeOne_cons (m x : Nat) (xs : List Nat) :
    removeOne m (x :: xs) = if x = m then xs else x :: removeOne m xs := rfl

/-- Membership transfer through a cons whose head is not the element. -/
theorem mem_cons_ne {a b : Nat} {l : List Nat} (h : a ∈ b :: l) (hb : ¬ b = a) : a ∈ l := by
  rw [List.mem_cons] at h
  cases h with
  | inl h => exact absurd h.symm hb
  | inr h => exact h

theorem maxOf_le : ∀ (xs : List Nat) (m : Nat), (∀ x ∈ xs, x ≤ m) → maxOf xs ≤ m := by
  intro xs
  induction xs with
  | nil => intro m _; rw [maxOf_nil]; exact Nat.zero_le m
  | cons y ys ih =>
      intro m h
      rw [maxOf_cons]
      exact max_le_iff.mpr ⟨h y List.mem_cons_self,
        ih m (fun x hx => h x (List.mem_cons_of_mem y hx))⟩

theorem le_maxOf : ∀ (xs : List Nat) (x : Nat), x ∈ xs → x ≤ maxOf xs := by
  intro xs
  induction xs with
  | nil => intro x h; exact absurd h List.not_mem_nil
  | cons y ys ih =>
      intro x h
      rw [maxOf_cons]
      rw [List.mem_cons] at h
      cases h with
      | inl h => rw [h]; exact Nat.le_max_left _ _
      | inr h => exact Nat.le_trans (ih x h) (Nat.le_max_right _ _)

theorem maxOf_mem : ∀ (xs : List Nat), xs ≠ [] → maxOf xs ∈ xs := by
  intro xs
  induction xs with
  | nil => intro h; exact absurd rfl h
  | cons y ys ih =>
      intro _
      have hgoal : max y (maxOf ys) = y ∨ max y (maxOf ys) ∈ ys := by
        cases ys with
        | nil =>
            left
            rw [maxOf_nil]
            exact Nat.max_eq_left (Nat.zero_le y)
        | cons z zs =>
            cases le_total y (maxOf (z :: zs)) with
            | inl hle =>
                right
                rw [Nat.max_eq_right hle]
                exact ih (by simp)
            | inr hle => left; exact Nat.max_eq_left hle
      rw [maxOf_cons, List.mem_cons]
      exact hgoal

theorem removeOne_perm (m : Nat) : ∀ xs : List Nat, m ∈ xs → (m :: removeOne m xs) ~ xs := by
  intro xs
  induction xs with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons x xs ih =>
      intro h
      by_cases hx : x = m
      · rw [removeOne_cons_eq m x xs hx, hx]
      · have hmem : m ∈ xs := mem_cons_ne h hx
        rw [removeOne_cons_ne m x xs hx]
        exact (List.Perm.swap x m (removeOne m xs)).trans (List.Perm.cons x (ih hmem))

theorem removeOne_length (m : Nat) :
    ∀ xs : List Nat, m ∈ xs → (removeOne m xs).length = xs.length - 1 := by
  intro xs
  induction xs with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons x xs ih =>
      intro h
      by_cases hx : x = m
      · rw [removeOne_cons_eq m x xs hx, List.length_cons]
        omega
      · have hmem : m ∈ xs := mem_cons_ne h hx
        have hpos : 0 < xs.length :=
          List.length_pos_iff.mpr (by rintro rfl; exact absurd hmem List.not_mem_nil)
        rw [removeOne_cons_ne m x xs hx, List.length_cons, List.length_cons, ih hmem]
        omega

theorem removeOne_le (m : Nat) : ∀ xs : List Nat,
    (∀ y ∈ xs, y ≤ m) → ∀ y ∈ removeOne m xs, y ≤ m := by
  intro xs
  induction xs with
  | nil => intro _ y hy; rw [removeOne_nil] at hy; exact absurd hy List.not_mem_nil
  | cons x xs ih =>
      intro h y hy
      by_cases hx : x = m
      · rw [removeOne_cons_eq m x xs hx] at hy
        exact h y (List.mem_cons_of_mem x hy)
      · rw [removeOne_cons_ne m x xs hx] at hy
        rw [List.mem_cons] at hy
        cases hy with
        | inl hy => rw [hy]; exact h x List.mem_cons_self
        | inr hy => exact ih (fun z hz => h z (List.mem_cons_of_mem x hz)) y hy

theorem maxExtract_nil : maxExtract [] = none := rfl

theorem maxExtract_cons (x : Nat) (xs : List Nat) :
    maxExtract (x :: xs) =
      some (maxOf (x :: xs), removeOne (maxOf (x :: xs)) (x :: xs)) := rfl

theorem maxExtract_eq_none : ∀ xs : List Nat, maxExtract xs = none ↔ xs = []
  | [] => by simp [maxExtract]
  | x :: xs => by simp [maxExtract]

theorem maxExtract_perm : ∀ (xs : List Nat) (m : Nat) (rest : List Nat),
    maxExtract xs = some (m, rest) → (m :: rest) ~ xs := by
  intro xs
  cases xs with
  | nil => intro m rest h; simp [maxExtract] at h
  | cons x xs =>
      intro m rest h
      injection h with hprod
      injection hprod with h1 h2
      subst h1 h2
      exact removeOne_perm _ _ (maxOf_mem _ (by simp))

theorem maxExtract_le : ∀ (xs : List Nat) (m : Nat) (rest : List Nat),
    maxExtract xs = some (m, rest) → ∀ y ∈ rest, y ≤ m := by
  intro xs
  cases xs with
  | nil => intro m rest h; simp [maxExtract] at h
  | cons x xs =>
      intro m rest h
      injection h with hprod
      injection hprod with h1 h2
      subst h1 h2
      exact removeOne_le _ _ (le_maxOf _)

theorem maxExtract_length : ∀ (xs : List Nat) (m : Nat) (rest : List Nat),
    maxExtract xs = some (m, rest) → rest.length = xs.length - 1 := by
  intro xs
  cases xs with
  | nil => intro m rest h; simp [maxExtract] at h
  | cons x xs =>
      intro m rest h
      injection h with hprod
      injection hprod with h1 h2
      subst h1 h2
      exact removeOne_length _ _ (maxOf_mem _ (by simp))

/-! ## 3. The functional implementation -/

/-- `extractAllPair fuel xs acc` performs `fuel` extraction steps on the not yet
sorted part `xs`, accumulating the popped maxima (which come out in ascending
order) in front of `acc`.  It returns `(remaining, accumulated)`. -/
def extractAllPair : Nat → List Nat → List Nat → List Nat × List Nat
  | 0, xs, acc => (xs, acc)
  | n + 1, xs, acc =>
      match maxExtract xs with
      | none => (xs, acc)
      | some (m, rest) => extractAllPair n rest (m :: acc)

/-- `extractAll fuel xs acc` is the accumulated output of `fuel` extraction steps. -/
def extractAll (fuel : Nat) (xs acc : List Nat) : List Nat := (extractAllPair fuel xs acc).2

/-- HEAPSORT: build the max-heap of `xs` and repeatedly extract its maximum.
The result is the ascending sorted copy of `xs`. -/
def heapsort (xs : List Nat) : List Nat := extractAll xs.length xs []

theorem extractAllPair_zero (xs acc : List Nat) : extractAllPair 0 xs acc = (xs, acc) := rfl

theorem extractAllPair_nil (fuel : Nat) (acc : List Nat) :
    extractAllPair fuel [] acc = ([], acc) := by
  cases fuel with
  | zero => rfl
  | succ n =>
      have h : extractAllPair (n + 1) [] acc = ([], acc) := by
        simp [extractAllPair, maxExtract]
      exact h

theorem extractAllPair_succ (n : Nat) (x : Nat) (xs acc : List Nat) :
    extractAllPair (n + 1) (x :: xs) acc =
      extractAllPair n (removeOne (maxOf (x :: xs)) (x :: xs)) (maxOf (x :: xs) :: acc) := rfl

theorem extractAll_spec : ∀ (fuel : Nat) (xs acc : List Nat), xs.length ≤ fuel →
    Sorted (· ≤ ·) acc → (∀ a ∈ acc, ∀ y ∈ xs, y ≤ a) →
    Sorted (· ≤ ·) (extractAll fuel xs acc) ∧ (extractAll fuel xs acc) ~ (xs ++ acc) := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs acc hlen hs _
      have hxs : xs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hxs
      have h1 : extractAll 0 [] acc = acc := rfl
      rw [h1, List.nil_append]
      exact ⟨hs, List.Perm.refl _⟩
  | succ n ih =>
      intro xs acc hlen hs hle
      cases xs with
      | nil =>
          have h1 : extractAll (n + 1) [] acc = acc := by
            show (extractAllPair (n + 1) [] acc).2 = acc
            rw [extractAllPair_nil]
          rw [h1, List.nil_append]
          exact ⟨hs, List.Perm.refl _⟩
      | cons x xs' =>
          let m := maxOf (x :: xs')
          let rest := removeOne m (x :: xs')
          have hmem : m ∈ x :: xs' := maxOf_mem _ (by simp)
          have hperm : (m :: rest) ~ x :: xs' := removeOne_perm _ _ hmem
          have hlenEq : rest.length = (x :: xs').length - 1 :=
            removeOne_length m (x :: xs') hmem
          have hlen' : rest.length ≤ n := by omega
          have hleRest : ∀ y ∈ rest, y ≤ m := removeOne_le _ _ (le_maxOf _)
          have hsorted' : Sorted (· ≤ ·) (m :: acc) :=
            List.sorted_cons.mpr ⟨fun a ha => hle a ha _ hmem, hs⟩
          have hle' : ∀ a ∈ (m :: acc), ∀ y ∈ rest, y ≤ a := by
            intro a ha y hy
            cases ha with
            | head => exact hleRest y hy
            | tail _ ha' =>
                exact hle a ha' y (List.Perm.subset hperm (List.mem_cons_of_mem _ hy))
          have hIH := ih rest (m :: acc) hlen' hsorted' hle'
          have hstep : extractAll (n + 1) (x :: xs') acc = extractAll n rest (m :: acc) := rfl
          have hperm2 : rest ++ [m] ~ x :: xs' := by
            refine (List.perm_append_comm (α := Nat)).trans ?_
            rw [List.singleton_append]
            exact hperm
          have hperm3 : rest ++ (m :: acc) ~ (x :: xs') ++ acc := by
            have e1 : m :: acc = [m] ++ acc := (List.singleton_append).symm
            have e2 : rest ++ (m :: acc) = (rest ++ [m]) ++ acc := by
              rw [e1, ← List.append_assoc]
            rw [e2]
            exact List.Perm.append_right acc hperm2
          rw [hstep]
          exact ⟨hIH.1, hIH.2.trans hperm3⟩

theorem heapsort_sorted (xs : List Nat) : Sorted (· ≤ ·) (heapsort xs) :=
  (extractAll_spec xs.length xs [] (Nat.le_refl _) List.Pairwise.nil (by simp)).1

theorem heapsort_perm (xs : List Nat) : heapsort xs ~ xs := by
  have h := (extractAll_spec xs.length xs [] (Nat.le_refl _) List.Pairwise.nil (by simp)).2
  simpa using h

theorem heapsort_length (xs : List Nat) : (heapsort xs).length = xs.length :=
  List.Perm.length_eq (heapsort_perm xs)

theorem heapsort_nil : heapsort [] = [] := rfl

theorem heapsort_singleton (x : Nat) : heapsort [x] = [x] :=
  List.eq_of_perm_of_sorted (heapsort_perm [x]) (heapsort_sorted [x]) (by simp [List.Sorted])

/-! ### Unit tests for the functional implementation -/

#eval heapsort [3, 1, 2]
#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsort []
#eval heapsort [42]
#eval heapsort [7, 7, 7, 7]
#eval heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1]

example : heapsort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsort [] = [] := by native_decide
example : heapsort [42] = [42] := by native_decide
example : heapsort [2, 1] = [1, 2] := by native_decide
example : heapsort [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsort [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : heapsort [2, 1] ≠ [2, 1] := by native_decide
example : maxExtract [3, 1, 2] = some (3, [1, 2]) := by native_decide
example : maxExtract [] = (none : Option (Nat × List Nat)) := by native_decide
example : parent 0 = 0 := by native_decide
example : parent 5 = 2 := by native_decide
example : left 3 = 7 := by native_decide
example : right 3 = 8 := by native_decide

/-! ## 3b. CLRS array-level implementation (faithful transcription of the Python)

The definitions below mirror the Python program line by line: `_swap`,
`max_heapify`, `build_max_heap` and `heapsort`.  They are written with total
operations (`Array.getD`, `swapD`) so that no out-of-bounds `panic` can occur;
whenever `hs ≤ a.size` (as in every call made by `heapsortArray`) they coincide
with the Python program.  They are cross-checked against the proved-correct
`heapsort` by the property-based tests below.
-/

/-- `_swap(arr, i, j)`: exchange the entries at positions `i` and `j`
(a no-op when an index is out of bounds). -/
def swapD (a : Array Nat) (i j : Nat) : Array Nat :=
  (a.set! i (a.getD j 0)).set! j (a.getD i 0)

/-- MAX-HEAPIFY (CLRS 6.2) for a 0-based array `a` with heap size `hs`.
The `while True` loop of the Python program becomes tail recursion; the three
branches correspond exactly to `largest = left i`, `largest = right i` and
`largest = i`. -/
def maxHeapify (a : Array Nat) (i hs : Nat) : Array Nat :=
  if h1 : left i < hs && a.getD (left i) 0 > a.getD i 0 then
    if h2 : right i < hs && a.getD (right i) 0 > a.getD (left i) 0 then
      maxHeapify (swapD a i (right i)) (right i) hs
    else
      maxHeapify (swapD a i (left i)) (left i) hs
  else if h2 : right i < hs && a.getD (right i) 0 > a.getD i 0 then
    maxHeapify (swapD a i (right i)) (right i) hs
  else
    a
termination_by hs - i
decreasing_by
  all_goals
    simp_wf
    simp only [Bool.and_eq_true, decide_eq_true_iff, left, right] at *
    omega

/-- BUILD-MAX-HEAP (CLRS 6.3): `for i in range(parent(n-1), -1, -1)`. -/
def buildMaxHeap (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a
  else (List.range (parent (a.size - 1) + 1)).reverse.foldl
      (fun b i => maxHeapify b i a.size) a

/-- HEAPSORT (CLRS 6.4) on arrays. -/
def heapsortArray (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a
  else
    let h := buildMaxHeap a
    (List.range' 1 (h.size - 1)).reverse.foldl
      (fun b i => maxHeapify (swapD b 0 i) 0 i) h

/-- The Python `heapsort` on lists: returns a sorted copy, the input is untouched. -/
def heapsortRef (xs : List Nat) : List Nat := (heapsortArray xs.toArray).toList

theorem buildMaxHeap_small (a : Array Nat) (h : a.size ≤ 1) : buildMaxHeap a = a := by
  simp [buildMaxHeap, h]

theorem heapsortArray_small (a : Array Nat) (h : a.size ≤ 1) : heapsortArray a = a := by
  simp [heapsortArray, h]

theorem maxHeapify_zero_heapSize (a : Array Nat) (i : Nat) : maxHeapify a i 0 = a := by
  simp [maxHeapify]

/-! ### Unit tests for the array-level implementation -/

#eval heapsortRef [3, 1, 2]
#eval heapsortRef [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsortRef []
#eval heapsortRef [42]
#eval heapsortRef [7, 7, 7, 7]
#eval heapsortRef [9, 8, 7, 6, 5, 4, 3, 2, 1]
#eval heapsortRef [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]
#eval buildMaxHeap #[4, 1, 3, 2, 16, 9, 10, 14, 8, 7]

example : heapsortRef [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsortRef [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsortRef [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsortRef [] = [] := by native_decide
example : heapsortRef [42] = [42] := by native_decide
example : heapsortRef [2, 1] = [1, 2] := by native_decide
example : heapsortRef [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsortRef [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapsortRef [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsortRef [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsortArray #[3, 1, 2] = #[1, 2, 3] := by native_decide
example : buildMaxHeap #[1, 2, 3] = #[3, 2, 1] := by native_decide

/-! ## 4. Pre-condition -/

/-- The Python pre-condition `pre`: the input is a list all of whose entries are
natural numbers.  In the `List Nat` model this holds by construction (the type
system enforces it); it is kept explicit so that the correctness theorem has the
`Pre → Post` shape of the Python program.  `PreInt` below models the very same
check at the `Int` level, where a negative entry triggers the `ValueError`. -/
def Pre (xs : List Nat) : Prop := ∀ x ∈ xs, 0 ≤ x

theorem Pre_holds (xs : List Nat) : Pre xs := fun _ _ => Nat.zero_le _

/-- `PreInt xs` is the pre-condition `pre` for a list of integers. -/
def PreInt (xs : List Int) : Prop := ∀ x ∈ xs, 0 ≤ x

/-- Executable form of `PreInt`: the Python `all(_is_nat(x) for x in arr)`. -/
def preCheck (xs : List Int) : Bool := xs.all (fun x => decide (0 ≤ x))

theorem preCheck_iff (xs : List Int) : preCheck xs = true ↔ PreInt xs := by
  simp only [preCheck, PreInt, List.all_eq_true, decide_eq_true_iff]

/-- The checked entry point of the Python program: it raises `ValueError`
(modelled as `Except.error`) when the pre-condition is violated, and otherwise
returns the sorted copy. -/
def heapsortInt (xs : List Int) : Except String (List Int) :=
  if preCheck xs then
    .ok ((heapsort (xs.map Int.toNat)).map (fun n : Nat => (n : Int)))
  else
    .error "Input must be List[Nat]"

theorem heapsortInt_error (xs : List Int) (h : ¬ PreInt xs) :
    heapsortInt xs = .error "Input must be List[Nat]" := by
  have hpc : preCheck xs = false := by
    cases hb : preCheck xs with
    | true => exact absurd hb (fun h2 => h ((preCheck_iff xs).mp h2))
    | false => rfl
  simp [heapsortInt, hpc]

theorem heapsortInt_ok (xs : List Int) (h : PreInt xs) :
    heapsortInt xs = .ok ((heapsort (xs.map Int.toNat)).map (fun n : Nat => (n : Int))) := by
  simp [heapsortInt, (preCheck_iff xs).mpr h]

theorem map_natCast_toNat (xs : List Int) (h : PreInt xs) :
    (xs.map Int.toNat).map (fun n : Nat => (n : Int)) = xs := by
  induction xs with
  | nil => rfl
  | cons a l ih =>
      have ha : (a.toNat : Int) = a := Int.toNat_of_nonneg (h a List.mem_cons_self)
      have hl : PreInt l := fun x hx => h x (List.mem_cons_of_mem a hx)
      have hrec := ih hl
      simp only [List.map_cons]
      rw [ha, hrec]

theorem sorted_map_natCast : ∀ l : List Nat, Sorted (· ≤ ·) l →
    Sorted (· ≤ ·) (l.map (fun n : Nat => (n : Int))) := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a l ih =>
      intro hl
      rw [List.sorted_cons] at hl
      rw [List.map_cons, List.sorted_cons]
      refine ⟨?_, ih hl.2⟩
      intro b hb
      rcases List.mem_map.mp hb with ⟨c, hc, rfl⟩
      exact Nat.cast_le.mpr (hl.1 c hc)

theorem heapsortInt_perm (xs : List Int) (h : PreInt xs) :
    ((heapsort (xs.map Int.toNat)).map (fun n : Nat => (n : Int))) ~ xs := by
  have h1 := List.Perm.map (fun n : Nat => (n : Int)) (heapsort_perm (xs.map Int.toNat))
  rw [map_natCast_toNat xs h] at h1
  exact h1

/-- The `Int`-level program is correct on every input satisfying `PreInt`. -/
theorem heapsortInt_correct (xs : List Int) (h : PreInt xs) :
    ∃ ys : List Int, heapsortInt xs = .ok ys ∧ Sorted (· ≤ ·) ys ∧ ys ~ xs ∧
      ys.length = xs.length :=
  ⟨_, heapsortInt_ok xs h, sorted_map_natCast _ (heapsort_sorted _), heapsortInt_perm xs h,
    List.Perm.length_eq (heapsortInt_perm xs h)⟩

/-! ## 5. Property propositions -/

/-- The output is sorted in ascending order. -/
def Sorted_prop (xs : List Nat) : Prop := Sorted (· ≤ ·) (heapsort xs)

/-- The output is a permutation of the input (no element is lost or invented). -/
def Perm_prop (xs : List Nat) : Prop := heapsort xs ~ xs

/-- The output has the same length as the input (Python `len(out) == len(arr)`). -/
def Length_prop (xs : List Nat) : Prop := (heapsort xs).length = xs.length

/-- The output has the same multiset of entries as the input
(Python `sorted(out) == sorted(arr)`); equivalent to `Perm_prop`. -/
def Multiset_prop (xs : List Nat) : Prop := (heapsort xs : Multiset Nat) = (xs : Multiset Nat)

/-- The output equals the canonical ascending sort of the input
(Python `out == sorted(arr)`). -/
def EqSorted_prop (xs : List Nat) : Prop := heapsort xs = xs.mergeSort (· ≤ ·)

/-- The first entry of the output is the minimum of the input. -/
def Min_prop (xs : List Nat) : Prop := ∀ x ∈ xs, (heapsort xs).headD 0 ≤ x

/-- Executable (decidable) forms of the properties above; they let the
property-based tests below check the very propositions that are proved. -/
instance decidableSorted_prop (xs : List Nat) : Decidable (Sorted_prop xs) :=
  decidable_of_iff (Sorted (· ≤ ·) (heapsort xs)) Iff.rfl

instance decidableLength_prop (xs : List Nat) : Decidable (Length_prop xs) :=
  decidable_of_iff ((heapsort xs).length = xs.length) Iff.rfl

instance decidableMultiset_prop (xs : List Nat) : Decidable (Multiset_prop xs) :=
  decidable_of_iff ((heapsort xs : Multiset Nat) = (xs : Multiset Nat)) Iff.rfl

instance decidableEqSorted_prop (xs : List Nat) : Decidable (EqSorted_prop xs) :=
  decidable_of_iff (heapsort xs = xs.mergeSort (· ≤ ·)) Iff.rfl

instance decidableMin_prop (xs : List Nat) : Decidable (Min_prop xs) :=
  decidable_of_iff (∀ x ∈ xs, (heapsort xs).headD 0 ≤ x) Iff.rfl

/-- `Perm_prop` and `Multiset_prop` are the same statement, so the multiset
equality test below is an executable property-based test for `Perm_prop`. -/
theorem Perm_prop_iff (xs : List Nat) : Perm_prop xs ↔ Multiset_prop xs :=
  Iff.symm Multiset.coe_eq_coe

theorem Sorted_thm (xs : List Nat) (h : Pre xs) : Sorted_prop xs := heapsort_sorted xs

theorem Perm_thm (xs : List Nat) (h : Pre xs) : Perm_prop xs := heapsort_perm xs

theorem Length_thm (xs : List Nat) (h : Pre xs) : Length_prop xs := heapsort_length xs

theorem Multiset_thm (xs : List Nat) (h : Pre xs) : Multiset_prop xs :=
  Multiset.coe_eq_coe.mpr (heapsort_perm xs)

theorem EqSorted_thm (xs : List Nat) (h : Pre xs) : EqSorted_prop xs :=
  List.eq_of_perm_of_sorted
    ((heapsort_perm xs).trans (List.mergeSort_perm xs (· ≤ ·)).symm)
    (heapsort_sorted xs) (List.sorted_mergeSort' (· ≤ ·) xs)

/-- Every list is either empty or a cons. -/
theorem eq_nil_or_cons (l : List Nat) : l = [] ∨ ∃ m t, l = m :: t := by
  cases l with
  | nil => exact Or.inl rfl
  | cons m t => exact Or.inr ⟨m, t, rfl⟩

theorem Min_thm (xs : List Nat) (h : Pre xs) : Min_prop xs := by
  intro x hx
  rcases eq_nil_or_cons (heapsort xs) with hnil | ⟨m, l, heq⟩
  · rw [hnil]
    exact Nat.zero_le x
  · have hget : (m :: l).headD 0 = m := rfl
    have hsort : Sorted (· ≤ ·) (m :: l) := by rw [← heq]; exact heapsort_sorted xs
    have hx' : x ∈ (m :: l) := by
      rw [← heq]
      exact (List.Perm.mem_iff (heapsort_perm xs)).mpr hx
    rw [List.mem_cons] at hx'
    rw [heq, hget]
    rcases hx' with rfl | hx'
    · exact Nat.le_refl _
    · exact (List.sorted_cons.mp hsort).1 x hx'

/-- In a sorted list every entry is at most the last one. -/
theorem le_getLastD_of_sorted : ∀ l : List Nat, Sorted (· ≤ ·) l →
    ∀ y ∈ l, y ≤ l.getLastD 0 := by
  intro l
  induction l with
  | nil => intro _ y hy; exact absurd hy List.not_mem_nil
  | cons a l ih =>
      intro hl y hy
      cases l with
      | nil =>
          simp at hy
          rw [hy]
          simp [List.getLastD]
      | cons b l' =>
          have hsorted : Sorted (· ≤ ·) (b :: l') := (List.sorted_cons.mp hl).2
          have hab : a ≤ b := (List.sorted_cons.mp hl).1 b List.mem_cons_self
          have hlast : (a :: b :: l').getLastD 0 = (b :: l').getLastD 0 := by
            simp [List.getLastD]
          rw [hlast]
          rw [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact Nat.le_trans hab (ih hsorted b List.mem_cons_self)
          · exact ih hsorted y hy

/-- The last entry of the output is the maximum of the input. -/
def Max_prop (xs : List Nat) : Prop := ∀ x ∈ xs, x ≤ (heapsort xs).getLastD 0

instance decidableMax_prop (xs : List Nat) : Decidable (Max_prop xs) :=
  decidable_of_iff (∀ x ∈ xs, x ≤ (heapsort xs).getLastD 0) Iff.rfl

theorem Max_thm (xs : List Nat) (h : Pre xs) : Max_prop xs := by
  intro x hx
  exact le_getLastD_of_sorted (heapsort xs) (heapsort_sorted xs) x
    ((List.Perm.mem_iff (heapsort_perm xs)).mpr hx)

/-- Sorting depends only on the multiset of the input. -/
theorem heapsort_perm_invariant (xs ys : List Nat) (h : xs ~ ys) :
    heapsort xs = heapsort ys :=
  List.eq_of_perm_of_sorted
    ((heapsort_perm xs).trans (h.trans (heapsort_perm ys).symm))
    (heapsort_sorted xs) (heapsort_sorted ys)

/-- HEAPSORT is idempotent: sorting an already sorted list changes nothing. -/
theorem heapsort_idempotent (xs : List Nat) : heapsort (heapsort xs) = heapsort xs :=
  List.eq_of_perm_of_sorted (heapsort_perm (heapsort xs)) (heapsort_sorted (heapsort xs))
    (heapsort_sorted xs)

/-! ## 6. Post-condition and correctness -/

/-- The post-condition of the Python program: the returned list is the ascending
sorted copy of the input. -/
def Post_prop (xs : List Nat) : Prop :=
  Sorted_prop xs ∧ Perm_prop xs ∧ Length_prop xs

theorem heapsort_correct (xs : List Nat) (h : Pre xs) : Post_prop xs :=
  ⟨Sorted_thm xs h, Perm_thm xs h, Length_thm xs h⟩

/-! ## 7. Property-based tests -/

/-- `allLists n k` is the exhaustive list of all `n`-element lists with entries
below `k`; used for bounded (exhaustive) property-based tests. -/
def allLists : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, k => (allLists n k).flatMap (fun l => (List.range k).map (fun x => x :: l))

example : (allLists 2 3).length = 9 := by native_decide
example : (allLists 3 3).length = 27 := by native_decide
example : (allLists 4 4).length = 256 := by native_decide

-- Bounded PBT for `Sorted_prop`
example : (allLists 4 4).all (fun l => decide (Sorted_prop l)) = true := by native_decide
-- Bounded PBT for `Perm_prop` (executable form: multiset equality, `Multiset.coe_eq_coe`)
example : (allLists 4 4).all (fun l => decide ((heapsort l : Multiset Nat) = (l : Multiset Nat)))
    = true := by native_decide
-- Bounded PBT for `Length_prop`
example : (allLists 4 4).all (fun l => decide (Length_prop l)) = true := by native_decide
-- Bounded PBT for `Multiset_prop`
example : (allLists 4 4).all (fun l => decide (Multiset_prop l)) = true := by native_decide
-- Bounded PBT for `EqSorted_prop`
example : (allLists 4 4).all (fun l => decide (EqSorted_prop l)) = true := by native_decide
-- Bounded PBT for `Min_prop`
example : (allLists 4 4).all (fun l => l.all (fun x => decide ((heapsort l).headD 0 ≤ x)))
    = true := by native_decide
-- Bounded PBT for `Max_prop`
example : (allLists 4 4).all (fun l => decide (Max_prop l)) = true := by native_decide
example : (allLists 5 3).all (fun l => decide (Min_prop l) && decide (Max_prop l)) = true := by
  native_decide
-- Bounded PBT for `Post_prop` (conjunction of the executable forms above)
example : (allLists 4 4).all (fun l =>
    decide (Sorted_prop l) && decide ((heapsort l : Multiset Nat) = (l : Multiset Nat))
      && decide (Length_prop l)) = true := by native_decide
-- Bounded PBT: the CLRS array-level transcription agrees with the proved implementation
example : (allLists 4 3).all (fun l => decide (heapsortRef l = heapsort l)) = true := by
  native_decide
example : (allLists 5 2).all (fun l => decide (heapsortRef l = heapsort l)) = true := by
  native_decide
example : (allLists 3 5).all (fun l => decide (heapsortRef l = heapsort l)) = true := by
  native_decide
-- Bounded PBT for the `Int` layer: a negative entry triggers the `ValueError` branch
example : (List.range 12).all (fun n =>
    decide (n = 0 ∨
      (heapsortInt ((List.range n).map (fun i => (i : Int) - 5))).toOption =
        (none : Option (List Int)))) = true := by
  native_decide
-- Bounded PBT for the `Int` layer: the error flag is exactly the negation of `preCheck`
example : (allLists 3 4).all (fun l =>
    let li := l.map (fun x => (x : Int) - 2)
    decide (((heapsortInt li).toOption = (none : Option (List Int))) =
      (preCheck li = false))) = true := by native_decide
-- Bounded PBT for the `Int` layer: on admissible input it returns the sorted list
example : (allLists 3 4).all (fun l =>
    decide ((heapsortInt (l.map (fun x => (x : Int)))).toOption =
      some ((heapsort l).map (fun n : Nat => (n : Int))))) = true := by native_decide

-- Randomised PBTs (Plausible); the file fails to compile if a counterexample exists
#eval Plausible.Testable.check (∀ xs : List Nat, decide (Sorted_prop xs))
#eval Plausible.Testable.check (∀ xs : List Nat, decide (Multiset_prop xs))
#eval Plausible.Testable.check (∀ xs : List Nat, decide (Length_prop xs))
#eval Plausible.Testable.check (∀ xs : List Nat, decide (EqSorted_prop xs))
#eval Plausible.Testable.check (∀ xs : List Nat, decide (heapsortRef xs = heapsort xs))
#eval Plausible.Testable.check (∀ xs : List Nat,
  decide ((heapsortInt (xs.map (fun n => (n : Int)))).toOption =
    some ((heapsort xs).map (fun n : Nat => (n : Int)))))
#eval Plausible.Testable.check (∀ xs : List Nat, decide (Min_prop xs))
#eval Plausible.Testable.check (∀ xs : List Nat, decide (Max_prop xs))

/-! ## 8. Imperative implementation (`Id.run do`, mutable state) -/

/-- One imperative extraction step acting on the mutable state `(rest, acc)`.
It mirrors `maxExtract`: pop the heap maximum into the accumulator. -/
def impStep (s : List Nat × List Nat) : List Nat × List Nat :=
  match maxExtract s.1 with
  | none => s
  | some (m, rest) => (rest, m :: s.2)

/-- The imperative HEAPSORT: mutable state in the `Id` monad and a bounded `for`
loop that pops the maximum of the remaining heap `xs.length` times. -/
def heapsortImp (xs : List Nat) : List Nat := Id.run do
  let mut st : List Nat × List Nat := (xs, [])
  for _ in List.range xs.length do
    st := impStep st
  return st.2

/-! ### Imperative tests -/

#eval heapsortImp [3, 1, 2]
#eval heapsortImp [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsortImp []
#eval heapsortImp [42]
#eval heapsortImp [7, 7, 7, 7]
#eval heapsortImp [9, 8, 7, 6, 5, 4, 3, 2, 1]
#eval heapsortImp [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]

example : heapsortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsortImp [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsortImp [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsortImp [] = [] := by native_decide
example : heapsortImp [42] = [42] := by native_decide
example : heapsortImp [2, 1] = [1, 2] := by native_decide
example : heapsortImp [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapsortImp [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsortImp [3, 1, 2] ≠ [3, 2, 1] := by native_decide

-- Bounded PBT: the imperative version satisfies the post-condition everywhere
example : (allLists 4 4).all (fun l => decide (Sorted_prop l) &&
    decide ((heapsortImp l : Multiset Nat) = (l : Multiset Nat)) &&
    decide ((heapsortImp l).length = l.length)) = true := by native_decide

-- Randomised PBT: imperative = functional
#eval Plausible.Testable.check (∀ xs : List Nat, decide (heapsortImp xs = heapsort xs))

/-! ### Equivalence of the functional and the imperative implementation -/

theorem impStep_nil (acc : List Nat) : impStep ([], acc) = ([], acc) := rfl

theorem impStep_cons (x : Nat) (xs acc : List Nat) :
    impStep (x :: xs, acc) =
      (removeOne (maxOf (x :: xs)) (x :: xs), maxOf (x :: xs) :: acc) := rfl

theorem extractAllPair_impStep (n : Nat) (xs acc : List Nat) :
    extractAllPair (n + 1) xs acc =
      extractAllPair n (impStep (xs, acc)).1 (impStep (xs, acc)).2 := by
  cases xs with
  | nil =>
      have h1 : impStep ([], acc) = ([], acc) := rfl
      rw [extractAllPair_nil (n + 1) acc, h1, extractAllPair_nil n acc]
  | cons x xs' => rfl

theorem impStep_extractAllPair (n : Nat) : ∀ (xs acc : List Nat),
    impStep (extractAllPair n xs acc) =
      extractAllPair n (impStep (xs, acc)).1 (impStep (xs, acc)).2 := by
  induction n with
  | zero => intro xs acc; rfl
  | succ n ih =>
      intro xs acc
      rw [extractAllPair_impStep n xs acc, ih _ _, ← extractAllPair_impStep n _ _]

theorem foldl_impStep (n : Nat) (xs acc : List Nat) :
    (List.range n).foldl (fun s _ => impStep s) (xs, acc) = extractAllPair n xs acc := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.foldl_concat, ih, impStep_extractAllPair n xs acc,
        ← extractAllPair_impStep n xs acc]

theorem heapsortImp_foldl (xs : List Nat) :
    heapsortImp xs = ((List.range xs.length).foldl (fun s _ => impStep s) (xs, [])).2 := by
  simp [heapsortImp]

/-- The imperative implementation computes exactly the functional one. -/
theorem heapsortImp_eq (xs : List Nat) : heapsortImp xs = heapsort xs := by
  rw [heapsortImp_foldl, foldl_impStep, heapsort]
  rfl

/-- Consequently the imperative implementation satisfies the post-condition. -/
theorem heapsortImp_correct (xs : List Nat) (h : Pre xs) :
    Sorted (· ≤ ·) (heapsortImp xs) ∧ heapsortImp xs ~ xs ∧
      (heapsortImp xs).length = xs.length := by
  rw [heapsortImp_eq]
  exact ⟨heapsort_sorted xs, heapsort_perm xs, heapsort_length xs⟩

/-! ## 9. Imperative CLRS transcription (mutable arrays)

`heapsortImpCLRS` below is a line-by-line imperative transcription of the Python
program: a mutable `Array Nat`, `build_max_heap`, and the extraction loop
`for i in range(n-1, 0, -1): swap(0, i); max_heapify(0, i)`.  It is validated
against the proved-correct `heapsort` by exhaustive bounded property-based tests
and by randomised property-based tests.
-/

/-- MAX-HEAPIFY, imperative form: the Python `while True` loop, bounded by `hs`
iterations (each iteration descends at most one level of the heap). -/
def maxHeapifyImp (a : Array Nat) (i hs : Nat) : Array Nat := Id.run do
  let mut a := a
  let mut i := i
  for _ in List.range hs do
    let l := left i
    let r := right i
    let mut largest := i
    if l < hs && a.getD l 0 > a.getD i 0 then
      largest := l
    if r < hs && a.getD r 0 > a.getD largest 0 then
      largest := r
    if largest = i then
      break
    a := swapD a i largest
    i := largest
  return a

/-- BUILD-MAX-HEAP, imperative form (`for i in range(parent(n-1), -1, -1)`). -/
def buildMaxHeapImp (a : Array Nat) : Array Nat := Id.run do
  let mut a := a
  let n := a.size
  if n ≤ 1 then
    return a
  for i in (List.range (parent (n - 1) + 1)).reverse do
    a := maxHeapifyImp a i n
  return a

/-- HEAPSORT, imperative form on a mutable array. -/
def heapsortImpCLRS (xs : List Nat) : List Nat := Id.run do
  let mut a := xs.toArray
  let n := a.size
  if n ≤ 1 then
    return a.toList
  a := buildMaxHeapImp a
  for i in (List.range' 1 (n - 1)).reverse do
    a := swapD a 0 i
    a := maxHeapifyImp a 0 i
  return a.toList

theorem maxHeapify_leaf (a : Array Nat) (i hs : Nat) (h : hs ≤ left i) :
    maxHeapify a i hs = a := by
  have h1 : ¬ left i < hs := by omega
  have h2 : ¬ right i < hs := by
    have hl : left i < right i := by simp [left, right]
    omega
  simp [maxHeapify, h1, h2]

/-- MAX-HEAPIFY leaves a heap of size one unchanged. -/
theorem maxHeapify_heapSize_one (a : Array Nat) (i : Nat) : maxHeapify a i 1 = a :=
  maxHeapify_leaf a i 1 (by simp [left])

theorem heapsortRef_nil : heapsortRef [] = [] := by decide

theorem heapsortRef_singleton (x : Nat) : heapsortRef [x] = [x] := by
  simp [heapsortRef, heapsortArray]

/-! ### Imperative CLRS tests -/

#eval maxHeapifyImp #[1, 5, 3] 0 3
#eval buildMaxHeapImp #[4, 1, 3, 2, 16, 9, 10, 14, 8, 7]
#eval heapsortImpCLRS [3, 1, 2]
#eval heapsortImpCLRS [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsortImpCLRS []
#eval heapsortImpCLRS [42]
#eval heapsortImpCLRS [7, 7, 7, 7]
#eval heapsortImpCLRS [9, 8, 7, 6, 5, 4, 3, 2, 1]

example : maxHeapifyImp #[1, 5, 3] 0 3 = #[5, 1, 3] := by native_decide
example : buildMaxHeapImp #[4, 1, 3, 2, 16, 9, 10, 14, 8, 7] =
    #[16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by native_decide
example : buildMaxHeap #[4, 1, 3, 2, 16, 9, 10, 14, 8, 7] =
    #[16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by native_decide
example : heapsortImpCLRS [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsortImpCLRS [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsortImpCLRS [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsortImpCLRS [] = [] := by native_decide
example : heapsortImpCLRS [42] = [42] := by native_decide
example : heapsortImpCLRS [2, 1] = [1, 2] := by native_decide
example : heapsortImpCLRS [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsortImpCLRS [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapsortImpCLRS [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsortImpCLRS [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide

-- Bounded PBTs: the imperative CLRS transcription agrees with the proved implementation
example : (allLists 4 3).all (fun l => decide (heapsortImpCLRS l = heapsort l)) = true := by
  native_decide
example : (allLists 5 2).all (fun l => decide (heapsortImpCLRS l = heapsort l)) = true := by
  native_decide
example : (allLists 3 5).all (fun l => decide (heapsortImpCLRS l = heapsort l)) = true := by
  native_decide
example : (allLists 4 3).all (fun l => decide (heapsortImpCLRS l = heapsortRef l)) = true := by
  native_decide
example : (allLists 4 3).all (fun l => decide (heapsortImpCLRS l = heapsortImp l)) = true := by
  native_decide
example : (allLists 3 4).all (fun l =>
    decide (Sorted (· ≤ ·) (heapsortImpCLRS l)) &&
      decide ((heapsortImpCLRS l : Multiset Nat) = (l : Multiset Nat))) = true := by native_decide

-- Randomised PBTs for the CLRS array-level implementations
#eval Plausible.Testable.check (∀ xs : List Nat, decide (heapsortImpCLRS xs = heapsort xs))
#eval Plausible.Testable.check (∀ xs : List Nat, decide (heapsortRef xs = heapsortImp xs))

/-! ## 10. The assertions of the Python `check` function -/

/-- Every fixed-input assertion made by the Python `check(heapsort)` function.
Each equality holds definitionally, so the whole conjunction is kernel-checked
by `rfl` (no `native_decide`). -/
theorem check_heapsort :
    heapsort [3, 1, 2] = [1, 2, 3] ∧
    heapsort [1, 2, 3] = [1, 2, 3] ∧
    heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] ∧
    heapsort [] = [] ∧
    heapsort [42] = [42] ∧
    heapsort [2, 1] = [1, 2] ∧
    heapsort [7, 7, 7, 7] = [7, 7, 7, 7] ∧
    heapsort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] ∧
    heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] ∧
    heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] ∧
    heapsort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] ∧
    heapsort [3, 1, 2] ≠ [3, 2, 1] ∧
    heapsort [2, 1] ≠ [2, 1] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩

/-- `heapsort` computes the canonical ascending sort of its input
(the Python `sorted(arr)`). -/
theorem heapsort_eq_mergeSort (xs : List Nat) : heapsort xs = xs.mergeSort (· ≤ ·) :=
  EqSorted_thm xs (Pre_holds xs)

/-- The three assertions the Python `check` loop makes for one input list:
`out == sorted(arr)`, `len(out) == len(arr)`, `sorted(out) == sorted(arr)`. -/
theorem check_one (arr : List Nat) :
    heapsort arr = arr.mergeSort (· ≤ ·) ∧ (heapsort arr).length = arr.length ∧
      (heapsort arr).mergeSort (· ≤ ·) = arr.mergeSort (· ≤ ·) :=
  ⟨heapsort_eq_mergeSort arr, heapsort_length arr,
    by rw [heapsort_eq_mergeSort arr,
      List.mergeSort_eq_self (· ≤ ·) (List.sorted_mergeSort' (· ≤ ·) arr)]⟩

/-- The `for arr in [[], [1], [2, 1], [3, 1, 2], [5, 13, 2, 25, 7, 17, 20, 8, 4]]`
loop of the Python `check` function. -/
theorem check_loop :
    ∀ arr ∈ ([[], [1], [2, 1], [3, 1, 2], [5, 13, 2, 25, 7, 17, 20, 8, 4]] : List (List Nat)),
      heapsort arr = arr.mergeSort (· ≤ ·) ∧ (heapsort arr).length = arr.length ∧
        (heapsort arr).mergeSort (· ≤ ·) = arr.mergeSort (· ≤ ·) := by
  intro arr harr
  have hcases : arr = [] ∨ arr = [1] ∨ arr = [2, 1] ∨ arr = [3, 1, 2] ∨
      arr = [5, 13, 2, 25, 7, 17, 20, 8, 4] := by simpa using harr
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact check_one []
  · exact check_one [1]
  · exact check_one [2, 1]
  · exact check_one [3, 1, 2]
  · exact check_one [5, 13, 2, 25, 7, 17, 20, 8, 4]

/-- The Python `check` requires a pre-condition violation to raise `ValueError`:
`candidate([1, -1])` must not return a list. -/
theorem check_pre_violation : heapsortInt [1, -1] = .error "Input must be List[Nat]" :=
  heapsortInt_error [1, -1] (by
    intro hPre
    have hneg : 0 ≤ (-1 : Int) := hPre (-1) (by simp)
    omega)

theorem check_pre_violation_none : (heapsortInt [1, -1]).toOption = (none : Option (List Int)) :=
  by decide

/-- On admissible input the checked entry point returns the sorted list. -/
theorem check_pre_ok : (heapsortInt [3, 1, 2]).toOption = some [1, 2, 3] := by decide

theorem preCheck_tests : preCheck [1, 2, 3] = true ∧ preCheck [1, -1] = false :=
  ⟨by decide, by decide⟩

end heapsort_algorithm
