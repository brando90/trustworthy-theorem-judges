import Mathlib

/-!
# Heap sort for a list of integers — VeriBench translation

This file formalises the Python program `heap_sort`, which

* dynamically checks its input with `pre(arr) = isinstance(arr, list) and
  all(isinstance(x, int) for x in arr)` and raises `ValueError` otherwise,
* sorts a `List[int]` with heap sort: build a max-heap, then repeatedly move the root
  (the maximum) to the end of the sorted prefix and `heapify` the shrunk heap,
* returns a *copy* for inputs of length `≤ 1`,
* is exercised by `check`, which asserts the result on fixed inputs (including `[]`,
  `[1]`, duplicates, sorted, reverse-sorted and an 11-element list) and asserts that a
  pre-condition violation raises `ValueError`.

## Modelling notes

* **Numeric layer.** The task is discrete: the Python program manipulates `int`s, so the
  Lean model uses `Int` throughout. No floating point is involved.
* **Pre-condition.** `arr : List Int` is statically a list of integers, so Python's
  `isinstance` test always succeeds on the modelled domain: `Pre arr` holds for every
  input (`pre_holds`). The *dynamic* check and the `ValueError` branch are nevertheless
  modelled faithfully on a heterogeneous element type `PyVal` by `pyPre` and
  `heapSortChecked`, which returns `Except.error "Input must be List[int]"` exactly when
  a non-integer element is present (`heapSortChecked_error`) and the sorted list
  otherwise (`heapSortChecked_ok`).
* **Algorithm.** The observable semantics of the Python heap sort is: *repeatedly remove
  a maximum element of the remaining input and append it to the output*. `extractMax`
  models one such extraction (the effect of `build_max_heap` followed by one root
  extraction plus `heapify`), and `heapSortGo` iterates it; its first argument is an
  explicit fuel counter playing the role of Python's loop bound `n = len(arr)`.
  `heapSort arr` runs the loop with fuel `arr.length`. The array-index bookkeeping of
  the Python code (`2*i+1`, `2*i+2`, in-place swaps) only serves to locate and remove a
  maximum, and the result is the *unique* sorted permutation of the input
  (`List.eq_of_perm_of_sorted`), which is what every theorem below states.
* **Imperative version.** `heapSortImp` is the imperative rendering: an `Id.run do`
  block with mutable state (`out`, the sorted prefix; `work`, the remaining heap; a
  loop counter), and `heapSortImp_eq` proves it agrees with the functional version.
-/

namespace heap_sort

open List

/-!
## 1. Implementation (functional definition)
-/

/-- One max-extraction step: for `xs ≠ []`, `extractMax xs = some (m, rest)` where `m` is
a maximum element of `xs` and `rest` is `xs` with one occurrence of `m` removed. This is
the observable effect of Python's `build_max_heap` followed by one root extraction and
the subsequent `heapify`. -/
def extractMax : List Int → Option (Int × List Int)
  | [] => none
  | x :: xs =>
      match extractMax xs with
      | none => some (x, [])
      | some (m, rest) => if x ≥ m then some (x, m :: rest) else some (m, x :: rest)

/-- The heap-sort extraction loop. `out` is the sorted prefix (ascending, every element
of the remaining list `xs` is `≤` every element of `out`), `fuel` bounds the number of
iterations exactly as Python's `for i in range(n - 1, 0, -1)` is bounded by `n`. -/
def heapSortGo : Nat → List Int → List Int → List Int
  | 0, _xs, out => out
  | fuel + 1, xs, out =>
      match extractMax xs with
      | none => out
      | some (m, rest) => heapSortGo fuel rest (m :: out)

/-- Heap sort of a list of integers. -/
def heapSort (arr : List Int) : List Int := heapSortGo arr.length arr []

/-!
## 2. Unit tests (the assertions of Python's `check`)
-/

#eval heapSort [3, 1, 2]
#eval heapSort []
#eval heapSort [1]
#eval heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

example : heapSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : heapSort [] = ([] : List Int) := by native_decide
example : heapSort [1] = [1] := by native_decide
example : heapSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSort [2, 1] = [1, 2] := by native_decide
example : heapSort [1, 2] = [1, 2] := by native_decide
example : heapSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : heapSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : heapSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : heapSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : List.Sorted (· ≤ ·) (heapSort [3, 1, 4, 1, 5, 9, 2, 6]) := by native_decide
example : List.Perm (heapSort [3, 1, 4, 1, 5, 9, 2, 6]) [3, 1, 4, 1, 5, 9, 2, 6] := by
  native_decide
example : (heapSort [3, 1, 4, 1, 5, 9, 2, 6]).length = 8 := by native_decide

/-!
## 3. Supporting lemmas: one extraction step and the extraction loop
-/

theorem extractMax_eq_none {xs : List Int} : extractMax xs = none ↔ xs = [] := by
  induction xs with
  | nil => simp [extractMax]
  | cons x xs _ih =>
      cases he : extractMax xs with
      | none =>
          have key : extractMax (x :: xs) = some (x, []) := by simp [extractMax, he]
          simp [key]
      | some p =>
          obtain ⟨m, rest⟩ := p
          have key : extractMax (x :: xs) =
              if x ≥ m then some (x, m :: rest) else some (m, x :: rest) := by
            simp [extractMax, he]
          rw [key]
          by_cases hge : x ≥ m <;> simp [hge]

/-- Specification of one max-extraction step: the extracted element belongs to the input,
is a maximum of the input, the remainder is a permutation of the input minus that
occurrence, and the remainder is exactly one element shorter. -/
theorem extractMax_spec_aux (xs : List Int) :
    ∀ (m : Int) (rest : List Int), extractMax xs = some (m, rest) →
      m ∈ xs ∧ List.Perm (m :: rest) xs ∧ (∀ y ∈ xs, y ≤ m) ∧ rest.length + 1 = xs.length := by
  induction xs with
  | nil => intro m rest h; exact absurd h (by simp [extractMax])
  | cons x xs ih =>
      intro m rest h
      cases he : extractMax xs with
      | none =>
          have hxs : xs = [] := extractMax_eq_none.mp he
          subst hxs
          have key : extractMax (x :: []) = some (x, []) := by simp [extractMax]
          rw [key] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hmx, hrest⟩ := h
          subst m
          subst rest
          simp
      | some p =>
          obtain ⟨mm, rr⟩ := p
          have ihmm := ih mm rr he
          have key : extractMax (x :: xs) =
              if x ≥ mm then some (x, mm :: rr) else some (mm, x :: rr) := by
            simp [extractMax, he]
          rw [key] at h
          by_cases hge : x ≥ mm
          · rw [if_pos hge] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hmx, hrest⟩ := h
            subst m
            subst rest
            refine ⟨by simp, List.Perm.cons x ihmm.2.1, ?_, by simp [ihmm.2.2.2]⟩
            intro y hy
            rw [List.mem_cons] at hy
            cases hy with
            | inl hy => subst hy; exact le_rfl
            | inr hy => exact le_trans (ihmm.2.2.1 y hy) hge
          · rw [if_neg hge] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hmx, hrest⟩ := h
            subst m
            subst rest
            refine ⟨by simp [ihmm.1],
              List.Perm.trans (List.Perm.swap x mm rr) (List.Perm.cons x ihmm.2.1), ?_,
              by simp [ihmm.2.2.2]⟩
            intro y hy
            rw [List.mem_cons] at hy
            cases hy with
            | inl hy => subst hy; exact le_of_not_ge hge
            | inr hy => exact ihmm.2.2.1 y hy

theorem extractMax_spec {xs : List Int} {m : Int} {rest : List Int}
    (h : extractMax xs = some (m, rest)) :
    m ∈ xs ∧ List.Perm (m :: rest) xs ∧ (∀ y ∈ xs, y ≤ m) ∧ rest.length + 1 = xs.length :=
  extractMax_spec_aux xs m rest h

theorem heapSortGo_perm (fuel : Nat) :
    ∀ (xs out : List Int), xs.length ≤ fuel →
      List.Perm (heapSortGo fuel xs out) (out ++ xs) := by
  induction fuel with
  | zero =>
      intro xs out h
      have hxs : xs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
      subst hxs
      simp [heapSortGo]
  | succ fuel ih =>
      intro xs out h
      cases he : extractMax xs with
      | none =>
          have hxs : xs = [] := extractMax_eq_none.mp he
          subst hxs
          simp [heapSortGo, extractMax]
      | some p =>
          obtain ⟨m, rest⟩ := p
          have hspec := extractMax_spec he
          have hlen : rest.length ≤ fuel := by
            have := hspec.2.2.2
            omega
          have h1 : heapSortGo (fuel + 1) xs out = heapSortGo fuel rest (m :: out) := by
            simp [heapSortGo, he]
          have h2 : List.Perm ((m :: out) ++ rest) (out ++ xs) := by
            rw [List.cons_append]
            exact List.Perm.trans
              (List.perm_middle (l₁ := out) (a := m) (l₂ := rest)).symm
              (List.Perm.append (List.Perm.refl out) hspec.2.1)
          rw [h1]
          exact List.Perm.trans (ih rest (m :: out) hlen) h2

theorem heapSortGo_length (fuel : Nat) :
    ∀ (xs out : List Int), xs.length ≤ fuel →
      (heapSortGo fuel xs out).length = out.length + xs.length := by
  induction fuel with
  | zero =>
      intro xs out h
      have hxs : xs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
      subst hxs
      simp [heapSortGo]
  | succ fuel ih =>
      intro xs out h
      cases he : extractMax xs with
      | none =>
          have hxs : xs = [] := extractMax_eq_none.mp he
          subst hxs
          simp [heapSortGo, extractMax]
      | some p =>
          obtain ⟨m, rest⟩ := p
          have hspec := extractMax_spec he
          have hlen : rest.length ≤ fuel := by
            have := hspec.2.2.2
            omega
          have h1 : heapSortGo (fuel + 1) xs out = heapSortGo fuel rest (m :: out) := by
            simp [heapSortGo, he]
          rw [h1, ih rest (m :: out) hlen]
          simp only [List.length_cons]
          have := hspec.2.2.2
          omega

theorem heapSortGo_sorted (fuel : Nat) :
    ∀ (xs out : List Int), xs.length ≤ fuel → List.Sorted (· ≤ ·) out →
      (∀ y ∈ xs, ∀ z ∈ out, y ≤ z) → List.Sorted (· ≤ ·) (heapSortGo fuel xs out) := by
  induction fuel with
  | zero =>
      intro xs out h hs _hle
      have hxs : xs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
      subst hxs
      simpa [heapSortGo] using hs
  | succ fuel ih =>
      intro xs out h hs hle
      cases he : extractMax xs with
      | none =>
          have hxs : xs = [] := extractMax_eq_none.mp he
          subst hxs
          simpa [heapSortGo, extractMax] using hs
      | some p =>
          obtain ⟨m, rest⟩ := p
          have hspec := extractMax_spec he
          have hlen : rest.length ≤ fuel := by
            have := hspec.2.2.2
            omega
          have h1 : heapSortGo (fuel + 1) xs out = heapSortGo fuel rest (m :: out) := by
            simp [heapSortGo, he]
          rw [h1]
          refine ih rest (m :: out) hlen ?_ ?_
          · rw [List.sorted_cons]
            exact ⟨hle m hspec.1, hs⟩
          · intro y hy z hz
            have hyxs : y ∈ xs := hspec.2.1.subset (List.mem_cons_of_mem m hy)
            rw [List.mem_cons] at hz
            cases hz with
            | inl hzm => rw [hzm]; exact hspec.2.2.1 y hyxs
            | inr hz => exact hle y hyxs z hz

/-!
## 4. Consequences for `heapSort`
-/

theorem heapSort_perm (arr : List Int) : List.Perm (heapSort arr) arr := by
  have h := heapSortGo_perm arr.length arr [] (Nat.le_refl arr.length)
  simpa [heapSort] using h

theorem heapSort_length (arr : List Int) : (heapSort arr).length = arr.length := by
  have h := heapSortGo_length arr.length arr [] (Nat.le_refl arr.length)
  simpa [heapSort] using h

theorem heapSort_sorted (arr : List Int) : List.Sorted (· ≤ ·) (heapSort arr) :=
  heapSortGo_sorted arr.length arr [] (Nat.le_refl arr.length) List.sorted_nil (by simp)

/-- Python: `if len(arr) <= 1: return arr.copy()` — the empty list. -/
theorem heapSort_nil : heapSort [] = [] := by simp [heapSort, heapSortGo]

/-- Python: `if len(arr) <= 1: return arr.copy()` — a single element. -/
theorem heapSort_singleton (x : Int) : heapSort [x] = [x] := by
  simp [heapSort, heapSortGo, extractMax]

lemma sorted_append_singleton {l : List Int} {m : Int} (hs : List.Sorted (· ≤ ·) l)
    (hle : ∀ z ∈ l, z ≤ m) : List.Sorted (· ≤ ·) (l ++ [m]) := by
  have : List.Pairwise (· ≤ ·) (l ++ [m]) := by
    rw [List.pairwise_append]
    refine ⟨hs, by simp, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb
    exact hle a ha
  exact this

/-- "Extract the maximum and place it at the end of the sorted portion": if `m` dominates
every element of `arr`, then `m` is the maximum extracted first and lands at the end. -/
theorem heapSort_append_max (arr : List Int) (m : Int) (h : ∀ x ∈ arr, x ≤ m) :
    heapSort (arr ++ [m]) = heapSort arr ++ [m] := by
  have h1 : List.Sorted (· ≤ ·) (heapSort (arr ++ [m])) := heapSort_sorted _
  have h2 : List.Perm (heapSort (arr ++ [m])) (arr ++ [m]) := heapSort_perm _
  have h3 : List.Sorted (· ≤ ·) (heapSort arr ++ [m]) :=
    sorted_append_singleton (heapSort_sorted arr)
      (fun z hz => h z ((heapSort_perm arr).subset hz))
  have h4 : List.Perm (heapSort arr ++ [m]) (arr ++ [m]) :=
    List.Perm.append_right [m] (heapSort_perm arr)
  exact List.eq_of_perm_of_sorted (List.Perm.trans h2 h4.symm) h1 h3

theorem heapSort_idempotent (arr : List Int) : heapSort (heapSort arr) = heapSort arr :=
  List.eq_of_perm_of_sorted (heapSort_perm (heapSort arr))
    (heapSort_sorted (heapSort arr)) (heapSort_sorted arr)

/-- The first element of the output is the minimum of a non-empty input. -/
theorem heapSort_min_le (arr : List Int) (_hne : arr ≠ []) :
    ∀ x ∈ arr, (heapSort arr).head! ≤ x := by
  have h1 : List.Sorted (· ≤ ·) (heapSort arr) := heapSort_sorted arr
  have h2 : List.Perm (heapSort arr) arr := heapSort_perm arr
  intro x hx
  have hx' : x ∈ heapSort arr := h2.symm.subset hx
  cases h3 : heapSort arr with
  | nil => rw [h3] at hx'; exact absurd hx' List.not_mem_nil
  | cons a t =>
      have hs : List.Sorted (· ≤ ·) (a :: t) := by rw [← h3]; exact h1
      rw [List.sorted_cons] at hs
      rw [h3] at hx'
      rw [List.mem_cons] at hx'
      have hhead : (a :: t).head! = a := rfl
      rw [hhead]
      cases hx' with
      | inl h => subst h; exact le_rfl
      | inr h => exact hs.1 x h

/-- `heapSort` agrees with Mathlib's reference sorting routine: a sorted permutation of a
list is unique, so any correct sort returns the same list. -/
theorem heapSort_eq_insertionSort (arr : List Int) :
    heapSort arr = List.insertionSort (· ≤ ·) arr :=
  List.eq_of_perm_of_sorted
    (List.Perm.trans (heapSort_perm arr) (List.perm_insertionSort (· ≤ ·) arr).symm)
    (heapSort_sorted arr) (List.sorted_insertionSort (· ≤ ·) arr)

/-!
## 5. Pre-condition (Python's `pre`) and the `ValueError` branch
-/

/-- A Python list element: either an `int`, or something else — e.g. the `float` `2.5` of
Python's negative test `candidate([1, 2.5])`. -/
inductive PyVal where
  | int (i : Int)
  | nonInt

/-- The integer denoted by a `PyVal`; only used on inputs that passed `pyPre`. -/
def pyValToInt : PyVal → Int
  | PyVal.int i => i
  | PyVal.nonInt => 0

/-- `all(isinstance(x, int) for x in arr)`. -/
def pyPre : List PyVal → Bool
  | [] => true
  | PyVal.int _ :: t => pyPre t
  | PyVal.nonInt :: _ => false

@[simp] theorem pyPre_map_int (arr : List Int) : pyPre (arr.map PyVal.int) = true := by
  induction arr with
  | nil => rfl
  | cons x xs ih => simp [pyPre, List.map_cons, ih]

theorem pyValToInt_map_int (arr : List Int) : (arr.map PyVal.int).map pyValToInt = arr := by
  induction arr with
  | nil => rfl
  | cons x xs ih => simp [List.map_cons, pyValToInt, ih]

/-- The pre-condition of the Python program:
`isinstance(arr, list) and all(isinstance(x, int) for x in arr)`. A Lean value of type
`List Int` is a list of integers by construction, so the dynamic check always succeeds on
the modelled domain — but it is *stated and proved* (`pre_holds`), not assumed away. -/
@[reducible] def Pre (arr : List Int) : Prop := pyPre (arr.map PyVal.int) = true

theorem pre_holds (arr : List Int) : Pre arr := pyPre_map_int arr

/-- `heap_sort` together with Python's dynamic check; `raise ValueError("Input must be
List[int]")` is modelled by `Except.error`. -/
def heapSortChecked (arr : List PyVal) : Except String (List Int) :=
  if pyPre arr then .ok (heapSort (arr.map pyValToInt))
  else .error "Input must be List[int]"

/-- Python's negative test: a pre-condition violation raises instead of returning. -/
theorem heapSortChecked_error (arr : List PyVal) (h : pyPre arr = false) :
    heapSortChecked arr = .error "Input must be List[int]" := by simp [heapSortChecked, h]

/-- On admissible input the checked version returns the sorted list. -/
theorem heapSortChecked_ok (arr : List Int) :
    heapSortChecked (arr.map PyVal.int) = .ok (heapSort arr) := by
  have hcomp : pyValToInt ∘ PyVal.int = id := by
    funext i
    rfl
  simp [heapSortChecked, hcomp, List.map_id]

example : heapSortChecked [PyVal.int 1, PyVal.nonInt] =
    .error "Input must be List[int]" := rfl
example : heapSortChecked [PyVal.int 3, PyVal.int 1, PyVal.int 2] = .ok [1, 2, 3] := rfl

/-!
## 6. Properties of the implementation
-/

/-- The output is sorted in non-decreasing order. -/
@[reducible] def sorted_prop (_arr out : List Int) : Prop := List.Sorted (· ≤ ·) out

/-- The output is a permutation of the input: no element is lost, duplicated or invented. -/
@[reducible] def perm_prop (arr out : List Int) : Prop := List.Perm out arr

/-- The output has the same length as the input. -/
@[reducible] def length_prop (arr out : List Int) : Prop := out.length = arr.length

/-- Membership is preserved by sorting. -/
@[reducible] def mem_prop (arr out : List Int) : Prop := ∀ x : Int, x ∈ out ↔ x ∈ arr

/-- Sorting an already sorted list is the identity (idempotence of a sorting routine). -/
@[reducible] def idempotent_prop (_arr out : List Int) : Prop := heapSort out = out

/-- "Repeatedly extracts the maximum element and places it at the end of the sorted
portion": appending a global maximum to the input appends it to the output. -/
@[reducible] def max_last_prop (arr out : List Int) : Prop :=
  ∀ m : Int, (∀ x ∈ arr, x ≤ m) → heapSort (arr ++ [m]) = out ++ [m]

/-- For a non-empty input the head of the output is a minimum of the input. -/
@[reducible] def min_first_prop (arr out : List Int) : Prop := arr ≠ [] → ∀ x ∈ arr, out.head! ≤ x

theorem sorted_thm (arr : List Int) : sorted_prop arr (heapSort arr) := heapSort_sorted arr

theorem perm_thm (arr : List Int) : perm_prop arr (heapSort arr) := heapSort_perm arr

theorem length_thm (arr : List Int) : length_prop arr (heapSort arr) := heapSort_length arr

theorem mem_thm (arr : List Int) : mem_prop arr (heapSort arr) :=
  fun _x => ⟨fun h => (heapSort_perm arr).subset h, fun h => (heapSort_perm arr).symm.subset h⟩

theorem idempotent_thm (arr : List Int) : idempotent_prop arr (heapSort arr) :=
  heapSort_idempotent arr

theorem max_last_thm (arr : List Int) : max_last_prop arr (heapSort arr) :=
  heapSort_append_max arr

theorem min_first_thm (arr : List Int) : min_first_prop arr (heapSort arr) :=
  heapSort_min_le arr

/-- Python's `if len(arr) <= 1: return arr.copy()`. -/
theorem edge_thm (x : Int) : heapSort [] = [] ∧ heapSort [x] = [x] :=
  ⟨heapSort_nil, heapSort_singleton x⟩

/-!
## 7. Post-condition
-/

/-- The post-condition of `heap_sort`: the result is sorted, is a permutation of the input
and has the same length. These three conditions characterise the result *uniquely*
(`List.eq_of_perm_of_sorted`), i.e. they fully specify what a sorting routine must return. -/
@[reducible] def Post_prop (arr out : List Int) : Prop :=
  sorted_prop arr out ∧ perm_prop arr out ∧ length_prop arr out

/-!
## 8. Property-based tests
-/

/-- All lists of length `n` over the alphabet `alpha`; used for exhaustive bounded PBTs. -/
def allListsOf : Nat → List Int → List (List Int)
  | 0, _ => [[]]
  | n + 1, alpha => alpha.flatMap fun a => (allListsOf n alpha).map fun l => a :: l

-- Randomised PBTs (Plausible ships with Mathlib). Each one states the executable Boolean
-- form of a property over the implementation; the file fails to compile if Plausible finds
-- a counterexample.
#eval Plausible.Testable.check (∀ xs : List Int, sorted_prop xs (heapSort xs))
#eval Plausible.Testable.check (∀ xs : List Int, perm_prop xs (heapSort xs))
#eval Plausible.Testable.check (∀ xs : List Int, length_prop xs (heapSort xs))
-- `mem_prop xs (heapSort xs)` written out as an explicit binder so that Plausible's
-- `Testable` instance for universally quantified properties applies:
#eval Plausible.Testable.check (∀ (xs : List Int) (x : Int), x ∈ heapSort xs ↔ x ∈ xs)
#eval Plausible.Testable.check (∀ xs : List Int, idempotent_prop xs (heapSort xs))
#eval Plausible.Testable.check (∀ xs : List Int, Post_prop xs (heapSort xs))
#eval Plausible.Testable.check (∀ arr : List Int, Pre arr)
#eval Plausible.Testable.check (∀ xs : List Int,
  heapSort (xs ++ [xs.foldl max 0]) = heapSort xs ++ [xs.foldl max 0])
#eval Plausible.Testable.check (∀ xs : List Int, heapSort xs = List.insertionSort (· ≤ ·) xs)
#eval Plausible.Testable.check (∀ xs : List Int, decide (xs = []) ||
  (xs.all (fun x => decide ((heapSort xs).head! ≤ x)) : Bool))

-- Bounded (exhaustive) PBTs: all 1 + 5 + 25 + 125 lists of length ≤ 3 over a 5-element
-- alphabet, checked for every executable property at once.
example : (allListsOf 3 [-3, -1, 0, 2, 4]).all (fun xs =>
      decide (List.Sorted (· ≤ ·) (heapSort xs)) &&
      decide (List.Perm (heapSort xs) xs) &&
      ((heapSort xs).length == xs.length) &&
      decide (heapSort (heapSort xs) = heapSort xs) &&
      (xs.all (fun x => decide (x ∈ heapSort xs))) &&
      (heapSort xs).all (fun y => decide (y ∈ xs))) = true := by native_decide

example : (allListsOf 3 [-3, -1, 0, 2, 4]).all (fun xs =>
      (xs.all (fun x => decide (x ≤ 5)) : Bool) &&
      (heapSort (xs ++ [5]) == heapSort xs ++ [5])) = true := by native_decide

-- the same property, exhaustively, for eleven different candidate maxima `m`
example : (allListsOf 3 [-3, -1, 0, 2, 4]).all (fun xs =>
      (List.range 11).all (fun k =>
        let m : Int := k - 5
        (!(xs.all (fun x => decide (x ≤ m))) ||
          (heapSort (xs ++ [m]) == heapSort xs ++ [m])))) = true := by native_decide

-- `heapSort` coincides with Mathlib's reference sort on every small input
example : (allListsOf 3 [-3, -1, 0, 2, 4]).all (fun xs =>
      (heapSort xs == List.insertionSort (· ≤ ·) xs)) = true := by native_decide

example : (allListsOf 3 [-3, -1, 0, 2, 4]).all (fun xs =>
      decide (xs = []) || (xs.all (fun x => decide ((heapSort xs).head! ≤ x)) : Bool)) = true :=
  by native_decide

example : (allListsOf 2 [-1, 0, 7]).all (fun xs => decide (Pre xs)) = true := by native_decide

/-!
## 9. Correctness: `Pre → Post`
-/

theorem heap_sort_correct (arr : List Int) (h : Pre arr) : Post_prop arr (heapSort arr) := by
  have hpre : pyPre (arr.map PyVal.int) = true := h
  exact ⟨heapSort_sorted arr, heapSort_perm arr, heapSort_length arr⟩

/-- Correctness together with the additional properties proved above. -/
theorem heap_sort_correct_full (arr : List Int) (h : Pre arr) :
    Post_prop arr (heapSort arr) ∧ mem_prop arr (heapSort arr) ∧
      idempotent_prop arr (heapSort arr) ∧ max_last_prop arr (heapSort arr) ∧
      min_first_prop arr (heapSort arr) := by
  have hpre : pyPre (arr.map PyVal.int) = true := h
  exact ⟨heap_sort_correct arr h, mem_thm arr, idempotent_thm arr, max_last_thm arr,
    min_first_thm arr⟩

/-!
## 10. Imperative implementation (`Id.run do` with mutable state)
-/

/-- The imperative worker loop. `fuel` is the loop counter (Python's `n = len(result)`),
`work` the not-yet-sorted part and `out` the sorted prefix. `o` and `w` are `let mut`
variables that are *reassigned* in the loop body, mirroring the in-place mutation of
Python's `result` array (`result[0], result[i] = result[i], result[0]` followed by
`heapify`). -/
def heapSortImpGo : Nat → List Int → List Int → Id (List Int)
  | 0, _work, out => do return out
  | fuel + 1, work, out => do
      let mut o := out
      let mut w := work
      match extractMax w with
      | none => return o
      | some (m, w') =>
          o := m :: o
          w := w'
          heapSortImpGo fuel w o

/-- Imperative heap sort: an `Id.run do` block with mutable state. -/
def heapSortImp (arr : List Int) : List Int :=
  Id.run do
    let mut out : List Int := []
    let mut work := arr
    let mut fuel := arr.length
    heapSortImpGo fuel work out

/-!
## 11. Imperative tests
-/

#eval heapSortImp [3, 1, 2]
#eval heapSortImp []
#eval heapSortImp [1]
#eval heapSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

example : heapSortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSortImp [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapSortImp [2, 1, 3] = [1, 2, 3] := by native_decide
example : heapSortImp [] = ([] : List Int) := by native_decide
example : heapSortImp [1] = [1] := by native_decide
example : heapSortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapSortImp [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSortImp [2, 1] = [1, 2] := by native_decide
example : heapSortImp [1, 2] = [1, 2] := by native_decide
example : heapSortImp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : heapSortImp [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : heapSortImp [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapSortImp [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : heapSortImp [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

-- Bounded PBT: the imperative version satisfies the post-condition and agrees with the
-- functional version on every list of length ≤ 3 over a 5-element alphabet.
example : (allListsOf 3 [-3, -1, 0, 2, 4]).all (fun xs =>
      decide (List.Sorted (· ≤ ·) (heapSortImp xs)) &&
      decide (List.Perm (heapSortImp xs) xs) &&
      ((heapSortImp xs).length == xs.length) &&
      (heapSortImp xs == heapSort xs)) = true := by native_decide

/-!
## 12. Equivalence: functional = imperative
-/

theorem heapSortImpGo_eq (fuel : Nat) (xs out : List Int) :
    heapSortImpGo fuel xs out = heapSortGo fuel xs out := by
  induction fuel generalizing xs out with
  | zero => rfl
  | succ fuel ih =>
      cases he : extractMax xs with
      | none =>
          have h1 : heapSortImpGo (fuel + 1) xs out = out := by
            simp [heapSortImpGo, he]; rfl
          have h2 : heapSortGo (fuel + 1) xs out = out := by simp [heapSortGo, he]
          rw [h1, h2]
      | some p =>
          obtain ⟨m, rest⟩ := p
          have h1 : heapSortImpGo (fuel + 1) xs out = heapSortImpGo fuel rest (m :: out) := by
            simp [heapSortImpGo, he]
          have h2 : heapSortGo (fuel + 1) xs out = heapSortGo fuel rest (m :: out) := by
            simp [heapSortGo, he]
          rw [h1, h2]
          exact ih rest (m :: out)

theorem heapSortImp_eq (arr : List Int) : heapSortImp arr = heapSort arr := by
  have h := heapSortImpGo_eq arr.length arr []
  simp [heapSortImp, heapSort, Id.run, h]

theorem heapSortImp_eq_insertionSort (arr : List Int) :
    heapSortImp arr = List.insertionSort (· ≤ ·) arr := by
  rw [heapSortImp_eq, heapSort_eq_insertionSort]

/-- The imperative implementation satisfies the same post-condition. -/
theorem heapSortImp_correct (arr : List Int) (h : Pre arr) : Post_prop arr (heapSortImp arr) := by
  rw [heapSortImp_eq]
  exact heap_sort_correct arr h

/-- The imperative implementation enjoys every stated property. -/
theorem heapSortImp_prop_all (arr : List Int) :
    sorted_prop arr (heapSortImp arr) ∧ perm_prop arr (heapSortImp arr) ∧
      length_prop arr (heapSortImp arr) ∧ mem_prop arr (heapSortImp arr) ∧
      idempotent_prop arr (heapSortImp arr) := by
  rw [heapSortImp_eq]
  exact ⟨sorted_thm arr, perm_thm arr, length_thm arr, mem_thm arr, idempotent_thm arr⟩

end heap_sort
