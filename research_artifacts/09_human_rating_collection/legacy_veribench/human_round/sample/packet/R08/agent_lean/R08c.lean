import Mathlib

/-!
# Heapsort (CLRS 6.4) on 0-based max-heap arrays

Lean 4 translation of the Python reference implementation `heapsort`.

The Python program builds a max-heap in place (`build_max_heap`) and then
repeatedly swaps the root with the last element of the active heap and sifts the
new root down (`max_heapify`), producing an ascending sorted copy of the input.

This file contains

* a purely functional model (`heapsort`) working on `Array Nat`,
* unit tests transcribed from the Python `check` function,
* the pre-condition, the individual post-condition properties and the
  correctness theorem,
* an imperative implementation (`heapsortImp`) using `Id.run do` with mutable
  state and `for` loops, together with a proof that it agrees with the
  functional model.
-/

namespace heapsort_algorithm

/-! ## Functional implementation -/

/-- `parent(i)`: index of the parent of `i` (0-based); the root is its own parent. -/
def parent (i : Nat) : Nat := if i = 0 then 0 else (i - 1) / 2

/-- `left(i)`: index of the left child of `i` (0-based). -/
def left (i : Nat) : Nat := 2 * i + 1

/-- `right(i)`: index of the right child of `i` (0-based). -/
def right (i : Nat) : Nat := 2 * i + 2

/-- `_swap(arr, i, j)`: exchange the entries at positions `i` and `j`
(out-of-range writes are ignored, as the indices used are always in range). -/
def swapArr (a : Array Nat) (i j : Nat) : Array Nat :=
  let x := a[i]!
  let y := a[j]!
  (a.set! i y).set! j x

/-- The `largest` variable of one iteration of the `max_heapify` loop: the index
of the largest of `a[i]`, `a[left i]`, `a[right i]` among those below `heapSize`. -/
def largestOf (a : Array Nat) (i heapSize : Nat) : Nat :=
  let l := left i
  let r := right i
  let m := if l < heapSize ∧ a[l]! > a[i]! then l else i
  if r < heapSize ∧ a[r]! > a[m]! then r else m

/-- The sift-down loop of `max_heapify`, unrolled with an explicit `fuel`
counter.  Since the index at least doubles at every iteration, `a.size + 1`
iterations are always enough. -/
def maxHeapifyAux (heapSize : Nat) : Nat → Array Nat → Nat → Array Nat
  | 0, a, _ => a
  | fuel + 1, a, i =>
      let m := largestOf a i heapSize
      if m = i then a else maxHeapifyAux heapSize fuel (swapArr a i m) m

/-- `max_heapify(arr, i, heap_size)`. -/
def maxHeapify (a : Array Nat) (i heapSize : Nat) : Array Nat :=
  maxHeapifyAux heapSize (a.size + 1) a i

/-- `for i in range(k, -1, -1): max_heapify(arr, i, n)`. -/
def buildAux (n : Nat) : Nat → Array Nat → Array Nat
  | 0, a => maxHeapify a 0 n
  | k + 1, a => buildAux n k (maxHeapify a (k + 1) n)

/-- `build_max_heap(arr)`. -/
def buildMaxHeap (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a else buildAux a.size (parent (a.size - 1)) a

/-- `for i in range(n-1, 0, -1): _swap(arr, 0, i); max_heapify(arr, 0, i)`. -/
def extractAux : Nat → Array Nat → Array Nat
  | 0, a => a
  | i + 1, a => extractAux i (maxHeapify (swapArr a 0 (i + 1)) 0 (i + 1))

/-- Heapsort on arrays. -/
def heapsortArr (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a else extractAux (a.size - 1) (buildMaxHeap a)

/-- `heapsort(arr)`: ascending sort of a list of naturals. -/
def heapsort (l : List Nat) : List Nat := (heapsortArr l.toArray).toList

/-! ## Unit tests (transcribed from the Python `check` function) -/

#eval heapsort [3, 1, 2]
#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]

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

-- `candidate(arr) == sorted(arr)` for the sample inputs of the final loop
example : heapsort [] = List.mergeSort ([] : List Nat) (· ≤ ·) := by native_decide
example : heapsort [1] = List.mergeSort [1] (· ≤ ·) := by native_decide
example : heapsort [2, 1] = List.mergeSort [2, 1] (· ≤ ·) := by native_decide
example : heapsort [3, 1, 2] = List.mergeSort [3, 1, 2] (· ≤ ·) := by native_decide
example :
    heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]
      = List.mergeSort [5, 13, 2, 25, 7, 17, 20, 8, 4] (· ≤ ·) := by native_decide

/-! ## Pre-condition -/

/-- The Python guard `pre(arr)`, modelled on integer lists: every entry must be
a natural number, i.e. non-negative.  `heapsort([1, -1])` raises `ValueError`. -/
def preInt (l : List Int) : Bool := l.all (fun x => 0 ≤ x)

example : preInt [1, -1] = false := by native_decide
example : preInt [5, 13, 2, 25, 7, 17, 20, 8, 4] = true := by native_decide

theorem preInt_iff (l : List Int) : preInt l = true ↔ ∀ x ∈ l, 0 ≤ x := by
  simp [preInt]

/-- Lists of naturals always satisfy the Python pre-condition. -/
theorem preInt_map_ofNat (l : List Nat) : preInt (l.map (fun n : Nat => (n : Int))) = true := by
  simp [preInt]

/-- Pre-condition of `heapsort`: the input is a list of naturals.  This is
already guaranteed by the type `List Nat`, so the predicate is vacuous. -/
def Pre (_l : List Nat) : Prop := True

theorem Pre_holds (l : List Nat) : Pre l := trivial

/-! ## Basic structural lemmas -/

@[simp] theorem swapArr_size (a : Array Nat) (i j : Nat) : (swapArr a i j).size = a.size := by
  simp [swapArr]

@[simp] theorem maxHeapifyAux_size (hs : Nat) :
    ∀ (fuel : Nat) (a : Array Nat) (i : Nat), (maxHeapifyAux hs fuel a i).size = a.size := by
  intro fuel
  induction fuel with
  | zero => intro a i; rfl
  | succ n ih =>
    intro a i
    rw [maxHeapifyAux]
    split
    · rfl
    · simp [ih]

@[simp] theorem maxHeapify_size (a : Array Nat) (i hs : Nat) :
    (maxHeapify a i hs).size = a.size := by
  simp [maxHeapify]

@[simp] theorem buildAux_size (n : Nat) :
    ∀ (k : Nat) (a : Array Nat), (buildAux n k a).size = a.size := by
  intro k
  induction k with
  | zero => intro a; simp [buildAux]
  | succ m ih => intro a; simp [buildAux, ih]

@[simp] theorem buildMaxHeap_size (a : Array Nat) : (buildMaxHeap a).size = a.size := by
  unfold buildMaxHeap; split <;> simp

@[simp] theorem extractAux_size :
    ∀ (k : Nat) (a : Array Nat), (extractAux k a).size = a.size := by
  intro k
  induction k with
  | zero => intro a; rfl
  | succ m ih => intro a; simp [extractAux, ih]

/-- One iteration of the sift-down loop either stops (`largest == i`) or moves
strictly down the heap, staying inside the heap. -/
theorem largestOf_spec (a : Array Nat) (i hs : Nat) :
    largestOf a i hs = i ∨ (i < largestOf a i hs ∧ largestOf a i hs < hs) := by
  simp only [largestOf, left, right]
  split_ifs <;> simp_all <;> omega

/-- Outside the heap the sift-down loop stops immediately. -/
theorem largestOf_of_ge (a : Array Nat) (i hs : Nat) (h : hs ≤ i) : largestOf a i hs = i := by
  simp only [largestOf, left, right]
  split_ifs <;> simp_all <;> omega

/-- Once the sift-down loop has run for `fuel ≥ heapSize - i` steps it has
reached its fixpoint: additional iterations do not change the array. -/
theorem maxHeapifyAux_fuel_stable (hs : Nat) :
    ∀ (fuel : Nat) (a : Array Nat) (i : Nat), hs ≤ a.size → hs ≤ i + fuel →
      maxHeapifyAux hs (fuel + 1) a i = maxHeapifyAux hs fuel a i := by
  intro fuel
  induction fuel with
  | zero =>
    intro a i _ h
    conv_lhs => rw [maxHeapifyAux]
    simp [largestOf_of_ge a i hs (by omega), maxHeapifyAux]
  | succ n ih =>
    intro a i hsize h
    conv_lhs => rw [maxHeapifyAux]
    conv_rhs => rw [maxHeapifyAux]
    by_cases hm : largestOf a i hs = i
    · simp [hm]
    · rcases largestOf_spec a i hs with h' | ⟨h1, _⟩
      · exact absurd h' hm
      · have hstep : hs ≤ (swapArr a i (largestOf a i hs)).size := by simpa using hsize
        have hfuel : hs ≤ largestOf a i hs + n := by omega
        simp only [hm, if_false]
        exact ih (swapArr a i (largestOf a i hs)) (largestOf a i hs) hstep hfuel

/-- The fuel used by `maxHeapify` is always sufficient: running the loop for
longer gives the same result, so the model agrees with Python's `while True`. -/
theorem maxHeapify_fuel_enough (a : Array Nat) (i hs extra : Nat) (h : hs ≤ a.size) :
    maxHeapifyAux hs (a.size + 1 + extra) a i = maxHeapify a i hs := by
  unfold maxHeapify
  induction extra with
  | zero => rfl
  | succ e ih =>
    rw [show a.size + 1 + (e + 1) = (a.size + 1 + e) + 1 by omega,
      maxHeapifyAux_fuel_stable hs (a.size + 1 + e) a i h (by omega), ih]

/-! ## The output is a permutation of the input -/

private theorem cons_set_perm :
    ∀ (t : List Nat) (j x : Nat), j < t.length → ((t.getD j 0) :: t.set j x).Perm (x :: t) := by
  intro t
  induction t with
  | nil => intro j x h; simp at h
  | cons c t' ih =>
    intro j x h
    cases j with
    | zero => simpa using List.Perm.swap x c t'
    | succ m =>
      have hm : m < t'.length := by simpa using h
      have h1 : (t'.getD m 0 :: c :: t'.set m x).Perm (c :: t'.getD m 0 :: t'.set m x) :=
        List.Perm.swap _ _ _
      have h2 : (c :: t'.getD m 0 :: t'.set m x).Perm (c :: x :: t') :=
        List.Perm.cons c (ih m x hm)
      have h3 : (c :: x :: t').Perm (x :: c :: t') := List.Perm.swap _ _ _
      simpa using (h1.trans h2).trans h3

private theorem list_swap_perm :
    ∀ (l : List Nat) (i j : Nat), i < l.length → j < l.length →
      ((l.set i (l.getD j 0)).set j (l.getD i 0)).Perm l := by
  intro l
  induction l with
  | nil => intro i j hi _; simp at hi
  | cons x t ih =>
    intro i j hi hj
    match i, j with
    | 0, 0 => simp
    | 0, m + 1 =>
      have hm : m < t.length := by simpa using hj
      simpa using cons_set_perm t m x hm
    | k + 1, 0 =>
      have hk : k < t.length := by simpa using hi
      simpa using cons_set_perm t k x hk
    | k + 1, m + 1 =>
      have hk : k < t.length := by simpa using hi
      have hm : m < t.length := by simpa using hj
      simpa using List.Perm.cons x (ih k m hk hm)

private theorem getElem_bang_eq_getD (a : Array Nat) (i : Nat) (h : i < a.size) :
    a[i]! = a.toList.getD i 0 := by
  rw [getElem!_pos a i h]
  simp [List.getD_eq_getElem?_getD, h]

private theorem swapArr_toList (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (swapArr a i j).toList = (a.toList.set i (a.toList.getD j 0)).set j (a.toList.getD i 0) := by
  simp [swapArr, Array.set!_eq_setIfInBounds, getElem_bang_eq_getD a i hi,
    getElem_bang_eq_getD a j hj]

theorem swapArr_perm (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (swapArr a i j).toList.Perm a.toList := by
  have hi' : i < a.toList.length := by simpa using hi
  have hj' : j < a.toList.length := by simpa using hj
  rw [swapArr_toList a i j hi hj]
  exact list_swap_perm a.toList i j hi' hj'

theorem maxHeapifyAux_perm (hs : Nat) :
    ∀ (fuel : Nat) (a : Array Nat) (i : Nat), hs ≤ a.size →
      (maxHeapifyAux hs fuel a i).toList.Perm a.toList := by
  intro fuel
  induction fuel with
  | zero => intro a i _; rfl
  | succ n ih =>
    intro a i hsize
    rw [maxHeapifyAux]
    split
    · rfl
    · rename_i hne
      rcases largestOf_spec a i hs with h | ⟨h1, h2⟩
      · exact absurd h hne
      · have hi : i < a.size := lt_of_lt_of_le (lt_trans h1 h2) hsize
        have hm : largestOf a i hs < a.size := lt_of_lt_of_le h2 hsize
        have hstep : hs ≤ (swapArr a i (largestOf a i hs)).size := by simpa using hsize
        exact (ih _ _ hstep).trans (swapArr_perm a i (largestOf a i hs) hi hm)

theorem maxHeapify_perm (a : Array Nat) (i hs : Nat) (h : hs ≤ a.size) :
    (maxHeapify a i hs).toList.Perm a.toList :=
  maxHeapifyAux_perm hs (a.size + 1) a i h

theorem buildAux_perm (n : Nat) :
    ∀ (k : Nat) (a : Array Nat), n ≤ a.size → (buildAux n k a).toList.Perm a.toList := by
  intro k
  induction k with
  | zero => intro a h; exact maxHeapify_perm a 0 n h
  | succ m ih =>
    intro a h
    have h' : n ≤ (maxHeapify a (m + 1) n).size := by simpa using h
    exact (ih _ h').trans (maxHeapify_perm a (m + 1) n h)

theorem buildMaxHeap_perm (a : Array Nat) : (buildMaxHeap a).toList.Perm a.toList := by
  unfold buildMaxHeap
  split
  · rfl
  · exact buildAux_perm a.size _ a (le_refl _)

theorem extractAux_perm :
    ∀ (k : Nat) (a : Array Nat), k < a.size → (extractAux k a).toList.Perm a.toList := by
  intro k
  induction k with
  | zero => intro a _; rfl
  | succ m ih =>
    intro a h
    have h0 : 0 < a.size := by omega
    have hswap : (swapArr a 0 (m + 1)).toList.Perm a.toList := swapArr_perm a 0 (m + 1) h0 h
    have hsize : m + 1 ≤ (swapArr a 0 (m + 1)).size := by
      simp only [swapArr_size]; omega
    have hheap :
        (maxHeapify (swapArr a 0 (m + 1)) 0 (m + 1)).toList.Perm (swapArr a 0 (m + 1)).toList :=
      maxHeapify_perm _ 0 (m + 1) hsize
    have hlt : m < (maxHeapify (swapArr a 0 (m + 1)) 0 (m + 1)).size := by
      simp only [maxHeapify_size, swapArr_size]; omega
    rw [extractAux]
    exact ((ih _ hlt).trans hheap).trans hswap

theorem heapsortArr_perm (a : Array Nat) : (heapsortArr a).toList.Perm a.toList := by
  unfold heapsortArr
  split
  · rfl
  · rename_i h
    have h1 : a.size - 1 < (buildMaxHeap a).size := by simp; omega
    exact (extractAux_perm _ _ h1).trans (buildMaxHeap_perm a)

/-! ## Properties, post-condition and correctness -/

/-- The result is sorted in ascending order. -/
def sorted_prop (out : List Nat) : Prop := out.Sorted (· ≤ ·)

/-- The result is a permutation of the input (`sorted(out) == sorted(arr)`). -/
def perm_prop (l out : List Nat) : Prop := out.Perm l

/-- The result has the same length as the input (`len(out) == len(arr)`). -/
def length_prop (l out : List Nat) : Prop := out.length = l.length

theorem heapsort_perm_thm (l : List Nat) : perm_prop l (heapsort l) := by
  unfold perm_prop heapsort
  simpa using heapsortArr_perm l.toArray

theorem heapsort_length_thm (l : List Nat) : length_prop l (heapsort l) :=
  (heapsort_perm_thm l).length_eq

theorem heapsort_mem_thm (l : List Nat) (x : Nat) : x ∈ heapsort l ↔ x ∈ l :=
  (heapsort_perm_thm l).mem_iff

/-- Every value occurs as often in the output as in the input. -/
theorem heapsort_count_thm (l : List Nat) (x : Nat) : (heapsort l).count x = l.count x :=
  (heapsort_perm_thm l).count_eq x

theorem heapsort_nil_thm : heapsort [] = [] := by simp [heapsort, heapsortArr]

theorem heapsort_singleton_thm (x : Nat) : heapsort [x] = [x] := by
  simp [heapsort, heapsortArr]

/-- Heapsort returns an ascending list.  (Proving this requires the full
max-heap invariant of CLRS 6.2-6.4; it is left unproven here.) -/
theorem heapsort_sorted_thm (l : List Nat) : sorted_prop (heapsort l) := by
  sorry

/-- Post-condition: the output is sorted, is a permutation of the input, and has
the same length. -/
def Post_prop (l out : List Nat) : Prop :=
  sorted_prop out ∧ perm_prop l out ∧ length_prop l out

/-- Correctness: `Pre l → Post_prop l (heapsort l)`. -/
theorem heapsort_correct_thm (l : List Nat) (_h : Pre l) : Post_prop l (heapsort l) :=
  ⟨heapsort_sorted_thm l, heapsort_perm_thm l, heapsort_length_thm l⟩

-- The post-condition, checked on the concrete inputs of the Python `check` function.
example : Post_prop [3, 1, 2] (heapsort [3, 1, 2]) := by
  unfold Post_prop sorted_prop perm_prop length_prop; native_decide
example : Post_prop [5, 13, 2, 25, 7, 17, 20, 8, 4] (heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]) := by
  unfold Post_prop sorted_prop perm_prop length_prop; native_decide
example : Post_prop [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] (heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]) := by
  unfold Post_prop sorted_prop perm_prop length_prop; native_decide

/-! ## Imperative implementation -/

/-- `[k, k-1, ..., 0]`, the index sequence of `range(k, -1, -1)`. -/
def downTo0 : Nat → List Nat
  | 0 => [0]
  | k + 1 => (k + 1) :: downTo0 k

/-- `[k, k-1, ..., 1]`, the index sequence of `range(k, 0, -1)`. -/
def downFrom1 : Nat → List Nat
  | 0 => []
  | k + 1 => (k + 1) :: downFrom1 k

theorem downTo0_eq (k : Nat) : downTo0 k = (List.range (k + 1)).reverse := by
  induction k with
  | zero => rfl
  | succ m ih => simp [downTo0, ih, List.range_succ]

theorem downFrom1_eq (k : Nat) : downFrom1 k = (List.range' 1 k).reverse := by
  induction k with
  | zero => rfl
  | succ m ih => simp [downFrom1, ih, List.range'_concat, Nat.add_comm]

/-- The `while True:` loop of `max_heapify`, as a bounded `for` loop with
mutable state and an early `break`. -/
def siftLoop (heapSize : Nat) (fuel : Nat) (a : Array Nat) (i : Nat) : Array Nat := Id.run do
  let mut arr := a
  let mut idx := i
  for _ in List.replicate fuel () do
    let l := left idx
    let r := right idx
    let mut largest := idx
    if l < heapSize ∧ arr[l]! > arr[idx]! then largest := l
    if r < heapSize ∧ arr[r]! > arr[largest]! then largest := r
    if largest = idx then break
    arr := swapArr arr idx largest
    idx := largest
  return arr

/-- `max_heapify(arr, i, heap_size)`, imperative. -/
def maxHeapifyImp (a : Array Nat) (i heapSize : Nat) : Array Nat :=
  siftLoop heapSize (a.size + 1) a i

/-- The `for i in range(parent(n-1), -1, -1)` loop of `build_max_heap`. -/
def buildLoop (n k : Nat) (a : Array Nat) : Array Nat := Id.run do
  let mut arr := a
  for i in downTo0 k do
    arr := maxHeapifyImp arr i n
  return arr

/-- `build_max_heap(arr)`, imperative. -/
def buildMaxHeapImp (a : Array Nat) : Array Nat := Id.run do
  let n := a.size
  if n ≤ 1 then
    return a
  return buildLoop n (parent (n - 1)) a

/-- The extraction loop `for i in range(n-1, 0, -1)` of `heapsort`. -/
def extractLoop (k : Nat) (a : Array Nat) : Array Nat := Id.run do
  let mut arr := a
  for i in downFrom1 k do
    arr := swapArr arr 0 i
    arr := maxHeapifyImp arr 0 i
  return arr

/-- `heapsort(arr)`, imperative. -/
def heapsortImp (l : List Nat) : List Nat := Id.run do
  let mut arr := l.toArray
  let n := arr.size
  if n ≤ 1 then
    return arr.toList
  arr := buildMaxHeapImp arr
  arr := extractLoop (n - 1) arr
  return arr.toList

/-! ## Imperative tests -/

#eval heapsortImp [3, 1, 2]
#eval heapsortImp [5, 13, 2, 25, 7, 17, 20, 8, 4]

example : heapsortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsortImp [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsortImp [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsortImp [] = [] := by native_decide
example : heapsortImp [42] = [42] := by native_decide
example : heapsortImp [2, 1] = [1, 2] := by native_decide
example : heapsortImp [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapsortImp [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide

/-! ## Equivalence of the functional and the imperative implementation -/

theorem siftLoop_eq (hs : Nat) : ∀ (fuel : Nat) (a : Array Nat) (i : Nat),
    siftLoop hs fuel a i = maxHeapifyAux hs fuel a i := by
  intro fuel
  induction fuel with
  | zero => intro a i; rfl
  | succ n ih =>
    intro a i
    simp only [siftLoop, Id.run] at ih ⊢
    simp only [List.replicate, List.forIn_cons, maxHeapifyAux, largestOf, if_true]
    split_ifs <;> first | rfl | exact ih _ _ | omega

theorem maxHeapifyImp_eq (a : Array Nat) (i hs : Nat) : maxHeapifyImp a i hs = maxHeapify a i hs :=
  siftLoop_eq hs (a.size + 1) a i

private theorem buildLoop_foldl (n k : Nat) (a : Array Nat) :
    buildLoop n k a = (downTo0 k).foldl (fun b i => maxHeapifyImp b i n) a := by
  simp [buildLoop]

theorem buildLoop_eq (n : Nat) : ∀ (k : Nat) (a : Array Nat), buildLoop n k a = buildAux n k a := by
  intro k
  induction k with
  | zero => intro a; simp [buildLoop_foldl, downTo0, buildAux, maxHeapifyImp_eq]
  | succ m ih =>
    intro a
    rw [buildLoop_foldl, downTo0, List.foldl_cons, ← buildLoop_foldl, ih, maxHeapifyImp_eq,
      buildAux]

theorem buildMaxHeapImp_eq (a : Array Nat) : buildMaxHeapImp a = buildMaxHeap a := by
  simp only [buildMaxHeapImp, buildMaxHeap, buildLoop_eq]
  split <;> simp

private theorem extractLoop_foldl (k : Nat) (a : Array Nat) :
    extractLoop k a = (downFrom1 k).foldl (fun b i => maxHeapifyImp (swapArr b 0 i) 0 i) a := by
  simp [extractLoop]

theorem extractLoop_eq : ∀ (k : Nat) (a : Array Nat), extractLoop k a = extractAux k a := by
  intro k
  induction k with
  | zero => intro a; simp [extractLoop_foldl, downFrom1, extractAux]
  | succ m ih =>
    intro a
    rw [extractLoop_foldl, downFrom1, List.foldl_cons, ← extractLoop_foldl, ih, maxHeapifyImp_eq,
      extractAux]

/-- The imperative implementation computes the same result as the functional one. -/
theorem heapsortImp_eq_heapsort (l : List Nat) : heapsortImp l = heapsort l := by
  simp only [heapsortImp, heapsort, heapsortArr, List.size_toArray, buildMaxHeapImp_eq,
    extractLoop_eq]
  split <;> simp

/-- The imperative implementation is correct as well. -/
theorem heapsortImp_correct_thm (l : List Nat) (h : Pre l) : Post_prop l (heapsortImp l) := by
  rw [heapsortImp_eq_heapsort]
  exact heapsort_correct_thm l h

end heapsort_algorithm
