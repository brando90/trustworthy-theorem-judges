import Mathlib
namespace Agent

/-!
# CLRS 6-1, 6-2 and 6-3: heaps and Young tableaux

A functional translation of the Python list algorithms. `Nat` implements the
source's checked natural-number type (in particular, booleans and negative
integers are not inputs). Lists are copied persistently. Indices are zero based.
`getD` and `set` totalize array access; the specifications use precisely the
bounds needed by the source, rather than interpreting an out-of-bounds read as
a successful Python execution. Positive arity and rectangular, nonempty tableau
preconditions are made explicit below. The sentinel is the source's finite
constant, not mathematical infinity; no assumption that keys are smaller than
it is made by the implementation.

The walks have structural fuel bounds: heap descent uses `heap_size + 1`,
heap ascent uses `i + 1`, and tableau walks use `rows + cols + 1` or
`row + col + 1`. On valid inputs a nonterminal step strictly advances in the
corresponding direction. Ties are resolved exactly as in the Python program.
-/
namespace heapsort_problems

def SENTINEL : Nat := 1000000

def my_swap (arr : List Nat) (i j : Nat) : List Nat :=
  if i < arr.length ∧ j < arr.length then
    (arr.set i (arr.getD j 0)).set j (arr.getD i 0)
  else arr

def parent (i : Nat) : Nat := if i = 0 then 0 else (i - 1) / 2
def left (i : Nat) : Nat := 2 * i + 1
def right (i : Nat) : Nat := 2 * i + 2

/-- The engine stops at `none`; it never resumes a stopped walk. -/
def walk {α : Type} (step : List Nat → α → Option (List Nat × α)) :
    Nat → List Nat → α → List Nat
  | 0, arr, _ => arr
  | fuel + 1, arr, p => match step arr p with
    | none => arr
    | some (arr', p') => walk step fuel arr' p'

def binaryLargest (arr : List Nat) (i heap_size : Nat) : Nat :=
  let l := left i
  let r := right i
  let largest := if l < heap_size ∧ arr.getD l 0 > arr.getD i 0 then l else i
  if r < heap_size ∧ arr.getD r 0 > arr.getD largest 0 then r else largest

def heapStep (heap_size : Nat) (arr : List Nat) (i : Nat) :
    Option (List Nat × Nat) :=
  let largest := binaryLargest arr i heap_size
  if largest = i then none else some (my_swap arr i largest, largest)

def max_heapify (arr : List Nat) (i heap_size : Nat) : List Nat :=
  if i ≥ heap_size ∨ i ≥ arr.length then arr
  else walk (heapStep heap_size) (heap_size + 1) arr i

/-- Calls heapify at n-1, ..., 0, holding the active size fixed. -/
def buildLoop (heapify : List Nat → Nat → List Nat) : Nat → List Nat → List Nat
  | 0, arr => arr
  | n + 1, arr => buildLoop heapify n (heapify arr n)

def build_max_heap (arr : List Nat) : List Nat :=
  buildLoop (fun a i => max_heapify a i arr.length) (arr.length / 2) arr

def upStep (par : Nat → Nat) (arr : List Nat) (i : Nat) : Option (List Nat × Nat) :=
  if i > 0 ∧ arr.getD (par i) 0 < arr.getD i 0 then
    some (my_swap arr i (par i), par i)
  else none

def sift_up (arr : List Nat) (i : Nat) : List Nat :=
  walk (upStep parent) (i + 1) arr i

def heap_increase_key (arr : List Nat) (i key : Nat) : List Nat :=
  if i ≥ arr.length then arr else sift_up (arr.set i key) i

def reserve (arr : List Nat) (heap_size : Nat) : List Nat :=
  if heap_size < arr.length then arr.set heap_size 0 else arr ++ [0]

def max_heap_insert (arr : List Nat) (key heap_size : Nat) : List Nat × Nat :=
  (heap_increase_key (reserve arr heap_size) heap_size key, heap_size + 1)

def insertLoop : List Nat → List Nat → Nat → List Nat
  | [], arr, _ => arr
  | key :: keys, arr, size =>
      let result := max_heap_insert arr key size
      insertLoop keys result.1 result.2

def build_max_heap_prime (arr : List Nat) : List Nat :=
  if arr.isEmpty then [] else insertLoop (arr.drop 1) arr 1

def d_ary_parent (i d : Nat) : Nat := if i = 0 then 0 else (i - 1) / d
def d_ary_child (i j d : Nat) : Nat := d * i + j + 1

def d_ary_find_largest_child (arr : List Nat) (i heap_size d : Nat) : Nat :=
  (List.range d).foldl (fun largest j =>
    let child := d_ary_child i j d
    if child < heap_size ∧ arr.getD child 0 > arr.getD largest 0 then child else largest) i

def dHeapStep (heap_size d : Nat) (arr : List Nat) (i : Nat) :
    Option (List Nat × Nat) :=
  let largest := d_ary_find_largest_child arr i heap_size d
  if largest = i then none else some (my_swap arr i largest, largest)

def d_ary_max_heapify (arr : List Nat) (i heap_size d : Nat) : List Nat :=
  if i ≥ heap_size ∨ i ≥ arr.length then arr
  else walk (dHeapStep heap_size d) (heap_size + 1) arr i

def d_ary_extract_max (arr : List Nat) (heap_size d : Nat) : Nat × List Nat × Nat :=
  if heap_size = 0 then (0, arr, 0)
  else (arr.getD 0 0,
    d_ary_max_heapify (arr.set 0 (arr.getD (heap_size - 1) 0)) 0 (heap_size - 1) d,
    heap_size - 1)

def d_ary_sift_up (arr : List Nat) (i d : Nat) : List Nat :=
  walk (upStep (fun k => d_ary_parent k d)) (i + 1) arr i

def d_ary_increase_key (arr : List Nat) (i key d : Nat) : List Nat :=
  if i ≥ arr.length then arr else d_ary_sift_up (arr.set i key) i d

def d_ary_insert (arr : List Nat) (key heap_size d : Nat) : List Nat × Nat :=
  (d_ary_increase_key (reserve arr heap_size) heap_size key d, heap_size + 1)

def build_d_ary_max_heap (arr : List Nat) (d : Nat) : List Nat :=
  buildLoop (fun a i => d_ary_max_heapify a i arr.length d) (arr.length / d) arr

def young_get (tab : List Nat) (cols row col : Nat) : Nat := tab.getD (row * cols + col) 0

def young_set (tab : List Nat) (cols row col value : Nat) : List Nat :=
  tab.set (row * cols + col) value

def youngDownStep (rows cols : Nat) (tab : List Nat) (p : Nat × Nat) :
    Option (List Nat × (Nat × Nat)) :=
  let (row, col) := p
  let curr := young_get tab cols row col
  let below := if row + 1 < rows then young_get tab cols (row + 1) col else curr + 1
  let rightVal := if col + 1 < cols then young_get tab cols row (col + 1) else curr + 1
  if below < curr ∧ below ≤ rightVal then
    some (young_set (young_set tab cols row col below) cols (row + 1) col curr,
      (row + 1, col))
  else if rightVal < curr then
    some (young_set (young_set tab cols row col rightVal) cols row (col + 1) curr,
      (row, col + 1))
  else none

def youngify_down (tab : List Nat) (rows cols row col : Nat) : List Nat :=
  walk (youngDownStep rows cols) (rows + cols + 1) tab (row, col)

def young_extract_min (tab : List Nat) (rows cols : Nat) : Nat × List Nat :=
  (young_get tab cols 0 0,
    youngify_down (young_set tab cols 0 0 SENTINEL) rows cols 0 0)

def youngUpStep (cols : Nat) (tab : List Nat) (p : Nat × Nat) :
    Option (List Nat × (Nat × Nat)) :=
  let (row, col) := p
  let curr := young_get tab cols row col
  let above := if row > 0 then young_get tab cols (row - 1) col else 0
  let leftVal := if col > 0 then young_get tab cols row (col - 1) else 0
  if row > 0 ∧ above > curr ∧ above ≥ leftVal then
    some (young_set (young_set tab cols row col above) cols (row - 1) col curr,
      (row - 1, col))
  else if col > 0 ∧ leftVal > curr then
    some (young_set (young_set tab cols row col leftVal) cols row (col - 1) curr,
      (row, col - 1))
  else none

def young_bubble_up (tab : List Nat) (cols row col : Nat) : List Nat :=
  walk (youngUpStep cols) (row + col + 1) tab (row, col)

def young_insert (tab : List Nat) (key rows cols : Nat) : List Nat :=
  young_bubble_up (young_set tab cols (rows - 1) (cols - 1) key)
    cols (rows - 1) (cols - 1)

def searchLoop (tab : List Nat) (key rows cols : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, row, col =>
      if row < rows ∧ col < cols then
        let value := young_get tab cols row col
        if value = key then true
        else if value > key then
          if col = 0 then false else searchLoop tab key rows cols fuel row (col - 1)
        else searchLoop tab key rows cols fuel (row + 1) col
      else false

def young_search (tab : List Nat) (key rows cols : Nat) : Bool :=
  if rows = 0 ∨ cols = 0 then false
  else searchLoop tab key rows cols (rows + cols + 1) 0 (cols - 1)

def is_max_heap (arr : List Nat) (heap_size : Nat) : Bool :=
  (List.range (min heap_size arr.length)).all fun i =>
    (!(left i < heap_size) || arr.getD (left i) 0 ≤ arr.getD i 0) &&
    (!(right i < heap_size) || arr.getD (right i) 0 ≤ arr.getD i 0)

def is_d_ary_max_heap (arr : List Nat) (heap_size d : Nat) : Bool :=
  (List.range (min heap_size arr.length)).all fun i =>
    (List.range d).all fun j =>
      !(d_ary_child i j d < heap_size) ||
        arr.getD (d_ary_child i j d) 0 ≤ arr.getD i 0

def is_young_tableau (tab : List Nat) (rows cols : Nat) : Bool :=
  if tab.length < rows * cols then false else
    (List.range rows).all fun row => (List.range cols).all fun col =>
      (!(col + 1 < cols) || young_get tab cols row col ≤ young_get tab cols row (col + 1)) &&
      (!(row + 1 < rows) || young_get tab cols row col ≤ young_get tab cols (row + 1) col)


/-! ### Checked dynamic boundary

`PythonValue.other` represents all non-integer/non-Boolean/non-list Python
objects; they are indistinguishable to these validators. `boolean` is kept
separate from `integer`, just as `_is_nat` explicitly excludes Python bools.
The typed numerical APIs above correspond to successful validation. The
wrappers below expose the explicit ValueError cases as `Except.error`.
-/
deriving instance DecidableEq for Except

inductive PythonValue where
  | integer : Int → PythonValue
  | boolean : Bool → PythonValue
  | list : List PythonValue → PythonValue
  | other : PythonValue
  deriving Repr

def _is_nat : PythonValue → Bool
  | .integer n => n ≥ 0
  | _ => false

def _check_nat (value : PythonValue) (name : String := "value") : Except String Nat :=
  match value with
  | .integer n => if n ≥ 0 then .ok n.toNat else .error (name ++ " must be a natural number")
  | _ => .error (name ++ " must be a natural number")

def _check_nat_list (value : PythonValue) (name : String := "arr") : Except String (List Nat) :=
  match value with
  | .list xs => if xs.all _is_nat then
      .ok (xs.map fun v => match v with | .integer n => n.toNat | _ => 0)
    else .error (name ++ " must be List[Nat]")
  | _ => .error (name ++ " must be List[Nat]")

def checked_build_max_heap (value : PythonValue) : Except String (List Nat) := do
  let arr ← _check_nat_list value
  return build_max_heap arr

def checked_d_ary_parent (i d : Nat) : Except String Nat :=
  if d = 0 then .error "d must be positive" else .ok (d_ary_parent i d)

def checked_d_ary_child (i j d : Nat) : Except String Nat :=
  if d = 0 then .error "d must be positive" else .ok (d_ary_child i j d)

def checked_build_d_ary_max_heap (arr : List Nat) (d : Nat) : Except String (List Nat) :=
  if d = 0 then .error "d must be positive" else .ok (build_d_ary_max_heap arr d)

def checked_max_heap_insert (arr : List Nat) (key n : Nat) : Except String (List Nat × Nat) :=
  if n > arr.length then .error "heap_size must be <= len(arr)" else .ok (max_heap_insert arr key n)

def checked_d_ary_insert (arr : List Nat) (key n d : Nat) : Except String (List Nat × Nat) :=
  if n > arr.length then .error "heap_size must be <= len(arr)"
  else if d = 0 then .error "d must be positive" else .ok (d_ary_insert arr key n d)

def checked_young_extract_min (tab : List Nat) (rows cols : Nat) : Except String (Nat × List Nat) :=
  if rows = 0 ∨ cols = 0 ∨ tab.length ≠ rows * cols then
    .error "Require non-empty rows/cols and len(tab) == rows * cols"
  else .ok (young_extract_min tab rows cols)

def checked_young_insert (tab : List Nat) (key rows cols : Nat) : Except String (List Nat) :=
  if rows = 0 ∨ cols = 0 ∨ tab.length ≠ rows * cols then
    .error "Require non-empty rows/cols and len(tab) == rows * cols"
  else .ok (young_insert tab key rows cols)

/-! ## The source's fixed regression checks -/
def check : Bool := Id.run do
  let arr := [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]
  let ternary := build_d_ary_max_heap arr 3
  let inserted := d_ary_insert (build_d_ary_max_heap [1, 2, 3] 3) 100 3 3
  let first := young_extract_min [1, 3, 2, 4] 2 2
  let second := young_extract_min first.2 2 2
  return [
    is_max_heap (build_max_heap arr) 10,
    is_max_heap (build_max_heap_prime arr) 10,
    build_max_heap [1, 2, 3, 4, 5, 6] != build_max_heap_prime [1, 2, 3, 4, 5, 6],
    d_ary_parent 1 3 == 0,
    d_ary_child 0 0 3 == 1, d_ary_child 0 1 3 == 2, d_ary_child 0 2 3 == 3,
    is_d_ary_max_heap ternary 10 3, (d_ary_extract_max ternary 10 3).1 == 16,
    is_young_tableau [1, 3, 5, 2, 4, 6] 2 3,
    young_search [1, 3, 5, 2, 4, 6] 4 2 3,
    !young_search [1, 3, 5, 2, 4, 6] 7 2 3,
    build_max_heap [] == [], is_max_heap (build_max_heap [42]) 1,
    is_max_heap (build_max_heap_prime [42]) 1, build_max_heap_prime [] == [],
    is_d_ary_max_heap (build_d_ary_max_heap [3, 1, 2] 1) 3 1,
    (d_ary_extract_max [5] 1 3).1 == 5, (d_ary_extract_max [] 0 3).1 == 0,
    first.1 == 1, is_young_tableau first.2 2 2,
    young_search [5] 5 1 1, !young_search [5] 3 1 1,
    (young_extract_min [1, 3, 5, 2, 4, 6] 2 3).1 == 1,
    is_young_tableau (young_extract_min [1, 3, 5, 2, 4, 6] 2 3).2 2 3,
    (d_ary_extract_max inserted.1 inserted.2 3).1 == 100,
    first.1 ≤ second.1, !is_max_heap [1, 10, 3] 3,
    !young_search [1, 2, 4, 3, 5, 7, 6, 8, 9] 10 3 3,
    is_max_heap (build_max_heap [5, 3, 8, 1]) 4,
    is_max_heap (build_max_heap [10, 20, 30, 40, 50]) 5,
    is_max_heap (build_max_heap_prime [5, 3, 8, 1]) 4,
    is_max_heap (build_max_heap_prime [10, 20, 30, 40, 50]) 5,
    d_ary_parent (d_ary_child 2 1 4) 4 == 2,
    d_ary_parent (d_ary_child 0 0 3) 3 == 0,
    is_young_tableau (young_insert [SENTINEL, SENTINEL, SENTINEL, SENTINEL] 5 2 2) 2 2,
    young_search [1, 2, 4, 3, 5, 7, 6, 8, 9] 5 3 3,
    young_search [1, 2, 4, 3, 5, 7, 6, 8, 9] 1 3 3,
    young_search [1, 2, 4, 3, 5, 7, 6, 8, 9] 9 3 3
  ].all id

example : check = true := by native_decide
example : checked_build_max_heap (.list [.integer 1, .integer (-1)]) =
    .error "arr must be List[Nat]" := by native_decide
example : _check_nat (.boolean true) = .error "value must be a natural number" := by native_decide
example : _check_nat_list .other = .error "arr must be List[Nat]" := by native_decide
example : checked_d_ary_parent 3 0 = .error "d must be positive" := by native_decide
example : checked_max_heap_insert [1] 2 2 = .error "heap_size must be <= len(arr)" := by native_decide
example : checked_young_extract_min [] 0 2 =
    .error "Require non-empty rows/cols and len(tab) == rows * cols" := by native_decide
example : my_swap [3, 4, 5] 0 2 = [5, 4, 3] := by native_decide
example : my_swap [3, 4, 5] 0 3 = [3, 4, 5] := by native_decide
-- The source really overwrites, even when the new key is smaller.
example : heap_increase_key [10, 8, 9] 0 1 = [1, 8, 9] := by native_decide
-- The finite sentinel is not an upper bound on the input type.
example : (young_extract_min [1000001] 1 1).2 = [SENTINEL] := by native_decide
#eval check
#eval build_max_heap [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]
#eval build_max_heap_prime [1, 2, 3, 4, 5, 6]
#eval young_insert [SENTINEL, SENTINEL, SENTINEL, SENTINEL] 5 2 2

/-! ## Admissibility

Each operation only uses the relevant component of `Pre`. The primitive
`my_swap` permits all indices; increase-key explicitly permits out-of-bounds
indices (a no-op). Sift-up requires an in-bounds starting index, heapify requires
an active size at most the length, and tableau cell operations require in-bounds
coordinates. These predicates encode successful Python inputs, not heap or
sortedness assumptions. Invariants, when needed, are separate hypotheses.
-/
def Pre (arr : List Nat) (heap_size d : Nat) (tab : List Nat) (rows cols : Nat) : Prop :=
  heap_size ≤ arr.length ∧ 0 < d ∧ 0 < rows ∧ 0 < cols ∧ tab.length = rows * cols

def HeapPre (arr : List Nat) (heap_size d : Nat) : Prop :=
  heap_size ≤ arr.length ∧ 0 < d

def TableauPre (tab : List Nat) (rows cols : Nat) : Prop :=
  0 < rows ∧ 0 < cols ∧ tab.length = rows * cols

/-! ## Kernel proofs and properties -/

theorem validation_thm (a : List Nat) :
    _check_nat_list (.list (a.map (fun n => PythonValue.integer (Int.ofNat n)))) = .ok a := by
  simp [_check_nat_list, _is_nat, List.all_map, List.map_map, Function.comp_def]

theorem d_ary_builder_counterexample :
    build_d_ary_max_heap [0, 1] 3 = [0, 1] ∧
    is_d_ary_max_heap (build_d_ary_max_heap [0, 1] 3) 2 3 = false := by
  decide


theorem swap_perm (arr : List Nat) (i j : Nat) : (my_swap arr i j).Perm arr := by
  unfold my_swap
  split
  next h => simpa [List.getD_eq_getElem, h.1, h.2] using List.set_set_perm h.1 h.2
  next => exact List.Perm.refl _

@[simp] theorem swap_length (arr : List Nat) (i j : Nat) :
    (my_swap arr i j).length = arr.length := (swap_perm arr i j).length_eq

theorem walk_perm {α : Type} (step : List Nat → α → Option (List Nat × α))
    (hs : ∀ a p b q, step a p = some (b, q) → b.Perm a)
    (fuel : Nat) (arr : List Nat) (p : α) : (walk step fuel arr p).Perm arr := by
  induction fuel generalizing arr p with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    simp only [walk]
    cases h : step arr p with
    | none => exact List.Perm.refl _
    | some b => exact (ih b.1 b.2).trans (hs arr p b.1 b.2 h)

theorem walk_length {α : Type} (step : List Nat → α → Option (List Nat × α))
    (hs : ∀ a p b q, step a p = some (b, q) → b.length = a.length)
    (fuel : Nat) (arr : List Nat) (p : α) : (walk step fuel arr p).length = arr.length := by
  induction fuel generalizing arr p with
  | zero => rfl
  | succ n ih =>
    simp only [walk]
    cases h : step arr p with
    | none => rfl
    | some b => exact (ih b.1 b.2).trans (hs arr p b.1 b.2 h)

theorem heapStep_perm (n : Nat) :
    ∀ a p b q, heapStep n a p = some (b, q) → b.Perm a := by
  intro a p b q h
  unfold heapStep at h
  dsimp only at h
  split at h
  · contradiction
  · cases Option.some.inj h
    exact swap_perm _ _ _

theorem dHeapStep_perm (n d : Nat) :
    ∀ a p b q, dHeapStep n d a p = some (b, q) → b.Perm a := by
  intro a p b q h
  unfold dHeapStep at h
  dsimp only at h
  split at h
  · contradiction
  · cases Option.some.inj h
    exact swap_perm _ _ _

theorem upStep_perm (par : Nat → Nat) :
    ∀ a p b q, upStep par a p = some (b, q) → b.Perm a := by
  intro a p b q h
  unfold upStep at h
  split at h
  · cases Option.some.inj h
    exact swap_perm _ _ _
  · contradiction

theorem heapify_perm (arr : List Nat) (i n : Nat) : (max_heapify arr i n).Perm arr := by
  unfold max_heapify
  split
  · exact List.Perm.refl _
  · exact walk_perm _ (heapStep_perm n) _ _ _

theorem d_heapify_perm (arr : List Nat) (i n d : Nat) :
    (d_ary_max_heapify arr i n d).Perm arr := by
  unfold d_ary_max_heapify
  split
  · exact List.Perm.refl _
  · exact walk_perm _ (dHeapStep_perm n d) _ _ _

theorem sift_perm (arr : List Nat) (i : Nat) : (sift_up arr i).Perm arr :=
  walk_perm _ (upStep_perm parent) _ _ _

theorem d_sift_perm (arr : List Nat) (i d : Nat) : (d_ary_sift_up arr i d).Perm arr :=
  walk_perm _ (upStep_perm _) _ _ _

theorem buildLoop_perm (f : List Nat → Nat → List Nat)
    (hf : ∀ a i, (f a i).Perm a) (n : Nat) (a : List Nat) : (buildLoop f n a).Perm a := by
  induction n generalizing a with
  | zero => exact List.Perm.refl _
  | succ n ih => exact (ih (f a n)).trans (hf a n)

def build_permutation_prop (arr : List Nat) (d : Nat) : Prop :=
  (build_max_heap arr).Perm arr ∧ (build_d_ary_max_heap arr d).Perm arr

theorem build_permutation_thm (arr : List Nat) (d : Nat) : build_permutation_prop arr d := by
  exact ⟨buildLoop_perm _ (fun a i => heapify_perm a i _) _ _,
    buildLoop_perm _ (fun a i => d_heapify_perm a i _ d) _ _⟩

@[simp] theorem increase_length (arr : List Nat) (i key : Nat) :
    (heap_increase_key arr i key).length = arr.length := by
  unfold heap_increase_key
  split
  · rfl
  · exact (sift_perm _ _).length_eq.trans (List.length_set ..)

@[simp] theorem d_increase_length (arr : List Nat) (i key d : Nat) :
    (d_ary_increase_key arr i key d).length = arr.length := by
  unfold d_ary_increase_key
  split
  · rfl
  · exact (d_sift_perm _ _ _).length_eq.trans (List.length_set ..)

@[simp] theorem reserve_length (arr : List Nat) (n : Nat) :
    (reserve arr n).length = if n < arr.length then arr.length else arr.length + 1 := by
  simp [reserve]; split <;> simp_all

def insertion_size_prop (arr : List Nat) (key n d : Nat) : Prop :=
  (max_heap_insert arr key n).2 = n + 1 ∧
  (d_ary_insert arr key n d).2 = n + 1 ∧
  (max_heap_insert arr key n).1.length = (if n < arr.length then arr.length else arr.length + 1) ∧
  (d_ary_insert arr key n d).1.length = (if n < arr.length then arr.length else arr.length + 1)

theorem insertion_size_thm (arr : List Nat) (key n d : Nat) :
    insertion_size_prop arr key n d := by
  simp [insertion_size_prop, max_heap_insert, d_ary_insert]

theorem insertLoop_length (keys arr : List Nat) (n : Nat)
    (h : n + keys.length ≤ arr.length) : (insertLoop keys arr n).length = arr.length := by
  induction keys generalizing arr n with
  | nil => rfl
  | cons k ks ih =>
    have hn : n < arr.length := by simp only [List.length_cons] at h; omega
    have hl : (max_heap_insert arr k n).1.length = arr.length := by
      simp [max_heap_insert, hn]
    exact (ih _ (n + 1) (by simp only [hl]; simp only [List.length_cons] at h; omega)).trans hl

def lengths_prop (arr : List Nat) (i n key d : Nat) (tab : List Nat) (rows cols : Nat) : Prop :=
  (max_heapify arr i n).length = arr.length ∧
  (d_ary_max_heapify arr i n d).length = arr.length ∧
  (build_max_heap arr).length = arr.length ∧
  (build_max_heap_prime arr).length = arr.length ∧
  (build_d_ary_max_heap arr d).length = arr.length ∧
  (heap_increase_key arr i key).length = arr.length ∧
  (d_ary_increase_key arr i key d).length = arr.length ∧
  (young_extract_min tab rows cols).2.length = tab.length ∧
  (young_insert tab key rows cols).length = tab.length

theorem youngDownStep_length (rows cols : Nat) :
    ∀ a p b q, youngDownStep rows cols a p = some (b, q) → b.length = a.length := by
  intro a ⟨r,c⟩ b q h
  unfold youngDownStep at h
  dsimp only at h
  repeat' split at h
  all_goals simp_all [young_set]
  all_goals rw [← h.1]; simp

theorem youngUpStep_length (cols : Nat) :
    ∀ a p b q, youngUpStep cols a p = some (b, q) → b.length = a.length := by
  intro a ⟨r,c⟩ b q h
  unfold youngUpStep at h
  dsimp only at h
  repeat' split at h
  all_goals simp_all [young_set]
  all_goals rw [← h.1]; simp

@[simp] theorem young_down_length (tab : List Nat) (rows cols row col : Nat) :
    (youngify_down tab rows cols row col).length = tab.length :=
  walk_length _ (youngDownStep_length rows cols) _ _ _

@[simp] theorem young_up_length (tab : List Nat) (cols row col : Nat) :
    (young_bubble_up tab cols row col).length = tab.length :=
  walk_length _ (youngUpStep_length cols) _ _ _

theorem lengths_thm (arr : List Nat) (i n key d : Nat) (tab : List Nat) (rows cols : Nat) :
    lengths_prop arr i n key d tab rows cols := by
  have hp : (build_max_heap_prime arr).length = arr.length := by
    unfold build_max_heap_prime
    split
    next h => simpa using (List.isEmpty_iff.mp h).symm ▸ (rfl : ([] : List Nat).length = [].length)
    next h =>
      apply insertLoop_length
      have ha : 0 < arr.length := List.length_pos_iff.mpr (by simpa using h)
      simp only [List.length_drop]; omega
  exact ⟨(heapify_perm ..).length_eq, (d_heapify_perm ..).length_eq,
    (build_permutation_thm arr d).1.length_eq, hp,
    (build_permutation_thm arr d).2.length_eq, increase_length .., d_increase_length ..,
    by simp [young_extract_min, young_set], by simp [young_insert, young_set]⟩

def parent_child_prop (i j d : Nat) : Prop :=
  (0 < d → j < d → d_ary_parent (d_ary_child i j d) d = i) ∧
  parent (left i) = i ∧ parent (right i) = i

theorem d_parent_child (i j d : Nat) (hd : 0 < d) (hj : j < d) :
    d_ary_parent (d_ary_child i j d) d = i := by
  simp [d_ary_parent, d_ary_child, Nat.mul_add_div hd, Nat.div_eq_of_lt hj, Nat.ne_of_gt hd]

theorem parent_child_thm (i j d : Nat) : parent_child_prop i j d := by
  refine ⟨d_parent_child i j d, ?_, ?_⟩
  · simpa [d_ary_parent, d_ary_child, parent, left] using d_parent_child i 0 2 (by omega) (by omega)
  · simpa [d_ary_parent, d_ary_child, parent, right, Nat.add_assoc] using
      d_parent_child i 1 2 (by omega) (by omega)

/-- Soundness requires only a rectangular backing list, not sortedness. -/
def search_sound_prop (tab : List Nat) (key rows cols : Nat) : Prop :=
  young_search tab key rows cols = true →
    ∃ r < rows, ∃ c < cols, young_get tab cols r c = key

theorem searchLoop_sound (tab : List Nat) (key rows cols fuel row col : Nat)
    (h : searchLoop tab key rows cols fuel row col = true) :
    ∃ r < rows, ∃ c < cols, young_get tab cols r c = key := by
  induction fuel generalizing row col with
  | zero => simp [searchLoop] at h
  | succ n ih =>
    simp only [searchLoop] at h
    split at h
    next hb =>
      split at h
      next he => exact ⟨row, hb.1, col, hb.2, he⟩
      next =>
        split at h
        · split at h
          · contradiction
          · exact ih _ _ h
        · exact ih _ _ h
    next => contradiction

theorem search_sound_thm (tab : List Nat) (key rows cols : Nat) :
    search_sound_prop tab key rows cols := by
  intro h
  unfold young_search at h
  split at h
  · contradiction
  · exact searchLoop_sound _ _ _ _ _ _ _ h

/-- A readable, coordinate-level specification of the Boolean recognizer. -/
theorem tableau_edges (tab : List Nat) (rows cols : Nat)
    (h : is_young_tableau tab rows cols = true) :
    ∀ r < rows, ∀ c < cols,
      (c + 1 < cols → young_get tab cols r c ≤ young_get tab cols r (c + 1)) ∧
      (r + 1 < rows → young_get tab cols r c ≤ young_get tab cols (r + 1) c) := by
  unfold is_young_tableau at h
  split at h
  · contradiction
  · simpa [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, or_iff_not_imp_left] using h

theorem tableau_row_mono (tab : List Nat) (rows cols : Nat)
    (h : is_young_tableau tab rows cols = true)
    (r c c' : Nat) (hr : r < rows) (hc : c ≤ c') (hc' : c' < cols) :
    young_get tab cols r c ≤ young_get tab cols r c' := by
  induction c', hc using Nat.le_induction with
  | base => exact le_rfl
  | succ k hck ih =>
    exact (ih (by omega)).trans ((tableau_edges tab rows cols h r hr k (by omega)).1 hc')

theorem tableau_col_mono (tab : List Nat) (rows cols : Nat)
    (h : is_young_tableau tab rows cols = true)
    (r r' c : Nat) (hc : c < cols) (hr : r ≤ r') (hr' : r' < rows) :
    young_get tab cols r c ≤ young_get tab cols r' c := by
  induction r', hr using Nat.le_induction with
  | base => exact le_rfl
  | succ k hrk ih =>
    exact (ih (by omega)).trans ((tableau_edges tab rows cols h k (by omega) c hc).2 hr')

theorem searchLoop_complete (tab : List Nat) (key rows cols : Nat)
    (h : is_young_tableau tab rows cols = true)
    (fuel row col r c : Nat) (hr : r < rows) (hc : c < cols)
    (hrow : row ≤ r) (hcol : c ≤ col) (hcol' : col < cols)
    (he : young_get tab cols r c = key) (hf : rows - row + col + 1 < fuel) :
    searchLoop tab key rows cols fuel row col = true := by
  induction fuel generalizing row col with
  | zero => omega
  | succ n ih =>
    have hb : row < rows ∧ col < cols := ⟨by omega, hcol'⟩
    simp only [searchLoop, if_pos hb]
    split
    · rfl
    next hne =>
      split
      next hgt =>
        have hcc : c < col := by
          by_contra hn
          have eq : c = col := by omega
          have hm := tableau_col_mono tab rows cols h row r c hc hrow hr
          rw [he, eq] at hm
          omega
        have hn : col ≠ 0 := by omega
        simp only [if_neg hn]
        apply ih row (col - 1) hrow (by omega) (by omega)
        omega
      next hle =>
        have hrr : row < r := by
          by_contra hn
          have eq : row = r := by omega
          have hm := tableau_row_mono tab rows cols h r c col hr hcol hcol'
          rw [he, ← eq] at hm
          omega
        apply ih (row + 1) col (by omega) hcol hcol'
        omega

def search_complete_prop (tab : List Nat) (key rows cols : Nat) : Prop :=
  is_young_tableau tab rows cols = true →
    (young_search tab key rows cols = true ↔
      ∃ r < rows, ∃ c < cols, young_get tab cols r c = key)

theorem search_complete_thm (tab : List Nat) (key rows cols : Nat) :
    search_complete_prop tab key rows cols := by
  intro h
  constructor
  · exact search_sound_thm tab key rows cols
  · rintro ⟨r, hr, c, hc, he⟩
    unfold young_search
    have hn : ¬ (rows = 0 ∨ cols = 0) := by omega
    rw [if_neg hn]
    exact searchLoop_complete tab key rows cols h _ 0 (cols - 1) r c hr hc
      (by omega) (by omega) (by omega) he (by omega)

def young_minimum_prop (tab : List Nat) (rows cols : Nat) : Prop :=
  is_young_tableau tab rows cols = true →
    ∀ r < rows, ∀ c < cols,
      (young_extract_min tab rows cols).1 ≤ young_get tab cols r c

theorem young_minimum_thm (tab : List Nat) (rows cols : Nat) :
    young_minimum_prop tab rows cols := by
  intro h r hr c hc
  exact (tableau_col_mono tab rows cols h 0 r 0 (by omega) (by omega) hr).trans
    (tableau_row_mono tab rows cols h r 0 c hr (by omega) hc)

theorem d_heap_edges (arr : List Nat) (n d : Nat)
    (h : is_d_ary_max_heap arr n d = true) :
    ∀ i < min n arr.length, ∀ j < d,
      d_ary_child i j d < n → arr.getD (d_ary_child i j d) 0 ≤ arr.getD i 0 := by
  simpa [is_d_ary_max_heap, List.all_eq_true, Bool.or_eq_true, or_iff_not_imp_left] using h

theorem d_parent_lt (i d : Nat) (hi : 0 < i) (hd : 0 < d) : d_ary_parent i d < i := by
  simp only [d_ary_parent, if_neg (by omega : i ≠ 0)]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

theorem d_child_parent (i d : Nat) (hi : 0 < i) (hd : 0 < d) :
    d_ary_child (d_ary_parent i d) ((i - 1) % d) d = i := by
  simp only [d_ary_child, d_ary_parent, if_neg (by omega : i ≠ 0)]
  have h := Nat.mod_add_div (i - 1) d
  omega

theorem d_heap_root (arr : List Nat) (n d : Nat) (hn : n ≤ arr.length) (hd : 0 < d)
    (hh : is_d_ary_max_heap arr n d = true) (i : Nat) (hi : i < n) :
    arr.getD i 0 ≤ arr.getD 0 0 := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hiz : i = 0
    · subst i; exact le_rfl
    · have hp := d_parent_lt i d (by omega) hd
      have hc := d_child_parent i d (by omega) hd
      have edge := d_heap_edges arr n d hh (d_ary_parent i d) (by omega)
        ((i - 1) % d) (Nat.mod_lt _ hd) (by rw [hc]; exact hi)
      rw [hc] at edge
      exact edge.trans (ih _ hp (by omega))

def extract_maximum_prop (arr : List Nat) (n d : Nat) : Prop :=
  (d_ary_extract_max arr n d).2.1.length = arr.length ∧
  (d_ary_extract_max arr n d).2.2 = n - 1 ∧
  (n = 0 → (d_ary_extract_max arr n d).1 = 0) ∧
  (0 < n → (d_ary_extract_max arr n d).1 = arr.getD 0 0) ∧
  (is_d_ary_max_heap arr n d = true → ∀ i < n,
    arr.getD i 0 ≤ (d_ary_extract_max arr n d).1)

theorem extract_maximum_thm (arr : List Nat) (n d : Nat) (h : HeapPre arr n d) :
    extract_maximum_prop arr n d := by
  rcases h with ⟨hn, hd⟩
  by_cases hz : n = 0
  · subst n; simp [extract_maximum_prop, d_ary_extract_max]
  · have hl := (d_heapify_perm (arr.set 0 (arr.getD (n - 1) 0)) 0 (n - 1) d).length_eq
    simp only [List.length_set] at hl
    simp only [extract_maximum_prop, d_ary_extract_max, if_neg hz, hl, true_and]
    refine ⟨by omega, fun _ => True.intro, ?_⟩
    exact fun hh i hi => d_heap_root arr n d hn hd hh i hi

theorem parent_le (i : Nat) : parent i ≤ i := by
  unfold parent
  split
  · omega
  · exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

theorem swap_drop (a : List Nat) (i j k : Nat) (hi : i < k) (hj : j < k) :
    (my_swap a i j).drop k = a.drop k := by
  unfold my_swap
  split
  · rw [List.drop_set_of_lt hj, List.drop_set_of_lt hi]
  · rfl

theorem up_walk_drop (par : Nat → Nat) (hp : ∀ i, par i ≤ i)
    (fuel : Nat) (a : List Nat) (i k : Nat) (hi : i < k) :
    (walk (upStep par) fuel a i).drop k = a.drop k := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ n ih =>
    by_cases h : i > 0 ∧ a.getD (par i) 0 < a.getD i 0
    · simp only [walk, upStep, if_pos h]
      exact (ih _ _ (lt_of_le_of_lt (hp i) hi)).trans
        (swap_drop a i (par i) k hi (lt_of_le_of_lt (hp i) hi))
    · simp only [walk, upStep, if_neg h]

theorem sift_drop (a : List Nat) (i k : Nat) (hi : i < k) :
    (sift_up a i).drop k = a.drop k := up_walk_drop parent parent_le _ _ _ _ hi

theorem insert_same (a : List Nat) (n : Nat) (hn : n < a.length) :
    max_heap_insert a (a.getD n 0) n = (sift_up a n, n + 1) := by
  simp [max_heap_insert, reserve, hn, heap_increase_key, Nat.not_le.mpr hn,
    List.getD_eq_getElem a 0 hn]

theorem insertLoop_perm (keys a : List Nat) (n : Nat) (hs : a.drop n = keys) :
    (insertLoop keys a n).Perm a := by
  induction keys generalizing a n with
  | nil => exact List.Perm.refl _
  | cons k ks ih =>
    have hn : n < a.length := by
      have hl := congrArg List.length hs
      simp only [List.length_drop, List.length_cons] at hl
      omega
    rw [List.drop_eq_getElem_cons hn] at hs
    obtain ⟨hk, ht⟩ := List.cons.inj hs
    have he : k = a.getD n 0 := hk.symm.trans (List.getD_eq_getElem a 0 hn).symm
    simp only [insertLoop, he, insert_same a n hn]
    exact (ih (sift_up a n) (n + 1) (by rw [sift_drop a n (n+1) (by omega)]; exact ht)).trans
      (sift_perm a n)

def prime_permutation_prop (a : List Nat) : Prop := (build_max_heap_prime a).Perm a

theorem prime_permutation_thm (a : List Nat) : prime_permutation_prop a := by
  unfold prime_permutation_prop build_max_heap_prime
  split
  next h => simp only [List.isEmpty_iff] at h; subst a; exact List.Perm.refl _
  next => exact insertLoop_perm _ _ _ rfl

def increase_content_prop (a : List Nat) (i key d : Nat) : Prop :=
  (heap_increase_key a i key).Perm (a.set i key) ∧
  (d_ary_increase_key a i key d).Perm (a.set i key)

theorem increase_content_thm (a : List Nat) (i key d : Nat) : increase_content_prop a i key d := by
  unfold increase_content_prop heap_increase_key d_ary_increase_key
  by_cases h : i ≥ a.length
  · simp [h, List.set_eq_of_length_le h]
  · simp only [if_neg h]
    exact ⟨sift_perm _ _, d_sift_perm _ _ _⟩

/-! ### Fuel is a termination bound, not a semantic cutoff -/
theorem walk_stable {α : Type} (step : List Nat → α → Option (List Nat × α))
    (measure : α → Nat)
    (hm : ∀ a p b q, step a p = some (b,q) → measure q < measure p)
    (fuel extra : Nat) (a : List Nat) (p : α) (hf : measure p < fuel) :
    walk step fuel a p = walk step (fuel + extra) a p := by
  induction fuel generalizing a p with
  | zero => omega
  | succ n ih =>
    rw [show n + 1 + extra = (n + extra) + 1 by omega]
    simp only [walk]
    cases h : step a p with
    | none => rfl
    | some b =>
      apply ih b.1 b.2
      have hh := hm a p b.1 b.2 h
      omega

theorem binaryLargest_position (a : List Nat) (i n : Nat) :
    binaryLargest a i n = i ∨ (i < binaryLargest a i n ∧ binaryLargest a i n < n) := by
  unfold binaryLargest
  dsimp only
  repeat' split
  all_goals simp_all [left, right] <;> omega

theorem heapStep_decreases (n : Nat) (a : List Nat) (i : Nat) (b : List Nat) (j : Nat)
    (h : heapStep n a i = some (b,j)) : n - j < n - i := by
  unfold heapStep at h
  dsimp only at h
  split at h
  · contradiction
  next hn =>
    cases Option.some.inj h
    have hp := binaryLargest_position a i n
    rcases hp with hp | ⟨hi, hj⟩
    · contradiction
    · omega

theorem dLargest_position (a : List Nat) (i n d : Nat) (hd : 0 < d) :
    d_ary_find_largest_child a i n d = i ∨
      (i < d_ary_find_largest_child a i n d ∧ d_ary_find_largest_child a i n d < n) := by
  have hc (j : Nat) : i < d_ary_child i j d := by
    unfold d_ary_child
    have : i ≤ d * i := by nlinarith
    omega
  have inv (js : List Nat) (start : Nat) (hs : start = i ∨ (i < start ∧ start < n)) :
      js.foldl (fun largest j =>
        if d_ary_child i j d < n ∧ a.getD (d_ary_child i j d) 0 > a.getD largest 0
        then d_ary_child i j d else largest) start = i ∨
      (i < js.foldl (fun largest j =>
        if d_ary_child i j d < n ∧ a.getD (d_ary_child i j d) 0 > a.getD largest 0
        then d_ary_child i j d else largest) start ∧
      js.foldl (fun largest j =>
        if d_ary_child i j d < n ∧ a.getD (d_ary_child i j d) 0 > a.getD largest 0
        then d_ary_child i j d else largest) start < n) := by
    induction js generalizing start with
    | nil => exact hs
    | cons j js ih =>
      simp only [List.foldl_cons]
      apply ih
      split
      next h => exact Or.inr ⟨hc j, h.1⟩
      next => exact hs
  exact inv (List.range d) i (Or.inl rfl)

theorem dHeapStep_decreases (n d : Nat) (hd : 0 < d) (a : List Nat) (i : Nat)
    (b : List Nat) (j : Nat) (h : dHeapStep n d a i = some (b,j)) : n - j < n - i := by
  unfold dHeapStep at h
  dsimp only at h
  split at h
  · contradiction
  next hn =>
    cases Option.some.inj h
    have hp := dLargest_position a i n d hd
    rcases hp with hp | ⟨hi, hj⟩
    · contradiction
    · omega

theorem upStep_decreases (par : Nat → Nat) (hp : ∀ i, 0 < i → par i < i)
    (a : List Nat) (i : Nat) (b : List Nat) (j : Nat)
    (h : upStep par a i = some (b,j)) : j < i := by
  unfold upStep at h
  split at h
  next hh => cases Option.some.inj h; exact hp i hh.1
  next => contradiction

theorem youngDownStep_decreases (rows cols : Nat) (a : List Nat) (p : Nat × Nat)
    (b : List Nat) (q : Nat × Nat) (h : youngDownStep rows cols a p = some (b,q)) :
    rows - q.1 + (cols - q.2) < rows - p.1 + (cols - p.2) := by
  rcases p with ⟨r,c⟩
  unfold youngDownStep at h
  dsimp only at h
  repeat' split at h
  all_goals simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
  all_goals rw [← h.2]; dsimp only; omega

theorem youngUpStep_decreases (cols : Nat) (a : List Nat) (p : Nat × Nat)
    (b : List Nat) (q : Nat × Nat) (h : youngUpStep cols a p = some (b,q)) :
    q.1 + q.2 < p.1 + p.2 := by
  rcases p with ⟨r,c⟩
  unfold youngUpStep at h
  dsimp only at h
  repeat' split at h
  all_goals simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
  all_goals rw [← h.2]; dsimp only; omega

/-- Increasing any of the downward-walk budgets leaves the result unchanged. -/
theorem downward_fuel_sufficient (a t : List Nat) (i n d rows cols row col extra : Nat)
    (hd : 0 < d) :
    walk (heapStep n) (n+1) a i = walk (heapStep n) (n+1+extra) a i ∧
    walk (dHeapStep n d) (n+1) a i = walk (dHeapStep n d) (n+1+extra) a i ∧
    walk (youngDownStep rows cols) (rows+cols+1) t (row,col) =
      walk (youngDownStep rows cols) (rows+cols+1+extra) t (row,col) := by
  exact ⟨walk_stable _ (fun i => n-i) (heapStep_decreases n) _ _ _ _ (by dsimp; omega),
    walk_stable _ (fun i => n-i) (dHeapStep_decreases n d hd) _ _ _ _ (by dsimp; omega),
    walk_stable _ (fun p => rows-p.1+(cols-p.2)) (youngDownStep_decreases rows cols)
      _ _ _ _ (by dsimp; omega)⟩

theorem upward_fuel_sufficient (a t : List Nat) (i d cols row col extra : Nat)
    (hd : 0 < d) :
    walk (upStep parent) (i+1) a i = walk (upStep parent) (i+1+extra) a i ∧
    walk (upStep (fun i => d_ary_parent i d)) (i+1) a i =
      walk (upStep (fun i => d_ary_parent i d)) (i+1+extra) a i ∧
    walk (youngUpStep cols) (row+col+1) t (row,col) =
      walk (youngUpStep cols) (row+col+1+extra) t (row,col) := by
  have hp : ∀ i, 0 < i → parent i < i := by
    intro i hi
    exact d_parent_lt i 2 hi (by omega)
  exact ⟨walk_stable _ id (upStep_decreases parent hp) _ _ _ _ (by dsimp; omega),
    walk_stable _ id (upStep_decreases _ (fun i hi => d_parent_lt i d hi hd)) _ _ _ _ (by dsimp; omega),
    walk_stable _ (fun p => p.1+p.2) (youngUpStep_decreases cols) _ _ _ _ (by dsimp; omega)⟩

/-! ## Post-condition and exhaustive small-domain property tests -/

def Post_prop (arr : List Nat) (i n key d : Nat) (tab : List Nat) (rows cols : Nat) : Prop :=
  prime_permutation_prop arr ∧
  increase_content_prop arr i key d ∧
  build_permutation_prop arr d ∧
  insertion_size_prop arr key n d ∧
  lengths_prop arr i n key d tab rows cols ∧
  parent_child_prop i key d ∧
  search_sound_prop tab key rows cols ∧
  search_complete_prop tab key rows cols ∧
  young_minimum_prop tab rows cols ∧
  extract_maximum_prop arr n d

/-- All words of a specified length over `0, ..., alphabet-1`. -/
def words (alphabet : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (List.range alphabet).flatMap fun k => (words alphabet n).map (k :: ·)

def smallArrays : List (List Nat) := (List.range 5).flatMap (words 3)

def rectangleContains (tab : List Nat) (key rows cols : Nat) : Bool :=
  (List.range rows).any fun r => (List.range cols).any fun c => young_get tab cols r c == key

def lengthsTest (a : List Nat) (i n k d : Nat) (t : List Nat) (r c : Nat) : Bool :=
  @decide (lengths_prop a i n k d t r c) (by unfold lengths_prop; infer_instance)

def insertionTest (a : List Nat) (k n d : Nat) : Bool :=
  @decide (insertion_size_prop a k n d) (by unfold insertion_size_prop; infer_instance)

def parentTest (i j d : Nat) : Bool :=
  (!(0 < d && j < d) || d_ary_parent (d_ary_child i j d) d == i) &&
    parent (left i) == i && parent (right i) == i

def searchSoundTest (t : List Nat) (k r c : Nat) : Bool :=
  !young_search t k r c || rectangleContains t k r c

def searchCompleteTest (t : List Nat) (k r c : Nat) : Bool :=
  !is_young_tableau t r c || (young_search t k r c == rectangleContains t k r c)

def minimumTest (t : List Nat) (r c : Nat) : Bool :=
  !is_young_tableau t r c || (List.range r).all fun row => (List.range c).all fun col =>
    (young_extract_min t r c).1 ≤ young_get t c row col

def extractTest (a : List Nat) (n d : Nat) : Bool :=
  let res := d_ary_extract_max a n d
  (res.2.1.length == a.length) && (res.2.2 == n - 1) &&
  (if n = 0 then res.1 == 0 else res.1 == a.getD 0 0) &&
  (!is_d_ary_max_heap a n d || (List.range n).all fun i => a.getD i 0 ≤ res.1)

def permutationTest (a : List Nat) (d : Nat) : Bool :=
  decide ((build_max_heap a).Perm a ∧ (build_d_ary_max_heap a d).Perm a)

def postTest (a : List Nat) (i n k d : Nat) (t : List Nat) (r c : Nat) : Bool :=
  decide ((build_max_heap_prime a).Perm a) &&
  decide ((heap_increase_key a i k).Perm (a.set i k) ∧ (d_ary_increase_key a i k d).Perm (a.set i k)) &&
  permutationTest a d && insertionTest a k n d && lengthsTest a i n k d t r c &&
  parentTest i k d && searchSoundTest t k r c && searchCompleteTest t k r c &&
  minimumTest t r c && extractTest a n d

-- Fuel-bound regression checks on many arrays and tableau layouts.
example : smallArrays.all (fun a =>
    walk (heapStep a.length) (a.length+1) a 0 == walk (heapStep a.length) (a.length+6) a 0 &&
    walk (dHeapStep a.length 3) (a.length+1) a 0 == walk (dHeapStep a.length 3) (a.length+6) a 0)
    = true := by native_decide
example : (words 3 6).all (fun t =>
    walk (youngDownStep 2 3) 6 t (0,0) == walk (youngDownStep 2 3) 12 t (0,0) &&
    walk (youngUpStep 3) 4 t (1,2) == walk (youngUpStep 3) 10 t (1,2)) = true := by native_decide
-- PBT for prime_permutation_prop.
example : smallArrays.all (fun a => decide ((build_max_heap_prime a).Perm a)) = true := by native_decide
-- PBT for increase_content_prop, including indices beyond the backing list.
example : smallArrays.all (fun a => (List.range (a.length + 2)).all fun i =>
    (List.range 5).all fun k => decide ((heap_increase_key a i k).Perm (a.set i k) ∧
      (d_ary_increase_key a i k 3).Perm (a.set i k))) = true := by native_decide
-- PBT for build_permutation_prop: every ternary word of length at most four.
example : smallArrays.all (fun a => (List.range 5).all (permutationTest a)) = true := by native_decide
-- PBT for insertion_size_prop, including insertion into spare capacity.
example : smallArrays.all (fun a => (List.range (a.length + 1)).all fun n =>
    (List.range 4).all fun k => insertionTest a k n 3) = true := by native_decide
-- PBT for lengths_prop, including out-of-bounds increase-key (a no-op).
example : smallArrays.all (fun a => (List.range (a.length + 2)).all fun i =>
    lengthsTest a i a.length 5 3 a 1 a.length) = true := by native_decide
-- PBT for parent_child_prop, including d=1, d=0 and non-child j values.
example : (List.range 25).all (fun i => (List.range 9).all fun d =>
    (List.range 12).all fun j => parentTest i j d) = true := by native_decide
-- PBT for search_sound_prop: unsorted as well as sorted rectangles.
example : (words 3 6).all (fun t => (List.range 5).all fun k =>
    searchSoundTest t k 2 3) = true := by native_decide
-- PBT for search_complete_prop: sortedness is a decidable implication,
-- and the generator includes every 2-by-3 tableau over three values.
example : (words 3 6).all (fun t => (List.range 5).all fun k =>
    searchCompleteTest t k 2 3) = true := by native_decide
-- PBT for young_minimum_prop.
example : (words 3 6).all (fun t => minimumTest t 2 3) = true := by native_decide
-- PBT for extract_maximum_prop: all admissible active sizes and several arities.
example : smallArrays.all (fun a => (List.range (a.length + 1)).all fun n =>
    (List.range 4).all fun d => extractTest a n (d + 1)) = true := by native_decide
-- PBT for the entire Post_prop, on admissible nonempty rectangles and arrays.
example : (words 3 4).all (fun a => (List.range 5).all fun n =>
    (List.range 4).all fun k => postTest a k n k 3 a 2 2) = true := by native_decide

-- Additional PBTs exercise the binary heap/tableau invariants directly.
-- IMPORTANT: the source d-ary builder uses length / d, not the index of the
-- last parent plus one. It can skip a parent. We preserve this behavior rather
-- than "repair" the translation to make a false universal claim pass.
example : build_d_ary_max_heap [0, 1] 3 = [0, 1] := by native_decide
example : is_d_ary_max_heap (build_d_ary_max_heap [0, 1] 3) 2 3 = false := by native_decide
example : smallArrays.all (fun a =>
    is_max_heap (build_max_heap a) a.length &&
    is_max_heap (build_max_heap_prime a) a.length)
    = true := by native_decide
example : (words 3 6).all (fun t => !is_young_tableau t 2 3 ||
    is_young_tableau (young_extract_min t 2 3).2 2 3) = true := by native_decide
#eval postTest [16, 14, 10, 8, 7, 9, 3, 2, 4, 1] 3 10 4 2 [1, 3, 5, 2, 4, 6] 2 3

theorem correctness (arr : List Nat) (i n key d : Nat) (tab : List Nat) (rows cols : Nat) :
    Pre arr n d tab rows cols → Post_prop arr i n key d tab rows cols := by
  intro h
  exact ⟨prime_permutation_thm arr, increase_content_thm arr i key d,
    build_permutation_thm arr d, insertion_size_thm arr key n d,
    lengths_thm arr i n key d tab rows cols, parent_child_thm i key d,
    search_sound_thm tab key rows cols, search_complete_thm tab key rows cols,
    young_minimum_thm tab rows cols, extract_maximum_thm arr n d ⟨h.1, h.2.1⟩⟩

/-! ## Imperative implementation

A mutable fold is the loop primitive. Heap and tableau walks carry both their
list and current coordinate, with `none` denoting a stopped loop. Bottom-up
construction carries a decreasing loop counter. Insertion construction carries
the active size. Thus this code does not call a functional heapify, build,
increase-key, insertion, extraction or tableau search to obtain its result.
The read-only arithmetic and branch-selection functions are shared.
-/
namespace Imperative

def fold {α β : Type} (xs : List α) (init : β) (f : β → α → β) : β := Id.run do
  let mut state := init
  for x in xs do
    state := f state x
  return state

def my_swap (arr : List Nat) (i j : Nat) : List Nat := Id.run do
  let mut result := arr
  if i < result.length ∧ j < result.length then
    let x := result.getD i 0
    let y := result.getD j 0
    result := result.set i y
    result := result.set j x
  return result

def advance {α : Type} (step : List Nat → α → Option (List Nat × α))
    (s : List Nat × Option α) : List Nat × Option α :=
  match s.2 with
  | none => s
  | some p => match step s.1 p with
    | none => (s.1, none)
    | some (b, q) => (b, some q)

def walk {α : Type} (step : List Nat → α → Option (List Nat × α))
    (fuel : Nat) (arr : List Nat) (p : α) : List Nat :=
  (fold (List.replicate fuel ()) (arr, some p) (fun s _ => advance step s)).1

def max_heapify (arr : List Nat) (i n : Nat) : List Nat := Id.run do
  let mut result := arr
  if i < n ∧ i < result.length then
    result := walk (heapStep n) (n + 1) result i
  return result

def buildLoop (f : List Nat → Nat → List Nat) (n : Nat) (arr : List Nat) : List Nat :=
  (fold (List.replicate n ()) (arr, n) fun s _ =>
    let i := s.2 - 1
    (f s.1 i, i)).1

def build_max_heap (arr : List Nat) : List Nat :=
  buildLoop (fun a i => max_heapify a i arr.length) (arr.length / 2) arr

def sift_up (arr : List Nat) (i : Nat) : List Nat :=
  walk (upStep parent) (i + 1) arr i

def heap_increase_key (arr : List Nat) (i key : Nat) : List Nat := Id.run do
  let mut result := arr
  if i < result.length then
    result := result.set i key
    result := sift_up result i
  return result

def reserve (arr : List Nat) (n : Nat) : List Nat := Id.run do
  let mut result := arr
  if n < result.length then
    result := result.set n 0
  else
    result := result ++ [0]
  return result

def max_heap_insert (arr : List Nat) (key n : Nat) : List Nat × Nat := Id.run do
  let mut result := reserve arr n
  let mut size := n
  size := size + 1
  result := heap_increase_key result (size - 1) key
  return (result, size)

def insertLoop (keys arr : List Nat) (n : Nat) : List Nat :=
  (fold keys (arr, n) (fun s key => max_heap_insert s.1 key s.2)).1

def build_max_heap_prime (arr : List Nat) : List Nat := Id.run do
  if arr.isEmpty then return []
  let mut result := arr
  result := insertLoop (arr.drop 1) result 1
  return result

def d_ary_find_largest_child (arr : List Nat) (i n d : Nat) : Nat :=
  fold (List.range d) i fun largest j =>
    let child := d_ary_child i j d
    if child < n ∧ arr.getD child 0 > arr.getD largest 0 then child else largest

def d_ary_max_heapify (arr : List Nat) (i n d : Nat) : List Nat := Id.run do
  let mut result := arr
  if i < n ∧ i < result.length then
    result := walk (dHeapStep n d) (n + 1) result i
  return result

def d_ary_sift_up (arr : List Nat) (i d : Nat) : List Nat :=
  walk (upStep (fun k => d_ary_parent k d)) (i + 1) arr i

def d_ary_increase_key (arr : List Nat) (i key d : Nat) : List Nat := Id.run do
  let mut result := arr
  if i < result.length then
    result := result.set i key
    result := d_ary_sift_up result i d
  return result

def d_ary_insert (arr : List Nat) (key n d : Nat) : List Nat × Nat := Id.run do
  let mut result := reserve arr n
  let mut size := n
  size := size + 1
  result := d_ary_increase_key result (size - 1) key d
  return (result, size)

def d_ary_extract_max (arr : List Nat) (n d : Nat) : Nat × List Nat × Nat := Id.run do
  if n = 0 then return (0, arr, 0)
  let mut result := arr
  let value := result.getD 0 0
  result := result.set 0 (result.getD (n - 1) 0)
  let mut size := n
  size := size - 1
  result := d_ary_max_heapify result 0 size d
  return (value, result, size)

def build_d_ary_max_heap (arr : List Nat) (d : Nat) : List Nat :=
  buildLoop (fun a i => d_ary_max_heapify a i arr.length d) (arr.length / d) arr

def young_set (tab : List Nat) (cols row col value : Nat) : List Nat := Id.run do
  let mut result := tab
  result := result.set (row * cols + col) value
  return result

def youngify_down (tab : List Nat) (rows cols row col : Nat) : List Nat :=
  walk (youngDownStep rows cols) (rows + cols + 1) tab (row, col)

def young_bubble_up (tab : List Nat) (cols row col : Nat) : List Nat :=
  walk (youngUpStep cols) (row + col + 1) tab (row, col)

def young_extract_min (tab : List Nat) (rows cols : Nat) : Nat × List Nat := Id.run do
  let mut result := tab
  let value := young_get result cols 0 0
  result := young_set result cols 0 0 SENTINEL
  result := youngify_down result rows cols 0 0
  return (value, result)

def young_insert (tab : List Nat) (key rows cols : Nat) : List Nat := Id.run do
  let mut result := tab
  let row := rows - 1
  let col := cols - 1
  result := young_set result cols row col key
  result := young_bubble_up result cols row col
  return result

/-- Structural countdown version of the source's imperative while loop. -/
def searchLoop (tab : List Nat) (key rows cols : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | n + 1, row, col => Id.run do
    let mut row := row
    let mut col := col
    if row ≥ rows ∨ col ≥ cols then return false
    let value := young_get tab cols row col
    if value = key then return true
    if value > key then
      if col = 0 then return false
      col := col - 1
    else
      row := row + 1
    return searchLoop tab key rows cols n row col

def young_search (tab : List Nat) (key rows cols : Nat) : Bool := Id.run do
  if rows = 0 ∨ cols = 0 then return false
  return searchLoop tab key rows cols (rows + cols + 1) 0 (cols - 1)

def is_max_heap (arr : List Nat) (heap_size : Nat) : Bool :=
  fold (List.range (min heap_size arr.length)) true fun ok i => ok &&
    ((!(left i < heap_size) || arr.getD (left i) 0 ≤ arr.getD i 0) &&
    (!(right i < heap_size) || arr.getD (right i) 0 ≤ arr.getD i 0))

def is_d_ary_max_heap (arr : List Nat) (heap_size d : Nat) : Bool :=
  fold (List.range (min heap_size arr.length)) true fun ok i => ok &&
    fold (List.range d) true (fun ok j => ok &&
      (!(d_ary_child i j d < heap_size) || arr.getD (d_ary_child i j d) 0 ≤ arr.getD i 0))

def is_young_tableau (tab : List Nat) (rows cols : Nat) : Bool :=
  if tab.length < rows * cols then false else
    fold (List.range rows) true fun ok row => ok &&
      fold (List.range cols) true (fun ok col => ok &&
        ((!(col + 1 < cols) || young_get tab cols row col ≤ young_get tab cols row (col + 1)) &&
        (!(row + 1 < rows) || young_get tab cols row col ≤ young_get tab cols (row + 1) col)))

def check : Bool := Id.run do
  let arr := [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]
  let ternary := build_d_ary_max_heap arr 3
  let inserted := d_ary_insert (build_d_ary_max_heap [1, 2, 3] 3) 100 3 3
  let first := young_extract_min [1, 3, 2, 4] 2 2
  let second := young_extract_min first.2 2 2
  return [
    is_max_heap (build_max_heap arr) 10,
    is_max_heap (build_max_heap_prime arr) 10,
    build_max_heap [1, 2, 3, 4, 5, 6] != build_max_heap_prime [1, 2, 3, 4, 5, 6],
    d_ary_parent 1 3 == 0,
    d_ary_child 0 0 3 == 1, d_ary_child 0 1 3 == 2, d_ary_child 0 2 3 == 3,
    is_d_ary_max_heap ternary 10 3, (d_ary_extract_max ternary 10 3).1 == 16,
    is_young_tableau [1, 3, 5, 2, 4, 6] 2 3,
    young_search [1, 3, 5, 2, 4, 6] 4 2 3,
    !young_search [1, 3, 5, 2, 4, 6] 7 2 3,
    build_max_heap [] == [], is_max_heap (build_max_heap [42]) 1,
    is_max_heap (build_max_heap_prime [42]) 1, build_max_heap_prime [] == [],
    is_d_ary_max_heap (build_d_ary_max_heap [3, 1, 2] 1) 3 1,
    (d_ary_extract_max [5] 1 3).1 == 5, (d_ary_extract_max [] 0 3).1 == 0,
    first.1 == 1, is_young_tableau first.2 2 2,
    young_search [5] 5 1 1, !young_search [5] 3 1 1,
    (young_extract_min [1, 3, 5, 2, 4, 6] 2 3).1 == 1,
    is_young_tableau (young_extract_min [1, 3, 5, 2, 4, 6] 2 3).2 2 3,
    (d_ary_extract_max inserted.1 inserted.2 3).1 == 100,
    first.1 ≤ second.1, !is_max_heap [1, 10, 3] 3,
    !young_search [1, 2, 4, 3, 5, 7, 6, 8, 9] 10 3 3,
    is_max_heap (build_max_heap [5, 3, 8, 1]) 4,
    is_max_heap (build_max_heap [10, 20, 30, 40, 50]) 5,
    is_max_heap (build_max_heap_prime [5, 3, 8, 1]) 4,
    is_max_heap (build_max_heap_prime [10, 20, 30, 40, 50]) 5,
    d_ary_parent (d_ary_child 2 1 4) 4 == 2,
    d_ary_parent (d_ary_child 0 0 3) 3 == 0,
    is_young_tableau (young_insert [SENTINEL, SENTINEL, SENTINEL, SENTINEL] 5 2 2) 2 2,
    young_search [1, 2, 4, 3, 5, 7, 6, 8, 9] 5 3 3,
    young_search [1, 2, 4, 3, 5, 7, 6, 8, 9] 1 3 3,
    young_search [1, 2, 4, 3, 5, 7, 6, 8, 9] 9 3 3
  ].all id

end Imperative

/-! ### Imperative tests -/
example : Imperative.check = true := by native_decide
#eval Imperative.check
example : smallArrays.all (fun a =>
    build_max_heap a == Imperative.build_max_heap a &&
    build_max_heap_prime a == Imperative.build_max_heap_prime a &&
    (List.range 5).all (fun d => build_d_ary_max_heap a d == Imperative.build_d_ary_max_heap a d)) = true := by native_decide
example : (words 3 6).all (fun t => (List.range 5).all fun k =>
    young_search t k 2 3 == Imperative.young_search t k 2 3) = true := by native_decide
example : Imperative.build_max_heap [4,1,3,2,16,9,10,14,8,7] = [16,14,10,8,7,9,3,2,4,1] := by native_decide
example : Imperative.build_max_heap_prime [1,2,3,4,5,6] = [6,4,5,1,3,2] := by native_decide
example : Imperative.young_search [1,3,5,2,4,6] 4 2 3 = true := by native_decide
example : Imperative.young_extract_min [1,3,2,4] 2 2 = (1, [2,3,4,SENTINEL]) := by native_decide
#eval Imperative.d_ary_extract_max (Imperative.build_d_ary_max_heap [4,1,3,2,16,9,10,14,8,7] 3) 10 3

/-! ### Kernel equivalence proofs -/
theorem fold_equiv {α β : Type} (xs : List α) (init : β) (f : β → α → β) :
    Imperative.fold xs init f = xs.foldl f init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simpa [Id.run, pure, bind, Imperative.fold, List.foldl, List.forIn_cons, List.forIn_nil] using ih (f init x)

theorem stopped_fold {α : Type} (step : List Nat → α → Option (List Nat × α))
    (n : Nat) (a : List Nat) :
    ((List.replicate n ()).foldl (fun s _ => Imperative.advance step s) (a, none)) = (a, none) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Id.run, pure, bind, List.replicate_succ, Imperative.advance] using ih

theorem walk_fold {α : Type} (step : List Nat → α → Option (List Nat × α))
    (n : Nat) (a : List Nat) (p : α) :
    ((List.replicate n ()).foldl (fun s _ => Imperative.advance step s) (a, some p)).1 =
      walk step n a p := by
  induction n generalizing a p with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.foldl_cons, Imperative.advance, walk]
    cases h : step a p with
    | none => exact congrArg Prod.fst (stopped_fold step n a)
    | some b => exact ih b.1 b.2

@[simp] theorem walk_equiv {α : Type} (step : List Nat → α → Option (List Nat × α))
    (n : Nat) (a : List Nat) (p : α) : Imperative.walk step n a p = walk step n a p := by
  simpa [Id.run, pure, bind, Imperative.walk, fold_equiv] using walk_fold step n a p

@[simp] theorem swap_equiv (a : List Nat) (i j : Nat) : Imperative.my_swap a i j = my_swap a i j := by
  simp [Id.run, pure, bind, Imperative.my_swap, my_swap]

@[simp] theorem heapify_equiv (a : List Nat) (i n : Nat) :
    Imperative.max_heapify a i n = max_heapify a i n := by
  by_cases h : i < n ∧ i < a.length
  · have hn : ¬(i ≥ n ∨ i ≥ a.length) := by omega
    simp [Id.run, pure, bind, Imperative.max_heapify, max_heapify, h, hn]
  · have hn : i ≥ n ∨ i ≥ a.length := by omega
    simp [Id.run, pure, bind, Imperative.max_heapify, max_heapify, h, hn]

@[simp] theorem sift_equiv (a : List Nat) (i : Nat) : Imperative.sift_up a i = sift_up a i := by
  simp [Id.run, pure, bind, Imperative.sift_up, sift_up]

@[simp] theorem increase_equiv (a : List Nat) (i k : Nat) :
    Imperative.heap_increase_key a i k = heap_increase_key a i k := by
  by_cases h : i < a.length
  · have hn : ¬i ≥ a.length := by omega
    simp [Id.run, pure, bind, Imperative.heap_increase_key, heap_increase_key, h, hn]
  · have hn : i ≥ a.length := by omega
    simp [Id.run, pure, bind, Imperative.heap_increase_key, heap_increase_key, h, hn]

@[simp] theorem reserve_equiv (a : List Nat) (n : Nat) : Imperative.reserve a n = reserve a n := by
  simp [Id.run, pure, bind, Imperative.reserve, reserve]

@[simp] theorem insert_equiv (a : List Nat) (k n : Nat) :
    Imperative.max_heap_insert a k n = max_heap_insert a k n := by
  simp [Id.run, pure, bind, Imperative.max_heap_insert, max_heap_insert]

@[simp] theorem buildLoop_equiv (f : List Nat → Nat → List Nat) (n : Nat) (a : List Nat) :
    Imperative.buildLoop f n a = buildLoop f n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simpa [Id.run, pure, bind, Imperative.buildLoop, fold_equiv, List.replicate_succ, buildLoop] using ih (f a n)

@[simp] theorem build_equiv (a : List Nat) : Imperative.build_max_heap a = build_max_heap a := by
  simp [Id.run, pure, bind, Imperative.build_max_heap, build_max_heap]

@[simp] theorem insertLoop_equiv (keys a : List Nat) (n : Nat) :
    Imperative.insertLoop keys a n = insertLoop keys a n := by
  induction keys generalizing a n with
  | nil => rfl
  | cons k ks ih =>
    simpa [Id.run, pure, bind, Imperative.insertLoop, fold_equiv, insertLoop] using
      ih (max_heap_insert a k n).1 (max_heap_insert a k n).2

@[simp] theorem build_prime_equiv (a : List Nat) :
    Imperative.build_max_heap_prime a = build_max_heap_prime a := by
  simp [Id.run, pure, bind, Imperative.build_max_heap_prime, build_max_heap_prime]

@[simp] theorem d_find_equiv (a : List Nat) (i n d : Nat) :
    Imperative.d_ary_find_largest_child a i n d = d_ary_find_largest_child a i n d := by
  change Imperative.fold (List.range d) i _ = _
  exact fold_equiv _ _ _

@[simp] theorem d_heapify_equiv (a : List Nat) (i n d : Nat) :
    Imperative.d_ary_max_heapify a i n d = d_ary_max_heapify a i n d := by
  by_cases h : i < n ∧ i < a.length
  · have hn : ¬(i ≥ n ∨ i ≥ a.length) := by omega
    simp [Id.run, pure, bind, Imperative.d_ary_max_heapify, d_ary_max_heapify, h, hn]
  · have hn : i ≥ n ∨ i ≥ a.length := by omega
    simp [Id.run, pure, bind, Imperative.d_ary_max_heapify, d_ary_max_heapify, h, hn]

@[simp] theorem d_sift_equiv (a : List Nat) (i d : Nat) :
    Imperative.d_ary_sift_up a i d = d_ary_sift_up a i d := by
  simp [Id.run, pure, bind, Imperative.d_ary_sift_up, d_ary_sift_up]

@[simp] theorem d_increase_equiv (a : List Nat) (i k d : Nat) :
    Imperative.d_ary_increase_key a i k d = d_ary_increase_key a i k d := by
  by_cases h : i < a.length
  · have hn : ¬i ≥ a.length := by omega
    simp [Id.run, pure, bind, Imperative.d_ary_increase_key, d_ary_increase_key, h, hn]
  · have hn : i ≥ a.length := by omega
    simp [Id.run, pure, bind, Imperative.d_ary_increase_key, d_ary_increase_key, h, hn]

@[simp] theorem d_insert_equiv (a : List Nat) (k n d : Nat) :
    Imperative.d_ary_insert a k n d = d_ary_insert a k n d := by
  simp [Id.run, pure, bind, Imperative.d_ary_insert, d_ary_insert]

@[simp] theorem d_extract_equiv (a : List Nat) (n d : Nat) :
    Imperative.d_ary_extract_max a n d = d_ary_extract_max a n d := by
  simp [Id.run, pure, bind, Imperative.d_ary_extract_max, d_ary_extract_max]

@[simp] theorem d_build_equiv (a : List Nat) (d : Nat) :
    Imperative.build_d_ary_max_heap a d = build_d_ary_max_heap a d := by
  simp [Id.run, pure, bind, Imperative.build_d_ary_max_heap, build_d_ary_max_heap]

@[simp] theorem young_set_equiv (a : List Nat) (cols row col value : Nat) :
    Imperative.young_set a cols row col value = young_set a cols row col value := rfl

@[simp] theorem young_down_equiv (a : List Nat) (rows cols row col : Nat) :
    Imperative.youngify_down a rows cols row col = youngify_down a rows cols row col := by
  simp [Id.run, pure, bind, Imperative.youngify_down, youngify_down]

@[simp] theorem young_up_equiv (a : List Nat) (cols row col : Nat) :
    Imperative.young_bubble_up a cols row col = young_bubble_up a cols row col := by
  simp [Id.run, pure, bind, Imperative.young_bubble_up, young_bubble_up]

@[simp] theorem young_extract_equiv (a : List Nat) (rows cols : Nat) :
    Imperative.young_extract_min a rows cols = young_extract_min a rows cols := by
  simp [Id.run, pure, bind, Imperative.young_extract_min, young_extract_min]

@[simp] theorem young_insert_equiv (a : List Nat) (key rows cols : Nat) :
    Imperative.young_insert a key rows cols = young_insert a key rows cols := by
  simp [Id.run, pure, bind, Imperative.young_insert, young_insert]

theorem searchLoop_equiv (a : List Nat) (key rows cols fuel row col : Nat) :
    Imperative.searchLoop a key rows cols fuel row col = searchLoop a key rows cols fuel row col := by
  induction fuel generalizing row col with
  | zero => rfl
  | succ n ih =>
    simp only [Imperative.searchLoop, searchLoop]
    by_cases hb : row < rows ∧ col < cols
    · have hn : ¬(row ≥ rows ∨ col ≥ cols) := by omega
      by_cases he : young_get a cols row col = key
      · simp [Id.run, pure, bind, hb, hn, he]
      · by_cases hg : young_get a cols row col > key
        · by_cases hz : col = 0 <;> simp_all [Id.run, pure, bind]
        · simp [Id.run, pure, bind, hb, hn, he, hg, ih]
    · have hn : row ≥ rows ∨ col ≥ cols := by omega
      simp [Id.run, pure, bind, hb, hn]

@[simp] theorem search_equiv (a : List Nat) (key rows cols : Nat) :
    Imperative.young_search a key rows cols = young_search a key rows cols := by
  by_cases hr : rows = 0 <;> by_cases hc : cols = 0 <;>
    simp [Id.run, pure, bind, Imperative.young_search, young_search, searchLoop_equiv, hr, hc]

theorem fold_and {α : Type} (xs : List α) (p : α → Bool) (b : Bool) :
    xs.foldl (fun ok x => ok && p x) b = (b && xs.all p) := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, Bool.and_assoc]

@[simp] theorem heap_recognizer_equiv (a : List Nat) (n : Nat) :
    Imperative.is_max_heap a n = is_max_heap a n := by
  simp [Imperative.is_max_heap, fold_equiv, fold_and, is_max_heap]

@[simp] theorem d_heap_recognizer_equiv (a : List Nat) (n d : Nat) :
    Imperative.is_d_ary_max_heap a n d = is_d_ary_max_heap a n d := by
  simp [Imperative.is_d_ary_max_heap, fold_equiv, fold_and, is_d_ary_max_heap]

@[simp] theorem tableau_recognizer_equiv (t : List Nat) (rows cols : Nat) :
    Imperative.is_young_tableau t rows cols = is_young_tableau t rows cols := by
  simp [Imperative.is_young_tableau, fold_equiv, fold_and, is_young_tableau]

/-- Exact functional/imperative correspondence, even for the totalized inputs. -/
theorem equivalence (a t : List Nat) (i j n key d rows cols row col : Nat) :
    my_swap a i j = Imperative.my_swap a i j ∧
    max_heapify a i n = Imperative.max_heapify a i n ∧
    build_max_heap a = Imperative.build_max_heap a ∧
    sift_up a i = Imperative.sift_up a i ∧
    heap_increase_key a i key = Imperative.heap_increase_key a i key ∧
    max_heap_insert a key n = Imperative.max_heap_insert a key n ∧
    build_max_heap_prime a = Imperative.build_max_heap_prime a ∧
    d_ary_find_largest_child a i n d = Imperative.d_ary_find_largest_child a i n d ∧
    d_ary_max_heapify a i n d = Imperative.d_ary_max_heapify a i n d ∧
    d_ary_extract_max a n d = Imperative.d_ary_extract_max a n d ∧
    d_ary_sift_up a i d = Imperative.d_ary_sift_up a i d ∧
    d_ary_increase_key a i key d = Imperative.d_ary_increase_key a i key d ∧
    d_ary_insert a key n d = Imperative.d_ary_insert a key n d ∧
    build_d_ary_max_heap a d = Imperative.build_d_ary_max_heap a d ∧
    young_set t cols row col key = Imperative.young_set t cols row col key ∧
    youngify_down t rows cols row col = Imperative.youngify_down t rows cols row col ∧
    young_bubble_up t cols row col = Imperative.young_bubble_up t cols row col ∧
    young_extract_min t rows cols = Imperative.young_extract_min t rows cols ∧
    young_insert t key rows cols = Imperative.young_insert t key rows cols ∧
    young_search t key rows cols = Imperative.young_search t key rows cols ∧
    is_max_heap a n = Imperative.is_max_heap a n ∧
    is_d_ary_max_heap a n d = Imperative.is_d_ary_max_heap a n d ∧
    is_young_tableau t rows cols = Imperative.is_young_tableau t rows cols := by
  simp

end heapsort_problems
end Agent
