import Mathlib

/-!
# Heap sort for Python integer lists

The functional implementation represents the array's complete binary tree explicitly.
`splitChildren` distributes breadth-first positions to the two subtrees, `siftDown`
repairs a root, and `buildMaxHeap` heapifies from the leaves upwards. Extraction removes
the deepest rightmost node, moves its value to the root, and sifts down. Extracted maxima
are placed at the end of the result. Integers are unbounded, as in Python.

The typed interface is `heapSort : List Int → List Int`. `checkedHeapSort` models the
dynamic type check and the exact ValueError message; Python booleans count as integers.
Lean values are immutable, so the caller's input is preserved even in the `Id.run`
implementation. No claim about allocation identity or sorting stability is made.
-/

namespace heap_sort

inductive Heap where
  | empty
  | node (value : Int) (left right : Heap)
  deriving Repr, DecidableEq

def Heap.size : Heap → Nat
  | .empty => 0
  | .node _ l r => 1 + l.size + r.size

def Heap.height : Heap → Nat
  | .empty => 0
  | .node _ l r => 1 + max l.height r.height

/-- The left child wins ties, just as in the source's two strict comparisons. -/
def siftDown (x : Int) (l r : Heap) : Heap :=
  match l, r with
  | .empty, .empty => .node x .empty .empty
  | .node a ll lr, .empty =>
      if x < a then .node a (siftDown x ll lr) .empty else .node x l r
  | .empty, .node b rl rr =>
      if x < b then .node b .empty (siftDown x rl rr) else .node x l r
  | .node a ll lr, .node b rl rr =>
      if x < a ∧ b ≤ a then .node a (siftDown x ll lr) r
      else if x < b then .node b l (siftDown x rl rr)
      else .node x l r
termination_by l.size + r.size
decreasing_by all_goals (simp only [Heap.size]; omega)

/-- State for distributing consecutive levels: block width, remaining slots, right side. -/
def nextSlot (width remaining : Nat) (right : Bool) : Nat × Nat × Bool :=
  if remaining ≤ 1 then
    if right then (2 * width, 2 * width, false) else (width, width, true)
  else (width, remaining - 1, right)

def splitAux (width remaining : Nat) (right : Bool) : List Int → List Int × List Int
  | [] => ([], [])
  | x :: xs =>
      let s := nextSlot width remaining right
      let p := splitAux s.1 s.2.1 s.2.2 xs
      if right then (p.1, x :: p.2) else (x :: p.1, p.2)

def splitChildren (xs : List Int) : List Int × List Int := splitAux 1 1 false xs

private theorem splitAux_length (xs : List Int) (w k : Nat) (b : Bool) :
    (splitAux w k b xs).1.length + (splitAux w k b xs).2.length = xs.length := by
  induction xs generalizing w k b with
  | nil => simp [splitAux]
  | cons x xs ih =>
      cases b <;> simp [splitAux, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

def buildMaxHeap : List Int → Heap
  | [] => .empty
  | x :: xs =>
      let p := splitChildren xs
      siftDown x (buildMaxHeap p.1) (buildMaxHeap p.2)
termination_by xs => xs.length
decreasing_by
  all_goals
    have h := splitAux_length xs 1 1 false
    simp only [splitChildren] at *
    simp_wf
    omega

/-- Remove the deepest rightmost leaf of a nonempty tree. -/
def removeLast (x : Int) (l r : Heap) : Int × Heap :=
  match l, r with
  | .empty, .empty => (x, .empty)
  | .node a ll lr, .empty =>
      let p := removeLast a ll lr
      (p.1, .node x p.2 .empty)
  | .empty, .node b rl rr =>
      let p := removeLast b rl rr
      (p.1, .node x .empty p.2)
  | .node a ll lr, .node b rl rr =>
      if l.height > r.height then
        let p := removeLast a ll lr
        (p.1, .node x p.2 r)
      else
        let p := removeLast b rl rr
        (p.1, .node x l p.2)
termination_by l.size + r.size
decreasing_by all_goals (simp only [Heap.size]; omega)

/-- Swap the last leaf into the root and heapify the reduced heap. -/
def dropMax (_x : Int) (l r : Heap) : Heap :=
  match l, r with
  | .empty, .empty => .empty
  | .node a ll lr, .empty =>
      let p := removeLast a ll lr
      siftDown p.1 p.2 .empty
  | .empty, .node b rl rr =>
      let p := removeLast b rl rr
      siftDown p.1 .empty p.2
  | .node a ll lr, .node b rl rr =>
      if l.height > r.height then
        let p := removeLast a ll lr
        siftDown p.1 p.2 r
      else
        let p := removeLast b rl rr
        siftDown p.1 l p.2

/-- There is one unit of fuel per input element, including the final singleton. -/
def extract : Nat → Heap → List Int
  | 0, _ => []
  | _ + 1, .empty => []
  | n + 1, .node x l r => extract n (dropMax x l r) ++ [x]

def heapSort (xs : List Int) : List Int := extract xs.length (buildMaxHeap xs)

inductive PyValue where
  | int (value : Int)
  | bool (value : Bool)
  | float (value : Float)
  | str (value : String)
  | list (values : List PyValue)
  | none
  | other (typeName : String)
  deriving Repr

def isPythonInt : PyValue → Bool
  | .int _ | .bool _ => true
  | _ => false

def pre : PyValue → Bool
  | .list xs => xs.all isPythonInt
  | _ => false

def asInt : PyValue → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | _ => none

def decodeInts : List PyValue → Option (List Int)
  | [] => some []
  | x :: xs => do
      let n ← asInt x
      let ns ← decodeInts xs
      pure (n :: ns)

def decodeInput : PyValue → Option (List Int)
  | .list xs => decodeInts xs
  | _ => none

def checkedHeapSort (v : PyValue) : Except String (List Int) :=
  match decodeInput v with
  | none => .error "Input must be List[int]"
  | some xs => .ok (heapSort xs)

deriving instance DecidableEq for Except

-- Unit tests, including every positive example from the source.
example : heapSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : heapSort [] = [] := by native_decide
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
example : heapSort [-5, 0, 7, -5, -1] = [-5, -5, -1, 0, 7] := by native_decide
example : checkedHeapSort (.list [.int 1, .float 2.5]) =
    .error "Input must be List[int]" := by native_decide
example : checkedHeapSort (.int 7) = .error "Input must be List[int]" := by native_decide
example : checkedHeapSort (.list [.bool true, .int (-2), .bool false]) =
    .ok [-2, 0, 1] := by native_decide
#eval heapSort [3, 1, 2]
#eval checkedHeapSort (.list [.int 1, .float 2.5])

/-- The Python `pre`: the argument is a list, and every item is an integer (or bool). -/
def Pre (v : PyValue) : Prop := pre v = true

-- The following invariants connect heap operations to integer-list semantics.
def Heap.contents : Heap → Multiset Int
  | .empty => 0
  | .node x l r => {x} + l.contents + r.contents

def Heap.Ordered : Heap → Prop
  | .empty => True
  | .node x l r => l.Ordered ∧ r.Ordered ∧
      (∀ y ∈ l.contents, y ≤ x) ∧ (∀ y ∈ r.contents, y ≤ x)

private theorem contents_card (t : Heap) : t.contents.card = t.size := by
  induction t <;> simp_all [Heap.contents, Heap.size, Nat.add_assoc, Nat.add_comm]

private theorem siftDown_contents (x : Int) (l r : Heap) :
    (siftDown x l r).contents = {x} + l.contents + r.contents := by
  fun_induction siftDown x l r <;>
    simp_all only [Heap.contents, add_zero, add_assoc, add_left_comm, add_comm]

private theorem list_cons_contents (x : Int) (xs : List Int) :
    ((x :: xs : List Int) : Multiset Int) = {x} + (xs : Multiset Int) := rfl

private theorem splitAux_contents (xs : List Int) (w k : Nat) (b : Bool) :
    ((splitAux w k b xs).1 : Multiset Int) + (splitAux w k b xs).2 = xs := by
  induction xs generalizing w k b with
  | nil => simp [splitAux]
  | cons x xs ih =>
      have h := congrArg (fun m : Multiset Int => {x} + m)
        (ih (nextSlot w k b).1 (nextSlot w k b).2.1 (nextSlot w k b).2.2)
      cases b <;> simpa only [splitAux, Bool.false_eq_true, ↓reduceIte, list_cons_contents,
        add_assoc, add_left_comm, add_comm] using h

private theorem siftDown_bound (x : Int) (l r : Heap) (a : Int)
    (hx : x ≤ a) (hl : ∀ y ∈ l.contents, y ≤ a) (hr : ∀ y ∈ r.contents, y ≤ a) :
    ∀ y ∈ (siftDown x l r).contents, y ≤ a := by
  intro y hy
  rw [siftDown_contents] at hy
  simp only [Multiset.mem_add, Multiset.mem_singleton] at hy
  rcases hy with (rfl | hy) | hy
  · exact hx
  · exact hl y hy
  · exact hr y hy

private theorem ordered_bound {x a : Int} {l r : Heap}
    (h : (Heap.node x l r).Ordered) (hx : x ≤ a) :
    ∀ y ∈ (Heap.node x l r).contents, y ≤ a := by
  intro y hy
  simp only [Heap.contents, Multiset.mem_add, Multiset.mem_singleton] at hy
  rcases hy with (rfl | hy) | hy
  · exact hx
  · exact (h.2.2.1 y hy).trans hx
  · exact (h.2.2.2 y hy).trans hx

private theorem empty_bound (a : Int) : ∀ y ∈ Heap.empty.contents, y ≤ a := by
  simp [Heap.contents]

private theorem siftDown_ordered (x : Int) (l r : Heap)
    (hl : l.Ordered) (hr : r.Ordered) : (siftDown x l r).Ordered := by
  fun_induction siftDown x l r with
  | case1 => exact ⟨hl, hr, empty_bound x, empty_bound x⟩
  | case2 a ll lr h ih =>
      exact ⟨ih hl.1 hl.2.1, hr,
        siftDown_bound x ll lr a (le_of_lt h) hl.2.2.1 hl.2.2.2, empty_bound a⟩
  | case3 a ll lr h =>
      exact ⟨hl, hr, ordered_bound hl (by omega), empty_bound x⟩
  | case4 b rl rr h ih =>
      exact ⟨hl, ih hr.1 hr.2.1, empty_bound b,
        siftDown_bound x rl rr b (le_of_lt h) hr.2.2.1 hr.2.2.2⟩
  | case5 b rl rr h =>
      exact ⟨hl, hr, empty_bound x, ordered_bound hr (by omega)⟩
  | case6 a ll lr b rl rr h ih =>
      exact ⟨ih hl.1 hl.2.1, hr,
        siftDown_bound x ll lr a (le_of_lt h.1) hl.2.2.1 hl.2.2.2,
        ordered_bound hr h.2⟩
  | case7 a ll lr b rl rr hn h ih =>
      exact ⟨hl, ih hr.1 hr.2.1, ordered_bound hl (by omega),
        siftDown_bound x rl rr b (le_of_lt h) hr.2.2.1 hr.2.2.2⟩
  | case8 a ll lr b rl rr hn h =>
      exact ⟨hl, hr, ordered_bound hl (by omega), ordered_bound hr (by omega)⟩

private theorem buildMaxHeap_contents (xs : List Int) :
    (buildMaxHeap xs).contents = xs := by
  fun_induction buildMaxHeap xs with
  | case1 => simp [Heap.contents]
  | case2 x xs p ihl ihr =>
      rw [siftDown_contents, ihl, ihr, add_assoc]
      exact congrArg (fun m : Multiset Int => {x} + m) (splitAux_contents xs 1 1 false)


private theorem buildMaxHeap_ordered (xs : List Int) : (buildMaxHeap xs).Ordered := by
  fun_induction buildMaxHeap xs with
  | case1 => trivial
  | case2 x xs p ihl ihr => exact siftDown_ordered x _ _ ihl ihr

private theorem removeLast_contents (x : Int) (l r : Heap) :
    {(removeLast x l r).1} + (removeLast x l r).2.contents =
      {x} + l.contents + r.contents := by
  fun_induction removeLast x l r with
  | case1 x => simp [Heap.contents]
  | case2 x a ll lr p ih =>
      simpa only [Heap.contents, add_zero, zero_add, add_assoc, add_left_comm, add_comm] using
        congrArg (fun m : Multiset Int => {x} + m) ih
  | case3 x b rl rr p ih =>
      simpa only [Heap.contents, add_zero, zero_add, add_assoc, add_left_comm, add_comm] using
        congrArg (fun m : Multiset Int => {x} + m) ih
  | case4 x a ll lr b rl rr h ih =>
      simpa only [h, ↓reduceIte, Heap.contents, add_assoc, add_left_comm, add_comm] using
        congrArg (fun m : Multiset Int => {x} + m + (Heap.node b rl rr).contents) ih
  | case5 x a ll lr b rl rr h ih =>
      simpa only [h, ↓reduceIte, Heap.contents, add_assoc, add_left_comm, add_comm] using
        congrArg (fun m : Multiset Int => {x} + (Heap.node a ll lr).contents + m) ih

private theorem removeLast_subset (x : Int) (l r : Heap) :
    ∀ y ∈ (removeLast x l r).2.contents, y ∈ (Heap.node x l r).contents := by
  intro y hy
  rw [Heap.contents, ← removeLast_contents x l r]
  exact Multiset.mem_add.mpr (Or.inr hy)

private theorem removeLast_ordered (x : Int) (l r : Heap)
    (h : (Heap.node x l r).Ordered) : (removeLast x l r).2.Ordered := by
  fun_induction removeLast x l r with
  | case1 x => trivial
  | case2 x a ll lr p ih =>
      exact ⟨ih h.1, h.2.1,
        fun y hy => h.2.2.1 y (removeLast_subset a ll lr y hy), h.2.2.2⟩
  | case3 x b rl rr p ih =>
      exact ⟨h.1, ih h.2.1, h.2.2.1,
        fun y hy => h.2.2.2 y (removeLast_subset b rl rr y hy)⟩
  | case4 x a ll lr b rl rr hc ih =>
      simp only [hc, ↓reduceIte]
      exact ⟨ih h.1, h.2.1,
        fun y hy => h.2.2.1 y (removeLast_subset a ll lr y hy), h.2.2.2⟩
  | case5 x a ll lr b rl rr hc ih =>
      simp only [hc, ↓reduceIte]
      exact ⟨h.1, ih h.2.1, h.2.2.1,
        fun y hy => h.2.2.2 y (removeLast_subset b rl rr y hy)⟩

private theorem dropMax_contents (x : Int) (l r : Heap) :
    (dropMax x l r).contents = l.contents + r.contents := by
  cases l with
  | empty =>
      cases r with
      | empty => simp [dropMax, Heap.contents]
      | node b rl rr =>
          simpa only [dropMax, siftDown_contents, Heap.contents, add_zero, zero_add,
            add_assoc, add_left_comm, add_comm] using removeLast_contents b rl rr
  | node a ll lr =>
      cases r with
      | empty =>
          simpa only [dropMax, siftDown_contents, Heap.contents, add_zero, zero_add] using
            removeLast_contents a ll lr
      | node b rl rr =>
          simp only [dropMax]
          split
          · rw [siftDown_contents, removeLast_contents]
            rfl
          · rw [siftDown_contents]
            have h := congrArg (fun m : Multiset Int => (Heap.node a ll lr).contents + m)
              (removeLast_contents b rl rr)
            simpa only [Heap.contents, add_assoc, add_left_comm, add_comm] using h

private theorem dropMax_ordered (x : Int) (l r : Heap)
    (h : (Heap.node x l r).Ordered) : (dropMax x l r).Ordered := by
  cases l with
  | empty =>
      cases r with
      | empty => trivial
      | node b rl rr =>
          exact siftDown_ordered _ _ _ trivial (removeLast_ordered b rl rr h.2.1)
  | node a ll lr =>
      cases r with
      | empty =>
          exact siftDown_ordered _ _ _ (removeLast_ordered a ll lr h.1) trivial
      | node b rl rr =>
          simp only [dropMax]
          split
          · exact siftDown_ordered _ _ _ (removeLast_ordered a ll lr h.1) h.2.1
          · exact siftDown_ordered _ _ _ h.1 (removeLast_ordered b rl rr h.2.1)

private theorem dropMax_size (x : Int) (l r : Heap) :
    (dropMax x l r).size = l.size + r.size := by
  simpa only [Multiset.card_add, contents_card] using
    congrArg Multiset.card (dropMax_contents x l r)

private theorem extract_contents (n : Nat) (t : Heap) (hn : t.size ≤ n) :
    (extract n t : Multiset Int) = t.contents := by
  induction n generalizing t with
  | zero =>
      cases t with
      | empty => rfl
      | node x l r => simp [Heap.size] at hn
  | succ n ih =>
      cases t with
      | empty => rfl
      | node x l r =>
          have hs : (dropMax x l r).size ≤ n := by
            rw [dropMax_size]
            simp only [Heap.size] at hn
            omega
          change ((extract n (dropMax x l r) ++ [x] : List Int) : Multiset Int) = _
          rw [← Multiset.coe_add, ih _ hs, dropMax_contents, Heap.contents]
          simp [add_comm]

private theorem extract_sorted (n : Nat) (t : Heap) (hn : t.size ≤ n)
    (ht : t.Ordered) : (extract n t).Pairwise (· ≤ ·) := by
  induction n generalizing t with
  | zero => simp [extract]
  | succ n ih =>
      cases t with
      | empty => simp [extract]
      | node x l r =>
          have hs : (dropMax x l r).size ≤ n := by
            rw [dropMax_size]
            simp only [Heap.size] at hn
            omega
          rw [extract, List.pairwise_append]
          refine ⟨ih _ hs (dropMax_ordered x l r ht), by simp, ?_⟩
          intro y hy z hz
          simp only [List.mem_singleton] at hz
          subst z
          have hm : y ∈ (extract n (dropMax x l r) : Multiset Int) := hy
          rw [extract_contents n _ hs, dropMax_contents] at hm
          rcases Multiset.mem_add.mp hm with hm | hm
          · exact ht.2.2.1 y hm
          · exact ht.2.2.2 y hm

private theorem buildMaxHeap_size (xs : List Int) : (buildMaxHeap xs).size = xs.length := by
  rw [← contents_card, buildMaxHeap_contents]
  rfl

/-- All output positions are in nondecreasing order. -/
def sorted_prop (_xs ys : List Int) : Prop := ys.Pairwise (· ≤ ·)

theorem sorted_thm (xs : List Int) : sorted_prop xs (heapSort xs) := by
  exact extract_sorted xs.length (buildMaxHeap xs)
    (by rw [buildMaxHeap_size]) (buildMaxHeap_ordered xs)

/-- Permutation preserves values and their multiplicities. -/
def permutation_prop (xs ys : List Int) : Prop := ys.Perm xs

theorem permutation_thm (xs : List Int) : permutation_prop xs (heapSort xs) := by
  apply Multiset.coe_eq_coe.mp
  rw [heapSort, extract_contents xs.length _ (by rw [buildMaxHeap_size]), buildMaxHeap_contents]

def length_prop (xs ys : List Int) : Prop := ys.length = xs.length

theorem length_thm (xs : List Int) : length_prop xs (heapSort xs) :=
  (permutation_thm xs).length_eq

def multiplicity_prop (xs ys : List Int) : Prop := ∀ z : Int, ys.count z = xs.count z

theorem multiplicity_thm (xs : List Int) : multiplicity_prop xs (heapSort xs) :=
  fun z => (permutation_thm xs).count_eq z

/-- Sorting an already sorted input returns the same sequence. -/
def ordered_input_prop (xs ys : List Int) : Prop := xs.Pairwise (· ≤ ·) → ys = xs

theorem ordered_input_thm (xs : List Int) : ordered_input_prop xs (heapSort xs) := by
  intro h
  exact List.eq_of_perm_of_sorted (permutation_thm xs) (sorted_thm xs) h

/-- Empty and singleton inputs are returned by value unchanged. -/
def small_input_prop (xs ys : List Int) : Prop := xs.length ≤ 1 → ys = xs

theorem small_input_thm (xs : List Int) : small_input_prop xs (heapSort xs) := by
  intro h
  apply ordered_input_thm xs
  cases xs with
  | nil => simp
  | cons x xs =>
      cases xs with
      | nil => simp
      | cons y ys => simp at h

def idempotent_prop (_xs ys : List Int) : Prop := heapSort ys = ys

theorem idempotent_thm (xs : List Int) : idempotent_prop xs (heapSort xs) :=
  ordered_input_thm (heapSort xs) (sorted_thm xs)

private theorem decodeInts_isSome (xs : List PyValue) :
    (decodeInts xs).isSome = xs.all isPythonInt := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases x <;> cases hd : decodeInts xs <;>
        simp_all [decodeInts, asInt, isPythonInt]

private theorem pre_iff_decode (v : PyValue) :
    Pre v ↔ ∃ xs, decodeInput v = some xs := by
  cases v <;> simp [Pre, pre, decodeInput, ← decodeInts_isSome, Option.isSome_iff_exists]

/-- Invalid arguments raise exactly the source's ValueError; all valid ones succeed. -/
def validation_prop (v : PyValue) : Prop :=
  (checkedHeapSort v = .error "Input must be List[int]" ↔ ¬ Pre v) ∧
  (∀ xs, decodeInput v = some xs → checkedHeapSort v = .ok (heapSort xs))

theorem validation_thm (v : PyValue) : validation_prop v := by
  unfold validation_prop
  rw [pre_iff_decode]
  unfold checkedHeapSort
  cases h : decodeInput v <;> simp

/-- The full successful-output contract, with no restriction on integer values or list size. -/
def Post_prop (xs ys : List Int) : Prop :=
  sorted_prop xs ys ∧ permutation_prop xs ys ∧ length_prop xs ys ∧
  multiplicity_prop xs ys ∧ ordered_input_prop xs ys ∧ small_input_prop xs ys ∧
  idempotent_prop xs ys

-- Property-based tests: randomized integer-list sampling.
-- Each check is an executable statement, independent of the proof terms above.
-- PBT: sorted_prop.
#eval Plausible.Testable.check (∀ xs : List Int, (heapSort xs).Pairwise (· ≤ ·))
-- PBT: permutation_prop.
#eval Plausible.Testable.check (∀ xs : List Int, (heapSort xs).Perm xs)
-- PBT: length_prop.
#eval Plausible.Testable.check (∀ xs : List Int, (heapSort xs).length = xs.length)
-- PBT: multiplicity_prop, including values absent from the input.
#eval Plausible.Testable.check (∀ (xs : List Int) (z : Int),
  (heapSort xs).count z = xs.count z)
-- PBT: idempotent_prop.
#eval Plausible.Testable.check (∀ xs : List Int, heapSort (heapSort xs) = heapSort xs)

/-- Exhaustive lists of a given length over a finite alphabet. -/
def listsOfLength {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun x => (listsOfLength alphabet n).map (x :: ·)

/-- All 3,906 lists of length at most five over [-2,-1,0,1,2]. -/
def smallInputs : List (List Int) :=
  (List.range 6).flatMap (listsOfLength [-2, -1, 0, 1, 2])

-- PBT: ordered_input_prop. Exhaustive implication avoids discarded random samples.
example : smallInputs.all (fun xs =>
    decide (xs.Pairwise (· ≤ ·) → heapSort xs = xs)) = true := by native_decide
-- PBT: small_input_prop; both lengths zero and one occur in this enumeration.
example : smallInputs.all (fun xs =>
    decide (xs.length ≤ 1 → heapSort xs = xs)) = true := by native_decide

/-- A finite support check expresses the universal multiplicity clause:
counts of values outside `xs ++ ys` are zero on both sides. -/
def postCheck (xs : List Int) : Bool :=
  let ys := heapSort xs
  decide (ys.Pairwise (· ≤ ·)) && decide (ys.Perm xs) &&
    decide (ys.length = xs.length) &&
    (xs ++ ys).all (fun z => decide (ys.count z = xs.count z)) &&
    decide (xs.Pairwise (· ≤ ·) → ys = xs) &&
    decide (xs.length ≤ 1 → ys = xs) && decide (heapSort ys = ys)

-- PBT: every conjunct of Post_prop, over all 3,906 small inputs and random lists.
example : smallInputs.all postCheck = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, postCheck xs = true)

/-- Dynamic values have no Plausible sampler, so enumerate lists of mixed values. -/
def dynamicAtoms : List PyValue :=
  [.int (-3), .int 0, .int 9, .bool false, .bool true,
   .float 2.5, .float 2.0, .str "x", .none, .list [], .other "tuple"]

def dynamicInputs : List PyValue :=
  dynamicAtoms ++ ((List.range 4).flatMap (listsOfLength dynamicAtoms)).map PyValue.list

-- PBT: validation_prop. Validity is checked by the independent Python-style `pre`.
example : dynamicInputs.all (fun v =>
    decide (checkedHeapSort v = .error "Input must be List[int]") == !pre v) = true := by
  native_decide
example : dynamicInputs.all (fun v =>
    match decodeInput v with
    | none => !pre v
    | some xs => pre v && decide (checkedHeapSort v = .ok (heapSort xs))) = true := by
  native_decide

/-- Every typed input satisfies the complete successful-output contract. -/
theorem typed_correctness_thm (xs : List Int) : Post_prop xs (heapSort xs) :=
  ⟨sorted_thm xs, permutation_thm xs, length_thm xs, multiplicity_thm xs,
   ordered_input_thm xs, small_input_thm xs, idempotent_thm xs⟩

/-- The dynamic precondition guarantees success and the complete postcondition. -/
theorem correctness_thm (v : PyValue) : Pre v →
    ∃ xs ys, decodeInput v = some xs ∧ checkedHeapSort v = .ok ys ∧ Post_prop xs ys := by
  intro hv
  obtain ⟨xs, hx⟩ := (pre_iff_decode v).mp hv
  exact ⟨xs, heapSort xs, hx, (validation_thm v).2 xs hx, typed_correctness_thm xs⟩

/-- Mutable heap and output state. The indices are the source's descending loop counter;
one extra iteration emits the final singleton root. -/
def extractImperative (steps : List Nat) (initial : Heap) (suffix : List Int) : List Int := Id.run do
  let mut heap := initial
  let mut result := suffix
  for _ in steps do
    match heap with
    | .empty => pure ()
    | .node x l r =>
        heap := dropMax x l r
        result := x :: result
  return result

def heapSortImperative (xs : List Int) : List Int := Id.run do
  let heap := buildMaxHeap xs
  let mut result : List Int := []
  result := extractImperative (List.range xs.length).reverse heap result
  return result

def checkedHeapSortImperative (v : PyValue) : Except String (List Int) :=
  match decodeInput v with
  | none => .error "Input must be List[int]"
  | some xs => .ok (heapSortImperative xs)

-- Imperative tests.
example : heapSortImperative [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSortImperative [] = [] := by native_decide
example : heapSortImperative [1] = [1] := by native_decide
example : heapSortImperative [3, -1, 4, -1, 0] = [-1, -1, 0, 3, 4] := by native_decide
example : heapSortImperative [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : checkedHeapSortImperative (.list [.int 1, .float 2.5]) =
    .error "Input must be List[int]" := by native_decide
#eval heapSortImperative [9, 8, 7, 6, 5, 4, 3, 2, 1]
example : smallInputs.all (fun xs => decide (heapSort xs = heapSortImperative xs)) = true := by
  native_decide

private theorem extract_empty (n : Nat) : extract n Heap.empty = [] := by
  cases n <;> rfl

private theorem extractImperative_eq (steps : List Nat) (t : Heap) (suffix : List Int) :
    extractImperative steps t suffix = extract steps.length t ++ suffix := by
  induction steps generalizing t suffix with
  | nil => simp [extractImperative, extract]
  | cons i steps ih =>
      cases t with
      | empty => simpa [extractImperative, extract, extract_empty] using ih Heap.empty suffix
      | node x l r =>
          simpa [extractImperative, extract, List.append_assoc] using
            ih (dropMax x l r) (x :: suffix)

/-- Functional and imperative implementations agree for every integer list. -/
theorem equivalence_thm (xs : List Int) : heapSort xs = heapSortImperative xs := by
  simp [heapSortImperative, extractImperative_eq, heapSort]

/-- Equivalence also includes invalid inputs and the exact error result. -/
theorem checked_equivalence_thm (v : PyValue) : checkedHeapSort v = checkedHeapSortImperative v := by
  unfold checkedHeapSort checkedHeapSortImperative
  cases decodeInput v <;> simp [equivalence_thm]

end heap_sort
