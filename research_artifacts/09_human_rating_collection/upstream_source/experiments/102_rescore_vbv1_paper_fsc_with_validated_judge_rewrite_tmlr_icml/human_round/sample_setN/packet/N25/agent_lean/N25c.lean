import Mathlib

/-!
# Heap sort of integer lists

A functional translation of Python's max-heap sort.  A binary tree represents
array positions (left child `2*i+1`, right child `2*i+2`).  Insertion follows the
binary address of the next array position.  Heap construction is bottom-up;
sift-down compares the root, left child, then right child using strict `<`.
Extraction removes the deepest rightmost leaf (the last array position), puts
it at the root, and sifts it down. Extracted maxima are accumulated in reverse
order, giving an ascending result. No library sorting routine is used.

`List Int` expresses the valid-input domain, including arbitrary-size and
negative integers. A separate checked interface models Python's dynamic input
validation and ValueError; Python booleans, which are integers, are accepted.
Pure values model the input copy: the caller's list is never modified.
-/

namespace heap_sort

deriving instance DecidableEq for Except

inductive Tree where
  | empty
  | node (key : Int) (left right : Tree)
  deriving Repr, DecidableEq

namespace Tree

def size : Tree → Nat
  | .empty => 0
  | .node _ l r => 1 + l.size + r.size

def height : Tree → Nat
  | .empty => 0
  | .node _ l r => 1 + max l.height r.height

def values : Tree → Multiset Int
  | .empty => 0
  | .node x l r => {x} + l.values + r.values

/-- Binary address of a one-based array position: false = left, true = right. -/
def address (n : Nat) : List Bool :=
  if n ≤ 1 then []
  else address (n / 2) ++ [n % 2 == 1]
termination_by n
decreasing_by omega

/-- Insert at an array address. The occupied-address fallback makes the
operation total; the next address in a complete tree is always vacant. -/
def insertAt (x : Int) : List Bool → Tree → Tree
  | _, .empty => .node x .empty .empty
  | [], .node y l r => .node y (insertAt x [] l) r
  | false :: p, .node y l r => .node y (insertAt x p l) r
  | true :: p, .node y l r => .node y l (insertAt x p r)
termination_by _ t => t.size
decreasing_by all_goals simp only [size]; omega

def insert (t : Tree) (x : Int) : Tree :=
  insertAt x (address (t.size + 1)) t

/-- Python's `heapify`: restore a root whose two subtrees are already heaps. -/
def sift (x : Int) (l r : Tree) : Tree :=
  match l, r with
  | .empty, .empty => .node x .empty .empty
  | .node a ll lr, .empty =>
      if x < a then .node a (sift x ll lr) .empty
      else .node x l r
  | .empty, .node b rl rr =>
      if x < b then .node b .empty (sift x rl rr)
      else .node x l r
  | .node a ll lr, .node b rl rr =>
      if x < a then
        if a < b then .node b l (sift x rl rr)
        else .node a (sift x ll lr) r
      else if x < b then .node b l (sift x rl rr)
      else .node x l r
termination_by l.size + r.size
decreasing_by all_goals simp only [size]; omega

def heapify : Tree → Tree
  | .empty => .empty
  | .node x l r => sift x l.heapify r.heapify

/-- Remove the deepest, rightmost leaf, i.e. the last breadth-first position. -/
def removeLast : Tree → Int × Tree
  | .empty => (0, .empty)
  | .node x .empty .empty => (x, .empty)
  | .node x (.node a ll lr) .empty =>
      let q := removeLast (.node a ll lr)
      (q.1, .node x q.2 .empty)
  | .node x .empty (.node b rl rr) =>
      let q := removeLast (.node b rl rr)
      (q.1, .node x .empty q.2)
  | .node x (.node a ll lr) (.node b rl rr) =>
      if (Tree.node a ll lr).height ≤ (Tree.node b rl rr).height then
        let q := removeLast (.node b rl rr)
        (q.1, .node x (.node a ll lr) q.2)
      else
        let q := removeLast (.node a ll lr)
        (q.1, .node x q.2 (.node b rl rr))

/-- Swap the maximum with the last leaf, remove it, and repair the reduced heap. -/
def pop : Tree → Tree
  | .empty => .empty
  | .node _ .empty .empty => .empty
  | .node _ (.node a ll lr) .empty =>
      let q := removeLast (.node a ll lr)
      sift q.1 q.2 .empty
  | .node _ .empty (.node b rl rr) =>
      let q := removeLast (.node b rl rr)
      sift q.1 .empty q.2
  | .node _ (.node a ll lr) (.node b rl rr) =>
      if (Tree.node a ll lr).height ≤ (Tree.node b rl rr).height then
        let q := removeLast (.node b rl rr)
        sift q.1 (.node a ll lr) q.2
      else
        let q := removeLast (.node a ll lr)
        sift q.1 q.2 (.node b rl rr)

def drain : Nat → Tree → List Int
  | 0, _ => []
  | _ + 1, .empty => []
  | n + 1, .node x l r => drain n (pop (.node x l r)) ++ [x]

end Tree

open Tree

def build_max_heap (xs : List Int) : Tree :=
  (xs.foldl Tree.insert .empty).heapify

def heapSort (xs : List Int) : List Int :=
  Tree.drain xs.length (build_max_heap xs)

inductive PyAtom where
  | integer (value : Int)
  | boolean (value : Bool)
  | floating (value : Float)
  | other
  deriving Repr

inductive PyInput where
  | list (values : List PyAtom)
  | notList
  deriving Repr

def decodeAtom : PyAtom → Option Int
  | .integer z => some z
  | .boolean b => some (if b then 1 else 0)
  | .floating _ | .other => none

def decode : PyInput → Option (List Int)
  | .notList => none
  | .list xs => xs.mapM decodeAtom

def checkedHeapSort (input : PyInput) : Except String (List Int) :=
  match decode input with
  | none => .error "Input must be List[int]"
  | some xs => .ok (heapSort xs)

-- Fixed examples from the Python program, plus negative and mixed-sign inputs.
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
example : heapSort [-3, 0, -1, -3, 2] = [-3, -3, -1, 0, 2] := by native_decide
example : checkedHeapSort (.list [.integer 1, .floating 2.5]) =
    .error "Input must be List[int]" := by native_decide
example : checkedHeapSort .notList = .error "Input must be List[int]" := by native_decide
example : checkedHeapSort (.list [.boolean true, .integer (-1), .boolean false]) =
    .ok [-1, 0, 1] := by native_decide
#eval heapSort [3, 1, 2]
#eval checkedHeapSort (.list [.integer 1, .floating 2.5])

/-- The static input type discharges Python's list/integer precondition. -/
def Pre (_xs : List Int) : Prop := True

namespace Tree

/-- A max heap: both subtrees are heaps and every descendant is at most the root. -/
def IsHeap : Tree → Prop
  | .empty => True
  | .node x l r => IsHeap l ∧ IsHeap r ∧
      (∀ z ∈ l.values, z ≤ x) ∧ (∀ z ∈ r.values, z ≤ x)

@[simp] theorem card_values (t : Tree) : t.values.card = t.size := by
  induction t with
  | empty => simp [values, size]
  | node x l r il ir => simp [values, size, il, ir]; omega

theorem insertAt_values (x : Int) (p : List Bool) (t : Tree) :
    (insertAt x p t).values = {x} + t.values := by
  fun_induction insertAt <;> simp_all only [values, add_zero] <;>
    simp only [add_assoc, add_left_comm]

theorem insert_values (t : Tree) (x : Int) :
    (insert t x).values = {x} + t.values := by
  exact insertAt_values x _ t

theorem fold_insert_values (xs : List Int) (t : Tree) :
    (xs.foldl insert t).values = (xs : Multiset Int) + t.values := by
  induction xs generalizing t with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, insert_values]
      change (xs : Multiset Int) + ({x} + t.values) = ({x} + (xs : Multiset Int)) + t.values
      simp only [add_assoc, add_comm]

theorem sift_values (x : Int) (l r : Tree) :
    (sift x l r).values = {x} + l.values + r.values := by
  fun_induction sift <;> simp_all only [values, add_zero] <;>
    simp only [add_assoc, add_left_comm]

private theorem bound_transfer {s : Multiset Int} {a b : Int}
    (h : ∀ z ∈ s, z ≤ a) (hab : a ≤ b) : ∀ z ∈ s, z ≤ b :=
  fun z hz => (h z hz).trans hab

theorem sift_heap (x : Int) (l r : Tree) (hl : IsHeap l) (hr : IsHeap r) :
    IsHeap (sift x l r) := by
  fun_induction sift <;>
    simp_all [IsHeap, values, sift_values, or_imp, forall_and]
  all_goals
    try rcases hl with ⟨hl1, hl2, hl3, hl4⟩
    try rcases hr with ⟨hr1, hr2, hr3, hr4⟩
    repeat' apply And.intro
    all_goals first
      | assumption
      | omega
      | (apply bound_transfer; assumption; omega)

theorem heapify_values (t : Tree) : t.heapify.values = t.values := by
  induction t with
  | empty => rfl
  | node x l r il ir => simp [heapify, sift_values, values, il, ir]

theorem heapify_heap (t : Tree) : IsHeap t.heapify := by
  induction t with
  | empty => trivial
  | node x l r il ir => exact sift_heap x _ _ il ir


theorem removeLast_values (t : Tree) (h : t ≠ .empty) :
    {(removeLast t).1} + (removeLast t).2.values = t.values := by
  fun_induction removeLast <;> dsimp +zetaDelta only at * <;>
    simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false, values,
      add_zero, true_implies]
  all_goals
    rename_i ih
    ext z
    have hc := congrArg (Multiset.count z) ih
    simp only [Multiset.count_add] at hc ⊢
    omega

theorem removeLast_subset (t : Tree) :
    ∀ z ∈ (removeLast t).2.values, z ∈ t.values := by
  cases t with
  | empty => simp [removeLast, values]
  | node x l r =>
      intro z hz
      rw [← removeLast_values (.node x l r) (by simp)]
      exact Multiset.mem_add.mpr (Or.inr hz)

theorem removeLast_heap (t : Tree) (ht : IsHeap t) :
    IsHeap (removeLast t).2 := by
  fun_induction removeLast <;> dsimp +zetaDelta only at * <;>
    simp_all [IsHeap]
  all_goals
    aesop (add safe forward removeLast_subset)

theorem pop_values (x : Int) (l r : Tree) :
    {x} + (pop (.node x l r)).values = (Tree.node x l r).values := by
  cases l with
  | empty =>
      cases r with
      | empty => simp [pop, values]
      | node b rl rr =>
          simp only [pop, sift_values, values, add_zero]
          rw [removeLast_values (.node b rl rr) (by simp)]
          rfl
  | node a ll lr =>
      cases r with
      | empty =>
          simp only [pop, sift_values, values, add_zero]
          rw [removeLast_values (.node a ll lr) (by simp)]
          rfl
      | node b rl rr =>
          simp only [pop]
          split
          · rw [sift_values]
            have h := congrArg (fun s : Multiset Int => {x} + (node a ll lr).values + s)
              (removeLast_values (.node b rl rr) (by simp))
            simpa only [values, add_assoc, add_left_comm, add_comm] using h
          · rw [sift_values]
            have h := congrArg (fun s : Multiset Int => {x} + s + (node b rl rr).values)
              (removeLast_values (.node a ll lr) (by simp))
            simpa only [values, add_assoc, add_left_comm, add_comm] using h

theorem pop_heap (t : Tree) (ht : IsHeap t) : IsHeap t.pop := by
  cases t with
  | empty => trivial
  | node x l r =>
      rcases ht with ⟨hl, hr, _, _⟩
      cases l <;> cases r <;> simp only [pop]
      · trivial
      · exact sift_heap _ _ _ trivial (removeLast_heap _ hr)
      · exact sift_heap _ _ _ (removeLast_heap _ hl) trivial
      · split
        · exact sift_heap _ _ _ hl (removeLast_heap _ hr)
        · exact sift_heap _ _ _ (removeLast_heap _ hl) hr


theorem root_upper (x : Int) (l r : Tree) (ht : IsHeap (.node x l r)) :
    ∀ z ∈ (Tree.node x l r).values, z ≤ x := by
  intro z hz
  simp only [values, Multiset.mem_add, Multiset.mem_singleton] at hz
  rcases hz with (rfl | hz) | hz
  · exact le_rfl
  · exact ht.2.2.1 z hz
  · exact ht.2.2.2 z hz

theorem pop_size (x : Int) (l r : Tree) :
    (pop (.node x l r)).size + 1 = (Tree.node x l r).size := by
  have h := congrArg Multiset.card (pop_values x l r)
  simpa [Nat.add_comm] using h

/-- The extraction-loop invariant, valid for any max heap and enough iterations. -/
theorem drain_spec (fuel : Nat) (t : Tree) (ht : IsHeap t) (hn : t.size ≤ fuel) :
    (drain fuel t : Multiset Int) = t.values ∧
      (drain fuel t).Pairwise (· ≤ ·) := by
  induction fuel generalizing t with
  | zero =>
      cases t with
      | empty => simp [drain, values]
      | node x l r => simp only [size] at hn; omega
  | succ n ih =>
      cases t with
      | empty => simp [drain, values]
      | node x l r =>
          have hp : (pop (.node x l r)).size ≤ n := by
            have := pop_size x l r
            omega
          obtain ⟨hv, hs⟩ := ih _ (pop_heap _ ht) hp
          constructor
          · simp only [drain, ← Multiset.coe_add, hv]
            change (pop (.node x l r)).values + {x} = (Tree.node x l r).values
            rw [add_comm]
            exact pop_values x l r
          · simp only [drain]
            apply List.pairwise_append.mpr
            refine ⟨hs, by simp, ?_⟩
            intro a ha b hb
            have hb' : b = x := by simpa using hb
            subst b
            apply root_upper x l r ht a
            rw [← pop_values x l r]
            apply Multiset.mem_add.mpr
            right
            rw [← hv]
            exact ha

end Tree


theorem build_values (xs : List Int) : (build_max_heap xs).values = (xs : Multiset Int) := by
  simp [build_max_heap, heapify_values, fold_insert_values, values]

theorem build_size (xs : List Int) : (build_max_heap xs).size = xs.length := by
  have h := congrArg Multiset.card (build_values xs)
  simpa using h

theorem build_heap (xs : List Int) : (build_max_heap xs).IsHeap :=
  heapify_heap _

def sorted_prop (_xs ys : List Int) : Prop := ys.Pairwise (· ≤ ·)
def permutation_prop (xs ys : List Int) : Prop := ys.Perm xs
def length_prop (xs ys : List Int) : Prop := ys.length = xs.length
def multiplicity_prop (xs ys : List Int) : Prop := ∀ z : Int, ys.count z = xs.count z
def membership_prop (xs ys : List Int) : Prop := ∀ z : Int, z ∈ ys ↔ z ∈ xs
def fixedPoint_prop (xs ys : List Int) : Prop := xs.Pairwise (· ≤ ·) → ys = xs
def idempotence_prop (_xs ys : List Int) : Prop := heapSort ys = ys
def smallInput_prop (xs ys : List Int) : Prop := xs.length ≤ 1 → ys = xs

theorem sorted_thm (xs : List Int) : sorted_prop xs (heapSort xs) := by
  exact (drain_spec xs.length _ (build_heap xs) (by rw [build_size])).2

theorem permutation_thm (xs : List Int) : permutation_prop xs (heapSort xs) := by
  apply Multiset.coe_eq_coe.mp
  exact (drain_spec xs.length _ (build_heap xs) (by rw [build_size])).1.trans (build_values xs)

theorem length_thm (xs : List Int) : length_prop xs (heapSort xs) :=
  (permutation_thm xs).length_eq

theorem multiplicity_thm (xs : List Int) : multiplicity_prop xs (heapSort xs) := by
  intro z
  exact (permutation_thm xs).count_eq z

theorem membership_thm (xs : List Int) : membership_prop xs (heapSort xs) :=
  fun _ => (permutation_thm xs).mem_iff

theorem fixedPoint_thm (xs : List Int) : fixedPoint_prop xs (heapSort xs) := by
  intro h
  exact List.eq_of_perm_of_sorted (permutation_thm xs) (sorted_thm xs) h

theorem idempotence_thm (xs : List Int) : idempotence_prop xs (heapSort xs) :=
  fixedPoint_thm (heapSort xs) (sorted_thm xs)

theorem smallInput_thm (xs : List Int) : smallInput_prop xs (heapSort xs) := by
  intro h
  apply fixedPoint_thm xs
  cases xs with
  | nil => simp
  | cons x xs =>
      cases xs with
      | nil => simp
      | cons y ys => simp at h

/-- Exact dynamic failure behavior, including a non-list input. -/
def validation_prop (input : PyInput) : Prop :=
  checkedHeapSort input = .error "Input must be List[int]" ↔ decode input = none

theorem validation_thm (input : PyInput) : validation_prop input := by
  unfold validation_prop checkedHeapSort
  cases decode input <;> simp

/-- The checked wrapper accepts every successfully decoded integer list. -/
def acceptance_prop (input : PyInput) (xs : List Int) : Prop :=
  decode input = some xs → checkedHeapSort input = .ok (heapSort xs)

theorem acceptance_thm (input : PyInput) (xs : List Int) : acceptance_prop input xs := by
  intro h
  simp [checkedHeapSort, h]

/-- Ascending order and exact multiplicities characterize the required result.
The additional conjuncts record useful consequences, including both edge cases. -/
def Post_prop (xs ys : List Int) : Prop :=
  sorted_prop xs ys ∧ permutation_prop xs ys ∧ length_prop xs ys ∧
  multiplicity_prop xs ys ∧ membership_prop xs ys ∧ fixedPoint_prop xs ys ∧
  idempotence_prop xs ys ∧ smallInput_prop xs ys


/-! ## Property-based tests
All lists of length at most five over a signed five-element alphabet are tested:
3906 inputs, including all duplicate patterns. These executable checks are
separate from (and are not used by) any theorem proof. -/

def words : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun xs => [-2, -1, 0, 1, 2].map (· :: xs)

def samples : List (List Int) := (List.range 6).flatMap words

def orderedCheck (ys : List Int) : Bool := decide (ys.Pairwise (· ≤ ·))

/-- It suffices to inspect the finite support: all other counts are zero. -/
def countCheck (xs ys : List Int) : Bool :=
  (xs ++ ys).all fun z => decide (ys.count z = xs.count z)

def memberCheck (xs ys : List Int) : Bool :=
  (xs ++ ys).all fun z => decide (z ∈ ys ↔ z ∈ xs)

def postCheck (xs ys : List Int) : Bool :=
  orderedCheck ys && decide (ys.Perm xs) && decide (ys.length = xs.length) &&
  countCheck xs ys && memberCheck xs ys &&
  (!orderedCheck xs || decide (ys = xs)) && decide (heapSort ys = ys) &&
  (decide (1 < xs.length) || decide (ys = xs))

-- PBT: sorted_prop
example : samples.all (fun xs => orderedCheck (heapSort xs)) = true := by native_decide
-- PBT: permutation_prop
example : samples.all (fun xs => decide ((heapSort xs).Perm xs)) = true := by native_decide
-- PBT: length_prop
example : samples.all (fun xs => decide ((heapSort xs).length = xs.length)) = true := by native_decide
-- PBT: multiplicity_prop, checking the entire finite support of both lists.
example : samples.all (fun xs => countCheck xs (heapSort xs)) = true := by native_decide
-- PBT: membership_prop
example : samples.all (fun xs => memberCheck xs (heapSort xs)) = true := by native_decide
-- PBT: fixedPoint_prop
example : samples.all (fun xs => !orderedCheck xs || decide (heapSort xs = xs)) = true := by native_decide
-- PBT: idempotence_prop
example : samples.all (fun xs => decide (heapSort (heapSort xs) = heapSort xs)) = true := by native_decide
-- PBT: smallInput_prop (includes all singleton samples and the empty list).
example : samples.all (fun xs => decide (1 < xs.length) || decide (heapSort xs = xs)) = true := by native_decide
-- PBT: the complete Post_prop.
example : samples.all (fun xs => postCheck xs (heapSort xs)) = true := by native_decide

def dynamicSamples : List PyInput :=
  [.notList, .list [], .list [.floating 2.5], .list [.other],
    .list [.integer 1, .floating 2.5], .list [.boolean true, .integer (-3), .boolean false]] ++
  (samples.take 200).map (fun xs => .list (xs.map PyAtom.integer)) ++
  (samples.take 200).map (fun xs => .list (xs.map PyAtom.integer ++ [.other]))

-- PBT: validation_prop, testing both sides of the exact failure equivalence.
example : dynamicSamples.all (fun input =>
    decide ((checkedHeapSort input = .error "Input must be List[int]") ↔ decode input = none)) = true := by
  native_decide
-- PBT: acceptance_prop, ranging over all successfully decoded samples.
example : dynamicSamples.all (fun input => match decode input with
    | none => true
    | some xs => decide (checkedHeapSort input = .ok (heapSort xs))) = true := by
  native_decide

-- Randomized checks supplement the exhaustive small-domain checks.
#eval Plausible.Testable.check (∀ xs : List Int, (heapSort xs).Pairwise (· ≤ ·))
#eval Plausible.Testable.check (∀ xs : List Int, (heapSort xs).Perm xs)
#eval Plausible.Testable.check (∀ (xs : List Int) (z : Int), (heapSort xs).count z = xs.count z)
#eval Plausible.Testable.check (∀ xs : List Int, postCheck xs (heapSort xs) = true)
#eval samples.length

/-! ## Correctness -/

theorem correctness_thm (xs : List Int) : Pre xs → Post_prop xs (heapSort xs) := by
  intro _
  exact ⟨sorted_thm xs, permutation_thm xs, length_thm xs, multiplicity_thm xs,
    membership_thm xs, fixedPoint_thm xs, idempotence_thm xs, smallInput_thm xs⟩

/-- Total correctness of the dynamic interface, including the exceptional case. -/
theorem checked_correctness_thm (input : PyInput) :
    match decode input with
    | none => checkedHeapSort input = .error "Input must be List[int]"
    | some xs => checkedHeapSort input = .ok (heapSort xs) ∧ Post_prop xs (heapSort xs) := by
  cases h : decode input with
  | none => simp [checkedHeapSort, h]
  | some xs => exact ⟨acceptance_thm input xs h, correctness_thm xs trivial⟩

/-! ## Imperative implementation
The mutable state consists of a heap and the sorted suffix. Each loop iteration
places the old maximum at the front of that suffix, just as Python places it
in the last unoccupied array slot. Both construction and extraction use for-loops.
-/

def extractionStep (state : Tree × List Int) : Tree × List Int :=
  match state.1 with
  | .empty => state
  | .node x l r => ((Tree.node x l r).pop, x :: state.2)

def heapSortImperative (xs : List Int) : List Int := Id.run do
  let mut heap := Tree.empty
  for x in xs do
    heap := heap.insert x
  heap := heap.heapify
  let mut state : Tree × List Int := (heap, [])
  for _ in List.range xs.length do
    state := extractionStep state
  return state.2

def checkedHeapSortImperative (input : PyInput) : Except String (List Int) :=
  match decode input with
  | none => .error "Input must be List[int]"
  | some xs => .ok (heapSortImperative xs)

-- All of the supplied integer regression cases, run against the imperative code.
def regressionCases : List (List Int × List Int) :=
  [([3, 1, 2], [1, 2, 3]), ([1, 2, 3], [1, 2, 3]), ([2, 1, 3], [1, 2, 3]),
   ([], []), ([1], [1]), ([5, 2, 4, 6, 1, 3], [1, 2, 3, 4, 5, 6]),
   ([9, 8, 7, 6, 5, 4, 3, 2, 1], [1, 2, 3, 4, 5, 6, 7, 8, 9]),
   ([2, 6, 4, 3, 1, 5], [1, 2, 3, 4, 5, 6]), ([2, 1], [1, 2]), ([1, 2], [1, 2]),
   ([3, 1, 4, 1, 2, 3], [1, 1, 2, 3, 3, 4]), ([5, 5, 5, 5, 5], [5, 5, 5, 5, 5]),
   ([1, 2, 3, 4, 5], [1, 2, 3, 4, 5]), ([5, 4, 3, 2, 1], [1, 2, 3, 4, 5]),
   ([3, 7, 1, 9, 2, 8, 4, 6, 5], [1, 2, 3, 4, 5, 6, 7, 8, 9]),
   ([64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42], [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90])]

example : regressionCases.all (fun p => decide (heapSortImperative p.1 = p.2)) = true := by native_decide
example : heapSortImperative [-3, 0, -1, -3, 2] = [-3, -3, -1, 0, 2] := by native_decide
example : checkedHeapSortImperative (.list [.integer 1, .floating 2.5]) =
    .error "Input must be List[int]" := by native_decide
example : samples.all (fun xs => postCheck xs (heapSortImperative xs)) = true := by native_decide
example : samples.all (fun xs => decide (heapSort xs = heapSortImperative xs)) = true := by native_decide
#eval heapSortImperative [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

@[simp] theorem drain_empty (n : Nat) : Tree.drain n .empty = [] := by
  cases n <;> rfl

/-- Accumulator invariant for the imperative extraction loop; it holds even
for arbitrary non-heap trees and arbitrary initial suffixes. -/
theorem extraction_fold (ticks : List Nat) (t : Tree) (acc : List Int) :
    (ticks.foldl (fun state _ => extractionStep state) (t, acc)).2 =
      Tree.drain ticks.length t ++ acc := by
  induction ticks generalizing t acc with
  | nil => rfl
  | cons i ticks ih =>
      cases t with
      | empty =>
          simp only [List.foldl_cons]
          change (ticks.foldl (fun state _ => extractionStep state) (.empty, acc)).2 = _
          rw [ih]
          simp
      | node x l r =>
          simp only [List.foldl_cons]
          change (ticks.foldl (fun state _ => extractionStep state)
            ((Tree.node x l r).pop, x :: acc)).2 = _
          rw [ih]
          simp [Tree.drain, List.append_assoc]

/-- Universal functional/imperative equivalence, not a test-based claim. -/
theorem equivalence_thm (xs : List Int) : heapSort xs = heapSortImperative xs := by
  simp [heapSortImperative, heapSort, build_max_heap, extraction_fold]

theorem checked_equivalence_thm (input : PyInput) :
    checkedHeapSort input = checkedHeapSortImperative input := by
  unfold checkedHeapSort checkedHeapSortImperative
  cases decode input with
  | none => rfl
  | some xs => simp only [equivalence_thm]

theorem imperative_correctness_thm (xs : List Int) :
    Pre xs → Post_prop xs (heapSortImperative xs) := by
  rw [← equivalence_thm]
  exact correctness_thm xs

end heap_sort
