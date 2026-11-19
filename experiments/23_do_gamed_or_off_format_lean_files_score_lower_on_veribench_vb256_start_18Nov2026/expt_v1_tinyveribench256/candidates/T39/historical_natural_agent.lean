import Mathlib
namespace Agent

/-!
# Heap sort for integer lists

A functional, representation-independent translation of the Python heap sort.
The array's max-heap is represented by a binary meldable max-heap: `meld`
repairs the heap by selecting the larger root and descending into a child.
Building the heap and repeatedly extracting its maximum gives the same ascending
integer list as the array algorithm. No library sorting routine is used.
The mutable version below uses the same heap operations with explicit heap and
output state. Lists are immutable, so returning a list cannot mutate the input.

`Int` models Python's unbounded integers. `Input` additionally models dynamic
validation: non-lists and non-integer elements produce the stated ValueError.
Python booleans (which are instances of `int`) are accepted as 0 and 1 in this
integer-valued model. Other Python objects are abstracted by an invalid tag.
-/

namespace heap_sort

deriving instance DecidableEq for Except

inductive Heap where
  | empty
  | node (key : Int) (left right : Heap)
  deriving Repr, DecidableEq

namespace Heap

def size : Heap → Nat
  | .empty => 0
  | .node _ l r => 1 + l.size + r.size

def contents : Heap → List Int
  | .empty => []
  | .node x l r => x :: (l.contents ++ r.contents)

/-- Meld two max-heaps, exchanging children on each descent (a skew heap). -/
def meld : Heap → Heap → Heap
  | .empty, h => h
  | h, .empty => h
  | .node a l r, .node b s t =>
    if b ≤ a then .node a (meld r (.node b s t)) l
    else .node b (meld (.node a l r) t) s
termination_by h₁ h₂ => h₁.size + h₂.size
decreasing_by all_goals simp_all [size]

def insert (x : Int) (h : Heap) : Heap := meld (.node x .empty .empty) h

/-- Every node dominates every element of both of its subheaps. -/
def Valid : Heap → Prop
  | .empty => True
  | .node x l r => l.Valid ∧ r.Valid ∧ ∀ y ∈ l.contents ++ r.contents, y ≤ x

end Heap

open Heap

def build : List Int → Heap
  | [] => .empty
  | x :: xs => (build xs).insert x

/-- The fuel is the number of heap elements. Maxima are placed at the right. -/
def drain : Nat → Heap → List Int
  | 0, _ => []
  | _ + 1, .empty => []
  | n + 1, .node x l r => drain n (meld l r) ++ [x]

def heapSort (xs : List Int) : List Int := drain xs.length (build xs)

inductive Atom where
  | integer (value : Int)
  | boolean (value : Bool)
  | other (description : String)
  deriving Repr, DecidableEq

inductive Input where
  | list (elements : List Atom)
  | other (description : String)
  deriving Repr, DecidableEq

def Atom.toInt : Atom → Option Int
  | .integer n => some n
  | .boolean b => some (if b then 1 else 0)
  | .other _ => none

def decodeElements : List Atom → Option (List Int)
  | [] => some []
  | x :: xs => do
    let n ← x.toInt
    let ns ← decodeElements xs
    pure (n :: ns)

def decode : Input → Option (List Int)
  | .list xs => decodeElements xs
  | .other _ => none

def valueError : String := "ValueError: Input must be List[int]"

def checkedHeapSort (input : Input) : Except String (List Int) :=
  match decode input with
  | none => .error valueError
  | some xs => .ok (heapSort xs)

-- Unit tests: all of the integer examples from the Python source.
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
example : heapSort [-3, 2, -1, 0, -3] = [-3, -3, -1, 0, 2] := by native_decide
example : checkedHeapSort (.list [.integer 1, .other "2.5"]) = .error valueError := by native_decide
example : checkedHeapSort (.other "not a list") = .error valueError := by native_decide
example : checkedHeapSort (.list [.boolean true, .integer (-1), .boolean false]) =
    .ok [-1, 0, 1] := by native_decide
#eval heapSort [3, 1, 2]
#eval checkedHeapSort (.list [.integer 1, .other "2.5"])

/-- The typed core accepts exactly integer lists; its type discharges validation. -/
def Pre (_xs : List Int) : Prop := True

def Atom.isInt : Atom → Bool
  | .integer _ => true
  | .boolean _ => true
  | .other _ => false

/-- Dynamic version of Python's `pre`, independent of sorting and decoding. -/
def pre : Input → Bool
  | .list xs => xs.all Atom.isInt
  | .other _ => false

def InputPre (input : Input) : Prop := pre input = true

-- Kernel-checked heap invariants and sorting properties follow here.

namespace Heap

theorem meld_perm (h k : Heap) : (meld h k).contents.Perm (h.contents ++ k.contents) := by
  fun_induction meld h k with
  | case1 => simp [contents]
  | case2 => simp [contents]
  | case3 a l r b s t hab ih =>
    apply List.perm_iff_count.mpr
    intro z
    have hz := ih.count_eq z
    simp only [contents, List.count_cons, List.count_append] at hz ⊢
    omega
  | case4 a l r b s t hab ih =>
    apply List.perm_iff_count.mpr
    intro z
    have hz := ih.count_eq z
    simp only [contents, List.count_cons, List.count_append] at hz ⊢
    omega

theorem meld_bound (h k : Heap) (x : Int)
    (hh : ∀ y ∈ h.contents, y ≤ x) (hk : ∀ y ∈ k.contents, y ≤ x) :
    ∀ y ∈ (meld h k).contents, y ≤ x := by
  intro y hy
  rcases List.mem_append.mp ((meld_perm h k).mem_iff.mp hy) with hy | hy
  · exact hh y hy
  · exact hk y hy

theorem meld_valid (h k : Heap) (hh : h.Valid) (hk : k.Valid) : (meld h k).Valid := by
  revert hh hk
  fun_induction meld h k with
  | case1 => exact fun _ hk => hk
  | case2 => exact fun hh _ => hh
  | case3 a l r b s t hab ih =>
    intro hh hk
    refine ⟨ih hh.2.1 hk, hh.1, ?_⟩
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · apply meld_bound r (.node b s t) a ?_ ?_ y hy
      · intro z hz
        exact hh.2.2 z (List.mem_append.mpr (.inr hz))
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hab
        · exact le_trans (hk.2.2 z hz) hab
    · exact hh.2.2 y (List.mem_append.mpr (.inl hy))
  | case4 a l r b s t hab ih =>
    intro hh hk
    have hab' : a ≤ b := by omega
    refine ⟨ih hh hk.2.1, hk.1, ?_⟩
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · apply meld_bound (.node a l r) t b ?_ ?_ y hy
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hab'
        · exact le_trans (hh.2.2 z hz) hab'
      · intro z hz
        exact hk.2.2 z (List.mem_append.mpr (.inr hz))
    · exact hk.2.2 y (List.mem_append.mpr (.inl hy))

theorem length_contents (h : Heap) : h.contents.length = h.size := by
  induction h <;> simp_all [contents, size, Nat.add_comm, Nat.add_assoc]

theorem meld_size (h k : Heap) : (meld h k).size = h.size + k.size := by
  have hp := (meld_perm h k).length_eq
  simpa only [List.length_append, length_contents] using hp

end Heap

theorem build_perm (xs : List Int) : (build xs).contents.Perm xs := by
  induction xs with
  | nil => simp [build, contents]
  | cons x xs ih =>
    have hp := meld_perm (.node x .empty .empty) (build xs)
    simpa [build, Heap.insert, contents] using hp.trans (by simpa [contents] using ih.cons x)

theorem build_valid (xs : List Int) : (build xs).Valid := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    exact meld_valid _ _ (by simp [Valid, contents]) ih

theorem build_size (xs : List Int) : (build xs).size = xs.length := by
  simpa only [length_contents] using (build_perm xs).length_eq

/-- The fuel cannot discard elements: it bounds the heap's size. -/
theorem drain_perm (n : Nat) (h : Heap) (hn : h.size ≤ n) :
    (drain n h).Perm h.contents := by
  induction n generalizing h with
  | zero =>
    cases h with
    | empty => simp [drain, contents]
    | node x l r => simp [size] at hn
  | succ n ih =>
    cases h with
    | empty => simp [drain, contents]
    | node x l r =>
      have hs : (meld l r).size ≤ n := by
        rw [meld_size]
        simp only [size] at hn
        omega
      have hp := (ih (meld l r) hs).trans (meld_perm l r)
      exact (hp.append_right [x]).trans List.perm_append_comm

theorem drain_sorted (n : Nat) (h : Heap) (hn : h.size ≤ n) (hv : h.Valid) :
    (drain n h).Pairwise (· ≤ ·) := by
  induction n generalizing h with
  | zero => simp [drain]
  | succ n ih =>
    cases h with
    | empty => simp [drain]
    | node x l r =>
      have hs : (meld l r).size ≤ n := by
        rw [meld_size]
        simp only [size] at hn
        omega
      rw [drain]
      refine List.pairwise_append.mpr ⟨ih _ hs (meld_valid l r hv.1 hv.2.1), by simp, ?_⟩
      intro y hy z hz
      have hz' : z = x := by simpa using hz
      subst z
      exact hv.2.2 y ((meld_perm l r).mem_iff.mp ((drain_perm n _ hs).mem_iff.mp hy))

/-- Ascending order, including equality between repeated values. -/
def sorted_prop (xs : List Int) : Prop := (heapSort xs).Pairwise (· ≤ ·)

theorem sorted_thm (xs : List Int) : sorted_prop xs :=
  drain_sorted xs.length (build xs) (by rw [build_size]) (build_valid xs)

/-- A permutation preserves all occurrences, not merely the set of values. -/
def permutation_prop (xs : List Int) : Prop := (heapSort xs).Perm xs

theorem permutation_thm (xs : List Int) : permutation_prop xs :=
  (drain_perm xs.length (build xs) (by rw [build_size])).trans (build_perm xs)

def length_prop (xs : List Int) : Prop := (heapSort xs).length = xs.length

theorem length_thm (xs : List Int) : length_prop xs := (permutation_thm xs).length_eq

def multiplicity_prop (xs : List Int) (x : Int) : Prop :=
  (heapSort xs).count x = xs.count x

theorem multiplicity_thm (xs : List Int) (x : Int) : multiplicity_prop xs x :=
  (permutation_thm xs).count_eq x

def membership_prop (xs : List Int) (x : Int) : Prop := x ∈ heapSort xs ↔ x ∈ xs

theorem membership_thm (xs : List Int) (x : Int) : membership_prop xs x :=
  (permutation_thm xs).mem_iff

/-- A sorted permutation of the input is uniquely the returned result. -/
def unique_prop (xs ys : List Int) : Prop :=
  ys.Pairwise (· ≤ ·) → ys.Perm xs → heapSort xs = ys

theorem unique_thm (xs ys : List Int) : unique_prop xs ys := by
  intro hs hp
  exact List.eq_of_perm_of_sorted ((permutation_thm xs).trans hp.symm) (sorted_thm xs) hs

def fixed_prop (xs : List Int) : Prop := xs.Pairwise (· ≤ ·) → heapSort xs = xs

theorem fixed_thm (xs : List Int) : fixed_prop xs := by
  intro hs
  exact unique_thm xs xs hs (List.Perm.refl xs)

def idempotent_prop (xs : List Int) : Prop := heapSort (heapSort xs) = heapSort xs

theorem idempotent_thm (xs : List Int) : idempotent_prop xs :=
  fixed_thm (heapSort xs) (sorted_thm xs)

def edge_prop (xs : List Int) : Prop := xs.length ≤ 1 → heapSort xs = xs

theorem edge_thm (xs : List Int) : edge_prop xs := by
  intro h
  apply fixed_thm
  match xs with
  | [] => simp
  | [x] => simp
  | x :: y :: xs => simp at h

theorem decodeElements_isSome (xs : List Atom) :
    (decodeElements xs).isSome = xs.all Atom.isInt := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> cases he : decodeElements xs <;>
      simp_all [decodeElements, Atom.toInt, Atom.isInt]

theorem input_pre_thm (input : Input) : (decode input).isSome = pre input := by
  cases input with
  | list xs => exact decodeElements_isSome xs
  | other _ => rfl

/-- Exact dynamic rejection behavior, and successful execution on decoded integers. -/
def validation_prop (input : Input) : Prop :=
  (¬InputPre input ↔ checkedHeapSort input = .error valueError) ∧
  ∀ xs, decode input = some xs → checkedHeapSort input = .ok (heapSort xs)

theorem validation_thm (input : Input) : validation_prop input := by
  unfold validation_prop InputPre checkedHeapSort
  rw [← input_pre_thm]
  cases h : decode input <;> simp

/-- The full typed sorting contract. Multiplicity and membership are also proved
separately for an arbitrary queried integer, and follow from the permutation. -/
def Post_prop (xs : List Int) : Prop :=
  sorted_prop xs ∧ permutation_prop xs ∧ length_prop xs ∧
  fixed_prop xs ∧ idempotent_prop xs ∧ edge_prop xs


/-! ## Bounded property-based tests

`smallLists n` exhaustively enumerates every list of length at most `n` over
{-2,-1,0,1,2}. These are evidence, separate from the universal proofs above.
Every `_prop` has an executable test below; the queried values also include
integers outside the generator's alphabet.
-/

def alphabet : List Int := [-2, -1, 0, 1, 2]

def smallLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun x => (smallLists n).map (x :: ·))

def samples : List (List Int) := smallLists 5

def queries : List Int := [-4, -3, -2, -1, 0, 1, 2, 3, 4]

-- sorted_prop
example : samples.all (fun xs => decide ((heapSort xs).Pairwise (· ≤ ·))) = true := by
  native_decide
-- permutation_prop
example : samples.all (fun xs => decide ((heapSort xs).Perm xs)) = true := by
  native_decide
-- length_prop
example : samples.all (fun xs => decide ((heapSort xs).length = xs.length)) = true := by
  native_decide
-- multiplicity_prop
example : samples.all (fun xs => queries.all
    (fun x => decide ((heapSort xs).count x = xs.count x))) = true := by
  native_decide
-- membership_prop
example : samples.all (fun xs => queries.all
    (fun x => decide (x ∈ heapSort xs ↔ x ∈ xs))) = true := by
  native_decide
-- unique_prop: exhaustive pairs include all sorted permutations, not just random
-- pairs for which the antecedent is usually false.
example : (smallLists 3).all (fun xs => (smallLists 3).all (fun ys =>
    decide (ys.Pairwise (· ≤ ·) → ys.Perm xs → heapSort xs = ys))) = true := by
  native_decide
-- fixed_prop
example : samples.all (fun xs => decide
    (xs.Pairwise (· ≤ ·) → heapSort xs = xs)) = true := by
  native_decide
-- idempotent_prop
example : samples.all (fun xs => decide (heapSort (heapSort xs) = heapSort xs)) = true := by
  native_decide
-- edge_prop (includes every generated singleton and the empty list).
example : samples.all (fun xs => decide (xs.length ≤ 1 → heapSort xs = xs)) = true := by
  native_decide

/-- Executable form of the conjunction in `Post_prop`. -/
def postCheck (xs : List Int) : Bool :=
  decide ((heapSort xs).Pairwise (· ≤ ·)) &&
  decide ((heapSort xs).Perm xs) &&
  decide ((heapSort xs).length = xs.length) &&
  decide (xs.Pairwise (· ≤ ·) → heapSort xs = xs) &&
  decide (heapSort (heapSort xs) = heapSort xs) &&
  decide (xs.length ≤ 1 → heapSort xs = xs)

-- Post_prop
example : samples.all postCheck = true := by native_decide
#eval (samples.length, samples.all postCheck)

/-- All short lists of representative valid and invalid Python atom tags. -/
def atomLists : Nat → List (List Atom)
  | 0 => [[]]
  | n + 1 => [] ::
    ([Atom.integer (-1), .integer 0, .integer 1, .boolean false,
      .boolean true, .other "2.5", .other "string"].flatMap
      (fun a => (atomLists n).map (a :: ·)))

def inputSamples : List Input :=
  .other "tuple" :: .other "None" :: (atomLists 3).map Input.list

/-- Executable counterpart of `validation_prop`: for a successful decode only
that decoded list can witness its universally quantified implication. -/
def validationCheck (input : Input) : Bool :=
  decide (pre input ≠ true ↔ checkedHeapSort input = .error valueError) &&
  match decode input with
  | none => true
  | some xs => decide (checkedHeapSort input = .ok (heapSort xs))

-- validation_prop
example : inputSamples.all validationCheck = true := by native_decide
#eval (inputSamples.length, inputSamples.all validationCheck)

/-- The executable postcondition test is exactly the stated conjunction. -/
theorem postCheck_iff (xs : List Int) : postCheck xs = true ↔ Post_prop xs := by
  simp only [postCheck, Bool.and_eq_true, decide_eq_true_eq, Post_prop,
    sorted_prop, permutation_prop, length_prop, fixed_prop, idempotent_prop,
    edge_prop, and_assoc]

/-- The finite executable validation check retains the universal specification. -/
theorem validationCheck_iff (input : Input) :
    validationCheck input = true ↔ validation_prop input := by
  cases hd : decode input <;>
    simp [validationCheck, validation_prop, InputPre, checkedHeapSort, hd]

/-! ## Correctness -/

theorem correctness_thm (xs : List Int) (_h : Pre xs) : Post_prop xs :=
  ⟨sorted_thm xs, permutation_thm xs, length_thm xs,
    fixed_thm xs, idempotent_thm xs, edge_thm xs⟩

/-- The checked entry point returns a sorted permutation whenever Python's
actual dynamic precondition holds. Invalid inputs are covered by validation_thm. -/
theorem checked_correctness_thm (input : Input) (h : InputPre input) :
    ∃ xs ys, decode input = some xs ∧ checkedHeapSort input = .ok ys ∧
      ys.Pairwise (· ≤ ·) ∧ ys.Perm xs ∧ Post_prop xs := by
  have hp : (decode input).isSome = true := (input_pre_thm input).trans h
  cases hd : decode input with
  | none => simp [hd] at hp
  | some xs =>
    exact ⟨xs, heapSort xs, rfl, by simp [checkedHeapSort, hd],
      sorted_thm xs, permutation_thm xs, correctness_thm xs trivial⟩


/-! ## Imperative implementation

Both loops use actual mutable state in `Id.run`: heap construction updates the
heap, and extraction updates both the remaining heap and the sorted suffix.
Prepending each successive maximum places it immediately before the previously
extracted (greater) elements, just as the Python array's sorted suffix grows left.
-/

def insertLoop (xs : List Int) (initial : Heap) : Heap := Id.run do
  let mut heap := initial
  for x in xs do
    heap := heap.insert x
  return heap

def buildImperative (xs : List Int) : Heap := insertLoop xs.reverse .empty

def drainLoop (ticks : List Nat) (initial : Heap) (suffix : List Int) : List Int := Id.run do
  let mut heap := initial
  let mut output := suffix
  for _ in ticks do
    match heap with
    | .empty => pure ()
    | .node x l r =>
      heap := meld l r
      output := x :: output
  return output

def heapSortImperative (xs : List Int) : List Int := Id.run do
  let mut heap := buildImperative xs
  let mut output : List Int := []
  for _ in List.range xs.length do
    match heap with
    | .empty => pure ()
    | .node x l r =>
      heap := meld l r
      output := x :: output
  return output

def checkedHeapSortImperative (input : Input) : Except String (List Int) :=
  match decode input with
  | none => .error valueError
  | some xs => .ok (heapSortImperative xs)

-- Imperative tests, including all the original positive examples.
def unitCases : List (List Int × List Int) :=
  [([3, 1, 2], [1, 2, 3]), ([1, 2, 3], [1, 2, 3]), ([2, 1, 3], [1, 2, 3]),
   ([], []), ([1], [1]), ([5, 2, 4, 6, 1, 3], [1, 2, 3, 4, 5, 6]),
   ([9, 8, 7, 6, 5, 4, 3, 2, 1], [1, 2, 3, 4, 5, 6, 7, 8, 9]),
   ([2, 6, 4, 3, 1, 5], [1, 2, 3, 4, 5, 6]), ([2, 1], [1, 2]), ([1, 2], [1, 2]),
   ([3, 1, 4, 1, 2, 3], [1, 1, 2, 3, 3, 4]), ([5, 5, 5, 5, 5], [5, 5, 5, 5, 5]),
   ([1, 2, 3, 4, 5], [1, 2, 3, 4, 5]), ([5, 4, 3, 2, 1], [1, 2, 3, 4, 5]),
   ([3, 7, 1, 9, 2, 8, 4, 6, 5], [1, 2, 3, 4, 5, 6, 7, 8, 9]),
   ([64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42],
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90])]

example : unitCases.all (fun p => decide (heapSortImperative p.1 = p.2)) = true := by
  native_decide
example : checkedHeapSortImperative (.list [.integer 1, .other "2.5"]) =
    .error valueError := by native_decide
example : samples.all (fun xs => decide (heapSort xs = heapSortImperative xs)) = true := by
  native_decide
example : inputSamples.all (fun input => decide
    (checkedHeapSort input = checkedHeapSortImperative input)) = true := by
  native_decide
#eval heapSortImperative [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
#eval checkedHeapSortImperative (.list [.integer 1, .other "2.5"])

/-! ## Kernel-checked loop invariants and equivalence -/

theorem insertLoop_eq (xs : List Int) (h : Heap) :
    insertLoop xs h = xs.foldl (fun h x => h.insert x) h := by
  simp [insertLoop, List.forIn_pure_yield_eq_foldl]

theorem build_foldr (xs : List Int) : xs.foldr Heap.insert .empty = build xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [build, ih]

theorem build_equiv (xs : List Int) : buildImperative xs = build xs := by
  rw [buildImperative, insertLoop_eq, List.foldl_reverse]
  exact build_foldr xs

@[simp] theorem drain_empty (n : Nat) : drain n .empty = [] := by
  cases n <;> rfl

/-- The loop's sorted suffix is an arbitrary accumulator, not only the empty list. -/
theorem drainLoop_eq (ticks : List Nat) (h : Heap) (suffix : List Int) :
    drainLoop ticks h suffix = drain ticks.length h ++ suffix := by
  induction ticks generalizing h suffix with
  | nil => rfl
  | cons k ticks ih =>
    cases h with
    | empty =>
      simpa [drainLoop, List.forIn_cons] using ih .empty suffix
    | node x l r =>
      simpa [drainLoop, List.forIn_cons, drain, List.append_assoc] using
        ih (meld l r) (x :: suffix)

/-- Exact equality for every integer list, without any bounded-size hypothesis. -/
theorem equivalence_thm (xs : List Int) : heapSort xs = heapSortImperative xs := by
  change heapSort xs = drainLoop (List.range xs.length) (buildImperative xs) []
  rw [drainLoop_eq, build_equiv, List.length_range, List.append_nil]
  rfl

theorem checked_equivalence_thm (input : Input) :
    checkedHeapSort input = checkedHeapSortImperative input := by
  unfold checkedHeapSort checkedHeapSortImperative
  cases decode input with
  | none => rfl
  | some xs => exact congrArg Except.ok (equivalence_thm xs)

-- These commands audit the universal proofs, not the native-decide examples.
#print axioms correctness_thm
#print axioms checked_correctness_thm
#print axioms equivalence_thm
#print axioms checked_equivalence_thm

end heap_sort
end Agent
