import Mathlib
namespace Agent

/-!
# Python merge sort on integer lists

The functional program splits at `length / 2`, recursively sorts the contiguous
halves, and merges them with a left-biased `≤` comparison. Integers are unbounded
Lean `Int`s. Lists are immutable, so returning a base-case list has the same
value semantics as Python's `copy`. A checked boundary below models `ValueError`
for non-lists and non-integer elements (including Python's bool-as-int rule).
-/

namespace merge_sort

deriving instance DecidableEq for Except

/-- The two-pointer merge, expressed by consuming the unprocessed suffixes. -/
def merge (left right : List Int) : List Int :=
  List.merge left right (fun a b => decide (a ≤ b))

/-- Contiguous-half merge sort, exactly as in the source. -/
def mergeSort (xs : List Int) : List Int :=
  if h : xs.length ≤ 1 then xs
  else
    let mid := xs.length / 2
    merge (mergeSort (xs.take mid)) (mergeSort (xs.drop mid))
termination_by xs.length
decreasing_by
  · simp only [List.length_take]
    have : xs.length / 2 < xs.length := Nat.div_lt_self (by omega) (by omega)
    omega
  · simp only [List.length_drop]
    have : 0 < xs.length / 2 := Nat.div_pos (by omega) (by omega)
    omega

/-- Values relevant to Python's `isinstance(x, int)` test. All other Python
objects are represented by `other`; their contents cannot affect this program. -/
inductive Element where
  | integer : Int → Element
  | boolean : Bool → Element
  | other : Element
  deriving Repr, DecidableEq

inductive Input where
  | list : List Element → Input
  | nonList : Input
  deriving Repr, DecidableEq

/-- Python's `isinstance(x, int)`, including its Boolean subclass. -/
def elementIsInt : Element → Bool
  | .integer _ => true
  | .boolean _ => true
  | .other => false

/-- The source precheck, before decoding any values. -/
def pre : Input → Bool
  | .list xs => xs.all elementIsInt
  | .nonList => false

-- Booleans are observed by their integer values, just as in Python's numeric
-- comparisons and list equality. Object identity is not part of this model.
def decodeElement : Element → Option Int
  | .integer n => some n
  | .boolean b => some (if b then 1 else 0)
  | .other => none

def decode : Input → Option (List Int)
  | .list xs => xs.mapM decodeElement
  | .nonList => none

def checkedMergeSort (input : Input) : Except String (List Int) :=
  match decode input with
  | some xs => .ok (mergeSort xs)
  | none => .error "ValueError: Input must be List[int]"

/-- All integer examples from the Python test suite, plus signed integers. -/
def unitCases : List (List Int × List Int) :=
  [([3, 1, 2], [1, 2, 3]),
   ([1, 2, 3], [1, 2, 3]),
   ([2, 1, 3], [1, 2, 3]),
   ([], []), ([1], [1]),
   ([5, 2, 4, 6, 1, 3], [1, 2, 3, 4, 5, 6]),
   ([9, 8, 7, 6, 5, 4, 3, 2, 1], [1, 2, 3, 4, 5, 6, 7, 8, 9]),
   ([2, 6, 4, 3, 1, 5], [1, 2, 3, 4, 5, 6]),
   ([2, 1], [1, 2]), ([1, 2], [1, 2]),
   ([3, 1, 4, 1, 2, 3], [1, 1, 2, 3, 3, 4]),
   ([5, 5, 5, 5, 5], [5, 5, 5, 5, 5]),
   ([1, 2, 3, 4, 5], [1, 2, 3, 4, 5]),
   ([5, 4, 3, 2, 1], [1, 2, 3, 4, 5]),
   ([3, 7, 1, 9, 2, 8, 4, 6, 5], [1, 2, 3, 4, 5, 6, 7, 8, 9]),
   ([64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42],
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90]),
   ([-3, 0, -1, -3, 2], [-3, -3, -1, 0, 2])]

example : mergeSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : mergeSort [] = [] := by native_decide
example : mergeSort [1] = [1] := by native_decide
example : unitCases.all (fun t => mergeSort t.1 == t.2) = true := by native_decide
-- `other` here stands for the source's 2.5, which is not an integer.
example : checkedMergeSort (.list [.integer 1, .other]) =
    .error "ValueError: Input must be List[int]" := by native_decide
example : checkedMergeSort .nonList =
    .error "ValueError: Input must be List[int]" := by native_decide
example : checkedMergeSort (.list [.boolean true, .integer (-2), .boolean false]) =
    .ok [-2, 0, 1] := by native_decide
#eval mergeSort [3, 1, 2]
#eval mergeSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
#eval checkedMergeSort (.list [.integer 1, .other])

/-- Typed integer lists satisfy the source precondition by construction. -/
def Pre (_xs : List Int) : Prop := True

/-- The actual run-time validation predicate on the untyped boundary. -/
def InputPre (input : Input) : Prop := pre input = true

/-- Successful decoding is exactly the source's list-and-integer check. -/
theorem decode_isSome (input : Input) : (decode input).isSome = pre input := by
  cases input with
  | nonList => rfl
  | list xs =>
    change (xs.mapM decodeElement).isSome = xs.all elementIsInt
    induction xs with
    | nil => rfl
    | cons e es ih =>
      cases ht : es.mapM decodeElement <;>
        cases e <;> simp_all [decodeElement, elementIsInt, List.mapM_cons]

/-- The typed core is the restriction of the checked boundary to integer lists. -/
theorem decode_integer_list (xs : List Int) :
    decode (.list (xs.map Element.integer)) = some xs := by
  change (xs.map Element.integer).mapM decodeElement = some xs
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.mapM_cons, decodeElement, ih]

theorem typed_input_valid (xs : List Int) : InputPre (.list (xs.map Element.integer)) := by
  unfold InputPre
  rw [← decode_isSome, decode_integer_list]
  rfl

theorem checked_integer_list (xs : List Int) :
    checkedMergeSort (.list (xs.map Element.integer)) = .ok (mergeSort xs) := by
  simp [checkedMergeSort, decode_integer_list]

/-- Merge preserves sortedness, with equality resolved in favor of the left. -/
theorem merge_sorted (left right : List Int)
    (hl : left.Pairwise (· ≤ ·)) (hr : right.Pairwise (· ≤ ·)) :
    (merge left right).Pairwise (· ≤ ·) := by
  have ht : ∀ a b c : Int, decide (a ≤ b) = true →
      decide (b ≤ c) = true → decide (a ≤ c) = true := by
    simp only [decide_eq_true_eq]
    exact fun _ _ _ => le_trans
  have htotal : ∀ a b : Int, (decide (a ≤ b) || decide (b ≤ a)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total
  simpa only [merge, decide_eq_true_eq] using
    (List.sorted_merge ht htotal left right
      (by simpa only [decide_eq_true_eq] using hl)
      (by simpa only [decide_eq_true_eq] using hr))

/-- Simultaneous recursive invariant of the algorithm. -/
theorem sort_invariants (xs : List Int) :
    (mergeSort xs).Pairwise (· ≤ ·) ∧ (mergeSort xs).Perm xs := by
  rw [mergeSort]
  split_ifs with h
  · constructor
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      omega
    · exact List.Perm.refl _
  · dsimp only
    obtain ⟨hl, pl⟩ := sort_invariants (xs.take (xs.length / 2))
    obtain ⟨hr, pr⟩ := sort_invariants (xs.drop (xs.length / 2))
    constructor
    · exact merge_sorted _ _ hl hr
    · apply (List.merge_perm_append (fun a b : Int => decide (a ≤ b))).trans
      simpa only [List.take_append_drop] using pl.append pr
termination_by xs.length
decreasing_by
  · simp only [List.length_take]
    have : xs.length / 2 < xs.length := Nat.div_lt_self (by omega) (by omega)
    omega
  · simp only [List.length_drop]
    have : 0 < xs.length / 2 := Nat.div_pos (by omega) (by omega)
    omega

def sorted_prop (xs : List Int) : Prop := (mergeSort xs).Pairwise (· ≤ ·)
theorem sorted_thm (xs : List Int) : sorted_prop xs := (sort_invariants xs).1

def permutation_prop (xs : List Int) : Prop := (mergeSort xs).Perm xs
theorem permutation_thm (xs : List Int) : permutation_prop xs := (sort_invariants xs).2

def length_prop (xs : List Int) : Prop := (mergeSort xs).length = xs.length
theorem length_thm (xs : List Int) : length_prop xs := (permutation_thm xs).length_eq

/-- Every integer's multiplicity, not just membership, is preserved. -/
def counts_prop (xs : List Int) (x : Int) : Prop :=
  (mergeSort xs).count x = xs.count x
theorem counts_thm (xs : List Int) (x : Int) : counts_prop xs x :=
  (permutation_thm xs).count_eq x

def membership_prop (xs : List Int) (x : Int) : Prop :=
  x ∈ mergeSort xs ↔ x ∈ xs
theorem membership_thm (xs : List Int) (x : Int) : membership_prop xs x :=
  (permutation_thm xs).mem_iff

def baseCase_prop (xs : List Int) : Prop := xs.length ≤ 1 → mergeSort xs = xs
theorem baseCase_thm (xs : List Int) : baseCase_prop xs := by
  intro h
  rw [mergeSort, dif_pos h]

/-- This also specifies the unique correct result, independent of algorithm. -/
theorem unique_sorted_result (xs ys : List Int)
    (hs : ys.Pairwise (· ≤ ·)) (hp : ys.Perm xs) : mergeSort xs = ys := by
  exact List.eq_of_perm_of_sorted ((permutation_thm xs).trans hp.symm)
    (sorted_thm xs) hs

def alreadySorted_prop (xs : List Int) : Prop :=
  xs.Pairwise (· ≤ ·) → mergeSort xs = xs
theorem alreadySorted_thm (xs : List Int) : alreadySorted_prop xs := by
  intro hs
  exact unique_sorted_result xs xs hs (List.Perm.refl _)

def idempotent_prop (xs : List Int) : Prop := mergeSort (mergeSort xs) = mergeSort xs
theorem idempotent_thm (xs : List Int) : idempotent_prop xs :=
  alreadySorted_thm (mergeSort xs) (sorted_thm xs)

/-- Invalid inputs raise precisely the source's ValueError; valid inputs do not. -/
def validation_prop (input : Input) : Prop :=
  checkedMergeSort input = .error "ValueError: Input must be List[int]" ↔ ¬InputPre input
theorem validation_thm (input : Input) : validation_prop input := by
  unfold validation_prop InputPre
  rw [← decode_isSome]
  cases h : decode input <;> simp [checkedMergeSort, h]

/-- Full value-level postcondition, including duplicate and edge-case behavior. -/
def Post_prop (xs : List Int) : Prop :=
  sorted_prop xs ∧ permutation_prop xs ∧ length_prop xs ∧
  (∀ x, counts_prop xs x) ∧ (∀ x, membership_prop xs x) ∧
  baseCase_prop xs ∧ alreadySorted_prop xs ∧ idempotent_prop xs

/-! ## Bounded property-based tests
Every list of length at most four over five signed integers is enumerated.
These tests are evidence only; none is used by a theorem proof.
-/
def smallLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => [[]] ++ [-2, -1, 0, 1, 2].flatMap
      (fun x => (smallLists n).map (fun xs => x :: xs))

-- PBT: sorted_prop
example : (smallLists 4).all (fun xs =>
    decide ((mergeSort xs).Pairwise (· ≤ ·))) = true := by native_decide
-- PBT: permutation_prop
example : (smallLists 4).all (fun xs =>
    decide ((mergeSort xs).Perm xs)) = true := by native_decide
-- PBT: length_prop
example : (smallLists 4).all (fun xs =>
    (mergeSort xs).length == xs.length) = true := by native_decide
-- PBT: counts_prop, including integers absent from every sampled input.
example : (smallLists 4).all (fun xs => [-3, -2, -1, 0, 1, 2, 3].all
    (fun x => (mergeSort xs).count x == xs.count x)) = true := by native_decide
-- PBT: membership_prop
example : (smallLists 4).all (fun xs => [-3, -2, -1, 0, 1, 2, 3].all
    (fun x => decide (x ∈ mergeSort xs ↔ x ∈ xs))) = true := by native_decide
-- PBT: baseCase_prop
example : (smallLists 4).all (fun xs =>
    decide (xs.length ≤ 1 → mergeSort xs = xs)) = true := by native_decide
-- PBT: alreadySorted_prop
example : (smallLists 4).all (fun xs =>
    decide (xs.Pairwise (· ≤ ·) → mergeSort xs = xs)) = true := by native_decide
-- PBT: idempotent_prop
example : (smallLists 4).all (fun xs =>
    mergeSort (mergeSort xs) == mergeSort xs) = true := by native_decide

def boundarySamples : List Input :=
  .nonList :: (smallLists 3).flatMap (fun xs =>
    let es := xs.map Element.integer
    [.list es, .list (.other :: es), .list (es ++ [.other]),
     .list (.boolean false :: .boolean true :: es)])

-- PBT: validation_prop, valid lists, non-lists, and bad elements at both ends.
example : boundarySamples.all (fun input =>
    decide (checkedMergeSort input = .error "ValueError: Input must be List[int]") ==
      !(pre input)) = true := by native_decide

-- PBT: validation/decoding agreement and the typed-core embedding.
example : boundarySamples.all (fun input =>
    (decode input).isSome == pre input) = true := by native_decide
example : (smallLists 4).all (fun xs =>
    decide (checkedMergeSort (.list (xs.map Element.integer)) =
      .ok (mergeSort xs))) = true := by native_decide

/-- Executable postcondition. Counts and membership need only be checked on
both finite supports: outside their union, both counts are zero and both
membership statements are false. -/
def postCheck (xs : List Int) : Bool :=
  let ys := mergeSort xs
  decide (ys.Pairwise (· ≤ ·)) && decide (ys.Perm xs) &&
  (ys.length == xs.length) &&
  (xs ++ ys).all (fun x => ys.count x == xs.count x) &&
  (xs ++ ys).all (fun x => decide (x ∈ ys ↔ x ∈ xs)) &&
  decide (xs.length ≤ 1 → ys = xs) &&
  decide (xs.Pairwise (· ≤ ·) → ys = xs) && (mergeSort ys == ys)

-- PBT: Post_prop, the complete conjunction.
example : (smallLists 4).all postCheck = true := by native_decide
#eval ((smallLists 4).length, (smallLists 4).all postCheck)

/-- Correctness on the entire (unbounded) integer-list domain. -/
theorem correctness_thm (xs : List Int) : Pre xs → Post_prop xs := by
  intro _
  exact ⟨sorted_thm xs, permutation_thm xs, length_thm xs,
    counts_thm xs, membership_thm xs, baseCase_thm xs,
    alreadySorted_thm xs, idempotent_thm xs⟩

/-- At the dynamic boundary every admissible input succeeds with the specified
sorted permutation; validation_thm covers every inadmissible input. -/
theorem checked_correctness_thm (input : Input) (h : InputPre input) :
    ∃ xs, decode input = some xs ∧
      checkedMergeSort input = .ok (mergeSort xs) ∧ Post_prop xs := by
  have hs : (decode input).isSome = true := by
    simpa only [decode_isSome, InputPre] using h
  cases hd : decode input with
  | none => simp [hd] at hs
  | some xs =>
    exact ⟨xs, rfl, by simp [checkedMergeSort, hd], correctness_thm xs trivial⟩

/-! ## Imperative implementation

`left` and `right` are the suffixes starting at Python's `i` and `j`.
The mutable accumulator is Python's `result`. Each recursive loop iteration
consumes one head; the sum of the initial lengths is therefore a sufficient
termination bound. On exiting the loop the unconsumed suffixes are appended.
This is a total, fuel-bounded presentation of the source's `while` loop, not a
call to the functional merge or to any external sorting primitive.
-/
def mergeLoop : Nat → List Int → List Int → List Int → List Int
  | 0, left, right, acc => acc ++ left ++ right
  | fuel + 1, left, right, acc => Id.run do
      let mut l := left
      let mut r := right
      let mut result := acc
      match l, r with
      | [], _ => result := result ++ r
      | _, [] => result := result ++ l
      | a :: as, b :: bs =>
        if a ≤ b then
          result := result ++ [a]
          l := as
        else
          result := result ++ [b]
          r := bs
        result := mergeLoop fuel l r result
      return result

def mergeImperative (left right : List Int) : List Int := Id.run do
  let mut result := []
  result := mergeLoop (left.length + right.length) left right result
  return result

def mergeSortImperative (xs : List Int) : List Int := Id.run do
  let mut result := xs
  if h : xs.length ≤ 1 then
    return result
  else
    let mid := xs.length / 2
    let mut left := xs.take mid
    let mut right := xs.drop mid
    left := mergeSortImperative left
    right := mergeSortImperative right
    result := mergeImperative left right
    return result
termination_by xs.length
decreasing_by
  · simp only [List.length_take]
    have : xs.length / 2 < xs.length := Nat.div_lt_self (by omega) (by omega)
    omega
  · simp only [List.length_drop]
    have : 0 < xs.length / 2 := Nat.div_pos (by omega) (by omega)
    omega

def checkedMergeSortImperative (input : Input) : Except String (List Int) := Id.run do
  match decode input with
  | none => return .error "ValueError: Input must be List[int]"
  | some xs =>
    let mut result := xs
    result := mergeSortImperative result
    return .ok result

example : mergeImperative [-2, 1, 1, 7] [-1, 1, 3] =
    [-2, -1, 1, 1, 1, 3, 7] := by native_decide
example : unitCases.all (fun t => mergeSortImperative t.1 == t.2) = true := by native_decide
example : checkedMergeSortImperative (.list [.integer 1, .other]) =
    .error "ValueError: Input must be List[int]" := by native_decide
example : checkedMergeSortImperative .nonList =
    .error "ValueError: Input must be List[int]" := by native_decide
example : checkedMergeSortImperative (.list [.boolean true, .integer (-2), .boolean false]) =
    .ok [-2, 0, 1] := by native_decide
-- Additional bounded equivalence tests, independent of the proofs below.
example : (smallLists 4).all (fun xs =>
    mergeSort xs == mergeSortImperative xs) = true := by native_decide
example : boundarySamples.all (fun input =>
    decide (checkedMergeSort input = checkedMergeSortImperative input)) = true := by
  native_decide
#eval mergeSortImperative [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
#eval checkedMergeSortImperative (.list [.integer 1, .other])

/-- Loop invariant: the result is the old accumulator followed by the merge of
all remaining elements. A sufficient fuel bound is proved, not assumed by the
public equivalence theorem. -/
theorem mergeLoop_invariant (fuel : Nat) (left right acc : List Int)
    (h : left.length + right.length ≤ fuel) :
    mergeLoop fuel left right acc = acc ++ merge left right := by
  induction fuel generalizing left right acc with
  | zero =>
    have hl : left = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hr : right = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst left
    subst right
    simp [mergeLoop, merge]
  | succ fuel ih =>
    cases left with
    | nil => simp [mergeLoop, merge]
    | cons a as =>
      cases right with
      | nil => simp [mergeLoop, merge]
      | cons b bs =>
        by_cases hab : a ≤ b
        · have hf : as.length + (b :: bs).length ≤ fuel := by
            simp only [List.length_cons] at h ⊢
            omega
          simp [mergeLoop, hab, ih as (b :: bs) (acc ++ [a]) hf,
            merge, List.append_assoc]
        · have hf : (a :: as).length + bs.length ≤ fuel := by
            simp only [List.length_cons] at h ⊢
            omega
          simp [mergeLoop, hab, ih (a :: as) bs (acc ++ [b]) hf,
            merge, List.append_assoc]

theorem merge_equivalence_thm (left right : List Int) :
    merge left right = mergeImperative left right := by
  simpa [mergeImperative] using
    (mergeLoop_invariant (left.length + right.length) left right [] (by omega)).symm

/-- Value equality of the two independently implemented sorts, without a size
bound or an additional hypothesis on the integers. -/
theorem equivalence_thm (xs : List Int) : mergeSort xs = mergeSortImperative xs := by
  rw [mergeSort, mergeSortImperative]
  split_ifs with h
  · rfl
  · dsimp only [Id.run, bind, pure]
    rw [← equivalence_thm (xs.take (xs.length / 2)),
      ← equivalence_thm (xs.drop (xs.length / 2))]
    exact merge_equivalence_thm _ _
termination_by xs.length
decreasing_by
  · simp only [List.length_take]
    have : xs.length / 2 < xs.length := Nat.div_lt_self (by omega) (by omega)
    omega
  · simp only [List.length_drop]
    have : 0 < xs.length / 2 := Nat.div_pos (by omega) (by omega)
    omega

/-- Equivalence includes the exceptional behavior, for *every* boundary input. -/
theorem checked_equivalence_thm (input : Input) :
    checkedMergeSort input = checkedMergeSortImperative input := by
  cases hd : decode input <;>
    simp [checkedMergeSort, checkedMergeSortImperative, hd, equivalence_thm]

end merge_sort
end Agent
