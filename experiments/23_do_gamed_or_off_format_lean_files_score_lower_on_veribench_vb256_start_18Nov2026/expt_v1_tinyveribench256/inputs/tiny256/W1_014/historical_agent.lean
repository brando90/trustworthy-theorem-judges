import Mathlib
namespace Agent

/-!
# Selection sort on Python integers

`Int` models Python's unbounded integers. The functional algorithm repeatedly
extracts a minimum from the unsorted list; it does not call a library sorting
routine. The imperative version uses mutable unsorted and sorted portions.
The relative order of equal integers is not observable. A small dynamic input
layer represents the Python list/type check and its `ValueError` result.
-/

namespace selection_sort

deriving instance DecidableEq for Except

/-- The inner scan uses the same strict comparison as Python. -/
def minimum (candidate : Int) : List Int → Int
  | [] => candidate
  | x :: xs => minimum (if x < candidate then x else candidate) xs

/-- Swap the head with the first minimum of the remaining suffix.
If the head is already minimal, Python swaps it with itself. Otherwise
`replace` puts the old head at the first occurrence of the minimum. -/
def selectMin (candidate : Int) (xs : List Int) : Int × List Int :=
  let m := minimum candidate xs
  if m < candidate then (m, xs.replace m candidate) else (candidate, xs)

/-- Fuel is initially the length, so every element is selected exactly once. -/
def sortAux : Nat → List Int → List Int
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, x :: xs =>
      let p := selectMin x xs
      p.1 :: sortAux n p.2

def selectionSort (xs : List Int) : List Int := sortAux xs.length xs

/-- Other Python values are distinguished only as far as validation needs them.
Python booleans pass `isinstance(x, int)` and denote zero and one. -/
inductive PyValue where
  | integer : Int → PyValue
  | boolean : Bool → PyValue
  | other : PyValue
  deriving DecidableEq, Repr

inductive PyInput where
  | list : List PyValue → PyInput
  | notList : PyInput
  deriving DecidableEq, Repr

def asInt : PyValue → Option Int
  | .integer n => some n
  | .boolean b => some (if b then 1 else 0)
  | .other => none

/-- Executable Python `isinstance(x, int)` in the dynamic input model. -/
def integerCheck : PyValue → Bool
  | .integer _ => true
  | .boolean _ => true
  | .other => false

/-- Python's list check and element check, independently of the decoder. -/
def preInput : PyInput → Bool
  | .list xs => xs.all integerCheck
  | .notList => false

def decode : PyInput → Option (List Int)
  | .list xs => xs.mapM asInt
  | .notList => none

def checkedSelectionSort (input : PyInput) : Except String (List Int) :=
  match decode input with
  | some xs => .ok (selectionSort xs)
  | none => .error "Input must be List[int]"

-- All positive examples from the Python test suite.
def testCases : List (List Int × List Int) :=
  [([3,1,2], [1,2,3]), ([1,2,3], [1,2,3]), ([2,1,3], [1,2,3]),
   ([], []), ([1], [1]),
   ([5,2,4,6,1,3], [1,2,3,4,5,6]),
   ([9,8,7,6,5,4,3,2,1], [1,2,3,4,5,6,7,8,9]),
   ([2,6,4,3,1,5], [1,2,3,4,5,6]),
   ([2,1], [1,2]), ([1,2], [1,2]),
   ([3,1,4,1,2,3], [1,1,2,3,3,4]), ([5,5,5,5,5], [5,5,5,5,5]),
   ([1,2,3,4,5], [1,2,3,4,5]), ([5,4,3,2,1], [1,2,3,4,5]),
   ([3,7,1,9,2,8,4,6,5], [1,2,3,4,5,6,7,8,9])]

example : testCases.all (fun p => selectionSort p.1 == p.2) = true := by native_decide
example : selectionSort [-3, 0, -9, 4, -3] = [-9, -3, -3, 0, 4] := by native_decide
example : checkedSelectionSort (.list [.integer 1, .other]) =
    .error "Input must be List[int]" := by native_decide
example : checkedSelectionSort .notList = .error "Input must be List[int]" := by native_decide
example : checkedSelectionSort (.list [.boolean true, .integer (-1), .boolean false]) =
    .ok [-1, 0, 1] := by native_decide
#eval selectionSort [3, 1, 2]
#eval selectionSort ([] : List Int)

/-- The typed core admits every list of integers, including the empty list. -/
def Pre (_xs : List Int) : Prop := True
/-- Dynamic admissibility is the source program's executable precheck. -/
def ValidInput (input : PyInput) : Prop := preInput input = true

theorem decode_isSome_thm (input : PyInput) : (decode input).isSome = preInput input := by
  cases input with
  | notList => rfl
  | list xs =>
      change (xs.mapM asInt).isSome = xs.all integerCheck
      induction xs with
      | nil => rfl
      | cons v vs ih =>
          cases ht : vs.mapM asInt <;> cases v <;>
            simp_all [List.mapM_cons, asInt, integerCheck]

theorem decode_valid_iff_thm (input : PyInput) :
    (∃ xs, decode input = some xs) ↔ ValidInput input := by
  unfold ValidInput
  rw [← decode_isSome_thm]
  cases decode input <;> simp

theorem decode_integers_thm (xs : List Int) :
    decode (.list (xs.map PyValue.integer)) = some xs := by
  change (xs.map PyValue.integer).mapM asInt = some xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, asInt, ih]


/-! ## Minimum-scan and swap invariants -/

theorem minimum_spec (a : Int) (xs : List Int) :
    minimum a xs ∈ a :: xs ∧ ∀ y ∈ a :: xs, minimum a xs ≤ y := by
  induction xs generalizing a with
  | nil => simp [minimum]
  | cons x xs ih =>
      simp only [minimum]
      split_ifs with h
      · obtain ⟨hm, hl⟩ := ih x
        constructor
        · exact List.mem_cons_of_mem a hm
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact le_trans (hl x (by simp)) (le_of_lt h)
          · exact hl y hy
      · obtain ⟨hm, hl⟩ := ih a
        constructor
        · rcases List.mem_cons.mp hm with hm | hm
          · simp [hm]
          · exact List.mem_cons_of_mem a (List.mem_cons_of_mem x hm)
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hl y (by simp)
          rcases List.mem_cons.mp hy with rfl | hy
          · exact le_trans (hl a (by simp)) (le_of_not_gt h)
          · exact hl y (by simp [hy])

/-- Replacing a known occurrence realizes a swap, not deletion of duplicates. -/
theorem cons_replace_perm (a m : Int) (xs : List Int) (hm : m ∈ xs) :
    (m :: xs.replace m a).Perm (a :: xs) := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
      by_cases h : m = x
      · subst x
        simp only [List.replace_cons_self]
        exact List.Perm.swap _ _ _
      · have ht : m ∈ xs := (List.mem_cons.mp hm).resolve_left h
        simp only [List.replace_cons, beq_eq_false_iff_ne.mpr h]
        exact (List.Perm.swap _ _ _).trans
          ((List.Perm.cons x (ih ht)).trans (List.Perm.swap _ _ _))

theorem selectMin_perm (a : Int) (xs : List Int) :
    ((selectMin a xs).1 :: (selectMin a xs).2).Perm (a :: xs) := by
  obtain ⟨hm, hl⟩ := minimum_spec a xs
  dsimp only [selectMin]
  split_ifs with h
  · apply cons_replace_perm
    rcases List.mem_cons.mp hm with he | he
    · omega
    · exact he
  · exact List.Perm.refl _

theorem selectMin_le (a : Int) (xs : List Int) :
    ∀ y ∈ (selectMin a xs).2, (selectMin a xs).1 ≤ y := by
  have hp := selectMin_perm a xs
  obtain ⟨_, hl⟩ := minimum_spec a xs
  intro y hy
  have hmem : y ∈ a :: xs := hp.mem_iff.mp (List.mem_cons_of_mem _ hy)
  have hle := hl y hmem
  dsimp only [selectMin] at *
  split_ifs at * with h
  · exact hle
  · have ha := hl a (by simp)
    have he : minimum a xs = a := by omega
    simpa [he] using hle

theorem selectMin_length (a : Int) (xs : List Int) :
    (selectMin a xs).2.length = xs.length := by
  have h := (selectMin_perm a xs).length_eq
  simpa using h

/-- The length bound is the loop invariant ensuring fuel never runs out early. -/
theorem sortAux_perm (n : Nat) (xs : List Int) (h : xs.length ≤ n) :
    (sortAux n xs).Perm xs := by
  induction n generalizing xs with
  | zero =>
      have he : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
      subst xs
      exact List.Perm.refl _
  | succ n ih =>
      cases xs with
      | nil => exact List.Perm.refl _
      | cons x xs =>
          have ht : (selectMin x xs).2.length ≤ n := by
            rw [selectMin_length]
            simpa using h
          exact (List.Perm.cons _ (ih _ ht)).trans (selectMin_perm x xs)

theorem sortAux_sorted (n : Nat) (xs : List Int) (h : xs.length ≤ n) :
    (sortAux n xs).Pairwise (· ≤ ·) := by
  induction n generalizing xs with
  | zero => simp [sortAux]
  | succ n ih =>
      cases xs with
      | nil => simp [sortAux]
      | cons x xs =>
          have ht : (selectMin x xs).2.length ≤ n := by
            rw [selectMin_length]
            simpa using h
          apply List.pairwise_cons.mpr
          constructor
          · intro y hy
            apply selectMin_le x xs y
            exact (sortAux_perm n _ ht).mem_iff.mp hy
          · exact ih _ ht

/-! ## Executable properties and their universal proofs -/

def sorted_prop (ys : List Int) : Prop := ys.Pairwise (· ≤ ·)
def permutation_prop (xs ys : List Int) : Prop := ys.Perm xs
def length_prop (xs ys : List Int) : Prop := ys.length = xs.length
def multiplicity_prop (xs ys : List Int) : Prop := ∀ z : Int, ys.count z = xs.count z
def unchanged_prop (xs ys : List Int) : Prop := sorted_prop xs → ys = xs
def idempotent_prop (ys : List Int) : Prop := selectionSort ys = ys
def empty_prop (xs ys : List Int) : Prop := ys = [] ↔ xs = []

theorem sorted_thm (xs : List Int) : sorted_prop (selectionSort xs) :=
  sortAux_sorted xs.length xs (le_refl _)

theorem permutation_thm (xs : List Int) : permutation_prop xs (selectionSort xs) :=
  sortAux_perm xs.length xs (le_refl _)

theorem length_thm (xs : List Int) : length_prop xs (selectionSort xs) :=
  (permutation_thm xs).length_eq

theorem multiplicity_thm (xs : List Int) : multiplicity_prop xs (selectionSort xs) :=
  (permutation_thm xs).count_eq

theorem unchanged_thm (xs : List Int) : unchanged_prop xs (selectionSort xs) := by
  intro hs
  exact List.eq_of_perm_of_sorted (permutation_thm xs) (sorted_thm xs) hs

theorem idempotent_thm (xs : List Int) : idempotent_prop (selectionSort xs) :=
  unchanged_thm (selectionSort xs) (sorted_thm xs)

theorem empty_thm (xs : List Int) : empty_prop xs (selectionSort xs) := by
  constructor
  · intro h
    have hl := length_thm xs
    change (selectionSort xs).length = xs.length at hl
    rw [h] at hl
    exact List.length_eq_zero_iff.mp hl.symm
  · rintro rfl
    rfl

theorem singleton_thm (x : Int) : selectionSort [x] = [x] := by
  simp [selectionSort, sortAux, selectMin, minimum]

/-- Sorted permutations of the same input are unique. -/
theorem unique_thm (xs ys : List Int) (hs : sorted_prop ys)
    (hp : permutation_prop xs ys) : selectionSort xs = ys :=
  List.eq_of_perm_of_sorted ((permutation_thm xs).trans hp.symm) (sorted_thm xs) hs

/-- Invalid Python values raise exactly the stated ValueError; valid ones run
on the decoded list without changing the mathematical integer domain. -/
def validation_prop (input : PyInput) : Prop :=
  (checkedSelectionSort input = .error "Input must be List[int]" ↔ ¬ ValidInput input) ∧
  (∀ xs, decode input = some xs → checkedSelectionSort input = .ok (selectionSort xs))

theorem validation_thm (input : PyInput) : validation_prop input := by
  unfold validation_prop checkedSelectionSort
  rw [← decode_valid_iff_thm]
  cases h : decode input <;> simp

theorem invalid_thm (input : PyInput) (h : ¬ ValidInput input) :
    checkedSelectionSort input = .error "Input must be List[int]" :=
  (validation_thm input).1.mpr h

theorem accepted_integer_list_thm (xs : List Int) :
    checkedSelectionSort (.list (xs.map PyValue.integer)) = .ok (selectionSort xs) := by
  simp [checkedSelectionSort, decode_integers_thm]

/-- The relational postcondition includes order, duplicates, cardinality,
fixed points on sorted inputs, idempotence, and the empty-list edge case. -/
def Post_prop (xs ys : List Int) : Prop :=
  sorted_prop ys ∧ permutation_prop xs ys ∧ length_prop xs ys ∧
  multiplicity_prop xs ys ∧ unchanged_prop xs ys ∧ idempotent_prop ys ∧ empty_prop xs ys

/-! ## Property-based tests

Every integer list is admissible. The bounded corpus exhausts lengths zero
through five over {-2,-1,0,1,2}, so it includes negative values, repeated minima,
already sorted lists, reverse lists, and all the short edge cases.
The tests below are evidence only; none is used in a theorem proof.
-/

def wordsOver {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap (fun x => (wordsOver alphabet n).map (x :: ·))

def smallLists : List (List Int) :=
  (List.range 6).flatMap (wordsOver [-2, -1, 0, 1, 2])

def sortedCheck (xs : List Int) : Bool := decide (xs.Pairwise (· ≤ ·))

/-- Checking the union of the supports checks every possible nonzero count;
all integers outside that union have count zero on both sides. -/
def multiplicityCheck (xs ys : List Int) : Bool :=
  (xs ++ ys).all (fun z => ys.count z == xs.count z)

def postCheck (xs ys : List Int) : Bool :=
  sortedCheck ys && decide (ys.Perm xs) && (ys.length == xs.length) &&
  multiplicityCheck xs ys && (!sortedCheck xs || ys == xs) &&
  (selectionSort ys == ys) && (ys.isEmpty == xs.isEmpty)

theorem multiplicityCheck_iff (xs ys : List Int) :
    multiplicityCheck xs ys = true ↔ multiplicity_prop xs ys := by
  simp only [multiplicityCheck, List.all_eq_true, beq_iff_eq, multiplicity_prop]
  constructor
  · intro h z
    by_cases hz : z ∈ xs ++ ys
    · exact h z hz
    · have hx : z ∉ xs := fun hx => hz (List.mem_append.mpr (Or.inl hx))
      have hy : z ∉ ys := fun hy => hz (List.mem_append.mpr (Or.inr hy))
      simp [List.count_eq_zero_of_not_mem hx, List.count_eq_zero_of_not_mem hy]
  · intro h z _
    exact h z

/-- The executable PBT checks the full postcondition, not a weaker surrogate. -/
theorem postCheck_iff (xs ys : List Int) : postCheck xs ys = true ↔ Post_prop xs ys := by
  have he : (ys.isEmpty == xs.isEmpty) = true ↔ empty_prop xs ys := by
    rw [beq_iff_eq, Bool.eq_iff_iff]
    simp [empty_prop]
  have hu : (!sortedCheck xs || ys == xs) = true ↔ unchanged_prop xs ys := by
    by_cases h : xs.Pairwise (· ≤ ·) <;>
      simp [sortedCheck, unchanged_prop, sorted_prop, h]
  simp only [postCheck, Bool.and_eq_true, he, hu]
  simp only [sortedCheck, decide_eq_true_eq, beq_iff_eq, multiplicityCheck_iff,
    Post_prop, sorted_prop, permutation_prop, length_prop, idempotent_prop, and_assoc]

-- PBT: sorted_prop.
example : smallLists.all (fun xs => sortedCheck (selectionSort xs)) = true := by native_decide
-- PBT: permutation_prop, hence no element is lost or introduced.
example : smallLists.all (fun xs => decide ((selectionSort xs).Perm xs)) = true := by native_decide
-- PBT: length_prop.
example : smallLists.all (fun xs => (selectionSort xs).length == xs.length) = true := by native_decide
-- PBT: multiplicity_prop, including every duplicate.
example : smallLists.all (fun xs => multiplicityCheck xs (selectionSort xs)) = true := by native_decide
-- PBT: unchanged_prop, using a decidable implication.
example : smallLists.all (fun xs => !sortedCheck xs || selectionSort xs == xs) = true := by native_decide
-- PBT: idempotent_prop.
example : smallLists.all (fun xs => selectionSort (selectionSort xs) == selectionSort xs) = true := by native_decide
-- PBT: empty_prop.
example : smallLists.all (fun xs => (selectionSort xs).isEmpty == xs.isEmpty) = true := by native_decide
-- PBT: Post_prop, checking the full conjunction on each input.
example : smallLists.all (fun xs => postCheck xs (selectionSort xs)) = true := by native_decide

-- Also exercise unbounded integer/list sampling, not only the finite alphabet.
#eval Plausible.Testable.check (∀ xs : List Int, postCheck xs (selectionSort xs) = true)
#eval Plausible.Testable.check (∀ (xs : List Int) (z : Int),
  (selectionSort xs).count z = xs.count z)

def smallInputs : List PyInput :=
  .notList :: ((List.range 4).flatMap
    (wordsOver [.integer (-2), .integer 0, .integer 2, .boolean false, .boolean true, .other])).map
      PyInput.list

def validationCheck (input : PyInput) : Bool :=
  match checkedSelectionSort input with
  | .error msg => !preInput input && msg == "Input must be List[int]"
  | .ok ys => preInput input &&
      match decode input with
      | some xs => ys == selectionSort xs
      | none => false

-- PBT: validation_prop, including malformed lists and non-list inputs.
example : smallInputs.all validationCheck = true := by native_decide
#eval (smallLists.length, smallInputs.length)

/-! ## Correctness -/

theorem correctness_thm (xs : List Int) (_h : Pre xs) :
    Post_prop xs (selectionSort xs) :=
  ⟨sorted_thm xs, permutation_thm xs, length_thm xs, multiplicity_thm xs,
   unchanged_thm xs, idempotent_thm xs, empty_thm xs⟩

theorem checked_correctness_thm (input : PyInput) (h : ValidInput input) :
    ∃ xs ys, decode input = some xs ∧ checkedSelectionSort input = .ok ys ∧ Post_prop xs ys := by
  obtain ⟨xs, hx⟩ := (decode_valid_iff_thm input).mpr h
  exact ⟨xs, selectionSort xs, hx, (validation_thm input).2 xs hx,
    correctness_thm xs trivial⟩

/-! ## Imperative implementation

The immutable input is not modified (Python first copies it). The mutable
`result` and `rest` represent the already-sorted prefix and remaining suffix
of that copy. Each pass scans the suffix and swaps its first minimum with its
head. Splitting the copy into these two portions avoids partial array indexing.
-/

def minimumImperative (a : Int) (xs : List Int) : Int := Id.run do
  let mut candidate := a
  for x in xs do
    if x < candidate then
      candidate := x
  return candidate

def selectMinImperative (a : Int) (xs : List Int) : Int × List Int := Id.run do
  let mut rest := xs
  let mut head := a
  let m := minimumImperative a xs
  if m < head then
    rest := rest.replace m head
    head := m
  return (head, rest)

/-- A generalized loop permits a proof with an arbitrary initial sorted prefix. -/
def imperativePasses (steps : List Nat) (remaining output : List Int) : List Int := Id.run do
  let mut rest := remaining
  let mut result := output
  for _ in steps do
    match rest with
    | [] => pure ()
    | x :: xs =>
        let p := selectMinImperative x xs
        result := result ++ [p.1]
        rest := p.2
  return result

def selectionSortImperative (xs : List Int) : List Int := Id.run do
  let mut rest := xs
  let mut result := []
  for _ in List.range xs.length do
    match rest with
    | [] => pure ()
    | x :: tail =>
        let p := selectMinImperative x tail
        result := result ++ [p.1]
        rest := p.2
  return result

def checkedSelectionSortImperative (input : PyInput) : Except String (List Int) :=
  match decode input with
  | some xs => .ok (selectionSortImperative xs)
  | none => .error "Input must be List[int]"

-- All original positive cases, plus negatives and error behavior.
example : testCases.all (fun p => selectionSortImperative p.1 == p.2) = true := by native_decide
example : selectionSortImperative [-3, 0, -9, 4, -3] = [-9, -3, -3, 0, 4] := by native_decide
example : checkedSelectionSortImperative (.list [.integer 1, .other]) =
    .error "Input must be List[int]" := by native_decide
example : checkedSelectionSortImperative .notList =
    .error "Input must be List[int]" := by native_decide
example : smallLists.all (fun xs => selectionSort xs == selectionSortImperative xs) = true := by native_decide
example : smallLists.all (fun xs => postCheck xs (selectionSortImperative xs)) = true := by native_decide
example : smallInputs.all (fun input =>
    decide (checkedSelectionSort input = checkedSelectionSortImperative input)) = true := by native_decide
#eval selectionSortImperative [5, 2, 4, 6, 1, 3]
#eval selectionSortImperative ([] : List Int)
#eval Plausible.Testable.check (∀ xs : List Int, selectionSort xs = selectionSortImperative xs)

/-! ## Kernel-checked functional–imperative equivalence -/

theorem minimumImperative_eq (a : Int) (xs : List Int) :
    minimumImperative a xs = minimum a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      simp only [minimumImperative, List.forIn_cons, Id.run, bind_pure_comp]
      split_ifs with h
      · simpa [minimum, h, minimumImperative] using ih x
      · simpa [minimum, h, minimumImperative] using ih a

theorem selectMinImperative_eq (a : Int) (xs : List Int) :
    selectMinImperative a xs = selectMin a xs := by
  simp only [selectMinImperative, selectMin, minimumImperative_eq]
  split_ifs <;> rfl

theorem imperativePasses_nil (steps : List Nat) (out : List Int) :
    imperativePasses steps [] out = out := by
  induction steps with
  | nil => rfl
  | cons i steps ih =>
      simpa [imperativePasses, List.forIn_cons, Id.run] using ih

theorem imperativePasses_cons (i : Nat) (steps : List Nat) (x : Int) (xs out : List Int) :
    imperativePasses (i :: steps) (x :: xs) out =
    imperativePasses steps (selectMinImperative x xs).2 (out ++ [(selectMinImperative x xs).1]) := by
  simp [imperativePasses, List.forIn_cons, Id.run]

/-- The loop invariant connects any number of remaining passes and any prefix
with the recursive algorithm. No tests or compiled decision procedure are used. -/
theorem imperativePasses_eq (steps : List Nat) (xs out : List Int) :
    imperativePasses steps xs out = out ++ sortAux steps.length xs := by
  induction steps generalizing xs out with
  | nil =>
      change out = out ++ []
      simp
  | cons i steps ih =>
      cases xs with
      | nil => simp [imperativePasses_nil, sortAux]
      | cons x xs =>
          rw [imperativePasses_cons, ih, selectMinImperative_eq]
          simp [sortAux, List.append_assoc]

theorem equivalence_thm (xs : List Int) :
    selectionSort xs = selectionSortImperative xs := by
  change sortAux xs.length xs = imperativePasses (List.range xs.length) xs []
  rw [imperativePasses_eq]
  simp

theorem checked_equivalence_thm (input : PyInput) :
    checkedSelectionSort input = checkedSelectionSortImperative input := by
  unfold checkedSelectionSort checkedSelectionSortImperative
  cases decode input with
  | none => rfl
  | some xs => exact congrArg Except.ok (equivalence_thm xs)

theorem imperative_correctness_thm (xs : List Int) (h : Pre xs) :
    Post_prop xs (selectionSortImperative xs) := by
  rw [← equivalence_thm]
  exact correctness_thm xs h

end selection_sort
end Agent
