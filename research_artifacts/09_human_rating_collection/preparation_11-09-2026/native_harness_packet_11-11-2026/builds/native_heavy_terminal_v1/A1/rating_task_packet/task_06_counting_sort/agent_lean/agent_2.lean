import Mathlib

/-!
# Counting sort for signed integers

A direct functional counting sort uses a zero-filled array indexed by the offset
from the minimum input. Each bin is incremented once per occurrence, then expanded
in increasing order. `Int` models Python's unbounded integers. The typed core has
no invalid elements; a separate dynamic-input wrapper models `ValueError`, including
Python's acceptance of booleans as integers. All non-integer values are represented
by one tag because their contents do not affect validation.
-/

namespace counting_sort

/-- Increment the bin belonging to `x`, using the minimum as an index shift. -/
def increment (lo : Int) (counts : Array Nat) (x : Int) : Array Nat :=
  counts.modify (x - lo).toNat (· + 1)

/-- A pure fold is the functional counterpart of the counting loop. -/
def histogram (lo : Int) (size : Nat) (xs : List Int) : Array Nat :=
  xs.foldl (increment lo) (Array.replicate size 0)

def lower : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl min x

def upper : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

def rangeSize (xs : List Int) : Nat := (upper xs - lower xs + 1).toNat

/-- The empty branch avoids consulting extrema of an empty list. -/
def countingSort (xs : List Int) : List Int :=
  if xs.isEmpty then [] else
    let lo := lower xs
    let size := rangeSize xs
    let counts := histogram lo size xs
    (List.range size).flatMap fun (i : Nat) => List.replicate counts[i]! (lo + (i : Int))

/-- Values relevant to Python's `isinstance(x, int)` check. -/
inductive PyValue where
  | integer (value : Int)
  | boolean (value : Bool)
  | nonInteger
  deriving DecidableEq, Repr

inductive PyInput where
  | list (values : List PyValue)
  | nonList
  deriving DecidableEq, Repr

def PyValue.asInt : PyValue → Option Int
  | .integer n => some n
  | .boolean b => some (if b then 1 else 0)
  | .nonInteger => none

def PyValue.isInteger : PyValue → Bool
  | .nonInteger => false
  | _ => true

/-- Python's list check and its `all(isinstance(x, int) ...)` element check. -/
def pre : PyInput → Bool
  | .list values => values.all PyValue.isInteger
  | .nonList => false

def decode : PyInput → Option (List Int)
  | .list values => values.mapM PyValue.asInt
  | .nonList => none

deriving instance DecidableEq for Except

def checkedCountingSort (input : PyInput) : Except String (List Int) :=
  match decode input with
  | none => .error "Input must be List[int]"
  | some xs => .ok (countingSort xs)

-- Unit tests: every valid-input example from the Python test suite.
example : countingSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : countingSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : countingSort [] = [] := by native_decide
example : countingSort [1] = [1] := by native_decide
example : countingSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [2, 1] = [1, 2] := by native_decide
example : countingSort [1, 2] = [1, 2] := by native_decide
example : countingSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSort [3, 1, 2, 1, 3, 2] = [1, 1, 2, 2, 3, 3] := by native_decide
example : countingSort [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : countingSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSort [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide
example : countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : countingSort [-3, 0, -1, -3, 2] = [-3, -3, -1, 0, 2] := by native_decide
example : countingSort [-2, -5, -1, -5] = [-5, -5, -2, -1] := by native_decide
example : countingSort [-100000000000000000000, -99999999999999999999] =
    [-100000000000000000000, -99999999999999999999] := by native_decide
-- The `nonInteger` tag includes the source test's floating-point value 2.5.
example : checkedCountingSort (.list [.integer 1, .nonInteger]) =
    .error "Input must be List[int]" := by native_decide
example : checkedCountingSort .nonList = .error "Input must be List[int]" := by native_decide
example : checkedCountingSort (.list [.boolean true, .integer (-1), .boolean false]) =
    .ok [-1, 0, 1] := by native_decide
#eval countingSort [3, -1, 2, -1, 0]
#eval checkedCountingSort (.list [.integer 1, .nonInteger])

/-- All values of `List Int` satisfy the Python precondition. No numeric bounds apply. -/
def Pre (_xs : List Int) : Prop := True

/-- The dynamic precondition also checks the outer list and the element tags. -/
def DynamicPre (input : PyInput) : Prop := pre input = true

private theorem fold_min_le_seed (xs : List Int) (a : Int) : xs.foldl min a ≤ a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => exact (ih (min a x)).trans (min_le_left _ _)

private theorem seed_le_fold_max (xs : List Int) (a : Int) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => exact (le_max_left _ _).trans (ih (max a x))

private theorem fold_min_le_member (xs : List Int) (a x : Int) (hx : x ∈ xs) :
    xs.foldl min a ≤ x := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (fold_min_le_seed ys (min a x)).trans (min_le_right _ _)
    · exact ih (min a y) hx

private theorem member_le_fold_max (xs : List Int) (a x : Int) (hx : x ∈ xs) :
    x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right _ _).trans (seed_le_fold_max ys (max a x))
    · exact ih (max a y) hx

private theorem lower_le (xs : List Int) (x : Int) (hx : x ∈ xs) : lower xs ≤ x := by
  cases xs with
  | nil => simp at hx
  | cons a xs =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact fold_min_le_seed xs x
    · exact fold_min_le_member xs a x hx

private theorem le_upper (xs : List Int) (x : Int) (hx : x ∈ xs) : x ≤ upper xs := by
  cases xs with
  | nil => simp at hx
  | cons a xs =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact seed_le_fold_max xs x
    · exact member_le_fold_max xs a x hx

private theorem histogram_fold_size (xs : List Int) (lo : Int) (a : Array Nat) :
    (xs.foldl (increment lo) a).size = a.size := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [List.foldl_cons, ih, increment]

/-- Loop invariant: each bin contains its initial value plus the number of hits. -/
private theorem histogram_fold_get (xs : List Int) (lo : Int) (a : Array Nat)
    (i : Nat) (hi : i < a.size) (hlo : ∀ x ∈ xs, lo ≤ x) :
    (xs.foldl (increment lo) a)[i]! = a[i]! + xs.count (lo + (i : Int)) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have hidx : (x - lo).toNat = i ↔ x = lo + (i : Int) := by
      have := hlo x (by simp)
      omega
    have hsize : i < (increment lo a x).size := by simpa [increment] using hi
    rw [List.foldl_cons, ih (increment lo a x) hsize (fun y hy => hlo y (by simp [hy]))]
    rw [getElem!_pos (increment lo a x) i hsize, getElem!_pos a i hi]
    simp only [increment, Array.getElem_modify, List.count_cons]
    by_cases h : x = lo + (i : Int)
    · simp [h, Nat.add_assoc, Nat.add_comm]
    · simp [hidx, h]

private theorem histogram_get (xs : List Int) (i : Nat) (hi : i < rangeSize xs) :
    (histogram (lower xs) (rangeSize xs) xs)[i]! = xs.count (lower xs + (i : Int)) := by
  rw [histogram, histogram_fold_get xs (lower xs) _ i (by simpa using hi) (lower_le xs)]
  simp [getElem!_pos (Array.replicate (rangeSize xs) 0) i (by simpa using hi)]

/-- All values between the minimum and maximum, in increasing order. -/
def bins (xs : List Int) : List Int :=
  (List.range (rangeSize xs)).map fun (i : Nat) => lower xs + (i : Int)

/-- Expand a list of bin values using the input multiplicities. -/
def expand (xs values : List Int) : List Int :=
  values.flatMap fun x => List.replicate (xs.count x) x

private theorem sort_eq_expand (xs : List Int) (hne : xs ≠ []) :
    countingSort xs = expand xs (bins xs) := by
  simp only [countingSort, List.isEmpty_eq_false_iff.mpr hne, Bool.false_eq_true, ↓reduceIte,
    expand, bins, List.flatMap_map]
  apply List.flatMap_congr
  intro i hi
  rw [histogram_get xs i (List.mem_range.mp hi)]

private theorem bins_sorted (xs : List Int) : (bins xs).Pairwise (· ≤ ·) := by
  apply List.pairwise_map.mpr
  exact List.pairwise_le_range.imp (by intros; omega)

private theorem bins_nodup (xs : List Int) : (bins xs).Nodup := by
  exact (List.nodup_map_iff (f := fun (i : Nat) => lower xs + (i : Int))
    (by intro a b h; dsimp at h; omega)).mpr List.nodup_range

private theorem member_bins (xs : List Int) (x : Int) (hx : x ∈ xs) : x ∈ bins xs := by
  have hl := lower_le xs x hx
  have hu := le_upper xs x hx
  apply List.mem_map.mpr
  refine ⟨(x - lower xs).toNat, List.mem_range.mpr ?_, ?_⟩
  · unfold rangeSize
    omega
  · omega

private theorem expand_sorted (xs values : List Int) (h : values.Pairwise (· ≤ ·)) :
    (expand xs values).Pairwise (· ≤ ·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro x _
    exact List.pairwise_replicate.mpr (Or.inr (le_refl x))
  · apply h.imp
    intro a b hab x hx y hy
    have hx' := (List.mem_replicate.mp hx).2
    have hy' := (List.mem_replicate.mp hy).2
    simpa [hx', hy'] using hab

private theorem count_expand (xs values : List Int) (x : Int) :
    (expand xs values).count x = xs.count x * values.count x := by
  induction values with
  | nil => simp [expand]
  | cons a values ih =>
    simp only [expand, List.flatMap_cons, List.count_append] at *
    rw [ih, List.count_cons, List.count_replicate]
    by_cases h : a = x
    · subst a
      simp [Nat.mul_add, Nat.add_comm]
    · simp [h]

def sorted_prop (xs : List Int) : Prop := (countingSort xs).Pairwise (· ≤ ·)

theorem sorted_thm (xs : List Int) : sorted_prop xs := by
  by_cases h : xs = []
  · subst xs; simp [sorted_prop, countingSort]
  · rw [sorted_prop, sort_eq_expand xs h]
    exact expand_sorted xs (bins xs) (bins_sorted xs)

def permutation_prop (xs : List Int) : Prop := (countingSort xs).Perm xs

theorem permutation_thm (xs : List Int) : permutation_prop xs := by
  by_cases h : xs = []
  · subst xs; simp [permutation_prop, countingSort]
  · rw [permutation_prop, sort_eq_expand xs h, List.perm_iff_count]
    intro x
    rw [count_expand, (bins_nodup xs).count]
    by_cases hx : x ∈ xs
    · simp [member_bins xs x hx]
    · simp [List.count_eq_zero.mpr hx]

def multiplicity_prop (xs : List Int) : Prop :=
  ∀ x : Int, (countingSort xs).count x = xs.count x

theorem multiplicity_thm (xs : List Int) : multiplicity_prop xs :=
  (permutation_thm xs).count_eq

def length_prop (xs : List Int) : Prop := (countingSort xs).length = xs.length

theorem length_thm (xs : List Int) : length_prop xs := (permutation_thm xs).length_eq

def empty_prop (xs : List Int) : Prop := countingSort xs = [] ↔ xs = []

theorem empty_thm (xs : List Int) : empty_prop xs := by
  constructor
  · intro h
    have := length_thm xs
    simp only [length_prop, h, List.length_nil] at this
    exact List.length_eq_zero_iff.mp this.symm
  · rintro rfl
    rfl

def idempotent_prop (xs : List Int) : Prop := countingSort (countingSort xs) = countingSort xs

theorem idempotent_thm (xs : List Int) : idempotent_prop xs := by
  exact List.Perm.eq_of_sorted (fun _ _ _ _ hab hba => le_antisymm hab hba)
    (sorted_thm (countingSort xs)) (sorted_thm xs) (permutation_thm (countingSort xs))

private theorem decode_valid (input : PyInput) : (decode input).isSome = pre input := by
  cases input with
  | nonList => rfl
  | list values =>
    induction values with
    | nil => rfl
    | cons value values ih =>
      cases value <;> cases hm : values.mapM PyValue.asInt <;>
        simp_all [decode, pre, PyValue.asInt, PyValue.isInteger, List.mapM_cons]

def validation_prop (input : PyInput) : Prop :=
  (checkedCountingSort input = .error "Input must be List[int]" ↔ ¬ DynamicPre input) ∧
  (∀ xs, decode input = some xs → checkedCountingSort input = .ok (countingSort xs))

theorem validation_thm (input : PyInput) : validation_prop input := by
  unfold validation_prop checkedCountingSort DynamicPre
  rw [← decode_valid]
  cases h : decode input <;> simp

/-- The output is a sorted permutation, retaining all multiplicities and length,
with the specified empty behavior and a stable result under repeated sorting. -/
def Post_prop (xs : List Int) : Prop :=
  sorted_prop xs ∧ permutation_prop xs ∧ multiplicity_prop xs ∧
  length_prop xs ∧ empty_prop xs ∧ idempotent_prop xs

-- Property-based tests. These computations provide test evidence independently
-- of the universal proofs above; no testing tactic is used to prove a theorem.

/-- Enumerate every list of length at most `n` over an alphabet. -/
def listsUpTo {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun x => (listsUpTo alphabet n).map (x :: ·))

/-- All 781 lists of length at most four with entries from -2 through 2. -/
def smallInputs : List (List Int) := listsUpTo [-2, -1, 0, 1, 2] 4

-- PBT for sorted_prop.
example : smallInputs.all (fun xs => decide ((countingSort xs).Pairwise (· ≤ ·))) = true := by
  native_decide
#eval Plausible.Testable.check
  (∀ xs : List Int, decide ((countingSort xs).Pairwise (· ≤ ·)) = true)
  { numInst := 200, maxSize := 30, randomSeed := some 2026091501 }

-- PBT for permutation_prop.
example : smallInputs.all (fun xs => decide ((countingSort xs).Perm xs)) = true := by
  native_decide
#eval Plausible.Testable.check
  (∀ xs : List Int, decide ((countingSort xs).Perm xs) = true)
  { numInst := 200, maxSize := 30, randomSeed := some 2026091502 }

-- PBT for multiplicity_prop: probe both present and absent values, including
-- integers outside the generated lists' range. Random tests quantify over x too.
example : smallInputs.all (fun xs =>
    ([-4, -3, -2, -1, 0, 1, 2, 3, 4] : List Int).all
      (fun x => (countingSort xs).count x == xs.count x)) = true := by native_decide
#eval Plausible.Testable.check
  (∀ (xs : List Int) (x : Int), (countingSort xs).count x = xs.count x)
  { numInst := 200, maxSize := 30, randomSeed := some 2026091503 }

-- PBT for length_prop.
example : smallInputs.all (fun xs => (countingSort xs).length == xs.length) = true := by
  native_decide
#eval Plausible.Testable.check
  (∀ xs : List Int, (countingSort xs).length = xs.length)
  { numInst := 200, maxSize := 30, randomSeed := some 2026091504 }

-- PBT for empty_prop.
example : smallInputs.all (fun xs => (countingSort xs).isEmpty == xs.isEmpty) = true := by
  native_decide
#eval Plausible.Testable.check
  (∀ xs : List Int, (countingSort xs).isEmpty = xs.isEmpty)
  { numInst := 200, maxSize := 30, randomSeed := some 2026091505 }

-- PBT for idempotent_prop.
example : smallInputs.all (fun xs => countingSort (countingSort xs) == countingSort xs) = true := by
  native_decide
#eval Plausible.Testable.check
  (∀ xs : List Int, countingSort (countingSort xs) = countingSort xs)
  { numInst := 200, maxSize := 30, randomSeed := some 2026091506 }

/-- The two clauses of validation_prop, as a Boolean computation. -/
def validationCheck (input : PyInput) : Bool :=
  (decide (checkedCountingSort input = .error "Input must be List[int]") == !pre input) &&
    match decode input with
    | none => true
    | some xs => decide (checkedCountingSort input = .ok (countingSort xs))

-- PBT for validation_prop. PyInput has no built-in Plausible sampler, so cover
-- the outer non-list case and all short lists over valid and invalid value tags.
def dynamicInputs : List PyInput :=
  .nonList :: (listsUpTo [.integer (-2), .integer 0, .integer 2,
    .boolean false, .boolean true, .nonInteger] 4).map PyInput.list
example : dynamicInputs.all validationCheck = true := by native_decide

/-- Executable form of the complete postcondition. Checking counts on the union
of input and output suffices: every other integer occurs zero times in both. -/
def postCheck (xs : List Int) : Bool :=
  let ys := countingSort xs
  decide (ys.Pairwise (· ≤ ·)) && decide (ys.Perm xs) &&
    (xs ++ ys).all (fun x => ys.count x == xs.count x) &&
    (ys.length == xs.length) && (ys.isEmpty == xs.isEmpty) && (countingSort ys == ys)

-- PBT for Post_prop.
example : smallInputs.all postCheck = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, postCheck xs = true)
  { numInst := 200, maxSize := 30, randomSeed := some 2026091507 }

theorem correctness_thm (xs : List Int) : Pre xs → Post_prop xs := by
  intro _
  exact ⟨sorted_thm xs, permutation_thm xs, multiplicity_thm xs,
    length_thm xs, empty_thm xs, idempotent_thm xs⟩

/-- Valid dynamic inputs decode successfully and inherit the full postcondition. -/
theorem dynamic_correctness_thm (input : PyInput) (h : DynamicPre input) :
    ∃ xs, decode input = some xs ∧ checkedCountingSort input = .ok (countingSort xs) ∧
      Post_prop xs := by
  have hd : (decode input).isSome = true := (decode_valid input).trans h
  cases he : decode input with
  | none => simp [he] at hd
  | some xs => exact ⟨xs, rfl, by simp [checkedCountingSort, he], correctness_thm xs trivial⟩

/-- The imperative version has a mutable count array and a mutable output list.
The two loops follow the Python counting and result-extension loops directly. -/
def countingSortImperative (xs : List Int) : List Int := Id.run do
  if xs.isEmpty then
    return []
  let lo := lower xs
  let size := rangeSize xs
  let mut counts := Array.replicate size 0
  for x in xs do
    counts := counts.modify (x - lo).toNat (· + 1)
  let mut result : List Int := []
  for i in List.range size do
    result := result ++ List.replicate counts[i]! (lo + (i : Int))
  return result

def checkedCountingSortImperative (input : PyInput) : Except String (List Int) :=
  match decode input with
  | none => .error "Input must be List[int]"
  | some xs => .ok (countingSortImperative xs)

-- Imperative unit tests and an exhaustive comparison on the bounded corpus.
example : countingSortImperative [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSortImperative [] = [] := by native_decide
example : countingSortImperative [1] = [1] := by native_decide
example : countingSortImperative [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSortImperative [-3, 0, -1, -3, 2] = [-3, -3, -1, 0, 2] := by native_decide
example : countingSortImperative [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : checkedCountingSortImperative (.list [.integer 1, .nonInteger]) =
    .error "Input must be List[int]" := by native_decide
example : smallInputs.all (fun xs => countingSort xs == countingSortImperative xs) = true := by
  native_decide
example : dynamicInputs.all (fun input =>
    decide (checkedCountingSort input = checkedCountingSortImperative input)) = true := by
  native_decide
#eval countingSortImperative [3, -1, 2, -1, 0]
#eval Plausible.Testable.check
  (∀ xs : List Int, countingSort xs = countingSortImperative xs)
  { numInst := 200, maxSize := 30, randomSeed := some 2026091508 }

/-- The mutable loops reduce to the pure histogram fold and bin expansion. -/
theorem equivalence_thm (xs : List Int) : countingSort xs = countingSortImperative xs := by
  unfold countingSort countingSortImperative
  split <;> simp_all [List.forIn_pure_yield_eq_foldl, histogram,
    List.foldl_append_eq_append, List.flatMap_def]
  rfl

theorem checked_equivalence_thm (input : PyInput) :
    checkedCountingSort input = checkedCountingSortImperative input := by
  unfold checkedCountingSort checkedCountingSortImperative
  cases decode input <;> simp [equivalence_thm]

end counting_sort
