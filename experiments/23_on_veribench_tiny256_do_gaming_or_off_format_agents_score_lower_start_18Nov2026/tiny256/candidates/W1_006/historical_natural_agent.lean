import Mathlib
namespace Agent

/-!
# Linear search for the first occurrence

The functional and imperative implementations search a list of natural numbers,
returning the first matching zero-based index, or `none` when the target is absent.
`List Nat` and `Nat` encode Python's admissible input domain: negative integers,
booleans and nonintegers are not inputs to this typed interface.
-/

namespace linear_search

/-- Search the head first; shift a tail result by one. -/
def linearSearch : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: xs, target =>
      if x = target then some 0 else (linearSearch xs target).map Nat.succ

-- The successful, absent, empty, and duplicate cases from the Python tests.
example : linearSearch [4, 2, 7, 9] 7 = some 2 := by native_decide
example : linearSearch [] 5 = none := by native_decide
example : linearSearch [3, 1, 3, 5] 3 = some 0 := by native_decide
example : linearSearch [3, 1, 3, 5] 4 = none := by native_decide
example : linearSearch [9, 4, 9, 1] 9 = some 0 := by native_decide
example : linearSearch [9, 4, 9, 1] 1 = some 3 := by native_decide
example : linearSearch [9, 4, 9, 1] 2 = none := by native_decide
example : linearSearch [5, 0, 5, 7, 5] 5 = some 0 ∧
    ([5, 0, 5, 7, 5] : List Nat)[0]? = some 5 := by native_decide
example : linearSearch [5, 0, 5, 7, 5] 0 = some 1 := by native_decide
example : linearSearch [5, 0, 5, 7, 5] 8 = none := by native_decide
#eval linearSearch [4, 2, 7, 9] 7
#eval linearSearch [] 5
#eval linearSearch [3, 1, 3, 5] 3

/-- The types enforce exactly the natural-number input precondition. -/
def Pre (_xs : List Nat) (_target : Nat) : Prop := True

/-- A returned index is within the list. -/
def bounds_prop (xs : List Nat) (target : Nat) : Prop :=
  ∀ i, linearSearch xs target = some i → i < xs.length

/-- A returned index points to the requested target. -/
def sound_prop (xs : List Nat) (target : Nat) : Prop :=
  ∀ i, linearSearch xs target = some i → xs[i]? = some target

/-- No smaller index contains the target. -/
def first_prop (xs : List Nat) (target : Nat) : Prop :=
  ∀ i, linearSearch xs target = some i → ∀ j, j < i → xs[j]? ≠ some target

/-- Failure is equivalent to absence, not merely implied by it. -/
def absent_prop (xs : List Nat) (target : Nat) : Prop :=
  linearSearch xs target = none ↔ target ∉ xs

/-- A target occurs if and only if a successful result exists. -/
def complete_prop (xs : List Nat) (target : Nat) : Prop :=
  target ∈ xs ↔ ∃ i, linearSearch xs target = some i

/-- The induction invariant describing every successful recursive search. -/
theorem search_some_spec (xs : List Nat) (target : Nat) :
    ∀ i, linearSearch xs target = some i →
      i < xs.length ∧ xs[i]? = some target ∧
        ∀ j, j < i → xs[j]? ≠ some target := by
  induction xs with
  | nil => simp [linearSearch]
  | cons x xs ih =>
      intro i hi
      by_cases hx : x = target
      · simp [linearSearch, hx] at hi
        subst i
        simp [hx]
      · simp only [linearSearch, if_neg hx, Option.map_eq_some_iff] at hi
        obtain ⟨k, hk, rfl⟩ := hi
        obtain ⟨hb, hm, hf⟩ := ih k hk
        refine ⟨Nat.succ_lt_succ hb, ?_, ?_⟩
        · simpa using hm
        · intro j hj
          cases j with
          | zero => simpa using hx
          | succ j => simpa using hf j (Nat.lt_of_succ_lt_succ hj)

theorem bounds_thm (xs : List Nat) (target : Nat) : bounds_prop xs target := by
  intro i hi
  exact (search_some_spec xs target i hi).1

theorem sound_thm (xs : List Nat) (target : Nat) : sound_prop xs target := by
  intro i hi
  exact (search_some_spec xs target i hi).2.1

theorem first_thm (xs : List Nat) (target : Nat) : first_prop xs target := by
  intro i hi
  exact (search_some_spec xs target i hi).2.2

theorem absent_thm (xs : List Nat) (target : Nat) : absent_prop xs target := by
  unfold absent_prop
  induction xs with
  | nil => simp [linearSearch]
  | cons x xs ih =>
      by_cases hx : x = target
      · simp [linearSearch, hx]
      · simp [linearSearch, hx, ih, Ne.symm hx]

theorem complete_thm (xs : List Nat) (target : Nat) : complete_prop xs target := by
  unfold complete_prop
  constructor
  · intro hm
    cases hs : linearSearch xs target with
    | none => exact False.elim ((absent_thm xs target).mp hs hm)
    | some i => exact ⟨i, rfl⟩
  · rintro ⟨i, hi⟩
    exact List.mem_iff_getElem?.mpr ⟨i, sound_thm xs target i hi⟩

/-- Total first-occurrence correctness, including failure and completeness. -/
def Post_prop (xs : List Nat) (target : Nat) : Prop :=
  bounds_prop xs target ∧ sound_prop xs target ∧ first_prop xs target ∧
    absent_prop xs target ∧ complete_prop xs target

/-! ## Property-based tests

These executable forms inspect the actual returned option. Universally quantified
indices in the successful-result properties become a single result inspection;
minimality checks all the smaller indices. The finite corpus contains *every*
list of length at most four over 0..4 and every target in 0..6, including absent
targets, empty lists, zeros, and duplicate occurrences (5,467 input pairs).
No additional precondition filtering is needed for `List Nat × Nat`.
-/

def boundsCheck (xs : List Nat) (target : Nat) : Bool :=
  match linearSearch xs target with
  | none => true
  | some i => decide (i < xs.length)

def soundCheck (xs : List Nat) (target : Nat) : Bool :=
  match linearSearch xs target with
  | none => true
  | some i => decide (xs[i]? = some target)

def firstCheck (xs : List Nat) (target : Nat) : Bool :=
  match linearSearch xs target with
  | none => true
  | some i => (List.range i).all fun j => decide (xs[j]? ≠ some target)

def absentCheck (xs : List Nat) (target : Nat) : Bool :=
  decide (linearSearch xs target = none ↔ target ∉ xs)

def completeCheck (xs : List Nat) (target : Nat) : Bool :=
  xs.contains target == (linearSearch xs target).isSome

def postCheck (xs : List Nat) (target : Nat) : Bool :=
  boundsCheck xs target && soundCheck xs target && firstCheck xs target &&
    absentCheck xs target && completeCheck xs target

/-- Exhaustively generate all lists up to the given length over five naturals. -/
def testLists : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => [] :: (List.range 5).flatMap (fun x => (testLists n).map (x :: ·))

def checkCases (p : List Nat → Nat → Bool) : Bool :=
  (testLists 4).all fun xs => (List.range 7).all (p xs)

-- PBT for bounds_prop.
example : checkCases boundsCheck = true := by native_decide
-- PBT for sound_prop.
example : checkCases soundCheck = true := by native_decide
-- PBT for first_prop.
example : checkCases firstCheck = true := by native_decide
-- PBT for absent_prop.
example : checkCases absentCheck = true := by native_decide
-- PBT for complete_prop.
example : checkCases completeCheck = true := by native_decide
-- PBT for the entire Post_prop conjunction.
example : checkCases postCheck = true := by native_decide
#eval checkCases postCheck

/-- The precondition implies all of the postcondition, for arbitrary inputs. -/
theorem correctness_thm (xs : List Nat) (target : Nat) :
    Pre xs target → Post_prop xs target := by
  intro _
  exact ⟨bounds_thm xs target, sound_thm xs target, first_thm xs target,
    absent_thm xs target, complete_thm xs target⟩

/-! ## Imperative implementation

The mutable counter and early return follow Python's enumeration loop. The
internal starting offset permits an induction over the remaining input list;
the public entry point always starts at zero.
-/

def linearSearchImperativeFrom (xs : List Nat) (target start : Nat) : Option Nat := Id.run do
  let mut idx := start
  for x in xs do
    if x = target then
      return some idx
    idx := idx + 1
  return none

def linearSearchImperative (xs : List Nat) (target : Nat) : Option Nat :=
  linearSearchImperativeFrom xs target 0

example : linearSearchImperative [4, 2, 7, 9] 7 = some 2 := by native_decide
example : linearSearchImperative [] 5 = none := by native_decide
example : linearSearchImperative [3, 1, 3, 5] 3 = some 0 := by native_decide
example : linearSearchImperative [3, 1, 3, 5] 4 = none := by native_decide
example : linearSearchImperative [9, 4, 9, 1] 9 = some 0 := by native_decide
example : linearSearchImperative [9, 4, 9, 1] 1 = some 3 := by native_decide
example : linearSearchImperative [9, 4, 9, 1] 2 = none := by native_decide
example : linearSearchImperative [5, 0, 5, 7, 5] 5 = some 0 ∧
    ([5, 0, 5, 7, 5] : List Nat)[0]? = some 5 := by native_decide
example : linearSearchImperative [5, 0, 5, 7, 5] 0 = some 1 := by native_decide
example : linearSearchImperative [5, 0, 5, 7, 5] 8 = none := by native_decide
#eval linearSearchImperative [4, 2, 7, 9] 7
#eval linearSearchImperative [] 5
#eval linearSearchImperative [3, 1, 3, 5] 3
example : checkCases (fun xs target =>
    decide (linearSearch xs target = linearSearchImperative xs target)) = true := by
  native_decide

private theorem imperativeFrom_nil (target start : Nat) :
    linearSearchImperativeFrom [] target start = none := by
  simp [linearSearchImperativeFrom]

private theorem imperativeFrom_cons (x target start : Nat) (xs : List Nat) :
    linearSearchImperativeFrom (x :: xs) target start =
      if x = target then some start else linearSearchImperativeFrom xs target (start + 1) := by
  by_cases hx : x = target <;> simp [linearSearchImperativeFrom, List.forIn_cons, hx]

/-- The loop returns the functional result shifted by its starting counter. -/
theorem imperativeFrom_eq (xs : List Nat) (target start : Nat) :
    linearSearchImperativeFrom xs target start =
      (linearSearch xs target).map (fun i => start + i) := by
  induction xs generalizing start with
  | nil => simp [imperativeFrom_nil, linearSearch]
  | cons x xs ih =>
      rw [imperativeFrom_cons]
      by_cases hx : x = target
      · simp [hx, linearSearch]
      · simp [linearSearch, hx, ih, Option.map_map, Function.comp_def,
          Nat.add_comm, Nat.add_left_comm]

/-- The two implementations agree on the entire admissible domain. -/
theorem equivalence_thm (xs : List Nat) (target : Nat) :
    linearSearch xs target = linearSearchImperative xs target := by
  simpa [linearSearchImperative] using (imperativeFrom_eq xs target 0).symm

end linear_search
end Agent
