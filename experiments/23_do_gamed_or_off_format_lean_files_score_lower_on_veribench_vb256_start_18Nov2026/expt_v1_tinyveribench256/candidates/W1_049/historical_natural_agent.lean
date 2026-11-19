import Mathlib
namespace Agent

/-!
# Counting integers divisible by seven and eight

The functional core models Python's arbitrary-precision integers by `Int`, and
its nonnegative count by `Nat`. Repeated elements are counted separately; zero
and negative multiples are included. A dynamic-value boundary also models the
`List[int]` validation and the `ValueError` branch. Python booleans are accepted
there because `bool` is a subclass of `int` (False = 0, True = 1).

`other` represents any remaining non-integer, non-list Python value; its label
has no computational significance. Thus invalid values are not silently removed
from the input. Proofs below are kernel proofs; native evaluation is used only
for executable tests.
-/

namespace DivisibleBySevenAndEightCount

/-! ## Functional implementation and checked Python boundary -/

def divisibleByBoth (x : Int) : Bool := x % 7 == 0 && x % 8 == 0

def count_div_by_7_and_8 : List Int → Nat
  | [] => 0
  | x :: xs => (if divisibleByBoth x then 1 else 0) + count_div_by_7_and_8 xs

inductive PyValue where
  | int (value : Int)
  | bool (value : Bool)
  | str (value : String)
  | list (values : List PyValue)
  | other (description : String)
  deriving Repr

deriving instance DecidableEq for Except

-- Independent implementation of Python's isinstance checks.
def isInteger : PyValue → Bool
  | .int _ => true
  | .bool _ => true
  | _ => false

def pythonPre : PyValue → Bool
  | .list xs => xs.all isInteger
  | _ => false

def asInt : PyValue → Option Int
  | .int n => some n
  | .bool false => some 0
  | .bool true => some 1
  | _ => none

def asIntList : PyValue → Option (List Int)
  | .list xs => xs.mapM asInt
  | _ => none

def fromInts (xs : List Int) : PyValue := .list (xs.map PyValue.int)

def valueError : String := "Input must be List[int]"

def checkedCount (v : PyValue) : Except String Nat :=
  match asIntList v with
  | none => .error valueError
  | some xs => .ok (count_div_by_7_and_8 xs)

/-! ## Unit tests -/

example : count_div_by_7_and_8 [56, 14, 28, 112] = 2 := by native_decide
example : count_div_by_7_and_8 [1, 2, 3, 4] = 0 := by native_decide
example : count_div_by_7_and_8 [0, 56, 84] = 2 := by native_decide
example : count_div_by_7_and_8 [] = 0 := by native_decide
example : count_div_by_7_and_8 [-112, -56, -8, -7, 0, 56, 56] = 5 := by native_decide
example : checkedCount (.list [.int 56, .str "x"]) = .error valueError := by native_decide
example : checkedCount (.int 56) = .error valueError := by native_decide
example : checkedCount (.list [.list []]) = .error valueError := by native_decide
example : checkedCount (.list [.bool false, .bool true, .int 56]) = .ok 2 := by native_decide
example : checkedCount (fromInts []) = .ok 0 := by native_decide

#eval count_div_by_7_and_8 [56, 14, 28, 112]
#eval count_div_by_7_and_8 []
#eval checkedCount (.list [.int 56, .str "x"])

/-! ## Preconditions

The type `List Int` already enforces the Python precondition on the core.
`InputPre` is the corresponding dynamic precondition at the checked boundary.
-/

def Pre (_xs : List Int) : Prop := True

def InputPre (v : PyValue) : Prop := pythonPre v = true

/-! ## Properties and kernel-checked proofs -/

def exact_count_prop (xs : List Int) : Prop :=
  count_div_by_7_and_8 xs = (xs.filter divisibleByBoth).length

theorem exact_count_thm (xs : List Int) : exact_count_prop xs := by
  unfold exact_count_prop
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : divisibleByBoth x <;> simp [count_div_by_7_and_8, h, ih, Nat.add_comm]

def bounds_prop (xs : List Int) : Prop :=
  0 ≤ count_div_by_7_and_8 xs ∧ count_div_by_7_and_8 xs ≤ xs.length

theorem bounds_thm (xs : List Int) : bounds_prop xs := by
  refine ⟨Nat.zero_le _, ?_⟩
  rw [show count_div_by_7_and_8 xs = (xs.filter divisibleByBoth).length from exact_count_thm xs]
  exact List.length_filter_le _ _

-- Divisibility, not just a syntactic test of the implementation.
theorem divisibleByBoth_iff (x : Int) :
    divisibleByBoth x = true ↔ (7 : Int) ∣ x ∧ (8 : Int) ∣ x := by
  simp only [divisibleByBoth, Bool.and_eq_true, beq_iff_eq, Int.dvd_iff_emod_eq_zero]

theorem divisibleByBoth_iff_mod56 (x : Int) :
    divisibleByBoth x = true ↔ x % 56 = 0 := by
  simp only [divisibleByBoth, Bool.and_eq_true, beq_iff_eq]
  omega

def multiple_56_prop (xs : List Int) : Prop :=
  count_div_by_7_and_8 xs = (xs.filter (fun x => x % 56 == 0)).length

theorem multiple_56_thm (xs : List Int) : multiple_56_prop xs := by
  unfold multiple_56_prop
  rw [show count_div_by_7_and_8 xs = (xs.filter divisibleByBoth).length from exact_count_thm xs]
  congr 1
  apply List.filter_congr
  intro x _
  exact Bool.eq_iff_iff.mpr (by simpa using divisibleByBoth_iff_mod56 x)

def step_prop (x : Int) (xs : List Int) : Prop :=
  count_div_by_7_and_8 (x :: xs) = count_div_by_7_and_8 xs +
    (if x % 7 = 0 ∧ x % 8 = 0 then 1 else 0)

theorem step_thm (x : Int) (xs : List Int) : step_prop x xs := by
  simp [step_prop, count_div_by_7_and_8, divisibleByBoth, Nat.add_comm]

def append_prop (xs ys : List Int) : Prop :=
  count_div_by_7_and_8 (xs ++ ys) = count_div_by_7_and_8 xs + count_div_by_7_and_8 ys

theorem append_thm (xs ys : List Int) : append_prop xs ys := by
  unfold append_prop
  induction xs with
  | nil => simp [count_div_by_7_and_8]
  | cons x xs ih => simp [count_div_by_7_and_8, ih, Nat.add_assoc]

def zero_prop (xs : List Int) : Prop :=
  count_div_by_7_and_8 xs = 0 ↔ ∀ x ∈ xs, ¬ ((7 : Int) ∣ x ∧ (8 : Int) ∣ x)

theorem zero_thm (xs : List Int) : zero_prop xs := by
  unfold zero_prop
  rw [show count_div_by_7_and_8 xs = (xs.filter divisibleByBoth).length from exact_count_thm xs]
  simp [List.filter_eq_nil_iff, divisibleByBoth_iff]

private theorem decode_elements_isSome (vs : List PyValue) :
    (vs.mapM asInt).isSome = vs.all isInteger := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases v with
    | bool b =>
      cases b <;> cases h : vs.mapM asInt <;>
        simp_all [List.mapM_cons, asInt, isInteger]
    | int n =>
      cases h : vs.mapM asInt <;> simp_all [List.mapM_cons, asInt, isInteger]
    | str s => simp [List.mapM_cons, asInt, isInteger]
    | list ws => simp [List.mapM_cons, asInt, isInteger]
    | other s => simp [List.mapM_cons, asInt, isInteger]

-- The type-checking predicate is specified independently of the decoder.
def precondition_prop (v : PyValue) : Prop :=
  InputPre v ↔ ∃ xs, asIntList v = some xs

theorem precondition_thm (v : PyValue) : precondition_prop v := by
  have h : (asIntList v).isSome = pythonPre v := by
    cases v <;> simp [asIntList, pythonPre, decode_elements_isSome]
  unfold precondition_prop InputPre
  rw [← h]
  cases asIntList v <;> simp

private theorem decode_fromInts (xs : List Int) :
    asIntList (fromInts xs) = some xs := by
  unfold asIntList fromInts
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, asInt, ih]

def embedding_prop (xs : List Int) : Prop :=
  checkedCount (fromInts xs) = .ok (count_div_by_7_and_8 xs)

theorem embedding_thm (xs : List Int) : embedding_prop xs := by
  simp [embedding_prop, checkedCount, decode_fromInts]

def validation_prop (v : PyValue) : Prop :=
  checkedCount v = .error valueError ↔ ¬ InputPre v

theorem validation_thm (v : PyValue) : validation_prop v := by
  unfold validation_prop
  rw [show InputPre v ↔ ∃ xs, asIntList v = some xs from precondition_thm v]
  unfold checkedCount
  cases h : asIntList v <;> simp

/-! ## Postcondition -/

def Post_prop (xs : List Int) : Prop :=
  exact_count_prop xs ∧ bounds_prop xs ∧ multiple_56_prop xs ∧ zero_prop xs

/-! ## Bounded property-based tests

All lists of length at most three over this signed alphabet are tested, including
zero, duplicate values, and positive/negative multiples and nonmultiples. The
executable forms do not depend on classical decidability of specifications.
-/

def testAlphabet : List Int := [-112, -56, -8, -7, -1, 0, 1, 7, 8, 56, 112]

def listsOfLength : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => testAlphabet.flatMap (fun x => (listsOfLength n).map (List.cons x))

def testLists : List (List Int) :=
  (List.range 4).flatMap listsOfLength

def shortLists : List (List Int) :=
  (List.range 3).flatMap listsOfLength

-- exact_count_prop
example : testLists.all (fun xs =>
    count_div_by_7_and_8 xs == (xs.filter divisibleByBoth).length) = true := by native_decide

-- bounds_prop (the lower bound is also explicit, although the result is a Nat).
example : testLists.all (fun xs =>
    decide (0 ≤ count_div_by_7_and_8 xs ∧ count_div_by_7_and_8 xs ≤ xs.length)) = true := by native_decide

-- multiple_56_prop, testing a predicate independent of the core's predicate.
example : testLists.all (fun xs =>
    count_div_by_7_and_8 xs == (xs.filter (fun x => x % 56 == 0)).length) = true := by native_decide

-- step_prop
example : testAlphabet.all (fun x => testLists.all (fun xs =>
    count_div_by_7_and_8 (x :: xs) == count_div_by_7_and_8 xs +
      (if x % 7 = 0 ∧ x % 8 = 0 then 1 else 0))) = true := by native_decide

-- append_prop
example : shortLists.all (fun xs => shortLists.all (fun ys =>
    count_div_by_7_and_8 (xs ++ ys) == count_div_by_7_and_8 xs + count_div_by_7_and_8 ys)) = true := by native_decide

-- zero_prop: finite universal quantification is executable as List.all.
example : testLists.all (fun xs =>
    (count_div_by_7_and_8 xs == 0) == xs.all (fun x => !(decide ((7 : Int) ∣ x ∧ (8 : Int) ∣ x)))) = true := by native_decide

def dynamicTests : List PyValue :=
  testLists.map fromInts ++
  testLists.map (fun xs => .list (xs.map PyValue.int ++ [.str "x"])) ++
  [.int 56, .str "not a list", .other "None", .list [.list []],
   .list [.bool false], .list [.bool true, .int 56]]

-- precondition_prop: check the independent isinstance model against decoding.
example : dynamicTests.all (fun v =>
    pythonPre v == (asIntList v).isSome) = true := by native_decide

-- embedding_prop: the dynamic boundary agrees with the integer-list core.
example : testLists.all (fun xs => decide
    (checkedCount (fromInts xs) = .ok (count_div_by_7_and_8 xs))) = true := by native_decide

-- validation_prop: test the precise exception message, not merely any error.
example : dynamicTests.all (fun v =>
    decide (checkedCount v = .error valueError) == !pythonPre v) = true := by native_decide

-- Auxiliary arithmetic correspondences, densely tested on signed integers.
example : (List.range 337).all (fun n =>
    let x : Int := (n : Int) - 168
    (divisibleByBoth x == decide ((7 : Int) ∣ x ∧ (8 : Int) ∣ x)) &&
    (divisibleByBoth x == (x % 56 == 0))) = true := by native_decide

-- Post_prop: all four conjuncts, including both directions of the zero criterion.
example : testLists.all (fun xs =>
    (count_div_by_7_and_8 xs == (xs.filter divisibleByBoth).length) &&
    decide (0 ≤ count_div_by_7_and_8 xs ∧ count_div_by_7_and_8 xs ≤ xs.length) &&
    (count_div_by_7_and_8 xs == (xs.filter (fun x => x % 56 == 0)).length) &&
    ((count_div_by_7_and_8 xs == 0) == xs.all (fun x => !(decide ((7 : Int) ∣ x ∧ (8 : Int) ∣ x))))) = true := by native_decide

#eval testLists.length
#eval testLists.all (fun xs => count_div_by_7_and_8 xs ≤ xs.length)

/-! ## Correctness -/

theorem correctness_thm (xs : List Int) (_h : Pre xs) : Post_prop xs := by
  exact ⟨exact_count_thm xs, bounds_thm xs, multiple_56_thm xs, zero_thm xs⟩

-- The checked boundary returns exactly the core's answer on every accepted input.
theorem checked_correctness_thm (v : PyValue) (h : InputPre v) :
    ∃ xs, asIntList v = some xs ∧
      checkedCount v = .ok (count_div_by_7_and_8 xs) ∧ Post_prop xs := by
  obtain ⟨xs, hxs⟩ := (precondition_thm v).mp h
  exact ⟨xs, hxs, by simp [checkedCount, hxs], correctness_thm xs trivial⟩

/-! ## Imperative implementation -/

def countImperative (xs : List Int) : Nat := Id.run do
  let mut count := 0
  for x in xs do
    if divisibleByBoth x then
      count := count + 1
  return count

def checkedCountImperative (v : PyValue) : Except String Nat :=
  match asIntList v with
  | none => .error valueError
  | some xs => .ok (countImperative xs)

/-! ## Imperative tests -/

example : countImperative [56, 14, 28, 112] = 2 := by native_decide
example : countImperative [] = 0 := by native_decide
example : countImperative [-56, 0, 56, 8, 7] = 3 := by native_decide
example : checkedCountImperative (.list [.int 56, .str "x"]) = .error valueError := by native_decide
example : checkedCountImperative (fromInts [56, 14, 28, 112]) = .ok 2 := by native_decide
#eval countImperative [0, 56, 84]
#eval checkedCountImperative (.list [.int 56, .str "x"])

-- Bounded PBT for the functional/imperative equivalence.
example : testLists.all (fun xs => count_div_by_7_and_8 xs == countImperative xs) = true := by native_decide

example : dynamicTests.all (fun v =>
    decide (checkedCount v = checkedCountImperative v)) = true := by native_decide

/-! ## Functional/imperative equivalence -/

-- The accumulator counts the already processed prefix; the remaining suffix
-- contributes exactly its functional count.
private theorem loop_invariant (xs : List Int) (acc : Nat) :
    (forIn xs acc (fun x n =>
      (if divisibleByBoth x then pure (ForInStep.yield (n + 1))
       else pure (ForInStep.yield n) : Id (ForInStep Nat)))).run =
      acc + count_div_by_7_and_8 xs := by
  induction xs generalizing acc with
  | nil => simp [count_div_by_7_and_8]
  | cons x xs ih =>
    cases h : divisibleByBoth x <;>
      simp [List.forIn_cons, h, count_div_by_7_and_8, ih, Nat.add_assoc]

theorem functional_eq_imperative_thm (xs : List Int) :
    count_div_by_7_and_8 xs = countImperative xs := by
  simpa [countImperative] using (loop_invariant xs 0).symm

-- Equivalence includes rejection of invalid values, not only successful counts.
theorem checked_functional_eq_imperative_thm (v : PyValue) :
    checkedCount v = checkedCountImperative v := by
  unfold checkedCount checkedCountImperative
  cases asIntList v with
  | none => rfl
  | some xs => simp only [functional_eq_imperative_thm]

end DivisibleBySevenAndEightCount
end Agent
