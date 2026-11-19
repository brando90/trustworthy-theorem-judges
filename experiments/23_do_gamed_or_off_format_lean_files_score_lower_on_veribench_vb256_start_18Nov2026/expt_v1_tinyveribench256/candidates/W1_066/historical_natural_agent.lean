import Mathlib
namespace Agent

/-!
# A stable list of even integers

Translation of `pre` and `prog` from the Python program. `prog` is the
statically typed, unbounded-integer core. `checkedProg` also models dynamic
Python inputs and raises the `valueError` result on a precondition violation.
Runtime booleans are admitted, as Python's `bool` is a subclass of `int`;
filtering retains the original values (including `False`), not coerced copies.
`other` represents objects outside the explicitly listed builtin classes.
The error constructor records the exception class, not its diagnostic text.
Lean lists are immutable, so the returned list cannot mutate the input.
-/

namespace MyEvanList

/-! ## Functional implementation -/

def isEven (x : Int) : Bool := decide (x % 2 = 0)

def prog (xs : List Int) : List Int := xs.filter isEven

/-- A runtime-value model; floats are invalid even when numerically integral. -/
inductive PyValue where
  | int (n : Int)
  | bool (b : Bool)
  | float (x : Float)
  | str (s : String)
  | list (xs : List PyValue)
  | none
  | other (description : String)
  deriving Repr

inductive PyError where
  | valueError
  deriving Repr, DecidableEq

def isInteger : PyValue → Bool
  | .int _ => true
  | .bool _ => true
  | _ => false

def evenValue : PyValue → Bool
  | .int n => isEven n
  | .bool b => !b
  | _ => false

def pre : PyValue → Bool
  | .list xs => xs.all isInteger
  | _ => false

def checkedProg : PyValue → Except PyError (List PyValue)
  | .list xs =>
      if xs.all isInteger then .ok (xs.filter evenValue)
      else .error .valueError
  | _ => .error .valueError

/-- View integer lists as admissible runtime inputs. -/
def intInput (xs : List Int) : PyValue := .list (xs.map PyValue.int)

/-- Observe admitted values without comparing floats. The tag distinguishes
Python integers from booleans, so retention of the original value is tested.
All successful outputs contain only these two constructors. -/
def integerView : PyValue → Option (Int × Bool)
  | .int n => some (n, false)
  | .bool b => some (if b then 1 else 0, true)
  | _ => none

def isValueError : Except PyError (List PyValue) → Bool
  | .error .valueError => true
  | .ok _ => false

/-- Observable result retaining the exception/success distinction. -/
def resultView : Except PyError (List PyValue) → Option (List (Option (Int × Bool)))
  | .error _ => none
  | .ok xs => some (xs.map integerView)

/-! ## Fixed unit tests -/

example : prog [1, 2, 3, 4, 5, 6] = [2, 4, 6] := by native_decide
example : prog [] = [] := by native_decide
example : prog [1, 3, -5] = [] := by native_decide
example : prog [-4, -3, -2, -1, 0, 2, 2] = [-4, -2, 0, 2, 2] := by native_decide
#eval prog [1, 2, 3, 4, 5, 6]
#eval prog ([] : List Int)
#eval checkedProg (.list [.int 1, .float 2.5, .int 3])
#eval checkedProg (.list [.str "a", .str "b"])

-- The Python negative unit tests, checked by their exception class.
example : isValueError (checkedProg (.list [.int 1, .float 2.5, .int 3])) = true := by
  native_decide
example : isValueError (checkedProg (.list [.str "a", .str "b"])) = true := by
  native_decide
example : isValueError (checkedProg (.int 2)) = true := by native_decide
example : (match checkedProg (.list [.bool true, .bool false, .int 0]) with
    | .ok ys => ys.map integerView
    | .error _ => []) = [some (0, true), some (0, false)] := by native_decide

example : resultView (checkedProg (intInput [1, 2, 3, 4, 5, 6])) =
    some [some (2, false), some (4, false), some (6, false)] := by native_decide
example : resultView (checkedProg (intInput [])) = some [] := by native_decide
#eval checkedProg (intInput [1, 2, 3, 4, 5, 6])

/-! ## Preconditions -/

/-- Exactly Python's runtime list-of-integers check in the value model. -/
def Pre (v : PyValue) : Prop := pre v = true

/-! ## Properties of the typed core -/

def membership_prop (xs : List Int) : Prop :=
  ∀ x : Int, x ∈ prog xs ↔ x ∈ xs ∧ x % 2 = 0

theorem membership_thm (xs : List Int) : membership_prop xs := by
  intro x
  simp [prog, isEven]

def order_prop (xs : List Int) : Prop := (prog xs).Sublist xs

theorem order_thm (xs : List Int) : order_prop xs := by
  exact List.filter_sublist

def length_prop (xs : List Int) : Prop := (prog xs).length ≤ xs.length

theorem length_thm (xs : List Int) : length_prop xs := by
  exact (order_thm xs).length_le

def append_prop (xs ys : List Int) : Prop :=
  prog (xs ++ ys) = prog xs ++ prog ys

theorem append_thm (xs ys : List Int) : append_prop xs ys := by
  simp [append_prop, prog]

def multiplicity_prop (xs : List Int) : Prop :=
  ∀ x : Int, (prog xs).count x = if x % 2 = 0 then xs.count x else 0

theorem multiplicity_thm (xs : List Int) : multiplicity_prop xs := by
  intro x
  by_cases h : x % 2 = 0
  · simp only [if_pos h]
    exact List.count_filter (p := isEven) (by simp [isEven, h])
  · have hn : x ∉ prog xs := by
      simp [prog, isEven, h]
    simp [h, List.count_eq_zero.mpr hn]

def empty_prop (xs : List Int) : Prop :=
  prog xs = [] ↔ ∀ x ∈ xs, x % 2 ≠ 0

theorem empty_thm (xs : List Int) : empty_prop xs := by
  simp [empty_prop, prog, List.filter_eq_nil_iff, isEven]

def unchanged_prop (xs : List Int) : Prop :=
  prog xs = xs ↔ ∀ x ∈ xs, x % 2 = 0

theorem unchanged_thm (xs : List Int) : unchanged_prop xs := by
  simp [unchanged_prop, prog, List.filter_eq_self, isEven]

def idempotent_prop (xs : List Int) : Prop := prog (prog xs) = prog xs

theorem idempotent_thm (xs : List Int) : idempotent_prop xs := by
  simp [idempotent_prop, prog, List.filter_filter]

/-! ## Dynamic input and output properties -/

theorem pre_characterization_thm (v : PyValue) :
    Pre v ↔ ∃ xs, v = .list xs ∧ ∀ x ∈ xs, isInteger x = true := by
  cases v <;> simp [Pre, pre, List.all_eq_true]

/-- Every admitted input returns the exact stable filter, without coercing values. -/
def accepted_prop (v : PyValue) : Prop :=
  Pre v → ∃ xs, v = .list xs ∧ checkedProg v = .ok (xs.filter evenValue)

theorem accepted_thm (v : PyValue) : accepted_prop v := by
  intro h
  obtain ⟨xs, rfl, hx⟩ := (pre_characterization_thm v).mp h
  exact ⟨xs, rfl, by simp [checkedProg, List.all_eq_true.mpr hx]⟩

/-- Invalid inputs raise ValueError, and valid inputs never do. -/
def rejected_prop (v : PyValue) : Prop :=
  checkedProg v = .error .valueError ↔ ¬ Pre v

theorem rejected_thm (v : PyValue) : rejected_prop v := by
  cases v <;> simp [rejected_prop, checkedProg, Pre, pre]

/-- An exact sequence specification, with explicit order, membership, typing,
and length consequences. This also preserves duplicate occurrences. -/
def output_prop (v : PyValue) : Prop :=
  ∀ xs ys, v = .list xs → checkedProg v = .ok ys →
    ys = xs.filter evenValue ∧ ys.Sublist xs ∧
    (∀ x, x ∈ ys ↔ x ∈ xs ∧ evenValue x = true) ∧
    (∀ x ∈ ys, isInteger x = true) ∧ ys.length ≤ xs.length

theorem output_thm (v : PyValue) : output_prop v := by
  intro xs ys hv hr
  subst v
  by_cases h : xs.all isInteger = true
  · have heq : xs.filter evenValue = ys := by
      simpa [checkedProg, h] using hr
    subst ys
    refine ⟨rfl, List.filter_sublist, ?_, ?_, List.length_filter_le _ _⟩
    · intro x
      exact List.mem_filter
    · intro x hx
      exact (List.all_eq_true.mp h) x (List.mem_filter.mp hx).1
  · simp [checkedProg, h] at hr

/-- The typed and dynamically checked implementations agree on all integer lists. -/
theorem integer_bridge_thm (xs : List Int) :
    Pre (intInput xs) ∧ checkedProg (intInput xs) = .ok ((prog xs).map PyValue.int) := by
  constructor
  · simp [Pre, pre, intInput, isInteger]
  · simp [checkedProg, intInput, isInteger, prog, List.filter_map, Function.comp_def, evenValue]

/-! ## Postconditions (conjunctions of the preceding properties) -/

def CorePost_prop (xs : List Int) : Prop :=
  membership_prop xs ∧ order_prop xs ∧ length_prop xs ∧
  multiplicity_prop xs ∧ empty_prop xs ∧ unchanged_prop xs ∧ idempotent_prop xs

def Post_prop (v : PyValue) : Prop :=
  accepted_prop v ∧ rejected_prop v ∧ output_prop v

/-! ## Property-based tests

`listsUpTo` enumerates every list up to a fixed length over an alphabet.
The bounded tests include negative integers, zero, odd/even numbers and
repetitions. These are tests only; none is used in a theorem proof.
-/

def listsUpTo {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun x => (listsUpTo alphabet n).map (x :: ·))

def intAlphabet : List Int := [-2, -1, 0, 1, 2]
def intSamples : List (List Int) := listsUpTo intAlphabet 4

-- PBT for membership_prop: all bounded lists, and both present and absent probes.
example : intSamples.all (fun xs =>
    ([-3, -2, -1, 0, 1, 2, 3] : List Int).all (fun x =>
      decide (x ∈ prog xs ↔ x ∈ xs ∧ x % 2 = 0))) = true := by native_decide

-- PBT for order_prop.
example : intSamples.all (fun xs => decide ((prog xs).Sublist xs)) = true := by
  native_decide

-- PBT for length_prop.
example : intSamples.all (fun xs => decide ((prog xs).length ≤ xs.length)) = true := by
  native_decide

-- PBT for append_prop, with independently generated arbitrary integer lists.
#eval Plausible.Testable.check (∀ xs ys : List Int, prog (xs ++ ys) = prog xs ++ prog ys)

-- PBT for multiplicity_prop.
example : intSamples.all (fun xs =>
    ([-3, -2, -1, 0, 1, 2, 3] : List Int).all (fun x =>
      decide ((prog xs).count x = if x % 2 = 0 then xs.count x else 0))) = true := by
  native_decide

-- PBT for empty_prop.
example : intSamples.all (fun xs =>
    decide (prog xs = []) == xs.all (fun x => decide (x % 2 ≠ 0))) = true := by
  native_decide

-- PBT for unchanged_prop.
example : intSamples.all (fun xs =>
    decide (prog xs = xs) == xs.all isEven) = true := by native_decide

-- PBT for idempotent_prop.
example : intSamples.all (fun xs => decide (prog (prog xs) = prog xs)) = true := by
  native_decide

/-- Executable conjunction for CorePost_prop. Checking membership and counts
on the union of input and output suffices: elsewhere both counts are zero. -/
def corePostCheck (xs : List Int) : Bool :=
  let ys := prog xs
  (xs ++ ys).all (fun x => decide (x ∈ ys ↔ x ∈ xs ∧ x % 2 = 0)) &&
  decide (ys.Sublist xs) && decide (ys.length ≤ xs.length) &&
  (xs ++ ys).all (fun x => decide (ys.count x = if x % 2 = 0 then xs.count x else 0)) &&
  (decide (ys = []) == xs.all (fun x => decide (x % 2 ≠ 0))) &&
  (decide (ys = xs) == xs.all isEven) && decide (prog ys = ys)

-- PBT for the complete typed postcondition CorePost_prop.
example : intSamples.all corePostCheck = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, corePostCheck xs = true)

def runtimeAlphabet : List PyValue :=
  [.int (-4), .int (-3), .int 0, .int 2, .bool false, .bool true,
   .float 2.5, .float 2.0, .str "a", .none, .list [], .other "tuple"]

def runtimeSamples : List PyValue :=
  runtimeAlphabet ++ (listsUpTo runtimeAlphabet 3).map PyValue.list

def acceptedCheck (v : PyValue) : Bool :=
  if pre v then
    match v, checkedProg v with
    | .list xs, .ok ys => decide (ys.map integerView = (xs.filter evenValue).map integerView)
    | _, _ => false
  else true

def rejectedCheck (v : PyValue) : Bool :=
  isValueError (checkedProg v) == !pre v

def outputCheck (v : PyValue) : Bool :=
  match v, checkedProg v with
  | .list xs, .ok ys =>
      decide (ys.map integerView = (xs.filter evenValue).map integerView) &&
      decide ((ys.map integerView).Sublist (xs.map integerView)) &&
      (xs ++ ys).all (fun x =>
        decide (integerView x ∈ ys.map integerView) ==
          (decide (integerView x ∈ xs.map integerView) && evenValue x)) &&
      ys.all isInteger && decide (ys.length ≤ xs.length)
  | _, .error _ => true
  | _, .ok _ => false

-- PBT for accepted_prop, including integer and boolean lists and invalid inputs.
example : runtimeSamples.all acceptedCheck = true := by native_decide
-- PBT for rejected_prop, including nested lists and integral-valued floats.
example : runtimeSamples.all rejectedCheck = true := by native_decide
-- PBT for output_prop, checking the complete sequence and its consequences.
example : runtimeSamples.all outputCheck = true := by native_decide
-- PBT for Post_prop: the conjunction of its three executable checks.
example : runtimeSamples.all (fun v =>
    acceptedCheck v && rejectedCheck v && outputCheck v) = true := by native_decide
#eval runtimeSamples.length

/-! ## Correctness -/

theorem core_correctness_thm (xs : List Int) : CorePost_prop xs := by
  exact ⟨membership_thm xs, order_thm xs, length_thm xs, multiplicity_thm xs,
    empty_thm xs, unchanged_thm xs, idempotent_thm xs⟩

/-- The requested precondition-to-postcondition theorem for dynamic inputs. -/
theorem correctness_thm (v : PyValue) : Pre v → Post_prop v := by
  intro _
  exact ⟨accepted_thm v, rejected_thm v, output_thm v⟩

/-! ## Imperative implementation

The loops traverse left to right. `out` appends selected elements, preserving
order and duplicate occurrences; `valid` accumulates the runtime type check.
-/

def filterImperative {α : Type} (p : α → Bool) (xs : List α) : List α := Id.run do
  let mut out : List α := []
  for x in xs do
    out := if p x then out ++ [x] else out
  return out

def allImperative {α : Type} (p : α → Bool) (xs : List α) : Bool := Id.run do
  let mut valid := true
  for x in xs do
    valid := valid && p x
  return valid

def progImperative (xs : List Int) : List Int := filterImperative isEven xs

def checkedProgImperative (v : PyValue) : Except PyError (List PyValue) := Id.run do
  match v with
  | .list xs =>
      let valid := allImperative isInteger xs
      if valid then
        return .ok (filterImperative evenValue xs)
      else
        return .error .valueError
  | _ => return .error .valueError

/-! ## Imperative tests -/

example : progImperative [1, 2, 3, 4, 5, 6] = [2, 4, 6] := by native_decide
example : progImperative [] = [] := by native_decide
example : progImperative [1, 3, -5] = [] := by native_decide
example : progImperative [-4, -3, -2, -1, 0, 2, 2] = [-4, -2, 0, 2, 2] := by
  native_decide
example : resultView (checkedProgImperative (intInput [1, 2, 3, 4, 5, 6])) =
    some [some (2, false), some (4, false), some (6, false)] := by native_decide
example : resultView (checkedProgImperative (intInput [])) = some [] := by native_decide
example : isValueError (checkedProgImperative (.list [.int 1, .float 2.5, .int 3])) =
    true := by native_decide
example : isValueError (checkedProgImperative (.list [.str "a", .str "b"])) =
    true := by native_decide
example : isValueError (checkedProgImperative (.str "not a list")) = true := by
  native_decide
example : resultView (checkedProgImperative (.list [.bool true, .bool false, .int 0])) =
    some [some (0, true), some (0, false)] := by native_decide
#eval progImperative [1, 2, 3, 4, 5, 6]
#eval checkedProgImperative (.list [.str "a", .str "b"])

-- Additional bounded cross-implementation tests, separate from the proofs.
example : intSamples.all (fun xs => decide (prog xs = progImperative xs)) = true := by
  native_decide
example : runtimeSamples.all (fun v =>
    decide (resultView (checkedProg v) = resultView (checkedProgImperative v))) = true := by
  native_decide

/-! ## Kernel proofs of loop invariants and equivalence -/

theorem filter_accumulator_thm {α : Type} (p : α → Bool) (xs acc : List α) :
    xs.foldl (fun out x => if p x then out ++ [x] else out) acc = acc ++ xs.filter p := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    cases h : p x <;> simp [List.foldl_cons, h, ih, List.append_assoc]

theorem filterImperative_eq_filter_thm {α : Type} (p : α → Bool) (xs : List α) :
    filterImperative p xs = xs.filter p := by
  simp [filterImperative, List.forIn_pure_yield_eq_foldl, filter_accumulator_thm]

theorem validation_accumulator_thm {α : Type} (p : α → Bool) (xs : List α) (acc : Bool) :
    xs.foldl (fun valid x => valid && p x) acc = (acc && xs.all p) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, Bool.and_assoc]

theorem allImperative_eq_all_thm {α : Type} (p : α → Bool) (xs : List α) :
    allImperative p xs = xs.all p := by
  simp [allImperative, List.forIn_pure_yield_eq_foldl, validation_accumulator_thm]

/-- Equivalence on the complete, unbounded integer-list domain. -/
theorem equivalence_thm (xs : List Int) : prog xs = progImperative xs := by
  simpa [prog, progImperative] using (filterImperative_eq_filter_thm isEven xs).symm

/-- Equivalence includes invalid inputs, booleans, and the ValueError branch. -/
theorem checked_equivalence_thm (v : PyValue) :
    checkedProg v = checkedProgImperative v := by
  cases v <;>
    simp [checkedProg, checkedProgImperative,
      allImperative_eq_all_thm, filterImperative_eq_filter_thm]
  split <;> simp_all

end MyEvanList
end Agent
