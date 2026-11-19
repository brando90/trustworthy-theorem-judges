import Mathlib
namespace Agent

/-!
# Python integer-list reversal

`myReverse` is the total list operation underlying `xs[::-1]`. `prog` models
Python's dynamic boundary, including rejection of non-lists and lists containing
non-integers. Python `bool` is a subclass of `int`, so booleans are accepted and
preserved rather than coerced. `PyValue.other` represents any remaining Python
value (its descriptive string is immaterial to validation). Thus floats, strings,
tuples, dictionaries, etc. are all rejected in precisely the same way. The error
model records the ValueError exception class, abstracting its diagnostic message.
Integers are mathematical, unbounded `Int`s. Tests are executable evidence; all
named theorems have separate kernel-checked proofs.
-/

namespace MyReverse

/-- The observations of Python values needed by this program. -/
inductive PyValue where
  | int (value : Int)
  | bool (value : Bool)
  | list (values : List PyValue)
  | other (description : String)
  deriving Repr

-- Computable structural equality for this nested datatype.
mutual
  def valueDecEq : (a b : PyValue) → Decidable (a = b)
    | .int a, .int b =>
        match decEq a b with
        | .isTrue h => .isTrue (congrArg PyValue.int h)
        | .isFalse h => .isFalse (fun e => h (PyValue.int.inj e))
    | .bool a, .bool b =>
        match decEq a b with
        | .isTrue h => .isTrue (congrArg PyValue.bool h)
        | .isFalse h => .isFalse (fun e => h (PyValue.bool.inj e))
    | .list a, .list b =>
        match valuesDecEq a b with
        | .isTrue h => .isTrue (congrArg PyValue.list h)
        | .isFalse h => .isFalse (fun e => h (PyValue.list.inj e))
    | .other a, .other b =>
        match decEq a b with
        | .isTrue h => .isTrue (congrArg PyValue.other h)
        | .isFalse h => .isFalse (fun e => h (PyValue.other.inj e))
    | .int _, .bool _ | .int _, .list _ | .int _, .other _
    | .bool _, .int _ | .bool _, .list _ | .bool _, .other _
    | .list _, .int _ | .list _, .bool _ | .list _, .other _
    | .other _, .int _ | .other _, .bool _ | .other _, .list _ =>
        .isFalse (by intro h; cases h)
  def valuesDecEq : (as bs : List PyValue) → Decidable (as = bs)
    | [], [] => .isTrue rfl
    | [], _ :: _ | _ :: _, [] => .isFalse (by intro h; cases h)
    | a :: as, b :: bs =>
        match valueDecEq a b, valuesDecEq as bs with
        | .isTrue h, .isTrue hs => .isTrue (by cases h; cases hs; rfl)
        | .isFalse h, _ => .isFalse (fun e => h (List.cons.inj e).1)
        | _, .isFalse hs => .isFalse (fun e => hs (List.cons.inj e).2)
end
instance : DecidableEq PyValue := valueDecEq

inductive PyError where
  | valueError
  deriving Repr, DecidableEq

-- Lean supplies no default decidable equality instance for Except.
deriving instance DecidableEq for Except

/-- Python's `isinstance(x, int)`, including its boolean subclass. -/
def isInt : PyValue → Bool
  | .int _ | .bool _ => true
  | _ => false

/-- The executable Python precondition. -/
def pre : PyValue → Bool
  | .list xs => xs.all isInt
  | _ => false

/-- The slicing operation is polymorphic; admissible Python elements are integers. -/
def myReverse {α : Type} (xs : List α) : List α := xs.reverse

/-- Dynamic validation followed by reversal, or the ValueError branch. -/
def prog : PyValue → Except PyError PyValue
  | .list xs =>
      if xs.all isInt then .ok (.list (myReverse xs)) else .error .valueError
  | _ => .error .valueError

-- Unit tests: the original tests and additional edge/boundary cases.
example : myReverse ([1, 2, 3, 4] : List Int) = [4, 3, 2, 1] := by native_decide
example : myReverse ([] : List Int) = [] := by native_decide
example : myReverse ([-7] : List Int) = [-7] := by native_decide
example : myReverse ([2, -3, 2, 0] : List Int) = [0, 2, -3, 2] := by native_decide
example : prog (.list [.int 1, .int 2, .int 3, .int 4]) =
    .ok (.list [.int 4, .int 3, .int 2, .int 1]) := by native_decide
example : prog (.list []) = .ok (.list []) := by native_decide
example : prog (.list [.int 1, .other "2.5", .int 3]) =
    .error .valueError := by native_decide
example : prog (.list [.other "'a'", .other "'b'"]) =
    .error .valueError := by native_decide
example : prog (.int 5) = .error .valueError := by native_decide
example : prog (.list [.list []]) = .error .valueError := by native_decide
example : prog (.list [.bool true, .int (-2), .bool false]) =
    .ok (.list [.bool false, .int (-2), .bool true]) := by native_decide
#eval myReverse ([1, 2, 3, 4] : List Int)
#eval prog (.list [.int 1, .other "2.5", .int 3])

/-- Exactly the Python admissible domain, not an extra restriction on integers. -/
def Pre (input : PyValue) : Prop := pre input = true

-- Relational properties of an input list and its output list.
def reverse_prop {α : Type} (xs ys : List α) : Prop := ys = xs.reverse

theorem reverse_thm {α : Type} (xs : List α) : reverse_prop xs (myReverse xs) := by
  rfl

def length_prop {α : Type} (xs ys : List α) : Prop := ys.length = xs.length

theorem length_thm {α : Type} (xs : List α) : length_prop xs (myReverse xs) := by
  simp [length_prop, myReverse]

/-- Permutation preserves elements including their multiplicities. -/
def permutation_prop {α : Type} (xs ys : List α) : Prop := ys.Perm xs

theorem permutation_thm {α : Type} (xs : List α) :
    permutation_prop xs (myReverse xs) := by
  exact List.reverse_perm xs

def involution_prop {α : Type} (xs ys : List α) : Prop := myReverse ys = xs

theorem involution_thm {α : Type} (xs : List α) :
    involution_prop xs (myReverse xs) := by
  simp [involution_prop, myReverse]

/-- Every position i comes from position length - 1 - i in the input.
Optional indexing keeps the statement independent of proof arguments. -/
def index_prop {α : Type} (xs ys : List α) : Prop :=
  ∀ i : Fin xs.length, ys[i.val]? = xs[xs.length - 1 - i.val]?

theorem index_thm {α : Type} (xs : List α) : index_prop xs (myReverse xs) := by
  intro i
  exact List.getElem?_reverse i.isLt

def append_prop {α : Type} (xs zs : List α) : Prop :=
  myReverse (xs ++ zs) = myReverse zs ++ myReverse xs

theorem append_thm {α : Type} (xs zs : List α) : append_prop xs zs := by
  simp [append_prop, myReverse]

def empty_prop : Prop := myReverse ([] : List Int) = []

theorem empty_thm : empty_prop := by rfl

def singleton_prop (x : Int) : Prop := myReverse [x] = [x]

theorem singleton_thm (x : Int) : singleton_prop x := by
  simp [singleton_prop, myReverse]

/-- On valid lists the dynamic wrapper returns the list, not an exception. -/
def success_prop (xs : List PyValue) : Prop :=
  Pre (.list xs) → prog (.list xs) = .ok (.list (myReverse xs))

theorem success_thm (xs : List PyValue) : success_prop xs := by
  intro h
  simpa [prog, Pre, pre] using h

/-- Every precondition violation raises ValueError, including non-list inputs. -/
def rejection_prop (input : PyValue) : Prop :=
  ¬ Pre input → prog input = .error .valueError

theorem rejection_thm (input : PyValue) : rejection_prop input := by
  intro h
  cases input with
  | int n => rfl
  | bool b => rfl
  | other s => rfl
  | list xs => simp_all [Pre, pre, prog]

/-- Successful reversal is exact, preserves length and multiplicities, and is
involutive. Non-list outputs and exceptions cannot satisfy this postcondition. -/
def Post_prop (input : PyValue) (output : Except PyError PyValue) : Prop :=
  match input, output with
  | .list xs, .ok (.list ys) =>
      reverse_prop xs ys ∧ length_prop xs ys ∧
      permutation_prop xs ys ∧ involution_prop xs ys ∧ index_prop xs ys
  | _, _ => False

/-! ## Bounded property-based tests
We enumerate all lists of length at most four over a signed integer alphabet.
The dynamic suite additionally enumerates both valid and invalid elements and
non-list inputs. Each test below names the proposition whose executable form it
checks. These tests do not serve as proofs of the named theorems.
-/

def listsUpTo {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun x => (listsUpTo alphabet n).map (x :: ·))

def intSamples : List (List Int) := listsUpTo [-2, -1, 0, 1, 2] 4

def valueAlphabet : List PyValue :=
  [.int (-2), .int 0, .int 3, .bool false, .bool true,
   .other "2.5", .other "'a'", .list []]

def dynamicLists : List (List PyValue) := listsUpTo valueAlphabet 3

def dynamicSamples : List PyValue :=
  dynamicLists.map PyValue.list ++ valueAlphabet ++ [.other "None", .other "(1, 2)"]

-- PBT: reverse_prop.
example : intSamples.all (fun xs => myReverse xs == xs.reverse) = true := by native_decide
-- PBT: length_prop.
example : intSamples.all (fun xs => (myReverse xs).length == xs.length) = true := by native_decide
-- PBT: permutation_prop, including multiplicities.
example : intSamples.all (fun xs => decide ((myReverse xs).Perm xs)) = true := by native_decide
-- PBT: involution_prop.
example : intSamples.all (fun xs => myReverse (myReverse xs) == xs) = true := by native_decide
-- PBT: index_prop, checking every valid index of every generated list.
example : intSamples.all (fun xs => (List.range xs.length).all (fun i =>
    (myReverse xs)[i]? == xs[xs.length - 1 - i]?)) = true := by native_decide
-- PBT: append_prop; exhaustive pairs of lists of length at most two.
example : (listsUpTo ([-2, -1, 0, 1, 2] : List Int) 2).all (fun xs =>
    (listsUpTo ([-2, -1, 0, 1, 2] : List Int) 2).all (fun zs =>
      myReverse (xs ++ zs) == myReverse zs ++ myReverse xs)) = true := by native_decide
-- PBT: empty_prop has no input, hence its domain has one case.
example : ([()] : List Unit).all (fun _ => myReverse ([] : List Int) == []) = true := by native_decide
-- PBT: singleton_prop, for 101 signed values.
example : (List.range 101).all (fun n =>
    myReverse [(n : Int) - 50] == [(n : Int) - 50]) = true := by native_decide
-- PBT: success_prop, expressed as a Boolean implication.
example : dynamicLists.all (fun xs =>
    !pre (.list xs) || decide (prog (.list xs) = .ok (.list (myReverse xs)))) = true := by native_decide
-- PBT: rejection_prop, including wrong outer types and mixed lists.
example : dynamicSamples.all (fun v =>
    pre v || decide (prog v = .error .valueError)) = true := by native_decide

/-- Executable conjunction corresponding to Post_prop. For permutations we use
an actual decidable permutation test; no Prop-level existential is sampled. -/
def postCheck (input : PyValue) (output : Except PyError PyValue) : Bool :=
  match input, output with
  | .list xs, .ok (.list ys) =>
      decide (ys = xs.reverse) && decide (ys.length = xs.length) &&
      decide (ys.Perm xs) && decide (myReverse ys = xs) &&
      (List.range xs.length).all (fun i => decide (ys[i]? = xs[xs.length - 1 - i]?))
  | _, _ => false

-- PBT: Post_prop on all admissible inputs in the dynamic suite.
example : dynamicSamples.all (fun v => !pre v || postCheck v (prog v)) = true := by native_decide

/-- The original contract: Pre implies Post for the actual result of prog. -/
theorem correctness (input : PyValue) (h : Pre input) : Post_prop input (prog input) := by
  cases input with
  | int n => simp [Pre, pre] at h
  | bool b => simp [Pre, pre] at h
  | other s => simp [Pre, pre] at h
  | list xs =>
      rw [success_thm xs h]
      exact ⟨reverse_thm xs, length_thm xs, permutation_thm xs, involution_thm xs, index_thm xs⟩

/-! ## Imperative implementation -/

/-- An independent linear traversal, accumulating by prepending. -/
def myReverseImperative {α : Type} (xs : List α) : List α := Id.run do
  let mut result : List α := []
  for x in xs do
    result := x :: result
  return result

def progImperative : PyValue → Except PyError PyValue
  | .list xs =>
      if xs.all isInt then .ok (.list (myReverseImperative xs)) else .error .valueError
  | _ => .error .valueError

example : myReverseImperative ([1, 2, 3, 4] : List Int) = [4, 3, 2, 1] := by native_decide
example : myReverseImperative ([] : List Int) = [] := by native_decide
example : myReverseImperative ([-5] : List Int) = [-5] := by native_decide
example : progImperative (.list [.int 1, .other "2.5", .int 3]) =
    .error .valueError := by native_decide
example : progImperative (.list [.other "'a'", .other "'b'"]) =
    .error .valueError := by native_decide
#eval myReverseImperative ([1, 2, 3, 4] : List Int)
#eval progImperative (.list [.bool true, .int (-1)])

-- Additional imperative tests include the accepted boolean subclass and rejection
-- of wrong outer types, as well as bounded functional/imperative comparisons.
example : progImperative (.list [.bool true, .int (-2), .bool false]) =
    .ok (.list [.bool false, .int (-2), .bool true]) := by native_decide
example : progImperative (.other "None") = .error .valueError := by native_decide
example : intSamples.all (fun xs => myReverse xs == myReverseImperative xs) = true := by native_decide
example : dynamicSamples.all (fun v => decide (prog v = progImperative v)) = true := by native_decide

/-- The mutable accumulator is a left fold by cons, hence the reverse.
This is a kernel proof for all lists, not an appeal to the bounded tests. -/
theorem functional_imperative_equivalence {α : Type} (xs : List α) :
    myReverse xs = myReverseImperative xs := by
  simp [myReverse, myReverseImperative]

/-- Equivalence on the entire dynamic domain, including every ValueError branch. -/
theorem prog_equivalence (input : PyValue) : prog input = progImperative input := by
  cases input with
  | int n => rfl
  | bool b => rfl
  | other s => rfl
  | list xs => simp only [prog, progImperative, functional_imperative_equivalence]

end MyReverse
end Agent
