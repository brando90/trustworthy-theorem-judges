import Mathlib
namespace Agent

/-!
# Python string length

`prog` returns the number of Unicode characters in a string, including zero
for the empty string. Non-string arguments produce a `ValueError`, represented
by `Except` rather than by an exception escaping the Lean evaluator.

`Input.string` represents Python string inputs. `Input.nonString r` represents
any other Python object whose `repr` is `r`. This abstraction retains all the
information that this program observes about a non-string input, and is not
restricted to the two invalid inputs in the Python tests. A successful Python
length is nonnegative, so its exact, unbounded numeric model is `Nat`.
-/

namespace MyStringLength

/-! ## Functional implementation -/

inductive Input where
  | string (s : String)
  | nonString (pythonRepr : String)
  deriving Repr, DecidableEq, BEq

inductive PythonError where
  | valueError (message : String)
  deriving Repr, DecidableEq, BEq

deriving instance DecidableEq, BEq for Except

abbrev Result := Except PythonError Nat

def pre : Input → Bool
  | .string _ => true
  | .nonString _ => false

def inputError (pythonRepr : String) : PythonError :=
  .valueError ("Require string input (got s=" ++ pythonRepr ++ ")")

/-- Lean's `String.length` counts characters, not bytes. -/
def stringLength (s : String) : Nat := s.length

def prog : Input → Result
  | .string s => .ok (stringLength s)
  | .nonString r => .error (inputError r)

/-! ## Fixed unit tests, including both Python precondition violations -/

example : prog (.string "hello") = .ok 5 := by native_decide
example : prog (.string "") = .ok 0 := by native_decide
example : prog (.nonString "None") =
    .error (.valueError "Require string input (got s=None)") := by native_decide
example : prog (.nonString "123") =
    .error (.valueError "Require string input (got s=123)") := by native_decide
example : prog (.string "éλ😀") = .ok 3 := by native_decide
-- Combining marks are separate characters; this is not a grapheme count.
example : prog (.string "e\u0301") = .ok 2 := by native_decide

#eval prog (.string "hello")
#eval prog (.string "")
#eval prog (.nonString "None")
#eval prog (.nonString "123")
#eval prog (.string "éλ😀")

/-! ## Precondition -/

/-- Exactly the Python `isinstance(s, str)` test in the input model. -/
def Pre (x : Input) : Prop := pre x = true

/-! ## Properties and kernel-checked proofs -/

/-- On a string, the successful result is its number of characters. -/
def length_prop (x : Input) (result : Result) : Prop :=
  match x with
  | .string s => result = .ok s.toList.length
  | .nonString _ => True

theorem length_thm (x : Input) : length_prop x (prog x) := by
  cases x with
  | string s => simp [length_prop, prog, stringLength]
  | nonString r => trivial

/-- Zero is returned exactly for the empty string, never for an invalid input. -/
def empty_prop (x : Input) (result : Result) : Prop :=
  result = .ok 0 ↔ x = .string ""

theorem empty_thm (x : Input) : empty_prop x (prog x) := by
  cases x with
  | string s =>
      change (Except.ok s.toList.length : Result) = .ok 0 ↔
        Input.string s = Input.string ""
      rw [Except.ok.injEq, Input.string.injEq, List.length_eq_zero_iff]
      exact String.toList_inj
  | nonString r => simp [empty_prop, prog]

/-- Every non-string raises ValueError with the Python program's message. -/
def error_prop (x : Input) (result : Result) : Prop :=
  match x with
  | .string _ => True
  | .nonString r => result = .error (inputError r)

theorem error_thm (x : Input) : error_prop x (prog x) := by
  cases x <;> simp [error_prop, prog]

/-- The precondition characterizes success, not merely a sufficient condition. -/
def success_prop (x : Input) (result : Result) : Prop :=
  result.isOk = pre x

theorem success_thm (x : Input) : success_prop x (prog x) := by
  cases x <;> rfl

/-! ## Postcondition -/

def Post_prop (x : Input) (result : Result) : Prop :=
  length_prop x result ∧ empty_prop x result ∧
    error_prop x result ∧ success_prop x result

/-! ## Bounded property-based tests

Enumerate *every* word of length at most four over an alphabet containing
ASCII, a NUL, a non-ASCII letter, a combining mark, and an emoji. Also exercise
non-string inputs, including arbitrary repr strings generated from those
words. These are checks over many inputs, not substitutes for the proofs.
Each check below is the executable Boolean form of the named property.
-/

def testAlphabet : List Char := ['a', 'Z', '\n', '\x00', 'é', '\u0301', '😀']

def wordsOfLength : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => (wordsOfLength n).flatMap fun w => testAlphabet.map fun c => c :: w

def testStrings : List String :=
  ((List.range 5).flatMap wordsOfLength).map String.mk

def testInputs : List Input :=
  testStrings.map Input.string ++
    (["None", "123", "-17", "True", "3.5", "[]", "{}", "b'abc'" ] ++
      testStrings).map Input.nonString

-- PBT for length_prop.
example : testInputs.all (fun x => match x with
    | .string s => prog x == (.ok s.toList.length : Result)
    | .nonString _ => true) = true := by native_decide

-- PBT for empty_prop (Boolean equivalence, not just one implication).
example : testInputs.all (fun x =>
    (prog x == (.ok 0 : Result)) == (x == .string "")) = true := by native_decide

-- PBT for error_prop, including the exact error message for every invalid input.
example : testInputs.all (fun x => match x with
    | .string _ => true
    | .nonString r => prog x == (.error (inputError r) : Result)) = true := by
  native_decide

-- PBT for success_prop.
example : testInputs.all (fun x => (prog x).isOk == pre x) = true := by native_decide

-- PBT for the entire conjunction Post_prop, on valid AND invalid inputs.
example : testInputs.all (fun x =>
    let result := prog x
    let lengthOK := match x with
      | .string s => result == (.ok s.toList.length : Result)
      | .nonString _ => true
    let emptyOK := (result == (.ok 0 : Result)) == (x == .string "")
    let errorOK := match x with
      | .string _ => true
      | .nonString r => result == (.error (inputError r) : Result)
    lengthOK && emptyOK && errorOK && (result.isOk == pre x)) = true := by
  native_decide

#eval testStrings.length
#eval testInputs.length
#eval testInputs.all (fun x => (prog x).isOk == pre x)

/-! ## Correctness -/

theorem correctness (x : Input) (_h : Pre x) : Post_prop x (prog x) := by
  exact ⟨length_thm x, empty_thm x, error_thm x, success_thm x⟩

/-- The specification also covers the exceptional cases outside `Pre`. -/
theorem total_correctness (x : Input) : Post_prop x (prog x) := by
  exact ⟨length_thm x, empty_thm x, error_thm x, success_thm x⟩

/-! ## Imperative implementation

The accumulator is incremented once for each character. Iterating over
`toList` deliberately avoids counting the bytes of the UTF-8 representation.
-/

def stringLengthImperative (s : String) : Nat := Id.run do
  let mut count := 0
  for _c in s.toList do
    count := count + 1
  return count

def progImperative (x : Input) : Result := Id.run do
  match x with
  | .string s =>
      let mut result := 0
      result := stringLengthImperative s
      return .ok result
  | .nonString r =>
      return .error (inputError r)

/-! ## Imperative tests -/

example : progImperative (.string "hello") = .ok 5 := by native_decide
example : progImperative (.string "") = .ok 0 := by native_decide
example : progImperative (.nonString "None") =
    .error (.valueError "Require string input (got s=None)") := by native_decide
example : progImperative (.nonString "123") =
    .error (.valueError "Require string input (got s=123)") := by native_decide
example : progImperative (.string "éλ😀") = .ok 3 := by native_decide
example : testInputs.all (fun x => prog x == progImperative x) = true := by
  native_decide

#eval progImperative (.string "hello")
#eval progImperative (.nonString "None")

/-! ## Functional/imperative equivalence -/

theorem stringLength_equiv (s : String) :
    stringLength s = stringLengthImperative s := by
  simp [stringLength, stringLengthImperative]

theorem equivalence (x : Input) : prog x = progImperative x := by
  cases x with
  | string s => simpa [prog, progImperative] using congrArg (Except.ok : Nat → Result) (stringLength_equiv s)
  | nonString r => rfl

end MyStringLength
end Agent
