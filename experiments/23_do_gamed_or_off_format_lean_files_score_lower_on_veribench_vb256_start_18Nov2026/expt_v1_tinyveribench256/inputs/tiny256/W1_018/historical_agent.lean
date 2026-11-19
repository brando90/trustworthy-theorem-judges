import Mathlib
namespace Agent

/-!
# First character of a non-empty string

A translation of the Python `pre` and `prog`. A successful result is a string
of length one (not a bare `Char`). `Except` models raising `ValueError`.

`Input.str` represents strings. `Input.other repr` represents any non-string
Python value, retaining its Python `repr` for the diagnostic. Thus `None` is
`Input.other "None"`; non-strings are not silently excluded by the Lean type.
No other information about a non-string is inspected by the Python program.
String indexing is by characters, not UTF-8 bytes.

The bounded property tests exhaust all strings of length at most three over
a mixed ASCII/Unicode alphabet, and also exercise non-string inputs. They are
only tests; the universally quantified theorems below have kernel proofs.
-/

namespace MyFirstChar

/-! ## Functional implementation -/

inductive Input where
  | str (value : String)
  | other (pythonRepr : String)
  deriving DecidableEq, Repr

inductive Error where
  | valueError (message : String)
  deriving DecidableEq, Repr

-- Executable equality for result-valued unit and property tests.
deriving instance DecidableEq for Except

/-- Construct the same diagnostic as the Python f-string. -/
def valueError (pythonRepr : String) : Error :=
  .valueError ("Require non-empty string (got s=" ++ pythonRepr ++ ")")

/-- The executable Python precondition, including its dynamic type check. -/
def pre : Input → Bool
  | .str s => !s.toList.isEmpty
  | .other _ => false

/-- Empty strings and every non-string raise ValueError. -/
def prog : Input → Except Error String
  | .str s =>
    match s.toList with
    | [] => .error (valueError "''")
    | c :: _ => .ok (String.singleton c)
  | .other repr => .error (valueError repr)

/-! ## Unit tests -/

example : prog (.str "hello") = .ok "h" := by native_decide
example : prog (.str "A") = .ok "A" := by native_decide
example : prog (.str "") =
    .error (.valueError "Require non-empty string (got s='')") := by native_decide
example : prog (.other "None") =
    .error (.valueError "Require non-empty string (got s=None)") := by native_decide
example : prog (.other "42") = .error (valueError "42") := by native_decide
example : prog (.str "界abc") = .ok "界" := by native_decide
example : prog (.str "😀hello") = .ok "😀" := by native_decide
example : prog (.str "\nabc") = .ok "\n" := by native_decide
example : pre (.str "A") = true ∧ pre (.str "") = false ∧
    pre (.other "None") = false := by native_decide

#eval prog (.str "hello")
#eval prog (.str "A")
#eval prog (.str "")
#eval prog (.other "None")

/-! ## Precondition -/

/-- Exactly the non-empty strings; all non-string inputs are inadmissible. -/
def Pre : Input → Prop
  | .str s => s.toList ≠ []
  | .other _ => False

/-! ## Properties and kernel-checked proofs -/

theorem pre_iff_thm (input : Input) : pre input = true ↔ Pre input := by
  cases input with
  | str s =>
    cases hs : s.data <;> simp [pre, Pre, String.toList, hs]
  | other repr => simp [pre, Pre]

/-- Relate the list formulation to Python's `len(s) > 0`. -/
theorem pre_length_thm (s : String) : Pre (.str s) ↔ 0 < s.length := by
  change s.data ≠ [] ↔ 0 < s.data.length
  exact List.length_pos_iff.symm

/-- The returned string consists of precisely the original head character. -/
def firstCharacter_prop (input : Input) : Prop :=
  ∃ (c : Char) (tail : List Char),
    input = .str (String.mk (c :: tail)) ∧
    prog input = .ok (String.singleton c)

theorem firstCharacter_thm (input : Input) (h : Pre input) :
    firstCharacter_prop input := by
  cases input with
  | other repr => simp [Pre] at h
  | str s =>
    cases s with
    | mk chars =>
      cases chars with
      | nil => simp [Pre, String.toList] at h
      | cons c tail => exact ⟨c, tail, rfl, rfl⟩

/-- A successful admissible call returns a string of character length one. -/
def length_prop (input : Input) : Prop :=
  ∃ output : String, prog input = .ok output ∧ output.length = 1

theorem length_thm (input : Input) (h : Pre input) : length_prop input := by
  obtain ⟨c, tail, _, hr⟩ := firstCharacter_thm input h
  exact ⟨String.singleton c, hr, String.length_singleton c⟩

/-- The returned character is a prefix of the input, with an unchanged suffix. -/
def prefix_prop (input : Input) : Prop :=
  ∃ output suffix : String,
    input = .str (output ++ suffix) ∧ prog input = .ok output

theorem prefix_thm (input : Input) (h : Pre input) : prefix_prop input := by
  obtain ⟨c, tail, hi, hr⟩ := firstCharacter_thm input h
  exact ⟨String.singleton c, String.mk tail, hi, hr⟩

/-- Single-character strings are returned unchanged. -/
def singleton_prop (c : Char) : Prop :=
  prog (.str (String.singleton c)) = .ok (String.singleton c)

theorem singleton_thm (c : Char) : singleton_prop c := by
  rfl

/-- Exact exception behavior, including the diagnostic on non-string inputs. -/
def valueError_prop (input : Input) : Prop :=
  match input with
  | .str s => (prog input = .error (valueError "''") ↔ s.toList = [])
  | .other repr => prog input = .error (valueError repr)

theorem valueError_thm (input : Input) : valueError_prop input := by
  cases input with
  | str s =>
    cases hs : s.data <;> simp [valueError_prop, prog, String.toList, hs]
  | other repr => rfl

/-- No error occurs on a valid call, and every pre-violation raises an error. -/
theorem error_iff_not_pre_thm (input : Input) :
    (∃ err, prog input = .error err) ↔ ¬ Pre input := by
  cases input with
  | str s => cases hs : s.data <;> simp [prog, Pre, String.toList, hs]
  | other repr => simp [prog, Pre]

/-- Successful termination is equivalent to the Python precondition. -/
theorem success_iff_pre_thm (input : Input) :
    (∃ output, prog input = .ok output) ↔ Pre input := by
  cases input with
  | str s => cases hs : s.data <;> simp [prog, Pre, String.toList, hs]
  | other repr => simp [prog, Pre]

/-! ## Postcondition -/

/-- On admissible inputs all success properties hold, along with the exact
exception specification (which rules out an exception on these inputs). -/
def Post_prop (input : Input) : Prop :=
  firstCharacter_prop input ∧ length_prop input ∧
  prefix_prop input ∧ valueError_prop input

/-! ## Bounded property-based tests

Each check below is the executable Boolean form of its named property,
evaluated on `prog`. Success properties are guarded by the executable `pre`;
exception properties are checked on *all* inputs, including invalid ones.
These are exhaustive bounded tests, not substitutes for the general proofs.
-/

def testAlphabet : List Char := ['a', 'Z', '0', ' ', '\n', 'é', '界', '😀']

def wordsOfLength : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => testAlphabet.flatMap (fun c => (wordsOfLength n).map (c :: ·))

def testStrings : List String :=
  ((List.range 4).flatMap wordsOfLength).map String.mk

def testInputs : List Input :=
  testStrings.map Input.str ++
    (["None", "0", "-17", "False", "True", "[]", "{}", "b'abc'"].map Input.other)

/-- Executable form of `firstCharacter_prop`. -/
def firstCharacterCheck (input : Input) : Bool :=
  match input, prog input with
  | .str s, .ok output => s.toList.head?.map String.singleton == some output
  | _, _ => false

/-- Executable form of `length_prop`. -/
def lengthCheck (input : Input) : Bool :=
  match prog input with
  | .ok output => output.length == 1
  | .error _ => false

/-- Executable form of `prefix_prop`, using list prefix comparison. -/
def prefixCheck (input : Input) : Bool :=
  match input, prog input with
  | .str s, .ok output => output.toList.isPrefixOf s.toList
  | _, _ => false

/-- Executable form of `valueError_prop`. -/
def valueErrorCheck (input : Input) : Bool :=
  match input with
  | .str s => decide (prog input = .error (valueError "''")) == s.toList.isEmpty
  | .other repr => decide (prog input = .error (valueError repr))

/-- Executable conjunction for `Post_prop`. -/
def postCheck (input : Input) : Bool :=
  firstCharacterCheck input && lengthCheck input &&
    prefixCheck input && valueErrorCheck input

-- PBT: firstCharacter_prop.
example : testInputs.all (fun input => !pre input || firstCharacterCheck input) = true := by
  native_decide

-- PBT: length_prop.
example : testInputs.all (fun input => !pre input || lengthCheck input) = true := by
  native_decide

-- PBT: prefix_prop.
example : testInputs.all (fun input => !pre input || prefixCheck input) = true := by
  native_decide

-- PBT: singleton_prop; include control characters as well as the Unicode alphabet.
example : (testAlphabet ++ (List.range 512).map Char.ofNat).all
    (fun c => decide (prog (.str (String.singleton c)) = .ok (String.singleton c))) = true := by
  native_decide

-- PBT: valueError_prop, including the empty string and all non-string samples.
example : testInputs.all valueErrorCheck = true := by native_decide

-- PBT: Post_prop.
example : testInputs.all (fun input => !pre input || postCheck input) = true := by
  native_decide

-- PBT: success iff Pre and error iff not Pre.
example : testInputs.all (fun input =>
    match prog input with
    | .ok _ => pre input
    | .error _ => !pre input) = true := by native_decide

-- PBT: the executable precondition agrees with the character length test.
example : testStrings.all
    (fun s => pre (.str s) == decide (0 < s.length)) = true := by native_decide

#eval (testInputs.length,
  testInputs.all (fun input => !pre input || postCheck input),
  testInputs.all valueErrorCheck)

/-! ## Correctness -/

theorem correctness_thm (input : Input) : Pre input → Post_prop input := by
  intro h
  exact ⟨firstCharacter_thm input h, length_thm input h,
    prefix_thm input h, valueError_thm input⟩

/-! ## Imperative implementation -/

/-- Mutable result state models the return/raise branches of the Python code. -/
def progImperative (input : Input) : Except Error String := Id.run do
  let mut result : Except Error String := .error (valueError "''")
  match input with
  | .str s =>
    match s.toList with
    | [] => pure ()
    | c :: _ => result := .ok (String.singleton c)
  | .other repr => result := .error (valueError repr)
  return result

/-! ## Imperative tests -/

example : progImperative (.str "hello") = .ok "h" := by native_decide
example : progImperative (.str "A") = .ok "A" := by native_decide
example : progImperative (.str "") = .error (valueError "''") := by native_decide
example : progImperative (.other "None") = .error (valueError "None") := by native_decide
example : progImperative (.str "😀abc") = .ok "😀" := by native_decide

-- Bounded equivalence test covers successful calls and both kinds of failure.
example : testInputs.all
    (fun input => decide (prog input = progImperative input)) = true := by native_decide

#eval progImperative (.str "hello")
#eval progImperative (.str "")
#eval progImperative (.other "None")

/-! ## Equivalence on the entire input domain -/

theorem equivalence_thm (input : Input) : prog input = progImperative input := by
  cases input with
  | str s => cases hs : s.data <;> simp [prog, progImperative, String.toList, hs]
  | other repr => rfl

end MyFirstChar
end Agent
