import Mathlib
namespace Agent

/-!
# Removing ASCII space characters

A translation of Python's `s.replace(' ', '')`. Only U+0020 is removed;
other whitespace and all other Unicode characters are preserved in order.
`PyInput.string` represents a Python string. `PyInput.nonString repr` represents
any non-string Python value, carrying its repr for the ValueError message.
This abstraction includes None, integers, and every other rejected input type.
Exceptions are represented by `Except PyError String`. The pure string algorithm
and its mutable-state counterpart are both executable.
-/

namespace MyRemoveSpaces14

inductive PyInput where
  | string (value : String)
  | nonString (repr : String)
  deriving DecidableEq, Repr

inductive PyError where
  | valueError (message : String)
  deriving DecidableEq, Repr

deriving instance DecidableEq for Except

def inputError (repr : String) : PyError :=
  .valueError ("Require string input (got s=" ++ repr ++ ")")

/-- Python removes the literal ASCII space, not all whitespace. -/
def keep (c : Char) : Bool := c != ' '

def removeSpaces (s : String) : String :=
  String.mk (s.toList.filter keep)

def prog : PyInput → Except PyError String
  | .string s => .ok (removeSpaces s)
  | .nonString repr => .error (inputError repr)

-- Unit tests, including both precondition violations from the Python tests.
example : prog (.string "hello world") = .ok "helloworld" := by native_decide
example : prog (.string "") = .ok "" := by native_decide
example : prog (.string "     ") = .ok "" := by native_decide
example : prog (.string " a  b ") = .ok "ab" := by native_decide
example : prog (.string "a \t\nb c 😀 ") = .ok "a\t\nb c 😀" := by native_decide
example : prog (.nonString "None") =
    .error (.valueError "Require string input (got s=None)") := by native_decide
example : prog (.nonString "123") =
    .error (.valueError "Require string input (got s=123)") := by native_decide
#eval prog (.string "hello world")
#eval prog (.string "")
#eval prog (.nonString "None")
#eval prog (.nonString "123")

/-- The Python isinstance(s, str) precondition. -/
def Pre : PyInput → Prop
  | .string _ => True
  | .nonString _ => False

/-- Exact replacement semantics; this also fixes the order and multiplicity. -/
def exact_prop (s t : String) : Prop :=
  t.toList = s.toList.filter keep

theorem exact_thm (s : String) : exact_prop s (removeSpaces s) := by
  rfl

def noSpaces_prop (t : String) : Prop := ' ' ∉ t.toList

theorem noSpaces_thm (s : String) : noSpaces_prop (removeSpaces s) := by
  simp [noSpaces_prop, removeSpaces, String.toList, keep]

def ordered_prop (s t : String) : Prop := t.toList.Sublist s.toList

theorem ordered_thm (s : String) : ordered_prop s (removeSpaces s) := by
  exact List.filter_sublist

def multiplicity_prop (s t : String) : Prop :=
  ∀ c : Char, c ≠ ' ' → t.toList.count c = s.toList.count c

theorem multiplicity_thm (s : String) : multiplicity_prop s (removeSpaces s) := by
  intro c hc
  exact List.count_filter (by simpa [keep] using hc)

/-- Length is measured in Unicode characters, as for Python strings. -/
def length_prop (s t : String) : Prop := t.length ≤ s.length

theorem length_thm (s : String) : length_prop s (removeSpaces s) := by
  exact List.length_filter_le keep s.toList

def idempotent_prop (t : String) : Prop := removeSpaces t = t

theorem idempotent_thm (s : String) : idempotent_prop (removeSpaces s) := by
  apply String.ext
  simp [removeSpaces, String.toList, List.filter_filter]

def unchanged_prop (s t : String) : Prop := (' ' ∉ s.toList) → t = s

theorem unchanged_thm (s : String) : unchanged_prop s (removeSpaces s) := by
  intro h
  apply String.ext
  apply List.filter_eq_self.mpr
  intro c hc
  have hne : c ≠ ' ' := by
    intro heq
    subst c
    exact h hc
  simpa [keep] using hne

def allSpaces_prop (s t : String) : Prop :=
  (∀ c ∈ s.toList, c = ' ') → t = ""

theorem allSpaces_thm (s : String) : allSpaces_prop s (removeSpaces s) := by
  intro h
  apply String.ext
  apply List.filter_eq_nil_iff.mpr
  intro c hc
  simp [keep, h c hc]

/-- Non-string inputs raise exactly the specified ValueError. -/
def rejection_prop (repr : String) (result : Except PyError String) : Prop :=
  result = .error (inputError repr)

theorem rejection_thm (repr : String) : rejection_prop repr (prog (.nonString repr)) := by
  rfl

theorem pre_iff_string_thm (input : PyInput) :
    Pre input ↔ ∃ s : String, input = .string s := by
  cases input <;> simp [Pre]

/-- On success, all properties are required together. On a rejected input,
    the result must instead be the corresponding ValueError. -/
def Post_prop (input : PyInput) (result : Except PyError String) : Prop :=
  match input, result with
  | .string s, .ok t =>
      exact_prop s t ∧ noSpaces_prop t ∧ ordered_prop s t ∧
      multiplicity_prop s t ∧ length_prop s t ∧ idempotent_prop t ∧
      unchanged_prop s t ∧ allSpaces_prop s t
  | .nonString repr, result => rejection_prop repr result
  | .string _, .error _ => False

/-! ## Bounded property-based tests

Exhaustively enumerate all strings of at most three characters over an alphabet
containing spaces, repeated letters, tab, newline, nonbreaking space, em space,
and an emoji (585 strings). These are evidence only; all universal claims above
and below have independent kernel-checked proofs. Boolean implications ensure
that the unchanged/all-space tests include precisely their admissible cases.
-/

def testAlphabet : List Char := [' ', 'a', 'b', '\t', '\n', ' ', ' ', '😀']

def shortWords : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: testAlphabet.flatMap (fun c => (shortWords n).map (c :: ·))

def testStrings : List String := (shortWords 3).map String.mk

-- PBT for exact_prop.
example : testStrings.all (fun s =>
    (removeSpaces s).toList == s.toList.filter keep) = true := by native_decide

-- PBT for noSpaces_prop.
example : testStrings.all (fun s =>
    !((removeSpaces s).toList.contains ' ')) = true := by native_decide

-- PBT for ordered_prop.
example : testStrings.all (fun s =>
    decide ((removeSpaces s).toList.Sublist s.toList)) = true := by native_decide

-- PBT for multiplicity_prop, bounding both the string and character inputs.
example : testStrings.all (fun s => testAlphabet.all (fun c =>
    c == ' ' || (removeSpaces s).toList.count c == s.toList.count c)) = true := by
  native_decide

-- PBT for length_prop.
example : testStrings.all (fun s =>
    decide ((removeSpaces s).length ≤ s.length)) = true := by native_decide

-- PBT for idempotent_prop.
example : testStrings.all (fun s =>
    removeSpaces (removeSpaces s) == removeSpaces s) = true := by native_decide

-- PBT for unchanged_prop (decidable implication).
example : testStrings.all (fun s =>
    s.toList.contains ' ' || removeSpaces s == s) = true := by native_decide

-- PBT for allSpaces_prop, including the empty string.
example : testStrings.all (fun s =>
    !(s.toList.all (· == ' ')) || removeSpaces s == "") = true := by native_decide

-- Additional non-vacuous all-space cases of increasing length.
example : (List.range 65).all (fun n =>
    removeSpaces (String.mk (List.replicate n ' ')) == "") = true := by native_decide

def rejectedReprs : List String :=
  ["None", "123", "-7", "True", "3.5", "[]", "{}", "b'abc'", "<object>"] ++ testStrings

-- PBT for rejection_prop: arbitrary repr text does not bypass the type check.
example : rejectedReprs.all (fun r =>
    decide (prog (.nonString r) = .error (inputError r))) = true := by native_decide

/-- Executable form of the complete string postcondition. Counting every input
    and output character covers all possibly nonzero character multiplicities. -/
def stringPostCheck (s t : String) : Bool :=
  (t.toList == s.toList.filter keep) &&
  !(t.toList.contains ' ') &&
  decide (t.toList.Sublist s.toList) &&
  (s.toList ++ t.toList).all (fun c => c == ' ' || t.toList.count c == s.toList.count c) &&
  decide (t.length ≤ s.length) &&
  (removeSpaces t == t) &&
  (s.toList.contains ' ' || t == s) &&
  (!(s.toList.all (· == ' ')) || t == "")

def postCheck (input : PyInput) (result : Except PyError String) : Bool :=
  match input, result with
  | .string s, .ok t => stringPostCheck s t
  | .nonString repr, result => decide (result = .error (inputError repr))
  | .string _, .error _ => false

def testInputs : List PyInput :=
  testStrings.map PyInput.string ++ rejectedReprs.map PyInput.nonString

-- PBT for Post_prop, including valid and invalid input classes.
example : testInputs.all (fun input => postCheck input (prog input)) = true := by
  native_decide
#eval (testStrings.length, testInputs.all (fun input => postCheck input (prog input)))

/-- Required Pre → Post correctness theorem. -/
theorem correctness_thm (input : PyInput) (h : Pre input) : Post_prop input (prog input) := by
  cases input with
  | string s =>
    exact ⟨exact_thm s, noSpaces_thm s, ordered_thm s, multiplicity_thm s,
      length_thm s, idempotent_thm s, unchanged_thm s, allSpaces_thm s⟩
  | nonString repr => exact False.elim h

/-- The error branch is specified too, without assuming the precondition. -/
theorem total_correctness_thm (input : PyInput) : Post_prop input (prog input) := by
  cases input with
  | string s => exact correctness_thm (.string s) trivial
  | nonString repr => exact rejection_thm repr


/-- Imperative translation: traverse the characters and append retained ones. -/
def removeSpacesImperative (s : String) : String := Id.run do
  let mut out : List Char := []
  for c in s.toList do
    if keep c then
      out := out ++ [c]
  return String.mk out

def progImperative (input : PyInput) : Except PyError String := Id.run do
  match input with
  | .nonString repr => return .error (inputError repr)
  | .string s =>
    let mut result := ""
    result := removeSpacesImperative s
    return .ok result

example : progImperative (.string "hello world") = .ok "helloworld" := by native_decide
example : progImperative (.string "") = .ok "" := by native_decide
example : progImperative (.string "   ") = .ok "" := by native_decide
example : progImperative (.nonString "None") = .error (inputError "None") := by native_decide
example : progImperative (.nonString "123") = .error (inputError "123") := by native_decide
#eval progImperative (.string " a  b ")
#eval progImperative (.nonString "123")

-- Imperative Unicode/whitespace and bounded regression tests.
example : progImperative (.string "a \t\nb c 😀 ") = .ok "a\t\nb c 😀" := by
  native_decide
example : testInputs.all (fun input => postCheck input (progImperative input)) = true := by
  native_decide
example : testInputs.all (fun input => decide (prog input = progImperative input)) = true := by
  native_decide
#eval testInputs.all (fun input => postCheck input (progImperative input))

/-- Loop invariant: an arbitrary initial accumulator is followed by precisely
    the retained characters of the remaining input, in their original order. -/
private theorem loop_filter (xs acc : List Char) :
    (forIn xs acc (fun c out =>
      if keep c then pure (ForInStep.yield (out ++ [c]))
      else pure (ForInStep.yield out)) : Id (List Char)) = acc ++ xs.filter keep := by
  induction xs generalizing acc with
  | nil =>
    simp
    rfl
  | cons c xs ih =>
    cases h : keep c <;>
      simp [List.forIn_cons, h, ih, List.append_assoc]

/-- Kernel-checked equivalence, for every string, not only the test corpus. -/
theorem string_equivalence_thm (s : String) :
    removeSpaces s = removeSpacesImperative s := by
  simp [removeSpacesImperative, removeSpaces, loop_filter]
  rfl

/-- The checked programs also agree on every rejected input and error message. -/
theorem equivalence_thm (input : PyInput) : prog input = progImperative input := by
  cases input with
  | string s =>
    change Except.ok (removeSpaces s) = Except.ok (removeSpacesImperative s)
    exact congrArg Except.ok (string_equivalence_thm s)
  | nonString repr => rfl

end MyRemoveSpaces14
end Agent
