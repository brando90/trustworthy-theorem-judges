import Mathlib

/-!
# Duplicate each character

Formalization of Python's `duplicate_chars`: traverse a string in character order
and emit each character twice. Lengths count characters, not UTF-8 bytes.
`PythonInput.nonString` abstracts all non-string Python values, including `None`:
they are indistinguishable to this program and raise the same `ValueError`.
The checked interface represents that exception as `Except.error` with its message.

The file proves exact output, length, indexed characters, emptiness, character
counts, concatenation, error behavior, and equivalence to a mutable loop. Random
property tests are supplemented by exhaustive short strings containing Unicode.
-/

namespace DuplicateChars

/- Functional implementation and the dynamically typed Python boundary. -/

inductive PythonInput where
  | str (value : String)
  | nonString
  deriving Repr, DecidableEq

deriving instance DecidableEq for Except

def pre : PythonInput → Bool
  | .str _ => true
  | .nonString => false

def duplicate_chars (s : String) : String :=
  String.mk (s.toList.flatMap fun c => [c, c])

def duplicate_chars_checked : PythonInput → Except String String
  | .str s => .ok (duplicate_chars s)
  | .nonString => .error "Input must be a string"

/- Unit tests, including all examples from the source and its invalid-input test. -/

example : duplicate_chars "abc" = "aabbcc" := by native_decide
example : duplicate_chars "" = "" := by native_decide
example : duplicate_chars "!a " = "!!aa  " := by native_decide
example : duplicate_chars "é🙂" = "éé🙂🙂" := by native_decide
example : duplicate_chars "aaa" = "aaaaaa" := by native_decide
example : duplicate_chars "\n\t" = "\n\n\t\t" := by native_decide
example : duplicate_chars_checked (.str "abc") = .ok "aabbcc" := by native_decide
example : duplicate_chars_checked .nonString =
    .error "Input must be a string" := by native_decide
example : pre .nonString = false := by native_decide

#eval duplicate_chars "abc"
#eval duplicate_chars ""
#eval duplicate_chars "!a "
#eval duplicate_chars_checked .nonString

/- Pre-condition: exactly the inputs satisfying Python's `isinstance(s, str)`. -/

def Pre (input : PythonInput) : Prop := pre input = true

/- Properties and proofs. -/

def sequence_prop (s output : String) : Prop :=
  output.toList = s.toList.flatMap (fun c => [c, c])

theorem sequence_thm (s : String) : sequence_prop s (duplicate_chars s) := by
  rfl

def length_prop (s output : String) : Prop :=
  output.length = 2 * s.length

private theorem duplicated_list_length (xs : List Char) :
    (xs.flatMap fun c => [c, c]).length = 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem length_thm (s : String) : length_prop s (duplicate_chars s) := by
  exact duplicated_list_length s.toList

/-- Optional indexing also specifies the behavior beyond the end of the string. -/
def positions_prop (s output : String) : Prop :=
  ∀ i : Nat, output.toList[2 * i]? = s.toList[i]? ∧
    output.toList[2 * i + 1]? = s.toList[i]?

private theorem duplicated_list_positions (xs : List Char) (i : Nat) :
    (xs.flatMap fun c => [c, c])[2 * i]? = xs[i]? ∧
    (xs.flatMap fun c => [c, c])[2 * i + 1]? = xs[i]? := by
  induction xs generalizing i with
  | nil => simp
  | cons c cs ih =>
    cases i with
    | zero => simp
    | succ i => simpa [List.flatMap_cons, Nat.mul_succ, Nat.add_assoc] using ih i

theorem positions_thm (s : String) : positions_prop s (duplicate_chars s) := by
  exact duplicated_list_positions s.toList

def empty_prop (s output : String) : Prop :=
  output = "" ↔ s = ""

theorem empty_thm (s : String) : empty_prop s (duplicate_chars s) := by
  constructor
  · intro h
    have hlen := length_thm s
    change (duplicate_chars s).length = 2 * s.length at hlen
    rw [h] at hlen
    have hs : s.length = 0 := by simpa using hlen.symm
    apply String.toList_inj.mp
    exact List.length_eq_zero_iff.mp hs
  · intro h
    subst s
    rfl

def count_prop (s output : String) : Prop :=
  ∀ c : Char, output.toList.count c = 2 * s.toList.count c

private theorem duplicated_list_count (xs : List Char) (c : Char) :
    (xs.flatMap fun d => [d, d]).count c = 2 * xs.count c := by
  induction xs with
  | nil => simp
  | cons d ds ih =>
    by_cases h : d = c
    · subst d
      simp [List.flatMap_cons, ih, Nat.mul_add, Nat.add_assoc]
    · simp [List.flatMap_cons, h, ih]

theorem count_thm (s : String) : count_prop s (duplicate_chars s) := by
  exact duplicated_list_count s.toList

def append_prop (s t : String) : Prop :=
  duplicate_chars (s ++ t) = duplicate_chars s ++ duplicate_chars t

theorem append_thm (s t : String) : append_prop s t := by
  apply String.toList_inj.mp
  exact List.flatMap_append

def rejection_prop (input : PythonInput) : Prop :=
  ¬ Pre input → duplicate_chars_checked input = .error "Input must be a string"

theorem rejection_thm (input : PythonInput) : rejection_prop input := by
  cases input <;> simp [rejection_prop, Pre, pre, duplicate_chars_checked]

/- The post-condition specifies successful output and the exceptional case. -/

def Post_prop (input : PythonInput) (result : Except String String) : Prop :=
  (∀ s, input = .str s →
    ∃ output, result = .ok output ∧
      sequence_prop s output ∧ length_prop s output ∧
      positions_prop s output ∧ empty_prop s output ∧ count_prop s output) ∧
  (¬ Pre input → result = .error "Input must be a string")

/- Property-based tests. Each proposition above has an executable check.
The universal index and character clauses are sampled without narrowing their
theorem statements. These tests are evidence; the proofs above are independent.
-/

#eval Plausible.Testable.check (∀ s : String,
  (duplicate_chars s).toList = s.toList.flatMap (fun c => [c, c]))

#eval Plausible.Testable.check (∀ s : String,
  (duplicate_chars s).length = 2 * s.length)

#eval Plausible.Testable.check (∀ (s : String) (i : Nat),
  (duplicate_chars s).toList[2 * i]? = s.toList[i]? ∧
  (duplicate_chars s).toList[2 * i + 1]? = s.toList[i]?)

#eval Plausible.Testable.check (∀ s : String,
  (duplicate_chars s = "" ↔ s = ""))

#eval Plausible.Testable.check (∀ (s : String) (c : Char),
  (duplicate_chars s).toList.count c = 2 * s.toList.count c)

#eval Plausible.Testable.check (∀ s t : String,
  duplicate_chars (s ++ t) = duplicate_chars s ++ duplicate_chars t)

#eval Plausible.Testable.check (∀ (isString : Bool) (s : String),
  let input := if isString then PythonInput.str s else .nonString
  pre input = false →
    duplicate_chars_checked input = .error "Input must be a string")

/-- Executable post-condition at sampled indices and characters. -/
def postCheck (input : PythonInput) (result : Except String String)
    (i : Nat) (c : Char) : Bool :=
  match input, result with
  | .str s, .ok output =>
    (output.toList == s.toList.flatMap (fun d => [d, d])) &&
    (output.length == 2 * s.length) &&
    (output.toList[2 * i]? == s.toList[i]?) &&
    (output.toList[2 * i + 1]? == s.toList[i]?) &&
    ((output == "") == (s == "")) &&
    (output.toList.count c == 2 * s.toList.count c)
  | .nonString, .error message => message == "Input must be a string"
  | _, _ => false

-- PBT for Post_prop, including both valid and invalid inputs.
#eval Plausible.Testable.check
  (∀ (isString : Bool) (s : String) (i : Nat) (c : Char),
    let input := if isString then PythonInput.str s else .nonString
    postCheck input (duplicate_chars_checked input) i c = true)

def testAlphabet : List Char := ['a', 'b', '!', ' ', 'é', '🙂']

/-- All words of length at most the bound, including the empty word. -/
def shortWords : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: testAlphabet.flatMap (fun c => (shortWords n).map (c :: ·))

def testStrings : List String := (shortWords 4).map String.mk

-- Exhaustive Post_prop checks on 1,555 strings. Test every in-range index and
-- two out-of-range indices, and characters both present and absent in the alphabet.
example : testStrings.all (fun s =>
    (List.range (s.length + 2)).all (fun i =>
      (testAlphabet ++ ['z', '\n', Char.ofNat 0]).all (fun c =>
        postCheck (.str s) (duplicate_chars_checked (.str s)) i c))) = true := by
  native_decide

-- Bounded rejection_prop and exceptional Post_prop checks over the same input set.
example : (testStrings.map PythonInput.str ++ [PythonInput.nonString]).all (fun input =>
    (pre input || decide
      (duplicate_chars_checked input = Except.error "Input must be a string")) &&
    postCheck input (duplicate_chars_checked input) 0 'z') = true := by
  native_decide

-- Bounded append_prop checks, including Unicode and empty strings.
example : (shortWords 2).all (fun xs => (shortWords 2).all (fun ys =>
    duplicate_chars (String.mk xs ++ String.mk ys) ==
      duplicate_chars (String.mk xs) ++ duplicate_chars (String.mk ys))) = true := by
  native_decide

#eval testStrings.length

/- Correctness, with the requested Pre → Post statement. -/

theorem duplicate_chars_total_correct (input : PythonInput) :
    Post_prop input (duplicate_chars_checked input) := by
  constructor
  · intro s hs
    subst input
    exact ⟨duplicate_chars s, rfl, sequence_thm s, length_thm s,
      positions_thm s, empty_thm s, count_thm s⟩
  · exact rejection_thm input

theorem duplicate_chars_correct (input : PythonInput) (_h : Pre input) :
    Post_prop input (duplicate_chars_checked input) := by
  exact duplicate_chars_total_correct input

/- Imperative implementation: append twice to a mutable string for each character. -/

def duplicate_chars_imperative (s : String) : String := Id.run do
  let mut output := ""
  for c in s.toList do
    output := output.push c
    output := output.push c
  return output

def duplicate_chars_checked_imperative : PythonInput → Except String String
  | .str s => .ok (duplicate_chars_imperative s)
  | .nonString => .error "Input must be a string"

/- Imperative tests. -/

example : duplicate_chars_imperative "abc" = "aabbcc" := by native_decide
example : duplicate_chars_imperative "" = "" := by native_decide
example : duplicate_chars_imperative "!a " = "!!aa  " := by native_decide
example : duplicate_chars_imperative "é🙂" = "éé🙂🙂" := by native_decide
example : duplicate_chars_checked_imperative .nonString =
    .error "Input must be a string" := by native_decide

#eval duplicate_chars_imperative "abc"
#eval duplicate_chars_checked_imperative .nonString

#eval Plausible.Testable.check (∀ s : String,
  duplicate_chars s = duplicate_chars_imperative s)

example : testStrings.all (fun s =>
    duplicate_chars s == duplicate_chars_imperative s) = true := by native_decide

/- The loop invariant describes any initial accumulator and remaining input. -/

private theorem duplicate_foldl (xs : List Char) (acc : String) :
    (xs.foldl (fun output c => (output.push c).push c) acc).toList =
      acc.toList ++ xs.flatMap (fun c => [c, c]) := by
  induction xs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    simpa [List.foldl_cons, List.flatMap_cons, String.toList, String.data_push,
      List.append_assoc] using ih ((acc.push c).push c)

theorem duplicate_chars_equiv (s : String) :
    duplicate_chars s = duplicate_chars_imperative s := by
  have loop : duplicate_chars_imperative s =
      s.toList.foldl (fun output c => (output.push c).push c) "" := by
    simp [duplicate_chars_imperative]
  apply String.toList_inj.mp
  rw [loop, duplicate_foldl]
  rfl

theorem duplicate_chars_checked_equiv (input : PythonInput) :
    duplicate_chars_checked input = duplicate_chars_checked_imperative input := by
  cases input with
  | str s => simp [duplicate_chars_checked, duplicate_chars_checked_imperative,
      duplicate_chars_equiv]
  | nonString => rfl

end DuplicateChars
