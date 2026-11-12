import Mathlib

/-!
# Duplicate each character

Translation of Python's `duplicate_chars`. Strings are traversed as lists of
Unicode characters, not UTF-8 bytes. `Input` is the abstraction of Python values
observed by `isinstance(s, str)`: every string retains its contents and every
non-string (including `None`) is represented by `nonString`. No other property of
an invalid value is inspected by the Python program. The checked interface uses
`Except` to represent the ValueError, including its original message.
-/

namespace DuplicateChars

/-- The functional implementation on the valid, statically typed domain. -/
def duplicate_chars (s : String) : String :=
  String.mk (s.data.flatMap fun c => [c, c])

inductive Input where
  | str (s : String)
  | nonString
  deriving DecidableEq, Repr

inductive InputError where
  | valueError (message : String)
  deriving DecidableEq, Repr

deriving instance DecidableEq for Except

/-- A total model of the Python function, including its exceptional behavior. -/
def duplicate_chars_checked : Input → Except InputError String
  | .str s => .ok (duplicate_chars s)
  | .nonString => .error (.valueError "Input must be a string")

example : duplicate_chars "abc" = "aabbcc" := by native_decide
example : duplicate_chars "" = "" := by native_decide
example : duplicate_chars "!a " = "!!aa  " := by native_decide
example : duplicate_chars "é🙂" = "éé🙂🙂" := by native_decide
example : duplicate_chars_checked (.str "abc") = .ok "aabbcc" := by native_decide
-- `None`, like every non-string Python value, is represented by `nonString`.
example : duplicate_chars_checked .nonString =
    .error (.valueError "Input must be a string") := by native_decide
#eval duplicate_chars "abc"
#eval duplicate_chars ""
#eval duplicate_chars "!a "
#eval duplicate_chars_checked .nonString

/-- Exactly the Python precondition: the input must be a string. -/
def Pre : Input → Prop
  | .str _ => True
  | .nonString => False

instance (x : Input) : Decidable (Pre x) := by
  cases x <;> simp only [Pre] <;> infer_instance

/-- Exact character sequence, including the order of the duplicates. -/
def chars_prop (s : String) : Prop :=
  (duplicate_chars s).data = s.data.flatMap (fun c => [c, c])

theorem chars_thm (s : String) : chars_prop s := by
  simp [chars_prop, duplicate_chars]

/-- Length counts characters, not UTF-8 bytes. -/
def length_prop (s : String) : Prop :=
  (duplicate_chars s).length = 2 * s.length

private theorem duplicateList_length (xs : List Char) :
    (xs.flatMap fun c => [c, c]).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem length_thm (s : String) : length_prop s := by
  change (s.data.flatMap fun c => [c, c]).length = 2 * s.data.length
  exact duplicateList_length s.data

/-- Both positions of every output pair equal the corresponding input position.
The use of optional indexing also specifies all out-of-bounds positions. -/
def pairs_prop (s : String) : Prop :=
  ∀ i : Nat,
    (duplicate_chars s).data[2 * i]? = s.data[i]? ∧
    (duplicate_chars s).data[2 * i + 1]? = s.data[i]?

private theorem duplicateList_pairs (xs : List Char) (i : Nat) :
    (xs.flatMap fun c => [c, c])[2 * i]? = xs[i]? ∧
    (xs.flatMap fun c => [c, c])[2 * i + 1]? = xs[i]? := by
  induction xs generalizing i with
  | nil => simp
  | cons c xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa [List.flatMap_cons, Nat.mul_succ, Nat.add_assoc] using ih i

theorem pairs_thm (s : String) : pairs_prop s := by
  intro i
  exact duplicateList_pairs s.data i

/-- The output is empty exactly when the input is empty. -/
def empty_prop (s : String) : Prop :=
  duplicate_chars s = "" ↔ s = ""

theorem empty_thm (s : String) : empty_prop s := by
  cases s with
  | mk xs =>
    change String.mk (xs.flatMap fun c => [c, c]) = String.mk [] ↔
      String.mk xs = String.mk []
    simp only [String.mk.injEq]
    cases xs <;> simp

/-- Duplication respects concatenation. -/
def append_prop (s t : String) : Prop :=
  duplicate_chars (s ++ t) = duplicate_chars s ++ duplicate_chars t

theorem append_thm (s t : String) : append_prop s t := by
  unfold append_prop
  apply String.ext
  simp [duplicate_chars, List.flatMap_append]

/-- The checked function returns normally on precisely the valid branch. -/
def valid_result_prop (s : String) : Prop :=
  duplicate_chars_checked (.str s) = .ok (duplicate_chars s)

theorem valid_result_thm (s : String) : valid_result_prop s := by
  rfl

/-- All non-string inputs raise the prescribed ValueError. -/
def rejection_prop (x : Input) : Prop :=
  ¬ Pre x → duplicate_chars_checked x =
    .error (.valueError "Input must be a string")

theorem rejection_thm (x : Input) : rejection_prop x := by
  cases x <;> simp [rejection_prop, Pre, duplicate_chars_checked]

/-- Postcondition for the total checked interface. The valid branch specifies
its returned value and the character-level properties of that value; rejection
is specified independently of the precondition. Concatenation is an additional
metamorphic property, proved above for arbitrary pairs of strings. -/
def Post_prop (x : Input) : Prop :=
  rejection_prop x ∧
  match x with
  | .str s => valid_result_prop s ∧ chars_prop s ∧ length_prop s ∧
      pairs_prop s ∧ empty_prop s
  | .nonString => True

/-! ## Bounded property-based tests

Exhaust all strings of length at most three over six distinct characters,
including whitespace, punctuation, and multibyte Unicode characters. Additional
longer strings exercise repetitions and concatenation. These tests are evidence,
not dependencies of any theorem. Every `_prop` has an executable check below.
The indexing checks include positions beyond the end of each string.
-/

private def alphabet : List Char := ['a', 'b', '!', ' ', 'é', '🙂']

private def wordsUpTo : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun c => (wordsUpTo n).map (c :: ·))

private def sampleStrings : List String :=
  (wordsUpTo 3).map String.mk ++ ["aaaaaa", "abcabc", "!a é🙂", "a\nb\t"]

private def sampleInputs : List Input :=
  .nonString :: sampleStrings.map Input.str

private def charsCheck (s : String) : Bool :=
  decide ((duplicate_chars s).data = s.data.flatMap (fun c => [c, c]))

private def lengthCheck (s : String) : Bool :=
  decide ((duplicate_chars s).length = 2 * s.length)

private def pairsCheck (s : String) : Bool :=
  (List.range (s.length + 3)).all fun i =>
    decide ((duplicate_chars s).data[2 * i]? = s.data[i]?) &&
    decide ((duplicate_chars s).data[2 * i + 1]? = s.data[i]?)

private def emptyCheck (s : String) : Bool :=
  decide (duplicate_chars s = "" ↔ s = "")

private def appendCheck (s t : String) : Bool :=
  decide (duplicate_chars (s ++ t) = duplicate_chars s ++ duplicate_chars t)

private def validResultCheck (s : String) : Bool :=
  decide (duplicate_chars_checked (.str s) = .ok (duplicate_chars s))

private def rejectionCheck (x : Input) : Bool :=
  decide (¬ Pre x → duplicate_chars_checked x =
    .error (.valueError "Input must be a string"))

private def postCheck (x : Input) : Bool :=
  rejectionCheck x && match x with
  | .str s => validResultCheck s && charsCheck s && lengthCheck s &&
      pairsCheck s && emptyCheck s
  | .nonString => true

-- PBT for chars_prop.
example : sampleStrings.all charsCheck = true := by native_decide
-- PBT for length_prop.
example : sampleStrings.all lengthCheck = true := by native_decide
-- PBT for pairs_prop (including out-of-bounds indices).
example : sampleStrings.all pairsCheck = true := by native_decide
-- PBT for empty_prop.
example : sampleStrings.all emptyCheck = true := by native_decide
-- PBT for append_prop: all pairs of generated strings.
example : sampleStrings.all (fun s => sampleStrings.all (appendCheck s)) = true := by
  native_decide
-- PBT for valid_result_prop.
example : sampleStrings.all validResultCheck = true := by native_decide
-- PBT for rejection_prop, on both valid and invalid inputs.
example : sampleInputs.all rejectionCheck = true := by native_decide
-- PBT for the entire Post_prop, with the pair-index quantifier bounded as above.
example : sampleInputs.all postCheck = true := by native_decide
#eval (sampleStrings.length, sampleInputs.all postCheck)
#eval sampleStrings.all (fun s => sampleStrings.all (appendCheck s))

/-- The Python precondition implies the complete normal-return postcondition. -/
theorem correctness_thm (x : Input) : Pre x → Post_prop x := by
  intro hx
  cases x with
  | str s =>
    exact ⟨rejection_thm (.str s), valid_result_thm s, chars_thm s,
      length_thm s, pairs_thm s, empty_thm s⟩
  | nonString => exact False.elim hx

/-! ## Imperative implementation -/

/-- Iterate over characters, mutating an initially empty string by two pushes. -/
def duplicate_chars_imperative (s : String) : String := Id.run do
  let mut result := ""
  for c in s.data do
    result := result.push c
    result := result.push c
  return result

def duplicate_chars_checked_imperative (x : Input) : Except InputError String := Id.run do
  match x with
  | .str s => return .ok (duplicate_chars_imperative s)
  | .nonString => return .error (.valueError "Input must be a string")

example : duplicate_chars_imperative "abc" = "aabbcc" := by native_decide
example : duplicate_chars_imperative "" = "" := by native_decide
example : duplicate_chars_imperative "!a " = "!!aa  " := by native_decide
example : duplicate_chars_imperative "é🙂" = "éé🙂🙂" := by native_decide
example : duplicate_chars_checked_imperative .nonString =
    .error (.valueError "Input must be a string") := by native_decide
example : sampleStrings.all (fun s =>
    decide (duplicate_chars s = duplicate_chars_imperative s)) = true := by native_decide
example : sampleInputs.all (fun x =>
    decide (duplicate_chars_checked x = duplicate_chars_checked_imperative x)) = true := by
  native_decide
#eval duplicate_chars_imperative "!a "
#eval duplicate_chars_checked_imperative .nonString

/-- Loop invariant: processing the remaining list appends precisely its doubled
characters to the existing accumulator, without modifying that prefix. -/
private theorem push_fold (xs : List Char) (acc : String) :
    xs.foldl (fun out c => (out.push c).push c) acc =
      String.mk (acc.data ++ xs.flatMap (fun c => [c, c])) := by
  induction xs generalizing acc with
  | nil => simp
  | cons c xs ih =>
    simp only [List.foldl_cons, ih]
    apply String.ext
    simp [List.flatMap_cons, List.append_assoc]

/-- Functional–imperative equivalence on all strings. -/
theorem equivalence_thm (s : String) :
    duplicate_chars s = duplicate_chars_imperative s := by
  simp [duplicate_chars_imperative, push_fold, duplicate_chars]

/-- Equivalence also preserves the exceptional behavior for every input. -/
theorem checked_equivalence_thm (x : Input) :
    duplicate_chars_checked x = duplicate_chars_checked_imperative x := by
  cases x <;> simp [duplicate_chars_checked, duplicate_chars_checked_imperative,
    equivalence_thm]

end DuplicateChars
