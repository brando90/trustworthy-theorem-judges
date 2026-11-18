import Mathlib
namespace Agent

/-!
# Removing digit characters

A translation of Python's `remove_digits`. Strings are Unicode scalar sequences.
`pythonIsDigit` uses the Unicode 15.0.0 Numeric_Type=Decimal/Digit
code points (the semantics of CPython `str.isdigit`, including superscripts and
non-ASCII digits). This is intentionally not Lean's ASCII-only `Char.isDigit`.
The table is a self-contained snapshot of the Unicode database used by Python.
`Input.nonString` abstracts every non-string value, including Python's `None`;
the checked API returns the corresponding ValueError as an `Except` result.
-/

namespace RemoveDigits
deriving instance DecidableEq for Except

private def digitRanges : List (Nat × Nat) :=
  [(48, 57), (178, 179), (185, 185), (1632, 1641),
   (1776, 1785), (1984, 1993), (2406, 2415), (2534, 2543),
   (2662, 2671), (2790, 2799), (2918, 2927), (3046, 3055),
   (3174, 3183), (3302, 3311), (3430, 3439), (3558, 3567),
   (3664, 3673), (3792, 3801), (3872, 3881), (4160, 4169),
   (4240, 4249), (4969, 4977), (6112, 6121), (6160, 6169),
   (6470, 6479), (6608, 6618), (6784, 6793), (6800, 6809),
   (6992, 7001), (7088, 7097), (7232, 7241), (7248, 7257),
   (8304, 8304), (8308, 8313), (8320, 8329), (9312, 9320),
   (9332, 9340), (9352, 9360), (9450, 9450), (9461, 9469),
   (9471, 9471), (10102, 10110), (10112, 10120), (10122, 10130),
   (42528, 42537), (43216, 43225), (43264, 43273), (43472, 43481),
   (43504, 43513), (43600, 43609), (44016, 44025), (65296, 65305),
   (66720, 66729), (68160, 68163), (68912, 68921), (69216, 69224),
   (69714, 69722), (69734, 69743), (69872, 69881), (69942, 69951),
   (70096, 70105), (70384, 70393), (70736, 70745), (70864, 70873),
   (71248, 71257), (71360, 71369), (71472, 71481), (71904, 71913),
   (72016, 72025), (72784, 72793), (73040, 73049), (73120, 73129),
   (73552, 73561), (92768, 92777), (92864, 92873), (93008, 93017),
   (120782, 120831), (123200, 123209), (123632, 123641), (124144, 124153),
   (125264, 125273), (127232, 127242), (130032, 130041)]

def pythonIsDigit (c : Char) : Bool :=
  digitRanges.any fun r => r.1 ≤ c.toNat && c.toNat ≤ r.2

def keep (c : Char) : Bool := !pythonIsDigit c

def removeDigits (s : String) : String :=
  String.mk (s.toList.filter keep)

inductive Input where
  | str : String → Input
  | nonString : Input
  deriving DecidableEq, Repr

def checkedRemoveDigits : Input → Except String String
  | .str s => .ok (removeDigits s)
  | .nonString => .error "Input must be a string"

example : removeDigits "abc123def" = "abcdef" := by native_decide
example : removeDigits "" = "" := by native_decide
example : removeDigits "no numbers" = "no numbers" := by native_decide
example : removeDigits "123" = "" := by native_decide
example : removeDigits "a١٢۳४９²⑨𝟘b½Ⅳ" = "ab½Ⅳ" := by native_decide
example : checkedRemoveDigits .nonString = .error "Input must be a string" := by
  native_decide
#eval removeDigits "abc123def"
#eval checkedRemoveDigits .nonString

/-! ## Precondition and mathematical properties -/

/-- Exactly the dynamic type check `isinstance(s, str)`. -/
def Pre : Input → Prop
  | .str _ => True
  | .nonString => False

/-- Exact character sequence: this also specifies order and multiplicity. -/
def exact_prop (s out : String) : Prop :=
  out.toList = s.toList.filter keep

theorem exact_thm (s : String) : exact_prop s (removeDigits s) := by
  rfl

/-- Every output character is a non-digit. -/
def noDigits_prop (out : String) : Prop :=
  ∀ c ∈ out.toList, pythonIsDigit c = false

theorem noDigits_thm (s : String) : noDigits_prop (removeDigits s) := by
  intro c hc
  have h := (List.mem_filter.mp hc).2
  simpa [keep] using h

/-- The output is a subsequence of the input, not a rearrangement. -/
def order_prop (s out : String) : Prop := out.toList.Sublist s.toList

theorem order_thm (s : String) : order_prop s (removeDigits s) := by
  exact List.filter_sublist

/-- Every non-digit occurrence is retained, and every digit occurrence removed. -/
def preservation_prop (s out : String) : Prop :=
  ∀ c : Char, out.toList.count c =
    if pythonIsDigit c then 0 else s.toList.count c

theorem preservation_thm (s : String) : preservation_prop s (removeDigits s) := by
  intro c
  change (s.toList.filter keep).count c = _
  cases h : pythonIsDigit c with
  | false => exact List.count_filter (show keep c = true by simp [keep, h])
  | true =>
    have hnot : c ∉ s.toList.filter keep := by
      simp [List.mem_filter, keep, h]
    exact List.count_eq_zero.mpr hnot

/-- Length here counts characters, as Python `len`, not UTF-8 bytes. -/
def length_prop (s out : String) : Prop := out.length ≤ s.length

theorem length_thm (s : String) : length_prop s (removeDigits s) := by
  exact List.length_filter_le keep s.toList

/-- A second call does not change the result. -/
def idempotent_prop (out : String) : Prop := removeDigits out = out

theorem idempotent_thm (s : String) : idempotent_prop (removeDigits s) := by
  apply String.ext
  simp [removeDigits, String.toList, List.filter_filter]

/-- Inputs containing no digits are unchanged. -/
def unchanged_prop (s out : String) : Prop :=
  (∀ c ∈ s.toList, pythonIsDigit c = false) → out = s

theorem unchanged_thm (s : String) : unchanged_prop s (removeDigits s) := by
  intro h
  apply String.ext
  apply List.filter_eq_self.mpr
  intro c hc
  simp [keep, h c hc]

/-- The output is empty exactly when every input character is a digit.
This includes the empty input, by vacuous quantification. -/
def emptyIff_prop (s out : String) : Prop :=
  out = "" ↔ ∀ c ∈ s.toList, pythonIsDigit c = true

theorem emptyIff_thm (s : String) : emptyIff_prop s (removeDigits s) := by
  change String.mk (s.toList.filter keep) = String.mk [] ↔ _
  rw [String.mk.injEq]
  simp [List.filter_eq_nil_iff, keep]

/-- Filtering respects concatenation and thus preserves the order across chunks. -/
def append_prop (a b : String) : Prop :=
  removeDigits (a ++ b) = removeDigits a ++ removeDigits b

theorem append_thm (a b : String) : append_prop a b := by
  apply String.ext
  exact List.filter_append a.toList b.toList

/-- Non-string input produces precisely the Python ValueError message. -/
def error_prop (v : Input) : Prop :=
  ¬ Pre v → checkedRemoveDigits v = .error "Input must be a string"

theorem error_thm (v : Input) : error_prop v := by
  cases v <;> simp [error_prop, Pre, checkedRemoveDigits]

/-- A complete contract for the dynamic API. For strings, all of the properties
hold of the returned string. For non-strings, the specified error is returned. -/
def Post_prop (v : Input) (result : Except String String) : Prop :=
  (∀ s, v = .str s → ∃ out, result = .ok out ∧
    exact_prop s out ∧ noDigits_prop out ∧ order_prop s out ∧
    preservation_prop s out ∧ length_prop s out ∧ idempotent_prop out ∧
    unchanged_prop s out ∧ emptyIff_prop s out) ∧
  (¬ Pre v → result = .error "Input must be a string")

/-! ## Bounded property-based tests

Exhaust all words of length at most three over a mixed 16-character alphabet.
It contains repeated-letter opportunities, ASCII and Unicode digits, non-digit
numeric characters, non-Latin letters, whitespace, NUL, and an emoji. Also test
both endpoints and neighboring characters of every Unicode digit interval.
The checks below are executable forms of the propositions, not proof tactics.
-/

private def testAlphabet : List Char :=
  ['a', 'β', '中', ' ', '\n', Char.ofNat 0, '0', '9',
   '١', '²', '⑨', '½', 'Ⅳ', '𝟘', '９', '😀']

private def testWords : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: testAlphabet.flatMap (fun c => (testWords n).map (c :: ·))

private def boundaryStrings : List String :=
  digitRanges.flatMap fun (lo, hi) =>
    [lo - 1, lo, hi, hi + 1].map fun n => String.mk ['a', Char.ofNat n, 'b', '9']

private def testStrings : List String :=
  (testWords 3).map String.mk ++ boundaryStrings

private def testInputs : List Input :=
  .nonString :: testStrings.map Input.str

private def exactCheck (s out : String) : Bool :=
  out.toList == s.toList.filter keep

private def noDigitsCheck (out : String) : Bool := out.toList.all keep

private def orderCheck (s out : String) : Bool :=
  decide (out.toList.Sublist s.toList)

/-- Checking the union of the two supports suffices: outside it both counts
are zero. Thus this checks all character multiplicities, not just a sample. -/
private def preservationCheck (s out : String) : Bool :=
  (s.toList ++ out.toList).all fun c =>
    out.toList.count c == if pythonIsDigit c then 0 else s.toList.count c

private def lengthCheck (s out : String) : Bool := out.length ≤ s.length

private def idempotentCheck (out : String) : Bool := removeDigits out == out

private def unchangedCheck (s out : String) : Bool :=
  !noDigitsCheck s || out == s

private def emptyIffCheck (s out : String) : Bool :=
  (out == "") == s.toList.all pythonIsDigit

private def errorCheck (v : Input) (result : Except String String) : Bool :=
  match v with
  | .str _ => true
  | .nonString => decide (result = .error "Input must be a string")

private def postCheck (v : Input) (result : Except String String) : Bool :=
  match v, result with
  | .str s, .ok out =>
    exactCheck s out && noDigitsCheck out && orderCheck s out &&
    preservationCheck s out && lengthCheck s out && idempotentCheck out &&
    unchangedCheck s out && emptyIffCheck s out
  | .nonString, .error message => message == "Input must be a string"
  | _, _ => false

-- PBT: exact_prop
example : testStrings.all (fun s => exactCheck s (removeDigits s)) = true := by
  native_decide
-- PBT: noDigits_prop
example : testStrings.all (fun s => noDigitsCheck (removeDigits s)) = true := by
  native_decide
-- PBT: order_prop
example : testStrings.all (fun s => orderCheck s (removeDigits s)) = true := by
  native_decide
-- PBT: preservation_prop
example : testStrings.all (fun s => preservationCheck s (removeDigits s)) = true := by
  native_decide
-- PBT: length_prop
example : testStrings.all (fun s => lengthCheck s (removeDigits s)) = true := by
  native_decide
-- PBT: idempotent_prop
example : testStrings.all (fun s => idempotentCheck (removeDigits s)) = true := by
  native_decide
-- PBT: unchanged_prop (decidable implication; digit-free cases are included)
example : testStrings.all (fun s => unchangedCheck s (removeDigits s)) = true := by
  native_decide
-- PBT: emptyIff_prop (includes empty and all-digit words)
example : testStrings.all (fun s => emptyIffCheck s (removeDigits s)) = true := by
  native_decide
-- PBT: append_prop; all pairs of words of length at most two.
example : ((testWords 2).map String.mk).all (fun a =>
    ((testWords 2).map String.mk).all (fun b =>
      removeDigits (a ++ b) == removeDigits a ++ removeDigits b)) = true := by
  native_decide
-- PBT: error_prop, on both admissible and inadmissible input constructors.
example : testInputs.all (fun v => errorCheck v (checkedRemoveDigits v)) = true := by
  native_decide
-- PBT: Post_prop, including the error branch, not just valid inputs.
example : testInputs.all (fun v => postCheck v (checkedRemoveDigits v)) = true := by
  native_decide
#eval (testStrings.length, testInputs.all (fun v => postCheck v (checkedRemoveDigits v)))

/-! ## Correctness -/

/-- The complete contract holds even on invalid inputs, with an error result. -/
theorem Post_thm (v : Input) : Post_prop v (checkedRemoveDigits v) := by
  refine ⟨?_, error_thm v⟩
  intro s hv
  subst v
  exact ⟨removeDigits s, rfl, exact_thm s, noDigits_thm s, order_thm s,
    preservation_thm s, length_thm s, idempotent_thm s, unchanged_thm s,
    emptyIff_thm s⟩

/-- In particular, the required precondition implies the postcondition. -/
theorem correctness (v : Input) (_h : Pre v) :
    Post_prop v (checkedRemoveDigits v) := by
  exact Post_thm v

/-! ## Imperative implementation -/

/-- A mutable left-to-right accumulator, matching the generator-and-join loop. -/
def removeDigitsImperative (s : String) : String := Id.run do
  let mut out : List Char := []
  for c in s.toList do
    if keep c then
      out := out ++ [c]
  return String.mk out

def checkedRemoveDigitsImperative : Input → Except String String
  | .str s => .ok (removeDigitsImperative s)
  | .nonString => .error "Input must be a string"

example : removeDigitsImperative "abc123def" = "abcdef" := by native_decide
example : removeDigitsImperative "" = "" := by native_decide
example : removeDigitsImperative "no numbers" = "no numbers" := by native_decide
example : removeDigitsImperative "123" = "" := by native_decide
example : removeDigitsImperative "a١٢۳४９²⑨𝟘b½Ⅳ" = "ab½Ⅳ" := by native_decide
example : checkedRemoveDigitsImperative .nonString = .error "Input must be a string" := by
  native_decide
example : testInputs.all (fun v =>
    decide (checkedRemoveDigits v = checkedRemoveDigitsImperative v)) = true := by
  native_decide
#eval removeDigitsImperative "abc123def"
#eval checkedRemoveDigitsImperative .nonString

/-! ## Loop invariant and equivalence -/

private def collect (xs : List Char) (initial : List Char) : List Char := Id.run do
  let mut out := initial
  for c in xs do
    if keep c then
      out := out ++ [c]
  return out

/-- For arbitrary initial state, the loop appends exactly the retained sequence. -/
private theorem collect_eq (xs initial : List Char) :
    collect xs initial = initial ++ xs.filter keep := by
  induction xs generalizing initial with
  | nil => simp [collect]
  | cons c cs ih =>
    cases h : keep c <;> simp_all [collect, List.forIn_cons, List.append_assoc]

theorem functional_eq_imperative (s : String) :
    removeDigits s = removeDigitsImperative s := by
  change String.mk (s.toList.filter keep) = String.mk (collect s.toList [])
  rw [collect_eq]
  rfl

theorem checked_functional_eq_imperative (v : Input) :
    checkedRemoveDigits v = checkedRemoveDigitsImperative v := by
  cases v with
  | str s => simp [checkedRemoveDigits, checkedRemoveDigitsImperative,
      functional_eq_imperative]
  | nonString => rfl

end RemoveDigits
end Agent
