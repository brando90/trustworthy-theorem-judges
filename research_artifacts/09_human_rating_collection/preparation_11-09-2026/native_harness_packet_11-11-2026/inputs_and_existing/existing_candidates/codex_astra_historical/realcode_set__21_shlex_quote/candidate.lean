import Mathlib

/-!
# Python `shlex.quote`

A character-wise translation of the supplied quoting function, including the
benchmark wrapper's `TypeError` for every non-string input. `PythonValue.other`
represents all non-string Python values: the wrapper treats them identically,
including falsey values. Lean `String` represents the admissible string inputs.

The specification records each branch, exact apostrophe replacement, character
recovery, and output length. The decoder describes the quote syntax generated
here; it does not model process execution or operating-system restrictions on
arguments (in particular, NUL characters).
-/

namespace ShlexQuote

/-- The exact ASCII whitelist in the Python source. -/
def safeChars : List Char :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_@%+=:,./-".toList

def isSafeChar (c : Char) : Bool := safeChars.contains c

def allSafe (s : String) : Bool := s.toList.all isSafeChar

/-- Replace one apostrophe by the five characters: single, double, single,
double, single quote. All other characters are copied verbatim. -/
def escapeChunk (c : Char) : List Char :=
  if c = '\'' then ['\'', '"', '\'', '"', '\''] else [c]

def escapeChars : List Char → List Char
  | [] => []
  | c :: cs => escapeChunk c ++ escapeChars cs

def escape (s : String) : String := String.mk (escapeChars s.toList)

/-- The Python `quote` function on its string domain. -/
def quote (s : String) : String :=
  if s = "" then "''"
  else if allSafe s then s
  else "'" ++ escape s ++ "'"

inductive PythonValue where
  | string (value : String)
  | other
  deriving DecidableEq, Repr

inductive QuoteError where
  | typeError (message : String)
  deriving DecidableEq, Repr

deriving instance DecidableEq for Except

/-- The main Python function, with exceptions represented explicitly. -/
def benchmark_quote : PythonValue → Except QuoteError String
  | .string s => .ok (quote s)
  | .other => .error (.typeError "expected string object")

-- The four tests supplied with the Python program.
example : quote "" = "''" := by native_decide
example : quote "abc" = "abc" := by native_decide
example : quote "a b c" = "'a b c'" := by native_decide
example : quote "a'b" = "'a'\"'\"'b'" := by native_decide
#eval ["", "abc", "a b c", "a'b"].map quote

-- Boundary cases: safe punctuation, consecutive quotes, Unicode, and controls.
example : quote "_@%+=:,./-" = "_@%+=:,./-" := by native_decide
example : quote "''" = "''\"'\"''\"'\"''" := by native_decide
example : quote "é🙂" = "'é🙂'" := by native_decide
example : quote "\n\t" = "'\n\t'" := by native_decide
example : benchmark_quote (.string "") = .ok "''" := by native_decide
example : benchmark_quote .other = .error (.typeError "expected string object") := by
  native_decide
#eval benchmark_quote .other

/-- Exactly the source precondition `isinstance(s, str)`. -/
def Pre : PythonValue → Prop
  | .string _ => True
  | .other => False

/-- A small decoder for unquoted safe characters, single-quoted literals, and
single apostrophes in double quotes. These are precisely the constructs emitted
by `quote`; no variable expansion or command execution is involved. -/
inductive QuoteMode where
  | unquoted | single | double
  deriving DecidableEq

def readWord : QuoteMode → List Char → Option (List Char)
  | .unquoted, [] => some []
  | .single, [] => none
  | .double, [] => none
  | .unquoted, c :: cs =>
      if c = '\'' then readWord .single cs
      else if c = '"' then readWord .double cs
      else if isSafeChar c then (c :: ·) <$> readWord .unquoted cs
      else none
  | .single, c :: cs =>
      if c = '\'' then readWord .unquoted cs
      else (c :: ·) <$> readWord .single cs
  | .double, c :: cs =>
      if c = '"' then readWord .unquoted cs
      else if c = '\'' then (c :: ·) <$> readWord .double cs
      else none

def decode (s : String) : Option String :=
  String.mk <$> readWord .unquoted s.toList

-- Structural facts used to prove the behavioral properties.
theorem allSafe_iff (s : String) :
    allSafe s = true ↔ ∀ c ∈ s.toList, c ∈ safeChars := by
  simp [allSafe, isSafeChar, List.all_eq_true]

theorem escapeChars_eq_flatMap (cs : List Char) :
    escapeChars cs = cs.flatMap escapeChunk := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [escapeChars, ih]

theorem escapeChars_length (cs : List Char) :
    (escapeChars cs).length = cs.length + 4 * cs.count '\'' := by
  induction cs with
  | nil => simp [escapeChars]
  | cons c cs ih =>
      by_cases h : c = '\''
      · subst c
        simp [escapeChars, escapeChunk, ih]
        omega
      · simp [escapeChars, escapeChunk, h, ih, List.count_cons_of_ne h]
        omega

theorem readWord_safe (cs : List Char) (h : cs.all isSafeChar = true) :
    readWord .unquoted cs = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      have hsingle : c ≠ '\'' := by
        intro hc
        subst c
        have : isSafeChar '\'' = false := by decide
        simp [this] at h
      have hdouble : c ≠ '"' := by
        intro hc
        subst c
        have : isSafeChar '"' = false := by decide
        simp [this] at h
      simp [readWord, hsingle, hdouble, h.1, ih h.2]

theorem readWord_escaped (cs rest : List Char) :
    readWord .single (escapeChars cs ++ '\'' :: rest) =
      (cs ++ ·) <$> readWord .unquoted rest := by
  induction cs with
  | nil => simp [escapeChars, readWord]
  | cons c cs ih =>
      by_cases h : c = '\''
      · subst c
        simp [escapeChars, escapeChunk, readWord, ih,
          Function.comp_def]
      · simp [escapeChars, escapeChunk, h, readWord, ih, Function.comp_def]

def empty_prop (s : String) : Prop := s = "" → quote s = "''"

theorem empty_thm (s : String) : empty_prop s := by
  intro h
  simp [quote, h]

def safe_prop (s : String) : Prop :=
  s ≠ "" → (∀ c ∈ s.toList, c ∈ safeChars) → quote s = s

theorem safe_thm (s : String) : safe_prop s := by
  intro hn hs
  simp [quote, hn, (allSafe_iff s).mpr hs]

/-- Exact output for any nonempty string containing an unsafe character. -/
def unsafe_prop (s : String) : Prop :=
  s ≠ "" → (∃ c ∈ s.toList, c ∉ safeChars) →
    quote s = "'" ++ String.mk (s.toList.flatMap escapeChunk) ++ "'"

theorem unsafe_thm (s : String) : unsafe_prop s := by
  intro hn hs
  have hsafe : allSafe s = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨c, hc, hu⟩ := hs
    exact hu ((allSafe_iff s).mp h c hc)
  simp [quote, hn, hsafe, escape, escapeChars_eq_flatMap]

def roundtrip_prop (s : String) : Prop := decode (quote s) = some s

theorem roundtrip_thm (s : String) : roundtrip_prop s := by
  unfold roundtrip_prop quote
  split_ifs with he hs
  · subst s
    rfl
  · change Option.map String.mk (readWord .unquoted s.toList) = some s
    rw [readWord_safe s.toList hs]
    rfl
  · change Option.map String.mk
      (readWord .single (escapeChars s.toList ++ ['\''])) = some s
    have h : readWord .single (escapeChars s.toList ++ ['\'']) = some s.toList := by
      simpa only [readWord, List.append_nil, Option.map_some, Option.map_eq_map] using
        readWord_escaped s.toList []
    rw [h]
    rfl

/-- Length is measured in characters, as in Python, rather than UTF-8 bytes. -/
def length_prop (s : String) : Prop :=
  (quote s).length =
    if s = "" then 2
    else if allSafe s then s.length
    else s.length + 4 * s.toList.count '\'' + 2

theorem length_thm (s : String) : length_prop s := by
  unfold length_prop quote
  split_ifs with he hs
  · rfl
  · rfl
  · simp only [String.length_append, escape, String.length_mk, escapeChars_length]
    have hl : s.toList.length = s.length := by simp [String.toList]
    change 1 + (s.toList.length + 4 * s.toList.count '\'') + 1 =
      s.length + 4 * s.toList.count '\'' + 2
    omega

def nonempty_prop (s : String) : Prop := quote s ≠ ""

theorem nonempty_thm (s : String) : nonempty_prop s := by
  intro h
  have hl := length_thm s
  unfold length_prop at hl
  rw [h] at hl
  split_ifs at hl with he hs
  · simp at hl
  · have : s = "" := by
      apply String.toList_inj.mp
      exact List.length_eq_zero_iff.mp hl.symm
    exact he this
  · simp only [String.length_empty] at hl
    omega

/-- A valid string input returns the functional implementation's result. -/
def stringResult_prop (x : PythonValue) : Prop :=
  ∀ s, x = .string s → benchmark_quote x = .ok (quote s)

theorem stringResult_thm (x : PythonValue) : stringResult_prop x := by
  intro s h
  simp [h, benchmark_quote]

/-- The wrapper rejects every non-string, including falsey non-strings. -/
def typeError_prop (x : PythonValue) : Prop :=
  ¬Pre x → benchmark_quote x = .error (.typeError "expected string object")

theorem typeError_thm (x : PythonValue) : typeError_prop x := by
  cases x <;> simp [typeError_prop, Pre, benchmark_quote]

/-- The complete contract combines all branch and preservation properties with
the dynamic wrapper's success and exception behavior. -/
def Post_prop (x : PythonValue) : Prop :=
  (match x with
   | .string s => empty_prop s ∧ safe_prop s ∧ unsafe_prop s ∧
       roundtrip_prop s ∧ length_prop s ∧ nonempty_prop s
   | .other => True) ∧
  stringResult_prop x ∧ typeError_prop x

/-! Bounded property-based tests. All words of length at most three over a
17-character alphabet are checked, together with every ASCII singleton and
longer boundary cases. This covers each branch, repeated apostrophes, shell
metacharacters, controls including NUL, and multibyte Unicode. The checks below
are executable Boolean counterparts of the propositions, not proof substitutes. -/

def testAlphabet : List Char :=
  ['a', 'Z', '0', '_', '-', ' ', '\'', '"', '$', ';', '\\', '\n', '\t',
    'é', '中', '🙂', Char.ofNat 0]

def wordsOfLength : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => testAlphabet.flatMap fun c => (wordsOfLength n).map (c :: ·)

def testStrings : List String :=
  ((List.range 4).flatMap wordsOfLength).map String.mk ++
  (List.range 128).map (fun n => String.singleton (Char.ofNat n)) ++
  [String.mk safeChars, String.mk (List.replicate 64 '\''),
    "hello; $(echo dangerous) && `echo text` | cat > file\n"]

def testInputs : List PythonValue :=
  .other :: testStrings.map PythonValue.string

def emptyCheck (s : String) : Bool :=
  decide (s = "" → quote s = "''")

def safeCheck (s : String) : Bool :=
  decide (s ≠ "" → allSafe s = true → quote s = s)

def unsafeCheck (s : String) : Bool :=
  decide (s ≠ "" → allSafe s = false →
    quote s = "'" ++ String.mk (s.toList.flatMap escapeChunk) ++ "'")

def roundtripCheck (s : String) : Bool := decide (decode (quote s) = some s)

def lengthCheck (s : String) : Bool :=
  decide ((quote s).length =
    if s = "" then 2 else if allSafe s then s.length
    else s.length + 4 * s.toList.count '\'' + 2)

def nonemptyCheck (s : String) : Bool := decide (quote s ≠ "")

def stringResultCheck (x : PythonValue) : Bool :=
  match x with
  | .string s => decide (benchmark_quote x = .ok (quote s))
  | .other => true

def typeErrorCheck (x : PythonValue) : Bool :=
  match x with
  | .string _ => true
  | .other => decide (benchmark_quote x = .error (.typeError "expected string object"))

def postCheck (x : PythonValue) : Bool :=
  (match x with
   | .string s => emptyCheck s && safeCheck s && unsafeCheck s &&
       roundtripCheck s && lengthCheck s && nonemptyCheck s
   | .other => true) &&
  stringResultCheck x && typeErrorCheck x

-- PBT: empty_prop.
example : testStrings.all emptyCheck = true := by native_decide
-- PBT: safe_prop; allSafe_iff proves the Boolean whitelist check equivalent.
example : testStrings.all safeCheck = true := by native_decide
-- PBT: unsafe_prop; allSafe = false means an unsafe character exists.
example : testStrings.all unsafeCheck = true := by native_decide
-- PBT: roundtrip_prop.
example : testStrings.all roundtripCheck = true := by native_decide
-- PBT: length_prop.
example : testStrings.all lengthCheck = true := by native_decide
-- PBT: nonempty_prop.
example : testStrings.all nonemptyCheck = true := by native_decide
-- PBT: stringResult_prop, on both dynamic input constructors.
example : testInputs.all stringResultCheck = true := by native_decide
-- PBT: typeError_prop, including the inadmissible input constructor.
example : testInputs.all typeErrorCheck = true := by native_decide
-- PBT: the complete Post_prop conjunction.
example : testInputs.all postCheck = true := by native_decide
#eval (testStrings.length, testInputs.all postCheck)

/-- Correctness on exactly the inputs allowed by the Python precondition. -/
theorem correctness_thm (x : PythonValue) : Pre x → Post_prop x := by
  intro hx
  cases x with
  | string s =>
      exact ⟨⟨empty_thm s, safe_thm s, unsafe_thm s, roundtrip_thm s,
        length_thm s, nonempty_thm s⟩, stringResult_thm _, typeError_thm _⟩
  | other => exact False.elim hx

/-- The contract also accounts for the wrapper's behavior outside Pre. -/
theorem total_correctness_thm (x : PythonValue) : Post_prop x := by
  cases x with
  | string s => exact correctness_thm (.string s) trivial
  | other => exact ⟨trivial, stringResult_thm _, typeError_thm _⟩

/-- A direct imperative translation: scan the whitelist with a mutable flag,
then append escaped characters to a mutable string only when quoting is needed. -/
def quoteImperative (s : String) : String := Id.run do
  if s = "" then
    return "''"
  let mut safe := true
  for c in s.toList do
    safe := safe && isSafeChar c
  if safe then
    return s
  let mut result := "'"
  for c in s.toList do
    result := if c = '\'' then result ++ "'\"'\"'" else result.push c
  result := result ++ "'"
  return result

def benchmark_quoteImperative (x : PythonValue) : Except QuoteError String := Id.run do
  match x with
  | .string s => return .ok (quoteImperative s)
  | .other => return .error (.typeError "expected string object")

example : quoteImperative "" = "''" := by native_decide
example : quoteImperative "abc" = "abc" := by native_decide
example : quoteImperative "a b c" = "'a b c'" := by native_decide
example : quoteImperative "a'b" = "'a'\"'\"'b'" := by native_decide
example : benchmark_quoteImperative .other =
    .error (.typeError "expected string object") := by native_decide
#eval ["", "abc", "a b c", "a'b"].map quoteImperative

-- Bounded PBT of equivalence, including errors and every generated string.
example : testInputs.all (fun x =>
    decide (benchmark_quote x = benchmark_quoteImperative x)) = true := by
  native_decide

theorem safe_fold (cs : List Char) (initial : Bool) :
    cs.foldl (fun acc c => acc && isSafeChar c) initial =
      (initial && cs.all isSafeChar) := by
  induction cs generalizing initial with
  | nil => simp
  | cons c cs ih => simp [List.foldl_cons, ih, Bool.and_assoc]

theorem escape_fold (cs : List Char) (initial : String) :
    cs.foldl (fun acc c =>
      if c = '\'' then acc ++ "'\"'\"'" else acc.push c) initial =
      initial ++ String.mk (escapeChars cs) := by
  induction cs generalizing initial with
  | nil => simp [escapeChars]
  | cons c cs ih =>
      simp only [List.foldl_cons, ih, escapeChars]
      by_cases h : c = '\''
      · subst c
        simp [escapeChunk, String.append_assoc]
        rfl
      · simp only [h, ↓reduceIte, escapeChunk]
        apply String.ext
        exact List.append_assoc initial.data [c] (escapeChars cs)

/-- The mutable loops compute exactly the recursive functional definition. -/
theorem quote_equivalence_thm (s : String) : quote s = quoteImperative s := by
  simp [quoteImperative, List.forIn_pure_yield_eq_foldl, safe_fold, escape_fold,
    quote, allSafe, escape]
  rfl

/-- Equivalence of the complete benchmark, including its TypeError branch. -/
theorem benchmark_equivalence_thm (x : PythonValue) :
    benchmark_quote x = benchmark_quoteImperative x := by
  cases x <;> simp [benchmark_quote, benchmark_quoteImperative, quote_equivalence_thm]

end ShlexQuote
