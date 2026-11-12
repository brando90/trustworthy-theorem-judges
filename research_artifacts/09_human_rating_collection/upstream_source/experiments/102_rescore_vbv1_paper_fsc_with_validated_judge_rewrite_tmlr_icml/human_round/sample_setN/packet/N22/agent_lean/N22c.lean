import Mathlib

/-!
# POSIX shell quoting

A translation of Python's `shlex.quote` and the checked `benchmark_quote` wrapper.
Strings are Unicode strings; the safe alphabet is deliberately ASCII only.
`Input.nonString` abstracts arbitrary non-string Python objects: their contents and
truth value are immaterial because the benchmark rejects them before calling quote.
`decodeWord` recognizes the shell syntax used by the encoder (safe unquoted text,
single-quoted text, and double-quoted apostrophes). It is not a general shell parser.
This is a character-level model, not an operating-system argument validity check:
NUL, for example, is retained by the encoder just as it is in Python.
-/

namespace ShlexQuote

-- Functional implementation.
def safeChars : String :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_@%+=:,./-"

def isSafe (c : Char) : Bool := safeChars.toList.contains c

def allSafe (s : String) : Bool := s.toList.all isSafe

/-- A quote ends the current single-quoted section, is emitted inside double
quotes, and then starts another single-quoted section. -/
def escapeChunk (c : Char) : List Char :=
  if c = '\'' then ['\'', '"', '\'', '"', '\''] else [c]

def escape (s : String) : String := String.mk (s.toList.flatMap escapeChunk)

def quote (s : String) : String :=
  if s = "" then "''"
  else if allSafe s then s
  else "'" ++ escape s ++ "'"

deriving instance DecidableEq for Except

inductive Input where
  | string (value : String)
  | nonString (description : String)
  deriving Repr, DecidableEq

def benchmarkQuote : Input → Except String String
  | .string s => .ok (quote s)
  | .nonString _ => .error "expected string object"

inductive Mode where
  | bare | single | double
  deriving DecidableEq, Repr

/-- A conservative, executable recognizer of a single shell word. No variable
expansion, command substitution, separators, or unquoted whitespace is accepted.
Inside single quotes every character other than the closing quote is literal. -/
def parseWord : Mode → List Char → Option (List Char)
  | .bare, [] => some []
  | .single, [] => none
  | .double, [] => none
  | .bare, c :: cs =>
      if c = '\'' then parseWord .single cs
      else if c = '"' then parseWord .double cs
      else if isSafe c then List.cons c <$> parseWord .bare cs
      else none
  | .single, c :: cs =>
      if c = '\'' then parseWord .bare cs
      else List.cons c <$> parseWord .single cs
  | .double, c :: cs =>
      if c = '"' then parseWord .bare cs
      else if c = '\'' then List.cons c <$> parseWord .double cs
      else none

def decodeWord (s : String) : Option String :=
  String.mk <$> parseWord .bare s.toList

-- The four tests from Python, plus Unicode, shell metacharacters and errors.
example : quote "" = "''" := by native_decide
example : quote "abc" = "abc" := by native_decide
example : quote "a b c" = "'a b c'" := by native_decide
example : quote "a'b" = "'a'\"'\"'b'" := by native_decide
example : quote "é" = "'é'" := by native_decide
example : quote "$(id);*" = "'$(id);*'" := by native_decide
example : benchmarkQuote (.nonString "None") = .error "expected string object" := by
  native_decide
#eval ["", "abc", "a b c", "a'b"].map quote
#eval decodeWord (quote "a'b $HOME\nλ")

/-- Exactly the Python precondition: the input has the string tag. -/
def Pre (x : Input) : Prop := ∃ s : String, x = .string s

-- Properties are stated for every string, not merely the sample inputs.
def empty_prop (s : String) : Prop := s = "" → quote s = "''"

theorem empty_thm (s : String) : empty_prop s := by
  intro h
  subst s
  rfl

def safe_prop (s : String) : Prop :=
  s ≠ "" → allSafe s = true → quote s = s

theorem safe_thm (s : String) : safe_prop s := by
  intro hn hs
  simp [quote, hn, hs]

def unsafe_prop (s : String) : Prop :=
  s ≠ "" → allSafe s = false → quote s = "'" ++ escape s ++ "'"

theorem unsafe_thm (s : String) : unsafe_prop s := by
  intro hn hs
  simp [quote, hn, hs]

/-- This is Python's single-character `replace("'", "'\"'\"'")`:
all occurrences are replaced, and no other character is changed. -/
def escape_prop (s : String) : Prop :=
  (escape s).toList = s.toList.flatMap
    (fun c => if c = '\'' then "'\"'\"'".toList else [c])

theorem escape_thm (s : String) : escape_prop s := by
  rfl

private theorem escaped_length (cs : List Char) :
    (cs.flatMap escapeChunk).length = cs.length + 4 * cs.count '\'' := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      by_cases hc : c = '\''
      · subst c
        simp [List.flatMap_cons, escapeChunk, ih]
        omega
      · simp [List.flatMap_cons, escapeChunk, hc, ih]
        omega

private theorem escape_length (s : String) :
    (escape s).length = s.length + 4 * s.toList.count '\'' := by
  exact escaped_length s.toList

/-- Length counts Unicode characters, as Python `len` does, not UTF-8 bytes. -/
def length_prop (s : String) : Prop :=
  (quote s).length =
    if s = "" then 2
    else if allSafe s then s.length
    else s.length + 4 * s.toList.count '\'' + 2

theorem length_thm (s : String) : length_prop s := by
  unfold length_prop quote
  split_ifs with hn hs
  · rfl
  · rfl
  · rw [String.length_append, String.length_append, escape_length]
    change 1 + (s.length + 4 * s.toList.count '\'') + 1 = _
    omega

def nonempty_prop (s : String) : Prop := quote s ≠ ""

theorem nonempty_thm (s : String) : nonempty_prop s := by
  unfold nonempty_prop quote
  split_ifs with hn hs
  · decide
  · exact hn
  · intro h
    have hl := congrArg String.length h
    rw [String.length_append, String.length_append] at hl
    change 1 + (escape s).length + 1 = 0 at hl
    omega

private theorem parse_safe (cs : List Char) (h : cs.all isSafe = true) :
    parseWord .bare cs = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      have hsingle : c ≠ '\'' := by
        intro hc
        subst c
        have hn : isSafe '\'' = false := by decide
        simp [hn] at h
      have hdouble : c ≠ '"' := by
        intro hc
        subst c
        have hn : isSafe '"' = false := by decide
        simp [hn] at h
      simp [parseWord, hsingle, hdouble, h.1, ih h.2]

private theorem parse_escaped (cs : List Char) :
    parseWord .single (cs.flatMap escapeChunk ++ ['\'']) = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      by_cases hc : c = '\''
      · subst c
        simp [List.flatMap_cons, escapeChunk, parseWord, ih]
      · simp [List.flatMap_cons, escapeChunk, hc, parseWord, ih]

/-- In the character-level shell-word model, the escaped result is one literal
word with exactly the original value. -/
def roundtrip_prop (s : String) : Prop := decodeWord (quote s) = some s

theorem roundtrip_thm (s : String) : roundtrip_prop s := by
  unfold roundtrip_prop
  by_cases hn : s = ""
  · subst s
    rfl
  · by_cases hs : allSafe s = true
    · simp only [quote, if_neg hn, if_pos hs, decodeWord]
      rw [parse_safe s.toList hs]
      rfl
    · simp only [quote, if_neg hn, if_neg hs, decodeWord]
      change String.mk <$> parseWord .single
        (s.toList.flatMap escapeChunk ++ ['\'']) = some s
      rw [parse_escaped]
      rfl

/-- The wrapper returns the string result for strings and the precise TypeError
message for every non-string input, including falsy non-strings. -/
def typing_prop (x : Input) : Prop :=
  (∀ s, x = .string s → benchmarkQuote x = .ok (quote s)) ∧
  (¬ Pre x → benchmarkQuote x = .error "expected string object")

theorem typing_thm (x : Input) : typing_prop x := by
  constructor
  · intro s hx
    subst x
    rfl
  · intro hn
    cases x with
    | string s => exact False.elim (hn ⟨s, rfl⟩)
    | nonString _ => rfl

/-- All behavioral properties, together with the wrapper's type contract. -/
def Post_prop (x : Input) : Prop :=
  typing_prop x ∧
  ∀ s, x = .string s →
    empty_prop s ∧ safe_prop s ∧ unsafe_prop s ∧ escape_prop s ∧
    length_prop s ∧ nonempty_prop s ∧ roundtrip_prop s

-- Bounded property-based tests. There is no dependency on a String sampler.
-- Exhaust all words of length at most three over an alphabet containing safe
-- characters, whitespace, both quotes, shell metacharacters, backslash and Unicode.
def testAlphabet : List Char :=
  ['a', 'Z', '0', '_', '-', ' ', '\'', '"', '$', ';', '\\', '\n', 'λ']

def wordsUpTo : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: testAlphabet.flatMap (fun c => (wordsUpTo n).map (c :: ·))

def testStrings : List String :=
  (wordsUpTo 3).map String.mk ++
  (List.range 128).map (fun n => String.singleton (Char.ofNat n)) ++
  [safeChars, "''''", "a'b'c", "日本語😀", "$(id);`pwd`|&<>*?()[]{}!#~",
   "\t\r\n", "a'\"'\\b", "--", "-n", "éλ😀"]

-- Each checker is the executable form of the corresponding proposition.
def emptyCheck (s : String) : Bool := decide (s = "" → quote s = "''")
def safeCheck (s : String) : Bool :=
  decide (s ≠ "" → allSafe s = true → quote s = s)
def unsafeCheck (s : String) : Bool :=
  decide (s ≠ "" → allSafe s = false → quote s = "'" ++ escape s ++ "'")
def escapeCheck (s : String) : Bool :=
  decide ((escape s).toList = s.toList.flatMap
    (fun c => if c = '\'' then "'\"'\"'".toList else [c]))
def lengthCheck (s : String) : Bool :=
  decide ((quote s).length =
    if s = "" then 2 else if allSafe s then s.length
    else s.length + 4 * s.toList.count '\'' + 2)
def nonemptyCheck (s : String) : Bool := decide (quote s ≠ "")
def roundtripCheck (s : String) : Bool := decide (decodeWord (quote s) = some s)

def testInputs : List Input :=
  testStrings.map Input.string ++ testStrings.map Input.nonString ++
  [ .nonString "None", .nonString "False", .nonString "0", .nonString "0.0",
    .nonString "[]", .nonString "{}", .nonString "bytes", .nonString "object" ]

/-- Case splitting removes the quantifiers in `typing_prop` without changing
its meaning: there is precisely one string payload, or no string payload. -/
def typingCheck (x : Input) : Bool :=
  match x with
  | .string s => decide (benchmarkQuote x = .ok (quote s))
  | .nonString _ => decide (benchmarkQuote x = .error "expected string object")

def postCheck (x : Input) : Bool :=
  typingCheck x && match x with
  | .string s => emptyCheck s && safeCheck s && unsafeCheck s && escapeCheck s &&
      lengthCheck s && nonemptyCheck s && roundtripCheck s
  | .nonString _ => true

-- PBT for each _prop, including Post_prop. These are tests, not theorem proofs.
example : testStrings.all emptyCheck = true := by native_decide
example : testStrings.all safeCheck = true := by native_decide
example : testStrings.all unsafeCheck = true := by native_decide
example : testStrings.all escapeCheck = true := by native_decide
example : testStrings.all lengthCheck = true := by native_decide
example : testStrings.all nonemptyCheck = true := by native_decide
example : testStrings.all roundtripCheck = true := by native_decide
example : testInputs.all typingCheck = true := by native_decide
example : testInputs.all postCheck = true := by native_decide

-- Additional differential test against Lean's general substring replacement.
example : testStrings.all (fun s =>
    decide (escape s = s.replace "'" "'\"'\"'")) = true := by native_decide
#eval (testStrings.length, testInputs.length, testInputs.all postCheck)

/-- Correctness on exactly the inputs admitted by Python's `pre_quote`. -/
theorem correctness_thm (x : Input) : Pre x → Post_prop x := by
  intro h
  rcases h with ⟨s, rfl⟩
  refine ⟨typing_thm _, ?_⟩
  intro t ht
  have hst : s = t := Input.string.inj ht
  subst t
  exact ⟨empty_thm s, safe_thm s, unsafe_thm s, escape_thm s,
    length_thm s, nonempty_thm s, roundtrip_thm s⟩

-- Imperative implementation: one character scan updates a safety flag and
-- an output buffer. The loop is independent of the functional flatMap.
def scanImperative (cs : List Char) (initial : Bool × List Char) :
    Bool × List Char := Id.run do
  let mut state := initial
  for c in cs do
    let chunk := if c = '\'' then ['\'', '"', '\'', '"', '\''] else [c]
    state := (state.1 && isSafe c, state.2 ++ chunk)
  return state

def quoteImperative (s : String) : String := Id.run do
  let mut result := "''"
  if s ≠ "" then
    let state := scanImperative s.toList (true, [])
    result := s
    if !state.1 then
      result := "'" ++ String.mk state.2 ++ "'"
  return result

def benchmarkQuoteImperative (x : Input) : Except String String := Id.run do
  let mut result : Except String String := .error "expected string object"
  match x with
  | .string s => result := .ok (quoteImperative s)
  | .nonString _ => pure ()
  return result

-- Imperative unit tests, then bounded equivalence checks.
example : quoteImperative "" = "''" := by native_decide
example : quoteImperative "abc" = "abc" := by native_decide
example : quoteImperative "a b c" = "'a b c'" := by native_decide
example : quoteImperative "a'b" = "'a'\"'\"'b'" := by native_decide
example : benchmarkQuoteImperative (.nonString "0") =
    .error "expected string object" := by native_decide
example : testStrings.all (fun s => decide (quote s = quoteImperative s)) = true := by
  native_decide
example : testInputs.all (fun x =>
    decide (benchmarkQuote x = benchmarkQuoteImperative x)) = true := by native_decide
#eval ["", "abc", "a b c", "a'b"].map quoteImperative
#eval benchmarkQuoteImperative (.nonString "None")

/-- The generalized accumulator invariant proves the loop for all initial
buffers and flags, not just the initial state used by quoteImperative. -/
private theorem scanImperative_invariant (cs : List Char) (initial : Bool × List Char) :
    scanImperative cs initial =
      (initial.1 && cs.all isSafe, initial.2 ++ cs.flatMap escapeChunk) := by
  induction cs generalizing initial with
  | nil => simp [scanImperative]
  | cons c cs ih =>
      have step : scanImperative (c :: cs) initial =
          scanImperative cs (initial.1 && isSafe c, initial.2 ++ escapeChunk c) := by
        simp [scanImperative, escapeChunk]
      rw [step, ih]
      simp [List.all_cons, List.flatMap_cons, Bool.and_assoc, List.append_assoc]

/-- Functional/imperative equivalence for every Unicode string. -/
theorem quote_equivalence_thm (s : String) : quote s = quoteImperative s := by
  by_cases hn : s = ""
  · simp [quote, quoteImperative, hn]
  · cases hs : s.data.all isSafe <;>
      simp [quote, quoteImperative, hn, scanImperative_invariant, allSafe, hs, escape]

/-- Equivalence also covers every rejected input, with the same error message. -/
theorem benchmark_equivalence_thm (x : Input) :
    benchmarkQuote x = benchmarkQuoteImperative x := by
  cases x <;> simp [benchmarkQuote, benchmarkQuoteImperative, quote_equivalence_thm]

end ShlexQuote
