import Mathlib

/-!
# 21_shlex_quote : a Lean 4 formalization of the Python `shlex.quote` benchmark

The benchmark program provides a function returning a shell-escaped version of the
given string, exactly as `shlex.quote` from the Python standard library:

* the empty string is quoted as `''`;
* a non-empty string all of whose characters are "safe" (the ASCII letters, the
  digits, and the punctuation underscore, at, percent, plus, equals, colon,
  comma, dot, slash and dash) is returned unchanged;
* every other string is wrapped in single quotes, each embedded single quote `'`
  being replaced by the five character sequence `'"'"'`;
* a non-string argument makes the entry point raise
  `TypeError("expected string object")`.

## Modelling notes

* In Lean 4 `String` is a structure with the single field `data : List Char`, so
  `String.toList`, `String.mk` and `String.append` are kernel transparent and
  `String.mk s.toList = s` holds by `rfl`.  All reasoning happens on `List Char`
  and is lifted back to `String`.
* Python's `all(c in safe_chars for c in s)` is modelled by the structurally
  recursive `allSafe` (`String.all` is an opaque extern operation, so the kernel
  cannot reduce it).
* Python's `s.replace("'", "'\"'\"'")` is modelled by the structurally recursive
  `escapeQuotes`; agreement with `String.replace` is checked on concrete inputs
  and on an exhaustive enumeration of the short words over `a`, `'`, `"`, ` `.
* Python's dynamic `isinstance(s, str)` test is modelled by `PyVal`: a dynamic
  value is either `PyVal.str s` (a string) or `PyVal.other t` (a non-string,
  tagged with its type name).  `Pre` is exactly that test and `benchmarkQuote`
  raises the `TypeError` for the values that fail it.
* `unquote` is a small POSIX word parser (single and double quotes) used to state
  the semantic round trip `unquote (quote s) = s`: the escaped string denotes
  exactly `s` for a POSIX shell.
-/

namespace «21_shlex_quote»

/-! ## Implementation (functional definition) -/

/-- The characters that need no quoting in a POSIX shell (Python's `safe_chars`). -/
def safeChars : String :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_@%+=:,./-"

/-- `safe_chars` as a list of characters. -/
def safeCharList : List Char := safeChars.toList

/-- `c in safe_chars` -/
def isSafeChar (c : Char) : Bool := safeCharList.contains c

/-- `all(c in safe_chars for c in s)` -/
def allSafe : List Char → Bool
  | [] => true
  | c :: cs => isSafeChar c && allSafe cs

/-- The replacement text `'"'"'` used for an embedded single quote. -/
def sqEscape : List Char := "'\"'\"'".toList

/-- `s.replace("'", "'\"'\"'")` -/
def escapeQuotes : List Char → List Char
  | [] => []
  | c :: cs => (if c = '\'' then sqEscape else [c]) ++ escapeQuotes cs

/-- The number of single quotes in a word (used for the length property). -/
def numQuotes : List Char → Nat
  | [] => 0
  | c :: cs => (if c = '\'' then 1 else 0) + numQuotes cs

/-- The character level version of `quote`. -/
def quoteChars (cs : List Char) : List Char :=
  if cs = [] then ['\'', '\'']
  else if allSafe cs then cs
  else ['\''] ++ escapeQuotes cs ++ ['\'']

/-- `quote` from the Python program: a shell-escaped version of `s`. -/
def quote (s : String) : String := String.mk (quoteChars s.toList)

/-! ### A POSIX word parser, used to state the round-trip property -/

/-- Parser states: outside a quoted section, inside `'...'`, inside `"..."`. -/
inductive QState where
  | outside : QState
  | sq : QState
  | dq : QState

/-- Strip the shell quoting from a word: `'...'` and `"..."` sections are taken
literally, everything else is taken character by character. -/
def unquoteChars : QState → List Char → List Char
  | _, [] => []
  | .outside, c :: cs =>
      if c = '\'' then unquoteChars .sq cs
      else if c = '"' then unquoteChars .dq cs
      else c :: unquoteChars .outside cs
  | .sq, c :: cs =>
      if c = '\'' then unquoteChars .outside cs else c :: unquoteChars .sq cs
  | .dq, c :: cs =>
      if c = '"' then unquoteChars .outside cs else c :: unquoteChars .dq cs
  termination_by _st cs => cs

/-- The inverse of `quote`: what a POSIX shell makes of the quoted word. -/
def unquote (s : String) : String := String.mk (unquoteChars .outside s.toList)

/-! ### The dynamic entry point `benchmark_quote` -/

/-- A Python-like dynamic value: either a string, or a non-string value tagged
with the name of its type. -/
inductive PyVal where
  | str : String → PyVal
  | other : String → PyVal

/-- The message of the `TypeError` raised by the Python program. -/
def typeErrorMsg : String := "expected string object"

/-- `benchmark_quote`: quote the value, raising `TypeError` for non-strings. -/
def benchmarkQuote (v : PyVal) : Except String String :=
  match v with
  | PyVal.str s => Except.ok (quote s)
  | PyVal.other _ => Except.error typeErrorMsg

/-- The `check` function of the Python program. -/
def check (f : String → String) : Bool :=
  (f "" == "''") && (f "abc" == "abc") && (f "a b c" == "'a b c'") &&
    (f "a'b" == "'a'\"'\"'b'")

/-- The Python expression `"'" + s.replace("'", "'\"'\"'") + "'"`, written with
`String.replace`; used only to cross-check `quote` on concrete inputs. -/
def pyQuote (s : String) : String :=
  if s == "" then "''"
  else if allSafe s.toList then s
  else "'" ++ s.replace "'" "'\"'\"'" ++ "'"

/-! ## Unit tests -/

example : quote "" = "''" := rfl
example : quote "abc" = "abc" := by native_decide
example : quote "a b c" = "'a b c'" := by native_decide
example : quote "a'b" = "'a'\"'\"'b'" := by native_decide
example : quote "hello_world@1.2%3-4/5:6,7=8+9" = "hello_world@1.2%3-4/5:6,7=8+9" := by native_decide
example : quote "a*b" = "'a*b'" := by native_decide
example : quote "\"" = "'\"'" := by native_decide
example : quote "'" = "''\"'\"''" := by native_decide
example : quote "a'b" = "'" ++ "a'b".replace "'" "'\"'\"'" ++ "'" := by native_decide
example : quote "a b c" = pyQuote "a b c" := by native_decide
example : check quote = true := by native_decide
example : unquote (quote "a'b") = "a'b" := by native_decide
example : benchmarkQuote (PyVal.str "a b") = Except.ok "'a b'" := rfl
example : benchmarkQuote (PyVal.other "int") = Except.error typeErrorMsg := rfl
example : (match benchmarkQuote (PyVal.str "a b") with
    | Except.ok r => r
    | Except.error e => "TypeError: " ++ e) = "'a b'" := by native_decide
example : (match benchmarkQuote (PyVal.other "int") with
    | Except.ok r => r
    | Except.error e => "TypeError: " ++ e) = "TypeError: expected string object" := by native_decide
example : isSafeChar 'a' = true := by decide
example : isSafeChar '-' = true := by decide
example : isSafeChar ' ' = false := by decide
example : isSafeChar '\'' = false := by decide

#eval quote ""
#eval quote "abc"
#eval quote "a b c"
#eval quote "a'b"
#eval check quote
#eval unquote (quote "a'b")
#eval match benchmarkQuote (PyVal.other "int") with
  | Except.ok s => s
  | Except.error e => "TypeError: " ++ e

/-! ## Auxiliary lemmas -/

theorem mk_toList (s : String) : String.mk s.toList = s := rfl

theorem toList_mk (cs : List Char) : (String.mk cs).toList = cs := rfl

theorem toList_eq_nil (s : String) : s.toList = [] ↔ s = "" := by
  constructor
  · intro h
    have e := mk_toList s
    rw [h] at e
    exact e.symm
  · intro h
    rw [h]
    rfl

theorem allSafe_true : ∀ cs : List Char, allSafe cs = true ↔ ∀ c ∈ cs, isSafeChar c = true := by
  intro cs
  induction cs with
  | nil => simp [allSafe]
  | cons c cs ih => simp [allSafe, Bool.and_eq_true, ih]

theorem allSafe_eq_false {cs : List Char} (h : ¬(allSafe cs = true)) : allSafe cs = false := by
  cases hc : allSafe cs with
  | true => exact absurd hc h
  | false => rfl

theorem sqEscape_def : sqEscape = ['\'', '"', '\'', '"', '\''] := rfl

theorem sqEscape_length : sqEscape.length = 5 := by decide

theorem quoteChars_nil : quoteChars [] = ['\'', '\''] := by simp [quoteChars]

theorem quoteChars_safe {cs : List Char} (h : cs ≠ []) (ha : allSafe cs = true) :
    quoteChars cs = cs := by simp [quoteChars, h, ha]

theorem quoteChars_unsafe {cs : List Char} (h : cs ≠ []) (ha : allSafe cs = false) :
    quoteChars cs = ['\''] ++ escapeQuotes cs ++ ['\''] := by simp [quoteChars, h, ha]

theorem escapeQuotes_flatMap :
    ∀ cs : List Char, escapeQuotes cs = cs.flatMap (fun c => if c = '\'' then sqEscape else [c]) := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [escapeQuotes, List.flatMap, ih]

theorem escapeQuotes_length :
    ∀ cs : List Char, (escapeQuotes cs).length = cs.length + 4 * numQuotes cs := by
  intro cs
  induction cs with
  | nil => simp [escapeQuotes, numQuotes]
  | cons c cs ih =>
      by_cases h : c = '\''
      · subst h
        simp [escapeQuotes, numQuotes, sqEscape_length, List.length_append, ih]
        omega
      · simp [escapeQuotes, numQuotes, h, ih]
        omega

theorem isSafeChar_quote : isSafeChar '\'' = false := by decide
theorem isSafeChar_dquote : isSafeChar '"' = false := by decide
theorem isSafeChar_space : isSafeChar ' ' = false := by decide

theorem contains_true_imp_mem {α : Type u} [BEq α] [LawfulBEq α] {a : α} :
    ∀ l : List α, l.contains a = true → a ∈ l := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons b l ih =>
      intro h
      have e : (b :: l).contains a = ((a == b) || l.contains a) := rfl
      rw [e, Bool.or_eq_true] at h
      rcases h with h1 | h2
      · exact List.mem_cons.mpr (Or.inl (LawfulBEq.eq_of_beq h1))
      · exact List.mem_cons.mpr (Or.inr (ih h2))

theorem escape_inv (cs : List Char) :
    unquoteChars .sq (escapeQuotes cs ++ ['\'']) = cs ∧
    unquoteChars .outside (['\''] ++ escapeQuotes cs ++ ['\'']) = cs := by
  induction cs with
  | nil => constructor <;> simp [escapeQuotes, unquoteChars]
  | cons c cs ih =>
      have h1 : unquoteChars .sq (escapeQuotes (c :: cs) ++ ['\'']) = c :: cs := by
        simp only [escapeQuotes]
        by_cases h : c = '\''
        · subst h; simp [sqEscape, unquoteChars, ih.1]
        · simp [h, unquoteChars, ih.1]
      exact ⟨h1, by simp [unquoteChars, h1]⟩

theorem unquoteChars_id :
    ∀ cs : List Char, (∀ c ∈ cs, c ≠ '\'' ∧ c ≠ '"') → ∀ st : QState, unquoteChars st cs = cs := by
  intro cs
  induction cs with
  | nil => simp [unquoteChars]
  | cons c cs ih =>
      intro h st
      have hc := h c (List.Mem.head _)
      have ht : ∀ d ∈ cs, d ≠ '\'' ∧ d ≠ '"' := fun d hd => h d (List.Mem.tail _ hd)
      cases st with
      | outside => simp [unquoteChars, hc.1, hc.2, ih ht]
      | sq => simp [unquoteChars, hc.1, ih ht]
      | dq => simp [unquoteChars, hc.2, ih ht]

theorem quoteChars_roundtrip (cs : List Char) : unquoteChars .outside (quoteChars cs) = cs := by
  by_cases h : cs = []
  · subst h; simp [quoteChars, unquoteChars]
  · by_cases ha : allSafe cs = true
    · rw [quoteChars_safe h ha]
      refine unquoteChars_id _ ?_ .outside
      intro c hc
      have hsc : isSafeChar c = true := (allSafe_true _).mp ha c hc
      constructor
      · intro e; rw [e] at hsc; rw [isSafeChar_quote] at hsc; cases hsc
      · intro e; rw [e] at hsc; rw [isSafeChar_dquote] at hsc; cases hsc
    · rw [quoteChars_unsafe h (allSafe_eq_false ha)]
      exact (escape_inv cs).2

/-! ## Pre-condition -/

/-- `pre_quote`: the argument has to be a string, i.e. `isinstance(s, str)`. -/
def Pre (v : PyVal) : Prop := ∃ s : String, v = PyVal.str s

theorem Pre_str (s : String) : Pre (PyVal.str s) := ⟨s, rfl⟩

theorem not_Pre_other (t : String) : ¬ Pre (PyVal.other t) := by
  rintro ⟨s, h⟩
  cases h

/-! ## Properties of the implementation -/

/-- Python test 1: `quote('') == "''"`. -/
def empty_prop : Prop := quote "" = "''"

/-- Python test 2: a non-empty word made only of safe characters is returned unchanged. -/
def safe_prop : Prop := ∀ s : String, s ≠ "" → allSafe s.toList = true → quote s = s

/-- The general case: `"'" + s.replace("'", "'\"'\"'") + "'"`. -/
def unsafe_prop : Prop :=
  ∀ s : String, s ≠ "" → allSafe s.toList = false →
    quote s = "'" ++ String.mk (escapeQuotes s.toList) ++ "'"

/-- `escapeQuotes` replaces every single quote by `'"'"'` and copies every other character. -/
def escape_prop : Prop :=
  ∀ cs : List Char, escapeQuotes cs = cs.flatMap (fun c => if c = '\'' then sqEscape else [c])

/-- The escaped word denotes exactly `s` for a POSIX shell (round trip). -/
def roundtrip_prop : Prop := ∀ s : String, unquote (quote s) = s

/-- Two different words are never escaped to the same word. -/
def injective_prop : Prop := Function.Injective quote

/-- Escaping never produces the empty word. -/
def nonempty_prop : Prop := ∀ s : String, (quote s).toList ≠ []

/-- Exact length of the escaped word: two quotes plus four extra characters per quote. -/
def length_prop : Prop :=
  ∀ s : String, s ≠ "" → allSafe s.toList = false →
    (quote s).toList.length = s.toList.length + 2 + 4 * numQuotes s.toList

/-- Words that need escaping are wrapped in single quotes. -/
def wrapped_prop : Prop :=
  ∀ s : String, s ≠ "" → allSafe s.toList = false →
    (quote s).toList.head? = some '\'' ∧ (quote s).toList.reverse.head? = some '\''

/-- `isSafeChar` decides exactly Python's `safe_chars` set. -/
def charset_prop : Prop :=
  (∀ c ∈ safeCharList, isSafeChar c = true) ∧
  (∀ c : Char, isSafeChar c = true → c ∈ safeCharList) ∧
  isSafeChar ' ' = false ∧ isSafeChar '\'' = false ∧ isSafeChar '"' = false

/-- `benchmark_quote` returns the escaped word for a string argument. -/
def okvalue_prop : Prop := ∀ s : String, benchmarkQuote (PyVal.str s) = Except.ok (quote s)

/-- `benchmark_quote` raises `TypeError("expected string object")` for a non-string. -/
def typeerror_prop : Prop :=
  ∀ t : String, benchmarkQuote (PyVal.other t) = Except.error typeErrorMsg

theorem empty_thm : empty_prop := rfl

theorem safe_thm : safe_prop := by
  intro s hne ha
  have h : s.toList ≠ [] := fun h0 => hne ((toList_eq_nil s).mp h0)
  rw [quote, quoteChars_safe h ha, mk_toList]

theorem unsafe_thm : unsafe_prop := by
  intro s hne ha
  have h : s.toList ≠ [] := fun h0 => hne ((toList_eq_nil s).mp h0)
  rw [quote, quoteChars_unsafe h ha]
  rfl

theorem escape_thm : escape_prop := escapeQuotes_flatMap

theorem roundtrip_thm_raw (s : String) : unquote (quote s) = s := by
  show String.mk (unquoteChars .outside (quoteChars s.toList)) = s
  rw [quoteChars_roundtrip, mk_toList]

theorem roundtrip_thm : roundtrip_prop := roundtrip_thm_raw

theorem injective_thm : injective_prop := by
  intro s₁ s₂ h
  have h' := congrArg unquote h
  rw [roundtrip_thm_raw, roundtrip_thm_raw] at h'
  exact h'

theorem nonempty_thm : nonempty_prop := by
  intro s
  by_cases h : s.toList = []
  · have e : quote s = "''" := by
      show String.mk (quoteChars s.toList) = "''"
      rw [h, quoteChars_nil]
    rw [e]
    decide
  · by_cases ha : allSafe s.toList = true
    · have e : quote s = s := by
        show String.mk (quoteChars s.toList) = s
        rw [quoteChars_safe h ha, mk_toList]
      rw [e, toList_mk]
      exact h
    · have hf := allSafe_eq_false ha
      have e : (quote s).toList = ['\''] ++ escapeQuotes s.toList ++ ['\''] := by
        rw [quote, toList_mk, quoteChars_unsafe h hf]
      rw [e]
      simp

theorem length_thm : length_prop := by
  intro s hne ha
  have h : s.toList ≠ [] := fun h0 => hne ((toList_eq_nil s).mp h0)
  have e : (quote s).toList = ['\''] ++ escapeQuotes s.toList ++ ['\''] := by
    rw [quote, toList_mk, quoteChars_unsafe h ha]
  rw [e]
  simp [List.length_append, escapeQuotes_length]
  omega

theorem wrapped_thm : wrapped_prop := by
  intro s hne ha
  have h : s.toList ≠ [] := fun h0 => hne ((toList_eq_nil s).mp h0)
  have e : (quote s).toList = ['\''] ++ escapeQuotes s.toList ++ ['\''] := by
    rw [quote, toList_mk, quoteChars_unsafe h ha]
  rw [e]
  constructor
  · simp
  · simp [List.reverse_append]

theorem charset_thm : charset_prop := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro c hc
    have hc' : safeCharList.contains c = true := hc
    exact contains_true_imp_mem safeCharList hc'
  · exact isSafeChar_space
  · exact isSafeChar_quote
  · exact isSafeChar_dquote

theorem okvalue_thm : okvalue_prop := fun _ => rfl

theorem typeerror_thm : typeerror_prop := fun _ => rfl

/-! ## Post-condition -/

/-- The post-condition of `benchmark_quote`: for a string argument the result is
`Except.ok (quote s)`, and `quote` satisfies every property of the Python program. -/
def Post_prop (v : PyVal) (r : Except String String) : Prop :=
  (∃ s : String, v = PyVal.str s ∧ r = Except.ok (quote s)) ∧
  empty_prop ∧ safe_prop ∧ unsafe_prop ∧ escape_prop ∧ roundtrip_prop ∧ injective_prop ∧
    nonempty_prop ∧ length_prop ∧ wrapped_prop ∧ charset_prop ∧ okvalue_prop ∧ typeerror_prop

/-! ## Property-based tests -/

/-- A fixed list of interesting words. -/
def sampleWords : List String :=
  ["", "a", "abc", "ABC", "0123456789", "_@%+=:,./-", "hello_world", "a b c", "a'b", "'",
   "''", "'a'", " ", "\t", "!", "*", "$HOME", "a\"b", "é", "hello world", "x'y'z", "\\",
   "|", ";", "&", "a-b.c/d:e,f=g+h%i@j_k"]

/-- Words made only of safe characters. -/
def safeSamples : List String :=
  ["a", "abc", "z", "A", "Z", "0", "9", "_", "@", "%", "+", "=", ":", ",", ".", "/", "-",
   "hello_world", "abcXYZ019", "_@%+=:,./-"]

/-- Words that need escaping. -/
def unsafeSamples : List String :=
  [" ", "a b", "'", "a'b", "!", "*", "\"", "\t", "é", "$x", "a;b", "a|b", "a&b", "(x)"]

/-- All the words of length at most `n` over `alpha`. -/
def wordsUpTo : List Char → Nat → List String
  | _, 0 => [""]
  | alpha, n + 1 =>
      wordsUpTo alpha n ++
        (wordsUpTo alpha n).flatMap (fun s => alpha.map (fun c => String.mk (c :: s.toList)))

def tinyAlphabet : List Char := ['a', '\'', '"', ' ']

-- PBT (randomized): the POSIX round trip `unquote (quote s) = s`.
#eval Plausible.Testable.check (∀ s : String, unquote (quote s) = s)

-- PBT (randomized): escaping never produces the empty word.
#eval Plausible.Testable.check (∀ s : String, (quote s).toList ≠ [])

-- PBT (randomized): `quote` is injective (two words are equal exactly when their
-- escaped forms are), in a precondition-free Boolean form.
#eval Plausible.Testable.check (∀ s t : String, (s == t) == (quote s == quote t))

-- PBT (randomized): `quote` agrees with the Python expression written with `String.replace`.
#eval Plausible.Testable.check (∀ s : String, quote s == pyQuote s)

-- PBT (randomized): a non-empty word of safe characters is returned unchanged
-- (precondition-free Boolean form, so that no sample is discarded).
#eval Plausible.Testable.check
  (∀ s : String, (allSafe s.toList == false) || (s == "") || (quote s == s))

-- PBT (randomized): the exact length formula, in a precondition-free Boolean form
-- that covers all three branches of `quote`.
#eval Plausible.Testable.check
  (∀ s : String, (quote s).toList.length ==
    (if s == "" then 2
     else if allSafe s.toList then s.toList.length
     else s.toList.length + 2 + 4 * numQuotes s.toList))

/-- `benchmarkQuote v` succeeds with the value `expected`. -/
def benchOk (v : PyVal) (expected : String) : Bool :=
  match benchmarkQuote v with
  | Except.ok r => r == expected
  | Except.error _ => false

/-- `benchmarkQuote v` fails with the message `expected`. -/
def benchErr (v : PyVal) (expected : String) : Bool :=
  match benchmarkQuote v with
  | Except.ok _ => false
  | Except.error e => e == expected

-- PBT (randomized): the entry point returns the escaped word for a string argument.
#eval Plausible.Testable.check (∀ s : String, benchOk (PyVal.str s) (quote s))

-- PBT (randomized): the entry point raises `TypeError` for a non-string argument.
#eval Plausible.Testable.check (∀ t : String, benchErr (PyVal.other t) typeErrorMsg)

-- PBT (bounded, exhaustive): all 125 words of length ≤ 3 over `a`, `'`, `"`, ` `.
example : (wordsUpTo tinyAlphabet 3).length = 125 := by native_decide
example : (wordsUpTo tinyAlphabet 3).all (fun s => quote s == pyQuote s) = true := by native_decide
example : (wordsUpTo tinyAlphabet 3).all (fun s => unquote (quote s) == s) = true := by native_decide
example : (wordsUpTo tinyAlphabet 3).all (fun s => (quote s).toList != []) = true := by native_decide
example : (wordsUpTo tinyAlphabet 3).all
    (fun s => (quote s).toList.length ==
      (if s.toList == [] then 2
       else if allSafe s.toList then s.toList.length
       else s.toList.length + 2 + 4 * numQuotes s.toList)) = true := by native_decide
example : (wordsUpTo tinyAlphabet 3).all
    (fun s => quote s == (if s.toList == [] then "''"
      else if allSafe s.toList then s
      else "'" ++ String.mk (escapeQuotes s.toList) ++ "'")) = true := by native_decide
example : (wordsUpTo tinyAlphabet 3).all (fun s => benchOk (PyVal.str s) (quote s)) = true :=
  by native_decide

-- PBT (bounded): the sample words.
example : sampleWords.all (fun s => quote s == pyQuote s) = true := by native_decide
example : sampleWords.all (fun s => unquote (quote s) == s) = true := by native_decide
example : sampleWords.all (fun s => (quote s).toList != []) = true := by native_decide
example : sampleWords.all (fun s => benchErr (PyVal.other s) typeErrorMsg) = true :=
  by native_decide
example : safeSamples.all (fun s => quote s == s && allSafe s.toList) = true := by native_decide
example : unsafeSamples.all
    (fun s => quote s == "'" ++ s.replace "'" "'\"'\"'" ++ "'" && !allSafe s.toList) = true :=
  by native_decide

-- PBT (bounded): `quote` is injective on the enumerated words (distinct inputs give
-- distinct escaped words).
example : ((wordsUpTo tinyAlphabet 3).map quote).dedup.length ==
    (wordsUpTo tinyAlphabet 3).dedup.length := by native_decide
example : sampleWords.all (fun s => sampleWords.all (fun t =>
    (quote s == quote t) == (s == t))) = true := by native_decide

/-! ## Correctness: `Pre -> Post` -/

theorem correctness_thm (v : PyVal) (h : Pre v) : Post_prop v (benchmarkQuote v) := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨⟨s, rfl, rfl⟩, empty_thm, safe_thm, unsafe_thm, escape_thm, roundtrip_thm,
    injective_thm, nonempty_thm, length_thm, wrapped_thm, charset_thm, okvalue_thm,
    typeerror_thm⟩

/-! ## Imperative implementation (`Id.run do` with mutable state) -/

/-- The mutable state: the "everything read so far is safe" flag and the output buffer. -/
structure ImpState where
  safe : Bool
  buf : Array Char

/-- The scanning loop: the flag stays `true` as long as every character read so far
is a safe character. -/
def scanLoop : List Char → Bool → Bool
  | [], flag => flag
  | c :: cs, flag => scanLoop cs (flag && isSafeChar c)

/-- The escaping loop: appends the shell-escaped form of every character to the buffer. -/
def escLoop : List Char → Array Char → Array Char
  | [], buf => buf
  | c :: cs, buf =>
      escLoop cs
        (if c = '\'' then ((((buf.push '\'').push '"').push '\'').push '"').push '\''
         else buf.push c)

/-- The imperative `quote`: one mutable pass decides whether escaping is needed, a
second mutable pass fills the output buffer. -/
def quoteImp (s : String) : String := Id.run do
  let cs := s.toList
  let mut st : ImpState := { safe := true, buf := #[] }
  st := { st with safe := scanLoop cs st.safe }
  if cs = [] then
    st := { st with buf := #['\'', '\''] }
  else if st.safe then
    st := { st with buf := cs.toArray }
  else
    st := { st with buf := (escLoop cs #['\'']).push '\'' }
  return String.mk st.buf.toList

theorem scanLoop_spec :
    ∀ cs : List Char, ∀ flag : Bool, scanLoop cs flag = (flag && allSafe cs) := by
  intro cs
  induction cs with
  | nil => intro f; cases f <;> rfl
  | cons c cs ih =>
      intro f
      have e1 : scanLoop (c :: cs) f = scanLoop cs (f && isSafeChar c) := rfl
      have e2 : allSafe (c :: cs) = (isSafeChar c && allSafe cs) := rfl
      rw [e1, e2, ih (f && isSafeChar c), Bool.and_assoc]

theorem escLoop_spec : ∀ cs : List Char, ∀ buf : Array Char,
    (escLoop cs buf).toList = buf.toList ++ escapeQuotes cs := by
  intro cs
  induction cs with
  | nil => intro buf; simp [escLoop, escapeQuotes]
  | cons c cs ih =>
      intro buf
      have e1 : escLoop (c :: cs) buf =
          escLoop cs
            (if c = '\'' then ((((buf.push '\'').push '"').push '\'').push '"').push '\''
             else buf.push c) := rfl
      have e2 : escapeQuotes (c :: cs) =
          (if c = '\'' then sqEscape else [c]) ++ escapeQuotes cs := rfl
      rw [e1, e2]
      by_cases h : c = '\''
      · subst h
        simp [sqEscape, Array.toList_push, ih, List.append_assoc]
      · simp [h, Array.toList_push, ih, List.append_assoc]

theorem quoteImp_eq_quote (cs : List Char) : quoteImp (String.mk cs) = quote (String.mk cs) := by
  by_cases h : cs = []
  · simp [quoteImp, quote, quoteChars, h, Id.run_pure]
  · have hsl : scanLoop cs true = allSafe cs := by rw [scanLoop_spec]; simp
    by_cases ha : allSafe cs = true
    · simp [quoteImp, quote, quoteChars, h, ha, hsl, Id.run_pure]
    · have hf := allSafe_eq_false ha
      simp [quoteImp, quote, quoteChars, h, hf, hsl, escLoop_spec,
        Array.toList_push, Id.run_pure]

/-! ## Imperative tests -/

example : quoteImp "" = "''" := by native_decide
example : quoteImp "abc" = "abc" := by native_decide
example : quoteImp "a b c" = "'a b c'" := by native_decide
example : quoteImp "a'b" = "'a'\"'\"'b'" := by native_decide
example : quoteImp "'" = "''\"'\"''" := by native_decide
example : check quoteImp = true := by native_decide
example : quoteImp "a'b" = pyQuote "a'b" := by native_decide

#eval quoteImp ""
#eval quoteImp "abc"
#eval quoteImp "a b c"
#eval quoteImp "a'b"
#eval check quoteImp

-- PBT (bounded): the imperative and the functional implementation agree.
example : sampleWords.all (fun s => quoteImp s == quote s) = true := by native_decide
example : safeSamples.all (fun s => quoteImp s == s) = true := by native_decide
example : unsafeSamples.all (fun s => quoteImp s == pyQuote s) = true := by native_decide
example : (wordsUpTo tinyAlphabet 3).all (fun s => quoteImp s == quote s) = true := by native_decide
example : (wordsUpTo tinyAlphabet 3).all (fun s => unquote (quoteImp s) == s) = true :=
  by native_decide

-- PBT (randomized): the imperative implementation agrees with the functional one.
#eval Plausible.Testable.check (∀ s : String, quoteImp s == quote s)
-- PBT (randomized): the imperative implementation satisfies the round trip.
#eval Plausible.Testable.check (∀ s : String, unquote (quoteImp s) = s)
-- PBT (randomized): the imperative implementation agrees with the Python expression.
#eval Plausible.Testable.check (∀ s : String, quoteImp s == pyQuote s)

/-! ## Equivalence: functional = imperative -/

theorem equivalence_thm : ∀ s : String, quoteImp s = quote s := by
  intro s
  rw [← mk_toList s]
  exact quoteImp_eq_quote s.toList

/-! ## Proof audit: every theorem below is checked by the kernel using only the
standard axioms `propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`, no
`Lean.ofReduceBool`, i.e. no `native_decide`, and no extra axioms). -/

#print axioms empty_thm
#print axioms safe_thm
#print axioms unsafe_thm
#print axioms escape_thm
#print axioms roundtrip_thm
#print axioms roundtrip_thm_raw
#print axioms injective_thm
#print axioms nonempty_thm
#print axioms length_thm
#print axioms wrapped_thm
#print axioms charset_thm
#print axioms okvalue_thm
#print axioms typeerror_thm
#print axioms Pre_str
#print axioms not_Pre_other
#print axioms correctness_thm
#print axioms scanLoop_spec
#print axioms escLoop_spec
#print axioms quoteImp_eq_quote
#print axioms equivalence_thm
#print axioms quoteChars_roundtrip
#print axioms escape_inv
#print axioms unquoteChars_id
#print axioms escapeQuotes_length
#print axioms escapeQuotes_flatMap
#print axioms allSafe_true
#print axioms contains_true_imp_mem

end «21_shlex_quote»
