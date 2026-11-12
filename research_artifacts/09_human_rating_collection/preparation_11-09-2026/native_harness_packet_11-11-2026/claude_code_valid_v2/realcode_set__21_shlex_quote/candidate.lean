import Mathlib

/-!
# Shell-escaping a string (`shlex.quote`)

Lean 4 formalization of the Python program `shlex.quote` (sourced from Python's
standard `shlex` library):

```python
def quote(s):
    if not s:
        return "''"
    safe_chars = set(ascii_letters + digits + '_@%+=:,.' + '/' + '-')
    if all(c in safe_chars for c in s):
        return s
    return "'" + s.replace("'", "'\"'\"'") + "'"
```

The Python pre-condition `pre_quote` only demands that the input is a `str`; in Lean
this is guaranteed by the type `String`, so `Pre` is trivially true.

`s.replace("'", "'\"'\"'")` replaces every single quote by the five-character sequence
`'"'"'` and leaves every other character untouched.  Because the pattern is a single
character, this is exactly a character-wise expansion, which is how it is modelled here
(`escapeChar` / `escapeQuotes`).  A property-based test below confirms the agreement
with Lean's own `String.replace`.

Besides the clause-by-clause specification of the Python code, the file states and
proves the *purpose* of `shlex.quote`: a minimal model of how a POSIX shell reads one
word (`shellRead`) recovers the original string from the quoted output
(`quote_shell_prop`), which in turn yields injectivity of `quote`.
-/

namespace «21_shlex_quote»

/-! ## Implementation (functional) -/

/-- Safe characters for POSIX shells (the `safe_chars` set of the Python source). -/
def safeChars : List Char :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_@%+=:,./-".toList

/-- `c in safe_chars` -/
def isSafeChar (c : Char) : Bool := safeChars.contains c

/-- Character-wise version of `s.replace("'", "'\"'\"'")`: a single quote becomes the
five characters `'"'"'`; every other character is kept. -/
def escapeChar (c : Char) : List Char :=
  if c = '\'' then ['\'', '"', '\'', '"', '\''] else [c]

/-- `s.replace("'", "'\"'\"'")` -/
def escapeQuotes (s : String) : String := ⟨s.toList.flatMap escapeChar⟩

/-- Return a shell-escaped version of the string `s` (Python `shlex.quote`). -/
def quote (s : String) : String :=
  if s.isEmpty then "''"
  else if s.toList.all isSafeChar then s
  else "'" ++ escapeQuotes s ++ "'"

/-! ## Unit tests (the `check` function of the Python source) -/

-- 1. Test empty string
example : quote "" = "''" := by native_decide
-- 2. Test safe string
example : quote "abc" = "abc" := by native_decide
-- 3. Test string with spaces
example : quote "a b c" = "'a b c'" := by native_decide
-- 4. Test string with quotes
example : quote "a'b" = "'a'\"'\"'b'" := by native_decide
-- additional ground tests
example : quote "'" = "''\"'\"''" := by native_decide
example : quote "_@%+=:,./-" = "_@%+=:,./-" := by native_decide
example : quote "$HOME" = "'$HOME'" := by native_decide
example : escapeQuotes "a'b'c" = "a'\"'\"'b'\"'\"'c" := by native_decide
example : escapeQuotes "a'b'c" = "a'b'c".replace "'" "'\"'\"'" := by native_decide

#eval quote ""          -- "''"
#eval quote "abc"       -- "abc"
#eval quote "a b c"     -- "'a b c'"
#eval quote "a'b"       -- "'a'\"'\"'b'"

/-! ## A minimal model of how a POSIX shell reads one word

`shellRead mode cs` reads the characters `cs` starting in quoting state `mode` and
returns the word the shell would see, or `none` when the model does not vouch for the
input (unterminated quotes, or a character outside quotes that is not in the safe set,
or a character inside double quotes that would trigger an expansion). -/

/-- Quoting state of the shell reader. -/
inductive ShellMode where
  | plain | single | double
  deriving DecidableEq, Repr

/-- Read one shell word. -/
def shellRead : ShellMode → List Char → Option (List Char)
  | .plain, [] => some []
  | .plain, c :: cs =>
      if c = '\'' then shellRead .single cs
      else if c = '"' then shellRead .double cs
      else if isSafeChar c then (shellRead .plain cs).map (c :: ·)
      else none
  | .single, [] => none
  | .single, c :: cs =>
      if c = '\'' then shellRead .plain cs
      else (shellRead .single cs).map (c :: ·)
  | .double, [] => none
  | .double, c :: cs =>
      if c = '"' then shellRead .plain cs
      else if c = '$' ∨ c = '`' ∨ c = '\\' then none
      else (shellRead .double cs).map (c :: ·)

/-- The word a POSIX shell reads from the token `s` (in our minimal model). -/
def shellUnquote (s : String) : Option String := (shellRead .plain s.toList).map String.mk

example : shellUnquote "'a'\"'\"'b'" = some "a'b" := by native_decide
example : shellUnquote "'a b c'" = some "a b c" := by native_decide
example : shellUnquote "''" = some "" := by native_decide
example : shellUnquote "abc" = some "abc" := by native_decide
example : shellUnquote "a b" = none := by native_decide
example : shellUnquote "'abc" = none := by native_decide

/-! ## Basic lemmas -/

theorem data_empty : ("" : String).data = [] := rfl
theorem data_sq : ("'" : String).data = ['\''] := rfl
theorem data_sqsq : ("''" : String).data = ['\'', '\''] := rfl
theorem data_esc : ("'\"'\"'" : String).data = ['\'', '"', '\'', '"', '\''] := rfl

theorem isEmpty_iff (s : String) : s.isEmpty = true ↔ s.data = [] := by
  cases s with
  | mk l =>
    cases l with
    | nil => simp [String.isEmpty]
    | cons c cs =>
      simp only [String.isEmpty, String.endPos, String.utf8ByteSize, String.utf8ByteSize.go]
      constructor
      · intro h
        exfalso
        have := Char.utf8Size_pos c
        simp [String.Pos.ext_iff] at h
        omega
      · intro h; cases h

theorem isEmpty_eq_false_iff (s : String) : s.isEmpty = false ↔ s.data ≠ [] := by
  rw [← Bool.not_eq_true, isEmpty_iff]

theorem not_isSafeChar_sq : isSafeChar '\'' = false := by decide
theorem not_isSafeChar_dq : isSafeChar '"' = false := by decide

theorem ne_sq_of_isSafeChar {c : Char} (h : isSafeChar c = true) : c ≠ '\'' := by
  rintro rfl; simp [not_isSafeChar_sq] at h
theorem ne_dq_of_isSafeChar {c : Char} (h : isSafeChar c = true) : c ≠ '"' := by
  rintro rfl; simp [not_isSafeChar_dq] at h

theorem escapeChar_ne_nil (c : Char) : escapeChar c ≠ [] := by
  unfold escapeChar; split <;> simp

theorem one_le_length_escapeChar (c : Char) : 1 ≤ (escapeChar c).length := by
  unfold escapeChar; split <;> simp

theorem length_le_length_flatMap_escapeChar (cs : List Char) :
    cs.length ≤ (cs.flatMap escapeChar).length := by
  induction cs with
  | nil => simp
  | cons c t ih =>
    have := one_le_length_escapeChar c
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem flatMap_escapeChar_eq_nil_iff (cs : List Char) :
    cs.flatMap escapeChar = [] ↔ cs = [] := by
  constructor
  · intro h
    rw [List.flatMap_eq_nil_iff] at h
    cases cs with
    | nil => rfl
    | cons c t => exact absurd (h c (List.mem_cons_self ..)) (escapeChar_ne_nil c)
  · rintro rfl; rfl

/-- `quote` on the level of character lists. -/
def quoteChars (cs : List Char) : List Char :=
  if cs = [] then ['\'', '\'']
  else if cs.all isSafeChar then cs
  else '\'' :: (cs.flatMap escapeChar ++ ['\''])

theorem data_quote (s : String) : (quote s).data = quoteChars s.data := by
  unfold quote quoteChars
  by_cases h0 : s.data = []
  · have : s.isEmpty = true := (isEmpty_iff s).2 h0
    simp [this, h0, data_sqsq]
  · have : s.isEmpty = false := (isEmpty_eq_false_iff s).2 h0
    simp only [this, h0, Bool.false_eq_true, ↓reduceIte, String.toList]
    split
    · rfl
    · simp [String.data_append, escapeQuotes, String.toList]

/-- Case split for `quote` mirroring the three branches of the Python function. -/
theorem quote_of_empty (s : String) (h : s = "") : quote s = "''" := by
  subst h; rfl

theorem quote_of_safe (s : String) (h0 : s ≠ "") (h1 : s.toList.all isSafeChar = true) :
    quote s = s := by
  have h0' : s.isEmpty = false := by
    rw [isEmpty_eq_false_iff]
    intro h; exact h0 (String.ext (h.trans data_empty.symm))
  unfold quote
  rw [if_neg (by simp [h0']), if_pos h1]

theorem quote_of_unsafe (s : String) (h1 : s.toList.all isSafeChar = false) :
    quote s = "'" ++ escapeQuotes s ++ "'" := by
  have h0' : s.isEmpty = false := by
    rw [isEmpty_eq_false_iff]
    intro h; rw [String.toList, h] at h1; simp at h1
  unfold quote
  rw [if_neg (by simp [h0']), if_neg (by rw [h1]; exact Bool.false_ne_true)]

theorem quote_cases (s : String) :
    (s = "" ∧ quote s = "''") ∨
    (s ≠ "" ∧ (∀ c ∈ s.toList, isSafeChar c = true) ∧ quote s = s) ∨
    ((∃ c ∈ s.toList, isSafeChar c = false) ∧ quote s = "'" ++ escapeQuotes s ++ "'") := by
  by_cases h0 : s = ""
  · exact Or.inl ⟨h0, quote_of_empty s h0⟩
  · by_cases h1 : s.toList.all isSafeChar = true
    · exact Or.inr (Or.inl ⟨h0, List.all_eq_true.1 h1, quote_of_safe s h0 h1⟩)
    · have h1' : s.toList.all isSafeChar = false := by simpa using h1
      refine Or.inr (Or.inr ⟨?_, quote_of_unsafe s h1'⟩)
      obtain ⟨c, hc, hcs⟩ := List.all_eq_false.1 h1'
      exact ⟨c, hc, by simpa using hcs⟩

/-! ## Shell-reader lemmas -/

theorem shellRead_plain_of_safe (cs : List Char) (h : ∀ c ∈ cs, isSafeChar c = true) :
    shellRead .plain cs = some cs := by
  induction cs with
  | nil => rfl
  | cons c t ih =>
    have hc : isSafeChar c = true := h c (List.mem_cons_self ..)
    have ih' := ih (fun d hd => h d (List.mem_cons_of_mem c hd))
    simp [shellRead, ne_sq_of_isSafeChar hc, ne_dq_of_isSafeChar hc, hc, ih']

theorem shellRead_single_escape (cs rest : List Char) :
    shellRead .single (cs.flatMap escapeChar ++ '\'' :: rest) =
      (shellRead .plain rest).map (cs ++ ·) := by
  induction cs with
  | nil => simp [shellRead]
  | cons c t ih =>
    by_cases hc : c = '\''
    · subst hc
      simp [escapeChar, shellRead, ih, Option.map_map, Function.comp_def]
    · simp [escapeChar, hc, shellRead, ih, Option.map_map, Function.comp_def]

theorem shellRead_quoteChars (cs : List Char) : shellRead .plain (quoteChars cs) = some cs := by
  unfold quoteChars
  split
  · subst cs; rfl
  · split
    · exact shellRead_plain_of_safe cs (List.all_eq_true.1 (by assumption))
    · simp only [shellRead, ↓reduceIte]
      rw [shellRead_single_escape cs []]
      simp [shellRead]

/-! ## Pre-condition -/

/-- The Python pre-condition `pre_quote` only asks the input to be a `str`;
the Lean type `String` guarantees that, so the pre-condition is trivial. -/
def Pre (_s : String) : Prop := True

/-! ## Properties -/

/-- Empty input is quoted as two single quotes (`if not s: return "''"`). -/
def quote_empty_prop (s : String) : Prop := s = "" → quote s = "''"

theorem quote_empty_thm (s : String) : quote_empty_prop s := by
  rintro rfl; rfl

/-- A non-empty string consisting only of safe characters is returned unchanged. -/
def quote_safe_prop (s : String) : Prop :=
  s ≠ "" → (∀ c ∈ s.toList, isSafeChar c = true) → quote s = s

theorem quote_safe_thm (s : String) : quote_safe_prop s := by
  intro hne hsafe
  rcases quote_cases s with ⟨h, _⟩ | ⟨_, _, h⟩ | ⟨⟨c, hc, hcs⟩, _⟩
  · exact absurd h hne
  · exact h
  · have := hsafe c hc; simp_all

/-- A string containing an unsafe character is wrapped in single quotes after every
single quote has been replaced by `'"'"'`. -/
def quote_unsafe_prop (s : String) : Prop :=
  (∃ c ∈ s.toList, isSafeChar c = false) → quote s = "'" ++ escapeQuotes s ++ "'"

theorem quote_unsafe_thm (s : String) : quote_unsafe_prop s := by
  rintro ⟨c, hc, hcs⟩
  rcases quote_cases s with ⟨h, _⟩ | ⟨_, hsafe, _⟩ | ⟨_, h⟩
  · subst h; simp [String.toList] at hc
  · have := hsafe c hc; simp_all
  · exact h

/-- Whenever quoting is needed, the result starts and ends with a single quote. -/
def quote_wrapped_prop (s : String) : Prop :=
  (∃ c ∈ s.toList, isSafeChar c = false) → ∃ m : String, quote s = "'" ++ m ++ "'"

theorem quote_wrapped_thm (s : String) : quote_wrapped_prop s := by
  intro h
  exact ⟨escapeQuotes s, quote_unsafe_thm s h⟩

/-- The result is never the empty string. -/
def quote_ne_empty_prop (s : String) : Prop := quote s ≠ ""

theorem quote_ne_empty_thm (s : String) : quote_ne_empty_prop s := by
  intro h
  have h' := congrArg String.data h
  rw [data_quote, data_empty] at h'
  unfold quoteChars at h'
  split_ifs at h' with h1 h2
  simp_all

/-- Quoting never shortens a string. -/
def quote_length_prop (s : String) : Prop := s.length ≤ (quote s).length

theorem quote_length_thm (s : String) : quote_length_prop s := by
  unfold quote_length_prop
  rw [← String.length_data, ← String.length_data, data_quote]
  unfold quoteChars
  split_ifs with h0 h1
  · rw [h0]; simp
  · exact le_refl _
  · have := length_le_length_flatMap_escapeChar s.data
    simp only [List.length_cons, List.length_append]
    omega

/-- `quote` leaves a string unchanged exactly when it is non-empty and entirely safe. -/
def quote_fixed_iff_prop (s : String) : Prop :=
  quote s = s ↔ (s ≠ "" ∧ ∀ c ∈ s.toList, isSafeChar c = true)

theorem quote_fixed_iff_thm (s : String) : quote_fixed_iff_prop s := by
  unfold quote_fixed_iff_prop
  constructor
  · intro h
    rcases quote_cases s with ⟨h0, h0'⟩ | ⟨hne, hsafe, _⟩ | ⟨⟨c, hc, hcs⟩, h2⟩
    · exfalso
      subst h0
      rw [h0'] at h
      exact absurd (congrArg String.data h) (by simp)
    · exact ⟨hne, hsafe⟩
    · exfalso
      have hlen := congrArg String.length h
      rw [h2] at hlen
      have hle := length_le_length_flatMap_escapeChar s.data
      simp only [String.length_append, escapeQuotes, String.length_mk, String.toList] at hlen
      have : ("'" : String).length = 1 := rfl
      rw [this, ← String.length_data s] at hlen
      omega
  · rintro ⟨hne, hsafe⟩
    exact quote_safe_thm s hne hsafe

/-- The purpose of `shlex.quote`: a POSIX shell reading the quoted token recovers
exactly the original string. -/
def quote_shell_prop (s : String) : Prop := shellUnquote (quote s) = some s

theorem quote_shell_thm (s : String) : quote_shell_prop s := by
  unfold quote_shell_prop shellUnquote
  rw [String.toList, data_quote, shellRead_quoteChars]
  rfl

/-- Quoting is injective: distinct strings have distinct quoted forms. -/
def quote_injective_prop (s t : String) : Prop := quote s = quote t → s = t

theorem quote_injective_thm (s t : String) : quote_injective_prop s t := by
  intro h
  have hs := quote_shell_thm s
  have ht := quote_shell_thm t
  unfold quote_shell_prop at hs ht
  rw [h, ht] at hs
  exact (Option.some.inj hs).symm

/-! ## Post-condition -/

/-- Post-condition: conjunction of all properties of `quote s`. -/
def Post_prop (s : String) : Prop :=
  quote_empty_prop s ∧ quote_safe_prop s ∧ quote_unsafe_prop s ∧ quote_wrapped_prop s ∧
  quote_ne_empty_prop s ∧ quote_length_prop s ∧ quote_fixed_iff_prop s ∧
  quote_shell_prop s ∧ (∀ t : String, quote_injective_prop s t)

/-! ## Property-based tests -/

/-- Executable form of `quote_empty_prop`. -/
def checkEmpty (s : String) : Bool := s != "" || quote s == "''"
/-- Executable form of `quote_safe_prop`. -/
def checkSafe (s : String) : Bool := s == "" || !(s.toList.all isSafeChar) || quote s == s
/-- Executable form of `quote_unsafe_prop`. -/
def checkUnsafe (s : String) : Bool :=
  !(s.toList.any (fun c => !isSafeChar c)) || quote s == "'" ++ escapeQuotes s ++ "'"
/-- Executable form of `quote_wrapped_prop` (`m` is the middle part of the result). -/
def checkWrapped (s : String) : Bool :=
  !(s.toList.any (fun c => !isSafeChar c)) ||
    (quote s == "'" ++ ((quote s).drop 1).dropRight 1 ++ "'")
/-- Executable form of `quote_ne_empty_prop`. -/
def checkNeEmpty (s : String) : Bool := quote s != ""
/-- Executable form of `quote_length_prop`. -/
def checkLength (s : String) : Bool := decide (s.length ≤ (quote s).length)
/-- Executable form of `quote_fixed_iff_prop`. -/
def checkFixedIff (s : String) : Bool :=
  (quote s == s) == (s != "" && s.toList.all isSafeChar)
/-- Executable form of `quote_shell_prop`. -/
def checkShell (s : String) : Bool := shellUnquote (quote s) == some s
/-- Executable form of `quote_injective_prop` (precondition-free formulation). -/
def checkInjective (s t : String) : Bool := (quote s == quote t) == (s == t)
/-- Executable form of `Post_prop s` (the injectivity clause is tested against `t`). -/
def checkPost (s t : String) : Bool :=
  checkEmpty s && checkSafe s && checkUnsafe s && checkWrapped s && checkNeEmpty s &&
  checkLength s && checkFixedIff s && checkShell s && checkInjective s t

-- Randomized PBTs (Plausible)
#eval Plausible.Testable.check (∀ s : String, s = "" → quote s = "''")
#eval Plausible.Testable.check
  (∀ s : String, s ≠ "" → s.toList.all isSafeChar = true → quote s = s)
#eval Plausible.Testable.check
  (∀ s : String, s.toList.any (fun c => !isSafeChar c) = true →
    quote s = "'" ++ escapeQuotes s ++ "'")
#eval Plausible.Testable.check (∀ s : String, checkWrapped s = true)
#eval Plausible.Testable.check (∀ s : String, quote s ≠ "")
#eval Plausible.Testable.check (∀ s : String, s.length ≤ (quote s).length)
#eval Plausible.Testable.check
  (∀ s : String, (quote s = s) ↔ (s ≠ "" ∧ s.toList.all isSafeChar = true))
#eval Plausible.Testable.check (∀ s : String, shellUnquote (quote s) = some s)
#eval Plausible.Testable.check (∀ s t : String, (quote s == quote t) = (s == t))
#eval Plausible.Testable.check (∀ s t : String, checkPost s t = true)
-- Precondition-free Boolean forms of the conditional properties (the implications above
-- discard most random samples, so these make sure the clauses are exercised at random).
#eval Plausible.Testable.check (∀ s : String, checkEmpty s = true)
#eval Plausible.Testable.check (∀ s : String, checkSafe s = true)
#eval Plausible.Testable.check (∀ s : String, checkUnsafe s = true)
-- Supporting evidence for the modelling of `s.replace("'", "'\"'\"'")`
#eval Plausible.Testable.check (∀ s : String, escapeQuotes s = s.replace "'" "'\"'\"'")

-- Bounded (exhaustive) PBTs over an alphabet mixing safe and unsafe characters,
-- in particular many single and double quotes.

/-- All words of exactly length `n` over `alpha`. -/
def wordsOfLength (alpha : List Char) : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => (wordsOfLength alpha n).flatMap (fun w => alpha.map (· :: w))

/-- All strings of length `≤ n` over `alpha`. -/
def wordsUpTo (alpha : List Char) (n : Nat) : List String :=
  ((List.range (n + 1)).flatMap (wordsOfLength alpha)).map String.mk

/-- Test alphabet: safe letters/digits/punctuation plus quotes, space, `$`, backslash. -/
def pbtAlphabet : List Char := ['a', 'Z', '0', '-', '\'', '"', ' ', '$', '\\']

example : (wordsUpTo pbtAlphabet 4).length = 7381 := by native_decide
example : (wordsUpTo pbtAlphabet 4).all checkEmpty = true := by native_decide
example : (wordsUpTo pbtAlphabet 4).all checkSafe = true := by native_decide
example : (wordsUpTo pbtAlphabet 4).all checkUnsafe = true := by native_decide
example : (wordsUpTo pbtAlphabet 4).all checkWrapped = true := by native_decide
example : (wordsUpTo pbtAlphabet 4).all checkNeEmpty = true := by native_decide
example : (wordsUpTo pbtAlphabet 4).all checkLength = true := by native_decide
example : (wordsUpTo pbtAlphabet 4).all checkFixedIff = true := by native_decide
example : (wordsUpTo pbtAlphabet 4).all checkShell = true := by native_decide
example : (wordsUpTo pbtAlphabet 3).all
    (fun s => (wordsUpTo pbtAlphabet 3).all (fun t => checkInjective s t)) = true := by
  native_decide
example : (wordsUpTo pbtAlphabet 3).all
    (fun s => (wordsUpTo pbtAlphabet 3).all (fun t => checkPost s t)) = true := by
  native_decide
example : (wordsUpTo pbtAlphabet 4).all
    (fun s => escapeQuotes s == s.replace "'" "'\"'\"'") = true := by native_decide

/-! ## Correctness theorem -/

theorem quote_correct (s : String) (_h : Pre s) : Post_prop s :=
  ⟨quote_empty_thm s, quote_safe_thm s, quote_unsafe_thm s, quote_wrapped_thm s,
   quote_ne_empty_thm s, quote_length_thm s, quote_fixed_iff_thm s, quote_shell_thm s,
   fun t => quote_injective_thm s t⟩

/-! ## Imperative implementation -/

/-- Imperative version of `quote`: a loop decides whether every character is safe,
and a second loop builds the escaped string character by character. -/
def quoteImp (s : String) : String := Id.run do
  if s.isEmpty then
    return "''"
  -- Check if all chars are safe
  let mut allSafe := true
  for c in s.toList do
    if !isSafeChar c then
      allSafe := false
  if allSafe then
    return s
  -- Use single quotes, and replace single quotes with '"'"'
  let mut out := "'"
  for c in s.toList do
    if c == '\'' then
      out := out ++ "'\"'\"'"
    else
      out := out.push c
  out := out.push '\''
  return out

/-! ## Imperative tests -/

example : quoteImp "" = "''" := by native_decide
example : quoteImp "abc" = "abc" := by native_decide
example : quoteImp "a b c" = "'a b c'" := by native_decide
example : quoteImp "a'b" = "'a'\"'\"'b'" := by native_decide
example : quoteImp "'" = "''\"'\"''" := by native_decide
example : quoteImp "$HOME" = "'$HOME'" := by native_decide

#eval quoteImp "a'b"    -- "'a'\"'\"'b'"

#eval Plausible.Testable.check (∀ s : String, quoteImp s = quote s)
example : (wordsUpTo pbtAlphabet 4).all (fun s => quoteImp s == quote s) = true := by
  native_decide

/-! ## Equivalence: functional = imperative -/

/-- A `for` loop over a list in the `Id` monad whose body always `yield`s is a fold. -/
theorem forIn_id_eq_foldl {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : α → β → β) (hf : ∀ a b, f a b = pure (ForInStep.yield (g a b))) :
    forIn l init f = (pure (l.foldl (fun b a => g a b) init) : Id β) := by
  induction l generalizing init with
  | nil => rfl
  | cons a t ih =>
    rw [List.forIn_cons, hf a init]
    simp only [List.foldl_cons]
    exact ih (g a init)

theorem foldl_allSafe (l : List Char) (b : Bool) :
    l.foldl (fun r c => if (!isSafeChar c) = true then false else r) b = (b && l.all isSafeChar) := by
  induction l generalizing b with
  | nil => simp
  | cons c t ih =>
    rw [List.foldl_cons, ih, List.all_cons]
    cases isSafeChar c <;> cases b <;> simp

theorem foldl_escape (l : List Char) (acc : String) :
    l.foldl (fun r c => if (c == '\'') = true then r ++ "'\"'\"'" else r.push c) acc =
      acc ++ ⟨l.flatMap escapeChar⟩ := by
  induction l generalizing acc with
  | nil => apply String.ext; simp
  | cons c t ih =>
    rw [List.foldl_cons, ih]
    apply String.ext
    by_cases hc : c = '\''
    · subst hc
      simp [String.data_append, escapeChar]
    · simp [String.data_append, String.data_push, escapeChar, hc]

theorem quoteImp_eq_quote (s : String) : quoteImp s = quote s := by
  unfold quoteImp
  simp only [Id.run]
  rw [forIn_id_eq_foldl s.toList true _ (fun c r => if (!isSafeChar c) = true then false else r)
        (by intros; beta_reduce; split <;> rfl)]
  rw [forIn_id_eq_foldl s.toList "'" _
        (fun c r => if (c == '\'') = true then r ++ "'\"'\"'" else r.push c)
        (by intros; beta_reduce; split <;> rfl)]
  simp only [pure_bind]
  rw [foldl_allSafe, foldl_escape, Bool.true_and]
  unfold quote
  split
  · rfl
  · split
    · rfl
    · apply String.ext
      show (String.push _ _).data = _
      simp [String.data_append, String.data_push, escapeQuotes, String.toList, data_sq]

end «21_shlex_quote»
