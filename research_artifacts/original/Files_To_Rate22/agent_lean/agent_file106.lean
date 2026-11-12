import Mathlib

/-!
# `shlex.quote`: shell-escaping a string

Lean 4 formalization of Python's `shlex.quote` (benchmark file `21_shlex_quote`).

```python
def quote(s):
    if not s:
        return "''"
    safe_chars = set('abcdefghijklmnopqrstuvwxyz' 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
                     '0123456789' '_@%+=:,.' + '/' + '-')
    if all(c in safe_chars for c in s):
        return s
    return "'" + s.replace("'", "'\"'\"'") + "'"
```

* `isSafeChar` is Python's `safe_chars` set.
* `escapeChars` is `s.replace("'", "'\"'\"'")` on the character list of `s`.
* `quote` is the functional implementation; `quoteImp` is the imperative
  (`Id.run do`, mutable state) implementation; they are proved equal.
* `shellLex` is a small model of POSIX shell word evaluation (`'...'` and
  `"..."` grouping).  The round-trip property
  `shellLex .plain (quote s).toList = s.toList` states that a shell reading the
  quoted word recovers exactly the original string -- the purpose of `shlex.quote`.
* The Python `TypeError` for non-strings cannot occur in Lean: the type `String`
  already enforces the pre-condition `pre_quote`, hence `Pre s := True`.
-/

namespace «21_shlex_quote»

/-! ## Functional implementation -/

/-- Python's `safe_chars`: ASCII letters, ASCII digits and the punctuation `_ @ % + = : , . / -`. -/
def isSafeChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '@' || c == '%' || c == '+' || c == '=' ||
    c == ':' || c == ',' || c == '.' || c == '/' || c == '-'

/-- Python's `safe_chars`, as the literal string of the source program. -/
def pySafeChars : String :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_@%+=:,./-"

/-- `s.replace("'", "'\"'\"'")` on character lists: each `'` becomes the five
characters `'"'"'`; every other character is kept unchanged. -/
def escapeChars : List Char → List Char
  | [] => []
  | c :: cs =>
    if c = '\'' then '\'' :: '"' :: '\'' :: '"' :: '\'' :: escapeChars cs
    else c :: escapeChars cs

/-- `shlex.quote`: return a shell-escaped version of the string `s`. -/
def quote (s : String) : String :=
  if s = "" then "''"
  else if s.toList.all isSafeChar then s
  else "'" ++ String.mk (escapeChars s.toList) ++ "'"

/-- The same computation on the underlying character list (proof helper). -/
def quoteChars (cs : List Char) : List Char :=
  if cs = [] then ['\'', '\'']
  else if cs.all isSafeChar then cs
  else '\'' :: (escapeChars cs ++ ['\''])

/-! ## Unit tests (the Python `check` function) -/

example : quote "" = "''" := by native_decide
example : quote "abc" = "abc" := by native_decide
example : quote "a b c" = "'a b c'" := by native_decide
example : quote "a'b" = "'a'\"'\"'b'" := by native_decide

#eval quote ""          -- "''"
#eval quote "abc"       -- "abc"
#eval quote "a b c"     -- "'a b c'"
#eval quote "a'b"       -- "'a'\"'\"'b'"
#eval quote "$HOME"     -- "'$HOME'"

example : isSafeChar 'a' = true := by decide
example : isSafeChar 'Z' = true := by decide
example : isSafeChar '7' = true := by decide
example : isSafeChar '-' = true := by decide
example : isSafeChar ' ' = false := by decide
example : isSafeChar '\'' = false := by decide
example : isSafeChar '$' = false := by decide

/-! ## A model of POSIX shell word evaluation

Only the two quoting mechanisms that `quote` produces are modelled: inside
`'...'` everything is literal; inside `"..."` everything is literal (the only
character `quote` ever places inside double quotes is `'`, which is not special
there); outside quotes a character is literal unless it opens a quote.  Safe
characters are never special in a POSIX shell, so this model agrees with a real
shell on every output of `quote`. -/

/-- Quoting state of the word scanner. -/
inductive LexMode
  | plain
  | single
  | double
  deriving DecidableEq, Repr

/-- Evaluate a shell word: strip quoting syntax, keep the quoted characters. -/
def shellLex : LexMode → List Char → List Char
  | _, [] => []
  | .plain, c :: cs =>
    if c = '\'' then shellLex .single cs
    else if c = '"' then shellLex .double cs
    else c :: shellLex .plain cs
  | .single, c :: cs =>
    if c = '\'' then shellLex .plain cs else c :: shellLex .single cs
  | .double, c :: cs =>
    if c = '"' then shellLex .plain cs else c :: shellLex .double cs

example : shellLex .plain "'a'\"'\"'b'".toList = "a'b".toList := by native_decide
example : shellLex .plain "'a b c'".toList = "a b c".toList := by native_decide

/-! ## Helper lemmas -/

theorem eq_empty_iff_toList (s : String) : s = "" ↔ s.toList = [] :=
  ⟨fun h => by subst h; rfl, fun h => congrArg String.mk h⟩

theorem quote_toList (s : String) : (quote s).toList = quoteChars s.toList := by
  unfold quote quoteChars
  by_cases h : s = ""
  · rw [if_pos h, if_pos ((eq_empty_iff_toList s).1 h)]
    rfl
  · have h' : s.toList ≠ [] := fun hl => h ((eq_empty_iff_toList s).2 hl)
    rw [if_neg h, if_neg h']
    by_cases hs : s.toList.all isSafeChar = true
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs]
      rfl

theorem isSafeChar_ne_squote {c : Char} (h : isSafeChar c = true) : c ≠ '\'' := by
  rintro rfl
  exact absurd h (by decide)

theorem isSafeChar_ne_dquote {c : Char} (h : isSafeChar c = true) : c ≠ '"' := by
  rintro rfl
  exact absurd h (by decide)

theorem escapeChars_length (cs : List Char) :
    (escapeChars cs).length = cs.length + 4 * cs.count '\'' := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = '\''
    · subst hc
      simp [escapeChars, ih]
      omega
    · simp [escapeChars, hc, ih]
      omega

theorem shellLex_plain_safe (cs : List Char) (h : cs.all isSafeChar = true) :
    shellLex .plain cs = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    simp only [shellLex, if_neg (isSafeChar_ne_squote h.1), if_neg (isSafeChar_ne_dquote h.1),
      ih h.2]

theorem shellLex_single_escape (cs rest : List Char) :
    shellLex .single (escapeChars cs ++ '\'' :: rest) = cs ++ shellLex .plain rest := by
  induction cs with
  | nil => simp [escapeChars, shellLex]
  | cons c cs ih =>
    by_cases hc : c = '\''
    · subst hc
      simp [escapeChars, shellLex, ih]
    · simp [escapeChars, shellLex, hc, ih]

theorem quoteChars_ne_nil (cs : List Char) : quoteChars cs ≠ [] := by
  unfold quoteChars
  split_ifs with h1 h2
  · simp
  · exact h1
  · simp

theorem quoteChars_roundtrip (cs : List Char) : shellLex .plain (quoteChars cs) = cs := by
  unfold quoteChars
  split_ifs with h1 h2
  · subst h1
    rfl
  · exact shellLex_plain_safe cs h2
  · have h := shellLex_single_escape cs []
    simpa [shellLex] using h

/-- Non-ASCII characters are never safe (Lean's `Char.isAlphanum` is ASCII-only,
like Python's explicit `safe_chars` set). -/
theorem isSafeChar_eq_false_of_ge (c : Char) (h : 128 ≤ c.toNat) : isSafeChar c = false := by
  have hv : 128 ≤ c.val.toNat := h
  apply Bool.eq_false_iff.mpr
  intro hs
  simp only [isSafeChar, Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, or_assoc] at hs
  rcases hs with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h3 := UInt32.le_iff_toNat_le.1 h2
    rw [show (90 : UInt32).toNat = 90 from rfl] at h3
    omega
  · have h3 := UInt32.le_iff_toNat_le.1 h2
    rw [show (122 : UInt32).toNat = 122 from rfl] at h3
    omega
  · have h3 := UInt32.le_iff_toNat_le.1 h2
    rw [show (57 : UInt32).toNat = 57 from rfl] at h3
    omega
  all_goals exact absurd h (by decide)

/-- `isSafeChar` is exactly membership in Python's `safe_chars` string. -/
theorem isSafeChar_iff_mem (c : Char) : isSafeChar c = true ↔ c ∈ pySafeChars.toList := by
  by_cases h : c.toNat < 128
  · have key : ∀ n, n < 128 →
        (isSafeChar (Char.ofNat n) = true ↔ Char.ofNat n ∈ pySafeChars.toList) := by decide
    have := key c.toNat h
    rwa [Char.ofNat_toNat] at this
  · constructor
    · intro hs
      rw [isSafeChar_eq_false_of_ge c (by omega)] at hs
      exact absurd hs Bool.false_ne_true
    · intro hm
      have : ∀ x ∈ pySafeChars.toList, x.toNat < 128 := by decide
      exact absurd (this c hm) h

/-! ## Pre-condition -/

/-- Python's `pre_quote(s)`: the input is a string.  The Lean type `String`
already guarantees this, so the pre-condition is trivially satisfied. -/
def Pre (_s : String) : Prop := True

/-! ## Properties -/

/-- `if not s: return "''"` -- the empty string is quoted as `''`. -/
def quote_empty_prop (s : String) : Prop := s = "" → quote s = "''"

/-- A non-empty string all of whose characters are in Python's `safe_chars`
(`all(c in safe_chars for c in s)`) is returned unchanged. -/
def quote_safe_prop (s : String) : Prop :=
  s ≠ "" → (∀ c ∈ s.toList, c ∈ pySafeChars.toList) → quote s = s

/-- A string containing a character outside `safe_chars` is wrapped in single
quotes, with every `'` replaced by `'"'"'` (`"'" + s.replace("'", "'\"'\"'") + "'"`). -/
def quote_unsafe_prop (s : String) : Prop :=
  (∃ c ∈ s.toList, c ∉ pySafeChars.toList) →
    quote s = "'" ++ String.mk (escapeChars s.toList) ++ "'"

/-- The result is never the empty string. -/
def quote_nonempty_prop (s : String) : Prop := quote s ≠ ""

/-- The result is either the input itself or a word that starts and ends with `'`. -/
def quote_shape_prop (s : String) : Prop :=
  quote s = s ∨
    ((quote s).toList.head? = some '\'' ∧ (quote s).toList.getLast? = some '\'')

/-- Round trip: a POSIX shell evaluating the quoted word obtains exactly `s`. -/
def quote_roundtrip_prop (s : String) : Prop :=
  shellLex .plain (quote s).toList = s.toList

/-- Exact length of the result: `2` for the empty string, unchanged for safe
strings, otherwise two surrounding quotes plus four extra characters per `'`. -/
def quote_length_prop (s : String) : Prop :=
  (quote s).length =
    if s = "" then 2
    else if s.toList.all isSafeChar then s.length
    else s.length + 2 + 4 * s.toList.count '\''

/-- Quoting is injective: distinct strings have distinct quoted forms. -/
def quote_injective_prop (s : String) : Prop :=
  ∀ t : String, quote s = quote t → s = t

/-- `quote` leaves `s` unchanged exactly when `s` is non-empty and all its
characters are in `safe_chars`. -/
def quote_unchanged_iff_prop (s : String) : Prop :=
  quote s = s ↔ (s ≠ "" ∧ ∀ c ∈ s.toList, c ∈ pySafeChars.toList)

/-- The implementation's safe-character test agrees with Python's `safe_chars`
set on every character. -/
def safe_set_prop : Prop := ∀ c : Char, isSafeChar c = true ↔ c ∈ pySafeChars.toList

/-! ## Property theorems -/

theorem quote_empty_thm (s : String) : quote_empty_prop s := by
  intro h
  subst h
  rfl

theorem quote_safe_thm (s : String) : quote_safe_prop s := by
  intro hne hsafe
  unfold quote
  rw [if_neg hne, if_pos (List.all_eq_true.mpr fun c hc => (isSafeChar_iff_mem c).2 (hsafe c hc))]

theorem quote_unsafe_thm (s : String) : quote_unsafe_prop s := by
  rintro ⟨c, hc, hunsafe⟩
  have hne : s ≠ "" := by
    intro h
    rw [(eq_empty_iff_toList s).1 h] at hc
    simp at hc
  have hall : ¬ s.toList.all isSafeChar = true := by
    intro h
    rw [List.all_eq_true] at h
    exact hunsafe ((isSafeChar_iff_mem c).1 (h c hc))
  unfold quote
  rw [if_neg hne, if_neg hall]

theorem quote_nonempty_thm (s : String) : quote_nonempty_prop s := by
  intro h
  apply quoteChars_ne_nil s.toList
  rw [← quote_toList, h]
  rfl

theorem quote_roundtrip_thm (s : String) : quote_roundtrip_prop s := by
  unfold quote_roundtrip_prop
  rw [quote_toList]
  exact quoteChars_roundtrip s.toList

theorem quote_injective_thm (s : String) : quote_injective_prop s := by
  intro t h
  have h1 := quote_roundtrip_thm s
  have h2 := quote_roundtrip_thm t
  unfold quote_roundtrip_prop at h1 h2
  rw [h] at h1
  exact congrArg String.mk (h1.symm.trans h2)

theorem quote_length_thm (s : String) : quote_length_prop s := by
  unfold quote_length_prop
  rw [show (quote s).length = (quote s).toList.length from rfl, quote_toList,
    show s.length = s.toList.length from rfl]
  unfold quoteChars
  by_cases h : s = ""
  · rw [if_pos h, if_pos ((eq_empty_iff_toList s).1 h)]
    rfl
  · have h' : s.toList ≠ [] := fun hl => h ((eq_empty_iff_toList s).2 hl)
    rw [if_neg h, if_neg h']
    by_cases hs : s.toList.all isSafeChar = true
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs]
      simp only [List.length_cons, List.length_append, List.length_nil, escapeChars_length]
      omega

theorem quote_shape_thm (s : String) : quote_shape_prop s := by
  unfold quote_shape_prop
  by_cases h : s = ""
  · right
    subst h
    exact ⟨rfl, rfl⟩
  · by_cases hs : s.toList.all isSafeChar = true
    · left
      unfold quote
      rw [if_neg h, if_pos hs]
    · right
      have h' : s.toList ≠ [] := fun hl => h ((eq_empty_iff_toList s).2 hl)
      rw [quote_toList]
      unfold quoteChars
      rw [if_neg h', if_neg hs]
      exact ⟨rfl, by rw [← List.cons_append, List.getLast?_concat]⟩

theorem quote_unchanged_iff_thm (s : String) : quote_unchanged_iff_prop s := by
  unfold quote_unchanged_iff_prop
  constructor
  · intro h
    by_cases h1 : s = ""
    · exfalso
      subst h1
      exact quote_nonempty_thm "" h
    · refine ⟨h1, ?_⟩
      by_contra hns
      have hns' : ¬ s.toList.all isSafeChar = true := fun hall =>
        hns fun c hc => (isSafeChar_iff_mem c).1 (List.all_eq_true.1 hall c hc)
      have hl := quote_length_thm s
      unfold quote_length_prop at hl
      rw [if_neg h1, if_neg hns', h] at hl
      omega
  · rintro ⟨h1, h2⟩
    exact quote_safe_thm s h1 h2

theorem safe_set_thm : safe_set_prop := isSafeChar_iff_mem

/-! ## Post-condition -/

/-- Post-condition of `quote`: conjunction of all properties above. -/
def Post_prop (s : String) : Prop :=
  quote_empty_prop s ∧ quote_safe_prop s ∧ quote_unsafe_prop s ∧ quote_nonempty_prop s ∧
    quote_shape_prop s ∧ quote_roundtrip_prop s ∧ quote_length_prop s ∧
    quote_injective_prop s ∧ quote_unchanged_iff_prop s ∧ safe_set_prop

/-! ## Property-based tests -/

-- quote_empty_prop
#eval Plausible.Testable.check (∀ s : String, s = "" → quote s = "''")
-- quote_safe_prop (random strings are rarely all-safe; see `safeStringOf` tests below)
#eval Plausible.Testable.check
  (∀ s : String, s ≠ "" → (s.toList.all fun c => decide (c ∈ pySafeChars.toList)) = true →
    quote s = s)
-- quote_unsafe_prop
#eval Plausible.Testable.check
  (∀ s : String, (∃ c ∈ s.toList, c ∉ pySafeChars.toList) →
    quote s = "'" ++ String.mk (escapeChars s.toList) ++ "'")
-- quote_nonempty_prop
#eval Plausible.Testable.check (∀ s : String, quote s ≠ "")
-- quote_shape_prop
#eval Plausible.Testable.check
  (∀ s : String, quote s = s ∨
    ((quote s).toList.head? = some '\'' ∧ (quote s).toList.getLast? = some '\''))
-- quote_roundtrip_prop
#eval Plausible.Testable.check (∀ s : String, shellLex .plain (quote s).toList = s.toList)
-- quote_length_prop
#eval Plausible.Testable.check
  (∀ s : String, (quote s).length =
    if s = "" then 2
    else if s.toList.all isSafeChar then s.length
    else s.length + 2 + 4 * s.toList.count '\'')
-- quote_injective_prop
#eval Plausible.Testable.check (∀ s t : String, quote s = quote t → s = t)
-- quote_unchanged_iff_prop
#eval Plausible.Testable.check
  (∀ s : String, (quote s = s ↔
    (s ≠ "" ∧ (s.toList.all fun c => decide (c ∈ pySafeChars.toList)) = true)))
-- safe_set_prop (random characters; exhaustive over ASCII below)
#eval Plausible.Testable.check (∀ c : Char, isSafeChar c = true ↔ c ∈ pySafeChars.toList)
example : (List.range 128).all (fun n =>
    decide (isSafeChar (Char.ofNat n) = true ↔ Char.ofNat n ∈ pySafeChars.toList)) = true := by
  native_decide
example : pySafeChars.length = 72 := by native_decide

/-- Build an all-safe string from indices into `pySafeChars`: a random generator
for the safe-input properties, which uniformly random strings almost never hit. -/
def safeStringOf (xs : List (Fin 72)) : String :=
  String.mk (xs.map fun i => pySafeChars.toList.getD i.val 'a')

#eval safeStringOf [0, 26, 52, 62, 71]   -- "aA0_-"
-- quote_safe_prop / quote_unchanged_iff_prop / quote_length_prop on random all-safe strings
#eval Plausible.Testable.check
  (∀ xs : List (Fin 72), xs ≠ [] → quote (safeStringOf xs) = safeStringOf xs)
#eval Plausible.Testable.check
  (∀ xs : List (Fin 72), (quote (safeStringOf xs) = safeStringOf xs ↔ xs ≠ []))
#eval Plausible.Testable.check
  (∀ xs : List (Fin 72), (quote (safeStringOf xs)).length = if xs = [] then 2 else xs.length)

/-- Executable form of `Post_prop` (the quantified injectivity clause is tested
separately on all pairs of samples). -/
def postCheck (s : String) : Bool :=
  decide ((s = "" → quote s = "''") ∧
    (s ≠ "" → (∀ c ∈ s.toList, c ∈ pySafeChars.toList) → quote s = s) ∧
    ((∃ c ∈ s.toList, c ∉ pySafeChars.toList) →
      quote s = "'" ++ String.mk (escapeChars s.toList) ++ "'") ∧
    quote s ≠ "" ∧
    (quote s = s ∨
      ((quote s).toList.head? = some '\'' ∧ (quote s).toList.getLast? = some '\'')) ∧
    shellLex .plain (quote s).toList = s.toList ∧
    ((quote s).length =
      if s = "" then 2
      else if s.toList.all isSafeChar then s.length
      else s.length + 2 + 4 * s.toList.count '\'') ∧
    (quote s = s ↔ (s ≠ "" ∧ ∀ c ∈ s.toList, c ∈ pySafeChars.toList)))

/-- Sample inputs for bounded property-based tests (safe, unsafe, quote-heavy,
non-ASCII, whitespace, shell metacharacters). -/
def samples : List String :=
  ["", "abc", "a b c", "a'b", "'", "''", "'''", "\"", "a\"b", "$HOME", "a\\b",
   "x@y.z", "/usr/bin/env", "1+1=2", ",./-_%:", "ABCxyz019", "hello world",
   "it's", "a'b'c", "don't \"quote\" me", "tab\there", "new\nline", "a;b",
   "a|b", "*.txt", "~user", "é", "日本語", "αβγ", " ", "  leading", "trailing  ",
   "`cmd`", "$(cmd)", "a&b", "<>", "#comment", "a=b", "-flag", "--opt=val"]

-- Post_prop (all clauses) on every sample
example : samples.all postCheck = true := by native_decide
-- quote_injective_prop on all pairs of samples
example : (samples.all fun s => samples.all fun t => decide (quote s = quote t → s = t)) = true := by
  native_decide
-- quote_safe_prop on explicitly safe inputs (the random test above rarely hits them)
example : (["abc", "x@y.z", "/usr/bin/env", "1+1=2", ",./-_%:", "ABCxyz019", "a=b",
    "-flag", "--opt=val"].all fun s => decide (quote s = s)) = true := by native_decide
-- quote_roundtrip_prop on every sample
example : (samples.all fun s => decide (shellLex .plain (quote s).toList = s.toList)) = true := by
  native_decide
-- Post_prop PBT via Plausible (executable clauses)
#eval Plausible.Testable.check (∀ s : String, postCheck s = true)

/-! ## Correctness: `Pre → Post` -/

theorem quote_correct (s : String) (_hpre : Pre s) : Post_prop s :=
  ⟨quote_empty_thm s, quote_safe_thm s, quote_unsafe_thm s, quote_nonempty_thm s,
    quote_shape_thm s, quote_roundtrip_thm s, quote_length_thm s, quote_injective_thm s,
    quote_unchanged_iff_thm s, safe_set_thm⟩

/-! ## Imperative implementation -/

/-- Imperative version of `quote`, following the Python control flow: early
return for the empty string, a loop computing `all(c in safe_chars for c in s)`,
and a loop building `"'" + s.replace("'", "'\"'\"'") + "'"`. -/
def quoteImp (s : String) : String := Id.run do
  let cs := s.toList
  -- if not s: return "''"
  if cs.isEmpty then
    return "''"
  -- all(c in safe_chars for c in s)
  let mut allSafe : Bool := true
  for c in cs do
    if !isSafeChar c then
      allSafe := false
  if allSafe then
    return s
  -- "'" + s.replace("'", "'\"'\"'") + "'"
  let mut out : List Char := ['\'']
  for c in cs do
    if c == '\'' then
      out := out ++ ['\'', '"', '\'', '"', '\'']
    else
      out := out ++ [c]
  out := out ++ ['\'']
  return String.mk out

/-! ## Imperative tests -/

example : quoteImp "" = "''" := by native_decide
example : quoteImp "abc" = "abc" := by native_decide
example : quoteImp "a b c" = "'a b c'" := by native_decide
example : quoteImp "a'b" = "'a'\"'\"'b'" := by native_decide
example : (samples.all fun s => decide (quoteImp s = quote s)) = true := by native_decide

#eval quoteImp ""        -- "''"
#eval quoteImp "a'b"     -- "'a'\"'\"'b'"
#eval Plausible.Testable.check (∀ s : String, quoteImp s = quote s)

/-! ## Equivalence: functional = imperative -/

/-- A `for` loop over a list in `Id` whose body always `yield`s is a left fold. -/
theorem forIn_eq_foldl_of_yield {α β : Type} (xs : List α) (init : β)
    (f : α → β → Id (ForInStep β)) (g : α → β → β)
    (hf : ∀ x r, f x r = pure (ForInStep.yield (g x r))) :
    forIn (m := Id) xs init f = xs.foldl (fun r x => g x r) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, hf]
    exact ih (g x init)

theorem foldl_and_safe (cs : List Char) (b : Bool) :
    cs.foldl (fun r c => r && isSafeChar c) b = (b && cs.all isSafeChar) := by
  induction cs generalizing b with
  | nil => simp
  | cons c cs ih => simp [List.foldl_cons, List.all_cons, ih, Bool.and_assoc]

theorem foldl_escape (cs acc : List Char) :
    cs.foldl (fun out c =>
      if (c == '\'') = true then out ++ ['\'', '"', '\'', '"', '\''] else out ++ [c]) acc
      = acc ++ escapeChars cs := by
  induction cs generalizing acc with
  | nil => simp [escapeChars]
  | cons c cs ih =>
    simp only [List.foldl_cons, ih, escapeChars]
    by_cases hc : c = '\''
    · subst hc
      simp
    · simp [hc]

theorem id_bind_eq {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

theorem id_pure_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl

theorem quoteImp_eq_quote (s : String) : quoteImp s = quote s := by
  unfold quoteImp
  simp only [Id.run]
  rw [forIn_eq_foldl_of_yield (g := fun c r => r && isSafeChar c)]
  · rw [forIn_eq_foldl_of_yield (g := fun c out =>
        if (c == '\'') = true then out ++ ['\'', '"', '\'', '"', '\''] else out ++ [c])]
    · simp only [foldl_and_safe, foldl_escape, id_bind_eq, id_pure_eq, Bool.true_and]
      unfold quote
      by_cases h : s = ""
      · subst h
        rfl
      · have h' : s.toList ≠ [] := fun hl => h ((eq_empty_iff_toList s).2 hl)
        have hne : ¬ s.toList.isEmpty = true := fun he => h' (List.isEmpty_iff.1 he)
        rw [if_neg hne, if_neg h]
        by_cases hs : s.toList.all isSafeChar = true
        · rw [if_pos hs, if_pos hs]
        · rw [if_neg hs, if_neg hs]
          rfl
    · intro x r
      cases hx : (x == '\'') <;> rfl
  · intro x r
    cases hx : isSafeChar x <;> cases r <;> rfl

end «21_shlex_quote»
