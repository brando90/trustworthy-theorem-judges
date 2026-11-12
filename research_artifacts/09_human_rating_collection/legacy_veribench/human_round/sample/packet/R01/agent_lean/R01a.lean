import Mathlib

/-!
# `shlex.quote` — shell escaping

Lean 4 formalization of Python's `shlex.quote`.

The Python source being modelled:

```python
def quote(s):
    if not s:
        return "''"
    if not isinstance(s, str):
        raise TypeError("expected string object")
    safe_chars = set(ascii_letters + digits + PUNCT)   # PUNCT = underscore, at,
                                                       # percent, plus, equals,
                                                       # colon, comma, dot,
                                                       # slash, dash
    if all(c in safe_chars for c in s):
        return s
    return "'" + s.replace("'", "'\"'\"'") + "'"
```

Because Lean's `String` type already enforces "is a string", the pre-condition
`pre_quote` degenerates to `True`; it is nevertheless recorded as `Pre`.

The file contains a functional implementation (`quote`), unit tests, the
pre-condition, a family of property propositions with proofs, the post-condition,
the correctness theorem, an imperative (`Id.run do`) implementation with mutable
state, and the functional/imperative equivalence theorem.
-/

namespace «21_shlex_quote»

/-! ## Implementation (functional) -/

/-- The POSIX-shell "safe" character set used by `shlex.quote`. -/
def safeChars : List Char :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_@%+=:,./-".toList

/-- `isSafeChar c` mirrors Python's `c in safe_chars`. -/
def isSafeChar (c : Char) : Bool := safeChars.contains c

/-- The replacement text for a single quote: `'"'"'`. -/
def quoteEscape : List Char := ['\'', '"', '\'', '"', '\'']

/-- `s.replace("'", "'\"'\"'")` at the level of character lists. -/
def escapeChars : List Char → List Char
  | [] => []
  | c :: cs => (if c = '\'' then quoteEscape else [c]) ++ escapeChars cs

/-- String-level version of `escapeChars`. -/
def escapeStr (s : String) : String := ⟨escapeChars s.data⟩

/-- `shlex.quote` at the level of character lists. -/
def quoteChars (l : List Char) : List Char :=
  if l = [] then ['\'', '\'']
  else if l.all isSafeChar then l
  else '\'' :: (escapeChars l ++ ['\''])

/-- `shlex.quote`: return a shell-escaped version of the string `s`. -/
def quote (s : String) : String := ⟨quoteChars s.data⟩

/-! ## Unit tests (mirroring Python's `check`) -/

-- 1. empty string
example : quote "" = "''" := by native_decide
-- 2. safe string
example : quote "abc" = "abc" := by native_decide
-- 3. string with spaces
example : quote "a b c" = "'a b c'" := by native_decide
-- 4. string containing a single quote
example : quote "a'b" = "'a'\"'\"'b'" := by native_decide

#eval quote ""
#eval quote "abc"
#eval quote "a b c"
#eval quote "a'b"

/-! ## Pre-condition -/

/-- `pre_quote s` is "s is a string".  In Lean this is guaranteed by typing, so
the pre-condition holds unconditionally. -/
def Pre (_s : String) : Prop := True

/-! ## Auxiliary lemmas -/

@[simp] theorem mk_data (s : String) : (String.mk s.data) = s := rfl

@[simp] theorem data_mk (l : List Char) : (String.mk l).data = l := rfl

theorem data_append (a b : String) : (a ++ b).data = a.data ++ b.data := rfl

@[simp] theorem id_pure_eq {α : Type _} (a : α) : (pure a : Id α) = a := rfl

@[simp] theorem data_eq_nil_iff (s : String) : s.data = [] ↔ s = "" := by
  constructor
  · intro h
    calc s = String.mk s.data := rfl
      _ = String.mk [] := by rw [h]
      _ = "" := rfl
  · intro h; subst h; rfl

/-- A witness of an unsafe character refutes `List.all isSafeChar`. -/
theorem not_all_safe {l : List Char} {c : Char} (hc : c ∈ l)
    (hcs : isSafeChar c = false) : ¬ (l.all isSafeChar = true) := by
  intro h
  have := (List.all_eq_true.mp h) c hc
  rw [hcs] at this
  exact Bool.noConfusion this

/-! ## Properties -/

/-- Empty input is quoted as `''`. -/
def quote_empty_prop (s : String) : Prop :=
  s = "" → quote s = "''"

theorem quote_empty_thm (s : String) : quote_empty_prop s := by
  intro h; subst h; rfl

/-- A non-empty string made only of safe characters is returned unchanged. -/
def quote_safe_prop (s : String) : Prop :=
  s ≠ "" → (∀ c ∈ s.data, isSafeChar c = true) → quote s = s

theorem quote_safe_thm (s : String) : quote_safe_prop s := by
  intro hne hall
  have h1 : s.data ≠ [] := by simpa using hne
  have h2 : s.data.all isSafeChar = true := List.all_eq_true.mpr hall
  simp [quote, quoteChars, h1, h2]

/-- A non-empty string containing at least one unsafe character is wrapped in
single quotes, with every embedded `'` replaced by `'"'"'`. -/
def quote_unsafe_prop (s : String) : Prop :=
  s ≠ "" → (∃ c ∈ s.data, isSafeChar c = false) →
    quote s = "'" ++ escapeStr s ++ "'"

theorem quote_unsafe_thm (s : String) : quote_unsafe_prop s := by
  intro hne hex
  obtain ⟨c, hc, hcs⟩ := hex
  have h1 : s.data ≠ [] := by simpa using hne
  have h2 : ¬ (s.data.all isSafeChar = true) := not_all_safe hc hcs
  have hq : quote s = String.mk ('\'' :: (escapeChars s.data ++ ['\''])) := by
    simp [quote, quoteChars, h1, h2]
  have hr : ("'" ++ escapeStr s ++ "'")
      = String.mk ('\'' :: (escapeChars s.data ++ ['\''])) := by
    apply congrArg String.mk
    rfl
  rw [hq, hr]

/-- The result of `quote` is never the empty string. -/
def quote_nonempty_prop (s : String) : Prop := quote s ≠ ""

theorem quote_nonempty_thm (s : String) : quote_nonempty_prop s := by
  have h : (quote s).data ≠ [] := by
    simp only [quote, data_mk, quoteChars]
    by_cases h1 : s.data = []
    · simp [h1]
    · by_cases h2 : s.data.all isSafeChar = true <;> simp [h1, h2]
  intro hc
  rw [hc] at h
  exact h rfl

/-- Escaping is the identity on strings that contain no single quote. -/
def escape_id_prop (s : String) : Prop :=
  '\'' ∉ s.data → escapeStr s = s

theorem escapeChars_id (l : List Char) (h : '\'' ∉ l) : escapeChars l = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    rw [List.mem_cons, not_or] at h
    have hcne : ¬ (c = '\'') := fun hh => h.1 hh.symm
    rw [escapeChars, if_neg hcne, ih h.2]
    rfl

theorem escape_id_thm (s : String) : escape_id_prop s := by
  intro h
  show String.mk (escapeChars s.data) = s
  rw [escapeChars_id s.data h, mk_data]

/-- Every single quote of the input becomes exactly three single quotes in the
escaped text (the replacement `'"'"'` contains three of them). -/
def escape_count_prop (s : String) : Prop :=
  (escapeChars s.data).count '\'' = 3 * s.data.count '\''

theorem escapeChars_count (l : List Char) :
    (escapeChars l).count '\'' = 3 * l.count '\'' := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : c = '\''
    · subst h
      have e1 : escapeChars ('\'' :: cs) = quoteEscape ++ escapeChars cs := by
        simp [escapeChars]
      have h3 : quoteEscape.count '\'' = 3 := by decide
      have h4 : ('\'' :: cs).count '\'' = cs.count '\'' + 1 := by simp
      rw [e1, List.count_append, ih, h3, h4]
      omega
    · have hne : ('\'' : Char) ≠ c := fun hh => h hh.symm
      have e1 : escapeChars (c :: cs) = c :: escapeChars cs := by
        simp [escapeChars, h]
      have h4 : ∀ l : List Char, (c :: l).count '\'' = l.count '\'' := by
        intro l; simp [h]
      rw [e1, h4, h4, ih]

theorem escape_count_thm (s : String) : escape_count_prop s :=
  escapeChars_count s.data

/-- When quoting actually happens, the result starts and ends with `'`. -/
def quote_wrapped_prop (s : String) : Prop :=
  (∃ c ∈ s.data, isSafeChar c = false) →
    (quote s).data.head? = some '\'' ∧ (quote s).data.getLast? = some '\''

theorem quote_wrapped_thm (s : String) : quote_wrapped_prop s := by
  intro hex
  obtain ⟨c, hc, hcs⟩ := hex
  have h1 : s.data ≠ [] := by
    intro h; rw [h] at hc; simp at hc
  have h2 : ¬ (s.data.all isSafeChar = true) := not_all_safe hc hcs
  simp only [quote, data_mk, quoteChars, if_neg h1, if_neg h2]
  refine ⟨rfl, ?_⟩
  show (('\'' :: escapeChars s.data) ++ ['\'']).getLast? = some '\''
  exact List.getLast?_concat

/-! ## Post-condition -/

/-- The post-condition: conjunction of all the properties above. -/
def Post_prop (s : String) : Prop :=
  quote_empty_prop s ∧ quote_safe_prop s ∧ quote_unsafe_prop s ∧
  quote_nonempty_prop s ∧ escape_id_prop s ∧ escape_count_prop s ∧
  quote_wrapped_prop s

/-! ## Correctness -/

/-- Correctness: the pre-condition implies the post-condition. -/
theorem quote_correct (s : String) : Pre s → Post_prop s := by
  intro _
  exact ⟨quote_empty_thm s, quote_safe_thm s, quote_unsafe_thm s,
    quote_nonempty_thm s, escape_id_thm s, escape_count_thm s,
    quote_wrapped_thm s⟩

/-! ## Imperative implementation -/

/-- Imperative "all characters are safe" loop with a mutable accumulator. -/
def allSafeLoop (l : List Char) (b : Bool) : Bool := Id.run do
  let mut acc := b
  for c in l do
    if !isSafeChar c then
      acc := false
  return acc

/-- Imperative escaping loop with a mutable output buffer. -/
def escapeLoop (l : List Char) (init : List Char) : List Char := Id.run do
  let mut out := init
  for c in l do
    if c = '\'' then
      out := out ++ quoteEscape
    else
      out := out ++ [c]
  return out

/-- Imperative version of `shlex.quote`, using `Id.run do` and mutable state. -/
def quoteImp (s : String) : String := Id.run do
  let l := s.data
  if l = [] then
    return "''"
  let mut allSafe := true
  allSafe := allSafeLoop l allSafe
  if allSafe then
    return s
  let mut out : List Char := ['\'']
  out := escapeLoop l out
  out := out ++ ['\'']
  return ⟨out⟩

/-! ## Imperative unit tests -/

example : quoteImp "" = "''" := by native_decide
example : quoteImp "abc" = "abc" := by native_decide
example : quoteImp "a b c" = "'a b c'" := by native_decide
example : quoteImp "a'b" = "'a'\"'\"'b'" := by native_decide

#eval quoteImp ""
#eval quoteImp "abc"
#eval quoteImp "a b c"
#eval quoteImp "a'b"

/-! ## Equivalence of the two implementations -/

theorem allSafeLoop_eq (l : List Char) (b : Bool) :
    allSafeLoop l b = (b && l.all isSafeChar) := by
  induction l generalizing b with
  | nil => show b = _ ; simp
  | cons c cs ih =>
    have step : allSafeLoop (c :: cs) b
        = allSafeLoop cs (if isSafeChar c then b else false) := by
      by_cases h : isSafeChar c <;> simp [allSafeLoop, Id.run, h] <;> rfl
    rw [step, ih]
    by_cases h : isSafeChar c <;> simp [h]

theorem escapeLoop_eq (l : List Char) (init : List Char) :
    escapeLoop l init = init ++ escapeChars l := by
  induction l generalizing init with
  | nil => show init = _ ; simp [escapeChars]
  | cons c cs ih =>
    have step : escapeLoop (c :: cs) init
        = escapeLoop cs (init ++ (if c = '\'' then quoteEscape else [c])) := by
      by_cases h : c = '\'' <;> simp [escapeLoop, Id.run, h] <;> rfl
    rw [step, ih, escapeChars, List.append_assoc]

/-- The functional and the imperative implementations agree. -/
theorem quote_eq_quoteImp (s : String) : quote s = quoteImp s := by
  simp only [quote, quoteImp, quoteChars, Id.run, id_pure_eq, allSafeLoop_eq,
    escapeLoop_eq, Bool.true_and]
  by_cases h1 : s.data = []
  · simp [h1]
  · by_cases h2 : s.data.all isSafeChar = true <;> simp [h1, h2] <;> rfl

end «21_shlex_quote»
