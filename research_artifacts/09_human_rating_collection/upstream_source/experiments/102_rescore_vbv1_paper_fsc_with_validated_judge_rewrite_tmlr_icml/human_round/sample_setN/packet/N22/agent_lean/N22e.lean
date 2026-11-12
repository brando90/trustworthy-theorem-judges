import Mathlib

/-!
# 21_shlex_quote — Formalization of Python's `shlex.quote`

This file formalizes the shell-quoting function from Python's standard
`shlex` library:

* the empty string is quoted as `''`;
* a string consisting only of shell-safe characters
  (`a-z A-Z 0-9` and `_@%+=:,./` plus `-`) is returned unchanged;
* any other string is wrapped in single quotes, and every embedded
  single quote `'` is replaced by the sequence `'"'"'`.

We give a functional implementation, state and prove its correctness
properties, give an imperative implementation in `Id` with mutable state,
and prove that the two implementations coincide.
-/

namespace «21_shlex_quote»

/-- The shell-safe characters, exactly as in CPython's `shlex`. -/
def isSafeChar (c : Char) : Bool :=
  decide (('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('0' ≤ c ∧ c ≤ '9') ∨
    c = '_' ∨ c = '@' ∨ c = '%' ∨ c = '+' ∨ c = '=' ∨ c = ':' ∨ c = ',' ∨ c = '.' ∨ c = '/' ∨ c = '-')

/-- The replacement text for a single character: `'` becomes `'"'"'`,
every other character is kept as-is. -/
def escChar (c : Char) : List Char :=
  if c == '\'' then ['\'', '"', '\'', '"', '\''] else [c]

/-- Escape every single quote in a character list (`s.replace("'", "'\"'\"'")`). -/
def escape : List Char → List Char
  | [] => []
  | c :: cs => escChar c ++ escape cs

/-- The quoting algorithm on character lists. -/
def quoteList (l : List Char) : List Char :=
  if l.isEmpty then ['\'', '\'']
  else if l.all isSafeChar then l
  else ['\''] ++ escape l ++ ['\'']

/-- Functional implementation of `shlex.quote`. -/
def quote (s : String) : String := (quoteList s.toList).asString

/-! ## Unit tests -/

example : quote "" = "''" := by native_decide
example : quote "abc" = "abc" := by native_decide
example : quote "a b c" = "'a b c'" := by native_decide
example : quote "a'b" = "'a'\"'\"'b'" := by native_decide
example : quote "user@example.com" = "user@example.com" := by native_decide
example : quote "-x_1.0" = "-x_1.0" := by native_decide
example : quote "a;b" = "'a;b'" := by native_decide

#eval quote ""          -- "''"
#eval quote "abc"       -- "abc"
#eval quote "a b c"     -- "'a b c'"
#eval quote "a'b"       -- "'a'\"'\"'b'"

/-! ## Pre-condition -/

/-- Python pre-condition `isinstance(s, str)`: in Lean the input is
statically known to be a `String`, so the predicate is trivially true. -/
def Pre (_s : String) : Prop := True

/-! ## Helper lemmas about `quoteList` -/

theorem quoteList_safe (l : List Char) (hne : l ≠ []) (hall : l.all isSafeChar = true) :
    quoteList l = l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons c cs => simp [quoteList, List.isEmpty, hall]

theorem quoteList_unsafe (l : List Char) (hall : l.all isSafeChar = false) :
    quoteList l = ['\''] ++ escape l ++ ['\''] := by
  cases l with
  | nil => simp at hall
  | cons c cs => simp [quoteList, List.isEmpty, hall]

theorem quoteList_nonempty (l : List Char) : quoteList l ≠ [] := by
  cases l with
  | nil => decide
  | cons c cs =>
    by_cases h : (c :: cs).all isSafeChar = true
    · simp [quoteList, List.isEmpty, h]
    · simp only [Bool.not_eq_true] at h
      simp [quoteList, List.isEmpty, h]

/-! ## Properties -/

/-- The empty string is quoted as `''`. -/
def empty_prop : Prop := quote "" = "''"

/-- Safe non-empty strings are returned unchanged. -/
def safe_prop (s : String) : Prop :=
  s ≠ "" → s.toList.all isSafeChar = true → quote s = s

/-- Unsafe strings are wrapped in single quotes. -/
def unsafe_prop (s : String) : Prop :=
  s.toList.all isSafeChar = false → ∃ mid : String, quote s = "'" ++ mid ++ "'"

/-- The output is never empty. -/
def nonempty_prop (s : String) : Prop := quote s ≠ ""

theorem empty_thm : empty_prop := rfl

theorem safe_thm (s : String) : safe_prop s := by
  intro hne hall
  obtain ⟨cs⟩ := s
  have hne' : cs ≠ [] := by
    intro h
    apply hne
    rw [h]
  have h := quoteList_safe cs hne' hall
  show (quoteList cs).asString = String.mk cs
  rw [h]
  rfl

theorem unsafe_thm (s : String) : unsafe_prop s := by
  intro hall
  obtain ⟨cs⟩ := s
  refine ⟨(escape cs).asString, ?_⟩
  show (quoteList cs).asString = "'" ++ (escape cs).asString ++ "'"
  rw [quoteList_unsafe cs hall]
  rfl

theorem nonempty_thm (s : String) : nonempty_prop s := by
  intro heq
  obtain ⟨cs⟩ := s
  exact quoteList_nonempty cs (congrArg String.data heq)

/-! ## Post-condition -/

/-- Post-condition: conjunction of all correctness properties. -/
def Post_prop (s : String) : Prop :=
  empty_prop ∧ safe_prop s ∧ unsafe_prop s ∧ nonempty_prop s

/-! ## Property-based tests -/

/-- A pool of test inputs (safe, unsafe, and edge-case strings). -/
def pbtInputs : List String :=
  ["", "a", "Z", "0", "abc", "ABC", "xyz_123", "a-b_c@d%e+f=g:h,i.j/k",
   "a b c", "a'b", "'", "''", "a b'c", "hello world", "user@example.com",
   "/usr/bin/ls", "--flag", "-", "100%", "a#b", "~user", "a;b", "a|b",
   "$(rm -rf /)", "quote'me", "..", "/", " mixed", "trailing ", "a\tb"]

-- PBT (bounded): the empty string is quoted as `''`
example : pbtInputs.all (fun s => if s == "" then quote s == "''" else true) = true := by
  native_decide

-- PBT (bounded): safe strings are returned unchanged
example : pbtInputs.all (fun s =>
    if (s != "") && (s.toList.all isSafeChar) then quote s == s else true) = true := by
  native_decide

-- PBT (bounded): unsafe strings are wrapped in single quotes
example : pbtInputs.all (fun s =>
    if s.toList.all isSafeChar then true
    else (quote s).startsWith "'" && (quote s).endsWith "'") = true := by
  native_decide

-- PBT (bounded): the output is never empty
example : pbtInputs.all (fun s => !(quote s).isEmpty) = true := by native_decide

-- PBT (bounded): full post-condition in executable form
example : pbtInputs.all (fun s =>
    (if s == "" then quote s == "''" else true)
    && (if (s != "") && (s.toList.all isSafeChar) then quote s == s else true)
    && (if s.toList.all isSafeChar then true
        else (quote s).startsWith "'" && (quote s).endsWith "'")
    && !(quote s).isEmpty) = true := by
  native_decide

-- PBT (randomized): safe strings are unchanged
#eval Plausible.Testable.check (∀ s : String,
  s ≠ "" → s.toList.all isSafeChar = true → quote s = s)

-- PBT (randomized): the output is never empty
#eval Plausible.Testable.check (∀ s : String, (quote s).isEmpty = false)

-- PBT (randomized): unsafe strings are wrapped in single quotes
#eval Plausible.Testable.check (∀ s : String,
  s.toList.all isSafeChar = false →
    (quote s).startsWith "'" = true ∧ (quote s).endsWith "'" = true)

/-! ## Correctness theorem: Pre → Post -/

theorem quote_correct (s : String) (_hpre : Pre s) : Post_prop s :=
  ⟨empty_thm, safe_thm s, unsafe_thm s, nonempty_thm s⟩

/-! ## Imperative implementation (`Id` monad with mutable state) -/

/-- Imperative scan: are all characters safe? -/
def scanSafe (l : List Char) : Bool := Id.run do
  let mut safe := true
  for c in l do
    if !isSafeChar c then safe := false
  return safe

/-- Imperative escaping loop. -/
def escapeImp (l : List Char) : List Char := Id.run do
  let mut out : List Char := []
  for c in l do
    out := out ++ escChar c
  return out

/-- Imperative implementation of `shlex.quote`. -/
def quoteImp (s : String) : String := Id.run do
  let mut result : String := ""
  if s.toList.isEmpty then
    result := "''"
  else if scanSafe s.toList then
    result := s
  else
    result := "'" ++ (escapeImp s.toList).asString ++ "'"
  return result

/-! ## Imperative tests -/

example : quoteImp "" = "''" := by native_decide
example : quoteImp "abc" = "abc" := by native_decide
example : quoteImp "a b c" = "'a b c'" := by native_decide
example : quoteImp "a'b" = "'a'\"'\"'b'" := by native_decide

#eval quoteImp "a'b"
#eval quoteImp "hello world"

/-! ## Equivalence of functional and imperative implementations -/

theorem scanSafe_gen (l : List Char) (b : Bool) :
    (Id.run do
      let mut safe := b
      for c in l do
        if !isSafeChar c then safe := false
      return safe) = (b && l.all isSafeChar) := by
  induction l generalizing b with
  | nil => simp
  | cons c cs ih =>
    rw [List.all_cons]
    by_cases h : isSafeChar c = true
    · have h1 : (Id.run do
          let mut safe := b
          for x in c :: cs do
            if !isSafeChar x then safe := false
          return safe)
        = (Id.run do
          let mut safe := b
          for x in cs do
            if !isSafeChar x then safe := false
          return safe) := by
        simp [h, forIn]
      rw [h1, ih, h]
      simp
    · simp only [Bool.not_eq_true] at h
      have h1 : (Id.run do
          let mut safe := b
          for x in c :: cs do
            if !isSafeChar x then safe := false
          return safe)
        = (Id.run do
          let mut safe := false
          for x in cs do
            if !isSafeChar x then safe := false
          return safe) := by
        simp [h, forIn]
      rw [h1, ih]
      simp [h]

theorem scanSafe_eq (l : List Char) : scanSafe l = l.all isSafeChar := by
  have h := scanSafe_gen l true
  simp only [Bool.true_and] at h
  exact h

theorem escapeImp_gen (l : List Char) (acc : List Char) :
    (Id.run do
      let mut out := acc
      for c in l do
        out := out ++ escChar c
      return out) = acc ++ escape l := by
  induction l generalizing acc with
  | nil => show acc = acc ++ []; simp
  | cons c cs ih =>
    have h1 : (Id.run do
          let mut out := acc
          for x in c :: cs do
            out := out ++ escChar x
          return out)
        = (Id.run do
          let mut out := acc ++ escChar c
          for x in cs do
            out := out ++ escChar x
          return out) := by
      simp only [forIn, List.forIn'_cons, Id.run_bind, Id.run_pure]
    rw [h1, ih]
    rw [show escape (c :: cs) = escChar c ++ escape cs from rfl, ← List.append_assoc]

theorem escapeImp_eq (l : List Char) : escapeImp l = escape l := by
  have h := escapeImp_gen l []
  simp only [List.nil_append] at h
  exact h

theorem quoteImp_eq (s : String) : quoteImp s = quote s := by
  obtain ⟨cs⟩ := s
  show (if cs.isEmpty then "''" else if scanSafe cs then String.mk cs
        else "'" ++ (escapeImp cs).asString ++ "'") = (quoteList cs).asString
  by_cases h1 : cs.isEmpty = true
  · rw [if_pos h1]
    cases cs with
    | nil => rfl
    | cons c cs' => simp [List.isEmpty] at h1
  · rw [if_neg h1]
    by_cases h2 : scanSafe cs = true
    · rw [if_pos h2]
      rw [scanSafe_eq] at h2
      cases cs with
      | nil => simp [List.isEmpty] at h1
      | cons c cs' =>
        rw [quoteList_safe (c :: cs') (by simp) h2]
        rfl
    · rw [if_neg h2]
      simp only [Bool.not_eq_true] at h2
      rw [scanSafe_eq] at h2
      rw [escapeImp_eq, quoteList_unsafe cs h2]
      rfl

/-- The functional and imperative implementations coincide. -/
theorem quote_eq_quoteImp (s : String) : quote s = quoteImp s := (quoteImp_eq s).symm

end «21_shlex_quote»
