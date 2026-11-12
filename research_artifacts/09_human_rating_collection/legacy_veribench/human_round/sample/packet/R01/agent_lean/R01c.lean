import Mathlib

/-!
# POSIX shell quoting

This file formalizes the string-valued part of Python's `shlex.quote`.  The
Python precondition that the dynamically typed input is a string is represented
by the argument type `String`; `Pre` records that precondition explicitly for
the benchmark specification.
-/

namespace ShlexQuote

/-- The characters which may occur without shell quoting. -/
def safeChars : String :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_@%+=:,./-"

/-- Decide whether a character is safe in an unquoted POSIX shell word. -/
def isSafe (c : Char) : Bool := safeChars.contains c

/-- A direct functional rendition of `shlex.quote`. -/
def quote (s : String) : String :=
  if s = "" then
    "''"
  else if s.all isSafe then
    s
  else
    "'" ++ s.replace "'" "'\"'\"'" ++ "'"

example : quote "" = "''" := by native_decide
example : quote "abc" = "abc" := by native_decide
example : quote "a b c" = "'a b c'" := by native_decide
example : quote "a'b" = "'a'\"'\"'b'" := by native_decide

#eval quote ""
#eval quote "abc"
#eval quote "a b c"
#eval quote "a'b"

/-- Lean accepts precisely string inputs, which captures `pre_quote`. -/
def Pre (_s : String) : Prop := True

/-- Quoting the empty string produces a nonempty pair of single quotes. -/
def empty_prop : Prop := quote "" = "''"

theorem empty_thm : empty_prop := by
  unfold empty_prop
  native_decide

/-- A nonempty word consisting only of safe characters is unchanged. -/
def safe_prop (s : String) : Prop :=
  s ≠ "" → s.all isSafe = true → quote s = s

theorem safe_thm (s : String) : safe_prop s := by
  intro hne hs
  simp [quote, hne, hs]

/-- Every nonempty word containing an unsafe character is single-quoted, with
embedded single quotes changed to the standard shell sequence `'"'"'`. -/
def unsafe_prop (s : String) : Prop :=
  s ≠ "" → s.all isSafe = false →
    quote s = "'" ++ s.replace "'" "'\"'\"'" ++ "'"

theorem unsafe_thm (s : String) : unsafe_prop s := by
  intro hne hs
  simp [quote, hne, hs]

/-- Complete branch-by-branch postcondition of `quote`. -/
def Post_prop (s result : String) : Prop :=
  result = quote s ∧
  (s = "" → result = "''") ∧
  (s ≠ "" → s.all isSafe = true → result = s) ∧
  (s ≠ "" → s.all isSafe = false →
    result = "'" ++ s.replace "'" "'\"'\"'" ++ "'")

/-- The functional implementation meets its full postcondition. -/
theorem quote_correct (s : String) : Pre s → Post_prop s (quote s) := by
  intro _
  refine ⟨rfl, ?_, safe_thm s, unsafe_thm s⟩
  intro hs
  subst s
  exact empty_thm

/-- An imperative rendition using mutable state in the identity monad. -/
def quoteImperative (s : String) : String := Id.run do
  let mut result := s
  if s = "" then
    result := "''"
  else if s.all isSafe then
    result := s
  else
    result := "'" ++ s.replace "'" "'\"'\"'" ++ "'"
  return result

example : quoteImperative "" = "''" := by native_decide
example : quoteImperative "abc" = "abc" := by native_decide
example : quoteImperative "a b c" = "'a b c'" := by native_decide
example : quoteImperative "a'b" = "'a'\"'\"'b'" := by native_decide

#eval quoteImperative ""
#eval quoteImperative "abc"
#eval quoteImperative "a b c"
#eval quoteImperative "a'b"

/-- The functional and imperative renditions agree on every input. -/
theorem quote_equiv (s : String) : quote s = quoteImperative s := by
  by_cases hempty : s = ""
  · simp [quote, quoteImperative, hempty]
  · by_cases hsafe : s.all isSafe = true
    · simp [quote, quoteImperative, hempty, hsafe]
    · simp [quote, quoteImperative, hempty, hsafe]

end ShlexQuote
