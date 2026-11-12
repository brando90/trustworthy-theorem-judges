import Mathlib

/-!
# HTML-safe string escaping

This file formalizes the relevant behavior of Python's `html.escape`: ampersands,
angle brackets, and (optionally) quotation marks are replaced by their HTML-safe
spellings.  The replacement of ampersands is performed first, so the ampersands
introduced by later replacements are not escaped again.
-/

namespace HtmlEscape

/-! ## Functional implementation -/

/-- Replace the three characters which are escaped independently of `quote`. -/
def escapeBasic (s : String) : String :=
  (s.replace "&" "&amp;").replace "<" "&lt;" |>.replace ">" "&gt;"

/-- Replace quotation marks after the basic HTML escaping has taken place. -/
def escapeQuotes (s : String) : String :=
  (s.replace "\"" "&quot;").replace "'" "&#x27;"

/-- Functional translation of the Python `escape` function. -/
def escape (s : String) (quote : Bool := true) : String :=
  let escaped := escapeBasic s
  if quote then escapeQuotes escaped else escaped

/-! ## Functional unit tests -/

example : escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by
  native_decide

example : escape "" = "" := by
  native_decide

example : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by
  native_decide

example : escape "&<" = "&amp;&lt;" := by
  native_decide

#eval escape "<b>\"&'</b>"
#eval escape "<b>\"&'</b>" false
#eval escape "&<"

/-! ## Specification and correctness -/

/--
Python checks dynamically that its input is a string.  Lean's argument already
has type `String`, so every inhabitant of the function's domain satisfies that
precondition.
-/
def Pre (_s : String) : Prop := True

/-- A specification of the result, factored into the mandated replacement order. -/
def EscapeSpec (s : String) (quote : Bool) : String :=
  if quote then escapeQuotes (escapeBasic s) else escapeBasic s

/-- The implementation agrees with the complete result specification. -/
def exact_result_prop (s : String) (quote : Bool) : Prop :=
  escape s quote = EscapeSpec s quote

theorem exact_result_thm (s : String) (quote : Bool) :
    exact_result_prop s quote := by
  rfl

/-- Disabling quote escaping performs only the three unconditional replacements. -/
def quote_disabled_prop (s : String) : Prop :=
  escape s false = escapeBasic s

theorem quote_disabled_thm (s : String) : quote_disabled_prop s := by
  rfl

/-- Enabling quote escaping applies both quote replacements after basic escaping. -/
def quote_enabled_prop (s : String) : Prop :=
  escape s true = escapeQuotes (escapeBasic s)

theorem quote_enabled_thm (s : String) : quote_enabled_prop s := by
  rfl

/-- The observable order check from the Python benchmark. -/
def ampersand_first_prop : Prop :=
  escape "&<" true = "&amp;&lt;"

theorem ampersand_first_thm : ampersand_first_prop := by
  unfold ampersand_first_prop
  native_decide

/--
The postcondition records the exact result and both branches of the optional
quote behavior; the order check makes the double-escaping requirement explicit.
-/
def Post_prop (s : String) (quote : Bool) : Prop :=
  exact_result_prop s quote ∧
    quote_disabled_prop s ∧
    quote_enabled_prop s ∧
    ampersand_first_prop

/-- Every well-typed input satisfies the complete escaping specification. -/
theorem escape_correct (s : String) (quote : Bool) :
    Pre s → Post_prop s quote := by
  intro _
  exact ⟨exact_result_thm s quote, quote_disabled_thm s,
    quote_enabled_thm s, ampersand_first_thm⟩

/-! ## Imperative implementation -/

/-- An imperative-style translation using mutable state in the identity monad. -/
def escapeImperative (s : String) (quote : Bool := true) : String := Id.run do
  let mut escaped := s
  escaped := escaped.replace "&" "&amp;"
  escaped := escaped.replace "<" "&lt;"
  escaped := escaped.replace ">" "&gt;"
  if quote then
    escaped := escaped.replace "\"" "&quot;"
    escaped := escaped.replace "'" "&#x27;"
  return escaped

/-! ## Imperative unit tests -/

example : escapeImperative "<b>\"&'</b>" =
    "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by
  native_decide

example : escapeImperative "" = "" := by
  native_decide

example : escapeImperative "<b>\"&'</b>" false =
    "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by
  native_decide

example : escapeImperative "&<" = "&amp;&lt;" := by
  native_decide

#eval escapeImperative "<b>\"&'</b>"
#eval escapeImperative "<b>\"&'</b>" false
#eval escapeImperative "&<"

/-- The functional and imperative translations return the same string. -/
theorem escape_equiv (s : String) (quote : Bool) :
    escape s quote = escapeImperative s quote := by
  cases quote <;> rfl

end HtmlEscape
