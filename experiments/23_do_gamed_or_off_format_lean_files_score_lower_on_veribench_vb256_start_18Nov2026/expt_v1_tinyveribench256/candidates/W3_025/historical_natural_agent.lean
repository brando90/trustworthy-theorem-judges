import Mathlib
namespace Agent

/-!
# Safe format-string logger

Translation of the Python `safe_format_string_leak` function. The template is
intentionally ignored: acceptance depends only on whether the user input has a
literal percent character. Thus even a lone `%` or an escaped-looking `%%` is
rejected, while a percent character in the template is harmless to this check.

The specification covers all strings (including empty and Unicode strings).
We prove exact acceptance/rejection, template independence, and compositional
behavior under concatenation. Bounded exhaustive tests exercise each property
and the full postcondition, independently of the general kernel-checked proofs.
-/

namespace UnsafeFormatStringLeakSafe

/-- The template is not interpolated or examined, just as in the Python source. -/
def safe_format_string_leak (_template user_input : String) : Bool :=
  !user_input.contains '%'

-- The five assertions from Python's `check`.
example : safe_format_string_leak "log: %s" "hello world" = true := by native_decide
example : safe_format_string_leak "log: %s" "user_name" = true := by native_decide
example : safe_format_string_leak "log: %s" "%x %x %x %s" = false := by native_decide
example : safe_format_string_leak "log: %s" "%n" = false := by native_decide
example : safe_format_string_leak "log: %s" "hello %s world" = false := by native_decide

-- Boundary cases: all percent characters are rejected, not only valid specifiers.
example : safe_format_string_leak "%n" "" = true := by native_decide
example : safe_format_string_leak "" "%" = false := by native_decide
example : safe_format_string_leak "" "%%" = false := by native_decide
example : safe_format_string_leak "log: %s" "café λ" = true := by native_decide
example : safe_format_string_leak "" "λ%é" = false := by native_decide

#eval safe_format_string_leak "log: %s" "hello world"
#eval safe_format_string_leak "log: %s" "user_name"
#eval safe_format_string_leak "log: %s" "%x %x %x %s"
#eval safe_format_string_leak "log: %s" "%n"
#eval safe_format_string_leak "log: %s" "hello %s world"

/-- Python imposes no restrictions on either string argument. -/
def Pre (_template _user_input : String) : Prop := True

/-- Exactly the percent-free inputs are accepted (both soundness and completeness). -/
def acceptance_prop (template user_input : String) : Prop :=
  safe_format_string_leak template user_input = true ↔ '%' ∉ user_input.toList

theorem acceptance_thm (template user_input : String) :
    acceptance_prop template user_input := by
  simp [acceptance_prop, safe_format_string_leak, String.contains, String.any_eq]
  constructor
  · intro h hmem
    exact h '%' hmem rfl
  · intro h x hx heq
    exact h (heq ▸ hx)

/-- A percent anywhere, regardless of what follows it, is rejected. -/
def rejection_prop (template user_input : String) : Prop :=
  safe_format_string_leak template user_input = false ↔ '%' ∈ user_input.toList

theorem rejection_thm (template user_input : String) :
    rejection_prop template user_input := by
  simp [rejection_prop, safe_format_string_leak, String.contains, String.any_eq]

/-- Changing the template cannot change the answer. -/
def template_independent_prop (template user_input : String) : Prop :=
  ∀ otherTemplate : String,
    safe_format_string_leak template user_input =
      safe_format_string_leak otherTemplate user_input

theorem template_independent_thm (template user_input : String) :
    template_independent_prop template user_input := by
  intro otherTemplate
  rfl

/-- A concatenation is safe exactly when both constituent inputs are safe. -/
def concatenation_prop (template user_input : String) : Prop :=
  ∀ suffix : String,
    safe_format_string_leak template (user_input ++ suffix) =
      (safe_format_string_leak template user_input &&
        safe_format_string_leak template suffix)

theorem concatenation_thm (template user_input : String) :
    concatenation_prop template user_input := by
  intro suffix
  simp [safe_format_string_leak, String.contains, String.any_eq]

/-- The complete contract of the check, with no input-domain restrictions. -/
def Post_prop (template user_input : String) : Prop :=
  acceptance_prop template user_input ∧
  rejection_prop template user_input ∧
  template_independent_prop template user_input ∧
  concatenation_prop template user_input

/-! ## Property-based tests

Exhaustively generate all strings of length at most three over a five-character
alphabet. It includes `%`, ordinary letters used in specifiers, and a Unicode
character. The checks use independently executable list membership for the
specification, rather than relying on decidability of universally quantified
`Prop` definitions. Every `_prop`, including `Post_prop`, has its own test below.
-/

def testAlphabet : List Char := ['a', '%', 's', 'n', 'λ']

def boundedInputs : Nat → List String
  | 0 => [""]
  | n + 1 => "" :: (boundedInputs n).flatMap (fun s =>
      testAlphabet.map (fun c => String.singleton c ++ s))

def testInputs : List String := boundedInputs 3

def testTemplates : List String := ["", "log: %s", "%n", "λ: %%", "plain"]

-- PBT for acceptance_prop: the accepted inputs are exactly the percent-free ones.
example : (testTemplates.all (fun t => testInputs.all (fun s =>
    (safe_format_string_leak t s == true) ==
      decide ('%' ∉ s.toList)))) = true := by native_decide

-- PBT for rejection_prop: every occurrence of percent, at every position, rejects.
example : (testTemplates.all (fun t => testInputs.all (fun s =>
    (safe_format_string_leak t s == false) ==
      decide ('%' ∈ s.toList)))) = true := by native_decide

-- PBT for template_independent_prop, varying both templates independently.
example : (testTemplates.all (fun t => testInputs.all (fun s =>
    testTemplates.all (fun other =>
      safe_format_string_leak t s == safe_format_string_leak other s)))) = true :=
  by native_decide

-- PBT for concatenation_prop over every pair of bounded input strings.
example : (testTemplates.all (fun t => testInputs.all (fun s =>
    testInputs.all (fun suffix =>
      safe_format_string_leak t (s ++ suffix) ==
        (safe_format_string_leak t s && safe_format_string_leak t suffix))))) = true :=
  by native_decide

/-- Executable bounded instance of all four conjuncts of `Post_prop`. -/
def postCheck (template user_input : String) : Bool :=
  (((safe_format_string_leak template user_input == true) ==
      decide ('%' ∉ user_input.toList)) &&
   ((safe_format_string_leak template user_input == false) ==
      decide ('%' ∈ user_input.toList))) &&
  (testTemplates.all (fun other =>
    safe_format_string_leak template user_input ==
      safe_format_string_leak other user_input)) &&
  (testInputs.all (fun suffix =>
    safe_format_string_leak template (user_input ++ suffix) ==
      (safe_format_string_leak template user_input &&
       safe_format_string_leak template suffix)))

-- PBT for Post_prop: test all conjuncts jointly for each admissible input.
example : (testTemplates.all (fun t => testInputs.all (postCheck t))) = true :=
  by native_decide

#eval testInputs.length
#eval testTemplates.all (fun t => testInputs.all (postCheck t))

/-- Every pair of strings satisfies the complete contract. -/
theorem correctness_thm (template user_input : String) :
    Pre template user_input → Post_prop template user_input := by
  intro _
  exact ⟨acceptance_thm template user_input,
    rejection_thm template user_input,
    template_independent_thm template user_input,
    concatenation_thm template user_input⟩

/-! ## Imperative translation -/

/-- A mutable acceptance flag is cleared when a percent character is present. -/
def safe_format_string_leak_imperative (_template user_input : String) : Bool := Id.run do
  let mut accepted := true
  if user_input.contains '%' then
    accepted := false
  return accepted

example : safe_format_string_leak_imperative "log: %s" "hello world" = true := by
  native_decide
example : safe_format_string_leak_imperative "log: %s" "user_name" = true := by
  native_decide
example : safe_format_string_leak_imperative "log: %s" "%x %x %x %s" = false := by
  native_decide
example : safe_format_string_leak_imperative "log: %s" "%n" = false := by
  native_decide
example : safe_format_string_leak_imperative "log: %s" "hello %s world" = false := by
  native_decide
example : safe_format_string_leak_imperative "%n" "" = true := by native_decide
example : safe_format_string_leak_imperative "" "%%" = false := by native_decide

#eval safe_format_string_leak_imperative "log: %s" "hello world"
#eval safe_format_string_leak_imperative "log: %s" "%x %x %x %s"

-- Bounded equivalence test, in addition to the universal proof below.
example : (testTemplates.all (fun t => testInputs.all (fun s =>
    safe_format_string_leak t s == safe_format_string_leak_imperative t s))) = true :=
  by native_decide

/-- Kernel-checked equivalence for all templates and all user inputs. -/
theorem functional_imperative_equivalence_thm (template user_input : String) :
    safe_format_string_leak template user_input =
      safe_format_string_leak_imperative template user_input := by
  cases h : user_input.contains '%' <;>
    simp [safe_format_string_leak, safe_format_string_leak_imperative, h]

end UnsafeFormatStringLeakSafe
end Agent
