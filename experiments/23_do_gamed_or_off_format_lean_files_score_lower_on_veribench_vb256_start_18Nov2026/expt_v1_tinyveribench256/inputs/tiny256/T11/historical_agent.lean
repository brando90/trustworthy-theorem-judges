import Mathlib
namespace Agent

/-!
# Safe reflected error-path check

Translation of Python's `safe_reflected_error`. A path is accepted exactly when
it contains none of `<`, `>`, `"`, `'`, and `&`. This is a rejection check, not an
HTML-escaping routine: even an already escaped entity containing `&` is rejected.
All Lean strings are admissible, including empty strings and Unicode strings.
-/

namespace UnsafeReflectedErrorSafe

/-- The five characters checked by the Python program, in its original order. -/
def dangerous : List Char := ['<', '>', '"', '\'', '&']

/-- Functional translation of `not any(c in req_path for c in dangerous)`. -/
def safe_reflected_error (req_path : String) : Bool :=
  !(dangerous.any fun c => req_path.toList.contains c)

-- The five tests in the Python source.
example : safe_reflected_error "/normal/page" = true := by native_decide
example : safe_reflected_error "/foo/bar" = true := by native_decide
example : safe_reflected_error "<script>alert(1)</script>" = false := by native_decide
example : safe_reflected_error "/foo?x=<img src=x>" = false := by native_decide
example : safe_reflected_error "foo&bar" = false := by native_decide

-- Boundary cases, the other two metacharacters, and Unicode.
example : safe_reflected_error "" = true := by native_decide
example : safe_reflected_error "/a\"b" = false := by native_decide
example : safe_reflected_error "/a'b" = false := by native_decide
example : safe_reflected_error "/&lt;script&gt;" = false := by native_decide
example : safe_reflected_error "/日本語/é/🙂" = true := by native_decide

#eval safe_reflected_error "/normal/page"
#eval safe_reflected_error "<script>alert(1)</script>"

/-- Python imposes no additional precondition on its string argument. -/
def Pre (_req_path : String) : Prop := True

/-- Acceptance is exactly the absence of each of the five HTML metacharacters. -/
def acceptance_prop (req_path : String) (result : Bool) : Prop :=
  result = true ↔
    '<' ∉ req_path.toList ∧ '>' ∉ req_path.toList ∧
    '"' ∉ req_path.toList ∧ '\'' ∉ req_path.toList ∧ '&' ∉ req_path.toList

theorem acceptance_thm (req_path : String) :
    acceptance_prop req_path (safe_reflected_error req_path) := by
  simp [acceptance_prop, safe_reflected_error, dangerous]

/-- Rejection is exactly the presence of a forbidden character, with a witness. -/
def rejection_prop (req_path : String) (result : Bool) : Prop :=
  result = false ↔ ∃ c ∈ dangerous, c ∈ req_path.toList

theorem rejection_thm (req_path : String) :
    rejection_prop req_path (safe_reflected_error req_path) := by
  simp [rejection_prop, safe_reflected_error]

/-- Concatenation is safe precisely when both constituent strings are safe. -/
def append_prop (left right : String) : Prop :=
  safe_reflected_error (left ++ right) =
    (safe_reflected_error left && safe_reflected_error right)

theorem append_thm (left right : String) : append_prop left right := by
  unfold append_prop
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true]
  have hcat := acceptance_thm (left ++ right)
  have hleft := acceptance_thm left
  have hright := acceptance_thm right
  unfold acceptance_prop at hcat hleft hright
  rw [hcat, hleft, hright]
  simp only [String.toList, String.data_append, List.mem_append, not_or]
  tauto

/-- Complete input/output specification: exact acceptance and exact rejection. -/
def Post_prop (req_path : String) (result : Bool) : Prop :=
  acceptance_prop req_path result ∧ rejection_prop req_path result

/-!
## Bounded property-based tests

`testWords n` enumerates every word of length at most `n` over `testAlphabet`.
The alphabet includes all five forbidden characters and ordinary, newline, and
Unicode characters. In particular, the tests exercise metacharacters at every
position, repetitions, mixed safe/unsafe paths, and the empty string.
The executable oracles scan the input's characters, independently of the
implementation's scan of the five-character forbidden list.
-/

def testAlphabet : List Char :=
  ['<', '>', '"', '\'', '&', '/', 'a', '?', '\n', 'é', '🙂']

def testWords : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: testAlphabet.flatMap (fun c => (testWords n).map (c :: ·))

def testPaths (maxLength : Nat) : List String :=
  (testWords maxLength).map String.mk

/-- Executable form of the acceptance condition. -/
def literalSafe (s : String) : Bool :=
  s.toList.all fun c =>
    c != '<' && c != '>' && c != '"' && c != '\'' && c != '&'

/-- Executable form of the forbidden-character witness condition. -/
def literalUnsafe (s : String) : Bool :=
  s.toList.any fun c =>
    c == '<' || c == '>' || c == '"' || c == '\'' || c == '&'

-- PBT for acceptance_prop: exhaustive length ≤ 3 (1,464 strings).
example : (testPaths 3).all (fun s =>
    safe_reflected_error s == literalSafe s) = true := by native_decide

-- PBT for rejection_prop, using the complementary result and a witness search.
example : (testPaths 3).all (fun s =>
    (!safe_reflected_error s) == literalUnsafe s) = true := by native_decide

-- PBT for append_prop: all 17,689 pairs of strings of length ≤ 2.
example : (testPaths 2).all (fun a => (testPaths 2).all (fun b =>
    safe_reflected_error (a ++ b) ==
      (safe_reflected_error a && safe_reflected_error b))) = true := by native_decide

-- PBT for the entire Post_prop conjunction, not just one of its components.
example : (testPaths 3).all (fun s =>
    let result := safe_reflected_error s
    (result == literalSafe s) && ((!result) == literalUnsafe s)) = true := by
  native_decide

#eval ((testPaths 3).length, (testPaths 3).all (fun s =>
  (safe_reflected_error s == literalSafe s) &&
  ((!safe_reflected_error s) == literalUnsafe s)))

/-- The Python contract holds for every admissible string. -/
theorem correctness_thm (req_path : String) :
    Pre req_path → Post_prop req_path (safe_reflected_error req_path) := by
  intro _
  exact ⟨acceptance_thm req_path, rejection_thm req_path⟩

/--
Imperative translation using a mutable accumulator. Evaluating all five pure
membership checks instead of short-circuiting does not change the result.
-/
def safe_reflected_error_imperative (req_path : String) : Bool := Id.run do
  let mut found := false
  for c in dangerous do
    found := found || req_path.toList.contains c
  return !found

-- Imperative versions of all five source tests, plus boundary/quote tests.
example : safe_reflected_error_imperative "/normal/page" = true := by native_decide
example : safe_reflected_error_imperative "/foo/bar" = true := by native_decide
example : safe_reflected_error_imperative "<script>alert(1)</script>" = false := by
  native_decide
example : safe_reflected_error_imperative "/foo?x=<img src=x>" = false := by native_decide
example : safe_reflected_error_imperative "foo&bar" = false := by native_decide
example : safe_reflected_error_imperative "" = true := by native_decide
example : safe_reflected_error_imperative "/a\"b" = false := by native_decide
example : safe_reflected_error_imperative "/a'b" = false := by native_decide

#eval safe_reflected_error_imperative "/normal/page"
#eval safe_reflected_error_imperative "<script>alert(1)</script>"

-- Additional bounded differential testing of the two implementations.
example : (testPaths 3).all (fun s =>
    safe_reflected_error s == safe_reflected_error_imperative s) = true := by
  native_decide

/-- Pointwise functional/imperative equivalence for every string, without Pre. -/
theorem equivalence_thm (req_path : String) :
    safe_reflected_error req_path = safe_reflected_error_imperative req_path := by
  simp [safe_reflected_error, safe_reflected_error_imperative, dangerous,
    List.any_cons, Bool.or_assoc]

end UnsafeReflectedErrorSafe
end Agent
