import Mathlib
namespace Agent

/-!
# HumanEval 29: filter_by_prefix

A translation of the Python list comprehension `[x for x in strings if
x.startswith(prefix)]`. Strings are treated as sequences of Unicode characters;
prefix matching is exact and case-sensitive, with no normalization. Filtering
preserves order and every occurrence of each matching string. The empty prefix
matches every string, including the empty string. There are no preconditions.

The specification includes membership in both directions, stable order,
multiplicity, a length bound, the empty-prefix law, and idempotence. Bounded
property-based tests check all lists of length at most three over a small string
alphabet, supplemented with the public examples and additional Unicode cases.
All named theorem proofs are kernel-checked; native_decide is used only in tests.
-/

namespace humaneval_29_filter_by_prefix

/-- Python's `s.startswith(prefix)`, expressed on Unicode character lists. -/
def startsWith (s pre : String) : Bool :=
  pre.toList.isPrefixOf s.toList

/-- The functional translation: a stable filter, not a set operation. -/
def filter_by_prefix (strings : List String) (pre : String) : List String :=
  strings.filter (fun s => startsWith s pre)

-- Unit tests: both docstring examples and both assertions in `check`.
example : filter_by_prefix [] "a" = [] := by native_decide
example : filter_by_prefix ["abc", "bcd", "cde", "array"] "a" =
    ["abc", "array"] := by native_decide
example : filter_by_prefix [] "john" = [] := by native_decide
example : filter_by_prefix ["xxx", "asd", "xxy", "john doe", "xxxAAA", "xxx"] "xxx" =
    ["xxx", "xxxAAA", "xxx"] := by native_decide
example : filter_by_prefix ["", "a", "a", "é", "🙂"] "" =
    ["", "a", "a", "é", "🙂"] := by native_decide
example : filter_by_prefix ["", "a", "ab", "abc"] "abcd" = [] := by native_decide
example : filter_by_prefix ["é", "éclair", "e", "É", "éclair"] "é" =
    ["é", "éclair", "éclair"] := by native_decide
example : filter_by_prefix ["🙂", "🙂a", "a🙂", ""] "🙂" =
    ["🙂", "🙂a"] := by native_decide
#eval filter_by_prefix ["abc", "bcd", "cde", "array"] "a"
#eval filter_by_prefix ["xxx", "asd", "xxy", "john doe", "xxxAAA", "xxx"] "xxx"

/-- Every finite list of strings and every prefix is admissible. -/
def Pre (_strings : List String) (_prefix : String) : Prop := True

/-- The executable predicate means that the prefix is an initial character segment. -/
def prefix_semantics_prop (s pre : String) : Prop :=
  startsWith s pre = true ↔ pre.toList <+: s.toList

theorem prefix_semantics_thm (s pre : String) : prefix_semantics_prop s pre := by
  exact List.isPrefixOf_iff_prefix

/-- No new strings appear, and every returned string has the requested prefix. -/
def soundness_prop (strings : List String) (pre : String) (result : List String) : Prop :=
  ∀ s ∈ result, s ∈ strings ∧ pre.toList <+: s.toList

theorem soundness_thm (strings : List String) (pre : String) :
    soundness_prop strings pre (filter_by_prefix strings pre) := by
  intro s hs
  obtain ⟨hin, hp⟩ := List.mem_filter.mp hs
  exact ⟨hin, (prefix_semantics_thm s pre).mp hp⟩

/-- Every matching input string is returned. -/
def completeness_prop (strings : List String) (pre : String) (result : List String) : Prop :=
  ∀ s ∈ strings, pre.toList <+: s.toList → s ∈ result

theorem completeness_thm (strings : List String) (pre : String) :
    completeness_prop strings pre (filter_by_prefix strings pre) := by
  intro s hin hp
  exact List.mem_filter.mpr ⟨hin, (prefix_semantics_thm s pre).mpr hp⟩

/-- The result is a subsequence of the input, so the input order is retained. -/
def order_prop (strings : List String) (result : List String) : Prop :=
  result.Sublist strings

theorem order_thm (strings : List String) (pre : String) :
    order_prop strings (filter_by_prefix strings pre) := by
  exact List.filter_sublist

/-- Every occurrence is kept exactly when it matches; duplicates are not removed. -/
def multiplicity_prop (strings : List String) (pre : String) (result : List String) : Prop :=
  ∀ s, result.count s = if startsWith s pre then strings.count s else 0

theorem multiplicity_thm (strings : List String) (pre : String) :
    multiplicity_prop strings pre (filter_by_prefix strings pre) := by
  intro s
  by_cases h : startsWith s pre = true
  · simp [filter_by_prefix, h]
  · have hn : s ∉ filter_by_prefix strings pre := by
      intro hs
      exact h (List.mem_filter.mp hs).2
    simp [h, List.count_eq_zero.mpr hn]

/-- Filtering never increases the number of strings. -/
def length_prop (strings result : List String) : Prop := result.length ≤ strings.length

theorem length_thm (strings : List String) (pre : String) :
    length_prop strings (filter_by_prefix strings pre) := by
  exact (order_thm strings pre).length_le

/-- The empty prefix returns the original list verbatim. -/
def empty_prefix_prop (strings : List String) (pre : String) (result : List String) : Prop :=
  pre = "" → result = strings

theorem empty_prefix_thm (strings : List String) (pre : String) :
    empty_prefix_prop strings pre (filter_by_prefix strings pre) := by
  intro hp
  subst pre
  simp [filter_by_prefix, startsWith]

/-- Once filtered, applying the same filter again changes nothing. -/
def idempotence_prop (pre : String) (result : List String) : Prop :=
  filter_by_prefix result pre = result

theorem idempotence_thm (strings : List String) (pre : String) :
    idempotence_prop pre (filter_by_prefix strings pre) := by
  simp [idempotence_prop, filter_by_prefix, List.filter_filter]

/-- The complete output contract, including order and duplicate preservation. -/
def Post_prop (strings : List String) (pre : String) (result : List String) : Prop :=
  soundness_prop strings pre result ∧
  completeness_prop strings pre result ∧
  order_prop strings result ∧
  multiplicity_prop strings pre result ∧
  length_prop strings result ∧
  empty_prefix_prop strings pre result ∧
  idempotence_prop pre result

/-! ## Bounded property-based tests

Enumerate all lists of length 0, 1, 2, or 3 over eight strings, including
empty, case-sensitive, and multi-byte strings. Extra inputs exercise longer
lists and longer matching prefixes. Each property has its own executable test.
For universally quantified membership/count properties, `strings ++ result`
is a complete finite support: all other strings have zero occurrences in both.
-/

def testAlphabet : List String := ["", "a", "ab", "b", "xxx", "é", "🙂", "A"]

def listsOfLength : Nat → List (List String)
  | 0 => [[]]
  | n + 1 => testAlphabet.flatMap (fun s => (listsOfLength n).map (s :: ·))

def testLists : List (List String) :=
  (List.range 4).flatMap listsOfLength ++
    [["abc", "bcd", "cde", "array"],
     ["xxx", "asd", "xxy", "john doe", "xxxAAA", "xxx"],
     ["é", "éclair", "e", "É", "éclair"], ["🙂", "🙂a", "a🙂", ""]]

def testPrefixes : List String :=
  testAlphabet ++ ["aa", "abc", "abcd", "john", "xxxAAA", "écl", "🙂a", "É"]

def boundedCheck (check : List String → String → Bool) : Bool :=
  testLists.all (fun xs => testPrefixes.all (check xs))

-- PBT for prefix_semantics_prop, using the independent take characterization.
def prefixSemanticsCheck : Bool :=
  testPrefixes.all (fun s => testPrefixes.all (fun p =>
    startsWith s p == (s.toList.take p.toList.length == p.toList)))
example : prefixSemanticsCheck = true := by native_decide
#eval prefixSemanticsCheck

/-- Executable soundness, using the character-prefix decision procedure. -/
def soundnessCheck (xs : List String) (p : String) (out : List String) : Bool :=
  out.all (fun s => xs.contains s && startsWith s p)

-- PBT for soundness_prop.
example : boundedCheck (fun xs p => soundnessCheck xs p (filter_by_prefix xs p)) = true := by
  native_decide
#eval boundedCheck (fun xs p => soundnessCheck xs p (filter_by_prefix xs p))

def completenessCheck (xs : List String) (p : String) (out : List String) : Bool :=
  xs.all (fun s => !startsWith s p || out.contains s)

-- PBT for completeness_prop.
example : boundedCheck (fun xs p => completenessCheck xs p (filter_by_prefix xs p)) = true := by
  native_decide
#eval boundedCheck (fun xs p => completenessCheck xs p (filter_by_prefix xs p))

def orderCheck (xs out : List String) : Bool := decide (out.Sublist xs)

-- PBT for order_prop.
example : boundedCheck (fun xs p => orderCheck xs (filter_by_prefix xs p)) = true := by
  native_decide
#eval boundedCheck (fun xs p => orderCheck xs (filter_by_prefix xs p))

def multiplicityCheck (xs : List String) (p : String) (out : List String) : Bool :=
  (xs ++ out).all (fun s => out.count s == (if startsWith s p then xs.count s else 0))

-- PBT for multiplicity_prop.
example : boundedCheck (fun xs p => multiplicityCheck xs p (filter_by_prefix xs p)) = true := by
  native_decide
#eval boundedCheck (fun xs p => multiplicityCheck xs p (filter_by_prefix xs p))

def lengthCheck (xs out : List String) : Bool := decide (out.length ≤ xs.length)

-- PBT for length_prop.
example : boundedCheck (fun xs p => lengthCheck xs (filter_by_prefix xs p)) = true := by
  native_decide
#eval boundedCheck (fun xs p => lengthCheck xs (filter_by_prefix xs p))

def emptyPrefixCheck (xs : List String) (p : String) (out : List String) : Bool :=
  p != "" || out == xs

-- PBT for empty_prefix_prop; the empty prefix is included for every test list.
example : boundedCheck (fun xs p => emptyPrefixCheck xs p (filter_by_prefix xs p)) = true := by
  native_decide
#eval boundedCheck (fun xs p => emptyPrefixCheck xs p (filter_by_prefix xs p))

def idempotenceCheck (p : String) (out : List String) : Bool :=
  filter_by_prefix out p == out

-- PBT for idempotence_prop.
example : boundedCheck (fun xs p => idempotenceCheck p (filter_by_prefix xs p)) = true := by
  native_decide
#eval boundedCheck (fun xs p => idempotenceCheck p (filter_by_prefix xs p))

def postCheck (xs : List String) (p : String) (out : List String) : Bool :=
  soundnessCheck xs p out && completenessCheck xs p out && orderCheck xs out &&
  multiplicityCheck xs p out && lengthCheck xs out && emptyPrefixCheck xs p out &&
  idempotenceCheck p out

-- PBT for the full Post_prop conjunction.
example : boundedCheck (fun xs p => postCheck xs p (filter_by_prefix xs p)) = true := by
  native_decide
#eval boundedCheck (fun xs p => postCheck xs p (filter_by_prefix xs p))

/-- Total correctness: all inputs satisfying Pre satisfy the full output contract. -/
theorem correctness_thm (strings : List String) (pre : String) :
    Pre strings pre → Post_prop strings pre (filter_by_prefix strings pre) := by
  intro _
  exact ⟨soundness_thm strings pre, completeness_thm strings pre,
    order_thm strings pre, multiplicity_thm strings pre,
    length_thm strings pre, empty_prefix_thm strings pre,
    idempotence_thm strings pre⟩

/-- A direct imperative version with a mutable result and a left-to-right loop. -/
def filter_by_prefix_imperative (strings : List String) (pre : String) : List String := Id.run do
  let mut result : List String := []
  for s in strings do
    if startsWith s pre then
      result := result ++ [s]
  return result

-- Imperative unit tests, including the original Python assertions.
example : filter_by_prefix_imperative [] "john" = [] := by native_decide
example : filter_by_prefix_imperative ["abc", "bcd", "cde", "array"] "a" =
    ["abc", "array"] := by native_decide
example : filter_by_prefix_imperative
    ["xxx", "asd", "xxy", "john doe", "xxxAAA", "xxx"] "xxx" =
    ["xxx", "xxxAAA", "xxx"] := by native_decide
example : filter_by_prefix_imperative ["", "a", "é", "🙂", "a"] "" =
    ["", "a", "é", "🙂", "a"] := by native_decide
example : filter_by_prefix_imperative ["é", "éclair", "e", "É", "éclair"] "é" =
    ["é", "éclair", "éclair"] := by native_decide
#eval filter_by_prefix_imperative ["abc", "bcd", "cde", "array"] "a"
#eval filter_by_prefix_imperative ["xxx", "asd", "xxy", "john doe", "xxxAAA", "xxx"] "xxx"
example : boundedCheck (fun xs p =>
    filter_by_prefix xs p == filter_by_prefix_imperative xs p) = true := by native_decide
#eval boundedCheck (fun xs p => filter_by_prefix xs p == filter_by_prefix_imperative xs p)

/-- Loop invariant: the processed result is followed by exactly the matches
from the remaining input. The accumulator is arbitrary, not necessarily empty. -/
private theorem loop_invariant (strings : List String) (pre : String) (acc : List String) :
    ((forIn strings acc (fun s r =>
      if startsWith s pre then pure (ForInStep.yield (r ++ [s]))
      else pure (ForInStep.yield r))) : Id (List String)).run =
      acc ++ filter_by_prefix strings pre := by
  induction strings generalizing acc with
  | nil => simp [filter_by_prefix]
  | cons s ss ih =>
    by_cases h : startsWith s pre = true <;>
      simp [List.forIn_cons, h, ih, filter_by_prefix, List.append_assoc]

/-- The mutable implementation is extensionally equal to the functional one. -/
theorem equivalence_thm (strings : List String) (pre : String) :
    filter_by_prefix strings pre = filter_by_prefix_imperative strings pre := by
  simpa [filter_by_prefix_imperative] using (loop_invariant strings pre []).symm

-- Audit the top-level proofs: native-decide tests are not proof dependencies.
#print axioms correctness_thm
#print axioms equivalence_thm

end humaneval_29_filter_by_prefix
end Agent
