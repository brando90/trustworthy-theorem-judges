import Mathlib
namespace Agent

/-!
# HumanEval 12: longest string

Return `none` for an empty list; otherwise return its first longest string.
Lengths count Unicode characters, as in Python's `len` on strings. The functional
implementation compares each head against the answer for its tail, retaining the
head on ties. A mutable right-to-left scan implements the same selection rule.
-/

namespace humaneval_12_longest

/-- Prepending a string to an already processed suffix: the new string wins ties. -/
def choose (s : String) (best : Option String) : Option String :=
  match best with
  | none => some s
  | some t => if t.length ≤ s.length then some s else some t

/-- The first longest string, or `none` for the empty list. -/
def longest : List String → Option String
  | [] => none
  | s :: ss => choose s (longest ss)

example : longest [] = none := by native_decide
example : longest ["a", "b", "c"] = some "a" := by native_decide
example : longest ["a", "bb", "ccc"] = some "ccc" := by native_decide
example : longest ["x", "y", "z"] = some "x" := by native_decide
example : longest ["x", "yyy", "zzzz", "www", "kkkk", "abc"] = some "zzzz" := by
  native_decide
example : longest ["", ""] = some "" := by native_decide
example : longest ["é", "🙂", "ab"] = some "ab" := by native_decide
#eval longest []
#eval longest ["a", "b", "c"]
#eval longest ["a", "bb", "ccc"]
#eval longest ["x", "yyy", "zzzz", "www", "kkkk", "abc"]

/-- Every list of strings is admissible. -/
def Pre (_strings : List String) : Prop := True

/-- `none` is returned exactly for an empty input. -/
def empty_prop (strings : List String) : Prop :=
  longest strings = none ↔ strings = []

theorem empty_thm (strings : List String) : empty_prop strings := by sorry

/-- A returned string comes from the input. -/
def membership_prop (strings : List String) : Prop :=
  ∀ s, longest strings = some s → s ∈ strings

theorem membership_thm (strings : List String) : membership_prop strings := by sorry

/-- No input string is longer than the returned string. -/
def maximal_prop (strings : List String) : Prop :=
  ∀ s, longest strings = some s → ∀ t ∈ strings, t.length ≤ s.length

theorem maximal_thm (strings : List String) : maximal_prop strings := by sorry

/-- The answer is the first input string having its length, so ties are stable. -/
def first_prop (strings : List String) : Prop :=
  ∀ s, longest strings = some s →
    strings.find? (fun t => decide (t.length = s.length)) = some s

theorem first_thm (strings : List String) : first_prop strings := by sorry

/-- Complete output contract: empty iff none, membership, maximum, and first tie. -/
def Post_prop (strings : List String) : Prop :=
  empty_prop strings ∧ membership_prop strings ∧ maximal_prop strings ∧ first_prop strings

/-!
## Property-based tests

Exhaustively enumerate all lists of length at most four over eight strings. The
alphabet contains empty strings, distinct equal-length strings, different lengths,
and non-ASCII characters. Each checker is an executable form of the corresponding
property; the `none` cases of the conditional properties are vacuously true.
These tests are evidence only; none is used in any theorem proof.
-/

def wordsOfLength (alphabet : List String) : Nat → List (List String)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap (fun s => (wordsOfLength alphabet n).map (s :: ·))

def testInputs : List (List String) :=
  (List.range 5).flatMap (wordsOfLength ["", "a", "b", "bb", "cd", "ccc", "é", "🙂"])

def emptyCheck (xs : List String) : Bool :=
  (longest xs).isNone == xs.isEmpty

def membershipCheck (xs : List String) : Bool :=
  match longest xs with
  | none => true
  | some s => xs.contains s

def maximalCheck (xs : List String) : Bool :=
  match longest xs with
  | none => true
  | some s => xs.all (fun t => decide (t.length ≤ s.length))

def firstCheck (xs : List String) : Bool :=
  match longest xs with
  | none => true
  | some s => xs.find? (fun t => decide (t.length = s.length)) == some s

def postCheck (xs : List String) : Bool :=
  emptyCheck xs && membershipCheck xs && maximalCheck xs && firstCheck xs

-- PBT for empty_prop, membership_prop, maximal_prop, first_prop, and Post_prop.
example : testInputs.all emptyCheck = true := by native_decide
example : testInputs.all membershipCheck = true := by native_decide
example : testInputs.all maximalCheck = true := by native_decide
example : testInputs.all firstCheck = true := by native_decide
example : testInputs.all postCheck = true := by native_decide
#eval (testInputs.length, testInputs.all postCheck)

/-- Correctness holds on the entire Python input domain, without restrictions. -/
theorem correctness_thm (strings : List String) : Pre strings → Post_prop strings := by sorry

/-- Mutable scan of the input from right to left. Replacing on equal length means
that the leftmost of the longest strings is retained in the final state. -/
def longestImperative (strings : List String) : Option String := Id.run do
  let mut best : Option String := none
  for s in strings.reverse do
    best := choose s best
  return best

example : longestImperative [] = none := by native_decide
example : longestImperative ["x", "y", "z"] = some "x" := by native_decide
example : longestImperative ["x", "yyy", "zzzz", "www", "kkkk", "abc"] = some "zzzz" := by
  native_decide
example : longestImperative ["", ""] = some "" := by native_decide
example : longestImperative ["é", "🙂", "ab"] = some "ab" := by native_decide
#eval longestImperative ["a", "bb", "ccc"]
#eval longestImperative ["x", "yyy", "zzzz", "www", "kkkk", "abc"]
example : testInputs.all (fun xs => longest xs == longestImperative xs) = true := by
  native_decide

/-- The recursive and mutable implementations agree on every input. -/
theorem equivalence_thm (strings : List String) :
    longest strings = longestImperative strings := by sorry

end humaneval_12_longest
end Agent
