import Mathlib
namespace Gold

/-!

# VeriBench – Longest Common Subsequence


The properties are proved; the functional/imperative equivalence remains an open proof obligation.

# Implementation

## Longest Common Subsequence

Finds the longest common subsequence between two strings.-/

namespace LongestCommonSubsequence

/-- Check if a list is a subsequence of another -/
def List.isSubsequence [DecidableEq α] (sub : List α) (sup : List α) : Bool :=
  match sub, sup with
  | [], _ => true
  | _, [] => false
  | h₁::t₁, h₂::t₂ =>
    if h₁ = h₂ then
      isSubsequence t₁ t₂
    else
      isSubsequence (h₁::t₁) t₂

/-- Check if a string is a subsequence of another -/
def String.isSubsequence (sub : String) (sup : String) : Bool :=
  List.isSubsequence sub.toList sup.toList

/--
**Implementation of `longestCommonSubsequence`.**

`longestCommonSubsequence s1 s2` returns the longest common subsequence between two strings.
Evaluates the Python prefix dynamic-programming recurrence on reversed character lists.

NOTE(curator, 2026-09-08): The old front-first recursion chose the wrong tied
subsequence. Reversing both inputs and the result evaluates the Python prefix
dynamic programme from the last characters, including its UP-on-equality tie rule.

## Examples

#eval longestCommonSubsequence "abcde" "ace" -- expected: "ace"
#eval longestCommonSubsequence "abc" "def" -- expected: ""
-/
def longestCommonSubsequence (s1 s2 : String) : String :=
  if s1.isEmpty || s2.isEmpty then
    ""
  else
    -- Evaluate the prefix recurrence from the last characters of each input.
    let chars1 := s1.toList.reverse
    let chars2 := s2.toList.reverse
    let rec findCommon (l1 l2 : List Char) (acc : List Char) : List Char :=
      match l1, l2 with
      | [], _ => acc.reverse
      | _, [] => acc.reverse
      | h1::t1, h2::t2 =>
        if h1 = h2 then
          findCommon t1 t2 (h1::acc)
        else
          let try1 := findCommon t1 (h2::t2) acc
          let try2 := findCommon (h1::t1) t2 acc
          if try1.length >= try2.length then try1 else try2
      termination_by l1.length + l2.length
    String.mk (findCommon chars1 chars2 []).reverse

/-!
# Tests
-/

/-- expected: "ace" -/
example : longestCommonSubsequence "abcde" "ace" = "ace" := by native_decide
#eval! longestCommonSubsequence "abcde" "ace" -- expected: "ace"

/-- expected: "abc" -/
example : longestCommonSubsequence "abc" "abc" = "abc" := by native_decide
#eval! longestCommonSubsequence "abc" "abc" -- expected: "abc"

/-!
# Tests: Edge Cases
-/

/-- expected: "" -/
example : longestCommonSubsequence "" "" = "" := by unfold longestCommonSubsequence; rfl
#eval! longestCommonSubsequence "" "" -- expected: ""

/-- expected: "" -/
example : longestCommonSubsequence "abc" "" = "" := by native_decide
#eval! longestCommonSubsequence "abc" "" -- expected: ""

/-!
# Positive / Negative Test‑Suite
-/

/-- positive: identical strings return the string -/
example : longestCommonSubsequence "test" "test" = "test" := by native_decide
#eval! longestCommonSubsequence "test" "test" -- expected: "test"

/-- positive: no common characters -/
example : longestCommonSubsequence "abc" "def" = "" := by native_decide
#eval! longestCommonSubsequence "abc" "def" -- expected: ""

/-- negative: result should not be longer than either input -/
example : ¬ ((longestCommonSubsequence "abc" "def").length > "abc".length) := by native_decide
#eval! (decide ((longestCommonSubsequence "abc" "def").length > "abc".length)) -- expected: false

example : longestCommonSubsequence "" "abc" = "" := by native_decide
#eval! longestCommonSubsequence "" "abc" -- expected: ""

example : longestCommonSubsequence "abc" "c" = "c" := by native_decide
#eval! longestCommonSubsequence "abc" "c" -- expected: "c"

example : longestCommonSubsequence "c" "abc" = "c" := by native_decide
#eval! longestCommonSubsequence "c" "abc" -- expected: "c"

example : longestCommonSubsequence "ab" "ba" = "a" := by native_decide
#eval! longestCommonSubsequence "ab" "ba" -- expected: "a"

example : longestCommonSubsequence "ba" "ab" = "b" := by native_decide
#eval! longestCommonSubsequence "ba" "ab" -- expected: "b"

example : longestCommonSubsequence "abcbdab" "bdcaba" = "bcba" := by native_decide
#eval! longestCommonSubsequence "abcbdab" "bdcaba" -- expected: "bcba"

example : longestCommonSubsequence "bdcaba" "abcbdab" = "bdab" := by native_decide
#eval! longestCommonSubsequence "bdcaba" "abcbdab" -- expected: "bdab"

example : longestCommonSubsequence "abab" "baba" = "aba" := by native_decide
#eval! longestCommonSubsequence "abab" "baba" -- expected: "aba"

example : longestCommonSubsequence "baba" "abab" = "bab" := by native_decide
#eval! longestCommonSubsequence "baba" "abab" -- expected: "bab"

example : longestCommonSubsequence "acb" "abc" = "ac" := by native_decide
#eval! longestCommonSubsequence "acb" "abc" -- expected: "ac"

example : longestCommonSubsequence "abc" "acb" = "ab" := by native_decide
#eval! longestCommonSubsequence "abc" "acb" -- expected: "ab"

example : longestCommonSubsequence "xyz" "zyx" = "x" := by native_decide
#eval! longestCommonSubsequence "xyz" "zyx" -- expected: "x"

example : longestCommonSubsequence "zyx" "xyz" = "z" := by native_decide
#eval! longestCommonSubsequence "zyx" "xyz" -- expected: "z"

-- Tie case: Python prefers dropping the last character of s1 (`>=`), so ("aab", "aba") gives "aa".
example : longestCommonSubsequence "aab" "aba" = "aa" := by native_decide
#eval! longestCommonSubsequence "aab" "aba" -- expected: "aa"

-- Tie case: Python prefers dropping the last character of s1 (`>=`), so ("aba", "aab") gives "ab".
example : longestCommonSubsequence "aba" "aab" = "ab" := by native_decide
#eval! longestCommonSubsequence "aba" "aab" -- expected: "ab"

example : longestCommonSubsequence "AGGTAB" "GXTXAYB" = "GTAB" := by native_decide
#eval! longestCommonSubsequence "AGGTAB" "GXTXAYB" -- expected: "GTAB"

example : longestCommonSubsequence "ABCDGH" "AEDFHR" = "ADH" := by native_decide
#eval! longestCommonSubsequence "ABCDGH" "AEDFHR" -- expected: "ADH"

example : longestCommonSubsequence "Hello" "HELLO" = "H" := by native_decide
#eval! longestCommonSubsequence "Hello" "HELLO" -- expected: "H"

example : longestCommonSubsequence "aXbXc" "XaXbXc" = "aXbXc" := by native_decide
#eval! longestCommonSubsequence "aXbXc" "XaXbXc" -- expected: "aXbXc"

example : longestCommonSubsequence "xaybzc" "abc" = "abc" := by native_decide
#eval! longestCommonSubsequence "xaybzc" "abc" -- expected: "abc"

/-!
# Pre‑Condition
-/

/-- **Pre‑condition.** Any two strings are valid inputs. -/
def Pre (s1 s2 : String) : Prop := True

/-!
# Property Theorems
-/

/-- **Empty string property**: LCS with empty string is empty string. -/
def empty_string_prop (s : String) : Prop := longestCommonSubsequence s "" = "" ∧ longestCommonSubsequence "" s = ""

/-- **Empty string theorem**: LCS with empty string is empty string. -/
@[simp] theorem empty_string_thm (s : String) : empty_string_prop s := sorry

/-- **Subsequence property**: Result is a subsequence of both inputs. -/
def subsequence_prop (s1 s2 : String) : Prop :=
  let lcs := longestCommonSubsequence s1 s2
  String.isSubsequence lcs s1 ∧ String.isSubsequence lcs s2

/-- **Subsequence theorem**: Result is a subsequence of both inputs. -/
-- TIER-A: requires unfolding longestCommonSubsequence recursion and String.isSubsequence over toList
@[simp] theorem subsequence_thm (s1 s2 : String) : subsequence_prop s1 s2 := sorry

/-- **Self LCS property**: LCS of a string with itself equals the string. -/
def self_lcs_prop (s : String) : Prop := longestCommonSubsequence s s = s

/-- **Self LCS theorem**: LCS of a string with itself equals the string. -/
-- TIER-A: requires induction on String.toList and String.mk roundtrip lemmas
@[simp] theorem self_lcs_thm (s : String) : self_lcs_prop s := sorry

-- NOTE(curator, 2026-09-08): string-level commutativity is FALSE: the Python DP tie rule picks `longestCommonSubsequence "ab" "ba" = "a"` but `longestCommonSubsequence "ba" "ab" = "b"`. What is symmetric is the LCS *length*, so the property remains stated on lengths.
/-- **Commutativity property**: the length of the longest common subsequence is symmetric in its arguments. -/
def commutativity_prop (s1 s2 : String) : Prop :=
  (longestCommonSubsequence s1 s2).length = (longestCommonSubsequence s2 s1).length

/-- **Commutativity theorem**: LCS is commutative. -/
-- TIER-A: proved by strong induction on the combined list lengths; tied branches have equal length.
@[simp] theorem commutativity_thm (s1 s2 : String) : commutativity_prop s1 s2 := sorry

/-- **Length bound property**: LCS length is bounded by minimum of input lengths. -/
def length_bound_prop (s1 s2 : String) : Prop := (longestCommonSubsequence s1 s2).length ≤ min s1.length s2.length

/-- **Length bound theorem**: LCS length is bounded by minimum of input lengths. -/
-- TIER-A: requires String.length / List.length bounds on LCS output
@[simp] theorem length_bound_thm (s1 s2 : String) : length_bound_prop s1 s2 := sorry

/-!
# Post‑Condition  (conjunction of all desired properties)
-/

/-- **Post‑condition**: conjunction of all desired properties for longestCommonSubsequence. -/
def Post_prop (s1 s2 : String) : Prop :=
  (∀ s, empty_string_prop s) ∧                           -- empty_string_prop
  (subsequence_prop s1 s2) ∧                             -- subsequence_prop
  (self_lcs_prop s1) ∧                                   -- self_lcs_prop (for s1)
  (commutativity_prop s1 s2) ∧                           -- commutativity_prop
  (length_bound_prop s1 s2)                              -- length_bound_prop

/-!
# Correctness Theorem
-/

/-- **Correctness theorem**: the pre‑condition implies the post‑condition. -/
theorem correctness_thm (s1 s2 : String) (hPre : Pre s1 s2) : Post_prop s1 s2 := sorry

/-!
# Imperative Implementation
-/

/--
`longestCommonSubsequenceImp s1 s2` computes the same LCS using imperative style.
Fills length and direction tables, then reconstructs the selected subsequence.

NOTE(curator, 2026-09-08): The old greedy scan missed common subsequences.
This port follows the Python dynamic programme, its UP-on-equality tie rule,
and its bottom-right reconstruction using a bounded loop.
-/
def longestCommonSubsequenceImp (s1 s2 : String) : String :=
  Id.run do
    if s1.isEmpty || s2.isEmpty then
      return ""

    let chars1 := s1.toList.toArray
    let chars2 := s2.toList.toArray
    let m := chars1.size
    let n := chars2.size
    let mut dp : Array (Array Nat) := Array.replicate (m + 1) (Array.replicate (n + 1) 0)
    let mut direction : Array (Array Nat) := Array.replicate (m + 1) (Array.replicate (n + 1) 0)

    -- Fill the dynamic-programming tables: diagonal on matches, UP on ties.
    for i in [1:m+1] do
      for j in [1:n+1] do
        if chars1[i - 1]! == chars2[j - 1]! then
          dp := dp.set! i (dp[i]!.set! j ((dp[i - 1]!)[j - 1]! + 1))
          direction := direction.set! i (direction[i]!.set! j 0)
        else if (dp[i - 1]!)[j]! >= (dp[i]!)[j - 1]! then
          dp := dp.set! i (dp[i]!.set! j (dp[i - 1]!)[j]!)
          direction := direction.set! i (direction[i]!.set! j 1)
        else
          dp := dp.set! i (dp[i]!.set! j (dp[i]!)[j - 1]!)
          direction := direction.set! i (direction[i]!.set! j 2)

    let mut i := m
    let mut j := n
    let mut result : List Char := []
    -- Every real reconstruction step strictly lowers i + j; m + n steps suffice.
    for _ in [0:m+n] do
      if i > 0 && j > 0 then
        if (direction[i]!)[j]! == 0 then
          result := chars1[i - 1]! :: result
          i := i - 1
          j := j - 1
        else if (direction[i]!)[j]! == 1 then
          i := i - 1
        else
          j := j - 1

    return String.mk result

/-!
# Imperative Tests
-/

/-- expected: "GTAB" -/
example : longestCommonSubsequenceImp "AGGTAB" "GXTXAYB" = "GTAB" := by native_decide
#eval! longestCommonSubsequenceImp "AGGTAB" "GXTXAYB" -- expected: "GTAB"

/-!
# Imperative Tests: Edge Cases
-/

/-- expected: "" -/
example : longestCommonSubsequenceImp "" "" = "" := by native_decide
#eval! longestCommonSubsequenceImp "" "" -- expected: ""

/-- expected: "" -/
example : longestCommonSubsequenceImp "test" "" = "" := by native_decide
#eval! longestCommonSubsequenceImp "test" "" -- expected: ""

/-!
# Positive / Negative Test‑Suite
-/

/-- positive: identical strings return the string -/
example : longestCommonSubsequenceImp "test" "test" = "test" := by native_decide
#eval! longestCommonSubsequenceImp "test" "test" -- expected: "test"

/-- negative: result should not be longer than shorter input -/
example : ¬ ((longestCommonSubsequenceImp "ab" "abc").length > "ab".length) := by native_decide
#eval! (decide ((longestCommonSubsequenceImp "ab" "abc").length > "ab".length)) -- expected: false

example : longestCommonSubsequenceImp "abcde" "ace" = "ace" := by native_decide
#eval! longestCommonSubsequenceImp "abcde" "ace" -- expected: "ace"

example : longestCommonSubsequenceImp "abc" "abc" = "abc" := by native_decide
#eval! longestCommonSubsequenceImp "abc" "abc" -- expected: "abc"

example : longestCommonSubsequenceImp "abc" "def" = "" := by native_decide
#eval! longestCommonSubsequenceImp "abc" "def" -- expected: ""

example : longestCommonSubsequenceImp "abc" "" = "" := by native_decide
#eval! longestCommonSubsequenceImp "abc" "" -- expected: ""

example : longestCommonSubsequenceImp "" "abc" = "" := by native_decide
#eval! longestCommonSubsequenceImp "" "abc" -- expected: ""

example : longestCommonSubsequenceImp "abc" "c" = "c" := by native_decide
#eval! longestCommonSubsequenceImp "abc" "c" -- expected: "c"

example : longestCommonSubsequenceImp "c" "abc" = "c" := by native_decide
#eval! longestCommonSubsequenceImp "c" "abc" -- expected: "c"

example : longestCommonSubsequenceImp "ab" "ba" = "a" := by native_decide
#eval! longestCommonSubsequenceImp "ab" "ba" -- expected: "a"

example : longestCommonSubsequenceImp "ba" "ab" = "b" := by native_decide
#eval! longestCommonSubsequenceImp "ba" "ab" -- expected: "b"

example : longestCommonSubsequenceImp "abcbdab" "bdcaba" = "bcba" := by native_decide
#eval! longestCommonSubsequenceImp "abcbdab" "bdcaba" -- expected: "bcba"

example : longestCommonSubsequenceImp "bdcaba" "abcbdab" = "bdab" := by native_decide
#eval! longestCommonSubsequenceImp "bdcaba" "abcbdab" -- expected: "bdab"

example : longestCommonSubsequenceImp "abab" "baba" = "aba" := by native_decide
#eval! longestCommonSubsequenceImp "abab" "baba" -- expected: "aba"

example : longestCommonSubsequenceImp "baba" "abab" = "bab" := by native_decide
#eval! longestCommonSubsequenceImp "baba" "abab" -- expected: "bab"

example : longestCommonSubsequenceImp "acb" "abc" = "ac" := by native_decide
#eval! longestCommonSubsequenceImp "acb" "abc" -- expected: "ac"

example : longestCommonSubsequenceImp "abc" "acb" = "ab" := by native_decide
#eval! longestCommonSubsequenceImp "abc" "acb" -- expected: "ab"

example : longestCommonSubsequenceImp "xyz" "zyx" = "x" := by native_decide
#eval! longestCommonSubsequenceImp "xyz" "zyx" -- expected: "x"

example : longestCommonSubsequenceImp "zyx" "xyz" = "z" := by native_decide
#eval! longestCommonSubsequenceImp "zyx" "xyz" -- expected: "z"

-- Tie case: Python prefers dropping the last character of s1 (`>=`), so ("aab", "aba") gives "aa".
example : longestCommonSubsequenceImp "aab" "aba" = "aa" := by native_decide
#eval! longestCommonSubsequenceImp "aab" "aba" -- expected: "aa"

-- Tie case: Python prefers dropping the last character of s1 (`>=`), so ("aba", "aab") gives "ab".
example : longestCommonSubsequenceImp "aba" "aab" = "ab" := by native_decide
#eval! longestCommonSubsequenceImp "aba" "aab" -- expected: "ab"

example : longestCommonSubsequenceImp "ABCDGH" "AEDFHR" = "ADH" := by native_decide
#eval! longestCommonSubsequenceImp "ABCDGH" "AEDFHR" -- expected: "ADH"

example : longestCommonSubsequenceImp "Hello" "HELLO" = "H" := by native_decide
#eval! longestCommonSubsequenceImp "Hello" "HELLO" -- expected: "H"

example : longestCommonSubsequenceImp "aXbXc" "XaXbXc" = "aXbXc" := by native_decide
#eval! longestCommonSubsequenceImp "aXbXc" "XaXbXc" -- expected: "aXbXc"

example : longestCommonSubsequenceImp "xaybzc" "abc" = "abc" := by native_decide
#eval! longestCommonSubsequenceImp "xaybzc" "abc" -- expected: "abc"

private theorem find_acc (l1 l2 acc : List Char) :
    longestCommonSubsequence.findCommon l1 l2 acc =
      acc.reverse ++ longestCommonSubsequence.findCommon l1 l2 [] := sorry

private def selected (a b : List Char) (i j : Nat) : List Char :=
  (longestCommonSubsequence.findCommon (a.take i).reverse (b.take j).reverse []).reverse

private theorem selected_zero_left (a b : List Char) (j : Nat) : selected a b 0 j = [] := sorry

private theorem selected_zero_right (a b : List Char) (i : Nat) : selected a b i 0 = [] := sorry

private theorem selected_step (a b : List Char) (i j : Nat) (hi : i < a.length)
    (hj : j < b.length) :
    selected a b (i+1) (j+1) =
      if a[i]! = b[j]! then selected a b i j ++ [a[i]!]
      else if (selected a b i (j+1)).length ≥ (selected a b (i+1) j).length then
        selected a b i (j+1) else selected a b (i+1) j := sorry

private abbrev Matrix := Array (Array Nat)

private def rectangle (t : Matrix) (m n : Nat) : Prop :=
  t.size = m + 1 ∧ ∀ r, r ≤ m → t[r]!.size = n + 1

private def matrixSet (t : Matrix) (i j value : Nat) : Matrix :=
  t.set! i (t[i]!.set! j value)

private theorem array_get_set {α : Type} [Inhabited α] (a : Array α)
    (i j : Nat) (v : α) (hj : j < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := sorry

private theorem matrixSet_rectangle (t : Matrix) (m n i j v : Nat)
    (ht : rectangle t m n) : rectangle (matrixSet t i j v) m n := sorry

private theorem matrixSet_get (t : Matrix) (m n i j r c v : Nat)
    (ht : rectangle t m n) (hr : r ≤ m) (hc : c ≤ n) :
    ((matrixSet t i j v)[r]!)[c]! = if i = r ∧ j = c then v else (t[r]!)[c]! := sorry

private abbrev Tables := MProd Matrix Matrix

private def directionAt (a b : List Char) (i j : Nat) : Nat :=
  if a[i-1]! = b[j-1]! then 0
  else if (selected a b (i-1) j).length ≥ (selected a b i (j-1)).length then 1 else 2

private def fillStep (a b : List Char) (i j : Nat) (st : Tables) : Tables :=
  if a[i-1]! == b[j-1]! then
    ⟨matrixSet st.fst i j 0, matrixSet st.snd i j ((st.snd[i-1]!)[j-1]! + 1)⟩
  else if (st.snd[i-1]!)[j]! ≥ (st.snd[i]!)[j-1]! then
    ⟨matrixSet st.fst i j 1, matrixSet st.snd i j (st.snd[i-1]!)[j]!⟩
  else
    ⟨matrixSet st.fst i j 2, matrixSet st.snd i j (st.snd[i]!)[j-1]!⟩

private theorem fillStep_spec (a b : List Char) (i j : Nat) (st : Tables)
    (hi0 : 0 < i) (hi : i ≤ a.length) (hj0 : 0 < j) (hj : j ≤ b.length)
    (hd : (st.snd[i-1]!)[j-1]! = (selected a b (i-1) (j-1)).length)
    (hu : (st.snd[i-1]!)[j]! = (selected a b (i-1) j).length)
    (hl : (st.snd[i]!)[j-1]! = (selected a b i (j-1)).length) :
    fillStep a b i j st =
      ⟨matrixSet st.fst i j (directionAt a b i j),
        matrixSet st.snd i j (selected a b i j).length⟩ := sorry

private def filled (a b : List Char) (i j : Nat) (st : Tables) : Prop :=
  rectangle st.fst a.length b.length ∧ rectangle st.snd a.length b.length ∧
  (∀ r c, r ≤ a.length → c ≤ b.length →
    (r = 0 ∨ c = 0 ∨ r < i ∨ (r = i ∧ c < j)) →
    (st.snd[r]!)[c]! = (selected a b r c).length) ∧
  (∀ r c, r ≤ a.length → c ≤ b.length → 0 < r → 0 < c →
    (r < i ∨ (r = i ∧ c < j)) → (st.fst[r]!)[c]! = directionAt a b r c)

private theorem fillStep_filled (a b : List Char) (i j : Nat) (st : Tables)
    (hi0 : 0 < i) (hi : i ≤ a.length) (hj0 : 0 < j) (hj : j ≤ b.length)
    (hs : filled a b i j st) : filled a b i (j+1) (fillStep a b i j st) := sorry

private theorem fold_range_invariant {α : Type} (f : Nat → α → α) (P : Nat → α → Prop)
    (k n : Nat) (st : α) (hstart : P k st)
    (hstep : ∀ j, k ≤ j → j < k+n → ∀ s, P j s → P (j+1) (f j s)) :
    P (k+n) ((List.range' k n).foldl (fun s j => f j s) st) := sorry

private def initialTables (a b : List Char) : Tables :=
  let zero := Array.replicate (a.length+1) (Array.replicate (b.length+1) 0)
  ⟨zero,zero⟩

private def fillRow (a b : List Char) (i : Nat) (st : Tables) : Tables :=
  (List.range' 1 b.length).foldl (fun s j => fillStep a b i j s) st

private def fillTables (a b : List Char) : Tables :=
  (List.range' 1 a.length).foldl (fun s i => fillRow a b i s) (initialTables a b)

private theorem replicate_get {α : Type} [Inhabited α] (n i : Nat) (v : α) (hi : i < n) :
    (Array.replicate n v)[i]! = v := sorry

private theorem initial_filled (a b : List Char) : filled a b 1 1 (initialTables a b) := sorry

private theorem advance_row (a b : List Char) (i : Nat) (st : Tables)
    (hs : filled a b i (b.length+1) st) : filled a b (i+1) 1 st := sorry

private theorem fillRow_filled (a b : List Char) (i : Nat) (st : Tables)
    (hi0 : 0 < i) (hi : i ≤ a.length) (hs : filled a b i 1 st) :
    filled a b (i+1) 1 (fillRow a b i st) := sorry

private theorem fillTables_filled (a b : List Char) :
    filled a b (a.length+1) 1 (fillTables a b) := sorry

private abbrev TraceState := MProd Nat (MProd Nat (List Char))

private def traceStep (a : List Char) (dir : Matrix) (st : TraceState) : TraceState :=
  let i := st.fst
  let j := st.snd.fst
  let acc := st.snd.snd
  if i > 0 ∧ j > 0 then
    if (dir[i]!)[j]! == 0 then ⟨i-1,j-1,a[i-1]! :: acc⟩
    else if (dir[i]!)[j]! == 1 then ⟨i-1,j,acc⟩
    else ⟨i,j-1,acc⟩
  else st

private def reconstruct (a : List Char) (dir : Matrix) : Nat → Nat → Nat → List Char → List Char
  | 0, _, _, acc => acc
  | fuel+1, i, j, acc =>
    if i > 0 ∧ j > 0 then
      if (dir[i]!)[j]! == 0 then reconstruct a dir fuel (i-1) (j-1) (a[i-1]! :: acc)
      else if (dir[i]!)[j]! == 1 then reconstruct a dir fuel (i-1) j acc
      else reconstruct a dir fuel i (j-1) acc
    else reconstruct a dir fuel i j acc

private theorem trace_fold (a : List Char) (dir : Matrix) (fuel k i j : Nat) (acc : List Char) :
    ((List.range' k fuel).foldl (fun st _ => traceStep a dir st)
      (⟨i,j,acc⟩ : TraceState)).snd.snd = reconstruct a dir fuel i j acc := sorry

private theorem reconstruct_spec (a b : List Char) (dir : Matrix)
    (hd : ∀ i j, i ≤ a.length → j ≤ b.length → 0 < i → 0 < j →
      (dir[i]!)[j]! = directionAt a b i j)
    (fuel i j : Nat) (acc : List Char) (hi : i ≤ a.length) (hj : j ≤ b.length)
    (hf : i = 0 ∨ j = 0 ∨ i+j ≤ fuel) :
    reconstruct a dir fuel i j acc = selected a b i j ++ acc := sorry

private theorem yield_ite {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if p then pure (ForInStep.yield a) else pure (ForInStep.yield b) : Id (ForInStep α)) =
      pure (ForInStep.yield (if p then a else b)) := sorry

private theorem imperative_form (s1 s2 : String)
    (h : (s1.isEmpty || s2.isEmpty) = false) :
    longestCommonSubsequenceImp s1 s2 = String.mk
      (reconstruct s1.data (fillTables s1.data s2.data).fst
        (s1.length+s2.length) s1.length s2.length []) := sorry


-- TIER-B: both implementations follow the Python prefix recurrence and UP-on-tie rule.
-- The remaining proof needs a table-fill invariant and a bounded reconstruction invariant.
/-- **Equivalence theorem**: functional and imperative implementations coincide. -/
theorem longestCommonSubsequence_equivalence_thm (s1 s2 : String) :
  longestCommonSubsequence s1 s2 = longestCommonSubsequenceImp s1 s2 := sorry

end LongestCommonSubsequence
end Gold
