import Mathlib
namespace Agent

/-!
# HumanEval 15: string_sequence

Python's `range(n + 1)` is represented by `List.range (n + 1).toNat`.
Thus every integer input is supported: a negative upper bound produces the
empty string, while a nonnegative bound produces the decimal numerals from
zero through that bound, separated by exactly one ASCII space.
-/

namespace humaneval_15_string_sequence

/-- The functional translation of the list comprehension followed by `join`. -/
def string_sequence (n : Int) : String :=
  String.intercalate " " ((List.range (n + 1).toNat).map fun k => toString k)

-- The three public tests, the docstring example, and negative-input checks.
example : string_sequence 0 = "0" := by native_decide
example : string_sequence 3 = "0 1 2 3" := by native_decide
example : string_sequence 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide
example : string_sequence (-1) = "" := by native_decide
example : string_sequence (-8) = "" := by native_decide
#eval string_sequence 0
#eval string_sequence 3
#eval string_sequence 10
#eval string_sequence (-3)

/-- Python accepts every integer; negative ranges are empty. -/
def Pre (_n : Int) : Prop := True

/-- Exact ordered, space-delimited decimal representation of the range. -/
def sequence_prop (n : Int) (result : String) : Prop :=
  result = String.intercalate " "
    ((List.range (n + 1).toNat).map fun k => toString k)

theorem sequence_thm (n : Int) : sequence_prop n (string_sequence n) := by sorry

/-- Negative bounds yield the empty string. -/
def negative_prop (n : Int) (result : String) : Prop :=
  n < 0 → result = ""

theorem negative_thm (n : Int) : negative_prop n (string_sequence n) := by sorry

/-- The sequence at zero has no delimiter. -/
def zero_prop (n : Int) (result : String) : Prop :=
  n = 0 → result = "0"

theorem zero_thm (n : Int) : zero_prop n (string_sequence n) := by sorry

/-! Auxiliary facts about the standard decimal printer and space joining. -/

lemma go_prefix (p a sep : String) (xs : List String) :
    String.intercalate.go (p ++ a) sep xs = p ++ String.intercalate.go a sep xs := by sorry

lemma intercalate_cons_cons (sep a b : String) (xs : List String) :
    String.intercalate sep (a :: b :: xs) =
      a ++ sep ++ String.intercalate sep (b :: xs) := by sorry

lemma intercalate_data (sep : String) (xs : List String) :
    (String.intercalate sep xs).data = List.intercalate sep.data (xs.map String.data) := by sorry

lemma digitChar_not_space (n : Nat) (hn : n < 10) : Nat.digitChar n ≠ ' ' := by sorry

lemma toDigitsCore_no_space (fuel n : Nat) (acc : List Char) (h : ' ' ∉ acc) :
    ' ' ∉ Nat.toDigitsCore 10 fuel n acc := by sorry

lemma decimal_no_space (n : Nat) : ' ' ∉ (toString n).data := by sorry

lemma intercalate_append_singleton (sep : String) (xs : List String) (x : String)
    (h : xs ≠ []) :
    String.intercalate sep (xs ++ [x]) = String.intercalate sep xs ++ sep ++ x := by sorry

/-- Extending a nonempty range adds one space and its new final numeral. -/
def step_prop (n : Int) (result : String) : Prop :=
  0 < n → result = string_sequence (n - 1) ++ " " ++ toString n.toNat

theorem step_thm (n : Int) : step_prop n (string_sequence n) := by sorry

/-- Splitting at ASCII spaces recovers exactly the ordered decimal tokens.
The character-list form avoids any assumptions about UTF-8 byte positions. -/
def tokens_prop (n : Int) (result : String) : Prop :=
  0 ≤ n → result.data.splitOn ' ' =
    (List.range (n + 1).toNat).map (fun k => (toString k).data)

theorem tokens_thm (n : Int) : tokens_prop n (string_sequence n) := by sorry

/-- There are exactly n+1 tokens when n is nonnegative. -/
def token_count_prop (n : Int) (result : String) : Prop :=
  0 ≤ n → (result.data.splitOn ' ').length = (n + 1).toNat

theorem token_count_thm (n : Int) : token_count_prop n (string_sequence n) := by sorry

lemma intercalate_space_count (xs : List String)
    (h : ∀ s ∈ xs, ' ' ∉ s.data) :
    (String.intercalate " " xs).data.count ' ' = xs.length - 1 := by sorry

/-- Exactly one delimiter per adjacent pair; negative inputs have none. -/
def space_count_prop (n : Int) (result : String) : Prop :=
  result.data.count ' ' = n.toNat

theorem space_count_thm (n : Int) : space_count_prop n (string_sequence n) := by sorry

lemma digitChar_isDigit (n : Nat) (hn : n < 10) :
    (Nat.digitChar n).isDigit = true := by sorry

lemma toDigitsCore_digits (fuel n : Nat) (acc : List Char)
    (h : ∀ c ∈ acc, c.isDigit = true) :
    ∀ c ∈ Nat.toDigitsCore 10 fuel n acc, c.isDigit = true := by sorry

lemma toDigitsCore_nonempty (fuel n : Nat) (acc : List Char) (h : acc ≠ []) :
    Nat.toDigitsCore 10 fuel n acc ≠ [] := by sorry

lemma decimal_nonempty (n : Nat) : (toString n).data ≠ [] := by sorry

lemma decimal_digits (n : Nat) : ∀ c ∈ (toString n).data, c.isDigit = true := by sorry

/-- Every space-delimited token is nonempty and contains only decimal digits.
In particular, there are no leading, trailing, or consecutive spaces. -/
def formatting_prop (n : Int) (result : String) : Prop :=
  0 ≤ n → ∀ token ∈ result.data.splitOn ' ',
    token ≠ [] ∧ ∀ c ∈ token, c.isDigit = true

theorem formatting_thm (n : Int) : formatting_prop n (string_sequence n) := by sorry

/-- Empty output occurs exactly for negative input, not at zero. -/
def empty_prop (n : Int) (result : String) : Prop :=
  result = "" ↔ n < 0

theorem empty_thm (n : Int) : empty_prop n (string_sequence n) := by sorry

/-- The complete contract, without excluding negative Python integers. -/
def Post_prop (n : Int) (result : String) : Prop :=
  sequence_prop n result ∧
  negative_prop n result ∧
  zero_prop n result ∧
  step_prop n result ∧
  tokens_prop n result ∧
  token_count_prop n result ∧
  space_count_prop n result ∧
  formatting_prop n result ∧
  empty_prop n result

/-! ## Property-based tests

These are exhaustive bounded PBTs, not proofs of the universal claims.
The range -30,...,120 includes negative inputs, zero, and both the 9/10
and 99/100 decimal-width transitions. Each executable property and the
whole postcondition is tested independently.
-/

/-- Computable decidability is used only to execute the bounded tests. -/
local instance (n : Int) (result : String) : Decidable (sequence_prop n result) := by
  unfold sequence_prop
  infer_instance

local instance (n : Int) (result : String) : Decidable (negative_prop n result) := by
  unfold negative_prop
  infer_instance

local instance (n : Int) (result : String) : Decidable (zero_prop n result) := by
  unfold zero_prop
  infer_instance

local instance (n : Int) (result : String) : Decidable (step_prop n result) := by
  unfold step_prop
  infer_instance

local instance (n : Int) (result : String) : Decidable (tokens_prop n result) := by
  unfold tokens_prop
  infer_instance

local instance (n : Int) (result : String) : Decidable (token_count_prop n result) := by
  unfold token_count_prop
  infer_instance

local instance (n : Int) (result : String) : Decidable (space_count_prop n result) := by
  unfold space_count_prop
  infer_instance

local instance (n : Int) (result : String) : Decidable (formatting_prop n result) := by
  unfold formatting_prop
  infer_instance

local instance (n : Int) (result : String) : Decidable (empty_prop n result) := by
  unfold empty_prop
  infer_instance

local instance (n : Int) (result : String) : Decidable (Post_prop n result) := by
  unfold Post_prop
  infer_instance

def testInputs : List Int :=
  (List.range 151).map (fun k => (k : Int) - 30)

-- PBT for `sequence_prop`.
example : testInputs.all (fun n => decide (sequence_prop n (string_sequence n))) = true := by
  native_decide

-- PBT for `negative_prop`.
example : testInputs.all (fun n => decide (negative_prop n (string_sequence n))) = true := by
  native_decide

-- PBT for `zero_prop`.
example : testInputs.all (fun n => decide (zero_prop n (string_sequence n))) = true := by
  native_decide

-- PBT for `step_prop`.
example : testInputs.all (fun n => decide (step_prop n (string_sequence n))) = true := by
  native_decide

-- PBT for `tokens_prop`.
example : testInputs.all (fun n => decide (tokens_prop n (string_sequence n))) = true := by
  native_decide

-- PBT for `token_count_prop`.
example : testInputs.all (fun n => decide (token_count_prop n (string_sequence n))) = true := by
  native_decide

-- PBT for `space_count_prop`.
example : testInputs.all (fun n => decide (space_count_prop n (string_sequence n))) = true := by
  native_decide

-- PBT for `formatting_prop`.
example : testInputs.all (fun n => decide (formatting_prop n (string_sequence n))) = true := by
  native_decide

-- PBT for `empty_prop`.
example : testInputs.all (fun n => decide (empty_prop n (string_sequence n))) = true := by
  native_decide

-- PBT for `Post_prop`.
example : testInputs.all (fun n => decide (Post_prop n (string_sequence n))) = true := by
  native_decide

/-- The functional translation satisfies the contract on every admissible input. -/
theorem correctness_thm (n : Int) : Pre n → Post_prop n (string_sequence n) := by sorry

/-! ## Imperative translation

The mutable list is the Python list-comprehension accumulator. The loop
appends each decimal numeral in range order, then joins with one space.
-/

/-- An `Id.run` implementation with a mutable token list and an explicit loop. -/
def string_sequence_imperative (n : Int) : String := Id.run do
  let mut parts : List String := []
  for k in List.range (n + 1).toNat do
    parts := parts ++ [toString k]
  return String.intercalate " " parts

example : string_sequence_imperative 0 = "0" := by native_decide
example : string_sequence_imperative 3 = "0 1 2 3" := by native_decide
example : string_sequence_imperative 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence_imperative 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide
example : string_sequence_imperative (-1) = "" := by native_decide
example : string_sequence_imperative (-8) = "" := by native_decide
#eval string_sequence_imperative 0
#eval string_sequence_imperative 3
#eval string_sequence_imperative 10
#eval string_sequence_imperative (-3)

-- Additional bounded differential test of the two implementations.
example : testInputs.all (fun n =>
    string_sequence n == string_sequence_imperative n) = true := by
  native_decide

/-- Loop invariant: processing a suffix appends precisely its printed tokens. -/
lemma fold_tokens (ks : List Nat) (acc : List String) :
    ks.foldl (fun parts k => parts ++ [toString k]) acc =
      acc ++ ks.map toString := by sorry

/-- Functional/imperative equivalence for all integers, including negative ones. -/
theorem equivalence_thm (n : Int) :
    string_sequence n = string_sequence_imperative n := by sorry

end humaneval_15_string_sequence
end Agent
