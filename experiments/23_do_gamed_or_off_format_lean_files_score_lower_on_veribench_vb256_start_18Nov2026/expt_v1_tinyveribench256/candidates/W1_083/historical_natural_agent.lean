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

theorem sequence_thm (n : Int) : sequence_prop n (string_sequence n) := by
  rfl

/-- Negative bounds yield the empty string. -/
def negative_prop (n : Int) (result : String) : Prop :=
  n < 0 → result = ""

theorem negative_thm (n : Int) : negative_prop n (string_sequence n) := by
  intro h
  have hz : (n + 1).toNat = 0 := by omega
  simp [string_sequence, hz, String.intercalate]

/-- The sequence at zero has no delimiter. -/
def zero_prop (n : Int) (result : String) : Prop :=
  n = 0 → result = "0"

theorem zero_thm (n : Int) : zero_prop n (string_sequence n) := by
  rintro rfl
  rfl

/-! Auxiliary facts about the standard decimal printer and space joining. -/

lemma go_prefix (p a sep : String) (xs : List String) :
    String.intercalate.go (p ++ a) sep xs = p ++ String.intercalate.go a sep xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simpa only [String.intercalate.go, String.append_assoc] using ih (a ++ sep ++ x)

lemma intercalate_cons_cons (sep a b : String) (xs : List String) :
    String.intercalate sep (a :: b :: xs) =
      a ++ sep ++ String.intercalate sep (b :: xs) := by
  exact go_prefix (a ++ sep) b sep xs

lemma intercalate_data (sep : String) (xs : List String) :
    (String.intercalate sep xs).data = List.intercalate sep.data (xs.map String.data) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => simp [String.intercalate, String.intercalate.go, List.intercalate]
    | cons b xs =>
      rw [intercalate_cons_cons]
      simp_all [List.intercalate, List.append_assoc]

lemma digitChar_not_space (n : Nat) (hn : n < 10) : Nat.digitChar n ≠ ' ' := by
  interval_cases n <;> decide

lemma toDigitsCore_no_space (fuel n : Nat) (acc : List Char) (h : ' ' ∉ acc) :
    ' ' ∉ Nat.toDigitsCore 10 fuel n acc := by
  induction fuel generalizing n acc with
  | zero => exact h
  | succ fuel ih =>
    simp only [Nat.toDigitsCore]
    have hc : Nat.digitChar (n % 10) ≠ ' ' := digitChar_not_space _ (Nat.mod_lt _ (by decide))
    have ha : ' ' ∉ Nat.digitChar (n % 10) :: acc := by simp [Ne.symm hc, h]
    split
    · exact ha
    · exact ih _ _ ha

lemma decimal_no_space (n : Nat) : ' ' ∉ (toString n).data := by
  exact toDigitsCore_no_space (n + 1) n [] (by simp)

lemma intercalate_append_singleton (sep : String) (xs : List String) (x : String)
    (h : xs ≠ []) :
    String.intercalate sep (xs ++ [x]) = String.intercalate sep xs ++ sep ++ x := by
  cases xs with
  | nil => contradiction
  | cons a xs =>
    have hg : ∀ (ys : List String) (acc : String),
        String.intercalate.go acc sep (ys ++ [x]) =
          String.intercalate.go acc sep ys ++ sep ++ x := by
      intro ys
      induction ys with
      | nil => intro acc; rfl
      | cons y ys ih => intro acc; exact ih (acc ++ sep ++ y)
    exact hg xs a

/-- Extending a nonempty range adds one space and its new final numeral. -/
def step_prop (n : Int) (result : String) : Prop :=
  0 < n → result = string_sequence (n - 1) ++ " " ++ toString n.toNat

theorem step_thm (n : Int) : step_prop n (string_sequence n) := by
  intro hn
  have hcount : (n + 1).toNat = n.toNat + 1 := by omega
  have hprev : (n - 1 + 1).toNat = n.toNat := by omega
  have hne : (List.range n.toNat).map (fun k => toString k) ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    omega
  simp only [string_sequence, hcount, hprev, List.range_succ,
    List.map_append, List.map_cons, List.map_nil]
  exact intercalate_append_singleton " " _ _ hne

/-- Splitting at ASCII spaces recovers exactly the ordered decimal tokens.
The character-list form avoids any assumptions about UTF-8 byte positions. -/
def tokens_prop (n : Int) (result : String) : Prop :=
  0 ≤ n → result.data.splitOn ' ' =
    (List.range (n + 1).toNat).map (fun k => (toString k).data)

theorem tokens_thm (n : Int) : tokens_prop n (string_sequence n) := by
  intro hn
  unfold string_sequence
  rw [intercalate_data]
  simp only [List.map_map, Function.comp_def]
  apply List.splitOn_intercalate
  · intro l hl
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hl
    exact decimal_no_space k
  · simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    omega

/-- There are exactly n+1 tokens when n is nonnegative. -/
def token_count_prop (n : Int) (result : String) : Prop :=
  0 ≤ n → (result.data.splitOn ' ').length = (n + 1).toNat

theorem token_count_thm (n : Int) : token_count_prop n (string_sequence n) := by
  intro hn
  rw [tokens_thm n hn]
  simp

lemma intercalate_space_count (xs : List String)
    (h : ∀ s ∈ xs, ' ' ∉ s.data) :
    (String.intercalate " " xs).data.count ' ' = xs.length - 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha : a.data.count ' ' = 0 := List.count_eq_zero.mpr (h a (by simp))
    have ht : ∀ s ∈ xs, ' ' ∉ s.data := by
      intro s hs
      exact h s (by simp [hs])
    cases xs with
    | nil => simpa only [String.intercalate, String.intercalate.go] using ha
    | cons b xs =>
      rw [intercalate_cons_cons]
      simp only [String.data_append, List.count_append, ha, ih ht]
      simp [Nat.add_comm]

/-- Exactly one delimiter per adjacent pair; negative inputs have none. -/
def space_count_prop (n : Int) (result : String) : Prop :=
  result.data.count ' ' = n.toNat

theorem space_count_thm (n : Int) : space_count_prop n (string_sequence n) := by
  unfold space_count_prop string_sequence
  rw [intercalate_space_count]
  · simp only [List.length_map, List.length_range]
    omega
  · intro s hs
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hs
    exact decimal_no_space k

lemma digitChar_isDigit (n : Nat) (hn : n < 10) :
    (Nat.digitChar n).isDigit = true := by
  interval_cases n <;> decide

lemma toDigitsCore_digits (fuel n : Nat) (acc : List Char)
    (h : ∀ c ∈ acc, c.isDigit = true) :
    ∀ c ∈ Nat.toDigitsCore 10 fuel n acc, c.isDigit = true := by
  induction fuel generalizing n acc with
  | zero => exact h
  | succ fuel ih =>
    simp only [Nat.toDigitsCore]
    have hd := digitChar_isDigit (n % 10) (Nat.mod_lt _ (by decide))
    have ha : ∀ c ∈ Nat.digitChar (n % 10) :: acc, c.isDigit = true := by
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨hd, h⟩
    split
    · exact ha
    · exact ih _ _ ha

lemma toDigitsCore_nonempty (fuel n : Nat) (acc : List Char) (h : acc ≠ []) :
    Nat.toDigitsCore 10 fuel n acc ≠ [] := by
  induction fuel generalizing n acc with
  | zero => exact h
  | succ fuel ih =>
    simp only [Nat.toDigitsCore]
    split
    · exact List.cons_ne_nil _ _
    · exact ih _ _ (List.cons_ne_nil _ _)

lemma decimal_nonempty (n : Nat) : (toString n).data ≠ [] := by
  change Nat.toDigitsCore 10 (n + 1) n [] ≠ []
  simp only [Nat.toDigitsCore]
  split
  · exact List.cons_ne_nil _ _
  · exact toDigitsCore_nonempty _ _ _ (List.cons_ne_nil _ _)

lemma decimal_digits (n : Nat) : ∀ c ∈ (toString n).data, c.isDigit = true := by
  exact toDigitsCore_digits (n + 1) n [] (by simp)

/-- Every space-delimited token is nonempty and contains only decimal digits.
In particular, there are no leading, trailing, or consecutive spaces. -/
def formatting_prop (n : Int) (result : String) : Prop :=
  0 ≤ n → ∀ token ∈ result.data.splitOn ' ',
    token ≠ [] ∧ ∀ c ∈ token, c.isDigit = true

theorem formatting_thm (n : Int) : formatting_prop n (string_sequence n) := by
  intro hn token ht
  rw [tokens_thm n hn] at ht
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp ht
  exact ⟨decimal_nonempty k, decimal_digits k⟩

/-- Empty output occurs exactly for negative input, not at zero. -/
def empty_prop (n : Int) (result : String) : Prop :=
  result = "" ↔ n < 0

theorem empty_thm (n : Int) : empty_prop n (string_sequence n) := by
  constructor
  · intro he
    by_contra hn
    have hnonneg : 0 ≤ n := by omega
    have hempty : ([] : List Char) ∈ (string_sequence n).data.splitOn ' ' := by
      simp [he, List.splitOn]
    exact (formatting_thm n hnonneg [] hempty).1 rfl
  · exact negative_thm n

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
theorem correctness_thm (n : Int) : Pre n → Post_prop n (string_sequence n) := by
  intro _
  exact ⟨sequence_thm n, negative_thm n, zero_thm n, step_thm n,
    tokens_thm n, token_count_thm n, space_count_thm n,
    formatting_thm n, empty_thm n⟩

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
      acc ++ ks.map toString := by
  induction ks generalizing acc with
  | nil => simp
  | cons k ks ih => simp [List.foldl_cons, ih, List.append_assoc]

/-- Functional/imperative equivalence for all integers, including negative ones. -/
theorem equivalence_thm (n : Int) :
    string_sequence n = string_sequence_imperative n := by
  symm
  simp only [string_sequence_imperative, pure_bind, List.forIn_pure_yield_eq_foldl]
  change String.intercalate " " ((List.range (n + 1).toNat).foldl
    (fun parts k => parts ++ [toString k]) []) = string_sequence n
  rw [fold_tokens, List.nil_append]
  rfl

end humaneval_15_string_sequence
end Agent
