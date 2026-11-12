import Mathlib

/-!
# HumanEval 15: String sequence

This file formalizes the Python function `string_sequence`.  Its natural-number
input represents the intended nonnegative part of Python's integer domain.  The
function converts every number from zero through the input (inclusive) to a
decimal string and joins the resulting tokens with single spaces.
-/

namespace humaneval_15_string_sequence

/-- Functional translation of Python's `" ".join(str(x) for x in range(n + 1))`. -/
def string_sequence (n : Nat) : String :=
  String.intercalate " " ((List.range (n + 1)).map toString)

example : string_sequence 0 = "0" := by native_decide
example : string_sequence 3 = "0 1 2 3" := by native_decide
example : string_sequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval string_sequence 0
#eval string_sequence 5
#eval string_sequence 10

/-- Natural numbers already express the intended precondition `n ≥ 0`. -/
def Pre (_n : Nat) : Prop := True

/-- The output is exactly the space-joined list of decimal numerals from `0` to `n`. -/
def exact_sequence_prop (n : Nat) (output : String) : Prop :=
  output = String.intercalate " " ((List.range (n + 1)).map toString)

theorem exact_sequence_thm (n : Nat) :
    exact_sequence_prop n (string_sequence n) := by
  rfl

/-- The inclusive range contributes exactly `n + 1` output tokens. -/
def token_count_prop (n : Nat) : Prop :=
  ((List.range (n + 1)).map toString).length = n + 1

theorem token_count_thm (n : Nat) : token_count_prop n := by
  simp [token_count_prop]

/-- The final token is the decimal representation of the inclusive endpoint `n`. -/
def final_token_prop (n : Nat) : Prop :=
  ((List.range (n + 1)).map toString).getLast? = some (toString n)

theorem final_token_thm (n : Nat) : final_token_prop n := by
  simp [final_token_prop, List.range_succ]

/-- Complete postcondition: exact output, correct token count, and inclusive endpoint. -/
def Post_prop (n : Nat) (output : String) : Prop :=
  exact_sequence_prop n output ∧ token_count_prop n ∧ final_token_prop n

theorem string_sequence_correct (n : Nat) :
    Pre n → Post_prop n (string_sequence n) := by
  intro _
  exact ⟨exact_sequence_thm n, token_count_thm n, final_token_thm n⟩

/--
Imperative translation.  It traverses the same range and mutably appends each
decimal token before joining the accumulated list with spaces.
-/
def string_sequence_imperative (n : Nat) : String := Id.run do
  let mut pieces : List String := []
  for i in List.range (n + 1) do
    pieces := pieces ++ [toString i]
  return String.intercalate " " pieces

example : string_sequence_imperative 0 = "0" := by native_decide
example : string_sequence_imperative 3 = "0 1 2 3" := by native_decide
example : string_sequence_imperative 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval string_sequence_imperative 0
#eval string_sequence_imperative 5
#eval string_sequence_imperative 10

/-- The token accumulator isolated from the final joining operation. -/
private def collect_strings (xs : List Nat) : List String := Id.run do
  let mut pieces : List String := []
  for i in xs do
    pieces := pieces ++ [toString i]
  return pieces

private theorem flatten_singletons (xs : List Nat) :
    (xs.map (fun x => [toString x])).flatten = xs.map toString := by
  induction xs <;> simp_all

private theorem collect_strings_eq_map (xs : List Nat) :
    collect_strings xs = xs.map toString := by
  simp [collect_strings, flatten_singletons]

/-- The functional and mutable-state implementations return identical strings. -/
theorem string_sequence_equiv (n : Nat) :
    string_sequence n = string_sequence_imperative n := by
  rw [string_sequence]
  change String.intercalate " " ((List.range (n + 1)).map toString) =
    String.intercalate " " (collect_strings (List.range (n + 1)))
  rw [collect_strings_eq_map]

end humaneval_15_string_sequence
