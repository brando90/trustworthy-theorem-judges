import Mathlib

/-!
# HumanEval 15: string_sequence

A translation of Python's `' '.join(str(x) for x in range(n + 1))`.
The input is an integer, including negative integers (whose range is empty).
Natural-number decimal printing is appropriate because all generated numbers
are nonnegative. The specification describes the complete ordered sequence,
its boundary cases, and its one-step extension. The imperative version builds
the same list of decimal tokens using a mutable accumulator.
-/

namespace humaneval_15_string_sequence

/-- Python's `range(n + 1)`, including its empty negative-input case. -/
def numbers (n : Int) : List Nat := List.range (n + 1).toNat

/-- Functional translation of the list comprehension followed by `join`. -/
def string_sequence (n : Int) : String :=
  String.intercalate " " ((numbers n).map toString)

example : string_sequence 0 = "0" := by native_decide
example : string_sequence 3 = "0 1 2 3" := by native_decide
example : string_sequence 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide
example : string_sequence (-1) = "" := by native_decide
example : string_sequence (-8) = "" := by native_decide
#eval string_sequence 0
#eval string_sequence 3
#eval string_sequence 10
#eval string_sequence (-2)

/-- Python accepts every integer; there is no nonnegativity restriction. -/
def Pre (_n : Int) : Prop := True

/-- The full output specification, with the negative case explicit. -/
def sequence_prop (n : Int) (result : String) : Prop :=
  result = if n < 0 then ""
    else String.intercalate " " ((List.range (n.toNat + 1)).map toString)

/-- An empty range prints the empty string. -/
def negative_prop (n : Int) (result : String) : Prop := n < 0 → result = ""

/-- The smallest nonempty output. -/
def zero_prop (n : Int) (result : String) : Prop := n = 0 → result = "0"

/-- Appending the next number adds exactly one separating space. -/
def successor_prop (n : Int) (result : String) : Prop :=
  0 ≤ n → string_sequence (n + 1) = result ++ " " ++ toString (n.toNat + 1)

/-- The output contains all numeral characters and exactly `max(n, 0)` spaces. -/
def length_prop (n : Int) (result : String) : Prop :=
  result.length =
    ((List.range (n + 1).toNat).map (fun k => (toString k).length)).sum + n.toNat

/- Elementary lemmas about the actual string join, proved structurally. -/
private theorem join_go_snoc (sep last : String) (xs : List String) (acc : String) :
    String.intercalate.go acc sep (xs ++ [last]) =
      String.intercalate.go acc sep xs ++ sep ++ last := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, String.intercalate.go] using ih (acc ++ sep ++ x)

private theorem join_snoc (sep last : String) (xs : List String) (h : xs ≠ []) :
    String.intercalate sep (xs ++ [last]) =
      String.intercalate sep xs ++ sep ++ last := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons x xs => exact join_go_snoc sep last xs x

private theorem join_go_length (sep : String) (xs : List String) (acc : String) :
    (String.intercalate.go acc sep xs).length =
      acc.length + xs.length * sep.length + (xs.map String.length).sum := by
  induction xs generalizing acc with
  | nil => simp [String.intercalate.go]
  | cons x xs ih =>
      simp only [String.intercalate.go, ih, String.length_append,
        List.length_cons, List.map_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
      omega

private theorem join_length (sep : String) (xs : List String) :
    (String.intercalate sep xs).length =
      (xs.map String.length).sum + (xs.length - 1) * sep.length := by
  cases xs with
  | nil => simp [String.intercalate]
  | cons x xs =>
      simp only [String.intercalate, join_go_length, List.map_cons, List.sum_cons,
        List.length_cons, Nat.add_sub_cancel]
      omega

/-- Exact agreement with the complete sequence specification. -/
theorem sequence_thm (n : Int) : sequence_prop n (string_sequence n) := by
  unfold sequence_prop string_sequence numbers
  split_ifs with h
  · have hz : (n + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    simp [hz, String.intercalate]
  · rw [Int.toNat_add (by omega : 0 ≤ n) (by omega : (0 : Int) ≤ 1)]
    rfl

theorem negative_thm (n : Int) : negative_prop n (string_sequence n) := by
  intro h
  simpa [sequence_prop, h] using sequence_thm n

theorem zero_thm (n : Int) : zero_prop n (string_sequence n) := by
  intro h
  subst n
  rfl

theorem successor_thm (n : Int) : successor_prop n (string_sequence n) := by
  intro hn
  have h1 : (n + 1).toNat = n.toNat + 1 := by omega
  have h2 : (n + 1 + 1).toNat = (n.toNat + 1) + 1 := by omega
  unfold string_sequence numbers
  rw [h1, h2, List.range_succ, List.map_append, List.map_singleton]
  apply join_snoc
  simp

theorem length_thm (n : Int) : length_prop n (string_sequence n) := by
  have h : (n + 1).toNat - 1 = n.toNat := by omega
  have hs : (" " : String).length = 1 := rfl
  simpa [length_prop, string_sequence, numbers, List.map_map, Function.comp_def, h, hs]
    using join_length " " ((List.range (n + 1).toNat).map toString)

/-- Complete postcondition: exact contents, boundaries, extension, and length. -/
def Post_prop (n : Int) (result : String) : Prop :=
  sequence_prop n result ∧ negative_prop n result ∧ zero_prop n result ∧
    successor_prop n result ∧ length_prop n result

/-!
## Property-based tests

Each bounded check below covers every integer from -30 through 100, including
both sides of zero and the transitions from one- to two- to three-digit tokens.
The expressions are executable forms of the corresponding propositions.
These tests are evidence only; the theorems above use kernel-checked proofs.
-/
private def testInputs : List Int := (List.range 131).map (fun k => (k : Int) - 30)

-- PBT for sequence_prop.
example : testInputs.all (fun n =>
    string_sequence n == (if n < 0 then ""
      else String.intercalate " " ((List.range (n.toNat + 1)).map toString))) = true := by
  native_decide

-- PBT for negative_prop (decidable implication, rather than discarding inputs).
example : testInputs.all (fun n =>
    decide (n < 0 → string_sequence n = "")) = true := by native_decide

-- PBT for zero_prop.
example : testInputs.all (fun n =>
    decide (n = 0 → string_sequence n = "0")) = true := by native_decide

-- PBT for successor_prop.
example : testInputs.all (fun n =>
    decide (0 ≤ n → string_sequence (n + 1) =
      string_sequence n ++ " " ++ toString (n.toNat + 1))) = true := by native_decide

-- PBT for length_prop.
example : testInputs.all (fun n =>
    (string_sequence n).length ==
      ((List.range (n + 1).toNat).map (fun k => (toString k).length)).sum + n.toNat) =
    true := by native_decide

-- PBT for the whole Post_prop conjunction.
example : testInputs.all (fun n =>
    decide (
      (string_sequence n = (if n < 0 then ""
        else String.intercalate " " ((List.range (n.toNat + 1)).map toString))) ∧
      (n < 0 → string_sequence n = "") ∧
      (n = 0 → string_sequence n = "0") ∧
      (0 ≤ n → string_sequence (n + 1) =
        string_sequence n ++ " " ++ toString (n.toNat + 1)) ∧
      ((string_sequence n).length =
        ((List.range (n + 1).toNat).map (fun k => (toString k).length)).sum + n.toNat)
    )) = true := by native_decide

/-- Correctness for every admissible input, including negative integers. -/
theorem correctness (n : Int) : Pre n → Post_prop n (string_sequence n) := by
  intro _
  exact ⟨sequence_thm n, negative_thm n, zero_thm n, successor_thm n, length_thm n⟩

/-- Imperative list-comprehension translation with a mutable token buffer. -/
def string_sequence_imperative (n : Int) : String := Id.run do
  let mut tokens : List String := []
  for x in List.range (n + 1).toNat do
    tokens := tokens ++ [toString x]
  return String.intercalate " " tokens

example : string_sequence_imperative 0 = "0" := by native_decide
example : string_sequence_imperative 3 = "0 1 2 3" := by native_decide
example : string_sequence_imperative 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence_imperative 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide
example : string_sequence_imperative (-1) = "" := by native_decide
example : string_sequence_imperative (-8) = "" := by native_decide
#eval string_sequence_imperative 0
#eval string_sequence_imperative 3
#eval string_sequence_imperative 10
#eval string_sequence_imperative (-2)

example : testInputs.all (fun n =>
    string_sequence n == string_sequence_imperative n) = true := by native_decide

/-- Loop invariant: the accumulated prefix followed by all remaining tokens. -/
private theorem collect_tokens (xs : List Nat) (acc : List String) :
    xs.foldl (fun ts x => ts ++ [toString x]) acc = acc ++ xs.map toString := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, List.append_assoc]

/-- Functional and imperative translations agree on the entire integer domain. -/
theorem functional_eq_imperative (n : Int) :
    string_sequence n = string_sequence_imperative n := by
  change String.intercalate " " ((List.range (n + 1).toNat).map toString) =
    String.intercalate " " (forIn (m := Id) (List.range (n + 1).toNat)
      ([] : List String) (fun x tokens => pure (ForInStep.yield (tokens ++ [toString x]))))
  rw [List.forIn_pure_yield_eq_foldl]
  change String.intercalate " " ((List.range (n + 1).toNat).map toString) =
    String.intercalate " " ((List.range (n + 1).toNat).foldl
      (fun tokens x => tokens ++ [toString x]) [])
  rw [collect_tokens]
  rfl

end humaneval_15_string_sequence
