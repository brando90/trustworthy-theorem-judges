import Mathlib

/-!
# HumanEval/15 — `string_sequence`

Lean 4 formalization of the Python program `humaneval_15_string_sequence.py`:

```python
def string_sequence(n: int) -> str:
    """ Return a string containing space-delimited numbers starting from 0 upto n inclusive. """
    return ' '.join([str(x) for x in range(n + 1)])
```

`string_sequence n` is the string of the space-delimited decimal numerals of `0, 1, …, n`
(inclusive).  The file contains

* a functional implementation mirroring the Python one-liner (`' '.join` over `range(n+1)`),
* unit tests taken from the docstring and the `check` function,
* the pre-condition, a collection of properties (closed form, tokens obtained by splitting on
  spaces, first and last token, number of separators, length, recursive structure) each
  with a proof, the post-condition and the correctness theorem,
* property-based tests,
* an imperative implementation (`Id.run do` with mutable state) and a proof that it agrees
  with the functional one.
-/

namespace humaneval_15_string_sequence

/-! ## Functional implementation -/

/-- `' '.join([str(x) for x in range(n + 1)])`: join the decimal representations of
`0, …, n` with single spaces. -/
def string_sequence (n : Nat) : String :=
  " ".intercalate ((List.range (n + 1)).map toString)

/-! ## Unit tests (docstring examples and `check`) -/

example : string_sequence 0 = "0" := by native_decide
example : string_sequence 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence 3 = "0 1 2 3" := by native_decide
example : string_sequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval string_sequence 0    -- "0"
#eval string_sequence 3    -- "0 1 2 3"
#eval string_sequence 10   -- "0 1 2 3 4 5 6 7 8 9 10"

/-! ## Auxiliary lemmas -/

/-- Appending one more piece to the accumulator loop of `String.intercalate`. -/
theorem intercalate_go_append (acc s : String) (l : List String) (x : String) :
    String.intercalate.go acc s (l ++ [x]) = String.intercalate.go acc s l ++ s ++ x := by
  induction l generalizing acc with
  | nil => simp [String.intercalate.go]
  | cons a l ih => simp only [List.cons_append, String.intercalate.go]; exact ih _

/-- `String.intercalate` of a non-empty list extended by one element. -/
theorem intercalate_append_singleton (s x : String) (l : List String) (hl : l ≠ []) :
    s.intercalate (l ++ [x]) = s.intercalate l ++ s ++ x := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a l => simp only [List.cons_append, String.intercalate]; exact intercalate_go_append _ _ _ _

/-- `List.intercalate` (with a one-element separator) of a non-empty list extended by one
element. -/
theorem list_intercalate_append_singleton {α : Type*} (s : α) (l : List (List α)) (x : List α)
    (hl : l ≠ []) : [s].intercalate (l ++ [x]) = [s].intercalate l ++ s :: x := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    cases l with
    | nil => simp [List.intercalate]
    | cons b l =>
      have h := ih (by simp)
      simp only [List.cons_append, List.intercalate, List.intersperse_cons₂, List.flatten_cons] at h ⊢
      rw [h]
      simp [List.append_assoc]

/-- No digit character is a space. -/
theorem digitChar_ne_space (d : Nat) : Nat.digitChar d ≠ ' ' := by
  by_cases h : d < 16
  · revert d; decide
  · have h0 : d ≠ 0 := by omega
    have h1 : d ≠ 1 := by omega
    have h2 : d ≠ 2 := by omega
    have h3 : d ≠ 3 := by omega
    have h4 : d ≠ 4 := by omega
    have h5 : d ≠ 5 := by omega
    have h6 : d ≠ 6 := by omega
    have h7 : d ≠ 7 := by omega
    have h8 : d ≠ 8 := by omega
    have h9 : d ≠ 9 := by omega
    have h10 : d ≠ 10 := by omega
    have h11 : d ≠ 11 := by omega
    have h12 : d ≠ 12 := by omega
    have h13 : d ≠ 13 := by omega
    have h14 : d ≠ 14 := by omega
    have h15 : d ≠ 15 := by omega
    simp only [Nat.digitChar, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      h15, if_false]
    decide

/-- `Nat.toDigitsCore` never produces a space (given a space-free accumulator). -/
theorem toDigitsCore_ne_space (b fuel n : Nat) (ds : List Char) (h : ∀ c ∈ ds, c ≠ ' ') :
    ∀ c ∈ Nat.toDigitsCore b fuel n ds, c ≠ ' ' := by
  induction fuel generalizing n ds with
  | zero => simpa [Nat.toDigitsCore] using h
  | succ fuel ih =>
    intro c hc
    simp only [Nat.toDigitsCore] at hc
    split at hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact digitChar_ne_space _
      · exact h c hc
    · refine ih _ _ ?_ c hc
      intro c' hc'
      simp only [List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · exact digitChar_ne_space _
      · exact h c' hc'

/-- The decimal representation `str(k)` of a natural number contains no space. -/
theorem toString_nat_no_space (k : Nat) : ' ' ∉ (toString k).toList := by
  intro h
  have hk : (toString k).toList = Nat.toDigits 10 k := rfl
  rw [hk] at h
  exact toDigitsCore_ne_space 10 _ k [] (by simp) ' ' h rfl

theorem toList_append (s t : String) : (s ++ t).toList = s.toList ++ t.toList :=
  String.data_append s t

theorem space_toList : " ".toList = [' '] := rfl

/-- Base case: `string_sequence 0 = "0"`. -/
theorem string_sequence_zero : string_sequence 0 = "0" := rfl

/-- Recursive characterization: the result for `n + 1` is the result for `n` followed by a
space and the numeral of `n + 1`. -/
theorem string_sequence_succ (n : Nat) :
    string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1) := by
  unfold string_sequence
  rw [List.range_succ (n := n + 1), List.map_append, List.map_singleton,
    intercalate_append_singleton _ _ _ (by simp)]

/-- Character-level description of the result: the numerals of `0, …, n` interspersed with
single spaces. -/
theorem string_sequence_toList (n : Nat) :
    (string_sequence n).toList =
      [' '].intercalate ((List.range (n + 1)).map fun k => (toString k).toList) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [string_sequence_succ, toList_append, toList_append, ih, List.range_succ (n := n + 1),
      List.map_append, List.map_singleton, list_intercalate_append_singleton _ _ _ (by simp),
      space_toList]
    simp [List.append_assoc]

/-! ## Pre-condition -/

/-- Every natural number `n` is an admissible input (`range(n + 1)` is always well defined). -/
def Pre (_n : Nat) : Prop := True

/-! ## Properties -/

/-- The result is exactly `' '.join([str(x) for x in range(n + 1)])`. -/
def join_prop (n : Nat) (result : String) : Prop :=
  result = " ".intercalate ((List.range (n + 1)).map toString)

/-- Splitting the result on spaces yields the numerals of `0, 1, …, n` in order
("space-delimited numbers starting from 0 up to n inclusive"). -/
def tokens_prop (n : Nat) (result : String) : Prop :=
  result.toList.splitOn ' ' = (List.range (n + 1)).map fun k => (toString k).toList

/-- The result starts with `"0"`. -/
def head_prop (_n : Nat) (result : String) : Prop :=
  ∃ t, result = "0" ++ t

/-- The result ends with the numeral of `n`. -/
def last_prop (n : Nat) (result : String) : Prop :=
  ∃ t, result = t ++ toString n

/-- The result contains exactly `n` spaces (one separator between consecutive numbers). -/
def space_count_prop (n : Nat) (result : String) : Prop :=
  result.toList.count ' ' = n

/-- The length of the result is the total length of the numerals plus the `n` separators. -/
def length_prop (n : Nat) (result : String) : Prop :=
  result.length = n + ((List.range (n + 1)).map fun k => (toString k).length).sum

/-- Recursive structure of the function itself. -/
def step_prop (n : Nat) : Prop :=
  string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1)

theorem join_thm (n : Nat) : join_prop n (string_sequence n) := rfl

theorem tokens_thm (n : Nat) : tokens_prop n (string_sequence n) := by
  unfold tokens_prop
  rw [string_sequence_toList]
  apply List.splitOn_intercalate
  · intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨k, -, rfl⟩ := hl
    exact toString_nat_no_space k
  · simp

theorem head_thm (n : Nat) : head_prop n (string_sequence n) := by
  induction n with
  | zero => exact ⟨"", rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t ++ " " ++ toString (n + 1), by rw [string_sequence_succ, ht]; simp [String.append_assoc]⟩

theorem last_thm (n : Nat) : last_prop n (string_sequence n) := by
  cases n with
  | zero => exact ⟨"", rfl⟩
  | succ n => exact ⟨string_sequence n ++ " ", string_sequence_succ n⟩

theorem space_count_thm (n : Nat) : space_count_prop n (string_sequence n) := by
  unfold space_count_prop
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [string_sequence_succ, toList_append, toList_append, List.count_append, List.count_append, ih,
      space_toList]
    have h1 : [' '].count ' ' = 1 := rfl
    have h2 : (toString (n + 1)).toList.count ' ' = 0 :=
      List.count_eq_zero.mpr (toString_nat_no_space _)
    omega

theorem length_thm (n : Nat) : length_prop n (string_sequence n) := by
  unfold length_prop
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [string_sequence_succ, String.length_append, String.length_append, ih,
      List.range_succ (n := n + 1)]
    simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_cons, List.sum_nil]
    have h1 : " ".length = 1 := rfl
    omega

theorem step_thm (n : Nat) : step_prop n := string_sequence_succ n

/-! ## Post-condition -/

/-- Post-condition: conjunction of all properties of the result. -/
def Post_prop (n : Nat) (result : String) : Prop :=
  join_prop n result ∧ tokens_prop n result ∧ head_prop n result ∧ last_prop n result ∧
    space_count_prop n result ∧ length_prop n result

/-! ## Property-based tests -/

-- join_prop
#eval Plausible.Testable.check
  (∀ n : Nat, string_sequence n = " ".intercalate ((List.range (n + 1)).map toString))
-- tokens_prop
#eval Plausible.Testable.check
  (∀ n : Nat, (string_sequence n).toList.splitOn ' ' =
    (List.range (n + 1)).map fun k => (toString k).toList)
-- the same tokenisation property stated with `String.splitOn` (as in Python's `split`)
#eval Plausible.Testable.check
  (∀ n : Nat, (string_sequence n).splitOn " " = (List.range (n + 1)).map toString)
-- head_prop (executable counterpart of `∃ t, result = "0" ++ t`)
#eval Plausible.Testable.check (∀ n : Nat, (string_sequence n).startsWith "0" = true)
-- last_prop (executable counterpart of `∃ t, result = t ++ toString n`)
#eval Plausible.Testable.check (∀ n : Nat, (string_sequence n).endsWith (toString n) = true)
-- space_count_prop
#eval Plausible.Testable.check (∀ n : Nat, (string_sequence n).toList.count ' ' = n)
-- length_prop
#eval Plausible.Testable.check
  (∀ n : Nat, (string_sequence n).length =
    n + ((List.range (n + 1)).map fun k => (toString k).length).sum)
-- step_prop
#eval Plausible.Testable.check
  (∀ n : Nat, string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1))
-- Post_prop (executable form, randomized)
#eval Plausible.Testable.check
  (∀ n : Nat,
    string_sequence n = " ".intercalate ((List.range (n + 1)).map toString) ∧
    (string_sequence n).toList.splitOn ' ' = ((List.range (n + 1)).map fun k => (toString k).toList) ∧
    (string_sequence n).startsWith "0" = true ∧
    (string_sequence n).endsWith (toString n) = true ∧
    (string_sequence n).toList.count ' ' = n ∧
    (string_sequence n).length = n + ((List.range (n + 1)).map fun k => (toString k).length).sum)

/-- Executable Boolean form of the post-condition. -/
def postCheck (n : Nat) : Bool :=
  string_sequence n == " ".intercalate ((List.range (n + 1)).map toString) &&
  (string_sequence n).toList.splitOn ' ' == ((List.range (n + 1)).map fun k => (toString k).toList) &&
  (string_sequence n).splitOn " " == (List.range (n + 1)).map toString &&
  (string_sequence n).startsWith "0" &&
  (string_sequence n).endsWith (toString n) &&
  (string_sequence n).toList.count ' ' == n &&
  (string_sequence n).length == n + ((List.range (n + 1)).map fun k => (toString k).length).sum &&
  string_sequence (n + 1) == string_sequence n ++ " " ++ toString (n + 1)

-- Post_prop and step_prop, exhaustive bounded check
example : (List.range 200).all postCheck = true := by native_decide

/-! ## Correctness theorem -/

theorem string_sequence_correct (n : Nat) (_h : Pre n) : Post_prop n (string_sequence n) :=
  ⟨join_thm n, tokens_thm n, head_thm n, last_thm n, space_count_thm n, length_thm n⟩

/-! ## Imperative implementation -/

/-- Imperative version: accumulate the numerals of `0, …, n`, inserting a space before every
numeral but the first (the separator is `""` for the first iteration and `" "` afterwards). -/
def string_sequence_imp (n : Nat) : String := Id.run do
  let mut acc : String := ""
  let mut sep : String := ""
  for x in List.range (n + 1) do
    acc := acc ++ sep ++ toString x
    sep := " "
  return acc

/-! ## Imperative tests -/

example : string_sequence_imp 0 = "0" := by native_decide
example : string_sequence_imp 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence_imp 3 = "0 1 2 3" := by native_decide
example : string_sequence_imp 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval string_sequence_imp 0
#eval string_sequence_imp 3
#eval string_sequence_imp 10

#eval Plausible.Testable.check (∀ n : Nat, string_sequence_imp n = string_sequence n)
example : (List.range 200).all (fun n => string_sequence_imp n == string_sequence n) = true := by
  native_decide

/-! ## Equivalence theorem -/

/-- The imperative implementation agrees with the functional one. -/
theorem string_sequence_imp_eq (n : Nat) : string_sequence_imp n = string_sequence n := by
  unfold string_sequence_imp string_sequence
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, String.intercalate]
  simp only [List.forIn_cons, Id.run, bind, pure, String.empty_append]
  generalize List.map Nat.succ (List.range n) = l
  generalize toString 0 = a
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [List.forIn_cons, bind, List.map_cons, String.intercalate.go]
    exact ih _

end humaneval_15_string_sequence
