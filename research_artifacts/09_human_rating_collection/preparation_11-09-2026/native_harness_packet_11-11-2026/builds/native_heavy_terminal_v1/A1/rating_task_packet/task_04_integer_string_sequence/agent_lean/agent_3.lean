import Mathlib

/-!
# HumanEval/15: `string_sequence`

Translation of the Python program `humaneval_15_string_sequence.py`:

```python
def string_sequence(n: int) -> str:
    """ Return a string containing space-delimited numbers starting from 0 upto n inclusive. """
    return ' '.join([str(x) for x in range(n + 1)])
```

The input `n` is modelled as a natural number (the docstring and the tests only
use non-negative `n`; `range(n + 1)` enumerates `0, 1, ..., n`).  `str(x)` is
`toString x` (decimal representation, `Nat.repr`) and `' '.join` is
`" ".intercalate`.

The file contains a functional implementation, unit tests, a pre-condition,
several proved properties (initial value, recursive structure, character-level
split round-trip, number of separators, length, prefix/suffix), the
post-condition, property-based tests, the correctness theorem, an imperative
implementation using a `for` loop with mutable state, and the proof that the two
implementations agree.
-/

namespace humaneval_15_string_sequence

/-! ## Functional implementation -/

/-- `' '.join([str(x) for x in range(n + 1)])`. -/
def string_sequence (n : Nat) : String :=
  " ".intercalate ((List.range (n + 1)).map toString)

/-! ## Unit tests (from the Python docstring and `check`) -/

example : string_sequence 0 = "0" := by native_decide
example : string_sequence 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence 3 = "0 1 2 3" := by native_decide
example : string_sequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval string_sequence 0
#eval string_sequence 5
#eval string_sequence 3
#eval string_sequence 10

/-! ## Pre-condition -/

/-- Every natural number is an admissible input (Python: `n >= 0`). -/
def Pre (_n : Nat) : Prop := True

/-! ## Helper lemmas -/

/-- `String.intercalate.go` distributes over list append. -/
theorem intercalate_go_append (acc s : String) (as bs : List String) :
    String.intercalate.go acc s (as ++ bs) =
      String.intercalate.go (String.intercalate.go acc s as) s bs := by
  induction as generalizing acc with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append, String.intercalate.go]
    exact ih _

/-- `intercalate` on a non-empty list followed by one more element. -/
theorem intercalate_append_singleton (s x : String) (l : List String) (hl : l ≠ []) :
    s.intercalate (l ++ [x]) = s.intercalate l ++ s ++ x := by
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [List.cons_append, String.intercalate]
  rw [intercalate_go_append]
  rfl

/-- The characters of `s.intercalate l` are `s.data` intercalated between the
characters of the elements of `l`. -/
theorem data_intercalate_go (acc s : String) (as : List String) :
    (String.intercalate.go acc s as).data =
      acc.data ++ (as.map fun a => s.data ++ a.data).flatten := by
  induction as generalizing acc with
  | nil => simp [String.intercalate.go]
  | cons a as ih =>
    simp only [String.intercalate.go, List.map_cons, List.flatten_cons]
    rw [ih]
    simp [String.data_append, List.append_assoc]

/-- `Nat.digitChar` never produces a space. -/
theorem digitChar_ne_space (m : Nat) : Nat.digitChar m ≠ ' ' := by
  by_cases h : m < 16
  · interval_cases m <;> decide
  · unfold Nat.digitChar
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    decide

/-- Every character produced by `Nat.toDigitsCore` is either from the initial
accumulator or a digit character. -/
theorem mem_toDigitsCore (b fuel n : Nat) (ds : List Char) (c : Char)
    (hc : c ∈ Nat.toDigitsCore b fuel n ds) : c ∈ ds ∨ ∃ m, c = Nat.digitChar m := by
  induction fuel generalizing n ds with
  | zero =>
    simp only [Nat.toDigitsCore] at hc
    exact Or.inl hc
  | succ fuel ih =>
    simp only [Nat.toDigitsCore] at hc
    split_ifs at hc with h
    · rcases List.mem_cons.mp hc with h1 | h1
      · exact Or.inr ⟨_, h1⟩
      · exact Or.inl h1
    · rcases ih _ _ hc with h1 | h1
      · rcases List.mem_cons.mp h1 with h2 | h2
        · exact Or.inr ⟨_, h2⟩
        · exact Or.inl h2
      · exact Or.inr h1

/-- `[x].intercalate` on a list with at least two elements. -/
theorem intercalate_cons_cons' {α : Type*} (x : α) (a b : List α) (bs : List (List α)) :
    [x].intercalate (a :: b :: bs) = a ++ x :: [x].intercalate (b :: bs) := by
  simp [List.intercalate, List.intersperse_cons₂]

theorem intercalate_cons_append_singleton_aux {α : Type*} (x : α) (a w : List α)
    (as : List (List α)) :
    [x].intercalate (a :: (as ++ [w])) = [x].intercalate (a :: as) ++ x :: w := by
  induction as generalizing a with
  | nil => simp [List.intercalate]
  | cons b bs ih =>
    rw [List.cons_append, intercalate_cons_cons', ih, intercalate_cons_cons']
    simp [List.append_assoc]

/-- `[x].intercalate` on a non-empty list followed by one more element. -/
theorem intercalate_cons_append_singleton {α : Type*} (x : α) (a w : List α)
    (as : List (List α)) :
    [x].intercalate ((a :: as) ++ [w]) = [x].intercalate (a :: as) ++ x :: w := by
  rw [List.cons_append]
  exact intercalate_cons_append_singleton_aux x a w as

/-- The decimal representation of a natural number contains no space. -/
theorem space_not_mem_toString (k : Nat) : ' ' ∉ (toString k).toList := by
  intro h
  have h' : ' ' ∈ Nat.toDigits 10 k := h
  rcases mem_toDigitsCore 10 (k + 1) k [] ' ' h' with h1 | ⟨m, hm⟩
  · simp at h1
  · exact digitChar_ne_space m hm.symm

/-! ## Properties -/

/-- `string_sequence(0) == '0'`. -/
def string_sequence_zero_prop : Prop := string_sequence 0 = "0"

theorem string_sequence_zero_thm : string_sequence_zero_prop := by
  unfold string_sequence_zero_prop
  decide

/-- Recursive structure: the sequence for `n + 1` is the sequence for `n`
followed by a space and the decimal representation of `n + 1`. -/
def string_sequence_succ_prop : Prop :=
  ∀ n : Nat, string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1)

theorem string_sequence_succ_thm : string_sequence_succ_prop := by
  intro n
  unfold string_sequence
  rw [List.range_succ, List.map_append, List.map_singleton]
  apply intercalate_append_singleton
  simp [List.range_succ]

/-- Character-level description: the characters of `string_sequence n` are the
decimal representations of `0, …, n`, intercalated with a single space. -/
theorem toList_string_sequence (n : Nat) :
    (string_sequence n).toList =
      [' '].intercalate ((List.range (n + 1)).map fun k => (toString k).toList) := by
  induction n with
  | zero =>
    decide
  | succ n ih =>
    rw [string_sequence_succ_thm n]
    show ((string_sequence n ++ " " ++ toString (n + 1))).data = _
    rw [String.data_append, String.data_append]
    change (string_sequence n).toList ++ " ".data ++ (toString (n + 1)).toList = _
    rw [ih]
    rw [List.range_succ (n := n + 1), List.map_append, List.map_singleton]
    have hne : (List.range (n + 1)).map (fun k => (toString k).toList) ≠ [] := by
      simp [List.range_succ]
    obtain ⟨a, as, has⟩ := List.exists_cons_of_ne_nil hne
    rw [has, intercalate_cons_append_singleton, List.append_assoc]
    rfl

/-- Round trip: splitting the characters of the result on a space yields exactly
the decimal representations of `0, …, n` (in order). -/
def string_sequence_splitOn_prop : Prop :=
  ∀ n : Nat, (string_sequence n).toList.splitOn ' ' =
    (List.range (n + 1)).map fun k => (toString k).toList

theorem string_sequence_splitOn_thm : string_sequence_splitOn_prop := by
  intro n
  rw [toList_string_sequence]
  apply List.splitOn_intercalate
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨k, _, rfl⟩ := hl
    exact space_not_mem_toString k
  · simp [List.range_succ]

/-- There are exactly `n` separators (spaces) in the result. -/
def string_sequence_count_space_prop : Prop :=
  ∀ n : Nat, (string_sequence n).toList.count ' ' = n

theorem string_sequence_count_space_thm : string_sequence_count_space_prop := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    rw [string_sequence_succ_thm n]
    show ((string_sequence n ++ " " ++ toString (n + 1))).data.count ' ' = n + 1
    rw [String.data_append, String.data_append, List.count_append, List.count_append]
    change (string_sequence n).toList.count ' ' + " ".data.count ' '
      + (toString (n + 1)).toList.count ' ' = n + 1
    rw [ih, List.count_eq_zero.mpr (space_not_mem_toString (n + 1))]
    rfl

/-- The length of the result is the total length of the decimal representations
of `0, …, n` plus the `n` separating spaces. -/
def string_sequence_length_prop : Prop :=
  ∀ n : Nat, (string_sequence n).length =
    ((List.range (n + 1)).map fun k => (toString k).length).sum + n

theorem string_sequence_length_thm : string_sequence_length_prop := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    rw [string_sequence_succ_thm n, String.length_append, String.length_append, ih,
      List.range_succ (n := n + 1), List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    have : (" " : String).length = 1 := rfl
    rw [this]
    omega

/-- The result starts with `'0'`. -/
def string_sequence_head_prop : Prop :=
  ∀ n : Nat, (string_sequence n).toList.head? = some '0'

theorem string_sequence_head_thm : string_sequence_head_prop := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    rw [string_sequence_succ_thm n]
    show ((string_sequence n ++ " " ++ toString (n + 1))).data.head? = some '0'
    rw [String.data_append, String.data_append, List.head?_append, List.head?_append]
    change ((string_sequence n).toList.head?.or _).or _ = some '0'
    rw [ih]
    rfl

/-- The result ends with the decimal representation of `n`. -/
def string_sequence_suffix_prop : Prop :=
  ∀ n : Nat, (toString n).toList <:+ (string_sequence n).toList

theorem string_sequence_suffix_thm : string_sequence_suffix_prop := by
  intro n
  cases n with
  | zero => decide
  | succ n =>
    rw [string_sequence_succ_thm n]
    show (toString (n + 1)).toList <:+ ((string_sequence n ++ " " ++ toString (n + 1))).data
    rw [String.data_append]
    exact List.suffix_append _ _

/-! ## Post-condition -/

/-- Post-condition: conjunction of all properties, specialised to the input `n`. -/
def Post_prop (n : Nat) : Prop :=
  (n = 0 → string_sequence n = "0") ∧
  (∀ m, n = m + 1 → string_sequence n = string_sequence m ++ " " ++ toString n) ∧
  (string_sequence n).toList.splitOn ' ' = ((List.range (n + 1)).map fun k => (toString k).toList) ∧
  (string_sequence n).toList.count ' ' = n ∧
  (string_sequence n).length = ((List.range (n + 1)).map fun k => (toString k).length).sum + n ∧
  (string_sequence n).toList.head? = some '0' ∧
  (toString n).toList <:+ (string_sequence n).toList

/-! ## Property-based tests -/

-- string_sequence_zero_prop (closed statement; checked exhaustively)
example : string_sequence 0 = "0" := by native_decide

-- string_sequence_succ_prop
#eval Plausible.Testable.check
  (∀ n : Nat, string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1))
example : (List.range 40).all
    (fun n => string_sequence (n + 1) == string_sequence n ++ " " ++ toString (n + 1)) = true := by
  native_decide

-- string_sequence_splitOn_prop
#eval Plausible.Testable.check
  (∀ n : Nat, (string_sequence n).toList.splitOn ' ' =
    (List.range (n + 1)).map fun k => (toString k).toList)
example : (List.range 40).all
    (fun n => (string_sequence n).toList.splitOn ' ' ==
      (List.range (n + 1)).map fun k => (toString k).toList) = true := by
  native_decide

-- (same round trip, phrased with Python-like `String.splitOn`; not a stated theorem)
example : (List.range 40).all
    (fun n => (string_sequence n).splitOn " " == (List.range (n + 1)).map toString) = true := by
  native_decide

-- string_sequence_count_space_prop
#eval Plausible.Testable.check (∀ n : Nat, (string_sequence n).toList.count ' ' = n)
example : (List.range 40).all (fun n => (string_sequence n).toList.count ' ' == n) = true := by
  native_decide

-- string_sequence_length_prop
#eval Plausible.Testable.check
  (∀ n : Nat, (string_sequence n).length =
    ((List.range (n + 1)).map fun k => (toString k).length).sum + n)
example : (List.range 40).all
    (fun n => (string_sequence n).length ==
      ((List.range (n + 1)).map fun k => (toString k).length).sum + n) = true := by
  native_decide

-- string_sequence_head_prop
#eval Plausible.Testable.check (∀ n : Nat, (string_sequence n).toList.head? = some '0')
example : (List.range 40).all (fun n => (string_sequence n).toList.head? == some '0') = true := by
  native_decide

-- string_sequence_suffix_prop
#eval Plausible.Testable.check (∀ n : Nat, (toString n).toList <:+ (string_sequence n).toList)
example : (List.range 40).all
    (fun n => (toString n).toList.isSuffixOf (string_sequence n).toList) = true := by
  native_decide

-- Post_prop (executable Boolean form of the conjunction)
def Post_check (n : Nat) : Bool :=
  (n != 0 || string_sequence n == "0") &&
  (n == 0 || string_sequence n == string_sequence (n - 1) ++ " " ++ toString n) &&
  ((string_sequence n).toList.splitOn ' ' ==
    (List.range (n + 1)).map fun k => (toString k).toList) &&
  ((string_sequence n).toList.count ' ' == n) &&
  ((string_sequence n).length ==
    ((List.range (n + 1)).map fun k => (toString k).length).sum + n) &&
  ((string_sequence n).toList.head? == some '0') &&
  ((toString n).toList.isSuffixOf (string_sequence n).toList)

#eval Plausible.Testable.check (∀ n : Nat, Post_check n = true)
example : (List.range 40).all Post_check = true := by native_decide

/-! ## Correctness theorem -/

theorem string_sequence_correct (n : Nat) (_h : Pre n) : Post_prop n := by
  refine ⟨?_, ?_, string_sequence_splitOn_thm n, string_sequence_count_space_thm n,
    string_sequence_length_thm n, string_sequence_head_thm n, string_sequence_suffix_thm n⟩
  · rintro rfl
    exact string_sequence_zero_thm
  · rintro m rfl
    exact string_sequence_succ_thm m

/-! ## Imperative implementation -/

/-- Imperative version: iterate `x` over `range(n + 1)` and accumulate the
space-separated string in a mutable variable. -/
def string_sequence_imp (n : Nat) : String := Id.run do
  let mut acc : String := ""
  for x in List.range (n + 1) do
    if x == 0 then
      acc := toString x
    else
      acc := acc ++ " " ++ toString x
  return acc

/-! ## Imperative tests -/

example : string_sequence_imp 0 = "0" := by native_decide
example : string_sequence_imp 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence_imp 3 = "0 1 2 3" := by native_decide
example : string_sequence_imp 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval string_sequence_imp 0
#eval string_sequence_imp 5
#eval string_sequence_imp 10

#eval Plausible.Testable.check (∀ n : Nat, string_sequence_imp n = string_sequence n)
example : (List.range 40).all (fun n => string_sequence_imp n == string_sequence n) = true := by
  native_decide

/-! ## Equivalence theorem -/

/-- The loop body of `string_sequence_imp` as a fold step. -/
def step (acc : String) (x : Nat) : String :=
  if x == 0 then toString x else acc ++ " " ++ toString x

/-- The `for` loop of `string_sequence_imp`, over an arbitrary list and start
value, is a left fold with `step`. -/
theorem loop_eq (l : List Nat) (acc : String) :
    (forIn (m := Id) l acc (fun x r =>
      if (x == 0) = true then pure (ForInStep.yield (toString x))
      else pure (ForInStep.yield (r ++ " " ++ toString x)))) = l.foldl step acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, List.foldl_cons]
    by_cases h : (x == 0) = true
    · simp only [h, if_true, step, pure_bind]
      exact ih _
    · simp only [h, step]
      exact ih _

theorem string_sequence_imp_eq_foldl (n : Nat) :
    string_sequence_imp n = (List.range (n + 1)).foldl step "" := by
  unfold string_sequence_imp
  exact loop_eq (List.range (n + 1)) ""

theorem foldl_step_eq (n : Nat) : (List.range (n + 1)).foldl step "" = string_sequence n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [List.range_succ (n := n + 1), List.foldl_append, ih, string_sequence_succ_thm n]
    simp [step]

theorem string_sequence_imp_eq (n : Nat) : string_sequence_imp n = string_sequence n := by
  rw [string_sequence_imp_eq_foldl, foldl_step_eq]

end humaneval_15_string_sequence
