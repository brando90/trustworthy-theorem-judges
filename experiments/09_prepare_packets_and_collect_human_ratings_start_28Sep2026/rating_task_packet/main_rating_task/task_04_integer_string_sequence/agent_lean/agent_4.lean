import Mathlib

/-!
# HumanEval 15 — `string_sequence`

Lean 4 formalization of the Python function

```python
def string_sequence(n: int) -> str:
    return ' '.join([str(x) for x in range(n + 1)])
```

The documented behaviour is a space-delimited sequence of decimals from 0 through `n`
inclusive. On that domain the function is the intercalation of `toString` over
`List.range (n + 1)`. Python `range(n + 1)` is empty for every `n < 0`, so the join is
`""`; that edge is modelled by `stringSequenceInt`.
-/

namespace humaneval_15_string_sequence

/-- Space-delimited decimal representations of `0, 1, …, n`. -/
def stringSequence (n : Nat) : String :=
  String.intercalate " " ((List.range (n + 1)).map toString)

/-- Python entry name. -/
abbrev string_sequence := stringSequence

example : stringSequence 0 = "0" := by native_decide
example : stringSequence 3 = "0 1 2 3" := by native_decide
example : stringSequence 5 = "0 1 2 3 4 5" := by native_decide
example : stringSequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval stringSequence 0
#eval stringSequence 5
#eval stringSequence 10

/-- Every natural number is admissible for the documented specification. -/
def Pre (_n : Nat) : Prop := True

lemma string_append_assoc (a b c : String) : (a ++ b) ++ c = a ++ (b ++ c) := by
  apply String.ext
  simp [String.data_append, List.append_assoc]

lemma intercalate_go_append_left (pre acc sep : String) (xs : List String) :
    String.intercalate.go (pre ++ acc) sep xs =
      pre ++ String.intercalate.go acc sep xs := by
  induction xs generalizing acc with
  | nil =>
    simp [String.intercalate.go]
  | cons a as ih =>
    rw [String.intercalate.go.eq_1, String.intercalate.go.eq_1]
    rw [show (pre ++ acc) ++ sep ++ a = pre ++ (acc ++ sep ++ a) from by
      simp [string_append_assoc]]
    exact ih (acc ++ sep ++ a)

lemma intercalate_cons (sep a : String) (as : List String) (h : as ≠ []) :
    String.intercalate sep (a :: as) = a ++ sep ++ String.intercalate sep as := by
  cases as with
  | nil => exact (h rfl).elim
  | cons b bs =>
    simp only [String.intercalate.eq_2, String.intercalate.go.eq_1]
    rw [show a ++ sep ++ b = a ++ (sep ++ b) from by simp [string_append_assoc]]
    rw [intercalate_go_append_left a (sep ++ b) sep bs]
    rw [intercalate_go_append_left sep b sep bs]
    simp [string_append_assoc]

lemma intercalate_append_singleton (sep : String) (xs : List String) (a : String)
    (h : xs ≠ []) :
    String.intercalate sep (xs ++ [a]) = String.intercalate sep xs ++ sep ++ a := by
  induction xs with
  | nil => exact (h rfl).elim
  | cons b bs ih =>
    rw [List.cons_append]
    by_cases hbs : bs = []
    · subst hbs
      simp [String.intercalate, String.intercalate.go, string_append_assoc]
    · rw [intercalate_cons sep b (bs ++ [a]) (by simp [hbs])]
      rw [intercalate_cons sep b bs hbs]
      rw [ih hbs]
      simp [string_append_assoc]

theorem stringSequence_succ (n : Nat) :
    stringSequence (n + 1) = stringSequence n ++ " " ++ toString (n + 1) := by
  unfold stringSequence
  rw [List.range_succ (n := n + 1)]
  rw [List.map_append, List.map_singleton]
  apply intercalate_append_singleton
  intro h
  simp at h

theorem stringSequence_zero : stringSequence 0 = "0" := by
  decide

lemma digitChar_ne_space (n : Nat) : Nat.digitChar n ≠ ' ' := by
  by_cases h : n < 16
  · interval_cases n <;> unfold Nat.digitChar <;> decide
  · unfold Nat.digitChar
    simp [(show n ≠ 0 by omega), (show n ≠ 1 by omega), (show n ≠ 2 by omega),
      (show n ≠ 3 by omega), (show n ≠ 4 by omega), (show n ≠ 5 by omega),
      (show n ≠ 6 by omega), (show n ≠ 7 by omega), (show n ≠ 8 by omega),
      (show n ≠ 9 by omega), (show n ≠ 10 by omega), (show n ≠ 11 by omega),
      (show n ≠ 12 by omega), (show n ≠ 13 by omega), (show n ≠ 14 by omega),
      (show n ≠ 15 by omega)]

lemma toDigitsCore_no_space (base fuel n : Nat) (ds : List Char) (hds : ' ' ∉ ds) :
    ' ' ∉ Nat.toDigitsCore base fuel n ds := by
  induction fuel generalizing n ds with
  | zero =>
    simpa [Nat.toDigitsCore] using hds
  | succ fuel ih =>
    rw [Nat.toDigitsCore]
    by_cases hdiv : n / base = 0
    · simp only [hdiv, ite_true]
      intro hmem
      rcases List.mem_cons.mp hmem with hmem | hmem
      · exact (digitChar_ne_space _).symm hmem
      · exact hds hmem
    · simp only [hdiv, ite_false]
      apply ih
      intro hmem
      rcases List.mem_cons.mp hmem with hmem | hmem
      · exact (digitChar_ne_space _).symm hmem
      · exact hds hmem

lemma toString_data (n : Nat) : (toString n).data = Nat.toDigits 10 n := by
  simp [toString, Nat.repr, List.asString]

lemma toString_zero : toString (0 : Nat) = "0" := by
  decide

lemma toString_data_no_space (n : Nat) : ' ' ∉ (toString n).data := by
  rw [toString_data, Nat.toDigits]
  exact toDigitsCore_no_space 10 (n + 1) n [] (by simp)

lemma space_data : (" " : String).data = [' '] := by
  decide

lemma string_intercalate_data (sep : String) (xs : List String) :
    (String.intercalate sep xs).data = List.intercalate sep.data (xs.map (·.data)) := by
  induction xs with
  | nil =>
    simp [String.intercalate, List.intercalate]
  | cons a as ih =>
    cases as with
    | nil =>
      simp [String.intercalate, String.intercalate.go, List.intercalate]
    | cons b bs =>
      rw [intercalate_cons sep a (b :: bs) (by simp)]
      simp only [List.map_cons, String.data_append, ih]
      simp [List.intercalate, List.intersperse_cons₂, List.flatten]

theorem stringSequence_data (n : Nat) :
    (stringSequence n).data =
      List.intercalate [' '] ((List.range (n + 1)).map (fun k => (toString k).data)) := by
  unfold stringSequence
  rw [string_intercalate_data, space_data]
  simp only [List.map_map]
  refine congrArg (List.intercalate [' ']) ?_
  refine List.map_congr_left ?_
  intro k _hk
  rfl

theorem stringSequence_split_data (n : Nat) :
    (stringSequence n).data.splitOn ' ' =
      (List.range (n + 1)).map (fun k => (toString k).data) := by
  rw [stringSequence_data]
  apply List.splitOn_intercalate
  · intro l hl
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hl
    exact toString_data_no_space k
  · intro h
    have := congrArg List.length h
    simp [List.length_map, List.length_range] at this

def zero_prop : Prop := stringSequence 0 = "0"

theorem zero_thm : zero_prop := by
  unfold zero_prop
  exact stringSequence_zero

def succ_prop (n : Nat) : Prop :=
  stringSequence (n + 1) = stringSequence n ++ " " ++ toString (n + 1)

theorem succ_thm (n : Nat) : succ_prop n := by
  unfold succ_prop
  exact stringSequence_succ n

def join_prop (n : Nat) : Prop :=
  stringSequence n = String.intercalate " " ((List.range (n + 1)).map toString)

theorem join_thm (n : Nat) : join_prop n := by
  unfold join_prop stringSequence
  rfl

def split_prop (n : Nat) : Prop :=
  (stringSequence n).data.splitOn ' ' =
    (List.range (n + 1)).map (fun k => (toString k).data)

theorem split_thm (n : Nat) : split_prop n := by
  unfold split_prop
  exact stringSequence_split_data n

def token_count_prop (n : Nat) : Prop :=
  ((stringSequence n).data.splitOn ' ').length = n + 1

theorem token_count_thm (n : Nat) : token_count_prop n := by
  unfold token_count_prop
  rw [stringSequence_split_data, List.length_map, List.length_range]

def starts_with_zero_prop (n : Nat) : Prop :=
  "0".data <+: (stringSequence n).data

theorem starts_with_zero_thm (n : Nat) : starts_with_zero_prop n := by
  unfold starts_with_zero_prop
  induction n with
  | zero =>
    rw [stringSequence_zero]
  | succ n ih =>
    rw [stringSequence_succ]
    have hdata :
        (stringSequence n ++ " " ++ toString (n + 1)).data =
          (stringSequence n).data ++ (" " ++ toString (n + 1)).data := by
      simp [String.data_append]
    rw [hdata]
    exact List.IsPrefix.trans ih (List.prefix_append _ _)

def ends_with_n_prop (n : Nat) : Prop :=
  (toString n).data <:+ (stringSequence n).data

theorem ends_with_n_thm (n : Nat) : ends_with_n_prop n := by
  unfold ends_with_n_prop
  induction n with
  | zero =>
    rw [stringSequence_zero, toString_zero]
  | succ n _ih =>
    rw [stringSequence_succ]
    simp only [String.data_append]
    exact List.suffix_append _ _

def space_count_prop (n : Nat) : Prop :=
  (stringSequence n).data.count ' ' = n

theorem space_count_thm (n : Nat) : space_count_prop n := by
  unfold space_count_prop
  induction n with
  | zero =>
    rw [stringSequence_zero]
    decide
  | succ n ih =>
    rw [stringSequence_succ]
    simp only [String.data_append, List.count_append, ih]
    have hspace : (" " : String).data.count ' ' = 1 := by decide
    have htok : (toString (n + 1)).data.count ' ' = 0 :=
      List.count_eq_zero.mpr (toString_data_no_space (n + 1))
    rw [hspace, htok]

def token_at_prop (n : Nat) : Prop :=
  ∀ i, i ≤ n → ((stringSequence n).data.splitOn ' ').getD i [] = (toString i).data

theorem token_at_thm (n : Nat) : token_at_prop n := by
  intro i hi
  have hi' : i < n + 1 := Nat.lt_succ_of_le hi
  unfold List.getD
  rw [stringSequence_split_data]
  simp [List.getElem?_map, List.getElem?_range hi']

theorem example_three_thm : stringSequence 3 = "0 1 2 3" := by decide
theorem example_five_thm : stringSequence 5 = "0 1 2 3 4 5" := by decide
theorem example_ten_thm : stringSequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by decide

/-- The recurrence implemented by the Python join is unique. -/
def rec_spec_prop (f : Nat → String) : Prop :=
  f 0 = "0" ∧ ∀ n, f (n + 1) = f n ++ " " ++ toString (n + 1)

theorem stringSequence_rec_thm : rec_spec_prop stringSequence := by
  refine ⟨stringSequence_zero, stringSequence_succ⟩

theorem rec_unique_thm (f : Nat → String) (h : rec_spec_prop f) :
    ∀ n, f n = stringSequence n := by
  intro n
  induction n with
  | zero =>
    rw [h.1, stringSequence_zero]
  | succ n ih =>
    rw [h.2 n, stringSequence_succ, ih]

def Post_prop (n : Nat) : Prop :=
  join_prop n ∧ split_prop n ∧ token_count_prop n ∧ starts_with_zero_prop n ∧
    ends_with_n_prop n ∧ space_count_prop n ∧ token_at_prop n

-- Property-based tests. Each `_prop` has an executable check.

#eval Plausible.Testable.check
  (∀ n : Nat, stringSequence n = String.intercalate " " ((List.range (n + 1)).map toString))

example : (List.range 30).all (fun n =>
    stringSequence n == String.intercalate " " ((List.range (n + 1)).map toString)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ n : Nat,
    (stringSequence n).data.splitOn ' ' =
      (List.range (n + 1)).map (fun k => (toString k).data))

example : (List.range 25).all (fun n =>
    (stringSequence n).data.splitOn ' ' ==
      (List.range (n + 1)).map (fun k => (toString k).data)) = true := by
  native_decide

-- Executable `String.splitOn` round-trip, matching Python `str.split(' ')`.
-- Proved theorems use `List.splitOn` on `.data` because `String.splitOnAux` is irreducible.
example : (List.range 25).all (fun n =>
    (stringSequence n).splitOn " " == (List.range (n + 1)).map toString) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ n : Nat, ((stringSequence n).data.splitOn ' ').length = n + 1)

example : (List.range 30).all (fun n =>
    ((stringSequence n).data.splitOn ' ').length == n + 1) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ n : Nat, List.isPrefixOf "0".data (stringSequence n).data = true)

example : (List.range 40).all (fun n =>
    List.isPrefixOf "0".data (stringSequence n).data) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ n : Nat, List.isSuffixOf (toString n).data (stringSequence n).data = true)

example : (List.range 30).all (fun n =>
    List.isSuffixOf (toString n).data (stringSequence n).data) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ n : Nat, (stringSequence n).data.count ' ' = n)

example : (List.range 30).all (fun n =>
    (stringSequence n).data.count ' ' == n) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ n i : Nat, i ≤ n →
    ((stringSequence n).data.splitOn ' ').getD i [] = (toString i).data)

example : (List.range 20).all (fun n =>
    (List.range (n + 1)).all (fun i =>
      ((stringSequence n).data.splitOn ' ').getD i [] == (toString i).data)) = true := by
  native_decide

#eval Plausible.Testable.check (stringSequence 0 = "0")

#eval Plausible.Testable.check
  (∀ n : Nat, stringSequence (n + 1) = stringSequence n ++ " " ++ toString (n + 1))

example : (List.range 30).all (fun n =>
    stringSequence (n + 1) == stringSequence n ++ " " ++ toString (n + 1)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ n : Nat,
    (stringSequence n).data.splitOn ' ' =
        (List.range (n + 1)).map (fun k => (toString k).data) ∧
      List.isPrefixOf "0".data (stringSequence n).data = true ∧
      List.isSuffixOf (toString n).data (stringSequence n).data = true ∧
      (stringSequence n).data.count ' ' = n ∧
      ((stringSequence n).data.splitOn ' ').length = n + 1)

example : (List.range 20).all (fun n =>
    ((stringSequence n).data.splitOn ' ' ==
        (List.range (n + 1)).map (fun k => (toString k).data)) &&
    List.isPrefixOf "0".data (stringSequence n).data &&
    List.isSuffixOf (toString n).data (stringSequence n).data &&
    ((stringSequence n).data.count ' ' == n) &&
    (((stringSequence n).data.splitOn ' ').length == n + 1)) = true := by
  native_decide

-- PBT: not executable (quantifies over all functions Nat → String; no sampler)

theorem correctness_thm (n : Nat) (_h : Pre n) : Post_prop n := by
  exact ⟨join_thm n, split_thm n, token_count_thm n, starts_with_zero_thm n,
    ends_with_n_thm n, space_count_thm n, token_at_thm n⟩

/-- Mutable accumulation of decimal tokens, then join. Mirrors the Python list then `' '.join`. -/
def buildPartsFrom (xs : List Nat) (init : List String) : List String :=
  Id.run do
    let mut parts : List String := init
    for x in xs do
      parts := parts ++ [toString x]
    return parts

theorem buildPartsFrom_eq (xs : List Nat) (init : List String) :
    buildPartsFrom xs init = init ++ xs.map toString := by
  induction xs generalizing init with
  | nil =>
    simp [buildPartsFrom, Id.run, pure, Id.instMonad]
  | cons x xs ih =>
    have hstep :
        buildPartsFrom (x :: xs) init = buildPartsFrom xs (init ++ [toString x]) := by
      simp [buildPartsFrom, Id.run, bind, pure, Id.instMonad, List.forIn_cons]
    rw [hstep, ih, List.map_cons, List.append_assoc, List.singleton_append]

def stringSequenceImp (n : Nat) : String :=
  Id.run do
    let mut parts : List String := []
    for x in List.range (n + 1) do
      parts := parts ++ [toString x]
    return String.intercalate " " parts

abbrev string_sequence_imp := stringSequenceImp

theorem stringSequenceImp_eq_build (n : Nat) :
    stringSequenceImp n =
      String.intercalate " " (buildPartsFrom (List.range (n + 1)) []) := by
  unfold stringSequenceImp buildPartsFrom
  rfl

example : stringSequenceImp 0 = "0" := by native_decide
example : stringSequenceImp 3 = "0 1 2 3" := by native_decide
example : stringSequenceImp 5 = "0 1 2 3 4 5" := by native_decide
example : stringSequenceImp 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval stringSequenceImp 0
#eval stringSequenceImp 5
#eval stringSequenceImp 10

def equiv_prop (n : Nat) : Prop := stringSequence n = stringSequenceImp n

theorem equivalence_thm (n : Nat) : equiv_prop n := by
  unfold equiv_prop
  rw [stringSequenceImp_eq_build, buildPartsFrom_eq]
  simp [stringSequence]

#eval Plausible.Testable.check (∀ n : Nat, stringSequence n = stringSequenceImp n)

example : (List.range 25).all (fun n => stringSequence n == stringSequenceImp n) = true := by
  native_decide

/-- Python `int` entry point. `range(n + 1)` is empty whenever `n < 0`. -/
def stringSequenceInt (n : Int) : String :=
  if n < 0 then "" else stringSequence n.toNat

def PreInt (_n : Int) : Prop := True

def negative_prop (n : Int) : Prop := n < 0 → stringSequenceInt n = ""

theorem negative_thm (n : Int) : negative_prop n := by
  intro h
  simp [stringSequenceInt, h]

def nonneg_prop (n : Int) : Prop :=
  0 ≤ n → stringSequenceInt n = stringSequence n.toNat

theorem nonneg_thm (n : Int) : nonneg_prop n := by
  intro h
  have hn : ¬ n < 0 := Int.not_lt.mpr h
  simp [stringSequenceInt, hn]

def PostInt_prop (n : Int) : Prop :=
  (n < 0 → stringSequenceInt n = "") ∧
    (0 ≤ n → stringSequenceInt n = stringSequence n.toNat ∧ Post_prop n.toNat)

theorem correctness_int_thm (n : Int) (_h : PreInt n) : PostInt_prop n := by
  refine ⟨negative_thm n, ?_⟩
  intro hn
  exact ⟨nonneg_thm n hn, correctness_thm n.toNat trivial⟩

#eval Plausible.Testable.check (∀ n : Nat, stringSequenceInt (-(n + 1) : Int) = "")

#eval Plausible.Testable.check (∀ n : Nat, stringSequenceInt (n : Int) = stringSequence n)

example : (List.range 15).all (fun i =>
    stringSequenceInt (i : Int) == stringSequence i) = true := by
  native_decide

example : (List.range 15).all (fun i =>
    stringSequenceInt (-(i + 1) : Int) == "") = true := by
  native_decide


end humaneval_15_string_sequence
