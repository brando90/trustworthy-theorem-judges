import Mathlib

/-!
# HumanEval/15: string_sequence

Translate the Python function `string_sequence(n: int) -> str`, which returns a string
containing space-delimited numbers starting from `0` up to `n` inclusive:
`' '.join([str(x) for x in range(n + 1)])`.

This file provides:
1. The functional implementation `string_sequence`.
2. Ground unit tests via `example ... := by native_decide` and `#eval`.
3. Pre-condition `Pre`, semantic property propositions (`*_prop`), and kernel-checked theorems (`*_thm`).
4. Complete post-condition `Post_prop` combining all properties, property-based tests (Plausible and bounded), and the total correctness theorem `string_sequence_correct`.
5. An imperative implementation `string_sequence_imp` using `Id.run do` with mutable state, tests, and the functional-imperative equivalence theorem `string_sequence_imp_eq`.
-/

namespace humaneval_15_string_sequence

/-! ## 1. Functional Implementation -/

/-- Return a string containing space-delimited numbers starting from `0` up to `n` inclusive. -/
def string_sequence (n : Nat) : String :=
  String.intercalate " " ((List.range (n + 1)).map toString)

/-! ## 2. Unit Tests -/

example : string_sequence 0 = "0" := by native_decide
example : string_sequence 1 = "0 1" := by native_decide
example : string_sequence 3 = "0 1 2 3" := by native_decide
example : string_sequence 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval string_sequence 0
#eval string_sequence 3
#eval string_sequence 5
#eval string_sequence 10

/-! ## 3. Pre-condition -/

/-- Pre-condition for `string_sequence`: all natural numbers `n` are valid inputs. -/
def Pre (_n : Nat) : Prop := True

/-! ## 4. Helper Lemmas -/

/-- Appending a singleton list inside `String.intercalate.go` appends `sep ++ y` to the result. -/
theorem intercalate_go_append_singleton (acc sep y : String) (xs : List String) :
    String.intercalate.go acc sep (xs ++ [y]) =
      String.intercalate.go acc sep xs ++ sep ++ y := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append, String.intercalate.go]
    exact ih (acc ++ sep ++ a)

/-- Base case: `string_sequence 0 = "0"`. -/
theorem string_sequence_zero : string_sequence 0 = "0" := rfl

/-- Step recurrence: `string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1)`. -/
theorem string_sequence_succ (n : Nat) :
    string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1) := by
  unfold string_sequence
  rw [List.range_succ, List.map_append, List.map_singleton]
  rw [List.range_succ_eq_map, List.map_cons]
  simp only [List.cons_append, String.intercalate]
  exact intercalate_go_append_singleton _ _ _ _

/-- `Nat.toDigitsCore` preserves non-emptiness of the accumulator `ds`. -/
theorem toDigitsCore_ne_nil_of_ne_nil (base fuel n : Nat) (ds : List Char) (h : ds ≠ []) :
    Nat.toDigitsCore base fuel n ds ≠ [] := by
  induction fuel generalizing n ds with
  | zero => exact h
  | succ fuel ih =>
    unfold Nat.toDigitsCore
    simp only []
    split
    · exact List.cons_ne_nil _ _
    · exact ih _ _ (List.cons_ne_nil _ _)

/-- `Nat.toDigits 10 k` is never empty. -/
theorem toDigits_ne_nil (k : Nat) : Nat.toDigits 10 k ≠ [] := by
  unfold Nat.toDigits Nat.toDigitsCore
  simp only []
  split
  · exact List.cons_ne_nil _ _
  · exact toDigitsCore_ne_nil_of_ne_nil 10 k (k / 10) _ (List.cons_ne_nil _ _)

/-- The string representation of any natural number `k` has positive length. -/
theorem toString_nat_length_pos (k : Nat) : 0 < (toString k).length := by
  change 0 < (Nat.toDigits 10 k).length
  exact List.length_pos_of_ne_nil (toDigits_ne_nil k)

/-- For any natural number `n`, `(n % 10).digitChar` is an ASCII decimal digit. -/
theorem digitChar_mod_ten_isDigit (n : Nat) : (n % 10).digitChar.isDigit = true := by
  have h : n % 10 < 10 := Nat.mod_lt n (by decide)
  generalize n % 10 = m at h
  interval_cases m <;> rfl

/-- `Nat.toDigitsCore 10` preserves the invariant that all characters in `ds` are decimal digits. -/
theorem toDigitsCore_all_isDigit (fuel n : Nat) (ds : List Char)
    (hds : ∀ c ∈ ds, c.isDigit = true) :
    ∀ c ∈ Nat.toDigitsCore 10 fuel n ds, c.isDigit = true := by
  induction fuel generalizing n ds with
  | zero => exact hds
  | succ fuel ih =>
    unfold Nat.toDigitsCore
    simp only []
    have hd : (n % 10).digitChar.isDigit = true := digitChar_mod_ten_isDigit n
    have hds' : ∀ c ∈ (n % 10).digitChar :: ds, c.isDigit = true := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hd
      · exact hds c hc'
    split
    · exact hds'
    · exact ih _ _ hds'

/-- Every character in `toString k` (for `k : Nat`) is a decimal digit. -/
theorem toString_nat_all_isDigit (k : Nat) : ∀ c ∈ (toString k).toList, c.isDigit = true := by
  change ∀ c ∈ Nat.toDigits 10 k, c.isDigit = true
  exact toDigitsCore_all_isDigit (k + 1) k [] (by intro _ hc; contradiction)

/-- A space character `' '` never appears in `toString k` for `k : Nat`. -/
theorem space_not_mem_toString_nat (k : Nat) : ' ' ∉ (toString k).toList := by
  intro h
  have hd := toString_nat_all_isDigit k ' ' h
  revert hd
  decide

/-- The count of `' '` in `(toString k).toList` is `0`. -/
theorem toString_nat_count_space (k : Nat) : (toString k).toList.count ' ' = 0 :=
  List.count_eq_zero.mpr (space_not_mem_toString_nat k)

/-- Boolean non-equality with `' '` for every character of `(toString k).toList`. -/
theorem toString_nat_not_beq_space (k : Nat) :
    ∀ c ∈ (toString k).toList, (c == ' ') = false := by
  intro c hc
  have hd := toString_nat_all_isDigit k c hc
  cases h : (c == ' ')
  · rfl
  · have hc_eq : c = ' ' := beq_iff_eq.mp h
    subst hc_eq
    revert hd
    decide

/-- Definitional lemma for `String.toList` over string concatenation. -/
theorem string_toList_append (a b : String) : (a ++ b).toList = a.toList ++ b.toList := rfl

/-- `List.splitOnP.go` on a list `w` containing no separator produces `[acc.reverse ++ w]`. -/
theorem splitOnP_go_no_sep {α : Type*} (P : α → Bool) (w acc : List α)
    (hw : ∀ c ∈ w, P c = false) :
    List.splitOnP.go P w acc = [acc.reverse ++ w] := by
  induction w generalizing acc with
  | nil => simp [List.splitOnP.go]
  | cons a t ih =>
    have ha : P a = false := hw a List.mem_cons_self
    have ht : ∀ c ∈ t, P c = false := fun c hc => hw c (List.mem_cons_of_mem a hc)
    simp only [List.splitOnP.go, ha, Bool.false_eq_true, ↓reduceIte]
    rw [ih (a :: acc) ht]
    simp [List.append_assoc]

/-- Appending `sep :: w` (where `P sep = true` and `w` has no separator) appends `w` to `List.splitOnP.go`. -/
theorem splitOnP_go_append_sep {α : Type*} (P : α → Bool) (xs w acc : List α) (sep : α)
    (hsep : P sep = true) (hw : ∀ c ∈ w, P c = false) :
    List.splitOnP.go P (xs ++ sep :: w) acc = List.splitOnP.go P xs acc ++ [w] := by
  induction xs generalizing acc with
  | nil =>
    simp only [List.nil_append, List.splitOnP.go, hsep, ↓reduceIte]
    rw [splitOnP_go_no_sep P w [] hw]
    simp
  | cons a t ih =>
    simp only [List.cons_append, List.splitOnP.go]
    split
    · rw [ih [], List.cons_append]
    · exact ih (a :: acc)

/-- `List.intersperse` on `xs ++ [y]` for non-empty `xs`. -/
theorem list_intersperse_append_singleton {α : Type*} (sep : α) (xs : List α) (y : α) (h : xs ≠ []) :
    List.intersperse sep (xs ++ [y]) = List.intersperse sep xs ++ [sep, y] := by
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs =>
      simp only [List.cons_append, List.intersperse_cons₂]
      rw [← List.cons_append, ih (List.cons_ne_nil b bs)]

/-- `List.intercalate` on `xss ++ [ys]` for non-empty `xss`. -/
theorem list_intercalate_append_singleton {α : Type*} (sep : List α) (xss : List (List α)) (ys : List α)
    (h : xss ≠ []) :
    List.intercalate sep (xss ++ [ys]) = List.intercalate sep xss ++ sep ++ ys := by
  simp only [List.intercalate]
  rw [list_intersperse_append_singleton sep xss ys h, List.flatten_append]
  simp [List.append_assoc]

/-! ## 5. Property Propositions and Theorems -/

/-- Property 1 (Base Case): When `n = 0`, the output string is `"0"`. -/
def zero_prop (n : Nat) (result : String) : Prop :=
  n = 0 → result = "0"

theorem zero_thm (n : Nat) : zero_prop n (string_sequence n) := by
  intro h
  subst h
  rfl

/-- Property 2 (Recurrence / Inductive Characterization):
For `n = 0`, the result is `"0"`; for `n > 0`, the result is `string_sequence (n - 1) ++ " " ++ toString n`. -/
def recurrence_prop (n : Nat) (result : String) : Prop :=
  if n = 0 then result = "0" else result = string_sequence (n - 1) ++ " " ++ toString n

theorem recurrence_thm (n : Nat) : recurrence_prop n (string_sequence n) := by
  unfold recurrence_prop
  cases n with
  | zero => rfl
  | succ k =>
    simp [string_sequence_succ]

/-- Property 3 (Intercalation Specification):
The output equals joining the string representations of `0 .. n` with `" "`, both at `String` and `List Char` levels. -/
def intercalate_prop (n : Nat) (result : String) : Prop :=
  result = String.intercalate " " ((List.range (n + 1)).map toString) ∧
    result.toList = List.intercalate [' '] ((List.range (n + 1)).map (fun k => (toString k).toList))

theorem string_sequence_toList_eq_intercalate (n : Nat) :
    (string_sequence n).toList =
      List.intercalate [' '] ((List.range (n + 1)).map (fun k => (toString k).toList)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ (n := n + 1), List.map_append, List.map_singleton]
    have hne : List.map (fun k => (toString k).toList) (List.range (n + 1)) ≠ [] := by
      simp [List.range_eq_nil]
    rw [list_intercalate_append_singleton [' '] _ _ hne]
    rw [string_sequence_succ, string_toList_append, string_toList_append, ih]
    rfl

theorem intercalate_thm (n : Nat) : intercalate_prop n (string_sequence n) :=
  ⟨rfl, string_sequence_toList_eq_intercalate n⟩

/-- Property 4 (Space-Delimited Tokens / Split Specification):
Splitting the character list of `result` on `' '` yields the exact sequence of `n + 1` number strings
`"0", "1", ..., toString n`, with token count `n + 1` and `i`-th token `toString i` for all `i ≤ n`. -/
def tokens_prop (n : Nat) (result : String) : Prop :=
  (result.toList.splitOn ' ').map List.asString = (List.range (n + 1)).map toString ∧
    (result.toList.splitOn ' ').length = n + 1 ∧
    ∀ i ≤ n, ((result.toList.splitOn ' ').map List.asString)[i]? = some (toString i)

theorem string_sequence_splitOn_space (n : Nat) :
    (string_sequence n).toList.splitOn ' ' =
      (List.range (n + 1)).map (fun k => (toString k).toList) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ (n := n + 1), List.map_append, List.map_singleton]
    rw [string_sequence_succ, string_toList_append, string_toList_append]
    have hsp : (" " : String).toList = [' '] := rfl
    rw [hsp, List.append_assoc, List.singleton_append]
    unfold List.splitOn List.splitOnP
    rw [splitOnP_go_append_sep (fun x => x == ' ') (string_sequence n).toList (toString (n + 1)).toList [] ' ' rfl
      (toString_nat_not_beq_space (n + 1))]
    exact congrArg (· ++ [(toString (n + 1)).toList]) ih

theorem string_sequence_splitOn_asString (n : Nat) :
    ((string_sequence n).toList.splitOn ' ').map List.asString =
      (List.range (n + 1)).map toString := by
  rw [string_sequence_splitOn_space, List.map_map]
  rfl

theorem tokens_thm (n : Nat) : tokens_prop n (string_sequence n) := by
  refine ⟨string_sequence_splitOn_asString n, ?_, ?_⟩
  · rw [string_sequence_splitOn_space, List.length_map, List.length_range]
  · intro i hi
    rw [string_sequence_splitOn_asString]
    have hlt : i < n + 1 := Nat.lt_succ_of_le hi
    simp [hlt]

/-- Property 5 (Space Count):
The output string contains exactly `n` space characters `' '` separating the `n + 1` numbers. -/
def space_count_prop (n : Nat) (result : String) : Prop :=
  result.toList.count ' ' = n

theorem space_count_thm (n : Nat) : space_count_prop n (string_sequence n) := by
  unfold space_count_prop
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [string_sequence_succ, string_toList_append, string_toList_append]
    rw [List.count_append, List.count_append, ih, toString_nat_count_space]
    rfl

/-- Property 6 (Valid Character Set):
Every character in `result` is either a single space `' '` or an ASCII decimal digit. -/
def valid_chars_prop (_n : Nat) (result : String) : Prop :=
  ∀ c ∈ result.toList, c = ' ' ∨ c.isDigit = true

theorem valid_chars_thm (n : Nat) : valid_chars_prop n (string_sequence n) := by
  unfold valid_chars_prop
  induction n with
  | zero => decide
  | succ n ih =>
    intro c hc
    rw [string_sequence_succ, string_toList_append, string_toList_append] at hc
    rcases List.mem_append.mp hc with hc1 | hc2
    · rcases List.mem_append.mp hc1 with hc1a | hc1b
      · exact ih c hc1a
      · left
        have : (" " : String).toList = [' '] := rfl
        rw [this, List.mem_singleton] at hc1b
        exact hc1b
    · right
      exact toString_nat_all_isDigit (n + 1) c hc2

/-- Property 7 (Non-emptiness and Length Formula / Lower Bound):
The output is non-empty, its length is at least `2 * n + 1`, and its exact length equals the sum of
the lengths of `toString 0 .. toString n` plus `n` spaces. -/
def length_prop (n : Nat) (result : String) : Prop :=
  result ≠ "" ∧
    0 < result.length ∧
    2 * n + 1 ≤ result.length ∧
    result.length = ((List.range (n + 1)).map (fun k => (toString k).length)).sum + n

theorem string_sequence_length_eq (n : Nat) :
    (string_sequence n).length =
      ((List.range (n + 1)).map (fun k => (toString k).length)).sum + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ (n := n + 1), List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    rw [string_sequence_succ, String.length_append, String.length_append, ih]
    have hsp : (" " : String).length = 1 := rfl
    omega

theorem string_sequence_length_ge (n : Nat) :
    2 * n + 1 ≤ (string_sequence n).length := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [string_sequence_succ, String.length_append, String.length_append]
    have hpos : 0 < (toString (n + 1)).length := toString_nat_length_pos (n + 1)
    have hsp : (" " : String).length = 1 := rfl
    omega

theorem length_thm (n : Nat) : length_prop n (string_sequence n) := by
  have hge : 2 * n + 1 ≤ (string_sequence n).length := string_sequence_length_ge n
  have hpos : 0 < (string_sequence n).length := by omega
  have hne : string_sequence n ≠ "" := by
    intro h
    rw [h] at hpos
    contradiction
  exact ⟨hne, hpos, hge, string_sequence_length_eq n⟩

/-- Property 8 (Prefix and Suffix Boundary Specification):
`result` starts with `"0"` and ends with `toString n`. -/
def boundary_prop (n : Nat) (result : String) : Prop :=
  ['0'].isPrefixOf result.toList = true ∧
    (toString n).toList.isSuffixOf result.toList = true ∧
    (∃ suffix : String, result = "0" ++ suffix) ∧
    (∃ pref : String, result = pref ++ toString n)

theorem string_sequence_prefix_of_le {m n : Nat} (h : m ≤ n) :
    ∃ suffix : String, string_sequence n = string_sequence m ++ suffix := by
  induction h with
  | refl => exact ⟨"", (String.append_empty _).symm⟩
  | step _ ih =>
    rename_i k _
    rcases ih with ⟨s, hs⟩
    refine ⟨s ++ " " ++ toString (k + 1), ?_⟩
    simp [string_sequence_succ, hs, String.append_assoc]

theorem string_sequence_isPrefixOf_of_le {m n : Nat} (h : m ≤ n) :
    (string_sequence m).toList.isPrefixOf (string_sequence n).toList = true := by
  rw [List.isPrefixOf_iff_prefix]
  rcases string_sequence_prefix_of_le h with ⟨s, hs⟩
  refine ⟨s.toList, ?_⟩
  rw [hs, string_toList_append]

theorem string_sequence_starts_with_zero (n : Nat) :
    ∃ suffix : String, string_sequence n = "0" ++ suffix := by
  have := string_sequence_prefix_of_le (Nat.zero_le n)
  simpa [string_sequence_zero] using this

theorem string_sequence_ends_with_n (n : Nat) :
    ∃ pref : String, string_sequence n = pref ++ toString n := by
  cases n with
  | zero => exact ⟨"", rfl⟩
  | succ k => exact ⟨string_sequence k ++ " ", string_sequence_succ k⟩

theorem boundary_thm (n : Nat) : boundary_prop n (string_sequence n) := by
  refine ⟨?_, ?_, string_sequence_starts_with_zero n, string_sequence_ends_with_n n⟩
  · have := string_sequence_isPrefixOf_of_le (Nat.zero_le n)
    simpa [string_sequence_zero] using this
  · rw [List.isSuffixOf_iff_suffix]
    rcases string_sequence_ends_with_n n with ⟨p, hp⟩
    refine ⟨p.toList, ?_⟩
    rw [hp, string_toList_append]

/-- Property 9 (Monotonicity and Injectivity):
For every `m ≤ n`, `string_sequence m` is a prefix of `result` and has length at most `result.length`;
for every `m < n`, `(string_sequence m).length < result.length`. -/
def monotonicity_prop (n : Nat) (result : String) : Prop :=
  (∀ m ≤ n, (string_sequence m).toList.isPrefixOf result.toList = true ∧
    (string_sequence m).length ≤ result.length) ∧
  (∀ m < n, (string_sequence m).length < result.length)

theorem string_sequence_length_strict_mono {m n : Nat} (h : m < n) :
    (string_sequence m).length < (string_sequence n).length := by
  induction h with
  | refl =>
    rw [string_sequence_succ, String.length_append, String.length_append]
    have hpos : 0 < (toString (m + 1)).length := toString_nat_length_pos (m + 1)
    have hsp : (" " : String).length = 1 := rfl
    omega
  | step _ ih =>
    rename_i k _
    rw [string_sequence_succ, String.length_append, String.length_append]
    have hpos : 0 < (toString (k + 1)).length := toString_nat_length_pos (k + 1)
    have hsp : (" " : String).length = 1 := rfl
    omega

theorem string_sequence_length_mono {m n : Nat} (h : m ≤ n) :
    (string_sequence m).length ≤ (string_sequence n).length := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (string_sequence_length_strict_mono hlt)

theorem string_sequence_injective {m n : Nat} :
    string_sequence m = string_sequence n ↔ m = n := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy m n with hlt | rfl | hgt
    · have hlen := string_sequence_length_strict_mono hlt
      rw [h] at hlen
      exact absurd hlen (Nat.lt_irrefl _)
    · rfl
    · have hlen := string_sequence_length_strict_mono hgt
      rw [h] at hlen
      exact absurd hlen (Nat.lt_irrefl _)
  · intro h
    subst h
    rfl

theorem monotonicity_thm (n : Nat) : monotonicity_prop n (string_sequence n) := by
  refine ⟨fun m hm => ⟨string_sequence_isPrefixOf_of_le hm, string_sequence_length_mono hm⟩,
    fun m hm => string_sequence_length_strict_mono hm⟩

/-! ## 6. Post-condition -/

/-- Complete post-condition for `string_sequence` as the conjunction of all semantic properties. -/
def Post_prop (n : Nat) (result : String) : Prop :=
  zero_prop n result ∧
  recurrence_prop n result ∧
  intercalate_prop n result ∧
  tokens_prop n result ∧
  space_count_prop n result ∧
  valid_chars_prop n result ∧
  length_prop n result ∧
  boundary_prop n result ∧
  monotonicity_prop n result

/-! ## 7. Property-Based Tests -/

-- Executable Boolean checkers for each property proposition and the post-condition
/-- Executable check for `zero_prop`. -/
def check_zero_prop (n : Nat) : Bool :=
  !(n == 0) || string_sequence n == "0"

/-- Executable check for `recurrence_prop`. -/
def check_recurrence_prop (n : Nat) : Bool :=
  if n == 0 then
    string_sequence n == "0"
  else
    string_sequence n == string_sequence (n - 1) ++ " " ++ toString n

/-- Executable check for `intercalate_prop`. -/
def check_intercalate_prop (n : Nat) : Bool :=
  let res := string_sequence n
  res == String.intercalate " " ((List.range (n + 1)).map toString) &&
    res.toList == List.intercalate [' '] ((List.range (n + 1)).map (fun k => (toString k).toList))

/-- Executable check for `tokens_prop`. -/
def check_tokens_prop (n : Nat) : Bool :=
  let res := string_sequence n
  let toks := (res.toList.splitOn ' ').map List.asString
  toks == (List.range (n + 1)).map toString &&
    (res.toList.splitOn ' ').length == n + 1 &&
    (List.range (n + 1)).all (fun i => toks[i]? == some (toString i))

/-- Executable check for `space_count_prop`. -/
def check_space_count_prop (n : Nat) : Bool :=
  (string_sequence n).toList.count ' ' == n

/-- Executable check for `valid_chars_prop`. -/
def check_valid_chars_prop (n : Nat) : Bool :=
  (string_sequence n).toList.all (fun c => c == ' ' || c.isDigit)

/-- Executable check for `length_prop`. -/
def check_length_prop (n : Nat) : Bool :=
  let res := string_sequence n
  res != "" &&
    0 < res.length &&
    2 * n + 1 ≤ res.length &&
    res.length == ((List.range (n + 1)).map (fun k => (toString k).length)).sum + n

/-- Executable check for `boundary_prop`. -/
def check_boundary_prop (n : Nat) : Bool :=
  let res := string_sequence n
  ['0'].isPrefixOf res.toList &&
    (toString n).toList.isSuffixOf res.toList

/-- Executable check for `monotonicity_prop`. -/
def check_monotonicity_prop (n : Nat) : Bool :=
  let res := string_sequence n
  (List.range (n + 1)).all (fun m =>
    (string_sequence m).toList.isPrefixOf res.toList &&
      (string_sequence m).length ≤ res.length) &&
  (List.range n).all (fun m =>
    (string_sequence m).length < res.length)

/-- Executable check for `Post_prop`. -/
def check_post_prop (n : Nat) : Bool :=
  check_zero_prop n &&
  check_recurrence_prop n &&
  check_intercalate_prop n &&
  check_tokens_prop n &&
  check_space_count_prop n &&
  check_valid_chars_prop n &&
  check_length_prop n &&
  check_boundary_prop n &&
  check_monotonicity_prop n

-- Randomized Property-Based Tests via Plausible
#eval Plausible.Testable.check (∀ n : Nat, check_zero_prop n = true)
#eval Plausible.Testable.check (∀ n : Nat, check_recurrence_prop n = true)
#eval Plausible.Testable.check (∀ n : Nat, check_intercalate_prop n = true)
#eval Plausible.Testable.check (∀ n : Nat, check_tokens_prop n = true)
#eval Plausible.Testable.check (∀ n : Nat, check_space_count_prop n = true)
#eval Plausible.Testable.check (∀ n : Nat, check_valid_chars_prop n = true)
#eval Plausible.Testable.check (∀ n : Nat, check_length_prop n = true)
#eval Plausible.Testable.check (∀ n : Nat, check_boundary_prop n = true)
#eval Plausible.Testable.check (∀ n : Nat, check_monotonicity_prop n = true)
#eval Plausible.Testable.check (∀ n : Nat, check_post_prop n = true)

-- Bounded Exhaustive Property-Based Tests over [0, 30)
example : (List.range 30).all check_zero_prop = true := by native_decide
example : (List.range 30).all check_recurrence_prop = true := by native_decide
example : (List.range 30).all check_intercalate_prop = true := by native_decide
example : (List.range 30).all check_tokens_prop = true := by native_decide
example : (List.range 30).all check_space_count_prop = true := by native_decide
example : (List.range 30).all check_valid_chars_prop = true := by native_decide
example : (List.range 30).all check_length_prop = true := by native_decide
example : (List.range 30).all check_boundary_prop = true := by native_decide
example : (List.range 30).all check_monotonicity_prop = true := by native_decide
example : (List.range 30).all check_post_prop = true := by native_decide

/-! ## 8. Total Correctness Theorem (Pre -> Post) -/

/-- Total correctness theorem: for any `n : Nat` satisfying `Pre n`, `string_sequence n` satisfies `Post_prop`. -/
theorem string_sequence_correct (n : Nat) (_hPre : Pre n) :
    Post_prop n (string_sequence n) :=
  ⟨zero_thm n,
   recurrence_thm n,
   intercalate_thm n,
   tokens_thm n,
   space_count_thm n,
   valid_chars_thm n,
   length_thm n,
   boundary_thm n,
   monotonicity_thm n⟩

/-! ## 9. Imperative Implementation -/

/-- Imperative implementation of `string_sequence` using `Id.run do` with mutable state. -/
def string_sequence_imp (n : Nat) : String := Id.run do
  let mut res : String := "0"
  for i in List.range n do
    res := res ++ " " ++ toString (i + 1)
  return res

/-! ## 10. Imperative Tests -/

example : string_sequence_imp 0 = "0" := by native_decide
example : string_sequence_imp 1 = "0 1" := by native_decide
example : string_sequence_imp 3 = "0 1 2 3" := by native_decide
example : string_sequence_imp 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence_imp 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval string_sequence_imp 0
#eval string_sequence_imp 3
#eval string_sequence_imp 5
#eval string_sequence_imp 10

#eval Plausible.Testable.check (∀ n : Nat, string_sequence_imp n = string_sequence n)
example : (List.range 30).all (fun n => string_sequence_imp n == string_sequence n) = true := by native_decide

/-! ## 11. Functional-Imperative Equivalence Theorem -/

/-- Helper lemma relating `List.foldl` of string concatenation to `String.intercalate.go`. -/
theorem foldl_append_eq_intercalate_go (acc sep : String) (xs : List String) :
    xs.foldl (fun res s => res ++ sep ++ s) acc = String.intercalate.go acc sep xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldl_cons, String.intercalate.go]
    exact ih (acc ++ sep ++ a)

/-- Pointwise equivalence between the imperative and functional implementations. -/
theorem string_sequence_imp_eq (n : Nat) :
    string_sequence_imp n = string_sequence n := by
  unfold string_sequence_imp string_sequence
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp [String.intercalate]
  change (List.range n).foldl (fun res i => res ++ " " ++ (toString ∘ Nat.succ) i) "0" =
    String.intercalate.go (toString 0) " " (List.map (toString ∘ Nat.succ) (List.range n))
  rw [← List.foldl_map (f := toString ∘ Nat.succ) (g := fun res s => res ++ " " ++ s)]
  exact foldl_append_eq_intercalate_go "0" " " (List.map (toString ∘ Nat.succ) (List.range n))

/-- Functional equality between `string_sequence` and `string_sequence_imp`. -/
theorem equivalence_thm : string_sequence = string_sequence_imp := by
  funext n
  exact (string_sequence_imp_eq n).symm

/-- Imperative implementation also satisfies the full post-condition `Post_prop`. -/
theorem string_sequence_imp_correct (n : Nat) (hPre : Pre n) :
    Post_prop n (string_sequence_imp n) := by
  rw [string_sequence_imp_eq]
  exact string_sequence_correct n hPre

end humaneval_15_string_sequence
