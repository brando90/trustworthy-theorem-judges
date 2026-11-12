import Mathlib
import Plausible

/-!
# HumanEval/15: `string_sequence`

This module formalizes the Python function `string_sequence(n: int) -> str` from HumanEval/15,
which returns a string containing space-delimited numbers starting from `0` up to `n` inclusive.

It includes:
1. Functional implementation (`string_sequence`).
2. Unit tests (`example` with `native_decide` and `#eval`).
3. Pre-condition (`Pre`).
4. Semantic properties (`*_prop`) and full kernel-checked proofs (`*_thm`).
5. Post-condition (`Post_prop`) as the conjunction of all properties.
6. Randomized (`Plausible.Testable.check`) and bounded property-based tests for every property and post-condition.
7. Correctness theorem (`Pre n → Post_prop n`).
8. Imperative implementation (`string_sequence_imp`) using `Id.run do` with mutable state.
9. Imperative tests and functional-imperative equivalence theorem (`string_sequence_equiv`).
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

/-- Pre-condition for `string_sequence`: any natural number `n` is a valid non-negative bound. -/
def Pre (_n : Nat) : Prop := True

/-! ## 4. Helper Lemmas -/

theorem intercalate_go_append (acc s b : String) (xs : List String) :
    String.intercalate.go acc s (xs ++ [b]) = String.intercalate.go acc s xs ++ s ++ b := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a as ih => exact ih (acc ++ s ++ a)

theorem intercalate_append_nonempty (s b : String) (xs : List String) (h : xs ≠ []) :
    String.intercalate s (xs ++ [b]) = String.intercalate s xs ++ s ++ b := by
  cases xs with
  | nil => contradiction
  | cons a as => exact intercalate_go_append a s b as

theorem string_sequence_zero : string_sequence 0 = "0" := rfl

theorem string_sequence_succ (n : Nat) :
    string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1) := by
  unfold string_sequence
  rw [List.range_succ (n := n + 1), List.map_append, List.map_singleton]
  apply intercalate_append_nonempty
  simp

theorem digitChar_lt_10_isDigit (d : Nat) (h : d < 10) : (Nat.digitChar d).isDigit = true := by
  interval_cases d <;> rfl

theorem toDigitsCore_nonempty (fuel n : Nat) (ds : List Char) (h : 0 < fuel) :
    Nat.toDigitsCore 10 fuel n ds ≠ [] := by
  induction fuel generalizing n ds with
  | zero => omega
  | succ f ih =>
    simp only [Nat.toDigitsCore]
    split
    · simp
    · cases f with
      | zero =>
        simp only [Nat.toDigitsCore]
        exact List.cons_ne_nil _ _
      | succ f' =>
        exact ih (n / 10) ((n % 10).digitChar :: ds) (Nat.succ_pos _)

theorem toDigitsCore_mem_isDigit (fuel n : Nat) (ds : List Char)
    (hds : ∀ c ∈ ds, c.isDigit = true) :
    ∀ c ∈ Nat.toDigitsCore 10 fuel n ds, c.isDigit = true := by
  induction fuel generalizing n ds with
  | zero =>
    simp only [Nat.toDigitsCore]
    exact hds
  | succ f ih =>
    have hd : ((n % 10).digitChar).isDigit = true := digitChar_lt_10_isDigit (n % 10) (by omega)
    have hds' : ∀ c ∈ (n % 10).digitChar :: ds, c.isDigit = true := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hd
      · exact hds c hc
    simp only [Nat.toDigitsCore]
    split
    · exact hds'
    · exact ih (n / 10) ((n % 10).digitChar :: ds) hds'

theorem toString_length_pos (n : Nat) : 0 < (toString n).length := by
  change 0 < (Nat.toDigits 10 n).length
  exact List.length_pos_of_ne_nil (toDigitsCore_nonempty (n + 1) n [] (Nat.succ_pos n))

theorem toString_mem_isDigit (n : Nat) : ∀ c ∈ (toString n).toList, c.isDigit = true := by
  intro c hc
  exact toDigitsCore_mem_isDigit (n + 1) n [] (by simp) c hc

theorem space_not_mem_toString (n : Nat) : ' ' ∉ (toString n).toList := by
  intro h
  have hd := toString_mem_isDigit n ' ' h
  revert hd; decide

theorem toString_count_space (n : Nat) : (toString n).toList.count ' ' = 0 := by
  rw [List.count_eq_zero]
  exact space_not_mem_toString n

theorem splitOnP_go_append_sep {α : Type*} (P : α → Bool) (l₁ l₂ : List α) (a : α) (acc : List α)
    (ha : P a = true) :
    List.splitOnP.go P (l₁ ++ a :: l₂) acc =
      List.splitOnP.go P l₁ acc ++ List.splitOnP.go P l₂ [] := by
  induction l₁ generalizing acc with
  | nil =>
    simp [List.splitOnP.go, ha]
  | cons x xs ih =>
    simp only [List.cons_append, List.splitOnP.go]
    split
    · rw [ih []]
      rfl
    · exact ih (x :: acc)

theorem splitOnP_go_no_sep {α : Type*} (P : α → Bool) (l : List α) (acc : List α)
    (hl : ∀ x ∈ l, P x = false) :
    List.splitOnP.go P l acc = [acc.reverse ++ l] := by
  induction l generalizing acc with
  | nil =>
    simp [List.splitOnP.go]
  | cons x xs ih =>
    have hx : P x = false := hl x (by simp)
    have hxs : ∀ y ∈ xs, P y = false := fun y hy => hl y (by simp [hy])
    simp only [List.splitOnP.go, hx, Bool.false_eq_true, ↓reduceIte]
    rw [ih (x :: acc) hxs]
    simp [List.reverse_cons, List.append_assoc]

theorem splitOn_append_sep {α : Type*} [BEq α] [LawfulBEq α] (a : α) (l₁ l₂ : List α) :
    List.splitOn a (l₁ ++ a :: l₂) = List.splitOn a l₁ ++ List.splitOn a l₂ := by
  unfold List.splitOn List.splitOnP
  exact splitOnP_go_append_sep (fun x => x == a) l₁ l₂ a [] (by simp)

theorem splitOn_no_sep {α : Type*} [BEq α] [LawfulBEq α] (a : α) (l : List α) (hl : a ∉ l) :
    List.splitOn a l = [l] := by
  unfold List.splitOn List.splitOnP
  have h : ∀ x ∈ l, (x == a) = false := by
    intro x hx
    rw [beq_eq_false_iff_ne]
    intro hxa
    subst hxa
    exact hl hx
  rw [splitOnP_go_no_sep (fun x => x == a) l [] h]
  simp

/-! ## 5. Properties and Theorems -/

/-- Property 1: Base case (`n = 0` yields `"0"`). -/
def zero_prop (n : Nat) : Prop :=
  n = 0 → string_sequence n = "0"

theorem zero_thm (n : Nat) (_h : Pre n) : zero_prop n := by
  intro hn
  subst hn
  rfl

/-- Property 2: Step recurrence (`string_sequence (n + 1)` appends `" " ++ toString (n + 1)`). -/
def succ_prop (n : Nat) : Prop :=
  string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1)

theorem succ_thm (n : Nat) (_h : Pre n) : succ_prop n :=
  string_sequence_succ n

/-- Property 3: The returned string is always non-empty and has positive length. -/
def nonempty_prop (n : Nat) : Prop :=
  0 < (string_sequence n).length ∧ string_sequence n ≠ ""

theorem nonempty_thm (n : Nat) (_h : Pre n) : nonempty_prop n := by
  clear _h
  have hlen : 0 < (string_sequence n).length := by
    induction n with
    | zero => decide
    | succ k ih =>
      rw [string_sequence_succ, String.length_append, String.length_append]
      omega
  refine ⟨hlen, ?_⟩
  intro hempty
  rw [hempty] at hlen
  contradiction

/-- Property 4: The returned string always starts with `'0'`. -/
def starts_with_zero_prop (n : Nat) : Prop :=
  "0".toList <+: (string_sequence n).toList ∧ (string_sequence n).toList.head? = some '0'

theorem starts_with_zero_thm (n : Nat) (_h : Pre n) : starts_with_zero_prop n := by
  clear _h
  have hpref : "0".toList <+: (string_sequence n).toList := by
    induction n with
    | zero => exact List.prefix_refl _
    | succ k ih =>
      rw [string_sequence_succ]
      simp only [String.toList, String.data_append, List.append_assoc]
      exact ih.trans (List.prefix_append _ _)
  refine ⟨hpref, ?_⟩
  rcases hpref with ⟨t, ht⟩
  have h0 : "0".toList = ['0'] := rfl
  rw [h0, List.singleton_append] at ht
  rw [← ht]
  rfl

/-- Property 5: The returned string always ends with `toString n` (and `" " ++ toString n` for `n > 0`). -/
def ends_with_n_prop (n : Nat) : Prop :=
  (toString n).toList <:+ (string_sequence n).toList ∧
    (0 < n → (" " ++ toString n).toList <:+ (string_sequence n).toList)

theorem ends_with_n_thm (n : Nat) (_h : Pre n) : ends_with_n_prop n := by
  clear _h
  unfold ends_with_n_prop
  cases n with
  | zero =>
    refine ⟨List.suffix_refl _, ?_⟩
    intro h
    omega
  | succ k =>
    rw [string_sequence_succ]
    refine ⟨?_, ?_⟩
    · simp only [String.toList, String.data_append]
      exact List.suffix_append _ _
    · intro _
      simp only [String.toList, String.data_append, List.append_assoc]
      exact List.suffix_append _ _

/-- Property 6: Prefix monotonicity (`m ≤ n` implies `string_sequence m` is a prefix of `string_sequence n`). -/
def prefix_mono_prop (n : Nat) : Prop :=
  ∀ m : Nat, m ≤ n → (string_sequence m).toList <+: (string_sequence n).toList

theorem prefix_mono_thm (n : Nat) (_h : Pre n) : prefix_mono_prop n := by
  clear _h
  unfold prefix_mono_prop
  induction n with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    exact List.prefix_refl _
  | succ k ih =>
    intro m hm
    rcases Nat.of_le_succ hm with hle | rfl
    · rw [string_sequence_succ]
      simp only [String.toList, String.data_append, List.append_assoc]
      exact (ih m hle).trans (List.prefix_append _ _)
    · exact List.prefix_refl _

/-- Property 7: The number of space characters `' '` in `string_sequence n` is exactly `n`. -/
def space_count_prop (n : Nat) : Prop :=
  (string_sequence n).toList.count ' ' = n

theorem space_count_thm (n : Nat) (_h : Pre n) : space_count_prop n := by
  clear _h
  unfold space_count_prop
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [string_sequence_succ]
    simp only [String.toList, String.data_append, List.count_append]
    have hspace : (" ").data.count ' ' = 1 := rfl
    have hnum : (toString (k + 1)).data.count ' ' = 0 := toString_count_space (k + 1)
    change (string_sequence k).toList.count ' ' + (" ").data.count ' ' + (toString (k + 1)).data.count ' ' = k + 1
    rw [ih, hspace, hnum]

/-- Property 8: Every character in `string_sequence n` is either `' '` or a decimal digit. -/
def valid_chars_prop (n : Nat) : Prop :=
  ∀ c ∈ (string_sequence n).toList, c = ' ' ∨ c.isDigit = true

theorem valid_chars_thm (n : Nat) (_h : Pre n) : valid_chars_prop n := by
  clear _h
  unfold valid_chars_prop
  induction n with
  | zero =>
    intro c hc
    right
    exact toString_mem_isDigit 0 c hc
  | succ k ih =>
    intro c hc
    rw [string_sequence_succ] at hc
    simp only [String.toList, String.data_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact ih c hc
    · left
      exact List.mem_singleton.mp hc
    · right
      exact toString_mem_isDigit (k + 1) c hc

/-- Property 9: Length lower bound (`2 * n + 1 ≤ length`) and strict length growth. -/
def length_bound_prop (n : Nat) : Prop :=
  2 * n + 1 ≤ (string_sequence n).length ∧
    (string_sequence n).length < (string_sequence (n + 1)).length

theorem length_bound_thm (n : Nat) (_h : Pre n) : length_bound_prop n := by
  clear _h
  have hlow : 2 * n + 1 ≤ (string_sequence n).length := by
    induction n with
    | zero => decide
    | succ k ih =>
      have hpos := toString_length_pos (k + 1)
      have hsp : (" ").length = 1 := rfl
      rw [string_sequence_succ, String.length_append, String.length_append, hsp]
      omega
  refine ⟨hlow, ?_⟩
  have hpos := toString_length_pos (n + 1)
  have hsp : (" ").length = 1 := rfl
  rw [string_sequence_succ, String.length_append, String.length_append, hsp]
  omega

/-- Property 10: Splitting `string_sequence n` on `' '` recovers the exact list of number strings `0..n` of length `n + 1`. -/
def tokens_prop (n : Nat) : Prop :=
  ((string_sequence n).toList.splitOn ' ').map List.asString = (List.range (n + 1)).map toString ∧
    ((string_sequence n).toList.splitOn ' ').length = n + 1

theorem tokens_thm (n : Nat) (_h : Pre n) : tokens_prop n := by
  clear _h
  have htok : ((string_sequence n).toList.splitOn ' ').map List.asString = (List.range (n + 1)).map toString := by
    induction n with
    | zero => rfl
    | succ k ih =>
      have hstep : (string_sequence (k + 1)).toList = (string_sequence k).toList ++ ' ' :: (toString (k + 1)).toList := by
        rw [string_sequence_succ]
        simp [String.toList, String.data_append]
      rw [hstep, splitOn_append_sep, splitOn_no_sep ' ' _ (space_not_mem_toString (k + 1))]
      rw [List.map_append, ih, List.range_succ (n := k + 1), List.map_append]
      rfl
  refine ⟨htok, ?_⟩
  have hlen := congrArg List.length htok
  simp only [List.length_map, List.length_range] at hlen
  exact hlen

/-- Property 11: Indexing the space-delimited tokens at any `i ≤ n` returns `some (toString i)`. -/
def token_getElem_prop (n : Nat) : Prop :=
  ∀ i : Nat, i ≤ n → (((string_sequence n).toList.splitOn ' ').map List.asString)[i]? = some (toString i)

theorem token_getElem_thm (n : Nat) (h : Pre n) : token_getElem_prop n := by
  intro i hi
  rw [(tokens_thm n h).1]
  have hilt : i < n + 1 := by omega
  simp [hilt]

/-! ## 6. Post-condition -/

/-- Full post-condition combining all semantic properties of `string_sequence`. -/
def Post_prop (n : Nat) : Prop :=
  zero_prop n ∧
  succ_prop n ∧
  nonempty_prop n ∧
  starts_with_zero_prop n ∧
  ends_with_n_prop n ∧
  prefix_mono_prop n ∧
  space_count_prop n ∧
  valid_chars_prop n ∧
  length_bound_prop n ∧
  tokens_prop n ∧
  token_getElem_prop n

/-! ## 7. Property-Based Tests -/

-- PBT for `zero_prop`
#eval Plausible.Testable.check (∀ n : Nat, (!(n == 0) || string_sequence n == "0") = true)
example : (List.range 30).all (fun n => !(n == 0) || string_sequence n == "0") = true := by native_decide

-- PBT for `succ_prop`
#eval Plausible.Testable.check (∀ n : Nat, string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1))
example : (List.range 30).all (fun n => string_sequence (n + 1) == string_sequence n ++ " " ++ toString (n + 1)) = true := by native_decide

-- PBT for `nonempty_prop`
#eval Plausible.Testable.check (∀ n : Nat, 0 < (string_sequence n).length ∧ string_sequence n ≠ "")
example : (List.range 30).all (fun n => decide (0 < (string_sequence n).length) && string_sequence n != "") = true := by native_decide

-- PBT for `starts_with_zero_prop`
#eval Plausible.Testable.check (∀ n : Nat, "0".toList <+: (string_sequence n).toList ∧ (string_sequence n).toList.head? = some '0')
example : (List.range 30).all (fun n => decide ("0".toList <+: (string_sequence n).toList) && ((string_sequence n).toList.head? == some '0')) = true := by native_decide

-- PBT for `ends_with_n_prop`
#eval Plausible.Testable.check (∀ n : Nat, (toString n).toList <:+ (string_sequence n).toList ∧ (0 < n → (" " ++ toString n).toList <:+ (string_sequence n).toList))
example : (List.range 30).all (fun n => decide ((toString n).toList <:+ (string_sequence n).toList) && (!(0 < n) || decide ((" " ++ toString n).toList <:+ (string_sequence n).toList))) = true := by native_decide

-- PBT for `prefix_mono_prop`
#eval Plausible.Testable.check (∀ n m : Nat, m ≤ n → (string_sequence m).toList <+: (string_sequence n).toList)
example : (List.range 20).all (fun n => (List.range (n + 1)).all (fun m => decide ((string_sequence m).toList <+: (string_sequence n).toList))) = true := by native_decide

-- PBT for `space_count_prop`
#eval Plausible.Testable.check (∀ n : Nat, (string_sequence n).toList.count ' ' = n)
example : (List.range 30).all (fun n => (string_sequence n).toList.count ' ' == n) = true := by native_decide

-- PBT for `valid_chars_prop`
#eval Plausible.Testable.check (∀ n : Nat, (string_sequence n).toList.all (fun c => c == ' ' || c.isDigit) = true)
example : (List.range 30).all (fun n => (string_sequence n).toList.all (fun c => c == ' ' || c.isDigit)) = true := by native_decide

-- PBT for `length_bound_prop`
#eval Plausible.Testable.check (∀ n : Nat, 2 * n + 1 ≤ (string_sequence n).length ∧ (string_sequence n).length < (string_sequence (n + 1)).length)
example : (List.range 30).all (fun n => decide (2 * n + 1 ≤ (string_sequence n).length) && decide ((string_sequence n).length < (string_sequence (n + 1)).length)) = true := by native_decide

-- PBT for `tokens_prop`
#eval Plausible.Testable.check (∀ n : Nat, ((string_sequence n).toList.splitOn ' ').map List.asString = (List.range (n + 1)).map toString ∧ ((string_sequence n).toList.splitOn ' ').length = n + 1)
example : (List.range 30).all (fun n => (((string_sequence n).toList.splitOn ' ').map List.asString == (List.range (n + 1)).map toString) && (((string_sequence n).toList.splitOn ' ').length == n + 1)) = true := by native_decide

-- PBT for `token_getElem_prop`
#eval Plausible.Testable.check (∀ n i : Nat, i ≤ n → (((string_sequence n).toList.splitOn ' ').map List.asString)[i]? = some (toString i))
example : (List.range 20).all (fun n => (List.range (n + 1)).all (fun i => (((string_sequence n).toList.splitOn ' ').map List.asString)[i]? == some (toString i))) = true := by native_decide

-- PBT for `Post_prop`
#eval Plausible.Testable.check (∀ n : Nat,
  ((!(n == 0) || string_sequence n == "0") = true) ∧
  (string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1)) ∧
  (0 < (string_sequence n).length ∧ string_sequence n ≠ "") ∧
  ("0".toList <+: (string_sequence n).toList ∧ (string_sequence n).toList.head? = some '0') ∧
  ((toString n).toList <:+ (string_sequence n).toList ∧ (0 < n → (" " ++ toString n).toList <:+ (string_sequence n).toList)) ∧
  ((string_sequence n).toList.count ' ' = n) ∧
  ((string_sequence n).toList.all (fun c => c == ' ' || c.isDigit) = true) ∧
  (2 * n + 1 ≤ (string_sequence n).length ∧ (string_sequence n).length < (string_sequence (n + 1)).length) ∧
  (((string_sequence n).toList.splitOn ' ').map List.asString = (List.range (n + 1)).map toString ∧ ((string_sequence n).toList.splitOn ' ').length = n + 1))

example : (List.range 20).all (fun n =>
  (!(n == 0) || string_sequence n == "0") &&
  (string_sequence (n + 1) == string_sequence n ++ " " ++ toString (n + 1)) &&
  (decide (0 < (string_sequence n).length) && string_sequence n != "") &&
  (decide ("0".toList <+: (string_sequence n).toList) && ((string_sequence n).toList.head? == some '0')) &&
  (decide ((toString n).toList <:+ (string_sequence n).toList) && (!(0 < n) || decide ((" " ++ toString n).toList <:+ (string_sequence n).toList))) &&
  (List.range (n + 1)).all (fun m => decide ((string_sequence m).toList <+: (string_sequence n).toList)) &&
  ((string_sequence n).toList.count ' ' == n) &&
  ((string_sequence n).toList.all (fun c => c == ' ' || c.isDigit)) &&
  (decide (2 * n + 1 ≤ (string_sequence n).length) && decide ((string_sequence n).length < (string_sequence (n + 1)).length)) &&
  ((((string_sequence n).toList.splitOn ' ').map List.asString == (List.range (n + 1)).map toString) && (((string_sequence n).toList.splitOn ' ').length == n + 1)) &&
  (List.range (n + 1)).all (fun i => (((string_sequence n).toList.splitOn ' ').map List.asString)[i]? == some (toString i))
) = true := by native_decide

/-! ## 8. Correctness Theorem (`Pre → Post`) -/

theorem string_sequence_correct (n : Nat) (h : Pre n) : Post_prop n :=
  ⟨zero_thm n h,
   succ_thm n h,
   nonempty_thm n h,
   starts_with_zero_thm n h,
   ends_with_n_thm n h,
   prefix_mono_thm n h,
   space_count_thm n h,
   valid_chars_thm n h,
   length_bound_thm n h,
   tokens_thm n h,
   token_getElem_thm n h⟩

/-! ## 9. Imperative Implementation -/

/-- Imperative implementation of `string_sequence` using `Id.run do` and mutable state. -/
def string_sequence_imp (n : Nat) : String := Id.run do
  let mut result : String := "0"
  for i in List.range n do
    result := result ++ " " ++ toString (i + 1)
  return result

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

#eval Plausible.Testable.check (∀ n : Nat, string_sequence n = string_sequence_imp n)
example : (List.range 30).all (fun n => string_sequence n == string_sequence_imp n) = true := by native_decide

/-! ## 11. Functional-Imperative Equivalence Theorem -/

theorem string_sequence_equiv (n : Nat) : string_sequence n = string_sequence_imp n := by
  unfold string_sequence_imp
  have h :
      List.foldl (fun (result : String) (i : Nat) => result ++ " " ++ toString (i + 1)) "0" (List.range n) =
        string_sequence n := by
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, string_sequence_succ]
  simpa [Id.run] using h.symm

end humaneval_15_string_sequence
