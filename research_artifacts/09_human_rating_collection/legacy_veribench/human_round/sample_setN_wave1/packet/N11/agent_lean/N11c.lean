import Mathlib

/-!
# VeriBench - HumanEval/15 `string_sequence`

Python source:

    def string_sequence(n: int) -> str:
        """ Return a string containing space-delimited numbers starting from 0 upto n
        inclusive.
        >>> string_sequence(0)
        '0'
        >>> string_sequence(5)
        '0 1 2 3 4 5'
        """
        return ' '.join([str(x) for x in range(n + 1)])

Modelling notes:

* `' '.join` is modelled by the structural recursion `joinSep`.
* `str(x)` is modelled by `toString` on `Nat`: Lean's decimal rendering of a natural number,
  which coincides with Python's `str` on non-negative integers.
* `range (n + 1)` is modelled by `List.range (n + 1)`.
* Python's declared parameter type is `int`; `range (n + 1)` is empty for `n < 0`, so the
  result is then `""`.  The main development uses the `Nat` domain (the pre-condition `Pre`
  records non-negativity of the argument) and the last section reproduces the full `int`
  behaviour through `string_sequence_int`.
-/

namespace humaneval_15_string_sequence

open List

/-! ## 1. Functional implementation -/

/-- `' '.join`: concatenate a list of strings, separating consecutive entries by a single
space. -/
def joinSep : List String → String
  | []     => ""
  | [s]    => s
  | s :: t => s ++ " " ++ joinSep t

/-- `[str(x) for x in range(n + 1)]`: the decimal tokens of `0, 1, …, n`. -/
def tokens (n : Nat) : List String := (List.range (n + 1)).map (fun x => toString x)

/-- `string_sequence n`: a string containing space-delimited numbers starting from `0`
up to `n` inclusive. -/
def string_sequence (n : Nat) : String := joinSep (tokens n)

/-! ## 2. Unit tests -/

example : string_sequence 0 = "0" := by native_decide
example : string_sequence 3 = "0 1 2 3" := by native_decide
example : string_sequence 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval string_sequence 0
#eval string_sequence 5
#eval string_sequence 10
#eval tokens 4

/-! ## 3. Pre-condition -/

/-- Pre-condition: the argument is a non-negative integer.  Over the `Nat` domain this is
automatic; it records the Python side condition under which `range (n + 1)` enumerates
`0, …, n`. -/
def Pre (n : Nat) : Prop := 0 ≤ n

/-! ## 4. Auxiliary definitions and lemmas -/

/-- `p` is a prefix of `s`. -/
def IsPrefix (p s : String) : Prop := ∃ t : String, s = p ++ t

/-- `q` is a suffix of `s`. -/
def IsSuffix (q s : String) : Prop := ∃ t : String, s = t ++ q

theorem joinSep_nil : joinSep ([] : List String) = "" := rfl

theorem joinSep_singleton (s : String) : joinSep [s] = s := rfl

theorem joinSep_cons_cons (a b : String) (t : List String) :
    joinSep (a :: b :: t) = a ++ " " ++ joinSep (b :: t) := rfl

theorem toString_zero : toString (0 : Nat) = "0" := rfl

theorem space_data : (" ".data : List Char) = [' '] := rfl

theorem zero_data : ("0".data : List Char) = ['0'] := rfl

theorem empty_data : ("".data : List Char) = [] := rfl

theorem str_append_nil (s : String) : s ++ "" = s := by
  rcases s with ⟨l⟩
  show String.mk (l ++ []) = String.mk l
  rw [List.append_nil]

theorem str_nil_append (s : String) : "" ++ s = s := by
  rcases s with ⟨l⟩
  show String.mk ([] ++ l) = String.mk l
  rw [List.nil_append]

theorem joinSep_append_singleton : ∀ (l : List String) (s : String), l ≠ [] →
    joinSep (l ++ [s]) = joinSep l ++ " " ++ s := by
  intro l
  induction l with
  | nil => intro s h; exact absurd rfl h
  | cons a t ih =>
    intro s h
    cases t with
    | nil =>
      have e : joinSep ([a] ++ [s]) = a ++ " " ++ s := by
        show joinSep (a :: [s]) = a ++ " " ++ s
        rw [joinSep_cons_cons, joinSep_singleton]
      rw [e, joinSep_singleton]
    | cons b u =>
      have hne : (b :: u : List String) ≠ [] := by simp
      have e1 : joinSep ((a :: b :: u) ++ [s]) = a ++ " " ++ joinSep ((b :: u) ++ [s]) := by
        show joinSep (a :: b :: (u ++ [s])) = a ++ " " ++ joinSep (b :: (u ++ [s]))
        rfl
      rw [e1, ih s hne, joinSep_cons_cons]
      simp only [String.append_assoc]

theorem tokens_succ (n : Nat) : tokens (n + 1) = tokens n ++ [toString (n + 1)] := by
  simp only [tokens, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem tokens_ne_nil (n : Nat) : tokens n ≠ [] := by
  intro hh
  have hl := congrArg List.length hh
  simp only [tokens, List.length_map, List.length_range, List.length_nil] at hl
  omega

theorem string_sequence_zero : string_sequence 0 = "0" := by
  simp [string_sequence, tokens, joinSep, toString_zero]

theorem string_sequence_succ (n : Nat) :
    string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1) := by
  show joinSep (tokens (n + 1)) = joinSep (tokens n) ++ " " ++ toString (n + 1)
  rw [tokens_succ, joinSep_append_singleton _ _ (tokens_ne_nil n)]

theorem append_space_ne_empty (x y : String) : x ++ " " ++ y ≠ "" := by
  intro h
  have h' := congrArg String.data h
  rw [String.data_append, String.data_append, space_data, empty_data] at h'
  rw [List.append_eq_nil_iff] at h'
  obtain ⟨h1, _⟩ := h'
  rw [List.append_eq_nil_iff] at h1
  obtain ⟨_, h2⟩ := h1
  simp at h2

theorem string_sequence_ne_empty : ∀ n : Nat, string_sequence n ≠ "" := by
  intro n
  induction n with
  | zero =>
    intro h
    have h' := congrArg String.data h
    rw [string_sequence_zero, zero_data, empty_data] at h'
    simp at h'
  | succ k ih =>
    intro h
    rw [string_sequence_succ k] at h
    exact append_space_ne_empty _ _ h

theorem string_sequence_prefix_zero : ∀ n : Nat, IsPrefix "0" (string_sequence n) := by
  intro n
  induction n with
  | zero => exact ⟨"", by rw [string_sequence_zero, str_append_nil]⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    rw [string_sequence_succ k, ht]
    exact ⟨t ++ " " ++ toString (k + 1), by simp only [String.append_assoc]⟩

theorem string_sequence_suffix_n : ∀ n : Nat, IsSuffix (toString n) (string_sequence n) := by
  intro n
  cases n with
  | zero => exact ⟨"", by rw [string_sequence_zero, str_nil_append, toString_zero]⟩
  | succ k => exact ⟨string_sequence k ++ " ", string_sequence_succ k⟩

theorem get?_map_self {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat),
    (l.map f)[i]? = (l[i]?).map f := by
  intro l
  induction l with
  | nil => intro i; cases i <;> rfl
  | cons a l ih =>
    intro i
    cases i with
    | zero => rfl
    | succ j => exact ih j

theorem get?_range : ∀ (n i : Nat), i < n → (List.range n)[i]? = some i := by
  intro n
  induction n with
  | zero => intro i h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro i h
    rw [List.range_succ_eq_map]
    cases i with
    | zero => rfl
    | succ j =>
      have h1 : (0 :: (List.range k).map Nat.succ)[j + 1]? =
          ((List.range k).map Nat.succ)[j]? := rfl
      rw [h1, get?_map_self, ih j (by omega)]
      rfl

theorem tokens_get? (n i : Nat) (h : i < n + 1) : (tokens n)[i]? = some (toString i) := by
  show ((List.range (n + 1)).map (fun x => toString x))[i]? = some (toString i)
  rw [get?_map_self, get?_range _ _ h]
  rfl

/-! ## 5. Properties of the functional implementation -/

/-- Property 1 (docstring example): the sequence for `0` is `"0"`. -/
def base_prop : Prop := string_sequence 0 = "0"

theorem base_thm : base_prop := string_sequence_zero

/-- Property 2 (recursive shape): the sequence for `n + 1` is the sequence for `n` followed
by one space and the decimal representation of `n + 1`. -/
def succ_prop : Prop :=
  ∀ n : Nat, string_sequence (n + 1) = string_sequence n ++ " " ++ toString (n + 1)

theorem succ_thm : succ_prop := fun n => string_sequence_succ n

/-- Property 3 (how many numbers are printed): exactly `n + 1` tokens. -/
def token_count_prop : Prop := ∀ n : Nat, (tokens n).length = n + 1

theorem token_count_thm : token_count_prop := by
  intro n
  simp only [tokens, List.length_map, List.length_range]

/-- Property 4 (which numbers are printed): the `i`-th token is `str i` for every
`0 ≤ i ≤ n`. -/
def token_at_prop : Prop :=
  ∀ n i : Nat, i < n + 1 → (tokens n)[i]? = some (toString i)

theorem token_at_thm : token_at_prop := fun n i h => tokens_get? n i h

/-- Property 5 (the enumeration starts from `0`). -/
def starts_at_zero_prop : Prop := ∀ n : Nat, IsPrefix "0" (string_sequence n)

theorem starts_at_zero_thm : starts_at_zero_prop := string_sequence_prefix_zero

/-- Property 6 (the enumeration stops at `n`, inclusive). -/
def ends_at_n_prop : Prop := ∀ n : Nat, IsSuffix (toString n) (string_sequence n)

theorem ends_at_n_thm : ends_at_n_prop := string_sequence_suffix_n

/-- Property 7 (on the admissible `Nat` domain the result is never empty). -/
def nonempty_prop : Prop := ∀ n : Nat, string_sequence n ≠ ""

theorem nonempty_thm : nonempty_prop := string_sequence_ne_empty

/-- Property 8 (nesting): the output for `n` is a prefix of the output for `n + 1`, i.e. the
enumeration is built by appending. -/
def prefix_step_prop : Prop :=
  ∀ n : Nat, IsPrefix (string_sequence n) (string_sequence (n + 1))

theorem prefix_step_thm : prefix_step_prop := by
  intro n
  exact ⟨" " ++ toString (n + 1), by
    rw [string_sequence_succ n]
    simp only [String.append_assoc]⟩

/-! ## 6. Post-condition -/

/-- Post-condition: `out` is the space-delimited enumeration of `0, …, n`, it exhibits the
two defining equations of the Python program, it starts with `0`, it ends with `str n` and
it is not empty. -/
def Post_prop (n : Nat) (out : String) : Prop :=
  out = string_sequence n ∧
  (n = 0 → out = "0") ∧
  (∀ m : Nat, n = m + 1 → out = string_sequence m ++ " " ++ toString (m + 1)) ∧
  IsPrefix "0" out ∧
  IsSuffix (toString n) out ∧
  out ≠ ""

/-! ## 7. Property-based tests -/

/-- Executable counterpart of `IsPrefix`. -/
def isPrefixBool (p s : String) : Bool := s.data.take p.data.length == p.data

/-- Executable counterpart of `IsSuffix`. -/
def isSuffixBool (q s : String) : Bool :=
  q.data.length ≤ s.data.length && s.data.drop (s.data.length - q.data.length) == q.data

/-- Executable counterpart of `token_at_prop`. -/
def tokenAtBool (n i : Nat) : Bool :=
  match (tokens n)[i]? with
  | some s => s == toString i
  | none   => false

/-- Executable counterpart of `Post_prop`. -/
def Post_bool (n : Nat) (out : String) : Bool :=
  (out == string_sequence n) &&
  (if n == 0 then out == "0" else true) &&
  (if n == 0 then true else out == string_sequence (n - 1) ++ " " ++ toString n) &&
  isPrefixBool "0" out &&
  isSuffixBool (toString n) out &&
  (out == "") == false

-- PBT for `base_prop`
example : (string_sequence 0 == "0") = true := by native_decide

-- PBT for `succ_prop` (bounded)
example : (List.range 30).all (fun n =>
    string_sequence (n + 1) == string_sequence n ++ " " ++ toString (n + 1)) = true := by
  native_decide

-- PBT for `succ_prop` (randomised; the argument is kept in a cheap range with `% 25`)
#eval Plausible.Testable.check
  (∀ n : Nat,
    string_sequence (n % 25 + 1) = string_sequence (n % 25) ++ " " ++ toString (n % 25 + 1))

-- PBT for `token_count_prop` (bounded)
example : (List.range 30).all (fun n => (tokens n).length == n + 1) = true := by native_decide

-- PBT for `token_count_prop` (randomised)
#eval Plausible.Testable.check (∀ n : Nat, (tokens (n % 40)).length = n % 40 + 1)

-- PBT for `token_at_prop` (bounded)
example : (List.range 25).all (fun n =>
    (List.range (n + 1)).all (fun i => tokenAtBool n i)) = true := by native_decide

-- PBT for `starts_at_zero_prop` (bounded)
example : (List.range 30).all (fun n => isPrefixBool "0" (string_sequence n)) = true := by
  native_decide

-- PBT for `ends_at_n_prop` (bounded)
example : (List.range 30).all (fun n =>
    isSuffixBool (toString n) (string_sequence n)) = true := by native_decide

-- PBT for `nonempty_prop` (bounded)
example : (List.range 30).all (fun n => (string_sequence n == "") == false) = true := by
  native_decide

-- PBT for `nonempty_prop` (randomised)
#eval Plausible.Testable.check (∀ n : Nat, string_sequence (n % 40) ≠ "")

-- PBT for `prefix_step_prop` (bounded)
example : (List.range 30).all (fun n =>
    isPrefixBool (string_sequence n) (string_sequence (n + 1))) = true := by native_decide

-- PBT for `prefix_step_prop` (randomised)
#eval Plausible.Testable.check
  (∀ n : Nat,
    isPrefixBool (string_sequence (n % 25)) (string_sequence (n % 25 + 1)) = true)

-- PBT for `Post_prop` (bounded)
example : (List.range 30).all (fun n => Post_bool n (string_sequence n)) = true := by
  native_decide

/-! ## 8. Correctness: `Pre -> Post` -/

theorem correctness_thm (n : Nat) (_h : Pre n) : Post_prop n (string_sequence n) := by
  refine ⟨rfl, ?_, ?_, string_sequence_prefix_zero n, string_sequence_suffix_n n,
    string_sequence_ne_empty n⟩
  · intro hn
    rw [hn]
    exact string_sequence_zero
  · intro m hm
    rw [hm]
    exact string_sequence_succ m

/-! ## 9. Imperative implementation (mutable state in the `Id` monad) -/

/-- One iteration of the imperative loop: append a space and the next number. -/
def appendToken (acc : String) (i : Nat) : String := acc ++ " " ++ toString (i + 1)

/-- Imperative implementation of `string_sequence`: a mutable accumulator initialised with
`"0"` and a bounded `for` loop over `0, …, n - 1` appending `str (i + 1)`. -/
def string_sequence_imp (n : Nat) : String :=
  Id.run do
    let mut result : String := "0"
    for i in List.range n do
      result := appendToken result i
    return result

/-! ## 10. Imperative tests -/

example : string_sequence_imp 0 = "0" := by native_decide
example : string_sequence_imp 3 = "0 1 2 3" := by native_decide
example : string_sequence_imp 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence_imp 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval string_sequence_imp 0
#eval string_sequence_imp 5
#eval string_sequence_imp 10

-- PBT: the imperative loop satisfies the recursive shape
example : (List.range 30).all (fun n =>
    string_sequence_imp (n + 1) == string_sequence_imp n ++ " " ++ toString (n + 1)) = true := by
  native_decide

-- PBT: the imperative loop satisfies the post-condition
example : (List.range 30).all (fun n => Post_bool n (string_sequence_imp n)) = true := by
  native_decide

/-! ## 11. Equivalence of the functional and the imperative implementation -/

/-- A `for`-loop in `Id` that always `yield`s is a left fold. -/
theorem forIn_yield_eq_foldl {α β : Type} (l : List α) (b : β) (f : α → β → β) :
    (forIn l b (fun a b => pure (ForInStep.yield (f a b))) : Id β) =
      l.foldl (fun b a => f a b) b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    have key : (forIn (a :: l) b (fun a b => pure (ForInStep.yield (f a b))) : Id β)
        = (forIn l (f a b) (fun a b => pure (ForInStep.yield (f a b))) : Id β) := by
      rw [List.forIn_cons]
      rfl
    rw [key, ih, List.foldl_cons]

theorem imp_foldl (n : Nat) :
    string_sequence_imp n = List.foldl appendToken "0" (List.range n) := by
  have h1 : string_sequence_imp n =
      (forIn (List.range n) "0"
        (fun i r => pure (ForInStep.yield (appendToken r i))) : Id String) := rfl
  rw [h1, forIn_yield_eq_foldl]

theorem foldl_append_self {α β : Type} (f : β → α → β) :
    ∀ (l₁ l₂ : List α) (a : β), (l₁ ++ l₂).foldl f a = l₂.foldl f (l₁.foldl f a) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ a; rfl
  | cons x l₁ ih =>
    intro l₂ a
    show (x :: (l₁ ++ l₂)).foldl f a = l₂.foldl f ((x :: l₁).foldl f a)
    rw [List.foldl_cons, List.foldl_cons, ih]

/-- The imperative accumulator, expressed as a join of the remaining tokens. -/
theorem foldl_appendToken : ∀ (l : List Nat) (acc : String),
    l.foldl appendToken acc =
      if l = [] then acc else acc ++ " " ++ joinSep (l.map (fun i => toString (i + 1))) := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons a t ih =>
    intro acc
    cases t with
    | nil =>
      have hne : ¬(([a] : List Nat) = []) := by simp
      have e : ([a] : List Nat).foldl appendToken acc = appendToken acc a := by
        rw [List.foldl_cons]
        rfl
      rw [e, if_neg hne, appendToken]
      simp only [List.map_cons, List.map_nil, joinSep_singleton]
    | cons b u =>
      have hne : ¬((a :: b :: u : List Nat) = []) := by simp
      have hne2 : ¬((b :: u : List Nat) = []) := by simp
      rw [List.foldl_cons, ih (appendToken acc a), if_neg hne2, if_neg hne]
      simp only [List.map_cons, appendToken]
      rw [joinSep_cons_cons]
      simp only [String.append_assoc]

theorem imp_succ (k : Nat) :
    string_sequence_imp (k + 1) = string_sequence_imp k ++ " " ++ toString (k + 1) := by
  rw [imp_foldl, imp_foldl, List.range_succ, foldl_append_self, List.foldl_cons, appendToken]
  rfl

/-- The imperative implementation computes the same string as the functional one. -/
theorem equivalence_thm : ∀ n : Nat, string_sequence_imp n = string_sequence n := by
  intro n
  induction n with
  | zero =>
    rw [string_sequence_zero, imp_foldl]
    rfl
  | succ k ih =>
    rw [string_sequence_succ k, imp_succ k, ih]

/-! ## 12. The full Python `int` domain -/

/-- Python declares `n : int`.  For `n < 0` the list `range (n + 1)` is empty, hence
`' '.join([])` is the empty string; for `n ≥ 0` the result is the `Nat` version above. -/
def string_sequence_int (n : Int) : String :=
  if 0 ≤ n then string_sequence (Int.toNat n) else ""

theorem string_sequence_int_neg (n : Int) (h : n < 0) : string_sequence_int n = "" := by
  rw [string_sequence_int, if_neg (by omega)]

theorem string_sequence_int_nonneg (n : Int) (h : 0 ≤ n) :
    string_sequence_int n = string_sequence (Int.toNat n) := by
  rw [string_sequence_int, if_pos h]

example : string_sequence_int (-3) = "" := by native_decide
example : string_sequence_int 0 = "0" := by native_decide
example : string_sequence_int 5 = "0 1 2 3 4 5" := by native_decide

#eval string_sequence_int (-1)
#eval string_sequence_int 4

-- PBT for the `int` layer: negative arguments give `""`, non-negative ones agree with `Nat`
example : (List.range 21).all (fun k =>
    string_sequence_int ((k : Int) - 10) ==
      (if k < 10 then "" else string_sequence (k - 10))) = true := by native_decide

end humaneval_15_string_sequence
