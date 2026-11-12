import Mathlib

/-!
# HumanEval 15: string sequence

This file translates Python's `' '.join(str(x) for x in range(n + 1))`.
Inputs are arbitrary integers: negative inputs produce the empty string.  The
specification describes the exact decimal tokens, their count and positions,
and the behavior when the upper bound is increased.  All properties are proved
and checked on bounded families of inputs.  A mutable loop is proved equivalent
to the functional implementation.
-/

namespace humaneval_15_string_sequence

/-- `Int.toNat` truncates a nonpositive range endpoint to zero, just as Python's
one-argument `range` does. -/
def string_sequence (n : Int) : String :=
  String.intercalate " " ((List.range (n + 1).toNat).map fun i => toString i)

/-- Split the result at spaces, with no tokens for the empty string. -/
def tokens (s : String) : List String :=
  if s = "" then [] else s.split (· == ' ')

example : string_sequence 0 = "0" := by native_decide
example : string_sequence 3 = "0 1 2 3" := by native_decide
example : string_sequence 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide
example : string_sequence (-1) = "" := by native_decide
example : string_sequence (-20) = "" := by native_decide

#eval string_sequence 0
#eval string_sequence 5
#eval string_sequence 10
#eval string_sequence (-3)

/-- Python accepts every integer, including negative integers. -/
def Pre (_n : Int) : Prop := True

private theorem go_append_left (a b sep : String) (xs : List String) :
    String.intercalate.go (a ++ b) sep xs =
      a ++ String.intercalate.go b sep xs := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    simpa only [String.intercalate.go, String.append_assoc] using
      ih (b ++ sep ++ x)

private theorem intercalate_cons_cons (sep a b : String) (xs : List String) :
    String.intercalate sep (a :: b :: xs) =
      a ++ sep ++ String.intercalate sep (b :: xs) := by
  exact go_append_left (a ++ sep) b sep xs

private theorem intercalate_data (sep : String) (xs : List String) :
    (String.intercalate sep xs).data =
      List.intercalate sep.data (xs.map String.data) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => simp [String.intercalate, String.intercalate.go, List.intercalate]
    | cons b xs =>
      rw [intercalate_cons_cons]
      simpa [List.intercalate, List.intersperse, String.data_append, List.append_assoc]
        using congrArg (fun ys => a.data ++ sep.data ++ ys) ih

private theorem decimal_no_space (n : Nat) : ' ' ∉ (toString n).data := by
  have digit_ok : ∀ i : Fin 10, Nat.digitChar i.val ≠ ' ' := by native_decide
  have core : ∀ fuel n ds, ' ' ∉ ds → ' ' ∉ Nat.toDigitsCore 10 fuel n ds := by
    intro fuel
    induction fuel with
    | zero => intro n ds h; exact h
    | succ fuel ih =>
      intro n ds h
      have hd : ' ' ∉ Nat.digitChar (n % 10) :: ds := by
        simp only [List.mem_cons, not_or]
        exact ⟨(digit_ok ⟨n % 10, Nat.mod_lt n (by decide)⟩).symm, h⟩
      simp only [Nat.toDigitsCore]
      split
      · exact hd
      · exact ih _ _ hd
  exact core (n + 1) n [] (by simp)

private theorem split_intercalate_decimal (xs : List Nat) (h : xs ≠ []) :
    (String.intercalate " " (xs.map toString)).split (· == ' ') =
      xs.map toString := by
  rw [String.split_of_valid, intercalate_data]
  change (List.splitOn ' ' (List.intercalate [' ']
    ((xs.map toString).map String.data))).map String.mk = xs.map toString
  rw [List.splitOn_intercalate]
  · simp
  · intro ds hds
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hds
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
    exact decimal_no_space i
  · simpa using h

private theorem range_render_nonempty (k : Nat) :
    String.intercalate " " ((List.range (k + 1)).map toString) ≠ "" := by
  rw [List.range_succ_eq_map, List.map_cons]
  change String.intercalate.go "0" " " _ ≠ ""
  have hg := go_append_left "0" "" " "
    ((List.map Nat.succ (List.range k)).map toString)
  rw [String.append_empty] at hg
  rw [hg]
  intro he
  have hc := congrArg String.data he
  simp only [String.data_append] at hc
  cases hc

/-- The complete rendering specification: decimal numerals separated by one space. -/
def sequence_prop (n : Int) (s : String) : Prop :=
  s = String.intercalate " " ((List.range (n + 1).toNat).map toString)

theorem sequence_thm (n : Int) : sequence_prop n (string_sequence n) := by
  rfl

/-- The result is empty exactly for negative inputs. -/
def empty_prop (n : Int) (s : String) : Prop := s = "" ↔ n < 0

theorem empty_thm (n : Int) : empty_prop n (string_sequence n) := by
  unfold empty_prop
  by_cases hn : n < 0
  · have hz : (n + 1).toNat = 0 := by omega
    simp [string_sequence, hz, hn, String.intercalate]
  · have hk : (n + 1).toNat = n.toNat + 1 := by omega
    have hs : string_sequence n ≠ "" := by
      simpa only [string_sequence, hk] using range_render_nonempty n.toNat
    simp [hs, hn]

/-- Splitting recovers exactly the ordered decimal tokens from zero through `n`. -/
def tokens_prop (n : Int) (s : String) : Prop :=
  tokens s = (List.range (n + 1).toNat).map toString

theorem tokens_thm (n : Int) : tokens_prop n (string_sequence n) := by
  unfold tokens_prop tokens
  by_cases hn : n < 0
  · have hz : (n + 1).toNat = 0 := by omega
    simp [(empty_thm n).mpr hn, hz]
  · rw [if_neg (fun he => hn ((empty_thm n).mp he))]
    apply split_intercalate_decimal
    have hp : 0 < (n + 1).toNat := by omega
    simpa using (Nat.ne_of_gt hp)

/-- There are exactly `max (n + 1) 0` tokens. -/
def count_prop (n : Int) (s : String) : Prop :=
  (tokens s).length = (n + 1).toNat

theorem count_thm (n : Int) : count_prop n (string_sequence n) := by
  unfold count_prop
  rw [tokens_thm n]
  simp

/-- Position `i` holds numeral `i` precisely when `0 ≤ i ≤ n`.
This also rules out omissions, reordering, and extra tokens. -/
def position_prop (n : Int) (s : String) : Prop :=
  ∀ i : Nat, (tokens s)[i]? = if (i : Int) ≤ n then some (toString i) else none

theorem position_thm (n : Int) : position_prop n (string_sequence n) := by
  intro i
  rw [tokens_thm n, List.getElem?_map]
  by_cases hi : (i : Int) ≤ n
  · have hb : i < (n + 1).toNat := by omega
    simp [hi, List.getElem?_range hb]
  · have hb : (List.range (n + 1).toNat).length ≤ i := by
      simp only [List.length_range]
      omega
    simp [hi, List.getElem?_eq_none hb]

/-- On nonnegative inputs, the first and last tokens are `0` and `n`. -/
def endpoints_prop (n : Int) (s : String) : Prop :=
  0 ≤ n → (tokens s).head? = some "0" ∧
    (tokens s).getLast? = some (toString n.toNat)

theorem endpoints_thm (n : Int) : endpoints_prop n (string_sequence n) := by
  intro hn
  have hk : (n + 1).toNat = n.toNat + 1 := by omega
  rw [tokens_thm n, hk]
  constructor
  · rw [List.range_succ_eq_map]
    rfl
  · rw [List.range_succ, List.map_append, List.getLast?_append]
    rfl

private theorem go_append (acc sep : String) (xs ys : List String) :
    String.intercalate.go acc sep (xs ++ ys) =
      String.intercalate.go (String.intercalate.go acc sep xs) sep ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => exact ih (acc ++ sep ++ x)

private theorem intercalate_append_singleton (sep : String) (xs : List String)
    (x : String) (h : xs ≠ []) :
    String.intercalate sep (xs ++ [x]) = String.intercalate sep xs ++ sep ++ x := by
  cases xs with
  | nil => contradiction
  | cons a xs =>
    simpa only [List.cons_append, String.intercalate, String.intercalate.go] using
      go_append a sep xs [x]

/-- Extending a nonempty sequence appends one space and the next numeral. -/
def step_prop (n : Int) (s : String) : Prop :=
  0 ≤ n → string_sequence (n + 1) = s ++ " " ++ toString (n + 1).toNat

theorem step_thm (n : Int) : step_prop n (string_sequence n) := by
  intro hn
  have hk : (n + 1 + 1).toNat = (n + 1).toNat + 1 := by omega
  unfold string_sequence
  rw [hk, List.range_succ, List.map_append, List.map_singleton]
  apply intercalate_append_singleton
  have hp : 0 < (n + 1).toNat := by omega
  simpa using (Nat.ne_of_gt hp)

/-- All observable sequence properties, with no restriction on integer inputs. -/
def Post_prop (n : Int) (s : String) : Prop :=
  sequence_prop n s ∧ empty_prop n s ∧ tokens_prop n s ∧ count_prop n s ∧
    position_prop n s ∧ endpoints_prop n s ∧ step_prop n s

/- Property-based tests.  These evaluate the implementation on every integer
from -30 through 120, including the empty/nonempty transition and multiple
decimal digit boundaries.  The checks use executable expressions directly. -/
private def testInputs : List Int := (List.range 151).map (fun k => (k : Int) - 30)

-- PBT for sequence_prop.
example : testInputs.all (fun n =>
    string_sequence n ==
      String.intercalate " " ((List.range (n + 1).toNat).map toString)) = true := by
  native_decide

-- PBT for empty_prop, including both directions of the equivalence.
example : testInputs.all (fun n =>
    (string_sequence n == "") == decide (n < 0)) = true := by
  native_decide

-- PBT for tokens_prop.
example : testInputs.all (fun n =>
    tokens (string_sequence n) == (List.range (n + 1).toNat).map toString) = true := by
  native_decide

-- PBT for count_prop.
example : testInputs.all (fun n =>
    (tokens (string_sequence n)).length == (n + 1).toNat) = true := by
  native_decide

-- PBT for position_prop: 160 indices per input, including out-of-range indices.
example : testInputs.all (fun n => (List.range 160).all (fun i =>
    (tokens (string_sequence n))[i]? ==
      if (i : Int) ≤ n then some (toString i) else none)) = true := by
  native_decide

-- PBT for endpoints_prop.
example : testInputs.all (fun n => decide (n < 0) ||
    ((tokens (string_sequence n)).head? == some "0" &&
      (tokens (string_sequence n)).getLast? == some (toString n.toNat))) = true := by
  native_decide

-- PBT for step_prop.
example : testInputs.all (fun n => decide (n < 0) ||
    (string_sequence (n + 1) == string_sequence n ++ " " ++
      toString (n + 1).toNat)) = true := by
  native_decide

/-- Executable conjunction of the postcondition's clauses at index `i`.
Universally checking `i` checks the universal clause in `position_prop`. -/
private def postCheck (n : Int) (i : Nat) : Bool :=
  let s := string_sequence n
  (s == String.intercalate " " ((List.range (n + 1).toNat).map toString)) &&
  ((s == "") == decide (n < 0)) &&
  (tokens s == (List.range (n + 1).toNat).map toString) &&
  ((tokens s).length == (n + 1).toNat) &&
  ((tokens s)[i]? == if (i : Int) ≤ n then some (toString i) else none) &&
  (decide (n < 0) || ((tokens s).head? == some "0" &&
    (tokens s).getLast? == some (toString n.toNat))) &&
  (decide (n < 0) || (string_sequence (n + 1) == s ++ " " ++
    toString (n + 1).toNat))

-- PBT for Post_prop: all clauses together over the same bounded input grid.
example : testInputs.all (fun n =>
    (List.range 160).all (postCheck n)) = true := by
  native_decide

-- Randomized PBT for Post_prop, sampling both integer inputs and token positions.
#eval Plausible.Testable.check (∀ n : Int, ∀ i : Nat, postCheck n i = true)

theorem correctness (n : Int) : Pre n → Post_prop n (string_sequence n) := by
  intro _
  exact ⟨sequence_thm n, empty_thm n, tokens_thm n, count_thm n,
    position_thm n, endpoints_thm n, step_thm n⟩

/-- A direct mutable loop.  Its Boolean state ensures that exactly one space is
inserted before every numeral after the first. -/
def string_sequence_imp (n : Int) : String := Id.run do
  let mut result := ""
  let mut first := true
  for i in List.range (n + 1).toNat do
    if first then
      result := toString i
      first := false
    else
      result := result ++ " " ++ toString i
  return result

example : string_sequence_imp 0 = "0" := by native_decide
example : string_sequence_imp 3 = "0 1 2 3" := by native_decide
example : string_sequence_imp 5 = "0 1 2 3 4 5" := by native_decide
example : string_sequence_imp 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide
example : string_sequence_imp (-1) = "" := by native_decide
example : string_sequence_imp (-20) = "" := by native_decide

#eval string_sequence_imp 5
#eval string_sequence_imp (-3)

-- Bounded PBT for functional/imperative agreement.
example : testInputs.all (fun n =>
    string_sequence n == string_sequence_imp n) = true := by
  native_decide

private def loopStep (state : MProd Bool String) (i : Nat) : MProd Bool String :=
  if state.fst then ⟨false, toString i⟩ else ⟨state.fst, state.snd ++ " " ++ toString i⟩

/-- Loop invariant after the first numeral has been emitted. -/
private theorem fold_after_first (xs : List Nat) (acc : String) :
    xs.foldl loopStep ⟨false, acc⟩ =
      ⟨false, String.intercalate.go acc " " (xs.map toString)⟩ := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
    simpa only [List.foldl_cons, loopStep, Bool.false_eq_true, ↓reduceIte,
      List.map_cons, String.intercalate.go] using ih (acc ++ " " ++ toString i)

private theorem fold_render (xs : List Nat) :
    (xs.foldl loopStep ⟨true, ""⟩).snd = String.intercalate " " (xs.map toString) := by
  cases xs with
  | nil => rfl
  | cons i xs =>
    simp only [List.foldl_cons, loopStep, ↓reduceIte]
    rw [fold_after_first]
    rfl

/-- The mutable loop and functional translation agree for every Python integer. -/
theorem functional_eq_imperative (n : Int) :
    string_sequence n = string_sequence_imp n := by
  have hstep :
      (fun (i : Nat) (state : MProd Bool String) =>
        if state.fst then (pure (ForInStep.yield (MProd.mk false (toString i))) : Id _)
        else pure (ForInStep.yield ⟨state.fst, state.snd ++ " " ++ toString i⟩)) =
      (fun i state => (pure (ForInStep.yield (loopStep state i)) : Id _)) := by
    funext i ⟨first, result⟩
    cases first <;> rfl
  unfold string_sequence string_sequence_imp
  change String.intercalate " " ((List.range (n + 1).toNat).map toString) =
    ((forIn (m := Id) (List.range (n + 1).toNat) (MProd.mk true "")
      (fun i state => if state.fst then pure (ForInStep.yield ⟨false, toString i⟩)
        else pure (ForInStep.yield ⟨state.fst, state.snd ++ " " ++ toString i⟩))).run).snd
  rw [hstep, List.forIn_pure_yield_eq_foldl]
  exact (fold_render _).symm

end humaneval_15_string_sequence
