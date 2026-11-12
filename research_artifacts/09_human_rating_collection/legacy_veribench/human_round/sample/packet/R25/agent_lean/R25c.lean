import Mathlib

/-!
# HumanEval 15 — `string_sequence`

Python original:

```python
def string_sequence(n: int) -> str:
    """ Return a string containing space-delimited numbers starting from 0 upto n inclusive. """
    return ' '.join([str(x) for x in range(n + 1)])
```

`range(n + 1)` enumerates `0, 1, …, n`, each element is rendered with `str`, and the
pieces are joined with a single space.  Since the interesting behaviour of the Python
function only happens for non-negative arguments (for `n < 0` the range is empty and the
result is `""`), the argument is modelled as a `Nat`.

This file contains

* a functional implementation `stringSequence` (`' '.join` ↦ `String.intercalate " "`),
* unit tests mirroring the Python `check` function,
* a pre-condition `Pre`, several property predicates with proofs, a post-condition
  `Post_prop` and the correctness theorem `Pre → Post`,
* an imperative implementation `stringSequenceImp` written with `Id.run do` and mutable
  state, plus the equivalence theorem `stringSequence = stringSequenceImp`.
-/

namespace humaneval_15_string_sequence

/-! ## Functional implementation -/

/-- `stringSequence n = "0 1 2 … n"`, the space-delimited numbers from `0` up to `n`. -/
def stringSequence (n : Nat) : String :=
  String.intercalate " " ((List.range (n + 1)).map toString)

/-! ## Unit tests (the Python `check` function) -/

example : stringSequence 0 = "0" := by native_decide
example : stringSequence 3 = "0 1 2 3" := by native_decide
example : stringSequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval stringSequence 0
#eval stringSequence 3
#eval stringSequence 10

/-! ## Pre-condition

The Python function is total: every `int` is accepted.  Modelling the argument as a `Nat`
(the range is non-empty exactly for `n ≥ 0`) the pre-condition is vacuous. -/

def Pre (n : Nat) : Prop := 0 ≤ n

/-! ## Auxiliary lemmas

The decimal rendering of a natural number never contains a space; this is what makes the
space a genuine separator, i.e. what makes `' '.join` invertible by splitting on `' '`. -/

private theorem digitChar_ne_space {d : Nat} (h : d < 10) : Nat.digitChar d ≠ ' ' := by
  interval_cases d <;> decide

private theorem toDigitsCore_ne_space :
    ∀ (fuel n : Nat) (acc : List Char), (∀ c ∈ acc, c ≠ ' ') →
      ∀ c ∈ Nat.toDigitsCore 10 fuel n acc, c ≠ ' ' := by
  intro fuel
  induction fuel with
  | zero => intro n acc hacc c hc; exact hacc c hc
  | succ f ih =>
    intro n acc hacc
    have hd : ∀ c ∈ (Nat.digitChar (n % 10) :: acc), c ≠ ' ' := by
      intro c hc
      rcases List.mem_cons.mp hc with h | h
      · subst h; exact digitChar_ne_space (Nat.mod_lt _ (by norm_num))
      · exact hacc c h
    simp only [Nat.toDigitsCore]
    split
    · exact hd
    · exact ih _ _ hd

/-- The decimal representation of a natural number contains no space character. -/
theorem space_not_mem_toString (x : Nat) : ' ' ∉ (toString x).data := by
  have h : (toString x).data = Nat.toDigitsCore 10 (x + 1) x [] := rfl
  intro hmem
  rw [h] at hmem
  exact toDigitsCore_ne_space _ _ _ (by simp) _ hmem rfl

/-- Appending one more piece to a non-empty `String.intercalate`. -/
private theorem intercalate_go_append (sep x : String) :
    ∀ (l : List String) (acc : String),
      String.intercalate.go acc sep (l ++ [x]) =
        String.intercalate.go acc sep l ++ sep ++ x := by
  intro l
  induction l with
  | nil => intro acc; simp [String.intercalate.go]
  | cons a as ih => intro acc; simp [String.intercalate.go, ih]

private theorem intercalate_append_singleton (sep x a : String) (as : List String) :
    String.intercalate sep (a :: (as ++ [x])) =
      String.intercalate sep (a :: as) ++ sep ++ x :=
  intercalate_go_append sep x as a

/-- The character list underlying `String.intercalate.go`. -/
private theorem data_intercalate_go (sep : String) :
    ∀ (l : List String) (acc : String),
      (String.intercalate.go acc sep l).data =
        acc.data ++ (l.map (fun s => sep.data ++ s.data)).flatten := by
  intro l
  induction l with
  | nil => intro acc; simp [String.intercalate.go]
  | cons a as ih =>
    intro acc
    simp [String.intercalate.go, ih, List.append_assoc]

private theorem flatten_intersperse {α : Type*} (s : List α) :
    ∀ (xs : List (List α)) (x : List α),
      (List.intersperse s (x :: xs)).flatten = x ++ (xs.map (fun y => s ++ y)).flatten := by
  intro xs
  induction xs with
  | nil => intro x; simp
  | cons a as ih =>
    intro x
    simp [List.intersperse, ih a, List.append_assoc]

/-- `String.intercalate` on the level of the underlying character lists is
`List.intercalate`. -/
private theorem data_intercalate (sep a : String) (as : List String) :
    (String.intercalate sep (a :: as)).data =
      List.intercalate sep.data ((a :: as).map String.data) := by
  show (String.intercalate.go a sep as).data = _
  rw [data_intercalate_go, List.intercalate, List.map_cons, flatten_intersperse]
  simp [Function.comp_def]

/-- The list `[0, 1, …, n]` rendered with `toString` is never empty; here is a
concrete head/tail decomposition. -/
private theorem range_map_toString_cons (n : Nat) :
    (List.range (n + 1)).map toString =
      toString 0 :: ((List.range n).map Nat.succ).map toString := by
  rw [List.range_succ_eq_map, List.map_cons]

/-! ## Properties -/

/-- `string_sequence(0) == '0'`. -/
def base_prop : Prop := stringSequence 0 = "0"

theorem base_thm : base_prop := by
  unfold base_prop
  rfl

/-- Going from `n` to `n + 1` appends `" " ++ str(n+1)`. -/
def step_prop (n : Nat) : Prop :=
  stringSequence (n + 1) = stringSequence n ++ " " ++ toString (n + 1)

theorem step_thm (n : Nat) : step_prop n := by
  unfold step_prop stringSequence
  rw [List.range_succ (n := n + 1), List.map_append, range_map_toString_cons n,
    List.cons_append]
  simp only [List.map_cons, List.map_nil]
  rw [intercalate_append_singleton]

/-- Splitting the result on `' '` recovers exactly the rendered numbers `0, 1, …, n`.
This is the faithful counterpart of `' '.join`. -/
def split_prop (n : Nat) : Prop :=
  (stringSequence n).split (· == ' ') = (List.range (n + 1)).map toString

theorem split_thm (n : Nat) : split_prop n := by
  unfold split_prop stringSequence
  rw [String.split_of_valid, range_map_toString_cons n, data_intercalate]
  have hx : ∀ l ∈ (toString 0 :: ((List.range n).map Nat.succ).map toString).map String.data,
      ' ' ∉ l := by
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨s, hs, rfl⟩ := hl
    simp only [List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | ⟨y, _, rfl⟩
    · exact space_not_mem_toString 0
    · exact space_not_mem_toString y
  have hne : (toString 0 :: ((List.range n).map Nat.succ).map toString).map String.data ≠ [] := by
    simp
  have hsplit :
      List.splitOnP (fun c => c == ' ')
        (List.intercalate (" " : String).data
          ((toString 0 :: ((List.range n).map Nat.succ).map toString).map String.data)) =
        (toString 0 :: ((List.range n).map Nat.succ).map toString).map String.data :=
    List.splitOn_intercalate _ ' ' hx hne
  rw [hsplit, List.map_map]
  simp [Function.comp]

/-- The result splits into exactly `n + 1` tokens. -/
def count_prop (n : Nat) : Prop := ((stringSequence n).split (· == ' ')).length = n + 1

theorem count_thm (n : Nat) : count_prop n := by
  unfold count_prop
  rw [split_thm n]
  simp

/-- The `i`-th token is `str(i)`, for every `i ≤ n`. -/
def entries_prop (n : Nat) : Prop :=
  ∀ i ≤ n, ((stringSequence n).split (· == ' '))[i]? = some (toString i)

theorem entries_thm (n : Nat) : entries_prop n := by
  unfold entries_prop
  intro i hi
  rw [split_thm n, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-! ## Post-condition and correctness -/

def Post_prop (n : Nat) : Prop :=
  split_prop n ∧ count_prop n ∧ entries_prop n ∧ step_prop n

theorem correctness (n : Nat) (_h : Pre n) : Post_prop n :=
  ⟨split_thm n, count_thm n, entries_thm n, step_thm n⟩

/-! ## Imperative implementation -/

/-- One iteration of the imperative loop: append `str i`, preceded by a separator unless
this is the very first piece (`none`). -/
def step (o : Option String) (i : Nat) : Option String :=
  match o with
  | none => some (toString i)
  | some s => some (s ++ " " ++ toString i)

/-- Imperative version: walk over `0, 1, …, n` accumulating the answer in a mutable
variable.  The `Option` records whether a separator still has to be emitted (i.e. whether
we are at the first element), mirroring how `str.join` behaves. -/
def stringSequenceImp (n : Nat) : String := Id.run do
  let mut out : Option String := none
  for i in List.range (n + 1) do
    out := step out i
  return out.getD ""

/-! ## Imperative unit tests -/

example : stringSequenceImp 0 = "0" := by native_decide
example : stringSequenceImp 3 = "0 1 2 3" := by native_decide
example : stringSequenceImp 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval stringSequenceImp 0
#eval stringSequenceImp 3
#eval stringSequenceImp 10

/-! ## Equivalence of the two implementations -/

private theorem imp_eq_foldl (n : Nat) :
    stringSequenceImp n = ((List.range (n + 1)).foldl step none).getD "" := by
  simp [stringSequenceImp]

private theorem foldl_step_some :
    ∀ (l : List Nat) (a : String),
      l.foldl step (some a) = some (String.intercalate.go a " " (l.map toString)) := by
  intro l
  induction l with
  | nil => intro a; simp [String.intercalate.go]
  | cons b bs ih => intro a; simp [step, ih, String.intercalate.go]

theorem functional_eq_imperative (n : Nat) : stringSequence n = stringSequenceImp n := by
  rw [imp_eq_foldl]
  unfold stringSequence
  rw [range_map_toString_cons n, List.range_succ_eq_map, List.foldl_cons]
  have h0 : step none 0 = some (toString 0) := rfl
  rw [h0, foldl_step_some]
  rfl

end humaneval_15_string_sequence
