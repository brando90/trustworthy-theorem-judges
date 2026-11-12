import Mathlib

/-!
# HumanEval/15 — `string_sequence`

Python source:

```python
def string_sequence(n: int) -> str:
    return ' '.join([str(x) for x in range(n + 1)])
```

The function returns the string of space-delimited numbers `0 1 2 ... n`.

Contents of this file:
* `stringSequence`: functional implementation (structural recursion on `n`),
* unit tests (`native_decide` examples and `#eval`),
* the precondition `Pre`, property propositions and their proofs,
* the post-condition `Post_prop` (conjunction of the properties),
* property-based tests (bounded, plus randomized Plausible checks),
* the correctness theorem `Pre → Post`,
* `stringSequenceImp`: an imperative implementation in `Id` with mutable state,
* the equivalence theorem `stringSequence n = stringSequenceImp n`.
-/

namespace humaneval_15_string_sequence

/-- Functional implementation: the space-delimited sequence `0 1 2 … n`. -/
def stringSequence : Nat → String
  | 0 => "0"
  | n + 1 => stringSequence n ++ " " ++ toString (n + 1)

-- ## Unit tests

example : stringSequence 0 = "0" := by native_decide
example : stringSequence 3 = "0 1 2 3" := by native_decide
example : stringSequence 5 = "0 1 2 3 4 5" := by native_decide
example : stringSequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval stringSequence 5
#eval stringSequence 10

/-- Precondition: every natural number is admissible. -/
def Pre (_n : Nat) : Prop := True

/-- Property: the result is never the empty string. -/
def stringSequence_nonempty_prop (n : Nat) : Prop := stringSequence n ≠ ""

/-- Property: the result ends with the decimal representation of `n`. -/
def stringSequence_suffix_prop (n : Nat) : Prop := ∃ s : String, stringSequence n = s ++ toString n

/-- Property: exact length — `n` separator spaces plus the lengths of the
decimal representations of `0, …, n`. -/
def stringSequence_length_prop (n : Nat) : Prop :=
  (stringSequence n).length = n + Finset.sum (Finset.range (n + 1)) (fun i => (toString i).length)

theorem stringSequence_length_pos : ∀ n : Nat, 0 < (stringSequence n).length := by
  intro n
  induction n with
  | zero => decide
  | succ k ih =>
    have hspace : (" " : String).length = 1 := rfl
    simp only [stringSequence, String.length_append, hspace]
    omega

theorem stringSequence_nonempty_thm (n : Nat) : stringSequence_nonempty_prop n := by
  intro h
  have hpos := stringSequence_length_pos n
  rw [h] at hpos
  exact absurd hpos (by decide)

theorem stringSequence_suffix_thm (n : Nat) : stringSequence_suffix_prop n := by
  induction n with
  | zero => exact ⟨"", by decide⟩
  | succ k _ =>
    refine ⟨stringSequence k ++ " ", ?_⟩
    simp only [stringSequence]

theorem stringSequence_length_thm (n : Nat) : stringSequence_length_prop n := by
  induction n with
  | zero =>
    show (stringSequence 0).length = 0 + Finset.sum (Finset.range (0 + 1)) (fun i => (toString i).length)
    decide
  | succ k ih =>
    have hspace : (" " : String).length = 1 := rfl
    have ih' : (stringSequence k).length =
        k + Finset.sum (Finset.range (k + 1)) (fun i => (toString i).length) := ih
    simp only [stringSequence_length_prop, stringSequence, String.length_append, hspace]
    rw [Finset.sum_range_succ]
    rw [ih']
    ring

/-- Post-condition: the conjunction of all stated properties. -/
def Post_prop (n : Nat) : Prop :=
  stringSequence_nonempty_prop n ∧ stringSequence_suffix_prop n ∧ stringSequence_length_prop n

-- ## Property-based tests

/-- PBT (bounded) for the nonemptiness property. -/
example : (List.range 100).all (fun n => stringSequence n != "") = true := by native_decide

/-- PBT (bounded) for the suffix property. -/
example : (List.range 100).all (fun n => (stringSequence n).endsWith (toString n)) = true := by
  native_decide

/-- PBT (bounded) for the length property. -/
example : (List.range 60).all (fun n =>
    (stringSequence n).length == n + ((List.range (n + 1)).map fun i => (toString i).length).sum) = true := by
  native_decide

/-- PBT (bounded) for the post-condition. -/
example : (List.range 60).all (fun n =>
    stringSequence n != "" &&
    (stringSequence n).endsWith (toString n) &&
    ((stringSequence n).length == n + ((List.range (n + 1)).map fun i => (toString i).length).sum)) = true := by
  native_decide

-- PBT (randomized, Plausible) for the nonemptiness and suffix properties
#eval Plausible.Testable.check (∀ n : Nat, stringSequence n ≠ "")
#eval Plausible.Testable.check (∀ n : Nat, (stringSequence n).endsWith (toString n) = true)

/-- Correctness theorem: the functional implementation satisfies the post-condition. -/
theorem stringSequence_correct (n : Nat) : Pre n → Post_prop n := fun _ =>
  ⟨stringSequence_nonempty_thm n, stringSequence_suffix_thm n, stringSequence_length_thm n⟩

-- ## Auxiliary lemmas for the equivalence proof

theorem range'_succ (s n : Nat) : List.range' s (n + 1) = List.range' s n ++ [s + n] := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
    show List.range' s (k + 1 + 1) = List.range' s (k + 1) ++ [s + (k + 1)]
    rw [show List.range' s (k + 1 + 1) = s :: List.range' (s + 1) (k + 1) from rfl]
    rw [show List.range' s (k + 1) = s :: List.range' (s + 1) k from rfl]
    rw [List.cons_append, ih (s + 1)]
    have h3 : s + 1 + k = s + (k + 1) := by omega
    rw [h3]

theorem foldl_range'_succ {β : Type} (f : β → Nat → β) (acc : β) (s n : Nat) :
    (List.range' s (n + 1)).foldl f acc = f ((List.range' s n).foldl f acc) (s + n) := by
  rw [range'_succ, List.foldl_append]
  try rfl

theorem stringSequence_eq_foldl (n : Nat) :
    stringSequence n = (List.range' 1 n).foldl (fun acc i => acc ++ " " ++ toString i) (toString 0) := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [foldl_range'_succ, ← ih, Nat.add_comm 1 k]
    try rfl

theorem foldl_attach_ignore {α β : Type} (xs : List α) (f : β → α → β) (init : β) :
    xs.attach.foldl (fun b ⟨a, _⟩ => f b a) init = xs.foldl f init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.attach_cons, List.foldl_cons, List.foldl_map]
    exact ih _

theorem idRun_forIn_eq_foldl {α β : Type} (xs : List α) (init : β) (f : β → α → β) :
    Id.run (ForIn.forIn xs init (fun x acc => pure (ForInStep.yield (f acc x)))) = xs.foldl f init := by
  show Id.run (ForIn'.forIn' xs init (fun a _ acc => pure (ForInStep.yield (f acc a)))) = xs.foldl f init
  rw [List.forIn'_pure_yield_eq_foldl]
  show xs.attach.foldl (fun b ⟨a, _⟩ => f b a) init = xs.foldl f init
  exact foldl_attach_ignore xs f init

/-- Imperative implementation: builds the string with a mutable accumulator. -/
def stringSequenceImp (n : Nat) : String := Id.run do
  let mut acc := toString 0
  for i in List.range' 1 n do
    acc := acc ++ " " ++ toString i
  return acc

-- ## Imperative tests

example : stringSequenceImp 0 = "0" := by native_decide
example : stringSequenceImp 3 = "0 1 2 3" := by native_decide
example : stringSequenceImp 5 = "0 1 2 3 4 5" := by native_decide
example : stringSequenceImp 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

#eval stringSequenceImp 5

/-- Equivalence: the functional and imperative implementations agree on every input. -/
theorem stringSequence_eq_imp (n : Nat) : stringSequence n = stringSequenceImp n := by
  rw [stringSequence_eq_foldl]
  have h : stringSequenceImp n =
      (List.range' 1 n).foldl (fun acc i => acc ++ " " ++ toString i) (toString 0) := by
    unfold stringSequenceImp
    exact idRun_forIn_eq_foldl (List.range' 1 n) (toString 0) (fun acc i => acc ++ " " ++ toString i)
  rw [h]

end humaneval_15_string_sequence
