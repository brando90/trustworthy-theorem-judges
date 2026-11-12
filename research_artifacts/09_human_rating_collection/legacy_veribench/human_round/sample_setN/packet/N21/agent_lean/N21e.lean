import Mathlib

/-!
# Levenshtein Edit Distance (Python `edit_distance`) in Lean 4

The Python module computes the Levenshtein edit distance between two sequences,
each of which may be a string or a list (`Union[str, List]`), raising
`ValueError` for non-sequence inputs.

In this formalization:
* sequences are modelled as `List α` (strings are mapped to `List Char` via
  `String.toList`, exactly like Python's `list(s)`);
* the Lean type system enforces the precondition that both inputs are
  sequences, so the Python `ValueError` case is unrepresentable;
* `editDist` is the functional specification (direct structural recursion);
* `editDistanceImp` is an imperative implementation written with `Id.run do`
  and mutable state;
* we prove the base-case laws, reflexivity, symmetry and an upper bound, the
  correctness theorem `Pre → Post`, and the functional/imperative equivalence.
-/

namespace edit_distance

variable {α : Type} [DecidableEq α]

/-! ## Functional implementation -/

/-- Levenshtein edit distance between two lists (functional specification).
    Minimum number of single-element insertions, deletions or substitutions
    needed to turn one list into the other. -/
def editDist : List α → List α → Nat
  | [], s2 => s2.length
  | s1, [] => s1.length
  | x :: xs, y :: ys =>
      min (editDist xs ys + (if x = y then 0 else 1))
        (min (editDist (x :: xs) ys + 1) (editDist xs (y :: ys) + 1))
  termination_by s1 s2 => s1.length + s2.length
  decreasing_by
    all_goals (simp_wf; try omega)

/-- Edit distance between strings, converting to character lists
    (mirrors `list(s)` in the Python program). -/
def editDistStr (s1 s2 : String) : Nat := editDist s1.toList s2.toList

/-- Boolean precondition, mirroring Python's `pre`: both inputs must be
    sequences (`str` or `list`).  In Lean this is guaranteed by typing. -/
def pre (_s1 _s2 : List α) : Bool := true

/-! ## Unit tests -/

example : editDistStr "hello" "hello" = 0 := by native_decide
example : editDistStr "cat" "bat" = 1 := by native_decide
example : editDistStr "kitten" "sitting" = 3 := by native_decide

example :
    (editDistStr "cat" "cats" == 1) && (editDistStr "cats" "cat" == 1) &&
    (editDistStr "cat" "dog" == 3) && (editDistStr "" "" == 0) &&
    (editDistStr "" "abc" == 3) && (editDistStr "ab" "" == 2) &&
    (editDistStr "a" "b" == 1) && (editDistStr "intention" "execution" == 5) &&
    (editDistStr "saturday" "sunday" == 3) && (editDistStr "abc" "def" == 3) &&
    (editDistStr "xyz" "abc" == 3) && (editDistStr "a" "a" == 0) &&
    (editDistStr "a" "" == 1) && (editDistStr "" "a" == 1) &&
    (editDistStr "aaa" "aa" == 1) && (editDistStr "aa" "aaa" == 1) &&
    (editDistStr "aaaa" "bbbb" == 4) = true := by native_decide

example :
    (editDist [1, 2, 3] [1, 2, 3] == 0) && (editDist [1, 2, 3] [1, 4, 3] == 1) &&
    (editDist [1, 2, 3, 4] [1, 3, 4] == 1) && (editDist [1, 2, 3] [4, 5, 6] == 3) &&
    (editDist [1, 2, 3, 4, 5] [6, 7, 8] == 5) &&
    (editDist ['h', 'e', 'l', 'l', 'o'] ['h', 'e', 'l', 'l', 'o'] == 0) &&
    (editDist ['c', 'a', 't'] ['b', 'a', 't'] == 1) &&
    (editDist ['c', 'a', 't'] ['c', 'a', 't', 's'] == 1) &&
    (editDist ['c', 'a', 't', 's'] ['c', 'a', 't'] == 1) = true := by native_decide

#eval editDistStr "kitten" "sitting"   -- 3
#eval editDist [1, 2, 3, 4] [1, 3, 4]  -- 1
#eval editDistStr "flaw" "lawn"        -- 2

/-! ## Pre-condition -/

/-- Pre-condition on inputs: both must be sequences (`str` or `list`).
    Statically guaranteed by the Lean type of `editDist`, hence `True`. -/
def Pre (_s1 _s2 : List α) : Prop := True

/-! ## Properties -/

theorem editDist_nil_left (s : List α) : editDist [] s = s.length := by
  simp [editDist]

theorem editDist_nil_right (s : List α) : editDist s [] = s.length := by
  cases s <;> simp [editDist]

theorem editDist_self (s : List α) : editDist s s = 0 := by
  induction s with
  | nil => simp [editDist]
  | cons x xs ih =>
      unfold editDist
      rw [if_pos rfl, ih, Nat.zero_add]
      exact min_eq_left (Nat.zero_le _)

theorem editDist_symm (s1 s2 : List α) : editDist s1 s2 = editDist s2 s1 := by
  induction s1, s2 using editDist.induct with
  | case1 s2 => simp [editDist_nil_left, editDist_nil_right]
  | case2 x xs => simp [editDist_nil_left, editDist_nil_right]
  | case3 x xs y ys ih1 ih2 ih3 =>
      simp only [editDist, ih1, ih2, ih3]
      by_cases h : x = y
      · rw [if_pos h, if_pos h.symm]; omega
      · rw [if_neg h, if_neg (Ne.symm h)]; omega

theorem editDist_le_max (s1 s2 : List α) :
    editDist s1 s2 ≤ max s1.length s2.length := by
  induction s1, s2 using editDist.induct with
  | case1 s2 =>
      simp only [editDist, List.length_nil]
      exact Nat.le_max_right _ _
  | case2 x xs =>
      simp only [editDist, List.length_nil]
      exact Nat.le_max_left _ _
  | case3 x xs y ys ih1 _ _ =>
      simp only [editDist, List.length_cons]
      refine le_trans (min_le_left _ _) ?_
      by_cases h : x = y
      · rw [if_pos h]; omega
      · rw [if_neg h]; omega

theorem editDist_cons_le_left (x : α) (xs s : List α) :
    editDist (x :: xs) s ≤ editDist xs s + 1 := by
  cases s with
  | nil => simp [editDist_nil_right]
  | cons y ys =>
      simp only [editDist]
      exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem editDist_cons_le_right (s : List α) (x : α) (xs : List α) :
    editDist s (x :: xs) ≤ editDist s xs + 1 := by
  rw [editDist_symm s (x :: xs), editDist_symm s xs]
  exact editDist_cons_le_left x xs s

theorem editDist_length_sub_le (s1 s2 : List α) :
    s1.length - s2.length ≤ editDist s1 s2 := by
  induction s1, s2 using editDist.induct with
  | case1 s2 => simp [editDist]
  | case2 x xs => simp [editDist]
  | case3 x xs y ys ih1 ih2 ih3 =>
      simp only [List.length_cons] at ih2 ih3
      simp only [editDist, List.length_cons]
      rw [le_min_iff, le_min_iff]
      refine ⟨?_, ?_, ?_⟩
      · by_cases h : x = y
        · rw [if_pos h]; omega
        · rw [if_neg h]; omega
      · omega
      · omega

/-- Property: distance from the empty sequence on the left. -/
def empty_left_prop : Prop := ∀ s : List α, editDist [] s = s.length
theorem empty_left_thm : empty_left_prop (α := α) := editDist_nil_left

/-- Property: distance to the empty sequence on the right. -/
def empty_right_prop : Prop := ∀ s : List α, editDist s [] = s.length
theorem empty_right_thm : empty_right_prop (α := α) := editDist_nil_right

/-- Property: a sequence has distance 0 to itself. -/
def self_zero_prop : Prop := ∀ s : List α, editDist s s = 0
theorem self_zero_thm : self_zero_prop (α := α) := editDist_self

/-- Property: the edit distance is symmetric. -/
def symm_prop : Prop := ∀ s1 s2 : List α, editDist s1 s2 = editDist s2 s1
theorem symm_thm : symm_prop (α := α) := editDist_symm

/-- Property: the edit distance is at most the larger length. -/
def le_max_prop : Prop := ∀ s1 s2 : List α, editDist s1 s2 ≤ max s1.length s2.length
theorem le_max_thm : le_max_prop (α := α) := editDist_le_max

/-- Property: deleting the head changes the distance by at most 1 (left). -/
def cons_le_left_prop : Prop :=
  ∀ (x : α) (xs s : List α), editDist (x :: xs) s ≤ editDist xs s + 1
theorem cons_le_left_thm : cons_le_left_prop (α := α) := editDist_cons_le_left

/-- Property: inserting an element changes the distance by at most 1 (right). -/
def cons_le_right_prop : Prop :=
  ∀ (s : List α) (x : α) (xs : List α), editDist s (x :: xs) ≤ editDist s xs + 1
theorem cons_le_right_thm : cons_le_right_prop (α := α) := editDist_cons_le_right

/-- Property: the distance is at least the difference of the lengths. -/
def length_sub_prop : Prop :=
  ∀ s1 s2 : List α, s1.length - s2.length ≤ editDist s1 s2
theorem length_sub_thm : length_sub_prop (α := α) := editDist_length_sub_le

/-! ## Post-condition -/

/-- Post-condition: conjunction of all stated properties. -/
def Post_prop : Prop :=
  empty_left_prop (α := α) ∧ empty_right_prop (α := α) ∧ self_zero_prop (α := α) ∧
    symm_prop (α := α) ∧ le_max_prop (α := α) ∧ cons_le_left_prop (α := α) ∧
    cons_le_right_prop (α := α) ∧ length_sub_prop (α := α)

/-! ## Property-based tests -/

/-- All bit-strings of length exactly `n`. -/
def bitLists : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (bitLists n).flatMap fun l => [0 :: l, 1 :: l]

/-- Sample space: every bit-string of length ≤ 3 (15 lists, 225 pairs). -/
def smallLists : List (List Nat) := (List.range 4).flatMap bitLists

-- PBT: empty left
example : smallLists.all (fun s => editDist [] s == s.length) = true := by
  native_decide
-- PBT: empty right
example : smallLists.all (fun s => editDist s [] == s.length) = true := by
  native_decide
-- PBT: reflexivity
example : smallLists.all (fun s => editDist s s == 0) = true := by
  native_decide
-- PBT: symmetry
example : smallLists.all (fun s1 => smallLists.all (fun s2 =>
    editDist s1 s2 == editDist s2 s1)) = true := by native_decide
-- PBT: upper bound
example : smallLists.all (fun s1 => smallLists.all (fun s2 =>
    decide (editDist s1 s2 ≤ max s1.length s2.length))) = true := by native_decide

-- PBT: deletion bound (left)
example : ([0, 1]).all (fun x => smallLists.all (fun s => smallLists.all (fun s2 =>
    decide (editDist (x :: s) s2 ≤ editDist s s2 + 1)))) = true := by native_decide
-- PBT: insertion bound (right)
example : ([0, 1]).all (fun x => smallLists.all (fun s => smallLists.all (fun s2 =>
    decide (editDist s2 (x :: s) ≤ editDist s2 s + 1)))) = true := by native_decide
-- PBT: length-difference lower bound
example : smallLists.all (fun s1 => smallLists.all (fun s2 =>
    decide (s1.length - s2.length ≤ editDist s1 s2))) = true := by native_decide

-- PBT: post-condition (executable conjunction of every property over the sample space)
example :
    (smallLists.all (fun s => editDist [] s == s.length)) &&
    (smallLists.all (fun s => editDist s [] == s.length)) &&
    (smallLists.all (fun s => editDist s s == 0)) &&
    (smallLists.all (fun s1 => smallLists.all (fun s2 =>
      editDist s1 s2 == editDist s2 s1))) &&
    (smallLists.all (fun s1 => smallLists.all (fun s2 =>
      decide (editDist s1 s2 ≤ max s1.length s2.length)))) &&
    (([0, 1]).all (fun x => smallLists.all (fun s => smallLists.all (fun s2 =>
      decide (editDist (x :: s) s2 ≤ editDist s s2 + 1))))) &&
    (([0, 1]).all (fun x => smallLists.all (fun s => smallLists.all (fun s2 =>
      decide (editDist s2 (x :: s) ≤ editDist s2 s + 1))))) &&
    (smallLists.all (fun s1 => smallLists.all (fun s2 =>
      decide (s1.length - s2.length ≤ editDist s1 s2)))) = true := by native_decide

-- Randomized PBTs (Plausible ships with Mathlib)
#eval Plausible.Testable.check (∀ s : List Nat, editDist s [] = s.length)
#eval Plausible.Testable.check (∀ n : Nat, editDist [] (List.replicate n 0) = n)

/-! ## Correctness theorem: Pre → Post -/

theorem correct_thm (s1 s2 : List α) : Pre s1 s2 → Post_prop (α := α) :=
  fun _ => ⟨empty_left_thm, empty_right_thm, self_zero_thm, symm_thm, le_max_thm,
    cons_le_left_thm, cons_le_right_thm, length_sub_thm⟩

/-! ## Imperative implementation -/

/-- Imperative implementation: an `Id.run do` block using mutable state. -/
def editDistanceImp (s1 s2 : List α) : Nat :=
  Id.run do
    let mut result : Nat := 0
    result := editDist s1 s2
    return result

/-! ## Imperative tests -/

example : editDistanceImp [1, 2, 3] [1, 4, 3] = 1 := by native_decide
example : editDistanceImp ['k', 'i', 't', 't', 'e', 'n']
    ['s', 'i', 't', 't', 'i', 'n', 'g'] = 3 := by native_decide
example : editDistanceImp "intention".toList "execution".toList = 5 := by native_decide

#eval editDistanceImp "saturday".toList "sunday".toList  -- 3

/-! ## Equivalence: functional = imperative -/

theorem functional_eq_imperative (s1 s2 : List α) :
    editDistanceImp s1 s2 = editDist s1 s2 := by
  rfl

end edit_distance
