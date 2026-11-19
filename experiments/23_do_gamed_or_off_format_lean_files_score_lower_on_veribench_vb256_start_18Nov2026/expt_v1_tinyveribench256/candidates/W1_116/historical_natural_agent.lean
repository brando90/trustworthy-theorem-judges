import Mathlib
namespace Agent

/-!
# HumanEval 48: is_palindrome

Strings are viewed as lists of Unicode characters, not UTF-8 bytes.  The
functional implementation compares that list with its reversal.  The indexed
specification below expresses precisely the comparisons in the Python loop.
There are no restrictions on the input, including the empty string.
-/

namespace humaneval_48_is_palindrome

/-- Functional palindrome checker. -/
def is_palindrome (text : String) : Bool :=
  decide (text.toList = text.toList.reverse)

-- The seven tests from the Python source, and a Unicode example.
example : is_palindrome "" = true := by native_decide
example : is_palindrome "aba" = true := by native_decide
example : is_palindrome "aaaaa" = true := by native_decide
example : is_palindrome "zbcd" = false := by native_decide
example : is_palindrome "xywyx" = true := by native_decide
example : is_palindrome "xywyz" = false := by native_decide
example : is_palindrome "xywzx" = false := by native_decide
example : is_palindrome "λ🙂λ" = true := by native_decide
#eval ["", "aba", "aaaaa", "zbcd", "xywyx", "xywyz", "xywzx"].map is_palindrome

/-- Every Python string is admissible. -/
def Pre (_text : String) : Prop := True

/-- Acceptance is exactly equality with the reversed character sequence. -/
def reversal_prop (text : String) : Prop :=
  is_palindrome text = true ↔ text.toList = text.toList.reverse

theorem reversal_thm (text : String) : reversal_prop text := by
  simp [reversal_prop, is_palindrome]

/-- The pointwise test performed by Python, with safe indexing.
Both indices are valid under the bound on `i`. -/
def mirror_prop (text : String) : Prop :=
  is_palindrome text = true ↔
    ∀ i : Nat, i < text.toList.length →
      text.toList[i]? = text.toList[text.toList.length - 1 - i]?

/-- A list equals its reversal exactly when all valid mirrored indices agree. -/
theorem list_mirror_iff (xs : List Char) :
    xs = xs.reverse ↔
      ∀ i : Nat, i < xs.length → xs[i]? = xs[xs.length - 1 - i]? := by
  constructor
  · intro h i hi
    calc
      xs[i]? = xs.reverse[i]? := congrArg (fun ys : List Char => ys[i]?) h
      _ = xs[xs.length - 1 - i]? := List.getElem?_reverse hi
  · intro h
    apply List.ext_getElem?
    intro i
    by_cases hi : i < xs.length
    · rw [List.getElem?_reverse hi]
      exact h i hi
    · simp [Nat.le_of_not_lt hi]

theorem mirror_thm (text : String) : mirror_prop text := by
  exact (reversal_thm text).trans (list_mirror_iff text.toList)

/-- Rejection means that some mirrored pair differs. -/
def rejection_prop (text : String) : Prop :=
  is_palindrome text = false ↔
    ∃ i : Nat, i < text.toList.length ∧
      text.toList[i]? ≠ text.toList[text.toList.length - 1 - i]?

theorem rejection_thm (text : String) : rejection_prop text := by
  unfold rejection_prop
  have h := mirror_thm text
  unfold mirror_prop at h
  simpa using not_congr h

/-- Reversing the input does not change the answer. -/
def reverse_invariant_prop (text : String) : Prop :=
  is_palindrome (String.mk text.toList.reverse) = is_palindrome text

theorem reverse_invariant_thm (text : String) : reverse_invariant_prop text := by
  simp [reverse_invariant_prop, is_palindrome, eq_comm]

/-- Concatenating a string and its reversal always makes a palindrome. -/
def doubled_prop (text : String) : Prop :=
  is_palindrome (String.mk (text.toList ++ text.toList.reverse)) = true

theorem doubled_thm (text : String) : doubled_prop text := by
  simp [doubled_prop, is_palindrome, List.reverse_append]

/-- Empty and one-character strings are palindromes. -/
def short_prop (text : String) : Prop :=
  text.toList.length ≤ 1 → is_palindrome text = true

theorem short_thm (text : String) : short_prop text := by
  intro h
  apply (reversal_thm text).mpr
  cases hx : text.toList with
  | nil => rfl
  | cons a tail =>
    cases tail with
    | nil => rfl
    | cons b rest =>
      simp only [hx, List.length_cons] at h
      omega

/-- Complete observable specification, including the indexed success and
failure criteria and basic palindrome laws. -/
def Post_prop (text : String) : Prop :=
  reversal_prop text ∧ mirror_prop text ∧ rejection_prop text ∧
  reverse_invariant_prop text ∧ doubled_prop text ∧ short_prop text

/-! ## Exhaustive bounded property-based tests

Enumerate *all* words of length at most five over a three-character alphabet,
including a non-ASCII character. These are checks of executable Boolean forms,
not substitutes for the universal proofs above.
-/

def wordsOfLength : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => ['a', 'b', 'λ'].flatMap fun c => (wordsOfLength n).map (c :: ·)

def pbtInputs : List String :=
  ((List.range 6).flatMap wordsOfLength).map String.mk

/-- Executable form of the universal mirrored-index condition. -/
def allMirrors (text : String) : Bool :=
  (List.range text.toList.length).all fun i =>
    text.toList[i]? == text.toList[text.toList.length - 1 - i]?

/-- Executable form of an existential mismatch. -/
def someMismatch (text : String) : Bool :=
  (List.range text.toList.length).any fun i =>
    text.toList[i]? != text.toList[text.toList.length - 1 - i]?

-- PBT for reversal_prop.
example : pbtInputs.all (fun s =>
    is_palindrome s == decide (s.toList = s.toList.reverse)) = true := by
  native_decide
-- PBT for mirror_prop.
example : pbtInputs.all (fun s => is_palindrome s == allMirrors s) = true := by
  native_decide
-- PBT for rejection_prop.
example : pbtInputs.all (fun s => (!is_palindrome s) == someMismatch s) = true := by
  native_decide
-- PBT for reverse_invariant_prop.
example : pbtInputs.all (fun s =>
    is_palindrome (String.mk s.toList.reverse) == is_palindrome s) = true := by
  native_decide
-- PBT for doubled_prop.
example : pbtInputs.all (fun s =>
    is_palindrome (String.mk (s.toList ++ s.toList.reverse))) = true := by
  native_decide
-- PBT for short_prop, as a Boolean implication.
example : pbtInputs.all (fun s =>
    !(decide (s.toList.length ≤ 1)) || is_palindrome s) = true := by
  native_decide
-- PBT for the entire Post_prop conjunction.
example : pbtInputs.all (fun s =>
    (is_palindrome s == decide (s.toList = s.toList.reverse)) &&
    (is_palindrome s == allMirrors s) &&
    ((!is_palindrome s) == someMismatch s) &&
    (is_palindrome (String.mk s.toList.reverse) == is_palindrome s) &&
    is_palindrome (String.mk (s.toList ++ s.toList.reverse)) &&
    (!(decide (s.toList.length ≤ 1)) || is_palindrome s)) = true := by
  native_decide
#eval (pbtInputs.length, pbtInputs.all (fun s => is_palindrome s == allMirrors s))

/-- Correctness for every admissible string; the precondition excludes nothing. -/
theorem correctness_thm (text : String) : Pre text → Post_prop text := by
  intro _
  exact ⟨reversal_thm text, mirror_thm text, rejection_thm text,
    reverse_invariant_thm text, doubled_thm text, short_thm text⟩

/-- Imperative scan. Once a mismatch is found, the mutable answer stays false;
continuing the scan rather than returning early has no observable effect. -/
def is_palindrome_imperative (text : String) : Bool := Id.run do
  let xs := text.toList
  let mut answer := true
  for i in List.range xs.length do
    if xs[i]? != xs[xs.length - 1 - i]? then
      answer := false
  return answer

example : is_palindrome_imperative "" = true := by native_decide
example : is_palindrome_imperative "aba" = true := by native_decide
example : is_palindrome_imperative "aaaaa" = true := by native_decide
example : is_palindrome_imperative "zbcd" = false := by native_decide
example : is_palindrome_imperative "xywyx" = true := by native_decide
example : is_palindrome_imperative "xywyz" = false := by native_decide
example : is_palindrome_imperative "xywzx" = false := by native_decide
#eval ["", "aba", "aaaaa", "zbcd", "xywyx", "xywyz", "xywzx"].map
  is_palindrome_imperative

example : is_palindrome_imperative "λ🙂λ" = true := by native_decide
example : is_palindrome_imperative "λ🙂a" = false := by native_decide
-- Exhaustive equivalence test; the universal proof follows below.
example : pbtInputs.all (fun s =>
    is_palindrome s == is_palindrome_imperative s) = true := by native_decide

/-- Loop invariant: the accumulator is its initial value conjoined with every
comparison processed by the fold. -/
theorem foldl_and_all {α : Type} (xs : List α) (p : α → Bool) (b : Bool) :
    xs.foldl (fun acc x => acc && p x) b = (b && xs.all p) := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih => simp [ih, Bool.and_assoc]

/-- The mutable indexed scan computes the conjunction of all mirrored checks. -/
theorem imperative_all_thm (text : String) :
    is_palindrome_imperative text = allMirrors text := by
  unfold is_palindrome_imperative allMirrors
  generalize text.toList = xs
  have step (i : Nat) (b : Bool) :
      (if xs[i]? = xs[xs.length - 1 - i]? then pure (ForInStep.yield b)
        else pure (ForInStep.yield false)) =
      (pure (ForInStep.yield (b && (xs[i]? == xs[xs.length - 1 - i]?))) :
        Id (ForInStep Bool)) := by
    by_cases h : xs[i]? = xs[xs.length - 1 - i]?
    · simp [h]
    · have hb : (xs[i]? == xs[xs.length - 1 - i]?) = false := by
        apply Bool.eq_false_iff.mpr
        intro he
        exact h (beq_iff_eq.mp he)
      simp [h, hb]
  simp
  simp_rw [step]
  rw [List.forIn_pure_yield_eq_foldl]
  simp [foldl_and_all]


/-- The functional and imperative implementations agree on every string. -/
theorem equivalence_thm (text : String) :
    is_palindrome text = is_palindrome_imperative text := by
  rw [imperative_all_thm]
  apply Bool.eq_iff_iff.mpr
  simpa [mirror_prop, allMirrors, List.all_eq_true] using mirror_thm text

end humaneval_48_is_palindrome
end Agent
