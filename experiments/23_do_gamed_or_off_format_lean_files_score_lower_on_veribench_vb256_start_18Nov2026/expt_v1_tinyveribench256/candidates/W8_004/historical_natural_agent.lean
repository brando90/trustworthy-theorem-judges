import Mathlib
namespace Agent

/-!
# HumanEval 18: how_many_times

Count all occurrences of a substring, including overlapping ones. Strings are
viewed as lists of Unicode characters, so positions and slices are character
based, rather than UTF-8 byte based. There are `n + 1 - m` candidate positions
(natural subtraction), which also gives the Python behavior for an empty
substring and for a substring longer than the original string.
-/

namespace humaneval_18_how_many_times

/-- Python's `range(len(string) - len(substring) + 1)`. -/
def positions (string substring : String) : List Nat :=
  List.range (string.toList.length + 1 - substring.toList.length)

/-- Equality of the character slice at position `i` with the substring. -/
def matchesAt (string substring : String) (i : Nat) : Bool :=
  (string.toList.drop i).take substring.toList.length == substring.toList

/-- Count all matching start positions; advancing by one allows overlaps. -/
def how_many_times (string substring : String) : Nat :=
  ((positions string substring).filter (matchesAt string substring)).length

example : how_many_times "" "a" = 0 := by native_decide
example : how_many_times "" "x" = 0 := by native_decide
example : how_many_times "xyxyxyx" "x" = 4 := by native_decide
example : how_many_times "cacacacac" "cac" = 4 := by native_decide
example : how_many_times "john doe" "john" = 1 := by native_decide
example : how_many_times "aaa" "a" = 3 := by native_decide
example : how_many_times "aaaa" "aa" = 3 := by native_decide
example : how_many_times "" "" = 1 := by native_decide
example : how_many_times "abc" "" = 4 := by native_decide
example : how_many_times "a" "abcd" = 0 := by native_decide
example : how_many_times "é🙂é🙂é" "é🙂é" = 2 := by native_decide
#eval how_many_times "cacacacac" "cac"
#eval how_many_times "aaaa" "aa"
#eval how_many_times "abc" ""

/-- Every pair of strings is admissible, including empty strings. -/
def Pre (_string _substring : String) : Prop := True

/-- A substring occurrence is a complete matching slice within the string. -/
def OccursAt (string substring : String) (i : Nat) : Prop :=
  i + substring.toList.length ≤ string.toList.length ∧
    (string.toList.drop i).take substring.toList.length = substring.toList

instance (string substring : String) (i : Nat) :
    Decidable (OccursAt string substring i) := by
  unfold OccursAt
  infer_instance

/-- Independent specification: all character boundaries, retaining exactly
those at which a complete copy of the substring occurs. -/
def occurrencePositions (string substring : String) : Finset Nat :=
  (Finset.range (string.toList.length + 1)).filter (OccursAt string substring)

/-- Every valid matching position is counted exactly once. -/
def exact_count_prop (string substring : String) (result : Nat) : Prop :=
  result = (occurrencePositions string substring).card

lemma mem_matching_positions (string substring : String) (i : Nat) :
    i ∈ (positions string substring).filter (matchesAt string substring) ↔
      OccursAt string substring i := by
  simp only [List.mem_filter, positions, List.mem_range, matchesAt, beq_iff_eq,
    OccursAt]
  constructor
  · rintro ⟨hi, hm⟩
    exact ⟨by omega, hm⟩
  · rintro ⟨hi, hm⟩
    exact ⟨by omega, hm⟩

theorem exact_count_thm (string substring : String) :
    exact_count_prop string substring (how_many_times string substring) := by
  unfold exact_count_prop how_many_times
  have hn : ((positions string substring).filter (matchesAt string substring)).Nodup :=
    List.Nodup.filter _ (by unfold positions; exact List.nodup_range)
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext i
  simp only [List.mem_toFinset, mem_matching_positions, occurrencePositions,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact ⟨by have := h.1; omega, h⟩
  · exact And.right

/-- No more occurrences than candidate starting positions. -/
def bound_prop (string substring : String) (result : Nat) : Prop :=
  result ≤ string.toList.length + 1 - substring.toList.length

theorem bound_thm (string substring : String) :
    bound_prop string substring (how_many_times string substring) := by
  simpa [bound_prop, how_many_times, positions] using
    List.length_filter_le (matchesAt string substring) (positions string substring)

/-- A positive result is equivalent to the existence of a complete occurrence. -/
def positive_prop (string substring : String) (result : Nat) : Prop :=
  0 < result ↔ ∃ i : Nat, OccursAt string substring i

theorem positive_thm (string substring : String) :
    positive_prop string substring (how_many_times string substring) := by
  unfold positive_prop
  rw [show how_many_times string substring =
    (occurrencePositions string substring).card from exact_count_thm string substring]
  rw [Finset.card_pos]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := hi.1
      omega), hi⟩⟩

/-- Zero means that no character position contains the whole substring. -/
def zero_prop (string substring : String) (result : Nat) : Prop :=
  result = 0 ↔ ∀ i : Nat, ¬ OccursAt string substring i

theorem zero_thm (string substring : String) :
    zero_prop string substring (how_many_times string substring) := by
  have h := positive_thm string substring
  unfold positive_prop at h
  unfold zero_prop
  simpa only [not_lt, Nat.le_zero, not_exists] using not_congr h

/-- Python finds the empty substring at every boundary, including the last. -/
def empty_substring_prop (string substring : String) (result : Nat) : Prop :=
  substring = "" → result = string.toList.length + 1

theorem empty_substring_thm (string substring : String) :
    empty_substring_prop string substring (how_many_times string substring) := by
  intro h
  subst substring
  unfold how_many_times
  rw [List.filter_eq_self.mpr (by intro i hi; simp [matchesAt])]
  simp [positions]

/-- Natural subtraction correctly makes Python's negative/zero range empty. -/
def too_long_prop (string substring : String) (result : Nat) : Prop :=
  string.toList.length < substring.toList.length → result = 0

theorem too_long_thm (string substring : String) :
    too_long_prop string substring (how_many_times string substring) := by
  intro h
  have hz : string.toList.length + 1 - substring.toList.length = 0 := by omega
  unfold how_many_times positions
  rw [hz]
  rfl

/-- The empty input has one empty-substring occurrence and no nonempty ones. -/
def empty_string_prop (string substring : String) (result : Nat) : Prop :=
  string = "" → result = if substring = "" then 1 else 0

theorem empty_string_thm (string substring : String) :
    empty_string_prop string substring (how_many_times string substring) := by
  intro h
  subst string
  by_cases ht : substring = ""
  · subst substring
    simp [how_many_times, positions, matchesAt]
  · rw [if_neg ht]
    apply too_long_thm
    have hn : substring.toList ≠ [] := by
      intro hn
      apply ht
      exact String.toList_inj.mp (by simpa only [String.toList_empty] using hn)
    simpa using List.length_pos_iff.mpr hn

/-- A string, empty or not, occurs in itself exactly once. -/
def self_prop (string substring : String) (result : Nat) : Prop :=
  substring = string → result = 1

theorem self_thm (string substring : String) :
    self_prop string substring (how_many_times string substring) := by
  intro h
  subst substring
  simp [how_many_times, positions, matchesAt, List.range_succ]

/-- The full contract, with no restriction on either input string. -/
def Post_prop (string substring : String) (result : Nat) : Prop :=
  exact_count_prop string substring result ∧
  bound_prop string substring result ∧
  positive_prop string substring result ∧
  zero_prop string substring result ∧
  empty_substring_prop string substring result ∧
  too_long_prop string substring result ∧
  empty_string_prop string substring result ∧
  self_prop string substring result

/-! ## Bounded property-based tests

The sample generator enumerates *all* strings of length at most three over a
four-character alphabet, and adds longer public and overlapping examples.
Every test below checks every pair of sample strings, including empty strings.
The positive and zero checks use the finite range of character boundaries:
`OccursAt s t i` implies `i ≤ s.toList.length`, so no occurrence is omitted.
These executable tests supplement, rather than replace, the universal proofs.
-/

private def smallWords : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: ['a', 'b', 'é', '🙂'].flatMap
      (fun c => (smallWords n).map (fun w => c :: w))

private def sampleStrings : List String :=
  (smallWords 3).map String.mk ++
    ["x", "xyxyxyx", "cacacacac", "cac", "john doe", "john",
      "aaaa", "aa", "abc", "abcd", "é🙂é🙂é", "é🙂é"]

private def testPairs (check : String → String → Bool) : Bool :=
  sampleStrings.all (fun s => sampleStrings.all (fun t => check s t))

private def exactCountCheck (s t : String) (r : Nat) : Bool :=
  r == (occurrencePositions s t).card

private def boundCheck (s t : String) (r : Nat) : Bool :=
  decide (r ≤ s.toList.length + 1 - t.toList.length)

private def positiveCheck (s t : String) (r : Nat) : Bool :=
  decide (0 < r) ==
    (List.range (s.toList.length + 1)).any (fun i => decide (OccursAt s t i))

private def zeroCheck (s t : String) (r : Nat) : Bool :=
  (r == 0) ==
    (List.range (s.toList.length + 1)).all (fun i => !decide (OccursAt s t i))

private def emptySubstringCheck (s t : String) (r : Nat) : Bool :=
  decide (t = "" → r = s.toList.length + 1)

private def tooLongCheck (s t : String) (r : Nat) : Bool :=
  decide (s.toList.length < t.toList.length → r = 0)

private def emptyStringCheck (s t : String) (r : Nat) : Bool :=
  decide (s = "" → r = if t = "" then 1 else 0)

private def selfCheck (s t : String) (r : Nat) : Bool :=
  decide (t = s → r = 1)

private def postCheck (s t : String) (r : Nat) : Bool :=
  exactCountCheck s t r && boundCheck s t r &&
  positiveCheck s t r && zeroCheck s t r &&
  emptySubstringCheck s t r && tooLongCheck s t r &&
  emptyStringCheck s t r && selfCheck s t r

-- PBT for exact_count_prop.
example : testPairs (fun s t => exactCountCheck s t (how_many_times s t)) = true := by
  native_decide
-- PBT for bound_prop.
example : testPairs (fun s t => boundCheck s t (how_many_times s t)) = true := by
  native_decide
-- PBT for positive_prop.
example : testPairs (fun s t => positiveCheck s t (how_many_times s t)) = true := by
  native_decide
-- PBT for zero_prop.
example : testPairs (fun s t => zeroCheck s t (how_many_times s t)) = true := by
  native_decide
-- PBT for empty_substring_prop.
example : testPairs (fun s t => emptySubstringCheck s t (how_many_times s t)) = true := by
  native_decide
-- PBT for too_long_prop.
example : testPairs (fun s t => tooLongCheck s t (how_many_times s t)) = true := by
  native_decide
-- PBT for empty_string_prop.
example : testPairs (fun s t => emptyStringCheck s t (how_many_times s t)) = true := by
  native_decide
-- PBT for self_prop.
example : testPairs (fun s t => selfCheck s t (how_many_times s t)) = true := by
  native_decide
-- PBT for the entire Post_prop conjunction.
example : testPairs (fun s t => postCheck s t (how_many_times s t)) = true := by
  native_decide
#eval (sampleStrings.length, testPairs (fun s t => postCheck s t (how_many_times s t)))


theorem correctness (string substring : String) :
    Pre string substring → Post_prop string substring (how_many_times string substring) := by
  intro _
  exact ⟨exact_count_thm string substring, bound_thm string substring,
    positive_thm string substring, zero_thm string substring,
    empty_substring_thm string substring, too_long_thm string substring,
    empty_string_thm string substring, self_thm string substring⟩

/-- The original loop: mutable counter, one step per possible start position. -/
def how_many_times_imperative (string substring : String) : Nat := Id.run do
  let mut times := 0
  for i in positions string substring do
    if matchesAt string substring i then
      times := times + 1
  return times

example : how_many_times_imperative "" "x" = 0 := by native_decide
example : how_many_times_imperative "xyxyxyx" "x" = 4 := by native_decide
example : how_many_times_imperative "cacacacac" "cac" = 4 := by native_decide
example : how_many_times_imperative "john doe" "john" = 1 := by native_decide
example : how_many_times_imperative "abc" "" = 4 := by native_decide
#eval how_many_times_imperative "aaaa" "aa"

example : how_many_times_imperative "" "" = 1 := by native_decide
example : how_many_times_imperative "a" "abcd" = 0 := by native_decide
example : how_many_times_imperative "é🙂é🙂é" "é🙂é" = 2 := by native_decide
example : testPairs (fun s t => how_many_times s t == how_many_times_imperative s t) = true := by
  native_decide

/-- Generalized loop used to express and prove the accumulator invariant. -/
private def countFrom (p : Nat → Bool) (xs : List Nat) (initial : Nat) : Nat := Id.run do
  let mut times := initial
  for i in xs do
    if p i then
      times := times + 1
  return times

/-- Loop invariant: the final count is the initial count plus all remaining hits. -/
private theorem countFrom_eq (p : Nat → Bool) (xs : List Nat) (initial : Nat) :
    countFrom p xs initial = initial + (xs.filter p).length := by
  induction xs generalizing initial with
  | nil => simp [countFrom]
  | cons i xs ih =>
    simp only [countFrom, List.forIn_cons, List.filter_cons]
    split <;> simp_all [countFrom, Nat.add_comm, Nat.add_left_comm]

/-- The functional and mutable implementations agree for every input pair. -/
theorem functional_eq_imperative (string substring : String) :
    how_many_times string substring = how_many_times_imperative string substring := by
  change how_many_times string substring =
    countFrom (matchesAt string substring) (positions string substring) 0
  rw [countFrom_eq]
  simp [how_many_times]

end humaneval_18_how_many_times
end Agent
