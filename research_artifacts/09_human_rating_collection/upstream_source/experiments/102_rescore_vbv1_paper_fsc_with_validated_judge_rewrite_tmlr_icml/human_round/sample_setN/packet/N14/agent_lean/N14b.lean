import Mathlib

/-!
# HumanEval/14: all prefixes

A character-based translation of the Python program. Strings are viewed as lists
of Unicode characters: the result contains every nonempty prefix, in increasing
length, including the whole string. The empty string has no nonempty prefixes.
-/

namespace humaneval_14_all_prefixes

/-- The Python slices `string[:i+1]`, for `i` from zero to the character length. -/
def all_prefixes (s : String) : List String :=
  (List.range s.toList.length).map fun i => String.mk (s.toList.take (i + 1))

example : all_prefixes "" = [] := by native_decide
example : all_prefixes "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by
  native_decide
example : all_prefixes "WWW" = ["W", "WW", "WWW"] := by native_decide
example : all_prefixes "abc" = ["a", "ab", "abc"] := by native_decide
example : all_prefixes "λ🙂界" = ["λ", "λ🙂", "λ🙂界"] := by native_decide
#eval all_prefixes "abc"
#eval all_prefixes ""
#eval all_prefixes "λ🙂界"

/-- Every string is admissible; there are no input restrictions. -/
def Pre (_s : String) : Prop := True

/-- Exactly one output for each character. -/
def length_prop (s : String) : Prop := (all_prefixes s).length = s.toList.length

/-- The output at index i is exactly the first i+1 characters. -/
def index_prop (s : String) : Prop :=
  ∀ i, i < s.toList.length →
    (all_prefixes s)[i]? = some (String.mk (s.toList.take (i + 1)))

/-- Soundness and completeness: precisely the nonempty prefixes occur. -/
def membership_prop (s : String) : Prop :=
  ∀ p : String, p ∈ all_prefixes s ↔ p.toList <+: s.toList ∧ p ≠ ""

/-- Prefixes are ordered strictly by character length, with no duplicates. -/
def ordered_prop (s : String) : Prop :=
  (all_prefixes s).Pairwise (fun p q => p.toList.length < q.toList.length)

/-- A nonempty input is the final prefix, and an empty input has no final prefix. -/
def last_prop (s : String) : Prop :=
  (all_prefixes s).getLast? = if s = "" then none else some s

/-- Only an empty input produces an empty result. -/
def empty_prop (s : String) : Prop := all_prefixes s = [] ↔ s = ""

theorem length_thm (s : String) : length_prop s := by
  simp [length_prop, all_prefixes]

theorem index_thm (s : String) : index_prop s := by
  intro i hi
  unfold all_prefixes
  rw [List.getElem?_map, List.getElem?_range hi]
  rfl

theorem membership_thm (s : String) : membership_prop s := by
  unfold membership_prop all_prefixes
  intro p
  constructor
  · intro hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have hi' : i < s.toList.length := List.mem_range.mp hi
    constructor
    · exact List.take_prefix (i + 1) s.toList
    · intro he
      have hz : (s.toList.take (i + 1)).length = 0 := by
        simpa using congrArg (fun t : String => t.toList.length) he
      simp only [List.length_take] at hz
      omega
  · rintro ⟨hp, hne⟩
    have hpos : 0 < p.toList.length := by
      by_contra hn
      have hz : p.toList = [] := List.length_eq_zero_iff.mp (by omega)
      exact hne (String.toList_inj.mp hz)
    have hle := hp.length_le
    apply List.mem_map.mpr
    refine ⟨p.toList.length - 1, List.mem_range.mpr (by omega), ?_⟩
    have hlen : p.toList.length - 1 + 1 = p.toList.length := by omega
    rw [hlen, ← List.prefix_iff_eq_take.mp hp]
    simp

theorem ordered_thm (s : String) : ordered_prop s := by
  unfold ordered_prop all_prefixes
  rw [List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_range]
  change (s.toList.take (i + 1)).length < (s.toList.take (j + 1)).length
  simp only [List.length_take]
  simp only [List.length_range] at hi hj
  omega

theorem last_thm (s : String) : last_prop s := by
  by_cases hs : s = ""
  · subst s
    simp [last_prop, all_prefixes]
  · have hpos : 0 < s.toList.length := by
      by_contra hn
      have hz : s.toList = [] := List.length_eq_zero_iff.mp (by omega)
      exact hs (String.toList_inj.mp hz)
    have hn : s.toList.length ≠ 0 := by omega
    have hlen : s.toList.length - 1 + 1 = s.toList.length := by omega
    unfold last_prop
    rw [if_neg hs]
    unfold all_prefixes
    rw [List.getLast?_map, List.getLast?_range, if_neg hn]
    change some (String.mk (s.toList.take (s.toList.length - 1 + 1))) = some s
    rw [hlen, List.take_length]
    rfl

theorem empty_thm (s : String) : empty_prop s := by
  unfold empty_prop
  constructor
  · intro h
    have hz : s.toList.length = 0 := by
      have hl := length_thm s
      change (all_prefixes s).length = s.toList.length at hl
      simpa [h] using hl.symm
    exact String.toList_inj.mp (List.length_eq_zero_iff.mp hz)
  · intro h
    subst s
    simp [all_prefixes]

/-- The full specification: count, exact slices, all and only nonempty prefixes,
strict length order, final element, and behavior on the empty string. -/
def Post_prop (s : String) : Prop :=
  length_prop s ∧ index_prop s ∧ membership_prop s ∧ ordered_prop s ∧
    last_prop s ∧ empty_prop s

/-! ## Bounded property-based tests

Exhaustively generate all words of length at most three over a four-character
alphabet (including multi-byte Unicode), then add longer, repeated, whitespace,
and mixed-character inputs. These are tests, not ingredients of the proofs.
-/

private def shortWords : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: (['a', 'W', 'λ', '🙂'].flatMap fun c =>
      (shortWords n).map fun cs => c :: cs)

private def pbtInputs : List String :=
  (shortWords 3).map String.mk ++
  ["asdfgh", "WWW", "abc", "λ🙂界", "éé", "a a", "a\nλ", "\n"] ++
  (List.range 31).map (fun n => String.mk (List.replicate n 'W'))

private def checkLength (s : String) : Bool :=
  (all_prefixes s).length == s.toList.length

private def checkIndex (s : String) : Bool :=
  (List.range s.toList.length).all fun i =>
    (all_prefixes s)[i]? == some (String.mk (s.toList.take (i + 1)))

-- membership_prop: check the equivalence for every pair of sampled strings.
-- Also check soundness for every actual output, even outside the sample set.
private def checkMembership (s : String) : Bool :=
  (all_prefixes s).all (fun p => decide (p.toList <+: s.toList ∧ p ≠ "")) &&
  pbtInputs.all (fun p =>
    decide (p ∈ all_prefixes s ↔ p.toList <+: s.toList ∧ p ≠ ""))

private def checkOrdered (s : String) : Bool :=
  decide ((all_prefixes s).Pairwise (fun p q => p.toList.length < q.toList.length))

private def checkLast (s : String) : Bool :=
  (all_prefixes s).getLast? == (if s = "" then none else some s)

private def checkEmpty (s : String) : Bool :=
  decide (all_prefixes s = [] ↔ s = "")

-- Executable conjunction corresponding to Post_prop.
private def checkPost (s : String) : Bool :=
  checkLength s && checkIndex s && checkMembership s && checkOrdered s &&
    checkLast s && checkEmpty s

-- PBT for length_prop.
example : pbtInputs.all checkLength = true := by native_decide
-- PBT for index_prop (all valid indices of each sampled string).
example : pbtInputs.all checkIndex = true := by native_decide
-- PBT for membership_prop (all pairs from the bounded domain).
example : pbtInputs.all checkMembership = true := by native_decide
-- PBT for ordered_prop.
example : pbtInputs.all checkOrdered = true := by native_decide
-- PBT for last_prop.
example : pbtInputs.all checkLast = true := by native_decide
-- PBT for empty_prop.
example : pbtInputs.all checkEmpty = true := by native_decide
-- PBT for the complete postcondition.
example : pbtInputs.all checkPost = true := by native_decide
#eval pbtInputs.all checkPost

/-- Correctness for the entire admissible input domain. -/
theorem correctness_thm (s : String) : Pre s → Post_prop s := by
  intro _
  exact ⟨length_thm s, index_thm s, membership_thm s, ordered_thm s,
    last_thm s, empty_thm s⟩

/-- Direct translation of the Python append loop using mutable state. -/
def all_prefixes_imperative (s : String) : List String := Id.run do
  let mut result : List String := []
  for i in List.range s.toList.length do
    result := result ++ [String.mk (s.toList.take (i + 1))]
  return result

example : all_prefixes_imperative "" = [] := by native_decide
example : all_prefixes_imperative "asdfgh" =
    ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide
example : all_prefixes_imperative "WWW" = ["W", "WW", "WWW"] := by native_decide
example : all_prefixes_imperative "λ🙂界" = ["λ", "λ🙂", "λ🙂界"] := by native_decide
example : pbtInputs.all (fun s => all_prefixes s == all_prefixes_imperative s) = true := by
  native_decide
#eval all_prefixes_imperative "abc"
#eval all_prefixes_imperative "λ🙂界"

/-- A loop with an arbitrary initial accumulator, used to prove the invariant. -/
private def collect (f : Nat → String) (is : List Nat) (acc : List String) :
    List String := Id.run do
  let mut result := acc
  for i in is do
    result := result ++ [f i]
  return result

/-- After processing a list of indices, append exactly their mapped prefixes. -/
private theorem collect_eq (f : Nat → String) (is : List Nat) (acc : List String) :
    collect f is acc = acc ++ is.map f := by
  induction is generalizing acc with
  | nil => simp [collect]
  | cons i is ih =>
    simpa [collect, List.forIn_cons, List.append_assoc] using ih (acc ++ [f i])

/-- The mutable append loop and the functional map agree on every input. -/
theorem equivalence_thm (s : String) : all_prefixes s = all_prefixes_imperative s := by
  change all_prefixes s =
    collect (fun i => String.mk (s.toList.take (i + 1))) (List.range s.toList.length) []
  rw [collect_eq]
  simp [all_prefixes]

end humaneval_14_all_prefixes
