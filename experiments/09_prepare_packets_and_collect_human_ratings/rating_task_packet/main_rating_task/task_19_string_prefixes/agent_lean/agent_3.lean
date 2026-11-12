import Mathlib

/-!
# HumanEval 14: all prefixes

`all_prefixes` returns every nonempty prefix of a string, from shortest to longest.
Lengths and slices use Unicode characters (`Char`), rather than UTF-8 byte offsets.
The specification proves the count, exact indexed contents, lengths, membership,
strict order, and final element. Exhaustive bounded property tests include Unicode.
A mutable `Id.run` loop mirrors the Python program and is proved equivalent.
-/

namespace humaneval_14_all_prefixes

/-- The first `n` Unicode characters, with the usual truncation at the end. -/
def takeChars (s : String) (n : Nat) : String :=
  String.mk (s.toList.take n)

/-- Functional translation of `string[:i+1]` for `i` in `range(len(string))`. -/
def all_prefixes (s : String) : List String :=
  (List.range s.length).map (fun i => takeChars s (i + 1))

example : all_prefixes "" = [] := by native_decide
example : all_prefixes "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by
  native_decide
example : all_prefixes "WWW" = ["W", "WW", "WWW"] := by native_decide
example : all_prefixes "abc" = ["a", "ab", "abc"] := by native_decide
example : all_prefixes "é🦀a" = ["é", "é🦀", "é🦀a"] := by native_decide
#eval all_prefixes "abc"
#eval all_prefixes "é🦀a"

/-- Every string is admissible, including the empty string. -/
def Pre (_s : String) : Prop := True

/-- There is one output for every character of the input. -/
def count_prop (s : String) (result : List String) : Prop :=
  result.length = s.length

theorem count_thm (s : String) : count_prop s (all_prefixes s) := by
  simp [count_prop, all_prefixes]

/-- Position `i` contains exactly the first `i + 1` characters. -/
def indexed_prop (s : String) (result : List String) : Prop :=
  ∀ i : Nat, i < s.length → result[i]? = some (takeChars s (i + 1))

theorem indexed_thm (s : String) : indexed_prop s (all_prefixes s) := by
  intro i hi
  simp [all_prefixes, List.getElem?_range hi]

private theorem prefix_length (s : String) (n : Nat) (hn : n ≤ s.length) :
    (takeChars s n).length = n := by
  change (s.toList.take n).length = n
  rw [List.length_take]
  exact Nat.min_eq_left hn

private theorem prefix_full (s : String) : takeChars s s.length = s := by
  cases s
  simp [takeChars, String.toList, String.length]

/-- Output lengths are precisely `1, 2, ..., s.length`. -/
def lengths_prop (s : String) (result : List String) : Prop :=
  result.map String.length = (List.range s.length).map (fun i => i + 1)

theorem lengths_thm (s : String) : lengths_prop s (all_prefixes s) := by
  unfold lengths_prop all_prefixes
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  exact prefix_length s (i + 1) (by have := List.mem_range.mp hi; omega)

/-- The results are exactly the nonempty character-list prefixes of the input. -/
def membership_prop (s : String) (result : List String) : Prop :=
  ∀ p : String, p ∈ result ↔ 0 < p.length ∧ p.toList <+: s.toList

theorem membership_thm (s : String) : membership_prop s (all_prefixes s) := by
  intro p
  constructor
  · intro hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have hi' : i + 1 ≤ s.length := by have := List.mem_range.mp hi; omega
    constructor
    · rw [prefix_length s (i + 1) hi']
      omega
    · exact List.take_prefix (i + 1) s.toList
  · rintro ⟨hp, hprefix⟩
    have hle : p.length ≤ s.length := hprefix.length_le
    apply List.mem_map.mpr
    refine ⟨p.length - 1, List.mem_range.mpr (by omega), ?_⟩
    have hindex : p.length - 1 + 1 = p.length := by omega
    rw [hindex]
    apply String.toList_inj.mp
    exact (List.prefix_iff_eq_take.mp hprefix).symm

/-- Earlier results are strictly shorter prefixes of later results. -/
def ordered_prop (_s : String) (result : List String) : Prop :=
  result.Pairwise (fun p q => p.length < q.length ∧ p.toList <+: q.toList)

theorem ordered_thm (s : String) : ordered_prop s (all_prefixes s) := by
  unfold ordered_prop all_prefixes
  rw [List.pairwise_map]
  apply List.pairwise_lt_range.imp_of_mem
  intro i j hi hj hij
  have hi' : i + 1 ≤ s.length := by have := List.mem_range.mp hi; omega
  have hj' : j + 1 ≤ s.length := by have := List.mem_range.mp hj; omega
  constructor
  · rw [prefix_length s (i + 1) hi', prefix_length s (j + 1) hj']
    omega
  · exact List.take_prefix_take_left (by omega)

/-- For nonempty inputs the last result is the entire input. -/
def last_prop (s : String) (result : List String) : Prop :=
  0 < s.length → result.getLast? = some s

theorem last_thm (s : String) : last_prop s (all_prefixes s) := by
  intro hs
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  rw [all_prefixes, hn, List.range_succ, List.map_append, List.map_singleton,
    List.getLast?_concat]
  congr 1
  rw [Nat.succ_eq_add_one] at hn
  rw [← hn]
  exact prefix_full s

/-- Complete specification, with no restriction on the input. -/
def Post_prop (s : String) (result : List String) : Prop :=
  count_prop s result ∧ indexed_prop s result ∧ lengths_prop s result ∧
    membership_prop s result ∧ ordered_prop s result ∧ last_prop s result

/-! Bounded property-based tests. The corpus contains all 341 strings of length
at most four over a four-character alphabet, including two multibyte characters.
Each property has its own executable check. Membership quantification is bounded
in tests only; the theorem above quantifies over every possible string. -/

private def wordsOfLength : Nat → List String
  | 0 => [""]
  | n + 1 => ['a', 'W', 'é', '🦀'].flatMap (fun c =>
      (wordsOfLength n).map (fun s => String.singleton c ++ s))

private def testStrings : List String :=
  (List.range 5).flatMap wordsOfLength

private def countCheck (s : String) (result : List String) : Bool :=
  result.length == s.length

private def indexedCheck (s : String) (result : List String) : Bool :=
  (List.range s.length).all (fun i => result[i]? == some (takeChars s (i + 1)))

private def lengthsCheck (s : String) (result : List String) : Bool :=
  result.map String.length == (List.range s.length).map (fun i => i + 1)

private def membershipCheck (s : String) (result : List String) : Bool :=
  (testStrings ++ ["z", "az", "aaaaa", s ++ "a"]).all (fun p =>
    decide (p ∈ result) == decide (0 < p.length ∧ p.toList <+: s.toList))

private def orderedCheck (result : List String) : Bool :=
  decide (result.Pairwise (fun p q => p.length < q.length ∧ p.toList <+: q.toList))

private def lastCheck (s : String) (result : List String) : Bool :=
  s.length == 0 || result.getLast? == some s

private def postCheck (s : String) (result : List String) : Bool :=
  countCheck s result && indexedCheck s result && lengthsCheck s result &&
    membershipCheck s result && orderedCheck result && lastCheck s result

-- PBT for count_prop.
example : testStrings.all (fun s => countCheck s (all_prefixes s)) = true := by
  native_decide

-- PBT for indexed_prop.
example : testStrings.all (fun s => indexedCheck s (all_prefixes s)) = true := by
  native_decide

-- PBT for lengths_prop.
example : testStrings.all (fun s => lengthsCheck s (all_prefixes s)) = true := by
  native_decide

-- PBT for membership_prop, checking both present and absent candidate strings.
example : testStrings.all (fun s => membershipCheck s (all_prefixes s)) = true := by
  native_decide

-- PBT for ordered_prop.
example : testStrings.all (fun s => orderedCheck (all_prefixes s)) = true := by
  native_decide

-- PBT for last_prop, including empty inputs via the implication's Boolean form.
example : testStrings.all (fun s => lastCheck s (all_prefixes s)) = true := by
  native_decide

-- PBT for the conjunction Post_prop.
example : testStrings.all (fun s => postCheck s (all_prefixes s)) = true := by
  native_decide

#eval (testStrings.length, testStrings.all (fun s => postCheck s (all_prefixes s)))

/-- The functional implementation satisfies the complete specification. -/
theorem correctness (s : String) : Pre s → Post_prop s (all_prefixes s) := by
  intro _
  exact ⟨count_thm s, indexed_thm s, lengths_thm s, membership_thm s,
    ordered_thm s, last_thm s⟩

/-- Direct translation of the Python loop and its mutable result list. -/
def all_prefixes_imperative (s : String) : List String := Id.run do
  let mut result : List String := []
  for i in List.range s.length do
    result := result ++ [takeChars s (i + 1)]
  return result

example : all_prefixes_imperative "" = [] := by native_decide
example : all_prefixes_imperative "asdfgh" =
    ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide
example : all_prefixes_imperative "WWW" = ["W", "WW", "WWW"] := by native_decide
example : all_prefixes_imperative "é🦀a" = ["é", "é🦀", "é🦀a"] := by native_decide
#eval all_prefixes_imperative "abc"

-- Bounded PBT of the imperative specification and functional equivalence.
example : testStrings.all (fun s => postCheck s (all_prefixes_imperative s)) = true := by
  native_decide
example : testStrings.all (fun s => all_prefixes s == all_prefixes_imperative s) = true := by
  native_decide

/-- Appending each prefix in the loop is equivalent to mapping the index range. -/
theorem functional_eq_imperative (s : String) :
    all_prefixes s = all_prefixes_imperative s := by
  simp [all_prefixes_imperative, all_prefixes, List.foldl_append_eq_append,
    ← List.flatMap_def, ← List.map_eq_flatMap]

end humaneval_14_all_prefixes
