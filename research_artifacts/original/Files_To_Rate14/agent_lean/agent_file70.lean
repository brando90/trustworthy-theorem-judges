import Mathlib

/-!
# HumanEval/14: `all_prefixes`

Lean 4 translation of the Python program `humaneval_14_all_prefixes.py`.

```python
def all_prefixes(string: str) -> List[str]:
    result = []
    for i in range(len(string)):
        result.append(string[:i+1])
    return result
```

`all_prefixes s` returns the list of all non-empty prefixes of `s`, ordered from
shortest to longest: `[s[:1], s[:2], ..., s[:len(s)]]`.  For the empty string the
result is the empty list.

The file contains a functional implementation, unit tests, a pre-condition,
several proved properties, a post-condition, property-based tests, a correctness
theorem, an imperative implementation (`Id.run do` with mutable state) and a
proved equivalence theorem between the two implementations.
-/

namespace humaneval_14_all_prefixes

/-! ## Functional implementation -/

/-- Python `string[:i+1]` is `s.take (i + 1)`; `range(len(string))` is
`List.range s.length`. -/
def all_prefixes (s : String) : List String :=
  (List.range s.length).map (fun i => s.take (i + 1))

/-! ## Unit tests (from the Python docstring and `check`) -/

example : all_prefixes "abc" = ["a", "ab", "abc"] := by native_decide
example : all_prefixes "" = [] := by native_decide
example : all_prefixes "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by
  native_decide
example : all_prefixes "WWW" = ["W", "WW", "WWW"] := by native_decide

#eval all_prefixes "abc"
#eval all_prefixes ""
#eval all_prefixes "asdfgh"
#eval all_prefixes "WWW"

/-! ## Pre-condition -/

/-- Every string is an admissible input. -/
def Pre (_s : String) : Prop := True

/-! ## Helper lemmas about `String.take` -/

/-- `String.length` is the length of the underlying character list. -/
theorem length_eq_data_length (s : String) : s.length = s.data.length := rfl

/-- Length of a prefix taken with `String.take`. -/
theorem length_take (s : String) (n : Nat) : (s.take n).length = min n s.length := by
  rw [length_eq_data_length, length_eq_data_length, String.data_take, List.length_take]

/-- Taking all characters returns the string itself. -/
theorem take_length_self (s : String) : s.take s.length = s := by
  apply String.ext
  rw [String.data_take, length_eq_data_length]
  exact List.take_of_length_le (le_refl _)

/-! ## Properties -/

/-- There is exactly one prefix per character of the input. -/
def length_prop (s : String) : Prop :=
  (all_prefixes s).length = s.length

theorem length_thm (s : String) : length_prop s := by
  unfold length_prop all_prefixes
  simp

/-- The `i`-th element of the result is `string[:i+1]`. -/
def nth_prop (s : String) : Prop :=
  ∀ i, i < s.length → (all_prefixes s)[i]? = some (s.take (i + 1))

theorem nth_thm (s : String) : nth_prop s := by
  intro i hi
  unfold all_prefixes
  simp [List.getElem?_map, List.getElem?_range hi]

/-- Every element of the result is a prefix of the input string. -/
def isPrefix_prop (s : String) : Prop :=
  ∀ p ∈ all_prefixes s, p.data <+: s.data

theorem isPrefix_thm (s : String) : isPrefix_prop s := by
  intro p hp
  unfold all_prefixes at hp
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨i, _, rfl⟩ := hp
  rw [String.data_take]
  exact List.take_prefix _ _

/-- The `i`-th element has length `i + 1`; in particular every element is
non-empty and lengths increase from `1` to `s.length`. -/
def lengths_prop (s : String) : Prop :=
  ∀ i (h : i < (all_prefixes s).length), ((all_prefixes s)[i]'h).length = i + 1

theorem lengths_thm (s : String) : lengths_prop s := by
  intro i h
  have hi : i < s.length := by
    have hl := length_thm s
    unfold length_prop at hl
    omega
  simp only [all_prefixes, List.getElem_map, List.getElem_range]
  rw [length_take]
  omega

/-- For a non-empty input the last (longest) prefix is the whole string. -/
def last_prop (s : String) : Prop :=
  0 < s.length → (all_prefixes s).getLast? = some s

theorem last_thm (s : String) : last_prop s := by
  intro hs
  have hl := length_thm s
  unfold length_prop at hl
  have hn := nth_thm s
  unfold nth_prop at hn
  rw [List.getLast?_eq_getElem?, hl, hn (s.length - 1) (by omega)]
  have h1 : s.length - 1 + 1 = s.length := by omega
  rw [h1, take_length_self]

/-- The result is ordered from shortest to longest: each element is a prefix of
the next one and is exactly one character shorter. -/
def chain_prop (s : String) : Prop :=
  List.Chain' (fun a b : String => a.data <+: b.data ∧ a.length + 1 = b.length)
    (all_prefixes s)

theorem chain_thm (s : String) : chain_prop s := by
  unfold chain_prop all_prefixes
  rw [List.chain'_map]
  cases h : s.length with
  | zero => simp
  | succ n =>
    rw [List.chain'_range_succ]
    intro m hm
    constructor
    · rw [String.data_take, String.data_take]
      have : s.data.take (m + 1) = (s.data.take (m + 1 + 1)).take (m + 1) := by
        rw [List.take_take]
        congr 1
        omega
      rw [this]
      exact List.take_prefix _ _
    · rw [length_take, length_take, h]
      omega

/-- `all_prefixes s` is exactly the list `[s[:1], ..., s[:len(s)]]`. -/
def spec_prop (s : String) : Prop :=
  all_prefixes s = (List.range s.length).map (fun i => s.take (i + 1))

theorem spec_thm (s : String) : spec_prop s := rfl

/-! ## Post-condition -/

/-- Post-condition: conjunction of all the properties above. -/
def Post_prop (s : String) : Prop :=
  length_prop s ∧ nth_prop s ∧ isPrefix_prop s ∧ lengths_prop s ∧ last_prop s ∧
    chain_prop s ∧ spec_prop s

/-! ## Property-based tests

Each `_prop` has an executable Boolean form checked below, both randomly
(Plausible) and exhaustively on a fixed list of small inputs. -/

/-- Executable form of `length_prop`. -/
def length_check (s : String) : Bool :=
  (all_prefixes s).length == s.length

/-- Executable form of `nth_prop`. -/
def nth_check (s : String) : Bool :=
  (List.range s.length).all (fun i => (all_prefixes s)[i]? == some (s.take (i + 1)))

/-- Executable form of `isPrefix_prop`. -/
def isPrefix_check (s : String) : Bool :=
  (all_prefixes s).all (fun p => p.isPrefixOf s)

/-- Executable form of `lengths_prop`. -/
def lengths_check (s : String) : Bool :=
  (all_prefixes s).map String.length == (List.range s.length).map (· + 1)

/-- Executable form of `last_prop`. -/
def last_check (s : String) : Bool :=
  s.length == 0 || (all_prefixes s).getLast? == some s

/-- Executable form of `chain_prop` (adjacent pairs). -/
def chain_check (s : String) : Bool :=
  ((all_prefixes s).zip (all_prefixes s).tail).all
    (fun (a, b) => a.isPrefixOf b && a.length + 1 == b.length)

/-- Executable form of `spec_prop`. -/
def spec_check (s : String) : Bool :=
  all_prefixes s == (List.range s.length).map (fun i => s.take (i + 1))

/-- Executable form of `Post_prop`. -/
def post_check (s : String) : Bool :=
  length_check s && nth_check s && isPrefix_check s && lengths_check s &&
    last_check s && chain_check s && spec_check s

-- Randomized PBTs (Plausible samples `String`s).
#eval Plausible.Testable.check (∀ s : String, length_check s = true)
#eval Plausible.Testable.check (∀ s : String, nth_check s = true)
#eval Plausible.Testable.check (∀ s : String, isPrefix_check s = true)
#eval Plausible.Testable.check (∀ s : String, lengths_check s = true)
-- `last_prop` has a precondition (`0 < s.length`); `last_check` tests it unconditionally and
-- the bounded tests below cover it exhaustively on the corpus.
#eval Plausible.Testable.check (∀ s : String, last_check s = true)
#eval Plausible.Testable.check (∀ s : String, chain_check s = true)
#eval Plausible.Testable.check (∀ s : String, spec_check s = true)
#eval Plausible.Testable.check (∀ s : String, post_check s = true)
-- Directly on the `Prop` forms that are decidable.
#eval Plausible.Testable.check (∀ s : String, (all_prefixes s).length = s.length)
#eval Plausible.Testable.check
  (∀ s : String, (all_prefixes s).all (fun p => decide (p.data <+: s.data)) = true)
#eval Plausible.Testable.check
  (∀ s : String, List.Chain' (fun a b : String => a.data <+: b.data ∧ a.length + 1 = b.length)
    (all_prefixes s))

/-- Fixed corpus of small inputs for exhaustive bounded PBTs. -/
def testStrings : List String :=
  ["", "a", "ab", "abc", "asdfgh", "WWW", "hello world", "aaaa", "xyz123", "αβγ",
   "  ", "a b c", "Lean4", "prefix"]

example : testStrings.all length_check = true := by native_decide
example : testStrings.all nth_check = true := by native_decide
example : testStrings.all isPrefix_check = true := by native_decide
example : testStrings.all lengths_check = true := by native_decide
example : testStrings.all last_check = true := by native_decide
example : testStrings.all chain_check = true := by native_decide
example : testStrings.all spec_check = true := by native_decide
example : testStrings.all post_check = true := by native_decide
-- Bounded PBT over all strings of the form `"ab..."` of length `< 40`.
example : (List.range 40).all (fun n => post_check (String.mk (List.replicate n 'a'))) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem correctness (s : String) (_h : Pre s) : Post_prop s :=
  ⟨length_thm s, nth_thm s, isPrefix_thm s, lengths_thm s, last_thm s, chain_thm s, spec_thm s⟩

/-! ## Imperative implementation -/

/-- Direct transcription of the Python loop: a mutable `result` that is appended
to for every `i in range(len(string))`. -/
def all_prefixes_imp (s : String) : List String := Id.run do
  let mut result : Array String := #[]
  for i in List.range s.length do
    result := result.push (s.take (i + 1))
  return result.toList

/-! ## Imperative tests -/

example : all_prefixes_imp "abc" = ["a", "ab", "abc"] := by native_decide
example : all_prefixes_imp "" = [] := by native_decide
example : all_prefixes_imp "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by
  native_decide
example : all_prefixes_imp "WWW" = ["W", "WW", "WWW"] := by native_decide

#eval all_prefixes_imp "abc"
#eval all_prefixes_imp "asdfgh"

-- PBT: the two implementations agree on random inputs.
#eval Plausible.Testable.check (∀ s : String, all_prefixes_imp s = all_prefixes s)
example : testStrings.all (fun s => all_prefixes_imp s == all_prefixes s) = true := by
  native_decide

/-! ## Equivalence theorem -/

theorem imp_eq_func (s : String) : all_prefixes_imp s = all_prefixes s := by
  unfold all_prefixes_imp all_prefixes
  simp

/-- The imperative implementation satisfies the post-condition as well. -/
theorem imp_correctness (s : String) (_h : Pre s) :
    (all_prefixes_imp s).length = s.length ∧
      (0 < s.length → (all_prefixes_imp s).getLast? = some s) := by
  rw [imp_eq_func]
  exact ⟨length_thm s, last_thm s⟩

end humaneval_14_all_prefixes
