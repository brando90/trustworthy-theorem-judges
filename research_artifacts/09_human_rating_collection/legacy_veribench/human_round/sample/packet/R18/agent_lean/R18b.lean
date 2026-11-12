import Mathlib

/-!
# HumanEval/14 — `all_prefixes`

Lean 4 formalization of the Python program `humaneval_14_all_prefixes.py`:

```python
def all_prefixes(string: str) -> List[str]:
    """ Return list of all prefixes from shortest to longest of the input string """
    result = []
    for i in range(len(string)):
        result.append(string[:i+1])
    return result
```

The function returns every *non-empty* prefix of the input string, ordered from
shortest to longest.

This file provides:

* a functional implementation `allPrefixes`;
* unit tests mirroring the Python `check` function;
* a pre-condition `Pre`, a collection of property predicates with proofs, and a
  post-condition `Post_prop` together with the correctness theorem
  `Pre s → Post_prop s`;
* an imperative implementation `allPrefixesImp` written with `Id.run do` and a
  mutable accumulator, plus a proof that it agrees with the functional one.
-/

namespace humaneval_14_all_prefixes

/-! ## Functional implementation -/

/-- `allPrefixes s = [s[:1], s[:2], …, s[:s.length]]`, i.e. all non-empty
prefixes of `s` from shortest to longest. -/
def allPrefixes (s : String) : List String :=
  (List.range s.length).map (fun i => s.take (i + 1))

/-! ## Unit tests (mirroring the Python `check`) -/

example : allPrefixes "" = [] := by native_decide

example : allPrefixes "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by
  native_decide

example : allPrefixes "WWW" = ["W", "WW", "WWW"] := by native_decide

example : allPrefixes "abc" = ["a", "ab", "abc"] := by native_decide

#eval allPrefixes "abc"
#eval allPrefixes "asdfgh"

/-! ## Auxiliary lemmas -/

private theorem data_length (s : String) : s.data.length = s.length := rfl

private theorem take_length_of_lt (s : String) {i : Nat} (h : i < s.length) :
    (s.take (i + 1)).length = i + 1 := by
  show (s.take (i + 1)).data.length = i + 1
  rw [String.data_take, List.length_take]
  have hs := data_length s
  omega

private theorem take_length_self (s : String) : s.take s.length = s := by
  apply String.ext
  rw [String.data_take]
  exact List.take_length

private theorem length_pos_of_ne_empty {t : String} (h : t ≠ "") : 0 < t.length := by
  rcases Nat.eq_zero_or_pos t.length with h0 | h0
  · exfalso
    apply h
    apply String.ext
    have : t.data.length = 0 := by rw [data_length]; exact h0
    rw [List.length_eq_zero_iff] at this
    rw [this]
  · exact h0

/-! ## Pre-condition -/

/-- The Python function is total: any string is an acceptable input. -/
def Pre (_s : String) : Prop := True

/-! ## Properties -/

/-- The result has one entry per character of the input (`len(range(len(s)))`). -/
def length_prop (s : String) : Prop :=
  (allPrefixes s).length = s.length

theorem length_thm (s : String) : length_prop s := by
  simp [length_prop, allPrefixes]

/-- The `i`-th entry of the result is `string[:i+1]`. -/
def getElem_prop (s : String) : Prop :=
  ∀ i, i < s.length → (allPrefixes s)[i]? = some (s.take (i + 1))

theorem getElem_thm (s : String) : getElem_prop s := by
  intro i hi
  simp [allPrefixes, List.getElem?_map, List.getElem?_range hi]

/-- The entries grow by exactly one character: the `i`-th one has length `i+1`.
This is the "shortest to longest" part of the specification. -/
def elem_length_prop (s : String) : Prop :=
  ∀ i, i < s.length → ((allPrefixes s)[i]?).map String.length = some (i + 1)

theorem elem_length_thm (s : String) : elem_length_prop s := by
  intro i hi
  rw [getElem_thm s i hi]
  simp [take_length_of_lt s hi]

/-- Every entry of the result is a prefix of the input. -/
def isPrefix_prop (s : String) : Prop :=
  ∀ t ∈ allPrefixes s, t.data <+: s.data

theorem isPrefix_thm (s : String) : isPrefix_prop s := by
  intro t ht
  simp only [allPrefixes, List.mem_map, List.mem_range] at ht
  obtain ⟨i, _, rfl⟩ := ht
  rw [String.data_take]
  exact List.take_prefix _ _

/-- The longest prefix produced is the whole string. -/
def last_prop (s : String) : Prop :=
  0 < s.length → (allPrefixes s).getLast? = some s

theorem last_thm (s : String) : last_prop s := by
  intro hs
  have hlen : (allPrefixes s).length = s.length := length_thm s
  rw [List.getLast?_eq_getElem?, hlen, getElem_thm s (s.length - 1) (by omega)]
  have h1 : s.length - 1 + 1 = s.length := by omega
  rw [h1, take_length_self]

/-- Full characterization of the output: exactly the non-empty prefixes of `s`. -/
def mem_iff_prop (s : String) : Prop :=
  ∀ t : String, t ∈ allPrefixes s ↔ (t.data <+: s.data ∧ t ≠ "")

theorem mem_iff_thm (s : String) : mem_iff_prop s := by
  intro t
  constructor
  · intro ht
    refine ⟨isPrefix_thm s t ht, ?_⟩
    simp only [allPrefixes, List.mem_map, List.mem_range] at ht
    obtain ⟨i, hi, ht⟩ := ht
    intro hempty
    have hlen : (s.take (i + 1)).length = i + 1 := take_length_of_lt s hi
    rw [ht, hempty] at hlen
    simp at hlen
  · rintro ⟨hp, hne⟩
    have hpos : 0 < t.length := length_pos_of_ne_empty hne
    have hle : t.length ≤ s.length := by
      have := hp.length_le
      rw [data_length, data_length] at this
      exact this
    simp only [allPrefixes, List.mem_map, List.mem_range]
    refine ⟨t.length - 1, by omega, ?_⟩
    have h1 : t.length - 1 + 1 = t.length := by omega
    rw [h1]
    apply String.ext
    rw [String.data_take]
    exact (List.prefix_iff_eq_take.mp hp).symm

/-- The empty string yields the empty list (the first Python assertion). -/
def empty_prop : Prop := allPrefixes "" = []

theorem empty_thm : empty_prop := by
  simp [empty_prop, allPrefixes]

/-! ## Post-condition -/

/-- The full post-condition of `all_prefixes`. -/
def Post_prop (s : String) : Prop :=
  length_prop s ∧ getElem_prop s ∧ elem_length_prop s ∧ isPrefix_prop s ∧
    last_prop s ∧ mem_iff_prop s

/-- Correctness: the pre-condition implies the post-condition. -/
theorem correctness_thm (s : String) (_h : Pre s) : Post_prop s :=
  ⟨length_thm s, getElem_thm s, elem_length_thm s, isPrefix_thm s, last_thm s,
    mem_iff_thm s⟩

/-! ## Imperative implementation -/

/-- Literal transcription of the Python loop, using a mutable accumulator. -/
def allPrefixesImp (s : String) : List String := Id.run do
  let mut result : List String := []
  for i in List.range s.length do
    result := result ++ [s.take (i + 1)]
  return result

/-! ### Imperative unit tests -/

example : allPrefixesImp "" = [] := by native_decide

example : allPrefixesImp "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by
  native_decide

example : allPrefixesImp "WWW" = ["W", "WW", "WWW"] := by native_decide

#eval allPrefixesImp "abc"

/-! ## Equivalence of the two implementations -/

private theorem flatten_map_singleton {α β : Type _} (g : α → β) (l : List α) :
    (l.map (fun x => [g x])).flatten = l.map g := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

/-- The functional and imperative implementations agree. -/
theorem allPrefixes_eq_allPrefixesImp (s : String) :
    allPrefixes s = allPrefixesImp s := by
  simp [allPrefixes, allPrefixesImp, Id.run, flatten_map_singleton]
  rfl

end humaneval_14_all_prefixes
