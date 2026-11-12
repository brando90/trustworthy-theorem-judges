import Mathlib

/-!
# HumanEval/14: `all_prefixes`

Python source (`humaneval_14_all_prefixes.py`):

```python
from typing import List


def all_prefixes(string: str) -> List[str]:
    """ Return list of all prefixes from shortest to longest of the input string
    >>> all_prefixes('abc')
    ['a', 'ab', 'abc']
    """
    result = []

    for i in range(len(string)):
        result.append(string[:i+1])
    return result
```

## Modelling

* Python 3 `str` is a finite sequence of Unicode scalar values. Lean's `String` is a wrapper
  around `List Char`, i.e. the same mathematical object, so `string` is modelled by `s : String`.
* `len(string)` is `s.length` (a count of characters, not of bytes).
* `string[:k]` is the prefix made of the first `k` characters, modelled by `s.take k`
  (`String.take_eq` gives `s.take k = String.mk (List.take k s.data)`).
* `range(len(string))` is `List.range s.length`, `result.append(x)` is `Array.push`, and the
  returned `List[str]` is a `List String`.
* `all_prefixes` is total (`all_prefixes("") == []` is required by the tests), so `Pre s = True`.

This file contains the functional implementation and its unit tests, the pre-condition, the
properties of the Python specification together with their proofs, the post-condition,
property-based tests, the correctness theorem `Pre -> Post`, an imperative implementation with
mutable state and its tests, and the functional/imperative equivalence theorem.
-/

namespace humaneval_14_all_prefixes

/-! ## 1. Functional implementation -/

/-- `allPrefixes s` is the list of all prefixes of `s`, from shortest to longest,
that is `[s[:1], s[:2], ..., s[:len s]]`.

Direct translation of the Python loop

```python
result = []
for i in range(len(string)):
    result.append(string[:i+1])
return result
```
-/
def allPrefixes (s : String) : List String :=
  (List.range s.length).map (fun i => s.take (i + 1))

/-! ## 2. Unit tests (the assertions of the Python `check` function) -/

example : allPrefixes "" = [] := by native_decide

example : allPrefixes "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide

example : allPrefixes "WWW" = ["W", "WW", "WWW"] := by native_decide

/-- The example from the Python docstring. -/
example : allPrefixes "abc" = ["a", "ab", "abc"] := by native_decide

#eval allPrefixes "abc"
#eval allPrefixes ""
#eval allPrefixes "WWW"

/-! ## 3. Pre-condition -/

/-- The Python function is total: every string is an admissible input.
In particular the empty string is admissible and yields `[]`. -/
def Pre (_s : String) : Prop := True

/-! ## 4. Auxiliary lemmas

In this Lean version `String` is a structure with a single field `data : List Char`, and
`String.take` / `String.drop` are defined through substrings. The following lemmas move them to
the `List Char` level, where Mathlib's list library applies. -/

theorem take_eq_mk (s : String) (n : Nat) : s.take n = String.mk (List.take n s.data) :=
  String.take_eq s n

theorem drop_eq_mk (s : String) (n : Nat) : s.drop n = String.mk (List.drop n s.data) :=
  String.drop_eq s n

theorem mk_data (s : String) : String.mk s.data = s := rfl

theorem mk_append_mk (a b : List Char) : String.mk a ++ String.mk b = String.mk (a ++ b) := rfl

theorem length_mk (l : List Char) : (String.mk l).length = l.length := rfl

theorem length_eq_data (s : String) : s.length = s.data.length := rfl

theorem length_take (s : String) (n : Nat) : (s.take n).length = min n s.length := by
  rw [take_eq_mk, length_mk, List.length_take, length_eq_data]

theorem take_append_drop (s : String) (n : Nat) : s.take n ++ s.drop n = s := by
  rw [take_eq_mk, drop_eq_mk, mk_append_mk, List.take_append_drop, mk_data]

theorem take_length (s : String) : s.take s.length = s := by
  rw [take_eq_mk, length_eq_data, List.take_length, mk_data]

/-- Membership characterisation: the elements of `allPrefixes s` are exactly `s[:i+1]`
for `i` in `range (len s)`. -/
theorem mem_allPrefixes {s p : String} :
    p ∈ allPrefixes s ↔ ∃ i < s.length, p = s.take (i + 1) := by
  constructor
  · intro h
    simp only [allPrefixes, List.mem_map] at h
    obtain ⟨i, hi, hpi⟩ := h
    exact ⟨i, List.mem_range.mp hi, by simpa using hpi.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- Two functions that agree on a list give the same `map`. -/
theorem map_congr_mem {α β : Type*} {l : List α} {f g : α → β}
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h1 : f a = g a := h a (by simp)
    have h2 : l.map f = l.map g := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, h1, h2]

/-- If the image of a list has no duplicates then neither does the list. -/
theorem nodup_of_map_nodup {α β : Type*} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a l ih =>
    intro h
    simp only [List.map_cons] at h
    obtain ⟨hfa, hl⟩ := List.nodup_cons.mp h
    exact List.Nodup.cons (fun ha => hfa (List.mem_map.mpr ⟨a, ha, rfl⟩)) (ih hl)

/-! ## 5. Properties of the Python specification -/

/-- P1: the result contains exactly `len(string)` prefixes. -/
def length_prop (s : String) : Prop := (allPrefixes s).length = s.length

theorem length_thm (s : String) : length_prop s := by
  show ((List.range s.length).map (fun i => s.take (i + 1))).length = s.length
  simp

/-- P2: the `i`-th element (0-based) of the result is `string[:i+1]`. -/
def elem_prop (s : String) : Prop :=
  ∀ i < s.length, (allPrefixes s)[i]? = some (s.take (i + 1))

theorem elem_thm (s : String) : elem_prop s := by
  intro i h
  show ((List.range s.length).map (fun j => s.take (j + 1)))[i]? = some (s.take (i + 1))
  rw [List.getElem?_map, List.getElem?_range h]
  rfl

/-- P3: every element of the result is a prefix of `s`.
(`∃ t, p ++ t = s` is precisely Mathlib's `String.IsPrefix p s`.) -/
def prefix_prop (s : String) : Prop := ∀ p ∈ allPrefixes s, ∃ t, p ++ t = s

theorem prefix_thm (s : String) : prefix_prop s := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := mem_allPrefixes.mp hp
  exact ⟨s.drop (i + 1), take_append_drop s (i + 1)⟩

/-- P3, phrased with Mathlib's prefix predicate `String.IsPrefix`
(`String.IsPrefix p s` unfolds to `∃ t, p.data ++ t = s.data`).
Its executable counterpart is the bounded/randomized PBT
`(allPrefixes s).all (fun p => s.take p.length == p)` in Section 7 below. -/
theorem prefix_isPrefix_thm (s : String) : ∀ p ∈ allPrefixes s, String.IsPrefix p s := by
  intro p hp
  obtain ⟨t, ht⟩ := prefix_thm s p hp
  cases s with
  | mk ls =>
    cases p with
    | mk lp =>
      cases t with
      | mk lt =>
        have h : lp ++ lt = ls := by
          have h2 := congrArg String.data ht
          simpa using h2
        show String.IsPrefix (String.mk lp) (String.mk ls)
        simp only [String.IsPrefix, List.IsPrefix]
        exact ⟨lt, h⟩

/-- P4: every element is non-empty and no longer than `s`. -/
def bounds_prop (s : String) : Prop :=
  ∀ p ∈ allPrefixes s, 0 < p.length ∧ p.length ≤ s.length

theorem bounds_thm (s : String) : bounds_prop s := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := mem_allPrefixes.mp hp
  rw [length_take, Nat.min_eq_left (Nat.succ_le_of_lt hi)]
  exact ⟨Nat.succ_pos i, Nat.succ_le_of_lt hi⟩

/-- P5: the lengths of the elements are `1, 2, ..., len s`, i.e. the prefixes are returned
from shortest to longest and no length is skipped or repeated. -/
def lengths_prop (s : String) : Prop :=
  (allPrefixes s).map String.length = (List.range s.length).map Nat.succ

theorem lengths_thm (s : String) : lengths_prop s := by
  have key : ∀ i ∈ List.range s.length, (s.take (i + 1)).length = i + 1 := by
    intro i hi
    rw [length_take, Nat.min_eq_left (Nat.succ_le_of_lt (List.mem_range.mp hi))]
  have h1 : (allPrefixes s).map String.length =
      (List.range s.length).map (fun i => (s.take (i + 1)).length) := by
    show ((List.range s.length).map (fun i => s.take (i + 1))).map String.length =
      (List.range s.length).map (fun i => (s.take (i + 1)).length)
    rw [List.map_map]
    rfl
  show (allPrefixes s).map String.length = (List.range s.length).map Nat.succ
  rw [h1, map_congr_mem key]

/-- P6: every prefix `s[:k]` with `1 <= k <= len s` occurs in the result
(the result contains *all* prefixes). -/
def complete_prop (s : String) : Prop :=
  ∀ k : Nat, 0 < k → k ≤ s.length → s.take k ∈ allPrefixes s

theorem complete_thm (s : String) : complete_prop s := by
  intro k hk1 hk2
  rw [mem_allPrefixes]
  refine ⟨k - 1, by omega, ?_⟩
  have h : k - 1 + 1 = k := by omega
  rw [h]

/-- P7: the result is ordered from shortest to longest: every element is a prefix of every
element that is at least as long. -/
def nested_prop (s : String) : Prop :=
  ∀ p q : String, p ∈ allPrefixes s → q ∈ allPrefixes s → p.length ≤ q.length → ∃ t, p ++ t = q

theorem nested_thm (s : String) : nested_prop s := by
  intro p q hp hq hle
  obtain ⟨i, hi, rfl⟩ := mem_allPrefixes.mp hp
  obtain ⟨j, hj, rfl⟩ := mem_allPrefixes.mp hq
  have hli : (s.take (i + 1)).length = i + 1 := by
    rw [length_take, Nat.min_eq_left (Nat.succ_le_of_lt hi)]
  have hlj : (s.take (j + 1)).length = j + 1 := by
    rw [length_take, Nat.min_eq_left (Nat.succ_le_of_lt hj)]
  have hij : i ≤ j := by
    rw [hli, hlj] at hle
    exact Nat.le_of_succ_le_succ hle
  have e2 : List.take (j + 1) s.data =
      List.take (i + 1) s.data ++ List.take (j - i) (List.drop (i + 1) s.data) := by
    have hid : i + 1 ≤ s.data.length := by
      rw [← length_eq_data]
      exact Nat.succ_le_of_lt hi
    have h1 : (List.take (i + 1) s.data).length = i + 1 := by
      rw [List.length_take, Nat.min_eq_left hid]
    calc List.take (j + 1) s.data
        = List.take (j + 1) (List.take (i + 1) s.data ++ List.drop (i + 1) s.data) := by
          congr 1
          exact (List.take_append_drop (i + 1) s.data).symm
      _ = List.take (j + 1) (List.take (i + 1) s.data) ++
            List.take (j + 1 - (List.take (i + 1) s.data).length) (List.drop (i + 1) s.data) := by
          rw [List.take_append]
      _ = List.take (i + 1) s.data ++ List.take (j - i) (List.drop (i + 1) s.data) := by
          rw [h1, List.take_take, Nat.min_comm, Nat.min_eq_left (Nat.succ_le_succ hij),
            show j + 1 - (i + 1) = j - i by omega]
  refine ⟨String.mk (List.take (j - i) (List.drop (i + 1) s.data)), ?_⟩
  rw [take_eq_mk s (i + 1), take_eq_mk s (j + 1), mk_append_mk]
  congr 1
  exact e2.symm

/-- P8: all prefixes in the result are pairwise distinct. -/
def nodup_prop (s : String) : Prop := (allPrefixes s).Nodup

theorem nodup_thm (s : String) : nodup_prop s := by
  have h : ((allPrefixes s).map String.length).Nodup := by
    have h1 : (allPrefixes s).map String.length = (List.range s.length).map Nat.succ :=
      lengths_thm s
    rw [h1]
    exact (List.nodup_map_iff Nat.succ_injective).mpr List.nodup_range
  show (allPrefixes s).Nodup
  exact nodup_of_map_nodup h

/-- P9: the last (longest) element is `s` itself, and the result is empty for the empty input. -/
def last_prop (s : String) : Prop :=
  (allPrefixes s).getLast? = if s.length = 0 then none else some s

theorem getLast?_allPrefixes (s : String) :
    (allPrefixes s).getLast? =
      Option.map (fun i => s.take (i + 1)) (List.range s.length).getLast? := by
  show ((List.range s.length).map (fun i => s.take (i + 1))).getLast? =
    Option.map (fun i => s.take (i + 1)) (List.range s.length).getLast?
  rw [List.getLast?_map]

theorem getLast?_range (n : Nat) :
    (List.range n).getLast? = if n = 0 then none else some (n - 1) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [List.range_succ, List.getLast?_concat]
    simp

theorem last_thm (s : String) : last_prop s := by
  show (allPrefixes s).getLast? = if s.length = 0 then none else some s
  rw [getLast?_allPrefixes, getLast?_range]
  by_cases h : s.length = 0
  · simp [h]
  · have h1 : s.length - 1 + 1 = s.length := by omega
    simp [h, h1, take_length]

/-- The empty string has no non-empty prefix. -/
theorem allPrefixes_empty : allPrefixes "" = [] := by
  show ((List.range ("" : String).length).map (fun i => ("" : String).take (i + 1))) = []
  simp

/-- Recursive structure: appending a character appends exactly one new (longest) prefix. -/
theorem allPrefixes_push (s : String) (c : Char) :
    allPrefixes (s.push c) = allPrefixes s ++ [s.push c] := by
  have hdata : (s.push c).data = s.data ++ [c] := by simp
  have hlen : (s.push c).length = Nat.succ s.length := by simp
  have push_eq : s.push c = String.mk (s.data ++ [c]) := by
    rw [← mk_data (s.push c), hdata]
  have key : ∀ i ∈ List.range s.length, (s.push c).take (i + 1) = s.take (i + 1) := by
    intro i hi
    have hi' : i < s.length := List.mem_range.mp hi
    rw [take_eq_mk, take_eq_mk, hdata]
    congr 1
    have h2 : i + 1 - s.data.length = 0 := by
      have h3 : i + 1 ≤ s.data.length := by
        rw [← length_eq_data]
        exact Nat.succ_le_of_lt hi'
      omega
    rw [List.take_append, h2, List.take_zero, List.append_nil]
  have last : (s.push c).take (s.length + 1) = s.push c := by
    rw [take_eq_mk, hdata, push_eq]
    congr 1
    rw [show s.length + 1 = (s.data ++ [c]).length by simp, List.take_length]
  show (List.range (s.push c).length).map (fun i => (s.push c).take (i + 1)) =
    (List.range s.length).map (fun i => s.take (i + 1)) ++ [s.push c]
  simp only [hlen, List.range_succ, List.map_append, List.map_singleton]
  rw [map_congr_mem key, last]

/-- Set-wise characterisation of the result: its elements are exactly the non-empty prefixes
`s[:k]` with `1 <= k <= len s`, each occurring once. -/
theorem mem_allPrefixes_iff (s p : String) :
    p ∈ allPrefixes s ↔ ∃ k, 0 < k ∧ k ≤ s.length ∧ p = s.take k := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := mem_allPrefixes.mp h
    exact ⟨i + 1, Nat.succ_pos i, Nat.succ_le_of_lt hi, rfl⟩
  · rintro ⟨k, hk1, hk2, rfl⟩
    exact complete_thm s k hk1 hk2

/-! ## 6. Post-condition -/

/-- The post-condition: conjunction of all properties of the Python specification. -/
def Post_prop (s : String) : Prop :=
  length_prop s ∧ elem_prop s ∧ prefix_prop s ∧ bounds_prop s ∧ lengths_prop s ∧
    complete_prop s ∧ nested_prop s ∧ nodup_prop s ∧ last_prop s

/-! ## 7. Property-based tests -/

/-- A fixed pool of test strings: the empty string, one-character strings, repeated characters,
the strings of the Python test suite, a string with spaces and a multi-byte (non-ASCII) one. -/
def testStrings : List String :=
  ["", "a", "W", "ab", "abc", "WWW", "asdfgh", "hello world", "aaaa", "xYz", "Lean4",
    "0123456789", "héllo", "  spaced  "]

/-- Executable counterpart of `Post_prop`.

The existential witnesses of `prefix_prop`, `nested_prop` and `complete_prop` are replaced by the
equivalent computable checks: `s.take p.length = p` says "`p` is a prefix of `s`" without an
existential quantifier over all strings, and `Nodup` is expressed through `dedup`. -/
def Post_check (s : String) : Bool :=
  ((allPrefixes s).length == s.length) &&
    ((List.range s.length).all (fun i => (allPrefixes s)[i]? == some (s.take (i + 1)))) &&
    ((allPrefixes s).all (fun p => s.take p.length == p)) &&
    ((allPrefixes s).all (fun p => decide (0 < p.length ∧ p.length ≤ s.length))) &&
    ((allPrefixes s).map String.length == (List.range s.length).map Nat.succ) &&
    ((List.range' 1 s.length).all (fun k => decide (s.take k ∈ allPrefixes s))) &&
    ((allPrefixes s).all (fun p => (allPrefixes s).all (fun q =>
      decide (p.length ≤ q.length → q.take p.length = p)))) &&
    ((allPrefixes s).dedup.length == (allPrefixes s).length) &&
    ((allPrefixes s).getLast? == if s.length = 0 then none else some s)

/-! ### Bounded property-based tests (exhaustive over `testStrings`) -/

-- PBT for `length_prop`
example : testStrings.all (fun s => (allPrefixes s).length == s.length) = true := by native_decide

-- PBT for `elem_prop`
example : testStrings.all (fun s =>
    (List.range s.length).all (fun i => (allPrefixes s)[i]? == some (s.take (i + 1)))) = true := by
  native_decide

-- PBT for `prefix_prop` (executable form: `s.take p.length = p`)
example : testStrings.all (fun s => (allPrefixes s).all (fun p => s.take p.length == p)) = true :=
  by native_decide

-- PBT for `bounds_prop`
example : testStrings.all (fun s =>
    (allPrefixes s).all (fun p => decide (0 < p.length ∧ p.length ≤ s.length))) = true := by
  native_decide

-- PBT for `lengths_prop`
example : testStrings.all (fun s =>
    (allPrefixes s).map String.length == (List.range s.length).map Nat.succ) = true := by
  native_decide

-- PBT for `complete_prop`
example : testStrings.all (fun s =>
    (List.range' 1 s.length).all (fun k => decide (s.take k ∈ allPrefixes s))) = true := by
  native_decide

-- PBT for `nested_prop` (executable form: `q.take p.length = p`)
example : testStrings.all (fun s => (allPrefixes s).all (fun p => (allPrefixes s).all (fun q =>
    decide (p.length ≤ q.length → q.take p.length = p)))) = true := by native_decide

-- PBT for `nodup_prop` (executable form: `dedup` does not shrink the list)
example : testStrings.all (fun s =>
    (allPrefixes s).dedup.length == (allPrefixes s).length) = true := by native_decide

-- PBT for `last_prop`
example : testStrings.all (fun s =>
    (allPrefixes s).getLast? == if s.length = 0 then none else some s) = true := by native_decide

-- PBT for the whole post-condition
example : testStrings.all Post_check = true := by native_decide

-- PBT for the recursive characterisation `allPrefixes_push`
example : testStrings.all (fun s => s.data.all (fun c =>
    allPrefixes (s.push c) == allPrefixes s ++ [s.push c])) = true := by native_decide

/-! ### Randomized property-based tests (Plausible) -/

#eval Plausible.Testable.check (∀ s : String, (allPrefixes s).length = s.length)

#eval Plausible.Testable.check
  (∀ s : String, ∀ i, decide (i < s.length → (allPrefixes s)[i]? = some (s.take (i + 1))))

#eval Plausible.Testable.check (∀ s : String, (allPrefixes s).all (fun p => s.take p.length == p))

#eval Plausible.Testable.check
  (∀ s : String, (allPrefixes s).all (fun p => decide (0 < p.length ∧ p.length ≤ s.length)))

#eval Plausible.Testable.check
  (∀ s : String, (allPrefixes s).map String.length = (List.range s.length).map Nat.succ)

#eval Plausible.Testable.check
  (∀ s : String, ∀ k, decide (0 < k → k ≤ s.length → s.take k ∈ allPrefixes s))

#eval Plausible.Testable.check
  (∀ s : String, (allPrefixes s).all (fun p => (allPrefixes s).all (fun q =>
    decide (p.length ≤ q.length → q.take p.length = p))))

#eval Plausible.Testable.check
  (∀ s : String, (allPrefixes s).dedup.length == (allPrefixes s).length)

#eval Plausible.Testable.check
  (∀ s : String, (allPrefixes s).getLast? == if s.length = 0 then none else some s)

#eval Plausible.Testable.check
  (∀ s : String, ∀ c : Char, allPrefixes (s.push c) == allPrefixes s ++ [s.push c])

#eval Plausible.Testable.check (∀ s : String, Post_check s)

/-! ## 8. Correctness theorem -/

/-- The implementation satisfies the specification: for every admissible input (all of them),
the post-condition holds. -/
theorem correctness_thm (s : String) : Pre s → Post_prop s := by
  intro _
  exact ⟨length_thm s, elem_thm s, prefix_thm s, bounds_thm s, lengths_thm s,
    complete_thm s, nested_thm s, nodup_thm s, last_thm s⟩

/-! ## 9. Imperative implementation (mutable state) -/

/-- The loop body of the Python program: `result.append(string[:i+1])`. -/
def pushPrefix (s : String) (acc : Array String) (i : Nat) : Array String :=
  acc.push (s.take (i + 1))

/-- Imperative implementation with mutable state, mirroring the Python code

```python
result = []
for i in range(len(string)):
    result.append(string[:i+1])
return result
```
-/
def allPrefixesImp (s : String) : List String := Id.run do
  let mut acc : Array String := #[]
  for i in List.range s.length do
    acc := pushPrefix s acc i
  return acc.toList

/-! ## 10. Imperative tests -/

example : allPrefixesImp "" = [] := by native_decide

example : allPrefixesImp "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] :=
  by native_decide

example : allPrefixesImp "WWW" = ["W", "WW", "WWW"] := by native_decide

example : allPrefixesImp "abc" = ["a", "ab", "abc"] := by native_decide

#eval allPrefixesImp "abc"
#eval allPrefixesImp ""

example : testStrings.all (fun s => allPrefixesImp s == allPrefixes s) = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, allPrefixesImp s == allPrefixes s)

/-! ## 11. Equivalence of the functional and the imperative implementations -/

/-- The imperative loop accumulates exactly `l.map (fun i => s.take (i + 1))` on top of `acc`. -/
theorem foldl_pushPrefix (s : String) (l : List Nat) :
    ∀ acc : Array String,
      (List.foldl (fun a i => pushPrefix s a i) acc l).toList =
        acc.toList ++ l.map (fun i => s.take (i + 1)) := by
  induction l with
  | nil => intro acc; simp [pushPrefix]
  | cons x xs ih =>
    intro acc
    have h1 : pushPrefix s acc x = acc.push (s.take (x + 1)) := rfl
    rw [List.foldl_cons, h1, List.map_cons, ih (acc.push (s.take (x + 1))),
      Array.toList_push, List.append_assoc, List.singleton_append]

/-- The imperative implementation computes the same list as the functional one. -/
theorem imp_eq_fun (s : String) : allPrefixesImp s = allPrefixes s := by
  have h := foldl_pushPrefix s (List.range s.length) #[]
  simp only [List.nil_append] at h
  have h2 : allPrefixesImp s =
      (List.foldl (fun a i => pushPrefix s a i) #[] (List.range s.length)).toList := by
    simp [allPrefixesImp]
  have h3 : (List.range s.length).map (fun i => s.take (i + 1)) = allPrefixes s := rfl
  exact h2.trans (h.trans h3)

end humaneval_14_all_prefixes
