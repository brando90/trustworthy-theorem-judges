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

`string[:i+1]` is the prefix consisting of the first `i + 1` characters (code points),
so the result is the list `[string[:1], string[:2], ..., string[:len(string)]]`.

The file contains

* a functional implementation `allPrefixes`,
* unit tests taken from the Python docstring and `check` function,
* a pre-condition `Pre` (every string is admissible),
* properties (`*_prop`) with proofs (`*_thm`), a post-condition `Post_prop`,
  property-based tests, and the correctness theorem `Pre → Post_prop`,
* an imperative implementation `allPrefixesImp` written with `Id.run do` and a
  mutable accumulator, mirroring the Python loop, together with an equivalence proof.
-/

namespace humaneval_14_all_prefixes

/-! ## Functional implementation -/

/-- `allPrefixes s` returns `[s.take 1, s.take 2, ..., s.take s.length]`, i.e. all non-empty
prefixes of `s` ordered from shortest to longest (Python: `[string[:i+1] for i in range(len(string))]`). -/
def allPrefixes (s : String) : List String :=
  (List.range s.length).map (fun i => s.take (i + 1))

/-! ## Unit tests (docstring example and the Python `check` function) -/

example : allPrefixes "abc" = ["a", "ab", "abc"] := by native_decide
example : allPrefixes "" = [] := by native_decide
example : allPrefixes "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide
example : allPrefixes "WWW" = ["W", "WW", "WWW"] := by native_decide
example : allPrefixes "L∃∀N" = ["L", "L∃", "L∃∀", "L∃∀N"] := by native_decide

#eval allPrefixes "abc"
#eval allPrefixes ""
#eval allPrefixes "asdfgh"
#eval allPrefixes "WWW"

/-! ## Pre-condition -/

/-- Pre-condition: every string is an admissible input. -/
def Pre (_s : String) : Prop := True

/-! ## Helper lemmas -/

/-- The `i`-th element (0-based) of `allPrefixes s` is the prefix of the first `i + 1` characters. -/
theorem getElem?_allPrefixes (s : String) (i : Nat) :
    (allPrefixes s)[i]? = if i < s.length then some (s.take (i + 1)) else none := by
  unfold allPrefixes
  by_cases h : i < s.length
  · simp [h]
  · simp [h]

/-- Membership characterization in terms of `String.take`. -/
theorem mem_allPrefixes_iff (s p : String) :
    p ∈ allPrefixes s ↔ ∃ i, i < s.length ∧ s.take (i + 1) = p := by
  unfold allPrefixes
  simp only [List.mem_map, List.mem_range]

theorem length_take_of_lt (s : String) (i : Nat) (h : i < s.length) :
    (s.take (i + 1)).length = i + 1 := by
  rw [String.take_eq]
  show (s.data.take (i + 1)).length = i + 1
  rw [List.length_take]
  exact Nat.min_eq_left h

theorem take_append_drop (s : String) (n : Nat) : s.take n ++ s.drop n = s := by
  rw [String.take_eq, String.drop_eq]
  show String.mk (s.data.take n ++ s.data.drop n) = s
  rw [List.take_append_drop]

theorem take_length_eq (s : String) : s.take s.length = s := by
  rw [String.take_eq]
  show String.mk (s.data.take s.data.length) = s
  rw [List.take_length]

theorem length_pos_of_ne_empty (s : String) (h : s ≠ "") : 0 < s.length := by
  rcases s with ⟨cs⟩
  cases cs with
  | nil => exact absurd rfl h
  | cons c cs => show 0 < (c :: cs).length; simp

/-! ## Properties -/

/-- The result has exactly `len(string)` elements (one per loop iteration). -/
def length_prop (s : String) : Prop := (allPrefixes s).length = s.length

theorem length_thm (s : String) : length_prop s := by
  unfold length_prop allPrefixes
  simp

/-- The `i`-th element (0-based) is `string[:i+1]`, the prefix of the first `i + 1` characters. -/
def nth_prop (s : String) : Prop :=
  ∀ i : Nat, i < s.length → (allPrefixes s)[i]? = some (s.take (i + 1))

theorem nth_thm (s : String) : nth_prop s := by
  intro i hi
  rw [getElem?_allPrefixes, if_pos hi]

/-- The same statement in terms of character lists: the `i`-th element consists of exactly the
first `i + 1` characters of the input (independent of the definition of `String.take`). -/
def nth_chars_prop (s : String) : Prop :=
  ∀ i : Nat, i < s.length → ((allPrefixes s)[i]?.map String.toList) = some (s.toList.take (i + 1))

theorem nth_chars_thm (s : String) : nth_chars_prop s := by
  intro i hi
  rw [nth_thm s i hi, Option.map_some, String.take_eq]
  rfl

/-- Every element of the result is a prefix of the input string. -/
def isPrefix_prop (s : String) : Prop :=
  ∀ p ∈ allPrefixes s, ∃ t : String, p ++ t = s

theorem isPrefix_thm (s : String) : isPrefix_prop s := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := (mem_allPrefixes_iff s p).mp hp
  exact ⟨s.drop (i + 1), take_append_drop s (i + 1)⟩

/-- Every element of the result is non-empty (the shortest prefix is `string[:1]`). -/
def nonempty_prop (s : String) : Prop :=
  ∀ p ∈ allPrefixes s, p ≠ ""

theorem nonempty_thm (s : String) : nonempty_prop s := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := (mem_allPrefixes_iff s p).mp hp
  intro h
  have h1 := length_take_of_lt s i hi
  rw [h] at h1
  have h2 : ("" : String).length = 0 := rfl
  omega

/-- The lengths of the prefixes are exactly `1, 2, ..., len(string)` (shortest to longest). -/
def lengths_prop (s : String) : Prop :=
  (allPrefixes s).map String.length = List.range' 1 s.length

theorem lengths_thm (s : String) : lengths_prop s := by
  unfold lengths_prop allPrefixes
  rw [List.map_map, List.range'_eq_map_range]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  show (s.take (i + 1)).length = 1 + i
  rw [length_take_of_lt s i hi, Nat.add_comm]

/-- The prefixes are listed from shortest to longest: lengths strictly increase along the list. -/
def sorted_prop (s : String) : Prop :=
  (allPrefixes s).Pairwise (fun a b => a.length < b.length)

theorem sorted_thm (s : String) : sorted_prop s := by
  unfold sorted_prop
  rw [← List.pairwise_map (f := String.length), lengths_thm s]
  exact List.pairwise_lt_range' 1

/-- All prefixes in the result are pairwise distinct. -/
def nodup_prop (s : String) : Prop := (allPrefixes s).Nodup

theorem nodup_thm (s : String) : nodup_prop s := by
  unfold nodup_prop List.Nodup
  exact (sorted_thm s).imp (fun h heq => by rw [heq] at h; exact Nat.lt_irrefl _ h)

/-- For a non-empty string the last (longest) prefix is the string itself. -/
def last_prop (s : String) : Prop :=
  s ≠ "" → (allPrefixes s).getLast? = some s

theorem last_thm (s : String) : last_prop s := by
  intro hs
  have hpos := length_pos_of_ne_empty s hs
  obtain ⟨n, hn⟩ : ∃ n, s.length = n + 1 := ⟨s.length - 1, by omega⟩
  unfold allPrefixes
  rw [hn, List.range_succ, List.map_append, List.map_singleton, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, ← hn, take_length_eq]

/-- The empty string has no prefixes in the result. -/
def empty_prop : Prop := allPrefixes "" = []

theorem empty_thm : empty_prop := by
  unfold empty_prop allPrefixes
  rfl

/-- Complete characterization: the result contains exactly the non-empty prefixes of the input. -/
def mem_iff_prop (s : String) : Prop :=
  ∀ p : String, p ∈ allPrefixes s ↔ (p ≠ "" ∧ ∃ t : String, p ++ t = s)

theorem mem_iff_thm (s : String) : mem_iff_prop s := by
  intro p
  constructor
  · intro hp
    exact ⟨nonempty_thm s p hp, isPrefix_thm s p hp⟩
  · rintro ⟨hne, t, rfl⟩
    rw [mem_allPrefixes_iff]
    have hp := length_pos_of_ne_empty p hne
    refine ⟨p.length - 1, ?_, ?_⟩
    · show p.length - 1 < (p ++ t).length
      show p.length - 1 < (p.data ++ t.data).length
      rw [List.length_append]
      have hpl : p.length = p.data.length := rfl
      omega
    · rw [Nat.sub_add_cancel hp, String.take_eq]
      show String.mk ((p.data ++ t.data).take p.data.length) = p
      rw [List.take_left]

/-! ## Post-condition -/

/-- Post-condition: conjunction of all properties above. -/
def Post_prop (s : String) : Prop :=
  length_prop s ∧ nth_prop s ∧ nth_chars_prop s ∧ isPrefix_prop s ∧ nonempty_prop s ∧
    lengths_prop s ∧ sorted_prop s ∧ nodup_prop s ∧ last_prop s ∧ empty_prop ∧ mem_iff_prop s

/-! ## Property-based tests -/

-- length_prop
#eval Plausible.Testable.check (∀ s : String, (allPrefixes s).length = s.length)

-- nth_prop: randomized with the precondition `i < s.length` (Plausible's final sample has size 0,
-- i.e. `s = ""`, so it reports one "gave up" sample), then an exhaustive check over all admissible
-- indices of each sampled string, and the precondition-free characterization of `getElem?`.
#eval Plausible.Testable.check
  (∀ s : String, ∀ i : Nat, i < s.length → (allPrefixes s)[i]? = some (s.take (i + 1)))
#eval Plausible.Testable.check
  (∀ s : String, (List.range s.length).all
    (fun i => (allPrefixes s)[i]? == some (s.take (i + 1))) = true)
#eval Plausible.Testable.check
  (∀ s : String, ∀ i : Nat,
    (allPrefixes s)[i]? = if i < s.length then some (s.take (i + 1)) else none)

-- nth_chars_prop
#eval Plausible.Testable.check
  (∀ s : String, (List.range s.length).all
    (fun i => (allPrefixes s)[i]?.map String.toList == some (s.toList.take (i + 1))) = true)

-- isPrefix_prop (executable form via `String.isPrefixOf`)
#eval Plausible.Testable.check
  (∀ s : String, (allPrefixes s).all (fun p => p.isPrefixOf s) = true)

-- nonempty_prop
#eval Plausible.Testable.check (∀ s : String, (allPrefixes s).all (fun p => p != "") = true)

-- lengths_prop
#eval Plausible.Testable.check
  (∀ s : String, (allPrefixes s).map String.length = List.range' 1 s.length)

-- sorted_prop
#eval Plausible.Testable.check
  (∀ s : String, (allPrefixes s).Pairwise (fun a b => a.length < b.length))

-- nodup_prop
#eval Plausible.Testable.check (∀ s : String, (allPrefixes s).Nodup)

-- last_prop (randomized with precondition -- the size-0 sample `s = ""` is reported as "gave up" --
-- plus two versions without precondition)
#eval Plausible.Testable.check (∀ s : String, s ≠ "" → (allPrefixes s).getLast? = some s)
#eval Plausible.Testable.check
  (∀ s : String, (s == "" || (allPrefixes s).getLast? == some s) = true)
#eval Plausible.Testable.check
  (∀ (c : Char) (s : String),
    (allPrefixes (c.toString ++ s)).getLast? = some (c.toString ++ s))

-- empty_prop
example : allPrefixes "" = [] := by decide

-- mem_iff_prop (executable form via `String.isPrefixOf`); random `p` plus the prefixes of `s`
#eval Plausible.Testable.check
  (∀ s p : String, decide (p ∈ allPrefixes s) = (p != "" && p.isPrefixOf s))
#eval Plausible.Testable.check
  (∀ s : String, (allPrefixes s).all (fun p => decide (p ∈ allPrefixes s) == (p != "" && p.isPrefixOf s)) = true)
#eval Plausible.Testable.check
  (∀ s : String, ∀ n : Nat,
    decide (s.take n ∈ allPrefixes s) = (s.take n != "" && (s.take n).isPrefixOf s))

/-- Executable Boolean form of `Post_prop` (used for property-based testing). -/
def postCheck (s : String) : Bool :=
  let ps := allPrefixes s
  ps.length == s.length &&
  (List.range s.length).all (fun i => ps[i]? == some (s.take (i + 1))) &&
  (List.range s.length).all (fun i => ps[i]?.map String.toList == some (s.toList.take (i + 1))) &&
  ps.all (fun p => p.isPrefixOf s) &&
  ps.all (fun p => p != "") &&
  (ps.map String.length == List.range' 1 s.length) &&
  decide (ps.Pairwise (fun a b => a.length < b.length)) &&
  decide ps.Nodup &&
  (s == "" || ps.getLast? == some s) &&
  (allPrefixes "" == []) &&
  ps.all (fun p => decide (p ∈ ps) == (p != "" && p.isPrefixOf s))

#eval Plausible.Testable.check (∀ s : String, postCheck s = true)
example : ["", "a", "ab", "abc", "WWW", "asdfgh", "L∃∀N", "a b c"].all postCheck = true := by
  native_decide

/-! ## Correctness theorem -/

theorem correctness (s : String) (_h : Pre s) : Post_prop s :=
  ⟨length_thm s, nth_thm s, nth_chars_thm s, isPrefix_thm s, nonempty_thm s, lengths_thm s,
    sorted_thm s, nodup_thm s, last_thm s, empty_thm, mem_iff_thm s⟩

/-! ## Imperative implementation -/

/-- Imperative version mirroring the Python loop: a mutable accumulator `result`, a loop over
`range(len(string))`, appending `string[:i+1]` at each step. -/
def allPrefixesImp (s : String) : List String := Id.run do
  let mut result : Array String := #[]
  for i in [0:s.length] do
    result := result.push (s.take (i + 1))
  return result.toList

/-! ## Imperative tests -/

example : allPrefixesImp "abc" = ["a", "ab", "abc"] := by native_decide
example : allPrefixesImp "" = [] := by native_decide
example : allPrefixesImp "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide
example : allPrefixesImp "WWW" = ["W", "WW", "WWW"] := by native_decide

#eval allPrefixesImp "abc"
#eval allPrefixesImp "asdfgh"

#eval Plausible.Testable.check (∀ s : String, allPrefixesImp s = allPrefixes s)

/-! ## Equivalence theorem -/

/-- Folding `push` over a list of indices appends the mapped values to the accumulator. -/
theorem foldl_push_toList (f : Nat → String) (l : List Nat) (acc : Array String) :
    (l.foldl (fun r i => r.push (f i)) acc).toList = acc.toList ++ l.map f := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Array.toList_push, List.map_cons, List.append_assoc,
      List.singleton_append]

theorem equiv (s : String) : allPrefixesImp s = allPrefixes s := by
  unfold allPrefixesImp allPrefixes
  -- `[0:n]` has `n` elements; the loop is a `foldl` of `push`; `Id.run` of `pure` is the identity.
  simp only [Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, bind_pure_comp, map_pure, List.forIn_pure_yield_eq_foldl, Id.run_pure,
    foldl_push_toList, List.nil_append, List.range_eq_range']

end humaneval_14_all_prefixes
