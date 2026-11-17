import Mathlib
import Plausible

/-!
# VeriBench — HumanEval/14 `all_prefixes`

File: `humaneval_14_all_prefixes.lean`

Python source: `humaneval_14_all_prefixes.py`

```python
def all_prefixes(string: str) -> List[str]:
    result = []
    for i in range(len(string)):
        result.append(string[:i+1])
    return result
```

Return every nonempty prefix of `string`, from shortest to longest.
The empty string has no nonempty prefix, so the result is `[]`.

Python 3 strings are sequences of Unicode code points. Lean's `String.data`
is that sequence (`List Char`), and `List.take` is the code-point slice
`string[:k]`. The empty prefix is a prefix of every string and is excluded,
matching `range(len(string))` which never emits `string[:0]`.
-/

namespace humaneval_14_all_prefixes

/-- All nonempty prefixes of `s`, shortest first.
`all_prefixes s` at index `i` is the code-point slice `s[:i+1]`. -/
def all_prefixes (s : String) : List String :=
  (List.range s.length).map fun i => (s.data.take (i + 1)).asString


/-- Ground tests from the Python docstring and `check`. -/
example : all_prefixes "" = [] := by native_decide
example : all_prefixes "abc" = ["a", "ab", "abc"] := by native_decide
example : all_prefixes "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by
  native_decide
example : all_prefixes "WWW" = ["W", "WW", "WWW"] := by native_decide
example : all_prefixes "a∃b" = ["a", "a∃", "a∃b"] := by native_decide

#eval all_prefixes ""
#eval all_prefixes "abc"
#eval all_prefixes "asdfgh"
#eval all_prefixes "WWW"


@[simp] theorem data_length (s : String) : s.data.length = s.length := by
  cases s
  rfl

@[simp] theorem asString_data (cs : List Char) : cs.asString.data = cs := rfl

@[simp] theorem asString_length (cs : List Char) : cs.asString.length = cs.length := by
  simp [List.asString]

@[simp] theorem asString_of_data (s : String) : s.data.asString = s := by
  cases s
  simp [List.asString]

theorem length_eq_zero_iff (s : String) : s.length = 0 ↔ s = "" := by
  cases s with
  | mk cs =>
    constructor
    · intro h
      apply String.ext
      have hlen : cs.length = 0 := by simpa [String.length_mk] using h
      exact List.length_eq_zero_iff.mp hlen
    · intro h
      have hdata : cs = [] := by
        have := congrArg String.data h
        simpa using this
      simp [hdata]

def Pre (_s : String) : Prop := True

def length_prop (s : String) : Prop :=
  (all_prefixes s).length = s.length

theorem length_thm (s : String) (_h : Pre s) : length_prop s := by
  simp [length_prop, all_prefixes]

def empty_prop (s : String) : Prop :=
  s = "" → all_prefixes s = []

theorem empty_thm (s : String) (_h : Pre s) : empty_prop s := by
  intro hs
  subst hs
  simp [all_prefixes]

def nth_prefix_prop (s : String) : Prop :=
  ∀ i, i < s.length →
    (all_prefixes s)[i]? = some ((s.data.take (i + 1)).asString)

theorem nth_prefix_thm (s : String) (_h : Pre s) : nth_prefix_prop s := by
  intro i hi
  simp [all_prefixes, List.getElem?_map, List.getElem?_range hi]

def prefix_lengths_prop (s : String) : Prop :=
  ∀ i, i < s.length →
    ((all_prefixes s)[i]?).map String.length = some (i + 1)

theorem prefix_lengths_thm (s : String) (_h : Pre s) : prefix_lengths_prop s := by
  intro i hi
  have htake : (s.data.take (i + 1)).length = i + 1 := by
    apply List.length_take_of_le
    simpa [data_length] using Nat.succ_le_of_lt hi
  simp [all_prefixes, List.getElem?_map, List.getElem?_range hi, htake]

def mem_iff_prop (s : String) : Prop :=
  ∀ p : String, p ∈ all_prefixes s ↔ p ≠ "" ∧ p.data <+: s.data

theorem mem_iff_thm (s : String) (_h : Pre s) : mem_iff_prop s := by
  intro p
  constructor
  · intro hp
    rw [all_prefixes, List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    have hi' : i < s.length := List.mem_range.mp hi
    constructor
    · intro h
      have hdata : s.data.take (i + 1) = [] := by
        have := congrArg String.data h
        simpa [asString_data] using this
      have hlen0 : (s.data.take (i + 1)).length = 0 := by simp [hdata]
      have hlen : (s.data.take (i + 1)).length = i + 1 := by
        apply List.length_take_of_le
        simpa [data_length] using Nat.succ_le_of_lt hi'
      omega
    · simpa [asString_data] using List.take_prefix (i + 1) s.data
  · intro hpre
    have hne : p ≠ "" := hpre.1
    have hpref : p.data <+: s.data := hpre.2
    have hdata_ne : p.data ≠ [] := by
      intro hnil
      apply hne
      apply String.ext
      rw [hnil]
    have hlen_pos : 0 < p.data.length := List.length_pos_iff.mpr hdata_ne
    have hp_eq : p.data = s.data.take p.data.length := (List.prefix_iff_eq_take).mp hpref
    have hlen_le : p.data.length ≤ s.data.length := List.IsPrefix.length_le hpref
    let i := p.data.length - 1
    have hi_len : i + 1 = p.data.length := Nat.sub_add_cancel hlen_pos
    have hi : i < s.length := by
      have : p.data.length ≤ s.length := by simpa [data_length] using hlen_le
      omega
    rw [all_prefixes, List.mem_map]
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    apply String.ext
    rw [asString_data, hp_eq, hi_len]

def ordered_prefix_prop (s : String) : Prop :=
  ∀ i j, i < j → j < (all_prefixes s).length →
    ∃ a b,
      (all_prefixes s)[i]? = some a ∧
      (all_prefixes s)[j]? = some b ∧
      a.data <+: b.data ∧
      a.length < b.length

theorem ordered_prefix_thm (s : String) (_h : Pre s) : ordered_prefix_prop s := by
  intro i j hij hj
  have hlen : (all_prefixes s).length = s.length := by simp [all_prefixes]
  have hj' : j < s.length := by simpa [hlen] using hj
  have hi' : i < s.length := Nat.lt_trans hij hj'
  have htake_i : (s.data.take (i + 1)).length = i + 1 := by
    apply List.length_take_of_le
    simpa [data_length] using Nat.succ_le_of_lt hi'
  have htake_j : (s.data.take (j + 1)).length = j + 1 := by
    apply List.length_take_of_le
    simpa [data_length] using Nat.succ_le_of_lt hj'
  refine ⟨(s.data.take (i + 1)).asString, (s.data.take (j + 1)).asString, ?_, ?_, ?_, ?_⟩
  · simp [all_prefixes, List.getElem?_map, List.getElem?_range hi']
  · simp [all_prefixes, List.getElem?_map, List.getElem?_range hj']
  · simpa [asString_data] using
      List.take_prefix_take_left (l := s.data) (i := i + 1) (j := j + 1)
        (Nat.succ_le_succ (Nat.le_of_lt hij))
  · simp [htake_i, htake_j]
    omega

def last_eq_prop (s : String) : Prop :=
  s ≠ "" → (all_prefixes s).getLast? = some s

theorem last_eq_thm (s : String) (_h : Pre s) : last_eq_prop s := by
  intro hne
  have hpos : 0 < s.length := Nat.pos_of_ne_zero fun h =>
    hne ((length_eq_zero_iff s).mp h)
  have hlen : (all_prefixes s).length = s.length := by simp [all_prefixes]
  rw [List.getLast?_eq_getElem?]
  have hidx' : s.length - 1 < s.length := Nat.sub_lt hpos (by decide)
  simp [all_prefixes, List.getElem?_map, List.getElem?_range hidx']
  have htake : s.data.take ((s.length - 1) + 1) = s.data := by
    have : (s.length - 1) + 1 = s.length := Nat.sub_add_cancel hpos
    rw [this]
    apply List.take_of_length_le
    simp
  apply String.ext
  simp [htake]

def nodup_prop (s : String) : Prop :=
  (all_prefixes s).Nodup

theorem all_prefixes_getElem (s : String) (i : Nat) (hi : i < (all_prefixes s).length) :
    (all_prefixes s)[i] = (s.data.take (i + 1)).asString := by
  have hlen : (all_prefixes s).length = s.length := by simp [all_prefixes]
  have hi' : i < s.length := by omega
  simp [all_prefixes, List.getElem_map, List.getElem_range]

theorem nodup_thm (s : String) (_h : Pre s) : nodup_prop s := by
  rw [nodup_prop, List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hlen : (all_prefixes s).length = s.length := by simp [all_prefixes]
  have hi' : i < s.length := by omega
  have hj' : j < s.length := by omega
  rw [all_prefixes_getElem s i hi, all_prefixes_getElem s j hj]
  intro heq
  have hlen_eq := congrArg String.length heq
  have hti : (s.data.take (i + 1)).length = i + 1 := by
    apply List.length_take_of_le
    simpa [data_length] using Nat.succ_le_of_lt hi'
  have htj : (s.data.take (j + 1)).length = j + 1 := by
    apply List.length_take_of_le
    simpa [data_length] using Nat.succ_le_of_lt hj'
  simp [hti, htj] at hlen_eq
  omega

def push_prop (s : String) : Prop :=
  ∀ c : Char, all_prefixes (s.push c) = all_prefixes s ++ [s.push c]

theorem push_thm (s : String) (_h : Pre s) : push_prop s := by
  intro c
  simp only [all_prefixes, String.length_push, String.data_push]
  rw [List.range_succ, List.map_append, List.map_singleton]
  have hleft :
      ((List.range s.length).map fun i => ((s.data ++ [c]).take (i + 1)).asString) =
        ((List.range s.length).map fun i => (s.data.take (i + 1)).asString) := by
    apply List.map_congr_left
    intro i hi
    apply congrArg List.asString
    apply List.take_append_of_le_length
    have hi' : i < s.length := List.mem_range.mp hi
    have : i + 1 ≤ s.data.length := by
      rw [data_length]
      exact Nat.succ_le_of_lt hi'
    exact this
  have hright : ((s.data ++ [c]).take (s.length + 1)).asString = s.push c := by
    apply String.ext
    rw [asString_data, String.data_push]
    have hlen : s.length = s.data.length := (data_length s).symm
    rw [hlen, List.take_length_add_append, List.take_succ_cons, List.take_zero]
  rw [hleft, hright]

def head_prop (s : String) : Prop :=
  0 < s.length → (all_prefixes s).head? = some ((s.data.take 1).asString)

theorem head_thm (s : String) (_h : Pre s) : head_prop s := by
  intro hpos
  rw [all_prefixes, List.head?_map, List.head?_range]
  simp [Nat.ne_of_gt hpos]

def no_empty_prefix_prop (s : String) : Prop :=
  "" ∉ all_prefixes s

theorem no_empty_prefix_thm (s : String) (h : Pre s) : no_empty_prefix_prop s := by
  intro hin
  have hmem := (mem_iff_thm s h) ""
  exact (hmem.mp hin).1 rfl

def Post_prop (s : String) : Prop :=
  length_prop s ∧ empty_prop s ∧ nth_prefix_prop s ∧ prefix_lengths_prop s ∧
  mem_iff_prop s ∧ ordered_prefix_prop s ∧ last_eq_prop s ∧ nodup_prop s ∧
  push_prop s ∧ head_prop s ∧ no_empty_prefix_prop s


/-! ## Property-based tests

Executable Boolean forms of each `_prop` and of `Post_prop`.
Randomized checks use Plausible. Bounded checks exhaust small code-point strings.
-/

def length_ok (s : String) : Bool :=
  (all_prefixes s).length == s.length

def empty_ok (s : String) : Bool :=
  if s == "" then all_prefixes s == [] else true

def nth_ok (s : String) : Bool :=
  (List.range s.length).all fun i =>
    (all_prefixes s)[i]? == some ((s.data.take (i + 1)).asString)

def prefix_lengths_ok (s : String) : Bool :=
  (List.range s.length).all fun i =>
    ((all_prefixes s)[i]?).map String.length == some (i + 1)

def mem_ok (s p : String) : Bool :=
  decide (p ∈ all_prefixes s) == decide (p ≠ "" ∧ p.data <+: s.data)

def ordered_ok (s : String) : Bool :=
  let ps := all_prefixes s
  (List.range ps.length).all fun j =>
    (List.range j).all fun i =>
      match ps[i]?, ps[j]? with
      | some a, some b => decide (a.data <+: b.data) && decide (a.length < b.length)
      | _, _ => false

def last_ok (s : String) : Bool :=
  if s == "" then true else (all_prefixes s).getLast? == some s

def nodup_ok (s : String) : Bool :=
  decide (all_prefixes s).Nodup

def push_ok (s : String) (c : Char) : Bool :=
  all_prefixes (s.push c) == all_prefixes s ++ [s.push c]

def head_ok (s : String) : Bool :=
  if s.length == 0 then true
  else (all_prefixes s).head? == some ((s.data.take 1).asString)

def no_empty_prefix_ok (s : String) : Bool :=
  decide ("" ∉ all_prefixes s)

/-- Executable form of `Post_prop`, with the two quantified conjuncts instantiated. -/
def post_ok (s p : String) (c : Char) : Bool :=
  length_ok s && empty_ok s && nth_ok s && prefix_lengths_ok s && mem_ok s p &&
    ordered_ok s && last_ok s && nodup_ok s && push_ok s c && head_ok s &&
    no_empty_prefix_ok s

#eval Plausible.Testable.check (∀ s : String, length_ok s = true)
#eval Plausible.Testable.check (∀ s : String, empty_ok s = true)
#eval Plausible.Testable.check (∀ s : String, nth_ok s = true)
#eval Plausible.Testable.check (∀ s : String, prefix_lengths_ok s = true)
#eval Plausible.Testable.check (∀ s p : String, mem_ok s p = true)
#eval Plausible.Testable.check (∀ s : String, ordered_ok s = true)
#eval Plausible.Testable.check (∀ s : String, last_ok s = true)
#eval Plausible.Testable.check (∀ s : String, nodup_ok s = true)
#eval Plausible.Testable.check (∀ s : String, ∀ c : Char, push_ok s c = true)
#eval Plausible.Testable.check (∀ s : String, head_ok s = true)
#eval Plausible.Testable.check (∀ s : String, no_empty_prefix_ok s = true)
#eval Plausible.Testable.check (∀ s p : String, ∀ c : Char, post_ok s p c = true)

/-- All lists of length exactly `n` over `alphabet`. -/
def listsOfLen : Nat → List Char → List (List Char)
  | 0, _ => [[]]
  | n + 1, alph => (listsOfLen n alph).flatMap fun cs => alph.map fun c => cs ++ [c]

/-- All lists of length at most `n` over `alphabet`, including `[]`. -/
def listsUpTo : Nat → List Char → List (List Char)
  | 0, _ => [[]]
  | n + 1, alph => listsUpTo n alph ++ listsOfLen (n + 1) alph

def smallAlphabet : List Char := ['a', 'b', 'W']

example : (listsUpTo 3 smallAlphabet).all (fun cs =>
    let s := cs.asString
    length_ok s && empty_ok s && nth_ok s && prefix_lengths_ok s &&
      ordered_ok s && last_ok s && nodup_ok s && head_ok s &&
      no_empty_prefix_ok s) = true := by
  native_decide

example : (listsUpTo 2 ['a', 'b']).all (fun cs =>
    (listsUpTo 2 ['a', 'b']).all (fun ds => mem_ok cs.asString ds.asString)) = true := by
  native_decide

example : (listsUpTo 2 ['a', 'b']).all (fun cs =>
    ['a', 'b', 'c', 'W', '∃'].all (fun c => push_ok cs.asString c)) = true := by
  native_decide

example : (listsUpTo 2 smallAlphabet).all (fun cs =>
    (listsUpTo 2 ['a', 'W']).all (fun ds =>
      ['x'].all (fun c => post_ok cs.asString ds.asString c))) = true := by
  native_decide

theorem correctness_thm (s : String) (h : Pre s) : Post_prop s :=
  ⟨length_thm s h, empty_thm s h, nth_prefix_thm s h, prefix_lengths_thm s h,
   mem_iff_thm s h, ordered_prefix_thm s h, last_eq_thm s h, nodup_thm s h,
   push_thm s h, head_thm s h, no_empty_prefix_thm s h⟩

/-- Imperative loop, matching the Python accumulator:
`for i in range(len(string)): result.append(string[:i+1])`. -/
def all_prefixesImp (s : String) : List String :=
  Id.run do
    let mut result : List String := []
    for i in List.range s.length do
      result := result ++ [(s.data.take (i + 1)).asString]
    return result


/-- Imperative tests: the same ground cases as the functional implementation. -/
example : all_prefixesImp "" = [] := by native_decide
example : all_prefixesImp "abc" = ["a", "ab", "abc"] := by native_decide
example : all_prefixesImp "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by
  native_decide
example : all_prefixesImp "WWW" = ["W", "WW", "WWW"] := by native_decide
example : all_prefixesImp "a∃b" = ["a", "a∃", "a∃b"] := by native_decide
example : all_prefixesImp "abc" = all_prefixes "abc" := by native_decide

#eval all_prefixesImp ""
#eval all_prefixesImp "abc"
#eval all_prefixesImp "WWW"

theorem forIn_id_yield_eq_foldl {α β : Type} (l : List α) (f : α → β → β) (init : β) :
    (forIn (m := Id) l init (fun a b => ForInStep.yield (f a b))) =
      l.foldl (fun b a => f a b) init := by
  induction l generalizing init with
  | nil =>
    simp [forIn]
    rfl
  | cons a as ih =>
    rw [List.forIn_cons]
    simp only [bind]
    exact ih (f a init)

theorem map_singleton_flatten {α β : Type} (f : α → β) (l : List α) :
    (l.map (fun a => [f a])).flatten = l.map f := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem foldl_append_singleton_eq_map {α β : Type} (l : List α) (f : α → β) :
    l.foldl (fun acc a => acc ++ [f a]) [] = l.map f := by
  simp [map_singleton_flatten, List.foldl_append_eq_append]

theorem all_prefixesImp_eq_foldl (s : String) :
    all_prefixesImp s =
      (List.range s.length).foldl
        (fun acc i => acc ++ [(s.data.take (i + 1)).asString]) [] := by
  unfold all_prefixesImp
  simp only [Id.run, bind, pure]
  exact forIn_id_yield_eq_foldl _ _ _

theorem equivalence_thm (s : String) : all_prefixes s = all_prefixesImp s := by
  rw [all_prefixes, all_prefixesImp_eq_foldl]
  exact (foldl_append_singleton_eq_map (List.range s.length)
    (fun i => (s.data.take (i + 1)).asString)).symm

end humaneval_14_all_prefixes
