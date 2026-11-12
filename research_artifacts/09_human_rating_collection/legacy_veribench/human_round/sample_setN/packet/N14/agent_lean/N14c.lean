import Mathlib
import Plausible

/-!
# HumanEval/14 - `all_prefixes`

Formalization of the Python program `humaneval_14_all_prefixes.py`
(HumanEval problem 14):

```python
def all_prefixes(string: str) -> List[str]:
    result = []
    for i in range(len(string)):
        result.append(string[:i+1])
    return result
```

`all_prefixes` returns the list of all non-empty prefixes of the input
string, ordered from shortest to longest.  For example
`all_prefixes('abc') = ['a', 'ab', 'abc']` and `all_prefixes('') = []`.

Contents of this file:
* the functional implementation `allPrefixes`,
* unit tests (`example ... := by native_decide` and `#eval`),
* the pre-condition `Pre`, property propositions `*_prop` and their proofs,
* the post-condition `Post_prop` and property-based tests,
* the correctness theorem `Pre -> Post`,
* an imperative implementation `allPrefixesImp` using `Id.run do` with a
  mutable accumulator, together with its tests,
* the equivalence theorem `allPrefixes = allPrefixesImp`.
-/

namespace humaneval_14_all_prefixes

/-- The `i`-th non-empty prefix (0-based) of `s`: its first `i + 1`
characters, mirroring Python's `string[:i+1]`. -/
def prefixAt (s : String) (i : Nat) : String :=
  String.mk (s.toList.take (i + 1))

/-- Functional implementation of `all_prefixes`. -/
def allPrefixes (s : String) : List String :=
  (List.range s.length).map (prefixAt s)

-- ## Unit tests

example : allPrefixes "" = [] := by native_decide
example : allPrefixes "abc" = ["a", "ab", "abc"] := by native_decide
example : allPrefixes "asdfgh" =
    ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide
example : allPrefixes "WWW" = ["W", "WW", "WWW"] := by native_decide

#eval allPrefixes "abc"     -- expected: ["a", "ab", "abc"]
#eval allPrefixes ""        -- expected: []
#eval allPrefixes "WWW"     -- expected: ["W", "WW", "WWW"]

/-- Pre-condition: Python's `all_prefixes` accepts any string, so the
pre-condition is trivially true. -/
def Pre (_s : String) : Prop := True

/-- Property 1: the result has exactly one prefix per character. -/
def allPrefixes_length_prop (s : String) (out : List String) : Prop :=
  out.length = s.length

/-- Property 2: the `i`-th element is the prefix of length `i + 1`. -/
def allPrefixes_elem_prop (s : String) (out : List String) : Prop :=
  ∀ i : Nat, i < s.length → out[i]? = some (prefixAt s i)

/-- Property 3: every element of the result is a prefix of the input. -/
def allPrefixes_prefix_prop (s : String) (out : List String) : Prop :=
  ∀ p ∈ out, p.toList <+: s.toList

theorem allPrefixes_length_thm (s : String) :
    allPrefixes_length_prop s (allPrefixes s) := by
  simp [allPrefixes_length_prop, allPrefixes]

theorem allPrefixes_elem_thm (s : String) :
    allPrefixes_elem_prop s (allPrefixes s) := by
  intro i hi
  simp [allPrefixes, hi]

theorem allPrefixes_prefix_thm (s : String) :
    allPrefixes_prefix_prop s (allPrefixes s) := by
  intro p hp
  simp [allPrefixes, List.mem_map, List.mem_range] at hp
  obtain ⟨i, -, rfl⟩ := hp
  exact List.take_prefix _ _

/-- Post-condition: the conjunction of the three properties above. -/
def Post_prop (s : String) (out : List String) : Prop :=
  allPrefixes_length_prop s out ∧
  allPrefixes_elem_prop s out ∧
  allPrefixes_prefix_prop s out

-- ## Property-based tests

/-- Executable Boolean form of the length property. -/
def lengthPropBool (s : String) : Bool :=
  (allPrefixes s).length == s.length

/-- Executable Boolean form of the element property. -/
def elemPropBool (s : String) : Bool :=
  (List.range s.length).all fun i =>
    (allPrefixes s)[i]? == some (prefixAt s i)

/-- Executable Boolean form of the prefix property. -/
def prefixPropBool (s : String) : Bool :=
  (allPrefixes s).all fun p => p.toList.isPrefixOf s.toList

/-- Executable Boolean form of the whole post-condition. -/
def postPropBool (s : String) : Bool :=
  lengthPropBool s && elemPropBool s && prefixPropBool s

/-- Test strings for the bounded (exhaustive small-case) PBTs. -/
def pbtStrings : List String :=
  ["", "a", "ab", "abc", "asdfgh", "WWW", "hello world", "lean 4", "λx→x"]

-- Randomized PBTs (Plausible samples lists of characters).
#eval Plausible.Testable.check (∀ cs : List Char,
  (allPrefixes (String.mk cs)).length = cs.length)
#eval Plausible.Testable.check (∀ cs : List Char,
  postPropBool (String.mk cs) = true)

-- Bounded PBTs: one for every property and for the post-condition.
example : pbtStrings.all (fun s => lengthPropBool s) = true := by native_decide
example : pbtStrings.all (fun s => elemPropBool s) = true := by native_decide
example : pbtStrings.all (fun s => prefixPropBool s) = true := by native_decide
example : pbtStrings.all (fun s => postPropBool s) = true := by native_decide

/-- Correctness theorem: the pre-condition implies the post-condition. -/
theorem allPrefixes_correct (s : String) :
    Pre s → Post_prop s (allPrefixes s) := by
  intro _
  exact ⟨allPrefixes_length_thm s, allPrefixes_elem_thm s,
    allPrefixes_prefix_thm s⟩

/-- Imperative implementation using `Id.run do` with a mutable
accumulator, mirroring the Python loop. -/
def allPrefixesImp (s : String) : List String := Id.run do
  let mut result : List String := []
  for i in List.range s.length do
    result := result ++ [prefixAt s i]
  return result

-- ## Imperative tests

example : allPrefixesImp "" = [] := by native_decide
example : allPrefixesImp "abc" = ["a", "ab", "abc"] := by native_decide
example : allPrefixesImp "asdfgh" =
    ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide
example : allPrefixesImp "WWW" = ["W", "WW", "WWW"] := by native_decide

#eval allPrefixesImp "abc"  -- expected: ["a", "ab", "abc"]

/-- Auxiliary lemma about the `Id` for-loop: appending `f i` for each
`i` in the iterated list to a mutable accumulator yields
`acc ++ is.map f`. -/
theorem loop_eq (f : Nat → String) (is : List Nat) (acc : List String) :
    (Id.run do
      let mut r := acc
      for i in is do
        r := r ++ [f i]
      return r) = acc ++ is.map f := by
  induction is generalizing acc with
  | nil =>
    show acc = acc ++ List.map f ([] : List Nat)
    exact (List.append_nil acc).symm
  | cons i is ih =>
    have step : (Id.run do
          let mut r := acc
          for i in i :: is do
            r := r ++ [f i]
          return r)
        = (Id.run do
          let mut r := acc ++ [f i]
          for i in is do
            r := r ++ [f i]
          return r) := by
      simp only [forIn, Id.run, Id.bind_eq, Id.pure_eq, List.forIn'_cons]
    exact step.trans (by
      rw [ih]
      simp [List.map_cons, List.append_assoc])

/-- Equivalence theorem: the functional and imperative implementations
agree on every input. -/
theorem allPrefixes_eq_imp (s : String) :
    allPrefixes s = allPrefixesImp s := by
  have h : allPrefixesImp s = [] ++ (List.range s.length).map (prefixAt s) :=
    loop_eq (prefixAt s) (List.range s.length) []
  rw [h]
  simp [allPrefixes]

end humaneval_14_all_prefixes
