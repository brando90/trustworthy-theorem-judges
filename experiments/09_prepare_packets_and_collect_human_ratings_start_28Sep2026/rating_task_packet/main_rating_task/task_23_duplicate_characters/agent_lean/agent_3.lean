import Mathlib

/-!
# Duplicate each character of a string

Lean 4 formalization of the Python program `duplicate_chars`:

```python
def duplicate_chars(s: str) -> str:
    if not pre(s):
        raise ValueError("Input must be a string")
    return ''.join(c * 2 for c in s)
```

* A Python `str` is modelled by a Lean `String`; its characters are the list `s.toList`.
* The Python pre-condition `isinstance(s, str)` holds for every Lean `String`, so `Pre` is
  `True`.  The negative test (`candidate(None)` raises `ValueError`) is excluded by Lean's type
  system: a non-string cannot be passed to `duplicateChars`.
* `''.join(c * 2 for c in s)` is modelled functionally by duplicating every element of the
  character list, and imperatively by a `for` loop that pushes every character twice.
-/

namespace «41_duplicate_chars»

/-! ## Functional implementation -/

/-- Duplicate every element of a list of characters: `[a, b] ↦ [a, a, b, b]`. -/
def dupChars : List Char → List Char
  | [] => []
  | c :: cs => c :: c :: dupChars cs

/-- Functional implementation of the Python `duplicate_chars`: every character of `s` is
duplicated, in order.  `"abc" ↦ "aabbcc"`. -/
def duplicateChars (s : String) : String :=
  String.mk (dupChars s.toList)

/-! ## Unit tests (mirroring the Python doctests and `check`) -/

example : duplicateChars "abc" = "aabbcc" := by native_decide
example : duplicateChars "" = "" := by native_decide
example : duplicateChars "!a " = "!!aa  " := by native_decide
example : duplicateChars "a" = "aa" := by native_decide
example : duplicateChars "hello world" = "hheelllloo  wwoorrlldd" := by native_decide

#eval duplicateChars "abc"        -- "aabbcc"
#eval duplicateChars ""           -- ""
#eval duplicateChars "!a "        -- "!!aa  "

/-! ## Pre-condition -/

/-- Python `pre(s)` is `isinstance(s, str)`.  Every Lean `String` is a string, so the
pre-condition is always satisfied. -/
def Pre (_s : String) : Prop := True

/-! ## Helper lemmas about `dupChars` -/

theorem dupChars_nil : dupChars [] = [] := rfl

theorem dupChars_cons (c : Char) (cs : List Char) :
    dupChars (c :: cs) = c :: c :: dupChars cs := rfl

theorem dupChars_eq_flatMap (cs : List Char) :
    dupChars cs = cs.flatMap (fun c => [c, c]) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [dupChars, ih]

theorem length_dupChars (cs : List Char) : (dupChars cs).length = 2 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [dupChars, ih]; omega

theorem dupChars_append (xs ys : List Char) :
    dupChars (xs ++ ys) = dupChars xs ++ dupChars ys := by
  induction xs with
  | nil => rfl
  | cons c cs ih => simp [dupChars, ih]

theorem mem_dupChars (cs : List Char) (c : Char) : c ∈ dupChars cs ↔ c ∈ cs := by
  induction cs with
  | nil => simp [dupChars]
  | cons d cs ih => simp [dupChars, ih]

theorem count_dupChars (cs : List Char) (c : Char) :
    (dupChars cs).count c = 2 * cs.count c := by
  induction cs with
  | nil => rfl
  | cons d cs ih =>
    simp only [dupChars, List.count_cons, ih]
    split <;> omega

theorem getElem?_dupChars_two_mul (cs : List Char) (i : Nat) :
    (dupChars cs)[2 * i]? = cs[i]? := by
  induction cs generalizing i with
  | nil => simp [dupChars]
  | cons c cs ih =>
    cases i with
    | zero => simp [dupChars]
    | succ i =>
      have h : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
      rw [h]
      simp [dupChars, ih]

theorem getElem?_dupChars_two_mul_add_one (cs : List Char) (i : Nat) :
    (dupChars cs)[2 * i + 1]? = cs[i]? := by
  induction cs generalizing i with
  | nil => simp [dupChars]
  | cons c cs ih =>
    cases i with
    | zero => simp [dupChars]
    | succ i =>
      have h : 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 := by omega
      rw [h]
      simp [dupChars, ih]

theorem dupChars_eq_nil_iff (cs : List Char) : dupChars cs = [] ↔ cs = [] := by
  cases cs <;> simp [dupChars]

theorem dupChars_injective : Function.Injective dupChars := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons d ds => simp [dupChars] at h
  | cons c cs ih =>
    intro ys h
    cases ys with
    | nil => simp [dupChars] at h
    | cons d ds =>
      simp only [dupChars, List.cons.injEq] at h
      obtain ⟨rfl, -, h⟩ := h
      rw [ih h]

/-- Characters of the result, as a list. -/
theorem toList_duplicateChars (s : String) :
    (duplicateChars s).toList = dupChars s.toList := rfl

/-! ## Properties -/

/-- The result has exactly twice as many characters as the input. -/
def length_prop (s : String) : Prop :=
  (duplicateChars s).length = 2 * s.length

theorem length_thm (s : String) : length_prop s := by
  unfold length_prop duplicateChars
  obtain ⟨l⟩ := s
  simp [String.toList, String.length_mk, length_dupChars]

/-- The characters of the result are obtained by replacing every character `c` of the input
by `[c, c]` (the direct reading of `''.join(c * 2 for c in s)`). -/
def flatMap_prop (s : String) : Prop :=
  (duplicateChars s).toList = s.toList.flatMap (fun c => [c, c])

theorem flatMap_thm (s : String) : flatMap_prop s := by
  unfold flatMap_prop
  rw [toList_duplicateChars, dupChars_eq_flatMap]

/-- Literal reading of the Python expression `''.join(c * 2 for c in s)`:
the result is the concatenation of the strings `c * 2` (= `String.replicate 2 c`). -/
def join_prop (s : String) : Prop :=
  duplicateChars s = String.join (s.toList.map (fun c => String.replicate 2 c))

theorem join_thm (s : String) : join_prop s := by
  unfold join_prop duplicateChars
  rw [String.join_eq]
  apply String.ext
  simp only
  obtain ⟨l⟩ := s
  simp only [String.toList]
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp [dupChars, String.replicate, ih]

/-- Positional characterisation: the characters at positions `2 * i` and `2 * i + 1` of the
result are both the character at position `i` of the input (and all three are absent together
when `i` is out of range). -/
def index_prop (s : String) : Prop :=
  ∀ i : Nat, (duplicateChars s).toList[2 * i]? = s.toList[i]? ∧
    (duplicateChars s).toList[2 * i + 1]? = s.toList[i]?

theorem index_thm (s : String) : index_prop s := by
  intro i
  rw [toList_duplicateChars]
  exact ⟨getElem?_dupChars_two_mul _ _, getElem?_dupChars_two_mul_add_one _ _⟩

/-- Consecutive characters of the result come in equal pairs. -/
def pairs_prop (s : String) : Prop :=
  ∀ i : Nat, (duplicateChars s).toList[2 * i]? = (duplicateChars s).toList[2 * i + 1]?

theorem pairs_thm (s : String) : pairs_prop s := by
  intro i
  obtain ⟨h₁, h₂⟩ := index_thm s i
  rw [h₁, h₂]

/-- The result is empty exactly when the input is empty. -/
def empty_prop (s : String) : Prop :=
  duplicateChars s = "" ↔ s = ""

theorem empty_thm (s : String) : empty_prop s := by
  unfold empty_prop duplicateChars
  obtain ⟨l⟩ := s
  rw [String.ext_iff, String.ext_iff]
  simp [String.toList, dupChars_eq_nil_iff]

/-- Duplication distributes over concatenation. -/
def append_prop (s t : String) : Prop :=
  duplicateChars (s ++ t) = duplicateChars s ++ duplicateChars t

theorem append_thm (s t : String) : append_prop s t := by
  unfold append_prop duplicateChars
  apply String.ext
  simp [String.toList, String.data_append, dupChars_append]

/-- A character occurs in the result iff it occurs in the input. -/
def mem_prop (s : String) : Prop :=
  ∀ c : Char, c ∈ (duplicateChars s).toList ↔ c ∈ s.toList

theorem mem_thm (s : String) : mem_prop s := by
  intro c
  rw [toList_duplicateChars, mem_dupChars]

/-- Every character occurs exactly twice as often in the result as in the input. -/
def count_prop (s : String) : Prop :=
  ∀ c : Char, (duplicateChars s).toList.count c = 2 * s.toList.count c

theorem count_thm (s : String) : count_prop s := by
  intro c
  rw [toList_duplicateChars, count_dupChars]

/-- Duplication is injective: equal outputs come from equal inputs. -/
def injective_prop (s t : String) : Prop :=
  duplicateChars s = duplicateChars t → s = t

theorem injective_thm (s t : String) : injective_prop s t := by
  intro h
  unfold duplicateChars at h
  rw [String.ext_iff] at h
  simp only at h
  apply String.ext
  exact dupChars_injective h

/-! ## Post-condition -/

/-- Post-condition of `duplicate_chars`: conjunction of all the properties above. -/
def Post_prop (s : String) : Prop :=
  length_prop s ∧ flatMap_prop s ∧ join_prop s ∧ index_prop s ∧ pairs_prop s ∧
    empty_prop s ∧ mem_prop s ∧ count_prop s ∧
    (∀ t : String, append_prop s t) ∧ (∀ t : String, injective_prop s t)

/-! ## Property-based tests

Executable Boolean forms of the properties above, checked on random strings by Plausible and
exhaustively on a fixed list of sample strings. -/

/-- Sample inputs for the bounded property-based tests. -/
def samples : List String :=
  ["", "a", "ab", "abc", "!a ", "hello world", "aa", "xyzzy", "αβγ", "日本語", "a b c"]

/-- Executable form of `length_prop`. -/
def lengthCheck (s : String) : Bool :=
  (duplicateChars s).length == 2 * s.length

/-- Executable form of `flatMap_prop`. -/
def flatMapCheck (s : String) : Bool :=
  (duplicateChars s).toList == s.toList.flatMap (fun c => [c, c])

/-- Executable form of `join_prop`. -/
def joinCheck (s : String) : Bool :=
  duplicateChars s == String.join (s.toList.map (fun c => String.replicate 2 c))

/-- Executable form of `index_prop`, checked for every `i < s.length + 3`
(indices beyond the length exercise the out-of-range case). -/
def indexCheck (s : String) : Bool :=
  (List.range (s.length + 3)).all fun i =>
    (duplicateChars s).toList[2 * i]? == s.toList[i]? &&
    (duplicateChars s).toList[2 * i + 1]? == s.toList[i]?

/-- Executable form of `pairs_prop`, checked for every `i < s.length + 3`. -/
def pairsCheck (s : String) : Bool :=
  (List.range (s.length + 3)).all fun i =>
    (duplicateChars s).toList[2 * i]? == (duplicateChars s).toList[2 * i + 1]?

/-- Executable form of `empty_prop`. -/
def emptyCheck (s : String) : Bool :=
  (duplicateChars s == "") == (s == "")

/-- Executable form of `append_prop`. -/
def appendCheck (s t : String) : Bool :=
  duplicateChars (s ++ t) == duplicateChars s ++ duplicateChars t

/-- Executable form of `mem_prop` (both inclusions, over the characters of either string). -/
def memCheck (s : String) : Bool :=
  (duplicateChars s).toList.all (fun c => decide (c ∈ s.toList)) &&
  s.toList.all (fun c => decide (c ∈ (duplicateChars s).toList))

/-- Executable form of `count_prop` for a given character. -/
def countCheck (s : String) (c : Char) : Bool :=
  (duplicateChars s).toList.count c == 2 * s.toList.count c

/-- Executable form of `injective_prop`. -/
def injectiveCheck (s t : String) : Bool :=
  !(duplicateChars s == duplicateChars t) || (s == t)

/-- Executable form of `Post_prop` (the two-argument properties are checked against `t`,
`count_prop` against every character of `s ++ t`). -/
def postCheck (s t : String) : Bool :=
  lengthCheck s && flatMapCheck s && joinCheck s && indexCheck s && pairsCheck s &&
  emptyCheck s && memCheck s && (s ++ t).toList.all (countCheck s) &&
  appendCheck s t && injectiveCheck s t

-- Randomized PBTs (Plausible samples random strings / characters).
#eval Plausible.Testable.check (∀ s : String, lengthCheck s = true)
#eval Plausible.Testable.check (∀ s : String, (duplicateChars s).length = 2 * s.length)
#eval Plausible.Testable.check (∀ s : String, flatMapCheck s = true)
#eval Plausible.Testable.check
  (∀ s : String, (duplicateChars s).toList = s.toList.flatMap (fun c => [c, c]))
#eval Plausible.Testable.check (∀ s : String, joinCheck s = true)
#eval Plausible.Testable.check (∀ s : String, indexCheck s = true)
#eval Plausible.Testable.check (∀ s : String, pairsCheck s = true)
#eval Plausible.Testable.check (∀ s : String, emptyCheck s = true)
#eval Plausible.Testable.check (∀ s t : String, appendCheck s t = true)
#eval Plausible.Testable.check
  (∀ s t : String, duplicateChars (s ++ t) = duplicateChars s ++ duplicateChars t)
#eval Plausible.Testable.check (∀ s : String, memCheck s = true)
#eval Plausible.Testable.check
  (∀ (s : String) (c : Char), c ∈ (duplicateChars s).toList ↔ c ∈ s.toList)
#eval Plausible.Testable.check (∀ (s : String) (c : Char), countCheck s c = true)
#eval Plausible.Testable.check
  (∀ (s : String) (c : Char), (duplicateChars s).toList.count c = 2 * s.toList.count c)
#eval Plausible.Testable.check (∀ s t : String, injectiveCheck s t = true)
#eval Plausible.Testable.check (∀ s : String, injectiveCheck s s = true)
#eval Plausible.Testable.check (∀ s t : String, postCheck s t = true)

-- Bounded (exhaustive on `samples`) PBTs.
example : samples.all lengthCheck = true := by native_decide
example : samples.all flatMapCheck = true := by native_decide
example : samples.all joinCheck = true := by native_decide
example : samples.all indexCheck = true := by native_decide
example : samples.all pairsCheck = true := by native_decide
example : samples.all emptyCheck = true := by native_decide
example : samples.all (fun s => samples.all (appendCheck s)) = true := by native_decide
example : samples.all memCheck = true := by native_decide
example : samples.all (fun s => (s ++ "qz").toList.all (countCheck s)) = true := by native_decide
example : samples.all (fun s => samples.all (injectiveCheck s)) = true := by native_decide
example : samples.all (fun s => samples.all (postCheck s)) = true := by native_decide

/-! ## Correctness theorem: `Pre → Post` -/

theorem correctness (s : String) (_h : Pre s) : Post_prop s :=
  ⟨length_thm s, flatMap_thm s, join_thm s, index_thm s, pairs_thm s, empty_thm s, mem_thm s,
    count_thm s, fun t => append_thm s t, fun t => injective_thm s t⟩

/-! ## Imperative implementation -/

/-- Imperative implementation: iterate over the characters and push each one twice onto a
mutable output string (the loop form of `''.join(c * 2 for c in s)`). -/
def duplicateCharsImp (s : String) : String := Id.run do
  let mut out : String := ""
  for c in s.toList do
    out := out.push c
    out := out.push c
  return out

/-! ## Imperative tests -/

example : duplicateCharsImp "abc" = "aabbcc" := by native_decide
example : duplicateCharsImp "" = "" := by native_decide
example : duplicateCharsImp "!a " = "!!aa  " := by native_decide
example : duplicateCharsImp "hello world" = "hheelllloo  wwoorrlldd" := by native_decide
example : samples.all (fun s => duplicateCharsImp s == duplicateChars s) = true := by
  native_decide

#eval duplicateCharsImp "abc"     -- "aabbcc"
#eval duplicateCharsImp ""        -- ""
#eval duplicateCharsImp "!a "     -- "!!aa  "
#eval Plausible.Testable.check (∀ s : String, duplicateCharsImp s = duplicateChars s)

/-! ## Equivalence: functional = imperative -/

/-- Loop invariant: folding the "push twice" step over `cs` starting from `acc` appends the
duplicated characters of `cs` to `acc`. -/
theorem foldl_push_twice (cs : List Char) (acc : String) :
    List.foldl (fun (out : String) (c : Char) => (out.push c).push c) acc cs =
      acc ++ String.mk (dupChars cs) := by
  induction cs generalizing acc with
  | nil =>
    apply String.ext
    simp [dupChars]
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    apply String.ext
    simp [dupChars, String.data_append, String.data_push]

theorem duplicateCharsImp_eq_foldl (s : String) :
    duplicateCharsImp s =
      List.foldl (fun (out : String) (c : Char) => (out.push c).push c) "" s.toList := by
  unfold duplicateCharsImp
  simp

theorem duplicateCharsImp_eq_duplicateChars (s : String) :
    duplicateCharsImp s = duplicateChars s := by
  rw [duplicateCharsImp_eq_foldl, foldl_push_twice, String.empty_append]
  rfl

end «41_duplicate_chars»
