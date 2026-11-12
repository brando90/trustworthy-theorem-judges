import Mathlib

/-!
# Duplicate each character in the input string

Lean 4 translation of the Python program `duplicate_chars`:

```python
def duplicate_chars(s: str) -> str:
    if not pre(s):
        raise ValueError("Input must be a string")
    return ''.join(c * 2 for c in s)
```

Every character of the input string is written twice, in the original order.
The empty string is mapped to the empty string.  The Python pre-condition
`pre(s) = isinstance(s, str)` is guaranteed by the Lean type `String`, so `Pre`
is trivially true; the Python negative test (`None` input raises `ValueError`)
is modelled separately by `duplicateCharsChecked : Option String → Except String String`.
-/

namespace «41_duplicate_chars»

/-! ## Functional implementation -/

/-- Duplicate every element of a list of characters: `[a, b, c] ↦ [a, a, b, b, c, c]`. -/
def dupList : List Char → List Char
  | [] => []
  | c :: cs => c :: c :: dupList cs

/-- `duplicateChars s` is the string in which every character of `s` appears twice,
in the original order (Python `''.join(c * 2 for c in s)`). -/
def duplicateChars (s : String) : String :=
  String.mk (dupList s.toList)

/-- Python-level entry point whose argument may be `None` (modelled by `Option String`).
`none` corresponds to the `ValueError("Input must be a string")` raised by Python. -/
def duplicateCharsChecked : Option String → Except String String
  | none => .error "Input must be a string"
  | some s => .ok (duplicateChars s)

/-! ## Unit tests -/

example : duplicateChars "abc" = "aabbcc" := by native_decide
example : duplicateChars "" = "" := by native_decide
example : duplicateChars "!a " = "!!aa  " := by native_decide
example : duplicateChars "a" = "aa" := by native_decide
example : duplicateChars "hello" = "hheelllloo" := by native_decide
example : (duplicateCharsChecked (some "abc") matches .ok "aabbcc") = true := by native_decide
example : (duplicateCharsChecked (some "") matches .ok "") = true := by native_decide
-- Negative test: `None` input raises `ValueError`.
example : (duplicateCharsChecked none matches .error _) = true := by native_decide

#eval duplicateChars "abc"      -- "aabbcc"
#eval duplicateChars ""         -- ""
#eval duplicateChars "!a "      -- "!!aa  "
#eval duplicateCharsChecked none
#eval duplicateCharsChecked (some "abc")

/-! ## Pre-condition -/

/-- Python: `pre(s) = isinstance(s, str)`.  Every Lean `String` is a string, so the
pre-condition always holds. -/
def Pre (_s : String) : Prop := True

theorem Pre_always (s : String) : Pre s := trivial

/-! ## Lemmas about `dupList` -/

@[simp] theorem dupList_nil : dupList [] = [] := rfl

@[simp] theorem dupList_cons (c : Char) (cs : List Char) :
    dupList (c :: cs) = c :: c :: dupList cs := rfl

theorem dupList_eq_flatMap (cs : List Char) : dupList cs = cs.flatMap (fun c => [c, c]) := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

theorem dupList_length (cs : List Char) : (dupList cs).length = 2 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]; omega

theorem dupList_append (xs ys : List Char) : dupList (xs ++ ys) = dupList xs ++ dupList ys := by
  induction xs with
  | nil => simp
  | cons c cs ih => simp [ih]

theorem dupList_mem (cs : List Char) (c : Char) : c ∈ dupList cs ↔ c ∈ cs := by
  induction cs with
  | nil => simp
  | cons d cs ih =>
    simp only [dupList_cons, List.mem_cons, ih]
    tauto

theorem dupList_count (cs : List Char) (c : Char) : (dupList cs).count c = 2 * cs.count c := by
  induction cs with
  | nil => simp
  | cons d cs ih =>
    simp only [dupList_cons, List.count_cons, ih]
    split <;> omega

theorem dupList_getElem? (cs : List Char) (i : Nat) :
    (dupList cs)[2 * i]? = cs[i]? ∧ (dupList cs)[2 * i + 1]? = cs[i]? := by
  induction cs generalizing i with
  | nil => simp
  | cons c cs ih =>
    cases i with
    | zero => simp
    | succ j =>
      have h1 : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
      rw [h1]
      simp only [dupList_cons, List.getElem?_cons_succ]
      exact ih j

theorem dupList_injective : Function.Injective dupList := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons d ds => simp at h
  | cons c cs ih =>
    intro ys h
    cases ys with
    | nil => simp at h
    | cons d ds =>
      simp only [dupList_cons, List.cons.injEq] at h
      obtain ⟨h1, -, h3⟩ := h
      rw [h1, ih h3]

/-! ## Properties -/

/-- The result has exactly twice as many characters as the input. -/
def length_prop (s : String) : Prop :=
  (duplicateChars s).length = 2 * s.length

theorem length_thm (s : String) : length_prop s := by
  unfold length_prop duplicateChars
  simp [dupList_length]

/-- The characters of the result are those of the input, each repeated twice in order
(`''.join(c * 2 for c in s)`). -/
def toList_prop (s : String) : Prop :=
  (duplicateChars s).toList = s.toList.flatMap (fun c => [c, c])

theorem toList_thm (s : String) : toList_prop s := by
  unfold toList_prop duplicateChars
  simp [dupList_eq_flatMap]

/-- Edge case: the empty string is mapped to the empty string. -/
def empty_prop : Prop := duplicateChars "" = ""

theorem empty_thm : empty_prop := by
  unfold empty_prop duplicateChars
  rfl

/-- Duplication distributes over string concatenation. -/
def append_prop (s t : String) : Prop :=
  duplicateChars (s ++ t) = duplicateChars s ++ duplicateChars t

theorem append_thm (s t : String) : append_prop s t := by
  unfold append_prop duplicateChars
  apply String.ext
  simp [dupList_append]

/-- A single character `c` is mapped to `cc` (Python `c * 2`). -/
def singleton_prop (c : Char) : Prop :=
  duplicateChars (String.singleton c) = String.mk [c, c]

theorem singleton_thm (c : Char) : singleton_prop c := by
  unfold singleton_prop duplicateChars
  rfl

/-- The result contains exactly the same characters as the input. -/
def mem_prop (s : String) : Prop :=
  ∀ c : Char, c ∈ (duplicateChars s).toList ↔ c ∈ s.toList

theorem mem_thm (s : String) : mem_prop s := by
  intro c
  unfold duplicateChars
  simp [dupList_mem]

/-- Every character occurs exactly twice as often in the result as in the input. -/
def count_prop (s : String) (c : Char) : Prop :=
  (duplicateChars s).toList.count c = 2 * s.toList.count c

theorem count_thm (s : String) (c : Char) : count_prop s c := by
  unfold count_prop duplicateChars
  simp [dupList_count]

/-- Positions `2*i` and `2*i+1` of the result both hold character `i` of the input
(and are out of range exactly when `i` is out of range). -/
def index_prop (s : String) : Prop :=
  ∀ i : Nat, (duplicateChars s).toList[2 * i]? = s.toList[i]? ∧
    (duplicateChars s).toList[2 * i + 1]? = s.toList[i]?

theorem index_thm (s : String) : index_prop s := by
  intro i
  unfold duplicateChars
  simpa using dupList_getElem? s.toList i

/-- Duplication is injective: the input can be recovered from the output. -/
def injective_prop : Prop :=
  ∀ s t : String, duplicateChars s = duplicateChars t → s = t

theorem injective_thm : injective_prop := by
  intro s t h
  unfold duplicateChars at h
  apply String.ext
  have h' : dupList s.toList = dupList t.toList := by
    simpa [String.ext_iff] using h
  simpa using dupList_injective h'

/-! ## Post-condition -/

/-- Post-condition relating an input `s` to the returned string `r`. -/
def Post_prop (s r : String) : Prop :=
  r.length = 2 * s.length ∧
  r.toList = s.toList.flatMap (fun c => [c, c]) ∧
  (∀ c : Char, c ∈ r.toList ↔ c ∈ s.toList) ∧
  (∀ c : Char, r.toList.count c = 2 * s.toList.count c) ∧
  (∀ i : Nat, r.toList[2 * i]? = s.toList[i]? ∧ r.toList[2 * i + 1]? = s.toList[i]?)

/-! ## Property-based tests -/

/-- Executable (Boolean) form of `Post_prop`; the index conjunct is checked for all
`i ≤ s.length + 1`, which covers every in-range and the first out-of-range indices. -/
def postCheck (s r : String) : Bool :=
  (r.length == 2 * s.length) &&
  (r.toList == s.toList.flatMap (fun c => [c, c])) &&
  r.toList.all (fun c => c ∈ s.toList) &&
  s.toList.all (fun c => c ∈ r.toList) &&
  (r.toList ++ s.toList).all (fun c => r.toList.count c == 2 * s.toList.count c) &&
  (List.range (s.length + 2)).all (fun i =>
    r.toList[2 * i]? == s.toList[i]? && r.toList[2 * i + 1]? == s.toList[i]?)

-- length_prop
#eval Plausible.Testable.check (∀ s : String, (duplicateChars s).length = 2 * s.length)
-- toList_prop
#eval Plausible.Testable.check
  (∀ s : String, (duplicateChars s).toList = s.toList.flatMap (fun c => [c, c]))
-- append_prop
#eval Plausible.Testable.check
  (∀ s t : String, duplicateChars (s ++ t) = duplicateChars s ++ duplicateChars t)
-- singleton_prop
#eval Plausible.Testable.check (∀ c : Char, duplicateChars (String.singleton c) = String.mk [c, c])
-- mem_prop
#eval Plausible.Testable.check
  (∀ s : String, ((duplicateChars s).toList.all (fun c => c ∈ s.toList) &&
    s.toList.all (fun c => c ∈ (duplicateChars s).toList)) = true)
-- count_prop
#eval Plausible.Testable.check
  (∀ s : String, ∀ c : Char, (duplicateChars s).toList.count c = 2 * s.toList.count c)
-- index_prop
#eval Plausible.Testable.check
  (∀ s : String, ∀ i : Nat, (duplicateChars s).toList[2 * i]? = s.toList[i]? ∧
    (duplicateChars s).toList[2 * i + 1]? = s.toList[i]?)
-- injective_prop (stated as an equivalence so that no sample is discarded)
#eval Plausible.Testable.check
  (∀ s t : String, duplicateChars s = duplicateChars t ↔ s = t)
-- Post_prop
#eval Plausible.Testable.check (∀ s : String, postCheck s (duplicateChars s) = true)

/-- Fixed sample inputs for exhaustive bounded checks. -/
def sampleStrings : List String :=
  ["", "a", "ab", "abc", "!a ", "aaa", "hello world", "Lean 4", "xyzxyz", "ünï", "  ", "aabbcc"]

-- empty_prop
example : duplicateChars "" = "" := by native_decide
-- length_prop, toList_prop, Post_prop on fixed samples
example : sampleStrings.all (fun s => (duplicateChars s).length == 2 * s.length) = true := by
  native_decide
example : sampleStrings.all
    (fun s => (duplicateChars s).toList == s.toList.flatMap (fun c => [c, c])) = true := by
  native_decide
example : sampleStrings.all (fun s => postCheck s (duplicateChars s)) = true := by native_decide
-- append_prop on all pairs of samples
example : (sampleStrings.product sampleStrings).all
    (fun p => duplicateChars (p.1 ++ p.2) == duplicateChars p.1 ++ duplicateChars p.2) = true := by
  native_decide
-- injective_prop on all pairs of samples
example : (sampleStrings.product sampleStrings).all
    (fun p => (duplicateChars p.1 == duplicateChars p.2) == (p.1 == p.2)) = true := by
  native_decide
-- singleton_prop on a range of characters
example : (List.range 128).all (fun n =>
    let c := Char.ofNat n
    duplicateChars (String.singleton c) == String.mk [c, c]) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem duplicateChars_correct (s : String) (_hpre : Pre s) : Post_prop s (duplicateChars s) :=
  ⟨length_thm s, toList_thm s, mem_thm s, fun c => count_thm s c, index_thm s⟩

/-! ## Imperative implementation -/

/-- Imperative version: walk over the characters, pushing each one twice onto a mutable
output string. -/
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
example : duplicateCharsImp "hello" = "hheelllloo" := by native_decide
#eval duplicateCharsImp "abc"
#eval duplicateCharsImp "!a "
#eval Plausible.Testable.check (∀ s : String, duplicateCharsImp s = duplicateChars s)
example : sampleStrings.all (fun s => duplicateCharsImp s == duplicateChars s) = true := by
  native_decide

/-! ## Equivalence theorem -/

/-- The `for` loop of `duplicateCharsImp` (in the `Id` monad), started from accumulator
`acc`, appends the duplicated characters to `acc`. -/
theorem duplicateCharsImp_loop (cs : List Char) (acc : String) :
    forIn (m := Id) cs acc (fun c out => ForInStep.yield ((out.push c).push c)) =
      acc ++ String.mk (dupList cs) := by
  induction cs generalizing acc with
  | nil =>
    rw [List.forIn_nil]
    show acc = _
    apply String.ext
    simp
  | cons c cs ih =>
    rw [List.forIn_cons]
    show forIn (m := Id) cs ((acc.push c).push c) _ = _
    rw [ih]
    apply String.ext
    simp

/-- The imperative implementation agrees with the functional one on every input. -/
theorem duplicateCharsImp_eq (s : String) : duplicateCharsImp s = duplicateChars s := by
  show forIn (m := Id) s.toList "" (fun c out => ForInStep.yield ((out.push c).push c)) = _
  rw [duplicateCharsImp_loop]
  apply String.ext
  simp [duplicateChars]

end «41_duplicate_chars»
