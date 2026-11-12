import Mathlib

/-!
# 41_duplicate_chars - Duplicate each character in the input string

Formalization of the Python program

```
def pre(s: str) -> bool:
    return isinstance(s, str)

def duplicate_chars(s: str) -> str:
    if not pre(s):
        raise ValueError("Input must be a string")
    return ''.join(c * 2 for c in s)
```

`duplicate_chars` returns a new string in which every character of the input occurs twice,
in the original order:

* `duplicate_chars("abc") == "aabbcc"`
* `duplicate_chars("") == ""` (the empty string is a fixed point)
* `duplicate_chars("!a ") == "!!aa  "` (punctuation and blanks are duplicated too)
* `duplicate_chars(None)` raises `ValueError("Input must be a string")`

## Modelling choices

* `dupList : List Char -> List Char` is the character-list kernel of
  `''.join(c * 2 for c in s)`; `duplicateChars : String -> String` is the program itself.
* Python's `pre` is a *dynamic* type test. In Lean a `String` argument is a string by
  typing, so in order to keep the observable behaviour of the guard - in particular the
  `ValueError` exercised by the negative test - the Python argument is modelled as
  `Option String`: `some s` stands for the Python `str` `s`, `none` stands for any
  non-string value such as `None`. `Pre` is exactly `isinstance(s, str)`, and
  `duplicateCharsPy` is the exception-raising Python function, with result type
  `Except String String`.
* `Post_prop` is the conjunction of the observable properties of the result and
  `correctness_thm` proves `Pre x -> Post_prop x (duplicateCharsPy x)`.
* `duplicateCharsImp` is an imperative re-implementation (`Id.run do` with a mutable
  `Array Char` buffer and a `for` loop); `equivalence_thm` proves that it computes the
  same string as the functional implementation.

Every theorem below is discharged by kernel-checked tactics (`rfl`, `simp`, `omega`,
induction). `native_decide` appears only in `example` unit tests and property-based tests.
-/

namespace DuplicateChars41

open String List

/-! ## Functional implementation -/

/-- The character-list kernel of `''.join(c * 2 for c in s)`: every character is emitted twice. -/
def dupList : List Char -> List Char
  | []        => []
  | (c :: cs) => c :: c :: dupList cs

@[simp] theorem dupList_nil : dupList [] = [] := rfl

@[simp] theorem dupList_cons (c : Char) (cs : List Char) :
    dupList (c :: cs) = c :: c :: dupList cs := rfl

/-- `duplicate_chars(s)`: a new string where each character from the input string is duplicated. -/
def duplicateChars (s : String) : String := String.mk (dupList s.toList)

/-! ## Unit tests (fixed examples, mirroring the Python doctests and `check`) -/

example : duplicateChars "abc" = "aabbcc" := by native_decide
example : duplicateChars "" = "" := by native_decide
example : duplicateChars "!a " = "!!aa  " := by native_decide
example : duplicateChars "a" = "aa" := by native_decide
example : duplicateChars "Lean 4" = "LLeeaann  44" := by native_decide
example : (duplicateChars "abc").length = 6 := by native_decide

#eval duplicateChars "abc"        -- "aabbcc"
#eval duplicateChars ""           -- ""
#eval duplicateChars "!a "        -- "!!aa  "
#eval duplicateChars "Lean 4"     -- "LLeeaann  44"
#eval (duplicateChars "abc").length

/-! ## Pre-condition -/

/-- The message carried by the `ValueError` that the Python guard raises. -/
def valueError : String := "Input must be a string"

/-- `pre(s) == isinstance(s, str)`.

The Python argument is modelled as `Option String`: `some s` is the Python string `s`,
`none` is a non-string value such as `None`. `Pre` holds exactly for the `str` arguments,
so `Pre` fails precisely when the Python program raises `ValueError`. -/
def Pre : Option String -> Prop
  | .some _ => True
  | .none   => False

/-- Executable Boolean form of `Pre`. -/
def preCheck (x : Option String) : Bool :=
  match x with
  | .some _ => true
  | .none   => false

theorem Pre_some (s : String) : Pre (some s) := trivial

theorem not_Pre_none : ¬ Pre (none : Option String) := fun h => h

theorem preCheck_spec (x : Option String) : preCheck x = x.isSome := by
  cases x <;> rfl

/-- `duplicate_chars` with its Python guard: a non-string argument raises `ValueError`. -/
def duplicateCharsPy : Option String -> Except String String
  | .some s => .ok (duplicateChars s)
  | .none   => .error valueError

/-! ## Auxiliary lemmas about the character-list kernel -/

theorem dupList_length : ∀ cs : List Char, (dupList cs).length = 2 * cs.length := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]; omega

theorem dupList_append : ∀ cs ts : List Char, dupList (cs ++ ts) = dupList cs ++ dupList ts := by
  intro cs
  induction cs with
  | nil => intro ts; rfl
  | cons c cs ih => intro ts; simp [ih]

/-- `dupList` really is `''.join(c * 2 for c in s)` at the character level. -/
theorem dupList_flatMap : ∀ cs : List Char, dupList cs = cs.flatMap (fun c => [c, c]) := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]

/-- Character-wise specification: the `i`-th input character occupies positions `2*i` and
`2*i+1` of the output. -/
theorem dupList_get : ∀ cs : List Char, ∀ i : Nat, i < cs.length →
    (dupList cs)[2 * i]? = cs[i]? ∧ (dupList cs)[2 * i + 1]? = cs[i]? := by
  intro cs
  induction cs with
  | nil => intro i h; simp at h
  | cons c cs ih =>
    intro i h
    rw [List.length_cons] at h
    cases i with
    | zero =>
      constructor
      · show (c :: c :: dupList cs)[0]? = (c :: cs)[0]?
        simp
      · show (c :: c :: dupList cs)[1]? = (c :: cs)[0]?
        simp
    | succ j =>
      have hj : j < cs.length := by omega
      obtain ⟨h1, h2⟩ := ih j hj
      have e1 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      have e2 : 2 * (j + 1) + 1 = ((2 * j + 1) + 1) + 1 := by omega
      constructor
      · show (dupList (c :: cs))[2 * (j + 1)]? = (c :: cs)[j + 1]?
        rw [e1]
        simp [h1]
      · show (dupList (c :: cs))[2 * (j + 1) + 1]? = (c :: cs)[j + 1]?
        rw [e2]
        simp [h2]

theorem dupList_nil_iff : ∀ cs : List Char, dupList cs = [] ↔ cs = [] := by
  intro cs
  constructor
  · intro h
    cases cs with
    | nil => rfl
    | cons c cs' => simp at h
  · intro h; rw [h]; rfl

/-- Duplicating characters neither adds nor removes characters. -/
theorem dupList_mem (c : Char) : ∀ cs : List Char, c ∈ dupList cs ↔ c ∈ cs := by
  intro cs
  induction cs with
  | nil => simp
  | cons d dis ih => simp [ih]

/-- Duplicating characters loses no information: `dupList` is injective. -/
theorem dupList_inj : ∀ {a b : List Char}, dupList a = dupList b → a = b := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons d ds => simp at h
  | cons c cs ih =>
    intro b h
    cases b with
    | nil => simp at h
    | cons d ds =>
      simp at h
      obtain ⟨rfl, htl2⟩ := h
      rw [ih htl2]

/-! ## Properties of the functional implementation -/

/-- Edge case from the Python docstring: the empty string maps to the empty string. -/
def empty_prop : Prop := duplicateChars "" = ""

theorem empty_thm : empty_prop := rfl

/-- Basic doctest: `duplicate_chars("abc") == "aabbcc"`. -/
def abc_prop : Prop := duplicateChars "abc" = "aabbcc"

theorem abc_thm : abc_prop := rfl

/-- Doctest with punctuation and a blank: `duplicate_chars("!a ") == "!!aa  "`. -/
def punct_prop : Prop := duplicateChars "!a " = "!!aa  "

theorem punct_thm : punct_prop := by
  show duplicateChars "!a " = "!!aa  "
  decide

/-- Recursive shape: the head character is emitted twice, then the tail is processed. -/
def cons_prop : Prop := ∀ (c : Char) (cs : List Char),
  duplicateChars (String.mk (c :: cs)) = String.mk (c :: c :: dupList cs)

theorem cons_thm : cons_prop := fun _ _ => rfl

/-- The characters of the result are exactly `dupList` applied to the characters of the input. -/
def toList_prop : Prop := ∀ s : String, (duplicateChars s).toList = dupList s.toList

theorem toList_thm : toList_prop := fun _ => rfl

/-- The result is the join of the doubled characters, i.e. `''.join(c * 2 for c in s)`. -/
def join_prop : Prop :=
  ∀ s : String, (duplicateChars s).toList = s.toList.flatMap (fun c => [c, c])

theorem join_thm : join_prop := fun s => dupList_flatMap s.toList

/-- The output is exactly twice as long as the input. -/
def length_prop : Prop := ∀ s : String, (duplicateChars s).length = 2 * s.length

theorem length_thm : length_prop := by
  intro s
  simp [duplicateChars, dupList_length]

/-- Character-wise specification: position `2*i` and position `2*i+1` of the output both hold
the `i`-th character of the input. -/
def chars_prop : Prop := ∀ (s : String) (i : Nat), i < s.length →
  (duplicateChars s).toList[2 * i]? = s.toList[i]? ∧
  (duplicateChars s).toList[2 * i + 1]? = s.toList[i]?

theorem chars_thm : chars_prop := by
  intro s i h
  have key := dupList_get s.toList i h
  simpa [duplicateChars] using key

/-- Duplicating characters is a string homomorphism (the join in the Python program). -/
def append_prop : Prop :=
  ∀ s t : String, duplicateChars (s ++ t) = duplicateChars s ++ duplicateChars t

theorem append_thm : append_prop := by
  intro s t
  have h2 : ∀ (l1 l2 : List Char), String.mk (l1 ++ l2) = String.mk l1 ++ String.mk l2 :=
    fun _ _ => rfl
  simp [duplicateChars, dupList_append, h2]

/-- The result is empty exactly when the input is empty. -/
def empty_iff_prop : Prop := ∀ s : String, duplicateChars s = "" ↔ s = ""

theorem empty_iff_thm : empty_iff_prop := by
  intro s
  constructor
  · intro h
    have h1 : dupList s.toList = [] := by
      have h2 := congrArg String.toList h
      simpa [duplicateChars] using h2
    have h3 : s.toList = [] := (dupList_nil_iff s.toList).mp h1
    have h4 : s = String.mk s.toList := rfl
    rw [h4, h3]
  · intro h; rw [h]; rfl

/-- Distinct inputs give distinct outputs. -/
def injective_prop : Prop := ∀ s t : String, duplicateChars s = duplicateChars t → s = t

theorem injective_thm : injective_prop := by
  intro s t h
  have h1 : dupList s.toList = dupList t.toList := by
    have h2 := congrArg String.toList h
    simpa [duplicateChars] using h2
  exact String.toList_inj.mp (dupList_inj h1)

/-- `duplicateChars` acts on the character list of its argument through `dupList`. -/
def mk_prop : Prop := ∀ cs : List Char, duplicateChars (String.mk cs) = String.mk (dupList cs)

theorem mk_thm : mk_prop := fun _ => rfl

/-- No character is added or removed: the result contains exactly the characters of the input. -/
def mem_prop : Prop :=
  ∀ (s : String) (c : Char), c ∈ s.toList ↔ c ∈ (duplicateChars s).toList

theorem mem_thm : mem_prop := by
  intro s c
  show c ∈ s.toList ↔ c ∈ dupList s.toList
  exact (dupList_mem c s.toList).symm

/-- Negative test of the Python `check`: a non-string argument raises `ValueError`. -/
def error_prop : Prop := duplicateCharsPy none = .error valueError

theorem error_thm : error_prop := rfl

/-- A string argument is accepted and returned unchanged-wrapped in `.ok`. -/
def ok_prop : Prop := ∀ s : String, duplicateCharsPy (some s) = .ok (duplicateChars s)

theorem ok_thm : ok_prop := fun _ => rfl

/-! ## Post-condition -/

/-- String-level post-condition: the conjunction of everything the Python program guarantees
about the string it returns. -/
def StrPost (s r : String) : Prop :=
  r = duplicateChars s ∧
  r.length = 2 * s.length ∧
  r.toList = dupList s.toList ∧
  r.toList = s.toList.flatMap (fun c => [c, c]) ∧
  (∀ i < s.length, r.toList[2 * i]? = s.toList[i]? ∧ r.toList[2 * i + 1]? = s.toList[i]?) ∧
  (s = "" ↔ r = "") ∧
  (∀ c : Char, c ∈ s.toList ↔ c ∈ r.toList)

theorem strPost_thm (s : String) : StrPost s (duplicateChars s) :=
  ⟨rfl, length_thm s, toList_thm s, join_thm s, chars_thm s, (empty_iff_thm s).symm,
    mem_thm s⟩

/-- Post-condition of the whole Python program: a `str` argument yields `.ok` of the duplicated
string (which satisfies `StrPost`), and a non-string argument yields the `ValueError`. -/
def Post_prop (x : Option String) (res : Except String String) : Prop :=
  (∀ s, x = some s → res = .ok (duplicateChars s) ∧ StrPost s (duplicateChars s)) ∧
  (x = none → res = .error valueError)

/-! ## Property-based tests

Randomized tests use `Plausible`; guarded / implicational properties are tested exhaustively
over a corpus of small strings (`native_decide`), because a random sampler would mostly
"give up" on the guards. -/

/-- A corpus of test strings: empty string, single characters, punctuation, blanks, digits. -/
def samples : List String :=
  ["", "a", "abc", "!a ", "hello world", "Lean 4", "0123456789", "aaa", "   ", "x", "Ab!z"]

/-- The corpus lifted to Python-level arguments, including the illegal (non-string) one. -/
def sampleArgs : List (Option String) := samples.map some ++ [none]

/-- Executable Boolean form of `Post_prop`. -/
def postCheck (x : Option String) : Bool :=
  match x, duplicateCharsPy x with
  | .some s, .ok r =>
      r == duplicateChars s &&
      r.length == 2 * s.length &&
      r.toList == dupList s.toList &&
      r.toList == s.toList.flatMap (fun c => [c, c]) &&
      (List.range s.length).all (fun i =>
        (r.toList[2 * i]? == s.toList[i]?) && (r.toList[2 * i + 1]? == s.toList[i]?)) &&
      decide (s = "" ↔ r = "") &&
      s.toList.all (fun c => decide (c ∈ r.toList)) &&
      r.toList.all (fun c => decide (c ∈ s.toList))
  | .none, .error e => e == valueError
  | _, _ => false

-- PBT for `length_prop`
example : samples.all (fun s => (duplicateChars s).length == 2 * s.length) = true := by
  native_decide
#eval Plausible.Testable.check (∀ s : String, (duplicateChars s).length = 2 * s.length)

-- PBT for `toList_prop`
example : samples.all (fun s => (duplicateChars s).toList == dupList s.toList) = true := by
  native_decide
#eval Plausible.Testable.check (∀ s : String, (duplicateChars s).toList = dupList s.toList)

-- PBT for `join_prop`
example : samples.all (fun s =>
    (duplicateChars s).toList == s.toList.flatMap (fun c => [c, c])) = true := by native_decide
#eval Plausible.Testable.check
  (∀ s : String, (duplicateChars s).toList = s.toList.flatMap (fun c => [c, c]))

-- PBT for `chars_prop` (guarded, hence bounded/exhaustive over the corpus and over all indices)
example : samples.all (fun s => (List.range s.length).all (fun i =>
    decide ((duplicateChars s).toList[2 * i]? = s.toList[i]?) &&
    decide ((duplicateChars s).toList[2 * i + 1]? = s.toList[i]?))) = true := by native_decide
#eval Plausible.Testable.check (∀ s : String, (List.range s.length).all (fun i =>
    decide ((duplicateChars s).toList[2 * i]? = s.toList[i]?) &&
    decide ((duplicateChars s).toList[2 * i + 1]? = s.toList[i]?)))

-- PBT for `cons_prop`
example : samples.all (fun s => s.toList.all (fun c =>
    decide (duplicateChars (String.mk (c :: s.toList)) =
      String.mk (c :: c :: dupList s.toList)))) = true := by native_decide
#eval Plausible.Testable.check (∀ (c : Char) (cs : List Char),
  duplicateChars (String.mk (c :: cs)) = String.mk (c :: c :: dupList cs))

-- PBT for `append_prop`
example : (samples.product samples).all (fun p =>
    duplicateChars (p.1 ++ p.2) == duplicateChars p.1 ++ duplicateChars p.2) = true := by
  native_decide
#eval Plausible.Testable.check
  (∀ s t : String, duplicateChars (s ++ t) = duplicateChars s ++ duplicateChars t)

-- PBT for `empty_prop`, `abc_prop`, `punct_prop`
example : (decide (duplicateChars "" = "") && decide (duplicateChars "abc" = "aabbcc") &&
    decide (duplicateChars "!a " = "!!aa  ")) = true := by native_decide

-- PBT for `empty_iff_prop`
example : samples.all (fun s => decide (duplicateChars s = "" ↔ s = "")) = true := by
  native_decide
#eval Plausible.Testable.check (∀ s : String, duplicateChars s = "" ↔ s = "")

-- PBT for `injective_prop` (implicational, hence tested in Boolean form)
example : (samples.product samples).all (fun p =>
    decide (duplicateChars p.1 = duplicateChars p.2 → p.1 = p.2)) = true := by native_decide
#eval Plausible.Testable.check
  (∀ s t : String, decide (duplicateChars s = duplicateChars t → s = t))

-- PBT for `mem_prop`
example : samples.all (fun s =>
    (s.toList.all (fun c => decide (c ∈ (duplicateChars s).toList))) &&
    ((duplicateChars s).toList.all (fun c => decide (c ∈ s.toList)))) = true := by native_decide
#eval Plausible.Testable.check
  (∀ (s : String) (c : Char), c ∈ s.toList ↔ c ∈ (duplicateChars s).toList)

-- PBT for `mk_prop`
example : samples.all (fun s =>
    decide (duplicateChars (String.mk s.toList) = String.mk (dupList s.toList))) = true := by
  native_decide
#eval Plausible.Testable.check
  (∀ cs : List Char, duplicateChars (String.mk cs) = String.mk (dupList cs))

-- PBT for `error_prop` and `ok_prop`
example : samples.all (fun s => match duplicateCharsPy (some s) with
    | .ok r => r == duplicateChars s
    | .error _ => false) = true := by native_decide
example : (match duplicateCharsPy none with
    | .error e => e == valueError
    | .ok _ => false) = true := by native_decide

-- PBT for `preCheck` (executable form of `Pre`)
example : sampleArgs.all (fun x => preCheck x == x.isSome) = true := by native_decide
#eval Plausible.Testable.check (∀ x : Option String, preCheck x = x.isSome)

-- PBT for the post-condition `Post_prop`
example : sampleArgs.all postCheck = true := by native_decide
example : postCheck none = true := by native_decide
example : samples.all (fun s => postCheck (some s)) = true := by native_decide
#eval Plausible.Testable.check (∀ x : Option String, postCheck x = true)

/-! ## Correctness: `Pre -> Post` -/

theorem correctness_thm (x : Option String) (h : Pre x) : Post_prop x (duplicateCharsPy x) := by
  cases x with
  | some s =>
    constructor
    · intro s' hs'
      have heq : s = s' := by simpa using hs'
      subst heq
      exact ⟨rfl, strPost_thm s⟩
    · intro hx
      exact Option.noConfusion hx
  | none => exact absurd h not_Pre_none

/-- The string-level correctness statement, for a genuine `str` argument. -/
theorem correctness_str (s : String) : StrPost s (duplicateChars s) := strPost_thm s

/-! ## Imperative implementation -/

/-- The imperative accumulation loop: `out` is a mutable buffer into which every character of
`cs` is pushed twice. -/
def dupLoop (cs : List Char) (init : Array Char) : Array Char := Id.run do
  let mut out := init
  for c in cs do
    out := out.push c
    out := out.push c
  return out

theorem dupLoop_nil (init : Array Char) : dupLoop [] init = init := by simp [dupLoop]

theorem dupLoop_cons (c : Char) (cs : List Char) (init : Array Char) :
    dupLoop (c :: cs) init = dupLoop cs ((init.push c).push c) := by simp [dupLoop]

/-- Loop invariant: the buffer always holds what was already in it followed by the duplicated
characters processed so far. -/
theorem dupLoop_toList (cs : List Char) (init : Array Char) :
    (dupLoop cs init).toList = init.toList ++ dupList cs := by
  induction cs generalizing init with
  | nil => simp [dupLoop_nil]
  | cons c cs ih =>
    rw [dupLoop_cons, ih ((init.push c).push c)]
    simp [Array.toList_push, List.append_assoc]

/-- Imperative `duplicate_chars`: `Id.run do` with mutable state (an `Array Char` buffer that is
pushed to inside a `for` loop). -/
def duplicateCharsImp (s : String) : String := Id.run do
  let mut out : Array Char := #[]
  for c in s.toList do
    out := out.push c
    out := out.push c
  return String.mk out.toList

theorem duplicateCharsImp_eq_loop (s : String) :
    duplicateCharsImp s = String.mk (dupLoop s.toList #[]).toList := by
  simp [duplicateCharsImp, dupLoop]

/-! ## Imperative tests -/

example : duplicateCharsImp "abc" = "aabbcc" := by native_decide
example : duplicateCharsImp "" = "" := by native_decide
example : duplicateCharsImp "!a " = "!!aa  " := by native_decide
example : duplicateCharsImp "Lean 4" = "LLeeaann  44" := by native_decide
example : (duplicateCharsImp "abc").length = 6 := by native_decide

#eval duplicateCharsImp "abc"
#eval duplicateCharsImp ""
#eval duplicateCharsImp "!a "
#eval duplicateCharsImp "Lean 4"

-- bounded PBT: the imperative loop invariant
example : samples.all (fun s =>
    (dupLoop s.toList #[]).toList == dupList s.toList) = true := by native_decide
example : samples.all (fun s =>
    (dupLoop s.toList #['z']).toList == ['z'] ++ dupList s.toList) = true := by native_decide

-- bounded PBT: imperative agrees with the functional implementation on the corpus
example : samples.all (fun s => duplicateCharsImp s == duplicateChars s) = true := by
  native_decide
example : samples.all (fun s => (duplicateCharsImp s).length == 2 * s.length) = true := by
  native_decide
example : samples.all (fun s =>
    (duplicateCharsImp s).toList == s.toList.flatMap (fun c => [c, c])) = true := by native_decide

-- randomized PBT: imperative = functional
#eval Plausible.Testable.check (∀ s : String, duplicateCharsImp s = duplicateChars s)
#eval Plausible.Testable.check
  (∀ cs : List Char, (dupLoop cs #[]).toList = dupList cs)

/-! ## Equivalence: functional = imperative -/

theorem equivalence_thm (s : String) : duplicateCharsImp s = duplicateChars s := by
  rw [duplicateCharsImp_eq_loop, dupLoop_toList, duplicateChars]
  simp

/-- The imperative implementation satisfies the same post-condition. -/
theorem correctness_imp (s : String) : StrPost s (duplicateCharsImp s) := by
  rw [equivalence_thm]
  exact strPost_thm s

end DuplicateChars41
