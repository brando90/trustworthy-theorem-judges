import Mathlib

/-!
# 41 — Duplicate Characters

Translation of the Python program `duplicate_chars`.

Given a string, return a new string in which every character is written twice,
in the same order:

* `duplicate_chars("abc") = "aabbcc"`
* `duplicate_chars("") = ""`
* `duplicate_chars("!a ") = "!!aa  "`

This is the string analogue of `''.join(c * 2 for c in s)`.
The empty string is a fixed point. Non-string input is rejected with an error
(`ValueError` in Python); that guard is modelled by `duplicate_chars_py`.
-/

namespace «41_duplicate_chars»

/-- List-level character duplication: each element is written twice. -/
def dupList : List Char → List Char
  | [] => []
  | c :: cs => c :: c :: dupList cs

/-- Recover characters at even indices. A trailing singleton is kept. -/
def evenChars : List Char → List Char
  | [] => []
  | [c] => [c]
  | c :: _ :: cs => c :: evenChars cs

/-- Recover characters at odd indices. A trailing singleton is dropped. -/
def oddChars : List Char → List Char
  | [] => []
  | [_] => []
  | _ :: c :: cs => c :: oddChars cs

/--
Functional implementation of Python `duplicate_chars`.

`''.join(c * 2 for c in s)` — each one-character string is repeated twice and
the pieces are concatenated.
-/
def duplicate_chars (s : String) : String :=
  String.join (s.data.map fun c => String.singleton c ++ String.singleton c)

/-- Python `isinstance` guard on a dynamically typed value. -/
inductive PyVal where
  | ofString : String → PyVal
  | none : PyVal
  | nonStr : PyVal

/-- Python `pre`: the value must be a string. -/
def pyPre : PyVal → Bool
  | .ofString _ => true
  | .none => false
  | .nonStr => false

/--
Python entry point, including the `ValueError` raised when `pre` fails.
-/
def duplicate_chars_py (v : PyVal) : Except String String :=
  match v with
  | .ofString s =>
    if pyPre v then Except.ok (duplicate_chars s)
    else Except.error "Input must be a string"
  | .none => Except.error "Input must be a string"
  | .nonStr => Except.error "Input must be a string"

/-! ## Unit tests -/

example : duplicate_chars "abc" = "aabbcc" := by native_decide
example : duplicate_chars "" = "" := by native_decide
example : duplicate_chars "!a " = "!!aa  " := by native_decide
example : duplicate_chars "a" = "aa" := by native_decide
example : duplicate_chars_py .none = Except.error "Input must be a string" := rfl
example : duplicate_chars_py .nonStr = Except.error "Input must be a string" := rfl
example : duplicate_chars_py (.ofString "abc") = Except.ok "aabbcc" := rfl

#eval duplicate_chars "abc"
#eval duplicate_chars ""
#eval duplicate_chars "!a "

/-! ## Pre-condition -/

/-- Boolean form of Python `pre` at the `String` layer (the type already guarantees it). -/
def pre (_s : String) : Bool := true

/-- `duplicate_chars` is defined on every Lean `String`, matching `isinstance(s, str)`. -/
def Pre (s : String) : Prop := pre s = true


/-! ## Auxiliary lemmas -/

theorem dupList_length (cs : List Char) : (dupList cs).length = 2 * cs.length := by
  induction cs with
  | nil => simp [dupList]
  | cons c cs ih => simp [dupList, ih, Nat.mul_succ]

theorem dupList_append (xs ys : List Char) :
    dupList (xs ++ ys) = dupList xs ++ dupList ys := by
  induction xs with
  | nil => simp [dupList]
  | cons c cs ih => simp [dupList, ih]

theorem dupList_getElem?_even (cs : List Char) (i : Nat) :
    (dupList cs)[2 * i]? = cs[i]? := by
  induction cs generalizing i with
  | nil => simp [dupList]
  | cons c cs ih =>
    cases i with
    | zero => simp [dupList]
    | succ i =>
      simp [dupList, Nat.mul_succ]
      exact ih i

theorem dupList_getElem?_odd (cs : List Char) (i : Nat) :
    (dupList cs)[2 * i + 1]? = cs[i]? := by
  induction cs generalizing i with
  | nil => simp [dupList]
  | cons c cs ih =>
    cases i with
    | zero => simp [dupList]
    | succ i =>
      simp [dupList, Nat.mul_succ]
      exact ih i

theorem evenChars_dupList (cs : List Char) : evenChars (dupList cs) = cs := by
  induction cs with
  | nil => simp [dupList, evenChars]
  | cons c cs ih => simp [dupList, evenChars, ih]

theorem oddChars_dupList (cs : List Char) : oddChars (dupList cs) = cs := by
  induction cs with
  | nil => simp [dupList, oddChars]
  | cons c cs ih => simp [dupList, oddChars, ih]

theorem dupList_count (cs : List Char) (c : Char) :
    (dupList cs).count c = 2 * cs.count c := by
  induction cs with
  | nil => simp [dupList]
  | cons x cs ih =>
    simp [dupList, List.count_cons, ih]
    split <;> omega

theorem mem_dupList (cs : List Char) (c : Char) : c ∈ dupList cs ↔ c ∈ cs := by
  induction cs with
  | nil => simp [dupList]
  | cons x cs ih => simp [dupList, ih]

theorem dupList_eq_flatMap (cs : List Char) :
    dupList cs = cs.flatMap (fun c => [c, c]) := by
  induction cs with
  | nil => simp [dupList]
  | cons c cs ih => simp [dupList, ih]

theorem singleton_dup (c : Char) :
    String.singleton c ++ String.singleton c = String.mk [c, c] := by
  apply String.ext
  simp [String.data_append, String.data_singleton]

theorem join_dup_aux (acc : String) (cs : List Char) :
    (cs.map fun c => String.singleton c ++ String.singleton c).foldl (fun r s => r ++ s) acc
      = acc ++ String.mk (dupList cs) := by
  induction cs generalizing acc with
  | nil => simp [dupList, String.append_empty]
  | cons c cs ih =>
    rw [List.map_cons, List.foldl_cons, ih, singleton_dup, String.append_assoc]
    apply congrArg (fun t => acc ++ t)
    apply String.ext
    simp [dupList, String.data_append]

theorem duplicate_chars_eq_mk (s : String) :
    duplicate_chars s = String.mk (dupList s.data) := by
  have h := join_dup_aux "" s.data
  simpa [duplicate_chars, String.join, String.empty_append] using h

theorem duplicate_chars_data (s : String) :
    (duplicate_chars s).data = dupList s.data := by
  rw [duplicate_chars_eq_mk]


/-! ## Properties -/

/-- The empty string is duplicated to the empty string. -/
def empty_prop : Prop := duplicate_chars "" = ""

theorem empty_thm : empty_prop := by
  simp [empty_prop, duplicate_chars_eq_mk, dupList]

/-- Output length is twice the input length (Python `len`). -/
def length_doubled_prop (s : String) : Prop :=
  (duplicate_chars s).length = 2 * s.length

theorem length_doubled_thm (s : String) : length_doubled_prop s := by
  simp [length_doubled_prop, duplicate_chars_eq_mk, dupList_length, String.length_mk]

/-- Duplication distributes over concatenation. -/
def concat_hom_prop (s t : String) : Prop :=
  duplicate_chars (s ++ t) = duplicate_chars s ++ duplicate_chars t

theorem concat_hom_thm (s t : String) : concat_hom_prop s t := by
  apply String.ext
  simp [duplicate_chars_data, dupList_append, String.data_append]

/-- A one-character string is duplicated to two copies of that character. -/
def singleton_prop (c : Char) : Prop :=
  duplicate_chars (String.singleton c) = String.singleton c ++ String.singleton c

theorem singleton_thm (c : Char) : singleton_prop c := by
  apply String.ext
  simp [duplicate_chars_data, String.data_singleton, dupList, String.data_append]

/--
Even positions of the result reproduce the input, and so do odd positions.
This is the pointwise reading of "each character is duplicated".
-/
def paired_positions_prop (s : String) : Prop :=
  evenChars (duplicate_chars s).data = s.data ∧
  oddChars (duplicate_chars s).data = s.data

theorem paired_positions_thm (s : String) : paired_positions_prop s := by
  simp [paired_positions_prop, duplicate_chars_data, evenChars_dupList, oddChars_dupList]

/-- Character at index `i` appears at both result indices `2*i` and `2*i+1`. -/
def index_dup_prop (s : String) : Prop :=
  ∀ i : Nat,
    (duplicate_chars s).data[2 * i]? = s.data[i]? ∧
    (duplicate_chars s).data[2 * i + 1]? = s.data[i]?

theorem index_dup_thm (s : String) : index_dup_prop s := by
  intro i
  simp [duplicate_chars_data, dupList_getElem?_even, dupList_getElem?_odd]

/-- Each character occurs exactly twice as often in the result. -/
def count_doubled_prop (s : String) : Prop :=
  ∀ c : Char, (duplicate_chars s).data.count c = 2 * s.data.count c

theorem count_doubled_thm (s : String) : count_doubled_prop s := by
  intro c
  simp [duplicate_chars_data, dupList_count]

/-- The result uses exactly the characters of the input. -/
def mem_prop (s : String) : Prop :=
  ∀ c : Char, c ∈ (duplicate_chars s).data ↔ c ∈ s.data

theorem mem_thm (s : String) : mem_prop s := by
  intro c
  simp [duplicate_chars_data, mem_dupList]

/-- Direct translation of `''.join(c * 2 for c in s)` as a list equation. -/
def flatMap_spec_prop (s : String) : Prop :=
  (duplicate_chars s).data = s.data.flatMap (fun c => [c, c])

theorem flatMap_spec_thm (s : String) : flatMap_spec_prop s := by
  simp [flatMap_spec_prop, duplicate_chars_data, dupList_eq_flatMap]

/-- Duplication is injective: the original string can be recovered. -/
def injective_prop : Prop := Function.Injective duplicate_chars

theorem injective_thm : injective_prop := by
  intro s t h
  apply String.ext
  have hd : dupList s.data = dupList t.data := by
    simpa [duplicate_chars_data] using congrArg String.data h
  simpa [evenChars_dupList] using congrArg evenChars hd

/--
Recursive characterization matching a left-to-right scan:
`f("") = ""` and `f(c + s) = (c + c) + f(s)`.
Any such `f` agrees with `duplicate_chars`.
-/
def recursive_spec_prop (f : String → String) : Prop :=
  f "" = "" ∧
  ∀ c s, f (String.singleton c ++ s) = String.singleton c ++ String.singleton c ++ f s

theorem recursive_spec_agrees (f : String → String) (hf : recursive_spec_prop f)
    (cs : List Char) : f (String.mk cs) = String.mk (dupList cs) := by
  rcases hf with ⟨h0, h1⟩
  induction cs with
  | nil =>
    simpa [dupList] using h0
  | cons c cs ih =>
    have step := h1 c (String.mk cs)
    have hs : String.singleton c ++ String.mk cs = String.mk (c :: cs) := by
      apply String.ext
      simp [String.data_singleton, String.data_append]
    have hr :
        String.singleton c ++ String.singleton c ++ String.mk (dupList cs)
          = String.mk (c :: c :: dupList cs) := by
      apply String.ext
      simp [String.data_singleton, String.data_append]
    simpa [hs, hr, dupList, ih] using step

theorem recursive_spec_thm (f : String → String) (hf : recursive_spec_prop f) (s : String) :
    f s = duplicate_chars s := by
  have h := recursive_spec_agrees f hf s.data
  simpa [duplicate_chars_eq_mk] using h

/-- `duplicate_chars` itself satisfies the recursive specification. -/
theorem duplicate_chars_recursive_thm : recursive_spec_prop duplicate_chars := by
  refine ⟨?_, ?_⟩
  · simpa using empty_thm
  · intro c s
    apply String.ext
    simp [duplicate_chars_data, String.data_singleton, String.data_append, dupList]


/-! ## Post-condition -/

/--
Post-condition of `duplicate_chars`: `r` is exactly the character-wise
duplication of `s` (the list form of `''.join(c * 2 for c in s)`), and therefore
has doubled length, doubled counts, matching even/odd projections, and the
pointwise index specification.
-/
def Post_prop (s r : String) : Prop :=
  r.data = s.data.flatMap (fun c => [c, c]) ∧
  r.length = 2 * s.length ∧
  evenChars r.data = s.data ∧
  oddChars r.data = s.data ∧
  (∀ i : Nat, r.data[2 * i]? = s.data[i]? ∧ r.data[2 * i + 1]? = s.data[i]?) ∧
  (∀ c : Char, r.data.count c = 2 * s.data.count c) ∧
  (∀ c : Char, c ∈ r.data ↔ c ∈ s.data)

/-! ## Property-based tests -/

#eval Plausible.Testable.check (duplicate_chars "" = "")

#eval Plausible.Testable.check
  (∀ s : String, (duplicate_chars s).length = 2 * s.length)

#eval Plausible.Testable.check
  (∀ s t : String, duplicate_chars (s ++ t) = duplicate_chars s ++ duplicate_chars t)

#eval Plausible.Testable.check
  (∀ c : Char,
    duplicate_chars (String.singleton c) = String.singleton c ++ String.singleton c)

#eval Plausible.Testable.check
  (∀ s : String,
    evenChars (duplicate_chars s).data = s.data ∧
    oddChars (duplicate_chars s).data = s.data)

#eval Plausible.Testable.check
  (∀ s : String, ∀ i : Nat,
    (duplicate_chars s).data[2 * i]? = s.data[i]? ∧
    (duplicate_chars s).data[2 * i + 1]? = s.data[i]?)

#eval Plausible.Testable.check
  (∀ s : String, ∀ c : Char,
    (duplicate_chars s).data.count c = 2 * s.data.count c)

#eval Plausible.Testable.check
  (∀ s : String, ∀ c : Char, c ∈ (duplicate_chars s).data ↔ c ∈ s.data)

#eval Plausible.Testable.check
  (∀ s : String, (duplicate_chars s).data = s.data.flatMap (fun c => [c, c]))

-- `injective_prop` is an implication, so random pairs rarely meet the premise
-- (Plausible reports Gave up). The bounded exhaustive check below covers it.
-- PBT for `recursive_spec_prop`: the higher-order spec is not itself sampleable;
-- its executable counterpart is that `duplicate_chars` obeys the two equations.
#eval Plausible.Testable.check
  (∀ c : Char, ∀ s : String,
    duplicate_chars (String.singleton c ++ s)
      = String.singleton c ++ String.singleton c ++ duplicate_chars s)

/-- Executable Boolean form of `Post_prop`.
The `∀ i` conjunct is checked for every `i ≤ s.length` (past that both sides are `none`).
The `∀ c` count and membership conjuncts are checked on characters of `s` and of the
result; characters outside that finite set have count 0 and are absent on both sides.
The separate Plausible checks above test those quantified conjuncts directly.
-/
def Post_bool (s : String) : Bool :=
  let r := duplicate_chars s
  let idxOk := (List.range (s.length + 1)).all fun i =>
    (r.data[2 * i]? == s.data[i]?) && (r.data[2 * i + 1]? == s.data[i]?)
  let countOk := (s.data ++ r.data).all fun c =>
    r.data.count c == 2 * s.data.count c
  let memOk := (s.data ++ r.data).all fun c =>
    decide (c ∈ r.data) == decide (c ∈ s.data)
  (r.data == s.data.flatMap (fun c => [c, c])) &&
    (r.length == 2 * s.length) &&
    (evenChars r.data == s.data) &&
    (oddChars r.data == s.data) &&
    idxOk && countOk && memOk

#eval Plausible.Testable.check (∀ s : String, Post_bool s = true)

/-- Bounded exhaustive check on strings of `'a'` repeated up to length 30. -/
example : (List.range 30).all (fun n =>
    let s := String.mk (List.replicate n 'a')
    (duplicate_chars s).length == 2 * s.length &&
    evenChars (duplicate_chars s).data == s.data &&
    (duplicate_chars s).data == s.data.flatMap (fun c => [c, c])) = true := by
  native_decide

/-- Bounded check of the specification on a fixed alphabet, lengths ≤ 3. -/
def alphabet : List Char := ['a', 'b', '!', ' ']

def stringsUpTo : Nat → List String
  | 0 => [""]
  | n + 1 =>
    stringsUpTo n ++
      (stringsUpTo n).flatMap fun s => alphabet.map fun c => s.push c

example : (stringsUpTo 3).all (fun s =>
    duplicate_chars s == String.mk (s.data.flatMap fun c => [c, c]) &&
    (duplicate_chars s).length == 2 * s.length &&
    Post_bool s) = true := by
  native_decide

/-- Bounded PBT for `injective_prop` on all strings of length ≤ 2 over `alphabet`. -/
example : (stringsUpTo 2).all (fun s =>
    (stringsUpTo 2).all (fun t =>
      !(duplicate_chars s == duplicate_chars t) || s == t)) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (s : String) (h : Pre s) : Post_prop s (duplicate_chars s) := by
  have _hp : pre s = true := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [flatMap_spec_prop] using flatMap_spec_thm s
  · simpa [length_doubled_prop] using length_doubled_thm s
  · simpa [duplicate_chars_data] using evenChars_dupList s.data
  · simpa [duplicate_chars_data] using oddChars_dupList s.data
  · intro i
    exact ⟨dupList_getElem?_even s.data i ▸ by simp [duplicate_chars_data],
           dupList_getElem?_odd s.data i ▸ by simp [duplicate_chars_data]⟩
  · intro c
    simpa [duplicate_chars_data] using dupList_count s.data c
  · intro c
    simpa [duplicate_chars_data] using mem_dupList s.data c

/-! ## Imperative implementation -/

/--
Imperative implementation: walk the characters, pushing each one twice into a
mutable accumulator.
-/
def duplicate_chars_imp (s : String) : String :=
  Id.run do
    let mut acc : String := ""
    for c in s.data do
      acc := (acc.push c).push c
    return acc

/-! ## Imperative tests -/

example : duplicate_chars_imp "abc" = "aabbcc" := by native_decide
example : duplicate_chars_imp "" = "" := by native_decide
example : duplicate_chars_imp "!a " = "!!aa  " := by native_decide
example : duplicate_chars_imp "a" = "aa" := by native_decide

#eval duplicate_chars_imp "abc"
#eval duplicate_chars_imp "!a "

/-! ## Equivalence -/

theorem push_push_eq_append (acc : String) (c : Char) :
    (acc.push c).push c = acc ++ String.mk [c, c] := by
  apply String.ext
  simp [String.data_push]

theorem foldl_push_eq_mk (acc : String) (cs : List Char) :
    cs.foldl (fun acc c => (acc.push c).push c) acc = acc ++ String.mk (dupList cs) := by
  induction cs generalizing acc with
  | nil => simp [dupList, String.append_empty]
  | cons c cs ih =>
    rw [List.foldl_cons, ih, push_push_eq_append, String.append_assoc]
    apply congrArg (fun t => acc ++ t)
    apply String.ext
    simp [dupList, String.data_append]

theorem duplicate_chars_imp_eq_foldl (s : String) :
    duplicate_chars_imp s =
      s.data.foldl (fun acc c => (acc.push c).push c) "" := by
  simp [duplicate_chars_imp]

/-- The functional and imperative implementations agree on every string. -/
theorem functional_eq_imperative_thm (s : String) :
    duplicate_chars s = duplicate_chars_imp s := by
  rw [duplicate_chars_eq_mk, duplicate_chars_imp_eq_foldl, foldl_push_eq_mk, String.empty_append]

end «41_duplicate_chars»
