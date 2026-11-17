import Mathlib

/-!
# 41_duplicate_chars

Formalization of the Python `duplicate_chars` program in Lean 4.
Given an input string `s`, `duplicate_chars s` returns a new string in which every
character from `s` is duplicated in order.

Edge cases:
- Empty string returns empty string.
-/

namespace «41_duplicate_chars»

/-! ## 1. Functional Implementation -/

/-- Helper function that duplicates each character in a list of characters. -/
def dupList : List Char → List Char
  | [] => []
  | c :: cs => c :: c :: dupList cs

/-- Return a new string where each character from the input string is duplicated. -/
def duplicate_chars (s : String) : String :=
  String.mk (dupList s.data)

/-! ## 2. Unit Tests -/

#eval duplicate_chars "abc"
#eval duplicate_chars ""
#eval duplicate_chars "!a "
#eval duplicate_chars "a"
#eval duplicate_chars "11"

example : duplicate_chars "abc" = "aabbcc" := by native_decide
example : duplicate_chars "" = "" := by native_decide
example : duplicate_chars "!a " = "!!aa  " := by native_decide
example : duplicate_chars "a" = "aa" := by native_decide
example : duplicate_chars "11" = "1111" := by native_decide
example : duplicate_chars "Hello!" = "HHeelllloo!!" := by native_decide

/-! ## 3. Pre-condition -/

/-- Pre-condition for `duplicate_chars`: in Lean's type system, the input `s : String`
    is guaranteed to be a valid string (`isinstance(s, str)` in Python). -/
def Pre (_s : String) : Prop := True

/-! ## 4. Helper Lemmas on `dupList` -/

@[simp]
theorem dupList_nil : dupList [] = [] := rfl

@[simp]
theorem dupList_cons (c : Char) (cs : List Char) :
    dupList (c :: cs) = c :: c :: dupList cs := rfl

/-- `dupList` is equivalent to `List.flatMap (fun c => [c, c])`. -/
theorem dupList_eq_flatMap (cs : List Char) :
    dupList cs = cs.flatMap (fun c => [c, c]) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [dupList, ih]

@[simp]
theorem dupList_length (cs : List Char) :
    (dupList cs).length = 2 * cs.length := by
  induction cs with
  | nil => simp [dupList]
  | cons c cs ih =>
    simp [dupList, ih]
    omega

@[simp]
theorem dupList_append (cs₁ cs₂ : List Char) :
    dupList (cs₁ ++ cs₂) = dupList cs₁ ++ dupList cs₂ := by
  induction cs₁ with
  | nil => simp [dupList]
  | cons c cs₁ ih => simp [dupList, ih]

@[simp]
theorem dupList_reverse (cs : List Char) :
    dupList cs.reverse = (dupList cs).reverse := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [dupList, ih, List.append_assoc]

@[simp]
theorem dupList_eq_nil_iff (cs : List Char) :
    dupList cs = [] ↔ cs = [] := by
  cases cs <;> simp [dupList]

theorem dupList_getElem?_even (cs : List Char) (i : Nat) :
    (dupList cs)[2 * i]? = cs[i]? := by
  induction cs generalizing i with
  | nil => simp [dupList]
  | cons c cs ih =>
    cases i with
    | zero => simp [dupList]
    | succ j =>
      have h : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
      rw [dupList_cons, h]
      simp [ih j]

theorem dupList_getElem?_odd (cs : List Char) (i : Nat) :
    (dupList cs)[2 * i + 1]? = cs[i]? := by
  induction cs generalizing i with
  | nil => simp [dupList]
  | cons c cs ih =>
    cases i with
    | zero => simp [dupList]
    | succ j =>
      have h : 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 := by omega
      rw [dupList_cons, h]
      simp [ih j]

@[simp]
theorem mem_dupList_iff (cs : List Char) (x : Char) :
    x ∈ dupList cs ↔ x ∈ cs := by
  induction cs with
  | nil => simp [dupList]
  | cons c cs ih =>
    simp [dupList, ih]

@[simp]
theorem dupList_count (cs : List Char) (x : Char) :
    (dupList cs).count x = 2 * cs.count x := by
  induction cs with
  | nil => simp [dupList]
  | cons c cs ih =>
    simp only [dupList, List.count_cons, ih]
    split_ifs <;> omega

theorem dupList_injective {cs₁ cs₂ : List Char} (h : dupList cs₁ = dupList cs₂) :
    cs₁ = cs₂ := by
  induction cs₁ generalizing cs₂ with
  | nil =>
    cases cs₂ with
    | nil => rfl
    | cons d ds => simp [dupList] at h
  | cons c cs₁ ih =>
    cases cs₂ with
    | nil => simp [dupList] at h
    | cons d ds =>
      simp only [dupList, List.cons.injEq] at h
      obtain ⟨rfl, _, hrest⟩ := h
      rw [ih hrest]

/-! ## 5. Property Propositions and Theorems -/

/-- Property 1: An empty input string produces an empty output string. -/
def empty_prop (s : String) : Prop :=
  s = "" → duplicate_chars s = ""

theorem empty_thm (s : String) (_h : Pre s := trivial) : empty_prop s := by
  intro hs
  subst hs
  rfl

/-- Property 2: The output string is empty if and only if the input string is empty. -/
def isEmpty_iff_prop (s : String) : Prop :=
  (duplicate_chars s = "") ↔ (s = "")

theorem isEmpty_iff_thm (s : String) (_h : Pre s := trivial) : isEmpty_iff_prop s := by
  cases s with
  | mk cs =>
    simp [isEmpty_iff_prop, duplicate_chars, String.ext_iff]

/-- Property 3: The length of the output string is twice the length of the input string. -/
def length_prop (s : String) : Prop :=
  (duplicate_chars s).length = 2 * s.length

theorem length_thm (s : String) (_h : Pre s := trivial) : length_prop s := by
  cases s with
  | mk cs =>
    simp [length_prop, duplicate_chars, ← String.length_data]

/-- Property 4: The length of the output string is always even. -/
def even_length_prop (s : String) : Prop :=
  (duplicate_chars s).length % 2 = 0

theorem even_length_thm (s : String) (_h : Pre s := trivial) : even_length_prop s := by
  have hlen := length_thm s
  simp only [length_prop] at hlen
  simp [even_length_prop, hlen]

/-- Property 5: The character list of `duplicate_chars s` equals `s.data.flatMap (fun c => [c, c])`,
    directly capturing Python's `''.join(c * 2 for c in s)`. -/
def flatMap_prop (s : String) : Prop :=
  (duplicate_chars s).data = s.data.flatMap (fun c => [c, c])

theorem flatMap_thm (s : String) (_h : Pre s := trivial) : flatMap_prop s := by
  simp [flatMap_prop, duplicate_chars, dupList_eq_flatMap]

/-- Property 6: Every even position `2 * i` in the output matches position `i` in the input. -/
def even_index_prop (s : String) : Prop :=
  ∀ i < s.length, (duplicate_chars s).data[2 * i]? = s.data[i]?

theorem even_index_thm (s : String) (_h : Pre s := trivial) : even_index_prop s := by
  intro i _hi
  simp [duplicate_chars, dupList_getElem?_even]

/-- Property 7: Every odd position `2 * i + 1` in the output matches position `i` in the input. -/
def odd_index_prop (s : String) : Prop :=
  ∀ i < s.length, (duplicate_chars s).data[2 * i + 1]? = s.data[i]?

theorem odd_index_thm (s : String) (_h : Pre s := trivial) : odd_index_prop s := by
  intro i _hi
  simp [duplicate_chars, dupList_getElem?_odd]

/-- Property 8: Every adjacent pair `(2 * i, 2 * i + 1)` in the output holds identical characters. -/
def adjacent_pair_prop (s : String) : Prop :=
  ∀ i < s.length, (duplicate_chars s).data[2 * i]? = (duplicate_chars s).data[2 * i + 1]?

theorem adjacent_pair_thm (s : String) (_h : Pre s := trivial) : adjacent_pair_prop s := by
  intro i _hi
  simp [duplicate_chars, dupList_getElem?_even, dupList_getElem?_odd]

/-- Property 9: In-bounds indexing into `(duplicate_chars s).data` at `2 * i` and `2 * i + 1`
    yields `s.data[i]`. -/
def getElem_dup_prop (s : String) : Prop :=
  ∀ (i : Nat) (hi : i < s.length),
    have hin : i < s.data.length := by simp [hi]
    have heven : 2 * i < (duplicate_chars s).data.length := by
      simp [duplicate_chars]; omega
    have hodd : 2 * i + 1 < (duplicate_chars s).data.length := by
      simp [duplicate_chars]; omega
    (duplicate_chars s).data[2 * i]'heven = s.data[i]'hin ∧
    (duplicate_chars s).data[2 * i + 1]'hodd = s.data[i]'hin

theorem getElem_dup_thm (s : String) (_h : Pre s := trivial) : getElem_dup_prop s := by
  intro i hi
  have hin : i < s.data.length := by simp [hi]
  have heven : 2 * i < (duplicate_chars s).data.length := by
    simp [duplicate_chars]; omega
  have hodd : 2 * i + 1 < (duplicate_chars s).data.length := by
    simp [duplicate_chars]; omega
  have h1 : (duplicate_chars s).data[2 * i]? = s.data[i]? := by
    simp [duplicate_chars, dupList_getElem?_even]
  have h2 : (duplicate_chars s).data[2 * i + 1]? = s.data[i]? := by
    simp [duplicate_chars, dupList_getElem?_odd]
  rw [List.getElem?_eq_getElem heven, List.getElem?_eq_getElem hin] at h1
  rw [List.getElem?_eq_getElem hodd, List.getElem?_eq_getElem hin] at h2
  exact ⟨Option.some.inj h1, Option.some.inj h2⟩

/-- Property 10: The count of each character in `duplicate_chars s` is twice its count in `s`. -/
def count_prop (s : String) : Prop :=
  ∀ c : Char, (duplicate_chars s).data.count c = 2 * s.data.count c

theorem count_thm (s : String) (_h : Pre s := trivial) : count_prop s := by
  intro c
  simp [duplicate_chars]

/-- Property 11: Character membership is preserved between the input and output strings. -/
def mem_prop (s : String) : Prop :=
  ∀ c : Char, c ∈ (duplicate_chars s).data ↔ c ∈ s.data

theorem mem_thm (s : String) (_h : Pre s := trivial) : mem_prop s := by
  intro c
  simp [duplicate_chars]

/-- Property 12: Duplicating characters commutes with string reversal. -/
def reverse_prop (s : String) : Prop :=
  String.mk (duplicate_chars s).data.reverse = duplicate_chars (String.mk s.data.reverse)

theorem reverse_thm (s : String) (_h : Pre s := trivial) : reverse_prop s := by
  simp [reverse_prop, duplicate_chars]

/-- Property 13: `duplicate_chars` distributes over string concatenation (`++`). -/
def append_prop (s₁ s₂ : String) : Prop :=
  duplicate_chars (s₁ ++ s₂) = duplicate_chars s₁ ++ duplicate_chars s₂

theorem append_thm (s₁ s₂ : String) : append_prop s₁ s₂ := by
  cases s₁ with
  | mk cs₁ =>
    cases s₂ with
    | mk cs₂ =>
      simp only [append_prop, duplicate_chars, String.data_append, dupList_append]
      rfl

/-- Property 14: `duplicate_chars` is injective. -/
def injective_prop (s₁ s₂ : String) : Prop :=
  duplicate_chars s₁ = duplicate_chars s₂ ↔ s₁ = s₂

theorem injective_thm (s₁ s₂ : String) : injective_prop s₁ s₂ := by
  constructor
  · intro h
    cases s₁ with
    | mk cs₁ =>
      cases s₂ with
      | mk cs₂ =>
        simp only [duplicate_chars, String.mk.injEq] at h
        exact congrArg String.mk (dupList_injective h)
  · intro h
    rw [h]

/-! ## 6. Post-condition -/

/-- Post-condition for `duplicate_chars`: conjunction of all single-input specification properties. -/
def Post_prop (s : String) : Prop :=
  empty_prop s ∧
  isEmpty_iff_prop s ∧
  length_prop s ∧
  even_length_prop s ∧
  flatMap_prop s ∧
  even_index_prop s ∧
  odd_index_prop s ∧
  adjacent_pair_prop s ∧
  getElem_dup_prop s ∧
  count_prop s ∧
  mem_prop s ∧
  reverse_prop s

/-! ## 7. Property-Based Tests (PBTs) -/

-- PBT for empty_prop
#eval Plausible.Testable.check (∀ s : String, (!(s == "") || duplicate_chars s == "") = true)
example : (["", "a", "abc", "!a "]).all (fun s => !(s == "") || duplicate_chars s == "") = true := by
  native_decide

-- PBT for isEmpty_iff_prop
#eval Plausible.Testable.check (∀ s : String, (duplicate_chars s == "") = (s == ""))

-- PBT for length_prop
#eval Plausible.Testable.check (∀ s : String, (duplicate_chars s).length = 2 * s.length)

-- PBT for even_length_prop
#eval Plausible.Testable.check (∀ s : String, (duplicate_chars s).length % 2 = 0)

-- PBT for flatMap_prop
#eval Plausible.Testable.check
  (∀ s : String, (duplicate_chars s).data = s.data.flatMap (fun c => [c, c]))

-- PBT for even_index_prop
#eval Plausible.Testable.check
  (∀ s : String, (List.range s.length).all (fun i => (duplicate_chars s).data[2 * i]? == s.data[i]?))

-- PBT for odd_index_prop
#eval Plausible.Testable.check
  (∀ s : String, (List.range s.length).all (fun i => (duplicate_chars s).data[2 * i + 1]? == s.data[i]?))

-- PBT for adjacent_pair_prop
#eval Plausible.Testable.check
  (∀ s : String, (List.range s.length).all
    (fun i => (duplicate_chars s).data[2 * i]? == (duplicate_chars s).data[2 * i + 1]?))

-- PBT for getElem_dup_prop
#eval Plausible.Testable.check
  (∀ s : String, (List.range s.data.length).all
    (fun i => (duplicate_chars s).data.getD (2 * i) default == s.data.getD i default &&
              (duplicate_chars s).data.getD (2 * i + 1) default == s.data.getD i default))

-- PBT for count_prop
#eval Plausible.Testable.check
  (∀ s : String, ∀ c : Char, (duplicate_chars s).data.count c = 2 * s.data.count c)

-- PBT for mem_prop
#eval Plausible.Testable.check
  (∀ s : String, ∀ c : Char, (decide (c ∈ (duplicate_chars s).data)) = (decide (c ∈ s.data)))

-- PBT for reverse_prop
#eval Plausible.Testable.check
  (∀ s : String, String.mk (duplicate_chars s).data.reverse = duplicate_chars (String.mk s.data.reverse))

-- PBT for append_prop
#eval Plausible.Testable.check
  (∀ s₁ s₂ : String, duplicate_chars (s₁ ++ s₂) = duplicate_chars s₁ ++ duplicate_chars s₂)

-- PBT for injective_prop
#eval Plausible.Testable.check
  (∀ s₁ s₂ : String, (duplicate_chars s₁ == duplicate_chars s₂) = (s₁ == s₂))

-- Executable Boolean checker for Post_prop
def checkPost (s : String) : Bool :=
  (!(s == "") || duplicate_chars s == "") &&
  ((duplicate_chars s == "") == (s == "")) &&
  ((duplicate_chars s).length == 2 * s.length) &&
  ((duplicate_chars s).length % 2 == 0) &&
  ((duplicate_chars s).data == s.data.flatMap (fun c => [c, c])) &&
  (List.range s.length).all (fun i => (duplicate_chars s).data[2 * i]? == s.data[i]?) &&
  (List.range s.length).all (fun i => (duplicate_chars s).data[2 * i + 1]? == s.data[i]?) &&
  (List.range s.length).all (fun i => (duplicate_chars s).data[2 * i]? == (duplicate_chars s).data[2 * i + 1]?) &&
  (List.range s.data.length).all (fun i =>
    (duplicate_chars s).data.getD (2 * i) default == s.data.getD i default &&
    (duplicate_chars s).data.getD (2 * i + 1) default == s.data.getD i default) &&
  s.data.all (fun c => (duplicate_chars s).data.count c == 2 * s.data.count c) &&
  s.data.all (fun c => decide (c ∈ (duplicate_chars s).data) == decide (c ∈ s.data)) &&
  (String.mk (duplicate_chars s).data.reverse == duplicate_chars (String.mk s.data.reverse))

-- PBT for Post_prop
#eval Plausible.Testable.check (∀ s : String, checkPost s = true)
example : (["", "a", "abc", "!a ", "11", "Hello, World!"]).all checkPost = true := by native_decide

/-! ## 8. Correctness Theorem (`Pre → Post`) -/

/-- Main correctness theorem: for every string `s` satisfying `Pre s`, `Post_prop s` holds. -/
theorem correctness_thm (s : String) (h : Pre s) : Post_prop s :=
  ⟨empty_thm s h,
   isEmpty_iff_thm s h,
   length_thm s h,
   even_length_thm s h,
   flatMap_thm s h,
   even_index_thm s h,
   odd_index_thm s h,
   adjacent_pair_thm s h,
   getElem_dup_thm s h,
   count_thm s h,
   mem_thm s h,
   reverse_thm s h⟩

/-! ## 9. Imperative Implementation -/

/-- Imperative implementation of `duplicate_chars` using `Id.run do` and mutable state. -/
def duplicate_chars_imp (s : String) : String := Id.run do
  let mut result : String := ""
  for c in s.data do
    result := result.push c
    result := result.push c
  return result

/-! ## 10. Imperative Tests -/

#eval duplicate_chars_imp "abc"
#eval duplicate_chars_imp ""
#eval duplicate_chars_imp "!a "
#eval duplicate_chars_imp "a"
#eval duplicate_chars_imp "11"

example : duplicate_chars_imp "abc" = "aabbcc" := by native_decide
example : duplicate_chars_imp "" = "" := by native_decide
example : duplicate_chars_imp "!a " = "!!aa  " := by native_decide
example : duplicate_chars_imp "a" = "aa" := by native_decide
example : duplicate_chars_imp "11" = "1111" := by native_decide
example : duplicate_chars_imp "Hello!" = "HHeelllloo!!" := by native_decide

-- PBT checking equivalence on random strings
#eval Plausible.Testable.check (∀ s : String, duplicate_chars s = duplicate_chars_imp s)

/-! ## 11. Equivalence Theorem (Functional = Imperative) -/

/-- Loop invariant relating `List.foldl` of double-push on `String` to `dupList`. -/
theorem foldl_push_twice (cs : List Char) (acc : String) :
    List.foldl (fun (result : String) (c : Char) => (result.push c).push c) acc cs =
      String.mk (acc.data ++ dupList cs) := by
  induction cs generalizing acc with
  | nil =>
    cases acc with
    | mk data => simp [dupList]
  | cons c cs ih =>
    simp only [List.foldl_cons, ih]
    cases acc with
    | mk data =>
      simp [String.push, dupList_cons]

/-- Equivalence theorem: the functional and imperative implementations produce identical results
    for all input strings `s`. -/
theorem equivalence_thm (s : String) : duplicate_chars s = duplicate_chars_imp s := by
  simp [duplicate_chars, duplicate_chars_imp, foldl_push_twice]

end «41_duplicate_chars»
