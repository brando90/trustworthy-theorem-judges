import Mathlib

/-!
# 41_duplicate_chars: Duplicate Each Character in a String

This module formalizes the Python `duplicate_chars` function in Lean 4.
Given an input string `s`, `duplicate_chars s` returns a new string in which every
character of `s` is duplicated in order.

## Structure
1. Functional implementation (`duplicate_chars` and option wrapper `duplicate_chars_opt`)
2. Unit tests (`example` with `native_decide` and `#eval`)
3. Pre-condition (`Pre`)
4. Property propositions (`*_prop`) and kernel-checked theorems (`*_thm`)
5. Post-condition (`Post_prop`)
6. Property-based tests (`Plausible.Testable.check` and bounded exhaustive tests)
7. Correctness theorem (`duplicate_chars_correct : Pre s → Post_prop s`)
8. Imperative implementation (`duplicate_chars_imp` using `Id.run do`)
9. Imperative unit tests
10. Functional-imperative equivalence theorem (`duplicate_chars_equiv`)
-/

namespace «41_duplicate_chars»

/-! ## Implementation -/

/-- Duplicate each character in the input string `s`. -/
def duplicate_chars (s : String) : String :=
  String.mk (s.data.flatMap (fun c => [c, c]))

/-- Option wrapper modeling the Python runtime check that rejects `None` (`none`). -/
def duplicate_chars_opt (s? : Option String) : Option String :=
  s?.map duplicate_chars

/-! ## Unit Tests -/

example : duplicate_chars "abc" = "aabbcc" := by native_decide
example : duplicate_chars "" = "" := by native_decide
example : duplicate_chars "!a " = "!!aa  " := by native_decide
example : duplicate_chars "x" = "xx" := by native_decide
example : duplicate_chars "123" = "112233" := by native_decide
example : duplicate_chars "aa" = "aaaa" := by native_decide
example : duplicate_chars_opt (some "abc") = some "aabbcc" := by native_decide
example : duplicate_chars_opt (some "") = some "" := by native_decide
example : duplicate_chars_opt none = none := by native_decide

#eval duplicate_chars "abc"
#eval duplicate_chars ""
#eval duplicate_chars "!a "
#eval duplicate_chars_opt (some "abc")
#eval duplicate_chars_opt none

/-! ## Pre-condition -/

/-- Pre-condition: in Lean's static type system, any `s : String` is a valid string. -/
def Pre (_s : String) : Prop := True

/-! ## Helper Lemmas on Lists and Strings -/

@[simp]
lemma string_empty_append (s : String) : "" ++ s = s := by
  ext : 1
  simp

lemma flatMap_dup_length (xs : List Char) :
    (xs.flatMap (fun c => [c, c])).length = 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

lemma flatMap_dup_getElem? (xs : List Char) (j : Nat) :
    (xs.flatMap (fun c => [c, c]))[j]? = xs[j / 2]? := by
  induction xs generalizing j with
  | nil => simp
  | cons c cs ih =>
    rcases j with _ | _ | k
    · simp
    · simp
    · have hk : (k + 1 + 1) / 2 = k / 2 + 1 := by omega
      rw [hk]
      simp [ih k]

lemma flatMap_dup_count (xs : List Char) (c : Char) :
    (xs.flatMap (fun x => [x, x])).count c = 2 * xs.count c := by
  induction xs with
  | nil => simp
  | cons x cs ih =>
    simp only [List.flatMap_cons, List.count_append, List.count_cons, List.count_nil, ih]
    split_ifs <;> omega

lemma flatMap_dup_injective {xs ys : List Char}
    (h : xs.flatMap (fun c => [c, c]) = ys.flatMap (fun c => [c, c])) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, _, hrest⟩ := h
      congr
      exact ih hrest

/-! ## Property Propositions and Theorems -/

/-- Empty string maps to empty string. -/
def empty_prop (s : String) : Prop :=
  s = "" → duplicate_chars s = ""

theorem empty_thm (s : String) : empty_prop s := by
  intro hs
  subst hs
  rfl

/-- Output is empty if and only if the input is empty. -/
def empty_iff_prop (s : String) : Prop :=
  duplicate_chars s = "" ↔ s = ""

theorem empty_iff_thm (s : String) : empty_iff_prop s := by
  rcases s with ⟨_ | ⟨c, cs⟩⟩
  · simp [empty_iff_prop, duplicate_chars]
  · simp only [empty_iff_prop, duplicate_chars, String.ext_iff]
    simp

/-- The length of `duplicate_chars s` is twice the length of `s`. -/
def length_prop (s : String) : Prop :=
  (duplicate_chars s).length = 2 * s.length

theorem length_thm (s : String) : length_prop s := by
  simp only [length_prop, duplicate_chars, String.length]
  exact flatMap_dup_length s.data

/-- The length of `duplicate_chars s` is always even. -/
def even_length_prop (s : String) : Prop :=
  (duplicate_chars s).length % 2 = 0

theorem even_length_thm (s : String) : even_length_prop s := by
  unfold even_length_prop
  have h : (duplicate_chars s).length = 2 * s.length := length_thm s
  omega

/-- Every index `j` in `duplicate_chars s` corresponds to index `j / 2` in `s`. -/
def index_div_two_prop (s : String) : Prop :=
  ∀ j : Nat, (duplicate_chars s).data[j]? = s.data[j / 2]?

theorem index_div_two_thm (s : String) : index_div_two_prop s := by
  intro j
  simp only [duplicate_chars]
  exact flatMap_dup_getElem? s.data j

/-- For every valid index `i < s.length`, the character at `2 * i` in `duplicate_chars s` equals `s.data[i]?`. -/
def even_index_prop (s : String) : Prop :=
  ∀ i : Nat, i < s.length → (duplicate_chars s).data[2 * i]? = s.data[i]?

theorem even_index_thm (s : String) : even_index_prop s := by
  intro i _hi
  rw [index_div_two_thm s (2 * i)]
  have hdiv : (2 * i) / 2 = i := by omega
  rw [hdiv]

/-- For every valid index `i < s.length`, the character at `2 * i + 1` in `duplicate_chars s` equals `s.data[i]?`. -/
def odd_index_prop (s : String) : Prop :=
  ∀ i : Nat, i < s.length → (duplicate_chars s).data[2 * i + 1]? = s.data[i]?

theorem odd_index_thm (s : String) : odd_index_prop s := by
  intro i _hi
  rw [index_div_two_thm s (2 * i + 1)]
  have hdiv : (2 * i + 1) / 2 = i := by omega
  rw [hdiv]

/-- Each pair of adjacent characters at `(2 * i, 2 * i + 1)` in `duplicate_chars s` are equal. -/
def adjacent_eq_prop (s : String) : Prop :=
  ∀ i : Nat, i < s.length → (duplicate_chars s).data[2 * i]? = (duplicate_chars s).data[2 * i + 1]?

theorem adjacent_eq_thm (s : String) : adjacent_eq_prop s := by
  intro i hi
  rw [even_index_thm s i hi, odd_index_thm s i hi]

/-- Character membership is preserved by `duplicate_chars`. -/
def mem_prop (s : String) : Prop :=
  ∀ c : Char, c ∈ (duplicate_chars s).data ↔ c ∈ s.data

theorem mem_thm (s : String) : mem_prop s := by
  intro c
  simp [duplicate_chars, List.mem_flatMap]

/-- The count of every character `c` in `duplicate_chars s` is twice its count in `s`. -/
def count_prop (s : String) : Prop :=
  ∀ c : Char, (duplicate_chars s).data.count c = 2 * s.data.count c

theorem count_thm (s : String) : count_prop s := by
  intro c
  simp only [duplicate_chars]
  exact flatMap_dup_count s.data c

/-- `duplicate_chars` distributes over string concatenation. -/
def append_prop (s₁ s₂ : String) : Prop :=
  duplicate_chars (s₁ ++ s₂) = duplicate_chars s₁ ++ duplicate_chars s₂

theorem append_thm (s₁ s₂ : String) : append_prop s₁ s₂ := by
  unfold append_prop
  ext : 1
  simp [duplicate_chars, List.flatMap_append]

/-- `duplicate_chars` is injective. -/
def injective_prop (s₁ s₂ : String) : Prop :=
  duplicate_chars s₁ = duplicate_chars s₂ ↔ s₁ = s₂

theorem injective_thm (s₁ s₂ : String) : injective_prop s₁ s₂ := by
  rcases s₁ with ⟨d₁⟩
  rcases s₂ with ⟨d₂⟩
  simp only [injective_prop, duplicate_chars, String.mk.injEq]
  constructor
  · exact flatMap_dup_injective
  · rintro rfl
    rfl

/-- Option wrapper specification: `none` returns `none` and `some s` returns `some (duplicate_chars s)`. -/
def opt_prop (s? : Option String) : Prop :=
  (s? = none ↔ duplicate_chars_opt s? = none) ∧
  (∀ s : String, s? = some s → duplicate_chars_opt s? = some (duplicate_chars s))

theorem opt_thm (s? : Option String) : opt_prop s? := by
  rcases s? with _ | s <;> simp [opt_prop, duplicate_chars_opt]

/-! ## Post-condition -/

/-- Post-condition conjunction of all single-string specification properties of `duplicate_chars`. -/
def Post_prop (s : String) : Prop :=
  empty_prop s ∧
  empty_iff_prop s ∧
  length_prop s ∧
  even_length_prop s ∧
  index_div_two_prop s ∧
  even_index_prop s ∧
  odd_index_prop s ∧
  adjacent_eq_prop s ∧
  mem_prop s ∧
  count_prop s

/-! ## Property-Based Tests -/

-- Executable Boolean check corresponding to `empty_iff_prop`.
#eval Plausible.Testable.check (∀ s : String, (duplicate_chars s == "") == (s == ""))

-- Bounded test for `empty_prop`.
example : (["", "a", "abc", "!a "].all (fun s => !(s == "") || (duplicate_chars s == ""))) = true := by
  native_decide

-- Randomized PBT for `length_prop`.
#eval Plausible.Testable.check (∀ s : String, (duplicate_chars s).length = 2 * s.length)

-- Randomized PBT for `even_length_prop`.
#eval Plausible.Testable.check (∀ s : String, (duplicate_chars s).length % 2 = 0)

-- Randomized PBT for `index_div_two_prop`.
#eval Plausible.Testable.check (∀ s : String,
  (List.range ((duplicate_chars s).length + 2)).all (fun j =>
    (duplicate_chars s).data[j]? == s.data[j / 2]?))

-- Randomized PBT for `even_index_prop`.
#eval Plausible.Testable.check (∀ s : String,
  (List.range s.length).all (fun i =>
    (duplicate_chars s).data[2 * i]? == s.data[i]?))

-- Randomized PBT for `odd_index_prop`.
#eval Plausible.Testable.check (∀ s : String,
  (List.range s.length).all (fun i =>
    (duplicate_chars s).data[2 * i + 1]? == s.data[i]?))

-- Randomized PBT for `adjacent_eq_prop`.
#eval Plausible.Testable.check (∀ s : String,
  (List.range s.length).all (fun i =>
    (duplicate_chars s).data[2 * i]? == (duplicate_chars s).data[2 * i + 1]?))

-- Randomized PBT for `mem_prop`.
#eval Plausible.Testable.check (∀ (s : String) (c : Char),
  (decide (c ∈ (duplicate_chars s).data)) == (decide (c ∈ s.data)))

-- Randomized PBT for `count_prop`.
#eval Plausible.Testable.check (∀ (s : String) (c : Char),
  (duplicate_chars s).data.count c = 2 * s.data.count c)

-- Randomized PBT for `append_prop`.
#eval Plausible.Testable.check (∀ s₁ s₂ : String,
  duplicate_chars (s₁ ++ s₂) = duplicate_chars s₁ ++ duplicate_chars s₂)

-- Randomized PBT for `injective_prop`.
#eval Plausible.Testable.check (∀ s₁ s₂ : String,
  (duplicate_chars s₁ == duplicate_chars s₂) == (s₁ == s₂))

-- Randomized PBT for `opt_prop`.
#eval Plausible.Testable.check (∀ s? : Option String,
  (duplicate_chars_opt s? == none) == (s? == none))

/-- Executable Boolean check for the combined `Post_prop`. -/
def check_post_bool (s : String) : Bool :=
  ((!(s == "") || (duplicate_chars s == "")) &&
   ((duplicate_chars s == "") == (s == "")) &&
   ((duplicate_chars s).length == 2 * s.length) &&
   ((duplicate_chars s).length % 2 == 0) &&
   (List.range ((duplicate_chars s).length + 1)).all (fun j =>
     (duplicate_chars s).data[j]? == s.data[j / 2]?) &&
   (List.range s.length).all (fun i =>
     (duplicate_chars s).data[2 * i]? == s.data[i]?) &&
   (List.range s.length).all (fun i =>
     (duplicate_chars s).data[2 * i + 1]? == s.data[i]?) &&
   (List.range s.length).all (fun i =>
     (duplicate_chars s).data[2 * i]? == (duplicate_chars s).data[2 * i + 1]?) &&
   s.data.all (fun c => decide (c ∈ (duplicate_chars s).data)) &&
   (duplicate_chars s).data.all (fun c => decide (c ∈ s.data)) &&
   s.data.all (fun c => (duplicate_chars s).data.count c == 2 * s.data.count c))

-- Randomized PBT for `Post_prop`.
#eval Plausible.Testable.check (∀ s : String, check_post_bool s = true)

-- Bounded PBT for `Post_prop` across representative test strings.
example :
    (["", "a", "abc", "!a ", "12345", "aaaa", "Hello, World!"].all check_post_bool) = true := by
  native_decide

/-! ## Correctness Theorem -/

/-- Main correctness theorem: for any input `s` satisfying `Pre s`, `Post_prop s` holds. -/
theorem duplicate_chars_correct (s : String) (_h : Pre s) : Post_prop s :=
  ⟨empty_thm s,
   empty_iff_thm s,
   length_thm s,
   even_length_thm s,
   index_div_two_thm s,
   even_index_thm s,
   odd_index_thm s,
   adjacent_eq_thm s,
   mem_thm s,
   count_thm s⟩

/-! ## Imperative Implementation -/

/-- Imperative implementation of `duplicate_chars` using `Id.run do` and mutable state. -/
def duplicate_chars_imp (s : String) : String := Id.run do
  let mut res : String := ""
  for c in s.data do
    res := res ++ String.mk [c, c]
  return res

/-! ## Imperative Tests -/

example : duplicate_chars_imp "abc" = "aabbcc" := by native_decide
example : duplicate_chars_imp "" = "" := by native_decide
example : duplicate_chars_imp "!a " = "!!aa  " := by native_decide
example : duplicate_chars_imp "x" = "xx" := by native_decide
example : duplicate_chars_imp "123" = "112233" := by native_decide

#eval duplicate_chars_imp "abc"
#eval duplicate_chars_imp ""
#eval duplicate_chars_imp "!a "

/-! ## Equivalence Theorem -/

/-- Auxiliary loop invariant relating the `List.foldl` accumulator to `List.flatMap`. -/
lemma foldl_dup_aux (xs : List Char) (acc : String) :
    List.foldl (fun b a => b ++ String.mk [a, a]) acc xs =
      acc ++ String.mk (xs.flatMap (fun c => [c, c])) := by
  induction xs generalizing acc with
  | nil =>
    ext : 1
    simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.flatMap_cons, ih]
    ext : 1
    simp [List.append_assoc]

/-- Proposition stating functional-imperative equivalence. -/
def equiv_prop (s : String) : Prop :=
  duplicate_chars s = duplicate_chars_imp s

/-- Equivalence theorem: the functional and imperative implementations produce identical results. -/
theorem duplicate_chars_equiv (s : String) : duplicate_chars s = duplicate_chars_imp s := by
  simp [duplicate_chars, duplicate_chars_imp, foldl_dup_aux]

-- Randomized PBT for functional-imperative equivalence.
#eval Plausible.Testable.check (∀ s : String, duplicate_chars s = duplicate_chars_imp s)

end «41_duplicate_chars»
