import Mathlib

/-!
# HumanEval/14: all_prefixes

This file formalizes the Python function `all_prefixes` from HumanEval/14.
Given an input string, `all_prefixes` returns the list of all non-empty prefixes
of the string ordered from shortest to longest.
-/

namespace humaneval_14_all_prefixes

/-! ## Functional Implementation -/

/-- Return list of all prefixes from shortest to longest of the input string. -/
def all_prefixes (string : String) : List String :=
  (List.range string.length).map (fun i => String.mk (string.data.take (i + 1)))

/-! ## Unit Tests -/

example : all_prefixes "abc" = ["a", "ab", "abc"] := by native_decide
example : all_prefixes "" = [] := by native_decide
example : all_prefixes "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide
example : all_prefixes "WWW" = ["W", "WW", "WWW"] := by native_decide

#eval all_prefixes "abc"
#eval all_prefixes ""
#eval all_prefixes "asdfgh"
#eval all_prefixes "WWW"

/-! ## Helper Lemmas -/

@[simp]
theorem length_mk (d : List Char) : (String.mk d).length = d.length := rfl

@[simp]
theorem data_mk (d : List Char) : (String.mk d).data = d := rfl

@[simp]
theorem mk_data (s : String) : String.mk s.data = s := by
  cases s
  rfl

@[simp]
theorem length_data (s : String) : s.data.length = s.length := rfl

@[simp]
theorem mk_eq_empty_iff (d : List Char) : String.mk d = "" ↔ d = [] := by
  constructor
  · intro h
    exact congrArg String.data h
  · rintro rfl
    rfl

/-! ## Pre-condition -/

/-- Pre-condition for `all_prefixes`: any `String` is admissible. -/
def Pre (_string : String) : Prop := True

/-! ## Properties and Theorems -/

/-- The number of returned prefixes equals the length of the input string. -/
def length_prop (string : String) : Prop :=
  (all_prefixes string).length = string.length

theorem length_thm (string : String) : length_prop string := by
  simp [length_prop, all_prefixes]

/-- The returned list is empty if and only if the input string is empty. -/
def empty_iff_prop (string : String) : Prop :=
  (all_prefixes string = []) ↔ (string = "")

theorem empty_iff_thm (string : String) : empty_iff_prop string := by
  cases string with
  | mk d =>
    simp [empty_iff_prop, all_prefixes]

/-- At each valid index `i`, the `i`-th element is the prefix of length `i + 1`. -/
def get_elem_prop (string : String) : Prop :=
  ∀ (i : Nat) (h : i < (all_prefixes string).length),
    (all_prefixes string)[i] = String.mk (string.data.take (i + 1)) ∧
    ((all_prefixes string)[i]).length = i + 1

theorem get_elem_thm (string : String) : get_elem_prop string := by
  intro i h
  have hi : i < string.length := by simpa [all_prefixes] using h
  simp only [all_prefixes, List.getElem_map, List.getElem_range, length_mk,
    List.length_take, length_data, true_and]
  omega

/-- Every element in `all_prefixes string` is a non-empty prefix of `string`. -/
def elements_are_prefixes_prop (string : String) : Prop :=
  ∀ p ∈ all_prefixes string, p.data <+: string.data ∧ 1 ≤ p.length ∧ p.length ≤ string.length

theorem elements_are_prefixes_thm (string : String) : elements_are_prefixes_prop string := by
  intro p hp
  simp only [all_prefixes, List.mem_map, List.mem_range] at hp
  rcases hp with ⟨i, hi, rfl⟩
  refine ⟨List.take_prefix (i + 1) string.data, ?_, ?_⟩
  · simp only [length_mk, List.length_take, length_data]
    omega
  · simp only [length_mk, List.length_take, length_data]
    omega

/-- Every prefix of length `k + 1` (for `k < string.length`) is present in `all_prefixes string`. -/
def all_prefixes_complete_prop (string : String) : Prop :=
  ∀ (k : Nat), k < string.length → String.mk (string.data.take (k + 1)) ∈ all_prefixes string

theorem all_prefixes_complete_thm (string : String) : all_prefixes_complete_prop string := by
  intro k hk
  simp only [all_prefixes, List.mem_map, List.mem_range]
  exact ⟨k, hk, rfl⟩

/-- A string `p` belongs to `all_prefixes string` iff `p` is a non-empty prefix of `string`. -/
def prefix_mem_iff_prop (string : String) : Prop :=
  ∀ p : String, p ∈ all_prefixes string ↔ (p.data <+: string.data ∧ 1 ≤ p.length)

theorem prefix_mem_iff_thm (string : String) : prefix_mem_iff_prop string := by
  intro p
  constructor
  · intro hp
    have h := elements_are_prefixes_thm string p hp
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hpref, hlen1⟩
    have hle : p.length ≤ string.length := by
      simpa using hpref.length_le
    have htake : p.data = string.data.take p.length := by
      simpa using List.prefix_iff_eq_take.mp hpref
    simp only [all_prefixes, List.mem_map, List.mem_range]
    refine ⟨p.length - 1, by omega, ?_⟩
    have hsub : p.length - 1 + 1 = p.length := by omega
    rw [hsub, ← htake, mk_data]

/-- Prefixes are ordered strictly from shortest to longest, and earlier elements are prefixes of later elements. -/
def shortest_to_longest_prop (string : String) : Prop :=
  ∀ (i : Nat) (hi : i < (all_prefixes string).length)
    (j : Nat) (hj : j < (all_prefixes string).length),
    i < j →
      ((all_prefixes string)[i]).length < ((all_prefixes string)[j]).length ∧
      ((all_prefixes string)[i]).data <+: ((all_prefixes string)[j]).data

theorem shortest_to_longest_thm (string : String) : shortest_to_longest_prop string := by
  intro i hi j hj hij
  have hi' : i < string.length := by simpa [all_prefixes] using hi
  have hj' : j < string.length := by simpa [all_prefixes] using hj
  simp only [all_prefixes, List.getElem_map, List.getElem_range, length_mk, data_mk,
    List.length_take, length_data]
  constructor
  · omega
  · have htake : List.take (i + 1) (List.take (j + 1) string.data) = List.take (i + 1) string.data := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [← htake]
    exact List.take_prefix (i + 1) (List.take (j + 1) string.data)

/-- For any non-empty input string, the last element of `all_prefixes string` is `string` itself. -/
def last_elem_prop (string : String) : Prop :=
  string ≠ "" → (all_prefixes string).getLast? = some string

theorem last_elem_thm (string : String) : last_elem_prop string := by
  intro hs
  have hpos : 0 < string.length := by
    cases string with
    | mk d =>
      cases d with
      | nil => contradiction
      | cons c cs => exact Nat.succ_pos _
  have hne : all_prefixes string ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp [all_prefixes] at hlen
    omega
  rw [List.getLast?_eq_some_getLast hne, Option.some.injEq]
  rw [List.getLast_eq_getElem]
  simp only [all_prefixes, List.length_map, List.length_range, List.getElem_map, List.getElem_range]
  have hsub : string.length - 1 + 1 = string.data.length := by
    rw [length_data]
    omega
  rw [hsub, List.take_length, mk_data]

/-! ## Post-condition -/

/-- Complete post-condition for `all_prefixes` as the conjunction of all properties. -/
def Post_prop (string : String) : Prop :=
  length_prop string ∧
  empty_iff_prop string ∧
  get_elem_prop string ∧
  elements_are_prefixes_prop string ∧
  all_prefixes_complete_prop string ∧
  prefix_mem_iff_prop string ∧
  shortest_to_longest_prop string ∧
  last_elem_prop string

/-! ## Property-Based Tests -/

instance (s : String) : Decidable (length_prop s) :=
  inferInstanceAs (Decidable ((all_prefixes s).length = s.length))

instance (s : String) : Decidable (empty_iff_prop s) :=
  inferInstanceAs (Decidable ((all_prefixes s = []) ↔ (s = "")))

instance (s : String) : Decidable (get_elem_prop s) :=
  Nat.decidableBallLT (all_prefixes s).length (fun i _ =>
    (all_prefixes s)[i] = String.mk (s.data.take (i + 1)) ∧
    ((all_prefixes s)[i]).length = i + 1)

instance (s : String) : Decidable (elements_are_prefixes_prop s) :=
  inferInstanceAs (Decidable (∀ p ∈ all_prefixes s, p.data <+: s.data ∧ 1 ≤ p.length ∧ p.length ≤ s.length))

instance (s : String) : Decidable (all_prefixes_complete_prop s) :=
  Nat.decidableBallLT s.length (fun k _ =>
    String.mk (s.data.take (k + 1)) ∈ all_prefixes s)

instance (s : String) : Decidable (prefix_mem_iff_prop s) :=
  decidable_of_iff (elements_are_prefixes_prop s ∧ all_prefixes_complete_prop s) <| by
    constructor
    · rintro ⟨helem, hcomp⟩ p
      constructor
      · intro hp
        have h := helem p hp
        exact ⟨h.1, h.2.1⟩
      · rintro ⟨hpref, hlen1⟩
        have hle : p.length ≤ s.length := by simpa using hpref.length_le
        have htake : p.data = s.data.take p.length := by
          simpa using List.prefix_iff_eq_take.mp hpref
        have hk : p.length - 1 < s.length := by omega
        have hmem := hcomp (p.length - 1) hk
        have hsub : p.length - 1 + 1 = p.length := by omega
        rwa [hsub, ← htake, mk_data] at hmem
    · intro hiff
      refine ⟨?_, ?_⟩
      · intro p hp
        have ⟨hpref, hlen1⟩ := (hiff p).mp hp
        exact ⟨hpref, hlen1, by simpa using hpref.length_le⟩
      · intro k hk
        apply (hiff (String.mk (s.data.take (k + 1)))).mpr
        refine ⟨List.take_prefix (k + 1) s.data, ?_⟩
        simp only [length_mk, List.length_take, length_data]
        omega

instance (s : String) : Decidable (shortest_to_longest_prop s) :=
  Nat.decidableBallLT (all_prefixes s).length (fun i _ =>
    ∀ (j : Nat) (hj : j < (all_prefixes s).length),
      i < j →
        ((all_prefixes s)[i]).length < ((all_prefixes s)[j]).length ∧
        ((all_prefixes s)[i]).data <+: ((all_prefixes s)[j]).data)

instance (s : String) : Decidable (last_elem_prop s) :=
  inferInstanceAs (Decidable (s ≠ "" → (all_prefixes s).getLast? = some s))

instance (s : String) : Decidable (Post_prop s) :=
  inferInstanceAs (Decidable (
    length_prop s ∧
    empty_iff_prop s ∧
    get_elem_prop s ∧
    elements_are_prefixes_prop s ∧
    all_prefixes_complete_prop s ∧
    prefix_mem_iff_prop s ∧
    shortest_to_longest_prop s ∧
    last_elem_prop s))

#eval Plausible.Testable.check (∀ s : String, length_prop s)
#eval Plausible.Testable.check (∀ s : String, empty_iff_prop s)
#eval Plausible.Testable.check (∀ s : String, get_elem_prop s)
#eval Plausible.Testable.check (∀ s : String, elements_are_prefixes_prop s)
#eval Plausible.Testable.check (∀ s : String, all_prefixes_complete_prop s)
#eval Plausible.Testable.check (∀ s : String, prefix_mem_iff_prop s)
#eval Plausible.Testable.check (∀ (s p : String), p ∈ all_prefixes s ↔ (p.data <+: s.data ∧ 1 ≤ p.length))
#eval Plausible.Testable.check (∀ s : String, shortest_to_longest_prop s)
#eval Plausible.Testable.check (∀ s : String, last_elem_prop s)
#eval Plausible.Testable.check (∀ s : String, Post_prop s)

/-- Sample test strings for bounded property-based checks. -/
def sample_strings : List String :=
  ["", "a", "ab", "abc", "asdfgh", "WWW", "hello world", "0123456789"]

example : sample_strings.all (fun s => decide (length_prop s)) = true := by native_decide
example : sample_strings.all (fun s => decide (empty_iff_prop s)) = true := by native_decide
example : sample_strings.all (fun s => decide (get_elem_prop s)) = true := by native_decide
example : sample_strings.all (fun s => decide (elements_are_prefixes_prop s)) = true := by native_decide
example : sample_strings.all (fun s => decide (all_prefixes_complete_prop s)) = true := by native_decide
example : sample_strings.all (fun s => decide (prefix_mem_iff_prop s)) = true := by native_decide
example : sample_strings.all (fun s => decide (shortest_to_longest_prop s)) = true := by native_decide
example : sample_strings.all (fun s => decide (last_elem_prop s)) = true := by native_decide
example : sample_strings.all (fun s => decide (Post_prop s)) = true := by native_decide

/-! ## Correctness Theorem -/

/-- Main correctness theorem: the pre-condition implies the full post-condition. -/
theorem all_prefixes_correct (string : String) (_hpre : Pre string) : Post_prop string :=
  ⟨length_thm string,
   empty_iff_thm string,
   get_elem_thm string,
   elements_are_prefixes_thm string,
   all_prefixes_complete_thm string,
   prefix_mem_iff_thm string,
   shortest_to_longest_thm string,
   last_elem_thm string⟩

/-! ## Imperative Implementation -/

/-- Imperative implementation of `all_prefixes` translating the Python loop directly. -/
def all_prefixes_imp (string : String) : List String := Id.run do
  let mut result : List String := []
  for i in List.range string.length do
    result := result ++ [String.mk (string.data.take (i + 1))]
  return result

/-! ## Imperative Tests -/

example : all_prefixes_imp "abc" = ["a", "ab", "abc"] := by native_decide
example : all_prefixes_imp "" = [] := by native_decide
example : all_prefixes_imp "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide
example : all_prefixes_imp "WWW" = ["W", "WW", "WWW"] := by native_decide

#eval all_prefixes_imp "abc"
#eval all_prefixes_imp ""
#eval all_prefixes_imp "asdfgh"
#eval all_prefixes_imp "WWW"

/-! ## Equivalence Theorem -/

theorem flatten_map_singleton {α β : Type*} (f : α → β) (l : List α) :
    (l.map (fun x => [f x])).flatten = l.map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [ih]

/-- The functional and imperative implementations of `all_prefixes` are equivalent. -/
theorem all_prefixes_eq_imp (string : String) : all_prefixes string = all_prefixes_imp string := by
  simp [all_prefixes, all_prefixes_imp, flatten_map_singleton]

#eval Plausible.Testable.check (∀ s : String, all_prefixes s = all_prefixes_imp s)

end humaneval_14_all_prefixes
