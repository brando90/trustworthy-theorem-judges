import Mathlib

/-!
# HumanEval/14: `all_prefixes`

Translation and formal verification of the Python program `humaneval_14_all_prefixes.py`.

Given an input string `s`, `all_prefixes s` returns the list of all non-empty prefixes
of `s` ordered from shortest to longest (`[s.take 1, s.take 2, ..., s.take s.length]`).
-/

namespace humaneval_14_all_prefixes

/-! ## 1. Functional Implementation -/

/-- Return list of all prefixes from shortest to longest of the input string. -/
def all_prefixes (s : String) : List String :=
  (List.range s.length).map (fun i => s.take (i + 1))

/-! ## 2. Unit Tests -/

example : all_prefixes "" = [] := by native_decide

example : all_prefixes "abc" = ["a", "ab", "abc"] := by native_decide

example : all_prefixes "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide

example : all_prefixes "WWW" = ["W", "WW", "WWW"] := by native_decide

example : all_prefixes "x" = ["x"] := by native_decide

#eval all_prefixes ""
#eval all_prefixes "abc"
#eval all_prefixes "asdfgh"
#eval all_prefixes "WWW"

/-! ## 3. Pre-condition -/

/-- Pre-condition for `all_prefixes`: any `String` is a valid input. -/
def Pre (_s : String) : Prop := True

/-! ## 4. Helper Lemmas and Decidable Instances -/

/-- `String.IsPrefix p s` is decidable via prefix decidability on the underlying character lists. -/
instance instDecidableStringIsPrefix (p s : String) : Decidable (String.IsPrefix p s) :=
  inferInstanceAs (Decidable (p.data <+: s.data))

@[simp]
theorem length_all_prefixes (s : String) :
    (all_prefixes s).length = s.length := by
  simp [all_prefixes]

@[simp]
theorem length_take_eq (s : String) (n : Nat) :
    (s.take n).length = min n s.length := by
  rw [← String.length_data, String.data_take, List.length_take, String.length_data]

theorem take_length_self (s : String) :
    s.take s.length = s := by
  ext : 1
  rw [String.data_take, ← String.length_data, List.take_length]

theorem isPrefix_iff_data (p s : String) :
    String.IsPrefix p s ↔ p.data <+: s.data := by
  cases p; cases s; rfl

theorem isPrefix_iff_toList_isPrefixOf (p s : String) :
    p.toList.isPrefixOf s.toList = true ↔ String.IsPrefix p s := by
  cases p; cases s; exact List.isPrefixOf_iff_prefix

theorem empty_iff_data_nil (s : String) :
    s = "" ↔ s.data = [] := by
  cases s; simp [String.ext_iff]

theorem empty_iff_length_zero (s : String) :
    s = "" ↔ s.length = 0 := by
  rw [empty_iff_data_nil, ← String.length_data, List.length_eq_zero_iff]

theorem isPrefix_take_of_le (s : String) {m n : Nat} (h : m ≤ n) :
    String.IsPrefix (s.take m) (s.take n) := by
  rw [isPrefix_iff_data, String.data_take, String.data_take]
  have htake : List.take m (List.take n s.data) = List.take m s.data := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [← htake]
  exact List.take_prefix m (List.take n s.data)

/-! ## 5. Property Propositions and Theorems -/

/-- Property 1: The number of prefixes returned equals the length of the input string. -/
@[reducible]
def length_prop (s : String) : Prop :=
  (all_prefixes s).length = s.length

theorem length_thm (s : String) : length_prop s := by
  simp [length_prop]

/-- Property 2: The output list is empty if and only if the input string is empty. -/
@[reducible]
def empty_prop (s : String) : Prop :=
  (all_prefixes s = [] ↔ s = "") ∧ all_prefixes "" = []

theorem empty_thm (s : String) : empty_prop s := by
  refine ⟨?_, rfl⟩
  rw [← List.length_eq_zero_iff, length_all_prefixes, empty_iff_length_zero]

/-- Property 3: At each valid index `i`, the element `(all_prefixes s)[i]` is `s.take (i + 1)`. -/
@[reducible]
def getElem_prop (s : String) : Prop :=
  ∀ (i : Nat) (h : i < (all_prefixes s).length),
    (all_prefixes s)[i] = s.take (i + 1)

theorem getElem_thm (s : String) : getElem_prop s := by
  intro i h
  simp [all_prefixes]

/-- Property 4: At each valid index `i`, the `i`-th prefix has length `i + 1`. -/
@[reducible]
def elem_length_prop (s : String) : Prop :=
  ∀ (i : Nat) (h : i < (all_prefixes s).length),
    ((all_prefixes s)[i]).length = i + 1

theorem elem_length_thm (s : String) : elem_length_prop s := by
  intro i h
  have hi : i < s.length := by simpa using h
  rw [getElem_thm s i h, length_take_eq]
  omega

/-- Property 5: Every element in `all_prefixes s` is a non-empty prefix of `s` with length in `1..s.length`. -/
@[reducible]
def all_are_prefixes_prop (s : String) : Prop :=
  ∀ p ∈ all_prefixes s,
    String.IsPrefix p s ∧ p.toList.isPrefixOf s.toList = true ∧
    0 < p.length ∧ p.length ≤ s.length ∧ p ≠ ""

theorem all_are_prefixes_thm (s : String) : all_are_prefixes_prop s := by
  intro p hp
  simp only [all_prefixes, List.mem_map, List.mem_range] at hp
  rcases hp with ⟨i, hi, rfl⟩
  have hpref : String.IsPrefix (s.take (i + 1)) s := by
    rw [isPrefix_iff_data, String.data_take]
    exact List.take_prefix (i + 1) s.data
  have hbool : (s.take (i + 1)).toList.isPrefixOf s.toList = true :=
    (isPrefix_iff_toList_isPrefixOf _ _).mpr hpref
  have hlen : (s.take (i + 1)).length = i + 1 := by
    rw [length_take_eq]
    omega
  refine ⟨hpref, hbool, by omega, by omega, ?_⟩
  rw [Ne, empty_iff_length_zero]
  omega

/-- Property 6: Completeness — `all_prefixes s` contains `s.take k` for every `1 ≤ k ≤ s.length`,
and a string `p` belongs to `all_prefixes s` if and only if `p` is a non-empty prefix of `s`. -/
def completeness_prop (s : String) : Prop :=
  (∀ (k : Nat), 0 < k → k ≤ s.length → s.take k ∈ all_prefixes s) ∧
  (∀ (p : String), p ∈ all_prefixes s ↔ (p ≠ "" ∧ String.IsPrefix p s))

theorem completeness_thm (s : String) : completeness_prop s := by
  have h1 : ∀ (k : Nat), 0 < k → k ≤ s.length → s.take k ∈ all_prefixes s := by
    intro k hkpos hkle
    simp only [all_prefixes, List.mem_map, List.mem_range]
    refine ⟨k - 1, by omega, ?_⟩
    congr 1
    omega
  refine ⟨h1, fun p => ⟨?_, ?_⟩⟩
  · intro hp
    have H := all_are_prefixes_thm s p hp
    exact ⟨H.2.2.2.2, H.1⟩
  · rintro ⟨hne, hpref⟩
    rw [Ne, empty_iff_length_zero] at hne
    rw [isPrefix_iff_data] at hpref
    have hlen_le : p.length ≤ s.length := by
      rw [← String.length_data, ← String.length_data]
      exact hpref.length_le
    have htake : s.take p.length = p := by
      ext : 1
      rw [String.data_take, ← String.length_data, ← List.prefix_iff_eq_take.mp hpref]
    rw [← htake]
    exact h1 p.length (Nat.pos_of_ne_zero hne) hlen_le

/-- Property 7: Prefixes are strictly ordered from shortest to longest. -/
@[reducible]
def shortest_to_longest_prop (s : String) : Prop :=
  (∀ (i : Nat) (hi : i < (all_prefixes s).length) (j : Nat) (hj : j < (all_prefixes s).length),
    i < j → ((all_prefixes s)[i]).length < ((all_prefixes s)[j]).length) ∧
  List.Pairwise (fun a b => a.length < b.length) (all_prefixes s)

theorem shortest_to_longest_thm (s : String) : shortest_to_longest_prop s := by
  have hidx : ∀ (i : Nat) (hi : i < (all_prefixes s).length) (j : Nat) (hj : j < (all_prefixes s).length),
      i < j → ((all_prefixes s)[i]).length < ((all_prefixes s)[j]).length := by
    intro i hi j hj hij
    rw [elem_length_thm s i hi, elem_length_thm s j hj]
    omega
  refine ⟨hidx, ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  exact hidx i hi j hj hij

/-- Property 8: Earlier elements in `all_prefixes s` are prefixes of later elements. -/
@[reducible]
def prefix_chain_prop (s : String) : Prop :=
  (∀ (i : Nat) (hi : i < (all_prefixes s).length) (j : Nat) (hj : j < (all_prefixes s).length),
    i ≤ j → String.IsPrefix ((all_prefixes s)[i]) ((all_prefixes s)[j])) ∧
  List.Pairwise String.IsPrefix (all_prefixes s)

theorem prefix_chain_thm (s : String) : prefix_chain_prop s := by
  have hidx : ∀ (i : Nat) (hi : i < (all_prefixes s).length) (j : Nat) (hj : j < (all_prefixes s).length),
      i ≤ j → String.IsPrefix ((all_prefixes s)[i]) ((all_prefixes s)[j]) := by
    intro i hi j hj hij
    rw [getElem_thm s i hi, getElem_thm s j hj]
    exact isPrefix_take_of_le s (by omega)
  refine ⟨hidx, ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  exact hidx i hi j hj (Nat.le_of_lt hij)

/-- Property 9: For any non-empty string `s`, the first prefix is `s.take 1` and the last prefix is `s`. -/
@[reducible]
def first_last_prop (s : String) : Prop :=
  s ≠ "" → (all_prefixes s).head? = some (s.take 1) ∧ (all_prefixes s).getLast? = some s

theorem first_last_thm (s : String) : first_last_prop s := by
  intro hne
  have hlen : 0 < s.length := by
    rw [Ne, empty_iff_length_zero] at hne
    omega
  constructor
  · rw [List.head?_eq_getElem?]
    simp [all_prefixes, hlen]
  · rw [List.getLast?_eq_getElem?]
    have hlast : (all_prefixes s).length - 1 < (all_prefixes s).length := by
      rw [length_all_prefixes]
      omega
    rw [List.getElem?_eq_getElem hlast]
    congr 1
    rw [getElem_thm s ((all_prefixes s).length - 1) hlast]
    have h1 : (all_prefixes s).length - 1 + 1 = s.length := by
      rw [length_all_prefixes]
      omega
    rw [h1, take_length_self]

/-- Property 10: All elements in `all_prefixes s` are distinct (no duplicates). -/
@[reducible]
def nodup_prop (s : String) : Prop :=
  (all_prefixes s).Nodup

theorem nodup_thm (s : String) : nodup_prop s := by
  rw [nodup_prop, List.Nodup]
  exact (shortest_to_longest_thm s).2.imp (fun h => by intro heq; rw [heq] at h; exact Nat.lt_irrefl _ h)

/-- Property 11: Prefix truncation compatibility — `all_prefixes (s.take k) = (all_prefixes s).take k`
for all `k ≤ s.length`. -/
@[reducible]
def prefix_truncation_prop (s : String) : Prop :=
  ∀ (k : Nat), k ≤ s.length → all_prefixes (s.take k) = (all_prefixes s).take k

theorem prefix_truncation_thm (s : String) : prefix_truncation_prop s := by
  intro k hk
  have hlen : (s.take k).length = k := by
    rw [length_take_eq, Nat.min_eq_left hk]
  rw [all_prefixes, all_prefixes, hlen, ← List.map_take, List.take_range, Nat.min_eq_left hk]
  refine List.map_congr_left ?_
  intro i hi
  rw [List.mem_range] at hi
  ext : 1
  rw [String.data_take, String.data_take, String.data_take, List.take_take, Nat.min_eq_left (by omega)]

/-! ## 6. Post-condition -/

/-- Post-condition combining all semantic properties of `all_prefixes`. -/
def Post_prop (s : String) : Prop :=
  length_prop s ∧
  empty_prop s ∧
  getElem_prop s ∧
  elem_length_prop s ∧
  all_are_prefixes_prop s ∧
  completeness_prop s ∧
  shortest_to_longest_prop s ∧
  prefix_chain_prop s ∧
  first_last_prop s ∧
  nodup_prop s ∧
  prefix_truncation_prop s

/-! ## 7. Property-Based Tests (PBTs) -/

/-- Representative sample of test strings for bounded exhaustive checking. -/
def sampleStrings : List String :=
  ["", "a", "ab", "abc", "asdfgh", "WWW", "hello world", "0123456789", "aaa", "Lean4"]

/-- Executable Boolean check for `completeness_prop` on a string `s` and candidate `p`. -/
def completenessCheck (s : String) : Bool :=
  (List.range s.length).all (fun i => decide (s.take (i + 1) ∈ all_prefixes s)) &&
  (sampleStrings ++ all_prefixes s).all (fun p =>
    decide (p ∈ all_prefixes s) == (decide (p ≠ "") && decide (String.IsPrefix p s)))

/-- Executable Boolean check for the full `Post_prop`. -/
def postCheck (s : String) : Bool :=
  decide (length_prop s) &&
  decide (empty_prop s) &&
  decide (getElem_prop s) &&
  decide (elem_length_prop s) &&
  decide (all_are_prefixes_prop s) &&
  completenessCheck s &&
  decide (shortest_to_longest_prop s) &&
  decide (prefix_chain_prop s) &&
  decide (first_last_prop s) &&
  decide (nodup_prop s) &&
  decide (prefix_truncation_prop s)

-- Randomized PBTs via Plausible
#eval Plausible.Testable.check (∀ s : String, length_prop s)
#eval Plausible.Testable.check (∀ s : String, empty_prop s)
#eval Plausible.Testable.check (∀ s : String, getElem_prop s)
#eval Plausible.Testable.check (∀ s : String, elem_length_prop s)
#eval Plausible.Testable.check (∀ s : String, all_are_prefixes_prop s)
#eval Plausible.Testable.check (∀ s : String, completenessCheck s = true)
#eval Plausible.Testable.check (∀ s p : String, decide (p ∈ all_prefixes s) = decide (p ≠ "" ∧ String.IsPrefix p s))
#eval Plausible.Testable.check (∀ s : String, shortest_to_longest_prop s)
#eval Plausible.Testable.check (∀ s : String, prefix_chain_prop s)
#eval Plausible.Testable.check (∀ s : String, first_last_prop s)
#eval Plausible.Testable.check (∀ s : String, nodup_prop s)
#eval Plausible.Testable.check (∀ s : String, prefix_truncation_prop s)
#eval Plausible.Testable.check (∀ s : String, postCheck s = true)

-- Bounded PBTs via `native_decide`
example : sampleStrings.all (fun s => decide (length_prop s)) = true := by native_decide
example : sampleStrings.all (fun s => decide (empty_prop s)) = true := by native_decide
example : sampleStrings.all (fun s => decide (getElem_prop s)) = true := by native_decide
example : sampleStrings.all (fun s => decide (elem_length_prop s)) = true := by native_decide
example : sampleStrings.all (fun s => decide (all_are_prefixes_prop s)) = true := by native_decide
example : sampleStrings.all (fun s => completenessCheck s) = true := by native_decide
example : sampleStrings.all (fun s => decide (shortest_to_longest_prop s)) = true := by native_decide
example : sampleStrings.all (fun s => decide (prefix_chain_prop s)) = true := by native_decide
example : sampleStrings.all (fun s => decide (first_last_prop s)) = true := by native_decide
example : sampleStrings.all (fun s => decide (nodup_prop s)) = true := by native_decide
example : sampleStrings.all (fun s => decide (prefix_truncation_prop s)) = true := by native_decide
example : sampleStrings.all (fun s => postCheck s) = true := by native_decide

/-! ## 8. Correctness Theorem (`Pre -> Post`) -/

/-- Total correctness theorem: `Pre s → Post_prop s` holds for every input string `s`. -/
theorem all_prefixes_correct (s : String) (_hPre : Pre s) : Post_prop s :=
  ⟨length_thm s,
   empty_thm s,
   getElem_thm s,
   elem_length_thm s,
   all_are_prefixes_thm s,
   completeness_thm s,
   shortest_to_longest_thm s,
   prefix_chain_thm s,
   first_last_thm s,
   nodup_thm s,
   prefix_truncation_thm s⟩

/-! ## 9. Imperative Implementation -/

/-- Imperative implementation of `all_prefixes` using `Id.run do` and mutable state,
mirroring the Python loop `for i in range(len(string)): result.append(string[:i+1])`. -/
def all_prefixes_imp (s : String) : List String := Id.run do
  let mut result : List String := []
  for i in List.range s.length do
    result := result ++ [s.take (i + 1)]
  return result

/-! ## 10. Imperative Tests -/

example : all_prefixes_imp "" = [] := by native_decide

example : all_prefixes_imp "abc" = ["a", "ab", "abc"] := by native_decide

example : all_prefixes_imp "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide

example : all_prefixes_imp "WWW" = ["W", "WW", "WWW"] := by native_decide

example : sampleStrings.all (fun s => all_prefixes s == all_prefixes_imp s) = true := by native_decide

#eval all_prefixes_imp ""
#eval all_prefixes_imp "abc"
#eval all_prefixes_imp "asdfgh"
#eval all_prefixes_imp "WWW"
#eval Plausible.Testable.check (∀ s : String, all_prefixes s = all_prefixes_imp s)

/-! ## 11. Equivalence Theorem (Functional = Imperative) -/

theorem flatten_map_singleton {α β : Type*} (f : α → β) (l : List α) :
    (l.map (fun x => [f x])).flatten = l.map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [ih]

/-- Equivalence theorem: the functional and imperative implementations produce identical results
for all input strings `s`. -/
theorem all_prefixes_eq_imp (s : String) :
    all_prefixes s = all_prefixes_imp s := by
  simp [all_prefixes, all_prefixes_imp, flatten_map_singleton]

/-- Corollary: the imperative implementation also satisfies `Post_prop`. -/
theorem all_prefixes_imp_correct (s : String) (hPre : Pre s) : Post_prop s :=
  all_prefixes_correct s hPre

end humaneval_14_all_prefixes
