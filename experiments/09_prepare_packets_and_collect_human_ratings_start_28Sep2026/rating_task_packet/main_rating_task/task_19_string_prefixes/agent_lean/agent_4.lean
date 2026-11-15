import Mathlib

/-!
# HumanEval/14 — all_prefixes

Translation of the Python HumanEval/14 program into Lean 4.

    def all_prefixes(string: str) -> List[str]:
        result = []
        for i in range(len(string)):
            result.append(string[:i+1])
        return result

The function returns every non-empty prefix of the input string, ordered from
shortest to longest. Slicing follows Python 3 str semantics: indices are Unicode
code points. Lean String.length and String.take are character-based
(String.take_eq), so they model that slicing exactly. This is a discrete string
problem; there is no floating-point obligation.
-/

namespace humaneval_14_all_prefixes

/-- Return the list of all prefixes of `string`, from shortest to longest. -/
def allPrefixes (string : String) : List String :=
  (List.range string.length).map fun i => string.take (i + 1)

/-- Python-facing name for the same function. -/
def all_prefixes (string : String) : List String :=
  allPrefixes string

theorem all_prefixes_eq (string : String) : all_prefixes string = allPrefixes string := rfl

/-! ## Unit tests -/

example : allPrefixes "" = [] := by native_decide
example : allPrefixes "abc" = ["a", "ab", "abc"] := by native_decide
example : allPrefixes "asdfgh" =
    ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by
  native_decide
example : allPrefixes "WWW" = ["W", "WW", "WWW"] := by native_decide
example : allPrefixes "he" = ["h", "he"] := by native_decide
example : all_prefixes "abc" = ["a", "ab", "abc"] := by native_decide

#eval allPrefixes ""
#eval allPrefixes "abc"
#eval allPrefixes "asdfgh"
#eval allPrefixes "WWW"

/-! ## Precondition -/

/-- The Python function is total: every string is admissible. -/
def Pre (_string : String) : Prop := True

/-! ## Helper lemmas -/

lemma eq_empty_of_length_eq_zero (s : String) (h : s.length = 0) : s = "" := by
  apply String.ext
  apply List.eq_nil_of_length_eq_zero
  simpa [String.length_data] using h

lemma length_ne_zero_of_ne_empty (s : String) (h : s ≠ "") : s.length ≠ 0 := by
  intro hlen
  exact h (eq_empty_of_length_eq_zero s hlen)

lemma length_pos_of_ne_empty (s : String) (h : s ≠ "") : 0 < s.length := by
  have hne := length_ne_zero_of_ne_empty s h
  omega

lemma take_length_of_le (s : String) {n : Nat} (h : n ≤ s.length) :
    (s.take n).length = n := by
  rw [← String.length_data, String.data_take, List.length_take, String.length_data, Nat.min_eq_left h]

lemma take_self (s : String) : s.take s.length = s := by
  apply String.ext
  rw [String.data_take, ← String.length_data, List.take_length]

lemma take_take_prefix (xs : List Char) {a b : Nat} (h : a ≤ b) :
    xs.take a <+: xs.take b := by
  have hmin : min a b = a := Nat.min_eq_left h
  have htake : xs.take a = (xs.take b).take a := by
    rw [List.take_take, hmin]
  rw [htake]
  exact List.take_prefix a (xs.take b)

lemma nodup_of_nodup_map {α β} {f : α → β} {l : List α}
    (h : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases h with ⟨ hnot, ht ⟩
    rw [List.nodup_cons]
    exact ⟨ fun ha => hnot (List.mem_map_of_mem ha), ih ht ⟩

/-! ## Properties and theorems -/

def spec_prop (s : String) (result : List String) : Prop :=
  result = (List.range s.length).map (fun i => s.take (i + 1))

theorem spec_thm (s : String) : spec_prop s (allPrefixes s) := by
  unfold spec_prop allPrefixes
  rfl

def reference_tests_prop : Prop :=
  allPrefixes "" = [] ∧
  allPrefixes "abc" = ["a", "ab", "abc"] ∧
  allPrefixes "asdfgh" =
    ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] ∧
  allPrefixes "WWW" = ["W", "WW", "WWW"]

theorem reference_tests_thm : reference_tests_prop := by
  unfold reference_tests_prop
  refine ⟨ rfl, rfl, rfl, rfl ⟩

def length_prop (s : String) (result : List String) : Prop :=
  result.length = s.length

theorem length_thm (s : String) : length_prop s (allPrefixes s) := by
  simp [length_prop, allPrefixes]

def empty_iff_prop (s : String) (result : List String) : Prop :=
  result = [] ↔ s = ""

theorem empty_iff_thm (s : String) : empty_iff_prop s (allPrefixes s) := by
  constructor
  · intro h
    have hlen : (allPrefixes s).length = s.length := by
      simpa [length_prop] using length_thm s
    rw [h] at hlen
    simp at hlen
    exact eq_empty_of_length_eq_zero s hlen.symm
  · intro h
    subst h
    rfl

def nth_prefix_prop (s : String) (result : List String) : Prop :=
  ∀ i, i < s.length → result[i]? = some (s.take (i + 1))

theorem nth_prefix_thm (s : String) : nth_prefix_prop s (allPrefixes s) := by
  intro i hi
  unfold allPrefixes
  rw [List.getElem?_map]
  have hlen : i < (List.range s.length).length := by simpa [List.length_range] using hi
  rw [List.getElem?_eq_getElem hlen]
  simp [List.getElem_range]

def mem_iff_prop (s : String) (result : List String) : Prop :=
  ∀ p : String, p ∈ result ↔ ∃ n, 0 < n ∧ n ≤ s.length ∧ p = s.take n

theorem mem_iff_thm (s : String) : mem_iff_prop s (allPrefixes s) := by
  intro p
  unfold allPrefixes
  constructor
  · intro h
    rcases (List.mem_map).1 h with ⟨ i, hi, hp ⟩
    have hi2 : i < s.length := (List.mem_range).1 hi
    exact ⟨ i + 1, Nat.succ_pos i, Nat.succ_le_of_lt hi2, hp.symm ⟩
  · rintro ⟨ n, hn0, hnle, hp ⟩
    have hlt : n - 1 < s.length := by omega
    have hadd : n - 1 + 1 = n := by omega
    rw [List.mem_map]
    refine ⟨ n - 1, (List.mem_range).2 hlt, ?_ ⟩
    simpa [hadd] using hp.symm

def lengths_prop (s : String) (result : List String) : Prop :=
  result.map String.length = (List.range s.length).map (fun i => i + 1)

theorem lengths_thm (s : String) : lengths_prop s (allPrefixes s) := by
  unfold lengths_prop allPrefixes
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi2 : i < s.length := (List.mem_range).1 hi
  simpa using take_length_of_le s (Nat.succ_le_of_lt hi2)

def last_eq_prop (s : String) (result : List String) : Prop :=
  s ≠ "" → result.getLast? = some s

theorem last_eq_thm (s : String) : last_eq_prop s (allPrefixes s) := by
  intro hne
  have hlen0 : s.length ≠ 0 := length_ne_zero_of_ne_empty s hne
  unfold allPrefixes
  rw [List.getLast?_map, List.getLast?_eq_getElem?]
  simp only [List.length_range]
  have hlt : s.length - 1 < (List.range s.length).length := by
    simp [List.length_range]
    omega
  rw [List.getElem?_eq_getElem hlt]
  simp [List.getElem_range hlt]
  have hadd : s.length - 1 + 1 = s.length := by omega
  rw [hadd]
  exact take_self s

def head_prop (s : String) (result : List String) : Prop :=
  s ≠ "" → result.head? = some (s.take 1)

theorem head_thm (s : String) : head_prop s (allPrefixes s) := by
  intro hne
  have hpos : 0 < s.length := length_pos_of_ne_empty s hne
  rw [List.head?_eq_getElem?]
  exact nth_prefix_thm s 0 hpos

def data_isPrefix_prop (s : String) (result : List String) : Prop :=
  ∀ p ∈ result, p.data <+: s.data

theorem data_isPrefix_thm (s : String) : data_isPrefix_prop s (allPrefixes s) := by
  intro p hp
  rcases (mem_iff_thm s p).1 hp with ⟨ n, _, _, rfl ⟩
  rw [String.data_take]
  exact List.take_prefix n s.data

def initial_segments_prop (s : String) (result : List String) : Prop :=
  ∀ p, p ∈ result ↔
    p.data <+: s.data ∧ 0 < p.length ∧ p.length ≤ s.length ∧ p = s.take p.length

theorem initial_segments_thm (s : String) : initial_segments_prop s (allPrefixes s) := by
  intro p
  constructor
  · intro hp
    rcases (mem_iff_thm s p).1 hp with ⟨ n, hn0, hnle, hp ⟩
    have hlenp : p.length = n := by
      rw [hp]
      exact take_length_of_le s hnle
    refine ⟨ ?_, ?_, ?_, ?_ ⟩
    · rw [hp, String.data_take]
      exact List.take_prefix n s.data
    · omega
    · omega
    · rw [hlenp]
      exact hp
  · rintro ⟨ _, hp0, hple, hp ⟩
    exact (mem_iff_thm s p).2 ⟨ p.length, hp0, hple, hp ⟩

def extends_prev_prop (_s : String) (result : List String) : Prop :=
  ∀ i, i + 1 < result.length →
    ∃ a b, result[i]? = some a ∧ result[i + 1]? = some b ∧
      a.data <+: b.data ∧ b.length = a.length + 1

theorem extends_prev_thm (s : String) : extends_prev_prop s (allPrefixes s) := by
  intro i hi
  have hlen : (allPrefixes s).length = s.length := by
    simpa [length_prop] using length_thm s
  have hi1 : i + 1 < s.length := by simpa [hlen] using hi
  have hi0 : i < s.length := Nat.lt_of_succ_lt hi1
  refine ⟨ s.take (i + 1), s.take (i + 2), nth_prefix_thm s i hi0,
    nth_prefix_thm s (i + 1) hi1, ?_, ?_ ⟩
  · rw [String.data_take, String.data_take]
    exact take_take_prefix s.data (Nat.le_succ (i + 1))
  · have ha : (s.take (i + 1)).length = i + 1 :=
      take_length_of_le s (Nat.succ_le_of_lt hi0)
    have hb : (s.take (i + 2)).length = i + 2 :=
      take_length_of_le s (Nat.succ_le_of_lt hi1)
    rw [ha, hb]

def shortest_to_longest_prop (_s : String) (result : List String) : Prop :=
  ∀ i j, i < j → j < result.length →
    ∃ a b, result[i]? = some a ∧ result[j]? = some b ∧ a.length < b.length

theorem shortest_to_longest_thm (s : String) :
    shortest_to_longest_prop s (allPrefixes s) := by
  intro i j hij hj
  have hlen : (allPrefixes s).length = s.length := by
    simpa [length_prop] using length_thm s
  have hj2 : j < s.length := by simpa [hlen] using hj
  have hi2 : i < s.length := by omega
  refine ⟨ s.take (i + 1), s.take (j + 1), nth_prefix_thm s i hi2,
    nth_prefix_thm s j hj2, ?_ ⟩
  have ha : (s.take (i + 1)).length = i + 1 :=
    take_length_of_le s (Nat.succ_le_of_lt hi2)
  have hb : (s.take (j + 1)).length = j + 1 :=
    take_length_of_le s (Nat.succ_le_of_lt hj2)
  rw [ha, hb]
  omega

def no_empty_prefix_prop (_s : String) (result : List String) : Prop :=
  "" ∉ result

theorem no_empty_prefix_thm (s : String) : no_empty_prefix_prop s (allPrefixes s) := by
  intro h
  rcases (mem_iff_thm s "").1 h with ⟨ n, hn0, hnle, heq ⟩
  have hlen := take_length_of_le s hnle
  have hempty : ("" : String).length = 0 := rfl
  rw [← heq, hempty] at hlen
  omega

def nodup_prop (_s : String) (result : List String) : Prop :=
  result.Nodup

theorem nodup_thm (s : String) : nodup_prop s (allPrefixes s) := by
  unfold nodup_prop
  apply nodup_of_nodup_map (f := String.length)
  have heq : (allPrefixes s).map String.length =
      (List.range s.length).map (fun i => i + 1) := by
    simpa [lengths_prop] using lengths_thm s
  rw [heq]
  have hinj : Function.Injective (fun i : Nat => i + 1) := by
    intro a b hab
    exact Nat.add_right_cancel hab
  exact (List.nodup_map_iff hinj).2 List.nodup_range

def one_char_extension_prop (s : String) (result : List String) : Prop :=
  ∀ i, i < result.length →
    ∃ c, result[i]? = some (String.mk (s.data.take i ++ [c])) ∧ s.data[i]? = some c

theorem one_char_extension_thm (s : String) :
    one_char_extension_prop s (allPrefixes s) := by
  intro i hi
  have hlen : (allPrefixes s).length = s.length := by
    simpa [length_prop] using length_thm s
  have hi2 : i < s.length := by omega
  have hc : i < s.data.length := by simpa [String.length_data] using hi2
  refine ⟨ s.data[i]'hc, ?_, List.getElem?_eq_getElem hc ⟩
  have hnth : (allPrefixes s)[i]? = some (s.take (i + 1)) := nth_prefix_thm s i hi2
  rw [hnth]
  apply congrArg some
  apply String.ext
  rw [String.data_take]
  exact (List.take_append_getElem hc).symm

def Post_prop (s : String) (result : List String) : Prop :=
  spec_prop s result ∧
  empty_iff_prop s result ∧
  length_prop s result ∧
  nth_prefix_prop s result ∧
  mem_iff_prop s result ∧
  lengths_prop s result ∧
  last_eq_prop s result ∧
  head_prop s result ∧
  data_isPrefix_prop s result ∧
  initial_segments_prop s result ∧
  extends_prev_prop s result ∧
  shortest_to_longest_prop s result ∧
  no_empty_prefix_prop s result ∧
  nodup_prop s result ∧
  one_char_extension_prop s result

/-! ## Property-based tests -/

def spec_bool (s : String) : Bool :=
  allPrefixes s == (List.range s.length).map (fun i => s.take (i + 1))

def reference_tests_bool : Bool :=
  (allPrefixes "" == []) &&
  (allPrefixes "abc" == ["a", "ab", "abc"]) &&
  (allPrefixes "asdfgh" ==
    ["a", "as", "asd", "asdf", "asdfg", "asdfgh"]) &&
  (allPrefixes "WWW" == ["W", "WW", "WWW"])

def reference_case_bool (k : Nat) : Bool :=
  match k % 4 with
  | 0 => allPrefixes "" == []
  | 1 => allPrefixes "abc" == ["a", "ab", "abc"]
  | 2 => allPrefixes "asdfgh" ==
      ["a", "as", "asd", "asdf", "asdfg", "asdfgh"]
  | _ => allPrefixes "WWW" == ["W", "WW", "WWW"]

def empty_iff_bool (s : String) : Bool :=
  ((allPrefixes s == []) == (s == ""))

def length_bool (s : String) : Bool :=
  (allPrefixes s).length == s.length

def nth_prefix_bool (s : String) : Bool :=
  (List.range s.length).all fun i => (allPrefixes s)[i]? == some (s.take (i + 1))

def mem_iff_bool (s : String) : Bool :=
  let result := allPrefixes s
  let forward := result.all fun p =>
    (List.range s.length).any fun i => p == s.take (i + 1)
  let backward := (List.range s.length).all fun i => result.contains (s.take (i + 1))
  forward && backward

def lengths_bool (s : String) : Bool :=
  (allPrefixes s).map String.length == (List.range s.length).map (fun i => i + 1)

def last_eq_bool (s : String) : Bool :=
  s == "" || (allPrefixes s).getLast? == some s

def head_bool (s : String) : Bool :=
  s == "" || (allPrefixes s).head? == some (s.take 1)

def data_isPrefix_bool (s : String) : Bool :=
  (allPrefixes s).all fun p => p.data.isPrefixOf s.data

def initial_segments_bool (s : String) : Bool :=
  let result := allPrefixes s
  let forward := result.all fun p =>
    p.data.isPrefixOf s.data &&
      decide (0 < p.length) &&
      decide (p.length ≤ s.length) &&
      p == s.take p.length
  let backward := (List.range s.length).all fun i =>
    let p := s.take (i + 1)
    result.contains p && p.data.isPrefixOf s.data && p == s.take p.length
  forward && backward

def extends_prev_bool (s : String) : Bool :=
  let result := allPrefixes s
  (List.range (result.length - 1)).all fun i =>
    match result[i]?, result[i + 1]? with
    | some a, some b => a.data.isPrefixOf b.data && b.length == a.length + 1
    | _, _ => false

def shortest_to_longest_bool (s : String) : Bool :=
  let result := allPrefixes s
  (List.range result.length).all fun j =>
    (List.range j).all fun i =>
      match result[i]?, result[j]? with
      | some a, some b => decide (a.length < b.length)
      | _, _ => false

def no_empty_prefix_bool (s : String) : Bool :=
  !(allPrefixes s).contains ""

def nodup_bool (s : String) : Bool :=
  let result := allPrefixes s
  (List.range result.length).all fun i =>
    (List.range result.length).all fun j =>
      i == j || result[i]! != result[j]!

def one_char_extension_bool (s : String) : Bool :=
  let result := allPrefixes s
  (List.range result.length).all fun i =>
    match s.data[i]? with
    | some c => result[i]? == some (String.mk (s.data.take i ++ [c]))
    | none => false

def post_bool (s : String) : Bool :=
  spec_bool s && empty_iff_bool s && length_bool s && nth_prefix_bool s &&
    mem_iff_bool s && lengths_bool s && last_eq_bool s && head_bool s &&
    data_isPrefix_bool s && initial_segments_bool s && extends_prev_bool s &&
    shortest_to_longest_bool s && no_empty_prefix_bool s && nodup_bool s &&
    one_char_extension_bool s

def smallStrings : List String :=
  (List.range 12).map fun n => String.mk (List.replicate n 'a')

def variedString (n : Nat) : String :=
  String.mk ((List.range n).map fun i => Char.ofNat (97 + i % 26))

example : reference_tests_bool = true := by native_decide
#eval Plausible.Testable.check (∀ k : Nat, reference_case_bool k = true)

#eval Plausible.Testable.check (∀ s : String, spec_bool s = true)
example : smallStrings.all spec_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, empty_iff_bool s = true)
example : smallStrings.all empty_iff_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, length_bool s = true)
example : smallStrings.all length_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, nth_prefix_bool s = true)
example : smallStrings.all nth_prefix_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, mem_iff_bool s = true)
example : smallStrings.all mem_iff_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, lengths_bool s = true)
example : smallStrings.all lengths_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, last_eq_bool s = true)
example : smallStrings.all last_eq_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, head_bool s = true)
example : smallStrings.all head_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, data_isPrefix_bool s = true)
example : smallStrings.all data_isPrefix_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, initial_segments_bool s = true)
example : smallStrings.all initial_segments_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, extends_prev_bool s = true)
example : smallStrings.all extends_prev_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, shortest_to_longest_bool s = true)
example : smallStrings.all shortest_to_longest_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, no_empty_prefix_bool s = true)
example : smallStrings.all no_empty_prefix_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, nodup_bool s = true)
example : smallStrings.all nodup_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, one_char_extension_bool s = true)
example : smallStrings.all one_char_extension_bool = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, post_bool s = true)
example : smallStrings.all post_bool = true := by native_decide
example : (List.range 12).all (fun n => post_bool (variedString n)) = true := by native_decide

theorem correctness_thm (s : String) : Pre s → Post_prop s (allPrefixes s) := by
  intro h
  cases h
  exact ⟨ spec_thm s, empty_iff_thm s, length_thm s, nth_prefix_thm s, mem_iff_thm s,
    lengths_thm s, last_eq_thm s, head_thm s, data_isPrefix_thm s, initial_segments_thm s,
    extends_prev_thm s, shortest_to_longest_thm s, no_empty_prefix_thm s, nodup_thm s,
    one_char_extension_thm s ⟩

theorem all_prefixes_correctness_thm (s : String) :
    Pre s → Post_prop s (all_prefixes s) := by
  simpa [all_prefixes] using correctness_thm s

/-- Imperative translation of the Python loop, using Id.run and mutable state. -/
def allPrefixesImp (string : String) : List String :=
  Id.run do
    let mut result : List String := []
    for i in List.range string.length do
      result := result ++ [string.take (i + 1)]
    return result

example : allPrefixesImp "" = [] := by native_decide
example : allPrefixesImp "abc" = ["a", "ab", "abc"] := by native_decide
example : allPrefixesImp "asdfgh" =
    ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by
  native_decide
example : allPrefixesImp "WWW" = ["W", "WW", "WWW"] := by native_decide
example : allPrefixesImp "he" = ["h", "he"] := by native_decide

#eval allPrefixesImp ""
#eval allPrefixesImp "abc"
#eval allPrefixesImp "asdfgh"
#eval allPrefixesImp "WWW"

example : (List.range 12).all (fun n =>
    allPrefixes (String.mk (List.replicate n 'b')) ==
      allPrefixesImp (String.mk (List.replicate n 'b'))) = true := by
  native_decide

def impMap {α β} (xs : List α) (f : α → β) : List β :=
  Id.run do
    let mut result : List β := []
    for x in xs do
      result := result ++ [f x]
    return result

theorem map_singleton_flatten {α β} (f : α → β) (xs : List α) :
    (xs.map (fun x => [f x])).flatten = xs.map f := by
  induction xs with
  | nil => rfl
  | cons _ t ih => simp [ih]

theorem impMap_eq_map {α β} (xs : List α) (f : α → β) :
    impMap xs f = xs.map f := by
  induction xs with
  | nil => rfl
  | cons _ t ih =>
    simp only [impMap] at ih ⊢
    simp [map_singleton_flatten] at *

theorem equivalence_thm (s : String) : allPrefixes s = allPrefixesImp s := by
  have h := impMap_eq_map (List.range s.length) (fun i => s.take (i + 1))
  have hdef : allPrefixesImp s =
      impMap (List.range s.length) (fun i => s.take (i + 1)) := by
    rfl
  simp [allPrefixes, hdef, h]

theorem imperative_correctness_thm (s : String) (h : Pre s) :
    Post_prop s (allPrefixesImp s) := by
  rw [← equivalence_thm s]
  exact correctness_thm s h

#eval Plausible.Testable.check (∀ s : String, allPrefixes s == allPrefixesImp s)



end humaneval_14_all_prefixes
