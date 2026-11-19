/-!
# HumanEval/12: `longest`

This is a Lean 4 translation of `humaneval_12_longest.py`. It returns the
longest string in a list, the first one when several are equally long, and
`none` when the list is empty.

The file uses only core Lean 4 (no Mathlib).

* `maxLen`        corresponds to `max(len(x) for x in strings)`
* `firstOfLength` corresponds to `for s in strings: if len(s) == maxlen: return s`
* `longest`       corresponds to `longest` (`Optional[str]` becomes `Option String`)

Python metadata: author `jt`, dataset `test`.
-/

namespace HumanEval12

/-- `max(len(x) for x in strings)`. It returns `0` on the empty list, but the
Python code never calls `max` on an empty list. -/
def maxLen : List String → Nat
  | [] => 0
  | s :: rest => max s.length (maxLen rest)

/-- The loop `for s in strings: if len(s) == maxlen: return s`.
Reaching the end of the loop without returning gives `none`. -/
def firstOfLength (n : Nat) : List String → Option String
  | [] => none
  | s :: rest => if s.length = n then some s else firstOfLength n rest

/-- Out of a list of strings, return the longest one. Return the first one in
case of multiple strings of the same length. Return `none` in case the input
list is empty. -/
def longest (strings : List String) : Option String :=
  match strings with
  | [] => none
  | _ :: _ =>
    let maxlen := maxLen strings
    firstOfLength maxlen strings

/-! ## Unit tests (the Python `check` function) -/

#guard longest [] == none
#guard longest ["x", "y", "z"] == some "x"
#guard longest ["x", "yyy", "zzzz", "www", "kkkk", "abc"] == some "zzzz"
#guard longest [""] == some ""
#guard longest ["x"] == some "x"

/-! ## Lemmas about `maxLen` -/

/-- Every string in the list is at most `maxLen` long. -/
theorem length_le_maxLen {t : String} {l : List String} (h : t ∈ l) :
    t.length ≤ maxLen l := by
  induction l with
  | nil => simp at h
  | cons s rest ih =>
    show t.length ≤ max s.length (maxLen rest)
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := ih h'
      omega

/-- In a nonempty list, `maxLen` is reached by some string. -/
theorem exists_mem_length_eq_maxLen {l : List String} (h : l ≠ []) :
    ∃ t ∈ l, t.length = maxLen l := by
  induction l with
  | nil => exact (h rfl).elim
  | cons s rest ih =>
    by_cases hs : maxLen rest ≤ s.length
    · refine ⟨s, List.mem_cons.mpr (Or.inl rfl), ?_⟩
      show s.length = max s.length (maxLen rest)
      omega
    · have hrest : rest ≠ [] := by
        intro hr
        subst hr
        exact hs (by simp [maxLen])
      obtain ⟨t, ht, hlen⟩ := ih hrest
      refine ⟨t, List.mem_cons.mpr (Or.inr ht), ?_⟩
      show t.length = max s.length (maxLen rest)
      omega

/-! ## Lemmas about the search loop `firstOfLength` -/

/-- If the loop returns `a`, then `a` has length `n`, and every string before
`a` has a different length. -/
theorem firstOfLength_eq_some {n : Nat} {a : String} {l : List String}
    (h : firstOfLength n l = some a) :
    a.length = n ∧ ∃ pre post, l = pre ++ a :: post ∧ ∀ x ∈ pre, x.length ≠ n := by
  induction l with
  | nil => simp [firstOfLength] at h
  | cons b rest ih =>
    simp only [firstOfLength] at h
    by_cases hb : b.length = n
    · rw [if_pos hb] at h
      cases h
      exact ⟨hb, [], rest, rfl, by simp⟩
    · rw [if_neg hb] at h
      obtain ⟨ha, pre, post, hl, hpre⟩ := ih h
      refine ⟨ha, b :: pre, post, by simp [hl], ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hb
      · exact hpre x hx'

/-- If some string in the list has length `n`, the loop does not return `none`. -/
theorem firstOfLength_ne_none {n : Nat} {x : String} {l : List String}
    (hx : x ∈ l) (hlen : x.length = n) : firstOfLength n l ≠ none := by
  induction l with
  | nil => simp at hx
  | cons b rest ih =>
    simp only [firstOfLength]
    by_cases hb : b.length = n
    · rw [if_pos hb]
      simp
    · rw [if_neg hb]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact absurd hlen hb
      · exact ih hx'

/-- The loop returns the first string whose length is `n`. -/
theorem firstOfLength_of_split {n : Nat} {s : String} {pre post : List String}
    (hpre : ∀ x ∈ pre, x.length ≠ n) (hs : s.length = n) :
    firstOfLength n (pre ++ s :: post) = some s := by
  induction pre with
  | nil =>
    simp only [List.nil_append, firstOfLength]
    rw [if_pos hs]
  | cons b rest ih =>
    have hb : ¬ b.length = n := hpre b (List.mem_cons.mpr (Or.inl rfl))
    simp only [List.cons_append, firstOfLength]
    rw [if_neg hb]
    exact ih (fun x hx => hpre x (List.mem_cons.mpr (Or.inr hx)))

/-! ## Theorems about `longest` -/

/-- `longest` is "compute the maximum length, then search for it". -/
theorem longest_eq (l : List String) : longest l = firstOfLength (maxLen l) l := by
  cases l <;> rfl

/-- The empty list gives `none`. -/
theorem longest_nil : longest [] = none := rfl

/-- `longest` returns `none` exactly when the input is empty. -/
theorem longest_eq_none_iff (l : List String) : longest l = none ↔ l = [] := by
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons s rest =>
      obtain ⟨t, ht, hlen⟩ := exists_mem_length_eq_maxLen (l := s :: rest) (by simp)
      rw [longest_eq] at h
      exact absurd h (firstOfLength_ne_none ht hlen)
  · rintro rfl
    rfl

/-- The result is an element of the input. -/
theorem longest_mem {l : List String} {s : String} (h : longest l = some s) : s ∈ l := by
  rw [longest_eq] at h
  obtain ⟨-, pre, post, hl, -⟩ := firstOfLength_eq_some h
  rw [hl]
  simp

/-- The result's length equals the maximum length. -/
theorem longest_length {l : List String} {s : String} (h : longest l = some s) :
    s.length = maxLen l := by
  rw [longest_eq] at h
  exact (firstOfLength_eq_some h).1

/-- No string in the input is longer than the result. -/
theorem longest_is_longest {l : List String} {s : String} (h : longest l = some s) :
    ∀ t ∈ l, t.length ≤ s.length := by
  intro t ht
  rw [longest_length h]
  exact length_le_maxLen ht

/-- Ties go to the first string: every string before the result is strictly
shorter than it. -/
theorem longest_first {l : List String} {s : String} (h : longest l = some s) :
    ∃ pre post, l = pre ++ s :: post ∧ ∀ t ∈ pre, t.length < s.length := by
  have hs := longest_length h
  rw [longest_eq] at h
  obtain ⟨-, pre, post, hl, hpre⟩ := firstOfLength_eq_some h
  refine ⟨pre, post, hl, ?_⟩
  intro t ht
  have hle : t.length ≤ maxLen l := length_le_maxLen (by rw [hl]; simp [ht])
  have hne : t.length ≠ maxLen l := hpre t ht
  omega

/-- Converse: a string of maximal length with only strictly shorter strings
before it is the result. -/
theorem longest_eq_some_of {pre post : List String} {s : String}
    (hmax : ∀ t ∈ pre ++ s :: post, t.length ≤ s.length)
    (hpre : ∀ t ∈ pre, t.length < s.length) :
    longest (pre ++ s :: post) = some s := by
  obtain ⟨u, hu, hulen⟩ :=
    exists_mem_length_eq_maxLen (l := pre ++ s :: post) (by simp)
  have hsmax : s.length = maxLen (pre ++ s :: post) := by
    have h1 : s.length ≤ maxLen (pre ++ s :: post) := length_le_maxLen (by simp)
    have h2 := hmax u hu
    omega
  rw [longest_eq]
  exact firstOfLength_of_split (fun t ht => by have := hpre t ht; omega) hsmax

/-- Full specification: `longest l = some s` if and only if `s` is a longest
element of `l` and it is the first one of that length. -/
theorem longest_eq_some_iff (l : List String) (s : String) :
    longest l = some s ↔
      (∀ t ∈ l, t.length ≤ s.length) ∧
      ∃ pre post, l = pre ++ s :: post ∧ ∀ t ∈ pre, t.length < s.length := by
  constructor
  · intro h
    exact ⟨longest_is_longest h, longest_first h⟩
  · rintro ⟨hmax, pre, post, rfl, hpre⟩
    exact longest_eq_some_of hmax hpre

/-- Any nonempty input has a result with every property in the specification. -/
theorem longest_correct (l : List String) (hl : l ≠ []) :
    ∃ s, longest l = some s ∧ s ∈ l ∧ (∀ t ∈ l, t.length ≤ s.length) ∧
      ∃ pre post, l = pre ++ s :: post ∧ ∀ t ∈ pre, t.length < s.length := by
  cases h : longest l with
  | none => exact absurd ((longest_eq_none_iff l).mp h) hl
  | some s => exact ⟨s, rfl, longest_mem h, longest_is_longest h, longest_first h⟩

/-- A one-element list returns its only element. -/
theorem longest_singleton (s : String) : longest [s] = some s := by
  have h := longest_eq_some_of (pre := []) (post := []) (s := s)
    (by intro t ht; simp at ht; simp [ht]) (by intro t ht; simp at ht)
  simpa using h

/-! ## Some of the Python tests, proved as theorems -/

theorem test_empty : longest [] = none := rfl
theorem test_single_empty : longest [""] = some "" := longest_singleton ""
theorem test_single_x : longest ["x"] = some "x" := longest_singleton "x"

end HumanEval12

/-!
TLDR-end [humaneval-12: Lean translation]: `longest` mirrors the Python. It
computes `maxLen`, returns the first string of that length, and returns `none`
on `[]`. The `#guard` lines replay `check`, and `longest_eq_some_iff` fully
specifies the result, with ties going to the first string. No Lean toolchain
was available, so this file has not been compiled.
-/
