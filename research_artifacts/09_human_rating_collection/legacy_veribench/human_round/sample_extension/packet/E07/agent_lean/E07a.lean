import Mathlib

namespace AllPrefixes

/-- `allPrefixes s` returns the list of all non-empty prefixes of `s`,
    from shortest to longest. -/
def allPrefixes (s : String) : List String :=
  (List.range s.length).map (fun i => ⟨s.data.take (i + 1)⟩)

-- Tests from the Python `check` function
example : allPrefixes "" = [] := by native_decide
example : allPrefixes "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide
example : allPrefixes "WWW" = ["W", "WW", "WWW"] := by native_decide
example : allPrefixes "abc" = ["a", "ab", "abc"] := by native_decide

def Pre (s : String) : Prop := True

/-- Auxiliary: the character list of a string has the string's length. -/
theorem data_length (s : String) : s.data.length = s.length := rfl

/-- The output has one entry per character of the input. -/
theorem length_allPrefixes (s : String) : (allPrefixes s).length = s.length := by
  simp [allPrefixes]

/-- The `i`-th output entry is the prefix of `s` of length `i + 1`. -/
theorem getElem_allPrefixes (s : String) (i : Nat) (h : i < (allPrefixes s).length) :
    (allPrefixes s)[i] = ⟨s.data.take (i + 1)⟩ := by
  simp [allPrefixes, List.getElem_map, List.getElem_range]

/-- The `i`-th output entry has length `i + 1`. -/
theorem length_getElem_allPrefixes (s : String) (i : Nat) (h : i < (allPrefixes s).length) :
    ((allPrefixes s)[i]).length = i + 1 := by
  have hi : i < s.length := by rw [length_allPrefixes] at h; exact h
  rw [getElem_allPrefixes s i h]
  show (s.data.take (i + 1)).length = i + 1
  rw [List.length_take, data_length]
  omega

/-- Every element of the output is a prefix of the input. -/
theorem mem_isPrefix (s t : String) (ht : t ∈ allPrefixes s) : t.data <+: s.data := by
  simp only [allPrefixes, List.mem_map, List.mem_range] at ht
  obtain ⟨i, _, rfl⟩ := ht
  exact List.take_prefix _ _

/-- The last entry (for a non-empty input) is the whole string. -/
theorem getElem_last_allPrefixes (s : String) (h : 0 < s.length) :
    (allPrefixes s)[s.length - 1]'(by rw [length_allPrefixes]; omega) = s := by
  rw [getElem_allPrefixes]
  have h1 : s.length - 1 + 1 = s.length := by omega
  rw [h1, ← data_length, List.take_length]
  cases s
  rfl

/-- The result is empty exactly when the input is empty. -/
theorem allPrefixes_eq_nil_iff (s : String) : allPrefixes s = [] ↔ s.length = 0 := by
  constructor
  · intro h
    have := length_allPrefixes s
    rw [h] at this
    simpa using this.symm
  · intro h
    have : (allPrefixes s).length = 0 := by rw [length_allPrefixes, h]
    exact List.eq_nil_of_length_eq_zero this

def Post (s : String) (r : List String) : Prop :=
  r.length = s.length ∧ ∀ i (h : i < r.length), (r[i]).data = s.data.take (i + 1)

theorem correctness (s : String) : Pre s → Post s (allPrefixes s) := by
  intro _
  refine ⟨length_allPrefixes s, ?_⟩
  intro i h
  rw [getElem_allPrefixes s i h]

end AllPrefixes