import Mathlib

/-!
# Levenshtein edit distance

Translation of the Python program `edit_distance.py`.

The Python function computes the Levenshtein distance between two sequences
(`str` or `list`) with the classical dynamic-programming table
`dp[i][j]` = distance between the prefixes `s1[:i]` and `s2[:j]`:

* `dp[i][0] = i` (deletions), `dp[0][j] = j` (insertions),
* `dp[i][j] = dp[i-1][j-1]` if `s1[i-1] == s2[j-1]`,
* `dp[i][j] = 1 + min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1])` otherwise.

In Lean the two inputs are lists over an arbitrary type with decidable
equality (`List Char` plays the role of `str`, `List Nat` the role of a
Python list of integers).  The dynamic `isinstance` check of the Python code
is enforced statically by the Lean types, so the pre-condition is trivially
satisfied for every well-typed input (a small dynamically-typed wrapper that
models the `isinstance` check and the `ValueError` is given after the
correctness theorem).
-/

namespace edit_distance

variable {α : Type} [DecidableEq α]

/-! ## Functional implementation -/

/-- `levIdx s1 s2 i j` is the value `dp[i][j]` of the Python DP table, i.e.
the edit distance between the prefixes `s1.take i` and `s2.take j`.
It is defined by exactly the DP recurrence of the Python program. -/
def levIdx (s1 s2 : List α) : Nat → Nat → Nat
  | 0, j => j                      -- dp[0][j] = j   (insertions)
  | i + 1, 0 => i + 1              -- dp[i][0] = i   (deletions)
  | i + 1, j + 1 =>
    if s1[i]? = s2[j]? then
      levIdx s1 s2 i j             -- no operation needed
    else
      1 + min (levIdx s1 s2 i (j + 1))          -- deletion
              (min (levIdx s1 s2 (i + 1) j)     -- insertion
                   (levIdx s1 s2 i j))          -- substitution
termination_by i j => (i, j)

/-- Levenshtein edit distance between two sequences (`dp[m][n]`). -/
def editDistance (s1 s2 : List α) : Nat :=
  levIdx s1 s2 s1.length s2.length

/-- Python strings are handled by converting them to lists of characters. -/
def editDistanceStr (s1 s2 : String) : Nat :=
  editDistance s1.toList s2.toList

/-! ## Unit tests (mirroring the Python `check`) -/

example : editDistanceStr "hello" "hello" = 0 := by native_decide
example : editDistanceStr "cat" "bat" = 1 := by native_decide
example : editDistanceStr "cat" "cats" = 1 := by native_decide
example : editDistanceStr "cats" "cat" = 1 := by native_decide
example : editDistanceStr "cat" "dog" = 3 := by native_decide
example : editDistanceStr "kitten" "sitting" = 3 := by native_decide
example : editDistanceStr "" "" = 0 := by native_decide
example : editDistanceStr "" "abc" = 3 := by native_decide
example : editDistanceStr "ab" "" = 2 := by native_decide
example : editDistanceStr "a" "b" = 1 := by native_decide
example : editDistance [1, 2, 3] [1, 2, 3] = 0 := by native_decide
example : editDistance [1, 2, 3] [1, 4, 3] = 1 := by native_decide
example : editDistance [1, 2, 3, 4] [1, 3, 4] = 1 := by native_decide
example : editDistance [1, 2, 3] [4, 5, 6] = 3 := by native_decide
example : editDistance [1, 2, 3, 4, 5] [6, 7, 8] = 5 := by native_decide
example : editDistance ['h', 'e', 'l', 'l', 'o'] ['h', 'e', 'l', 'l', 'o'] = 0 := by native_decide
example : editDistance ['c', 'a', 't'] ['b', 'a', 't'] = 1 := by native_decide
example : editDistance ['c', 'a', 't'] ['c', 'a', 't', 's'] = 1 := by native_decide
example : editDistance ['c', 'a', 't', 's'] ['c', 'a', 't'] = 1 := by native_decide
example : editDistanceStr "intention" "execution" = 5 := by native_decide
example : editDistanceStr "saturday" "sunday" = 3 := by native_decide
example : editDistanceStr "abc" "def" = 3 := by native_decide
example : editDistanceStr "xyz" "abc" = 3 := by native_decide
example : editDistanceStr "a" "a" = 0 := by native_decide
example : editDistanceStr "a" "" = 1 := by native_decide
example : editDistanceStr "" "a" = 1 := by native_decide
example : editDistanceStr "aaa" "aa" = 1 := by native_decide
example : editDistanceStr "aa" "aaa" = 1 := by native_decide
example : editDistanceStr "aaaa" "bbbb" = 4 := by native_decide

#eval editDistanceStr "kitten" "sitting"        -- 3
#eval editDistanceStr "intention" "execution"   -- 5
#eval editDistance [1, 2, 3, 4, 5] [6, 7, 8]    -- 5

/-! ## Pre-condition -/

/-- The Python code requires both arguments to be `str` or `list`.  In Lean both
arguments are lists by construction, so the pre-condition always holds. -/
def Pre (_s1 _s2 : List α) : Prop := True

/-! ## Lemmas about the DP table `levIdx` -/

theorem levIdx_zero_left (s1 s2 : List α) (j : Nat) : levIdx s1 s2 0 j = j := by
  simp [levIdx]

theorem levIdx_succ_zero (s1 s2 : List α) (i : Nat) : levIdx s1 s2 (i + 1) 0 = i + 1 := by
  simp [levIdx]

theorem levIdx_succ_succ (s1 s2 : List α) (i j : Nat) :
    levIdx s1 s2 (i + 1) (j + 1) =
      if s1[i]? = s2[j]? then levIdx s1 s2 i j
      else 1 + min (levIdx s1 s2 i (j + 1)) (min (levIdx s1 s2 (i + 1) j) (levIdx s1 s2 i j)) := by
  simp only [levIdx]

/-- `dp[i][j]` only depends on the first `i` elements of `s1` and the first `j`
elements of `s2`. -/
theorem levIdx_congr (s1 s1' s2 s2' : List α) :
    ∀ (i j : Nat), (∀ k, k < i → s1[k]? = s1'[k]?) → (∀ k, k < j → s2[k]? = s2'[k]?) →
      levIdx s1 s2 i j = levIdx s1' s2' i j := by
  intro i
  induction i with
  | zero => intro j _ _; simp [levIdx]
  | succ i ih =>
    intro j
    induction j with
    | zero => intro _ _; simp [levIdx]
    | succ j ihj =>
      intro h1 h2
      rw [levIdx_succ_succ, levIdx_succ_succ, h1 i (by omega), h2 j (by omega),
        ih j (fun k hk => h1 k (by omega)) (fun k hk => h2 k (by omega)),
        ih (j + 1) (fun k hk => h1 k (by omega)) h2,
        ihj h1 (fun k hk => h2 k (by omega))]

theorem levIdx_symm (s1 s2 : List α) : ∀ i j, levIdx s1 s2 i j = levIdx s2 s1 j i := by
  intro i
  induction i with
  | zero => intro j; cases j <;> simp [levIdx]
  | succ i ih =>
    intro j
    induction j with
    | zero => simp [levIdx]
    | succ j ihj =>
      rw [levIdx_succ_succ, levIdx_succ_succ, ih j, ih (j + 1), ihj]
      by_cases h : s1[i]? = s2[j]?
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
        omega

theorem levIdx_self (s : List α) : ∀ i, levIdx s s i i = 0 := by
  intro i
  induction i with
  | zero => simp [levIdx]
  | succ i ih => rw [levIdx_succ_succ, if_pos rfl, ih]

theorem levIdx_le_max (s1 s2 : List α) : ∀ i j, levIdx s1 s2 i j ≤ max i j := by
  intro i
  induction i with
  | zero => intro j; simp [levIdx]
  | succ i ih =>
    intro j
    induction j with
    | zero => simp [levIdx]
    | succ j ihj =>
      rw [levIdx_succ_succ]
      have h1 := ih j
      have h2 := ih (j + 1)
      have h3 := ihj
      split_ifs <;> omega

theorem levIdx_ge (s1 s2 : List α) :
    ∀ i j, i ≤ levIdx s1 s2 i j + j ∧ j ≤ levIdx s1 s2 i j + i := by
  intro i
  induction i with
  | zero => intro j; simp [levIdx]
  | succ i ih =>
    intro j
    induction j with
    | zero => simp [levIdx]
    | succ j ihj =>
      rw [levIdx_succ_succ]
      have h1 := ih j
      have h2 := ih (j + 1)
      have h3 := ihj
      split_ifs <;> omega

theorem levIdx_eq_zero (s1 s2 : List α) :
    ∀ i j, levIdx s1 s2 i j = 0 → i = j ∧ s1.take i = s2.take j := by
  intro i
  induction i with
  | zero =>
    intro j h
    simp [levIdx] at h
    subst h
    simp
  | succ i ih =>
    intro j
    induction j with
    | zero => intro h; simp [levIdx] at h
    | succ j _ =>
      intro h
      rw [levIdx_succ_succ] at h
      split_ifs at h with heq
      · obtain ⟨hij, htake⟩ := ih j h
        refine ⟨by omega, ?_⟩
        rw [List.take_succ, List.take_succ, htake, heq]
      · omega

/-! ## Properties of `editDistance` -/

/-- The distance is symmetric. -/
def symm_prop (s1 s2 : List α) : Prop :=
  editDistance s1 s2 = editDistance s2 s1

theorem symm_thm (s1 s2 : List α) : symm_prop s1 s2 :=
  levIdx_symm s1 s2 _ _

/-- The distance vanishes exactly on equal sequences. -/
def eq_zero_iff_prop (s1 s2 : List α) : Prop :=
  editDistance s1 s2 = 0 ↔ s1 = s2

theorem eq_zero_iff_thm (s1 s2 : List α) : eq_zero_iff_prop s1 s2 := by
  unfold eq_zero_iff_prop
  constructor
  · intro h
    obtain ⟨_, ht⟩ := levIdx_eq_zero s1 s2 s1.length s2.length h
    simpa using ht
  · rintro rfl
    exact levIdx_self s1 _

/-- Upper bound: at most `max m n` single-element edits are ever needed. -/
def le_max_length_prop (s1 s2 : List α) : Prop :=
  editDistance s1 s2 ≤ max s1.length s2.length

theorem le_max_length_thm (s1 s2 : List α) : le_max_length_prop s1 s2 :=
  levIdx_le_max s1 s2 _ _

/-- Lower bound: at least the difference of the lengths. -/
def length_diff_le_prop (s1 s2 : List α) : Prop :=
  s1.length - s2.length ≤ editDistance s1 s2 ∧ s2.length - s1.length ≤ editDistance s1 s2

theorem length_diff_le_thm (s1 s2 : List α) : length_diff_le_prop s1 s2 := by
  unfold length_diff_le_prop editDistance
  have := levIdx_ge s1 s2 s1.length s2.length
  omega

/-- Edge cases with an empty sequence: only insertions / deletions. -/
def nil_prop (s : List α) : Prop :=
  editDistance [] s = s.length ∧ editDistance s [] = s.length

theorem nil_thm (s : List α) : nil_prop s := by
  unfold nil_prop editDistance
  constructor
  · simp [levIdx]
  · rw [levIdx_symm]
    simp [levIdx]

/-- The DP recurrence of the Python program, stated on whole sequences. -/
def snoc_recurrence_prop (s1 s2 : List α) (x y : α) : Prop :=
  editDistance (s1 ++ [x]) (s2 ++ [y]) =
    if x = y then editDistance s1 s2
    else 1 + min (editDistance s1 (s2 ++ [y]))
                 (min (editDistance (s1 ++ [x]) s2) (editDistance s1 s2))

theorem snoc_recurrence_thm (s1 s2 : List α) (x y : α) : snoc_recurrence_prop s1 s2 x y := by
  unfold snoc_recurrence_prop
  have hs : (s1 ++ [x]).length = s1.length + 1 := by simp
  have ht : (s2 ++ [y]).length = s2.length + 1 := by simp
  unfold editDistance
  rw [hs, ht, levIdx_succ_succ, List.getElem?_concat_length, List.getElem?_concat_length]
  have e1 : levIdx (s1 ++ [x]) (s2 ++ [y]) s1.length s2.length = levIdx s1 s2 s1.length s2.length :=
    levIdx_congr _ _ _ _ _ _ (fun k hk => List.getElem?_append_left hk)
      (fun k hk => List.getElem?_append_left hk)
  have e2 : levIdx (s1 ++ [x]) (s2 ++ [y]) s1.length (s2.length + 1) =
      levIdx s1 (s2 ++ [y]) s1.length (s2.length + 1) :=
    levIdx_congr _ _ _ _ _ _ (fun k hk => List.getElem?_append_left hk) (fun _ _ => rfl)
  have e3 : levIdx (s1 ++ [x]) (s2 ++ [y]) (s1.length + 1) s2.length =
      levIdx (s1 ++ [x]) s2 (s1.length + 1) s2.length :=
    levIdx_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => List.getElem?_append_left hk)
  rw [e1, e2, e3]
  simp only [Option.some_inj]

/-- Appending the same suffix to both sequences does not change the distance. -/
def append_same_suffix_prop (s1 s2 u : List α) : Prop :=
  editDistance (s1 ++ u) (s2 ++ u) = editDistance s1 s2

theorem snoc_same_eq (s1 s2 : List α) (x : α) :
    editDistance (s1 ++ [x]) (s2 ++ [x]) = editDistance s1 s2 := by
  have h := snoc_recurrence_thm s1 s2 x x
  unfold snoc_recurrence_prop at h
  rwa [if_pos rfl] at h

theorem append_same_suffix_thm (s1 s2 u : List α) : append_same_suffix_prop s1 s2 u := by
  unfold append_same_suffix_prop
  induction u generalizing s1 s2 with
  | nil => simp
  | cons a u ih =>
    rw [show s1 ++ a :: u = (s1 ++ [a]) ++ u by simp,
      show s2 ++ a :: u = (s2 ++ [a]) ++ u by simp, ih, snoc_same_eq]

/-! ## Post-condition -/

/-- Post-condition for `result = edit_distance s1 s2`: the result is the DP value
`dp[m][n]` of the Python table, and it satisfies the properties above stated on
`result` (`eq_zero_iff_prop`, `symm_prop`, `le_max_length_prop`,
`length_diff_le_prop`). -/
def Post_prop (s1 s2 : List α) (result : Nat) : Prop :=
  result = levIdx s1 s2 s1.length s2.length ∧
  (result = 0 ↔ s1 = s2) ∧
  result = editDistance s2 s1 ∧
  result ≤ max s1.length s2.length ∧
  s1.length - s2.length ≤ result ∧ s2.length - s1.length ≤ result

instance (s1 s2 : List α) (r : Nat) : Decidable (Post_prop s1 s2 r) := by
  unfold Post_prop; infer_instance

/-! ## Property-based tests -/

-- symmetry (`symm_prop`)
#eval Plausible.Testable.check (∀ s t : List Nat, editDistance s t = editDistance t s)
  (cfg := { maxSize := 8 })
-- zero iff equal (`eq_zero_iff_prop`)
#eval Plausible.Testable.check (∀ s t : List Nat, (editDistance s t = 0 ↔ s = t))
  (cfg := { maxSize := 8 })
-- upper bound (`le_max_length_prop`)
#eval Plausible.Testable.check (∀ s t : List Nat, editDistance s t ≤ max s.length t.length)
  (cfg := { maxSize := 8 })
-- lower bound (`length_diff_le_prop`)
#eval Plausible.Testable.check
  (∀ s t : List Nat, s.length - t.length ≤ editDistance s t ∧ t.length - s.length ≤ editDistance s t)
  (cfg := { maxSize := 8 })
-- empty sequences (`nil_prop`)
#eval Plausible.Testable.check
  (∀ s : List Nat, editDistance [] s = s.length ∧ editDistance s [] = s.length)
  (cfg := { maxSize := 8 })
-- DP recurrence on whole sequences (`snoc_recurrence_prop`)
#eval Plausible.Testable.check
  (∀ (s t : List Nat) (x y : Nat), editDistance (s ++ [x]) (t ++ [y]) =
    if x = y then editDistance s t
    else 1 + min (editDistance s (t ++ [y])) (min (editDistance (s ++ [x]) t) (editDistance s t)))
  (cfg := { maxSize := 7 })
-- common suffix (`append_same_suffix_prop`)
#eval Plausible.Testable.check
  (∀ s t u : List Nat, editDistance (s ++ u) (t ++ u) = editDistance s t)
  (cfg := { maxSize := 6 })
-- post-condition (`Post_prop`)
#eval Plausible.Testable.check (∀ s t : List Nat, Post_prop s t (editDistance s t))
  (cfg := { maxSize := 8 })

/-- All binary words of length `≤ 4` (for exhaustive bounded tests). -/
def smallWords : List (List Nat) :=
  (List.range 5).flatMap fun len =>
    (List.range (2 ^ len)).map fun k => (List.range len).map fun b => (k / 2 ^ b) % 2

#eval smallWords.length   -- 31

-- exhaustive bounded PBT of the post-condition on all pairs of small binary words
example : (smallWords.all fun s => smallWords.all fun t =>
    decide (Post_prop s t (editDistance s t))) = true := by native_decide

instance (s1 s2 : List α) (x y : α) : Decidable (snoc_recurrence_prop s1 s2 x y) := by
  unfold snoc_recurrence_prop; infer_instance

-- exhaustive bounded PBT of the DP recurrence on small binary words
example : (smallWords.all fun s => smallWords.all fun t => [0, 1].all fun x => [0, 1].all fun y =>
    decide (snoc_recurrence_prop s t x y)) = true := by native_decide

/-! ## Correctness theorem -/

theorem correctness (s1 s2 : List α) (_h : Pre s1 s2) : Post_prop s1 s2 (editDistance s1 s2) :=
  ⟨rfl, eq_zero_iff_thm s1 s2, symm_thm s1 s2, le_max_length_thm s1 s2, length_diff_le_thm s1 s2⟩

/-! ## Properties of the string wrapper -/

theorem editDistanceStr_symm (s t : String) : editDistanceStr s t = editDistanceStr t s :=
  symm_thm _ _

theorem editDistanceStr_eq_zero_iff (s t : String) : editDistanceStr s t = 0 ↔ s = t := by
  have h := eq_zero_iff_thm s.toList t.toList
  unfold eq_zero_iff_prop at h
  unfold editDistanceStr
  rw [h]
  exact ⟨String.ext, fun h => by rw [h]⟩

theorem editDistanceStr_le_max (s t : String) : editDistanceStr s t ≤ max s.length t.length :=
  le_max_length_thm s.toList t.toList

-- PBTs for the string wrapper
#eval Plausible.Testable.check (∀ s t : String, editDistanceStr s t = editDistanceStr t s)
  (cfg := { maxSize := 8 })
#eval Plausible.Testable.check
  (∀ s t : String, (editDistanceStr s t = 0 ↔ s = t) ∧ editDistanceStr s t ≤ max s.length t.length)
  (cfg := { maxSize := 8 })

/-! ## Dynamically-typed wrapper (models the `isinstance` check and `ValueError`)

The Python function accepts *any* value and raises `ValueError` unless both
arguments are `str` or `list`.  We model the fragment of Python values used by
the program and its tests: integers, strings and (flat) lists of integers or
strings.  A `str` argument is converted with `list(s)` to a list of one-character
strings, exactly as in the Python code. -/

/-- Elements of a Python list (the fragment used by the tests). -/
inductive PyElem where
  | int (n : Int)
  | str (s : String)
  deriving DecidableEq, Repr

/-- A Python value passed to `edit_distance`. -/
inductive PyVal where
  | int (n : Int)
  | str (s : String)
  | list (l : List PyElem)
  deriving DecidableEq, Repr

/-- `isinstance(v, (str, list))`. -/
def isSeq : PyVal → Bool
  | .str _ => true
  | .list _ => true
  | .int _ => false

/-- The Python `pre(s1, s2)`. -/
def pre (s1 s2 : PyVal) : Bool := isSeq s1 && isSeq s2

/-- Python's `list(s)` for a `str`, the list itself for a `list`, `none` otherwise. -/
def toSeq : PyVal → Option (List PyElem)
  | .str s => some (s.toList.map fun c => .str (String.singleton c))
  | .list l => some l
  | .int _ => none

deriving instance DecidableEq for Except

/-- The Python `edit_distance` on dynamically-typed arguments; raising
`ValueError` is modelled by `Except.error`. -/
def editDistancePy (s1 s2 : PyVal) : Except String Nat :=
  match toSeq s1, toSeq s2 with
  | some l1, some l2 => .ok (editDistance l1 l2)
  | _, _ => .error "Inputs must be str or list"

example : editDistancePy (.str "kitten") (.str "sitting") = .ok 3 := by native_decide
example : editDistancePy (.list [.int 1, .int 2, .int 3]) (.list [.int 1, .int 4, .int 3]) = .ok 1 := by
  native_decide
example : editDistancePy (.str "cat") (.list [.str "c", .str "a", .str "t", .str "s"]) = .ok 1 := by
  native_decide
-- negative test: `candidate(123, "abc")` raises `ValueError`
example : editDistancePy (.int 123) (.str "abc") = .error "Inputs must be str or list" := by
  native_decide

/-- Pre-condition of the dynamically-typed version (the Python `pre`). -/
def PrePy (s1 s2 : PyVal) : Prop := pre s1 s2 = true

/-- Valid inputs: the call succeeds and returns the edit distance of the underlying
sequences, which satisfies the post-condition. -/
theorem editDistancePy_ok (s1 s2 : PyVal) (h : PrePy s1 s2) :
    ∃ l1 l2, toSeq s1 = some l1 ∧ toSeq s2 = some l2 ∧
      editDistancePy s1 s2 = .ok (editDistance l1 l2) ∧ Post_prop l1 l2 (editDistance l1 l2) := by
  unfold PrePy pre isSeq at h
  cases s1 <;> cases s2 <;> simp at h <;>
    exact ⟨_, _, rfl, rfl, rfl, correctness _ _ trivial⟩

/-- Invalid inputs raise `ValueError`. -/
theorem editDistancePy_error (s1 s2 : PyVal) (h : ¬ PrePy s1 s2) :
    editDistancePy s1 s2 = .error "Inputs must be str or list" := by
  unfold PrePy pre isSeq at h
  cases s1 <;> cases s2 <;> simp at h <;> rfl

/-- The call succeeds exactly when the Python pre-condition holds. -/
theorem editDistancePy_isOk_iff (s1 s2 : PyVal) :
    (editDistancePy s1 s2).toOption.isSome = true ↔ PrePy s1 s2 := by
  unfold PrePy pre isSeq editDistancePy toSeq
  cases s1 <;> cases s2 <;> simp [Except.toOption]

/-- Sample Python values for a bounded PBT of the dynamic layer. -/
def pyVals : List PyVal :=
  [.int 123, .int 0, .str "", .str "abc", .str "cat", .list [], .list [.int 1, .int 2],
   .list [.str "c", .str "a", .str "t"]]

example : (pyVals.all fun a => pyVals.all fun b =>
    (editDistancePy a b).toOption.isSome == pre a b) = true := by native_decide

/-! ## Imperative implementation -/

/-- Imperative version of the Python DP (row by row, with mutable state).
`prev` is row `dp[i-1]`, `curr` is row `dp[i]`. -/
def editDistanceImp (s1 s2 : List α) : Nat := Id.run do
  let n := s2.length
  -- dp[0][j] = j  (insertions)
  let mut prev : Array Nat := Array.range (n + 1)
  let mut i : Nat := 0
  for x in s1 do
    i := i + 1
    -- dp[i][0] = i  (deletions)
    let mut curr : Array Nat := #[i]
    let mut j : Nat := 0
    for y in s2 do
      j := j + 1
      let v :=
        if x = y then
          prev[j - 1]!                                     -- no operation needed
        else
          1 + min prev[j]! (min curr[j - 1]! prev[j - 1]!) -- deletion / insertion / substitution
      curr := curr.push v
    prev := curr
  return prev[n]!

/-- String wrapper of the imperative implementation. -/
def editDistanceImpStr (s1 s2 : String) : Nat :=
  editDistanceImp s1.toList s2.toList

/-! ## Imperative tests -/

example : editDistanceImpStr "hello" "hello" = 0 := by native_decide
example : editDistanceImpStr "cat" "bat" = 1 := by native_decide
example : editDistanceImpStr "cat" "cats" = 1 := by native_decide
example : editDistanceImpStr "cats" "cat" = 1 := by native_decide
example : editDistanceImpStr "cat" "dog" = 3 := by native_decide
example : editDistanceImpStr "kitten" "sitting" = 3 := by native_decide
example : editDistanceImpStr "" "" = 0 := by native_decide
example : editDistanceImpStr "" "abc" = 3 := by native_decide
example : editDistanceImpStr "ab" "" = 2 := by native_decide
example : editDistanceImp [1, 2, 3, 4] [1, 3, 4] = 1 := by native_decide
example : editDistanceImp [1, 2, 3, 4, 5] [6, 7, 8] = 5 := by native_decide
example : editDistanceImp ['c', 'a', 't'] ['c', 'a', 't', 's'] = 1 := by native_decide
example : editDistanceImpStr "intention" "execution" = 5 := by native_decide
example : editDistanceImpStr "saturday" "sunday" = 3 := by native_decide
example : editDistanceImpStr "aaaa" "bbbb" = 4 := by native_decide

#eval editDistanceImpStr "kitten" "sitting"   -- 3

-- PBT: the imperative and functional implementations agree
#eval Plausible.Testable.check (∀ s t : List Nat, editDistanceImp s t = editDistance s t)
  (cfg := { maxSize := 8 })

/-! ## Equivalence of the two implementations -/

/-- A `for` loop in `Id` whose body only yields is a left fold. -/
theorem forIn_pure_yield_eq_foldl_Id {β γ : Type} (l : List γ) (f : γ → β → β) (init : β) :
    (forIn (m := Id) l init fun a b => pure (ForInStep.yield (f a b))) =
      pure (List.foldl (fun b a => f a b) init l) := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons]
    exact ih (f x init)

/-- Body of the inner loop (state: current row and column counter `j`). -/
def innerStep (prev : Array Nat) (x : α) (st : MProd (Array Nat) Nat) (y : α) :
    MProd (Array Nat) Nat :=
  ⟨st.fst.push (if x = y then prev[st.snd + 1 - 1]!
      else 1 + min prev[st.snd + 1]! (min st.fst[st.snd + 1 - 1]! prev[st.snd + 1 - 1]!)),
    st.snd + 1⟩

/-- Body of the outer loop (state: row counter `i` and previous row). -/
def outerStep (s2 : List α) (st : MProd Nat (Array Nat)) (x : α) : MProd Nat (Array Nat) :=
  ⟨st.fst + 1, (List.foldl (innerStep st.snd x) ⟨#[st.fst + 1], 0⟩ s2).fst⟩

theorem editDistanceImp_eq_foldl (s1 s2 : List α) :
    editDistanceImp s1 s2 =
      (List.foldl (outerStep s2) ⟨0, Array.range (s2.length + 1)⟩ s1).snd[s2.length]! := by
  unfold editDistanceImp
  simp only [forIn_pure_yield_eq_foldl_Id, pure_bind, Id.run_pure]
  rfl

theorem getElem!_of_toList_eq_map_range (a : Array Nat) (N : Nat) (f : Nat → Nat)
    (h : a.toList = (List.range N).map f) (k : Nat) (hk : k < N) : a[k]! = f k := by
  have ha : a = ((List.range N).map f).toArray := List.eq_toArray_iff.mpr h
  subst ha
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk]
  rfl

/-- Invariant of the inner loop: starting from the first `pre.length + 1` entries of
row `i+1`, it computes the whole row `i+1`. -/
theorem innerStep_spec (s1 s2 : List α) (i : Nat) (x : α) (hx : s1[i]? = some x)
    (prev : Array Nat) (hprev : prev.toList = (List.range (s2.length + 1)).map (levIdx s1 s2 i)) :
    ∀ (ys pre : List α) (curr : Array Nat), s2 = pre ++ ys →
      curr.toList = (List.range (pre.length + 1)).map (levIdx s1 s2 (i + 1)) →
      (List.foldl (innerStep prev x) ⟨curr, pre.length⟩ ys).fst.toList =
        (List.range (s2.length + 1)).map (levIdx s1 s2 (i + 1)) := by
  intro ys
  induction ys with
  | nil =>
    intro pre curr hs2 hcurr
    simp only [List.foldl_nil]
    rw [hcurr, hs2, List.append_nil]
  | cons y ys ih =>
    intro pre curr hs2 hcurr
    have hlen : s2.length = pre.length + 1 + ys.length := by
      rw [hs2, List.length_append, List.length_cons]; omega
    have hy : s2[pre.length]? = some y := by
      rw [hs2, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero]
    have hv : innerStep prev x ⟨curr, pre.length⟩ y =
        ⟨curr.push (levIdx s1 s2 (i + 1) (pre.length + 1)), pre.length + 1⟩ := by
      unfold innerStep
      simp only [Nat.add_sub_cancel]
      rw [getElem!_of_toList_eq_map_range prev _ _ hprev pre.length (by omega),
        getElem!_of_toList_eq_map_range prev _ _ hprev (pre.length + 1) (by omega),
        getElem!_of_toList_eq_map_range curr _ _ hcurr pre.length (by omega),
        levIdx_succ_succ, hx, hy]
      simp only [Option.some_inj]
    rw [List.foldl_cons, hv]
    have := ih (pre ++ [y]) (curr.push (levIdx s1 s2 (i + 1) (pre.length + 1)))
      (by rw [hs2, List.append_assoc, List.singleton_append])
      (by rw [Array.toList_push, hcurr, List.length_append, List.length_singleton,
            List.range_succ (n := pre.length + 1), List.map_append, List.map_singleton])
    rwa [List.length_append, List.length_singleton] at this

/-- Invariant of the outer loop: after processing `pre`, `prev` is row `pre.length`;
at the end it is the last row `dp[m]`. -/
theorem outerStep_spec (s1 s2 : List α) :
    ∀ (xs pre : List α) (prev : Array Nat), s1 = pre ++ xs →
      prev.toList = (List.range (s2.length + 1)).map (levIdx s1 s2 pre.length) →
      (List.foldl (outerStep s2) ⟨pre.length, prev⟩ xs).snd.toList =
        (List.range (s2.length + 1)).map (levIdx s1 s2 s1.length) := by
  intro xs
  induction xs with
  | nil =>
    intro pre prev hs1 hprev
    simp only [List.foldl_nil]
    rw [hprev, hs1, List.append_nil]
  | cons x xs ih =>
    intro pre prev hs1 hprev
    have hx : s1[pre.length]? = some x := by
      rw [hs1, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero]
    have hrow : (List.foldl (innerStep prev x) ⟨#[pre.length + 1], 0⟩ s2).fst.toList =
        (List.range (s2.length + 1)).map (levIdx s1 s2 (pre.length + 1)) := by
      have := innerStep_spec s1 s2 pre.length x hx prev hprev s2 [] #[pre.length + 1]
        (by simp) (by simp [levIdx])
      simpa using this
    rw [List.foldl_cons]
    have hstep : outerStep s2 ⟨pre.length, prev⟩ x =
        ⟨pre.length + 1, (List.foldl (innerStep prev x) ⟨#[pre.length + 1], 0⟩ s2).fst⟩ := rfl
    rw [hstep]
    have := ih (pre ++ [x]) (List.foldl (innerStep prev x) ⟨#[pre.length + 1], 0⟩ s2).fst
      (by rw [hs1, List.append_assoc, List.singleton_append])
      (by rw [List.length_append, List.length_singleton]; exact hrow)
    rwa [List.length_append, List.length_singleton] at this

/-- The imperative implementation agrees with the functional one. -/
theorem editDistanceImp_eq_editDistance (s1 s2 : List α) :
    editDistanceImp s1 s2 = editDistance s1 s2 := by
  rw [editDistanceImp_eq_foldl]
  have h0 : levIdx s1 s2 0 = id := funext (fun j => by simp [levIdx])
  have h := outerStep_spec s1 s2 s1 [] (Array.range (s2.length + 1)) (by simp)
    (by rw [Array.toList_range, List.length_nil, h0, List.map_id])
  simp only [List.length_nil] at h
  rw [getElem!_of_toList_eq_map_range _ _ _ h s2.length (by omega)]
  rfl

theorem editDistanceImpStr_eq_editDistanceStr (s1 s2 : String) :
    editDistanceImpStr s1 s2 = editDistanceStr s1 s2 :=
  editDistanceImp_eq_editDistance _ _

end edit_distance
