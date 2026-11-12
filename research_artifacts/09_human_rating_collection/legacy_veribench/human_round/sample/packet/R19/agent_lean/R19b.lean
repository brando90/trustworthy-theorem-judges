import Mathlib

namespace EditDistance

variable {α : Type} [DecidableEq α]

/-! ## Definition

Levenshtein edit distance between two sequences (lists).  In Lean the
"is a sequence" precondition of the Python code is enforced by the type
system, so the precondition is vacuously true.  Strings are handled by
`String.toList` (see `editDistanceStr` below). -/

/-- Minimum number of insertions / deletions / substitutions turning `l1` into `l2`. -/
def editDistance : List α → List α → Nat
  | [], l2 => l2.length
  | a :: t1, [] => (a :: t1).length
  | a :: t1, b :: t2 =>
      if a = b then editDistance t1 t2
      else 1 + min (editDistance t1 (b :: t2))
                 (min (editDistance (a :: t1) t2) (editDistance t1 t2))
termination_by l1 l2 => l1.length + l2.length
decreasing_by
  all_goals (try simp_wf)
  all_goals (try simp only [List.length_cons])
  all_goals omega

/-- Convenience wrapper for strings. -/
def editDistanceStr (s1 s2 : String) : Nat := editDistance s1.toList s2.toList

/-! ## Unfolding lemmas -/

@[simp] theorem editDistance_nil_left (l : List α) :
    editDistance ([] : List α) l = l.length := by
  simp [editDistance]

@[simp] theorem editDistance_nil_right (l : List α) :
    editDistance l ([] : List α) = l.length := by
  cases l <;> simp [editDistance]

theorem editDistance_cons_cons_eq (a : α) (t1 t2 : List α) :
    editDistance (a :: t1) (a :: t2) = editDistance t1 t2 := by
  simp [editDistance]

theorem editDistance_cons_cons_ne {a b : α} (h : a ≠ b) (t1 t2 : List α) :
    editDistance (a :: t1) (b :: t2)
      = 1 + min (editDistance t1 (b :: t2))
            (min (editDistance (a :: t1) t2) (editDistance t1 t2)) := by
  simp [editDistance, h]

/-! ## Tests (mirroring the Python `check`) -/

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
example : editDistanceStr "a" "a" = 0 := by native_decide
example : editDistanceStr "a" "" = 1 := by native_decide
example : editDistanceStr "" "a" = 1 := by native_decide
example : editDistanceStr "intention" "execution" = 5 := by native_decide
example : editDistanceStr "saturday" "sunday" = 3 := by native_decide
example : editDistanceStr "abc" "def" = 3 := by native_decide
example : editDistanceStr "xyz" "abc" = 3 := by native_decide
example : editDistanceStr "aaa" "aa" = 1 := by native_decide
example : editDistanceStr "aa" "aaa" = 1 := by native_decide
example : editDistanceStr "aaaa" "bbbb" = 4 := by native_decide

example : editDistance ([1, 2, 3] : List Nat) [1, 2, 3] = 0 := by native_decide
example : editDistance ([1, 2, 3] : List Nat) [1, 4, 3] = 1 := by native_decide
example : editDistance ([1, 2, 3, 4] : List Nat) [1, 3, 4] = 1 := by native_decide
example : editDistance ([1, 2, 3] : List Nat) [4, 5, 6] = 3 := by native_decide
example : editDistance ([1, 2, 3, 4, 5] : List Nat) [6, 7, 8] = 5 := by native_decide
example : editDistance ['h', 'e', 'l', 'l', 'o'] ['h', 'e', 'l', 'l', 'o'] = 0 := by native_decide
example : editDistance ['c', 'a', 't'] ['b', 'a', 't'] = 1 := by native_decide
example : editDistance ['c', 'a', 't'] ['c', 'a', 't', 's'] = 1 := by native_decide
example : editDistance ['c', 'a', 't', 's'] ['c', 'a', 't'] = 1 := by native_decide

/-! ## Properties -/

/-- The distance from a sequence to itself is `0`. -/
theorem editDistance_self (l : List α) : editDistance l l = 0 := by
  induction l with
  | nil => simp
  | cons a t ih => rw [editDistance_cons_cons_eq]; exact ih

/-- Edit distance is symmetric. -/
theorem editDistance_comm : ∀ (l1 l2 : List α), editDistance l1 l2 = editDistance l2 l1
  | [], l2 => by simp
  | a :: t1, [] => by simp
  | a :: t1, b :: t2 => by
      by_cases h : a = b
      · subst h
        rw [editDistance_cons_cons_eq, editDistance_cons_cons_eq, editDistance_comm t1 t2]
      · rw [editDistance_cons_cons_ne h, editDistance_cons_cons_ne (Ne.symm h),
            editDistance_comm t1 (b :: t2), editDistance_comm (a :: t1) t2,
            editDistance_comm t1 t2]
        omega
termination_by l1 l2 => l1.length + l2.length
decreasing_by
  all_goals (try simp_wf)
  all_goals (try simp only [List.length_cons])
  all_goals omega

/-- The distance never exceeds the length of the longer sequence. -/
theorem editDistance_le_max : ∀ (l1 l2 : List α),
    editDistance l1 l2 ≤ max l1.length l2.length
  | [], l2 => by simp only [editDistance_nil_left, List.length_nil]; omega
  | a :: t1, [] => by simp only [editDistance_nil_right, List.length_nil]; omega
  | a :: t1, b :: t2 => by
      have ih := editDistance_le_max t1 t2
      by_cases h : a = b
      · subst h
        rw [editDistance_cons_cons_eq]
        simp only [List.length_cons]
        omega
      · rw [editDistance_cons_cons_ne h]
        simp only [List.length_cons]
        omega
termination_by l1 l2 => l1.length + l2.length
decreasing_by
  all_goals (try simp_wf)
  all_goals (try simp only [List.length_cons])
  all_goals omega

/-- The distance is at least the difference of the lengths. -/
theorem length_le_editDistance_add : ∀ (l1 l2 : List α),
    l1.length ≤ editDistance l1 l2 + l2.length
  | [], l2 => by simp
  | a :: t1, [] => by rw [editDistance_nil_right]; simp
  | a :: t1, b :: t2 => by
      by_cases h : a = b
      · subst h
        have ih := length_le_editDistance_add t1 t2
        rw [editDistance_cons_cons_eq]
        simp only [List.length_cons]
        omega
      · have ih1 := length_le_editDistance_add t1 (b :: t2)
        have ih2 := length_le_editDistance_add (a :: t1) t2
        have ih3 := length_le_editDistance_add t1 t2
        rw [editDistance_cons_cons_ne h]
        simp only [List.length_cons] at ih1 ih2 ih3 ⊢
        omega
termination_by l1 l2 => l1.length + l2.length
decreasing_by
  all_goals (try simp_wf)
  all_goals (try simp only [List.length_cons])
  all_goals omega

/-- Distance `0` forces the two sequences to be equal. -/
theorem eq_of_editDistance_eq_zero : ∀ (l1 l2 : List α), editDistance l1 l2 = 0 → l1 = l2
  | [], l2 => by
      intro h
      cases l2 with
      | nil => rfl
      | cons c t => rw [editDistance_nil_left] at h; simp at h
  | a :: t1, [] => by
      intro h
      rw [editDistance_nil_right] at h
      simp at h
  | a :: t1, b :: t2 => by
      intro h
      by_cases hab : a = b
      · subst hab
        rw [editDistance_cons_cons_eq] at h
        rw [eq_of_editDistance_eq_zero t1 t2 h]
      · rw [editDistance_cons_cons_ne hab] at h
        exfalso
        omega
termination_by l1 l2 => l1.length + l2.length
decreasing_by
  all_goals (try simp_wf)
  all_goals (try simp only [List.length_cons])
  all_goals omega

/-- `editDistance` is a "distance-zero iff equal" measure. -/
theorem editDistance_eq_zero_iff (l1 l2 : List α) :
    editDistance l1 l2 = 0 ↔ l1 = l2 :=
  ⟨eq_of_editDistance_eq_zero l1 l2, fun h => h ▸ editDistance_self l1⟩

/-! ## Specification -/

/-- In Lean the inputs are sequences by typing, so the precondition holds always. -/
def Pre (_l1 _l2 : List α) : Prop := True

def Post (l1 l2 : List α) : Prop :=
  editDistance l1 l2 = editDistance l2 l1 ∧
  (editDistance l1 l2 = 0 ↔ l1 = l2) ∧
  editDistance l1 l2 ≤ max l1.length l2.length ∧
  l1.length ≤ editDistance l1 l2 + l2.length ∧
  l2.length ≤ editDistance l1 l2 + l1.length ∧
  editDistance ([] : List α) l2 = l2.length ∧
  editDistance l1 ([] : List α) = l1.length

theorem correctness (l1 l2 : List α) : Pre l1 l2 → Post l1 l2 := by
  intro _
  refine ⟨editDistance_comm l1 l2, editDistance_eq_zero_iff l1 l2,
    editDistance_le_max l1 l2, length_le_editDistance_add l1 l2, ?_,
    editDistance_nil_left l2, editDistance_nil_right l1⟩
  have h := length_le_editDistance_add l2 l1
  rw [editDistance_comm l2 l1] at h
  exact h

end EditDistance