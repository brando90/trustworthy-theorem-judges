/-!
# VeriBench -- Max Element
Every stated theorem is PROVEN (no `sorry`) -- this is the expected standard.
-/

namespace MaxElement

def maxElement : List Int -> Int
  | [] => 0
  | h :: t => List.foldl max h t

example : maxElement [1, 2, 3] = 3 := by native_decide
example : maxElement [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide

def Pre (l : List Int) : Prop := True

def Post_prop (l : List Int) (result : Int) : Prop :=
  (l = [] ∧ result = 0) ∨ (∃ x ∈ l, result = x ∧ ∀ y ∈ l, y ≤ result)

theorem foldl_max_mem (h : Int) (t : List Int) : List.foldl max h t ∈ (h :: t) := by
  induction' t with hd tl IH
  · simp
  · simp
    exact IH

theorem foldl_max_greatest (h : Int) (t : List Int) : ∀ x ∈ (h :: t), x ≤ List.foldl max h t := by
  induction' t with hd tl IH
  · intro x hx
    simp at hx
    subst hx
    rfl
  · intro x hx
    simp at hx
    rcases hx with (rfl | hx)
    · exact le_max_left _ _
    · exact le_trans (IH x hx) (le_max_right _ _)

theorem correctness_thm (l : List Int) (hPre : Pre l) : Post_prop l (maxElement l) := by
  unfold maxElement
  cases' l with h t
  · left
    rfl
  · right
    have hm : List.foldl max h t ∈ (h :: t) := foldl_max_mem h t
    have hg : ∀ x ∈ (h :: t), x ≤ List.foldl max h t := foldl_max_greatest h t
    refine ⟨List.foldl max h t, hm, rfl, hg⟩

end MaxElement