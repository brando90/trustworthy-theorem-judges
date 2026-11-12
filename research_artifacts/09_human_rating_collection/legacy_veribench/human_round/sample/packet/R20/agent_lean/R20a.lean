import Mathlib

namespace HumanEval35

/-- Auxiliary accumulator loop: `maxAux m l` scans `l`, keeping the running maximum `m`. -/
def maxAux : Int → List Int → Int
  | m, [] => m
  | m, e :: t => maxAux (if e > m then e else m) t

/-- `max_element`: maximum element of the list (`0` on the empty list, which the
    Python version rejects via `l[0]` raising `IndexError`). -/
def maxElement (l : List Int) : Int :=
  match l with
  | [] => 0
  | h :: t => maxAux h t

example : maxElement [1, 2, 3] = 3 := by native_decide
example : maxElement [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : maxElement [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide

/-! ### Auxiliary lemmas -/

theorem maxAux_ge (l : List Int) : ∀ m : Int, m ≤ maxAux m l := by
  induction l with
  | nil => intro m; simp [maxAux]
  | cons e t ih =>
    intro m
    simp only [maxAux]
    by_cases hc : e > m
    · rw [if_pos hc]
      exact le_trans (le_of_lt hc) (ih e)
    · rw [if_neg hc]
      exact ih m

theorem maxAux_mem_ge (l : List Int) : ∀ (m : Int), ∀ x ∈ l, x ≤ maxAux m l := by
  induction l with
  | nil => intro m x hx; simp at hx
  | cons e t ih =>
    intro m x hx
    simp only [maxAux]
    rcases List.mem_cons.mp hx with h | h
    · rw [h]
      by_cases hc : e > m
      · rw [if_pos hc]; exact maxAux_ge t e
      · rw [if_neg hc]; exact le_trans (not_lt.mp hc) (maxAux_ge t m)
    · exact ih _ x h

theorem maxAux_mem (l : List Int) : ∀ m : Int, maxAux m l = m ∨ maxAux m l ∈ l := by
  induction l with
  | nil => intro m; left; rfl
  | cons e t ih =>
    intro m
    simp only [maxAux]
    by_cases hc : e > m
    · rw [if_pos hc]
      rcases ih e with h | h
      · right; rw [h]; simp
      · right; exact List.mem_cons_of_mem _ h
    · rw [if_neg hc]
      rcases ih m with h | h
      · left; exact h
      · right; exact List.mem_cons_of_mem _ h

/-! ### Specification -/

/-- Precondition: the list is non-empty (Python indexes `l[0]`). -/
def Pre (l : List Int) : Prop := l ≠ []

/-- The result is an upper bound of the list. -/
def isUpperBound_prop (l : List Int) : Prop := ∀ x ∈ l, x ≤ maxElement l

/-- The result is itself an element of the list. -/
def mem_prop (l : List Int) : Prop := maxElement l ∈ l

theorem maxElement_ub (l : List Int) : isUpperBound_prop l := by
  intro x hx
  cases l with
  | nil => simp at hx
  | cons h t =>
    simp only [maxElement]
    rcases List.mem_cons.mp hx with hxe | hxt
    · rw [hxe]; exact maxAux_ge t h
    · exact maxAux_mem_ge t h x hxt

theorem maxElement_mem (l : List Int) (hne : l ≠ []) : mem_prop l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons h t =>
    simp only [mem_prop, maxElement]
    rcases maxAux_mem t h with hh | hh
    · rw [hh]; simp
    · exact List.mem_cons_of_mem _ hh

/-- The result is the greatest element: it belongs to the list and dominates every element. -/
def Post (l : List Int) : Prop := mem_prop l ∧ isUpperBound_prop l

theorem correctness (l : List Int) : Pre l → Post l := by
  intro hne
  exact ⟨maxElement_mem l hne, maxElement_ub l⟩

/-- Consequence: the result is characterized uniquely as the maximum. -/
theorem maxElement_unique (l : List Int) (hne : l ≠ []) (v : Int)
    (hv : v ∈ l) (hub : ∀ x ∈ l, x ≤ v) : maxElement l = v :=
  le_antisymm (hub _ (maxElement_mem l hne)) (maxElement_ub l v hv)

end HumanEval35