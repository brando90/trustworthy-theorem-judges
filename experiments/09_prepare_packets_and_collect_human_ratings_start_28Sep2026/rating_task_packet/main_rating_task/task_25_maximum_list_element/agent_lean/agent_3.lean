import Mathlib

/-!
# HumanEval/35: max_element

This module formalizes the Python function `max_element` from HumanEval problem 35.
Given a non-empty list of integers, `max_element` returns the maximum element in the list.
-/

namespace humaneval_35_max_element

-- ============================================================================
-- 4. Implementation (functional definition)
-- ============================================================================

/-- Functional step that updates the running maximum `m` with element `e`. -/
def max_step (m e : Int) : Int :=
  if e > m then e else m

/-- Return the maximum element in the list `l`.
    Initializes the accumulator with `l[0]!` (which defaults to `0` on `[]`)
    and folds `max_step` across `l`. -/
def max_element (l : List Int) : Int :=
  l.foldl max_step l[0]!

-- ============================================================================
-- 5. Unit tests
-- ============================================================================

#eval max_element [1, 2, 3]
#eval max_element [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
#eval max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

example : max_element [1, 2, 3] = 3 := by native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : max_element [-10, -20, -3, -50] = -3 := by native_decide
example : max_element [42] = 42 := by native_decide
example : max_element [0, -1, 1] = 1 := by native_decide

-- ============================================================================
-- 6. Pre-condition predicate
-- ============================================================================

/-- Pre-condition for `max_element`: the input list must be non-empty. -/
def Pre (l : List Int) : Prop :=
  l ≠ []

-- ============================================================================
-- Helper lemmas for `max_step` and `List.foldl`
-- ============================================================================

@[simp]
theorem max_step_eq_max (m e : Int) : max_step m e = max m e := by
  unfold max_step
  omega

@[simp]
theorem max_step_self (x : Int) : max_step x x = x := by
  unfold max_step
  omega

@[simp]
theorem getElem!_cons_zero (x : Int) (xs : List Int) : (x :: xs)[0]! = x := rfl

theorem foldl_max_step_ge_init (l : List Int) (init : Int) :
    init ≤ l.foldl max_step init := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp only [List.foldl, max_step_eq_max]
    exact le_trans (le_max_left init h) (ih (max init h))

theorem foldl_max_step_ge_mem (l : List Int) (init : Int) :
    ∀ x ∈ l, x ≤ l.foldl max_step init := by
  induction l generalizing init with
  | nil =>
    intro x hx
    contradiction
  | cons h t ih =>
    intro x hx
    simp only [List.foldl, max_step_eq_max]
    cases List.mem_cons.mp hx with
    | inl h_eq =>
      subst h_eq
      exact le_trans (le_max_right init x) (foldl_max_step_ge_init t (max init x))
    | inr h_mem =>
      exact ih (max init h) x h_mem

theorem foldl_max_step_mem_or_eq (l : List Int) (init : Int) :
    l.foldl max_step init = init ∨ l.foldl max_step init ∈ l := by
  induction l generalizing init with
  | nil =>
    left
    rfl
  | cons h t ih =>
    simp only [List.foldl]
    cases ih (max_step init h) with
    | inl h_eq =>
      rw [h_eq]
      unfold max_step
      split_ifs with h_gt
      · right; exact List.mem_cons_self
      · left; rfl
    | inr h_mem =>
      right
      exact List.mem_cons_of_mem h h_mem

-- ============================================================================
-- 7. Property propositions and theorems
-- ============================================================================

/-- Property 1 (Membership): The result of `max_element l` is an element of `l`. -/
def max_element_mem_prop (l : List Int) : Prop :=
  max_element l ∈ l

theorem max_element_mem_thm (l : List Int) (h : Pre l) : max_element_mem_prop l := by
  unfold max_element_mem_prop max_element Pre at *
  cases l with
  | nil => contradiction
  | cons x xs =>
    simp only [getElem!_cons_zero, List.foldl_cons, max_step_self]
    cases foldl_max_step_mem_or_eq xs x with
    | inl h_eq =>
      rw [h_eq]
      exact List.mem_cons_self
    | inr h_mem =>
      exact List.mem_cons_of_mem x h_mem

/-- Property 2 (Upper Bound): Every element in `l` is at most `max_element l`. -/
def max_element_upper_bound_prop (l : List Int) : Prop :=
  ∀ x ∈ l, x ≤ max_element l

theorem max_element_upper_bound_thm (l : List Int) (h : Pre l) :
    max_element_upper_bound_prop l := by
  cases l with
  | nil => exact False.elim (h rfl)
  | cons x xs =>
    intro y hy
    exact foldl_max_step_ge_mem (x :: xs) (x :: xs)[0]! y hy

/-- Property 3 (Index Upper Bound): Every element `l[i]` at a valid index is at most `max_element l`. -/
def max_element_index_bound_prop (l : List Int) : Prop :=
  ∀ (i : Nat) (hi : i < l.length), l[i] ≤ max_element l

theorem max_element_index_bound_thm (l : List Int) (h : Pre l) :
    max_element_index_bound_prop l := by
  unfold max_element_index_bound_prop
  intro i hi
  exact max_element_upper_bound_thm l h l[i] (List.getElem_mem hi)

/-- Property 4 (Existence of Maximizing Index): There exists a valid index `i` where `l[i] = max_element l`. -/
def max_element_exists_index_prop (l : List Int) : Prop :=
  ∃ (i : Nat) (hi : i < l.length), l[i] = max_element l

theorem max_element_exists_index_thm (l : List Int) (h : Pre l) :
    max_element_exists_index_prop l := by
  unfold max_element_exists_index_prop
  exact List.mem_iff_getElem.mp (max_element_mem_thm l h)

/-- Property 5 (Head Lower Bound): The first element `l[0]!` is at most `max_element l`. -/
def max_element_ge_head_prop (l : List Int) : Prop :=
  l[0]! ≤ max_element l

theorem max_element_ge_head_thm (l : List Int) (h : Pre l) :
    max_element_ge_head_prop l := by
  unfold max_element_ge_head_prop
  cases l with
  | nil => exact False.elim (h rfl)
  | cons x xs =>
    simp only [getElem!_cons_zero]
    exact max_element_upper_bound_thm (x :: xs) h x List.mem_cons_self

/-- Property 6 (Least Upper Bound): `max_element l ≤ k` iff every element in `l` is at most `k`. -/
def max_element_lub_prop (l : List Int) : Prop :=
  ∀ k : Int, max_element l ≤ k ↔ ∀ x ∈ l, x ≤ k

theorem max_element_lub_thm (l : List Int) (h : Pre l) :
    max_element_lub_prop l := by
  unfold max_element_lub_prop
  intro k
  constructor
  · intro hk x hx
    exact le_trans (max_element_upper_bound_thm l h x hx) hk
  · intro hall
    exact hall (max_element l) (max_element_mem_thm l h)

/-- Property 7 (Uniqueness): Any `m ∈ l` that bounds all elements of `l` from above equals `max_element l`. -/
def max_element_unique_prop (l : List Int) : Prop :=
  ∀ m : Int, m ∈ l → (∀ x ∈ l, x ≤ m) → m = max_element l

theorem max_element_unique_thm (l : List Int) (h : Pre l) :
    max_element_unique_prop l := by
  unfold max_element_unique_prop
  intro m hm hbound
  apply le_antisymm
  · exact max_element_upper_bound_thm l h m hm
  · exact hbound (max_element l) (max_element_mem_thm l h)

/-- Property 8 (Singleton): For a single-element list `[x]`, `max_element [x] = x`. -/
def max_element_singleton_prop (x : Int) : Prop :=
  max_element [x] = x

theorem max_element_singleton_thm (x : Int) :
    max_element_singleton_prop x := by
  unfold max_element_singleton_prop max_element max_step
  simp

/-- Property 9 (Cons): Prepending `x` to a non-empty list `l` yields `max x (max_element l)`. -/
def max_element_cons_prop (x : Int) (l : List Int) : Prop :=
  max_element (x :: l) = max x (max_element l)

theorem max_element_cons_thm (x : Int) (l : List Int) (h : Pre l) :
    max_element_cons_prop x l := by
  unfold max_element_cons_prop
  apply le_antisymm
  · have h_mem : max_element (x :: l) ∈ x :: l :=
      max_element_mem_thm (x :: l) (List.cons_ne_nil x l)
    cases List.mem_cons.mp h_mem with
    | inl h_eq =>
      rw [h_eq]
      exact le_max_left x (max_element l)
    | inr h_in_l =>
      exact le_trans (max_element_upper_bound_thm l h _ h_in_l) (le_max_right x (max_element l))
  · apply max_le
    · exact max_element_upper_bound_thm (x :: l) (List.cons_ne_nil x l) x List.mem_cons_self
    · exact max_element_upper_bound_thm (x :: l) (List.cons_ne_nil x l) (max_element l)
        (List.mem_cons_of_mem x (max_element_mem_thm l h))

/-- Property 10 (Append): Concatenating two non-empty lists yields the maximum of their maxima. -/
def max_element_append_prop (l₁ l₂ : List Int) : Prop :=
  max_element (l₁ ++ l₂) = max (max_element l₁) (max_element l₂)

theorem max_element_append_thm (l₁ l₂ : List Int) (h₁ : Pre l₁) (h₂ : Pre l₂) :
    max_element_append_prop l₁ l₂ := by
  unfold max_element_append_prop
  have h12 : Pre (l₁ ++ l₂) := List.append_ne_nil_of_left_ne_nil h₁ l₂
  apply le_antisymm
  · have h_mem : max_element (l₁ ++ l₂) ∈ l₁ ++ l₂ := max_element_mem_thm (l₁ ++ l₂) h12
    cases List.mem_append.mp h_mem with
    | inl h_in1 =>
      exact le_trans (max_element_upper_bound_thm l₁ h₁ _ h_in1) (le_max_left _ _)
    | inr h_in2 =>
      exact le_trans (max_element_upper_bound_thm l₂ h₂ _ h_in2) (le_max_right _ _)
  · apply max_le
    · exact max_element_upper_bound_thm (l₁ ++ l₂) h12 _
        (List.mem_append_left l₂ (max_element_mem_thm l₁ h₁))
    · exact max_element_upper_bound_thm (l₁ ++ l₂) h12 _
        (List.mem_append_right l₁ (max_element_mem_thm l₂ h₂))

/-- Property 11 (Subset Monotonicity): If `l₁ ⊆ l₂`, then `max_element l₁ ≤ max_element l₂`. -/
def max_element_subset_prop (l₁ l₂ : List Int) : Prop :=
  l₁ ⊆ l₂ → max_element l₁ ≤ max_element l₂

theorem max_element_subset_thm (l₁ l₂ : List Int) (h₁ : Pre l₁) (h₂ : Pre l₂) :
    max_element_subset_prop l₁ l₂ := by
  unfold max_element_subset_prop
  intro hsub
  exact max_element_upper_bound_thm l₂ h₂ (max_element l₁) (hsub (max_element_mem_thm l₁ h₁))

/-- Property 12 (Permutation Invariance): Permuting a non-empty list preserves `max_element`. -/
def max_element_perm_prop (l₁ l₂ : List Int) : Prop :=
  l₁.Perm l₂ → max_element l₁ = max_element l₂

theorem max_element_perm_thm (l₁ l₂ : List Int) (h₁ : Pre l₁) :
    max_element_perm_prop l₁ l₂ := by
  unfold max_element_perm_prop
  intro hp
  have h₂ : Pre l₂ := by
    intro hnil
    subst hnil
    exact h₁ (List.Perm.nil_eq hp.symm).symm
  apply le_antisymm
  · exact max_element_subset_thm l₁ l₂ h₁ h₂ hp.subset
  · exact max_element_subset_thm l₂ l₁ h₂ h₁ hp.symm.subset

/-- Property 13 (Reverse Invariance): Reversing a non-empty list preserves `max_element`. -/
def max_element_reverse_prop (l : List Int) : Prop :=
  max_element l.reverse = max_element l

theorem max_element_reverse_thm (l : List Int) (h : Pre l) :
    max_element_reverse_prop l := by
  unfold max_element_reverse_prop
  have h_rev : Pre l.reverse := by
    intro hnil
    exact h (List.reverse_eq_nil_iff.mp hnil)
  exact max_element_perm_thm l.reverse l h_rev (List.reverse_perm l)

-- ============================================================================
-- 8. Post-condition
-- ============================================================================

/-- Post-condition for `max_element`: conjunction of core specification properties. -/
def Post_prop (l : List Int) : Prop :=
  max_element_mem_prop l ∧
  max_element_upper_bound_prop l ∧
  max_element_index_bound_prop l ∧
  max_element_exists_index_prop l ∧
  max_element_ge_head_prop l

-- ============================================================================
-- 9. Property-Based Tests (PBTs)
-- ============================================================================

/-- Sample non-empty lists used for bounded property-based tests. -/
def sample_lists : List (List Int) :=
  [ [1, 2, 3]
  , [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
  , [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]
  , [-10, -20, -3, -50]
  , [42]
  , [0, 0, 0]
  , [-1, 0, 1]
  , [100, 99, 98, 97]
  , [-100, -99, -98, -97]
  , [7, -7, 7, -7, 7]
  ]

-- PBT for Property 1: max_element_mem_prop
#eval Plausible.Testable.check (∀ l : List Int, 0 < l.length → max_element l ∈ l)
example : sample_lists.all (fun l => decide (max_element l ∈ l)) = true := by native_decide

-- PBT for Property 2: max_element_upper_bound_prop
#eval Plausible.Testable.check (∀ l : List Int, 0 < l.length → ∀ x ∈ l, x ≤ max_element l)
example : sample_lists.all (fun l => decide (∀ x ∈ l, x ≤ max_element l)) = true := by native_decide

-- PBT for Property 3: max_element_index_bound_prop
#eval Plausible.Testable.check (∀ l : List Int, 0 < l.length →
  (List.range l.length).all (fun i => decide (l[i]! ≤ max_element l)) = true)
example : sample_lists.all (fun l =>
  (List.range l.length).all (fun i => decide (l[i]! ≤ max_element l))) = true := by native_decide

-- PBT for Property 4: max_element_exists_index_prop
#eval Plausible.Testable.check (∀ l : List Int, 0 < l.length →
  (List.range l.length).any (fun i => decide (l[i]! = max_element l)) = true)
example : sample_lists.all (fun l =>
  (List.range l.length).any (fun i => decide (l[i]! = max_element l))) = true := by native_decide

-- PBT for Property 5: max_element_ge_head_prop
#eval Plausible.Testable.check (∀ l : List Int, 0 < l.length → l[0]! ≤ max_element l)
example : sample_lists.all (fun l => decide (l[0]! ≤ max_element l)) = true := by native_decide

-- PBT for Property 6: max_element_lub_prop
#eval Plausible.Testable.check (∀ (l : List Int) (k : Int), 0 < l.length →
  decide (max_element l ≤ k) = l.all (fun x => decide (x ≤ k)))
example : sample_lists.all (fun l =>
  ([-100, -10, 0, 3, 42, 124, 200] : List Int).all (fun k =>
    decide (max_element l ≤ k ↔ ∀ x ∈ l, x ≤ k))) = true := by native_decide

-- PBT for Property 7: max_element_unique_prop
#eval Plausible.Testable.check (∀ l : List Int, 0 < l.length →
  l.all (fun m => !l.all (fun x => decide (x ≤ m)) || decide (m = max_element l)) = true)
example : sample_lists.all (fun l =>
  decide (∀ m ∈ l, (∀ x ∈ l, x ≤ m) → m = max_element l)) = true := by native_decide

-- PBT for Property 8: max_element_singleton_prop
#eval Plausible.Testable.check (∀ x : Int, max_element [x] = x)
example : ([-50, -1, 0, 1, 3, 42, 123] : List Int).all
  (fun x => decide (max_element [x] = x)) = true := by native_decide

-- PBT for Property 9: max_element_cons_prop
#eval Plausible.Testable.check (∀ (x : Int) (l : List Int), 0 < l.length →
  max_element (x :: l) = max x (max_element l))
example : sample_lists.all (fun l =>
  ([-20, 0, 50, 200] : List Int).all (fun x =>
    decide (max_element (x :: l) = max x (max_element l)))) = true := by native_decide

-- PBT for Property 10: max_element_append_prop
#eval Plausible.Testable.check (∀ l₁ l₂ : List Int, 0 < l₁.length → 0 < l₂.length →
  max_element (l₁ ++ l₂) = max (max_element l₁) (max_element l₂))
example : sample_lists.all (fun l₁ =>
  sample_lists.all (fun l₂ =>
    decide (max_element (l₁ ++ l₂) = max (max_element l₁) (max_element l₂)))) = true := by native_decide

-- PBT for Property 11: max_element_subset_prop
#eval Plausible.Testable.check (∀ l₁ l₂ : List Int, 0 < l₁.length → 0 < l₂.length →
  max_element l₁ ≤ max_element (l₁ ++ l₂))
example : sample_lists.all (fun l₁ =>
  sample_lists.all (fun l₂ =>
    decide (max_element l₁ ≤ max_element (l₁ ++ l₂)))) = true := by native_decide

-- PBT for Property 12: max_element_perm_prop
#eval Plausible.Testable.check (∀ (x y : Int) (l : List Int),
  max_element (x :: y :: l) = max_element (y :: x :: l))
example : sample_lists.all (fun l =>
  decide (max_element (10 :: -5 :: l) = max_element (-5 :: 10 :: l))) = true := by native_decide

-- PBT for Property 13: max_element_reverse_prop
#eval Plausible.Testable.check (∀ l : List Int, 0 < l.length →
  max_element l.reverse = max_element l)
example : sample_lists.all (fun l =>
  decide (max_element l.reverse = max_element l)) = true := by native_decide

-- PBT for Post-condition: Post_prop
#eval Plausible.Testable.check (∀ l : List Int, 0 < l.length →
  (max_element l ∈ l ∧
   (∀ x ∈ l, x ≤ max_element l) ∧
   (List.range l.length).all (fun i => decide (l[i]! ≤ max_element l)) = true ∧
   (List.range l.length).any (fun i => decide (l[i]! = max_element l)) = true ∧
   l[0]! ≤ max_element l))
example : sample_lists.all (fun l =>
  decide (max_element l ∈ l ∧
          (∀ x ∈ l, x ≤ max_element l) ∧
          (List.range l.length).all (fun i => decide (l[i]! ≤ max_element l)) = true ∧
          (List.range l.length).any (fun i => decide (l[i]! = max_element l)) = true ∧
          l[0]! ≤ max_element l)) = true := by native_decide

-- ============================================================================
-- 10. Correctness theorem: Pre -> Post
-- ============================================================================

/-- Correctness theorem: for any list `l` satisfying `Pre l`, `Post_prop l` holds. -/
theorem max_element_correct (l : List Int) (h : Pre l) : Post_prop l :=
  ⟨ max_element_mem_thm l h
  , max_element_upper_bound_thm l h
  , max_element_index_bound_thm l h
  , max_element_exists_index_thm l h
  , max_element_ge_head_thm l h
  ⟩

-- ============================================================================
-- 11. Imperative implementation
-- ============================================================================

/-- Imperative implementation of `max_element` using `Id.run do` and mutable state. -/
def max_element_imp (l : List Int) : Int := Id.run do
  let mut m := l[0]!
  for e in l do
    if e > m then
      m := e
  return m

-- ============================================================================
-- 12. Imperative tests
-- ============================================================================

#eval max_element_imp [1, 2, 3]
#eval max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
#eval max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

example : max_element_imp [1, 2, 3] = 3 := by native_decide
example : max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide
example : max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : max_element_imp [-10, -20, -3, -50] = -3 := by native_decide
example : max_element_imp [42] = 42 := by native_decide
example : max_element_imp [0, -1, 1] = 1 := by native_decide

-- ============================================================================
-- 13. Equivalence theorem: functional = imperative
-- ============================================================================

/-- Helper lemma relating `List.foldl max_step` to the `forIn` loop used in `max_element_imp`. -/
theorem foldl_max_step_eq_forIn (l : List Int) (init : Int) :
    l.foldl max_step init =
      (forIn l init (fun e m =>
        if e > m then
          pure (ForInStep.yield e)
        else
          pure (ForInStep.yield m)) : Id Int).run := by
  induction l generalizing init with
  | nil => rfl
  | cons h t ih =>
    simp only [List.foldl_cons, List.forIn_cons]
    unfold max_step
    split_ifs with h_gt
    · exact ih h
    · exact ih init

/-- Equivalence theorem: the functional and imperative implementations are equal on all inputs. -/
theorem max_element_equiv (l : List Int) : max_element l = max_element_imp l := by
  unfold max_element max_element_imp
  exact foldl_max_step_eq_forIn l l[0]!

end humaneval_35_max_element
