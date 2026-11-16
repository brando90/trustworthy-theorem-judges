import Mathlib

/-!
# HumanEval/35: max_element

Formalization of the Python `max_element` function from HumanEval/35 in Lean 4.
Given a non-empty list of integers `l`, `max_element l` returns the maximum element in `l`.

## File Structure
1. `import Mathlib`
2. Module docstring
3. Namespace `humaneval_35_max_element`
4. Functional implementation (`max_element`)
5. Unit tests (`example` with `native_decide` and `#eval`)
6. Pre-condition predicate (`Pre`)
7. Property propositions (`*_prop`) and kernel-checked theorems (`*_thm`)
8. Post-condition (`Post_prop`) as conjunction of core specification properties
9. Property-based tests (`#eval Plausible.Testable.check` and bounded `example` checks)
10. Correctness theorem (`Pre l → Post_prop l`)
11. Imperative implementation (`max_element_imp`) using `Id.run do` and mutable state
12. Imperative unit tests
13. Functional-imperative equivalence theorem (`max_element l = max_element_imp l`)
14. End namespace
-/

namespace humaneval_35_max_element

/-! ## 4. Implementation (Functional Definition) -/

/-- Return the maximum element in the list `l`. Returns `0` for an empty list. -/
def max_element (l : List Int) : Int :=
  match l with
  | [] => 0
  | h :: t => t.foldl (fun m e => if e > m then e else m) h

/-! ## 5. Unit Tests -/

example : max_element [1, 2, 3] = 3 := by native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : max_element [-10, -20, -3, -50] = -3 := by native_decide
example : max_element [42] = 42 := by native_decide
example : max_element [0, 0, 0] = 0 := by native_decide

#eval max_element [1, 2, 3]
#eval max_element [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
#eval max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

/-! ## 6. Pre-condition Predicate -/

/-- Pre-condition: the input list `l` must be non-empty (`l ≠ []`). -/
def Pre (l : List Int) : Prop :=
  l ≠ []

theorem pre_iff_length_pos (l : List Int) : Pre l ↔ 0 < l.length :=
  List.length_pos_iff_ne_nil.symm

/-! ## 7. Property Propositions and Theorems -/

private theorem step_eq_max (m e : Int) : (if e > m then e else m) = max m e := by
  split_ifs with h <;> omega

private theorem foldl_step_eq_foldl_max (t : List Int) (h : Int) :
    t.foldl (fun m e => if e > m then e else m) h = t.foldl max h := by
  induction t generalizing h with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, step_eq_max]
    exact ih (max h x)

theorem max_element_cons_eq_foldl_max (h : Int) (t : List Int) :
    max_element (h :: t) = t.foldl max h := by
  simp [max_element, foldl_step_eq_foldl_max]

private theorem foldl_max_mem (t : List Int) (h : Int) :
    t.foldl max h = h ∨ t.foldl max h ∈ t := by
  induction t generalizing h with
  | nil => left; rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rcases ih (max h x) with h_eq | h_mem
    · rcases max_choice h x with h_max | h_max
      · left; omega
      · right; left; omega
    · right; right; exact h_mem

private theorem le_foldl_max_init (t : List Int) (h : Int) :
    h ≤ t.foldl max h := by
  induction t generalizing h with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left h x) (ih (max h x))

private theorem le_foldl_max_of_mem (t : List Int) (h x : Int) (hx : x ∈ t) :
    x ≤ t.foldl max h := by
  induction t generalizing h with
  | nil => contradiction
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | h_in
    · exact le_trans (le_max_right h x) (le_foldl_max_init ys (max h x))
    · exact ih (max h y) h_in

private theorem foldl_max_assoc (t : List Int) (a b : Int) :
    t.foldl max (max a b) = max a (t.foldl max b) := by
  induction t generalizing a b with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, max_assoc, ih]

/-- Property 1 (Membership): The returned maximum element is a member of `l`. -/
def mem_prop (l : List Int) : Prop :=
  max_element l ∈ l

theorem mem_thm (l : List Int) (h : Pre l) : mem_prop l := by
  cases l with
  | nil => contradiction
  | cons x xs =>
    unfold mem_prop
    rw [max_element_cons_eq_foldl_max, List.mem_cons]
    exact foldl_max_mem xs x

/-- Property 2 (Upper Bound): Every element in `l` is less than or equal to `max_element l`. -/
def upper_bound_prop (l : List Int) : Prop :=
  ∀ x ∈ l, x ≤ max_element l

theorem upper_bound_thm (l : List Int) (_h : Pre l) : upper_bound_prop l := by
  intro x hx
  cases l with
  | nil => contradiction
  | cons y ys =>
    rw [max_element_cons_eq_foldl_max]
    rcases List.mem_cons.mp hx with rfl | h_in
    · exact le_foldl_max_init ys x
    · exact le_foldl_max_of_mem ys y x h_in

/-- Property 3 (Index Upper Bound): Every element accessed by a valid index is at most `max_element l`. -/
def index_upper_bound_prop (l : List Int) : Prop :=
  ∀ (i : Nat) (hi : i < l.length), l[i] ≤ max_element l

theorem index_upper_bound_thm (l : List Int) (h : Pre l) : index_upper_bound_prop l := by
  intro i hi
  exact upper_bound_thm l h l[i] (List.getElem_mem hi)

/-- Property 4 (Attained at Valid Index): Some valid index in `l` holds `max_element l`. -/
def exists_index_prop (l : List Int) : Prop :=
  ∃ (i : Nat) (hi : i < l.length), l[i] = max_element l

theorem exists_index_thm (l : List Int) (h : Pre l) : exists_index_prop l := by
  have hmem : max_element l ∈ l := mem_thm l h
  exact List.mem_iff_getElem.mp hmem

/-- Property 5 (Least Upper Bound): `max_element l ≤ b` iff every element in `l` is at most `b`. -/
def least_upper_bound_prop (l : List Int) (b : Int) : Prop :=
  (max_element l ≤ b) ↔ (∀ x ∈ l, x ≤ b)

theorem least_upper_bound_thm (l : List Int) (b : Int) (h : Pre l) :
    least_upper_bound_prop l b := by
  constructor
  · intro hle x hx
    exact le_trans (upper_bound_thm l h x hx) hle
  · intro hall
    exact hall (max_element l) (mem_thm l h)

/-- Property 6 (Singleton): The maximum of a singleton list `[x]` is `x`. -/
def singleton_prop (x : Int) : Prop :=
  max_element [x] = x

theorem singleton_thm (x : Int) : singleton_prop x := rfl

/-- Property 7 (Cons Recurrence): Prepending `x` to a non-empty list `l` gives `max x (max_element l)`. -/
def cons_prop (x : Int) (l : List Int) : Prop :=
  max_element (x :: l) = max x (max_element l)

theorem cons_thm (x : Int) (l : List Int) (h : Pre l) : cons_prop x l := by
  cases l with
  | nil => contradiction
  | cons y ys =>
    unfold cons_prop
    rw [max_element_cons_eq_foldl_max, max_element_cons_eq_foldl_max]
    simp only [List.foldl_cons, foldl_max_assoc]

/-- Property 8 (Append Distributivity): The maximum of `l₁ ++ l₂` for non-empty `l₁, l₂` is the max of their maxima. -/
def append_prop (l₁ l₂ : List Int) : Prop :=
  max_element (l₁ ++ l₂) = max (max_element l₁) (max_element l₂)

theorem append_thm (l₁ l₂ : List Int) (h₁ : Pre l₁) (h₂ : Pre l₂) : append_prop l₁ l₂ := by
  induction l₁ with
  | nil => contradiction
  | cons x xs ih =>
    unfold append_prop at *
    cases xs with
    | nil =>
      simp only [List.nil_append, singleton_thm]
      exact cons_thm x l₂ h₂
    | cons y ys =>
      have hxs : Pre (y :: ys) := List.cons_ne_nil y ys
      have hxs_l2 : Pre (y :: (ys ++ l₂)) := List.cons_ne_nil y (ys ++ l₂)
      rw [List.cons_append, List.cons_append, cons_thm x (y :: (ys ++ l₂)) hxs_l2,
          cons_thm x (y :: ys) hxs, ih hxs, max_assoc]

/-- Property 9 (Subset Monotonicity): If `l₁ ⊆ l₂` and `l₁` is non-empty, `max_element l₁ ≤ max_element l₂`. -/
def subset_mono_prop (l₁ l₂ : List Int) : Prop :=
  l₁ ⊆ l₂ → max_element l₁ ≤ max_element l₂

theorem subset_mono_thm (l₁ l₂ : List Int) (h₁ : Pre l₁) : subset_mono_prop l₁ l₂ := by
  intro hsub
  have hmem1 : max_element l₁ ∈ l₁ := mem_thm l₁ h₁
  have hmem2 : max_element l₁ ∈ l₂ := hsub hmem1
  have h2 : Pre l₂ := List.ne_nil_of_mem hmem2
  exact upper_bound_thm l₂ h2 (max_element l₁) hmem2

/-- Property 10 (Permutation Invariance): Permuting a list preserves `max_element`. -/
def perm_prop (l₁ l₂ : List Int) : Prop :=
  l₁.Perm l₂ → max_element l₁ = max_element l₂

theorem perm_thm (l₁ l₂ : List Int) : perm_prop l₁ l₂ := by
  intro hp
  cases l₁ with
  | nil =>
    have : l₂ = [] := hp.symm.eq_nil
    subst this
    rfl
  | cons x xs =>
    have h1 : Pre (x :: xs) := List.cons_ne_nil x xs
    have h2 : Pre l₂ := by
      intro hnil
      rw [hnil] at hp
      exact h1 hp.eq_nil
    apply le_antisymm
    · exact subset_mono_thm (x :: xs) l₂ h1 hp.subset
    · exact subset_mono_thm l₂ (x :: xs) h2 hp.symm.subset

/-- Property 11 (Reverse Invariance): Reversing a list preserves `max_element`. -/
def reverse_prop (l : List Int) : Prop :=
  max_element l.reverse = max_element l

theorem reverse_thm (l : List Int) : reverse_prop l :=
  perm_thm l.reverse l (List.reverse_perm l)

/-- Property 12 (Replicate Idempotence): The maximum of `n > 0` copies of `x` is `x`. -/
def replicate_prop (n : Nat) (x : Int) : Prop :=
  max_element (List.replicate n x) = x

theorem replicate_thm (n : Nat) (x : Int) (hn : 0 < n) : replicate_prop n x := by
  unfold replicate_prop
  have hne : Pre (List.replicate n x) := by
    unfold Pre
    simp [Nat.ne_of_gt hn]
  apply le_antisymm
  · apply (least_upper_bound_thm (List.replicate n x) x hne).mpr
    intro y hy
    rw [(List.mem_replicate.mp hy).2]
  · exact upper_bound_thm (List.replicate n x) hne x
      (List.mem_replicate.mpr ⟨Nat.ne_of_gt hn, rfl⟩)

/-- Property 13 (Translation Equivariance): Adding a constant `c` to all elements shifts the maximum by `c`. -/
def map_add_prop (l : List Int) (c : Int) : Prop :=
  max_element (l.map (· + c)) = max_element l + c

theorem map_add_thm (l : List Int) (c : Int) (h : Pre l) : map_add_prop l c := by
  unfold map_add_prop
  have hmap : Pre (l.map (· + c)) := by
    unfold Pre at *
    simp [h]
  apply le_antisymm
  · apply (least_upper_bound_thm (l.map (· + c)) (max_element l + c) hmap).mpr
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hx_le := upper_bound_thm l h x hx
    omega
  · have hmem : max_element l ∈ l := mem_thm l h
    have hmem_map : max_element l + c ∈ l.map (· + c) :=
      List.mem_map.mpr ⟨max_element l, hmem, rfl⟩
    exact upper_bound_thm (l.map (· + c)) hmap (max_element l + c) hmem_map

/-! ## 8. Post-condition -/

/-- Post-condition for `max_element`: the result is in `l`, is an upper bound of all elements
in `l` (both by membership and by index), and is attained at some valid index in `l`. -/
def Post_prop (l : List Int) : Prop :=
  mem_prop l ∧ upper_bound_prop l ∧ index_upper_bound_prop l ∧ exists_index_prop l

/-! ## 9. Property-Based Tests -/

-- Randomized PBTs via Plausible for every `_prop` and `Post_prop`
#eval Plausible.Testable.check (∀ l : List Int, l ≠ [] → max_element l ∈ l)
#eval Plausible.Testable.check (∀ l : List Int, l ≠ [] → ∀ x ∈ l, x ≤ max_element l)
#eval Plausible.Testable.check (∀ l : List Int, l ≠ [] →
  (List.range l.length).all (fun i => decide (l[i]! ≤ max_element l)) = true)
#eval Plausible.Testable.check (∀ l : List Int, l ≠ [] →
  (List.range l.length).any (fun i => decide (l[i]! = max_element l)) = true)
#eval Plausible.Testable.check (∀ (l : List Int) (b : Int), l ≠ [] →
  (decide (max_element l ≤ b) == l.all (fun x => decide (x ≤ b))) = true)
#eval Plausible.Testable.check (∀ x : Int, max_element [x] = x)
#eval Plausible.Testable.check (∀ (x : Int) (l : List Int), l ≠ [] →
  max_element (x :: l) = max x (max_element l))
#eval Plausible.Testable.check (∀ l₁ l₂ : List Int, l₁ ≠ [] → l₂ ≠ [] →
  max_element (l₁ ++ l₂) = max (max_element l₁) (max_element l₂))
#eval Plausible.Testable.check (∀ l₁ l₂ : List Int, l₁ ≠ [] →
  max_element l₁ ≤ max_element (l₁ ++ l₂))
#eval Plausible.Testable.check (∀ l₁ l₂ : List Int,
  max_element (l₁ ++ l₂) = max_element (l₂ ++ l₁))
#eval Plausible.Testable.check (∀ l : List Int, max_element l.reverse = max_element l)
#eval Plausible.Testable.check (∀ (n : Nat) (x : Int), 0 < n →
  max_element (List.replicate n x) = x)
#eval Plausible.Testable.check (∀ (l : List Int) (c : Int), l ≠ [] →
  max_element (l.map (· + c)) = max_element l + c)
#eval Plausible.Testable.check (∀ l : List Int, l ≠ [] →
  max_element l ∈ l ∧ (∀ x ∈ l, x ≤ max_element l) ∧
  (List.range l.length).all (fun i => decide (l[i]! ≤ max_element l)) = true ∧
  (List.range l.length).any (fun i => decide (l[i]! = max_element l)) = true)

-- Bounded PBTs via `native_decide`
example : ([[1], [1, 2, 3], [5, -3, 9, 0], [-10, -2, -30], [7, 7, 7]] : List (List Int)).all
    (fun l => decide (max_element l ∈ l) && l.all (fun x => decide (x ≤ max_element l)) &&
      (List.range l.length).all (fun i => decide (l[i]! ≤ max_element l)) &&
      (List.range l.length).any (fun i => decide (l[i]! = max_element l))) = true := by native_decide

example : (List.range 20).all (fun n => decide (max_element [Int.ofNat n - 10] = Int.ofNat n - 10)) = true := by
  native_decide

example : (List.range 15).all (fun n =>
    decide (max_element (List.replicate (n + 1) (Int.ofNat n - 7)) = Int.ofNat n - 7)) = true := by
  native_decide

/-! ## 10. Correctness Theorem (`Pre → Post`) -/

theorem correctness_thm (l : List Int) (h : Pre l) : Post_prop l :=
  ⟨mem_thm l h, upper_bound_thm l h, index_upper_bound_thm l h, exists_index_thm l h⟩

theorem max_element_correct (l : List Int) : Pre l → Post_prop l :=
  correctness_thm l

/-! ## 11. Imperative Implementation -/

/-- Imperative implementation of `max_element` using `Id.run do` and mutable state. -/
def max_element_imp (l : List Int) : Int := Id.run do
  let mut m := l[0]!
  for e in l do
    if e > m then
      m := e
  return m

/-! ## 12. Imperative Tests -/

example : max_element_imp [1, 2, 3] = 3 := by native_decide
example : max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123 := by native_decide
example : max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide
example : max_element_imp [-10, -20, -3, -50] = -3 := by native_decide
example : max_element_imp [42] = 42 := by native_decide

#eval max_element_imp [1, 2, 3]
#eval max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
#eval max_element_imp [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]
#eval Plausible.Testable.check (∀ l : List Int, max_element l = max_element_imp l)

/-! ## 13. Equivalence Theorem (Functional = Imperative) -/

theorem max_element_equiv_thm (l : List Int) : max_element l = max_element_imp l := by
  cases l with
  | nil => rfl
  | cons h t =>
    simp only [max_element, max_element_imp, Id.run, List.getElem!_cons_zero, List.forIn_cons,
      gt_iff_lt, lt_self_iff_false, ↓reduceIte, bind_pure_comp, map_pure, pure_bind]
    induction t generalizing h with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.foldl_cons, List.forIn_cons]
      split_ifs <;> exact ih _

theorem equiv_thm (l : List Int) (_h : Pre l) : max_element l = max_element_imp l :=
  max_element_equiv_thm l

end humaneval_35_max_element
