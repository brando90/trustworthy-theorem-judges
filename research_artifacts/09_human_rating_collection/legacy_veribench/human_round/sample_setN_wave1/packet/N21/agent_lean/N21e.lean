import Mathlib

/-!
# Levenshtein edit distance — VeriBench translation of `edit_distance.py`

The Python program computes the Levenshtein edit distance between two sequences
(`str` or `list`) with a bottom-up dynamic-programming table, and raises
`ValueError` when an argument is not a sequence (`pre` returns `False`).

This file formalises that program:

* `Elem` / `SeqInput` model Python's `Union[str, List]` argument domain, including
  the *invalid* (non-sequence) inputs such as `123` that trigger the `ValueError`.
  Characters and list items live in different constructors, so comparing an element
  of a `str` with an element of a `list` yields "not equal", exactly as in Python.
* `ed` is the mathematical specification: the Levenshtein distance given by the
  standard insertion / deletion / substitution recurrence.
* `editDistance` is the executable functional implementation, a rolling-row
  dynamic-programming table (`initRow`, `nextRow`, `dpRows`) that is the direct
  analogue of the Python `dp` table.  `editDistance_eq` proves it equals `ed`.
* `Pre` is the pre-condition `isinstance(s1, (str, list)) and isinstance(s2, (str, list))`;
  `editDistanceSeq` returns `Except.error "Inputs must be str or list"` when it fails,
  modelling the Python `ValueError`.
* Metric properties of the distance (empty sequences, identity, symmetry,
  definiteness, the length-gap lower bounds, the `max` upper bound, the recurrence,
  the one-edit bound, the Lipschitz bounds and the triangle inequality) are stated
  as `<name>_prop` and proved as `<name>_thm`.
* `Post_prop` bundles the post-condition and `correctness_thm` proves `Pre → Post`;
  `error_thm` covers the exceptional branch.
* `editDistanceImp` is an imperative implementation (`Id.run do` with a mutable
  rolling row) and `editDistanceImp_eq` / `editDistanceImp_ed` prove it equivalent
  to the functional implementation and to the specification.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace edit_distance

/-! ## Input model for `Union[str, List]` -/

/-- An element of a sequence: either a character (coming from a `str`) or a natural
number (coming from a `list`).  Python compares elements of different types as
unequal, which is exactly what the two distinct constructors give. -/
inductive Elem where
  | ch : Char → Elem
  | num : Nat → Elem
  deriving DecidableEq, Repr

/-- A program input: a string, a list of naturals, or a non-sequence value such as
`123`, which violates the pre-condition and makes Python raise `ValueError`. -/
inductive SeqInput where
  | str : String → SeqInput
  | lst : List Nat → SeqInput
  | invalid : Nat → SeqInput
  deriving DecidableEq, Repr

/-- Convert an input into a uniform list of elements (Python: `list(s1)`). -/
def SeqInput.toElems : SeqInput → List Elem
  | .str s => s.toList.map Elem.ch
  | .lst l => l.map Elem.num
  | .invalid _ => []

/-- Executable form of `isinstance(x, (str, list))`. -/
def SeqInput.isSequence : SeqInput → Bool
  | .str _ => true
  | .lst _ => true
  | .invalid _ => false

section Generic

variable {α : Type} [DecidableEq α]

def ed : List α → List α → Nat
  | [], t => t.length
  | s, [] => s.length
  | a :: s, b :: t =>
      if a = b then ed s t
      else 1 + min (ed s t) (min (ed (a :: s) t) (ed s (b :: t)))
  termination_by s t => s.length + t.length
  decreasing_by all_goals simp [List.length_cons] <;> omega

theorem ed_nil (t : List α) : ed [] t = t.length := by simp [ed]
theorem ed_nil_right (s : List α) : ed s [] = s.length := by cases s <;> simp [ed]
theorem ed_cons_cons (a b : α) (s t : List α) :
    ed (a :: s) (b :: t) =
      if a = b then ed s t else 1 + min (ed s t) (min (ed (a :: s) t) (ed s (b :: t))) := by
  simp [ed]

theorem ed_self (s : List α) : ed s s = 0 := by
  induction s with
  | nil => simp [ed_nil]
  | cons a s ih => rw [ed_cons_cons, if_pos rfl, ih]

theorem ed_common_head (a : α) (s t : List α) : ed (a :: s) (a :: t) = ed s t := by
  rw [ed_cons_cons, if_pos rfl]

theorem ed_symm (s t : List α) : ed s t = ed t s := by
  have key : ∀ (n : Nat) (s t : List α), s.length + t.length ≤ n → ed s t = ed t s := by
    intro n
    induction n with
    | zero =>
      intro s t h
      have hs : s = [] := List.length_eq_zero_iff.mp (by omega)
      have ht : t = [] := List.length_eq_zero_iff.mp (by omega)
      subst hs
      subst ht
      simp [ed_nil]
    | succ n ih =>
      intro s t h
      cases s with
      | nil => simp [ed_nil, ed_nil_right]
      | cons a s' =>
        cases t with
        | nil => simp [ed_nil, ed_nil_right]
        | cons b t' =>
          have h1 : s'.length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h2 : s'.length + (b :: t').length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h3 : (a :: s').length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have e1 := ih s' t' h1
          have e2 := ih s' (b :: t') h2
          have e3 := ih (a :: s') t' h3
          rw [ed_cons_cons, ed_cons_cons]
          by_cases hab : a = b
          · simp [hab, e1]
          · have hba : ¬ b = a := fun hh => hab hh.symm
            simp [hab, hba, e1, e2, e3]
            omega
  exact key (s.length + t.length) s t (Nat.le_refl _)

theorem ed_le_max (s t : List α) : ed s t ≤ max s.length t.length := by
  have key : ∀ (n : Nat) (s t : List α), s.length + t.length ≤ n →
      ed s t ≤ max s.length t.length := by
    intro n
    induction n with
    | zero =>
      intro s t h
      have hs : s = [] := List.length_eq_zero_iff.mp (by omega)
      have ht : t = [] := List.length_eq_zero_iff.mp (by omega)
      subst hs
      subst ht
      simp [ed_nil]
    | succ n ih =>
      intro s t h
      cases s with
      | nil => simp [ed_nil]
      | cons a s' =>
        cases t with
        | nil => simp [ed_nil_right]
        | cons b t' =>
          have h1 : s'.length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h2 : s'.length + (b :: t').length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h3 : (a :: s').length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have b1 := ih s' t' h1
          have b2 := ih s' (b :: t') h2
          have b3 := ih (a :: s') t' h3
          rw [ed_cons_cons]
          simp only [List.length_cons] at b1 b2 b3 ⊢
          split <;> omega
  exact key (s.length + t.length) s t (Nat.le_refl _)

theorem ed_length_le (s t : List α) : s.length ≤ ed s t + t.length := by
  have key : ∀ (n : Nat) (s t : List α), s.length + t.length ≤ n →
      s.length ≤ ed s t + t.length := by
    intro n
    induction n with
    | zero =>
      intro s t h
      have hs : s = [] := List.length_eq_zero_iff.mp (by omega)
      have ht : t = [] := List.length_eq_zero_iff.mp (by omega)
      subst hs
      subst ht
      simp [ed_nil]
    | succ n ih =>
      intro s t h
      cases s with
      | nil => simp [ed_nil]
      | cons a s' =>
        cases t with
        | nil => simp [ed_nil_right]
        | cons b t' =>
          have h1 : s'.length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h2 : s'.length + (b :: t').length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h3 : (a :: s').length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have b1 := ih s' t' h1
          have b2 := ih s' (b :: t') h2
          have b3 := ih (a :: s') t' h3
          rw [ed_cons_cons]
          simp only [List.length_cons] at b1 b2 b3 ⊢
          split <;> omega
  exact key (s.length + t.length) s t (Nat.le_refl _)

theorem ed_length_le_symm (s t : List α) : t.length ≤ ed s t + s.length := by
  have h := ed_length_le t s
  rw [ed_symm] at h
  exact h

theorem ed_lipschitz_both : ∀ (n : Nat) (s t : List α), s.length + t.length ≤ n →
    (∀ a, ed (a :: s) t ≤ ed s t + 1) ∧ (∀ b, ed s (b :: t) ≤ ed s t + 1) ∧
    (∀ a, ed s t ≤ ed (a :: s) t + 1) ∧ (∀ b, ed s t ≤ ed s (b :: t) + 1) := by
  intro n
  induction n with
  | zero =>
    intro s t h
    have hs : s = [] := List.length_eq_zero_iff.mp (by omega)
    have ht : t = [] := List.length_eq_zero_iff.mp (by omega)
    subst hs
    subst ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      simp [ed_nil_right]
    · intro b
      simp [ed_nil]
    · intro a
      simp [ed_nil_right]
    · intro b
      simp [ed_nil]
  | succ n ih =>
    intro s t h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      cases s with
      | nil =>
        cases t with
        | nil => simp [ed_nil_right, ed_nil]
        | cons c t' =>
          rw [ed_cons_cons]
          simp only [ed_nil, List.length_cons]
          split <;> omega
      | cons a0 s' =>
        cases t with
        | nil => simp [ed_nil_right]
        | cons b0 t' =>
          have h3 : (a0 :: s').length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          rw [ed_cons_cons]
          by_cases hab : a = b0
          · rw [if_pos hab]
            exact (ih (a0 :: s') t' h3).2.2.2 b0
          · rw [if_neg hab]
            omega
    · intro b
      cases s with
      | nil => simp [ed_nil]
      | cons a0 s' =>
        cases t with
        | nil =>
          rw [ed_cons_cons]
          simp only [ed_nil_right, List.length_cons]
          split <;> omega
        | cons b0 t' =>
          have h2 : s'.length + (b0 :: t').length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          rw [ed_cons_cons]
          by_cases hab : a0 = b
          · rw [if_pos hab]
            exact (ih s' (b0 :: t') h2).2.2.1 a0
          · rw [if_neg hab]
            omega
    · intro a
      cases s with
      | nil =>
        cases t with
        | nil => simp [ed_nil_right, ed_nil]
        | cons c t' =>
          rw [ed_nil]
          have hl : ([a] : List α).length = 1 := rfl
          have hle := ed_length_le_symm (α := α) [a] (c :: t')
          omega
      | cons c s' =>
        cases t with
        | nil => simp [ed_nil_right]
        | cons d t' =>
          have h1 : s'.length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h2 : (c :: s').length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h3 : s'.length + (d :: t').length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          rw [ed_cons_cons, ed_cons_cons]
          by_cases hcd : c = d
          · rw [if_pos hcd]
            by_cases had : a = d
            · rw [if_pos had]
              exact (ih s' t' h1).2.2.1 c
            · rw [if_neg had]
              have f1 := (ih s' t' h1).2.2.1 c
              have f2 := (ih (c :: s') t' h2).2.2.1 a
              have f3 := (ih s' t' h1).2.2.2 d
              have f4 := (ih s' (d :: t') h3).2.2.1 c
              omega
          · rw [if_neg hcd]
            by_cases had : a = d
            · rw [if_pos had]
              omega
            · rw [if_neg had]
              have f1 := (ih (c :: s') t' h2).2.2.1 a
              have f2 := (ih (c :: s') t' h2).2.2.2 d
              omega
    · intro b
      cases s with
      | nil =>
        cases t with
        | nil => simp [ed_nil]
        | cons c t' => simp [ed_nil]
      | cons c s' =>
        cases t with
        | nil =>
          rw [ed_nil_right]
          have hl : ([b] : List α).length = 1 := rfl
          have hle := ed_length_le (α := α) (c :: s') [b]
          omega
        | cons d t' =>
          have h1 : s'.length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h2 : (c :: s').length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h3 : s'.length + (d :: t').length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          rw [ed_cons_cons, ed_cons_cons]
          by_cases hcd : c = d
          · rw [if_pos hcd]
            by_cases hcb : c = b
            · rw [if_pos hcb]
              exact (ih s' t' h1).2.2.2 d
            · rw [if_neg hcb]
              have f1 := (ih s' t' h1).2.2.2 d
              have f2 := (ih s' t' h1).2.2.1 c
              have f3 := (ih (c :: s') t' h2).2.2.2 d
              have f4 := (ih s' (d :: t') h3).2.2.2 b
              omega
          · rw [if_neg hcd]
            by_cases hcb : c = b
            · rw [if_pos hcb]
              omega
            · rw [if_neg hcb]
              have f1 := (ih s' (d :: t') h3).2.2.1 c
              have f2 := (ih s' (d :: t') h3).2.2.2 b
              omega

theorem ed_cons_le (a : α) (s t : List α) : ed (a :: s) t ≤ ed s t + 1 :=
  (ed_lipschitz_both (s.length + t.length) s t (Nat.le_refl _)).1 a

theorem ed_cons_le_right (b : α) (s t : List α) : ed s (b :: t) ≤ ed s t + 1 :=
  (ed_lipschitz_both (s.length + t.length) s t (Nat.le_refl _)).2.1 b

theorem ed_le_cons (a : α) (s t : List α) : ed s t ≤ ed (a :: s) t + 1 :=
  (ed_lipschitz_both (s.length + t.length) s t (Nat.le_refl _)).2.2.1 a

theorem ed_le_cons_right (b : α) (s t : List α) : ed s t ≤ ed s (b :: t) + 1 :=
  (ed_lipschitz_both (s.length + t.length) s t (Nat.le_refl _)).2.2.2 b

theorem ed_eq_zero (s t : List α) : ed s t = 0 ↔ s = t := by
  constructor
  · intro hz
    have key : ∀ (n : Nat) (s t : List α), s.length + t.length ≤ n → ed s t = 0 → s = t := by
      intro n
      induction n with
      | zero =>
        intro s t h h0
        have hs : s = [] := List.length_eq_zero_iff.mp (by omega)
        have ht : t = [] := List.length_eq_zero_iff.mp (by omega)
        subst hs
        subst ht
        rfl
      | succ n ih =>
        intro s t h h0
        cases s with
        | nil =>
          cases t with
          | nil => rfl
          | cons b t' => simp [ed_nil] at h0
        | cons a s' =>
          cases t with
          | nil => simp [ed_nil_right] at h0
          | cons b t' =>
            have h1 : s'.length + t'.length ≤ n := by
              simp only [List.length_cons] at h ⊢
              omega
            rw [ed_cons_cons] at h0
            by_cases hab : a = b
            · rw [if_pos hab] at h0
              have hs := ih s' t' h1 h0
              rw [hab, hs]
            · rw [if_neg hab] at h0
              omega
    exact key (s.length + t.length) s t (Nat.le_refl _) hz
  · intro h
    rw [h]
    exact ed_self t

theorem ed_pos (s t : List α) : s ≠ t → 0 < ed s t := by
  intro hne
  by_contra hz
  have h0 : ed s t = 0 := by omega
  exact hne ((ed_eq_zero s t).mp h0)

theorem ed_one_edit (a b : α) (s t : List α) : ed (a :: s) (b :: t) ≤ ed s t + 1 := by
  rw [ed_cons_cons]
  split <;> omega

theorem ed_triangle (s t u : List α) : ed s u ≤ ed s t + ed t u := by
  have key : ∀ (n : Nat) (s u : List α), s.length + u.length ≤ n →
      ∀ (t : List α), ed s u ≤ ed s t + ed t u := by
    intro n
    induction n with
    | zero =>
      intro s u h t
      have hs : s = [] := List.length_eq_zero_iff.mp (by omega)
      have hu : u = [] := List.length_eq_zero_iff.mp (by omega)
      subst hs
      subst hu
      simp [ed_nil]
    | succ n ih =>
      intro s u h t
      cases s with
      | nil =>
        rw [ed_nil, ed_nil]
        have f := ed_length_le_symm (α := α) t u
        omega
      | cons a s' =>
        cases u with
        | nil =>
          rw [ed_nil_right, ed_nil_right]
          exact ed_length_le (α := α) (a :: s') t
        | cons c u' =>
          have h1 : s'.length + u'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h2 : (a :: s').length + u'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h3 : s'.length + (c :: u').length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          cases t with
          | nil =>
            rw [ed_nil_right, ed_nil]
            have f := ed_le_max (a :: s') (c :: u')
            simp only [List.length_cons] at f ⊢
            omega
          | cons b t' =>
            rw [ed_cons_cons (a := a) (s := s') (b := c) (t := u')]
            by_cases hac : a = c
            · rw [if_pos hac]
              rw [ed_cons_cons (a := a) (s := s') (b := b) (t := t'),
                ed_cons_cons (a := b) (s := t') (b := c) (t := u')]
              by_cases hab : a = b
              · have hbc : b = c := hab.symm.trans hac
                rw [if_pos hab, if_pos hbc]
                exact ih s' u' h1 t'
              · have hbc : ¬ b = c := by
                  intro hbc'
                  apply hab
                  rw [hbc', hac]
                rw [if_neg hab, if_neg hbc]
                have f1 := ed_le_cons a s' t'
                have f2 := ed_le_cons_right b s' t'
                have f3 := ed_le_cons b t' u'
                have f4 := ed_le_cons_right c t' u'
                have i1 := ih s' u' h1 t'
                omega
            · rw [if_neg hac]
              rw [ed_cons_cons (a := a) (s := s') (b := b) (t := t'),
                ed_cons_cons (a := b) (s := t') (b := c) (t := u')]
              by_cases hab : a = b
              · have hbc : ¬ b = c := by
                  intro hbc'
                  apply hac
                  rw [hab, hbc']
                rw [if_pos hab, if_neg hbc]
                have hcx : ed (a :: s') (b :: t') = ed s' t' := by
                  rw [← hab]
                  exact ed_common_head a s' t'
                have i1 := ih s' u' h1 t'
                have i4 := ih (a :: s') u' h2 (b :: t')
                have i5 := ih s' (c :: u') h3 t'
                rw [hcx] at i4
                omega
              · by_cases hbc : b = c
                · rw [if_neg hab, if_pos hbc]
                  have i1 := ih s' u' h1 t'
                  have i3 := ih (a :: s') u' h2 t'
                  have i6 := ih s' (c :: u') h3 (b :: t')
                  have hcy : ed (b :: t') (c :: u') = ed t' u' := by
                    rw [hbc]
                    exact ed_common_head c t' u'
                  rw [hcy] at i6
                  omega
                · rw [if_neg hab, if_neg hbc]
                  have i1 := ih s' u' h1 t'
                  have i3 := ih (a :: s') u' h2 t'
                  have i4 := ih (a :: s') u' h2 (b :: t')
                  have i6 := ih s' (c :: u') h3 (b :: t')
                  rw [ed_cons_cons (a := a) (s := s') (b := b) (t := t'), if_neg hab] at i4
                  rw [ed_cons_cons (a := b) (s := t') (b := c) (t := u'), if_neg hbc] at i6
                  have f5 := ed_le_cons b t' u'
                  have f6 := ed_le_cons_right c t' u'
                  omega
  exact key (s.length + u.length) s u (Nat.le_refl _) t
/-- The distance is invariant under injective relabelling of the elements. -/
theorem ed_map {β : Type} [DecidableEq β] (f : α → β) (hf : Function.Injective f) :
    ∀ (s t : List α), ed (s.map f) (t.map f) = ed s t := by
  have key : ∀ (n : Nat) (s t : List α), s.length + t.length ≤ n →
      ed (s.map f) (t.map f) = ed s t := by
    intro n
    induction n with
    | zero =>
      intro s t h
      have hs : s = [] := List.length_eq_zero_iff.mp (by omega)
      have ht : t = [] := List.length_eq_zero_iff.mp (by omega)
      subst hs
      subst ht
      simp [ed_nil]
    | succ n ih =>
      intro s t h
      cases s with
      | nil => simp [ed_nil]
      | cons a s' =>
        cases t with
        | nil => simp [ed_nil_right]
        | cons b t' =>
          have h1 : s'.length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h2 : s'.length + (b :: t').length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have h3 : (a :: s').length + t'.length ≤ n := by
            simp only [List.length_cons] at h ⊢
            omega
          have e1 := ih s' t' h1
          have e2 := ih s' (b :: t') h2
          have e3 := ih (a :: s') t' h3
          simp only [List.map_cons] at e2 e3
          have hab : (f a = f b) ↔ (a = b) := by
            constructor
            · intro hh
              exact hf hh
            · intro hh
              rw [hh]
          simp only [List.map_cons, ed_cons_cons, hab]
          by_cases hab' : a = b
          · simp [hab', e1]
          · simp [hab', e1, e2, e3]
  intro s t
  exact key (s.length + t.length) s t (Nat.le_refl _)

def initRow : List α → List Nat
  | [] => [0]
  | _a :: s => (s.length + 1) :: initRow s

theorem initRow_length : ∀ s : List α, (initRow s).length = s.length + 1 := by
  intro s; induction s with
  | nil => rfl
  | cons a s ih => simp [initRow, ih]

theorem drop_cons_succ (a : α) (s : List α) (j : Nat) : (a :: s).drop (j + 1) = s.drop j := rfl

theorem initRow_getD : ∀ (s : List α) (i : Nat), i ≤ s.length → (initRow s).getD i 0 = (s.drop i).length := by
  intro s; induction s with
  | nil =>
      intro i hi
      have : i = 0 := by simp_all
      subst this; simp [initRow]
  | cons a s ih =>
      intro i hi
      cases i with
      | zero => simp [initRow]
      | succ j =>
          have hj : j ≤ s.length := by
            simp only [List.length_cons] at hi; omega
          simp only [initRow, List.getD_cons_succ, ih j hj, drop_cons_succ]

def nextRow (b : α) : List α → List Nat → List Nat
  | [], n :: _ => [n + 1]
  | [], [] => [0]
  | a :: s, n :: ns =>
      let rest := nextRow b s ns
      (if a = b then ns.getD 0 0
       else 1 + min (ns.getD 0 0) (min (rest.getD 0 0) n)) :: rest
  | _ :: _, [] => []

theorem nextRow_nil_cons (b : α) (n : Nat) (ns : List Nat) :
    nextRow b [] (n :: ns) = [n + 1] := rfl

theorem nextRow_cons (b a : α) (s : List α) (n : Nat) (ns : List Nat) :
    nextRow b (a :: s) (n :: ns) =
      (if a = b then ns.getD 0 0
       else 1 + min (ns.getD 0 0) (min ((nextRow b s ns).getD 0 0) n)) :: nextRow b s ns := rfl

theorem nextRow_length (b : α) : ∀ (s : List α) (nxt : List Nat),
    nxt.length = s.length + 1 → (nextRow b s nxt).length = s.length + 1 := by
  intro s; induction s with
  | nil =>
      intro nxt h
      cases nxt with
      | nil => simp at h
      | cons n ns => simp [nextRow_nil_cons]
  | cons a s ih =>
      intro nxt h
      cases nxt with
      | nil => simp at h
      | cons n ns =>
          have hns : ns.length = s.length + 1 := by
            simp only [List.length_cons] at h; omega
          have := ih ns hns
          simp only [nextRow_cons, List.length_cons] at this ⊢
          omega

theorem nextRow_spec (b : α) : ∀ (s : List α) (nxt : List Nat) (t' : List α),
    nxt.length = s.length + 1 →
    (∀ i, i ≤ s.length → nxt.getD i 0 = ed (s.drop i) t') →
    ∀ i, i ≤ s.length → (nextRow b s nxt).getD i 0 = ed (s.drop i) (b :: t') := by
  intro s; induction s with
  | nil =>
      intro nxt t' hlen H i hi
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      cases nxt with
      | nil => simp at hlen
      | cons n ns =>
          have hn : n = ed ([] : List α) t' := by
            have := H 0 (by simp); simp at this; exact this
          simp only [nextRow_nil_cons, List.getD_cons_zero, List.drop_zero, ed_nil, hn,
            List.length_cons]
  | cons a s ih =>
      intro nxt t' hlen H i hi
      cases nxt with
      | nil => simp at hlen
      | cons n ns =>
          have hns : ns.length = s.length + 1 := by
            simp only [List.length_cons] at hlen; omega
          have Hns : ∀ j, j ≤ s.length → ns.getD j 0 = ed (s.drop j) t' := by
            intro j hj
            have := H (j + 1) (by simp only [List.length_cons] at hi ⊢; omega)
            simp only [List.getD_cons_succ, drop_cons_succ] at this
            exact this
          cases i with
          | zero =>
              have hn : n = ed (a :: s) t' := by
                have := H 0 (by simp); simp at this; exact this
              have hns0 : ns.getD 0 0 = ed s t' := by
                have := Hns 0 (by simp); simp at this; exact this
              have hrec : (nextRow b s ns).getD 0 0 = ed s (b :: t') :=
                ih ns t' hns Hns 0 (by simp)
              simp only [nextRow_cons, List.getD_cons_zero, List.drop_zero, hns0, hn, hrec,
                ed_cons_cons]
              by_cases hab : a = b <;> simp [hab] <;> omega
          | succ j =>
              have hj : j ≤ s.length := by
                simp only [List.length_cons] at hi; omega
              simp only [nextRow_cons, List.getD_cons_succ, drop_cons_succ]
              exact ih ns t' hns Hns j hj

def dpRows (s t : List α) : List Nat :=
  List.foldr (fun b acc => nextRow b s acc) (initRow s) t

theorem dpRows_length (s t : List α) : (dpRows s t).length = s.length + 1 := by
  induction t with
  | nil => show (initRow s).length = s.length + 1; exact initRow_length s
  | cons b t' ih =>
      show (nextRow b s (dpRows s t')).length = s.length + 1
      exact nextRow_length b s _ ih

theorem dpRows_getD (s t : List α) : ∀ (i : Nat), i ≤ s.length →
    (dpRows s t).getD i 0 = ed (s.drop i) t := by
  induction t with
  | nil =>
      intro i hi
      show (initRow s).getD i 0 = ed (s.drop i) []
      rw [initRow_getD s i hi, ed_nil_right]
  | cons b t' ih =>
      intro i hi
      show (nextRow b s (dpRows s t')).getD i 0 = ed (s.drop i) (b :: t')
      exact nextRow_spec b s _ _ (dpRows_length s t') (fun j hj => ih j hj) i hi

def editDistance (s t : List α) : Nat := (dpRows s t).getD 0 0

theorem editDistance_eq (s t : List α) : editDistance s t = ed s t := by
  show (dpRows s t).getD 0 0 = ed (s.drop 0) t
  rw [dpRows_getD s t 0 (Nat.zero_le _), List.drop_zero]
/-- The dynamic program satisfies the Levenshtein recurrence. -/
theorem editDistance_recurrence (a b : α) (s t : List α) :
    editDistance (a :: s) (b :: t) =
      if a = b then editDistance s t
      else 1 + min (editDistance s t)
        (min (editDistance (a :: s) t) (editDistance s (b :: t))) := by
  simp only [editDistance_eq, ed_cons_cons]

theorem editDistance_nil_left (t : List α) : editDistance [] t = t.length := by
  simp only [editDistance_eq, ed_nil]

theorem editDistance_nil_right (s : List α) : editDistance s [] = s.length := by
  simp only [editDistance_eq, ed_nil_right]

theorem editDistance_self (s : List α) : editDistance s s = 0 := by
  simp only [editDistance_eq, ed_self]

theorem editDistance_symm (s t : List α) : editDistance s t = editDistance t s := by
  simp only [editDistance_eq, ed_symm]

theorem editDistance_eq_zero (s t : List α) : editDistance s t = 0 ↔ s = t := by
  simp only [editDistance_eq, ed_eq_zero]

theorem editDistance_le_max (s t : List α) :
    editDistance s t ≤ max s.length t.length := by
  simp only [editDistance_eq, ed_le_max]

theorem editDistance_length_le (s t : List α) :
    s.length ≤ editDistance s t + t.length := by
  simp only [editDistance_eq, ed_length_le]

theorem editDistance_length_le_symm (s t : List α) :
    t.length ≤ editDistance s t + s.length := by
  simp only [editDistance_eq, ed_length_le_symm]

theorem editDistance_triangle (s t u : List α) :
    editDistance s u ≤ editDistance s t + editDistance t u := by
  simp only [editDistance_eq, ed_triangle]

theorem editDistance_common_head (a : α) (s t : List α) :
    editDistance (a :: s) (a :: t) = editDistance s t := by
  simp only [editDistance_eq, ed_common_head]

/-- The dynamic program is invariant under injective relabelling too. -/
theorem editDistance_map {β : Type} [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (s t : List α) :
    editDistance (s.map f) (t.map f) = editDistance s t := by
  rw [editDistance_eq, editDistance_eq, ed_map f hf]

end Generic

/-! ## Concrete entry points (the Python callable) -/

/-- `edit_distance(s1, s2)` for two strings. -/
def editDistanceStr (s1 s2 : String) : Nat := editDistance s1.toList s2.toList

/-- `edit_distance(s1, s2)` for two lists of naturals. -/
def editDistanceList (l1 l2 : List Nat) : Nat := editDistance l1 l2

theorem editDistanceStr_ed (s1 s2 : String) :
    editDistanceStr s1 s2 = ed s1.toList s2.toList := editDistance_eq _ _

theorem editDistanceList_ed (l1 l2 : List Nat) :
    editDistanceList l1 l2 = ed l1 l2 := editDistance_eq _ _

/-! ## Unit tests -- the assertions of the Python `check` function -/

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
example : editDistanceList [1, 2, 3] [1, 2, 3] = 0 := by native_decide
example : editDistanceList [1, 2, 3] [1, 4, 3] = 1 := by native_decide
example : editDistanceList [1, 2, 3, 4] [1, 3, 4] = 1 := by native_decide
example : editDistanceList [1, 2, 3] [4, 5, 6] = 3 := by native_decide
example : editDistanceList [1, 2, 3, 4, 5] [6, 7, 8] = 5 := by native_decide
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

#eval editDistanceStr "kitten" "sitting"
#eval editDistanceStr "intention" "execution"
#eval editDistanceList [1, 2, 3, 4, 5] [6, 7, 8]

/-! ## Pre-condition -/

/-- `pre(s1, s2)`: both arguments must be sequences (`str` or `list`). -/
def Pre (x y : SeqInput) : Prop := x.isSequence && y.isSequence = true

instance (x y : SeqInput) : Decidable (Pre x y) :=
  show Decidable (x.isSequence && y.isSequence = true) from inferInstance

/-- Executable counterpart of `Pre`. -/
def Pre_bool (x y : SeqInput) : Bool := x.isSequence && y.isSequence

theorem Pre_bool_iff (x y : SeqInput) : Pre_bool x y = true ↔ Pre x y := by
  simp [Pre_bool, Pre]

theorem Pre_invalid_left (n : Nat) (y : SeqInput) : ¬ Pre (.invalid n) y := by
  simp [Pre, SeqInput.isSequence]

theorem Pre_invalid_right (x : SeqInput) (n : Nat) : ¬ Pre x (.invalid n) := by
  cases x <;> simp [Pre, SeqInput.isSequence]

/-- The Python callable, including the `ValueError` branch. -/
def editDistanceSeq (x y : SeqInput) : Except String Nat :=
  if Pre x y then .ok (editDistance x.toElems y.toElems)
  else .error "Inputs must be str or list"

/-- The message of a failed call (`none` when the call succeeds). -/
def seqErr (r : Except String Nat) : Option String :=
  match r with
  | .error e => some e
  | .ok _ => none

-- the negative test of the Python `check` function: a non-sequence input raises
example : (editDistanceSeq (.invalid 123) (.str "abc")).toOption = none := by native_decide
example : seqErr (editDistanceSeq (.invalid 123) (.str "abc")) =
    some "Inputs must be str or list" := by native_decide
example : (editDistanceSeq (.str "abc") (.invalid 123)).toOption = none := by native_decide
example : seqErr (editDistanceSeq (.str "abc") (.invalid 123)) =
    some "Inputs must be str or list" := by native_decide
example : (editDistanceSeq (.invalid 3) (.invalid 4)).toOption = none := by native_decide
example : (editDistanceSeq (.str "cat") (.str "bat")).toOption = some 1 := by native_decide
example : (editDistanceSeq (.lst [1, 2, 3]) (.lst [1, 4, 3])).toOption = some 1 := by native_decide
-- mixed `str` / `list` arguments are compared elementwise and never equal
example : (editDistanceSeq (.str "cat") (.lst [1, 2, 3])).toOption = some 3 := by native_decide
example : (editDistanceSeq (.str "cat") (.lst [1, 2, 3])).toOption =
    (editDistanceSeq (.str "cat") (.str "abc")).toOption := by native_decide

#eval (editDistanceSeq (.str "kitten") (.str "sitting")).toOption
#eval seqErr (editDistanceSeq (.invalid 123) (.str "abc"))

/-! ## Properties -/

section Props

variable {α : Type} [DecidableEq α]

def nil_left_prop (t : List α) : Prop := ed [] t = t.length
theorem nil_left_thm (t : List α) : nil_left_prop t := ed_nil t

def nil_right_prop (s : List α) : Prop := ed s [] = s.length
theorem nil_right_thm (s : List α) : nil_right_prop s := ed_nil_right s

def self_prop (s : List α) : Prop := ed s s = 0
theorem self_thm (s : List α) : self_prop s := ed_self s

def symm_prop (s t : List α) : Prop := ed s t = ed t s
theorem symm_thm (s t : List α) : symm_prop s t := ed_symm s t

def definite_prop (s t : List α) : Prop := ed s t = 0 ↔ s = t
theorem definite_thm (s t : List α) : definite_prop s t := ed_eq_zero s t

def pos_prop (s t : List α) : Prop := 0 < ed s t ↔ s ≠ t
theorem pos_thm (s t : List α) : pos_prop s t := by
  constructor
  · intro h ne
    rw [ne, ed_self] at h
    exact absurd h (by omega)
  · intro ne
    exact ed_pos s t ne

def recurrence_prop (a b : α) (s t : List α) : Prop :=
  ed (a :: s) (b :: t) =
    if a = b then ed s t
    else 1 + min (ed s t) (min (ed (a :: s) t) (ed s (b :: t)))
theorem recurrence_thm (a b : α) (s t : List α) : recurrence_prop a b s t :=
  ed_cons_cons a b s t

def upper_bound_prop (s t : List α) : Prop := ed s t ≤ max s.length t.length
theorem upper_bound_thm (s t : List α) : upper_bound_prop s t := ed_le_max s t

def length_gap_prop (s t : List α) : Prop :=
  s.length ≤ ed s t + t.length ∧ t.length ≤ ed s t + s.length
theorem length_gap_thm (s t : List α) : length_gap_prop s t :=
  ⟨ed_length_le s t, ed_length_le_symm s t⟩

def common_head_prop (a : α) (s t : List α) : Prop := ed (a :: s) (a :: t) = ed s t
theorem common_head_thm (a : α) (s t : List α) : common_head_prop a s t :=
  ed_common_head a s t

def one_edit_prop (a b : α) (s t : List α) : Prop := ed (a :: s) (b :: t) ≤ ed s t + 1
theorem one_edit_thm (a b : α) (s t : List α) : one_edit_prop a b s t :=
  ed_one_edit a b s t

def lipschitz_prop (a b : α) (s t : List α) : Prop :=
  ed (a :: s) t ≤ ed s t + 1 ∧ ed s (b :: t) ≤ ed s t + 1 ∧
  ed s t ≤ ed (a :: s) t + 1 ∧ ed s t ≤ ed s (b :: t) + 1
theorem lipschitz_thm (a b : α) (s t : List α) : lipschitz_prop a b s t :=
  ⟨ed_cons_le a s t, ed_cons_le_right b s t, ed_le_cons a s t, ed_le_cons_right b s t⟩

def triangle_prop (s t u : List α) : Prop := ed s u ≤ ed s t + ed t u
theorem triangle_thm (s t u : List α) : triangle_prop s t u := ed_triangle s t u

def dp_correct_prop (s t : List α) : Prop := editDistance s t = ed s t
theorem dp_correct_thm (s t : List α) : dp_correct_prop s t := editDistance_eq s t

def nonneg_prop (s t : List α) : Prop := 0 ≤ ed s t
theorem nonneg_thm (s t : List α) : nonneg_prop s t := Nat.zero_le _

end Props

/-! ## Post-condition -/

/-- Post-condition of `editDistanceSeq` on admissible inputs: it returns the dynamic
programming value, which agrees with the specification and satisfies the metric
properties of the Levenshtein distance. -/
def Post_prop (x y : SeqInput) (r : Except String Nat) : Prop :=
  Pre x y ∧
  ∃ n, r = Except.ok n ∧
    n = editDistance x.toElems y.toElems ∧
    n = ed x.toElems y.toElems ∧
    n ≤ max x.toElems.length y.toElems.length ∧
    x.toElems.length ≤ n + y.toElems.length ∧
    y.toElems.length ≤ n + x.toElems.length ∧
    (n = 0 ↔ x.toElems = y.toElems) ∧
    ed x.toElems y.toElems = ed y.toElems x.toElems ∧
    ∀ z : List Elem, ed x.toElems z ≤ ed x.toElems y.toElems + ed y.toElems z

/-- Post-condition of the exceptional (`ValueError`) branch. -/
def ErrorPost_prop (x y : SeqInput) (r : Except String Nat) : Prop :=
  ¬ Pre x y ∧ r = Except.error "Inputs must be str or list"

/-! ## Property-based tests -/

def smallLists : List (List Nat) :=
  [[], [0], [1], [2], [0, 0], [0, 1], [1, 0], [1, 1], [0, 1, 2], [2, 1, 0], [1, 1, 2], [0, 0, 1]]

def tinyLists : List (List Nat) :=
  [[], [0], [1], [0, 0], [0, 1], [1, 0]]

def smallSeqs : List SeqInput :=
  [.str "", .str "a", .str "ab", .str "abc", .str "aa",
   .lst [], .lst [1], .lst [1, 2], .lst [0, 0, 1], .invalid 0, .invalid 7]

-- Randomised property-based tests (Plausible) over the executable implementation.
#eval Plausible.Testable.check (∀ xs : List Nat, editDistance [] xs = xs.length)
#eval Plausible.Testable.check (∀ xs : List Nat, editDistance xs [] = xs.length)
#eval Plausible.Testable.check (∀ xs : List Nat, editDistance xs xs = 0)
#eval Plausible.Testable.check (∀ xs ys : List Nat, editDistance xs ys = editDistance ys xs)
#eval Plausible.Testable.check (∀ xs ys : List Nat, (editDistance xs ys = 0) = (xs == ys))
#eval Plausible.Testable.check
  (∀ xs ys : List Nat, editDistance xs ys ≤ max xs.length ys.length)
#eval Plausible.Testable.check
  (∀ xs ys : List Nat, xs.length ≤ editDistance xs ys + ys.length)
#eval Plausible.Testable.check
  (∀ xs ys : List Nat, ys.length ≤ editDistance xs ys + xs.length)
#eval Plausible.Testable.check
  (∀ a b : Nat, ∀ xs ys : List Nat,
    editDistance (a :: xs) (b :: ys) =
      if a = b then editDistance xs ys
      else 1 + min (editDistance xs ys)
        (min (editDistance (a :: xs) ys) (editDistance xs (b :: ys))))
#eval Plausible.Testable.check
  (∀ a : Nat, ∀ xs ys : List Nat, editDistance (a :: xs) (a :: ys) = editDistance xs ys)
#eval Plausible.Testable.check
  (∀ a b : Nat, ∀ xs ys : List Nat, editDistance (a :: xs) (b :: ys) ≤ editDistance xs ys + 1)
#eval Plausible.Testable.check
  (∀ a : Nat, ∀ xs ys : List Nat, editDistance xs ys ≤ editDistance (a :: xs) ys + 1)
#eval Plausible.Testable.check
  (∀ a : Nat, ∀ xs ys : List Nat, editDistance xs ys ≤ editDistance xs (a :: ys) + 1)
#eval Plausible.Testable.check
  (∀ xs ys zs : List Nat, editDistance xs zs ≤ editDistance xs ys + editDistance ys zs)
-- PBT: `editDistance = ed` is checked exhaustively on `smallLists` below
-- (a randomised check would evaluate the exponential reference `ed`).
#eval Plausible.Testable.check (∀ xs ys : List Nat, 0 ≤ editDistance xs ys)

-- Bounded (exhaustive small-case) property-based tests over the specification `ed`.
example : (List.product smallLists smallLists).all
    (fun p => ed p.1 p.2 = ed p.2 p.1) = true := by native_decide
example : (List.product smallLists smallLists).all
    (fun p => ed p.1 p.1 = 0) = true := by native_decide
example : (List.product smallLists smallLists).all
    (fun p => (ed p.1 p.2 = 0) = (p.1 == p.2)) = true := by native_decide
example : (List.product smallLists smallLists).all
    (fun p => ed p.1 p.2 ≤ max p.1.length p.2.length) = true := by native_decide
example : (List.product smallLists smallLists).all
    (fun p => p.1.length ≤ ed p.1 p.2 + p.2.length ∧
      p.2.length ≤ ed p.1 p.2 + p.1.length) = true := by native_decide
example : (List.product smallLists smallLists).all
    (fun p => ed p.1 p.2 = editDistance p.1 p.2) = true := by native_decide
example : (List.product smallLists smallLists).all
    (fun p => ed [] p.2 = p.2.length ∧ ed p.1 [] = p.1.length) = true := by native_decide
example : (List.product smallLists (List.product smallLists smallLists)).all
    (fun q => ed q.1 q.2.1 ≤ ed q.1 q.2.2 + ed q.2.2 q.2.1) = true := by native_decide
example : (List.product tinyLists (List.product tinyLists tinyLists)).all
    (fun q => ∀ a b : Fin 2, ed (a.val :: q.1) (b.val :: q.2.1) ≤ ed q.1 q.2.1 + 1) =
    true := by native_decide
example : (List.product tinyLists (List.product tinyLists tinyLists)).all
    (fun q => ∀ a b : Fin 2,
      ed (a.val :: q.1) (b.val :: q.2.1) =
        if a.val = b.val then ed q.1 q.2.1
        else 1 + min (ed q.1 q.2.1)
          (min (ed (a.val :: q.1) q.2.1) (ed q.1 (b.val :: q.2.1)))) = true := by native_decide
example : (List.product tinyLists (List.product tinyLists tinyLists)).all
    (fun q => ∀ a b : Fin 2,
      ed q.1 q.2.1 ≤ ed (a.val :: q.1) q.2.1 + 1 ∧
      ed q.1 q.2.1 ≤ ed q.1 (b.val :: q.2.1) + 1) = true := by native_decide
example : (List.product smallLists smallLists).all
    (fun p => ∀ a : Fin 2, ed (a.val :: p.1) (a.val :: p.2) = ed p.1 p.2) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ xs ys : List Nat, (0 < editDistance xs ys) = (xs != ys))
#eval Plausible.Testable.check
  (∀ a b : Nat, ∀ xs ys : List Nat,
    editDistance (a :: xs) (b :: ys) ≤ editDistance xs ys + 1)

example : (List.product smallLists smallLists).all
    (fun p => (0 < ed p.1 p.2) = (p.1 != p.2)) = true := by native_decide
example : (List.product smallLists smallLists).all
    (fun p => ∀ a b : Fin 2, ed (a.val :: p.1) (b.val :: p.2) ≤ ed p.1 p.2 + 1) =
    true := by native_decide
example : (List.product smallLists smallLists).all
    (fun p => ∀ a b : Fin 2,
      ed p.1 p.2 ≤ ed (a.val :: p.1) p.2 + 1 ∧ ed p.1 p.2 ≤ ed p.1 (b.val :: p.2) + 1) =
    true := by native_decide
example : (List.product smallLists smallLists).all
    (fun p => ∀ a b : Fin 2,
      ed (a.val :: p.1) (b.val :: p.2) ≤ max (a.val :: p.1).length (b.val :: p.2).length) =
    true := by native_decide

-- Bounded property-based tests for the pre-condition and the post-condition.
example : (List.product smallSeqs smallSeqs).all
    (fun p => Pre_bool p.1 p.2 = false ∨
      (editDistanceSeq p.1 p.2).toOption.getD 0 = ed p.1.toElems p.2.toElems) = true := by
  native_decide
example : (List.product smallSeqs smallSeqs).all
    (fun p => Pre_bool p.1 p.2 = false ∨
      (editDistanceSeq p.1 p.2).toOption.getD 0 = editDistance p.1.toElems p.2.toElems) = true :=
  by native_decide

example : (List.product smallSeqs smallSeqs).all
    (fun p => (p.1.isSequence && p.2.isSequence) = false ∨
      (editDistanceSeq p.1 p.2).toOption = some (editDistance p.1.toElems p.2.toElems)) =
    true := by native_decide
example : (List.product smallSeqs smallSeqs).all
    (fun p => (p.1.isSequence && p.2.isSequence) = true ∨
      seqErr (editDistanceSeq p.1 p.2) = some "Inputs must be str or list") = true := by
  native_decide
example : (List.product smallSeqs smallSeqs).all
    (fun p => (Pre_bool p.1 p.2 = true) = (editDistanceSeq p.1 p.2).toOption.isSome) =
    true := by native_decide
example : (List.product smallSeqs smallSeqs).all
    (fun p => (editDistanceSeq p.1 p.2).toOption = none ∨
      ((editDistanceSeq p.1 p.2).toOption.getD 0 ≤
          max p.1.toElems.length p.2.toElems.length ∧
        p.1.toElems.length ≤
          (editDistanceSeq p.1 p.2).toOption.getD 0 + p.2.toElems.length ∧
        p.2.toElems.length ≤
          (editDistanceSeq p.1 p.2).toOption.getD 0 + p.1.toElems.length ∧
        ((editDistanceSeq p.1 p.2).toOption.getD 0 = 0) = (p.1.toElems == p.2.toElems))) =
    true := by native_decide

/-! ## Correctness -/

theorem correctness_thm (x y : SeqInput) (h : Pre x y) :
    Post_prop x y (editDistanceSeq x y) := by
  rw [editDistanceSeq, if_pos h]
  have hn : editDistance x.toElems y.toElems = ed x.toElems y.toElems := editDistance_eq _ _
  refine ⟨h, ed x.toElems y.toElems, by rw [hn], hn.symm, rfl, ed_le_max _ _,
    ed_length_le _ _, ed_length_le_symm _ _, ed_eq_zero _ _, ed_symm _ _,
    fun z => ed_triangle _ _ _⟩

theorem error_thm (x y : SeqInput) (h : ¬ Pre x y) :
    ErrorPost_prop x y (editDistanceSeq x y) := by
  rw [editDistanceSeq, if_neg h]
  exact ⟨h, rfl⟩

/-- On two strings the wrapper agrees with `editDistanceStr`. -/
theorem editDistanceSeq_str (s1 s2 : String) :
    editDistanceSeq (.str s1) (.str s2) = .ok (editDistanceStr s1 s2) := by
  have hinj : Function.Injective Elem.ch := fun _ _ hh => by injection hh
  have hpre : Pre (.str s1) (.str s2) := by simp [Pre, SeqInput.isSequence]
  rw [editDistanceSeq, if_pos hpre, editDistanceStr]
  congr 1
  show editDistance (s1.toList.map Elem.ch) (s2.toList.map Elem.ch) =
    editDistance s1.toList s2.toList
  exact editDistance_map Elem.ch hinj _ _

/-- On two lists the wrapper agrees with `editDistanceList`. -/
theorem editDistanceSeq_lst (l1 l2 : List Nat) :
    editDistanceSeq (.lst l1) (.lst l2) = .ok (editDistanceList l1 l2) := by
  have hinj : Function.Injective Elem.num := fun _ _ hh => by injection hh
  have hpre : Pre (.lst l1) (.lst l2) := by simp [Pre, SeqInput.isSequence]
  rw [editDistanceSeq, if_pos hpre, editDistanceList]
  congr 1
  show editDistance (l1.map Elem.num) (l2.map Elem.num) = editDistance l1 l2
  exact editDistance_map Elem.num hinj _ _

/-- A non-sequence argument always produces the Python `ValueError` message. -/
theorem editDistanceSeq_invalid_left (n : Nat) (y : SeqInput) :
    editDistanceSeq (.invalid n) y = .error "Inputs must be str or list" := by
  rw [editDistanceSeq, if_neg (Pre_invalid_left n y)]

theorem editDistanceSeq_invalid_right (x : SeqInput) (n : Nat) :
    editDistanceSeq x (.invalid n) = .error "Inputs must be str or list" := by
  rw [editDistanceSeq, if_neg (Pre_invalid_right x n)]

/-! ## Imperative implementation -/

section Imperative

variable {α : Type} [DecidableEq α]

/-- Imperative version of the dynamic program: the current row of the DP table is held
in a mutable variable which is overwritten inside a `for` loop (`Id.run do`). -/
def editDistanceImp (s t : List α) : Nat :=
  Id.run do
    let mut row : List Nat := initRow s
    for b in t.reverse do
      row := nextRow b s row
    return row.getD 0 0

/-- The left fold performed by the imperative loop is the right fold of `dpRows`,
because the loop walks the second sequence from its last element to its first. -/
theorem foldl_reverse_nextRow (s : List α) : ∀ (t : List α) (r0 : List Nat),
    List.foldl (fun r b => nextRow b s r) r0 t.reverse =
      List.foldr (fun b r => nextRow b s r) r0 t := by
  intro t
  induction t with
  | nil => intro r0; rfl
  | cons b t' ih =>
    intro r0
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldr_cons]
    rw [ih]

end Imperative

def editDistanceImpStr (s1 s2 : String) : Nat := editDistanceImp s1.toList s2.toList

def editDistanceImpList (l1 l2 : List Nat) : Nat := editDistanceImp l1 l2

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
example : editDistanceImpStr "a" "b" = 1 := by native_decide
example : editDistanceImpStr "intention" "execution" = 5 := by native_decide
example : editDistanceImpStr "saturday" "sunday" = 3 := by native_decide
example : editDistanceImpStr "abc" "def" = 3 := by native_decide
example : editDistanceImpStr "aaa" "aa" = 1 := by native_decide
example : editDistanceImpStr "aa" "aaa" = 1 := by native_decide
example : editDistanceImpStr "aaaa" "bbbb" = 4 := by native_decide
example : editDistanceImpList [1, 2, 3] [1, 2, 3] = 0 := by native_decide
example : editDistanceImpList [1, 2, 3] [1, 4, 3] = 1 := by native_decide
example : editDistanceImpList [1, 2, 3, 4] [1, 3, 4] = 1 := by native_decide
example : editDistanceImpList [1, 2, 3] [4, 5, 6] = 3 := by native_decide
example : editDistanceImpList [1, 2, 3, 4, 5] [6, 7, 8] = 5 := by native_decide
example : editDistanceImp ['c', 'a', 't'] ['b', 'a', 't'] = 1 := by native_decide
example : editDistanceImp ['h', 'e', 'l', 'l', 'o'] ['h', 'e', 'l', 'l', 'o'] = 0 := by native_decide

#eval editDistanceImpStr "kitten" "sitting"
#eval editDistanceImpStr "saturday" "sunday"
#eval editDistanceImpList [1, 2, 3, 4, 5] [6, 7, 8]

-- bounded property-based test: the imperative loop agrees with the specification
example : (List.product smallLists smallLists).all
    (fun p => editDistanceImp p.1 p.2 = ed p.1 p.2) = true := by native_decide
#eval Plausible.Testable.check
  (∀ xs ys : List Nat, editDistanceImp xs ys = editDistance xs ys)

/-! ## Equivalence: functional = imperative -/

section Equiv

variable {α : Type} [DecidableEq α]

theorem editDistanceImp_eq (s t : List α) : editDistanceImp s t = editDistance s t := by
  simp [editDistanceImp, editDistance, dpRows, foldl_reverse_nextRow]

theorem editDistanceImp_ed (s t : List α) : editDistanceImp s t = ed s t := by
  rw [editDistanceImp_eq, editDistance_eq]

end Equiv

theorem editDistanceImpStr_ed (s1 s2 : String) :
    editDistanceImpStr s1 s2 = ed s1.toList s2.toList := editDistanceImp_ed _ _

theorem editDistanceImpList_ed (l1 l2 : List Nat) :
    editDistanceImpList l1 l2 = ed l1 l2 := editDistanceImp_ed _ _

theorem editDistanceImpStr_eq (s1 s2 : String) :
    editDistanceImpStr s1 s2 = editDistanceStr s1 s2 := editDistanceImp_eq _ _

theorem editDistanceImpList_eq (l1 l2 : List Nat) :
    editDistanceImpList l1 l2 = editDistanceList l1 l2 := editDistanceImp_eq _ _

end edit_distance
