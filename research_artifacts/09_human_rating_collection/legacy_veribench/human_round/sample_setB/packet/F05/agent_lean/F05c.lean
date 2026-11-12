import Mathlib

/-!
# edit_distance - Levenshtein edit distance between two sequences

Formalisation of the Python program

```
def pre(s1, s2) -> bool:
    return isinstance(s1, (str, list)) and isinstance(s2, (str, list))

def edit_distance(s1, s2) -> int:
    if not pre(s1, s2):
        raise ValueError("Inputs must be str or list")
    ...  # classical dynamic programming table for the Levenshtein distance
```

## Modelling decisions

* Python accepts a `str` *or* a `list`; both are finite sequences of elements.
  The admissible inputs are modelled by the inductive type `Input` below
  (`.str` for strings, `.lst` for lists of integers) and inadmissible inputs
  (such as the integer `123` of the negative test) by `.num`.
  `Pre` is exactly Python's `pre`, and `editDistanceOpt` returns `none`
  exactly where Python raises `ValueError`.
* The distance itself is developed for an arbitrary element type `α` with
  decidable equality, so it covers strings (`α = Char`) and lists of integers
  (`α = Int`) at once, as the Python tests require.
* `editDistance` is the mathematical specification of the Levenshtein distance
  (proved symmetric, definite, bounded by the length difference / maximum, and
  to satisfy the triangle inequality).  `editDistanceDP` is the pure
  dynamic-programming row iteration of the Python program and `editDistanceImp`
  is its imperative `Id.run do` transcription with a mutable row; all three are
  proved equal.
-/


namespace edit_distance

section Induction2

theorem listStrongInduction₂ {α : Type u} {P : List α → List α → Prop}
    (h : ∀ xs ys,
      (∀ xs' ys', xs'.length + ys'.length < xs.length + ys.length → P xs' ys') → P xs ys) :
    ∀ xs ys, P xs ys := by
  have key : ∀ n : Nat, ∀ xs ys : List α, xs.length + ys.length = n → P xs ys := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro xs ys hxy
      exact h xs ys (fun xs' ys' hlt => ih (xs'.length + ys'.length) (by omega) xs' ys' rfl)
  exact fun xs ys => key _ xs ys rfl

end Induction2

section Functional

variable {α : Type*} [DecidableEq α]

def edCore : List α → List α → Nat
  | [], ys => ys.length
  | xs, [] => xs.length
  | (a :: xs), (b :: ys) =>
      if a = b then edCore xs ys
      else 1 + min (edCore xs (b :: ys)) (min (edCore (a :: xs) ys) (edCore xs ys))
termination_by xs ys => (xs.length, ys.length)

theorem edCore_nil (ys : List α) : edCore [] ys = ys.length := by simp [edCore]

theorem edCore_nil_right (xs : List α) : edCore xs [] = xs.length := by
  cases xs <;> simp [edCore]

theorem edCore_cons (a b : α) (xs ys : List α) :
    edCore (a :: xs) (b :: ys) =
      if a = b then edCore xs ys
      else 1 + min (edCore xs (b :: ys)) (min (edCore (a :: xs) ys) (edCore xs ys)) := by
  simp [edCore]

def editDistance (xs ys : List α) : Nat := edCore xs.reverse ys.reverse

theorem editDistance_nil_left (ys : List α) : editDistance [] ys = ys.length := by
  simp [editDistance, edCore_nil]

theorem editDistance_nil_right (xs : List α) : editDistance xs [] = xs.length := by
  simp [editDistance, edCore_nil_right]

theorem editDistance_append (us vs : List α) (a b : α) :
    editDistance (us ++ [a]) (vs ++ [b]) =
      if a = b then editDistance us vs
      else 1 + min (editDistance us (vs ++ [b]))
        (min (editDistance (us ++ [a]) vs) (editDistance us vs)) := by
  have h1 : (us ++ [a]).reverse = a :: us.reverse := by simp
  have h2 : (vs ++ [b]).reverse = b :: vs.reverse := by simp
  simp only [editDistance, h1, h2, edCore_cons]

theorem edCore_self (xs : List α) : edCore xs xs = 0 := by
  have key : ∀ xs ys : List α, xs = ys → edCore xs ys = 0 := by
    refine listStrongInduction₂ (P := fun xs ys => xs = ys → edCore xs ys = 0) ?_
    intro xs ys ih h
    cases xs with
    | nil =>
        cases ys with
        | nil => simp [edCore]
        | cons b ys' => exact absurd h.symm (by simp)
    | cons a xs' =>
        cases ys with
        | nil => exact absurd h (by simp)
        | cons b ys' =>
          obtain ⟨hab, hxy⟩ := List.cons.inj h
          subst hab
          subst hxy
          rw [edCore_cons, if_pos rfl]
          exact ih xs' xs' (by simp only [List.length_cons]; omega) rfl
  exact key xs xs rfl

theorem edCore_zero_iff {xs ys : List α} : edCore xs ys = 0 ↔ xs = ys := by
  constructor
  · have key : ∀ xs ys : List α, edCore xs ys = 0 → xs = ys := by
      refine listStrongInduction₂ (P := fun xs ys => edCore xs ys = 0 → xs = ys) ?_
      intro xs ys ih h
      cases xs with
      | nil =>
          rw [edCore_nil] at h
          cases ys with
          | nil => rfl
          | cons b ys' => simp only [List.length_cons] at h; omega
      | cons a xs' =>
          cases ys with
          | nil =>
            rw [edCore_nil_right] at h
            simp only [List.length_cons] at h
            omega
          | cons b ys' =>
            by_cases hab : a = b
            · rw [edCore_cons, if_pos hab] at h
              have hxy := ih xs' ys' (by simp only [List.length_cons]; omega) h
              rw [hab, hxy]
            · rw [edCore_cons, if_neg hab] at h
              omega
    exact key xs ys
  · intro h; rw [h]; exact edCore_self _

theorem edCore_symm : ∀ xs ys : List α, edCore xs ys = edCore ys xs := by
  refine listStrongInduction₂ (P := fun xs ys => edCore xs ys = edCore ys xs) ?_
  intro xs ys ih
  cases xs with
  | nil => simp [edCore_nil, edCore_nil_right]
  | cons a xs' =>
    cases ys with
    | nil => simp [edCore_nil, edCore_nil_right]
    | cons b ys' =>
      have h1 := ih xs' (b :: ys') (by simp only [List.length_cons]; omega)
      have h2 := ih (a :: xs') ys' (by simp only [List.length_cons]; omega)
      have h3 := ih xs' ys' (by simp only [List.length_cons]; omega)
      rw [edCore_cons, edCore_cons, h1, h2, h3]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab.symm]
      · rw [if_neg hab, if_neg (fun h => hab h.symm)]
        omega

theorem edCore_le_max : ∀ xs ys : List α, edCore xs ys ≤ max xs.length ys.length := by
  refine listStrongInduction₂ (P := fun xs ys => edCore xs ys ≤ max xs.length ys.length) ?_
  intro xs ys ih
  cases xs with
  | nil => simp only [List.length_nil, edCore_nil]; omega
  | cons a xs' =>
    cases ys with
    | nil => simp only [List.length_nil, List.length_cons, edCore_nil_right]; omega
    | cons b ys' =>
      have h1 := ih xs' (b :: ys') (by simp only [List.length_cons]; omega)
      have h2 := ih (a :: xs') ys' (by simp only [List.length_cons]; omega)
      have h3 := ih xs' ys' (by simp only [List.length_cons]; omega)
      simp only [List.length_cons] at *
      rw [edCore_cons]
      split <;> omega

theorem edCore_length_bound : ∀ xs ys : List α,
    max xs.length ys.length ≤ edCore xs ys + min xs.length ys.length := by
  refine listStrongInduction₂
    (P := fun xs ys => max xs.length ys.length ≤ edCore xs ys + min xs.length ys.length) ?_
  intro xs ys ih
  cases xs with
  | nil => simp only [List.length_nil, edCore_nil]; omega
  | cons a xs' =>
    cases ys with
    | nil => simp only [List.length_nil, List.length_cons, edCore_nil_right]; omega
    | cons b ys' =>
      have h1 := ih xs' (b :: ys') (by simp only [List.length_cons]; omega)
      have h2 := ih (a :: xs') ys' (by simp only [List.length_cons]; omega)
      have h3 := ih xs' ys' (by simp only [List.length_cons]; omega)
      simp only [List.length_cons] at *
      rw [edCore_cons]
      split <;> omega

theorem edCore_cons_bounds : ∀ xs ys : List α,
    (∀ a : α, edCore (a :: xs) ys ≤ edCore xs ys + 1) ∧
    (∀ b : α, edCore xs ys ≤ edCore xs (b :: ys) + 1) := by
  refine listStrongInduction₂ (P := fun xs ys =>
    (∀ a : α, edCore (a :: xs) ys ≤ edCore xs ys + 1) ∧
    (∀ b : α, edCore xs ys ≤ edCore xs (b :: ys) + 1)) ?_
  intro xs ys ih
  cases xs with
  | nil =>
      constructor
      · intro a
        have h := edCore_le_max ([a] : List α) ys
        have h2 := edCore_nil ys
        simp at h
        omega
      · intro b
        rw [edCore_nil, edCore_nil]
        simp only [List.length_cons]
        omega
  | cons x xs' =>
    cases ys with
    | nil =>
      constructor
      · intro a
        simp only [List.length_cons, List.length_nil, edCore_nil_right]
        omega
      · intro e
        have h := edCore_length_bound (x :: xs') ([e] : List α)
        simp only [List.length_cons, List.length_nil, edCore_nil_right] at h ⊢
        omega
    | cons y ys' =>
      have ih1 := ih xs' ys' (by simp only [List.length_cons]; omega)
      have ih2 := ih xs' (y :: ys') (by simp only [List.length_cons]; omega)
      have ih3 := ih (y :: ys') xs' (by simp only [List.length_cons]; omega)
      have ih4 := ih (x :: xs') ys' (by simp only [List.length_cons]; omega)
      constructor
      · intro a
        rw [edCore_cons a y (x :: xs') ys']
        by_cases hab : a = y
        · subst hab
          rw [if_pos rfl]
          exact ih4.2 a
        · rw [if_neg hab]
          omega
      · intro e
        rw [edCore_cons x y xs' ys', edCore_cons x e xs' (y :: ys')]
        by_cases hxy : x = y
        · subst hxy
          by_cases hxe : x = e
          · subst hxe
            rw [if_pos rfl, if_pos rfl]
            exact ih1.2 x
          · rw [if_pos rfl, if_neg hxe]
            have hZ : edCore xs' ys' ≤ edCore xs' (x :: ys') + 1 := ih1.2 x
            have hY : edCore xs' (x :: ys') ≤ edCore (x :: xs') (x :: ys') + 1 := by
              have h := ih3.2 x
              rw [edCore_symm (x :: ys') xs', edCore_symm (x :: ys') (x :: xs')] at h
              exact h
            have hX : edCore xs' (x :: ys') ≤ edCore xs' (e :: x :: ys') + 1 := ih2.2 e
            omega
        · by_cases hxe : x = e
          · subst hxe
            rw [if_neg hxy, if_pos rfl]
            omega
          · rw [if_neg hxy, if_neg hxe]
            have hX : edCore xs' (y :: ys') ≤ edCore xs' (e :: y :: ys') + 1 := ih2.2 e
            have hY : edCore xs' (y :: ys') ≤ edCore (x :: xs') (y :: ys') + 1 := by
              have h := ih3.2 x
              rw [edCore_symm (y :: ys') xs', edCore_symm (y :: ys') (x :: xs')] at h
              exact h
            omega

theorem edCore_cons_le (a : α) (xs ys : List α) : edCore (a :: xs) ys ≤ edCore xs ys + 1 :=
  (edCore_cons_bounds xs ys).1 a

theorem edCore_le_cons2 (b : α) (xs ys : List α) : edCore xs ys ≤ edCore xs (b :: ys) + 1 :=
  (edCore_cons_bounds xs ys).2 b

theorem edCore_cons2_le (b : α) (xs ys : List α) : edCore xs (b :: ys) ≤ edCore xs ys + 1 := by
  have h := edCore_cons_le b ys xs
  rw [edCore_symm (b :: ys) xs, edCore_symm ys xs] at h
  exact h

theorem edCore_le_cons (a : α) (xs ys : List α) : edCore xs ys ≤ edCore (a :: xs) ys + 1 := by
  have h := edCore_le_cons2 a ys xs
  rw [edCore_symm ys (a :: xs), edCore_symm ys xs] at h
  exact h

theorem edCore_cons_cons_le (xs ys : List α) (a b : α) :
    edCore (a :: xs) (b :: ys) ≤ edCore xs ys + 1 := by
  by_cases hab : a = b
  · rw [edCore_cons, if_pos hab]; omega
  · rw [edCore_cons, if_neg hab]; omega

theorem edCore_append_cancel (t p q : List α) : edCore (t ++ p) (t ++ q) = edCore p q := by
  induction t generalizing p q with
  | nil => simp
  | cons a t ih =>
    rw [List.cons_append, List.cons_append, edCore_cons, if_pos rfl, ih]


theorem edCore_triangle : ∀ xs zs : List α, ∀ ys : List α,
    edCore xs zs ≤ edCore xs ys + edCore ys zs := by
  refine listStrongInduction₂
    (P := fun xs zs => ∀ ys : List α, edCore xs zs ≤ edCore xs ys + edCore ys zs) ?_
  intro xs zs ih ys
  cases xs with
  | nil =>
      rw [edCore_nil, edCore_nil]
      have h := edCore_length_bound ys zs
      omega
  | cons a xs' =>
    cases zs with
    | nil =>
      rw [edCore_nil_right, edCore_nil_right]
      have h := edCore_length_bound (a :: xs') ys
      omega
    | cons c zs' =>
      cases ys with
      | nil =>
        rw [edCore_nil_right, edCore_nil]
        have h := edCore_le_max (a :: xs') (c :: zs')
        simp only [List.length_cons, List.length_nil] at h ⊢
        omega
      | cons b ys' =>
        have ih1 := ih xs' (c :: zs') (by simp only [List.length_cons]; omega)
        have ih2 := ih (a :: xs') zs' (by simp only [List.length_cons]; omega)
        have ih3 := ih xs' zs' (by simp only [List.length_cons]; omega)
        have t1 := ih1 ys'
        have t2 := ih1 (b :: ys')
        have t3 := ih2 ys'
        have t4 := ih2 (b :: ys')
        have t5 := ih3 ys'
        have t6 := ih3 (b :: ys')
        have b1 := edCore_le_cons2 b xs' ys'
        have b2 := edCore_cons2_le b xs' ys'
        have b3 := edCore_le_cons a xs' ys'
        have b4 := edCore_cons_le a xs' ys'
        have b5 := edCore_le_cons2 c ys' zs'
        have b6 := edCore_cons2_le c ys' zs'
        have b7 := edCore_le_cons b ys' zs'
        have b8 := edCore_cons_le b ys' zs'
        by_cases hac : a = c
        · by_cases hab : a = b
          · have hbc : b = c := hab.symm.trans hac
            rw [edCore_cons a c xs' zs', edCore_cons a b xs' ys', edCore_cons b c ys' zs',
                if_pos hac, if_pos hab, if_pos hbc]
            exact t5
          · have hbc : ¬(b = c) := fun h => hab ((h.trans hac.symm).symm)
            have hBC : edCore (b :: ys') (c :: zs') =
                1 + min (edCore ys' (c :: zs'))
                  (min (edCore (b :: ys') zs') (edCore ys' zs')) := by
              rw [edCore_cons b c ys' zs', if_neg hbc]
            rw [edCore_cons a c xs' zs', edCore_cons a b xs' ys', edCore_cons b c ys' zs',
                if_pos hac, if_neg hab, if_neg hbc]
            simp only [hBC] at t2
            omega
        · by_cases hab : a = b
          · have hbc : ¬(b = c) := fun h => hac (hab.trans h)
            have hA : edCore (a :: xs') (b :: ys') = edCore xs' ys' := by
              rw [edCore_cons a b xs' ys', if_pos hab]
            rw [edCore_cons a c xs' zs', edCore_cons a b xs' ys', edCore_cons b c ys' zs',
                if_neg hac, if_pos hab, if_neg hbc]
            simp only [hA] at t4
            omega
          · by_cases hbc : b = c
            · have hF : edCore (b :: ys') (c :: zs') = edCore ys' zs' := by
                rw [edCore_cons b c ys' zs', if_pos hbc]
              rw [edCore_cons a c xs' zs', edCore_cons a b xs' ys', edCore_cons b c ys' zs',
                  if_neg hac, if_neg hab, if_pos hbc]
              simp only [hF] at t2
              omega
            · have hAB : edCore (a :: xs') (b :: ys') =
                  1 + min (edCore xs' (b :: ys'))
                    (min (edCore (a :: xs') ys') (edCore xs' ys')) := by
                rw [edCore_cons a b xs' ys', if_neg hab]
              have hBC : edCore (b :: ys') (c :: zs') =
                  1 + min (edCore ys' (c :: zs'))
                    (min (edCore (b :: ys') zs') (edCore ys' zs')) := by
                rw [edCore_cons b c ys' zs', if_neg hbc]
              rw [edCore_cons a c xs' zs', edCore_cons a b xs' ys', edCore_cons b c ys' zs',
                  if_neg hac, if_neg hab, if_neg hbc]
              simp only [hAB] at t4
              simp only [hBC] at t2
              omega

end Functional

section Properties

variable {α : Type*} [DecidableEq α]

theorem editDistance_self (xs : List α) : editDistance xs xs = 0 := edCore_self _

theorem editDistance_zero_iff {xs ys : List α} : editDistance xs ys = 0 ↔ xs = ys := by
  constructor
  · intro h
    exact List.reverse_inj.1 (edCore_zero_iff.1 h)
  · intro h; rw [h]; exact editDistance_self _

theorem editDistance_pos_iff {xs ys : List α} : 0 < editDistance xs ys ↔ xs ≠ ys := by
  constructor
  · intro h heq; rw [heq, editDistance_self] at h; omega
  · intro h
    have h0 : editDistance xs ys ≠ 0 := fun hd => h (editDistance_zero_iff.1 hd)
    omega

theorem editDistance_symm (xs ys : List α) : editDistance xs ys = editDistance ys xs :=
  edCore_symm _ _

theorem editDistance_le_max_length (xs ys : List α) :
    editDistance xs ys ≤ max xs.length ys.length := by
  have h := edCore_le_max xs.reverse ys.reverse
  simp only [List.length_reverse] at h
  exact h

theorem editDistance_length_bound (xs ys : List α) :
    max xs.length ys.length ≤ editDistance xs ys + min xs.length ys.length := by
  have h := edCore_length_bound xs.reverse ys.reverse
  simp only [List.length_reverse] at h
  exact h

theorem editDistance_triangle (xs ys zs : List α) :
    editDistance xs zs ≤ editDistance xs ys + editDistance ys zs :=
  edCore_triangle _ _ _

theorem editDistance_append_le (a : α) (xs ys : List α) :
    editDistance (xs ++ [a]) ys ≤ editDistance xs ys + 1 := by
  have h1 : (xs ++ [a]).reverse = a :: xs.reverse := by simp
  simp only [editDistance, h1]
  exact edCore_cons_le a xs.reverse ys.reverse

theorem editDistance_le_append (a : α) (xs ys : List α) :
    editDistance xs ys ≤ editDistance (xs ++ [a]) ys + 1 := by
  have h1 : (xs ++ [a]).reverse = a :: xs.reverse := by simp
  simp only [editDistance, h1]
  exact edCore_le_cons a xs.reverse ys.reverse

theorem editDistance_append2_le (b : α) (xs ys : List α) :
    editDistance xs (ys ++ [b]) ≤ editDistance xs ys + 1 := by
  have h1 : (ys ++ [b]).reverse = b :: ys.reverse := by simp
  simp only [editDistance, h1]
  exact edCore_cons2_le b xs.reverse ys.reverse

theorem editDistance_le_append2 (b : α) (xs ys : List α) :
    editDistance xs ys ≤ editDistance xs (ys ++ [b]) + 1 := by
  have h1 : (ys ++ [b]).reverse = b :: ys.reverse := by simp
  simp only [editDistance, h1]
  exact edCore_le_cons2 b xs.reverse ys.reverse

theorem editDistance_suffix (p q t : List α) :
    editDistance (p ++ t) (q ++ t) = editDistance p q := by
  have h1 : (p ++ t).reverse = t.reverse ++ p.reverse := by simp
  have h2 : (q ++ t).reverse = t.reverse ++ q.reverse := by simp
  have h3 : edCore (t.reverse ++ p.reverse) (t.reverse ++ q.reverse) =
      edCore p.reverse q.reverse := edCore_append_cancel t.reverse p.reverse q.reverse
  rw [editDistance, editDistance, h1, h2, h3]

theorem editDistance_singleton (a b : α) :
    editDistance [a] [b] = if a = b then 0 else 1 := by
  have h1 : ([a] : List α).reverse = [a] := by simp
  have h2 : ([b] : List α).reverse = [b] := by simp
  rw [editDistance, h1, h2, edCore_cons a b [] []]
  simp [edCore_nil, edCore_nil_right]

end Properties

section UnitTests

/-- Edit distance between two strings (Python's `str` case). -/
def strDist (s t : String) : Nat := editDistance s.toList t.toList

example : strDist "hello" "hello" = 0 := by native_decide
example : strDist "cat" "bat" = 1 := by native_decide
example : strDist "cat" "cats" = 1 := by native_decide
example : strDist "cats" "cat" = 1 := by native_decide
example : strDist "cat" "dog" = 3 := by native_decide
example : strDist "kitten" "sitting" = 3 := by native_decide
example : strDist "" "" = 0 := by native_decide
example : strDist "" "abc" = 3 := by native_decide
example : strDist "ab" "" = 2 := by native_decide
example : strDist "a" "b" = 1 := by native_decide
example : strDist "intention" "execution" = 5 := by native_decide
example : strDist "saturday" "sunday" = 3 := by native_decide
example : strDist "abc" "def" = 3 := by native_decide
example : strDist "xyz" "abc" = 3 := by native_decide
example : strDist "a" "a" = 0 := by native_decide
example : strDist "a" "" = 1 := by native_decide
example : strDist "" "a" = 1 := by native_decide
example : strDist "aaa" "aa" = 1 := by native_decide
example : strDist "aa" "aaa" = 1 := by native_decide
example : strDist "aaaa" "bbbb" = 4 := by native_decide

example : editDistance (['h','e','l','l','o'] : List Char)
    (['h','e','l','l','o'] : List Char) = 0 := by native_decide
example : editDistance (['c','a','t'] : List Char) (['b','a','t'] : List Char) = 1 := by native_decide
example : editDistance (['c','a','t'] : List Char)
    (['c','a','t','s'] : List Char) = 1 := by native_decide
example : editDistance (['c','a','t','s'] : List Char)
    (['c','a','t'] : List Char) = 1 := by native_decide

example : editDistance ([1,2,3] : List Nat) ([1,2,3] : List Nat) = 0 := by native_decide
example : editDistance ([1,2,3] : List Nat) ([1,4,3] : List Nat) = 1 := by native_decide
example : editDistance ([1,2,3,4] : List Nat) ([1,3,4] : List Nat) = 1 := by native_decide
example : editDistance ([1,2,3] : List Nat) ([4,5,6] : List Nat) = 3 := by native_decide
example : editDistance ([1,2,3,4,5] : List Nat) ([6,7,8] : List Nat) = 5 := by native_decide
example : editDistance ([1,2,-3] : List Int) ([1,2,-3] : List Int) = 0 := by native_decide
example : editDistance ([1,2,-3] : List Int) ([1,4,-3] : List Int) = 1 := by native_decide
example : editDistance ([] : List Nat) ([] : List Nat) = 0 := by native_decide
example : editDistance ([] : List Nat) ([7,8,9] : List Nat) = 3 := by native_decide

#eval strDist "kitten" "sitting"
#eval strDist "intention" "execution"
#eval editDistance ([1,2,3,4,5] : List Nat) ([6,7,8] : List Nat)
#eval editDistance ([1,2,-3] : List Int) ([1,4,-3] : List Int)

end UnitTests

section DP

variable {α : Type*} [DecidableEq α]

/-! ### The dynamic-programming implementation (Python's `dp` table, one row at a time)

`rowStep a ys prev` turns the row `prev[j] = editDistance us (ys.take j)` into the row
for `us ++ [a]`, exactly the inner loop of the Python program:
`dp[i][0] = i` and `dp[i][j+1] = if a = ys[j] then dp[i-1][j]
else 1 + min dp[i-1][j+1] dp[i][j] dp[i-1][j]`.
-/

def rowGo (a : α) (cur : Nat) : List α → List Nat → List Nat
  | [], _ => []
  | _, [] => []
  | _ :: _, _ :: [] => []
  | b :: ys, p :: q :: prev =>
      (if a = b then p else 1 + min q (min cur p)) ::
        rowGo a (if a = b then p else 1 + min q (min cur p)) ys (q :: prev)

theorem rowGo_nil (a : α) (cur : Nat) (prev : List Nat) : rowGo a cur [] prev = [] := by
  simp [rowGo]

theorem rowGo_cons (a b : α) (cur p q : Nat) (ys : List α) (prev : List Nat) :
    rowGo a cur (b :: ys) (p :: q :: prev) =
      (if a = b then p else 1 + min q (min cur p)) ::
        rowGo a (if a = b then p else 1 + min q (min cur p)) ys (q :: prev) := by
  simp [rowGo]

def rowStep (a : α) (ys : List α) (prev : List Nat) : List Nat :=
  match prev with
  | [] => []
  | p0 :: _ => (p0 + 1) :: rowGo a (p0 + 1) ys prev

theorem rowStep_cons (a : α) (ys : List α) (p0 : Nat) (row' : List Nat) :
    rowStep a ys (p0 :: row') = (p0 + 1) :: rowGo a (p0 + 1) ys (p0 :: row') := by
  simp [rowStep]

theorem length_rowGo (a : α) : ∀ (cur : Nat) (ys : List α) (prev : List Nat),
    (rowGo a cur ys prev).length = min ys.length (prev.length - 1) := by
  intro cur ys prev
  induction ys generalizing cur prev with
  | nil => simp [rowGo]
  | cons b ys' ih =>
      cases prev with
      | nil => simp [rowGo]
      | cons p rest =>
        cases rest with
        | nil => simp [rowGo]
        | cons q prev' =>
          rw [rowGo_cons, List.length_cons, ih _ (q :: prev')]
          simp only [List.length_cons]
          omega

theorem rowGo_correct (a : α) (us : List α) (ys : List α) :
    ∀ (ys' : List α) (prev' : List Nat) (k cur : Nat),
      prev'.length = ys'.length + 1 →
      k + ys'.length ≤ ys.length →
      (∀ (j : Nat), j < prev'.length →
        prev'.getD j 0 = editDistance us (ys.take (k + j))) →
      (∀ (j : Nat), ys'[j]? = ys[k + j]?) →
      cur = editDistance (us ++ [a]) (ys.take k) →
      rowGo a cur ys' prev' =
        (List.range ys'.length).map
          (fun i => editDistance (us ++ [a]) (ys.take (k + 1 + i))) := by
  intro ys'
  induction ys' with
  | nil =>
      intro prev' k cur hlen hkle hprev hys hcur
      simp [rowGo]
  | cons b ys'' ih =>
      intro prev' k cur hlen hkle hprev hys hcur
      cases prev' with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons p rest =>
        cases rest with
        | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
        | cons q prev'' =>
          simp only [List.length_cons] at hlen hkle
          have hk : k < ys.length := by omega
          have hb : b = ys[k]'hk := by
            have h0 := hys 0
            simp only [List.getElem?_cons_zero, Nat.add_zero,
              List.getElem?_eq_getElem hk] at h0
            injection h0
          have htake : ys.take (k + 1) = ys.take k ++ [b] := by
            rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, ← hb]
          have hp : p = editDistance us (ys.take k) := by
            have := hprev 0 (by simp only [List.length_cons]; omega)
            simp only [List.getD_cons_zero, Nat.add_zero] at this
            exact this
          have hq : q = editDistance us (ys.take (k + 1)) := by
            have := hprev 1 (by simp only [List.length_cons]; omega)
            simp only [List.getD_cons_succ, List.getD_cons_zero] at this
            exact this
          have hq2 : editDistance us (ys.take k ++ [b]) = q := by
            rw [← htake, hq]
          have hv : (if a = b then p else 1 + min q (min cur p)) =
              editDistance (us ++ [a]) (ys.take (k + 1)) := by
            rw [htake, editDistance_append us (ys.take k) a b, hq2, ← hcur, ← hp]
          have hlen2 : (q :: prev'').length = ys''.length + 1 := by
            simp only [List.length_cons]; omega
          have hkle2 : (k + 1) + ys''.length ≤ ys.length := by omega
          have hprev2 : ∀ (j : Nat), j < (q :: prev'').length →
              (q :: prev'').getD j 0 = editDistance us (ys.take (k + 1 + j)) := by
            intro j hj
            have hj' : j + 1 < (p :: q :: prev'').length := by
              simp only [List.length_cons] at hlen hj ⊢
              omega
            have h := hprev (j + 1) hj'
            simp only [List.getD_cons_succ] at h
            have e : k + (j + 1) = k + 1 + j := by omega
            rw [e] at h
            exact h
          have hys2 : ∀ (j : Nat), ys''[j]? = ys[k + 1 + j]? := by
            intro j
            have h := hys (j + 1)
            rw [List.getElem?_cons_succ] at h
            have e : k + (j + 1) = k + 1 + j := by omega
            rw [e] at h
            exact h
          have hih := ih (q :: prev'') (k + 1)
            (if a = b then p else 1 + min q (min cur p)) hlen2 hkle2 hprev2 hys2 hv
          have hrl : (b :: ys'').length = ys''.length + 1 := List.length_cons
          rw [rowGo_cons, hih, hrl]
          simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_apply,
            Nat.succ_eq_add_one, Nat.add_zero, Nat.zero_add]
          have hfn : (fun i => editDistance (us ++ [a]) (ys.take (k + 1 + 1 + i))) =
              ((fun i => editDistance (us ++ [a]) (ys.take (k + 1 + i))) ∘ Nat.succ) := by
            funext i
            simp only [Function.comp_apply, Nat.succ_eq_add_one]
            apply congrArg (fun t => editDistance (us ++ [a]) (ys.take t))
            omega
          rw [hv, hfn]

theorem rowStep_correct (a : α) (us : List α) (ys : List α) (row : List Nat)
    (hlen : row.length = ys.length + 1)
    (hrow : ∀ (j : Nat), j < row.length → row.getD j 0 = editDistance us (ys.take j)) :
    rowStep a ys row =
      (List.range (ys.length + 1)).map (fun j => editDistance (us ++ [a]) (ys.take j)) := by
  cases row with
  | nil => simp at hlen
  | cons p0 row' =>
    have hp0 : p0 = editDistance us (ys.take 0) := by
      have := hrow 0 (by simp only [List.length_cons]; omega)
      simp only [List.getD_cons_zero] at this
      exact this
    have hcur : p0 + 1 = editDistance (us ++ [a]) (ys.take 0) := by
      rw [hp0, List.take_zero, editDistance_nil_right, editDistance_nil_right]
      simp
    have hprev : ∀ (j : Nat), j < (p0 :: row').length →
        (p0 :: row').getD j 0 = editDistance us (ys.take (0 + j)) := by
      intro j hj
      have h := hrow j hj
      simp only [Nat.zero_add]
      exact h
    have hys : ∀ (j : Nat), ys[j]? = ys[0 + j]? := by intro j; rw [Nat.zero_add]
    have hgo := rowGo_correct a us ys ys (p0 :: row') 0 (p0 + 1) hlen (by omega)
      hprev hys hcur
    rw [rowStep_cons, hgo]
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_apply,
      Nat.succ_eq_add_one, Nat.add_zero, Nat.zero_add]
    have hfn : (fun i => editDistance (us ++ [a]) (ys.take (1 + i))) =
        ((fun j => editDistance (us ++ [a]) (ys.take j)) ∘ Nat.succ) := by
      funext i
      simp only [Function.comp_apply, Nat.succ_eq_add_one]
      apply congrArg (fun t => editDistance (us ++ [a]) (ys.take t))
      omega
    rw [← hcur, hfn]

theorem dpRow_correct (ys : List α) :
    ∀ (us vs : List α) (row : List Nat),
      row.length = ys.length + 1 →
      (row = (List.range (ys.length + 1)).map (fun j => editDistance us (ys.take j))) →
      vs.foldl (fun r a => rowStep a ys r) row =
        (List.range (ys.length + 1)).map (fun j => editDistance (us ++ vs) (ys.take j)) := by
  intro us vs row hlen hrow
  induction vs generalizing us row with
  | nil =>
      simp only [List.foldl_nil, List.append_nil, hrow]
  | cons a vs' ih =>
      have hget : ∀ (j : Nat), j < row.length → row.getD j 0 = editDistance us (ys.take j) := by
        intro j hj
        have hj' : j < ((List.range (ys.length + 1)).map
            (fun jj => editDistance us (ys.take jj))).length := by rw [← hrow]; exact hj
        have e1 : row.getD j 0 = ((List.range (ys.length + 1)).map
            (fun jj => editDistance us (ys.take jj))).getD j 0 := by rw [hrow]
        have e2 : ((List.range (ys.length + 1)).map
            (fun jj => editDistance us (ys.take jj))).getD j 0 =
            editDistance us (ys.take j) := by
          rw [List.getD_eq_getElem _ _ hj', List.getElem_map, List.getElem_range]
        rw [e1, e2]
      have hr := rowStep_correct a us ys row hlen hget
      have hlen' : (rowStep a ys row).length = ys.length + 1 := by rw [hr]; simp
      have e : us ++ (a :: vs') = (us ++ [a]) ++ vs' := by simp
      rw [List.foldl_cons, e]
      exact ih (us ++ [a]) (rowStep a ys row) hlen' hr

def dpFinalRow (xs ys : List α) : List Nat :=
  xs.foldl (fun row a => rowStep a ys row) (List.range (ys.length + 1))

/-- The pure dynamic-programming computation of the edit distance (Python's `dp` table,
  kept as a single rolling row). -/
def editDistanceDP (xs ys : List α) : Nat := (dpFinalRow xs ys).getD ys.length 0

theorem initRow_eq (ys : List α) :
    (List.range (ys.length + 1)) =
      (List.range (ys.length + 1)).map
        (fun j => editDistance ([] : List α) (ys.take j)) := by
  apply List.ext_getElem
  · simp
  · intro j hj1 hj2
    rw [List.getElem_range, List.getElem_map, List.getElem_range,
      editDistance_nil_left, List.length_take]
    simp at hj1
    omega

theorem dpFinalRow_eq (xs ys : List α) :
    dpFinalRow xs ys =
      (List.range (ys.length + 1)).map (fun j => editDistance xs (ys.take j)) := by
  have hlen : (List.range (ys.length + 1)).length = ys.length + 1 := by simp
  have h := dpRow_correct ys [] xs (List.range (ys.length + 1)) hlen (initRow_eq ys)
  simpa [dpFinalRow] using h

theorem editDistanceDP_eq (xs ys : List α) : editDistanceDP xs ys = editDistance xs ys := by
  have hd : dpFinalRow xs ys =
      (List.range (ys.length + 1)).map (fun j => editDistance xs (ys.take j)) :=
    dpFinalRow_eq xs ys
  have h2 : (dpFinalRow xs ys).getD ys.length 0 = editDistance xs ys := by
    rw [hd]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range,
      List.take_length]
  rw [editDistanceDP, h2]

example : editDistanceDP "kitten".toList "sitting".toList = 3 := by native_decide
example : editDistanceDP "intention".toList "execution".toList = 5 := by native_decide
example : editDistanceDP "saturday".toList "sunday".toList = 3 := by native_decide
example : editDistanceDP ([1,2,3,4,5] : List Nat) ([6,7,8] : List Nat) = 5 := by native_decide
#eval editDistanceDP "kitten".toList "sitting".toList

end DP



section PrePost

/-! ## Precondition (Python's `pre`) -/

/-- A Python argument of `edit_distance`: a `str`, a `list`, or a non-sequence value
(modelled by an integer, e.g. the `123` of the negative test). -/
inductive Input where
  | str : String → Input
  | lst : List Int → Input
  | num : Int → Input
  deriving DecidableEq, Repr

/-- The elements of an admissible input, as a uniform `List Int`: a string contributes
its characters (as code points), a list contributes its integers.  `none` for a
non-sequence input. -/
def Input.toSeq : Input → Option (List Int)
  | .str s => some (s.toList.map (fun c => (c.toNat : Int)))
  | .lst l => some l
  | .num _ => none

/-- Python's `pre`: both arguments must be sequences (`str` or `list`). -/
def Pre (s1 s2 : Input) : Prop := s1.toSeq ≠ none ∧ s2.toSeq ≠ none

instance (s1 s2 : Input) : Decidable (Pre s1 s2) :=
  decidable_of_iff (s1.toSeq ≠ none ∧ s2.toSeq ≠ none) Iff.rfl

theorem Pre_str_str (s t : String) : Pre (.str s) (.str t) := by simp [Pre, Input.toSeq]
theorem Pre_str_lst (s : String) (l : List Int) : Pre (.str s) (.lst l) := by
  simp [Pre, Input.toSeq]
theorem Pre_lst_str (l : List Int) (s : String) : Pre (.lst l) (.str s) := by
  simp [Pre, Input.toSeq]
theorem Pre_lst_lst (l m : List Int) : Pre (.lst l) (.lst m) := by simp [Pre, Input.toSeq]
theorem not_Pre_num_left (v : Int) (s2 : Input) : ¬ Pre (.num v) s2 := by
  simp [Pre, Input.toSeq]
theorem not_Pre_num_right (s1 : Input) (v : Int) : ¬ Pre s1 (.num v) := by
  simp [Pre, Input.toSeq]

theorem Pre_iff_exists (s1 s2 : Input) :
    Pre s1 s2 ↔ (∃ xs, s1.toSeq = some xs) ∧ (∃ ys, s2.toSeq = some ys) := by
  simp only [Pre, Option.ne_none_iff_exists]
  exact ⟨fun ⟨⟨xs, hxs⟩, ys, hys⟩ => ⟨⟨xs, hxs.symm⟩, ys, hys.symm⟩,
    fun ⟨⟨xs, hxs⟩, ys, hys⟩ => ⟨⟨xs, hxs.symm⟩, ys, hys.symm⟩⟩

/-- The Python function.  `none` models `raise ValueError("Inputs must be str or list")`. -/
def editDistanceOpt (s1 s2 : Input) : Option Nat :=
  match s1.toSeq, s2.toSeq with
  | some xs, some ys => some (editDistance xs ys)
  | _, _ => none

theorem editDistanceOpt_str (s t : String) :
    editDistanceOpt (.str s) (.str t) =
      some (editDistance (s.toList.map (fun c => (c.toNat : Int)))
        (t.toList.map (fun c => (c.toNat : Int)))) := by
  simp [editDistanceOpt, Input.toSeq]

theorem editDistanceOpt_lst (l m : List Int) :
    editDistanceOpt (.lst l) (.lst m) = some (editDistance l m) := by
  simp [editDistanceOpt, Input.toSeq]

theorem editDistanceOpt_num_left (v : Int) (s2 : Input) :
    editDistanceOpt (.num v) s2 = none := by
  cases s2 <;> simp [editDistanceOpt, Input.toSeq]

theorem editDistanceOpt_num_right (s1 : Input) (v : Int) :
    editDistanceOpt s1 (.num v) = none := by
  cases s1 <;> simp [editDistanceOpt, Input.toSeq]

example : editDistanceOpt (.num 123) (.str "abc") = none := editDistanceOpt_num_left _ _
example : ¬ Pre (.num 123) (.str "abc") := not_Pre_num_left _ _
example : Pre (.str "cat") (.lst [1, 2]) := Pre_str_lst _ _
#eval editDistanceOpt (.str "kitten") (.str "sitting")
#eval editDistanceOpt (.lst [1,2,3]) (.lst [1,4,3])
#eval editDistanceOpt (.num 123) (.str "abc")

end PrePost

section PropertyStatements

/-! ## Properties of the implementation -/

def nil_left_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (ys : List α), editDistance ([] : List α) ys = ys.length
theorem nil_left_thm : nil_left_prop := fun α _ ys => editDistance_nil_left ys

def nil_right_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs : List α), editDistance xs ([] : List α) = xs.length
theorem nil_right_thm : nil_right_prop := fun α _ xs => editDistance_nil_right xs

def recurrence_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (us vs : List α) (a b : α),
    editDistance (us ++ [a]) (vs ++ [b]) =
      if a = b then editDistance us vs
      else 1 + min (editDistance us (vs ++ [b]))
        (min (editDistance (us ++ [a]) vs) (editDistance us vs))
theorem recurrence_thm : recurrence_prop := fun α _ us vs a b => editDistance_append us vs a b

def self_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs : List α), editDistance xs xs = 0
theorem self_thm : self_prop := fun α _ xs => editDistance_self xs

def zero_iff_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α), editDistance xs ys = 0 ↔ xs = ys
theorem zero_iff_thm : zero_iff_prop := fun α _ xs ys => editDistance_zero_iff

def pos_iff_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α), 0 < editDistance xs ys ↔ xs ≠ ys
theorem pos_iff_thm : pos_iff_prop := fun α _ xs ys => editDistance_pos_iff

def symm_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α), editDistance xs ys = editDistance ys xs
theorem symm_thm : symm_prop := fun α _ xs ys => editDistance_symm xs ys

def upper_bound_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α),
    editDistance xs ys ≤ max xs.length ys.length
theorem upper_bound_thm : upper_bound_prop := fun α _ xs ys => editDistance_le_max_length xs ys

def lower_bound_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α),
    max xs.length ys.length ≤ editDistance xs ys + min xs.length ys.length
theorem lower_bound_thm : lower_bound_prop := fun α _ xs ys => editDistance_length_bound xs ys

def triangle_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys zs : List α),
    editDistance xs zs ≤ editDistance xs ys + editDistance ys zs
theorem triangle_thm : triangle_prop := fun α _ xs ys zs => editDistance_triangle xs ys zs

def suffix_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (p q t : List α),
    editDistance (p ++ t) (q ++ t) = editDistance p q
theorem suffix_thm : suffix_prop := fun α _ p q t => editDistance_suffix p q t

def singleton_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (a b : α),
    editDistance [a] [b] = if a = b then 0 else 1
theorem singleton_thm : singleton_prop := fun α _ a b => editDistance_singleton a b

def insert_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (b : α) (xs ys : List α),
    editDistance xs (ys ++ [b]) ≤ editDistance xs ys + 1 ∧
    editDistance xs ys ≤ editDistance xs (ys ++ [b]) + 1
theorem insert_thm : insert_prop :=
  fun α _ b xs ys => ⟨editDistance_append2_le b xs ys, editDistance_le_append2 b xs ys⟩

def delete_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (a : α) (xs ys : List α),
    editDistance (xs ++ [a]) ys ≤ editDistance xs ys + 1 ∧
    editDistance xs ys ≤ editDistance (xs ++ [a]) ys + 1
theorem delete_thm : delete_prop :=
  fun α _ a xs ys => ⟨editDistance_append_le a xs ys, editDistance_le_append a xs ys⟩

def dp_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α), editDistanceDP xs ys = editDistance xs ys
theorem dp_thm : dp_prop := fun α _ xs ys => editDistanceDP_eq xs ys

def error_prop : Prop :=
  ∀ (s1 s2 : Input), ¬ Pre s1 s2 → editDistanceOpt s1 s2 = none
theorem error_thm : error_prop := by
  intro s1 s2 h
  unfold Pre at h
  by_cases h1 : s1.toSeq = none
  · simp [editDistanceOpt, h1]
  · by_cases h2 : s2.toSeq = none
    · simp [editDistanceOpt, h2]
    · exact absurd ⟨h1, h2⟩ h

def defined_prop : Prop :=
  ∀ (s1 s2 : Input), Pre s1 s2 → ∃ d, editDistanceOpt s1 s2 = some d
theorem defined_thm : defined_prop := by
  intro s1 s2 h
  obtain ⟨⟨xs, hxs⟩, ys, hys⟩ := (Pre_iff_exists s1 s2).mp h
  refine ⟨editDistance xs ys, ?_⟩
  simp [editDistanceOpt, hxs, hys]

def value_prop : Prop :=
  ∀ (s1 s2 : Input) (xs ys : List Int),
    s1.toSeq = some xs → s2.toSeq = some ys →
    editDistanceOpt s1 s2 = some (editDistance xs ys)
theorem value_thm : value_prop := by
  intro s1 s2 xs ys hxs hys
  simp [editDistanceOpt, hxs, hys]

end PropertyStatements

section PostCondition

/-! ## Post-condition -/

def Post_prop (s1 s2 : Input) (r : Option Nat) : Prop :=
  (¬ Pre s1 s2 → r = none) ∧
  (Pre s1 s2 → ∃ xs ys, s1.toSeq = some xs ∧ s2.toSeq = some ys ∧
    r = some (editDistance xs ys) ∧
    (editDistance xs ys = 0 ↔ xs = ys) ∧
    editDistance xs ys ≤ max xs.length ys.length ∧
    max xs.length ys.length ≤ editDistance xs ys + min xs.length ys.length ∧
    editDistance xs ys = editDistance ys xs ∧
    ∀ zs : List Int, editDistance xs zs ≤ editDistance xs ys + editDistance ys zs)

theorem Post_thm (s1 s2 : Input) : Post_prop s1 s2 (editDistanceOpt s1 s2) := by
  constructor
  · exact error_thm s1 s2
  · intro h
    obtain ⟨⟨xs, hxs⟩, ys, hys⟩ := (Pre_iff_exists s1 s2).mp h
    refine ⟨xs, ys, hxs, hys, ?_, editDistance_zero_iff, editDistance_le_max_length xs ys,
      editDistance_length_bound xs ys, editDistance_symm xs ys,
      fun zs => editDistance_triangle xs ys zs⟩
    simp [editDistanceOpt, hxs, hys]

end PostCondition

section PBT

/-! ## Property-based tests

Randomised tests use `Plausible.Testable.check` (the file fails to compile if a
counterexample is found); bounded tests exhaustively check small inputs with
`native_decide`.  Every executable property stated above is tested here.
-/

def smallLists : List (List Nat) :=
  [[], [0], [1], [2], [0,1], [1,0], [0,0], [1,1], [0,1,2], [2,1,0], [1,1,1], [0,0,1],
   [3], [1,2]]

def smallElems : List Nat := [0, 1, 2]

def smallInputs : List Input :=
  [.str "", .str "a", .str "ab", .str "abc", .lst [], .lst [1], .lst [1,2], .lst [-1,2],
   .num 0, .num 123]

-- PBT for `symm_prop`
#eval Plausible.Testable.check
  (∀ xs ys : List Nat, editDistance xs ys = editDistance ys xs)
-- PBT for `self_prop`
#eval Plausible.Testable.check (∀ xs : List Nat, editDistance xs xs = 0)
-- PBT for `zero_iff_prop`
#eval Plausible.Testable.check
  (∀ xs ys : List Nat, (editDistance xs ys = 0) ↔ (xs = ys))
-- PBT for `pos_iff_prop`
#eval Plausible.Testable.check
  (∀ xs ys : List Nat, (0 < editDistance xs ys) ↔ (xs ≠ ys))
-- PBT for `upper_bound_prop`
#eval Plausible.Testable.check
  (∀ xs ys : List Nat, editDistance xs ys ≤ max xs.length ys.length)
-- PBT for `lower_bound_prop`
#eval Plausible.Testable.check
  (∀ xs ys : List Nat,
    max xs.length ys.length ≤ editDistance xs ys + min xs.length ys.length)
-- PBT for `triangle_prop`
#eval Plausible.Testable.check
  (∀ xs ys zs : List Nat, editDistance xs zs ≤ editDistance xs ys + editDistance ys zs)
-- PBT for `recurrence_prop`
#eval Plausible.Testable.check
  (∀ (us vs : List Nat) (a b : Nat),
    editDistance (us ++ [a]) (vs ++ [b]) =
      if a = b then editDistance us vs
      else 1 + min (editDistance us (vs ++ [b]))
        (min (editDistance (us ++ [a]) vs) (editDistance us vs)))
-- PBT for `suffix_prop`
#eval Plausible.Testable.check
  (∀ xs ys t : List Nat, editDistance (xs ++ t) (ys ++ t) = editDistance xs ys)
-- PBTs for `nil_left_prop` / `nil_right_prop`
#eval Plausible.Testable.check (∀ xs : List Nat, editDistance xs [] = xs.length)
#eval Plausible.Testable.check (∀ xs : List Nat, editDistance [] xs = xs.length)
-- PBT for `singleton_prop`
#eval Plausible.Testable.check
  (∀ a b : Nat, editDistance [a] [b] = if a = b then 0 else 1)
-- PBTs for `insert_prop` / `delete_prop`
#eval Plausible.Testable.check
  (∀ (b : Nat) (xs ys : List Nat), editDistance xs (ys ++ [b]) ≤ editDistance xs ys + 1)
#eval Plausible.Testable.check
  (∀ (b : Nat) (xs ys : List Nat), editDistance xs ys ≤ editDistance xs (ys ++ [b]) + 1)
#eval Plausible.Testable.check
  (∀ (a : Nat) (xs ys : List Nat), editDistance (xs ++ [a]) ys ≤ editDistance xs ys + 1)
#eval Plausible.Testable.check
  (∀ (a : Nat) (xs ys : List Nat), editDistance xs ys ≤ editDistance (xs ++ [a]) ys + 1)
-- PBT for `dp_prop`
#eval Plausible.Testable.check
  (∀ xs ys : List Nat, editDistanceDP xs ys = editDistance xs ys)

-- Bounded PBTs (exhaustive over small inputs)
example : (smallLists.product smallLists).all
    (fun p => editDistance p.1 p.2 == editDistance p.2 p.1) = true := by native_decide
example : smallLists.all (fun xs => editDistance xs xs == 0) = true := by native_decide
example : (smallLists.product smallLists).all
    (fun p => (editDistance p.1 p.2 == 0) == (p.1 == p.2)) = true := by native_decide
example : (smallLists.product smallLists).all
    (fun p => decide (editDistance p.1 p.2 ≤ max p.1.length p.2.length)) = true :=
  by native_decide
example : (smallLists.product smallLists).all
    (fun p => decide (max p.1.length p.2.length ≤
      editDistance p.1 p.2 + min p.1.length p.2.length)) = true := by native_decide
example : ((smallLists.product smallLists).product smallLists).all
    (fun q => decide (editDistance q.1.1 q.1.2 ≤
      editDistance q.1.1 q.2 + editDistance q.2 q.1.2)) = true := by native_decide
example : ((smallLists.product smallLists).product (smallElems.product smallElems)).all
    (fun p => editDistance (p.1.1 ++ [p.2.1]) (p.1.2 ++ [p.2.2]) ==
      (if p.2.1 == p.2.2 then editDistance p.1.1 p.1.2
       else 1 + min (editDistance p.1.1 (p.1.2 ++ [p.2.2]))
              (min (editDistance (p.1.1 ++ [p.2.1]) p.1.2)
                (editDistance p.1.1 p.1.2)))) = true := by native_decide
example : ((smallLists.product smallLists).product smallLists).all
    (fun p => editDistance (p.1.1 ++ p.2) (p.1.2 ++ p.2) ==
      editDistance p.1.1 p.1.2) = true := by native_decide
example : smallLists.all (fun xs => editDistance xs [] == xs.length) = true := by native_decide
example : smallLists.all (fun xs => editDistance [] xs == xs.length) = true := by native_decide
example : (smallElems.product smallElems).all
    (fun p => editDistance [p.1] [p.2] == (if p.1 == p.2 then 0 else 1)) = true :=
  by native_decide
example : ((smallLists.product smallLists).product smallElems).all
    (fun p => decide (editDistance p.1.1 (p.1.2 ++ [p.2]) ≤
      editDistance p.1.1 p.1.2 + 1)) = true := by native_decide
example : ((smallLists.product smallLists).product smallElems).all
    (fun p => decide (editDistance (p.1.1 ++ [p.2]) p.1.2 ≤
      editDistance p.1.1 p.1.2 + 1)) = true := by native_decide
example : (smallLists.product smallLists).all
    (fun p => editDistanceDP p.1 p.2 == editDistance p.1 p.2) = true := by native_decide

/-- Executable counterpart of `Post_prop`. -/
def postCheck (s1 s2 : Input) : Bool :=
  match editDistanceOpt s1 s2, s1.toSeq, s2.toSeq, decide (Pre s1 s2) with
  | some d, some xs, some ys, true =>
      (d == editDistance xs ys) &&
      ((d == 0) == (xs == ys)) &&
      decide (d ≤ max xs.length ys.length) &&
      decide (max xs.length ys.length ≤ d + min xs.length ys.length) &&
      (d == editDistance ys xs)
  | none, _, _, false => true
  | _, _, _, _ => false

-- PBT for `Post_prop`
example : (smallInputs.product smallInputs).all
    (fun p => postCheck p.1 p.2) = true := by native_decide
-- PBT for `error_prop`
example : (smallInputs.product smallInputs).all
    (fun p => (editDistanceOpt p.1 p.2 == none) == !decide (Pre p.1 p.2)) = true :=
  by native_decide
-- PBT for `defined_prop`
example : (smallInputs.product smallInputs).all
    (fun p => decide (Pre p.1 p.2) == (editDistanceOpt p.1 p.2).isSome) = true :=
  by native_decide
-- PBT for `value_prop`
example : (smallInputs.product smallInputs).all
    (fun p => match p.1.toSeq, p.2.toSeq, editDistanceOpt p.1 p.2 with
      | some xs, some ys, some d => d == editDistance xs ys
      | none, _, none => true
      | _, none, none => true
      | _, _, _ => false) = true := by native_decide

end PBT

section Correctness

/-! ## Correctness: `Pre -> Post` -/

theorem correctness_thm (s1 s2 : Input) :
    Pre s1 s2 → Post_prop s1 s2 (editDistanceOpt s1 s2) := fun _ => Post_thm s1 s2

theorem correctness_unconditional (s1 s2 : Input) :
    Post_prop s1 s2 (editDistanceOpt s1 s2) := Post_thm s1 s2

end Correctness

section Imperative

variable {α : Type*} [DecidableEq α]

/-! ## Imperative implementation (`Id.run do` with mutable state) -/

/-- Python's `edit_distance` transcribed imperatively: a mutable DP row (`dp[i]` of the
Python table) updated by one sweep per element of the first sequence. -/
def editDistanceImp (xs ys : List α) : Nat := Id.run do
  -- dp[0][j] = j  (insertions)
  let mut row : List Nat := List.range (ys.length + 1)
  for a in xs do
    -- dp[i][0] = i (deletions) and the inner sweep over j
    row := rowStep a ys row
  return row.getD ys.length 0

theorem impLoop_eq (ys : List α) :
    ∀ (xs : List α) (init : List Nat),
      (Id.run do
        let mut row := init
        for a in xs do
          row := rowStep a ys row
        return row) = xs.foldl (fun r a => rowStep a ys r) init := by
  intro xs
  induction xs with
  | nil => intro init; rfl
  | cons a as ih => intro init; simp [ih]

theorem editDistanceImp_eq_dp (xs ys : List α) :
    editDistanceImp xs ys = editDistanceDP xs ys := by
  simp only [editDistanceImp, editDistanceDP, dpFinalRow]
  rw [impLoop_eq ys xs (List.range (ys.length + 1))]

/-- Equivalence of the imperative and the functional implementation. -/
theorem editDistanceImp_eq (xs ys : List α) :
    editDistanceImp xs ys = editDistance xs ys := by
  rw [editDistanceImp_eq_dp, editDistanceDP_eq]

def equivalence_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α),
    @editDistanceImp α _ xs ys = @editDistance xs ys
theorem equivalence_thm : equivalence_prop :=
  fun α _ xs ys => @editDistanceImp_eq α _ xs ys

def equivalenceDP_prop : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α),
    @editDistanceDP α _ xs ys = @editDistance xs ys
theorem equivalenceDP_thm : equivalenceDP_prop :=
  fun α _ xs ys => @editDistanceDP_eq α _ xs ys

/-- The imperative version of the whole Python function (`none` = `ValueError`). -/
def editDistanceOptImp (s1 s2 : Input) : Option Nat :=
  match s1.toSeq, s2.toSeq with
  | some xs, some ys => some (editDistanceImp xs ys)
  | _, _ => none

theorem editDistanceOptImp_eq (s1 s2 : Input) :
    editDistanceOptImp s1 s2 = editDistanceOpt s1 s2 := by
  cases s1 <;> cases s2 <;>
    simp [editDistanceOptImp, editDistanceOpt, Input.toSeq, editDistanceImp_eq]

theorem editDistanceOptImp_Post (s1 s2 : Input) :
    Post_prop s1 s2 (editDistanceOptImp s1 s2) := by
  rw [editDistanceOptImp_eq]
  exact Post_thm s1 s2

end Imperative

section ImperativeTests

variable {α : Type*} [DecidableEq α]

example : editDistanceImp "hello".toList "hello".toList = 0 := by native_decide
example : editDistanceImp "cat".toList "bat".toList = 1 := by native_decide
example : editDistanceImp "cat".toList "cats".toList = 1 := by native_decide
example : editDistanceImp "cats".toList "cat".toList = 1 := by native_decide
example : editDistanceImp "cat".toList "dog".toList = 3 := by native_decide
example : editDistanceImp "kitten".toList "sitting".toList = 3 := by native_decide
example : editDistanceImp "".toList "".toList = 0 := by native_decide
example : editDistanceImp "".toList "abc".toList = 3 := by native_decide
example : editDistanceImp "ab".toList "".toList = 2 := by native_decide
example : editDistanceImp "a".toList "b".toList = 1 := by native_decide
example : editDistanceImp "intention".toList "execution".toList = 5 := by native_decide
example : editDistanceImp "saturday".toList "sunday".toList = 3 := by native_decide
example : editDistanceImp "abc".toList "def".toList = 3 := by native_decide
example : editDistanceImp "aaa".toList "aa".toList = 1 := by native_decide
example : editDistanceImp "aaaa".toList "bbbb".toList = 4 := by native_decide
example : editDistanceImp ([1,2,3] : List Nat) ([1,2,3] : List Nat) = 0 := by native_decide
example : editDistanceImp ([1,2,3] : List Nat) ([1,4,3] : List Nat) = 1 := by native_decide
example : editDistanceImp ([1,2,3,4] : List Nat) ([1,3,4] : List Nat) = 1 := by native_decide
example : editDistanceImp ([1,2,3] : List Nat) ([4,5,6] : List Nat) = 3 := by native_decide
example : editDistanceImp ([1,2,3,4,5] : List Nat) ([6,7,8] : List Nat) = 5 := by native_decide
example : editDistanceImp ([1,2,-3] : List Int) ([1,4,-3] : List Int) = 1 := by native_decide
example : editDistanceImp (['c','a','t'] : List Char) (['b','a','t'] : List Char) = 1 :=
  by native_decide
example : editDistanceOptImp (.str "kitten") (.str "sitting") = some 3 := by native_decide
example : editDistanceOptImp (.lst [1,2,3]) (.lst [1,4,3]) = some 1 := by native_decide
example : editDistanceOptImp (.num 123) (.str "abc") = none := rfl

#eval editDistanceImp "kitten".toList "sitting".toList
#eval editDistanceImp "intention".toList "execution".toList
#eval editDistanceImp ([1,2,3,4,5] : List Nat) ([6,7,8] : List Nat)
#eval editDistanceOptImp (.lst [-1,2,-3]) (.lst [-1,4,-3])
#eval editDistanceOptImp (.num 123) (.str "abc")

-- PBT for the equivalence theorem
#eval Plausible.Testable.check
  (∀ xs ys : List Nat, editDistanceImp xs ys = editDistance xs ys)
example : (smallLists.product smallLists).all
    (fun p => editDistanceImp p.1 p.2 == editDistance p.1 p.2) = true := by native_decide
example : (smallLists.product smallLists).all
    (fun p => editDistanceImp p.1 p.2 == editDistanceDP p.1 p.2) = true := by native_decide
example : (smallInputs.product smallInputs).all
    (fun p => editDistanceOptImp p.1 p.2 == editDistanceOpt p.1 p.2) = true := by native_decide
example : (smallInputs.product smallInputs).all
    (fun p => postCheck p.1 p.2) = true := by native_decide

end ImperativeTests

section PythonTestSuite

/-! ## The Python `check` test-suite, as a single Boolean -/

def check : Bool :=
  (strDist "hello" "hello" == 0) &&
  (strDist "cat" "bat" == 1) &&
  (strDist "cat" "cats" == 1) &&
  (strDist "cats" "cat" == 1) &&
  (strDist "cat" "dog" == 3) &&
  (strDist "kitten" "sitting" == 3) &&
  (strDist "" "" == 0) &&
  (strDist "" "abc" == 3) &&
  (strDist "ab" "" == 2) &&
  (strDist "a" "b" == 1) &&
  (editDistance ([1,2,3] : List Int) ([1,2,3] : List Int) == 0) &&
  (editDistance ([1,2,3] : List Int) ([1,4,3] : List Int) == 1) &&
  (editDistance ([1,2,3,4] : List Int) ([1,3,4] : List Int) == 1) &&
  (editDistance ([1,2,3] : List Int) ([4,5,6] : List Int) == 3) &&
  (editDistance ([1,2,3,4,5] : List Int) ([6,7,8] : List Int) == 5) &&
  (editDistance (['h','e','l','l','o'] : List Char)
    (['h','e','l','l','o'] : List Char) == 0) &&
  (editDistance (['c','a','t'] : List Char) (['b','a','t'] : List Char) == 1) &&
  (editDistance (['c','a','t'] : List Char) (['c','a','t','s'] : List Char) == 1) &&
  (editDistance (['c','a','t','s'] : List Char) (['c','a','t'] : List Char) == 1) &&
  (strDist "intention" "execution" == 5) &&
  (strDist "saturday" "sunday" == 3) &&
  (strDist "abc" "def" == 3) &&
  (strDist "xyz" "abc" == 3) &&
  (strDist "a" "a" == 0) &&
  (strDist "a" "" == 1) &&
  (strDist "" "a" == 1) &&
  (strDist "aaa" "aa" == 1) &&
  (strDist "aa" "aaa" == 1) &&
  (strDist "aaaa" "bbbb" == 4) &&
  (editDistanceOpt (.num 123) (.str "abc") == none)

example : check = true := by native_decide
#eval check

/-- The same suite run against the imperative implementation. -/
def checkImp : Bool :=
  (editDistanceImp "hello".toList "hello".toList == 0) &&
  (editDistanceImp "cat".toList "bat".toList == 1) &&
  (editDistanceImp "cat".toList "cats".toList == 1) &&
  (editDistanceImp "cats".toList "cat".toList == 1) &&
  (editDistanceImp "cat".toList "dog".toList == 3) &&
  (editDistanceImp "kitten".toList "sitting".toList == 3) &&
  (editDistanceImp "".toList "".toList == 0) &&
  (editDistanceImp "".toList "abc".toList == 3) &&
  (editDistanceImp "ab".toList "".toList == 2) &&
  (editDistanceImp "a".toList "b".toList == 1) &&
  (editDistanceImp ([1,2,3] : List Int) ([1,2,3] : List Int) == 0) &&
  (editDistanceImp ([1,2,3] : List Int) ([1,4,3] : List Int) == 1) &&
  (editDistanceImp ([1,2,3,4] : List Int) ([1,3,4] : List Int) == 1) &&
  (editDistanceImp ([1,2,3] : List Int) ([4,5,6] : List Int) == 3) &&
  (editDistanceImp ([1,2,3,4,5] : List Int) ([6,7,8] : List Int) == 5) &&
  (editDistanceImp "intention".toList "execution".toList == 5) &&
  (editDistanceImp "saturday".toList "sunday".toList == 3) &&
  (editDistanceImp "abc".toList "def".toList == 3) &&
  (editDistanceImp "xyz".toList "abc".toList == 3) &&
  (editDistanceImp "a".toList "a".toList == 0) &&
  (editDistanceImp "a".toList "".toList == 1) &&
  (editDistanceImp "".toList "a".toList == 1) &&
  (editDistanceImp "aaa".toList "aa".toList == 1) &&
  (editDistanceImp "aa".toList "aaa".toList == 1) &&
  (editDistanceImp "aaaa".toList "bbbb".toList == 4) &&
  (editDistanceOptImp (.num 123) (.str "abc") == none)

example : checkImp = true := by native_decide
#eval checkImp

end PythonTestSuite

end edit_distance
