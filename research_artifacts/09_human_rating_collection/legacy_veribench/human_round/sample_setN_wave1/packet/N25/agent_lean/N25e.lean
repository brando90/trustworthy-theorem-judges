import Mathlib
import Plausible

/-!
# Heap sort

Lean 4 formalization of a Python heap sort on lists of integers.

The algorithm builds a max-heap by sifting down from the last non-leaf
(`n / 2 - 1` down to `0`), then repeatedly swaps the root with the end of the
unsorted prefix and sifts that prefix down. Comparisons use strict `>`, so
equal elements are not reordered by a sift; the result is still the unique
non-decreasing rearrangement of the input multiset.

Edge cases match the Python program: an empty or singleton list is returned
unchanged (Python returns a copy). Inputs that are not lists of integers are
outside the type `List Int`; in Python those inputs fail `pre` and raise
`ValueError`.
-/

namespace heap_sort


def swap (a : List Int) (i j : Nat) : List Int :=
  if hi : i < a.length then
    if hj : j < a.length then
      (a.set i (a[j])).set j (a[i])
    else a
  else a

theorem swap_length (a : List Int) (i j : Nat) : (swap a i j).length = a.length := by
  unfold swap
  split
  · split
    · simp [List.length_set]
    · rfl
  · rfl

theorem swap_getElem!_left (a : List Int) (i j : Nat)
    (hi : i < a.length) (hj : j < a.length) :
    (swap a i j)[i]! = a[j]! := by
  unfold swap
  rw [dif_pos hi, dif_pos hj]
  grind

theorem swap_getElem!_right (a : List Int) (i j : Nat)
    (hi : i < a.length) (hj : j < a.length) :
    (swap a i j)[j]! = a[i]! := by
  unfold swap
  rw [dif_pos hi, dif_pos hj]
  grind

theorem swap_getElem!_of_ne (a : List Int) (i j k : Nat)
    (hi : i < a.length) (hj : j < a.length) (hki : k ≠ i) (hkj : k ≠ j) :
    (swap a i j)[k]! = a[k]! := by
  unfold swap
  rw [dif_pos hi, dif_pos hj]
  grind

def heapify (a : List Int) (n i : Nat) : List Int :=
  if hi : i < n ∧ n ≤ a.length then
    if hL : 2 * i + 1 < n ∧ a[2 * i + 1]! > a[i]! then
      if hR : 2 * i + 2 < n ∧ a[2 * i + 2]! > a[2 * i + 1]! then
        heapify (swap a i (2 * i + 2)) n (2 * i + 2)
      else
        heapify (swap a i (2 * i + 1)) n (2 * i + 1)
    else if hR : 2 * i + 2 < n ∧ a[2 * i + 2]! > a[i]! then
      heapify (swap a i (2 * i + 2)) n (2 * i + 2)
    else
      a
  else
    a
termination_by n - i
decreasing_by all_goals (simp_wf; omega)

theorem heapify_length (n : Nat) (a : List Int) (i : Nat) :
    (heapify a n i).length = a.length := by
  induction a, i using heapify.induct n with
  | case1 a i hi hL hR ih =>
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_pos hR, ih, swap_length]
  | case2 a i hi hL hR ih =>
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_neg hR, ih, swap_length]
  | case3 a i hi hL hR ih =>
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_pos hR, ih, swap_length]
  | case4 a i hi hL hR =>
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_neg hR]
  | case5 a i hi =>
    unfold heapify
    rw [dif_neg hi]

theorem swap_perm (a : List Int) (i j : Nat) : List.Perm (swap a i j) a := by
  unfold swap
  split
  · rename_i hi
    split
    · rename_i hj
      simpa using List.set_set_perm hi hj
    · exact List.Perm.rfl
  · exact List.Perm.rfl

theorem heapify_perm (n : Nat) (a : List Int) (i : Nat) : List.Perm (heapify a n i) a := by
  induction a, i using heapify.induct n with
  | case1 a i hi hL hR ih =>
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_pos hR]
    exact List.Perm.trans ih (swap_perm _ _ _)
  | case2 a i hi hL hR ih =>
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_neg hR]
    exact List.Perm.trans ih (swap_perm _ _ _)
  | case3 a i hi hL hR ih =>
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_pos hR]
    exact List.Perm.trans ih (swap_perm _ _ _)
  | case4 a i hi hL hR =>
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_neg hR]
  | case5 a i hi =>
    unfold heapify
    rw [dif_neg hi]




def inSubtree (root idx : Nat) : Bool :=
  if idx < root then
    false
  else if idx = root then
    true
  else
    inSubtree root ((idx - 1) / 2)
termination_by idx
decreasing_by
  simp_wf
  omega

theorem inSubtree_of_lt (root idx : Nat) (h : idx < root) : inSubtree root idx = false := by
  conv_lhs => unfold inSubtree
  simp [h]

theorem inSubtree_self (i : Nat) : inSubtree i i = true := by
  conv_lhs => unfold inSubtree
  simp

theorem inSubtree_step (root idx : Nat) (h : root < idx) :
    inSubtree root idx = inSubtree root ((idx - 1) / 2) := by
  conv_lhs => unfold inSubtree
  have h1 : ¬ idx < root := by omega
  have h2 : ¬ idx = root := by omega
  simp only [h1, h2, ite_false]

theorem inSubtree_le (root idx : Nat) (h : inSubtree root idx = true) : root ≤ idx := by
  induction idx using Nat.strongRecOn with
  | ind idx ih =>
    by_cases hlt : idx < root
    · simp [inSubtree_of_lt _ _ hlt] at h
    · by_cases heq : idx = root
      · omega
      · have hgt : root < idx := by omega
        rw [inSubtree_step root idx hgt] at h
        have hp : (idx - 1) / 2 < idx := by omega
        have := ih ((idx - 1) / 2) hp h
        omega

theorem inSubtree_left (i : Nat) : inSubtree i (2 * i + 1) = true := by
  have h : i < 2 * i + 1 := by omega
  rw [inSubtree_step i (2 * i + 1) h]
  have heq : (2 * i + 1 - 1) / 2 = i := by omega
  rw [heq, inSubtree_self]

theorem inSubtree_right (i : Nat) : inSubtree i (2 * i + 2) = true := by
  have h : i < 2 * i + 2 := by omega
  rw [inSubtree_step i (2 * i + 2) h]
  have heq : (2 * i + 2 - 1) / 2 = i := by omega
  rw [heq, inSubtree_self]

theorem inSubtree_of_inSubtree_left (i k : Nat) (h : inSubtree (2 * i + 1) k = true) :
    inSubtree i k = true := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k = 2 * i + 1
    · subst hk
      exact inSubtree_left i
    · have hle : 2 * i + 1 ≤ k := inSubtree_le _ _ h
      have hgt : 2 * i + 1 < k := by omega
      rw [inSubtree_step _ _ hgt] at h
      have hp : (k - 1) / 2 < k := by omega
      have hparent : inSubtree i ((k - 1) / 2) = true := ih _ hp h
      have hki : i < k := by omega
      rw [inSubtree_step i k hki]
      exact hparent

theorem inSubtree_of_inSubtree_right (i k : Nat) (h : inSubtree (2 * i + 2) k = true) :
    inSubtree i k = true := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k = 2 * i + 2
    · subst hk
      exact inSubtree_right i
    · have hle : 2 * i + 2 ≤ k := inSubtree_le _ _ h
      have hgt : 2 * i + 2 < k := by omega
      rw [inSubtree_step _ _ hgt] at h
      have hp : (k - 1) / 2 < k := by omega
      have hparent : inSubtree i ((k - 1) / 2) = true := ih _ hp h
      have hki : i < k := by omega
      rw [inSubtree_step i k hki]
      exact hparent

theorem not_inSubtree_child_left (root j : Nat) (h : inSubtree root j = false)
    (hne : 2 * j + 1 ≠ root) : inSubtree root (2 * j + 1) = false := by
  by_cases hlt : 2 * j + 1 < root
  · exact inSubtree_of_lt _ _ hlt
  · have hgt : root < 2 * j + 1 := by omega
    rw [inSubtree_step _ _ hgt]
    have hparent : (2 * j + 1 - 1) / 2 = j := by omega
    rw [hparent]
    exact h

theorem inSubtree_zero (k : Nat) : inSubtree 0 k = true := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k = 0
    · simp [hk, inSubtree_self]
    · have hgt : 0 < k := by omega
      rw [inSubtree_step 0 k hgt]
      exact ih _ (by omega)


theorem not_inSubtree_child_right (root j : Nat) (h : inSubtree root j = false)
    (hne : 2 * j + 2 ≠ root) : inSubtree root (2 * j + 2) = false := by
  by_cases hlt : 2 * j + 2 < root
  · exact inSubtree_of_lt _ _ hlt
  · have hgt : root < 2 * j + 2 := by omega
    rw [inSubtree_step _ _ hgt]
    have hparent : (2 * j + 2 - 1) / 2 = j := by omega
    rw [hparent]
    exact h

theorem heapify_get_outside (n : Nat) (a : List Int) (i k : Nat)
    (hsub : inSubtree i k = false) (hk : k < a.length) :
    (heapify a n i)[k]! = a[k]! := by
  induction a, i using heapify.induct n with
  | case1 a i hi hL hR ih =>
    have hnot : inSubtree (2 * i + 2) k = false := by
      by_cases h : inSubtree (2 * i + 2) k = true
      · exact absurd (inSubtree_of_inSubtree_right i k h) (by simpa using hsub)
      · simpa using h
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_pos hR]
    have hk' : k < (swap a i (2 * i + 2)).length := by rw [swap_length]; exact hk
    rw [ih hnot hk']
    have hki : k ≠ i := by
      intro heq; subst heq; simp [inSubtree_self] at hsub
    have hkr : k ≠ 2 * i + 2 := by
      intro heq; subst heq; simp [inSubtree_right i] at hsub
    have hi' : i < a.length := by omega
    have hr' : 2 * i + 2 < a.length := by omega
    exact swap_getElem!_of_ne a i (2 * i + 2) k hi' hr' hki hkr
  | case2 a i hi hL hR ih =>
    have hnot : inSubtree (2 * i + 1) k = false := by
      by_cases h : inSubtree (2 * i + 1) k = true
      · exact absurd (inSubtree_of_inSubtree_left i k h) (by simpa using hsub)
      · simpa using h
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_neg hR]
    have hk' : k < (swap a i (2 * i + 1)).length := by rw [swap_length]; exact hk
    rw [ih hnot hk']
    have hki : k ≠ i := by
      intro heq; subst heq; simp [inSubtree_self] at hsub
    have hkl : k ≠ 2 * i + 1 := by
      intro heq; subst heq; simp [inSubtree_left i] at hsub
    have hi' : i < a.length := by omega
    have hl' : 2 * i + 1 < a.length := by omega
    exact swap_getElem!_of_ne a i (2 * i + 1) k hi' hl' hki hkl
  | case3 a i hi hL hR ih =>
    have hnot : inSubtree (2 * i + 2) k = false := by
      by_cases h : inSubtree (2 * i + 2) k = true
      · exact absurd (inSubtree_of_inSubtree_right i k h) (by simpa using hsub)
      · simpa using h
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_pos hR]
    have hk' : k < (swap a i (2 * i + 2)).length := by rw [swap_length]; exact hk
    rw [ih hnot hk']
    have hki : k ≠ i := by
      intro heq; subst heq; simp [inSubtree_self] at hsub
    have hkr : k ≠ 2 * i + 2 := by
      intro heq; subst heq; simp [inSubtree_right i] at hsub
    have hi' : i < a.length := by omega
    have hr' : 2 * i + 2 < a.length := by omega
    exact swap_getElem!_of_ne a i (2 * i + 2) k hi' hr' hki hkr
  | case4 a i hi hL hR =>
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_neg hR]
  | case5 a i hi =>
    unfold heapify
    rw [dif_neg hi]

theorem heapify_get_ge (n : Nat) (a : List Int) (i : Nat) :
    ∀ k, n ≤ k → k < a.length → (heapify a n i)[k]! = a[k]! := by
  induction a, i using heapify.induct n with
  | case1 a i hi hL hR ih =>
    intro k hk hkL
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_pos hR]
    have hk' : k < (swap a i (2 * i + 2)).length := by rw [swap_length]; exact hkL
    rw [ih k hk hk']
    have hki : k ≠ i := by omega
    have hkr : k ≠ 2 * i + 2 := by omega
    have hi' : i < a.length := by omega
    have hr' : 2 * i + 2 < a.length := by omega
    exact swap_getElem!_of_ne a i (2 * i + 2) k hi' hr' hki hkr
  | case2 a i hi hL hR ih =>
    intro k hk hkL
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_neg hR]
    have hk' : k < (swap a i (2 * i + 1)).length := by rw [swap_length]; exact hkL
    rw [ih k hk hk']
    have hki : k ≠ i := by omega
    have hkl : k ≠ 2 * i + 1 := by omega
    have hi' : i < a.length := by omega
    have hl' : 2 * i + 1 < a.length := by omega
    exact swap_getElem!_of_ne a i (2 * i + 1) k hi' hl' hki hkl
  | case3 a i hi hL hR ih =>
    intro k hk hkL
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_pos hR]
    have hk' : k < (swap a i (2 * i + 2)).length := by rw [swap_length]; exact hkL
    rw [ih k hk hk']
    have hki : k ≠ i := by omega
    have hkr : k ≠ 2 * i + 2 := by omega
    have hi' : i < a.length := by omega
    have hr' : 2 * i + 2 < a.length := by omega
    exact swap_getElem!_of_ne a i (2 * i + 2) k hi' hr' hki hkr
  | case4 a i hi hL hR =>
    intro k hk hkL
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_neg hR]
  | case5 a i hi =>
    intro k hk hkL
    unfold heapify
    rw [dif_neg hi]

def HeapFrom (a : List Int) (n start : Nat) : Prop :=
  ∀ j, start ≤ j →
    (2 * j + 1 < n → a[j]! ≥ a[2 * j + 1]!) ∧
    (2 * j + 2 < n → a[j]! ≥ a[2 * j + 2]!)

theorem heapFrom_mono (a : List Int) (n s t : Nat) (hst : s ≤ t) (h : HeapFrom a n s) :
    HeapFrom a n t := by
  intro j hj
  exact h j (Nat.le_trans hst hj)

theorem heapFrom_congr (a b : List Int) (n start : Nat) (h : HeapFrom a n start)
    (heq : ∀ j, start ≤ j → j < n → a[j]! = b[j]!) :
    HeapFrom b n start := by
  intro j hj
  constructor
  · intro hc
    have hjn : j < n := by omega
    rw [← heq j hj hjn, ← heq (2 * j + 1) (by omega) hc]
    exact (h j hj).1 hc
  · intro hc
    have hjn : j < n := by omega
    rw [← heq j hj hjn, ← heq (2 * j + 2) (by omega) hc]
    exact (h j hj).2 hc

theorem heap_subtree_ge (a : List Int) (n root k : Nat)
    (hH : HeapFrom a n root) (hsub : inSubtree root k = true)
    (hk : k < n) (_hn : n ≤ a.length) :
    a[root]! ≥ a[k]! := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases heq : k = root
    · subst heq
      exact le_refl _
    · have hgt : root < k := by
        have hle := inSubtree_le root k hsub
        omega
      have hparent_sub : inSubtree root ((k - 1) / 2) = true := by
        rw [inSubtree_step root k hgt] at hsub
        exact hsub
      have ihp := ih ((k - 1) / 2) (by omega) hparent_sub (by omega)
      have hp_ge : root ≤ (k - 1) / 2 := inSubtree_le _ _ hparent_sub
      have hchild : k = 2 * ((k - 1) / 2) + 1 ∨ k = 2 * ((k - 1) / 2) + 2 := by omega
      rcases hchild with hk1 | hk2
      · have hc : 2 * ((k - 1) / 2) + 1 < n := by rw [← hk1]; exact hk
        have hge := (hH _ hp_ge).1 hc
        have hge' : a[k]! ≤ a[(k - 1) / 2]! := by
          conv_lhs => rw [hk1]
          exact hge
        exact le_trans hge' ihp
      · have hc : 2 * ((k - 1) / 2) + 2 < n := by rw [← hk2]; exact hk
        have hge := (hH _ hp_ge).2 hc
        have hge' : a[k]! ≤ a[(k - 1) / 2]! := by
          conv_lhs => rw [hk2]
          exact hge
        exact le_trans hge' ihp


theorem heapify_subtree_le (n : Nat) (a : List Int) (idx : Nat) :
    n ≤ a.length →
    ∀ M : Int, (∀ k, inSubtree idx k = true → k < n → a[k]! ≤ M) →
      ∀ k, inSubtree idx k = true → k < n → (heapify a n idx)[k]! ≤ M := by
  induction a, idx using heapify.induct n with
  | case1 a i hi hL hR ih =>
    intro hn M hbound k hk hkn
    let right := 2 * i + 2
    let b := swap a i right
    have hi_len : i < a.length := by omega
    have hr_len : right < a.length := by omega
    have hn_b : n ≤ b.length := by simpa [b, right, swap_length] using hn
    have hB : ∀ t, inSubtree right t = true → t < n → b[t]! ≤ M := by
      intro t ht htn
      by_cases htr : t = right
      · subst htr
        rw [swap_getElem!_right a i right hi_len hr_len]
        exact hbound i (inSubtree_self i) hi.1
      · have ht_ne_i : t ≠ i := by
          intro heq
          rw [heq] at ht
          simp [inSubtree_of_lt right i (by omega : i < right)] at ht
        rw [swap_getElem!_of_ne a i right t hi_len hr_len ht_ne_i htr]
        exact hbound t (inSubtree_of_inSubtree_right i t ht) htn
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_pos hR]
    cases hsubr : inSubtree right k with
    | false =>
      have hkL : k < a.length := by omega
      have hkB : k < b.length := by simpa [b, swap_length] using hkL
      rw [heapify_get_outside n b right k hsubr hkB]
      by_cases hki : k = i
      · rw [hki]
        rw [swap_getElem!_left a i right hi_len hr_len]
        exact hbound right (inSubtree_right i) hR.1
      · have hkr : k ≠ right := by
          intro heq
          rw [heq] at hsubr
          simp [inSubtree_self] at hsubr
        rw [swap_getElem!_of_ne a i right k hi_len hr_len hki hkr]
        exact hbound k hk hkn
    | true =>
      exact ih hn_b M hB k hsubr hkn
  | case2 a i hi hL hR ih =>
    intro hn M hbound k hk hkn
    let left := 2 * i + 1
    let b := swap a i left
    have hi_len : i < a.length := by omega
    have hl_len : left < a.length := by omega
    have hn_b : n ≤ b.length := by simpa [b, left, swap_length] using hn
    have hB : ∀ t, inSubtree left t = true → t < n → b[t]! ≤ M := by
      intro t ht htn
      by_cases htl : t = left
      · subst htl
        rw [swap_getElem!_right a i left hi_len hl_len]
        exact hbound i (inSubtree_self i) hi.1
      · have ht_ne_i : t ≠ i := by
          intro heq
          rw [heq] at ht
          simp [inSubtree_of_lt left i (by omega : i < left)] at ht
        rw [swap_getElem!_of_ne a i left t hi_len hl_len ht_ne_i htl]
        exact hbound t (inSubtree_of_inSubtree_left i t ht) htn
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_neg hR]
    cases hsubl : inSubtree left k with
    | false =>
      have hkL : k < a.length := by omega
      have hkB : k < b.length := by simpa [b, swap_length] using hkL
      rw [heapify_get_outside n b left k hsubl hkB]
      by_cases hki : k = i
      · rw [hki]
        rw [swap_getElem!_left a i left hi_len hl_len]
        exact hbound left (inSubtree_left i) hL.1
      · have hkl : k ≠ left := by
          intro heq
          rw [heq] at hsubl
          simp [inSubtree_self] at hsubl
        rw [swap_getElem!_of_ne a i left k hi_len hl_len hki hkl]
        exact hbound k hk hkn
    | true =>
      exact ih hn_b M hB k hsubl hkn
  | case3 a i hi hL hR ih =>
    intro hn M hbound k hk hkn
    let right := 2 * i + 2
    let b := swap a i right
    have hi_len : i < a.length := by omega
    have hr_len : right < a.length := by omega
    have hn_b : n ≤ b.length := by simpa [b, right, swap_length] using hn
    have hB : ∀ t, inSubtree right t = true → t < n → b[t]! ≤ M := by
      intro t ht htn
      by_cases htr : t = right
      · subst htr
        rw [swap_getElem!_right a i right hi_len hr_len]
        exact hbound i (inSubtree_self i) hi.1
      · have ht_ne_i : t ≠ i := by
          intro heq
          rw [heq] at ht
          simp [inSubtree_of_lt right i (by omega : i < right)] at ht
        rw [swap_getElem!_of_ne a i right t hi_len hr_len ht_ne_i htr]
        exact hbound t (inSubtree_of_inSubtree_right i t ht) htn
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_pos hR]
    cases hsubr : inSubtree right k with
    | false =>
      have hkL : k < a.length := by omega
      have hkB : k < b.length := by simpa [b, swap_length] using hkL
      rw [heapify_get_outside n b right k hsubr hkB]
      by_cases hki : k = i
      · rw [hki]
        rw [swap_getElem!_left a i right hi_len hr_len]
        exact hbound right (inSubtree_right i) hR.1
      · have hkr : k ≠ right := by
          intro heq
          rw [heq] at hsubr
          simp [inSubtree_self] at hsubr
        rw [swap_getElem!_of_ne a i right k hi_len hr_len hki hkr]
        exact hbound k hk hkn
    | true =>
      exact ih hn_b M hB k hsubr hkn
  | case4 a i hi hL hR =>
    intro hn M hbound k hk hkn
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_neg hR]
    exact hbound k hk hkn
  | case5 a i hi =>
    intro hn M hbound k hk hkn
    have hik : i ≤ k := inSubtree_le i k hk
    exact (hi ⟨by omega, hn⟩).elim

theorem heapify_restores (n : Nat) (a : List Int) (idx : Nat) :
    n ≤ a.length → idx < n → HeapFrom a n (idx + 1) →
      HeapFrom (heapify a n idx) n idx := by
  induction a, idx using heapify.induct n with
  | case1 a i hi hL hR ih =>
    intro hn hi_n hFrom
    let right := 2 * i + 2
    let left := 2 * i + 1
    let b := swap a i right
    have hi_len : i < a.length := by omega
    have hr_len : right < a.length := by omega
    have hl_len : left < a.length := by omega
    have hn_b : n ≤ b.length := by simpa [b, swap_length] using hn
    have hFrom_b : HeapFrom b n (right + 1) := by
      refine heapFrom_congr a b n (right + 1)
        (heapFrom_mono a n (i + 1) (right + 1) (by omega) hFrom) ?_
      intro j hj hjn
      have hji : j ≠ i := by omega
      have hjr : j ≠ right := by omega
      exact (swap_getElem!_of_ne a i right j hi_len hr_len hji hjr).symm
    have hRest := ih hn_b hR.1 hFrom_b
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_pos hR]
    intro j hj
    by_cases hjr : right ≤ j
    · exact hRest j hjr
    · have hj_lt : j < right := by omega
      have hnotj : inSubtree right j = false := inSubtree_of_lt right j hj_lt
      have hjL : j < a.length := by omega
      have hjB : j < b.length := by simpa [b, swap_length] using hjL
      have hcj : (heapify b n right)[j]! = b[j]! :=
        heapify_get_outside n b right j hnotj hjB
      by_cases hji : j = i
      · rw [hji] at hcj hj ⊢
        constructor
        · intro hc
          have hnotL : inSubtree right left = false := inSubtree_of_lt right left (by omega)
          have hlB : left < b.length := by simpa [b, swap_length] using hl_len
          have hcl : (heapify b n right)[left]! = b[left]! :=
            heapify_get_outside n b right left hnotL hlB
          have hbl : b[left]! = a[left]! :=
            swap_getElem!_of_ne a i right left hi_len hr_len (by omega) (by omega)
          have hbi : b[i]! = a[right]! := swap_getElem!_left a i right hi_len hr_len
          rw [hcj, hcl, hbi, hbl]
          exact le_of_lt hR.2
        · intro hc
          have hbi : b[i]! = a[right]! := swap_getElem!_left a i right hi_len hr_len
          have hroot_le : (heapify b n right)[right]! ≤ a[right]! := by
            refine heapify_subtree_le n b right hn_b (a[right]!) ?_ right (inSubtree_self right) hc
            intro t ht htn
            by_cases htr : t = right
            · rw [htr, swap_getElem!_right a i right hi_len hr_len]
              exact le_of_lt (lt_trans hL.2 hR.2)
            · have ht_ne_i : t ≠ i := by
                intro heq
                rw [heq] at ht
                simp [inSubtree_of_lt right i (by omega : i < right)] at ht
              rw [swap_getElem!_of_ne a i right t hi_len hr_len ht_ne_i htr]
              have htn' : t < n := htn
              have hsub_a : inSubtree right t = true := ht
              have hHeapR : HeapFrom a n right :=
                heapFrom_mono a n (i + 1) right (by omega) hFrom
              exact heap_subtree_ge a n right t hHeapR hsub_a htn' hn
          rw [hcj, hbi]
          exact hroot_le
      · have hji' : i < j := by omega
        have hj_ne_i : j ≠ i := hji
        have hj_ne_r : j ≠ right := by omega
        have hbj : b[j]! = a[j]! :=
          swap_getElem!_of_ne a i right j hi_len hr_len hj_ne_i hj_ne_r
        constructor
        · intro hc
          have hne1 : 2 * j + 1 ≠ right := by omega
          have hnotc : inSubtree right (2 * j + 1) = false :=
            not_inSubtree_child_left right j hnotj hne1
          have hcL : 2 * j + 1 < a.length := by omega
          have hcB : 2 * j + 1 < b.length := by simpa [b, swap_length] using hcL
          have hcc : (heapify b n right)[2 * j + 1]! = b[2 * j + 1]! :=
            heapify_get_outside n b right (2 * j + 1) hnotc hcB
          have hbc : b[2 * j + 1]! = a[2 * j + 1]! := by
            apply swap_getElem!_of_ne a i right (2 * j + 1) hi_len hr_len
            · omega
            · omega
          rw [hcj, hcc, hbj, hbc]
          exact (hFrom j (by omega)).1 hc
        · intro hc
          have hne2 : 2 * j + 2 ≠ right := by omega
          have hnotc : inSubtree right (2 * j + 2) = false :=
            not_inSubtree_child_right right j hnotj hne2
          have hcL : 2 * j + 2 < a.length := by omega
          have hcB : 2 * j + 2 < b.length := by simpa [b, swap_length] using hcL
          have hcc : (heapify b n right)[2 * j + 2]! = b[2 * j + 2]! :=
            heapify_get_outside n b right (2 * j + 2) hnotc hcB
          have hbc : b[2 * j + 2]! = a[2 * j + 2]! := by
            apply swap_getElem!_of_ne a i right (2 * j + 2) hi_len hr_len <;> omega
          rw [hcj, hcc, hbj, hbc]
          exact (hFrom j (by omega)).2 hc
  | case2 a i hi hL hR ih =>
    intro hn hi_n hFrom
    let left := 2 * i + 1
    let right := 2 * i + 2
    let b := swap a i left
    have hi_len : i < a.length := by omega
    have hl_len : left < a.length := by omega
    have hn_b : n ≤ b.length := by simpa [b, swap_length] using hn
    have hFrom_b : HeapFrom b n (left + 1) := by
      refine heapFrom_congr a b n (left + 1)
        (heapFrom_mono a n (i + 1) (left + 1) (by omega) hFrom) ?_
      intro j hj hjn
      exact (swap_getElem!_of_ne a i left j hi_len hl_len (by omega) (by omega)).symm
    have hRest := ih hn_b hL.1 hFrom_b
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_neg hR]
    intro j hj
    by_cases hjl : left ≤ j
    · exact hRest j hjl
    · have hj_lt : j < left := by omega
      have hnotj : inSubtree left j = false := inSubtree_of_lt left j hj_lt
      have hjL : j < a.length := by omega
      have hjB : j < b.length := by simpa [b, swap_length] using hjL
      have hcj : (heapify b n left)[j]! = b[j]! :=
        heapify_get_outside n b left j hnotj hjB
      by_cases hji : j = i
      · rw [hji] at hcj hj ⊢
        constructor
        · intro hc
          have hroot_le : (heapify b n left)[left]! ≤ a[left]! := by
            refine heapify_subtree_le n b left hn_b (a[left]!) ?_ left (inSubtree_self left) hc
            intro t ht htn
            by_cases htl : t = left
            · rw [htl, swap_getElem!_right a i left hi_len hl_len]
              exact le_of_lt hL.2
            · have ht_ne_i : t ≠ i := by
                intro heq
                rw [heq] at ht
                simp [inSubtree_of_lt left i (by omega : i < left)] at ht
              rw [swap_getElem!_of_ne a i left t hi_len hl_len ht_ne_i htl]
              exact heap_subtree_ge a n left t
                (heapFrom_mono a n (i + 1) left (by omega) hFrom) ht htn hn
          rw [hcj, swap_getElem!_left a i left hi_len hl_len]
          exact hroot_le
        · intro hc
          have hnotR : inSubtree left right = false := by
            rw [inSubtree_step left right (by omega)]
            have hpar : (right - 1) / 2 = i := by omega
            rw [hpar]
            exact inSubtree_of_lt left i (by omega)
          have hr_len : right < a.length := by omega
          have hrB : right < b.length := by simpa [b, swap_length] using hr_len
          have hcr : (heapify b n left)[right]! = b[right]! :=
            heapify_get_outside n b left right hnotR hrB
          have hbr : b[right]! = a[right]! :=
            swap_getElem!_of_ne a i left right hi_len hl_len (by omega) (by omega)
          have hbi : b[i]! = a[left]! := swap_getElem!_left a i left hi_len hl_len
          have hle : a[right]! ≤ a[left]! := by
            have hnot : ¬ a[left]! < a[right]! := by
              intro hlt
              exact hR ⟨hc, hlt⟩
            exact not_lt.mp hnot
          rw [hcj, hcr, hbi, hbr]
          exact hle
      · constructor
        · intro hc
          have hnotc : inSubtree left (2 * j + 1) = false :=
            not_inSubtree_child_left left j hnotj (by omega)
          have hcL : 2 * j + 1 < a.length := by omega
          have hcB : 2 * j + 1 < b.length := by simpa [b, swap_length] using hcL
          have hcc : (heapify b n left)[2 * j + 1]! = b[2 * j + 1]! :=
            heapify_get_outside n b left (2 * j + 1) hnotc hcB
          have hbc : b[2 * j + 1]! = a[2 * j + 1]! := by
            apply swap_getElem!_of_ne a i left (2 * j + 1) hi_len hl_len <;> omega
          have hbj : b[j]! = a[j]! := by
            apply swap_getElem!_of_ne a i left j hi_len hl_len <;> omega
          rw [hcj, hcc, hbj, hbc]
          exact (hFrom j (by omega)).1 hc
        · intro hc
          have hnotc : inSubtree left (2 * j + 2) = false :=
            not_inSubtree_child_right left j hnotj (by omega)
          have hcL : 2 * j + 2 < a.length := by omega
          have hcB : 2 * j + 2 < b.length := by simpa [b, swap_length] using hcL
          have hcc : (heapify b n left)[2 * j + 2]! = b[2 * j + 2]! :=
            heapify_get_outside n b left (2 * j + 2) hnotc hcB
          have hbc : b[2 * j + 2]! = a[2 * j + 2]! := by
            apply swap_getElem!_of_ne a i left (2 * j + 2) hi_len hl_len <;> omega
          have hbj : b[j]! = a[j]! := by
            apply swap_getElem!_of_ne a i left j hi_len hl_len <;> omega
          rw [hcj, hcc, hbj, hbc]
          exact (hFrom j (by omega)).2 hc
  | case3 a i hi hL hR ih =>
    intro hn hi_n hFrom
    let right := 2 * i + 2
    let left := 2 * i + 1
    let b := swap a i right
    have hi_len : i < a.length := by omega
    have hr_len : right < a.length := by omega
    have hn_b : n ≤ b.length := by simpa [b, swap_length] using hn
    have hFrom_b : HeapFrom b n (right + 1) := by
      refine heapFrom_congr a b n (right + 1)
        (heapFrom_mono a n (i + 1) (right + 1) (by omega) hFrom) ?_
      intro j hj hjn
      exact (swap_getElem!_of_ne a i right j hi_len hr_len (by omega) (by omega)).symm
    have hRest := ih hn_b hR.1 hFrom_b
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_pos hR]
    intro j hj
    by_cases hjr : right ≤ j
    · exact hRest j hjr
    · have hj_lt : j < right := by omega
      have hnotj : inSubtree right j = false := inSubtree_of_lt right j hj_lt
      have hjL : j < a.length := by omega
      have hjB : j < b.length := by simpa [b, swap_length] using hjL
      have hcj : (heapify b n right)[j]! = b[j]! :=
        heapify_get_outside n b right j hnotj hjB
      by_cases hji : j = i
      · rw [hji] at hcj hj ⊢
        constructor
        · intro hc
          have hnotL : inSubtree right left = false := inSubtree_of_lt right left (by omega)
          have hl_len : left < a.length := by omega
          have hlB : left < b.length := by simpa [b, swap_length] using hl_len
          have hcl : (heapify b n right)[left]! = b[left]! :=
            heapify_get_outside n b right left hnotL hlB
          have hbl : b[left]! = a[left]! :=
            swap_getElem!_of_ne a i right left hi_len hr_len (by omega) (by omega)
          have hbi : b[i]! = a[right]! := swap_getElem!_left a i right hi_len hr_len
          have hle : a[left]! ≤ a[right]! := by
            have hnot : ¬ a[i]! < a[left]! := by
              intro hlt
              exact hL ⟨hc, hlt⟩
            exact le_trans (not_lt.mp hnot) (le_of_lt hR.2)
          rw [hcj, hcl, hbi, hbl]
          exact hle
        · intro hc
          have hbi : b[i]! = a[right]! := swap_getElem!_left a i right hi_len hr_len
          have hroot_le : (heapify b n right)[right]! ≤ a[right]! := by
            refine heapify_subtree_le n b right hn_b (a[right]!) ?_ right (inSubtree_self right) hc
            intro t ht htn
            by_cases htr : t = right
            · rw [htr, swap_getElem!_right a i right hi_len hr_len]
              exact le_of_lt hR.2
            · have ht_ne_i : t ≠ i := by
                intro heq
                rw [heq] at ht
                simp [inSubtree_of_lt right i (by omega : i < right)] at ht
              rw [swap_getElem!_of_ne a i right t hi_len hr_len ht_ne_i htr]
              exact heap_subtree_ge a n right t
                (heapFrom_mono a n (i + 1) right (by omega) hFrom) ht htn hn
          rw [hcj, hbi]
          exact hroot_le
      · constructor
        · intro hc
          have hnotc : inSubtree right (2 * j + 1) = false :=
            not_inSubtree_child_left right j hnotj (by omega)
          have hcL : 2 * j + 1 < a.length := by omega
          have hcB : 2 * j + 1 < b.length := by simpa [b, swap_length] using hcL
          have hcc : (heapify b n right)[2 * j + 1]! = b[2 * j + 1]! :=
            heapify_get_outside n b right (2 * j + 1) hnotc hcB
          have hbc : b[2 * j + 1]! = a[2 * j + 1]! := by
            apply swap_getElem!_of_ne a i right (2 * j + 1) hi_len hr_len <;> omega
          have hbj : b[j]! = a[j]! := by
            apply swap_getElem!_of_ne a i right j hi_len hr_len <;> omega
          rw [hcj, hcc, hbj, hbc]
          exact (hFrom j (by omega)).1 hc
        · intro hc
          have hnotc : inSubtree right (2 * j + 2) = false :=
            not_inSubtree_child_right right j hnotj (by omega)
          have hcL : 2 * j + 2 < a.length := by omega
          have hcB : 2 * j + 2 < b.length := by simpa [b, swap_length] using hcL
          have hcc : (heapify b n right)[2 * j + 2]! = b[2 * j + 2]! :=
            heapify_get_outside n b right (2 * j + 2) hnotc hcB
          have hbc : b[2 * j + 2]! = a[2 * j + 2]! := by
            apply swap_getElem!_of_ne a i right (2 * j + 2) hi_len hr_len <;> omega
          have hbj : b[j]! = a[j]! := by
            apply swap_getElem!_of_ne a i right j hi_len hr_len <;> omega
          rw [hcj, hcc, hbj, hbc]
          exact (hFrom j (by omega)).2 hc
  | case4 a i hi hL hR =>
    intro hn hi_n hFrom
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_neg hR]
    intro j hj
    by_cases hji : i < j
    · exact hFrom j (by omega)
    · have hj_eq : j = i := by omega
      rw [hj_eq]
      constructor
      · intro hc
        have hnot : ¬ a[i]! < a[2 * i + 1]! := by
          intro hlt
          exact hL ⟨hc, hlt⟩
        exact not_lt.mp hnot
      · intro hc
        have hnot : ¬ a[i]! < a[2 * i + 2]! := by
          intro hlt
          exact hR ⟨hc, hlt⟩
        exact not_lt.mp hnot
  | case5 a i hi =>
    intro hn hi_n hFrom
    exact (hi ⟨hi_n, hn⟩).elim

def buildGo (n s : Nat) (a : List Int) : List Int :=
  match s with
  | 0 => a
  | s + 1 => buildGo n s (heapify a n s)

theorem buildGo_length (n s : Nat) (a : List Int) (ha : a.length = n) :
    (buildGo n s a).length = n := by
  induction s generalizing a with
  | zero => simpa [buildGo] using ha
  | succ s ih =>
    simpa [buildGo] using ih (heapify a n s) (by rw [heapify_length, ha])

theorem buildGo_perm (n s : Nat) (a : List Int) :
    List.Perm (buildGo n s a) a := by
  induction s generalizing a with
  | zero =>
    simp [buildGo]
  | succ s ih =>
    simpa [buildGo] using List.Perm.trans (ih (heapify a n s)) (heapify_perm n a s)

theorem heapFrom_leaves (a : List Int) (n : Nat) (_hn : n ≤ a.length) :
    HeapFrom a n (n / 2) := by
  intro j hj
  constructor <;> intro hc <;> omega

theorem buildGo_heap (n s : Nat) (a : List Int)
    (ha : a.length = n) (hs : s ≤ n) (h : HeapFrom a n s) :
    HeapFrom (buildGo n s a) n 0 := by
  induction s generalizing a with
  | zero => simpa [buildGo] using h
  | succ s ih =>
    have hs' : s < n := by omega
    have hHeap := heapify_restores n a s (by simp [ha]) hs' h
    exact ih (heapify a n s) (by rw [heapify_length, ha]) (by omega) hHeap

def SuffixSorted (a : List Int) (start : Nat) : Prop :=
  ∀ i j, start ≤ i → i < j → j < a.length → a[i]! ≤ a[j]!

def CrossLe (a : List Int) (sz : Nat) : Prop :=
  ∀ i j, i < sz → sz ≤ j → j < a.length → a[i]! ≤ a[j]!

def FullySorted (a : List Int) : Prop :=
  ∀ i j, i < j → j < a.length → a[i]! ≤ a[j]!

theorem fullySorted_of_split (a : List Int) (sz : Nat) (hsz : sz ≤ 1)
    (hSuf : SuffixSorted a sz) (hCross : CrossLe a sz) : FullySorted a := by
  intro i j hij hj
  by_cases hi : sz ≤ i
  · exact hSuf i j hi hij hj
  · have hi' : i < sz := by omega
    have hj' : sz ≤ j := by omega
    exact hCross i j hi' hj' hj

theorem heap_root_max (a : List Int) (n k : Nat)
    (hH : HeapFrom a n 0) (hk : k < n) (hn : n ≤ a.length) :
    a[0]! ≥ a[k]! :=
  heap_subtree_ge a n 0 k hH (inSubtree_zero k) hk hn

theorem swap_prefix_val (a : List Int) (i j k n : Nat)
    (hi : i < n) (hj : j < n) (hk : k < n) (hn : n ≤ a.length) :
    ∃ t, t < n ∧ (swap a i j)[k]! = a[t]! := by
  have hi' : i < a.length := by omega
  have hj' : j < a.length := by omega
  by_cases hki : k = i
  · refine ⟨j, hj, ?_⟩
    rw [hki, swap_getElem!_left a i j hi' hj']
  · by_cases hkj : k = j
    · refine ⟨i, hi, ?_⟩
      rw [hkj, swap_getElem!_right a i j hi' hj']
    · refine ⟨k, hk, ?_⟩
      exact swap_getElem!_of_ne a i j k hi' hj' hki hkj

theorem heapify_prefix_val (n : Nat) (a : List Int) (idx : Nat) :
    n ≤ a.length → ∀ k, k < n → ∃ t, t < n ∧ (heapify a n idx)[k]! = a[t]! := by
  induction a, idx using heapify.induct n with
  | case1 a i hi hL hR ih =>
    intro hn k hk
    let right := 2 * i + 2
    let b := swap a i right
    have hn_b : n ≤ b.length := by simpa [b, swap_length] using hn
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_pos hR]
    obtain ⟨t, ht, heq⟩ := ih hn_b k hk
    obtain ⟨s, hs, heq'⟩ := swap_prefix_val a i right t n hi.1 hR.1 ht hn
    exact ⟨s, hs, by rw [heq, heq']⟩
  | case2 a i hi hL hR ih =>
    intro hn k hk
    let left := 2 * i + 1
    let b := swap a i left
    have hn_b : n ≤ b.length := by simpa [b, swap_length] using hn
    unfold heapify
    rw [dif_pos hi, dif_pos hL, dif_neg hR]
    obtain ⟨t, ht, heq⟩ := ih hn_b k hk
    obtain ⟨s, hs, heq'⟩ := swap_prefix_val a i left t n hi.1 hL.1 ht hn
    exact ⟨s, hs, by rw [heq, heq']⟩
  | case3 a i hi hL hR ih =>
    intro hn k hk
    let right := 2 * i + 2
    let b := swap a i right
    have hn_b : n ≤ b.length := by simpa [b, swap_length] using hn
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_pos hR]
    obtain ⟨t, ht, heq⟩ := ih hn_b k hk
    obtain ⟨s, hs, heq'⟩ := swap_prefix_val a i right t n hi.1 hR.1 ht hn
    exact ⟨s, hs, by rw [heq, heq']⟩
  | case4 a i hi hL hR =>
    intro hn k hk
    unfold heapify
    rw [dif_pos hi, dif_neg hL, dif_neg hR]
    exact ⟨k, hk, rfl⟩
  | case5 a i hi =>
    intro hn k hk
    unfold heapify
    rw [dif_neg hi]
    exact ⟨k, hk, rfl⟩

def extract (a : List Int) : Nat → List Int
  | 0 => a
  | 1 => a
  | sz + 2 => extract (heapify (swap a 0 (sz + 1)) (sz + 1) 0) (sz + 1)

theorem extract_length (sz : Nat) (a : List Int) (hn : sz ≤ a.length) :
    (extract a sz).length = a.length := by
  induction sz using Nat.strongRecOn generalizing a with
  | ind sz ih =>
    cases sz with
    | zero => simp [extract]
    | succ sz =>
      cases sz with
      | zero => simp [extract]
      | succ sz =>
        have hlen : (heapify (swap a 0 (sz + 1)) (sz + 1) 0).length = a.length := by
          rw [heapify_length, swap_length]
        have hsz : sz + 1 ≤ (heapify (swap a 0 (sz + 1)) (sz + 1) 0).length := by
          rw [hlen]; omega
        rw [extract, ih (sz + 1) (by omega) (heapify (swap a 0 (sz + 1)) (sz + 1) 0) hsz, hlen]

theorem extract_perm (sz : Nat) (a : List Int) :
    List.Perm (extract a sz) a := by
  induction sz using Nat.strongRecOn generalizing a with
  | ind sz ih =>
    cases sz with
    | zero => simp [extract]
    | succ sz =>
      cases sz with
      | zero => simp [extract]
      | succ sz =>
        simp [extract]
        exact List.Perm.trans
          (ih (sz + 1) (by omega) (heapify (swap a 0 (sz + 1)) (sz + 1) 0))
          (List.Perm.trans (heapify_perm _ _ _) (swap_perm _ _ _))


theorem extract_sorted (sz : Nat) (a : List Int)
    (hn : sz ≤ a.length)
    (hHeap : HeapFrom a sz 0)
    (hSuf : SuffixSorted a sz)
    (hCross : CrossLe a sz) :
    FullySorted (extract a sz) := by
  induction sz using Nat.strongRecOn generalizing a with
  | ind sz ih =>
    cases sz with
    | zero =>
      simpa [extract] using fullySorted_of_split a 0 (by omega) hSuf hCross
    | succ sz =>
      cases sz with
      | zero =>
        simpa [extract] using fullySorted_of_split a 1 (by omega) hSuf hCross
      | succ sz =>
        let endIdx := sz + 1
        let swapped := swap a 0 endIdx
        let heapArr := heapify swapped endIdx 0
        have hend_len : endIdx < a.length := by omega
        have h0_len : 0 < a.length := by omega
        have hlenSw : swapped.length = a.length := by simp [swapped, swap_length]
        have hlenArr : heapArr.length = a.length := by simp [heapArr, heapify_length, hlenSw]
        have hFromSw : HeapFrom swapped endIdx 1 := by
          intro j hj
          constructor
          · intro hc
            have hbj : swapped[j]! = a[j]! := by
              apply swap_getElem!_of_ne a 0 endIdx j h0_len hend_len <;> omega
            have hbc : swapped[2 * j + 1]! = a[2 * j + 1]! := by
              apply swap_getElem!_of_ne a 0 endIdx (2 * j + 1) h0_len hend_len <;> omega
            rw [hbj, hbc]
            exact (hHeap j (by omega)).1 (by omega)
          · intro hc
            have hbj : swapped[j]! = a[j]! := by
              apply swap_getElem!_of_ne a 0 endIdx j h0_len hend_len <;> omega
            have hbc : swapped[2 * j + 2]! = a[2 * j + 2]! := by
              apply swap_getElem!_of_ne a 0 endIdx (2 * j + 2) h0_len hend_len <;> omega
            rw [hbj, hbc]
            exact (hHeap j (by omega)).2 (by omega)
        have hHeapArr : HeapFrom heapArr endIdx 0 := by
          have h := heapify_restores endIdx swapped 0 (by simp [hlenSw]; omega) (by omega) hFromSw
          simpa [heapArr] using h
        have hEnd : heapArr[endIdx]! = a[0]! := by
          have h1 : heapArr[endIdx]! = swapped[endIdx]! := by
            have h := heapify_get_ge endIdx swapped 0 endIdx (by omega) (by simp [hlenSw]; exact hend_len)
            simpa [heapArr] using h
          rw [h1]
          simpa [swapped] using swap_getElem!_right a 0 endIdx h0_len hend_len
        have htail : ∀ k, endIdx < k → k < a.length → heapArr[k]! = a[k]! := by
          intro k hk hkL
          have h1 : heapArr[k]! = swapped[k]! := by
            have h := heapify_get_ge endIdx swapped 0 k (by omega) (by simp [hlenSw]; exact hkL)
            simpa [heapArr] using h
          rw [h1]
          simpa [swapped] using swap_getElem!_of_ne a 0 endIdx k h0_len hend_len (by omega) (by omega)
        have hSufArr : SuffixSorted heapArr endIdx := by
          intro p q hp hpq hq
          have hq' : q < a.length := by simpa [hlenArr] using hq
          by_cases hp' : endIdx < p
          · rw [htail p hp' (by omega), htail q (by omega) hq']
            exact hSuf p q (by omega) hpq hq'
          · have hp0 : p = endIdx := by omega
            rw [hp0, hEnd, htail q (by omega) hq']
            exact hCross 0 q (by omega) (by omega) hq'
        have hCrossArr : CrossLe heapArr endIdx := by
          intro p q hp hq hqL
          have hq' : q < a.length := by simpa [hlenArr] using hqL
          obtain ⟨t, ht, ht_eq⟩ := heapify_prefix_val endIdx swapped 0 (by simp [hlenSw]; omega) p hp
          have hpt : heapArr[p]! = swapped[t]! := by simpa [heapArr] using ht_eq
          obtain ⟨s, hs, hs_eq⟩ :=
            swap_prefix_val a 0 endIdx t (endIdx + 1) (by omega) (by omega) (by omega) (by omega)
          have hps : heapArr[p]! = a[s]! := by rw [hpt]; simpa [swapped] using hs_eq
          have hmax : a[s]! ≤ a[0]! := heap_root_max a (endIdx + 1) s hHeap hs (by omega)
          by_cases hq0 : q = endIdx
          · rw [hps, hq0, hEnd]
            exact hmax
          · have hqgt : endIdx < q := by omega
            rw [hps, htail q hqgt hq']
            exact hCross s q hs (by omega) hq'
        have hres := ih endIdx (by omega) heapArr (by simp [hlenArr]; omega) hHeapArr hSufArr hCrossArr
        simpa [extract, endIdx, swapped, heapArr] using hres


theorem fullySorted_iff_sorted (a : List Int) :
    FullySorted a ↔ List.Sorted (· ≤ ·) a := by
  constructor
  · intro h
    unfold List.Sorted
    rw [List.pairwise_iff_getElem]
    intro idx jdx hidx hjdx hij
    have h1 : a[idx]! = a[idx] := getElem!_pos a idx hidx
    have h2 : a[jdx]! = a[jdx] := getElem!_pos a jdx hjdx
    rw [← h1, ← h2]
    exact h idx jdx hij hjdx
  · intro h idx jdx hij hjdx
    have hidx : idx < a.length := by omega
    unfold List.Sorted at h
    rw [List.pairwise_iff_getElem] at h
    have h1 : a[idx]! = a[idx] := getElem!_pos a idx hidx
    have h2 : a[jdx]! = a[jdx] := getElem!_pos a jdx hjdx
    rw [h1, h2]
    exact h idx jdx hidx hjdx hij


def heapSort (a : List Int) : List Int :=
  if a.length ≤ 1 then
    a
  else
    extract (buildGo a.length (a.length / 2) a) a.length

theorem heapSort_perm (a : List Int) : List.Perm (heapSort a) a := by
  unfold heapSort
  split
  · exact List.Perm.rfl
  · exact List.Perm.trans (extract_perm _ _) (buildGo_perm _ _ _)

theorem heapSort_length (a : List Int) : (heapSort a).length = a.length :=
  (heapSort_perm a).length_eq

theorem heapSort_sorted (a : List Int) : List.Sorted (· ≤ ·) (heapSort a) := by
  unfold heapSort
  split
  · rename_i hshort
    rw [← fullySorted_iff_sorted]
    apply fullySorted_of_split a a.length (by omega)
    · intro idx jdx hidx hij hjdx
      omega
    · intro idx jdx hidx hjdx hjL
      omega
  · rename_i hlong
    rw [← fullySorted_iff_sorted]
    have hlen : (buildGo a.length (a.length / 2) a).length = a.length :=
      buildGo_length a.length (a.length / 2) a rfl
    have hHeap :=
      buildGo_heap a.length (a.length / 2) a rfl (by omega)
        (heapFrom_leaves a a.length (by omega))
    have hSuf : SuffixSorted (buildGo a.length (a.length / 2) a) a.length := by
      intro idx jdx hidx hij hjdx
      omega
    have hCross : CrossLe (buildGo a.length (a.length / 2) a) a.length := by
      intro idx jdx hidx hjdx hjL
      omega
    simpa using
      extract_sorted a.length (buildGo a.length (a.length / 2) a) (by simp [hlen]) hHeap hSuf hCross

theorem fold_buildGo (n s : Nat) (a : List Int) :
    ((List.range s).reverse).foldl (fun cur idx => heapify cur n idx) a = buildGo n s a := by
  induction s generalizing a with
  | zero => simp [buildGo]
  | succ s ih =>
    simp [List.range_succ, List.reverse_append, buildGo, ih]

def extractSteps (n : Nat) : List Nat :=
  (List.range (n - 1)).reverse.map (fun idx => idx + 1)

theorem extract_eq_foldl (a : List Int) (n : Nat) :
    extract a n =
      (extractSteps n).foldl (fun cur j => heapify (swap cur 0 j) j 0) a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp [extract, extractSteps, List.range_succ, List.reverse_append, ih]


/-! ## Unit tests -/

example : heapSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : heapSort ([] : List Int) = [] := by native_decide
example : heapSort [1] = [1] := by native_decide
example : heapSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSort [2, 1] = [1, 2] := by native_decide
example : heapSort [1, 2] = [1, 2] := by native_decide
example : heapSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : heapSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : heapSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : heapSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : heapSort [-1, -3, 2, 0] = [-3, -1, 0, 2] := by native_decide

#eval heapSort ([3, 1, 2] : List Int)
#eval heapSort ([] : List Int)
#eval heapSort ([1] : List Int)
#eval heapSort ([5, 2, 4, 6, 1, 3] : List Int)
#eval heapSort ([-1, -3, 2, 0] : List Int)

/-! ## Precondition -/

/-- Python `pre`: the argument is a list of integers.
Every value of type `List Int` meets that requirement. A non-list or a list
containing a non-integer is not a `List Int`; the Python program rejects those
inputs with `ValueError`. -/
def Pre (_arr : List Int) : Prop := True

/-! ## Properties -/

/-- The output is sorted in non-decreasing order. -/
def sorted_prop (a : List Int) : Prop :=
  List.Sorted (· ≤ ·) (heapSort a)

theorem sorted_thm (a : List Int) : sorted_prop a :=
  heapSort_sorted a

/-- The output is a permutation of the input, so multiplicities are preserved. -/
def perm_prop (a : List Int) : Prop :=
  List.Perm (heapSort a) a

theorem perm_thm (a : List Int) : perm_prop a :=
  heapSort_perm a

/-- The output has the same length as the input. -/
def length_prop (a : List Int) : Prop :=
  (heapSort a).length = a.length

theorem length_thm (a : List Int) : length_prop a :=
  heapSort_length a

/-- Empty and singleton inputs are returned unchanged, as in Python `copy`. -/
def short_prop (a : List Int) : Prop :=
  a.length ≤ 1 → heapSort a = a

theorem short_thm (a : List Int) : short_prop a := by
  intro h
  unfold heapSort
  simp [h]

def empty_prop : Prop :=
  heapSort ([] : List Int) = []

theorem empty_thm : empty_prop := by
  unfold empty_prop heapSort
  simp

def singleton_prop (x : Int) : Prop :=
  heapSort [x] = [x]

theorem singleton_thm (x : Int) : singleton_prop x := by
  unfold singleton_prop heapSort
  simp

/-- Sorting twice is the same as sorting once. -/
def idempotent_prop (a : List Int) : Prop :=
  heapSort (heapSort a) = heapSort a

theorem idempotent_thm (a : List Int) : idempotent_prop a := by
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact heapSort_perm (heapSort a)
  · exact heapSort_sorted (heapSort a)
  · exact heapSort_sorted a

/-- Heap sort agrees with merge sort, i.e. it returns the unique non-decreasing rearrangement. -/
def mergesort_prop (a : List Int) : Prop :=
  heapSort a = a.mergeSort (fun x y => x ≤ y)

theorem mergesort_thm (a : List Int) : mergesort_prop a := by
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact List.Perm.trans (heapSort_perm a) (List.mergeSort_perm a (fun x y => x ≤ y)).symm
  · exact heapSort_sorted a
  · simpa using List.sorted_mergeSort' (r := (· ≤ ·)) a

/-- Any non-decreasing permutation of the input equals the heap-sort result. -/
def unique_sorted_prop (a : List Int) : Prop :=
  ∀ b, List.Sorted (· ≤ ·) b → List.Perm b a → b = heapSort a

theorem unique_sorted_thm (a : List Int) : unique_sorted_prop a := by
  intro b hb hp
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact List.Perm.trans hp (heapSort_perm a).symm
  · exact hb
  · exact heapSort_sorted a

/-! ## Post-condition -/

/-- Post-condition of Python `heap_sort`: sorted, same elements, same length,
and unchanged on inputs of length at most one. -/
def Post_prop (a : List Int) : Prop :=
  sorted_prop a ∧ perm_prop a ∧ length_prop a ∧ short_prop a

/-! ## Property-based tests -/

/-- Consecutive non-decreasing check, the executable form of `List.Sorted (· ≤ ·)`. -/
def isSorted : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => (x ≤ y) && isSorted (y :: xs)

def pbtCfg : Plausible.Configuration :=
  { numInst := 25, maxSize := 12, quiet := true }

-- sorted_prop
#eval Plausible.Testable.check (∀ xs : List Int, isSorted (heapSort xs) = true) pbtCfg
-- perm_prop
#eval Plausible.Testable.check (∀ xs : List Int, (heapSort xs).isPerm xs = true) pbtCfg
-- length_prop
#eval Plausible.Testable.check (∀ xs : List Int, (heapSort xs).length = xs.length) pbtCfg
-- short_prop (implication may discard samples; bounded check is below)
#eval Plausible.Testable.check (∀ xs : List Int, xs.length ≤ 1 → heapSort xs = xs) pbtCfg
-- empty_prop
#eval Plausible.Testable.check (heapSort ([] : List Int) = []) pbtCfg
-- singleton_prop
#eval Plausible.Testable.check (∀ x : Int, heapSort [x] = [x]) pbtCfg
-- idempotent_prop
#eval Plausible.Testable.check (∀ xs : List Int, heapSort (heapSort xs) = heapSort xs) pbtCfg
-- mergesort_prop, also the executable form of unique_sorted_prop
#eval Plausible.Testable.check (∀ xs : List Int, heapSort xs = xs.mergeSort (fun x y => x ≤ y)) pbtCfg
-- Post_prop
#eval Plausible.Testable.check (∀ xs : List Int,
    isSorted (heapSort xs) = true ∧ (heapSort xs).isPerm xs = true ∧
      (heapSort xs).length = xs.length ∧ (xs.length ≤ 1 → heapSort xs = xs)) pbtCfg

def boundedInputs : List (List Int) :=
  [[], [0], [1], [-5], [2, 1], [1, 2], [1, 1],
   [3, 1, 2], [5, 2, 4, 6, 1, 3], [9, 8, 7, 6, 5, 4, 3, 2, 1],
   [3, 1, 4, 1, 2, 3], [-1, -3, 2, 0], [5, 5, 5],
   [64, 34, 25, 12, 22, 11, 90]]

example : boundedInputs.all (fun xs => isSorted (heapSort xs)) = true := by native_decide
example : boundedInputs.all (fun xs => (heapSort xs).isPerm xs) = true := by native_decide
example : boundedInputs.all (fun xs => (heapSort xs).length == xs.length) = true := by native_decide
example : boundedInputs.all (fun xs => if xs.length ≤ 1 then heapSort xs == xs else true) = true := by native_decide
example : boundedInputs.all (fun xs => heapSort (heapSort xs) == heapSort xs) = true := by native_decide
example : boundedInputs.all (fun xs => heapSort xs == xs.mergeSort (fun x y => x ≤ y)) = true := by native_decide
example : boundedInputs.all (fun xs =>
    isSorted (heapSort xs) && (heapSort xs).isPerm xs &&
      ((heapSort xs).length == xs.length) &&
      (if xs.length ≤ 1 then heapSort xs == xs else true)) = true := by native_decide
example : ([[], [0], [1], [-7]] : List (List Int)).all (fun xs => heapSort xs == xs) = true := by native_decide
example : (List.range 20).all (fun n =>
    let xs := (List.range n).map (fun i => Int.ofNat (n - i))
    heapSort xs == (List.range n).map (fun i => Int.ofNat (i + 1))) = true := by native_decide
example : (List.range 20).all (fun n =>
    let xs := (List.range n).map Int.ofNat
    heapSort xs == xs) = true := by native_decide

/-! ## Correctness -/

theorem correctness_thm (a : List Int) (_h : Pre a) : Post_prop a :=
  ⟨sorted_thm a, perm_thm a, length_thm a, short_thm a⟩

/-! ## Imperative implementation -/

def heapSortImp (a : List Int) : List Int :=
  Id.run do
    if a.length ≤ 1 then
      return a
    let n := a.length
    let mut cur := a
    for idx in (List.range (n / 2)).reverse do
      cur := heapify cur n idx
    for j in extractSteps n do
      cur := heapify (swap cur 0 j) j 0
    return cur


/-! ## Imperative tests -/

example : heapSortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSortImp ([] : List Int) = [] := by native_decide
example : heapSortImp [1] = [1] := by native_decide
example : heapSortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapSortImp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : heapSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : heapSortImp [-1, -3, 2, 0] = [-3, -1, 0, 2] := by native_decide
example : heapSortImp [2, 1] = [1, 2] := by native_decide

#eval heapSortImp ([3, 1, 2] : List Int)
#eval heapSortImp ([5, 4, 3, 2, 1] : List Int)
#eval heapSortImp ([] : List Int)

/-! ## Equivalence -/

theorem heapSortImp_eq_fold (a : List Int) (h : ¬a.length ≤ 1) :
    heapSortImp a =
      (extractSteps a.length).foldl (fun cur j => heapify (swap cur 0 j) j 0)
        (((List.range (a.length / 2)).reverse).foldl (fun cur idx => heapify cur a.length idx) a) := by
  simp only [heapSortImp, h, ite_false, Id.run, pure_bind, List.forIn_pure_yield_eq_foldl]
  rfl

theorem heapSort_eq_imp (a : List Int) : heapSort a = heapSortImp a := by
  by_cases h : a.length ≤ 1
  · simp [heapSort, heapSortImp, h]
  · rw [heapSortImp_eq_fold a h]
    simp only [heapSort, h, ite_false]
    rw [fold_buildGo, ← extract_eq_foldl]


theorem equivalence_thm (a : List Int) : heapSort a = heapSortImp a :=
  heapSort_eq_imp a

end heap_sort
