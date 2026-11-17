import Mathlib

/-!
# Heap sort

Lean 4 formalization of the Python heap sort on a list of integers.

The functional implementation follows the Python algorithm: build a max-heap by
sifting down from the last non-leaf, then repeatedly swap the root with the end
of the heap and sift the reduced prefix. Comparisons use the strict order `>`,
so equal elements are not swapped. Empty and singleton inputs are returned
unchanged, matching the Python early return (which is a copy).

Python raises `ValueError` when the input is not a list of integers. In Lean
that check is the type `List Int`: every well-typed input is admissible, and
values that are not integers lie outside the type.
-/

namespace heap_sort

open List

/-! ## Index helpers -/

/-- `idx` lies in the binary-heap subtree rooted at `root` (array layout). -/
def inSubtree (root idx : Nat) : Bool :=
  if idx < root then
    false
  else if idx == root then
    true
  else
    inSubtree root ((idx - 1) / 2)
termination_by idx
decreasing_by
  simp_all
  omega

theorem inSubtree_self (i : Nat) : inSubtree i i = true := by
  rw [inSubtree.eq_def]
  simp

theorem inSubtree_of_lt {root idx : Nat} (h : idx < root) : inSubtree root idx = false := by
  rw [inSubtree.eq_def]
  simp [h]

theorem inSubtree_le {root idx : Nat} (h : inSubtree root idx = true) : root ≤ idx := by
  rw [inSubtree.eq_def] at h
  by_cases hlt : idx < root
  · simp [hlt] at h
  · omega

theorem inSubtree_parent {root idx : Nat} (h : root < idx) :
    inSubtree root idx = inSubtree root ((idx - 1) / 2) := by
  rw [inSubtree.eq_def]
  have hlt : ¬ idx < root := by omega
  have hne : idx ≠ root := by omega
  simp [hlt, hne]

/-- A positive index is the left or right child of its parent. -/
theorem child_split (j : Nat) (hj : 0 < j) :
    j = 2 * ((j - 1) / 2) + 1 ∨ j = 2 * ((j - 1) / 2) + 2 := by
  have hdiv : 2 * ((j - 1) / 2) + (j - 1) % 2 = j - 1 := Nat.div_add_mod (j - 1) 2
  have hmod : (j - 1) % 2 = 0 ∨ (j - 1) % 2 = 1 := by
    have : (j - 1) % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  rcases hmod with h0 | h1
  · left
    omega
  · right
    omega

theorem inSubtree_left_child (i : Nat) : inSubtree i (2 * i + 1) = true := by
  rw [inSubtree_parent (by omega : i < 2 * i + 1)]
  rw [show (2 * i + 1 - 1) / 2 = i by omega]
  exact inSubtree_self i

theorem inSubtree_right_child (i : Nat) : inSubtree i (2 * i + 2) = true := by
  rw [inSubtree_parent (by omega : i < 2 * i + 2)]
  rw [show (2 * i + 2 - 1) / 2 = i by omega]
  exact inSubtree_self i

theorem inSubtree_of_left {i j : Nat} (h : inSubtree (2 * i + 1) j = true) :
    inSubtree i j = true := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    have hj : 2 * i + 1 ≤ j := inSubtree_le h
    have hij : i < j := by omega
    rw [inSubtree_parent hij]
    by_cases heq : j = 2 * i + 1
    · subst heq
      rw [show (2 * i + 1 - 1) / 2 = i by omega]
      exact inSubtree_self i
    · have hgt : 2 * i + 1 < j := by omega
      have hrec : inSubtree (2 * i + 1) ((j - 1) / 2) = true := by
        rw [← inSubtree_parent hgt]
        exact h
      have hp : (j - 1) / 2 < j := by omega
      exact ih _ hp hrec

theorem inSubtree_of_right {i j : Nat} (h : inSubtree (2 * i + 2) j = true) :
    inSubtree i j = true := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    have hj : 2 * i + 2 ≤ j := inSubtree_le h
    have hij : i < j := by omega
    rw [inSubtree_parent hij]
    by_cases heq : j = 2 * i + 2
    · subst heq
      rw [show (2 * i + 2 - 1) / 2 = i by omega]
      exact inSubtree_self i
    · have hgt : 2 * i + 2 < j := by omega
      have hrec : inSubtree (2 * i + 2) ((j - 1) / 2) = true := by
        rw [← inSubtree_parent hgt]
        exact h
      have hp : (j - 1) / 2 < j := by omega
      exact ih _ hp hrec

theorem inSubtree_left_right_disjoint {i j : Nat}
    (hl : inSubtree (2 * i + 1) j = true) (hr : inSubtree (2 * i + 2) j = true) : False := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    have hjr : 2 * i + 2 ≤ j := inSubtree_le hr
    have hjl : 2 * i + 1 ≤ j := inSubtree_le hl
    have hneL : j ≠ 2 * i + 1 := by omega
    by_cases heq : j = 2 * i + 2
    · subst heq
      have hparent : inSubtree (2 * i + 1) (2 * i + 2) =
          inSubtree (2 * i + 1) ((2 * i + 2 - 1) / 2) := by
        apply inSubtree_parent
        omega
      have hp : (2 * i + 2 - 1) / 2 = i := by omega
      rw [hparent, hp, inSubtree_of_lt (by omega : i < 2 * i + 1)] at hl
      simp at hl
    · have hl' : inSubtree (2 * i + 1) ((j - 1) / 2) = true := by
        have : 2 * i + 1 < j := by omega
        rw [← inSubtree_parent this]
        exact hl
      have hr' : inSubtree (2 * i + 2) ((j - 1) / 2) = true := by
        have : 2 * i + 2 < j := by omega
        rw [← inSubtree_parent this]
        exact hr
      exact ih _ (by omega) hl' hr'

theorem inSubtree_split {i j : Nat} (h : inSubtree i j = true) (hne : j ≠ i) :
    inSubtree (2 * i + 1) j = true ∨ inSubtree (2 * i + 2) j = true := by
  induction j using Nat.strongRecOn generalizing i with
  | ind j ih =>
    have hij : i < j := by
      have := inSubtree_le h
      omega
    have hparent : inSubtree i ((j - 1) / 2) = true := by
      rw [← inSubtree_parent hij]
      exact h
    let p := (j - 1) / 2
    by_cases hp : p = i
    · have hp' : (j - 1) / 2 = i := by simpa [p] using hp
      rcases child_split j (by omega) with hleft | hright
      · left
        rw [hp'] at hleft
        simpa [hleft] using inSubtree_self (2 * i + 1)
      · right
        rw [hp'] at hright
        simpa [hright] using inSubtree_self (2 * i + 2)
    · have hplt : p < j := by omega
      have hsub := ih p hplt hparent (by simpa [p] using hp)
      have hp_eq : (j - 1) / 2 = p := rfl
      rcases hsub with hsub | hsub
      · left
        have hc : 2 * i + 1 < j := by
          have := inSubtree_le hsub
          omega
        rw [inSubtree_parent hc, hp_eq]
        exact hsub
      · right
        have hc : 2 * i + 2 < j := by
          have := inSubtree_le hsub
          omega
        rw [inSubtree_parent hc, hp_eq]
        exact hsub

theorem inSubtree_zero (k : Nat) : inSubtree 0 k = true := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero =>
      simpa using inSubtree_self 0
    | succ k =>
      rw [inSubtree_parent (by omega : 0 < k + 1)]
      exact ih ((k + 1 - 1) / 2) (by omega)

theorem not_inSubtree_ancestor {i : Nat} : inSubtree (2 * i + 1) i = false :=
  inSubtree_of_lt (by omega)

/-! ## Swapping and choosing the larger child -/

/-- Swap indices `i` and `j` when both are in range. -/
def swapList (a : List Int) (i j : Nat) : List Int :=
  if hi : i < a.length then
    if hj : j < a.length then
      (a.set i a[j]).set j a[i]
    else
      a
  else
    a

theorem swapList_length (a : List Int) (i j : Nat) : (swapList a i j).length = a.length := by
  unfold swapList
  split_ifs <;> simp

theorem swapList_perm (a : List Int) (i j : Nat) : swapList a i j ~ a := by
  unfold swapList
  split_ifs with hi hj
  · exact set_set_perm hi hj
  · rfl
  · rfl

theorem swapList_getElem! (a : List Int) (i j k : Nat) (hk : k < a.length) :
    (swapList a i j)[k]! =
      if i < a.length ∧ j < a.length then
        if k = i then a[j]! else if k = j then a[i]! else a[k]!
      else
        a[k]! := by
  unfold swapList
  by_cases hi : i < a.length
  · by_cases hj : j < a.length
    · simp only [hi, hj, and_self, ↓reduceDIte]
      have hk' : k < ((a.set i a[j]).set j a[i]).length := by simpa using hk
      rw [show ((a.set i a[j]).set j a[i])[k]! =
          ((a.set i a[j]).set j a[i])[k] by rw [getElem!_pos (h := hk')]]
      simp only [getElem_set]
      by_cases hki : k = i
      · simp only [hki, ite_true, ite_false, getElem!_pos, hj]
        by_cases hkj : k = j
        · simp [hkj, getElem!_pos, hi]
        · simp [hkj, getElem!_pos, hj]
      · by_cases hkj : k = j
        · simp only [hki, hkj, ite_true, ite_false, getElem!_pos, hi]
        · simp only [hki, hkj, ite_false, getElem!_pos, hk]
    · simp [hi, hj, getElem!_pos, hk]
  · simp [hi, getElem!_pos, hk]

theorem swapList_get_left (a : List Int) (i j : Nat) (hi : i < a.length) (hj : j < a.length) :
    (swapList a i j)[i]! = a[j]! := by
  rw [swapList_getElem! a i j i hi]
  simp [hi, hj]

theorem swapList_get_right (a : List Int) (i j : Nat) (hi : i < a.length) (hj : j < a.length) :
    (swapList a i j)[j]! = a[i]! := by
  rw [swapList_getElem! a i j j hj]
  by_cases hij : j = i
  · subst hij
    simp [hi]
  · simp [hi, hj, hij]

theorem swapList_get_ne (a : List Int) (i j k : Nat) (hk : k < a.length)
    (hki : k ≠ i) (hkj : k ≠ j) : (swapList a i j)[k]! = a[k]! := by
  rw [swapList_getElem! a i j k hk]
  by_cases h : i < a.length ∧ j < a.length
  · simp [h, hki, hkj]
  · simp [h]

/-- Index of the larger child of `i` inside a heap of size `n`, or `i` if `i` is largest.
Mirrors the Python `heapify` child selection (`>` , so ties keep the parent). -/
def chooseLargest (a : List Int) (n i : Nat) : Nat :=
  let left := 2 * i + 1
  let right := 2 * i + 2
  if left < n then
    if right < n then
      if a[i]! < a[left]! then
        if a[left]! < a[right]! then right else left
      else
        if a[i]! < a[right]! then right else i
    else
      if a[i]! < a[left]! then left else i
  else
    i

theorem chooseLargest_le_children (a : List Int) (n i : Nat) :
    let L := chooseLargest a n i
    (2 * i + 1 < n → a[2 * i + 1]! ≤ a[L]!) ∧
      (2 * i + 2 < n → a[2 * i + 2]! ≤ a[L]!) ∧
        a[i]! ≤ a[L]! ∧
          (L = i ∨ (L = 2 * i + 1 ∧ 2 * i + 1 < n) ∨ (L = 2 * i + 2 ∧ 2 * i + 2 < n)) := by
  unfold chooseLargest
  by_cases hl : 2 * i + 1 < n
  · by_cases hr : 2 * i + 2 < n
    · by_cases hli : a[i]! < a[2 * i + 1]!
      · by_cases hri : a[2 * i + 1]! < a[2 * i + 2]!
        · rw [if_pos hl, if_pos hr, if_pos hli, if_pos hri]
          refine ⟨?_, ?_, ?_, Or.inr (Or.inr ⟨rfl, hr⟩)⟩
          · intro _; exact le_of_lt hri
          · intro _; exact le_refl _
          · exact le_of_lt (lt_trans hli hri)
        · rw [if_pos hl, if_pos hr, if_pos hli, if_neg hri]
          refine ⟨?_, ?_, ?_, Or.inr (Or.inl ⟨rfl, hl⟩)⟩
          · intro _; exact le_refl _
          · intro _; exact not_lt.mp hri
          · exact le_of_lt hli
      · by_cases hri : a[i]! < a[2 * i + 2]!
        · rw [if_pos hl, if_pos hr, if_neg hli, if_pos hri]
          refine ⟨?_, ?_, ?_, Or.inr (Or.inr ⟨rfl, hr⟩)⟩
          · intro _; exact le_trans (not_lt.mp hli) (le_of_lt hri)
          · intro _; exact le_refl _
          · exact le_of_lt hri
        · rw [if_pos hl, if_pos hr, if_neg hli, if_neg hri]
          refine ⟨?_, ?_, le_refl _, Or.inl rfl⟩
          · intro _; exact not_lt.mp hli
          · intro _; exact not_lt.mp hri
    · by_cases hli : a[i]! < a[2 * i + 1]!
      · rw [if_pos hl, if_neg hr, if_pos hli]
        refine ⟨?_, ?_, ?_, Or.inr (Or.inl ⟨rfl, hl⟩)⟩
        · intro _; exact le_refl _
        · intro hbad; exact (hr hbad).elim
        · exact le_of_lt hli
      · rw [if_pos hl, if_neg hr, if_neg hli]
        refine ⟨?_, ?_, le_refl _, Or.inl rfl⟩
        · intro _; exact not_lt.mp hli
        · intro hbad; exact (hr hbad).elim
  · rw [if_neg hl]
    refine ⟨?_, ?_, le_refl _, Or.inl rfl⟩
    · intro hbad; exact (hl hbad).elim
    · intro hbad; omega
