import Mathlib

/-!
# Heapsort (CLRS 6.4)

0-based max-heap heapsort on lists of natural numbers.
The functional implementation follows the Python program: `parent`, `left`,
`right`, in-place `maxHeapify`, `buildMaxHeap`, then the extraction loop.
The result is a nondecreasing permutation of the input.
-/

namespace heapsort_algorithm

/-! ## Index arithmetic -/

/-- Parent of index `i` in a 0-based binary heap. `parent 0 = 0`. -/
def parent (i : Nat) : Nat :=
  if i = 0 then 0 else (i - 1) / 2

/-- Left child of index `i`. -/
def left (i : Nat) : Nat := 2 * i + 1

/-- Right child of index `i`. -/
def right (i : Nat) : Nat := 2 * i + 2

theorem parent_eq_div {i : Nat} (h : i ≠ 0) : parent i = (i - 1) / 2 := by
  simp [parent, h]

theorem parent_lt {i : Nat} (h : i ≠ 0) : parent i < i := by
  rw [parent_eq_div h]
  have : (i - 1) / 2 ≤ i - 1 := Nat.div_le_self _ _
  omega

theorem parent_left (i : Nat) : parent (left i) = i := by
  unfold parent left
  simp

theorem parent_right (i : Nat) : parent (right i) = i := by
  have hne : right i ≠ 0 := by unfold right; omega
  rw [parent_eq_div hne]
  have hr : right i - 1 = 2 * i + 1 := by unfold right; omega
  rw [hr]
  exact Nat.div_eq_of_lt_le (n := 2) (k := i) (m := 2 * i + 1) (by omega) (by omega)

theorem left_gt (i : Nat) : i < left i := by
  unfold left
  omega

theorem right_gt (i : Nat) : i < right i := by
  unfold right
  omega

theorem eq_left_or_right (j : Nat) (hj : j ≠ 0) :
    j = left (parent j) ∨ j = right (parent j) := by
  rw [parent_eq_div hj]
  unfold left right
  have hmod : (j - 1) % 2 = 0 ∨ (j - 1) % 2 = 1 := by
    have : (j - 1) % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have hdiv : j - 1 = 2 * ((j - 1) / 2) + (j - 1) % 2 := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod (j - 1) 2).symm
  rcases hmod with h0 | h1 <;> omega

/-! ## Subtree membership -/

/-- `inSubtree root idx` holds when `idx` lies in the heap subtree rooted at `root`. -/
def inSubtree (root idx : Nat) : Bool :=
  if idx < root then
    false
  else if idx = root then
    true
  else
    inSubtree root (parent idx)
termination_by idx
decreasing_by
  simp_wf
  exact parent_lt (by omega)

theorem inSubtree_of_lt {root idx : Nat} (h : idx < root) : inSubtree root idx = false := by
  rw [inSubtree.eq_def]
  simp [h]

theorem inSubtree_self (root : Nat) : inSubtree root root = true := by
  rw [inSubtree.eq_def]
  simp

theorem inSubtree_parent {root idx : Nat} (h : root < idx) :
    inSubtree root idx = inSubtree root (parent idx) := by
  rw [inSubtree.eq_def]
  simp [show ¬ idx < root by omega, show idx ≠ root by omega]

theorem inSubtree_le {root idx : Nat} (h : inSubtree root idx = true) : root ≤ idx := by
  by_cases hlt : idx < root
  · simp [inSubtree_of_lt hlt] at h
  · omega

theorem inSubtree_zero (j : Nat) : inSubtree 0 j = true := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    rw [inSubtree.eq_def]
    by_cases hj : j = 0
    · simp [hj]
    · have hlt : parent j < j := parent_lt hj
      simp [show ¬ j < 0 by omega, hj, ih (parent j) hlt]

theorem inSubtree_of_parent {root j : Nat} (hroot : root < j)
    (hp : inSubtree root (parent j) = true) : inSubtree root j = true := by
  rw [inSubtree_parent hroot]
  exact hp

theorem inSubtree_left_self (i : Nat) : inSubtree i (left i) = true := by
  rw [inSubtree_parent (left_gt i), parent_left, inSubtree_self]

theorem inSubtree_right_self (i : Nat) : inSubtree i (right i) = true := by
  rw [inSubtree_parent (right_gt i), parent_right, inSubtree_self]

theorem inSubtree_left_desc {i j : Nat} (h : inSubtree i j = true) :
    inSubtree i (left j) = true := by
  have hlt : i < left j := by
    have hij : i ≤ j := inSubtree_le h
    unfold left
    omega
  rw [inSubtree_parent hlt, parent_left]
  exact h

theorem inSubtree_right_desc {i j : Nat} (h : inSubtree i j = true) :
    inSubtree i (right j) = true := by
  have hlt : i < right j := by
    have hij : i ≤ j := inSubtree_le h
    unfold right
    omega
  rw [inSubtree_parent hlt, parent_right]
  exact h

theorem inSubtree_child_of (i j : Nat) (h : inSubtree (left i) j = true) :
    inSubtree i j = true := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    if hlt : j < left i then
      simp [inSubtree_of_lt hlt] at h
    else
      have hge : left i ≤ j := Nat.le_of_not_lt hlt
      if heq : j = left i then
        rw [heq, inSubtree_left_self]
      else
        have hgt : left i < j := Nat.lt_of_le_of_ne hge (Ne.symm heq)
        have hpar : inSubtree (left i) (parent j) = true := by
          rw [← inSubtree_parent hgt]
          exact h
        have hp : parent j < j := parent_lt (by omega)
        have ihp : inSubtree i (parent j) = true := ih (parent j) hp hpar
        have hj : i < j := by
          have : i < left i := left_gt i
          omega
        rw [inSubtree_parent hj]
        exact ihp

theorem inSubtree_child_of_right (i j : Nat) (h : inSubtree (right i) j = true) :
    inSubtree i j = true := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    if hlt : j < right i then
      simp [inSubtree_of_lt hlt] at h
    else
      have hge : right i ≤ j := Nat.le_of_not_lt hlt
      if heq : j = right i then
        rw [heq, inSubtree_right_self]
      else
        have hgt : right i < j := Nat.lt_of_le_of_ne hge (Ne.symm heq)
        have hpar : inSubtree (right i) (parent j) = true := by
          rw [← inSubtree_parent hgt]
          exact h
        have hp : parent j < j := parent_lt (by omega)
        have ihp : inSubtree i (parent j) = true := ih (parent j) hp hpar
        have hj : i < j := by
          have : i < right i := right_gt i
          omega
        rw [inSubtree_parent hj]
        exact ihp

theorem not_inSubtree_right_of_left (i j : Nat) :
    inSubtree (left i) j = true → inSubtree (right i) j = false := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hL
    if hlt : j < right i then
      rw [inSubtree.eq_def]
      simp [hlt]
    else if heq : j = right i then
      have hnot : inSubtree (left i) (right i) = false := by
        rw [inSubtree_parent (by unfold left right; omega), parent_right]
        exact inSubtree_of_lt (by unfold left; omega)
      simp [heq, hnot] at hL
    else
      have hgt : right i < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
      have hLj : left i < j := by
        have : left i < right i := by unfold left right; omega
        omega
      have hLp : inSubtree (left i) (parent j) = true := by
        rw [← inSubtree_parent hLj]
        exact hL
      have hp : parent j < j := parent_lt (by omega)
      rw [inSubtree_parent hgt]
      exact ih (parent j) hp hLp

theorem not_inSubtree_left_of_right (i j : Nat) :
    inSubtree (right i) j = true → inSubtree (left i) j = false := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hR
    if hlt : j < left i then
      rw [inSubtree.eq_def]
      simp [hlt]
    else if heq : j = left i then
      have hnot : inSubtree (right i) (left i) = false := by
        exact inSubtree_of_lt (by unfold left right; omega)
      simp [heq, hnot] at hR
    else
      if heqR : j = right i then
        subst heqR
        rw [inSubtree_parent (by unfold left right; omega), parent_right]
        exact inSubtree_of_lt (left_gt i)
      else
        have hgt : left i < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
        have hgtR : right i < j := by
          have hstep : right i = left i + 1 := by unfold left right; omega
          omega
        have hp : parent j < j := parent_lt (by omega)
        have hRp : inSubtree (right i) (parent j) = true := by
          rw [← inSubtree_parent hgtR]
          exact hR
        rw [inSubtree_parent hgt]
        exact ih (parent j) hp hRp

theorem inSubtree_trichotomy (i j : Nat) :
    inSubtree i j = true ↔
      j = i ∨ inSubtree (left i) j = true ∨ inSubtree (right i) j = true := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    constructor
    · intro h
      if hlt : j < i then
        simp [inSubtree_of_lt hlt] at h
      else if heq : j = i then
        exact Or.inl heq
      else
        have hgt : i < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
        have hpar : inSubtree i (parent j) = true := by
          rw [← inSubtree_parent hgt]
          exact h
        have hp : parent j < j := parent_lt (by omega)
        have ihp := (ih (parent j) hp).1 hpar
        rcases ihp with hroot | hsub
        · rcases eq_left_or_right j (by omega) with hl | hr
          · exact Or.inr (Or.inl (by rw [hl, hroot]; exact inSubtree_self _))
          · exact Or.inr (Or.inr (by rw [hr, hroot]; exact inSubtree_self _))
        · rcases hsub with hl | hr
          · have hltj : left i < j := by
              have : left i ≤ parent j := inSubtree_le hl
              omega
            exact Or.inr (Or.inl (inSubtree_of_parent hltj hl))
          · have hltj : right i < j := by
              have : right i ≤ parent j := inSubtree_le hr
              omega
            exact Or.inr (Or.inr (inSubtree_of_parent hltj hr))
    · intro h
      rcases h with hji | hl | hr
      · rw [hji]; exact inSubtree_self _
      · exact inSubtree_child_of i j hl
      · exact inSubtree_child_of_right i j hr
/-! ## Array access and swaps -/

theorem getD_of_lt {a : Array Nat} {i : Nat} (h : i < a.size) : a.getD i 0 = a[i] := by
  simp [Array.getD, h]

theorem getD_of_ge {a : Array Nat} {i : Nat} (h : a.size ≤ i) : a.getD i 0 = 0 := by
  simp [Array.getD, show ¬ i < a.size by omega]

theorem swapIfInBounds_eq_swap (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    a.swapIfInBounds i j = a.swap i j hi hj := by
  simp [Array.swapIfInBounds, hi, hj]

theorem getD_swap_eq_left (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (a.swapIfInBounds i j).getD i 0 = a.getD j 0 := by
  rw [swapIfInBounds_eq_swap a i j hi hj]
  have hi' : i < (a.swap i j hi hj).size := by
    simpa only [Array.size_swap] using hi
  rw [getD_of_lt hi', getD_of_lt hj, Array.getElem_swap hi hj hi']
  simp

theorem getD_swap_eq_right (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (a.swapIfInBounds i j).getD j 0 = a.getD i 0 := by
  rw [swapIfInBounds_eq_swap a i j hi hj]
  have hj' : j < (a.swap i j hi hj).size := by
    simpa only [Array.size_swap] using hj
  rw [getD_of_lt hj', getD_of_lt hi, Array.getElem_swap hi hj hj']
  by_cases hij : j = i
  · simp [hij]
  · simp [hij]

theorem getD_swap_eq_of_ne (a : Array Nat) (i j k : Nat) (hi : i < a.size) (hj : j < a.size)
    (hki : k ≠ i) (hkj : k ≠ j) :
    (a.swapIfInBounds i j).getD k 0 = a.getD k 0 := by
  rw [swapIfInBounds_eq_swap a i j hi hj]
  by_cases hk : k < a.size
  · have hk' : k < (a.swap i j hi hj).size := by
      simpa only [Array.size_swap] using hk
    rw [getD_of_lt hk', getD_of_lt hk, Array.getElem_swap hi hj hk']
    simp [hki, hkj]
  · rw [getD_of_ge (by omega : a.size ≤ k)]
    have hk' : (a.swap i j hi hj).size ≤ k := by
      simpa only [Array.size_swap] using (show a.size ≤ k by omega)
    rw [getD_of_ge hk']

theorem swapIfInBounds_perm (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    Array.Perm (a.swapIfInBounds i j) a := by
  rw [swapIfInBounds_eq_swap a i j hi hj]
  exact Array.swap_perm hi hj

/-! ## Choosing the largest child -/

/-- Index of the largest value among `i` and its children that lie inside the heap. -/
def chooseLargest (a : Array Nat) (i heapSize : Nat) : Nat :=
  if left i < heapSize ∧ a.getD (left i) 0 > a.getD i 0 then
    if right i < heapSize ∧ a.getD (right i) 0 > a.getD (left i) 0 then
      right i
    else
      left i
  else if right i < heapSize ∧ a.getD (right i) 0 > a.getD i 0 then
    right i
  else
    i

theorem chooseLargest_ne_gt (a : Array Nat) (i heapSize : Nat)
    (h : chooseLargest a i heapSize ≠ i) : i < chooseLargest a i heapSize := by
  unfold chooseLargest at h ⊢
  by_cases hL : left i < heapSize ∧ a.getD (left i) 0 > a.getD i 0
  · rw [if_pos hL] at h ⊢
    by_cases hR : right i < heapSize ∧ a.getD (right i) 0 > a.getD (left i) 0
    · rw [if_pos hR] at h ⊢
      exact right_gt i
    · rw [if_neg hR] at h ⊢
      exact left_gt i
  · rw [if_neg hL] at h ⊢
    by_cases hR : right i < heapSize ∧ a.getD (right i) 0 > a.getD i 0
    · rw [if_pos hR] at h ⊢
      exact right_gt i
    · rw [if_neg hR] at h ⊢
      exact absurd rfl h

theorem chooseLargest_spec (a : Array Nat) (i heapSize : Nat) (hi : i < heapSize) :
    chooseLargest a i heapSize < heapSize ∧
    (chooseLargest a i heapSize = i ∨
      chooseLargest a i heapSize = left i ∨
      chooseLargest a i heapSize = right i) ∧
    a.getD i 0 ≤ a.getD (chooseLargest a i heapSize) 0 ∧
    (left i < heapSize → a.getD (left i) 0 ≤ a.getD (chooseLargest a i heapSize) 0) ∧
    (right i < heapSize → a.getD (right i) 0 ≤ a.getD (chooseLargest a i heapSize) 0) := by
  unfold chooseLargest
  split
  · next hL =>
    split
    · next hR =>
      refine ⟨hR.1, Or.inr (Or.inr rfl), ?_, ?_, ?_⟩
      · exact Nat.le_trans (Nat.le_of_lt hL.2) (Nat.le_of_lt hR.2)
      · intro _; exact Nat.le_of_lt hR.2
      · intro _; exact Nat.le_refl _
    · next hR =>
      refine ⟨hL.1, Or.inr (Or.inl rfl), Nat.le_of_lt hL.2, ?_, ?_⟩
      · intro _; exact Nat.le_refl _
      · intro hr
        have hnot : ¬ a.getD (left i) 0 < a.getD (right i) 0 := by
          intro hlt
          exact hR ⟨hr, hlt⟩
        exact Nat.not_lt.mp hnot
  · next hL =>
    split
    · next hR =>
      refine ⟨hR.1, Or.inr (Or.inr rfl), Nat.le_of_lt hR.2, ?_, ?_⟩
      · intro hl
        have hnot : ¬ a.getD i 0 < a.getD (left i) 0 := by
          intro hlt
          exact hL ⟨hl, hlt⟩
        exact Nat.le_trans (Nat.not_lt.mp hnot) (Nat.le_of_lt hR.2)
      · intro _; exact Nat.le_refl _
    · next hR =>
      refine ⟨hi, Or.inl rfl, Nat.le_refl _, ?_, ?_⟩
      · intro hl
        have hnot : ¬ a.getD i 0 < a.getD (left i) 0 := by
          intro hlt
          exact hL ⟨hl, hlt⟩
        exact Nat.not_lt.mp hnot
      · intro hr
        have hnot : ¬ a.getD i 0 < a.getD (right i) 0 := by
          intro hlt
          exact hR ⟨hr, hlt⟩
        exact Nat.not_lt.mp hnot

/-! ## Max-heapify -/

/-- Restore the max-heap property at index `i` inside a heap of length `heapSize`. -/
def maxHeapify (a : Array Nat) (i heapSize : Nat) : Array Nat :=
  if h : i < heapSize ∧ heapSize ≤ a.size then
    if hl : chooseLargest a i heapSize = i then
      a
    else
      maxHeapify (a.swapIfInBounds i (chooseLargest a i heapSize))
        (chooseLargest a i heapSize) heapSize
  else
    a
termination_by heapSize - i
decreasing_by
  simp_wf
  have hgt : i < chooseLargest a i heapSize := chooseLargest_ne_gt a i heapSize hl
  omega

/-- A node is locally a max-heap parent for heap length `n`. -/
def heapOkAt (a : Array Nat) (n i : Nat) : Prop :=
  (left i < n → a.getD (left i) 0 ≤ a.getD i 0) ∧
  (right i < n → a.getD (right i) 0 ≤ a.getD i 0)

/-- Every index below `n` is a max-heap parent. -/
def IsMaxHeap (a : Array Nat) (n : Nat) : Prop :=
  ∀ i, i < n → heapOkAt a n i

theorem subtree_ge (a : Array Nat) (n root j : Nat)
    (hheap : ∀ i, i < n → inSubtree root i = true → heapOkAt a n i)
    (hj : j < n) (hsub : inSubtree root j = true) :
    a.getD j 0 ≤ a.getD root 0 := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    if heq : j = root then
      simp [heq]
    else
      have hlt : root < j := by
        have := inSubtree_le hsub
        omega
      have hpSub : inSubtree root (parent j) = true := by
        rw [← inSubtree_parent hlt]
        exact hsub
      have hpj : parent j < j := parent_lt (by omega)
      have hpn : parent j < n := Nat.lt_trans hpj hj
      have hok := hheap (parent j) hpn hpSub
      have hle : a.getD j 0 ≤ a.getD (parent j) 0 := by
        rcases eq_left_or_right j (by omega) with hl | hr
        · have hchild : left (parent j) < n := by
            rw [← hl]
            exact hj
          have hineq := hok.1 hchild
          rw [← hl] at hineq
          exact hineq
        · have hchild : right (parent j) < n := by
            rw [← hr]
            exact hj
          have hineq := hok.2 hchild
          rw [← hr] at hineq
          exact hineq
      exact Nat.le_trans hle (ih (parent j) hpj hpn hpSub)

theorem root_max {a : Array Nat} {n : Nat} (h : IsMaxHeap a n) {j : Nat} (hj : j < n) :
    a.getD j 0 ≤ a.getD 0 0 :=
  subtree_ge a n 0 j (fun i hi _ => h i hi) hj (inSubtree_zero j)

theorem maxHeapify_size (heapSize : Nat) (d : Nat) (a : Array Nat) (i : Nat)
    (hd : heapSize - i = d) : (maxHeapify a i heapSize).size = a.size := by
  induction d using Nat.strongRecOn generalizing a i with
  | ind d ih =>
    rw [maxHeapify.eq_def]
    split
    · next hpre =>
      split
      · rfl
      · next hl =>
        have hgt : i < chooseLargest a i heapSize := chooseLargest_ne_gt a i heapSize hl
        have hlt : heapSize - chooseLargest a i heapSize < d := by omega
        have ih' := ih (heapSize - chooseLargest a i heapSize) hlt
          (a.swapIfInBounds i (chooseLargest a i heapSize))
          (chooseLargest a i heapSize) rfl
        rw [Array.size_swapIfInBounds] at ih'
        exact ih'
    · rfl

theorem maxHeapify_outside (heapSize : Nat) (d : Nat) (a : Array Nat) (i j : Nat)
    (hd : heapSize - i = d) (hsub : inSubtree i j = false) :
    (maxHeapify a i heapSize).getD j 0 = a.getD j 0 := by
  induction d using Nat.strongRecOn generalizing a i with
  | ind d ih =>
    rw [maxHeapify.eq_def]
    split
    · next hpre =>
      split
      · rfl
      · next hl =>
        set L := chooseLargest a i heapSize with hLdef
        have hgt : i < L := chooseLargest_ne_gt a i heapSize hl
        have hlt : heapSize - L < d := by omega
        have hiS : i < a.size := Nat.lt_of_lt_of_le hpre.1 hpre.2
        have hLS : L < a.size := by
          have hLh : L < heapSize := (chooseLargest_spec a i heapSize hpre.1).1
          exact Nat.lt_of_lt_of_le hLh hpre.2
        have hLmem : L = i ∨ L = left i ∨ L = right i := by
          have hmem := (chooseLargest_spec a i heapSize hpre.1).2.1
          rwa [← hLdef] at hmem
        have hLin : inSubtree i L = true := by
          rcases hLmem with hI | hleft | hright
          · exact absurd hI hl
          · rw [hleft]; exact inSubtree_left_self i
          · rw [hright]; exact inSubtree_right_self i
        have hj_ne_i : j ≠ i := by
          intro hji
          rw [hji, inSubtree_self i] at hsub
          cases hsub
        have hj_ne_L : j ≠ L := by
          intro hjL
          rw [hjL, hLin] at hsub
          cases hsub
        have hnotL : inSubtree L j = false := by
          rcases hLmem with hI | hleft | hright
          · exact absurd hI hl
          · rw [hleft]
            cases hval : inSubtree (left i) j
            · rfl
            · have hcontr := inSubtree_child_of i j hval
              rw [hcontr] at hsub
              cases hsub
          · rw [hright]
            cases hval : inSubtree (right i) j
            · rfl
            · have hcontr := inSubtree_child_of_right i j hval
              rw [hcontr] at hsub
              cases hsub
        have hswap : (a.swapIfInBounds i L).getD j 0 = a.getD j 0 :=
          getD_swap_eq_of_ne a i L j hiS hLS hj_ne_i hj_ne_L
        have ih' := ih (heapSize - L) hlt (a.swapIfInBounds i L) L rfl hnotL
        exact ih'.trans hswap
    · rfl

theorem maxHeapify_suffix (heapSize : Nat) (d : Nat) (a : Array Nat) (i j : Nat)
    (hd : heapSize - i = d) (hj : heapSize ≤ j) :
    (maxHeapify a i heapSize).getD j 0 = a.getD j 0 := by
  induction d using Nat.strongRecOn generalizing a i with
  | ind d ih =>
    rw [maxHeapify.eq_def]
    split
    · next hpre =>
      split
      · rfl
      · next hl =>
        set L := chooseLargest a i heapSize
        have hgt : i < L := chooseLargest_ne_gt a i heapSize hl
        have hlt : heapSize - L < d := by omega
        have hiS : i < a.size := Nat.lt_of_lt_of_le hpre.1 hpre.2
        have hLh : L < heapSize := (chooseLargest_spec a i heapSize hpre.1).1
        have hLS : L < a.size := Nat.lt_of_lt_of_le hLh hpre.2
        have hne1 : j ≠ i := by omega
        have hne2 : j ≠ L := by omega
        have hswap := getD_swap_eq_of_ne a i L j hiS hLS hne1 hne2
        exact (ih (heapSize - L) hlt (a.swapIfInBounds i L) L rfl).trans hswap
    · rfl

theorem maxHeapify_perm (heapSize : Nat) (d : Nat) (a : Array Nat) (i : Nat)
    (hd : heapSize - i = d) : Array.Perm (maxHeapify a i heapSize) a := by
  induction d using Nat.strongRecOn generalizing a i with
  | ind d ih =>
    rw [maxHeapify.eq_def]
    split
    · next hpre =>
      split
      · exact Array.Perm.refl a
      · next hl =>
        set L := chooseLargest a i heapSize
        have hgt : i < L := chooseLargest_ne_gt a i heapSize hl
        have hlt : heapSize - L < d := by omega
        have hiS : i < a.size := Nat.lt_of_lt_of_le hpre.1 hpre.2
        have hLh : L < heapSize := (chooseLargest_spec a i heapSize hpre.1).1
        have hLS : L < a.size := Nat.lt_of_lt_of_le hLh hpre.2
        have hswap := swapIfInBounds_perm a i L hiS hLS
        have hrec := ih (heapSize - L) hlt (a.swapIfInBounds i L) L rfl
        exact Array.Perm.trans hrec hswap
    · exact Array.Perm.refl a

theorem maxHeapify_le_bound (heapSize : Nat) (d : Nat) (a : Array Nat) (i : Nat) (B : Nat)
    (hd : heapSize - i = d) (hi : i < heapSize) (hs : heapSize ≤ a.size)
    (hB : ∀ j, j < heapSize → inSubtree i j = true → a.getD j 0 ≤ B) :
    ∀ j, j < heapSize → inSubtree i j = true → (maxHeapify a i heapSize).getD j 0 ≤ B := by
  induction d using Nat.strongRecOn generalizing a i with
  | ind d ih =>
    intro j hj hsub
    rw [maxHeapify.eq_def]
    split
    · next hpre =>
      split
      · exact hB j hj hsub
      · next hl =>
        set L := chooseLargest a i heapSize
        have hgt : i < L := chooseLargest_ne_gt a i heapSize hl
        have hltm : heapSize - L < d := by omega
        have spec0 := chooseLargest_spec a i heapSize hi
        have hLh : L < heapSize := spec0.1
        have hiS : i < a.size := Nat.lt_of_lt_of_le hi hs
        have hLS : L < a.size := Nat.lt_of_lt_of_le hLh hs
        have hLmem : L = i ∨ L = left i ∨ L = right i := spec0.2.1
        have hLin : inSubtree i L = true := by
          rcases hLmem with hI | hleft | hright
          · exact absurd hI hl
          · rw [hleft]; exact inSubtree_left_self i
          · rw [hright]; exact inSubtree_right_self i
        have hB1 : ∀ k, k < heapSize → inSubtree L k = true →
            (a.swapIfInBounds i L).getD k 0 ≤ B := by
          intro k hk hksub
          have hk_in_i : inSubtree i k = true := by
            rcases hLmem with hI | hleft | hright
            · exact absurd hI hl
            · rw [hleft] at hksub
              exact inSubtree_child_of i k hksub
            · rw [hright] at hksub
              exact inSubtree_child_of_right i k hksub
          have hk_ne_i : k ≠ i := by
            intro hki
            have hksub' : inSubtree L i = true := by
              rw [hki] at hksub
              exact hksub
            have : L ≤ i := inSubtree_le hksub'
            omega
          by_cases hkL : k = L
          · rw [hkL, getD_swap_eq_right a i L hiS hLS]
            exact hB i hi (inSubtree_self i)
          · rw [getD_swap_eq_of_ne a i L k hiS hLS hk_ne_i hkL]
            exact hB k hk hk_in_i
        have hs1 : heapSize ≤ (a.swapIfInBounds i L).size := by
          rw [Array.size_swapIfInBounds]
          exact hs
        have ih' := ih (heapSize - L) hltm (a.swapIfInBounds i L) L rfl hLh hs1 hB1
        by_cases hjL : inSubtree L j = true
        · exact ih' j hj hjL
        · have hjLf : inSubtree L j = false := by
            cases hval : inSubtree L j
            · rfl
            · exact absurd hval hjL
          have houtside := maxHeapify_outside heapSize (heapSize - L)
            (a.swapIfInBounds i L) L j rfl hjLf
          rw [houtside]
          by_cases hji : j = i
          · rw [hji, getD_swap_eq_left a i L hiS hLS]
            exact hB L hLh hLin
          · have hj_ne_L : j ≠ L := by
              intro hje
              apply hjL
              rw [hje]
              exact inSubtree_self L
            rw [getD_swap_eq_of_ne a i L j hiS hLS hji hj_ne_L]
            exact hB j hj hsub
    · exact hB j hj hsub

