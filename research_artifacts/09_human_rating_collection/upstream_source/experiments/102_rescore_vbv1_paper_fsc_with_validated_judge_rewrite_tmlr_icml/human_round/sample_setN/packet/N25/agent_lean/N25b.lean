import Mathlib

/-!
# Heap sort formalized in Lean 4

This file formalizes the Python `heap_sort` program:

* a purely functional implementation (`heapSort`) of the heap sort algorithm
  for `List Int`, built from `siftDown` (the Python `heapify`), `buildHeap` and
  the extraction loop, operating on `Array Int`;
* unit tests, property-based tests, and a full correctness proof: the output is
  sorted and is a permutation of the input;
* an imperative implementation (`heapSortImperative`) using `Id.run do` with
  mutable state, together with a proof that it agrees with the functional one.

The Python precondition (`pre`) only rules out non-`int` elements; since the
Lean function is typed `List Int → List Int`, that precondition is modelled as
the trivially-true predicate `Pre`.
-/

namespace heap_sort

/-- Swap two elements of an integer array; if either index is out of bounds the
array is returned unchanged (a total version of `Array.swap`). -/
def swapArr (a : Array Int) (i j : Nat) : Array Int :=
  if h : i < a.size ∧ j < a.size then a.swap i j h.1 h.2 else a

theorem size_swapArr (a : Array Int) (i j : Nat) : (swapArr a i j).size = a.size := by
  unfold swapArr
  split
  · exact Array.size_swap
  · rfl

theorem swapArr_eq_of_lt {a : Array Int} {i j : Nat} (hi : i < a.size) (hj : j < a.size) :
    swapArr a i j = a.swap i j hi hj := by
  unfold swapArr
  rw [dif_pos ⟨hi, hj⟩]

theorem getElem!_swapArr (a : Array Int) (i j k : Nat) (hi : i < a.size) (hj : j < a.size) :
    (swapArr a i j)[k]! = if k = i then a[j]! else if k = j then a[i]! else a[k]! := by
  rw [swapArr_eq_of_lt hi hj]
  by_cases hki : k = i
  · rw [hki]
    rw [getElem!_pos (a.swap i j hi hj) i (by rw [Array.size_swap]; exact hi),
      Array.getElem_swap_left, getElem!_pos a j hj]
    simp
  · by_cases hkj : k = j
    · rw [hkj] at hki ⊢
      rw [getElem!_pos (a.swap i j hi hj) j (by rw [Array.size_swap]; exact hj),
        Array.getElem_swap_right, getElem!_pos a i hi]
      simp [hki]
    · by_cases hk : k < a.size
      · rw [getElem!_pos (a.swap i j hi hj) k (by rw [Array.size_swap]; exact hk),
          getElem!_pos a k hk, Array.getElem_swap_of_ne hk hki hkj]
        simp [hki, hkj]
      · rw [getElem!_neg (a.swap i j hi hj) k (by rw [Array.size_swap]; exact hk),
          getElem!_neg a k hk]
        simp [hki, hkj]

/-- Swapping a single position of a list against a new value is a permutation. -/
theorem cons_set_perm {α : Type} (l : List α) (t : Nat) (ht : t < l.length) (v : α) :
    (l[t] :: l.set t v).Perm (v :: l) := by
  rw [List.set_eq_take_cons_drop v ht]
  have hl : l = l.take t ++ l[t] :: l.drop (t + 1) := by
    conv_lhs => rw [← List.set_getElem_self ht, List.set_eq_take_cons_drop _ ht]
  conv_rhs => rw [hl]
  have h1 : (l.take t ++ v :: l.drop (t + 1)).Perm (v :: (l.take t ++ l.drop (t + 1))) :=
    List.perm_middle
  have h2 : (l.take t ++ l[t] :: l.drop (t + 1)).Perm (l[t] :: (l.take t ++ l.drop (t + 1))) :=
    List.perm_middle
  exact ((List.Perm.cons _ h1).trans (List.Perm.swap _ _ _)).trans (List.Perm.cons _ h2.symm)

/-- Writing the swapped pair of elements back into a list is a permutation. -/
theorem set_set_swap_perm {α : Type} (l : List α) (i j : Nat)
    (hi : i < l.length) (hj : j < l.length) :
    ((l.set i l[j]).set j l[i]).Perm l := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons x l ih =>
    cases i with
    | zero =>
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.getElem_cons_succ, List.set_cons_zero, List.getElem_cons_zero,
          List.set_cons_succ]
        exact cons_set_perm l j (by simpa using hj) x
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, List.set_cons_succ, List.getElem_cons_succ,
          List.set_cons_zero]
        exact cons_set_perm l i (by simpa using hi) x
      | succ j =>
        simp only [List.getElem_cons_succ, List.set_cons_succ]
        exact List.Perm.cons x (ih i j (by simpa using hi) (by simpa using hj))

theorem toList_swapArr (a : Array Int) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (swapArr a i j).toList =
      (a.toList.set i (a.toList[j]'(by rw [Array.length_toList]; exact hj))).set j
        (a.toList[i]'(by rw [Array.length_toList]; exact hi)) := by
  have hv : a[j] = a.toList[j]'(by rw [Array.length_toList]; exact hj) :=
    (Array.getElem_toList hj).symm
  have hw : a[i] = a.toList[i]'(by rw [Array.length_toList]; exact hi) :=
    (Array.getElem_toList hi).symm
  rw [swapArr_eq_of_lt hi hj, Array.swap_def, Array.toList_set, Array.toList_set, hv, hw]

theorem perm_swapArr (a : Array Int) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (swapArr a i j).toList.Perm a.toList := by
  rw [toList_swapArr a i j hi hj]
  exact set_set_swap_perm _ _ _ _ _

/-- Restore the max-heap property at node `i` within the first `n` elements of `a`,
assuming both subtrees below `i` already satisfy the heap property.  This is the
Python `heapify`: it compares node `i` with its two children, swaps with the larger
child when needed, and recurses. -/
def siftDown (a : Array Int) (n i : Nat) : Array Int :=
  if h : 2 * i + 1 < n then
    if h2 : 2 * i + 2 < n ∧ a[2 * i + 2]! > a[2 * i + 1]! then
      if a[2 * i + 2]! > a[i]! then
        siftDown (swapArr a i (2 * i + 2)) n (2 * i + 2)
      else a
    else
      if a[2 * i + 1]! > a[i]! then
        siftDown (swapArr a i (2 * i + 1)) n (2 * i + 1)
      else a
  else a
termination_by n - i
decreasing_by all_goals omega


theorem size_siftDown (a : Array Int) (n i : Nat) : (siftDown a n i).size = a.size := by
  fun_induction siftDown a n i
  case case1 a i h h2 h3 ih => rw [ih, size_swapArr]
  case case3 a i h h2 h3 ih => rw [ih, size_swapArr]
  case case2 => rfl
  case case4 => rfl
  case case5 => rfl

/-- `siftDown` does not touch positions strictly above its root. -/
theorem siftDown_unchanged_lt {a : Array Int} {n i k : Nat} (hn : n ≤ a.size)
    (hk : k < i) : (siftDown a n i)[k]! = a[k]! := by
  fun_induction siftDown a n i
  case case1 a i h h2 h3 ih =>
    rw [ih (by rw [size_swapArr]; exact hn) (by omega),
      getElem!_swapArr a i (2 * i + 2) k (by omega) (by omega)]
    simp [show k ≠ i by omega, show k ≠ 2 * i + 2 by omega]
  case case3 a i h h2 h3 ih =>
    rw [ih (by rw [size_swapArr]; exact hn) (by omega),
      getElem!_swapArr a i (2 * i + 1) k (by omega) (by omega)]
    simp [show k ≠ i by omega, show k ≠ 2 * i + 1 by omega]
  case case2 => rfl
  case case4 => rfl
  case case5 => rfl

/-- `siftDown` does not touch positions at or beyond the heap size `n`. -/
theorem siftDown_unchanged_ge {a : Array Int} {n i k : Nat} (hn : n ≤ a.size)
    (hk : n ≤ k) : (siftDown a n i)[k]! = a[k]! := by
  fun_induction siftDown a n i
  case case1 a i h h2 h3 ih =>
    rw [ih (by rw [size_swapArr]; exact hn),
      getElem!_swapArr a i (2 * i + 2) k (by omega) (by omega)]
    simp [show k ≠ i by omega, show k ≠ 2 * i + 2 by omega]
  case case3 a i h h2 h3 ih =>
    rw [ih (by rw [size_swapArr]; exact hn),
      getElem!_swapArr a i (2 * i + 1) k (by omega) (by omega)]
    simp [show k ≠ i by omega, show k ≠ 2 * i + 1 by omega]
  case case2 => rfl
  case case4 => rfl
  case case5 => rfl

/-- After `siftDown`, the value at the root is either the original value there or the
value of one of its two (in-bounds) children. -/
theorem siftDown_root_mem {a : Array Int} {n i : Nat} (hn : n ≤ a.size) :
    (siftDown a n i)[i]! = a[i]! ∨
      ∃ m, (m = 2 * i + 1 ∨ m = 2 * i + 2) ∧ m < n ∧ (siftDown a n i)[i]! = a[m]! := by
  fun_induction siftDown a n i
  case case1 a i h h2 h3 _ih =>
    right
    refine ⟨2 * i + 2, Or.inr rfl, h2.1, ?_⟩
    rw [siftDown_unchanged_lt (by rw [size_swapArr]; exact hn) (by omega),
      getElem!_swapArr a i (2 * i + 2) i (by omega) (by omega)]
    simp
  case case3 a i h h2 h3 _ih =>
    right
    refine ⟨2 * i + 1, Or.inl rfl, h, ?_⟩
    rw [siftDown_unchanged_lt (by rw [size_swapArr]; exact hn) (by omega),
      getElem!_swapArr a i (2 * i + 1) i (by omega) (by omega)]
    simp
  case case2 => exact Or.inl rfl
  case case4 => exact Or.inl rfl
  case case5 => exact Or.inl rfl

/-- `siftDown` preserves pointwise upper bounds over the heap region. -/
theorem siftDown_le {a : Array Int} {n i : Nat} {B : Int} (hn : n ≤ a.size)
    (hB : ∀ k, k < n → a[k]! ≤ B) : ∀ k, k < n → (siftDown a n i)[k]! ≤ B := by
  fun_induction siftDown a n i
  case case1 a i h h2 h3 ih =>
    intro k hkn
    have hB' : ∀ m, m < n → (swapArr a i (2 * i + 2))[m]! ≤ B := by
      intro m hm
      rw [getElem!_swapArr a i (2 * i + 2) m (by omega) (by omega)]
      by_cases hmi : m = i
      · rw [if_pos hmi]; exact hB _ h2.1
      · by_cases hmr : m = 2 * i + 2
        · rw [if_neg hmi, if_pos hmr]; exact hB _ (by omega)
        · rw [if_neg hmi, if_neg hmr]; exact hB _ hm
    exact ih (by rw [size_swapArr]; exact hn) hB' k hkn
  case case3 a i h h2 h3 ih =>
    intro k hkn
    have hB' : ∀ m, m < n → (swapArr a i (2 * i + 1))[m]! ≤ B := by
      intro m hm
      rw [getElem!_swapArr a i (2 * i + 1) m (by omega) (by omega)]
      by_cases hmi : m = i
      · rw [if_pos hmi]; exact hB _ h
      · by_cases hmr : m = 2 * i + 1
        · rw [if_neg hmi, if_pos hmr]; exact hB _ (by omega)
        · rw [if_neg hmi, if_neg hmr]; exact hB _ hm
    exact ih (by rw [size_swapArr]; exact hn) hB' k hkn
  case case2 => exact hB
  case case4 => exact hB
  case case5 => exact hB

/-- `Reaches i k` holds when `k` lies in the subtree rooted at `i`: following the
binary-heap parent map `j ↦ (j - 1) / 2` from `k` eventually reaches `i`. -/
def Reaches (i k : Nat) : Prop :=
  if k = 0 then i = 0 else k = i ∨ Reaches i ((k - 1) / 2)
termination_by k
decreasing_by omega

theorem Reaches.self (i : Nat) : Reaches i i := by
  rw [Reaches.eq_def]
  by_cases h : i = 0
  · simp [h]
  · simp [h]

theorem Reaches.ge {i k : Nat} (h : Reaches i k) : i ≤ k := by
  fun_induction Reaches i k
  case case1 => omega
  case case2 k hk ih =>
    rcases h with rfl | h'
    · exact le_refl _
    · have := ih h'
      omega

theorem Reaches.parent {i k : Nat} (h : Reaches i k) (hne : k ≠ i) : Reaches i ((k - 1) / 2) := by
  rw [Reaches.eq_def] at h
  by_cases hk : k = 0
  · subst hk
    simp at h
    subst h
    exact absurd rfl hne
  · rw [if_neg hk] at h
    rcases h with rfl | h'
    · exact absurd rfl hne
    · exact h'

theorem Reaches.of_parent {i k : Nat} (hk : 0 < k) (h : Reaches i ((k - 1) / 2)) :
    Reaches i k := by
  rw [Reaches.eq_def, if_neg (by omega)]
  exact Or.inr h

theorem Reaches.trans {a b c : Nat} (h1 : Reaches a b) (h2 : Reaches b c) : Reaches a c := by
  fun_induction Reaches b c
  case case1 =>
    subst h2
    have h3 : a = 0 := by
      have := Reaches.ge h1
      omega
    subst h3
    exact Reaches.self 0
  case case2 c hc ih =>
    rcases h2 with rfl | h2'
    · exact h1
    · exact Reaches.of_parent (by omega) (ih h2')

theorem Reaches.child_left (i : Nat) : Reaches i (2 * i + 1) := by
  apply Reaches.of_parent (by omega)
  rw [show (2 * i + 1 - 1) / 2 = i by omega]
  exact Reaches.self i

theorem Reaches.child_right (i : Nat) : Reaches i (2 * i + 2) := by
  apply Reaches.of_parent (by omega)
  rw [show (2 * i + 2 - 1) / 2 = i by omega]
  exact Reaches.self i

/-- `siftDown` does not touch positions outside the subtree of its root. -/
theorem siftDown_unchanged_out {a : Array Int} {n i k : Nat} (hn : n ≤ a.size)
    (hk : ¬ Reaches i k) : (siftDown a n i)[k]! = a[k]! := by
  fun_induction siftDown a n i
  case case1 a i h h2 h3 ih =>
    have hnm : ¬ Reaches (2 * i + 2) k := fun hr => hk (Reaches.trans (Reaches.child_right i) hr)
    rw [ih (by rw [size_swapArr]; exact hn) hnm,
      getElem!_swapArr a i (2 * i + 2) k (by omega) (by omega)]
    have hki : k ≠ i := fun hke => hk (by rw [hke]; exact Reaches.self i)
    have hkm : k ≠ 2 * i + 2 := fun hke => hk (by rw [hke]; exact Reaches.child_right i)
    simp [hki, hkm]
  case case3 a i h h2 h3 ih =>
    have hnm : ¬ Reaches (2 * i + 1) k := fun hr => hk (Reaches.trans (Reaches.child_left i) hr)
    rw [ih (by rw [size_swapArr]; exact hn) hnm,
      getElem!_swapArr a i (2 * i + 1) k (by omega) (by omega)]
    have hki : k ≠ i := fun hke => hk (by rw [hke]; exact Reaches.self i)
    have hkm : k ≠ 2 * i + 1 := fun hke => hk (by rw [hke]; exact Reaches.child_left i)
    simp [hki, hkm]
  case case2 => rfl
  case case4 => rfl
  case case5 => rfl

/-- The max-heap property restricted to parents `p ≥ i`: every such node is at least
as large as each of its children within the first `n` elements. -/
def IsHeapFrom (a : Array Int) (n i : Nat) : Prop :=
  ∀ p j : Nat, i ≤ p → (j = 2 * p + 1 ∨ j = 2 * p + 2) → j < n → a[j]! ≤ a[p]!

/-- The key lemma: if all parents below `i` satisfy the heap property, then after
`siftDown` at `i`, all parents from `i` downwards satisfy it. -/
theorem siftDown_heap {a : Array Int} {n i : Nat} (hn : n ≤ a.size)
    (hpre : IsHeapFrom a n (i + 1)) : IsHeapFrom (siftDown a n i) n i := by
  fun_induction siftDown a n i
  case case1 a i h h2 h3 ih =>
    have hpre' : IsHeapFrom (swapArr a i (2 * i + 2)) n (2 * i + 2 + 1) := by
      intro q j' hq hj' hj'n
      rw [getElem!_swapArr a i (2 * i + 2) j' (by omega) (by omega),
        getElem!_swapArr a i (2 * i + 2) q (by omega) (by omega),
        if_neg (show j' ≠ i by omega), if_neg (show j' ≠ 2 * i + 2 by omega),
        if_neg (show q ≠ i by omega), if_neg (show q ≠ 2 * i + 2 by omega)]
      exact hpre q j' (by omega) hj' hj'n
    have hres := ih (by rw [size_swapArr]; exact hn) hpre'
    have hRi : (siftDown (swapArr a i (2 * i + 2)) n (2 * i + 2))[i]! = a[2 * i + 2]! := by
      rw [siftDown_unchanged_lt (by rw [size_swapArr]; exact hn) (by omega),
        getElem!_swapArr a i (2 * i + 2) i (by omega) (by omega)]
      simp
    have hRl : (siftDown (swapArr a i (2 * i + 2)) n (2 * i + 2))[2 * i + 1]! = a[2 * i + 1]! := by
      rw [siftDown_unchanged_lt (by rw [size_swapArr]; exact hn) (by omega),
        getElem!_swapArr a i (2 * i + 2) (2 * i + 1) (by omega) (by omega),
        if_neg (show (2 * i + 1) ≠ i by omega), if_neg (show (2 * i + 1) ≠ 2 * i + 2 by omega)]
    have hRm : (siftDown (swapArr a i (2 * i + 2)) n (2 * i + 2))[2 * i + 2]! ≤ a[2 * i + 2]! := by
      rcases siftDown_root_mem (a := swapArr a i (2 * i + 2)) (n := n) (i := 2 * i + 2)
          (hn := by rw [size_swapArr]; exact hn) with hr | ⟨c, hc, hcn, hr⟩
      · rw [hr, getElem!_swapArr a i (2 * i + 2) (2 * i + 2) (by omega) (by omega)]
        simp [show ¬(2 * i + 2 = i) by omega]
        omega
      · rw [hr, getElem!_swapArr a i (2 * i + 2) c (by omega) (by omega),
          if_neg (show c ≠ i by omega), if_neg (show c ≠ 2 * i + 2 by omega)]
        exact hpre (2 * i + 2) c (by omega) hc hcn
    intro p j hp hj hjn
    by_cases hpm : 2 * i + 2 ≤ p
    · exact hres p j hpm hj hjn
    · by_cases hpi : p = i
      · rcases hj with rfl | rfl <;> rw [hpi]
        · rw [hRl, hRi]
          omega
        · rw [hRi]
          exact hRm
      · have hRp : (siftDown (swapArr a i (2 * i + 2)) n (2 * i + 2))[p]! = a[p]! := by
          rw [siftDown_unchanged_lt (by rw [size_swapArr]; exact hn) (by omega),
            getElem!_swapArr a i (2 * i + 2) p (by omega) (by omega),
            if_neg (show p ≠ i by omega), if_neg (show p ≠ 2 * i + 2 by omega)]
        have hRj : (siftDown (swapArr a i (2 * i + 2)) n (2 * i + 2))[j]! = a[j]! := by
          have hnr : ¬ Reaches (2 * i + 2) j := by
            intro hr
            have hjm : j ≠ 2 * i + 2 := by omega
            have hparent := Reaches.parent hr hjm
            have hpar : (j - 1) / 2 = p := by omega
            rw [hpar] at hparent
            have := Reaches.ge hparent
            omega
          rw [siftDown_unchanged_out (by rw [size_swapArr]; exact hn) hnr,
            getElem!_swapArr a i (2 * i + 2) j (by omega) (by omega),
            if_neg (show j ≠ i by omega), if_neg (show j ≠ 2 * i + 2 by omega)]
        rw [hRp, hRj]
        exact hpre p j (by omega) hj hjn
  case case3 a i h h2 h3 ih =>
    have hpre' : IsHeapFrom (swapArr a i (2 * i + 1)) n (2 * i + 1 + 1) := by
      intro q j' hq hj' hj'n
      rw [getElem!_swapArr a i (2 * i + 1) j' (by omega) (by omega),
        getElem!_swapArr a i (2 * i + 1) q (by omega) (by omega),
        if_neg (show j' ≠ i by omega), if_neg (show j' ≠ 2 * i + 1 by omega),
        if_neg (show q ≠ i by omega), if_neg (show q ≠ 2 * i + 1 by omega)]
      exact hpre q j' (by omega) hj' hj'n
    have hres := ih (by rw [size_swapArr]; exact hn) hpre'
    have hRi : (siftDown (swapArr a i (2 * i + 1)) n (2 * i + 1))[i]! = a[2 * i + 1]! := by
      rw [siftDown_unchanged_lt (by rw [size_swapArr]; exact hn) (by omega),
        getElem!_swapArr a i (2 * i + 1) i (by omega) (by omega)]
      simp
    have hRr : (siftDown (swapArr a i (2 * i + 1)) n (2 * i + 1))[2 * i + 2]! = a[2 * i + 2]! := by
      have hnr : ¬ Reaches (2 * i + 1) (2 * i + 2) := by
        intro hr
        have hne : (2 * i + 2) ≠ (2 * i + 1) := by omega
        have hparent := Reaches.parent hr hne
        have hpar : (2 * i + 2 - 1) / 2 = i := by omega
        rw [hpar] at hparent
        have := Reaches.ge hparent
        omega
      rw [siftDown_unchanged_out (by rw [size_swapArr]; exact hn) hnr,
        getElem!_swapArr a i (2 * i + 1) (2 * i + 2) (by omega) (by omega),
        if_neg (show (2 * i + 2) ≠ i by omega), if_neg (show (2 * i + 2) ≠ 2 * i + 1 by omega)]
    have hRm : (siftDown (swapArr a i (2 * i + 1)) n (2 * i + 1))[2 * i + 1]! ≤ a[2 * i + 1]! := by
      rcases siftDown_root_mem (a := swapArr a i (2 * i + 1)) (n := n) (i := 2 * i + 1)
          (hn := by rw [size_swapArr]; exact hn) with hr | ⟨c, hc, hcn, hr⟩
      · rw [hr, getElem!_swapArr a i (2 * i + 1) (2 * i + 1) (by omega) (by omega)]
        simp [show ¬(2 * i + 1 = i) by omega]
        omega
      · rw [hr, getElem!_swapArr a i (2 * i + 1) c (by omega) (by omega),
          if_neg (show c ≠ i by omega), if_neg (show c ≠ 2 * i + 1 by omega)]
        exact hpre (2 * i + 1) c (by omega) hc hcn
    intro p j hp hj hjn
    by_cases hpm : 2 * i + 1 ≤ p
    · exact hres p j hpm hj hjn
    · by_cases hpi : p = i
      · rcases hj with rfl | rfl <;> rw [hpi] at hjn ⊢
        · rw [hRi]
          exact hRm
        · rw [hRr, hRi]
          have h2' : ¬ a[2 * i + 2]! > a[2 * i + 1]! := fun hc => h2 ⟨hjn, hc⟩
          omega
      · have hRp : (siftDown (swapArr a i (2 * i + 1)) n (2 * i + 1))[p]! = a[p]! := by
          rw [siftDown_unchanged_lt (by rw [size_swapArr]; exact hn) (by omega),
            getElem!_swapArr a i (2 * i + 1) p (by omega) (by omega),
            if_neg (show p ≠ i by omega), if_neg (show p ≠ 2 * i + 1 by omega)]
        have hRj : (siftDown (swapArr a i (2 * i + 1)) n (2 * i + 1))[j]! = a[j]! := by
          have hnr : ¬ Reaches (2 * i + 1) j := by
            intro hr
            have hjm : j ≠ 2 * i + 1 := by omega
            have hparent := Reaches.parent hr hjm
            have hpar : (j - 1) / 2 = p := by omega
            rw [hpar] at hparent
            have := Reaches.ge hparent
            omega
          rw [siftDown_unchanged_out (by rw [size_swapArr]; exact hn) hnr,
            getElem!_swapArr a i (2 * i + 1) j (by omega) (by omega),
            if_neg (show j ≠ i by omega), if_neg (show j ≠ 2 * i + 1 by omega)]
        rw [hRp, hRj]
        exact hpre p j (by omega) hj hjn
  case case2 a i h h2 h3 =>
    intro p j hp hj hjn
    by_cases hpi : p = i
    · rcases hj with rfl | rfl <;> rw [hpi] <;> omega
    · exact hpre p j (by omega) hj hjn
  case case4 a i h h2 h3 =>
    intro p j hp hj hjn
    by_cases hpi : p = i
    · rcases hj with rfl | rfl
      · rw [hpi]; omega
      · rw [hpi] at hjn ⊢
        have h2' : ¬ a[2 * i + 2]! > a[2 * i + 1]! := fun hc => h2 ⟨hjn, hc⟩
        omega
    · exact hpre p j (by omega) hj hjn
  case case5 a i h =>
    intro p j hp hj hjn
    by_cases hpi : p = i
    · rcases hj with rfl | rfl <;> omega
    · exact hpre p j (by omega) hj hjn

/-- `siftDown` only swaps elements, so it produces a permutation of its input. -/
theorem perm_siftDown {a : Array Int} {n i : Nat} (hn : n ≤ a.size) :
    (siftDown a n i).toList.Perm a.toList := by
  fun_induction siftDown a n i
  case case1 a i h h2 h3 ih =>
    exact (ih (by rw [size_swapArr]; exact hn)).trans (perm_swapArr a i (2 * i + 2) (by omega) (by omega))
  case case3 a i h h2 h3 ih =>
    exact (ih (by rw [size_swapArr]; exact hn)).trans (perm_swapArr a i (2 * i + 1) (by omega) (by omega))
  case case2 => exact .refl _
  case case4 => exact .refl _
  case case5 => exact .refl _

/-- Build a max heap by sifting down every non-leaf node from the last one up to the
root (Python's `build_max_heap`). -/
def buildHeap (a : Array Int) : Array Int :=
  (List.range (a.size / 2)).reverse.foldl (fun b i => siftDown b b.size i) a

/-- The extraction loop of heap sort: repeatedly swap the root (the maximum) with the
last element of the current heap and sift the new root down. -/
def extractAll (a : Array Int) : Array Int :=
  (List.range' 1 (a.size - 1)).reverse.foldl (fun b j => siftDown (swapArr b 0 j) j 0) a

/-- Heap sort on arrays: build a max heap, then extract the maximum repeatedly. -/
def heapSortArr (a : Array Int) : Array Int :=
  extractAll (buildHeap a)

/-- Heap sort for a list of integers (the Python `heap_sort`). -/
def heapSort (xs : List Int) : List Int :=
  (heapSortArr xs.toArray).toList

theorem size_fold_sift (is : List Nat) (a : Array Int) :
    (is.foldl (fun b i => siftDown b b.size i) a).size = a.size := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih => rw [List.foldl_cons, ih, size_siftDown]

theorem size_fold_extract (is : List Nat) (a : Array Int) :
    (is.foldl (fun b j => siftDown (swapArr b 0 j) j 0) a).size = a.size := by
  induction is generalizing a with
  | nil => rfl
  | cons j is ih => rw [List.foldl_cons, ih, size_siftDown, size_swapArr]

theorem size_buildHeap (a : Array Int) : (buildHeap a).size = a.size := size_fold_sift _ _

theorem size_heapSortArr (a : Array Int) : (heapSortArr a).size = a.size := by
  rw [heapSortArr, extractAll, size_fold_extract, size_buildHeap]

/-- Nodes beyond `n / 2` are leaves, so the heap property holds vacuously there. -/
theorem IsHeapFrom_vac {a : Array Int} {n i : Nat} (h : n / 2 ≤ i) : IsHeapFrom a n i := by
  intro p j hp hj hjn
  omega

/-- In a max heap (from 0), the root is a maximum of the first `n` elements. -/
theorem root_max {a : Array Int} {n : Nat} (h : IsHeapFrom a n 0) (p : Nat) (hp : p < n) :
    a[p]! ≤ a[0]! := by
  induction p using Nat.strong_induction_on
  next p ih =>
    by_cases hp0 : p = 0
    · subst hp0
      exact le_refl _
    · have hq : (p - 1) / 2 < p := by omega
      have h1 := ih _ hq (by omega)
      have h2 : a[p]! ≤ a[(p - 1) / 2]! := h ((p - 1) / 2) p (Nat.zero_le _) (by omega) hp
      exact le_trans h2 h1

/-- Sifting down the nodes `k - 1, ..., 0` (in that order) establishes the heap property
from 0, given it already holds from `k`. -/
theorem IsHeapFrom_fold_sift (a : Array Int) (k : Nat) (h : IsHeapFrom a a.size k) :
    IsHeapFrom ((List.range k).reverse.foldl (fun b i => siftDown b b.size i) a) a.size 0 := by
  revert h
  induction k generalizing a with
  | zero =>
    intro h
    exact h
  | succ k ih =>
    intro h
    have e : (List.range (k + 1)).reverse = k :: (List.range k).reverse := by
      rw [show k + 1 = Nat.succ k from rfl, List.range_succ, List.reverse_append]
      simp
    rw [e, List.foldl_cons]
    have h1 : IsHeapFrom (siftDown a a.size k) a.size k := siftDown_heap (le_refl _) h
    have h2 := ih (siftDown a a.size k) (by rwa [size_siftDown])
    rwa [size_siftDown] at h2

theorem buildHeap_heap (a : Array Int) : IsHeapFrom (buildHeap a) a.size 0 := by
  rw [buildHeap]
  exact IsHeapFrom_fold_sift a (a.size / 2) (IsHeapFrom_vac (le_refl _))

/-- Correctness of the extraction loop: starting from a max heap of size `n + 1` with an
already-sorted tail at positions `≥ n + 1` that dominates the heap, after repeatedly
moving the maximum to the end the whole array is sorted. -/
theorem extract_sorted (n : Nat) (a : Array Int) (hn : n + 1 ≤ a.size)
    (hheap : IsHeapFrom a (n + 1) 0)
    (htail : ∀ x y, n + 1 ≤ x → x < y → y < a.size → a[x]! ≤ a[y]!)
    (hsep : ∀ p q, p < n + 1 → n + 1 ≤ q → q < a.size → a[p]! ≤ a[q]!) :
    ∀ x y, x < y → y < ((List.range' 1 n).reverse.foldl
        (fun b j => siftDown (swapArr b 0 j) j 0) a).size →
      ((List.range' 1 n).reverse.foldl (fun b j => siftDown (swapArr b 0 j) j 0) a)[x]! ≤
      ((List.range' 1 n).reverse.foldl (fun b j => siftDown (swapArr b 0 j) j 0) a)[y]! := by
  induction n generalizing a with
  | zero =>
    intro x y hxy hy
    have e : (List.range' 1 0).reverse.foldl (fun b j => siftDown (swapArr b 0 j) j 0) a = a := rfl
    rw [e] at hy ⊢
    by_cases hx : x = 0
    · rw [hx]
      exact hsep 0 y (by omega) (by omega) hy
    · exact htail x y (by omega) hxy hy
  | succ n ih =>
    have e : (List.range' 1 (n + 1)).reverse = (n + 1) :: (List.range' 1 n).reverse := by
      have h1 : List.range' 1 (n + 1) = List.range' 1 n ++ [n + 1] := by
        rw [← List.range'_append, show (1 : Nat) + 1 * n = n + 1 by omega]
        rfl
      rw [h1, List.reverse_append]
      simp
    rw [e, List.foldl_cons]
    have hs0 : 0 < a.size := by omega
    have hs1 : n + 1 < a.size := by omega
    have hsz1 : (swapArr a 0 (n + 1)).size = a.size := size_swapArr _ _ _
    have hheap1 : IsHeapFrom (swapArr a 0 (n + 1)) (n + 1) 1 := by
      intro p j hp hj hjn
      by_cases hp1 : p = n + 1
      · rcases hj with rfl | rfl <;> omega
      · rw [getElem!_swapArr a 0 (n + 1) p hs0 hs1, getElem!_swapArr a 0 (n + 1) j hs0 hs1,
          if_neg (show p ≠ 0 by omega), if_neg hp1,
          if_neg (show j ≠ 0 by omega), if_neg (show j ≠ n + 1 by omega)]
        exact hheap p j (Nat.zero_le _) hj (by omega)
    have hheap2 : IsHeapFrom (siftDown (swapArr a 0 (n + 1)) (n + 1) 0) (n + 1) 0 :=
      siftDown_heap (by rw [hsz1]; omega) hheap1
    have htail1 : ∀ x y, n + 1 ≤ x → x < y →
        y < (siftDown (swapArr a 0 (n + 1)) (n + 1) 0).size →
        (siftDown (swapArr a 0 (n + 1)) (n + 1) 0)[x]! ≤
        (siftDown (swapArr a 0 (n + 1)) (n + 1) 0)[y]! := by
      intro x y hx hxy hy
      rw [size_siftDown, hsz1] at hy
      rw [siftDown_unchanged_ge (by rw [hsz1]; omega) hx,
        siftDown_unchanged_ge (by rw [hsz1]; omega) (by omega : n + 1 ≤ y)]
      by_cases hx1 : x = n + 1
      · rw [hx1, getElem!_swapArr a 0 (n + 1) (n + 1) hs0 hs1, if_neg (by omega), if_pos rfl,
          getElem!_swapArr a 0 (n + 1) y hs0 hs1, if_neg (by omega), if_neg (by omega)]
        exact hsep 0 y (by omega) (by omega) (by omega)
      · rw [getElem!_swapArr a 0 (n + 1) x hs0 hs1, getElem!_swapArr a 0 (n + 1) y hs0 hs1,
          if_neg (by omega), if_neg hx1, if_neg (by omega), if_neg (by omega)]
        exact htail x y (by omega) hxy hy
    have hsep1 : ∀ p q, p < n + 1 → n + 1 ≤ q →
        q < (siftDown (swapArr a 0 (n + 1)) (n + 1) 0).size →
        (siftDown (swapArr a 0 (n + 1)) (n + 1) 0)[p]! ≤
        (siftDown (swapArr a 0 (n + 1)) (n + 1) 0)[q]! := by
      intro p q hp hq hq'
      rw [size_siftDown, hsz1] at hq'
      have hbound : ∀ k, k < n + 1 → (swapArr a 0 (n + 1))[k]! ≤ a[0]! := by
        intro k hk
        rw [getElem!_swapArr a 0 (n + 1) k hs0 hs1]
        by_cases hk0 : k = 0
        · rw [if_pos hk0]
          exact root_max hheap (n + 1) (by omega)
        · rw [if_neg hk0, if_neg (by omega)]
          exact root_max hheap k (by omega)
      have hp_le : (siftDown (swapArr a 0 (n + 1)) (n + 1) 0)[p]! ≤ a[0]! :=
        siftDown_le (by rw [hsz1]; omega) hbound p hp
      rw [siftDown_unchanged_ge (by rw [hsz1]; omega) hq]
      by_cases hq1 : q = n + 1
      · rw [hq1, getElem!_swapArr a 0 (n + 1) (n + 1) hs0 hs1, if_neg (by omega), if_pos rfl]
        exact hp_le
      · rw [getElem!_swapArr a 0 (n + 1) q hs0 hs1, if_neg (by omega), if_neg hq1]
        exact le_trans hp_le (hsep 0 q (by omega) (by omega) hq')
    exact ih _ (by rw [size_siftDown, hsz1]; omega) hheap2 htail1 hsep1

/-- The output of `heapSortArr` is pointwise non-decreasing. -/
theorem sorted_heapSortArr (a : Array Int) :
    ∀ x y, x < y → y < (heapSortArr a).size → (heapSortArr a)[x]! ≤ (heapSortArr a)[y]! := by
  by_cases h0 : a.size = 0
  · intro x y hxy hy
    simp [heapSortArr, extractAll, buildHeap, h0] at hy
  · have hs : 1 ≤ a.size := by omega
    rw [heapSortArr, extractAll, size_buildHeap]
    apply extract_sorted (a.size - 1) (buildHeap a) (by rw [size_buildHeap]; omega)
    · rw [show a.size - 1 + 1 = a.size by omega]
      exact buildHeap_heap a
    · intro x y hx hxy hy
      rw [size_buildHeap] at hy
      omega
    · intro p q hp hq hq'
      rw [size_buildHeap] at hq'
      omega

/-- Bridge from pointwise order on an array to `List.Sorted` of its `toList`. -/
theorem sorted_toList_of_pairwise {a : Array Int}
    (h : ∀ x y, x < y → y < a.size → a[x]! ≤ a[y]!) : a.toList.Sorted (· ≤ ·) := by
  show a.toList.Pairwise (· ≤ ·)
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [Array.length_toList] at hi hj
  rw [Array.getElem_toList, Array.getElem_toList]
  rw [← getElem!_pos a i hi, ← getElem!_pos a j hj]
  exact h i j hij hj

theorem perm_fold_sift (is : List Nat) (a : Array Int) :
    (is.foldl (fun b i => siftDown b b.size i) a).toList.Perm a.toList := by
  induction is generalizing a with
  | nil => exact .refl _
  | cons i is ih =>
    rw [List.foldl_cons]
    exact (ih _).trans (perm_siftDown (le_refl _))

theorem perm_fold_extract (is : List Nat) (a : Array Int)
    (h : ∀ j ∈ is, 0 < j ∧ j < a.size) :
    (is.foldl (fun b j => siftDown (swapArr b 0 j) j 0) a).toList.Perm a.toList := by
  revert h
  induction is generalizing a with
  | nil =>
    intro h
    exact .refl _
  | cons j is ih =>
    intro h
    rw [List.foldl_cons]
    have hj := h j List.mem_cons_self
    have h1 : (swapArr a 0 j).toList.Perm a.toList := perm_swapArr a 0 j (by omega) (by omega)
    have h2 : (siftDown (swapArr a 0 j) j 0).toList.Perm (swapArr a 0 j).toList :=
      perm_siftDown (by rw [size_swapArr]; omega)
    apply (ih _ _).trans (h2.trans h1)
    intro k hk
    have := h k (List.mem_cons_of_mem _ hk)
    rwa [size_siftDown, size_swapArr]

theorem perm_buildHeap (a : Array Int) : (buildHeap a).toList.Perm a.toList := perm_fold_sift _ _

theorem perm_heapSortArr (a : Array Int) : (heapSortArr a).toList.Perm a.toList := by
  rw [heapSortArr, extractAll, size_buildHeap]
  exact (perm_fold_extract _ (buildHeap a) (by
    intro j hj
    rw [List.mem_reverse, List.mem_range'] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    constructor
    · omega
    · rw [size_buildHeap]
      omega)).trans (perm_buildHeap a)

theorem sorted_heapSort (xs : List Int) : (heapSort xs).Sorted (· ≤ ·) := by
  rw [heapSort]
  apply sorted_toList_of_pairwise
  intro x y hxy hy
  exact sorted_heapSortArr _ x y hxy hy

theorem perm_heapSort (xs : List Int) : (heapSort xs).Perm xs := by
  rw [heapSort]
  exact (perm_heapSortArr xs.toArray).trans (by rw [List.toList_toArray])

/-- Boolean sortedness check (executable, used for property-based tests). -/
def sortedB : List Int → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (a ≤ b) && sortedB (b :: t)

/-- Boolean permutation check (executable, used for property-based tests). -/
def permB (xs ys : List Int) : Bool := decide (xs.Perm ys)

/-! ## Unit tests (mirroring the Python `check` function) -/

example : heapSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : heapSort [] = ([] : List Int) := by native_decide
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
example : heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
    = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

-- Negative Python test (`heap_sort [1, 2.5]` raising `ValueError`): not modelled here,
-- because `heapSort` is typed `List Int → List Int`, so non-integer elements are already
-- excluded by the type system (see `Pre`).

#eval heapSort [3, 1, 2]
#eval heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

/-! ## Precondition, properties, postcondition -/

/-- The Python precondition `pre`: `isinstance(arr, list) and all(isinstance(x, int) for x in arr)`.
In Lean the input is typed `List Int`, so the precondition is always satisfied; the only
Python inputs it rejects (non-integer elements) are inexpressible at this type. -/
def Pre (_arr : List Int) : Prop := True

/-- Sortedness property: the output is non-decreasing. -/
def sorted_prop (arr : List Int) : Prop := (heapSort arr).Sorted (· ≤ ·)

/-- Permutation property: the output is a permutation of the input. -/
def perm_prop (arr : List Int) : Prop := (heapSort arr).Perm arr

/-- Length preservation property (implied by `perm_prop`, kept separate as in the Python
specification `len(arr) <= 1` returns a copy of the same length). -/
def len_prop (arr : List Int) : Prop := (heapSort arr).length = arr.length

theorem sorted_thm (arr : List Int) : sorted_prop arr := sorted_heapSort arr

theorem perm_thm (arr : List Int) : perm_prop arr := perm_heapSort arr

theorem len_thm (arr : List Int) : len_prop arr := (perm_heapSort arr).length_eq

/-- Post-condition: the conjunction of the properties. -/
def Post_prop (arr : List Int) : Prop :=
  sorted_prop arr ∧ perm_prop arr ∧ len_prop arr

/-! ## Property-based tests -/

/-- All lists over a fixed alphabet of a given exact length. -/
def allLists (alphabet : List Int) : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (allLists alphabet n).flatMap fun xs => alphabet.map (· :: xs)

/-- All lists over a fixed alphabet of length at most `n`. -/
def allListsUpTo (alphabet : List Int) (n : Nat) : List (List Int) :=
  ((List.range (n + 1)).map (allLists alphabet)).flatten

-- Bounded PBT: exhaustive small cases for sortedness.
example : (allListsUpTo [-1, 0, 1, 2] 5).all (fun xs => sortedB (heapSort xs)) = true := by
  native_decide

-- Bounded PBT: exhaustive small cases for the permutation property.
example : (allListsUpTo [-1, 0, 1, 2] 5).all (fun xs => permB xs (heapSort xs)) = true := by
  native_decide

-- Bounded PBT: exhaustive small cases for the full post-condition (sorted, permutation,
-- same length).
example : (allListsUpTo [0, 1] 7).all (fun xs =>
    sortedB (heapSort xs) && permB xs (heapSort xs)
      && decide ((heapSort xs).length = xs.length)) = true := by
  native_decide

-- Randomized PBT (Plausible): sortedness on random integer lists.
#eval Plausible.Testable.check (∀ xs : List Int, sortedB (heapSort xs) = true)

-- Randomized PBT (Plausible): permutation property on random integer lists.
#eval Plausible.Testable.check (∀ xs : List Int, xs.Perm (heapSort xs))

-- Randomized PBT (Plausible): full post-condition on random integer lists.
#eval Plausible.Testable.check (∀ xs : List Int,
  sortedB (heapSort xs) = true ∧ xs.Perm (heapSort xs) ∧ (heapSort xs).length = xs.length)

/-! ## Correctness theorem: `Pre → Post` -/

theorem heapSort_correct (arr : List Int) (_h : Pre arr) : Post_prop arr :=
  ⟨sorted_thm arr, perm_thm arr, len_thm arr⟩

/-! ## Imperative implementation -/

/-- Heap sort using `Id.run do` with mutable state: the same algorithm as `heapSort`,
written with mutable variables and `for` loops (mirroring the Python in-place loops). -/
def heapSortImperative (xs : List Int) : List Int := Id.run do
  let mut a := xs.toArray
  for i in (List.range (a.size / 2)).reverse do
    a := siftDown a a.size i
  for j in (List.range' 1 (a.size - 1)).reverse do
    a := swapArr a 0 j
    a := siftDown a j 0
  return a.toList

/-! ## Imperative tests -/

example : heapSortImperative [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSortImperative [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapSortImperative [2, 1, 3] = [1, 2, 3] := by native_decide
example : heapSortImperative [] = ([] : List Int) := by native_decide
example : heapSortImperative [1] = [1] := by native_decide
example : heapSortImperative [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSortImperative [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapSortImperative [2, 1] = [1, 2] := by native_decide
example : heapSortImperative [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : heapSortImperative [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : heapSortImperative [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : heapSortImperative [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapSortImperative [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
    = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

#eval heapSortImperative [3, 1, 2]

/-! ## Equivalence of the functional and imperative implementations -/

/-- `bind` in the `Id` monad is just application. -/
theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

/-- `pure` in the `Id` monad is the identity. -/
theorem id_pure {α : Type} (x : α) : (pure x : Id α) = x := rfl

/-- A `for` loop over a list in the `Id` monad whose body only updates the loop state is
a left fold. -/
theorem forIn_list_id {α β : Type} (xs : List α) (init : β) (f : β → α → β) :
    (forIn xs init (fun x b => ForInStep.yield (f b x)) : Id β) = xs.foldl f init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, List.foldl_cons, ← ih, id_bind]

theorem heapSortImperative_eq_heapSort (xs : List Int) :
    heapSortImperative xs = heapSort xs := by
  unfold heapSortImperative heapSort heapSortArr buildHeap extractAll
  simp only [Id.run, id_bind, id_pure]
  rw [forIn_list_id, forIn_list_id]

-- Executable check of the equivalence on small inputs.
example : (allListsUpTo [0, 1, 2] 5).all (fun xs =>
    decide (heapSortImperative xs = heapSort xs)) = true := by native_decide

end heap_sort





