import Mathlib

/-!
# Heapsort (CLRS §6.4, 0-based max-heap)

Formalization of the Python `heapsort` program (CLRS 6.4 with 0-based
max-heap arrays).  The development mirrors the Python code:

* `parent`, `left`, `right` — 0-based heap index arithmetic,
* `maxHeapify` — sift-down (`while` loop modeled with a fuel parameter,
  which is justified because the node index strictly increases and stays
  below the heap size),
* `buildMaxHeap` — heap construction from `parent (n-1)` down to `0`,
* `heapsort` — build-heap followed by repeated extraction of the maximum.

Contents:

* a functional implementation on `Array Nat` mirroring the Python in-place
  array algorithm,
* unit tests (the Python `check` assertions) via `native_decide` and `#eval`,
* the pre-condition `Pre`, property propositions and their theorems
  (sortedness, permutation, length preservation),
* the post-condition `Post_prop`, property-based tests, and the correctness
  theorem `Pre → Post`,
* an imperative implementation in `Id` with mutable state, and a proof that
  it coincides with the functional one.
-/

namespace heapsort_algorithm

open List

/-! ## Index arithmetic -/

/-- Parent index in a 0-based heap (as in the Python program). -/
def parent (i : Nat) : Nat := if i = 0 then 0 else (i - 1) / 2

/-- Left child index. -/
def left (i : Nat) : Nat := 2 * i + 1

/-- Right child index. -/
def right (i : Nat) : Nat := 2 * i + 2

lemma parent_eq (i : Nat) : parent i = (i - 1) / 2 := by
  unfold parent; split <;> omega

lemma parent_le (i : Nat) : parent i ≤ i := by rw [parent_eq]; omega

lemma parent_lt (i : Nat) (h : 0 < i) : parent i < i := by rw [parent_eq]; omega

lemma parent_left (i : Nat) : parent (left i) = i := by rw [parent_eq]; unfold left; omega

lemma parent_right (i : Nat) : parent (right i) = i := by rw [parent_eq]; unfold right; omega

lemma left_gt (i : Nat) : i < left i := by unfold left; omega

lemma right_gt (i : Nat) : i < right i := by unfold right; omega

lemma left_ne (i : Nat) : left i ≠ i := by unfold left; omega

lemma right_ne (i : Nat) : right i ≠ i := by unfold right; omega

lemma left_ne_right (i : Nat) : left i ≠ right i := by unfold left right; omega

/-- Every nonzero index is the left or the right child of its parent. -/
lemma eq_left_or_right_of_parent (j : Nat) (h : 0 < j) :
    j = left (parent j) ∨ j = right (parent j) := by
  rw [parent_eq]; unfold left right; omega

/-! ## Bounds-unchecked array access -/

/-- Read `a[i]`, returning `0` when out of bounds (total). -/
def getd (a : Array Nat) (i : Nat) : Nat := (a[i]?).getD 0

lemma getd_eq (a : Array Nat) (i : Nat) (h : i < a.size) : getd a i = a[i] := by
  simp only [getd, Array.getElem?_eq_getElem h, Option.getD_some]

lemma getd_ge (a : Array Nat) (i : Nat) (h : a.size ≤ i) : getd a i = 0 := by
  simp only [getd, Array.getElem?_eq_none h, Option.getD_none]

lemma getd_eq_toList (a : Array Nat) (i : Nat) (h : i < a.size) :
    getd a i = a.toList[i]'(by rw [Array.length_toList]; exact h) := by
  rw [getd_eq a i h, Array.getElem_toList]

/-- Swap entries `i` and `j`; no-op when either is out of bounds (total). -/
def swapd (a : Array Nat) (i j : Nat) : Array Nat :=
  if hi : i < a.size then
    if hj : j < a.size then
      (a.set i a[j] hi).set j a[i] (by rw [Array.size_set]; exact hj)
    else a
  else a

lemma size_swapd (a : Array Nat) (i j : Nat) : (swapd a i j).size = a.size := by
  simp only [swapd]
  split
  · split
    · rw [Array.size_set, Array.size_set]
    · rfl
  · rfl

lemma swapd_eq_swap (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    swapd a i j = a.swap i j hi hj := by
  simp only [swapd, dif_pos hi, dif_pos hj]
  rw [Array.swap_def]

lemma getd_swapd (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) (k : Nat) :
    getd (swapd a i j) k = if k = i then getd a j else if k = j then getd a i else getd a k := by
  by_cases hk : k < a.size
  · have hk' : k < (swapd a i j).size := by rw [size_swapd]; exact hk
    rw [getd_eq _ _ hk', getd_eq a i hi, getd_eq a j hj, getd_eq a k hk]
    simp only [swapd, dif_pos hi, dif_pos hj, Array.getElem_set]
    by_cases h1 : j = k
    · subst h1
      by_cases h2 : i = j
      · subst h2; simp
      · simp [h2, Ne.symm h2]
    · by_cases h2 : i = k
      · subst h2; simp [h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · rw [getd_ge _ _ (by rw [size_swapd]; omega)]
    by_cases hki : k = i
    · subst hki; exact absurd hi hk
    · by_cases hkj : k = j
      · subst hkj; exact absurd hj hk
      · rw [if_neg hki, if_neg hkj, getd_ge a k (by omega)]

/-! ## Swaps preserve the multiset of elements -/

lemma getElem_cons_set_perm (l : List Nat) (i : Nat) (h : i < l.length) (v : Nat) :
    l[i] :: l.set i v ~ v :: l := by
  induction i generalizing l with
  | zero =>
    cases l with
    | nil => simp at h
    | cons x t => exact List.Perm.swap _ _ _
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons x t =>
      have hi' : i < t.length := by
        have hl : (x :: t).length = t.length + 1 := rfl
        omega
      have e1 : (x :: t)[i + 1] = t[i] := rfl
      have e2 : (x :: t).set (i + 1) v = x :: t.set i v := rfl
      rw [e1, e2]
      calc t[i] :: (x :: t.set i v) ~ x :: (t[i] :: t.set i v) := List.Perm.swap _ _ _
        _ ~ x :: (v :: t) := List.Perm.cons x (ih t hi')
        _ ~ v :: (x :: t) := List.Perm.swap _ _ _

lemma set_set_swap_perm (l : List Nat) (i j : Nat) (hi : i < l.length) (hj : j < l.length) :
    ((l.set i l[j]).set j l[i]) ~ l := by
  by_cases hij : i = j
  · subst hij
    have h1 := getElem_cons_set_perm l i hi l[i]
    have h2 : l.set i l[i] ~ l := List.Perm.cons_inv h1
    have h3 : i < (l.set i l[i]).length := by rwa [List.length_set]
    have h4 := getElem_cons_set_perm (l.set i l[i]) i h3 l[i]
    have h5 : (l.set i l[i])[i]'h3 = l[i] := List.getElem_set_self h3
    rw [h5] at h4
    exact (List.Perm.cons_inv h4).trans h2
  · have hj' : j < (l.set i l[j]).length := by rwa [List.length_set]
    have h1 := getElem_cons_set_perm (l.set i l[j]) j hj' l[i]
    have h6 : (l.set i l[j])[j]'hj' = l[j] := List.getElem_set_ne hij hj'
    rw [h6] at h1
    have h2 := getElem_cons_set_perm l i hi l[j]
    exact List.Perm.cons_inv (h1.trans h2)

lemma set_set_swap_perm' (l : List Nat) (i j : Nat) (hi : i < l.length) (hj : j < l.length)
    (vi vj : Nat) (hvi : l[i] = vi) (hvj : l[j] = vj) :
    ((l.set i vj).set j vi) ~ l := by
  rw [← hvi, ← hvj]
  exact set_set_swap_perm l i j hi hj

lemma toList_swapd_perm (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (swapd a i j).toList ~ a.toList := by
  rw [swapd_eq_swap a i j hi hj, Array.swap_def, Array.toList_set, Array.toList_set]
  apply set_set_swap_perm' _ _ _ (by rw [Array.length_toList]; exact hi)
    (by rw [Array.length_toList]; exact hj)
  · exact Array.getElem_toList hi
  · exact Array.getElem_toList hj

/-! ## Functional implementation -/

/-- `maxHeapify` with explicit fuel: restores the max-heap property at node `i`
    in `a[0..n)`, assuming the subtrees rooted at `left i` and `right i` are
    already max-heaps.  Mirrors the Python `while` loop; the fuel `n - i + 1`
    always suffices because the current index strictly increases and stays
    below `n`. -/
def maxHeapifyF : Nat → Array Nat → Nat → Nat → Array Nat
  | 0, a, i, n => a
  | k + 1, a, i, n =>
    if left i < n ∧ getd a (left i) > getd a i then
      if right i < n ∧ getd a (right i) > getd a (left i) then
        maxHeapifyF k (swapd a i (right i)) (right i) n
      else
        maxHeapifyF k (swapd a i (left i)) (left i) n
    else
      if right i < n ∧ getd a (right i) > getd a i then
        maxHeapifyF k (swapd a i (right i)) (right i) n
      else
        a

/-- `max_heapify` from the Python program. -/
abbrev maxHeapify (a : Array Nat) (i n : Nat) : Array Nat :=
  maxHeapifyF (n - i + 1) a i n

/-- Loop of `build_max_heap`: heapify nodes `m-1, m-2, ..., 0`. -/
def buildLoop : Array Nat → Nat → Array Nat
  | a, 0 => a
  | a, m + 1 => buildLoop (maxHeapify a m a.size) m

/-- `build_max_heap` from the Python program. -/
def buildMaxHeap (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a else buildLoop a (parent (a.size - 1) + 1)

/-- Extraction loop of `heapsort`: for `i = m, m-1, ..., 1`, swap the root
    (the maximum of `a[0..i]`) into position `i` and restore the heap on
    `a[0..i)`. -/
def extractLoop : Array Nat → Nat → Array Nat
  | a, 0 => a
  | a, m + 1 => extractLoop (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)) m

/-- `heapsort` from the Python program. -/
def heapsort (xs : List Nat) : List Nat :=
  if xs.length ≤ 1 then xs
  else (extractLoop (buildMaxHeap xs.toArray) ((buildMaxHeap xs.toArray).size - 1)).toList

/-! ## Unit tests (mirroring the assertions of the Python `check`) -/

example : heapsort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsort [] = ([] : List Nat) := by native_decide
example : heapsort [42] = [42] := by native_decide
example : heapsort [2, 1] = [1, 2] := by native_decide
example : heapsort [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsort [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : heapsort [2, 1] ≠ [2, 1] := by native_decide

-- index arithmetic used by the algorithm
example : parent 0 = 0 := rfl
example : parent 1 = 0 := rfl
example : parent 2 = 0 := rfl
example : parent 3 = 1 := rfl
example : parent 4 = 1 := rfl
example : left 2 = 5 := rfl
example : right 2 = 6 := rfl

#eval heapsort [3, 1, 2]
#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsort ([] : List Nat)
#eval heapsort [7, 7, 7, 7]
#eval buildMaxHeap [3, 1, 2].toArray
#eval heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1]

/-! ## Pre-condition -/

/-- The Python `pre` accepts exactly the lists of natural numbers; in Lean the
    type `List Nat` already enforces this, so the predicate is trivially true
    (the full Python input domain is preserved). -/
def Pre (xs : List Nat) : Prop := True

/-! ## Heap invariant infrastructure -/

/-- `Desc i j` : `j` lies in the subtree rooted at `i` (0-based heap). -/
inductive Desc : Nat → Nat → Prop where
  | self {i : Nat} : Desc i i
  | ofLeft {i j : Nat} : Desc i j → Desc i (left j)
  | ofRight {i j : Nat} : Desc i j → Desc i (right j)

lemma desc_le {i j : Nat} (h : Desc i j) : i ≤ j := by
  induction h with
  | self => exact Nat.le_refl _
  | ofLeft h ih => unfold left; omega
  | ofRight h ih => unfold right; omega

lemma desc_trans {i j k : Nat} (h1 : Desc i j) (h2 : Desc j k) : Desc i k := by
  induction h2 with
  | self => exact h1
  | ofLeft h ih => exact Desc.ofLeft ih
  | ofRight h ih => exact Desc.ofRight ih

/-- The parent of a proper descendant is still a descendant. -/
lemma desc_peel {i j : Nat} (h : Desc i j) : j ≠ i → Desc i (parent j) := by
  induction h with
  | self => intro hne; exact absurd rfl hne
  | ofLeft h ih => intro _; rw [parent_left]; exact h
  | ofRight h ih => intro _; rw [parent_right]; exact h

/-- A proper descendant of `i` lies in the left or the right subtree. -/
lemma desc_cases {i j : Nat} (h : Desc i j) : j ≠ i → Desc (left i) j ∨ Desc (right i) j := by
  induction h
  case self =>
    intro hne; exact absurd rfl hne
  case ofLeft j h ih =>
    intro _
    by_cases hji : j = i
    · subst hji; exact Or.inl Desc.self
    · rcases ih hji with hl | hr
      · exact Or.inl (Desc.ofLeft hl)
      · exact Or.inr (Desc.ofLeft hr)
  case ofRight j h ih =>
    intro _
    by_cases hji : j = i
    · subst hji; exact Or.inr Desc.self
    · rcases ih hji with hl | hr
      · exact Or.inl (Desc.ofRight hl)
      · exact Or.inr (Desc.ofRight hr)

/-- Two nodes with a common descendant are comparable in the tree order. -/
lemma desc_cmp {i j k : Nat} (h1 : Desc i j) : Desc k j → Desc i k ∨ Desc k i := by
  induction h1
  case self =>
    intro h2; exact Or.inr h2
  case ofLeft j h ih =>
    intro h2
    by_cases hk : left j = k
    · subst hk; exact Or.inl (Desc.ofLeft h)
    · have hpeel := desc_peel h2 hk
      rw [parent_left] at hpeel
      exact ih hpeel
  case ofRight j h ih =>
    intro h2
    by_cases hk : right j = k
    · subst hk; exact Or.inl (Desc.ofRight h)
    · have hpeel := desc_peel h2 hk
      rw [parent_right] at hpeel
      exact ih hpeel

/-- Every node is in the subtree of the root `0`. -/
lemma desc_zero (j : Nat) : Desc 0 j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j = 0
    · subst hj; exact Desc.self
    · have hpos : 0 < j := Nat.pos_of_ne_zero hj
      have hp := ih (parent j) (parent_lt j hpos)
      rcases eq_left_or_right_of_parent j hpos with h | h
      · rw [h]; exact Desc.ofLeft hp
      · rw [h]; exact Desc.ofRight hp

lemma desc_right_left_false {i : Nat} (h : Desc (right i) (left i)) : False := by
  have hle := desc_le h
  unfold left right at hle; omega

lemma desc_left_right_false {i : Nat} (h : Desc (left i) (right i)) : False := by
  have hne : right i ≠ left i := by unfold left right; omega
  rcases desc_cases h hne with h1 | h1
  · have hle := desc_le h1
    unfold left right at hle; omega
  · have hle := desc_le h1
    unfold left right at hle; omega

/-- The left and right subtrees of a node are disjoint. -/
lemma desc_disjoint_lr {i j : Nat} (h1 : Desc (left i) j) (h2 : Desc (right i) j) : False := by
  rcases desc_cmp h1 h2 with h | h
  · exact desc_left_right_false h
  · exact desc_right_left_false h

lemma desc_disjoint_rl {i j : Nat} (h1 : Desc (right i) j) (h2 : Desc (left i) j) : False := by
  rcases desc_cmp h1 h2 with h | h
  · exact desc_right_left_false h
  · exact desc_left_right_false h

/-- Max-heap property restricted to the window `a[0..n)`: every proper
    descendant `j` of `i` inside the window satisfies
    `a[j] ≤ a[parent j]`. -/
def IsHeap (a : Array Nat) (n i : Nat) : Prop :=
  ∀ j : Nat, j < n → Desc i j → j ≠ i → getd a j ≤ getd a (parent j)

/-- All entries of the subtree of `i` within `a[0..n)` are at most `b`. -/
def Bounded (a : Array Nat) (n i b : Nat) : Prop :=
  ∀ j : Nat, j < n → Desc i j → getd a j ≤ b

lemma isHeap_eq_of_size {a : Array Nat} {s t : Nat} {i : Nat} (hst : s = t) (h : IsHeap a s i) :
    IsHeap a t i := by
  subst hst; exact h

/-- In a heap, the root is the maximum of its subtree (inside the window). -/
lemma isHeap_rootMax {a : Array Nat} {n i : Nat} (h : IsHeap a n i) (j : Nat) (hd : Desc i j) :
    j < n → getd a j ≤ getd a i := by
  induction hd
  case self => intro _; exact Nat.le_refl _
  case ofLeft k hdk ih =>
    intro hjn
    have hkn : k < n := by have := left_gt k; omega
    have h1 := ih hkn
    have h2 := h (left k) hjn (Desc.ofLeft hdk)
      (by have := desc_le hdk; unfold left; omega)
    rw [parent_left] at h2
    exact Nat.le_trans h2 h1
  case ofRight k hdk ih =>
    intro hjn
    have hkn : k < n := by have := right_gt k; omega
    have h1 := ih hkn
    have h2 := h (right k) hjn (Desc.ofRight hdk)
      (by have := desc_le hdk; unfold right; omega)
    rw [parent_right] at h2
    exact Nat.le_trans h2 h1

/-- A subtree of a heap is a heap. -/
lemma isHeap_sub {a : Array Nat} {n i j : Nat} (h : IsHeap a n i) (hd : Desc i j) :
    IsHeap a n j := by
  intro k hk hdk hne
  apply h k hk (desc_trans hd hdk)
  intro hki
  subst hki
  have h1 := desc_le hd
  have h2 := desc_le hdk
  have hjk : j = k := by omega
  subst hjk
  exact hne rfl

lemma isHeap_mono {a : Array Nat} {n m i : Nat} (h : IsHeap a n i) (hnm : m ≤ n) :
    IsHeap a m i := by
  intro j hj hd hne
  exact h j (Nat.lt_of_lt_of_le hj hnm) hd hne

/-- The heap property only depends on the values inside the subtree. -/
lemma isHeap_congr {a b : Array Nat} {n i : Nat}
    (hval : ∀ j : Nat, j < n → Desc i j → getd a j = getd b j) (h : IsHeap a n i) :
    IsHeap b n i := by
  intro j hj hd hne
  rw [← hval j hj hd, ← hval (parent j) (Nat.lt_of_le_of_lt (parent_le j) hj) (desc_peel hd hne)]
  exact h j hj hd hne

/-- A node with no children inside the window is trivially a heap. -/
lemma isHeap_leaf {a : Array Nat} {n i : Nat} (h : n ≤ left i) : IsHeap a n i := by
  intro j hj hd hne
  rcases desc_cases hd hne with h1 | h1
  · have hle := desc_le h1
    unfold left at h hle; omega
  · have hle := desc_le h1
    unfold right at hle; unfold left at h; omega

lemma bounded_sub {a : Array Nat} {n i j b : Nat} (h : Bounded a n i b) (hd : Desc i j) :
    Bounded a n j b := by
  intro k hk hdk
  exact h k hk (desc_trans hd hdk)

lemma bounded_congr {a c : Array Nat} {n i b : Nat}
    (hval : ∀ j : Nat, j < n → Desc i j → getd a j = getd c j) (h : Bounded a n i b) :
    Bounded c n i b := by
  intro j hj hd
  rw [← hval j hj hd]
  exact h j hj hd

/-- A global upper bound for an array. -/
def foldMax (a : Array Nat) : Nat := a.toList.foldl max 0

lemma le_foldl_max_init (l : List Nat) (b : Nat) : b ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => exact Nat.le_refl _
  | cons y t ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left b y) (ih (max b y))

lemma le_foldl_max_mem (l : List Nat) (x : Nat) (b : Nat) : x ∈ l → x ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => intro hx; exact absurd hx List.not_mem_nil
  | cons y t ih =>
    intro hx
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h
      exact Nat.le_trans (Nat.le_max_right b x) (le_foldl_max_init t (max b x))
    · exact ih (max b y) h

lemma getd_le_foldMax (a : Array Nat) (i : Nat) (h : i < a.size) : getd a i ≤ foldMax a := by
  rw [getd_eq a i h]
  exact le_foldl_max_mem a.toList a[i] 0 (Array.getElem_mem_toList h)

/-! ## Correctness of `maxHeapify` -/

/-- Specification of `maxHeapifyF`: the result is a permutation of the input,
    has the same size, satisfies the max-heap property at `i`, stays below the
    given bound `b`, and only modifies entries inside the subtree of `i`
    within the window `a[0..n)`. -/
theorem maxHeapifyF_spec (fuel : Nat) (a : Array Nat) (i n b : Nat)
    (hfuel : n - i < fuel) (hi : i < n) (hn : n ≤ a.size)
    (hl : IsHeap a n (left i)) (hr : IsHeap a n (right i))
    (bl : Bounded a n (left i) b) (br : Bounded a n (right i) b) (bi : getd a i ≤ b) :
    (maxHeapifyF fuel a i n).toList ~ a.toList ∧ (maxHeapifyF fuel a i n).size = a.size ∧
    IsHeap (maxHeapifyF fuel a i n) n i ∧ Bounded (maxHeapifyF fuel a i n) n i b ∧
    (∀ x : Nat, ¬ (Desc i x ∧ x < n) → getd (maxHeapifyF fuel a i n) x = getd a x) := by
  induction fuel generalizing a i b with
  | zero =>
    exact absurd hfuel (Nat.not_lt_zero _)
  | succ k ih =>
    have hisz : i < a.size := lt_of_lt_of_le hi hn
    simp only [maxHeapifyF]
    by_cases hc1 : left i < n ∧ getd a (left i) > getd a i
    · rw [if_pos hc1]
      by_cases hc2 : right i < n ∧ getd a (right i) > getd a (left i)
      · -- swap with right child (from the left-favored branch)
        rw [if_pos hc2]
        have hrsz : right i < a.size := lt_of_lt_of_le hc2.1 hn
        have hval : ∀ j : Nat, j < n → Desc (left (right i)) j →
            getd a j = getd (swapd a i (right i)) j := by
          intro j hj hd
          rw [getd_swapd a i (right i) hisz hrsz j,
            if_neg (by intro h; subst h; have := desc_le hd; simp only [left, right] at this; omega),
            if_neg (by intro h; subst h; have := desc_le hd; simp only [left, right] at this; omega)]
        have hval2 : ∀ j : Nat, j < n → Desc (right (right i)) j →
            getd a j = getd (swapd a i (right i)) j := by
          intro j hj hd
          rw [getd_swapd a i (right i) hisz hrsz j,
            if_neg (by intro h; subst h; have := desc_le hd; simp only [left, right] at this; omega),
            if_neg (by intro h; subst h; have := desc_le hd; simp only [left, right] at this; omega)]
        obtain ⟨hp1, hs1, hh1, hb1, hf1⟩ := ih (swapd a i (right i)) (right i) (getd a (right i))
          (by have := right_gt i; omega) hc2.1 (by rw [size_swapd]; exact hn)
          (isHeap_congr hval (isHeap_sub hr (Desc.ofLeft Desc.self)))
          (isHeap_congr hval2 (isHeap_sub hr (Desc.ofRight Desc.self)))
          (bounded_congr hval (bounded_sub (fun j hj hd => isHeap_rootMax hr j hd hj)
            (Desc.ofLeft Desc.self)))
          (bounded_congr hval2 (bounded_sub (fun j hj hd => isHeap_rootMax hr j hd hj)
            (Desc.ofRight Desc.self)))
          (by rw [getd_swapd a i (right i) hisz hrsz (right i), if_neg (right_ne i), if_pos rfl]
              exact le_of_lt (lt_trans hc1.2 hc2.2))
        have hci : getd (maxHeapifyF k (swapd a i (right i)) (right i) n) i = getd a (right i) := by
          rw [hf1 i (fun hcon => by have := desc_le hcon.1; unfold right at this; omega),
            getd_swapd a i (right i) hisz hrsz i, if_pos rfl]
        have hgetd_left : ∀ j : Nat, Desc (left i) j →
            getd (maxHeapifyF k (swapd a i (right i)) (right i) n) j = getd a j := by
          intro j hd
          rw [hf1 j (fun hcon => desc_disjoint_rl hcon.1 hd),
            getd_swapd a i (right i) hisz hrsz j,
            if_neg (by intro h; subst h; have := desc_le hd; unfold left at this; omega),
            if_neg (by intro h; subst h; exact desc_left_right_false hd)]
        refine ⟨hp1.trans (toList_swapd_perm a i (right i) hisz hrsz),
          hs1.trans (size_swapd _ _ _), ?_, ?_, ?_⟩
        · intro j hj hd hne
          by_cases hpj : parent j = i
          · have hj0 : 0 < j := by
              by_contra hz
              push_neg at hz
              have hjz : j = 0 := by omega
              subst hjz
              rw [parent_eq] at hpj
              have hi0 : i = 0 := by omega
              subst hi0
              exact hne rfl
            rcases eq_left_or_right_of_parent j hj0 with hjl | hjr
            · rw [hpj] at hjl; subst hjl
              rw [parent_left, hci, hgetd_left _ Desc.self]
              exact le_of_lt hc2.2
            · rw [hpj] at hjr; subst hjr
              rw [parent_right, hci]
              exact hb1 (right i) hc2.1 Desc.self
          · have hpd : Desc i (parent j) := desc_peel hd hne
            have hj0 : 0 < j := by
              by_contra hz
              push_neg at hz
              have hjz : j = 0 := by omega
              subst hjz
              have hi0 : i = 0 := by have := desc_le hd; omega
              subst hi0
              exact absurd (by rfl : parent 0 = 0) hpj
            rcases desc_cases hpd hpj with hdl | hdr
            · have hdj : Desc (left i) j := by
                rcases eq_left_or_right_of_parent j hj0 with hjl | hjr
                · rw [hjl]; exact Desc.ofLeft hdl
                · rw [hjr]; exact Desc.ofRight hdl
              have hjne : j ≠ left i := by
                intro heq; rw [heq, parent_left] at hpj; exact hpj rfl
              rw [hgetd_left j hdj, hgetd_left (parent j) hdl]
              exact hl j hj hdj hjne
            · have hdj : Desc (right i) j := by
                rcases eq_left_or_right_of_parent j hj0 with hjl | hjr
                · rw [hjl]; exact Desc.ofLeft hdr
                · rw [hjr]; exact Desc.ofRight hdr
              have hjne : j ≠ right i := by
                intro heq; rw [heq, parent_right] at hpj; exact hpj rfl
              exact hh1 j hj hdj hjne
        · intro j hj hd
          by_cases hji : j = i
          · subst j
            rw [hci]
            exact br (right i) hc2.1 Desc.self
          · rcases desc_cases hd hji with hdl | hdr
            · rw [hgetd_left j hdl]
              exact bl j hj hdl
            · exact le_trans (hb1 j hj hdr) (br (right i) hc2.1 Desc.self)
        · intro x hx
          rw [hf1 x (fun hcon => hx ⟨desc_trans (Desc.ofRight Desc.self) hcon.1, hcon.2⟩),
            getd_swapd a i (right i) hisz hrsz x,
            if_neg (by intro h; subst h; exact hx ⟨Desc.self, hi⟩),
            if_neg (by intro h; subst h; exact hx ⟨Desc.ofRight Desc.self, hc2.1⟩)]
      · -- swap with left child
        rw [if_neg hc2]
        have hlsz : left i < a.size := lt_of_lt_of_le hc1.1 hn
        have hval : ∀ j : Nat, j < n → Desc (left (left i)) j →
            getd a j = getd (swapd a i (left i)) j := by
          intro j hj hd
          rw [getd_swapd a i (left i) hisz hlsz j,
            if_neg (by intro h; subst h; have := desc_le hd; simp only [left, right] at this; omega),
            if_neg (by intro h; subst h; have := desc_le hd; simp only [left, right] at this; omega)]
        have hval2 : ∀ j : Nat, j < n → Desc (right (left i)) j →
            getd a j = getd (swapd a i (left i)) j := by
          intro j hj hd
          rw [getd_swapd a i (left i) hisz hlsz j,
            if_neg (by intro h; subst h; have := desc_le hd; simp only [left, right] at this; omega),
            if_neg (by intro h; subst h; have := desc_le hd; simp only [left, right] at this; omega)]
        obtain ⟨hp1, hs1, hh1, hb1, hf1⟩ := ih (swapd a i (left i)) (left i) (getd a (left i))
          (by have := left_gt i; omega) hc1.1 (by rw [size_swapd]; exact hn)
          (isHeap_congr hval (isHeap_sub hl (Desc.ofLeft Desc.self)))
          (isHeap_congr hval2 (isHeap_sub hl (Desc.ofRight Desc.self)))
          (bounded_congr hval (bounded_sub (fun j hj hd => isHeap_rootMax hl j hd hj)
            (Desc.ofLeft Desc.self)))
          (bounded_congr hval2 (bounded_sub (fun j hj hd => isHeap_rootMax hl j hd hj)
            (Desc.ofRight Desc.self)))
          (by rw [getd_swapd a i (left i) hisz hlsz (left i), if_neg (left_ne i), if_pos rfl]
              exact le_of_lt hc1.2)
        have hci : getd (maxHeapifyF k (swapd a i (left i)) (left i) n) i = getd a (left i) := by
          rw [hf1 i (fun hcon => by have := desc_le hcon.1; unfold left at this; omega),
            getd_swapd a i (left i) hisz hlsz i, if_pos rfl]
        have hgetd_right : ∀ j : Nat, Desc (right i) j →
            getd (maxHeapifyF k (swapd a i (left i)) (left i) n) j = getd a j := by
          intro j hd
          rw [hf1 j (fun hcon => desc_disjoint_lr hcon.1 hd),
            getd_swapd a i (left i) hisz hlsz j,
            if_neg (by intro h; subst h; have := desc_le hd; unfold right at this; omega),
            if_neg (by intro h; subst h; exact desc_right_left_false hd)]
        refine ⟨hp1.trans (toList_swapd_perm a i (left i) hisz hlsz),
          hs1.trans (size_swapd _ _ _), ?_, ?_, ?_⟩
        · intro j hj hd hne
          by_cases hpj : parent j = i
          · have hj0 : 0 < j := by
              by_contra hz
              push_neg at hz
              have hjz : j = 0 := by omega
              subst hjz
              rw [parent_eq] at hpj
              have hi0 : i = 0 := by omega
              subst hi0
              exact hne rfl
            rcases eq_left_or_right_of_parent j hj0 with hjl | hjr
            · rw [hpj] at hjl; subst hjl
              rw [parent_left, hci]
              exact hb1 (left i) hc1.1 Desc.self
            · rw [hpj] at hjr; subst hjr
              rw [parent_right, hci, hgetd_right _ Desc.self]
              exact le_of_not_gt (not_and.mp hc2 hj)
          · have hpd : Desc i (parent j) := desc_peel hd hne
            have hj0 : 0 < j := by
              by_contra hz
              push_neg at hz
              have hjz : j = 0 := by omega
              subst hjz
              have hi0 : i = 0 := by have := desc_le hd; omega
              subst hi0
              exact absurd (by rfl : parent 0 = 0) hpj
            rcases desc_cases hpd hpj with hdl | hdr
            · have hdj : Desc (left i) j := by
                rcases eq_left_or_right_of_parent j hj0 with hjl | hjr
                · rw [hjl]; exact Desc.ofLeft hdl
                · rw [hjr]; exact Desc.ofRight hdl
              have hjne : j ≠ left i := by
                intro heq; rw [heq, parent_left] at hpj; exact hpj rfl
              exact hh1 j hj hdj hjne
            · have hdj : Desc (right i) j := by
                rcases eq_left_or_right_of_parent j hj0 with hjl | hjr
                · rw [hjl]; exact Desc.ofLeft hdr
                · rw [hjr]; exact Desc.ofRight hdr
              have hjne : j ≠ right i := by
                intro heq; rw [heq, parent_right] at hpj; exact hpj rfl
              rw [hgetd_right j hdj, hgetd_right (parent j) hdr]
              exact hr j hj hdj hjne
        · intro j hj hd
          by_cases hji : j = i
          · subst j
            rw [hci]
            exact bl (left i) hc1.1 Desc.self
          · rcases desc_cases hd hji with hdl | hdr
            · exact le_trans (hb1 j hj hdl) (bl (left i) hc1.1 Desc.self)
            · rw [hgetd_right j hdr]
              exact br j hj hdr
        · intro x hx
          rw [hf1 x (fun hcon => hx ⟨desc_trans (Desc.ofLeft Desc.self) hcon.1, hcon.2⟩),
            getd_swapd a i (left i) hisz hlsz x,
            if_neg (by intro h; subst h; exact hx ⟨Desc.self, hi⟩),
            if_neg (by intro h; subst h; exact hx ⟨Desc.ofLeft Desc.self, hc1.1⟩)]
    · rw [if_neg hc1]
      by_cases hc2 : right i < n ∧ getd a (right i) > getd a i
      · -- swap with right child (from the unbiased branch)
        rw [if_pos hc2]
        have hrsz : right i < a.size := lt_of_lt_of_le hc2.1 hn
        have hval : ∀ j : Nat, j < n → Desc (left (right i)) j →
            getd a j = getd (swapd a i (right i)) j := by
          intro j hj hd
          rw [getd_swapd a i (right i) hisz hrsz j,
            if_neg (by intro h; subst h; have := desc_le hd; simp only [left, right] at this; omega),
            if_neg (by intro h; subst h; have := desc_le hd; simp only [left, right] at this; omega)]
        have hval2 : ∀ j : Nat, j < n → Desc (right (right i)) j →
            getd a j = getd (swapd a i (right i)) j := by
          intro j hj hd
          rw [getd_swapd a i (right i) hisz hrsz j,
            if_neg (by intro h; subst h; have := desc_le hd; simp only [left, right] at this; omega),
            if_neg (by intro h; subst h; have := desc_le hd; simp only [left, right] at this; omega)]
        obtain ⟨hp1, hs1, hh1, hb1, hf1⟩ := ih (swapd a i (right i)) (right i) (getd a (right i))
          (by have := right_gt i; omega) hc2.1 (by rw [size_swapd]; exact hn)
          (isHeap_congr hval (isHeap_sub hr (Desc.ofLeft Desc.self)))
          (isHeap_congr hval2 (isHeap_sub hr (Desc.ofRight Desc.self)))
          (bounded_congr hval (bounded_sub (fun j hj hd => isHeap_rootMax hr j hd hj)
            (Desc.ofLeft Desc.self)))
          (bounded_congr hval2 (bounded_sub (fun j hj hd => isHeap_rootMax hr j hd hj)
            (Desc.ofRight Desc.self)))
          (by rw [getd_swapd a i (right i) hisz hrsz (right i), if_neg (right_ne i), if_pos rfl]
              exact le_of_lt hc2.2)
        have hci : getd (maxHeapifyF k (swapd a i (right i)) (right i) n) i = getd a (right i) := by
          rw [hf1 i (fun hcon => by have := desc_le hcon.1; unfold right at this; omega),
            getd_swapd a i (right i) hisz hrsz i, if_pos rfl]
        have hgetd_left : ∀ j : Nat, Desc (left i) j →
            getd (maxHeapifyF k (swapd a i (right i)) (right i) n) j = getd a j := by
          intro j hd
          rw [hf1 j (fun hcon => desc_disjoint_rl hcon.1 hd),
            getd_swapd a i (right i) hisz hrsz j,
            if_neg (by intro h; subst h; have := desc_le hd; unfold left at this; omega),
            if_neg (by intro h; subst h; exact desc_left_right_false hd)]
        refine ⟨hp1.trans (toList_swapd_perm a i (right i) hisz hrsz),
          hs1.trans (size_swapd _ _ _), ?_, ?_, ?_⟩
        · intro j hj hd hne
          by_cases hpj : parent j = i
          · have hj0 : 0 < j := by
              by_contra hz
              push_neg at hz
              have hjz : j = 0 := by omega
              subst hjz
              rw [parent_eq] at hpj
              have hi0 : i = 0 := by omega
              subst hi0
              exact hne rfl
            rcases eq_left_or_right_of_parent j hj0 with hjl | hjr
            · rw [hpj] at hjl; subst hjl
              rw [parent_left, hci, hgetd_left _ Desc.self]
              exact le_trans (le_of_not_gt (not_and.mp hc1 hj)) (le_of_lt hc2.2)
            · rw [hpj] at hjr; subst hjr
              rw [parent_right, hci]
              exact hb1 (right i) hc2.1 Desc.self
          · have hpd : Desc i (parent j) := desc_peel hd hne
            have hj0 : 0 < j := by
              by_contra hz
              push_neg at hz
              have hjz : j = 0 := by omega
              subst hjz
              have hi0 : i = 0 := by have := desc_le hd; omega
              subst hi0
              exact absurd (by rfl : parent 0 = 0) hpj
            rcases desc_cases hpd hpj with hdl | hdr
            · have hdj : Desc (left i) j := by
                rcases eq_left_or_right_of_parent j hj0 with hjl | hjr
                · rw [hjl]; exact Desc.ofLeft hdl
                · rw [hjr]; exact Desc.ofRight hdl
              have hjne : j ≠ left i := by
                intro heq; rw [heq, parent_left] at hpj; exact hpj rfl
              rw [hgetd_left j hdj, hgetd_left (parent j) hdl]
              exact hl j hj hdj hjne
            · have hdj : Desc (right i) j := by
                rcases eq_left_or_right_of_parent j hj0 with hjl | hjr
                · rw [hjl]; exact Desc.ofLeft hdr
                · rw [hjr]; exact Desc.ofRight hdr
              have hjne : j ≠ right i := by
                intro heq; rw [heq, parent_right] at hpj; exact hpj rfl
              exact hh1 j hj hdj hjne
        · intro j hj hd
          by_cases hji : j = i
          · subst j
            rw [hci]
            exact br (right i) hc2.1 Desc.self
          · rcases desc_cases hd hji with hdl | hdr
            · rw [hgetd_left j hdl]
              exact bl j hj hdl
            · exact le_trans (hb1 j hj hdr) (br (right i) hc2.1 Desc.self)
        · intro x hx
          rw [hf1 x (fun hcon => hx ⟨desc_trans (Desc.ofRight Desc.self) hcon.1, hcon.2⟩),
            getd_swapd a i (right i) hisz hrsz x,
            if_neg (by intro h; subst h; exact hx ⟨Desc.self, hi⟩),
            if_neg (by intro h; subst h; exact hx ⟨Desc.ofRight Desc.self, hc2.1⟩)]
      · -- no swap: `i` already satisfies the heap property
        rw [if_neg hc2]
        refine ⟨List.Perm.refl _, rfl, ?_, ?_, fun x _ => rfl⟩
        · intro j hj hd hne
          by_cases hpj : parent j = i
          · have hj0 : 0 < j := by
              by_contra hz
              push_neg at hz
              have hjz : j = 0 := by omega
              subst hjz
              rw [parent_eq] at hpj
              have hi0 : i = 0 := by omega
              subst hi0
              exact hne rfl
            rcases eq_left_or_right_of_parent j hj0 with hjl | hjr
            · rw [hpj] at hjl; subst hjl
              rw [parent_left]
              exact le_of_not_gt (not_and.mp hc1 hj)
            · rw [hpj] at hjr; subst hjr
              rw [parent_right]
              exact le_of_not_gt (not_and.mp hc2 hj)
          · have hpd : Desc i (parent j) := desc_peel hd hne
            have hj0 : 0 < j := by
              by_contra hz
              push_neg at hz
              have hjz : j = 0 := by omega
              subst hjz
              have hi0 : i = 0 := by have := desc_le hd; omega
              subst hi0
              exact absurd (by rfl : parent 0 = 0) hpj
            rcases desc_cases hpd hpj with hdl | hdr
            · have hdj : Desc (left i) j := by
                rcases eq_left_or_right_of_parent j hj0 with hjl | hjr
                · rw [hjl]; exact Desc.ofLeft hdl
                · rw [hjr]; exact Desc.ofRight hdl
              have hjne : j ≠ left i := by
                intro heq; rw [heq, parent_left] at hpj; exact hpj rfl
              exact hl j hj hdj hjne
            · have hdj : Desc (right i) j := by
                rcases eq_left_or_right_of_parent j hj0 with hjl | hjr
                · rw [hjl]; exact Desc.ofLeft hdr
                · rw [hjr]; exact Desc.ofRight hdr
              have hjne : j ≠ right i := by
                intro heq; rw [heq, parent_right] at hpj; exact hpj rfl
              exact hr j hj hdj hjne
        · intro j hj hd
          by_cases hji : j = i
          · subst j; exact bi
          · rcases desc_cases hd hji with hdl | hdr
            · exact bl j hj hdl
            · exact br j hj hdr

/-! ## Correctness of `buildMaxHeap` -/

lemma buildLoop_spec (a : Array Nat) (m : Nat) (hm : m ≤ a.size)
    (h : ∀ j : Nat, m ≤ j → IsHeap a a.size j) :
    (buildLoop a m).toList ~ a.toList ∧ (buildLoop a m).size = a.size ∧
    ∀ j : Nat, IsHeap (buildLoop a m) (buildLoop a m).size j := by
  induction m generalizing a with
  | zero =>
    exact ⟨List.Perm.refl _, rfl, fun j => h j (Nat.zero_le j)⟩
  | succ m ih =>
    have hmn : m < a.size := by omega
    simp only [buildLoop]
    obtain ⟨hp1, hs1, hh1, hb1, hf1⟩ := maxHeapifyF_spec (a.size - m + 1) a m a.size (foldMax a)
      (by omega) hmn (Nat.le_refl _)
      (h (left m) (by have := left_gt m; omega))
      (h (right m) (by have := right_gt m; omega))
      (fun j hj hd => getd_le_foldMax a j (by omega))
      (fun j hj hd => getd_le_foldMax a j (by omega))
      (getd_le_foldMax a m hmn)
    have h' : ∀ j : Nat, m ≤ j → IsHeap (maxHeapify a m a.size) (maxHeapify a m a.size).size j := by
      intro j hj
      have hj' : IsHeap (maxHeapifyF (a.size - m + 1) a m a.size) a.size j := by
        by_cases hjm : j = m
        · subst j
          exact hh1
        · by_cases hdesc : Desc m j
          · exact isHeap_sub hh1 hdesc
          · apply isHeap_congr _ (h j (by omega))
            intro x hx hdx
            exact (hf1 x (fun hcon => by
              rcases desc_cmp hcon.1 hdx with h1 | h1
              · exact absurd h1 hdesc
              · have := desc_le h1; omega)).symm
      exact isHeap_eq_of_size hs1.symm hj'
    have hm' : m ≤ (maxHeapify a m a.size).size := by
      have hs : (maxHeapify a m a.size).size = a.size := hs1
      omega
    obtain ⟨hp2, hs2, hh2⟩ := ih (maxHeapify a m a.size) hm' h'
    exact ⟨hp2.trans hp1, hs2.trans hs1, hh2⟩

lemma buildMaxHeap_spec (a : Array Nat) :
    (buildMaxHeap a).toList ~ a.toList ∧ (buildMaxHeap a).size = a.size ∧
    ∀ j : Nat, IsHeap (buildMaxHeap a) (buildMaxHeap a).size j := by
  unfold buildMaxHeap
  by_cases h : a.size ≤ 1
  · rw [if_pos h]
    exact ⟨List.Perm.refl _, rfl, fun j => isHeap_leaf (by unfold left; omega)⟩
  · rw [if_neg h]
    have hn2 : 2 ≤ a.size := by omega
    obtain ⟨hp, hs, hh⟩ := buildLoop_spec a (parent (a.size - 1) + 1)
      (by have := parent_le (a.size - 1); omega)
      (fun j hj => isHeap_leaf (by
        rw [parent_eq] at hj
        unfold left
        omega))
    exact ⟨hp, hs, hh⟩

/-! ## Correctness of the extraction loop -/

lemma extractLoop_spec (a : Array Nat) (m : Nat) (hm : m + 1 ≤ a.size)
    (hheap : IsHeap a (m + 1) 0)
    (htail : ∀ x y : Nat, m + 1 ≤ x → x < y → y < a.size → getd a x ≤ getd a y)
    (hbridge : ∀ x y : Nat, x < m + 1 → m + 1 ≤ y → y < a.size → getd a x ≤ getd a y) :
    (extractLoop a m).toList ~ a.toList ∧ (extractLoop a m).size = a.size ∧
    (∀ x y : Nat, x < y → y < a.size → getd (extractLoop a m) x ≤ getd (extractLoop a m) y) := by
  induction m generalizing a with
  | zero =>
    refine ⟨List.Perm.refl _, rfl, ?_⟩
    intro x y hxy hy
    by_cases hx0 : x = 0
    · subst x
      exact hbridge 0 y (by omega) (by omega) hy
    · exact htail x y (by omega) hxy hy
  | succ m ih =>
    simp only [extractLoop]
    have hi_pos : 0 < m + 1 := by omega
    have hi_sz : m + 1 < a.size := by omega
    have h0sz : 0 < a.size := by omega
    have hb_size : (swapd a 0 (m + 1)).size = a.size := size_swapd _ _ _
    have hpre_left : IsHeap (swapd a 0 (m + 1)) (m + 1) (left 0) := by
      apply isHeap_congr _ (isHeap_mono (isHeap_sub hheap (Desc.ofLeft Desc.self)) (by omega))
      intro j hj hd
      rw [getd_swapd a 0 (m + 1) h0sz hi_sz j]
      have hj0 : j ≠ 0 := by
        intro hz
        have hle := desc_le hd
        rw [hz] at hle
        unfold left at hle; omega
      have hji : j ≠ m + 1 := by omega
      rw [if_neg hj0, if_neg hji]
    have hpre_right : IsHeap (swapd a 0 (m + 1)) (m + 1) (right 0) := by
      apply isHeap_congr _ (isHeap_mono (isHeap_sub hheap (Desc.ofRight Desc.self)) (by omega))
      intro j hj hd
      rw [getd_swapd a 0 (m + 1) h0sz hi_sz j]
      have hj0 : j ≠ 0 := by
        intro hz
        have hle := desc_le hd
        rw [hz] at hle
        unfold right at hle; omega
      have hji : j ≠ m + 1 := by omega
      rw [if_neg hj0, if_neg hji]
    obtain ⟨hc_perm, hc_size, hc_heap, hc_bound, hc_frame⟩ :=
      maxHeapifyF_spec (m + 1 - 0 + 1) (swapd a 0 (m + 1)) 0 (m + 1) (foldMax (swapd a 0 (m + 1)))
        (by omega) hi_pos (by rw [hb_size]; omega)
        hpre_left hpre_right
        (fun j hj hd => getd_le_foldMax _ j (by rw [hb_size]; omega))
        (fun j hj hd => getd_le_foldMax _ j (by rw [hb_size]; omega))
        (getd_le_foldMax _ 0 (by rw [hb_size]; omega))
    have hcsize : (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).size = a.size := hc_size.trans hb_size
    have hframe : ∀ x : Nat, m + 1 ≤ x →
        getd (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)) x = getd (swapd a 0 (m + 1)) x := by
      intro x hx
      apply hc_frame x
      intro hcon
      omega
    have hm' : m + 1 ≤ (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).size := by rw [hcsize]; omega
    have hheap' : IsHeap (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)) (m + 1) 0 := hc_heap
    have htail' : ∀ x y : Nat, m + 1 ≤ x → x < y →
        y < (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).size →
        getd (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)) x ≤
          getd (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)) y := by
      intro x y hx hxy hy
      rw [hcsize] at hy
      rw [hframe x (by omega), hframe y (by omega)]
      by_cases hxi : x = m + 1
      · subst x
        rw [getd_swapd a 0 (m + 1) h0sz hi_sz (m + 1), if_neg (by omega), if_pos rfl]
        have hyi : y ≠ m + 1 := by omega
        rw [getd_swapd a 0 (m + 1) h0sz hi_sz y, if_neg (by omega), if_neg hyi]
        exact hbridge 0 y (by omega) (by omega) hy
      · rw [getd_swapd a 0 (m + 1) h0sz hi_sz x, if_neg (by omega), if_neg hxi]
        have hyi : y ≠ m + 1 := by omega
        rw [getd_swapd a 0 (m + 1) h0sz hi_sz y, if_neg (by omega), if_neg hyi]
        exact htail x y (by omega) hxy hy
    have hbridge' : ∀ x y : Nat, x < m + 1 → m + 1 ≤ y →
        y < (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).size →
        getd (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)) x ≤
          getd (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)) y := by
      intro x y hx hy hyn
      rw [hcsize] at hyn
      rw [hframe y (by omega)]
      have h1 : getd (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)) x ≤
          getd (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)) 0 :=
        isHeap_rootMax hheap' x (desc_zero x) hx
      have h2 : getd (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)) 0 ≤
          getd (swapd a 0 (m + 1)) (m + 1) := by
        have hplen : 0 < ((maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).toList.take (m + 1)).length := by
          rw [List.length_take, Array.length_toList, hcsize]
          omega
        have hmem : getd (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)) 0 ∈
            (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).toList.take (m + 1) := by
          have e := List.getElem_mem (l := (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).toList.take (m + 1))
            (n := 0) hplen
          rw [List.getElem_take] at e
          rw [getd_eq_toList _ 0 (by rw [hcsize]; omega)]
          exact e
        have htake : (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).toList.take (m + 1) ~
            (swapd a 0 (m + 1)).toList.take (m + 1) := by
          have hdrop : (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).toList.drop (m + 1) =
              (swapd a 0 (m + 1)).toList.drop (m + 1) := by
            apply List.ext_getElem
            · rw [List.length_drop, List.length_drop, Array.length_toList, Array.length_toList,
                hcsize, hb_size]
            · intro k hk1 hk2
              have hk : m + 1 + k < a.size := by
                rw [List.length_drop, Array.length_toList, hcsize] at hk1
                omega
              rw [List.getElem_drop, List.getElem_drop,
                ← getd_eq_toList _ (m + 1 + k) (by rw [hcsize]; omega),
                ← getd_eq_toList _ (m + 1 + k) (by rw [hb_size]; omega)]
              exact hframe (m + 1 + k) (by omega)
          have h1' := List.take_append_drop (m + 1) (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).toList
          have h2' := List.take_append_drop (m + 1) (swapd a 0 (m + 1)).toList
          have hperm : ((maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).toList.take (m + 1) ++
                (swapd a 0 (m + 1)).toList.drop (m + 1)) ~
              ((swapd a 0 (m + 1)).toList.take (m + 1) ++ (swapd a 0 (m + 1)).toList.drop (m + 1)) := by
            have e : ((maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).toList.take (m + 1) ++
                  (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)).toList.drop (m + 1)) ~
                ((swapd a 0 (m + 1)).toList.take (m + 1) ++ (swapd a 0 (m + 1)).toList.drop (m + 1)) := by
              rw [h1', h2']
              exact hc_perm
            rwa [hdrop] at e
          exact (List.perm_iff_count).mpr (fun w => by
            have hc1 := List.Perm.count_eq hperm w
            rw [List.count_append, List.count_append] at hc1
            omega)
        rw [List.Perm.mem_iff htake] at hmem
        rw [List.mem_iff_getElem] at hmem
        obtain ⟨x', hx', hxx⟩ := hmem
        rw [List.getElem_take] at hxx
        have hx'i : x' < m + 1 := by
          have htmp := hx'
          rw [List.length_take] at htmp
          omega
        have hx'sz : x' < a.size := by omega
        rw [← hxx, ← getd_eq_toList _ x' (by rw [hb_size]; omega)]
        by_cases hx0 : x' = 0
        · subst x'
          rw [getd_swapd a 0 (m + 1) h0sz hi_sz 0, if_pos rfl,
            getd_swapd a 0 (m + 1) h0sz hi_sz (m + 1), if_neg (by omega), if_pos rfl]
          exact isHeap_rootMax hheap (m + 1) (desc_zero _) (by omega)
        · have hxi : x' ≠ m + 1 := by omega
          rw [getd_swapd a 0 (m + 1) h0sz hi_sz x', if_neg hx0, if_neg hxi,
            getd_swapd a 0 (m + 1) h0sz hi_sz (m + 1), if_neg (by omega), if_pos rfl]
          exact isHeap_rootMax hheap x' (desc_zero _) (by omega)
      have h3 : getd (swapd a 0 (m + 1)) (m + 1) ≤ getd (swapd a 0 (m + 1)) y := by
        by_cases hyi : y = m + 1
        · subst y
          exact Nat.le_refl _
        · rw [getd_swapd a 0 (m + 1) h0sz hi_sz (m + 1), if_neg (by omega), if_pos rfl,
              getd_swapd a 0 (m + 1) h0sz hi_sz y, if_neg (by omega), if_neg hyi]
          exact hbridge 0 y (by omega) (by omega) hyn
      exact Nat.le_trans (Nat.le_trans h1 h2) h3
    obtain ⟨hperm3, hsize3, hsorted3⟩ :=
      ih (maxHeapify (swapd a 0 (m + 1)) 0 (m + 1)) hm' hheap' htail' hbridge'
    refine ⟨hperm3.trans (hc_perm.trans (toList_swapd_perm a 0 (m + 1) h0sz hi_sz)),
      hsize3.trans hcsize, ?_⟩
    intro x y hxy hy
    exact hsorted3 x y hxy (by rw [hcsize]; exact hy)

/-! ## Correctness of `heapsort` -/

lemma heapsort_spec (xs : List Nat) :
    (heapsort xs) ~ xs ∧ (heapsort xs).Sorted (· ≤ ·) ∧ (heapsort xs).length = xs.length := by
  unfold heapsort
  by_cases h : xs.length ≤ 1
  · rw [if_pos h]
    refine ⟨List.Perm.refl _, ?_, rfl⟩
    cases xs with
    | nil => exact List.sorted_nil
    | cons x t =>
      cases t with
      | nil => exact List.sorted_singleton x
      | cons y u => simp at h
  · rw [if_neg h]
    have hn2 : 2 ≤ xs.toArray.size := by rw [List.size_toArray]; omega
    obtain ⟨hb_perm, hb_size, hb_heap⟩ := buildMaxHeap_spec xs.toArray
    obtain ⟨hc_perm, hc_size, hc_sorted⟩ :=
      extractLoop_spec (buildMaxHeap xs.toArray) ((buildMaxHeap xs.toArray).size - 1)
        (by omega)
        (isHeap_eq_of_size (by omega) (hb_heap 0))
        (by intro x y hx hxy hy; omega)
        (by intro x y hx hxy hy; omega)
    refine ⟨hc_perm.trans (hb_perm.trans (by rw [List.toList_toArray])), ?_, ?_⟩
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      have hj' : j < (buildMaxHeap xs.toArray).size := by
        rw [Array.length_toList, hc_size] at hj
        exact hj
      rw [← getd_eq_toList _ i (by rw [hc_size]; omega),
          ← getd_eq_toList _ j (by rw [hc_size]; omega)]
      exact hc_sorted i j hij hj'
    · have e1 := hc_perm.length_eq
      have e2 := hb_perm.length_eq
      rw [e1, e2, List.toList_toArray]

/-! ## Properties and theorems -/

/-- Sortedness property of `heapsort`. -/
def sorted_prop (xs : List Nat) : Prop := (heapsort xs).Sorted (· ≤ ·)

/-- Permutation property of `heapsort`: the output is a permutation of the input. -/
def perm_prop (xs : List Nat) : Prop := heapsort xs ~ xs

/-- Length preservation property of `heapsort`. -/
def length_prop (xs : List Nat) : Prop := (heapsort xs).length = xs.length

theorem sorted_thm (xs : List Nat) : Pre xs → sorted_prop xs := fun _ => (heapsort_spec xs).2.1

theorem perm_thm (xs : List Nat) : Pre xs → perm_prop xs := fun _ => (heapsort_spec xs).1

theorem length_thm (xs : List Nat) : Pre xs → length_prop xs := fun _ => (heapsort_spec xs).2.2

/-- Post-condition: the conjunction of the three properties. -/
def Post_prop (xs : List Nat) : Prop := sorted_prop xs ∧ perm_prop xs ∧ length_prop xs

/-! ## Property-based tests -/

/-- Executable sortedness check. -/
def sortedB : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: t => decide (x ≤ y) && sortedB (y :: t)

/-- Executable permutation check (via element counts). -/
def permB (xs ys : List Nat) : Bool :=
  xs.length == ys.length &&
    xs.all (fun x => decide (ys.count x = xs.count x)) &&
    ys.all (fun y => decide (ys.count y = xs.count y))

/-- Executable form of the post-condition. -/
def postB (xs : List Nat) : Bool :=
  sortedB (heapsort xs) && permB (heapsort xs) xs && ((heapsort xs).length == xs.length)

-- randomized PBT for `sorted_prop`
#eval Plausible.Testable.check (∀ xs : List Nat, sortedB (heapsort xs) = true)
-- randomized PBT for `perm_prop`
#eval Plausible.Testable.check (∀ xs : List Nat, permB (heapsort xs) xs = true)
-- randomized PBT for `length_prop`
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).length = xs.length)
-- randomized PBT for the post-condition
#eval Plausible.Testable.check (∀ xs : List Nat, postB xs = true)

-- bounded PBTs (exhaustive small structured cases)
example : (List.range 12).all (fun n => sortedB (heapsort (List.range n))) = true := by
  native_decide
example : (List.range 12).all (fun n => sortedB (heapsort (List.range n).reverse)) = true := by
  native_decide
example : (List.range 10).all (fun n =>
    permB (heapsort (List.range n).reverse) (List.range n).reverse) = true := by
  native_decide
example : (List.range 10).all (fun n => postB (List.range n)) = true := by native_decide

/-! ## Correctness theorem: `Pre → Post` -/

theorem heapsort_correct (xs : List Nat) : Pre xs → Post_prop xs :=
  fun _ => ⟨sorted_thm xs trivial, perm_thm xs trivial, length_thm xs trivial⟩

/-! ## Imperative implementation (using `Id.run` with mutable state) -/

/-- Imperative `maxHeapifyF`: mirrors the Python `while` loop using a mutable
    `largest` index. -/
def maxHeapifyFImp : Nat → Array Nat → Nat → Nat → Id (Array Nat)
  | 0, a, i, n => pure a
  | k + 1, a, i, n => do
    let mut largest := i
    if left i < n ∧ getd a (left i) > getd a i then
      largest := left i
    else
      largest := i
    if right i < n ∧ getd a (right i) > getd a largest then
      largest := right i
    else
      largest := largest
    if largest = i then
      pure a
    else
      maxHeapifyFImp k (swapd a i largest) largest n

/-- Imperative `max_heapify`. -/
def maxHeapifyImp (a : Array Nat) (i n : Nat) : Id (Array Nat) :=
  maxHeapifyFImp (n - i + 1) a i n

/-- Imperative `buildLoop`. -/
def buildLoopImp : Array Nat → Nat → Id (Array Nat)
  | a, 0 => pure a
  | a, m + 1 => do
    let a' ← maxHeapifyImp a m a.size
    buildLoopImp a' m

/-- Imperative `build_max_heap`. -/
def buildMaxHeapImp (a : Array Nat) : Id (Array Nat) := do
  if a.size ≤ 1 then
    pure a
  else
    buildLoopImp a (parent (a.size - 1) + 1)

/-- Imperative `extractLoop`. -/
def extractLoopImp : Array Nat → Nat → Id (Array Nat)
  | a, 0 => pure a
  | a, m + 1 => do
    let a' ← maxHeapifyImp (swapd a 0 (m + 1)) 0 (m + 1)
    extractLoopImp a' m

/-- Imperative `heapsort` using `Id.run` with mutable state. -/
def heapsortImperative (xs : List Nat) : List Nat := Id.run do
  if xs.length ≤ 1 then
    return xs
  let mut a := xs.toArray
  a ← buildMaxHeapImp a
  a ← extractLoopImp a (a.size - 1)
  return a.toList

/-! ## Imperative tests -/

example : heapsortImperative [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsortImperative [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsortImperative [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsortImperative [] = ([] : List Nat) := by native_decide
example : heapsortImperative [42] = [42] := by native_decide
example : heapsortImperative [2, 1] = [1, 2] := by native_decide
example : heapsortImperative [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsortImperative [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapsortImperative [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsortImperative [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide

#eval heapsortImperative [3, 1, 2]
#eval heapsortImperative [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsortImperative [9, 8, 7, 6, 5, 4, 3, 2, 1]

/-! ## Equivalence: functional = imperative -/

theorem maxHeapifyFImp_eq (fuel : Nat) (a : Array Nat) (i n : Nat) :
    maxHeapifyFImp fuel a i n = pure (maxHeapifyF fuel a i n) := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ k ih =>
    simp only [maxHeapifyFImp, maxHeapifyF, pure_bind]
    repeat' split
    all_goals first
      | rfl
      | exact ih _ _
      | (rename_i h; exact absurd h (right_ne i))
      | (rename_i h; exact absurd h (left_ne i))
      | (rename_i h; exact absurd rfl h)
      | (rename_i h; omega)
      | (rename_i h; simp at h)

theorem maxHeapifyImp_eq (a : Array Nat) (i n : Nat) :
    maxHeapifyImp a i n = pure (maxHeapify a i n) :=
  maxHeapifyFImp_eq _ _ _ _

theorem buildLoopImp_eq (a : Array Nat) (m : Nat) :
    buildLoopImp a m = pure (buildLoop a m) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    simp only [buildLoopImp, buildLoop, maxHeapifyImp_eq, pure_bind]
    exact ih _

theorem buildMaxHeapImp_eq (a : Array Nat) :
    buildMaxHeapImp a = pure (buildMaxHeap a) := by
  unfold buildMaxHeapImp buildMaxHeap
  split
  · rfl
  · exact buildLoopImp_eq _ _

theorem extractLoopImp_eq (a : Array Nat) (m : Nat) :
    extractLoopImp a m = pure (extractLoop a m) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    simp only [extractLoopImp, extractLoop, maxHeapifyImp_eq, pure_bind]
    exact ih _

theorem heapsort_equiv (xs : List Nat) : heapsortImperative xs = heapsort xs := by
  unfold heapsortImperative heapsort
  split
  · rfl
  · simp only [buildMaxHeapImp_eq, extractLoopImp_eq, pure_bind]
    rfl

end heapsort_algorithm
