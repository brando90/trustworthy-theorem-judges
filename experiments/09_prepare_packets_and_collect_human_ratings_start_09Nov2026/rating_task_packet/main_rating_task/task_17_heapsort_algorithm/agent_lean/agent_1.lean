import Mathlib

/-!
# Heapsort

0-based max-heap heapsort following CLRS 6.4 and the supplied Python program.
-/

namespace heapsort_algorithm

def parent (i : Nat) : Nat :=
  if i = 0 then 0 else (i - 1) / 2

def left (i : Nat) : Nat := 2 * i + 1

def right (i : Nat) : Nat := 2 * i + 2

theorem parent_of_pos (i : Nat) (hi : 0 < i) : parent i = (i - 1) / 2 := by
  simp [parent, hi.ne']

theorem parent_lt (i : Nat) (hi : 0 < i) : parent i < i := by
  rw [parent_of_pos i hi]; omega

theorem left_gt (i : Nat) : i < left i := by unfold left; omega
theorem right_gt (i : Nat) : i < right i := by unfold right; omega

theorem parent_left (i : Nat) : parent (left i) = i := by
  have hpos : 0 < left i := by unfold left; omega
  rw [parent_of_pos _ hpos]; unfold left; omega

theorem parent_right (i : Nat) : parent (right i) = i := by
  have hpos : 0 < right i := by unfold right; omega
  rw [parent_of_pos _ hpos]; unfold right; omega

theorem parent_eq_child (j i : Nat) (hj : 0 < j) :
    parent j = i ↔ j = left i ∨ j = right i := by
  constructor
  · intro h
    have hdiv : (j - 1) / 2 = i := by rwa [parent_of_pos j hj] at h
    unfold left right
    omega
  · rintro (h | h) <;> simp [h, parent_left, parent_right]

def inSubtree (root j : Nat) : Bool :=
  if j == root then true
  else if j == 0 then false
  else inSubtree root (parent j)
termination_by j
decreasing_by
  simp_wf
  have hj : j ≠ 0 := by simp_all [beq_iff_eq]
  exact parent_lt j (Nat.pos_of_ne_zero hj)

theorem inSubtree_unfold (root j : Nat) :
    inSubtree root j =
      if j == root then true else if j == 0 then false else inSubtree root (parent j) := by
  rw [inSubtree.eq_1]

theorem inSubtree_self (root : Nat) : inSubtree root root = true := by
  rw [inSubtree_unfold]; simp

theorem inSubtree_zero_of_ne (root : Nat) (h : root ≠ 0) : inSubtree root 0 = false := by
  rw [inSubtree_unfold]; simp [beq_iff_eq, Ne.symm h]

theorem inSubtree_of_ne (root j : Nat) (hne : j ≠ root) (hpos : 0 < j) :
    inSubtree root j = inSubtree root (parent j) := by
  rw [inSubtree_unfold]; simp [beq_iff_eq, hne, hpos.ne']


theorem inSubtree_le (root j : Nat) (h : inSubtree root j = true) : root ≤ j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hje : j = root
    · omega
    · have hpos : 0 < j := by
        by_contra hz
        have hj0 : j = 0 := by omega
        rw [hj0] at h
        simp [inSubtree_zero_of_ne root (by omega : root ≠ 0)] at h
      rw [inSubtree_of_ne root j hje hpos] at h
      have hp : parent j < j := parent_lt j hpos
      have : root ≤ parent j := ih (parent j) hp h
      omega

theorem inSubtree_parent (root j : Nat) (h : inSubtree root j = true) (hne : j ≠ root) :
    inSubtree root (parent j) = true := by
  have hpos : 0 < j := by
    by_contra hz
    have hj0 : j = 0 := by omega
    rw [hj0] at h
    simp [inSubtree_zero_of_ne root (by omega : root ≠ 0)] at h
  rwa [inSubtree_of_ne root j hne hpos] at h

theorem inSubtree_down (root j : Nat) (h : inSubtree root (parent j) = true) (hpos : 0 < j) :
    inSubtree root j = true := by
  by_cases hje : j = root
  · simp [hje, inSubtree_self]
  · rw [inSubtree_of_ne root j hje hpos]; exact h

theorem inSubtree_left (i : Nat) : inSubtree i (left i) = true := by
  rw [inSubtree_of_ne i (left i) (by unfold left; omega) (by unfold left; omega)]
  simp [parent_left, inSubtree_self]

theorem inSubtree_right (i : Nat) : inSubtree i (right i) = true := by
  rw [inSubtree_of_ne i (right i) (by unfold right; omega) (by unfold right; omega)]
  simp [parent_right, inSubtree_self]

theorem inSubtree_child_of_parent (root j : Nat) (h : parent j = root) :
    inSubtree root j = true := by
  by_cases hj : j = 0
  · subst hj
    have : root = 0 := by simpa [parent] using h.symm
    simp [this, inSubtree_self]
  · exact inSubtree_down root j (by simpa [h, inSubtree_self]) (Nat.pos_of_ne_zero hj)

theorem inSubtree_trans (root mid j : Nat)
    (hm : inSubtree root mid = true) (hj : inSubtree mid j = true) :
    inSubtree root j = true := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hjm : j = mid
    · simp [hjm, hm]
    · have hpos : 0 < j := by
        by_contra hz
        have hj0 : j = 0 := by omega
        rw [hj0] at hj
        have hmne : mid ≠ 0 := by
          intro hz
          subst hz
          subst hj0
          exact hjm rfl
        simp [inSubtree_zero_of_ne mid hmne] at hj
      rw [inSubtree_of_ne mid j hjm hpos] at hj
      have hp : parent j < j := parent_lt j hpos
      exact inSubtree_down root j (ih (parent j) hp hj) hpos

theorem inSubtree_split (root j : Nat) (h : inSubtree root j = true) (hne : j ≠ root) :
    inSubtree (left root) j = true ∨ inSubtree (right root) j = true := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    have hpos : 0 < j := by
      by_contra hz
      have hj0 : j = 0 := by omega
      rw [hj0] at h
      simp [inSubtree_zero_of_ne root (by omega : root ≠ 0)] at h
    have hp : inSubtree root (parent j) = true := inSubtree_parent root j h hne
    by_cases hpar : parent j = root
    · have hc := (parent_eq_child j root hpos).mp hpar
      cases hc with
      | inl hl => exact Or.inl (by simp [hl, inSubtree_self])
      | inr hr => exact Or.inr (by simp [hr, inSubtree_self])
    · have hp' : parent j < j := parent_lt j hpos
      cases ih (parent j) hp' hp hpar with
      | inl hl =>
        exact Or.inl (inSubtree_trans (left root) (parent j) j hl
          (inSubtree_child_of_parent (parent j) j rfl))
      | inr hr =>
        exact Or.inr (inSubtree_trans (right root) (parent j) j hr
          (inSubtree_child_of_parent (parent j) j rfl))

theorem inSubtree_not_below (i j : Nat) (hij : j < i) : inSubtree i j = false := by
  by_contra h
  have h' : inSubtree i j = true := by simpa using h
  have : i ≤ j := inSubtree_le i j h'
  omega

theorem inSubtree_zero (j : Nat) : inSubtree 0 j = true := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hj : j = 0
    · simp [hj, inSubtree_self]
    · have hpos : 0 < j := Nat.pos_of_ne_zero hj
      rw [inSubtree_of_ne 0 j hj hpos]
      exact ih (parent j) (parent_lt j hpos)

theorem inSubtree_ancestor (a b j : Nat)
    (ha : inSubtree a j = true) (hb : inSubtree b j = true) :
    inSubtree a b = true ∨ inSubtree b a = true := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hab : a = b
    · simp [hab, inSubtree_self]
    · by_cases hja : j = a
      · subst hja
        exact Or.inr hb
      · by_cases hjb : j = b
        · subst hjb
          exact Or.inl ha
        · have hpos : 0 < j := by
            by_contra hz
            have hj0 : j = 0 := by omega
            rw [hj0] at ha
            simp [inSubtree_zero_of_ne a (by omega : a ≠ 0)] at ha
          exact ih (parent j) (parent_lt j hpos)
            (inSubtree_parent a j ha hja) (inSubtree_parent b j hb hjb)

def aget (a : List Nat) (i : Nat) : Nat := a.getD i 0

theorem aget_of_lt (a : List Nat) (i : Nat) (hi : i < a.length) : aget a i = a[i] := by
  simp [aget, List.getD_eq_getElem?_getD, hi]

theorem aget_set (a : List Nat) (i v k : Nat) (hi : i < a.length) :
    aget (a.set i v) k = if k = i then v else aget a k := by
  unfold aget
  grind [List.getD_eq_getElem?_getD, List.getElem?_set]

theorem count_set (a : List Nat) (i : Nat) (v x : Nat) (hi : i < a.length) :
    (a.set i v).count x =
      a.count x - (if a[i] = x then 1 else 0) + (if v = x then 1 else 0) := by
  induction a generalizing i with
  | nil => simp at hi
  | cons y ys ih =>
    cases i with
    | zero => grind [List.count_cons]
    | succ i =>
      have hi' : i < ys.length := by grind
      grind [List.count_cons]

def swap (a : List Nat) (i j : Nat) : List Nat :=
  if hi : i < a.length then
    if hj : j < a.length then
      if _h : i = j then a else (a.set i (a[j]'hj)).set j (a[i]'hi)
    else a
  else a

theorem swap_length (a : List Nat) (i j : Nat) : (swap a i j).length = a.length := by
  unfold swap; split_ifs <;> simp

theorem swap_count (a : List Nat) (i j x : Nat) : (swap a i j).count x = a.count x := by
  unfold swap
  split_ifs with hi hj hne <;> grind [count_set, List.getElem_set, List.length_set]

theorem swap_perm (a : List Nat) (i j : Nat) : List.Perm (swap a i j) a := by
  rw [List.perm_iff_count]; intro x; exact swap_count a i j x

theorem aget_swap_eq (a : List Nat) (i j : Nat) (hi : i < a.length) (hj : j < a.length)
    (hne : i ≠ j) (k : Nat) :
    aget (swap a i j) k = if k = i then aget a j else if k = j then aget a i else aget a k := by
  unfold swap
  simp only [hi, hj, hne, dite_true, dite_false]
  have hj' : j < (a.set i (a[j])).length := by simp [hj]
  rw [aget_set (a.set i (a[j])) j (a[i]) k hj']
  rw [aget_set a i (a[j]) k hi]
  by_cases hki : k = i <;> by_cases hkj : k = j
  · subst hki; subst hkj; exact absurd rfl hne
  · subst hki
    simp [hkj, hne, aget_of_lt a j hj]
  · subst hkj
    simp [hki, hne, aget_of_lt a i hi]
  · simp [hki, hkj]


def chooseLargest (a : List Nat) (i n : Nat) : Nat :=
  let l := left i
  let r := right i
  let best := if l < n ∧ aget a i < aget a l then l else i
  if r < n ∧ aget a best < aget a r then r else best

def maxHeapifyFuel (a : List Nat) (i n fuel : Nat) : List Nat :=
  match fuel with
  | 0 => a
  | fuel + 1 =>
    if i < n ∧ n ≤ a.length then
      let best := chooseLargest a i n
      if best = i then a
      else maxHeapifyFuel (swap a i best) best n fuel
    else a

def maxHeapify (a : List Nat) (i n : Nat) : List Nat :=
  maxHeapifyFuel a i n n

theorem maxHeapifyFuel_length (a : List Nat) (i n fuel : Nat) :
    (maxHeapifyFuel a i n fuel).length = a.length := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
    unfold maxHeapifyFuel
    by_cases h : i < n ∧ n ≤ a.length
    · simp only [h, dite_true]
      by_cases hb : chooseLargest a i n = i
      · simp [hb]
      · simp [hb, ih, swap_length]
    · simp [h]

theorem maxHeapifyFuel_count (a : List Nat) (i n fuel x : Nat) :
    (maxHeapifyFuel a i n fuel).count x = a.count x := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
    unfold maxHeapifyFuel
    by_cases h : i < n ∧ n ≤ a.length
    · simp only [h, dite_true]
      by_cases hb : chooseLargest a i n = i
      · simp [hb]
      · simp [hb, ih, swap_count]
    · simp [h]

theorem maxHeapify_perm (a : List Nat) (i n : Nat) :
    List.Perm (maxHeapify a i n) a := by
  rw [List.perm_iff_count]
  intro x
  simpa [maxHeapify] using maxHeapifyFuel_count a i n n x

def heapifyDown (a : List Nat) (i n : Nat) : List Nat :=
  match i with
  | 0 => maxHeapify a 0 n
  | i + 1 => heapifyDown (maxHeapify a (i + 1) n) i n

def buildMaxHeap (a : List Nat) : List Nat :=
  let n := a.length
  if n ≤ 1 then a else heapifyDown a (parent (n - 1)) n

def extract (a : List Nat) (heapSize : Nat) : List Nat :=
  match heapSize with
  | 0 => a
  | 1 => a
  | sz + 2 =>
    extract (maxHeapify (swap a 0 (sz + 1)) 0 (sz + 1)) (sz + 1)

def heapsort (a : List Nat) : List Nat :=
  let n := a.length
  if n ≤ 1 then a else extract (buildMaxHeap a) n

def inputPre (arr : List Int) : Bool :=
  arr.all (fun x => decide (0 ≤ x))

def heapsortChecked (arr : List Int) : Except String (List Int) :=
  if inputPre arr then
    .ok ((heapsort (arr.map fun x => x.toNat)).map Int.ofNat)
  else
    .error "Input must be List[Nat]"

example : heapsort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by native_decide
example : heapsort [] = [] := by native_decide
example : heapsort [42] = [42] := by native_decide
example : heapsort [2, 1] = [1, 2] := by native_decide
example : heapsort [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by native_decide
example : heapsort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsort [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : heapsort [2, 1] ≠ [2, 1] := by native_decide

#eval heapsort [3, 1, 2]
#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsortChecked [1, -1]

example : heapsortChecked [1, -1] = Except.error "Input must be List[Nat]" := by
  simp [heapsortChecked, inputPre]

def Pre (arr : List Nat) : Prop := ∀ x ∈ arr, 0 ≤ x

def sorted_prop (arr : List Nat) : Prop := List.Sorted (· ≤ ·) (heapsort arr)
def perm_prop (arr : List Nat) : Prop := List.Perm (heapsort arr) arr
def length_prop (arr : List Nat) : Prop := (heapsort arr).length = arr.length
def build_perm_prop (arr : List Nat) : Prop := List.Perm (buildMaxHeap arr) arr

theorem chooseLargest_cases (a : List Nat) (i n : Nat) :
    chooseLargest a i n = i ∨ chooseLargest a i n = left i ∨ chooseLargest a i n = right i := by
  unfold chooseLargest
  by_cases h1 : left i < n ∧ aget a i < aget a (left i)
  · by_cases h2 : right i < n ∧ aget a (left i) < aget a (right i)
    · right; right; simp [h1, h2]
    · right; left; simp [h1, h2]
  · by_cases h2 : right i < n ∧ aget a i < aget a (right i)
    · right; right; simp [h1, h2]
    · left; simp [h1, h2]

theorem chooseLargest_inSubtree (a : List Nat) (i n : Nat) :
    inSubtree i (chooseLargest a i n) = true := by
  rcases chooseLargest_cases a i n with h | h | h
  · simp [h, inSubtree_self]
  · simp [h, inSubtree_left]
  · simp [h, inSubtree_right]

theorem chooseLargest_lt (a : List Nat) (i n : Nat) (hi : i < n) :
    chooseLargest a i n < n := by
  rcases chooseLargest_cases a i n with h | h | h
  · simpa [h] using hi
  · have : left i < n := by
      by_contra hge
      have hnot : ¬ (left i < n ∧ aget a i < aget a (left i)) := by
        intro hc; exact hge hc.1
      unfold chooseLargest at h
      simp [hnot] at h
      by_cases h2 : right i < n ∧ aget a i < aget a (right i)
      · simp [h2] at h
        exact absurd h (by unfold left right; omega)
      · simp [h2] at h
        exact absurd h (by unfold left; omega)
    simpa [h] using this
  · have : right i < n := by
      unfold chooseLargest at h
      by_cases h1 : left i < n ∧ aget a i < aget a (left i)
      · by_cases h2 : right i < n ∧ aget a (left i) < aget a (right i)
        · exact h2.1
        · simp [h1, h2] at h
          exact absurd h (by unfold left right; omega)
      · by_cases h2 : right i < n ∧ aget a i < aget a (right i)
        · exact h2.1
        · simp [h1, h2] at h
          exact absurd h (by unfold right; omega)
    simpa [h] using this

theorem sub_shift (i k : Nat) : (i + 1) - (k + 1) = i - k := by omega

theorem heapifyDown_perm (a : List Nat) (i n : Nat) :
    List.Perm (heapifyDown a i n) a := by
  induction i generalizing a with
  | zero =>
    simpa [heapifyDown] using maxHeapify_perm a 0 n
  | succ i ih =>
    rw [heapifyDown]
    exact (ih _).trans (maxHeapify_perm a (i + 1) n)

theorem extract_perm (a : List Nat) (n : Nat) : List.Perm (extract a n) a := by
  induction n using Nat.strongRecOn generalizing a with
  | ind n ih =>
    cases n with
    | zero => simp [extract]
    | succ n =>
      cases n with
      | zero => simp [extract]
      | succ n =>
        rw [extract]
        refine (ih (n + 1) (by omega) _).trans ?_
        exact (maxHeapify_perm _ 0 (n + 1)).trans (swap_perm _ 0 (n + 1))

theorem build_perm_thm (arr : List Nat) : build_perm_prop arr := by
  unfold build_perm_prop buildMaxHeap
  by_cases h : arr.length ≤ 1
  · simp [h]
  · simp [h]
    exact heapifyDown_perm arr (parent (arr.length - 1)) arr.length

theorem perm_thm (arr : List Nat) : perm_prop arr := by
  unfold perm_prop heapsort
  by_cases h : arr.length ≤ 1
  · simp [h]
  · simp [h]
    exact (extract_perm _ _).trans (build_perm_thm arr)

theorem length_thm (arr : List Nat) : length_prop arr := by
  unfold length_prop
  exact (perm_thm arr).length_eq

theorem heapifyDown_eq_foldl (a : List Nat) (i n : Nat) :
    heapifyDown a i n =
      (List.range (i + 1)).foldl (fun acc k => maxHeapify acc (i - k) n) a := by
  induction i generalizing a with
  | zero => simp [heapifyDown]
  | succ i ih =>
    rw [heapifyDown, ih]
    conv_rhs => rw [List.range_succ_eq_map]
    rw [List.foldl_cons, List.foldl_map]
    apply congrArg (fun g => List.foldl g (maxHeapify a (i + 1) n) (List.range (i + 1)))
    funext acc k
    rw [sub_shift]

theorem extract_eq_foldl (a : List Nat) (n : Nat) :
    extract a n =
      (List.range (n - 1)).foldl
        (fun acc k => maxHeapify (swap acc 0 (n - 1 - k)) 0 (n - 1 - k)) a := by
  induction n using Nat.strongRecOn generalizing a with
  | ind n ih =>
    cases n with
    | zero => simp [extract]
    | succ n =>
      cases n with
      | zero => simp [extract]
      | succ n =>
        rw [extract]
        rw [ih (n + 1) (by omega)]
        have hn : n + 2 - 1 = n + 1 := by omega
        conv_rhs => rw [hn, List.range_succ_eq_map]
        rw [List.foldl_cons, List.foldl_map]
        apply congrArg (fun g =>
          List.foldl g (maxHeapify (swap a 0 (n + 1)) 0 (n + 1)) (List.range n))
        funext acc k
        simp [sub_shift]

def IsHeapRoot (a : List Nat) (root n : Nat) : Prop :=
  ∀ j, j < n → inSubtree root j = true → j ≠ root → aget a j ≤ aget a (parent j)

theorem IsHeapRoot_of_ge (a : List Nat) (root n : Nat) (h : n ≤ root) : IsHeapRoot a root n := by
  intro j hj hs _
  have : root ≤ j := inSubtree_le root j hs
  omega

theorem IsHeapRoot_mono (a : List Nat) (root n j : Nat) (h : IsHeapRoot a root n)
    (hs : inSubtree root j = true) : IsHeapRoot a j n := by
  intro k hk hsk hkne
  apply h k hk (inSubtree_trans root j k hs hsk)
  intro hkr
  exfalso
  have : j = root := by
    have h1 := inSubtree_le root j hs
    have hsk' : inSubtree j root = true := by simpa [hkr] using hsk
    have h2 := inSubtree_le j root hsk'
    omega
  exact hkne (hkr.trans this.symm)

theorem heap_root_ge (a : List Nat) (root n j : Nat) (h : IsHeapRoot a root n)
    (hj : j < n) (hs : inSubtree root j = true) : aget a j ≤ aget a root := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hje : j = root
    · subst hje; exact le_refl _
    · have hpos : 0 < j := by
        by_contra hz
        have hj0 : j = 0 := by omega
        rw [hj0] at hs
        simp [inSubtree_zero_of_ne root (by omega : root ≠ 0)] at hs
      have hp := inSubtree_parent root j hs hje
      have hplt : parent j < j := parent_lt j hpos
      have hpn : parent j < n := by omega
      exact le_trans (h j hj hs hje) (ih (parent j) hplt hpn hp)

theorem not_inSubtree_left_right (i : Nat) : inSubtree (left i) (right i) = false := by
  rw [inSubtree_of_ne (left i) (right i) (by unfold left right; omega) (by unfold right; omega)]
  rw [parent_right]
  exact inSubtree_not_below (left i) i (by unfold left; omega)

theorem not_inSubtree_right_left (i : Nat) : inSubtree (right i) (left i) = false := by
  exact inSubtree_not_below (right i) (left i) (by unfold left right; omega)

theorem children_disjoint (i j : Nat)
    (hl : inSubtree (left i) j = true) (hr : inSubtree (right i) j = true) : False := by
  rcases inSubtree_ancestor (left i) (right i) j hl hr with h | h
  · simp [not_inSubtree_left_right i] at h
  · simp [not_inSubtree_right_left i] at h

theorem chooseLargest_gt (a : List Nat) (i n : Nat) (hne : chooseLargest a i n ≠ i) :
    i < chooseLargest a i n := by
  rcases chooseLargest_cases a i n with h | h | h
  · exact absurd h hne
  · simpa [h] using left_gt i
  · simpa [h] using right_gt i

theorem chooseLargest_ge_i (a : List Nat) (i n : Nat) :
    aget a i ≤ aget a (chooseLargest a i n) := by
  unfold chooseLargest
  by_cases h1 : left i < n ∧ aget a i < aget a (left i)
  · by_cases h2 : right i < n ∧ aget a (left i) < aget a (right i)
    · simp [h1, h2]; exact le_of_lt (lt_trans h1.2 h2.2)
    · simp [h1, h2]; exact le_of_lt h1.2
  · by_cases h2 : right i < n ∧ aget a i < aget a (right i)
    · simp [h1, h2]; exact le_of_lt h2.2
    · simp [h1, h2]

theorem chooseLargest_ge_left (a : List Nat) (i n : Nat) (hl : left i < n) :
    aget a (left i) ≤ aget a (chooseLargest a i n) := by
  unfold chooseLargest
  by_cases h1 : left i < n ∧ aget a i < aget a (left i)
  · by_cases h2 : right i < n ∧ aget a (left i) < aget a (right i)
    · simp [h1, h2]; exact le_of_lt h2.2
    · simp [h1, h2]
  · by_cases h2 : right i < n ∧ aget a i < aget a (right i)
    · simp [h1, h2]
      have : ¬ aget a i < aget a (left i) := by intro hc; exact h1 ⟨hl, hc⟩
      have : aget a (left i) ≤ aget a i := by omega
      exact le_trans this (le_of_lt h2.2)
    · simp [h1, h2]
      have : ¬ aget a i < aget a (left i) := by intro hc; exact h1 ⟨hl, hc⟩
      omega

theorem chooseLargest_ge_right (a : List Nat) (i n : Nat) (hr : right i < n) :
    aget a (right i) ≤ aget a (chooseLargest a i n) := by
  unfold chooseLargest
  by_cases h1 : left i < n ∧ aget a i < aget a (left i)
  · by_cases h2 : right i < n ∧ aget a (left i) < aget a (right i)
    · simp [h1, h2]
    · simp [h1, h2]
      have : ¬ aget a (left i) < aget a (right i) := by intro hc; exact h2 ⟨hr, hc⟩
      omega
  · by_cases h2 : right i < n ∧ aget a i < aget a (right i)
    · simp [h1, h2]
    · simp [h1, h2]
      have : ¬ aget a i < aget a (right i) := by intro hc; exact h2 ⟨hr, hc⟩
      omega

theorem maxHeapifyFuel_outside (a : List Nat) (i n fuel j : Nat)
    (hj : inSubtree i j = false) :
    aget (maxHeapifyFuel a i n fuel) j = aget a j := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
    unfold maxHeapifyFuel
    by_cases h : i < n ∧ n ≤ a.length
    · rw [if_pos h]
      by_cases hb : chooseLargest a i n = i
      · simp [hb]
      · simp only [hb, ite_false]
        have hbest : inSubtree i (chooseLargest a i n) = true := chooseLargest_inSubtree a i n
        have hsub : inSubtree (chooseLargest a i n) j = false := by
          by_contra hs
          have hs' : inSubtree (chooseLargest a i n) j = true := by simpa using hs
          have : inSubtree i j = true :=
            inSubtree_trans i (chooseLargest a i n) j hbest hs'
          simp [hj] at this
        have hrec := ih (swap a i (chooseLargest a i n)) (chooseLargest a i n) hsub
        rw [hrec]
        have hne_i : j ≠ i := by
          intro eq; subst eq; simp [inSubtree_self] at hj
        have hne_b : j ≠ chooseLargest a i n := by
          intro eq; subst eq; simp [hbest] at hj
        have hi : i < a.length := Nat.lt_of_lt_of_le h.1 h.2
        have hbnd : chooseLargest a i n < a.length :=
          Nat.lt_of_lt_of_le (chooseLargest_lt a i n h.1) h.2
        have hne : i ≠ chooseLargest a i n := fun eq => hb eq.symm
        rw [aget_swap_eq a i (chooseLargest a i n) hi hbnd hne j]
        simp [hne_i, hne_b]
    · rw [if_neg h]

theorem IsHeapRoot_eq (a a' : List Nat) (root n : Nat) (h : IsHeapRoot a root n)
    (hget : ∀ k, k < n → inSubtree root k = true → aget a' k = aget a k) :
    IsHeapRoot a' root n := by
  intro j hj hs hne
  have hpos : 0 < j := by
    by_contra hz
    have hj0 : j = 0 := by omega
    rw [hj0] at hs
    simp [inSubtree_zero_of_ne root (by omega : root ≠ 0)] at hs
  have hpj : parent j < n := by
    have : parent j < j := parent_lt j hpos
    omega
  have hps : inSubtree root (parent j) = true := inSubtree_parent root j hs hne
  rw [hget j hj hs, hget (parent j) hpj hps]
  exact h j hj hs hne

theorem IsHeapRoot_shrink (a : List Nat) (root n m : Nat) (hm : m ≤ n)
    (h : IsHeapRoot a root n) : IsHeapRoot a root m := by
  intro j hj hs hne
  exact h j (Nat.lt_of_lt_of_le hj hm) hs hne

theorem aget_swap_at_i (a : List Nat) (i j : Nat) (hi : i < a.length) (hj : j < a.length)
    (hne : i ≠ j) : aget (swap a i j) i = aget a j := by
  rw [aget_swap_eq a i j hi hj hne i, if_pos rfl]

theorem aget_swap_at_j (a : List Nat) (i j : Nat) (hi : i < a.length) (hj : j < a.length)
    (hne : i ≠ j) : aget (swap a i j) j = aget a i := by
  rw [aget_swap_eq a i j hi hj hne j, if_neg hne.symm, if_pos rfl]

theorem aget_swap_at_ne (a : List Nat) (i j k : Nat) (hi : i < a.length) (hj : j < a.length)
    (hne : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    aget (swap a i j) k = aget a k := by
  rw [aget_swap_eq a i j hi hj hne k, if_neg hki, if_neg hkj]

theorem maxHeapifyFuel_bound (a : List Nat) (i n fuel X : Nat)
    (hX : ∀ j, j < n → inSubtree i j = true → aget a j ≤ X) :
    ∀ j, j < n → inSubtree i j = true → aget (maxHeapifyFuel a i n fuel) j ≤ X := by
  induction fuel generalizing a i with
  | zero =>
    intro j hj hs
    exact hX j hj hs
  | succ fuel ih =>
    intro j hj hs
    unfold maxHeapifyFuel
    by_cases h : i < n ∧ n ≤ a.length
    · rw [if_pos h]
      by_cases hb : chooseLargest a i n = i
      · simp [hb]
        exact hX j hj hs
      · simp only [hb, ite_false]
        let b := chooseLargest a i n
        have hne : i ≠ b := fun eq => hb (by simpa [b] using eq.symm)
        have hi : i < a.length := Nat.lt_of_lt_of_le h.1 h.2
        have hblt : b < n := by simpa [b] using chooseLargest_lt a i n h.1
        have hbl : b < a.length := Nat.lt_of_lt_of_le hblt h.2
        have hbb : inSubtree i b = true := by simpa [b] using chooseLargest_inSubtree a i n
        have hswap : ∀ k, k < n → inSubtree b k = true → aget (swap a i b) k ≤ X := by
          intro k hk hsk
          have hski : inSubtree i k = true := inSubtree_trans i b k hbb hsk
          have hkne : k ≠ i := by
            intro eq
            have hsk' : inSubtree b i = true := by simpa [eq] using hsk
            have hle : b ≤ i := inSubtree_le b i hsk'
            have hgt : i < b := by simpa [b] using chooseLargest_gt a i n hb
            omega
          by_cases hkb : k = b
          · rw [hkb, aget_swap_at_j a i b hi hbl hne]
            exact hX i h.1 (inSubtree_self i)
          · rw [aget_swap_at_ne a i b k hi hbl hne hkne hkb]
            exact hX k hk hski
        by_cases hjb : inSubtree b j = true
        · exact ih (swap a i b) b hswap j hj hjb
        · have hout : inSubtree b j = false := by simpa using hjb
          rw [maxHeapifyFuel_outside (swap a i b) b n fuel j hout]
          have hjne : j ≠ b := by
            intro eq
            have : inSubtree b j = true := by simpa [eq] using inSubtree_self b
            simp [hout] at this
          by_cases hji : j = i
          · rw [hji, aget_swap_at_i a i b hi hbl hne]
            exact hX b hblt hbb
          · rw [aget_swap_at_ne a i b j hi hbl hne hji hjne]
            exact hX j hj hs
    · rw [if_neg h]
      exact hX j hj hs

theorem maxHeapifyFuel_ge (a : List Nat) (i n fuel j : Nat) (hj : n ≤ j) :
    aget (maxHeapifyFuel a i n fuel) j = aget a j := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
    unfold maxHeapifyFuel
    by_cases h : i < n ∧ n ≤ a.length
    · rw [if_pos h]
      by_cases hb : chooseLargest a i n = i
      · simp [hb]
      · simp only [hb, ite_false]
        rw [ih (swap a i (chooseLargest a i n)) (chooseLargest a i n)]
        have hi : i < a.length := Nat.lt_of_lt_of_le h.1 h.2
        have hcl : chooseLargest a i n < n := chooseLargest_lt a i n h.1
        have hbl : chooseLargest a i n < a.length := Nat.lt_of_lt_of_le hcl h.2
        have hne : i ≠ chooseLargest a i n := fun eq => hb eq.symm
        rw [aget_swap_eq a i _ hi hbl hne j]
        have hji : j ≠ i := by omega
        have hjb : j ≠ chooseLargest a i n := by omega
        simp [hji, hjb]
    · rw [if_neg h]

theorem maxHeapifyFuel_heap (a : List Nat) (i n fuel : Nat)
    (hn : n ≤ a.length) (hfuel : i + fuel ≥ n)
    (hL : IsHeapRoot a (left i) n) (hR : IsHeapRoot a (right i) n) :
    IsHeapRoot (maxHeapifyFuel a i n fuel) i n := by
  induction fuel generalizing a i with
  | zero =>
    intro j hj hs _
    have : i ≤ j := inSubtree_le i j hs
    omega
  | succ fuel ih =>
    unfold maxHeapifyFuel
    by_cases h : i < n ∧ n ≤ a.length
    · rw [if_pos h]
      by_cases hb : chooseLargest a i n = i
      · simp only [hb, ite_true]
        intro j hj hs hne
        rcases inSubtree_split i j hs hne with hl | hr
        · by_cases hjl : j = left i
          · rw [hjl, parent_left]
            simpa [hb, hjl] using chooseLargest_ge_left a i n (by simpa [hjl] using hj)
          · exact hL j hj hl hjl
        · by_cases hjr : j = right i
          · rw [hjr, parent_right]
            simpa [hb, hjr] using chooseLargest_ge_right a i n (by simpa [hjr] using hj)
          · exact hR j hj hr hjr
      · simp only [hb, ite_false]
        let b := chooseLargest a i n
        have hne : i ≠ b := fun eq => hb (by simpa [b] using eq.symm)
        have hgt : i < b := by simpa [b] using chooseLargest_gt a i n hb
        have hblt : b < n := by simpa [b] using chooseLargest_lt a i n h.1
        have hi : i < a.length := Nat.lt_of_lt_of_le h.1 hn
        have hblen : b < a.length := Nat.lt_of_lt_of_le hblt hn
        have hfuel' : b + fuel ≥ n := by omega
        have hchild : b = left i ∨ b = right i := by
          rcases chooseLargest_cases a i n with c | c | c
          · exact absurd c hb
          · exact Or.inl (by simpa [b] using c)
          · exact Or.inr (by simpa [b] using c)
        have hHeapB : IsHeapRoot a b n := by
          rcases hchild with hc | hc
          · simpa [hc] using hL
          · simpa [hc] using hR
        have hAvoid (root : Nat) (hout_i : inSubtree root i = false)
            (hout_b : inSubtree root b = false) (hroot : IsHeapRoot a root n) :
            IsHeapRoot (swap a i b) root n := by
          apply IsHeapRoot_eq a (swap a i b) root n hroot
          intro k hk hs
          have hki : k ≠ i := by
            intro eq
            have : inSubtree root i = true := by simpa [eq] using hs
            simp [hout_i] at this
          have hkb : k ≠ b := by
            intro eq
            have : inSubtree root b = true := by simpa [eq] using hs
            simp [hout_b] at this
          exact aget_swap_at_ne a i b k hi hblen hne hki hkb
        have hLb : IsHeapRoot (swap a i b) (left b) n :=
          hAvoid (left b) (inSubtree_not_below (left b) i (by have := left_gt b; omega))
            (inSubtree_not_below (left b) b (left_gt b))
            (IsHeapRoot_mono a b n (left b) hHeapB (inSubtree_left b))
        have hRb : IsHeapRoot (swap a i b) (right b) n :=
          hAvoid (right b) (inSubtree_not_below (right b) i (by have := right_gt b; omega))
            (inSubtree_not_below (right b) b (right_gt b))
            (IsHeapRoot_mono a b n (right b) hHeapB (inSubtree_right b))
        have hnswap : n ≤ (swap a i b).length := by rw [swap_length]; exact hn
        have hrec : IsHeapRoot (maxHeapifyFuel (swap a i b) b n fuel) b n :=
          ih (swap a i b) b hnswap hfuel' hLb hRb
        let a' := maxHeapifyFuel (swap a i b) b n fuel
        have h_i : aget a' i = aget a b := by
          rw [maxHeapifyFuel_outside (swap a i b) b n fuel i (inSubtree_not_below b i hgt)]
          exact aget_swap_at_i a i b hi hblen hne
        intro j hj hs hjne
        by_cases hjb : inSubtree b j = true
        · by_cases hjbeq : j = b
          · rw [hjbeq]
            have hparent : parent b = i := by
              rcases hchild with hc | hc
              · simpa [hc] using parent_left i
              · simpa [hc] using parent_right i
            rw [hparent]
            have hX : ∀ k, k < n → inSubtree b k = true → aget (swap a i b) k ≤ aget a b := by
              intro k hk hsk
              have hkne : k ≠ i := by
                intro eq
                have hsk' : inSubtree b i = true := by simpa [eq] using hsk
                exact absurd (inSubtree_le b i hsk') (Nat.not_le_of_gt hgt)
              by_cases hkb : k = b
              · rw [hkb, aget_swap_at_j a i b hi hblen hne]
                simpa [b] using chooseLargest_ge_i a i n
              · rw [aget_swap_at_ne a i b k hi hblen hne hkne hkb]
                exact heap_root_ge a b n k hHeapB hk hsk
            have hfin := maxHeapifyFuel_bound (swap a i b) b n fuel (aget a b) hX b
              (by simpa [hjbeq] using hj) (inSubtree_self b)
            rw [h_i]
            simpa [a'] using hfin
          · exact by simpa [a'] using hrec j hj hjb hjbeq
        · have hout : inSubtree b j = false := by simpa using hjb
          have hpos : 0 < j := by
            by_contra hz
            have hj0 : j = 0 := by omega
            have hine : i ≠ 0 := by simpa [hj0] using hjne.symm
            rw [hj0] at hs
            simp [inSubtree_zero_of_ne i hine] at hs
          have not_here (hbj : inSubtree b j = true) : False := by
            have hf : false = true := by simpa [hbj] using hout
            cases hf
          rcases hchild with hc | hc
          · have hsub : inSubtree (right i) j = true := by
              rcases inSubtree_split i j hs hjne with hl | hr
              · exact False.elim (not_here (by simpa [hc] using hl))
              · exact hr
            by_cases hjr : j = right i
            · rw [hjr, parent_right]
              have hout' : inSubtree b (right i) = false := by simpa [hjr] using hout
              have hgetj : aget a' (right i) = aget a (right i) := by
                rw [maxHeapifyFuel_outside (swap a i b) b n fuel (right i) hout']
                have hrne_b : right i ≠ b := by
                  intro eq
                  have : left i = right i := by simpa [hc] using eq.symm
                  unfold left right at this
                  omega
                exact aget_swap_at_ne a i b (right i) hi hblen hne (by unfold right; omega) hrne_b
              rw [hgetj, h_i]
              simpa [b] using chooseLargest_ge_right a i n (by simpa [hjr] using hj)
            · have hold := hR j hj hsub hjr
              have hp_out : inSubtree b (parent j) = false := by
                by_contra hc'
                exact not_here (inSubtree_down b j (by simpa using hc') hpos)
              have hgj : aget a' j = aget a j := by
                rw [maxHeapifyFuel_outside (swap a i b) b n fuel j hout]
                have hjne_b : j ≠ b := by
                  intro eq
                  exact not_here (by simpa [eq] using inSubtree_self b)
                exact aget_swap_at_ne a i b j hi hblen hne hjne hjne_b
              have hgp : aget a' (parent j) = aget a (parent j) := by
                rw [maxHeapifyFuel_outside (swap a i b) b n fuel (parent j) hp_out]
                have hpne_i : parent j ≠ i := by
                  intro eq
                  rcases (parent_eq_child j i hpos).mp eq with hjl | hjr'
                  · have : inSubtree (left i) j = true := by simp [hjl, inSubtree_self]
                    exact children_disjoint i j this hsub
                  · exact hjr hjr'
                have hpne_b : parent j ≠ b := by
                  intro eq
                  exact not_here (inSubtree_down b j (by simpa [eq] using inSubtree_self b) hpos)
                exact aget_swap_at_ne a i b (parent j) hi hblen hne hpne_i hpne_b
              rw [hgj, hgp]
              exact hold
          · have hsub : inSubtree (left i) j = true := by
              rcases inSubtree_split i j hs hjne with hl | hr
              · exact hl
              · exact False.elim (not_here (by simpa [hc] using hr))
            by_cases hjl : j = left i
            · rw [hjl, parent_left]
              have hout' : inSubtree b (left i) = false := by simpa [hjl] using hout
              have hgetj : aget a' (left i) = aget a (left i) := by
                rw [maxHeapifyFuel_outside (swap a i b) b n fuel (left i) hout']
                have hlne_b : left i ≠ b := by
                  intro eq
                  have : left i = right i := by simpa [hc] using eq
                  unfold left right at this
                  omega
                exact aget_swap_at_ne a i b (left i) hi hblen hne (by unfold left; omega) hlne_b
              rw [hgetj, h_i]
              simpa [b] using chooseLargest_ge_left a i n (by simpa [hjl] using hj)
            · have hold := hL j hj hsub hjl
              have hp_out : inSubtree b (parent j) = false := by
                by_contra hc'
                exact not_here (inSubtree_down b j (by simpa using hc') hpos)
              have hgj : aget a' j = aget a j := by
                rw [maxHeapifyFuel_outside (swap a i b) b n fuel j hout]
                have hjne_b : j ≠ b := by
                  intro eq
                  exact not_here (by simpa [eq] using inSubtree_self b)
                exact aget_swap_at_ne a i b j hi hblen hne hjne hjne_b
              have hgp : aget a' (parent j) = aget a (parent j) := by
                rw [maxHeapifyFuel_outside (swap a i b) b n fuel (parent j) hp_out]
                have hpne_i : parent j ≠ i := by
                  intro eq
                  rcases (parent_eq_child j i hpos).mp eq with hjl' | hjr'
                  · exact hjl hjl'
                  · have : inSubtree (right i) j = true := by simp [hjr', inSubtree_self]
                    exact children_disjoint i j hsub this
                have hpne_b : parent j ≠ b := by
                  intro eq
                  exact not_here (inSubtree_down b j (by simpa [eq] using inSubtree_self b) hpos)
                exact aget_swap_at_ne a i b (parent j) hi hblen hne hpne_i hpne_b
              rw [hgj, hgp]
              exact hold
    · rw [if_neg h]
      exact IsHeapRoot_of_ge a i n (by omega)

theorem inSubtree_proper_ge (root j : Nat) (hs : inSubtree root j = true) (hne : j ≠ root) :
    left root ≤ j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    have hpos : 0 < j := by
      by_contra hz
      have hj0 : j = 0 := by omega
      have hrne : root ≠ 0 := by simpa [hj0] using hne.symm
      have hf : false = true := by
        simpa [hj0, inSubtree_zero_of_ne root hrne] using hs
      cases hf
    have hp := inSubtree_parent root j hs hne
    by_cases hpar : parent j = root
    · rcases (parent_eq_child j root hpos).mp hpar with h | h
      · simpa [h]
      · have : left root ≤ right root := by unfold left right; omega
        simpa [h] using this
    · have hplt : parent j < j := parent_lt j hpos
      exact le_trans (ih (parent j) hplt hp hpar) (Nat.le_of_lt hplt)

theorem IsHeapRoot_no_child (a : List Nat) (root n : Nat) (h : n ≤ left root) :
    IsHeapRoot a root n := by
  intro j hj hs hne
  have : left root ≤ j := inSubtree_proper_ge root j hs hne
  omega

theorem left_ge_of_after_parent (n j : Nat) (hn : 2 ≤ n) (hj : parent (n - 1) < j) :
    n ≤ left j := by
  have hpos : 0 < n - 1 := by omega
  have hp : parent (n - 1) = (n - 2) / 2 := parent_of_pos (n - 1) hpos
  have hq : (n - 2) / 2 < j := by simpa [hp] using hj
  have hq1 : (n - 2) / 2 + 1 ≤ j := Nat.succ_le_of_lt hq
  unfold left
  have hr : (n - 2) % 2 = 0 ∨ (n - 2) % 2 = 1 := by
    have := Nat.mod_lt (n - 2) (by decide : 0 < 2)
    omega
  have hdiv := Nat.div_add_mod (n - 2) 2
  rcases hr with hr | hr
  · have hmul : 2 * ((n - 2) / 2) = n - 2 := by omega
    have : 2 * ((n - 2) / 2 + 1) + 1 = n + 1 := by omega
    omega
  · have hmul : 2 * ((n - 2) / 2) = n - 3 := by omega
    have : 2 * ((n - 2) / 2 + 1) + 1 = n := by omega
    omega

theorem maxHeapify_heap (a : List Nat) (i n : Nat) (hn : n ≤ a.length)
    (hL : IsHeapRoot a (left i) n) (hR : IsHeapRoot a (right i) n) :
    IsHeapRoot (maxHeapify a i n) i n := by
  simpa [maxHeapify] using maxHeapifyFuel_heap a i n n hn (by omega) hL hR

theorem maxHeapify_ge (a : List Nat) (i n j : Nat) (hj : n ≤ j) :
    aget (maxHeapify a i n) j = aget a j := by
  simpa [maxHeapify] using maxHeapifyFuel_ge a i n n j hj

theorem maxHeapify_bound (a : List Nat) (i n X : Nat)
    (hX : ∀ j, j < n → inSubtree i j = true → aget a j ≤ X) :
    ∀ j, j < n → inSubtree i j = true → aget (maxHeapify a i n) j ≤ X := by
  simpa [maxHeapify] using maxHeapifyFuel_bound a i n n X hX

theorem subtree_avoids (i j k : Nat) (hij : i < j)
    (hout : inSubtree i j = false) (hk : inSubtree j k = true) :
    inSubtree i k = false := by
  by_contra hs
  have hs' : inSubtree i k = true := by simpa using hs
  rcases inSubtree_ancestor i j k hs' hk with h | h
  · have hf : false = true := by simpa [h] using hout
    cases hf
  · have : j ≤ i := inSubtree_le j i h
    omega

theorem maxHeapify_preserves_above (a : List Nat) (i n j : Nat)
    (hij : i < j) (hout : inSubtree i j = false) (hj : j < n) (h : IsHeapRoot a j n) :
    IsHeapRoot (maxHeapify a i n) j n := by
  apply IsHeapRoot_eq a (maxHeapify a i n) j n h
  intro k _hk hs
  have hkout : inSubtree i k = false := subtree_avoids i j k hij hout hs
  simpa [maxHeapify] using maxHeapifyFuel_outside a i n n k hkout

theorem heapifyDown_zero (a : List Nat) (n : Nat) :
    heapifyDown a 0 n = maxHeapify a 0 n := by
  unfold heapifyDown
  rfl

theorem heapifyDown_succ (a : List Nat) (i n : Nat) :
    heapifyDown a (i + 1) n = heapifyDown (maxHeapify a (i + 1) n) i n := by
  conv_lhs => unfold heapifyDown


theorem heapifyDown_heap (a : List Nat) (i n : Nat)
    (hn : n ≤ a.length)
    (hpre : ∀ j, i < j → j < n → IsHeapRoot a j n) :
    ∀ j, j < n → IsHeapRoot (heapifyDown a i n) j n := by
  induction i generalizing a with
  | zero =>
    intro j hj
    have hL : IsHeapRoot a (left 0) n := by
      by_cases hlt : left 0 < n
      · exact hpre (left 0) (by unfold left; omega) hlt
      · exact IsHeapRoot_of_ge a (left 0) n (by omega)
    have hR : IsHeapRoot a (right 0) n := by
      by_cases hlt : right 0 < n
      · exact hpre (right 0) (by unfold right; omega) hlt
      · exact IsHeapRoot_of_ge a (right 0) n (by omega)
    have h0 := maxHeapify_heap a 0 n hn hL hR
    rw [heapifyDown_zero]
    exact IsHeapRoot_mono (maxHeapify a 0 n) 0 n j h0 (inSubtree_zero j)
  | succ i ih =>
    intro j hj
    have hL : IsHeapRoot a (left (i + 1)) n := by
      by_cases hlt : left (i + 1) < n
      · exact hpre (left (i + 1)) (by unfold left; omega) hlt
      · exact IsHeapRoot_of_ge a (left (i + 1)) n (by omega)
    have hR : IsHeapRoot a (right (i + 1)) n := by
      by_cases hlt : right (i + 1) < n
      · exact hpre (right (i + 1)) (by unfold right; omega) hlt
      · exact IsHeapRoot_of_ge a (right (i + 1)) n (by omega)
    have hiHeap := maxHeapify_heap a (i + 1) n hn hL hR
    have hpre' : ∀ j, i < j → j < n → IsHeapRoot (maxHeapify a (i + 1) n) j n := by
      intro j hji hjn
      by_cases heq : j = i + 1
      · simpa [heq] using hiHeap
      · by_cases hin : inSubtree (i + 1) j = true
        · exact IsHeapRoot_mono (maxHeapify a (i + 1) n) (i + 1) n j hiHeap hin
        · have hgt : i + 1 < j := by omega
          have hout : inSubtree (i + 1) j = false := by simpa using hin
          exact maxHeapify_preserves_above a (i + 1) n j hgt hout hjn (hpre j (by omega) hjn)
    rw [heapifyDown_succ]
    have hn1 : n ≤ (maxHeapify a (i + 1) n).length := by
      rw [maxHeapify, maxHeapifyFuel_length]; exact hn
    exact ih (maxHeapify a (i + 1) n) hn1 hpre' j hj

theorem buildMaxHeap_length (a : List Nat) : (buildMaxHeap a).length = a.length :=
  (build_perm_thm a).length_eq

theorem buildMaxHeap_def (a : List Nat) (hn : 1 < a.length) :
    buildMaxHeap a = heapifyDown a (parent (a.length - 1)) a.length := by
  unfold buildMaxHeap
  simp [show ¬ a.length ≤ 1 from by omega]

theorem buildMaxHeap_heap (a : List Nat) (hn : 1 < a.length) :
    IsHeapRoot (buildMaxHeap a) 0 a.length := by
  rw [buildMaxHeap_def a hn]
  have hpre : ∀ j, parent (a.length - 1) < j → j < a.length → IsHeapRoot a j a.length := by
    intro j hj jn
    exact IsHeapRoot_no_child a j a.length (left_ge_of_after_parent a.length j (by omega) hj)
  exact heapifyDown_heap a (parent (a.length - 1)) a.length (le_refl _) hpre 0 (by omega)

structure ExtractInv (a : List Nat) (heapSize : Nat) : Prop where
  size_le : heapSize ≤ a.length
  heap : IsHeapRoot a 0 heapSize
  suffix_sorted : ∀ i j, heapSize ≤ i → i < j → j < a.length → aget a i ≤ aget a j
  heap_le_suffix : ∀ i j, i < heapSize → heapSize ≤ j → j < a.length → aget a i ≤ aget a j

theorem extract_step (a : List Nat) (m : Nat) (h : ExtractInv a (m + 1)) (hm : 0 < m) :
    ExtractInv (maxHeapify (swap a 0 m) 0 m) m := by
  have hm1 : m + 1 ≤ a.length := h.size_le
  have hmle : m < a.length := by omega
  have h0 : 0 < a.length := by omega
  have hne : (0 : Nat) ≠ m := by omega
  let a1 := swap a 0 m
  let a2 := maxHeapify a1 0 m
  have hlen1 : a1.length = a.length := by simpa [a1] using swap_length a 0 m
  have hlen2 : a2.length = a.length := by
    simp [a2, a1, maxHeapify, maxHeapifyFuel_length, swap_length]
  have hL : IsHeapRoot a (left 0) m := by
    by_cases hlt : left 0 < m
    · exact IsHeapRoot_shrink a (left 0) (m + 1) m (by omega)
        (IsHeapRoot_mono a 0 (m + 1) (left 0) h.heap (inSubtree_left 0))
    · exact IsHeapRoot_of_ge a (left 0) m (by omega)
  have hR : IsHeapRoot a (right 0) m := by
    by_cases hlt : right 0 < m
    · exact IsHeapRoot_shrink a (right 0) (m + 1) m (by omega)
        (IsHeapRoot_mono a 0 (m + 1) (right 0) h.heap (inSubtree_right 0))
    · exact IsHeapRoot_of_ge a (right 0) m (by omega)
  have hL1 : IsHeapRoot a1 (left 0) m := by
    apply IsHeapRoot_eq a a1 (left 0) m hL
    intro k hk hs
    have hk0 : k ≠ 0 := by
      intro eq
      have hf : false = true := by
        simpa [eq, inSubtree_zero_of_ne (left 0) (by unfold left; omega)] using hs
      cases hf
    exact aget_swap_at_ne a 0 m k h0 hmle hne hk0 (by omega : k ≠ m)
  have hR1 : IsHeapRoot a1 (right 0) m := by
    apply IsHeapRoot_eq a a1 (right 0) m hR
    intro k hk hs
    have hk0 : k ≠ 0 := by
      intro eq
      have hf : false = true := by
        simpa [eq, inSubtree_zero_of_ne (right 0) (by unfold right; omega)] using hs
      cases hf
    exact aget_swap_at_ne a 0 m k h0 hmle hne hk0 (by omega : k ≠ m)
  have hn1 : m ≤ a1.length := by simpa [hlen1] using (by omega : m ≤ a.length)
  have hheap : IsHeapRoot a2 0 m := by
    simpa [a2] using maxHeapify_heap a1 0 m hn1 hL1 hR1
  have hX : ∀ k, k < m → inSubtree 0 k = true → aget a1 k ≤ aget a 0 := by
    intro k hk _
    by_cases hk0 : k = 0
    · rw [hk0]
      simpa [a1] using
        (aget_swap_at_i a 0 m h0 hmle hne).trans_le
          (heap_root_ge a 0 (m + 1) m h.heap (by omega) (inSubtree_zero m))
    · have hget : aget a1 k = aget a k := by
        simpa [a1] using aget_swap_at_ne a 0 m k h0 hmle hne hk0 (by omega)
      rw [hget]
      exact heap_root_ge a 0 (m + 1) k h.heap (by omega) (inSubtree_zero k)
  have hbound : ∀ k, k < m → aget a2 k ≤ aget a 0 := by
    intro k hk
    simpa [a2] using maxHeapify_bound a1 0 m (aget a 0) hX k hk (inSubtree_zero k)
  have h_at_m : aget a2 m = aget a 0 := by
    have hge : aget a2 m = aget a1 m := by simpa [a2] using maxHeapify_ge a1 0 m m (le_refl m)
    simpa [a1] using hge.trans (aget_swap_at_j a 0 m h0 hmle hne)
  have htail : ∀ j, m < j → aget a2 j = aget a j := by
    intro j hj
    have hge : aget a2 j = aget a1 j := by
      simpa [a2] using maxHeapify_ge a1 0 m j (by omega)
    have hsw : aget a1 j = aget a j := by
      simpa [a1] using aget_swap_at_ne a 0 m j h0 hmle hne (by omega) (by omega)
    exact hge.trans hsw
  refine ⟨?size, hheap, ?suffix, ?bound⟩
  · rw [hlen2]; omega
  · intro i j hi hij hj
    have hjlen : j < a.length := by rw [← hlen2]; simpa [a2] using hj
    by_cases him : i = m
    · rw [him, h_at_m, htail j (by omega)]
      exact h.heap_le_suffix 0 j (by omega) (by omega) hjlen
    · have hi' : m + 1 ≤ i := by omega
      rw [htail i (by omega), htail j (by omega)]
      exact h.suffix_sorted i j hi' hij hjlen
  · intro i j hi hj hjl
    have hjlen : j < a.length := by rw [← hlen2]; simpa [a2] using hjl
    by_cases hjm : j = m
    · rw [hjm, h_at_m]
      exact hbound i hi
    · rw [htail j (by omega)]
      exact le_trans (hbound i hi) (h.heap_le_suffix 0 j (by omega) (by omega) hjlen)

theorem extract_index_sorted (heapSize : Nat) :
    ∀ a, ExtractInv a heapSize →
      ∀ i j, i < j → j < a.length →
        aget (extract a heapSize) i ≤ aget (extract a heapSize) j := by
  induction heapSize using Nat.strongRecOn with
  | ind heapSize ih =>
    intro a h i j hij hj
    match heapSize with
    | 0 =>
      unfold extract
      exact h.suffix_sorted i j (by omega) hij hj
    | 1 =>
      unfold extract
      by_cases hi : i = 0
      · rw [hi]
        exact h.heap_le_suffix 0 j (by omega) (by omega) hj
      · exact h.suffix_sorted i j (by omega) hij hj
    | sz + 2 =>
      have hm : 0 < sz + 1 := by omega
      have hstep := extract_step a (sz + 1) h hm
      have hlena :
          (maxHeapify (swap a 0 (sz + 1)) 0 (sz + 1)).length = a.length := by
        rw [maxHeapify, maxHeapifyFuel_length, swap_length]
      have hrec := ih (sz + 1) (by omega)
        (maxHeapify (swap a 0 (sz + 1)) 0 (sz + 1)) hstep i j hij (by simpa [hlena] using hj)
      have hdef :
          extract a (sz + 2) =
            extract (maxHeapify (swap a 0 (sz + 1)) 0 (sz + 1)) (sz + 1) := by
        conv_lhs => unfold extract

      simpa [hdef] using hrec

theorem sorted_of_index (a : List Nat)
    (h : ∀ i j, i < j → j < a.length → aget a i ≤ aget a j) :
    List.Sorted (· ≤ ·) a := by
  rw [List.Sorted, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa [aget_of_lt a i hi, aget_of_lt a j hj] using h i j hij hj

theorem build_extract_inv (a : List Nat) (hn : 1 < a.length) :
    ExtractInv (buildMaxHeap a) a.length := by
  refine ⟨?_, buildMaxHeap_heap a hn, ?_, ?_⟩
  · rw [buildMaxHeap_length]
  · intro i j hi hij hj
    rw [buildMaxHeap_length] at hj
    omega
  · intro i j hi hj hjl
    rw [buildMaxHeap_length] at hjl
    omega

theorem heapsort_def (a : List Nat) (hn : 1 < a.length) :
    heapsort a = extract (buildMaxHeap a) a.length := by
  unfold heapsort
  simp [show ¬ a.length ≤ 1 from by omega]

theorem sorted_thm (arr : List Nat) : sorted_prop arr := by
  unfold sorted_prop
  by_cases h : arr.length ≤ 1
  · rw [heapsort]
    simp only [h, ite_true]
    exact sorted_of_index arr (by
      intro i j hij hj
      omega)
  · have hn : 1 < arr.length := by omega
    rw [heapsort_def arr hn]
    apply sorted_of_index
    intro i j hij hj
    have hlen : (buildMaxHeap arr).length = arr.length := buildMaxHeap_length arr
    have hlenE : (extract (buildMaxHeap arr) arr.length).length = arr.length := by
      exact (extract_perm (buildMaxHeap arr) arr.length).length_eq.trans hlen
    have hj2 : j < (buildMaxHeap arr).length := by
      rw [hlen]
      simpa [hlenE] using hj
    exact extract_index_sorted arr.length (buildMaxHeap arr) (build_extract_inv arr hn)
      i j hij hj2

theorem heapsortChecked_error_thm (arr : List Int) (h : inputPre arr = false) :
    heapsortChecked arr = Except.error "Input must be List[Nat]" := by
  simp [heapsortChecked, h]

theorem heapsortChecked_ok_thm (arr : List Int) (h : inputPre arr = true) :
    heapsortChecked arr =
      Except.ok ((heapsort (arr.map fun x => x.toNat)).map Int.ofNat) := by
  simp [heapsortChecked, h]

theorem heapsort_mergeSort_thm (arr : List Nat) :
    heapsort arr = arr.mergeSort (· ≤ ·) := by
  have hperm : List.Perm (heapsort arr) (arr.mergeSort (· ≤ ·)) :=
    (perm_thm arr).trans (List.mergeSort_perm arr (· ≤ ·)).symm
  have hsorted : List.Sorted (· ≤ ·) (heapsort arr) := sorted_thm arr
  have hms : List.Sorted (· ≤ ·) (arr.mergeSort (· ≤ ·)) :=
    List.sorted_mergeSort' (· ≤ ·) arr
  exact List.eq_of_perm_of_sorted hperm hsorted hms

def Post_prop (arr : List Nat) : Prop := sorted_prop arr ∧ perm_prop arr ∧ length_prop arr

def isSorted : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: xs => decide (a ≤ b) && isSorted (b :: xs)

def propBool (xs : List Nat) : Bool :=
  isSorted (heapsort xs) &&
  ((heapsort xs).length == xs.length) &&
  ((heapsort xs).mergeSort == xs.mergeSort) &&
  ((buildMaxHeap xs).mergeSort == xs.mergeSort)

-- PBT for sorted_prop
#eval Plausible.Testable.check (∀ xs : List Nat, isSorted (heapsort xs) = true)
-- PBT for perm_prop
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).mergeSort = xs.mergeSort)
-- PBT for length_prop
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).length = xs.length)
-- PBT for build_perm_prop
#eval Plausible.Testable.check (∀ xs : List Nat, (buildMaxHeap xs).mergeSort = xs.mergeSort)
-- PBT for Post_prop and the sorted rearrangement
#eval Plausible.Testable.check (∀ xs : List Nat, heapsort xs = xs.mergeSort)
#eval Plausible.Testable.check (∀ xs : List Nat, propBool xs = true)

example : (List.range 6).all (fun n => propBool (List.range n)) = true := by native_decide
example : propBool [3, 1, 4, 1, 5] && propBool [7, 7, 7, 7] && propBool [5, 2, 4, 6, 1, 3] = true := by
  native_decide

theorem correctness_thm (arr : List Nat) (_h : Pre arr) : Post_prop arr :=
  ⟨sorted_thm arr, perm_thm arr, length_thm arr⟩

-- Imperative implementation
def heapsortImp (a : List Nat) : List Nat :=
  Id.run do
    let n := a.length
    if n ≤ 1 then
      return a
    let mut acc := a
    for k in List.range (parent (n - 1) + 1) do
      acc := maxHeapify acc (parent (n - 1) - k) n
    for k in List.range (n - 1) do
      let i := n - 1 - k
      acc := maxHeapify (swap acc 0 i) 0 i
    return acc


example : heapsortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
#eval heapsortImp [3, 1, 4, 1, 5]

theorem equivalence_thm (arr : List Nat) : heapsort arr = heapsortImp arr := by
  by_cases h : arr.length ≤ 1
  · simp [heapsort, heapsortImp, h]
  · simp [heapsort, heapsortImp, buildMaxHeap, h, heapifyDown_eq_foldl, extract_eq_foldl]

end heapsort_algorithm
