import Mathlib

/-!
# CLRS heapsort on zero-based arrays of natural numbers

Lists give an immutable model of the Python array: `swap` performs two indexed
updates, heap construction visits the internal nodes in decreasing order, and
extraction swaps the maximum into the last active slot before sifting down.
`List Nat` represents precisely the elementwise natural-number precondition;
`heapsortChecked` additionally models rejection of negative integer inputs.
The recursive sift uses a heap-size fuel bound: each swap moves strictly to a
larger child index, so this bound cannot truncate a valid sift.
-/

namespace heapsort_algorithm

deriving instance DecidableEq for Except

/-- The root is its own parent. Natural subtraction makes this valid at zero. -/
def parent (i : Nat) : Nat := (i - 1) / 2
def left (i : Nat) : Nat := 2 * i + 1
def right (i : Nat) : Nat := 2 * i + 2

/-- Total lookup; all indices used for a swap in heapsort are in bounds. -/
def val (a : List Nat) (i : Nat) : Nat := a.getD i 0

def swap (a : List Nat) (i j : Nat) : List Nat :=
  (a.set i (val a j)).set j (val a i)

/-- Strict comparisons preserve Python's choice of the left child on a tie. -/
def largest (a : List Nat) (i n : Nat) : Nat :=
  let m := if left i < n ∧ val a i < val a (left i) then left i else i
  if right i < n ∧ val a m < val a (right i) then right i else m

def sift : Nat → Nat → Nat → List Nat → List Nat
  | 0, _, _, a => a
  | fuel + 1, n, i, a =>
    let j := largest a i n
    if j = i then a else sift fuel n j (swap a i j)

def max_heapify (a : List Nat) (i heap_size : Nat) : List Nat :=
  sift heap_size heap_size i a

def buildLoop : Nat → Nat → List Nat → List Nat
  | 0, _, a => a
  | k + 1, n, a => buildLoop k n (max_heapify a k n)

def build_max_heap (a : List Nat) : List Nat :=
  if a.length ≤ 1 then a
  else buildLoop (parent (a.length - 1) + 1) a.length a

/-- `k` is the last active index; the zero case performs no extraction. -/
def extractLoop : Nat → List Nat → List Nat
  | 0, a => a
  | k + 1, a =>
    extractLoop k (max_heapify (swap a 0 (k + 1)) 0 (k + 1))

def heapsort (a : List Nat) : List Nat :=
  if a.length ≤ 1 then a
  else extractLoop (a.length - 1) (build_max_heap a)

/-- An integer-facing interface models the Python `ValueError` branch. -/
def heapsortChecked (a : List Int) : Except String (List Nat) :=
  if a.all (fun x => decide (0 ≤ x)) then .ok (heapsort (a.map Int.toNat))
  else .error "Input must be List[Nat]"

example : parent 0 = 0 ∧ parent 8 = 3 ∧ left 3 = 7 ∧ right 3 = 8 := by native_decide
example : heapsort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4] =
    [2, 4, 5, 7, 8, 13, 17, 20, 25] := by native_decide
example : heapsort [] = [] := by native_decide
example : heapsort [42] = [42] := by native_decide
example : heapsort [2, 1] = [1, 2] := by native_decide
example : heapsort [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by native_decide
example : heapsort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsort [3, 1, 2] ≠ [3, 2, 1] ∧ heapsort [2, 1] ≠ [2, 1] := by native_decide
example : heapsortChecked [1, -1] = .error "Input must be List[Nat]" := by native_decide
example : heapsortChecked [3, 1, 2] = .ok [1, 2, 3] := by native_decide
#eval build_max_heap [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]

/-- Lists and natural elements are guaranteed by the input type. -/
def Pre (_a : List Nat) : Prop := True

/-- A directed edge in the zero-based binary tree. -/
def Child (p c : Nat) : Prop := c = left p ∨ c = right p

/-- All edges whose parent is at least `lo` satisfy the max-heap condition. -/
def HeapFrom (a : List Nat) (lo n : Nat) : Prop :=
  ∀ p c, lo ≤ p → Child p c → c < n → val a c ≤ val a p

/-- A single node may need repair. Its parent already bounds its children. -/
def Repair (a : List Nat) (lo n i : Nat) : Prop :=
  (∀ p c, lo ≤ p → Child p c → c < n → p ≠ i → val a c ≤ val a p) ∧
  (∀ p c, lo ≤ p → Child p i → Child i c → c < n → val a c ≤ val a p)

/-- Every suffix element bounds all preceding elements. -/
def Suffix (a : List Nat) (n : Nat) : Prop :=
  ∀ p q, p < q → n ≤ q → q < a.length → val a p ≤ val a q

private theorem child_gt {p c : Nat} (h : Child p c) : p < c := by
  rcases h with h | h <;> simp only [left, right] at h <;> omega

private theorem child_parent_unique {p q c : Nat} (h : Child p c) (h' : Child q c) : p = q := by
  rcases h with h | h <;> rcases h' with h' | h' <;>
    simp only [left, right] at * <;> omega

private theorem child_parent (c : Nat) (h : 0 < c) : Child (parent c) c := by
  unfold Child parent left right
  omega

@[simp] private theorem length_swap (a : List Nat) (i j : Nat) :
    (swap a i j).length = a.length := by simp [swap]

private theorem at_swap (a : List Nat) {i j : Nat}
    (hi : i < a.length) (hj : j < a.length) (hij : i ≠ j) (k : Nat) :
    val (swap a i j) k = if k = i then val a j else if k = j then val a i else val a k := by
  by_cases hki : k = i
  · subst k
    simp [val, swap, List.getD, hi, hj, Ne.symm hij]
  · by_cases hkj : k = j
    · subst k
      simp [val, swap, List.getD, hi, hj, Ne.symm hij]
    · simp [val, swap, List.getD, hki, hkj, Ne.symm hki, Ne.symm hkj]

private theorem swap_perm (a : List Nat) {i j : Nat}
    (hi : i < a.length) (hj : j < a.length) : (swap a i j).Perm a := by
  simpa [swap, val, List.getD_eq_getElem, hi, hj] using List.set_set_perm hi hj

private theorem largest_spec (a : List Nat) (i n : Nat) :
    (largest a i n = i ∨ (Child i (largest a i n) ∧ largest a i n < n)) ∧
    val a i ≤ val a (largest a i n) ∧
    (∀ c, Child i c → c < n → val a c ≤ val a (largest a i n)) := by
  unfold largest
  split <;> dsimp only <;> split
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · simp_all [Child]
    · omega
    · intro c hc hn
      rcases hc with rfl | rfl <;> omega


private theorem repair_swap (a : List Nat) {lo n i : Nat}
    (hn : n ≤ a.length) (hlo : lo ≤ i) (h : Repair a lo n i)
    (hne : largest a i n ≠ i) :
    Repair (swap a i (largest a i n)) lo n (largest a i n) := by
  obtain ⟨hc, hm, hmax⟩ := largest_spec a i n
  obtain ⟨hc, hjn⟩ := hc.resolve_left hne
  have hij := child_gt hc
  have hi : i < a.length := by omega
  have hj : largest a i n < a.length := by omega
  have hs := at_swap a hi hj (Ne.symm hne)
  constructor
  · intro p c hp hpc hcn hpj
    have hpc' := child_gt hpc
    by_cases hpi : p = i
    · subst p
      rw [hs c, hs i]
      have hci : c ≠ i := by omega
      simp only [hci, ↓reduceIte]
      split
      · exact hm
      · exact hmax c hpc hcn
    · by_cases hci : c = i
      · subst c
        rw [hs i, hs p]
        simp only [hpi, hpj, ↓reduceIte]
        exact h.2 p (largest a i n) hp hpc hc hjn
      · have hcj : c ≠ largest a i n := by
          intro heq
          subst c
          exact hpi (child_parent_unique hpc hc)
        rw [hs c, hs p]
        simpa only [hci, hcj, hpi, hpj, ↓reduceIte] using h.1 p c hp hpc hcn hpi
  · intro p c hp hpj hjc hcn
    have hpi := child_parent_unique hpj hc
    subst p
    have hjc' := child_gt hjc
    have hci : c ≠ i := by omega
    have hcj : c ≠ largest a i n := by omega
    rw [hs c, hs i]
    simp only [hci, hcj, ↓reduceIte]
    exact h.1 (largest a i n) c (by omega) hjc hcn hne

@[simp] private theorem length_sift (fuel n i : Nat) (a : List Nat) :
    (sift fuel n i a).length = a.length := by
  induction fuel generalizing i a with
  | zero => rfl
  | succ fuel ih =>
    simp only [sift]
    split
    · rfl
    · rw [ih, length_swap]

@[simp] private theorem length_heapify (a : List Nat) (i n : Nat) :
    (max_heapify a i n).length = a.length := length_sift n n i a

private theorem sift_perm (fuel n i : Nat) (a : List Nat) (hn : n ≤ a.length) :
    (sift fuel n i a).Perm a := by
  induction fuel generalizing i a with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    simp only [sift]
    split
    · exact List.Perm.refl _
    · rename_i hne
      obtain ⟨hc, hjn⟩ := (largest_spec a i n).1.resolve_left hne
      have hij := child_gt hc
      exact (ih _ _ (by simpa)).trans (swap_perm a (by omega) (by omega))

private theorem sift_heap (fuel n i : Nat) (a : List Nat) {lo : Nat}
    (hn : n ≤ a.length) (hlo : lo ≤ i) (hf : n ≤ i + fuel)
    (h : Repair a lo n i) : HeapFrom (sift fuel n i a) lo n := by
  induction fuel generalizing i a with
  | zero =>
    intro p c hp hpc hcn
    have hpc' := child_gt hpc
    exact h.1 p c hp hpc hcn (by omega)
  | succ fuel ih =>
    simp only [sift]
    split
    · rename_i heq
      intro p c hp hpc hcn
      by_cases hpi : p = i
      · subst p
        simpa only [heq] using (largest_spec a i n).2.2 c hpc hcn
      · exact h.1 p c hp hpc hcn hpi
    · rename_i hne
      obtain ⟨hc, hjn⟩ := (largest_spec a i n).1.resolve_left hne
      have hij := child_gt hc
      exact ih _ _ (by simpa) (by omega) (by omega) (repair_swap a hn hlo h hne)

private theorem heapify_heap (a : List Nat) {lo n i : Nat}
    (hn : n ≤ a.length) (hlo : lo ≤ i) (h : Repair a lo n i) :
    HeapFrom (max_heapify a i n) lo n :=
  sift_heap n n i a hn hlo (by omega) h

private theorem swap_suffix (a : List Nat) {n i j : Nat}
    (hi : i < n) (hj : j < n) (hn : n ≤ a.length) (hne : i ≠ j)
    (h : Suffix a n) : Suffix (swap a i j) n := by
  intro p q hpq hnq hq
  have hiq : q ≠ i := by omega
  have hjq : q ≠ j := by omega
  have hq' : q < a.length := by simpa using hq
  rw [at_swap a (by omega) (by omega) hne p,
      at_swap a (by omega) (by omega) hne q]
  simp only [hiq, hjq, ↓reduceIte]
  split
  · exact h j q (by omega) hnq hq'
  · split
    · exact h i q (by omega) hnq hq'
    · exact h p q hpq hnq hq'

private theorem sift_suffix (fuel n i : Nat) (a : List Nat)
    (hn : n ≤ a.length) (h : Suffix a n) : Suffix (sift fuel n i a) n := by
  induction fuel generalizing i a with
  | zero => exact h
  | succ fuel ih =>
    simp only [sift]
    split
    · exact h
    · rename_i hne
      obtain ⟨hc, hjn⟩ := (largest_spec a i n).1.resolve_left hne
      have hij := child_gt hc
      exact ih _ _ (by simpa) (swap_suffix a (by omega) hjn hn (Ne.symm hne) h)

private theorem heap_root_max (a : List Nat) {n : Nat} (h : HeapFrom a 0 n)
    (k : Nat) (hk : k < n) : val a k ≤ val a 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk0 : k = 0
    · subst k; exact le_refl _
    · have hc := child_parent k (by omega)
      have hpk := child_gt hc
      exact (h (parent k) k (by omega) hc hk).trans (ih (parent k) hpk (by omega))


@[simp] private theorem length_buildLoop (k n : Nat) (a : List Nat) :
    (buildLoop k n a).length = a.length := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [buildLoop, ih, length_heapify]

@[simp] private theorem length_build (a : List Nat) :
    (build_max_heap a).length = a.length := by
  unfold build_max_heap
  split <;> simp

private theorem buildLoop_spec (k n : Nat) (a : List Nat)
    (hn : n ≤ a.length) (h : HeapFrom a k n) :
    (buildLoop k n a).Perm a ∧ HeapFrom (buildLoop k n a) 0 n := by
  induction k generalizing a with
  | zero => exact ⟨List.Perm.refl _, h⟩
  | succ k ih =>
    have hr : Repair a k n k := by
      constructor
      · intro p c hp hpc hcn hpk
        exact h p c (by omega) hpc hcn
      · intro p c hp hpk hkc hcn
        have := child_gt hpk
        omega
    have hh := heapify_heap a hn (le_refl k) hr
    have hi := ih (max_heapify a k n) (by simpa) hh
    exact ⟨hi.1.trans (sift_perm n n k a hn), hi.2⟩

/-- Heap construction establishes all heap edges and preserves multiplicities. -/
def build_heap_prop (a : List Nat) : Prop :=
  HeapFrom (build_max_heap a) 0 a.length ∧ (build_max_heap a).Perm a

theorem build_heap_thm (a : List Nat) : build_heap_prop a := by
  unfold build_heap_prop build_max_heap
  split
  · rename_i hn
    refine ⟨?_, List.Perm.refl _⟩
    intro p c hp hpc hcn
    have := child_gt hpc
    omega
  · apply And.symm
    apply buildLoop_spec _ _ a (le_refl _)
    intro p c hp hpc hcn
    simp only [parent] at hp
    rcases hpc with hc | hc <;> simp only [left, right] at hc <;> omega

private theorem extraction_repair (a : List Nat) (k : Nat)
    (hn : k + 2 ≤ a.length) (h : HeapFrom a 0 (k + 2)) :
    Repair (swap a 0 (k + 1)) 0 (k + 1) 0 := by
  have hs := at_swap a (i := 0) (j := k + 1) (by omega) (by omega) (by omega)
  constructor
  · intro p c hp hpc hcn hp0
    have hpc' := child_gt hpc
    have hc0 : c ≠ 0 := by omega
    have hck : c ≠ k + 1 := by omega
    have hpk : p ≠ k + 1 := by omega
    rw [hs c, hs p]
    simpa only [hc0, hck, hp0, hpk, ↓reduceIte] using h p c hp hpc (by omega)
  · intro p c hp hp0 h0c hcn
    have := child_gt hp0
    omega

private theorem extraction_suffix (a : List Nat) (k : Nat)
    (hn : k + 2 ≤ a.length) (hh : HeapFrom a 0 (k + 2))
    (h : Suffix a (k + 2)) : Suffix (swap a 0 (k + 1)) (k + 1) := by
  have hs := at_swap a (i := 0) (j := k + 1) (by omega) (by omega) (by omega)
  intro p q hpq hnq hq
  have hq' : q < a.length := by simpa using hq
  rw [hs p, hs q]
  by_cases hqk : q = k + 1
  · subst q
    have hq0 : k + 1 ≠ 0 := by omega
    have hpk : p ≠ k + 1 := by omega
    simp only [hq0, hpk, ↓reduceIte]
    split
    · exact heap_root_max a hh (k + 1) (by omega)
    · exact heap_root_max a hh p (by omega)
  · have hq0 : q ≠ 0 := by omega
    simp only [hq0, hqk, ↓reduceIte]
    split
    · exact h (k + 1) q (by omega) (by omega) hq'
    · split
      · exact h 0 q (by omega) (by omega) hq'
      · exact h p q hpq (by omega) hq'

private theorem extractLoop_spec (k : Nat) (a : List Nat)
    (hn : k + 1 ≤ a.length) (hh : HeapFrom a 0 (k + 1))
    (hs : Suffix a (k + 1)) :
    (extractLoop k a).Perm a ∧ Suffix (extractLoop k a) 1 := by
  induction k generalizing a with
  | zero => exact ⟨List.Perm.refl _, hs⟩
  | succ k ih =>
    have hr := extraction_repair a k hn hh
    have hh' := heapify_heap (swap a 0 (k + 1)) (by simpa using (show k + 1 ≤ a.length by omega))
      (le_refl 0) hr
    have hs' := sift_suffix (k + 1) (k + 1) 0 (swap a 0 (k + 1))
      (by simp only [length_swap]; omega) (extraction_suffix a k hn hh hs)
    have hi := ih (max_heapify (swap a 0 (k + 1)) 0 (k + 1)) (by simp only [length_heapify, length_swap]; omega) hh' hs'
    refine ⟨hi.1.trans ?_, hi.2⟩
    exact (sift_perm (k + 1) (k + 1) 0 (swap a 0 (k + 1))
      (by simp only [length_swap]; omega)).trans (swap_perm a (by omega) (by omega))

private theorem suffix_sorted (a : List Nat) (h : Suffix a 1) :
    a.Pairwise (· ≤ ·) := by
  apply List.pairwise_iff_getElem.mpr
  intro p q hp hq hpq
  simpa only [val, List.getD_eq_getElem a 0 hp, List.getD_eq_getElem a 0 hq]
    using h p q hpq (by omega) hq

private theorem heapsort_spec (a : List Nat) :
    (heapsort a).Perm a ∧ (heapsort a).Pairwise (· ≤ ·) := by
  unfold heapsort
  split
  · rename_i hn
    refine ⟨List.Perm.refl _, List.pairwise_iff_getElem.mpr ?_⟩
    intro p q hp hq hpq
    omega
  · rename_i hn
    have hl : a.length - 1 + 1 = a.length := by omega
    have hb := build_heap_thm a
    have hi := extractLoop_spec (a.length - 1) (build_max_heap a)
      (by simp [hl]) (by simpa only [hl] using hb.1)
      (by intro p q hpq hnq hq; simp only [length_build] at hq; omega)
    exact ⟨hi.1.trans hb.2, suffix_sorted _ hi.2⟩

/-- Ascending order, including repeated values. -/
def sorted_prop (a : List Nat) : Prop := (heapsort a).Pairwise (· ≤ ·)
theorem sorted_thm (a : List Nat) : sorted_prop a := (heapsort_spec a).2

/-- Exact multiset preservation, stronger than set equality. -/
def permutation_prop (a : List Nat) : Prop := (heapsort a).Perm a
theorem permutation_thm (a : List Nat) : permutation_prop a := (heapsort_spec a).1

def length_prop (a : List Nat) : Prop := (heapsort a).length = a.length
theorem length_thm (a : List Nat) : length_prop a := (permutation_thm a).length_eq

def multiplicity_prop (a : List Nat) (x : Nat) : Prop :=
  (heapsort a).count x = a.count x
theorem multiplicity_thm (a : List Nat) (x : Nat) : multiplicity_prop a x :=
  (permutation_thm a).count_eq x


/-- Agreement with an independently specified ascending sort. -/
def reference_sort_prop (a : List Nat) : Prop := heapsort a = a.mergeSort

theorem reference_sort_thm (a : List Nat) : reference_sort_prop a := by
  apply List.eq_of_perm_of_sorted
    ((permutation_thm a).trans (List.mergeSort_perm a _).symm)
    (sorted_thm a)
  exact List.sorted_mergeSort' (· ≤ ·) a

def idempotent_prop (a : List Nat) : Prop := heapsort (heapsort a) = heapsort a

theorem idempotent_thm (a : List Nat) : idempotent_prop a :=
  List.eq_of_perm_of_sorted (permutation_thm (heapsort a))
    (sorted_thm (heapsort a)) (sorted_thm a)

/-- Valid integer inputs succeed with an ordered permutation; invalid ones fail. -/
def checked_input_prop (a : List Int) : Prop :=
  match heapsortChecked a with
  | .ok out => (∀ x ∈ a, 0 ≤ x) ∧ (out.map Int.ofNat).Perm a ∧ out.Pairwise (· ≤ ·)
  | .error message => message = "Input must be List[Nat]" ∧ ∃ x ∈ a, x < 0

theorem checked_input_thm (a : List Int) : checked_input_prop a := by
  unfold checked_input_prop
  by_cases ha : a.all (fun x => decide (0 ≤ x)) = true
  · simp only [heapsortChecked, if_pos ha]
    have hnonneg : ∀ x ∈ a, 0 ≤ x := by simpa only [List.all_eq_true, decide_eq_true_eq] using ha
    have hcast : (a.map Int.toNat).map Int.ofNat = a := by
      rw [List.map_map]
      calc
        _ = a.map id := List.map_congr_left (fun x hx => Int.toNat_of_nonneg (hnonneg x hx))
        _ = a := List.map_id a
    refine ⟨hnonneg, ?_, sorted_thm _⟩
    simpa only [hcast] using (permutation_thm (a.map Int.toNat)).map Int.ofNat
  · simp only [heapsortChecked, if_neg ha]
    refine ⟨True.intro, ?_⟩
    simpa only [List.all_eq_true, decide_eq_true_eq, not_forall, not_le, exists_prop] using ha

/-- The full specification: ordered output, identical multiplicities and length,
reference-sort agreement, and idempotence. -/
def Post_prop (a : List Nat) : Prop :=
  sorted_prop a ∧ permutation_prop a ∧ length_prop a ∧
  (∀ x, multiplicity_prop a x) ∧ reference_sort_prop a ∧ idempotent_prop a

/-! Property-based tests. These checks are executable evidence in addition to
(the independently proved) universal theorems above. -/

/-- The finite, executable form of the max-heap edge condition. -/
def heapCheck (a : List Nat) (n : Nat) : Bool :=
  (List.range n).all fun p =>
    decide (left p < n → val a (left p) ≤ val a p) &&
    decide (right p < n → val a (right p) ≤ val a p)

-- PBT for build_heap_prop: both heap edges and exact multiplicities.
#eval Plausible.Testable.check (∀ a : List Nat,
  (heapCheck (build_max_heap a) a.length && decide ((build_max_heap a).Perm a)) = true)
  { numInst := 200, maxSize := 50 }

-- PBT for sorted_prop.
#eval Plausible.Testable.check (∀ a : List Nat,
  decide ((heapsort a).Pairwise (· ≤ ·)) = true) { numInst := 200, maxSize := 50 }

-- PBT for permutation_prop.
#eval Plausible.Testable.check (∀ a : List Nat,
  decide ((heapsort a).Perm a) = true) { numInst := 200, maxSize := 50 }

-- PBT for length_prop.
#eval Plausible.Testable.check (∀ a : List Nat,
  (heapsort a).length = a.length) { numInst := 200, maxSize := 50 }

-- PBT for multiplicity_prop, sampling the value as well as the input.
#eval Plausible.Testable.check (∀ (a : List Nat) (x : Nat),
  (heapsort a).count x = a.count x) { numInst := 200, maxSize := 50 }

-- PBT for reference_sort_prop.
#eval Plausible.Testable.check (∀ a : List Nat,
  heapsort a = a.mergeSort) { numInst := 200, maxSize := 50 }

-- PBT for idempotent_prop.
#eval Plausible.Testable.check (∀ a : List Nat,
  heapsort (heapsort a) = heapsort a) { numInst := 200, maxSize := 50 }

-- PBT for checked_input_prop, including negative integers and the error branch.
#eval Plausible.Testable.check (∀ a : List Int,
  (match heapsortChecked a with
  | .ok out => a.all (fun x => decide (0 ≤ x)) &&
      decide ((out.map Int.ofNat).Perm a) && decide (out.Pairwise (· ≤ ·))
  | .error message => (message == "Input must be List[Nat]") && a.any (fun x => decide (x < 0))) = true)
  { numInst := 200, maxSize := 50 }

/-- A Boolean form of the complete postcondition. Checking counts on the input
and output covers every possible present value; all other counts are zero. -/
def postCheck (a : List Nat) : Bool :=
  let out := heapsort a
  decide (out.Pairwise (· ≤ ·)) && decide (out.Perm a) &&
  (out.length == a.length) &&
  (a ++ out).all (fun x => out.count x == a.count x) &&
  (out == a.mergeSort) && (heapsort out == out)

-- Randomized PBT for Post_prop.
#eval Plausible.Testable.check (∀ a : List Nat, postCheck a = true)
  { numInst := 300, maxSize := 60 }

/-- All lists of the specified length over an initial segment of Nat. -/
def listsOfLength (alphabetSize : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (List.range alphabetSize).flatMap fun x =>
      (listsOfLength alphabetSize n).map (x :: ·)

/-- Exhaustive duplicate-heavy inputs: lengths 0–6 over {0,1,2,3}. -/
def smallInputs : List (List Nat) :=
  (List.range 7).flatMap (listsOfLength 4)

-- Bounded PBT for the whole postcondition: 5,461 inputs, including empty lists.
example : smallInputs.all postCheck = true := by native_decide
-- Bounded PBT for heap construction, including all short shapes and ties.
example : smallInputs.all (fun a =>
    heapCheck (build_max_heap a) a.length && decide ((build_max_heap a).Perm a)) = true := by
  native_decide
#eval smallInputs.length

theorem correctness (a : List Nat) : Pre a → Post_prop a := by
  intro _
  exact ⟨sorted_thm a, permutation_thm a, length_thm a,
    multiplicity_thm a, reference_sort_thm a, idempotent_thm a⟩


/-! Imperative implementation. The three loops carry mutable state. Sifting
uses the same heap-size bound as the functional version; after reaching a
fixed point, the remaining iterations leave both the array and index alone. -/

def siftStepImperative (n : Nat) (state : List Nat × Nat) : List Nat × Nat := Id.run do
  let mut result := state.1
  let mut index := state.2
  let l := left index
  let r := right index
  let mut biggest := index
  if l < n ∧ val result index < val result l then
    biggest := l
  if r < n ∧ val result biggest < val result r then
    biggest := r
  if biggest ≠ index then
    result := swap result index biggest
    index := biggest
  return (result, index)

def siftImperative (fuel n i : Nat) (a : List Nat) : List Nat := Id.run do
  let mut state := (a, i)
  for _ in (List.range fuel).reverse do
    state := siftStepImperative n state
  return state.1

def max_heapifyImperative (a : List Nat) (i heap_size : Nat) : List Nat :=
  siftImperative heap_size heap_size i a

def build_max_heapImperative (a : List Nat) : List Nat := Id.run do
  let mut result := a
  let n := result.length
  if n ≤ 1 then return result
  for i in (List.range (parent (n - 1) + 1)).reverse do
    result := max_heapifyImperative result i n
  return result

def heapsortImperative (a : List Nat) : List Nat := Id.run do
  if a.length ≤ 1 then return a
  let mut result := build_max_heapImperative a
  for i in (List.range (a.length - 1)).reverse do
    let last := i + 1
    result := swap result 0 last
    result := max_heapifyImperative result 0 last
  return result

example : heapsortImperative [] = [] := by native_decide
example : heapsortImperative [42] = [42] := by native_decide
example : heapsortImperative [2, 1] = [1, 2] := by native_decide
example : heapsortImperative [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsortImperative [5, 13, 2, 25, 7, 17, 20, 8, 4] =
    [2, 4, 5, 7, 8, 13, 17, 20, 25] := by native_decide
example : heapsortImperative [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsortImperative [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] =
    [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by native_decide
#eval heapsortImperative [9, 8, 7, 6, 5, 4, 3, 2, 1]
#eval Plausible.Testable.check (∀ a : List Nat, heapsort a = heapsortImperative a)
  { numInst := 300, maxSize := 60 }
example : smallInputs.all (fun a => heapsort a == heapsortImperative a) = true := by native_decide

private theorem siftStepImperative_eq (a : List Nat) (i n : Nat) :
    siftStepImperative n (a, i) =
      if largest a i n = i then (a, i) else (swap a i (largest a i n), largest a i n) := by
  simp only [siftStepImperative, largest]
  split_ifs <;> simp_all

private theorem sift_stopped (fuel n i : Nat) (a : List Nat) (h : largest a i n = i) :
    sift fuel n i a = a := by
  cases fuel <;> simp [sift, h]

private theorem sift_fold (fuel n i : Nat) (a : List Nat) :
    ((List.range fuel).reverse.foldl (fun s _ => siftStepImperative n s) (a, i)).1 =
      sift fuel n i a := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.foldl_cons, siftStepImperative_eq]
    by_cases h : largest a i n = i
    · simp only [h, ↓reduceIte, ih, sift_stopped _ _ _ _ h, sift]
    · simp only [h, ↓reduceIte, ih, sift]

private theorem heapifyImperative_eq (a : List Nat) (i n : Nat) :
    max_heapifyImperative a i n = max_heapify a i n := by
  simpa [max_heapifyImperative, siftImperative, max_heapify] using sift_fold n n i a

private theorem build_fold (k n : Nat) (a : List Nat) :
    (List.range k).reverse.foldl (fun a i => max_heapifyImperative a i n) a = buildLoop k n a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.foldl_cons]
    rw [ih, heapifyImperative_eq]
    rfl

private theorem buildImperative_eq (a : List Nat) :
    build_max_heapImperative a = build_max_heap a := by
  by_cases hn : a.length ≤ 1 <;>
    simp [build_max_heapImperative, build_max_heap, hn, -List.foldl_reverse, build_fold]

private theorem extract_fold (k : Nat) (a : List Nat) :
    (List.range k).reverse.foldl
      (fun a i => max_heapifyImperative (swap a 0 (i + 1)) 0 (i + 1)) a = extractLoop k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.foldl_cons]
    rw [ih, heapifyImperative_eq]
    rfl

/-- The mutable loops compute exactly the functional heapsort, on every input. -/
theorem functional_eq_imperative (a : List Nat) : heapsort a = heapsortImperative a := by
  by_cases hn : a.length ≤ 1 <;>
    simp [heapsortImperative, heapsort, hn, -List.foldl_reverse, extract_fold, buildImperative_eq]

end heapsort_algorithm
