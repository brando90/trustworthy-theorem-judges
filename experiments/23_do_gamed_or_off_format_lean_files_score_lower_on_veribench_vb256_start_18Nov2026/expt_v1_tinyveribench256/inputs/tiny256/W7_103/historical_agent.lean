import Mathlib
namespace Agent

/-!
# CLRS heapsort, with zero-based indices

The input type `List Nat` encodes the Python precondition: booleans, negative
integers and non-lists are not admissible inputs. Array updates are pure in the
functional implementation. The active heap is a prefix of the array; extraction
leaves the sorted suffix in place. Heapify uses a decreasing fuel counter bounded
by the heap size (a descent always moves to a strictly larger index).
-/

namespace heapsort_algorithm

deriving instance DecidableEq for Except

def parent (i : Nat) : Nat := (i - 1) / 2
def left (i : Nat) : Nat := 2 * i + 1
def right (i : Nat) : Nat := 2 * i + 2

/-- Ties are left untouched, exactly as with Python's strict comparisons. -/
def largest (a : Array Nat) (i n : Nat) : Nat :=
  let l := left i
  let r := right i
  let j := if l < n && a[i]! < a[l]! then l else i
  if r < n && a[j]! < a[r]! then r else j

/-- The total swap also makes the helpers defined outside their intended bounds. -/
def swap (a : Array Nat) (i j : Nat) : Array Nat := a.swapIfInBounds i j

def sift : Nat → Array Nat → Nat → Nat → Array Nat
  | 0, a, _, _ => a
  | fuel + 1, a, i, n =>
      let j := largest a i n
      if j = i then a else sift fuel (swap a i j) j n

def max_heapify (a : Array Nat) (i n : Nat) : Array Nat := sift n a i n

/-- Visit k-1, ..., 0. -/
def buildLoop : Nat → Array Nat → Array Nat
  | 0, a => a
  | k + 1, a => buildLoop k (max_heapify a k a.size)

def build_max_heap (xs : List Nat) : Array Nat :=
  if xs.length ≤ 1 then xs.toArray
  else buildLoop (parent (xs.length - 1) + 1) xs.toArray

/-- Visit k, ..., 1, placing the maximum at k at each step. -/
def extractLoop : Nat → Array Nat → Array Nat
  | 0, a => a
  | k + 1, a => extractLoop k (max_heapify (swap a 0 (k + 1)) 0 (k + 1))

def heapsort (xs : List Nat) : List Nat :=
  if xs.length ≤ 1 then xs
  else (extractLoop (xs.length - 1) (build_max_heap xs)).toList

/-- A boundary adapter for integer lists. Negative entries raise the same
precondition error as Python. Other ill-typed Python values are excluded by the
Lean input types rather than silently coerced. -/
def heapsortChecked (xs : List Int) : Except String (List Nat) :=
  if xs.all (fun z => decide (0 ≤ z)) then
    .ok (heapsort (xs.map Int.toNat))
  else .error "Input must be List[Nat]"

example : heapsortChecked [1, -1] = .error "Input must be List[Nat]" := by native_decide
example : heapsortChecked [3, 1, 2] = .ok [1, 2, 3] := by native_decide
example : (parent 0, parent 1, parent 2, parent 3, left 2, right 2) =
    (0, 0, 0, 1, 5, 6) := by native_decide

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
example : heapsort [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : heapsort [2, 1] ≠ [2, 1] := by native_decide
#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]

/-- Every value of the typed input domain satisfies the Python precondition. -/
def Pre (_xs : List Nat) : Prop := True


@[simp] theorem size_swap (a : Array Nat) (i j : Nat) :
    (swap a i j).size = a.size := by simp [swap]

theorem swap_perm (a : Array Nat) (i j : Nat) :
    (swap a i j).toList.Perm a.toList := by
  unfold swap Array.swapIfInBounds
  split <;> (try split)
  · exact Array.perm_iff_toList_perm.mp (Array.swap_perm _ _)
  all_goals exact List.Perm.refl _

theorem sift_perm (fuel : Nat) (a : Array Nat) (i n : Nat) :
    (sift fuel a i n).toList.Perm a.toList := by
  induction fuel generalizing a i with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    simp only [sift]
    split
    · exact List.Perm.refl _
    · exact (ih _ _).trans (swap_perm _ _ _)

@[simp] theorem size_sift (fuel : Nat) (a : Array Nat) (i n : Nat) :
    (sift fuel a i n).size = a.size := by
  simpa using (sift_perm fuel a i n).length_eq

@[simp] theorem size_heapify (a : Array Nat) (i n : Nat) :
    (max_heapify a i n).size = a.size := size_sift _ _ _ _

theorem buildLoop_perm (k : Nat) (a : Array Nat) :
    (buildLoop k a).toList.Perm a.toList := by
  induction k generalizing a with
  | zero => exact List.Perm.refl _
  | succ k ih => exact (ih _).trans (sift_perm _ _ _ _)

theorem build_perm (xs : List Nat) : (build_max_heap xs).toList.Perm xs := by
  unfold build_max_heap
  split
  · simp
  · simpa using buildLoop_perm (parent (xs.length - 1) + 1) xs.toArray

@[simp] theorem size_build (xs : List Nat) : (build_max_heap xs).size = xs.length := by
  simpa using (build_perm xs).length_eq

theorem extractLoop_perm (k : Nat) (a : Array Nat) :
    (extractLoop k a).toList.Perm a.toList := by
  induction k generalizing a with
  | zero => exact List.Perm.refl _
  | succ k ih => exact (ih _).trans ((sift_perm _ _ _ _).trans (swap_perm _ _ _))

/-- An edge of the zero-based complete binary tree. -/
def Child (p c : Nat) : Prop := c = left p ∨ c = right p

theorem child_lt {p c : Nat} (h : Child p c) : p < c := by
  rcases h with h | h <;> simp only [left, right] at h <;> omega

theorem child_unique {p q c : Nat} (h : Child p c) (h' : Child q c) : p = q := by
  unfold Child left right at *
  omega

theorem child_parent {c : Nat} (h : 0 < c) : Child (parent c) c := by
  unfold Child parent left right
  omega

/-- All edges whose parent is at least lo satisfy the max-heap order. -/
def HeapFrom (a : Array Nat) (n lo : Nat) : Prop :=
  ∀ p c, lo ≤ p → c < n → Child p c → a[c]! ≤ a[p]!

/-- A single node i may need repair. -/
def Repair (a : Array Nat) (n lo i : Nat) : Prop :=
  (∀ p c, lo ≤ p → p ≠ i → c < n → Child p c → a[c]! ≤ a[p]!) ∧
  (∀ p c, lo ≤ p → Child p i → c < n → Child i c → a[c]! ≤ a[p]!)

theorem largest_spec (a : Array Nat) (i n : Nat) :
    (largest a i n = i ∨ (Child i (largest a i n) ∧ largest a i n < n)) ∧
    a[i]! ≤ a[largest a i n]! ∧
    (∀ c, Child i c → c < n → a[c]! ≤ a[largest a i n]!) := by
  unfold largest
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  split <;> split <;> simp_all [Child] <;> omega

theorem get_swap (a : Array Nat) (i j k : Nat)
    (hi : i < a.size) (hj : j < a.size) (hk : k < a.size) :
    (swap a i j)[k]! = if k = i then a[j]! else if k = j then a[i]! else a[k]! := by
  simp [swap, Array.swapIfInBounds, hi, hj, getElem!_pos,
    hk, Array.getElem_swap]


theorem repair_step (a : Array Nat) (n lo i : Nat)
    (hn : n ≤ a.size) (hi : i < n) (hlo : lo ≤ i)
    (hr : Repair a n lo i) (hne : largest a i n ≠ i) :
    Repair (swap a i (largest a i n)) n lo (largest a i n) := by
  obtain ⟨hj, hmax, hcmax⟩ := largest_spec a i n
  obtain ⟨hcj, hjn⟩ := hj.resolve_left hne
  have hij := child_lt hcj
  have his : i < a.size := by omega
  have hjs : largest a i n < a.size := by omega
  constructor
  · intro p c hp hpj hcn hpc
    have hlt := child_lt hpc
    have hps : p < a.size := by omega
    have hcs : c < a.size := by omega
    rw [get_swap a i _ c his hjs hcs, get_swap a i _ p his hjs hps]
    by_cases hpi : p = i
    · subst p
      have hci : c ≠ i := by omega
      simp only [if_neg hci]
      split
      · exact hmax
      · exact hcmax c hpc hcn
    · by_cases hci : c = i
      · subst c
        simp only [if_neg hpi, if_neg hpj]
        exact hr.2 p _ hp hpc hjn hcj
      · have hcne : c ≠ largest a i n := by
          intro he
          subst c
          exact hpi (child_unique hpc hcj)
        simp only [if_neg hci, if_neg hcne, if_neg hpi, if_neg hpj]
        exact hr.1 p c hp hpi hcn hpc
  · intro p c hp hpj hcn hjc
    have hpi : p = i := child_unique hpj hcj
    subst p
    have hjc_lt := child_lt hjc
    have hci : c ≠ i := by omega
    have hcne : c ≠ largest a i n := by omega
    rw [get_swap a i _ c his hjs (by omega), get_swap a i _ i his hjs his]
    simp only [if_neg hci, if_neg hcne]
    exact hr.1 _ c (by omega) hne hcn hjc

theorem sift_heap (fuel : Nat) (a : Array Nat) (n lo i : Nat)
    (hn : n ≤ a.size) (hi : i < n) (hlo : lo ≤ i)
    (hf : n - i ≤ fuel) (hr : Repair a n lo i) :
    HeapFrom (sift fuel a i n) n lo := by
  induction fuel generalizing a i with
  | zero => omega
  | succ fuel ih =>
    rw [sift]
    split
    · rename_i he
      intro p c hp hcn hpc
      by_cases hpi : p = i
      · subst p
        have h := (largest_spec a i n).2.2 c hpc hcn
        simpa only [he] using h
      · exact hr.1 p c hp hpi hcn hpc
    · rename_i he
      obtain ⟨hc, hjn⟩ := (largest_spec a i n).1.resolve_left he
      have hij := child_lt hc
      apply ih (swap a i (largest a i n)) (largest a i n)
      · simpa using hn
      · exact hjn
      · omega
      · omega
      · exact repair_step a n lo i hn hi hlo hr he

theorem heapify_heap (a : Array Nat) (n i : Nat)
    (hn : n ≤ a.size) (hi : i < n) (hh : HeapFrom a n (i + 1)) :
    HeapFrom (max_heapify a i n) n i := by
  apply sift_heap n a n i i hn hi (by omega) (by omega)
  constructor
  · intro p c hp hpi hcn hpc
    exact hh p c (by omega) hcn hpc
  · intro p c hp hpi
    have := child_lt hpi
    omega

theorem sift_frame (fuel : Nat) (a : Array Nat) (i n k : Nat)
    (hn : n ≤ a.size) (hi : i < n) (hkn : n ≤ k) (hk : k < a.size) :
    (sift fuel a i n)[k]! = a[k]! := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
    rw [sift]
    split
    · rfl
    · rename_i he
      obtain ⟨hc, hjn⟩ := (largest_spec a i n).1.resolve_left he
      rw [ih _ _ (by simpa using hn) hjn (by simpa using hk)]
      rw [get_swap a i _ k (by omega) (by omega) hk]
      simp only [if_neg (show k ≠ i by omega),
        if_neg (show k ≠ largest a i n by omega)]

theorem sift_bound (fuel : Nat) (a : Array Nat) (i n : Nat) (P : Nat → Prop)
    (hn : n ≤ a.size) (hi : i < n) (hb : ∀ k, k < n → P a[k]!) :
    ∀ k, k < n → P (sift fuel a i n)[k]! := by
  induction fuel generalizing a i with
  | zero => exact hb
  | succ fuel ih =>
    rw [sift]
    split
    · exact hb
    · rename_i he
      obtain ⟨hc, hjn⟩ := (largest_spec a i n).1.resolve_left he
      apply ih _ _ (by simpa using hn) hjn
      intro k hk
      rw [get_swap a i _ k (by omega) (by omega) (by omega)]
      split
      · exact hb _ hjn
      · split
        · exact hb _ hi
        · exact hb _ hk


theorem buildLoop_heap (k : Nat) (a : Array Nat) (hk : k ≤ a.size)
    (hh : HeapFrom a a.size k) : HeapFrom (buildLoop k a) a.size 0 := by
  induction k generalizing a with
  | zero => exact hh
  | succ k ih =>
    have h := heapify_heap a a.size k (by omega) (by omega) hh
    have h' := ih (max_heapify a k a.size) (by simp; omega) (by simpa using h)
    simpa only [buildLoop, size_heapify] using h'

theorem build_heap (xs : List Nat) : HeapFrom (build_max_heap xs) xs.length 0 := by
  unfold build_max_heap
  split
  · rename_i hs
    intro p c hp hc hpc
    have h := child_lt hpc
    omega
  · apply buildLoop_heap
    · simp only [List.size_toArray]
      unfold parent
      omega
    · intro p c hp hc hpc
      simp only [List.size_toArray] at hc
      unfold parent at hp
      unfold Child left right at hpc
      omega

theorem heap_root_max (a : Array Nat) (n : Nat) (hh : HeapFrom a n 0) :
    ∀ c, c < n → a[c]! ≤ a[0]! := by
  intro c
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro hc
    by_cases hz : c = 0
    · subst c; exact le_rfl
    · have he := child_parent (show 0 < c by omega)
      have hlt := child_lt he
      exact (hh _ c (by omega) hc he).trans (ih _ hlt (by omega))

/-- Every suffix element dominates every earlier element. This includes both
sortedness of the suffix and the partition between heap and suffix. -/
def Tail (a : Array Nat) (k : Nat) : Prop :=
  ∀ p q, p < q → k ≤ q → q < a.size → a[p]! ≤ a[q]!

theorem heapify_tail (a : Array Nat) (n : Nat) (hn : n ≤ a.size)
    (hpos : 0 < n) (ht : Tail a n) : Tail (max_heapify a 0 n) n := by
  intro p q hpq hnq hq
  have hqa : q < a.size := by simpa using hq
  change (sift n a 0 n)[p]! ≤ (sift n a 0 n)[q]!
  rw [sift_frame n a 0 n q hn hpos hnq hqa]
  by_cases hp : p < n
  · apply sift_bound n a 0 n (fun x => x ≤ a[q]!) hn hpos _ p hp
    intro k hk
    exact ht k q (by omega) hnq hqa
  · rw [sift_frame n a 0 n p hn hpos (by omega) (by omega)]
    exact ht p q hpq hnq hqa

theorem extract_step (a : Array Nat) (k : Nat) (hk : k + 1 < a.size)
    (hh : HeapFrom a (k + 2) 0) (ht : Tail a (k + 2)) :
    HeapFrom (max_heapify (swap a 0 (k + 1)) 0 (k + 1)) (k + 1) 0 ∧
    Tail (max_heapify (swap a 0 (k + 1)) 0 (k + 1)) (k + 1) := by
  have hzero : 0 < a.size := by omega
  have hs : (swap a 0 (k + 1)).size = a.size := size_swap _ _ _
  constructor
  · apply heapify_heap _ _ _ (by omega) (by omega)
    intro p c hp hc hpc
    have hlt := child_lt hpc
    rw [get_swap a 0 (k + 1) c hzero hk (by omega),
      get_swap a 0 (k + 1) p hzero hk (by omega)]
    simp only [if_neg (show c ≠ 0 by omega), if_neg (show c ≠ k + 1 by omega),
      if_neg (show p ≠ 0 by omega), if_neg (show p ≠ k + 1 by omega)]
    exact hh p c (by omega) (by omega) hpc
  · apply heapify_tail _ _ (by omega) (by omega)
    intro p q hpq hnq hq
    have hqa : q < a.size := by omega
    rw [get_swap a 0 (k + 1) p hzero hk (by omega),
      get_swap a 0 (k + 1) q hzero hk hqa]
    by_cases hqe : q = k + 1
    · subst q
      simp only [if_neg (show k + 1 ≠ 0 by omega)]
      split
      · exact heap_root_max a (k + 2) hh (k + 1) (by omega)
      · split
        · exact le_rfl
        · exact heap_root_max a (k + 2) hh p (by omega)
    · simp only [if_neg (show q ≠ 0 by omega), if_neg hqe]
      split
      · exact ht (k + 1) q (by omega) (by omega) hqa
      · split
        · exact ht 0 q (by omega) (by omega) hqa
        · exact ht p q hpq (by omega) hqa

theorem extractLoop_tail (k : Nat) (a : Array Nat) (hk : k < a.size)
    (hh : HeapFrom a (k + 1) 0) (ht : Tail a (k + 1)) :
    Tail (extractLoop k a) 1 := by
  induction k generalizing a with
  | zero => exact ht
  | succ k ih =>
    obtain ⟨hh', ht'⟩ := extract_step a k hk hh ht
    exact ih _ (by simp; omega) hh' ht'

theorem pairwise_of_tail (a : Array Nat) (ht : Tail a 1) :
    a.toList.Pairwise (· ≤ ·) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have h := ht i j hij (by omega) (by simpa using hj)
  simpa [getElem!_pos, show i < a.size by simpa using hi,
    show j < a.size by simpa using hj] using h

/-- The result is in nondecreasing order. -/
def sorted_prop (xs : List Nat) : Prop := (heapsort xs).Pairwise (· ≤ ·)

theorem sorted_thm (xs : List Nat) : sorted_prop xs := by
  unfold sorted_prop heapsort
  split
  · rename_i hs
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    omega
  · rename_i hs
    apply pairwise_of_tail
    apply extractLoop_tail
    · simp; omega
    · have h := build_heap xs
      convert h using 1; omega
    · intro p q hpq hnq hq
      simp only [size_build] at hq
      omega

/-- No input occurrence is lost or duplicated. -/
def permutation_prop (xs : List Nat) : Prop := (heapsort xs).Perm xs

theorem permutation_thm (xs : List Nat) : permutation_prop xs := by
  unfold permutation_prop heapsort
  split
  · exact List.Perm.refl _
  · exact (extractLoop_perm _ _).trans (build_perm xs)

def length_prop (xs : List Nat) : Prop := (heapsort xs).length = xs.length

theorem length_thm (xs : List Nat) : length_prop xs :=
  (permutation_thm xs).length_eq

def multiplicity_prop (xs : List Nat) (x : Nat) : Prop :=
  (heapsort xs).count x = xs.count x

theorem multiplicity_thm (xs : List Nat) (x : Nat) : multiplicity_prop xs x :=
  (permutation_thm xs).count_eq x

/-- Agreement with a separately implemented, library sorting specification. -/
def reference_prop (xs : List Nat) : Prop :=
  heapsort xs = xs.mergeSort (fun a b => decide (a ≤ b))

theorem reference_thm (xs : List Nat) : reference_prop xs := by
  apply List.eq_of_perm_of_sorted
    ((permutation_thm xs).trans (List.mergeSort_perm xs _).symm) (sorted_thm xs)
  have h := List.sorted_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (by intro a b c hab hbc; simp_all; omega)
    (by intro a b; simp; omega) xs
  simpa using h

def checked_valid_prop (xs : List Nat) : Prop :=
  heapsortChecked (xs.map Int.ofNat) = .ok (heapsort xs)

theorem checked_valid_thm (xs : List Nat) : checked_valid_prop xs := by
  simp [checked_valid_prop, heapsortChecked, List.all_map, List.map_map, Function.comp_def, Int.toNat]

def checked_invalid_prop (xs : List Int) : Prop :=
  (∃ z ∈ xs, z < 0) → heapsortChecked xs = .error "Input must be List[Nat]"

theorem checked_invalid_thm (xs : List Int) : checked_invalid_prop xs := by
  rintro ⟨z, hz, hneg⟩
  have hn : ¬ xs.all (fun z => decide (0 ≤ z)) = true := by
    intro h
    have h' := List.all_eq_true.mp h z hz
    simp only [decide_eq_true_eq] at h'
    omega
  simp [heapsortChecked, hn]

/-- The mathematical postcondition: sorted output, unchanged multiset and length. -/
def Post_prop (xs : List Nat) : Prop :=
  sorted_prop xs ∧ permutation_prop xs ∧ length_prop xs


/-! ## Property-based tests
Each named public property has its own randomized executable check. The final
bounded check exhausts all lists of length at most five over {0,1,2,3}, checking
the postcondition together with agreement with the library sort.
These are tests only; none is used in a theorem proof.
-/

-- PBT: sorted_prop
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).Pairwise (· ≤ ·))
-- PBT: permutation_prop
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).Perm xs)
-- PBT: length_prop
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).length = xs.length)
-- PBT: multiplicity_prop
#eval Plausible.Testable.check (∀ (xs : List Nat) (x : Nat),
  (heapsort xs).count x = xs.count x)
-- PBT: reference_prop
#eval Plausible.Testable.check (∀ xs : List Nat,
  heapsort xs = xs.mergeSort (fun a b => decide (a ≤ b)))
-- PBT: checked_valid_prop
#eval Plausible.Testable.check (∀ xs : List Nat,
  heapsortChecked (xs.map Int.ofNat) = .ok (heapsort xs))
-- PBT: checked_invalid_prop, as a total Boolean implication so that
-- empty/nonnegative lists do not discard randomized samples.
#eval Plausible.Testable.check (∀ xs : List Int,
  (!(xs.any (fun z => decide (z < 0))) ||
    decide (heapsortChecked xs = .error "Input must be List[Nat]")) = true)
-- PBT: Post_prop, expanded into its executable form.
#eval Plausible.Testable.check (∀ xs : List Nat,
  (heapsort xs).Pairwise (· ≤ ·) ∧ (heapsort xs).Perm xs ∧
    (heapsort xs).length = xs.length)

/-- All words of a given length over the four-element alphabet. -/
def testWords : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (List.range 4).flatMap (fun x => (testWords n).map (x :: ·))

def testInputs : List (List Nat) := (List.range 6).flatMap testWords

example : testInputs.length = 1365 := by native_decide
example : testInputs.all (fun xs =>
    decide ((heapsort xs).Pairwise (· ≤ ·)) &&
    decide ((heapsort xs).Perm xs) &&
    decide ((heapsort xs).length = xs.length) &&
    (heapsort xs == xs.mergeSort (fun a b => decide (a ≤ b)))) = true := by
  native_decide

-- Bounded PBT for checked_invalid_prop: all short lists over {-1,0,1,2}.
example : testInputs.all (fun xs =>
    let zs := xs.map (fun x => (x : Int) - 1)
    !(zs.any (fun z => decide (z < 0))) ||
      decide (heapsortChecked zs = .error "Input must be List[Nat]")) = true := by
  native_decide

/-- Total correctness for every admissible Python input. -/
theorem correctness_thm (xs : List Nat) : Pre xs → Post_prop xs := by
  intro _
  exact ⟨sorted_thm xs, permutation_thm xs, length_thm xs⟩

/-! ## Imperative implementation
The descending `for` loop carries a mutable accumulator. Heapify uses the same
bounded descent as the functional implementation; after it reaches a fixed
point, remaining iterations do nothing. Child selection is implemented with
mutable locals rather than by calling the functional `largest` definition.
-/

def downFor {α : Type} (step : α → Nat → α) (k : Nat) (a : α) : α := Id.run do
  let mut result := a
  for i in (List.range k).reverse do
    result := step result i
  return result

def siftStep (n : Nat) (state : Array Nat × Nat) : Array Nat × Nat := Id.run do
  let mut result := state.1
  let mut i := state.2
  let l := left i
  let r := right i
  let mut j := i
  if l < n && result[i]! < result[l]! then
    j := l
  if r < n && result[j]! < result[r]! then
    j := r
  if j != i then
    result := swap result i j
    i := j
  return (result, i)

def siftImperative (fuel : Nat) (a : Array Nat) (i n : Nat) : Array Nat :=
  (downFor (fun state _ => siftStep n state) fuel (a, i)).1

def max_heapifyImperative (a : Array Nat) (i n : Nat) : Array Nat :=
  siftImperative n a i n

def buildImperative (k : Nat) (a : Array Nat) : Array Nat :=
  downFor (fun result i => max_heapifyImperative result i result.size) k a

def extractImperative (k : Nat) (a : Array Nat) : Array Nat :=
  downFor (fun result i =>
    max_heapifyImperative (swap result 0 (i + 1)) 0 (i + 1)) k a

def heapsortImperative (xs : List Nat) : List Nat := Id.run do
  let mut result := xs.toArray
  if xs.length ≤ 1 then
    return result.toList
  result := buildImperative (parent (xs.length - 1) + 1) result
  result := extractImperative (xs.length - 1) result
  return result.toList

example : heapsortImperative [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsortImperative [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsortImperative [5, 13, 2, 25, 7, 17, 20, 8, 4] =
    [2, 4, 5, 7, 8, 13, 17, 20, 25] := by native_decide
example : heapsortImperative [] = [] := by native_decide
example : heapsortImperative [42] = [42] := by native_decide
example : heapsortImperative [2, 1] = [1, 2] := by native_decide
example : heapsortImperative [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsortImperative [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapsortImperative [9, 8, 7, 6, 5, 4, 3, 2, 1] =
    [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapsortImperative [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] =
    [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by native_decide
example : heapsortImperative [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsortImperative [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : heapsortImperative [2, 1] ≠ [2, 1] := by native_decide
#eval heapsortImperative [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval Plausible.Testable.check (∀ xs : List Nat, heapsortImperative xs = heapsort xs)
example : testInputs.all (fun xs => heapsortImperative xs == heapsort xs) = true := by
  native_decide

@[simp] theorem downFor_zero {α : Type} (step : α → Nat → α) (a : α) :
    downFor step 0 a = a := by simp [downFor]

theorem downFor_succ {α : Type} (step : α → Nat → α) (a : α) (k : Nat) :
    downFor step (k + 1) a = downFor step k (step a k) := by
  simp [downFor, List.range_succ, List.reverse_append]

theorem siftStep_eq (a : Array Nat) (i n : Nat) :
    siftStep n (a, i) =
      if largest a i n = i then (a, i) else (swap a i (largest a i n), largest a i n) := by
  simp [siftStep, largest]
  split_ifs <;> first | rfl | contradiction

theorem siftImperative_eq (fuel : Nat) (a : Array Nat) (i n : Nat) :
    siftImperative fuel a i n = sift fuel a i n := by
  unfold siftImperative
  induction fuel generalizing a i with
  | zero => simp [sift]
  | succ fuel ih =>
    rw [downFor_succ, siftStep_eq]
    by_cases he : largest a i n = i
    · simp only [he, sift]
      rw [ih]
      cases fuel <;> simp [sift, he]
    · simp only [if_neg he, sift]
      exact ih _ _

@[simp] theorem max_heapifyImperative_eq (a : Array Nat) (i n : Nat) :
    max_heapifyImperative a i n = max_heapify a i n := siftImperative_eq _ _ _ _

theorem buildImperative_eq (k : Nat) (a : Array Nat) :
    buildImperative k a = buildLoop k a := by
  unfold buildImperative
  induction k generalizing a with
  | zero => simp [buildLoop]
  | succ k ih =>
    simp only [downFor_succ, max_heapifyImperative_eq, buildLoop]
    simpa only [max_heapifyImperative_eq] using ih (max_heapify a k a.size)

theorem extractImperative_eq (k : Nat) (a : Array Nat) :
    extractImperative k a = extractLoop k a := by
  unfold extractImperative
  induction k generalizing a with
  | zero => simp [extractLoop]
  | succ k ih =>
    simp only [downFor_succ, max_heapifyImperative_eq, extractLoop]
    simpa only [max_heapifyImperative_eq] using
      ih (max_heapify (swap a 0 (k + 1)) 0 (k + 1))

/-- The two complete programs return exactly the same list, on every input. -/
theorem equivalence_thm (xs : List Nat) : heapsort xs = heapsortImperative xs := by
  by_cases hs : xs.length ≤ 1 <;>
    simp [heapsort, heapsortImperative, build_max_heap, hs,
      buildImperative_eq, extractImperative_eq]

end heapsort_algorithm
end Agent
