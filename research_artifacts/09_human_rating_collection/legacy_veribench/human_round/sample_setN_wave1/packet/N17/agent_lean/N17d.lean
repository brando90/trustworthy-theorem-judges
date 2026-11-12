import Mathlib

/-!
# CLRS heapsort on natural-number lists

The public interface sorts a copy. Internally, arrays use zero-based children,
bottom-up heap construction, and repeated root/last swaps. Heapify's fuel is
an upper bound on the strictly descending path through the finite heap.
`List Nat` represents precisely the admissible Python inputs; the checked
integer interface below also makes rejection of negative entries explicit.
-/

namespace heapsort_algorithm

def parent (i : Nat) : Nat := (i - 1) / 2
def left (i : Nat) : Nat := 2 * i + 1
def right (i : Nat) : Nat := 2 * i + 2

/-- Total reads and swaps simplify the internal interface. All algorithmic
reads and swaps on admissible heaps are in bounds. -/
def val (a : Array Nat) (i : Nat) : Nat := a[i]?.getD 0
def swap (a : Array Nat) (i j : Nat) : Array Nat := a.swapIfInBounds i j

def largest (a : Array Nat) (i n : Nat) : Nat :=
  let l := left i
  let r := right i
  let j := if l < n ∧ val a i < val a l then l else i
  if r < n ∧ val a j < val a r then r else j

def heapifyFuel : Nat → Array Nat → Nat → Nat → Array Nat
  | 0, a, _, _ => a
  | fuel + 1, a, i, n =>
    let j := largest a i n
    if j = i then a else heapifyFuel fuel (swap a i j) j n

def max_heapify (a : Array Nat) (i n : Nat) : Array Nat :=
  heapifyFuel n a i n

/-- Visit `count-1, ..., 0`. -/
def buildLoop : Nat → Array Nat → Nat → Array Nat
  | 0, a, _ => a
  | k + 1, a, n => buildLoop k (max_heapify a k n) n

def buildArray (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a
  else buildLoop (parent (a.size - 1) + 1) a a.size

def build_max_heap (xs : List Nat) : List Nat := (buildArray xs.toArray).toList

/-- Visit the last live positions `last, ..., 1`. -/
def extractLoop : Nat → Array Nat → Array Nat
  | 0, a => a
  | k + 1, a => extractLoop k (max_heapify (swap a 0 (k + 1)) 0 (k + 1))

def heapsort (xs : List Nat) : List Nat :=
  if xs.length ≤ 1 then xs
  else (extractLoop (xs.length - 1) (buildArray xs.toArray)).toList

/-- A typed analogue of the Python `ValueError` boundary. Lean's type system
already excludes booleans and non-list inputs. -/
def heapsortChecked (xs : List Int) : Except String (List Nat) :=
  if xs.all (fun x => decide (0 ≤ x)) then
    .ok (heapsort (xs.map Int.toNat))
  else .error "Input must be List[Nat]"

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
example : (match heapsortChecked [1, -1] with
    | .error s => s == "Input must be List[Nat]"
    | .ok _ => false) = true := by native_decide
#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval build_max_heap [5, 13, 2, 25, 7, 17, 20, 8, 4]

example : parent 0 = 0 ∧ parent 1 = 0 ∧ parent 2 = 0 ∧ parent 5 = 2 := by
  native_decide
example : left 3 = 7 ∧ right 3 = 8 := by native_decide

/-- Every value of `List Nat` satisfies the Python precondition. -/
def Pre (_xs : List Nat) : Prop := True


/-! ## Structural invariants -/

@[simp] theorem swap_size (a : Array Nat) (i j : Nat) :
    (swap a i j).size = a.size := by simp [swap]

theorem swap_perm (a : Array Nat) (i j : Nat) :
    (swap a i j).toList.Perm a.toList := by
  unfold swap Array.swapIfInBounds
  split
  · split
    · exact Array.perm_iff_toList_perm.mp (Array.swap_perm _ _)
    · exact List.Perm.refl _
  · exact List.Perm.refl _

theorem heapifyFuel_perm (fuel : Nat) (a : Array Nat) (i n : Nat) :
    (heapifyFuel fuel a i n).toList.Perm a.toList := by
  induction fuel generalizing a i with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    simp only [heapifyFuel]
    split
    · exact List.Perm.refl _
    · exact (ih _ _).trans (swap_perm _ _ _)

theorem max_heapify_perm (a : Array Nat) (i n : Nat) :
    (max_heapify a i n).toList.Perm a.toList := heapifyFuel_perm _ _ _ _

@[simp] theorem heapifyFuel_size (fuel : Nat) (a : Array Nat) (i n : Nat) :
    (heapifyFuel fuel a i n).size = a.size :=
  (heapifyFuel_perm fuel a i n).length_eq

@[simp] theorem max_heapify_size (a : Array Nat) (i n : Nat) :
    (max_heapify a i n).size = a.size := heapifyFuel_size _ _ _ _

theorem buildLoop_perm (k : Nat) (a : Array Nat) (n : Nat) :
    (buildLoop k a n).toList.Perm a.toList := by
  induction k generalizing a with
  | zero => exact List.Perm.refl _
  | succ k ih => exact (ih _).trans (max_heapify_perm _ _ _)

theorem buildArray_perm (a : Array Nat) :
    (buildArray a).toList.Perm a.toList := by
  unfold buildArray
  split
  · exact List.Perm.refl _
  · exact buildLoop_perm _ _ _

@[simp] theorem buildArray_size (a : Array Nat) : (buildArray a).size = a.size :=
  (buildArray_perm a).length_eq

theorem extractLoop_perm (k : Nat) (a : Array Nat) :
    (extractLoop k a).toList.Perm a.toList := by
  induction k generalizing a with
  | zero => exact List.Perm.refl _
  | succ k ih =>
    exact (ih _).trans ((max_heapify_perm _ _ _).trans (swap_perm _ _ _))

@[simp] theorem extractLoop_size (k : Nat) (a : Array Nat) :
    (extractLoop k a).size = a.size := (extractLoop_perm k a).length_eq

def permutation_prop (xs : List Nat) : Prop := (heapsort xs).Perm xs

theorem permutation_thm (xs : List Nat) : permutation_prop xs := by
  unfold permutation_prop heapsort
  split
  · exact List.Perm.refl _
  · simpa using (extractLoop_perm _ _).trans (buildArray_perm xs.toArray)

def length_prop (xs : List Nat) : Prop := (heapsort xs).length = xs.length

theorem length_thm (xs : List Nat) : length_prop xs := (permutation_thm xs).length_eq

def multiplicity_prop (xs : List Nat) (x : Nat) : Prop :=
  (heapsort xs).count x = xs.count x

theorem multiplicity_thm (xs : List Nat) (x : Nat) : multiplicity_prop xs x :=
  (permutation_thm xs).count_eq x

/-! ## Heap order and repair -/

def Child (p c : Nat) : Prop := c = left p ∨ c = right p

theorem child_lt {p c : Nat} (h : Child p c) : p < c := by
  rcases h with h | h <;> simp [left, right] at h <;> omega

theorem child_unique {p q c : Nat} (h : Child p c) (h' : Child q c) : p = q := by
  rcases h with h | h <;> rcases h' with h' | h' <;>
    simp [left, right] at * <;> omega

theorem child_parent {c : Nat} (h : 0 < c) : Child (parent c) c := by
  unfold Child parent left right
  omega

theorem largest_spec (a : Array Nat) (i n : Nat) :
    (largest a i n = i ∨ (Child i (largest a i n) ∧ largest a i n < n)) ∧
    val a i ≤ val a (largest a i n) ∧
    (∀ c, Child i c → c < n → val a c ≤ val a (largest a i n)) := by
  dsimp only [largest]
  split_ifs <;> simp_all [Child] <;> omega


/-- Outside the live heap there cannot be a live child. -/
theorem largest_eq_of_ge (a : Array Nat) (i n : Nat) (h : n ≤ i) :
    largest a i n = i := by
  rcases (largest_spec a i n).1 with heq | ⟨hc, hcn⟩
  · exact heq
  · have := child_lt hc
    omega

theorem heapifyFuel_stop (fuel : Nat) (a : Array Nat) (i n : Nat)
    (h : largest a i n = i) : heapifyFuel fuel a i n = a := by
  cases fuel <;> simp [heapifyFuel, h]

/-- Extra fuel beyond the maximum remaining downward path changes nothing,
for arbitrary arrays, not just arrays already satisfying heap invariants. -/
theorem heapifyFuel_stable (fuel extra : Nat) (a : Array Nat) (i n : Nat)
    (hf : n ≤ i + fuel) :
    heapifyFuel (fuel + extra) a i n = heapifyFuel fuel a i n := by
  induction fuel generalizing a i with
  | zero =>
    simpa [heapifyFuel] using
      heapifyFuel_stop extra a i n (largest_eq_of_ge a i n (by omega))
  | succ fuel ih =>
    simp only [Nat.succ_add, heapifyFuel]
    split_ifs with heq
    · rfl
    · obtain ⟨hc, _⟩ := (largest_spec a i n).1.resolve_left heq
      have := child_lt hc
      exact ih _ _ (by omega)

theorem swap_val (a : Array Nat) {i j : Nat}
    (hi : i < a.size) (hj : j < a.size) (k : Nat) :
    val (swap a i j) k =
      if k = i then val a j else if k = j then val a i else val a k := by
  simp only [swap, Array.swapIfInBounds, dif_pos hi, dif_pos hj, val,
    Array.getElem?_swap]
  by_cases hki : k = i
  · subst k
    by_cases hji : j = i
    · subst j; simp [Array.getElem?_eq_getElem hi]
    · simp [hji, Array.getElem?_eq_getElem hj]
  · by_cases hkj : k = j
    · subst k; simp [hki, Array.getElem?_eq_getElem hi]
    · simp [hki, hkj, Ne.symm hki, Ne.symm hkj]

/-- Heap edges whose parent is at least `lo` are ordered. -/
def HeapFrom (a : Array Nat) (n lo : Nat) : Prop :=
  ∀ p c, lo ≤ p → Child p c → c < n → val a c ≤ val a p

/-- The edge invariant during a downward sift. The second clause ensures
that moving a child up into the hole cannot break the edge above it. -/
def Hole (a : Array Nat) (n lo i : Nat) : Prop :=
  (∀ p c, lo ≤ p → p ≠ i → Child p c → c < n → val a c ≤ val a p) ∧
  (∀ p c, lo ≤ p → Child p i → Child i c → c < n → val a c ≤ val a p)

theorem hole_initial {a : Array Nat} {n i : Nat} (h : HeapFrom a n (i + 1)) :
    Hole a n i i := by
  constructor
  · intro p c hp hpi hc hn
    exact h p c (by omega) hc hn
  · intro p c hp hpi
    have := child_lt hpi
    omega

theorem hole_finished {a : Array Nat} {n lo i : Nat} (h : Hole a n lo i)
    (hj : largest a i n = i) : HeapFrom a n lo := by
  intro p c hp hc hn
  by_cases hpi : p = i
  · subst p
    simpa [hj] using (largest_spec a i n).2.2 c hc hn
  · exact h.1 p c hp hpi hc hn

theorem hole_swap {a : Array Nat} {n lo i j : Nat}
    (hn : n ≤ a.size) (hli : lo ≤ i) (h : Hole a n lo i)
    (hij : Child i j) (hjn : j < n)
    (hmax : ∀ c, Child i c → c < n → val a c ≤ val a j)
    (hup : val a i ≤ val a j) : Hole (swap a i j) n lo j := by
  have hijlt := child_lt hij
  have hi : i < a.size := by omega
  have hj : j < a.size := by omega
  constructor
  · intro p c hp hpj hpc hcn
    have hpclt := child_lt hpc
    by_cases hpi : p = i
    · subst p
      rw [swap_val a hi hj, swap_val a hi hj]
      by_cases hcj : c = j
      · subst c; simp [show j ≠ i by omega, hup]
      · simp [show c ≠ i by omega, hcj, hmax c hpc hcn]
    · by_cases hci : c = i
      · subst c
        rw [swap_val a hi hj, swap_val a hi hj]
        simpa [hpi, hpj] using h.2 p j hp hpc hij hjn
      · have hcj : c ≠ j := by
          intro heq
          subst c
          exact hpi (child_unique hpc hij)
        rw [swap_val a hi hj, swap_val a hi hj]
        simpa [hci, hcj, hpi, hpj] using h.1 p c hp hpi hpc hcn
  · intro p c hp hpj hjc hcn
    have hpi : p = i := child_unique hpj hij
    subst p
    have hjclt := child_lt hjc
    rw [swap_val a hi hj, swap_val a hi hj]
    simpa [show c ≠ i by omega, show c ≠ j by omega] using
      h.1 j c (by omega) (by omega) hjc hcn

/-- Each nontrivial step moves to a strictly larger valid index, so `n`
steps are sufficient. This proves that the fuel does not truncate a sift. -/
theorem heapifyFuel_order (fuel : Nat) (a : Array Nat) (n lo i : Nat)
    (hn : n ≤ a.size) (hli : lo ≤ i) (hf : n ≤ i + fuel)
    (h : Hole a n lo i) : HeapFrom (heapifyFuel fuel a i n) n lo := by
  induction fuel generalizing a i with
  | zero =>
    intro p c hp hc hcn
    have := child_lt hc
    exact h.1 p c hp (by omega) hc hcn
  | succ fuel ih =>
    dsimp only [heapifyFuel]
    split_ifs with heq
    · exact hole_finished h heq
    · obtain ⟨hc, hjn⟩ := (largest_spec a i n).1.resolve_left heq
      have hlt := child_lt hc
      apply ih (swap a i (largest a i n)) (largest a i n)
      · simpa using hn
      · omega
      · omega
      · exact hole_swap hn hli h hc hjn (largest_spec a i n).2.2
          (largest_spec a i n).2.1

theorem max_heapify_order {a : Array Nat} {n i : Nat} (hn : n ≤ a.size)
    (h : HeapFrom a n (i + 1)) : HeapFrom (max_heapify a i n) n i :=
  heapifyFuel_order n a n i i hn (by omega) (by omega) (hole_initial h)

theorem buildLoop_order (k : Nat) (a : Array Nat) (n : Nat)
    (hn : n ≤ a.size) (h : HeapFrom a n k) : HeapFrom (buildLoop k a n) n 0 := by
  induction k generalizing a with
  | zero => exact h
  | succ k ih =>
    apply ih (max_heapify a k n)
    · simpa using hn
    · exact max_heapify_order hn h

theorem buildArray_order (a : Array Nat) : HeapFrom (buildArray a) a.size 0 := by
  unfold buildArray
  split_ifs with hs
  · intro p c hp hc hcn
    have := child_lt hc
    omega
  · apply buildLoop_order _ _ _ (by omega)
    intro p c hp hc hcn
    rcases hc with hc | hc <;> simp [parent, left, right] at * <;> omega


/-! ## Frame and bound preservation -/

theorem heapifyFuel_frame (fuel : Nat) (a : Array Nat) (i n k : Nat)
    (hn : n ≤ a.size) (hk : k < i ∨ n ≤ k) :
    val (heapifyFuel fuel a i n) k = val a k := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
    dsimp only [heapifyFuel]
    split_ifs with heq
    · rfl
    · obtain ⟨hc, hjn⟩ := (largest_spec a i n).1.resolve_left heq
      have hlt := child_lt hc
      have hi : i < a.size := by omega
      have hj : largest a i n < a.size := by omega
      rw [ih _ _ (by simpa using hn) (by omega), swap_val a hi hj]
      simp [show k ≠ i by omega, show k ≠ largest a i n by omega]

theorem heapifyFuel_bound (fuel : Nat) (a : Array Nat) (i n bound : Nat)
    (hn : n ≤ a.size) (hb : ∀ k, k < n → val a k ≤ bound) :
    ∀ k, k < n → val (heapifyFuel fuel a i n) k ≤ bound := by
  induction fuel generalizing a i with
  | zero => exact hb
  | succ fuel ih =>
    dsimp only [heapifyFuel]
    split_ifs with heq
    · exact hb
    · obtain ⟨hc, hjn⟩ := (largest_spec a i n).1.resolve_left heq
      have hlt := child_lt hc
      have hi : i < a.size := by omega
      have hj : largest a i n < a.size := by omega
      apply ih _ _ (by simpa using hn)
      intro k hk
      rw [swap_val a hi hj]
      split_ifs
      · exact hb _ hjn
      · exact hb i (by omega)
      · exact hb k hk

theorem heap_root_max {a : Array Nat} {n : Nat} (h : HeapFrom a n 0) :
    ∀ c, c < n → val a c ≤ val a 0 := by
  intro c
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro hc
    by_cases hz : c = 0
    · subst c; exact le_rfl
    · have hedge := child_parent (show 0 < c by omega)
      have hlt := child_lt hedge
      exact (h _ _ (Nat.zero_le _) hedge hc).trans (ih _ hlt (by omega))

/-- The extracted suffix is ascending and bounds every live heap entry. -/
def Tail (a : Array Nat) (n : Nat) : Prop :=
  (∀ p q, n ≤ p → p < q → q < a.size → val a p ≤ val a q) ∧
  (∀ p q, p < n → n ≤ q → q < a.size → val a p ≤ val a q)

def Ordered (a : Array Nat) : Prop :=
  ∀ p q, p < q → q < a.size → val a p ≤ val a q

theorem tail_initial (a : Array Nat) : Tail a a.size := by
  constructor <;> intro p q hp hq hs <;> omega

theorem max_heapify_tail {a : Array Nat} {i n : Nat}
    (hn : n ≤ a.size) (h : Tail a n) : Tail (max_heapify a i n) n := by
  constructor
  · intro p q hp hpq hq
    have hqs : q < a.size := by simpa using hq
    change val (heapifyFuel n a i n) p ≤ val (heapifyFuel n a i n) q
    rw [heapifyFuel_frame n a i n p hn (Or.inr hp),
      heapifyFuel_frame n a i n q hn (Or.inr (by omega))]
    exact h.1 p q hp hpq hqs
  · intro p q hp hq hqs
    have hqs' : q < a.size := by simpa using hqs
    change val (heapifyFuel n a i n) p ≤ val (heapifyFuel n a i n) q
    rw [heapifyFuel_frame n a i n q hn (Or.inr hq)]
    exact heapifyFuel_bound n a i n (val a q) hn
      (fun k hk => h.2 k q hk hq hqs') p hp

theorem extract_swap_order {a : Array Nat} {t : Nat} (ht : 0 < t)
    (hs : t < a.size) (h : HeapFrom a (t + 1) 0) :
    HeapFrom (swap a 0 t) t 1 := by
  intro p c hp hc hcn
  have hpc := child_lt hc
  have hz : 0 < a.size := by omega
  simpa [swap_val a hz hs, show c ≠ 0 by omega, show c ≠ t by omega,
    show p ≠ 0 by omega, show p ≠ t by omega] using
      h p c (by omega) hc (by omega)

theorem extract_swap_tail {a : Array Nat} {t : Nat} (ht : 0 < t)
    (hs : t < a.size) (hh : HeapFrom a (t + 1) 0) (h : Tail a (t + 1)) :
    Tail (swap a 0 t) t := by
  have hz : 0 < a.size := by omega
  constructor
  · intro p q hp hpq hqs
    simp only [swap_size] at hqs
    have hpz : p ≠ 0 := by omega
    have hqz : q ≠ 0 := by omega
    have hqt : q ≠ t := by omega
    by_cases hpt : p = t
    · subst p
      simpa [swap_val a hz hs, hqz, hqt, show t ≠ 0 by omega] using
        h.2 0 q (by omega) (by omega) hqs
    · simpa [swap_val a hz hs, hpz, hqz, hqt, hpt] using
        h.1 p q (by omega) hpq hqs
  · intro p q hp hq hqs
    simp only [swap_size] at hqs
    have hqz : q ≠ 0 := by omega
    have hpt : p ≠ t := by omega
    by_cases hqt : q = t
    · subst q
      by_cases hpz : p = 0
      · subst p
        simpa [swap_val a hz hs, show t ≠ 0 by omega] using
          heap_root_max hh t (by omega)
      · simpa [swap_val a hz hs, hpz, hpt, show t ≠ 0 by omega] using
          heap_root_max hh p (by omega)
    · by_cases hpz : p = 0
      · subst p
        simpa [swap_val a hz hs, hqz, hqt] using
          h.2 t q (by omega) (by omega) hqs
      · simpa [swap_val a hz hs, hpz, hpt, hqz, hqt] using
          h.2 p q (by omega) (by omega) hqs

theorem extractLoop_order (k : Nat) (a : Array Nat)
    (hs : k + 1 ≤ a.size) (hh : HeapFrom a (k + 1) 0) (ht : Tail a (k + 1)) :
    Ordered (extractLoop k a) := by
  induction k generalizing a with
  | zero =>
    intro p q hpq hqs
    by_cases hp : 1 ≤ p
    · exact ht.1 p q hp hpq hqs
    · exact ht.2 p q (by omega) (by omega) hqs
  | succ k ih =>
    apply ih (max_heapify (swap a 0 (k + 1)) 0 (k + 1))
    · simp only [max_heapify_size, swap_size]; omega
    · apply max_heapify_order (by simp only [swap_size]; omega)
      exact extract_swap_order (by omega) (by omega) hh
    · apply max_heapify_tail (by simp only [swap_size]; omega)
      exact extract_swap_tail (by omega) (by omega) hh ht

theorem ordered_toList {a : Array Nat} (h : Ordered a) :
    a.toList.Pairwise (· ≤ ·) := by
  apply List.pairwise_iff_getElem.mpr
  intro p q hp hq hpq
  have hp' : p < a.size := hp
  have hq' : q < a.size := hq
  simpa [val, Array.getElem?_eq_getElem hp', Array.getElem?_eq_getElem hq'] using
    h p q hpq hq'

def sorted_prop (xs : List Nat) : Prop := (heapsort xs).Pairwise (· ≤ ·)

theorem sorted_thm (xs : List Nat) : sorted_prop xs := by
  unfold sorted_prop heapsort
  split_ifs with hs
  · apply List.pairwise_iff_getElem.mpr
    intro p q hp hq hpq
    omega
  · apply ordered_toList
    have hn : xs.length - 1 + 1 = xs.length := by omega
    apply extractLoop_order
    · simp [hn]
    · simpa [hn] using buildArray_order xs.toArray
    · simpa [hn] using tail_initial (buildArray xs.toArray)


/-! ## Public specifications -/

def reference_prop (xs : List Nat) : Prop :=
  heapsort xs = xs.mergeSort (· ≤ ·)

theorem reference_thm (xs : List Nat) : reference_prop xs := by
  apply List.eq_of_perm_of_sorted
    ((permutation_thm xs).trans (List.mergeSort_perm xs (· ≤ ·)).symm)
    (sorted_thm xs)
  simpa using List.sorted_mergeSort
    (le := fun a b : Nat => a ≤ b)
    (by intro a b c hab hbc; simp_all; omega)
    (by intro a b; simp; omega) xs

def build_heap_prop (xs : List Nat) : Prop :=
  HeapFrom (buildArray xs.toArray) xs.length 0 ∧ (build_max_heap xs).Perm xs

theorem build_heap_thm (xs : List Nat) : build_heap_prop xs := by
  constructor
  · simpa using buildArray_order xs.toArray
  · simpa [build_max_heap] using buildArray_perm xs.toArray

/-- Boolean version of max-heap order, used in the property-based tests. -/
def heapCheck (a : Array Nat) (n : Nat) : Bool :=
  (List.range n).all (fun c => decide (val a c ≤ val a (parent c)))

theorem heapCheck_iff (a : Array Nat) (n : Nat) :
    heapCheck a n = true ↔ HeapFrom a n 0 := by
  simp only [heapCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h p c hp hc hcn
    have hpos : 0 < c := lt_of_le_of_lt (Nat.zero_le p) (child_lt hc)
    have heq : parent c = p := child_unique (child_parent hpos) hc
    simpa [heq] using h c hcn
  · intro h c hcn
    by_cases hz : c = 0
    · subst c; simp [parent]
    · exact h (parent c) c (Nat.zero_le _) (child_parent (by omega)) hcn

def checked_acceptance_prop (xs : List Nat) : Prop :=
  heapsortChecked (xs.map Int.ofNat) = .ok (heapsort xs)

theorem checked_acceptance_thm (xs : List Nat) : checked_acceptance_prop xs := by
  simp [checked_acceptance_prop, heapsortChecked, List.all_eq_true,
    List.map_map, Function.comp_def]

def checked_rejection_prop (xs : List Int) : Prop :=
  (∃ x ∈ xs, x < 0) → heapsortChecked xs = .error "Input must be List[Nat]"

theorem checked_rejection_thm (xs : List Int) : checked_rejection_prop xs := by
  intro h
  obtain ⟨x, hx, hneg⟩ := h
  have hn : ¬ xs.all (fun x => decide (0 ≤ x)) = true := by
    intro hall
    have := List.all_eq_true.mp hall x hx
    simp only [decide_eq_true_eq] at this
    omega
  simp [heapsortChecked, hn]

/-- Sorting preserves exactly the input elements and their multiplicities,
returns an ascending list of the same length, and agrees with `sorted`. -/
def Post_prop (xs : List Nat) : Prop :=
  sorted_prop xs ∧ permutation_prop xs ∧ length_prop xs ∧ reference_prop xs

/-! ## Property-based tests
These are executable evidence only. All universal claims above and below
have separate kernel-checked proofs. Each named public property is covered.
-/

-- sorted_prop
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).Pairwise (· ≤ ·))
-- permutation_prop
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).Perm xs)
-- length_prop
#eval Plausible.Testable.check (∀ xs : List Nat, (heapsort xs).length = xs.length)
-- multiplicity_prop (also samples the value whose occurrences are counted)
#eval Plausible.Testable.check
  (∀ (xs : List Nat) (x : Nat), (heapsort xs).count x = xs.count x)
-- reference_prop
#eval Plausible.Testable.check
  (∀ xs : List Nat, heapsort xs = xs.mergeSort (· ≤ ·))
-- build_heap_prop, using the proved equivalent Boolean heap predicate
#eval Plausible.Testable.check
  (∀ xs : List Nat, heapCheck (buildArray xs.toArray) xs.length = true ∧
    (build_max_heap xs).Perm xs)
-- checked_acceptance_prop: pattern matching avoids requiring DecidableEq Except.
#eval Plausible.Testable.check (∀ xs : List Nat,
  (match heapsortChecked (xs.map Int.ofNat) with
   | .ok ys => ys == heapsort xs
   | .error _ => false) = true)
-- checked_rejection_prop
#eval Plausible.Testable.check (∀ xs : List Int,
  ((!xs.any (fun x => decide (x < 0))) ||
    (match heapsortChecked xs with
     | .error s => s == "Input must be List[Nat]"
     | .ok _ => false)) = true)
-- Post_prop, with its definitions expanded to executable propositions.
#eval Plausible.Testable.check (∀ xs : List Nat,
  (heapsort xs).Pairwise (· ≤ ·) ∧ (heapsort xs).Perm xs ∧
  (heapsort xs).length = xs.length ∧ heapsort xs = xs.mergeSort (· ≤ ·))

/-- Exhaustively generate every list of the given length over an alphabet. -/
def listsOfLength (alphabet : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap (fun x => (listsOfLength alphabet n).map (x :: ·))

/-- 1365 lists, including duplicates, empty inputs, and all orders. -/
def smallInputs : List (List Nat) :=
  (List.range 6).flatMap (listsOfLength (List.range 4))

-- Bounded PBT for the complete postcondition, independently of the random seed.
example : smallInputs.all (fun xs =>
    decide ((heapsort xs).Pairwise (· ≤ ·)) && decide ((heapsort xs).Perm xs) &&
    decide ((heapsort xs).length = xs.length) &&
    decide (heapsort xs = xs.mergeSort (· ≤ ·))) = true := by native_decide

-- Bounded PBT for build_heap_prop and multiplicity_prop.
example : smallInputs.all (fun xs =>
    heapCheck (buildArray xs.toArray) xs.length &&
    decide ((build_max_heap xs).Perm xs) &&
    (List.range 6).all (fun x => decide ((heapsort xs).count x = xs.count x))) = true := by
  native_decide

-- A guaranteed admissible rejection test family (no sampling/discard bias).
example : (List.range 30).all (fun n =>
    match heapsortChecked [Int.ofNat n, -(Int.ofNat n + 1)] with
    | .error s => s == "Input must be List[Nat]"
    | .ok _ => false) = true := by native_decide

theorem correctness_thm (xs : List Nat) : Pre xs → Post_prop xs := by
  intro _
  exact ⟨sorted_thm xs, permutation_thm xs, length_thm xs, reference_thm xs⟩


/-! ## Imperative implementation
The state changes below use `Id.run`, mutable arrays/indices, and `for`
loops. Heapify stops with `break` as soon as its root dominates its children.
-/

def largestImperative (a : Array Nat) (i n : Nat) : Nat := Id.run do
  let l := left i
  let r := right i
  let mut j := i
  if l < n ∧ val a i < val a l then
    j := l
  if r < n ∧ val a j < val a r then
    j := r
  return j

def heapifyStepsImperative (steps : List Nat) (a : Array Nat) (i n : Nat) :
    Array Nat := Id.run do
  let mut result := a
  let mut pos := i
  for _ in steps do
    let j := largestImperative result pos n
    if j = pos then break
    result := swap result pos j
    pos := j
  return result

def max_heapifyImperative (a : Array Nat) (i n : Nat) : Array Nat :=
  heapifyStepsImperative (List.range n) a i n

def buildIndicesImperative (indices : List Nat) (a : Array Nat) (n : Nat) :
    Array Nat := Id.run do
  let mut result := a
  for i in indices do
    result := max_heapifyImperative result i n
  return result

def buildArrayImperative (a : Array Nat) : Array Nat := Id.run do
  let n := a.size
  let mut result := a
  if n ≤ 1 then return result
  result := buildIndicesImperative (List.range (parent (n - 1) + 1)).reverse result n
  return result

def extractIndicesImperative (indices : List Nat) (a : Array Nat) :
    Array Nat := Id.run do
  let mut result := a
  for k in indices do
    let i := k + 1
    result := swap result 0 i
    result := max_heapifyImperative result 0 i
  return result

def heapsortImperative (xs : List Nat) : List Nat := Id.run do
  let mut result := xs.toArray
  if result.size ≤ 1 then return result.toList
  result := buildArrayImperative result
  result := extractIndicesImperative (List.range (xs.length - 1)).reverse result
  return result.toList

def heapsortCheckedImperative (xs : List Int) : Except String (List Nat) := Id.run do
  if xs.all (fun x => decide (0 ≤ x)) then
    return .ok (heapsortImperative (xs.map Int.toNat))
  return .error "Input must be List[Nat]"

/-! ## Imperative tests -/

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
example : (match heapsortCheckedImperative [1, -1] with
    | .error s => s == "Input must be List[Nat]"
    | .ok _ => false) = true := by native_decide
#eval heapsortImperative [5, 13, 2, 25, 7, 17, 20, 8, 4]

#eval Plausible.Testable.check (∀ xs : List Int,
  (match heapsortChecked xs, heapsortCheckedImperative xs with
   | .ok ys, .ok zs => ys == zs
   | .error e, .error f => e == f
   | _, _ => false) = true)

#eval Plausible.Testable.check
  (∀ xs : List Nat, heapsortImperative xs = heapsort xs)
example : smallInputs.all (fun xs => heapsortImperative xs == heapsort xs) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem largestImperative_eq (a : Array Nat) (i n : Nat) :
    largestImperative a i n = largest a i n := by
  simp [largestImperative, largest]
  split_ifs <;> rfl

theorem heapifyStepsImperative_eq (steps : List Nat) (a : Array Nat) (i n : Nat) :
    heapifyStepsImperative steps a i n = heapifyFuel steps.length a i n := by
  induction steps generalizing a i with
  | nil => simp [heapifyStepsImperative, heapifyFuel]
  | cons x steps ih =>
    by_cases h : largest a i n = i
    · simp [heapifyStepsImperative, heapifyFuel, largestImperative_eq, h]
    · simpa [heapifyStepsImperative, heapifyFuel, largestImperative_eq, h] using
        ih (swap a i (largest a i n)) (largest a i n)

theorem max_heapifyImperative_eq (a : Array Nat) (i n : Nat) :
    max_heapifyImperative a i n = max_heapify a i n := by
  simp [max_heapifyImperative, heapifyStepsImperative_eq, max_heapify]

theorem buildIndicesImperative_cons (indices : List Nat) (a : Array Nat) (n i : Nat) :
    buildIndicesImperative (i :: indices) a n =
      buildIndicesImperative indices (max_heapifyImperative a i n) n := by
  simp [buildIndicesImperative]

theorem buildIndicesImperative_eq (k : Nat) (a : Array Nat) (n : Nat) :
    buildIndicesImperative (List.range k).reverse a n = buildLoop k a n := by
  induction k generalizing a with
  | zero => simp [buildIndicesImperative, buildLoop]
  | succ k ih =>
    simp [List.range_succ, List.reverse_append, buildIndicesImperative_cons,
      max_heapifyImperative_eq, buildLoop, ih]

theorem buildArrayImperative_eq (a : Array Nat) :
    buildArrayImperative a = buildArray a := by
  simp [buildArrayImperative, buildArray, buildIndicesImperative_eq]
  split_ifs <;> rfl

theorem extractIndicesImperative_cons (indices : List Nat) (a : Array Nat) (k : Nat) :
    extractIndicesImperative (k :: indices) a =
      extractIndicesImperative indices (max_heapifyImperative (swap a 0 (k + 1)) 0 (k + 1)) := by
  simp [extractIndicesImperative]

theorem extractIndicesImperative_eq (k : Nat) (a : Array Nat) :
    extractIndicesImperative (List.range k).reverse a = extractLoop k a := by
  induction k generalizing a with
  | zero => simp [extractIndicesImperative, extractLoop]
  | succ k ih =>
    simp [List.range_succ, List.reverse_append, extractIndicesImperative_cons,
      max_heapifyImperative_eq, extractLoop, ih]

theorem equivalence_thm (xs : List Nat) : heapsort xs = heapsortImperative xs := by
  simp [heapsort, heapsortImperative, buildArrayImperative_eq, extractIndicesImperative_eq]
  split_ifs <;> rfl

/-- The same equivalence includes both successful and exceptional returns. -/
theorem checked_equivalence_thm (xs : List Int) :
    heapsortChecked xs = heapsortCheckedImperative xs := by
  simp [heapsortChecked, heapsortCheckedImperative, equivalence_thm]
  split_ifs <;> rfl

theorem imperative_correctness_thm (xs : List Nat) (h : Pre xs) :
    (heapsortImperative xs).Pairwise (· ≤ ·) ∧
    (heapsortImperative xs).Perm xs ∧
    (heapsortImperative xs).length = xs.length ∧
    heapsortImperative xs = xs.mergeSort (· ≤ ·) := by
  simpa only [Post_prop, sorted_prop, permutation_prop, length_prop,
    reference_prop, equivalence_thm] using correctness_thm xs h

end heapsort_algorithm
