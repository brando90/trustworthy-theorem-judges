import Mathlib
namespace Agent

/-!
# CLRS BUILD-MAX-HEAP and BUILD-MIN-HEAP

Zero-based heaps of natural numbers. Child selection is strict and tests the
left child before the right child, so ties have precisely the Python order.
`List Nat` enforces the source's element validation (in particular, negative
integers and booleans are not inputs). Standalone heap operations have their
usual invariant `heap_size ≤ arr.length`; the builders always satisfy it.
The `checked_*` entry points additionally model validation errors and IndexError
for arbitrary raw inputs and arbitrary heap sizes, without imposing that invariant.
The natural-list core uses total default lookup outside the invariant. Lists are immutable, modelling `arr.copy()`.
-/

namespace heapsort_build_heap

def parent (i : Nat) : Nat := if i = 0 then 0 else (i - 1) / 2
def left (i : Nat) : Nat := 2 * i + 1
def right (i : Nat) : Nat := 2 * i + 2

def value (a : List Nat) (i : Nat) : Nat := a[i]?.getD 0

def swap (a : List Nat) (i j : Nat) : List Nat :=
  (a.set i (value a j)).set j (value a i)

/-- `true` denotes a max heap; `false` denotes a min heap. -/
def better (mx : Bool) (x y : Nat) : Bool :=
  if mx then x > y else x < y

def choose (mx : Bool) (a : List Nat) (n i : Nat) : Nat :=
  let l := left i
  let r := right i
  let best := if l < n && better mx (value a l) (value a i) then l else i
  if r < n && better mx (value a r) (value a best) then r else best

/-- Each nontrivial step goes strictly down the tree; `n` steps suffice. -/
def sift (mx : Bool) : Nat → List Nat → Nat → Nat → List Nat
  | 0, a, _, _ => a
  | fuel + 1, a, n, i =>
    if i < n && i < a.length then
      let j := choose mx a n i
      if j = i then a else sift mx fuel (swap a i j) n j
    else a

def max_heapify (a : List Nat) (n i : Nat) : List Nat := sift true n a n i
def min_heapify (a : List Nat) (n i : Nat) : List Nat := sift false n a n i

def is_max_heap (a : List Nat) (n : Nat) : Bool :=
  (List.range (min n a.length)).all fun i =>
    (!(left i < n) || !(value a (left i) > value a i)) &&
    (!(right i < n) || !(value a (right i) > value a i))

def is_min_heap (a : List Nat) (n : Nat) : Bool :=
  (List.range (min n a.length)).all fun i =>
    (!(left i < n) || !(value a (left i) < value a i)) &&
    (!(right i < n) || !(value a (right i) < value a i))

/-- Process `k-1, k-2, ..., 0`, using the original heap size. -/
def buildLoop (mx : Bool) (n : Nat) : Nat → List Nat → List Nat
  | 0, a => a
  | k + 1, a => buildLoop mx n k (sift mx n a n k)

def build_max_heap (a : List Nat) : List Nat := buildLoop true a.length (a.length / 2) a
def build_min_heap (a : List Nat) : List Nat := buildLoop false a.length (a.length / 2) a


deriving instance DecidableEq, BEq for Except

/-- Dynamic input categories relevant to Python's validation. `other` collects
strings, floats, tuples, and other objects rejected by these checks. -/
inductive RawValue where
  | integer (z : Int)
  | boolean (b : Bool)
  | list (xs : List RawValue)
  | other
  deriving Repr

def _is_nat : RawValue → Bool
  | .integer z => decide (0 ≤ z)
  | _ => false

def rawNat : RawValue → Nat
  | .integer z => z.toNat
  | _ => 0

def _check_nat (v : RawValue) (name : String := "value") : Except String Nat :=
  if _is_nat v then .ok (rawNat v) else .error (name ++ " must be a natural number")

def _check_nat_list (v : RawValue) (name : String := "arr") : Except String (List Nat) :=
  match v with
  | .list xs => if xs.all _is_nat then .ok (xs.map rawNat)
      else .error (name ++ " must be List[Nat]")
  | _ => .error (name ++ " must be List[Nat]")

def validRaw : RawValue → Bool
  | .list xs => xs.all _is_nat
  | _ => false

def encode (a : List Nat) : RawValue := .list (a.map fun n => .integer (Int.ofNat n))

def checked_build_max_heap (v : RawValue) : Except String (List Nat) :=
  match _check_nat_list v with
  | .ok a => .ok (build_max_heap a)
  | .error e => .error e

def checked_build_min_heap (v : RawValue) : Except String (List Nat) :=
  match _check_nat_list v with
  | .ok a => .ok (build_min_heap a)
  | .error e => .error e

/-- Checked entry points retain Python's exceptional behavior. A ValueError is
represented by its validation message; an IndexError by `list index out of range`.
The typed core is used directly when all the accessed indices exist. -/
def badChild (a : List Nat) (n i : Nat) : Bool :=
  (left i < n && a.length ≤ left i) || (right i < n && a.length ≤ right i)

def checkedSift (mx : Bool) : Nat → List Nat → Nat → Nat → Except String (List Nat)
  | 0, a, _, _ => .ok a
  | f + 1, a, n, i =>
    if i < n && i < a.length then
      if badChild a n i then .error "list index out of range"
      else
        let j := choose mx a n i
        if j = i then .ok a else checkedSift mx f (swap a i j) n j
    else .ok a

def checked_heapify (mx : Bool) (arr heap_size index : RawValue) : Except String (List Nat) := do
  let a ← _check_nat_list arr
  let n ← _check_nat heap_size "heap_size"
  let i ← _check_nat index "i"
  checkedSift mx n a n i

def checked_max_heapify := checked_heapify true
def checked_min_heapify := checked_heapify false

/-- True means this edge is ordered (or absent). -/
def checkedEdge (mx : Bool) (a : List Nat) (n p c : Nat) : Except String Bool :=
  if c < n then
    if c < a.length then .ok (!better mx (value a c) (value a p))
    else .error "list index out of range"
  else .ok true

def checkedNodes (mx : Bool) (a : List Nat) (n : Nat) : List Nat → Except String Bool
  | [] => .ok true
  | p :: ps => do
    let l ← checkedEdge mx a n p (left p)
    if !l then return false
    let r ← checkedEdge mx a n p (right p)
    if !r then return false
    checkedNodes mx a n ps

def checked_is_heap (mx : Bool) (arr heap_size : RawValue) : Except String Bool := do
  let a ← _check_nat_list arr
  let n ← _check_nat heap_size "heap_size"
  checkedNodes mx a n (List.range (min n a.length))

def checked_is_max_heap := checked_is_heap true
def checked_is_min_heap := checked_is_heap false

def checked_parent (index : RawValue) : Except String Nat := do
  return parent (← _check_nat index "i")
def checked_left (index : RawValue) : Except String Nat := do
  return left (← _check_nat index "i")
def checked_right (index : RawValue) : Except String Nat := do
  return right (← _check_nat index "i")

example : build_max_heap [4,1,3,2,16,9,10,14,8,7] =
    [16,14,10,8,7,9,3,2,4,1] := by native_decide
example : build_max_heap [5,3,17,10,84,19,6,22,9] =
    [84,22,19,10,3,17,6,5,9] := by native_decide
example : build_max_heap [] = [] := by native_decide
example : build_max_heap [42] = [42] := by native_decide
example : build_max_heap [1,2] = [2,1] := by native_decide
example : build_max_heap [2,1] = [2,1] := by native_decide
example : build_max_heap [3,3,3] = [3,3,3] := by native_decide
example : build_max_heap [16,14,10,8,7,9,3,2,4,1] =
    [16,14,10,8,7,9,3,2,4,1] := by native_decide
#eval build_max_heap [4,1,3,2,16,9,10,14,8,7]
#eval build_min_heap [4,1,3,2,16,9,10,14,8,7]

example : is_max_heap (build_max_heap [4,1,3,2,16,9,10,14,8,7]) 10 = true := by native_decide
example : is_max_heap (build_max_heap [5,3,17,10,84,19,6,22,9]) 9 = true := by native_decide
example : is_max_heap (build_max_heap [7,3,5,1,9,2,8]) 7 = true := by native_decide
example : is_max_heap (build_max_heap [1,2,3,4,5,6,7,8,9]) 9 = true := by native_decide
example : (build_max_heap [4,1,3,2,16,9,10,14,8,7]).length = 10 := by native_decide
example : is_min_heap (build_min_heap [4,1,3,2,16,9,10,14,8,7]) 10 = true := by native_decide
example : is_max_heap [4,1,3,2,16,9,10,14,8,7] 10 = false := by native_decide
example : build_max_heap [4,1,3,2,16,9,10,14,8,7] ≠ [4,1,3,2,16,9,10,14,8,7] := by native_decide
example : value (build_max_heap [10,20,30,40,50]) 0 = 50 := by native_decide
example : value (build_max_heap [100,1,50,2,99]) 0 = 100 := by native_decide
example : (build_max_heap [5,3,17,10,84,19,6,22,9]).mergeSort (· ≤ ·) =
    [3,5,6,9,10,17,19,22,84] := by native_decide
example : build_min_heap [] = [] ∧ build_min_heap [42] = [42] ∧
    build_min_heap [2,1] = [1,2] ∧ build_min_heap [3,3,3] = [3,3,3] := by native_decide
example : max_heapify [1,5,4,3,2] 5 0 = [5,3,4,1,2] := by native_decide
example : min_heapify [9,2,3,4,5] 5 0 = [2,4,3,9,5] := by native_decide
example : max_heapify [1,2,3] 0 0 = [1,2,3] ∧
    min_heapify [1,2,3] 3 3 = [1,2,3] := by native_decide
example : parent 0 = 0 ∧ parent 1 = 0 ∧ parent 2 = 0 ∧ parent 3 = 1 ∧
    left 4 = 9 ∧ right 4 = 10 := by native_decide

example : checked_build_max_heap (.list [.integer 1, .integer (-1)]) =
    .error "arr must be List[Nat]" := by native_decide
example : checked_build_max_heap (.list [.boolean true]) =
    .error "arr must be List[Nat]" := by native_decide
example : checked_build_min_heap (.integer 42) =
    .error "arr must be List[Nat]" := by native_decide
example : checked_build_max_heap (.list [.integer 1, .integer 2]) = .ok [2,1] := by native_decide
example : _check_nat (.integer (-1)) "i" = .error "i must be a natural number" ∧
    _check_nat (.boolean false) = .error "value must be a natural number" ∧
    _check_nat (.integer 0) = .ok 0 := by native_decide

-- Oversized heaps are not silently clamped. The early returns still apply.
example : checked_max_heapify (encode [2,1]) (.integer 3) (.integer 0) =
    .error "list index out of range" := by native_decide
example : checked_min_heapify (encode [2,1]) (.integer 20) (.integer 2) =
    .ok [2,1] := by native_decide
example : checked_is_max_heap (encode [1,2]) (.integer 3) = .ok false := by native_decide
example : checked_is_max_heap (encode [2,1]) (.integer 3) =
    .error "list index out of range" := by native_decide
example : checked_is_min_heap (encode [2,1]) (.integer 3) = .ok false := by native_decide
example : checked_is_min_heap (encode [1,2]) (.integer 3) =
    .error "list index out of range" := by native_decide
example : checked_is_max_heap (encode []) (.integer 100) = .ok true := by native_decide
example : checked_max_heapify (encode [1,2]) (.integer (-1)) (.integer 0) =
    .error "heap_size must be a natural number" := by native_decide
example : checked_parent (.boolean true) = .error "i must be a natural number" ∧
    checked_left (.integer 4) = .ok 9 ∧ checked_right (.integer 4) = .ok 10 := by native_decide

/-- Every `List Nat` is an admissible builder input. -/
def Pre (_a : List Nat) : Prop := True


/-- Parent value dominates child value, in the selected heap order. -/
def Dom (mx : Bool) (x y : Nat) : Prop := if mx then y ≤ x else x ≤ y

def Child (p c : Nat) : Prop := c = left p ∨ c = right p

lemma child_gt {p c : Nat} (h : Child p c) : p < c := by
  rcases h with h | h <;> simp only [left, right] at h <;> omega

lemma child_unique {p q c : Nat} (h : Child p c) (h' : Child q c) : p = q := by
  rcases h with h | h <;> rcases h' with h' | h' <;>
    simp only [left, right] at * <;> omega

lemma dom_refl (mx : Bool) (x : Nat) : Dom mx x x := by cases mx <;> simp [Dom]
lemma dom_trans {mx : Bool} {x y z : Nat}
    (h : Dom mx x y) (h' : Dom mx y z) : Dom mx x z := by
  cases mx <;> simp_all [Dom] <;> omega

lemma choose_cases (mx : Bool) (a : List Nat) (n i : Nat) :
    choose mx a n i = i ∨
      (Child i (choose mx a n i) ∧ choose mx a n i < n) := by
  dsimp only [choose]
  split <;> split <;> simp_all [Child, Bool.and_eq_true]

lemma choose_dominates (mx : Bool) (a : List Nat) (n i : Nat) :
    Dom mx (value a (choose mx a n i)) (value a i) ∧
    (∀ c, Child i c → c < n → Dom mx (value a (choose mx a n i)) (value a c)) := by
  cases mx <;> dsimp only [choose] <;>
    split <;> split <;> simp_all [better, Dom, Bool.and_eq_true, Child] <;>
    omega

@[simp] lemma swap_length (a : List Nat) (i j : Nat) :
    (swap a i j).length = a.length := by simp [swap]

lemma value_swap (a : List Nat) (i j k : Nat)
    (hi : i < a.length) (hj : j < a.length) :
    value (swap a i j) k =
      if k = j then value a i else if k = i then value a j else value a k := by
  simp only [value, swap, List.getElem?_set, List.length_set]
  by_cases hk : k = j
  · subst k; simp [hj]
  · by_cases hk' : k = i
    · subst k; simp [hk, Ne.symm hk, hi]
    · simp [hk, hk', Ne.symm hk, Ne.symm hk']

lemma swap_perm (a : List Nat) (i j : Nat)
    (hi : i < a.length) (hj : j < a.length) : (swap a i j).Perm a := by
  simpa [swap, value, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    using List.set_set_perm hi hj

@[simp] lemma sift_length (mx : Bool) (f : Nat) (a : List Nat) (n i : Nat) :
    (sift mx f a n i).length = a.length := by
  induction f generalizing a i with
  | zero => rfl
  | succ f ih => simp only [sift]; split <;> [split; skip] <;> simp_all

lemma sift_perm (mx : Bool) (f : Nat) (a : List Nat) (n i : Nat)
    (hn : n ≤ a.length) : (sift mx f a n i).Perm a := by
  induction f generalizing a i with
  | zero => exact .refl _
  | succ f ih =>
    simp only [sift]
    split
    · rename_i h
      have hg : i < n ∧ i < a.length := by simpa using h
      have hi : i < a.length := hg.2
      split
      · exact .refl _
      · rename_i hne
        have hc := choose_cases mx a n i
        have hj : choose mx a n i < a.length := by rcases hc with hc | hc; contradiction; omega
        exact (ih _ _ (by simpa using hn)).trans (swap_perm a i _ hi hj)
    · exact .refl _

@[simp] lemma buildLoop_length (mx : Bool) (n k : Nat) (a : List Nat) :
    (buildLoop mx n k a).length = a.length := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [buildLoop, ih]

lemma buildLoop_perm (mx : Bool) (n k : Nat) (a : List Nat)
    (hn : n ≤ a.length) : (buildLoop mx n k a).Perm a := by
  induction k generalizing a with
  | zero => exact .refl _
  | succ k ih =>
    exact (ih _ (by simpa using hn)).trans (sift_perm mx n a n k hn)


lemma sift_out_of_bounds (mx : Bool) (f : Nat) (a : List Nat) (n i : Nat)
    (hi : n ≤ i ∨ a.length ≤ i) : sift mx f a n i = a := by
  cases f with
  | zero => rfl
  | succ f =>
    have hg : ¬ (i < n ∧ i < a.length) := by omega
    simp [sift, hg]

/-- The fuel is a termination device, not a truncation of Python's while loop. -/
lemma sift_fuel_stable (mx : Bool) (f extra : Nat) (a : List Nat) (n i : Nat)
    (hf : n ≤ i + f) : sift mx (f + extra) a n i = sift mx f a n i := by
  induction f generalizing a i with
  | zero =>
    simpa only [Nat.zero_add, sift] using
      (sift_out_of_bounds mx extra a n i (Or.inl (by omega)))
  | succ f ih =>
    simp only [Nat.succ_add, sift]
    split
    · try dsimp only
      split
      · rfl
      · rename_i hne
        have hj := (choose_cases mx a n i).resolve_left hne
        have hgt := child_gt hj.1
        exact ih _ _ (by omega)
    · rfl

lemma checkedSift_out_of_bounds (mx : Bool) (f : Nat) (a : List Nat) (n i : Nat)
    (hi : n ≤ i ∨ a.length ≤ i) : checkedSift mx f a n i = .ok a := by
  cases f with
  | zero => rfl
  | succ f =>
    have hg : ¬ (i < n ∧ i < a.length) := by omega
    simp [checkedSift, hg]

lemma checkedSift_fuel_stable (mx : Bool) (f extra : Nat) (a : List Nat) (n i : Nat)
    (hf : n ≤ i + f) : checkedSift mx (f + extra) a n i = checkedSift mx f a n i := by
  induction f generalizing a i with
  | zero =>
    simpa only [Nat.zero_add, checkedSift] using
      (checkedSift_out_of_bounds mx extra a n i (Or.inl (by omega)))
  | succ f ih =>
    simp only [Nat.succ_add, checkedSift]
    split
    · split
      · rfl
      · try dsimp only
        split
        · rfl
        · rename_i hne
          have hj := (choose_cases mx a n i).resolve_left hne
          have hgt := child_gt hj.1
          exact ih _ _ (by omega)
    · rfl

/-- All parent-child edges whose parent is at least `start` are ordered. -/
def HeapFrom (mx : Bool) (a : List Nat) (n start : Nat) : Prop :=
  ∀ p c, start ≤ p → Child p c → c < n → Dom mx (value a p) (value a c)

/-- One defective node, together with the bridge needed when it is swapped. -/
def Repair (mx : Bool) (a : List Nat) (n start i : Nat) : Prop :=
  (∀ p c, start ≤ p → Child p c → c < n → p ≠ i →
    Dom mx (value a p) (value a c)) ∧
  (∀ p c, start ≤ p → Child p i → Child i c → c < n →
    Dom mx (value a p) (value a c))

lemma repair_swap {mx : Bool} {a : List Nat} {n start i j : Nat}
    (hn : n ≤ a.length) (hi : i < n) (hs : start ≤ i)
    (hj : Child i j) (hjn : j < n)
    (hd : Dom mx (value a j) (value a i))
    (hdc : ∀ c, Child i c → c < n → Dom mx (value a j) (value a c))
    (hr : Repair mx a n start i) : Repair mx (swap a i j) n start j := by
  have hij := child_gt hj
  have hji : j ≠ i := by omega
  have hil : i < a.length := by omega
  have hjl : j < a.length := by omega
  have vi : value (swap a i j) i = value a j := by
    simp [value_swap a i j i hil hjl, Ne.symm hji]
  have vj : value (swap a i j) j = value a i := by
    simp [value_swap a i j j hil hjl]
  have vo (k : Nat) (hki : k ≠ i) (hkj : k ≠ j) :
      value (swap a i j) k = value a k := by
    simp [value_swap a i j k hil hjl, hki, hkj]
  constructor
  · intro p c hp hc hcn hpj
    by_cases hpi : p = i
    · subst p
      rw [vi]
      by_cases hcj : c = j
      · subst c; rw [vj]; exact hd
      · rw [vo c (by have := child_gt hc; omega) hcj]
        exact hdc c hc hcn
    · by_cases hci : c = i
      · subst c
        rw [vo p hpi hpj, vi]
        exact hr.2 p j hp hc hj hjn
      · have hcj : c ≠ j := by
          intro he; subst c; exact hpi (child_unique hc hj)
        rw [vo p hpi hpj, vo c hci hcj]
        exact hr.1 p c hp hc hcn hpi
  · intro p c hp hpj hjc hcn
    have hpi := child_unique hpj hj
    subst p
    have hjc' := child_gt hjc
    rw [vi, vo c (by omega) (by omega)]
    exact hr.1 j c (by omega) hjc hcn hji

lemma repair_finish {mx : Bool} {a : List Nat} {n start i : Nat}
    (hr : Repair mx a n start i)
    (hd : ∀ c, Child i c → c < n → Dom mx (value a i) (value a c)) :
    HeapFrom mx a n start := by
  intro p c hp hc hcn
  by_cases hpi : p = i
  · subst p; exact hd c hc hcn
  · exact hr.1 p c hp hc hcn hpi

lemma sift_heap {mx : Bool} (f : Nat) (a : List Nat) (n start i : Nat)
    (hn : n ≤ a.length) (hs : start ≤ i) (hf : n ≤ i + f)
    (hr : Repair mx a n start i) : HeapFrom mx (sift mx f a n i) n start := by
  induction f generalizing a i with
  | zero =>
    apply repair_finish hr
    intro c hc hcn
    have := child_gt hc
    omega
  | succ f ih =>
    by_cases hi : i < n
    · have hil : i < a.length := by omega
      simp only [sift, hi, hil, decide_true, Bool.and_self, ite_true]
      have hd := choose_dominates mx a n i
      by_cases he : choose mx a n i = i
      · simp only [he, ite_true]
        exact repair_finish hr (by simpa only [he] using hd.2)
      · simp only [he, ite_false]
        have hj := (choose_cases mx a n i).resolve_left he
        have hgt := child_gt hj.1
        apply ih _ _ (by simpa using hn) (by omega) (by omega)
        exact repair_swap hn hi hs hj.1 hj.2 hd.1 hd.2 hr
    · simp only [sift, hi, decide_false, Bool.false_and, Bool.false_eq_true, ite_false]
      apply repair_finish hr
      intro c hc hcn
      have := child_gt hc
      omega

lemma sift_suffix {mx : Bool} (a : List Nat) (n i : Nat)
    (hn : n ≤ a.length) (h : HeapFrom mx a n (i + 1)) :
    HeapFrom mx (sift mx n a n i) n i := by
  apply sift_heap n a n i i hn (by omega) (by omega)
  constructor
  · intro p c hp hc hcn hpi
    exact h p c (by omega) hc hcn
  · intro p c hp hpi hic hcn
    have := child_gt hpi
    omega

lemma buildLoop_heap {mx : Bool} (n k : Nat) (a : List Nat)
    (hn : n ≤ a.length) (h : HeapFrom mx a n k) :
    HeapFrom mx (buildLoop mx n k a) n 0 := by
  induction k generalizing a with
  | zero => exact h
  | succ k ih =>
    exact ih _ (by simpa using hn) (sift_suffix a n k hn h)

lemma leaf_suffix (mx : Bool) (a : List Nat) : HeapFrom mx a a.length (a.length / 2) := by
  intro p c hp hc hcn
  rcases hc with hc | hc <;> simp only [left, right] at hc <;> omega

lemma build_heap_order (mx : Bool) (a : List Nat) :
    HeapFrom mx (buildLoop mx a.length (a.length / 2) a) a.length 0 :=
  buildLoop_heap _ _ _ (by omega) (leaf_suffix mx a)


lemma is_max_heap_iff (a : List Nat) (n : Nat) (hn : n ≤ a.length) :
    is_max_heap a n = true ↔ HeapFrom true a n 0 := by
  constructor
  · intro h p c hp hc hcn
    have hpc := child_gt hc
    have hp' : p < min n a.length := by omega
    have hh := List.all_eq_true.mp h p (List.mem_range.mpr hp')
    simp only [Bool.and_eq_true] at hh
    have hl := hh.1
    have hr := hh.2
    simp at hl hr
    rcases hc with rfl | rfl <;> simp only [Dom, ite_true] <;> omega
  · intro h
    apply List.all_eq_true.mpr
    intro p hp
    have hl := h p (left p) (Nat.zero_le _) (Or.inl rfl)
    have hr := h p (right p) (Nat.zero_le _) (Or.inr rfl)
    simp only [Dom, ite_true] at hl hr
    simp only [Bool.and_eq_true]
    constructor <;> simp <;> omega

lemma is_min_heap_iff (a : List Nat) (n : Nat) (hn : n ≤ a.length) :
    is_min_heap a n = true ↔ HeapFrom false a n 0 := by
  constructor
  · intro h p c hp hc hcn
    have hpc := child_gt hc
    have hp' : p < min n a.length := by omega
    have hh := List.all_eq_true.mp h p (List.mem_range.mpr hp')
    simp only [Bool.and_eq_true] at hh
    have hl := hh.1
    have hr := hh.2
    simp at hl hr
    rcases hc with rfl | rfl <;> simp only [Dom, Bool.false_eq_true, ite_false] <;> omega
  · intro h
    apply List.all_eq_true.mpr
    intro p hp
    have hl := h p (left p) (Nat.zero_le _) (Or.inl rfl)
    have hr := h p (right p) (Nat.zero_le _) (Or.inr rfl)
    simp only [Dom, Bool.false_eq_true, ite_false] at hl hr
    simp only [Bool.and_eq_true]
    constructor <;> simp <;> omega

lemma choose_fixed (mx : Bool) (a : List Nat) (n i : Nat)
    (h : ∀ c, Child i c → c < n → Dom mx (value a i) (value a c)) :
    choose mx a n i = i := by
  have hl : ¬ (left i < n ∧ better mx (value a (left i)) (value a i) = true) := by
    intro hc
    have hd := h _ (Or.inl rfl) hc.1
    cases mx <;> simp_all [better, Dom] <;> omega
  have hr : ¬ (right i < n ∧ better mx (value a (right i)) (value a i) = true) := by
    intro hc
    have hd := h _ (Or.inr rfl) hc.1
    cases mx <;> simp_all [better, Dom] <;> omega
  dsimp only [choose]
  simp only [Bool.and_eq_true, decide_eq_true_eq, hl, hr, ite_false]

lemma sift_fixed (mx : Bool) (f : Nat) (a : List Nat) (n i : Nat)
    (h : ∀ c, Child i c → c < n → Dom mx (value a i) (value a c)) :
    sift mx f a n i = a := by
  cases f <;> simp [sift, choose_fixed mx a n i h]

lemma buildLoop_fixed (mx : Bool) (n k : Nat) (a : List Nat)
    (h : HeapFrom mx a n 0) : buildLoop mx n k a = a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [buildLoop, sift_fixed mx n a n k (h k · (Nat.zero_le _)), ih]

lemma child_parent {i : Nat} (hi : 0 < i) : Child (parent i) i := by
  simp only [parent, show i ≠ 0 by omega, ite_false, Child, left, right]
  omega

lemma heap_root_dominates {mx : Bool} {a : List Nat} {n : Nat}
    (h : HeapFrom mx a n 0) (i : Nat) (hi : i < n) :
    Dom mx (value a 0) (value a i) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hz : i = 0
    · subst i; exact dom_refl _ _
    · have hc := child_parent (show 0 < i by omega)
      have hpi := child_gt hc
      exact dom_trans (ih (parent i) hpi (by omega)) (h _ _ (Nat.zero_le _) hc hi)


/-! ## Public properties -/

def length_prop (a : List Nat) : Prop :=
  (build_max_heap a).length = a.length ∧ (build_min_heap a).length = a.length

theorem length_thm (a : List Nat) : length_prop a := by
  simp [length_prop, build_max_heap, build_min_heap]

def permutation_prop (a : List Nat) : Prop :=
  (build_max_heap a).Perm a ∧ (build_min_heap a).Perm a

theorem permutation_thm (a : List Nat) : permutation_prop a :=
  ⟨buildLoop_perm true _ _ _ (le_refl _), buildLoop_perm false _ _ _ (le_refl _)⟩

def heap_order_prop (a : List Nat) : Prop :=
  is_max_heap (build_max_heap a) a.length = true ∧
  is_min_heap (build_min_heap a) a.length = true

theorem heap_order_thm (a : List Nat) : heap_order_prop a := by
  constructor
  · apply (is_max_heap_iff _ _ (by rw [(length_thm a).1])).mpr
    exact build_heap_order true a
  · apply (is_min_heap_iff _ _ (by rw [(length_thm a).2])).mpr
    exact build_heap_order false a

def fixed_point_prop (a : List Nat) : Prop :=
  (is_max_heap a a.length = true → build_max_heap a = a) ∧
  (is_min_heap a a.length = true → build_min_heap a = a)

theorem fixed_point_thm (a : List Nat) : fixed_point_prop a := by
  constructor
  · intro h
    exact buildLoop_fixed true _ _ a ((is_max_heap_iff _ _ (le_refl _)).mp h)
  · intro h
    exact buildLoop_fixed false _ _ a ((is_min_heap_iff _ _ (le_refl _)).mp h)

def idempotence_prop (a : List Nat) : Prop :=
  build_max_heap (build_max_heap a) = build_max_heap a ∧
  build_min_heap (build_min_heap a) = build_min_heap a

theorem idempotence_thm (a : List Nat) : idempotence_prop a := by
  constructor
  · apply (fixed_point_thm _).1
    rw [(length_thm a).1]
    exact (heap_order_thm a).1
  · apply (fixed_point_thm _).2
    rw [(length_thm a).2]
    exact (heap_order_thm a).2

/-- Both extrema are expressed over the original multiset, not just the result. -/
def root_extrema_prop (a : List Nat) : Prop :=
  ∀ x ∈ a, x ≤ value (build_max_heap a) 0 ∧ value (build_min_heap a) 0 ≤ x

theorem root_extrema_thm (a : List Nat) : root_extrema_prop a := by
  intro x hx
  have hm := (permutation_thm a).1.mem_iff.mpr hx
  have hn := (permutation_thm a).2.mem_iff.mpr hx
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hm
  obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hn
  have hmax := heap_root_dominates (build_heap_order true a) i
    (by simpa only [(length_thm a).1] using hi)
  have hmin := heap_root_dominates (build_heap_order false a) j
    (by simpa only [(length_thm a).2] using hj)
  have vi : value (build_max_heap a) i = x := by simp [value, List.getElem?_eq_getElem hi, hix]
  have vj : value (build_min_heap a) j = x := by simp [value, List.getElem?_eq_getElem hj, hjx]
  change Dom true (value (build_max_heap a) 0) (value (build_max_heap a) i) at hmax
  change Dom false (value (build_min_heap a) 0) (value (build_min_heap a) j) at hmin
  simpa [Dom, vi, vj] using And.intro hmax hmin

/-- Heapify preserves the entire list's multiset, including the inactive tail. -/
def heapify_preservation_prop (a : List Nat) (n i : Nat) : Prop :=
  n ≤ a.length →
    (max_heapify a n i).Perm a ∧ (min_heapify a n i).Perm a ∧
    (max_heapify a n i).length = a.length ∧ (min_heapify a n i).length = a.length

theorem heapify_preservation_thm (a : List Nat) (n i : Nat) :
    heapify_preservation_prop a n i := by
  intro hn
  exact ⟨sift_perm true n a n i hn, sift_perm false n a n i hn,
    sift_length true n a n i, sift_length false n a n i⟩

/-- The bottom-up loop invariant: fixing `i` extends the heap suffix by one. -/
def heapify_order_prop (a : List Nat) (n i : Nat) : Prop :=
  n ≤ a.length →
    (HeapFrom true a n (i + 1) → HeapFrom true (max_heapify a n i) n i) ∧
    (HeapFrom false a n (i + 1) → HeapFrom false (min_heapify a n i) n i)

theorem heapify_order_thm (a : List Nat) (n i : Nat) : heapify_order_prop a n i := by
  intro hn
  exact ⟨sift_suffix a n i hn, sift_suffix a n i hn⟩

lemma badChild_false (a : List Nat) (n i : Nat) (hn : n ≤ a.length) :
    badChild a n i = false := by
  simp [badChild]
  omega

lemma checkedSift_eq (mx : Bool) (f : Nat) (a : List Nat) (n i : Nat)
    (hn : n ≤ a.length) : checkedSift mx f a n i = .ok (sift mx f a n i) := by
  induction f generalizing a i with
  | zero => rfl
  | succ f ih =>
    simp only [checkedSift, sift, badChild_false a n i hn, Bool.false_eq_true, ite_false]
    split
    · try dsimp only
      split
      · rfl
      · exact ih _ _ (by simpa using hn)
    · rfl

lemma checkedEdge_eq (mx : Bool) (a : List Nat) (n p c : Nat) (hn : n ≤ a.length) :
    checkedEdge mx a n p c = .ok (!(c < n) || !better mx (value a c) (value a p)) := by
  by_cases hc : c < n
  · have hcl : c < a.length := by omega
    simp [checkedEdge, hc, hcl]
  · simp [checkedEdge, hc]

lemma checkedNodes_eq (mx : Bool) (a : List Nat) (n : Nat) (ps : List Nat)
    (hn : n ≤ a.length) :
    checkedNodes mx a n ps = .ok (ps.all fun p =>
      (!(left p < n) || !better mx (value a (left p)) (value a p)) &&
      (!(right p < n) || !better mx (value a (right p)) (value a p))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [checkedNodes, checkedEdge_eq mx a n p (left p) hn,
      checkedEdge_eq mx a n p (right p) hn, List.all_cons]
    cases hl : (!(left p < n) || !better mx (value a (left p)) (value a p)) <;>
      cases hr : (!(right p < n) || !better mx (value a (right p)) (value a p)) <;>
      simp [ih, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Correspondence of the checked interface with the typed helper layer.
The checked interface itself is defined for every raw input and every heap size. -/
def checked_helpers_prop (a : List Nat) (n i : Nat) : Prop :=
  n ≤ a.length →
    checked_max_heapify (encode a) (.integer n) (.integer i) = .ok (max_heapify a n i) ∧
    checked_min_heapify (encode a) (.integer n) (.integer i) = .ok (min_heapify a n i) ∧
    checked_is_max_heap (encode a) (.integer n) = .ok (is_max_heap a n) ∧
    checked_is_min_heap (encode a) (.integer n) = .ok (is_min_heap a n)

theorem checked_helpers_thm (a : List Nat) (n i : Nat) : checked_helpers_prop a n i := by
  intro hn
  simp [checked_max_heapify, checked_min_heapify, checked_heapify, checked_is_max_heap,
    checked_is_min_heap, checked_is_heap, _check_nat_list, _check_nat, _is_nat,
    rawNat, encode, List.map_map, Function.comp_def, checkedSift_eq _ _ _ _ _ hn,
    checkedNodes_eq _ _ _ _ hn, max_heapify, min_heapify, is_max_heap, is_min_heap, better,
    Bind.bind, Except.bind]

/-- Checked entry points agree exactly with the natural-number implementation. -/
def validation_roundtrip_prop (a : List Nat) : Prop :=
  checked_build_max_heap (encode a) = .ok (build_max_heap a) ∧
  checked_build_min_heap (encode a) = .ok (build_min_heap a)

theorem validation_roundtrip_thm (a : List Nat) : validation_roundtrip_prop a := by
  simp [validation_roundtrip_prop, checked_build_max_heap, checked_build_min_heap,
    _check_nat_list, encode, _is_nat, rawNat, List.map_map, Function.comp_def]

/-- ValueError is represented by `Except.error`, for exactly the rejected inputs. -/
def validation_prop (v : RawValue) : Prop :=
  (checked_build_max_heap v = .error "arr must be List[Nat]" ↔ validRaw v = false) ∧
  (checked_build_min_heap v = .error "arr must be List[Nat]" ↔ validRaw v = false)

theorem validation_thm (v : RawValue) : validation_prop v := by
  cases v with
  | integer z => simp [validation_prop, checked_build_max_heap, checked_build_min_heap,
      _check_nat_list, validRaw]
  | boolean b => simp [validation_prop, checked_build_max_heap, checked_build_min_heap,
      _check_nat_list, validRaw]
  | other => simp [validation_prop, checked_build_max_heap, checked_build_min_heap,
      _check_nat_list, validRaw]
  | list xs =>
    cases h : xs.all _is_nat <;>
      simp [validation_prop, checked_build_max_heap, checked_build_min_heap,
        _check_nat_list, validRaw, h]

/-- Full builder contract, with no restriction beyond the natural-number input type. -/
def Post_prop (a : List Nat) : Prop :=
  length_prop a ∧ permutation_prop a ∧ heap_order_prop a ∧ fixed_point_prop a ∧
  idempotence_prop a ∧ root_extrema_prop a ∧ validation_roundtrip_prop a

/-! ## Property-based tests
The bounded suite enumerates every list of length at most five over `{0,1,2}`.
It includes empty lists, duplicates, both heap orders, and non-heap inputs.
Permutation is checked by sorting; the mathematical theorem uses `List.Perm`.
-/

def smallLists : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => [] :: (smallLists k).flatMap (fun a => (List.range 3).map (fun x => x :: a))

def samples : List (List Nat) := smallLists 5

def lengthCheck (a : List Nat) : Bool :=
  (build_max_heap a).length == a.length && (build_min_heap a).length == a.length

def permutationCheck (a : List Nat) : Bool :=
  (build_max_heap a).mergeSort (· ≤ ·) == a.mergeSort (· ≤ ·) &&
  (build_min_heap a).mergeSort (· ≤ ·) == a.mergeSort (· ≤ ·)

def heapOrderCheck (a : List Nat) : Bool :=
  is_max_heap (build_max_heap a) a.length && is_min_heap (build_min_heap a) a.length

def fixedPointCheck (a : List Nat) : Bool :=
  (!is_max_heap a a.length || build_max_heap a == a) &&
  (!is_min_heap a a.length || build_min_heap a == a)

def idempotenceCheck (a : List Nat) : Bool :=
  build_max_heap (build_max_heap a) == build_max_heap a &&
  build_min_heap (build_min_heap a) == build_min_heap a

def rootExtremaCheck (a : List Nat) : Bool :=
  a.all fun x => x ≤ value (build_max_heap a) 0 && value (build_min_heap a) 0 ≤ x

/-- Executable finite version of `HeapFrom`, on admissible heap sizes. -/
def heapFromCheck (mx : Bool) (a : List Nat) (n start : Nat) : Bool :=
  (List.range n).all fun p =>
    p < start || ((! (left p < n) || !better mx (value a (left p)) (value a p)) &&
      (! (right p < n) || !better mx (value a (right p)) (value a p)))

def heapifyPreservationCheck (a : List Nat) : Bool :=
  (List.range (a.length + 1)).all fun n => (List.range (a.length + 2)).all fun i =>
    (max_heapify a n i).mergeSort (· ≤ ·) == a.mergeSort (· ≤ ·) &&
    (min_heapify a n i).mergeSort (· ≤ ·) == a.mergeSort (· ≤ ·) &&
    (max_heapify a n i).length == a.length && (min_heapify a n i).length == a.length

def heapifyOrderCheck (a : List Nat) : Bool :=
  (List.range (a.length + 1)).all fun n => (List.range (a.length + 2)).all fun i =>
    (!heapFromCheck true a n (i+1) || heapFromCheck true (max_heapify a n i) n i) &&
    (!heapFromCheck false a n (i+1) || heapFromCheck false (min_heapify a n i) n i)

def checkedHelpersCheck (a : List Nat) : Bool :=
  (List.range (a.length + 1)).all fun n => (List.range (a.length + 2)).all fun i =>
    checked_max_heapify (encode a) (.integer n) (.integer i) == .ok (max_heapify a n i) &&
    checked_min_heapify (encode a) (.integer n) (.integer i) == .ok (min_heapify a n i) &&
    checked_is_max_heap (encode a) (.integer n) == .ok (is_max_heap a n) &&
    checked_is_min_heap (encode a) (.integer n) == .ok (is_min_heap a n)

def validationRoundtripCheck (a : List Nat) : Bool :=
  checked_build_max_heap (encode a) == .ok (build_max_heap a) &&
  checked_build_min_heap (encode a) == .ok (build_min_heap a)

def validationCheck (v : RawValue) : Bool :=
  ((checked_build_max_heap v == .error "arr must be List[Nat]") == !validRaw v) &&
  ((checked_build_min_heap v == .error "arr must be List[Nat]") == !validRaw v)

def rawAlphabet : List RawValue :=
  [.integer (-1), .integer 0, .integer 1, .boolean false, .boolean true, .other, .list []]

def rawLists : Nat → List (List RawValue)
  | 0 => [[]]
  | k + 1 => [] :: (rawLists k).flatMap (fun xs => rawAlphabet.map (fun x => x :: xs))

def rawSamples : List RawValue := rawAlphabet ++ (rawLists 3).map RawValue.list

def postCheck (a : List Nat) : Bool :=
  lengthCheck a && permutationCheck a && heapOrderCheck a && fixedPointCheck a &&
  idempotenceCheck a && rootExtremaCheck a && validationRoundtripCheck a

-- One bounded PBT for each executable `_prop`, including `Post_prop`.
example : samples.all lengthCheck = true := by native_decide
example : samples.all permutationCheck = true := by native_decide
example : samples.all heapOrderCheck = true := by native_decide
example : samples.all fixedPointCheck = true := by native_decide
example : samples.all idempotenceCheck = true := by native_decide
example : samples.all rootExtremaCheck = true := by native_decide
example : samples.all heapifyPreservationCheck = true := by native_decide
example : samples.all heapifyOrderCheck = true := by native_decide
example : samples.all checkedHelpersCheck = true := by native_decide
example : samples.all validationRoundtripCheck = true := by native_decide
example : rawSamples.all validationCheck = true := by native_decide
example : samples.all postCheck = true := by native_decide
#eval (samples.length, samples.all postCheck)

/-- Kernel-checked correctness; none of the tests is used in this proof. -/
theorem correctness_thm (a : List Nat) : Pre a → Post_prop a := by
  intro _
  exact ⟨length_thm a, permutation_thm a, heap_order_thm a, fixed_point_thm a,
    idempotence_thm a, root_extrema_thm a, validation_roundtrip_thm a⟩


/-! ## Imperative implementation
The recursive fuel parameter is a total loop driver. The loop body uses mutable
array state, current position, and best-child selection. The outer builder is
an actual descending `for` loop; it does not call the functional builder.
-/

def siftImp (mx : Bool) : Nat → List Nat → Nat → Nat → List Nat
  | 0, a, _, _ => a
  | f + 1, a, n, i => Id.run do
    let mut result := a
    let mut current := i
    if current < n && current < result.length then
      let l := left current
      let r := right current
      let mut best := current
      if l < n && better mx (value result l) (value result current) then
        best := l
      if r < n && better mx (value result r) (value result best) then
        best := r
      if best != current then
        let old := value result current
        result := result.set current (value result best)
        result := result.set best old
        current := best
        result := siftImp mx f result n current
    return result

def max_heapify_imp (a : List Nat) (n i : Nat) : List Nat := siftImp true n a n i
def min_heapify_imp (a : List Nat) (n i : Nat) : List Nat := siftImp false n a n i

def buildHeapImp (mx : Bool) (a : List Nat) : List Nat := Id.run do
  let mut result := a
  let n := result.length
  for i in (List.range (n / 2)).reverse do
    result := siftImp mx n result n i
  return result

def build_max_heap_imp (a : List Nat) : List Nat := buildHeapImp true a
def build_min_heap_imp (a : List Nat) : List Nat := buildHeapImp false a

example : build_max_heap_imp [4,1,3,2,16,9,10,14,8,7] =
    [16,14,10,8,7,9,3,2,4,1] := by native_decide
example : build_max_heap_imp [5,3,17,10,84,19,6,22,9] =
    [84,22,19,10,3,17,6,5,9] := by native_decide
example : build_min_heap_imp [4,1,3,2,16,9,10,14,8,7] =
    [1,2,3,4,7,9,10,14,8,16] := by native_decide
example : build_max_heap_imp [] = [] ∧ build_min_heap_imp [42] = [42] := by native_decide
example : samples.all (fun a => build_max_heap_imp a == build_max_heap a &&
    build_min_heap_imp a == build_min_heap a) = true := by native_decide
example : samples.all (fun a => (List.range (a.length + 1)).all fun n =>
    (List.range (a.length + 2)).all fun i =>
      max_heapify_imp a n i == max_heapify a n i &&
      min_heapify_imp a n i == min_heapify a n i) = true := by native_decide
#eval build_max_heap_imp [10,20,30,40,50]
#eval build_min_heap_imp [10,20,30,40,50]

lemma siftImp_eq (mx : Bool) (f : Nat) (a : List Nat) (n i : Nat) :
    siftImp mx f a n i = sift mx f a n i := by
  induction f generalizing a i with
  | zero => rfl
  | succ f ih =>
    simp [siftImp, sift, choose, swap, ih]
    split_ifs <;> first | rfl | contradiction

lemma descending_fold (mx : Bool) (n k : Nat) (a : List Nat) :
    (List.range k).reverse.foldl (fun acc i => sift mx n acc n i) a =
      buildLoop mx n k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [List.range_succ, buildLoop, ih]

lemma buildHeapImp_eq (mx : Bool) (a : List Nat) :
    buildHeapImp mx a = buildLoop mx a.length (a.length / 2) a := by
  simpa [buildHeapImp, siftImp_eq] using
    (descending_fold mx a.length (a.length / 2) a)

theorem heapify_equivalence_thm (a : List Nat) (n i : Nat) :
    max_heapify a n i = max_heapify_imp a n i ∧
    min_heapify a n i = min_heapify_imp a n i := by
  constructor <;> exact (siftImp_eq _ _ _ _ _).symm

/-- Exact equality, not merely that both implementations produce some heap. -/
theorem equivalence_thm (a : List Nat) :
    build_max_heap a = build_max_heap_imp a ∧
    build_min_heap a = build_min_heap_imp a := by
  simp [build_max_heap_imp, build_min_heap_imp, buildHeapImp_eq,
    build_max_heap, build_min_heap]

end heapsort_build_heap
end Agent
