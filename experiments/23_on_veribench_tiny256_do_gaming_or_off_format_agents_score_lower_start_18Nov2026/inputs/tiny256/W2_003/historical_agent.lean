import Mathlib
namespace Agent

/-!
# Python's `bisect_right`

A binary search with the same midpoint and strict comparison as Python.  Lists
need not be sorted in order to run the program.  The only checked precondition
is nonnegative `lo`; an actually visited invalid index raises `indexError`.
Negative upper bounds cause an empty search, just as in Python.  Successful
indices are represented by `Nat` (their embedding into Python integers is exact).

`lessElement` models Python's possibly heterogeneous comparison `x < a[mid]`;
with a key, `lessKey` instead compares `x < key(a[mid])`.  Thus a key is applied
only to visited elements and never to the query.  Comparisons and keys are
assumed pure and total, as usual for this functional model.
-/
namespace BisectRight

variable {α κ : Type*}

inductive Error where
  | negativeLo
  | indexError
  deriving DecidableEq, Repr

abbrev Result := Except Error Nat

instance : DecidableEq Result := fun a b =>
  match a, b with
  | .ok x, .ok y => decidable_of_iff (x = y) (by simp)
  | .error x, .error y => decidable_of_iff (x = y) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

def search (a : List α) (cut : α → Bool) (lo hi : Nat) : Result :=
  if lo < hi then
    let mid := (lo + hi) / 2
    match a[mid]? with
    | none => .error .indexError
    | some v =>
      if cut v then search a cut lo mid
      else search a cut (mid + 1) hi
  else .ok lo
termination_by hi - lo
decreasing_by
  all_goals have hm₁ : lo ≤ (lo + hi) / 2 := by omega
  all_goals have hm₂ : (lo + hi) / 2 < hi := by omega
  all_goals omega

def comparison (x : κ) (lessElement : κ → α → Bool)
    (lessKey : κ → κ → Bool) (key : Option (α → κ)) : α → Bool :=
  match key with
  | none => lessElement x
  | some f => fun v => lessKey x (f v)

def bisect_right (a : List α) (x : κ)
    (lessElement : κ → α → Bool) (lessKey : κ → κ → Bool)
    (lo : Int := 0) (hi : Option Int := none)
    (key : Option (α → κ) := none) : Result :=
  search a (comparison x lessElement lessKey key) lo.toNat
    ((hi.getD (Int.ofNat a.length)).toNat)

def benchmark_bisect_right (a : List α) (x : κ)
    (lessElement : κ → α → Bool) (lessKey : κ → κ → Bool)
    (lo : Int := 0) (hi : Option Int := none)
    (key : Option (α → κ) := none) : Result :=
  if lo < 0 then .error .negativeLo
  else bisect_right a x lessElement lessKey lo hi key

def ints (a : List Int) (x : Int) (lo : Int := 0)
    (hi : Option Int := none) : Result :=
  benchmark_bisect_right a x (fun x y => decide (x < y))
    (fun x y => decide (x < y)) lo hi

def lengths (a : List String) (x : Nat) : Result :=
  benchmark_bisect_right a x (fun x s => decide (x < s.length))
    (fun x y => decide (x < y)) 0 none (some String.length)

example : ints [1,2,4,4,10] 4 = .ok 4 := by native_decide
example : ints [1,2,4,4,10] 0 = .ok 0 := by native_decide
example : ints [1,2,4,4,10] 99 = .ok 5 := by native_decide
example : lengths ["A","bb","CC","ddd"] 1 = .ok 1 := by native_decide
example : lengths ["A","bb","CC","ddd"] 2 = .ok 3 := by native_decide
example : lengths ["A","bb","CC","ddd"] 3 = .ok 4 := by native_decide
example : ints [1,2,3] 1 (-1) = .error .negativeLo := by native_decide
example : ints [1,2,3] 2 0 (some (-3)) = .ok 0 := by native_decide
example : ints [1,2,3] 2 7 (some 2) = .ok 7 := by native_decide
example : ints [1,2,3] 2 0 (some 20) = .error .indexError := by native_decide
example : ints [1,2,4,4,10] 4 1 (some 3) = .ok 3 := by native_decide
#eval ints [1,2,4,4,10] 4
#eval lengths ["A","bb","CC","ddd"] 2

/-- Precisely the Python precondition; `Int` already enforces the integer type. -/
def Pre (_a : List α) (lo : Int) (_hi : Option Int) : Prop := 0 ≤ lo

/-- Even for an unsorted list or an oversized upper bound, a successful search
stays in the original interval (or returns `lo` for an empty interval). -/
def bounds_prop (a : List α) (cut : α → Bool) (lo hi : Nat) : Prop :=
  ∀ i, search a cut lo hi = .ok i → lo ≤ i ∧ i ≤ max lo hi

theorem bounds_thm (a : List α) (cut : α → Bool) (lo hi : Nat) :
    bounds_prop a cut lo hi := by
  unfold bounds_prop
  intro i
  fun_induction search a cut lo hi with
  | case1 lo hi h mid he => simp
  | case2 lo hi h mid v he hc ih =>
    intro hr
    have hp := ih hr
    have hm : (lo + hi) / 2 < hi := by omega
    constructor
    · exact hp.1
    · exact le_trans hp.2 (max_le_max_left lo (by omega))
  | case3 lo hi h mid v he hc ih =>
    intro hr
    have hp := ih hr
    have hm : lo ≤ (lo + hi) / 2 := by omega
    have hm' : (lo + hi) / 2 < hi := by omega
    constructor
    · omega
    · have hmid : mid = (lo + hi) / 2 := rfl
      omega
  | case4 lo hi h =>
    intro hr
    cases hr
    exact ⟨le_rfl, le_max_left _ _⟩

theorem search_not_negative (a : List α) (cut : α → Bool) (lo hi : Nat) :
    search a cut lo hi ≠ .error .negativeLo := by
  fun_induction search a cut lo hi <;> simp_all

/-- A slice is partitionable if `true` comparisons stay true to the right. -/
def MonotoneSlice (a : List α) (cut : α → Bool) (lo hi : Nat) : Prop :=
  ∀ j k v w, lo ≤ j → j ≤ k → k < hi →
    a[j]? = some v → a[k]? = some w → cut v = true → cut w = true

/-- The returned index separates false comparisons from true comparisons.
Only the requested slice is constrained, not the elements outside it. -/
def Partition (a : List α) (cut : α → Bool) (lo hi i : Nat) : Prop :=
  lo ≤ i ∧ i ≤ hi ∧
  (∀ j v, lo ≤ j → j < i → a[j]? = some v → cut v = false) ∧
  (∀ j v, i ≤ j → j < hi → a[j]? = some v → cut v = true)

def safe_prop (a : List α) (cut : α → Bool) (lo hi : Nat) : Prop :=
  hi ≤ a.length → ∃ i, search a cut lo hi = .ok i

theorem safe_thm (a : List α) (cut : α → Bool) (lo hi : Nat) :
    safe_prop a cut lo hi := by
  unfold safe_prop
  fun_induction search a cut lo hi with
  | case1 lo hi h mid he =>
    intro hs
    have hb := List.getElem?_eq_none_iff.mp he
    have hm : (lo + hi) / 2 < hi := by omega
    omega
  | case2 lo hi h mid v he hc ih =>
    intro hs
    apply ih
    have hm : (lo + hi) / 2 < hi := by omega
    omega
  | case3 lo hi h mid v he hc ih => exact ih
  | case4 lo hi h => exact fun _ => ⟨lo, rfl⟩

def partition_prop (a : List α) (cut : α → Bool) (lo hi : Nat) : Prop :=
  lo ≤ hi → hi ≤ a.length → MonotoneSlice a cut lo hi →
  ∃ i, search a cut lo hi = .ok i ∧ Partition a cut lo hi i

theorem partition_thm (a : List α) (cut : α → Bool) (lo hi : Nat) :
    partition_prop a cut lo hi := by
  unfold partition_prop
  fun_induction search a cut lo hi with
  | case1 lo hi h mid he =>
    intro hl hs hm
    have hb := List.getElem?_eq_none_iff.mp he
    have hm' : (lo + hi) / 2 < hi := by omega
    omega
  | case2 lo hi h mid v he hc ih =>
    intro hl hs hm
    have ml : lo ≤ mid := by dsimp [mid]; omega
    have mh : mid < hi := by dsimp [mid]; omega
    have mono : MonotoneSlice a cut lo mid := by
      intro j k u w hj hjk hk hju hkw hu
      exact hm j k u w hj hjk (by omega) hju hkw hu
    obtain ⟨i, hr, hli, him, hleft, hright⟩ := ih ml (by omega) mono
    refine ⟨i, hr, hli, by omega, hleft, ?_⟩
    intro j w hij hjh hjw
    by_cases hjm : j < mid
    · exact hright j w hij hjm hjw
    · exact hm mid j v w ml (by omega) hjh he hjw hc
  | case3 lo hi h mid v he hc ih =>
    intro hl hs hm
    have ml : lo ≤ mid := by dsimp [mid]; omega
    have mh : mid < hi := by dsimp [mid]; omega
    have mono : MonotoneSlice a cut (mid + 1) hi := by
      intro j k u w hj hjk hk hju hkw hu
      exact hm j k u w (by omega) hjk hk hju hkw hu
    obtain ⟨i, hr, hmi, hih, hleft, hright⟩ := ih (by omega) hs mono
    refine ⟨i, hr, by omega, hih, ?_, hright⟩
    intro j w hlj hji hjw
    by_cases hmj : mid < j
    · exact hleft j w (by omega) hji hjw
    · cases hw : cut w with
      | false => rfl
      | true => exact False.elim (hc (hm j mid w v hlj (by omega) mh hjw he hw))
  | case4 lo hi h =>
    intro hl hs hm
    have heq : lo = hi := by omega
    refine ⟨lo, rfl, le_rfl, hl, ?_, ?_⟩ <;> intros <;> omega

/-- Sortedness is needed only within the searched slice. -/
def SortedSlice [LE κ] (a : List α) (key : α → κ) (lo hi : Nat) : Prop :=
  ∀ j k v w, lo ≤ j → j ≤ k → k < hi →
    a[j]? = some v → a[k]? = some w → key v ≤ key w

/-- The familiar ordered specification, including insertion after every equal
key in the searched slice. -/
def ordered_prop [LinearOrder κ] (a : List α) (key : α → κ) (x : κ)
    (lo hi : Nat) : Prop :=
  lo ≤ hi → hi ≤ a.length → SortedSlice a key lo hi →
  ∃ i, search a (fun v => decide (x < key v)) lo hi = .ok i ∧
    lo ≤ i ∧ i ≤ hi ∧
    (∀ j v, lo ≤ j → j < i → a[j]? = some v → key v ≤ x) ∧
    (∀ j v, i ≤ j → j < hi → a[j]? = some v → x < key v) ∧
    (∀ j v, lo ≤ j → j < hi → a[j]? = some v → key v = x → j < i)

theorem ordered_thm [LinearOrder κ] (a : List α) (key : α → κ) (x : κ)
    (lo hi : Nat) : ordered_prop a key x lo hi := by
  intro hl hs hsort
  have hm : MonotoneSlice a (fun v => decide (x < key v)) lo hi := by
    intro j k v w hj hjk hk hjv hkw hv
    have hv' : x < key v := of_decide_eq_true hv
    exact decide_eq_true (lt_of_lt_of_le hv' (hsort j k v w hj hjk hk hjv hkw))
  obtain ⟨i, hr, hli, hih, hleft, hright⟩ := partition_thm a _ lo hi hl hs hm
  refine ⟨i, hr, hli, hih, ?_, ?_, ?_⟩
  · intro j v hj hji hjv
    have hn : ¬ x < key v := of_decide_eq_false (hleft j v hj hji hjv)
    exact le_of_not_gt hn
  · intro j v hij hjh hjv
    exact of_decide_eq_true (hright j v hij hjh hjv)
  · intro j v hj hjh hjv heq
    by_contra hn
    have hv : x < key v := of_decide_eq_true (hright j v (by omega) hjh hjv)
    simp [heq] at hv

/-- Invalid lower bounds are rejected, and no valid lower bound is rejected as
negative. Other errors are deliberately not excluded by `Pre`. -/
def error_prop (a : List α) (x : κ) (lelt : κ → α → Bool)
    (klt : κ → κ → Bool) (lo : Int) (hi : Option Int)
    (key : Option (α → κ)) : Prop :=
  benchmark_bisect_right a x lelt klt lo hi key = .error .negativeLo ↔ lo < 0

theorem error_thm (a : List α) (x : κ) (lelt : κ → α → Bool)
    (klt : κ → κ → Bool) (lo : Int) (hi : Option Int)
    (key : Option (α → κ)) : error_prop a x lelt klt lo hi key := by
  unfold error_prop benchmark_bisect_right
  split
  · simp_all
  · simp_all [bisect_right, search_not_negative]

def empty_prop (a : List α) (x : κ) (lelt : κ → α → Bool)
    (klt : κ → κ → Bool) (lo : Int) (hi : Option Int)
    (key : Option (α → κ)) : Prop :=
  Pre a lo hi → (hi.getD (Int.ofNat a.length)).toNat ≤ lo.toNat →
    benchmark_bisect_right a x lelt klt lo hi key = .ok lo.toNat

theorem empty_thm (a : List α) (x : κ) (lelt : κ → α → Bool)
    (klt : κ → κ → Bool) (lo : Int) (hi : Option Int)
    (key : Option (α → κ)) : empty_prop a x lelt klt lo hi key := by
  intro hp he
  have hn : ¬lo < 0 := by exact not_lt.mpr hp
  simp only [benchmark_bisect_right, if_neg hn, bisect_right]
  rw [search]
  split
  · omega
  · rfl

def default_hi_prop (a : List α) (x : κ) (lelt : κ → α → Bool)
    (klt : κ → κ → Bool) (lo : Int) (key : Option (α → κ)) : Prop :=
  benchmark_bisect_right a x lelt klt lo none key =
    benchmark_bisect_right a x lelt klt lo (some (Int.ofNat a.length)) key

theorem default_hi_thm (a : List α) (x : κ) (lelt : κ → α → Bool)
    (klt : κ → κ → Bool) (lo : Int) (key : Option (α → κ)) :
    default_hi_prop a x lelt klt lo key := by rfl

theorem search_map (a : List α) (f : α → κ) (cut : κ → Bool) (lo hi : Nat) :
    search (a.map f) cut lo hi = search a (fun v => cut (f v)) lo hi := by
  fun_induction search a (fun v => cut (f v)) lo hi with
  | case1 lo hi h mid he =>
    rw [search]
    simp only [mid] at he
    simp [h, List.getElem?_map, he]
  | case2 lo hi h mid v he hc ih =>
    rw [search]
    simp only [mid] at he ih
    simpa [h, List.getElem?_map, he, hc] using ih
  | case3 lo hi h mid v he hc ih =>
    rw [search]
    simp only [mid] at he ih
    simpa [h, List.getElem?_map, he, hc] using ih
  | case4 lo hi h => rw [search]; simp [h]

/-- With a key, searching elements is equivalent to searching their keys.
In particular, the query itself is not transformed. -/
def key_prop (a : List α) (x : κ) (lelt : κ → α → Bool)
    (klt : κ → κ → Bool) (lo : Int) (hi : Option Int)
    (key : Option (α → κ)) : Prop :=
  match key with
  | none => benchmark_bisect_right a x lelt klt lo hi none =
      if lo < 0 then .error .negativeLo
      else search a (lelt x) lo.toNat (hi.getD (Int.ofNat a.length)).toNat
  | some f => benchmark_bisect_right a x lelt klt lo hi (some f) =
      benchmark_bisect_right (a.map f) x klt klt lo hi none

theorem key_thm (a : List α) (x : κ) (lelt : κ → α → Bool)
    (klt : κ → κ → Bool) (lo : Int) (hi : Option Int)
    (key : Option (α → κ)) : key_prop a x lelt klt lo hi key := by
  cases key with
  | none => rfl
  | some f =>
    unfold key_prop benchmark_bisect_right
    split
    · rfl
    · simp only [bisect_right, comparison, List.length_map, search_map]

/-- For a safe slice the boundary characterized by `Partition` is unique. -/
theorem partition_unique (a : List α) (cut : α → Bool) (lo hi i j : Nat)
    (hs : hi ≤ a.length) (hiP : Partition a cut lo hi i)
    (hjP : Partition a cut lo hi j) : i = j := by
  rcases hiP with ⟨hli, hih, hil, hir⟩
  rcases hjP with ⟨hlj, hjh, hjl, hjr⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · have hv : i < a.length := by omega
    have hget := List.getElem?_eq_getElem (l := a) hv
    have ht := hir i a[i] le_rfl (by omega) hget
    have hf := hjl i a[i] hli hij hget
    simp_all
  · exact hij
  · have hv : j < a.length := by omega
    have hget := List.getElem?_eq_getElem (l := a) hv
    have ht := hjr j a[j] le_rfl (by omega) hget
    have hf := hil j a[j] hlj hij hget
    simp_all

/-- Ordered semantics on the public wrapper.  The compatibility equation
allows both the no-key branch (`value = id`) and heterogeneous keyed searches.
It assumes no ordering of elements outside the searched slice. -/
def benchmark_ordered_prop [LinearOrder κ] (a : List α) (x : κ)
    (lelt : κ → α → Bool) (klt : κ → κ → Bool) (lo : Int) (hi : Option Int)
    (key : Option (α → κ)) (value : α → κ) : Prop :=
  Pre a lo hi → comparison x lelt klt key = (fun v => decide (x < value v)) →
  let l := lo.toNat
  let h := (hi.getD (Int.ofNat a.length)).toNat
  l ≤ h → h ≤ a.length → SortedSlice a value l h →
  ∃ i, benchmark_bisect_right a x lelt klt lo hi key = .ok i ∧
    l ≤ i ∧ i ≤ h ∧
    (∀ j v, l ≤ j → j < i → a[j]? = some v → value v ≤ x) ∧
    (∀ j v, i ≤ j → j < h → a[j]? = some v → x < value v) ∧
    (∀ j v, l ≤ j → j < h → a[j]? = some v → value v = x → j < i)

theorem benchmark_ordered_thm [LinearOrder κ] (a : List α) (x : κ)
    (lelt : κ → α → Bool) (klt : κ → κ → Bool) (lo : Int) (hi : Option Int)
    (key : Option (α → κ)) (value : α → κ) :
    benchmark_ordered_prop a x lelt klt lo hi key value := by
  intro hp hc
  dsimp only
  intro hl hh hs
  obtain ⟨i, hr, hrest⟩ := ordered_thm a value x lo.toNat
    (hi.getD (Int.ofNat a.length)).toNat hl hh hs
  refine ⟨i, ?_, hrest⟩
  simpa only [benchmark_bisect_right, if_neg (not_lt.mpr hp), bisect_right, hc] using hr

/-- `Pre` is deliberately not strengthened by sortedness or safe bounds.
The guarantees requiring those assumptions are implications.  The final
conjunct connects every core-search guarantee to the public benchmark result. -/
def Post_prop (a : List α) (x : κ) (lelt : κ → α → Bool)
    (klt : κ → κ → Bool) (lo : Int) (hi : Option Int)
    (key : Option (α → κ)) : Prop :=
  let cut := comparison x lelt klt key
  let l := lo.toNat
  let h := (hi.getD (Int.ofNat a.length)).toNat
  bounds_prop a cut l h ∧ safe_prop a cut l h ∧ partition_prop a cut l h ∧
    error_prop a x lelt klt lo hi key ∧ empty_prop a x lelt klt lo hi key ∧
    default_hi_prop a x lelt klt lo key ∧ key_prop a x lelt klt lo hi key ∧
    benchmark_bisect_right a x lelt klt lo hi key = search a cut l h

/-! ## Bounded property-based tests

These checks use computable, finite-index versions of the propositions, not
proofs of them.  Enumerating all words of length at most three over {-1,0,1}
includes empty, unsorted, constant, and duplicate-containing lists.  Bounds
extend past the end of every such list.  Wrapper tests also use negative lower
and upper bounds, default bounds, and three different optional keys.
-/

def boundsCheck (a : List α) (cut : α → Bool) (lo hi : Nat) : Bool :=
  match search a cut lo hi with
  | .ok i => decide (lo ≤ i ∧ i ≤ max lo hi)
  | .error e => e == .indexError

def safeCheck (a : List α) (cut : α → Bool) (lo hi : Nat) : Bool :=
  if hi ≤ a.length then
    match search a cut lo hi with
    | .ok _ => true
    | .error _ => false
  else true

def monotoneCheck (a : List α) (cut : α → Bool) (lo hi : Nat) : Bool :=
  (List.range hi).all fun j => (List.range hi).all fun k =>
    if lo ≤ j ∧ j ≤ k then
      match a[j]?, a[k]? with
      | some v, some w => !cut v || cut w
      | _, _ => true
    else true

def partitionCheck (a : List α) (cut : α → Bool) (lo hi : Nat)
    (r : Result) : Bool :=
  match r with
  | .error _ => false
  | .ok i => decide (lo ≤ i ∧ i ≤ hi) &&
      (List.range hi).all fun j =>
        if lo ≤ j then
          match a[j]? with
          | some v => if j < i then !cut v else cut v
          | none => false
        else true

def partitionTest (a : List α) (cut : α → Bool) (lo hi : Nat) : Bool :=
  if lo ≤ hi ∧ hi ≤ a.length then
    !monotoneCheck a cut lo hi || partitionCheck a cut lo hi (search a cut lo hi)
  else true

def sortedCheck (a : List Int) (f : Int → Int) (lo hi : Nat) : Bool :=
  (List.range hi).all fun j => (List.range hi).all fun k =>
    if lo ≤ j ∧ j ≤ k then
      match a[j]?, a[k]? with
      | some v, some w => decide (f v ≤ f w)
      | _, _ => true
    else true

def orderedCheck (a : List Int) (f : Int → Int) (x : Int) (lo hi : Nat) : Bool :=
  if lo ≤ hi ∧ hi ≤ a.length then
    if sortedCheck a f lo hi then
      match search a (fun v => decide (x < f v)) lo hi with
      | .error _ => false
      | .ok i => decide (lo ≤ i ∧ i ≤ hi) &&
          (List.range hi).all fun j =>
            if lo ≤ j then
              match a[j]? with
              | none => false
              | some v => (if j < i then decide (f v ≤ x) else decide (x < f v)) &&
                  decide (f v ≠ x ∨ j < i)
            else true
    else true
  else true

def benchmarkOrderedCheck (a : List Int) (x lo : Int) (hi : Option Int)
    (key : Option (Int → Int)) : Bool :=
  let f := key.getD id
  let l := lo.toNat
  let h := (hi.getD (Int.ofNat a.length)).toNat
  if 0 ≤ lo ∧ l ≤ h ∧ h ≤ a.length then
    if sortedCheck a f l h then
      match benchmark_bisect_right a x (fun x y => decide (x < y))
          (fun x y => decide (x < y)) lo hi key with
      | .error _ => false
      | .ok i => decide (l ≤ i ∧ i ≤ h) &&
          (List.range h).all fun j =>
            if l ≤ j then
              match a[j]? with
              | none => false
              | some v => (if j < i then decide (f v ≤ x) else decide (x < f v)) &&
                  decide (f v ≠ x ∨ j < i)
            else true
    else true
  else true

def ilt (x y : Int) : Bool := decide (x < y)

def errorCheck (a : List Int) (x lo : Int) (hi : Option Int)
    (key : Option (Int → Int)) : Bool :=
  (benchmark_bisect_right a x ilt ilt lo hi key == .error .negativeLo) == decide (lo < 0)

def emptyCheck (a : List Int) (x lo : Int) (hi : Option Int)
    (key : Option (Int → Int)) : Bool :=
  if 0 ≤ lo ∧ (hi.getD (Int.ofNat a.length)).toNat ≤ lo.toNat then
    benchmark_bisect_right a x ilt ilt lo hi key == .ok lo.toNat
  else true

def defaultCheck (a : List Int) (x lo : Int) (_hi : Option Int)
    (key : Option (Int → Int)) : Bool :=
  benchmark_bisect_right a x ilt ilt lo none key ==
    benchmark_bisect_right a x ilt ilt lo (some (Int.ofNat a.length)) key

def keyCheck (a : List Int) (x lo : Int) (hi : Option Int)
    (key : Option (Int → Int)) : Bool :=
  let rhs := match key with
    | none => if lo < 0 then .error .negativeLo
        else search a (ilt x) lo.toNat (hi.getD (Int.ofNat a.length)).toNat
    | some f => benchmark_bisect_right (a.map f) x ilt ilt lo hi none
  benchmark_bisect_right a x ilt ilt lo hi key == rhs

def postCheck (a : List Int) (x lo : Int) (hi : Option Int)
    (key : Option (Int → Int)) : Bool :=
  if 0 ≤ lo then
    let cut := comparison x ilt ilt key
    let l := lo.toNat
    let h := (hi.getD (Int.ofNat a.length)).toNat
    boundsCheck a cut l h && safeCheck a cut l h && partitionTest a cut l h &&
      errorCheck a x lo hi key && emptyCheck a x lo hi key &&
      defaultCheck a x lo hi key && keyCheck a x lo hi key &&
      (benchmark_bisect_right a x ilt ilt lo hi key == search a cut l h)
  else true

def words : Nat → List (List Int)
  | 0 => [[]]
  | n+1 => [-1,0,1].flatMap fun x => (words n).map (x :: ·)

def smallLists : List (List Int) := (List.range 4).flatMap words

def searchCases (test : List Int → (Int → Bool) → Nat → Nat → Bool) : Bool :=
  smallLists.all fun a => [-2,-1,0,1,2].all fun x =>
    (List.range 6).all fun lo => (List.range 6).all fun hi => test a (ilt x) lo hi

def sampleKeys : List (Option (Int → Int)) := [none, some (fun v => 2*v), some (fun v => -v)]

def wrapperCases
    (test : List Int → Int → Int → Option Int → Option (Int → Int) → Bool) : Bool :=
  smallLists.all fun a => [-2,-1,0,1,2].all fun x =>
    [-2,-1,0,1,2,3,5].all fun lo =>
      [none, some (-3), some (-1), some 0, some 1, some 2, some 3, some 5].all fun hi =>
        sampleKeys.all fun key => test a x lo hi key

-- PBT for bounds_prop (also checks search_not_negative).
example : searchCases boundsCheck = true := by native_decide
-- PBT for safe_prop.
example : searchCases safeCheck = true := by native_decide
-- PBT for partition_prop, including all partitionable unsorted slices.
example : searchCases partitionTest = true := by native_decide
-- PBT for ordered_prop, including its rightmost-equal clause.
example : (smallLists.all fun a => [-2,-1,0,1,2].all fun x =>
    (List.range 5).all fun lo => (List.range 5).all fun hi =>
      [id, (fun v => -v), (fun v => 2*v)].all fun f => orderedCheck a f x lo hi) = true := by
  native_decide
-- PBT for benchmark_ordered_prop, with and without a key.
example : wrapperCases benchmarkOrderedCheck = true := by native_decide
-- PBT for error_prop.
example : wrapperCases errorCheck = true := by native_decide
-- PBT for empty_prop.
example : wrapperCases emptyCheck = true := by native_decide
-- PBT for default_hi_prop.
example : wrapperCases defaultCheck = true := by native_decide
-- PBT for key_prop (and its underlying search_map correspondence).
example : wrapperCases keyCheck = true := by native_decide
-- PBT for the complete Post_prop, restricted to exactly Pre.
example : wrapperCases postCheck = true := by native_decide
-- PBT for uniqueness: no other boundary satisfies the partition test.
example : (smallLists.all fun a => [-2,-1,0,1,2].all fun x =>
    (List.range (a.length+1)).all fun i =>
      (List.range (a.length+1)).all fun j =>
        !(partitionCheck a (ilt x) 0 a.length (.ok i) &&
          partitionCheck a (ilt x) 0 a.length (.ok j)) || decide (i = j)) = true := by
  native_decide
#eval wrapperCases postCheck

theorem correctness_thm (a : List α) (x : κ) (lelt : κ → α → Bool)
    (klt : κ → κ → Bool) (lo : Int) (hi : Option Int)
    (key : Option (α → κ)) : Pre a lo hi → Post_prop a x lelt klt lo hi key := by
  intro hp
  refine ⟨bounds_thm _ _ _ _, safe_thm _ _ _ _, partition_thm _ _ _ _,
    error_thm _ _ _ _ _ _ _, empty_thm _ _ _ _ _ _ _,
    default_hi_thm _ _ _ _ _ _, key_thm _ _ _ _ _ _ _, ?_⟩
  exact if_neg (not_lt.mpr hp)

/-! ## Imperative implementation

The counted loop is a total version of Python's `while lo < hi`.  Each active
step decreases `hi - lo`, so that many iterations suffice.  Once the interval
is empty, later iterations are no-ops; errors are likewise absorbing.  Unlike
the functional search, this implementation mutates its bounds and its loop
state.  It does not call the functional implementation.
-/

abbrev State := Except Error (Nat × Nat)

def step (a : List α) (cut : α → Bool) (s : State) : State := Id.run do
  match s with
  | .error e => return .error e
  | .ok (lo, hi) =>
    let mut low := lo
    let mut high := hi
    if low < high then
      let mid := (low + high) / 2
      match a[mid]? with
      | none => return .error .indexError
      | some v =>
        if cut v then
          high := mid
        else
          low := mid + 1
    return .ok (low, high)

def iterations (a : List α) (cut : α → Bool) (fuel : Nat) (s : State) : State := Id.run do
  let mut state := s
  for _ in List.replicate fuel () do
    state := step a cut state
  return state

def finish : State → Result
  | .error e => .error e
  | .ok (lo, _) => .ok lo

def searchImperative (a : List α) (cut : α → Bool) (lo hi : Nat) : Result :=
  finish (iterations a cut (hi - lo) (.ok (lo, hi)))

def benchmarkImperative (a : List α) (x : κ)
    (lessElement : κ → α → Bool) (lessKey : κ → κ → Bool)
    (lo : Int := 0) (hi : Option Int := none)
    (key : Option (α → κ) := none) : Result := Id.run do
  if lo < 0 then return .error .negativeLo
  let high := (hi.getD (Int.ofNat a.length)).toNat
  let cut := comparison x lessElement lessKey key
  let mut state : State := .ok (lo.toNat, high)
  for _ in List.replicate (high - lo.toNat) () do
    state := step a cut state
  return finish state

example : benchmarkImperative [1,2,4,4,10] (4 : Int) ilt ilt = .ok 4 := by native_decide
example : benchmarkImperative [1,2,4,4,10] (0 : Int) ilt ilt = .ok 0 := by native_decide
example : benchmarkImperative [1,2,4,4,10] (99 : Int) ilt ilt = .ok 5 := by native_decide
example : benchmarkImperative [1,2,3] (1 : Int) ilt ilt (-1) = .error .negativeLo := by native_decide
example : benchmarkImperative [1,2,3] (1 : Int) ilt ilt 0 (some 20) = .error .indexError := by
  native_decide
example : benchmarkImperative [1,2,3] (1 : Int) ilt ilt 0 (some (-2)) = .ok 0 := by native_decide
example : benchmarkImperative ["A","bb","CC","ddd"] (1 : Nat)
    (fun x s => decide (x < s.length)) (fun x y => decide (x < y))
    0 none (some String.length) = .ok 1 := by native_decide
example : benchmarkImperative ["A","bb","CC","ddd"] (2 : Nat)
    (fun x s => decide (x < s.length)) (fun x y => decide (x < y))
    0 none (some String.length) = .ok 3 := by native_decide
example : benchmarkImperative ["A","bb","CC","ddd"] (3 : Nat)
    (fun x s => decide (x < s.length)) (fun x y => decide (x < y))
    0 none (some String.length) = .ok 4 := by native_decide
#eval benchmarkImperative [1,2,4,4,10] (4 : Int) ilt ilt

-- Bounded PBT for functional/imperative equivalence, including errors and keys.
example : (wrapperCases fun a x lo hi key =>
    benchmark_bisect_right a x ilt ilt lo hi key ==
      benchmarkImperative a x ilt ilt lo hi key) = true := by native_decide

theorem iterations_zero (a : List α) (cut : α → Bool) (s : State) :
    iterations a cut 0 s = s := by rfl

theorem iterations_succ (a : List α) (cut : α → Bool) (n : Nat) (s : State) :
    iterations a cut (n+1) s = iterations a cut n (step a cut s) := by
  simp [iterations, List.replicate_succ]

theorem iterations_error (a : List α) (cut : α → Bool) (n : Nat) (e : Error) :
    iterations a cut n (.error e) = .error e := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterations_succ]; simpa [step] using ih

theorem iterations_empty (a : List α) (cut : α → Bool) (n lo hi : Nat)
    (h : hi ≤ lo) : iterations a cut n (.ok (lo, hi)) = .ok (lo, hi) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterations_succ]
    simpa [step, Nat.not_lt.mpr h] using ih

theorem iterations_correct (a : List α) (cut : α → Bool) (n lo hi : Nat)
    (enough : hi - lo ≤ n) :
    finish (iterations a cut n (.ok (lo, hi))) = search a cut lo hi := by
  induction n generalizing lo hi with
  | zero =>
    have he : ¬lo < hi := by omega
    rw [iterations_zero, search]
    simp [finish, he]
  | succ n ih =>
    by_cases h : lo < hi
    · have ml : lo ≤ (lo + hi) / 2 := by omega
      have mh : (lo + hi) / 2 < hi := by omega
      rw [iterations_succ, search]
      cases hv : a[(lo + hi) / 2]? with
      | none => simp [step, h, hv, iterations_error, finish]
      | some v =>
        cases hc : cut v with
        | false =>
          have hn : hi - ((lo + hi) / 2 + 1) ≤ n := by omega
          simpa [step, h, hv, hc] using ih ((lo + hi) / 2 + 1) hi hn
        | true =>
          have hn : (lo + hi) / 2 - lo ≤ n := by omega
          simpa [step, h, hv, hc] using ih lo ((lo + hi) / 2) hn
    · rw [iterations_empty a cut (n+1) lo hi (by omega), search]
      simp [finish, h]

theorem search_equivalence_thm (a : List α) (cut : α → Bool) (lo hi : Nat) :
    search a cut lo hi = searchImperative a cut lo hi := by
  exact (iterations_correct a cut (hi-lo) lo hi le_rfl).symm

/-- Equivalence on the entire input domain, not merely on sorted or safe inputs. -/
theorem equivalence_thm (a : List α) (x : κ) (lelt : κ → α → Bool)
    (klt : κ → κ → Bool) (lo : Int) (hi : Option Int)
    (key : Option (α → κ)) :
    benchmark_bisect_right a x lelt klt lo hi key =
      benchmarkImperative a x lelt klt lo hi key := by
  by_cases h : lo < 0
  · simp [benchmark_bisect_right, benchmarkImperative, h]
  · simp only [benchmark_bisect_right, if_neg h, bisect_right]
    rw [search_equivalence_thm]
    simp [benchmarkImperative, h, searchImperative, iterations]

end BisectRight
end Agent
