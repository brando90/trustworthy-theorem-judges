import Mathlib
namespace Agent

/-!
# Heap indices and heap-structure predicates (CLRS 6.1)

A zero-based, natural-number model of the Python program. Heap predicates inspect
only the first `min heap_size arr.length` entries. `is_leaf` deliberately does
not require the index to be in the heap. `Nat.log2` models bit-length minus one,
including the specified value zero for the empty heap.

The core uses `Nat` and `List Nat`, so its input contracts are enforced by types.
The `PyValue` boundary additionally models the Python validation errors, including
the exclusion of booleans from natural numbers. Unit/PBT computations are tests;
the named theorems below are independently checked by the Lean kernel.
-/

namespace heapsort_heap_structure

-- Computable equality for checked results, also used by the executable tests.
local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

-- Functional implementation.
def parent (i : Nat) : Nat := (i - 1) / 2
def left (i : Nat) : Nat := 2 * i + 1
def right (i : Nat) : Nat := 2 * i + 2

def entry (arr : List Nat) (i : Nat) : Nat := arr[i]?.getD 0

def maxEdge (arr : List Nat) (i : Nat) : Bool :=
  decide (i = 0 ∨ entry arr i ≤ entry arr (parent i))
def minEdge (arr : List Nat) (i : Nat) : Bool :=
  decide (i = 0 ∨ entry arr (parent i) ≤ entry arr i)

def is_max_heap (arr : List Nat) (heap_size : Nat) : Bool :=
  (List.range (min heap_size arr.length)).all (maxEdge arr)
def is_min_heap (arr : List Nat) (heap_size : Nat) : Bool :=
  (List.range (min heap_size arr.length)).all (minEdge arr)
def heap_height (n : Nat) : Nat := n.log2
def is_leaf (i heap_size : Nat) : Bool := decide (left i ≥ heap_size)

/-- Runtime values at the validation boundary; `other` covers all other types. -/
inductive PyValue where
  | int (n : Int)
  | bool (b : Bool)
  | list (xs : List PyValue)
  | other
  deriving Repr

def natValue : PyValue → Option Nat
  | .int n => if 0 ≤ n then some n.toNat else none
  | _ => none

def natListValue : PyValue → Option (List Nat)
  | .list xs => xs.mapM natValue
  | _ => none

def _is_nat (v : PyValue) : Bool := (natValue v).isSome

def _check_nat (v : PyValue) (name : String := "value") : Except String Unit :=
  if _is_nat v then .ok () else .error (name ++ " must be a natural number")

def _check_nat_list (v : PyValue) (name : String := "arr") : Except String Unit :=
  if (natListValue v).isSome then .ok () else .error (name ++ " must be List[Nat]")

def checkedNat (f : Nat → Nat) (v : PyValue) (name : String) : Except String Nat :=
  match natValue v with
  | some n => .ok (f n)
  | none => .error (name ++ " must be a natural number")

def parent_checked (v : PyValue) := checkedNat parent v "i"
def left_checked (v : PyValue) := checkedNat left v "i"
def right_checked (v : PyValue) := checkedNat right v "i"
def heap_height_checked (v : PyValue) := checkedNat heap_height v "n"

def checkedHeap (f : List Nat → Nat → Bool) (arr size : PyValue) : Except String Bool :=
  match natListValue arr with
  | none => .error "arr must be List[Nat]"
  | some xs => match natValue size with
    | none => .error "heap_size must be a natural number"
    | some n => .ok (f xs n)

def is_max_heap_checked := checkedHeap is_max_heap
def is_min_heap_checked := checkedHeap is_min_heap

def is_leaf_checked (i size : PyValue) : Except String Bool :=
  match natValue i with
  | none => .error "i must be a natural number"
  | some j => match natValue size with
    | none => .error "heap_size must be a natural number"
    | some n => .ok (is_leaf j n)

/-- Collect the seven observable results for a typed invocation. -/
def functional (arr : List Nat) (heap_size i n : Nat) :
    Nat × Nat × Nat × Bool × Bool × Nat × Bool :=
  (parent i, left i, right i, is_max_heap arr heap_size,
    is_min_heap arr heap_size, heap_height n, is_leaf i heap_size)

/-- Executable translation of the Python check harness. -/
def check : Bool := decide (
  (List.range 6).map parent = [0, 0, 0, 1, 1, 2] ∧
  (List.range 3).map left = [1, 3, 5] ∧
  (List.range 3).map right = [2, 4, 6] ∧
  is_max_heap [23, 17, 14, 6, 13, 10, 1, 5, 7, 12] 10 = false ∧
  is_min_heap [1, 2, 3, 4, 5, 6, 7] 7 = true ∧
  is_max_heap [] 0 = true ∧ is_max_heap [42] 1 = true ∧
  is_min_heap [42] 1 = true ∧ is_min_heap [] 0 = true ∧
  [0, 1, 7, 15].map heap_height = [0, 0, 2, 3] ∧
  is_leaf 0 1 = true ∧ is_leaf 0 3 = false ∧
  is_leaf 6 7 = true ∧ is_leaf 2 7 = false ∧
  is_max_heap_checked (.list [.int 1, .int (-1)]) (.int 2) =
    .error "arr must be List[Nat]")

-- The fixed assertions from Python's check().
example : check = true := by native_decide
#eval check
example : (List.range 6).map parent = [0, 0, 0, 1, 1, 2] := by native_decide
example : (List.range 3).map left = [1, 3, 5] := by native_decide
example : (List.range 3).map right = [2, 4, 6] := by native_decide
example : is_max_heap [23, 17, 14, 6, 13, 10, 1, 5, 7, 12] 10 = false := by native_decide
example : is_min_heap [1, 2, 3, 4, 5, 6, 7] 7 = true := by native_decide
example : is_max_heap [] 0 = true := by native_decide
example : is_max_heap [42] 1 = true := by native_decide
example : is_min_heap [42] 1 = true := by native_decide
example : is_min_heap [] 0 = true := by native_decide
example : [0, 1, 7, 15].map heap_height = [0, 0, 2, 3] := by native_decide
example : is_leaf 0 1 = true := by native_decide
example : is_leaf 0 3 = false := by native_decide
example : is_leaf 6 7 = true := by native_decide
example : is_leaf 2 7 = false := by native_decide
example : is_max_heap_checked (.list [.int 1, .int (-1)]) (.int 2) =
    .error "arr must be List[Nat]" := by native_decide
example : parent_checked (.bool true) = .error "i must be a natural number" := by native_decide
example : is_min_heap_checked (.list [.int 1]) (.int (-1)) =
    .error "heap_size must be a natural number" := by native_decide
example : is_max_heap [9, 4, 2] 100 = true := by native_decide
example : is_max_heap [1, 9] 1 = true := by native_decide
example : is_leaf 100 0 = true := by native_decide

#eval (parent 5, left 2, right 2, heap_height 15)
#eval (is_max_heap [23, 17, 14, 6, 13, 10, 1, 5, 7, 12] 10,
       is_min_heap [1, 2, 3, 4, 5, 6, 7] 7)

/-- All typed inputs are admissible. In particular, the size may exceed the list length. -/
def Pre (_arr : List Nat) (_heap_size _i _n : Nat) (_v : PyValue) : Prop := True

-- Property specifications and kernel-checked proofs.
def indices_prop (i : Nat) : Prop :=
  parent 0 = 0 ∧ left i = 2 * i + 1 ∧ right i = left i + 1 ∧
  parent (left i) = i ∧ parent (right i) = i ∧
  (0 < i → parent i < i ∧ (left (parent i) = i ∨ right (parent i) = i))

theorem indices_thm (i : Nat) : indices_prop i := by
  unfold indices_prop parent left right
  omega

def index_safety_prop (arr : List Nat) (heap_size i : Nat) : Prop :=
  i < min heap_size arr.length →
    i < arr.length ∧ (0 < i → parent i < arr.length)

theorem index_safety_thm (arr : List Nat) (heap_size i : Nat) :
    index_safety_prop arr heap_size i := by
  have h := indices_thm i
  unfold indices_prop at h
  unfold index_safety_prop
  omega

/-- At every index actually read, the default in `entry` is irrelevant. -/
theorem entry_eq_getElem (arr : List Nat) (i : Nat) (h : i < arr.length) :
    entry arr i = arr[i] := by
  simp [entry, List.getElem?_eq_getElem h]

def max_heap_prop (arr : List Nat) (heap_size : Nat) : Prop :=
  is_max_heap arr heap_size = true ↔
    ∀ i, 0 < i → i < min heap_size arr.length → entry arr i ≤ entry arr (parent i)

theorem max_heap_thm (arr : List Nat) (heap_size : Nat) : max_heap_prop arr heap_size := by
  unfold max_heap_prop is_max_heap
  simp only [List.all_eq_true, List.mem_range, maxEdge, decide_eq_true_eq]
  constructor
  · intro h i hi hib
    exact (h i hib).resolve_left (by omega)
  · intro h i hib
    by_cases hi : i = 0
    · exact Or.inl hi
    · exact Or.inr (h i (by omega) hib)

def min_heap_prop (arr : List Nat) (heap_size : Nat) : Prop :=
  is_min_heap arr heap_size = true ↔
    ∀ i, 0 < i → i < min heap_size arr.length → entry arr (parent i) ≤ entry arr i

theorem min_heap_thm (arr : List Nat) (heap_size : Nat) : min_heap_prop arr heap_size := by
  unfold min_heap_prop is_min_heap
  simp only [List.all_eq_true, List.mem_range, minEdge, decide_eq_true_eq]
  constructor
  · intro h i hi hib
    exact (h i hib).resolve_left (by omega)
  · intro h i hib
    by_cases hi : i = 0
    · exact Or.inl hi
    · exact Or.inr (h i (by omega) hib)

def clamp_prop (arr : List Nat) (heap_size : Nat) : Prop :=
  is_max_heap arr heap_size = is_max_heap arr (min heap_size arr.length) ∧
  is_min_heap arr heap_size = is_min_heap arr (min heap_size arr.length)

theorem clamp_thm (arr : List Nat) (heap_size : Nat) : clamp_prop arr heap_size := by
  simp [clamp_prop, is_max_heap, is_min_heap]

def prefix_prop (arr : List Nat) (small big : Nat) : Prop :=
  small ≤ big →
    (is_max_heap arr big = true → is_max_heap arr small = true) ∧
    (is_min_heap arr big = true → is_min_heap arr small = true)

theorem prefix_thm (arr : List Nat) (small big : Nat) : prefix_prop arr small big := by
  intro h
  constructor
  · intro hb
    apply (max_heap_thm arr small).mpr
    intro i hi hib
    exact (max_heap_thm arr big).mp hb i hi (by omega)
  · intro hb
    apply (min_heap_thm arr small).mpr
    intro i hi hib
    exact (min_heap_thm arr big).mp hb i hi (by omega)

/-- A max-heap's root is maximal and a min-heap's root is minimal in its active prefix. -/
def root_prop (arr : List Nat) (heap_size i : Nat) : Prop :=
  i < min heap_size arr.length →
    (is_max_heap arr heap_size = true → entry arr i ≤ entry arr 0) ∧
    (is_min_heap arr heap_size = true → entry arr 0 ≤ entry arr i)

theorem root_thm (arr : List Nat) (heap_size i : Nat) : root_prop arr heap_size i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hib
    by_cases hi : i = 0
    · subst i
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
    · have hp : parent i < i := ((indices_thm i).2.2.2.2.2 (by omega)).1
      have hr := ih (parent i) hp (by omega)
      constructor
      · intro hm
        exact le_trans ((max_heap_thm arr heap_size).mp hm i (by omega) hib) (hr.1 hm)
      · intro hm
        exact le_trans (hr.2 hm) ((min_heap_thm arr heap_size).mp hm i (by omega) hib)

def trivial_heaps_prop (arr : List Nat) (n a : Nat) : Prop :=
  is_max_heap arr 0 = true ∧ is_min_heap arr 0 = true ∧
  is_max_heap [] n = true ∧ is_min_heap [] n = true ∧
  is_max_heap [a] n = true ∧ is_min_heap [a] n = true

theorem trivial_heaps_thm (arr : List Nat) (n a : Nat) : trivial_heaps_prop arr n a := by
  unfold trivial_heaps_prop
  have hmax : is_max_heap [a] n = true := by
    apply (max_heap_thm [a] n).mpr
    intro i hi hib
    simp only [List.length_singleton] at hib
    omega
  have hmin : is_min_heap [a] n = true := by
    apply (min_heap_thm [a] n).mpr
    intro i hi hib
    simp only [List.length_singleton] at hib
    omega
  simp [is_max_heap, is_min_heap] at hmax hmin ⊢
  exact ⟨hmax, hmin⟩

def height_prop (n : Nat) : Prop :=
  (n = 0 → heap_height n = 0) ∧
  (0 < n → 2 ^ heap_height n ≤ n ∧ n < 2 ^ (heap_height n + 1))

theorem height_thm (n : Nat) : height_prop n := by
  constructor
  · intro h
    subst n
    exact Nat.log2_zero
  · intro h
    exact ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

def height_mono_prop (n m : Nat) : Prop :=
  n ≤ m → heap_height n ≤ heap_height m

theorem height_mono_thm (n m : Nat) : height_mono_prop n m := by
  intro h
  simpa [heap_height, Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) h

def leaf_prop (i heap_size : Nat) : Prop :=
  (is_leaf i heap_size = true ↔ heap_size / 2 ≤ i) ∧
  (is_leaf i heap_size = true ↔ left i ≥ heap_size ∧ right i ≥ heap_size)

theorem leaf_thm (i heap_size : Nat) : leaf_prop i heap_size := by
  simp only [leaf_prop, is_leaf, decide_eq_true_eq, left, right]
  omega

-- Validation: successful decoding has exactly the intended natural-number domain.
theorem natValue_some_iff (v : PyValue) (n : Nat) :
    natValue v = some n ↔ v = .int (n : Int) := by
  cases v with
  | int z =>
    by_cases hz : 0 ≤ z
    · simp [natValue, hz]
      omega
    · simp [natValue, hz]
      omega
  | bool b => simp [natValue]
  | list xs => simp [natValue]
  | other => simp [natValue]

def encodeList (xs : List Nat) : PyValue := .list (xs.map (fun n : Nat => PyValue.int (n : Int)))

theorem natValues_some_iff (vs : List PyValue) (ns : List Nat) :
    vs.mapM natValue = some ns ↔ vs = ns.map (fun n : Nat => PyValue.int (n : Int)) := by
  induction vs generalizing ns with
  | nil => cases ns <;> simp
  | cons v vs ih =>
    cases hn : natValue v with
    | none =>
      have hv (n : Nat) : v ≠ .int (n : Int) := by
        intro h
        have he := (natValue_some_iff v n).mpr h
        rw [hn] at he
        cases he
      cases ns <;> simp [List.mapM_cons, hn, hv]
    | some n =>
      have hv := (natValue_some_iff v n).mp hn
      subst v
      cases ht : vs.mapM natValue with
      | none =>
        have hv (ns : List Nat) : vs ≠ ns.map (fun n : Nat => PyValue.int (n : Int)) := by
          intro h
          have he := (ih ns).mpr h
          rw [ht] at he
          cases he
        cases ns <;> simp [List.mapM_cons, hn, ht, hv]
      | some ns' =>
        have hi (ks : List Nat) : ns' = ks ↔
            vs = ks.map (fun n : Nat => PyValue.int (n : Int)) := by
          simpa only [ht, Option.some.injEq] using ih ks
        cases ns <;> simp [List.mapM_cons, hn, ht, hi]

theorem natListValue_some_iff (v : PyValue) (ns : List Nat) :
    natListValue v = some ns ↔ v = encodeList ns := by
  cases v with
  | list vs =>
    change vs.mapM natValue = some ns ↔
      PyValue.list vs = PyValue.list (ns.map (fun n : Nat => PyValue.int (n : Int)))
    rw [PyValue.list.injEq, natValues_some_iff]
  | int z => simp only [natListValue, encodeList, reduceCtorEq]
  | bool b => simp only [natListValue, encodeList, reduceCtorEq]
  | other => simp only [natListValue, encodeList, reduceCtorEq]

def validation_prop (v : PyValue) : Prop :=
  (_check_nat v = .ok () ↔ ∃ n : Nat, v = .int (n : Int)) ∧
  (_check_nat_list v = .ok () ↔ ∃ ns : List Nat, v = encodeList ns)

theorem validation_thm (v : PyValue) : validation_prop v := by
  constructor
  · cases hn : natValue v with
    | none =>
      simp only [_check_nat, _is_nat, hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
        false_iff, not_exists]
      intro n hv
      have he := (natValue_some_iff v n).mpr hv
      simp [hn] at he
    | some n =>
      simp only [_check_nat, _is_nat, hn, Option.isSome_some, ↓reduceIte, true_iff]
      exact ⟨n, (natValue_some_iff v n).mp hn⟩
  · cases hn : natListValue v with
    | none =>
      simp only [_check_nat_list, hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
        false_iff, not_exists]
      intro ns hv
      have he := (natListValue_some_iff v ns).mpr hv
      simp [hn] at he
    | some ns =>
      simp only [_check_nat_list, hn, Option.isSome_some, ↓reduceIte, true_iff]
      exact ⟨ns, (natListValue_some_iff v ns).mp hn⟩


/-- `Nat.size` is the bit length, so this also specifies Python's exact formula. -/
def bit_length_prop (n : Nat) : Prop := heap_height n = n.size - 1

theorem bit_length_thm (n : Nat) : bit_length_prop n := by
  unfold bit_length_prop heap_height
  by_cases hn : n = 0
  · subst n; simp
  · have h₁ : n.log2 < n.size := (Nat.log2_lt hn).mpr (Nat.lt_size_self n)
    have h₂ : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
    omega

def boundary_prop (arr : List Nat) (heap_size i n : Nat) : Prop :=
  parent_checked (.int i) = .ok (parent i) ∧
  left_checked (.int i) = .ok (left i) ∧
  right_checked (.int i) = .ok (right i) ∧
  heap_height_checked (.int n) = .ok (heap_height n) ∧
  is_leaf_checked (.int i) (.int heap_size) = .ok (is_leaf i heap_size) ∧
  is_max_heap_checked (encodeList arr) (.int heap_size) = .ok (is_max_heap arr heap_size) ∧
  is_min_heap_checked (encodeList arr) (.int heap_size) = .ok (is_min_heap arr heap_size)

theorem boundary_thm (arr : List Nat) (heap_size i n : Nat) :
    boundary_prop arr heap_size i n := by
  have ha : natListValue (encodeList arr) = some arr :=
    (natListValue_some_iff _ _).mpr rfl
  simp [boundary_prop, parent_checked, left_checked, right_checked,
    heap_height_checked, checkedNat, is_leaf_checked, is_max_heap_checked,
    is_min_heap_checked, checkedHeap, ha, natValue]

/-- Both heap checks validate the array first, even when the requested size is zero. -/
def rejection_prop (arr size : PyValue) : Prop :=
  (natListValue arr = none →
    is_max_heap_checked arr size = .error "arr must be List[Nat]" ∧
    is_min_heap_checked arr size = .error "arr must be List[Nat]") ∧
  (natListValue arr ≠ none → natValue size = none →
    is_max_heap_checked arr size = .error "heap_size must be a natural number" ∧
    is_min_heap_checked arr size = .error "heap_size must be a natural number")

theorem rejection_thm (arr size : PyValue) : rejection_prop arr size := by
  constructor
  · intro h
    simp [is_max_heap_checked, is_min_heap_checked, checkedHeap, h]
  · intro h hs
    cases ha : natListValue arr with
    | none => exact False.elim (h ha)
    | some ns => simp [is_max_heap_checked, is_min_heap_checked, checkedHeap, ha, hs]

/-- Joint specification; it imposes no extra restriction on sizes or indices. -/
def Post_prop (arr : List Nat) (heap_size i n : Nat) (v : PyValue) : Prop :=
  indices_prop i ∧ index_safety_prop arr heap_size i ∧
  max_heap_prop arr heap_size ∧ min_heap_prop arr heap_size ∧
  clamp_prop arr heap_size ∧ prefix_prop arr i heap_size ∧
  root_prop arr heap_size i ∧ trivial_heaps_prop arr heap_size n ∧
  height_prop n ∧ height_mono_prop i n ∧ bit_length_prop n ∧
  leaf_prop i heap_size ∧ validation_prop v ∧
  boundary_prop arr heap_size i n ∧ rejection_prop v (.int heap_size)

-- Property-based tests. These Boolean forms are computational evidence only.
-- They are not used in the proofs. The heap specification checks use the actual
-- Python range 1..size-1, independently of the root-skipping implementation.
def indices_test (i : Nat) : Bool :=
  @decide (indices_prop i) (by unfold indices_prop; infer_instance)
def safety_test (arr : List Nat) (s i : Nat) : Bool :=
  @decide (index_safety_prop arr s i) (by unfold index_safety_prop; infer_instance)
def max_heap_test (arr : List Nat) (s : Nat) : Bool :=
  is_max_heap arr s == (List.range (min s arr.length - 1)).all
    (fun k => decide (entry arr (k + 1) ≤ entry arr (parent (k + 1))))
def min_heap_test (arr : List Nat) (s : Nat) : Bool :=
  is_min_heap arr s == (List.range (min s arr.length - 1)).all
    (fun k => decide (entry arr (parent (k + 1)) ≤ entry arr (k + 1)))
def clamp_test (arr : List Nat) (s : Nat) : Bool :=
  @decide (clamp_prop arr s) (by unfold clamp_prop; infer_instance)
def prefix_test (arr : List Nat) (a b : Nat) : Bool :=
  @decide (prefix_prop arr a b) (by unfold prefix_prop; infer_instance)
def root_test (arr : List Nat) (s i : Nat) : Bool :=
  @decide (root_prop arr s i) (by unfold root_prop; infer_instance)
def trivial_heaps_test (arr : List Nat) (n a : Nat) : Bool :=
  @decide (trivial_heaps_prop arr n a) (by unfold trivial_heaps_prop; infer_instance)
def height_test (n : Nat) : Bool :=
  @decide (height_prop n) (by unfold height_prop; infer_instance)
def height_mono_test (n m : Nat) : Bool :=
  @decide (height_mono_prop n m) (by unfold height_mono_prop; infer_instance)
def bit_length_test (n : Nat) : Bool :=
  @decide (bit_length_prop n) (by unfold bit_length_prop; infer_instance)
def leaf_test (i s : Nat) : Bool :=
  @decide (leaf_prop i s) (by unfold leaf_prop; infer_instance)

def naturalRuntimeSpec : PyValue → Bool
  | .int z => decide (0 ≤ z)
  | _ => false

def listRuntimeSpec : PyValue → Bool
  | .list vs => vs.all naturalRuntimeSpec
  | _ => false

-- Executable counterpart of the existential input-domain characterization.
def validation_test (v : PyValue) : Bool :=
  (decide (_check_nat v = .ok ()) == naturalRuntimeSpec v) &&
  (decide (_check_nat_list v = .ok ()) == listRuntimeSpec v)
def boundary_test (arr : List Nat) (s i n : Nat) : Bool :=
  @decide (boundary_prop arr s i n) (by unfold boundary_prop; infer_instance)
def rejection_test (arr size : PyValue) : Bool :=
  @decide (rejection_prop arr size) (by unfold rejection_prop; infer_instance)

def post_test (arr : List Nat) (s i n : Nat) (v : PyValue) : Bool :=
  indices_test i && safety_test arr s i && max_heap_test arr s && min_heap_test arr s &&
  clamp_test arr s && prefix_test arr i s && root_test arr s i &&
  trivial_heaps_test arr s n && height_test n && height_mono_test i n &&
  bit_length_test n && leaf_test i s && validation_test v &&
  boundary_test arr s i n && rejection_test v (.int s)

/-- All lists of a given length over {0,1,2}. -/
def ternaryLists : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (ternaryLists n).flatMap (fun xs => (List.range 3).map (fun x => x :: xs))
def smallArrays : List (List Nat) := (List.range 5).flatMap ternaryLists

def runtimeSamples : List PyValue :=
  [.other, .bool false, .bool true, .int (-1), .int (-17), .int 0, .int 12,
    .list [], .list [.bool true], .list [.int 1, .int (-1)],
    .list [.list []], .list [.other]] ++ smallArrays.map encodeList

-- PBT: indices_prop (including root and both inverse identities).
example : (List.range 1024).all indices_test = true := by native_decide
-- PBT: index_safety_prop, including oversized heap_size values.
example : smallArrays.all (fun xs => (List.range 9).all (fun s =>
    (List.range 10).all (safety_test xs s))) = true := by native_decide
-- PBT: max_heap_prop and min_heap_prop, over all ternary arrays of length <= 4.
example : smallArrays.all (fun xs => (List.range 9).all (max_heap_test xs)) = true := by native_decide
example : smallArrays.all (fun xs => (List.range 9).all (min_heap_test xs)) = true := by native_decide
-- PBT: clamp_prop.
example : smallArrays.all (fun xs => (List.range 12).all (clamp_test xs)) = true := by native_decide
-- PBT: prefix_prop, both admissible and vacuous implications.
example : smallArrays.all (fun xs => (List.range 8).all (fun a =>
    (List.range 8).all (prefix_test xs a))) = true := by native_decide
-- PBT: root_prop; exhaustive small lists include many valid max and min heaps.
example : smallArrays.all (fun xs => (List.range 8).all (fun s =>
    (List.range 8).all (root_test xs s))) = true := by native_decide
-- PBT: trivial_heaps_prop.
example : smallArrays.all (fun xs => (List.range 8).all (fun s =>
    (List.range 8).all (trivial_heaps_test xs s))) = true := by native_decide
-- PBT: height_prop, height_mono_prop, and bit_length_prop.
example : (List.range 2049).all height_test = true := by native_decide
example : (List.range 100).all (fun n =>
    (List.range 100).all (height_mono_test n)) = true := by native_decide
example : (List.range 2049).all bit_length_test = true := by native_decide
-- PBT: leaf_prop, including indices outside the heap and an empty heap.
example : (List.range 80).all (fun i =>
    (List.range 80).all (leaf_test i)) = true := by native_decide
-- PBT: validation_prop, including wrong types, nested lists, and negatives.
example : runtimeSamples.all validation_test = true := by native_decide
-- PBT: boundary_prop and rejection_prop.
example : smallArrays.all (fun xs => (List.range 8).all (fun s =>
    (List.range 8).all (fun i => boundary_test xs s i (s + i)))) = true := by native_decide
example : runtimeSamples.all (fun v => runtimeSamples.all (rejection_test v)) = true := by native_decide
-- PBT: the entire Post_prop conjunction, not just its individual components.
example : smallArrays.all (fun xs => (List.range 8).all (fun s =>
    (List.range 8).all (fun i => post_test xs s i (s + i) (encodeList xs)))) = true := by native_decide
example : runtimeSamples.all (fun v => (List.range 20).all
    (fun n => post_test [9, 8, 7, 6, 5, 4, 3] n n n v)) = true := by native_decide
#eval smallArrays.length
#eval runtimeSamples.all validation_test
#eval (List.range 2049).all (fun n => height_test n && bit_length_test n)

-- Correctness: typing is the precondition, and no bound on heap_size is assumed.
theorem correctness_thm (arr : List Nat) (heap_size i n : Nat) (v : PyValue) :
    Pre arr heap_size i n v → Post_prop arr heap_size i n v := by
  intro _
  exact ⟨indices_thm i, index_safety_thm arr heap_size i,
    max_heap_thm arr heap_size, min_heap_thm arr heap_size,
    clamp_thm arr heap_size, prefix_thm arr i heap_size,
    root_thm arr heap_size i, trivial_heaps_thm arr heap_size n,
    height_thm n, height_mono_thm i n, bit_length_thm n,
    leaf_thm i heap_size, validation_thm v,
    boundary_thm arr heap_size i n, rejection_thm v (.int heap_size)⟩

-- Imperative implementation. No imperative function calls its functional twin.
def parent_imp (i : Nat) : Nat := Id.run do
  let mut p := 0
  if 0 < i then
    p := (i - 1) / 2
  return p

def left_imp (i : Nat) : Nat := Id.run do
  let mut child := i
  child := child + i
  child := child + 1
  return child

def right_imp (i : Nat) : Nat := Id.run do
  let mut child := i
  child := child + i
  child := child + 2
  return child

/-- Mutable scan: once false, the accumulator remains false. -/
def scanImp (p : Nat → Bool) (xs : List Nat) (initial : Bool) : Bool := Id.run do
  let mut ok := initial
  for i in xs do
    ok := ok && p i
  return ok

def is_max_heap_imp (arr : List Nat) (heap_size : Nat) : Bool := Id.run do
  let mut size := heap_size
  if arr.length < size then
    size := arr.length
  let mut ok := true
  ok := scanImp (maxEdge arr) (List.range size) ok
  return ok

def is_min_heap_imp (arr : List Nat) (heap_size : Nat) : Bool := Id.run do
  let mut size := heap_size
  if arr.length < size then
    size := arr.length
  let mut ok := true
  ok := scanImp (minEdge arr) (List.range size) ok
  return ok

/-- A terminating division loop, written recursively to expose its decreasing measure. -/
def heap_height_imp (n : Nat) : Nat := Id.run do
  let mut q := n
  let mut h := 0
  if 2 ≤ q then
    q := q / 2
    h := heap_height_imp q + 1
  return h
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

def is_leaf_imp (i heap_size : Nat) : Bool := Id.run do
  let mut leaf := false
  if heap_size ≤ left_imp i then
    leaf := true
  return leaf

def imperative (arr : List Nat) (heap_size i n : Nat) :
    Nat × Nat × Nat × Bool × Bool × Nat × Bool := Id.run do
  let p := parent_imp i
  let l := left_imp i
  let r := right_imp i
  let maxHeap := is_max_heap_imp arr heap_size
  let minHeap := is_min_heap_imp arr heap_size
  let height := heap_height_imp n
  let leaf := is_leaf_imp i heap_size
  return (p, l, r, maxHeap, minHeap, height, leaf)

-- The same validation boundary for the imperative algorithms.
def parent_checked_imp (v : PyValue) := checkedNat parent_imp v "i"
def left_checked_imp (v : PyValue) := checkedNat left_imp v "i"
def right_checked_imp (v : PyValue) := checkedNat right_imp v "i"
def heap_height_checked_imp (v : PyValue) := checkedNat heap_height_imp v "n"
def is_max_heap_checked_imp := checkedHeap is_max_heap_imp
def is_min_heap_checked_imp := checkedHeap is_min_heap_imp

def is_leaf_checked_imp (i size : PyValue) : Except String Bool :=
  match natValue i with
  | none => .error "i must be a natural number"
  | some j => match natValue size with
    | none => .error "heap_size must be a natural number"
    | some n => .ok (is_leaf_imp j n)

-- Imperative fixed tests, including the negative-input assertion.
example : (List.range 6).map parent_imp = [0, 0, 0, 1, 1, 2] := by native_decide
example : (List.range 3).map left_imp = [1, 3, 5] := by native_decide
example : (List.range 3).map right_imp = [2, 4, 6] := by native_decide
example : is_max_heap_imp [23, 17, 14, 6, 13, 10, 1, 5, 7, 12] 10 = false := by native_decide
example : is_min_heap_imp [1, 2, 3, 4, 5, 6, 7] 7 = true := by native_decide
example : is_max_heap_imp [] 0 = true ∧ is_max_heap_imp [42] 1 = true ∧
    is_min_heap_imp [42] 1 = true ∧ is_min_heap_imp [] 0 = true := by native_decide
example : [0, 1, 7, 15].map heap_height_imp = [0, 0, 2, 3] := by native_decide
example : is_leaf_imp 0 1 = true ∧ is_leaf_imp 0 3 = false ∧
    is_leaf_imp 6 7 = true ∧ is_leaf_imp 2 7 = false := by native_decide
example : is_max_heap_checked_imp (.list [.int 1, .int (-1)]) (.int 2) =
    .error "arr must be List[Nat]" := by native_decide
#eval imperative [1, 2, 3, 4, 5, 6, 7] 7 6 15

-- Bounded equivalence tests: successful runs, errors, and all height transitions.
example : smallArrays.all (fun xs => (List.range 8).all (fun s =>
    (List.range 8).all (fun i => decide
      (functional xs s i (s + i) = imperative xs s i (s + i))))) = true := by native_decide
example : (List.range 2049).all (fun n =>
    decide (heap_height n = heap_height_imp n)) = true := by native_decide
example : runtimeSamples.all (fun a => runtimeSamples.all (fun s => decide
    (is_max_heap_checked a s = is_max_heap_checked_imp a s ∧
     is_min_heap_checked a s = is_min_heap_checked_imp a s ∧
     is_leaf_checked a s = is_leaf_checked_imp a s))) = true := by native_decide

-- Equivalence proofs: no test, native_decide, or unproved assumption is used.
theorem parent_equiv_thm (i : Nat) : parent i = parent_imp i := by
  by_cases h : 0 < i
  · simp [parent, parent_imp, h]
  · have hi : i = 0 := by omega
    subst i
    simp [parent, parent_imp]

theorem left_equiv_thm (i : Nat) : left i = left_imp i := by
  simp [left, left_imp]
  omega

theorem right_equiv_thm (i : Nat) : right i = right_imp i := by
  simp [right, right_imp]
  omega

/-- The loop invariant is that the accumulator is the initial flag AND the scanned edges. -/
theorem scanImp_eq_thm (p : Nat → Bool) (xs : List Nat) (initial : Bool) :
    scanImp p xs initial = (initial && xs.all p) := by
  induction xs generalizing initial with
  | nil => simp [scanImp]
  | cons x xs ih =>
    simpa [scanImp, List.forIn_cons, Bool.and_assoc] using ih (initial && p x)

theorem max_heap_equiv_thm (arr : List Nat) (heap_size : Nat) :
    is_max_heap arr heap_size = is_max_heap_imp arr heap_size := by
  by_cases h : arr.length < heap_size
  · simp [is_max_heap_imp, h, scanImp_eq_thm, is_max_heap, min_eq_right (by omega : arr.length ≤ heap_size)]
  · simp [is_max_heap_imp, h, scanImp_eq_thm, is_max_heap, min_eq_left (by omega : heap_size ≤ arr.length)]

theorem min_heap_equiv_thm (arr : List Nat) (heap_size : Nat) :
    is_min_heap arr heap_size = is_min_heap_imp arr heap_size := by
  by_cases h : arr.length < heap_size
  · simp [is_min_heap_imp, h, scanImp_eq_thm, is_min_heap, min_eq_right (by omega : arr.length ≤ heap_size)]
  · simp [is_min_heap_imp, h, scanImp_eq_thm, is_min_heap, min_eq_left (by omega : heap_size ≤ arr.length)]

theorem height_equiv_thm (n : Nat) : heap_height n = heap_height_imp n := by
  symm
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [heap_height_imp]
    change (if 2 ≤ n then heap_height_imp (n / 2) + 1 else 0) = n.log2
    by_cases hn : 2 ≤ n
    · rw [if_pos hn, ih (n / 2) (Nat.div_lt_self (by omega) (by omega))]
      simpa only [heap_height, Nat.log2_eq_log_two] using
        (Nat.log_of_one_lt_of_le (by decide : 1 < 2) hn).symm
    · rw [if_neg hn, Nat.log2_eq_log_two, Nat.log_of_lt (by omega : n < 2)]

theorem leaf_equiv_thm (i heap_size : Nat) : is_leaf i heap_size = is_leaf_imp i heap_size := by
  by_cases h : heap_size ≤ left i
  · simp [is_leaf, is_leaf_imp, ← left_equiv_thm, h]
  · simp [is_leaf, is_leaf_imp, ← left_equiv_thm, h]

theorem equivalence_thm (arr : List Nat) (heap_size i n : Nat) :
    functional arr heap_size i n = imperative arr heap_size i n := by
  simp [functional, imperative, parent_equiv_thm, left_equiv_thm, right_equiv_thm,
    max_heap_equiv_thm, min_heap_equiv_thm, height_equiv_thm, leaf_equiv_thm]

/-- Equality holds for every runtime input, including all validation failures. -/
theorem checked_equivalence_thm (arr size i n : PyValue) :
    parent_checked i = parent_checked_imp i ∧
    left_checked i = left_checked_imp i ∧
    right_checked i = right_checked_imp i ∧
    heap_height_checked n = heap_height_checked_imp n ∧
    is_leaf_checked i size = is_leaf_checked_imp i size ∧
    is_max_heap_checked arr size = is_max_heap_checked_imp arr size ∧
    is_min_heap_checked arr size = is_min_heap_checked_imp arr size := by
  have hp : parent = parent_imp := funext parent_equiv_thm
  have hl : left = left_imp := funext left_equiv_thm
  have hr : right = right_imp := funext right_equiv_thm
  have hh : heap_height = heap_height_imp := funext height_equiv_thm
  have hmax : is_max_heap = is_max_heap_imp := funext (fun xs => funext (max_heap_equiv_thm xs))
  have hmin : is_min_heap = is_min_heap_imp := funext (fun xs => funext (min_heap_equiv_thm xs))
  simp [parent_checked, parent_checked_imp, left_checked, left_checked_imp,
    right_checked, right_checked_imp, heap_height_checked, heap_height_checked_imp,
    is_leaf_checked, is_leaf_checked_imp, is_max_heap_checked, is_max_heap_checked_imp,
    is_min_heap_checked, is_min_heap_checked_imp, hp, hl, hr, hh, hmax, hmin, leaf_equiv_thm]

end heapsort_heap_structure
end Agent
