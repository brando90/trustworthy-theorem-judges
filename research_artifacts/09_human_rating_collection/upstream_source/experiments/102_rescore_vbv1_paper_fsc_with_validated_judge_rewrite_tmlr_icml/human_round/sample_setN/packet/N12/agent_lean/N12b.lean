import Mathlib

/-!
# Counting sort for integers

The functional algorithm finds the minimum and maximum, enumerates the shifted
integer range, and emits each key as many times as it occurs in the input.
`Int` models Python's unbounded integers. The typed interface `List Int` enforces
the Python precondition; a checked, dynamically tagged interface below also
models rejection of non-integer elements. Mutable histograms are represented by
index-to-counter functions (zero outside the allocated range).
-/

namespace counting_sort

deriving instance DecidableEq for Except

/-- Bounds are only used on nonempty lists; the empty-list defaults are zero. -/
def lower (xs : List Int) : Int := xs.foldl min (xs.headD 0)
def upper (xs : List Int) : Int := xs.foldl max (xs.headD 0)

/-- The keys corresponding to the shifted slots of the count array. -/
def keys (lo : Int) (n : Nat) : List Int :=
  (List.range n).map (fun (i : Nat) => lo + (i : Int))

/-- Emit a histogram in key order. -/
def emit (xs ks : List Int) : List Int :=
  ks.flatMap (fun k => List.replicate (xs.count k) k)

def countingSort (xs : List Int) : List Int :=
  if xs.isEmpty then []
  else emit xs (keys (lower xs) (upper xs - lower xs + 1).toNat)

/-- A tagged Python value. All non-integer object kinds are rejected.
Booleans are accepted because Python's `bool` is a subclass of `int`.
The `other` constructor abstracts all remaining Python object kinds. -/
inductive PyValue where
  | integer (n : Int)
  | boolean (b : Bool)
  | floating (x : Float)
  | other

inductive PyInput where
  | list (xs : List PyValue)
  | nonList

def decodeValue : PyValue → Option Int
  | .integer n => some n
  | .boolean b => some (if b then 1 else 0)
  | .floating _ | .other => none

def decodeList : List PyValue → Option (List Int)
  | [] => some []
  | x :: xs => do
    let n ← decodeValue x
    let ns ← decodeList xs
    pure (n :: ns)

def decodeInput : PyInput → Option (List Int)
  | .list xs => decodeList xs
  | .nonList => none

/-- `Except.error` is the source's ValueError, with the original message. -/
def checkedSort (a : PyInput) : Except String (List Int) :=
  match decodeInput a with
  | none => .error "Input must be List[int]"
  | some xs => .ok (countingSort xs)

-- The complete integer-valued suite from the source, plus signed examples.
example : countingSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : countingSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : countingSort [] = [] := by native_decide
example : countingSort [1] = [1] := by native_decide
example : countingSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [2, 1] = [1, 2] := by native_decide
example : countingSort [1, 2] = [1, 2] := by native_decide
example : countingSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSort [3, 1, 2, 1, 3, 2] = [1, 1, 2, 2, 3, 3] := by native_decide
example : countingSort [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : countingSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSort [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide
example : countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : countingSort [-3, 0, -1, -3, 2] = [-3, -3, -1, 0, 2] := by native_decide
example : countingSort [-5, -9, -7] = [-9, -7, -5] := by native_decide
#eval countingSort [3, -2, 0, 3, -2]

example : checkedSort (.list [.integer 1, .floating 2.5]) =
    .error "Input must be List[int]" := by native_decide
example : checkedSort .nonList = .error "Input must be List[int]" := by native_decide
example : checkedSort (.list [.boolean true, .integer (-1), .boolean false]) =
    .ok [-1, 0, 1] := by native_decide
#eval checkedSort (.list [.integer 1, .floating 2.5])

/-- Every inhabitant of `List Int` satisfies the Python type precondition. -/
def Pre (_xs : List Int) : Prop := True

/-- Executable type check on the dynamically tagged interface. -/
def DynamicPre (a : PyInput) : Prop := (decodeInput a).isSome = true

private theorem fold_min_bounds (xs : List Int) (z : Int) :
    xs.foldl min z ≤ z ∧ ∀ x ∈ xs, xs.foldl min z ≤ x := by
  induction xs generalizing z with
  | nil => simp
  | cons a xs ih =>
    rcases ih (min z a) with ⟨h, hm⟩
    simp only [List.foldl_cons]
    constructor
    · exact h.trans (min_le_left _ _)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.trans (min_le_right _ _)
      · exact hm x hx

private theorem fold_max_bounds (xs : List Int) (z : Int) :
    z ≤ xs.foldl max z ∧ ∀ x ∈ xs, x ≤ xs.foldl max z := by
  induction xs generalizing z with
  | nil => simp
  | cons a xs ih =>
    rcases ih (max z a) with ⟨h, hm⟩
    simp only [List.foldl_cons]
    constructor
    · exact (le_max_left _ _).trans h
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (le_max_right _ _).trans h
      · exact hm x hx

theorem lower_le (xs : List Int) (x : Int) (hx : x ∈ xs) : lower xs ≤ x :=
  (fold_min_bounds xs (xs.headD 0)).2 x hx

theorem le_upper (xs : List Int) (x : Int) (hx : x ∈ xs) : x ≤ upper xs :=
  (fold_max_bounds xs (xs.headD 0)).2 x hx

theorem mem_keys (lo x : Int) (n : Nat) :
    x ∈ keys lo n ↔ lo ≤ x ∧ x < lo + (n : Int) := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have := List.mem_range.mp hi
    omega
  · rintro ⟨hlo, hhi⟩
    apply List.mem_map.mpr
    refine ⟨(x - lo).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega

theorem keys_nodup (lo : Int) (n : Nat) : (keys lo n).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro i j h
  dsimp at h
  omega

theorem keys_ordered (lo : Int) (n : Nat) :
    (keys lo n).Pairwise (· ≤ ·) := by
  apply List.pairwise_map.mpr
  apply List.pairwise_lt_range.imp
  intro i j h
  dsimp
  omega

theorem keys_cover (xs : List Int) (x : Int) (hx : x ∈ xs) :
    x ∈ keys (lower xs) (upper xs - lower xs + 1).toNat := by
  apply (mem_keys _ _ _).mpr
  have hl := lower_le xs x hx
  have hu := le_upper xs x hx
  constructor <;> omega

/-- Every key is emitted once per occurrence in the original input. -/
theorem count_emit (xs ks : List Int) (v : Int) :
    (emit xs ks).count v = ks.count v * xs.count v := by
  induction ks with
  | nil => simp [emit]
  | cons k ks ih =>
    change (List.replicate (xs.count k) k ++ emit xs ks).count v = _
    rw [List.count_append, ih, List.count_cons, List.count_replicate]
    by_cases h : k = v
    · subst k
      simp [Nat.add_mul, Nat.add_comm]
    · simp [h]

theorem emit_ordered (xs ks : List Int) (h : ks.Pairwise (· ≤ ·)) :
    (emit xs ks).Pairwise (· ≤ ·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro k _
    exact List.pairwise_replicate.mpr (Or.inr (le_refl k))
  · apply h.imp
    intro a b hab x hx y hy
    have hx' := (List.mem_replicate.mp hx).2
    have hy' := (List.mem_replicate.mp hy).2
    simpa [hx', hy'] using hab

/-- Nondecreasing order, allowing duplicate keys. -/
def sorted_prop (xs : List Int) : Prop :=
  (countingSort xs).Pairwise (· ≤ ·)

theorem sorted_thm (xs : List Int) : sorted_prop xs := by
  unfold sorted_prop countingSort
  split
  · simp
  · exact emit_ordered _ _ (keys_ordered _ _)

/-- Exact preservation of multiplicities, including absent and negative keys. -/
def counts_prop (xs : List Int) : Prop :=
  ∀ v : Int, (countingSort xs).count v = xs.count v

theorem counts_thm (xs : List Int) : counts_prop xs := by
  intro v
  unfold countingSort
  split
  · rename_i h
    have hx : xs = [] := List.isEmpty_iff.mp h
    simp [hx]
  · rw [count_emit]
    by_cases hv : v ∈ xs
    · have hk := keys_cover xs v hv
      have hn := keys_nodup (lower xs) (upper xs - lower xs + 1).toNat
      have hc : (keys (lower xs) (upper xs - lower xs + 1).toNat).count v = 1 := by
        exact List.count_eq_one_of_mem hn hk
      simp [hc]
    · simp [List.count_eq_zero.mpr hv]

/-- Output is a permutation of the input, not merely a sorted list. -/
def permutation_prop (xs : List Int) : Prop := (countingSort xs).Perm xs

theorem permutation_thm (xs : List Int) : permutation_prop xs :=
  List.perm_iff_count.mpr (counts_thm xs)

def length_prop (xs : List Int) : Prop := (countingSort xs).length = xs.length

theorem length_thm (xs : List Int) : length_prop xs :=
  (permutation_thm xs).length_eq

def membership_prop (xs : List Int) : Prop :=
  ∀ v : Int, v ∈ countingSort xs ↔ v ∈ xs

theorem membership_thm (xs : List Int) : membership_prop xs :=
  fun _ => (permutation_thm xs).mem_iff

def idempotent_prop (xs : List Int) : Prop :=
  countingSort (countingSort xs) = countingSort xs

theorem idempotent_thm (xs : List Int) : idempotent_prop xs :=
  List.eq_of_perm_of_sorted (permutation_thm (countingSort xs))
    (sorted_thm (countingSort xs)) (sorted_thm xs)

def sorted_input_prop (xs : List Int) : Prop :=
  xs.Pairwise (· ≤ ·) → countingSort xs = xs

theorem sorted_input_thm (xs : List Int) : sorted_input_prop xs :=
  fun h => List.eq_of_perm_of_sorted (permutation_thm xs) (sorted_thm xs) h

def empty_prop : Prop := countingSort [] = []

theorem empty_thm : empty_prop := by rfl

def singleton_prop (x : Int) : Prop := countingSort [x] = [x]

theorem singleton_thm (x : Int) : singleton_prop x :=
  sorted_input_thm [x] (by simp)

def bounds_prop (xs : List Int) : Prop :=
  ∀ x ∈ countingSort xs, lower xs ≤ x ∧ x ≤ upper xs

theorem bounds_thm (xs : List Int) : bounds_prop xs := by
  intro x hx
  have hm := (membership_thm xs x).mp hx
  exact ⟨lower_le xs x hm, le_upper xs x hm⟩

/-- The checked interface rejects exactly the precondition violations. -/
def rejection_prop (a : PyInput) : Prop :=
  checkedSort a = .error "Input must be List[int]" ↔ ¬ DynamicPre a

theorem rejection_thm (a : PyInput) : rejection_prop a := by
  unfold rejection_prop checkedSort DynamicPre
  cases decodeInput a <;> simp

private theorem decode_integers (xs : List Int) :
    decodeList (xs.map PyValue.integer) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [decodeList, decodeValue, ih]

def acceptance_prop (xs : List Int) : Prop :=
  checkedSort (.list (xs.map PyValue.integer)) = .ok (countingSort xs)

theorem acceptance_thm (xs : List Int) : acceptance_prop xs := by
  simp [acceptance_prop, checkedSort, decodeInput, decode_integers]

/-- Complete sorting contract. Multiplicity preservation rules out both loss
and invention of elements; the remaining clauses expose useful consequences. -/
def Post_prop (xs : List Int) : Prop :=
  sorted_prop xs ∧ counts_prop xs ∧ permutation_prop xs ∧ length_prop xs ∧
  membership_prop xs ∧ idempotent_prop xs ∧ sorted_input_prop xs ∧ bounds_prop xs ∧
  (xs = [] → empty_prop) ∧ acceptance_prop xs

/-! ## Property-based tests

Exhaustive bounded PBTs: all 781 lists of length at most four over five signed
keys. Universal count and membership clauses are checked on the union of the
input and output supports, and additionally on absent probes -3 and 3.
No theorem below is proved by these tests.
-/

def smallLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => [] :: ([-2, -1, 0, 1, 2] : List Int).flatMap
      (fun x => (smallLists n).map (x :: ·))

def samples : List (List Int) := smallLists 4

def countCheck (xs ys : List Int) : Bool :=
  ([-3, 3] ++ xs ++ ys).all (fun v => xs.count v == ys.count v)

def memberCheck (xs ys : List Int) : Bool :=
  ([-3, 3] ++ xs ++ ys).all (fun v => decide (v ∈ xs ↔ v ∈ ys))

-- sorted_prop
example : samples.all (fun xs => decide ((countingSort xs).Pairwise (· ≤ ·))) = true := by
  native_decide
-- counts_prop
example : samples.all (fun xs => countCheck (countingSort xs) xs) = true := by native_decide
-- permutation_prop
example : samples.all (fun xs => decide ((countingSort xs).Perm xs)) = true := by native_decide
-- length_prop
example : samples.all (fun xs => (countingSort xs).length == xs.length) = true := by native_decide
-- membership_prop
example : samples.all (fun xs => memberCheck (countingSort xs) xs) = true := by native_decide
-- idempotent_prop
example : samples.all (fun xs => countingSort (countingSort xs) == countingSort xs) = true := by
  native_decide
-- sorted_input_prop (decidable implication, not a filtered collection of only easy cases)
example : samples.all (fun xs => decide (xs.Pairwise (· ≤ ·) → countingSort xs = xs)) = true := by
  native_decide
-- bounds_prop
example : samples.all (fun xs => (countingSort xs).all
    (fun x => decide (lower xs ≤ x ∧ x ≤ upper xs))) = true := by native_decide
-- empty_prop has no inputs; check the empty outcome alongside all generated inputs.
example : samples.all (fun xs => decide (countingSort [] = [] ∧
    (xs = [] → countingSort xs = []))) = true := by native_decide
-- singleton_prop, including signed keys beyond the list-test alphabet
example : (List.range 101).all (fun n =>
    decide (countingSort [(n : Int) - 50] = [(n : Int) - 50])) = true := by native_decide
-- acceptance_prop
example : samples.all (fun xs => decide
    (checkedSort (.list (xs.map PyValue.integer)) = .ok (countingSort xs))) = true := by
  native_decide

/-- Every integer sample, and failures both before and after its integer elements. -/
def dynamicSamples : List PyInput :=
  [.nonList, .list [.boolean true, .boolean false], .list [.floating 2.0]] ++
  samples.flatMap (fun xs =>
    let vs := xs.map PyValue.integer
    [.list vs, .list (.floating 2.5 :: vs), .list (vs ++ [.other])])

-- rejection_prop: direct executable form, including all modeled input kinds.
example : dynamicSamples.all (fun a => decide
    (checkedSort a = .error "Input must be List[int]") == !(decodeInput a).isSome) = true := by
  native_decide

/-- Executable counterpart of the entire postcondition. -/
def postCheck (xs : List Int) : Bool :=
  let ys := countingSort xs
  decide (ys.Pairwise (· ≤ ·)) && countCheck ys xs && decide (ys.Perm xs) &&
  (ys.length == xs.length) && memberCheck ys xs &&
  (countingSort ys == ys) && decide (xs.Pairwise (· ≤ ·) → ys = xs) &&
  ys.all (fun x => decide (lower xs ≤ x ∧ x ≤ upper xs)) &&
  decide (xs = [] → countingSort [] = []) &&
  decide (checkedSort (.list (xs.map PyValue.integer)) = .ok ys)

-- Post_prop
example : samples.all postCheck = true := by native_decide
#eval (samples.length, samples.all postCheck)

/-- Kernel-checked correctness, independent of all executable tests. -/
theorem correctness (xs : List Int) : Pre xs → Post_prop xs := by
  intro _
  exact ⟨sorted_thm xs, counts_thm xs, permutation_thm xs, length_thm xs,
    membership_thm xs, idempotent_thm xs, sorted_input_thm xs, bounds_thm xs,
    fun _ => empty_thm, acceptance_thm xs⟩

/-- Successful dynamic calls enjoy the same sorting specification. -/
theorem checked_correctness (a : PyInput) (h : DynamicPre a) :
    ∃ xs, decodeInput a = some xs ∧ checkedSort a = .ok (countingSort xs) ∧ Post_prop xs := by
  cases hd : decodeInput a with
  | none => simp [DynamicPre, hd] at h
  | some xs => exact ⟨xs, rfl, by simp [checkedSort, hd], correctness xs trivial⟩

/-! ## Imperative counting sort
The count array is modeled extensionally: slot `i` stores a natural counter.
Only indices in `[0, range_size)` are ever accessed. A function representation
avoids machine-size limits while keeping the source's update semantics.
-/

def bump (c : Nat → Nat) (i : Nat) : Nat → Nat :=
  fun j => if j = i then c j + 1 else c j

def countingSortImperative (xs : List Int) : List Int := Id.run do
  if xs.isEmpty then return []
  let lo := lower xs
  let hi := upper xs
  let rangeSize := (hi - lo + 1).toNat
  let mut count : Nat → Nat := fun _ => 0
  for num in xs do
    count := bump count (num - lo).toNat
  let mut result : List Int := []
  for i in List.range rangeSize do
    result := result ++ List.replicate (count i) (lo + (i : Int))
  return result

example : countingSortImperative [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSortImperative [] = [] := by native_decide
example : countingSortImperative [1] = [1] := by native_decide
example : countingSortImperative [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSortImperative [-3, 0, -1, -3, 2] = [-3, -3, -1, 0, 2] := by native_decide
example : countingSortImperative [-5, -9, -7] = [-9, -7, -5] := by native_decide
example : samples.all (fun xs => countingSortImperative xs == countingSort xs) = true := by
  native_decide
#eval countingSortImperative [3, -2, 0, 3, -2]

/-- The first loop's invariant: each shifted slot accumulates its exact frequency. -/
theorem histogram_fold (xs : List Int) (lo : Int)
    (h : ∀ x ∈ xs, lo ≤ x) (c : Nat → Nat) (i : Nat) :
    (xs.foldl (fun c x => bump c (x - lo).toNat) c) i =
      c i + xs.count (lo + (i : Int)) := by
  induction xs generalizing c with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ xs, lo ≤ y := fun y hy => h y (by simp [hy])
    rw [List.foldl_cons, ih ht, List.count_cons]
    by_cases he : i = (x - lo).toNat
    · have he' : x = lo + (i : Int) := by omega
      have hb : bump c (x - lo).toNat i = c i + 1 := if_pos he
      rw [hb]
      simp [he', Nat.add_comm, Nat.add_left_comm]
    · have he' : x ≠ lo + (i : Int) := by omega
      simp [bump, he, he']

/-- Every array write performed by the source's counting loop is in range. -/
theorem shifted_index_in_range (xs : List Int) (x : Int) (hx : x ∈ xs) :
    (x - lower xs).toNat < (upper xs - lower xs + 1).toNat := by
  have hl := lower_le xs x hx
  have hu := le_upper xs x hx
  omega

/-- The mutable histogram and reconstruction loops implement the functional sort. -/
theorem functional_eq_imperative (xs : List Int) :
    countingSort xs = countingSortImperative xs := by
  have hc : xs.foldl (fun c x => bump c (x - lower xs).toNat) (fun _ => 0) =
      fun (i : Nat) => xs.count (lower xs + (i : Int)) := by
    funext i
    simpa using histogram_fold xs (lower xs) (fun x hx => lower_le xs x hx) (fun _ => 0) i
  by_cases h : xs = [] <;>
    simp [countingSort, countingSortImperative, h, List.foldl_append_eq_append,
      hc, emit, keys, List.flatMap, Id.run] <;> rfl

end counting_sort
