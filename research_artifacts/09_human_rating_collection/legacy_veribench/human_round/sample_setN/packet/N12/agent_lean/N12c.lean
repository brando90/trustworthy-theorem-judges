import Mathlib

/-!
# Counting Sort

Counting sort for a list of integers, including negatives via a shift so that
the minimum value maps to index `0`. This follows the Python program:

* the empty list returns the empty list;
* otherwise compute `min` and `max`, count occurrences of every integer in
  that closed range, and emit values from `min` to `max` according to those
  counts.

The Python precondition that every element is an `int` is expressed by the
type `List Int`.
-/

namespace counting_sort

/-- Emit `len` consecutive buckets starting at `start`, each value repeated
by its multiplicity in `arr`. This is the reconstruction phase of counting sort. -/
def emitFrom (arr : List Int) (start : Int) : Nat → List Int
  | 0 => []
  | n + 1 => List.replicate (arr.count start) start ++ emitFrom arr (start + 1) n

/-- Functional counting sort. Empty input (no minimum) yields `[]`. -/
def countingSort (arr : List Int) : List Int :=
  match arr.min?, arr.max? with
  | some mn, some mx => emitFrom arr mn ((mx - mn).toNat + 1)
  | _, _ => []

/-! ## Unit tests -/

example : countingSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : countingSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : countingSort ([] : List Int) = [] := by native_decide
example : countingSort [1] = [1] := by native_decide
example : countingSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : countingSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [2, 1] = [1, 2] := by native_decide
example : countingSort [1, 2] = [1, 2] := by native_decide
example : countingSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSort [3, 1, 2, 1, 3, 2] = [1, 1, 2, 2, 3, 3] := by native_decide
example : countingSort [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : countingSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : countingSort [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide
example : countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : countingSort [-1, -3, 2, 0] = [-3, -1, 0, 2] := by native_decide
example : countingSort [-5, -5, -1] = [-5, -5, -1] := by native_decide
example : countingSort [0, -2, -2, 3] = [-2, -2, 0, 3] := by native_decide

#eval countingSort [3, 1, 2]
#eval countingSort ([] : List Int)
#eval countingSort [-1, 4, -3, 0]

/-! ## Precondition -/

/-- Python `pre` checks that the argument is a list of integers.
At this layer that obligation is the type `List Int`, so the predicate holds
for every well-typed input. -/
def Pre (_arr : List Int) : Prop := True

/-! ## Auxiliary lemmas -/

theorem count_replicate_ne {a b : Int} {n : Nat} (h : a ≠ b) :
    (List.replicate n a).count b = 0 := by
  rw [List.count_replicate]
  simp [h]

theorem emitFrom_ge (arr : List Int) (start : Int) (len : Nat) {x : Int}
    (hx : x ∈ emitFrom arr start len) : start ≤ x := by
  induction len generalizing start x with
  | zero => simp [emitFrom] at hx
  | succ n ih =>
    rw [emitFrom] at hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩ | hx
    · exact Int.le_refl _
    · exact Int.le_trans (by omega : start ≤ start + 1) (ih (start := start + 1) hx)

theorem emitFrom_sorted_pairwise (arr : List Int) (start : Int) (len : Nat) :
    (emitFrom arr start len).Pairwise (· ≤ ·) := by
  induction len generalizing start with
  | zero => simp [emitFrom]
  | succ n ih =>
    rw [emitFrom, List.pairwise_append]
    refine ⟨(List.pairwise_replicate).2 (Or.inr (Int.le_refl _)), ih (start := start + 1), ?_⟩
    intro a ha b hb
    obtain ⟨_, haeq⟩ := List.mem_replicate.mp ha
    rw [haeq]
    exact Int.le_trans (by omega : start ≤ start + 1) (emitFrom_ge arr (start + 1) n hb)

theorem emitFrom_count_lt (arr : List Int) (start : Int) (len : Nat) {x : Int}
    (hx : x < start) : (emitFrom arr start len).count x = 0 := by
  induction len generalizing start with
  | zero => simp [emitFrom]
  | succ n ih =>
    rw [emitFrom, List.count_append, count_replicate_ne (a := start) (b := x) (by omega),
      Nat.zero_add]
    exact ih (start := start + 1) (by omega)

theorem count_emitFrom_bucket (arr : List Int) (start : Int) (len : Nat)
    (k : Nat) (hk : k < len) :
    (emitFrom arr start len).count (start + ↑k) = arr.count (start + ↑k) := by
  induction len generalizing start k with
  | zero => omega
  | succ n ih =>
    rw [emitFrom, List.count_append]
    cases k with
    | zero =>
      have hz : start + ↑(0 : Nat) = start := by simp
      rw [hz, List.count_replicate_self, emitFrom_count_lt arr (start + 1) n (by omega),
        Nat.add_zero]
    | succ k =>
      rw [count_replicate_ne (a := start) (b := start + ↑(Nat.succ k)) (by omega), Nat.zero_add]
      have hshift : start + ↑(Nat.succ k) = start + 1 + ↑k := by omega
      rw [hshift]
      exact ih (start := start + 1) k (by omega)

theorem count_emitFrom_out (arr : List Int) (start : Int) (len : Nat) {x : Int}
    (hx : ∀ k, k < len → x ≠ start + ↑k) :
    (emitFrom arr start len).count x = 0 := by
  induction len generalizing start with
  | zero => simp [emitFrom]
  | succ n ih =>
    rw [emitFrom, List.count_append]
    have hne : x ≠ start := by
      intro h
      exact hx 0 (by omega) (by simp [h])
    rw [count_replicate_ne (a := start) (b := x) hne.symm, Nat.zero_add]
    apply ih (start := start + 1)
    intro k hk
    have hshift : start + 1 + ↑k = start + ↑(k + 1) := by omega
    rw [hshift]
    exact hx (k + 1) (by omega)

theorem emitFrom_succ_le (arr : List Int) (start : Int) (len : Nat) {x : Int}
    (hx : x ∈ emitFrom arr start len) : x + 1 ≤ start + ↑len := by
  induction len generalizing start x with
  | zero => simp [emitFrom] at hx
  | succ n ih =>
    rw [emitFrom] at hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩ | hx
    · omega
    · have := ih (start := start + 1) hx
      omega

theorem int_min?_spec {xs : List Int} {a : Int} :
    xs.min? = some a ↔ a ∈ xs ∧ ∀ b ∈ xs, a ≤ b := by
  simpa using
    List.min?_eq_some_iff (α := Int) (xs := xs) (a := a)
      (le_refl := fun _ => Int.le_refl _)
      (min_eq_or := min_choice)
      (le_min_iff := fun _ _ _ => le_min_iff)
      (anti := fun _ _ _ _ h1 h2 => Int.le_antisymm h1 h2)

theorem int_max?_spec {xs : List Int} {a : Int} :
    xs.max? = some a ↔ a ∈ xs ∧ ∀ b ∈ xs, b ≤ a := by
  haveI : Std.Antisymm (· ≤ · : Int → Int → Prop) := ⟨fun _ _ => Int.le_antisymm⟩
  simpa using
    List.max?_eq_some_iff (α := Int) (xs := xs) (a := a)
      (le_refl := fun _ => Int.le_refl _)
      (max_eq_or := max_choice)
      (max_le_iff := fun _ _ _ => max_le_iff)

theorem index_lt_range {mn mx y : Int} (hmn : mn ≤ y) (hmx : y ≤ mx) :
    (y - mn).toNat < (mx - mn).toNat + 1 := by
  have h1 : 0 ≤ y - mn := by omega
  have h2 : 0 ≤ mx - mn := by omega
  have h3 : y - mn ≤ mx - mn := by omega
  have h4 : (y - mn).toNat ≤ (mx - mn).toNat := by
    rw [← Int.ofNat_le, Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
    exact h3
  omega

theorem eq_min_add_index {mn y : Int} (hmn : mn ≤ y) :
    y = mn + ↑((y - mn).toNat) := by
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ y - mn)]
  omega

/-! ## Properties -/

/-- The output is sorted nondecreasingly. -/
def sorted_prop (arr : List Int) : Prop :=
  List.Sorted (· ≤ ·) (countingSort arr)

theorem sorted_thm (arr : List Int) : sorted_prop arr := by
  unfold sorted_prop countingSort
  cases hmin : arr.min? <;> cases hmax : arr.max? <;> simp [List.Sorted]
  · exact emitFrom_sorted_pairwise arr _ _

/-- Counting sort preserves multiplicities of every integer. -/
def count_prop (arr : List Int) : Prop :=
  ∀ x : Int, (countingSort arr).count x = arr.count x

theorem count_thm (arr : List Int) : count_prop arr := by
  intro x
  unfold countingSort
  cases hmin : arr.min? <;> cases hmax : arr.max? <;> simp
  · have harr : arr = [] := List.min?_eq_none_iff.mp hmin
    simp [harr]
  · have harr : arr = [] := List.min?_eq_none_iff.mp hmin
    simp [harr] at hmax
  · have harr : arr = [] := List.max?_eq_none_iff.mp hmax
    simp [harr] at hmin
  · rename_i mn mx
    have hmn := (int_min?_spec (xs := arr) (a := mn)).1 hmin
    have hmx := (int_max?_spec (xs := arr) (a := mx)).1 hmax
    let len := (mx - mn).toNat + 1
    change (emitFrom arr mn len).count x = arr.count x
    by_cases hex : ∃ k : Nat, k < len ∧ x = mn + ↑k
    · obtain ⟨k, hk, rfl⟩ := hex
      exact count_emitFrom_bucket arr mn len k hk
    · rw [count_emitFrom_out arr mn len (fun k hk heq => hex ⟨k, hk, heq⟩)]
      apply Eq.symm
      apply List.count_eq_zero.mpr
      intro hx
      have hlo : mn ≤ x := hmn.2 x hx
      have hhi : x ≤ mx := hmx.2 x hx
      refine hex ⟨(x - mn).toNat, index_lt_range hlo hhi, ?_⟩
      exact eq_min_add_index hlo

/-- The output is a permutation of the input. -/
def perm_prop (arr : List Int) : Prop :=
  List.Perm (countingSort arr) arr

theorem perm_thm (arr : List Int) : perm_prop arr := by
  unfold perm_prop
  rw [List.perm_iff_count]
  intro x
  exact count_thm arr x

/-- Length is preserved. -/
def length_prop (arr : List Int) : Prop :=
  (countingSort arr).length = arr.length

theorem length_thm (arr : List Int) : length_prop arr := by
  unfold length_prop
  have hperm := perm_thm arr
  unfold perm_prop at hperm
  exact hperm.length_eq

/-- Membership is preserved. -/
def mem_prop (arr : List Int) : Prop :=
  ∀ x : Int, x ∈ countingSort arr ↔ x ∈ arr

theorem mem_thm (arr : List Int) : mem_prop arr := by
  intro x
  have hperm := perm_thm arr
  unfold perm_prop at hperm
  exact hperm.mem_iff

/-- Sorting the empty list yields the empty list. -/
def empty_prop : Prop :=
  countingSort ([] : List Int) = []

theorem empty_thm : empty_prop := by
  unfold empty_prop countingSort
  simp

/-- Sorting is idempotent. -/
def idempotent_prop (arr : List Int) : Prop :=
  countingSort (countingSort arr) = countingSort arr

theorem idempotent_thm (arr : List Int) : idempotent_prop arr := by
  unfold idempotent_prop
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · have hperm := perm_thm (countingSort arr)
    unfold perm_prop at hperm
    exact hperm
  · have hsort := sorted_thm (countingSort arr)
    unfold sorted_prop at hsort
    exact hsort
  · have hsort := sorted_thm arr
    unfold sorted_prop at hsort
    exact hsort

/-- Every output element lies between the input minimum and maximum. -/
def bounds_prop (arr : List Int) : Prop :=
  match arr.min?, arr.max? with
  | some mn, some mx => ∀ x ∈ countingSort arr, mn ≤ x ∧ x ≤ mx
  | _, _ => countingSort arr = []

theorem bounds_thm (arr : List Int) : bounds_prop arr := by
  unfold bounds_prop countingSort
  cases hmin : arr.min? <;> cases hmax : arr.max? <;> simp
  · rename_i mn mx
    intro x hx
    have hmn := (int_min?_spec (xs := arr) (a := mn)).1 hmin
    have hmx := (int_max?_spec (xs := arr) (a := mx)).1 hmax
    have hle : mn ≤ mx := hmx.2 mn hmn.1
    refine ⟨emitFrom_ge arr mn _ hx, ?_⟩
    have hsucc := emitFrom_succ_le arr mn ((mx - mn).toNat + 1) hx
    have hspan : mn + ↑((mx - mn).toNat + 1) = mx + 1 := by
      have h0 : 0 ≤ mx - mn := by omega
      have hcast : (↑((mx - mn).toNat) : Int) = mx - mn := Int.toNat_of_nonneg h0
      have hadd : (↑((mx - mn).toNat + 1) : Int) = ↑((mx - mn).toNat) + 1 := by
        simp [Nat.cast_add]
      omega
    omega

/-- Post-condition: counting sort returns the unique sorted permutation of the input,
preserving counts, length, membership, bounds, and idempotence. -/
def Post_prop (arr : List Int) : Prop :=
  sorted_prop arr ∧ count_prop arr ∧ perm_prop arr ∧ length_prop arr ∧
    mem_prop arr ∧ idempotent_prop arr ∧ bounds_prop arr ∧
    (arr = [] → countingSort arr = [])

/-! ## Property-based tests -/

def sortedBool : List Int → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a ≤ b) && sortedBool (b :: rest)

def countsMatch (a b : List Int) : Bool :=
  a.all (fun x => a.count x == b.count x) && b.all (fun x => a.count x == b.count x)

def memMatch (a b : List Int) : Bool :=
  a.all (fun x => b.contains x) && b.all (fun x => a.contains x)

def boundsBool (arr : List Int) : Bool :=
  match arr.min?, arr.max? with
  | some mn, some mx =>
    (countingSort arr).all fun x => decide (mn ≤ x) && decide (x ≤ mx)
  | _, _ => countingSort arr == []

def postBool (arr : List Int) : Bool :=
  sortedBool (countingSort arr) && countsMatch (countingSort arr) arr &&
    ((countingSort arr).length == arr.length) &&
    memMatch (countingSort arr) arr &&
    (countingSort (countingSort arr) == countingSort arr) &&
    boundsBool arr &&
    (!(arr == []) || countingSort arr == [])

def smallVals : List Int := [-2, -1, 0, 1, 2]

def enumLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (enumLists n).flatMap fun xs => smallVals.map fun a => a :: xs

def boundedLists : List (List Int) :=
  enumLists 0 ++ enumLists 1 ++ enumLists 2 ++ enumLists 3

example : boundedLists.all (fun xs => sortedBool (countingSort xs)) = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, sortedBool (countingSort xs) = true)

example : boundedLists.all (fun xs => countsMatch (countingSort xs) xs) = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, countsMatch (countingSort xs) xs = true)

example : boundedLists.all (fun xs => countsMatch (countingSort xs) xs &&
    (countingSort xs).length == xs.length) = true := by native_decide
#eval Plausible.Testable.check
  (∀ xs : List Int, countsMatch (countingSort xs) xs = true ∧ (countingSort xs).length = xs.length)

example : boundedLists.all (fun xs => (countingSort xs).length == xs.length) = true := by
  native_decide
#eval Plausible.Testable.check (∀ xs : List Int, (countingSort xs).length = xs.length)

example : boundedLists.all (fun xs => memMatch (countingSort xs) xs) = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, memMatch (countingSort xs) xs = true)

example : (List.range 5).all (fun _ => countingSort ([] : List Int) == []) = true := by
  native_decide
#eval Plausible.Testable.check (countingSort ([] : List Int) = [])

example : boundedLists.all (fun xs => countingSort (countingSort xs) == countingSort xs) = true := by
  native_decide
#eval Plausible.Testable.check (∀ xs : List Int, countingSort (countingSort xs) = countingSort xs)

example : boundedLists.all (fun xs => boundsBool xs) = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, boundsBool xs = true)

example : boundedLists.all (fun xs => postBool xs) = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, postBool xs = true)

/-! ## Correctness -/

theorem countingSort_correct_thm (arr : List Int) (h : Pre arr) : Post_prop arr := by
  cases h
  exact ⟨sorted_thm arr, count_thm arr, perm_thm arr, length_thm arr, mem_thm arr,
    idempotent_thm arr, bounds_thm arr, fun harr => by
      subst harr
      simpa [empty_prop] using empty_thm⟩

/-! ## Imperative implementation -/

/-- Increment the bucket for `num` in a count array shifted by `mn`. -/
def incrCount (mn : Int) (counts : Array Nat) (num : Int) : Array Nat :=
  if h : (num - mn).toNat < counts.size then
    counts.set (num - mn).toNat (counts[(num - mn).toNat] + 1) h
  else
    counts

/-- Imperative counting sort: mutable count array, then a mutable emit buffer.
This mirrors the Python loops (`count[num - min] += 1`, then `extend`). -/
def countingSortImp (arr : List Int) : List Int :=
  Id.run do
    match arr.min?, arr.max? with
    | some mn, some mx =>
      let rangeSize := (mx - mn).toNat + 1
      let mut counts : Array Nat := Array.replicate rangeSize 0
      for num in arr do
        counts := incrCount mn counts num
      let mut result : List Int := []
      for i in List.range rangeSize do
        result := result ++ List.replicate (counts[i]?.getD 0) (mn + (i : Int))
      return result
    | _, _ =>
      return []

/-! ## Imperative tests -/

example : countingSortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSortImp ([] : List Int) = [] := by native_decide
example : countingSortImp [1] = [1] := by native_decide
example : countingSortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSortImp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSortImp [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide
example : countingSortImp [-1, -3, 2, 0] = [-3, -1, 0, 2] := by native_decide
example : countingSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : countingSortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide

#eval countingSortImp [3, 1, 2]
#eval countingSortImp [-2, 0, -2, 1]

/-! ## Equivalence -/

theorem forIn_yield_eq_foldl' {α β : Type} (l : List α) (f : α → β → β) (init : β) :
    forIn (m := Id) l init (fun a b => ForInStep.yield (f a b)) =
      l.foldl (fun b a => f a b) init :=
  List.forIn_pure_yield_eq_foldl (m := Id) f init

theorem size_incrCount (mn : Int) (counts : Array Nat) (num : Int) :
    (incrCount mn counts num).size = counts.size := by
  unfold incrCount
  split
  · simp [Array.size_set]
  · rfl

theorem get_incrCount (mn : Int) (counts : Array Nat) (num : Int) (i : Nat)
    (hi : i < counts.size) :
    (incrCount mn counts num)[i]'(by rw [size_incrCount]; exact hi) =
      counts[i] + if (num - mn).toNat = i then 1 else 0 := by
  unfold incrCount
  split
  · rename_i hidx
    by_cases heq : (num - mn).toNat = i
    · simp [heq]
    · simp [heq, hi]
  · rename_i hidx
    have hne : (num - mn).toNat ≠ i := fun heq => hidx (by simpa [heq] using hi)
    simp [hne]

theorem toNat_sub_eq_iff {y mn : Int} {i : Nat} (hy : mn ≤ y) :
    (y - mn).toNat = i ↔ y = mn + ↑i := by
  constructor
  · intro h
    have hcast : ((y - mn).toNat : Int) = y - mn := Int.toNat_of_nonneg (by omega)
    omega
  · intro h
    have : y - mn = ↑i := by omega
    simp [this]

theorem foldl_incrCount_size (xs : List Int) (mn : Int) (init : Array Nat) :
    (xs.foldl (fun c n => incrCount mn c n) init).size = init.size := by
  induction xs generalizing init with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [ih, size_incrCount]

theorem foldl_incrCount_get (xs : List Int) (mn : Int) (init : Array Nat)
    (hcover : ∀ y ∈ xs, mn ≤ y ∧ (y - mn).toNat < init.size)
    (i : Nat) (hi : i < init.size) :
    (xs.foldl (fun c n => incrCount mn c n) init)[i]'(by rw [foldl_incrCount_size]; exact hi) =
      init[i] + xs.count (mn + ↑i) := by
  induction xs generalizing init with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, List.count_cons]
    have hsize : (incrCount mn init y).size = init.size := size_incrCount _ _ _
    have hcover' : ∀ z ∈ ys, mn ≤ z ∧ (z - mn).toNat < (incrCount mn init y).size := by
      intro z hz
      have hz' := hcover z (List.mem_cons_of_mem _ hz)
      exact ⟨hz'.1, by simpa [hsize] using hz'.2⟩
    have hi' : i < (incrCount mn init y).size := by simpa [hsize] using hi
    rw [ih (incrCount mn init y) hcover' hi']
    rw [get_incrCount mn init y i hi]
    have hy : mn ≤ y := (hcover y List.mem_cons_self).1
    have hiff : (y - mn).toNat = i ↔ y = mn + ↑i := toNat_sub_eq_iff hy
    have hbeq : (y == (mn + ↑i)) = true ↔ y = mn + ↑i := by simp
    cases h : decide ((y - mn).toNat = i) <;> simp [hiff, hbeq] at * <;> omega

theorem emitFrom_eq_flatten (arr : List Int) (start : Int) (len : Nat) :
    emitFrom arr start len =
      ((List.range len).map fun (i : Nat) =>
        List.replicate (arr.count (start + ↑i)) (start + ↑i)).flatten := by
  induction len generalizing start with
  | zero => simp [emitFrom]
  | succ n ih =>
    rw [emitFrom, List.range_succ_eq_map]
    simp only [List.map_cons, List.flatten_cons, List.map_map]
    have hz : start + ↑(0 : Nat) = start := by simp
    simp only [hz]
    apply congrArg (fun t => List.replicate (arr.count start) start ++ t)
    rw [ih]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i _hi
    have h : start + 1 + ↑i = start + ↑(Nat.succ i) := by omega
    simp [h]

theorem countingSortImp_flatten (arr : List Int) :
    countingSortImp arr =
      match arr.min?, arr.max? with
      | some mn, some mx =>
        let len := (mx - mn).toNat + 1
        let counts :=
          List.foldl (fun b a => incrCount mn b a) (Array.replicate len 0) arr
        ((List.range len).map fun (i : Nat) =>
          List.replicate (counts[i]?.getD 0) (mn + ↑i)).flatten
      | _, _ => [] := by
  cases hmin : arr.min? <;> cases hmax : arr.max? <;>
    simp [countingSortImp, Id.run, bind, pure, forIn_yield_eq_foldl', hmin, hmax]

theorem buildCounts_getD (arr : List Int) (mn : Int) (len : Nat)
    (hcover : ∀ y ∈ arr, mn ≤ y ∧ (y - mn).toNat < len)
    (i : Nat) (hi : i < len) :
    (arr.foldl (fun c n => incrCount mn c n) (Array.replicate len 0))[i]?.getD 0 =
      arr.count (mn + ↑i) := by
  have hsize :
      (arr.foldl (fun c n => incrCount mn c n) (Array.replicate len 0)).size = len := by
    rw [foldl_incrCount_size]
    simp
  rw [Array.getD_getElem?]
  simp only [hsize, hi]
  have hbase : i < (Array.replicate len 0).size := by simp [hi]
  have hg :=
    foldl_incrCount_get arr mn (Array.replicate len 0)
      (fun y hy => ⟨(hcover y hy).1, by simpa using (hcover y hy).2⟩) i hbase
  simpa [Array.getElem_replicate] using hg

theorem counts_flatten_eq_emitFrom (arr : List Int) (mn : Int) (len : Nat)
    (hcover : ∀ y ∈ arr, mn ≤ y ∧ (y - mn).toNat < len) :
    ((List.range len).map fun (i : Nat) =>
      List.replicate
        ((arr.foldl (fun c n => incrCount mn c n) (Array.replicate len 0))[i]?.getD 0)
        (mn + ↑i)).flatten =
      emitFrom arr mn len := by
  have hmap :
      ((List.range len).map fun (i : Nat) =>
        List.replicate
          ((arr.foldl (fun c n => incrCount mn c n) (Array.replicate len 0))[i]?.getD 0)
          (mn + ↑i)) =
      ((List.range len).map fun (i : Nat) =>
        List.replicate (arr.count (mn + ↑i)) (mn + ↑i)) := by
    apply List.map_congr_left
    intro i hi
    rw [buildCounts_getD arr mn len hcover i (List.mem_range.mp hi)]
  rw [hmap]
  exact (emitFrom_eq_flatten arr mn len).symm

/-- Functional counting sort equals the imperative implementation. -/
theorem equiv_thm (arr : List Int) : countingSort arr = countingSortImp arr := by
  rw [countingSortImp_flatten]
  cases hmin : arr.min? <;> cases hmax : arr.max? <;> simp [countingSort, hmin, hmax]
  · rename_i mn mx
    have hmn := (int_min?_spec (xs := arr) (a := mn)).1 hmin
    have hmx := (int_max?_spec (xs := arr) (a := mx)).1 hmax
    have hcover : ∀ y ∈ arr, mn ≤ y ∧ (y - mn).toNat < (mx - mn).toNat + 1 := by
      intro y hy
      exact ⟨hmn.2 y hy, index_lt_range (hmn.2 y hy) (hmx.2 y hy)⟩
    simpa using (counts_flatten_eq_emitFrom arr mn ((mx - mn).toNat + 1) hcover).symm

end counting_sort
