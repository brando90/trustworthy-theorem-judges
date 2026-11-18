import Mathlib
namespace Agent

/-!
# HumanEval 37: sort_even

The input is a list of arbitrary mathematical integers (including negatives).
Indices are zero based. We extract the even and odd subsequences, sort the
former, and alternate the two again. The specifications below express length,
unchanged odd entries, and sortedness and multiset preservation of even entries.
-/

namespace humaneval_37_sort_even

/-- Entries at indices 0, 2, 4, ... . -/
def evenEntries : List Int → List Int
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: evenEntries xs

/-- Entries at indices 1, 3, 5, ... . -/
def oddEntries : List Int → List Int
  | [] => []
  | [_] => []
  | _ :: y :: xs => y :: oddEntries xs

/-- Alternate two lists, retaining any unpaired suffix. -/
def weave : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => x :: y :: weave xs ys

/-- Functional translation of the Python function. -/
def sort_even (l : List Int) : List Int :=
  weave ((evenEntries l).mergeSort (· ≤ ·)) (oddEntries l)

example : sort_even [1, 2, 3] = [1, 2, 3] := by native_decide
example : sort_even [5, 6, 3, 4] = [3, 6, 5, 4] := by native_decide
example : sort_even [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] =
    [-10, 3, -5, 2, -3, 3, 5, 0, 9, 1, 123] := by native_decide
example : sort_even [5, 8, -12, 4, 23, 2, 3, 11, 12, -10] =
    [-12, 8, 3, 4, 5, 2, 12, 11, 23, -10] := by native_decide
example : sort_even [] = [] := by native_decide
example : sort_even [-7] = [-7] := by native_decide
#eval sort_even [5, 6, 3, 4]
#eval sort_even [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]

/-- Python imposes no additional restriction on integer lists. -/
def Pre (_l : List Int) : Prop := True

/-! ## Structural proof foundations -/

/-- Induction which consumes a pair of consecutive positions at a time. -/
theorem pair_induction {P : List Int → Prop}
    (hnil : P []) (hsingle : ∀ x, P [x])
    (hpair : ∀ x y xs, P xs → P (x :: y :: xs)) : ∀ xs, P xs
  | [] => hnil
  | [x] => hsingle x
  | x :: y :: xs => hpair x y xs (pair_induction hnil hsingle hpair xs)

theorem split_lengths (l : List Int) :
    (evenEntries l).length + (oddEntries l).length = l.length ∧
    (oddEntries l).length ≤ (evenEntries l).length ∧
    (evenEntries l).length ≤ (oddEntries l).length + 1 := by
  induction l using pair_induction with
  | hnil => simp [evenEntries, oddEntries]
  | hsingle x => simp [evenEntries, oddEntries]
  | hpair x y xs ih =>
      simp only [evenEntries, oddEntries, List.length_cons] at *
      omega

theorem weave_length (es os : List Int) :
    (weave es os).length = es.length + os.length := by
  induction es generalizing os with
  | nil => simp [weave]
  | cons e es ih =>
      cases os with
      | nil => simp [weave]
      | cons o os => simp [weave, ih]; omega

theorem weave_entries (es os : List Int)
    (hlo : os.length ≤ es.length) (hhi : es.length ≤ os.length + 1) :
    evenEntries (weave es os) = es ∧ oddEntries (weave es os) = os := by
  induction es generalizing os with
  | nil =>
      have ho : os = [] := List.length_eq_zero_iff.mp (by simpa using hlo)
      subst os
      simp [weave, evenEntries, oddEntries]
  | cons e es ih =>
      cases os with
      | nil =>
          have he : es = [] := List.length_eq_zero_iff.mp (by simpa using hhi)
          subst es
          simp [weave, evenEntries, oddEntries]
      | cons o os =>
          have hs := ih os (by simpa using hlo) (by simpa using hhi)
          simp [weave, evenEntries, oddEntries, hs.1, hs.2]

theorem weave_split (l : List Int) : weave (evenEntries l) (oddEntries l) = l := by
  induction l using pair_induction with
  | hnil => rfl
  | hsingle x => rfl
  | hpair x y xs ih => simp [evenEntries, oddEntries, weave, ih]

theorem weave_perm (es os : List Int) : (weave es os).Perm (es ++ os) := by
  induction es generalizing os with
  | nil => simp [weave]
  | cons e es ih =>
      cases os with
      | nil => simp [weave]
      | cons o os =>
          simp only [weave, List.cons_append]
          exact ((ih os).cons o |>.cons e).trans (List.perm_middle.symm.cons e)

theorem evenEntries_get (l : List Int) (i : Nat) :
    (evenEntries l)[i]? = l[2 * i]? := by
  induction i generalizing l with
  | zero =>
      cases l with
      | nil => rfl
      | cons x xs => cases xs <;> rfl
  | succ i ih =>
      have hi : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
      cases l with
      | nil => simp [evenEntries]
      | cons x xs =>
          cases xs with
          | nil => simp [evenEntries, hi]
          | cons y xs => simpa [evenEntries, hi] using ih xs

theorem oddEntries_get (l : List Int) (i : Nat) :
    (oddEntries l)[i]? = l[2 * i + 1]? := by
  induction i generalizing l with
  | zero =>
      cases l with
      | nil => rfl
      | cons x xs => cases xs <;> rfl
  | succ i ih =>
      have hi : 2 * (i + 1) + 1 = ((2 * i + 1) + 1) + 1 := by omega
      cases l with
      | nil => simp [oddEntries]
      | cons x xs =>
          cases xs with
          | nil => simp [oddEntries, hi]
          | cons y xs => simpa [oddEntries, hi] using ih xs

theorem sort_even_entries (l : List Int) :
    evenEntries (sort_even l) = (evenEntries l).mergeSort (· ≤ ·) ∧
    oddEntries (sort_even l) = oddEntries l := by
  apply weave_entries
  · simpa using (split_lengths l).2.1
  · simpa using (split_lengths l).2.2

/-! ## Semantic properties -/

def length_prop (l result : List Int) : Prop := result.length = l.length

theorem length_thm (l : List Int) : length_prop l (sort_even l) := by
  unfold length_prop sort_even
  rw [weave_length, List.length_mergeSort]
  exact (split_lengths l).1

/-- The complete odd subsequence, including order and duplicates, is unchanged. -/
def odd_prop (l result : List Int) : Prop := oddEntries result = oddEntries l

theorem odd_thm (l : List Int) : odd_prop l (sort_even l) :=
  (sort_even_entries l).2

/-- Explicit zero-based indexing form, also valid for out-of-bounds queries. -/
def odd_index_prop (l result : List Int) : Prop :=
  ∀ i : Nat, result[2 * i + 1]? = l[2 * i + 1]?

theorem odd_index_thm (l : List Int) : odd_index_prop l (sort_even l) := by
  intro i
  rw [← oddEntries_get, ← oddEntries_get, (sort_even_entries l).2]

/-- No even-position value is added or lost; multiplicities are preserved. -/
def even_perm_prop (l result : List Int) : Prop :=
  (evenEntries result).Perm (evenEntries l)

theorem even_perm_thm (l : List Int) : even_perm_prop l (sort_even l) := by
  unfold even_perm_prop
  rw [(sort_even_entries l).1]
  exact List.mergeSort_perm _ _

/-- Even-position values are nondecreasing, not necessarily strictly increasing. -/
def even_sorted_prop (_l result : List Int) : Prop :=
  List.Sorted (· ≤ ·) (evenEntries result)

theorem even_sorted_thm (l : List Int) : even_sorted_prop l (sort_even l) := by
  unfold even_sorted_prop
  rw [(sort_even_entries l).1]
  exact List.sorted_mergeSort' (· ≤ ·) _

def permutation_prop (l result : List Int) : Prop := result.Perm l

theorem permutation_thm (l : List Int) : permutation_prop l (sort_even l) := by
  unfold permutation_prop sort_even
  have hp := (weave_perm ((evenEntries l).mergeSort (· ≤ ·)) (oddEntries l)).trans
    ((List.mergeSort_perm (evenEntries l) (· ≤ ·)).append_right (oddEntries l))
  have hq : (evenEntries l ++ oddEntries l).Perm l := by
    simpa only [weave_split] using (weave_perm (evenEntries l) (oddEntries l)).symm
  exact hp.trans hq

/-- Sorting an already sorted even subsequence leaves every entry unchanged. -/
theorem sorted_fixed (l : List Int) (h : List.Sorted (· ≤ ·) (evenEntries l)) :
    sort_even l = l := by
  unfold sort_even
  rw [List.mergeSort_eq_self (· ≤ ·) h, weave_split]

def idempotent_prop (_l result : List Int) : Prop := sort_even result = result

theorem idempotent_thm (l : List Int) : idempotent_prop l (sort_even l) :=
  sorted_fixed _ (even_sorted_thm l)

/-- Together these properties characterize the Python result. -/
def Post_prop (l result : List Int) : Prop :=
  length_prop l result ∧ odd_prop l result ∧ odd_index_prop l result ∧
  even_perm_prop l result ∧ even_sorted_prop l result ∧
  permutation_prop l result ∧ idempotent_prop l result

/-! ## Property-based tests

`smallInputs 5` enumerates all 3906 lists of length at most five whose
entries belong to {-2, -1, 0, 1, 2}. This covers negatives, duplicates,
empty lists, and both parities of length. Each property has its own check.
The unbounded odd-index proposition has a finite executable counterpart:
beyond the maximum list length both optional lookups are `none`.
-/

def smallInputs : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => [] :: ([-2, -1, 0, 1, 2] : List Int).flatMap
      (fun x => (smallInputs n).map (x :: ·))

def lengthCheck (l : List Int) : Bool := (sort_even l).length == l.length

def oddCheck (l : List Int) : Bool := oddEntries (sort_even l) == oddEntries l

def oddIndexCheck (l : List Int) : Bool :=
  let result := sort_even l
  (List.range (max result.length l.length + 1)).all
    (fun i => result[2 * i + 1]? == l[2 * i + 1]?)

def evenPermCheck (l : List Int) : Bool :=
  decide ((evenEntries (sort_even l)).Perm (evenEntries l))

def evenSortedCheck (l : List Int) : Bool :=
  decide (List.Sorted (· ≤ ·) (evenEntries (sort_even l)))

def permutationCheck (l : List Int) : Bool := decide ((sort_even l).Perm l)

def idempotentCheck (l : List Int) : Bool := sort_even (sort_even l) == sort_even l

/-- Executable conjunction corresponding to `Post_prop` on the implementation. -/
def postCheck (l : List Int) : Bool :=
  lengthCheck l && oddCheck l && oddIndexCheck l && evenPermCheck l &&
  evenSortedCheck l && permutationCheck l && idempotentCheck l

-- PBT for length_prop.
example : (smallInputs 5).all lengthCheck = true := by native_decide
-- PBT for odd_prop.
example : (smallInputs 5).all oddCheck = true := by native_decide
-- PBT for odd_index_prop.
example : (smallInputs 5).all oddIndexCheck = true := by native_decide
-- PBT for even_perm_prop (including multiplicities).
example : (smallInputs 5).all evenPermCheck = true := by native_decide
-- PBT for even_sorted_prop.
example : (smallInputs 5).all evenSortedCheck = true := by native_decide
-- PBT for permutation_prop.
example : (smallInputs 5).all permutationCheck = true := by native_decide
-- PBT for idempotent_prop.
example : (smallInputs 5).all idempotentCheck = true := by native_decide
-- PBT for the already-sorted fixed-point theorem.
example : (smallInputs 5).all (fun l =>
    !(decide (List.Sorted (· ≤ ·) (evenEntries l))) || (sort_even l == l)) = true :=
  by native_decide
-- PBT for Post_prop.
example : (smallInputs 5).all postCheck = true := by native_decide
#eval (smallInputs 5).length
#eval (smallInputs 5).all postCheck
-- Randomized PBT for the entire postcondition on unrestricted integer lists.
#eval Plausible.Testable.check (∀ l : List Int, postCheck l = true)

/-! ## Correctness -/

/-- Total correctness for every input admitted by Python's integer-list domain. -/
theorem Post_thm (l : List Int) : Pre l → Post_prop l (sort_even l) := by
  intro _
  exact ⟨length_thm l, odd_thm l, odd_index_thm l, even_perm_thm l,
    even_sorted_thm l, permutation_thm l, idempotent_thm l⟩

/-- The postcondition determines a unique output, not just necessary conditions. -/
theorem post_unique (l result : List Int) (h : Post_prop l result) :
    result = sort_even l := by
  rcases h with ⟨_, ho, _, hp, hs, _, _⟩
  have he : evenEntries result = evenEntries (sort_even l) :=
    List.eq_of_perm_of_sorted (hp.trans (even_perm_thm l).symm) hs (even_sorted_thm l)
  calc
    result = weave (evenEntries result) (oddEntries result) := (weave_split result).symm
    _ = weave (evenEntries (sort_even l)) (oddEntries (sort_even l)) := by
      rw [he, show oddEntries result = oddEntries (sort_even l) from
        ho.trans (odd_thm l).symm]
    _ = sort_even l := weave_split _

/-! ## Imperative implementation

The slices are implemented by the same index-extraction functions. The local
`evens` variable is then sorted, the zip loop extends a mutable answer, and an
unpaired final even entry is appended exactly as in the Python source.
-/

/-- The accumulator loop, exposed separately for its loop invariant. -/
def extendPairs (ps : List (Int × Int)) (initial : List Int) : List Int := Id.run do
  let mut ans := initial
  for (e, o) in ps do
    ans := ans ++ [e, o]
  return ans

/-- Direct mutable-state translation of the Python program. -/
def sort_even_imperative (l : List Int) : List Int := Id.run do
  let mut evens := evenEntries l
  let odds := oddEntries l
  evens := evens.mergeSort (· ≤ ·)
  let mut ans := []
  for (e, o) in evens.zip odds do
    ans := ans ++ [e, o]
  if evens.length > odds.length then
    ans := ans ++ [evens.getLast!]
  return ans

/-! ## Imperative tests -/

example : sort_even_imperative [1, 2, 3] = [1, 2, 3] := by native_decide
example : sort_even_imperative [5, 6, 3, 4] = [3, 6, 5, 4] := by native_decide
example : sort_even_imperative [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] =
    [-10, 3, -5, 2, -3, 3, 5, 0, 9, 1, 123] := by native_decide
example : sort_even_imperative [5, 8, -12, 4, 23, 2, 3, 11, 12, -10] =
    [-12, 8, 3, 4, 5, 2, 12, 11, 23, -10] := by native_decide
example : sort_even_imperative [] = [] := by native_decide
example : sort_even_imperative [-7] = [-7] := by native_decide
example : sort_even_imperative [2, 99, 2, 88, -1, 77] =
    [-1, 99, 2, 88, 2, 77] := by native_decide
#eval sort_even_imperative [5, 6, 3, 4]
#eval sort_even_imperative [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
example : (smallInputs 5).all (fun l => sort_even l == sort_even_imperative l) = true :=
  by native_decide

/-! ## Loop invariant and equivalence proof -/

/-- Processing pairs appends their flattened values to the previous answer. -/
theorem extendPairs_eq (ps : List (Int × Int)) (initial : List Int) :
    extendPairs ps initial = initial ++ ps.flatMap (fun p => [p.1, p.2]) := by
  induction ps generalizing initial with
  | nil => simp [extendPairs]
  | cons p ps ih =>
      rcases p with ⟨e, o⟩
      have step : extendPairs ((e, o) :: ps) initial =
          extendPairs ps (initial ++ [e, o]) := by
        simp [extendPairs]
      rw [step, ih]
      simp [List.append_assoc]

/-- Zipping consumes all odds; the only possible remainder comes from evens. -/
theorem weave_zip_drop (es os : List Int) (h : os.length ≤ es.length) :
    weave es os = (es.zip os).flatMap (fun p => [p.1, p.2]) ++ es.drop os.length := by
  induction es generalizing os with
  | nil =>
      have ho : os = [] := List.length_eq_zero_iff.mp (by simpa using h)
      subst os
      rfl
  | cons e es ih =>
      cases os with
      | nil => simp [weave]
      | cons o os =>
          have h' : os.length ≤ es.length := by simpa using h
          simp [weave, ih os h']

/-- The Python-style last-element access is safe on a nonempty list. -/
theorem last_of_nonempty (xs : List Int) (h : xs ≠ []) :
    xs.getLast! = xs.getLast h := by
  cases xs with
  | nil => contradiction
  | cons x xs => rfl

/-- Kernel-checked equivalence, including both parities and the empty input. -/
theorem functional_eq_imperative (l : List Int) :
    sort_even l = sort_even_imperative l := by
  symm
  let es := (evenEntries l).mergeSort (· ≤ ·)
  let os := oddEntries l
  change (if es.length > os.length then
      extendPairs (es.zip os) [] ++ [es.getLast!]
    else extendPairs (es.zip os) []) = weave es os
  have hlo : os.length ≤ es.length := by
    simpa [es, os] using (split_lengths l).2.1
  have hhi : es.length ≤ os.length + 1 := by
    simpa [es, os] using (split_lengths l).2.2
  rw [extendPairs_eq]
  simp only [List.nil_append]
  rw [weave_zip_drop es os hlo]
  split
  · rename_i h
    have hne : es ≠ [] := by
      intro he
      simp [he] at h
    have hn : os.length = es.length - 1 := by omega
    rw [hn, List.drop_length_sub_one hne]
    rw [last_of_nonempty es hne]
  · rename_i h
    have hd : es.drop os.length = [] := List.drop_eq_nil_of_le (by omega)
    simp [hd]

/-- The imperative program satisfies the very same complete specification. -/
theorem imperative_correctness (l : List Int) : Pre l → Post_prop l (sort_even_imperative l) := by
  rw [← functional_eq_imperative]
  exact Post_thm l

end humaneval_37_sort_even
end Agent
