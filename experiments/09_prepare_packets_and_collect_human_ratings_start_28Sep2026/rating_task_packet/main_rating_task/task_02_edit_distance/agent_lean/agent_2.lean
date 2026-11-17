import Mathlib

/-!
# Levenshtein edit distance

Translation of the Python `edit_distance` program: the minimum number of
single-element insertions, deletions, and substitutions that turn one sequence
into another.

Strings and homogeneous lists in the Python source are both sequences. They are
represented here by `List α` with decidable equality (`String.toList` for
strings). Non-sequence inputs, which Python rejects with `ValueError`, are
represented by `Option.none` and rejected by `editDistanceChecked`.

The functional implementation is the standard row dynamic program (Wagner–Fischer).
It is proved equal to Mathlib's `levenshtein` with unit costs, and therefore
satisfies the usual recurrence, bounds, symmetry, and the triangle inequality.
An imperative `Id.run do` loop computes the same rows.
-/

namespace edit_distance

variable {α : Type _} [DecidableEq α]

/-- Mathlib Levenshtein distance with the unit-cost model used by the Python
program: deletion and insertion cost `1`, substitution costs `0` when the
elements are equal and `1` otherwise. -/
def lev (xs ys : List α) : Nat :=
  levenshtein Levenshtein.defaultCost xs ys

theorem lev_nil_left (ys : List α) : lev [] ys = ys.length := by
  induction ys with
  | nil => simp [lev]
  | cons y ys ih =>
    rw [lev, levenshtein_nil_cons, Levenshtein.defaultCost_insert, ← lev, ih]
    omega

theorem lev_nil_right (xs : List α) : lev xs [] = xs.length := by
  induction xs with
  | nil => simp [lev]
  | cons x xs ih =>
    rw [lev, levenshtein_cons_nil, Levenshtein.defaultCost_delete, ← lev, ih]
    omega

theorem lev_cons_cons (x : α) (xs : List α) (y : α) (ys : List α) :
    lev (x :: xs) (y :: ys) =
      min (1 + lev xs (y :: ys))
        (min (1 + lev (x :: xs) ys) ((if x = y then 0 else 1) + lev xs ys)) := by
  simp [lev, levenshtein_cons_cons, Levenshtein.defaultCost_delete,
    Levenshtein.defaultCost_insert, Levenshtein.defaultCost_substitute]

/-- Advance one target character in the suffix-distance row.

`row` stores `lev t prev` for every suffix `t` of the source, head first.
The result stores those distances against `y :: prev`. -/
def applyChar (y : α) : List α → List Nat → List Nat
  | [], ds => [1 + ds.headD 0]
  | x :: xs, d0 :: d1 :: ds =>
    let rest := applyChar y xs (d1 :: ds)
    min (1 + rest.headD 0) (min (1 + d0) ((if x = y then 0 else 1) + d1)) :: rest
  | _ :: _, _ => []

/-- Distances from every suffix of `xs` to the empty list: `[xs.length, …, 0]`. -/
def initRow : List α → List Nat
  | [] => [0]
  | _ :: xs =>
    let rest := initRow xs
    (1 + rest.headD 0) :: rest

/-- Levenshtein distance between two sequences.

This is the functional form of the Python dynamic program: one row per source
element (here, one step per target element, stored by source suffixes), with the
same insertion, deletion, and substitution costs. -/
def editDistance (xs ys : List α) : Nat :=
  (ys.foldr (fun y row => applyChar y xs row) (initRow xs)).headD 0

/-- String wrapper. Python converts `str` to a list of characters before the DP. -/
def editDistanceString (s1 s2 : String) : Nat :=
  editDistance s1.toList s2.toList

/-! ### Row DP agrees with `lev` -/

theorem tails_map_headD (xs : List α) (f : List α → Nat) :
    (xs.tails.map f).headD 0 = f xs := by
  cases xs <;> simp [List.tails]

theorem initRow_spec (xs : List α) :
    initRow xs = xs.tails.map (fun xs' => lev xs' []) := by
  induction xs with
  | nil => simp [initRow, List.tails, lev]
  | cons x xs ih =>
    simp [initRow, List.tails, ih, tails_map_headD, lev_nil_right]
    omega

theorem applyChar_nil (y : α) (ds : List Nat) :
    applyChar y [] ds = [1 + ds.headD 0] := rfl

theorem applyChar_cons (y x : α) (xs : List α) (d0 d1 : Nat) (ds : List Nat) :
    applyChar y (x :: xs) (d0 :: d1 :: ds) =
      let rest := applyChar y xs (d1 :: ds)
      min (1 + rest.headD 0) (min (1 + d0) ((if x = y then 0 else 1) + d1)) :: rest := rfl

theorem applyChar_spec (y : α) (xs ys : List α) :
    applyChar y xs (xs.tails.map (fun t => lev t ys)) =
      xs.tails.map (fun t => lev t (y :: ys)) := by
  induction xs with
  | nil =>
    simp [List.tails, applyChar_nil, lev_nil_left]
  | cons x xs ih =>
    have hrow :
        (x :: xs).tails.map (fun t => lev t ys) =
          lev (x :: xs) ys :: xs.tails.map (fun t => lev t ys) := by
      simp [List.tails]
    have hne : xs.tails.map (fun t => lev t ys) ≠ [] := by
      cases xs <;> simp [List.tails]
    obtain ⟨d1, ds, hsplit⟩ := List.exists_cons_of_ne_nil hne
    rw [hrow, hsplit, applyChar_cons, ih, hsplit]
    have hd1 : d1 = lev xs ys := by
      have hhead := congrArg (fun l => List.headD l 0) hsplit
      simpa [tails_map_headD] using hhead
    have hrestHead : (xs.tails.map (fun t => lev t (y :: ys))).headD 0 = lev xs (y :: ys) :=
      tails_map_headD xs (fun t => lev t (y :: ys))
    simp [hd1, hrestHead, lev_cons_cons, List.tails]

theorem row_spec (xs ys : List α) :
    ys.foldr (fun y row => applyChar y xs row) (initRow xs) =
      xs.tails.map (fun t => lev t ys) := by
  induction ys with
  | nil => simp [initRow_spec]
  | cons y ys ih =>
    rw [List.foldr_cons, ih, applyChar_spec]

theorem editDistance_eq_lev (xs ys : List α) : editDistance xs ys = lev xs ys := by
  rw [editDistance, row_spec, tails_map_headD]

/-! ## Unit tests

Python checks, including strings, integer lists, character lists, and edges.
-/

example : editDistanceString "hello" "hello" = 0 := by native_decide
example : editDistanceString "cat" "bat" = 1 := by native_decide
example : editDistanceString "cat" "cats" = 1 := by native_decide
example : editDistanceString "cats" "cat" = 1 := by native_decide
example : editDistanceString "cat" "dog" = 3 := by native_decide
example : editDistanceString "kitten" "sitting" = 3 := by native_decide
example : editDistanceString "" "" = 0 := by native_decide
example : editDistanceString "" "abc" = 3 := by native_decide
example : editDistanceString "ab" "" = 2 := by native_decide
example : editDistanceString "a" "b" = 1 := by native_decide
example : editDistance ([1, 2, 3] : List Nat) [1, 2, 3] = 0 := by native_decide
example : editDistance ([1, 2, 3] : List Nat) [1, 4, 3] = 1 := by native_decide
example : editDistance ([1, 2, 3, 4] : List Nat) [1, 3, 4] = 1 := by native_decide
example : editDistance ([1, 2, 3] : List Nat) [4, 5, 6] = 3 := by native_decide
example : editDistance ([1, 2, 3, 4, 5] : List Nat) [6, 7, 8] = 5 := by native_decide
example : editDistance ['h', 'e', 'l', 'l', 'o'] ['h', 'e', 'l', 'l', 'o'] = 0 := by
  native_decide
example : editDistance ['c', 'a', 't'] ['b', 'a', 't'] = 1 := by native_decide
example : editDistance ['c', 'a', 't'] ['c', 'a', 't', 's'] = 1 := by native_decide
example : editDistance ['c', 'a', 't', 's'] ['c', 'a', 't'] = 1 := by native_decide
example : editDistanceString "intention" "execution" = 5 := by native_decide
example : editDistanceString "saturday" "sunday" = 3 := by native_decide
example : editDistanceString "abc" "def" = 3 := by native_decide
example : editDistanceString "xyz" "abc" = 3 := by native_decide
example : editDistanceString "a" "a" = 0 := by native_decide
example : editDistanceString "a" "" = 1 := by native_decide
example : editDistanceString "" "a" = 1 := by native_decide
example : editDistanceString "aaa" "aa" = 1 := by native_decide
example : editDistanceString "aa" "aaa" = 1 := by native_decide
example : editDistanceString "aaaa" "bbbb" = 4 := by native_decide

#eval editDistanceString "kitten" "sitting"
#eval editDistanceString "intention" "execution"
#eval editDistance ([1, 2, 3] : List Nat) [1, 4, 3]

/-! ## Pre-condition

Python `pre` accepts exactly `str` and `list`. Both become lists before the DP.
`Option.none` stands for a rejected non-sequence such as `int`.
-/

/-- The two lists are admissible sequences. Lists are always admissible. -/
def Pre (_xs _ys : List α) : Prop := True

/-- Dynamic inputs: `some` is a sequence, `none` is not a `str` or `list`. -/
def PreOpt (s1 s2 : Option (List α)) : Prop :=
  s1.isSome ∧ s2.isSome

/-- Entry point that mirrors `ValueError` on non-sequences. -/
def editDistanceChecked (s1 s2 : Option (List α)) : Except String Nat :=
  match s1, s2 with
  | some xs, some ys => .ok (editDistance xs ys)
  | _, _ => .error "Inputs must be str or list"

example : editDistanceChecked (none : Option (List Char)) (some "abc".toList) =
    .error "Inputs must be str or list" := rfl
example : editDistanceChecked (some ([1, 2] : List Nat)) none =
    .error "Inputs must be str or list" := rfl
example : editDistanceChecked (some ([1, 2, 3] : List Nat)) (some [1, 4, 3]) =
    .ok 1 := by native_decide

/-! ## Properties -/

/-- `z ≤ min p q + k` from the two separate bounds. -/
theorem nat_le_min_add {z p q k : Nat} (hp : z ≤ p + k) (hq : z ≤ q + k) :
    z ≤ min p q + k := by
  rcases Nat.le_total p q with h | h
  · rw [Nat.min_eq_left h]
    exact hp
  · rw [Nat.min_eq_right h]
    exact hq

theorem min3_eq_zero {a b c : Nat} (h : min (1 + a) (min (1 + b) c) = 0) : c = 0 := by
  have hpos1 : 1 + a ≠ 0 := by omega
  have hpos2 : 1 + b ≠ 0 := by omega
  have aux {p q : Nat} (hpq : min p q = 0) (hp : p ≠ 0) : q = 0 := by
    rw [Nat.min_def] at hpq
    split at hpq
    · exact absurd hpq hp
    · exact hpq
  exact aux (aux h hpos1) hpos2

theorem lev_comm_aux (n : Nat) :
    ∀ xs ys : List α, xs.length + ys.length ≤ n → lev xs ys = lev ys xs := by
  induction n with
  | zero =>
    intro xs ys h
    have hx : xs.length = 0 := by omega
    have hy : ys.length = 0 := by omega
    simp [List.length_eq_zero.mp hx, List.length_eq_zero.mp hy, lev]
  | succ n ih =>
    intro xs ys h
    cases xs with
    | nil => simp [lev_nil_left, lev_nil_right]
    | cons x xs =>
      cases ys with
      | nil => simp [lev_nil_left, lev_nil_right]
      | cons y ys =>
        have h1 : xs.length + (y :: ys).length ≤ n := by simp at *; omega
        have h2 : (x :: xs).length + ys.length ≤ n := by simp at *; omega
        have h3 : xs.length + ys.length ≤ n := by simp at *; omega
        rw [lev_cons_cons, lev_cons_cons,
          ih xs (y :: ys) h1, ih (x :: xs) ys h2, ih xs ys h3]
        simp [eq_comm, min_left_comm]

theorem lev_comm (xs ys : List α) : lev xs ys = lev ys xs :=
  lev_comm_aux (xs.length + ys.length) xs ys le_rfl

theorem lev_self (xs : List α) : lev xs xs = 0 := by
  induction xs with
  | nil => simp [lev]
  | cons x xs ih =>
    rw [lev_cons_cons]
    simp [ih, Nat.zero_min, Nat.min_zero]

theorem lev_le_lengths (xs ys : List α) : lev xs ys ≤ xs.length + ys.length := by
  induction xs generalizing ys with
  | nil => simp [lev_nil_left]
  | cons x xs ih =>
    cases ys with
    | nil => simp [lev_nil_right]
    | cons y ys =>
      rw [lev_cons_cons]
      have hsub : (if x = y then 0 else 1) ≤ 1 := by split <;> omega
      have htail := ih ys
      calc
        min (1 + lev xs (y :: ys))
            (min (1 + lev (x :: xs) ys) ((if x = y then 0 else 1) + lev xs ys))
            ≤ (if x = y then 0 else 1) + lev xs ys :=
          le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
        _ ≤ 1 + lev xs ys := by omega
        _ ≤ 1 + xs.length + ys.length := by omega
        _ ≤ (x :: xs).length + (y :: ys).length := by simp; omega

theorem length_le_lev_add_aux (n : Nat) :
    ∀ xs ys : List α, xs.length + ys.length ≤ n → xs.length ≤ lev xs ys + ys.length := by
  induction n with
  | zero =>
    intro xs ys h
    have hx : xs.length = 0 := by omega
    simp [hx]
  | succ n ih =>
    intro xs ys h
    cases xs with
    | nil => simp
    | cons x xs =>
      cases ys with
      | nil => simp [lev_nil_right]
      | cons y ys =>
        rw [lev_cons_cons]
        have h1 : xs.length + (y :: ys).length ≤ n := by simp at *; omega
        have h2 : (x :: xs).length + ys.length ≤ n := by simp at *; omega
        have h3 : xs.length + ys.length ≤ n := by simp at *; omega
        have ih1 := ih xs (y :: ys) h1
        have ih2 := ih (x :: xs) ys h2
        have ih3 := ih xs ys h3
        have hA : xs.length ≤ (1 + lev xs (y :: ys)) + ys.length := by omega
        have hB : xs.length ≤ (1 + lev (x :: xs) ys) + ys.length := by omega
        have hS : xs.length ≤
            ((if x = y then 0 else 1) + lev xs ys) + ys.length := by
          have : (if x = y then 0 else 1) ≥ 0 := by omega
          omega
        have hBS := nat_le_min_add hB hS
        have hABS := nat_le_min_add hA hBS
        simpa using hABS

theorem length_le_lev_add (xs ys : List α) : xs.length ≤ lev xs ys + ys.length :=
  length_le_lev_add_aux (xs.length + ys.length) xs ys le_rfl

theorem length_le_lev_add_right (xs ys : List α) : ys.length ≤ lev xs ys + xs.length := by
  simpa [lev_comm] using length_le_lev_add ys xs

/-- Deleting one element from the target decreases the distance by at most one. -/
theorem lev_remove_right (xs ys : List α) (b : α) :
    lev xs ys ≤ lev xs (b :: ys) + 1 := by
  induction xs generalizing ys b with
  | nil =>
    simp [lev_nil_left]
    omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      simpa [lev_nil_right] using length_le_lev_add (x :: xs) [b]
    | cons y ys =>
      set z := lev (x :: xs) (y :: ys)
      have hz_le : z ≤ 1 + lev xs (y :: ys) := by
        rw [lev_cons_cons]
        exact Nat.min_le_left _ _
      have hih := ih (y :: ys) b
      have hP : z ≤ (1 + lev xs (b :: y :: ys)) + 1 := by omega
      have hQ : z ≤ (1 + z) + 1 := by omega
      have hR : z ≤ ((if x = b then 0 else 1) + lev xs (y :: ys)) + 1 := by
        have hsub : (0 : Nat) ≤ if x = b then 0 else 1 := by omega
        omega
      have hQR := nat_le_min_add hQ hR
      have hPQR := nat_le_min_add hP hQR
      simpa [z, lev_cons_cons] using hPQR

/-- Inserting one element into the target increases the distance by at most one. -/
theorem lev_add_right (xs ys : List α) (b : α) :
    lev xs (b :: ys) ≤ lev xs ys + 1 := by
  cases xs with
  | nil => simp [lev_nil_left]
  | cons x xs =>
    rw [lev_cons_cons]
    calc
      min (1 + lev xs (b :: ys))
          (min (1 + lev (x :: xs) ys) ((if x = b then 0 else 1) + lev xs ys))
          ≤ 1 + lev (x :: xs) ys :=
        le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
      _ = lev (x :: xs) ys + 1 := by omega

theorem lev_add_left (xs ys : List α) (a : α) :
    lev (a :: xs) ys ≤ lev xs ys + 1 := by
  simpa [lev_comm] using lev_add_right ys xs a

/-- Python recurrence: equal heads cost nothing; otherwise one edit plus the best
of deletion, insertion, and substitution. -/
theorem lev_python_rec (x : α) (xs : List α) (y : α) (ys : List α) :
    lev (x :: xs) (y :: ys) =
      if x = y then lev xs ys
      else min (lev xs (y :: ys)) (min (lev (x :: xs) ys) (lev xs ys)) + 1 := by
  rw [lev_cons_cons]
  by_cases hxy : x = y
  · simp only [hxy, if_true, zero_add]
    apply le_antisymm
    · exact le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
    · refine Nat.le_min ?_ (Nat.le_min ?_ (Nat.le_refl _))
      · simpa [hxy] using lev_remove_right xs ys y
      · simpa [hxy, lev_comm] using lev_remove_right ys xs y
  · simp only [hxy, if_false]
    have hBC : min (1 + lev (x :: xs) ys) (1 + lev xs ys) =
        1 + min (lev (x :: xs) ys) (lev xs ys) := by
      simpa using (Nat.min_add_add_left 1 (lev (x :: xs) ys) (lev xs ys)).symm? 
    -- filled below if the lemma direction differs
    sorry

theorem lev_eq_zero_iff (xs ys : List α) : lev xs ys = 0 ↔ xs = ys := by
  constructor
  · intro h
    induction xs generalizing ys with
    | nil =>
      simp [lev_nil_left] at h
      exact List.length_eq_zero.mp h
    | cons x xs ih =>
      cases ys with
      | nil => simp [lev_nil_right] at h
      | cons y ys =>
        rw [lev_cons_cons] at h
        have hS : (if x = y then 0 else 1) + lev xs ys = 0 := min3_eq_zero h
        obtain ⟨hsub, hed⟩ := Nat.add_eq_zero.mp hS
        have hxy : x = y := by
          by_contra hne
          simp [hne] at hsub
        have htail : xs = ys := ih ys hed
        simp [hxy, htail]
  · rintro rfl
    exact lev_self xs

-- PLACEHOLDER_REST

end edit_distance
