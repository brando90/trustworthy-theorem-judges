import Mathlib
import Mathlib.Data.List.EditDistance.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Batteries.Data.List.Basic
import Plausible

/-!
# Levenshtein edit distance

Translation of a Python Levenshtein (edit) distance routine.
The distance is the minimum number of single-element insertions, deletions
and substitutions needed to transform one sequence into another.

Strings are represented as `List Char` via `String.toList`, and arbitrary
sequences as `List α` with decidable equality — the same uniform model the
Python code uses after converting `str` to a list. Inputs that are neither
strings nor lists are rejected by `editDistanceChecked`, matching `ValueError`.

The executable implementation is the classic Wagner–Fischer dynamic program.
It is proved equal to Mathlib's unit-cost `Levenshtein.levenshtein`, which
satisfies the recurrence implemented by the Python nested loops. When the two
symbols are equal, Python copies the diagonal cell; that agrees with the
min-of-three recurrence (see `python_cell_eq`).
-/

namespace edit_distance

open Levenshtein

variable {α : Type} [DecidableEq α]

/-- Substitution cost: `0` if the symbols agree, otherwise `1`. -/
def substCost (x y : α) : Nat :=
  if x = y then 0 else 1

/-- Unit-cost Levenshtein distance as specified by Mathlib's recurrence. -/
def lev (xs ys : List α) : Nat :=
  levenshtein defaultCost xs ys

@[simp] theorem lev_nil_nil : lev ([] : List α) [] = 0 := by
  simp [lev]

@[simp] theorem lev_nil_cons (y : α) (ys : List α) :
    lev [] (y :: ys) = lev [] ys + 1 := by
  simp [lev, levenshtein_nil_cons, defaultCost_insert, Nat.add_comm]

@[simp] theorem lev_cons_nil (x : α) (xs : List α) :
    lev (x :: xs) [] = lev xs [] + 1 := by
  simp [lev, levenshtein_cons_nil, defaultCost_delete, Nat.add_comm]

@[simp] theorem lev_cons_cons (x : α) (xs : List α) (y : α) (ys : List α) :
    lev (x :: xs) (y :: ys) =
      min (lev xs (y :: ys) + 1)
        (min (lev (x :: xs) ys + 1) (lev xs ys + substCost x y)) := by
  simp [lev, levenshtein_cons_cons, defaultCost_delete, defaultCost_insert,
    defaultCost_substitute, substCost, Nat.add_comm]

theorem lev_nil_left (ys : List α) : lev [] ys = ys.length := by
  induction ys with
  | nil => simp
  | cons y ys ih => simp [ih]

theorem lev_nil_right (xs : List α) : lev xs [] = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem substCost_comm (x y : α) : substCost x y = substCost y x := by
  simp [substCost, eq_comm]

theorem substCost_le_one (x y : α) : substCost x y ≤ 1 := by
  unfold substCost
  split <;> decide

theorem substCost_eq_zero_iff (x y : α) : substCost x y = 0 ↔ x = y := by
  unfold substCost
  split <;> simp [*]

theorem lev_insert_le (xs : List α) (y : α) (ys : List α) :
    lev xs (y :: ys) ≤ lev xs ys + 1 := by
  cases xs with
  | nil => simp [lev_nil_left]
  | cons x xs =>
    simp only [lev_cons_cons]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)

theorem lev_delete_le (x : α) (xs ys : List α) :
    lev (x :: xs) ys ≤ lev xs ys + 1 := by
  cases ys with
  | nil => simp [lev_nil_right]
  | cons y ys =>
    simp only [lev_cons_cons]
    exact Nat.min_le_left _ _

theorem lev_subst_le (x : α) (xs : List α) (y : α) (ys : List α) :
    lev (x :: xs) (y :: ys) ≤ lev xs ys + substCost x y := by
  simp only [lev_cons_cons]
  exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)

theorem min3_eq (a b c : Nat) :
    min a (min b c) = a ∨ min a (min b c) = b ∨ min a (min b c) = c := by
  rcases Nat.le_total b c with hbc | hbc
  · rw [Nat.min_eq_left hbc]
    rcases Nat.le_total a b with hab | hab
    · exact Or.inl (Nat.min_eq_left hab)
    · exact Or.inr (Or.inl (Nat.min_eq_right hab))
  · rw [Nat.min_eq_right hbc]
    rcases Nat.le_total a c with hac | hac
    · exact Or.inl (Nat.min_eq_left hac)
    · exact Or.inr (Or.inr (Nat.min_eq_right hac))


/-- A concrete edit script turning `xs` into `ys` by front insertions,
deletions, substitutions and keeps. `cost` counts non-keep edits. -/
inductive EW : List α → List α → Type where
  | nil : EW [] []
  | del {x xs ys} : EW xs ys → EW (x :: xs) ys
  | ins {y xs ys} : EW xs ys → EW xs (y :: ys)
  | sub {x y xs ys} : x ≠ y → EW xs ys → EW (x :: xs) (y :: ys)
  | keep {x xs ys} : EW xs ys → EW (x :: xs) (x :: ys)

namespace EW

def cost : {xs ys : List α} → EW xs ys → Nat
  | _, _, .nil => 0
  | _, _, .del h => h.cost + 1
  | _, _, .ins h => h.cost + 1
  | _, _, .sub _ h => h.cost + 1
  | _, _, .keep h => h.cost

def size : {xs ys : List α} → EW xs ys → Nat
  | _, _, .nil => 0
  | _, _, .del h => h.size + 1
  | _, _, .ins h => h.size + 1
  | _, _, .sub _ h => h.size + 1
  | _, _, .keep h => h.size + 1

def castTarget {xs ys zs : List α} (h : ys = zs) (w : EW xs ys) : EW xs zs :=
  h ▸ w

theorem castTarget_cost {xs ys zs : List α} (h : ys = zs) (w : EW xs ys) :
    (castTarget h w).cost = w.cost := by
  subst h
  rfl

mutual
def compose {xs ys zs : List α} (h1 : EW xs ys) (h2 : EW ys zs) : EW xs zs :=
  match h1 with
  | .nil => h2
  | .del h1 => .del (compose h1 h2)
  | .ins h1 => composeIns h1 h2
  | .keep h1 => composeKeep h1 h2
  | .sub hne h1 => composeSub hne h1 h2

def composeIns {xs ys zs : List α} {y : α} (h1 : EW xs ys) (h2 : EW (y :: ys) zs) : EW xs zs :=
  match h2 with
  | .del h2 => compose h1 h2
  | .ins h2 => .ins (composeIns h1 h2)
  | .sub _ h2 => .ins (compose h1 h2)
  | .keep h2 => .ins (compose h1 h2)

def composeKeep {xs ys zs : List α} {x : α} (h1 : EW xs ys) (h2 : EW (x :: ys) zs) :
    EW (x :: xs) zs :=
  match h2 with
  | .del h2 => .del (compose h1 h2)
  | .ins h2 => .ins (composeKeep h1 h2)
  | .sub hne h2 => .sub hne (compose h1 h2)
  | .keep h2 => .keep (compose h1 h2)

def composeSub {xs ys zs : List α} {x y : α} (hne : x ≠ y) (h1 : EW xs ys)
    (h2 : EW (y :: ys) zs) : EW (x :: xs) zs :=
  match h2 with
  | .del h2 => .del (compose h1 h2)
  | .ins h2 => .ins (composeSub hne h1 h2)
  | .sub _ h2 => .ins (.del (compose h1 h2))
  | .keep h2 => .sub hne (compose h1 h2)
end

theorem composeIns_cost_le {xs ys zs : List α} {y : α}
    (h1 : EW xs ys) (h2 : EW (y :: ys) zs)
    (ih : ∀ {zs : List α} (h2 : EW ys zs), (compose h1 h2).cost ≤ h1.cost + h2.cost) :
    (composeIns h1 h2).cost ≤ h1.cost + 1 + h2.cost := by
  match h2 with
  | .del h2 =>
    simp [composeIns, cost]
    have := ih h2
    omega
  | .ins h2 =>
    simp [composeIns, cost]
    have := composeIns_cost_le h1 h2 ih
    omega
  | .sub _ h2 =>
    simp [composeIns, cost]
    have := ih h2
    omega
  | .keep h2 =>
    simp [composeIns, cost]
    have := ih h2
    omega
termination_by h2.size
decreasing_by
  simp [EW.size]

theorem composeKeep_cost_le {xs ys zs : List α} {x : α}
    (h1 : EW xs ys) (h2 : EW (x :: ys) zs)
    (ih : ∀ {zs : List α} (h2 : EW ys zs), (compose h1 h2).cost ≤ h1.cost + h2.cost) :
    (composeKeep h1 h2).cost ≤ h1.cost + h2.cost := by
  match h2 with
  | .del h2 =>
    simp [composeKeep, cost]
    have := ih h2
    omega
  | .ins h2 =>
    simp [composeKeep, cost]
    have := composeKeep_cost_le h1 h2 ih
    omega
  | .sub _ h2 =>
    simp [composeKeep, cost]
    have := ih h2
    omega
  | .keep h2 =>
    simp [composeKeep, cost]
    have := ih h2
    omega
termination_by h2.size
decreasing_by
  simp [EW.size]

theorem composeSub_cost_le {xs ys zs : List α} {x y : α} (hne : x ≠ y)
    (h1 : EW xs ys) (h2 : EW (y :: ys) zs)
    (ih : ∀ {zs : List α} (h2 : EW ys zs), (compose h1 h2).cost ≤ h1.cost + h2.cost) :
    (composeSub hne h1 h2).cost ≤ h1.cost + 1 + h2.cost := by
  match h2 with
  | .del h2 =>
    simp [composeSub, cost]
    have := ih h2
    omega
  | .ins h2 =>
    simp [composeSub, cost]
    have := composeSub_cost_le hne h1 h2 ih
    omega
  | .sub _ h2 =>
    simp [composeSub, cost]
    have := ih h2
    omega
  | .keep h2 =>
    simp [composeSub, cost]
    have := ih h2
    omega
termination_by h2.size
decreasing_by
  simp [EW.size]

theorem compose_cost_le {xs ys zs : List α} (h1 : EW xs ys) (h2 : EW ys zs) :
    (compose h1 h2).cost ≤ h1.cost + h2.cost := by
  induction h1 generalizing zs with
  | nil => simp [compose, cost]
  | del h1 ih =>
    simp [compose, cost]
    have := ih h2
    omega
  | ins h1 ih =>
    simpa [compose] using composeIns_cost_le h1 h2 ih
  | keep h1 ih =>
    simpa [compose] using composeKeep_cost_le h1 h2 ih
  | sub hne h1 ih =>
    simpa [compose] using composeSub_cost_le hne h1 h2 ih


theorem sound {xs ys : List α} (h : EW xs ys) : lev xs ys ≤ h.cost := by
  induction h with
  | nil => simp [cost]
  | del h ih =>
    rename_i x xs ys
    simp only [cost]
    exact Nat.le_trans (lev_delete_le x xs ys) (Nat.add_le_add_right ih 1)
  | ins h ih =>
    rename_i y xs ys
    simp only [cost]
    exact Nat.le_trans (lev_insert_le xs y ys) (Nat.add_le_add_right ih 1)
  | sub hne h ih =>
    rename_i x y xs ys
    simp only [cost]
    have hc : substCost x y = 1 := by simp [substCost, hne]
    have hs := lev_subst_le x xs y ys
    omega
  | keep h ih =>
    rename_i x xs ys
    simp only [cost]
    have hs := lev_subst_le x xs x ys
    simp only [substCost, Nat.add_zero] at hs
    exact Nat.le_trans hs ih

def ofSame : (xs : List α) → EW xs xs
  | [] => .nil
  | x :: xs => .keep (ofSame xs)

theorem ofSame_cost (xs : List α) : (ofSame xs).cost = 0 := by
  induction xs with
  | nil => simp [ofSame, cost]
  | cons x xs ih => simp [ofSame, cost, ih]

theorem complete (xs ys : List α) : ∃ w : EW xs ys, w.cost = lev xs ys := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => exact ⟨.nil, by simp [cost]⟩
    | cons y ys ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨.ins w, by simp [cost, hw, lev_nil_cons]⟩
  | cons x xs ih =>
    induction ys with
    | nil =>
      obtain ⟨w, hw⟩ := ih ([] : List α)
      exact ⟨.del w, by simp [cost, hw, lev_cons_nil]⟩
    | cons y ys ihy =>
      obtain ⟨wDel, hDel⟩ := ih (y :: ys)
      obtain ⟨wIns, hIns⟩ := ihy
      obtain ⟨wSub, hSub⟩ := ih ys
      have hlev := lev_cons_cons x xs y ys
      rcases min3_eq (lev xs (y :: ys) + 1) (lev (x :: xs) ys + 1)
          (lev xs ys + substCost x y) with hbr | hbr | hbr
      · refine ⟨.del wDel, ?_⟩
        simp [cost, hDel, hlev, hbr]
      · refine ⟨.ins wIns, ?_⟩
        simp [cost, hIns, hlev, hbr]
      · by_cases hxy : x = y
        · have hzero : substCost x y = 0 := by simp [substCost, hxy]
          refine ⟨castTarget (by simp [hxy]) (.keep wSub), ?_⟩
          simp only [castTarget_cost, cost, hSub]
          rw [hlev, hbr, hzero]
          omega
        · have hone : substCost x y = 1 := by simp [substCost, hxy]
          refine ⟨.sub hxy wSub, ?_⟩
          simp only [cost, hSub]
          rw [hlev, hbr, hone]

end EW

theorem lev_self (xs : List α) : lev xs xs = 0 := by
  have h := EW.sound (EW.ofSame xs)
  simpa [EW.ofSame_cost] using h

theorem lev_symm (xs ys : List α) : lev xs ys = lev ys xs := by
  induction xs generalizing ys with
  | nil => simp [lev_nil_left, lev_nil_right]
  | cons x xs ih =>
    induction ys with
    | nil => simp [lev_nil_left, lev_nil_right]
    | cons y ys ihy =>
      simp only [lev_cons_cons]
      rw [ih (y :: ys), ih ys, ihy, substCost_comm x y]
      exact Nat.min_left_comm _ _ _

theorem lev_eq_zero_iff (xs ys : List α) : lev xs ys = 0 ↔ xs = ys := by
  constructor
  · intro h
    induction xs generalizing ys with
    | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp [lev_nil_cons] at h
    | cons x xs ih =>
      cases ys with
      | nil => simp [lev_cons_nil] at h
      | cons y ys =>
        have hmin := min3_eq (lev xs (y :: ys) + 1) (lev (x :: xs) ys + 1)
          (lev xs ys + substCost x y)
        rw [lev_cons_cons] at h
        rcases hmin with hbr | hbr | hbr
        · omega
        · omega
        · have hc : lev xs ys + substCost x y = 0 := by simpa [hbr] using h
          have hlev : lev xs ys = 0 := by omega
          have hsub : substCost x y = 0 := by omega
          have hxy : x = y := (substCost_eq_zero_iff x y).mp hsub
          have htail : xs = ys := ih ys hlev
          simp [hxy, htail]
  · intro h
    subst h
    exact lev_self xs

theorem lev_le_length_add (xs ys : List α) : lev xs ys ≤ xs.length + ys.length := by
  induction xs generalizing ys with
  | nil => simp [lev_nil_left]
  | cons x xs ih =>
    cases ys with
    | nil => simp [lev_nil_right]
    | cons y ys =>
      have h := lev_subst_le x xs y ys
      have hc := substCost_le_one x y
      have ih' := ih ys
      simp only [List.length_cons]
      omega

theorem length_le_lev_add (xs ys : List α) : xs.length ≤ lev xs ys + ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ihxs =>
    induction ys generalizing x with
    | nil => simp [lev_nil_right]
    | cons y ys ihys =>
      have ha : xs.length ≤ (lev xs (y :: ys) + 1) + ys.length := by
        have := ihxs (y :: ys)
        simp at this
        omega
      have hb : xs.length ≤ (lev (x :: xs) ys + 1) + ys.length := by
        have := ihys x
        simp at this
        omega
      have hc : xs.length ≤ (lev xs ys + substCost x y) + ys.length := by
        have := ihxs ys
        omega
      have hlev := lev_cons_cons x xs y ys
      rcases min3_eq (lev xs (y :: ys) + 1) (lev (x :: xs) ys + 1)
          (lev xs ys + substCost x y) with hbr | hbr | hbr
      · rw [hlev, hbr]; simp only [List.length_cons]; omega
      · rw [hlev, hbr]; simp only [List.length_cons]; omega
      · rw [hlev, hbr]; simp only [List.length_cons]; omega

theorem lev_le_max_length (xs ys : List α) : lev xs ys ≤ max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [lev_nil_left]
  | cons x xs ih =>
    cases ys with
    | nil => simp [lev_nil_right]
    | cons y ys =>
      have h := lev_subst_le x xs y ys
      have hc := substCost_le_one x y
      have ih' := ih ys
      have hmax : max xs.length ys.length + 1 = max (xs.length + 1) (ys.length + 1) := by
        rcases Nat.le_total xs.length ys.length with hle | hle
        · simp [Nat.max_eq_right hle, Nat.max_eq_right (Nat.succ_le_succ hle)]
        · simp [Nat.max_eq_left hle, Nat.max_eq_left (Nat.succ_le_succ hle)]
      simp only [List.length_cons]
      omega

theorem lev_triangle (xs ys zs : List α) :
    lev xs zs ≤ lev xs ys + lev ys zs := by
  obtain ⟨w1, h1⟩ := EW.complete xs ys
  obtain ⟨w2, h2⟩ := EW.complete ys zs
  have hc := EW.compose_cost_le w1 w2
  have hs := EW.sound (EW.compose w1 w2)
  omega


theorem lev_insert_back (xs : List α) (x : α) : lev xs (xs ++ [x]) = 1 := by
  induction xs with
  | nil => simp [lev_nil_left]
  | cons a xs ih =>
    simp only [List.cons_append, lev_cons_cons, substCost, ih]
    have hB : min (lev (a :: xs) (xs ++ [x]) + 1) 1 = 1 := by
      apply Nat.min_eq_right
      omega
    have hA : min (lev xs (a :: (xs ++ [x])) + 1) 1 = 1 := by
      apply Nat.min_eq_right
      omega
    simp [hB, hA, Nat.min_assoc]

theorem lev_subst_back (xs : List α) (x y : α) (hxy : x ≠ y) :
    lev (xs ++ [x]) (xs ++ [y]) = 1 := by
  induction xs with
  | nil =>
    simp [lev_cons_cons, lev_nil_left, lev_nil_right, substCost, hxy]
  | cons a xs ih =>
    simp only [List.cons_append, lev_cons_cons, substCost, ih]
    have h1 : 1 ≤ lev xs (a :: (xs ++ [y])) + 1 := by omega
    have h2 : 1 ≤ lev (a :: (xs ++ [x])) (xs ++ [y]) + 1 := by omega
    simp [Nat.min_eq_right h1, Nat.min_eq_right h2]

/-- Python's equal-symbol branch copies the diagonal. For unit costs this
equals the min-of-three cell whenever adjacent cells differ by at most 1. -/
theorem python_cell_eq (up left diag : Nat) (same : Bool)
    (hup : diag ≤ up + 1) (hleft : diag ≤ left + 1) :
    (if same then diag else 1 + min up (min left diag)) =
      min (up + 1) (min (left + 1) (diag + if same then 0 else 1)) := by
  cases same <;> simp <;> omega

/-- One DP row step, consuming source symbol `x` against target `ys`.
`ds` is parallel to `ys.tails` and stores distances from the previous source
suffix to each target suffix. -/
def extendRow (x : α) : List α → List Nat → List Nat
  | [], d :: _ => [d + 1]
  | [], [] => []
  | y :: ys, d :: rest =>
    let rest' := extendRow x ys rest
    min (d + 1) (min (rest'.headD 0 + 1) (rest.headD 0 + substCost x y)) :: rest'
  | _ :: _, [] => []

theorem extendRow_nil (x : α) (d : Nat) (rest : List Nat) :
    extendRow x [] (d :: rest) = [d + 1] := rfl

theorem extendRow_cons (x y : α) (ys : List α) (d : Nat) (rest : List Nat) :
    extendRow x (y :: ys) (d :: rest) =
      let rest' := extendRow x ys rest
      min (d + 1) (min (rest'.headD 0 + 1) (rest.headD 0 + substCost x y)) :: rest' := rfl

theorem extendRow_eq (x : α) (xs ys : List α) :
    extendRow x ys (ys.tails.map (lev xs)) = ys.tails.map (lev (x :: xs)) := by
  induction ys with
  | nil => simp [extendRow_nil, List.tails, lev_cons_nil]
  | cons y ys ih =>
    rw [List.tails, List.map_cons, extendRow_cons, ih]
    have hnew : ((ys.tails.map (lev (x :: xs))).headD 0) = lev (x :: xs) ys := by
      cases ys <;> simp [List.tails]
    have hold : ((ys.tails.map (lev xs)).headD 0) = lev xs ys := by
      cases ys <;> simp [List.tails]
    simp only [hnew, hold]
    have hmin :
        min (lev xs (y :: ys) + 1)
          (min (lev (x :: xs) ys + 1) (lev xs ys + substCost x y)) =
        lev (x :: xs) (y :: ys) := by
      simpa using (lev_cons_cons x xs y ys).symm
    simp only [hmin, List.tails, List.map_cons]

/-- Distances from every suffix of `ys` after consuming source `xs`
(right-to-left Wagner–Fischer; same values as the Python prefix table). -/
def initSuffixRow (ys : List α) : List Nat :=
  ys.tails.map List.length

def suffixRow (xs ys : List α) : List Nat :=
  xs.foldr (fun x row => extendRow x ys row) (initSuffixRow ys)

theorem suffixRow_eq (xs ys : List α) :
    suffixRow xs ys = ys.tails.map (lev xs) := by
  induction xs with
  | nil =>
    simp [suffixRow, initSuffixRow]
    induction ys with
    | nil => simp [List.tails, lev_nil_left]
    | cons y ys ih => simp [List.tails, List.map_cons, lev_nil_left, ih]
  | cons x xs ih =>
    unfold suffixRow
    rw [List.foldr_cons]
    have ih' :
        List.foldr (fun x row => extendRow x ys row) (initSuffixRow ys) xs =
          ys.tails.map (lev xs) := by
      simpa [suffixRow] using ih
    rw [ih', extendRow_eq]

/-- Levenshtein edit distance between two sequences. -/
def editDistance (s1 s2 : List α) : Nat :=
  (suffixRow s1 s2).headD 0

theorem editDistance_eq_lev (s1 s2 : List α) : editDistance s1 s2 = lev s1 s2 := by
  simp [editDistance, suffixRow_eq]
  cases s2 <;> simp [List.tails]

/-- String specialisation, matching Python `str` inputs. -/
def editDistanceString (s1 s2 : String) : Nat :=
  editDistance s1.toList s2.toList

/-- Python inputs: a homogeneous sequence, or a non-sequence that must be rejected. -/
inductive PyInput (β : Type) where
  | seq : List β → PyInput β
  | invalid : PyInput β

/-- Python `pre`: both arguments are `str` or `list`. -/
def pre {β : Type} (s1 s2 : PyInput β) : Bool :=
  match s1, s2 with
  | .seq _, .seq _ => true
  | _, _ => false

/-- Entry point that raises the Python `ValueError` on non-sequences. -/
def editDistanceChecked (s1 s2 : PyInput α) : Except String Nat :=
  match s1, s2 with
  | .seq a, .seq b => .ok (editDistance a b)
  | _, _ => .error "Inputs must be str or list"


namespace EW

def snocDel {xs ys : List α} (a : α) : EW xs ys → EW (xs ++ [a]) ys
  | .nil => by
      change EW [a] []
      exact .del .nil
  | .del w => .del (snocDel a w)
  | .ins w => .ins (snocDel a w)
  | .sub h w => .sub h (snocDel a w)
  | .keep w => .keep (snocDel a w)

def snocIns {xs ys : List α} (b : α) : EW xs ys → EW xs (ys ++ [b])
  | .nil => by
      change EW [] [b]
      exact .ins .nil
  | .del w => .del (snocIns b w)
  | .ins w => .ins (snocIns b w)
  | .sub h w => .sub h (snocIns b w)
  | .keep w => .keep (snocIns b w)

def snocKeep {xs ys : List α} (a : α) : EW xs ys → EW (xs ++ [a]) (ys ++ [a])
  | .nil => by
      change EW [a] [a]
      exact .keep .nil
  | .del w => .del (snocKeep a w)
  | .ins w => .ins (snocKeep a w)
  | .sub h w => .sub h (snocKeep a w)
  | .keep w => .keep (snocKeep a w)

def snocSub {xs ys : List α} {a b : α} (h : a ≠ b) : EW xs ys → EW (xs ++ [a]) (ys ++ [b])
  | .nil => by
      change EW [a] [b]
      exact .sub h .nil
  | .del w => .del (snocSub h w)
  | .ins w => .ins (snocSub h w)
  | .sub h' w => .sub h' (snocSub h w)
  | .keep w => .keep (snocSub h w)

theorem snocDel_cost {xs ys : List α} (a : α) (w : EW xs ys) :
    (snocDel a w).cost = w.cost + 1 := by
  induction w with
  | nil => simp [snocDel, cost]
  | del w ih => simp [snocDel, cost, ih]
  | ins w ih => simp [snocDel, cost, ih]
  | sub _ w ih => simp [snocDel, cost, ih]
  | keep w ih => simp [snocDel, cost, ih]

theorem snocIns_cost {xs ys : List α} (b : α) (w : EW xs ys) :
    (snocIns b w).cost = w.cost + 1 := by
  induction w with
  | nil => simp [snocIns, cost]
  | del w ih => simp [snocIns, cost, ih]
  | ins w ih => simp [snocIns, cost, ih]
  | sub _ w ih => simp [snocIns, cost, ih]
  | keep w ih => simp [snocIns, cost, ih]

theorem snocKeep_cost {xs ys : List α} (a : α) (w : EW xs ys) :
    (snocKeep a w).cost = w.cost := by
  induction w with
  | nil => simp [snocKeep, cost]
  | del w ih => simp [snocKeep, cost, ih]
  | ins w ih => simp [snocKeep, cost, ih]
  | sub _ w ih => simp [snocKeep, cost, ih]
  | keep w ih => simp [snocKeep, cost, ih]

theorem snocSub_cost {xs ys : List α} {a b : α} (h : a ≠ b) (w : EW xs ys) :
    (snocSub h w).cost = w.cost + 1 := by
  induction w with
  | nil => simp [snocSub, cost]
  | del w ih => simp [snocSub, cost, ih]
  | ins w ih => simp [snocSub, cost, ih]
  | sub _ w ih => simp [snocSub, cost, ih]
  | keep w ih => simp [snocSub, cost, ih]

def transport {xs ys xs' ys' : List α} (hxs : xs = xs') (hys : ys = ys') (w : EW xs ys) :
    EW xs' ys' :=
  hxs ▸ hys ▸ w

theorem transport_cost {xs ys xs' ys' : List α} (hxs : xs = xs') (hys : ys = ys') (w : EW xs ys) :
    (transport hxs hys w).cost = w.cost := by
  cases hxs
  cases hys
  rfl

def rev {xs ys : List α} : EW xs ys → EW xs.reverse ys.reverse
  | .nil => .nil
  | .del (x := x) (xs := xs) w =>
      transport (List.reverse_cons (a := x) (as := xs)).symm rfl (snocDel x w.rev)
  | .ins (y := y) (ys := ys) w =>
      transport rfl (List.reverse_cons (a := y) (as := ys)).symm (snocIns y w.rev)
  | .sub (x := x) (y := y) (xs := xs) (ys := ys) h w =>
      transport (List.reverse_cons (a := x) (as := xs)).symm (List.reverse_cons (a := y) (as := ys)).symm (snocSub h w.rev)
  | .keep (x := x) (xs := xs) (ys := ys) w =>
      transport (List.reverse_cons (a := x) (as := xs)).symm (List.reverse_cons (a := x) (as := ys)).symm (snocKeep x w.rev)

theorem rev_cost {xs ys : List α} (w : EW xs ys) : w.rev.cost = w.cost := by
  induction w with
  | nil => rfl
  | del w ih =>
      rw [rev, transport_cost, snocDel_cost, ih]
      simp [cost]
  | ins w ih =>
      rw [rev, transport_cost, snocIns_cost, ih]
      simp [cost]
  | sub _ w ih =>
      rw [rev, transport_cost, snocSub_cost, ih]
      simp [cost]
  | keep w ih =>
      rw [rev, transport_cost, snocKeep_cost, ih]
      simp [cost]

end EW

theorem lev_reverse (xs ys : List α) : lev xs ys = lev xs.reverse ys.reverse := by
  obtain ⟨w, hw⟩ := EW.complete xs ys
  have hle : lev xs.reverse ys.reverse ≤ lev xs ys := by
    have hs := EW.sound w.rev
    simpa [EW.rev_cost, hw] using hs
  obtain ⟨wr, hwr⟩ := EW.complete xs.reverse ys.reverse
  have hge : lev xs ys ≤ lev xs.reverse ys.reverse := by
    have hs := EW.sound wr.rev
    simpa [EW.rev_cost, hwr, List.reverse_reverse] using hs
  omega

namespace EW

/-- Drop the leading source symbol from an edit script, increasing cost by at most 1. -/
def dropSource {x : α} {xs ys : List α} (w : EW (x :: xs) ys) : EW xs ys :=
  match w with
  | .del w => w
  | .ins w => .ins (@dropSource x xs _ w)
  | .sub _ w => .ins w
  | .keep w => .ins w

theorem dropSource_cost {x : α} {xs ys : List α} (w : EW (x :: xs) ys) :
    (dropSource w).cost ≤ w.cost + 1 := by
  match w with
  | .del w =>
      simp [dropSource, cost]
      omega
  | .ins w =>
      have ih := dropSource_cost w
      simp [dropSource, cost] at ih
      simp [dropSource, cost]
      omega
  | .sub _ w =>
      simp [dropSource, cost]
  | .keep w =>
      simp [dropSource, cost]
termination_by w.size
decreasing_by
  simp [size]

end EW

theorem lev_le_cons_left (x : α) (xs ys : List α) :
    lev xs ys ≤ lev (x :: xs) ys + 1 := by
  obtain ⟨w, hw⟩ := EW.complete (x :: xs) ys
  have hs := EW.sound (EW.dropSource w)
  have hc := EW.dropSource_cost w
  omega

theorem lev_le_cons_right (xs : List α) (y : α) (ys : List α) :
    lev xs ys ≤ lev xs (y :: ys) + 1 := by
  have h := lev_le_cons_left y ys xs
  simpa [lev_symm] using h

private theorem min_succ_succ (a b : Nat) : min (a + 1) (b + 1) = min a b + 1 := by
  rcases Nat.le_total a b with h | h
  · simp [Nat.min_eq_left h, Nat.min_eq_left (Nat.add_le_add_right h 1)]
  · simp [Nat.min_eq_right h, Nat.min_eq_right (Nat.add_le_add_right h 1)]

theorem lev_python_branch (x : α) (xs : List α) (y : α) (ys : List α) :
    lev (x :: xs) (y :: ys) =
      if x = y then lev xs ys
      else 1 + min (lev xs (y :: ys)) (min (lev (x :: xs) ys) (lev xs ys)) := by
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have hrec := lev_cons_cons x xs x ys
    simp only [substCost, eq_self_iff_true, if_true, Nat.add_zero] at hrec
    have h1 := lev_le_cons_right xs x ys
    have h2 := lev_le_cons_left x xs ys
    rw [hrec, Nat.min_eq_right h2, Nat.min_eq_right h1]
  · have hrec := lev_cons_cons x xs y ys
    have hsub : substCost x y = 1 := by simp [substCost, hxy]
    have hmin :
        min (lev xs (y :: ys) + 1)
          (min (lev (x :: xs) ys + 1) (lev xs ys + 1)) =
          1 + min (lev xs (y :: ys)) (min (lev (x :: xs) ys) (lev xs ys)) := by
      rw [min_succ_succ (lev (x :: xs) ys) (lev xs ys)]
      rw [min_succ_succ (lev xs (y :: ys)) (min (lev (x :: xs) ys) (lev xs ys))]
      simp [Nat.add_comm]
    rw [hrec, hsub, if_neg hxy, hmin]

/-! ## Unit tests -/

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
example : editDistance (['h', 'e', 'l', 'l', 'o'] : List Char) ['h', 'e', 'l', 'l', 'o'] = 0 := by
  native_decide
example : editDistance (['c', 'a', 't'] : List Char) ['b', 'a', 't'] = 1 := by native_decide
example : editDistance (['c', 'a', 't'] : List Char) ['c', 'a', 't', 's'] = 1 := by native_decide
example : editDistance (['c', 'a', 't', 's'] : List Char) ['c', 'a', 't'] = 1 := by native_decide
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
example : editDistanceChecked (PyInput.invalid : PyInput Nat) (.seq [1, 2, 3]) =
    .error "Inputs must be str or list" := by rfl
example : editDistanceChecked (.seq ([1, 2] : List Nat)) .invalid =
    .error "Inputs must be str or list" := by rfl

#eval editDistanceString "kitten" "sitting"
#eval editDistanceString "intention" "execution"
#eval editDistance ([1, 2, 3] : List Nat) [1, 4, 3]

/-! ## Pre-condition -/

/-- Every `List` is a Python sequence, so the list API has no extra precondition.
Invalid non-sequences are rejected by `pre` / `editDistanceChecked`. -/
def Pre (_s1 _s2 : List α) : Prop := True

/-! ## Properties -/

def empty_left_prop (ys : List α) : Prop :=
  editDistance ([] : List α) ys = ys.length

theorem empty_left_thm (ys : List α) : empty_left_prop ys := by
  simp [empty_left_prop, editDistance_eq_lev, lev_nil_left]

def empty_right_prop (xs : List α) : Prop :=
  editDistance xs ([] : List α) = xs.length

theorem empty_right_thm (xs : List α) : empty_right_prop xs := by
  simp [empty_right_prop, editDistance_eq_lev, lev_nil_right]

def self_prop (xs : List α) : Prop :=
  editDistance xs xs = 0

theorem self_thm (xs : List α) : self_prop xs := by
  simpa [self_prop, editDistance_eq_lev] using lev_self xs

def symm_prop (xs ys : List α) : Prop :=
  editDistance xs ys = editDistance ys xs

theorem symm_thm (xs ys : List α) : symm_prop xs ys := by
  simpa [symm_prop, editDistance_eq_lev] using lev_symm xs ys

def zero_iff_prop (xs ys : List α) : Prop :=
  editDistance xs ys = 0 ↔ xs = ys

theorem zero_iff_thm (xs ys : List α) : zero_iff_prop xs ys := by
  simpa [zero_iff_prop, editDistance_eq_lev] using lev_eq_zero_iff xs ys

def bound_prop (xs ys : List α) : Prop :=
  editDistance xs ys ≤ xs.length + ys.length

theorem bound_thm (xs ys : List α) : bound_prop xs ys := by
  simpa [bound_prop, editDistance_eq_lev] using lev_le_length_add xs ys

def lower_bound_prop (xs ys : List α) : Prop :=
  xs.length ≤ editDistance xs ys + ys.length ∧
    ys.length ≤ editDistance xs ys + xs.length

theorem lower_bound_thm (xs ys : List α) : lower_bound_prop xs ys := by
  refine ⟨?_, ?_⟩
  · simpa [editDistance_eq_lev] using length_le_lev_add xs ys
  · simpa [editDistance_eq_lev, lev_symm] using length_le_lev_add ys xs

def max_bound_prop (xs ys : List α) : Prop :=
  editDistance xs ys ≤ max xs.length ys.length

theorem max_bound_thm (xs ys : List α) : max_bound_prop xs ys := by
  simpa [max_bound_prop, editDistance_eq_lev] using lev_le_max_length xs ys

def triangle_prop (xs ys zs : List α) : Prop :=
  editDistance xs zs ≤ editDistance xs ys + editDistance ys zs

theorem triangle_thm (xs ys zs : List α) : triangle_prop xs ys zs := by
  simpa [triangle_prop, editDistance_eq_lev] using lev_triangle xs ys zs

def recurrence_prop (x : α) (xs : List α) (y : α) (ys : List α) : Prop :=
  editDistance (x :: xs) (y :: ys) =
    min (editDistance xs (y :: ys) + 1)
      (min (editDistance (x :: xs) ys + 1)
        (editDistance xs ys + substCost x y))

theorem recurrence_thm (x : α) (xs : List α) (y : α) (ys : List α) :
    recurrence_prop x xs y ys := by
  simp [recurrence_prop, editDistance_eq_lev, lev_cons_cons]

def python_branch_prop (x : α) (xs : List α) (y : α) (ys : List α) : Prop :=
  editDistance (x :: xs) (y :: ys) =
    if x = y then editDistance xs ys
    else 1 + min (editDistance xs (y :: ys))
      (min (editDistance (x :: xs) ys) (editDistance xs ys))

theorem python_branch_thm (x : α) (xs : List α) (y : α) (ys : List α) :
    python_branch_prop x xs y ys := by
  simpa [python_branch_prop, editDistance_eq_lev] using lev_python_branch x xs y ys

def insert_one_prop (xs : List α) (x : α) : Prop :=
  editDistance xs (xs ++ [x]) = 1

theorem insert_one_thm (xs : List α) (x : α) : insert_one_prop xs x := by
  simpa [insert_one_prop, editDistance_eq_lev] using lev_insert_back xs x

def subst_one_prop (xs : List α) (x y : α) : Prop :=
  x ≠ y → editDistance (xs ++ [x]) (xs ++ [y]) = 1

theorem subst_one_thm (xs : List α) (x y : α) : subst_one_prop xs x y := by
  intro hxy
  simpa [subst_one_prop, editDistance_eq_lev] using lev_subst_back xs x y hxy

def checked_ok_prop (a b : List α) : Prop :=
  editDistanceChecked (.seq a) (.seq b) = .ok (editDistance a b)

theorem checked_ok_thm (a b : List α) : checked_ok_prop a b := by
  simp [checked_ok_prop, editDistanceChecked]

def checked_error_prop (s1 s2 : PyInput α) : Prop :=
  pre s1 s2 = false →
    editDistanceChecked s1 s2 = .error "Inputs must be str or list"

theorem checked_error_thm (s1 s2 : PyInput α) : checked_error_prop s1 s2 := by
  intro h
  cases s1 <;> cases s2
  · simp [pre] at h
  · rfl
  · rfl
  · rfl

def string_layer_prop (s1 s2 : String) : Prop :=
  editDistanceString s1 s2 = editDistance s1.toList s2.toList

theorem string_layer_thm (s1 s2 : String) : string_layer_prop s1 s2 := rfl

/-! ## Post-condition -/

def Post_prop (s1 s2 : List α) : Prop :=
  editDistance s1 s2 = lev s1 s2 ∧
    symm_prop s1 s2 ∧
    bound_prop s1 s2 ∧
    zero_iff_prop s1 s2 ∧
    lower_bound_prop s1 s2 ∧
    empty_right_prop s1 ∧
    empty_left_prop s2 ∧
    triangle_prop s1 s2 (s1 ++ s2)

/-! ## Property-based tests -/

def pbtLists : List (List Nat) :=
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 1, 2], [2, 1, 0], [1, 2, 3],
   [4, 5, 6], [1, 2, 3, 4], [1, 3, 4], [9], [7, 7], [1, 1, 1, 1]]

example : pbtLists.all (fun ys =>
    editDistance ([] : List Nat) ys = ys.length) = true := by native_decide

example : pbtLists.all (fun xs =>
    editDistance xs ([] : List Nat) = xs.length) = true := by native_decide

example : pbtLists.all (fun xs => editDistance xs xs = 0) = true := by native_decide

example : pbtLists.all (fun xs => pbtLists.all (fun ys =>
    editDistance xs ys = editDistance ys xs)) = true := by native_decide

example : pbtLists.all (fun xs => pbtLists.all (fun ys =>
    ((editDistance xs ys == 0) == (xs == ys)))) = true := by native_decide

example : pbtLists.all (fun xs => pbtLists.all (fun ys =>
    editDistance xs ys ≤ xs.length + ys.length)) = true := by native_decide

example : pbtLists.all (fun xs => pbtLists.all (fun ys =>
    xs.length ≤ editDistance xs ys + ys.length &&
      ys.length ≤ editDistance xs ys + xs.length)) = true := by native_decide

example : pbtLists.all (fun xs => pbtLists.all (fun ys =>
    editDistance xs ys ≤ max xs.length ys.length)) = true := by native_decide

example : pbtLists.all (fun xs => pbtLists.all (fun ys => pbtLists.all (fun zs =>
    editDistance xs zs ≤ editDistance xs ys + editDistance ys zs))) = true := by native_decide

example : (List.range 4).all (fun n =>
    (List.range 4).all (fun m =>
      let xs := List.replicate n (1 : Nat)
      let ys := List.replicate m (2 : Nat)
      editDistance (0 :: xs) (1 :: ys) =
        min (editDistance xs (1 :: ys) + 1)
          (min (editDistance (0 :: xs) ys + 1)
            (editDistance xs ys + substCost (0 : Nat) 1)))) = true := by native_decide

example : (List.range 4).all (fun n =>
    (List.range 4).all (fun m =>
      let xs := List.replicate n (1 : Nat)
      let ys := List.replicate m (1 : Nat)
      editDistance (1 :: xs) (1 :: ys) =
        (if (1 : Nat) = 1 then editDistance xs ys
         else 1 + min (editDistance xs (1 :: ys))
           (min (editDistance (1 :: xs) ys) (editDistance xs ys))))) = true := by native_decide

example : pbtLists.all (fun xs =>
    (List.range 4).all (fun k => editDistance xs (xs ++ [k]) = 1)) = true := by native_decide

example : pbtLists.all (fun xs =>
    editDistance (xs ++ [0]) (xs ++ [1]) = 1) = true := by native_decide

example : pbtLists.all (fun a => pbtLists.all (fun b =>
    match editDistanceChecked (.seq a) (.seq b) with
    | .ok n => n == editDistance a b
    | .error _ => false)) = true := by native_decide

example :
    ((match editDistanceChecked (PyInput.invalid : PyInput Nat) .invalid with
      | .error m => m == "Inputs must be str or list"
      | .ok _ => false) &&
    (match editDistanceChecked .invalid (.seq ([0] : List Nat)) with
      | .error m => m == "Inputs must be str or list"
      | .ok _ => false)) = true := by native_decide

example : (["", "a", "cat", "hello"] : List String).all (fun s1 =>
    (["", "a", "bat", "hello"] : List String).all (fun s2 =>
      editDistanceString s1 s2 = editDistance s1.toList s2.toList)) = true := by native_decide

example : pbtLists.all (fun s1 => pbtLists.all (fun s2 =>
    editDistance s1 s2 = lev s1 s2 &&
      editDistance s1 s2 = editDistance s2 s1 &&
      editDistance s1 s2 ≤ s1.length + s2.length &&
      ((editDistance s1 s2 == 0) == (s1 == s2)) &&
      s1.length ≤ editDistance s1 s2 + s2.length &&
      editDistance s1 [] = s1.length &&
      editDistance [] s2 = s2.length &&
      editDistance s1 (s1 ++ s2) ≤ editDistance s1 s2 + editDistance s2 (s1 ++ s2))) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ xs ys : List Nat, editDistance xs ys = editDistance ys xs)
  { numInst := 20, maxSize := 6 }

#eval Plausible.Testable.check
  (∀ xs : List Nat, editDistance xs xs = 0)
  { numInst := 20, maxSize := 8 }

#eval Plausible.Testable.check
  (∀ ys : List Nat, editDistance ([] : List Nat) ys = ys.length)
  { numInst := 20, maxSize := 8 }

#eval Plausible.Testable.check
  (∀ xs ys : List Nat, editDistance xs ys ≤ xs.length + ys.length)
  { numInst := 20, maxSize := 6 }

/-! ## Correctness -/

theorem correctness_thm (s1 s2 : List α) (_h : Pre s1 s2) : Post_prop s1 s2 := by
  refine ⟨editDistance_eq_lev s1 s2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact symm_thm s1 s2
  · exact bound_thm s1 s2
  · exact zero_iff_thm s1 s2
  · exact lower_bound_thm s1 s2
  · exact empty_right_thm s1
  · exact empty_left_thm s2
  · exact triangle_thm s1 s2 (s1 ++ s2)

/-! ## Imperative implementation -/

/-- Mutable Wagner–Fischer sweep. Each step is the inner loop of the Python DP. -/
def sweepFrom (row : List Nat) (xs ys : List α) : List Nat :=
  Id.run do
    let mut row := row
    for x in xs do
      row := extendRow x ys row
    return row

/-- Imperative edit distance. The mutable row stores distances from the current
source suffix to every target suffix — the same cells as the Python table. -/
def editDistanceImp (s1 s2 : List α) : Nat :=
  Id.run do
    let mut row : List Nat := initSuffixRow s2
    for x in s1.reverse do
      row := extendRow x s2 row
    return row.headD 0

theorem sweepFrom_eq (row : List Nat) (xs ys : List α) :
    sweepFrom row xs ys = xs.foldl (fun r x => extendRow x ys r) row := by
  induction xs generalizing row with
  | nil => simp [sweepFrom, List.forIn_nil, Id.run, bind, pure]
  | cons x xs ih =>
      unfold sweepFrom
      simp [List.forIn_cons, Id.run, bind, pure, List.foldl_cons]
      have h := ih (extendRow x ys row)
      unfold sweepFrom at h
      simpa [Id.run, List.forIn_cons, bind, pure] using h

theorem editDistanceImp_sweep (s1 s2 : List α) :
    editDistanceImp s1 s2 = (sweepFrom (initSuffixRow s2) s1.reverse s2).headD 0 := by
  simp [editDistanceImp, sweepFrom]

/-! ## Imperative tests -/

example : editDistanceImp ("hello".toList) ("hello".toList) = 0 := by native_decide
example : editDistanceImp ("cat".toList) ("bat".toList) = 1 := by native_decide
example : editDistanceImp ("cat".toList) ("cats".toList) = 1 := by native_decide
example : editDistanceImp ("kitten".toList) ("sitting".toList) = 3 := by native_decide
example : editDistanceImp ([] : List Char) ("abc".toList) = 3 := by native_decide
example : editDistanceImp ([1, 2, 3] : List Nat) [4, 5, 6] = 3 := by native_decide
example : editDistanceImp ("intention".toList) ("execution".toList) = 5 := by native_decide
example : editDistanceImp ("saturday".toList) ("sunday".toList) = 3 := by native_decide

#eval editDistanceImp ("kitten".toList) ("sitting".toList)

/-! ## Equivalence -/

theorem editDistance_eq_imp (s1 s2 : List α) :
    editDistance s1 s2 = editDistanceImp s1 s2 := by
  rw [editDistanceImp_sweep, sweepFrom_eq, List.foldl_reverse]
  simp [editDistance, suffixRow]

end edit_distance
