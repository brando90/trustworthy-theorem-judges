import Mathlib

/-!
# HumanEval/35: maximum element

The numeric model is unbounded mathematical integers, as in the supplied examples.
`max_element` returns the maximum of a nonempty list. `none` represents the
IndexError raised by Python's initial `l[0]` on an empty list; `some m` represents
normal return of `m`. The functional fold and the mutable loop are proved equal.
-/

namespace humaneval_35_max_element

/-- Functional maximum; the first element initializes the accumulator. -/
def max_element : List Int → Option Int
  | [] => none
  | x :: xs => some (xs.foldl max x)

-- Unit tests, including the docstring and the supplied test function.
example : max_element [1, 2, 3] = some 3 := by native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = some 123 := by
  native_decide
example : max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = some 124 := by
  native_decide
example : max_element [-11] = some (-11) := by native_decide
example : max_element [-7, -2, -9] = some (-2) := by native_decide
example : max_element [4, 4, 4] = some 4 := by native_decide
example : max_element [] = none := by native_decide
#eval max_element [1, 2, 3]
#eval max_element [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

/-- Exactly the inputs on which Python returns normally. -/
def Pre (xs : List Int) : Prop := xs ≠ []

/-- The result exists and is an actual input element. -/
def member_prop (xs : List Int) : Prop :=
  ∃ m, max_element xs = some m ∧ m ∈ xs

/-- Every input element is at most the returned value. -/
def upper_bound_prop (xs : List Int) : Prop :=
  ∀ m, max_element xs = some m → ∀ x ∈ xs, x ≤ m

/-- An integer bounds the input iff it bounds the returned maximum. -/
def least_bound_prop (xs : List Int) : Prop :=
  ∀ m, max_element xs = some m → ∀ b : Int,
    (m ≤ b ↔ ∀ x ∈ xs, x ≤ b)

/-- Failure occurs exactly for the empty list, not for negative inputs. -/
def empty_prop (xs : List Int) : Prop :=
  max_element xs = none ↔ xs = []

-- Fold invariants used in the proofs below.
theorem fold_max_mem (xs : List Int) (a : Int) :
    xs.foldl max a = a ∨ xs.foldl max a ∈ xs := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases ih (max a x) with h | h
    · by_cases ha : a ≤ x
      · right
        simp only [max_eq_right ha] at h
        simp [max_eq_right ha, h]
      · left
        simpa [max_eq_left (le_of_not_ge ha)] using h
    · exact Or.inr (List.mem_cons_of_mem x h)

theorem fold_max_bounds (xs : List Int) (a : Int) :
    a ≤ xs.foldl max a ∧ ∀ x ∈ xs, x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hacc, hxs⟩ := ih (max a x)
    constructor
    · exact le_trans (le_max_left a x) hacc
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact le_trans (le_max_right a y) hacc
      · exact hxs y hy

theorem member_thm (xs : List Int) (h : Pre xs) : member_prop xs := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons a xs =>
    refine ⟨xs.foldl max a, rfl, ?_⟩
    rcases fold_max_mem xs a with hm | hm
    · simp [hm]
    · exact List.mem_cons_of_mem a hm

theorem upper_bound_thm (xs : List Int) : upper_bound_prop xs := by
  intro m hm x hx
  cases xs with
  | nil => simp [max_element] at hm
  | cons a xs =>
    simp only [max_element, Option.some.injEq] at hm
    subst m
    obtain ⟨ha, hs⟩ := fold_max_bounds xs a
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact hs x hx

theorem least_bound_thm (xs : List Int) : least_bound_prop xs := by
  intro m hm b
  constructor
  · intro hb x hx
    exact le_trans (upper_bound_thm xs m hm x hx) hb
  · intro hb
    have hn : Pre xs := by
      intro he
      simp [he, max_element] at hm
    obtain ⟨n, hn, hmem⟩ := member_thm xs hn
    have heq : n = m := Option.some.inj (hn.symm.trans hm)
    subst n
    exact hb m hmem

theorem empty_thm (xs : List Int) : empty_prop xs := by
  cases xs <;> simp [empty_prop, max_element]

/-- Full normal-return contract: membership, maximality, least bound, and failure behavior. -/
def Post_prop (xs : List Int) : Prop :=
  member_prop xs ∧ upper_bound_prop xs ∧ least_bound_prop xs ∧ empty_prop xs

-- Property-based tests: exhaust all lists of length at most four over [-2,2].
-- These are executable counterparts of the quantified properties, not proofs.
def smallLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => [] :: ([-2, -1, 0, 1, 2] : List Int).flatMap
      (fun a => (smallLists n).map (fun xs => a :: xs))

def memberCheck (xs : List Int) : Bool :=
  match max_element xs with
  | none => xs.isEmpty -- skip the inadmissible empty input
  | some m => xs.contains m

def upperBoundCheck (xs : List Int) : Bool :=
  match max_element xs with
  | none => true
  | some m => xs.all (fun x => decide (x ≤ m))

def leastBoundCheck (xs : List Int) : Bool :=
  match max_element xs with
  | none => true
  | some m => ([-3, -2, -1, 0, 1, 2, 3] : List Int).all
      (fun b => decide (m ≤ b) == xs.all (fun x => decide (x ≤ b)))

def emptyCheck (xs : List Int) : Bool :=
  (max_element xs).isNone == xs.isEmpty

-- PBT: member_prop, under Pre.
example : (smallLists 4).all memberCheck = true := by native_decide
-- PBT: upper_bound_prop.
example : (smallLists 4).all upperBoundCheck = true := by native_decide
-- PBT: least_bound_prop, with bounds sampled exhaustively from [-3,3].
example : (smallLists 4).all leastBoundCheck = true := by native_decide
-- PBT: empty_prop, including the exceptional case.
example : (smallLists 4).all emptyCheck = true := by native_decide
-- PBT: Post_prop, under Pre.
example : (smallLists 4).all (fun xs =>
    memberCheck xs && upperBoundCheck xs && leastBoundCheck xs && emptyCheck xs)
    = true := by native_decide
#eval (smallLists 4).length
#eval (smallLists 4).all (fun xs =>
  memberCheck xs && upperBoundCheck xs && leastBoundCheck xs && emptyCheck xs)

theorem correctness (xs : List Int) : Pre xs → Post_prop xs := by
  intro h
  exact ⟨member_thm xs h, upper_bound_thm xs, least_bound_thm xs, empty_thm xs⟩

/-- Literal mutable-state translation: the loop visits the whole original list. -/
def max_element_imperative (xs : List Int) : Option Int := Id.run do
  match xs with
  | [] => return none
  | a :: _ =>
    let mut m := a
    for e in xs do
      if e > m then
        m := e
    return some m

example : max_element_imperative [1, 2, 3] = some 3 := by native_decide
example : max_element_imperative
    [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = some 124 := by native_decide
example : max_element_imperative [-7, -2, -9] = some (-2) := by native_decide
example : max_element_imperative [] = none := by native_decide
#eval max_element_imperative [1, 2, 3]
#eval max_element_imperative [5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]

/-- The Python conditional is the integer maximum operation. -/
private theorem loop_update (m e : Int) :
    (if m < e then (pure (ForInStep.yield e) : Id (ForInStep Int))
     else pure (ForInStep.yield m)) = pure (ForInStep.yield (max m e)) := by
  by_cases h : m < e
  · simp [h, max_eq_right (le_of_lt h)]
  · simp [h, max_eq_left (le_of_not_gt h)]

/-- Equality includes the exceptional empty case. Visiting the initial element
again in the Python loop leaves the accumulator unchanged. -/
theorem functional_eq_imperative (xs : List Int) :
    max_element xs = max_element_imperative xs := by
  cases xs with
  | nil => rfl
  | cons a xs => simp [max_element, max_element_imperative, loop_update]

end humaneval_35_max_element
