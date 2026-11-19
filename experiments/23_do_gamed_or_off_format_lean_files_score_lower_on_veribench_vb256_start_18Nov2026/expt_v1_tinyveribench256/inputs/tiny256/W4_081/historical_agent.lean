import Mathlib
namespace Agent

/-!
# Safe concrete witness generation

Translation of the Python `safe_witness_gen` and its six `check` assertions.
Python integers are modeled by unbounded `Int`, and `None` by `Option.none`.
The function returns the lower bound itself exactly when the half-open interval
is nonempty. There is no feasibility precondition: empty and inverted intervals
are valid inputs and return `none`.

The array check uses an actual `Array Int` containing `0, ..., 19`. Optional
array lookup expresses successful, directly executable indexing without an
exception. Its specification includes nonnegativity, so conversion to `Nat`
does not lose information. Bounded tests are evidence only; the general
properties and functional/imperative equivalence have separate proofs.
-/

namespace SafeWitnessGenSafe

/-! ## Functional implementation -/

def safe_witness_gen (lower upper : Int) : Option Int :=
  if lower < upper then some lower else none

/-- The Python expression `list(range(n))`, represented as an array. -/
def rangeArray (n : Nat) : Array Int :=
  ((List.range n).map (fun i : Nat => (i : Int))).toArray

/-- Boolean translation of all six assertions in the Python test driver. -/
def check (candidate : Int → Int → Option Int) : Bool :=
  let feasible := match candidate 3 7 with
    | none => false
    | some w => decide (3 ≤ w ∧ w < 7)
  let indexable := match candidate 5 15 with
    | none => false
    | some w => (rangeArray 20)[w.toNat]? == some w
  feasible &&
    (candidate 10 3 == none) &&
    (candidate 5 5 == none) &&
    (candidate 0 1 == some 0) &&
    indexable &&
    (candidate 100 50 == none)

/-! ## Unit tests: all six original checks -/

example : (match safe_witness_gen 3 7 with
    | none => false
    | some w => decide (3 ≤ w ∧ w < 7)) = true := by native_decide

example : safe_witness_gen 10 3 = none := by native_decide
example : safe_witness_gen 5 5 = none := by native_decide
example : safe_witness_gen 0 1 = some 0 := by native_decide

example : (match safe_witness_gen 5 15 with
    | none => false
    | some w => decide ((rangeArray 20)[w.toNat]? = some w)) = true := by native_decide

example : safe_witness_gen 100 50 = none := by native_decide
example : check safe_witness_gen = true := by native_decide

-- Additional signed and arbitrary-precision integer cases.
example : safe_witness_gen (-8) (-3) = some (-8) := by native_decide
example : safe_witness_gen (-3) (-8) = none := by native_decide
example : safe_witness_gen (-4) (-4) = none := by native_decide
example : safe_witness_gen (-1) 0 = some (-1) := by native_decide
example : safe_witness_gen 100000000000000000000 100000000000000000001 =
    some 100000000000000000000 := by native_decide

#eval safe_witness_gen 3 7
#eval safe_witness_gen 10 3
#eval safe_witness_gen 5 5
#eval safe_witness_gen 0 1
#eval (safe_witness_gen 5 15).bind (fun w => (rangeArray 20)[w.toNat]?)
#eval safe_witness_gen 100 50
#eval check safe_witness_gen

/-! ## Precondition and proved properties -/

/-- Every pair of Python integers is admissible, including inverted bounds. -/
def Pre (_lower _upper : Int) : Prop := True

/-- A feasible interval yields exactly its lower bound, not just any witness. -/
def feasible_prop (lower upper : Int) : Prop :=
  lower < upper → safe_witness_gen lower upper = some lower

theorem feasible_thm (lower upper : Int) : feasible_prop lower upper := by
  unfold feasible_prop
  intro h
  simp [safe_witness_gen, h]

/-- `none` is returned exactly for empty or inverted half-open intervals. -/
def infeasible_prop (lower upper : Int) : Prop :=
  safe_witness_gen lower upper = none ↔ upper ≤ lower

theorem infeasible_thm (lower upper : Int) : infeasible_prop lower upper := by
  unfold infeasible_prop safe_witness_gen
  by_cases h : lower < upper
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

/-- Every returned value is the concrete lower bound and lies in the interval. -/
def witness_prop (lower upper : Int) : Prop :=
  ∀ w : Int, safe_witness_gen lower upper = some w →
    w = lower ∧ lower ≤ w ∧ w < upper

theorem witness_thm (lower upper : Int) : witness_prop lower upper := by
  unfold witness_prop
  intro w hw
  by_cases h : lower < upper
  · have heq : lower = w := by simpa [safe_witness_gen, h] using hw
    subst w
    exact ⟨rfl, le_refl lower, h⟩
  · simp [safe_witness_gen, h] at hw

/-- The generator succeeds if and only if a satisfying integer exists. -/
def completeness_prop (lower upper : Int) : Prop :=
  (∃ w : Int, safe_witness_gen lower upper = some w) ↔
    ∃ w : Int, lower ≤ w ∧ w < upper

theorem completeness_thm (lower upper : Int) : completeness_prop lower upper := by
  unfold completeness_prop
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨_, hl, hu⟩ := witness_thm lower upper w hw
    exact ⟨w, hl, hu⟩
  · rintro ⟨w, hl, hu⟩
    exact ⟨lower, feasible_thm lower upper (lt_of_le_of_lt hl hu)⟩

/-- Any feasible subinterval of the source array bounds supplies an index
whose array element equals the witness, with no additional search. -/
def array_index_prop (lower upper : Int) : Prop :=
  0 ≤ lower → upper ≤ 20 → lower < upper →
    ∃ w : Int, safe_witness_gen lower upper = some w ∧
      0 ≤ w ∧ (rangeArray 20)[w.toNat]? = some w

theorem array_index_thm (lower upper : Int) : array_index_prop lower upper := by
  unfold array_index_prop
  intro hl hu hlt
  refine ⟨lower, feasible_thm lower upper hlt, hl, ?_⟩
  have hn : lower.toNat < 20 := by omega
  have hc : (lower.toNat : Int) = lower := Int.toNat_of_nonneg hl
  simp only [rangeArray, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hn, Option.map_some, hc]

/-! ## Postcondition -/

/-- Total correctness, including infeasibility and concrete witness usability. -/
def Post_prop (lower upper : Int) : Prop :=
  feasible_prop lower upper ∧
  infeasible_prop lower upper ∧
  witness_prop lower upper ∧
  completeness_prop lower upper ∧
  array_index_prop lower upper

/-! ## Property-based tests

Exhaustive small cases use all 4,225 ordered pairs from `[-32, 32]`.
These include empty/inverted intervals, negative witnesses, singleton ranges,
and all admissible subintervals of the 20-element array. The checkers below
are executable forms of the corresponding propositions, not proof oracles.
-/

private def testInts : List Int :=
  (List.range 65).map (fun n : Nat => (n : Int) - 32)

private def forAllBounds (p : Int → Int → Bool) : Bool :=
  testInts.all (fun lower => testInts.all (fun upper => p lower upper))

private def feasibleCheck (lower upper : Int) : Bool :=
  decide (lower < upper → safe_witness_gen lower upper = some lower)

private def infeasibleCheck (lower upper : Int) : Bool :=
  decide (safe_witness_gen lower upper = none ↔ upper ≤ lower)

-- The universally quantified witness implication is vacuous for `none`;
-- for `some w`, only that returned w can satisfy its antecedent.
private def witnessCheck (lower upper : Int) : Bool :=
  match safe_witness_gen lower upper with
  | none => true
  | some w => decide (w = lower ∧ lower ≤ w ∧ w < upper)

-- An integer exists in [lower, upper) iff lower < upper, with lower itself
-- furnishing a witness. This avoids an infinite existential search in a PBT.
private def completenessCheck (lower upper : Int) : Bool :=
  (safe_witness_gen lower upper).isSome == decide (lower < upper)

private def arrayIndexCheck (lower upper : Int) : Bool :=
  if 0 ≤ lower ∧ upper ≤ 20 ∧ lower < upper then
    match safe_witness_gen lower upper with
    | none => false
    | some w => decide (0 ≤ w ∧ (rangeArray 20)[w.toNat]? = some w)
  else true

private def postCheck (lower upper : Int) : Bool :=
  feasibleCheck lower upper && infeasibleCheck lower upper &&
    witnessCheck lower upper && completenessCheck lower upper &&
    arrayIndexCheck lower upper

-- PBT for feasible_prop.
example : forAllBounds feasibleCheck = true := by native_decide
-- PBT for infeasible_prop.
example : forAllBounds infeasibleCheck = true := by native_decide
-- PBT for witness_prop.
example : forAllBounds witnessCheck = true := by native_decide
-- PBT for completeness_prop.
example : forAllBounds completenessCheck = true := by native_decide
-- PBT for array_index_prop.
example : forAllBounds arrayIndexCheck = true := by native_decide
-- PBT for the full Post_prop, without excluding infeasible inputs.
example : forAllBounds postCheck = true := by native_decide

#eval forAllBounds postCheck

/-! ## Correctness -/

theorem correctness_thm (lower upper : Int) :
    Pre lower upper → Post_prop lower upper := by
  intro _
  exact ⟨feasible_thm lower upper, infeasible_thm lower upper,
    witness_thm lower upper, completeness_thm lower upper,
    array_index_thm lower upper⟩

/-! ## Imperative implementation -/

/-- The same branching algorithm with a mutable optional result. -/
def safe_witness_gen_imp (lower upper : Int) : Option Int := Id.run do
  let mut result : Option Int := none
  if lower < upper then
    result := some lower
  return result

/-! ## Imperative tests -/

example : safe_witness_gen_imp 3 7 = some 3 := by native_decide
example : safe_witness_gen_imp 10 3 = none := by native_decide
example : safe_witness_gen_imp 5 5 = none := by native_decide
example : safe_witness_gen_imp 0 1 = some 0 := by native_decide
example : (match safe_witness_gen_imp 5 15 with
    | none => false
    | some w => decide ((rangeArray 20)[w.toNat]? = some w)) = true := by native_decide
example : safe_witness_gen_imp 100 50 = none := by native_decide
example : check safe_witness_gen_imp = true := by native_decide
example : safe_witness_gen_imp (-8) (-3) = some (-8) := by native_decide

#eval check safe_witness_gen_imp
#eval safe_witness_gen_imp 5 15

-- Bounded PBT for functional/imperative equivalence on all signed test pairs.
example : forAllBounds (fun lower upper =>
    decide (safe_witness_gen lower upper = safe_witness_gen_imp lower upper)) =
    true := by native_decide

/-! ## Functional/imperative equivalence -/

theorem equivalence_thm (lower upper : Int) :
    safe_witness_gen lower upper = safe_witness_gen_imp lower upper := by
  by_cases h : lower < upper <;>
    simp [safe_witness_gen, safe_witness_gen_imp, h]

/-- Extensional equality holds over the entire integer input domain. -/
theorem functional_eq_imperative_thm : safe_witness_gen = safe_witness_gen_imp := by
  funext lower upper
  exact equivalence_thm lower upper

end SafeWitnessGenSafe
end Agent
