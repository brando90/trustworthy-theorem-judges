import Mathlib
namespace Agent

/-!
# Safe baggy-bounds access

Translation of the Python program from MIT 6.858 Lecture 4.  Logical bounds,
not the rounded slot size, decide whether an access is permitted. Python's
unbounded signed integers are represented by `Int`; the buffer is a polymorphic
list. `Except` represents raised exceptions, including the `IndexError` that
Python's final list access can raise when an inconsistent size exceeds the
physical buffer length. The ValueError diagnostic is preserved verbatim.

The power-of-two helper has its exact mathematical closed form: ceiling base-2
logarithm followed by exponentiation. Its specification proves positivity,
coverage, minimality, and the minimum-one behavior, including negative inputs.
`Pre` describes a well-formed allocation (padding is permitted); the bounds and
exception theorems themselves apply even to malformed allocations.
-/

namespace UnsafeBaggyBoundsSafe

inductive AccessError where
  | valueError (message : String)
  | indexError
  deriving DecidableEq, BEq, Repr

deriving instance DecidableEq, BEq for Except

/-- The actual error message constructed by the Python guard. -/
def boundsMessage (size index : Int) : String :=
  s!"index {index} out of logical bounds [0, {size}): baggy-bounds violation prevented"

/-- Smallest power of two at least `n`, with minimum one. -/
def nextPowerOfTwo (n : Int) : Nat :=
  2 ^ Nat.clog 2 n.toNat

/-- One guarded doubling step, also used to describe the loop invariant. -/
private def doublingStep (n p : Nat) : Nat := if p < n then 2 * p else p

/-- The guard is checked before performing the physical list lookup. -/
def safeBaggyGet (buf : List α) (size index : Int) : Except AccessError α :=
  if index < 0 ∨ size ≤ index then
    .error (.valueError (boundsMessage size index))
  else
    match buf[index.toNat]? with
    | some value => .ok value
    | none => .error .indexError

/-- Executable translation of all assertions in Python's `check`. -/
def check (candidate : List Int → Int → Int → Except AccessError Int) : Bool :=
  candidate [10, 20, 30] 3 0 == .ok 10 &&
  candidate [10, 20, 30] 3 2 == .ok 30 &&
  candidate [10, 20, 30] 3 3 == .error (.valueError (boundsMessage 3 3)) &&
  candidate [99] 1 0 == .ok 99 &&
  candidate [1, 2, 3, 4, 5] 5 5 == .error (.valueError (boundsMessage 5 5)) &&
  candidate [1, 2, 3] 3 10 == .error (.valueError (boundsMessage 3 10)) &&
  candidate [1, 2] 2 (-1) == .error (.valueError (boundsMessage 2 (-1))) &&
  candidate [0, 1, 2, 3] 4 3 == .ok 3

-- Fixed tests: each of the Python assertions, plus representation edge cases.
example : safeBaggyGet [10, 20, 30] 3 0 = .ok 10 := by native_decide
example : safeBaggyGet [10, 20, 30] 3 2 = .ok 30 := by native_decide
example : safeBaggyGet [10, 20, 30] 3 3 =
    .error (.valueError (boundsMessage 3 3)) := by native_decide
example : safeBaggyGet [99] 1 0 = .ok 99 := by native_decide
example : safeBaggyGet [1, 2, 3, 4, 5] 5 5 =
    .error (.valueError (boundsMessage 5 5)) := by native_decide
example : safeBaggyGet [1, 2, 3] 3 10 =
    .error (.valueError (boundsMessage 3 10)) := by native_decide
example : safeBaggyGet [1, 2] 2 (-1) =
    .error (.valueError (boundsMessage 2 (-1))) := by native_decide
example : safeBaggyGet [0, 1, 2, 3] 4 3 = .ok 3 := by native_decide
-- A physically present padding element must still be inaccessible.
example : safeBaggyGet [10, 20, 30, 999] 3 3 =
    .error (.valueError (boundsMessage 3 3)) := by native_decide
example : safeBaggyGet ([] : List Nat) 0 0 =
    .error (.valueError (boundsMessage 0 0)) := by native_decide
example : safeBaggyGet [7] (-2) 0 =
    .error (.valueError (boundsMessage (-2) 0)) := by native_decide
example : safeBaggyGet [7] 3 1 = .error .indexError := by native_decide
example : nextPowerOfTwo (-5) = 1 ∧ nextPowerOfTwo 0 = 1 ∧
    nextPowerOfTwo 1 = 1 ∧ nextPowerOfTwo 3 = 4 ∧
    nextPowerOfTwo 4 = 4 ∧ nextPowerOfTwo 5 = 8 := by native_decide
example : check safeBaggyGet = true := by native_decide
#eval check safeBaggyGet
#eval safeBaggyGet [10, 20, 30, 999] 3 3
#eval ([-3, 0, 1, 2, 3, 4, 5, 17] : List Int).map nextPowerOfTwo

/-- A logical allocation fits in its physical buffer, possibly with padding.
No restriction on `index` is made: exceptional accesses are part of the spec. -/
def Pre (buf : List α) (size : Int) : Prop :=
  0 ≤ size ∧ size ≤ (buf.length : Int)

/-- Full least-power specification, over every signed Python integer. -/
def next_power_prop (n : Int) : Prop :=
  0 < nextPowerOfTwo n ∧
  n ≤ (nextPowerOfTwo n : Int) ∧
  (∃ k : Nat, nextPowerOfTwo n = 2 ^ k) ∧
  (∀ k : Nat, n ≤ (2 ^ k : Nat) → nextPowerOfTwo n ≤ 2 ^ k) ∧
  (n ≤ 1 → nextPowerOfTwo n = 1)

theorem next_power_thm (n : Int) : next_power_prop n := by
  refine ⟨by exact pow_pos (by decide) _,
    Int.toNat_le.mp (Nat.le_pow_clog (by decide : 1 < 2) n.toNat),
    ⟨Nat.clog 2 n.toNat, rfl⟩, ?_, ?_⟩
  · intro k hk
    exact Nat.pow_le_pow_right (by decide)
      ((Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp (Int.toNat_le.mpr hk))
  · intro hn
    have ht : n.toNat ≤ 1 := by omega
    simp [nextPowerOfTwo, Nat.clog_of_right_le_one ht]

/-- ValueError occurs exactly for a negative or logically out-of-range index. -/
def logical_bounds_prop (buf : List α) (size index : Int) : Prop :=
  safeBaggyGet buf size index = .error (.valueError (boundsMessage size index)) ↔
    ¬ (0 ≤ index ∧ index < size)

theorem logical_bounds_thm (buf : List α) (size index : Int) :
    logical_bounds_prop buf size index := by
  unfold logical_bounds_prop
  by_cases h : index < 0 ∨ size ≤ index
  · have hg : ¬ (0 ≤ index ∧ index < size) := by omega
    simp [safeBaggyGet, h, hg]
  · have hg : 0 ≤ index ∧ index < size := by omega
    cases hl : buf[index.toNat]? <;> simp [safeBaggyGet, h, hl, hg]

/-- A successful call returns exactly the stored element, and is logically valid. -/
def successful_read_prop (buf : List α) (size index : Int) (value : α) : Prop :=
  safeBaggyGet buf size index = .ok value ↔
    0 ≤ index ∧ index < size ∧ buf[index.toNat]? = some value

theorem successful_read_thm (buf : List α) (size index : Int) (value : α) :
    successful_read_prop buf size index value := by
  unfold successful_read_prop
  by_cases h : index < 0 ∨ size ≤ index
  · have hg : ¬ (0 ≤ index ∧ index < size) := by omega
    simp [safeBaggyGet, h, ← and_assoc, hg]
  · have hg : 0 ≤ index ∧ index < size := by omega
    cases hl : buf[index.toNat]? <;>
      simp [safeBaggyGet, h, hl, hg.1, hg.2]

/-- No physical error is hidden: malformed allocations behave like Python lists. -/
def physical_bounds_prop (buf : List α) (size index : Int) : Prop :=
  safeBaggyGet buf size index = .error .indexError ↔
    0 ≤ index ∧ index < size ∧ buf.length ≤ index.toNat

theorem physical_bounds_thm (buf : List α) (size index : Int) :
    physical_bounds_prop buf size index := by
  unfold physical_bounds_prop
  by_cases h : index < 0 ∨ size ≤ index
  · have hg : ¬ (0 ≤ index ∧ index < size) := by omega
    simp [safeBaggyGet, h, ← and_assoc, hg]
  · have hg : 0 ≤ index ∧ index < size := by omega
    have hn : buf[index.toNat]? = none ↔ buf.length ≤ index.toNat :=
      List.getElem?_eq_none_iff
    simp only [safeBaggyGet, if_neg h, hg.1, hg.2, true_and, ← hn]
    cases buf[index.toNat]? <;> simp

/-- In particular, the unused portion of a rounded slot is inaccessible. -/
def intra_slot_prop (buf : List α) (size index : Int) : Prop :=
  size ≤ index ∧ index < (nextPowerOfTwo size : Int) →
    safeBaggyGet buf size index = .error (.valueError (boundsMessage size index))

theorem intra_slot_thm (buf : List α) (size index : Int) :
    intra_slot_prop buf size index := by
  intro h
  exact (logical_bounds_thm buf size index).mpr (by omega)

/-- Every logically valid access in a well-formed allocation actually has an
    element and returns it; it cannot fail with either exception. -/
def valid_allocation_prop (buf : List α) (size index : Int) : Prop :=
  0 ≤ index ∧ index < size →
    (buf[index.toNat]?).isSome = true ∧
    (safeBaggyGet buf size index).toOption = buf[index.toNat]?

theorem valid_allocation_thm (buf : List α) (size index : Int) (hp : Pre buf size) :
    valid_allocation_prop buf size index := by
  intro hg
  have hi : index.toNat < buf.length := by
    have := hp.2
    have := Int.toNat_of_nonneg hg.1
    omega
  have h : ¬ (index < 0 ∨ size ≤ index) := by omega
  simp [safeBaggyGet, h, List.getElem?_eq_getElem hi, Except.toOption]

/-- Adding slot padding cannot change the observable behavior. -/
def padding_invariance_prop (buf padding : List α) (size index : Int) : Prop :=
  safeBaggyGet (buf ++ padding) size index = safeBaggyGet buf size index

theorem padding_invariance_thm (buf padding : List α) (size index : Int)
    (hp : Pre buf size) : padding_invariance_prop buf padding size index := by
  unfold padding_invariance_prop safeBaggyGet
  by_cases h : index < 0 ∨ size ≤ index
  · simp [h]
  · have hi : index.toNat < buf.length := by
      have := hp.2
      have hz : 0 ≤ index := by omega
      have := Int.toNat_of_nonneg hz
      omega
    simp [h, List.getElem?_append_left hi]

/-- Combined contract. Exact exception and success specifications are included,
    as well as the least-power slot layout and its noninterference with access. -/
def Post_prop (buf : List α) (size index : Int) : Prop :=
  next_power_prop size ∧
  logical_bounds_prop buf size index ∧
  (∀ value, successful_read_prop buf size index value) ∧
  physical_bounds_prop buf size index ∧
  intra_slot_prop buf size index ∧
  valid_allocation_prop buf size index ∧
  (∀ padding, padding_invariance_prop buf padding size index)

/-! ## Bounded property-based tests

These checks evaluate the implementation, not the proved theorems. All lists of
length 0..4 over {0,1,7} are enumerated; sizes and indices range over -3..11.
This includes empty/negative allocations, physical errors, both logical
boundaries, padding, and out-of-slot accesses. Theorems remain polymorphic and
unbounded. The finite exponent and value loops below are PBT samples of the
unbounded quantifiers, not replacements for them.
-/

private def buffersOfLength : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => [0, 1, 7].flatMap fun value =>
      (buffersOfLength n).map (value :: ·)

private def testBuffers : List (List Nat) :=
  (List.range 5).flatMap buffersOfLength

private def testPaddings : List (List Nat) :=
  (List.range 3).flatMap buffersOfLength

private def testInts : List Int :=
  (List.range 15).map (fun n => (n : Int) - 3)

private def allAccessCases (test : List Nat → Int → Int → Bool) : Bool :=
  testBuffers.all fun buf => testInts.all fun size =>
    testInts.all fun index => test buf size index

/-- Executable counterpart of `next_power_prop`; exponents are sampled too. -/
private def powerTest (n : Int) : Bool :=
  decide (0 < nextPowerOfTwo n ∧ n ≤ (nextPowerOfTwo n : Int)) &&
  (List.range (n.toNat + 1)).any (fun k => decide (nextPowerOfTwo n = 2 ^ k)) &&
  (List.range (n.toNat + 2)).all (fun k =>
    decide (n ≤ (2 ^ k : Nat) → nextPowerOfTwo n ≤ 2 ^ k)) &&
  decide (n ≤ 1 → nextPowerOfTwo n = 1)

private def logicalBoundsTest (buf : List Nat) (size index : Int) : Bool :=
  decide (safeBaggyGet buf size index = .error (.valueError (boundsMessage size index)) ↔
    ¬ (0 ≤ index ∧ index < size))

private def successfulReadTest (buf : List Nat) (size index : Int) (value : Nat) : Bool :=
  decide (safeBaggyGet buf size index = .ok value ↔
    0 ≤ index ∧ index < size ∧ buf[index.toNat]? = some value)

private def physicalBoundsTest (buf : List Nat) (size index : Int) : Bool :=
  decide (safeBaggyGet buf size index = .error .indexError ↔
    0 ≤ index ∧ index < size ∧ buf.length ≤ index.toNat)

private def intraSlotTest (buf : List Nat) (size index : Int) : Bool :=
  decide (size ≤ index ∧ index < (nextPowerOfTwo size : Int) →
    safeBaggyGet buf size index = .error (.valueError (boundsMessage size index)))

private def validAllocationTest (buf : List Nat) (size index : Int) : Bool :=
  decide (0 ≤ size ∧ size ≤ (buf.length : Int) →
    0 ≤ index ∧ index < size →
    (buf[index.toNat]?).isSome = true ∧
    (safeBaggyGet buf size index).toOption = buf[index.toNat]?)

private def paddingInvarianceTest (buf padding : List Nat) (size index : Int) : Bool :=
  decide (0 ≤ size ∧ size ≤ (buf.length : Int) →
    safeBaggyGet (buf ++ padding) size index = safeBaggyGet buf size index)

private def postTest (buf : List Nat) (size index : Int) : Bool :=
  if 0 ≤ size ∧ size ≤ (buf.length : Int) then
    powerTest size && logicalBoundsTest buf size index &&
    (List.range 9).all (successfulReadTest buf size index) &&
    physicalBoundsTest buf size index && intraSlotTest buf size index &&
    validAllocationTest buf size index &&
    testPaddings.all (fun padding => paddingInvarianceTest buf padding size index)
  else true

-- PBT for next_power_prop: signed requests -5..64, including power boundaries.
example : ((List.range 70).map (fun n => (n : Int) - 5)).all powerTest = true := by
  native_decide
-- PBT for logical_bounds_prop (no precondition).
example : allAccessCases logicalBoundsTest = true := by native_decide
-- PBT for successful_read_prop (both present and absent return values).
example : allAccessCases (fun buf size index =>
    (List.range 9).all (successfulReadTest buf size index)) = true := by native_decide
-- PBT for physical_bounds_prop (including oversized logical allocations).
example : allAccessCases physicalBoundsTest = true := by native_decide
-- PBT for intra_slot_prop (in particular, logical size 3 and index 3).
example : allAccessCases intraSlotTest = true := by native_decide
-- PBT for valid_allocation_prop, with precisely the theorem's Pre implication.
example : allAccessCases validAllocationTest = true := by native_decide
-- PBT for padding_invariance_prop, including arbitrary sampled padding values.
example : allAccessCases (fun buf size index =>
    testPaddings.all (fun padding => paddingInvarianceTest buf padding size index)) = true := by
  native_decide
-- PBT for the entire Post_prop under Pre, retaining every conjunct.
example : allAccessCases postTest = true := by native_decide
#eval ("bounded Post_prop", allAccessCases postTest)

/-- Correctness includes invalid indices: Pre constrains only the allocation. -/
theorem correctness_thm (buf : List α) (size index : Int) :
    Pre buf size → Post_prop buf size index := by
  intro hp
  exact ⟨next_power_thm size, logical_bounds_thm buf size index,
    successful_read_thm buf size index, physical_bounds_thm buf size index,
    intra_slot_thm buf size index, valid_allocation_thm buf size index hp,
    fun padding => padding_invariance_thm buf padding size index hp⟩

/-! ## Imperative translation -/

/-- Mutable result state; neither failure of the guard nor a negative index
    reaches the list access. The guards have the same order as in Python. -/
def safeBaggyGetImperative (buf : List α) (size index : Int) : Except AccessError α := Id.run do
  let mut result : Except AccessError α := .error .indexError
  if index < 0 then
    result := .error (.valueError (boundsMessage size index))
  else if size ≤ index then
    result := .error (.valueError (boundsMessage size index))
  else
    match buf[index.toNat]? with
    | some value => result := .ok value
    | none => result := .error .indexError
  return result

/-- Python's `p <<= 1` is exact multiplication by two on natural numbers.
The finite loop permits `n.toNat` iterations. After reaching `p ≥ n` the state
is unchanged; the invariant below proves this bound always suffices. Thus no
fuel-exhaustion result or nontermination axiom changes the Python behavior. -/
def nextPowerOfTwoImperative (n : Int) : Nat := Id.run do
  let mut p := 1
  for _ in List.range n.toNat do
    p := if p < n.toNat then 2 * p else p
  return p

-- The same complete source test suite is applied to the imperative candidate.
example : check safeBaggyGetImperative = true := by native_decide
example : safeBaggyGetImperative [10, 20, 30, 999] 3 3 =
    .error (.valueError (boundsMessage 3 3)) := by native_decide
example : safeBaggyGetImperative [7] 3 1 = .error .indexError := by native_decide
example : safeBaggyGetImperative ([] : List Nat) (-1) 0 =
    .error (.valueError (boundsMessage (-1) 0)) := by native_decide
example : allAccessCases (fun buf size index =>
    decide (safeBaggyGet buf size index = safeBaggyGetImperative buf size index)) = true := by
  native_decide
#eval check safeBaggyGetImperative
#eval safeBaggyGetImperative [10, 20, 30, 999] 3 3

-- Helper unit tests and bounded PBTs, including the intermediate loop invariant.
example : nextPowerOfTwoImperative (-5) = 1 ∧ nextPowerOfTwoImperative 0 = 1 ∧
    nextPowerOfTwoImperative 1 = 1 ∧ nextPowerOfTwoImperative 3 = 4 ∧
    nextPowerOfTwoImperative 4 = 4 ∧ nextPowerOfTwoImperative 5 = 8 := by native_decide
example : ((List.range 70).map (fun n => (n : Int) - 5)).all (fun n =>
    decide (nextPowerOfTwo n = nextPowerOfTwoImperative n) &&
    decide (nextPowerOfTwoImperative n = (doublingStep n.toNat)^[n.toNat] 1)) = true := by
  native_decide
example : (List.range 20).all (fun n => (List.range 20).all (fun t =>
    decide ((doublingStep n)^[t] 1 = 2 ^ min t (Nat.clog 2 n)))) = true := by
  native_decide
example : (List.range 20).all (fun n => (List.range 20).all (fun k =>
    decide (doublingStep n (2 ^ k) =
      2 ^ (if k < Nat.clog 2 n then k + 1 else k)))) = true := by native_decide
#eval ([-3, 0, 1, 2, 3, 4, 5, 17] : List Int).map nextPowerOfTwoImperative

/-- Unconditional equivalence, including negative sizes and short physical buffers. -/
theorem functional_imperative_equivalence_thm (buf : List α) (size index : Int) :
    safeBaggyGet buf size index = safeBaggyGetImperative buf size index := by
  by_cases hn : index < 0 <;> by_cases hs : size ≤ index <;>
    simp [safeBaggyGet, safeBaggyGetImperative, hn, hs]
  cases buf[index.toNat]? <;> rfl

/-- Before the threshold each iteration increments the power exponent once. -/
theorem doubling_pow_thm (n k : Nat) :
    doublingStep n (2 ^ k) = 2 ^ (if k < Nat.clog 2 n then k + 1 else k) := by
  have h : 2 ^ k < n ↔ k < Nat.clog 2 n := Nat.pow_lt_iff_lt_clog (by decide)
  by_cases hk : k < Nat.clog 2 n <;>
    simp [doublingStep, h, hk, pow_succ, Nat.mul_comm]

/-- Exact loop invariant, including all iterations after the guard becomes false. -/
theorem doubling_iterate_thm (n t : Nat) :
    (doublingStep n)^[t] 1 = 2 ^ min t (Nat.clog 2 n) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, doubling_pow_thm]
    congr 1
    split_ifs <;> omega

/-- Refinement of the mutable finite loop by functional iteration. -/
theorem loop_eq_iterate_thm (n : Int) :
    nextPowerOfTwoImperative n = (doublingStep n.toNat)^[n.toNat] 1 := by
  change (forIn (List.range n.toNat) 1
    (fun (_ : Nat) (p : Nat) => pure (ForInStep.yield (doublingStep n.toNat p))) : Id Nat).run = _
  rw [List.forIn_pure_yield_eq_foldl]
  change (List.range n.toNat).foldl (fun p _ => doublingStep n.toNat p) 1 = _
  rw [List.foldl_const, List.length_range]

/-- The least-power closed form equals the imperative doubling algorithm. -/
theorem next_power_equivalence_thm (n : Int) :
    nextPowerOfTwo n = nextPowerOfTwoImperative n := by
  rw [loop_eq_iterate_thm, doubling_iterate_thm]
  have hc : Nat.clog 2 n.toNat ≤ n.toNat :=
    (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp
      (Nat.le_of_lt (Nat.lt_two_pow_self (n := n.toNat)))
  simp [nextPowerOfTwo, Nat.min_eq_right hc]

end UnsafeBaggyBoundsSafe
end Agent
