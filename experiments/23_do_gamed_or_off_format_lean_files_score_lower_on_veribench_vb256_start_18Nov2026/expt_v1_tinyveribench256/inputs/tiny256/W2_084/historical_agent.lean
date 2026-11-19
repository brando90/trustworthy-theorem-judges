import Mathlib
namespace Agent

/-!
# Safe return-address interval check

Translation of Python's `safe_rop_check` and its five regression tests.
`Int` models Python's unbounded signed integers; acceptance means membership in
`[text_start, text_end)`. No positivity or well-formedness assumption is needed:
empty and reversed intervals reject every address. This establishes the address
range check, not a claim that range checking alone prevents all ROP attacks.

Every named theorem is proved by kernel-checked reasoning. Bounded executable
property tests are separate evidence and use `native_decide` only in examples.
-/

namespace «115_unsafeROPChain_safe»

/-! ## Functional implementation -/

def safe_rop_check (return_addr text_start text_end : Int) : Bool :=
  decide (text_start ≤ return_addr ∧ return_addr < text_end)

/-- The Python test driver, including its failure messages and success output. -/
def check : IO Unit := do
  let tests : List (Bool × String) :=
    [ (safe_rop_check 0x08048000 0x08048000 0x08049000, "valid ret rejected"),
      (safe_rop_check 0x08048500 0x08048000 0x08049000, "mid-text rejected"),
      (!safe_rop_check 0xb7e90000 0x08048000 0x08049000, "libc addr accepted"),
      (!safe_rop_check 0x00000000 0x08048000 0x08049000, "null accepted"),
      (!safe_rop_check 0x08049000 0x08048000 0x08049000, "end boundary accepted") ]
  for (passed, message) in tests do
    unless passed do
      throw (IO.userError message)
  IO.println "All tests passed."

/-! ## Unit tests -/

example : safe_rop_check 0x08048000 0x08048000 0x08049000 = true := by
  native_decide
example : safe_rop_check 0x08048500 0x08048000 0x08049000 = true := by
  native_decide
example : safe_rop_check 0xb7e90000 0x08048000 0x08049000 = false := by
  native_decide
example : safe_rop_check 0x00000000 0x08048000 0x08049000 = false := by
  native_decide
example : safe_rop_check 0x08049000 0x08048000 0x08049000 = false := by
  native_decide

-- Additional coverage for Python's signed, unrestricted input domain.
example : safe_rop_check (-3) (-5) 0 = true := by native_decide
example : safe_rop_check 0 0 0 = false := by native_decide
example : safe_rop_check 4 5 3 = false := by native_decide

#eval check

/-! ## Preconditions and mathematical properties -/

/-- The Python function is defined on every triple of integers. -/
def Pre (_return_addr _text_start _text_end : Int) : Prop := True

/-- Exact half-open interval semantics. -/
def in_range_prop (return_addr text_start text_end : Int) : Prop :=
  safe_rop_check return_addr text_start text_end = true ↔
    text_start ≤ return_addr ∧ return_addr < text_end

theorem in_range_thm (return_addr text_start text_end : Int) :
    in_range_prop return_addr text_start text_end := by
  simp [in_range_prop, safe_rop_check]

/-- An accepted address satisfies both range constraints. -/
def soundness_prop (return_addr text_start text_end : Int) : Prop :=
  safe_rop_check return_addr text_start text_end = true →
    text_start ≤ return_addr ∧ return_addr < text_end

theorem soundness_thm (return_addr text_start text_end : Int) :
    soundness_prop return_addr text_start text_end := by
  intro h
  exact (in_range_thm return_addr text_start text_end).mp h

/-- Every address in the specified interval is accepted. -/
def completeness_prop (return_addr text_start text_end : Int) : Prop :=
  (text_start ≤ return_addr ∧ return_addr < text_end) →
    safe_rop_check return_addr text_start text_end = true

theorem completeness_thm (return_addr text_start text_end : Int) :
    completeness_prop return_addr text_start text_end := by
  intro h
  exact (in_range_thm return_addr text_start text_end).mpr h

/-- Rejection is exactly being below the start or at/above the end. -/
def rejection_prop (return_addr text_start text_end : Int) : Prop :=
  safe_rop_check return_addr text_start text_end = false ↔
    return_addr < text_start ∨ text_end ≤ return_addr

theorem rejection_thm (return_addr text_start text_end : Int) :
    rejection_prop return_addr text_start text_end := by
  by_cases hLower : text_start ≤ return_addr <;>
    by_cases hUpper : return_addr < text_end <;>
    simp [rejection_prop, safe_rop_check, hLower, hUpper] <;> omega

/-- The lower boundary is included exactly when the interval is nonempty. -/
def start_boundary_prop (text_start text_end : Int) : Prop :=
  safe_rop_check text_start text_start text_end = decide (text_start < text_end)

theorem start_boundary_thm (text_start text_end : Int) :
    start_boundary_prop text_start text_end := by
  simp [start_boundary_prop, safe_rop_check]

/-- The upper boundary is always excluded, even for reversed intervals. -/
def end_boundary_prop (text_start text_end : Int) : Prop :=
  safe_rop_check text_end text_start text_end = false

theorem end_boundary_thm (text_start text_end : Int) :
    end_boundary_prop text_start text_end := by
  simp [end_boundary_prop, safe_rop_check]

/-- Empty and reversed intervals reject every integer address. -/
def empty_segment_prop (return_addr text_start text_end : Int) : Prop :=
  text_end ≤ text_start → safe_rop_check return_addr text_start text_end = false

theorem empty_segment_thm (return_addr text_start text_end : Int) :
    empty_segment_prop return_addr text_start text_end := by
  intro h
  apply (rejection_thm return_addr text_start text_end).mpr
  omega

/-! ## Postcondition -/

/-- All behavioral guarantees, including boundary and degenerate cases. -/
def Post_prop (return_addr text_start text_end : Int) : Prop :=
  in_range_prop return_addr text_start text_end ∧
  soundness_prop return_addr text_start text_end ∧
  completeness_prop return_addr text_start text_end ∧
  rejection_prop return_addr text_start text_end ∧
  start_boundary_prop text_start text_end ∧
  end_boundary_prop text_start text_end ∧
  empty_segment_prop return_addr text_start text_end

/-! ## Bounded property-based tests

Exhaustively check all pairs/triples from a signed small-integer range augmented
with the source addresses, their neighbors, and very large signed integers.
In particular, the samples include nonempty, empty, and reversed intervals.
Each check below is the corresponding property's executable Boolean form, not
a test of an already proved theorem and not an assumed Decidable instance for
the proposition. Implications use Boolean `!antecedent || consequent`.
-/

private def testInts : List Int :=
  (List.range 17).map (fun n => (n : Int) - 8) ++
    [0x08047fff, 0x08048000, 0x08048500, 0x08048fff, 0x08049000,
     0x08049001, 0xb7e90000, -(2 ^ 100), 2 ^ 100]

private def allPairs (p : Int → Int → Bool) : Bool :=
  testInts.all (fun s => testInts.all (fun e => p s e))

private def allTriples (p : Int → Int → Int → Bool) : Bool :=
  testInts.all (fun r => allPairs (p r))

-- PBT for in_range_prop.
private def inRangeCheck (r s e : Int) : Bool :=
  safe_rop_check r s e == (decide (s ≤ r) && decide (r < e))
example : allTriples inRangeCheck = true := by native_decide

-- PBT for soundness_prop.
private def soundnessCheck (r s e : Int) : Bool :=
  !safe_rop_check r s e || (decide (s ≤ r) && decide (r < e))
example : allTriples soundnessCheck = true := by native_decide

-- PBT for completeness_prop.
private def completenessCheck (r s e : Int) : Bool :=
  !(decide (s ≤ r) && decide (r < e)) || safe_rop_check r s e
example : allTriples completenessCheck = true := by native_decide

-- PBT for rejection_prop.
private def rejectionCheck (r s e : Int) : Bool :=
  (!safe_rop_check r s e) == (decide (r < s) || decide (e ≤ r))
example : allTriples rejectionCheck = true := by native_decide

-- PBT for start_boundary_prop.
private def startBoundaryCheck (s e : Int) : Bool :=
  safe_rop_check s s e == decide (s < e)
example : allPairs startBoundaryCheck = true := by native_decide

-- PBT for end_boundary_prop.
private def endBoundaryCheck (s e : Int) : Bool :=
  !safe_rop_check e s e
example : allPairs endBoundaryCheck = true := by native_decide

-- PBT for empty_segment_prop, with many samples meeting its premise.
private def emptySegmentCheck (r s e : Int) : Bool :=
  !decide (e ≤ s) || !safe_rop_check r s e
example : allTriples emptySegmentCheck = true := by native_decide

-- PBT for the complete Post_prop conjunction.
private def postCheck (r s e : Int) : Bool :=
  inRangeCheck r s e && soundnessCheck r s e && completenessCheck r s e &&
  rejectionCheck r s e && startBoundaryCheck s e && endBoundaryCheck s e &&
  emptySegmentCheck r s e
example : allTriples postCheck = true := by native_decide

#eval allTriples postCheck

/-! ## Correctness -/

theorem correctness_thm (return_addr text_start text_end : Int) :
    Pre return_addr text_start text_end → Post_prop return_addr text_start text_end := by
  intro _
  exact ⟨in_range_thm return_addr text_start text_end,
    soundness_thm return_addr text_start text_end,
    completeness_thm return_addr text_start text_end,
    rejection_thm return_addr text_start text_end,
    start_boundary_thm text_start text_end,
    end_boundary_thm text_start text_end,
    empty_segment_thm return_addr text_start text_end⟩

/-! ## Imperative implementation -/

/-- Short-circuiting comparisons with an explicitly mutable result. -/
def safe_rop_check_imp (return_addr text_start text_end : Int) : Bool := Id.run do
  let mut accepted := false
  if text_start ≤ return_addr then
    if return_addr < text_end then
      accepted := true
  return accepted

/-! ## Imperative tests -/

example : safe_rop_check_imp 0x08048000 0x08048000 0x08049000 = true := by
  native_decide
example : safe_rop_check_imp 0x08048500 0x08048000 0x08049000 = true := by
  native_decide
example : safe_rop_check_imp 0xb7e90000 0x08048000 0x08049000 = false := by
  native_decide
example : safe_rop_check_imp 0x00000000 0x08048000 0x08049000 = false := by
  native_decide
example : safe_rop_check_imp 0x08049000 0x08048000 0x08049000 = false := by
  native_decide
example : safe_rop_check_imp (-3) (-5) 0 = true := by native_decide
example : safe_rop_check_imp 0 0 0 = false := by native_decide
example : safe_rop_check_imp 4 5 3 = false := by native_decide

#eval [safe_rop_check_imp 0x08048000 0x08048000 0x08049000,
       safe_rop_check_imp 0x08048500 0x08048000 0x08049000,
       safe_rop_check_imp 0xb7e90000 0x08048000 0x08049000,
       safe_rop_check_imp 0x00000000 0x08048000 0x08049000,
       safe_rop_check_imp 0x08049000 0x08048000 0x08049000]

-- Additional bounded evidence for functional/imperative agreement.
example : allTriples (fun r s e => safe_rop_check r s e == safe_rop_check_imp r s e) =
    true := by native_decide

/-! ## Functional/imperative equivalence -/

theorem equivalence_thm (return_addr text_start text_end : Int) :
    safe_rop_check return_addr text_start text_end =
      safe_rop_check_imp return_addr text_start text_end := by
  by_cases hLower : text_start ≤ return_addr <;>
    by_cases hUpper : return_addr < text_end <;>
    simp [safe_rop_check, safe_rop_check_imp, hLower, hUpper]

end «115_unsafeROPChain_safe»
end Agent
