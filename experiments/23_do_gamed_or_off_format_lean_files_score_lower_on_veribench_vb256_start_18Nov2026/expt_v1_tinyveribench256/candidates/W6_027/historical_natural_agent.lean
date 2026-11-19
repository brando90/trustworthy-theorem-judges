import Mathlib
namespace Agent

/-!
# Unsafe double-read: checking one value and returning another

Translation of the Python TOCTOU example from MIT 6.858's RLBox discussion.
`len1` is the checked first read; `len2` is the potentially attacker-modified
second read. The program deliberately does NOT check `len2` and does NOT freeze
the shared value. Python's unbounded signed integers are modelled by `Int`, and
`None` by `Option.none`. In particular, neither lengths nor buffer sizes are
silently restricted to nonnegative values.

The specification describes the bug, not a repaired program. It characterizes
both branches and exactly when a returned value exceeds the buffer size.
Bounded property-based tests are evidence only; all named theorems have separate
kernel-checked proofs.
-/

namespace UnsafeDoubleRead

/-! ## Functional implementation -/

def unsafe_double_read (len1 len2 buf_size : Int) : Option Int :=
  if len1 ≤ buf_size then some len2 else none

/-- Boolean rendition of the five assertions in Python's test harness. -/
def check (candidate : Int → Int → Int → Option Int) : Bool :=
  candidate 5 5 100 == some 5 &&
  candidate 5 999 100 == some 999 &&
  candidate 200 200 100 == none &&
  candidate 100 100 100 == some 100 &&
  candidate 50 0 100 == some 0

/-! ## Unit tests -/

example : unsafe_double_read 5 5 100 = some 5 := by native_decide
example : unsafe_double_read 5 999 100 = some 999 := by native_decide
example : unsafe_double_read 200 200 100 = none := by native_decide
example : unsafe_double_read 100 100 100 = some 100 := by native_decide
example : unsafe_double_read 50 0 100 = some 0 := by native_decide
example : check unsafe_double_read = true := by native_decide

-- There is no implicit nonnegativity check in the Python program.
example : unsafe_double_read (-5) (-99) (-1) = some (-99) := by native_decide
example : unsafe_double_read (-1) 7 (-2) = none := by native_decide
example : unsafe_double_read (-1) 0 (-1) = some 0 := by native_decide

#eval [unsafe_double_read 5 5 100, unsafe_double_read 5 999 100,
  unsafe_double_read 200 200 100, unsafe_double_read 100 100 100,
  unsafe_double_read 50 0 100]
#eval check unsafe_double_read
#eval if check unsafe_double_read then "All tests passed." else "Candidate failed tests"

/-! ## Precondition and properties -/

/-- Every triple of Python integers is admissible; the two reads may differ. -/
def Pre (_len1 _len2 _buf_size : Int) : Prop := True

/-- Acceptance is controlled solely by the first read, but returns the second. -/
def accepted_prop (len1 len2 buf_size : Int) : Prop :=
  unsafe_double_read len1 len2 buf_size = some len2 ↔ len1 ≤ buf_size

theorem accepted_thm (len1 len2 buf_size : Int) :
    accepted_prop len1 len2 buf_size := by
  by_cases h : len1 ≤ buf_size <;>
    simp [accepted_prop, unsafe_double_read, h]

/-- Rejection occurs exactly when the first read exceeds the buffer size. -/
def rejected_prop (len1 len2 buf_size : Int) : Prop :=
  unsafe_double_read len1 len2 buf_size = none ↔ buf_size < len1

theorem rejected_thm (len1 len2 buf_size : Int) :
    rejected_prop len1 len2 buf_size := by
  by_cases h : len1 ≤ buf_size
  · simp [rejected_prop, unsafe_double_read, h, not_lt.mpr h]
  · simp [rejected_prop, unsafe_double_read, h, lt_of_not_ge h]

/-- Any returned integer is exactly the second read, not a clipped value. -/
def returned_value_prop (len1 len2 buf_size : Int) : Prop :=
  match unsafe_double_read len1 len2 buf_size with
  | none => True
  | some result => result = len2

theorem returned_value_thm (len1 len2 buf_size : Int) :
    returned_value_prop len1 len2 buf_size := by
  by_cases h : len1 ≤ buf_size <;>
    simp [returned_value_prop, unsafe_double_read, h]

/-- If the two reads agree, every returned value satisfies the checked upper bound.
This states only the upper bound actually checked by Python, not nonnegativity. -/
def unchanged_read_safe_prop (len1 len2 buf_size : Int) : Prop :=
  len1 = len2 →
    match unsafe_double_read len1 len2 buf_size with
    | none => True
    | some result => result ≤ buf_size

theorem unchanged_read_safe_thm (len1 len2 buf_size : Int) :
    unchanged_read_safe_prop len1 len2 buf_size := by
  unfold unchanged_read_safe_prop
  intro hSame
  subst len2
  by_cases h : len1 ≤ buf_size <;> simp [unsafe_double_read, h]

/-- Exact characterization of the TOCTOU vulnerability: an OOB result is returned
iff the first read passes and the second read exceeds the buffer size. -/
def out_of_bounds_prop (len1 len2 buf_size : Int) : Prop :=
  (match unsafe_double_read len1 len2 buf_size with
   | none => False
   | some result => buf_size < result) ↔
    len1 ≤ buf_size ∧ buf_size < len2

theorem out_of_bounds_thm (len1 len2 buf_size : Int) :
    out_of_bounds_prop len1 len2 buf_size := by
  by_cases h : len1 ≤ buf_size <;>
    simp [out_of_bounds_prop, unsafe_double_read, h]

/-- A kernel-checked witness to the bug, in addition to the executable unit test. -/
theorem unsafe_counterexample_thm :
    unsafe_double_read 5 999 100 = some 999 ∧ (100 : Int) < 999 := by
  norm_num [unsafe_double_read]

/-! ## Post-condition -/

/-- Full behavior, including (rather than excluding) the unsafe case. -/
def Post_prop (len1 len2 buf_size : Int) : Prop :=
  accepted_prop len1 len2 buf_size ∧
  rejected_prop len1 len2 buf_size ∧
  returned_value_prop len1 len2 buf_size ∧
  unchanged_read_safe_prop len1 len2 buf_size ∧
  out_of_bounds_prop len1 len2 buf_size

/-! ## Bounded property-based tests

Each test checks the executable Boolean form of its named property directly
against the functional implementation. We exhaust all triples from a signed
small range together with larger values, including the original attack inputs.
The equal-read cases, both branches, equality boundary, negative integers, and
changed second reads all occur in this domain. No sampling precondition can
cause these tests to give up.
-/

def pbtInputs : List Int :=
  (List.range 13).map (fun n => (n : Int) - 6) ++ [-999, -100, 50, 100, 200, 999]

def boundedTriples (property : Int → Int → Int → Bool) : Bool :=
  pbtInputs.all fun len1 =>
    pbtInputs.all fun len2 =>
      pbtInputs.all fun buf_size => property len1 len2 buf_size

-- Executable counterparts of the five property propositions.
def acceptedCheck (len1 len2 buf_size : Int) : Bool :=
  decide (unsafe_double_read len1 len2 buf_size = some len2 ↔ len1 ≤ buf_size)

def rejectedCheck (len1 len2 buf_size : Int) : Bool :=
  decide (unsafe_double_read len1 len2 buf_size = none ↔ buf_size < len1)

def returnedValueCheck (len1 len2 buf_size : Int) : Bool :=
  match unsafe_double_read len1 len2 buf_size with
  | none => true
  | some result => decide (result = len2)

def unchangedReadSafeCheck (len1 len2 buf_size : Int) : Bool :=
  if len1 = len2 then
    match unsafe_double_read len1 len2 buf_size with
    | none => true
    | some result => decide (result ≤ buf_size)
  else true

def outOfBoundsCheck (len1 len2 buf_size : Int) : Bool :=
  (match unsafe_double_read len1 len2 buf_size with
   | none => false
   | some result => decide (buf_size < result)) ==
    decide (len1 ≤ buf_size ∧ buf_size < len2)

-- PBT for accepted_prop.
example : boundedTriples acceptedCheck = true := by native_decide
-- PBT for rejected_prop.
example : boundedTriples rejectedCheck = true := by native_decide
-- PBT for returned_value_prop.
example : boundedTriples returnedValueCheck = true := by native_decide
-- PBT for unchanged_read_safe_prop.
example : boundedTriples unchangedReadSafeCheck = true := by native_decide
-- PBT for out_of_bounds_prop.
example : boundedTriples outOfBoundsCheck = true := by native_decide

/-- Boolean conjunction corresponding to Post_prop. Pre is True for every input. -/
def postCheck (len1 len2 buf_size : Int) : Bool :=
  acceptedCheck len1 len2 buf_size &&
  rejectedCheck len1 len2 buf_size &&
  returnedValueCheck len1 len2 buf_size &&
  unchangedReadSafeCheck len1 len2 buf_size &&
  outOfBoundsCheck len1 len2 buf_size

-- PBT for the complete post-condition on all admissible bounded inputs.
example : boundedTriples postCheck = true := by native_decide
#eval boundedTriples postCheck

/-! ## Correctness -/

theorem correctness_thm (len1 len2 buf_size : Int) :
    Pre len1 len2 buf_size → Post_prop len1 len2 buf_size := by
  intro _
  exact ⟨accepted_thm len1 len2 buf_size,
    rejected_thm len1 len2 buf_size,
    returned_value_thm len1 len2 buf_size,
    unchanged_read_safe_thm len1 len2 buf_size,
    out_of_bounds_thm len1 len2 buf_size⟩

/-! ## Imperative implementation with mutable state -/

def unsafe_double_read_imp (len1 len2 buf_size : Int) : Option Int := Id.run do
  let mut result : Option Int := none
  if len1 ≤ buf_size then
    result := some len2
  return result

/-! ## Imperative tests -/

example : unsafe_double_read_imp 5 5 100 = some 5 := by native_decide
example : unsafe_double_read_imp 5 999 100 = some 999 := by native_decide
example : unsafe_double_read_imp 200 200 100 = none := by native_decide
example : unsafe_double_read_imp 100 100 100 = some 100 := by native_decide
example : unsafe_double_read_imp 50 0 100 = some 0 := by native_decide
example : unsafe_double_read_imp (-5) (-99) (-1) = some (-99) := by native_decide
example : unsafe_double_read_imp (-1) 7 (-2) = none := by native_decide
example : unsafe_double_read_imp (-1) 0 (-1) = some 0 := by native_decide
example : check unsafe_double_read_imp = true := by native_decide

#eval [unsafe_double_read_imp 5 5 100, unsafe_double_read_imp 5 999 100,
  unsafe_double_read_imp 200 200 100, unsafe_double_read_imp 100 100 100,
  unsafe_double_read_imp 50 0 100]
#eval check unsafe_double_read_imp

-- Bounded agreement test; the universal equivalence is proved below.
example : boundedTriples (fun len1 len2 buf_size =>
    decide (unsafe_double_read len1 len2 buf_size =
      unsafe_double_read_imp len1 len2 buf_size)) = true := by native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_eq_imperative_thm (len1 len2 buf_size : Int) :
    unsafe_double_read len1 len2 buf_size =
      unsafe_double_read_imp len1 len2 buf_size := by
  by_cases h : len1 ≤ buf_size <;>
    simp [unsafe_double_read, unsafe_double_read_imp, h]

end UnsafeDoubleRead
end Agent
