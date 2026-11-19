import Mathlib
namespace Agent

/-!
# Safe heap address validation

Translation of the Python `safe_heap_validate` function and its test driver.
An address is accepted exactly when it belongs to the half-open heap interval
`[heap_base, heap_base + heap_size)`. Lean `Int` models Python's unbounded
integers: negative addresses and bases are permitted, and a nonpositive size
makes the interval empty. No unsigned arithmetic or overflow is introduced.

The file proves exact acceptance and rejection specifications, empty-region
and boundary behavior, correctness, and equivalence with a mutable-state
implementation. Bounded property-based tests supplement, but do not replace,
the kernel-checked proofs.
-/

namespace UnsafeHeapSprayingSafe

/-- Functional translation of Python's chained integer comparison. -/
def safe_heap_validate (addr heap_base heap_size : Int) : Bool :=
  decide (heap_base ≤ addr ∧ addr < heap_base + heap_size)

-- The six original unit tests.
example : safe_heap_validate 120 100 50 = true := by native_decide
example : safe_heap_validate 100 100 50 = true := by native_decide
example : safe_heap_validate 149 100 50 = true := by native_decide
example : safe_heap_validate 0 100 50 = false := by native_decide
example : safe_heap_validate 150 100 50 = false := by native_decide
example : safe_heap_validate 200 100 50 = false := by native_decide

-- Additional tests exercising the unrestricted integer domain.
example : safe_heap_validate (-5) (-10) 10 = true := by native_decide
example : safe_heap_validate 0 (-10) 10 = false := by native_decide
example : safe_heap_validate 100 100 0 = false := by native_decide
example : safe_heap_validate 95 100 (-10) = false := by native_decide

/-- Executable counterpart of the Python `check` driver. -/
def check : IO Unit := do
  unless safe_heap_validate 120 100 50 do
    throw (IO.userError "valid addr rejected")
  unless safe_heap_validate 100 100 50 do
    throw (IO.userError "lower bound rejected")
  unless safe_heap_validate 149 100 50 do
    throw (IO.userError "upper bound rejected")
  if safe_heap_validate 0 100 50 then
    throw (IO.userError "addr below heap accepted")
  if safe_heap_validate 150 100 50 then
    throw (IO.userError "addr at upper limit accepted")
  if safe_heap_validate 200 100 50 then
    throw (IO.userError "addr above heap accepted")
  IO.println "All tests passed."

#eval check

/-- Python accepts all integer arguments; positivity is not a precondition. -/
def Pre (_addr _heap_base _heap_size : Int) : Prop := True

/-- Exact acceptance: both safety and completeness for the half-open interval. -/
def validation_prop (addr heap_base heap_size : Int) : Prop :=
  safe_heap_validate addr heap_base heap_size = true ↔
    heap_base ≤ addr ∧ addr < heap_base + heap_size

theorem validation_thm (addr heap_base heap_size : Int) :
    validation_prop addr heap_base heap_size := by
  simp [validation_prop, safe_heap_validate]

/-- Exact rejection, covering both the lower and upper invalid regions. -/
def rejection_prop (addr heap_base heap_size : Int) : Prop :=
  safe_heap_validate addr heap_base heap_size = false ↔
    addr < heap_base ∨ heap_base + heap_size ≤ addr

theorem rejection_thm (addr heap_base heap_size : Int) :
    rejection_prop addr heap_base heap_size := by
  simp [rejection_prop, safe_heap_validate]
  omega

/-- Zero and negative sizes admit no addresses, regardless of the base. -/
def empty_heap_prop (addr heap_base heap_size : Int) : Prop :=
  heap_size ≤ 0 → safe_heap_validate addr heap_base heap_size = false

theorem empty_heap_thm (addr heap_base heap_size : Int) :
    empty_heap_prop addr heap_base heap_size := by
  simp [empty_heap_prop, safe_heap_validate]
  omega

/-- The inclusive lower endpoint is valid exactly for positive sizes. -/
def lower_boundary_prop (heap_base heap_size : Int) : Prop :=
  safe_heap_validate heap_base heap_base heap_size = true ↔ 0 < heap_size

theorem lower_boundary_thm (heap_base heap_size : Int) :
    lower_boundary_prop heap_base heap_size := by
  simp [lower_boundary_prop, safe_heap_validate]

/-- The exclusive upper endpoint is always rejected. -/
def upper_boundary_prop (heap_base heap_size : Int) : Prop :=
  safe_heap_validate (heap_base + heap_size) heap_base heap_size = false

theorem upper_boundary_thm (heap_base heap_size : Int) :
    upper_boundary_prop heap_base heap_size := by
  simp [upper_boundary_prop, safe_heap_validate]

/-- For a positive integer size, the final address before the endpoint is valid. -/
def last_address_prop (heap_base heap_size : Int) : Prop :=
  0 < heap_size →
    safe_heap_validate (heap_base + heap_size - 1) heap_base heap_size = true

theorem last_address_thm (heap_base heap_size : Int) :
    last_address_prop heap_base heap_size := by
  simp [last_address_prop, safe_heap_validate]
  omega

/-- The post-condition combines the exact contract and its boundary guarantees. -/
def Post_prop (addr heap_base heap_size : Int) : Prop :=
  validation_prop addr heap_base heap_size ∧
  rejection_prop addr heap_base heap_size ∧
  empty_heap_prop addr heap_base heap_size ∧
  lower_boundary_prop heap_base heap_size ∧
  upper_boundary_prop heap_base heap_size ∧
  last_address_prop heap_base heap_size

/-! ## Bounded property-based tests

Every integer from -20 through 20 is sampled. Ternary properties are tested
on all 41^3 triples, and binary properties on all 41^2 pairs. These samples
include negative, zero, and positive sizes and bases. Implications use an
executable conditional rather than filtering away inadmissible samples.
Each checker below is the Boolean form of the correspondingly named property.
-/

def pbtInts : List Int :=
  (List.range 41).map (fun n => (n : Int) - 20)

def allPairs (p : Int → Int → Bool) : Bool :=
  pbtInts.all (fun b => pbtInts.all (fun s => p b s))

def allTriples (p : Int → Int → Int → Bool) : Bool :=
  pbtInts.all (fun a => pbtInts.all (fun b => pbtInts.all (fun s => p a b s)))

def validation_check (a b s : Int) : Bool :=
  safe_heap_validate a b s == (decide (b ≤ a) && decide (a < b + s))

def rejection_check (a b s : Int) : Bool :=
  (safe_heap_validate a b s == false) ==
    (decide (a < b) || decide (b + s ≤ a))

def empty_heap_check (a b s : Int) : Bool :=
  if s ≤ 0 then safe_heap_validate a b s == false else true

def lower_boundary_check (b s : Int) : Bool :=
  safe_heap_validate b b s == decide (0 < s)

def upper_boundary_check (b s : Int) : Bool :=
  safe_heap_validate (b + s) b s == false

def last_address_check (b s : Int) : Bool :=
  if 0 < s then safe_heap_validate (b + s - 1) b s else true

def post_check (a b s : Int) : Bool :=
  validation_check a b s && rejection_check a b s && empty_heap_check a b s &&
  lower_boundary_check b s && upper_boundary_check b s && last_address_check b s

-- PBT for validation_prop.
example : allTriples validation_check = true := by native_decide
-- PBT for rejection_prop.
example : allTriples rejection_check = true := by native_decide
-- PBT for empty_heap_prop.
example : allTriples empty_heap_check = true := by native_decide
-- PBT for lower_boundary_prop.
example : allPairs lower_boundary_check = true := by native_decide
-- PBT for upper_boundary_prop.
example : allPairs upper_boundary_check = true := by native_decide
-- PBT for last_address_prop.
example : allPairs last_address_check = true := by native_decide
-- PBT for the complete Post_prop.
example : allTriples post_check = true := by native_decide

#eval allTriples post_check

/-- All integer inputs satisfy the post-condition under the unrestricted Pre. -/
theorem correctness_thm (addr heap_base heap_size : Int) :
    Pre addr heap_base heap_size → Post_prop addr heap_base heap_size := by
  intro _
  exact ⟨validation_thm addr heap_base heap_size,
    rejection_thm addr heap_base heap_size,
    empty_heap_thm addr heap_base heap_size,
    lower_boundary_thm heap_base heap_size,
    upper_boundary_thm heap_base heap_size,
    last_address_thm heap_base heap_size⟩

/-- Mutable-state version, short-circuiting the comparisons as in Python. -/
def safe_heap_validate_imperative (addr heap_base heap_size : Int) : Bool :=
  Id.run do
    let mut valid := false
    if heap_base ≤ addr then
      if addr < heap_base + heap_size then
        valid := true
    return valid

-- Imperative unit tests, including all six original assertions.
example : safe_heap_validate_imperative 120 100 50 = true := by native_decide
example : safe_heap_validate_imperative 100 100 50 = true := by native_decide
example : safe_heap_validate_imperative 149 100 50 = true := by native_decide
example : safe_heap_validate_imperative 0 100 50 = false := by native_decide
example : safe_heap_validate_imperative 150 100 50 = false := by native_decide
example : safe_heap_validate_imperative 200 100 50 = false := by native_decide
example : safe_heap_validate_imperative (-5) (-10) 10 = true := by native_decide
example : safe_heap_validate_imperative 100 100 0 = false := by native_decide
example : safe_heap_validate_imperative 95 100 (-10) = false := by native_decide

#eval [safe_heap_validate_imperative 120 100 50,
  safe_heap_validate_imperative 100 100 50,
  safe_heap_validate_imperative 149 100 50,
  safe_heap_validate_imperative 0 100 50,
  safe_heap_validate_imperative 150 100 50,
  safe_heap_validate_imperative 200 100 50]

-- Additional bounded evidence for equivalence (the proof is below).
example : allTriples (fun a b s =>
    safe_heap_validate a b s == safe_heap_validate_imperative a b s) = true := by
  native_decide

/-- Functional and imperative validators agree for all Python integer inputs. -/
theorem functional_eq_imperative_thm (addr heap_base heap_size : Int) :
    safe_heap_validate addr heap_base heap_size =
      safe_heap_validate_imperative addr heap_base heap_size := by
  by_cases hlo : heap_base ≤ addr
  · by_cases hhi : addr < heap_base + heap_size
    · simp [safe_heap_validate, safe_heap_validate_imperative, hlo, hhi]
    · simp [safe_heap_validate, safe_heap_validate_imperative, hlo, hhi]
  · simp [safe_heap_validate, safe_heap_validate_imperative, hlo]

end UnsafeHeapSprayingSafe
end Agent
