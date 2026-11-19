import Mathlib
namespace Agent

/-!
# Unsafe TLS padding oracle

Translation of the abstract padding oracle from MIT 6.858 Lecture 14.
The response codes are 0 (success), 1 (bad padding), and 2 (bad MAC).
Padding is checked first, so invalid padding hides the MAC result but is
itself distinguishable from a MAC failure. This models the error-code leak,
not cryptography or a concrete plaintext-recovery algorithm.

The Python integer results are represented by `Nat`: all results are the
nonnegative constants 0, 1, and 2. Both Boolean inputs are unrestricted.
Property-based tests exhaust the entire four-element input domain; named
proofs are checked by the kernel independently of these executable tests.
-/

namespace UnsafePaddingOracle

/-! ## Functional implementation and Python assertion harness -/

def unsafe_padding_oracle (padding_valid mac_valid : Bool) : Nat :=
  if !padding_valid then 1
  else if !mac_valid then 2
  else 0

/-- Boolean counterpart of the conjunction of assertions in Python `check`.
It is true exactly when all assertions pass. -/
def check (candidate : Bool → Bool → Nat) : Bool :=
  (candidate true true == 0) &&
  (candidate false true == 1) &&
  (candidate true false == 2) &&
  (candidate false true != candidate true false) &&
  (candidate false false == 1) &&
  (candidate false true != 0) &&
  (candidate true false != 0)

/-! ## Unit tests: every assertion in the source -/

example : unsafe_padding_oracle true true = 0 := by native_decide
example : unsafe_padding_oracle false true = 1 := by native_decide
example : unsafe_padding_oracle true false = 2 := by native_decide
example : unsafe_padding_oracle false true ≠ unsafe_padding_oracle true false := by
  native_decide
example : unsafe_padding_oracle false false = 1 := by native_decide
example : unsafe_padding_oracle false true ≠ 0 := by native_decide
example : unsafe_padding_oracle true false ≠ 0 := by native_decide
example : check unsafe_padding_oracle = true := by native_decide

#eval unsafe_padding_oracle true true
#eval unsafe_padding_oracle false true
#eval unsafe_padding_oracle true false
#eval unsafe_padding_oracle false false
#eval check unsafe_padding_oracle
#eval if check unsafe_padding_oracle then "All tests passed." else "Candidate failed tests"

/-! ## Precondition and proved properties -/

/-- The source admits every pair of Boolean inputs. -/
def Pre (_padding_valid _mac_valid : Bool) : Prop := True

/-- Success occurs exactly when both checks pass. -/
def success_prop (padding_valid mac_valid : Bool) : Prop :=
  unsafe_padding_oracle padding_valid mac_valid = 0 ↔
    padding_valid = true ∧ mac_valid = true

theorem success_thm (padding_valid mac_valid : Bool) :
    success_prop padding_valid mac_valid := by
  unfold success_prop
  cases padding_valid <;> cases mac_valid <;> decide

/-- Code 1 identifies invalid padding, regardless of the MAC. -/
def bad_padding_prop (padding_valid mac_valid : Bool) : Prop :=
  unsafe_padding_oracle padding_valid mac_valid = 1 ↔ padding_valid = false

theorem bad_padding_thm (padding_valid mac_valid : Bool) :
    bad_padding_prop padding_valid mac_valid := by
  unfold bad_padding_prop
  cases padding_valid <;> cases mac_valid <;> decide

/-- Code 2 identifies a MAC failure only after padding has passed. -/
def bad_mac_prop (padding_valid mac_valid : Bool) : Prop :=
  unsafe_padding_oracle padding_valid mac_valid = 2 ↔
    padding_valid = true ∧ mac_valid = false

theorem bad_mac_thm (padding_valid mac_valid : Bool) :
    bad_mac_prop padding_valid mac_valid := by
  unfold bad_mac_prop
  cases padding_valid <;> cases mac_valid <;> decide

/-- The observable vulnerability: padding and MAC failures have distinct codes. -/
def distinguishable_prop (mac_valid : Bool) : Prop :=
  unsafe_padding_oracle false mac_valid ≠ unsafe_padding_oracle true false

theorem distinguishable_thm (mac_valid : Bool) : distinguishable_prop mac_valid := by
  unfold distinguishable_prop
  cases mac_valid <;> decide

/-- Invalid padding short-circuits, including when the MAC is also invalid. -/
def short_circuit_prop (mac_valid : Bool) : Prop :=
  unsafe_padding_oracle false mac_valid = 1

theorem short_circuit_thm (mac_valid : Bool) : short_circuit_prop mac_valid := by
  unfold short_circuit_prop
  cases mac_valid <;> decide

/-- Any failure, including simultaneous failures, yields a nonzero code. -/
def failure_nonzero_prop (padding_valid mac_valid : Bool) : Prop :=
  (padding_valid = false ∨ mac_valid = false) →
    unsafe_padding_oracle padding_valid mac_valid ≠ 0

theorem failure_nonzero_thm (padding_valid mac_valid : Bool) :
    failure_nonzero_prop padding_valid mac_valid := by
  unfold failure_nonzero_prop
  cases padding_valid <;> cases mac_valid <;> decide

/-- There are no response codes other than the three documented ones. -/
def response_range_prop (padding_valid mac_valid : Bool) : Prop :=
  unsafe_padding_oracle padding_valid mac_valid = 0 ∨
  unsafe_padding_oracle padding_valid mac_valid = 1 ∨
  unsafe_padding_oracle padding_valid mac_valid = 2

theorem response_range_thm (padding_valid mac_valid : Bool) :
    response_range_prop padding_valid mac_valid := by
  unfold response_range_prop
  cases padding_valid <;> cases mac_valid <;> decide

/-- Kernel-checked counterpart of the source's final assertion. -/
theorem check_thm : check unsafe_padding_oracle = true := by
  decide

/-! ## Postcondition -/

def Post_prop (padding_valid mac_valid : Bool) : Prop :=
  success_prop padding_valid mac_valid ∧
  bad_padding_prop padding_valid mac_valid ∧
  bad_mac_prop padding_valid mac_valid ∧
  distinguishable_prop mac_valid ∧
  short_circuit_prop mac_valid ∧
  failure_nonzero_prop padding_valid mac_valid ∧
  response_range_prop padding_valid mac_valid ∧
  check unsafe_padding_oracle = true

/-! ## Exhaustive property-based tests

These are bounded PBTs over *all* inputs, not selected examples. `decide`
produces executable Boolean forms of the expanded properties, so no
`Decidable` instances for the named specification predicates are needed.
-/

def allInputs : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

-- PBT for success_prop.
example : allInputs.all (fun x => decide
    (unsafe_padding_oracle x.1 x.2 = 0 ↔ x.1 = true ∧ x.2 = true)) = true := by
  native_decide

-- PBT for bad_padding_prop.
example : allInputs.all (fun x => decide
    (unsafe_padding_oracle x.1 x.2 = 1 ↔ x.1 = false)) = true := by
  native_decide

-- PBT for bad_mac_prop.
example : allInputs.all (fun x => decide
    (unsafe_padding_oracle x.1 x.2 = 2 ↔ x.1 = true ∧ x.2 = false)) = true := by
  native_decide

-- PBT for distinguishable_prop: both possible MAC values on the padding-fail path.
example : [false, true].all (fun m => decide
    (unsafe_padding_oracle false m ≠ unsafe_padding_oracle true false)) = true := by
  native_decide

-- PBT for short_circuit_prop.
example : [false, true].all (fun m => decide
    (unsafe_padding_oracle false m = 1)) = true := by
  native_decide

-- PBT for failure_nonzero_prop, with the original failure hypothesis intact.
example : allInputs.all (fun x => decide
    ((x.1 = false ∨ x.2 = false) → unsafe_padding_oracle x.1 x.2 ≠ 0)) = true := by
  native_decide

-- PBT for response_range_prop.
example : allInputs.all (fun x => decide
    (unsafe_padding_oracle x.1 x.2 = 0 ∨
     unsafe_padding_oracle x.1 x.2 = 1 ∨
     unsafe_padding_oracle x.1 x.2 = 2)) = true := by
  native_decide

-- PBT for the full Post_prop, expanded to its executable form. The final
-- conjunct also tests the source assertion harness proved in check_thm.
example : allInputs.all (fun x => decide
    ((unsafe_padding_oracle x.1 x.2 = 0 ↔ x.1 = true ∧ x.2 = true) ∧
     (unsafe_padding_oracle x.1 x.2 = 1 ↔ x.1 = false) ∧
     (unsafe_padding_oracle x.1 x.2 = 2 ↔ x.1 = true ∧ x.2 = false) ∧
     unsafe_padding_oracle false x.2 ≠ unsafe_padding_oracle true false ∧
     unsafe_padding_oracle false x.2 = 1 ∧
     ((x.1 = false ∨ x.2 = false) → unsafe_padding_oracle x.1 x.2 ≠ 0) ∧
     (unsafe_padding_oracle x.1 x.2 = 0 ∨
      unsafe_padding_oracle x.1 x.2 = 1 ∨
      unsafe_padding_oracle x.1 x.2 = 2) ∧
     check unsafe_padding_oracle = true)) = true := by
  native_decide

#eval allInputs.map (fun x => (x, unsafe_padding_oracle x.1 x.2))

/-! ## Correctness -/

theorem correctness_thm (padding_valid mac_valid : Bool) :
    Pre padding_valid mac_valid → Post_prop padding_valid mac_valid := by
  intro _
  exact ⟨success_thm padding_valid mac_valid,
    bad_padding_thm padding_valid mac_valid,
    bad_mac_thm padding_valid mac_valid,
    distinguishable_thm mac_valid,
    short_circuit_thm mac_valid,
    failure_nonzero_thm padding_valid mac_valid,
    response_range_thm padding_valid mac_valid,
    check_thm⟩

/-! ## Imperative implementation with mutable response state -/

def unsafe_padding_oracle_imp (padding_valid mac_valid : Bool) : Nat := Id.run do
  let mut response : Nat := 0
  if !padding_valid then
    response := 1
  else if !mac_valid then
    response := 2
  return response

/-! ## Imperative tests -/

example : unsafe_padding_oracle_imp true true = 0 := by native_decide
example : unsafe_padding_oracle_imp false true = 1 := by native_decide
example : unsafe_padding_oracle_imp true false = 2 := by native_decide
example : unsafe_padding_oracle_imp false true ≠ unsafe_padding_oracle_imp true false := by
  native_decide
example : unsafe_padding_oracle_imp false false = 1 := by native_decide
example : unsafe_padding_oracle_imp false true ≠ 0 := by native_decide
example : unsafe_padding_oracle_imp true false ≠ 0 := by native_decide
example : check unsafe_padding_oracle_imp = true := by native_decide

-- Exhaustive PBT for functional/imperative equivalence.
example : allInputs.all (fun x =>
    unsafe_padding_oracle x.1 x.2 == unsafe_padding_oracle_imp x.1 x.2) = true := by
  native_decide

#eval allInputs.map (fun x => (x, unsafe_padding_oracle_imp x.1 x.2))
#eval check unsafe_padding_oracle_imp

/-! ## Kernel-checked equivalence for every input -/

theorem functional_imperative_equiv_thm (padding_valid mac_valid : Bool) :
    unsafe_padding_oracle padding_valid mac_valid =
      unsafe_padding_oracle_imp padding_valid mac_valid := by
  cases padding_valid <;> cases mac_valid <;> rfl

end UnsafePaddingOracle
end Agent
