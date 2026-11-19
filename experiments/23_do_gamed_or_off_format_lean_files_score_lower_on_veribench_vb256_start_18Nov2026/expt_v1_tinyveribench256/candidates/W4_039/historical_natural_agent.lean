import Mathlib
namespace Agent

/-!
# Safe TLS padding oracle

Translation of the Python TLS padding-oracle mitigation. The response is the
integer 0 exactly when both checks pass, and the integer 1 for every failure.
Only the response code is modeled: the indistinguishability claim is about
that observation, not about timing or other implementation side channels.

All Boolean inputs are admissible. The bounded property-based tests enumerate
the entire Boolean domain, including all pairs of records for the relational
indistinguishability property. Named proofs use kernel-checked reasoning;
`native_decide` is used only for executable test examples.
-/

namespace SafePaddingOracle

/-- The Python integer response: acceptance is 0; every rejection is 1. -/
def safe_padding_oracle (padding_valid mac_valid : Bool) : Int :=
  if padding_valid && mac_valid then 0 else 1

/-- Executable translation of the six assertions in Python's `check`. -/
def check (candidate : Bool → Bool → Int) : Bool :=
  decide (candidate true true = 0) &&
  decide (candidate false true = candidate true false) &&
  decide (candidate true false = 1) &&
  decide (candidate false false = 1) &&
  (decide (candidate false true = candidate true false) &&
    decide (candidate true false = candidate false false)) &&
  decide (candidate true true ≠ candidate false true)

-- Unit tests: each assertion in the supplied Python check.
example : safe_padding_oracle true true = 0 := by native_decide
example : safe_padding_oracle false true =
    safe_padding_oracle true false := by native_decide
example : safe_padding_oracle true false = 1 := by native_decide
example : safe_padding_oracle false false = 1 := by native_decide
example : safe_padding_oracle false true = safe_padding_oracle true false ∧
    safe_padding_oracle true false = safe_padding_oracle false false := by
  native_decide
example : safe_padding_oracle true true ≠
    safe_padding_oracle false true := by native_decide
example : check safe_padding_oracle = true := by native_decide

#eval safe_padding_oracle true true
#eval safe_padding_oracle false true
#eval safe_padding_oracle true false
#eval safe_padding_oracle false false
#eval check safe_padding_oracle
#eval if check safe_padding_oracle then "All tests passed." else "Candidate failed tests"

/-- No restriction beyond the two Boolean argument types. -/
def Pre (_padding_valid _mac_valid : Bool) : Prop := True

/-- Success occurs if and only if both checks pass. -/
def acceptance_prop (padding_valid mac_valid : Bool) : Prop :=
  safe_padding_oracle padding_valid mac_valid = 0 ↔
    padding_valid = true ∧ mac_valid = true

theorem acceptance_thm (padding_valid mac_valid : Bool) :
    acceptance_prop padding_valid mac_valid := by
  cases padding_valid <;> cases mac_valid <;>
    simp [acceptance_prop, safe_padding_oracle]

/-- Padding failure and MAC failure have the same response, regardless of
whether the other check succeeds. This includes assertion 2 of `check`. -/
def padding_mac_failure_prop (padding_valid mac_valid : Bool) : Prop :=
  safe_padding_oracle false mac_valid =
    safe_padding_oracle padding_valid false

theorem padding_mac_failure_thm (padding_valid mac_valid : Bool) :
    padding_mac_failure_prop padding_valid mac_valid := by
  cases padding_valid <;> cases mac_valid <;>
    simp [padding_mac_failure_prop, safe_padding_oracle]

/-- A bad MAC always gives the generic error, including assertion 3. -/
def bad_mac_prop (padding_valid : Bool) : Prop :=
  safe_padding_oracle padding_valid false = 1

theorem bad_mac_thm (padding_valid : Bool) : bad_mac_prop padding_valid := by
  cases padding_valid <;> simp [bad_mac_prop, safe_padding_oracle]

/-- Every unsuccessful record gives 1, including the both-invalid case. -/
def failure_prop (padding_valid mac_valid : Bool) : Prop :=
  (padding_valid && mac_valid) = false →
    safe_padding_oracle padding_valid mac_valid = 1

theorem failure_thm (padding_valid mac_valid : Bool) :
    failure_prop padding_valid mac_valid := by
  cases padding_valid <;> cases mac_valid <;>
    simp [failure_prop, safe_padding_oracle]

/-- Any two failing records have identical observable responses. This covers
all pairs among padding-only, MAC-only, and simultaneous failures. -/
def indistinguishability_prop (p m q n : Bool) : Prop :=
  (p && m) = false → (q && n) = false →
    safe_padding_oracle p m = safe_padding_oracle q n

theorem indistinguishability_thm (p m q n : Bool) :
    indistinguishability_prop p m q n := by
  intro hp hq
  exact (failure_thm p m hp).trans (failure_thm q n hq).symm

/-- Acceptance remains distinguishable from every failure. -/
def success_ne_failure_prop (padding_valid mac_valid : Bool) : Prop :=
  (padding_valid && mac_valid) = false →
    safe_padding_oracle true true ≠
      safe_padding_oracle padding_valid mac_valid

theorem success_ne_failure_thm (padding_valid mac_valid : Bool) :
    success_ne_failure_prop padding_valid mac_valid := by
  cases padding_valid <;> cases mac_valid <;>
    simp [success_ne_failure_prop, safe_padding_oracle]

/-- The translated Python assertion suite passes; this is a kernel proof. -/
theorem check_thm : check safe_padding_oracle = true := by
  decide

/-- All guarantees, including the original assertion suite and the relational
comparison with every other record. -/
def Post_prop (padding_valid mac_valid : Bool) : Prop :=
  acceptance_prop padding_valid mac_valid ∧
  padding_mac_failure_prop padding_valid mac_valid ∧
  bad_mac_prop padding_valid ∧
  failure_prop padding_valid mac_valid ∧
  (∀ q n : Bool, indistinguishability_prop padding_valid mac_valid q n) ∧
  success_ne_failure_prop padding_valid mac_valid ∧
  check safe_padding_oracle = true

/-! ## Exhaustive bounded property-based tests

These are executable Boolean versions of each property, not theorem proofs.
The two-element input list is exhaustive rather than a random sample.
-/

def boolInputs : List Bool := [false, true]

def allInputs (test : Bool → Bool → Bool) : Bool :=
  boolInputs.all (fun p => boolInputs.all (fun m => test p m))

-- PBT: acceptance_prop, over all four input pairs.
example : allInputs (fun p m =>
    (safe_padding_oracle p m == 0) == (p && m)) = true := by
  native_decide

-- PBT: padding_mac_failure_prop, including both-invalid records.
example : allInputs (fun p m =>
    safe_padding_oracle false m == safe_padding_oracle p false) = true := by
  native_decide

-- PBT: bad_mac_prop, over both padding outcomes.
example : boolInputs.all (fun p =>
    safe_padding_oracle p false == 1) = true := by
  native_decide

-- PBT: failure_prop. The first disjunct expresses the implication's guard.
example : allInputs (fun p m =>
    (p && m) || (safe_padding_oracle p m == 1)) = true := by
  native_decide

-- PBT: indistinguishability_prop, over all sixteen pairs of records.
example : allInputs (fun p m => allInputs (fun q n =>
    (p && m) || (q && n) ||
      (safe_padding_oracle p m == safe_padding_oracle q n))) = true := by
  native_decide

-- PBT: success_ne_failure_prop, for every potentially failing record.
example : allInputs (fun p m =>
    (p && m) ||
      (safe_padding_oracle true true != safe_padding_oracle p m)) = true := by
  native_decide

/-- Executable Boolean form of the complete postcondition. -/
def post_test (p m : Bool) : Bool :=
  ((safe_padding_oracle p m == 0) == (p && m)) &&
  (safe_padding_oracle false m == safe_padding_oracle p false) &&
  (safe_padding_oracle p false == 1) &&
  ((p && m) || (safe_padding_oracle p m == 1)) &&
  allInputs (fun q n =>
    (p && m) || (q && n) ||
      (safe_padding_oracle p m == safe_padding_oracle q n)) &&
  ((p && m) ||
    (safe_padding_oracle true true != safe_padding_oracle p m)) &&
  check safe_padding_oracle

-- PBT: Post_prop. Pre is True, so no inputs are filtered out.
example : allInputs post_test = true := by native_decide
#eval allInputs post_test

/-- Correctness on the entire admissible input domain. -/
theorem correctness (padding_valid mac_valid : Bool) :
    Pre padding_valid mac_valid → Post_prop padding_valid mac_valid := by
  intro _
  exact ⟨acceptance_thm padding_valid mac_valid,
    padding_mac_failure_thm padding_valid mac_valid,
    bad_mac_thm padding_valid,
    failure_thm padding_valid mac_valid,
    fun q n => indistinguishability_thm padding_valid mac_valid q n,
    success_ne_failure_thm padding_valid mac_valid,
    check_thm⟩

/-- Mutable-state version: start with the generic failure code, and overwrite
it only when both checks pass. -/
def safe_padding_oracle_imperative (padding_valid mac_valid : Bool) : Int :=
  Id.run do
    let mut response : Int := 1
    if padding_valid && mac_valid then
      response := 0
    return response

-- Imperative unit tests and the complete translated Python check.
example : safe_padding_oracle_imperative true true = 0 := by native_decide
example : safe_padding_oracle_imperative false true = 1 := by native_decide
example : safe_padding_oracle_imperative true false = 1 := by native_decide
example : safe_padding_oracle_imperative false false = 1 := by native_decide
example : check safe_padding_oracle_imperative = true := by native_decide
#eval check safe_padding_oracle_imperative

-- Exhaustive executable agreement test, in addition to the proof below.
example : allInputs (fun p m =>
    safe_padding_oracle p m == safe_padding_oracle_imperative p m) = true := by
  native_decide

/-- Pointwise functional/imperative equivalence for all inputs. -/
theorem functional_eq_imperative (padding_valid mac_valid : Bool) :
    safe_padding_oracle padding_valid mac_valid =
      safe_padding_oracle_imperative padding_valid mac_valid := by
  cases padding_valid <;> cases mac_valid <;> rfl

end SafePaddingOracle
end Agent
