import Mathlib
namespace Agent

/-!
# Safe cgroup memory allocation

A direct model of the Python test `current_bytes + request_bytes <= limit_bytes`.
`Int` preserves Python's unbounded signed-integer arithmetic, including negative
inputs: the function does not validate that its arguments describe physical
memory sizes. Admission and rejection are characterized exactly. Additional
properties cover the boundary, zero requests, zero limits for nonnegative sizes,
and monotonicity in usage, request size, and the cap.

The supplied Python assertions are checked below. Exhaustive bounded PBTs include
negative inputs and check every stated property and their postcondition. These
executable tests are separate from the kernel-checked general proofs.
-/

namespace UnsafeCgroupMemorySafe

-- Functional implementation.
def safe_cgroup_memory (current_bytes request_bytes limit_bytes : Int) : Bool :=
  decide (current_bytes + request_bytes ≤ limit_bytes)

-- A Boolean rendering of the Python assertion-based test harness.
def check (candidate : Int → Int → Int → Bool) : Bool :=
  candidate 100 50 200 == true &&
  candidate 100 100 200 == true &&
  candidate 100 101 200 == false &&
  candidate 100 200 150 == false &&
  candidate 0 200 200 == true &&
  candidate 0 201 200 == false &&
  candidate 0 1 0 == false &&
  candidate 0 0 0 == true &&
  candidate 0 (10 ^ 9) (10 ^ 9) == true &&
  candidate 1 (10 ^ 9) (10 ^ 9) == false

-- Unit tests: all ten original assertions.
example : safe_cgroup_memory 100 50 200 = true := by native_decide
example : safe_cgroup_memory 100 100 200 = true := by native_decide
example : safe_cgroup_memory 100 101 200 = false := by native_decide
example : safe_cgroup_memory 100 200 150 = false := by native_decide
example : safe_cgroup_memory 0 200 200 = true := by native_decide
example : safe_cgroup_memory 0 201 200 = false := by native_decide
example : safe_cgroup_memory 0 1 0 = false := by native_decide
example : safe_cgroup_memory 0 0 0 = true := by native_decide
example : safe_cgroup_memory 0 (10 ^ 9) (10 ^ 9) = true := by native_decide
example : safe_cgroup_memory 1 (10 ^ 9) (10 ^ 9) = false := by native_decide
example : check safe_cgroup_memory = true := by native_decide
#eval check safe_cgroup_memory
#eval safe_cgroup_memory 100 101 200
-- Signed inputs are preserved, not clamped or rejected.
example : safe_cgroup_memory 10 (-5) 5 = true := by native_decide
example : safe_cgroup_memory (-10) 3 (-7) = true := by native_decide

-- Python has no input validation: all triples of integers are admissible.
def Pre (_current_bytes _request_bytes _limit_bytes : Int) : Prop := True

-- Soundness and completeness of admission, not merely one direction.
def admission_prop (c r l : Int) : Prop :=
  safe_cgroup_memory c r l = true ↔ c + r ≤ l

theorem admission_thm (c r l : Int) : admission_prop c r l := by
  simp [admission_prop, safe_cgroup_memory]

-- Rejection occurs exactly when the resulting usage would exceed the cap.
def rejection_prop (c r l : Int) : Prop :=
  safe_cgroup_memory c r l = false ↔ l < c + r

theorem rejection_thm (c r l : Int) : rejection_prop c r l := by
  simp [rejection_prop, safe_cgroup_memory]

-- Equality is permitted, including a zero request under a zero cap.
def exact_limit_prop (c r : Int) : Prop :=
  safe_cgroup_memory c r (c + r) = true

theorem exact_limit_thm (c r : Int) : exact_limit_prop c r := by
  simp [exact_limit_prop, safe_cgroup_memory]

-- A zero request does not hide existing over-limit usage.
def zero_request_prop (c l : Int) : Prop :=
  safe_cgroup_memory c 0 l = decide (c ≤ l)

theorem zero_request_thm (c l : Int) : zero_request_prop c l := by
  simp [zero_request_prop, safe_cgroup_memory]

-- This physical-memory interpretation explicitly needs nonnegative sizes.
-- It is a conditional property, not a restriction on the function's domain.
def zero_limit_prop (c r : Int) : Prop :=
  0 ≤ c → 0 ≤ r →
    (safe_cgroup_memory c r 0 = true ↔ c = 0 ∧ r = 0)

theorem zero_limit_thm (c r : Int) : zero_limit_prop c r := by
  unfold zero_limit_prop
  simp only [safe_cgroup_memory, decide_eq_true_eq]
  omega

-- Reducing an admitted request preserves admission.
def request_monotone_prop (c smaller r l : Int) : Prop :=
  smaller ≤ r → safe_cgroup_memory c r l = true →
    safe_cgroup_memory c smaller l = true

theorem request_monotone_thm (c smaller r l : Int) :
    request_monotone_prop c smaller r l := by
  unfold request_monotone_prop
  simp only [safe_cgroup_memory, decide_eq_true_eq]
  omega

-- Raising the cap preserves admission.
def limit_monotone_prop (c r l larger : Int) : Prop :=
  l ≤ larger → safe_cgroup_memory c r l = true →
    safe_cgroup_memory c r larger = true

theorem limit_monotone_thm (c r l larger : Int) :
    limit_monotone_prop c r l larger := by
  unfold limit_monotone_prop
  simp only [safe_cgroup_memory, decide_eq_true_eq]
  omega

-- Reducing existing usage also preserves admission.
def usage_monotone_prop (smaller c r l : Int) : Prop :=
  smaller ≤ c → safe_cgroup_memory c r l = true →
    safe_cgroup_memory smaller r l = true

theorem usage_monotone_thm (smaller c r l : Int) :
    usage_monotone_prop smaller c r l := by
  unfold usage_monotone_prop
  simp only [safe_cgroup_memory, decide_eq_true_eq]
  omega

-- The postcondition combines exact behavior with its boundary and order laws.
def Post_prop (c r l : Int) : Prop :=
  admission_prop c r l ∧
  rejection_prop c r l ∧
  exact_limit_prop c r ∧
  zero_request_prop c l ∧
  zero_limit_prop c r ∧
  (∀ smaller : Int, request_monotone_prop c smaller r l) ∧
  (∀ larger : Int, limit_monotone_prop c r l larger) ∧
  (∀ smaller : Int, usage_monotone_prop smaller c r l)

-- Property-based tests. Enumerate all signed values from -6 through 6.
-- Each check is the executable form of the named property. Implications are
-- retained, so negative inputs are covered without assuming physical sizes.
def pbtInputs : List Int := (List.range 13).map (fun n => (n : Int) - 6)

def admissionCheck : Bool :=
  pbtInputs.all fun c => pbtInputs.all fun r => pbtInputs.all fun l =>
    decide (safe_cgroup_memory c r l = true ↔ c + r ≤ l)
example : admissionCheck = true := by native_decide
#eval admissionCheck

def rejectionCheck : Bool :=
  pbtInputs.all fun c => pbtInputs.all fun r => pbtInputs.all fun l =>
    decide (safe_cgroup_memory c r l = false ↔ l < c + r)
example : rejectionCheck = true := by native_decide
#eval rejectionCheck

def exactLimitCheck : Bool :=
  pbtInputs.all fun c => pbtInputs.all fun r =>
    safe_cgroup_memory c r (c + r)
example : exactLimitCheck = true := by native_decide
#eval exactLimitCheck

def zeroRequestCheck : Bool :=
  pbtInputs.all fun c => pbtInputs.all fun l =>
    safe_cgroup_memory c 0 l == decide (c ≤ l)
example : zeroRequestCheck = true := by native_decide
#eval zeroRequestCheck

def zeroLimitCheck : Bool :=
  pbtInputs.all fun c => pbtInputs.all fun r =>
    decide (0 ≤ c → 0 ≤ r →
      (safe_cgroup_memory c r 0 = true ↔ c = 0 ∧ r = 0))
example : zeroLimitCheck = true := by native_decide
#eval zeroLimitCheck

def requestMonotoneCheck : Bool :=
  pbtInputs.all fun c => pbtInputs.all fun smaller =>
  pbtInputs.all fun r => pbtInputs.all fun l =>
    decide (smaller ≤ r → safe_cgroup_memory c r l = true →
      safe_cgroup_memory c smaller l = true)
example : requestMonotoneCheck = true := by native_decide
#eval requestMonotoneCheck

def limitMonotoneCheck : Bool :=
  pbtInputs.all fun c => pbtInputs.all fun r =>
  pbtInputs.all fun l => pbtInputs.all fun larger =>
    decide (l ≤ larger → safe_cgroup_memory c r l = true →
      safe_cgroup_memory c r larger = true)
example : limitMonotoneCheck = true := by native_decide
#eval limitMonotoneCheck

def usageMonotoneCheck : Bool :=
  pbtInputs.all fun smaller => pbtInputs.all fun c =>
  pbtInputs.all fun r => pbtInputs.all fun l =>
    decide (smaller ≤ c → safe_cgroup_memory c r l = true →
      safe_cgroup_memory smaller r l = true)
example : usageMonotoneCheck = true := by native_decide
#eval usageMonotoneCheck

-- Bounded counterpart of the entire Post_prop; its internal universal
-- quantifiers are also enumerated over pbtInputs. The theorem below, unlike
-- these tests, proves the postcondition over ALL integers.
def postCheck : Bool :=
  pbtInputs.all fun c => pbtInputs.all fun r => pbtInputs.all fun l =>
    decide (safe_cgroup_memory c r l = true ↔ c + r ≤ l) &&
    decide (safe_cgroup_memory c r l = false ↔ l < c + r) &&
    safe_cgroup_memory c r (c + r) &&
    (safe_cgroup_memory c 0 l == decide (c ≤ l)) &&
    decide (0 ≤ c → 0 ≤ r →
      (safe_cgroup_memory c r 0 = true ↔ c = 0 ∧ r = 0)) &&
    (pbtInputs.all fun smaller =>
      decide (smaller ≤ r → safe_cgroup_memory c r l = true →
        safe_cgroup_memory c smaller l = true)) &&
    (pbtInputs.all fun larger =>
      decide (l ≤ larger → safe_cgroup_memory c r l = true →
        safe_cgroup_memory c r larger = true)) &&
    (pbtInputs.all fun smaller =>
      decide (smaller ≤ c → safe_cgroup_memory c r l = true →
        safe_cgroup_memory smaller r l = true))
example : postCheck = true := by native_decide
#eval postCheck

-- General correctness: no testing or native evaluation is used in this proof.
theorem correctness_thm (c r l : Int) : Pre c r l → Post_prop c r l := by
  intro _
  exact ⟨admission_thm c r l, rejection_thm c r l,
    exact_limit_thm c r, zero_request_thm c l, zero_limit_thm c r,
    fun smaller => request_monotone_thm c smaller r l,
    fun larger => limit_monotone_thm c r l larger,
    fun smaller => usage_monotone_thm smaller c r l⟩

-- Imperative version: calculate prospective usage in a mutable variable and
-- grant only on a successful comparison. There is no bounded-integer overflow.
def safe_cgroup_memory_imp (current_bytes request_bytes limit_bytes : Int) : Bool :=
  Id.run do
    let mut prospective := current_bytes
    prospective := prospective + request_bytes
    let mut granted := false
    if prospective ≤ limit_bytes then
      granted := true
    return granted

-- Imperative tests include every original Python assertion via `check`.
example : check safe_cgroup_memory_imp = true := by native_decide
example : safe_cgroup_memory_imp 100 50 200 = true := by native_decide
example : safe_cgroup_memory_imp 100 100 200 = true := by native_decide
example : safe_cgroup_memory_imp 100 101 200 = false := by native_decide
example : safe_cgroup_memory_imp 100 200 150 = false := by native_decide
example : safe_cgroup_memory_imp 0 200 200 = true := by native_decide
example : safe_cgroup_memory_imp 0 201 200 = false := by native_decide
example : safe_cgroup_memory_imp 0 1 0 = false := by native_decide
example : safe_cgroup_memory_imp 0 0 0 = true := by native_decide
example : safe_cgroup_memory_imp 0 (10 ^ 9) (10 ^ 9) = true := by native_decide
example : safe_cgroup_memory_imp 1 (10 ^ 9) (10 ^ 9) = false := by native_decide
example : safe_cgroup_memory_imp 10 (-5) 5 = true := by native_decide
#eval check safe_cgroup_memory_imp
#eval safe_cgroup_memory_imp 100 101 200

-- Kernel-checked equivalence on the entire signed integer domain.
theorem equivalence_thm (c r l : Int) :
    safe_cgroup_memory c r l = safe_cgroup_memory_imp c r l := by
  by_cases h : c + r ≤ l <;>
    simp [safe_cgroup_memory, safe_cgroup_memory_imp, h]

end UnsafeCgroupMemorySafe
end Agent
