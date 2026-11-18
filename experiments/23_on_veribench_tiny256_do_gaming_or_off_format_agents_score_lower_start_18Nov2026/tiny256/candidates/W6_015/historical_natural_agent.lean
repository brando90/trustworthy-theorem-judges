import Mathlib
namespace Agent

/-!
# Unsafe cgroup memory allocation

Translation of the MIT 6.858 Lecture 6 example: every allocation request is
accepted, without consulting the current usage, requested size, or cgroup limit.
This deliberately models the vulnerability, not a repaired allocator.

Python integers are represented by `Int`, including negative and arbitrarily
large values. The source has no input checks, so the precondition is `True`.
The tests include the five Python assertions and bounded property-based checks.
All named theorems are proved by kernel-checked proofs, independently of tests.
-/

namespace UnsafeCgroupMemory

/-! ## Functional implementation and the Python test harness -/

/-- The limit is deliberately never enforced. -/
def unsafe_cgroup_memory
    (_current_bytes _request_bytes _limit_bytes : Int) : Bool :=
  true

/-- The Boolean counterpart of the five assertions in Python's `check`.
For a Bool-valued candidate, a conjunction succeeds exactly when every call
returns `True`. -/
def check (candidate : Int → Int → Int → Bool) : Bool :=
  candidate 100 50 200 &&
  candidate 100 200 150 &&
  candidate 0 1 0 &&
  candidate 200 1 200 &&
  candidate 0 (10 ^ 9) 1024

/-! ## Unit tests -/

-- Normal allocation, well within the limit.
example : unsafe_cgroup_memory 100 50 200 = true := by native_decide
-- 100 + 200 > 150, yet the allocation is accepted.
example : unsafe_cgroup_memory 100 200 150 = true := by native_decide
-- A zero limit does not prevent a nonzero allocation.
example : unsafe_cgroup_memory 0 1 0 = true := by native_decide
-- Already at the limit.
example : unsafe_cgroup_memory 200 1 200 = true := by native_decide
-- Far beyond the limit; Int introduces no machine-integer overflow.
example : unsafe_cgroup_memory 0 (10 ^ 9) 1024 = true := by native_decide
-- The function does not validate signs either.
example : unsafe_cgroup_memory (-100) (-50) (-200) = true := by native_decide
example : check unsafe_cgroup_memory = true := by native_decide

#eval unsafe_cgroup_memory 100 50 200
#eval unsafe_cgroup_memory 100 200 150
#eval unsafe_cgroup_memory 0 1 0
#eval unsafe_cgroup_memory 200 1 200
#eval unsafe_cgroup_memory 0 (10 ^ 9) 1024
#eval check unsafe_cgroup_memory
#eval if check unsafe_cgroup_memory then "All tests passed." else "Candidate failed cgroup memory tests"

/-! ## Preconditions -/

/-- No restrictions are imposed by the Python implementation. -/
def Pre (_current_bytes _request_bytes _limit_bytes : Int) : Prop := True

/-! ## Properties and proofs -/

/-- The complete return-value specification, on every integer input. -/
def always_granted_prop (current_bytes request_bytes limit_bytes : Int) : Prop :=
  unsafe_cgroup_memory current_bytes request_bytes limit_bytes = true

theorem always_granted_thm (current_bytes request_bytes limit_bytes : Int) :
    always_granted_prop current_bytes request_bytes limit_bytes := by
  rfl

/-- Changing only the limit cannot affect the decision. -/
def limit_ignored_prop
    (current_bytes request_bytes limit_bytes other_limit_bytes : Int) : Prop :=
  unsafe_cgroup_memory current_bytes request_bytes limit_bytes =
    unsafe_cgroup_memory current_bytes request_bytes other_limit_bytes

theorem limit_ignored_thm
    (current_bytes request_bytes limit_bytes other_limit_bytes : Int) :
    limit_ignored_prop current_bytes request_bytes limit_bytes other_limit_bytes := by
  rfl

/-- The unsafe acceptance persists even when the prospective usage exceeds the cap. -/
def over_limit_granted_prop (current_bytes request_bytes limit_bytes : Int) : Prop :=
  limit_bytes < current_bytes + request_bytes →
    unsafe_cgroup_memory current_bytes request_bytes limit_bytes = true

theorem over_limit_granted_thm (current_bytes request_bytes limit_bytes : Int) :
    over_limit_granted_prop current_bytes request_bytes limit_bytes := by
  intro _
  rfl

/-- A zero cap is ignored, for all usages and requests (including positive requests). -/
def zero_limit_granted_prop (current_bytes request_bytes : Int) : Prop :=
  unsafe_cgroup_memory current_bytes request_bytes 0 = true

theorem zero_limit_granted_thm (current_bytes request_bytes : Int) :
    zero_limit_granted_prop current_bytes request_bytes := by
  rfl

/-- Being already at the cap does not prevent any further request. -/
def at_limit_granted_prop (limit_bytes request_bytes : Int) : Prop :=
  unsafe_cgroup_memory limit_bytes request_bytes limit_bytes = true

theorem at_limit_granted_thm (limit_bytes request_bytes : Int) :
    at_limit_granted_prop limit_bytes request_bytes := by
  rfl

/-! ## Postcondition -/

/-- The exact return behavior together with its limit-enforcement consequences.
The universal conjunct expresses independence from every possible replacement cap. -/
def Post_prop (current_bytes request_bytes limit_bytes : Int) : Prop :=
  always_granted_prop current_bytes request_bytes limit_bytes ∧
  limit_ignored_prop current_bytes request_bytes limit_bytes 0 ∧
  (∀ other_limit_bytes : Int,
    limit_ignored_prop current_bytes request_bytes limit_bytes other_limit_bytes) ∧
  over_limit_granted_prop current_bytes request_bytes limit_bytes ∧
  zero_limit_granted_prop current_bytes request_bytes ∧
  at_limit_granted_prop limit_bytes request_bytes

/-! ## Property-based tests

Exhaust the Cartesian products of a small signed interval and representative
boundary/large values. These are executable Boolean counterparts, not proofs
of the universally quantified specifications. In particular, implication is
checked as `!antecedent || consequent`, so no Decidable instance for the named
Prop definitions is needed. The domain includes both satisfying and violating
prospective memory caps.
-/

private def testBytes : List Int :=
  (List.range 11).map (fun n => (n : Int) - 5) ++
    [50, 100, 150, 200, 1024, 10 ^ 9, -(10 ^ 9)]

-- PBT: always_granted_prop.
example :
    testBytes.all (fun current =>
      testBytes.all (fun request =>
        testBytes.all (fun limit =>
          unsafe_cgroup_memory current request limit))) = true := by
  native_decide

-- PBT: limit_ignored_prop, varying both limits independently.
example :
    testBytes.all (fun current =>
      testBytes.all (fun request =>
        testBytes.all (fun limit =>
          testBytes.all (fun otherLimit =>
            decide (unsafe_cgroup_memory current request limit =
              unsafe_cgroup_memory current request otherLimit))))) = true := by
  native_decide

-- PBT: over_limit_granted_prop.
example :
    testBytes.all (fun current =>
      testBytes.all (fun request =>
        testBytes.all (fun limit =>
          !decide (limit < current + request) ||
            unsafe_cgroup_memory current request limit))) = true := by
  native_decide

-- PBT: zero_limit_granted_prop.
example :
    testBytes.all (fun current =>
      testBytes.all (fun request =>
        unsafe_cgroup_memory current request 0)) = true := by
  native_decide

-- PBT: at_limit_granted_prop.
example :
    testBytes.all (fun limit =>
      testBytes.all (fun request =>
        unsafe_cgroup_memory limit request limit)) = true := by
  native_decide

-- PBT: Post_prop, checking all conjuncts together. Its universal replacement-limit
-- conjunct is sampled exhaustively over testBytes, as are its three input arguments.
example :
    testBytes.all (fun current =>
      testBytes.all (fun request =>
        testBytes.all (fun limit =>
          unsafe_cgroup_memory current request limit &&
          decide (unsafe_cgroup_memory current request limit =
            unsafe_cgroup_memory current request 0) &&
          testBytes.all (fun otherLimit =>
            decide (unsafe_cgroup_memory current request limit =
              unsafe_cgroup_memory current request otherLimit)) &&
          (!decide (limit < current + request) ||
            unsafe_cgroup_memory current request limit) &&
          unsafe_cgroup_memory current request 0 &&
          unsafe_cgroup_memory limit request limit))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (current_bytes request_bytes limit_bytes : Int) :
    Pre current_bytes request_bytes limit_bytes →
      Post_prop current_bytes request_bytes limit_bytes := by
  intro _
  exact ⟨always_granted_thm current_bytes request_bytes limit_bytes,
    limit_ignored_thm current_bytes request_bytes limit_bytes 0,
    fun other_limit_bytes =>
      limit_ignored_thm current_bytes request_bytes limit_bytes other_limit_bytes,
    over_limit_granted_thm current_bytes request_bytes limit_bytes,
    zero_limit_granted_thm current_bytes request_bytes,
    at_limit_granted_thm limit_bytes request_bytes⟩

/-! ## Imperative implementation -/

/-- The decision is overwritten unconditionally; no memory-limit check occurs. -/
def unsafe_cgroup_memory_imperative
    (_current_bytes _request_bytes _limit_bytes : Int) : Bool := Id.run do
  let mut granted := false
  granted := true
  return granted

/-! ## Imperative tests -/

example : unsafe_cgroup_memory_imperative 100 50 200 = true := by native_decide
example : unsafe_cgroup_memory_imperative 100 200 150 = true := by native_decide
example : unsafe_cgroup_memory_imperative 0 1 0 = true := by native_decide
example : unsafe_cgroup_memory_imperative 200 1 200 = true := by native_decide
example : unsafe_cgroup_memory_imperative 0 (10 ^ 9) 1024 = true := by native_decide
example : check unsafe_cgroup_memory_imperative = true := by native_decide

#eval check unsafe_cgroup_memory_imperative
#eval if check unsafe_cgroup_memory_imperative then "All tests passed." else "Candidate failed cgroup memory tests"

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm
    (current_bytes request_bytes limit_bytes : Int) :
    unsafe_cgroup_memory current_bytes request_bytes limit_bytes =
      unsafe_cgroup_memory_imperative current_bytes request_bytes limit_bytes := by
  rfl

end UnsafeCgroupMemory
end Agent
