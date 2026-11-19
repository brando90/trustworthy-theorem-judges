import Mathlib
namespace Agent

/-!
# Unsafe null pointer acceptance

Translation of the Python `unsafe_ptr_check` example from the MIT 6.858
Spring 2013 Quiz 1 memory-safety setting. Python integers are represented by
`Int`: no nonnegativity, machine-word bound, or non-null precondition is imposed.
The check ignores its argument and returns `true`, including for address zero.

This file specifies the unsafe behavior rather than repairing it. It models
only the check, not memory mappings or a subsequent pointer dereference, so it
makes no claim that any accepted integer is a safe address to dereference.
-/

namespace UnsafeNullPtrDeref

/-! ## Functional implementation -/

/-- The Python function returns `True` without examining its argument. -/
def unsafe_ptr_check (_ptr_val : Int) : Bool := true

/-! ## Unit tests and the Python test harness -/

example : unsafe_ptr_check 1 = true := by native_decide
example : unsafe_ptr_check 0 = true := by native_decide
example : unsafe_ptr_check 0xdeadbeef = true := by native_decide
example : unsafe_ptr_check (-1) = true := by native_decide

/-- Reproduce the assertions and success message of Python's `check()`. -/
def check : IO Unit := do
  if unsafe_ptr_check 1 != true then
    throw (IO.userError "valid ptr rejected")
  if unsafe_ptr_check 0 != true then
    throw (IO.userError "vuln: null ptr accepted")
  if unsafe_ptr_check 0xdeadbeef != true then
    throw (IO.userError "non-null ptr rejected")
  IO.println "All tests passed."

#eval check
#eval unsafe_ptr_check (-1)

/-! ## Precondition -/

/-- Every integer is admissible, notably including zero. -/
def Pre (_ptr_val : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Acceptance is unconditional. -/
def always_accepts_prop (ptr_val : Int) : Prop :=
  unsafe_ptr_check ptr_val = true

theorem always_accepts_thm (ptr_val : Int) : always_accepts_prop ptr_val := by
  rfl

/-- A null input is accepted, explicitly capturing the unsafe case. -/
def null_accepted_prop (ptr_val : Int) : Prop :=
  ptr_val = 0 → unsafe_ptr_check ptr_val = true

theorem null_accepted_thm (ptr_val : Int) : null_accepted_prop ptr_val := by
  intro _
  rfl

/-- Non-null inputs are also accepted; this does not establish memory safety. -/
def nonnull_accepted_prop (ptr_val : Int) : Prop :=
  ptr_val ≠ 0 → unsafe_ptr_check ptr_val = true

theorem nonnull_accepted_thm (ptr_val : Int) : nonnull_accepted_prop ptr_val := by
  intro _
  rfl

/-- Changing the pointer value never changes the result of this check. -/
def input_independent_prop (ptr_val other : Int) : Prop :=
  unsafe_ptr_check ptr_val = unsafe_ptr_check other

theorem input_independent_thm (ptr_val other : Int) :
    input_independent_prop ptr_val other := by
  rfl

/-! ## Postcondition -/

/-- All behavior properties, with independence from every other integer. -/
def Post_prop (ptr_val : Int) : Prop :=
  always_accepts_prop ptr_val ∧
  null_accepted_prop ptr_val ∧
  nonnull_accepted_prop ptr_val ∧
  (∀ other : Int, input_independent_prop ptr_val other)

/-! ## Property-based tests

These bounded PBTs exhaust all integers from -128 through 128 and also test
large positive and negative integers. The two-input property is tested on the
Cartesian product. Each predicate below is the executable Boolean form of the
named property, not a proof of its unrestricted theorem. In particular, the
null-acceptance test includes zero, so its implication is not tested vacuously.
-/

def pbtInputs : List Int :=
  (List.range 257).map (fun n => (n : Int) - 128) ++
    [0xdeadbeef, -0xdeadbeef, (2 : Int) ^ 100, -((2 : Int) ^ 100)]

-- PBT for always_accepts_prop.
example : pbtInputs.all (fun ptr_val => unsafe_ptr_check ptr_val == true) = true := by
  native_decide

-- PBT for null_accepted_prop: A → B is encoded as (!A) || B.
example : pbtInputs.all (fun ptr_val =>
    (ptr_val != 0) || (unsafe_ptr_check ptr_val == true)) = true := by
  native_decide

-- PBT for nonnull_accepted_prop.
example : pbtInputs.all (fun ptr_val =>
    (ptr_val == 0) || (unsafe_ptr_check ptr_val == true)) = true := by
  native_decide

-- PBT for input_independent_prop, covering every pair of sampled integers.
example : pbtInputs.all (fun ptr_val =>
    pbtInputs.all (fun other =>
      unsafe_ptr_check ptr_val == unsafe_ptr_check other)) = true := by
  native_decide

-- PBT for Post_prop: all conjuncts, sampling its universal 'other' argument.
example : pbtInputs.all (fun ptr_val =>
    (unsafe_ptr_check ptr_val == true) &&
    ((ptr_val != 0) || (unsafe_ptr_check ptr_val == true)) &&
    ((ptr_val == 0) || (unsafe_ptr_check ptr_val == true)) &&
    pbtInputs.all (fun other =>
      unsafe_ptr_check ptr_val == unsafe_ptr_check other)) = true := by
  native_decide

/-! ## Correctness -/

/-- The implementation satisfies the specification of its unsafe behavior. -/
theorem correctness_thm (ptr_val : Int) : Pre ptr_val → Post_prop ptr_val := by
  intro _
  exact ⟨always_accepts_thm ptr_val,
    null_accepted_thm ptr_val,
    nonnull_accepted_thm ptr_val,
    fun other => input_independent_thm ptr_val other⟩

/-! ## Imperative implementation -/

/-- Mutable-state version: set the result to true without checking the input. -/
def unsafe_ptr_check_imperative (_ptr_val : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_ptr_check_imperative 1 = true := by native_decide
example : unsafe_ptr_check_imperative 0 = true := by native_decide
example : unsafe_ptr_check_imperative 0xdeadbeef = true := by native_decide
example : unsafe_ptr_check_imperative (-1) = true := by native_decide

#eval (unsafe_ptr_check_imperative 1,
  unsafe_ptr_check_imperative 0,
  unsafe_ptr_check_imperative 0xdeadbeef)

example : pbtInputs.all (fun ptr_val =>
    unsafe_ptr_check ptr_val == unsafe_ptr_check_imperative ptr_val) = true := by
  native_decide

/-! ## Functional-imperative equivalence -/

/-- Equivalence holds for all integers, without any precondition. -/
theorem functional_imperative_equiv_thm (ptr_val : Int) :
    unsafe_ptr_check ptr_val = unsafe_ptr_check_imperative ptr_val := by
  rfl

end UnsafeNullPtrDeref
end Agent
