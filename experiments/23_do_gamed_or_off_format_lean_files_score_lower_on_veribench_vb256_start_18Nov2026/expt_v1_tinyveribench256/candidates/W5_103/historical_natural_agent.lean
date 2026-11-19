import Mathlib
namespace Agent

/-!
# Unchecked kernel-address disclosure

Translation of Python's `unsafeKernelAddrLeak` and its six checks. Python's
unbounded integer arguments are modeled by `Int`, including negative values and
values larger than a machine word. The function deliberately ignores privilege:
privilege 1 is the kernel convention, while privilege 0 denotes userspace.

This file describes the vulnerable behavior, not a repaired access-control
policy. In particular, the user-leak theorem proves that userspace receives the
entire address unchanged. Tests provide executable evidence; the named theorems
have independent kernel-checked proofs.
-/

namespace «149_unsafeKernelAddrLeak»

/-! ## Functional implementation -/

/-- No privilege check, masking, truncation, or validation is performed. -/
def unsafeKernelAddrLeak (_caller_privilege : Int) (kernel_addr : Int) : Int :=
  kernel_addr

/-! ## The six source unit tests -/

example : unsafeKernelAddrLeak 1 0xFFFF800000000000 = 0xFFFF800000000000 := by
  native_decide

example : unsafeKernelAddrLeak 1 0xFFFFFFFF81000000 = 0xFFFFFFFF81000000 := by
  native_decide

-- These two passing tests exhibit the vulnerability, not safe behavior.
example : unsafeKernelAddrLeak 0 0xFFFF800000000000 = 0xFFFF800000000000 := by
  native_decide

example : unsafeKernelAddrLeak 0 0xFFFFFFFF81000000 = 0xFFFFFFFF81000000 := by
  native_decide

example : unsafeKernelAddrLeak 0 0 = 0 := by
  native_decide

example : unsafeKernelAddrLeak 0 0xDEADBEEF = 0xDEADBEEF := by
  native_decide

/-- Executable counterpart of the assertions in Python's `check`. -/
def check : Bool :=
  (unsafeKernelAddrLeak 1 0xFFFF800000000000 == 0xFFFF800000000000) &&
  (unsafeKernelAddrLeak 1 0xFFFFFFFF81000000 == 0xFFFFFFFF81000000) &&
  (unsafeKernelAddrLeak 0 0xFFFF800000000000 == 0xFFFF800000000000) &&
  (unsafeKernelAddrLeak 0 0xFFFFFFFF81000000 == 0xFFFFFFFF81000000) &&
  (unsafeKernelAddrLeak 0 0 == 0) &&
  (unsafeKernelAddrLeak 0 0xDEADBEEF == 0xDEADBEEF)

example : check = true := by native_decide

#eval if check then "All tests passed." else "A test failed."

/-! ## Preconditions and semantic properties -/

/-- Every pair of Python integers is admissible; even privilege is unrestricted. -/
def Pre (_caller_privilege _kernel_addr : Int) : Prop := True

/-- The returned address is exactly the supplied integer for every caller. -/
def returnsAddress_prop (caller_privilege kernel_addr : Int) : Prop :=
  unsafeKernelAddrLeak caller_privilege kernel_addr = kernel_addr

theorem returnsAddress_thm (caller_privilege kernel_addr : Int) :
    returnsAddress_prop caller_privilege kernel_addr := by
  rfl

/-- Expected behavior for a kernel caller, for every address. -/
def kernelCaller_prop (kernel_addr : Int) : Prop :=
  unsafeKernelAddrLeak 1 kernel_addr = kernel_addr

theorem kernelCaller_thm (kernel_addr : Int) : kernelCaller_prop kernel_addr := by
  rfl

/-- Vulnerability: a userspace caller receives the same raw address. -/
def userLeak_prop (kernel_addr : Int) : Prop :=
  unsafeKernelAddrLeak 0 kernel_addr = kernel_addr

theorem userLeak_thm (kernel_addr : Int) : userLeak_prop kernel_addr := by
  rfl

/-- Changing privilege cannot change the output, even for nonstandard values. -/
def privilegeIndependent_prop (caller_privilege other_privilege kernel_addr : Int) : Prop :=
  unsafeKernelAddrLeak caller_privilege kernel_addr =
    unsafeKernelAddrLeak other_privilege kernel_addr

theorem privilegeIndependent_thm (caller_privilege other_privilege kernel_addr : Int) :
    privilegeIndependent_prop caller_privilege other_privilege kernel_addr := by
  rfl

/-! ## Postcondition -/

/-- The behavioral contract includes the disclosure, rather than forbidding it. -/
def Post_prop (caller_privilege kernel_addr : Int) : Prop :=
  returnsAddress_prop caller_privilege kernel_addr ∧
  kernelCaller_prop kernel_addr ∧
  userLeak_prop kernel_addr ∧
  (∀ other_privilege : Int,
    privilegeIndependent_prop caller_privilege other_privilege kernel_addr)

/-! ## Property-based tests

Each property has a randomized check of its executable equality form and a
bounded Boolean check. For the universal clause of `Post_prop`, the randomized
check samples the other privilege too; the bounded check enumerates it. These
finite tests do not replace the universal theorems above and below.
-/

-- PBT for returnsAddress_prop.
#eval Plausible.Testable.check
  (∀ caller_privilege kernel_addr : Int,
    unsafeKernelAddrLeak caller_privilege kernel_addr = kernel_addr)

-- PBT for kernelCaller_prop.
#eval Plausible.Testable.check
  (∀ kernel_addr : Int, unsafeKernelAddrLeak 1 kernel_addr = kernel_addr)

-- PBT for userLeak_prop.
#eval Plausible.Testable.check
  (∀ kernel_addr : Int, unsafeKernelAddrLeak 0 kernel_addr = kernel_addr)

-- PBT for privilegeIndependent_prop.
#eval Plausible.Testable.check
  (∀ caller_privilege other_privilege kernel_addr : Int,
    unsafeKernelAddrLeak caller_privilege kernel_addr =
      unsafeKernelAddrLeak other_privilege kernel_addr)

-- PBT for all conjuncts of Post_prop, including its universally quantified clause.
#eval Plausible.Testable.check
  (∀ caller_privilege kernel_addr other_privilege : Int,
    unsafeKernelAddrLeak caller_privilege kernel_addr = kernel_addr ∧
    unsafeKernelAddrLeak 1 kernel_addr = kernel_addr ∧
    unsafeKernelAddrLeak 0 kernel_addr = kernel_addr ∧
    unsafeKernelAddrLeak caller_privilege kernel_addr =
      unsafeKernelAddrLeak other_privilege kernel_addr)

/-- Exhaustive small privileges plus values far beyond the 0/1 convention. -/
private def testPrivileges : List Int :=
  (List.range 21).map (fun n => (n : Int) - 10) ++
    [-0x10000000000000000, 0x10000000000000000]

/-- Small signed addresses and original examples, including beyond-64-bit cases. -/
private def testAddresses : List Int :=
  (List.range 41).map (fun n => (n : Int) - 20) ++
    [0xFFFF800000000000, 0xFFFFFFFF81000000, 0xDEADBEEF,
     -0xFFFF800000000000, -0x10000000000000000, 0x10000000000000000]

-- Bounded PBT for returnsAddress_prop.
example : (testPrivileges.all fun p =>
    testAddresses.all fun a => unsafeKernelAddrLeak p a == a) = true := by
  native_decide

-- Bounded PBT for kernelCaller_prop.
example : (testAddresses.all fun a => unsafeKernelAddrLeak 1 a == a) = true := by
  native_decide

-- Bounded PBT for userLeak_prop.
example : (testAddresses.all fun a => unsafeKernelAddrLeak 0 a == a) = true := by
  native_decide

-- Bounded PBT for privilegeIndependent_prop.
example : (testPrivileges.all fun p =>
    testPrivileges.all fun q =>
      testAddresses.all fun a =>
        unsafeKernelAddrLeak p a == unsafeKernelAddrLeak q a) = true := by
  native_decide

-- Bounded PBT for Post_prop, enumerating each input of every conjunct.
example : (testPrivileges.all fun p =>
    testAddresses.all fun a =>
      (unsafeKernelAddrLeak p a == a) &&
      (unsafeKernelAddrLeak 1 a == a) &&
      (unsafeKernelAddrLeak 0 a == a) &&
      (testPrivileges.all fun q =>
        unsafeKernelAddrLeak p a == unsafeKernelAddrLeak q a)) = true := by
  native_decide

/-! ## Correctness of the vulnerable behavior -/

theorem correctness_thm (caller_privilege kernel_addr : Int) :
    Pre caller_privilege kernel_addr → Post_prop caller_privilege kernel_addr := by
  intro _
  exact ⟨returnsAddress_thm caller_privilege kernel_addr,
    kernelCaller_thm kernel_addr,
    userLeak_thm kernel_addr,
    fun other_privilege =>
      privilegeIndependent_thm caller_privilege other_privilege kernel_addr⟩

/-! ## Imperative implementation -/

/-- A mutable return slot, still with no access-control check. -/
def unsafeKernelAddrLeakImperative (_caller_privilege : Int) (kernel_addr : Int) : Int :=
  Id.run do
    let mut result : Int := 0
    result := kernel_addr
    return result

/-! ## Imperative unit tests -/

example : unsafeKernelAddrLeakImperative 1 0xFFFF800000000000 = 0xFFFF800000000000 := by
  native_decide

example : unsafeKernelAddrLeakImperative 1 0xFFFFFFFF81000000 = 0xFFFFFFFF81000000 := by
  native_decide

example : unsafeKernelAddrLeakImperative 0 0xFFFF800000000000 = 0xFFFF800000000000 := by
  native_decide

example : unsafeKernelAddrLeakImperative 0 0xFFFFFFFF81000000 = 0xFFFFFFFF81000000 := by
  native_decide

example : unsafeKernelAddrLeakImperative 0 0 = 0 := by
  native_decide

example : unsafeKernelAddrLeakImperative 0 0xDEADBEEF = 0xDEADBEEF := by
  native_decide

#eval [unsafeKernelAddrLeakImperative 1 0xFFFF800000000000,
       unsafeKernelAddrLeakImperative 1 0xFFFFFFFF81000000,
       unsafeKernelAddrLeakImperative 0 0xFFFF800000000000,
       unsafeKernelAddrLeakImperative 0 0xFFFFFFFF81000000,
       unsafeKernelAddrLeakImperative 0 0,
       unsafeKernelAddrLeakImperative 0 0xDEADBEEF]

-- Bounded functional/imperative agreement test, including signed integers.
example : (testPrivileges.all fun p =>
    testAddresses.all fun a =>
      unsafeKernelAddrLeak p a == unsafeKernelAddrLeakImperative p a) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equiv_thm (caller_privilege kernel_addr : Int) :
    unsafeKernelAddrLeak caller_privilege kernel_addr =
      unsafeKernelAddrLeakImperative caller_privilege kernel_addr := by
  rfl

end «149_unsafeKernelAddrLeak»
end Agent
