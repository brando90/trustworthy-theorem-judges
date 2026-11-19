import Mathlib
namespace Agent

/-!
# Safe kernel address disclosure

Translation of the Python `safeKernelAddrLeak` program. Python integers are
modelled by unbounded signed `Int`, both for privileges and for addresses.
Exactly privilege 1 may observe the supplied address; every other privilege
receives 0. There is no assumption that privileges are restricted to {0, 1},
or that addresses are nonnegative or fit in a machine word.

The functional and mutable-state implementations are proved equivalent.
Named theorems use kernel-checked proofs. `native_decide` is used only for
unit tests and bounded property-based tests, not as a proof of correctness.
-/

namespace «149_unsafeKernelAddrLeak_safe»

-- Implementation: the constants and branch are those of the Python source.
def KERNEL_PRIVILEGE : Int := 1
def USER_PRIVILEGE : Int := 0
def REDACTED_ADDR : Int := 0

def safeKernelAddrLeak (caller_privilege kernel_addr : Int) : Int :=
  if caller_privilege = KERNEL_PRIVILEGE then kernel_addr else REDACTED_ADDR

-- Unit tests: all seven assertions in Python's `check`.
example : safeKernelAddrLeak 1 0xFFFF800000000000 = 0xFFFF800000000000 := by
  native_decide
example : safeKernelAddrLeak 1 0xFFFFFFFF81000000 = 0xFFFFFFFF81000000 := by
  native_decide
example : safeKernelAddrLeak 0 0xFFFF800000000000 = 0 := by native_decide
example : safeKernelAddrLeak 0 0xFFFFFFFF81000000 = 0 := by native_decide
example : safeKernelAddrLeak 0 0 = 0 := by native_decide
example : safeKernelAddrLeak 1 0 = 0 := by native_decide
example : safeKernelAddrLeak 0 0xDEADBEEF = 0 := by native_decide

-- Additional unit tests protect the full signed-integer domain.
example : safeKernelAddrLeak (-1) 0xDEADBEEF = 0 := by native_decide
example : safeKernelAddrLeak 2 0xFFFF800000000000 = 0 := by native_decide
example : safeKernelAddrLeak 1 (-123) = -123 := by native_decide
example : safeKernelAddrLeak 0 (-123) = 0 := by native_decide

/-- Executable counterpart of Python's test runner. -/
def check : IO Unit := do
  let tests : List Bool := [
    safeKernelAddrLeak 1 0xFFFF800000000000 == 0xFFFF800000000000,
    safeKernelAddrLeak 1 0xFFFFFFFF81000000 == 0xFFFFFFFF81000000,
    safeKernelAddrLeak 0 0xFFFF800000000000 == 0,
    safeKernelAddrLeak 0 0xFFFFFFFF81000000 == 0,
    safeKernelAddrLeak 0 0 == 0,
    safeKernelAddrLeak 1 0 == 0,
    safeKernelAddrLeak 0 0xDEADBEEF == 0]
  if tests.all id then
    IO.println "All tests passed."
  else
    throw (IO.userError "safeKernelAddrLeak: a unit test failed")

#eval check

/-- All pairs of Python integer inputs are admissible. -/
def Pre (_caller_privilege _kernel_addr : Int) : Prop := True

/-- A kernel-privileged caller gets the exact supplied address. -/
def privilegedAccess_prop (caller_privilege kernel_addr : Int) : Prop :=
  caller_privilege = KERNEL_PRIVILEGE →
    safeKernelAddrLeak caller_privilege kernel_addr = kernel_addr

theorem privilegedAccess_thm (caller_privilege kernel_addr : Int) :
    privilegedAccess_prop caller_privilege kernel_addr := by
  intro h
  simp [safeKernelAddrLeak, h]

/-- Every privilege other than 1 is redacted, not just privilege 0. -/
def unprivilegedRedaction_prop (caller_privilege kernel_addr : Int) : Prop :=
  caller_privilege ≠ KERNEL_PRIVILEGE →
    safeKernelAddrLeak caller_privilege kernel_addr = REDACTED_ADDR

theorem unprivilegedRedaction_thm (caller_privilege kernel_addr : Int) :
    unprivilegedRedaction_prop caller_privilege kernel_addr := by
  intro h
  simp [safeKernelAddrLeak, h]

/-- In particular, the designated user-space privilege always gets zero. -/
def userRedaction_prop (kernel_addr : Int) : Prop :=
  safeKernelAddrLeak USER_PRIVILEGE kernel_addr = REDACTED_ADDR

theorem userRedaction_thm (kernel_addr : Int) : userRedaction_prop kernel_addr := by
  simp [userRedaction_prop, safeKernelAddrLeak, USER_PRIVILEGE, KERNEL_PRIVILEGE]

/-- A zero address yields zero for every caller, including kernel callers. -/
def zeroAddress_prop (caller_privilege : Int) : Prop :=
  safeKernelAddrLeak caller_privilege 0 = 0

theorem zeroAddress_thm (caller_privilege : Int) : zeroAddress_prop caller_privilege := by
  simp [zeroAddress_prop, safeKernelAddrLeak, REDACTED_ADDR]

/-- Nonzero disclosure occurs exactly for privilege 1 and a nonzero address.
The address condition is necessary: a privileged caller can also receive 0. -/
def nonzeroDisclosure_prop (caller_privilege kernel_addr : Int) : Prop :=
  safeKernelAddrLeak caller_privilege kernel_addr ≠ REDACTED_ADDR ↔
    caller_privilege = KERNEL_PRIVILEGE ∧ kernel_addr ≠ REDACTED_ADDR

theorem nonzeroDisclosure_thm (caller_privilege kernel_addr : Int) :
    nonzeroDisclosure_prop caller_privilege kernel_addr := by
  by_cases h : caller_privilege = KERNEL_PRIVILEGE <;>
    simp [nonzeroDisclosure_prop, safeKernelAddrLeak, h]

/-- An unprivileged observer cannot distinguish any two supplied addresses. -/
def noninterference_prop (caller_privilege addr₁ addr₂ : Int) : Prop :=
  caller_privilege ≠ KERNEL_PRIVILEGE →
    safeKernelAddrLeak caller_privilege addr₁ = safeKernelAddrLeak caller_privilege addr₂

theorem noninterference_thm (caller_privilege addr₁ addr₂ : Int) :
    noninterference_prop caller_privilege addr₁ addr₂ := by
  intro h
  simp [safeKernelAddrLeak, h]

/-- The postcondition combines access control, the edge case, and confidentiality.
The final conjunct compares this address with every possible other address. -/
def Post_prop (caller_privilege kernel_addr : Int) : Prop :=
  privilegedAccess_prop caller_privilege kernel_addr ∧
  unprivilegedRedaction_prop caller_privilege kernel_addr ∧
  userRedaction_prop kernel_addr ∧
  zeroAddress_prop caller_privilege ∧
  nonzeroDisclosure_prop caller_privilege kernel_addr ∧
  ∀ other_addr : Int, noninterference_prop caller_privilege kernel_addr other_addr

/-! ## Bounded property-based tests

Each PBT below checks an executable form of a named property. These tests
exhaust privileges -16 through 16 and addresses -32 through 32, augmented by
large positive and negative addresses. Both privilege branches are exercised
nonvacuously. The theorems above and below, unlike these finite tests, cover
all integers. In the postcondition PBT the universal `other_addr` conjunct is
checked over the same address sample; it is not assumed or dropped.
-/

def privilegeSamples : List Int :=
  (List.range 33).map (fun n => (n : Int) - 16)

def addressSamples : List Int :=
  (List.range 65).map (fun n => (n : Int) - 32) ++
    [0xFFFF800000000000, 0xFFFFFFFF81000000, 0xDEADBEEF,
     -0xFFFF800000000000, -0xFFFFFFFF81000000,
     0x100000000000000000000, -0x100000000000000000000]

-- PBT: privilegedAccess_prop.
example : privilegeSamples.all (fun p => addressSamples.all (fun a =>
    decide (p = KERNEL_PRIVILEGE → safeKernelAddrLeak p a = a))) = true := by
  native_decide

-- PBT: unprivilegedRedaction_prop.
example : privilegeSamples.all (fun p => addressSamples.all (fun a =>
    decide (p ≠ KERNEL_PRIVILEGE → safeKernelAddrLeak p a = REDACTED_ADDR))) = true := by
  native_decide

-- PBT: userRedaction_prop.
example : addressSamples.all (fun a =>
    decide (safeKernelAddrLeak USER_PRIVILEGE a = REDACTED_ADDR)) = true := by
  native_decide

-- PBT: zeroAddress_prop.
example : privilegeSamples.all (fun p =>
    decide (safeKernelAddrLeak p 0 = 0)) = true := by
  native_decide

-- PBT: nonzeroDisclosure_prop, including both directions of the equivalence.
example : privilegeSamples.all (fun p => addressSamples.all (fun a =>
    decide (safeKernelAddrLeak p a ≠ REDACTED_ADDR ↔
      p = KERNEL_PRIVILEGE ∧ a ≠ REDACTED_ADDR))) = true := by
  native_decide

-- PBT: noninterference_prop, over every pair of sampled addresses.
example : privilegeSamples.all (fun p => addressSamples.all (fun a =>
    addressSamples.all (fun b => decide (p ≠ KERNEL_PRIVILEGE →
      safeKernelAddrLeak p a = safeKernelAddrLeak p b)))) = true := by
  native_decide

/-- Executable, bounded form of every conjunct of Post_prop. -/
def postCheck (p a : Int) : Bool :=
  decide ((p = KERNEL_PRIVILEGE → safeKernelAddrLeak p a = a) ∧
    (p ≠ KERNEL_PRIVILEGE → safeKernelAddrLeak p a = REDACTED_ADDR) ∧
    safeKernelAddrLeak USER_PRIVILEGE a = REDACTED_ADDR ∧
    safeKernelAddrLeak p 0 = 0 ∧
    (safeKernelAddrLeak p a ≠ REDACTED_ADDR ↔
      p = KERNEL_PRIVILEGE ∧ a ≠ REDACTED_ADDR)) &&
  addressSamples.all (fun b => decide (p ≠ KERNEL_PRIVILEGE →
    safeKernelAddrLeak p a = safeKernelAddrLeak p b))

-- PBT: Post_prop. Pre is True, so no sampled inputs need to be discarded.
example : privilegeSamples.all (fun p => addressSamples.all (postCheck p)) = true := by
  native_decide

#eval privilegeSamples.all (fun p => addressSamples.all (postCheck p))

/-- Correctness on the full, unrestricted input domain. -/
theorem correctness_thm (caller_privilege kernel_addr : Int) :
    Pre caller_privilege kernel_addr → Post_prop caller_privilege kernel_addr := by
  intro _
  exact ⟨privilegedAccess_thm caller_privilege kernel_addr,
    unprivilegedRedaction_thm caller_privilege kernel_addr,
    userRedaction_thm kernel_addr,
    zeroAddress_thm caller_privilege,
    nonzeroDisclosure_thm caller_privilege kernel_addr,
    fun other_addr => noninterference_thm caller_privilege kernel_addr other_addr⟩

/-- Mutable-state implementation of the same guarded disclosure. -/
def safeKernelAddrLeakImperative (caller_privilege kernel_addr : Int) : Int := Id.run do
  let mut result : Int := REDACTED_ADDR
  if caller_privilege = KERNEL_PRIVILEGE then
    result := kernel_addr
  return result

-- Imperative tests: all seven original Python assertions.
example : safeKernelAddrLeakImperative 1 0xFFFF800000000000 = 0xFFFF800000000000 := by
  native_decide
example : safeKernelAddrLeakImperative 1 0xFFFFFFFF81000000 = 0xFFFFFFFF81000000 := by
  native_decide
example : safeKernelAddrLeakImperative 0 0xFFFF800000000000 = 0 := by native_decide
example : safeKernelAddrLeakImperative 0 0xFFFFFFFF81000000 = 0 := by native_decide
example : safeKernelAddrLeakImperative 0 0 = 0 := by native_decide
example : safeKernelAddrLeakImperative 1 0 = 0 := by native_decide
example : safeKernelAddrLeakImperative 0 0xDEADBEEF = 0 := by native_decide
example : safeKernelAddrLeakImperative (-1) (-123) = 0 := by native_decide
example : safeKernelAddrLeakImperative 1 (-123) = -123 := by native_decide

-- A bounded check also compares the two implementations on many inputs.
example : privilegeSamples.all (fun p => addressSamples.all (fun a =>
    decide (safeKernelAddrLeak p a = safeKernelAddrLeakImperative p a))) = true := by
  native_decide

#eval safeKernelAddrLeakImperative 1 0xFFFF800000000000
#eval safeKernelAddrLeakImperative 0 0xFFFF800000000000

/-- Exact equivalence for every pair of integers, without a precondition. -/
theorem functional_imperative_equivalence_thm (caller_privilege kernel_addr : Int) :
    safeKernelAddrLeak caller_privilege kernel_addr =
      safeKernelAddrLeakImperative caller_privilege kernel_addr := by
  by_cases h : caller_privilege = KERNEL_PRIVILEGE <;>
    simp [safeKernelAddrLeak, safeKernelAddrLeakImperative, h]

end «149_unsafeKernelAddrLeak_safe»
end Agent
