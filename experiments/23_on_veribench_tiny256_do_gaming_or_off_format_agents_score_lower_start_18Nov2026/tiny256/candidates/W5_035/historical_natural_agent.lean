import Mathlib
namespace Agent

/-!
# Unsafe XFI direct-jump check

Translation of the Python `unsafe_xfi_jump` program. The implementation deliberately
returns `true` without inspecting the target, module bounds, or approved entries.
In particular, an unapproved libc `unlink` address is accepted: this file models
and proves the vulnerability, rather than silently repairing the check.

`Int` models Python's unbounded signed integers, and `List Int` models lists of
entry addresses. There is no alignment, nonnegativity, ordering, or membership
precondition. The half-open interval used in the outside-module property is only
an observation about the inputs; the implementation never enforces it.
-/

namespace UnsafeXFIJump

/-! ## Functional implementation -/

/-- Faithful translation of the unconditional Python `return True`. -/
def unsafe_xfi_jump (_target_addr _module_start _module_end : Int)
    (_approved_entries : List Int) : Bool :=
  true

/-! ## Unit tests and the Python `check` routine -/

def approved : List Int := [0x08048100, 0x08048200]

example : unsafe_xfi_jump 0x08048100 0x08048000 0x08049000 approved = true := by
  native_decide

example : unsafe_xfi_jump 0xb7f00000 0x08048000 0x08049000 approved = true := by
  native_decide

example : unsafe_xfi_jump 0xdeadbeef 0x08048000 0x08049000 approved = true := by
  native_decide

example : unsafe_xfi_jump 0 0x08048000 0x08049000 approved = true := by
  native_decide

-- Negative addresses, reversed bounds, and an empty approved list are allowed too.
example : unsafe_xfi_jump (-7) 10 (-10) [] = true := by
  native_decide

/-- Executable counterpart of all four assertions and the final Python print. -/
def check : IO Unit := do
  unless unsafe_xfi_jump 0x08048100 0x08048000 0x08049000 approved do
    throw (IO.userError "approved rejected")
  unless unsafe_xfi_jump 0xb7f00000 0x08048000 0x08049000 approved do
    throw (IO.userError "vuln: libc unlink accepted")
  unless unsafe_xfi_jump 0xdeadbeef 0x08048000 0x08049000 approved do
    throw (IO.userError "vuln: arbitrary accepted")
  unless unsafe_xfi_jump 0 0x08048000 0x08049000 approved do
    throw (IO.userError "vuln: null accepted")
  IO.println "All tests passed."

#eval check

/-! ## Precondition -/

/-- All integer addresses, all bounds, and all lists are admissible. -/
def Pre (_target_addr _module_start _module_end : Int)
    (_approved_entries : List Int) : Prop :=
  True

/-! ## Properties and kernel-checked proofs -/

/-- The complete return-value semantics: every invocation is accepted. -/
def always_accepts_prop (target_addr module_start module_end : Int)
    (approved_entries : List Int) : Prop :=
  unsafe_xfi_jump target_addr module_start module_end approved_entries = true

theorem always_accepts_thm (target_addr module_start module_end : Int)
    (approved_entries : List Int) :
    always_accepts_prop target_addr module_start module_end approved_entries := by
  rfl

/-- Approved targets are accepted. -/
def approved_accepted_prop (target_addr module_start module_end : Int)
    (approved_entries : List Int) : Prop :=
  target_addr ∈ approved_entries →
    unsafe_xfi_jump target_addr module_start module_end approved_entries = true

theorem approved_accepted_thm (target_addr module_start module_end : Int)
    (approved_entries : List Int) :
    approved_accepted_prop target_addr module_start module_end approved_entries := by
  intro _
  rfl

/-- The security failure: targets absent from the approved list are also accepted. -/
def unapproved_accepted_prop (target_addr module_start module_end : Int)
    (approved_entries : List Int) : Prop :=
  target_addr ∉ approved_entries →
    unsafe_xfi_jump target_addr module_start module_end approved_entries = true

theorem unapproved_accepted_thm (target_addr module_start module_end : Int)
    (approved_entries : List Int) :
    unapproved_accepted_prop target_addr module_start module_end approved_entries := by
  intro _
  rfl

/-- Even being outside the half-open module interval does not cause rejection. -/
def outside_module_accepted_prop (target_addr module_start module_end : Int)
    (approved_entries : List Int) : Prop :=
  (target_addr < module_start ∨ module_end ≤ target_addr) →
    unsafe_xfi_jump target_addr module_start module_end approved_entries = true

theorem outside_module_accepted_thm (target_addr module_start module_end : Int)
    (approved_entries : List Int) :
    outside_module_accepted_prop target_addr module_start module_end approved_entries := by
  intro _
  rfl

/-- Concrete witness from the Python example, proved by kernel reduction. -/
theorem libc_unlink_bypass_thm :
    (0xb7f00000 : Int) ∉ approved ∧
    (0x08049000 : Int) ≤ 0xb7f00000 ∧
    unsafe_xfi_jump 0xb7f00000 0x08048000 0x08049000 approved = true := by
  decide

/-! ## Postcondition -/

/-- Behavioral correctness includes the unsafe behavior; it is not a safety claim. -/
def Post_prop (target_addr module_start module_end : Int)
    (approved_entries : List Int) : Prop :=
  always_accepts_prop target_addr module_start module_end approved_entries ∧
  approved_accepted_prop target_addr module_start module_end approved_entries ∧
  unapproved_accepted_prop target_addr module_start module_end approved_entries ∧
  outside_module_accepted_prop target_addr module_start module_end approved_entries

/-! ## Property-based tests

Exhaustive bounded tests take the Cartesian product of a signed small-address
range, the addresses in the Python examples, and representative entry lists.
Bounds vary independently, so empty and reversed intervals are tested as well.
These bounds restrict only the tests, not the precondition or any theorem.
Each check below is an executable Boolean form of the named proposition.
-/

def testAddresses : List Int :=
  (List.range 13).map (fun n => (n : Int) - 6) ++
    [0x08048000, 0x08048100, 0x08048200, 0x08049000, 0xb7f00000, 0xdeadbeef]

def testEntryLists : List (List Int) :=
  [[], [0], [-1, 1], [0, 0], approved, [0xb7f00000], [0xdeadbeef], testAddresses]

def checkSampledInputs (p : Int → Int → Int → List Int → Bool) : Bool :=
  testAddresses.all fun target =>
    testAddresses.all fun lo =>
      testAddresses.all fun hi =>
        testEntryLists.all fun entries => p target lo hi entries

-- PBT for always_accepts_prop.
example : checkSampledInputs (fun target lo hi entries =>
    unsafe_xfi_jump target lo hi entries) = true := by
  native_decide

-- PBT for approved_accepted_prop; both membership cases occur in the samples.
example : checkSampledInputs (fun target lo hi entries =>
    decide (target ∈ entries → unsafe_xfi_jump target lo hi entries = true)) = true := by
  native_decide

-- PBT for unapproved_accepted_prop, including empty lists and unapproved libc targets.
example : checkSampledInputs (fun target lo hi entries =>
    decide (target ∉ entries → unsafe_xfi_jump target lo hi entries = true)) = true := by
  native_decide

-- PBT for outside_module_accepted_prop, including interval boundary equalities.
example : checkSampledInputs (fun target lo hi entries =>
    decide ((target < lo ∨ hi ≤ target) →
      unsafe_xfi_jump target lo hi entries = true)) = true := by
  native_decide

-- PBT for Post_prop: executable conjunction of all four properties.
example : checkSampledInputs (fun target lo hi entries =>
    decide (unsafe_xfi_jump target lo hi entries = true ∧
      (target ∈ entries → unsafe_xfi_jump target lo hi entries = true) ∧
      (target ∉ entries → unsafe_xfi_jump target lo hi entries = true) ∧
      ((target < lo ∨ hi ≤ target) →
        unsafe_xfi_jump target lo hi entries = true))) = true := by
  native_decide

#eval checkSampledInputs (fun target lo hi entries => unsafe_xfi_jump target lo hi entries)

/-! ## Correctness -/

theorem correctness_thm (target_addr module_start module_end : Int)
    (approved_entries : List Int) :
    Pre target_addr module_start module_end approved_entries →
      Post_prop target_addr module_start module_end approved_entries := by
  intro _
  exact ⟨always_accepts_thm target_addr module_start module_end approved_entries,
    approved_accepted_thm target_addr module_start module_end approved_entries,
    unapproved_accepted_thm target_addr module_start module_end approved_entries,
    outside_module_accepted_thm target_addr module_start module_end approved_entries⟩

/-! ## Imperative implementation -/

/-- A mutable return register is set unconditionally; no input is inspected. -/
def unsafe_xfi_jump_imperative (_target_addr _module_start _module_end : Int)
    (_approved_entries : List Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_xfi_jump_imperative 0x08048100 0x08048000 0x08049000 approved = true := by
  native_decide

example : unsafe_xfi_jump_imperative 0xb7f00000 0x08048000 0x08049000 approved = true := by
  native_decide

example : unsafe_xfi_jump_imperative 0xdeadbeef 0x08048000 0x08049000 approved = true := by
  native_decide

example : unsafe_xfi_jump_imperative 0 0x08048000 0x08049000 approved = true := by
  native_decide

example : unsafe_xfi_jump_imperative (-7) 10 (-10) [] = true := by
  native_decide

#eval [unsafe_xfi_jump_imperative 0x08048100 0x08048000 0x08049000 approved,
       unsafe_xfi_jump_imperative 0xb7f00000 0x08048000 0x08049000 approved,
       unsafe_xfi_jump_imperative 0xdeadbeef 0x08048000 0x08049000 approved,
       unsafe_xfi_jump_imperative 0 0x08048000 0x08049000 approved]

-- Bounded regression test for functional/imperative agreement.
example : checkSampledInputs (fun target lo hi entries =>
    unsafe_xfi_jump target lo hi entries ==
      unsafe_xfi_jump_imperative target lo hi entries) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_eq_imperative_thm (target_addr module_start module_end : Int)
    (approved_entries : List Int) :
    unsafe_xfi_jump target_addr module_start module_end approved_entries =
      unsafe_xfi_jump_imperative target_addr module_start module_end approved_entries := by
  rfl

end UnsafeXFIJump
end Agent
