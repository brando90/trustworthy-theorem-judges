import Mathlib
namespace Agent

/-!
# Unsafe return-to-libc / ROP check

Translation of the Python `unsafe_rop_check` and its test driver. Python's
unbounded integers are represented by `Int`. The function deliberately returns
`true` without inspecting any argument: this formalization documents the bug,
not a repaired security check. In particular, an NX defense does not prevent
reuse of existing libc code when return addresses are never validated.

The expected text segment is described by the half-open interval
`[text_start, text_end)`, solely for specifications; the implementation never
consults it. There are no restrictions on addresses or on the order of bounds.
The bounded executable tests are evidence only; all named theorems have
independent kernel-checked proofs.
-/

namespace UnsafeROPChain

/-! ## Functional implementation -/

/-- The vulnerable check accepts every return address and ignores both bounds. -/
def unsafe_rop_check (_return_addr _text_start _text_end : Int) : Bool :=
  true

/-! ## Original unit tests and executable Python-style test driver -/

example : unsafe_rop_check 0x08048000 0x08048000 0x08049000 = true := by
  native_decide

example : unsafe_rop_check 0xb7e90000 0x08048000 0x08049000 = true := by
  native_decide

example : unsafe_rop_check 0x00000000 0x08048000 0x08049000 = true := by
  native_decide

example : unsafe_rop_check 0xdeadbeef 0x08048000 0x08049000 = true := by
  native_decide

/-- The four assertions and success message from Python's `check`. -/
def check : IO Unit := do
  unless unsafe_rop_check 0x08048000 0x08048000 0x08049000 do
    throw (IO.userError "valid ret rejected")
  unless unsafe_rop_check 0xb7e90000 0x08048000 0x08049000 do
    throw (IO.userError "vuln: libc addr accepted")
  unless unsafe_rop_check 0x00000000 0x08048000 0x08049000 do
    throw (IO.userError "vuln: null accepted")
  unless unsafe_rop_check 0xdeadbeef 0x08048000 0x08049000 do
    throw (IO.userError "vuln: arbitrary addr accepted")
  IO.println "All tests passed."

#eval check

/-! ## Precondition -/

/-- Python imposes no restrictions, not even ordered or nonnegative bounds. -/
def Pre (_return_addr _text_start _text_end : Int) : Prop := True

/-! ## Properties and proofs -/

/-- Exact output semantics over the complete input domain. -/
def alwaysAccepts_prop (return_addr text_start text_end : Int) : Prop :=
  unsafe_rop_check return_addr text_start text_end = true

theorem alwaysAccepts_thm (return_addr text_start text_end : Int) :
    alwaysAccepts_prop return_addr text_start text_end := by
  rfl

/-- A return address inside the expected text segment is accepted. -/
def validReturnAccepted_prop (return_addr text_start text_end : Int) : Prop :=
  (text_start ≤ return_addr ∧ return_addr < text_end) →
    unsafe_rop_check return_addr text_start text_end = true

theorem validReturnAccepted_thm (return_addr text_start text_end : Int) :
    validReturnAccepted_prop return_addr text_start text_end := by
  intro _
  rfl

/-- The vulnerability: addresses outside the text segment are also accepted.
The disjunction describes the complement of the half-open text interval,
including every address when the bounds are reversed or equal. -/
def outsideAccepted_prop (return_addr text_start text_end : Int) : Prop :=
  (return_addr < text_start ∨ text_end ≤ return_addr) →
    unsafe_rop_check return_addr text_start text_end = true

theorem outsideAccepted_thm (return_addr text_start text_end : Int) :
    outsideAccepted_prop return_addr text_start text_end := by
  intro _
  rfl

/-- Changing any or all three arguments cannot affect the result. -/
def inputIndependent_prop (return_addr text_start text_end : Int) : Prop :=
  ∀ other_addr other_start other_end : Int,
    unsafe_rop_check return_addr text_start text_end =
      unsafe_rop_check other_addr other_start other_end

theorem inputIndependent_thm (return_addr text_start text_end : Int) :
    inputIndependent_prop return_addr text_start text_end := by
  intro other_addr other_start other_end
  rfl

/-! ## Postcondition -/

/-- Observable behavior and its consequences, including the security failure. -/
def Post_prop (return_addr text_start text_end : Int) : Prop :=
  alwaysAccepts_prop return_addr text_start text_end ∧
  validReturnAccepted_prop return_addr text_start text_end ∧
  outsideAccepted_prop return_addr text_start text_end ∧
  inputIndependent_prop return_addr text_start text_end

/-! ## Bounded property-based tests

Exhaustively enumerate triples from a finite domain containing all integers
from -3 through 3 and all distinct addresses/bounds in the original tests.
This covers negative inputs, empty and reversed intervals, both boundaries,
and large positive addresses. Independence additionally enumerates all second
triples. Each test below is the executable Boolean form of its named property;
universal quantifiers are bounded only in tests, never in theorem statements.
-/

private def pbtInputs : List Int :=
  (List.range 7).map (fun n => (n : Int) - 3) ++
    [0x08048000, 0x08049000, 0xb7e90000, 0xdeadbeef]

private def allInputTriples (p : Int → Int → Int → Bool) : Bool :=
  pbtInputs.all (fun a =>
    pbtInputs.all (fun s =>
      pbtInputs.all (fun e => p a s e)))

private def alwaysAcceptsPBT : Bool :=
  allInputTriples (fun a s e => unsafe_rop_check a s e == true)

-- Executable implication: not antecedent, or accepted.
private def validReturnAcceptedPBT : Bool :=
  allInputTriples (fun a s e =>
    (!decide (s ≤ a ∧ a < e)) || (unsafe_rop_check a s e == true))

private def outsideAcceptedPBT : Bool :=
  allInputTriples (fun a s e =>
    (!decide (a < s ∨ e ≤ a)) || (unsafe_rop_check a s e == true))

private def inputIndependentPBT : Bool :=
  allInputTriples (fun a s e =>
    allInputTriples (fun a' s' e' =>
      unsafe_rop_check a s e == unsafe_rop_check a' s' e'))

private def postPBT : Bool :=
  allInputTriples (fun a s e =>
    (unsafe_rop_check a s e == true) &&
    ((!decide (s ≤ a ∧ a < e)) || (unsafe_rop_check a s e == true)) &&
    ((!decide (a < s ∨ e ≤ a)) || (unsafe_rop_check a s e == true)) &&
    allInputTriples (fun a' s' e' =>
      unsafe_rop_check a s e == unsafe_rop_check a' s' e'))

-- PBT for alwaysAccepts_prop.
example : alwaysAcceptsPBT = true := by native_decide

-- PBT for validReturnAccepted_prop.
example : validReturnAcceptedPBT = true := by native_decide

-- PBT for outsideAccepted_prop.
example : outsideAcceptedPBT = true := by native_decide

-- PBT for inputIndependent_prop (all pairs of sampled triples).
example : inputIndependentPBT = true := by native_decide

-- PBT for the complete Post_prop conjunction.
example : postPBT = true := by native_decide

#eval [("alwaysAccepts_prop", alwaysAcceptsPBT),
       ("validReturnAccepted_prop", validReturnAcceptedPBT),
       ("outsideAccepted_prop", outsideAcceptedPBT),
       ("inputIndependent_prop", inputIndependentPBT),
       ("Post_prop", postPBT)]

/-! ## Correctness with respect to the intentionally unsafe specification -/

theorem correctness_thm (return_addr text_start text_end : Int) :
    Pre return_addr text_start text_end →
      Post_prop return_addr text_start text_end := by
  intro _
  exact ⟨alwaysAccepts_thm return_addr text_start text_end,
    validReturnAccepted_thm return_addr text_start text_end,
    outsideAccepted_thm return_addr text_start text_end,
    inputIndependent_thm return_addr text_start text_end⟩

/-! ## Imperative implementation -/

/-- Mutable-state version: acceptance is assigned unconditionally. -/
def unsafe_rop_check_imp (_return_addr _text_start _text_end : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_rop_check_imp 0x08048000 0x08048000 0x08049000 = true := by
  native_decide

example : unsafe_rop_check_imp 0xb7e90000 0x08048000 0x08049000 = true := by
  native_decide

example : unsafe_rop_check_imp 0x00000000 0x08048000 0x08049000 = true := by
  native_decide

example : unsafe_rop_check_imp 0xdeadbeef 0x08048000 0x08049000 = true := by
  native_decide

#eval [unsafe_rop_check_imp 0x08048000 0x08048000 0x08049000,
       unsafe_rop_check_imp 0xb7e90000 0x08048000 0x08049000,
       unsafe_rop_check_imp 0x00000000 0x08048000 0x08049000,
       unsafe_rop_check_imp 0xdeadbeef 0x08048000 0x08049000]

example : allInputTriples (fun a s e =>
    unsafe_rop_check a s e == unsafe_rop_check_imp a s e) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (return_addr text_start text_end : Int) :
    unsafe_rop_check return_addr text_start text_end =
      unsafe_rop_check_imp return_addr text_start text_end := by
  rfl

end UnsafeROPChain
end Agent
