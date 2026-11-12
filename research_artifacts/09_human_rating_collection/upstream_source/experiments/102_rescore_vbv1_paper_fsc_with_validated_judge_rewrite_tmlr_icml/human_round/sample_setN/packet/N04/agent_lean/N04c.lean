import Mathlib

/-!
# 129 — Unsafe Tor Hidden-Service Rendezvous

The Python program models a Tor hidden service that does **not** authenticate
its rendezvous point: `unsafe_tor_rendezvous` returns `True` for every input,
including rendezvous addresses controlled by an adversary
(MIT 6.858 Fall 2012 Quiz 2 vulnerability: a malicious Tor OR can run the
rendezvous point on itself and deanonymize the hidden service when it connects).

This Lean 4 file formalizes:
* the functional implementation (always `true`),
* unit tests mirroring the Python `check()` assertions,
* the precondition `Pre`, the acceptance / no-authentication properties and the
  postcondition `Post_prop` as their conjunction, each with proofs,
* property-based tests (Plausible randomized and bounded exhaustive),
* the correctness theorem `Pre → Post`,
* an imperative `Id.run do` implementation using mutable state,
* imperative tests, and a functional/imperative equivalence theorem.
-/

namespace «129_unsafeTorHiddenService»

/-- Functional implementation: the rendezvous point is never authenticated,
so the function returns `true` for every input (the vulnerability). -/
def unsafeTorRendezvous (rendezvousAddr : Nat) (isMalicious hiddenServiceConnects : Bool) : Bool :=
  true

-- ============================================================================
-- Unit tests (mirror the Python `check()` assertions)
-- ============================================================================

example : unsafeTorRendezvous 0x0A000001 false true = true := by native_decide
example : unsafeTorRendezvous 0xDEADBEEF true true = true := by native_decide
example : unsafeTorRendezvous 0x00000000 true false = true := by native_decide
example : unsafeTorRendezvous 0x7F000001 false false = true := by native_decide

#eval unsafeTorRendezvous 0x0A000001 false true   -- expect true
#eval unsafeTorRendezvous 0xDEADBEEF true true    -- expect true (vuln: malicious accepted)
#eval unsafeTorRendezvous 0x00000000 true false   -- expect true (vuln: no-connect accepted)
#eval unsafeTorRendezvous 0x7F000001 false false  -- expect true

/-- Precondition: the Python program places no restriction on its inputs. -/
def Pre (_rendezvousAddr : Nat) (_isMalicious _hiddenServiceConnects : Bool) : Prop :=
  True

/-- Property: the function accepts the rendezvous (returns `true`). -/
def accepts_prop (rendezvousAddr : Nat) (isMalicious hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects = true

/-- Property (the vulnerability): even a malicious rendezvous point is
accepted — the rendezvous point is never authenticated or vetted. -/
def noAuthentication_prop (rendezvousAddr : Nat) (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr true hiddenServiceConnects = true

theorem accepts_thm :
    ∀ addr m c, accepts_prop addr m c := by
  intro addr m c; rfl

theorem noAuthentication_thm :
    ∀ addr c, noAuthentication_prop addr c := by
  intro addr c; rfl

/-- Postcondition: conjunction of the stated properties. -/
def Post_prop (rendezvousAddr : Nat) (isMalicious hiddenServiceConnects : Bool) : Prop :=
  accepts_prop rendezvousAddr isMalicious hiddenServiceConnects
    ∧ noAuthentication_prop rendezvousAddr hiddenServiceConnects

-- ============================================================================
-- Property-based tests
-- ============================================================================

-- Randomized PBT (Plausible ships with Mathlib): the function always returns true.
#eval Plausible.Testable.check
  (∀ (addr : Nat) (m c : Bool), unsafeTorRendezvous addr m c = true)

-- Randomized PBT: malicious rendezvous points are accepted (the vulnerability).
#eval Plausible.Testable.check
  (∀ (addr : Nat) (c : Bool), unsafeTorRendezvous addr true c = true)

-- Bounded PBT: exhaustive over small addresses and all flag combinations,
-- checking the postcondition's executable Boolean form.
example : (List.range 16).all (fun addr =>
    [false, true].all (fun m =>
      [false, true].all (fun c =>
        unsafeTorRendezvous addr m c && unsafeTorRendezvous addr true c))) = true := by
  native_decide

/-- Correctness: from the precondition, the postcondition follows. -/
theorem correct :
    ∀ addr m c, Pre addr m c → Post_prop addr m c := by
  intro addr m c _
  exact ⟨rfl, rfl⟩

-- ============================================================================
-- Imperative implementation with mutable state
-- ============================================================================

/-- Imperative implementation using `Id.run do` with a mutable variable,
mirroring the Python body `return True`. -/
def unsafeTorRendezvousImp (rendezvousAddr : Nat) (isMalicious hiddenServiceConnects : Bool) : Bool :=
  Id.run do
    let mut result : Bool := true
    result := true  -- vulnerable: rendezvous never authenticated
    return result

-- Imperative tests (mirror the Python `check()` assertions).
example : unsafeTorRendezvousImp 0x0A000001 false true = true := by native_decide
example : unsafeTorRendezvousImp 0xDEADBEEF true true = true := by native_decide
example : unsafeTorRendezvousImp 0x00000000 true false = true := by native_decide
example : unsafeTorRendezvousImp 0x7F000001 false false = true := by native_decide

#eval unsafeTorRendezvousImp 0x0A000001 false true
#eval unsafeTorRendezvousImp 0xDEADBEEF true true
#eval unsafeTorRendezvousImp 0x00000000 true false
#eval unsafeTorRendezvousImp 0x7F000001 false false

/-- Equivalence: the functional and imperative implementations agree. -/
theorem functional_eq_imperative :
    ∀ addr m c, unsafeTorRendezvous addr m c = unsafeTorRendezvousImp addr m c := by
  intro addr m c; rfl

end «129_unsafeTorHiddenService»
