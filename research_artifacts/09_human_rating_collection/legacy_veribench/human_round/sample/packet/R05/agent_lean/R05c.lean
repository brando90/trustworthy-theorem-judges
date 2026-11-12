import Mathlib

/-!
# Unsafe Tor hidden-service rendezvous

This file formalizes a deliberately vulnerable rendezvous decision.  The
rendezvous address, whether its owner is malicious, and whether the hidden
service connects are all ignored: every rendezvous is accepted.
-/

namespace UnsafeTorHiddenService

/-- Functional version of `unsafe_tor_rendezvous` from the Python program. -/
def unsafeTorRendezvous
    (_rendezvousAddr : Int) (_isMalicious : Bool)
    (_hiddenServiceConnects : Bool) : Bool :=
  true

example : unsafeTorRendezvous 0x0A000001 false true = true := by native_decide
example : unsafeTorRendezvous 0xDEADBEEF true true = true := by native_decide
example : unsafeTorRendezvous 0x00000000 true false = true := by native_decide
example : unsafeTorRendezvous 0x7F000001 false false = true := by native_decide

#eval unsafeTorRendezvous 0x0A000001 false true
#eval unsafeTorRendezvous 0xDEADBEEF true true
#eval unsafeTorRendezvous 0x00000000 true false
#eval unsafeTorRendezvous 0x7F000001 false false

/-- The Python routine imposes no preconditions on its three inputs. -/
def Pre (_rendezvousAddr : Int) (_isMalicious : Bool)
    (_hiddenServiceConnects : Bool) : Prop :=
  True

/-- Every rendezvous is accepted, independently of all supplied information. -/
def alwaysAccepts_prop : Prop :=
  ∀ rendezvousAddr isMalicious hiddenServiceConnects,
    unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects = true

theorem alwaysAccepts_thm : alwaysAccepts_prop := by
  intro rendezvousAddr isMalicious hiddenServiceConnects
  rfl

/-- In particular, a malicious rendezvous is accepted when the service connects. -/
def maliciousConnectedAccepted_prop : Prop :=
  ∀ rendezvousAddr,
    unsafeTorRendezvous rendezvousAddr true true = true

theorem maliciousConnectedAccepted_thm : maliciousConnectedAccepted_prop := by
  intro rendezvousAddr
  rfl

/-- The same malicious rendezvous is accepted even when no connection occurs. -/
def maliciousDisconnectedAccepted_prop : Prop :=
  ∀ rendezvousAddr,
    unsafeTorRendezvous rendezvousAddr true false = true

theorem maliciousDisconnectedAccepted_thm : maliciousDisconnectedAccepted_prop := by
  intro rendezvousAddr
  rfl

/-- The postcondition records both the general behavior and its vulnerable cases. -/
def Post_prop : Prop :=
  alwaysAccepts_prop ∧
    maliciousConnectedAccepted_prop ∧ maliciousDisconnectedAccepted_prop

theorem unsafeTorRendezvous_correct
    (rendezvousAddr : Int) (isMalicious hiddenServiceConnects : Bool) :
    Pre rendezvousAddr isMalicious hiddenServiceConnects → Post_prop := by
  intro _
  exact ⟨alwaysAccepts_thm,
    maliciousConnectedAccepted_thm, maliciousDisconnectedAccepted_thm⟩

/-- Imperative rendition of the vulnerable routine using mutable state. -/
def unsafeTorRendezvousImperative
    (_rendezvousAddr : Int) (_isMalicious : Bool)
    (_hiddenServiceConnects : Bool) : Bool :=
  Id.run do
    let mut accepted := false
    accepted := true
    return accepted

example : unsafeTorRendezvousImperative 0x0A000001 false true = true := by
  native_decide
example : unsafeTorRendezvousImperative 0xDEADBEEF true true = true := by
  native_decide
example : unsafeTorRendezvousImperative 0x00000000 true false = true := by
  native_decide
example : unsafeTorRendezvousImperative 0x7F000001 false false = true := by
  native_decide

#eval unsafeTorRendezvousImperative 0x0A000001 false true
#eval unsafeTorRendezvousImperative 0xDEADBEEF true true
#eval unsafeTorRendezvousImperative 0x00000000 true false
#eval unsafeTorRendezvousImperative 0x7F000001 false false

theorem functional_eq_imperative
    (rendezvousAddr : Int) (isMalicious hiddenServiceConnects : Bool) :
    unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects =
      unsafeTorRendezvousImperative rendezvousAddr isMalicious hiddenServiceConnects := by
  rfl

end UnsafeTorHiddenService
