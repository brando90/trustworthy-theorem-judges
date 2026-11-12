import Mathlib

/-!
# Unsafe TLS version downgrade

This file formalizes a TLS server that negotiates the highest version visible
in both the (possibly attacker-modified) client offer and the server's own
capability.  Version numbers are natural numbers, with larger numbers denoting
newer protocols.  Because the negotiation does not authenticate the client's
true maximum, stripping newer versions from the offer causes a downgrade.
-/

namespace UnsafeTlsDowngrade95

/-- Select the highest TLS version common to the visible offer and the server. -/
def unsafeTlsDowngrade (clientOfferedMax serverMax : Nat) : Nat :=
  min clientOfferedMax serverMax

/-! ## Functional unit tests -/

example : unsafeTlsDowngrade 4 4 = 4 := by native_decide
example : unsafeTlsDowngrade 1 4 = 1 := by native_decide
example : unsafeTlsDowngrade 4 2 = 2 := by native_decide
example : unsafeTlsDowngrade 3 3 = 3 := by native_decide
example : unsafeTlsDowngrade 4 0 = 0 := by native_decide
example : unsafeTlsDowngrade 2 4 ≥ unsafeTlsDowngrade 1 4 := by native_decide

#eval unsafeTlsDowngrade 4 4
#eval unsafeTlsDowngrade 1 4
#eval unsafeTlsDowngrade 4 2
#eval unsafeTlsDowngrade 3 3
#eval unsafeTlsDowngrade 4 0

/-- The fixed check suite imposes no additional input precondition. -/
def Pre : Prop := True

/-- With full TLS 1.3 support visible on both sides, TLS 1.3 is selected. -/
def noAttack_prop : Prop :=
  unsafeTlsDowngrade 4 4 = 4

theorem noAttack_thm : noAttack_prop := by
  rfl

/-- A stripped offer advertising only TLS 1.0 makes the server select it. -/
def strippedOffer_prop : Prop :=
  unsafeTlsDowngrade 1 4 = 1

theorem strippedOffer_thm : strippedOffer_prop := by
  rfl

/-- The server's own maximum caps the negotiated version. -/
def serverCap_prop : Prop :=
  unsafeTlsDowngrade 4 2 = 2

theorem serverCap_thm : serverCap_prop := by
  rfl

/-- Equal client and server maxima negotiate that full version. -/
def matchingVersions_prop : Prop :=
  unsafeTlsDowngrade 3 3 = 3

theorem matchingVersions_thm : matchingVersions_prop := by
  rfl

/-- A legacy-only server forces the legacy version. -/
def legacyServer_prop : Prop :=
  unsafeTlsDowngrade 4 0 = 0

theorem legacyServer_thm : legacyServer_prop := by
  rfl

/-- Exposing a higher client maximum can never lower the selected version. -/
def monotoneOffer_prop : Prop :=
  ∀ lowerOffer higherOffer serverMax : Nat,
    lowerOffer ≤ higherOffer →
      unsafeTlsDowngrade lowerOffer serverMax ≤
        unsafeTlsDowngrade higherOffer serverMax

theorem monotoneOffer_thm : monotoneOffer_prop := by
  intro lowerOffer higherOffer serverMax h
  exact min_le_min h (le_refl serverMax)

/-- All observable properties checked by the Python program. -/
def Post_prop : Prop :=
  noAttack_prop ∧
    strippedOffer_prop ∧
    serverCap_prop ∧
    matchingVersions_prop ∧
    legacyServer_prop ∧
    monotoneOffer_prop

theorem unsafeTlsDowngrade_correct : Pre → Post_prop := by
  intro _
  exact ⟨noAttack_thm, strippedOffer_thm, serverCap_thm,
    matchingVersions_thm, legacyServer_thm, monotoneOffer_thm⟩

/-! ## Imperative implementation -/

/-- The same negotiation written with mutable state in `Id`. -/
def unsafeTlsDowngradeImperative (clientOfferedMax serverMax : Nat) : Nat :=
  Id.run do
    let mut negotiated := clientOfferedMax
    if serverMax < negotiated then
      negotiated := serverMax
    return negotiated

/-! ## Imperative unit tests -/

example : unsafeTlsDowngradeImperative 4 4 = 4 := by native_decide
example : unsafeTlsDowngradeImperative 1 4 = 1 := by native_decide
example : unsafeTlsDowngradeImperative 4 2 = 2 := by native_decide
example : unsafeTlsDowngradeImperative 3 3 = 3 := by native_decide
example : unsafeTlsDowngradeImperative 4 0 = 0 := by native_decide
example : unsafeTlsDowngradeImperative 2 4 ≥
    unsafeTlsDowngradeImperative 1 4 := by native_decide

#eval unsafeTlsDowngradeImperative 4 4
#eval unsafeTlsDowngradeImperative 1 4
#eval unsafeTlsDowngradeImperative 4 2
#eval unsafeTlsDowngradeImperative 3 3
#eval unsafeTlsDowngradeImperative 4 0

/-- The functional and imperative negotiations agree for every input. -/
theorem functional_imperative_equiv
    (clientOfferedMax serverMax : Nat) :
    unsafeTlsDowngrade clientOfferedMax serverMax =
      unsafeTlsDowngradeImperative clientOfferedMax serverMax := by
  by_cases h : serverMax < clientOfferedMax
  · simp [unsafeTlsDowngrade, unsafeTlsDowngradeImperative, min_def, h,
      Nat.not_le_of_lt h, Id.run]
    change serverMax = serverMax
    rfl
  · have hle : clientOfferedMax ≤ serverMax := Nat.le_of_not_gt h
    simp [unsafeTlsDowngrade, unsafeTlsDowngradeImperative, h, hle,
      Id.run]
    change clientOfferedMax = clientOfferedMax
    rfl

end UnsafeTlsDowngrade95
