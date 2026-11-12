import Mathlib

/-!
# 129_unsafeTorHiddenService

Lean 4 formalization of the Python program `unsafe_tor_rendezvous`.

The Python function models an *unsafe* Tor hidden-service rendezvous: the hidden
service accepts whatever rendezvous point it is told about, without authenticating
or vetting it. The function therefore returns `True` regardless of whether the
rendezvous point is controlled by an adversary (`is_malicious`) and regardless of
whether the hidden service actually connects (`hidden_service_connects`).

Vulnerability (MIT 6.858 Fall 2012 Quiz 2): a malicious Tor OR can set up a
rendezvous point on itself and send its address to the introduction point of a
hidden service. When the hidden service connects, the malicious node records the
incoming connection's origin, deanonymizing the service.

This file contains
* the functional implementation `unsafeTorRendezvous`,
* unit tests mirroring the Python `check()`,
* a precondition `Pre`, properties (`*_prop`) with proven theorems (`*_thm`),
* a postcondition `Post_prop` and property-based tests,
* a correctness theorem `Pre → Post_prop`,
* an imperative implementation `unsafeTorRendezvousImp` using `Id.run do`,
* an equivalence theorem between the functional and imperative implementations.
-/

namespace «129_unsafeTorHiddenService»

/-! ## Functional implementation -/

/-- Unsafe Tor hidden-service rendezvous.

Returns `true` regardless of whether the rendezvous point `rendezvousAddr` is
controlled by an adversary (`isMalicious`) and regardless of whether the hidden
service connects (`hiddenServiceConnects`). The rendezvous point is never
authenticated or vetted: this is the vulnerability. -/
def unsafeTorRendezvous (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Bool :=
  true  -- vulnerable: rendezvous never authenticated

/-- Executable model of the attack outcome: the hidden service is deanonymized when
the rendezvous point is malicious, the hidden service connects to it, and the
(unauthenticated) rendezvous was accepted. -/
def deanonymized (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Bool :=
  isMalicious && hiddenServiceConnects &&
    unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects

/-! ## Unit tests (mirroring the Python `check()`) -/

example : unsafeTorRendezvous 0x0A000001 false true = true := by native_decide
example : unsafeTorRendezvous 0xDEADBEEF true true = true := by native_decide
example : unsafeTorRendezvous 0x00000000 true false = true := by native_decide
example : unsafeTorRendezvous 0x7F000001 false false = true := by native_decide

-- The attack succeeds in the malicious-and-connecting scenario.
example : deanonymized 0xDEADBEEF true true = true := by native_decide
example : deanonymized 0x0A000001 false true = false := by native_decide
example : deanonymized 0x00000000 true false = false := by native_decide

/-- Executable analogue of the Python `check()` function: all four assertions. -/
def check : Bool :=
  (unsafeTorRendezvous 0x0A000001 false true == true) &&
  (unsafeTorRendezvous 0xDEADBEEF true true == true) &&
  (unsafeTorRendezvous 0x00000000 true false == true) &&
  (unsafeTorRendezvous 0x7F000001 false false == true)

example : check = true := by native_decide

#eval unsafeTorRendezvous 0x0A000001 false true   -- true
#eval unsafeTorRendezvous 0xDEADBEEF true true    -- true (vuln: malicious accepted)
#eval unsafeTorRendezvous 0x00000000 true false   -- true (vuln: no-connect malicious accepted)
#eval unsafeTorRendezvous 0x7F000001 false false  -- true
#eval check                                        -- true ("All tests passed.")

/-! ## Pre-condition -/

/-- Pre-condition: the Python function accepts any address and any pair of flags,
so there is no restriction on the inputs. -/
def Pre (rendezvousAddr : Nat) (isMalicious : Bool) (hiddenServiceConnects : Bool) : Prop :=
  True

theorem Pre_always_thm (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Pre rendezvousAddr isMalicious hiddenServiceConnects := by
  unfold Pre
  trivial

/-! ## Properties -/

/-- The rendezvous point is always accepted: the result is `true` for every input. -/
def always_accepts_prop (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects = true

theorem always_accepts_thm (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    always_accepts_prop rendezvousAddr isMalicious hiddenServiceConnects := by
  unfold always_accepts_prop unsafeTorRendezvous
  rfl

/-- The vulnerability: a malicious rendezvous point is accepted. -/
def malicious_accepted_prop (rendezvousAddr : Nat) (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr true hiddenServiceConnects = true

theorem malicious_accepted_thm (rendezvousAddr : Nat) (hiddenServiceConnects : Bool) :
    malicious_accepted_prop rendezvousAddr hiddenServiceConnects := by
  unfold malicious_accepted_prop unsafeTorRendezvous
  rfl

/-- An honest rendezvous point is accepted (no false rejections). -/
def honest_accepted_prop (rendezvousAddr : Nat) (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr false hiddenServiceConnects = true

theorem honest_accepted_thm (rendezvousAddr : Nat) (hiddenServiceConnects : Bool) :
    honest_accepted_prop rendezvousAddr hiddenServiceConnects := by
  unfold honest_accepted_prop unsafeTorRendezvous
  rfl

/-- No authentication: the outcome does not depend on whether the rendezvous point
is malicious. -/
def no_authentication_prop (rendezvousAddr : Nat) (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr true hiddenServiceConnects =
    unsafeTorRendezvous rendezvousAddr false hiddenServiceConnects

theorem no_authentication_thm (rendezvousAddr : Nat) (hiddenServiceConnects : Bool) :
    no_authentication_prop rendezvousAddr hiddenServiceConnects := by
  unfold no_authentication_prop unsafeTorRendezvous
  rfl

/-- The outcome is independent of every input (address and both flags). -/
def input_independent_prop (rendezvousAddr rendezvousAddr' : Nat)
    (isMalicious isMalicious' hiddenServiceConnects hiddenServiceConnects' : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects =
    unsafeTorRendezvous rendezvousAddr' isMalicious' hiddenServiceConnects'

theorem input_independent_thm (rendezvousAddr rendezvousAddr' : Nat)
    (isMalicious isMalicious' hiddenServiceConnects hiddenServiceConnects' : Bool) :
    input_independent_prop rendezvousAddr rendezvousAddr' isMalicious isMalicious'
      hiddenServiceConnects hiddenServiceConnects' := by
  unfold input_independent_prop unsafeTorRendezvous
  rfl

/-- The hidden service never rejects a rendezvous point. -/
def never_rejects_prop (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects ≠ false

theorem never_rejects_thm (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    never_rejects_prop rendezvousAddr isMalicious hiddenServiceConnects := by
  unfold never_rejects_prop unsafeTorRendezvous
  decide

/-- The attack: whenever the rendezvous point is malicious and the hidden service
connects, the hidden service is deanonymized (because the rendezvous was accepted). -/
def deanonymization_prop (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  isMalicious = true → hiddenServiceConnects = true →
    deanonymized rendezvousAddr isMalicious hiddenServiceConnects = true

theorem deanonymization_thm (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    deanonymization_prop rendezvousAddr isMalicious hiddenServiceConnects := by
  unfold deanonymization_prop deanonymized unsafeTorRendezvous
  intro hm hc
  subst hm
  subst hc
  rfl

/-- Conversely, deanonymization happens exactly when the rendezvous point is malicious
and the hidden service connects. -/
def deanonymized_iff_prop (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  deanonymized rendezvousAddr isMalicious hiddenServiceConnects =
    (isMalicious && hiddenServiceConnects)

theorem deanonymized_iff_thm (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    deanonymized_iff_prop rendezvousAddr isMalicious hiddenServiceConnects := by
  unfold deanonymized_iff_prop deanonymized unsafeTorRendezvous
  cases isMalicious <;> cases hiddenServiceConnects <;> rfl

/-! ## Post-condition -/

/-- Post-condition: conjunction of all the properties above. -/
def Post_prop (rendezvousAddr : Nat) (isMalicious : Bool) (hiddenServiceConnects : Bool) : Prop :=
  always_accepts_prop rendezvousAddr isMalicious hiddenServiceConnects ∧
  malicious_accepted_prop rendezvousAddr hiddenServiceConnects ∧
  honest_accepted_prop rendezvousAddr hiddenServiceConnects ∧
  no_authentication_prop rendezvousAddr hiddenServiceConnects ∧
  never_rejects_prop rendezvousAddr isMalicious hiddenServiceConnects ∧
  deanonymization_prop rendezvousAddr isMalicious hiddenServiceConnects ∧
  deanonymized_iff_prop rendezvousAddr isMalicious hiddenServiceConnects

/-! ## Property-based tests -/

-- always_accepts_prop
#eval Plausible.Testable.check
  (∀ a : Nat, ∀ m c : Bool, unsafeTorRendezvous a m c = true)

-- malicious_accepted_prop
#eval Plausible.Testable.check
  (∀ a : Nat, ∀ c : Bool, unsafeTorRendezvous a true c = true)

-- honest_accepted_prop
#eval Plausible.Testable.check
  (∀ a : Nat, ∀ c : Bool, unsafeTorRendezvous a false c = true)

-- no_authentication_prop
#eval Plausible.Testable.check
  (∀ a : Nat, ∀ c : Bool, unsafeTorRendezvous a true c = unsafeTorRendezvous a false c)

-- input_independent_prop
#eval Plausible.Testable.check
  (∀ a a' : Nat, ∀ m m' c c' : Bool, unsafeTorRendezvous a m c = unsafeTorRendezvous a' m' c')

-- never_rejects_prop
#eval Plausible.Testable.check
  (∀ a : Nat, ∀ m c : Bool, unsafeTorRendezvous a m c ≠ false)

-- deanonymization_prop (precondition-free Boolean form: `m ∧ c` implies deanonymized)
#eval Plausible.Testable.check
  (∀ a : Nat, ∀ m c : Bool, (!(m && c) || deanonymized a m c) = true)
#eval Plausible.Testable.check
  (∀ a : Nat, deanonymized a true true = true)

-- deanonymization_prop, bounded (exhaustive) PBT over addresses 0..255
example :
    (List.range 256).all (fun a =>
      [true, false].all (fun m =>
        [true, false].all (fun c => !(m && c) || deanonymized a m c))) = true := by
  native_decide

-- deanonymized_iff_prop
#eval Plausible.Testable.check
  (∀ a : Nat, ∀ m c : Bool, deanonymized a m c = (m && c))

-- Post_prop (executable Boolean form of the whole conjunction)
#eval Plausible.Testable.check
  (∀ a : Nat, ∀ m c : Bool,
    unsafeTorRendezvous a m c = true ∧
    unsafeTorRendezvous a true c = true ∧
    unsafeTorRendezvous a false c = true ∧
    unsafeTorRendezvous a true c = unsafeTorRendezvous a false c ∧
    unsafeTorRendezvous a m c ≠ false ∧
    (!(m && c) || deanonymized a m c) = true ∧
    deanonymized a m c = (m && c))

/-- Executable Boolean form of `Post_prop`, used for bounded (exhaustive) PBTs. -/
def postCheck (a : Nat) (m c : Bool) : Bool :=
  (unsafeTorRendezvous a m c == true) &&
  (unsafeTorRendezvous a true c == true) &&
  (unsafeTorRendezvous a false c == true) &&
  (unsafeTorRendezvous a true c == unsafeTorRendezvous a false c) &&
  (unsafeTorRendezvous a m c != false) &&
  (!(m && c) || deanonymized a m c) &&
  (deanonymized a m c == (m && c))

-- Bounded PBT: exhaustive over addresses 0..255 and all flag combinations.
example :
    (List.range 256).all (fun a =>
      [true, false].all (fun m =>
        [true, false].all (fun c => postCheck a m c))) = true := by native_decide

-- Bounded PBT over the concrete addresses from the Python tests and all flags.
example :
    [0x0A000001, 0xDEADBEEF, 0x00000000, 0x7F000001].all (fun a =>
      [true, false].all (fun m =>
        [true, false].all (fun c => postCheck a m c))) = true := by native_decide

/-! ## Correctness theorem -/

theorem correctness_thm (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    Pre rendezvousAddr isMalicious hiddenServiceConnects →
      Post_prop rendezvousAddr isMalicious hiddenServiceConnects := by
  intro _
  unfold Post_prop
  exact ⟨always_accepts_thm rendezvousAddr isMalicious hiddenServiceConnects,
    malicious_accepted_thm rendezvousAddr hiddenServiceConnects,
    honest_accepted_thm rendezvousAddr hiddenServiceConnects,
    no_authentication_thm rendezvousAddr hiddenServiceConnects,
    never_rejects_thm rendezvousAddr isMalicious hiddenServiceConnects,
    deanonymization_thm rendezvousAddr isMalicious hiddenServiceConnects,
    deanonymized_iff_thm rendezvousAddr isMalicious hiddenServiceConnects⟩

/-! ## Imperative implementation -/

/-- Imperative version of `unsafeTorRendezvous`, written with `Id.run do` and mutable
state. The hidden service receives the rendezvous address from the introduction
point and accepts it. Vulnerability: neither `isMalicious` nor
`hiddenServiceConnects` is ever consulted -- no authentication step exists. -/
def unsafeTorRendezvousImp (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Bool := Id.run do
  let mut accepted : Bool := false
  -- A safe implementation would authenticate the rendezvous point here and set
  -- `accepted` only when the check passes. The unsafe one accepts unconditionally.
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafeTorRendezvousImp 0x0A000001 false true = true := by native_decide
example : unsafeTorRendezvousImp 0xDEADBEEF true true = true := by native_decide
example : unsafeTorRendezvousImp 0x00000000 true false = true := by native_decide
example : unsafeTorRendezvousImp 0x7F000001 false false = true := by native_decide

#eval unsafeTorRendezvousImp 0x0A000001 false true   -- true
#eval unsafeTorRendezvousImp 0xDEADBEEF true true    -- true
#eval unsafeTorRendezvousImp 0x00000000 true false   -- true
#eval unsafeTorRendezvousImp 0x7F000001 false false  -- true

-- PBT: imperative implementation agrees with the functional one.
#eval Plausible.Testable.check
  (∀ a : Nat, ∀ m c : Bool, unsafeTorRendezvous a m c = unsafeTorRendezvousImp a m c)

example :
    (List.range 256).all (fun a =>
      [true, false].all (fun m =>
        [true, false].all (fun c =>
          unsafeTorRendezvous a m c == unsafeTorRendezvousImp a m c))) = true := by
  native_decide

/-! ## Equivalence theorem -/

theorem functional_imperative_equiv_thm (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects =
      unsafeTorRendezvousImp rendezvousAddr isMalicious hiddenServiceConnects := by
  unfold unsafeTorRendezvous unsafeTorRendezvousImp
  rfl

/-- The imperative implementation also satisfies the post-condition. -/
theorem imperative_correctness_thm (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    Pre rendezvousAddr isMalicious hiddenServiceConnects →
      unsafeTorRendezvousImp rendezvousAddr isMalicious hiddenServiceConnects = true := by
  intro _
  rw [← functional_imperative_equiv_thm]
  exact always_accepts_thm rendezvousAddr isMalicious hiddenServiceConnects

end «129_unsafeTorHiddenService»
